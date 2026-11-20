/* Sixways core — pure game logic: hex grid, Hamiltonian-path finder,
   uniqueness solver, difficulty table and the strict puzzle generator.
   No DOM or browser references: this module runs in the web page, in a
   Web Worker, under Node for verification, and is the shared core a
   future Android (Capacitor) build will reuse.
   Extracted verbatim from the original web build (rikudo-app/www);
   behaviour, constants and generation are unchanged. */
"use strict";
/* ================= Grid ================= */
var DIRS = [[1,0],[1,-1],[0,-1],[-1,0],[-1,1],[0,1]];
function edgeKey(a, b) { return a < b ? a + "-" + b : b + "-" + a; }

function buildGrid(side) {
  // Hexagon of given side length, centre cell removed -> 36 / 60 / 90 cells.
  var cells = [], index = {};
  for (var q = -(side - 1); q <= side - 1; q++) {
    for (var r = -(side - 1); r <= side - 1; r++) {
      var s = -q - r;
      if (Math.max(Math.abs(q), Math.abs(r), Math.abs(s)) >= side) continue;
      if (q === 0 && r === 0) continue;
      index[q + "," + r] = cells.length;
      cells.push({ q: q, r: r, id: cells.length, nbrs: [] });
    }
  }
  cells.forEach(function (c) {
    DIRS.forEach(function (d) {
      var k = (c.q + d[0]) + "," + (c.r + d[1]);
      if (index.hasOwnProperty(k)) c.nbrs.push(index[k]);
    });
  });
  return cells;
}

/* ============ Search budget (monotonic deadline) ============ */
// Mirrors the native app's SearchBudget: a deadline on a monotonic
// clock (performance.now, never the wall clock), polled INSIDE the
// path search and the solver. When it fires, searches unwind and
// report "unproven" — a result that lands after the deadline is
// never accepted as a proof.
function makeBudget(seconds) {
  var deadline = performance.now() + seconds * 1000;
  return {
    isStopped: function () { return performance.now() >= deadline; }
  };
}
function unlimitedBudget() {
  return { isStopped: function () { return false; } };
}

/* ============ Random Hamiltonian path (the hidden solution) ============ */
function hamiltonianPath(cells, budget) {
  budget = budget || unlimitedBudget();
  var N = cells.length;
  var visited = new Uint8Array(N);
  var path = [];
  var nodes = 0, NODE_BUDGET = 60000;

  function dfs(cell) {
    if (path.length === N) return true;
    if (++nodes > NODE_BUDGET) return false;
    // Poll the budget inside the search (every 512 nodes), so a
    // path search stops at its deadline instead of overrunning it.
    if (nodes % 512 === 0 && budget.isStopped()) return false;
    var cands = [];
    for (var i = 0; i < cells[cell].nbrs.length; i++) {
      var nb = cells[cell].nbrs[i];
      if (visited[nb]) continue;
      var deg = 0;
      for (var j = 0; j < cells[nb].nbrs.length; j++) if (!visited[cells[nb].nbrs[j]]) deg++;
      cands.push({ cell: nb, deg: deg, rnd: Math.random() });
    }
    cands.sort(function (a, b) { return (a.deg - b.deg) || (a.rnd - b.rnd); });
    for (var k = 0; k < cands.length; k++) {
      visited[cands[k].cell] = 1; path.push(cands[k].cell);
      if (dfs(cands[k].cell)) return true;
      path.pop(); visited[cands[k].cell] = 0;
      if (nodes > NODE_BUDGET) return false;
      // Latch the stop: once the budget has fired, unwind
      // immediately instead of trying sibling candidates until
      // the next poll. (A passed deadline never reverses.)
      if (budget.isStopped()) return false;
    }
    return false;
  }

  for (var attempt = 0; attempt < 300; attempt++) {
    if (budget.isStopped()) return null;
    visited.fill(0); path = []; nodes = 0;
    var start = Math.floor(Math.random() * N);
    visited[start] = 1; path.push(start);
    if (dfs(start) && path.length === N) {
      // A path that completed between polls, after the deadline,
      // is not used — the stop is checked again on success.
      if (budget.isStopped()) return null;
      return path.slice();
    }
  }
  return null;
}

/* ============ Solver: count solutions (uniqueness check) ============ */
function makeSolver(cells, givens, givenByNum, links) {
  var N = cells.length;
  var linkNbrs = cells.map(function () { return []; });
  links.forEach(function (ek) {
    var parts = ek.split("-"), a = +parts[0], b = +parts[1];
    linkNbrs[a].push(b); linkNbrs[b].push(a);
  });
  var pos = new Int32Array(N + 2).fill(-1);
  var val = new Int32Array(N).fill(0);
  var nodes = 0;

  function connectedOK(fromCell) {
    var start = -1, total = 0, i;
    for (i = 0; i < N; i++) if (val[i] === 0) { total++; if (start < 0) start = i; }
    if (total === 0) return true;
    var seen = new Uint8Array(N), stack = [start], count = 0;
    seen[start] = 1;
    while (stack.length) {
      var c = stack.pop(); count++;
      for (var j = 0; j < cells[c].nbrs.length; j++) {
        var nb = cells[c].nbrs[j];
        if (!seen[nb] && val[nb] === 0) { seen[nb] = 1; stack.push(nb); }
      }
    }
    return count === total;
  }

  function canPlace(num, cell) {
    if (val[cell] !== 0) return false;
    if (givens.has(cell) && givens.get(cell) !== num) return false;
    if (givenByNum.has(num) && givenByNum.get(num) !== cell) return false;
    if (num > 1) {
      var prev = pos[num - 1];
      if (prev < 0 || cells[cell].nbrs.indexOf(prev) === -1) return false;
    }
    var ln = linkNbrs[cell];
    for (var i = 0; i < ln.length; i++) {
      var v = val[ln[i]];
      if (v !== 0 && Math.abs(v - num) !== 1) return false;
    }
    if (ln.length) {
      // Link-availability prune (ported from the native solver;
      // sound — it only cuts branches that cannot complete):
      // every EMPTY link neighbour of this cell must eventually
      // hold num-1 or num+1, and the only values still available
      // to fill them are the ones not placed yet. A value already
      // placed at a cell that is not one of these link neighbours
      // is spent. Without this, the fully-linked fallback board
      // (every path edge a link) makes the counter thrash through
      // off-path chains whose link diamonds can never be
      // satisfied, and the recount of a by-construction-unique
      // puzzle hits the node cap.
      var available = 0;
      if (num > 1 && pos[num - 1] === -1) available++;
      if (num < N && pos[num + 1] === -1) available++;
      var emptyLinks = 0;
      for (var li = 0; li < ln.length; li++) if (val[ln[li]] === 0) emptyLinks++;
      if (emptyLinks > available) return false;
    }
    if (ln.length) {
      var okAny = false;
      for (var a = 0; a < ln.length; a++) {
        var w = val[ln[a]];
        if (w !== 0) { okAny = true; break; }
        if (num < N && pos[num + 1] === -1) { okAny = true; break; }
        if (num > 1 && pos[num - 1] === cell) { okAny = true; break; }
      }
      if (!okAny) return false;
    }
    return true;
  }

  function pruneOK(num) {
    var end = pos[num];
    var finalCell = givenByNum.has(N) ? givenByNum.get(N) : -1;
    var degOne = 0;
    for (var i = 0; i < N; i++) {
      if (val[i] !== 0) continue;
      var deg = 0;
      for (var j = 0; j < cells[i].nbrs.length; j++) {
        var nb = cells[i].nbrs[j];
        if (val[nb] === 0 || nb === end) deg++;
      }
      if (i === finalCell) { if (deg === 0) return false; }
      else if (deg <= 1) {
        if (finalCell >= 0) return false;
        if (++degOne > 1) return false;
      }
    }
    return true;
  }

  function search(num, limit, cap, found) {
    if (found.count >= limit || nodes > cap || found.aborted) return;
    if (num > N) {
      found.count++;
      if (!found.first) found.first = val.slice();
      else if (!found.second) found.second = val.slice();
      return;
    }
    nodes++;
    // Poll the budget inside the search (every 512 nodes), not
    // just between operations: past the deadline the count is
    // unproven and reported as aborted, never accepted late.
    if (nodes % 512 === 0 && activeBudget && activeBudget.isStopped()) {
      found.aborted = true;
      return;
    }
    var cands;
    if (givenByNum.has(num)) {
      cands = [givenByNum.get(num)];
    } else if (num === 1) {
      cands = [];
      for (var i = 0; i < N; i++) if (!givens.has(i)) cands.push(i);
    } else {
      cands = cells[pos[num - 1]].nbrs.filter(function (nb) { return val[nb] === 0; });
      cands.sort(function (a, b) {
        var da = 0, db = 0, j;
        for (j = 0; j < cells[a].nbrs.length; j++) if (val[cells[a].nbrs[j]] === 0) da++;
        for (j = 0; j < cells[b].nbrs.length; j++) if (val[cells[b].nbrs[j]] === 0) db++;
        return da - db;
      });
    }
    for (var k = 0; k < cands.length; k++) {
      var cell = cands[k];
      if (!canPlace(num, cell)) continue;
      val[cell] = num; pos[num] = cell;
      if (num === N || (connectedOK(cell) && pruneOK(num))) search(num + 1, limit, cap, found);
      val[cell] = 0; pos[num] = -1;
      if (found.count >= limit || nodes > cap || found.aborted) return;
    }
  }

  var activeBudget = null;
  return {
    count: function (limit, cap, budget) {
      nodes = 0;
      activeBudget = budget || null;
      var found = { count: 0, first: null, second: null, aborted: false };
      search(1, limit, cap, found);
      return { count: found.count, capped: nodes > cap, aborted: found.aborted, first: found.first, second: found.second };
    }
  };
}

/* ============ Puzzle generation (strict uniqueness) ============ */
var DIFFS = {
  easy:   { givenFrac: 0.19, linkFrac: 0.26, cap: 500000, title: "Easy", desc: "The gentlest way in, with candidate cells glowing. The generator aims for about 19% printed numbers and 26% links, and adds an extra clue only when it must to prove a single solution — each board lists its actual counts underneath." },
  medium: { givenFrac: 0.13, linkFrac: 0.16, cap: 500000, title: "Medium — the standard game", desc: "Sparse givens, few links — you have to deduce the chain. Candidate cells still glow. The generator aims for about 13% printed numbers and 16% links; the repair loop may add a clue to guarantee exactly one solution, and each board lists its actual counts underneath." },
  hard:   { givenFrac: 0.08, linkFrac: 0.09, cap: 650000, title: "Hard", desc: "Very sparse clues and no candidate glow — work it out from the links, endpoints and dead ends. The generator aims for about 8% printed numbers and 9% links, adding a clue only when uniqueness can't be proved without it." },
  expert: { givenFrac: 0.055, linkFrac: 0.05, cap: 800000, title: "Expert", desc: "The sparsest level: the generator aims for about 5–6% printed numbers and 5% links, with no glow and mistakes hidden — tick “Show mistakes” if you want to check yourself. Extra clues are added whenever a unique solution can't be proved without them, so finished Expert puzzles can carry more clues than the target." }
};

function shuffle(arr) {
  for (var i = arr.length - 1; i > 0; i--) {
    var j = Math.floor(Math.random() * (i + 1));
    var t = arr[i]; arr[i] = arr[j]; arr[j] = t;
  }
  return arr;
}

/* ============ Bundled preverified paths (fallback) ============ */
// Validated Hamiltonian paths, one per board side, taken from the
// native app's BundledPaths.swift, which produced them with the
// same path finder over the identical grid (cell ids are assigned
// deterministically). They make fallback construction bounded and
// guaranteed: link the bundled path's edges and print its
// endpoints — O(N), cannot fail, no fresh search at serve time.
// bundledPath() re-validates the count, the id range, uniqueness
// and every adjacency before use; if validation ever failed,
// buildFallbackPuzzle falls back to the search-based construction.
var BUNDLED_PATHS = {
  4: [
    3, 2, 1, 0, 4, 5, 6, 7, 8, 14, 20, 26, 19, 13, 12,
    11, 10, 9, 15, 16, 21, 27, 32, 33, 28, 22, 17, 23, 29, 34,
    35, 31, 30, 24, 18, 25
  ],
  5: [
    55, 56, 57, 58, 59, 54, 48, 41, 33, 25, 17, 10, 4, 3, 9,
    16, 24, 32, 40, 31, 23, 30, 22, 15, 8, 2, 1, 0, 5, 6,
    7, 14, 21, 13, 12, 11, 18, 26, 34, 42, 49, 50, 43, 35, 27,
    19, 20, 28, 29, 36, 37, 44, 51, 45, 38, 39, 47, 53, 52, 46
  ],
  6: [
    19, 12, 20, 29, 39, 49, 59, 68, 76, 83, 89, 88, 82, 75, 67,
    58, 48, 38, 28, 27, 37, 47, 57, 46, 36, 45, 56, 66, 74, 81,
    87, 86, 85, 84, 77, 78, 79, 80, 73, 65, 55, 64, 72, 71, 63,
    54, 53, 62, 70, 69, 61, 60, 50, 40, 30, 41, 51, 52, 42, 31,
    21, 13, 6, 0, 1, 7, 14, 22, 32, 43, 44, 33, 23, 15, 24,
    34, 35, 25, 26, 18, 17, 16, 8, 2, 9, 3, 10, 11, 5, 4
  ]
};
function bundledPath(side, cells) {
  var raw = BUNDLED_PATHS[side];
  if (!raw || raw.length !== cells.length) return null;
  // Range-check every id BEFORE any indexing, plus uniqueness.
  var seen = new Uint8Array(cells.length);
  for (var i = 0; i < raw.length; i++) {
    if (raw[i] < 0 || raw[i] >= cells.length || seen[raw[i]]) return null;
    seen[raw[i]] = 1;
  }
  for (var j = 1; j < raw.length; j++) {
    if (cells[raw[j - 1]].nbrs.indexOf(raw[j]) === -1) return null;
  }
  return raw.slice();
}

// Preverified fallback: every edge of the hidden path is a link and
// both endpoints (1 and N) are printed. The link graph is then itself
// a Hamiltonian path, so any solution must follow it in order — the
// puzzle is unique by construction, no solver budget involved.
function fallbackFromPath(cells, path, side, diffKey) {
  var N = cells.length;
  var solution = new Map(), solByNum = new Array(N + 1);
  path.forEach(function (cell, i) { solution.set(cell, i + 1); solByNum[i + 1] = cell; });
  var givens = new Map(), givenByNum = new Map();
  [path[0], path[N - 1]].forEach(function (cell) {
    var n = solution.get(cell);
    givens.set(cell, n); givenByNum.set(n, cell);
  });
  var links = new Set();
  for (var e = 0; e < N - 1; e++) links.add(edgeKey(path[e], path[e + 1]));
  return { cells: cells, N: N, solution: solution, solByNum: solByNum, givens: givens, givenByNum: givenByNum, links: links, side: side, diff: diffKey, fallback: true };
}

function buildFallbackPuzzle(side, diffKey, budget) {
  var cells = buildGrid(side);
  var bundled = bundledPath(side, cells);
  if (bundled) return fallbackFromPath(cells, bundled, side, diffKey);
  // Backstop only (bundled data failed validation): the search is
  // bounded by the caller's budget — the generator's own when
  // called from generate(), a fresh 10-second budget when the
  // watchdog calls directly — on top of the finder's per-attempt
  // node budget.
  var b = budget || makeBudget(10);
  for (var attempt = 0; attempt < 20; attempt++) {
    if (b.isStopped()) return null;
    var cells2 = buildGrid(side);
    var path = hamiltonianPath(cells2, b);
    if (!path) continue;
    return fallbackFromPath(cells2, path, side, diffKey);
  }
  return null;
}

function generate(side, diffKey) {
  var spec = DIFFS[diffKey];
  var nodeCap = Math.max(150000, spec.cap - (side - 4) * 125000);
  // Monotonic 20-second budget per puzzle. It is polled INSIDE
  // the path search and the solver as well as between operations,
  // so a search that would finish after the deadline reports
  // unproven instead of being accepted late.
  var budget = makeBudget(20);

  for (var attempt = 0; attempt < 6; attempt++) {
    if (budget.isStopped()) break;
    var cells = buildGrid(side);
    var N = cells.length;
    var path = hamiltonianPath(cells, budget);
    if (!path) continue;
    var solution = new Map(), solByNum = new Array(N + 1);
    path.forEach(function (cell, i) { solution.set(cell, i + 1); solByNum[i + 1] = cell; });

    var givens = new Map(), givenByNum = new Map();
    function addGiven(cell) {
      var n = solution.get(cell);
      givens.set(cell, n); givenByNum.set(n, cell);
    }
    addGiven(path[0]); addGiven(path[N - 1]); // 1 and N always shown
    var midCells = shuffle(path.slice(1, N - 1));
    var wantGivens = Math.max(2, Math.round(N * spec.givenFrac));
    for (var i = 0; i < midCells.length && givens.size < wantGivens; i++) addGiven(midCells[i]);

    var pathEdges = [];
    for (var e = 0; e < N - 1; e++) pathEdges.push(edgeKey(path[e], path[e + 1]));
    var links = new Set();
    var shuffledEdges = shuffle(pathEdges.slice());
    var wantLinks = Math.round((N - 1) * spec.linkFrac);
    for (var l = 0; l < shuffledEdges.length && links.size < wantLinks; l++) links.add(shuffledEdges[l]);

    // Strict repair loop, structured verify → mutate → verify: a
    // puzzle is published ONLY when the solver runs on the final
    // clue set and returns count === 1 with the solver neither
    // capped nor aborted. The solver runs at the top of every
    // iteration, so a clue added by any repair — including the
    // 120th — is always followed by a fresh check before the
    // candidate can be published.
    var proven = false;
    var repairs = 0;
    repairLoop: while (true) {
      if (budget.isStopped()) break;
      var solver = makeSolver(cells, givens, givenByNum, links);
      var res = solver.count(2, nodeCap, budget);
      if (res.count === 1 && !res.capped && !res.aborted) {
        // Fresh budget check AFTER the count: the search polls
        // its budget every 512 nodes, so it can legitimately
        // finish a few nodes past the deadline with aborted false.
        // A proof that lands after the deadline is not accepted.
        if (budget.isStopped()) break;
        proven = true;
        break;
      }
      if (res.aborted) break; // budget fired mid-count: unproven, stop
      if (res.capped) {
        // Unproven, not disproven — handled BEFORE the zero-count
        // case: a capped count of 0 has NOT proven there is no
        // solution. Add clues (up to 3 givens plus 1 link), then
        // loop back and recheck. Never accept a capped result.
        // The "nothing left to add" test uses whether THIS step
        // added a link, so adding the final link is still
        // followed by a recheck.
        if (repairs >= 120) break;
        repairs++;
        var extra = shuffle(path.slice(1, N - 1));
        var addedC = 0;
        for (var ei = 0; ei < extra.length && addedC < 3; ei++) {
          if (!givens.has(extra[ei])) { addGiven(extra[ei]); addedC++; }
        }
        var addedLinkC = false;
        for (var pj = 0; pj < pathEdges.length; pj++) {
          if (!links.has(pathEdges[pj])) { links.add(pathEdges[pj]); addedLinkC = true; break; }
        }
        if (addedC === 0 && !addedLinkC) break;
        continue;
      }
      if (res.count === 0) break; // uncapped zero: proven no solution under these clues — abandon this path
      if (repairs >= 120) break;
      repairs++;
      // count >= 2, uncapped: pin a cell where an alternative
      // solution disagrees with the true one, then recheck.
      var alt = null;
      [res.first, res.second].forEach(function (cand) {
        if (!cand || alt) return;
        for (var ci = 0; ci < N; ci++) if (cand[ci] !== solution.get(cells[ci].id)) { alt = cand; break; }
      });
      var fixed = false;
      if (alt) {
        var order = shuffle(cells.map(function (c) { return c.id; }));
        for (var oi = 0; oi < order.length; oi++) {
          var cell2 = order[oi];
          if (!givens.has(cell2) && alt[cell2] !== solution.get(cell2)) { addGiven(cell2); fixed = true; break; }
        }
      }
      if (!fixed) {
        var addedL = false;
        for (var pe = 0; pe < pathEdges.length; pe++) if (!links.has(pathEdges[pe])) { links.add(pathEdges[pe]); addedL = true; break; }
        if (!addedL) break repairLoop;
      }
    }
    if (proven) {
      return { cells: cells, N: N, solution: solution, solByNum: solByNum, givens: givens, givenByNum: givenByNum, links: links, side: side, diff: diffKey, fallback: false };
    }
    // Not proven: discard this candidate entirely and try a new path.
  }
  // Budget exhausted without a proof: fall back to a preverified
  // puzzle rather than publishing an unchecked one.
  return buildFallbackPuzzle(side, diffKey, budget);
}

/* ============ Module export (browser global + CommonJS) ============ */
var SixwaysCore = {
  DIRS: DIRS,
  edgeKey: edgeKey,
  buildGrid: buildGrid,
  makeBudget: makeBudget,
  unlimitedBudget: unlimitedBudget,
  hamiltonianPath: hamiltonianPath,
  makeSolver: makeSolver,
  DIFFS: DIFFS,
  shuffle: shuffle,
  BUNDLED_PATHS: BUNDLED_PATHS,
  bundledPath: bundledPath,
  fallbackFromPath: fallbackFromPath,
  buildFallbackPuzzle: buildFallbackPuzzle,
  generate: generate
};
if (typeof module !== "undefined" && module.exports) module.exports = SixwaysCore;
