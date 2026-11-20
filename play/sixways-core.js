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

/* ============ Phase 2: seeded RNG (SplitMix64) ============ */
// Bit-exact port of the native app's SeededRNG + DeterministicRandom
// helpers. Swift's UInt64 arithmetic is mirrored with BigInt, so a
// seed produces the identical stream in JS as in the app — which is
// what lets the web Daily Race deal the SAME board as iOS for a day.
var SEED_SALT = 0x5369787761797321n; // DailyRacePolicy salt ("Sixways!")
function makeSeededRNG(seed) {
  var state = BigInt.asUintN(64, seed);
  return {
    next: function () {
      state = BigInt.asUintN(64, state + 0x9E3779B97F4A7C15n);
      var z = state;
      z = BigInt.asUintN(64, (z ^ (z >> 30n)) * 0xBF58476D1CE4E5B9n);
      z = BigInt.asUintN(64, (z ^ (z >> 27n)) * 0x94D049BB133111EBn);
      return z ^ (z >> 31n);
    },
    getState: function () { return state; },
    setState: function (s) { state = BigInt.asUintN(64, s); }
  };
}
// Lemire's unbiased draw in 0..<bound, as in DeterministicRandom.swift.
function detNextBelow(rng, bound) {
  var b = BigInt(bound);
  var x = rng.next();
  var product = x * b;
  var low = BigInt.asUintN(64, product);
  var high = product >> 64n;
  if (low < b) {
    var threshold = BigInt.asUintN(64, -b) % b;
    while (low < threshold) {
      x = rng.next();
      product = x * b;
      low = BigInt.asUintN(64, product);
      high = product >> 64n;
    }
  }
  return Number(high);
}
function detUnitDouble(rng) {
  return Number(rng.next() >> 11n) * Math.pow(2, -53);
}
function detShuffled(arr, rng) {
  var result = arr.slice();
  if (result.length <= 1) return result;
  for (var i = result.length - 1; i >= 1; i--) {
    var j = detNextBelow(rng, i + 1);
    if (i !== j) { var t = result[i]; result[i] = result[j]; result[j] = t; }
  }
  return result;
}

/* ============ Phase 2: seeded Hamiltonian path ============ */
// Port of HamiltonianPathFinder's RNG-threaded form: the start cell
// is drawn from the outer stream, the search runs on a copy, and the
// copy's state is written back after each attempt — one continuous
// stream across attempts, exactly as in Swift.
function seededHamiltonianPath(cells, rng) {
  var N = cells.length;
  for (var attempt = 0; attempt < 300; attempt++) {
    var start = detNextBelow(rng, N);
    var searchRng = makeSeededRNG(rng.getState());
    var search = { visited: new Uint8Array(N), path: [start], nodes: 0 };
    search.visited[start] = 1;
    var found = seededDfs(cells, search, searchRng, start);
    rng.setState(searchRng.getState());
    if (found && search.path.length === N) return search.path.slice();
  }
  return null;
}
function seededDfs(cells, search, rng, cell) {
  var N = cells.length;
  if (search.path.length === N) return true;
  search.nodes++;
  if (search.nodes > 60000) return false;
  var cands = [];
  var nbrs = cells[cell].nbrs;
  for (var i = 0; i < nbrs.length; i++) {
    var nb = nbrs[i];
    if (search.visited[nb]) continue;
    var deg = 0;
    var nn = cells[nb].nbrs;
    for (var j = 0; j < nn.length; j++) if (!search.visited[nn[j]]) deg++;
    cands.push({ cell: nb, deg: deg, rnd: detUnitDouble(rng) });
  }
  cands.sort(function (a, b) { return (a.deg - b.deg) || (a.rnd - b.rnd); });
  for (var k = 0; k < cands.length; k++) {
    var c = cands[k].cell;
    search.visited[c] = 1; search.path.push(c);
    if (seededDfs(cells, search, rng, c)) return true;
    search.path.pop(); search.visited[c] = 0;
    if (search.nodes > 60000) return false;
  }
  return false;
}

/* ============ Phase 2: seeded carve-and-prove ============ */
// PuzzleGenerator.carveAndProve with the seeded stream: identical
// structure to generate()'s carve above, with every shuffle drawn
// from the day's RNG instead of Math.random, and an unlimited
// budget — the daily board may depend only on deterministic node
// caps, never on wall-clock time.
function carveAndProveSeeded(cells, path, side, diffKey, rng, isFallback) {
  var spec = DIFFS[diffKey];
  var N = cells.length;
  var cap = Math.max(150000, spec.cap - (side - 4) * 125000);
  var budget = unlimitedBudget();
  var solution = new Map(), solByNum = new Array(N + 1);
  path.forEach(function (cell, i) { solution.set(cell, i + 1); solByNum[i + 1] = cell; });
  var givens = new Map(), givenByNum = new Map();
  function addGiven(cell) {
    var n = solution.get(cell);
    givens.set(cell, n); givenByNum.set(n, cell);
  }
  addGiven(path[0]); addGiven(path[N - 1]);
  var midCells = detShuffled(path.slice(1, N - 1), rng);
  var wantGivens = Math.max(2, Math.round(N * spec.givenFrac));
  for (var i = 0; i < midCells.length && givens.size < wantGivens; i++) addGiven(midCells[i]);

  var pathEdges = [];
  for (var e = 0; e < N - 1; e++) pathEdges.push(edgeKey(path[e], path[e + 1]));
  var links = new Set();
  var shuffledEdges = detShuffled(pathEdges.slice(), rng);
  var wantLinks = Math.round((N - 1) * spec.linkFrac);
  for (var l = 0; l < shuffledEdges.length && links.size < wantLinks; l++) links.add(shuffledEdges[l]);

  var proven = false;
  var repairs = 0;
  repairLoop: while (true) {
    var solver = makeSolver(cells, givens, givenByNum, links);
    var res = solver.count(2, cap, budget);
    if (res.count === 1 && !res.capped && !res.aborted) { proven = true; break; }
    if (res.aborted) break;
    if (res.capped) {
      if (repairs >= 120) break;
      repairs++;
      var extra = detShuffled(path.slice(1, N - 1), rng);
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
    if (res.count === 0) break;
    if (repairs >= 120) break;
    repairs++;
    var alt = null;
    [res.first, res.second].forEach(function (cand) {
      if (!cand || alt) return;
      for (var ci = 0; ci < N; ci++) if (cand[ci] !== solution.get(cells[ci].id)) { alt = cand; break; }
    });
    var fixed = false;
    if (alt) {
      var order = detShuffled(cells.map(function (c) { return c.id; }), rng);
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
  if (!proven) return null;
  return { cells: cells, N: N, solution: solution, solByNum: solByNum, givens: givens, givenByNum: givenByNum, links: links, side: side, diff: diffKey, fallback: !!isFallback };
}

/* ============ Phase 2: the Daily Race ============ */
var DAILY_SIDE = 4;
var DAILY_DIFF = "medium";
// Days since the epoch (1 Dec 2026) in the player's LOCAL calendar:
// local Y/M/D components differenced as calendar days, so DST never
// shifts the count. Mirrors DailyRacePolicy.dayNumber.
function dayNumberFor(date) {
  var epoch = Date.UTC(2026, 11, 1);
  var d = Date.UTC(date.getFullYear(), date.getMonth(), date.getDate());
  return Math.round((d - epoch) / 86400000);
}
// DailyRacePolicy.seed(forDayNumber:): the day scrambled through
// the SplitMix64 finalizer with the fixed salt.
function dailySeed(day) {
  var rng = makeSeededRNG(BigInt.asUintN(64, BigInt(day)) ^ SEED_SALT);
  return rng.next();
}
// PuzzleGenerator.generateDaily: seeded pipeline, unlimited budget,
// seeded bundled-path carve, then the by-construction floor.
function generateDaily(day) {
  var rng = makeSeededRNG(dailySeed(day));
  var cells = buildGrid(DAILY_SIDE);
  for (var attempt = 0; attempt < 6; attempt++) {
    var path = seededHamiltonianPath(cells, rng);
    if (!path) continue;
    var p = carveAndProveSeeded(cells, path, DAILY_SIDE, DAILY_DIFF, rng, false);
    if (p) return p;
  }
  var bundled = bundledPath(DAILY_SIDE, cells);
  if (bundled) {
    var carved = carveAndProveSeeded(cells, bundled, DAILY_SIDE, DAILY_DIFF, rng, true);
    if (carved) return carved;
    var floor = fallbackFromPath(cells, bundled, DAILY_SIDE, DAILY_DIFF);
    floor.unranked = true; // the app's floor is unranked in every mode
    return floor;
  }
  return null;
}

/* ============ Phase 2: daily history (DailyRacePolicy) ============ */
// Pure port of DailyRacePolicy's recording rules: write-once per
// day, streaks frozen onto each result at recording time, backfilled
// days mint nothing. History shape:
// { results: {day: {day, elapsed, score, hintsUsed, streak}},
//   currentStreak, lastCompletedDay, totalCompleted, bestTime }
function emptyDailyHistory() {
  return { results: {}, currentStreak: 0, lastCompletedDay: null, totalCompleted: 0, bestTime: null };
}
function streakEndingAt(day, results) {
  var streak = 0, d = day;
  while (results[d] != null) { streak++; d--; }
  return streak;
}
function recordingDaily(history, result) {
  if (history.results[result.day] != null) return history;
  var h = { results: Object.assign({}, history.results),
            currentStreak: history.currentStreak,
            lastCompletedDay: history.lastCompletedDay,
            totalCompleted: history.totalCompleted,
            bestTime: history.bestTime };
  var stamped = { day: result.day, elapsed: result.elapsed, score: result.score,
                  hintsUsed: result.hintsUsed, streak: 0 };
  h.results[result.day] = stamped;
  stamped.streak = streakEndingAt(result.day, h.results);
  if (h.lastCompletedDay != null) {
    var last = h.lastCompletedDay;
    if (result.day === last + 1) h.currentStreak += 1;
    else if (result.day > last + 1) h.currentStreak = 1;
    h.lastCompletedDay = Math.max(last, result.day);
  } else {
    h.currentStreak = 1;
    h.lastCompletedDay = result.day;
  }
  var backfilled = history.lastCompletedDay != null && result.day < history.lastCompletedDay;
  if (!backfilled) {
    h.totalCompleted += 1;
    h.bestTime = h.bestTime == null ? result.elapsed : Math.min(h.bestTime, result.elapsed);
  }
  return h;
}
function effectiveStreak(history, today) {
  if (history.lastCompletedDay == null || history.lastCompletedDay < today - 1) return 0;
  return history.currentStreak;
}

/* ============ Phase 2: scoring (ScoreStore) ============ */
// Ruled 2026-11-19 and mirrored exactly: par by size x difficulty,
// hint -150, charged mistake -25, +2 per second under the par time
// capped at +25% of par, no penalty past par, floor 0.
var PAR_TABLE = {
  36: { easy: 600, medium: 1000, hard: 1400, expert: 1800 },
  60: { easy: 1000, medium: 1700, hard: 2400, expert: 3000 },
  90: { easy: 1500, medium: 2500, hard: 3500, expert: 4500 }
};
var HINT_COST = 150, MISTAKE_COST = 25;
function parFor(count, diffKey) {
  var row = PAR_TABLE[count];
  return row && row[diffKey] != null ? row[diffKey] : 1000;
}
function parTimeFor(count, diffKey) { return parFor(count, diffKey) * 0.24; }
function computeScore(count, diffKey, hints, mistakes, elapsed) {
  var par = parFor(count, diffKey);
  var parTime = parTimeFor(count, diffKey);
  var score = par - HINT_COST * hints - MISTAKE_COST * mistakes;
  if (elapsed < parTime) {
    var bonus = Math.trunc(parTime - elapsed) * 2;
    score += Math.min(Math.floor(par / 4), bonus);
  }
  return Math.max(0, score);
}
// The app's conflict rule (GameSession.conflicts): consecutive
// placed numbers that are not neighbours, and link endpoints whose
// values are not consecutive. values: array of number per cell id,
// 0 when empty (givens included). Returns a Set of cell ids.
function conflictCells(cells, values, links) {
  var bad = new Set();
  var N = cells.length;
  var cellOfNum = new Array(N + 1).fill(-1);
  for (var i = 0; i < N; i++) if (values[i] !== 0) cellOfNum[values[i]] = i;
  for (var n = 1; n < N; n++) {
    var a = cellOfNum[n], b = cellOfNum[n + 1];
    if (a >= 0 && b >= 0 && cells[a].nbrs.indexOf(b) === -1) { bad.add(a); bad.add(b); }
  }
  links.forEach(function (ek) {
    var parts = ek.split("-"), x = +parts[0], y = +parts[1];
    var va = values[x], vb = values[y];
    if (va !== 0 && vb !== 0 && Math.abs(va - vb) !== 1) { bad.add(x); bad.add(y); }
  });
  return bad;
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
  generate: generate,
  makeSeededRNG: makeSeededRNG,
  detNextBelow: detNextBelow,
  detUnitDouble: detUnitDouble,
  detShuffled: detShuffled,
  seededHamiltonianPath: seededHamiltonianPath,
  carveAndProveSeeded: carveAndProveSeeded,
  dailySeed: dailySeed,
  dayNumberFor: dayNumberFor,
  generateDaily: generateDaily,
  emptyDailyHistory: emptyDailyHistory,
  streakEndingAt: streakEndingAt,
  recordingDaily: recordingDaily,
  effectiveStreak: effectiveStreak,
  PAR_TABLE: PAR_TABLE,
  parFor: parFor,
  parTimeFor: parTimeFor,
  computeScore: computeScore,
  conflictCells: conflictCells
};
if (typeof module !== "undefined" && module.exports) module.exports = SixwaysCore;
