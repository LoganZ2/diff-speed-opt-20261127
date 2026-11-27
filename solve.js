// Exact, ultra-fast drop-in for makefun-diff 1.0.0.
// Preserves 100% identical Myers tie-breaking (furthest oldPos, deletion wins ties, no edge pruning).
// Algorithm: 1-to-1 unique-line LIS + provably exact forced-bridge cascade (super-gap 1D DP)
// + tiny monomorphic Myers leaves (with exact large-leaf fallback).

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;

// Compact reusable scratch buffers (aliased across disjoint phases to minimize memory/page faults).
let sCapN = 40960;
let sA = new Int32Array(sCapN);
let sB = new Int32Array(sCapN);
let sDelOnlyA = new Int32Array(sCapN);
let sInsOnlyB = new Int32Array(sCapN);
let sWork1 = new Int32Array(sCapN); // tailsJ / prefB
let sWork2 = new Int32Array(sCapN); // tailsIdx / suffB
let sWork3 = new Int32Array(sCapN); // matchI / supEnd
let sWork4 = new Int32Array(sCapN); // matchJ / supNeed
let sPrev = new Int32Array(sCapN);
let sAncI = new Int32Array(sCapN);
let sAncJ = new Int32Array(sCapN);
let sDr = new Int32Array(sCapN);
let sNeed = new Int32Array(sCapN);
let sUbPref = new Int32Array(sCapN);

let sCapId = 49152;
let sFp = new Int32Array(sCapId);
let sCntA = new Int32Array(sCapId);
let sCntB = new Int32Array(sCapId);
let sPosB = new Int32Array(sCapId);

// Small-leaf Myers fixed buffers (handles ub <= 128 with zero heap allocations).
const SMALL_MAX = 128;
const sVsPrev = new Int32Array(2 * SMALL_MAX + 6);
const sVsCurr = new Int32Array(2 * SMALL_MAX + 6);
const sVsRowBase = new Int32Array(SMALL_MAX + 2);
const sVsRowLo = new Int32Array(SMALL_MAX + 2);
const sVsRowHi = new Int32Array(SMALL_MAX + 2);
const sVsTrace = new Int32Array((SMALL_MAX + 2) * (SMALL_MAX + 2));
const sVub = new Int32Array(265);
const sRevO = new Int32Array(SMALL_MAX + 2);
const sRevP = new Int32Array(SMALL_MAX + 2);
const sRevD = new Int32Array(SMALL_MAX + 2);
const sRevI = new Int32Array(SMALL_MAX + 2);

let sChCap = 8192;
let sChO = new Int32Array(sChCap);
let sChP = new Int32Array(sChCap);
let sChD = new Int32Array(sChCap);
let sChI = new Int32Array(sChCap);
const sState = new Int32Array(3);

function ensureCapN(need) {
  if (sCapN >= need) return;
  let cap = sCapN;
  while (cap < need) cap <<= 1;
  sCapN = cap;
  sA = new Int32Array(cap);
  sB = new Int32Array(cap);
  sDelOnlyA = new Int32Array(cap);
  sInsOnlyB = new Int32Array(cap);
  sWork1 = new Int32Array(cap);
  sWork2 = new Int32Array(cap);
  sWork3 = new Int32Array(cap);
  sWork4 = new Int32Array(cap);
  sPrev = new Int32Array(cap);
  sAncI = new Int32Array(cap);
  sAncJ = new Int32Array(cap);
  sDr = new Int32Array(cap);
  sNeed = new Int32Array(cap);
  sUbPref = new Int32Array(cap);
}

function ensureCapId(need) {
  if (sCapId >= need) return;
  let cap = sCapId;
  while (cap < need) cap <<= 1;
  sCapId = cap;
  sFp = new Int32Array(cap);
  sCntA = new Int32Array(cap);
  sCntB = new Int32Array(cap);
  sPosB = new Int32Array(cap);
}

function ensureChCap(need) {
  if (sChCap >= need) return;
  let cap = sChCap;
  while (cap < need) cap <<= 1;
  const nO = new Int32Array(cap), nP = new Int32Array(cap), nD = new Int32Array(cap), nI = new Int32Array(cap);
  nO.set(sChO); nP.set(sChP); nD.set(sChD); nI.set(sChI);
  sChO = nO; sChP = nP; sChD = nD; sChI = nI; sChCap = cap;
}

function appendChange(o, p, d, ins) {
  const chLen = sState[0];
  if (chLen > 0 && sChO[chLen - 1] + sChD[chLen - 1] === o && sChP[chLen - 1] + sChI[chLen - 1] === p) {
    sChD[chLen - 1] += d;
    sChI[chLen - 1] += ins;
  } else {
    if (chLen >= sChCap) ensureChCap(chLen + 256);
    sChO[chLen] = o; sChP[chLen] = p; sChD[chLen] = d; sChI[chLen] = ins;
    sState[0] = chLen + 1;
  }
  sState[1] += d;
  sState[2] += ins;
}

function localDist(A, B, x0, x1, y0, y1, maxCap) {
  while (x0 < x1 && y0 < y1 && A[x0] === B[y0]) { x0++; y0++; }
  while (x0 < x1 && y0 < y1 && A[x1 - 1] === B[y1 - 1]) { x1--; y1--; }
  const n = x1 - x0, m = y1 - y0;
  if (n === 0) return m;
  if (m === 0) return n;
  const locMax = n + m < maxCap ? n + m : maxCap;
  const off = locMax + 2, V = sVub;
  let lx = 0, ly = 0;
  while (lx < n && ly < m && A[x0 + lx] === B[y0 + ly]) { lx++; ly++; }
  V[off] = lx;
  if (lx === n && ly === m) return 0;
  for (let d = 1; d <= locMax; d++) {
    for (let k = -d; k <= d; k += 2) {
      const rem = k > -d ? V[off + k - 1] : -1;
      const add = k < d ? V[off + k + 1] : -1;
      const byDel = rem >= 0 && rem < n ? rem + 1 : -1;
      const byIns = add >= 0 && add - k <= m ? add : -1;
      let nx = byDel >= byIns ? byDel : byIns;
      if (nx < 0) { V[off + k] = -1; continue; }
      let ny = nx - k;
      while (nx < n && ny < m && A[x0 + nx] === B[y0 + ny]) { nx++; ny++; }
      V[off + k] = nx;
      if (nx === n && ny === m) return d;
    }
  }
  return -1;
}

function solveLeafSmall(A, B, xL, xR, yL, yR, ub, prefix) {
  while (xL < xR && yL < yR && A[xL] === B[yL]) { xL++; yL++; }
  const N = xR - xL, M = yR - yL;
  if (N === 0 && M === 0) return;
  if (N === 0 || M === 0) { appendChange(prefix + xL, prefix + yL, N, M); return; }

  const delta = N - M, off = ub + 2, vLen = 2 * ub + 5;
  let Vprev = sVsPrev, Vcurr = sVsCurr;
  Vprev.fill(-2, 0, vLen);
  Vcurr.fill(-2, 0, vLen);
  Vprev[off] = 0;

  const trace = sVsTrace, rowBase = sVsRowBase, rowLo = sVsRowLo, rowHi = sVsRowHi;
  trace[0] = 1; rowBase[0] = 0; rowLo[0] = 0; rowHi[0] = 0;
  let tPos = 1, prevLo = 0, prevHi = 0, finalD = -1;

  for (let d = 1; d <= ub; d++) {
    const remD = ub - d;
    let lo = prevLo - 1, hi = prevHi + 1;
    if (lo < delta - remD) lo = delta - remD;
    if (hi > delta + remD) hi = delta + remD;
    if (((lo ^ d) & 1) !== 0) lo++;
    if (((hi ^ d) & 1) !== 0) hi--;

    const base = tPos;
    let idx = base, vi = off + lo, viEnd = off + hi, k = lo, prevRem = Vprev[vi - 1];
    for (; vi <= viEnd; vi += 2, k += 2, idx++) {
      const r = prevRem, a = Vprev[vi + 1]; prevRem = a;
      const byDel = r < N ? r + 1 : -1;
      const byIns = a - k <= M ? a : -1;
      let nx = byDel >= byIns ? byDel : byIns;
      if (nx < 0) { Vcurr[vi] = -2; trace[idx] = 0; continue; }
      let ny = nx - k;
      while (nx < N && ny < M && A[xL + nx] === B[yL + ny]) { nx++; ny++; }
      Vcurr[vi] = nx;
      trace[idx] = nx + 1;
    }
    rowBase[d] = base; rowLo[d] = lo; rowHi[d] = hi; tPos = idx;
    if (delta >= lo && delta <= hi && ((d ^ delta) & 1) === 0 && Vcurr[off + delta] === N) {
      finalD = d; break;
    }
    for (let ck = prevLo; ck <= prevHi; ck += 2) Vprev[off + ck] = -2;
    const tmp = Vprev; Vprev = Vcurr; Vcurr = tmp;
    prevLo = lo; prevHi = hi;
  }

  const revO = sRevO, revP = sRevP, revD = sRevD, revI = sRevI;
  let rLen = 0, k = delta, x = N, curO = -1, curP = -1, curD = 0, curI = 0;
  const baseO = prefix + xL, baseP = prefix + yL;
  for (let d = finalD; d >= 1; d--) {
    const pBase = rowBase[d - 1], pLo = rowLo[d - 1], pHi = rowHi[d - 1];
    const km1 = k - 1, kp1 = k + 1;
    const r = km1 >= pLo && km1 <= pHi ? trace[pBase + ((km1 - pLo) >> 1)] - 1 : -1;
    const a = kp1 >= pLo && kp1 <= pHi ? trace[pBase + ((kp1 - pLo) >> 1)] - 1 : -1;
    const byDel = r >= 0 && r < N ? r + 1 : -1;
    const byIns = a >= 0 && a - k <= M ? a : -1;
    const isDel = byDel >= byIns;
    if (x - (isDel ? byDel : byIns) > 0 && curD + curI > 0) {
      revO[rLen] = baseO + curO; revP[rLen] = baseP + curP; revD[rLen] = curD; revI[rLen] = curI; rLen++;
      curD = 0; curI = 0;
    }
    if (isDel) { curO = r; curP = r - km1; curD++; x = r; k = km1; }
    else { curO = a; curP = a - kp1; curI++; x = a; k = kp1; }
  }
  if (curD + curI > 0) {
    revO[rLen] = baseO + curO; revP[rLen] = baseP + curP; revD[rLen] = curD; revI[rLen] = curI; rLen++;
  }
  for (let j = rLen - 1; j >= 0; j--) appendChange(revO[j], revP[j], revD[j], revI[j]);
}

function solveLeafLarge(A, B, xL, xR, yL, yR, ubHint, prefix, delOnlyA, insOnlyB) {
  while (xL < xR && yL < yR && A[xL] === B[yL]) { xL++; yL++; }
  const N = xR - xL, M = yR - yL;
  if (N === 0 && M === 0) return;
  if (N === 0 || M === 0) { appendChange(prefix + xL, prefix + yL, N, M); return; }

  const ub = ubHint < N + M ? ubHint : N + M;
  const delta = N - M, off = ub + 2, vLen = 2 * ub + 5;
  let Vprev = new Int32Array(vLen).fill(-2);
  let Vcurr = new Int32Array(vLen).fill(-2);
  const rowBase = new Int32Array(ub + 2), rowLo = new Int32Array(ub + 2), rowHi = new Int32Array(ub + 2);
  const useU16 = N <= 65534;
  let traceCap = 1048576;
  let trace = useU16 ? new Uint16Array(traceCap) : new Int32Array(traceCap);

  Vprev[off] = 0; trace[0] = 1; rowBase[0] = 0; rowLo[0] = 0; rowHi[0] = 0;
  let tPos = 1, prevLo = 0, prevHi = 0, finalD = -1;
  const useH2 = delOnlyA !== null;
  const daEnd = useH2 ? delOnlyA[xR] : 0, ibEnd = useH2 ? insOnlyB[yR] : 0;

  for (let d = 1; d <= ub; d++) {
    const remD = ub - d;
    let lo = prevLo - 1, hi = prevHi + 1;
    if (lo < delta - remD) lo = delta - remD;
    if (hi > delta + remD) hi = delta + remD;
    if (((lo ^ d) & 1) !== 0) lo++;
    if (((hi ^ d) & 1) !== 0) hi--;
    const width = ((hi - lo) >> 1) + 1;
    if (tPos + width > traceCap) {
      traceCap <<= 1;
      const nt = useU16 ? new Uint16Array(traceCap) : new Int32Array(traceCap);
      nt.set(trace); trace = nt;
    }
    const base = tPos;
    let idx = base, vi = off + lo, viEnd = off + hi, k = lo, prevRem = Vprev[vi - 1];
    let nextLo = lo, nextHi = hi;
    const doPrune = useH2 && (d & 7) === 0;
    if (doPrune) { nextLo = 0x3fffffff; nextHi = -0x3fffffff; }
    for (; vi <= viEnd; vi += 2, k += 2, idx++) {
      const r = prevRem, a = Vprev[vi + 1]; prevRem = a;
      const byDel = r < N ? r + 1 : -1, byIns = a - k <= M ? a : -1;
      let nx = byDel >= byIns ? byDel : byIns;
      if (nx < 0) { Vcurr[vi] = -2; trace[idx] = 0; continue; }
      let ny = nx - k;
      while (nx < N && ny < M && A[xL + nx] === B[yL + ny]) { nx++; ny++; }
      if (nx === N && ny === M) { Vcurr[vi] = nx; trace[idx] = nx + 1; finalD = d; idx++; break; }
      if (doPrune) {
        const da = delOnlyA[xL + nx] - daEnd, ib = insOnlyB[yL + ny] - ibEnd;
        const diff = (N - nx - da) - (M - ny - ib);
        if (d + da + ib + (diff < 0 ? -diff : diff) > ub) { Vcurr[vi] = -2; trace[idx] = 0; continue; }
        if (k < nextLo) nextLo = k;
        if (k > nextHi) nextHi = k;
      }
      Vcurr[vi] = nx; trace[idx] = nx + 1;
    }
    rowBase[d] = base; rowLo[d] = lo; rowHi[d] = hi; tPos = idx;
    if (finalD >= 0 || (delta >= lo && delta <= hi && ((d ^ delta) & 1) === 0 && Vcurr[off + delta] === N)) {
      finalD = d; break;
    }
    Vprev.fill(-2, off + prevLo, off + prevHi + 1);
    const tmp = Vprev; Vprev = Vcurr; Vcurr = tmp;
    prevLo = nextLo; prevHi = nextHi;
  }

  const revO = new Int32Array(finalD), revP = new Int32Array(finalD), revD = new Int32Array(finalD), revI = new Int32Array(finalD);
  let rLen = 0, k = delta, x = N, curO = -1, curP = -1, curD = 0, curI = 0;
  const baseO = prefix + xL, baseP = prefix + yL;
  for (let d = finalD; d >= 1; d--) {
    const pBase = rowBase[d - 1], pLo = rowLo[d - 1], pHi = rowHi[d - 1];
    const km1 = k - 1, kp1 = k + 1;
    const r = km1 >= pLo && km1 <= pHi ? trace[pBase + ((km1 - pLo) >> 1)] - 1 : -1;
    const a = kp1 >= pLo && kp1 <= pHi ? trace[pBase + ((kp1 - pLo) >> 1)] - 1 : -1;
    const byDel = r >= 0 && r < N ? r + 1 : -1, byIns = a >= 0 && a - k <= M ? a : -1;
    const isDel = byDel >= byIns;
    if (x - (isDel ? byDel : byIns) > 0 && curD + curI > 0) {
      revO[rLen] = baseO + curO; revP[rLen] = baseP + curP; revD[rLen] = curD; revI[rLen] = curI; rLen++;
      curD = 0; curI = 0;
    }
    if (isDel) { curO = r; curP = r - km1; curD++; x = r; k = km1; }
    else { curO = a; curP = a - kp1; curI++; x = a; k = kp1; }
  }
  if (curD + curI > 0) {
    revO[rLen] = baseO + curO; revP[rLen] = baseP + curP; revD[rLen] = curD; revI[rLen] = curI; rLen++;
  }
  for (let j = rLen - 1; j >= 0; j--) appendChange(revO[j], revP[j], revD[j], revI[j]);
}

function solveLeaf(A, B, xL, xR, yL, yR, ubHint, prefix, delOnlyA, insOnlyB) {
  const ub = ubHint < (xR - xL) + (yR - yL) ? ubHint : (xR - xL) + (yR - yL);
  if (ub <= SMALL_MAX) solveLeafSmall(A, B, xL, xR, yL, yR, ub, prefix);
  else solveLeafLarge(A, B, xL, xR, yL, yR, ub, prefix, delOnlyA, insOnlyB);
}

function relaxDp(dp, needArr, r, rEnd, baseNeed, aL, aR, maxKCap, isFwd) {
  let eL = 0, eR = 0;
  let maxK = r - aL < aR - 1 - rEnd ? r - aL : aR - 1 - rEnd;
  if (maxK > maxKCap) maxK = maxKCap;
  for (let K = 1; K <= maxK; K++) {
    if (K > 1) {
      const nl = needArr[r - K + 1], nr = needArr[rEnd + K - 1];
      if (nl < 0 || nr < 0) break;
      eL += nl; eR += nr;
    }
    const c1 = baseNeed - eL - eR;
    const b = c1 < K << 1 ? c1 : K << 1;
    if (b > 0) {
      if (isFwd) {
        const val = dp[r - K - aL] + b, ei = rEnd + K - aL;
        if (val > dp[ei]) dp[ei] = val;
      } else {
        const val = dp[rEnd + K + 1 - aL] + b, si = r - K + 1 - aL;
        if (val > dp[si]) dp[si] = val;
      }
    }
    if (K << 1 >= c1) break;
  }
}

function computePrefSuffDp(needArr, supEnd, supNeed, aL, aR, useSup, maxKCap) {
  const len = aR - aL + 1;
  const prefB = sWork1, suffB = sWork2;
  prefB.fill(0, 0, len);
  suffB.fill(0, 0, len);

  for (let r = aL + 1; r < aR; r++) {
    const ri = r - aL;
    if (prefB[ri] < prefB[ri - 1]) prefB[ri] = prefB[ri - 1];
    const need = needArr[r];
    if (need <= 0) continue;
    relaxDp(prefB, needArr, r, r, need, aL, aR, maxKCap, true);
    if (useSup) {
      const rEnd = supEnd[r];
      if (rEnd > r && rEnd < aR - 1) relaxDp(prefB, needArr, r, rEnd, supNeed[r], aL, aR, maxKCap, true);
    }
  }
  for (let i = 1; i < len; i++) if (prefB[i] < prefB[i - 1]) prefB[i] = prefB[i - 1];

  for (let r = aR - 1; r > aL; r--) {
    const ri = r - aL;
    if (suffB[ri] < suffB[ri + 1]) suffB[ri] = suffB[ri + 1];
    const need = needArr[r];
    if (need <= 0) continue;
    relaxDp(suffB, needArr, r, r, need, aL, aR, maxKCap, false);
    if (useSup) {
      const rEnd = supEnd[r];
      if (rEnd > r && rEnd < aR - 1) relaxDp(suffB, needArr, r, rEnd, supNeed[r], aL, aR, maxKCap, false);
    }
  }
  for (let i = len - 2; i >= 0; i--) if (suffB[i] < suffB[i + 1]) suffB[i] = suffB[i + 1];
}

function decomposeAndSolve(A, B, ancI, ancJ, drArr, needArr, ubPref, delOnlyA, insOnlyB, aL, aR, depth, prefix) {
  const ubSub = ubPref[aR] - ubPref[aL];
  if (ubSub === 0) return;
  if (ubSub <= 48 || aR - aL <= 4) {
    solveLeaf(A, B, ancI[aL] + 1, ancI[aR], ancJ[aL] + 1, ancJ[aR], ubSub, prefix, delOnlyA, insOnlyB);
    return;
  }

  const daSub = delOnlyA[ancI[aL] + 1] - delOnlyA[ancI[aR]];
  const ibSub = insOnlyB[ancJ[aL] + 1] - insOnlyB[ancJ[aR]];
  computePrefSuffDp(needArr, sWork3, sWork4, aL, aR, depth === 0, depth === 0 ? 24 : 12);

  const prefB = sWork1, suffB = sWork2;
  const bridges = [];
  let c = aL + 1;
  while (c < aR) {
    let cEnd = c;
    while (cEnd + 1 < aR && needArr[cEnd] === 0) cEnd++;
    const K = cEnd - c + 1;
    if ((K << 1) + daSub + ibSub + prefB[c - 1 - aL] + suffB[cEnd + 1 - aL] > ubSub) {
      bridges.push(c, cEnd);
    }
    c = cEnd + 1;
  }

  if (bridges.length === 0) {
    solveLeaf(A, B, ancI[aL] + 1, ancI[aR], ancJ[aL] + 1, ancJ[aR], ubSub, prefix, delOnlyA, insOnlyB);
    return;
  }

  let prevA = aL;
  for (let bi = 0; bi < bridges.length; bi += 2) {
    const bc = bridges[bi], bcEnd = bridges[bi + 1];
    decomposeAndSolve(A, B, ancI, ancJ, drArr, needArr, ubPref, delOnlyA, insOnlyB, prevA, bc, depth + 1, prefix);
    for (let r = bc; r < bcEnd; r++) {
      if (drArr[r] > 0) solveLeaf(A, B, ancI[r] + 1, ancI[r + 1], ancJ[r] + 1, ancJ[r + 1], drArr[r], prefix, null, null);
    }
    prevA = bcEnd;
  }
  decomposeAndSolve(A, B, ancI, ancJ, drArr, needArr, ubPref, delOnlyA, insOnlyB, prevA, aR, depth + 1, prefix);
}

function internLines(pa, pb, prefix, n, m, N, M, hasBareA, hasBareB) {
  const A = sA, B = sB, fp = sFp;
  const map = new Map();
  let nextId = 1; // Reserve 0 for empty line ""
  fp[0] = -1;
  const normN = hasBareA ? N - 1 : N;
  const normM = hasBareB ? M - 1 : M;

  for (let i = 0; i < normN; i++) {
    const s = pa[prefix + i];
    if (s.length === 0) { A[i] = 0; continue; }
    let id = map.get(s);
    if (id === undefined) { id = nextId++; map.set(s, id); fp[id] = i; }
    A[i] = id;
  }
  let pred = 0;
  for (let j = 0; j < normM; j++) {
    const s = pb[prefix + j];
    if (pred < normN && s === pa[prefix + pred]) { B[j] = A[pred++]; continue; }
    if (s.length === 0) { B[j] = 0; continue; }
    let id = map.get(s);
    if (id === undefined) { id = nextId++; map.set(s, id); fp[id] = -1; }
    else { const p = fp[id]; if (p >= 0) pred = p + 1; }
    B[j] = id;
  }
  if (hasBareA && hasBareB) {
    const idA = nextId++;
    A[N - 1] = idA;
    B[M - 1] = pa[n - 1] === pb[m - 1] ? idA : nextId++;
  } else if (hasBareA) A[N - 1] = nextId++;
  else if (hasBareB) B[M - 1] = nextId++;
  return nextId;
}

function buildLis(A, B, N, M, nextId) {
  const cntA = sCntA, cntB = sCntB, posB = sPosB;
  cntA.fill(0, 0, nextId);
  cntB.fill(0, 0, nextId);
  for (let i = 0; i < N; i++) cntA[A[i]]++;
  for (let j = 0; j < M; j++) { const id = B[j]; cntB[id]++; posB[id] = j; }

  const delOnlyA = sDelOnlyA, insOnlyB = sInsOnlyB;
  delOnlyA[N] = 0; insOnlyB[M] = 0;
  for (let i = N - 1; i >= 0; i--) delOnlyA[i] = delOnlyA[i + 1] + (cntB[A[i]] === 0 ? 1 : 0);
  for (let j = M - 1; j >= 0; j--) insOnlyB[j] = insOnlyB[j + 1] + (cntA[B[j]] === 0 ? 1 : 0);

  const tailsJ = sWork1, tailsIdx = sWork2, matchI = sWork3, matchJ = sWork4, prev = sPrev;
  let mCnt = 0, lisLen = 0;
  for (let i = 0; i < N; i++) {
    const id = A[i];
    if (cntA[id] === 1 && cntB[id] === 1) {
      const j = posB[id], idx = mCnt++;
      matchI[idx] = i; matchJ[idx] = j;
      let lo = 0, hi = lisLen;
      while (lo < hi) { const mid = (lo + hi) >>> 1; if (tailsJ[mid] < j) lo = mid + 1; else hi = mid; }
      prev[idx] = lo > 0 ? tailsIdx[lo - 1] : -1;
      tailsJ[lo] = j; tailsIdx[lo] = idx;
      if (lo === lisLen) lisLen++;
    }
  }

  const ancI = sAncI, ancJ = sAncJ;
  ancI[0] = -1; ancJ[0] = -1;
  let cur = lisLen > 0 ? tailsIdx[lisLen - 1] : -1;
  for (let k = lisLen; k >= 1; k--) { ancI[k] = matchI[cur]; ancJ[k] = matchJ[cur]; cur = prev[cur]; }
  ancI[lisLen + 1] = N; ancJ[lisLen + 1] = M;
  return lisLen;
}

function buildGaps(A, B, lisLen) {
  const ancI = sAncI, ancJ = sAncJ, drArr = sDr, needArr = sNeed, ubPref = sUbPref;
  const delOnlyA = sDelOnlyA, insOnlyB = sInsOnlyB;
  ubPref[0] = 0;
  for (let r = 0; r <= lisLen; r++) {
    const x0 = ancI[r] + 1, x1 = ancI[r + 1], y0 = ancJ[r] + 1, y1 = ancJ[r + 1];
    let d = 0, exact = true;
    if (x0 === x1) d = y1 - y0;
    else if (y0 === y1) d = x1 - x0;
    else {
      const ld = localDist(A, B, x0, x1, y0, y1, 128);
      if (ld >= 0) d = ld;
      else { d = x1 - x0 + (y1 - y0); exact = false; }
    }
    drArr[r] = d;
    needArr[r] = exact ? d - (delOnlyA[x0] - delOnlyA[x1]) - (insOnlyB[y0] - insOnlyB[y1]) : -1;
    ubPref[r + 1] = ubPref[r] + d;
  }

  const supEnd = sWork3, supNeed = sWork4;
  for (let r = 1; r < lisLen; r++) {
    supEnd[r] = 0;
    const need = needArr[r];
    if (need <= 0) continue;
    const lim = r + 4 < lisLen ? r + 4 : lisLen - 1;
    let rEnd = -1;
    for (let t = r + 1; t <= lim; t++) { if (needArr[t] > 0) { rEnd = t; break; } }
    if (rEnd > r && ancI[rEnd + 1] - ancI[r] <= 128 && ancJ[rEnd + 1] - ancJ[r] <= 128) {
      const sd = localDist(A, B, ancI[r] + 1, ancI[rEnd + 1], ancJ[r] + 1, ancJ[rEnd + 1], 64);
      if (sd >= 0) {
        const sNeed = sd - (delOnlyA[ancI[r] + 1] - delOnlyA[ancI[rEnd + 1]]) - (insOnlyB[ancJ[r] + 1] - insOnlyB[ancJ[rEnd + 1]]);
        if (sNeed > need) { supEnd[r] = rEnd; supNeed[r] = sNeed; }
      }
    }
  }
}

function formatPatch(pa, pb, n, m, oldBare, newBare, chO, chP, chD, chI, chLen, deleted, inserted) {
  if (chLen === 0) return `${FORMAT} old=${n} new=${m} hunks=0 deleted=0 inserted=0\n`;

  let hCount = 1;
  for (let i = 1; i < chLen; i++) {
    if (chO[i] - (chO[i - 1] + chD[i - 1]) > 2 * CONTEXT) hCount++;
  }

  const oldLastBare = oldBare ? n - 1 : -1;
  const newLastBare = newBare ? m - 1 : -1;
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hCount} deleted=${deleted} inserted=${inserted}\n`];

  let cStart = 0;
  while (cStart < chLen) {
    let cEnd = cStart + 1;
    while (cEnd < chLen && chO[cEnd] - (chO[cEnd - 1] + chD[cEnd - 1]) <= 2 * CONTEXT) cEnd++;

    const firstO = chO[cStart], firstP = chP[cStart];
    const lastIdx = cEnd - 1;
    const lastOEnd = chO[lastIdx] + chD[lastIdx], lastPEnd = chP[lastIdx] + chI[lastIdx];
    const oldStart = firstO > CONTEXT ? firstO - CONTEXT : 0;
    const newStart = firstP - (firstO - oldStart);
    const remAfter = n - lastOEnd;
    const after = remAfter < CONTEXT ? remAfter : CONTEXT;
    const oldEnd = lastOEnd + after, newEnd = lastPEnd + after;

    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);

    let at = oldStart;
    for (let ci = cStart; ci < cEnd; ci++) {
      const co = chO[ci], cp = chP[ci], cd = chD[ci], ins = chI[ci];
      for (; at < co; at++) out.push(at === oldLastBare ? `=${pa[at]}\n%\n` : `=${pa[at]}\n`);
      for (let i = 0; i < cd; i++) { const idx = co + i; out.push(idx === oldLastBare ? `-${pa[idx]}\n%\n` : `-${pa[idx]}\n`); }
      for (let i = 0; i < ins; i++) { const idx = cp + i; out.push(idx === newLastBare ? `+${pb[idx]}\n%\n` : `+${pb[idx]}\n`); }
      at = co + cd;
    }
    for (; at < oldEnd; at++) out.push(at === oldLastBare ? `=${pa[at]}\n%\n` : `=${pa[at]}\n`);
    cStart = cEnd;
  }

  return out.join('');
}

export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldStr = input.old, newStr = input.new;
  if (oldStr === newStr) {
    let n = 0;
    const len = oldStr.length;
    if (len > 0) {
      let pos = 0;
      while (pos < len) {
        const nl = oldStr.indexOf('\n', pos);
        n++;
        if (nl === -1) break;
        pos = nl + 1;
      }
    }
    return `${FORMAT} old=${n} new=${n} hunks=0 deleted=0 inserted=0\n`;
  }

  const pa = oldStr.split('\n');
  const pb = newStr.split('\n');
  const oldBare = oldStr.length > 0 && pa[pa.length - 1] !== '';
  const newBare = newStr.length > 0 && pb[pb.length - 1] !== '';
  const n = oldBare ? pa.length : pa.length - 1;
  const m = newBare ? pb.length : pb.length - 1;
  const oldLastBare = oldBare ? n - 1 : -1;
  const newLastBare = newBare ? m - 1 : -1;

  let prefix = 0;
  const minNM = n < m ? n : m;
  while (prefix < minNM && pa[prefix] === pb[prefix] && (prefix === oldLastBare) === (prefix === newLastBare)) prefix++;
  let suffix = 0;
  const maxSuf = minNM - prefix;
  while (
    suffix < maxSuf &&
    pa[n - 1 - suffix] === pb[m - 1 - suffix] &&
    (n - 1 - suffix === oldLastBare) === (m - 1 - suffix === newLastBare)
  ) suffix++;

  const N = n - prefix - suffix, M = m - prefix - suffix;
  if (N === 0 && M === 0) return `${FORMAT} old=${n} new=${m} hunks=0 deleted=0 inserted=0\n`;
  if (N === 0 || M === 0) {
    sChO[0] = prefix; sChP[0] = prefix; sChD[0] = N; sChI[0] = M;
    return formatPatch(pa, pb, n, m, oldBare, newBare, sChO, sChP, sChD, sChI, 1, N, M);
  }

  const maxNM = N > M ? N : M;
  ensureCapN(maxNM + 4);
  ensureCapId(N + M + 6);
  sState[0] = 0; sState[1] = 0; sState[2] = 0;

  const nextId = internLines(pa, pb, prefix, n, m, N, M, oldBare && suffix === 0, newBare && suffix === 0);
  if (N + M <= 96) {
    solveLeaf(sA, sB, 0, N, 0, M, N + M, prefix, null, null);
    return formatPatch(pa, pb, n, m, oldBare, newBare, sChO, sChP, sChD, sChI, sState[0], sState[1], sState[2]);
  }

  const lisLen = buildLis(sA, sB, N, M, nextId);
  buildGaps(sA, sB, lisLen);
  decomposeAndSolve(sA, sB, sAncI, sAncJ, sDr, sNeed, sUbPref, sDelOnlyA, sInsOnlyB, 0, lisLen + 1, 0, prefix);
  return formatPatch(pa, pb, n, m, oldBare, newBare, sChO, sChP, sChD, sChI, sState[0], sState[1], sState[2]);
}
