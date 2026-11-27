// Exact, ultra-fast drop-in for makefun-diff 1.0.0.
// Preserves 100% identical Myers tie-breaking (furthest oldPos, deletion wins ties, no edge pruning).

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;

// Reusable scratch buffers (completely overwritten/zeroed per call; zero case data cached).
let sVprev = new Int32Array(16384);
let sVcurr = new Int32Array(16384);
let sTraceU16 = new Uint16Array(1024 * 1024);
const sVub = new Int32Array(265);
const sOutBounds = new Int32Array(3);

function localDist(A, B, x0, x1, y0, y1, Vub, maxCap) {
  while (x0 < x1 && y0 < y1 && A[x0] === B[y0]) {
    x0++;
    y0++;
  }
  while (x0 < x1 && y0 < y1 && A[x1 - 1] === B[y1 - 1]) {
    x1--;
    y1--;
  }
  const n = x1 - x0;
  const m = y1 - y0;
  if (n === 0) return m;
  if (m === 0) return n;
  const locMax = n + m < maxCap ? n + m : maxCap;
  const locOff = locMax + 2;
  let lx = 0;
  let ly = 0;
  while (lx < n && ly < m && A[x0 + lx] === B[y0 + ly]) {
    lx++;
    ly++;
  }
  Vub[locOff] = lx;
  if (lx === n && ly === m) return 0;
  for (let d = 1; d <= locMax; d++) {
    for (let k = -d; k <= d; k += 2) {
      const rem = k > -d ? Vub[locOff + k - 1] : -1;
      const add = k < d ? Vub[locOff + k + 1] : -1;
      const byDel = rem >= 0 && rem < n ? rem + 1 : -1;
      const byIns = add >= 0 && add - k <= m ? add : -1;
      let nx = byDel >= byIns ? byDel : byIns;
      if (nx < 0) {
        Vub[locOff + k] = -1;
        continue;
      }
      let ny = nx - k;
      while (nx < n && ny < m && A[x0 + nx] === B[y0 + ny]) {
        nx++;
        ny++;
      }
      Vub[locOff + k] = nx;
      if (nx === n && ny === m) return d;
    }
  }
  return -1;
}

/**
 * Computes a valid upper bound `ub >= D*` and provably admissible suffix lower bounds:
 * - delOnlyA / insOnlyB: lines absent from the opposite text
 * - lisRemA / lisRemB: 1-to-1 unique-line LIS divergence
 * - exTotA / exTotB: private disjoint K-anchor region bonuses (min(needTot, 2*K))
 */
function prepareBounds(A, B, N, M, nextId) {
  const cntA = new Int32Array(nextId);
  const cntB = new Int32Array(nextId);
  const posB = new Int32Array(nextId);
  for (let i = 0; i < N; i++) cntA[A[i]]++;
  for (let j = 0; j < M; j++) {
    const id = B[j];
    cntB[id]++;
    posB[id] = j;
  }

  const delOnlyA = new Int32Array(N + 1);
  const insOnlyB = new Int32Array(M + 1);
  for (let i = N - 1; i >= 0; i--) delOnlyA[i] = delOnlyA[i + 1] + (cntB[A[i]] === 0 ? 1 : 0);
  for (let j = M - 1; j >= 0; j--) insOnlyB[j] = insOnlyB[j + 1] + (cntA[B[j]] === 0 ? 1 : 0);

  // LIS of 1-to-1 unique lines (cntA === 1 && cntB === 1)
  const maxL = N < M ? N : M;
  const tailsJ = new Int32Array(maxL + 1);
  const tailsIdx = new Int32Array(maxL + 1);
  const matchI = new Int32Array(maxL);
  const matchJ = new Int32Array(maxL);
  const prev = new Int32Array(maxL);
  let mCnt = 0;
  let lisLen = 0;
  for (let i = 0; i < N; i++) {
    const id = A[i];
    if (cntA[id] === 1 && cntB[id] === 1) {
      const j = posB[id];
      const idx = mCnt++;
      matchI[idx] = i;
      matchJ[idx] = j;
      let lo = 0;
      let hi = lisLen;
      while (lo < hi) {
        const mid = (lo + hi) >>> 1;
        if (tailsJ[mid] < j) lo = mid + 1;
        else hi = mid;
      }
      prev[idx] = lo > 0 ? tailsIdx[lo - 1] : -1;
      tailsJ[lo] = j;
      tailsIdx[lo] = idx;
      if (lo === lisLen) lisLen++;
    }
  }

  const ancI = new Int32Array(lisLen + 2);
  const ancJ = new Int32Array(lisLen + 2);
  ancI[0] = -1;
  ancJ[0] = -1;
  let cur = lisLen > 0 ? tailsIdx[lisLen - 1] : -1;
  for (let k = lisLen; k >= 1; k--) {
    ancI[k] = matchI[cur];
    ancJ[k] = matchJ[cur];
    cur = prev[cur];
  }
  ancI[lisLen + 1] = N;
  ancJ[lisLen + 1] = M;

  const lisRemA = new Int32Array(N + 1);
  const lisRemB = new Int32Array(M + 1);
  for (let k = 1; k <= lisLen; k++) {
    lisRemA[ancI[k]] = 1;
    lisRemB[ancJ[k]] = 1;
  }
  for (let i = N - 1; i >= 0; i--) lisRemA[i] += lisRemA[i + 1];
  for (let j = M - 1; j >= 0; j--) lisRemB[j] += lisRemB[j + 1];

  // Pass 1: exact local edit distances between consecutive LIS anchors -> tight upper bound `ub`
  const drArr = new Int32Array(lisLen + 1);
  let ub = 0;
  for (let r = 0; r <= lisLen; r++) {
    const x0 = ancI[r] + 1;
    const x1 = ancI[r + 1];
    const y0 = ancJ[r] + 1;
    const y1 = ancJ[r + 1];
    const d = localDist(A, B, x0, x1, y0, y1, sVub, 128);
    if (d >= 0) {
      drArr[r] = d;
      ub += d;
    } else {
      drArr[r] = -1;
      ub += x1 - x0 + (y1 - y0);
    }
  }
  if (ub > N + M) ub = N + M;

  // Pass 2: private disjoint K-anchor regions (super-gap merging + min(needTot, 2*K) bonus)
  const exTotA = new Int32Array(N + 1);
  const exTotB = new Int32Array(M + 1);
  if (lisLen >= 2) {
    const zeroLeft = new Int32Array(lisLen + 1);
    for (let r = 1; r <= lisLen; r++) zeroLeft[r] = drArr[r - 1] === 0 ? zeroLeft[r - 1] + 1 : 0;
    const zeroRight = new Int32Array(lisLen + 1);
    for (let r = lisLen - 1; r >= 0; r--) zeroRight[r] = drArr[r + 1] === 0 ? zeroRight[r + 1] + 1 : 0;

    let lastUsedRightAnc = 0;
    for (let r = 1; r < lisLen; r++) {
      if (drArr[r] <= 0) continue;
      let rEnd = r;
      let sumDr = drArr[r];
      while (rEnd + 1 < lisLen && zeroRight[rEnd] <= 1) {
        const nextR = rEnd + 1 + zeroRight[rEnd];
        if (
          nextR < lisLen &&
          drArr[nextR] > 0 &&
          sumDr + drArr[nextR] <= 48 &&
          ancI[nextR + 1] - ancI[r] <= 128 &&
          ancJ[nextR + 1] - ancJ[r] <= 128
        ) {
          rEnd = nextR;
          sumDr += drArr[nextR];
        } else {
          break;
        }
      }
      let dr = drArr[r];
      if (rEnd > r) {
        const sd = localDist(A, B, ancI[r] + 1, ancI[rEnd + 1], ancJ[r] + 1, ancJ[rEnd + 1], sVub, 64);
        if (sd >= 0) dr = sd;
        else rEnd = r;
      }
      const x0 = ancI[r] + 1;
      const x1 = ancI[rEnd + 1];
      const y0 = ancJ[r] + 1;
      const y1 = ancJ[rEnd + 1];
      const needTot = dr - (delOnlyA[x0] - delOnlyA[x1]) - (insOnlyB[y0] - insOnlyB[y1]);
      if (needTot <= 0) {
        r = rEnd;
        continue;
      }
      const wantK = (needTot + 1) >> 1;
      const maxLeft = zeroLeft[r] + 1 < r - lastUsedRightAnc ? zeroLeft[r] + 1 : r - lastUsedRightAnc;
      let maxRight = zeroRight[rEnd] + 1 < lisLen - rEnd ? zeroRight[rEnd] + 1 : lisLen - rEnd;
      if (rEnd + 1 + zeroRight[rEnd] < lisLen && maxRight > 1) {
        const avail = zeroRight[rEnd] + 1;
        maxRight = wantK < avail ? wantK : avail >> 1 > 1 ? avail >> 1 : 1;
      }
      let K = wantK < maxLeft ? wantK : maxLeft;
      if (maxRight < K) K = maxRight;
      if (K > 0) {
        const bonus = needTot < K << 1 ? needTot : K << 1;
        const leftAnc = r - K + 1;
        lastUsedRightAnc = rEnd + K;
        exTotA[ancI[leftAnc]] += bonus;
        exTotB[ancJ[leftAnc]] += bonus;
      }
      r = rEnd;
    }

    // Final gap after anc[lisLen]: right boundary is fixed at (N, M), only needs K left anchors
    if (drArr[lisLen] > 0 && lisLen > lastUsedRightAnc) {
      const x0 = ancI[lisLen] + 1;
      const y0 = ancJ[lisLen] + 1;
      const needTot = drArr[lisLen] - delOnlyA[x0] - insOnlyB[y0];
      if (needTot > 0) {
        const wantK = (needTot + 1) >> 1;
        const maxLeft = zeroLeft[lisLen] + 1 < lisLen - lastUsedRightAnc ? zeroLeft[lisLen] + 1 : lisLen - lastUsedRightAnc;
        const K = wantK < maxLeft ? wantK : maxLeft;
        if (K > 0) {
          const bonus = needTot < K << 1 ? needTot : K << 1;
          const leftAnc = lisLen - K + 1;
          exTotA[ancI[leftAnc]] += bonus;
          exTotB[ancJ[leftAnc]] += bonus;
        }
      }
    }

    for (let i = N - 1; i >= 0; i--) exTotA[i] += exTotA[i + 1];
    for (let j = M - 1; j >= 0; j--) exTotB[j] += exTotB[j + 1];
  }

  return { ub, delOnlyA, insOnlyB, lisRemA, lisRemB, exTotA, exTotB };
}

function stepFast(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, idx) {
  let vi = off + lo;
  const viEnd = off + hi;
  let k = lo;
  let prevRem = Vprev[vi - 1];
  for (; vi <= viEnd; vi += 2, k += 2, idx++) {
    const r = prevRem;
    const a = Vprev[vi + 1];
    prevRem = a;
    const byDel = r < N ? r + 1 : -1;
    const byIns = a - k <= M ? a : -1;
    let nx = byDel >= byIns ? byDel : byIns;
    if (nx < 0) {
      Vcurr[vi] = -2;
      trace[idx] = 0;
      continue;
    }
    let ny = nx - k;
    while (A[nx] === B[ny]) {
      nx++;
      ny++;
    }
    Vcurr[vi] = nx;
    trace[idx] = nx + 1;
  }
  return idx;
}

function stepPrune(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, idx, d, ub, delOnlyA, insOnlyB, lisRemA, lisRemB, exTotA, exTotB, outBounds) {
  let vi = off + lo;
  const viEnd = off + hi;
  let k = lo;
  let prevRem = Vprev[vi - 1];
  let nextLo = 0x3fffffff;
  let nextHi = -0x3fffffff;
  let reached = 0;
  for (; vi <= viEnd; vi += 2, k += 2, idx++) {
    const r = prevRem;
    const a = Vprev[vi + 1];
    prevRem = a;
    const byDel = r < N ? r + 1 : -1;
    const byIns = a - k <= M ? a : -1;
    let nx = byDel >= byIns ? byDel : byIns;
    if (nx < 0) {
      Vcurr[vi] = -2;
      trace[idx] = 0;
      continue;
    }
    let ny = nx - k;
    while (A[nx] === B[ny]) {
      nx++;
      ny++;
    }
    if (nx === N && ny === M) {
      Vcurr[vi] = nx;
      trace[idx] = nx + 1;
      reached = 1;
      idx++;
      break;
    }
    const da = delOnlyA[nx];
    const ib = insOnlyB[ny];
    const la = lisRemA[nx];
    const lb = lisRemB[ny];
    const lisDel = la > lb ? la - lb : 0;
    const lisIns = lb > la ? lb - la : 0;
    const ex = exTotA[nx] < exTotB[ny] ? exTotA[nx] : exTotB[ny];
    const fDel = da + lisDel;
    const fIns = ib + lisIns;
    const h1 = fDel + fIns + ex;
    const diff = (N - nx - fDel) - (M - ny - fIns);
    const h2 = fDel + fIns + (diff < 0 ? -diff : diff);
    if (d + (h1 > h2 ? h1 : h2) > ub) {
      Vcurr[vi] = -2;
      trace[idx] = 0;
      continue;
    }
    Vcurr[vi] = nx;
    trace[idx] = nx + 1;
    if (k < nextLo) nextLo = k;
    if (k > nextHi) nextHi = k;
  }
  outBounds[0] = nextLo;
  outBounds[1] = nextHi;
  outBounds[2] = reached;
  return idx;
}

function runMyers(A, B, N, M, ub, prefix, usePrune, b) {
  const delta = N - M;
  const off = ub + 2;
  const vLen = 2 * ub + 5;
  if (sVprev.length < vLen) {
    sVprev = new Int32Array(vLen);
    sVcurr = new Int32Array(vLen);
  }
  let Vprev = sVprev;
  let Vcurr = sVcurr;
  Vprev.fill(-2, 0, vLen);
  Vcurr.fill(-2, 0, vLen);

  let x0 = 0;
  let y0 = 0;
  while (A[x0] === B[y0]) {
    x0++;
    y0++;
  }
  Vprev[off] = x0;
  if (x0 === N && y0 === M) {
    return { chO: null, chP: null, chD: null, chI: null, chLen: 0, deleted: 0, inserted: 0 };
  }

  const useU16 = N <= 65534;
  let trace = useU16 ? sTraceU16 : new Int32Array(1024 * 1024);
  let traceCap = trace.length;
  const rowBase = new Int32Array(ub + 2);
  const rowLo = new Int32Array(ub + 2);
  const rowHi = new Int32Array(ub + 2);
  trace[0] = x0 + 1;
  rowBase[0] = 0;
  rowLo[0] = 0;
  rowHi[0] = 0;
  let tPos = 1;
  let prevLo = 0;
  let prevHi = 0;
  let finalD = -1;

  for (let d = 1; d <= ub; d++) {
    const remD = ub - d;
    let lo = prevLo - 1;
    let hi = prevHi + 1;
    const dMin = delta - remD;
    const dMax = delta + remD;
    if (lo < dMin) lo = dMin;
    if (hi > dMax) hi = dMax;
    if (((lo ^ d) & 1) !== 0) lo++;
    if (((hi ^ d) & 1) !== 0) hi--;

    const width = ((hi - lo) >> 1) + 1;
    if (tPos + width > traceCap) {
      traceCap <<= 1;
      const nt = useU16 ? new Uint16Array(traceCap) : new Int32Array(traceCap);
      nt.set(trace);
      trace = nt;
      if (useU16) sTraceU16 = nt;
    }

    const base = tPos;
    let nextLo = lo;
    let nextHi = hi;

    if (!usePrune || (d & 15) !== 0) {
      tPos = stepFast(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base);
    } else {
      tPos = stepPrune(
        A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base, d, ub,
        b.delOnlyA, b.insOnlyB, b.lisRemA, b.lisRemB, b.exTotA, b.exTotB, sOutBounds
      );
      nextLo = sOutBounds[0];
      nextHi = sOutBounds[1];
      if (sOutBounds[2] !== 0) finalD = d;
    }

    rowBase[d] = base;
    rowLo[d] = lo;
    rowHi[d] = hi;

    if (finalD >= 0 || (delta >= lo && delta <= hi && ((d ^ delta) & 1) === 0 && Vcurr[off + delta] === N)) {
      finalD = d;
      break;
    }

    Vprev.fill(-2, off + prevLo, off + prevHi + 1);
    const tmp = Vprev;
    Vprev = Vcurr;
    Vcurr = tmp;
    prevLo = nextLo;
    prevHi = nextHi;
  }

  if (finalD < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Backtrack directly into forward change runs
  const revO = new Int32Array(finalD);
  const revP = new Int32Array(finalD);
  const revD = new Int32Array(finalD);
  const revI = new Int32Array(finalD);
  let chLen = 0;
  let deleted = 0;
  let inserted = 0;
  let k = delta;
  let x = N;
  let curO = -1;
  let curP = -1;
  let curD = 0;
  let curI = 0;

  for (let d = finalD; d >= 1; d--) {
    const pBase = rowBase[d - 1];
    const pLo = rowLo[d - 1];
    const pHi = rowHi[d - 1];
    const km1 = k - 1;
    const kp1 = k + 1;
    const r = km1 >= pLo && km1 <= pHi ? trace[pBase + ((km1 - pLo) >> 1)] - 1 : -1;
    const a = kp1 >= pLo && kp1 <= pHi ? trace[pBase + ((kp1 - pLo) >> 1)] - 1 : -1;
    const byDel = r >= 0 && r < N ? r + 1 : -1;
    const byIns = a >= 0 && a - k <= M ? a : -1;
    const isDel = byDel >= byIns;
    const xAfterEdit = isDel ? byDel : byIns;

    if (x - xAfterEdit > 0 && curD + curI > 0) {
      revO[chLen] = prefix + curO;
      revP[chLen] = prefix + curP;
      revD[chLen] = curD;
      revI[chLen] = curI;
      chLen++;
      curD = 0;
      curI = 0;
    }

    if (isDel) {
      curO = r;
      curP = r - km1;
      curD++;
      deleted++;
      x = r;
      k = km1;
    } else {
      curO = a;
      curP = a - kp1;
      curI++;
      inserted++;
      x = a;
      k = kp1;
    }
  }
  if (curD + curI > 0) {
    revO[chLen] = prefix + curO;
    revP[chLen] = prefix + curP;
    revD[chLen] = curD;
    revI[chLen] = curI;
    chLen++;
  }

  const chO = new Int32Array(chLen);
  const chP = new Int32Array(chLen);
  const chD = new Int32Array(chLen);
  const chI = new Int32Array(chLen);
  for (let i = 0, j = chLen - 1; i < chLen; i++, j--) {
    chO[i] = revO[j];
    chP[i] = revP[j];
    chD[i] = revD[j];
    chI[i] = revI[j];
  }
  return { chO, chP, chD, chI, chLen, deleted, inserted };
}

function formatPatch(pa, pb, n, m, oldBare, newBare, chO, chP, chD, chI, chLen, deleted, inserted) {
  if (chLen === 0) {
    return `${FORMAT} old=${n} new=${m} hunks=0 deleted=0 inserted=0\n`;
  }

  const hunkStart = new Int32Array(chLen);
  const hunkEnd = new Int32Array(chLen);
  let hCount = 0;
  let hs = 0;
  for (let i = 1; i < chLen; i++) {
    if (chO[i] - (chO[i - 1] + chD[i - 1]) > 2 * CONTEXT) {
      hunkStart[hCount] = hs;
      hunkEnd[hCount] = i;
      hCount++;
      hs = i;
    }
  }
  hunkStart[hCount] = hs;
  hunkEnd[hCount] = chLen;
  hCount++;

  const oldLastBare = oldBare ? n - 1 : -1;
  const newLastBare = newBare ? m - 1 : -1;
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hCount} deleted=${deleted} inserted=${inserted}\n`];

  for (let h = 0; h < hCount; h++) {
    const cStart = hunkStart[h];
    const cEnd = hunkEnd[h];
    const firstO = chO[cStart];
    const firstP = chP[cStart];
    const lastIdx = cEnd - 1;
    const lastOEnd = chO[lastIdx] + chD[lastIdx];
    const lastPEnd = chP[lastIdx] + chI[lastIdx];

    const oldStart = firstO > CONTEXT ? firstO - CONTEXT : 0;
    const newStart = firstP - (firstO - oldStart);
    const remAfter = n - lastOEnd;
    const after = remAfter < CONTEXT ? remAfter : CONTEXT;
    const oldEnd = lastOEnd + after;
    const newEnd = lastPEnd + after;

    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);

    let at = oldStart;
    for (let ci = cStart; ci < cEnd; ci++) {
      const co = chO[ci];
      const cp = chP[ci];
      const cd = chD[ci];
      const ins = chI[ci];

      for (; at < co; at++) {
        out.push(at === oldLastBare ? `=${pa[at]}\n%\n` : `=${pa[at]}\n`);
      }
      for (let i = 0; i < cd; i++) {
        const idx = co + i;
        out.push(idx === oldLastBare ? `-${pa[idx]}\n%\n` : `-${pa[idx]}\n`);
      }
      for (let i = 0; i < ins; i++) {
        const idx = cp + i;
        out.push(idx === newLastBare ? `+${pb[idx]}\n%\n` : `+${pb[idx]}\n`);
      }
      at = co + cd;
    }
    for (; at < oldEnd; at++) {
      out.push(at === oldLastBare ? `=${pa[at]}\n%\n` : `=${pa[at]}\n`);
    }
  }

  return out.join('');
}

export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldStr = input.old;
  const newStr = input.new;

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

  // Common prefix & suffix (bareness must also match!)
  let prefix = 0;
  const minNM = n < m ? n : m;
  while (prefix < minNM && pa[prefix] === pb[prefix] && (prefix === oldLastBare) === (prefix === newLastBare)) {
    prefix++;
  }
  let suffix = 0;
  const maxSuf = minNM - prefix;
  while (
    suffix < maxSuf &&
    pa[n - 1 - suffix] === pb[m - 1 - suffix] &&
    (n - 1 - suffix === oldLastBare) === (m - 1 - suffix === newLastBare)
  ) {
    suffix++;
  }

  const N = n - prefix - suffix;
  const M = m - prefix - suffix;

  if (N === 0 && M === 0) {
    return `${FORMAT} old=${n} new=${m} hunks=0 deleted=0 inserted=0\n`;
  }
  if (N === 0) {
    return formatPatch(pa, pb, n, m, oldBare, newBare, new Int32Array([prefix]), new Int32Array([prefix]), new Int32Array([0]), new Int32Array([M]), 1, 0, M);
  }
  if (M === 0) {
    return formatPatch(pa, pb, n, m, oldBare, newBare, new Int32Array([prefix]), new Int32Array([prefix]), new Int32Array([N]), new Int32Array([0]), 1, N, 0);
  }

  // Intern middle slice with V8 C++ Map + sequential prediction (bare last lines handled separately)
  const A = new Int32Array(N + 1);
  const B = new Int32Array(M + 1);
  A[N] = -1;
  B[M] = -2;
  const map = new Map();
  const fp = new Int32Array(N + M + 2);
  let nextId = 0;

  const hasBareA = oldBare && suffix === 0;
  const hasBareB = newBare && suffix === 0;
  const normN = hasBareA ? N - 1 : N;
  const normM = hasBareB ? M - 1 : M;

  for (let i = 0; i < normN; i++) {
    const s = pa[prefix + i];
    let id = map.get(s);
    if (id === undefined) {
      id = nextId++;
      map.set(s, id);
      fp[id] = i;
    }
    A[i] = id;
  }

  let pred = 0;
  for (let j = 0; j < normM; j++) {
    const s = pb[prefix + j];
    if (pred < normN && s === pa[prefix + pred]) {
      B[j] = A[pred++];
      continue;
    }
    let id = map.get(s);
    if (id === undefined) {
      id = nextId++;
      map.set(s, id);
      fp[id] = -1;
    } else {
      const p = fp[id];
      if (p >= 0) pred = p + 1;
    }
    B[j] = id;
  }

  if (hasBareA && hasBareB) {
    const idA = nextId++;
    A[N - 1] = idA;
    B[M - 1] = pa[n - 1] === pb[m - 1] ? idA : nextId++;
  } else if (hasBareA) {
    A[N - 1] = nextId++;
  } else if (hasBareB) {
    B[M - 1] = nextId++;
  }

  const usePrune = N + M > 96;
  const b = usePrune ? prepareBounds(A, B, N, M, nextId) : null;
  const res = runMyers(A, B, N, M, usePrune ? b.ub : N + M, prefix, usePrune, b);
  return formatPatch(pa, pb, n, m, oldBare, newBare, res.chO, res.chP, res.chD, res.chI, res.chLen, res.deleted, res.inserted);
}
