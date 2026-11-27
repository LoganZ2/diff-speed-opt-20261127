// Exact, ultra-fast drop-in for makefun-diff 1.0.0.
// Preserves 100% identical Myers tie-breaking (furthest oldPos, deletion wins ties, no edge pruning).

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;

// Reusable scratch buffers (zero state carried across cases; overwritten/cleared per call).
let sOldOff = new Int32Array(65536);
let sNewOff = new Int32Array(65536);
let sHtCap = 131072;
let sHtGen = new Uint16Array(sHtCap);
let sHtGenCur = 0;
let sHtHash = new Int32Array(sHtCap);
let sHtStart = new Int32Array(sHtCap);
let sHtEnd = new Int32Array(sHtCap);
let sHtId = new Int32Array(sHtCap);
let sHtSrc = new Uint8Array(sHtCap);
let sFirstPos = new Int32Array(65536);
let sVprev = new Int32Array(16384);
let sVcurr = new Int32Array(16384);
let sTraceU16 = new Uint16Array(2 * 1024 * 1024);
const sVub = new Int32Array(265);
const sOutBounds = new Int32Array(3);

let sCntA = new Int32Array(65536);
let sCntB = new Int32Array(65536);
let sPosB = new Int32Array(65536);
let sDelOnlyA = new Int32Array(65536);
let sInsOnlyB = new Int32Array(65536);
let sLisRemA = new Int32Array(65536);
let sLisRemB = new Int32Array(65536);
let sInvRemA = new Int32Array(65536);
let sInvRemB = new Int32Array(65536);
let sTailsJ = new Int32Array(65536);
let sTailsIdx = new Int32Array(65536);
let sMatchI = new Int32Array(65536);
let sMatchJ = new Int32Array(65536);
let sPrev = new Int32Array(65536);
let sInLis = new Uint8Array(65536);
let sLisUsed = new Uint8Array(65536);

function countLines(text) {
  const len = text.length;
  if (len === 0) return 0;
  let n = 0;
  let pos = 0;
  while (pos < len) {
    const nl = text.indexOf('\n', pos);
    if (nl === -1) {
      n++;
      break;
    }
    n++;
    pos = nl + 1;
  }
  return n;
}

function scanLinesInto(text, buf) {
  const len = text.length;
  buf[0] = 0;
  if (len === 0) return { off: buf, count: 0 };
  let off = buf;
  let cap = off.length;
  let n = 0;
  let pos = 0;
  while (pos < len) {
    const nl = text.indexOf('\n', pos);
    const end = nl === -1 ? len : nl + 1;
    n++;
    if (n >= cap) {
      cap <<= 1;
      const next = new Int32Array(cap);
      next.set(off);
      off = next;
    }
    off[n] = end;
    pos = end;
  }
  return { off, count: n };
}

function linesEqual(s1, a1, b1, s2, a2, b2) {
  const len = b1 - a1;
  if (len !== b2 - a2) return false;
  for (let k = 0; k < len; k++) {
    if (s1.charCodeAt(a1 + k) !== s2.charCodeAt(a2 + k)) return false;
  }
  return true;
}

function hashLine(str, s, len) {
  let h = (2166136261 ^ len) | 0;
  if (len <= 8) {
    for (let k = 0; k < len; k++) h = Math.imul(h ^ str.charCodeAt(s + k), 16777619);
  } else {
    const m = s + (len >> 1);
    const e = s + len;
    h = Math.imul(h ^ str.charCodeAt(s), 16777619);
    h = Math.imul(h ^ str.charCodeAt(s + 2), 16777619);
    h = Math.imul(h ^ str.charCodeAt(m - 1), 16777619);
    h = Math.imul(h ^ str.charCodeAt(m + 1), 16777619);
    h = Math.imul(h ^ str.charCodeAt(e - 3), 16777619);
    h = Math.imul(h ^ str.charCodeAt(e - 1), 16777619);
  }
  return h ^ (h >>> 16);
}

function ensureHtCap(needed) {
  if (sHtCap >= needed) return;
  let cap = sHtCap;
  while (cap < needed) cap <<= 1;
  sHtCap = cap;
  sHtGen = new Uint16Array(cap);
  sHtGenCur = 0;
  sHtHash = new Int32Array(cap);
  sHtStart = new Int32Array(cap);
  sHtEnd = new Int32Array(cap);
  sHtId = new Int32Array(cap);
  sHtSrc = new Uint8Array(cap);
}

function internOld(oldStr, oldOff, prefix, N, A, cap, gen) {
  const mask = cap - 1;
  const htGen = sHtGen;
  const htHash = sHtHash;
  const htStart = sHtStart;
  const htEnd = sHtEnd;
  const htId = sHtId;
  const htSrc = sHtSrc;
  const firstPos = sFirstPos;
  let nextId = 0;

  for (let i = 0; i < N; i++) {
    const oi = prefix + i;
    const s = oldOff[oi];
    const e = oldOff[oi + 1];
    const len = e - s;
    const h = hashLine(oldStr, s, len);
    let slot = h & mask;
    while (true) {
      if (htGen[slot] !== gen) {
        htGen[slot] = gen;
        htHash[slot] = h;
        htStart[slot] = s;
        htEnd[slot] = e;
        htSrc[slot] = 0;
        const id = nextId++;
        htId[slot] = id;
        firstPos[id] = i;
        A[i] = id;
        break;
      }
      if (htHash[slot] === h) {
        const hs = htStart[slot];
        const he = htEnd[slot];
        if (he - hs === len) {
          let eq = true;
          for (let k = 0; k < len; k++) {
            if (oldStr.charCodeAt(s + k) !== oldStr.charCodeAt(hs + k)) {
              eq = false;
              break;
            }
          }
          if (eq) {
            A[i] = htId[slot];
            break;
          }
        }
      }
      slot = (slot + 1) & mask;
    }
  }
  return nextId;
}

function internNew(oldStr, newStr, oldOff, newOff, prefix, N, M, A, B, cap, gen, nextId) {
  const mask = cap - 1;
  const htGen = sHtGen;
  const htHash = sHtHash;
  const htStart = sHtStart;
  const htEnd = sHtEnd;
  const htId = sHtId;
  const htSrc = sHtSrc;
  const firstPos = sFirstPos;
  let pred = 0;

  for (let j = 0; j < M; j++) {
    const nj = prefix + j;
    const s = newOff[nj];
    const e = newOff[nj + 1];
    const len = e - s;
    if (pred < N) {
      const os = oldOff[prefix + pred];
      const oe = oldOff[prefix + pred + 1];
      if (oe - os === len) {
        let eq = true;
        for (let k = 0; k < len; k++) {
          if (newStr.charCodeAt(s + k) !== oldStr.charCodeAt(os + k)) {
            eq = false;
            break;
          }
        }
        if (eq) {
          B[j] = A[pred];
          pred++;
          continue;
        }
      }
    }
    const h = hashLine(newStr, s, len);
    let slot = h & mask;
    while (true) {
      if (htGen[slot] !== gen) {
        htGen[slot] = gen;
        htHash[slot] = h;
        htStart[slot] = s;
        htEnd[slot] = e;
        htSrc[slot] = 1;
        const id = nextId++;
        htId[slot] = id;
        firstPos[id] = -1;
        B[j] = id;
        break;
      }
      if (htHash[slot] === h) {
        const hs = htStart[slot];
        const he = htEnd[slot];
        if (he - hs === len) {
          const ref = htSrc[slot] === 0 ? oldStr : newStr;
          let eq = true;
          for (let k = 0; k < len; k++) {
            if (newStr.charCodeAt(s + k) !== ref.charCodeAt(hs + k)) {
              eq = false;
              break;
            }
          }
          if (eq) {
            const id = htId[slot];
            B[j] = id;
            const fp = firstPos[id];
            if (fp >= 0) pred = fp + 1;
            break;
          }
        }
      }
      slot = (slot + 1) & mask;
    }
  }
  return nextId;
}

function internMiddle(oldStr, newStr, oldOff, newOff, prefix, N, M) {
  let cap = 64;
  const target = (N + M) * 2 + 64;
  while (cap < target) cap <<= 1;
  ensureHtCap(cap);
  sHtGenCur++;
  if (sHtGenCur >= 65535) {
    sHtGen.fill(0);
    sHtGenCur = 1;
  }
  const gen = sHtGenCur;
  if (sFirstPos.length < N + M + 1) sFirstPos = new Int32Array(N + M + 1);

  const A = new Int32Array(N + 1);
  const B = new Int32Array(M + 1);
  A[N] = -1;
  B[M] = -2;

  let nextId = internOld(oldStr, oldOff, prefix, N, A, cap, gen);
  nextId = internNew(oldStr, newStr, oldOff, newOff, prefix, N, M, A, B, cap, gen, nextId);
  return { A, B, nextId };
}

function computeUniqueLis(A, N, cntA, cntB, posB, maxL) {
  if (sTailsJ.length <= maxL) {
    const sz = maxL + 1024;
    sTailsJ = new Int32Array(sz);
    sTailsIdx = new Int32Array(sz);
    sMatchI = new Int32Array(sz);
    sMatchJ = new Int32Array(sz);
    sPrev = new Int32Array(sz);
    sInLis = new Uint8Array(sz);
    sLisUsed = new Uint8Array(sz + 2);
  }
  const tailsJ = sTailsJ;
  const tailsIdx = sTailsIdx;
  const matchI = sMatchI;
  const matchJ = sMatchJ;
  const prev = sPrev;
  const inLis = sInLis;
  let mCnt = 0;
  let lisLen = 0;

  for (let i = 0; i < N; i++) {
    const id = A[i];
    if (cntA[id] === 1 && cntB[id] === 1) {
      const j = posB[id];
      const idx = mCnt++;
      matchI[idx] = i;
      matchJ[idx] = j;
      inLis[idx] = 0;
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
    inLis[cur] = 1;
    ancI[k] = matchI[cur];
    ancJ[k] = matchJ[cur];
    cur = prev[cur];
  }
  ancI[lisLen + 1] = N;
  return { ancI, ancJ, inLis, matchI, matchJ, mCnt, lisLen };
}

function computeInversions(ancI, ancJ, inLis, matchI, matchJ, mCnt, lisLen, N, M, invRemA, invRemB) {
  invRemA.fill(0, 0, N + 1);
  invRemB.fill(0, 0, M + 1);
  if (mCnt <= lisLen || lisLen === 0) return;

  const lisUsed = sLisUsed;
  lisUsed.fill(0, 0, lisLen + 2);
  const nonLis = mCnt - lisLen;
  const pMinI = new Int32Array(nonLis);
  const pMinJ = new Int32Array(nonLis);
  let pLen = 0;

  for (let idx = 0; idx < mCnt; idx++) {
    if (inLis[idx]) continue;
    const mi = matchI[idx];
    const mj = matchJ[idx];
    let lo = 1;
    let hi = lisLen + 1;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (ancI[mid] < mi) lo = mid + 1;
      else hi = mid;
    }
    let mk = 0;
    if (lo <= lisLen && ancJ[lo] < mj) {
      for (let k = lo; k <= lisLen && ancJ[k] < mj; k++) {
        if (!lisUsed[k]) {
          mk = k;
          break;
        }
      }
    }
    if (mk === 0 && lo > 1 && ancJ[lo - 1] > mj) {
      for (let k = lo - 1; k >= 1 && ancJ[k] > mj; k--) {
        if (!lisUsed[k]) {
          mk = k;
          break;
        }
      }
    }
    if (mk > 0) {
      lisUsed[mk] = 1;
      pMinI[pLen] = mi < ancI[mk] ? mi : ancI[mk];
      pMinJ[pLen] = mj < ancJ[mk] ? mj : ancJ[mk];
      pLen++;
    }
  }

  if (pLen === 0) return;

  const ord = new Int32Array(pLen);
  for (let t = 0; t < pLen; t++) ord[t] = t;
  ord.sort((a, b) => pMinI[a] - pMinI[b] || pMinJ[a] - pMinJ[b]);

  const pT = new Int32Array(pLen);
  const pTI = new Int32Array(pLen);
  const pPr = new Int32Array(pLen);
  let pL = 0;
  for (let t = 0; t < pLen; t++) {
    const j = pMinJ[ord[t]];
    let lo = 0;
    let hi = pL;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (pT[mid] <= j) lo = mid + 1;
      else hi = mid;
    }
    pPr[t] = lo > 0 ? pTI[lo - 1] : -1;
    pT[lo] = j;
    pTI[lo] = t;
    if (lo === pL) pL++;
  }
  let pc = pL > 0 ? pTI[pL - 1] : -1;
  while (pc !== -1) {
    const p = ord[pc];
    invRemA[pMinI[p]]++;
    invRemB[pMinJ[p]]++;
    pc = pPr[pc];
  }
  for (let i = N - 1; i >= 0; i--) invRemA[i] += invRemA[i + 1];
  for (let j = M - 1; j >= 0; j--) invRemB[j] += invRemB[j + 1];
}

function localMyersDist(A, B, x0, y0, n, m, Vub, locMax) {
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
  return n + m;
}

function computeUpperBound(A, B, ancI, ancJ, lisLen) {
  let ubAcc = 0;
  const UB_LOCAL_MAX = 128;
  const Vub = sVub;
  for (let r = 0; r <= lisLen; r++) {
    let x0 = ancI[r] + 1;
    let x1 = ancI[r + 1];
    let y0 = ancJ[r] + 1;
    let y1 = ancJ[r + 1];
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
    if (n === 0) {
      ubAcc += m;
      continue;
    }
    if (m === 0) {
      ubAcc += n;
      continue;
    }
    const locMax = n + m < UB_LOCAL_MAX ? n + m : UB_LOCAL_MAX;
    ubAcc += localMyersDist(A, B, x0, y0, n, m, Vub, locMax);
  }
  return ubAcc;
}

function prepareBounds(A, B, N, M, nextId) {
  if (sCntA.length < nextId) {
    const sz = nextId + 4096;
    sCntA = new Int32Array(sz);
    sCntB = new Int32Array(sz);
    sPosB = new Int32Array(sz);
  }
  const cntA = sCntA;
  const cntB = sCntB;
  const posB = sPosB;
  cntA.fill(0, 0, nextId);
  cntB.fill(0, 0, nextId);
  for (let i = 0; i < N; i++) cntA[A[i]]++;
  for (let j = 0; j < M; j++) {
    const id = B[j];
    cntB[id]++;
    posB[id] = j;
  }

  if (sDelOnlyA.length <= N) {
    const sz = N + 4096;
    sDelOnlyA = new Int32Array(sz);
    sLisRemA = new Int32Array(sz);
    sInvRemA = new Int32Array(sz);
  }
  if (sInsOnlyB.length <= M) {
    const sz = M + 4096;
    sInsOnlyB = new Int32Array(sz);
    sLisRemB = new Int32Array(sz);
    sInvRemB = new Int32Array(sz);
  }
  const delOnlyA = sDelOnlyA;
  const insOnlyB = sInsOnlyB;
  delOnlyA[N] = 0;
  insOnlyB[M] = 0;
  for (let i = N - 1; i >= 0; i--) delOnlyA[i] = delOnlyA[i + 1] + (cntB[A[i]] === 0 ? 1 : 0);
  for (let j = M - 1; j >= 0; j--) insOnlyB[j] = insOnlyB[j + 1] + (cntA[B[j]] === 0 ? 1 : 0);

  const maxL = N < M ? N : M;
  const { ancI, ancJ, inLis, matchI, matchJ, mCnt, lisLen } = computeUniqueLis(A, N, cntA, cntB, posB, maxL);
  ancJ[lisLen + 1] = M;

  const lisRemA = sLisRemA;
  const lisRemB = sLisRemB;
  lisRemA.fill(0, 0, N + 1);
  lisRemB.fill(0, 0, M + 1);
  for (let k = 1; k <= lisLen; k++) {
    lisRemA[ancI[k]] = 1;
    lisRemB[ancJ[k]] = 1;
  }
  for (let i = N - 1; i >= 0; i--) lisRemA[i] += lisRemA[i + 1];
  for (let j = M - 1; j >= 0; j--) lisRemB[j] += lisRemB[j + 1];

  const invRemA = sInvRemA;
  const invRemB = sInvRemB;
  computeInversions(ancI, ancJ, inLis, matchI, matchJ, mCnt, lisLen, N, M, invRemA, invRemB);

  let ub = computeUpperBound(A, B, ancI, ancJ, lisLen);
  if (ub > N + M) ub = N + M;

  return { ub, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB };
}

function stepFastU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, idx) {
  let vi = off + lo;
  const viEnd = off + hi;
  let k = lo;
  let prevRem = Vprev[vi - 1];
  for (; vi <= viEnd; vi += 2, k += 2, idx++) {
    const r = prevRem;
    const a = Vprev[vi + 1];
    prevRem = a;
    // Dead entries in Vprev are -2: r=-2 -> r+1=-1; a=-2 -> a=-2 or -1 (both < 0).
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

function stepPruneU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, idx, d, ub, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB, outBounds) {
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
    const ia = invRemA[nx];
    const jb = invRemB[ny];
    const fDel = da + (la > lb ? la - lb : 0);
    const fIns = ib + (lb > la ? lb - la : 0);
    const diff = (N - nx - fDel) - (M - ny - fIns);
    if (d + fDel + fIns + ((ia < jb ? ia : jb) << 1) + (diff < 0 ? -diff : diff) > ub) {
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

function backtrackTrace(trace, rowBase, rowLo, rowHi, finalD, N, M, delta, prefix) {
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
    const snake = x - xAfterEdit;

    if (snake > 0 && curD + curI > 0) {
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

function runMyersU16(A, B, N, M, ub, prefix, usePrune, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB) {
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

  let trace = sTraceU16;
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
  const outBounds = sOutBounds;

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
      const nt = new Uint16Array(traceCap);
      nt.set(trace);
      trace = nt;
      sTraceU16 = nt;
    }

    const base = tPos;
    let nextLo = lo;
    let nextHi = hi;

    if (!usePrune || (d & 15) !== 0) {
      tPos = stepFastU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base);
    } else {
      tPos = stepPruneU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base, d, ub, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB, outBounds);
      nextLo = outBounds[0];
      nextHi = outBounds[1];
      if (outBounds[2] !== 0) finalD = d;
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

  if (finalD < 0) {
    throw new Error('makefun-diff: the search ended without reaching both ends');
  }
  return backtrackTrace(trace, rowBase, rowLo, rowHi, finalD, N, M, delta, prefix);
}

/** Fallback for giant texts with N > 65534 (uses Int32Array trace). */
function runMyersI32(A, B, N, M, ub, prefix, usePrune, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB) {
  const delta = N - M;
  const off = ub + 2;
  const vLen = 2 * ub + 5;
  let Vprev = new Int32Array(vLen).fill(-2);
  let Vcurr = new Int32Array(vLen).fill(-2);

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

  let traceCap = 2 * 1024 * 1024;
  let trace = new Int32Array(traceCap);
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
  const outBounds = sOutBounds;

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
      const nt = new Int32Array(traceCap);
      nt.set(trace);
      trace = nt;
    }

    const base = tPos;
    let nextLo = lo;
    let nextHi = hi;
    if (!usePrune || (d & 15) !== 0) {
      tPos = stepFastU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base);
    } else {
      tPos = stepPruneU16(A, B, N, M, Vprev, Vcurr, off, lo, hi, trace, base, d, ub, delOnlyA, insOnlyB, lisRemA, lisRemB, invRemA, invRemB, outBounds);
      nextLo = outBounds[0];
      nextHi = outBounds[1];
      if (outBounds[2] !== 0) finalD = d;
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

  if (finalD < 0) {
    throw new Error('makefun-diff: the search ended without reaching both ends');
  }
  return backtrackTrace(trace, rowBase, rowLo, rowHi, finalD, N, M, delta, prefix);
}

function formatPatch(oldStr, newStr, oldOff, newOff, n, m, chO, chP, chD, chI, chLen, deleted, inserted) {
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
        const s = oldOff[at];
        const e = oldOff[at + 1];
        out.push(oldStr.charCodeAt(e - 1) === 10 ? `=${oldStr.slice(s, e)}` : `=${oldStr.slice(s, e)}\n%\n`);
      }
      for (let i = 0; i < cd; i++) {
        const s = oldOff[co + i];
        const e = oldOff[co + i + 1];
        out.push(oldStr.charCodeAt(e - 1) === 10 ? `-${oldStr.slice(s, e)}` : `-${oldStr.slice(s, e)}\n%\n`);
      }
      for (let i = 0; i < ins; i++) {
        const s = newOff[cp + i];
        const e = newOff[cp + i + 1];
        out.push(newStr.charCodeAt(e - 1) === 10 ? `+${newStr.slice(s, e)}` : `+${newStr.slice(s, e)}\n%\n`);
      }
      at = co + cd;
    }
    for (; at < oldEnd; at++) {
      const s = oldOff[at];
      const e = oldOff[at + 1];
      out.push(oldStr.charCodeAt(e - 1) === 10 ? `=${oldStr.slice(s, e)}` : `=${oldStr.slice(s, e)}\n%\n`);
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
    const n = countLines(oldStr);
    return `${FORMAT} old=${n} new=${n} hunks=0 deleted=0 inserted=0\n`;
  }

  const rOld = scanLinesInto(oldStr, sOldOff);
  sOldOff = rOld.off;
  const oldOff = rOld.off;
  const n = rOld.count;

  const rNew = scanLinesInto(newStr, sNewOff);
  sNewOff = rNew.off;
  const newOff = rNew.off;
  const m = rNew.count;

  let prefix = 0;
  const minNM = n < m ? n : m;
  while (prefix < minNM && linesEqual(oldStr, oldOff[prefix], oldOff[prefix + 1], newStr, newOff[prefix], newOff[prefix + 1])) {
    prefix++;
  }
  let suffix = 0;
  const maxSuf = minNM - prefix;
  while (
    suffix < maxSuf &&
    linesEqual(oldStr, oldOff[n - 1 - suffix], oldOff[n - suffix], newStr, newOff[m - 1 - suffix], newOff[m - suffix])
  ) {
    suffix++;
  }

  const N = n - prefix - suffix;
  const M = m - prefix - suffix;

  if (N === 0 && M === 0) {
    return `${FORMAT} old=${n} new=${m} hunks=0 deleted=0 inserted=0\n`;
  }
  if (N === 0) {
    const chO = new Int32Array([prefix]);
    const chP = new Int32Array([prefix]);
    const chD = new Int32Array([0]);
    const chI = new Int32Array([M]);
    return formatPatch(oldStr, newStr, oldOff, newOff, n, m, chO, chP, chD, chI, 1, 0, M);
  }
  if (M === 0) {
    const chO = new Int32Array([prefix]);
    const chP = new Int32Array([prefix]);
    const chD = new Int32Array([N]);
    const chI = new Int32Array([0]);
    return formatPatch(oldStr, newStr, oldOff, newOff, n, m, chO, chP, chD, chI, 1, N, 0);
  }

  const { A, B, nextId } = internMiddle(oldStr, newStr, oldOff, newOff, prefix, N, M);
  const usePrune = N + M > 96;
  let res;
  if (usePrune) {
    const b = prepareBounds(A, B, N, M, nextId);
    res =
      N <= 65534
        ? runMyersU16(A, B, N, M, b.ub, prefix, true, b.delOnlyA, b.insOnlyB, b.lisRemA, b.lisRemB, b.invRemA, b.invRemB)
        : runMyersI32(A, B, N, M, b.ub, prefix, true, b.delOnlyA, b.insOnlyB, b.lisRemA, b.lisRemB, b.invRemA, b.invRemB);
  } else {
    res = runMyersU16(A, B, N, M, N + M, prefix, false, null, null, null, null, null, null);
  }
  return formatPatch(oldStr, newStr, oldOff, newOff, n, m, res.chO, res.chP, res.chD, res.chI, res.chLen, res.deleted, res.inserted);
}
