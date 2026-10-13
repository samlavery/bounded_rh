"""Float sizing (no certification) of the seven-point bisection outside the basins, comparing leaf tests:
  Z : zero-order (min of w over each pair-sum interval),
  M : mean value with derivative ranges on the pair-sum intervals, leaning-corner centre,
  T : second order at a corner point q: G(q) + grad G(q).(g - q) + 1/2 sum_t a_t l_t (s_t(g) - s_t(q))^2,
      l_t = min of w'' on the pair-sum interval; only negative l_t are charged (the positive part is dropped).
Usage: float7.py DELTA TAU HW MODES (e.g. ZM, ZT, ZMT)"""
import sys, time, itertools, numpy as np
sys.path.insert(0, '.')
sys.setrecursionlimit(100000)
from sevenw import Fun, w, w1, PAIRS, Q, INC
SC = 32768
d = np.load('w40.npz'); aN = np.array([int(x) for x in d['aN']], float); bN = np.array([int(x) for x in d['bN']], float)
a = aN / 1e8; b = bN / 1e8
mins = d['mins']; vals = d['vals']; gmin = vals[0]
delta = float(sys.argv[1]); tau = float(sys.argv[2]); hw = int(sys.argv[3]); modes = sys.argv[4]
c = gmin * (1 - delta)
basins = []
for v, x in zip(vals, mins):
    if v > gmin * (1 + tau): break
    for y in (x, x[::-1]):
        cc = [int(round(xi * SC)) for xi in y]
        bx = tuple((ci - hw, ci + hw) for ci in cc)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins: basins.append(bx)
# grids of w, w', w'' on the unit grid (x in units 1/SC) up to 40
XM = 40 * SC
xs = np.arange(XM + 2) / SC
Wg = w(xs); W1g = w1(xs)
W2g = np.gradient(W1g, 1.0 / SC)
BLK = 256
def blockify(arr, f):
    nb = len(arr) // BLK + 1; p = np.pad(arr, (0, nb * BLK - len(arr)), mode='edge'); return f(p.reshape(nb, BLK), axis=1)
bmin = {'w': blockify(Wg, np.min), 'w1lo': blockify(W1g, np.min), 'w1hi': blockify(W1g, np.max), 'w2lo': blockify(W2g, np.min)}
src = {'w': (Wg, np.min), 'w1lo': (W1g, np.min), 'w1hi': (W1g, np.max), 'w2lo': (W2g, np.min)}
def rq(key, lo, hi):
    arr, f = src[key]
    lo = max(lo, 0); hi = min(hi, XM)
    if hi - lo < 4 * BLK: return float(f(arr[lo:hi + 1]))
    A = -(-lo // BLK); B = (hi + 1) // BLK
    parts = [arr[lo:A * BLK], bmin[key][A:B], arr[B * BLK:hi + 1]]
    return float(f(np.concatenate([p for p in parts if len(p)])))
PI = [(i, j) for (i, j) in PAIRS]
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]
def ivals(box):
    return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
def zlow(box):
    return sum(b[r] * box[r][0] / SC for r in range(Q)) + sum(a[t] * rq('w', lo, hi) for t, (lo, hi) in enumerate(ivals(box)))
def mlow(box):
    iv = ivals(box)
    lo1 = [rq('w1lo', l, h) for l, h in iv]; hi1 = [rq('w1hi', l, h) for l, h in iv]
    m = []; pen = 0.0
    for r in range(Q):
        Dlo = b[r] + sum(a[t] * lo1[t] for t in TS[r]); Dhi = b[r] + sum(a[t] * hi1[t] for t in TS[r])
        Pos = max(Dhi, 0); Neg = max(-Dlo, 0)
        mr = box[r][0] if Pos >= Neg else box[r][1]
        m.append(mr); pen += ((mr - box[r][0]) * Pos + (box[r][1] - mr) * Neg) / SC
    mm = np.array(m) / SC
    return float(b @ mm + a @ w(INC @ mm)) - pen
def tlow(box):
    iv = ivals(box)
    l2 = np.array([rq('w2lo', l, h) for l, h in iv])
    cen = np.array([(x[0] + x[1]) / 2 / SC for x in box])
    s = INC @ cen; grad = b + INC.T @ (a * w1(s))
    q = np.array([(box[r][0] if grad[r] >= 0 else box[r][1]) / SC for r in range(Q)])
    sq = INC @ q; gq = b + INC.T @ (a * w1(sq))
    val = float(b @ q + a @ w(sq))
    lin = 0.0
    for r in range(Q):
        e_lo = box[r][0] / SC - q[r]; e_hi = box[r][1] / SC - q[r]
        lin += min(gq[r] * e_lo, gq[r] * e_hi)
    quad = 0.0
    for t, (i, j) in enumerate(PAIRS):
        if l2[t] < 0:
            dl = sum(box[r][0] / SC - q[r] for r in range(i, j)); dh = sum(box[r][1] / SC - q[r] for r in range(i, j))
            quad += 0.5 * a[t] * l2[t] * max(dl * dl, dh * dh)
    return val + lin + quad
def inbas(box):
    return any(all(bb[r][0] <= box[r][0] and box[r][1] <= bb[r][1] for r in range(Q)) for bb in basins)
def lower(box):
    if inbas(box): return c
    v = zlow(box)
    if v >= c: return v
    if 'M' in modes: v = max(v, mlow(box))
    if v >= c: return v
    if 'T' in modes: v = max(v, tlow(box))
    return v
cnt = collections = None
import collections
count = collections.Counter()
LEAVES = []
def choose(box):
    wd = [x[1] - x[0] for x in box]; mw = max(wd); best = None
    for k in range(Q):
        if wd[k] * 4 < mw or wd[k] == 0: continue
        mid = (box[k][0] + box[k][1]) // 2
        A = list(box); A[k] = (box[k][0], mid); B2 = list(box); B2[k] = (mid, box[k][1])
        la, lb = lower(tuple(A)), lower(tuple(B2))
        sc = ((la >= c) + (lb >= c), la + lb)
        if best is None or sc > best[0]: best = (sc, k)
    return best[1]
def sub(box, depth=0):
    if box[0][0] > box[Q - 1][1]: count['refl'] += 1; return True
    if sum(b[r] * box[r][0] / SC for r in range(Q)) >= c: count['lin'] += 1; return True
    if inbas(box): count['basin'] += 1; LEAVES.append(('basin', box)); return True
    if zlow(box) >= c: count['Z'] += 1; LEAVES.append(('Z', box)); return True
    if 'M' in modes and mlow(box) >= c: count['M'] += 1; LEAVES.append(('M', box)); return True
    if 'T' in modes and tlow(box) >= c: count['T'] += 1; LEAVES.append(('T', box)); return True
    if depth > 70 or sum(count.values()) > 4e6 or max(x[1] - x[0] for x in box) <= 1:
        print("stuck", box, flush=True); return False
    k = choose(box); mid = (box[k][0] + box[k][1]) // 2
    A = list(box); A[k] = (box[k][0], mid); B2 = list(box); B2[k] = (mid, box[k][1])
    return sub(tuple(A), depth + 1) and sub(tuple(B2), depth + 1)
sys.path.insert(0, '../pyr')
from size_pyr import phase1, QUARTER
cN = c * 1e8
adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
S = [-(-(4 * int(cN) * SC) // (int(bN[r]) * 4 * QUARTER)) * QUARTER for r in range(Q)]
covers = [phase1(int(cN), adj[r], S[r]) for r in range(Q)]
bads = [cv[1] for cv in covers]
t0 = time.time()
ok = True
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    box = tuple(bads[r][tup[r]] for r in range(Q))
    if not sub(box): ok = False; break
print(f"delta={delta} tau={tau} hw={hw} modes={modes} basins={len(basins)} ok={ok} leaves={sum(count.values())} {dict(count)} ({time.time()-t0:.0f}s)")

import pickle
pickle.dump(LEAVES, open(f"leaves_{modes}_{delta}_{tau}_{hw}.pkl", "wb"))
