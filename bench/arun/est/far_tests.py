"""Phase 2b: real far-field tests on bridge-port's t570 split tree (read-only dump).  A node is certified if LB >= cN/SA.
T1 interval-min: LB = sum_t a_t min_{s in [lo_t, hi_t]} w(s) + sum_r b_r lo_r, pair-sum ranges from the box intersected with the node's
   explicit constraints; min w from a dyadic table at 2^-k (outer cover: the minimum over all table cells meeting [lo, hi]).
T2 long-gap decoupling: for gaps r with lo_r >= g*, LB = mL(r) + mR(r) + b_r lo_r with mL/mR the global minima of the left/right sub-frame
   functionals (same weights restricted; cross pairs dropped, they are >= 0).
Leaves after collapse: walk top-down; a certified node counts 1, a leaf counts 1, else recurse.
usage: python3 far_tests.py DUMP.pkl WINDOW.json"""
import sys, json, pickle, itertools, numpy as np
from scipy.optimize import minimize
DUMP, WJ = sys.argv[1], sys.argv[2]
class Cell(tuple):
    def __new__(cls, box, cons=None):
        c = tuple.__new__(cls, box); c.cons = dict(cons or {}); return c
class U(pickle.Unpickler):
    def find_class(self, mod, name):
        if name == 'Cell': return Cell
        return super().find_class(mod, name)
D = U(open(DUMP, 'rb')).load(); W = json.load(open(WJ))
n = W['n']; Q = n - 1; SA = W['SA']; SC = 2 ** 15
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]
aN = np.array([W['aN']['%d,%d' % (i, j)] for i, j in PAIRS], float) / SA; bN = np.array(W['bN'], float) / SA
cN = W['c_cert_target']['cN_over_1e8'] / SA
cw = np.array(W['cnum'], float) / W['cden']; om = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw))])
def Kraw(x):
    x = np.asarray(x, float)[..., None]
    return ((np.sinc((om - 2 * np.pi * x) / 2 / np.pi) + np.sinc((om + 2 * np.pi * x) / 2 / np.pi)) / 2 * cw).sum(-1)
K0 = float(Kraw(0.0))
def w(s): return (Kraw(s) / K0) ** 2
# max pair-sum upper bound in the tree (roots)
SMAX = max(max(t[2][k][1] for k in t[2]) if t[2] else 0 for t in D['trees']) / SC
SMAX = max(SMAX, max(np.array(t[1])[:, 1].sum() for t in D['trees']) / SC)
FINE = 2 ** 14; sf = np.arange(0, SMAX + 1, 1 / FINE); wf_ = np.empty(len(sf))
for i in range(0, len(sf), 200000): wf_[i:i + 200000] = w(sf[i:i + 200000])
print('w sampled on [0, %.1f] at 2^-14 (%d points); cN/SA = %.8f' % (SMAX, len(sf), cN), flush=True)
TABLES = {}
for k in (6, 8, 10):
    step = 2 ** (14 - k); ncell = int(np.ceil(len(sf) / step))
    cellmin = np.array([wf_[i * step:(i + 1) * step + 1].min() for i in range(ncell)])      # min over the cell incl. its right end
    # 2nd-derivative allowance for the discrete sampling inside a cell (sample spacing 2^-14): subtract max|w''| h^2/8
    cellmin = np.maximum(cellmin - 6.1 * (1 / FINE) ** 2 / 8, 0.0)
    # sparse table for range-min queries (pyramid)
    sp = [cellmin]
    while (1 << len(sp)) <= ncell: prev = sp[-1]; s2 = 1 << (len(sp) - 1); sp.append(np.minimum(prev[:-s2], prev[s2:]))
    TABLES[k] = (cellmin, sp, ncell)
    print('T1 table 2^-%d: %d cells over [0, %.1f]; pyramid levels %d, total entries %d (%.1f KB at 4 B/entry; %.1f KB base level only)'
          % (k, ncell, SMAX, len(sp), sum(len(x) for x in sp), 4 * sum(len(x) for x in sp) / 1024, 4 * ncell / 1024), flush=True)
def rmin(k, lo, hi):
    cellmin, sp, ncell = TABLES[k]; a = int(np.floor(lo * 2 ** k)); b = int(np.floor(hi * 2 ** k))
    a = max(0, min(a, ncell - 1)); b = max(a, min(b, ncell - 1)); L = int(np.log2(b - a + 1))
    return min(sp[L][a], sp[L][b - (1 << L) + 1])
def pair_ranges(box, cons):
    lo = np.array([box[i:j, 0].sum() for i, j in PAIRS]); hi = np.array([box[i:j, 1].sum() for i, j in PAIRS])
    for t, (l_, u_) in cons.items(): lo[t] = max(lo[t], l_ / SC); hi[t] = min(hi[t], u_ / SC)
    return lo, hi
def T1(k, box, cons):
    lo, hi = pair_ranges(box, cons)
    return sum(aN[t] * rmin(k, lo[t], hi[t]) for t in range(len(PAIRS)) if aN[t] > 0) + float(bN @ box[:, 0])
# sub-frame global minima for T2
def subframe_min(pts):
    """global min over gaps >= 0 of the functional restricted to consecutive points pts (list of indices)"""
    m = len(pts)
    if m <= 1: return 0.0
    idx = [t for t, (i, j) in enumerate(PAIRS) if i in pts and j in pts]
    gaps = list(range(pts[0], pts[-1]))
    def f(g):
        p = np.concatenate([[0.0], np.cumsum(g)]); val = float(bN[gaps] @ g)
        for t in idx:
            i, j = PAIRS[t]; val += aN[t] * float(w(p[j - pts[0]] - p[i - pts[0]]))
        return val
    best = np.inf
    starts = [np.array(wd) for wd in itertools.product((1.04, 1.97, 2.93), repeat=m - 1)] if m - 1 <= 7 else []
    rng = np.random.default_rng(3); starts += [rng.uniform(0, 4, m - 1) for _ in range(60)]
    for g0 in starts:
        r = minimize(f, g0, method='L-BFGS-B', bounds=[(0, 40)] * (m - 1), options={'maxiter': 500})
        best = min(best, float(r.fun))
    return best
mL = [subframe_min(list(range(0, r + 1))) for r in range(Q)]          # gap r joins points r, r+1: left frame = points 0..r
mR = [subframe_min(list(range(r + 1, n))) for r in range(Q)]
print('sub-frame minima (left points 0..r | right points r+1..8):', [('%d: %.5f | %.5f' % (r, mL[r], mR[r])) for r in range(Q)], flush=True)
def T2(gstar, box):
    best = -np.inf
    for r in range(Q):
        if box[r, 0] >= gstar: best = max(best, mL[r] + mR[r] + bN[r] * box[r, 0])
    return best
def count(nd, test):
    box = np.array(nd[1], float) / SC; cons = nd[2]
    if test(box, cons) >= cN: return 1, 1
    if nd[0] == 'leaf': return 1, 0
    a, ca = count(nd[4], test); b, cb = count(nd[5], test); return a + b, ca + cb
tests = {}
for k in (6, 8, 10): tests['T1 2^-%d' % k] = (lambda box, cons, k=k: T1(k, box, cons))
for gs in (2.0, 2.5, 3.0): tests['T2 g*=%.1f' % gs] = (lambda box, cons, gs=gs: T2(gs, box))
for k in (8, 10):
    for gs in (2.0, 2.5):
        tests['T1 2^-%d + T2 g*=%.1f' % (k, gs)] = (lambda box, cons, k=k, gs=gs: max(T1(k, box, cons), T2(gs, box)))
base = sum(count(t, lambda b, c: -np.inf)[0] for t in D['trees'])
print('baseline leaves %d (perfect far test at 1e-1: 7,896)' % base, flush=True)
out = {}
for nm, f in tests.items():
    tot = cert = 0
    for t in D['trees']:
        a, cc = count(t, f); tot += a; cert += cc
    out[nm] = tot
    print('%-22s leaves %6d (%.1f%% of %d; removed %.1f%%); nodes certified by the test %d' % (nm, tot, 100 * tot / base, base, 100 * (1 - tot / base), cert), flush=True)
json.dump(out, open('far_tests_t570.json', 'w'), indent=1)
