"""Float prototype: how many bisection leaves does a FIRST-ORDER (mean-value) leaf test need, against the current
ZERO-ORDER test (each pair term's min taken separately)? Same weights, level c, half-space, widest-axis bisection.
w(x) = ((cos(pi x) - 2 gam pi x sin(pi x)) / (1 - 2 pi^2 x^2))^2;  F(g) = sum_r b_r g_r + sum_t a_t w(s_t(g)).
Interval min/max of w and w' via a fine grid + sparse tables (RMQ), padded by grid-step x Lipschitz bound.
Leaf tests:  Z0: sum b_r l_r + sum a_t min_{I_t} w >= c
             F1: F(mid) - sum_r h_r * max|b_r + sum_{t ni r} a_t [w'min_t, w'max_t]| >= c
             HYB: max(Z0, F1) >= c"""
import sys, os, math, itertools, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission")); sys.setrecursionlimit(100000)
import gen_w
Q = 5; pairs, A, Bv = gen_w.load_weights(os.path.expanduser("~/work/riemann-submission/wq_Q5_B0.00180_sym.npz"), Q)
a = {t: float(v) for t, v in A.items()}; b = [float(v) for v in Bv]
S2 = math.sqrt(2.0); GAM = (1/S2)*math.cos(1/S2)/math.sin(1/S2)
H = 2e-6; X = np.arange(0, 40, H)
B_ = math.pi*X
num = np.cos(B_) - 2*GAM*B_*np.sin(B_); den = 1 - 2*B_*B_
with np.errstate(divide='ignore', invalid='ignore'):
    W = (num/den)**2
sing = np.abs(den) < 1e-6; W[sing] = np.interp(X[sing], X[~sing], W[~sing])
dW = np.gradient(W, H)
def sparse(arr, op):
    tab = [arr]; k = 1
    while (1 << k) <= len(arr):
        prev = tab[-1]; tab.append(op(prev[:-(1 << (k-1))], prev[(1 << (k-1)):])); k += 1
    return tab
Tmin, Tmax = sparse(W, np.minimum), sparse(W, np.maximum)
Dmin, Dmax = sparse(dW, np.minimum), sparse(dW, np.maximum)
LIPW = np.max(np.abs(dW[X > 0.4])); LIPD = np.max(np.abs(np.gradient(dW, H)[X > 0.4]))
def q(tab, lo, hi, op):
    i = max(0, int(lo/H)); j = min(len(tab[0]) - 1, int(math.ceil(hi/H)))
    k = (j - i + 1).bit_length() - 1
    return op(tab[k][i], tab[k][j - (1 << k) + 1])
def wmin(lo, hi): return q(Tmin, lo, hi, min) - LIPW*H
def dwr(lo, hi): return q(Dmin, lo, hi, min) - LIPD*H, q(Dmax, lo, hi, max) + LIPD*H
def wpt(x): return float(np.interp(x, X, W))
terms = [(a[(i, j)], tuple(range(i, j))) for (i, j) in pairs if a[(i, j)] != 0]
def Z0(box):
    tot = sum(b[r]*box[r][0] for r in range(Q))
    for coef, idx in terms:
        tot += coef*wmin(sum(box[i][0] for i in idx), sum(box[i][1] for i in idx))
    return tot
def F1(box):
    m = [(lo + hi)/2 for lo, hi in box]; h = [(hi - lo)/2 for lo, hi in box]
    val = sum(b[r]*m[r] for r in range(Q)) + sum(coef*wpt(sum(m[i] for i in idx)) for coef, idx in terms)
    dlo = list(b); dhi = list(b)
    for coef, idx in terms:
        lo, hi = dwr(sum(box[i][0] for i in idx), sum(box[i][1] for i in idx))
        for r in idx: dlo[r] += coef*lo; dhi[r] += coef*hi
    return val - sum(h[r]*max(abs(dlo[r]), abs(dhi[r])) for r in range(Q)) - 1e-12
TESTS = {"Z0": Z0, "F1": F1, "HYB": lambda bx: max(Z0(bx), F1(bx))}
def run(c, test, max_leaves=2_000_000):
    # per-gap bad intervals from the existing 1-D cover (exact), as in gen_w.size
    adj = [A[(r, r+1)] for r in range(Q)]
    S = [Fr(-(-(4*c)//Bv[r]), 4) for r in range(Q)]
    bads = []
    for r in range(Q):
        _, bad = gen_w.G.phase1(c/adj[r], S[r]); bads.append([(float(l), float(u)) for l, u in bad])
    cf = float(c); cnt = [0]; f = TESTS[test]
    def sub(box, d=0):
        if box[0][0] > box[Q-1][1]: cnt[0] += 1; return True           # half-space (reflection)
        if sum(b[r]*box[r][0] for r in range(Q)) >= cf or f(box) >= cf: cnt[0] += 1; return True
        if d > 80 or cnt[0] > max_leaves: return False
        w = [hi - lo for lo, hi in box]; k = w.index(max(w)); mid = (box[k][0] + box[k][1])/2
        l1 = list(box); l1[k] = (box[k][0], mid); l2 = list(box); l2[k] = (mid, box[k][1])
        return sub(tuple(l1), d+1) and sub(tuple(l2), d+1)
    ok = True
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        if sum(b[r]*box[r][0] for r in range(Q)) >= cf: cnt[0] += 1; continue
        if not sub(box): ok = False; break
    return ok, cnt[0]
for delta in [float(x) for x in sys.argv[1:]] or [0.08, 0.06]:
    c = Fr(int(358288*(1 - delta)), 10**8)
    for test in ("Z0", "F1", "HYB"):
        t = time.time(); ok, n = run(c, test)
        print(f"delta {delta:.3f} c={float(c):.8f}  {test:3s}: {'OK ' if ok else 'FAIL'} leaves {n:8d}  ({time.time()-t:.0f}s)", flush=True)
