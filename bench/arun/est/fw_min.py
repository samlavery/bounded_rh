"""Estimate round (a)-(c): the eight-point functional Fw of MOP's certificate W8 (aW8/bW8 read from MOP_Solution.lean),
  Fw(g) = sum_r b_r g_r + sum_{i<j} a_ij wfun(p_j - p_i),  p = partial sums of g,  wfun = kfun^2, kfun = K/K(0),
  K(x) = sum_j c_j (sinc((w_j - 2 pi x)/2) + sinc((w_j + 2 pi x)/2))/2, w_0 = sqrt 2, w_j = 2 pi j (the R8 window).
Minimised over g in [lo, 30]^7 by multi-start L-BFGS-B, for lo = 0 (MOP's hCert domain) and lo = 17/20 (the separated
remainder's actual domain), plus a scan in lo.  Prints the minimisers.  usage: python3 fw_min.py [NSTART]"""
import sys, json, numpy as np
from scipy.optimize import minimize
NST = int(sys.argv[1]) if len(sys.argv) > 1 else 400
cn = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum']
c = np.array(cn, float) / cn[0]; w = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(c))])
def K(x):
    x = np.asarray(x, float)[..., None]
    a = (w - 2 * np.pi * x) / 2; b = (w + 2 * np.pi * x) / 2
    return ((np.sinc(a / np.pi) + np.sinc(b / np.pi)) / 2 * c).sum(-1)
K0 = float(K(0.0))
def wfun(x): return (K(x) / K0) ** 2
def dwfun(x, h=1e-6): return (wfun(x + h) - wfun(x - h)) / (2 * h)
A = np.zeros((8, 8))
src = open('/Users/samuellavery/work/riemann-submission/bench/arun/MOP_Solution.lean').read()
blk = src[src.index('def aW8 : Fin 8 → Fin 8 → ℝ'):src.index('def bW8')]
import re
for i, j, v in re.findall(r'\| (\d), (\d) => \((\d+) : ℝ\) / 100000000', blk): A[int(i), int(j)] = int(v) / 1e8
blk2 = src[src.index('def bW8 : Fin 7 → ℝ'):src.index('def W8 : WCert 8')]
bw = np.array([int(v) / 1e8 for _, v in re.findall(r'\| (\d) => \((\d+) : ℝ\) / 100000000', blk2)])
assert abs(bw.sum() - 0.0040435) < 1e-12, bw.sum()
I, J = np.triu_indices(8, 1); aij = A[I, J]
def Fw(g):
    p = np.concatenate([[0.0], np.cumsum(g)]); d = p[J] - p[I]
    return float(bw @ g + aij @ wfun(d))
def gradF(g):
    p = np.concatenate([[0.0], np.cumsum(g)]); d = p[J] - p[I]; dw = dwfun(d) * aij
    gr = bw.copy()
    for k in range(7):          # d_ij depends on g_k iff i <= k < j
        m = (I <= k) & (J > k); gr[k] += dw[m].sum()
    return gr
def fmin(lo, nst=NST, seed=0):
    rng = np.random.default_rng(seed); best = (np.inf, None)
    starts = [np.full(7, max(lo, v)) for v in (0.5, 0.85, 1.0, 1.5)] + [rng.uniform(lo, lo + 3, 7) for _ in range(nst)]
    for g0 in starts:
        r = minimize(lambda g: (Fw(g), gradF(g)), g0, jac=True, method='L-BFGS-B', bounds=[(lo, 30.0)] * 7, options={'ftol': 1e-15, 'gtol': 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
    return best
print('window K(0) = %.6f; wfun(17/20) = %.6f (>= 1/64 = %.6f); a capacity check: max spanMass = %.4f' % (K0, wfun(0.85), 1 / 64,
      max(sum(A[i, i + s] for i in range(8 - s)) for s in range(1, 8))))
f0, g0 = fmin(0.0)
print('lo = 0    : min Fw = %.8f (MOP floor c = 0.00805124) at gaps %s' % (f0, np.round(g0, 4)))
f1, g1 = fmin(0.85)
print('lo = 0.85 : min Fw = %.8f at gaps %s' % (f1, np.round(g1, 4)))
H, B = 0.67216841, 0.0040435
for nm, cc in (('MOP c', 0.00805124), ('min lo=0', f0), ('min lo=0.85', f1)):
    print('  kappa = (H - B)/(1 - c) with c = %s = %.8f: %.8f' % (nm, cc, (H - B) / (1 - cc)))
for lo in (0.3, 0.5, 0.7, 0.8, 0.9, 1.0):
    f, g = fmin(lo, nst=150, seed=1); print('scan lo = %.2f: min Fw %.8f at %s' % (lo, f, np.round(g, 3)))
