"""E6: Lambda_min(P, y) = min over positions of Lambda = int q B_y |V|^2 (two-sided), P up to 32; Lambda is increasing in y
for fixed positions (B_y increasing in y), so y = y1 is the worst case for equal depths.  Also the ratio K/g on [0, 0.85]
and sup_{|u| >= 0.85} K (for bounding ||S_on^near||^2 by T_g)."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(3)

def L_and_grad(s, wB):
    E = np.exp(2j * np.pi * np.outer(al, s)); V = E.sum(1)
    G = 2 * np.real(np.conj(V)[:, None] * (2j * np.pi * al[:, None]) * E)
    return float(wB @ np.abs(V) ** 2), wB @ G

y = float(sys.argv[1]) if len(sys.argv) > 1 else 0.8
wB = W2 * B(y)
print('y = %.2f: L_y(0) = %.4f (single pair)' % (y, float(wB.sum())), flush=True)
for P in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32):
    best = (np.inf, None)
    for t in range(30):
        k = t % 4
        if k == 0: s0 = np.sort(rng.uniform(0, 0.6 * P, P))
        elif k == 1: s0 = rng.choice([0.4, 0.5, 0.6, 0.75]) * np.arange(P) + rng.normal(0, 0.02, P)
        elif k == 2: s0 = np.sort(rng.uniform(0, 2 * P, P))
        else: s0 = np.sort(rng.uniform(0, 0.2 * P + 0.5, P))
        r = minimize(lambda s: L_and_grad(s, wB), s0, jac=True, method='L-BFGS-B', options={'maxiter': 4000})
        if r.fun < best[0]: best = (r.fun, np.sort(r.x - r.x.min()))
    s = best[1]
    print('  P=%2d: Lambda_min = %.4f  (/L(0) = %.3f) | diam %.2f | gaps %s' % (P, best[0], best[0] / wB.sum(), s[-1], np.round(np.diff(s)[:8], 3)), flush=True)
u = np.linspace(0.0, 0.85, 171); Ku = K_of(u); gu = g_of(u)
print('K/g on [0, 0.85]: max %.4f at u = %.3f' % (np.max(Ku / gu), u[np.argmax(Ku / gu)]), flush=True)
uu = np.linspace(0.85, 40, 40000); KK = K_of(uu)
print('sup_{u >= 0.85} K = %.4e; sum_{n>=1} sup_{|u-n|<=1/2, u>=0.85} K = %.4e' %
      (KK.max(), sum(KK[(uu >= max(0.85, n - 0.5)) & (uu <= n + 0.5)].max() for n in range(1, 40))), flush=True)
