"""E20: the minimiser family of e19 (arched chains): P pairs at spacing a, depths y_p = 0.8 + A sin(pi t_p)^k, t_p = p/(P-1).
Minimise Q_pp + T_g^pp over (a, A, k) for large P (Nelder-Mead, multi-start).  Is the total bounded below by a positive constant?"""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
def tot(par, P):
    a, A, k = par
    if a <= 0.05 or A < 0 or k <= 0.1: return 1e9
    s = a * np.arange(P); t = np.arange(P) / (P - 1); y = 0.8 + A * np.sin(np.pi * t) ** k
    E = np.exp(2j * np.pi * np.outer(al, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    Q = float(W2 @ (np.abs((ch * E).sum(1)) ** 2 - 4 * np.abs(E.sum(1)) ** 2))
    d = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool); T = 4 * float(g_of(d[off]).sum())
    return Q + T
rng = np.random.default_rng(5)
for P in [int(v) for v in sys.argv[1].split(',')]:
    best = (np.inf, None)
    for t in range(12):
        x0 = [rng.uniform(0.55, 1.0), rng.uniform(0.0, 1.5), rng.uniform(0.3, 2.0)]
        r = minimize(tot, x0, args=(P,), method='Nelder-Mead', options={'maxiter': 600, 'xatol': 1e-4, 'fatol': 1e-4})
        if r.fun < best[0]: best = (r.fun, r.x)
    print('P=%3d: min (Q_pp + T_g^pp) over arches = %+9.3f  (/P %+.4f) at a=%.4f A=%.4f k=%.3f' % ((P, best[0], best[0] / P) + tuple(best[1])), flush=True)
