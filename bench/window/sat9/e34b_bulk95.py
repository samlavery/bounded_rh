"""E34b: is the per-pair bulk margin at a = 0.95 really negative?  min over depth profiles in [0.8, 3] of Q_pp + T_g on exact
lattices, P = 32, 48, 64, 96, 128, many starts (flat 0.8, arches of several heights, periodic modulations, random), report
truth(P), truth(P) - P tau(a), and the profile's bulk statistics."""
import numpy as np
from scipy.optimize import minimize
from common import *
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def tau(a): return 8 * float(g_of(a * np.arange(1, 400)).sum())
def prof_min(a, P, rng):
    s = a * np.arange(P); E = np.exp(2j * np.pi * np.outer(al, s)); T = Tg(s); Gs = E.sum(1); G2 = float(W2 @ (4 * np.abs(Gs) ** 2))
    def f(y):
        C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
        F = (C * E).sum(1); return float(W2 @ np.abs(F) ** 2) - G2, W2 @ (2 * np.real(np.conj(F)[:, None] * D * E))
    starts = [np.full(P, 0.8)]
    t = np.arange(P) / (P - 1)
    for h in (0.3, 0.6, 0.9): starts.append(0.8 + h * np.sin(np.pi * t) ** 0.6)
    for per in (2, 3, 4, 6): starts.append(0.8 + 0.3 * (1 + np.cos(2 * np.pi * np.arange(P) / per)) / 2)
    for _ in range(4): starts.append(rng.uniform(0.8, 1.6, P))
    best = (np.inf, None)
    for y0 in starts:
        r = minimize(f, y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 5000})
        if r.fun < best[0]: best = (r.fun, r.x)
    return best[0] + T, best[1], T
rng = np.random.default_rng(9)
for a in (0.9, 0.95, 1.0):
    ta = tau(a); prev = None
    for P in (32, 48, 64, 96, 128):
        tr, y, T = prof_min(a, P, rng)
        mid = y[P // 4: 3 * P // 4]
        print('a=%.2f P=%3d truth %10.3f | T_g %8.3f (P tau %.3f) | Q_pp %+10.3f | truth - P tau %+9.3f | slope vs prev %s | mid-profile mean %.3f std %.3f min %.2f max %.2f'
              % (a, P, tr, T, P * ta, tr - T, tr - P * ta, ('%+.4f' % ((tr - prev[1]) / (P - prev[0]))) if prev else '   -  ', mid.mean(), mid.std(), mid.min(), mid.max()), flush=True)
        prev = (P, tr)
