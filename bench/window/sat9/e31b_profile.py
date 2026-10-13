"""E31b: lattice positions (exact spacing a), depth PROFILE free in [0.8, 3]: min Q_pp over profiles (analytic gradient),
P = 6, 12, 24, 48; a = 0.6, 0.7, 0.76, 0.8, 0.9.  Is Q_pp >= 0 on exact lattices for every depth profile?"""
import numpy as np
from scipy.optimize import minimize
from common import *
def f(y, s):
    E = np.exp(2j * np.pi * np.outer(al, s)); C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    F = (C * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    return Q, W2 @ (2 * np.real(np.conj(F)[:, None] * D * E))
rng = np.random.default_rng(5)
for a in (0.6, 0.7, 0.76, 0.8, 0.9):
    for P in (6, 12, 24, 48):
        s = a * np.arange(P); best = (np.inf, None)
        for t in range(8):
            if t == 0: y0 = np.full(P, 0.8)
            elif t == 1: y0 = 0.8 + 0.8 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8
            else: y0 = rng.uniform(0.8, 2.0, P)
            r = minimize(f, y0, args=(s,), jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, r.x)
        y = best[1]
        print('a=%.2f P=%2d: min Q_pp over profiles = %+9.4f | profile %s' % (a, P, best[0], np.round(y, 2).tolist() if P <= 24 else np.round(y[::4], 2).tolist()), flush=True)
