"""E39b: POST-REGISTRATION diagnostic (declared after e39): fixed lattice a = 0.99, N = 4P, extend to P = 256, 512 to test the
Bragg-peak-leakage explanation of the negative slope (comb peak at 1/a = 1.0101 just outside the band; its main lobe, width
~1/(P a), overlaps the band until P ~ 1/(a (1/a - 1)) ~ 99, after which only P-independent sidelobes remain).  Predicted: the
slope turns >= 0 by P = 256-512.  Same optimiser and starts as e39."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
rng = np.random.default_rng(77); a = 0.99; prev = (128, 1298.4371)
for P in (256, 512):
    N = 4 * P; M = Model(N, P); n = M.n_on; s = a * np.arange(P); t = np.arange(P) / (P - 1); best = np.inf
    for prof in ('flat', 'arch', 'rand'):
        y0 = np.full(P, 0.8) if prof == 'flat' else (0.8 + 0.7 * np.sin(np.pi * t) ** 0.8 if prof == 'arch' else rng.uniform(0.8, 1.6, P))
        z0 = embed(M, s, y0, rng, 0.02); sfix = z0[n:n + P].copy()
        def f(v):
            z = np.concatenate([v[:n], sfix, v[n:]]); val, g = M.LP(z); return val, np.concatenate([g[:n], g[n + P:]])
        r = minimize(f, np.concatenate([z0[:n], z0[n + P:]]), jac=True, method='L-BFGS-B', bounds=[(None, None)] * n + [(0.8, 3.0)] * P, options={'maxiter': 3000})
        best = min(best, r.fun)
    print('a=0.99 N=4P fixed P=%3d N=%4d: LP %+11.4f (per pair %+.4f) | slope vs P=%d: %+.4f' % (P, N, best, best / P, prev[0], (best - prev[1]) / (P - prev[0])), flush=True)
    prev = (P, best)
