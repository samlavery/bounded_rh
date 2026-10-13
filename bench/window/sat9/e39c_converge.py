"""E39c: convergence check for the e39b P = 512 value (fixed lattice a = 0.99, N = 2048): L-BFGS from the flat and arched starts
with maxiter 3000 vs 10000; report the final LP and the projected-gradient norm."""
import numpy as np
from scipy.optimize import minimize
exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
rng = np.random.default_rng(77); a = 0.99
for P in (256, 512):
    N = 4 * P; M = Model(N, P); n = M.n_on; s = a * np.arange(P); t = np.arange(P) / (P - 1)
    for prof in ('flat', 'arch'):
        y0 = np.full(P, 0.8) if prof == 'flat' else 0.8 + 0.7 * np.sin(np.pi * t) ** 0.8
        z0 = embed(M, s, y0, rng, 0.02); sfix = z0[n:n + P].copy()
        def f(v):
            z = np.concatenate([v[:n], sfix, v[n:]]); val, g = M.LP(z); return val, np.concatenate([g[:n], g[n + P:]])
        v0 = np.concatenate([z0[:n], z0[n + P:]])
        for it in (3000, 10000):
            r = minimize(f, v0, jac=True, method='L-BFGS-B', bounds=[(None, None)] * n + [(0.8, 3.0)] * P, options={'maxiter': it, 'maxfun': 3 * it})
            g = r.jac.copy(); yv = r.x[n:]; g[n:][(yv <= 0.8 + 1e-9) & (g[n:] > 0)] = 0; g[n:][(yv >= 3 - 1e-9) & (g[n:] < 0)] = 0
            print('P=%d %s maxiter %5d: LP %+11.4f | proj-grad norm %.2e | nit %d' % (P, prof, it, r.fun, np.linalg.norm(g), r.nit), flush=True)
