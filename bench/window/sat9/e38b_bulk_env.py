"""E38b: near-density-1 deep chains WITH environment: pair positions held on an exact lattice of spacing a, depths and the
environment free (relaxed); LP(P) at N = 256 for P = 16, 32, 48, 64; marginal per-pair margin (LP(P2) - LP(P1))/(P2 - P1).
Compares with the pair-pair periodic bulk margin tau(a)."""
import numpy as np
from scipy.optimize import minimize
exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
def tau(a): return 8 * float(g_of(a * np.arange(1, 400)).sum())
rng = np.random.default_rng(5)
for a in (0.9, 0.95, 0.99):
    prev = None
    for P in (16, 32, 48, 64):
        N = 256; M = Model(N, P); n = M.n_on; s = a * np.arange(P)
        best = np.inf
        for prof in ('flat', 'arch'):
            t = np.arange(P) / (P - 1); y0 = np.full(P, 0.8) if prof == 'flat' else 0.8 + 0.7 * np.sin(np.pi * t) ** 0.8
            z0 = embed(M, s, y0, rng); sfix = z0[n:n + P].copy()
            def f(v):
                z = np.concatenate([v[:n], sfix, v[n:]]); val, g = M.LP(z); return val, np.concatenate([g[:n], g[n + P:]])
            r = minimize(f, np.concatenate([z0[:n], z0[n + P:]]), jac=True, method='L-BFGS-B',
                         bounds=[(None, None)] * n + [(0.8, 3.0)] * P, options={'maxiter': 4000})
            best = min(best, r.fun)
        sl = ('%+.4f' % ((best - prev[1]) / (P - prev[0]))) if prev else '   -   '
        print('a=%.2f N=256 P=%2d: min LP %+9.4f (per pair %+.4f) | marginal per added pair %s | tau(a) = %.4f' % (a, P, best, best / P, sl, tau(a)), flush=True)
        prev = (P, best)
