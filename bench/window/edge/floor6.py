"""k = 6 floor, robust: (i) L-BFGS-B from every start in {0.5, 1.04, 1.97, 3.0}^6 (4096 starts) with the exact
kernel; (ii) a non-uniform grid concentrated on the short/long gap scales (27 levels, 27^6 points, tabulated W) with
refinement from the 300 best grid points.  Also re-checks k = 4, 5 by (i)."""
import itertools, json, math, time, numpy as np
from scipy.optimize import minimize
from floors import F_exact, F_grid_batch, bN, aN, SA, R8
def multistart(k, lv=(0.5, 1.04, 1.97, 3.0)):
    best = (np.inf, None)
    for s0 in itertools.product(lv, repeat=k):
        r = minimize(lambda g: F_exact(g, k), np.array(s0), method='L-BFGS-B', bounds=[(0, 60)] * k, options={'ftol': 1e-15, 'gtol': 1e-12})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    return best
t0 = time.time()
for k in (4, 5, 6):
    v, g = multistart(k)
    print('k=%d multistart {0.5,1.04,1.97,3}^k: floor %.10f at %s (%.0fs)' % (k, v, np.round(g, 5), time.time() - t0), flush=True)
lev = np.array([0, 0.5, 0.9, 0.95, 1.0, 1.02, 1.04, 1.06, 1.08, 1.1, 1.2, 1.5, 1.8, 1.9, 1.94, 1.96, 1.98, 2.0, 2.02, 2.05, 2.2, 2.5, 3.0, 3.5, 4.0, 5.0, 8.0])
k = 6; best = []
for v0 in lev:
    rest = np.array(list(itertools.product(lev, repeat=k - 1)))
    Gc = np.concatenate([np.full((rest.shape[0], 1), v0), rest], axis=1)
    vals = F_grid_batch(Gc, k); idx = np.argsort(vals)[:300]
    best = sorted(best + [(float(vals[i]), Gc[i].copy()) for i in idx], key=lambda t: t[0])[:300]
ref = (np.inf, None)
for v, g0 in best:
    r = minimize(lambda g: F_exact(g, k), g0, method='L-BFGS-B', bounds=[(0, 60)] * k, options={'ftol': 1e-15, 'gtol': 1e-12})
    if r.fun < ref[0]: ref = (float(r.fun), r.x.copy())
print('k=6 non-uniform grid (27^6) best %.9f; refined %.10f at %s (%.0fs)' % (best[0][0], ref[0], np.round(ref[1], 5), time.time() - t0), flush=True)
