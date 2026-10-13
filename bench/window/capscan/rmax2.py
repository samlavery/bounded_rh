"""R_max curve, robust minimisation: smooth objective (sqrt branch for E_band > tau instead of inf), a dense (a, b)
grid for alternating words, Nelder-Mead refinement, and Nelder-Mead multistart over general words q <= 8."""
import sys, math, itertools, time, json
import numpy as np
from scipy.optimize import minimize
from rmax import wbar, kappa, B, tau, m, KMAX
def gt(E): return E if E <= tau else 2 * math.sqrt(tau * E) - tau
def V(g, Rmax, mm=m):
    g = np.abs(np.asarray(g, float))
    w = wbar(g, mm - 1); kk = np.arange(1, mm); Ek = 2 * (mm - kk) * w
    Eb = Ek[:7].sum(); Eo = Ek[7:min(Rmax, mm - 1)].sum() if Rmax > 7 else 0.0
    press = (mm - 7) * B * float(np.mean(g))
    if Eb > tau: return gt(Eb) + press
    beta = 1.0 if Eo <= 0 else min(1.0, (1 - math.sqrt(Eb / tau)) / math.sqrt(Eo))
    return Eb + (2 * beta - beta ** 2) * Eo + press
t0 = time.time(); rng = np.random.default_rng(21); out = {}
for Rmax in [7, 8, 10, 12, 15, 20, 30, 60, KMAX]:
    best = (np.inf, None)
    A_ = np.arange(1.00, 1.1001, 0.004); B_ = np.arange(1.90, 2.0601, 0.004)
    for a in A_:
        for b in B_:
            v = V([a, b], Rmax)
            if v < best[0]: best = (v, np.array([a, b]))
    starts = [best[1]] + [np.array(p) for qq in (3, 4, 5, 6, 7, 8) for p in itertools.product((1.04, 1.97), repeat=qq)][:400:3] \
             + [rng.uniform(0.8, 2.2, qq) for qq in range(2, 9) for _ in range(4)]
    for s0 in starts:
        r = minimize(lambda g: V(g, Rmax), s0, method='Nelder-Mead', options={'xatol': 1e-6, 'fatol': 1e-10, 'maxiter': 4000})
        if r.fun < best[0]: best = (float(r.fun), np.abs(r.x))
    g = best[1]; sums = [g[i] + g[(i + 1) % len(g)] for i in range(len(g))]
    kb = max((kappa(V(g, Rmax, mm), mm), mm) for mm in range(120, 321, 8))
    out[str(Rmax)] = dict(R=best[0], kappa=kappa(best[0]), word=list(map(float, g)), kappa_bestm=kb)
    print('R_max %4s: R = %.6f  kappa(m=152) = %.7f [best m %d: %.7f]  binding q=%d gaps %s  period %.4f  consecutive sums %s (%.0fs)'
          % ('inf' if Rmax == KMAX else Rmax, best[0], kappa(best[0]), kb[1], kb[0], len(g), np.round(g, 4), g.sum(),
             np.round(sums, 4)[:6], time.time() - t0), flush=True)
json.dump(out, open('rmax2_r8.json', 'w'), indent=1)
