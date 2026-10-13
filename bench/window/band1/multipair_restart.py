"""Restarts for the densest case of multipair_denseN.py (N = 128, block of 64 equal-depth pairs, contiguous vacancies):
random perturbations (sigma 0.15, 0.3) and inward-compressed starts, all positions relaxed; minimum W per defect."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', 128"))
rr = np.random.default_rng(23); P = 64
cen0 = np.arange(P, dtype=float); xon0 = np.array([t for t in range(P, N) if t not in set(range(P, 2 * P))], float)
for y in (0.2, 0.4):
    best = np.inf; ys = np.full(P, y)
    for t in range(8):
        cen = cen0 * (0.97 if t == 6 else 1.0) + (rr.normal(0, 0.15 if t < 3 else 0.3, P) if t < 6 else 0.0)
        xon = xon0 + (rr.normal(0, 0.15, len(xon0)) if t < 6 else 0.0)
        if t == 7: cen = cen0 + 0.5 * (np.arange(P) % 2)       # staggered start
        z = np.concatenate([xon, cen]); n1 = len(xon)
        r = minimize(lambda zz: d_and_grad(zz, n1, 0, P, ys), z, jac=True, method='L-BFGS-B', options={'maxiter': 8000})
        W = (r.fun / N - N * (gN0 - gh0) / 2 - gN0 * P) / P / g0; best = min(best, W)
        print('  y=%.1f start %d: relaxed W/defect %+.5f' % (y, t, W), flush=True)
    print('y=%.1f: MIN over restarts W/defect %+.5f (units 2 delta\')' % (y, best), flush=True)
