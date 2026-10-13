"""E11: the deep pair-pair term for SEPARATED pairs (distinct zeros): positions parametrised by gaps >= dmin, depths free in
[0.8, 3].  Minimise Q_pp; report min Q_pp, T_g (distinct points, ordered pairs) and save the minimiser."""
import sys, json, numpy as np
from scipy.optimize import minimize
import common as C
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
y1 = 0.8
dmin = float(sys.argv[1]) if len(sys.argv) > 1 else 0.1
Ps = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [8, 16, 24]

def obj(z, P):
    gaps, y = z[:P - 1], z[P - 1:]
    s = np.concatenate([[0.0], np.cumsum(gaps)])
    E = np.exp(2j * np.pi * np.outer(C.al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(C.al, y))
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(C.W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * C.al[:, None]
    gs = C.W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    gg = np.cumsum(gs[::-1])[::-1][1:]          # d/d gap_j = sum_{p > j} d/ds_p
    dc = 4 * np.pi * C.al[:, None] * np.sinh(2 * np.pi * np.outer(C.al, y))
    gy = C.W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    return Q, np.concatenate([gg, gy])

def Tg(s):
    P = len(s); D = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool); return float(4 * C.g_of(D[off]).sum())

for P in Ps:
    best = (np.inf, None)
    for t in range(24):
        g0 = np.maximum(dmin, rng.choice([0.4, 0.55, 0.7, 1.0]) + rng.normal(0, 0.15, P - 1))
        y0 = np.where(rng.uniform(size=P) < 0.6, y1, rng.uniform(y1, 1.5, P))
        r = minimize(lambda z: obj(z, P), np.concatenate([g0, y0]), jac=True, method='L-BFGS-B',
                     bounds=[(dmin, None)] * (P - 1) + [(y1, 3.0)] * P, options={'maxiter': 6000})
        if r.fun < best[0]: best = (r.fun, r.x.copy())
    z = best[1]; s = np.concatenate([[0.0], np.cumsum(z[:P - 1])]); yv = z[P - 1:]
    json.dump({'s': s.tolist(), 'y': yv.tolist(), 'Qpp': best[0], 'Tg': Tg(s)}, open('e11_cfg_%g_%d.json' % (dmin, P), 'w'))
    print('dmin=%.2f P=%2d: min Q_pp %+.4e | T_g %.3f | gaps %s | y %s' % (dmin, P, best[0], Tg(s), np.round(z[:P - 1], 3)[:10],
          np.round(yv, 2)[:10]), flush=True)
