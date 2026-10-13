"""E9: how negative can the deep pair-pair term get, and does the exact W follow?
For each P: minimise Q_pp over positions and free depths in [0.8, 3] (continuum alpha grid), save the minimiser at once
(e9_cfg_<P>.json), then compute the exact Lemma P W (periodic model of band1/lemmaP.py, backed R8 certificate) with the
cluster embedded in a lattice environment: environment relaxed (cluster fixed); then centres + environment relaxed (depths
fixed); then everything relaxed with depths free in [0.8, 3]."""
import sys, json, numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '.')
import common as C
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 99)
y1 = 0.8

def Qobj(z, P):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(C.al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(C.al, y))
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(C.W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * C.al[:, None]
    gs = C.W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 4 * np.pi * C.al[:, None] * np.sinh(2 * np.pi * np.outer(C.al, y))
    gy = C.W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    return Q, np.concatenate([gs, gy])

def Tg(s):
    P = len(s); D = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool); return float(4 * C.g_of(D[off]).sum())

Ps = [int(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [16, 24, 32, 48]
NS = int(sys.argv[3]) if len(sys.argv) > 3 else 24
for P in Ps:
    best = (np.inf, None)
    for t in range(NS):
        k = t % 4
        if k == 0: s0 = np.sort(rng.uniform(0, 0.6 * P, P))
        elif k == 1: s0 = rng.choice([0.5, 0.6, 0.7]) * np.arange(P) + rng.normal(0, 0.05, P)
        elif k == 2: s0 = np.sort(rng.uniform(0, 0.3 * P + 1, P))
        else: s0 = np.sort(rng.uniform(0, 0.45 * P, P))
        y0 = np.where(rng.uniform(size=P) < 0.7, y1, rng.uniform(y1, 1.4, P))
        r = minimize(lambda z: Qobj(z, P), np.concatenate([s0, y0]), jac=True, method='L-BFGS-B',
                     bounds=[(None, None)] * P + [(y1, 3.0)] * P, options={'maxiter': 6000})
        if r.fun < best[0]: best = (r.fun, r.x.copy())
    z = best[1]; s, yv = z[:P], z[P:]; o = np.argsort(s); s = s[o] - s[o][0]; yv = yv[o]
    cfg = {'s': s.tolist(), 'y': yv.tolist(), 'Qpp': best[0], 'Tg': Tg(s)}
    json.dump(cfg, open('e9_cfg_%d.json' % P, 'w'))
    print('P=%2d: min Q_pp %+.4e | T_g %.3f | Q_pp/T_g %+.4f | Q_pp/P %+.4f | #deep>0.81: %d | diam %.2f'
          % (P, best[0], cfg['Tg'], best[0] / cfg['Tg'], best[0] / P, int(np.sum(yv > 0.81)), s[-1]), flush=True)
