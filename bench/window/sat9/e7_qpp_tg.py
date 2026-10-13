"""E7: the unequal-depth pair-pair term with the doubles' own cost.  Minimise Q_pp + lam * T_g over positions and free
depths y_p in [y1, 3] (T_g = sum_{p != p'} 4 g(s_p - s_p'), ordered pairs; 2 s(D) >= T_g), P up to 32, lam in a grid;
saves the minimisers to e7_best.json for the exact-W check (e8)."""
import sys, json, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 77)
y1 = 0.8

# analytic gradient of g: g(u) = Dk sinc^2(Dk u) C(2 pi Dk u)
def g_and_dg(u):
    u = np.asarray(u, float); h = 1e-6
    return g_of(u), (g_of(u + h) - g_of(u - h)) / (2 * h)

def obj(z, P, lam):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    gy = W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    if lam:
        D = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool)
        gv, dg = g_and_dg(D[off])
        Tg = 4 * gv.sum()
        dG = np.zeros((P, P)); dG[off] = dg
        gs = gs + lam * 4 * 2 * dG.sum(1)        # d/ds_p of sum_{p != p'} g(s_p - s_p') counts both orders
        Q += lam * Tg
    return Q, np.concatenate([gs, gy])

def Tg(s):
    P = len(s); D = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool); return float(4 * g_of(D[off]).sum())

def starts(P, n):
    out = []
    for t in range(n):
        k = t % 4
        if k == 0: out.append(np.sort(rng.uniform(0, 0.6 * P, P)))
        elif k == 1: out.append(rng.choice([0.5, 0.6, 0.7]) * np.arange(P) + rng.normal(0, 0.05, P))
        elif k == 2: out.append(np.sort(rng.uniform(0, 0.3 * P + 1, P)))
        else: out.append(np.sort(rng.uniform(0, 1.2 * P, P)))
    return out

lams = [float(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [0.0, 0.05, 0.1, 0.25]
save = {}
for lam in lams:
    print('minimise Q_pp + %.3f T_g, depths in [%.1f, 3]' % (lam, y1), flush=True)
    for P in (12, 16, 24, 32):
        best = (np.inf, None)
        for s0 in starts(P, 36):
            y0 = np.where(rng.uniform(size=P) < 0.7, y1, rng.uniform(y1, 1.4, P))
            r = minimize(lambda z: obj(z, P, lam), np.concatenate([s0, y0]), jac=True, method='L-BFGS-B',
                         bounds=[(None, None)] * P + [(y1, 3.0)] * P, options={'maxiter': 5000})
            if r.fun < best[0]: best = (r.fun, r.x.copy())
        z = best[1]; s, yv = z[:P], z[P:]; o = np.argsort(s)
        Q0, _ = obj(z, P, 0.0)
        print('  P=%2d: min %+.4e | Q_pp %+.4e | T_g %.3f | Q_pp/T_g %+.4f | depths>%.2f: %d'
              % (P, best[0], Q0, Tg(s), Q0 / Tg(s), y1 + 0.01, int(np.sum(yv > y1 + 0.01))), flush=True)
        save['%g,%d' % (lam, P)] = {'s': (s[o] - s[o][0]).tolist(), 'y': yv[o].tolist(), 'Qpp': Q0, 'Tg': Tg(s)}
json.dump(save, open('e7_best.json', 'w'))
