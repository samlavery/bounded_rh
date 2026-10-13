"""E3: unequal depths.  Q_pp = ||sum_p (B_p + 2) e_p||^2 - ||sum_p 2 e_p||^2 (pairs' own energy minus their doubles').
Equal depths: Q_pp = int q (B^2 + 4B)|V|^2 >= 0 identically.  Unequal: minimise Q_pp over positions and depths y_p in [y0, y1]
(L-BFGS-B, analytic gradient, many starts) and report it against the doubles' own pair cost T_g = sum_{p != p'} 4 g(s_p - s_p').
Also minimise Q_pp + 2 T_g (the part of 2W that the cluster controls without environment: 2W >= 2 T_g + Q_pp + field terms)."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(23)

def Qpp(z, P, lam):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s))
    c = 2 * np.cosh(2 * np.pi * np.outer(al, y))          # B_p + 2
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 2 * 2 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    gy = W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    if lam:
        d = s[:, None] - s[None, :]; iu = np.triu_indices(P, 1)
        Tg = 8 * g_of(d[iu]).sum()
        # gradient of T_g by finite differences (small P)
        h = 1e-6; gT = np.zeros(P)
        for p in range(P):
            sp = s.copy(); sp[p] += h; dd = sp[:, None] - sp[None, :]
            gT[p] = (8 * g_of(dd[iu]).sum() - Tg) / h
        Q += lam * Tg; gs = gs + lam * gT
    return Q, np.concatenate([gs, gy])

def Tg(s):
    P = len(s); d = s[:, None] - s[None, :]; iu = np.triu_indices(P, 1); return float(8 * g_of(d[iu]).sum())

y0, y1 = (float(v) for v in (sys.argv[1].split(',') if len(sys.argv) > 1 else ['0.8', '2.0']))
Ps = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [2, 3, 4, 6, 8]
for lam in (0.0, 2.0):
    print('minimise Q_pp + %.0f T_g over positions and depths in [%.2f, %.2f]' % (lam, y0, y1), flush=True)
    for P in Ps:
        best = (np.inf, None)
        for t in range(40):
            s0 = np.sort(rng.uniform(0, rng.choice([0.5, 1.0, 2.0, 4.0]) * P, P))
            yv = rng.uniform(y0, y1, P)
            r = minimize(lambda z: Qpp(z, P, lam), np.concatenate([s0, yv]), jac=True, method='L-BFGS-B',
                         bounds=[(None, None)] * P + [(y0, y1)] * P, options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, r.x.copy())
        z = best[1]; s, y = z[:P], z[P:]; o = np.argsort(s)
        Q0, _ = Qpp(z, P, 0.0)
        print('  P=%d: min = %+.4e | Q_pp %+.4e, T_g %.4f, ||V||_q^2 %.3f | s %s | y %s'
              % (P, best[0], Q0, Tg(s), float(W2 @ np.abs(np.exp(2j * np.pi * np.outer(al, s)).sum(1)) ** 2),
                 np.round(s[o] - s[o][0], 3), np.round(y[o], 3)), flush=True)
