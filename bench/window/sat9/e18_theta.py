"""E18: per-pair split test for window-scope.  Q_pp = ||sum (2+B_p) e_p||^2 - ||sum 2 e_p||^2 (two-sided),
self_p = int q (B_p^2 + 4 B_p), T_g = sum_{p != p'} 4 g(s_p - s_p')  (the pair-pair part of T_g(D), R convention, which is
the amount carried in LP = s_2(D) + Q_pp + 2 Re<S_on, S_B>).
theta_max(c) := inf over configurations of (Q_pp + c T_g) / sum_p self_p.  A split Q_pp >= theta sum self - c T_g holds iff
theta <= theta_max(c).  (A) exact equal-depth lattices (spacing a, P pairs); (B) P = 2 scan over depths and separation;
(C) adversarial minimisation over positions and depths in [ylo, yhi] (multi-start, Nelder-Mead/L-BFGS on the ratio)."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(31)

def pieces(s, y):
    E = np.exp(2j * np.pi * np.outer(al, s)); Bm = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2
    F = ((Bm + 2) * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    selfs = float((W2 @ (Bm ** 2 + 4 * Bm)).sum())
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool)
    Tg = 4 * float(g_of(d[off]).sum())
    return Q, Tg, selfs

mode = sys.argv[1]
cs = (0.0, 0.5, 1.0)
if mode == 'lattice':
    for y in (0.1, 0.2, 0.4, 0.8):
        for a in (0.5, 1.0, 2.0):
            row = []
            for P in (2, 4, 8, 16, 32, 64):
                Q, Tg, S = pieces(a * np.arange(P, dtype=float), np.full(P, y))
                row.append('P=%2d: %s' % (P, ' '.join('%+.3f' % ((Q + c * Tg) / S) for c in cs)))
            print('y=%.1f a=%.1f  (Q+cT_g)/Σself for c=%s | %s' % (y, a, cs, ' | '.join(row)), flush=True)
elif mode == 'p2':
    ys = tuple(float(v) for v in sys.argv[2].split(',')) if len(sys.argv) > 2 else (0.05, 0.1, 0.2, 0.4, 0.8)
    ds = np.linspace(0.0, 4.0, 801)
    for c in cs:
        worst = (np.inf, None)
        for y1 in ys:
            for y2 in ys:
                for d in ds:
                    Q, Tg, S = pieces(np.array([0.0, d]), np.array([y1, y2]))
                    r = (Q + c * Tg) / S
                    if r < worst[0]: worst = (r, (y1, y2, d, Q, Tg, S))
        print('P=2 c=%.1f: theta_max = %+.4f at y=(%.2f,%.2f) d=%.3f  Q %+.4f T_g %.4f Σself %.4f' % ((c, worst[0]) + worst[1]), flush=True)
else:
    ylo, yhi = (float(v) for v in sys.argv[2].split(',')); Ps = [int(v) for v in sys.argv[3].split(',')]
    for c in cs:
        for P in Ps:
            def f(z):
                s, y = z[:P], np.clip(z[P:], ylo, yhi)
                Q, Tg, S = pieces(s, y); return (Q + c * Tg) / S
            best = (np.inf, None)
            for t in range(24):
                z0 = np.concatenate([np.sort(rng.uniform(0, rng.uniform(0.5, 1.2) * P, P)), rng.uniform(ylo, yhi, P)])
                r = minimize(f, z0, method='L-BFGS-B', bounds=[(None, None)] * P + [(ylo, yhi)] * P, options={'maxiter': 3000})
                if r.fun < best[0]: best = (r.fun, r.x)
            z = best[1]; s, y = z[:P], z[P:]; o = np.argsort(s); Q, Tg, S = pieces(s, y)
            print('y in [%.2f,%.2f] c=%.1f P=%d: theta_max <= %+.4f | Q %+.4f T_g %.4f Σself %.4f | s %s | y %s' % (ylo, yhi, c, P,
                  best[0], Q, Tg, S, np.round(s[o] - s[o][0], 3), np.round(y[o], 3)), flush=True)
