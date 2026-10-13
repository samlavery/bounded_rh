"""E5: harder adversarial search for Q_pp < 0 with deep unequal depths (y_p >= y1).
(a) two depth classes {y1, y2} (P/2 each), positions free, P up to 24, many starts incl. interleaved cancelling clusters;
(b) free depths in [y1, y1 + 2.2], P up to 16.
Q_pp/4 = int q (|sum cosh(2 pi a y_p) e_p|^2 - |sum e_p|^2) (two-sided); reported as Q_pp = 4 x that, with T_g of the doubles."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 41)
y1 = float(sys.argv[1]) if len(sys.argv) > 1 else 0.8

def Q_and_grad_s(s, y):
    E = np.exp(2j * np.pi * np.outer(al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    return Q, gs

def Q_and_grad_sy(z, P):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    F = (c * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    gy = W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    return Q, np.concatenate([gs, gy])

def Tg(s):
    P = len(s); d = s[:, None] - s[None, :]; iu = np.triu_indices(P, 1); return float(8 * g_of(d[iu]).sum())

def starts(P, n):
    out = []
    for t in range(n):
        k = t % 5
        if k == 0: out.append(np.sort(rng.uniform(0, 0.6 * P, P)))
        elif k == 1: out.append(0.5 * np.arange(P) + rng.normal(0, 0.05, P))
        elif k == 2: out.append(np.sort(np.concatenate([0.55 * np.arange(P - P // 2), 0.27 + 0.55 * np.arange(P // 2)])))
        elif k == 3: out.append(np.sort(rng.uniform(0, 2.0 * P, P)))
        else: out.append(np.sort(rng.uniform(0, 0.25 * P + 1, P)))
    return out

print('(a) two depth classes {%.2f, y2}' % y1, flush=True)
for y2 in (0.9, 1.0, 1.2, 1.5):
    for P in (4, 8, 12, 16, 24):
        y = np.array([y1] * (P - P // 2) + [y2] * (P // 2))
        best = (np.inf, None, None)
        for s0 in starts(P, 30):
            yy = rng.permutation(y)
            r = minimize(lambda s: Q_and_grad_s(s, yy), s0, jac=True, method='L-BFGS-B', options={'maxiter': 4000})
            if r.fun < best[0]: best = (r.fun, r.x.copy(), yy)
        Q, s, yy = best
        o = np.argsort(s)
        print('  y2=%.2f P=%2d: min Q_pp %+.4e | T_g %.3f | Q_pp/P %+.3f | depth order %s'
              % (y2, P, Q, Tg(s), Q / P, ''.join('a' if v == y1 else 'b' for v in yy[o])), flush=True)
print('(b) free depths in [%.2f, %.2f]' % (y1, y1 + 2.2), flush=True)
for P in (3, 4, 6, 8, 12, 16):
    best = (np.inf, None)
    for s0 in starts(P, 40):
        y0 = rng.uniform(y1, y1 + rng.choice([0.2, 0.6, 2.2]), P)
        r = minimize(lambda z: Q_and_grad_sy(z, P), np.concatenate([s0, y0]), jac=True, method='L-BFGS-B',
                     bounds=[(None, None)] * P + [(y1, y1 + 2.2)] * P, options={'maxiter': 4000})
        if r.fun < best[0]: best = (r.fun, r.x.copy())
    z = best[1]; s, yv = z[:P], z[P:]; o = np.argsort(s)
    print('  P=%2d: min Q_pp %+.4e | T_g %.3f | Q_pp/P %+.3f | y %s' % (P, best[0], Tg(s), best[0] / P, np.round(yv[o], 3)), flush=True)
