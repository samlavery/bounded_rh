"""E19: the slack-assisted replacement of item (1) in the deep regime.
(1')  Q_pp + c T_g^pp >= 0,  T_g^pp = 4 sum_{p != p'} g(s_p - s_p'),  depths y_p in [ylo, yhi].
Exact identity (pencil): Q_pp + T_g^pp = ||S_A||_q^2 - 4 g0 P - 4 sum_{p,p'} h(s_p - s_p'),  S_A = sum_p 2cosh(2 pi a y_p) e(a s_p).
Adversarial minimisation of (Q_pp + c T_g^pp)/P (analytic gradients; g tabulated), random and stack-like starts.
Also reports ||S_A||^2/P and H = sum_{p != p'} h at the minimiser, and checks the identity."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 3)
U = np.linspace(0.0, 64.0, 128001); GT = g_of(U); GT[0] = g0; dGT = np.gradient(GT, U)
def gtab(u):
    a = np.abs(u); v = np.interp(a, U, GT, right=0.0); d = np.interp(a, U, dGT, right=0.0) * np.sign(u); return v, d
ylo, yhi = (float(v) for v in sys.argv[1].split(',')); Ps = [int(v) for v in sys.argv[2].split(',')]; c = float(sys.argv[3])

def f(z, P):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    F = (ch * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * ch * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    gy = W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    d = s[:, None] - s[None, :]; gv, gd = gtab(d); np.fill_diagonal(gv, 0.0); np.fill_diagonal(gd, 0.0)
    T = 4 * gv.sum(); gT = 8 * gd.sum(1)
    return (Q + c * T) / P, np.concatenate([gs + c * gT, gy]) / P

def report(z, P):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    SA = float(W2 @ np.abs((ch * E).sum(1)) ** 2); V2 = float(W2 @ np.abs(E.sum(1)) ** 2)
    d = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool)
    Tg = 4 * float(g_of(d[off]).sum()); H = float((K_of(d[off]) - g_of(d[off])).sum())
    Q = SA - 4 * V2
    return Q, Tg, SA, H, Q + Tg - (SA - 4 * g0 * P - 4 * (P * (1 - g0) + H))

for P in Ps:
    best = (np.inf, None)
    for t in range(40):
        kind = t % 3
        if kind == 0:
            s0 = np.sort(rng.uniform(0, rng.uniform(0.3, 1.0) * P, P))
        elif kind == 1:   # stacks: k sites, pairs distributed, chain between
            k = max(2, P // rng.integers(2, 5)); sites = np.sort(rng.uniform(0, 0.7 * k, k))
            s0 = np.sort(sites[rng.integers(0, k, P)] + rng.normal(0, 0.01, P))
        else:
            s0 = np.sort(0.6 * np.arange(P) + rng.normal(0, 0.05, P))
        y0 = rng.uniform(ylo, min(yhi, ylo + 1.5), P)
        r = minimize(f, np.concatenate([s0, y0]), args=(P,), jac=True, method='L-BFGS-B',
                     bounds=[(None, None)] * P + [(ylo, yhi)] * P, options={'maxiter': 5000})
        if r.fun < best[0]: best = (r.fun, r.x.copy())
    z = best[1]; s, y = z[:P], z[P:]; o = np.argsort(s)
    Q, Tg, SA, H, idchk = report(z, P)
    print('y in [%.2f,%.2f] c=%.2f P=%2d: min (Q_pp + c T_g)/P = %+9.4f | Q_pp %+10.3f  T_g^pp %9.3f  ||S_A||^2/P %9.3f  H %+.4f  (identity err %.1e)'
          % (ylo, yhi, c, P, best[0], Q, Tg, SA / P, H, idchk), flush=True)
    print('    s', np.round(s[o] - s[o][0], 3).tolist(), '\n    y', np.round(y[o], 3).tolist(), flush=True)
