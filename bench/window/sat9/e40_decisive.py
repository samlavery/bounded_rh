"""E40 = DECISIVE TEST for the fixed a = 0.99 family (lead, 2026-10-09).  Fixed BEFORE any run.
(a) EXACT asymptote, pair-pair only, a = 0.99:
    C_end(0.99, y) = 1/2 int_{-1}^{1} q (B_y^2 + 4 B_y)/sin^2(pi a al)  for y in {0.8, 1.0, 1.5, 2.0, 2.5, 3.0} (closed form, e31);
    profile minimum of Q_pp over depths in [0.8, 3] on the exact lattice s_p = 0.99 p, P in {64, 128, 256, 512, 1024}
    (L-BFGS, starts flat 0.8 / arched / the previous P's profile resampled), with T_g^pp(P) and (1') = Q_pp + T_g^pp.
(b) CONVERGED minimisation of the full LP (pSq, periodic, e38 model) for the FIXED lattice a = 0.99, N = 4P, P in {128, 256, 512}:
    variables = environment positions and pair depths, y = 0.8 + u^2 (smooth, bound-free); L-BFGS warm start (3000 its) then
    trust-region Newton-Krylov (scipy 'trust-krylov') with exact Hessian-vector products; stop at ||grad|| <= 1e-6 * ||grad_0||
    or 400 Newton iterations; report ||grad|| (absolute and relative), LP, and the smallest Hessian eigenvalue (Lanczos) to show
    a local minimum, not a saddle.  mp50 re-check if LP < 1.
SUPPORTS: every converged LP > 0, AND converged slope 256 -> 512 >= -0.5 per pair, AND (a) positive asymptote.
REFUTES: a converged LP < 0 (mp50), OR converged slope 256 -> 512 <= -1 per pair.  Otherwise: undecided.
PREDICTION (bridge-port): SUPPORTS.  Converged LP ~ 850-920 at P = 128-512 (a little below the L-BFGS upper bounds 1298/919/911),
  slope 256 -> 512 in [-0.5, +0.2]; (a): C_end(0.99, 0.8) in the thousands, profile-min Q_pp positive and flat in P for P >= 128
  (an end term), so the pair-pair asymptote is end term + tau(0.99) P with tau = 0.019."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
from scipy.sparse.linalg import LinearOperator, eigsh
import mpmath as mp
from common import *
part = sys.argv[1] if len(sys.argv) > 1 else 'a'
A = 0.99
def Tgpp(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
if part == 'a':
    for y in (0.8, 1.0, 1.5, 2.0, 2.5, 3.0):
        B = 2 * np.cosh(2 * np.pi * al * y) - 2
        integ = np.where(al > 0, (B ** 2 + 4 * B) / np.sin(np.pi * A * al) ** 2, 16 * y ** 2 / A ** 2)
        print('C_end(0.99, %.1f) = %.6g' % (y, 0.5 * float(W2 @ integ)), flush=True)
    prev_y = None
    for P in (64, 128, 256, 512, 1024):
        s = A * np.arange(P); E = np.exp(2j * np.pi * np.outer(al, s)); G2 = float(W2 @ (4 * np.abs(E.sum(1)) ** 2))
        def f(y):
            C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
            F = (C * E).sum(1); return float(W2 @ np.abs(F) ** 2) - G2, W2 @ (2 * np.real(np.conj(F)[:, None] * D * E))
        t = np.arange(P) / (P - 1); starts = [np.full(P, 0.8), 0.8 + 0.7 * np.sin(np.pi * t) ** 0.8]
        if prev_y is not None: starts.append(np.interp(t, np.linspace(0, 1, len(prev_y)), prev_y))
        best = (np.inf, None)
        for y0 in starts:
            r = minimize(f, y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 20000, 'gtol': 1e-10})
            g = r.jac.copy(); g[(r.x <= 0.8 + 1e-9) & (g > 0)] = 0
            if r.fun < best[0]: best = (r.fun, r.x, np.linalg.norm(g))
        Q, y, gn = best; T = Tgpp(s); prev_y = y
        print('P=%5d: profile-min Q_pp %+12.5f (proj-grad %.1e) | T_g %10.4f | (1\') = %+12.5f | end-ish Q_pp+T_g - tau P = %+10.4f | depths ends %.2f/%.2f max %.2f'
              % (P, Q, gn, T, Q + T, Q + T - 8 * float(g_of(A * np.arange(1, 400)).sum()) * P, y[0], y[-1], y.max()), flush=True)
else:
    exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
    rng = np.random.default_rng(40); res = {}
    for P in (128, 256, 512):
        N = 4 * P; M = Model(N, P); n = M.n_on; s = A * np.arange(P); t0 = time.time()
        Jv = M.J.astype(float); kap = 2 * np.pi * Jv / N; w = (2 / N) * M.q
        z0 = embed(M, s, 0.8 + 0.7 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8, rng, 0.02); sfix = z0[n:n + P].copy()
        Es = np.exp(1j * np.outer(kap, sfix))                                       # fixed pair phases
        def unpack(v): return v[:n], 0.8 + v[n:] ** 2
        cache = {}
        def fg(v):
            x, y = unpack(v); Ex = np.exp(1j * np.outer(kap, x)); ch = 2 * np.cosh(np.outer(kap, y)); sh = 2 * np.sinh(np.outer(kap, y))
            S = Ex.sum(1) + (ch * Es).sum(1); val = float(w @ np.abs(S) ** 2) - M.const
            dSx = 1j * kap[:, None] * Ex                                              # dS/dx_b
            dSu = (kap[:, None] * sh * Es) * (2 * v[n:])[None, :]                     # dS/du_p
            Jm = np.concatenate([dSx, dSu], 1)
            d2x = -(kap ** 2)[:, None] * Ex
            d2u = (kap[:, None] ** 2 * ch * Es) * (2 * v[n:]) [None, :] ** 2 + (kap[:, None] * sh * Es) * 2.0
            cache['J'] = Jm; cache['S'] = S; cache['d2'] = np.concatenate([d2x, d2u], 1); cache['v'] = v.copy()
            g = 2 * np.real(np.conj(Jm).T @ (w * S))
            return val, g
        def hessp(v, p):
            if 'v' not in cache or not np.array_equal(cache['v'], v): fg(v)
            Jm = cache['J']; S = cache['S']; d2 = cache['d2']
            Jp = Jm @ p
            return 2 * np.real(np.conj(Jm).T @ (w * Jp)) + 2 * np.real((np.conj(S) * w) @ d2) * p
        v0 = np.concatenate([z0[:n], np.sqrt(np.maximum(z0[n + P:] - 0.8, 0)) + 1e-3])
        r1 = minimize(fg, v0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        g0 = np.linalg.norm(fg(r1.x)[1])
        r2 = minimize(fg, r1.x, jac=True, hessp=hessp, method='trust-krylov', options={'maxiter': 400, 'gtol': 1e-6 * g0})
        val, g = fg(r2.x); gn = np.linalg.norm(g)
        Hop = LinearOperator((len(r2.x), len(r2.x)), matvec=lambda p: hessp(r2.x, p))
        try:
            lam = float(eigsh(Hop, k=1, which='SA', tol=1e-6, maxiter=5000, return_eigenvectors=False)[0])
        except Exception as e:
            lam = float('nan')
        z = np.concatenate([r2.x[:n], sfix, 0.8 + r2.x[n:] ** 2])
        vm = M.LP_mp(z) if val < 1 else None
        print('P=%3d N=%4d: L-BFGS %.4f -> Newton LP %+12.6f | ||grad|| %.3e (rel %.2e to %.3e) | Newton its %d, success %s | min Hessian eig %.3e | depths max %.3f | %.0fs%s'
              % (P, N, r1.fun, val, gn, gn / g0, g0, r2.nit, r2.success, lam, (0.8 + r2.x[n:] ** 2).max(), time.time() - t0,
                 (' | mp50 %+.6f' % vm) if vm is not None else ''), flush=True)
        res[P] = {'LP': val, 'grad': gn, 'grad_rel': gn / g0, 'mineig': lam, 'z': z.tolist()}
        json.dump(res, open('e40b_results.json', 'w'))
    if 256 in res and 512 in res:
        print('converged slope 256 -> 512: %+.4f per pair' % ((res[512]['LP'] - res[256]['LP']) / 256), flush=True)
