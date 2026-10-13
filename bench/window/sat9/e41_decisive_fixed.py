"""E41: the E40 decisive test, RE-RUN after a bug fix, same pre-registration (see e40_decisive.py docstring; unchanged).
BUG in e40 part (b): the gradient-norm variable was named g0, which overwrote the certificate's g(0) used by Model() for the
next P; so the e40 LP values for P = 256, 512 were shifted by -(g0_bug - g(0))(n_on + 4P) (the "mp50" re-checks used the same
corrupted Model constant).  Gradients/minimisers were unaffected.  Corrected values at the e40 configurations: P = 128 +1303.396
(unaffected), P = 256 +871.236, P = 512 +978.538 (recomputed with a fresh Model; e40c below).
SOLVER (upgrade, declared here): exact dense Hessian H = 2 Re(J^H diag(w) J) + diag(2 Re(conj(S) w d2S)), y = 0.8 + u^2, and
scipy 'trust-exact' (full Newton, trust region), warm-started from L-BFGS (part a) or from the saved e40 configurations
(part b).  Stop at ||grad|| <= 1e-6 * ||grad at warm start|| or 300 iterations.  Report ||grad||, its ratio, the smallest
Hessian eigenvalue, and LP.
(a) pair-pair profile minimum of Q_pp at a = 0.99, P in {64, 128, 256, 512, 1024};  (b) full LP, fixed a = 0.99, N = 4P,
P in {128, 256, 512}.  Decision rule as in e40."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
part = sys.argv[1]
A = 0.99
def newton(fgh, v0, maxit=300):
    f0, gr0, _ = fgh(v0); gref = np.linalg.norm(gr0)
    r = minimize(lambda v: fgh(v)[:2], v0, jac=True, hess=lambda v: fgh(v)[2], method='trust-exact',
                 options={'maxiter': maxit, 'gtol': 1e-6 * gref})
    f, gr, H = fgh(r.x); lam = float(np.linalg.eigvalsh(H)[0])
    return r.x, f, np.linalg.norm(gr), gref, lam, r.nit
if part == 'a':
    from common import al, W2, g_of
    tauA = 8 * float(g_of(A * np.arange(1, 400)).sum())
    for P in ([int(a) for a in sys.argv[2].split(',')] if len(sys.argv) > 2 else (64, 128, 256, 512, 1024)):
        t0 = time.time(); s = A * np.arange(P); E = np.exp(2j * np.pi * np.outer(al, s)); G2 = float(W2 @ (4 * np.abs(E.sum(1)) ** 2))
        k2 = (2 * np.pi * al) ** 2
        def fgh(v):
            if (0.8 + v ** 2).max() > 3.0: return 1e30, np.zeros_like(v), np.eye(len(v))   # outside the depth box: reject
            y = 0.8 + v ** 2; ch = 2 * np.cosh(2 * np.pi * np.outer(al, y)); sh = 2 * np.sinh(2 * np.pi * np.outer(al, y))
            S = (ch * E).sum(1); f = float(W2 @ np.abs(S) ** 2) - G2
            dy = (2 * np.pi * al)[:, None] * sh * E; J = dy * (2 * v)[None, :]
            d2 = (k2[:, None] * ch * E) * (2 * v)[None, :] ** 2 + dy * 2.0
            g = 2 * np.real(np.conj(J).T @ (W2 * S))
            H = 2 * np.real(np.conj(J).T @ (W2[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * W2) @ d2))
            return f, g, H
        t = np.arange(P) / (P - 1); best = None
        for y0 in (np.full(P, 0.8) + 1e-4, 0.8 + 0.7 * np.sin(np.pi * t) ** 0.8 + 1e-4):
            v0 = np.sqrt(y0 - 0.8)
            r0 = minimize(lambda v: fgh(v)[:2], v0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            x, f, gn, gref, lam, nit = newton(fgh, r0.x)
            if best is None or f < best[1]: best = (x, f, gn, gref, lam, nit)
        x, f, gn, gref, lam, nit = best; y = 0.8 + x ** 2
        d = s[:, None] - s[None, :]; off = ~np.eye(P, dtype=bool); T = 4 * float(g_of(d[off]).sum())
        print('(a) P=%5d: Q_pp %+13.6f | ||grad|| %.2e (ratio %.1e) | min Hess eig %+.2e | Newton its %d | T_g %.4f | (1\') %+12.5f | (1\') - tau P %+12.5f | depths max %.3f | %.0fs'
              % (P, f, gn, gn / gref, lam, nit, T, f + T, f + T - tauA * P, y.max(), time.time() - t0), flush=True)
else:
    exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
    saved = json.load(open('e40b_results.json')); res = {}
    for P in ([int(a) for a in sys.argv[2].split(',')] if len(sys.argv) > 2 else (128, 256, 512)):
        t0 = time.time(); N = 4 * P; M = Model(N, P); n = M.n_on; z = np.array(saved[str(P)]['z']); sfix = z[n:n + P]
        kap = 2 * np.pi * M.J.astype(float) / N; w = (2 / N) * M.q; Es = np.exp(1j * np.outer(kap, sfix))
        def fgh(v):
            if (0.8 + v[n:] ** 2).max() > 3.0: return 1e30, np.zeros_like(v), np.eye(len(v))   # outside the depth box: reject
            x = v[:n]; u = v[n:]; y = 0.8 + u ** 2
            Ex = np.exp(1j * np.outer(kap, x)); ch = 2 * np.cosh(np.outer(kap, y)); sh = 2 * np.sinh(np.outer(kap, y))
            S = Ex.sum(1) + (ch * Es).sum(1); f = float(w @ np.abs(S) ** 2) - M.const
            dx = 1j * kap[:, None] * Ex; dy = kap[:, None] * sh * Es; du = dy * (2 * u)[None, :]
            J = np.concatenate([dx, du], 1)
            d2 = np.concatenate([-(kap ** 2)[:, None] * Ex, (kap[:, None] ** 2 * ch * Es) * (2 * u)[None, :] ** 2 + dy * 2.0], 1)
            g = 2 * np.real(np.conj(J).T @ (w * S))
            H = 2 * np.real(np.conj(J).T @ (w[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * w) @ d2))
            return f, g, H
        v0 = np.concatenate([z[:n], np.sqrt(np.maximum(z[n + P:] - 0.8, 0)) + 1e-6])
        x, f, gn, gref, lam, nit = newton(fgh, v0)
        zz = np.concatenate([x[:n], sfix, 0.8 + x[n:] ** 2]); check = Model(N, P).LP(zz, False)
        print('(b) P=%3d N=%4d: LP %+13.6f (fresh-Model check %+.6f) | ||grad|| %.2e (ratio %.1e to %.2e) | min Hess eig %+.2e | Newton its %d | depths max %.3f | %.0fs'
              % (P, N, f, check, gn, gn / gref, gref, lam, nit, (0.8 + x[n:] ** 2).max(), time.time() - t0), flush=True)
        res[P] = {'LP': f, 'check': check, 'grad': gn, 'ratio': gn / gref, 'mineig': lam, 'z': zz.tolist()}
        json.dump(res, open('e41b_results_%s.json' % (sys.argv[2] if len(sys.argv) > 2 else 'all'), 'w'))
    if 256 in res and 512 in res:
        print('(b) converged slope 256 -> 512: %+.4f per pair' % ((res[512]['LP'] - res[256]['LP']) / 256), flush=True)
