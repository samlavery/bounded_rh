"""E42 (lead, 2026-10-09): the a = 0.99 question, separated into two parts.  Fixed BEFORE any run.
(i) ENVIRONMENT BASELINE.  Pure on-line periodic structure of density rho: cell of length l = m/rho with m points t_1..t_m
    (m = 1..6, positions optimised), per unit length
      s_env = (2/l^2) sum_{k>=1, k/l<1} q(k/l) |sum_i e(k t_i/l)|^2 + ghat(0) rho^2 - g(0) rho   (>= 0 by the certificate),
    s_env* = min over m and positions.  rho = (N - 2P)/(N - L_chain), ~0.664 at N = 4P, a = 0.99.
    Then LP_chain := LP - L_env * s_env*(rho), L_env = N - L_chain, for the fixed a = 0.99, N = 4P family at P = 128, 256, 512,
    with the environment of EVERY P re-seeded from the optimal s_env* structure (tiled outside the chain) and re-relaxed by
    saddle-free damped Newton (exact Hessian) to ||grad|| <= 1e-6 relative or 3000 iterations; report gradient and min eigenvalue.
(ii) PAIR-PAIR END TERM (statement E).  Q_pp profile minimum on exact lattices, a in {0.99, 0.95, 0.9}, P in {256, 512, 1024},
    depths y = 0.8 + u^2, saddle-free damped Newton (exact Hessian) to ||grad|| <= 1e-8 relative, PD Hessian required at stop.
    Starts: P = 256 from flat/arched (converged first); P = 512, 1024 from the P = 256 profile's end layers (100 sites each,
    the 1/(1/a - 1) scale) with a flat interior at the P = 256 mid value.
    SUPPORTS (E) at 0.99: converged Q_pp(1024) > 0 and |Q_pp(1024) - Q_pp(512)| <= 5%.  REFUTES: any converged Q_pp < 0.
    Otherwise undecided (report the end-layer width).
PREDICTIONS (bridge-port): (i) the optimal environment is dimerised (m = 2) with s_env* ~ 0.01-0.05 per unit length, small and
    positive; LP_chain at P = 128/256/512 is roughly flat and positive (hundreds), the downward trend being largely the
    environment.  (ii) (E) SUPPORTED at a = 0.99: Q_pp(512) and Q_pp(1024) agree within 5% at a positive value in the hundreds;
    a = 0.95 and 0.9 level off lower (tens to ~150)."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
part = sys.argv[1]
def sfn(fgh, v, gtol_rel, maxit, log=None, every=200):
    f, g, H = fgh(v); g0n = np.linalg.norm(g)
    for it in range(maxit):
        lam, V = np.linalg.eigh(H); gn = np.linalg.norm(g)
        if gn <= gtol_rel * g0n and lam[0] > 0: break
        mu = max(1e-10 * np.abs(lam).max(), 1e-9)
        step = -V @ ((V.T @ g) / np.maximum(np.abs(lam), mu)); t = 1.0; ok = False
        while t > 1e-14:
            f2 = fgh(v + t * step, False)[0]
            if f2 < f - 1e-6 * t * abs(g @ step): ok = True; break
            t *= 0.5
        if not ok:
            if gn <= 10 * gtol_rel * g0n: break
            step = -g / max(np.abs(lam).max(), 1.0); t = 1.0
            while t > 1e-14:
                if fgh(v + t * step, False)[0] < f: ok = True; break
                t *= 0.5
            if not ok: break
        v = v + t * step; f, g, H = fgh(v)
        if log and it % every == 0: print('    it %4d f %+.6f |g| %.2e mineig %+.2e' % (it, f, np.linalg.norm(g), lam[0]), flush=True)
    lam = np.linalg.eigvalsh(H)
    return v, f, np.linalg.norm(g), g0n, float(lam[0]), it
if part == 'env':
    exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
    def s_env(t, ell, rho):
        ks = np.arange(1, int(np.floor(ell * 0.9999999)) + 1); al_k = ks / ell; qk = qfun(np.minimum(al_k, 0.9999999))
        F = np.exp(2j * np.pi * np.outer(al_k, t)).sum(1)
        return (2 / ell ** 2) * float(qk @ np.abs(F) ** 2) + gh0 * rho ** 2 - g0 * rho
    rng = np.random.default_rng(42)
    rho = 2.0 / (4 - 0.99) if len(sys.argv) < 3 else float(sys.argv[2])
    best = (np.inf, None, None)
    for m in range(1, 7):
        ell = m / rho
        for t_ in range(40 if m > 1 else 1):
            t0 = np.sort(rng.uniform(0, ell, m)) if m > 1 else np.zeros(1)
            r = minimize(lambda t: s_env(t, ell, rho), t0, method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-14, 'maxiter': 20000})
            if r.fun < best[0]: best = (r.fun, m, np.sort(np.mod(r.x - r.x.min(), ell)))
        print('  rho %.4f m=%d: best so far s_env* %.6f (m*=%d, cell %s)' % (rho, m, best[0], best[1], np.round(best[2], 4)), flush=True)
    print('ENV BASELINE rho=%.4f: s_env*(rho) = %.6f per unit length (uniform lattice: %.6f), structure m=%d, positions %s'
          % (rho, best[0], s_env(np.zeros(1), 1 / rho, rho), best[1], np.round(best[2], 4)), flush=True)
    json.dump({'rho': rho, 's_env': best[0], 'm': best[1], 'cell': best[2].tolist()}, open('e42_env_baseline.json', 'w'))
elif part == 'chain':
    exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
    base = json.load(open('e42_env_baseline.json')); A = 0.99
    for P in [int(x) for x in sys.argv[2].split(',')]:
        t0 = time.time(); N = 4 * P; M = Model(N, P); n = M.n_on; s = 2.0 + A * np.arange(P); Lc = s[-1] - s[0]
        ell = base['m'] / base['rho']; cell = np.array(base['cell'])
        start = s[-1] + 1.0; xs = []
        k = 0
        while len(xs) < n:
            for c in cell:
                xs.append(start + k * ell + c)
            k += 1
        x = np.array(xs[:n]); x = start + (x - start) * ((N - Lc - 2.0) / (x.max() - start + 1.0))   # fit the environment window
        prior = json.load(open('e40b_results.json')).get(str(P)) if P in (128, 256, 512) else None
        y0 = np.array(prior['z'])[n + P:] if prior is not None else 0.8 + 0.7 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8
        kap = 2 * np.pi * M.J.astype(float) / N; w = (2 / N) * M.q; Es = np.exp(1j * np.outer(kap, s))
        def fgh(v, need=True):
            if (0.8 + v[n:] ** 2).max() > 3.0: return np.inf, None, None
            xx = v[:n]; u = v[n:]; y = 0.8 + u ** 2
            Ex = np.exp(1j * np.outer(kap, xx)); ch = 2 * np.cosh(np.outer(kap, y)); sh = 2 * np.sinh(np.outer(kap, y))
            S = Ex.sum(1) + (ch * Es).sum(1); f = float(w @ np.abs(S) ** 2) - M.const
            if not need: return f, None, None
            dx = 1j * kap[:, None] * Ex; dy = kap[:, None] * sh * Es; du = dy * (2 * u)[None, :]
            J = np.concatenate([dx, du], 1)
            d2 = np.concatenate([-(kap ** 2)[:, None] * Ex, (kap[:, None] ** 2 * ch * Es) * (2 * u)[None, :] ** 2 + dy * 2.0], 1)
            g = 2 * np.real(np.conj(J).T @ (w * S))
            H = 2 * np.real(np.conj(J).T @ (w[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * w) @ d2))
            return f, g, H
        v0 = np.concatenate([x, np.sqrt(np.maximum(y0 - 0.8, 0)) + 1e-6])
        r = minimize(lambda v: fgh(v)[:2] if np.isfinite(fgh(v, False)[0]) else (1e30, np.zeros_like(v)), v0, jac=True, method='L-BFGS-B', options={'maxiter': 2000})
        v, f, gn, g0n, lam, it = sfn(fgh, r.x, 1e-6, 3000)
        zz = np.concatenate([v[:n], s, 0.8 + v[n:] ** 2]); check = Model(N, P).LP(zz, False)
        rho = (N - 2 * P) / (N - Lc); Lenv = N - Lc
        print('(i) P=%3d N=%4d: LP %+.6f (fresh %+.6f) | ||grad|| %.2e (rel %.1e) mineig %+.2e its %d | env density %.4f, L_env %.1f -> LP_chain = LP - L_env*s_env* = %+.4f | %.0fs'
              % (P, N, f, check, gn, gn / g0n, lam, it, rho, Lenv, f - Lenv * base['s_env'], time.time() - t0), flush=True)
        json.dump({'LP': f, 'z': zz.tolist()}, open('e42_chain_P%d.json' % P, 'w'))
else:   # part 'pp': pair-pair end term
    from common import al, W2, g_of
    for A in [float(x) for x in sys.argv[2].split(',')]:
        prof256 = None
        for P in (256, 512, 1024):
            t0 = time.time(); s = A * np.arange(P); E = np.exp(2j * np.pi * np.outer(al, s)); G2 = float(W2 @ (4 * np.abs(E.sum(1)) ** 2))
            k2 = (2 * np.pi * al) ** 2
            def fgh(v, need=True):
                if (0.8 + v ** 2).max() > 3.0: return np.inf, None, None
                y = 0.8 + v ** 2; ch = 2 * np.cosh(2 * np.pi * np.outer(al, y)); sh = 2 * np.sinh(2 * np.pi * np.outer(al, y))
                S = (ch * E).sum(1); f = float(W2 @ np.abs(S) ** 2) - G2
                if not need: return f, None, None
                dy = (2 * np.pi * al)[:, None] * sh * E; J = dy * (2 * v)[None, :]
                d2 = (k2[:, None] * ch * E) * (2 * v)[None, :] ** 2 + dy * 2.0
                g = 2 * np.real(np.conj(J).T @ (W2 * S))
                H = 2 * np.real(np.conj(J).T @ (W2[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * W2) @ d2))
                return f, g, H
            if P == 256:
                starts = [np.full(P, 0.8) + 1e-4, 0.8 + 0.7 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8 + 1e-4]
            else:
                L = 100; mid = prof256[len(prof256) // 2]; y0 = np.full(P, mid); y0[:L] = prof256[:L]; y0[-L:] = prof256[-L:]; starts = [y0]
            best = None
            for y0 in starts:
                r = minimize(lambda v: fgh(v)[:2] if np.isfinite(fgh(v, False)[0]) else (1e30, np.zeros_like(v)), np.sqrt(np.maximum(y0 - 0.8, 0)) + 1e-6,
                             jac=True, method='L-BFGS-B', options={'maxiter': 3000})
                out = sfn(fgh, r.x, 1e-8, 400)
                if best is None or out[1] < best[1]: best = out
            v, f, gn, g0n, lam, it = best; y = 0.8 + v ** 2
            if P == 256: prof256 = y.copy()
            dev = np.abs(y - y[len(y) // 2]); wl = int(np.argmax(dev < 0.01 * max(dev.max(), 1e-12)))
            print('(ii) a=%.2f P=%4d: Q_pp %+.6f | ||grad|| %.2e (rel %.1e) | mineig %+.3e (%s) | its %d | end layer (|y - y_mid| > 1%% of max dev) %d sites | depths ends %.3f mid %.3f max %.3f | %.0fs'
                  % (A, P, f, gn, gn / g0n, lam, 'PD' if lam > 0 else 'NOT PD', it, wl, y[0], y[len(y) // 2], y.max(), time.time() - t0), flush=True)
