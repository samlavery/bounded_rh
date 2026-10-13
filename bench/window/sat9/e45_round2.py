"""E45 = ANALYTIC END-TERM STUDY, round 2 (last; lead, 2026-10-09).  Fixed BEFORE any run.
E_end[c] = int_{-1}^{1} q/(4 sin^2(pi a al)) (|A|^2 - 4), A = sum_{p=0}^{L} Dc_p z^p (stable X-form as e44), exact-kernel GL with
n = max(6000, 4 a L + 2000) nodes; depths y = ymin + (5 - ymin) sin^2 u; L-BFGS (3000) then saddle-free damped Newton with the
analytic Hessian (<= 300 its); PD Hessian and ||g|| <= 1e-8 max(1,|E|) required to call a value converged.
(1) ymin = 0.8, a = 0.99, L in {400, 800, 1600}; seeds = previous L's optimum padded with its y_inf (+ e44c L = 400 point).
    min over L <= L_max is non-increasing (padding embeds shorter layers).  Report the sequence and the optimal layer length
    (sites until y within 1% of y_inf).
(2) ymin = 0.01 (end depth free), a in {0.9, 0.95, 0.99}, L in {50, 100, 200, 400}; seeds = e44c optima with the first k sites
    lowered (k in {1, 3, 10}, end depth in {0.01, 0.3}) + fresh ramps from 0.01.  If any E_end < 0: mirror the layer, build the
    finite chain with a flat interior of m sites (P = 2L + m, m in {0, 25, 50, 100, 200, 400}), evaluate (1') = Q_pp + T_g with the
    exact-kernel chain evaluator (e43 Chain); if (1') < 0, run the full LP (e38 model, N = 4P, environment relaxed) and confirm
    in mp50.
SUPPORTS (E_inf): (1) converges above 0 AND (2) finds no negative.  REFUTES: a confirmed negative (1') or full LP.
Otherwise undecided.
(3) Pencil (written in the report): for a stretched smooth ramp, Riemann-Lebesgue in p gives A(al) -> c_0(al) for al away from
    0 and from 1/a, so E_end -> E_const(y_0) = int q (c_{y0}^2 - 4)/(4 sin^2) >= 0; minima below E_const come from finite-length
    interference (the cross term 2 c_0 Re Y, Y = sum_{p>=1} Dc_p z^p).
PREDICTION (bridge-port): (1) still decreasing at L = 1600 (~330 / ~260 / ~210), i.e. UNDECIDED rather than converged-by-800.
  (2) NEGATIVE E_end found at a = 0.9 (the floor E_const(y_0) -> 0 as y_0 -> 0, and interference does the rest), of size
  ~1-10; the finite chain (1') then decides: positive if tau(a) P with P ~ 2L outweighs 2|E_end|."""
import sys, json, time, numpy as np
exec(open('e44_endterm.py').read().rsplit("if __name__ == '__main__':", 1)[0])
YMAX = 5.0
def solve(a, L, ymin, seeds, n=None):
    n = n or max(6000, int(4 * a * L) + 2000); ET = EndTerm(a, L, n); al = ET.al; k = 2 * np.pi * al; wq = ET.wq; z = ET.z
    M = np.concatenate([(1 - z)[:, None] * ET.Zp[:, :L], ET.Zp[:, L:L + 1]], 1)
    def fgh(u, need=True):
        y = ymin + (YMAX - ymin) * np.sin(u) ** 2; yp = (YMAX - ymin) * np.sin(2 * u); ypp = 2 * (YMAX - ymin) * np.cos(2 * u)
        ch = 2 * np.cosh(np.outer(k, y)); cinf = ch[:, L]
        D = np.concatenate([ch[:, :1], np.diff(ch, axis=1)], 1); X = (D[:, 1:] * (ET.Zp[:, 1:L + 1] - 1)).sum(1)
        F = (cinf ** 2 - 4) + 2 * cinf * np.real(X) + np.abs(X) ** 2; f = float(wq @ F)
        if not need: return f, None, None
        sh = 2 * np.sinh(np.outer(k, y)); A = (M * ch).sum(1); Jy = M * (k[:, None] * sh)
        gy = 2 * np.real((wq * np.conj(A)) @ Jy)
        Hy = 2 * np.real(np.conj(Jy).T @ (wq[:, None] * Jy)) + np.diag(2 * np.real((wq * np.conj(A)) @ (M * (k[:, None] ** 2 * ch))))
        return f, gy * yp, Hy * np.outer(yp, yp) + np.diag(gy * ypp)
    def inv(y): return np.arcsin(np.sqrt(np.clip((np.asarray(y, float) - ymin) / (YMAX - ymin), 1e-12, 1 - 1e-12)))
    best = (np.inf, None)
    for y0 in seeds:
        r = minimize(lambda u: fgh(u)[:2], inv(y0), jac=True, method='L-BFGS-B', options={'maxiter': 3000, 'gtol': 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
    u = best[1]; f, g, H = fgh(u)
    for it in range(300):
        lam, V = np.linalg.eigh(H)
        if np.linalg.norm(g) <= 1e-8 * max(1.0, abs(f)) and lam[0] > 0: break
        step = -V @ ((V.T @ g) / np.maximum(np.abs(lam), 1e-10 * np.abs(lam).max() + 1e-12)); t = 1.0
        while t > 1e-14 and fgh(u + t * step, False)[0] > f - 1e-6 * t * abs(g @ step): t *= 0.5
        if t <= 1e-14: break
        u = u + t * step; f, g, H = fgh(u)
    lam0 = float(np.linalg.eigvalsh(H)[0]); y = ymin + (YMAX - ymin) * np.sin(u) ** 2
    conv = np.linalg.norm(g) <= 1e-8 * max(1.0, abs(f)) and lam0 > 0
    return f, y, np.linalg.norm(g), lam0, conv, it
def ramp(L, y0, yi, frac): t = np.arange(L) / max(frac * L, 1); return np.concatenate([y0 + (yi - y0) * (1 - np.exp(-t)), [yi]])
def layer_len(y): yi = y[-1]; d = np.abs(y[:-1] - yi) > 0.01 * max(abs(yi - y[0]), 1e-12); return int(np.nonzero(d)[0].max() + 1) if d.any() else 0
if __name__ == '__main__':
    part = sys.argv[1]
    if part == '1':
        a = 0.99; d = json.load(open('e44c_end_a0.99_L400.json')); prev = np.concatenate([d['y'], [d['yinf']]])
        for L in (400, 800, 1600):
            t0 = time.time(); ext = np.concatenate([prev[:-1], np.full(max(L - (len(prev) - 1), 0), prev[-1]), [prev[-1]]])[:L + 1]; ext[-1] = prev[-1]
            seeds = [ext, ramp(L, 0.8, prev[-1], 0.3), ramp(L, 0.8, min(prev[-1] + 0.5, 4.5), 0.4)]
            f, y, gn, lam, conv, it = solve(a, L, 0.8, seeds); prev = y
            print('(1) a=0.99 L=%4d: min E_end %+.6f | ||g|| %.2e | min eig %+.3e | %s | y_inf %.4f | layer length %d | its %d | %.0fs'
                  % (L, f, gn, lam, 'CONVERGED' if conv else 'not converged', y[-1], layer_len(y), it, time.time() - t0), flush=True)
            json.dump({'a': a, 'L': L, 'E_end': f, 'y': y.tolist(), 'conv': bool(conv)}, open('e45_1_L%d.json' % L, 'w'))
    else:
        a = float(sys.argv[2]); found = []
        for L in (50, 100, 200, 400):
            t0 = time.time(); d = json.load(open('e44c_end_a%.2f_L%d.json' % (a, L))); base = np.concatenate([d['y'], [d['yinf']]])
            seeds = []
            for kk in (1, 3, 10):
                for y0 in (0.01, 0.3):
                    s = base.copy(); s[:kk] = np.linspace(y0, base[kk], kk, endpoint=False); seeds.append(s)
            for yi in (1.5, 2.3):
                seeds.append(ramp(L, 0.01, yi, 0.3))
            f, y, gn, lam, conv, it = solve(a, L, 0.01, seeds)
            print('(2) a=%.2f L=%3d (end depth free): min E_end %+.6f | ||g|| %.2e | min eig %+.3e | %s | y_0 %.4f y_1 %.4f y_inf %.4f | its %d | %.0fs'
                  % (a, L, f, gn, lam, 'CONVERGED' if conv else 'not converged', y[0], y[1], y[-1], it, time.time() - t0), flush=True)
            json.dump({'a': a, 'L': L, 'E_end': f, 'y': y.tolist(), 'conv': bool(conv)}, open('e45_2_a%.2f_L%d.json' % (a, L), 'w'))
            if f < 0: found.append((L, f, y))
        if found:
            exec(open('e43_scalable.py').read().split("if __name__ == '__main__':")[0])
            for (L, f, y) in found:
                layer = y[:-1]; yi = y[-1]
                for m in (0, 25, 50, 100, 200, 400):
                    prof = np.concatenate([layer, np.full(m, yi), layer[::-1]]); P = len(prof); ch = Chain(a, P)
                    v = ch.onep(prof)[0]
                    print('   finite chain a=%.2f L=%d m=%d P=%d: (1\') = Q_pp + T_g = %+.6f (T_g %.4f)' % (a, L, m, P, v, ch.Tg), flush=True)
