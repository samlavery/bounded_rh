"""E44c: part (b) of the E44 pre-registration (quantity, ranges, decision rule unchanged), re-implemented for speed: analytic
gradient AND Hessian of E_end in the box-free variables u (y = 0.8 + 4.2 sin^2 u), saddle-free damped Newton after L-BFGS;
starts: the previous L's optimum (extended by its y_inf) plus 4 ramp ansatz starts.  PD Hessian required at stop."""
import sys, json, time, numpy as np
exec(open('e44_endterm.py').read().rsplit("if __name__ == '__main__':", 1)[0])
a = float(sys.argv[1]); Ls = [int(x) for x in sys.argv[2].split(',')]; Ymax = 5.0; prev = None
for L in Ls:
    t0 = time.time(); ET = EndTerm(a, L); al = ET.al; k = 2 * np.pi * al; wq = ET.wq; z = ET.z
    M = np.concatenate([(1 - z)[:, None] * ET.Zp[:, :L], ET.Zp[:, L:L + 1]], 1)        # A = sum_j M_j c_j, j = 0..L (L = inf)
    def fgh(u, need=True):
        y = 0.8 + (Ymax - 0.8) * np.sin(u) ** 2; yp = (Ymax - 0.8) * np.sin(2 * u); ypp = 2 * (Ymax - 0.8) * np.cos(2 * u)
        ch = 2 * np.cosh(np.outer(k, y)); sh = 2 * np.sinh(np.outer(k, y))
        A = (M * ch).sum(1)
        # stable |A|^2 - 4: use the E44 X-form
        cinf = ch[:, L]; cc = ch; D = np.concatenate([cc[:, :1], np.diff(cc, axis=1)], 1)
        X = (D[:, 1:] * (ET.Zp[:, 1:L + 1] - 1)).sum(1)
        F = (cinf ** 2 - 4) + 2 * cinf * np.real(X) + np.abs(X) ** 2; f = float(wq @ F)
        if not need: return f, None, None
        Jy = M * (k[:, None] * sh)                                   # dA/dy_j
        gy = 2 * np.real((wq * np.conj(A)) @ Jy)
        Hy = 2 * np.real(np.conj(Jy).T @ (wq[:, None] * Jy)) + np.diag(2 * np.real((wq * np.conj(A)) @ (M * (k[:, None] ** 2 * ch))))
        g = gy * yp; H = Hy * np.outer(yp, yp) + np.diag(gy * ypp)
        return f, g, H
    def inv(y): return np.arcsin(np.sqrt(np.clip((np.asarray(y, float) - 0.8) / (Ymax - 0.8), 1e-12, 1 - 1e-12)))
    starts = []
    if prev is not None:
        yp_, yi_ = prev; ext = np.concatenate([yp_, np.full(max(L - len(yp_), 0), yi_)])[:L]; starts.append(np.concatenate([ext, [yi_]]))
    for yi in (1.5, 2.2, 3.0, 4.0):
        t = np.arange(L) / (0.4 * L); y0 = 0.8 + (yi - 0.8) * (1 - np.exp(-t)); starts.append(np.concatenate([y0, [yi]]))
    best = (np.inf, None)
    for y0 in starts:
        r = minimize(lambda u: fgh(u)[:2], inv(y0), jac=True, method='L-BFGS-B', options={'maxiter': 2000, 'gtol': 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
    u = best[1]; f, g, H = fgh(u)
    for it in range(400):
        lam, V = np.linalg.eigh(H)
        if np.linalg.norm(g) <= 1e-9 * max(1.0, abs(f)) and lam[0] > 0: break
        step = -V @ ((V.T @ g) / np.maximum(np.abs(lam), 1e-10 * np.abs(lam).max() + 1e-12)); t = 1.0
        while t > 1e-14 and fgh(u + t * step, False)[0] > f - 1e-6 * t * abs(g @ step): t *= 0.5
        if t <= 1e-14: break
        u = u + t * step; f, g, H = fgh(u)
    lam = np.linalg.eigvalsh(H); y = 0.8 + (Ymax - 0.8) * np.sin(u) ** 2; prev = (y[:L], y[L])
    print('(b) a=%.2f L=%3d: min E_end %+.6f | ||grad|| %.2e | min Hess eig %+.3e (%s) | y_inf %.4f | end depth %.3f | layer max %.3f | Newton its %d | %.0fs'
          % (a, L, f, np.linalg.norm(g), lam[0], 'PD' if lam[0] > 0 else 'NOT PD', y[L], y[0], y[:L].max(), it, time.time() - t0), flush=True)
    json.dump({'a': a, 'L': L, 'E_end': f, 'y': y[:L].tolist(), 'yinf': float(y[L])}, open('e44c_end_a%.2f_L%d.json' % (a, L), 'w'))
