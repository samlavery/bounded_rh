"""E44 = ANALYTIC END-TERM STUDY, round 1 (lead, 2026-10-09).  Fixed BEFORE any run.
EXACT (Abel): on s_p = p a, z = e(al a), c_p = 2cosh(2 pi al y_p):
  (1-z) S_A = c_0 + sum_{p=1}^{P-1} (c_p - c_{p-1}) z^p - c_{P-1} z^P,  (1-z) 2V = 2(1 - z^P),
  Q_pp = int_{-1}^{1} q/(4 sin^2(pi al a)) [ |c_0 + sum Dc_p z^p - c_{P-1} z^P|^2 - 4|1 - z^P|^2 ] dal.
END TERM: E_end[c] = int q/(4 sin^2(pi a al)) (|A|^2 - 4), A = sum_{p=0}^{L} Dc_p z^p = (1-z) sum_{p<L} c_p z^p + c_inf z^L,
  evaluated stably as |A|^2 - 4 = (c_inf^2 - 4) + 2 c_inf Re X + |X|^2, X = sum_{p>=1} Dc_p (z^p - 1) (each term O(al^2)).
  Prediction of decoupling: Q_pp(P) -> E_end[left] + E_end[right] as P >> 1/(1/a - 1).
(a) Check the Abel form against the direct GL evaluator (e43 Chain) on the converged dense profiles (a = 0.99, P = 64, 128, 256;
    re-converged by Newton here and saved), and the decoupling error Q_pp - (E_L + E_R) with the end layers read from each
    profile (c_inf = the mid value); report the error vs P.
(b) min E_end over end layers: L in {50, 100, 200, 400} sites, y_p in [0.8, 5], y_inf in [0.8, 5], a in {0.9, 0.95, 0.99};
    variables u with y = 0.8 + 4.2 sin^2(u) (box-free); L-BFGS then saddle-free Newton with exact Hessian; PD Hessian required
    at stop.  (E_inf) SUPPORTS: inf E_end >= 0 at every a.  If inf E_end = -C < 0: report C, P_crit = 2C/tau(a), the configuration.
(c) Pencil lower bound on E_end: low band vs near-pole band, which part binds (from the minimisers' integrand split).
PREDICTION (bridge-port): (a) Abel = direct to <= 1e-9 relative; decoupling error decays roughly like (P(1/a - 1))^-2, still
  ~5-15% of Q_pp at a = 0.99, P = 256.  (b) SUPPORTS (~60%): E_end decreases with L and y_inf (minimisers push y_inf to the cap 5),
  but stays positive; smallest at a = 0.9, of order 1-10.  (c) the near-pole band binds."""
import sys, json, time, numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize
exec(open('e43_scalable.py').read().split("if __name__ == '__main__':")[0])
def glw(n, a):
    x, w = leggauss(n); al = 0.5 * (x + 1); wq = 2 * 0.5 * w * qfun(np.minimum(al, 0.9999999)) / (4 * np.sin(np.pi * a * al) ** 2)
    return al, wq
class EndTerm:
    def __init__(self, a, L, n=6000):
        self.a, self.L = a, L; self.al, self.wq = glw(n, a); self.z = np.exp(2j * np.pi * a * self.al)
        self.Zp = self.z[:, None] ** np.arange(L + 1)[None, :]                     # z^p, p = 0..L
    def value(self, y, yinf, grad=False):
        al = self.al; L = self.L; k = 2 * np.pi * al
        c = 2 * np.cosh(np.outer(k, y)); cinf = 2 * np.cosh(k * yinf)              # (n, L), (n,)
        cc = np.concatenate([c, cinf[:, None]], 1)                                 # c_0..c_{L-1}, c_inf at p = L
        D = np.concatenate([cc[:, :1], np.diff(cc, axis=1)], 1)                    # Dc_0..Dc_L
        X = (D[:, 1:] * (self.Zp[:, 1:] - 1)).sum(1)
        F = (cinf ** 2 - 4) + 2 * cinf * np.real(X) + np.abs(X) ** 2               # |A|^2 - 4
        val = float(self.wq @ F)
        if not grad: return val
        A = cinf + X                                                               # = sum D_p z^p
        # dA/dy_p = (1 - z) z^p dc_p/dy (p < L);  dA/dyinf = z^L dc_inf/dy
        dc = 2 * k[:, None] * np.sinh(np.outer(k, y)); dcinf = 2 * k * np.sinh(k * yinf)
        dA = (1 - self.z)[:, None] * self.Zp[:, :L] * dc; dAinf = self.Zp[:, L] * dcinf
        gy = 2 * np.real((self.wq * np.conj(A)) @ dA); gi = 2 * float(np.real((self.wq * np.conj(A)) @ dAinf))
        return val, gy, gi
def chain_Qpp(ch, y): return ch.SA2(y)[0] - ch.V4
def abel_Qpp(a, y, n=12000):
    al, wq = glw(n, a); z = np.exp(2j * np.pi * a * al); P = len(y); k = 2 * np.pi * al
    c = 2 * np.cosh(np.outer(k, y)); D = np.concatenate([c[:, :1], np.diff(c, axis=1)], 1)
    Zp = z[:, None] ** np.arange(P + 1)[None, :]
    N = (D * Zp[:, :P]).sum(1) - c[:, -1] * Zp[:, P]
    return float(wq @ (np.abs(N) ** 2 - 4 * np.abs(1 - Zp[:, P]) ** 2))
if __name__ == '__main__':
    part = sys.argv[1]
    if part == 'a':
        from common import al as alg, W2 as W2g
        a = 0.99
        for P in (64, 128, 256):
            ch = Chain(a, P); s = a * np.arange(P)
            if P == 256: y = np.array(json.load(open('e42c_pp_a0.99_P256.json'))['y'])
            else:
                y0 = 0.8 + 0.6 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8
                r = minimize(lambda yy: ch.onep(yy, True), y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 20000, 'gtol': 1e-10})
                y = r.x
            # polish at the GL evaluator
            r = minimize(lambda yy: ch.onep(yy, True), y, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 5000, 'gtol': 1e-10}); y = r.x
            json.dump({'a': a, 'P': P, 'y': y.tolist()}, open('e44_profile_a0.99_P%d.json' % P, 'w'))
            Qd = chain_Qpp(ch, y); Qa = abel_Qpp(a, y)
            half = P // 2; mid = y[half]
            EL = EndTerm(a, half).value(y[:half], mid); ER = EndTerm(a, half).value(y[::-1][:half], mid)
            print('(a) a=%.2f P=%3d: Q_pp direct %.8f | Abel %.8f (rel diff %.1e) | E_L %.4f E_R %.4f sum %.4f | decoupling error %+.4f (%.2f%% of Q_pp)'
                  % (a, P, Qd, Qa, abs(Qa - Qd) / abs(Qd), EL, ER, EL + ER, Qd - EL - ER, 100 * (Qd - EL - ER) / Qd), flush=True)
    elif part == 'b':
        a = float(sys.argv[2]); Ls = [int(x) for x in sys.argv[3].split(',')]
        rng = np.random.default_rng(1); prev = None
        for L in Ls:
            t0 = time.time(); ET = EndTerm(a, L)
            Ymax = 5.0
            def unpack(u): return 0.8 + (Ymax - 0.8) * np.sin(u[:L]) ** 2, 0.8 + (Ymax - 0.8) * np.sin(u[L]) ** 2
            def fg(u):
                y, yi = unpack(u); v, gy, gi = ET.value(y, yi, True)
                dy = (Ymax - 0.8) * np.sin(2 * u[:L]); di = (Ymax - 0.8) * np.sin(2 * u[L])
                return v, np.concatenate([gy * dy, [gi * di]])
            def inv(y): return np.arcsin(np.sqrt(np.clip((np.asarray(y) - 0.8) / (Ymax - 0.8), 1e-12, 1 - 1e-12)))
            starts = []
            for yi in (1.2, 1.6, 2.0, 2.5, 3.0):
                for Lw in (0.2, 0.5, 1.0):
                    t = np.arange(L) / max(L * Lw, 1); starts.append((0.8 + (yi - 0.8) * (1 - np.exp(-t)), yi))
            if prev is not None:
                yp, yip = prev; ext = np.concatenate([yp, np.full(L - len(yp), yip)]) if L > len(yp) else yp[:L]; starts.append((ext, yip))
            best = (np.inf, None)
            for (y0, yi0) in starts:
                u0 = np.concatenate([inv(y0), inv([yi0])])
                r = minimize(fg, u0, jac=True, method='L-BFGS-B', options={'maxiter': 5000, 'gtol': 1e-12})
                if r.fun < best[0]: best = (r.fun, r.x)
            # saddle-free Newton polish with finite-difference Hessian of the gradient (dimension L+1 <= 401)
            u = best[1]; f, g = fg(u)
            for it in range(200):
                h = 1e-6; H = np.zeros((L + 1, L + 1))
                for j in range(L + 1):
                    e = np.zeros(L + 1); e[j] = h; H[:, j] = (fg(u + e)[1] - fg(u - e)[1]) / (2 * h)
                H = 0.5 * (H + H.T); lam, Vv = np.linalg.eigh(H)
                if np.linalg.norm(g) < 1e-9 * max(1, abs(f)) and lam[0] > 0: break
                step = -Vv @ ((Vv.T @ g) / np.maximum(np.abs(lam), 1e-8 * np.abs(lam).max() + 1e-12)); t = 1.0
                while t > 1e-12 and fg(u + t * step)[0] > f - 1e-6 * t * abs(g @ step): t *= 0.5
                if t <= 1e-12: break
                u = u + t * step; f, g = fg(u)
            lam = np.linalg.eigvalsh(H); y, yi = unpack(u); prev = (y, yi)
            print('(b) a=%.2f L=%3d: min E_end %+.6f | ||grad|| %.2e | min Hess eig %+.3e (%s) | y_inf %.4f | end depth %.3f | layer max %.3f | %.0fs'
                  % (a, L, f, np.linalg.norm(g), lam[0], 'PD' if lam[0] > 0 else 'NOT PD', yi, y[0], y.max(), time.time() - t0), flush=True)
            json.dump({'a': a, 'L': L, 'E_end': f, 'y': y.tolist(), 'yinf': yi}, open('e44_end_a%.2f_L%d.json' % (a, L), 'w'))
