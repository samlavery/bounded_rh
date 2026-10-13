"""E43 (lead, 2026-10-09; LAST round on the near-density-1 deep-chain family).  Fixed BEFORE any run.
QUANTITY: pair-pair (1') = Q_pp + T_g^pp = ||S_A||_q^2 - 4||V||_q^2 + T_g^pp on EXACT lattice positions s_p = a p,
  S_A(al) = sum_p 2cosh(2 pi al y_p) e(al a p).
EVALUATOR (scalable, exact up to quadrature):
  4||V||^2 = 4 sum_{|k|<P} (P-|k|) K(a k), K(u) = G(u) G(-u) in CLOSED FORM, G(z) = int_{-1/2}^{1/2} v(t) e(t z) dt for the R8
    window v = (1/A)(cos(w0 t) + sum c_j cos(2 pi j t));  T_g^pp = 8 sum_{k=1}^{P-1} (P-k) g(a k)  (both O(P));
  ||S_A||^2 = 2 int_0^1 q |S_A|^2 by Gauss-Legendre on [0,1] with n_gl = max(4000, 3 a P + 2000) nodes (q analytic on [0,1],
    S_A entire), O(P n_gl), chunked; gradient in y the same way.  Validation: the dense code at P = 256 (e42c profile), and a
    node-doubling check at the largest P.
DEPTHS: ansatz y_p = 0.8 + (Y - 0.8) psi(d_p / L), d_p = min(p, P-1-p), psi(x) = (1 - exp(-x^b)) (1 + c exp(-x)), params (Y, L, b, c)
  (Y in [0.8, 3] enforced by clipping); Nelder-Mead from seeds fitted to the e42c P = 256 profiles; then free local refinement of
  all y_p (L-BFGS-B, bounds [0.8, 3], maxiter 300).  a in {0.9, 0.95, 0.99}, P in {256, 512, 1024, 2048, 4096, 8192}.
Every evaluated configuration is an UPPER bound on the family minimum.
REFUTES: any configuration with (1') < 0, confirmed in mpmath at 50 digits (exact K double sum for P <= 512; otherwise the GL sum
  in mpmath on the same nodes) plus the dense code at the largest P it reaches.  SUPPORTS-TREND: per a, the minimum over P of
  the best (1') is attained at a finite P with a positive value and rises after it.  Otherwise undecided.
PREDICTION (bridge-port): a = 0.9 and 0.95: SUPPORTS-TREND, minimum positive at P <= 1024 (bulk tau = 0.30, 0.091 pays early).
  a = 0.99: (1') positive at every P, decreasing through P ~ 2048-4096 and turning up by 8192 (minimum ~150-400) -> SUPPORTS-TREND,
  with UNDECIDED the main alternative if the turn lies beyond 8192."""
import sys, json, math, time, numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum, S2
from common import g_of
cw = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24); qfun = make_qf(cw)
z_ = np.concatenate([[1.0], cw]); w_ = np.concatenate([[S2], 2 * np.pi * np.arange(1, len(z_))]); A_ = 2 * math.sin(S2 / 2) / S2
def Sfun(x):
    x = np.asarray(x, complex); out = np.ones_like(x); m = np.abs(x) > 1e-12; out[m] = 2 * np.sin(x[m] / 2) / x[m]; return out
def G(zz):
    b = 2 * np.pi * np.asarray(zz, complex); out = np.zeros_like(b)
    for zi, wi in zip(z_, w_): out += zi * 0.5 * (Sfun(b + wi) + Sfun(b - wi))
    return out / A_
def Kexact(u): return np.real(G(u) * G(-np.asarray(u, complex)))
class Chain:
    def __init__(self, a, P):
        self.a, self.P = a, P; k = np.arange(1, P)
        self.V4 = 4 * (P * float(Kexact(np.array([0.0]))[0]) + 2 * float(((P - k) * Kexact(a * k)).sum()))
        self.Tg = 8 * float(((P - k) * g_of(a * k)).sum())
        n = max(4000, int(3 * a * P) + 2000); x, wgl = leggauss(n); self.al = 0.5 * (x + 1); self.wq = 2 * 0.5 * wgl * qfun(np.minimum(self.al, 0.9999999))
        self.p = np.arange(P)
    def SA2(self, y, grad=False, chunk=600):
        tot = 0.0; g = np.zeros(self.P) if grad else None
        for i in range(0, len(self.al), chunk):
            al = self.al[i:i + chunk]; wq = self.wq[i:i + chunk]
            arg = 2 * np.pi * np.outer(al, y); E = np.exp(2j * np.pi * np.outer(al, self.a * self.p))
            C = 2 * np.cosh(arg); S = (C * E).sum(1); tot += float(wq @ np.abs(S) ** 2)
            if grad: g += 2 * np.real((wq * np.conj(S)) @ ((2 * np.pi * al)[:, None] * 2 * np.sinh(arg) * E))
        return tot, g
    def onep(self, y, grad=False):
        s2, g = self.SA2(y, grad); return s2 - self.V4 + self.Tg, g
def ansatz(par, P):
    Y, L, b, c = par; Y = min(max(Y, 0.8), 3.0); L = max(L, 0.5); b = min(max(b, 0.2), 6.0)
    d = np.minimum(np.arange(P), P - 1 - np.arange(P)) / L
    psi = (1 - np.exp(-d ** b)) * (1 + c * np.exp(-d)); return np.clip(0.8 + (Y - 0.8) * psi, 0.8, 3.0)
def fit_seed(yprof):
    P = len(yprof); best = (np.inf, None)
    for L in (5, 10, 20, 40, 80):
        for b in (0.7, 1.0, 1.5, 2.0):
            par = [yprof[P // 2], L, b, 0.0]; e = float(((ansatz(par, P) - yprof) ** 2).sum())
            if e < best[0]: best = (e, par)
    r = minimize(lambda pr: float(((ansatz(pr, P) - yprof) ** 2).sum()), best[1], method='Nelder-Mead', options={'maxiter': 2000})
    return list(r.x)
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'validate':
        y = np.array(json.load(open('e42c_pp_a0.99_P256.json'))['y']); ch = Chain(0.99, 256)
        print('VALIDATE a=0.99 P=256 (e42c profile): (1\') = %.6f, Q_pp = %.6f, T_g = %.6f  [dense e42c: Q_pp 946.731018, T_g 4.4566]'
              % (ch.onep(y)[0], ch.onep(y)[0] - ch.Tg, ch.Tg), flush=True)
        # exact double-sum check at small P
        P = 48; yy = 0.8 + 0.6 * np.sin(np.pi * np.arange(P) / (P - 1)); ch = Chain(0.99, P); a = 0.99
        pp = np.arange(P); tot = 0.0
        for s1 in (1, -1):
            for s2 in (1, -1):
                zz = a * (pp[:, None] - pp[None, :]) - 1j * (s1 * yy[:, None] + s2 * yy[None, :])
                tot += float(np.real((G(zz) * G(-zz)).sum()))
        print('EXACT double-sum ||S_A||^2 at P=48: %.10f vs GL %.10f' % (tot, ch.SA2(yy)[0]), flush=True)
        sys.exit()
    a = float(mode); seed = json.load(open('e42c_pp_a%.2f_P256.json' % a))['y']; par = fit_seed(np.array(seed))
    rows = []
    for P in [int(x) for x in sys.argv[2].split(',')]:
        t0 = time.time(); ch = Chain(a, P)
        f = lambda pr: ch.onep(ansatz(pr, P))[0]
        cands = [par, [par[0], par[1] * (P / 256) ** 0.5, par[2], par[3]], [min(par[0] + 0.3, 3.0), par[1] * (P / 256) ** 0.5, par[2], 0.0]]
        best = (np.inf, None)
        for c0 in cands:
            r = minimize(f, c0, method='Nelder-Mead', options={'maxiter': 300 if P <= 2048 else 150, 'xatol': 1e-4, 'fatol': 1e-6})
            if r.fun < best[0]: best = (r.fun, list(r.x))
        par = best[1]; y0 = ansatz(par, P)
        rr = minimize(lambda y: ch.onep(y, True), y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 300 if P <= 2048 else 120})
        y = rr.x; val = rr.fun
        print('a=%.2f P=%5d: (1\') ansatz %+12.4f (Y=%.3f L=%.2f b=%.2f c=%.3f) | refined %+12.4f | Q_pp %+12.4f T_g %9.4f | depths ends %.3f mid %.3f max %.3f | n_gl %d | %.0fs'
              % (a, P, best[0], par[0], par[1], par[2], par[3], val, val - ch.Tg, ch.Tg, y[0], y[P // 2], y.max(), len(ch.al), time.time() - t0), flush=True)
        rows.append({'P': P, 'ansatz': best[0], 'refined': float(val), 'par': par, 'Tg': ch.Tg})
        json.dump({'a': a, 'rows': rows, 'last_y': y.tolist()}, open('e43_a%.2f.json' % a, 'w'))
