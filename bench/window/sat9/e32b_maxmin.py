"""E32b: same pre-registered quantity as E32 (round 2), computed by its PRIMAL max-min form (solver change only; the projected
gradient / Frank-Wolfe dual in e32 did not converge: the curvature spans ~1e16 across depths).
  D(s) = max_{w} [ T_g + sum_p min_{y in [0.8,3]} 4( sum_p' L_y(s_p - s_p') + sum_n w_n L_y(s_p - t_n) ) - 4 w^T G w ],
  U = W - V = sum_n w_n e(al t_n), t_n = own positions (deduplicated) + 4 virtual sites per end at the mean gap; G = K(t_n - t_m).
  The objective is concave in w (min of affine minus PSD quadratic): maximised by L-BFGS on a soft-min with temperature
  continuation, then evaluated with the HARD min over a fine depth grid (step 0.005), which is the reported D (any w gives a valid
  lower bound up to the grid; the fine grid makes it conservative relative to the e32 grid).
Truth = min over depth profiles of Q_pp + T_g at the same positions (as e32).  PASS = D >= 0 on every configuration."""
import json, numpy as np
from scipy.optimize import minimize
from common import *
YK = np.round(np.arange(0.8, 3.00001, 0.005), 4); BK = np.array([2 * np.cosh(2 * np.pi * al * y) - 2 for y in YK])
def Lmat(u):
    u = np.asarray(u, float); cu = np.cos(2 * np.pi * np.outer(u.ravel(), al))
    return ((W2 * BK) @ cu.T).reshape((len(YK),) + u.shape)
def Kmat(u):
    u = np.asarray(u, float); return (np.cos(2 * np.pi * np.outer(u.ravel(), al)) @ W2).reshape(u.shape)
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def D_of(s):
    s = np.sort(np.asarray(s, float)); P = len(s); a = (s[-1] - s[0]) / (P - 1)
    t = np.unique(np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9))
    base = 4 * Lmat(s[:, None] - s[None, :]).sum(2)              # (K, P)
    M = 4 * Lmat(s[:, None] - t[None, :])                        # (K, P, n)
    G = Kmat(t[:, None] - t[None, :]); T = Tg(s)
    def hard(w):
        ob = base + np.einsum('kpn,n->kp', M, w); k = ob.argmin(0)
        return T + ob.min(0).sum() - 4 * w @ G @ w, YK[k]
    def soft(w, tau):
        ob = base + np.einsum('kpn,n->kp', M, w); m = ob.min(0)
        e = np.exp(-(ob - m) / tau); Z = e.sum(0); sm = m - tau * np.log(Z); pi = e / Z
        val = T + sm.sum() - 4 * w @ G @ w
        grad = np.einsum('kp,kpn->n', pi, M) - 8 * G @ w
        return -val, -grad
    w = np.zeros(len(t)); scale = max(1.0, float(np.abs(base).max()))
    best = (hard(w)[0], w.copy())
    for tau in scale * np.array([1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8]):
        r = minimize(soft, w, args=(tau,), jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        w = r.x; h = hard(w)[0]
        if h > best[0]: best = (h, w.copy())
    D, ystar = hard(best[1])
    return D, ystar, T
def truth_min(s):
    s = np.sort(np.asarray(s, float)); P = len(s); E = np.exp(2j * np.pi * np.outer(al, s)); T = Tg(s)
    def f(y):
        C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); Dd = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
        F = (C * E).sum(1); Gs = E.sum(1)
        return float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(Gs) ** 2)), W2 @ (2 * np.real(np.conj(F)[:, None] * Dd * E))
    best = (np.inf, None); rng = np.random.default_rng(3)
    for t in range(6):
        y0 = np.full(P, 0.8) if t == 0 else (0.8 + 0.8 * np.sin(np.pi * np.arange(P) / max(P - 1, 1)) ** 0.8 if t == 1 else rng.uniform(0.8, 2.0, P))
        r = minimize(f, np.clip(np.nan_to_num(y0, nan=0.8), 0.8, 3), jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 3000})
        if r.fun < best[0]: best = (r.fun, r.x)
    return best[0] + T, best[1]
if __name__ == '__main__':
    cfgs = []
    for a in (0.6, 0.7, 0.76, 0.8, 0.9):
        for P in (6, 12, 24, 48): cfgs.append(('lattice a=%.2f P=%d' % (a, P), a * np.arange(P)))
    for P in (6, 8, 12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
    allpass = True
    for name, s in cfgs:
        D, ystar, T = D_of(s); tr, ytr = truth_min(s)
        allpass &= D >= 0
        n3 = int((ystar >= 2.99).sum())
        print('%-24s truth %+10.3f | D %+12.3f | loss %12.3f | %s | T_g %.2f | adversarial depths at D: ends %.2f/%.2f, #at cap(3) %d of %d | truth profile ends %.2f/%.2f max %.2f'
              % (name, tr, D, tr - D, 'PASS' if D >= 0 else 'FAIL', T, ystar[0], ystar[-1], n3, len(ystar), ytr[0], ytr[-1], ytr.max()), flush=True)
    print('VERDICT: %s' % ('PASS' if allpass else 'FAIL'))
