"""E36 (Sam: 'run the cheap refuting test first'; am-cert's named experiment): W TRANSPLANT at larger radius, regime A only.
Fixed BEFORE any run:
  For a in {0.6, 0.7, 0.76, 0.8}: optimal positions-only witnesses w* at P = 64 and P = 128 (e32d QP: t = sites + 4 virtual
  sites per end at spacing a; depth nodes step 0.02 in the QP; two-sided certificate: QP optimum >= D >= hard value on the
  step-0.005 depth grid).  Transplant: w(128) := w*(64) on the first r and last r entries of t (r counts from the outermost
  virtual site), interior := median of w*(64) over its central half; r in {16, 20, 24}.  Certified hard D of each transplant
  (fine grid; valid lower bound for (1') on that lattice up to the depth grid).
  PASS: hard D >= 0 at some r <= 24 for ALL four spacings.  FAIL otherwise; report loss vs r.
PREDICTION (bridge-port, before the run): the e35 losses fell ~25x from r = 8 to r = 12 (~0.8 per site in the exponent), and the
  optimum at P = 128 is ~T_g ~ 120-340.  Extrapolating, r = 16 loses ~ 1e2-5e2 and r = 20 ~ 5-20, so PASS at r <= 20 for
  a = 0.6, 0.7, 0.76; a = 0.8 (interior spread 5x larger at P = 48) is the risk, predicted PASS at r = 24.  If the interior of
  w*(128) is not flat to ~1e-6 relative to w*(64)'s median, the transplant fails regardless of r (stiffness ~1e6-1e7)."""
import json, time, numpy as np, cvxpy as cp
from common import *
YC = np.round(np.arange(0.8, 3.00001, 0.02), 4); YF = np.round(np.arange(0.8, 3.00001, 0.005), 4)
BC = np.array([2 * np.cosh(2 * np.pi * al * y) - 2 for y in YC]); BF = np.array([2 * np.cosh(2 * np.pi * al * y) - 2 for y in YF])
def Lfun(BY, u, chunk=1500):
    u = np.asarray(u, float).ravel(); out = np.empty((BY.shape[0], len(u))); WB = W2 * BY
    for i in range(0, len(u), chunk):
        out[:, i:i + chunk] = WB @ np.cos(2 * np.pi * np.outer(al, u[i:i + chunk]))
    return out
def Kfun(u, chunk=1500):
    u = np.asarray(u, float).ravel(); out = np.empty(len(u))
    for i in range(0, len(u), chunk): out[i:i + chunk] = W2 @ np.cos(2 * np.pi * np.outer(al, u[i:i + chunk]))
    return out
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def setup(a, P, BY):
    s = a * np.arange(P); t = np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9); n = len(t)
    base = 4 * Lfun(BY, (s[:, None] - s[None, :])).reshape(BY.shape[0], P, P).sum(2)
    M = 4 * Lfun(BY, (s[:, None] - t[None, :])).reshape(BY.shape[0], P, n)
    G = Kfun(t[:, None] - t[None, :]).reshape(n, n)
    return s, t, base, M, G, Tg(s)
def qp(a, P):
    s, t, base, M, G, T = setup(a, P, BC)
    ev, V_ = np.linalg.eigh(G); keep = ev > 1e-12 * ev.max(); Vk = V_[:, keep]; ek = ev[keep]
    z = cp.Variable(Vk.shape[1]); tau = cp.Variable(P); cons = []
    for k in range(len(YC)):
        A = M[k] @ Vk; sc = np.maximum(1.0, np.maximum(np.abs(base[k]), np.abs(A).max(1)))
        cons.append(cp.multiply(1 / sc, tau) <= cp.multiply(1 / sc, base[k] + A @ z))
    prob = cp.Problem(cp.Maximize(T + cp.sum(tau) - 4 * cp.sum_squares(cp.multiply(np.sqrt(ek), z))), cons); prob.solve(solver=cp.CLARABEL)
    return prob.value, Vk @ np.asarray(z.value).ravel()
def hard(a, P, w, cache={}):
    if (a, P) not in cache: cache[(a, P)] = setup(a, P, BF)
    s, t, base, M, G, T = cache[(a, P)]
    ob = base + np.einsum('kpn,n->kp', M, w); return T + ob.min(0).sum() - 4 * w @ G @ w
if __name__ == '__main__':
    res = {}; allpass = True
    for a in (0.6, 0.7, 0.76, 0.8):
        t0 = time.time()
        o64, w64 = qp(a, 64); h64 = hard(a, 64, w64)
        o128, w128 = qp(a, 128); h128 = hard(a, 128, w128)
        n64, n128 = len(w64), len(w128); c64 = w64[n64 // 4: 3 * n64 // 4]; fill = float(np.median(c64))
        c128 = w128[n128 // 4: 3 * n128 // 4]
        print('a=%.2f: w*(64) QP %+.3f hard %+.3f | w*(128) QP %+.3f hard %+.3f | interior: w*(64) median %.6f (spread %.2e), w*(128) median %.6f (spread %.2e) | %.0fs'
              % (a, o64, h64, o128, h128, fill, c64.max() - c64.min(), np.median(c128), c128.max() - c128.min(), time.time() - t0), flush=True)
        rowpass = False
        for r in (16, 20, 24):
            w = np.full(n128, fill); w[:r] = w64[:r]; w[-r:] = w64[-r:]
            D = hard(a, 128, w); rowpass |= D >= 0
            print('     r=%2d: transplant hard D %+14.3f (optimum %+.3f, loss %.3f)  %s' % (r, D, h128, h128 - D, 'ok' if D >= 0 else 'neg'), flush=True)
            res['a=%.2f r=%d' % (a, r)] = {'D': float(D), 'opt': float(h128)}
        # diagnostics: transplant with the P=128 optimum's own interior median (isolates end-pattern vs interior error)
        w = np.full(n128, float(np.median(c128))); w[:24] = w64[:24]; w[-24:] = w64[-24:]
        print('     [diag] r=24 with w*(128) interior median: hard D %+.3f' % hard(a, 128, w), flush=True)
        allpass &= rowpass
        json.dump({'a': a, 'w64': w64.tolist(), 'w128': w128.tolist()}, open('e36_w_a%.2f.json' % a, 'w'))
    json.dump(res, open('e36_results.json', 'w'))
    print('VERDICT: %s' % ('PASS' if allpass else 'FAIL'), flush=True)
