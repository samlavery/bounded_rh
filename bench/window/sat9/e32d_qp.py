"""E32d: the pre-registered round-2 quantity D(s) computed EXACTLY as a convex QP (cvxpy/Clarabel):
  maximise  T_g + sum_p tau_p - 4 w^T G w   s.t.  tau_p <= base_kp + (M_k w)_p   for all depth nodes k (coarse grid, step 0.02),
rows rescaled by their size.  QP optimum (coarse grid) >= D(fine) >= D_hard(w*) evaluated on the fine grid (step 0.005), so
  QP optimum < 0  => FAIL certified;   D_hard(w*) >= 0 => PASS certified."""
import json, numpy as np, cvxpy as cp
exec(open('e32b_maxmin.py').read().split("if __name__ == '__main__':")[0])
YC = np.round(np.arange(0.8, 3.00001, 0.02), 4); BC = np.array([2 * np.cosh(2 * np.pi * al * y) - 2 for y in YC])
def Lc(u):
    u = np.asarray(u, float); cu = np.cos(2 * np.pi * np.outer(u.ravel(), al)); return ((W2 * BC) @ cu.T).reshape((len(YC),) + u.shape)
def solve(s):
    s = np.sort(np.asarray(s, float)); P = len(s); a = (s[-1] - s[0]) / (P - 1)
    t = np.unique(np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9))
    base = 4 * Lc(s[:, None] - s[None, :]).sum(2); M = 4 * Lc(s[:, None] - t[None, :]); G = Kmat(t[:, None] - t[None, :]); T = Tg(s)
    ev, V_ = np.linalg.eigh(G); keep = ev > 1e-12 * ev.max(); Rh = V_[:, keep] * np.sqrt(ev[keep])   # G = Rh Rh^T on its range
    n = len(t); w = cp.Variable(n); tau = cp.Variable(P)
    cons = []
    for k in range(len(YC)):
        sc = np.maximum(1.0, np.maximum(np.abs(base[k]), np.abs(M[k]).max(1)))
        cons.append(cp.multiply(1 / sc, tau) <= cp.multiply(1 / sc, base[k] + M[k] @ w))
    prob = cp.Problem(cp.Maximize(T + cp.sum(tau) - 4 * cp.sum_squares(Rh.T @ w)), cons)
    try:
        prob.solve(solver=cp.CLARABEL)
    except Exception as e:
        return None, None, str(e)
    ws = np.asarray(w.value).ravel()
    # hard evaluation on the FINE grid (YK from e32b)
    baseF = 4 * Lmat(s[:, None] - s[None, :]).sum(2); MF = 4 * Lmat(s[:, None] - t[None, :])
    ob = baseF + np.einsum('kpn,n->kp', MF, ws)
    Dh = T + ob.min(0).sum() - 4 * ws @ G @ ws
    return prob.value, Dh, YK[ob.argmin(0)]
if __name__ == '__main__':
    cfgs = []
    for a in (0.6, 0.7, 0.76, 0.8, 0.9):
        for P in (6, 12, 24, 48): cfgs.append(('lattice a=%.2f P=%d' % (a, P), a * np.arange(P)))
    for P in (6, 8, 12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
    for name, s in cfgs:
        opt, Dh, ys = solve(s)
        if opt is None: print('%-22s solver error: %s' % (name, ys), flush=True); continue
        tag = 'PASS (certified)' if Dh >= 0 else ('FAIL (certified)' if opt < 0 else 'UNDECIDED')
        print('%-22s QP optimum %+12.4f | D_hard(w*) fine grid %+12.4f | %s | depths at D: ends %.2f/%.2f, #at cap %d/%d'
              % (name, opt, Dh, tag, ys[0], ys[-1], int((ys >= 2.99).sum()), len(ys)), flush=True)
