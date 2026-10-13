"""E32 = core push ROUND 2 (lead, 2026-10-09): depth-free reduction by a dual test function.  Fixed BEFORE any run.
EXACT: Q_pp = ||S_B||^2 + 4Re<S_B,V> >= 4Re<S_B,W> - 4||W-V||^2 for any W (equality at W = S_A/2), all inner products
two-sided in L^2(q).  With W depending on positions only, 4Re<S_B,W> = sum_p 4<B_{y_p}, g_p>_q, g_p = Re(conj(W) e(al s_p)), so
  (1') <= D(s) := max_W [ T_g^pp + sum_p min_{y in [0.8,3]} 4<B_y, g_p>_q - 4||W - V||^2 ]   (positions only).
COMPUTATION (exact reformulation, Sion; the summand is linear in B_y, so min over y = min over mixtures B-bar_p in conv{B_y}):
  D(s) = T_g + min_{mixtures} [ 4 sum_{p,p'} L_{Bbar_p}(s_p - s_p') + b^T G^+ b ],  b_n = sum_p L_{Bbar_p}(s_p - t_n),
  G_nm = K(t_n - t_m), L_B(u) = int q B cos(2 pi al u)  (all real; real w_n suffice by symmetry).  Mixtures over the depth grid
  y_k = 0.8, 0.9, ..., 3.0 (23 nodes); convex QP over simplices (projected gradient, then FISTA).  The maximising W is then
  rebuilt as W* = V + P_F S_Bbar*/2 and the max-min value T_g + sum_p min_y 4<B_y,g_p> - 4||W*-V||^2 is evaluated directly
  (rigorous direction; equals D at the saddle point).
FAMILY F (primary, as specified): t_n = the chain's own positions (deduplicated) + 4 virtual sites per end at the mean gap.
DIAGNOSTIC (declared now): F = all of L^2(q) -> 'conv' = min over mixtures of T_g + 4Re<S_Bbar,V> + ||S_Bbar||^2, the best any W
  can do; decoupling loss = truth - D = (truth - conv) [convexification] + (conv - D) [projection onto F].
TRUTH: min over depth profiles y_p in [0.8, 3] of Q_pp + T_g at the same positions (L-BFGS, several starts).
CONFIGS: exact lattices a in {0.6, 0.7, 0.76, 0.8, 0.9} x P in {6, 12, 24, 48}; the e23 minimisers P = 6, 8, 12, 16, 24, 32.
PASS: D >= 0 on all of them.
PREDICTION (bridge-port): FAIL.  A positions-only W is a constant-coefficient exponential sum; S_B has coefficients B_y(al) that
  grow like e^{2 pi al y}, so ||P_F S_B||^2 recovers only part of ||S_B||^2 at the band edge, while the min over y drives end
  pairs to y = 3 where the one-body end potentials are ~ -1e5.  Expected loss dominated by projection, not convexification."""
import json, numpy as np
from scipy.optimize import minimize
from common import *
YK = np.round(np.arange(0.8, 3.0001, 0.1), 3); BK = np.array([2 * np.cosh(2 * np.pi * al * y) - 2 for y in YK])   # (K, nA)
def Lmat(u):  # L_k(u) for array u: returns (K, *u.shape)
    u = np.asarray(u, float); cu = np.cos(2 * np.pi * np.outer(u.ravel(), al))   # (n, nA)
    return ((W2 * BK) @ cu.T).reshape((len(YK),) + u.shape)
def Kmat(u):
    u = np.asarray(u, float); return (np.cos(2 * np.pi * np.outer(u.ravel(), al)) @ W2).reshape(u.shape)
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def proj_simplex(v):
    u = np.sort(v)[::-1]; css = np.cumsum(u); rho = np.nonzero(u * np.arange(1, len(v) + 1) > (css - 1))[0][-1]
    th = (css[rho] - 1) / (rho + 1.0); return np.maximum(v - th, 0)
def D_of(s, family='F'):
    s = np.sort(np.asarray(s, float)); P = len(s); a = (s[-1] - s[0]) / (P - 1)
    N = Lmat(s[:, None] - s[None, :])                               # (K, P, P)
    lin = 4 * N.sum(2)                                               # (K, P): coefficient of lambda_pk in 4 sum L(s_p - s_p')
    if family == 'F':
        t = np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)])
        t = np.unique(np.round(t, 9))
        M = Lmat(s[:, None] - t[None, :])                           # (K, P, n)
        G = Kmat(t[:, None] - t[None, :]); Gi = np.linalg.pinv(G, rcond=1e-12)
        def quad(lam):  # b = sum_pk lam_pk M_k[p,:]
            b = np.einsum('pk,kpn->n', lam, M); return b @ Gi @ b, 2 * np.einsum('kpn,n->pk', M, Gi @ b)
    else:
        E = np.exp(2j * np.pi * np.outer(al, s))
        def quad(lam):
            Bb = lam @ BK                                                # (P, nA)
            S = (Bb.T * E).sum(1); val = float(W2 @ np.abs(S) ** 2)
            gr = 2 * np.real(np.einsum('a,ka,ap->pk', W2 * np.conj(S), BK, E))
            return val, gr
    def obj(lam):
        q_, gq = quad(lam); return float((lam * lin.T).sum()) + q_, lin.T + gq
    K = len(YK); lam = np.zeros((P, K)); lam[:, 0] = 1.0                 # start at y = 0.8
    # Frank-Wolfe with exact line search (objective = linear + homogeneous convex quadratic); certified gap
    f, g = obj(lam); gap = np.inf
    for it in range(6000):
        kstar = np.argmin(g, 1); Svert = np.zeros_like(lam); Svert[np.arange(P), kstar] = 1.0
        d = Svert - lam; gd = float((g * d).sum()); gap = -gd
        if gap <= 1e-9 * max(1.0, abs(f)): break
        qd = quad(d)[0]
        gam = 1.0 if qd <= 0 else min(1.0, gap / (2 * qd))
        lam = lam + gam * d; f, g = obj(lam)
    f_lower = f - gap                                                   # certified: min f >= f - gap
    val = (Tg(s) + f, Tg(s) + f_lower)
    # rigorous max-min check: W* = V + P_F S_Bbar/2, evaluate T_g + sum_p min_y 4<B_y,g_p> - 4||W*-V||^2
    if family == 'F':
        b = np.einsum('pk,kpn->n', lam, M); w = Gi @ b / 2                 # U = W* - V = sum w_n e(al t_n)
        # 4<B_y, g_p> with W = V + U:  g_p-term = 4 sum_{p'} L_y(s_p - s_p') + 4 sum_n w_n L_y(s_p - t_n)
        onebody = 4 * N.sum(2) + 4 * np.einsum('kpn,n->kp', M, w)       # (K, P)
        mm = onebody.min(0).sum() - 4 * float(w @ G @ w)
        return val, Tg(s) + mm, lam
    return val, None, lam
def truth_min(s):
    s = np.sort(np.asarray(s, float)); P = len(s); E = np.exp(2j * np.pi * np.outer(al, s)); T = Tg(s)
    def f(y):
        C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
        F = (C * E).sum(1); Gs = E.sum(1)
        return float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(Gs) ** 2)), W2 @ (2 * np.real(np.conj(F)[:, None] * D * E))
    best = np.inf; rng = np.random.default_rng(3)
    for t in range(6):
        y0 = np.full(P, 0.8) if t == 0 else (0.8 + 0.8 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8 if t == 1 else rng.uniform(0.8, 2.0, P))
        r = minimize(f, y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 3000}); best = min(best, r.fun)
    return best + T
if __name__ == '__main__':
    cfgs = []
    for a in (0.6, 0.7, 0.76, 0.8, 0.9):
        for P in (6, 12, 24, 48): cfgs.append(('lattice a=%.2f P=%d' % (a, P), a * np.arange(P)))
    for P in (6, 8, 12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
    allpass = True
    for name, s in cfgs:
        (DF, DFl), Dmm, lam = D_of(s, 'F'); (conv, convl), _, _ = D_of(s, 'full'); tr = truth_min(s)
        ymix = (lam * YK[None, :]).sum(1)
        verdict = 'PASS' if max(Dmm, DFl) >= 0 else ('FAIL' if DF < 0 else 'UNDECIDED')
        allpass &= verdict == 'PASS'
        print('%-24s truth %+10.3f | conv (any W) %+10.3f [lower %+.3f] | D (F) %+10.3f [certified lower %+.3f; max-min W* %+.3f] | loss: convexify %.3f, projection %.3f | %s | mixture depth ends %.2f/%.2f mid %.2f'
              % (name, tr, conv, convl, DF, DFl, Dmm, tr - conv, conv - DF, verdict, ymix[0], ymix[-1], ymix[len(ymix) // 2]), flush=True)
    print('VERDICT: %s' % ('PASS' if allpass else 'FAIL'))
