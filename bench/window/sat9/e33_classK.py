"""E33 = core push ROUND 3 part (1) (lead, 2026-10-09): depth-CLASS-resolved reduction D_K.  Fixed BEFORE any run.
Classes: [0.8, 3] split into K equal-width classes C_1..C_K (K in {2, 4, 8}); class centres yhat_j; each pair p carries a label
kappa(p).  W may depend on positions AND labels:  W = V + U,  U = sum_{n,j} w_{n,j} phi_j(al) e(al t_n),
  t_n = chain sites + 4 virtual sites per end at the mean gap;  phi_0 = 1, phi_j = B_{yhat_j}/||B_{yhat_j}||_q (j = 1..K).
Exact dual: Q_pp >= 4Re<S_B,W> - 4||W - V||^2 = sum_p 4<B_{y_p}, Re(conj(W) e_p)> - 4||U||^2; the one-body min over y_p runs
only over the pair's own class.  D_K(s, labels) = max_w [T_g + sum_p min_{y in C_kappa(p)} 4<B_y, Re(conj W e_p)> - 4 w^T G w].
  D_K -> truth as K grows (phi family contains the class profiles at the pair sites, so W = S_A/2 is approximated).
Computation: convex QP (cvxpy/Clarabel), depth nodes of step 0.02 in the QP (QP optimum >= D_K) and hard evaluation of the
  maximiser on a step-0.005 grid (<= D_K): two-sided certificate, as in e32d.
LABELLINGS: (L0) the labels of the true min-profile depths at these positions; (L1) a greedy single-label local search from L0
  that lowers D_K (each move = one pair to another class; one full sweep, stop when no move lowers D_K by > 1e-6).
  A certified negative value for ANY labelling is a certified FAIL of the K-reduction for that configuration.  A PASS here
  covers the labellings tested only (L0 and the local-search minimum), not all K^P labellings; stated before the run.
Configurations: lattice a = 0.9 (P = 12, 48); e23 minimisers P = 12, 16, 24, 32.  K in {2, 4, 8}.
PREDICTION (bridge-port): lattice a = 0.9 P = 12 (round-2 deficit -0.16) PASSES already at K = 2.  The irregular e23 minimisers
  improve with K but stay NEGATIVE at K = 8 for P >= 16 (their cancellation uses specific depths finer than 2.2/8 = 0.275);
  the loss (truth - D_K) falls by a factor ~3-10 from K = 2 to K = 8."""
import sys, json, time, numpy as np, cvxpy as cp
from common import *
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def Kq(u, prof=None):
    u = np.asarray(u, float); w = W2 if prof is None else W2 * prof
    return (np.cos(2 * np.pi * np.outer(u.ravel(), al)) @ w).reshape(u.shape)
def Bof(y): return 2 * np.cosh(2 * np.pi * al * y) - 2
class Setup:
    def __init__(self, s, K, step):
        s = np.sort(np.asarray(s, float)); self.s = s; P = len(s); self.P = P; a = (s[-1] - s[0]) / (P - 1)
        self.t = np.unique(np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9))
        n = len(self.t); self.K = K
        edges = np.linspace(0.8, 3.0, K + 1); self.edges = edges; yhat = 0.5 * (edges[:-1] + edges[1:])
        phis = [np.ones_like(al)] + [Bof(y) / np.sqrt(W2 @ Bof(y) ** 2) for y in yhat]; self.J = len(phis)
        self.Y = np.round(np.arange(0.8, 3.0 + 1e-9, step), 4); BY = np.array([Bof(y) for y in self.Y])   # (Ny, nA)
        cs = np.cos(2 * np.pi * np.outer((s[:, None] - s[None, :]).ravel(), al))                    # (P*P, nA)
        self.base = 4 * ((W2 * BY) @ cs.T).reshape(len(self.Y), P, P).sum(2)                      # (Ny, P)
        ct = np.cos(2 * np.pi * np.outer((s[:, None] - self.t[None, :]).ravel(), al))            # (P*n, nA)
        self.M = np.stack([4 * ((W2 * BY * ph) @ ct.T).reshape(len(self.Y), P, n) for ph in phis], -1).reshape(len(self.Y), P, n * self.J)
        cg = np.cos(2 * np.pi * np.outer((self.t[:, None] - self.t[None, :]).ravel(), al))
        G = np.zeros((n * self.J, n * self.J))
        for j in range(self.J):
            for i in range(j, self.J):
                blk = (cg @ (W2 * phis[j] * phis[i])).reshape(n, n)
                G[j::self.J, i::self.J] = blk; G[i::self.J, j::self.J] = blk.T
        self.G = 0.5 * (G + G.T); self.T = Tg(s)
    def classmask(self, labels):
        lo = self.edges[labels]; hi = self.edges[labels + 1]
        return (self.Y[:, None] >= lo[None, :] - 1e-9) & (self.Y[:, None] <= hi[None, :] + 1e-9)    # (Ny, P)
def solveQP(Sc, labels):
    mask = Sc.classmask(labels); P = Sc.P; nv = Sc.M.shape[2]
    ev, Vv = np.linalg.eigh(Sc.G); keep = ev > 1e-11 * ev.max(); Vk = Vv[:, keep]; ek = ev[keep]   # w = Vk z (range of G)
    z = cp.Variable(Vk.shape[1]); tau = cp.Variable(P); cons = []
    for p in range(P):
        rows = np.nonzero(mask[:, p])[0]
        A = Sc.M[rows, p, :] @ Vk; b = Sc.base[rows, p]; sc = np.maximum(1.0, np.maximum(np.abs(b), np.abs(A).max(1)))
        cons.append(tau[p] / sc <= (b + A @ z) / sc)
    prob = cp.Problem(cp.Maximize(Sc.T + cp.sum(tau) - 4 * cp.sum_squares(cp.multiply(np.sqrt(ek), z))), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value, Vk @ np.asarray(z.value).ravel()
def hardval(Sf, labels, w):
    mask = Sf.classmask(labels); ob = Sf.base + np.einsum('ypv,v->yp', Sf.M, w); ob = np.where(mask, ob, np.inf)
    return Sf.T + ob.min(0).sum() - 4 * w @ Sf.G @ w
def truth_profile(s):
    from scipy.optimize import minimize
    s = np.sort(np.asarray(s, float)); P = len(s); E = np.exp(2j * np.pi * np.outer(al, s)); T = Tg(s)
    def f(y):
        C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); Dd = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
        F = (C * E).sum(1); Gs = E.sum(1)
        return float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(Gs) ** 2)), W2 @ (2 * np.real(np.conj(F)[:, None] * Dd * E))
    best = (np.inf, None); rng = np.random.default_rng(3)
    for t in range(6):
        y0 = np.full(P, 0.8) if t == 0 else (0.8 + 0.8 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8 if t == 1 else rng.uniform(0.8, 2.0, P))
        r = minimize(f, np.clip(np.nan_to_num(y0, nan=0.8), 0.8, 3), jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': 3000})
        if r.fun < best[0]: best = (r.fun, r.x)
    return best[0] + T, best[1]
if __name__ == '__main__':
    cfgs = [('lattice a=0.90 P=12', 0.9 * np.arange(12)), ('lattice a=0.90 P=48', 0.9 * np.arange(48))]
    for P in (12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
    only = sys.argv[1:]  # optional subset of names
    out = {}
    for name, s in cfgs:
        if only and not any(o in name for o in only): continue
        tr, yt = truth_profile(s)
        for K in (2, 4, 8):
            t0 = time.time()
            Sc = Setup(s, K, 0.02); Sf = Setup(s, K, 0.005)
            lab0 = np.clip(np.searchsorted(Sc.edges, np.sort(yt) if False else yt[np.argsort(np.argsort(np.sort(s)))] , side='right') - 1, 0, K - 1)
            lab0 = np.clip(np.searchsorted(Sc.edges, yt, side='right') - 1, 0, K - 1)
            opt, w = solveQP(Sc, lab0); hv = hardval(Sf, lab0, w)
            best = (opt, hv, lab0.copy())
            # one greedy sweep of single-label moves
            labs = lab0.copy()
            for p in range(len(s)):
                for k in range(K):
                    if k == labs[p]: continue
                    trial = labs.copy(); trial[p] = k
                    o2, w2 = solveQP(Sc, trial)
                    if o2 < best[0] - 1e-6:
                        best = (o2, hardval(Sf, trial, w2), trial.copy()); labs = trial
            o, h, lb = best
            tag = 'PASS(labellings tested)' if (h >= 0 and hv >= 0) else ('FAIL certified' if o < 0 or opt < 0 else 'UNDECIDED')
            print('%-22s K=%d truth %+9.3f | L0: QP %+10.3f hard %+10.3f | local-search min: QP %+10.3f hard %+10.3f | loss(min) %9.3f | %s | %.0fs'
                  % (name, K, tr, opt, hv, o, h, tr - o, tag, time.time() - t0), flush=True)
            out['%s K=%d' % (name, K)] = {'truth': tr, 'L0_qp': opt, 'L0_hard': hv, 'min_qp': o, 'min_hard': h, 'labels_min': lb.tolist()}
    json.dump(out, open('e33_results.json', 'w'))
