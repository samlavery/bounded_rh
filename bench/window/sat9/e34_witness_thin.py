"""E34: round 3 parts (2) and (3).
(3) Save the round-2 QP optimal witnesses W* = V + sum_n w_n e(al t_n) (positions-only family) for the certified-PASS lattices
    a in {0.6, 0.7, 0.76, 0.8} x P in {6, 12, 24, 48}: e34_witness.json (s, t, w, QP optimum, hard D, argmin depths).
(2) Near-density-1 thinness: for long lattice chains a in {0.85, 0.9, 0.95, 1.0, 1.05}: tau(a) and the true per-pair margin
    under the optimal depth profile, from truth(P) = min over profiles of Q_pp + T_g at P = 24, 48, 96:
    bulk per-pair margin = (truth(96) - truth(48))/48; end term = truth(48) - 48 * bulk."""
import json, numpy as np
exec(open('e32d_qp.py').read().rsplit("if __name__ == '__main__':", 1)[0])
wit = {}
for a in (0.6, 0.7, 0.76, 0.8):
    for P in (6, 12, 24, 48):
        s = a * np.arange(P)
        sP = np.sort(s); aa = (sP[-1] - sP[0]) / (P - 1)
        t = np.unique(np.round(np.concatenate([sP[0] - aa * np.arange(4, 0, -1), sP, sP[-1] + aa * np.arange(1, 5)]), 9))
        # re-solve and keep w
        base = 4 * Lc(sP[:, None] - sP[None, :]).sum(2); M = 4 * Lc(sP[:, None] - t[None, :]); G = Kmat(t[:, None] - t[None, :]); T = Tg(sP)
        ev, V_ = np.linalg.eigh(G); keep = ev > 1e-12 * ev.max(); Vk = V_[:, keep]; ek = ev[keep]
        z = cp.Variable(Vk.shape[1]); tau = cp.Variable(P); cons = []
        for k in range(len(YC)):
            A = M[k] @ Vk; sc = np.maximum(1.0, np.maximum(np.abs(base[k]), np.abs(A).max(1)))
            cons.append(cp.multiply(1 / sc, tau) <= cp.multiply(1 / sc, base[k] + A @ z))
        prob = cp.Problem(cp.Maximize(T + cp.sum(tau) - 4 * cp.sum_squares(cp.multiply(np.sqrt(ek), z))), cons); prob.solve(solver=cp.CLARABEL)
        w = Vk @ np.asarray(z.value).ravel()
        baseF = 4 * Lmat(sP[:, None] - sP[None, :]).sum(2); MF = 4 * Lmat(sP[:, None] - t[None, :])
        ob = baseF + np.einsum('kpn,n->kp', MF, w); Dh = T + ob.min(0).sum() - 4 * w @ G @ w
        wit['a=%.2f P=%d' % (a, P)] = {'s': sP.tolist(), 't': t.tolist(), 'w': w.tolist(), 'QP_opt': float(prob.value), 'D_hard': float(Dh),
                                       'argmin_depths': YK[ob.argmin(0)].tolist(), 'T_g': T}
        print('witness a=%.2f P=%2d: QP %+9.3f hard %+9.3f | |w|_inf %.3g, n=%d' % (a, P, prob.value, Dh, np.abs(w).max(), len(t)), flush=True)
json.dump(wit, open('e34_witness.json', 'w'))
def tau(a): return 8 * float(g_of(a * np.arange(1, 400)).sum())
print('Near-density-1 thinness (optimal depth profile, depths in [0.8, 3]):')
for a in (0.85, 0.9, 0.95, 1.0, 1.05):
    tr = {}
    for P in (24, 48, 96):
        tr[P] = truth_min(a * np.arange(P))[0]
    bulk = (tr[96] - tr[48]) / 48; endt = tr[48] - 48 * bulk
    print('  a=%.2f tau(a) %.4f | truth(24) %.3f truth(48) %.3f truth(96) %.3f | bulk per-pair margin %.4f | end term %.3f'
          % (a, tau(a), tr[24], tr[48], tr[96], bulk, endt), flush=True)
