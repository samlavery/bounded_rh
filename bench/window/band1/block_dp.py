"""Multi-pair class (iii), first case: an EXACT-LATTICE block of P equal-depth pairs at sites 0..P-1 (line model, certificate v1).
  LP_total >= Q_pp + T_g + sum_env m_b Phi_P(x_b),   Q_pp = int qf (B^2 + 4B) |V_P|^2 (exact, bridge-port), |V_P|^2 = sin^2(pi P a)/sin^2(pi a),
  Phi_P(x) = sum_{j<P} phi_y(x - j)  (the block field), P_h dropped.
Environment: the two outer chains (by symmetry 2 V_edge), each a cluster-charged chain DP (crowd_dp2.py) from the edge pair outward with
one-body m Phi_P/y^2 + 4 m g(u)/y^2 (nearest pair double only); plus interstitial points inside the block, which pay
4 m [g(t) + g(1-t)] to their two neighbouring doubles: they are excluded by checking min_x [Phi_P(x) + 4 g(t) + 4 g(1-t)] >= 0
(a second interstitial in the same gap pays more).  Block bonds 8 g(1) (P - 1) kept.
  LP_total / y^2 >= Q_pp(y_lo)/y_hi^2... (Q_pp increasing in y) + 8 g(1)(P-1)/y_hi^2 + 2 V_edge.
usage: python3 block_dp.py YLO YHI NY P1,P2,..."""
import sys, time, numpy as np
YLO, YHI, NY = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); PS = [int(v) for v in sys.argv[4].split(',')]
sys.argv = ['crowd_dp2.py', '0', '1', '1', '32']
import crowd_dp2 as D2
C = D2.C
K, lo, hi = C.K, C.lo, C.hi
iaC = np.round(lo / C.ETA_C).astype(int); ibC = np.round(hi / C.ETA_C).astype(int); nC = C.Cg.shape[1]
def cj_shift_lo(j):
    """lower bounds of c_1..c_J over every cell shifted by +j (within the table; beyond it a tail bound is used by the caller)"""
    out = np.full((C.J, K), np.nan)
    ok = ibC + j * 2048 < nC
    for k in np.where(ok)[0]:
        out[:, k] = C.Cg[:, iaC[k] + j * 2048: ibC[k] + j * 2048 + 1].min(1)
    return out - (C.Cj2 * C.ETA_C ** 2 / 8)[:, None] - C.EPS, ok
xg, wg = np.polynomial.legendre.leggauss(400); al = (xg + 1) / 2; wa = wg / 2; qa = C.qf(al)
def Qpp(P, y):
    """int_{-1}^{1} qf (B^2 + 4B) sin^2(pi P a)/sin^2(pi a) / y^2  (increasing in y: B/y^2 and B^2/y^2 are), Gauss-Legendre on 4P pieces"""
    tot = 0.0; edges = np.linspace(0, 1, 4 * P + 1)
    for a0, a1 in zip(edges[:-1], edges[1:]):
        a = a0 + (a1 - a0) * al; w = (a1 - a0) * wa; b = (2 * np.cosh(2 * np.pi * a * y) - 2) / y ** 2 if y > 0 else (2 * np.pi * a) ** 2
        s = np.sin(np.pi * a); F = np.where(s > 1e-12, np.sin(np.pi * P * a) ** 2 / np.maximum(s, 1e-300) ** 2, P ** 2)
        tot += float(np.sum(w * C.qf(np.minimum(a, 1 - 1e-13)) * (b ** 2 * y ** 2 + 4 * b) * F))
    return 2 * tot
shift_cache = {}
def block_ps(P, ylo, yhi):
    tlo, thi = ylo ** 2, yhi ** 2; ps = np.zeros(K); A2, A3 = C.Btail(yhi); pjs = []
    for j in range(P):
        if j not in shift_cache: shift_cache[j] = cj_shift_lo(j)
        cl, ok = shift_cache[j]; pj = np.zeros(K)
        for i in range(1, C.J + 1):
            c = cl[i - 1]; pj += np.where(c < 0, c * thi ** (i - 1), c * tlo ** (i - 1))
        pj -= C.series_rem(thi)
        u = lo + j; tail = -(A2 / np.maximum(u, 1.0) ** 2 + A3 / np.maximum(u, 1.0) ** 3)
        pj = np.where(ok, pj, tail); ps += pj; pjs.append(pj)
    return ps, pjs
g1 = float(C.gfun(1.0)[0])
if __name__ == '__main__':
    t0 = time.time(); yb = np.linspace(YLO, YHI, NY + 1)
    orig = C.one_body
    print('exact-lattice equal-depth block: certified LP_total/y^2 lower bound (and per pair)', flush=True)
    for P in PS:
        worst = (np.inf, None)
        for ylo, yhi in zip(yb[:-1], yb[1:]):
            psb, pjs = block_ps(P, ylo, yhi)
            # interstitial check inside the block: x = p + t (t in cell k of [0,1), 256 cells of width 1/256), pairs at distances
            # t + i (i = 0..p, left) and (1 - t) + i (i = 0..P-2-p, right; mirror cell 255 - k); cost 4[g(t) + g(1-t)] per unit mass
            inter = np.inf; icorr = 0.0
            if P >= 2:
                kk = np.arange(256); assert abs(hi[255] - 1.0) < 1e-12
                L = np.cumsum([pj[kk] for pj in pjs], axis=0); R = np.cumsum([pj[255 - kk] for pj in pjs], axis=0)
                gt = 4 * (C.gcell[kk] + C.gcell[255 - kk]) / yhi ** 2
                icorr = 0.0; aps = D2.a_half / yhi ** 2
                for p in range(P - 1):
                    net = L[p] + R[P - 2 - p] + gt; inter = min(inter, float(np.min(net)))
                    for half in (net[:128], net[128:]):       # two half gaps; >= 2 points in a half gap pay g(1/2) per pair
                        Ph = max(0.0, -float(np.min(half)))
                        icorr += -2 * Ph if Ph <= 2 * aps else -aps * (1 + Ph / (2 * aps)) ** 2
            C.one_body = lambda a, b, psb=psb: (psb, orig(a, b)[1])
            try:
                s0, tx, V = D2.dp2(ylo, yhi)
            except AssertionError as e:
                print('  P=%d y in [%.4f, %.4f]: DP precondition fails (%s)' % (P, ylo, yhi, e), flush=True); C.one_body = orig; continue
            C.one_body = orig
            q = Qpp(P, ylo); bb = 8 * g1 * (P - 1) / yhi ** 2
            b = q + bb + 2 * V + icorr
            if b < worst[0]: worst = (b, (ylo, yhi))
            print('  P=%2d y in [%.4f, %.4f]: Q_pp/y^2 %.4f (per pair %.4f) bonds %.4f 2V_edge %+.4f -> LP_total/y^2 >= %+.4f (per pair %+.4f); interstitial net min %s (correction %+.3f)  [%.0fs]'
                  % (P, ylo, yhi, q, q / P, bb, 2 * V, b, b / P, ('%+.3f' % inter) if P >= 2 else '-', icorr, time.time() - t0), flush=True)
        print('P=%d: min LP_total/y^2 >= %+.4f at %s' % (P, worst[0], worst[1]), flush=True)
