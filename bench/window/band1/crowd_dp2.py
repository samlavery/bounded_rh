"""Single pair, intermediate depths: the nearest-neighbour chain DP of crowd_dp.py with an explicit CLUSTER CHARGE.
Half bins H_j = [j/2, (j+1)/2) on each side of s.  Every same-side pair of points inside one half bin is at distance < 1/2,
so it pays at least g(1/2) (g decreasing on [0, 0.9]); consecutive pairs keep their exact bond.  The DP state carries the
mass p already placed in the current half bin before the last point (capped at P; at the cap the charge uses P, a lower
bound), so a new point in the same half bin pays 2 m' p g(1/2)/y^2 on top of its bond: clusters cost quadratically.
  LP/y^2 >= S0(y_lo) + 2 V,  V = min over one-sided chains of
     sum_i [m_i psi_y(u_i) + 4 m_i g(u_i)/y^2] + sum_i 2 m_i m_{i+1} g(u_{i+1}-u_i)/y^2 + sum_{H} sum_{non-consecutive pairs in H} 2 m m' g(1/2)/y^2.
Tail beyond X by half bins (needs g(1/2)/y^2 >= sup|psi|).  Same cell bounds, tables and allowances as crowd_dp.py.
usage: python3 crowd_dp2.py YLO YHI NY [P] [LOC]"""
import sys, time, numpy as np
YLO, YHI, NY = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); PCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 16
LOC = float(sys.argv[5]) if len(sys.argv) > 5 else None     # slack localised to [0, LOC]: beyond, only cluster parts (bond < 1/2, half-bin charges)
sys.argv = ['crowd_dp.py', '128', '8', '', '1e-8']
import crowd_dp as C
K, lo, hi = C.K, C.lo, C.hi
hb = np.floor(lo * 2 + 1e-9).astype(int); assert np.all(np.floor(hi * 2 - 1e-9).astype(int) == hb)
a_half = float(C.gmin_range(np.array([0.0]), np.array([0.5]))[0])
def dp2(ylo, yhi):
    ps, gg = C.one_body(ylo, yhi); iy2 = 1 / yhi ** 2
    if LOC is not None: gg = np.where(hi <= LOC + 1e-12, gg, 0.0)
    one = {m: m * ps + 4 * m * gg for m in (1, 2)}
    A2, A3 = C.Btail(yhi); jj = np.arange(int(2 * C.X), int(2 * C.X) + 400000, dtype=float) / 2; Psi = A2 / jj ** 2 + A3 / jj ** 3
    assert a_half * iy2 >= Psi[0]
    T_X = -2 * float(Psi.sum()) - 4 * (A2 / jj[-1] + A3 / jj[-1] ** 2)
    selfg = C.gmin_range(np.zeros(K), hi - lo) * iy2
    cl = 2 * a_half * iy2                                   # per unit m' p
    W = np.full((3, PCAP + 1, K), np.inf)                  # W[m][p][k], m in {1, 2}
    for k in range(K - 1, -1, -1):
        kk = np.arange(k + 1, K); same = hb[kk] == hb[k]; ko, ks = kk[~same], kk[same]
        go = C.pair_g_full(k, ko) * iy2 if len(ko) else None
        gs = C.pair_g_full(k, ks) * iy2 if len(ks) else None
        A = {}
        for m in (1, 2):
            best = C_T = T_X
            for m2 in (1, 2):
                if len(ko):
                    v = float(np.min(2 * m * m2 * go + one[m2][ko] + W[m2, 0, ko]))
                    if v < best: best = v
            A[m] = best
        for p in range(PCAP, -1, -1):
            for m in (1, 2):
                pn = min(p + m, PCAP); best = A[m]
                for m2 in (1, 2):
                    if len(ks):
                        v = float(np.min(2 * m * m2 * gs + one[m2][ks] + cl * m2 * p + W[m2, pn, ks]))
                        if v < best: best = v
                    base = 2 * m * m2 * selfg[k] + one[m2][k] + cl * m2 * p
                    if pn == p:
                        assert base > 0, 'cluster cap too small: same-cell loop at the cap not positive (k=%d)' % k
                    else:
                        v = base + W[m2, pn, k]
                        if v < best: best = v
                W[m, p, k] = best
    V = min(T_X, float(min(np.min(one[m] + W[m, 0]) for m in (1, 2))))
    return C.S0(ylo), T_X, V
def pair_g_full(k, kk):
    dmin = np.maximum(lo[kk] - hi[k], 0.0); dmax = hi[kk] - lo[k]; full = C.gmin_range(dmin, dmax)
    if LOC is None: return full
    clus = np.where(dmin < 0.5, C.gmin_range(dmin, np.minimum(dmax, 0.5)), 0.0)
    return np.where(hi[kk] <= LOC + 1e-12, full, clus)
C.pair_g_full = pair_g_full
if __name__ == '__main__':
    t0 = time.time(); yb = np.linspace(YLO, YHI, NY + 1); worst = (np.inf, None)
    print('cluster-charged chain DP: g(1/2) = %.6f, cap P = %d, y in [%.4f, %.4f] in %d intervals; slack %s' % (a_half, PCAP, YLO, YHI, NY, 'full' if LOC is None else 'localised to [0, %g] (+ cluster parts)' % LOC), flush=True)
    for ylo, yhi in zip(yb[:-1], yb[1:]):
        t1 = time.time()
        try:
            s0, tx, V = dp2(ylo, yhi)
        except AssertionError as e:
            print('  y in [%.4f, %.4f]: precondition fails (%s)' % (ylo, yhi, e), flush=True); continue
        b = s0 + 2 * V
        if b < worst[0]: worst = (b, (ylo, yhi))
        print('  y in [%.4f, %.4f]: S0 %.3f T_X %+.4f V %+.4f -> ALL D: LP/y^2 >= %+.4f  [%.0fs]' % (ylo, yhi, s0, tx, V, b, time.time() - t1), flush=True)
    print('CERTIFIED on [%.4f, %.4f]: LP/y^2 >= %+.4f (binding %s)  total %.0fs' % (YLO, YHI, worst[0], worst[1], time.time() - t0), flush=True)
