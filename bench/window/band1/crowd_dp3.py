"""Multi-pair class (i), separated pairs: the single-pair chain DP of crowd_dp2.py with the SLACK ALLOCATION used when several
pairs share one configuration.  Pair p may use:
  * non-cluster T_g (bond length >= 1/2, and its own double's pair terms at distance >= 1/2) only inside its window |u| <= L;
  * cluster parts (bonds < 1/2, half-bin charges, same-cell pairs, its own double at distance < 1/2) with weight
        w(u) = WIN           for |u| <= L,
        w(u) = CW * (L/u)^2  for |u| >  L;
    for centres pairwise >= D0 apart these weights sum to <= 1 at every point (checked below), so no slack is used twice.
Everything else (cells, tables, field bounds, tail by half bins with the weighted cluster charge) as in crowd_dp2.py.
usage: python3 crowd_dp3.py YLO YHI NY [P] [L WIN CW D0]"""
import sys, time, numpy as np
YLO, YHI, NY = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); PCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 24
L, WIN, CW, D0 = ([float(v) for v in sys.argv[5:9]] if len(sys.argv) > 8 else [8.0, 0.9, 0.5, 32.0])
sys.argv = ['crowd_dp.py', '128', '8', '', '1e-8']
import crowd_dp as C
K, lo, hi = C.K, C.lo, C.hi
hb = np.floor(lo * 2 + 1e-9).astype(int)
a_half = float(C.gmin_range(np.array([0.0]), np.array([0.5]))[0])
def wcl(u):
    u = np.asarray(u, float); return np.where(u <= L + 1e-12, WIN, CW * (L / np.maximum(u, L)) ** 2)
# allocation check: for centres on the densest D0-separated set (a lattice of spacing D0, the worst case for decreasing weights),
# sup_x sum_p w_p(x) <= 1; nearest centres beyond L at distances r and D0 - r on the two sides
xs = np.linspace(-D0 / 2, D0 / 2, 20001); cen = D0 * np.arange(-400, 401)
tot = np.array([float(np.sum(wcl(np.abs(x - cen)))) for x in xs])
print('allocation: L=%g WIN=%g CW=%g D0=%g: sup_x sum_p w_p(x) = %.4f (must be <= 1)' % (L, WIN, CW, D0, tot.max()), flush=True)
assert tot.max() <= 1
w_cell = np.minimum(wcl(lo), wcl(hi))
hb_lo = hb / 2.0; w_hb = np.minimum(wcl(hb_lo), wcl(hb_lo + 0.5))
ws = np.where(hi <= 0.5 + 1e-12, WIN, np.where(hi <= L + 1e-12, 1.0, 0.0))     # own-double pair terms
def bond(k, kk):
    dmin = np.maximum(lo[kk] - hi[k], 0.0); dmax = hi[kk] - lo[k]
    inwin = hi[kk] <= L + 1e-12
    nc = np.where(dmax >= 0.5, C.gmin_range(np.maximum(dmin, 0.5), np.maximum(dmax, 0.5)), np.inf)
    nc = np.where(inwin, nc, np.where(dmax >= 0.5, 0.0, np.inf))
    wc = np.minimum(w_cell[k], w_cell[kk])
    cpart = np.where(dmin < 0.5, C.gmin_range(dmin, np.minimum(dmax, 0.5)) * wc, np.inf)
    return np.minimum(nc, cpart)
def dp3(ylo, yhi):
    ps, gg = C.one_body(ylo, yhi); iy2 = 1 / yhi ** 2
    one = {m: m * ps + 4 * m * gg * ws for m in (1, 2)}
    A2, A3 = C.Btail(yhi); jj = np.arange(int(2 * C.X), int(2 * C.X) + 400000, dtype=float) / 2; Psi = A2 / jj ** 2 + A3 / jj ** 3
    assert np.all(2 * a_half * wcl(jj) * iy2 >= Psi), 'tail: weighted cluster charge too small'
    T_X = -2 * float(Psi.sum()) - 4 * (A2 / jj[-1] + A3 / jj[-1] ** 2)
    selfg = C.gmin_range(np.zeros(K), hi - lo) * iy2 * w_cell
    clk = 2 * a_half * iy2 * w_hb                                  # per unit m' p, per cell
    W = np.full((3, PCAP + 1, K), np.inf)
    for k in range(K - 1, -1, -1):
        kk = np.arange(k + 1, K); same = hb[kk] == hb[k]; ko, ks = kk[~same], kk[same]
        go = bond(k, ko) * iy2 if len(ko) else None
        gs = bond(k, ks) * iy2 if len(ks) else None
        A = {}
        for m in (1, 2):
            best = T_X
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
                        v = float(np.min(2 * m * m2 * gs + one[m2][ks] + clk[ks] * m2 * p + W[m2, pn, ks]))
                        if v < best: best = v
                    base = 2 * m * m2 * selfg[k] + one[m2][k] + clk[k] * m2 * p
                    if pn == p:
                        assert base > 0, 'cluster cap too small at k=%d (u=%.3f)' % (k, lo[k])
                    else:
                        v = base + W[m2, pn, k]
                        if v < best: best = v
                W[m, p, k] = best
    V = min(T_X, float(min(np.min(one[m] + W[m, 0]) for m in (1, 2))))
    return C.S0(ylo), T_X, V
if __name__ == '__main__':
    t0 = time.time(); yb = np.linspace(YLO, YHI, NY + 1); worst = (np.inf, None); rows = []
    print('allocated-slack chain DP (class (i)): cap %d, y in [%.4f, %.4f] in %d intervals' % (PCAP, YLO, YHI, NY), flush=True)
    for ylo, yhi in zip(yb[:-1], yb[1:]):
        t1 = time.time()
        try:
            s0, tx, V = dp3(ylo, yhi)
        except AssertionError as e:
            print('  y in [%.4f, %.4f]: precondition fails (%s)' % (ylo, yhi, e), flush=True); worst = (-np.inf, (ylo, yhi)); continue
        b = s0 + 2 * V
        if b < worst[0]: worst = (b, (ylo, yhi))
        print('  y in [%.4f, %.4f]: S0 %.3f T_X %+.4f V %+.4f -> LP_p/y^2 >= %+.4f  [%.0fs]' % (ylo, yhi, s0, tx, V, b, time.time() - t1), flush=True)
    print('CERTIFIED (allocated slack) on [%.4f, %.4f]: LP_p/y^2 >= %+.4f (binding %s)  total %.0fs' % (YLO, YHI, worst[0], worst[1], time.time() - t0), flush=True)
