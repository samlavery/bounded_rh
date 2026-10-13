"""Multi-pair class (i) at small separation D0 = 2L (Voronoi version of crowd_dp3.py).  Pair p uses
  * non-cluster T_g (bonds >= 1/2, own-double terms at distance >= 1/2) with the Voronoi weight v(u) = 1 on [0, L-DEL], linear to 0 at
    L+DEL (so v(u) + v(D0-u) = 1 for two centres D0 apart, and sum_p v_p <= 1 for any D0-separated set);
  * cluster parts with weight c(u) = WINC v(u) + CW (L/u)^2 [u >= L]  (sum_p c_p <= 1 checked on the densest D0-separated set).
(Text below from crowd_dp3.py describes the step-profile special case.)
Multi-pair class (i), separated pairs: the single-pair chain DP of crowd_dp2.py with the SLACK ALLOCATION used when several
pairs share one configuration.  Pair p may use:
  * non-cluster T_g (bond length >= 1/2, and its own double's pair terms at distance >= 1/2) only inside its window |u| <= L;
  * cluster parts (bonds < 1/2, half-bin charges, same-cell pairs, its own double at distance < 1/2) with weight
        w(u) = WIN           for |u| <= L,
        w(u) = CW * (L/u)^2  for |u| >  L;
    for centres pairwise >= D0 apart these weights sum to <= 1 at every point (checked below), so no slack is used twice.
Everything else (cells, tables, field bounds, tail by half bins with the weighted cluster charge) as in crowd_dp2.py.
usage: python3 crowd_dp4.py YLO YHI NY [P] [L WINC CW DEL]"""
import sys, time, numpy as np
YLO, YHI, NY = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); PCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 24
L, WINC, CW, DEL = ([float(v) for v in sys.argv[5:9]] if len(sys.argv) > 8 else [2.0, 0.8, 0.1, 0.5]); D0 = 2 * L
sys.argv = ['crowd_dp.py', '128', '8', '', '1e-8']
import crowd_dp as C
K, lo, hi = C.K, C.lo, C.hi
hb = np.floor(lo * 2 + 1e-9).astype(int)
a_half = float(C.gmin_range(np.array([0.0]), np.array([0.5]))[0])
def vnc(u):
    u = np.asarray(u, float); return np.clip((L + DEL - u) / (2 * DEL), 0.0, 1.0)
def wcl(u):
    u = np.asarray(u, float); return WINC * vnc(u) + np.where(u >= L + DEL, CW * (L / np.maximum(u, L)) ** 2, 0.0)
# allocation check: for centres on the densest D0-separated set (a lattice of spacing D0, the worst case for decreasing weights),
# sup_x sum_p w_p(x) <= 1; nearest centres beyond L at distances r and D0 - r on the two sides
xs = np.linspace(-D0 / 2, D0 / 2, 20001); cen = D0 * np.arange(-400, 401)
tot = np.array([float(np.sum(wcl(np.abs(x - cen)))) for x in xs]); totv = np.array([float(np.sum(vnc(np.abs(x - cen)))) for x in xs])
print('allocation: L=%g WINC=%g CW=%g DEL=%g D0=%g: sup sum cluster weights %.4f, sup sum non-cluster weights %.4f (both <= 1)' % (L, WINC, CW, DEL, D0, tot.max(), totv.max()), flush=True)
assert tot.max() <= 1 + 1e-12 and totv.max() <= 1 + 1e-12
w_cell = np.minimum(wcl(lo), wcl(hi))
hb_lo = hb / 2.0; w_hb = np.minimum(wcl(hb_lo), wcl(hb_lo + 0.5))
vcell = np.minimum(vnc(lo), vnc(hi))
ws = np.where(hi <= 0.5 + 1e-12, w_cell, vcell)                                    # own-double pair terms
def bond(k, kk):
    dmin = np.maximum(lo[kk] - hi[k], 0.0); dmax = hi[kk] - lo[k]
    vw = np.minimum(vcell[k], vcell[kk])
    nc = np.where(dmax >= 0.5, C.gmin_range(np.maximum(dmin, 0.5), np.maximum(dmax, 0.5)) * vw, np.inf)
    wc = np.minimum(w_cell[k], w_cell[kk])
    cpart = np.where(dmin < 0.5, C.gmin_range(dmin, np.minimum(dmax, 0.5)) * wc, np.inf)
    return np.minimum(nc, cpart)
def dp3(ylo, yhi):
    ps, gg = C.one_body(ylo, yhi); iy2 = 1 / yhi ** 2
    one = {m: m * ps + 4 * m * gg * ws for m in (1, 2)}
    A2, A3 = C.Btail(yhi); jj = np.arange(int(2 * C.X), int(2 * C.X) + 400000, dtype=float) / 2; Psi = A2 / jj ** 2 + A3 / jj ** 3
    aw = a_half * wcl(jj) * iy2                                   # weighted cluster charge per half bin (units of y^2)
    bj = np.where(Psi <= 2 * aw, -2 * Psi, -aw * (1 + Psi / (2 * aw)) ** 2)   # half-bin minimum, valid for any weight
    T_X = float(bj.sum()) - 4 * (A2 / jj[-1] + A3 / jj[-1] ** 2) * max(1.0, float(Psi[-1] / (2 * aw[-1])))
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
    print('Voronoi-allocated chain DP (class (i), D0 = %g): cap %d, y in [%.4f, %.4f] in %d intervals' % (D0, PCAP, YLO, YHI, NY), flush=True)
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
