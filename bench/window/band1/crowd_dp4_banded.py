"""Round 5, am-cert fit conditions.  (C2) banded DP: crowd_dp4.dp3 with every bond of cell distance d_min > r set to 0 (valid lower bound:
bond >= 0 since gblk >= 0 and the weights are >= 0); the successor search beyond r becomes a suffix minimum of one[m2] + W[m2, 0].
r = inf reproduces dp3 exactly (validation).  Class-(i) margin per y-interval = (LP_p/y^2 bound) - (X charge from the xlemma log).
(C3) on the unbanded tables: is W[m, p, k] non-decreasing in the cluster count p, and the saturation level p* beyond which
W[m, p, k] = W[m, PCAP, k].
usage: python3 crowd_dp4_banded.py YLO YHI NY PCAP L WINC CW DEL R1,R2,.. XLOG"""
import sys, re, time, numpy as np
args = sys.argv[1:]; RS = [float(v) for v in args[8].split(',')]; XLOG = args[9]
sys.argv = ['crowd_dp4.py'] + args[:8]
exec(open('crowd_dp4.py').read().split("if __name__ == '__main__':")[0])
XC = {(round(float(a), 4), round(float(b), 4)): float(r) for a, b, r in
      re.findall(r'y_q in \[([\d.]+), ([\d.]+)\]: margin [-\d.]+ \| X charge ([-\d.]+)', open(XLOG).read())}
def dpb(ylo, yhi, r):
    ps, gg = C.one_body(ylo, yhi); iy2 = 1 / yhi ** 2
    one = {m: m * ps + 4 * m * gg * ws for m in (1, 2)}
    A2, A3 = C.Btail(yhi); jj = np.arange(int(2 * C.X), int(2 * C.X) + 400000, dtype=float) / 2; Psi = A2 / jj ** 2 + A3 / jj ** 3
    aw = a_half * wcl(jj) * iy2
    bj = np.where(Psi <= 2 * aw, -2 * Psi, -aw * (1 + Psi / (2 * aw)) ** 2)
    T_X = float(bj.sum()) - 4 * (A2 / jj[-1] + A3 / jj[-1] ** 2) * max(1.0, float(Psi[-1] / (2 * aw[-1])))
    selfg = C.gmin_range(np.zeros(K), hi - lo) * iy2 * w_cell
    clk = 2 * a_half * iy2 * w_hb
    W = np.full((3, PCAP + 1, K), np.inf); SM = {m2: np.full(K + 1, np.inf) for m2 in (1, 2)}
    for k in range(K - 1, -1, -1):
        jf = K if not np.isfinite(r) else int(np.searchsorted(lo, hi[k] + r, side='right'))
        kk = np.arange(k + 1, jf); same = hb[kk] == hb[k]; ko, ks = kk[~same], kk[same]
        assert jf >= K or hb[jf] != hb[k]
        go = bond(k, ko) * iy2 if len(ko) else None
        gs = bond(k, ks) * iy2 if len(ks) else None
        A = {}
        for m in (1, 2):
            best = T_X
            for m2 in (1, 2):
                if len(ko):
                    v = float(np.min(2 * m * m2 * go + one[m2][ko] + W[m2, 0, ko]))
                    if v < best: best = v
                if jf < K and SM[m2][jf] < best: best = float(SM[m2][jf])     # bonds beyond r dropped (>= 0)
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
        for m2 in (1, 2): SM[m2][k] = min(SM[m2][k + 1], one[m2][k] + W[m2, 0, k])
    V = min(T_X, float(min(np.min(one[m] + W[m, 0]) for m in (1, 2))))
    return C.S0(ylo), T_X, V, W
def mono(W):
    Wm = W[1:3]; d = Wm[:, :-1, :] - Wm[:, 1:, :]; scale = 1e-12 * np.maximum(1.0, np.abs(Wm[:, :-1, :]))
    viol = float(np.max(d - scale)); nviol = int(np.sum(d > scale))
    sat = np.abs(Wm - Wm[:, -1:, :]) <= 1e-12 * np.maximum(1.0, np.abs(Wm[:, -1:, :]))          # W[m, p, k] == W[m, PCAP, k]
    tail_ok = np.flip(np.cumprod(np.flip(sat, axis=1), axis=1), axis=1).astype(bool)          # saturated from p onwards
    pstar = np.argmax(tail_ok, axis=1)                                                       # first p with saturation onwards
    return viol, nviol, int(pstar.max()), np.bincount(pstar.ravel(), minlength=PCAP + 1)
yb = np.linspace(YLO, YHI, NY + 1); res = {r: [] for r in RS}; t0 = time.time(); allp = np.zeros(PCAP + 1, int); worstv = -np.inf
print('banded crowd_dp4: L=%g WINC=%g CW=%g DEL=%g, cap %d, y in [%.4f, %.4f] (%d intervals), r in %s' % (L, WINC, CW, DEL, PCAP, YLO, YHI, NY, RS), flush=True)
for ylo, yhi in zip(yb[:-1], yb[1:]):
    R = XC[(round(ylo, 4), round(yhi, 4))]; line = '  y in [%.4f, %.4f]: X charge %.4f |' % (ylo, yhi, R)
    for r in RS:
        s0, tx, V, W = dpb(ylo, yhi, r); b = s0 + 2 * V; res[r].append((b - R, b, (ylo, yhi)))
        line += ' r=%g: LP_p/y^2 >= %+.4f, m-R %+.4f |' % (r, b, b - R)
        if not np.isfinite(r):
            viol, nviol, pmax, hist = mono(W); allp += hist; worstv = max(worstv, viol)
            line += ' [C3: max decrease in p %.2e (%d cells), p* max %d] |' % (max(viol, 0.0), nviol, pmax)
    print(line, flush=True)
for r in RS:
    mn = min(res[r]); print('r = %g: min (margin - X charge) = %+.4f at y in [%.4f, %.4f] -> %s' % (r, mn[0], mn[2][0], mn[2][1], 'CLOSED' if mn[0] > 0 else 'NOT closed'), flush=True)
if any(not np.isfinite(r) for r in RS):
    print('C3: W[m, p, k] non-decreasing in p: %s (max decrease %.2e); saturation level p* histogram over all (m, k, y-intervals): %s'
          % ('YES' if worstv <= 0 else 'NO', max(worstv, 0.0), {i: int(v) for i, v in enumerate(allp) if v}), flush=True)
print('total %.0fs' % (time.time() - t0), flush=True)
