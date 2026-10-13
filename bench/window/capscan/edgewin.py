"""(2) Edge windows: PC8SF plus truncated windows at both block ends (the same pair weights and pressures restricted to
the available gaps).  Each truncated window with k gaps (k = 1..6) adds its own floor c_t(k) = min over gaps of the
restricted functional to the certified sum, and its restricted pressure B_t(k) to the cost; pair coverage stays <= 2
(the full set of window offsets sums to the span mass).  kappa' = (mH - P - dP)/(m - g(c(m-q) + sum c_t))."""
import itertools, math, numpy as np
from scipy.optimize import minimize
from rmax import Fwin, kappa, B, tau, m, K, bN, aN
from slack import H
cN = 805124 / 1e8; q = 7
def g(E): return E if E <= tau else 2 * math.sqrt(tau * E) - tau
def Ftrunc(gk, k, side):
    """right truncation: points 0..k (gaps 0..k-1); left: points 7-k..7 (gaps 7-k..6)"""
    off = 0 if side == 'R' else 7 - k
    x = np.concatenate([[0.0], np.cumsum(gk)])
    v = float(np.dot(bN[off:off + k], gk))
    for (a, b), wt in aN.items():
        if wt and off <= a and b <= off + k:
            v += wt * K(np.array([x[b - off] - x[a - off]]))[0] ** 2
    return v
tot_c = 0.0; tot_B = 0.0; rows = []
for side in ('R', 'L'):
    off = lambda k: 0 if side == 'R' else 7 - k
    for k in range(1, 7):
        best = (np.inf, None)
        starts = [np.array(p) for p in itertools.product((0.0, 1.04, 1.97, 3.0), repeat=k)] if k <= 4 else \
                 [np.array(p) for p in itertools.product((1.04, 1.97), repeat=k)] + [np.random.default_rng(k).uniform(0, 3, k) for _ in range(40)]
        for s0 in starts:
            r = minimize(lambda gk: Ftrunc(gk, k, side), s0, method='L-BFGS-B', bounds=[(0, 8)] * k)
            if r.fun < best[0]: best = (float(r.fun), r.x)
        Bt = float(bN[off(k):off(k) + k].sum())
        rows.append((side, k, best[0], Bt, np.round(best[1], 3)))
        tot_c += best[0]; tot_B += Bt
        print('%s k=%d: floor c_t %.7f  restricted pressure B_t %.7f  (kappa*c_t - B_t = %+.2e)  at %s'
              % (side, k, best[0], Bt, 0.6734832 * best[0] - Bt, np.round(best[1], 3)), flush=True)
R0 = g(cN * (m - q)); P0 = B * (m - q); k0 = (m * H - P0) / (m - R0)
def kap(extra_c, extra_B, mm=m):
    return (mm * H - B * (mm - q) - extra_B) / (mm - g(cN * (mm - q) + extra_c))
print('\nPC8SF kappa %.7f (H %.10f)' % (k0, H))
print('all 12 edge windows: sum c_t %.6f, sum B_t %.6f -> kappa %.7f (gain %+.2e)' % (tot_c, tot_B, kap(tot_c, tot_B), kap(tot_c, tot_B) - k0))
# only the windows that pay for themselves
good = [r for r in rows if 0.6734832 * r[2] - r[3] > 0]
cg = sum(r[2] for r in good); Bg = sum(r[3] for r in good)
print('profitable subset (%d windows): kappa %.7f (gain %+.2e)' % (len(good), kap(cg, Bg), kap(cg, Bg) - k0))
best_m = max((kap(cg, Bg, mm) - ((mm * H - B * (mm - q)) / (mm - g(cN * (mm - q)))), mm) for mm in range(130, 200))
print('gain at other m (profitable subset vs PC8SF formula at the same m): best %+.2e at m %d' % best_m)
