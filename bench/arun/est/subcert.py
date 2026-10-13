"""Round 11 (2): leaf-count proxy for certificates of 'F_S >= theta on a box' (S = a sub-frame or the full frame).
Test of a box: the centred second-order bound
    LB = F(x_c) - sum_s |dF/dg_s(x_c)| h_s - 1/2 sum_t a_t sup|w''|(range_t) (sum_{s in t} h_s)^2,
a valid lower bound (Taylor with Lagrange remainder; the Hessian is sum_t a_t w''(d_t) u_t u_t^T).  Bisect the widest gap.
Boxes whose pair-sum range misses a constraint interval are dropped (they are empty).  Values: tabled K, K' (step 2e-4), |w''| from
w_profile.npz maximised over cells of width 0.01, range max by a sparse table.  Calibrated against the sizer's own subtree sizes."""
import numpy as np
Z = np.load('/Users/samuellavery/work/riemann-submission/bench/arun/est/w_profile.npz')
_s, _d2 = Z['s'], np.abs(Z['d2']); CW = 0.01; NC = int(np.ceil(_s[-1] / CW))
_cell = np.array([_d2[int(round(c * CW / 2e-4)):int(round((c + 1) * CW / 2e-4)) + 1].max() for c in range(NC)])
_ST = [_cell]
while 2 ** len(_ST) <= NC:
    p = _ST[-1]; k = 2 ** (len(_ST) - 1); _ST.append(np.maximum(p[:-k], p[k:]))
def m2(dlo, dhi):
    """sup |w''| over [dlo, dhi], elementwise (cell-conservative; distances beyond the table use the last cell)"""
    a = np.clip((dlo / CW).astype(int), 0, NC - 1); b = np.clip((dhi / CW).astype(int), 0, NC - 1); b = np.maximum(a, b)
    L = b - a + 1; k = np.floor(np.log2(L)).astype(int); out = np.empty(a.shape)
    for kk in np.unique(k):
        sel = k == kk; T = _ST[kk]; out[sel] = np.maximum(T[a[sel]], T[b[sel] - 2 ** kk + 1])
    return out
def lower_bound(side, LO, HI):
    xc = (LO + HI) / 2; h = (HI - LO) / 2
    f, g = side.fgt(xc)
    dlo = LO @ side.Inc.T; dhi = HI @ side.Inc.T; hs = h @ side.Inc.T
    return f - (np.abs(g) * h).sum(1) - 0.5 * (side.a * m2(dlo, dhi) * hs * hs).sum(1)
def nonempty(LO, HI, cl):
    ok = np.ones(len(LO), bool)
    for i, j, lb, ub in cl:
        ok &= (HI[:, i:j].sum(1) >= lb - 1e-12) & (LO[:, i:j].sum(1) <= ub + 1e-12)
    return ok
def count(side, lo, hi, cl, theta, cap=100000, minw=2.0 ** -16):
    """number of leaves of the proxy bisection certifying F_side >= theta on the box (with constraints cl); cap -> returns (cap, False)"""
    if side.m == 0: return 0, True
    LO = np.array([lo], float); HI = np.array([hi], float); leaves = 0
    while len(LO):
        ok = nonempty(LO, HI, cl); LO, HI = LO[ok], HI[ok]
        if not len(LO): break
        lb = lower_bound(side, LO, HI); done = lb >= theta; leaves += int(done.sum())
        LO, HI = LO[~done], HI[~done]
        if leaves + 2 * len(LO) > cap: return cap, False
        if not len(LO): break
        w = HI - LO; s = np.argmax(w, 1); r = np.arange(len(LO))
        if np.any(w[r, s] < minw): return cap, False
        mid = (LO[r, s] + HI[r, s]) / 2
        LO2 = LO.copy(); HI2 = HI.copy(); HI[r, s] = mid; LO2[r, s] = mid
        LO = np.vstack([LO, LO2]); HI = np.vstack([HI, HI2])
    return leaves, True
