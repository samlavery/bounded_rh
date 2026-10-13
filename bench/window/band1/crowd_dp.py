"""Step d (crowding regime): certified lower bound for the shallow-depth defect gap, certificate v1, line model.

  LP(D, y) = s(D) + Delta_B(y) = P_h(D) + T_g(D) + 2[K(2iy) - K(0)] + sum_env m_b phi_y(u_b),
  phi_y(u) = 4[Re K(u + iy) - K(u)],  T_g(D) = sum_{a != b} m_a m_b g(x_a - x_b) >= 0,  P_h >= 0,
  u_b = x_b - s, the pair's own double at s (mass 2).  Dropping P_h, the cross-side env-env pairs and every same-side pair
  that is not consecutive (all >= 0, since g >= 0 by the certified C >= m_C):
      LP / y^2 >= S0(y) + V_right + V_left,     S0 = 2[K(2iy) - K(0)]/y^2,
      V_side = sum_i [ m_i psi_y(u_i) + 4 m_i g(u_i)/y^2 ] + sum_i 2 m_i m_{i+1} g(u_{i+1} - u_i)/y^2,   psi = phi/y^2,
  over ordered one-sided chains 0 < u_1 <= u_2 <= ... with masses in {1, 2}.
Crowding class C(R, d0): some env point with 0 < |u| <= R + 1/2 lies outside every site window [n - d0, n + d0]
(n = +-1..+-R), or two env points share a site window.  On C one side carries the crowding event, so
      LP / y^2 >= S0(y) + V^free + V^crowd(R, d0).
Both V's are computed by a backward DP over position cells (shortest path on the ordered cells, self-loops allowed and
positive), each one-body / pair term replaced by a certified cell lower bound:
  * psi_y(u) = sum_j t^{j-1} c_j(u), t = y^2, c_j = (8/(2j)!) int_0^1 qf (2 pi a)^{2j} cos(2 pi a u) da; min over the cell of
    c_j from a grid of spacing eta_c minus |c_j''|_max eta_c^2/8, then the extreme over t in the y-interval; series
    remainder bounded explicitly;
  * g from its exact trigonometric form; block minima on a grid of spacing eta_g minus |g''|_max eta_g^2/8 (|g''|_max from
    the knot values of g^), clipped at 0; pair terms use the min of g over the full distance range of the two cells;
  * 1/y^2 on g-terms taken at y_hi, S0 at y_lo (S0 is increasing in y);
  * tail beyond X (step 6): |psi_y(u)| <= B(y)/u^2 by two integrations by parts; a unit bin with >= 2 points pays
    k(k-1) g(1)/y^2, so each bin contributes >= -2 sup|psi| when g(1)/y^2 >= sup|psi| (checked).
Floating point: double precision; quadrature verified by node doubling; an allowance EPS is subtracted per evaluation.
usage: python3 crowd_dp.py [X]"""
import sys, json, time, math, numpy as np
from fractions import Fraction
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
t00 = time.time()
X = float(sys.argv[1]) if len(sys.argv) > 1 else 128.0
EPS = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-10
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); nb, Dk = 96, 1 / 32
assert len(yk) == nb

# ---------------- g (certificate v1) ----------------
def gfun(u):
    u = np.atleast_1d(np.asarray(u, float)); out = np.empty(len(u)); bs = np.arange(1, nb)
    for i in range(0, len(u), 20000):
        th = 2 * np.pi * Dk * u[i:i + 20000]; C = yk[0] + 2 * (np.cos(np.outer(th, bs)) @ yk[1:])
        out[i:i + 20000] = Dk * np.sinc(Dk * u[i:i + 20000]) ** 2 * C
    return out
yext = np.concatenate([yk, [0.0]])
M2g = 2 * (2 * np.pi) ** 2 * sum(max(abs(yext[b]), abs(yext[b + 1])) * (((b + 1) * Dk) ** 3 - (b * Dk) ** 3) / 3 for b in range(nb))
ETA_G = 1 / 8192; BLK = 8                       # blocks of 8 fine intervals = 1/1024
ug = np.arange(0, X + 2 + 1e-12, ETA_G); gv = gfun(ug)
nblk = (len(ug) - 1) // BLK
gblk = gv[:nblk * BLK + 1]
gblk = np.minimum(gblk[:-1].reshape(nblk, BLK).min(1), gblk[BLK::BLK]) - M2g * ETA_G ** 2 / 8 - 1e-14
gblk = np.maximum(gblk, 0.0)                     # g >= 0 (certified C >= m_C > 0)
ETA_B = ETA_G * BLK
# sparse table for range minima over blocks
ST = [gblk]
while (1 << len(ST)) <= nblk:
    p = ST[-1]; s = 1 << (len(ST) - 1); ST.append(np.minimum(p[:-s], p[s:]) if len(p) > s else p[:0])
def gmin_range(a, b):
    """certified lower bound of g on [a, b] (arrays), a >= 0"""
    ia = np.clip(np.floor(a / ETA_B).astype(np.int64), 0, nblk - 1); ib = np.clip(np.ceil(b / ETA_B).astype(np.int64) - 1, 0, nblk - 1)
    ib = np.maximum(ib, ia); L = np.floor(np.log2(ib - ia + 1)).astype(np.int64)
    out = np.empty(len(ia))
    for l in np.unique(L):
        sel = L == l; out[sel] = np.minimum(ST[l][ia[sel]], ST[l][ib[sel] - (1 << l) + 1])
    return out
g1 = float(gmin_range(np.array([0.0]), np.array([1.0]))[0])     # certified min of g on [0, 1] (tail bins)

# ---------------- psi coefficients ----------------
xg, wg = np.polynomial.legendre.leggauss(600); al = (xg + 1) / 2; wa = wg / 2; qa = qf(al)
xg2, wg2 = np.polynomial.legendre.leggauss(1000); al2 = (xg2 + 1) / 2; wa2 = wg2 / 2; qa2 = qf(al2)
J = 9
def cjs(u, A=al, W=wa, Q=qa):
    u = np.atleast_1d(np.asarray(u, float)); out = np.empty((J, len(u)))
    Wj = np.array([8 / math.factorial(2 * j) * Q * W * (2 * np.pi * A) ** (2 * j) for j in range(1, J + 1)])   # J x n
    for i in range(0, len(u), 4000):
        out[:, i:i + 4000] = Wj @ np.cos(2 * np.pi * np.outer(A, u[i:i + 4000]))
    return out
Qabs = lambda k: float(np.sum(np.abs(qa2) * wa2 * (2 * np.pi * al2) ** k))
Cj2 = np.array([8 / math.factorial(2 * j) * Qabs(2 * j + 2) for j in range(1, J + 1)])    # sup |c_j''|
def series_rem(t):  # sup_u |sum_{j > J} t^{j-1} c_j(u)|
    return sum(t ** (j - 1) * 8 / math.factorial(2 * j) * Qabs(2 * j) for j in range(J + 1, J + 30))
uchk = np.array([0.0, 0.79, 1.0, 2.37, 31.1, X + 1.0]); dq = np.max(np.abs(cjs(uchk) - cjs(uchk, al2, wa2, qa2)))
print('X = %g; |g\'\'| <= %.3f; min g on [0,1] = %.3e; quadrature check (600 vs 1000 nodes) max diff %.2e; EPS %.0e' % (X, M2g, g1, dq, EPS), flush=True)
assert dq < EPS / 10
ETA_C = 1 / 2048
uc = np.arange(0, X + 1 + 1e-12, ETA_C); Cg = cjs(uc)
print('  c_j tables on %d points [%.0fs]' % (len(uc), time.time() - t00), flush=True)
def S0(y):
    if y == 0: return float(4 * np.sum(qa2 * wa2 * (4 * np.pi * al2) ** 2 / 2))
    return float(4 * np.sum(qa2 * wa2 * (np.cosh(4 * np.pi * al2 * y) - 1)) / y ** 2)

# tail constants: psi = 8 int_0^1 p cos(w a), w = 2 pi u, p = qf (cosh(2 pi a y)-1)/y^2, p(1) = p'(0) = 0; three integrations
# by parts give |psi_y(u)| <= A2/u^2 + A3/u^3, A2 = 8|p'(1)|/(2 pi)^2, A3 = 8(|p''(1)| + int|p'''|)/(2 pi)^3
# (derivatives by finite differences, times 1.05; checked against the exact psi on [X, X + 40])
af = np.linspace(0, 1, 20001); qff = qf(np.minimum(af, 1 - 1e-13)); qff[-1] = 0.0
def Btail(y):
    b = (np.cosh(2 * np.pi * af * y) - 1) / y ** 2 if y > 0 else (2 * np.pi * af) ** 2 / 2
    p = qff * b; d1 = np.gradient(p, af, edge_order=2); d2 = np.gradient(d1, af, edge_order=2); d3 = np.gradient(d2, af, edge_order=2)
    return (1.05 * 8 * abs(d1[-1]) / (2 * np.pi) ** 2, 1.05 * 8 * (abs(d2[-1]) + np.trapezoid(np.abs(d3), af)) / (2 * np.pi) ** 3)
ut = np.linspace(X, X + 40, 4001)
for yt in (0.05, 0.4):
    emp = np.abs((cjs(ut)[:5] * np.array([yt ** (2 * j) for j in range(5)])[:, None]).sum(0)); A2, A3 = Btail(yt)
    print('  tail check y=%.2f: A2 %.4f A3 %.4f; max over [X, X+40] of |psi|/(A2/u^2 + A3/u^3) = %.4f (must be < 1)'
          % (yt, A2, A3, np.max(emp / (A2 / ut ** 2 + A3 / ut ** 3))), flush=True)

# ---------------- cells ----------------
edges = [0.0]
for (end, h) in ((5.0, 1 / 256), (16.0, 1 / 128), (48.0, 1 / 64), (X, 1 / 32)):
    end = min(end, X)
    while edges[-1] < end - 1e-12: edges.append(round(edges[-1] + h, 12))
edges = np.array(edges); lo, hi = edges[:-1], edges[1:]; K = len(lo)
def cell_min_grid(T):   # min over grid points of each cell (grid aligned: all edges are multiples of ETA_C)
    ia = np.round(lo / ETA_C).astype(int); ib = np.round(hi / ETA_C).astype(int)
    return np.array([T[..., ia[k]:ib[k] + 1].min(-1) for k in range(K)]).T
cjlo = cell_min_grid(Cg) - (Cj2 * ETA_C ** 2 / 8)[:, None] - EPS          # J x K
gcell = gmin_range(lo, hi)
print('  %d cells on (0, %g]; [%.0fs]' % (K, X, time.time() - t00), flush=True)

def one_body(ylo, yhi):
    tlo, thi = ylo ** 2, yhi ** 2
    ps = np.zeros(K)
    for j in range(1, J + 1):
        c = cjlo[j - 1]; ps += np.where(c < 0, c * thi ** (j - 1), c * tlo ** (j - 1))
    ps -= series_rem(thi)
    return ps, gcell / yhi ** 2

def dp(ylo, yhi, configs, L=None, lam=1.0):
    """L = None: all slack terms kept as in the docstring.  L given (localised slack): the g-terms of a point beyond L
    (its pair with s, and every bond reaching beyond L) are dropped except the cluster part (bond length < 1/2), and the
    tail beyond X uses half-unit bins (two points in a half bin pay g(1/2))"""
    ps, gg = one_body(ylo, yhi); iy2 = lam / yhi ** 2; gg = lam * gg     # lam: fraction of T_g this pair may use
    if L is not None: gg = np.where(hi <= L + 1e-12, gg, 0.0)
    one = {m: m * ps + 4 * m * gg for m in (1, 2)}
    # tail beyond X
    A2, A3 = Btail(yhi)
    if L is None:
        jj = np.arange(int(X), int(X) + 200000, dtype=float); Psi = A2 / jj ** 2 + A3 / jj ** 3
        assert g1 * iy2 >= Psi[0], 'tail bin argument needs min_[0,1] g / y^2 >= sup|psi|'
        T_X = -2 * float(Psi.sum()) - 2 * (A2 / jj[-1] + A3 / jj[-1] ** 2)
    else:
        jj = np.arange(int(2 * X), int(2 * X) + 400000, dtype=float) / 2; Psi = A2 / jj ** 2 + A3 / jj ** 3
        assert float(gmin_range(np.array([0.0]), np.array([0.5]))[0]) * iy2 >= Psi[0]
        T_X = -2 * float(Psi.sum()) - 2 * 2 * (A2 / jj[-1] + A3 / jj[-1] ** 2)
    def pair_g(k, kk):
        dmin = np.maximum(lo[kk] - hi[k], 0.0); dmax = hi[kk] - lo[k]
        if L is None: return gmin_range(dmin, dmax)
        full = gmin_range(dmin, dmax); clus = np.where(dmin < 0.5, gmin_range(dmin, np.minimum(dmax, 0.5)), 0.0)
        return np.where(hi[kk] <= L + 1e-12, full, clus)
    # same-cell pair cost (two points in one cell): 2 m m' g(dist in [0, width]) / y^2
    selfc = {(m, m2): 2 * m * m2 * gmin_range(np.zeros(K), hi - lo) * iy2 for m in (1, 2) for m2 in (1, 2)}
    for m in (1, 2):
        for m2 in (1, 2): assert np.all(selfc[(m, m2)] + one[m2] > 0), 'same-cell loop not positive'
    # backward DP, free
    W = {m: np.full(K, T_X) for m in (1, 2)}; nxt = {m: np.full((K, 2), -1) for m in (1, 2)}
    for k in range(K - 1, -1, -1):
        kk = np.arange(k + 1, K)
        if len(kk):
            gpair = pair_g(k, kk) * iy2
            for m in (1, 2):
                best, arg = W[m][k], (-1, -1)
                for m2 in (1, 2):
                    cand = 2 * m * m2 * gpair + one[m2][kk] + W[m2][kk]; i = int(np.argmin(cand))
                    if cand[i] < best: best, arg = float(cand[i]), (int(kk[i]), m2)
                W[m][k] = best; nxt[m][k] = arg
        for _ in range(2):   # same-cell transitions (positive loops)
            for m in (1, 2):
                for m2 in (1, 2):
                    c = selfc[(m, m2)][k] + one[m2][k] + W[m2][k]
                    if c < W[m][k]: W[m][k] = c; nxt[m][k] = (k, m2)
    st = [(one[m][k] + W[m][k], k, m) for m in (1, 2) for k in range(K)]
    vfree = min(min(st)[0], T_X); vstart = min(st)
    out = {'S0': S0(ylo), 'T_X': T_X, 'Vfree': vfree, 'free_chain': chain(vstart, nxt), 'crowd': {}}
    for (R, d0) in configs:
        # site index for window cells: n if the cell lies in [n - d0, n + d0], 0 if crowded, -1 if outside the window
        site = np.full(K, -1)
        win = hi <= R + 0.5 + 1e-12
        site[win] = 0
        for n in range(1, R + 1):
            ins = (lo >= n - d0 - 1e-12) & (hi <= n + d0 + 1e-12); site[ins] = n
        nwin = int(win.sum()); assert np.all(win[:nwin]) and not np.any(win[nwin:])
        W0 = {m: np.full(nwin, np.inf) for m in (1, 2)}; nx0 = {m: np.full((nwin, 3), -1) for m in (1, 2)}
        for k in range(nwin - 1, -1, -1):
            if site[k] == 0: continue          # never in state 'flag unset' at a crowded cell
            kk = np.arange(k + 1, K); dmin = lo[kk] - hi[k]; dmax = hi[kk] - lo[k]
            gpair = pair_g(k, kk) * iy2
            setf = (site[kk] == 0) | ((site[kk] == site[k]) & (site[k] > 0))
            for m in (1, 2):
                best, arg = np.inf, (-1, -1, -1)
                for m2 in (1, 2):
                    cont = np.where(setf, W[m2][kk], np.concatenate([W0[m2][k + 1:], np.full(K - nwin, np.inf)])[:len(kk)])
                    cand = 2 * m * m2 * gpair + one[m2][kk] + cont; i = int(np.argmin(cand))
                    if cand[i] < best: best, arg = float(cand[i]), (int(kk[i]), m2, int(setf[i]))
                # second point in the same cell (same site window: sets the flag)
                for m2 in (1, 2):
                    c = selfc[(m, m2)][k] + one[m2][k] + W[m2][k]
                    if c < best: best, arg = c, (k, m2, 1)
                W0[m][k] = best; nx0[m][k] = arg
        cands = []
        for k in range(K):
            for m in (1, 2):
                if k < nwin and site[k] == 0: cands.append((one[m][k] + W[m][k], k, m, 1))
                elif k < nwin: cands.append((one[m][k] + W0[m][k], k, m, 0))
        vc = min(cands)
        out['crowd'][(R, d0)] = (vc[0], chain_c(vc, nxt, nx0))
    return out

def chain(start, nxt):
    v, k, m = start; pts = [(k, m)]
    while True:
        k2, m2 = nxt[m][k]
        if k2 < 0 or len(pts) > 60: break
        pts.append((k2, m2)); k, m = k2, m2
    return pts
def chain_c(start, nxt, nx0):
    v, k, m, f = start; pts = [(k, m)]
    while len(pts) < 60:
        if f == 0:
            k2, m2, f2 = nx0[m][k]
        else:
            k2, m2 = nxt[m][k]; f2 = 1
        if k2 < 0: break
        pts.append((k2, m2)); k, m, f = k2, m2, f2
    return pts
def fmt(pts, n=8):
    return ' '.join('%.3f(m%d)' % ((lo[k] + hi[k]) / 2, m) for k, m in pts[:n]) + (' ...' if len(pts) > n else '')

if __name__ == '__main__':
    NY = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    LOCS = [None] + ([float(v) for v in sys.argv[3].split(',')] if len(sys.argv) > 3 else [])
    D0 = (26 / 256, 38 / 256, 52 / 256)
    configs = [(R, d0) for R in (2, 3, 4) for d0 in D0]
    yb = np.linspace(0, 0.4, NY + 1)
    print('crowding DP: %d y-intervals; R in (2,3,4), d0 in %s; bound = certified lower bound of LP/y^2' % (NY, ', '.join('%.4f' % d for d in D0)), flush=True)
    for L in LOCS:
        worst = {c: (np.inf, None) for c in configs}; wfree = (np.inf, None)
        print('== slack %s ==' % ('FULL (all consecutive same-side bonds out to X, pairs with s)' if L is None else 'LOCALISED to [0, %g] (beyond: cluster part only)' % L), flush=True)
        for ylo, yhi in zip(yb[:-1], yb[1:]):
            t1 = time.time(); o = dp(ylo, yhi, configs, L)
            free2 = o['S0'] + 2 * o['Vfree']
            if free2 < wfree[0]: wfree = (free2, (ylo, yhi))
            row = []
            for c in configs:
                v, ch = o['crowd'][c]; lb = o['S0'] + o['Vfree'] + v
                if lb < worst[c][0]: worst[c] = (lb, (ylo, yhi))
                row.append('%+.3f' % lb)
            print('  y in [%.4f, %.4f]: S0 %.3f T_X %+.4f | ALL D: S0 + 2 V_free = %+.4f | crowd (R,d0) %s  [%.0fs]  free chain %s'
                  % (ylo, yhi, o['S0'], o['T_X'], free2, ' '.join(row), time.time() - t1, fmt(o['free_chain'], 5)), flush=True)
        print('  CERTIFIED (slack %s): ALL real D: LP/y^2 >= %+.4f (binding y-interval %s)' % ('full' if L is None else 'localised to %g' % L, wfree[0], wfree[1]), flush=True)
        for c in configs: print('     crowding class R=%d d0=%.4f: c_d >= %+.4f (binding %s)' % (c[0], c[1], worst[c][0], worst[c][1]), flush=True)
    print('total %.0fs' % (time.time() - t00), flush=True)
