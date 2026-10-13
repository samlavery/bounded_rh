"""Round 11 (2), proxy v2: a leaf-count emulation of the sizer's minorant leaf on pair-distance cells.
Cell: gap ranges plus bounds on pair sums.  Leaf test: the LP relaxation
    min  sum_r b_r g_r + sum_t a_t z_t   s.t.  z_t >= lower convex hull of w (64 samples) on the pair's effective range,
                                              s_t = sum_{r in t} g_r within the cell
is >= theta.  Split rule as the sizer's SPLIT=err: the pair with the largest relaxation error a_t (w(s_t*) - z_t*) at the LP point; an
adjacent pair splits its gap, a longer pair splits its effective range.  Not a certificate: hull from samples, float LP.
(subcert.py, the centred second-order test, could not certify even single sizer leaves: the sizer's leaves are wide boxes cut by
pair-sum bounds, and a box-only Taylor test ignores the bounds.)"""
import numpy as np
from scipy.optimize import linprog
NS_HULL = 64
def hull_pieces(wt, lo, hi):
    """(slopes, intercepts) of the lower convex hull of w sampled on [lo, hi]"""
    if hi - lo < 1e-9: v = float(wt(np.array([lo]))[0]); return np.array([0.0]), np.array([v])
    x = np.linspace(lo, hi, NS_HULL); y = wt(x); H = []
    for p in zip(x, y):
        while len(H) >= 2 and (H[-1][0] - H[-2][0]) * (p[1] - H[-2][1]) - (H[-1][1] - H[-2][1]) * (p[0] - H[-2][0]) <= 0: H.pop()
        H.append(p)
    H = np.array(H)
    if len(H) == 1: return np.array([0.0]), H[:, 1]
    s = np.diff(H[:, 1]) / np.diff(H[:, 0]); c = H[:-1, 1] - s * H[:-1, 0]
    return s, c
class SideLP:
    def __init__(self, side, wt):
        self.side = side; self.wt = wt; self.m = side.m; self.P = len(side.tix)
        self.I, self.J, self.a, self.b = side.I, side.J, side.a, side.b
    def hull(self, L, U): return hull_pieces(self.wt, L, U)
    def ranges(self, lo, hi, cons):
        L = np.array([lo[i:j].sum() for i, j in zip(self.I, self.J)]); U = np.array([hi[i:j].sum() for i, j in zip(self.I, self.J)])
        for q, (lb, ub) in cons.items(): L[q] = max(L[q], lb); U[q] = min(U[q], ub)
        return L, U
    def test(self, lo, hi, cons):
        """(LP value or None if empty, LP point g, relaxation errors per pair, ranges)"""
        L, U = self.ranges(lo, hi, cons)
        if np.any(L > U + 1e-12): return None, None, None, (L, U)
        m, P = self.m, self.P; A = []; bu = []; act = [q for q in range(P) if self.a[q] > 0]
        for q in act:
            s, c = self.hull(L[q], U[q])
            for sk, ck in zip(s, c):                       # z_q >= sk s_q + ck   ->   sk s_q - z_q <= -ck
                row = np.zeros(m + P); row[self.I[q]:self.J[q]] = sk; row[m + q] = -1.0; A.append(row); bu.append(-ck)
        for q in range(P):                                 # pair-sum bounds
            if self.J[q] - self.I[q] >= 2:
                row = np.zeros(m + P); row[self.I[q]:self.J[q]] = 1.0; A.append(row); bu.append(U[q]); A.append(-row); bu.append(-L[q])
        cost = np.concatenate([self.b, self.a]); bnds = list(zip(lo, hi)) + [(None, None) if self.a[q] > 0 else (0, 0) for q in range(P)]
        r = linprog(cost, A_ub=np.array(A) if A else None, b_ub=np.array(bu) if bu else None, bounds=bnds, method='highs')
        if r.status == 2: return None, None, None, (L, U)
        if r.status != 0: return -np.inf, None, None, (L, U)
        g = r.x[:m]; z = r.x[m:]; p = np.concatenate([[0.0], np.cumsum(g)]); s_ = p[self.J] - p[self.I]
        err = self.a * (self.wt(s_) - z)
        return float(r.fun), g, err, (L, U)
    PFK = 1
    def children(self, lo_, hi_, cs, q, L, U):
        if self.J[q] - self.I[q] == 1:
            r = self.I[q]; mid = (lo_[r] + hi_[r]) / 2
            h1 = hi_.copy(); h1[r] = mid; l2 = lo_.copy(); l2[r] = mid
            return (lo_, h1, cs), (l2, hi_, cs)
        mid = (L[q] + U[q]) / 2; c1 = dict(cs); c1[q] = (L[q], mid); c2 = dict(cs); c2[q] = (mid, U[q])
        return (lo_, hi_, c1), (lo_, hi_, c2)
    def count(self, lo, hi, cons, theta, cap=20000, minw=2.0 ** -14):
        """leaves of the emulated bisection certifying side >= theta on the cell; (cap, False) if over the cap.
        PFK > 1: the sizer's pf rule -- the PFK largest-error axes are tried and the split whose worse child has the larger LP value wins."""
        if self.m == 0: return 0, True
        stack = [(np.array(lo, float), np.array(hi, float), dict(cons), None)]; leaves = 0; work = 0
        while stack:
            lo_, hi_, cs, tr = stack.pop(); work += 1
            if work > 4 * cap: return cap, False
            v, g, err, (L, U) = tr if tr is not None else self.test(lo_, hi_, cs)
            if v is None: continue                        # empty
            if v >= theta: leaves += 1; continue
            if leaves + len(stack) >= cap: return cap, False
            order = list(np.argsort(-err)) if err is not None else list(np.argsort(-(U - L)))
            order = [q for q in order if U[q] - L[q] >= minw]
            if not order: return cap, False
            best = None
            for q in order[:max(1, self.PFK)]:
                A, B = self.children(lo_, hi_, cs, q, L, U)
                if self.PFK == 1: best = (0, A + (None,), B + (None,)); break
                tA = self.test(*A); tB = self.test(*B)
                sc = min(np.inf if tA[0] is None else tA[0], np.inf if tB[0] is None else tB[0])
                if best is None or sc > best[0]: best = (sc, A + (tA,), B + (tB,))
            stack.append(best[1]); stack.append(best[2])
        return leaves, True

# ---- engine-like minorants (closer to the sizer's leaf): per pair only the zero-order bound min w on the range and tangents at
# 9 points of the range corrected by the mean-value term R(q) = max((U-q)(w'(q) - min w' on [q,U])^+, (q-L)(max w' on [L,q] - w'(q))^+).
class RangeTab:
    """range min / max of a sampled function by blocks of 64 and a sparse table on the block extrema"""
    def __init__(self, x, y, B=64):
        self.x0, self.dx, self.y, self.B = x[0], x[1] - x[0], y, B
        nb = len(y) // B; self.nb = nb; Y = y[:nb * B].reshape(nb, B)
        self.mn = [Y.min(1)]; self.mx = [Y.max(1)]
        while 2 ** len(self.mn) <= nb:
            k = 2 ** (len(self.mn) - 1); self.mn.append(np.minimum(self.mn[-1][:-k], self.mn[-1][k:])); self.mx.append(np.maximum(self.mx[-1][:-k], self.mx[-1][k:]))
    def q(self, lo, hi):
        i = max(0, int(np.floor((lo - self.x0) / self.dx))); j = min(len(self.y) - 1, int(np.ceil((hi - self.x0) / self.dx)))
        bi, bj = (i + self.B - 1) // self.B, j // self.B           # whole blocks bi..bj-1
        if bj <= bi: seg = self.y[i:j + 1]; return float(seg.min()), float(seg.max())
        mn = min(self.y[i:bi * self.B + 1].min(), self.y[bj * self.B:j + 1].min()); mx = max(self.y[i:bi * self.B + 1].max(), self.y[bj * self.B:j + 1].max())
        k = int(np.log2(bj - bi)); mn = min(mn, self.mn[k][bi], self.mn[k][bj - 2 ** k]); mx = max(mx, self.mx[k][bi], self.mx[k][bj - 2 ** k])
        return float(mn), float(mx)
class SideEng(SideLP):
    NT = 9
    def __init__(self, side, xt, w, w1):
        super().__init__(side, lambda x: np.interp(x, xt, w)); self.w1f = lambda x: np.interp(x, xt, w1)
        self.TW = RangeTab(xt, w); self.TD = RangeTab(xt, w1)
    def test(self, lo, hi, cons):
        L, U = self.ranges(lo, hi, cons)
        if np.any(L > U + 1e-12): return None, None, None, (L, U)
        m, P = self.m, self.P; A = []; bu = []
        for q in range(P):
            if self.a[q] <= 0: continue
            def add(sk, ck):
                row = np.zeros(m + P); row[self.I[q]:self.J[q]] = sk; row[m + q] = -1.0; A.append(row); bu.append(-ck)
            add(0.0, self.TW.q(L[q], U[q])[0])
            if U[q] - L[q] > 1e-12:
                for p in np.linspace(L[q], U[q], self.NT):
                    v = float(self.wt(np.array([p]))[0]); d = float(self.w1f(np.array([p]))[0])
                    R = max((U[q] - p) * max(0.0, d - self.TD.q(p, U[q])[0]), (p - L[q]) * max(0.0, self.TD.q(L[q], p)[1] - d))
                    add(d, v - d * p - R)
        for q in range(P):
            if self.J[q] - self.I[q] >= 2:
                row = np.zeros(m + P); row[self.I[q]:self.J[q]] = 1.0; A.append(row); bu.append(U[q]); A.append(-row); bu.append(-L[q])
        cost = np.concatenate([self.b, self.a]); bnds = list(zip(lo, hi)) + [(None, None) if self.a[q] > 0 else (0, 0) for q in range(P)]
        r = linprog(cost, A_ub=np.array(A), b_ub=np.array(bu), bounds=bnds, method='highs')
        if r.status == 2: return None, None, None, (L, U)
        if r.status != 0: return -np.inf, None, None, (L, U)
        g = r.x[:m]; z = r.x[m:]; p_ = np.concatenate([[0.0], np.cumsum(g)]); s_ = p_[self.J] - p_[self.I]
        return float(r.fun), g, self.a * (self.wt(s_) - z), (L, U)

class SideHull(SideLP):
    """SideLP with a VALID convex minorant: the lower hull of the step function of cell minima of w (<= 128 cells per range), memoised"""
    def __init__(self, side, xt, w):
        super().__init__(side, lambda x: np.interp(x, xt, w)); self.x0, self.dx, self.wg = xt[0], xt[1] - xt[0], w
        self.HC = {}
    def hull(self, L, U):
        i = max(0, int(np.floor((L - self.x0) / self.dx))); j = min(len(self.wg) - 1, int(np.ceil((U - self.x0) / self.dx)))
        if j <= i: v = float(self.wg[i]); return np.array([0.0]), np.array([v])
        key = (i, j)
        if key in self.HC: return self.HC[key]
        k = max(1, -(-(j - i) // 128)); seg = self.wg[i:j + 1]; nc = -(-len(seg) // k)
        seg = np.concatenate([seg, np.full(nc * k - len(seg), np.inf)]).reshape(nc, k).min(1)
        xs = self.x0 + self.dx * (i + k * np.arange(nc + 1)); xs[-1] = max(xs[-1], U)
        X = np.repeat(xs, 2)[1:-1]; Y = np.repeat(seg, 2); H = []
        for p in zip(X, Y):
            while len(H) >= 2 and (H[-1][0] - H[-2][0]) * (p[1] - H[-2][1]) - (H[-1][1] - H[-2][1]) * (p[0] - H[-2][0]) <= 0: H.pop()
            H.append(p)
        H = np.array(H)
        if len(H) == 1: return np.array([0.0]), H[:, 1]
        dxh = np.diff(H[:, 0]); ok = dxh > 1e-15; sl = np.diff(H[:, 1])[ok] / dxh[ok]; c = H[:-1, 1][ok] - sl * H[:-1, 0][ok]
        out = (sl, c) if len(sl) else (np.array([0.0]), np.array([H[:, 1].min()]))
        if len(self.HC) < 2000000: self.HC[key] = out
        return out
