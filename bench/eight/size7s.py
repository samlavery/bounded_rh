"""Integer-faithful sizing of the seven-point (Q = 6) certificate with
  Z : the zero-order pyramid test;
  S : the slope test at a point q of the box: per pair term either the zero-order bound or the expansion
        w(s) >= w(q_t) + w'(q_t)(s - q_t) - R_t,   R_t = max((hi_t - q_t)(w'(q_t) - min w' on [q_t, hi_t])^+,
                                                           (q_t - lo_t)(max w' on [lo_t, q_t] - w'(q_t))^+),
      the linear part summed per gap as in the mean-value test; q_r from a 2-bit mode per gap (lower end, upper
      end, centre, each aligned to 2^JCQ), the expansion set T from 21 bits;
  B : basin leaves (inside a basin box certified once by the slope test at an explicit q).
Tables: the w pyramid (zero-order terms), the derivative pair pyramid (half-interval slope bounds), point values of w
and of w' at the expansion points (degenerate integer cells).  After the bisection every leaf is re-decided on the
built tables (fix-up)."""
import os, sys, time, itertools, math
from functools import lru_cache
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
for p in (HERE, os.path.join(HERE, "..", "pyr"), os.path.join(HERE, "..", "mvt")):
    sys.path.insert(0, p)
sys.setrecursionlimit(1000000)
from size_pyr import phase1, SA, SC, QUARTER, WFRAC
from pyr_table import Pyr
from wz import WZ, SW
from w1cell import fP, fM, U1, KU1
from size_m import PyrF
from sevenw import w as wf, w1 as w1f

Q = 7
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
NP = len(PAIRS)
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]
INC = np.zeros((NP, Q))
for t, (i, j) in enumerate(PAIRS): INC[t, i:j] = 1.0
U = 10**10; RU = U // U1
M32 = (1 << 32) - 1

# ---------------- float helpers (steering only) ----------------
XM = 80 * SC
_xs = np.arange(XM + 2) / SC
_W = wf(_xs); _W1 = w1f(_xs)
BLK = 256
def _blk(arr, f):
    nb = len(arr) // BLK + 1; p = np.pad(arr, (0, nb * BLK - len(arr)), mode='edge'); return f(p.reshape(nb, BLK), axis=1)
_B = {'w': (_W, np.min, _blk(_W, np.min)), 'lo': (_W1, np.min, _blk(_W1, np.min)), 'hi': (_W1, np.max, _blk(_W1, np.max))}
def frq(key, lo, hi):
    arr, f, bb = _B[key]
    lo = max(lo, 0); hi = min(hi, XM); lo = min(lo, hi)
    if hi - lo < 4 * BLK: return float(f(arr[lo:hi + 1]))
    A = -(-lo // BLK); Bq = (hi + 1) // BLK
    parts = [arr[lo:A * BLK], bb[A:Bq], arr[Bq * BLK:hi + 1]]
    return float(f(np.concatenate([p for p in parts if len(p)])))

def make_q(JCQ):
    """the expansion point of a gap from its mode, exactly as the Lean `dec` (multiples of 2^JCQ, else of 16)"""
    A = 1 << JCQ
    def dec(mode, l, u):
        if mode == 0:
            m = ((l + A - 1) >> JCQ) << JCQ
            if m <= u: return m
            m2 = ((l + 15) >> 4) << 4; return m2 if m2 <= u else l
        if mode == 1:
            m = (u >> JCQ) << JCQ
            if m >= l: return m
            m2 = (u >> 4) << 4; return m2 if m2 >= l else u
        c = (l + u) >> 1; mm = (c >> JCQ) << JCQ
        if mm >= l: return mm
        c2 = (c >> 4) << 4; return c2 if c2 >= l else c
    return dec

def wcell(a, b): return WZ(a, b) * U // SW
def lb3_of(lb, SH, MINW):
    """the three-piece read min(lb[lo, lo + a], lb[lo + a, hi - a], lb[hi - a, hi]), a = (hi - lo) >> SH, for
    hi - lo >= MINW (else lb[lo, hi]): the middle read's overhang stays inside [lo, hi]"""
    cache = {}
    def lb3(lo, hi):
        k = (lo, hi); v = cache.get(k)
        if v is not None: return v
        w = hi - lo
        if w < MINW: v = lb(lo, hi)
        else:
            a = w >> SH; v = min(lb(lo, lo + a), lb(lo + a, hi - a), lb(hi - a, hi))
        cache[k] = v
        return v
    return lb3
def pieces(lo, hi, SH, MINW):
    w = hi - lo
    if w < MINW: return [(lo, hi)]
    a = w >> SH; return [(lo, lo + a), (lo + a, hi - a), (hi - a, hi)]

def run(cN, aN, bN, JCQ=8, dmin=5, PED=4, basins=(), verbose=True, max_leaves=4 * 10**6, WF=WFRAC, WMIN=6, SH=4, MINW=1024, probe=False, DFUEL=14, DLO=None, DHI=None, XD=81920, regions=(), centers=(), CRAD=0.25, FACE=False, TAILCUT=None, DUMP=None, SECOND=None, TRUEMIN=False, QOPT=False, MTEST=0, NPT=9, MLOG=None):
    t0 = time.time()
    a = np.array(aN, float) / SA; b = np.array(bN, float) / SA
    P = PyrF(wcell, dmin=WMIN, PE=5, PB=10, MAXA=4, U=U, FUEL=14)
    PP = PyrF(fP, dmin=dmin, PE=PED, PB=10, MAXA=4, U=U1, FUEL=DFUEL)
    PM = PyrF(fM, dmin=dmin, PE=PED, PB=10, MAXA=4, U=U1, FUEL=DFUEL)
    DENSE = DLO is not None
    def dres(i, l):
        """the dense derivative table's finest level in the block of the level-l cell i"""
        return DLO if ((i << l) < XD) else DHI
    EMX = P.EM
    adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
    S = [-(-(4 * cN * SC) // (bN[r] * 4 * QUARTER)) * QUARTER for r in range(Q)]
    covers = [phase1(cN, adj[r], S[r]) for r in range(Q)]
    bads = [cv[1] for cv in covers]
    dec = make_q(JCQ)
    CSU = cN * SC * U
    LONG = [TAILCUT is not None and (j - i) >= TAILCUT for (i, j) in PAIRS]
    LONGMASK = sum(1 << t for t in range(NP) if LONG[t])
    nface = [0, 0]
    @lru_cache(maxsize=None)
    def E(l, i):
        if l < WMIN: return E(WMIN, i >> (WMIN - l))
        if l <= WMIN: return min(WZ(i << l, (i + 1) << l) * U // SW, EMX)
        return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
    @lru_cache(maxsize=None)
    def EP(l, i):
        if DENSE and l <= 10:
            R = dres(i, l)
            if l < R: return EP(R, i >> (R - l))
            if l == R: return min(fP(i << l, (i + 1) << l), EMX)
            return min(EP(l - 1, 2 * i), EP(l - 1, 2 * i + 1))
        if DENSE: return min(EP(l - 1, 2 * i), EP(l - 1, 2 * i + 1))
        if l < dmin: return EP(dmin, i >> (dmin - l))
        if l <= 13: return min(fP(i << l, (i + 1) << l), EMX)
        return min(EP(l - 1, 2 * i), EP(l - 1, 2 * i + 1))
    @lru_cache(maxsize=None)
    def EMd(l, i):
        if DENSE and l <= 10:
            R = dres(i, l)
            if l < R: return EMd(R, i >> (R - l))
            if l == R: return min(fM(i << l, (i + 1) << l), EMX)
            return min(EMd(l - 1, 2 * i), EMd(l - 1, 2 * i + 1))
        if DENSE: return min(EMd(l - 1, 2 * i), EMd(l - 1, 2 * i + 1))
        if l < dmin: return EMd(dmin, i >> (dmin - l))
        if l <= 13: return min(fM(i << l, (i + 1) << l), EMX)
        return min(EMd(l - 1, 2 * i), EMd(l - 1, 2 * i + 1))
    def mk(Ef, X):
        @lru_cache(maxsize=None)
        def lbq(lo, hi):
            cv = X.cover(lo, hi)
            if not cv or cv[-1] is None: return 0
            return min(Ef(l, i) for (l, i) in cv)
        return lbq
    lbE1 = mk(E, P); lbE, lbPE, lbME = lb3_of(lbE1, SH, MINW), mk(EP, PP), mk(EMd, PM)
    @lru_cache(maxsize=None)
    def ptw(x): return min(WZ(x, x) * U // SW, EMX)
    @lru_cache(maxsize=None)
    def ptd(x): return (min(fP(x, x), EMX), min(fM(x, x), EMX))
    def inbas(box):
        for bb in basins:
            if all(bb[r][0] <= box[r][0] and box[r][1] <= bb[r][1] for r in range(Q)): return True
        return False
    def iv(box):
        return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
    def zlow(box, lb):
        tot = U * sum(bN[r] * box[r][0] for r in range(Q)); s = 0
        for t, (lo, hi) in enumerate(iv(box)):
            if not LONG[t]: s += aN[t] * lb(lo, hi)
        return tot + s * SC
    NEG = -(1 << 200)
    RGK = {}
    for (a_, b_) in regions:
        k_ = (a_ + 16384) >> 15
        if k_ < 16: RGK[k_] = (a_, b_)
    def inreg(lo, hi):
        """exactly as the Lean `inRg`: the region of the integer nearest to lo"""
        k_ = (lo + 16384) >> 15
        if k_ >= 16 or k_ not in RGK: return False
        a_, b_ = RGK[k_]
        return a_ <= lo and hi <= b_
    def sint(box, q, T, lbw, lbP, lbM, pw, pd):
        """the integer slope test (value comparable to CSU), exactly as the Lean `ctest`"""
        if any(not (box[r][0] <= q[r] <= box[r][1]) for r in range(Q)): return NEG
        T &= ~LONGMASK
        I = iv(box); lhs_t = 0; Rsum = 0
        Pt = [0] * NP; Mt = [0] * NP
        for t, (i, j) in enumerate(PAIRS):
            lo, hi = I[t]
            if T >> t & 1:
                qt = sum(q[i:j]); p, m = pd(qt)
                if p < 1 or m < 1: return NEG
                Pt[t] = p; Mt[t] = m
                if inreg(lo, hi):
                    lhs_t += aN[t] * pw(qt); continue
                up = dn = 0
                if hi > qt:
                    e = lbP(qt, hi)
                    if e < 1: return NEG
                    up = (hi - qt) * max(0, 4 * U1 - m - e)
                if qt > lo:
                    e = lbM(lo, qt)
                    if e < 1: return NEG
                    dn = (qt - lo) * max(0, 4 * U1 - e - p)
                Rsum += aN[t] * max(up, dn)
                lhs_t += aN[t] * pw(qt)
            elif not LONG[t]:
                lhs_t += aN[t] * lbw(lo, hi)
        pen = 0
        for r in range(Q):
            AT = sum(aN[t] for t in TS[r] if T >> t & 1)
            Pos = max(0, U1 * bN[r] + KU1 * AT - sum(aN[t] * Mt[t] for t in TS[r] if T >> t & 1))
            Neg = max(0, KU1 * AT - U1 * bN[r] - sum(aN[t] * Pt[t] for t in TS[r] if T >> t & 1))
            pen += (q[r] - box[r][0]) * Pos + (box[r][1] - q[r]) * Neg
        return U * sum(bN[r] * q[r] for r in range(Q)) + SC * lhs_t - RU * (pen + Rsum)
    def sfloat(box, q, passes=2):
        """float steering: expansion set at q by passes of single-term switches; returns (value, T)"""
        qq = np.array(q, float) / SC
        lo = np.array([x[0] for x in box]) / SC - qq; hi = np.array([x[1] for x in box]) / SC - qq
        I = iv(box); sq = INC @ qq; wq = wf(sq); w1q = w1f(sq)
        w0 = np.array([frq('w', l, h) for l, h in I]); pen = np.zeros(NP)
        for t, (i, j) in enumerate(PAIRS):
            l_, h_ = I[t]; qt = sum(q[i:j]); up = dn = 0.0
            if h_ > qt: up = max(0.0, w1q[t] - frq('lo', qt, h_)) * (h_ - qt) / SC
            if qt > l_: dn = max(0.0, frq('hi', l_, qt) - w1q[t]) * (qt - l_) / SC
            pen[t] = 0.0 if inreg(l_, h_) else max(up, dn)
        tay = a * (wq - pen); zer = a * w0; slope = a * w1q
        LM = np.array(LONG, bool); tay = np.where(LM, 0.0, tay); zer = np.where(LM, 0.0, zer)
        use = ~LM
        def total(use):
            g = b + INC.T @ (slope * use)
            return float(b @ qq + np.minimum(g * lo, g * hi).sum() + np.where(use, tay, zer).sum())
        cur = total(use)
        for _ in range(passes):
            changed = False
            for t in np.argsort(-pen):
                if LM[t]: continue
                use[t] = not use[t]; v = total(use)
                if v > cur: cur = v; changed = True
                else: use[t] = not use[t]
            if not changed: break
        return cur, sum(1 << t for t in range(NP) if use[t])
    CEN = [list(c_) for c_ in centers]
    if QOPT:
        from scipy.optimize import minimize as _minimize2
        from sevenw import Fun as _Fun2
        _F2 = _Fun2(a, b)
    def qopt_modes(box):
        """3-bit positions per gap of the box minimiser of G (local descent from the centre)"""
        lo = np.array([x[0] for x in box]) / SC; hi = np.array([x[1] for x in box]) / SC
        r_ = _minimize2(_F2.vg, (lo + hi) / 2, jac=True, method='L-BFGS-B', bounds=list(zip(lo, hi)))
        ks = []
        for k in range(Q):
            wd = hi[k] - lo[k]
            ks.append(0 if wd <= 0 else int(round((r_.x[k] - lo[k]) / wd * 7)))
        return ('Q', tuple(ks))
    def qof(modes, box):
        """the expansion point of a slope leaf: per-gap modes, or ('C', k): the centre k clamped to the box"""
        if modes[0] == 'Q':
            out = []
            for r in range(Q):
                l_, u_ = box[r]; x_ = l_ + ((u_ - l_) * modes[1][r]) // 7; xa = (x_ >> 4) << 4
                out.append(xa if xa >= l_ else x_)
            return out
        if modes[0] == 'C':
            c_ = CEN[modes[1]]; out = []
            for r in range(Q):
                l_, u_ = box[r]; la = ((l_ + 15) >> 4) << 4; ua = (u_ >> 4) << 4
                out.append(min(max(c_[r], la), ua) if la <= ua else min(max(c_[r], l_), u_))
            return out
        return [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
    def near_center(box):
        if not CEN: return None
        best = None
        for k_, c_ in enumerate(CEN):
            dd = max(max(box[r][0] - c_[r], c_[r] - box[r][1], 0) for r in range(Q))
            if best is None or dd < best[0]: best = (dd, k_)
        return best[1] if best[0] <= CRAD * SC else None
    def scands(box):
        cen = [(x[0] + x[1]) / 2 / SC for x in box]
        g = b + INC.T @ (a * w1f(INC @ np.array(cen)))
        m1 = tuple(0 if g[r] >= 0 else 1 for r in range(Q)); m2 = (2,) * Q
        out = []
        cands = [m1, m2]
        k_ = near_center(box)
        if k_ is not None: cands.append(('C', k_))
        if QOPT: cands.append(qopt_modes(box))
        for modes in cands:
            q = qof(modes, box)
            v, T = sfloat(box, q); out.append((v, modes, q, T))
        out.sort(key=lambda z: -z[0])
        return out
    cF = cN / SA
    def flower(box):
        if inbas(box): return cF
        zf = sum(b[r] * box[r][0] / SC for r in range(Q)) + sum(a[t] * frq('w', l, h) for t, (l, h) in enumerate(iv(box)) if not LONG[t])
        if zf >= cF: return zf
        if SECOND:
            v2 = second(box)
            if v2 >= cF: return v2
        cen = [(x[0] + x[1]) / 2 / SC for x in box]
        g = b + INC.T @ (a * w1f(INC @ np.array(cen)))
        best = zf
        cands = [tuple(0 if g[r] >= 0 else 1 for r in range(Q)), (2,) * Q]
        k_ = near_center(box)
        if k_ is not None: cands.append(('C', k_))
        if QOPT: cands.append(qopt_modes(box))
        for modes in cands:
            q = qof(modes, box)
            best = max(best, sfloat(box, q, passes=1)[0])
        return best
    count = [0, 0, 0, 0, 0, 0, 0]
    def choose(box):
        wd = [x[1] - x[0] for x in box]; mw = max(wd); best = None
        for k in range(Q):
            if wd[k] == 0 or wd[k] * WF < mw: continue
            mid = (box[k][0] + box[k][1]) // 2
            A_ = list(box); A_[k] = (box[k][0], mid); B_ = list(box); B_[k] = (mid, box[k][1])
            la, lb_ = flower(tuple(A_)), flower(tuple(B_))
            sc = ((la >= cF) + (lb_ >= cF), la + lb_)
            if best is None or sc > best[0]: best = (sc, k)
        return best[1]
    if SECOND:
        _xs2 = np.arange(XM + 2) / SC; _W2 = (w1f(_xs2 + 1e-6) - w1f(_xs2 - 1e-6)) / 2e-6
        _B2 = _blk(_W2, np.min)
        def w2min(lo, hi):
            lo = max(lo, 0); hi = min(hi, XM); lo = min(lo, hi)
            if hi - lo < 4 * BLK: return float(_W2[lo:hi + 1].min())
            A = -(-lo // BLK); Bq = (hi + 1) // BLK
            parts = [_W2[lo:A * BLK], _B2[A:Bq], _W2[Bq * BLK:hi + 1]]
            return float(np.min(np.concatenate([p_ for p_ in parts if len(p_)])))
    def second(box):
        """float second-order test at the box centre: G(q) + sum_r min (g_r d + lam d^2 / 2), lam <= lambda_min of
        sum_t a_t l_t e_t e_t^T with l_t = min w'' on the term's range (SECOND = 'eig' exact, 'gersh' Gershgorin)"""
        qq = np.array([(x[0] + x[1]) / 2 for x in box]) / SC
        lo = np.array([x[0] for x in box]) / SC - qq; hi = np.array([x[1] for x in box]) / SC - qq
        I = iv(box); l_ = np.array([w2min(a_, b_) for a_, b_ in I])
        M = INC.T @ np.diag(a * l_) @ INC
        if SECOND == 'eig': lam = float(np.linalg.eigvalsh(M)[0])
        else: lam = float(min(M[r, r] - (np.abs(M[r]).sum() - abs(M[r, r])) for r in range(Q)))
        sq = INC @ qq; G0 = float(b @ qq + a @ wf(sq)); g = b + INC.T @ (a * w1f(sq))
        tot = G0
        for r in range(Q):
            cands = [lo[r], hi[r]]
            if lam > 0:
                dstar = -g[r] / lam
                if lo[r] < dstar < hi[r]: cands.append(dstar)
            tot += min(g[r] * d_ + 0.5 * lam * d_ * d_ for d_ in cands)
        return tot
    if TRUEMIN:
        from scipy.optimize import minimize as _minimize
        from sevenw import Fun as _Fun
        _F = _Fun(a, b); _rng = np.random.default_rng(3)
        def truemin(box):
            lo = np.array([x[0] for x in box]) / SC; hi = np.array([x[1] for x in box]) / SC
            X = lo + (hi - lo) * _rng.random((300, Q)); X = np.vstack([X, (lo + hi) / 2, lo, hi])
            v = _F.val(X); i0 = int(np.argmin(v))
            r_ = _minimize(_F.vg, X[i0], jac=True, method='L-BFGS-B', bounds=list(zip(lo, hi)))
            return min(float(v[i0]), float(r_.fun))
    if MTEST:
        from scipy.optimize import linprog as _linprog
        _xsc = np.arange(0, 80 * SC + 2) / SC; _w2c = (w1f(_xsc + 1e-6) - w1f(_xsc - 1e-6)) / 2e-6
        _cc = np.concatenate([[0], np.cumsum(_w2c > 0)])
        def in_concave(p1, p2): return p2 + 1 < len(_cc) and _cc[p2 + 1] - _cc[p1] == 0
    mstat = [0, 0, 0]; MST = {}
    GS = int(os.environ.get("GSH", "8")); GM = (1 << GS) - 1
    TWOGRID = os.environ.get("TWOGRID") == "1"
    GRIDS = [0, 1] if TWOGRID else [0]
    MPASS = [[0], [0, 1]] if TWOGRID else [[0]]
    REGL = sorted(regions)
    RGK2 = {}
    for (za_, zb_) in REGL:
        k_ = (za_ + 16384) >> 15
        if k_ < 16: RGK2[k_] = (za_, zb_)
    def mcands(lo, hi, lbw, lbP, lbM, pw, pd):
        """certifiable minorants of w on [lo, hi] / SC as (alpha*U, d*U1, p): w(s) >= (alpha + d (s - p/SC)) on the range;
        the constant lb, and lines through (p, w(p)) (p on the 256-grid) with slope dR = min w' on [p, hi] or
        dL = max w' on [lo, p] (table bounds) when dL <= dR"""
        if os.environ.get("MREG") == "3":
            # as MREG=2 with the Lean semantics: p = clamp(((lo + (hi - lo) j / 8) >> 8) << 8, ga, gb), region of the
            # integer nearest to p, candidates carry (v, dmid, p, j, P, M)
            out = [(lbw(lo, hi), 0, lo, None, 0, 0)]
            if hi - lo < 64: return out
            seen = set()
            for jj in [j + 16 * f_ for f_ in GRIDS for j in range(9)]:
                p = gpt(lo, hi, jj)
                if p is None or p in seen: continue
                seen.add(p)
                j = jj
                k = (p + 16384) >> 15
                if k >= 16 or k not in RGK2: continue
                za, zb = RGK2[k]
                if not (za <= p <= zb): continue
                P_, M_ = pd(p)
                if P_ < 1 or M_ < 1: continue
                if hi > zb:
                    e = lbP(zb, hi)
                    if e < 1 or e + M_ < 2 * KU1: continue
                if lo < za:
                    e = lbM(lo, za)
                    if e < 1 or e + P_ < 2 * KU1: continue
                out.append((pw(p), (P_ - M_) // 2, p, j, P_, M_))
            return out
        if os.environ.get("MREG") == "2":
            # extended tangents: at a 256-grid point p inside a convex region [za, zb], valid on [lo, hi] when the
            # derivative table bounds w' >= w'(p) on [zb, hi] and w' <= w'(p) on [lo, za] (strictly, slack allowed)
            out = [(lbw(lo, hi), 0, lo)]
            if hi - lo < 64: return out
            ga = ((lo + 255) >> 8) << 8; gb = (hi >> 8) << 8
            if ga > gb: return out
            pts = sorted({min(gb, max(ga, ((lo + (hi - lo) * j // (NPT - 1)) >> 8) << 8)) for j in range(NPT)})
            for p in pts:
                rg = next(((za, zb) for (za, zb) in REGL if za <= p <= zb), None)
                if rg is None: continue
                za, zb = rg
                P_, M_ = pd(p)
                if P_ < 1 or M_ < 1: continue
                if hi > zb:
                    e = lbP(zb, hi)
                    if e < 1 or e - KU1 < KU1 - M_: continue
                if lo < za:
                    e = lbM(lo, za)
                    if e < 1 or KU1 - e > P_ - KU1: continue
                out.append((pw(p), (P_ - M_) // 2, p))
            p1 = (lo >> 8) << 8; p2 = ((hi + 255) >> 8) << 8
            if p2 > p1 and in_concave(p1, p2) and not os.environ.get("NOCHORD"):
                w1_ = float(wf(p1 / SC)); w2_ = float(wf(p2 / SC)); dd = (w2_ - w1_) / ((p2 - p1) / SC)
                out.append((w1_ * U - 1, dd * U1, p1))
            return out
        if os.environ.get("MREG"):
            # region-certified minorants: the constant (pyramid), tangents at 256-grid points when the range lies in a
            # convex region, the secant between the 256-grid points around the range when that lies in a concave region
            out = [(lbw(lo, hi), 0, lo)]
            if hi - lo < 64: return out
            if inreg(lo, hi):
                ga = ((lo + 255) >> 8) << 8; gb = (hi >> 8) << 8
                if ga <= gb:
                    pts = sorted({min(gb, max(ga, ((lo + (hi - lo) * j // (NPT - 1)) >> 8) << 8)) for j in range(NPT)})
                    for p in pts:
                        P_, M_ = pd(p)
                        if P_ < 1 or M_ < 1: continue
                        out.append((pw(p), (P_ - M_) // 2, p))
            else:
                p1 = (lo >> 8) << 8; p2 = ((hi + 255) >> 8) << 8
                if p2 > p1 and in_concave(p1, p2):
                    w1_ = float(wf(p1 / SC)); w2_ = float(wf(p2 / SC)); dd = (w2_ - w1_) / ((p2 - p1) / SC)
                    out.append((w1_ * U - 1, dd * U1, p1))
            return out
        if os.environ.get("MEXACT"):
            ed = float(os.environ.get("MEPSD", "0")) * U1; ew = float(os.environ.get("MEPSW", "0")) * U
            out = [(frq('w', lo, hi) * U - ew, 0, lo)]
            if hi - lo < 64: return out
            for p in sorted({lo + (hi - lo) * j // (NPT - 1) for j in range(NPT)}):
                dR = (frq('lo', p, hi) * U1 - ed) if hi > p else 10 ** 18
                dL = (frq('hi', lo, p) * U1 + ed) if p > lo else -10 ** 18
                if dL > dR: continue
                for dd in {max(dL, -10 ** 12), min(dR, 10 ** 12)}: out.append((float(wf(p / SC)) * U - ew, dd, p))
            return out
        out = [(lbw(lo, hi), 0, lo)]
        if hi - lo < 64: return out
        ga = ((lo + 255) >> 8) << 8; gb = (hi >> 8) << 8
        if gb < ga: return out
        pts = sorted({min(gb, max(ga, ((lo + (hi - lo) * j // (NPT - 1)) >> 8) << 8)) for j in range(NPT)})
        for p in pts:
            P_, M_ = pd(p)
            if P_ < 1 or M_ < 1: continue
            dR = (lbP(p, hi) - KU1) if hi > p else None
            dL = (KU1 - lbM(lo, p)) if p > lo else None
            if hi > p and lbP(p, hi) < 1: continue
            if p > lo and lbM(lo, p) < 1: continue
            if dR is None: dR = 10 ** 18
            if dL is None: dL = -10 ** 18
            if dL > dR: continue
            for dd in {max(dL, -10 ** 12), min(dR, 10 ** 12)}:
                out.append((pw(p), dd, p))
        return out
    def gpt(L, U_, jj):
        """the Lean `gptG` (TWOGRID: `gptF`, bit 4 of jj selects the fine grid 2^GS, else the 2^8 grid); None when
        the grid has no point in [L, U] (the clamp then leaves the range and the Lean test fails)"""
        gs = (GS if jj >> 4 else 8) if TWOGRID else GS; j = jj & 15
        gm = (1 << gs) - 1
        ga = ((L + gm) >> gs) << gs; gb = (U_ >> gs) << gs; x = ((L + (((U_ - L) * j) >> 3)) >> gs) << gs
        r = ga if x <= ga else (gb if gb <= x else x)
        return r if ga <= gb else (r if L <= r <= U_ else None)
    def tchk(L, U_, p, lbP, lbM, pd, Q_=None):
        k = (p + 16384) >> 15
        if k >= 16 or k not in RGK2: return False
        za, zb = RGK2[k]
        if not (za <= p <= zb and L <= p <= U_): return False
        P_, M_ = pd(p)
        if P_ < 1 or M_ < 1: return False
        if U_ > zb:
            if Q_ is not None: Q_['d'].add((zb, U_))
            e = lbP(zb, U_)
            if e < 1 or e + M_ < 4 * U1: return False
        if L < za:
            if Q_ is not None: Q_['d'].add((L, za))
            e = lbM(L, za)
            if e < 1 or e + P_ < 4 * U1: return False
        return True
    def mweights(kap, lam):
        if kap == 1: return 0, 1024, 0
        if kap == 2: return 1024 - lam, lam, 0
        if kap == 3: return 0, 1024 - lam, lam
        return 1024, 0, 0
    def meval(box, mc, lbw, lbP, lbM, pw, pd, Q_=None):
        """the Lean `mscheck` on the certificate mc[t] = (kappa, j1, j2, lam) (active terms)"""
        I = iv(box); lhs = 1024 * U * sum(bN[r] * box[r][0] for r in range(Q)); rhs = 1024 * cN * SC * U
        SL = [1024 * U1 * bN[r] for r in range(Q)]; SK = [0] * Q
        for t, (i, j) in enumerate(PAIRS):
            if aN[t] == 0: continue
            L, U_ = I[t]; kap, j1, j2, lam = mc[t]
            if lam > 1024: return False
            c_, l1, l2 = mweights(kap, lam); p1 = gpt(L, U_, j1); p2 = gpt(L, U_, j2)
            for lk, pk in ((l1, p1), (l2, p2)):
                if lk == 0: continue
                if not tchk(L, U_, pk, lbP, lbM, pd, Q_): return False
                if Q_ is not None: Q_['p'].add(pk)
                P_, M_ = pd(pk); v = pw(pk)
                lhs += SC * aN[t] * lk * v
                lhs += RU * aN[t] * lk * max(0, M_ - KU1) * (pk - L); rhs += RU * aN[t] * lk * max(0, KU1 - M_) * (pk - L)
                for r in range(i, j): SL[r] += aN[t] * lk * P_; SK[r] += aN[t] * lk
            if c_:
                if Q_ is not None: Q_['z'].add((L, U_))
                lhs += SC * aN[t] * c_ * lbw(L, U_)
        for r in range(Q):
            rhs += RU * (box[r][1] - box[r][0]) * max(0, KU1 * SK[r] - SL[r])
        return lhs >= rhs
    def tocert(cert):
        out = []
        for c_ in cert:
            if c_[0] == 'C': out.append((0, 0, 0, 0))
            elif c_[0] == 'T': out.append((1, c_[1][3], 0, 0))
            elif c_[0] == 'CT': out.append((2, c_[1][3], 0, c_[2]))
            else: out.append((3, c_[1][3], c_[2][3], c_[3]))
        return out
    def icheck(box, cert, lbw):
        """the integer minorant check (Lean semantics): 1024 U sum bN l + SC sum aN (sum lam v + lamc lb) >=
        1024 cN SC U + RU sum aN sum lam (KU1 - M)(p - L) + RU sum_r (u - l) max(0, KU1 sum aN lam - 1024 U1 bN - sum aN lam P)"""
        I = iv(box); lhs = 1024 * U * sum(bN[r] * box[r][0] for r in range(Q)); rhs = 1024 * cN * SC * U
        SL = [0] * Q; SK = [0] * Q
        for t, (i, j) in enumerate(PAIRS):
            L_, U_ = I[t]; c_ = cert[t]
            if c_[0] == 'C': tl = [(1024, None)]
            elif c_[0] == 'T': tl = [(1024, c_[1])]
            elif c_[0] == 'CT': tl = [(1024 - c_[2], None), (c_[2], c_[1])]
            else: tl = [(1024 - c_[3], c_[1]), (c_[3], c_[2])]
            for lam, m in tl:
                if m is None: lhs += SC * aN[t] * lam * lbw(L_, U_); continue
                v, dmid, p, jj, P_, M_ = m
                lhs += SC * aN[t] * lam * v
                rhs += RU * aN[t] * lam * (KU1 - M_) * (p - L_)
                for r in range(i, j): SL[r] += aN[t] * lam * P_; SK[r] += aN[t] * lam
        for r in range(Q):
            rhs += RU * (box[r][1] - box[r][0]) * max(0, KU1 * SK[r] - 1024 * U1 * bN[r] - SL[r])
        return lhs >= rhs
    def mtest(box, lbw, lbP, lbM, pw, pd):
        """per-term independent certifiable minorants: LP over the box (convex-combination certificate) and the
        single-minorant rounding; returns (LP value - c, rounded value - c) relative to c.  TWOGRID: first with the
        tangents of the 2^8 grid only, then with both grids (fine points only where the coarse ones do not certify)"""
        I = iv(box)
        Call = [mcands(I[t][0], I[t][1], lbw, lbP, lbM, pw, pd) for t in range(NP)]
        res = None
        for gs_ in MPASS:
            C = [[m__ for m__ in cs if len(m__) < 4 or m__[3] is None or (m__[3] >> 4) in gs_] for cs in Call]
            res = mtest1(box, C, lbw, lbP, lbM, pw, pd)
            if MTEST != 3 or (len(res) == 3 and res[1] > 0): return res
        return res
    def mtest1(box, C, lbw, lbP, lbM, pw, pd):
        lo = np.array([x[0] for x in box]) / SC; hi = np.array([x[1] for x in box]) / SC
        A_ub = []; b_ub = []
        for t, (i, j) in enumerate(PAIRS):
            cs = C[t]
            for m__ in cs:
                al, dd, p = m__[0], m__[1], m__[2]
                row = np.zeros(Q + NP); row[i:j] = dd / U1; row[Q + t] = -1.0
                A_ub.append(row); b_ub.append(-(al / U - dd / U1 * p / SC))
        r_ = _linprog(np.concatenate([b, a]), A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=list(zip(lo, hi)) + [(None, None)] * NP, method='highs')
        if r_.status != 0: return -1.0, -1.0
        if os.environ.get("MSTATS") and (r_.fun - cF) / cF >= 1e-7:
            mu = -r_.ineqlin.marginals; k0 = 0
            for t in range(NP):
                nk = len(C[t]); m_ = mu[k0:k0 + nk]; k0 += nk
                nz = [j for j in range(nk) if m_[j] > 1e-12 * max(1e-30, a[t])]
                kinds = tuple(sorted(('c' if j == 0 else ('s' if C[t][j][1] != 0 and C[t][j][2] % 256 == 0 and False else 'l')) for j in nz))
                MST[(len(nz), 'const' if nz == [0] else ('mix' if 0 in nz else 'lines'))] = MST.get((len(nz), 'const' if nz == [0] else ('mix' if 0 in nz else 'lines')), 0) + 1
        if MTEST == 3:
            mu = -r_.ineqlin.marginals; k0 = 0; cert = []
            for t in range(NP):
                nk = len(C[t]); m_ = mu[k0:k0 + nk]; k0 += nk
                if aN[t] == 0: cert.append(('C',)); continue
                order = [j for j in np.argsort(-m_) if m_[j] > 0][:2]
                if not order: order = [0]
                if len(order) == 1:
                    cert.append(('C',) if order[0] == 0 else ('T', C[t][order[0]]))
                else:
                    w0_, w1_ = m_[order[0]], m_[order[1]]
                    lam = int(round(1024 * w1_ / (w0_ + w1_)))
                    A_, B_ = C[t][order[0]], C[t][order[1]]
                    if lam <= 0: cert.append(('C',) if order[0] == 0 else ('T', A_))
                    elif lam >= 1024: cert.append(('C',) if order[1] == 0 else ('T', B_))
                    elif order[0] == 0: cert.append(('CT', B_, lam))
                    elif order[1] == 0: cert.append(('CT', A_, 1024 - lam))
                    else: cert.append(('TT', A_, B_, lam))
            mc = tocert(cert)
            return (r_.fun - cF) / cF, (1.0 if meval(box, mc, lbw, lbP, lbM, pw, pd) else -1.0), mc
        g = r_.x[:Q]; s_ = INC @ g
        coef = b.copy(); const = 0.0
        for t, (i, j) in enumerate(PAIRS):
            best = max(C[t], key=lambda m: m[0] / U + m[1] / U1 * (s_[t] - m[2] / SC))
            coef[i:j] += a[t] * best[1] / U1; const += a[t] * (best[0] / U - best[1] / U1 * best[2] / SC)
        v1 = const + float(np.minimum(coef * lo, coef * hi).sum())
        return (r_.fun - cF) / cF, (v1 - cF) / cF
    def decide(box, lbw, lbP, lbM, pw, pd, lbw3):
        if TRUEMIN:
            if box[0][0] > box[Q - 1][1]: return (0, None)
            if inbas(box): return (3, None)
            return (5, None) if truemin(box) >= cF * (1 + 1e-4) else None
        """leaf kind and payload, or None"""
        if box[0][0] > box[Q - 1][1]: return (0, None)
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: return (1, None)
        if inbas(box): return (3, None)
        if zlow(box, lbw3) >= CSU: return (1, None)
        for v, modes, q, T in (scands(box) if not os.environ.get("NOS") else []):
            if v < cF * 0.999: break
            if sint(box, q, T, lbw, lbP, lbM, pw, pd) >= CSU: return (2, (modes, T))
        if SECOND and second(box) >= cF * (1 + 1e-6): return (4, None)
        if MTEST == 3:
            res_ = mtest(box, lbw, lbP, lbM, pw, pd)
            if len(res_) == 3:
                vlp, ok_, cert = res_
                mstat[0] += 1; mstat[1] += vlp >= 0; mstat[2] += ok_ > 0
                if ok_ > 0: return (6, cert)
        elif MTEST:
            vlp, v1 = mtest(box, lbw, lbP, lbM, pw, pd)[:2]
            mstat[0] += 1; mstat[1] += vlp >= 0; mstat[2] += v1 >= 0
            if (vlp if MTEST == 2 else v1) >= 1e-7: return (6, None)
        return None
    def reduce(box, lbP, lbM):
        """monotone face reduction: collapse a gap to its lower (upper) face where dG/dg_r >= 0 (<= 0) on the box"""
        box = list(box); changed = True
        while changed:
            changed = False
            I = iv(tuple(box))
            for r in range(Q):
                if box[r][0] == box[r][1]: continue
                lo_ok = hi_ok = True; Dlo = U1 * bN[r]; Dhi = U1 * bN[r]
                for t in TS[r]:
                    lo_t, hi_t = I[t]
                    if hi_t == lo_t:
                        p_, m_ = ptd(lo_t)
                    else:
                        p_, m_ = lbP(lo_t, hi_t), lbM(lo_t, hi_t)
                    if p_ < 1: lo_ok = False
                    else: Dlo += aN[t] * (p_ - KU1)
                    if m_ < 1: hi_ok = False
                    else: Dhi += aN[t] * (KU1 - m_)
                if lo_ok and Dlo >= 0 and r != Q - 1:
                    box[r] = (box[r][0], box[r][0]); changed = True; nface[0] += 1; break
                if hi_ok and Dhi <= 0 and r != 0:
                    box[r] = (box[r][1], box[r][1]); changed = True; nface[0] += 1; break
        return tuple(box)
    def subdivide(box, depth, tabs, parent=None):
        if FACE:
            rb = reduce(box, tabs[1], tabs[2])
            if rb != box: nface[1] += 1; box = rb
        d = decide(box, *tabs)
        if d is not None:
            if DUMP is not None: DUMP.append((box, d[0], parent, d[1]))
            count[0] += 1; count[d[0]] += 1 if d[0] in (1, 2, 3, 4, 5, 6) else 0
            if verbose and count[0] % 20000 == 0:
                print(f"  ... {count[0]} leaves (Z {count[1]}, S {count[2]}, B {count[3]}, 2nd {count[4]}, M {count[6]}) mtests {mstat} ({time.time()-t0:.0f}s)", flush=True)
            return ('leaf', box, d[0], d[1])
        if depth > 70 or count[0] > max_leaves or max(x[1] - x[0] for x in box) <= 1:
            if verbose: print("  stuck", box, flush=True)
            return None
        k = choose(box); mid = (box[k][0] + box[k][1]) // 2
        A_ = list(box); A_[k] = (box[k][0], mid); B_ = list(box); B_[k] = (mid, box[k][1])
        X = subdivide(tuple(A_), depth + 1, tabs, box)
        if X is None: return None
        Y = subdivide(tuple(B_), depth + 1, tabs, box)
        if Y is None: return None
        return ('split', box, k, mid, X, Y)
    est = (lbE1, lbPE, lbME, ptw, ptd, lbE)
    if probe: return dict(est=est, sint=sint, sfloat=sfloat, scands=scands, dec=dec, zlow=zlow, flower=flower, decide=decide, iv=iv, inreg=inreg)
    nodes = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        nd = subdivide(box, 0, est)
        if nd is None: return None
        nodes[tup] = nd
    if verbose: print(f"  bisection: {count[0]} leaves (Z {count[1]}, S {count[2]}, basin {count[3]}); face nodes {nface[1]} (collapses {nface[0]}) ({time.time()-t0:.0f}s)", flush=True)
    if os.environ.get("MSTATS"): print("MSTATS", sorted(MST.items()), flush=True)
    if DUMP is not None: return dict(nleaves=count[0], nZ=count[1], nS=count[2], nB=count[3], n2=count[4], nM=count[6], nface=nface[1])
    # ---- tables from the queries ----
    leaves = []
    def collect(nd):
        if nd[0] == 'leaf': leaves.append(nd)
        else: collect(nd[4]); collect(nd[5])
    for nd in nodes.values(): collect(nd)
    qz, qd, qz1 = set(), set(), set()
    for _, box, kind, pay in leaves:
        I = iv(box)
        if kind == 1: qz.update(I)
        elif kind == 2:
            modes, T = pay; q = qof(modes, box)
            for t, (i, j) in enumerate(PAIRS):
                lo, hi = I[t]
                if T >> t & 1:
                    qt = sum(q[i:j])
                    if inreg(lo, hi): continue
                    if hi > qt: qd.add((qt, hi))
                    if qt > lo: qd.add((lo, qt))
                else: qz1.add((lo, hi))
        elif kind == 6:
            Q_ = {'z': set(), 'd': set(), 'p': set()}
            meval(box, pay, *est[:5], Q_=Q_); qz1 |= Q_['z']; qd |= Q_['d']
    for bx in basins: qz1.update(iv(bx))
    qz = {pc for (lo, hi) in qz for pc in pieces(lo, hi, SH, MINW)} | qz1
    P.need(qz)
    for j in range(P.X0 >> P.PB, ((P.xmax - 1) >> P.PB) + 1): P.res[j] = WMIN
    P.build(); PP.need(qd); PM.need(qd)
    if DENSE:
        for X_ in (PP, PM):
            for j in range(X_.X0 >> X_.PB, ((X_.xmax - 1) >> X_.PB) + 1): X_.res[j] = DLO if (j << 10) < XD else DHI
    PP.build(); PM.build()
    Plb3 = lb3_of(P.lb, SH, MINW)
    built = (P.lb, PP.lb, PM.lb, ptw, ptd, Plb3)
    fixed = [0, 0]
    def fix(nd, depth=0):
        if nd[0] == 'split':
            return ('split', nd[1], nd[2], nd[3], fix(nd[4], depth + 1), fix(nd[5], depth + 1))
        _, box, kind, pay = nd
        if kind in (0, 3) or sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: return nd
        if kind == 1 and zlow(box, Plb3) >= CSU: return nd
        if kind == 2:
            modes, T = pay; q = qof(modes, box)
            if sint(box, q, T, *built[:5]) >= CSU: return nd
        if kind == 6 and meval(box, pay, *built[:5]): return nd
        fixed[0] += 1
        r = subdivide(box, depth, built)
        assert r is not None, ("fix-up failed", box)
        return r
    nodes = {k: fix(v) for k, v in nodes.items()}
    leaves = []
    for nd in nodes.values(): collect(nd)
    pts = set(); bad = 0
    nZ = nS = nB = 0
    for _, box, kind, pay in leaves:
        if kind == 1:
            nZ += 1
            if sum(bN[r] * box[r][0] for r in range(Q)) < cN * SC and zlow(box, Plb3) < CSU: bad += 1
        elif kind == 2:
            nS += 1; modes, T = pay; q = qof(modes, box)
            for t, (i, j) in enumerate(PAIRS):
                if T >> t & 1: pts.add(sum(q[i:j]))
            if sint(box, q, T, *built[:5]) < CSU: bad += 1
        elif kind == 3: nB += 1
        elif kind == 6:
            Q_ = {'z': set(), 'd': set(), 'p': set()}
            if not meval(box, pay, *built[:5], Q_=Q_): bad += 1
            pts |= Q_['p']
    tzb = {}
    for x in pts:
        o = x & 1023; tz = min(10, (o & -o).bit_length() - 1) if o else 10
        tzb[x >> 10] = min(tzb.get(x >> 10, 10), tz)
    st = dict(w=P.stats(), d=PP.stats(), points=len(pts), ptcells=sum(1 << (10 - r) for r in tzb.values()))
    if verbose:
        print(f"  fix-up: {fixed[0]} re-decided; tables: w {st['w']['finest']} cells, d {st['d']['finest']} cells, "
              f"{len(pts)} points ({st['ptcells']} point cells); failing {bad} ({time.time()-t0:.0f}s)", flush=True)
    return dict(P=P, PP=PP, PM=PM, nodes=nodes, covers=covers, bads=bads, S=S, leaves=leaves, nleaves=len(leaves),
                nZ=nZ, nS=nS, nB=nB, pts=pts, stats=st, bad=bad, dec=dec, sint=sint, built=built, cN=cN, sfloat=sfloat, iv=iv, inreg=inreg, qof=qof, Plb3=Plb3, pieces=lambda lo, hi: pieces(lo, hi, SH, MINW), meval=meval, gpt=gpt, mweights=mweights)
