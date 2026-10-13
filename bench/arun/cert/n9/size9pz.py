"""(size8pz: copy of size8amz.py with PAIR-DISTANCE CELLS: cells carry explicit bounds Lb_t <= s_t <= Ub_t on
non-adjacent pair sums, integer bound tightening, splits on gaps or pair sums, empty cells, and the minorant leaf with
multipliers on the explicit constraints (quantised to QB bits); split rule SPLIT=err (relaxation error at the LP point)
or pf (the PFK best by error, children LP-tested).  Below: the size8amz header.)
(AM copy of bench/eight/size7s.py WITH the two-grid tangent option (TWOGRID), mvt-engine: kernel swapped to amk (AMWIN selects the window's
numerators); the AM per-gap cover `phase1`; nothing else changed.)
Integer-faithful sizing of the seven-point (Q = 6) certificate with
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
import collections
class Cell(tuple):
    """a box of Q integer gap ranges with explicit pair-distance constraints .cons = {t: (Lb, Ub)}"""
    def __new__(cls, box, cons=None):
        c = tuple.__new__(cls, box); c.cons = dict(cons or {}); return c
    def __reduce__(self): return (Cell, (tuple(self), self.cons))
# (bridge-port, 2026-10-10: size9pz.py = mvt-engine's eight/am8/size8pz.py with one change, the per-gap linear-pay bound
#  S_r kept below the Lean cell bound KB = 2^20 (PCellRoot.coverChk requires every cover end b < KB).  S_r is the QUARTER
#  multiple as before unless that reaches KB, then the 1024 multiple (still >= cN SC / b_r).  At n = 8 nothing changes.
#  HERE is pinned to eight/am8 so the relative imports resolve from this copy.)
HERE = "/Users/samuellavery/work/riemann-submission/bench/eight/am8"
for p in (HERE, os.path.join(HERE, "..", "..", "window", "amg"), os.path.join(HERE, "..", "..", "pyr"), os.path.join(HERE, "..", "..", "mvt"), os.path.join(HERE, "..")):
    sys.path.insert(0, p)
sys.setrecursionlimit(1000000)
from size_pyr import SA, SC, QUARTER, WFRAC, X0
from pyr_table import Pyr
import amk
from amk import WZ, SW, fP, fM, U1, KU1
from size_m import PyrF
from amk import w as wf, w1 as w1f
import sevenw as _sw
_sw.w = amk.w; _sw.w1 = amk.w1; _sw.w2 = amk.w2
def phase1(cN, aAdjN, S):
    """per-gap cover of [1/2, S] (units 2^-15), as size_pyr.phase1 with the AM cell bound and float w"""
    roots = []; a = X0
    while a < S:
        b = min(a + QUARTER, S); roots.append((a, b)); a = b
    clear, bad = [], []
    stack = list(reversed(roots))
    while stack:
        l, u = stack.pop()
        if cN * SW <= aAdjN * WZ(l, u): clear.append((l, u)); continue
        wm = float(wf(np.linspace(l / SC, u / SC, 121)).min())
        if wm * aAdjN < cN and (u - l) <= SC // 64: bad.append((l, u)); continue
        if u - l <= SC // 4096: bad.append((l, u)); continue
        m = (l + u) // 2; stack.append((m, u)); stack.append((l, m))
    bad.sort(); merged = []
    for iv in bad:
        if merged and merged[-1][1] == iv[0]: merged[-1] = (merged[-1][0], iv[1])
        else: merged.append(iv)
    clear.sort()
    return clear, merged

Q = int(os.environ.get("SQ", "7"))   # gaps (n - 1); run8pz sets it from the window's n
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
    _KB = 1 << 20
    S = [s if s < _KB else -(-(cN * SC) // (bN[r] * 1024)) * 1024 for r, s in enumerate(S)]
    assert all(s < _KB and s * bN[r] >= cN * SC for r, s in enumerate(S)), S
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
    def iv0(box):
        return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
    def iv(box):
        """the EFFECTIVE pair ranges: the box sums clipped by the cell's explicit pair constraints (TRIPLE: the
        propagated intervals)"""
        rng = getattr(box, 'rng', None)
        if rng is not None: return [rng[t] for t in range(len(PAIRS))]
        I = iv0(box); cons = getattr(box, 'cons', None)
        if not cons: return I
        for t, (Lb, Ub) in cons.items():
            L0, U0 = I[t]
            I[t] = (L0 if Lb is None else max(L0, Lb), U0 if Ub is None else min(U0, Ub))
        return I
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
    mstat = [0, 0, 0]; MST = {}; MDG = []
    LROUND = os.environ.get("LROUND") == "1"
    MINR = int(os.environ.get("MINR", "64"))
    PEC = int(os.environ.get("PEC", "0"))   # sizing only: the constant minorant read on a cover of shift PEC (0 = the table's own read)
    _ec = {}
    def lbc(lbw, lo, hi):
        if os.environ.get("EXACTC") == "1":
            k_ = (lo, hi)
            if k_ not in _ec:
                i0 = lo * _HX // SC; i1 = -(-hi * _HX // SC)
                _ec[k_] = max(0, int(float(_WS[i0:i1 + 1].min()) * U) - 1)
            return _ec[k_]
        if hi <= lo: return lbw(lo, lo + 1)   # a degenerate range reads [lo, lo + 1] (the pyramid read needs lo < hi)
        if not PEC: return lbw(lo, hi)
        k = max(0, (hi - lo).bit_length() - PEC)
        return lbw((lo >> k) << k, (((hi >> k) + 1) << k) - 1)   # ranges narrower than this get only the constant minorant (sizing heuristic)
    JSH = int(os.environ.get("JSH", "4" if os.environ.get("J16") == "1" else "3"))   # grid points at (U - L) j / 2^JSH (Lean: 3)
    LS = int(os.environ.get("LSC", "1024"))   # the weight scale of a mixed minorant (Lean MinCore: 1024)
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
        ZTAB[0] = lbw; ZTAB[1] = pw
        """certifiable minorants of w on [lo, hi] / SC as (alpha*U, d*U1, p): w(s) >= (alpha + d (s - p/SC)) on the range;
        the constant lb, and lines through (p, w(p)) (p on the 256-grid) with slope dR = min w' on [p, hi] or
        dL = max w' on [lo, p] (table bounds) when dL <= dR"""
        if os.environ.get("MREG") == "3":
            # as MREG=2 with the Lean semantics: p = clamp(((lo + (hi - lo) j / 8) >> 8) << 8, ga, gb), region of the
            # integer nearest to p, candidates carry (v, dmid, p, j, P, M)
            out = [(lbc(lbw, lo, hi), 0, lo, None, 0, 0)]
            if hi - lo < MINR and not (PLO and hi == lo): return out
            seen = set()
            for jj in [j + (1 << (JSH + 1)) * f_ for f_ in GRIDS for j in range((1 << JSH) + 1)] + ([JLO] if PLO else []):
                p = gpt(lo, hi, jj)
                if p is None or p in seen: continue
                seen.add(p)
                j = jj
                if not tchk(lo, hi, p, lbP, lbM, pd): continue      # the leaf's own validity check (one source of truth)
                P_, M_ = pd(p)
                out.append((pw(p), (P_ - M_) // 2, p, j, P_, M_))
            if os.environ.get("DBGC") and hi == lo and DBGN[0] < 5:
                DBGN[0] += 1; print("   DBG mcands", lo, hi, [(c__[2], c__[3]) for c__ in out], PLO, flush=True)
            if os.environ.get("CHORD"):
                p1 = (lo >> 8) << 8; p2 = ((hi + 255) >> 8) << 8
                if p2 > p1 and in_concave(p1, p2):
                    w1_ = float(wf(p1 / SC)); w2_ = float(wf(p2 / SC)); dd = (w2_ - w1_) / ((p2 - p1) / SC)
                    out.append((w1_ * U - 1, dd * U1, p1))
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
    PLO = os.environ.get("PLO") == "1"; JLO = (1 << JSH) + 1; DBGN = [0]   # PLO: the unused position value 2^JSH + 1 (grid bit clear) = the range start L
    def gpt(L, U_, jj):
        if jj == JLO: return L
        """the Lean `gptG` (TWOGRID: `gptF`, bit 4 of jj selects the fine grid 2^GS, else the 2^8 grid); None when
        the grid has no point in [L, U] (the clamp then leaves the range and the Lean test fails)"""
        gs = (GS if jj >> (JSH + 1) else 8) if TWOGRID else GS; j = jj & ((1 << (JSH + 1)) - 1); sh = JSH
        gm = (1 << gs) - 1
        ga = ((L + gm) >> gs) << gs; gb = (U_ >> gs) << gs; x = ((L + (((U_ - L) * j) >> sh)) >> gs) << gs
        r = ga if x <= ga else (gb if gb <= x else x)
        return r if ga <= gb else (r if L <= r <= U_ else None)
    EXACTV = os.environ.get("EXACTV") == "1"; EXACTC = os.environ.get("EXACTC") == "1"; LPACCEPT = os.environ.get("LPACCEPT") == "1"
    _ev = {}
    _HX = 4096; _XS = np.arange(0, 96 * _HX + 2) / _HX
    _WS = wf(_XS) if (os.environ.get("EXACTV") == "1" or os.environ.get("EXACTC") == "1") else None
    def exact_valid(L, U_, p):
        """the tangent at p (float w, w') below w on [L, U], checked on the 1/4096 grid (sizing only)"""
        k_ = (L, U_, p)
        if k_ in _ev: return _ev[k_]
        i0 = L * _HX // SC; i1 = -(-U_ * _HX // SC); x = _XS[i0:i1 + 1]; y = _WS[i0:i1 + 1]
        ok = bool((y - (float(wf(p / SC)) + float(w1f(p / SC)) * (x - p / SC))).min() >= -1e-13)
        _ev[k_] = ok; return ok
    VDIAG = collections.Counter()
    def tchk_reason(L, U_, p, lbP, lbM, pd):
        """why the faithful tchk rejects (or accepts) p on [L, U]"""
        if L == U_ == p: return 'ok'
        k = (p + 16384) >> 15
        if k >= 16 or k not in RGK2: return 'no region for k'
        za, zb = RGK2[k]
        if not (za <= p <= zb): return 'p outside region'
        P_, M_ = pd(p)
        if U_ > zb:
            e = lbP(zb, U_)
            if e < 1 or e + M_ < 4 * U1: return 'right extension'
        if L < za:
            e = lbM(L, za)
            if e < 1 or e + P_ < 4 * U1: return 'left extension'
        return 'ok'
    def tchk(L, U_, p, lbP, lbM, pd, Q_=None):
        if EXACTV:
            if not (L <= p <= U_): return False
            P_, M_ = pd(p)
            ok = P_ >= 1 and M_ >= 1 and exact_valid(L, U_, p)
            if ok and os.environ.get("DIAGV"): VDIAG[tchk_reason(L, U_, p, lbP, lbM, pd)] += 1
            return ok
        if PLO and L == U_ == p:
            P_, M_ = pd(p); return P_ >= 1 and M_ >= 1      # a one-point range: the tangent at the point itself
        k = (p + 16384) >> 15
        if k >= 16 or k not in RGK2: return False
        za, zb = RGK2[k]
        if not (za <= p <= zb and L <= p <= U_): return False
        P_, M_ = pd(p)
        if P_ < 1 or M_ < 1: return False
        if U_ > zb:
            if Q_ is not None: Q_['d'].add((zb, U_))
            e = lbP(zb, U_)
            if e < 1 or e + M_ < 4 * U1:
                if not (ZEXT and zext(zb, U_, p, P_, M_, 1, Q_)): return False
        if L < za:
            if Q_ is not None: Q_['d'].add((L, za))
            e = lbM(L, za)
            if e < 1 or e + P_ < 4 * U1:
                if not (ZEXT and zext(L, za, p, P_, M_, 0, Q_)): return False
        return True
    ZEXT = int(os.environ.get("ZEXT", "0"))
    def zext(a_, b_, p, P_, M_, right, Q_=None):
        """tz.zext (TZ.md): the tangent through (p, v) with the worst slope claim below the pyramid read on ZEXT pieces"""
        lbw = ZTAB[0]
        if lbw is None: return False
        if Q_ is not None:
            for k in range(ZEXT):
                x0 = a_ + (b_ - a_) * k // ZEXT; x1 = a_ + (b_ - a_) * (k + 1) // ZEXT
                if x1 > x0: Q_['z'].add((x0, x1))
        if BUILT[0] and len(ZLOG) < int(os.environ.get("ZLOGN", "0")):
            lg = []; ok = _tz.zext(a_, b_, p, ZTAB[1](p), P_, M_, right, lbw, n=ZEXT, log=lg)
            if ok or sum(1 for z in ZLOG if not z['ok']) < 2:
                ZLOG.append(dict(a=a_, b=b_, p=p, v=ZTAB[1](p), P=P_, M=M_, right=bool(right), n=ZEXT, pieces=lg, ok=ok))
            return ok
        return _tz.zext(a_, b_, p, ZTAB[1](p), P_, M_, right, lbw, n=ZEXT)
    ZTAB = [None, None]; BUILT = [False]; ZLOG = []
    def mweights(kap, lam):
        if kap == 1: return 0, LS, 0
        if kap == 2: return LS - lam, lam, 0
        if kap == 3: return 0, LS - lam, lam
        return LS, 0, 0
    # ================= size8pz: pair-distance cells =================
    # A cell is a Cell: Q integer gap ranges (units 1/SC) with .cons = {t: (Lb, Ub)} for split non-adjacent pairs
    # (s_t = g_i + ... + g_{j-1} in [Lb, Ub]; None = no bound).  iv() gives the effective pair ranges, iv0() the box sums.
    YFRAC = int(os.environ.get("YFRAC", "20"))
    SIG = max(1, (LS * U1 * SA) >> YFRAC)           # the multiplier quantum: y in units of 2^-YFRAC (S units = LS U1 SA y)
    QB = 0
    SPLIT = os.environ.get("SPLIT", "err"); PFK = int(os.environ.get("PFK", "4"))
    JB = JSH + 2                                     # bits of a tangent's position field (JSH+1) and grid bit
    LASTX = [None]
    MINPW = int(os.environ.get("MINPW", "256"))
    NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]
    def meval(cell, cert, lbw, lbP, lbM, pw, pd, Q_=None):
        """the leaf inequality: per term a minorant valid on the term's EFFECTIVE range [Le, Ue] (tchk, lbc, gptF on that
        range), expanded at the box corner L0 = sum of l (p >= Le >= L0), mixed by 10-bit weights; plus the multipliers
        Y on the explicit constraints: -y_lo (s - Lb) - y_hi (Ub - s) <= 0 on the cell, so they shift the gap slopes by
        -/+ Y and the constant by -RU Y (L0 - Lb), -RU Y (Ub - L0); then the per-gap corner minimum.  Units: S = slope
        per unit of g in 1/SC times LS U1 SA (the bN scale)."""
        mc, Ys = cert
        ZTAB[0] = lbw; ZTAB[1] = pw
        I = iv(cell); I0 = iv0(cell)
        lhs = LS * U * sum(bN[r] * cell[r][0] for r in range(Q)); rhs = LS * cN * SC * U
        SL = [LS * U1 * bN[r] for r in range(Q)]; SK = [0] * Q
        for t, (i, j) in enumerate(PAIRS):
            if aN[t] == 0: continue
            L, U_ = I[t]; L0 = I0[t][0]; kap, j1, j2, lam = mc[t]
            if lam > LS: return False
            c_, l1, l2 = mweights(kap, lam); p1 = gpt(L, U_, j1); p2 = gpt(L, U_, j2)
            for lk, pk in ((l1, p1), (l2, p2)):
                if lk == 0: continue
                if pk is None or not tchk(L, U_, pk, lbP, lbM, pd, Q_): return False
                if Q_ is not None: Q_['p'].add(pk)
                P_, M_ = pd(pk); v = pw(pk)
                lhs += SC * aN[t] * lk * v
                lhs += RU * aN[t] * lk * max(0, M_ - KU1) * (pk - L0); rhs += RU * aN[t] * lk * max(0, KU1 - M_) * (pk - L0)
                for r in range(i, j): SL[r] += aN[t] * lk * P_; SK[r] += aN[t] * lk
            if c_:
                if Q_ is not None: Q_['z'].add((L, U_))
                lhs += SC * aN[t] * c_ * lbc(lbw, L, U_)
        for (t, side), Yq in Ys.items():
            Y = Yq * SIG; i, j = PAIRS[t]; L0 = I0[t][0]; Lb, Ub = cell.cons[t]
            if side == 0:
                for r in range(i, j): SL[r] -= Y
                lhs -= RU * Y * (L0 - Lb)
            else:
                for r in range(i, j): SL[r] += Y
                lhs -= RU * Y * (Ub - L0)
        for r in range(Q):
            rhs += RU * (cell[r][1] - cell[r][0]) * max(0, KU1 * SK[r] - SL[r])
        return lhs >= rhs
    def tocert(cert):
        out = []
        for c_ in cert:
            if c_[0] == 'C': out.append((0, 0, 0, 0))
            elif c_[0] == 'T': out.append((1, c_[1][3], 0, 0))
            elif c_[0] == 'CT': out.append((2, c_[1][3], 0, c_[2]))
            else: out.append((3, c_[1][3], c_[2][3], c_[3]))
        return out
    MSTAT = dict(lp=0, lp_pass=0, ok=0, yfix=0, nzY=collections.Counter(), ncons=collections.Counter())
    def mtest(cell, lbw, lbP, lbM, pw, pd):
        I = iv(cell)
        Call = [mcands(I[t][0], I[t][1], lbw, lbP, lbM, pw, pd) if aN[t] > 0 else [] for t in range(NP)]
        res = None
        for gs_ in MPASS:
            C = [[m__ for m__ in cs if len(m__) < 4 or m__[3] is None or m__[3] == JLO or (m__[3] >> (JSH + 1)) in gs_] for cs in Call]
            res = mtest1(cell, C, lbw, lbP, lbM, pw, pd)
            if res[0] == 'empty' or res[1] > 0: return res
        return res
    RESTRICT = os.environ.get("RESTRICT", "1") == "1"
    def mtest1(cell, C, lbw, lbP, lbM, pw, pd, _restricted=False):
        lo = np.array([x[0] for x in cell]) / SC; hi = np.array([x[1] for x in cell]) / SC
        I0 = iv0(cell)
        A_ub = []; b_ub = []
        for t, (i, j) in enumerate(PAIRS):
            for m__ in C[t]:
                al, dd, p = m__[0], m__[1], m__[2]
                row = np.zeros(Q + NP); row[i:j] = dd / U1; row[Q + t] = -1.0
                A_ub.append(row); b_ub.append(-(al / U - dd / U1 * p / SC))
        ncand = len(A_ub); crow = []
        for t, (Lb, Ub) in cell.cons.items():
            i, j = PAIRS[t]; L0, U0 = I0[t]
            if Ub is not None and Ub < U0:
                row = np.zeros(Q + NP); row[i:j] = 1.0; A_ub.append(row); b_ub.append(Ub / SC); crow.append((t, 1))
            if Lb is not None and Lb > L0:
                row = np.zeros(Q + NP); row[i:j] = -1.0; A_ub.append(row); b_ub.append(-Lb / SC); crow.append((t, 0))
        r_ = _linprog(np.concatenate([b, a]), A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                      bounds=list(zip(lo, hi)) + [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)], method='highs')
        MSTAT['lp'] += 1
        if r_.status == 2: return ('empty', -1.0, None, None)
        if r_.status != 0: return (-1.0, -1.0, None, None)
        LASTX[0] = r_.x
        vlp = (r_.fun - cF) / cF
        if vlp < 0: return (vlp, -1.0, None, r_.x)
        MSTAT['lp_pass'] += 1
        if LPACCEPT: return (vlp, 1.0, ([(0, 0, 0, 0)] * NP, {}), r_.x)
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
                lam = int(round(LS * w1_ / (w0_ + w1_)))
                A_, B_ = C[t][order[0]], C[t][order[1]]
                if lam <= 0: cert.append(('C',) if order[0] == 0 else ('T', A_))
                elif lam >= LS: cert.append(('C',) if order[1] == 0 else ('T', B_))
                elif order[0] == 0: cert.append(('CT', B_, lam))
                elif order[1] == 0: cert.append(('CT', A_, LS - lam))
                else: cert.append(('TT', A_, B_, lam))
        mc = tocert(cert)
        yv = mu[ncand:]
        Yx = {crow[k]: LS * U1 * SA * float(yv[k]) / SIG for k in range(len(crow)) if yv[k] > 1e-15}
        if os.environ.get("DBGY") and vlp > 0.05:
            # float evaluation of the rounded certificate with exact multipliers, and meval with exact (unquantised) Y
            Yexact = {k: v * SIG for k, v in Yx.items()}
            print("   DBGY vlp", vlp, "Yx", {k: round(v, 2) for k, v in Yx.items()}, "ncand", ncand, "crow", crow, flush=True)
            SIGs = SIG
            for k_, v_ in Yx.items(): pass
        for rnd in (lambda x: int(round(x)), lambda x: int(math.floor(x)), lambda x: int(math.ceil(x))):
            Ys = {k: rnd(v) for k, v in Yx.items()}
            Ys = {k: v for k, v in Ys.items() if v > 0}
            if meval(cell, (mc, Ys), lbw, lbP, lbM, pw, pd):
                MSTAT['ok'] += 1; MSTAT['nzY'][len(Ys)] += 1; MSTAT['ncons'][len(cell.cons)] += 1
                return (vlp, 1.0, (mc, Ys), r_.x)
        if os.environ.get("STUCKDBG") and vlp > 0.3:
            # where the certificate loses its LP margin: float value of the rounded certificate with exact multipliers
            lo_ = np.array([x[0] for x in cell]) / SC; hi_ = np.array([x[1] for x in cell]) / SC
            coef = b.copy(); const = 0.0; I0_ = iv0(cell)
            for t, (i, j) in enumerate(PAIRS):
                c_ = cert[t]
                if c_[0] == 'C': parts = [(1.0, C[t][0])]
                elif c_[0] == 'T': parts = [(1.0, c_[1])]
                elif c_[0] == 'CT': parts = [(1 - c_[2] / LS, C[t][0]), (c_[2] / LS, c_[1])]
                else: parts = [(1 - c_[3] / LS, c_[1]), (c_[3] / LS, c_[2])]
                for wgt, m__ in parts:
                    coef[i:j] += a[t] * wgt * m__[1] / U1; const += a[t] * wgt * (m__[0] / U - m__[1] / U1 * m__[2] / SC)
            for k_, (t, sd) in enumerate(crow):
                yy = float(yv[k_]); i, j = PAIRS[t]; Lb, Ub = cell.cons[t]
                if sd == 0: coef[i:j] -= yy; const += yy * Lb / SC
                else: coef[i:j] += yy; const -= yy * Ub / SC
            vr = const + float(np.minimum(coef * lo_, coef * hi_).sum())
            if not os.path.exists("lpdump.pkl"):
                import pickle as _pk
                _pk.dump(dict(c=np.concatenate([b, a]), A=np.array(A_ub), bu=np.array(b_ub), bounds=list(zip(lo, hi)) + [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)],
                              ncand=ncand, crow=crow, C=C, cert=cert, mu=mu, x=r_.x, fun=r_.fun, cF=cF, cons=cell.cons, box=tuple(cell)), open("lpdump.pkl", "wb"))
            print(f"   STUCKDBG vlp {vlp:.4f}; rounded-support float value rel {(vr - cF) / cF:.4f}; ncons {len(cell.cons)} crow {len(crow)} "
                  f"Yx {sorted((k, round(v, 1)) for k, v in Yx.items())}; terms with >=3 duals "
                  f"{sum(1 for t in range(NP) if 0)}", flush=True)
        if RESTRICT and not _restricted:
            # re-solve with each term limited to its two heaviest candidates, so the dual needs no support rounding
            k1 = 0; C2 = []
            for t in range(NP):
                nk = len(C[t]); m_ = mu[k1:k1 + nk]; k1 += nk
                if nk == 0: C2.append([]); continue
                keep = sorted([j for j in np.argsort(-m_)[:2] if m_[j] > 0] or [0])
                C2.append([C[t][j] for j in keep])
            MSTAT['restrict'] = MSTAT.get('restrict', 0) + 1
            return mtest1(cell, C2, lbw, lbP, lbM, pw, pd, _restricted=True)
        return (vlp, -1.0, None, r_.x)
    def decide(cell, lbw, lbP, lbM, pw, pd, lbw3):
        """leaf kind and payload, or None: 0 reflected half-space, 1 zero-order (or the linear part alone), 6 minorant
        with multipliers, 7 empty"""
        if cell[0][0] > cell[Q - 1][1] and not NOREFL: return (0, None)   # NOREFL: no mirror symmetry (truncated functionals)
        if not NOZ:
            if sum(bN[r] * cell[r][0] for r in range(Q)) >= cN * SC: return (1, None)
            if zlow(cell, lbw3) >= CSU: return (1, None)
        LASTX[0] = None
        res = mtest(cell, lbw, lbP, lbM, pw, pd)
        if res[0] == 'empty': return None if os.environ.get("LPEMPTY") == "split" else (8, None)
        if res[1] > 0: return (6, res[2])
        return None
    NR = int(os.environ.get("NR", "2")); NOZ = os.environ.get("NOZ") == "1"
    NODEC = collections.Counter()      # explicit constraints per visited node (after tightening)
    def tighten_gs(cell):
        l = [x[0] for x in cell]; u = [x[1] for x in cell]
        if any(l[r] > u[r] for r in range(Q)): return None
        cons = cell.cons
        for _ in range(8):
            ch = False
            for t in sorted(cons):
                Lb, Ub = cons[t]; i, j = PAIRS[t]
                for r in range(i, j):
                    sl = sum(l[i:j]); su = sum(u[i:j])
                    Le = sl if Lb is None else max(sl, Lb); Ue = su if Ub is None else min(su, Ub)
                    if Le > Ue: return None
                    nu = Ue - (sl - l[r]); nl = Le - (su - u[r])
                    if nu < u[r]: u[r] = nu; ch = True
                    if nl > l[r]: l[r] = nl; ch = True
                    if l[r] > u[r]: return None
            if not ch: break
        return Cell(tuple(zip(l, u)), cons)
    TRIPLE = int(os.environ.get("TRIPLE", "0"))
    import tz as _tz
    PERSIST = os.environ.get("PERSIST") == "1"
    TCLOSE = os.environ.get("TCLOSE") == "1"   # tz.close (the exact closure) in place of tz.t1
    def triples(cell):
        """TRIPLE passes of tz.t1 (TZ.md): intervals for every pair sum, the triple pass, gaps take the adjacent
        intervals; PERSIST: the non-adjacent intervals become the cell's pair bounds (children inherit them)"""
        l = [x[0] for x in cell]; u = [x[1] for x in cell]
        cons = {PAIRS[t]: v for t, v in cell.cons.items()}
        I = None
        for _ in range(TRIPLE):
            r_ = _tz.close(l, u, cons, Q) if TCLOSE else _tz.t1(l, u, cons, Q)
            if r_ is None: return None
            l, u, cons2, I = r_
            if PERSIST: cons = cons2
        newcons = {PAIRS.index(k): v for k, v in cons.items()} if PERSIST else cell.cons
        c2 = Cell(tuple(zip(l, u)), newcons); c2.rng = {t: tuple(I[PAIRS[t]]) for t in range(NP)}
        return c2
    def tighten(cell):
        c2 = tighten_gs(cell) if os.environ.get("TIGHT") == "gs" else tighten_j(cell)
        if c2 is None or not TRIPLE: return c2
        return triples(c2)
    def tighten_j(cell):
        """the kernel's tightening: NR rounds; per constraint (in PAIRS order) sl, su, Le, Ue computed once, empty if
        Le > Ue, then for every gap of the pair, from the OLD l, u: u_r = min(u_r, Ue - (sl - l_r)), l_r = max(l_r,
        Le - (su - u_r)) (Jacobi); None when the cell is empty"""
        l = [x[0] for x in cell]; u = [x[1] for x in cell]
        if any(l[r] > u[r] for r in range(Q)): return None
        cons = cell.cons
        for _ in range(NR):
            ch = False
            for t in sorted(cons):
                Lb, Ub = cons[t]; i, j = PAIRS[t]
                sl = sum(l[i:j]); su = sum(u[i:j])
                Le = sl if Lb is None else max(sl, Lb); Ue = su if Ub is None else min(su, Ub)
                if Le > Ue: return None
                ol = l[i:j]; ou = u[i:j]
                for k, r in enumerate(range(i, j)):
                    nu = min(ou[k], Ue - (sl - ol[k])); nl = max(ol[k], Le - (su - ou[k]))
                    if nu != u[r] or nl != l[r]: ch = True
                    u[r] = nu; l[r] = nl
                    if l[r] > u[r]: return None
            if not ch: break
        return Cell(tuple(zip(l, u)), cons)
    MINSPLIT = int(os.environ.get("MINSPLIT", "1"))
    NOREFL = os.environ.get("NOREFL") == "1"
    # BSPLIT=1 (the lead's size8pzb lever): a split may also cut at the convex-region boundary nearest the midpoint, at
    # least BMARG inside the range (mode 1, one extra walk bit per split); `choose` tries both modes
    BSPLIT = os.environ.get("BSPLIT") == "1"; BMARG = int(os.environ.get("BMARG", "64"))
    BND = sorted({z for zz in REGL for z in zz})
    def bpoint(lo, hi):
        m = (lo + hi) / 2; best = None
        for z in BND:
            if lo + BMARG <= z <= hi - BMARG and (best is None or abs(z - m) < abs(best - m)): best = z
        return best
    CMODE = [0]
    def children(cell, ax, mode=0):
        """the split of cell on axis ax (0..Q-1 a gap, Q + t a pair distance) at the integer midpoint of its (effective)
        range (mode 1: at `bpoint`); None when the range has width < MINSPLIT (MINSPLIT=2: a width-1 range [l, l+1] has
        midpoint l, so child B would be the cell itself and the bisection would descend without progress; default 1)"""
        if ax < Q:
            l_, u_ = cell[ax]
            if u_ - l_ < MINSPLIT: return None
            m = (l_ + u_) // 2
            if mode == 1:
                m = bpoint(l_, u_)
                if m is None: return None
            A_ = list(cell); A_[ax] = (l_, m); B_ = list(cell); B_[ax] = (m, u_)
            return Cell(tuple(A_), cell.cons), Cell(tuple(B_), cell.cons)
        t = ax - Q; Le, Ue = iv(cell)[t]
        if Ue - Le < MINSPLIT: return None
        m = (Le + Ue) // 2; Lb, Ub = cell.cons.get(t, (None, None))
        if mode == 1:
            m = bpoint(Le, Ue)
            if m is None: return None
        cA = dict(cell.cons); cA[t] = (Lb, m); cB = dict(cell.cons); cB[t] = (m, Ub)
        return Cell(tuple(cell), cA), Cell(tuple(cell), cB)
    def err_axes(cell, x):
        """axes ranked by the relaxation error a_t (w(s*_t) - z*_t) at the LP point (adjacent pairs map to their gap)"""
        g = x[:Q]; s = INC @ g; out = []; I = iv(cell)
        for t in range(NP):
            if aN[t] == 0: continue
            e = a[t] * (float(wf(s[t])) - x[Q + t]); i, j = PAIRS[t]
            if j - i == 1: out.append((e, i)); continue
            Le, Ue = I[t]
            if Ue - Le < MINPW:   # a narrow pair range: split its widest gap instead
                out.append((e, max(range(i, j), key=lambda r: cell[r][1] - cell[r][0])))
            else: out.append((e, Q + t))
        out.sort(reverse=True)
        return out
    def lpval(cell, tabs):
        c2 = tighten(cell)
        if c2 is None: return 1e9
        I = iv(c2)
        C = [mcands(I[t][0], I[t][1], *tabs[:5]) if aN[t] > 0 else [] for t in range(NP)]
        r_ = mtest1_lp(c2, C)
        return r_
    def mtest1_lp(cell, C):
        lo = np.array([x[0] for x in cell]) / SC; hi = np.array([x[1] for x in cell]) / SC; I0 = iv0(cell)
        A_ub = []; b_ub = []
        for t, (i, j) in enumerate(PAIRS):
            for m__ in C[t]:
                al, dd, p = m__[0], m__[1], m__[2]
                row = np.zeros(Q + NP); row[i:j] = dd / U1; row[Q + t] = -1.0
                A_ub.append(row); b_ub.append(-(al / U - dd / U1 * p / SC))
        for t, (Lb, Ub) in cell.cons.items():
            i, j = PAIRS[t]; L0, U0 = I0[t]
            if Ub is not None and Ub < U0:
                row = np.zeros(Q + NP); row[i:j] = 1.0; A_ub.append(row); b_ub.append(Ub / SC)
            if Lb is not None and Lb > L0:
                row = np.zeros(Q + NP); row[i:j] = -1.0; A_ub.append(row); b_ub.append(-Lb / SC)
        r_ = _linprog(np.concatenate([b, a]), A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                      bounds=list(zip(lo, hi)) + [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)], method='highs')
        if r_.status == 2: return 1e9
        if r_.status != 0: return -1e9
        return r_.fun
    def choose(cell, tabs):
        x = LASTX[0]
        if x is None:
            ws = [(cell[r][1] - cell[r][0], r) for r in range(Q)]
            return max(ws)[1]
        ranked = [ax for e, ax in err_axes(cell, x)]
        seen = []
        GW = int(os.environ.get("GUARDW", "0"))
        def wide(ax):
            if ax < Q: return cell[ax][1] - cell[ax][0] >= GW
            Le, Ue = iv(cell)[ax - Q]; return Ue - Le >= GW
        if GW and any(wide(ax_) for ax_ in ranked): ranked = [ax_ for ax_ in ranked if wide(ax_)] + [ax_ for ax_ in ranked if not wide(ax_)]
        for ax in ranked:
            if ax in seen: continue
            if children(cell, ax) is not None: seen.append(ax)
            if SPLIT == "err" and seen: return seen[0]
            if len(seen) >= PFK: break
        if not seen: return max((cell[r][1] - cell[r][0], r) for r in range(Q))[1]
        best = None
        for ax in seen:
            for mode in ((0, 1) if BSPLIT else (0,)):
                ch_ = children(cell, ax, mode)
                if ch_ is None: continue
                A_, B_ = ch_
                va, vb = lpval(A_, tabs), lpval(B_, tabs)
                sc = ((va >= cF) + (vb >= cF), min(va, vb), va + vb)
                if best is None or sc > best[0]: best = (sc, ax, mode)
        CMODE[0] = best[2]
        return best[1]
    NODES = [0]; NBS = [0]
    def subdivide(cell, depth, tabs, parent=None):
        c2 = tighten(cell)
        if c2 is None:
            count[0] += 1; count[7] += 1
            return ('leaf', cell, 7, None)
        cell = c2
        NODEC[len(cell.cons)] += 1
        d = decide(cell, *tabs)
        if d is not None:
            count[0] += 1
            if d[0]: count[d[0]] += 1
            if verbose and count[0] % 5000 == 0:
                print(f"  ... {count[0]} leaves (Z {count[1]}, M {count[6]}, empty {count[7]}, refl {count[0] - count[1] - count[6] - count[7]}) "
                      f"nodes {NODES[0]} LP {MSTAT['lp']} ({time.time()-t0:.0f}s)", flush=True)
            return ('leaf', cell, d[0], d[1])
        if depth > int(os.environ.get("MAXD", "160")) or count[0] > max_leaves:
            if verbose:
                print("  stuck", tuple(cell), cell.cons, flush=True)
                try:
                    I = iv(cell); res = mtest(cell, *tabs[:5]); x = LASTX[0]
                    print("   LP rel", res[0], "zlow rel", (zlow(cell, tabs[5]) - CSU) / CSU, flush=True)
                    if x is not None:
                        for e, ax in err_axes(cell, x)[:6]:
                            t_ = ax - Q if ax >= Q else PAIRS.index((ax, ax + 1))
                            cs = mcands(I[t_][0], I[t_][1], *tabs[:5])
                            print(f"   err {e:.3e} axis {ax} term {PAIRS[t_]} range {I[t_]} width {I[t_][1] - I[t_][0]} cands {len(cs)} inreg {inreg(*I[t_])} "
                                  f"w(s*) {float(wf(INC[t_] @ x[:Q])):.6f} z* {x[Q + t_]:.6f}", flush=True)
                except Exception as e_: print("   diag failed", repr(e_), flush=True)
            return None
        CMODE[0] = 0; ax = choose(cell, tabs); mode = CMODE[0]
        ch = children(cell, ax, mode)
        if mode: NBS[0] += 1
        if ch is None:
            for ax in range(Q):
                ch = children(cell, ax)
                if ch is not None: break
        if ch is None:
            if verbose:
                print("  stuck (point cell)", tuple(cell), cell.cons, flush=True)
                I = iv(cell); I0 = iv0(cell)
                Call = [mcands(I[t][0], I[t][1], *tabs[:5]) for t in range(NP)]
                print("   ranges", I[:7], "box sums", I0[:7], flush=True)
                print("   cands per term", [len(c) for c in Call], flush=True)
                res = mtest1(cell, Call, *tabs[:5])
                print("   mtest1 ->", res[0], res[1], flush=True)
                z = sum(bN[r] * cell[r][0] for r in range(Q)) / SA + sum(a[t] * max(c[0] for c in Call[t]) / U for t in range(NP))
                print("   point bound with best constants", z, "cF", cF, flush=True)
            return None
        NODES[0] += 1
        X = subdivide(ch[0], depth + 1, tabs, cell)
        if X is None: return None
        Y = subdivide(ch[1], depth + 1, tabs, cell)
        if Y is None: return None
        return ('split', cell, ax, (mode or None), X, Y)
    count = [0] * 9
    est = (lbE1, lbPE, lbME, ptw, ptd, lbE)
    nodes = {}
    # REPLAY=dump.pkl: no bisection; the dump's trees are replayed as the kernel would walk them: at every node the
    # tightening (T1) of the incoming cell, which must equal the dump's cell; a split recomputes its children from the
    # tightened cell and the axis; a leaf keeps its kind and payload.  The leaves are then re-verified on the built tables.
    REPLAY = os.environ.get("REPLAY"); REPLAY_TREES = None; RPL = collections.Counter()
    if REPLAY is not None:
        import pickle as _pk
        REPLAY_TREES = _pk.load(open(REPLAY, "rb"))["trees"]
    def replay(cell_in, t):
        c = tighten(cell_in)
        if t[0] == 'leaf' and t[3] == 7:
            assert c is None, ("dump says empty, T1 does not", tuple(cell_in))
            count[0] += 1; count[7] += 1; RPL['empty'] += 1
            return ('leaf', cell_in, 7, None)
        assert c is not None, ("T1 empties a cell the dump kept", tuple(cell_in))
        assert tuple(c) == tuple(t[1]) and c.cons == t[2], ("tightened cell differs from the dump", tuple(c), tuple(t[1]))
        if t[0] == 'split':
            md = t[6] if len(t) > 6 else 0          # the BSPLIT mode (dumps from 10-07 on)
            ch = children(c, t[3], md); RPL['split'] += 1
            return ('split', c, t[3], md or None, replay(ch[0], t[4]), replay(ch[1], t[5]))
        count[0] += 1
        if t[3]: count[t[3]] += 1
        RPL[t[3]] += 1
        return ('leaf', c, t[3], t[4])
    _rs = [int(x) for x in os.environ["ROOTSEL"].split(",")] if os.environ.get("ROOTSEL") else None
    for _ri, tup in enumerate(itertools.product(*[range(len(bd)) for bd in bads])):
        if _rs is not None and _ri not in _rs: continue
        cell = Cell(tuple(bads[r][tup[r]] for r in range(Q)), {})
        _c0 = count[0]
        if REPLAY is not None: nd = replay(cell, REPLAY_TREES[len(nodes)])
        else: nd = subdivide(cell, 0, est)
        if verbose: print(f"  root {_ri} {tup}: {count[0] - _c0} leaves ({time.time()-t0:.0f}s)", flush=True)
        if nd is None: return None
        nodes[tup] = nd
    if verbose: print(f"  bisection: {count[0]} leaves (Z {count[1]}, M {count[6]}, empty {count[7]}), {NODES[0]} splits, {NBS[0]} at region boundaries ({time.time()-t0:.0f}s)", flush=True)
    # ---- tables from the queries, re-verification (fix-up) on the built tables ----
    leaves = []
    def collect(nd):
        if nd[0] == 'leaf': leaves.append(nd)
        else: collect(nd[4]); collect(nd[5])
    for nd in nodes.values(): collect(nd)
    qz, qd, qz1 = set(), set(), set()
    for _, cell, kind, pay in leaves:
        I = iv(cell)
        if kind == 1: qz.update(I)
        elif kind == 6:
            Q_ = {'z': set(), 'd': set(), 'p': set()}
            meval(cell, pay, *est[:5], Q_=Q_); qz1 |= Q_['z']; qd |= Q_['d']
    qz = {pc for (lo, hi) in qz for pc in pieces(lo, hi, SH, MINW)} | qz1
    P.need(qz)
    for j in range(P.X0 >> P.PB, ((P.xmax - 1) >> P.PB) + 1): P.res[j] = WMIN
    P.build(); PP.need(qd); PM.need(qd)
    if DENSE:
        for X_ in (PP, PM):
            for j in range(X_.X0 >> X_.PB, ((X_.xmax - 1) >> X_.PB) + 1): X_.res[j] = DLO if (j << 10) < XD else DHI
    PP.build(); PM.build()
    Plb3 = lb3_of(P.lb, SH, MINW)
    built = (P.lb, PP.lb, PM.lb, ptw, ptd, Plb3); BUILT[0] = True
    fixed = [0]
    def ok_on(cell, kind, pay, tabs):
        if kind in (0, 7, 8): return True
        if kind == 1:
            return sum(bN[r] * cell[r][0] for r in range(Q)) >= cN * SC or zlow(cell, tabs[5]) >= CSU
        if kind == 6: return LPACCEPT or meval(cell, pay, *tabs[:5])
        return False
    def fix(nd, depth=0):
        if nd[0] == 'split':
            return ('split', nd[1], nd[2], nd[3], fix(nd[4], depth + 1), fix(nd[5], depth + 1))
        _, cell, kind, pay = nd
        if ok_on(cell, kind, pay, built): return nd
        fixed[0] += 1
        if REPLAY is not None: return nd
        r = subdivide(cell, depth, built)
        assert r is not None, ("fix-up failed", cell)
        return r
    nodes = {k: fix(v) for k, v in nodes.items()}
    leaves = []
    for nd in nodes.values(): collect(nd)
    pts = set(); bad = 0; kinds = collections.Counter(); nzY = collections.Counter(); ncons = collections.Counter()
    bits = 0; nsplit = 0; nsplit_pair = 0; YBITS = []; YW0 = int(os.environ.get("YW0", "12"))
    NCP = sum(1 for (i, j) in PAIRS if j - i >= 2); AXB = (Q + NCP - 1).bit_length(); CB_ = (NCP - 1).bit_length()
    def walkbits(nd):
        """split 1 + AXB axis bits (5 at Q = 7, 6 at Q = 8); an empty cell 0 bits (the kernel's tightening finds it); a leaf 2 bits (leaf, kind);
        an M leaf adds the minorant fields and the multiplier list: per entry 1 + 5 (constraint) + 1 (side) + the value,
        and 1 closing bit; a Farkas leaf (kind 8) is budgeted as 3 entries"""
        nonlocal bits, nsplit, nsplit_pair
        if nd[0] == 'split':
            nsplit += 1; nsplit_pair += nd[2] >= Q; bits += 1 + AXB + (1 if BSPLIT else 0)
            walkbits(nd[4]); walkbits(nd[5]); return
        _, cell, kind, pay = nd
        if kind == 7: return
        if kind == 0: bits += 1; return
        bits += 2
        if kind == 8:
            bits += 1 + 3 * 7; YBITS.extend([YW0] * 3); return
        if kind == 6:
            mc, Ys = pay
            for t in range(NP):
                if aN[t] == 0: continue
                k_ = mc[t][0]; bits += 2 + (JB if k_ >= 1 else 0) + (JB if k_ == 3 else 0) + (10 if k_ >= 2 else 0)
            bits += 1 + (2 + CB_) * len(Ys)
            for k_, v_ in Ys.items(): YBITS.append(v_.bit_length())
    for nd in nodes.values(): walkbits(nd)
    YW = max(YBITS) if YBITS else 0; bits += YW * len(YBITS)     # fixed-width multiplier fields
    for _, cell, kind, pay in leaves:
        kinds[kind] += 1
        if not ok_on(cell, kind, pay, built): bad += 1
        if kind == 6:
            Q_ = {'z': set(), 'd': set(), 'p': set()}
            meval(cell, pay, *built[:5], Q_=Q_); pts |= Q_['p']
            nzY[len(pay[1])] += 1; ncons[len(cell.cons)] += 1
    tzb = {}
    for x in pts:
        o = x & 1023; tz = min(10, (o & -o).bit_length() - 1) if o else 10
        tzb[x >> 10] = min(tzb.get(x >> 10, 10), tz)
    st = dict(w=P.stats(), d=PP.stats(), points=len(pts), ptcells=sum(1 << (10 - r) for r in tzb.values()))
    if verbose:
        print(f"  fix-up: {fixed[0]} re-decided; tables: w {st['w']['finest']} cells, d {st['d']['finest']} cells, "
              f"{len(pts)} points ({st['ptcells']} point cells); failing {bad} ({time.time()-t0:.0f}s)", flush=True)
    return dict(P=P, PP=PP, PM=PM, nodes=nodes, covers=covers, bads=bads, S=S, leaves=leaves, nleaves=len(leaves), kinds=dict(kinds),
                nzY=dict(nzY), ncons=dict(ncons), bits=bits, nsplit=nsplit, nsplit_pair=nsplit_pair, pts=pts, stats=st, bad=bad,
                built=built, cN=cN, iv=iv, Plb3=Plb3, ZLOG=ZLOG, RPL=dict(RPL), tighten=tighten, children=children, Cell=Cell, meval=meval, gpt=gpt, mweights=mweights, MSTAT=MSTAT, YW=YW, nY=len(YBITS), JB=JB, NODEC=dict(NODEC), VDIAG=dict(VDIAG))
