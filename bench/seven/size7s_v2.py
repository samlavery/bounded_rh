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

Q = 6
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
    A = 1 << JCQ
    def dec(mode, l, u):
        if mode == 0:
            m = ((l + A - 1) >> JCQ) << JCQ; return m if m <= u else l
        if mode == 1:
            m = (u >> JCQ) << JCQ; return m if m >= l else u
        m = (l + u) >> 1; mm = (m >> JCQ) << JCQ
        return mm if mm >= l else m
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

def run(cN, aN, bN, JCQ=8, dmin=5, PED=4, basins=(), verbose=True, max_leaves=4 * 10**6, WF=WFRAC, WMIN=6, SH=4, MINW=1024, probe=False):
    t0 = time.time()
    a = np.array(aN, float) / SA; b = np.array(bN, float) / SA
    P = PyrF(wcell, dmin=WMIN, PE=5, PB=10, MAXA=4, U=U, FUEL=14)
    PP = PyrF(fP, dmin=dmin, PE=PED, PB=10, MAXA=4, U=U1, FUEL=14)
    PM = PyrF(fM, dmin=dmin, PE=PED, PB=10, MAXA=4, U=U1, FUEL=14)
    EMX = P.EM
    adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
    S = [-(-(4 * cN * SC) // (bN[r] * 4 * QUARTER)) * QUARTER for r in range(Q)]
    covers = [phase1(cN, adj[r], S[r]) for r in range(Q)]
    bads = [cv[1] for cv in covers]
    dec = make_q(JCQ)
    CSU = cN * SC * U
    @lru_cache(maxsize=None)
    def E(l, i):
        if l < WMIN: return E(WMIN, i >> (WMIN - l))
        if l <= WMIN: return min(WZ(i << l, (i + 1) << l) * U // SW, EMX)
        return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
    @lru_cache(maxsize=None)
    def EP(l, i):
        if l < dmin: return EP(dmin, i >> (dmin - l))
        if l <= 13: return min(fP(i << l, (i + 1) << l), EMX)
        return min(EP(l - 1, 2 * i), EP(l - 1, 2 * i + 1))
    @lru_cache(maxsize=None)
    def EMd(l, i):
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
    lbE, lbPE, lbME = lb3_of(mk(E, P), SH, MINW), mk(EP, PP), mk(EMd, PM)
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
        for t, (lo, hi) in enumerate(iv(box)): s += aN[t] * lb(lo, hi)
        return tot + s * SC
    NEG = -(1 << 200)
    def sint(box, q, T, lbw, lbP, lbM, pw, pd):
        """the integer slope test (value comparable to CSU), exactly as the Lean `stest`"""
        if any(not (box[r][0] <= q[r] <= box[r][1]) for r in range(Q)): return NEG
        I = iv(box); lhs_t = 0; Rsum = 0
        Pt = [0] * NP; Mt = [0] * NP
        for t, (i, j) in enumerate(PAIRS):
            lo, hi = I[t]
            if T >> t & 1:
                qt = sum(q[i:j]); p, m = pd(qt)
                if p < 1 or m < 1: return NEG
                Pt[t] = p; Mt[t] = m
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
            else:
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
            pen[t] = max(up, dn)
        tay = a * (wq - pen); zer = a * w0; slope = a * w1q
        use = np.ones(NP, bool)
        def total(use):
            g = b + INC.T @ (slope * use)
            return float(b @ qq + np.minimum(g * lo, g * hi).sum() + np.where(use, tay, zer).sum())
        cur = total(use)
        for _ in range(passes):
            changed = False
            for t in np.argsort(-pen):
                use[t] = not use[t]; v = total(use)
                if v > cur: cur = v; changed = True
                else: use[t] = not use[t]
            if not changed: break
        return cur, sum(1 << t for t in range(NP) if use[t])
    def scands(box):
        cen = [(x[0] + x[1]) / 2 / SC for x in box]
        g = b + INC.T @ (a * w1f(INC @ np.array(cen)))
        m1 = tuple(0 if g[r] >= 0 else 1 for r in range(Q)); m2 = (2,) * Q
        out = []
        for modes in (m1, m2):
            q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
            v, T = sfloat(box, q); out.append((v, modes, q, T))
        out.sort(key=lambda z: -z[0])
        return out
    cF = cN / SA
    def flower(box):
        if inbas(box): return cF
        zf = sum(b[r] * box[r][0] / SC for r in range(Q)) + sum(a[t] * frq('w', l, h) for t, (l, h) in enumerate(iv(box)))
        if zf >= cF: return zf
        cen = [(x[0] + x[1]) / 2 / SC for x in box]
        g = b + INC.T @ (a * w1f(INC @ np.array(cen)))
        best = zf
        for modes in (tuple(0 if g[r] >= 0 else 1 for r in range(Q)), (2,) * Q):
            q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
            best = max(best, sfloat(box, q, passes=1)[0])
        return best
    count = [0, 0, 0, 0]
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
    def decide(box, lbw, lbP, lbM, pw, pd):
        """leaf kind and payload, or None"""
        if box[0][0] > box[Q - 1][1]: return (0, None)
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: return (1, None)
        if inbas(box): return (3, None)
        if zlow(box, lbw) >= CSU: return (1, None)
        for v, modes, q, T in scands(box):
            if v < cF * 0.999: break
            if sint(box, q, T, lbw, lbP, lbM, pw, pd) >= CSU: return (2, (modes, T))
        return None
    def subdivide(box, depth, tabs):
        d = decide(box, *tabs)
        if d is not None:
            count[0] += 1; count[d[0]] += 1 if d[0] in (1, 2, 3) else 0
            return ('leaf', box, d[0], d[1])
        if depth > 70 or count[0] > max_leaves or max(x[1] - x[0] for x in box) <= 1:
            if verbose: print("  stuck", box, flush=True)
            return None
        k = choose(box); mid = (box[k][0] + box[k][1]) // 2
        A_ = list(box); A_[k] = (box[k][0], mid); B_ = list(box); B_[k] = (mid, box[k][1])
        X = subdivide(tuple(A_), depth + 1, tabs)
        if X is None: return None
        Y = subdivide(tuple(B_), depth + 1, tabs)
        if Y is None: return None
        return ('split', box, k, mid, X, Y)
    est = (lbE, lbPE, lbME, ptw, ptd)
    if probe: return dict(est=est, sint=sint, sfloat=sfloat, scands=scands, dec=dec, zlow=zlow, flower=flower, decide=decide, iv=iv)
    nodes = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        nd = subdivide(box, 0, est)
        if nd is None: return None
        nodes[tup] = nd
    if verbose: print(f"  bisection: {count[0]} leaves (Z {count[1]}, S {count[2]}, basin {count[3]}) ({time.time()-t0:.0f}s)", flush=True)
    # ---- tables from the queries ----
    leaves = []
    def collect(nd):
        if nd[0] == 'leaf': leaves.append(nd)
        else: collect(nd[4]); collect(nd[5])
    for nd in nodes.values(): collect(nd)
    qz, qd = set(), set()
    for _, box, kind, pay in leaves:
        I = iv(box)
        if kind == 1: qz.update(I)
        elif kind == 2:
            modes, T = pay; q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
            for t, (i, j) in enumerate(PAIRS):
                lo, hi = I[t]
                if T >> t & 1:
                    qt = sum(q[i:j])
                    if hi > qt: qd.add((qt, hi))
                    if qt > lo: qd.add((lo, qt))
                else: qz.add((lo, hi))
    qz = {pc for (lo, hi) in qz for pc in pieces(lo, hi, SH, MINW)}
    P.need(qz)
    for j in range(P.X0 >> P.PB, ((P.xmax - 1) >> P.PB) + 1): P.res[j] = WMIN
    P.build(); PP.need(qd); PP.build(); PM.need(qd); PM.build()
    Plb3 = lb3_of(P.lb, SH, MINW)
    built = (Plb3, PP.lb, PM.lb, ptw, ptd)
    fixed = [0, 0]
    def fix(nd, depth=0):
        if nd[0] == 'split':
            return ('split', nd[1], nd[2], nd[3], fix(nd[4], depth + 1), fix(nd[5], depth + 1))
        _, box, kind, pay = nd
        if kind in (0, 3) or sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: return nd
        if kind == 1 and zlow(box, Plb3) >= CSU: return nd
        if kind == 2:
            modes, T = pay; q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
            if sint(box, q, T, *built) >= CSU: return nd
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
            nS += 1; modes, T = pay; q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
            for t, (i, j) in enumerate(PAIRS):
                if T >> t & 1: pts.add(sum(q[i:j]))
            if sint(box, q, T, *built) < CSU: bad += 1
        elif kind == 3: nB += 1
    tzb = {}
    for x in pts:
        o = x & 1023; tz = min(10, (o & -o).bit_length() - 1) if o else 10
        tzb[x >> 10] = min(tzb.get(x >> 10, 10), tz)
    st = dict(w=P.stats(), d=PP.stats(), points=len(pts), ptcells=sum(1 << (10 - r) for r in tzb.values()))
    if verbose:
        print(f"  fix-up: {fixed[0]} re-decided; tables: w {st['w']['finest']} cells, d {st['d']['finest']} cells, "
              f"{len(pts)} points ({st['ptcells']} point cells); failing {bad} ({time.time()-t0:.0f}s)", flush=True)
    return dict(P=P, PP=PP, PM=PM, nodes=nodes, covers=covers, bads=bads, S=S, leaves=leaves, nleaves=len(leaves),
                nZ=nZ, nS=nS, nB=nB, pts=pts, stats=st, bad=bad, dec=dec, sint=sint, built=built, cN=cN, sfloat=sfloat, iv=iv, Plb3=Plb3, pieces=lambda lo, hi: pieces(lo, hi, SH, MINW))
