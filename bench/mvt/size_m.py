"""Integer-faithful sizing of the weighted six-point certificate with two leaf tests:
  Z : the zero-order pyramid test of the accepted certificate (each pair term bounded by a lower bound of w on its
      pair-sum interval, read from the w pyramid);
  M : the mean-value test at a centre m of the box (any point of the box):
        U Σ b_r m_r + SC Σ a_t v_t  >=  cN SC U + (U/U1) Σ_r [ (m_r - l_r) Pos_r + (u_r - m_r) Neg_r ]
      v_t   = point lower bound of w at s_t(m) (degenerate integer cell [x, x], units 1/U),
      Pos_r = (U1 b_r + KU1 A_r) - Σ_{t∋r} a_t pM_t   (truncated at 0),
      Neg_r = KU1 A_r - (U1 b_r + Σ_{t∋r} a_t pP_t)   (truncated at 0),
      pP_t / pM_t = lower bounds of (w' + 2) U1 and (2 - w') U1 on the pair-sum interval, read from two derivative
      pyramids with the same cover arithmetic as the w pyramid (0 = no information: the test fails).
Leaves are tested Z first; a leaf records which test it passes.  After the bisection the tables are built from the
queries the leaves make (Z leaves: the w pyramid; M leaves: the derivative pyramids and the point table) and every
leaf is re-verified on the built tables.
Usage (module): run(cN, ...) -> dict; CLI: size_m.py DELTA [JC]"""
import os, sys, time, itertools
from functools import lru_cache
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "pyr"))
sys.setrecursionlimit(1000000)
from size_pyr import phase1, PAIRS, Q, AN, BN, SA, SC, QUARTER, WFRAC
from pyr_table import Pyr
from wz import WZ, SW
from w1cell import fP, fM, U1, KU1

U = 10**10
RU = U // U1
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]

class PyrF(Pyr):
    """a pyramid whose finest cells carry the bound `f(LN, UN)` (0 = no information); no block is refined below
    level `dmin` (reads of finer cells get the ancestor at `dmin`)"""
    def __init__(self, f, dmin=0, **kw):
        super().__init__(**kw); self.f = f; self.dmin = dmin
    def need(self, queries):
        super().need(queries)
        for j in self.res: self.res[j] = max(self.res[j], self.dmin)
    def cellval(self, l, i):
        return min(self.f(i << l, (i + 1) << l), self.EM)

def make_centre(JC):
    def centre(l, u):
        m = (l + u) >> 1
        if JC:
            w = u - l; j = JC if JC > 0 else max(0, w.bit_length() + JC)
            mm = (m >> j) << j
            if mm >= l: m = mm
        return m
    return centre

def make_pick(JC, corner):
    centre = make_centre(JC)
    A = 1 << JC
    def up(l, u):
        mm = (u >> JC) << JC
        return mm if mm >= l else u
    def lo(l, u):
        mm = ((l + A - 1) >> JC) << JC
        return mm if mm <= u else l
    def pick(l, u, Pos, Neg):
        if corner == "lean":
            return lo(l, u) if Pos >= Neg else up(l, u)
        if corner == "lean2":
            # the centre when the two bounds are within a factor 2, else the leaning corner
            if 2 * Neg <= Pos: return lo(l, u)
            if 2 * Pos <= Neg: return up(l, u)
            return centre(l, u)
        if corner:
            if Pos == 0: return up(l, u)
            if Neg == 0: return lo(l, u)
        return centre(l, u)
    return pick

def run(cN, PE=5, PB=10, MAXA=4, FUEL=14, JC=0, mode="ZM", max_leaves=4 * 10**6, verbose=True, aN=AN, bN=BN, corner=False, dmin=0, PED=5, MAXAD=4):
    t0 = time.time()
    P = Pyr(PE=PE, PB=PB, MAXA=MAXA, U=U, FUEL=FUEL)
    PP = PyrF(fP, dmin=dmin, PE=PED, PB=PB, MAXA=MAXAD, U=U1, FUEL=FUEL)
    PM = PyrF(fM, dmin=dmin, PE=PED, PB=PB, MAXA=MAXAD, U=U1, FUEL=FUEL)
    EMX = P.EM
    AR = [sum(aN[t] for t in TS[r]) for r in range(Q)]
    adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
    S = [-(-(4 * cN * SC) // (bN[r] * 4 * QUARTER)) * QUARTER for r in range(Q)]
    for r in range(Q): assert cN * SC <= bN[r] * S[r]
    covers = [phase1(cN, adj[r], S[r]) for r in range(Q)]
    bads = [cv[1] for cv in covers]
    if verbose: print(f"cN={cN}: covers done ({time.time()-t0:.0f}s) bad sizes {[len(b) for b in bads]}", flush=True)
    centre = make_centre(JC)
    pick = make_pick(JC, corner)
    # ---- direct-entry estimates (never above what the built tables store) ----
    @lru_cache(maxsize=None)
    def E(l, i):
        if l <= 13: return min(WZ(i << l, (i + 1) << l) * U // SW, EMX)
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
    lbE, lbPE, lbME = mk(E, P), mk(EP, PP), mk(EMd, PM)
    @lru_cache(maxsize=None)
    def ptv(x): return min(WZ(x, x) * U // SW, EMX)
    CSU = cN * SC * U
    def zlow(box, lb):
        tot = U * sum(bN[r] * box[r][0] for r in range(Q)); s = 0
        for t, (i, j) in enumerate(PAIRS):
            lo = 0; hi = 0
            for r in range(i, j): lo += box[r][0]; hi += box[r][1]
            s += aN[t] * lb(lo, hi)
        return tot + s * SC
    NEG = -(1 << 200)
    def mlow(box, lbP, lbM, pt):
        pP = [0] * len(PAIRS); pM = [0] * len(PAIRS)
        for t, (i, j) in enumerate(PAIRS):
            lo = 0; hi = 0
            for r in range(i, j): lo += box[r][0]; hi += box[r][1]
            a = lbP(lo, hi); b = lbM(lo, hi)
            if a == 0 or b == 0: return NEG
            pP[t] = a; pM[t] = b
        PN = []
        for r in range(Q):
            Pos = max(0, U1 * bN[r] + KU1 * AR[r] - sum(aN[t] * pM[t] for t in TS[r]))
            Neg = max(0, KU1 * AR[r] - U1 * bN[r] - sum(aN[t] * pP[t] for t in TS[r]))
            PN.append((Pos, Neg))
        m = [pick(box[r][0], box[r][1], *PN[r]) for r in range(Q)]
        lhs = U * sum(bN[r] * m[r] for r in range(Q)); sv = 0
        for t, (i, j) in enumerate(PAIRS):
            sv += aN[t] * pt(sum(m[i:j]))
        lhs += SC * sv
        pen = 0
        for r in range(Q):
            pen += (m[r] - box[r][0]) * PN[r][0] + (box[r][1] - m[r]) * PN[r][1]
        return lhs - RU * pen
    def mpoints(box):
        """the points the mean-value test reads for the box (centres from the direct estimates)"""
        pP = []; pM = []
        for (i, j) in PAIRS:
            lo = sum(box[r][0] for r in range(i, j)); hi = sum(box[r][1] for r in range(i, j))
            pP.append(lbPE(lo, hi)); pM.append(lbME(lo, hi))
        m = []
        for r in range(Q):
            Pos = max(0, U1 * bN[r] + KU1 * AR[r] - sum(aN[t] * pM[t] for t in TS[r]))
            Neg = max(0, KU1 * AR[r] - U1 * bN[r] - sum(aN[t] * pP[t] for t in TS[r]))
            m.append(pick(box[r][0], box[r][1], Pos, Neg))
        return [sum(m[i:j]) for (i, j) in PAIRS]
    def lower(box):
        z = zlow(box, lbE)
        if mode == "Z" or z >= CSU: return z
        return max(z, mlow(box, lbPE, lbME, ptv))
    def choose_axis(box):
        w = [b[1] - b[0] for b in box]; mw = max(w); best = None
        for k in range(Q):
            if w[k] == 0: continue
            mid = (box[k][0] + box[k][1]) // 2
            a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
            la, lb2 = lower(tuple(a)), lower(tuple(b2))
            both = la >= CSU and lb2 >= CSU
            if w[k] * WFRAC < mw and not both: continue
            score = ((la >= CSU) + (lb2 >= CSU), la + lb2)
            if best is None or score > best[0]: best = (score, k)
        return best[1]
    count = [0, 0, 0]          # leaves, Z leaves, M leaves
    def subdivide(box, depth=0):
        """('leaf', box, kind) kind 0 = trivial (half-space / linear), 1 = Z, 2 = M; or ('split', box, k, m, A, B)"""
        if box[0][0] > box[Q - 1][1]: count[0] += 1; return ('leaf', box, 0)
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: count[0] += 1; return ('leaf', box, 1)
        z = zlow(box, lbE)
        if z >= CSU: count[0] += 1; count[1] += 1; return ('leaf', box, 1)
        if mode != "Z" and mlow(box, lbPE, lbME, ptv) >= CSU: count[0] += 1; count[2] += 1; return ('leaf', box, 2)
        if depth > 60 or count[0] > max_leaves: return None
        if max(b[1] - b[0] for b in box) <= 1: return None
        k = choose_axis(box); mm = (box[k][0] + box[k][1]) // 2
        a = list(box); a[k] = (box[k][0], mm); b2 = list(box); b2[k] = (mm, box[k][1])
        A = subdivide(tuple(a), depth + 1)
        if A is None: return None
        B = subdivide(tuple(b2), depth + 1)
        if B is None: return None
        return ('split', box, k, mm, A, B)
    nodes = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        nd = subdivide(box)
        if nd is None:
            if verbose: print("FAIL at root", tup, count)
            return None
        nodes[tup] = nd
    if verbose: print(f"  bisection: {count[0]} leaves (Z {count[1]}, M {count[2]}) ({time.time()-t0:.0f}s)", flush=True)
    leaves = []
    def collect(nd):
        if nd[0] == 'leaf': leaves.append((nd[1], nd[2]))
        else: collect(nd[4]); collect(nd[5])
    for nd in nodes.values(): collect(nd)
    def terms(box):
        return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
    qz, qm, pts = set(), set(), set()
    for b, kind in leaves:
        if kind == 1: qz.update(terms(b))
        elif kind == 2:
            qm.update(terms(b))
            pts.update(mpoints(b))
    P.need(qz); P.build()
    PP.need(qm); PP.build(); PM.need(qm); PM.build()
    # ---- fix-up on the built tables: a leaf whose test fails there (the built entries can move a centre) is
    # re-decided by the other test or split further, every decision now taken on the built tables ----
    ptB = lru_cache(maxsize=None)(ptv)
    def zB(b): return zlow(b, P.lb)
    def mB(b): return mlow(b, PP.lb, PM.lb, ptB)
    def lowerB(b):
        z = zB(b)
        return z if z >= CSU else max(z, mB(b))
    def choose_axisB(box):
        w = [b[1] - b[0] for b in box]; mw = max(w); best = None
        for k in range(Q):
            if w[k] == 0: continue
            mid = (box[k][0] + box[k][1]) // 2
            a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
            la, lb2 = lowerB(tuple(a)), lowerB(tuple(b2))
            both = la >= CSU and lb2 >= CSU
            if w[k] * WFRAC < mw and not both: continue
            score = ((la >= CSU) + (lb2 >= CSU), la + lb2)
            if best is None or score > best[0]: best = (score, k)
        return best[1]
    fixed = [0, 0]
    def subdivideB(box, depth):
        if box[0][0] > box[Q - 1][1]: return ('leaf', box, 0)
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: return ('leaf', box, 1)
        if zB(box) >= CSU: return ('leaf', box, 1)
        if mB(box) >= CSU: return ('leaf', box, 2)
        assert depth < 60 and max(b[1] - b[0] for b in box) > 1, ("fix-up failed", box)
        fixed[1] += 1
        k = choose_axisB(box); mm = (box[k][0] + box[k][1]) // 2
        a = list(box); a[k] = (box[k][0], mm); b2 = list(box); b2[k] = (mm, box[k][1])
        return ('split', box, k, mm, subdivideB(tuple(a), depth + 1), subdivideB(tuple(b2), depth + 1))
    def fix(nd, depth=0):
        if nd[0] == 'split':
            return ('split', nd[1], nd[2], nd[3], fix(nd[4], depth + 1), fix(nd[5], depth + 1))
        b, kind = nd[1], nd[2]
        if kind == 0 or sum(bN[r] * b[r][0] for r in range(Q)) >= cN * SC: return nd
        if kind == 1 and zB(b) >= CSU: return nd
        if kind == 2 and mB(b) >= CSU: return nd
        fixed[0] += 1
        return subdivideB(b, depth)
    nodes = {k: fix(v) for k, v in nodes.items()}
    leaves = []
    for nd in nodes.values(): collect(nd)
    count = [len(leaves), sum(1 for _, k in leaves if k == 1), sum(1 for _, k in leaves if k == 2)]
    if verbose and fixed[0]: print(f"  fix-up: {fixed[0]} leaves re-decided, {fixed[1]} new splits", flush=True)
    PT = {}
    for b, kind in leaves:
        if kind != 2: continue
        tm = terms(b); pPb = [PP.lb(lo, hi) for lo, hi in tm]; pMb = [PM.lb(lo, hi) for lo, hi in tm]
        m = []
        for r in range(Q):
            Pos = max(0, U1 * bN[r] + KU1 * AR[r] - sum(aN[t] * pMb[t] for t in TS[r]))
            Neg = max(0, KU1 * AR[r] - U1 * bN[r] - sum(aN[t] * pPb[t] for t in TS[r]))
            m.append(pick(b[r][0], b[r][1], Pos, Neg))
        for (i, j) in PAIRS:
            x = sum(m[i:j])
            if x not in PT: PT[x] = ptv(x)
    bad = 0
    for b, kind in leaves:
        if kind == 0: continue
        if sum(bN[r] * b[r][0] for r in range(Q)) >= cN * SC: continue
        if kind == 1:
            if zlow(b, P.lb) < CSU: bad += 1
        elif mlow(b, PP.lb, PM.lb, PT.__getitem__) < CSU: bad += 1
    st = dict(w=P.stats(), dP=PP.stats(), dM=PM.stats(), points=len(PT))
    if verbose:
        print(f"  tables: w {st['w']}\n          d+ {st['dP']}\n          d- {st['dM']}\n          points {len(PT)}; "
              f"leaves failing on the built tables: {bad} ({time.time()-t0:.0f}s)", flush=True)
    return dict(P=P, PP=PP, PM=PM, PT=PT, nodes=nodes, covers=covers, bads=bads, S=S, nleaves=count[0], nZ=count[1],
                nM=count[2], bad_leaves=bad, stats=st, cN=cN, centre=centre, pick=pick, leaves=leaves, fixed=fixed)

if __name__ == "__main__":
    delta = float(sys.argv[1]); JC = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    mode = sys.argv[3] if len(sys.argv) > 3 else "ZM"
    corner = len(sys.argv) > 4 and sys.argv[4] == "corner"
    cN = round(358287 * (1 - delta))
    r = run(cN, JC=JC, mode=mode, corner=corner)
    if r:
        import collections
        ws = collections.Counter()
        for b, kind in r["leaves"]:
            if kind == 2: ws[min(b[q][1] - b[q][0] for q in range(Q)).bit_length()] += 1
        print("  M-leaf min-width bit lengths:", sorted(ws.items()))
