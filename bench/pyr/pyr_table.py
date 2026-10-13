"""Dyadic pyramid lower-bound table for `wfun` on the coordinate grid n / 2^15 (our SC), and an exact Python replica
of the Lean oracle `lb` that reads it.

Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0): dyadic cells, dense top levels,
per-block sub-pyramids packed into one natural number each, queries covered by aligned dyadic blocks.

Layout (all cells absolute and aligned: level-l cell i is [i 2^l, (i+1) 2^l] in units of 2^-15):
* `TOP`: levels PB+1 .. KT in heap order, cell (l, i) at field 2^(KT-l) + i (field 1 is the root [0, 2^KT]).
* block j (the level-PB cell j) has the constant `BK j = r + 2^5 * fields`: r = its finest stored level
  (r <= PB), then levels PB, PB-1, .., r of its sub-pyramid: depth d = PB - l, local index t, at field 2^d - 1 + t.
Every field is EB bits; entries are lower bounds in units of 1/U.  Finest cells carry the integer cell bound
(`CellN.WZ` replica, rescaled from SW = 10^13 to U and clamped to EM); every coarser entry is the min of its children.

Query lb(lo, hi) for lo < hi <= 2^KT: level k = bitLen(hi - lo) - PE (truncated at 0); the cells ia = lo >> k ..
ib = (hi - 1) >> k cover [lo, hi]; they are read greedily left to right in aligned groups of 2^t cells (t <= MAXA),
each group through its own entry at level k + t, or through the finest stored ancestor when its block stops coarser.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wz import WZ, SW

class Pyr:
    def __init__(self, PE=5, PB=10, KT=19, MAXA=4, EB=32, U=10**10, FUEL=14, X0=1 << 14):
        self.PE, self.PB, self.KT, self.MAXA, self.EB, self.U, self.FUEL, self.X0 = PE, PB, KT, MAXA, EB, U, FUEL, X0
        self.EM = (1 << EB) - 1
        self.res = {}          # block j -> finest level r_j
        self.cache = {}
        self.xmax = 0          # largest query end seen
    # ---------------- cover (the same arithmetic as the Lean `lb`) ----------------
    @staticmethod
    def bitlen(w): return w.bit_length()
    def alignK(self, g, ib):
        for t in range(self.MAXA, 0, -1):
            if g & ((1 << t) - 1) == 0 and g + (1 << t) <= ib + 1: return t
        return 0
    def cover(self, lo, hi):
        """the (level, index) cells lb reads for [lo, hi], or None when lb returns 0 without reading"""
        if hi <= lo or hi > (1 << self.KT): return None
        k = max(0, self.bitlen(hi - lo) - self.PE)
        ib = (hi - 1) >> k; g = lo >> k; out = []
        for _ in range(self.FUEL):
            t = self.alignK(g, ib)
            out.append((k + t, g >> t)); g2 = g + (1 << t)
            if ib < g2: return out
            g = g2
        return out + [None]     # fuel ran out: lb is 0
    # ---------------- table construction ----------------
    def need(self, queries):
        """record, for every block, the finest level any query reads in it"""
        for (lo, hi) in queries:
            cv = self.cover(lo, hi)
            if not cv: continue
            self.xmax = max(self.xmax, hi)
            for c in cv:
                if c is None: continue
                l, i = c
                if l <= self.PB:
                    j = i >> (self.PB - l)
                    self.res[j] = min(self.res.get(j, self.PB), l)
    def cellval(self, l, i):
        return min(WZ(i << l, (i + 1) << l) * self.U // SW, self.EM)
    def build(self):
        PB = self.PB
        # every block between X0 and the last query end exists (unrefined blocks carry their own cell bound), so
        # that the coarse levels above PB are mins over real bounds rather than over absent (zero) blocks
        for j in range(self.X0 >> PB, ((self.xmax - 1) >> PB) + 1):
            self.res.setdefault(j, PB)
        self.blk = {}          # j -> list of levels: blk[j][d] = list of 2^d entries
        for j, r in sorted(self.res.items()):
            D = PB - r
            levels = [None] * (D + 1)
            levels[D] = [self.cellval(r, (j << D) + t) for t in range(1 << D)]
            for d in range(D - 1, -1, -1):
                ch = levels[d + 1]
                levels[d] = [min(ch[2 * t], ch[2 * t + 1]) for t in range(1 << d)]
            self.blk[j] = levels
        # TOP heap: levels PB+1..KT; level PB values are the blocks' d = 0 entries (0 where no block)
        self.top = {}
        def val(l, i):
            if l == PB: return self.blk[i][0][0] if i in self.blk else 0
            return self.top[(l, i)]
        for l in range(PB + 1, self.KT + 1):
            for i in range(1 << (self.KT - l)):
                self.top[(l, i)] = min(val(l - 1, 2 * i), val(l - 1, 2 * i + 1))
        # packed constants
        EB = self.EB
        T = 0
        for (l, i), v in self.top.items(): T |= v << (EB * ((1 << (self.KT - l)) + i))
        self.TOPN = T
        self.BKN = {}
        for j, levels in self.blk.items():
            X = 0
            for d, row in enumerate(levels):
                for t, v in enumerate(row): X |= v << (EB * ((1 << d) - 1 + t))
            self.BKN[j] = self.res[j] | (X << 5)
        return self
    # ---------------- exact replica of the Lean reads ----------------
    def fld(self, X, i): return (X >> (self.EB * i)) & self.EM
    def entry(self, l, i):
        PB = self.PB
        if l > self.KT: return 0
        if PB < l: return self.fld(self.TOPN, (1 << (self.KT - l)) + i)
        j = i >> (PB - l)
        X = self.BKN.get(j, 0)
        r = X & 31
        kk = r if l <= r else l
        d = max(0, PB - kk)
        idx = ((1 << d) - 1) + max(0, (i >> (kk - l)) - (j << d))
        return self.fld(X >> 5, idx)
    def lb(self, lo, hi):
        key = (lo, hi)
        v = self.cache.get(key)
        if v is not None: return v
        cv = self.cover(lo, hi)
        if not cv or cv[-1] is None: v = 0
        else: v = min(self.entry(l, i) for (l, i) in cv)
        self.cache[key] = v
        return v
    # ---------------- sizes ----------------
    def stats(self):
        nfin = sum(1 << (self.PB - r) for r in self.res.values())
        nent = sum(sum(len(row) for row in lv) for lv in self.blk.values())
        return dict(blocks=len(self.blk), finest=nfin, entries=nent, top=len(self.top),
                    bits=sum(X.bit_length() for X in self.BKN.values()) + self.TOPN.bit_length())

def lean_consts(P, BKname="BK"):
    """Lean text: the packed constants and the binary block dispatch `BK : ℕ → ℕ` (0 outside the stored blocks)"""
    L = [f"def TOP : ℕ := {P.TOPN}"]
    js = sorted(P.BKN)
    for j in js: L.append(f"def {BKname}_{j} : ℕ := {P.BKN[j]}")
    def sub(a, b):
        if b - a == 1:
            j = js[a]; return f"(Bool.rec (motive := fun _ => ℕ) 0 {BKname}_{j} (Nat.beq j {j}))"
        return f"({BKname}s{a}_{b} j)"
    def mk(a, b):
        if b - a == 1: return
        m = (a + b) // 2
        mk(a, m); mk(m, b)
        L.append(f"def {BKname}s{a}_{b} (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) {sub(a, m)} {sub(m, b)} (Nat.ble {js[m]} j)")
    mk(0, len(js))
    L.append(f"def {BKname} (j : ℕ) : ℕ := {sub(0, len(js))}")
    return "\n".join(L) + "\n"
