"""Lean text for the tables of a mean-value certificate: the w pyramid (`TOP`/`BK`), the derivative pyramids
(`TOPP`/`BKP` for w' + 2, `TOPM`/`BKM` for 2 - w'), the point table `PTB` (block j: r + 16 * fields, the points
j 2^10 + t 2^r), each with a binary block dispatch (0 outside the stored blocks)."""

def dispatch(name, consts):
    """`def name (j : ℕ) : ℕ` returning consts[j] (a dict j -> constant name), 0 elsewhere"""
    L = []
    js = sorted(consts)
    if not js:
        L.append(f"def {name} (j : ℕ) : ℕ := 0")
        return L
    def sub(a, b):
        if b - a == 1:
            j = js[a]; return f"(Bool.rec (motive := fun _ => ℕ) 0 {consts[j]} (Nat.beq j {j}))"
        return f"({name}s{a}_{b} j)"
    def mk(a, b):
        if b - a == 1: return
        m = (a + b) // 2
        mk(a, m); mk(m, b)
        L.append(f"def {name}s{a}_{b} (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) {sub(a, m)} {sub(m, b)} (Nat.ble {js[m]} j)")
    mk(0, len(js))
    L.append(f"def {name} (j : ℕ) : ℕ := {sub(0, len(js))}")
    return L

def pyr_consts(P, top, bk):
    L = [f"def {top} : ℕ := {P.TOPN}"]
    for j in sorted(P.BKN): L.append(f"def {bk}_{j} : ℕ := {P.BKN[j]}")
    L += dispatch(bk, {j: f"{bk}_{j}" for j in P.BKN})
    return "\n".join(L) + "\n"

def pt_blocks(PT, EB=32):
    """PT: dict x -> value. Returns dict j -> packed constant (r + 16 * fields)."""
    from collections import defaultdict
    blocks = defaultdict(dict)
    for x, v in PT.items(): blocks[x >> 10][x & 1023] = v
    out = {}
    for j, d in blocks.items():
        if all(v == 0 for v in d.values()): continue
        tz = min(min(10, (o & -o).bit_length() - 1) if o else 10 for o in d)
        X = 0
        for o, v in d.items():
            assert o % (1 << tz) == 0
            X |= v << (EB * (o >> tz))
        out[j] = tz | (X << 4)
    return out

def pt_lookup(PB, x, EB=32):
    """exact replica of `PyrD.ptv`"""
    if x >= 524288: return 0
    X = PB.get(x >> 10, 0); r = X & 15
    if x & ((1 << r) - 1): return 0
    return ((X >> 4) >> (EB * ((x & 1023) >> r))) & ((1 << EB) - 1)

def pt_consts(PB, name="PTB"):
    L = []
    for j in sorted(PB): L.append(f"def {name}_{j} : ℕ := {PB[j]}")
    L += dispatch(name, {j: f"{name}_{j}" for j in PB})
    return "\n".join(L) + "\n"

class PairTable:
    """the two derivative pyramids packed as one pyramid of 64-bit pairs (low: PP, high: PM), with an exact
    replica of the Lean reads `PyrD.entry2` / `PyrD.lb2`"""
    M32 = (1 << 32) - 1
    def __init__(self, PP, PM):
        assert sorted(PP.res.items()) == sorted(PM.res.items())
        self.PP, self.PM = PP, PM
        self.PB, self.KT = PP.PB, PP.KT
        T = 0
        for (l, i), v in PP.top.items():
            w = PM.top[(l, i)]
            T |= (v | (w << 32)) << (64 * ((1 << (self.KT - l)) + i))
        self.TOPN = T
        self.BKN = {}
        for j, levels in PP.blk.items():
            lm = PM.blk[j]; X = 0
            for d, row in enumerate(levels):
                for t, v in enumerate(row): X |= (v | (lm[d][t] << 32)) << (64 * ((1 << d) - 1 + t))
            self.BKN[j] = PP.res[j] | (X << 5)
        self.cache = {}
    def fld2(self, X, i): return (X >> (64 * i)) & ((1 << 64) - 1)
    def entry2(self, l, i):
        PB = self.PB
        if l > self.KT: return 0
        if PB < l: return self.fld2(self.TOPN, (1 << (self.KT - l)) + i)
        j = i >> (PB - l)
        X = self.BKN.get(j, 0)
        r = X & 31
        kk = r if l <= r else l
        d = max(0, PB - kk)
        idx = ((1 << d) - 1) + max(0, (i >> (kk - l)) - (j << d))
        return self.fld2(X >> 5, idx)
    def lb2(self, lo, hi):
        key = (lo, hi)
        v = self.cache.get(key)
        if v is not None: return v
        cv = self.PP.cover(lo, hi)
        if not cv or cv[-1] is None: v = 0
        else:
            a = b = None
            for (l, i) in cv:
                e = self.entry2(l, i); x, y = e & self.M32, e >> 32
                a = x if a is None else min(a, x); b = y if b is None else min(b, y)
            v = a | (b << 32)
        self.cache[key] = v
        return v

def pair_consts(T, top, bk):
    L = [f"def {top} : ℕ := {T.TOPN}"]
    for j in sorted(T.BKN): L.append(f"def {bk}_{j} : ℕ := {T.BKN[j]}")
    L += dispatch(bk, {j: f"{bk}_{j}" for j in T.BKN})
    return "\n".join(L) + "\n"
