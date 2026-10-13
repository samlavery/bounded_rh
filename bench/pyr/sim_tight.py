"""Tightness of candidate lower-bound oracles on the RKF leaves: fraction of leaves whose check still passes."""
import sys, time
from functools import lru_cache
from tree import load, terms
from wz import WZ, SW
d = load("SixW35RKF"); Q = d["Q"]; aN = d["aN"]; bN = d["bN"]; cN = d["cN"]; SC = 2**15
XFARN = 3 * SC; FSH = 7
def roundFar(a, b): return ((a >> FSH) << FSH, ((b + 127) >> FSH) << FSH) if a >= XFARN else (a, b)
@lru_cache(maxsize=None)
def pieces_oracle(lo, hi):
    out = []; a = lo
    while True:
        q = ((a >> 13) + 1) << 13
        if q < hi: out.append(roundFar(a, q)); a = q
        else: out.append(roundFar(a, hi)); break
    return min(WZ(*p) for p in out)
@lru_cache(maxsize=None)
def E(k, i):
    """entry of the aligned cell [i 2^k, (i+1) 2^k]: its own cell test up to a quarter, min of children above"""
    if k <= 13: return WZ(i << k, (i + 1) << k)
    return min(E(k - 1, 2 * i), E(k - 1, 2 * i + 1))
def bitlen(w): return w.bit_length()
def dcov(k, ia, ib, maxblk=4):
    """greedy aligned decomposition of cells ia..ib at level k: list of (level, index)"""
    out = []; g = ia
    while g <= ib:
        t = 0
        while t < maxblk and g % (1 << (t + 1)) == 0 and g + (1 << (t + 1)) - 1 <= ib: t += 1
        out.append((k + t, g >> t)); g += 1 << t
    return out
def make_pyr(e, kmin=0, endx=True, maxblk=4):
    @lru_cache(maxsize=None)
    def lb(lo, hi):
        w = hi - lo
        k = max(kmin, bitlen(w) - e)
        ia = lo >> k; ib = ((hi - 1) >> k) if endx else (hi >> k)
        return min(E(kk, ii) for kk, ii in dcov(k, ia, ib, maxblk))
    return lb
def check(box, lb):
    l = [b[0] for b in box]
    lin = sum(bN[r] * l[r] for r in range(Q))
    ws = sum(a * lb(lo, hi) for a, (lo, hi) in zip(aN, terms(box)))
    return lin * SW + ws * SC - cN * SC * SW
leaves = [b for b in d["leaves"] if not b[Q - 1][1] < b[0][0]]
print(len(leaves), "leaves checked (half-space skips removed)")
oracles = [("pieces", pieces_oracle)] + [(f"pyr e={e} kmin={km}", make_pyr(e, km)) for e in (2, 3, 4) for km in (0, 3)] + [("pyr e=3 b-incl", make_pyr(3, 0, False)), ("pyr e=5", make_pyr(5, 0))]
for name, lb in oracles:
    t = time.time(); fail = 0; reads = 0
    for b in leaves:
        if check(b, lb) < 0: fail += 1
    print(f"{name:22s} fail {fail:6d} ({100*fail/len(leaves):.2f}%)  {time.time()-t:.0f}s", flush=True)
