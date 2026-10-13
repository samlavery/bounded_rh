import sys, time, collections
from functools import lru_cache
exec(open("sim_tight.py").read().split("leaves = [b for b")[0])
leaves = [b for b in d["leaves"] if not b[Q - 1][1] < b[0][0]]
def tz(x): return (x & -x).bit_length() - 1 if x else 64
@lru_cache(maxsize=None)
def exact_lb(lo, hi):
    k = min(tz(lo), tz(hi))
    return min(E(kk, ii) for kk, ii in dcov(k, lo >> k, (hi >> k) - 1, 64))
def stats(name, cover):
    qs = set()
    for b in leaves:
        for t in terms(b): qs.add(t)
    R = collections.Counter(); cells = set(); minlev = collections.Counter()
    for (lo, hi) in qs:
        cv = cover(lo, hi); R[len(cv)] += 1; cells.update(cv)
    tot = sum(k * v for k, v in R.items())
    print(f"{name:18s} distinct queries {len(qs)}  reads/query {tot/len(qs):.2f}  max {max(R)}  distinct cells read {len(cells)}  hist {sorted(R.items())[:12]}")
    return cells
def cov_pyr(e, maxblk=4):
    def f(lo, hi):
        k = max(0, (hi - lo).bit_length() - e)
        return dcov(k, lo >> k, (hi - 1) >> k, maxblk)
    return f
def cov_exact(lo, hi):
    k = min(tz(lo), tz(hi))
    return dcov(k, lo >> k, (hi >> k) - 1, 64)
for e in (4, 5):
    stats(f"pyr e={e}", cov_pyr(e))
stats("pyr e=5 blk8", cov_pyr(5, 3))
stats("exact", cov_exact)
fail = sum(1 for b in leaves if check(b, exact_lb) < 0)
print("exact decomposition: fail", fail)
