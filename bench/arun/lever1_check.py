#!/usr/bin/env python3
"""lever1_check.py DATA.json [VERIFIER]: offline check of lever 1 (precertified point validity intervals), am-cert 2026-10-10.

Runs the independent replay `verify8pz.py` (unmodified; its source is exec'd with a recorder wrapped around `tcheck`) and
collects every (point p, range [L, U]) on which a minorant leaf's tangent side condition is evaluated.  Per point, the
ranges are sorted and merged greedily: the current interval is extended by the next range when `tcheck` accepts the hull
(the exact integer replica of the kernel's side condition); otherwise a new interval starts.  Every interval is checked
by `tcheck` and covers its ranges, so a leaf's condition reduces to `a ≤ L ∧ U ≤ b` for one of its point's intervals
(tangent validity is pointwise in s, hence monotone under shrinking the range).
Prints the intervals-per-point distribution, the worst points, and the table bytes."""
import sys, os, json, collections
DATA = sys.argv[1]
VER = sys.argv[2] if len(sys.argv) > 2 else os.path.expanduser("~/work/riemann-submission/bench/eight/am8/verify8pz.py")
src = open(VER, encoding="utf-8").read()
hook = "def weights(k, m):"
assert src.count(hook) == 1
rec = '''_REC = []
_tcheck0 = tcheck
def tcheck(L, Uu, p):
    r = _tcheck0(L, Uu, p)
    _REC.append((p, L, Uu, r))
    return r
'''
src = src.replace(hook, rec + hook)
# the split-axis field is AXB = bit_length(Q + NC - 1) bits (5 at Q = 7, 6 at Q = 8; emit9pz.py)
assert src.count("ax = get(5)") == 1
src = src.replace("ax = get(5)", "ax = get((Q + len(NADJ) - 1).bit_length())")
sys.argv = [VER, DATA]
g = {"__name__": "__main__", "__file__": VER}
sys.path.insert(0, os.path.dirname(VER))
exec(compile(src, VER, "exec"), g)
REC, tcheck = g["_REC"], g["_tcheck0"]
M = g["stats"]["M"]
print(f"tangent side conditions evaluated: {len(REC)} on {M} minorant leaves ({len(REC) / M:.1f} per leaf); "
      f"failed: {sum(1 for r in REC if not r[3])}")
by = collections.defaultdict(set)
for p, L, U, r in REC:
    if r: by[p].add((L, U))
cnt = {}; worst = []; spans = []
for p, rs in by.items():
    rs = sorted(rs); ivs = []
    a, b = rs[0]
    for (L, U) in rs[1:]:
        na, nb = min(a, L), max(b, U)
        if tcheck(na, nb, p): a, b = na, nb
        else: ivs.append((a, b)); a, b = L, U
    ivs.append((a, b))
    for (x, y) in ivs: assert tcheck(x, y, p)
    cnt[p] = len(ivs); spans.append((len(rs), len(ivs)))
    worst.append((len(ivs), len(rs), p))
n = len(cnt); dist = collections.Counter(cnt.values())
le2 = sum(v for k, v in dist.items() if k <= 2)
tot = sum(cnt.values())
print(f"points with tangent checks: {n} (point table {len(g['PT'])}); intervals {tot} ({tot / n:.2f} per point)")
print("intervals per point:", dict(sorted(dist.items())))
print(f"≤ 2 intervals: {le2}/{n} = {100 * le2 / n:.1f} %  -> {'CLEAN' if le2 >= 0.95 * n else 'NOT clean'} (rule: ≥ 95 %)")
worst.sort(reverse=True)
print("worst points (intervals, distinct ranges, p):", worst[:10])
print(f"distinct (p, range) pairs: {sum(len(v) for v in by.values())}; leaf checks saved per leaf: {len(REC) / M:.1f}")
# bytes: two 20-bit endpoints per interval, packed in hex (10 hex chars), plus an interval count per point
print(f"table bytes (packed hex, 40 bits per interval + 4 bits count per point): "
      f"{(40 * tot + 4 * n) / 4:.0f} B ≈ {(40 * tot + 4 * n) / 4 / 1024:.1f} KB")
