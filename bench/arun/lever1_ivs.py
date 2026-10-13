#!/usr/bin/env python3
"""lever1_ivs.py DATA.json OUT.json [VERIFIER]: the precertified tangent intervals of lever 1 (am-cert, 2026-10-10).

lever1_check.py's merge, written out: the independent replay `verify8pz.py` (or `verify9pz.py`) runs with a recorder on
`tcheck`; per point, the hull of every range on which a minorant leaf evaluates the point's tangent side condition is
checked once by `tcheck`.  One interval per point is required (the point word has one interval field); the script stops
otherwise.  OUT.json: {"ivs": {p: [a, b]}, "points": n, "with_iv": m}."""
import sys, os, json, collections
DATA, OUT = sys.argv[1], sys.argv[2]
VER = sys.argv[3] if len(sys.argv) > 3 else os.path.expanduser("~/work/riemann-submission/bench/eight/am8/verify8pz.py")
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
if src.count("ax = get(5)") == 1:
    src = src.replace("ax = get(5)", "ax = get((Q + len(NADJ) - 1).bit_length())")
sys.argv = [VER, DATA]
g = {"__name__": "__main__", "__file__": VER}
sys.path.insert(0, os.path.dirname(VER))
exec(compile(src, VER, "exec"), g)
REC, tcheck = g["_REC"], g["_tcheck0"]
assert all(r for (_, _, _, r) in REC), "a recorded tangent check failed"
by = collections.defaultdict(set)
for p, L, U, r in REC: by[p].add((L, U))
ivs = {}
for p, rs in by.items():
    a = min(L for L, _ in rs); b = max(U for _, U in rs)
    assert tcheck(a, b, p), f"point {p}: the hull [{a}, {b}] fails"
    assert a <= p <= b and 0 < b and a < (1 << 24)
    ivs[p] = [a, b]
json.dump({"data": os.path.abspath(DATA), "verifier": VER, "points": len(g["PT"]), "with_iv": len(ivs),
           "ivs": {str(p): v for p, v in sorted(ivs.items())}}, open(OUT, "w"))
print(f"{len(ivs)} points with an interval (point table {len(g['PT'])}); {len(REC)} recorded checks; -> {OUT}")
