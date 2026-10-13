#!/usr/bin/env python3
"""Assemble Solution<NAME>.lean for a mean-value certificate, with the verified SolutionSixW25P.lean as template.
Usage: assemble_mvt.py NAME  (needs head_/checker_/data_<NAME>.lean, <NAME>_params.txt, kappa_<NAME>.txt in the
workspace root).  The base (imports and the bridge port) and the submission layer are copied verbatim apart from the
certificate name; the tail is tail_SixW25P.lean with the name, cN, m and the exact constant substituted."""
import sys, os
ROOT = os.path.expanduser("~/work/riemann-submission")
NAME = sys.argv[1]; T = "SixW25P"
rd = lambda f: open(os.path.join(ROOT, f), encoding="utf-8").read()
s = rd(f"Solution{T}.lean")
old = {k: rd(f"{k}_{T}.lean") for k in ["checker", "data", "tail"]}
new = {k: rd(f"{k}_{NAME}.lean") for k in ["checker", "data", "head"]}
IMP = "import ChallengeDeps.CandidateSpec\n"
i_imp = s.index(IMP); ic = s.index(old["checker"]); idd = s.index(old["data"]); it = s.index(old["tail"])
assert ic + len(old["checker"]) == idd and s[it + len(old["tail"]):] == ""
base = s[i_imp:ic]; mid = s[idd + len(old["data"]):it]
assert T not in mid
print("name occurrences in base:", base.count(T))
base = base.replace(T, NAME)
Q, SA, aN, bN, cN, _ = open(os.path.join(ROOT, f"{NAME}_params.txt")).read().split()[:6]
cN = int(cN); SA = int(SA); m = 5 + SA // cN
_, _, P, R, D = rd(f"kappa_{NAME}.txt").split()
cN0 = 349330; m0 = 5 + SA // cN0; P0, R0, D0 = "14550000000", "25739571", "14500045810"
t = old["tail"]
subs = [(T, NAME), (f"({cN0} : ℝ)", f"({cN} : ℝ)"), (f"c {m0} B", f"c {m} B"), (f") {m0} (", f") {m} ("), (f") {m0} WW", f") {m} WW"),
        (P0, P), (R0, R), (D0, D)]
for a, b in subs:
    k = t.count(a); assert k > 0, a; t = t.replace(a, b); print(f"tail: {a!r} -> {b!r} x{k}")
assert str(cN0) not in t and P0 not in t
head = new["head"][:new["head"].index(IMP)]
out = head + base + new["checker"] + new["data"] + mid + t
open(os.path.join(ROOT, f"Solution{NAME}.lean"), "w", encoding="utf-8").write(out)
print(f"wrote Solution{NAME}.lean: {len(out.encode())} bytes")
