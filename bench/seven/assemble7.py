#!/usr/bin/env python3
"""Assemble Solution<NAME>.lean for the seven-point certificate, with the verified SolutionSixW25P.lean as template:
its base (imports and the bridge port) and the constant-independent submission layer copied verbatim apart from the
certificate name; the checker and data from make7.py, the header from gen_head7.py, the tail from gen_tail7.py.
Usage: assemble7.py NAME"""
import sys, os
ROOT = os.path.expanduser("~/work/riemann-submission")
NAME = sys.argv[1]; T = "SixW25P"
rd = lambda f: open(os.path.join(ROOT, f), encoding="utf-8").read()
s = rd(f"Solution{T}.lean")
old = {k: rd(f"{k}_{T}.lean") for k in ["checker", "data", "tail"]}
new = {k: rd(f"{k}_{NAME}.lean") for k in ["checker", "data", "head", "tail"]}
IMP = "import ChallengeDeps.CandidateSpec\n"
i_imp = s.index(IMP); ic = s.index(old["checker"]); idd = s.index(old["data"]); it = s.index(old["tail"])
assert ic + len(old["checker"]) == idd and s[it + len(old["tail"]):] == ""
base = s[i_imp:ic]; mid = s[idd + len(old["data"]):it]
assert T not in mid
print("name occurrences in base:", base.count(T))
base = base.replace(T, NAME)
head = new["head"][:new["head"].index(IMP)]
out = head + base + new["checker"] + new["data"] + mid + new["tail"]
assert T not in out
open(os.path.join(ROOT, f"Solution{NAME}.lean"), "w", encoding="utf-8").write(out)
print(f"wrote Solution{NAME}.lean: {len(out.encode())} bytes")
