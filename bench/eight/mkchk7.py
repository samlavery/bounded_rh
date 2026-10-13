#!/usr/bin/env python3
"""Write checker_<NAME>.lean for the eight-point certificate: cells + pyramid of the accepted certificate, the
mean-value core, the slope core, the convex-basin core, and the instance (gen7n).  Usage: mkchk7.py NAME"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
from gen7n import checker
NAME = sys.argv[1]
Qs, SA, aN, bN, cN = open(os.path.join(ROOT, f"{NAME}_params.txt")).read().split()[:5]
SA = int(SA); aN = [int(x) for x in aN.split(",")]; bN = [int(x) for x in bN.split(",")]; cN = int(cN)
ORDER = [int(x) for x in open(os.path.join(ROOT, f"{NAME}_order.txt")).read().strip().split(",")]
c25 = open(os.path.join(ROOT, "checker_SixW25P.lean"), encoding="utf-8").read()
pre = c25[:c25.index("/-! ###### the 6-point weighted certificate `SixW25P`")].replace("SixW25P", NAME)
def part(path, a, b, drop=()):
    t = open(path, encoding="utf-8").read(); t = t[t.index(a):t.index(b)].replace(a + "\n", "")
    for x in drop: t = t.replace(x + "\n", "")
    return t
defs = part(os.path.join(HERE, "..", "mvt", "MvtDefs.lean"), "-- MVTDEFS-BEGIN", "-- MVTDEFS-END")
core = part(os.path.join(HERE, "..", "mvt", "MvtCore.lean"), "-- MVTPROOFS-BEGIN", "-- MVTPROOFS-END")
sl = part(os.path.join(HERE, "SlopeCore.lean"), "-- SLOPE-BEGIN", "-- SLOPE-END", ("-- SLOPEDEFS-END",))
cv = part(os.path.join(HERE, "ConvCore.lean"), "-- CONV-BEGIN", "-- CONV-END", ("-- CONVDEFS-END",))
inst = (f"\n/-! ###### the 8-point weighted certificate `{NAME}`: zero-order and slope leaf tests, convex basins, walk, cover ###### -/\n"
        + checker(NAME, SA, aN, bN, cN, ORDER, 8))
chk = pre + defs + core + sl + cv + inst
open(os.path.join(ROOT, f"checker_{NAME}.lean"), "w", encoding="utf-8").write(chk)
print(f"wrote checker_{NAME}.lean: {len(chk.encode())} bytes")
