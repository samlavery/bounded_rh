#!/usr/bin/env python3
"""dprune.py DATA.json IV.json OUT.json [VERIFIER]: bytes lever L5 (am-cert, 2026-10-11) — prune the derivative pair
table to the blocks the precertified tangent intervals need.

With lever 1 the derivative table (TOPD/BKD) is read only by the once-per-point interval check (`ivOk` → `tcheckPZC`); the
leaves never read it.  A missing block is the zero block, which `blockOk2` accepts as is (`Nat.beq X 0`), and a zero read
makes the check fall back to the zero-order extension.  This script
  1. finds the hulls that fail with every derivative read zeroed;
  2. records the BKD blocks and TOPD cells those hulls read when the table is present;
  3. keeps exactly those blocks, and zeroes every TOPD cell above a dropped block (so `topOk2` still holds: a parent pair
     is ≤ the pairwise minimum of its children, and 0 is ≤ everything);
  4. re-checks EVERY hull against the pruned table with the replay's own `tcheck`, and re-runs the full replay;
  5. writes OUT.json = DATA.json with the pruned BKD and TOPD (every other field unchanged).
Stops if any hull fails."""
import sys, os, json
DATA, IVP, OUT = sys.argv[1:4]
VER = sys.argv[4] if len(sys.argv) > 4 else os.path.expanduser("~/work/riemann-submission/bench/eight/am8/verify8pz.py")
src = open(VER, encoding="utf-8").read()
if src.count("ax = get(5)") == 1: src = src.replace("ax = get(5)", "ax = get((Q + len(NADJ) - 1).bit_length())")
sys.argv = [VER, DATA]
g = {"__name__": "__main__", "__file__": VER}
sys.path.insert(0, os.path.dirname(VER))
exec(compile(src, VER, "exec"), g)
IV = {int(p): v for p, v in json.load(open(IVP))["ivs"].items()}
tc = g["tcheck"]; DPc = g["DPc"]; BKD0 = dict(g["BKD"]); TOPD0 = g["TOPD"]; lb2_0 = g["lb2"]; e2_0 = g["entry2"]
g["lb2"] = lambda a, b: (0, 0)
fail = [p for p, (a, b) in IV.items() if not tc(a, b, p)]
reads = set()
def e2rec(l, i):
    if DPc.PB >= l: reads.add(i >> (DPc.PB - l))
    return e2_0(l, i)
g["entry2"] = e2rec; g["_c2"].clear(); g["lb2"] = lb2_0
assert all(tc(*IV[p], p) for p in fail), "a hull fails even with the full table"
keep = {j for j in reads if j in BKD0}
PB, KT = DPc.PB, DPc.KT
T = TOPD0
for l in range(PB + 1, KT + 1):
    for i in range(1 << (KT - l)):
        if any(j in BKD0 and j not in keep for j in range(i << (l - PB), (i + 1) << (l - PB))):
            T &= ~(((1 << 64) - 1) << (64 * ((1 << (KT - l)) + i)))
g["BKD"].clear(); g["BKD"].update({j: v for j, v in BKD0.items() if j in keep}); g["TOPD"] = T
g["entry2"] = e2_0; g["_c2"].clear()
bad = [p for p, (a, b) in IV.items() if not tc(a, b, p)]
assert not bad, f"{len(bad)} hulls fail on the pruned table"
D = json.load(open(DATA))
D["tables"]["BKD"] = {str(j): hex(v)[2:] if not D["tables"]["BKD"][str(j)].startswith("0x") else hex(v)
                      for j, v in BKD0.items() if j in keep}
TD = D["tables"]["TOPD"]
D["tables"]["TOPD"] = (hex(T) if TD.startswith("0x") else hex(T)[2:])
D.setdefault("settings", {})["DPRUNE"] = f"{len(keep)}/{len(BKD0)} derivative blocks (am-cert dprune.py)"
json.dump(D, open(OUT, "w"))
print(f"hulls failing without the derivative table: {len(fail)}; blocks kept {len(keep)} of {len(BKD0)}; "
      f"all {len(IV)} hulls pass on the pruned table -> {OUT}")
