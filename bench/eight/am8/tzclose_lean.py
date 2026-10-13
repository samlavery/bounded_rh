#!/usr/bin/env python3
"""Lean golden tests of the closure split (TZ.md §5) against a genpcellC CLOSE instance: each split of tz_golden_close.json,
run through the kernel's split function from the parent's closed state with a packing walk (`FPk pos` packs the child's
state, 24 bits a field, above `pos`), must give child A then child B as logged:
`U (split FPk 1) parent = ((2^NB + pack A) << NB) + pack B`, NB = 56 · 24.  Writes ROOT/AMW/PCellCloseG.lean.
Usage: tzclose_lean.py ROOT MOD GOLDEN.json"""
import sys, os, json
ROOT, MOD, GJ = sys.argv[1:4]
NS = MOD[:-4] if MOD.endswith("Inst") else MOD   # the instance namespace AMW.Cert.NS
G = json.load(open(GJ)); Q = 7
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]
NF = 2 * Q + 2 * len(SUMS); NB = 24 * NF
def fields(I): return [x for r in range(Q) for x in I[f"{r},{r + 1}"]] + [x for (i, j) in SUMS for x in I[f"{i},{j}"]]
def pack(fs): return sum(x << (24 * i) for i, x in enumerate(fs))
names = [f"x{i}" for i in range(NF)]
out = [f"""import AMW.{MOD}

/-! ###### golden tests of the closure split (mvt-engine; tz_golden_close.json, TZ.md §5)

Each logged split, from the parent's closed state, through the kernel's split function with the packing walk `FPk`:
child A's state is packed above the start position, then child B's above that. The expected numbers are the
sizer's `tz.close_split` children (each equal to `tz.close` of the child). ###### -/

set_option maxRecDepth 100000

namespace AMW.Cert.PCellCloseG

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.{NS}

/-- the packing walk: the state's 56 fields, 24 bits each, above `pos` -/
def FPk : WF := fun pos {" ".join(names)} _ => Nat.add (Nat.shiftLeft pos {NB}) ({" + ".join(f"Nat.shiftLeft {n} {24 * i}" for i, n in enumerate(names))})
"""]
for i, sp in enumerate(G['splits']):
    ax = sp['axis']; nm_ = f"gsplit{ax}" if ax < Q else f"ssplit{SUMS[ax - Q][0]}{SUMS[ax - Q][1]}"
    par = fields(sp['parent']); A = fields(sp['childA_hi_eq_m']); B = fields(sp['childB_lo_eq_m'])
    assert all(0 <= x < 1 << 24 for x in par + A + B)
    exp = (((1 << NB) + pack(A)) << NB) + pack(B)
    out.append(f"""/-- split {i}: axis {ax} (pair {sp['pair'][0]},{sp['pair'][1]}) at {sp['m']}; child A changes {len(sp['changedA'])} bounds, child B {len(sp['changedB'])} -/
theorem cs_{i} : U ({nm_} FPk 1) ⟨{", ".join(map(str, par + [0]))}⟩ = {exp} := by decide +kernel""")
out.append("end AMW.Cert.PCellCloseG\n")
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "window", ROOT, "AMW", "PCellCloseG.lean")
open(P, "w").write("\n\n".join(out))
print(P, len(G['splits']), "splits")
