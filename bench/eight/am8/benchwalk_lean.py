#!/usr/bin/env python3
"""Per-node kernel cost of a pair-cell walk (T1 or closure): the DATA json's 32 walks through a --decode instance MOD
(genpcellC.py, every minorant check replaced by `true`, so a node costs its decode plus its tightening/split), one
`decide +kernel` theorem per walk under `set_option profiler true`.  Writes ROOT/AMW/{OUT}.lean.
Usage: benchwalk_lean.py ROOT MOD DATA.json OUT [ROOTS]   (ROOTS: comma list of walk indices, default all)"""
import sys, os, json
ROOT, MOD, DJ, OUT = sys.argv[1:5]
NS = MOD[:-4] if MOD.endswith("Inst") else MOD
D = json.load(open(DJ)); Q = 7; NC = 21; WW = 1 << 40
SEL = [int(x) for x in sys.argv[5].split(",")] if len(sys.argv) > 5 else list(range(len(D['walks'])))
out = [f"""import AMW.{MOD}

/-! ###### walk cost bench (mvt-engine): {os.path.basename(DJ)}'s walks through the decode-only instance `{MOD}` ###### -/

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1

namespace AMW.Cert.{OUT}

open AMW.Cert AMW.Cert.PCell AMW.Cert.{NS}
"""]
for n in SEL:
    wk = D['walks'][n]; bits = int(wk['hex'], 16) << 1
    st = [x for c in wk['cell'] for x in c] + [0, WW] * NC + [0]
    out.append(f"def WB{n} : ℕ := {hex(bits)}")
    out.append(f"theorem w{n} : U (walk 0 (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) (0, 0, []) WB{n} 128 1) ⟨{', '.join(map(str, st))}⟩ = {wk['nbits'] + 1} := by decide +kernel")
out.append(f"end AMW.Cert.{OUT}\n")
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "window", ROOT, "AMW", f"{OUT}.lean")
if os.path.exists(P): raise SystemExit(f"{P} exists")
open(P, "w").write("\n\n".join(out))
print(P, len(SEL), "walks")
