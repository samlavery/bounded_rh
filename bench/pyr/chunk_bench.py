"""Core-only kernel benchmark of real walk chunks: the final checker's computational code (Pyr.lb + instance walk,
from checker_<NAME>.lean) and the table constants of data_<NAME>.lean; each selected chunk as
`walk TOP BK bits fuel 1 coords = e := by decide +kernel` with the profiler on.
Usage: chunk_bench.py NAME TAG first_leaf_chunk_names...   (writes bench/BenchK{TAG}Defs.lean and bench/BenchK{TAG}.lean)"""
import re, sys, os
sys.set_int_max_str_digits(0)
os.chdir(os.path.expanduser("~/work/riemann-submission"))
NAME, TAG = sys.argv[1], sys.argv[2]; sel = sys.argv[3:]
chk = open(f"checker_{NAME}.lean", encoding="utf-8").read()
gen = chk[chk.index("/-- evaluate a natural number to a numeral"):chk.index("/-! ### verification of a table -/")]
inst = chk[chk.index("def SA : ℕ"):chk.index("/-- the box `[l_r, u_r] / SC` satisfies")]
inst = re.sub(r"/-- the weighted functional on the gaps, in real form -/\ndef G \(.*?\n\n", "", inst, flags=re.S)
data = open(f"data_{NAME}.lean", encoding="utf-8").read()
consts = data[data.index("def TOP : ℕ"):data.index("theorem top_ok")]
defs = ("-- chunk benchmark: final kernel code of " + NAME + "\nimport BenchCore\n\nnoncomputable section\n\nnamespace Zeta23Ext.Bridge.ThreePoint.PyrK\n\n"
        + consts + "\n" + gen + "\n" + inst + "\nend Zeta23Ext.Bridge.ThreePoint.PyrK\n\nend\n")
open(f"bench/BenchK{TAG}Defs.lean", "w", encoding="utf-8").write(defs)
thms = []
for nm in sel:
    m = re.search(rf"theorem {nm} : {NAME}\.Covered ([\d ]+) :=\n  {NAME}\.covered_of_walk lbS (\d+) (\d+) ([\d ]+) (\d+) \(by decide \+kernel\)", data)
    coords, bits, fuel, coords2, e = m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)
    thms.append(f"theorem {nm} : walk TOP BK {bits} {fuel} 1 {coords} = {e} := by decide +kernel")

open(f"bench/BenchK{TAG}.lean", "w", encoding="utf-8").write(
    f"import BenchCore\nimport BenchK{TAG}Defs\n\nset_option Elab.async false\nset_option profiler true\nset_option profiler.threshold 1\n\n"
    "namespace Zeta23Ext.Bridge.ThreePoint.PyrK\n\nset_option maxRecDepth 100000\n\n" + "\n\n".join(thms) + "\n\nend Zeta23Ext.Bridge.ThreePoint.PyrK\n")
print("ok", len(thms))
