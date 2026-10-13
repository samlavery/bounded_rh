"""Apply typh's engine speed-ups (riemannzeta-fun dc788ef, submissions/seven-point-optimised-window, Apache-2.0) to an AM
root in place: CEngine, GBase, GFar from typh's file (same statements; Bool.rec `&&ₖ`/`||ₖ`, Nat.sub min, unrolled
pyramid cover with packed reads, unforced point reads, proof-order tweaks), and GCell with the far sum unrolled into
literal `farJ` steps for THE ROOT'S OWN coefficients (read from its current GCell `CE`, so re-key GCell first).
Keeps each file's own `import` lines.  Usage: port_typh.py ROOTDIR   (e.g. ../rootTW)
Measured on AMR7 (R7, n=7): per-chunk kernel time 0.92× (Z 1.74 vs 1.86 ms, S 6.38 vs 6.98, M 7.27 vs 8.34)."""
import os, re, sys, subprocess
R = os.path.join(os.path.abspath(sys.argv[1]), "AMW")
src = subprocess.run(["git", "-C", os.path.expanduser("~/work/riemannzeta-fun"), "show",
                      "dc788ef:submissions/seven-point-optimised-window/proof/Solution.lean"], capture_output=True, text=True, check=True).stdout
parts = re.split(r'/-! ###### AMW module: (\w+) ###### -/\n', src); T = dict(zip(parts[1::2], parts[2::2]))
def imports(s): return "".join(l + "\n" for l in s.splitlines() if l.startswith("import "))
CREDIT = "-- engine speed-ups by typh (riemannzeta-fun dc788ef, seven-point-optimised-window, Apache-2.0)\n"
ours = {m: open(f"{R}/{m}.lean").read() for m in ["GCell", "GBase", "GFar", "CEngine"]}
for m in ["CEngine", "GBase", "GFar"]:
    open(f"{R}/{m}.lean", "w").write(imports(ours[m]) + CREDIT + "\n" + T[m])
g = T["GCell"]; oc = ours["GCell"]
pat_ce = r"def CE : List \(ℕ × ℕ × Bool\) :=\n(.*?)\n/--"; pat_cj = r"def CJ \(j : ℕ\) : ℕ × Bool :=\n(.*?)\n\n"
ce_o = re.search(pat_ce, oc, re.S).group(1)
g = g.replace(re.search(pat_ce, g, re.S).group(1), ce_o).replace(re.search(pat_cj, g, re.S).group(1), re.search(pat_cj, oc, re.S).group(1))
chain = "⟨0, 0, 0, 0⟩"
for (j, e, sg) in re.findall(r"\((\d+), (\d+), (true|false)\)", ce_o): chain = f"(farJ n k XL XU XL2 XU2 {chain} {j} {e} {sg})"
g = g.replace(re.search(r"  let a := (\(farJ .*?)\n", g).group(1), chain)
open(f"{R}/GCell.lean", "w").write(imports(oc) + CREDIT + "\n" + g)
print("ported into", R, "; rebuild GCell GBase GConst GFar GNear GAsm1 GAsm2 GCellSound CFacade CEngine CWindow CMin CMLeaf CMinX and dependents")
