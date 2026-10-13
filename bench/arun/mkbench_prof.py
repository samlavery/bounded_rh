#!/usr/bin/env python3
"""mkbench_prof.py ROOTS: walk-cost profile benches for PC8C5BF (am-cert, 2026-10-10).

Writes into bench/window/rootR8f/AMW (refuses existing files):
  PFBenchNP.lean  — the 32 (or ROOTS) root walks of PC8C5BFData through PFNPInst (genpcellC --nproof: the real leaf check,
                    definitions only), on PC8C5BFData's tables: the full per-node cost;
  PFBenchDEC.lean — the same walks through PFDECInst (--decode: every minorant check replaced by `true`): navigation plus
                    leaf decode;
  PFBenchSK.lean  — the same walks with the leaf replaced by a length scan (reads only the 2-bit term kinds and the
                    multiplier-list flags to find the leaf's end) on PFDECInst's splits and root closure: navigation only.
Each walk is one `decide +kernel` theorem whose end position is PC8C5BFData's (same walk, same bits); kernel time per
theorem comes from ReplayTimes on the compiled bench."""
import re, sys, os

W = os.path.expanduser("~/work/riemann-submission/bench/window/rootR8f/AMW")
data = open(f"{W}/PC8C5BFData.lean", encoding="utf-8").read().split("\n")
sel = None if len(sys.argv) < 2 else {int(x) for x in sys.argv[1].split(",")}
walks = []
for k, l in enumerate(data):
    m = re.match(r"^theorem wcc(\d+)_(\d+) : U \(walk TOP BK TOPD BKD PT REG WB(\d+) 128 1\) (⟨[^⟩]*⟩) = (\d+) := by(.*)$", l)
    if m and (sel is None or int(m.group(1)) in sel):
        tail = m.group(6).strip() or data[k + 1].strip()
        assert tail == "decide +kernel", tail
        walks.append((m.group(3), m.group(4), m.group(5)))
assert walks, "no walk theorems matched"
D = "AMW.Cert.PC8C5BFData"
HEAD = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
"""

def bench(name, mod, ns, extra=""):
    p = f"{W}/{name}.lean"
    if os.path.exists(p): raise SystemExit(f"{p} exists")
    out = [f"import AMW.PC8C5BFData\nimport AMW.{mod}\n", f"/-! walk-cost bench (am-cert): PC8C5BF's walks through `{mod}` -/\n", HEAD,
           f"namespace AMW.Cert.{name}\n", "open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell\n", extra]
    for (r, st, e) in walks:
        if extra:
            out.append(f"theorem b{r} : AMW.Cert.{ns}.U (walkSkip {D}.WB{r} 128 1) {st} = {e} := by decide +kernel")
        else:
            out.append(f"theorem b{r} : AMW.Cert.{ns}.U (AMW.Cert.{ns}.walk {D}.TOP {D}.BK {D}.TOPD {D}.BKD {D}.PT {D}.REG "
                       f"{D}.WB{r} 128 1) {st} = {e} := by decide +kernel")
    out.append(f"\nend AMW.Cert.{name}\n")
    open(p, "w", encoding="utf-8").write("\n".join(out))
    print(p, len(walks), "walks")

# the length scan: per active term 2 kind bits (+7 for k ≥ 1, +7 for k = 3, +8 for k ≥ 2), then multiplier entries of
# 19 bits while the flag bit is 1, then the closing 0; returns the same offset as mleafP's y.o
NS = "PFDEC"
VARS = "l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A24 B24 A25 B25 A26 B26 A27 B27 A35 B35 A36 B36 A37 B37 A46 B46 A47 B47 A57 B57 M"
SKIP = f"""open AMW.Cert.{NS} in
def tstep (w o : ℕ) : ℕ :=
  forceT (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Nat.add o (Nat.add 2 (Nat.add (Bool.rec (motive := fun _ => ℕ) 7 0 (Nat.beq k 0))
    (Nat.add (Bool.rec (motive := fun _ => ℕ) 0 7 (Nat.beq k 3)) (Bool.rec (motive := fun _ => ℕ) 0 8 (Nat.ble 2 k)))))
def tscan (w : ℕ) (n : ℕ) (o : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun o => o) (fun _ ih o => ih (tstep w o)) n o
def yscan (w : ℕ) (n : ℕ) (o : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun o => o)
    (fun _ ih o => Bool.rec (motive := fun _ => ℕ) (Nat.add o 1) (ih (Nat.add o 19)) (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)) n o
open AMW.Cert.{NS} in
def leafSkip (pos w : ℕ) : ST := fun {VARS} =>
  Bool.rec (motive := fun _ => ℕ)
    (forceR (yscan (Nat.shiftRight w 2) 42 (tscan (Nat.shiftRight w 2) 26 0)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u6 l0)
open AMW.Cert.{NS} in
def nodeSkip (bits : ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafSkip pos (Nat.shiftRight bits pos))
    (splitAx ih (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 6) 1) (Nat.add pos 7) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))
    (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)
open AMW.Cert.{NS} in
def walkCSkip (bits fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => nodeSkip bits ih pos) fuel
open AMW.Cert.{NS} in
def walkSkip (bits fuel : ℕ) : WF := fun pos => tm (walkCSkip bits fuel pos)
"""
bench("PFBenchNP", "PFNPInst", "PFNP")
bench("PFBenchDEC", "PFDECInst", "PFDEC")
bench("PFBenchSK", "PFDECInst", "PFDEC", SKIP)
