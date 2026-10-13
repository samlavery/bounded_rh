#!/usr/bin/env python3
"""(bridge-port) Timing prototype, structure-accumulator form of `mleafC`: the per-term steps pass an accumulator
structure `MA` (offset, value side, charge side, per-gap slope sums and slope weights, side-condition flag) by nested
application; fields stay explicit sums (no packing), which is the form the soundness proof wants.
Emits ROOT/AMW/{NAME}MS.lean.  Usage: bp_mleafs.py ROOT NAME"""
import sys, os
ROOT, NAME = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(HERE, "..", ROOT, "AMW")
toks = open(os.path.join(HERE, f"{NAME}_params.txt")).read().split()
Q = int(toks[0]); aN = [int(x) for x in toks[2].split(",")]; bN = [int(x) for x in toks[3].split(",")]; cN = int(toks[4])
PAIRS = [(i, j) for i in range(Q) for j in range(i + 1, Q + 1)]
DT = [t for t in range(len(PAIRS)) if aN[t] != 0]
SC, U, U1 = 32768, 10**10, 10**9
F = ["o", "A", "B"] + [f"p{r}" for r in range(Q)] + [f"s{r}" for r in range(Q)]
HDR = "(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))"
out = [f"import AMW.{NAME}Inst", "", "set_option maxRecDepth 100000", "", "noncomputable section", "",
       f"namespace AMW.Cert.{NAME}MS", "", f"open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.{NAME}", "",
       "/-- the accumulator of a minorant leaf -/",
       "structure MA where\n  (ok : Bool) (" + " ".join(F) + " : ℕ)", "",
       "/-- evaluate a natural before continuing with an accumulator -/",
       "def forceM (a : ℕ) (k : ℕ → MA) : MA := Nat.rec (motive := fun _ => MA) (k 0) (fun n _ => k (Nat.succ n)) a", ""]
def mk(ok, upd):
    return "⟨" + ok + ", " + ", ".join(upd.get(f, f"acc.{f}") for f in F) + "⟩"
V = lambda X: f"(lo32 {X})"; PP = lambda X: f"(lo32 (hi32 {X}))"; MM = lambda X: f"(hi32 (hi32 {X}))"
TC = lambda p, X: f"(tcheck R L U {p} {X} (treadU R tD bD U {p}) (treadD R tD bD L {p}))"
for t in DT:
    i, j = PAIRS[t]; a = aN[t]; gaps = range(i, j)
    def upd(olen, val, cp, cn):
        u = {"o": f"(Nat.add acc.o {olen})", "A": f"(Nat.add acc.A (Nat.add (Nat.mul {SC * a} {val}) (Nat.mul {10 * a} {cp})))",
             "B": f"(Nat.add acc.B (Nat.mul {a} {cn}))"}
        for r in gaps:
            u[f"p{r}"] = f"(Nat.add acc.p{r} sp)"; u[f"s{r}"] = f"(Nat.add acc.s{r} sw)"
        return u
    uA = upd(6, f"(Nat.mul 1024 {V('X')})", f"(Nat.mul (Nat.mul 1024 (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L))",
             f"(Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L))")
    uB = upd(16, f"(Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m {V('X')}))",
             f"(Nat.mul (Nat.mul m (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L))",
             f"(Nat.mul (Nat.mul m (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L))")
    uC = upd(20, f"(Nat.add (Nat.mul (Nat.sub 1024 m) {V('X')}) (Nat.mul m {V('Y')}))",
             f"(Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub {MM('Y')} 2000000000)) (Nat.sub r L)))",
             f"(Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 {MM('Y')})) (Nat.sub r L)))")
    uZ = {"o": "(Nat.add acc.o 2)", "A": f"(Nat.add acc.A (Nat.mul {SC * a * 1024} (lb top bk L U)))"}
    out.append(f"""def ta{t} {HDR} (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul {a * 1024} {PP('X')}) fun sp =>
  forceM {2 * U1 * a * 1024} fun sw =>
  {mk(f"(acc.ok && {TC('p', 'X')})", uA)}

def tb{t} {HDR} (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul {a} (Nat.mul m {PP('X')})) fun sp =>
  forceM (Nat.mul {2 * U1 * a} m) fun sw =>
  {mk(f"(acc.ok && (Nat.beq m 0 || {TC('p', 'X')}))", uB)}

def tc{t} {HDR} (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul {a} (Nat.add (Nat.mul (Nat.sub 1024 m) {PP('X')}) (Nat.mul m {PP('Y')}))) fun sp =>
  forceM {2 * U1 * a * 1024} fun sw =>
  {mk(f"(acc.ok && ((Nat.beq m 1024 || {TC('p', 'X')}) && (Nat.beq m 0 || {TC('r', 'Y')})))", uC)}

def st{t} {HDR} (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc{t} top bk tD bD pb R w L U o acc) (tb{t} top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta{t} top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    {mk("acc.ok", uZ)} (Nat.beq k 0)
""")
box = " ".join(f"l{r} u{r}" for r in range(Q))
def ns(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e
chain = "⟨true, " + ", ".join("0" for _ in F) + "⟩"
for t in DT:
    i, j = PAIRS[t]
    chain = f"(st{t} top bk tD bD pb R w {ns('l', i, j)} {ns('u', i, j)} {chain})"
linb = "0"
for r in range(Q): linb = f"(Nat.add {linb} (Nat.mul {bN[r]} l{r}))"
neg = "0"
for r in range(Q):
    neg = f"(Nat.add {neg} (Nat.mul (Nat.sub u{r} l{r}) (Nat.sub acc.s{r} (Nat.add {1024 * U1 * bN[r]} acc.p{r}))))"
final = f"Nat.ble (Nat.add {1024 * cN * SC * U} (Nat.mul 10 (Nat.add acc.B {neg}))) (Nat.add (Nat.mul {1024 * U} {linb}) acc.A)"
out.append(f"""def mleafS {HDR} (w {box} : ℕ) : ℕ :=
  let acc := {chain}
  Bool.rec (motive := fun _ => ℕ) 0 acc.o (acc.ok && {final})

end AMW.Cert.{NAME}MS
""")
open(os.path.join(P, f"{NAME}MS.lean"), "w").write("\n".join(out))
print("written", len(DT), "steps")
