#!/usr/bin/env python3
"""(bridge-port) Timing prototype: the minorant leaf of an eight-point instance (AMT8 layout) evaluated as a chain of small
per-term steps over one packed accumulator (nested applications, every step's inputs forced), with zero-order
terms (κ = 0) reduced to one pyramid read.  Same leaf word as `mleafN`; computes the same inequality as `mscheck`.
Emits ROOT/AMW/{NAME}MC.lean (definitions + batch theorems).  Usage: bp_mleafc.py ROOT NAME"""
import sys, os, re, json
ROOT, NAME = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(HERE, "..", ROOT, "AMW")
toks = open(os.path.join(HERE, f"{NAME}_params.txt")).read().split()
Q = int(toks[0]); aN = [int(x) for x in toks[2].split(",")]; bN = [int(x) for x in toks[3].split(",")]; cN = int(toks[4])
PAIRS = [(i, j) for i in range(Q) for j in range(i + 1, Q + 1)]
DT = [t for t in range(len(PAIRS)) if aN[t] != 0]
SC, U, U1 = 32768, 10**10, 10**9
W = 100                        # accumulator field width
FO, FA, FB = 0, 1, 2           # fields: offset, value side, charge side
FSP = lambda r: 3 + r; FSW = lambda r: 3 + Q + r
SENT = 3 + 2 * Q               # sentinel field (keeps the accumulator nonzero)
def sh(x, f): return f"(Nat.shiftLeft {x} {W * f})" if f else x
def fld(acc, f): return f"(Nat.land (Nat.shiftRight {acc} {W * f}) {2**W - 1})"

out = [f"import AMW.{NAME}Inst", "", "set_option maxRecDepth 100000", "", "noncomputable section", "",
       f"namespace AMW.Cert.{NAME}MC", "", "open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.{NAME}".replace("{NAME}", NAME), ""]
def upd(t, gaps, a, olen, val, cp, cn, sl, wsum):
    e = (f"(Nat.add (Nat.add (Nat.add acc {olen}) {sh(f'(Nat.add (Nat.mul {SC * a} {val}) (Nat.mul {10 * a} {cp}))', FA)})"
         f" {sh(f'(Nat.mul {a} {cn})', FB)})")
    e = f"(Nat.add {e} (Nat.add {sh('sp', FSP(gaps[0]))} {sh('sw', FSW(gaps[0]))}))"
    for r in gaps[1:]:
        e = f"(Nat.add {e} (Nat.add {sh('sp', FSP(r))} {sh('sw', FSW(r))}))"
    return e
V = lambda X: f"(lo32 {X})"; PP = lambda X: f"(lo32 (hi32 {X}))"; MM = lambda X: f"(hi32 (hi32 {X}))"
TC = lambda p, X: f"(tcheck R L U {p} {X} (treadU R tD bD U {p}) (treadD R tD bD L {p}))"
HDR = "(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))"
for t in DT:
    i, j = PAIRS[t]; a = aN[t]
    gaps = list(range(i, j))
    # kind 1: the tangent at p alone (weight 1024)
    uA = upd(t, gaps, a, 6, f"(Nat.mul 1024 {V('X')})", f"(Nat.mul (Nat.mul 1024 (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L))",
             f"(Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L))", None, None)
    # kind 2: (1024 − m)·constant + m·tangent at p
    uB = upd(t, gaps, a, 16, f"(Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m {V('X')}))",
             f"(Nat.mul (Nat.mul m (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L))",
             f"(Nat.mul (Nat.mul m (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L))", None, None)
    # kind 3: (1024 − m)·tangent at p + m·tangent at r
    uC = upd(t, gaps, a, 20, f"(Nat.add (Nat.mul (Nat.sub 1024 m) {V('X')}) (Nat.mul m {V('Y')}))",
             f"(Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub {MM('X')} 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub {MM('Y')} 2000000000)) (Nat.sub r L)))",
             f"(Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 {MM('X')})) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 {MM('Y')})) (Nat.sub r L)))", None, None)
    out.append(f"""/-- term {t}, kind 1: the tangent at `p` -/
def ta{t} {HDR} (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul {a * 1024} {PP('X')}) fun sp =>
  forceR {2 * U1 * a * 1024} fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 {uA} {TC('p', 'X')}

/-- term {t}, kind 2: the constant and the tangent at `p` -/
def tb{t} {HDR} (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul {a} (Nat.mul m {PP('X')})) fun sp =>
  forceR (Nat.mul {2 * U1 * a} m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 {uB} (Nat.beq m 0 || {TC('p', 'X')})

/-- term {t}, kind 3: the tangents at `p` and `r` -/
def tc{t} {HDR} (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul {a} (Nat.add (Nat.mul (Nat.sub 1024 m) {PP('X')}) (Nat.mul m {PP('Y')}))) fun sp =>
  forceR {2 * U1 * a * 1024} fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 {uC} ((Nat.beq m 1024 || {TC('p', 'X')}) && (Nat.beq m 0 || {TC('r', 'Y')}))

/-- term {t} (gaps {i}..{j - 1}, weight {a}) -/
def st{t} {HDR} (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc{t} top bk tD bD pb R w L U acc o) (tb{t} top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta{t} top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) {sh(f'(Nat.mul {SC * a * 1024} (lb top bk L U))', FA)}) (Nat.beq k 0)
""")
box = " ".join(f"l{r} u{r}" for r in range(Q))
def ns(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e
chain = sh("1", SENT)
for t in DT:
    i, j = PAIRS[t]
    chain = f"(st{t} top bk tD bD pb R w {ns('l', i, j)} {ns('u', i, j)} {chain})"
lin = " ".join([])
linb = "0"
for r in range(Q): linb = f"(Nat.add {linb} (Nat.mul {bN[r]} l{r}))"
neg = "0"
for r in range(Q):
    neg = (f"(Nat.add {neg} (Nat.mul (Nat.sub u{r} l{r}) (Nat.sub {fld('acc', FSW(r))} "
           f"(Nat.add {1024 * U1 * bN[r]} {fld('acc', FSP(r))}))))")
final = (f"Nat.ble (Nat.add {1024 * cN * SC * U} (Nat.mul 10 (Nat.add {fld('acc', FB)} {neg}))) "
         f"(Nat.add (Nat.mul {1024 * U} {linb}) {fld('acc', FA)})")
out.append(f"""/-- the minorant leaf as a chain of term steps: the payload length when it passes, else `0` -/
def mleafC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w {box} : ℕ) : ℕ :=
  forceR {chain} fun acc =>
  Bool.rec (motive := fun _ => ℕ) 0 {fld('acc', FO)} (Nat.ble {2**(W*SENT)} acc && {final})
""")
out.append(f"end AMW.Cert.{NAME}MC\n")
open(os.path.join(P, f"{NAME}MC.lean"), "w").write("\n".join(out))
print("written", len(DT), "steps")
