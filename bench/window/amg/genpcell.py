#!/usr/bin/env python3
"""(bridge-port) Polytope-cell certificate layer (pair-distance splits) for Q gaps: emits ROOT/AMW/{NAME}.lean.

A cell is the box l_r <= SC g_r <= u_r cut by A_t <= SC s_t <= B_t for every non-adjacent pair t = (i, j), s_t = g_i + ...
+ g_{j-1} (absent bounds: A_t = 0, B_t large), so the walk state is the fixed tuple (l_r, u_r)_r, (A_t, B_t)_t.
Emitted: the functional G, InCell / Covered (Covered'), the split lemmas (gap and pair sum), the empty-range lemma,
the bound tightening (Jacobi per constraint, NR rounds, constraints in pair order) with its soundness, the multiplier
accumulator (list of (constraint, side, Yq) entries) with its validity invariant, the minorant leaf check with effective
ranges and multipliers (mcheckP) with its soundness, the leaf decoder, the walk and its soundness.

Usage: genpcell.py ROOT NAME Q [--bench]   (Q = 3: the toy weights; Q = 7: the AMT8 weights; --bench: definitions only,
with the AMT8 box leaves in place of the polytope leaf, for kernel timing)"""
import sys, os

ROOT, NAME, Q = sys.argv[1], sys.argv[2], int(sys.argv[3])
BENCH = "--bench" in sys.argv
NR = int(os.environ.get("NR", "2"))          # rounds of bound tightening per node
QB = int(os.environ.get("QB", "12"))         # bits of a multiplier field Yq
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [(i, j) for (i, j) in PAIRS if j - i >= 2]
NC = len(SUMS)
if Q == 3:
    BW = [31833, 58928, 31833]
    AW = {(0, 1): 16291486, (0, 2): 59631729, (0, 3): 100000000, (1, 2): 32082429, (1, 3): 59631729, (2, 3): 16291486}
    CN = int(os.environ.get("CN", "550000"))
elif Q == 7:
    BW = [31833, 58928, 69744, 83339, 69744, 58928, 31833]
    AL = [16291486, 0, 0, 100000000, 39006345, 100000000, 200000000, 32082429, 3747073, 59631729, 0, 121987310, 100000000,
          32723633, 96252927, 80736542, 0, 39006345, 37804904, 96252927, 59631729, 100000000, 32723633, 3747073, 0, 32082429, 0,
          16291486]
    AW = dict(zip(PAIRS, AL)); CN = 557992
else:
    raise SystemExit("Q = 3 or 7")
ACT = [t for t in PAIRS if AW[t] > 0]
SIGSH = int(os.environ.get("SIGSH", "14"))   # the multiplier quantum 2^-SIGSH per unit g (mvt-engine: 2^-14 costs +3 % leaves)
SIG = max(1, (1024 * 1000000000 * 100000000) >> SIGSH)
CB = max(1, (NC - 1).bit_length())           # bits of a constraint index
AXB = max(1, (Q + NC - 1).bit_length())      # bits of a split axis
SPB = 1 + AXB                                # bits of a split node
EB = 1 + CB + 1 + QB                         # bits of a multiplier entry

def nm(t): return f"{t[0]}{t[1]}"
GS = [f"g{r}" for r in range(Q)]
STV = [x for r in range(Q) for x in (f"l{r}", f"u{r}")] + [x for t in SUMS for x in (f"A{nm(t)}", f"B{nm(t)}")]
MASK = os.environ.get("MASK") == "1"   # an active-constraint mask M in the state: tightening skips constraints never split
if MASK: STV.append("M")
ST = " ".join(STV)
def st(**kw): return " ".join(kw.get(v, v) for v in STV)
HV = [x for r in range(Q) for x in (f"hl{r}", f"hu{r}")] + [x for t in SUMS for x in (f"hA{nm(t)}", f"hB{nm(t)}")]
def hv(**kw): return ", ".join(kw.get(v, v) for v in HV)
NAT = " ".join(["ℕ"] * len(STV))

# ---- a small expression tree, printed in kernel form (Nat.add ...) or infix form (the simp normal form) ----
def A(x): return ("a", x)
def add(*xs):
    xs = [x for x in xs if x is not None]
    return xs[0] if len(xs) == 1 else ("+", xs)
def mul(a, b): return ("*", a, b)
def sub(a, b): return ("-", a, b)
def K(e):
    if e[0] == "a": return e[1]
    if e[0] == "+":
        s = K(e[1][0])
        for x in e[1][1:]: s = f"Nat.add {par(s)} {par(K(x))}"
        return s
    op = {"*": "Nat.mul", "-": "Nat.sub"}[e[0]]
    return f"{op} {par(K(e[1]))} {par(K(e[2]))}"
def I(e):
    if e[0] == "a": return e[1]
    if e[0] == "+": return " + ".join(I(x) if x[0] == "a" else f"({I(x)})" for x in e[1])
    return f"{pi(e[1])} {e[0]} {pi(e[2])}"
def pi(e): return I(e) if e[0] == "a" else f"({I(e)})"
def grp(s):
    """`s` is one parenthesised group"""
    if not s.startswith("("): return False
    d = 0
    for i, c in enumerate(s):
        d += (c == "(") - (c == ")")
        if d == 0: return i == len(s) - 1
    return False
def par(s): return s if " " not in s or grp(s) else f"({s})"

def sl(t): return add(*[A(f"l{r}") for r in range(*t)])
def su(t): return add(*[A(f"u{r}") for r in range(*t)])
def sg(t): return " + ".join(f"g{r}" for r in range(*t))
def single(t): return t[1] - t[0] == 1
def mset(t): return {"M": f"(Nat.lor M {1 << SUMS.index(t)})"} if MASK else {}
def Le(t): return A(f"l{t[0]}") if single(t) else ("a", f"(nmax A{nm(t)} {par(K(sl(t)))})")
def Ue(t): return A(f"u{t[0]}") if single(t) else ("a", f"(nmin B{nm(t)} {par(K(su(t)))})")
def LeI(t): return f"l{t[0]}" if single(t) else f"(nmax A{nm(t)} {pi(sl(t))})"
def UeI(t): return f"u{t[0]}" if single(t) else f"(nmin B{nm(t)} {pi(su(t))})"
def chain(lem, hs):
    s = hs[0]
    for h in hs[1:]: s = f"{lem} ({s}) {h}" if " " in s else f"{lem} {s} {h}"
    return s
def slo(rs): return chain("slo_add", [f"hl{r}" for r in rs])
def shi(rs): return chain("shi_add", [f"hu{r}" for r in rs])
def lnest(names):
    return "⟨" * (len(names) - 1) + names[0] + "".join(f", {x}⟩" for x in names[1:])

out = []
W = out.append
imports = "import AMW.PCellCore\n" + ("import AMW.AMT8Inst\n" if BENCH else "")
W(f"""{imports}
/-! ###### polytope cells for Q = {Q} (pair-distance splits; bridge-port, generated by amg/genpcell.py)

The cell: the box `l_r ≤ SC g_r ≤ u_r` cut by `A_t ≤ SC s_t ≤ B_t` for every non-adjacent pair `t = (i, j)`,
`s_t = g_i + … + g_{{j−1}}` (absent bounds `A_t = 0`, `B_t` large): the walk state is the fixed tuple of {2 * Q} gap and
{2 * NC} pair bounds.  Splits on a gap at the midpoint of `[l_r, u_r]`, or on a pair distance at the midpoint of its
effective range `[max(A_t, Σ l), min(B_t, Σ u)]`; every node first tightens the gap bounds against the pair bounds
({NR} rounds, Jacobi per constraint, constraints in pair order) and is an empty leaf (no bits) when an effective range
is empty.  The minorant leaf reads each term on its effective range, expands it at the term's box corner, and adds
multipliers `y ≥ 0` on the pair bounds: `G ≥ G − Σ y⁺ (s_t − A_t) − Σ y⁻ (B_t − s_t)` on the cell, which moves only the
gap slopes and the constant.  Engine, tables and per-term minorants: mvt-engine's MinCore on the AM engine
(pyramid oracle adapted from five-point-pyramid-2 by typh, convex basins after six-point-convex-basins-2 by typh,
Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.{NAME}

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def SA : ℕ := 100000000
def cN : ℕ := {CN}
/-- the multiplier quantum (a per-certificate constant): a multiplier is `SIG · Yq`, `Yq < 2^{QB}`; `SIG = 1024 U1 SA / 2^{SIGSH}` -/
def SIG : ℕ := {SIG}
""")

# ---- G, InCell, Covered ----
gl = " + ".join(f"({BW[r]} / (SA:ℝ)) * g{r}" for r in range(Q))
gw = " + ".join(f"({AW[t]} / (SA:ℝ)) * wfun ({sg(t)})" for t in ACT)
W(f"""/-- the weighted functional on the gaps -/
def G ({" ".join(GS)} : ℝ) : ℝ :=
  {gl}
    + {gw}

/-- the polytope cell -/
def InCell ({ST} : ℕ) ({" ".join(GS)} : ℝ) : Prop :=
  """ + " ∧ ".join([f"(l{r} : ℝ) / SC ≤ g{r} ∧ g{r} ≤ (u{r} : ℝ) / SC" for r in range(Q)]
                     + [f"(A{nm(t)} : ℝ) / SC ≤ {sg(t)} ∧ {sg(t)} ≤ (B{nm(t)} : ℝ) / SC" for t in SUMS]) + f"""

/-- (1) the cell satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered ({ST} : ℕ) : Prop :=
  ∀ {" ".join(GS)} : ℝ, InCell {ST} {" ".join(GS)} → (cN : ℝ) / SA ≤ G {" ".join(GS)} ∨ g{Q - 1} < g0
""")

# ---- split lemmas ----
for r in range(Q):
    W(f"""theorem covered_gsplit{r} {{{ST} : ℕ}} (q : ℕ) (hA : Covered {st(**{f"u{r}": "q"})})
    (hB : Covered {st(**{f"l{r}": "q"})}) : Covered {ST} := by
  rintro {" ".join(GS)} ⟨{hv()}⟩
  rcases le_total g{r} ((q : ℝ) / SC) with h | h
  · exact hA {" ".join(GS)} ⟨{hv(**{f"hu{r}": "h"})}⟩
  · exact hB {" ".join(GS)} ⟨{hv(**{f"hl{r}": "h"})}⟩
""")
for t in SUMS:
    n = nm(t)
    W(f"""/-- (2) the split on the pair distance `{sg(t)}` at any `q` -/
theorem covered_ssplit{n} {{{ST} : ℕ}} (q : ℕ) (hA : Covered {st(**{f"B{n}": "q"})})
    (hB : Covered {st(**{f"A{n}": "q"})}) : Covered {ST} := by
  rintro {" ".join(GS)} ⟨{hv()}⟩
  rcases le_total ({sg(t)}) ((q : ℝ) / SC) with h | h
  · exact hA {" ".join(GS)} ⟨{hv(**{f"hB{n}": "h"})}⟩
  · exact hB {" ".join(GS)} ⟨{hv(**{f"hA{n}": "h"})}⟩

/-- (4) an empty effective range of `{sg(t)}`: the cell is empty -/
theorem covered_empty{n} {{{ST} : ℕ}} (he : Nat.blt (nmin B{n} {par(K(su(t)))}) (nmax A{n} {par(K(sl(t)))}) = true) :
    Covered {ST} := by
  rintro {" ".join(GS)} ⟨{hv()}⟩
  exact (range_empty hA{n} ({slo(range(*t))}) hB{n} ({shi(range(*t))}) he).elim
""")

# ---- bound tightening ----
W(f"""/-- a continuation on the cell bounds -/
abbrev ST : Type := {" → ".join(["ℕ"] * (len(STV) + 1))}

/-- every non-failing run of `k` covers its cell -/
def CovK (k : ST) : Prop := ∀ {ST} : ℕ, k {ST} ≠ 0 → Covered {ST}
""")
for t in SUMS:
    n = nm(t); rs = list(range(*t)); ci = SUMS.index(t)
    mopen = f"Bool.rec (motive := fun _ => ℕ) (k {ST}) (" if MASK else ""
    mclose = f") (Nat.beq (Nat.land (Nat.shiftRight M {ci}) 1) 1)" if MASK else ""
    body = "".join(f"forceR (nmax l{r} (Nat.sub Le (Nat.sub su u{r}))) fun l{r}' => forceR (nmin u{r} (Nat.sub Ue (Nat.sub sl l{r}))) fun u{r}' =>\n     " for r in rs)
    W(f"""/-- (5) bound tightening against `A{n} ≤ SC ({sg(t)}) ≤ B{n}` (Jacobi: every new gap bound from the old ones), then
`k`; `pos` (an empty leaf, no bits) when the effective range is empty -/
def fb{n} (pos : ℕ) (k : ST) ({ST} : ℕ) : ℕ :=
  {mopen}forceR {par(K(sl(t)))} fun sl => forceR {par(K(su(t)))} fun su =>
  forceR (nmax A{n} sl) fun Le => forceR (nmin B{n} su) fun Ue =>
  Bool.rec (motive := fun _ => ℕ)
    ({body}k {st(**{v: v + "'" for r in rs for v in (f"l{r}", f"u{r}")})})
    pos (Nat.blt Ue Le){mclose}
""")
    facts = {}
    for r in rs:
        oth = [x for x in rs if x != r]
        og = " + ".join(f"g{x}" for x in oth); ou = " + ".join(f"u{x}" for x in oth); ol = " + ".join(f"l{x}" for x in oth)
        facts[f"hl{r}"] = (f"fb_lo (o := {og}) (ou := {ou}) (by first | rfl | omega | (simp only [Nat.add_eq]; omega)) hl{r} (by linarith) ({shi(oth)})")
        mskip = (f"\n  cases hmk : Nat.beq (Nat.land (Nat.shiftRight M {ci}) 1) 1\n  · rw [hmk] at h; exact hk {ST} h\n  rw [hmk] at h" if MASK else "")
        facts[f"hu{r}"] = (f"fb_hi (o := {og}) (ol := {ol}) (by first | rfl | omega | (simp only [Nat.add_eq]; omega)) hu{r} (by linarith) ({slo(oth)})")
    W(f"""theorem fb{n}_sound {{pos : ℕ}} {{k : ST}} (hk : CovK k) : CovK (fb{n} pos k) := by
  intro {ST} h
  unfold fb{n} at h{mskip}
  simp only [forceR_eq] at h
  rintro {" ".join(GS)} ⟨{hv()}⟩
  have hlo : ((nmax A{n} {par(K(sl(t)))} : ℕ) : ℝ) / SC ≤ {sg(t)} := lo_nmax hA{n} ({slo(rs)})
  have hhi : {sg(t)} ≤ ((nmin B{n} {par(K(su(t)))} : ℕ) : ℝ) / SC := hi_nmin hB{n} ({shi(rs)})
  cases he : Nat.blt (nmin B{n} {par(K(su(t)))}) (nmax A{n} {par(K(sl(t)))})
  · rw [he] at h
    exact hk _ {" ".join(["_"] * (len(STV) - 1))} h {" ".join(GS)}
      ⟨{hv(**facts)}⟩
  · exact (range_empty hA{n} ({slo(rs)}) hB{n} ({shi(rs)}) he).elim
""")
rnd = "k"
for t in reversed(SUMS): rnd = f"fb{nm(t)} pos ({rnd})"
rnds = "k"; rnds_p = "hk"
for _ in range(NR): rnds = f"fbR pos ({rnds})"; rnds_p = f"fbR_sound ({rnds_p})"
rp = "hk"
for t in reversed(SUMS): rp = f"fb{nm(t)}_sound ({rp})"
W(f"""/-- one round of bound tightening: every pair constraint once, in pair order -/
def fbR (pos : ℕ) (k : ST) : ST := {rnd}
/-- the tightening of a node: {NR} rounds -/
def fbN (pos : ℕ) (k : ST) : ST := {rnds}

theorem fbR_sound {{pos : ℕ}} {{k : ST}} (hk : CovK k) : CovK (fbR pos k) := {rp}
theorem fbN_sound {{pos : ℕ}} {{k : ST}} (hk : CovK k) : CovK (fbN pos k) := {rnds_p}
""")

# ---- multipliers ----
PV = [f"P{r}" for r in range(Q)]; SV = [f"S{r}" for r in range(Q)]
YF = ["o"] + PV + SV + ["Cp", "Cm"]
def yk(**kw): return "⟨" + ", ".join(kw.get(f, f"y.{f}") for f in YF) + "⟩"
mexpr = " + ".join(f"((y.P{r} : ℝ) - y.S{r}) * (32768 * g{r} - l{r})" for r in range(Q))
W(f"""/-- the multiplier accumulator: end offset, per-gap slope charges `P_r` and gains `S_r`, constant charge `Cp` and gain `Cm` -/
structure YA where
  ({" ".join(YF)} : ℕ)

/-- the accumulated multipliers are valid on the cell: `Σ y (slack) = (Cp − Cm) + Σ_r (P_r − S_r)(SC g_r − l_r) ≥ 0` -/
def MulOK ({ST} : ℕ) (y : YA) : Prop :=
  ∀ {" ".join(GS)} : ℝ, InCell {ST} {" ".join(GS)} → 0 ≤ ((y.Cp : ℝ) - y.Cm) + {mexpr}

theorem MulOK_zero ({ST} o : ℕ) : MulOK {ST} ⟨o, {", ".join(["0"] * (len(YF) - 1))}⟩ := by
  intro {" ".join(GS)} _; simp

theorem brec_okY {{P : YA → Prop}} {{a b : YA}} (ha : P a) (hb : P b) (c : Bool) :
    P (Bool.rec (motive := fun _ => YA) a b c) := by cases c <;> assumption

/-- evaluate a natural before continuing with an accumulator -/
def forceY (a : ℕ) (k : ℕ → YA) : YA := Nat.rec (motive := fun _ => YA) (k 0) (fun n _ => k (Nat.succ n)) a
theorem forceY_eq (a : ℕ) (k : ℕ → YA) : forceY a k = k a := by cases a <;> rfl
""")
for t in SUMS:
    n = nm(t); rs = list(range(*t))
    lo = yk(o="o", **{f"P{r}": f"(Nat.add y.P{r} Y)" for r in rs}, Cp=f"(Nat.add y.Cp (Nat.mul Y (Nat.sub {par(K(sl(t)))} A{n})))",
            Cm=f"(Nat.add y.Cm (Nat.mul Y (Nat.sub A{n} {par(K(sl(t)))})))")
    hi = yk(o="o", **{f"S{r}": f"(Nat.add y.S{r} Y)" for r in rs}, Cp=f"(Nat.add y.Cp (Nat.mul Y (Nat.sub B{n} {par(K(sl(t)))})))",
            Cm=f"(Nat.add y.Cm (Nat.mul Y (Nat.sub {par(K(sl(t)))} B{n})))")
    W(f"""/-- a multiplier `Y` on `A{n} ≤ SC ({sg(t)})` (side 0) or on `SC ({sg(t)}) ≤ B{n}` (side 1) -/
def yc{n} ({ST} : ℕ) (o sd Y : ℕ) (y : YA) : YA :=
  Bool.rec (motive := fun _ => YA)
    {lo}
    {hi}
    (Nat.beq sd 1)

theorem yc{n}_ok {{{ST} : ℕ}} {{o sd Y : ℕ}} {{y : YA}} (hy : MulOK {ST} y) :
    MulOK {ST} (yc{n} {ST} o sd Y y) := by
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  unfold yc{n}
  apply brec_okY
  · intro {" ".join(GS)} hc
    have h0 := hy {" ".join(GS)} hc
    obtain ⟨{hv()}⟩ := hc
    rw [hSCe] at hA{n}
    have hm := mul_nonneg (Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ)) (show (0:ℝ) ≤ 32768 * ({sg(t)}) - (A{n} : ℝ) by linarith)
    have hd := congrArg (fun x => (Y : ℝ) * x) (natsub_diff ({I(sl(t))}) A{n})
    try simp only at hd
    dsimp only
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast at hd ⊢
    linarith
  · intro {" ".join(GS)} hc
    have h0 := hy {" ".join(GS)} hc
    obtain ⟨{hv()}⟩ := hc
    rw [hSCe] at hB{n}
    have hm := mul_nonneg (Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ)) (show (0:ℝ) ≤ (B{n} : ℝ) - 32768 * ({sg(t)}) by linarith)
    have hd := congrArg (fun x => (Y : ℝ) * x) (natsub_diff B{n} ({I(sl(t))}))
    try simp only at hd
    dsimp only
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast at hd ⊢
    linarith
""")
disp = f"⟨o, {', '.join(f'y.{f}' for f in YF[1:])}⟩"
for ci in reversed(range(NC)):
    disp = f"Bool.rec (motive := fun _ => YA) ({disp}) (yc{nm(SUMS[ci])} {ST} o sd Y y) (Nat.beq c {ci})"
dp = "(by intro _ _ _ _ hc; exact hy _ _ _ hc)" if Q == 3 else None
dp = f"(by intro {' '.join(['_'] * Q)} hc; exact hy {' '.join(['_'] * Q)} hc)"
for ci in reversed(range(NC)):
    dp = f"brec_okY ({dp}) (yc{nm(SUMS[ci])}_ok hy) _"
CM = (1 << CB) - 1; QM = (1 << QB) - 1
W(f"""/-- a multiplier entry: constraint `c` (pair order), side `sd`, value `Y`; `o` the new offset -/
def yadd ({ST} : ℕ) (o c sd Y : ℕ) (y : YA) : YA :=
  {disp}

theorem yadd_ok {{{ST} : ℕ}} {{o c sd Y : ℕ}} {{y : YA}} (hy : MulOK {ST} y) :
    MulOK {ST} (yadd {ST} o c sd Y y) := by
  unfold yadd
  exact {dp}

/-- one multiplier entry from bit `o` of `w`: `1`, `c` ({CB} bits), side (1 bit), `Yq` ({QB} bits); a `0` closes the list -/
def ystep ({ST} : ℕ) (w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceY y.o fun o =>
  Bool.rec (motive := fun _ => YA)
    {yk(o="(Nat.add o 1)")}
    (ih (yadd {ST} (Nat.add o {EB}) (Nat.land (Nat.shiftRight w (Nat.add o 1)) {CM})
      (Nat.land (Nat.shiftRight w (Nat.add o {1 + CB})) 1) (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o {2 + CB})) {QM})) y))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

/-- the multiplier list (at most `fuel` entries) -/
def ydec ({ST} : ℕ) (w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep {ST} w ih) fuel

theorem ydec_ok {{{ST} : ℕ}} (w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK {ST} y → MulOK {ST} (ydec {ST} w fuel y)
  | 0, _, h => h
  | n + 1, y, h => by
    show MulOK {ST} (ystep {ST} w (ydec {ST} w n) y)
    unfold ystep
    rw [forceY_eq]
    exact brec_okY (by intro {" ".join(GS)} hc; exact h {" ".join(GS)} hc) (ydec_ok w n _ (yadd_ok h)) _
""")

# ---- the leaf check ----
def F(t): return f"k{nm(t)} m{nm(t)} p{nm(t)} r{nm(t)}"
FL = " ".join(F(t) for t in ACT)
def mw(t): return add(A(f"(mw1 k{nm(t)} m{nm(t)})"), A(f"(mw2 k{nm(t)} m{nm(t)})"))
def mslt(t): return A(f"(msl f (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)})")
def L0(t): return sl(t)
terms_r = {r: [t for t in ACT if t[0] <= r < t[1]] for r in range(Q)}
Am = add(*[mul(A(str(AW[t])), A(f"(mval top bk f {par(K(Le(t)))} {par(K(Ue(t)))} (mwc k{nm(t)} m{nm(t)}) (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)})")) for t in ACT])
AmI = add(*[mul(A(str(AW[t])), A(f"(mval top bk f {LeI(t)} {UeI(t)} (mwc k{nm(t)} m{nm(t)}) (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)})")) for t in ACT])
def Ap(I_): return add(*[mul(A(str(AW[t])), A(f"(mcp f {par(I_(L0(t)))} (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)})")) for t in ACT])
def Bm(I_): return add(*[mul(A(str(AW[t])), A(f"(mcn f {par(I_(L0(t)))} (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)})")) for t in ACT])
def Xr(r): return add(mul(A("2000000000"), add(*[mul(A(str(AW[t])), mw(t)) for t in terms_r[r]])), A(f"P{r}"))
def Yr(r): return add(A(str(1024 * 1000000000 * BW[r])), *[mul(A(str(AW[t])), mslt(t)) for t in terms_r[r]], A(f"S{r}"))
def Nr(r): return sub(Xr(r), Yr(r))
BL = add(*[mul(A(str(BW[r])), A(f"l{r}")) for r in range(Q)])
KC = 1024 * 32768 * 10000000000
def lhs(I_, AmX): return add(mul(A(str(KC)), A("cN")), mul(A("10"), add(Bm(I_), A("Cp"), *[mul(sub(A(f"u{r}"), A(f"l{r}")), Nr(r)) for r in range(Q)])))
def rhs(AmX): return add(mul(A("10240000000000"), BL), mul(A("32768"), AmX), mul(A("10"), add(Ap(K), A("Cm"))))
conds = [f"Nat.ble l{r} u{r}" for r in range(Q)]
for t in ACT:
    conds += [f"Nat.ble m{nm(t)} 1024", f"mok R tD bD f {par(K(Le(t)))} {par(K(Ue(t)))} (mw1 k{nm(t)} m{nm(t)}) (mw2 k{nm(t)} m{nm(t)}) p{nm(t)} r{nm(t)}"]
main = f"Nat.ble ({K(lhs(K, Am))}) ({K(add(mul(A('10240000000000'), BL), mul(A('32768'), Am), mul(A('10'), add(Ap(K), A('Cm')))))})"
W(f"""/-- (3) the minorant leaf on the polytope cell: per term its kind `k`, weight `m` and points `p`, `r` on its effective
range, and the accumulated multipliers: `1024 cN SC U + RU (Σ a mcn + Cp + Σ_r (u − l) N_r) ≤ 1024 U Σ b l + SC Σ a mval
+ RU (Σ a mcp + Cm)`, `N_r = (KU1 Σ a (mw1 + mw2) + P_r − 1024 U1 b_r − Σ a msl − S_r)⁺` -/
def mcheckP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) ({ST} : ℕ)
    ({FL} : ℕ) ({" ".join(PV + SV)} Cp Cm : ℕ) : Bool :=
  {" && ".join(conds)}
  && {main}
""")
if not BENCH:
    hn = [f"hlu{r}" for r in range(Q)] + [x for t in ACT for x in (f"hm{nm(t)}", f"hok{nm(t)}")] + ["hmain"]
    tl = []
    for t in ACT:
        n = nm(t); rs = list(range(*t))
        if single(t):
            r = t[0]
            tl.append(f"""  obtain ⟨D{n}, hDl{n}, hb{n}⟩ := mterm_okA hlb hD hpt hR l{r} l{r} u{r} k{n} m{n} p{n} r{n} le_rfl hm{n} hok{n}
    g{r} hl{r} hu{r}""")
        else:
            tl.append(f"""  obtain ⟨D{n}, hDl{n}, hb{n}⟩ := mterm_okA hlb hD hpt hR ({I(sl(t))}) {LeI(t)} {UeI(t)} k{n} m{n} p{n} r{n}
    (le_nmax_right _ _) hm{n} hok{n} ({sg(t)}) (lo_nmax hA{n} ({slo(rs)})) (hi_nmin hB{n} ({shi(rs)}))""")
        if not single(t): tl.append(f"  push_cast at hb{n}")
    gl_ = []
    def Ysub(e, r):   # the accumulator fields as projections of y
        return e
    for r in range(Q):
        X = I(Xr(r)).replace(f"P{r}", f"y.P{r}"); Y = I(Yr(r)).replace(f"S{r}", f"y.S{r}")
        E = f"(1024 * {BW[r]} : ℝ) + " + " + ".join(f"{AW[t]} * D{nm(t)}" for t in terms_r[r]) + f" - ((y.P{r} : ℝ) - y.S{r}) / 1000000000"
        lc = " + ".join(f"{AW[t]} * hDl{nm(t)}" for t in terms_r[r])
        gl_.append(f"""  have hN{r} : -((({X}) - ({Y}) : ℕ) : ℝ) ≤ 1000000000 * ({E}) := by
    have := natsub_ge ({X}) ({Y})
    push_cast at this ⊢
    linear_combination this + {lc}
  have hlu{r}' : ((u{r} - l{r} : ℕ) : ℝ) = (u{r} : ℝ) - l{r} := Nat.cast_sub hlu{r}
  have hg{r} := gap_lo (E := {E}) (e := g{r} - (l{r} : ℝ) / 32768) (H := ((u{r} - l{r} : ℕ) : ℝ))
    (natsub_nonneg _ _) hN{r} (sub_nonneg.mpr hl{r}) (by rw [hlu{r}', sub_div]; exact sub_le_sub_right hu{r} _)""")
    EGR = " + ".join(f"{BW[r]} * g{r}" for r in range(Q)) + " + " + " + ".join(f"{AW[t]} * wfun ({sg(t)})" for t in ACT)
    mb = ", ".join(f"mul_le_mul_of_nonneg_left hb{nm(t)} (by norm_num : (0:ℝ) ≤ {AW[t]})" for t in ACT)
    hus = ", ".join(f"hlu{r}'" for r in range(Q)); hgs = " ".join(f"hg{r}" for r in range(Q)); hgl = ", ".join(f"hg{r}" for r in range(Q))
    hlh = " ".join(f"hl{r} hu{r}" for r in range(Q))
    yfields = " ".join(f"y.{f}" for f in YF[1:])
    W(f"""theorem mcheckP_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{f : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) ({ST} : ℕ) ({FL} : ℕ) (y : YA)
    (hY : MulOK {ST} y) (h : mcheckP top bk tD bD f R {ST} {FL} {yfields} = true) :
    Covered {ST} := by
  intro {" ".join(GS)} hc
  have hYg := hY {" ".join(GS)} hc
  obtain ⟨{hv()}⟩ := hc
  left
  unfold mcheckP at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain {lnest(hn)} := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
""" + "\n".join(tl) + f"""
  rw [hSCe] at {hlh}
""" + "\n".join(gl_) + f"""
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  simp only [{hus}] at hq {hgs}
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have eG : G {" ".join(GS)} * (SA : ℝ) = {EGR} := by
    simp only [G, SA]; push_cast; ring
  rw [div_le_iff₀ hSA, eG]
  linarith [hq, {hgl}, {mb}, hYg]
""")

# ---- the leaf decoder ----
dec = []
for t in SUMS:
    n = nm(t)
    dec.append(f"  forceR (nmax A{n} {par(K(sl(t)))}) fun L{n} => forceR (nmin B{n} {par(K(su(t)))}) fun U{n} =>")
dec.append("  forceR 0 fun o0 =>")
for q, t in enumerate(ACT):
    n = nm(t); Lx = f"l{t[0]}" if single(t) else f"L{n}"; Ux = f"u{t[0]}" if single(t) else f"U{n}"
    dec.append(f"""  forceR (Nat.land (Nat.shiftRight w o{q}) 3) fun k{n} =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o{q} 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o{q} 6)) 1023) (Nat.beq k{n} 2)) fun m{n} =>
  forceR (gpt {Lx} {Ux} (Nat.land (Nat.shiftRight w (Nat.add o{q} 2)) 15)) fun p{n} =>
  forceR (gpt {Lx} {Ux} (Nat.land (Nat.shiftRight w (Nat.add o{q} 6)) 15)) fun r{n} =>
  forceR (Nat.add o{q} (plen k{n})) fun o{q + 1} =>""")
NA = len(ACT)
W(f"""/-- the payload length of a minorant term of kind `k` (as AMT8: 2, 6, 16, 20 bits) -/
def plen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 20 (Nat.beq k 3)) 16 (Nat.beq k 2)) 6 (Nat.beq k 1)

/-- the polytope minorant leaf: the payload length when the check passes, else `0`; the term fields as AMT8 with the
grid points on the effective ranges, then the multiplier list -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w {ST} : ℕ) : ℕ :=
""" + "\n".join(dec) + f"""
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (mcheckP top bk tD bD (pt3 pb) R {ST} {FL} {" ".join("y." + f for f in YF[1:])}))
  (ydec {ST} w 8 ⟨o{NA}, {", ".join(["0"] * (len(YF) - 1))}⟩)
""")
if not BENCH:
    W(f"""theorem mleafP_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w {ST} : ℕ)
    (h : mleafP top bk tD bD pb R w {ST} ≠ 0) : Covered {ST} := by
  unfold mleafP at h
  simp only [forceR_eq] at h
  exact mcheckP_sound (f := pt3 pb) hlb hD hpt hR {ST} {" ".join(["_"] * (4 * NA))} _
    (ydec_ok w 8 _ (MulOK_zero {ST} _)) (brec_ne h)
""")

# ---- the walk ----
W(f"""/-- a walk continuation: position and the cell bounds to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ST
""")
axes = []
for r in range(Q):
    W(f"""/-- a split on gap {r}: the lower half (`u{r} := q`) from `pos + {SPB}`, then the upper half -/
def gsplit{r} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l{r} u{r}) 1) fun q =>
  let p := ih (Nat.add pos {SPB}) {st(**{f"u{r}": "q"})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"l{r}": "q"})}) 0 (Nat.beq p 0)
""")
    axes.append(f"gsplit{r}")
for t in SUMS:
    n = nm(t)
    W(f"""/-- a split on the pair distance `{sg(t)}` at the midpoint of its effective range: `B{n} := q`, then `A{n} := q` -/
def ssplit{n} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add (nmax A{n} {par(K(sl(t)))}) (nmin B{n} {par(K(su(t)))})) 1) fun q =>
  let p := ih (Nat.add pos {SPB}) {st(**{f"B{n}": "q", **mset(t)})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"A{n}": "q", **mset(t)})}) 0 (Nat.beq p 0)
""")
    axes.append(f"ssplit{n}")
ax = "0"
for k in reversed(range(len(axes))):
    ax = f"Bool.rec (motive := fun _ => ℕ) ({ax}) ({axes[k]} ih pos {ST}) (Nat.beq ax {k})"
AXM = (1 << AXB) - 1
if BENCH:
    box = " ".join(f"l{r} u{r}" for r in range(Q))
    leaf = f"""/-- (bench) the AMT8 box leaf on the gap bounds -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w {ST} : ℕ) : ℕ :=
  AMW.Cert.AMT8.leafStep top bk tD bD pb R pos w {box}
"""
else:
    leaf = f"""/-- a leaf (bit 0 clear): the reflected half-space (`u{Q - 1} < l0`, no further bits), or the polytope minorant leaf with its
payload from bit 1 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w {ST} : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (mleafP top bk tD bD pb R (Nat.shiftRight w 1) {ST}) fun n => Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 1 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1)
    (Nat.blt u{Q - 1} l0)
"""
W(f"""/-- a split node: the axis selects a gap (`0 … {Q - 1}`) or a pair distance (`{Q} … {Q + NC - 1}`, pair order) -/
def splitAx (ih : WF) (pos ax {ST} : ℕ) : ℕ :=
  {ax}

{leaf}
/-- the walk (`Nat.rec` on the fuel): every node is first tightened (an empty node ends there, no bits); then the node
word is `bits >>> pos` (bit 0 split, bits 1..{AXB} axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ {" ".join(["_"] * len(STV))} => 0)
    (fun _ ih pos => fbN pos (fun {ST} =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos w {ST})
        (splitAx ih pos (Nat.land (Nat.shiftRight w 1) {AXM}) {ST}) (Nat.beq (Nat.land w 1) 1)))
    fuel
""")
if not BENCH:
    W(f"""def WalkOK (f : WF) : Prop := ∀ pos {ST} : ℕ, f pos {ST} ≠ 0 → Covered {ST}
""")
    for k, a in enumerate(axes):
        if a.startswith("g"):
            r = int(a[6:]); vA = {f"u{r}": f"(Nat.shiftRight (Nat.add l{r} u{r}) 1)"}; vB = {f"l{r}": f"(Nat.shiftRight (Nat.add l{r} u{r}) 1)"}
            lem = f"covered_gsplit{r}"
        else:
            n = a[6:]; t = (int(n[0]), int(n[1]))
            q = f"(Nat.shiftRight (Nat.add (nmax A{n} {par(K(sl(t)))}) (nmin B{n} {par(K(su(t)))})) 1)"
            vA = {f"B{n}": q, **mset(t)}; vB = {f"A{n}": q, **mset(t)}; lem = f"covered_ssplit{n}"
        W(f"""theorem {a}_sound {{ih : WF}} (hih : WalkOK ih) (pos {ST} : ℕ) (h : {a} ih pos {ST} ≠ 0) : Covered {ST} := by
  unfold {a} at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos {SPB}) {st(**vA)}) 0
  · have h' : ih (ih (Nat.add pos {SPB}) {st(**vA)}) {st(**vB)} ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos {SPB}) {st(**vA)} (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact {lem} _ hA (hih _ {st(**vB)} h')
  · exact absurd (by simp only [hp]) h
""")
    disp = f"exact absurd rfl h"
    lines = []
    ind = "  "
    for k, a in enumerate(axes):
        lines.append(f"{ind}cases ha{k} : Nat.beq ax {k}")
        lines.append(f"{ind}· rw [ha{k}] at h")
        ind += "  "
    lines.append(f"{ind}exact absurd rfl h")
    for k in reversed(range(len(axes))):
        ind = ind[:-2]
        lines.append(f"{ind}· rw [ha{k}] at h; exact {axes[k]}_sound hih pos {ST} h")
    W(f"""theorem splitAx_sound {{ih : WF}} (hih : WalkOK ih) (pos ax {ST} : ℕ) (h : splitAx ih pos ax {ST} ≠ 0) :
    Covered {ST} := by
  unfold splitAx at h
""" + "\n".join(lines) + f"""

theorem leafStep_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (pos w {ST} : ℕ)
    (h : leafStep top bk tD bD pb R pos w {ST} ≠ 0) : Covered {ST} := by
  unfold leafStep at h
  cases hs : Nat.blt u{Q - 1} l0
  · rw [hs, forceR_eq] at h
    exact mleafP_sound hlb hD hpt hR (Nat.shiftRight w 1) {ST} (by intro h0; rw [h0] at h; exact h rfl)
  · rintro {" ".join(GS)} ⟨{hv()}⟩
    right
    have hsk : u{Q - 1} < l0 := Nat.blt_eq.mp hs
    have : (u{Q - 1} : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) SC_pos
    linarith

theorem walk_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos {ST} h; exact absurd rfl h
  | succ fuel ih =>
    intro pos {ST} h
    have hk : CovK (fun {ST} => Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos) {ST})
        (splitAx (walk top bk tD bD pb R bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) {AXM}) {ST})
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)) := by
      intro {ST} h'
      beta_reduce at h'
      cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
      · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR pos _ {ST} h'
      · rw [hb] at h'; exact splitAx_sound ih pos _ {ST} h'
    exact fbN_sound hk {ST} h

theorem covered_of_walk {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits fuel {ST} e : ℕ)
    (h : walk top bk tD bD pb R bits fuel 1 {ST} = e) (he : e ≠ 0) : Covered {ST} :=
  walk_sound hlb hD hpt hR bits fuel 1 {ST} (h ▸ he)
""")
if not BENCH:
    root = {f"A{nm(t)}": "0" for t in SUMS}; root.update({f"B{nm(t)}": "W" for t in SUMS})
    if MASK: root["M"] = "0"
    BX = " ".join(f"l{r} u{r}" for r in range(Q))
    hyps = " → ".join(f"(l{r} : ℝ) / SC ≤ g{r} → g{r} ≤ (u{r} : ℝ) / SC" for r in range(Q))
    usum = " + ".join(f"u{r}" for r in range(Q))
    rf = {}
    for t in SUMS:
        rf[f"hA{nm(t)}"] = f"(by rw [Nat.cast_zero, zero_div]; linarith [{', '.join(f'hg{r}' for r in range(*t))}])"
        rf[f"hB{nm(t)}"] = (f"(le_trans ({shi(range(*t))}) (div_le_div_of_nonneg_right "
                            f"(by exact_mod_cast (show {I(su(t))} ≤ W by omega)) SC_pos.le))")
    W(f"""/-- the root: a box with every pair bound absent (`A = 0`, `B = W ≥ Σ u`) is covered once its polytope cell is -/
theorem covered_box {{{BX} : ℕ}} (W : ℕ) (hW : {usum} ≤ W) (h : Covered {st(**root)}) :
    ∀ {" ".join(GS)} : ℝ, {hyps} → (cN : ℝ) / SA ≤ G {" ".join(GS)} ∨ g{Q - 1} < g0 := by
  intro {" ".join(GS)} {" ".join(f"hl{r} hu{r}" for r in range(Q))}
""" + "".join(f"  have hg{r} : (0 : ℝ) ≤ g{r} := le_trans (div_nonneg (Nat.cast_nonneg _) SC_pos.le) hl{r}\n" for r in range(Q))
      + f"  exact h {' '.join(GS)} ⟨{hv(**rf)}⟩\n")
W(f"\nend AMW.Cert.{NAME}\n")
if BENCH:   # definitions only: drop every top-level theorem block
    txt = "\n".join(out); keep = []
    for ch in txt.split("\n\n"):
        heads = [ln for ln in ch.split("\n") if ln[:1].isalpha()]
        if heads and heads[0].startswith("theorem "): continue
        keep.append(ch)
    out = ["\n\n".join(keep)]
P = os.path.join(os.environ["PCOUT"], f"{NAME}.lean") if os.environ.get("PCOUT") else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW", f"{NAME}.lean")
open(P, "w").write("\n".join(out))
print(P, "pairs", len(PAIRS), "constraints", NC, "active terms", len(ACT), "SIG", SIG, "axis bits", AXB, "entry bits", EB)
