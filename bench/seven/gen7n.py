#!/usr/bin/env python3
"""Instance checker for the weighted seven-point certificate (six gaps): functional `G`, the zero-order test
`leafOK`, the slope test `ctest` (expansion point `q`, expansion set `T`, convex set `V`), the walk (leaf kinds: zero-order, slope
with a 33-bit payload, basin), and their soundness; the per-gap cover and `of_check` (from gen_cover7.py).
Usage (module): checker(NAME, SA, aN, bN, cN, ORDER, JCQ) -> str"""
import os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
Q = 6
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
NP = len(PAIRS)
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]
SC = 1 << 15; U = 10**10; U1 = 10**9; KU1 = 2 * U1; RU = U // U1
CO = [f"l{r} u{r}" for r in range(Q)]; COORDS = " ".join(CO)
QV = " ".join(f"q{r}" for r in range(Q))
V = [f"g{r}" for r in range(Q)]
mem = " → ".join(f"(l{r} : ℝ) / SC ≤ g{r} → g{r} ≤ (u{r} : ℝ) / SC" for r in range(Q))
HV = " ".join(f"h{r}1 h{r}2" for r in range(Q))
TBLB = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ}"
HYPS = "(hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)"
TARGS = "top bk tD bD pb R C"
LEAFLEN = {0: 3, 1: 3 + 2 * Q + 1 + NP, 2: 3}
SLEN_FULL = 3 + 2 * Q + 1
def rsum(xs): return " + ".join(xs)
def term_g(i, j): return rsum(V[i:j])
def nsum(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e
def ssum(kind, i, j): return " + ".join(f"{kind}{r}" for r in range(i, j))
def nadd(xs):
    e = xs[0]
    for x in xs[1:]: e = f"(Nat.add {e} {x})"
    return e
def br(c, t, e, mot="ℕ"): return f"Bool.rec (motive := fun _ => {mot}) ({e}) ({t}) ({c})"
def args_with(ax, which, val):
    cs = COORDS.split(); cs[2 * ax + (1 if which == "u" else 0)] = val; return " ".join(cs)
def bit(t): return f"(bitOf T {t})"

NIL = '[] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []'
def checker(NAME, SA, aN, bN, cN, ORDER, JCQ):
    C = cN * SC * U
    full_nat = f"{U} * ({rsum([f'{bN[r]} * l{r}' for r in range(Q)])}) + {SC} * ({rsum([f'{aN[t]} * lb3 top bk ({ssum(chr(108), i, j)}) ({ssum(chr(117), i, j)})' for t, (i, j) in enumerate(PAIRS)])})"
    lin = "(Nat.add " * (Q - 1) + f"(Nat.mul {bN[0]} l0)" + "".join(f" (Nat.mul {bN[r]} l{r}))" for r in range(1, Q))
    body = f"Nat.ble {C} s{NP}"
    for k in range(NP - 1, -1, -1):
        t = ORDER[k]; i, j = PAIRS[t]
        term = f"Nat.mul {aN[t] * SC} (lb3 top bk {nsum('l', i, j)} {nsum('u', i, j)})"
        body = f"let s{k + 1} := Nat.add s{k} ({term})\n  " + (f"ee {C} s{k + 1} (\n  {body})" if k < NP - 1 else body)
    LEAF = f"let s0 := Nat.mul {lin} {U}\n  ee {C} s0 (\n  {body})"
    SPLITS = []
    for ax in range(Q):
        SPLITS.append(f"/-- a split on gap {ax}: the lower half (`u{ax} := q`) from `pos + 4`, then the upper half from where it ends -/\n"
                      f"def split{ax} (ih : WF) (pos {COORDS} : ℕ) : ℕ :=\n"
                      f"  forceR (Nat.shiftRight (Nat.add l{ax} u{ax}) 1) fun q =>\n  let p := ih (Nat.add pos 4) {args_with(ax, 'u', 'q')}\n  "
                      + br("Nat.beq p 0", "0", f"ih p {args_with(ax, 'l', 'q')}") + "\n")
    SPLITAX = f"split{Q-1} ih pos {COORDS}"
    for ax in range(Q - 2, -1, -1):
        SPLITAX = br(f"Nat.beq ax {ax}", f"split{ax} ih pos {COORDS}", SPLITAX)
    MOT = " → ".join(["ℕ"] * (2 * Q + 2))
    SLEAF = ("\n  ".join(f"forceB (dec (Nat.land (Nat.shiftRight w {3 + 2 * r}) 3) l{r} u{r}) fun q{r} =>" for r in range(Q))
             + f"\n  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w {3 + 2 * Q + 1}) {(1 << NP) - 1}) {(1 << NP) - 1} (Nat.beq (Nat.land (Nat.shiftRight w {3 + 2 * Q}) 1) 1)) fun T =>\n  ctest top bk tD bD (pt3 pb) R {COORDS} {QV} T")
    KIND = "(Nat.land (Nat.shiftRight w 1) 3)"
    CLEAF = ("forceB (Nat.land (Nat.shiftRight w 3) 15) fun k =>\n  "
             + "\n  ".join(f"forceB (cdec C k {r} l{r} u{r}) fun q{r} =>" for r in range(Q))
             + f"\n  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 8) {(1 << NP) - 1}) {(1 << NP) - 1} (Nat.beq (Nat.land (Nat.shiftRight w 7) 1) 1)) fun T =>\n  ctest top bk tD bD (pt3 pb) R {COORDS} {QV} T")
    CLEAF_FULL = 8; CLEAF_LEN = 8 + NP
    LEAFB = br(f"Nat.ble (Nat.add u{Q-1} 1) l0", f"Nat.add pos {LEAFLEN[0]}",
               br(f"Nat.beq {KIND} 0",
                  br(f"leafOK top bk {COORDS}", f"Nat.add pos {LEAFLEN[0]}", "0"),
                  br(f"Nat.beq {KIND} 1",
                     br(f"sleaf {TARGS} w {COORDS}", br(f"Nat.beq (Nat.land (Nat.shiftRight w {3 + 2 * Q}) 1) 1", f"Nat.add pos {SLEN_FULL}", f"Nat.add pos {LEAFLEN[1]}"), "0"),
                     br(f"Nat.beq {KIND} 2",
                        br(f"inBas bas {COORDS}", f"Nat.add pos {LEAFLEN[2]}", "0"),
                        br(f"cleaf {TARGS} w {COORDS}", br("Nat.beq (Nat.land (Nat.shiftRight w 7) 1) 1", f"Nat.add pos {CLEAF_FULL}", f"Nat.add pos {CLEAF_LEN}"), "0")))))
    BOXF = " ".join(f"(l{r} u{r} : ℕ)" for r in range(Q))
    _fl = []
    for r in range(Q): _fl += [f"hbl{r}", f"hbu{r}"]
    INPAT = _fl[0]
    for c in _fl[1:]: INPAT = f"⟨{INPAT}, {c}⟩"
    INB = " && ".join(f"Nat.ble b.l{r} l{r} && Nat.ble u{r} b.u{r}" for r in range(Q))
    from gen7cn import ctest_defs, ctest_proofs
    CTDEFS = ctest_defs(NAME, aN, bN, cN)
    out = f"""
noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.{NAME}

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD

def SA : ℕ := {SA}
def cN : ℕ := {cN}

/-- the weighted functional on the gaps, in real form -/
def G ({' '.join(V)} : ℝ) : ℝ :=
  {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
    + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb3_t` (U = 10¹⁰; three-piece pyramid reads), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) ({COORDS} : ℕ) : Bool :=
  {LEAF}

/-- bit `t` of `T` -/
def bitOf (T t : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight T t) 1) 1

{CTDEFS}
/-- the expansion point of a gap from its 2-bit mode: the lower end, the upper end or the midpoint, each rounded to a
multiple of `2^{JCQ}`, else of `16`, when that stays in `[l, u]` (any value is sound: the test checks `l ≤ q ≤ u`) -/
def dec (m l u : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (Nat.shiftRight (Nat.add l u) 1) fun c =>
        forceR (Nat.shiftLeft (Nat.shiftRight c {JCQ}) {JCQ}) fun cc =>
          Bool.rec (motive := fun _ => ℕ)
            (forceR (Nat.shiftLeft (Nat.shiftRight c 4) 4) fun c2 => Bool.rec (motive := fun _ => ℕ) c c2 (Nat.ble l c2))
            cc (Nat.ble l cc))
      (forceR (Nat.shiftLeft (Nat.shiftRight u {JCQ}) {JCQ}) fun mm =>
        Bool.rec (motive := fun _ => ℕ)
          (forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun m2 => Bool.rec (motive := fun _ => ℕ) u m2 (Nat.ble l m2))
          mm (Nat.ble l mm))
      (Nat.beq m 1))
    (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l {(1 << JCQ) - 1}) {JCQ}) {JCQ}) fun mm =>
      Bool.rec (motive := fun _ => ℕ)
        (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun m2 => Bool.rec (motive := fun _ => ℕ) l m2 (Nat.ble m2 u))
        mm (Nat.ble mm u))
    (Nat.beq m 0)

/-- a slope leaf: modes (bits 3..{2 + 2 * Q}), then a flag (bit {3 + 2 * Q}: every term expanded) or the expansion set
(bits {4 + 2 * Q}..) of the walk word `w` -/
def sleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) ({COORDS} : ℕ) : Bool :=
  {SLEAF}

/-- the expansion point of a gap at a centre leaf: coordinate `r` of the centre `k` (20-bit fields of `C`), clamped to
`[l, u]` rounded inward to multiples of `16` when that is nonempty, else to `[l, u]` -/
def cdec (C k r l u : ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight C (Nat.mul 20 (Nat.add (Nat.mul 6 k) r))) 1048575) fun c =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun la =>
  forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun ua =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c u (Nat.ble u c)) l (Nat.ble c l))
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c ua (Nat.ble ua c)) la (Nat.ble c la))
    (Nat.ble la ua)

/-- a centre leaf: the centre index (bits 3..6), then a flag (bit 7: every term expanded) or the expansion set
(bits 8..) of the walk word `w` -/
def cleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) ({COORDS} : ℕ) : Bool :=
  {CLEAF}

/-- a basin box -/
structure Bx where
  {BOXF}

/-- the box lies inside one of the basin boxes -/
def inBas (bas : List Bx) ({COORDS} : ℕ) : Bool :=
  bas.any fun b => {INB}

/-- the type of a walk continuation: position and the coordinates to the end position (`0` = failure) -/
abbrev WF : Type := {MOT}

{chr(10).join(SPLITS)}
/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax {COORDS} : ℕ) : ℕ :=
  {SPLITAX}

/-- a leaf (bit 0 clear; bits 1..2 the kind: zero-order, slope with its payload, basin): in the reflected half-space, or
the leaf's own test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (pos w {COORDS} : ℕ) : ℕ :=
  {LEAFB}

/-- the bisection walk (`Nat.rec` on the fuel): the node word is `bits >>> pos` (bit 0 split, bits 1..3 axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun {' '.join(['_'] * (2 * Q + 1))} => 0)
    (fun _ ih pos {COORDS} =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep {TARGS} bas pos w {COORDS}) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) {COORDS}) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered ({COORDS} : ℕ) : Prop :=
  ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} ∨ g{Q-1} < g0

theorem ee_or {{C s : ℕ}} {{rest : Bool}} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) ({COORDS} : ℕ) (h : leafOK top bk {COORDS} = true) :
    {C} ≤ {full_nat} := by
  unfold leafOK at h
  dsimp only at h
{chr(10).join("  rcases ee_or h with h | h" + chr(10) + "  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega" for _ in range(NP))}
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 8000000 in
theorem leaf_sound {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) ({COORDS} : ℕ) (h : leafOK top bk {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  have hq0 := leafOK_le top bk {COORDS} h
"""
    for t, (i, j) in enumerate(PAIRS):
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  have w{t} := lb3_sound hlb ({ssum('l', i, j)}) ({ssum('u', i, j)}) ({term_g(i, j)}) "
                f"(by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n")
    out += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := {' + '.join(f'{bN[r]} * ((l{r} : ℝ) / SC)' for r in range(Q))} with hL
  set Wt : ℝ := {' + '.join(f"{aN[t]} * ((lb3 top bk ({ssum('l', i, j)}) ({ssum('u', i, j)}) : ℝ) / 10000000000)" for t, (i, j) in enumerate(PAIRS))} with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * ({' + '.join(f'{bN[r]} * (l{r} : ℝ)' for r in range(Q))}) + {SC} * ({' + '.join(f"{aN[t]} * (lb3 top bk ({ssum('l', i, j)}) ({ssum('u', i, j)}) : ℝ)" for t, (i, j) in enumerate(PAIRS))}) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = {C} := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))} := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', {', '.join(f'mul_le_mul_of_nonneg_left h{r}1 (by positivity : (0:ℝ) ≤ {bN[r]})' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left w{t} (by positivity : (0:ℝ) ≤ {aN[t]})' for t in range(NP))}]
"""
    # ---------------- convex basins ----------------
    out += ctest_proofs(NAME, aN, bN, cN)
    # ---------------- walk ----------------
    for ax in range(Q):
        out += f"""
/-- a box split on gap {ax} at `q` is covered when both halves are -/
theorem covered_split{ax} {{{COORDS} : ℕ}} (q : ℕ) (hA : Covered {args_with(ax, 'u', 'q')}) (hB : Covered {args_with(ax, 'l', 'q')}) :
    Covered {COORDS} := by
  intro {' '.join(V)} {HV}
  rcases le_total g{ax} ((q : ℝ) / SC) with hq | hq
  · exact hA {' '.join(V)} {' '.join(f'h{r}1 ' + ('hq' if r == ax else f'h{r}2') for r in range(Q))}
  · exact hB {' '.join(V)} {' '.join(('hq ' if r == ax else f'h{r}1 ') + f'h{r}2' for r in range(Q))}
"""
    out += f"""
/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos {COORDS} : ℕ, f pos {COORDS} ≠ 0 → Covered {COORDS}
"""
    for ax in range(Q):
        q = f"(Nat.shiftRight (Nat.add l{ax} u{ax}) 1)"
        out += f"""
theorem split{ax}_sound {{ih : WF}} (hih : WalkOK ih) (pos {COORDS} : ℕ) (h : split{ax} ih pos {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold split{ax} at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) {args_with(ax, 'u', q)}) 0
  · have h' : ih (ih (Nat.add pos 4) {args_with(ax, 'u', q)}) {args_with(ax, 'l', q)} ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) {args_with(ax, 'u', q)} (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split{ax} _ hA (hih _ {args_with(ax, 'l', q)} h')
  · exact absurd (by simp only [hp]) h
"""
    out += f"""
theorem splitAx_sound {{ih : WF}} (hih : WalkOK ih) (pos ax {COORDS} : ℕ) (h : splitAx ih pos ax {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold splitAx at h
"""
    def ax_proof(ax, ind):
        if ax == Q - 1:
            return [f"{ind}exact split{Q-1}_sound hih pos {COORDS} h"]
        o = [f"{ind}cases ha{ax} : Nat.beq ax {ax}", f"{ind}· rw [ha{ax}] at h"]
        o += ax_proof(ax + 1, ind + "  ")
        o += [f"{ind}· rw [ha{ax}] at h; exact split{ax}_sound hih pos {COORDS} h"]
        return o
    out += "\n".join(ax_proof(0, "  ")) + "\n"
    out += f"""
theorem sleaf_sound {TBLB} {HYPS} (w {COORDS} : ℕ) (h : sleaf {TARGS} w {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  unfold sleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR {' '.join(['_'] * (2 * Q + Q + 1))} h

theorem cleaf_sound {TBLB} {HYPS} (w {COORDS} : ℕ) (h : cleaf {TARGS} w {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  unfold cleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR {' '.join(['_'] * (2 * Q + Q + 1))} h

/-- the basin boxes are covered -/
def BasOK (bas : List Bx) : Prop := ∀ b ∈ bas, Covered {' '.join(f'b.l{r} b.u{r}' for r in range(Q))}

theorem inBas_sound {{bas : List Bx}} (hbas : BasOK bas) ({COORDS} : ℕ) (h : inBas bas {COORDS} = true) :
    Covered {COORDS} := by
  unfold inBas at h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, hin⟩ := h
  simp only [Bool.and_eq_true, Nat.ble_eq] at hin
  obtain {INPAT} := hin
  intro {' '.join(V)} {HV}
  exact hbas b hb {' '.join(V)} {' '.join(f'(le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl{r}) (by norm_num [SC])) h{r}1) (le_trans h{r}2 (div_le_div_of_nonneg_right (by exact_mod_cast hbu{r}) (by norm_num [SC])))' for r in range(Q))}

theorem leafStep_sound {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (pos w {COORDS} : ℕ)
    (h : leafStep {TARGS} bas pos w {COORDS} ≠ 0) : Covered {COORDS} := by
  unfold leafStep at h
  cases hs : Nat.ble (Nat.add u{Q-1} 1) l0
  · rw [hs] at h
    cases hk0 : Nat.beq {KIND} 0
    · rw [hk0] at h
      cases hk1 : Nat.beq {KIND} 1
      · rw [hk1] at h
        cases hk2 : Nat.beq {KIND} 2
        · rw [hk2] at h
          cases hl : cleaf {TARGS} w {COORDS}
          · rw [hl] at h; exact absurd rfl h
          · intro {' '.join(V)} {HV}
            exact Or.inl (cleaf_sound hlb hD hpt hR w {COORDS} hl {' '.join(V)} {HV})
        · rw [hk2] at h
          cases hl : inBas bas {COORDS}
          · rw [hl] at h; exact absurd rfl h
          · exact inBas_sound hbas {COORDS} hl
      · rw [hk1] at h
        cases hl : sleaf {TARGS} w {COORDS}
        · rw [hl] at h; exact absurd rfl h
        · intro {' '.join(V)} {HV}
          exact Or.inl (sleaf_sound hlb hD hpt hR w {COORDS} hl {' '.join(V)} {HV})
    · rw [hk0] at h
      cases hl : leafOK top bk {COORDS}
      · rw [hl] at h; exact absurd rfl h
      · intro {' '.join(V)} {HV}
        exact Or.inl (leaf_sound hlb {COORDS} hl {' '.join(V)} {HV})
  · intro {' '.join(V)} {HV}
    right
    have hsk : u{Q-1} < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u{Q-1} : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (bits : ℕ) :
    ∀ fuel, WalkOK (walk {TARGS} bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos {COORDS} h; exact absurd rfl h
  | succ fuel ih =>
    intro pos {COORDS} h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep {TARGS} bas pos (Nat.shiftRight bits pos) {COORDS})
        (splitAx (walk {TARGS} bas bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) {COORDS})
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR hbas pos _ {COORDS} h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ {COORDS} h'

theorem covered_of_walk {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (bits fuel {COORDS} e : ℕ)
    (h : walk {TARGS} bas bits fuel 1 {COORDS} = e) (he : e ≠ 0) : Covered {COORDS} :=
  walk_sound hlb hD hpt hR hbas bits fuel 1 {COORDS} (h ▸ he)

"""
    # ---------------- cover and of_check (from gen_cover7.py) ----------------
    tmpname = NAME + "Cov"
    subprocess.run(["python3", os.path.join(HERE, "gen_cover7.py"), str(Q), str(SA), ",".join(map(str, aN)), ",".join(map(str, bN)),
                    str(cN), tmpname, ",".join(map(str, ORDER))], check=True, env=dict(os.environ, PARTS="inst"), capture_output=True)
    cv = open(os.path.join(HERE, f"covpart_{tmpname}.lean"), encoding="utf-8").read()
    a = cv.index("/-- per-gap one-dimensional cover"); b = cv.index(f"end Zeta23Ext.Bridge.ThreePoint.{tmpname}")
    out += "\n" + cv[a:b] + f"end Zeta23Ext.Bridge.ThreePoint.{NAME}\n\nend\n"
    return out
