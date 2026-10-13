#!/usr/bin/env python3
"""(AM copy of bench/seven/gen_cover7.py: namespace AMW.Cert, window bound 1/4, output next to this file) Checker for a weighted n-point certificate on the PYRAMID oracle (new file; the BST checker of gen_checkerN_force.py
is untouched).  Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Usage: gen_checker_pyr.py Q SA aN_list bN_list cN NAME ORDER
  ORDER: comma list of the term indices (pairs i<j in order) in the leaf's early-exit order.
Writes checker_<NAME>.lean:
  * the integer cell pipeline (`CellN`, ZDEFS/ZLEMMAS of checkerZ.lean, `cellN_soundZ'`, `cellN_soundWZ`);
  * the generic pyramid oracle `Pyr.lb`, its verification `Pyr.topOk`/`Pyr.blockOk` and `Pyr.lb_sound`
    (text of bench/pyr/PyrCheck.lean);
  * the instance: functional `G`, early-exit leaf test `leafOK`, the `Nat.rec` walk over ten coordinate arguments,
    `Covered`, the split lemmas, the per-gap cover check (clear segments by the cell bound itself) and `of_check`.
Coordinates are at scale SC = 2^15, oracle values at U = 10^10, cell values at SW = 10^13."""
import sys, os
HERE = os.path.expanduser("~/work/riemann-submission")
Q = int(sys.argv[1]); SA = int(sys.argv[2])
aN = [int(x) for x in sys.argv[3].split(",")]; bN = [int(x) for x in sys.argv[4].split(",")]
cN = int(sys.argv[5]); NAME = sys.argv[6]; ORDER = [int(x) for x in sys.argv[7].split(",")]
pass
n = Q + 1
pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
assert len(aN) == len(pairs) and len(bN) == Q and sorted(ORDER) == list(range(len(pairs)))
SC = 1 << 15; U = 10**10
C = cN * SC * U
V = [f"g{r}" for r in range(Q)]
CO = [f"l{r} u{r}" for r in range(Q)]; COORDS = " ".join(CO)
def rsum(xs): return " + ".join(xs)
def nsum(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e
def term_g(i, j): return rsum(V[i:j])

# ---------------- integer cell pipeline (from checkerZ.lean) ----------------
z = open(os.path.join(HERE, "checkerZ.lean"), encoding="utf-8").read()
ZD = z[z.index("-- ZDEFS-BEGIN"):z.index("-- ZDEFS-END") + len("-- ZDEFS-END")]
ZL = z[z.index("-- ZLEMMAS-BEGIN"):z.index("-- ZLEMMAS-END") + len("-- ZLEMMAS-END")]
CELLS = f"""
/-! ###### integer cell pipeline for the pyramid certificate `{NAME}` ###### -/

section {NAME}Cells

namespace AMW.Cert

structure CellN where
  (key : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000

/-- a cell's endpoints are packed into one key `LN * KB + UN` (every coordinate is below `KB`) -/
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

{ZD}

end AMW.Cert

end {NAME}Cells

noncomputable section

open Real

namespace AMW.Cert

{ZL}

end AMW.Cert

end
"""
# ---------------- generic pyramid oracle ----------------
g = open(os.path.join(HERE, "bench", "pyr", "PyrCheck.lean"), encoding="utf-8").read()
GENERIC = g[g.index("/-! ###### pyramid lower-bound oracle"):]

# ---------------- instance ----------------
lin = "(Nat.add " * (Q - 1) + f"(Nat.mul {bN[0]} l0)" + "".join(f" (Nat.mul {bN[r]} l{r}))" for r in range(1, Q))
# leaf test, early exit after each term (in ORDER)
body = f"Nat.ble {C} s{len(pairs)}"
for k in range(len(pairs) - 1, -1, -1):
    t = ORDER[k]; i, j = pairs[t]
    term = f"Nat.mul {aN[t] * SC} (lb top bk {nsum('l', i, j)} {nsum('u', i, j)})"
    body = f"let s{k + 1} := Nat.add s{k} ({term})\n  " + (f"ee {C} s{k + 1} (\n  {body})" if k < len(pairs) - 1 else body)
LEAF = f"let s0 := Nat.mul {lin} {U}\n  ee {C} s0 (\n  {body})"
full_nat = f"{U} * ({rsum([f'{bN[r]} * l{r}' for r in range(Q)])}) + {SC} * ({rsum([f'{aN[t]} * lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])})' for t, (i, j) in enumerate(pairs)])})"
def args_with(ax, which, val):
    cs = COORDS.split(); cs[2 * ax + (1 if which == "u" else 0)] = val; return " ".join(cs)
def br(c, t, e, mot="ℕ"): return f"Bool.rec (motive := fun _ => {mot}) ({e}) ({t}) ({c})"
def split_def(ax):
    return (f"/-- a split on gap {ax}: the lower half (`u{ax} := q`) from `pos + 4`, then the upper half from where it ends -/\n"
            f"def split{ax} (ih : WF) (pos {COORDS} : ℕ) : ℕ :=\n"
            f"  forceR (Nat.shiftRight (Nat.add l{ax} u{ax}) 1) fun q =>\n  let p := ih (Nat.add pos 4) {args_with(ax, 'u', 'q')}\n  "
            + br("Nat.beq p 0", "0", f"ih p {args_with(ax, 'l', 'q')}") + "\n")
SPLITS = "\n".join(split_def(ax) for ax in range(Q))
SPLITAX = f"split{Q-1} ih pos {COORDS}"
for ax in range(Q - 2, -1, -1):
    SPLITAX = br(f"Nat.beq ax {ax}", f"split{ax} ih pos {COORDS}", SPLITAX)
LEAFB = br(f"Nat.ble (Nat.add u{Q-1} 1) l0", "Nat.add pos 1", br(f"leafOK top bk {COORDS}", "Nat.add pos 1", "0"))
MOT = " → ".join(["ℕ"] * (2 * Q + 2))
mem = " → ".join(f"(l{r} : ℝ) / SC ≤ g{r} → g{r} ≤ (u{r} : ℝ) / SC" for r in range(Q))

INST = f"""
/-! ###### the {n}-point weighted certificate `{NAME}` on the pyramid oracle: leaf test, walk, cover ###### -/

noncomputable section

namespace AMW.Cert.{NAME}

open AMW.Cert AMW.Cert.Pyr

def SA : ℕ := {SA}
def cN : ℕ := {cN}

/-- the weighted functional on the gaps, in real form -/
def G ({' '.join(V)} : ℝ) : ℝ :=
  {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
    + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))}

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) ({COORDS} : ℕ) : Bool :=
  {LEAF}

/-- the type of a walk continuation: position and the ten coordinates to the end position (`0` = failure) -/
abbrev WF : Type := {MOT}

{SPLITS}
/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax {COORDS} : ℕ) : ℕ :=
  {SPLITAX}

/-- a leaf: in the reflected half-space, or the leaf test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (pos {COORDS} : ℕ) : ℕ :=
  {LEAFB}

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis); the position after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun {' '.join(['_'] * (2 * Q + 1))} => 0)
    (fun _ ih pos {COORDS} =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos {COORDS}) (splitAx ih pos (Nat.shiftRight w 1) {COORDS}) (Nat.beq (Nat.land w 1) 1))
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
{chr(10).join("  rcases ee_or h with h | h" + chr(10) + "  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega" for _ in range(len(pairs)))}
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 4000000 in
theorem leaf_sound {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) ({COORDS} : ℕ) (h : leafOK top bk {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {' '.join(f'h{r}1 h{r}2' for r in range(Q))}
  have hq0 := leafOK_le top bk {COORDS} h
"""
for t, (i, j) in enumerate(pairs):
    hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
    INST += (f"  have w{t} := hlb ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) ({term_g(i, j)}) "
             f"(by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n")
INST += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU : (0:ℝ) < 10000000000 := by norm_num
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := {' + '.join(f'{bN[r]} * ((l{r} : ℝ) / SC)' for r in range(Q))} with hL
  set Wt : ℝ := {' + '.join(f"{aN[t]} * ((lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) : ℝ) / 10000000000)" for t, (i, j) in enumerate(pairs))} with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * ({' + '.join(f'{bN[r]} * (l{r} : ℝ)' for r in range(Q))}) + {SC} * ({' + '.join(f"{aN[t]} * (lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) : ℝ)" for t, (i, j) in enumerate(pairs))}) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = {C} := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))} := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', {', '.join(f'mul_le_mul_of_nonneg_left h{r}1 (by positivity : (0:ℝ) ≤ {bN[r]})' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left w{t} (by positivity : (0:ℝ) ≤ {aN[t]})' for t in range(len(pairs)))}]

"""
for ax in range(Q):
    other = ", ".join(f"h{r}1, h{r}2" for r in range(Q) if r != ax)
    INST += f"""
/-- a box split on gap {ax} at `q` is covered when both halves are -/
theorem covered_split{ax} {{{COORDS} : ℕ}} (q : ℕ) (hA : Covered {args_with(ax, 'u', 'q')}) (hB : Covered {args_with(ax, 'l', 'q')}) :
    Covered {COORDS} := by
  intro {' '.join(V)} {' '.join(f'h{r}1 h{r}2' for r in range(Q))}
  rcases le_total g{ax} ((q : ℝ) / SC) with hq | hq
  · exact hA {' '.join(V)} {' '.join(f'h{r}1 ' + ('hq' if r == ax else f'h{r}2') for r in range(Q))}
  · exact hB {' '.join(V)} {' '.join(('hq ' if r == ax else f'h{r}1 ') + f'h{r}2' for r in range(Q))}
"""
INST += f"""
/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos {COORDS} : ℕ, f pos {COORDS} ≠ 0 → Covered {COORDS}
"""
for ax in range(Q):
    q = f"(Nat.shiftRight (Nat.add l{ax} u{ax}) 1)"
    INST += f"""
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
INST += f"""
theorem splitAx_sound {{ih : WF}} (hih : WalkOK ih) (pos ax {COORDS} : ℕ) (h : splitAx ih pos ax {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold splitAx at h
"""
def ax_proof(ax, ind):
    if ax == Q - 1:
        return [f"{ind}exact split{Q-1}_sound hih pos {COORDS} h"]
    out = [f"{ind}cases ha{ax} : Nat.beq ax {ax}",
           f"{ind}· rw [ha{ax}] at h"]
    out += ax_proof(ax + 1, ind + "  ")
    out += [f"{ind}· rw [ha{ax}] at h; exact split{ax}_sound hih pos {COORDS} h"]
    return out
INST += "\n".join(ax_proof(0, "  ")) + "\n"
INST += f"""
theorem leafStep_sound {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) (pos {COORDS} : ℕ) (h : leafStep top bk pos {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold leafStep at h
  intro {' '.join(V)} {' '.join(f'h{r}1 h{r}2' for r in range(Q))}
  cases hs : Nat.ble (Nat.add u{Q-1} 1) l0
  · rw [hs] at h
    cases hl : leafOK top bk {COORDS}
    · rw [hl] at h; exact absurd rfl h
    · exact Or.inl (leaf_sound hlb {COORDS} hl {' '.join(V)} {' '.join(f'h{r}1 h{r}2' for r in range(Q))})
  · right
    have hsk : u{Q-1} < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u{Q-1} : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) (bits : ℕ) : ∀ fuel, WalkOK (walk top bk bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos {COORDS} h; exact absurd rfl h
  | succ fuel ih =>
    intro pos {COORDS} h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos {COORDS})
        (splitAx (walk top bk bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) {COORDS})
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb pos {COORDS} h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ {COORDS} h'
"""
INST += f"""
theorem covered_of_walk {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) (bits fuel {COORDS} e : ℕ)
    (h : walk top bk bits fuel 1 {COORDS} = e) (he : e ≠ 0) : Covered {COORDS} :=
  walk_sound hlb bits fuel 1 {COORDS} (h ▸ he)

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear segment's own integer
cell bound must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WZ ≥ cN * SW` -/
def coverCheck (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b) && decide (b < KB)
        && (!cl || Nat.ble (cN * SW) (aAdjN * CellN.WZ ⟨a * KB + b, 0⟩))
        && coverCheck aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

theorem cover_sound (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        rw [Nat.ble_eq] at hcl
        have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
          simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
        have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
          simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
        have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSA : (0:ℝ) < SA := by norm_num [SA]
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        rw [div_le_iff₀ hSA]
        have hm2 : (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
        rw [e]
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdjN : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {{cover : List (ℕ × ℕ × Bool)}} {{s : ℕ × ℕ × Bool}} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check ({' '.join(f'cover{r}' for r in range(Q))} : List (ℕ × ℕ × Bool)) ({' '.join(f'S{r}' for r in range(Q))} : ℕ)
    {' '.join(f'(hS{r} : cN * SC ≤ {bN[r]} * S{r})' for r in range(Q))}
    {' '.join(f'(hcov{r} : coverCheck {aN[pairs.index((r, r+1))]} (SC / 2) S{r} cover{r} = true)' for r in range(Q))}
    (hwin : cN * 4 ≤ {min(aN[pairs.index((r, r+1))] for r in range(Q))})
    (hrun : ∀ {' '.join(f'i{r}' for r in range(Q))}, {' → '.join(f'i{r} < (badOf cover{r}).length' for r in range(Q))} →
      Covered {' '.join(f'((badOf cover{r}).getD i{r} (0, 0)).1 ((badOf cover{r}).getD i{r} (0, 0)).2' for r in range(Q))}) :
    ∀ {' '.join(V)} : ℝ, {' → '.join(f'0 ≤ {V[r]}' for r in range(Q))} → (cN : ℝ) / SA ≤ G {' '.join(V)} ∨ g{Q-1} < g0 := by
  intro {' '.join(V)} {' '.join(f'hg{r}' for r in range(Q))}
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))} with hLin
  set Wt : ℝ := {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))} with hWt
  have hG : G {' '.join(V)} = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
"""
INST += "".join(f"  have hb{r}0 : (0:ℝ) ≤ ({bN[r]} / (SA:ℝ)) * {V[r]} := mul_nonneg (by positivity) hg{r}\n" for r in range(Q))
INST += "".join(f"  have ha{t}0 : (0:ℝ) ≤ ({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)}) := mul_nonneg (by positivity) (hw _)\n" for t, (i, j) in enumerate(pairs))
INST += f"  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [{', '.join(f'hb{r}0' for r in range(Q))}]\n"
INST += f"  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [{', '.join(f'ha{t}0' for t in range(len(pairs)))}]\n"
INST += "".join(f"  have hbL{r} : ({bN[r]} / (SA:ℝ)) * {V[r]} ≤ Lin := by rw [hLin]; linarith [{', '.join(f'hb{k}0' for k in range(Q) if k != r)}]\n" for r in range(Q))
INST += "".join(f"  have haW{t} : ({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)}) ≤ Wt := by rw [hWt]; linarith [{', '.join(f'ha{k}0' for k in range(len(pairs)) if k != t)}]\n" for t, (i, j) in enumerate(pairs))
for r in range(Q):
    adj = aN[pairs.index((r, r + 1))]; tadj = pairs.index((r, r + 1))
    INST += f"""  -- gap {r}: beyond the cutoff the pressure alone pays
  by_cases hcut{r} : (S{r} : ℝ) / SC ≤ {V[r]}
  · have h1 : (cN : ℝ) / SA ≤ ({bN[r]} / (SA:ℝ)) * {V[r]} := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS{r}; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : ({bN[r]} / (SA:ℝ)) * {V[r]} * SA = {bN[r]} * {V[r]} := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ {bN[r]} * S{r} / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = {bN[r]} * ((S{r} : ℝ) / SC) := by ring
        _ ≤ {bN[r]} * {V[r]} := mul_le_mul_of_nonneg_left hcut{r} (by norm_num)
    left; rw [hG]; linarith [h1, hbL{r}, hWt0]
  push_neg at hcut{r}
  rcases le_total {V[r]} ((SC / 2 : ℕ) / (SC : ℝ)) with hwin{r} | hwin{r}
  · have hw19 := wfun_window {V[r]} hg{r} (by rw [hhalf] at hwin{r}; exact hwin{r})
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ ({adj} / (SA:ℝ)) * wfun {V[r]} := by
      rw [div_le_iff₀ hSA]
      have e : ({adj} / (SA:ℝ)) * wfun {V[r]} * SA = {adj} * wfun {V[r]} := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ {adj})
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW{tadj}, hLin0]
  rcases cover_sound _ cover{r} (SC / 2) S{r} hcov{r} {V[r]} hwin{r} hcut{r} with hclear{r} | ⟨s{r}, hs{r}, he{r}, hb{r}1, hb{r}2⟩
  · left; rw [hG]; linarith [hclear{r}, haW{tadj}, hLin0]
  obtain ⟨i{r}, hi{r}, hsi{r}⟩ := List.mem_iff_getElem.mp (badOf_mem hs{r} he{r})
  have hb{r}1' : (((badOf cover{r}).getD i{r} (0, 0)).1 : ℝ) / SC ≤ {V[r]} := by
    rw [List.getD_eq_getElem _ _ hi{r}, hsi{r}]; exact hb{r}1
  have hb{r}2' : {V[r]} ≤ (((badOf cover{r}).getD i{r} (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi{r}, hsi{r}]; exact hb{r}2
"""
INST += f"""  exact hrun {' '.join(f'i{r}' for r in range(Q))} {' '.join(f'hi{r}' for r in range(Q))} {' '.join(V)} {' '.join(f"hb{r}1' hb{r}2'" for r in range(Q))}

end AMW.Cert.{NAME}

end
"""
text = INST if os.environ.get("PARTS") == "inst" else CELLS + "\n" + GENERIC + "\n" + INST
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"covpart_{NAME}.lean"), "w", encoding="utf-8").write(text)
print(f"wrote checker_{NAME}.lean ({len(text.encode())} bytes)")
