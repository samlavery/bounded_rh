import AMW.CMin

/-! ###### the minorant leaf of the AM certificate (stage G): one pair term with its reads forced once, and the
decoder of a term's code in the walk word

A term of a minorant leaf is the convex combination (MinCore `mwc`/`mw1`/`mw2`, kind `κ`, weight `lam`) of the
zero-order constant and the extended tangents at the grid points `gpt L U j1`, `gpt L U j2` (MinCore `mterm_ok`).  Here
its point reads are forced once and passed through the two-point restriction `fpick` of the point table, and the
constant's pyramid read is made only when its weight is positive. ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the point function `X1` at `p1`, `X2` at `p2`, `0` elsewhere -/
def fpick (p1 X1 p2 X2 : ℕ) (x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 X2 (Nat.beq x p2)) X1 (Nat.beq x p1)

theorem ptf_zero (x : ℕ) : (lo32 0 : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 0) ((x : ℝ) / SC) := by
  rw [lo32_zero, hi32_zero]
  exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩

/-- a restriction of a sound point function, each value read or zero, is sound -/
theorem fpick_ptf {f : ℕ → ℕ} (hpt : PTF f) {p1 X1 p2 X2 : ℕ} (h1 : X1 = 0 ∨ X1 = f p1) (h2 : X2 = 0 ∨ X2 = f p2) :
    PTF (fpick p1 X1 p2 X2) := by
  intro x
  unfold fpick
  cases hb1 : Nat.beq x p1
  · cases hb2 : Nat.beq x p2
    · exact ptf_zero x
    · have hx : x = p2 := by simpa using hb2
      subst hx
      rcases h2 with h | h
      · rw [h]; exact ptf_zero x
      · rw [h]; exact hpt x
  · have hx : x = p1 := by simpa using hb1
    subst hx
    rcases h1 with h | h
    · rw [h]; exact ptf_zero x
    · rw [h]; exact hpt x

/-- the read `X` of `pt3 pb p` when `0 < l`, else `0` -/
def rdIf (pb : ℕ → ℕ) (l p : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 (pt3 pb p) (Nat.blt 0 l)

theorem rdIf_cases (pb : ℕ → ℕ) (l p : ℕ) : rdIf pb l p = 0 ∨ rdIf pb l p = pt3 pb p := by
  unfold rdIf; cases Nat.blt 0 l
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- one term of a minorant leaf on the range `[L, U]`: the side conditions, then `k val cp cn sl wt` with its value
(units `1/(1024 U)`), its charges, its slope claim and its slope weight -/
def mtrm (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))
    (L U κ lam j1 j2 : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  forceB (gpt L U j1) fun p1 =>
  forceB (gpt L U j2) fun p2 =>
  forceB (mwc κ lam) fun c =>
  forceB (mw1 κ lam) fun l1 =>
  forceB (mw2 κ lam) fun l2 =>
  forceB (rdIf pb l1 p1) fun X1 =>
  forceB (rdIf pb l2 p2) fun X2 =>
  forceB (Bool.rec (motive := fun _ => ℕ) 0 (lb top bk L U) (Nat.blt 0 c)) fun B =>
  Nat.ble lam 1024 && mok R tD bD (fpick p1 X1 p2 X2) L U l1 l2 p1 p2 &&
    forceB (Nat.add (Nat.mul c B) (Nat.add (Nat.mul l1 (lo32 (fpick p1 X1 p2 X2 p1)))
        (Nat.mul l2 (lo32 (fpick p1 X1 p2 X2 p2))))) fun val =>
    forceB (mcp (fpick p1 X1 p2 X2) L l1 l2 p1 p2) fun cp =>
    forceB (mcn (fpick p1 X1 p2 X2) L l1 l2 p1 p2) fun cn =>
    forceB (msl (fpick p1 X1 p2 X2) l1 l2 p1 p2) fun sl =>
    forceB (Nat.add l1 l2) fun wt =>
    k val cp cn sl wt

theorem cB_eq (top : ℕ) (bk : ℕ → ℕ) (L U c : ℕ) :
    Nat.mul c (Bool.rec (motive := fun _ => ℕ) 0 (lb top bk L U) (Nat.blt 0 c)) = Nat.mul c (lb top bk L U) := by
  cases c with
  | zero => simp only [Nat.mul_eq, Nat.zero_mul]
  | succ n => rfl

/-- **one minorant term**: the side conditions give the term's bound on its range -/
theorem mtrm_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)
    (L U κ lam j1 j2 : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (h : mtrm top bk tD bD pb R L U κ lam j1 j2 k = true) :
    ∃ val cp cn sl wt : ℕ, k val cp cn sl wt = true ∧
      ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
        ∃ D : ℝ, (sl : ℝ) - 2000000000 * (wt : ℝ) ≤ 1000000000 * D ∧
          32768 * (val : ℝ) + 327680000000000 * (D * (s - (L : ℝ) / 32768)) + 10 * (cp : ℝ) - 10 * (cn : ℝ)
            ≤ 327680000000000 * 1024 * wfun s := by
  unfold mtrm at h
  simp only [forceB_eq, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hl, hok⟩, hk⟩ := h
  refine ⟨_, _, _, _, _, hk, ?_⟩
  intro s hs1 hs2
  have hf : PTF (fpick (gpt L U j1) (rdIf pb (mw1 κ lam) (gpt L U j1)) (gpt L U j2) (rdIf pb (mw2 κ lam) (gpt L U j2))) :=
    fpick_ptf hpt (rdIf_cases _ _ _) (rdIf_cases _ _ _)
  obtain ⟨D, hD1, hD2⟩ := mterm_ok hlb hD hf hR L U κ lam (gpt L U j1) (gpt L U j2) hl hok s hs1 hs2
  refine ⟨D, ?_, ?_⟩
  · unfold msl at hD1 ⊢; simp only [Nat.add_eq, Nat.mul_eq] at hD1 ⊢; push_cast at hD1 ⊢; linarith
  · rw [cB_eq]
    unfold mval at hD2
    simp only [Nat.add_eq, Nat.mul_eq] at hD2 ⊢
    push_cast at hD2 ⊢
    linarith

/-- the code of a term at bit `o` of `v`: `κ` (2 bits), then `j1` (4 bits) when `κ ≥ 1`, `j2` (4 bits) when `κ = 3`,
`lam` (10 bits) when `κ ≥ 2`; `k κ lam j1 j2 o'` with `o'` the bit after the code -/
def mdec (v o : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight v o) 3) fun κ =>
  forceR (Nat.land (Nat.shiftRight v (Nat.add o 2)) 15) fun j1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight v (Nat.add o 6)) 15) (Nat.beq κ 3)) fun j2 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight v (Nat.add o 6)) 1023) (Nat.beq κ 2))
    (Nat.land (Nat.shiftRight v (Nat.add o 10)) 1023) (Nat.beq κ 3)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.add o 2) (Nat.add o 6) (Nat.beq κ 1))
      (Nat.add o 16) (Nat.beq κ 2)) (Nat.add o 20) (Nat.beq κ 3)) fun o' =>
  k κ lam j1 j2 o'

theorem mdec_elim {v o : ℕ} {k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (h : mdec v o k ≠ 0) :
    ∃ κ lam j1 j2 o' : ℕ, k κ lam j1 j2 o' ≠ 0 := by
  unfold mdec at h
  simp only [forceR_eq] at h
  exact ⟨_, _, _, _, _, h⟩

theorem brec0_ne {b : Bool} {x : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 x b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

end AMW.Cert.PyrD

end
