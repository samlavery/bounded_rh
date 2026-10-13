
/-! ### the mean-value step for one pair term, and the per-gap bound -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the mean value theorem on a pair-sum interval read with nonzero derivative bounds `p`, `q`: the increment of `w`
between two points of `[lo, hi] / SC` is `d` times the increment of the argument, `p − 2 U1 ≤ U1 d ≤ 2 U1 − q` -/
theorem mvt_pair {tP : ℕ} {bP : ℕ → ℕ} {tM : ℕ} {bM : ℕ → ℕ} (hP : LBSoundD true tP bP)
    (hM : LBSoundD false tM bM) (lo hi : ℕ) (hp : 1 ≤ lb tP bP lo hi) (hq : 1 ≤ lb tM bM lo hi) (y z : ℝ)
    (hy1 : (lo : ℝ) / SC ≤ y) (hy2 : y ≤ (hi : ℝ) / SC) (hz1 : (lo : ℝ) / SC ≤ z) (hz2 : z ≤ (hi : ℝ) / SC) :
    ∃ d : ℝ, wfun z = wfun y + d * (z - y) ∧ (lb tP bP lo hi : ℝ) - 2000000000 ≤ 1000000000 * d ∧
      1000000000 * d ≤ 2000000000 - (lb tM bM lo hi : ℝ) := by
  have hp0 : lb tP bP lo hi ≠ 0 := by omega
  have hq0 : lb tM bM lo hi ≠ 0 := by omega
  have hb : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC →
      kD ξ < 0 ∧ (lb tP bP lo hi : ℝ) - 2000000000 ≤ 1000000000 * w1 ξ ∧
        1000000000 * w1 ξ ≤ 2000000000 - (lb tM bM lo hi : ℝ) := by
    intro ξ h1 h2
    obtain ⟨hk, hPb⟩ := hP lo hi ξ h1 h2 hp0
    obtain ⟨_, hMb⟩ := hM lo hi ξ h1 h2 hq0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPb hMb
    rw [div_le_iff₀ U1_posR] at hPb hMb
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    rw [eU] at hPb hMb
    exact ⟨hk, by linarith, by linarith⟩
  have hderiv : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC → HasDerivAt wfun (w1 ξ) ξ :=
    fun ξ h1 h2 => hasDerivAt_wfun ξ (hb ξ h1 h2).1.ne
  rcases lt_trichotomy y z with hyz | hyz | hyz
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hy1.trans hξ.1) (hξ.2.trans hz2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring
  · subst hyz
    obtain ⟨_, h1, h2⟩ := hb y hy1 hy2
    exact ⟨w1 y, by ring, h1, h2⟩
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hz1.trans hξ.1) (hξ.2.trans hy2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring

/-- one gap's term of the mean-value expansion: `e ∈ [−lo, hi]`, `U1 E ≤ P`, `−U1 E ≤ N` -/
theorem mterm {e E lo hi P N : ℝ} (he1 : -lo ≤ e) (he2 : e ≤ hi) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hP : 1000000000 * E ≤ P) (hN : -(1000000000 * E) ≤ N) (hP0 : 0 ≤ P) (hN0 : 0 ≤ N) :
    -(lo * P) - hi * N ≤ 1000000000 * (e * E) := by
  rcases le_total 0 e with h | h
  · have h1 := mul_le_mul_of_nonneg_left (show -N ≤ 1000000000 * E by linarith) h
    have h2 := mul_le_mul_of_nonneg_right he2 hN0
    nlinarith [mul_nonneg hlo hP0]
  · have h1 := mul_le_mul_of_nonpos_left hP h
    have h2 := mul_le_mul_of_nonneg_right he1 hP0
    nlinarith [mul_nonneg hhi hN0]

/-- truncated subtraction bounds the real difference from above -/
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have := (Nat.cast_le (α := ℝ)).mpr h
    simp only [Nat.cast_zero]; linarith

theorem natsub_nonneg (a b : ℕ) : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _

/-! ### the combined check of the two derivative tables, and the table-level corollaries -/

theorem allBelow_of {n : ℕ} {f : ℕ → Bool} (h : ∀ i < n, f i = true) : allBelow n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Bool.rec (motive := fun _ => Bool) false (f n) (allBelow n f) = true
    rw [ih (fun i hi => h i (by omega))]
    exact h n (by omega)

theorem allBelow_and {n : ℕ} {f g : ℕ → Bool} (h : allBelow n (fun t => f t && g t) = true) :
    allBelow n f = true ∧ allBelow n g = true := by
  have h' := allBelow_spec h
  refine ⟨allBelow_of fun i hi => ?_, allBelow_of fun i hi => ?_⟩
  · have := h' i hi; rw [Bool.and_eq_true] at this; exact this.1
  · have := h' i hi; rw [Bool.and_eq_true] at this; exact this.2

theorem allBelow_and2 {n : ℕ} {f g : ℕ → ℕ → Bool}
    (h : allBelow n (fun d => allBelow (Nat.shiftLeft 1 d) (fun t => f d t && g d t)) = true) :
    allBelow n (fun d => allBelow (Nat.shiftLeft 1 d) (f d)) = true ∧
      allBelow n (fun d => allBelow (Nat.shiftLeft 1 d) (g d)) = true := by
  have h' := allBelow_spec h
  refine ⟨allBelow_of fun i hi => (allBelow_and (h' i hi)).1, allBelow_of fun i hi => (allBelow_and (h' i hi)).2⟩

theorem blockOkPM_split {XP XM j : ℕ} (h : blockOkPM XP XM j = true) :
    blockOkD true XP j = true ∧ blockOkD false XM j = true := by
  have hD : ∀ (sgn : Bool) (X : ℕ), blockOkDX sgn X j = true → blockOkD sgn X j = true := by
    intro sgn X hX
    unfold blockOkD
    cases Nat.beq X 0
    · exact hX
    · rfl
  unfold blockOkPM at h
  cases hz : (Nat.beq XP 0 && Nat.beq XM 0)
  · rw [hz] at h
    have h' : blockOkPMX XP XM j = true := h
    unfold blockOkPMX at h'
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨h10, hr⟩, hfin⟩, hint⟩ := h'
    have hrr : Nat.land XM 31 = Nat.land XP 31 := by
      have := hr; rw [Nat.beq_eq] at this; exact this
    obtain ⟨hfP, hfM⟩ := allBelow_and hfin
    obtain ⟨hiP, hiM⟩ := allBelow_and2 hint
    refine ⟨hD true XP ?_, hD false XM ?_⟩
    · unfold blockOkDX
      simp only [Bool.and_eq_true]
      exact ⟨⟨h10, hfP⟩, hiP⟩
    · unfold blockOkDX
      simp only [Bool.and_eq_true]
      rw [hrr]
      exact ⟨⟨h10, hfM⟩, hiM⟩
  · rw [Bool.and_eq_true] at hz
    obtain ⟨h1, h2⟩ := hz
    have e1 : XP = 0 := by rw [← Nat.beq_eq]; exact h1
    have e2 : XM = 0 := by rw [← Nat.beq_eq]; exact h2
    subst e1; subst e2
    exact ⟨rfl, rfl⟩

theorem dblocks_of {bP bM : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOkPM (bP j) (bM j) j) = true) :
    (∀ j < 512, blockOkD true (bP j) j = true) ∧ (∀ j < 512, blockOkD false (bM j) j = true) := by
  have h' := allFrom_spec h
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := h' j hj; simp only [Nat.zero_add] at this; exact (blockOkPM_split this).1
  · have := h' j hj; simp only [Nat.zero_add] at this; exact (blockOkPM_split this).2

theorem ptblocks_of {pb : ℕ → ℕ} (h : allFrom 0 512 (fun j => ptBlockOk (pb j) j) = true) :
    ∀ j < 512, ptBlockOk (pb j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
