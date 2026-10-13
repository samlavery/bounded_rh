
/-! ### the mean-value step for one pair term, and the per-gap bound -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the mean value theorem on a pair-sum interval read with nonzero derivative bounds `p`, `q`: the increment of `w`
between two points of `[lo, hi] / SC` is `d` times the increment of the argument, `p − 2 U1 ≤ U1 d ≤ 2 U1 − q` -/
theorem mvt_pair {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSound2 tD bD) (lo hi : ℕ) (hp : 1 ≤ lo32 (lb2 tD bD lo hi))
    (hq : 1 ≤ hi32 (lb2 tD bD lo hi)) (y z : ℝ)
    (hy1 : (lo : ℝ) / SC ≤ y) (hy2 : y ≤ (hi : ℝ) / SC) (hz1 : (lo : ℝ) / SC ≤ z) (hz2 : z ≤ (hi : ℝ) / SC) :
    ∃ d : ℝ, wfun z = wfun y + d * (z - y) ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * d ∧
      1000000000 * d ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
  have hp0 : lo32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hq0 : hi32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hb : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC →
      kD ξ < 0 ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * w1 ξ ∧
        1000000000 * w1 ξ ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
    intro ξ h1 h2
    obtain ⟨hk, hPb⟩ := (hD lo hi ξ h1 h2).1 hp0
    obtain ⟨_, hMb⟩ := (hD lo hi ξ h1 h2).2 hq0
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

theorem ptblocks_of {pb : ℕ → ℕ} (h : allFrom 0 512 (fun j => ptBlockOk (pb j) j) = true) :
    ∀ j < 512, ptBlockOk (pb j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
