import TauDev

/-! ###### the band profile `min ((q+1)/q) E_band ≤ defect` (bridge-port)

AMTOPA's trace-corrected band profile (zeta-exact-pressure, MIT license), as presented in Gebendorfer, "Zeta Geometry and
Class Cap" (preprint), Lemma 3.3; here in the min form, for any Hermitian `G` (positive semidefiniteness is not used).
With `λ_i` the eigenvalues of `G` and `U` its eigenvector unitary, `defect = Σ Psi(λ_i)`.
* Fenchel bound (`bp_fenchel`). For any `A` whose eigenbasis diagonal `a_i = Re (Uᴴ A U)_ii` is `≤ 2`:
  `Psi(λ) ≥ a (λ − 1) − a²/4` (`affine_le_Psi`) and `Σ a_i² ≤ ‖Uᴴ A U‖_F² = ‖A‖_F²`, so
  `defect ≥ Re tr(A (G − 1)) − ¼ Re tr(A Aᴴ)`.
* Band bound (`bp_band_quad`). `Y` is the band part of `G` (the entries at rank distance `1 … q`). Two indices of the
  band lie in different classes `r mod (q + 1)`, so `|vᴴ Y v|² ≤ E · Σ_band p_j p_k ≤ E · q/(q+1) · (Σ p)²` with
  `p = |v|²` (`bp_class_sum`).
* Take `A = 2αY`, with `α = 1` if `E ≤ τ` and `α = τ/E` otherwise. Since `Re tr(Y (G − 1)) = Re tr(Y Yᴴ) = E`,
  `defect ≥ (2α − α²) E ≥ min τ E`. ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

section BandProfileProof

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- the band part of `G`: its entries at rank distance `1 … q` -/
def bpBand (G : Matrix κ κ ℂ) (r : κ → ℕ) (q : ℕ) : Matrix κ κ ℂ :=
  fun i j => if i ≠ j ∧ r i ≤ r j + q ∧ r j ≤ r i + q then G i j else 0

/-- two indices at rank distance `1 … q` lie in different classes `r mod (q + 1)`; the band's mass on the vector `p ≥ 0`
is at most `q/(q+1) (Σ p)²` -/
lemma bp_class_sum (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (r : κ → ℕ) (hr : Function.Injective r) (q : ℕ) :
    ∑ j, ∑ k, (if j ≠ k ∧ r j ≤ r k + q ∧ r k ≤ r j + q then p j * p k else 0)
      ≤ (q : ℝ) / (q + 1) * (∑ j, p j) ^ 2 := by
  set c : κ → ℕ := fun j => r j % (q + 1) with hc
  have hsep : ∀ j k, (j ≠ k ∧ r j ≤ r k + q ∧ r k ≤ r j + q) → c k ≠ c j := by
    rintro j k ⟨hjk, h1, h2⟩ he
    have hne : r j ≠ r k := hr.ne hjk
    simp only [hc] at he
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hd := Nat.sub_mod_eq_zero_of_mod_eq he
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hd)
      omega
    · have hd := Nat.sub_mod_eq_zero_of_mod_eq he.symm
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hd)
      omega
  set P : ℕ → ℝ := fun m => ∑ k ∈ univ.filter (fun k => c k = m), p k with hP
  have hmaps : ∀ j ∈ (univ : Finset κ), c j ∈ range (q + 1) :=
    fun j _ => mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : ∀ j, ∑ k, (if c k = c j then p j * p k else 0) = p j * P (c j) := by
    intro j
    simp only [hP, sum_filter, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hsame : ∑ j, ∑ k, (if c k = c j then p j * p k else 0) = ∑ m ∈ range (q + 1), P m ^ 2 := by
    rw [sum_congr rfl fun j _ => h1 j, ← sum_fiberwise_of_maps_to hmaps (fun j => p j * P (c j))]
    refine sum_congr rfl fun m _ => ?_
    rw [sq]
    conv_rhs => rw [hP]
    simp only [sum_mul]
    refine sum_congr rfl fun j hj => ?_
    rw [(mem_filter.1 hj).2]
  have htot : ∑ m ∈ range (q + 1), P m = ∑ j, p j := sum_fiberwise_of_maps_to hmaps p
  have hcs := sq_sum_le_card_mul_sum_sq (s := range (q + 1)) (f := P)
  rw [card_range, htot] at hcs
  push_cast at hcs
  have hle : ∑ j, ∑ k, (if j ≠ k ∧ r j ≤ r k + q ∧ r k ≤ r j + q then p j * p k else 0)
      ≤ ∑ j, ∑ k, (p j * p k - if c k = c j then p j * p k else 0) := by
    refine sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    by_cases hb : j ≠ k ∧ r j ≤ r k + q ∧ r k ≤ r j + q
    · rw [if_pos hb, if_neg (hsep j k hb)]; simp
    · rw [if_neg hb]
      split_ifs
      · simp
      · simpa using mul_nonneg (hp j) (hp k)
  have hS : ∑ j, ∑ k, (p j * p k - if c k = c j then p j * p k else 0)
      = (∑ j, p j) ^ 2 - ∑ m ∈ range (q + 1), P m ^ 2 := by
    rw [← hsame, sq, sum_mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => sum_sub_distrib _ _
  rw [hS] at hle
  have hq1 : (0 : ℝ) < q + 1 := by positivity
  have hfin : (∑ j, p j) ^ 2 - ∑ m ∈ range (q + 1), P m ^ 2 ≤ (q : ℝ) / (q + 1) * (∑ j, p j) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq1]
    nlinarith
  linarith

/-- the band's quadratic form: `|vᴴ Y v|² ≤ E · q/(q+1) · (Σ |v_j|²)²` (Cauchy–Schwarz on the band, then the classes) -/
lemma bp_band_quad (G : Matrix κ κ ℂ) (r : κ → ℕ) (hr : Function.Injective r) (q : ℕ) (v : κ → ℂ) :
    ‖∑ j, ∑ k, star (v j) * bpBand G r q j k * v k‖ ^ 2
      ≤ bandSq G r q * ((q : ℝ) / (q + 1) * (∑ j, ‖v j‖ ^ 2) ^ 2) := by
  set f : κ → κ → ℝ := fun j k => ‖bpBand G r q j k‖ with hf
  set g : κ → κ → ℝ := fun j k => if j ≠ k ∧ r j ≤ r k + q ∧ r k ≤ r j + q then ‖v j‖ * ‖v k‖ else 0 with hg
  have h1 : ‖∑ j, ∑ k, star (v j) * bpBand G r q j k * v k‖ ≤ ∑ j, ∑ k, f j k * g j k := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_))
    simp only [hf, hg, bpBand]
    split_ifs with hb
    · rw [norm_mul, norm_mul, norm_star]
      exact le_of_eq (by ring)
    · simp
  have hcs : (∑ j, ∑ k, f j k * g j k) ^ 2 ≤ (∑ j, ∑ k, f j k ^ 2) * ∑ j, ∑ k, g j k ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq (univ : Finset (κ × κ)) (fun x => f x.1 x.2) (fun x => g x.1 x.2)
    simpa only [Fintype.sum_prod_type] using this
  have hf2 : ∑ j, ∑ k, f j k ^ 2 = bandSq G r q := by
    unfold bandSq
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    simp only [hf, bpBand]
    split_ifs <;> simp
  have hg2 : ∑ j, ∑ k, g j k ^ 2 ≤ (q : ℝ) / (q + 1) * (∑ j, ‖v j‖ ^ 2) ^ 2 := by
    refine le_trans (le_of_eq ?_) (bp_class_sum (fun j => ‖v j‖ ^ 2) (fun j => by positivity) r hr q)
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    simp only [hg]
    split_ifs <;> ring
  have hE0 : 0 ≤ bandSq G r q :=
    sum_nonneg fun j _ => sum_nonneg fun k _ => by split_ifs <;> positivity
  calc ‖∑ j, ∑ k, star (v j) * bpBand G r q j k * v k‖ ^ 2 ≤ (∑ j, ∑ k, f j k * g j k) ^ 2 := by
        gcongr
    _ ≤ (∑ j, ∑ k, f j k ^ 2) * ∑ j, ∑ k, g j k ^ 2 := hcs
    _ ≤ bandSq G r q * ((q : ℝ) / (q + 1) * (∑ j, ‖v j‖ ^ 2) ^ 2) := by
        rw [hf2]; exact mul_le_mul_of_nonneg_left hg2 hE0

/-- the Fenchel bound: if `G − 1 = U diag(λ − 1) Uᴴ` with `U` unitary and the eigenbasis diagonal of `A` is `≤ 2`, then
`defect ≥ Re tr(A (G − 1)) − ¼ Re tr(A Aᴴ)` -/
lemma bp_fenchel {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (U : Matrix κ κ ℂ) (hUU : U * star U = 1)
    (hG1 : G - 1 = U * diagonal (fun i => ((hG.eigenvalues i - 1 : ℝ) : ℂ)) * star U) (A : Matrix κ κ ℂ)
    (hA : ∀ i, ((star U * A * U) i i).re ≤ 2) :
    rtrace (A * (G - 1)) - rtrace (A * Aᴴ) / 4 ≤ defect hG := by
  have htr : rtrace (A * (G - 1)) = ∑ i, ((star U * A * U) i i).re * (hG.eigenvalues i - 1) := by
    rw [hG1]
    unfold rtrace
    rw [show A * (U * diagonal (fun i => ((hG.eigenvalues i - 1 : ℝ) : ℂ)) * star U)
        = (A * U * diagonal (fun i => ((hG.eigenvalues i - 1 : ℝ) : ℂ))) * star U by
          simp only [Matrix.mul_assoc],
      trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, mul_diagonal, map_sum, RCLike.re_to_complex]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hWW : (star U * A * U) * (star U * A * U)ᴴ = star U * (A * Aᴴ) * U := by
    rw [conjTranspose_mul, conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [Matrix.star_eq_conjTranspose] at hUU
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
  have hfro : rtrace (A * Aᴴ) = rtrace ((star U * A * U) * (star U * A * U)ᴴ) := by
    rw [hWW]
    unfold rtrace
    rw [trace_mul_comm (star U * (A * Aᴴ)) U, ← Matrix.mul_assoc U (star U), hUU, Matrix.one_mul]
  have hdiag : ∑ i, ((star U * A * U) i i).re ^ 2 ≤ rtrace (A * Aᴴ) := by
    rw [hfro, rtrace_self_mul_conjTranspose]
    refine sum_le_sum fun i _ => ?_
    have h0 : ((star U * A * U) i i).re ^ 2 ≤ ‖(star U * A * U) i i‖ ^ 2 := by
      have h := Complex.abs_re_le_norm ((star U * A * U) i i)
      nlinarith [abs_nonneg ((star U * A * U) i i).re, sq_abs ((star U * A * U) i i).re]
    exact h0.trans (single_le_sum (f := fun i' => ‖(star U * A * U) i' i‖ ^ 2) (fun _ _ => by positivity) (mem_univ i))
  have hpt : ∀ i, ((star U * A * U) i i).re * (hG.eigenvalues i - 1) - ((star U * A * U) i i).re ^ 2 / 4
      ≤ Psi (hG.eigenvalues i) := by
    intro i
    have h := affine_le_Psi (s := 1 + ((star U * A * U) i i).re / 2) (x := hG.eigenvalues i) (by linarith [hA i])
    nlinarith [h]
  have hsum : ∑ i, (((star U * A * U) i i).re * (hG.eigenvalues i - 1) - ((star U * A * U) i i).re ^ 2 / 4)
      ≤ defect hG := by
    unfold defect
    rw [rtrace_specMap]
    exact sum_le_sum fun i _ => hpt i
  rw [sum_sub_distrib, ← sum_div, ← htr] at hsum
  linarith

/-- **The band profile** (AMTOPA, after Gebendorfer Lemma 3.3), for any Hermitian `G`, injective ranking `r` and
`q ≥ 1`: `min ((q+1)/q) (bandSq G r q) ≤ defect`. -/
theorem band_profile_herm {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (r : κ → ℕ) (hr : Function.Injective r)
    (q : ℕ) (hq : 1 ≤ q) : min (((q : ℝ) + 1) / q) (bandSq G r q) ≤ defect hG := by
  obtain ⟨U, hUU, hUU', hG1⟩ : ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      G - 1 = U * diagonal (fun i => ((hG.eigenvalues i - 1 : ℝ) : ℂ)) * star U :=
    ⟨_, Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2, Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2,
      by rw [← specMap_sub_one hG]; unfold specMap; rw [Unitary.conjStarAlgAut_apply]; rfl⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- the two traces of the band part
  have hYG : rtrace (bpBand G r q * (G - 1)) = bandSq G r q := by
    unfold rtrace bandSq
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, RCLike.re_to_complex]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bpBand]
    split_ifs with hb
    · rw [Matrix.sub_apply, Matrix.one_apply_ne (Ne.symm hb.1), sub_zero, ← hG.apply j i, RCLike.star_def,
        RCLike.mul_conj]
      norm_cast
    · simp
  have hYY : rtrace (bpBand G r q * (bpBand G r q)ᴴ) = bandSq G r q := by
    rw [rtrace_self_mul_conjTranspose, sum_comm]
    unfold bandSq
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bpBand]
    split_ifs <;> simp
  obtain ⟨E, hE⟩ : ∃ E, bandSq G r q = E := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, ((q : ℝ) + 1) / q = τ := ⟨_, rfl⟩
  rw [hE, hτ]
  rw [hE] at hYG hYY
  have hτ0 : 0 < τ := by rw [← hτ]; positivity
  have hE0 : 0 ≤ E := by rw [← hE]; exact sum_nonneg fun j _ => sum_nonneg fun k _ => by split_ifs <;> positivity
  -- each eigenvector is a unit vector, and the band form on it is at most `E/τ`
  have hcol : ∀ i, ∑ j, ‖U j i‖ ^ 2 = 1 := by
    intro i
    have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have h := congrArg Complex.re (congrFun (congrFun hUU' i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum, Complex.one_re] at h
    simpa only [hre] using h
  have hz : ∀ i, ‖(star U * bpBand G r q * U) i i‖ ^ 2 * τ ≤ E := by
    intro i
    have hexp : (star U * bpBand G r q * U) i i = ∑ j, ∑ k, star (U j i) * bpBand G r q j k * U k i := by
      simp only [Matrix.mul_apply, Matrix.star_apply, sum_mul]
      exact sum_comm
    have hb := bp_band_quad G r hr q (fun j => U j i)
    beta_reduce at hb
    rw [hcol i, one_pow, mul_one, hE] at hb
    rw [hexp]
    calc ‖∑ j, ∑ k, star (U j i) * bpBand G r q j k * U k i‖ ^ 2 * τ ≤ E * ((q : ℝ) / (q + 1)) * τ := by
          gcongr
      _ = E := by rw [← hτ]; field_simp
  -- `A = 2αY` with `α² E ≤ τ` gives `defect ≥ (2α − α²) E`
  have key : ∀ α : ℝ, 0 ≤ α → α ^ 2 * E ≤ τ → (2 * α - α ^ 2) * E ≤ defect hG := by
    intro α hα hαE
    have hF := bp_fenchel hG U hUU hG1 ((((2 * α : ℝ)) : ℂ) • bpBand G r q) (fun i => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      have h1 := Complex.re_le_norm ((star U * bpBand G r q * U) i i)
      have h2 : (α * ‖(star U * bpBand G r q * U) i i‖) ^ 2 ≤ 1 := by
        have h4 : α ^ 2 * (‖(star U * bpBand G r q * U) i i‖ ^ 2 * τ) ≤ α ^ 2 * E :=
          mul_le_mul_of_nonneg_left (hz i) (sq_nonneg α)
        have h5 : (α * ‖(star U * bpBand G r q * U) i i‖) ^ 2 * τ ≤ 1 * τ := by nlinarith
        exact le_of_mul_le_mul_right h5 hτ0
      have h3 : α * ‖(star U * bpBand G r q * U) i i‖ ≤ 1 := by
        nlinarith [mul_nonneg hα (norm_nonneg ((star U * bpBand G r q * U) i i))]
      nlinarith)
    have h1 : rtrace ((((2 * α : ℝ)) : ℂ) • bpBand G r q * (G - 1)) = 2 * α * E := by
      rw [Matrix.smul_mul]
      unfold rtrace at hYG ⊢
      rw [Matrix.trace_smul, smul_eq_mul, RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, hYG]
    have h2 : rtrace ((((2 * α : ℝ)) : ℂ) • bpBand G r q * ((((2 * α : ℝ)) : ℂ) • bpBand G r q)ᴴ)
        = 4 * α ^ 2 * E := by
      rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      unfold rtrace at hYY ⊢
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.re_ofReal_mul,
        ← RCLike.re_to_complex, hYY]
      ring
    rw [h1, h2] at hF
    linarith
  rcases le_or_gt E τ with h | h
  · have := key 1 zero_le_one (by simpa using h)
    exact (min_le_right _ _).trans (by linarith)
  · have hEpos : 0 < E := hτ0.trans h
    have := key (τ / E) (by positivity) (by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := mul_pos (mul_pos hτ0 hEpos) (sub_pos.mpr h)
      nlinarith)
    refine (min_le_left _ _).trans (le_trans ?_ this)
    rw [show (2 * (τ / E) - (τ / E) ^ 2) * E = 2 * τ - τ * (τ / E) by field_simp]
    have : τ / E ≤ 1 := (div_le_one hEpos).mpr h.le
    nlinarith

/-- `BandProfile` (the hypothesis of `block_bound_w'_τ`) -/
theorem band_profile_holds : BandProfile := by
  intro κ _ _ G hG r hr q hq
  exact band_profile_herm hG.1 r hr q hq

end BandProfileProof

end Zeta23Ext.BridgeW

end
