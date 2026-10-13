import AMW.Constant

/-!
# AMW/Floor — a rational floor for `H_W` and the ranges of `a`, `b` (stage E4)

* `HW_ge : 67218115/10⁸ ≤ HW` (`HW = 0.6721811508…`; the floor is `8.6·10⁻¹⁰` below);
* `1/2 < aInf < 1`, `1/2 < bInf` (Cauchy–Schwarz `bInf ≥ aInf²`), hence eventually
  `1/2 ≤ a_T ≤ 1` and `1/2 ≤ b_T` for the data `localFunW P T`.
Enclosures of `sin θ₀, cos θ₀` (`θ₀ = √2/2`) by the twelve-term Taylor bound (the argument of the record
file's `cos_sin_taylor12`).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

theorem taylor12_F (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

theorem sqrt2_half_bounds :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

theorem cos_theta0_le : Real.cos (Real.sqrt 2 / 2) ≤ 76024459708 / 10 ^ 11 := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475244/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.cos (Real.sqrt 2 / 2) ≤ Real.cos r :=
    Real.cos_le_cos_of_nonneg_of_le_pi hr0 (by linarith [hb.2, Real.pi_gt_three]) hb.1
  have ht := (abs_le.mp (taylor12_F r hr1).1).2
  rw [abs_of_nonneg hr0] at ht
  have hv : (1 - r^2/2 + r^4/24 - r^6/720 + r^8/40320 - r^10/3628800) + r ^ 12 * (13/5748019200)
      ≤ 76024459708 / 10 ^ 11 := by
    rw [hr]; norm_num
  linarith

theorem sin_theta0_ge : 64963693904 / 10 ^ 11 ≤ Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475244/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.sin r ≤ Real.sin (Real.sqrt 2 / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
      (by linarith [hb.2, Real.pi_gt_three]) hb.1
  have ht := (abs_le.mp (taylor12_F r hr1).2).1
  rw [abs_of_nonneg hr0] at ht
  have hv : 64963693904 / 10 ^ 11
      ≤ (r - r^3/6 + r^5/120 - r^7/5040 + r^9/362880 - r^11/39916800) - r ^ 12 * (13/5748019200) := by
    rw [hr]; norm_num
  linarith

theorem sin_theta0_le : Real.sin (Real.sqrt 2 / 2) ≤ 64963693912 / 10 ^ 11 := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475245/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.sin (Real.sqrt 2 / 2) ≤ Real.sin r :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hb.1, Real.pi_gt_three])
      (by rw [hr]; linarith [Real.pi_gt_three]) hb.2
  have ht := (abs_le.mp (taylor12_F r hr1).2).2
  rw [abs_of_nonneg hr0] at ht
  have hv : (r - r^3/6 + r^5/120 - r^7/5040 + r^9/362880 - r^11/39916800) + r ^ 12 * (13/5748019200)
      ≤ 64963693912 / 10 ^ 11 := by
    rw [hr]; norm_num
  linarith

/-- `PAM` with `π` replaced by its upper bound `π_hi` (an upper bound for `PAM`). -/
def PAMhi : ℝ :=
  ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * (314159265358979323847 / 10 ^ 20) ^ 2 * ((n : ℝ) + 1) ^ 2))

theorem PAM_le : PAM ≤ PAMhi := by
  unfold PAM PAMhi
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply sub_le_sub_left
  have hπ := Real.pi_lt_d20
  have hπ0 := Real.pi_pos
  have hk : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  apply one_div_le_one_div_of_le (by positivity)
  have : π ^ 2 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ hπ0.le; linarith
  have := mul_le_mul_of_nonneg_right this hk.le
  nlinarith

theorem PAMhi_nonneg : 0 ≤ PAMhi := by
  unfold PAMhi
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg (sq_nonneg _)
  have hk : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith
  have : 1 / (4 * (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem floor_numeric :
    (67218115 / 10 ^ 8 : ℝ) ≤ 3 / 2 - (76024459708 / 10 ^ 11) / (2 * (7071067811865475244/10^19) * (64963693904 / 10 ^ 11))
      - PAMhi / (2 * (64963693904 / 10 ^ 11) ^ 2) := by
  unfold PAMhi dAM
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
  norm_num

/-- **The rational floor**: `0.67218115 ≤ H_W`. -/
theorem HW_ge : (67218115 / 10 ^ 8 : ℝ) ≤ HW := by
  rw [HW_eq]
  have hc := cos_theta0_le
  have hs := sin_theta0_ge
  have hb := sqrt2_half_bounds
  have hP := PAM_le
  have hP0 := PAMhi_nonneg
  have hs0 : (0:ℝ) < 64963693904 / 10 ^ 11 := by norm_num
  have hr0 : (0:ℝ) < 7071067811865475244/10^19 := by norm_num
  have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
  have hden : 2 * (7071067811865475244/10^19 : ℝ) * (64963693904 / 10 ^ 11)
      ≤ Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
    have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
    exact mul_le_mul h2 hs hs0.le (Real.sqrt_nonneg 2)
  have h1 : Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      ≤ (76024459708 / 10 ^ 11) / (2 * (7071067811865475244/10^19) * (64963693904 / 10 ^ 11)) :=
    div_le_div₀ (by norm_num) hc (by positivity) hden
  have hsq : (64963693904 / 10 ^ 11 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 :=
    pow_le_pow_left₀ hs0.le hs 2
  have h2 : PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤ PAMhi / (2 * (64963693904 / 10 ^ 11) ^ 2) :=
    div_le_div₀ hP0 hP (by positivity) (by linarith)
  have := floor_numeric
  linarith

/-! ## Ranges of `a` and `b` -/

theorem aInf_eq : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
  unfold aInf; rw [integral_vAM]

theorem aInf_gt_half : 1 / 2 < aInf := by
  rw [aInf_eq]
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_ge
  unfold MAM
  rw [lt_div_iff₀ (by norm_num)]
  have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
  nlinarith

theorem aInf_lt_one : aInf < 1 := by
  rw [aInf_eq]
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_le
  have hs0 := sin_theta0_pos
  unfold MAM
  rw [div_lt_iff₀ (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 * (7071067811865475245/10^19 : ℝ) := by linarith [hb.2]
  nlinarith [Real.sqrt_nonneg 2]

/-- Cauchy–Schwarz on the unit window: `bInf ≥ aInf²`. -/
theorem aInf_sq_le_bInf : aInf ^ 2 ≤ bInf := by
  set q : ℝ → ℝ := fun s => vAM s / MAM with hq
  have hqc : Continuous q := vAM_continuous.div_const _
  have ha : aInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s := by
    unfold aInf; rw [hq, intervalIntegral.integral_div]
  have hb : bInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s ^ 2 := rfl
  have h0 : 0 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have hexp : ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 = bInf - aInf ^ 2 := by
    have e : (fun s => (q s - aInf) ^ 2) = fun s => q s ^ 2 - 2 * aInf * q s + aInf ^ 2 := by
      funext s; ring
    have i1 : IntervalIntegrable (fun s => q s ^ 2 - 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
      ((hqc.pow 2).sub (continuous_const.mul hqc)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => q s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
      (hqc.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun s => 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
      (continuous_const.mul hqc).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← ha, ← hb]
    simp only [smul_eq_mul]
    ring
  linarith

theorem bInf_gt_half : 1 / 2 < bInf := by
  have h1 := aInf_gt_half
  have h2 := aInf_sq_le_bInf
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_ge
  -- aInf ≥ 2·r_lo·s_lo/(5/4) > 0.734, so aInf² > 1/2
  have ha : (734 / 1000 : ℝ) < aInf := by
    rw [aInf_eq]
    unfold MAM
    rw [lt_div_iff₀ (by norm_num)]
    have h2' : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
    nlinarith
  nlinarith

theorem eventually_aW_range {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).a ∧ (localFunW P T).a ≤ 1 := by
  have h := tendsto_aW hP
  filter_upwards [h.eventually (lt_mem_nhds aInf_gt_half), h.eventually (gt_mem_nhds aInf_lt_one)]
    with T h1 h2
  exact ⟨h1.le, h2.le⟩

theorem eventually_bW_ge_half {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).b := by
  filter_upwards [(tendsto_bW hP).eventually (lt_mem_nhds bInf_gt_half)] with T h
  exact h.le

end AMW
