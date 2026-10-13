import AMW.DEFourier

/-! ###### AMW/DEDensity — the density (DC) term by Cauchy–Schwarz (bridge-port)

Let `B ≥ 0` be continuous with compact support and `κ(x) = ∫ B(α) cos(2παx) dα ≥ 0` with `∫ κ = 1`.  For a finite
configuration of weights `m_a ≥ 0` at points `x_a ∈ [0, W]` (total `N`) and the trapezoid comparison weight `ψ`
(`1` on `[−M, W+M]`, `0` off `[−2M, W+2M]`),
  `N² (∫_{−M}^{M} κ)² / ∫ψ ≤ ∫ B(α) |S(α)|² dα`  (`density_lb`),
by the positivity of `∫ B |S − λ ψ̂|²` in `λ`: the cross term is `Σ_a m_a ∫ ψ(y) κ(x_a − y) dy ≥ N ∫_{−M}^{M} κ`
(`cross_eq`) and the square term is `∫∫ ψψ κ ≤ ∫ ψ` (`quad_eq`).  No local density of the points enters, only
their number and the length of the interval. ###### -/

noncomputable section

open Real MeasureTheory Finset Set Filter

namespace AMW.DE

/-- the cosine transform of a weight -/
def Cw (ψ : ℝ → ℝ) (α : ℝ) : ℝ := ∫ y, ψ y * Real.cos (2 * π * α * y)

/-- the sine transform of a weight -/
def Sw (ψ : ℝ → ℝ) (α : ℝ) : ℝ := ∫ y, ψ y * Real.sin (2 * π * α * y)

section Density

variable {B κ ψ : ℝ → ℝ}

theorem integrable_mul_cos_of_cs (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (a : ℝ) :
    Integrable (fun y => ψ y * Real.cos (2 * π * a * y)) :=
  (hψc.mul (Real.continuous_cos.comp (by fun_prop))).integrable_of_hasCompactSupport hψs.mul_right

theorem integrable_mul_sin_of_cs (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (a : ℝ) :
    Integrable (fun y => ψ y * Real.sin (2 * π * a * y)) :=
  (hψc.mul (Real.continuous_sin.comp (by fun_prop))).integrable_of_hasCompactSupport hψs.mul_right

theorem continuous_Cw (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) : Continuous (Cw ψ) := by
  unfold Cw
  refine continuous_of_dominated (bound := fun y => |ψ y|) (fun α => ?_) (fun α => ?_) ?_ ?_
  · exact (integrable_mul_cos_of_cs hψc hψs α).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact (hψc.integrable_of_hasCompactSupport hψs).abs
  · exact Eventually.of_forall fun y => continuous_const.mul (Real.continuous_cos.comp (by fun_prop))

theorem continuous_Sw (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) : Continuous (Sw ψ) := by
  unfold Sw
  refine continuous_of_dominated (bound := fun y => |ψ y|) (fun α => ?_) (fun α => ?_) ?_ ?_
  · exact (integrable_mul_sin_of_cs hψc hψs α).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · exact (hψc.integrable_of_hasCompactSupport hψs).abs
  · exact Eventually.of_forall fun y => continuous_const.mul (Real.continuous_sin.comp (by fun_prop))

/-- the uncurried product `B(α) ψ(y) F(α, y)` has compact support -/
theorem hasCompactSupport_prod_mul (hBs : HasCompactSupport B) (hψs : HasCompactSupport ψ) (F : ℝ → ℝ → ℝ) :
    HasCompactSupport (Function.uncurry fun α y => B α * (ψ y * F α y)) := by
  refine HasCompactSupport.intro (hBs.isCompact.prod hψs.isCompact) fun p hp => ?_
  simp only [Function.uncurry]
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, mul_zero]

/-- **the cross term**: `∫ B(α) (cos(2παx) Cψ(α) + sin(2παx) Sψ(α)) dα = ∫ ψ(y) κ(x − y) dy` -/
theorem cross_eq (hBc : Continuous B) (hBs : HasCompactSupport B) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hκ : ∀ x, κ x = ∫ α, B α * Real.cos (2 * π * α * x)) (x : ℝ) :
    ∫ α, B α * (Real.cos (2 * π * α * x) * Cw ψ α + Real.sin (2 * π * α * x) * Sw ψ α)
      = ∫ y, ψ y * κ (x - y) := by
  have h1 : ∀ α, B α * (Real.cos (2 * π * α * x) * Cw ψ α + Real.sin (2 * π * α * x) * Sw ψ α)
      = ∫ y, B α * (ψ y * Real.cos (2 * π * α * (x - y))) := by
    intro α
    unfold Cw Sw
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((integrable_mul_cos_of_cs hψc hψs α).const_mul _)
        ((integrable_mul_sin_of_cs hψc hψs α).const_mul _), ← integral_const_mul]
    congr 1 with y
    rw [show 2 * π * α * (x - y) = 2 * π * α * x - 2 * π * α * y by ring, Real.cos_sub]
    ring
  simp_rw [h1]
  rw [integral_integral_swap_of_hasCompactSupport (f := fun α y => B α * (ψ y * Real.cos (2 * π * α * (x - y))))
    (by fun_prop) (hasCompactSupport_prod_mul hBs hψs _)]
  congr 1 with y
  rw [hκ (x - y), ← integral_const_mul]
  congr 1 with α
  ring

/-- **the square term**: `∫ B(α) (Cψ(α)² + Sψ(α)²) dα = ∫ ψ(y) ∫ ψ(y') κ(y − y') dy' dy` -/
theorem quad_eq (hBc : Continuous B) (hBs : HasCompactSupport B) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hκ : ∀ x, κ x = ∫ α, B α * Real.cos (2 * π * α * x)) :
    ∫ α, B α * (Cw ψ α ^ 2 + Sw ψ α ^ 2) = ∫ y, ψ y * ∫ y', ψ y' * κ (y - y') := by
  have hCc := continuous_Cw hψc hψs
  have hSc := continuous_Sw hψc hψs
  have h1 : ∀ α, B α * (Cw ψ α ^ 2 + Sw ψ α ^ 2)
      = ∫ y, B α * (ψ y * (Real.cos (2 * π * α * y) * Cw ψ α + Real.sin (2 * π * α * y) * Sw ψ α)) := by
    intro α
    rw [integral_const_mul]
    congr 1
    have e : ∀ y, ψ y * (Real.cos (2 * π * α * y) * Cw ψ α + Real.sin (2 * π * α * y) * Sw ψ α)
        = Cw ψ α * (ψ y * Real.cos (2 * π * α * y)) + Sw ψ α * (ψ y * Real.sin (2 * π * α * y)) := by
      intro y; ring
    simp_rw [e]
    rw [integral_add ((integrable_mul_cos_of_cs hψc hψs α).const_mul _)
        ((integrable_mul_sin_of_cs hψc hψs α).const_mul _), integral_const_mul, integral_const_mul]
    unfold Cw Sw
    ring
  simp_rw [h1]
  rw [integral_integral_swap_of_hasCompactSupport
    (f := fun α y => B α * (ψ y * (Real.cos (2 * π * α * y) * Cw ψ α + Real.sin (2 * π * α * y) * Sw ψ α)))
    (by fun_prop) (hasCompactSupport_prod_mul hBs hψs _)]
  congr 1 with y
  rw [← cross_eq hBc hBs hψc hψs hκ y, ← integral_const_mul]
  congr 1 with α
  ring

/-- the square term is at most `∫ ψ` (`0 ≤ ψ ≤ 1`, `κ ≥ 0`, `∫ κ = 1`) -/
theorem quad_le (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1)
    (hκ0 : ∀ x, 0 ≤ κ x) (hκi : Integrable κ) (hκ1 : ∫ x, κ x = 1) :
    ∫ y, ψ y * ∫ y', ψ y' * κ (y - y') ≤ ∫ y, ψ y := by
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hin : ∀ y, ∫ y', ψ y' * κ (y - y') ≤ 1 := by
    intro y
    have hκy : Integrable (fun y' => κ (y - y')) := hκi.comp_sub_left y
    calc ∫ y', ψ y' * κ (y - y') ≤ ∫ y', κ (y - y') := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y' => mul_nonneg (hψ0 y') (hκ0 _)) hκy
            (Eventually.of_forall fun y' => ?_)
          exact mul_le_of_le_one_left (hκ0 _) (hψ1 y')
      _ = 1 := by rw [integral_sub_left_eq_self (fun t => κ t) volume y, hκ1]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (hψ0 y) ?_) hψi
    (Eventually.of_forall fun y => ?_)
  · exact integral_nonneg fun y' => mul_nonneg (hψ0 y') (hκ0 _)
  · exact mul_le_of_le_one_right (hψ0 y) (hin y)

/-- the cross term is at least `∫_{−M}^{M} κ` at a point of `[0, W]` -/
theorem cross_ge (hψc : Continuous ψ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1) {W M : ℝ}
    (hψI : ∀ y, -M ≤ y → y ≤ W + M → ψ y = 1) (hκ0 : ∀ x, 0 ≤ κ x) (hκi : Integrable κ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxW : x ≤ W) :
    ∫ t in (-M)..M, κ t ≤ ∫ y, ψ y * κ (x - y) := by
  rcases le_or_gt M (-M) with hM | hM
  · rw [intervalIntegral.integral_of_ge hM]
    have : 0 ≤ ∫ t in Ioc M (-M), κ t := setIntegral_nonneg measurableSet_Ioc fun t _ => hκ0 t
    have h2 : 0 ≤ ∫ y, ψ y * κ (x - y) := integral_nonneg fun y => mul_nonneg (hψ0 y) (hκ0 _)
    linarith
  rw [← integral_sub_left_eq_self (fun y => ψ y * κ (x - y)) volume x]
  simp only [sub_sub_cancel]
  rw [intervalIntegral.integral_of_le hM.le, ← integral_indicator measurableSet_Ioc]
  have hg : Integrable (fun t => ψ (x - t) * κ t) :=
    hκi.bdd_mul (c := 1) ((hψc.comp (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 _)]; exact hψ1 _)
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) hg (Eventually.of_forall fun t => ?_)
  · exact indicator_nonneg (fun t _ => hκ0 t) t
  · show (Ioc (-M) M).indicator κ t ≤ ψ (x - t) * κ t
    by_cases ht : t ∈ Ioc (-M) M
    · rw [indicator_of_mem ht, hψI (x - t) (by linarith [ht.2]) (by linarith [ht.1]), one_mul]
    · rw [indicator_of_notMem ht]
      exact mul_nonneg (hψ0 _) (hκ0 _)

/-- **the density bound** -/
theorem density_lb {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (hm : ∀ a, 0 ≤ m a)
    (hBc : Continuous B) (hBs : HasCompactSupport B) (hB0 : ∀ α, 0 ≤ B α)
    (hκ : ∀ x, κ x = ∫ α, B α * Real.cos (2 * π * α * x)) (hκ0 : ∀ x, 0 ≤ κ x) (hκi : Integrable κ)
    (hκ1 : ∫ x, κ x = 1)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1)
    {W M : ℝ} (hM : 0 ≤ M) (hψI : ∀ y, -M ≤ y → y ≤ W + M → ψ y = 1) (hψpos : 0 < ∫ y, ψ y)
    (hx : ∀ a ∈ s, 0 ≤ x a ∧ x a ≤ W) :
    (∑ a ∈ s, m a) ^ 2 * (∫ t in (-M)..M, κ t) ^ 2 / ∫ y, ψ y ≤ ∫ α, B α * Ssq s m x α := by
  set N := ∑ a ∈ s, m a with hN
  set I := ∫ t in (-M)..M, κ t with hI
  set P := ∫ y, ψ y with hP
  set CS : ℝ → ℝ := fun α => ∑ a ∈ s, m a * Real.cos (2 * π * α * x a) with hCS
  set SS : ℝ → ℝ := fun α => ∑ a ∈ s, m a * Real.sin (2 * π * α * x a) with hSS
  have hCc := continuous_Cw hψc hψs
  have hSc := continuous_Sw hψc hψs
  have hCSc : Continuous CS := continuous_finsetSum _ fun a _ => by fun_prop
  have hSSc : Continuous SS := continuous_finsetSum _ fun a _ => by fun_prop
  have hint : ∀ F : ℝ → ℝ, Continuous F → Integrable (fun α => B α * F α) := fun F hF =>
    (hBc.mul hF).integrable_of_hasCompactSupport hBs.mul_right
  -- the three integrals
  set E := ∫ α, B α * Ssq s m x α with hE
  set X := ∫ α, B α * (CS α * Cw ψ α + SS α * Sw ψ α) with hX
  set Y := ∫ α, B α * (Cw ψ α ^ 2 + Sw ψ α ^ 2) with hY
  have hXeq : X = ∑ a ∈ s, m a * ∫ y, ψ y * κ (x a - y) := by
    rw [hX]
    have e : ∀ α, B α * (CS α * Cw ψ α + SS α * Sw ψ α)
        = ∑ a ∈ s, m a * (B α * (Real.cos (2 * π * α * x a) * Cw ψ α + Real.sin (2 * π * α * x a) * Sw ψ α)) := by
      intro α
      simp only [hCS, hSS, sum_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun a _ => (hint _ (by fun_prop)).const_mul (m a)]
    refine sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, cross_eq hBc hBs hψc hψs hκ]
  have hXge : N * I ≤ X := by
    rw [hXeq, hN, sum_mul]
    exact sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
      (cross_ge hψc hψ0 hψ1 hψI hκ0 hκi (hx a ha).1 (hx a ha).2) (hm a)
  have hYle : Y ≤ P := by
    rw [hY, quad_eq hBc hBs hψc hψs hκ]
    exact quad_le hψc hψs hψ0 hψ1 hκ0 hκi hκ1
  have hY0 : 0 ≤ Y := integral_nonneg fun α => mul_nonneg (hB0 α) (by positivity)
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by linarith) fun t _ => hκ0 t
  have hN0 : 0 ≤ N := sum_nonneg fun a _ => hm a
  -- positivity of ∫ B |S − λ ψ̂|²
  have hquad : ∀ l : ℝ, 0 ≤ E - 2 * l * X + l ^ 2 * Y := by
    intro l
    have hpt : ∀ α, B α * ((CS α - l * Cw ψ α) ^ 2 + (SS α - l * Sw ψ α) ^ 2)
        = B α * Ssq s m x α - 2 * l * (B α * (CS α * Cw ψ α + SS α * Sw ψ α))
          + l ^ 2 * (B α * (Cw ψ α ^ 2 + Sw ψ α ^ 2)) := by
      intro α; simp only [Ssq, hCS, hSS]; ring
    have h0 : 0 ≤ ∫ α, B α * ((CS α - l * Cw ψ α) ^ 2 + (SS α - l * Sw ψ α) ^ 2) :=
      integral_nonneg fun α => mul_nonneg (hB0 α) (by positivity)
    rw [integral_congr_ae (Eventually.of_forall hpt)] at h0
    have i1 : Integrable (fun α => B α * Ssq s m x α) := hint _ (by unfold Ssq; fun_prop)
    have i2 : Integrable (fun α => B α * (CS α * Cw ψ α + SS α * Sw ψ α)) := hint _ (by fun_prop)
    have i3 : Integrable (fun α => B α * (Cw ψ α ^ 2 + Sw ψ α ^ 2)) := hint _ (by fun_prop)
    have i12 : Integrable (fun α => B α * Ssq s m x α - 2 * l * (B α * (CS α * Cw ψ α + SS α * Sw ψ α))) :=
      i1.sub (i2.const_mul _)
    rw [integral_add i12 (i3.const_mul _), integral_sub i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul] at h0
    exact h0
  -- take `λ = X / P`
  have hl := hquad (X / P)
  have hXP : X ^ 2 / P * Y / P ≤ X ^ 2 / P := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hψpos).mpr hYle)
  have hmain : X ^ 2 / P ≤ E := by
    have : E - 2 * (X / P) * X + (X / P) ^ 2 * Y = E - 2 * (X ^ 2 / P) + X ^ 2 / P * Y / P := by
      field_simp
    rw [this] at hl
    linarith
  have hNI : (N * I) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (mul_nonneg hN0 hI0) hXge 2
  calc N ^ 2 * I ^ 2 / P = (N * I) ^ 2 / P := by ring
    _ ≤ X ^ 2 / P := div_le_div_of_nonneg_right hNI hψpos.le
    _ ≤ E := hmain

end Density

end AMW.DE

end
