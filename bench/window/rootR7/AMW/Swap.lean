import AMW.Moments

/-!
# AMW/Swap — the overlap moment is the `|s − t|` energy (stage E2)

For continuous `q` with `|q| ≤ B`:
  `2 ∫₀¹ (∫_{-½}^{½-r} q(s) q(s+r) ds) · r dr = ∫_{-½}^{½} q(s) (∫_{-½}^{½} |s − t| q(t) dt) ds`.
Proof on the line, with `e = 1_{[-½,½]} q`: substitute `t = s + r` in the inner integral, swap the order
(Fubini; the integrand is bounded and supported in `[-½,½] × [-1,1]`), use that `r ↦ ∫ e(s)e(s+r) ds` is even
and vanishes for `r > 1`, and fold `∫_ℝ |r| A(r) dr = 2∫₀¹ r A(r) dr`.
Consequence: `JInf · MAM² = ∫ vAM(s) K(s) ds` with `K(s) = ∫ |s − t| vAM(t) dt`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace AMW

section Swap

variable {q : ℝ → ℝ} {B : ℝ}

/-- the extension of `q` by zero off `[-1/2, 1/2]`. -/
def ext0 (q : ℝ → ℝ) : ℝ → ℝ := (Icc (-(1:ℝ)/2) (1/2)).indicator q

theorem ext0_measurable (hq : Continuous q) : Measurable (ext0 q) :=
  hq.measurable.indicator measurableSet_Icc

theorem abs_ext0_le (hB : ∀ s, |q s| ≤ B) (s : ℝ) : |ext0 q s| ≤ B := by
  unfold ext0
  by_cases h : s ∈ Icc (-(1:ℝ)/2) (1/2)
  · rw [Set.indicator_of_mem h]; exact hB s
  · rw [Set.indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hB s)

theorem intervalIntegral_eq_indicator (f : ℝ → ℝ) :
    ∫ s in (-(1:ℝ)/2)..(1/2), f s = ∫ s, (Icc (-(1:ℝ)/2) (1/2)).indicator f s := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

/-- the autocorrelation of the extension. -/
def acor (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s, ext0 q s * ext0 q (s + r)

theorem acor_neg (r : ℝ) : acor q (-r) = acor q r := by
  unfold acor
  have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun x => ext0 q (x + r) * ext0 q x) r
  simp only [sub_add_cancel] at h
  calc ∫ s, ext0 q s * ext0 q (s + -r) = ∫ x, ext0 q x * ext0 q (x - r) := by
        simp only [sub_eq_add_neg]
    _ = ∫ x, ext0 q (x + r) * ext0 q x := h
    _ = ∫ s, ext0 q s * ext0 q (s + r) := by
        congr 1; funext s; ring

theorem acor_eq_zero {r : ℝ} (hr : 1 < r) : acor q r = 0 := by
  unfold acor
  have : ∀ s, ext0 q s * ext0 q (s + r) = 0 := by
    intro s
    unfold ext0
    by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2)
    · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r), mul_zero]
      intro h; linarith [hs.1, h.2]
    · rw [Set.indicator_of_notMem hs, zero_mul]
  simp only [this, integral_zero]

/-- on `[0, 1]` the autocorrelation is the overlap integral. -/
theorem acor_eq_overlap {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    acor q r = ∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r) := by
  unfold acor
  have hind : ∀ s : ℝ, ext0 q s * ext0 q (s + r)
      = (Icc (-(1:ℝ)/2) (1/2 - r)).indicator (fun s => q s * q (s + r)) s := by
    intro s
    unfold ext0
    by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2 - r)
    · have hs1 : s ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨hs.1, by linarith [hs.2]⟩
      have hs2 : s + r ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs1, Set.indicator_of_mem hs2]
    · rw [Set.indicator_of_notMem hs]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1:ℝ)/2 ≤ 1/2 - r)]

/-- the integrand of the double integral is integrable on the plane. -/
theorem integrable_swap (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
    Integrable (fun p : ℝ × ℝ => ext0 q p.1 * (|p.2| * ext0 q (p.1 + p.2)))
      (volume.prod volume) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set K : Set (ℝ × ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-1:ℝ) 1 with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hKf : (volume.prod volume) K ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hg : Integrable (K.indicator (fun _ => B ^ 2)) (volume.prod volume) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hKf)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((ext0_measurable hq).comp measurable_fst).mul
      ((continuous_abs.measurable.comp measurable_snd).mul
        ((ext0_measurable hq).comp (measurable_fst.add measurable_snd))) |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    by_cases h1 : p.1 ∈ Icc (-(1:ℝ)/2) (1/2)
    · by_cases h2 : p.1 + p.2 ∈ Icc (-(1:ℝ)/2) (1/2)
      · have hpK : p ∈ K := ⟨h1, by constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
        rw [Set.indicator_of_mem hpK, abs_mul, abs_mul, abs_abs]
        have hr : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
          by linarith [h1.1, h1.2, h2.1, h2.2]⟩
        have e1 := abs_ext0_le hB p.1 (q := q)
        have e2 := abs_ext0_le hB (p.1 + p.2) (q := q)
        calc |ext0 q p.1| * (|p.2| * |ext0 q (p.1 + p.2)|) ≤ B * (1 * B) := by
              apply mul_le_mul e1 (mul_le_mul hr e2 (abs_nonneg _) zero_le_one)
                (by positivity) hB0
          _ = B ^ 2 := by ring
      · have : ext0 q (p.1 + p.2) = 0 := Set.indicator_of_notMem h2 _
        rw [this, mul_zero, mul_zero, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p
    · have : ext0 q p.1 = 0 := Set.indicator_of_notMem h1 _
      rw [this, zero_mul, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p

/-- **The swap identity.** -/
theorem swap_identity (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
    2 * ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
      = ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t := by
  -- right side on the line
  have hR1 : ∀ s, ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t = ∫ t, |s - t| * ext0 q t := by
    intro s
    rw [intervalIntegral_eq_indicator]
    congr 1; funext t
    unfold ext0
    exact Set.indicator_mul_right _ (fun t => |s - t|) q
  have hR2 : ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t
      = ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r)) := by
    simp_rw [hR1]
    rw [intervalIntegral_eq_indicator]
    congr 1; funext s
    have e1 : (Icc (-(1:ℝ)/2) (1/2)).indicator (fun s => q s * ∫ t, |s - t| * ext0 q t) s
        = ext0 q s * ∫ t, |s - t| * ext0 q t := by
      unfold ext0
      exact Set.indicator_mul_left _ q (fun s => ∫ t, |s - t| * ext0 q t)
    rw [e1, ← integral_const_mul]
    have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
      (fun t => ext0 q s * (|s - t| * ext0 q t)) s
    rw [← h]
    congr 1; funext r
    rw [show s - (s + r) = -r by ring, abs_neg]
  -- swap
  have hS : ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r))
      = ∫ r, |r| * acor q r := by
    rw [MeasureTheory.integral_integral_swap (integrable_swap hq hB)]
    congr 1; funext r
    unfold acor
    rw [← integral_const_mul]
    congr 1; funext s
    ring
  -- fold the even function
  have hE : ∫ r, |r| * acor q r = 2 * ∫ r in Ioi 0, r * acor q r := by
    have e : (fun r => |r| * acor q r) = fun r => (fun x => x * acor q x) |r| := by
      funext r
      simp only
      rcases le_or_gt 0 r with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, acor_neg]
    rw [e]
    exact integral_comp_abs (f := fun x => x * acor q x)
  have hI : ∫ r in Ioi 0, r * acor q r = ∫ r in (0:ℝ)..1, r * acor q r := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
      (f := fun r => r * acor q r) measurableSet_Ioi
      (Ioc_subset_Ioi_self : Ioc (0:ℝ) 1 ⊆ Ioi 0) ?_)
    intro x hx
    have hx1 : 1 < x := by
      rcases hx with ⟨hx0, hx1⟩
      simp only [mem_Ioc, not_and_or, not_le] at hx1
      rcases hx1 with h | h
      · exact absurd (mem_Ioi.mp hx0) h
      · exact h
    rw [acor_eq_zero hx1, mul_zero]
  have hO : ∫ r in (0:ℝ)..1, r * acor q r
      = ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    show r * acor q r = (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
    rw [acor_eq_overlap hr.1 hr.2, mul_comm]
  rw [hR2, hS, hE, hI, hO]

end Swap

/-- **`JInf` as an energy**: `JInf·MAM² = ∫_{-½}^{½} vAM(s) ∫_{-½}^{½} |s−t| vAM(t) dt ds`. -/
theorem JInf_eq_energy :
    JInf * MAM ^ 2
      = ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t := by
  rw [← swap_identity vAM_continuous abs_vAM_le]
  unfold JInf vConvAM
  have h := MAM_pos
  field_simp

end AMW
