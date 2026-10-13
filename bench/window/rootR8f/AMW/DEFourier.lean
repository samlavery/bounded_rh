import AMW.DEDefs
import AMW.Kernel
import Zeta23.Taper

/-! ###### AMW/DEFourier — the Fourier layer of the dip-certificate route (bridge-port)

* `integral_tri_cos`: `∫ tri(s) cos(ωs + φ) ds = cos φ · sinc(ω/2)²`; hence the tent pairs (`integral_tent_cos`)
  and the closed form of the certificate, `∫ ĝ(α) cos(2παu) dα = gPL c u` (`integral_ghat_cos`).
* `integral_qfAM_cos`: `wfunAM u = ∫ qfAM(α) cos(2παu) dα` — the band function is the Fourier transform of the pair
  weight (the convolution theorem for the indicator-cut profile `Vam`, which is integrable but not continuous).
* `energy_eq_integral`: for a finite weighted configuration and an integrable `F`,
  `Σ_{a,b} m_a m_b ∫ F(α) cos(2πα(x_a − x_b)) dα = ∫ F(α) |S(α)|² dα` with `|S|² = (Σ m cos)² + (Σ m sin)²`. ###### -/

noncomputable section

open Real MeasureTheory Finset Set

namespace AMW.DE

/-! ### The tent transform -/

theorem tri_eq_zero_of_not_mem {s : ℝ} (hs : s ∉ Icc (-1 : ℝ) 1) : tri s = 0 := by
  apply tri_eq_zero
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem hasDerivAt_right_tri (ω φ : ℝ) (hω : ω ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => (1 - s) * Real.sin (ω * s + φ) / ω - Real.cos (ω * s + φ) / ω ^ 2)
      ((1 - s) * Real.cos (ω * s + φ)) s := by
  have h1 : HasDerivAt (fun s => ω * s + φ) ω s := by
    simpa using ((hasDerivAt_id' s).const_mul ω).add_const φ
  have := ((((hasDerivAt_id' s).const_sub 1).mul h1.sin).div_const ω).sub (h1.cos.div_const (ω ^ 2))
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_left_tri (ω φ : ℝ) (hω : ω ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => (1 + s) * Real.sin (ω * s + φ) / ω + Real.cos (ω * s + φ) / ω ^ 2)
      ((1 + s) * Real.cos (ω * s + φ)) s := by
  have h1 : HasDerivAt (fun s => ω * s + φ) ω s := by
    simpa using ((hasDerivAt_id' s).const_mul ω).add_const φ
  have := ((((hasDerivAt_id' s).const_add 1).mul h1.sin).div_const ω).add (h1.cos.div_const (ω ^ 2))
  refine this.congr_deriv ?_
  field_simp
  ring

/-- **the tent transform**: `∫ tri(s) cos(ωs + φ) ds = cos φ · sinc(ω/2)²` -/
theorem integral_tri_cos (ω φ : ℝ) :
    ∫ s, tri s * Real.cos (ω * s + φ) = Real.cos φ * Real.sinc (ω / 2) ^ 2 := by
  have hcont : Continuous fun s => tri s * Real.cos (ω * s + φ) :=
    continuous_tri.mul (Real.continuous_cos.comp (by fun_prop))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-1 : ℝ) 1)
      (fun s hs => by rw [tri_eq_zero_of_not_mem hs, zero_mul]),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hL : ∫ s in (-1 : ℝ)..0, tri s * Real.cos (ω * s + φ) = ∫ s in (-1 : ℝ)..0, (1 + s) * Real.cos (ω * s + φ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    show tri s * Real.cos (ω * s + φ) = (1 + s) * Real.cos (ω * s + φ)
    rw [tri_of_abs_le (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]), abs_of_nonpos hs.2]
    ring
  have hR : ∫ s in (0 : ℝ)..1, tri s * Real.cos (ω * s + φ) = ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (ω * s + φ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    show tri s * Real.cos (ω * s + φ) = (1 - s) * Real.cos (ω * s + φ)
    rw [tri_of_abs_le (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]), abs_of_nonneg hs.1]
  rw [hL, hR]
  by_cases hω : ω = 0
  · have hl : ∀ s : ℝ, HasDerivAt (fun s => (s + s ^ 2 / 2) * Real.cos (ω * 0 + φ))
        ((1 + s) * Real.cos (ω * s + φ)) s := by
      intro s
      have := ((hasDerivAt_id' s).add ((hasDerivAt_pow 2 s).div_const 2)).mul_const (Real.cos (ω * 0 + φ))
      refine this.congr_deriv ?_
      rw [hω]; norm_num
    have hr : ∀ s : ℝ, HasDerivAt (fun s => (s - s ^ 2 / 2) * Real.cos (ω * 0 + φ))
        ((1 - s) * Real.cos (ω * s + φ)) s := by
      intro s
      have := ((hasDerivAt_id' s).sub ((hasDerivAt_pow 2 s).div_const 2)).mul_const (Real.cos (ω * 0 + φ))
      refine this.congr_deriv ?_
      rw [hω]; norm_num
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hl s)
        ((by fun_prop : Continuous fun s : ℝ => (1 + s) * Real.cos (ω * s + φ)).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hr s)
        ((by fun_prop : Continuous fun s : ℝ => (1 - s) * Real.cos (ω * s + φ)).intervalIntegrable _ _)]
    rw [hω]
    simp only [zero_mul, zero_add, zero_div, Real.sinc_zero, one_pow, mul_one]
    ring
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_left_tri ω φ hω s)
        ((by fun_prop : Continuous fun s : ℝ => (1 + s) * Real.cos (ω * s + φ)).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_right_tri ω φ hω s)
        ((by fun_prop : Continuous fun s : ℝ => (1 - s) * Real.cos (ω * s + φ)).intervalIntegrable _ _)]
    have hω2 : ω / 2 ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hω2]
    have e1 : Real.cos (ω * -1 + φ) = Real.cos φ * Real.cos ω + Real.sin φ * Real.sin ω := by
      rw [show ω * -1 + φ = φ - ω by ring, Real.cos_sub]
    have e2 : Real.cos (ω * 1 + φ) = Real.cos φ * Real.cos ω - Real.sin φ * Real.sin ω := by
      rw [show ω * 1 + φ = φ + ω by ring, Real.cos_add]
    have e3 : ω * 0 + φ = φ := by ring
    have hhalf : Real.cos ω = 1 - 2 * Real.sin (ω / 2) ^ 2 := by
      rw [show ω = 2 * (ω / 2) by ring, Real.cos_two_mul, Real.cos_sq']
      ring_nf
    rw [e1, e2, e3, hhalf]
    field_simp
    ring

/-- the shifted, dilated tent: `∫ tri(αD − k) cos(2παu) dα = D⁻¹ sinc(πu/D)² cos(2πku/D)` -/
theorem integral_tri_affine_cos {D : ℝ} (hD : 0 < D) (k u : ℝ) :
    ∫ α, tri (α * D - k) * Real.cos (2 * π * α * u)
      = D⁻¹ * Real.sinc (π * u / D) ^ 2 * Real.cos (2 * π * k * u / D) := by
  set ω : ℝ := 2 * π * u / D with hω
  set φ : ℝ := 2 * π * k * u / D with hφ
  set f : ℝ → ℝ := fun s => tri s * Real.cos (ω * s + φ) with hf
  have hpt : ∀ α, tri (α * D - k) * Real.cos (2 * π * α * u) = (fun β => f (β - k)) (α * D) := by
    intro α
    simp only [hf, hω, hφ]
    congr 2
    field_simp
    ring
  simp_rw [hpt]
  rw [Measure.integral_comp_mul_right (fun β => f (β - k)) D, integral_sub_right_eq_self f k,
    abs_of_pos (inv_pos.mpr hD), smul_eq_mul, hf, integral_tri_cos]
  rw [show ω / 2 = π * u / D by rw [hω]; ring]
  ring

theorem hasCompactSupport_tri_affine {D : ℝ} (hD : 0 < D) (k : ℝ) :
    HasCompactSupport (fun α => tri (α * D - k)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (k - 1) / D) (b := (k + 1) / D)) fun α hα => ?_
  apply tri_eq_zero_of_not_mem
  intro h
  apply hα
  rw [Set.mem_Icc] at h ⊢
  constructor
  · rw [div_le_iff₀ hD]; linarith [h.1]
  · rw [le_div_iff₀ hD]; linarith [h.2]

theorem integrable_tri_affine_cos {D : ℝ} (hD : 0 < D) (k u : ℝ) :
    Integrable (fun α => tri (α * D - k) * Real.cos (2 * π * α * u)) :=
  (continuous_tri.comp (by fun_prop) |>.mul (Real.continuous_cos.comp (by fun_prop))).integrable_of_hasCompactSupport
    ((hasCompactSupport_tri_affine hD k).mul_right)

/-- the tent pair transform -/
theorem integral_tent_cos {D : ℝ} (hD : 0 < D) (k : ℕ) (u : ℝ) :
    ∫ α, tent D k α * Real.cos (2 * π * α * u)
      = (if k = 0 then 1 else 2) * D⁻¹ * Real.sinc (π * u / D) ^ 2 * Real.cos (k * (2 * π * u / D)) := by
  unfold tent
  split_ifs with hk
  · subst hk
    have := integral_tri_affine_cos hD 0 u
    simp only [sub_zero, Nat.cast_zero, zero_mul, mul_zero, zero_div, Real.cos_zero, mul_one] at this ⊢
    rw [this]; ring
  · have e : ∀ α, (tri (α * D - k) + tri (α * D + k)) * Real.cos (2 * π * α * u)
        = tri (α * D - k) * Real.cos (2 * π * α * u) + tri (α * D - (-(k : ℝ))) * Real.cos (2 * π * α * u) := by
      intro α; rw [sub_neg_eq_add]; ring
    simp_rw [e]
    rw [integral_add (integrable_tri_affine_cos hD _ _) (integrable_tri_affine_cos hD _ _),
      integral_tri_affine_cos hD, integral_tri_affine_cos hD,
      show 2 * π * (-(k : ℝ)) * u / D = -(2 * π * k * u / D) by ring, Real.cos_neg,
      show (k : ℝ) * (2 * π * u / D) = 2 * π * k * u / D by ring]
    ring

theorem integrable_tent_cos {D : ℝ} (hD : 0 < D) (k : ℕ) (u : ℝ) :
    Integrable (fun α => tent D k α * Real.cos (2 * π * α * u)) := by
  unfold tent
  split_ifs
  · simpa using integrable_tri_affine_cos hD 0 u
  · simp_rw [add_mul]
    exact (integrable_tri_affine_cos hD _ _).add (by simpa using integrable_tri_affine_cos hD (-(k : ℝ)) u)

/-- **the certificate's transform in closed form**: `∫ ĝ(α) cos(2παu) dα = Dk sinc²(πDk·u) C(2πDk·u)` -/
theorem integral_ghat_cos (c : PLCert) (hD : 0 < c.DkInv) (u : ℝ) :
    ∫ α, ghat c α * Real.cos (2 * π * α * u) = gPL c u := by
  have hD' : (0 : ℝ) < c.DkInv := by exact_mod_cast hD
  set D : ℝ := (c.DkInv : ℝ) with hDdef
  set A : ℝ := D⁻¹ * Real.sinc (π * u / D) ^ 2 with hA
  set θ : ℝ := 2 * π * u / D with hθ
  have hpt : ∀ α, ghat c α * Real.cos (2 * π * α * u)
      = ∑ k ∈ range c.n, c.y k * (tent D k α * Real.cos (2 * π * α * u)) := by
    intro α
    unfold ghat
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k _ => (integrable_tent_cos hD' k u).const_mul (c.y k))]
  simp_rw [integral_const_mul, integral_tent_cos hD']
  have hg : gPL c u = A * certC c θ := by
    unfold gPL PLCert.dk
    rw [hA, hθ, ← hDdef]
    congr 1
    · rw [one_div, show π * D⁻¹ * u = π * u / D by ring]
    · rw [show 2 * π * (1 / D) * u = 2 * π * u / D by ring]
  rw [hg]
  unfold certC
  rcases Nat.eq_zero_or_pos c.n with hn | hn
  · rw [hn, range_zero, sum_empty, c.y_eq_zero (k := 0) (by omega)]; simp
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn, mul_add, zero_add]
    congr 1
    · simp only [if_true, Nat.cast_zero, zero_mul, Real.cos_zero]
      rw [hA]; ring
    · rw [mul_sum, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [if_neg (by have := (mem_Ico.mp hk).1; omega), hA]
      ring

/-! ### The band function is the transform of the pair weight -/

/-- the profile cut to the window -/
def Vam (u : ℝ) : ℝ := (Icc (-(1:ℝ)/2) (1/2)).indicator vAM u

theorem Vam_neg (u : ℝ) : Vam (-u) = Vam u := by
  unfold Vam
  by_cases hu : u ∈ Icc (-(1:ℝ)/2) (1/2)
  · have hu' : -u ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [indicator_of_mem hu, indicator_of_mem hu', vAM_even]
  · have hu' : -u ∉ Icc (-(1:ℝ)/2) (1/2) := fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_notMem hu, indicator_of_notMem hu']

theorem integrable_Vam : Integrable Vam :=
  (vAM_continuous.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem Vam_eq_MAM_sW (u : ℝ) : Vam u = MAM * sW 1 u := by
  unfold Vam sW
  by_cases hu : u ∈ Icc (-(1:ℝ)/2) (1/2)
  · have hu' : u ∈ Icc (-((1:ℝ)/2)) (1/2) := ⟨by linarith [hu.1], hu.2⟩
    rw [indicator_of_mem hu, indicator_of_mem hu']
    simp only [hW, div_one]
    field_simp [MAM]
  · have hu' : u ∉ Icc (-((1:ℝ)/2)) (1/2) := fun h => hu ⟨by linarith [h.1], h.2⟩
    rw [indicator_of_notMem hu, indicator_of_notMem hu', mul_zero]

/-- the autocorrelation of the cut profile is the band function times `(∫vAM)²` -/
theorem autocorr_Vam (α : ℝ) : Zeta23.Params.autocorr Vam α = qfAM α * Ivam ^ 2 := by
  have hI : Ivam ≠ 0 := by rw [Ivam, ← KfunAM_zero]; exact KfunAM_zero_pos.ne'
  -- reduce to `α ≥ 0`
  wlog hα : 0 ≤ α generalizing α
  · rw [← Zeta23.Taper.autocorr_neg, this (-α) (by linarith), qfAM_neg]
  unfold qfAM
  rw [abs_of_nonneg hα]
  split_ifs with h1
  · rw [div_mul_cancel₀ _ (pow_ne_zero 2 hI)]
    unfold Zeta23.Params.autocorr
    simp_rw [Vam_eq_MAM_sW]
    have := sharp_overlap (L := 1) one_pos hα h1
    simp only [one_mul, div_one] at this
    have e : ∀ u, MAM * sW 1 u * (MAM * sW 1 (u + α)) = MAM ^ 2 * (sW 1 u * sW 1 (u + α)) := fun u => by ring
    simp_rw [e]
    rw [integral_const_mul, this]
    field_simp [MAM]
  · rw [zero_mul]
    unfold Zeta23.Params.autocorr
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.zero_apply]
    unfold Vam
    by_cases hu : u ∈ Icc (-(1:ℝ)/2) (1/2)
    · have hu' : u + α ∉ Icc (-(1:ℝ)/2) (1/2) := fun h => h1 (by linarith [hu.1, h.2])
      rw [indicator_of_notMem hu', mul_zero]
    · rw [indicator_of_notMem hu, zero_mul]

theorem integrable_autocorr_Vam : Integrable (Zeta23.Params.autocorr Vam) := by
  have hiC : Integrable (fun u => (Vam u : ℂ)) := integrable_Vam.ofReal
  have : Integrable (fun y => (Zeta23.Params.autocorr Vam y : ℂ)) := by
    rw [Zeta23.Taper.ofReal_autocorr_eq_convolution Vam_neg]
    exact hiC.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hiC
  simpa using this.re

/-- the real cosine transform of an even integrable real function is its paper transform -/
theorem paperFT_eq_integral_cos {v : ℝ → ℝ} (hv : ∀ u, v (-u) = v u) (hi : Integrable v) (r : ℝ) :
    Zeta23.paperFT (fun u => (v u : ℂ)) r = ((∫ u, v u * Real.cos (r * u) : ℝ) : ℂ) := by
  rw [Zeta23.Taper.paperFT_ofReal_eq_re hv r]
  congr 1
  have hgi : Integrable (fun u : ℝ => (v u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * u)) := by
    refine (hi.ofReal (𝕜 := ℂ)).norm.mono' ((hi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * u)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, show Complex.I * (r : ℂ) * u = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  rw [Zeta23.paperFT_def, ← Zeta23.integral_re_C hgi]
  congr 1 with u
  rw [show Complex.I * (r : ℂ) * u = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- the convolution theorem for an even integrable real function (no continuity) -/
theorem paperFT_autocorr_of_integrable {v : ℝ → ℝ} (hv : ∀ u, v (-u) = v u) (hi : Integrable v) (r : ℝ) :
    Zeta23.paperFT (fun y => (Zeta23.Params.autocorr v y : ℂ)) r = (Zeta23.paperFT (fun u => (v u : ℂ)) r) ^ 2 := by
  have hiC : Integrable (fun u => (v u : ℂ)) := hi.ofReal
  rw [Zeta23.Taper.ofReal_autocorr_eq_convolution hv, Zeta23.paperFT_ofReal_eq_fourier,
    Zeta23.paperFT_ofReal_eq_fourier, Real.fourier_mul_convolution_eq hiC hiC, sq]

theorem KfunAM_eq_integral_Vam (x : ℝ) : KfunAM x = ∫ t, Vam t * Real.cos (2 * π * x * t) := by
  unfold KfunAM Vam
  have : ∀ t, (Icc (-(1:ℝ)/2) (1/2)).indicator vAM t * Real.cos (2 * π * x * t)
      = (Icc (-(1:ℝ)/2) (1/2)).indicator (fun t => vAM t * Real.cos (2 * π * x * t)) t := by
    intro t
    by_cases ht : t ∈ Icc (-(1:ℝ)/2) (1/2)
    · rw [indicator_of_mem ht, indicator_of_mem ht]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  simp_rw [this]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

/-- **the band function is the transform of the pair weight**: `wfunAM u = ∫ qfAM(α) cos(2παu) dα` -/
theorem integral_qfAM_cos (u : ℝ) : ∫ α, qfAM α * Real.cos (2 * π * α * u) = wfunAM u := by
  have hI : Ivam ≠ 0 := by rw [Ivam, ← KfunAM_zero]; exact KfunAM_zero_pos.ne'
  have h1 := paperFT_autocorr_of_integrable Vam_neg integrable_Vam (2 * π * u)
  rw [paperFT_eq_integral_cos (fun y => Zeta23.Taper.autocorr_neg Vam y) integrable_autocorr_Vam,
    paperFT_eq_integral_cos Vam_neg integrable_Vam] at h1
  have h2 : ∫ y, Zeta23.Params.autocorr Vam y * Real.cos (2 * π * u * y)
      = (∫ t, Vam t * Real.cos (2 * π * u * t)) ^ 2 := by exact_mod_cast h1
  rw [← KfunAM_eq_integral_Vam] at h2
  simp_rw [autocorr_Vam] at h2
  unfold wfunAM kfunAM
  rw [KfunAM_zero, ← Ivam, div_pow, ← h2, ← integral_div]
  congr 1 with α
  rw [show 2 * π * α * u = 2 * π * u * α by ring]
  field_simp

theorem integrable_qfAM_cos (u : ℝ) : Integrable (fun α => qfAM α * Real.cos (2 * π * α * u)) := by
  have hI : Ivam ≠ 0 := by rw [Ivam, ← KfunAM_zero]; exact KfunAM_zero_pos.ne'
  have hq : qfAM = fun α => Zeta23.Params.autocorr Vam α / Ivam ^ 2 := by
    funext α; rw [autocorr_Vam]; field_simp
  rw [hq]
  refine ((integrable_autocorr_Vam.div_const _).mul_bdd (c := 1) ?_ ?_)
  · exact (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun α => by simpa using Real.abs_cos_le_one _

theorem integrable_ghat_cos (c : PLCert) (hD : 0 < c.DkInv) (u : ℝ) :
    Integrable (fun α => ghat c α * Real.cos (2 * π * α * u)) := by
  have hD' : (0 : ℝ) < c.DkInv := by exact_mod_cast hD
  have hpt : (fun α => ghat c α * Real.cos (2 * π * α * u))
      = fun α => ∑ k ∈ range c.n, c.y k * (tent (c.DkInv : ℝ) k α * Real.cos (2 * π * α * u)) := by
    funext α
    unfold ghat
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [hpt]
  exact integrable_finsetSum _ fun k _ => (integrable_tent_cos hD' k u).const_mul (c.y k)

/-! ### The energy identity -/

/-- `|S(α)|²` for a finite weighted configuration -/
def Ssq {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (α : ℝ) : ℝ :=
  (∑ a ∈ s, m a * Real.cos (2 * π * α * x a)) ^ 2 + (∑ a ∈ s, m a * Real.sin (2 * π * α * x a)) ^ 2

theorem Ssq_nonneg {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (α : ℝ) : 0 ≤ Ssq s m x α := by
  unfold Ssq; positivity

theorem Ssq_eq {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (α : ℝ) :
    Ssq s m x α = ∑ a ∈ s, ∑ b ∈ s, m a * m b * Real.cos (2 * π * α * (x a - x b)) := by
  unfold Ssq
  rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [show 2 * π * α * (x a - x b) = 2 * π * α * x a - 2 * π * α * x b by ring, Real.cos_sub]
  ring

/-- **the energy identity** -/
theorem energy_eq_integral {ι : Type*} (s : Finset ι) (m x : ι → ℝ) {F : ℝ → ℝ}
    (hF : ∀ u, Integrable (fun α => F α * Real.cos (2 * π * α * u))) :
    ∑ a ∈ s, ∑ b ∈ s, m a * m b * ∫ α, F α * Real.cos (2 * π * α * (x a - x b))
      = ∫ α, F α * Ssq s m x α := by
  have hint : ∀ a b, Integrable (fun α => m a * m b * (F α * Real.cos (2 * π * α * (x a - x b)))) :=
    fun a b => (hF (x a - x b)).const_mul (m a * m b)
  have hpt : ∀ α, F α * ∑ a ∈ s, ∑ b ∈ s, m a * m b * Real.cos (2 * π * α * (x a - x b))
      = ∑ a ∈ s, ∑ b ∈ s, m a * m b * (F α * Real.cos (2 * π * α * (x a - x b))) := by
    intro α
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  simp_rw [Ssq_eq, hpt]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  refine sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hint a b]
  refine sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

end AMW.DE

end
