import AMW.DEDensity
import Zeta23.Defs.Profile

/-! ###### AMW/DECert — the dip certificate on finite real configurations (bridge-port)

For a piecewise-linear certificate `c` with `C ≥ 0` (`CertGNonneg`, so `g = gPL c ≥ 0`) and `ĝ ≤ qf`
(`CertHNonneg`, so `ĥ = qf − ĝ ≥ 0`), every finite configuration of weights `m_a ≥ 0` at points of `[0, W]` has
  `(ĥ(0) − ε) N²/(W + R) + g(0) Σ m_a² ≤ Σ_{a,b} m_a m_b wfunAM(x_a − x_b)`   (`cert_T_free`),
`ĥ(0) = qfAM 0 − y₀`, `g(0) = gPL c 0`, with `R` depending only on `ε`.  The off-diagonal `g` terms are dropped
(`g ≥ 0`); the `ĥ` part is bounded below by its density term (`DEDensity.density_lb`) through the positive-definite
minorant `B = A_φ/A_φ(0)` of a narrow Zeta23 taper (`taperB`, whose `x`-side kernel `φ̂(2πx)²/A_φ(0)` has integral
`1` by Plancherel). ###### -/

noncomputable section

open Real MeasureTheory Finset Set Filter Topology
open Zeta23

namespace AMW.DE

/-! ### The taper minorant -/

section TaperKernel

variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Aphi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {y : ℝ} (hy : L ≤ |y|) :
    Taper.Aphi ϱ L w y = 0 := by
  unfold Taper.Aphi Params.autocorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  simp only [Pi.zero_apply]
  by_cases hu : L / 2 ≤ |u|
  · rw [Taper.phi_eq_zero hϱ hw hu, zero_mul]
  · rw [Taper.phi_eq_zero hϱ hw (u := u + y), mul_zero]
    push Not at hu
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h] at hy
      rw [abs_lt] at hu
      calc L / 2 ≤ u + y := by linarith
        _ ≤ |u + y| := le_abs_self _
    · rw [abs_of_nonpos h] at hy
      rw [abs_lt] at hu
      calc L / 2 ≤ -(u + y) := by linarith
        _ ≤ |u + y| := neg_le_abs _

theorem Aphi_zero_pos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) : 0 < Taper.Aphi ϱ L w 0 := by
  unfold Taper.Aphi Params.autocorr
  simp only [add_zero]
  have hc := Taper.phi_continuous hϱ hw hwL
  refine (hc.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (Taper.phi_hasCompactSupport hϱ hw).mul_right (fun u => mul_nonneg (Taper.phi_nonneg hϱ u)
      (Taper.phi_nonneg hϱ u)) (x := 0) ?_
  rw [Taper.phi_eq_one hϱ hw (by rw [abs_zero]; linarith)]
  norm_num

theorem Aphi_nonneg (hϱ : TaperProfile ϱ) (y : ℝ) : 0 ≤ Taper.Aphi ϱ L w y :=
  integral_nonneg fun u => mul_nonneg (Taper.phi_nonneg hϱ u) (Taper.phi_nonneg hϱ _)

theorem continuous_Aphi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (Taper.Aphi ϱ L w) :=
  Taper.autocorr_continuous_of_even Taper.phi_even (Taper.phi_continuous hϱ hw hwL)
    (Taper.phi_hasCompactSupport hϱ hw)

theorem integrable_Aphi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (Taper.Aphi ϱ L w) :=
  Taper.autocorr_integrable_of_even Taper.phi_even (Taper.phi_continuous hϱ hw hwL)
    (Taper.phi_hasCompactSupport hϱ hw)

theorem Aphi_le_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Taper.Aphi ϱ L w y ≤ Taper.Aphi ϱ L w 0 := by
  have h1 := Taper.integral_phiHatR_sq_mul_cos hϱ hw hwL y
  have h0 := Taper.integral_phiHatR_sq_mul_cos hϱ hw hwL 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  have hi := Taper.integrable_phiHatR_sq hϱ hw hwL
  have hle : ∫ r, Taper.phiHatR ϱ L w r ^ 2 * Real.cos (r * y) ≤ ∫ r, Taper.phiHatR ϱ L w r ^ 2 := by
    refine integral_mono ?_ hi fun r => mul_le_of_le_one_right (sq_nonneg _) (Real.cos_le_one _)
    exact hi.mul_bdd (c := 1) (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hπ : 0 < 2 * π := by positivity
  nlinarith

/-- the `x`-side transform of `A_φ`: `∫ A_φ(α) cos(2παx) dα = φ̂(2πx)²` -/
theorem integral_Aphi_cos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (x : ℝ) :
    ∫ α, Taper.Aphi ϱ L w α * Real.cos (2 * π * α * x) = Taper.phiHatR ϱ L w (2 * π * x) ^ 2 := by
  have h := Taper.phiHatR_sq_eq hϱ hw hwL (2 * π * x)
  rw [paperFT_eq_integral_cos (v := Taper.Aphi ϱ L w) (fun y => Taper.autocorr_neg _ y)
    (integrable_Aphi hϱ hw hwL)] at h
  have h' : Taper.phiHatR ϱ L w (2 * π * x) ^ 2 = ∫ u, Taper.Aphi ϱ L w u * Real.cos (2 * π * x * u) := by
    exact_mod_cast h
  rw [h']
  congr 1 with α
  rw [show 2 * π * α * x = 2 * π * x * α by ring]

theorem integral_phiHatR_sq_scaled (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ x, Taper.phiHatR ϱ L w (2 * π * x) ^ 2 = Taper.Aphi ϱ L w 0 := by
  have h := Measure.integral_comp_mul_left (fun r => Taper.phiHatR ϱ L w r ^ 2) (2 * π)
  rw [h, Taper.integral_phiHatR_sq hϱ hw hwL, Taper.Aphi_zero hϱ hw hwL, abs_of_pos (by positivity),
    smul_eq_mul]
  field_simp

end TaperKernel

/-! ### The trapezoid comparison weight -/

/-- `1` on `[−M, W + M]`, `0` off `[−2M, W + 2M]`, linear between -/
def trap (W M y : ℝ) : ℝ := max 0 (min 1 (min ((y + 2 * M) / M) ((W + 2 * M - y) / M)))

theorem trap_nonneg (W M y : ℝ) : 0 ≤ trap W M y := le_max_left _ _

theorem trap_le_one (W M y : ℝ) : trap W M y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_trap (W M : ℝ) : Continuous (trap W M) := by
  unfold trap; fun_prop

theorem trap_eq_one {W M y : ℝ} (hM : 0 < M) (h1 : -M ≤ y) (h2 : y ≤ W + M) : trap W M y = 1 := by
  unfold trap
  have a : 1 ≤ (y + 2 * M) / M := by rw [le_div_iff₀ hM]; linarith
  have b : 1 ≤ (W + 2 * M - y) / M := by rw [le_div_iff₀ hM]; linarith
  rw [min_eq_left (le_min a b), max_eq_right zero_le_one]

theorem trap_eq_zero {W M y : ℝ} (hM : 0 < M) (h : y ∉ Icc (-2 * M) (W + 2 * M)) : trap W M y = 0 := by
  unfold trap
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  apply max_eq_left
  rcases h with h | h
  · have : (y + 2 * M) / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
    exact (min_le_right _ _).trans ((min_le_left _ _).trans this)
  · have : (W + 2 * M - y) / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
    exact (min_le_right _ _).trans ((min_le_right _ _).trans this)

theorem hasCompactSupport_trap {W M : ℝ} (hM : 0 < M) : HasCompactSupport (trap W M) :=
  HasCompactSupport.intro (isCompact_Icc (a := -2 * M) (b := W + 2 * M)) fun y hy => trap_eq_zero hM hy

theorem integral_trap_le {W M : ℝ} (hM : 0 < M) (hW : 0 ≤ W) : ∫ y, trap W M y ≤ W + 4 * M := by
  have hle : ∀ y, trap W M y ≤ (Icc (-2 * M) (W + 2 * M)).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ Icc (-2 * M) (W + 2 * M)
    · rw [indicator_of_mem hy]; exact trap_le_one W M y
    · rw [indicator_of_notMem hy, trap_eq_zero hM hy]
  calc ∫ y, trap W M y ≤ ∫ y, (Icc (-2 * M) (W + 2 * M)).indicator (fun _ => (1 : ℝ)) y :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => trap_nonneg W M y)
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
          (Eventually.of_forall hle)
    _ = W + 4 * M := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
          Real.volume_real_Icc_of_le (by linarith)]
        ring

theorem integral_trap_pos {W M : ℝ} (hM : 0 < M) (hW : 0 ≤ W) : 0 < ∫ y, trap W M y :=
  (continuous_trap W M).integral_pos_of_hasCompactSupport_nonneg_nonzero (hasCompactSupport_trap hM)
    (fun y => trap_nonneg W M y) (x := 0) (by rw [trap_eq_one hM (by linarith) (by linarith)]; norm_num)

/-! ### Certificate facts -/

theorem continuousAt_qfAM_zero : ContinuousAt qfAM 0 := by
  have hc : Continuous fun α : ℝ => vConvAM |α| / Ivam ^ 2 :=
    (continuous_vConvAM.comp continuous_abs).div_const _
  refine hc.continuousAt.congr ?_
  have : ∀ᶠ α in 𝓝 (0 : ℝ), |α| < 1 := by
    have := (continuous_abs (G := ℝ)).continuousAt (x := 0)
    simpa using this.eventually (gt_mem_nhds (show |(0 : ℝ)| < 1 by norm_num))
  filter_upwards [this] with α hα
  unfold qfAM
  rw [if_pos hα.le]

theorem ghat_zero (c : PLCert) (hD : 0 < c.DkInv) : ghat c 0 = c.y 0 := by
  rw [ghat_seg c hD 0 (by simp) (by simp)]
  simp

theorem gPL_nonneg (c : PLCert) (hG : CertGNonneg c) (u : ℝ) : 0 ≤ gPL c u := by
  unfold gPL PLCert.dk
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (hG _)

theorem ghat_le_qfAM (c : PLCert) (hH : CertHNonneg c) (α : ℝ) : ghat c α ≤ qfAM α := by
  rcases le_total 0 α with h | h
  · exact hH α h
  · have := hH (-α) (by linarith)
    rwa [ghat_neg, qfAM_neg] at this

theorem integrable_mul_Ssq {ι : Type*} (s : Finset ι) (m x : ι → ℝ) {F : ℝ → ℝ}
    (hF : ∀ u, Integrable (fun α => F α * Real.cos (2 * π * α * u))) :
    Integrable (fun α => F α * Ssq s m x α) := by
  have e : (fun α => F α * Ssq s m x α)
      = fun α => ∑ a ∈ s, ∑ b ∈ s, m a * m b * (F α * Real.cos (2 * π * α * (x a - x b))) := by
    funext α
    rw [Ssq_eq, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hF _).const_mul _

/-! ### The theorem -/

/-- **the dip certificate on finite real configurations** -/
theorem cert_T_free (c : PLCert) (hD : 0 < c.DkInv) (hG : CertGNonneg c) (hH : CertHNonneg c) :
    ∀ ε > 0, ∃ R > 0, ∀ (ι : Type) (s : Finset ι) (m x : ι → ℝ) (W : ℝ), 0 ≤ W → (∀ a, 0 ≤ m a) →
      (∀ a ∈ s, 0 ≤ x a ∧ x a ≤ W) →
      (qfAM 0 - c.y 0 - ε) * (∑ a ∈ s, m a) ^ 2 / (W + R) + gPL c 0 * ∑ a ∈ s, m a ^ 2
        ≤ ∑ a ∈ s, ∑ b ∈ s, m a * m b * wfunAM (x a - x b) := by
  intro ε hε
  set h0 := qfAM 0 - c.y 0 with hh0
  set F : ℝ → ℝ := fun α => qfAM α - ghat c α with hFdef
  have hF0 : F 0 = h0 := by simp only [hFdef, ghat_zero c hD, hh0]
  have hFnn : ∀ α, 0 ≤ F α := fun α => sub_nonneg.mpr (ghat_le_qfAM c hH α)
  have hFc : ContinuousAt F 0 := continuousAt_qfAM_zero.sub (continuous_ghat c).continuousAt
  obtain ⟨L₀, hL₀, hL₀F⟩ := Metric.continuousAt_iff.mp hFc (ε / 2) (by positivity)
  -- the taper minorant, supported in `|α| < L₀`
  set L : ℝ := L₀ / 2 with hL
  set w : ℝ := L / 4 with hw
  have hLpos : 0 < L := by positivity
  have hwpos : 0 < w := by positivity
  have hwL : 2 * w ≤ L := by rw [hw]; linarith
  have hϱ := taperProfile_stdProfile
  set A0 := Taper.Aphi stdProfile L w 0 with hA0
  have hA0 : 0 < A0 := Aphi_zero_pos hϱ hwpos hwL
  set B : ℝ → ℝ := fun α => Taper.Aphi stdProfile L w α / A0 with hB
  set κ : ℝ → ℝ := fun x => Taper.phiHatR stdProfile L w (2 * π * x) ^ 2 / A0 with hκdef
  have hBc : Continuous B := (continuous_Aphi hϱ hwpos hwL).div_const _
  have hBz : ∀ α, L ≤ |α| → B α = 0 := fun α h => by simp only [hB, Aphi_eq_zero hϱ hwpos h, zero_div]
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun α hα => hBz α ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hα
    rcases hα with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hB0 : ∀ α, 0 ≤ B α := fun α => div_nonneg (Aphi_nonneg hϱ α) hA0.le
  have hB1 : ∀ α, B α ≤ 1 := fun α => (div_le_one hA0).mpr (Aphi_le_zero hϱ hwpos hwL α)
  have hκ : ∀ x, κ x = ∫ α, B α * Real.cos (2 * π * α * x) := by
    intro x
    simp only [hκdef, hB]
    rw [← integral_Aphi_cos hϱ hwpos hwL x, ← integral_div]
    congr 1 with α
    ring
  have hκ0 : ∀ x, 0 ≤ κ x := fun x => div_nonneg (sq_nonneg _) hA0.le
  have hκi : Integrable κ :=
    ((Taper.integrable_phiHatR_sq hϱ hwpos hwL).comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).div_const _
  have hκ1 : ∫ x, κ x = 1 := by
    simp only [hκdef]
    rw [integral_div, integral_phiHatR_sq_scaled hϱ hwpos hwL, div_self hA0.ne']
  -- the pointwise minorant `F ≥ (h0 − ε/2) B`
  have hFB : ∀ α, (h0 - ε / 2) * B α ≤ F α := by
    intro α
    by_cases hα : |α| < L₀
    · have hd := hL₀F (by rw [Real.dist_eq, sub_zero]; exact hα)
      rw [Real.dist_eq, hF0] at hd
      have hFα : h0 - ε / 2 ≤ F α := by linarith [(abs_lt.mp hd).1]
      by_cases hs : 0 ≤ h0 - ε / 2
      · exact (mul_le_of_le_one_right hs (hB1 α)).trans hFα
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hB0 α)).trans (hFnn α)
    · rw [hBz α (by linarith), mul_zero]; exact hFnn α
  -- the window `M`
  have hItend : Tendsto (fun M : ℝ => (h0 - ε / 2) * (∫ t in (-M)..M, κ t) ^ 2) atTop
      (𝓝 ((h0 - ε / 2) * 1 ^ 2)) := by
    have := intervalIntegral_tendsto_integral hκi tendsto_neg_atTop_atBot tendsto_id
    rw [hκ1] at this
    exact (this.pow 2).const_mul _
  rw [one_pow, mul_one] at hItend
  obtain ⟨M, hMI, hM1⟩ := ((hItend.eventually (eventually_ge_nhds (by linarith : h0 - ε < h0 - ε / 2))).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have hMpos : 0 < M := by linarith
  refine ⟨4 * M, by positivity, fun ι s m x W hW hm hx => ?_⟩
  set N := ∑ a ∈ s, m a with hN
  -- the energy and the certificate part
  have hE : ∑ a ∈ s, ∑ b ∈ s, m a * m b * wfunAM (x a - x b) = ∫ α, qfAM α * Ssq s m x α := by
    rw [← energy_eq_integral s m x integrable_qfAM_cos]
    simp_rw [integral_qfAM_cos]
  have hGeq : ∑ a ∈ s, ∑ b ∈ s, m a * m b * gPL c (x a - x b) = ∫ α, ghat c α * Ssq s m x α := by
    rw [← energy_eq_integral s m x (integrable_ghat_cos c hD)]
    simp_rw [integral_ghat_cos c hD]
  have iq := integrable_mul_Ssq s m x integrable_qfAM_cos
  have ig := integrable_mul_Ssq s m x (integrable_ghat_cos c hD)
  have iF : Integrable (fun α => F α * Ssq s m x α) := by
    refine (iq.sub ig).congr (Eventually.of_forall fun α => ?_)
    simp only [hFdef, Pi.sub_apply]
    ring
  have hsplit : ∫ α, qfAM α * Ssq s m x α = (∫ α, ghat c α * Ssq s m x α) + ∫ α, F α * Ssq s m x α :=
    (integral_congr_ae (Eventually.of_forall fun α => by simp only [hFdef]; ring)).trans (integral_add ig iF)
  -- the diagonal of `g`
  have hGdiag : gPL c 0 * ∑ a ∈ s, m a ^ 2 ≤ ∑ a ∈ s, ∑ b ∈ s, m a * m b * gPL c (x a - x b) := by
    rw [mul_sum]
    refine sum_le_sum fun a ha => ?_
    have := single_le_sum (f := fun b => m a * m b * gPL c (x a - x b))
      (fun b _ => mul_nonneg (mul_nonneg (hm a) (hm b)) (gPL_nonneg c hG _)) ha
    simp only [sub_self] at this
    linarith [show gPL c 0 * m a ^ 2 = m a * m a * gPL c 0 by ring]
  -- the density part
  have hFpart : (h0 - ε) * N ^ 2 / (W + 4 * M) ≤ ∫ α, F α * Ssq s m x α := by
    have hFS0 : 0 ≤ ∫ α, F α * Ssq s m x α :=
      integral_nonneg fun α => mul_nonneg (hFnn α) (Ssq_nonneg s m x α)
    by_cases hs : h0 - ε ≤ 0
    · exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg _))
        (by linarith)).trans hFS0
    push Not at hs
    have iB : Integrable (fun α => B α * Ssq s m x α) :=
      (hBc.mul (by unfold Ssq; fun_prop)).integrable_of_hasCompactSupport hBs.mul_right
    have hmono : (h0 - ε / 2) * ∫ α, B α * Ssq s m x α ≤ ∫ α, F α * Ssq s m x α := by
      rw [← integral_const_mul]
      refine integral_mono (iB.const_mul _) iF fun α => ?_
      have := mul_le_mul_of_nonneg_right (hFB α) (Ssq_nonneg s m x α)
      calc (h0 - ε / 2) * (B α * Ssq s m x α) = (h0 - ε / 2) * B α * Ssq s m x α := by ring
        _ ≤ F α * Ssq s m x α := this
    have hdens := density_lb s m x hm hBc hBs hB0 hκ hκ0 hκi hκ1 (continuous_trap W M)
      (hasCompactSupport_trap hMpos) (trap_nonneg W M) (trap_le_one W M) hMpos.le
      (fun y h1 h2 => trap_eq_one hMpos h1 h2) (integral_trap_pos hMpos hW) hx
    have hP := integral_trap_le (W := W) hMpos hW
    have hPpos := integral_trap_pos (W := W) hMpos hW
    set I := ∫ t in (-M)..M, κ t with hI
    set P := ∫ y, trap W M y with hPdef
    have h1 : (h0 - ε) * N ^ 2 / (W + 4 * M) ≤ (h0 - ε) * N ^ 2 / P :=
      div_le_div_of_nonneg_left (by positivity) hPpos hP
    have h2 : (h0 - ε) * N ^ 2 / P ≤ (h0 - ε / 2) * (N ^ 2 * I ^ 2 / P) := by
      rw [show (h0 - ε / 2) * (N ^ 2 * I ^ 2 / P) = (h0 - ε / 2) * I ^ 2 * N ^ 2 / P by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hMI (sq_nonneg _)) hPpos.le
    have h3 : (h0 - ε / 2) * (N ^ 2 * I ^ 2 / P) ≤ (h0 - ε / 2) * ∫ α, B α * Ssq s m x α :=
      mul_le_mul_of_nonneg_left hdens (by linarith)
    linarith
  calc (h0 - ε) * N ^ 2 / (W + 4 * M) + gPL c 0 * ∑ a ∈ s, m a ^ 2
      ≤ (∫ α, F α * Ssq s m x α) + ∑ a ∈ s, ∑ b ∈ s, m a * m b * gPL c (x a - x b) := add_le_add hFpart hGdiag
    _ = (∫ α, F α * Ssq s m x α) + ∫ α, ghat c α * Ssq s m x α := by rw [hGeq]
    _ = ∫ α, qfAM α * Ssq s m x α := by rw [hsplit]; ring
    _ = ∑ a ∈ s, ∑ b ∈ s, m a * m b * wfunAM (x a - x b) := hE.symm

end AMW.DE

end
