/-
AMW/ZeroSide.lean — the zero side for a window family `atW P W`, and the AMTOPA instance.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/XiPrime/QuarticWindow/ZeroSide.lean §1 and Zeta23/ThmD/ZeroSideD.lean, generic in the window:
from an admissibility witness T ↦ AdmWindow (W T) (L_T) w c (for 8w ≤ L_T) and 1/2 ≤ a eventually,
the fixed-T producers `ZeroSide.blockInputsAt`, `Tail.TailHyp.tailInputs`, `ZeroConfig.Gz_eq_Gp`
give prop:block, prop:tail (θ₀ ≤ C·l·T^{λ/2−1}) and the H-EF bridge for `atW P W T`.
The AMTOPA instance W T = phiW ϱ L_T w adds 1/2 ≤ a ≤ 1 for 32w ≤ L_T (vAM/MAM ≥ 137/250).
-/
import AMW.Params
import AMW.PV

noncomputable section

open Filter Complex Real Set MeasureTheory

namespace AMW

open Zeta23

section generic

variable {P : Params} {W : ℝ → ℝ → ℝ} {cW : ℝ} (hP : P.Valid) (hev : ∀ T u, W T (-u) = W T u)
  (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w cW)
include hP hev hW

/-! ### lem:poisson and prop:block -/

theorem poissonSqW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ZeroSide.PoissonSq T (atW P W T) := by
  intro γ
  have h := (hW T h8).hasSum_vHatR_mul T γ γ
  rw [sub_self, (hW T h8).VPhiR_zero] at h
  simp only [atW_phiHatR T hP (hev T), atW_a T hP (hev T), atW_tau_eq, atW_L, sq]
  convert h using 1
  ring

theorem blockInputsW (Z : ZeroConfig) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (haT : 0 < (atW P W T).a T) :
    Assembly.BlockInputs Z (atW P W T) T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  exact ZeroSide.blockInputsAt Z (atW P W T) T (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqW hP hev hW h8) hL (mul_pos haT (pow_pos hL 2))

/-! ### the H-EF bridge -/

theorem GzGpW (Z : ZeroConfig) (H : PaperInputs Z) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    Z.Gz (atW P W T) T = (atW P W T).Gp T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  refine Z.Gz_eq_Gp (atW P W T) T H.EF hL ?_ ?_
  · rw [atW_phi_valid T hP (hev T)]; exact (hW T h8).vC_contDiff
  · rw [atW_phi_valid T hP (hev T)]; exact closure_minimal (hW T h8).support_subset isClosed_Icc

/-! ### prop:tail -/

omit hP hev hW in
/-- C₁(T) := ‖(W T)″‖₁. -/
lemma C1W_nonneg (W : ℝ → ℝ → ℝ) (T : ℝ) : 0 ≤ ∫ u, |deriv (deriv (W T)) u| :=
  integral_nonneg fun _ => abs_nonneg _

omit hev in
lemma C1W_le {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ∫ u, |deriv (deriv (W T)) u| ≤ cW :=
  (hW T h8).l1_deriv2.trans (div_le_self (hW T h8).c_nonneg hP.one_le_w)

theorem hdecayW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖(atW P W T).phiHat T (r - I * y)‖
      ≤ Real.exp ((atW P W T).L T / 4) * (∫ u, |deriv (deriv (W T)) u|) / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hL : 0 ≤ P.L T := (hW T h8).L_pos.le
  rw [atW_phiHat T hP (hev T), atW_L, le_div_iff₀ (by positivity)]
  refine le_trans ((hW T h8).norm_vHat_mul_sq_le _) ?_
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

theorem eventually_tailPackageW (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (atW P W T).a T) (Z : ZeroConfig)
    (H : PaperInputs Z) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atW P W T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * ∫ u, |deriv (deriv (W T)) u|) T, ?_, ?_⟩
  · have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (ThmD.tendsto_L hP).eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop Tail.T₀, hL2, ThmD.eventually_w8 hP, ha] with T hT hL h8 haT
    have HT : Tail.TailHyp Z (atW P W T) T A₀ (∫ u, |deriv (deriv (W T)) u|) :=
      { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := C1W_nonneg W T,
        hdecay := fun r y hy hz => hdecayW hP hev hW h8 r y hy hz }
    exact HT.tailInputs (by linarith) (fun z => GzGp.phiHat_conj _ T z)
  · exact Tail.eventually_theta0_le P hP hA₀ (fun T => ∫ u, |deriv (deriv (W T)) u|)
      (C1W_nonneg W) (R := cW / 2) ((ThmD.eventually_w8 hP).mono fun T h8 => by linarith [C1W_le hP hW h8])

/-! ### the eventual exports -/

theorem eventually_blockInputsW (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (atW P W T).a T) (Z : ZeroConfig) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (atW P W T) T := by
  filter_upwards [ThmD.eventually_w8 hP, ha] with T h8 haT
  exact blockInputsW hP hev hW Z h8 (by linarith)

theorem eventually_GzGpW (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ᶠ T in atTop, Z.Gz (atW P W T) T = (atW P W T).Gp T := by
  filter_upwards [ThmD.eventually_w8 hP] with T h8
  exact GzGpW hP hev hW Z H h8

omit hW in
theorem eventually_a_le_one (hW' : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w cW) :
    ∀ᶠ T in atTop, (atW P W T).a T ≤ 1 := by
  filter_upwards [ThmD.eventually_w8 hP] with T h8
  rw [atW_a T hP (hev T)]; exact (hW' T h8).av_le_one

end generic

/-! ## The AMTOPA instance -/

/-- the AMTOPA window family of `P`. -/
def WAM (P : Params) (T : ℝ) : ℝ → ℝ := phiW P.ϱ (P.L T) P.w

/-- the per-height parameter set realizing it (the AM analogue of `Params.atD`). -/
def atAM (P : Params) (T : ℝ) : Params := atW P (WAM P) T

variable {P : Params}

theorem WAM_even (P : Params) (T u : ℝ) : WAM P T (-u) = WAM P T u := phiW_even u

theorem admWindow_WAM (hP : P.Valid) (T : ℝ) (h8 : 8 * P.w ≤ P.L T) :
    AdmWindow (WAM P T) (P.L T) P.w (cAMW P.ϱ) :=
  admWindow_phiW hP.taper hP.one_le_w h8

theorem atAM_a (hP : P.Valid) (T : ℝ) : (atAM P T).a T = AdmWindow.av (WAM P T) (P.L T) :=
  atW_a T hP (WAM_even P T)

theorem localFunW_eq (P : Params) (T : ℝ) : localFunW P T = AdmWindow.localFun (WAM P T) (P.L T) := rfl

/-- `phiW² ≥ (137/250)·φ²` pointwise. -/
lemma phiW_sq_ge (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
    137 / 250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ WAM P T u ^ 2 := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [WAM, phiW_sq_eq hP.taper hw0 hL]
  rcases le_or_gt (P.L T / 2) |u| with hu | hu
  · rw [Taper.phi_eq_zero hP.taper hw0 hu]; simp
  · exact mul_le_mul_of_nonneg_right (hW_core_ge hL hu.le) (sq_nonneg _)

/-- **1/2 ≤ a ≤ 1 for the AMTOPA window**, as soon as 32w ≤ L. -/
theorem aAM_range_of (hP : P.Valid) {T : ℝ} (h32 : 32 * P.w ≤ P.L T) :
    1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
  have h8 : 8 * P.w ≤ P.L T := by linarith [hP.one_le_w]
  have hW := admWindow_WAM hP T h8
  rw [atAM_a hP]
  refine ⟨?_, hW.av_le_one⟩
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2 : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hb : 1 - 2 * P.w / P.L T ≤ Taper.aConst P.ϱ (P.L T) P.w :=
    (Taper.one_sub_le_bConst hP.taper hw0 h2).trans (Taper.bConst_le_aConst hP.taper hw0 h2)
  have hwL : 2 * P.w / P.L T ≤ 1 / 16 := by rw [div_le_iff₀ hL]; linarith
  have hint : Integrable (fun u => WAM P T u ^ 2) := hW.integrable_pow two_pos
  have hint' : Integrable (fun u => 137 / 250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2) :=
    (((Taper.phi_continuous hP.taper hw0 h2).fun_pow 2).integrable_of_hasCompactSupport
      ((Taper.phi_hasCompactSupport hP.taper hw0).comp_left (g := fun t => t ^ 2) (by norm_num))).const_mul _
  have hcmp : 137 / 250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ ∫ u, WAM P T u ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono hint' hint (phiW_sq_ge hP h8)
  unfold AdmWindow.av
  unfold Taper.aConst at hb
  have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
  calc (1:ℝ) / 2 ≤ 137 / 250 * (1 - 2 * P.w / P.L T) := by nlinarith
    _ ≤ 137 / 250 * ((P.L T)⁻¹ * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by gcongr
    _ = (P.L T)⁻¹ * (137 / 250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by ring
    _ ≤ (P.L T)⁻¹ * ∫ u, WAM P T u ^ 2 := mul_le_mul_of_nonneg_left hcmp hLi.le

theorem eventually_w32 (hP : P.Valid) : ∀ᶠ T in atTop, 32 * P.w ≤ P.L T :=
  (ThmD.tendsto_L hP).eventually_ge_atTop _

theorem eventually_aAM_range (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
  filter_upwards [eventually_w32 hP] with T h32
  exact aAM_range_of hP h32

/-! ### the AMTOPA exports (instances of the generic section) -/

theorem eventually_blockInputsAM (Z : ZeroConfig) (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (atAM P T) T :=
  eventually_blockInputsW hP (WAM_even P) (admWindow_WAM hP)
    ((eventually_aAM_range hP).mono fun _ h => h.1) Z

theorem eventually_GzGpAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∀ᶠ T in atTop, Z.Gz (atAM P T) T = (atAM P T).Gp T :=
  eventually_GzGpW hP (WAM_even P) (admWindow_WAM hP) Z H

theorem eventually_tailPackageAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atAM P T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) :=
  eventually_tailPackageW hP (WAM_even P) (admWindow_WAM hP)
    ((eventually_aAM_range hP).mono fun _ h => h.1) Z H

end AMW

end
