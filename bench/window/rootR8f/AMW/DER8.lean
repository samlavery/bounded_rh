import AMW.DEObjMain
import AMW.DESOSR8
import AMW.DEQfR8

/-! ###### AMW/DER8 — the R8 certificate through the D chain (bridge-port)

With am-cert's `certG_R8` (`C ≥ 0`, Fejér–Riesz) and mvt-engine's `certH_R8` (`ĝ ≤ qf`, cells), the dip certificate
`cR8` satisfies the T-free theorem (`cert_T_free_R8`).  Its slack is `σ = ĝ(0) − g(0) = 12023728861/8796093022208`
(`ghat0_sub_g0_R8`), and `qf(0) = e₀` (`qfAM_zero_eq_e0DE`), so `e₀ = h₀ + g₀ + σ` exactly.  Under Lemma P on the
Lean object (`LemmaPObj`, a hypothesis) the board's two shapes follow with `κ ≤ 1 − (e∞ + σ/2)/(g(0)/2)`
(`AMW.am_dyadic_R8`, `AMW.am_cumulative_R8`).  `lemmaPObj_R8_online` is the on-line instance (conditional on the
window zeros being on the line). ###### -/

noncomputable section

open Filter Real Finset
open Zeta23 Zeta23Ext.Bridge

namespace AMW.DE

theorem cert_T_free_R8 :
    ∀ ε > 0, ∃ R > 0, ∀ (ι : Type) (s : Finset ι) (m x : ι → ℝ) (W : ℝ), 0 ≤ W → (∀ a, 0 ≤ m a) →
      (∀ a ∈ s, 0 ≤ x a ∧ x a ≤ W) →
      (qfAM 0 - cR8.y 0 - ε) * (∑ a ∈ s, m a) ^ 2 / (W + R) + gPL cR8 0 * ∑ a ∈ s, m a ^ 2
        ≤ ∑ a ∈ s, ∑ b ∈ s, m a * m b * wfunAM (x a - x b) :=
  cert_T_free cR8 (by decide) certG_R8 certH_R8

/-- `qf(0) = ∫v²/(∫v)² = e₀` -/
theorem qfAM_zero_eq_e0DE : qfAM 0 = e0DE := by
  have hM := MAM_pos
  have hI : Ivam ≠ 0 := by rw [Ivam, ← KfunAM_zero]; exact KfunAM_zero_pos.ne'
  unfold qfAM e0DE aInf bInf vConvAM
  rw [if_pos (by simp), abs_zero]
  simp only [sub_zero, add_zero]
  have hb : ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s / MAM) ^ 2 = (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * vAM s) / MAM ^ 2 := by
    rw [← intervalIntegral.integral_div]
    congr 1; funext s; ring
  rw [hb]
  unfold Ivam
  field_simp

/-- `qf(0) ≥ 1` (Cauchy–Schwarz on the unit window) -/
theorem one_le_qfAM_zero : 1 ≤ qfAM 0 := by
  have hI : 0 < Ivam := by rw [Ivam, ← KfunAM_zero]; exact KfunAM_zero_pos
  unfold qfAM vConvAM
  rw [if_pos (by simp), abs_zero]
  simp only [sub_zero, add_zero]
  rw [one_le_div (by positivity)]
  -- `0 ≤ ∫ (v − I)² = ∫ v² − I²` on an interval of length one
  have hc : Continuous vAM := vAM_continuous
  have h0 : 0 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s - Ivam) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have e : ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s - Ivam) ^ 2
      = (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * vAM s) - Ivam ^ 2 := by
    have e1 : ∀ s, (vAM s - Ivam) ^ 2 = vAM s * vAM s - 2 * Ivam * vAM s + Ivam ^ 2 := fun s => by ring
    simp_rw [e1]
    have i1 : IntervalIntegrable (fun s => vAM s * vAM s) MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
      (hc.mul hc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => 2 * Ivam * vAM s) MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
      (continuous_const.mul hc).intervalIntegrable _ _
    have i12 : IntervalIntegrable (fun s => vAM s * vAM s - 2 * Ivam * vAM s) MeasureTheory.volume
        (-(1:ℝ)/2) (1/2) := i1.sub i2
    rw [intervalIntegral.integral_add i12 intervalIntegrable_const, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    unfold Ivam
    simp only [smul_eq_mul]
    ring
  linarith

theorem y0_lt_qfAM_R8 : cR8.y 0 < qfAM 0 := by
  have h1 : cR8.y 0 < 1 := by
    simp only [PLCert.y, PLCert.Y, cR8]
    norm_num
  linarith [one_le_qfAM_zero]

/-- `g(0) > 0` for `cR8` -/
theorem gPL_zero_pos_R8 : 0 < gPL cR8 0 := by
  have h := ghat0_sub_g0_R8
  have hg : gPL cR8 0 = cR8.dk * certC cR8 0 := by
    unfold gPL; simp
  rw [hg]
  have hy : cR8.y 0 = (1090493185684 : ℝ) / 1099511627776 := by
    simp only [PLCert.y, PLCert.Y, cR8]
    norm_num
  rw [hy] at h
  linarith

end AMW.DE

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge AMW.DE

/-- the R8 slack `σ = ĝ(0) − g(0)` -/
def sigmaR8 : ℝ := cR8.y 0 - gPL cR8 0

theorem sigmaR8_eq : sigmaR8 = (12023728861 : ℝ) / 8796093022208 := by
  have h := ghat0_sub_g0_R8
  have hg : gPL cR8 0 = cR8.dk * certC cR8 0 := by unfold gPL; simp
  unfold sigmaR8; rw [hg]; exact h

theorem e0DE_eq_R8 : e0DE ≤ (DE.qfAM 0 - cR8.y 0) + gPL cR8 0 + sigmaR8 := by
  unfold sigmaR8; rw [← qfAM_zero_eq_e0DE]; linarith

/-- **the board's dyadic shape for R8 under Lemma P on the Lean object** -/
theorem am_dyadic_R8 (hP : LemmaPObj zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) {κ : ℝ}
    (hκ : κ ≤ 1 - (eInfDE + sigmaR8 / 2) / (gPL cR8 0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_lemmaP hP gPL_zero_pos_R8 e0DE_eq_R8 hκ

/-- the cumulative form -/
theorem am_cumulative_R8 (hP : LemmaPObj zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) {κ : ℝ}
    (hκ : κ ≤ 1 - (eInfDE + sigmaR8 / 2) / (gPL cR8 0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_lemmaP hP gPL_zero_pos_R8 e0DE_eq_R8 hκ

/-- the on-line instance of `LemmaPObj` for R8 (conditional on the window zeros being on the line) -/
theorem lemmaPObj_R8_online (hon : ∀ᶠ T in atTop, ∀ ρ ∈ zetaZeroConfig.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObj zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0) :=
  lemmaPObj_online zetaZeroConfig paperInputs_zeta cR8 (by decide) certG_R8 certH_R8 y0_lt_qfAM_R8 hon

end AMW

end
