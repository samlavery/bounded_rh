import AMW.DER8
import AMW.DEQfZero
import AMW.Floor

/-! ###### AMW/DER8K — the rational κ for R8 (bridge-port)

`e∞ = (2 − H_W − e₀)/2` (`eInfDE_eq`, from `cRatio_inv_eq`), with `H_W ≥ 0.67216841` (`HW_ge`) and
`e₀ = qf(0) ≥ 1.0082637` (mvt-engine's `qfAM_zero_ge`), so
`1 − (e∞ + σ/2)/(g(0)/2) ≥ 1 − (2 − 0.67216841 − 1.0082637 + σ)/g(0) = 0.67596442…` (`kappa_R8_floor`).
Under Lemma P on the Lean object (`LemmaPObj`, a hypothesis): `κ = 0.6759644` (`AMW.am_dyadic_R8_rat`,
`AMW.am_cumulative_R8_rat`). ###### -/

noncomputable section

open Filter Real
open Zeta23 Zeta23Ext.Bridge AMW.DE

namespace AMW

/-- `e∞ = (2 − H_W − e₀)/2` -/
theorem eInfDE_eq : eInfDE = (2 - HW - e0DE) / 2 := by
  unfold HW
  rw [cRatio_inv_eq]
  ring

/-- `g(0)` of `cR8` in closed form -/
theorem gPL_zero_R8 : gPL cR8 0 = (1090493185684 : ℝ) / 1099511627776 - 12023728861 / 8796093022208 := by
  have h := sigmaR8_eq
  unfold sigmaR8 at h
  have hy : cR8.y 0 = (1090493185684 : ℝ) / 1099511627776 := by
    simp only [PLCert.y, PLCert.Y, cR8]
    norm_num
  rw [hy] at h
  linarith

/-- **the rational floor of the R8 κ** -/
theorem kappa_R8_floor :
    (6759644 / 10 ^ 7 : ℝ) ≤ 1 - (eInfDE + sigmaR8 / 2) / (gPL cR8 0 / 2) := by
  have hg := gPL_zero_R8
  have hg0 := gPL_zero_pos_R8
  have hHW := HW_ge
  have hq := qfAM_zero_ge
  have he0 : e0DE = DE.qfAM 0 := qfAM_zero_eq_e0DE.symm
  rw [eInfDE_eq, sigmaR8_eq]
  have key : (2 - HW - e0DE) / 2 + 12023728861 / 8796093022208 / 2
      ≤ (2 - 67216841 / 10 ^ 8 - 10082637 / 10 ^ 7 + (12023728861 : ℝ) / 8796093022208) / 2 := by
    rw [he0]; linarith
  have hfrac : ((2 - HW - e0DE) / 2 + 12023728861 / 8796093022208 / 2) / (gPL cR8 0 / 2)
      ≤ ((2 - 67216841 / 10 ^ 8 - 10082637 / 10 ^ 7 + (12023728861 : ℝ) / 8796093022208) / 2)
        / (gPL cR8 0 / 2) :=
    div_le_div_of_nonneg_right key (by linarith)
  have hnum : (6759644 / 10 ^ 7 : ℝ)
      ≤ 1 - ((2 - 67216841 / 10 ^ 8 - 10082637 / 10 ^ 7 + (12023728861 : ℝ) / 8796093022208) / 2)
        / (gPL cR8 0 / 2) := by
    rw [hg]; norm_num
  linarith

/-- **the board's dyadic shape for R8 at `κ = 0.6759644`, under Lemma P on the Lean object** -/
theorem am_dyadic_R8_rat (hP : LemmaPObj zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_R8 hP kappa_R8_floor

/-- the cumulative form -/
theorem am_cumulative_R8_rat (hP : LemmaPObj zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_R8 hP kappa_R8_floor

end AMW

end
