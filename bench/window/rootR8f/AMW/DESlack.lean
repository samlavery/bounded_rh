import AMW.DefectEnergy

/-! ###### AMW/DESlack — the defect-energy inequality with a fixed slack (bridge-port)

`DefectEnergyS Z δ σ`: `δ (N − N₀ˢ) ≤ N ℰ_T + (σ + ε) N` eventually, for every `ε > 0`.  A certificate whose
`ĝ(0)` exceeds `g(0)` by a fixed amount enters here as `σ`.  Under it the simple on-line zeros are at least
`(1 − (e∞ + σ)/δ) N` (`AMW.dyadic_of_defectEnergyS`), with the board's two shapes `AMW.am_dyadic_defectS`,
`AMW.am_cumulative_defectS`.  `DefectEnergy` is the case `σ = 0` (`defectEnergyS_of_defectEnergy`). ###### -/

noncomputable section

open Filter Topology
open Zeta23

namespace Zeta23Ext.Bridge

/-- **the defect-energy inequality with slack `σ`** -/
def DefectEnergyS (Z : ZeroConfig) (δ σ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    δ * ((Z.N T (2 * T) : ℝ) - (Z.N0s T (2 * T) : ℝ))
      ≤ (Z.N T (2 * T) : ℝ) * edE Z T + (σ + ε) * (Z.N T (2 * T) : ℝ)

theorem defectEnergyS_of_defectEnergy {Z : ZeroConfig} {δ : ℝ} (hD : DefectEnergy Z δ) :
    DefectEnergyS Z δ 0 := by
  intro ε hε
  filter_upwards [hD ε hε] with T h
  simpa using h

end Zeta23Ext.Bridge

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge

/-- **from `D(δ)` with slack `σ`**: `(1 − (e∞ + σ)/δ − ε) N(T,2T) ≤ N₀ˢ(T,2T)` for large `T` -/
theorem dyadic_of_defectEnergyS {δ σ : ℝ} (hδ : 0 < δ) (hD : DefectEnergyS zetaZeroConfig δ σ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (eInfDE + σ) / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((hD (δ * ε / 2) (by positivity)).and
      (defectEnergy_datum zetaZeroConfig paperInputs_zeta (δ * ε / 2) (by positivity)))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at h1 h2
  have e : δ * ((1 - (eInfDE + σ) / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      = δ * (Zeta23.Ncount T (2 * T) : ℝ) - (eInfDE + σ) * (Zeta23.Ncount T (2 * T) : ℝ)
        - δ * ε * (Zeta23.Ncount T (2 * T) : ℝ) := by
    field_simp
  have key : δ * ((1 - (eInfDE + σ) / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      ≤ δ * (Zeta23.N0simple T (2 * T) : ℝ) := by
    rw [e]; linarith
  exact le_of_mul_le_mul_left key hδ

/-- the board's dyadic shape: `κ ≤ 1 − (e∞ + σ)/δ` under `D(δ)` with slack `σ` -/
theorem am_dyadic_defectS {δ σ κ : ℝ} (hδ : 0 < δ) (hD : DefectEnergyS zetaZeroConfig δ σ)
    (hκ : κ ≤ 1 - (eInfDE + σ) / δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := dyadic_of_defectEnergyS hδ hD ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (1 - (eInfDE + σ) / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- the cumulative form -/
theorem am_cumulative_defectS {δ σ κ : ℝ} (hδ : 0 < δ) (hD : DefectEnergyS zetaZeroConfig δ σ)
    (hκ : κ ≤ 1 - (eInfDE + σ) / δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic_defectS hδ hD hκ)

end AMW

end
