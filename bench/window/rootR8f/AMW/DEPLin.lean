import AMW.DEPSq

/-! ###### AMW/DEPLin — Lemma P with linear per-zero weights (am-cert)

`LemmaPObjZ` (`AMW/DEPSq`) charges an on-line zero of multiplicity `m` the weight `m²`.  In the periodic model that
charge is too large: an on-line zero of multiplicity `M` flanked by shallow off-line pairs gives `LP_pSq < 0` (window
`R8b`):
* `M ≥ 4` at `N = 64`;
* `M ≥ 5` at `N = 256`, where `M = 4` gives `+0.0099`.

Sources: bench/window/band1/round8_onmult_{a,b,c}.log (with an mp50 recheck) and round9_lin_i{64,256}.log.

Here every zero carries the weight the count needs and nothing more (`wLin`):
* `1` for a simple on-line zero;
* `2m` for an on-line zero of multiplicity `m ≥ 2`;
* `2m` for an off-line zero.

Then `pLin Z T = Σ_ρ wLin(ρ)`, and the count is an identity, not just an inequality:
* `pLin_add_N0s`: `pLin + N₀ˢ = 2N` exactly, so `pLin_ge`: `2N ≤ pLin + N₀ˢ`;
* `pLin_le_pSq`: `pLin ≤ pSq` (`2m ≤ m²` for `m ≥ 2`), so `LemmaPObjZ → LemmaPObjL` (`lemmaPObjL_of_lemmaPObjZ`), and
  `LemmaPObjL` is the weaker hypothesis;
* `AMW.am_dyadic_R8_ratL`, `AMW.am_cumulative_R8_ratL`: `κ = 0.6759644`, unchanged, under `LemmaPObjL` (a hypothesis);
* `lemmaPObjL_online`, `AMW.lemmaPObjL_R8_online`: the on-line instance, through the implication.

In the same model, `LP_lin` has minimum `+3.12` (`M = 3`, `N = 64`) and grows like `≈ 0.30·M²` up to `M = 48`
(round9_lin_i64.log, round9_lin_largeM.log).  These are numerical model results; nothing here depends on them.
`DEPSq` is unchanged. ###### -/

noncomputable section

open Filter Topology Finset Classical
open Zeta23 RHLinalg

namespace Zeta23Ext.Bridge

/-- the linear weight of one zero: `1` for a simple on-line zero, `2m` otherwise -/
def wLin (Z : ZeroConfig) (ρ : ℂ) : ℕ :=
  if ρ.re = 1 / 2 then (if Z.mult ρ = 1 then 1 else 2 * Z.mult ρ) else 2 * Z.mult ρ

/-- `Σ_ρ wLin(ρ)` over the zeros with ordinate in `(T, 2T]` -/
def pLin (Z : ZeroConfig) (T : ℝ) : ℕ := ∑ ρ ∈ winFin Z T, wLin Z ρ

/-- **Lemma P, count-only, linear per-zero weights** (a hypothesis) -/
def LemmaPObjL (Z : ZeroConfig) (h0 g0 : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    h0 * (Z.N T (2 * T) : ℝ) + g0 * (pLin Z T : ℝ) - ε * (Z.N T (2 * T) : ℝ)
      ≤ frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))

/-- **the count, exactly**: `pLin + N₀ˢ = 2N` -/
theorem pLin_add_N0s (Z : ZeroConfig) (T : ℝ) :
    pLin Z T + Z.N0s T (2 * T) = 2 * Z.N T (2 * T) := by
  rw [N_eq_sum_winFin, N0s_eq_card, card_eq_sum_ones, sum_filter, pLin, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ρ _ => ?_
  unfold wLin
  by_cases hre : ρ.re = 1 / 2
  · by_cases h1 : Z.mult ρ = 1
    · simp [hre, h1]
    · simp [hre, h1]
  · rw [if_neg hre, if_neg (fun h => hre h.1), add_zero]

/-- **the count**: `2N ≤ pLin + N₀ˢ` -/
theorem pLin_ge (Z : ZeroConfig) (T : ℝ) :
    2 * Z.N T (2 * T) ≤ pLin Z T + Z.N0s T (2 * T) :=
  (pLin_add_N0s Z T).ge

/-- one zero's linear weight is at most its `pSq` weight -/
theorem wLin_le_zWeight (Z : ZeroConfig) (T : ℝ) {ρ : ℂ} (hρS : ρ ∈ winFin Z T) :
    wLin Z ρ ≤ zWeight Z ρ := by
  have hm : 1 ≤ Z.mult ρ := Z.one_le_mult ρ (mem_winFin.mp hρS).1
  unfold wLin zWeight
  by_cases hre : ρ.re = 1 / 2
  · by_cases h1 : Z.mult ρ = 1
    · simp [hre, h1]
    · have h2 : 2 ≤ Z.mult ρ := by omega
      simp only [if_pos hre, if_neg h1]
      nlinarith
  · rw [if_neg hre, if_neg hre]

/-- **the linear weights are dominated by the `pSq` weights**: `pLin ≤ pSq` -/
theorem pLin_le_pSq (Z : ZeroConfig) (T : ℝ) : pLin Z T ≤ pSq Z T :=
  sum_le_sum fun _ hρ => wLin_le_zWeight Z T hρ

/-- **the per-zero (`pSq`) hypothesis implies the linear one** -/
theorem lemmaPObjL_of_lemmaPObjZ {Z : ZeroConfig} {h0 g0 : ℝ} (hP : LemmaPObjZ Z h0 g0) (hg0 : 0 ≤ g0) :
    LemmaPObjL Z h0 g0 := by
  intro ε hε
  filter_upwards [hP ε hε] with T h
  have hle : (pLin Z T : ℝ) ≤ pSq Z T := by exact_mod_cast pLin_le_pSq Z T
  have := mul_le_mul_of_nonneg_left hle hg0
  linarith

/-- the ordinate-class hypothesis implies the linear one -/
theorem lemmaPObjL_of_lemmaPObj {Z : ZeroConfig} {h0 g0 : ℝ} (hP : LemmaPObj Z h0 g0) (hg0 : 0 ≤ g0) :
    LemmaPObjL Z h0 g0 :=
  lemmaPObjL_of_lemmaPObjZ (lemmaPObjZ_of_lemmaPObj hP hg0) hg0

/-- **Lemma P (linear) ⇒ the defect-energy inequality** with `δ = g₀/2` and slack `σ/2` -/
theorem defectEnergyS_of_lemmaPL {Z : ZeroConfig} {h0 g0 σ : ℝ} (hP : LemmaPObjL Z h0 g0) (hg0 : 0 ≤ g0)
    (hs : e0DE ≤ h0 + g0 + σ) : DefectEnergyS Z (g0 / 2) (σ / 2) := by
  intro ε hε
  filter_upwards [hP ε hε] with T h
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set Ns : ℝ := (Z.N0s T (2 * T) : ℝ) with hNsdef
  set F := frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) with hFdef
  have hc : 2 * N ≤ (pLin Z T : ℝ) + Ns := by
    have := pLin_ge Z T
    rw [hNdef, hNsdef]
    exact_mod_cast this
  have hNs0 : 0 ≤ Ns := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  unfold edE
  rw [← hFdef, ← hNdef]
  rcases eq_or_ne N 0 with h0' | h0'
  · rw [h0']
    have : 0 ≤ g0 / 2 * Ns := by positivity
    simp only [zero_sub, mul_neg, zero_mul, add_zero, mul_zero]
    linarith
  · have hF : N * ((F / N - e0DE) / 2) = (F - e0DE * N) / 2 := by field_simp
    rw [hF]
    have hg : g0 * (2 * N - Ns) ≤ g0 * (pLin Z T : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hg0
    have hεN : 0 ≤ ε * N := mul_nonneg hε.le hN0
    have hsN : e0DE * N ≤ (h0 + g0 + σ) * N := mul_le_mul_of_nonneg_right hs hN0
    nlinarith

/-- the on-line instance of `LemmaPObjL` (conditional on the window zeros being on the line) -/
theorem lemmaPObjL_online (Z : ZeroConfig) (H : PaperInputs Z) (c : AMW.DE.PLCert) (hD : 0 < c.DkInv)
    (hG : AMW.DE.CertGNonneg c) (hH : AMW.DE.CertHNonneg c) (hy : c.y 0 < AMW.DE.qfAM 0)
    (hon : ∀ᶠ T in atTop, ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObjL Z (AMW.DE.qfAM 0 - c.y 0) (AMW.DE.gPL c 0) :=
  lemmaPObjL_of_lemmaPObjZ (lemmaPObjZ_online Z H c hD hG hH hy hon) (AMW.DE.gPL_nonneg c hG 0)

end Zeta23Ext.Bridge

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge AMW.DE

/-- **the board's dyadic shape under Lemma P (linear)**: `κ ≤ 1 − (e∞ + σ/2)/(g₀/2)` -/
theorem am_dyadic_lemmaPL {h0 g0 σ κ : ℝ} (hP : LemmaPObjL zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_defectS (by positivity) (defectEnergyS_of_lemmaPL hP hg0.le hs) hκ

/-- the cumulative form -/
theorem am_cumulative_lemmaPL {h0 g0 σ κ : ℝ} (hP : LemmaPObjL zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_defectS (by positivity) (defectEnergyS_of_lemmaPL hP hg0.le hs) hκ

/-- **the board's dyadic shape for R8 at `κ = 0.6759644`, under Lemma P (linear) on the Lean object** -/
theorem am_dyadic_R8_ratL (hP : LemmaPObjL zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_lemmaPL hP gPL_zero_pos_R8 e0DE_eq_R8 kappa_R8_floor

/-- the cumulative form -/
theorem am_cumulative_R8_ratL (hP : LemmaPObjL zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_lemmaPL hP gPL_zero_pos_R8 e0DE_eq_R8 kappa_R8_floor

/-- the on-line instance of `LemmaPObjL` for R8 (conditional on the window zeros being on the line) -/
theorem lemmaPObjL_R8_online (hon : ∀ᶠ T in atTop, ∀ ρ ∈ zetaZeroConfig.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObjL zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0) :=
  lemmaPObjL_of_lemmaPObjZ (lemmaPObjZ_R8_online hon) gPL_zero_pos_R8.le

end AMW

end
