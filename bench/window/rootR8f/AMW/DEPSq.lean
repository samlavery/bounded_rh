import AMW.DER8K

/-! ###### AMW/DEPSq — Lemma P with per-zero weights (bridge-port)

`LemmaPObj` (`AMW/DEPInterface`) groups the zeros by ordinate and charges `g₀ Σ_t M_T(t)²` (`ordSq`).  That form is
stronger than the count needs: a cluster whose zeros share one ordinate (an off-line zero of multiplicity `m` with its
reflection, or several zeros on one ordinate) is charged `g₀ (2m)²`, and in the periodic model of Lemma P two such
stacks joined by a chain of deeper pairs give `E(Z) < F_C` at `m ≥ 12`, stably in the period (bench/window/sat9/e15).

Here each zero carries its own weight `w(ρ) = m_ρ²` on the line and `w(ρ) = 2 m_ρ` off it (`zWeight`), and
`pSq Z T = Σ_ρ w(ρ)`.  This is the convention of the numerical model (each off-line pair a double of mass 2).
* `pSq_ge`: `2N ≤ pSq + N₀ˢ`, term by term, so the count goes through unchanged (`defectEnergyS_of_lemmaPZ`).
* `pSq_le_ordSq`: `pSq ≤ ordSq` (an off-line class contains the reflection, so `M_T(t) ≥ 2`), hence
  `LemmaPObj → LemmaPObjZ` (`lemmaPObjZ_of_lemmaPObj`): the per-zero hypothesis is the weaker one.
* `pSq_eq_of_online`: on an on-line window `pSq = ordSq`; `lemmaPObjZ_online`, `lemmaPObjZ_R8_online`.
* `AMW.am_dyadic_R8_ratZ`, `AMW.am_cumulative_R8_ratZ`: `κ = 0.6759644` under `LemmaPObjZ` (a hypothesis).
The `ordSq` versions are kept as they were. ###### -/

noncomputable section

open Filter Topology Finset Classical
open Zeta23 RHLinalg

namespace Zeta23Ext.Bridge

/-- the weight of one zero: `m²` on the line, `2m` off it -/
def zWeight (Z : ZeroConfig) (ρ : ℂ) : ℕ := if ρ.re = 1 / 2 then Z.mult ρ ^ 2 else 2 * Z.mult ρ

/-- `Σ_ρ w(ρ)` over the zeros with ordinate in `(T, 2T]` -/
def pSq (Z : ZeroConfig) (T : ℝ) : ℕ := ∑ ρ ∈ winFin Z T, zWeight Z ρ

/-- **Lemma P, count-only, per-zero weights** (a hypothesis) -/
def LemmaPObjZ (Z : ZeroConfig) (h0 g0 : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    h0 * (Z.N T (2 * T) : ℝ) + g0 * (pSq Z T : ℝ) - ε * (Z.N T (2 * T) : ℝ)
      ≤ frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))

/-- **the count**: `2N ≤ Σ_ρ w(ρ) + N₀ˢ` -/
theorem pSq_ge (Z : ZeroConfig) (T : ℝ) :
    2 * Z.N T (2 * T) ≤ pSq Z T + Z.N0s T (2 * T) := by
  rw [N_eq_sum_winFin, N0s_eq_card, card_eq_sum_ones, sum_filter, pSq, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun ρ hρ => ?_
  have hm : 1 ≤ Z.mult ρ := Z.one_le_mult ρ (mem_winFin.mp hρ).1
  unfold zWeight
  by_cases hre : ρ.re = 1 / 2
  · by_cases h1 : Z.mult ρ = 1
    · simp [hre, h1]
    · have h2 : 2 ≤ Z.mult ρ := by omega
      simp only [if_pos hre, h1, and_false, if_false, add_zero]
      nlinarith
  · rw [if_neg hre, if_neg (fun h => hre h.1)]
    omega

/-- one zero's weight is at most its multiplicity times its ordinate class -/
theorem zWeight_le (Z : ZeroConfig) (T : ℝ) {ρ : ℂ} (hρS : ρ ∈ winFin Z T) :
    zWeight Z ρ ≤ Z.mult ρ * ordMult Z T ρ.im := by
  have hρ := mem_winFin.mp hρS
  have hρC : ρ ∈ (winFin Z T).filter (fun x => x.im = ρ.im) := mem_filter.mpr ⟨hρS, rfl⟩
  have hle : Z.mult ρ ≤ ordMult Z T ρ.im :=
    single_le_sum (f := fun ρ => Z.mult ρ) (fun _ _ => Nat.zero_le _) hρC
  unfold zWeight
  split_ifs with hre
  · rw [sq]
    exact Nat.mul_le_mul_left _ hle
  · -- an off-line zero shares its ordinate with its reflection, so the class has multiplicity `≥ 2`
    have hrS : reflect ρ ∈ winFin Z T := by
      refine mem_winFin.mpr ⟨Z.reflect_mem ρ hρ.1, ?_, ?_⟩ <;> rw [reflect_im]
      · exact hρ.2.1
      · exact hρ.2.2
    have hrC : reflect ρ ∈ (winFin Z T).filter (fun x => x.im = ρ.im) :=
      mem_filter.mpr ⟨hrS, reflect_im ρ⟩
    have hne' : reflect ρ ≠ ρ := by
      intro h
      apply hre
      have := congrArg Complex.re h
      rw [reflect_re] at this
      linarith
    have hpair : ({ρ, reflect ρ} : Finset ℂ) ⊆ (winFin Z T).filter (fun x => x.im = ρ.im) := by
      intro x hx
      rcases mem_insert.mp hx with h | h
      · rw [h]; exact hρC
      · rw [mem_singleton.mp h]; exact hrC
    have hsum := sum_le_sum_of_subset (f := fun ρ => Z.mult ρ) hpair
    rw [sum_pair hne'.symm, Z.mult_reflect ρ hρ.1] at hsum
    have hm1 : 1 ≤ Z.mult ρ := Z.one_le_mult ρ hρ.1
    have h2 : 2 ≤ ordMult Z T ρ.im := by unfold ordMult; omega
    calc 2 * Z.mult ρ = Z.mult ρ * 2 := Nat.mul_comm _ _
      _ ≤ Z.mult ρ * ordMult Z T ρ.im := Nat.mul_le_mul_left _ h2

/-- **the per-zero weights are dominated by the ordinate classes**: `pSq ≤ ordSq` -/
theorem pSq_le_ordSq (Z : ZeroConfig) (T : ℝ) : pSq Z T ≤ ordSq Z T := by
  have hmaps : ∀ ρ ∈ winFin Z T, ρ.im ∈ (winFin Z T).image Complex.im := fun ρ hρ => mem_image_of_mem _ hρ
  have key : ∑ ρ ∈ winFin Z T, Z.mult ρ * ordMult Z T ρ.im = ordSq Z T := by
    rw [← sum_fiberwise_of_maps_to hmaps (fun ρ => Z.mult ρ * ordMult Z T ρ.im), ordSq]
    refine sum_congr rfl fun t _ => ?_
    have hc : ∀ ρ ∈ (winFin Z T).filter (fun ρ => ρ.im = t),
        Z.mult ρ * ordMult Z T ρ.im = Z.mult ρ * ordMult Z T t := by
      intro ρ hρ
      rw [(mem_filter.mp hρ).2]
    rw [sum_congr rfl hc, ← sum_mul, sq]
    rfl
  rw [← key]
  exact sum_le_sum fun ρ hρ => zWeight_le Z T hρ

/-- on an on-line window the two weightings agree -/
theorem pSq_eq_of_online (Z : ZeroConfig) (T : ℝ) (hon : ∀ ρ ∈ winFin Z T, ρ.re = 1 / 2) :
    (pSq Z T : ℝ) = ordSq Z T := by
  rw [ordSq_eq_of_online Z T hon, pSq]
  push_cast
  refine sum_congr rfl fun ρ hρ => ?_
  rw [zWeight, if_pos (hon ρ hρ)]
  push_cast
  rfl

/-- **the ordinate-class hypothesis implies the per-zero one** -/
theorem lemmaPObjZ_of_lemmaPObj {Z : ZeroConfig} {h0 g0 : ℝ} (hP : LemmaPObj Z h0 g0) (hg0 : 0 ≤ g0) :
    LemmaPObjZ Z h0 g0 := by
  intro ε hε
  filter_upwards [hP ε hε] with T h
  have hle : (pSq Z T : ℝ) ≤ ordSq Z T := by exact_mod_cast pSq_le_ordSq Z T
  have := mul_le_mul_of_nonneg_left hle hg0
  linarith

/-- **Lemma P (per-zero) ⇒ the defect-energy inequality** with `δ = g₀/2` and slack `σ/2` -/
theorem defectEnergyS_of_lemmaPZ {Z : ZeroConfig} {h0 g0 σ : ℝ} (hP : LemmaPObjZ Z h0 g0) (hg0 : 0 ≤ g0)
    (hs : e0DE ≤ h0 + g0 + σ) : DefectEnergyS Z (g0 / 2) (σ / 2) := by
  intro ε hε
  filter_upwards [hP ε hε] with T h
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set Ns : ℝ := (Z.N0s T (2 * T) : ℝ) with hNsdef
  set F := frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) with hFdef
  have hc : 2 * N ≤ (pSq Z T : ℝ) + Ns := by
    have := pSq_ge Z T
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
    have hg : g0 * (2 * N - Ns) ≤ g0 * (pSq Z T : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hg0
    have hεN : 0 ≤ ε * N := mul_nonneg hε.le hN0
    have hsN : e0DE * N ≤ (h0 + g0 + σ) * N := mul_le_mul_of_nonneg_right hs hN0
    nlinarith

/-- the on-line instance of `LemmaPObjZ` (conditional on the window zeros being on the line) -/
theorem lemmaPObjZ_online (Z : ZeroConfig) (H : PaperInputs Z) (c : AMW.DE.PLCert) (hD : 0 < c.DkInv)
    (hG : AMW.DE.CertGNonneg c) (hH : AMW.DE.CertHNonneg c) (hy : c.y 0 < AMW.DE.qfAM 0)
    (hon : ∀ᶠ T in atTop, ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObjZ Z (AMW.DE.qfAM 0 - c.y 0) (AMW.DE.gPL c 0) :=
  lemmaPObjZ_of_lemmaPObj (lemmaPObj_online Z H c hD hG hH hy hon) (AMW.DE.gPL_nonneg c hG 0)

end Zeta23Ext.Bridge

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge AMW.DE

/-- **the board's dyadic shape under Lemma P (per-zero)**: `κ ≤ 1 − (e∞ + σ/2)/(g₀/2)` -/
theorem am_dyadic_lemmaPZ {h0 g0 σ κ : ℝ} (hP : LemmaPObjZ zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_defectS (by positivity) (defectEnergyS_of_lemmaPZ hP hg0.le hs) hκ

/-- the cumulative form -/
theorem am_cumulative_lemmaPZ {h0 g0 σ κ : ℝ} (hP : LemmaPObjZ zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_defectS (by positivity) (defectEnergyS_of_lemmaPZ hP hg0.le hs) hκ

/-- **the board's dyadic shape for R8 at `κ = 0.6759644`, under Lemma P (per-zero) on the Lean object** -/
theorem am_dyadic_R8_ratZ (hP : LemmaPObjZ zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_lemmaPZ hP gPL_zero_pos_R8 e0DE_eq_R8 kappa_R8_floor

/-- the cumulative form -/
theorem am_cumulative_R8_ratZ (hP : LemmaPObjZ zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6759644 / 10 ^ 7 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_lemmaPZ hP gPL_zero_pos_R8 e0DE_eq_R8 kappa_R8_floor

/-- the on-line instance of `LemmaPObjZ` for R8 (conditional on the window zeros being on the line) -/
theorem lemmaPObjZ_R8_online (hon : ∀ᶠ T in atTop, ∀ ρ ∈ zetaZeroConfig.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObjZ zetaZeroConfig (DE.qfAM 0 - cR8.y 0) (gPL cR8 0) :=
  lemmaPObjZ_of_lemmaPObj (lemmaPObj_R8_online hon) gPL_zero_pos_R8.le

end AMW

end
