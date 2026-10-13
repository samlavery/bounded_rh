import AMW.DEObjC

/-! ###### AMW/DEObj — growth facts for the on-line instance (bridge-port)

`growth`: the two wall counts are `O(L²) = o(N)` (from the bridge's `strips_le`), their square is `o(N)`, and the
number of sample points satisfies `d ≤ (1 + κ) N` (RvM).  `kfunAM_zero`, `natFloor_le_of_le` are small helpers.
The on-line instance of Lemma P is `DEObjMain.lemmaPObj_online`. ###### -/

noncomputable section

open Finset Real Filter Topology Asymptotics RHLinalg
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

open Classical

/-- the two wall counts at height `T` -/
def wallN (Z : ZeroConfig) (T : ℝ) : ℝ :=
  (Z.N T (T + 2 * Real.pi * (paramsOf stdProfile 1).L T) : ℝ)
    + Z.N (2 * T - (2 * Real.pi * (paramsOf stdProfile 1).L T + 2 * Real.pi / (paramsOf stdProfile 1).L T)) (2 * T)

/-- **growth**: the walls are `o(N)`, their square is `o(N)`, and `d ≤ (1 + κ) N` -/
theorem growth (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ κ > 0, ∀ᶠ T in atTop,
      wallN Z T ≤ κ * Z.N T (2 * T) ∧ wallN Z T ^ 2 ≤ κ * Z.N T (2 * T)
        ∧ ((mtParams T).d T : ℝ) ≤ (1 + κ) * Z.N T (2 * T) := by
  intro κ hκ
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hπ := Real.pi_pos
  set B : ℝ := 1600 * A₀ + 1 with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  set c4 : ℝ := κ / (4 * Real.pi * B ^ 2) with hc4
  set c1 : ℝ := min (1 / (4 * Real.pi * (|C| + 1))) (κ / (4 * Real.pi * (|C| + 1))) with hc1
  have hc4pos : 0 < c4 := by positivity
  have hc1pos : 0 < c1 := lt_min (by positivity) (by positivity)
  have hl4 : ∀ᶠ x in atTop, ‖Real.log x ^ 4‖ ≤ c4 * ‖id x‖ :=
    (Real.isLittleO_pow_log_id_atTop (n := 4)).def hc4pos
  have hl1 : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c1 * ‖id x‖ := Real.isLittleO_log_id_atTop.def hc1pos
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    hl4, hl1] with T hT3 hTT₀ hL1 h4 h1
  have hT0 : 0 < T := by linarith
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
  have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
    rw [hLdef]
    show 1 * Real.log (T / (2 * Real.pi)) = _
    rw [one_mul, Real.log_div hT0.ne' (by positivity)]
  have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
  have hLlogT : L ≤ Real.log T := by linarith
  have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
  have hLT : L ≤ T := by linarith
  have hlogT1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log T := by linarith
  have h4' : Real.log T ^ 4 ≤ c4 * T := by
    simpa [Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlog0] using h4
  have h1' : Real.log T ≤ c1 * T := by
    simpa [Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlog0] using h1
  have hstrips := strips_le Z hA₀ hloc (by linarith : (1 : ℝ) ≤ T) hL1 hLT hlogT
  have hw : wallN Z T ≤ 1600 * A₀ * L ^ 2 := hstrips
  have hw0 : 0 ≤ wallN Z T := by unfold wallN; positivity
  -- the lower bound for `N`
  have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have h := hRvM T hTT₀
    have hℓ₁ : L ≤ ell1 T := by
      show 1 * l T ≤ l T + 2 * Real.log 2 - 1
      have := Real.log_two_gt_d9
      linarith
    have h1 := (abs_le.mp h).1
    have h2 : C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith
  have hC1 : |C| * Real.log T ≤ T / (4 * Real.pi) := by
    have : c1 ≤ 1 / (4 * Real.pi * (|C| + 1)) := min_le_left _ _
    calc |C| * Real.log T ≤ (|C| + 1) * (c1 * T) :=
          mul_le_mul (by linarith [abs_nonneg C]) h1' hlog0 (by positivity)
      _ ≤ (|C| + 1) * (1 / (4 * Real.pi * (|C| + 1)) * T) := by gcongr
      _ = T / (4 * Real.pi) := by field_simp
  have hCκ : |C| * Real.log T ≤ κ * (T / (4 * Real.pi)) := by
    have : c1 ≤ κ / (4 * Real.pi * (|C| + 1)) := min_le_right _ _
    calc |C| * Real.log T ≤ (|C| + 1) * (c1 * T) :=
          mul_le_mul (by linarith [abs_nonneg C]) h1' hlog0 (by positivity)
      _ ≤ (|C| + 1) * (κ / (4 * Real.pi * (|C| + 1)) * T) := by gcongr
      _ = κ * (T / (4 * Real.pi)) := by field_simp
  have hTL : T / (2 * Real.pi) ≤ T * L / (2 * Real.pi) := by
    rw [show T * L / (2 * Real.pi) = T / (2 * Real.pi) * L by ring]
    exact le_mul_of_one_le_right (by positivity) hL1
  have hNT : T / (4 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) := by
    have : T / (4 * Real.pi) = T / (2 * Real.pi) - T / (4 * Real.pi) := by field_simp; ring
    linarith
  have hL2 : L ^ 2 ≤ Real.log T ^ 4 := by
    have hL0 : 0 ≤ L := by linarith
    calc L ^ 2 ≤ Real.log T ^ 2 := pow_le_pow_left₀ hL0 hLlogT 2
      _ ≤ Real.log T ^ 4 := pow_le_pow_right₀ hlogT1 (by norm_num)
  have hL4 : L ^ 4 ≤ Real.log T ^ 4 := pow_le_pow_left₀ (by linarith) hLlogT 4
  have hBT : B ^ 2 * (c4 * T) = κ * (T / (4 * Real.pi)) := by rw [hc4]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · calc wallN Z T ≤ 1600 * A₀ * L ^ 2 := hw
      _ ≤ B * Real.log T ^ 4 := by
          have : 1600 * A₀ ≤ B := by rw [hB]; linarith
          exact mul_le_mul this hL2 (sq_nonneg _) (by linarith)
      _ ≤ B ^ 2 * (c4 * T) := by
          have : B ≤ B ^ 2 := by nlinarith
          calc B * Real.log T ^ 4 ≤ B * (c4 * T) := mul_le_mul_of_nonneg_left h4' (by linarith)
            _ ≤ B ^ 2 * (c4 * T) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = κ * (T / (4 * Real.pi)) := hBT
      _ ≤ κ * Z.N T (2 * T) := mul_le_mul_of_nonneg_left hNT hκ.le
  · calc wallN Z T ^ 2 ≤ (1600 * A₀ * L ^ 2) ^ 2 := pow_le_pow_left₀ hw0 hw 2
      _ = (1600 * A₀) ^ 2 * L ^ 4 := by ring
      _ ≤ B ^ 2 * Real.log T ^ 4 := by
          have : (1600 * A₀) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by linarith) (by rw [hB]; linarith) 2
          exact mul_le_mul this hL4 (by positivity) (by positivity)
      _ ≤ B ^ 2 * (c4 * T) := mul_le_mul_of_nonneg_left h4' (by positivity)
      _ = κ * (T / (4 * Real.pi)) := hBT
      _ ≤ κ * Z.N T (2 * T) := mul_le_mul_of_nonneg_left hNT hκ.le
  · have hd : ((mtParams T).d T : ℝ) ≤ (mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le (by
      have : 0 < (mtParams T).L T := by show 0 < L; linarith
      positivity)
    have hLm : (mtParams T).L T = L := rfl
    rw [hLm] at hd
    have : κ * (T / (4 * Real.pi)) ≤ κ * Z.N T (2 * T) := mul_le_mul_of_nonneg_left hNT hκ.le
    have e : L * T / (2 * Real.pi) = T * L / (2 * Real.pi) := by ring
    linarith

theorem kfunAM_zero : AMW.kfunAM 0 = 1 := by
  unfold AMW.kfunAM; exact div_self AMW.KfunAM_zero_pos.ne'

theorem natFloor_le_of_le {y z : ℝ} (hz : 0 ≤ z) (h : y ≤ z) : (⌊y⌋₊ : ℝ) ≤ z := by
  rcases le_or_gt 0 y with hy | hy
  · exact (Nat.floor_le hy).trans h
  · rw [Nat.floor_of_nonpos hy.le, Nat.cast_zero]; exact hz

end Zeta23Ext.Bridge

end
