import AMW.CEngine

/-!
# AMW/CWindow — `wfunAM ≥ 1/4` on `[0, 1/2]` (stage G)

On `[0, 1/4]`: `kfunAM x ≥ cos(πx) ≥ √2/2` (the window is positive on `[−½, ½]` and `cos(2πxt) ≥ cos(πx)` there).
On `[1/4, 1/2]`: sixteen cells of width `1/64`, each checked by the AM cell evaluator.
-/

noncomputable section

open Real

namespace AMW.Cert

theorem kfunAM_ge_cos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.cos (π * x) ≤ AMW.kfunAM x := by
  have hK0 := AMW.KfunAM_zero_pos
  unfold AMW.kfunAM
  rw [le_div_iff₀ hK0, AMW.KfunAM_zero]
  unfold AMW.KfunAM
  have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
  · exact (continuous_const.mul AMW.vAM_continuous).intervalIntegrable _ _
  · exact (AMW.vAM_continuous.mul (by fun_prop : Continuous fun t : ℝ => Real.cos (2 * π * x * t))).intervalIntegrable _ _
  · intro t ht
    have hv := AMW.vAM_pos_on ht
    have habs : |2 * π * x * t| ≤ π * x := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * x)]
      have : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have hpx : 0 ≤ π * x := mul_nonneg Real.pi_pos.le h0
      have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 2 * π * x)
      linarith
    have hcos : Real.cos (π * x) ≤ Real.cos (2 * π * x * t) := by
      rw [← Real.cos_abs (2 * π * x * t)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by nlinarith [Real.pi_pos]) habs
    calc Real.cos (π * x) * AMW.vAM t ≤ Real.cos (2 * π * x * t) * AMW.vAM t := mul_le_mul_of_nonneg_right hcos hv.le
      _ = AMW.vAM t * Real.cos (2 * π * x * t) := mul_comm _ _

theorem wfun_quarter_low {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) : (1 / 4 : ℝ) ≤ wfun x := by
  have hk := kfunAM_ge_cos h0 (by linarith)
  have hc : Real.sqrt 2 / 2 ≤ Real.cos (π * x) := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hk' : Real.sqrt 2 / 2 ≤ AMW.kfunAM x := hc.trans hk
  unfold wfun AMW.wfunAM
  nlinarith

/-- the sixteen window cells `[8192 + 512 i, 8704 + 512 i] / SC` -/
def winCell (i : ℕ) : AMW.G.CellA := ⟨8192 + 512 * i, 8704 + 512 * i⟩

def winOk (i : ℕ) : Bool := (winCell i).ok && Nat.ble (Nat.mul AMW.G.DZ AMW.G.DZ) (Nat.mul 4 (Nat.mul (winCell i).KAn (winCell i).KAn))

theorem winOk_all : Pyr.allBelow 16 winOk = true := by decide +kernel

theorem wfun_quarter_high {x : ℝ} (h0 : 1 / 4 ≤ x) (h1 : x ≤ 1 / 2) : (1 / 4 : ℝ) ≤ wfun x := by
  have hall := Pyr.allBelow_spec winOk_all
  -- the cell index
  obtain ⟨i, hi, hx1, hx2⟩ : ∃ i < 16, ((8192 + 512 * i : ℕ) : ℝ) / AMW.G.SC ≤ x ∧ x ≤ ((8704 + 512 * i : ℕ) : ℝ) / AMW.G.SC := by
    have hSC : (AMW.G.SC : ℝ) = 32768 := by norm_num [AMW.G.SC]
    by_cases hx : x = 1 / 2
    · exact ⟨15, by norm_num, by rw [hSC, hx]; norm_num, by rw [hSC, hx]; norm_num⟩
    · have hlt : x < 1 / 2 := lt_of_le_of_ne h1 hx
      set n := ⌊(x - 1 / 4) * 64⌋₊ with hn
      have hn0 : (0 : ℝ) ≤ (x - 1 / 4) * 64 := by linarith
      have hnle := Nat.floor_le hn0
      have hnlt := Nat.lt_floor_add_one ((x - 1 / 4) * 64)
      have hn16 : n < 16 := by
        have : (n : ℝ) < 16 := by linarith
        exact_mod_cast this
      refine ⟨n, hn16, ?_, ?_⟩ <;> rw [hSC] <;> push_cast <;> linarith
  have hc := hall i hi
  unfold winOk at hc
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨hok, hK⟩ := hc
  have hw := (winCell i).w_lower hok (x := x) hx1 hx2
  have hD := AMW.G.DZ_pos
  generalize (winCell i).KAn = K at hK hw
  have hK' : (AMW.G.DZ : ℝ) * AMW.G.DZ ≤ 4 * ((K : ℝ) * K) := by
    have := (Nat.cast_le (α := ℝ)).mpr hK; simp only [Nat.mul_eq] at this; push_cast at this; exact this
  unfold wfun
  refine le_trans ?_ hw
  generalize (AMW.G.DZ : ℝ) = D at hD hK' ⊢
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith

theorem wfun_window (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 / 4 : ℝ) ≤ wfun x := by
  rcases le_total x (1 / 4) with h | h
  · exact wfun_quarter_low h0 h
  · exact wfun_quarter_high h h1

end AMW.Cert
