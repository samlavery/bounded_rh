import AMW.DEQfH

/-! ###### AMW/DEQfZero — a rational lower bound on `qf(0)` (mvt-engine; D track)

`qf(0) = Σ_i qA0 i` (the closed form at `0`: `cos 0 = 1`, `sin 0 = 0`), bounded below by the lower ends of the
coefficient table `qA0T` (`AMW/DEQfIv`).  The true value is `1.0082637790`; the bound is `1.0082637`. ###### -/

noncomputable section

open Real

namespace AMW.DE

open AMW.DQ

theorem qf0_zero : qf0 0 = ∑ i ∈ Finset.range 13, qA0 i := by
  unfold qf0 trigF; simp

theorem qA0T_lo_sum : (10082637 / 10000000 : ℚ) ≤ qsum (fun i => (qA0T i).1) 13 := by decide +kernel

theorem qfAM_zero_ge : (10082637 / 10000000 : ℝ) ≤ qfAM 0 := by
  rw [qfAM_eq_on le_rfl zero_le_one, qfAM_eq_trig, qf0_zero]
  have hs : ((qsum (fun i => (qA0T i).1) 13 : ℚ) : ℝ) ≤ ∑ i ∈ Finset.range 13, qA0 i := by
    rw [qsum_cast]
    exact Finset.sum_le_sum fun i hi => (iv_qA0T (Finset.mem_range.mp hi)).1
  have hr : ((10082637 / 10000000 : ℚ) : ℝ) ≤ ((qsum (fun i => (qA0T i).1) 13 : ℚ) : ℝ) := by
    exact_mod_cast qA0T_lo_sum
  have e : ((10082637 / 10000000 : ℚ) : ℝ) = (10082637 / 10000000 : ℝ) := by push_cast; ring
  rw [e] at hr
  exact hr.trans hs

end AMW.DE

#print axioms AMW.DE.qfAM_zero_ge
