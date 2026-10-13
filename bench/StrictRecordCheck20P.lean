-- standalone check for the SixW20P candidate (κ = 3365271/5000000), against the board record 67291431/100000000:
--   (1) the strict-improvement step, by the tail's own `strict` tactic on the literal values;
--   (2) κ is at most the constant the candidate proves, `(7225000000·HD 1 − 12779787)/7200070409`, from the
--       candidate's enclosure `RiemannFail.HD_one_bounds` (the shared CandidateSpec is not modified).
import Cand20P

example : (67291431 : ℝ) / 100000000 < (3365271 : ℝ) / 5000000 := by
  first
    | (norm_num; done)

example : ¬ ((3365271 : ℝ) / 5000000 < (67291431 : ℝ) / 100000000) := by norm_num

example : (3365271 : ℝ) / 5000000 ≤ (7225000000 * Zeta23.ThmD.HD 1 - 12779787) / 7200070409 := by
  rw [le_div_iff₀ (by norm_num)]
  linarith [RiemannFail.HD_one_bounds.1]

-- the proved bound itself, at that constant
#check @RiemannFail.bound_WW
#print axioms RiemannFail.bound_WW
