-- standalone checks for the SixW25P candidate (κ = 6730423/10000000), built against the private spec
-- (record 33649269/50000000, candidate 6730423/10000000); the shared CandidateSpec is not modified.
import Cand25P

-- the board records: the one named in the task (67291431/100000000) and the current one (33649269/50000000)
example : (67291431 : ℝ) / 100000000 < (6730423 : ℝ) / 10000000 := by
  first
    | (norm_num; done)
example : (33649269 : ℝ) / 50000000 < (6730423 : ℝ) / 10000000 := by
  first
    | (norm_num; done)
example : currentRecordKappa = (33649269 : ℝ) / 50000000 := rfl
example : candidateKappa = (6730423 : ℝ) / 10000000 := rfl

-- κ is at most the constant the candidate proves, from the candidate's own enclosure of HD 1
example : (6730423 : ℝ) / 10000000 ≤ (14550000000 * Zeta23.ThmD.HD 1 - 25739571) / 14500045810 := by
  rw [le_div_iff₀ (by norm_num)]
  linarith [RiemannFail.HD_one_bounds.1]

#check @RiemannFail.bound_WW
#print axioms RiemannFail.bound_WW
#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
