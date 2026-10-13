-- standalone check: the strict-improvement step against the board record 67291431/100000000
-- (same tactic as the tail's `strict`, on the literal values; the shared CandidateSpec is not modified)
import ChallengeDeps.CandidateSpec

example : (67291431 : ℝ) / 100000000 < (6730187 : ℝ) / 10000000 := by
  first
    | (norm_num; done)

example : ¬ ((6730187 : ℝ) / 10000000 < (67291431 : ℝ) / 100000000) := by norm_num

#check @currentRecordKappa
