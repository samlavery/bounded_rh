import AMW.CMin

/-! ###### the range lemmas of mvt-engine's MinCore added after the AMR7 port (`AMW/CMin` is that port, unchanged):
pair-sum ranges one gap at a time, so the instance proofs avoid `linarith` on the ranges ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

theorem slo_add {A a : ℕ} {X x : ℝ} (h : (A : ℝ) / SC ≤ X) (h' : (a : ℝ) / SC ≤ x) : ((A + a : ℕ) : ℝ) / SC ≤ X + x := by
  push_cast; rw [add_div]; exact add_le_add h h'
theorem shi_add {A a : ℕ} {X x : ℝ} (h : X ≤ (A : ℝ) / SC) (h' : x ≤ (a : ℝ) / SC) : X + x ≤ ((A + a : ℕ) : ℝ) / SC := by
  push_cast; rw [add_div]; exact add_le_add h h'

end AMW.Cert.PyrD

end
