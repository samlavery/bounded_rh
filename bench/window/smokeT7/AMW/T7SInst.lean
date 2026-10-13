import AMW.AMTail

/-! smoke test of the n = 7 tail generator only: the certificate below is a STUB (`sorry`), never assembled for upload. -/

noncomputable section

namespace AMW.Cert

def wfun (x : ℝ) : ℝ := AMW.wfunAM x

namespace T7S

def SA : ℕ := 100000000
def cN : ℕ := 786661

def G (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  (43281 / (SA:ℝ)) * g0
    + (71389 / (SA:ℝ)) * g1
    + (85330 / (SA:ℝ)) * g2
    + (85330 / (SA:ℝ)) * g3
    + (71389 / (SA:ℝ)) * g4
    + (43281 / (SA:ℝ)) * g5
    + (21531053 / (SA:ℝ)) * wfun (g0)
    + (7880362 / (SA:ℝ)) * wfun (g0 + g1)
    + (24799396 / (SA:ℝ)) * wfun (g0 + g1 + g2)
    + (74525146 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3)
    + (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4)
    + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5)
    + (35099970 / (SA:ℝ)) * wfun (g1)
    + (52687248 / (SA:ℝ)) * wfun (g1 + g2)
    + (75200603 / (SA:ℝ)) * wfun (g1 + g2 + g3)
    + (50949707 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4)
    + (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5)
    + (43368975 / (SA:ℝ)) * wfun (g2)
    + (78864778 / (SA:ℝ)) * wfun (g2 + g3)
    + (75200603 / (SA:ℝ)) * wfun (g2 + g3 + g4)
    + (74525146 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5)
    + (43368975 / (SA:ℝ)) * wfun (g3)
    + (52687248 / (SA:ℝ)) * wfun (g3 + g4)
    + (24799396 / (SA:ℝ)) * wfun (g3 + g4 + g5)
    + (35099970 / (SA:ℝ)) * wfun (g4)
    + (7880362 / (SA:ℝ)) * wfun (g4 + g5)
    + (21531053 / (SA:ℝ)) * wfun (g5)

end T7S

theorem T7S_cert_full : ∀ x0 x1 x2 x3 x4 x5 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → 0 ≤ x5 →
    (T7S.cN : ℝ) / T7S.SA ≤ T7S.G x0 x1 x2 x3 x4 x5 := by
  sorry

end AMW.Cert
