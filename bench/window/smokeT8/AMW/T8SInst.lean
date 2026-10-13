import AMW.AMTail

/-! smoke test of the n = 8 tail generator only: the certificate below is a STUB (`sorry`), never assembled for upload. -/

noncomputable section

namespace AMW.Cert

def wfun (x : ℝ) : ℝ := AMW.wfunAM x

namespace T8S

def SA : ℕ := 100000000
def cN : ℕ := 804359

def G (g0 g1 g2 g3 g4 g5 g6 : ℝ) : ℝ :=
  (28898 / (SA:ℝ)) * g0
    + (57272 / (SA:ℝ)) * g1
    + (75526 / (SA:ℝ)) * g2
    + (80958 / (SA:ℝ)) * g3
    + (75526 / (SA:ℝ)) * g4
    + (57272 / (SA:ℝ)) * g5
    + (28898 / (SA:ℝ)) * g6
    + (13630830 / (SA:ℝ)) * wfun (g0)
    + (0 / (SA:ℝ)) * wfun (g0 + g1)
    + (19565904 / (SA:ℝ)) * wfun (g0 + g1 + g2)
    + (20317441 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3)
    + (45030671 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4)
    + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5)
    + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6)
    + (29997996 / (SA:ℝ)) * wfun (g1)
    + (30621878 / (SA:ℝ)) * wfun (g1 + g2)
    + (47766489 / (SA:ℝ)) * wfun (g1 + g2 + g3)
    + (79682558 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4)
    + (109938656 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5)
    + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6)
    + (37356140 / (SA:ℝ)) * wfun (g2)
    + (69378121 / (SA:ℝ)) * wfun (g2 + g3)
    + (65335210 / (SA:ℝ)) * wfun (g2 + g3 + g4)
    + (79682558 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5)
    + (45030671 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6)
    + (38030065 / (SA:ℝ)) * wfun (g3)
    + (69378121 / (SA:ℝ)) * wfun (g3 + g4)
    + (47766489 / (SA:ℝ)) * wfun (g3 + g4 + g5)
    + (20317441 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6)
    + (37356140 / (SA:ℝ)) * wfun (g4)
    + (30621878 / (SA:ℝ)) * wfun (g4 + g5)
    + (19565904 / (SA:ℝ)) * wfun (g4 + g5 + g6)
    + (29997996 / (SA:ℝ)) * wfun (g5)
    + (0 / (SA:ℝ)) * wfun (g5 + g6)
    + (13630830 / (SA:ℝ)) * wfun (g6)

end T8S

theorem T8S_cert_full : ∀ x0 x1 x2 x3 x4 x5 x6 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → 0 ≤ x5 → 0 ≤ x6 →
    (T8S.cN : ℝ) / T8S.SA ≤ T8S.G x0 x1 x2 x3 x4 x5 x6 := by
  sorry

end AMW.Cert
