import AMW.AMTail
open AMW Zeta23Ext.BridgeW
example (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → (78927 / 10 ^ 7 : ℝ) ≤ Fw WAMT g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((67340 / 100000 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic WAMT_adm (by norm_num) WAMT_bmin (by norm_num) (m := 132) (by norm_num) (by norm_num)
    (by rw [WAMT_B]; exact Phi_w'_ge (by norm_num) (by norm_num) (by norm_num)) hCert
#print axioms am_dyadic
#print axioms am_cumulative
#print axioms WAMT_adm
#print axioms Phi_w'_ge
