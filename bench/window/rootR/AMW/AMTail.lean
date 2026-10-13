/-
AMW/AMTail.lean — the end state of the retargeted bridge: the seven-point weighted bound for the AMTOPA
window from a certificate hypothesis.

For any admissible weight certificate W : WCert 7 and c, m with `∀ g ≥ 0, c ≤ Fw W g` (Fw over
`wfun = AMW.wfunAM`), `n_point_bound_w'` gives (Phi_w' 7 c m B − ε)·N ≤ N0simple ≤ N0star, with
Phi_w' 7 c m B = (HW − B(m−6)/m)/(1 − c(m−6)/m); `Phi_w'_ge` reduces κ ≤ Phi_w' to a rational inequality
through `HW_ge : 6722198/10⁷ ≤ HW`.  `WAMT` is the certificate with AMTOPA's pair weights and per-gap
pressures (B = 93/23000).  Adapted from the submission layer of SolutionSevW10D.lean.
-/
import AMW.BrC

noncomputable section

open Filter

namespace AMW

open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star' (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩

/-- `κ ≤ Phi_w' 7 c m B` from the floor of `HW`. -/
theorem Phi_w'_ge {c B κ : ℝ} {m : ℕ} (hm : 0 < m) (hD : c * ((m : ℝ) - 6) < m)
    (h : κ * (1 - c * ((m : ℝ) - 6) / m) ≤ 6722198 / 10 ^ 7 - B * ((m : ℝ) - 6) / m) :
    κ ≤ Phi_w' 7 c m B := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : 0 < 1 - c * ((m : ℝ) - 6) / m := by
    rw [sub_pos, div_lt_one hm']; exact hD
  unfold Phi_w'
  rw [show ((7 : ℕ) : ℝ) - 1 = 6 by norm_num, le_div_iff₀ hD']
  linarith [HW_ge]

/-- **The seven-point bound for the AMTOPA window**, from a certificate for `Fw W`. -/
theorem am_dyadic {W : WCert 7} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 14 ≤ m) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (hκ : κ ≤ Phi_w' 7 c m W.B)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w' 7 c m W (by norm_num) (by omega) hW hbmin hb hc hCert
    (by push_cast; linarith) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_w' 7 c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- The cumulative form. -/
theorem am_cumulative {W : WCert 7} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 14 ≤ m) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (hκ : κ ≤ Phi_w' 7 c m W.B)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic hW hbmin hb hc hm hA0 hκ hCert)

/-! ### general n, and the six-point instance -/

/-- `κ ≤ Phi_w' n c m B` from the floor of `HW`. -/
theorem Phi_w'_ge_n {n : ℕ} {c B κ : ℝ} {m : ℕ} (hm : 0 < m) (hD : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (h : κ * (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) ≤ 6722198 / 10 ^ 7 - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) :
    κ ≤ Phi_w' n c m B := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : 0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
    rw [sub_pos, div_lt_one hm']; exact hD
  unfold Phi_w'
  rw [le_div_iff₀ hD']
  linarith [HW_ge]

/-- **The n-point bound for the AMTOPA window**, from a certificate for `Fw W`. -/
theorem am_dyadic_n {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin)
    (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) (hκ : κ ≤ Phi_w' n c m W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w' n c m W hn hm hW hbmin hb hc hCert hA0 ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- `κ ≤ Phi_w' 6 c m B` from the floor of `HW` (q = 5). -/
theorem Phi_w'_ge6 {c B κ : ℝ} {m : ℕ} (hm : 0 < m) (hD : c * ((m : ℝ) - 5) < m)
    (h : κ * (1 - c * ((m : ℝ) - 5) / m) ≤ 6722198 / 10 ^ 7 - B * ((m : ℝ) - 5) / m) :
    κ ≤ Phi_w' 6 c m B :=
  Phi_w'_ge_n (n := 6) hm (by norm_num; linarith) (by norm_num; linarith)

/-- **The six-point bound for the AMTOPA window**, from a certificate for `Fw W`. -/
theorem am_dyadic6 {W : WCert 6} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 12 ≤ m) (hA0 : c * ((m : ℝ) - 5) ≤ 1)
    (hκ : κ ≤ Phi_w' 6 c m W.B)
    (hCert : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_n (n := 6) (by norm_num) hW hbmin hb hc (by omega) (by norm_num; linarith) hκ hCert

/-- The six-point cumulative form. -/
theorem am_cumulative6 {W : WCert 6} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 12 ≤ m) (hA0 : c * ((m : ℝ) - 5) ≤ 1)
    (hκ : κ ≤ Phi_w' 6 c m W.B)
    (hCert : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic6 hW hbmin hb hc hm hA0 hκ hCert)

/-! ### AMTOPA's pair weights and per-gap pressures -/

/-- the pair weights `a_ij` (zero unless `i < j`), over `10⁹` (AMTOPA_PAIRS). -/
def aAMT : Fin 7 → Fin 7 → ℝ :=
  ![![0, 244109993 / 10 ^ 9, 0, 254223074 / 10 ^ 9, 1, 1, 2],
    ![0, 0, 346264551 / 10 ^ 9, 368129744 / 10 ^ 9, 745776926 / 10 ^ 9, 0, 1],
    ![0, 0, 0, 409625456 / 10 ^ 9, 1263740512 / 10 ^ 9, 745776926 / 10 ^ 9, 1],
    ![0, 0, 0, 0, 409625456 / 10 ^ 9, 368129744 / 10 ^ 9, 254223074 / 10 ^ 9],
    ![0, 0, 0, 0, 0, 346264551 / 10 ^ 9, 0],
    ![0, 0, 0, 0, 0, 0, 244109993 / 10 ^ 9],
    ![0, 0, 0, 0, 0, 0, 0]]

/-- the per-gap pressures, over `46·10⁹` (AMTOPA_B). -/
def bAMT : Fin 6 → ℝ :=
  ![22420713 / 46000000000, 32878293 / 46000000000, 37700994 / 46000000000,
    37700994 / 46000000000, 32878293 / 46000000000, 22420713 / 46000000000]

def WAMT : WCert 7 := ⟨aAMT, bAMT⟩

theorem WAMT_B : WAMT.B = 93 / 23000 := by
  show (∑ r : Fin 6, bAMT r) = _
  simp [Fin.sum_univ_six, bAMT]; norm_num

theorem WAMT_bmin : ∀ r, (22420713 / 46000000000 : ℝ) ≤ WAMT.b r := by
  intro r
  show _ ≤ bAMT r
  fin_cases r <;> simp [bAMT] <;> norm_num

theorem WAMT_adm : WAMT.Adm where
  a_nonneg := by
    intro i j
    show 0 ≤ aAMT i j
    fin_cases i <;> fin_cases j <;> simp [aAMT] <;> norm_num
  b_nonneg := fun r => le_trans (by norm_num) (WAMT_bmin r)
  capacity := by
    intro s
    unfold WCert.spanMass
    show (∑ i : Fin 7, ∑ j : Fin 7, if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then aAMT i j else 0) ≤ 2
    rcases lt_or_ge s 7 with hs | hs
    · interval_cases s <;> simp [Fin.sum_univ_seven, aAMT] <;> norm_num
    · have h0 : ∀ i j : Fin 7, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
        intro i j ⟨_, h⟩
        have := j.2
        omega
      simp only [h0, if_false, Finset.sum_const_zero]
      norm_num

end AMW

end
