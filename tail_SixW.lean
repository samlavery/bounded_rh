
/-! ###### the 6-point weighted bound from the checked certificate `SixW` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW Zeta23Ext.Bridge.ThreePoint

/-- the pair weights, row `i`, column `j`, over `100000000` -/
def aW : Fin 6 → Fin 6 → ℝ :=
  ![![0, (25715100 : ℝ) / 100000000, (61242800 : ℝ) / 100000000, (40905100 : ℝ) / 100000000, (104929600 : ℝ) / 100000000, (200000000 : ℝ) / 100000000], ![0, 0, (48318100 : ℝ) / 100000000, (40072400 : ℝ) / 100000000, (119746800 : ℝ) / 100000000, (95070300 : ℝ) / 100000000], ![0, 0, 0, (52857300 : ℝ) / 100000000, (35189000 : ℝ) / 100000000, (39348000 : ℝ) / 100000000], ![0, 0, 0, 0, (48170700 : ℝ) / 100000000, (63495600 : ℝ) / 100000000], ![0, 0, 0, 0, 0, (24938600 : ℝ) / 100000000], ![0, 0, 0, 0, 0, 0]]

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ := ![(25232 : ℝ) / 100000000, (42025 : ℝ) / 100000000, (46137 : ℝ) / 100000000, (42044 : ℝ) / 100000000, (24559 : ℝ) / 100000000]

def WW : WCert 6 := ⟨aW, bW⟩

theorem WW_B : WW.B = (179997 : ℝ) / 100000000 := by
  unfold WCert.B WW bW
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

theorem WW_a_nonneg : ∀ i j, 0 ≤ WW.a i j := by
  intro i j
  unfold WW aW
  fin_cases i <;> fin_cases j <;> norm_num

theorem WW_bmin : ∀ r, ((24559 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW bW
  fin_cases r <;> norm_num

theorem WW_capacity : ∀ s : ℕ, WW.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass WW aW
  rcases lt_or_ge s 6 with hs | hs
  · interval_cases s <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
  · have h0 : ∀ i j : Fin 6, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem WW_adm : WW.Adm := ⟨WW_a_nonneg, fun r => le_trans (by norm_num) (WW_bmin r), WW_capacity⟩

private lemma sumQ (f : Fin (6 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW.G g 0 g 1 g 2 g 3 g 4 := by
  unfold Fw WW aW bW SixW.G ptsN
  simp only [sumQ, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.cons_val]
  norm_num [SixW.SA]
  try ring

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (347539 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := SixWData.cert g 0 g 1 g 2 g 3 g 4 (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW.cN, SixW.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 292 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((347539 : ℝ) / 100000000) 292 ((179997 : ℝ) / 100000000)
    = (29200000000 * HD 1 - 51659139) / 29100256307 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((29200000000 * HD 1 - 51659139) / 29100256307 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((347539 : ℝ) / 100000000) 292 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24559 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (29200000000 * HD 1 - 51659139) / 29100256307 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 29100256307)]
  linarith [HD_one_bounds.1]

/-- The dyadic bound at the candidate rational, in the library's vocabulary. -/
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := bound_WW ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star T (2 * T)
  have h0 : (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ ((29200000000 * HD 1 - 51659139) / 29100256307 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [candidateKappa_le]) hN
  linarith

/-- The cumulative form, through the library's dyadic-to-cumulative wrapper. -/
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

/-- Strict improvement over the record. -/
theorem strict : currentRecordKappa < candidateKappa := by
  rw [currentRecordKappa_eq]
  unfold candidateKappa
  linarith [HD_one_bounds.2]

end RiemannFail

end

/-! ###### the three scored theorems, statements as generated by the trusted template ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative

end
