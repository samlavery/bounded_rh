
/-! ###### the 6-point weighted bound from the checked certificate `SixW6` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW Zeta23Ext.Bridge.ThreePoint

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW : Fin 6 → Fin 6 → ℝ
  | 0, 1 => (25326800 : ℝ) / 100000000
  | 0, 2 => (62369200 : ℝ) / 100000000
  | 0, 3 => (40126500 : ℝ) / 100000000
  | 0, 4 => (99999900 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (48244400 : ℝ) / 100000000
  | 1, 3 => (37630700 : ℝ) / 100000000
  | 1, 4 => (119746800 : ℝ) / 100000000
  | 1, 5 => (99999900 : ℝ) / 100000000
  | 2, 3 => (52857300 : ℝ) / 100000000
  | 2, 4 => (37630700 : ℝ) / 100000000
  | 2, 5 => (40126500 : ℝ) / 100000000
  | 3, 4 => (48244400 : ℝ) / 100000000
  | 3, 5 => (62369200 : ℝ) / 100000000
  | 4, 5 => (25326800 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ
  | 0 => (24896 : ℝ) / 100000000
  | 1 => (42034 : ℝ) / 100000000
  | 2 => (46137 : ℝ) / 100000000
  | 3 => (42034 : ℝ) / 100000000
  | 4 => (24896 : ℝ) / 100000000

def WW : WCert 6 := ⟨aW, bW⟩

theorem aW_0_0 : aW 0 0 = 0 := rfl
theorem aW_0_1 : aW 0 1 = (25326800 : ℝ) / 100000000 := rfl
theorem aW_0_2 : aW 0 2 = (62369200 : ℝ) / 100000000 := rfl
theorem aW_0_3 : aW 0 3 = (40126500 : ℝ) / 100000000 := rfl
theorem aW_0_4 : aW 0 4 = (99999900 : ℝ) / 100000000 := rfl
theorem aW_0_5 : aW 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW_1_0 : aW 1 0 = 0 := rfl
theorem aW_1_1 : aW 1 1 = 0 := rfl
theorem aW_1_2 : aW 1 2 = (48244400 : ℝ) / 100000000 := rfl
theorem aW_1_3 : aW 1 3 = (37630700 : ℝ) / 100000000 := rfl
theorem aW_1_4 : aW 1 4 = (119746800 : ℝ) / 100000000 := rfl
theorem aW_1_5 : aW 1 5 = (99999900 : ℝ) / 100000000 := rfl
theorem aW_2_0 : aW 2 0 = 0 := rfl
theorem aW_2_1 : aW 2 1 = 0 := rfl
theorem aW_2_2 : aW 2 2 = 0 := rfl
theorem aW_2_3 : aW 2 3 = (52857300 : ℝ) / 100000000 := rfl
theorem aW_2_4 : aW 2 4 = (37630700 : ℝ) / 100000000 := rfl
theorem aW_2_5 : aW 2 5 = (40126500 : ℝ) / 100000000 := rfl
theorem aW_3_0 : aW 3 0 = 0 := rfl
theorem aW_3_1 : aW 3 1 = 0 := rfl
theorem aW_3_2 : aW 3 2 = 0 := rfl
theorem aW_3_3 : aW 3 3 = 0 := rfl
theorem aW_3_4 : aW 3 4 = (48244400 : ℝ) / 100000000 := rfl
theorem aW_3_5 : aW 3 5 = (62369200 : ℝ) / 100000000 := rfl
theorem aW_4_0 : aW 4 0 = 0 := rfl
theorem aW_4_1 : aW 4 1 = 0 := rfl
theorem aW_4_2 : aW 4 2 = 0 := rfl
theorem aW_4_3 : aW 4 3 = 0 := rfl
theorem aW_4_4 : aW 4 4 = 0 := rfl
theorem aW_4_5 : aW 4 5 = (25326800 : ℝ) / 100000000 := rfl
theorem aW_5_0 : aW 5 0 = 0 := rfl
theorem aW_5_1 : aW 5 1 = 0 := rfl
theorem aW_5_2 : aW 5 2 = 0 := rfl
theorem aW_5_3 : aW 5 3 = 0 := rfl
theorem aW_5_4 : aW 5 4 = 0 := rfl
theorem aW_5_5 : aW 5 5 = 0 := rfl
theorem bW_0 : bW 0 = (24896 : ℝ) / 100000000 := rfl
theorem bW_1 : bW 1 = (42034 : ℝ) / 100000000 := rfl
theorem bW_2 : bW 2 = (46137 : ℝ) / 100000000 := rfl
theorem bW_3 : bW 3 = (42034 : ℝ) / 100000000 := rfl
theorem bW_4 : bW 4 = (24896 : ℝ) / 100000000 := rfl

theorem WW_B : WW.B = (179997 : ℝ) / 100000000 := by
  show (∑ r : Fin 5, bW r) = _
  norm_num [Fin.sum_univ_five, bW_0, bW_1, bW_2, bW_3, bW_4]

theorem WW_a_nonneg : ∀ i j, 0 ≤ WW.a i j := by
  intro i j
  unfold WW
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW 0 0; norm_num [aW_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW 0 1; norm_num [aW_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW 0 2; norm_num [aW_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW 0 3; norm_num [aW_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW 0 4; norm_num [aW_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW 0 5; norm_num [aW_0_5]
  | 1, 0 => show (0:ℝ) ≤ aW 1 0; norm_num [aW_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW 1 1; norm_num [aW_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW 1 2; norm_num [aW_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW 1 3; norm_num [aW_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW 1 4; norm_num [aW_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW 1 5; norm_num [aW_1_5]
  | 2, 0 => show (0:ℝ) ≤ aW 2 0; norm_num [aW_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW 2 1; norm_num [aW_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW 2 2; norm_num [aW_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW 2 3; norm_num [aW_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW 2 4; norm_num [aW_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW 2 5; norm_num [aW_2_5]
  | 3, 0 => show (0:ℝ) ≤ aW 3 0; norm_num [aW_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW 3 1; norm_num [aW_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW 3 2; norm_num [aW_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW 3 3; norm_num [aW_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW 3 4; norm_num [aW_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW 3 5; norm_num [aW_3_5]
  | 4, 0 => show (0:ℝ) ≤ aW 4 0; norm_num [aW_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW 4 1; norm_num [aW_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW 4 2; norm_num [aW_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW 4 3; norm_num [aW_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW 4 4; norm_num [aW_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW 4 5; norm_num [aW_4_5]
  | 5, 0 => show (0:ℝ) ≤ aW 5 0; norm_num [aW_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW 5 1; norm_num [aW_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW 5 2; norm_num [aW_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW 5 3; norm_num [aW_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW 5 4; norm_num [aW_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW 5 5; norm_num [aW_5_5]

theorem WW_bmin : ∀ r, ((24896 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((24896 : ℝ) / 100000000) ≤ bW 0; norm_num [bW_0]
  | 1 => show ((24896 : ℝ) / 100000000) ≤ bW 1; norm_num [bW_1]
  | 2 => show ((24896 : ℝ) / 100000000) ≤ bW 2; norm_num [bW_2]
  | 3 => show ((24896 : ℝ) / 100000000) ≤ bW 3; norm_num [bW_3]
  | 4 => show ((24896 : ℝ) / 100000000) ≤ bW 4; norm_num [bW_4]

theorem WW_capacity : ∀ s : ℕ, WW.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass WW
  rcases lt_or_ge s 6 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_six, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 6, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem WW_adm : WW.Adm := ⟨WW_a_nonneg, fun r => le_trans (by norm_num) (WW_bmin r), WW_capacity⟩

private lemma sumQ (f : Fin (6 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4
  exact Fin.sum_univ_five f

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW6.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW6.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW6.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW6.SA]
  try ring

theorem G_rev (x0 x1 x2 x3 x4 : ℝ) : SixW6.G x4 x3 x2 x1 x0 = SixW6.G x0 x1 x2 x3 x4 := by
  unfold SixW6.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (SixW6.cN : ℝ) / SixW6.SA ≤ SixW6.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases SixW6Data.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases SixW6Data.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (336790 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW6.cN, SixW6.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 301 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((336790 : ℝ) / 100000000) 301 ((179997 : ℝ) / 100000000)
    = (3762500000 * HD 1 - 6659889) / 3750038770 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3762500000 * HD 1 - 6659889) / 3750038770 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((336790 : ℝ) / 100000000) 301 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (3762500000 * HD 1 - 6659889) / 3750038770 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3750038770)]
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
      ≤ ((3762500000 * HD 1 - 6659889) / 3750038770 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [candidateKappa_le]) hN
  linarith

/-- The cumulative form, through the library's dyadic-to-cumulative wrapper. -/
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

/-- Strict improvement over the record.  The board pins `currentRecordKappa` as the exact rational
of the last accepted candidate, so the comparison is decided by `norm_num`; the second branch covers
the original closed form `2 - 1/cMT = HD 1`, through `cStar_one_eq_cMT` and the enclosure of `HD 1`. -/
theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  first
    | (norm_num; done)
    | (rw [← cStar_one_eq_cMT]
       have h := HD_one_bounds.2
       unfold Zeta23.ThmD.HD at h
       linarith)

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

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
