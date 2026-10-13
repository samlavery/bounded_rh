import ChallengeDeps.CandidateSpec
import AMW.T7SInst

set_option linter.all false
/-! ###### tail: the AM seven-point bound from the certificate `AMW.Cert.T7S_cert_full` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW7 : Fin 7 → Fin 7 → ℝ
  | 0, 1 => (21531053 : ℝ) / 100000000
  | 0, 2 => (7880362 : ℝ) / 100000000
  | 0, 3 => (24799396 : ℝ) / 100000000
  | 0, 4 => (74525146 : ℝ) / 100000000
  | 0, 5 => (99999999 : ℝ) / 100000000
  | 0, 6 => (200000000 : ℝ) / 100000000
  | 1, 2 => (35099970 : ℝ) / 100000000
  | 1, 3 => (52687248 : ℝ) / 100000000
  | 1, 4 => (75200603 : ℝ) / 100000000
  | 1, 5 => (50949707 : ℝ) / 100000000
  | 1, 6 => (99999999 : ℝ) / 100000000
  | 2, 3 => (43368975 : ℝ) / 100000000
  | 2, 4 => (78864778 : ℝ) / 100000000
  | 2, 5 => (75200603 : ℝ) / 100000000
  | 2, 6 => (74525146 : ℝ) / 100000000
  | 3, 4 => (43368975 : ℝ) / 100000000
  | 3, 5 => (52687248 : ℝ) / 100000000
  | 3, 6 => (24799396 : ℝ) / 100000000
  | 4, 5 => (35099970 : ℝ) / 100000000
  | 4, 6 => (7880362 : ℝ) / 100000000
  | 5, 6 => (21531053 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW7 : Fin 6 → ℝ
  | 0 => (43281 : ℝ) / 100000000
  | 1 => (71389 : ℝ) / 100000000
  | 2 => (85330 : ℝ) / 100000000
  | 3 => (85330 : ℝ) / 100000000
  | 4 => (71389 : ℝ) / 100000000
  | 5 => (43281 : ℝ) / 100000000

def W7 : WCert 7 := ⟨aW7, bW7⟩

theorem aW7_0_0 : aW7 0 0 = 0 := rfl
theorem aW7_0_1 : aW7 0 1 = (21531053 : ℝ) / 100000000 := rfl
theorem aW7_0_2 : aW7 0 2 = (7880362 : ℝ) / 100000000 := rfl
theorem aW7_0_3 : aW7 0 3 = (24799396 : ℝ) / 100000000 := rfl
theorem aW7_0_4 : aW7 0 4 = (74525146 : ℝ) / 100000000 := rfl
theorem aW7_0_5 : aW7 0 5 = (99999999 : ℝ) / 100000000 := rfl
theorem aW7_0_6 : aW7 0 6 = (200000000 : ℝ) / 100000000 := rfl
theorem aW7_1_0 : aW7 1 0 = 0 := rfl
theorem aW7_1_1 : aW7 1 1 = 0 := rfl
theorem aW7_1_2 : aW7 1 2 = (35099970 : ℝ) / 100000000 := rfl
theorem aW7_1_3 : aW7 1 3 = (52687248 : ℝ) / 100000000 := rfl
theorem aW7_1_4 : aW7 1 4 = (75200603 : ℝ) / 100000000 := rfl
theorem aW7_1_5 : aW7 1 5 = (50949707 : ℝ) / 100000000 := rfl
theorem aW7_1_6 : aW7 1 6 = (99999999 : ℝ) / 100000000 := rfl
theorem aW7_2_0 : aW7 2 0 = 0 := rfl
theorem aW7_2_1 : aW7 2 1 = 0 := rfl
theorem aW7_2_2 : aW7 2 2 = 0 := rfl
theorem aW7_2_3 : aW7 2 3 = (43368975 : ℝ) / 100000000 := rfl
theorem aW7_2_4 : aW7 2 4 = (78864778 : ℝ) / 100000000 := rfl
theorem aW7_2_5 : aW7 2 5 = (75200603 : ℝ) / 100000000 := rfl
theorem aW7_2_6 : aW7 2 6 = (74525146 : ℝ) / 100000000 := rfl
theorem aW7_3_0 : aW7 3 0 = 0 := rfl
theorem aW7_3_1 : aW7 3 1 = 0 := rfl
theorem aW7_3_2 : aW7 3 2 = 0 := rfl
theorem aW7_3_3 : aW7 3 3 = 0 := rfl
theorem aW7_3_4 : aW7 3 4 = (43368975 : ℝ) / 100000000 := rfl
theorem aW7_3_5 : aW7 3 5 = (52687248 : ℝ) / 100000000 := rfl
theorem aW7_3_6 : aW7 3 6 = (24799396 : ℝ) / 100000000 := rfl
theorem aW7_4_0 : aW7 4 0 = 0 := rfl
theorem aW7_4_1 : aW7 4 1 = 0 := rfl
theorem aW7_4_2 : aW7 4 2 = 0 := rfl
theorem aW7_4_3 : aW7 4 3 = 0 := rfl
theorem aW7_4_4 : aW7 4 4 = 0 := rfl
theorem aW7_4_5 : aW7 4 5 = (35099970 : ℝ) / 100000000 := rfl
theorem aW7_4_6 : aW7 4 6 = (7880362 : ℝ) / 100000000 := rfl
theorem aW7_5_0 : aW7 5 0 = 0 := rfl
theorem aW7_5_1 : aW7 5 1 = 0 := rfl
theorem aW7_5_2 : aW7 5 2 = 0 := rfl
theorem aW7_5_3 : aW7 5 3 = 0 := rfl
theorem aW7_5_4 : aW7 5 4 = 0 := rfl
theorem aW7_5_5 : aW7 5 5 = 0 := rfl
theorem aW7_5_6 : aW7 5 6 = (21531053 : ℝ) / 100000000 := rfl
theorem aW7_6_0 : aW7 6 0 = 0 := rfl
theorem aW7_6_1 : aW7 6 1 = 0 := rfl
theorem aW7_6_2 : aW7 6 2 = 0 := rfl
theorem aW7_6_3 : aW7 6 3 = 0 := rfl
theorem aW7_6_4 : aW7 6 4 = 0 := rfl
theorem aW7_6_5 : aW7 6 5 = 0 := rfl
theorem aW7_6_6 : aW7 6 6 = 0 := rfl
theorem bW7_0 : bW7 0 = (43281 : ℝ) / 100000000 := rfl
theorem bW7_1 : bW7 1 = (71389 : ℝ) / 100000000 := rfl
theorem bW7_2 : bW7 2 = (85330 : ℝ) / 100000000 := rfl
theorem bW7_3 : bW7 3 = (85330 : ℝ) / 100000000 := rfl
theorem bW7_4 : bW7 4 = (71389 : ℝ) / 100000000 := rfl
theorem bW7_5 : bW7 5 = (43281 : ℝ) / 100000000 := rfl

theorem W7_B : W7.B = (400000 : ℝ) / 100000000 := by
  show (∑ r : Fin 6, bW7 r) = _
  norm_num [Fin.sum_univ_six, bW7_0, bW7_1, bW7_2, bW7_3, bW7_4, bW7_5]

theorem W7_a_nonneg : ∀ i j, 0 ≤ W7.a i j := by
  intro i j
  unfold W7
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW7 0 0; norm_num [aW7_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW7 0 1; norm_num [aW7_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW7 0 2; norm_num [aW7_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW7 0 3; norm_num [aW7_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW7 0 4; norm_num [aW7_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW7 0 5; norm_num [aW7_0_5]
  | 0, 6 => show (0:ℝ) ≤ aW7 0 6; norm_num [aW7_0_6]
  | 1, 0 => show (0:ℝ) ≤ aW7 1 0; norm_num [aW7_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW7 1 1; norm_num [aW7_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW7 1 2; norm_num [aW7_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW7 1 3; norm_num [aW7_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW7 1 4; norm_num [aW7_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW7 1 5; norm_num [aW7_1_5]
  | 1, 6 => show (0:ℝ) ≤ aW7 1 6; norm_num [aW7_1_6]
  | 2, 0 => show (0:ℝ) ≤ aW7 2 0; norm_num [aW7_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW7 2 1; norm_num [aW7_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW7 2 2; norm_num [aW7_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW7 2 3; norm_num [aW7_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW7 2 4; norm_num [aW7_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW7 2 5; norm_num [aW7_2_5]
  | 2, 6 => show (0:ℝ) ≤ aW7 2 6; norm_num [aW7_2_6]
  | 3, 0 => show (0:ℝ) ≤ aW7 3 0; norm_num [aW7_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW7 3 1; norm_num [aW7_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW7 3 2; norm_num [aW7_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW7 3 3; norm_num [aW7_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW7 3 4; norm_num [aW7_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW7 3 5; norm_num [aW7_3_5]
  | 3, 6 => show (0:ℝ) ≤ aW7 3 6; norm_num [aW7_3_6]
  | 4, 0 => show (0:ℝ) ≤ aW7 4 0; norm_num [aW7_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW7 4 1; norm_num [aW7_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW7 4 2; norm_num [aW7_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW7 4 3; norm_num [aW7_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW7 4 4; norm_num [aW7_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW7 4 5; norm_num [aW7_4_5]
  | 4, 6 => show (0:ℝ) ≤ aW7 4 6; norm_num [aW7_4_6]
  | 5, 0 => show (0:ℝ) ≤ aW7 5 0; norm_num [aW7_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW7 5 1; norm_num [aW7_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW7 5 2; norm_num [aW7_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW7 5 3; norm_num [aW7_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW7 5 4; norm_num [aW7_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW7 5 5; norm_num [aW7_5_5]
  | 5, 6 => show (0:ℝ) ≤ aW7 5 6; norm_num [aW7_5_6]
  | 6, 0 => show (0:ℝ) ≤ aW7 6 0; norm_num [aW7_6_0]
  | 6, 1 => show (0:ℝ) ≤ aW7 6 1; norm_num [aW7_6_1]
  | 6, 2 => show (0:ℝ) ≤ aW7 6 2; norm_num [aW7_6_2]
  | 6, 3 => show (0:ℝ) ≤ aW7 6 3; norm_num [aW7_6_3]
  | 6, 4 => show (0:ℝ) ≤ aW7 6 4; norm_num [aW7_6_4]
  | 6, 5 => show (0:ℝ) ≤ aW7 6 5; norm_num [aW7_6_5]
  | 6, 6 => show (0:ℝ) ≤ aW7 6 6; norm_num [aW7_6_6]

theorem W7_bmin : ∀ r, ((43281 : ℝ) / 100000000) ≤ W7.b r := by
  intro r
  unfold W7
  match r with
  | 0 => show ((43281 : ℝ) / 100000000) ≤ bW7 0; norm_num [bW7_0]
  | 1 => show ((43281 : ℝ) / 100000000) ≤ bW7 1; norm_num [bW7_1]
  | 2 => show ((43281 : ℝ) / 100000000) ≤ bW7 2; norm_num [bW7_2]
  | 3 => show ((43281 : ℝ) / 100000000) ≤ bW7 3; norm_num [bW7_3]
  | 4 => show ((43281 : ℝ) / 100000000) ≤ bW7 4; norm_num [bW7_4]
  | 5 => show ((43281 : ℝ) / 100000000) ≤ bW7 5; norm_num [bW7_5]

theorem W7_capacity : ∀ s : ℕ, W7.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass W7
  rcases lt_or_ge s 7 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_seven, aW7_0_0, aW7_0_1, aW7_0_2, aW7_0_3, aW7_0_4, aW7_0_5, aW7_0_6, aW7_1_0, aW7_1_1, aW7_1_2, aW7_1_3, aW7_1_4, aW7_1_5, aW7_1_6, aW7_2_0, aW7_2_1, aW7_2_2, aW7_2_3, aW7_2_4, aW7_2_5, aW7_2_6, aW7_3_0, aW7_3_1, aW7_3_2, aW7_3_3, aW7_3_4, aW7_3_5, aW7_3_6, aW7_4_0, aW7_4_1, aW7_4_2, aW7_4_3, aW7_4_4, aW7_4_5, aW7_4_6, aW7_5_0, aW7_5_1, aW7_5_2, aW7_5_3, aW7_5_4, aW7_5_5, aW7_5_6, aW7_6_0, aW7_6_1, aW7_6_2, aW7_6_3, aW7_6_4, aW7_6_5, aW7_6_6, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 7, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem W7_adm : W7.Adm := ⟨W7_a_nonneg, fun r => le_trans (by norm_num) (W7_bmin r), W7_capacity⟩

private lemma sum6 (f : Fin (7 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  show ∑ i : Fin 6, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5
  exact Fin.sum_univ_six f

/-- the certificate's kernel is the bridge's (both are `AMW.wfunAM`) -/
theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl

/-- `Fw W7` written out on the gaps: it is the certificate's functional `T7S.G`. -/
theorem Fw_W7 (g : Fin (7 - 1) → ℝ) :
    Fw W7 g = AMW.Cert.T7S.G (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) := by
  show (∑ r : Fin 6, bW7 r * g r) + (∑ i : Fin 7, ∑ j : Fin 7, if (i : ℕ) < (j : ℕ) then aW7 i j * wfun (ptsN 7 g j - ptsN 7 g i) else 0) = _
  unfold AMW.Cert.T7S.G ptsN
  simp only [cert_wfun_eq, sum6, Fin.sum_univ_seven, Fin.sum_univ_six, Fin.isValue, aW7_0_0, aW7_0_1, aW7_0_2, aW7_0_3, aW7_0_4, aW7_0_5, aW7_0_6, aW7_1_0, aW7_1_1, aW7_1_2, aW7_1_3, aW7_1_4, aW7_1_5, aW7_1_6, aW7_2_0, aW7_2_1, aW7_2_2, aW7_2_3, aW7_2_4, aW7_2_5, aW7_2_6, aW7_3_0, aW7_3_1, aW7_3_2, aW7_3_3, aW7_3_4, aW7_3_5, aW7_3_6, aW7_4_0, aW7_4_1, aW7_4_2, aW7_4_3, aW7_4_4, aW7_4_5, aW7_4_6, aW7_5_0, aW7_5_1, aW7_5_2, aW7_5_3, aW7_5_4, aW7_5_5, aW7_5_6, aW7_6_0, aW7_6_1, aW7_6_2, aW7_6_3, aW7_6_4, aW7_6_5, aW7_6_6, bW7_0, bW7_1, bW7_2, bW7_3, bW7_4, bW7_5]
  norm_num [AMW.Cert.T7S.SA]
  try ring

/-- **the certificate**: `c ≤ Fw W7 g` on the nonnegative orthant -/
theorem cert_AM : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → ((786661 : ℝ) / 100000000) ≤ Fw W7 g := by
  intro g hg
  rw [Fw_W7]
  have h := AMW.Cert.T7S_cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4) (hg 5)
  simp only [AMW.Cert.T7S.cN, AMW.Cert.T7S.SA] at h
  push_cast at h
  exact h

theorem kappa_le : candidateKappa ≤ Phi_w' 7 ((786661 : ℝ) / 100000000) 133 W7.B := by
  rw [W7_B]
  exact Phi_w'_ge_n (n := 7) (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)

theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_n (n := 7) (by norm_num) W7_adm (by norm_num : (0 : ℝ) < (43281 : ℝ) / 100000000) W7_bmin (by norm_num) (m := 133)
    (by norm_num) (by norm_num) kappa_le cert_AM

theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  norm_num

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
