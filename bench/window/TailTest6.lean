import ChallengeDeps.CandidateSpec
import AMW.AMTail
import AMW.AMX05Data

set_option linter.all false
/-! ###### tail: the AM six-point bound from the certificate `AMW.Cert.AMX05_cert_full` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW6 : Fin 6 → Fin 6 → ℝ
  | 0, 1 => (26253915 : ℝ) / 100000000
  | 0, 2 => (32896625 : ℝ) / 100000000
  | 0, 3 => (39780473 : ℝ) / 100000000
  | 0, 4 => (100000000 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (47534277 : ℝ) / 100000000
  | 1, 3 => (67103375 : ℝ) / 100000000
  | 1, 4 => (120439054 : ℝ) / 100000000
  | 1, 5 => (100000000 : ℝ) / 100000000
  | 2, 3 => (52423615 : ℝ) / 100000000
  | 2, 4 => (67103375 : ℝ) / 100000000
  | 2, 5 => (39780473 : ℝ) / 100000000
  | 3, 4 => (47534277 : ℝ) / 100000000
  | 3, 5 => (32896625 : ℝ) / 100000000
  | 4, 5 => (26253915 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW6 : Fin 5 → ℝ
  | 0 => (48515 : ℝ) / 100000000
  | 1 => (84596 : ℝ) / 100000000
  | 2 => (93778 : ℝ) / 100000000
  | 3 => (84596 : ℝ) / 100000000
  | 4 => (48515 : ℝ) / 100000000

def W6 : WCert 6 := ⟨aW6, bW6⟩

theorem aW6_0_0 : aW6 0 0 = 0 := rfl
theorem aW6_0_1 : aW6 0 1 = (26253915 : ℝ) / 100000000 := rfl
theorem aW6_0_2 : aW6 0 2 = (32896625 : ℝ) / 100000000 := rfl
theorem aW6_0_3 : aW6 0 3 = (39780473 : ℝ) / 100000000 := rfl
theorem aW6_0_4 : aW6 0 4 = (100000000 : ℝ) / 100000000 := rfl
theorem aW6_0_5 : aW6 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW6_1_0 : aW6 1 0 = 0 := rfl
theorem aW6_1_1 : aW6 1 1 = 0 := rfl
theorem aW6_1_2 : aW6 1 2 = (47534277 : ℝ) / 100000000 := rfl
theorem aW6_1_3 : aW6 1 3 = (67103375 : ℝ) / 100000000 := rfl
theorem aW6_1_4 : aW6 1 4 = (120439054 : ℝ) / 100000000 := rfl
theorem aW6_1_5 : aW6 1 5 = (100000000 : ℝ) / 100000000 := rfl
theorem aW6_2_0 : aW6 2 0 = 0 := rfl
theorem aW6_2_1 : aW6 2 1 = 0 := rfl
theorem aW6_2_2 : aW6 2 2 = 0 := rfl
theorem aW6_2_3 : aW6 2 3 = (52423615 : ℝ) / 100000000 := rfl
theorem aW6_2_4 : aW6 2 4 = (67103375 : ℝ) / 100000000 := rfl
theorem aW6_2_5 : aW6 2 5 = (39780473 : ℝ) / 100000000 := rfl
theorem aW6_3_0 : aW6 3 0 = 0 := rfl
theorem aW6_3_1 : aW6 3 1 = 0 := rfl
theorem aW6_3_2 : aW6 3 2 = 0 := rfl
theorem aW6_3_3 : aW6 3 3 = 0 := rfl
theorem aW6_3_4 : aW6 3 4 = (47534277 : ℝ) / 100000000 := rfl
theorem aW6_3_5 : aW6 3 5 = (32896625 : ℝ) / 100000000 := rfl
theorem aW6_4_0 : aW6 4 0 = 0 := rfl
theorem aW6_4_1 : aW6 4 1 = 0 := rfl
theorem aW6_4_2 : aW6 4 2 = 0 := rfl
theorem aW6_4_3 : aW6 4 3 = 0 := rfl
theorem aW6_4_4 : aW6 4 4 = 0 := rfl
theorem aW6_4_5 : aW6 4 5 = (26253915 : ℝ) / 100000000 := rfl
theorem aW6_5_0 : aW6 5 0 = 0 := rfl
theorem aW6_5_1 : aW6 5 1 = 0 := rfl
theorem aW6_5_2 : aW6 5 2 = 0 := rfl
theorem aW6_5_3 : aW6 5 3 = 0 := rfl
theorem aW6_5_4 : aW6 5 4 = 0 := rfl
theorem aW6_5_5 : aW6 5 5 = 0 := rfl
theorem bW6_0 : bW6 0 = (48515 : ℝ) / 100000000 := rfl
theorem bW6_1 : bW6 1 = (84596 : ℝ) / 100000000 := rfl
theorem bW6_2 : bW6 2 = (93778 : ℝ) / 100000000 := rfl
theorem bW6_3 : bW6 3 = (84596 : ℝ) / 100000000 := rfl
theorem bW6_4 : bW6 4 = (48515 : ℝ) / 100000000 := rfl

theorem W6_B : W6.B = (360000 : ℝ) / 100000000 := by
  show (∑ r : Fin 5, bW6 r) = _
  norm_num [Fin.sum_univ_five, bW6_0, bW6_1, bW6_2, bW6_3, bW6_4]

theorem W6_a_nonneg : ∀ i j, 0 ≤ W6.a i j := by
  intro i j
  unfold W6
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW6 0 0; norm_num [aW6_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW6 0 1; norm_num [aW6_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW6 0 2; norm_num [aW6_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW6 0 3; norm_num [aW6_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW6 0 4; norm_num [aW6_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW6 0 5; norm_num [aW6_0_5]
  | 1, 0 => show (0:ℝ) ≤ aW6 1 0; norm_num [aW6_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW6 1 1; norm_num [aW6_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW6 1 2; norm_num [aW6_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW6 1 3; norm_num [aW6_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW6 1 4; norm_num [aW6_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW6 1 5; norm_num [aW6_1_5]
  | 2, 0 => show (0:ℝ) ≤ aW6 2 0; norm_num [aW6_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW6 2 1; norm_num [aW6_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW6 2 2; norm_num [aW6_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW6 2 3; norm_num [aW6_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW6 2 4; norm_num [aW6_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW6 2 5; norm_num [aW6_2_5]
  | 3, 0 => show (0:ℝ) ≤ aW6 3 0; norm_num [aW6_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW6 3 1; norm_num [aW6_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW6 3 2; norm_num [aW6_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW6 3 3; norm_num [aW6_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW6 3 4; norm_num [aW6_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW6 3 5; norm_num [aW6_3_5]
  | 4, 0 => show (0:ℝ) ≤ aW6 4 0; norm_num [aW6_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW6 4 1; norm_num [aW6_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW6 4 2; norm_num [aW6_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW6 4 3; norm_num [aW6_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW6 4 4; norm_num [aW6_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW6 4 5; norm_num [aW6_4_5]
  | 5, 0 => show (0:ℝ) ≤ aW6 5 0; norm_num [aW6_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW6 5 1; norm_num [aW6_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW6 5 2; norm_num [aW6_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW6 5 3; norm_num [aW6_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW6 5 4; norm_num [aW6_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW6 5 5; norm_num [aW6_5_5]

theorem W6_bmin : ∀ r, ((48515 : ℝ) / 100000000) ≤ W6.b r := by
  intro r
  unfold W6
  match r with
  | 0 => show ((48515 : ℝ) / 100000000) ≤ bW6 0; norm_num [bW6_0]
  | 1 => show ((48515 : ℝ) / 100000000) ≤ bW6 1; norm_num [bW6_1]
  | 2 => show ((48515 : ℝ) / 100000000) ≤ bW6 2; norm_num [bW6_2]
  | 3 => show ((48515 : ℝ) / 100000000) ≤ bW6 3; norm_num [bW6_3]
  | 4 => show ((48515 : ℝ) / 100000000) ≤ bW6 4; norm_num [bW6_4]

theorem W6_capacity : ∀ s : ℕ, W6.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass W6
  rcases lt_or_ge s 6 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_six, aW6_0_0, aW6_0_1, aW6_0_2, aW6_0_3, aW6_0_4, aW6_0_5, aW6_1_0, aW6_1_1, aW6_1_2, aW6_1_3, aW6_1_4, aW6_1_5, aW6_2_0, aW6_2_1, aW6_2_2, aW6_2_3, aW6_2_4, aW6_2_5, aW6_3_0, aW6_3_1, aW6_3_2, aW6_3_3, aW6_3_4, aW6_3_5, aW6_4_0, aW6_4_1, aW6_4_2, aW6_4_3, aW6_4_4, aW6_4_5, aW6_5_0, aW6_5_1, aW6_5_2, aW6_5_3, aW6_5_4, aW6_5_5, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 6, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem W6_adm : W6.Adm := ⟨W6_a_nonneg, fun r => le_trans (by norm_num) (W6_bmin r), W6_capacity⟩

private lemma sum5 (f : Fin (6 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4
  exact Fin.sum_univ_five f

/-- the certificate's kernel is the bridge's (both are `AMW.wfunAM`) -/
theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl

/-- `Fw W6` written out on the gaps: it is the certificate's functional `AMX05.G`. -/
theorem Fw_W6 (g : Fin (6 - 1) → ℝ) :
    Fw W6 g = AMW.Cert.AMX05.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW6 r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW6 i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold AMW.Cert.AMX05.G ptsN
  simp only [cert_wfun_eq, sum5, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW6_0_0, aW6_0_1, aW6_0_2, aW6_0_3, aW6_0_4, aW6_0_5, aW6_1_0, aW6_1_1, aW6_1_2, aW6_1_3, aW6_1_4, aW6_1_5, aW6_2_0, aW6_2_1, aW6_2_2, aW6_2_3, aW6_2_4, aW6_2_5, aW6_3_0, aW6_3_1, aW6_3_2, aW6_3_3, aW6_3_4, aW6_3_5, aW6_4_0, aW6_4_1, aW6_4_2, aW6_4_3, aW6_4_4, aW6_4_5, aW6_5_0, aW6_5_1, aW6_5_2, aW6_5_3, aW6_5_4, aW6_5_5, bW6_0, bW6_1, bW6_2, bW6_3, bW6_4]
  norm_num [AMW.Cert.AMX05.SA]
  try ring

/-- **the certificate**: `c ≤ Fw W6 g` on the nonnegative orthant -/
theorem cert_AM : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) → ((707843 : ℝ) / 100000000) ≤ Fw W6 g := by
  intro g hg
  rw [Fw_W6]
  have h := AMW.Cert.AMX05_cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [AMW.Cert.AMX05.cN, AMW.Cert.AMX05.SA] at h
  push_cast at h
  exact h

theorem kappa_le : candidateKappa ≤ Phi_w' 6 ((707843 : ℝ) / 100000000) 146 W6.B := by
  rw [W6_B]
  exact Phi_w'_ge6 (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)

theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic6 W6_adm (by norm_num : (0 : ℝ) < (48515 : ℝ) / 100000000) W6_bmin (by norm_num) (m := 146)
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
