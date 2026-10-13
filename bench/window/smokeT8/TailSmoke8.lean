import ChallengeDeps.CandidateSpec
import AMW.T8SInst

set_option linter.all false
/-! ###### tail: the AM eight-point bound from the certificate `AMW.Cert.T8S_cert_full` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW8 : Fin 8 → Fin 8 → ℝ
  | 0, 1 => (13630830 : ℝ) / 100000000
  | 0, 2 => (0 : ℝ) / 100000000
  | 0, 3 => (19565904 : ℝ) / 100000000
  | 0, 4 => (20317441 : ℝ) / 100000000
  | 0, 5 => (45030671 : ℝ) / 100000000
  | 0, 6 => (100000000 : ℝ) / 100000000
  | 0, 7 => (200000000 : ℝ) / 100000000
  | 1, 2 => (29997996 : ℝ) / 100000000
  | 1, 3 => (30621878 : ℝ) / 100000000
  | 1, 4 => (47766489 : ℝ) / 100000000
  | 1, 5 => (79682558 : ℝ) / 100000000
  | 1, 6 => (109938656 : ℝ) / 100000000
  | 1, 7 => (100000000 : ℝ) / 100000000
  | 2, 3 => (37356140 : ℝ) / 100000000
  | 2, 4 => (69378121 : ℝ) / 100000000
  | 2, 5 => (65335210 : ℝ) / 100000000
  | 2, 6 => (79682558 : ℝ) / 100000000
  | 2, 7 => (45030671 : ℝ) / 100000000
  | 3, 4 => (38030065 : ℝ) / 100000000
  | 3, 5 => (69378121 : ℝ) / 100000000
  | 3, 6 => (47766489 : ℝ) / 100000000
  | 3, 7 => (20317441 : ℝ) / 100000000
  | 4, 5 => (37356140 : ℝ) / 100000000
  | 4, 6 => (30621878 : ℝ) / 100000000
  | 4, 7 => (19565904 : ℝ) / 100000000
  | 5, 6 => (29997996 : ℝ) / 100000000
  | 5, 7 => (0 : ℝ) / 100000000
  | 6, 7 => (13630830 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW8 : Fin 7 → ℝ
  | 0 => (28898 : ℝ) / 100000000
  | 1 => (57272 : ℝ) / 100000000
  | 2 => (75526 : ℝ) / 100000000
  | 3 => (80958 : ℝ) / 100000000
  | 4 => (75526 : ℝ) / 100000000
  | 5 => (57272 : ℝ) / 100000000
  | 6 => (28898 : ℝ) / 100000000

def W8 : WCert 8 := ⟨aW8, bW8⟩

theorem aW8_0_0 : aW8 0 0 = 0 := rfl
theorem aW8_0_1 : aW8 0 1 = (13630830 : ℝ) / 100000000 := rfl
theorem aW8_0_2 : aW8 0 2 = (0 : ℝ) / 100000000 := rfl
theorem aW8_0_3 : aW8 0 3 = (19565904 : ℝ) / 100000000 := rfl
theorem aW8_0_4 : aW8 0 4 = (20317441 : ℝ) / 100000000 := rfl
theorem aW8_0_5 : aW8 0 5 = (45030671 : ℝ) / 100000000 := rfl
theorem aW8_0_6 : aW8 0 6 = (100000000 : ℝ) / 100000000 := rfl
theorem aW8_0_7 : aW8 0 7 = (200000000 : ℝ) / 100000000 := rfl
theorem aW8_1_0 : aW8 1 0 = 0 := rfl
theorem aW8_1_1 : aW8 1 1 = 0 := rfl
theorem aW8_1_2 : aW8 1 2 = (29997996 : ℝ) / 100000000 := rfl
theorem aW8_1_3 : aW8 1 3 = (30621878 : ℝ) / 100000000 := rfl
theorem aW8_1_4 : aW8 1 4 = (47766489 : ℝ) / 100000000 := rfl
theorem aW8_1_5 : aW8 1 5 = (79682558 : ℝ) / 100000000 := rfl
theorem aW8_1_6 : aW8 1 6 = (109938656 : ℝ) / 100000000 := rfl
theorem aW8_1_7 : aW8 1 7 = (100000000 : ℝ) / 100000000 := rfl
theorem aW8_2_0 : aW8 2 0 = 0 := rfl
theorem aW8_2_1 : aW8 2 1 = 0 := rfl
theorem aW8_2_2 : aW8 2 2 = 0 := rfl
theorem aW8_2_3 : aW8 2 3 = (37356140 : ℝ) / 100000000 := rfl
theorem aW8_2_4 : aW8 2 4 = (69378121 : ℝ) / 100000000 := rfl
theorem aW8_2_5 : aW8 2 5 = (65335210 : ℝ) / 100000000 := rfl
theorem aW8_2_6 : aW8 2 6 = (79682558 : ℝ) / 100000000 := rfl
theorem aW8_2_7 : aW8 2 7 = (45030671 : ℝ) / 100000000 := rfl
theorem aW8_3_0 : aW8 3 0 = 0 := rfl
theorem aW8_3_1 : aW8 3 1 = 0 := rfl
theorem aW8_3_2 : aW8 3 2 = 0 := rfl
theorem aW8_3_3 : aW8 3 3 = 0 := rfl
theorem aW8_3_4 : aW8 3 4 = (38030065 : ℝ) / 100000000 := rfl
theorem aW8_3_5 : aW8 3 5 = (69378121 : ℝ) / 100000000 := rfl
theorem aW8_3_6 : aW8 3 6 = (47766489 : ℝ) / 100000000 := rfl
theorem aW8_3_7 : aW8 3 7 = (20317441 : ℝ) / 100000000 := rfl
theorem aW8_4_0 : aW8 4 0 = 0 := rfl
theorem aW8_4_1 : aW8 4 1 = 0 := rfl
theorem aW8_4_2 : aW8 4 2 = 0 := rfl
theorem aW8_4_3 : aW8 4 3 = 0 := rfl
theorem aW8_4_4 : aW8 4 4 = 0 := rfl
theorem aW8_4_5 : aW8 4 5 = (37356140 : ℝ) / 100000000 := rfl
theorem aW8_4_6 : aW8 4 6 = (30621878 : ℝ) / 100000000 := rfl
theorem aW8_4_7 : aW8 4 7 = (19565904 : ℝ) / 100000000 := rfl
theorem aW8_5_0 : aW8 5 0 = 0 := rfl
theorem aW8_5_1 : aW8 5 1 = 0 := rfl
theorem aW8_5_2 : aW8 5 2 = 0 := rfl
theorem aW8_5_3 : aW8 5 3 = 0 := rfl
theorem aW8_5_4 : aW8 5 4 = 0 := rfl
theorem aW8_5_5 : aW8 5 5 = 0 := rfl
theorem aW8_5_6 : aW8 5 6 = (29997996 : ℝ) / 100000000 := rfl
theorem aW8_5_7 : aW8 5 7 = (0 : ℝ) / 100000000 := rfl
theorem aW8_6_0 : aW8 6 0 = 0 := rfl
theorem aW8_6_1 : aW8 6 1 = 0 := rfl
theorem aW8_6_2 : aW8 6 2 = 0 := rfl
theorem aW8_6_3 : aW8 6 3 = 0 := rfl
theorem aW8_6_4 : aW8 6 4 = 0 := rfl
theorem aW8_6_5 : aW8 6 5 = 0 := rfl
theorem aW8_6_6 : aW8 6 6 = 0 := rfl
theorem aW8_6_7 : aW8 6 7 = (13630830 : ℝ) / 100000000 := rfl
theorem aW8_7_0 : aW8 7 0 = 0 := rfl
theorem aW8_7_1 : aW8 7 1 = 0 := rfl
theorem aW8_7_2 : aW8 7 2 = 0 := rfl
theorem aW8_7_3 : aW8 7 3 = 0 := rfl
theorem aW8_7_4 : aW8 7 4 = 0 := rfl
theorem aW8_7_5 : aW8 7 5 = 0 := rfl
theorem aW8_7_6 : aW8 7 6 = 0 := rfl
theorem aW8_7_7 : aW8 7 7 = 0 := rfl
theorem bW8_0 : bW8 0 = (28898 : ℝ) / 100000000 := rfl
theorem bW8_1 : bW8 1 = (57272 : ℝ) / 100000000 := rfl
theorem bW8_2 : bW8 2 = (75526 : ℝ) / 100000000 := rfl
theorem bW8_3 : bW8 3 = (80958 : ℝ) / 100000000 := rfl
theorem bW8_4 : bW8 4 = (75526 : ℝ) / 100000000 := rfl
theorem bW8_5 : bW8 5 = (57272 : ℝ) / 100000000 := rfl
theorem bW8_6 : bW8 6 = (28898 : ℝ) / 100000000 := rfl

theorem W8_B : W8.B = (404350 : ℝ) / 100000000 := by
  show (∑ r : Fin 7, bW8 r) = _
  norm_num [Fin.sum_univ_seven, bW8_0, bW8_1, bW8_2, bW8_3, bW8_4, bW8_5, bW8_6]

theorem W8_a_nonneg : ∀ i j, 0 ≤ W8.a i j := by
  intro i j
  unfold W8
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW8 0 0; norm_num [aW8_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW8 0 1; norm_num [aW8_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW8 0 2; norm_num [aW8_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW8 0 3; norm_num [aW8_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW8 0 4; norm_num [aW8_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW8 0 5; norm_num [aW8_0_5]
  | 0, 6 => show (0:ℝ) ≤ aW8 0 6; norm_num [aW8_0_6]
  | 0, 7 => show (0:ℝ) ≤ aW8 0 7; norm_num [aW8_0_7]
  | 1, 0 => show (0:ℝ) ≤ aW8 1 0; norm_num [aW8_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW8 1 1; norm_num [aW8_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW8 1 2; norm_num [aW8_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW8 1 3; norm_num [aW8_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW8 1 4; norm_num [aW8_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW8 1 5; norm_num [aW8_1_5]
  | 1, 6 => show (0:ℝ) ≤ aW8 1 6; norm_num [aW8_1_6]
  | 1, 7 => show (0:ℝ) ≤ aW8 1 7; norm_num [aW8_1_7]
  | 2, 0 => show (0:ℝ) ≤ aW8 2 0; norm_num [aW8_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW8 2 1; norm_num [aW8_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW8 2 2; norm_num [aW8_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW8 2 3; norm_num [aW8_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW8 2 4; norm_num [aW8_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW8 2 5; norm_num [aW8_2_5]
  | 2, 6 => show (0:ℝ) ≤ aW8 2 6; norm_num [aW8_2_6]
  | 2, 7 => show (0:ℝ) ≤ aW8 2 7; norm_num [aW8_2_7]
  | 3, 0 => show (0:ℝ) ≤ aW8 3 0; norm_num [aW8_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW8 3 1; norm_num [aW8_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW8 3 2; norm_num [aW8_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW8 3 3; norm_num [aW8_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW8 3 4; norm_num [aW8_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW8 3 5; norm_num [aW8_3_5]
  | 3, 6 => show (0:ℝ) ≤ aW8 3 6; norm_num [aW8_3_6]
  | 3, 7 => show (0:ℝ) ≤ aW8 3 7; norm_num [aW8_3_7]
  | 4, 0 => show (0:ℝ) ≤ aW8 4 0; norm_num [aW8_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW8 4 1; norm_num [aW8_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW8 4 2; norm_num [aW8_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW8 4 3; norm_num [aW8_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW8 4 4; norm_num [aW8_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW8 4 5; norm_num [aW8_4_5]
  | 4, 6 => show (0:ℝ) ≤ aW8 4 6; norm_num [aW8_4_6]
  | 4, 7 => show (0:ℝ) ≤ aW8 4 7; norm_num [aW8_4_7]
  | 5, 0 => show (0:ℝ) ≤ aW8 5 0; norm_num [aW8_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW8 5 1; norm_num [aW8_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW8 5 2; norm_num [aW8_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW8 5 3; norm_num [aW8_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW8 5 4; norm_num [aW8_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW8 5 5; norm_num [aW8_5_5]
  | 5, 6 => show (0:ℝ) ≤ aW8 5 6; norm_num [aW8_5_6]
  | 5, 7 => show (0:ℝ) ≤ aW8 5 7; norm_num [aW8_5_7]
  | 6, 0 => show (0:ℝ) ≤ aW8 6 0; norm_num [aW8_6_0]
  | 6, 1 => show (0:ℝ) ≤ aW8 6 1; norm_num [aW8_6_1]
  | 6, 2 => show (0:ℝ) ≤ aW8 6 2; norm_num [aW8_6_2]
  | 6, 3 => show (0:ℝ) ≤ aW8 6 3; norm_num [aW8_6_3]
  | 6, 4 => show (0:ℝ) ≤ aW8 6 4; norm_num [aW8_6_4]
  | 6, 5 => show (0:ℝ) ≤ aW8 6 5; norm_num [aW8_6_5]
  | 6, 6 => show (0:ℝ) ≤ aW8 6 6; norm_num [aW8_6_6]
  | 6, 7 => show (0:ℝ) ≤ aW8 6 7; norm_num [aW8_6_7]
  | 7, 0 => show (0:ℝ) ≤ aW8 7 0; norm_num [aW8_7_0]
  | 7, 1 => show (0:ℝ) ≤ aW8 7 1; norm_num [aW8_7_1]
  | 7, 2 => show (0:ℝ) ≤ aW8 7 2; norm_num [aW8_7_2]
  | 7, 3 => show (0:ℝ) ≤ aW8 7 3; norm_num [aW8_7_3]
  | 7, 4 => show (0:ℝ) ≤ aW8 7 4; norm_num [aW8_7_4]
  | 7, 5 => show (0:ℝ) ≤ aW8 7 5; norm_num [aW8_7_5]
  | 7, 6 => show (0:ℝ) ≤ aW8 7 6; norm_num [aW8_7_6]
  | 7, 7 => show (0:ℝ) ≤ aW8 7 7; norm_num [aW8_7_7]

theorem W8_bmin : ∀ r, ((28898 : ℝ) / 100000000) ≤ W8.b r := by
  intro r
  unfold W8
  match r with
  | 0 => show ((28898 : ℝ) / 100000000) ≤ bW8 0; norm_num [bW8_0]
  | 1 => show ((28898 : ℝ) / 100000000) ≤ bW8 1; norm_num [bW8_1]
  | 2 => show ((28898 : ℝ) / 100000000) ≤ bW8 2; norm_num [bW8_2]
  | 3 => show ((28898 : ℝ) / 100000000) ≤ bW8 3; norm_num [bW8_3]
  | 4 => show ((28898 : ℝ) / 100000000) ≤ bW8 4; norm_num [bW8_4]
  | 5 => show ((28898 : ℝ) / 100000000) ≤ bW8 5; norm_num [bW8_5]
  | 6 => show ((28898 : ℝ) / 100000000) ≤ bW8 6; norm_num [bW8_6]

theorem W8_capacity : ∀ s : ℕ, W8.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass W8
  rcases lt_or_ge s 8 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_eight, aW8_0_0, aW8_0_1, aW8_0_2, aW8_0_3, aW8_0_4, aW8_0_5, aW8_0_6, aW8_0_7, aW8_1_0, aW8_1_1, aW8_1_2, aW8_1_3, aW8_1_4, aW8_1_5, aW8_1_6, aW8_1_7, aW8_2_0, aW8_2_1, aW8_2_2, aW8_2_3, aW8_2_4, aW8_2_5, aW8_2_6, aW8_2_7, aW8_3_0, aW8_3_1, aW8_3_2, aW8_3_3, aW8_3_4, aW8_3_5, aW8_3_6, aW8_3_7, aW8_4_0, aW8_4_1, aW8_4_2, aW8_4_3, aW8_4_4, aW8_4_5, aW8_4_6, aW8_4_7, aW8_5_0, aW8_5_1, aW8_5_2, aW8_5_3, aW8_5_4, aW8_5_5, aW8_5_6, aW8_5_7, aW8_6_0, aW8_6_1, aW8_6_2, aW8_6_3, aW8_6_4, aW8_6_5, aW8_6_6, aW8_6_7, aW8_7_0, aW8_7_1, aW8_7_2, aW8_7_3, aW8_7_4, aW8_7_5, aW8_7_6, aW8_7_7, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 8, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem W8_adm : W8.Adm := ⟨W8_a_nonneg, fun r => le_trans (by norm_num) (W8_bmin r), W8_capacity⟩

private lemma sum7 (f : Fin (8 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  show ∑ i : Fin 7, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6
  exact Fin.sum_univ_seven f

/-- the certificate's kernel is the bridge's (both are `AMW.wfunAM`) -/
theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl

/-- `Fw W8` written out on the gaps: it is the certificate's functional `T8S.G`. -/
theorem Fw_W8 (g : Fin (8 - 1) → ℝ) :
    Fw W8 g = AMW.Cert.T8S.G (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by
  show (∑ r : Fin 7, bW8 r * g r) + (∑ i : Fin 8, ∑ j : Fin 8, if (i : ℕ) < (j : ℕ) then aW8 i j * wfun (ptsN 8 g j - ptsN 8 g i) else 0) = _
  unfold AMW.Cert.T8S.G ptsN
  simp only [cert_wfun_eq, sum7, Fin.sum_univ_eight, Fin.sum_univ_seven, Fin.isValue, aW8_0_0, aW8_0_1, aW8_0_2, aW8_0_3, aW8_0_4, aW8_0_5, aW8_0_6, aW8_0_7, aW8_1_0, aW8_1_1, aW8_1_2, aW8_1_3, aW8_1_4, aW8_1_5, aW8_1_6, aW8_1_7, aW8_2_0, aW8_2_1, aW8_2_2, aW8_2_3, aW8_2_4, aW8_2_5, aW8_2_6, aW8_2_7, aW8_3_0, aW8_3_1, aW8_3_2, aW8_3_3, aW8_3_4, aW8_3_5, aW8_3_6, aW8_3_7, aW8_4_0, aW8_4_1, aW8_4_2, aW8_4_3, aW8_4_4, aW8_4_5, aW8_4_6, aW8_4_7, aW8_5_0, aW8_5_1, aW8_5_2, aW8_5_3, aW8_5_4, aW8_5_5, aW8_5_6, aW8_5_7, aW8_6_0, aW8_6_1, aW8_6_2, aW8_6_3, aW8_6_4, aW8_6_5, aW8_6_6, aW8_6_7, aW8_7_0, aW8_7_1, aW8_7_2, aW8_7_3, aW8_7_4, aW8_7_5, aW8_7_6, aW8_7_7, bW8_0, bW8_1, bW8_2, bW8_3, bW8_4, bW8_5, bW8_6]
  norm_num [AMW.Cert.T8S.SA]
  try ring

/-- **the certificate**: `c ≤ Fw W8 g` on the nonnegative orthant -/
theorem cert_AM : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → ((804359 : ℝ) / 100000000) ≤ Fw W8 g := by
  intro g hg
  rw [Fw_W8]
  have h := AMW.Cert.T8S_cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4) (hg 5) (hg 6)
  simp only [AMW.Cert.T8S.cN, AMW.Cert.T8S.SA] at h
  push_cast at h
  exact h

theorem kappa_le : candidateKappa ≤ Phi_w' 8 ((804359 : ℝ) / 100000000) 131 W8.B := by
  rw [W8_B]
  exact Phi_w'_ge_n (n := 8) (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)

theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_n (n := 8) (by norm_num) W8_adm (by norm_num : (0 : ℝ) < (28898 : ℝ) / 100000000) W8_bmin (by norm_num) (m := 131)
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
