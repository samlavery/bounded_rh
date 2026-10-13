/-
Riemann.fail submission — an unconditional critical-line proportion of 3364797/5000000 = 0.6729594,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW6`: a table of 8220 interval cells, each certified by
an integer pipeline (Taylor enclosures of cos and sin at scale 10¹⁵, `cellN_soundZ`), and a
bisection over the gaps with 32612 leaves over the half-space
g₀ ≤ g₄; the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`.  The resulting constant is
`(3762500000·H − 6659889)/3750038770 = 0.67295943…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is
enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places the exact rational
`3364797/5000000` strictly between the record and the proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.ThmD.Mult
import Zeta23.ThmD.ZeroSideD
import Zeta23.PrimeSideA.EndsE1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.all false

set_option Elab.async false

/-! ###### source module: Zeta23Ext/StableRankTrace.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder

namespace Zeta23Ext.StableRankTrace

def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

lemma Psi_eq_gc_two_add_one (t : ℝ) : Psi t = gc 2 t + 1 := by
  unfold Psi
  split_ifs with h
  · rw [gc_of_le h]; ring
  · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring

@[simp] lemma Psi_zero : Psi 0 = 1 := by norm_num [Psi]

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split_ifs with h
  · positivity
  · have : (2 : ℝ) < t := not_le.mp h
    linarith

lemma two_mul_sub_one_add_Psi_le {p nu : ℝ} (hp : 0 ≤ p) (hnu : 0 ≤ nu) :
    2 * p - 1 + Psi p ≤ (p - nu) ^ 2 + 4 * nu := by
  have h := sq_sub_ge_gc (c := 2) hp hnu (by norm_num)
  rw [Psi_eq_gc_two_add_one]
  linarith

lemma Psi_attained (p : ℝ) :
    (p - max (p - 2) 0) ^ 2 + 4 * max (p - 2) 0 = 2 * p - 1 + Psi p := by
  unfold Psi
  rcases le_or_gt p 2 with h | h
  · rw [max_eq_right (by linarith), if_pos h]; ring
  · rw [max_eq_left (by linarith), if_neg (not_le.mpr h)]; ring

section Eigen

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j

lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (eigCols hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, eigCols, Matrix.mul_diagonal]
  ring

lemma pmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Pmat hP.1.eigenvalues (eigCols hP) = P := by
  have hdd : (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)
        * ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜))
      = RCLike.ofReal ∘ hP.1.eigenvalues := by
    funext j
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    rw [Real.mul_self_sqrt (hP.eigenvalues_nonneg j)]
  have hstar : (diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)))ᴴ
      = diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
    rw [diagonal_conjTranspose]
    simp [RCLike.star_def]
  unfold Pmat
  rw [wmat_eigCols hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
  conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (eigCols hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j

end Eigen

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma rtrace_specMap_Psi (V : Matrix n r 𝕜) :
    rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
        + (Fintype.card r : ℝ) := by
  rw [rtrace_specMap]
  have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := Psi_eq_gc_two_add_one
  simp only [hshift]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  congr 1
  exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm

theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
  have hR := rank_trace_mult hm (eigCols hP) hQ hb (c := 2) (by norm_num)
  rw [pmat_eigCols hP] at hR
  have hx : ∀ j, hP.1.eigenvalues j * xsq (eigCols hP) j = hP.1.eigenvalues j := by
    intro j; rw [xsq_eigCols hP j, mul_one]
  simp only [hx] at hR
  rw [rtrace_specMap_Psi V]
  have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
  linarith [hR]

theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hsharp := stable_rank_trace_sharp V hQ hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

theorem stable_rank_trace_no_defect (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hr : (V * Vᴴ).rank ≤ Fintype.card r := by
    rw [Matrix.rank_self_mul_conjTranspose]
    exact Matrix.rank_le_card_width V
  have h := rank_trace_ineq_two hP hQ hr hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

theorem stable_rank_trace_collapse (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := stable_rank_trace V hV hQ hb
  have hpos : 0 ≤ rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi) := by
    rw [rtrace_specMap]
    exact Finset.sum_nonneg fun j _ => Psi_nonneg _
  linarith

theorem sharp_le_stable (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ)
      ≤ 2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) := by
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

end Main


end Zeta23Ext.StableRankTrace

end

/-! ###### source module: Zeta23Ext/Bridge/Defs.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

def wfun (x : ℝ) : ℝ := kfun x ^ 2

def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0

def F (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (ptsN n g j - ptsN n g i)
        else 0

def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0

def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (pts g j - pts g i)
        else 0

theorem pts_eq_ptsN (g : Fin 6 → ℝ) (i : Fin 7) : pts g i = ptsN 7 g i := rfl

theorem F6_eq (p : ℕ) (g : Fin 6 → ℝ) : F6 p g = F 7 p g := rfl

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def energyOn (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else wfun (x i - x j)

def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2

def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0

def IsInterval (x : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, ∀ k, x i ≤ x k → x k ≤ x j → k ∈ B

lemma abs_sub_le_spanOf (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
    |x i - x j| ≤ spanOf x B := by
  have hne : B.Nonempty := ⟨i, hi⟩
  unfold spanOf
  rw [dif_pos hne, abs_le]
  constructor
  · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
  · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]

lemma spanOf_nonneg (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
  unfold spanOf
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
  · exact le_rfl

def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)

lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => Psi_nonneg _

def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))

lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ blockDefect hM B :=
  defect_nonneg _

end Blocks

def Phi_n (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

theorem Phi_eq_Phi_n (c : ℝ) (m p : ℕ) : Phi c m p = Phi_n 7 c m p := by
  unfold Phi Phi_n
  norm_num

section BlockLevel

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)

def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ

def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c

def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c

lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _

lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
  isHermitian_conjTranspose_mul_self _

lemma gramS₁_posSemidef (c : ℝ) : (gramS₁ D c).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

lemma blockP_isHermitian (c : ℝ) : (D.blockP c).IsHermitian :=
  ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _

lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
  ((blockP_isHermitian D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1

lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
  unfold Q'; abel

end BlockLevel

section Concrete

open Classical

def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atD T

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)

def aL2 : ℝ := P.a T * P.L T ^ 2

def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj

def retained : Finset (ZI Z T) :=
  (bdata Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2

lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1

def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩

lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)

def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)

lemma gram_isHermitian : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _

lemma gram_posSemidef : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _

def Dcirc : ℝ := defect (gram_isHermitian Z P T)

def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)

lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (bdata Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h

lemma xret_injective (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
  intro z z' h
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  unfold xret xnorm at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
    have h1 := (div_left_inj' hpi.ne').mp h
    have h2 := mul_left_cancel₀ hL.ne' h1
    linarith
  apply Subtype.ext; apply Subtype.ext
  exact Complex.ext (by rw [hz, hz']) him

end Concrete


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_finite.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

lemma Kfun_neg (x : ℝ) : Kfun (-x) = Kfun x := by
  unfold Kfun
  simp only [mul_neg, neg_mul, Real.cos_neg]

lemma kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
  unfold kfun; rw [Kfun_neg]

lemma wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
  unfold wfun; rw [kfun_neg]

lemma wfun_sub_comm (a b : ℝ) : wfun (a - b) = wfun (b - a) := by
  rw [← wfun_neg, neg_sub]

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

lemma cos_sqrt_two_mul_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Real.cos (Real.sqrt 2 * t) := by
  obtain ⟨h1, h2⟩ := ht
  have hs : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]

lemma abs_Kfun_le_Kfun_zero (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
  refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro t ht
    rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
    calc Real.cos (Real.sqrt 2 * t) * |Real.cos (2 * Real.pi * x * t)|
        ≤ Real.cos (Real.sqrt 2 * t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (cos_sqrt_two_mul_nonneg ht)
      _ = Real.cos (Real.sqrt 2 * t) := mul_one _

lemma abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := by
  unfold kfun
  rw [abs_div]
  rcases eq_or_ne (Kfun 0) 0 with h | h
  · rw [h, abs_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact (abs_Kfun_le_Kfun_zero x).trans (le_abs_self _)

lemma wfun_le_one (x : ℝ) : wfun x ≤ 1 := by
  unfold wfun
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_kfun_le_one x)

section Sorted

variable {m : ℕ}

def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0

lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
  unfold sortedExt; rw [dif_pos h]

lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    sortedExt y a ≤ sortedExt y b := by
  rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
  exact hy.monotone (Fin.mk_le_mk.mpr hab)

def windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
  fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)

lemma range_filter_lt {N k : ℕ} (hk : k ≤ N) : ((range N).filter fun j => j < k) = range k := by
  ext j
  simp only [mem_filter, mem_range]
  omega

lemma ptsN_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) (k : Fin n) :
    ptsN n (windowGaps n Y i) k = Y (i + k) - Y i := by
  have hk : (k : ℕ) ≤ n - 1 := by have := k.2; omega
  unfold ptsN windowGaps
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < (k : ℕ) then Y (i + (j + 1)) - Y (i + j) else 0) (n - 1),
    ← sum_filter, range_filter_lt hk]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (k : ℕ)
  simpa using this

lemma sum_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    ∑ j, windowGaps n Y i j = Y (i + (n - 1)) - Y i := by
  unfold windowGaps
  rw [Fin.sum_univ_eq_sum_range (fun j => Y (i + (j + 1)) - Y (i + j)) (n - 1)]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (n - 1)
  simpa using this

lemma F_windowGaps (n p : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    F n p (windowGaps n Y i) = (1 / (p : ℝ)) * (Y (i + (n - 1)) - Y i)
      + ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then
            (2 / ((n : ℝ) - (((b : ℕ) - (a : ℕ) : ℕ) : ℝ))) * wfun (Y (i + b) - Y (i + a))
          else 0 := by
  unfold F
  rw [sum_windowGaps]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [ptsN_windowGaps, ptsN_windowGaps,
    show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]

lemma sum_shift_sub (f : ℕ → ℝ) (d N : ℕ) :
    ∑ i ∈ range N, (f (i + d) - f i) = ∑ i ∈ range d, (f (N + i) - f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 : ∑ i ∈ range d, (f (N + 1 + i) - f i) = ∑ i ∈ range d, (f (N + (i + 1)) - f i) :=
      sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    have h2 : ∑ i ∈ range d, f (N + (i + 1)) = ∑ i ∈ range d, f (N + i) + f (N + d) - f (N + 0) := by
      have := sum_range_succ' (fun i => f (N + i)) d
      rw [sum_range_succ] at this
      linarith
    rw [h1, sum_sub_distrib, sum_sub_distrib, h2]
    simp only [add_zero]
    ring

end Sorted


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_pinching.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

section PsiConvex
open Zeta23Ext.StableRankTrace

lemma affine_le_Psi {s x : ℝ} (hs : s ≤ 2) : 2 * (s - 1) * x - (s ^ 2 - 1) ≤ Psi x := by
  unfold Psi
  split_ifs with h
  · nlinarith [sq_nonneg (x - s)]
  · have hx : 2 < x := not_le.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0 : ℝ) ≤ 2 * x - 2 - s)]

lemma affine_eq_Psi (x : ℝ) : 2 * (min x 2 - 1) * x - ((min x 2) ^ 2 - 1) = Psi x := by
  unfold Psi
  rcases le_or_gt x 2 with h | h
  · rw [min_eq_left h, if_pos h]; ring
  · rw [min_eq_right h.le, if_neg (not_le.mpr h)]; ring

theorem Psi_convexOn : ConvexOn ℝ Set.univ Psi := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hz
  set t := min z 2 with ht
  have ht2 : t ≤ 2 := min_le_right _ _
  have hx := affine_le_Psi (x := x) ht2
  have hy := affine_le_Psi (x := y) ht2
  have hsplit : 2 * (t - 1) * z - (t ^ 2 - 1)
      = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := by
    rw [hz]; linear_combination (t ^ 2 - 1) * hab
  calc Psi z = 2 * (t - 1) * z - (t ^ 2 - 1) := (affine_eq_Psi z).symm
    _ = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := hsplit
    _ ≤ a * Psi x + b * Psi y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

end PsiConvex

section Entries

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma re_mul_conjTranspose_apply_self (Y : Matrix κ ι 𝕜) (j : κ) :
    RCLike.re ((Y * Yᴴ) j j) = ∑ i, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
  simp

lemma re_conjTranspose_mul_apply_self (Y : Matrix κ ι 𝕜) (i : ι) :
    RCLike.re ((Yᴴ * Y) i i) = ∑ j, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma re_mul_diagonal_mul_conjTranspose_apply (Y : Matrix κ ι 𝕜) (d : ι → ℝ) (j : κ) :
    RCLike.re ((Y * (diagonal (RCLike.ofReal ∘ d) : Matrix ι ι 𝕜) * Yᴴ : Matrix κ κ 𝕜) j j)
      = ∑ i, ‖Y j i‖ ^ 2 * d i := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, conjTranspose_apply, Function.comp_apply, RCLike.star_def,
    show Y j i * (d i : 𝕜) * starRingEnd 𝕜 (Y j i) = (d i : 𝕜) * (Y j i * starRingEnd 𝕜 (Y j i))
      by ring,
    RCLike.mul_conj,
    show ((d i : 𝕜) * ((‖Y j i‖ : 𝕜) ^ 2) : 𝕜) = ((‖Y j i‖ ^ 2 * d i : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

lemma sum_normSq_col_eigenvectorUnitary {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (i : ι) :
    ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 = 1 := by
  have h := re_conjTranspose_mul_apply_self (hM.eigenvectorUnitary : Matrix ι ι 𝕜) i
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2] at h
  simpa using h.symm

end Entries

section Mix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def compressWeight {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
  ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2

lemma compressWeight_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) :
    0 ≤ compressWeight hM g i :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma compressWeight_le_one {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) (i : ι) : compressWeight hM g i ≤ 1 := by
  unfold compressWeight
  calc ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
      = ∑ k ∈ univ.image g, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        (Finset.sum_image (f := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2)
          (s := univ) (g := g) hg.injOn).symm
    _ ≤ ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = 1 := sum_normSq_col_eigenvectorUnitary hM i

lemma sum_compressWeight_fiberwise {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (β : ι → κ) (i : ι) :
    ∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i = 1 := by
  unfold compressWeight
  have h : ∀ b : κ, ∑ j : (univ.filter fun i => β i = b),
      ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (j : ι) i‖ ^ 2
        = ∑ j ∈ univ.filter (fun i => β i = b), ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2 :=
    fun b => Finset.sum_coe_sort (univ.filter fun i => β i = b)
      (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)
  simp only [h]
  rw [Finset.sum_fiberwise univ β (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)]
  exact sum_normSq_col_eigenvectorUnitary hM i

theorem eigenvalues_submatrix_eq_mix {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) :
    ∃ S : κ → ι → ℝ, (∀ j i, 0 ≤ S j i) ∧ (∀ j, ∑ i, S j i = 1)
      ∧ (∀ i, ∑ j, S j i = compressWeight hM g i)
      ∧ ∀ j, (hM.submatrix g).eigenvalues j = ∑ i, S j i * hM.eigenvalues i := by
  set U : Matrix ι ι 𝕜 := (hM.eigenvectorUnitary : Matrix ι ι 𝕜) with hUdef
  have hP : (M.submatrix g g).IsHermitian := hM.submatrix g
  set V : Matrix κ κ 𝕜 := (hP.eigenvectorUnitary : Matrix κ κ 𝕜) with hVdef
  set Ug : Matrix κ ι 𝕜 := U.submatrix g id with hUgdef
  set Y : Matrix κ ι 𝕜 := star V * Ug with hYdef
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have hVsV : star V * V = 1 := Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
  have hVVs : V * star V = 1 := Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2

  have hM' : M = U * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]

  have hUgUg : Ug * Ugᴴ = 1 := by
    rw [hUgdef, conjTranspose_submatrix, ← star_eq_conjTranspose,
      ← Matrix.submatrix_mul _ _ g id g Function.bijective_id, hUU, submatrix_one _ hg]
  have hPsub : M.submatrix g g = Ug * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Ugᴴ := by
    conv_lhs => rw [hM']
    rw [Matrix.submatrix_mul _ _ g id g Function.bijective_id,
      Matrix.submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id, hUgdef,
      conjTranspose_submatrix, star_eq_conjTranspose]

  have hdiag0 : diagonal (RCLike.ofReal ∘ hP.eigenvalues) = star V * M.submatrix g g * V := by
    rw [← hP.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_star_apply]
  have hdiag : diagonal (RCLike.ofReal ∘ hP.eigenvalues)
      = Y * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Yᴴ := by
    rw [hdiag0, hPsub, hYdef, conjTranspose_mul, star_eq_conjTranspose V,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hYY : Y * Yᴴ = 1 := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Ug, hUgUg, Matrix.one_mul, ← star_eq_conjTranspose,
      hVsV]
  have hYtY : Yᴴ * Y = Ugᴴ * Ug := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, ← star_eq_conjTranspose V, hVVs, Matrix.one_mul]
  refine ⟨fun j i => ‖Y j i‖ ^ 2, fun j i => by positivity, ?_, ?_, ?_⟩
  · intro j
    show ∑ i, ‖Y j i‖ ^ 2 = 1
    have h := re_mul_conjTranspose_apply_self Y j
    rw [hYY] at h
    simpa using h.symm
  · intro i
    show ∑ j, ‖Y j i‖ ^ 2 = compressWeight hM g i
    have h1 := re_conjTranspose_mul_apply_self Y i
    have h2 := re_conjTranspose_mul_apply_self Ug i
    rw [hYtY] at h1
    rw [← h1, h2]
    rfl
  · intro j
    show hP.eigenvalues j = ∑ i, ‖Y j i‖ ^ 2 * hM.eigenvalues i
    have h := re_mul_diagonal_mul_conjTranspose_apply Y hM.eigenvalues j
    rw [← hdiag, diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re] at h
    exact h

end Mix

section Pinching

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sum_eigenvalues_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ j, f ((hM.submatrix g).eigenvalues j)
      ≤ ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by
  obtain ⟨S, hS0, hSrow, hScol, hSeig⟩ := eigenvalues_submatrix_eq_mix hM hg
  calc ∑ j, f ((hM.submatrix g).eigenvalues j)
      = ∑ j, f (∑ i, S j i * hM.eigenvalues i) := by simp only [hSeig]
    _ ≤ ∑ j, ∑ i, S j i * f (hM.eigenvalues i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := hf.map_sum_le (t := Finset.univ) (w := S j) (p := hM.eigenvalues)
          (fun i _ => hS0 j i) (hSrow j) (fun i _ => Set.mem_univ _)
        simpa only [smul_eq_mul] using h
    _ = ∑ i, (∑ j, S j i) * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by simp only [hScol]

theorem sum_eigenvalues_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ i, f (hM.eigenvalues i) := by
  calc ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ b, ∑ i, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i
            * f (hM.eigenvalues i) :=
        Finset.sum_le_sum fun b _ => sum_eigenvalues_submatrix_le hM Subtype.val_injective hf
    _ = ∑ i, (∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i)
            * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, f (hM.eigenvalues i) := by simp only [sum_compressWeight_fiberwise, one_mul]

theorem sum_eigenvalues_submatrix_le_of_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    {g : κ → ι} (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∑ j, f ((hM.submatrix g).eigenvalues j) ≤ ∑ i, f (hM.eigenvalues i) :=
  (sum_eigenvalues_submatrix_le hM hg hf).trans <| Finset.sum_le_sum fun i _ => by
    calc compressWeight hM g i * f (hM.eigenvalues i) ≤ 1 * f (hM.eigenvalues i) :=
          mul_le_mul_of_nonneg_right (compressWeight_le_one hM hg i) (hf0 _)
      _ = f (hM.eigenvalues i) := one_mul _

theorem rtrace_specMap_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, rtrace (specMap (hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)) f)
      ≤ rtrace (specMap hM f) := by
  simp only [rtrace_specMap]
  exact sum_eigenvalues_pinching_le hM hf β

theorem rtrace_specMap_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ t, 0 ≤ f t) :
    rtrace (specMap (hM.submatrix g) f) ≤ rtrace (specMap hM f) := by
  rw [rtrace_specMap, rtrace_specMap]
  exact sum_eigenvalues_submatrix_le_of_nonneg hM hg hf hf0

end Pinching


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S8.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real RHLinalg
open Zeta23 Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

theorem seamA_mult2_defect {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {D : ℝ}
    (hcore : 4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) + D ≤ (Z.s1 T : ℝ)) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      + D ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le

  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0))
    (D : ℝ → ℝ)
    (hcore : ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Az (P.atD T) T))
        - frobSq ((P.atD T).hat T (Z.Az (P.atD T) T))
        - 2 * (Z.NIprime T : ℝ) + D T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) + D T ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII

  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr

  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'

  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T - err T ≤ (Z.N0s T (2 * T) : ℝ) - D T := by
    filter_upwards [hcore, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hcoreT hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity

    have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT

    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA

    have hA' : 4 * ((aT T * P.L T)⁻¹ * trG T) - ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
        - θ₀ T / (aT T * P.L T)
            * (4 + 2 * Real.sqrt (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + θ₀ T / (aT T * P.L T))
        ≤ (Z.N0s T (2 * T) : ℝ) - D T := by linarith [hA]

    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)

    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA' htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith

  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM

  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring

  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2

  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]

  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)

  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1

  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6

  have hfin := eps_form_of_isLittleO (lower := fun T => (Z.N0s T (2 * T) : ℝ) - D T) hmain
    (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hfin ε hε
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have := hT₀ T hT
  simp only [hNdef] at this
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S9.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

section GramEntry

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

lemma bdata_v_eq (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (bdata Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
  simp only [bdata, blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]

lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
    gram Z P T z z' =
      (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
        P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hentry : ∀ a b : (bdata Z P T).S₁, gramS₁ (bdata Z P T) (aL2 P T) a b
      = ∑ k, star (Vsimple (bdata Z P T) (aL2 P T) k a) * Vsimple (bdata Z P T) (aL2 P T) k b := by
    intro a b
    simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
  unfold gram
  rw [Matrix.submatrix_apply, hentry]
  have e : ∀ k : Fin (P.d T),
      star (Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z))
        * Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z')
      = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
          * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
    intro k
    have h1 : (bdata Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz k
    have h2 : (bdata Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz' k
    simp only [Vsimple]
    rw [h1, h2]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq]
    push_cast
    ring
  simp_rw [e]
  rw [← Complex.ofReal_sum, Finset.mul_sum]

end GramEntry

section Window

variable {P : Params} (hP : P.Valid) (T : ℝ)
include hP

lemma atD_phiHatR_eq : (P.atD T).phiHatR T = AdmWindow.vHatR (P.phiD T) := atD_phiHatR hP T

lemma phiHatReal_atD : PhiHatReal T (P.atD T) := fun r => GzGp.phiHat_ofReal _ T r

lemma abs_phiHatR_atD_mul_sq_le (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.atD T).phiHatR T r| * r ^ 2 ≤ cDT P.ϱ P.lam / P.w := by
  rw [atD_phiHatR_eq hP T]
  exact (admWindow_params hP h8).abs_vHatR_mul_sq_le r

lemma hasSum_phiHatR_atD_mul (h8 : 8 * P.w ≤ P.L T) (τ τ' : ℝ) :
    HasSum (fun k : ℤ => (P.atD T).phiHatR T (τ - (P.atD T).tau T k)
        * (P.atD T).phiHatR T (τ' - (P.atD T).tau T k))
      (P.L T * AdmWindow.VPhiR (P.phiD T) (τ - τ')) := by
  have h := (admWindow_params hP h8).hasSum_vHatR_mul T τ τ'
  simp only [atD_phiHatR_eq hP T, atD_tau_eq]
  exact h

end Window

section Tail

lemma Wfun_le_of_L_le {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Δ : ℝ} (hΔ : p.L ≤ Δ) :
    PrimeSide.Wfun c p Δ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h8 := hF.eight_le_L
  have hL : 0 < p.L := hF.L_pos
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hL hΔ
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  set K : ℝ := (c / p.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hπ := Real.pi_pos

  have hψ : PrimeSide.psiA c p Δ ^ 2 ≤ K / Δ ^ 4 := by
    have h1 : PrimeSide.psiA c p Δ ≤ c / (p.w * Δ ^ 2) := PrimeSide.psiA_le_div_sq hΔ0.ne'
    calc PrimeSide.psiA c p Δ ^ 2 ≤ (c / (p.w * Δ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Δ) h1 2
      _ = K / Δ ^ 4 := by rw [hK]; field_simp

  have hint : ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2 ≤ K / (3 * Δ ^ 3) :=
    PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ0
  have hh : (p.h)⁻¹ = p.L / (2 * Real.pi) := by
    unfold PrimeSide.Setting.h; rw [inv_div]
  have hhpos : 0 ≤ (p.h)⁻¹ := by rw [hh]; positivity

  have hΔ4 : p.L ^ 2 ≤ Δ ^ 4 := by
    have : p.L ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hL.le hΔ 2
    have h2 : (1 : ℝ) ≤ Δ ^ 2 := by nlinarith
    calc p.L ^ 2 ≤ Δ ^ 2 := this
      _ = Δ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Δ ^ 2 * Δ ^ 2 := by gcongr
      _ = Δ ^ 4 := by ring
  have hA : K / Δ ^ 4 ≤ K / p.L ^ 2 :=
    div_le_div_of_nonneg_left hK0 (by positivity) hΔ4
  have hB : (p.h)⁻¹ * (K / (3 * Δ ^ 3)) ≤ K / p.L ^ 2 := by
    rw [hh]
    have e : p.L / (2 * Real.pi) * (K / (3 * Δ ^ 3)) = K * (p.L / (6 * Real.pi * Δ ^ 3)) := by
      field_simp; ring
    rw [e]
    have hΔ3 : p.L ^ 3 ≤ Δ ^ 3 := pow_le_pow_left₀ hL.le hΔ 3
    have h3 : p.L / (6 * Real.pi * Δ ^ 3) ≤ 1 / p.L ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : p.L * p.L ^ 2 = p.L ^ 3 := by ring
      rw [this]
      nlinarith [Real.pi_gt_three, pow_pos hΔ0 3]
    calc K * (p.L / (6 * Real.pi * Δ ^ 3)) ≤ K * (1 / p.L ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = K / p.L ^ 2 := by ring
  unfold PrimeSide.Wfun
  calc PrimeSide.psiA c p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2
      ≤ K / Δ ^ 4 + (p.h)⁻¹ * (K / (3 * Δ ^ 3)) := by
        gcongr
    _ ≤ K / p.L ^ 2 + K / p.L ^ 2 := add_le_add hA hB
    _ = 2 * K / p.L ^ 2 := by ring

lemma rho_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj := PrimeSide.rho_le_majorant hF hT hτ
  have hW1 := Wfun_le_of_L_le hF h1
  have hW2 := Wfun_le_of_L_le hF h2
  have hψ : PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / p.w) ^ 2 / p.L ^ 2 := by
    have hΔ0 : 0 < p.tau p.d - τ := lt_of_lt_of_le hL h3
    have hw : 0 < p.w := by linarith [hF.one_le_w]
    have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
    have hb : PrimeSide.psiA c p (p.tau p.d - τ) ≤ c / (p.w * (p.tau p.d - τ) ^ 2) :=
      PrimeSide.psiA_le_div_sq hΔ0.ne'
    have hΔ4 : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 4 := by
      have h8 := hF.eight_le_L
      have : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := pow_le_pow_left₀ hL.le h3 2
      have h2' : (1 : ℝ) ≤ (p.tau p.d - τ) ^ 2 := by nlinarith
      calc p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := this
        _ = (p.tau p.d - τ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (p.tau p.d - τ) ^ 2 * (p.tau p.d - τ) ^ 2 := by gcongr
        _ = (p.tau p.d - τ) ^ 4 := by ring
    calc PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF _) hb 2
      _ = (c / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by field_simp
      _ ≤ (c / p.w) ^ 2 / p.L ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΔ4
  calc PrimeSide.rho p F τ
      ≤ PrimeSide.Wfun c p (τ - p.T) + PrimeSide.Wfun c p (2 * p.T - τ)
          + PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 := hmaj
    _ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 + 2 * (c / p.w) ^ 2 / p.L ^ 2 + (c / p.w) ^ 2 / p.L ^ 2 :=
        add_le_add (add_le_add hW1 hW2) hψ
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

lemma abs_Kinf_sub_Kfun_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
    (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
    |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
  have hρ := rho_le_of_far hF hT h1 h2 h3
  have hρ' := rho_le_of_far hF hT h1' h2' h3'
  calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
      ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
    _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
        gcongr
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

end Tail

section Limit

lemma Kfun_zero_eq_aStar : Kfun 0 = aStar 1 := by
  simp [Kfun, aStar, vStar]

lemma cos_sqrt_two_mul_pos {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2)) :
    0 < Real.cos (Real.sqrt 2 * t) := by
  apply Real.cos_pos_of_mem_Ioo
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [mul_nonneg h0 (by linarith [ht.1] : (0:ℝ) ≤ t + 1 / 2),
    mul_nonneg h0 (by linarith [ht.2] : (0:ℝ) ≤ 1 / 2 - t)]

lemma Kfun_zero_pos : 0 < Kfun 0 := by
  unfold Kfun
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
  · intro t ht
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact cos_sqrt_two_mul_pos ht
  · norm_num

lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  calc |∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)|
      ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t) := by
        apply intervalIntegral.integral_mono_on hab
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)).abs).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
        · intro t ht
          simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
          rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
          exact mul_le_of_le_one_right (cos_sqrt_two_mul_nonneg ht) (Real.abs_cos_le_one _)

lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  unfold paperFT
  have hexp : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by fun_prop
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine hg.ofReal.mul_bdd (c := 1) hexp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]
    simp
  rw [← integral_re_C hint]
  congr 1 with u
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma sharpW_integrable {L : ℝ} : Integrable (sharpW 1 L) := by
  unfold sharpW
  rw [integrable_indicator_iff measurableSet_Icc]
  have hc : Continuous fun u : ℝ => vStar 1 (u / L) := by unfold vStar; fun_prop
  exact hc.integrableOn_Icc

lemma integral_sharpW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u) = L * Kfun x := by
  set f : ℝ → ℝ := fun t => Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t) with hf
  have hind : ∀ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u)
      = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
    intro u
    unfold sharpW vStar
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
      simp only [mul_one]
      congr 2
      field_simp
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_div (f := f) hL.ne',
    smul_eq_mul, show -(L / 2) / L = -(1 : ℝ) / 2 by field_simp; try ring,
    show L / 2 / L = (1 : ℝ) / 2 by field_simp; try ring]
  rfl

lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
  have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
  have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hfi : Integrable fun u => f u * Real.cos (r * u) :=
    hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hgi : Integrable fun u => g u * Real.cos (r * u) :=
    hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  rw [← integral_sub hfi hgi]
  calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
      ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
        refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

variable {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP hlam h8

lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) - P.L T * Kfun x| ≤ 2 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (P.phiD T) r = ∫ u, P.phiD T u ^ 2 * Real.cos (r * u) :=
    re_paperFT_ofReal (hW.integrable_pow two_pos) r
  have hS : ∫ u, sharpW 1 (P.L T) u * Real.cos (r * u) = P.L T * Kfun x :=
    integral_sharpW_mul_cos hL x
  have hL1 : ∫ u, |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u| ≤ 2 * P.w :=
    integral_abs_phiDsq_sub_sharp hP.taper hP.lam_pos hP.lam_le_one hw (by linarith)
  rw [hlam] at hL1
  rw [hV, ← hS]
  exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) sharpW_integrable r).trans hL1

lemma abs_aL_sub_L_mul_Kfun_zero_le :
    |(P.atD T).a T * P.L T - P.L T * Kfun 0| ≤ 4 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have h : |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - aStar P.lam| ≤ 4 * P.w / P.L T :=
    aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8
  rw [hlam, ← Kfun_zero_eq_aStar] at h
  have ha : (P.atD T).a T = (P.L T)⁻¹ * ∫ u, P.phiD T u ^ 2 := by rw [atD_a_eq_av hP]; rfl
  rw [ha]
  have e : (P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) * P.L T - P.L T * Kfun 0
      = ((P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0) * P.L T := by ring
  rw [e, abs_mul, abs_of_pos hL]
  calc |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0| * P.L T ≤ 4 * P.w / P.L T * P.L T :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = 4 * P.w := by field_simp

lemma abs_VPhiR_div_sub_kfun_le (h4π : 4 * Real.pi * P.w ≤ P.L T) (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) / ((P.atD T).a T * P.L T) - kfun x|
      ≤ 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP hlam h8 x
  have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP hlam h8
  have hK0 : 0 < Kfun 0 := Kfun_zero_pos
  have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
  set V := AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) with hV
  set A := (P.atD T).a T * P.L T with hA
  set K := Kfun x with hK'
  set K0 := Kfun 0 with hK0'
  have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have e : V / A - K / K0 = (V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0) := by
    field_simp
    ring
  unfold kfun
  rw [e]
  have h2' : |P.L T * K0 - A| ≤ 4 * P.w := by rw [abs_sub_comm]; exact h2
  calc |(V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0)|
      ≤ |(V - P.L T * K) / A| + |K * (P.L T * K0 - A) / (A * K0)| := abs_add_le _ _
    _ = |V - P.L T * K| / A + |K| * |P.L T * K0 - A| / (A * K0) := by
        rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
    _ ≤ 2 * P.w / A + K0 * (4 * P.w) / (A * K0) := by gcongr
    _ = 6 * P.w / A := by field_simp; ring
    _ ≤ 12 * P.w / P.L T := by
        rw [div_le_div_iff₀ hApos hL]
        nlinarith

end Limit

section Assembly

lemma retained_far {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    {z : ZI Z T} (hz : z ∈ retained Z P T) :
    P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
  unfold xnorm at h1 h2
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * ((z : ℂ).im - T) := by
    have := (le_div_iff₀ hπ).mp h1; linarith
  have h2' : P.L T * ((z : ℂ).im - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
    have := (div_le_iff₀ hπ).mp h2; linarith
  have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
    have := (le_div_iff₀ hπ).mp hd; linarith
  have g1 : 2 * Real.pi * P.L T ≤ (z : ℂ).im - T := by
    have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * ((z : ℂ).im - T) := by nlinarith
    exact le_of_mul_le_mul_left this hL
  have g2 : 2 * Real.pi * P.L T ≤ 2 * T - (z : ℂ).im := by
    have : P.L T * ((z : ℂ).im - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
    have := le_of_mul_le_mul_left this hL
    linarith
  have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩

  have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
    simp only [Params.tau, Params.hgrid, Int.cast_natCast]
  rw [htau]
  have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - (z : ℂ).im
      = (2 * Real.pi * (P.d T : ℝ) - P.L T * ((z : ℂ).im - T)) / P.L T := by
    field_simp
    ring
  rw [e, le_div_iff₀ hL]
  nlinarith

lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
    PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'
      = ∑ k : Fin ((P.atD T).d T), (P.atD T).phiHatR T (γ - (P.atD T).tau T k)
          * (P.atD T).phiHatR T (γ' - (P.atD T).tau T k) := by
  rw [atD_phiHatR_eq hP T]; rfl

lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      = P.L T * AdmWindow.VPhiR (P.phiD T) (γ - γ') := rfl

theorem gram_close_of {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T) (h4π : 4 * Real.pi * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T))
    (Z : ZeroConfig) (z z' : retained Z (P.atD T) T) :
    ‖gram Z (P.atD T) T z z'
        - (kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z') : ℂ)‖
      ≤ 10 * (cDT P.ϱ P.lam / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have hc : 0 < aL2 (P.atD T) T := by
    unfold aL2; rw [Params.atD_L]; positivity
  set K : ℝ := (cDT P.ϱ P.lam / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  rw [gram_apply Z (P.atD T) T (phiHatReal_atD hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'

  obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'

  have hx : 2 * Real.pi * (xret Z (P.atD T) T z - xret Z (P.atD T) T z') / P.L T = γ - γ' := by
    unfold xret xnorm
    rw [Params.atD_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP hlam h8 h4π (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
  rw [hx] at hlim

  set A : ℝ := (P.atD T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (P.phiD T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ' = P.L T * V := Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (P.atD T) T = A * P.L T ^ 2 := by unfold aL2; rw [Params.atD_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z'))|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
    _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
        gcongr
    _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
        field_simp
        ring

end Assembly

section Strips

variable (Z : ZeroConfig)

lemma window_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by
  ext ρ
  simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hc⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hc⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 hb, hc⟩

lemma N_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
  unfold ZeroConfig.N
  rw [window_union Z h1 h2]
  refine finsum_mem_union ?_ (Z.finite_window a b) (Z.finite_window b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, hb', _⟩
  exact absurd hb (not_le.2 hb')

lemma N_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Z.N a b ≤ Z.N c d := by
  unfold ZeroConfig.N
  have hsub : Z.window a b ⊆ Z.window c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  have hfab : (Z.window a b).Finite := Z.finite_window a b
  have hfcd : (Z.window c d).Finite := Z.finite_window c d
  rw [finsum_mem_eq_finite_toFinset_sum _ hfab, finsum_mem_eq_finite_toFinset_sum _ hfcd]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

lemma ncard_window_le_N (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
  unfold ZeroConfig.N
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exact Z.one_le_mult ρ hρ.1

lemma N_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
    (Z.N a (a + n) : ℝ) ≤ n * A₀ * Real.log (|a| + n + 3) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul]
    have : Z.N a a = 0 := by
      unfold ZeroConfig.N
      have : Z.window a a = ∅ := by
        ext ρ
        simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨_, h1, h2⟩; linarith
      rw [this, finsum_mem_empty]
    rw [this]; simp
  | succ n ih =>
    have hsplit : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc]
      exact N_add Z (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) (by linarith)
    rw [hsplit]
    push_cast
    have h1 := hloc (a + n)
    have hlogmono : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogmono' : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith [abs_add_le a (n : ℝ), abs_of_nonneg (n.cast_nonneg : (0:ℝ) ≤ n)])
    have hA : 0 ≤ A₀ := by linarith
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    calc ((Z.N a (a + n) : ℕ) : ℝ) + ((Z.N (a + n) (a + n + 1) : ℕ) : ℝ)
        ≤ n * A₀ * Real.log (|a| + n + 3) + A₀ * Real.log (|a + n| + 3) := add_le_add ih h1
      _ ≤ n * A₀ * Real.log (|a| + (n + 1) + 3) + A₀ * Real.log (|a| + (n + 1) + 3) := by
          gcongr
      _ = (n + 1) * A₀ * Real.log (|a| + (n + 1) + 3) := by ring

lemma N_le_of_local_count_real {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (Z.N a (a + ℓ) : ℝ) ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by
  set n : ℕ := ⌈ℓ⌉₊ with hn
  have hn1 : ℓ ≤ n := Nat.le_ceil ℓ
  have hn2 : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ
  have hA : 0 ≤ A₀ := by linarith
  have hmono : (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := by
    exact_mod_cast N_mono Z le_rfl (by linarith)
  have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + ℓ + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg a, (n.cast_nonneg : (0:ℝ) ≤ n)])
  calc (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := hmono
    _ ≤ n * A₀ * Real.log (|a| + n + 3) := N_le_of_local_count Z hA₀ hloc a n
    _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr

end Strips

section StripInclusion

lemma N0s_le_card_retained_add (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
    (Z.N0s T (2 * T) : ℝ) ≤ (retained Z P T).card
      + Z.N T (T + 2 * Real.pi * P.L T)
      + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
  classical
  set ℓ : ℝ := 2 * Real.pi * P.L T with hℓ
  set ℓ' : ℝ := 2 * Real.pi * P.L T + 2 * Real.pi / P.L T with hℓ'
  set A : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple with hA
  set R : Finset ℂ := (retained Z P T).map (Function.Embedding.subtype _) with hR
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have hsub : A ⊆ (↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T) := by
    rintro ρ ⟨⟨⟨hρc, hT1, hT2⟩, hre⟩, hm⟩
    have hre' : ρ.re = 1 / 2 := hre
    have hm' : Z.mult ρ = 1 := hm
    have hρZ : ρ ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      exact ⟨hρc, by linarith, by linarith⟩
    set z : ZI Z T := ⟨ρ, hρZ⟩ with hz
    have hzS : z ∈ (bdata Z P T).S₁ := by
      simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
    by_cases hx : P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
    · left; left
      rw [Finset.mem_coe, hR, Finset.mem_map]
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · left; right
        refine ⟨hρc, hT1, ?_⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (div_lt_iff₀ hπ).mp hx
        have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
        have := lt_of_mul_lt_mul_left this hL.le
        show ρ.im ≤ T + ℓ
        linarith
      · right
        refine ⟨hρc, ?_, hT2⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (lt_div_iff₀ hπ).mp hx
        have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
        have hd' := (div_lt_iff₀ hπ).mp hd
        have hLℓ' : P.L T * ℓ' = 2 * Real.pi * P.L T ^ 2 + 2 * Real.pi := by
          rw [hℓ']; field_simp
        have : P.L T * (2 * T - ℓ') < P.L T * ρ.im := by nlinarith
        exact lt_of_mul_lt_mul_left this hL.le
  have hfin : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).Finite :=
    ((R.finite_toSet).union (Z.finite_window _ _)).union (Z.finite_window _ _)
  have hN0s : Z.N0s T (2 * T) = A.ncard := rfl
  have hcard : ((↑R : Set ℂ).ncard : ℝ) = (retained Z P T).card := by
    rw [Set.ncard_coe_finset, hR, Finset.card_map]
  have hlo := ncard_window_le_N Z T (T + ℓ)
  have hhi := ncard_window_le_N Z (2 * T - ℓ') (2 * T)
  have hu : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).ncard
      ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_union_le _ _).trans (by gcongr; exact Set.ncard_union_le _ _)
  have hle : A.ncard ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard
      + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_le_ncard hsub hfin).trans hu
  rw [hN0s]
  calc (A.ncard : ℝ) ≤ ((↑R : Set ℂ).ncard : ℝ) + (Z.window T (T + ℓ)).ncard
        + (Z.window (2 * T - ℓ') (2 * T)).ncard := by exact_mod_cast hle
    _ ≤ (retained Z P T).card + Z.N T (T + ℓ) + Z.N (2 * T - ℓ') (2 * T) := by
        rw [hcard]
        have hlo' : ((Z.window T (T + ℓ)).ncard : ℝ) ≤ Z.N T (T + ℓ) := by exact_mod_cast hlo
        have hhi' : ((Z.window (2 * T - ℓ') (2 * T)).ncard : ℝ) ≤ Z.N (2 * T - ℓ') (2 * T) := by
          exact_mod_cast hhi
        linarith

end StripInclusion

section StripCount

lemma strips_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T L : ℝ} (hT : 1 ≤ T)
    (hL1 : 1 ≤ L) (hLT : L ≤ T) (hlogT : Real.log T ≤ L + 2 * Real.pi) :
    (Z.N T (T + 2 * Real.pi * L) : ℝ) + Z.N (2 * T - (2 * Real.pi * L + 2 * Real.pi / L)) (2 * T)
      ≤ 1600 * A₀ * L ^ 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hπ3 := Real.pi_gt_three
  have hA : 0 ≤ A₀ := by linarith
  set ℓ : ℝ := 2 * Real.pi * L with hℓ
  set ℓ' : ℝ := 2 * Real.pi * L + 2 * Real.pi / L with hℓ'
  have hLpos : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by positivity
  have h2πL : 2 * Real.pi / L ≤ 2 * Real.pi * L := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hℓ'0 : 0 ≤ ℓ' := by positivity
  have hℓ'le : ℓ' ≤ 4 * Real.pi * L := by rw [hℓ']; linarith
  have hℓle : ℓ ≤ ℓ' := by
    have : 0 ≤ 2 * Real.pi / L := by positivity
    rw [hℓ, hℓ']; linarith
  have h1 := N_le_of_local_count_real Z hA₀ hloc T hℓ0
  have h2 := N_le_of_local_count_real Z hA₀ hloc (2 * T - ℓ') hℓ'0
  rw [sub_add_cancel] at h2

  set M : ℝ := (6 + 8 * Real.pi) * T with hM
  have hM1 : |T| + ℓ + 4 ≤ M := by
    rw [abs_of_pos (by linarith), hM]; nlinarith
  have hM2 : |2 * T - ℓ'| + ℓ' + 4 ≤ M := by
    have : |2 * T - ℓ'| ≤ 2 * T + ℓ' := by
      rw [abs_le]; constructor <;> linarith
    rw [hM]; nlinarith
  have hlogM : Real.log M ≤ (6 + 10 * Real.pi) * L := by
    have hT0 : 0 < T := by linarith
    rw [hM, Real.log_mul (by positivity) hT0.ne']
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
    nlinarith
  have hlog1 : Real.log (|T| + ℓ + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM1).trans hlogM
  have hlog2 : Real.log (|2 * T - ℓ'| + ℓ' + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM2).trans hlogM
  have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith
  have hcoef' : ℓ + 1 ≤ (4 * Real.pi + 1) * L := by linarith
  have hb1 : (Z.N T (T + ℓ) : ℝ) ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h1.trans ?_
    have h0 : 0 ≤ Real.log (|T| + ℓ + 4) := Real.log_nonneg (by linarith [abs_nonneg T])
    gcongr
  have hb2 : (Z.N (2 * T - ℓ') (2 * T) : ℝ)
      ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h2.trans ?_
    have h0 : 0 ≤ Real.log (|2 * T - ℓ'| + ℓ' + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * T - ℓ')])
    gcongr
  have hL2 : 0 ≤ A₀ * L ^ 2 := by positivity
  have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith
  calc (Z.N T (T + ℓ) : ℝ) + Z.N (2 * T - ℓ') (2 * T)
      ≤ 2 * ((4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L)) := by linarith
    _ = 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) * (A₀ * L ^ 2) := by ring
    _ ≤ 1600 * (A₀ * L ^ 2) := by
        gcongr
    _ = 1600 * A₀ * L ^ 2 := by ring

end StripCount

end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S6.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def multPart (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma mem_S₂_σ {z : ι} (hz : z ∈ D.S₂) : D.σ z = z := by
  simp only [ZeroBlockData.S₂, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_σ {z : ι} (hz : z ∈ D.S₁) : D.σ z = z := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_m {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.2

lemma multPart_posSemidef {c : ℝ} (hc : 0 < c) : (multPart D c).PosSemidef := by
  unfold multPart
  refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rank_multPart_le {c : ℝ} (hc : 0 < c) : (multPart D c).rank ≤ D.s₂ := by
  unfold multPart
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp [ZeroBlockData.s₂]

lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
    P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
  ext k l
  simp only [P₁, Vsimple, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort D.S₁, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  have hσ := mem_S₁_σ D z.2
  have hm := mem_S₁_m D z.2
  have hstar : star (D.v z l) = D.v z l := congrFun (D.star_v_of_onLine hσ) l
  rw [hm, star_div₀, hstar, Nat.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt c : ℂ)) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [div_mul_div_comm, hsq, Complex.ofReal_inv, inv_mul_eq_div]

lemma Q'_eq_multPart_add_blockQ {c : ℝ} (hc : 0 < c) :
    Q' D c = multPart D c + D.blockQ c := by
  unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart multPart
  rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
  abel

theorem regroup_posIndex (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hR := multPart_posSemidef D hc
  have hH : (multPart D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
  rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
  calc posIndex hH
      ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := by
        rw [posIndex_eq_rank_of_posSemidef hR]
        exact Nat.add_le_add (rank_multPart_le D hc) (D.posIndex_blockQ_le Pr hc)


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S7.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

lemma Vsimple_col_le_one {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.S₁) :
    ∑ k, ‖Vsimple D c k z‖ ^ 2 ≤ 1 := by
  have hz : (z : ι) ∈ D.onLine := by
    have := z.2
    simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at this
    exact (D.mem_onLine).mpr this.1
  have hs : ∀ k, ‖Vsimple D c k z‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
    intro k
    simp only [Vsimple]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
      Real.sq_sqrt hc.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hc]
  exact hPois z hz

theorem count_defect (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ)
      + defect (gramS₁_isHermitian D c) ≤ (D.s₁ : ℝ) := by
  classical
  have hb := regroup_posIndex D Pr hc
  have h := stable_rank_trace (Vsimple D c) (Vsimple_col_le_one D hc hPois) (Q'_isHermitian D c) hb
  have e : Vsimple D c * (Vsimple D c)ᴴ + Q' D c = D.blockP c + D.blockQ c := P₁_add_Q' D c
  rw [e] at h
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card D.S₁ : ℝ) = D.s₁ := by rw [Fintype.card_coe]; rfl
  have hdef : defect (gramS₁_isHermitian D c)
      = rtrace (specMap (isHermitian_conjTranspose_mul_self (Vsimple D c)) Psi) := rfl
  rw [hcard] at h
  push_cast at h
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S8.lean ###### -/



noncomputable section

open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by

  set P : Params := paramsOf stdProfile 1 with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := rfl

  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)

  have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
    (fun T => Dcirc Z (mtParams T) T) h7
  intro ε hε
  have h' := h ε hε

  have hHD : HD 1 = 2 - (cStar P.lam)⁻¹ := by rw [hlam, HD, one_div]
  rw [hHD]
  exact h'


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S9.lean ###### -/



noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

set_option linter.unusedVariables false in

theorem kernel_limit (Z : ZeroConfig) (H : PaperInputs Z) (R₀ : ℝ) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      |xret Z (mtParams T) T z - xret Z (mtParams T) T z'| ≤ R₀ →
      ‖gram Z (mtParams T) T z z'
          - (kfun (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : (paramsOf stdProfile 1).lam = 1 := rfl
  obtain ⟨T₀, hT₀⟩ := localHypsCoreD_eventually hP
  set K : ℝ := (cDT (paramsOf stdProfile 1).ϱ (paramsOf stdProfile 1).lam
    / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, eventually_w4pi hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h4π hTT₀ hL1 hLδ
  intro z z' _
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hlam hT h8 h4π hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
      ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2

theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
        ≤ ((retained Z (mtParams T) T).card : ℝ) := by
  intro ε hε
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hA0 : 0 < A₀ := by linarith
  have hπ := Real.pi_pos
  set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
  have hcpos : 0 < c := by positivity
  have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.def hcpos
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
    (tendsto_L hP).eventually_ge_atTop 1, hlittle,
    eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
  have hT0 : 0 < T := by linarith
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef

  have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
    rw [hLdef]
    show 1 * Real.log (T / (2 * Real.pi)) = _
    rw [one_mul, Real.log_div hT0.ne' (by positivity)]
  have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
  have hLlogT : L ≤ Real.log T := by linarith
  have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
  have hLT : L ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogc : Real.log T ≤ c * T := by
    have h := hlog
    simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
    exact h

  have hLpos : 0 < (mtParams T).L T := by show 0 < L; linarith
  have hincl := N0s_le_card_retained_add Z (mtParams T) T hLpos
  have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
  have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
    have e1 : (mtParams T).L T = L := rfl
    rw [e1] at hincl
    linarith

  have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have h := hRvM T hTT₀
    have hℓ₁ : L ≤ ell1 T := by
      show 1 * l T ≤ l T + 2 * Real.log 2 - 1
      have := Real.log_two_gt_d9
      linarith
    have h1 := (abs_le.mp h).1
    have h2 : C * Real.log T ≤ |C| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
    have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith

  have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
    have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
        have : L * L ≤ L * (c * T) := by
          have : L ≤ c * T := hLlogT.trans hlogc
          exact mul_le_mul_of_nonneg_left this (by linarith)
        nlinarith
      have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
        rw [hc]; field_simp
      linarith
    have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        nlinarith
      have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
      have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have hL0 : 0 ≤ L := by linarith
        nlinarith
      calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
        _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
        _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
        _ = ε * T * L / (4 * Real.pi) := by ring
    have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
      field_simp
      ring
    linarith
  have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hN hε.le
    nlinarith [hkey]
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S11.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairCoef (n r : ℕ) : ℝ := 2 / ((n : ℝ) - (r : ℝ))

lemma energyOn_eq_sorted {m : ℕ} (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    energyOn x univ = ∑ r : Fin m × Fin m,
      if r.1 = r.2 then 0 else wfun ((univ.image x).orderEmbOfFin hS r.1
        - (univ.image x).orderEmbOfFin hS r.2) := by
  classical
  set S := univ.image x with hSdef
  set y := S.orderEmbOfFin hS with hydef
  have hy : Function.Injective y := y.injective
  have hSy : univ.image y = S := by
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin S hS
  unfold energyOn
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else wfun (x i - x j))
      = (if x i = x j then 0 else wfun (x i - x j)) := by
    intro i j; simp [hx.eq_iff]
  simp_rw [h1]
  have e1 : ∀ i : ι, ∑ j, (if x i = x j then (0 : ℝ) else wfun (x i - x j))
      = ∑ t ∈ S, (if x i = t then 0 else wfun (x i - t)) := fun i =>
    (sum_image (f := fun t => if x i = t then (0 : ℝ) else wfun (x i - t))
      (fun a _ b _ h => hx h)).symm
  simp_rw [e1]
  rw [← sum_image (f := fun s => ∑ t ∈ S, (if s = t then (0 : ℝ) else wfun (s - t)))
    (fun a _ b _ h => hx h)]
  rw [← hSdef, ← hSy, sum_image (fun a _ b _ h => hy h)]
  simp_rw [sum_image (fun a _ b _ h => hy h)]
  simp only [hy.eq_iff]
  exact (Fintype.sum_prod_type' (f := fun k l => if k = l then (0 : ℝ) else wfun (y k - y l))).symm

lemma window_pairs_le_energy {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (x : ι → ℝ)
    (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          pairCoef n ((b : ℕ) - (a : ℕ))
            * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega

  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    pairCoef n ((t.2.2 : ℕ) - (t.2.1 : ℕ)) * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        pairCoef n ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      pairCoef n ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]

  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q), f t = pairCoef n r * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2, hrdef, ← e1, ← e2, Nat.add_sub_add_left]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]

    have hcard : (T.filter (fun t => φ t = q)).card ≤ n - r := by
      rw [← card_range (n - r)]
      refine card_le_card_of_injOn (fun t => (t.2.1 : ℕ)) ?_ ?_
      · intro t ht
        rw [mem_coe, mem_filter] at ht
        obtain ⟨ht, hφt⟩ := ht
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
        have hb := t.2.2.2
        simp only [coe_range, Set.mem_Iio]
        omega
      · intro t ht t' ht' hee
        rw [mem_coe, mem_filter] at ht ht'
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
        have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
        have e2' : t'.1 + (t'.2.2 : ℕ) = q.2 := congrArg Prod.snd ht'.2
        simp only at hee
        have ha : t.2.1 = t'.2.1 := Fin.ext hee
        have hi : t.1 = t'.1 := by omega
        have hb : t.2.2 = t'.2.2 := Fin.ext (by omega)
        exact Prod.ext hi (Prod.ext ha hb)
    have hr7 : (r : ℝ) < (n : ℝ) := by exact_mod_cast hq3
    have hcoef : 0 ≤ pairCoef n r := by
      unfold pairCoef; apply div_nonneg (by norm_num); linarith
    have hcardR : ((T.filter (fun t => φ t = q)).card : ℝ) ≤ (n : ℝ) - (r : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hq3.le] at this
    calc ((T.filter (fun t => φ t = q)).card : ℝ) * (pairCoef n r * wfun (Y q.2 - Y q.1))
        ≤ ((n : ℝ) - (r : ℝ)) * (pairCoef n r * wfun (Y q.2 - Y q.1)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg hcoef (wfun_nonneg _))
      _ = 2 * wfun (Y q.2 - Y q.1) := by
          have h7 : (n : ℝ) - (r : ℝ) ≠ 0 := by linarith
          unfold pairCoef
          field_simp
  refine (sum_le_sum hfib).trans ?_

  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

theorem block_energy {c : ℝ} {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ energyOn x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by
  classical

  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num

  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ F n p (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), F n p (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [F_windowGaps] at hsum
  rw [sum_add_distrib, ← mul_sum] at hsum

  have hlin : ∑ i ∈ range (m - (n - 1)), (Y (i + (n - 1)) - Y i)
      ≤ ((n : ℝ) - 1) * spanOf x univ := by
    rw [sum_shift_sub]
    have hterm : ∀ i ∈ range (n - 1), Y (m - (n - 1) + i) - Y i ≤ Y (m - 1) - Y 0 := by
      intro i hi
      rw [mem_range] at hi
      have h1 := sortedExt_mono hymono (a := m - (n - 1) + i) (b := m - 1) (by omega) (by omega)
      have h2 := sortedExt_mono hymono (a := 0) (b := i) (by omega) (by omega)
      linarith
    have hspan : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, sortedExt_of_lt y (by omega : m - 1 < m), sortedExt_of_lt y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i₀) (mem_univ j₀))
    calc ∑ i ∈ range (n - 1), (Y (m - (n - 1) + i) - Y i)
        ≤ ∑ i ∈ range (n - 1), (Y (m - 1) - Y 0) := sum_le_sum hterm
      _ = ((n : ℝ) - 1) * (Y (m - 1) - Y 0) := by
          rw [sum_const, card_range, nsmul_eq_mul, hcastn]
      _ ≤ ((n : ℝ) - 1) * spanOf x univ := by nlinarith

  have hquad := window_pairs_le_energy hn hm x hx hS
  simp only [pairCoef] at hquad
  rw [← hydef, ← hYdef] at hquad
  have hp' : 0 ≤ 1 / (p : ℝ) := by positivity
  calc c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ _ := hsum
    _ ≤ (1 / (p : ℝ)) * (((n : ℝ) - 1) * spanOf x univ) + energyOn x univ := by
        gcongr
    _ = energyOn x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by ring


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S12.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma specMap_const_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp

lemma specMap_sub_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun t => t - 1) = A - 1 := by
  have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
  rw [h, specMap_sub, specMap_id, specMap_const_one]

lemma offDiagSqOn_le_frobSq_sub_one (A : Matrix ι ι ℂ) :
    offDiagSqOn A univ ≤ frobSq (A - 1) := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  unfold offDiagSqOn
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs with h
  · positivity
  · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]

theorem block_defect_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    min 1 (offDiagSqOn A univ) ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
  ·
    have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
      sum_congr rfl fun i _ => by simp [Psi, hall i]
    have hfrob := frobSq_specMap hA (fun t => t - 1)
    rw [specMap_sub_one] at hfrob
    rw [hsum, ← hfrob]
    exact (min_le_right _ _).trans (offDiagSqOn_le_frobSq_sub_one A)
  ·
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (min_le_left _ _).trans ?_
    calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
          unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
      _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
          single_le_sum (fun j _ => Psi_nonneg (hA.eigenvalues j)) (mem_univ i)

theorem block_defect {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    min 1 (offDiagSqOn G univ) ≤ defect hG.1 :=
  block_defect_of_isHermitian hG.1


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S13.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sq_sub_two_mul_le_sq {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (h : |b - a| ≤ δ) : a ^ 2 - 2 * δ ≤ b ^ 2 := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_or_gt a b with hab | hab
  · nlinarith
  · rcases le_or_gt δ a with hδa | hδa
    · nlinarith
    · nlinarith

lemma wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ} (h : ‖g - (kfun t : ℂ)‖ ≤ δ) :
    wfun t - 2 * δ ≤ ‖g‖ ^ 2 := by
  have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
  have htri : abs (‖g‖ - |kfun t|) ≤ δ := by
    rw [← hk]; exact (abs_norm_sub_norm_le g _).trans h
  have := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
  rw [sq_abs] at this
  exact this

lemma offDiagSqOn_submatrix (G : Matrix ι ι ℂ) (B : Finset ι) :
    offDiagSqOn (G.submatrix (Subtype.val : B → ι) Subtype.val) univ = offDiagSqOn G B := by
  unfold offDiagSqOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [submatrix_apply, Subtype.ext_iff]

lemma energyOn_subtype (x : ι → ℝ) (B : Finset ι) :
    energyOn (fun i : B => x i) univ = energyOn x B := by
  unfold energyOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [Subtype.ext_iff]

lemma spanOf_subtype_le (x : ι → ℝ) (B : Finset ι) :
    spanOf (fun i : B => x i) univ ≤ spanOf x B := by
  by_cases h1 : (univ : Finset B).Nonempty
  · have h2 : B.Nonempty := by
      obtain ⟨i, -⟩ := h1
      exact ⟨i.1, i.2⟩
    unfold spanOf
    rw [dif_pos h1, dif_pos h2]
    have hs : (univ : Finset B).sup' h1 (fun i : B => x i) ≤ B.sup' h2 x :=
      sup'_le _ _ fun i _ => le_sup' x i.2
    have hi : B.inf' h2 x ≤ (univ : Finset B).inf' h1 (fun i : B => x i) :=
      le_inf' _ _ fun i _ => inf'_le x i.2
    linarith
  · have h0 : spanOf (fun i : B => x i) univ = 0 := by
      unfold spanOf; rw [dif_neg h1]
    rw [h0]
    exact spanOf_nonneg x B

theorem block_bound {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
  classical
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    linarith

  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h

  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith

  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ energyOn x B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := block_energy hn hp hCert hm hcard (fun i : B => x i) hinj
    rw [energyOn_subtype] at h
    have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
    have := mul_le_mul_of_nonneg_left (spanOf_subtype_le x B) hp'
    linarith

  have hspan := spanOf_nonneg x B
  have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith [mul_nonneg hp' hspan]
  · rw [min_eq_right h1.le] at hS12
    nlinarith [mul_nonneg hp' hspan]


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S14.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pinching_partition {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
    ∑ b, blockDefect hM (univ.filter fun i => β i = b) ≤ defect hM := by
  unfold blockDefect defect
  exact rtrace_specMap_pinching_le hM Psi_convexOn β

theorem pinching_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
    defect (hM.submatrix f) ≤ defect hM := by
  unfold defect
  exact rtrace_specMap_submatrix_le hM hf Psi_convexOn Zeta23Ext.StableRankTrace.Psi_nonneg


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S15.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma eq_of_mod_eq_of_overlap {m s s' k : ℕ} (_hm : 0 < m) (h : s % m = s' % m)
    (hs : s ≤ k ∧ k < s + m) (hs' : s' ≤ k ∧ k < s' + m) : s = s' := by
  rcases le_total s s' with h1 | h1
  · have hd : m ∣ s' - s := (Nat.modEq_iff_dvd' h1).mp h
    rcases Nat.eq_zero_or_pos (s' - s) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega
  · have hd : m ∣ s - s' := (Nat.modEq_iff_dvd' h1).mp h.symm
    rcases Nat.eq_zero_or_pos (s - s') with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega

open Classical in

def blockStart (n m j k : ℕ) : ℕ :=
  if h : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m then h.choose else n

lemma blockStart_le (n m j k : ℕ) : blockStart n m j k ≤ n := by
  unfold blockStart
  split_ifs with h
  · have := h.choose_spec.1; omega
  · exact le_rfl

lemma blockStart_eq_iff {n m j k s : ℕ} (hm : 0 < m) (hs : s + m ≤ n) (hj : s % m = j) :
    blockStart n m j k = s ↔ (s ≤ k ∧ k < s + m) := by
  unfold blockStart
  constructor
  · intro h
    split_ifs at h with hex
    · obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      rw [h] at h3; exact h3
    · omega
  · intro hk
    have hex : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m := ⟨s, hs, hj, hk⟩
    rw [dif_pos hex]
    obtain ⟨h1, h2, h3⟩ := hex.choose_spec
    exact eq_of_mod_eq_of_overlap hm (h2.trans hj.symm) h3 hk

theorem offset_average (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : 1 ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + q * spanOf x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ ≤ m * Dtot := by
  classical
  set n := Fintype.card ι with hndef
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm

  rcases lt_or_ge n m with hnm | hnm
  · have : (n : ℝ) - m ≤ 0 := by
      have : (n : ℝ) < m := by exact_mod_cast hnm
      linarith
    nlinarith [mul_nonneg hq (mul_nonneg (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hspan0),
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - n), mul_nonneg (by positivity : (0:ℝ) ≤ m) hDtot]

  have hS : (univ.image x).card = n := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin n → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hymem k)
  have hι'inj : Function.Injective ι' := by
    intro k k' h
    apply hymono.injective
    rw [← (hι' k).2, ← (hι' k').2, h]
  have hbij : Function.Bijective ι' :=
    (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, by simp [hndef]⟩
  set e : Fin n ≃ ι := Equiv.ofBijective ι' hbij with hedef
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hposdef
  set Y := sortedExt y with hYdef
  have hpos_lt : ∀ i, pos i < n := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]

  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBdef
  have hmemB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := by
    intro s i; simp [hBdef]
  set toFin : ℕ → Fin n := fun t => if h : t < n then ⟨t, h⟩ else ⟨0, by omega⟩ with htoFin
  have hcardB : ∀ s, s + m ≤ n → (B s).card = m := by
    intro s hs
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (toFin t)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_coe, hmemB] at hi
        rw [mem_coe, mem_Ico]; exact hi
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmemB]
        have htn : t < n := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
        exact ht
      · intro i hi
        have h := hpos_lt i
        simp only [htoFin, dif_pos h]
        simp only [hposdef, Fin.eta, Equiv.apply_symm_apply]
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        have htn : t < n := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hintB : ∀ s, IsInterval x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega
  have hspanB : ∀ s, s + m ≤ n → spanOf x (B s) ≤ Y (s + (m - 1)) - Y s := by
    intro s hs
    have hne : (B s).Nonempty := by
      rw [← card_pos, hcardB s hs]; exact hm0
    unfold spanOf
    rw [dif_pos hne]
    have h1 : (B s).sup' hne x ≤ Y (s + (m - 1)) := by
      apply sup'_le
      intro i hi
      rw [hmemB] at hi
      rw [hxY]
      exact sortedExt_mono hymono (by omega) (by omega)
    have h2 : Y s ≤ (B s).inf' hne x := by
      apply le_inf'
      intro i hi
      rw [hmemB] at hi
      rw [hxY]
      exact sortedExt_mono hymono (by omega) (hpos_lt i)
    linarith

  set St := range (n - m + 1) with hStdef
  have hmemSt : ∀ s, s ∈ St ↔ s + m ≤ n := by
    intro s; rw [hStdef, mem_range]; omega
  have hsumblock : A * ((n : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + q * ∑ s ∈ St, spanOf x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at h
    have hcast : ((n - m + 1 : ℕ) : ℝ) = (n : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith

  have hspans : ∑ s ∈ St, spanOf x (B s) ≤ ((m : ℝ) - 1) * spanOf x univ := by
    have hY0 : ∀ i ∈ range (m - 1), Y (n - m + 1 + i) - Y i ≤ spanOf x univ := by
      intro i hi
      rw [mem_range] at hi
      have hi' : n - m + 1 + i < n := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨n - m + 1 + i, hi'⟩)
      obtain ⟨b, -, hb⟩ := mem_image.mp (hymem ⟨i, by omega⟩)
      rw [hYdef, sortedExt_of_lt y hi', sortedExt_of_lt y (by omega : i < n), ← ha, ← hb]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ a) (mem_univ b))
    calc ∑ s ∈ St, spanOf x (B s)
        ≤ ∑ s ∈ St, (Y (s + (m - 1)) - Y s) :=
          sum_le_sum fun s hs => hspanB s ((hmemSt s).mp hs)
      _ = ∑ i ∈ range (m - 1), (Y (n - m + 1 + i) - Y i) := sum_shift_sub Y (m - 1) (n - m + 1)
      _ ≤ ∑ i ∈ range (m - 1), spanOf x univ := sum_le_sum hY0
      _ = ((m : ℝ) - 1) * spanOf x univ := by
          rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hm]; norm_num

  have hdefects : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j hj => ?_

          set β : ι → Fin (n + 1) := fun i =>
            ⟨blockStart n m j (pos i), Nat.lt_succ_of_le (blockStart_le n m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ n) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact blockStart_eq_iff hm0 hs hj
          set toFin' : ℕ → Fin (n + 1) := fun s => if h : s < n + 1 then ⟨s, h⟩ else 0 with htoFin'
          have hinj : Set.InjOn toFin' (St.filter (fun s => s % m = j)) := by
            intro s hs s' hs' h
            rw [mem_coe, mem_filter, hmemSt] at hs hs'
            simp only [htoFin', dif_pos (by omega : s < n + 1), dif_pos (by omega : s' < n + 1),
              Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = toFin' s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmemSt] at hs
                have hsn : s < n + 1 := by omega
                rw [← hclass s hs.1 hs.2]
                congr 2
                simp only [htoFin', dif_pos hsn]
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image toFin',
                  Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (n + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]

  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hnm
  calc A * ((n : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ
      ≤ A * ((n : ℝ) - m + 1) - q * ((m : ℝ) - 1) * spanOf x univ := by linarith
    _ ≤ ∑ s ∈ St, Dblk (B s) + q * ∑ s ∈ St, spanOf x (B s)
          - q * ((m : ℝ) - 1) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by nlinarith [mul_le_mul_of_nonneg_left hspans hq]

end Abstract

section Analytic

open Classical

lemma spanOf_xret_le_d (Z : ZeroConfig) (P : Params) (T : ℝ) :
    spanOf (xret Z P T) univ ≤ (P.d T : ℝ) := by
  have hb : ∀ z : retained Z P T,
      P.L T ^ 2 ≤ xret Z P T z ∧ xret Z P T z ≤ (P.d T : ℝ) - P.L T ^ 2 :=
    fun z => (Finset.mem_filter.mp z.2).2
  unfold spanOf
  split_ifs with h
  · have h1 : (univ : Finset (retained Z P T)).sup' h (xret Z P T) ≤ (P.d T : ℝ) - P.L T ^ 2 :=
      sup'_le _ _ fun z _ => (hb z).2
    have h2 : P.L T ^ 2 ≤ (univ : Finset (retained Z P T)).inf' h (xret Z P T) :=
      le_inf' _ _ fun z _ => (hb z).1
    have : 0 ≤ P.L T ^ 2 := sq_nonneg _
    linarith
  · exact Nat.cast_nonneg _

theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      spanOf (xret Z (mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hV : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hLpos : ∀ᶠ T in atTop, 0 < (mtParams T).L T := (tendsto_L hV).eventually_gt_atTop 0
  set K : ℝ := max ((1 + ε) * C / ε) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hc : (0 : ℝ) < 1 / (2 * Real.pi * (K + 1)) := by positivity
  have hlogT : ∀ᶠ T in atTop, ‖Real.log T‖ ≤ (1 / (2 * Real.pi * (K + 1))) * ‖id T‖ :=
    Real.isLittleO_log_id_atTop.def hc
  have hell : ∀ᶠ T in atTop, 1 ≤ ell1 T := by
    have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    have h' : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1))
        atTop atTop := h.atTop_add tendsto_const_nhds
    exact (h'.eventually_ge_atTop 1).mono fun T hT => by unfold ell1 l; linarith
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * Real.pi), hLpos, hlogT, hell]
    with T hT₀ h2π hL hlog hel
  have hpi : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := lt_of_lt_of_le hpi h2π
  have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
  have hLg0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hl0 : 0 ≤ l T := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
  have hN := abs_le.mp (hRvM T hT₀)

  have hLle : (mtParams T).L T ≤ l T := by
    show (paramsOf stdProfile 1).lam * l T ≤ l T
    exact mul_le_of_le_one_left hl0 hV.lam_le_one
  have hl_ell : l T ≤ ell1 T := by
    unfold ell1; linarith [Real.log_two_gt_d9]
  have hd : ((mtParams T).d T : ℝ) ≤ T / (2 * Real.pi) * ell1 T := by
    have h0 : 0 ≤ (mtParams T).L T * T / (2 * Real.pi) := by positivity
    calc ((mtParams T).d T : ℝ) ≤ (mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le h0
      _ = T / (2 * Real.pi) * (mtParams T).L T := by ring
      _ ≤ T / (2 * Real.pi) * ell1 T := by gcongr; exact hLle.trans hl_ell

  have hKA : K * Real.log T ≤ T / (2 * Real.pi) * ell1 T := by
    simp only [Real.norm_eq_abs, id, abs_of_nonneg hLg0, abs_of_pos hT0] at hlog
    have h1 : K * Real.log T ≤ K * (1 / (2 * Real.pi * (K + 1)) * T) :=
      mul_le_mul_of_nonneg_left hlog hK0
    have h2 : K * (1 / (2 * Real.pi * (K + 1)) * T) ≤ T / (2 * Real.pi) := by
      rw [show K * (1 / (2 * Real.pi * (K + 1)) * T) = T / (2 * Real.pi) * (K / (K + 1)) by
        field_simp]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_right (by positivity) this
    have h3 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T :=
      le_mul_of_one_le_right (by positivity) hel
    linarith
  have h1 : (1 + ε) * C / ε * Real.log T ≤ T / (2 * Real.pi) * ell1 T :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hLg0).trans hKA
  have h2 : (1 + ε) * C * Real.log T ≤ ε * (T / (2 * Real.pi) * ell1 T) := by
    have e : (1 + ε) * C * Real.log T = ε * ((1 + ε) * C / ε * Real.log T) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hε.le
  calc spanOf (xret Z (mtParams T) T) univ ≤ ((mtParams T).d T : ℝ) := spanOf_xret_le_d Z _ T
    _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]

end Analytic


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S16.lean ###### -/



noncomputable section

open Filter
open Zeta23.ThmD

namespace Zeta23Ext.Bridge

lemma one_sub_div_pos {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith

theorem solve_linear {N N0 : ℝ → ℝ} {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Phi_n n c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : Phi_n n c m p
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

theorem Phi_paper : Phi (19 / 5000) 269 3000 = (1345000 * HD 1 - 2680) / 1340003 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_paper' :
    Phi (19 / 5000) 269 3000
      = (1345000 * (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹))
          - 2680) / 1340003 := by
  rw [Phi_paper, HD_one]

theorem Phi_lab : Phi (34697 / 10000000) 294 3400
    = (520625000 * HD 1 - 915625) / 518855453 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_lab8 : Phi_n 8 (41763 / 10000000) 246 3200
    = (2460000000 * HD 1 - 5359375) / 2450018643 := by
  unfold Phi_n
  norm_num
  field_simp
  ring


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Main.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

def P₀ : Params := paramsOf stdProfile 1

lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl

lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
  (tendsto_L P₀_valid).eventually_gt_atTop 0

theorem eventually_h7 (Z : ZeroConfig) :
    ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
  filter_upwards [eventually_w8 P₀_valid, eventually_w4pi P₀_valid] with T h8 h4π
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (aD_range_of P₀_valid h8 h4π).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := poissonSqD P₀_valid h8
  have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj phiHatReal hPois)
  have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
    pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
      (toS₁_injective Z P T)
  have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hA, hN, hs]
  linarith [h7, hD]

theorem block_bound_eventually (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + (((n : ℝ) - 1) / (p : ℝ)) * spanOf (xret Z (mtParams T) T) B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hgap : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [kernel_limit Z H ((p : ℝ) / ((n : ℝ) - 1)) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  set q : ℝ := ((n : ℝ) - 1) / (p : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) hp'
  by_cases hsp : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ q * spanOf x B
  · linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ (p : ℝ) / ((n : ℝ) - 1) := by
      have h1 : spanOf x B < 1 / q := by
        rw [lt_div_iff₀ hq0]; linarith
      have h1q : 1 / q = (p : ℝ) / ((n : ℝ) - 1) := by
        rw [hq]; exact one_div_div ((n : ℝ) - 1) (p : ℝ)
      linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hR)
    have h13 := block_bound hn hm hp hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      (xret_injective Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13

theorem pre_solve (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hgap : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg (by linarith) hp'.le
  have hqn : ((n : ℝ) - 1) / (p : ℝ) ≤ (n : ℝ) - 1 := by
    rw [div_le_iff₀ hp']; nlinarith

  set Cn : ℝ := (m : ℝ) + 3 + ((n : ℝ) - 1) * ((m : ℝ) - 1) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually Z H hn hm hp hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    (((n : ℝ) - 1) / (p : ℝ))
    hA' hq0 (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := ((n : ℝ) - 1) / (p : ℝ) with hq
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : q * ((m : ℝ) - 1) * sp ≤ q * ((m : ℝ) - 1) * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 (by linarith))
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hq' : q * ((m : ℝ) - 1) ≤ ((n : ℝ) - 1) * ((m : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hqn (by linarith)
  have hcoef1 : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]; linarith) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀, div_mul_eq_mul_div, mul_div_assoc, div_self hCne, mul_one]
  have hcoef : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N
      = ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N / m := by
    rw [hq]; field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := solve_linear (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) hn hm hA0 (by
      have := pre_solve zetaZeroConfig paperInputs_zeta hn hm hp hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h7 : ((7 : ℕ) : ℝ) - 1 = 6 := by norm_num
  rw [Phi_eq_Phi_n]
  refine n_point_bound 7 c m p (by norm_num) hm hp hc (fun g hg => ?_) ?_
  · exact le_of_le_of_eq (hCert g hg) (F6_eq p g)
  · rw [h7]; exact hA0

theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * HD 1 - 2680) / 1340003 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_paper]
  exact seven_point_bound (19 / 5000) 269 3000 (by norm_num) (by norm_num) (by norm_num) hCert
    (by norm_num)

lemma eventually_Ncount_pos : ∀ᶠ T in atTop, 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0

theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * HD 1 - 915625) / 518855453 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab]
  exact seven_point_bound (34697 / 10000000) 294 3400 (by norm_num) (by norm_num) (by norm_num)
    hCert (by norm_num)

theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * HD 1 - 915625) / 518855453 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := seven_point_bound_lab hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1

theorem eight_point_bound
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5359375) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab8]
  exact n_point_bound 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hCert (by norm_num)

theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5359375) / 2450018643 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := eight_point_bound hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/BridgeW/DefsW.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

structure WCert (n : ℕ) where
  a : Fin n → Fin n → ℝ
  b : Fin (n - 1) → ℝ

variable {n : ℕ}

def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
  ∑ r, W.b r * g r
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then W.a i j * wfun (ptsN n g j - ptsN n g i) else 0

def WCert.B (W : WCert n) : ℝ := ∑ r, W.b r

def WCert.spanMass (W : WCert n) (s : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then W.a i j else 0

structure WCert.Adm (W : WCert n) : Prop where
  a_nonneg : ∀ i j, 0 ≤ W.a i j
  b_nonneg : ∀ r, 0 ≤ W.b r
  capacity : ∀ s : ℕ, W.spanMass s ≤ 2

lemma WCert.B_nonneg {W : WCert n} (hW : W.Adm) : 0 ≤ W.B :=
  sum_nonneg fun r _ => hW.b_nonneg r

def ofFixed (n p : ℕ) : WCert n :=
  ⟨fun i j => 2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)), fun _ => 1 / (p : ℝ)⟩

theorem Fw_ofFixed (n p : ℕ) (g : Fin (n - 1) → ℝ) : Fw (ofFixed n p) g = F n p g := by
  unfold Fw F ofFixed
  simp only
  rw [← mul_sum]

lemma Fw_windowGaps (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
    Fw W (windowGaps n Y i)
      = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
        + ∑ a : Fin n, ∑ b : Fin n,
            if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
  unfold Fw
  have hq : (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (ptsN n (windowGaps n Y i) b - ptsN n (windowGaps n Y i) a) else 0)
      = ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [ptsN_windowGaps, ptsN_windowGaps,
      show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
  rw [hq]
  rfl

section BlockPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sortedOn (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
  sortedExt (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))

def blkPress (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ r : Fin (n - 1), b r * (sortedOn x B ((B.image x).card - (n - 1) + r) - sortedOn x B r)

end BlockPressure


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S11W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma window_pairs_le_energy_w {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega

  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]

  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2]
    rw [sum_congr rfl hconst, ← sum_mul]

    set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
    have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' hee
      rw [mem_coe, mem_filter] at ht ht'
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
      simp only [hψdef] at hee
      have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
      have hi : t.1 = t'.1 := by omega
      exact Prod.ext hi hee
    have hsub : (T.filter (fun t => φ t = q)).image ψ
        ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
            (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      rw [mem_filter] at ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
      obtain ⟨-, hlt⟩ := hmem t ht.1
      rw [mem_filter, mem_product]
      refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
      simp only [hψdef]
      omega
    have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
      have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
          = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
        rw [sum_image hψinj]
      have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
          ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
      have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
          = W.spanMass r := by
        unfold WCert.spanMass
        rw [sum_filter, sum_product]
      rw [h1]
      exact h2.trans (h3 ▸ hW.capacity r)
    exact mul_le_mul_of_nonneg_right hmass (wfun_nonneg _)
  refine (sum_le_sum hfib).trans ?_

  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

lemma sum_gap_shift (Y : ℕ → ℝ) (r N : ℕ) :
    ∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r)) = Y (N + r) - Y r := by
  have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
  simp_rw [h]
  have := Finset.sum_range_sub (fun i => Y (i + r)) N
  simpa using this

theorem block_energy_w {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x univ + W.B * spanOf x univ := by
  classical

  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num

  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum

  have hspan : ∀ r : Fin (n - 1), Y (m - (n - 1) + r) - Y r ≤ spanOf x univ := by
    intro r
    have hr := r.2
    have h1 := sortedExt_mono hymono (a := m - (n - 1) + r) (b := m - 1) (by omega) (by omega)
    have h2 := sortedExt_mono hymono (a := 0) (b := r) (by omega) (by omega)
    have hsp : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, sortedExt_of_lt y (by omega : m - 1 < m), sortedExt_of_lt y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i₀) (mem_univ j₀))
    linarith
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      ≤ W.B * spanOf x univ := by
    rw [sum_comm]
    unfold WCert.B
    rw [sum_mul]
    refine sum_le_sum fun r _ => ?_
    rw [← mul_sum, sum_gap_shift]
    exact mul_le_mul_of_nonneg_left (hspan r) (hW.b_nonneg r)

  have hquad := window_pairs_le_energy_w hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

lemma sortedOn_eq {x : ι → ℝ} {B : Finset ι} {m : ℕ} (hS : (B.image x).card = m) (k : ℕ) :
    sortedOn x B k = sortedExt (⇑((B.image x).orderEmbOfFin hS)) k := by
  unfold sortedOn sortedExt
  by_cases hk : k < (B.image x).card
  · have hk' : k < m := hS ▸ hk
    rw [dif_pos hk, dif_pos hk']
    set f : Fin (B.image x).card → ℝ := fun j => (B.image x).orderEmbOfFin hS ⟨j, hS ▸ j.2⟩
      with hf
    have hfs : ∀ j, f j ∈ B.image x := fun j => Finset.orderEmbOfFin_mem _ hS _
    have hmono : StrictMono f := by
      intro j j' hj
      exact ((B.image x).orderEmbOfFin hS).strictMono (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hj))
    have := Finset.orderEmbOfFin_unique rfl hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]
  · have hk' : ¬ k < m := hS ▸ hk
    rw [dif_neg hk, dif_neg hk']

lemma sortedOn_congr {S S' : Finset ℝ} (h : S = S') :
    sortedExt (⇑(S.orderEmbOfFin (rfl : S.card = S.card)))
      = sortedExt (⇑(S'.orderEmbOfFin (rfl : S'.card = S'.card))) := by
  subst h; rfl

theorem block_energy_w' {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x univ + blkPress W.b x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      = blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hquad := window_pairs_le_energy_w hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

theorem block_energy_blk {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x B + blkPress W.b x B := by
  classical
  have hcard : Fintype.card B = m := by simp [hB]
  have hinj : Function.Injective (fun i : B => x i) := by
    intro i j h
    exact Subtype.ext (hx i.2 j.2 h)
  have h := block_energy_w' hn W hW hCert hm hcard (fun i : B => x i) hinj
  rw [energyOn_subtype] at h
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hP : blkPress W.b (fun i : B => x i) univ = blkPress W.b x B := by
    unfold blkPress sortedOn
    rw [sortedOn_congr himg, himg]
  rw [hP] at h
  exact h


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S13W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem block_bound_w {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + W.B * spanOf x B := by
  classical
  have hBnn : 0 ≤ W.B := WCert.B_nonneg hW

  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h

  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith

  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x B + W.B * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := block_energy_w hn W hW hCert hm hcard (fun i : B => x i) hinj
    rw [energyOn_subtype] at h
    have := mul_le_mul_of_nonneg_left (spanOf_subtype_le x B) hBnn
    linarith

  have hspan := spanOf_nonneg x B
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith [mul_nonneg hBnn hspan]
  · rw [min_eq_right h1.le] at hS12
    nlinarith [mul_nonneg hBnn hspan]

theorem block_bound_w' {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + blkPress W.b x B := by
  classical
  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h
  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 := block_energy_blk hn W hW hCert hm x B hB hx
  have hP0 : 0 ≤ blkPress W.b x B := by
    unfold blkPress
    refine sum_nonneg fun r _ => mul_nonneg (hW.b_nonneg r) ?_

    unfold sortedOn
    have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
    have hr2 := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
    rw [sub_nonneg, sortedExt_of_lt _ hk, sortedExt_of_lt _ hr]
    exact hmono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith
  · rw [min_eq_right h1.le] at hS12
    nlinarith


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S15W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem offset_average_w {n : ℕ} (hn : 2 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ r, 0 ≤ b r)
    (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : n ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A : ℝ) (hA : 0 ≤ A)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + blkPress b x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m)
      - (∑ r, b r) * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ ≤ m * Dtot := by
  classical
  set N := Fintype.card ι with hNdef
  set Bt : ℝ := ∑ r, b r with hBt
  have hBt0 : 0 ≤ Bt := sum_nonneg fun r _ => hb r
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hmn' : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hmq0 : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith

  rcases lt_or_ge N m with hnm | hnm
  · have : (N : ℝ) - m ≤ 0 := by
      have : (N : ℝ) < m := by exact_mod_cast hnm
      linarith
    nlinarith [mul_nonneg hBt0 (mul_nonneg hmq0 hspan0),
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - N), mul_nonneg (by positivity : (0:ℝ) ≤ m) hDtot]

  have hS : (univ.image x).card = N := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin N → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hymem k)
  have hι'inj : Function.Injective ι' := by
    intro k k' h
    apply hymono.injective
    rw [← (hι' k).2, ← (hι' k').2, h]
  have hbij : Function.Bijective ι' :=
    (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, by simp [hNdef]⟩
  set e : Fin N ≃ ι := Equiv.ofBijective ι' hbij with hedef
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hposdef
  set Y := sortedExt y with hYdef
  have hpos_lt : ∀ i, pos i < N := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := by
    intro a b hab hb
    rw [hYdef, sortedExt_of_lt y (lt_trans hab hb), sortedExt_of_lt y hb]
    exact hymono (Fin.mk_lt_mk.mpr hab)

  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBdef
  have hmemB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := by
    intro s i; simp [hBdef]
  set toFin : ℕ → Fin N := fun t => if h : t < N then ⟨t, h⟩ else ⟨0, by omega⟩ with htoFin
  have hcardB : ∀ s, s + m ≤ N → (B s).card = m := by
    intro s hs
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (toFin t)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_coe, hmemB] at hi
        rw [mem_coe, mem_Ico]; exact hi
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmemB]
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
        exact ht
      · intro i hi
        have h := hpos_lt i
        simp only [htoFin, dif_pos h]
        simp only [hposdef, Fin.eta, Equiv.apply_symm_apply]
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hintB : ∀ s, IsInterval x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega

  have hsortB : ∀ s, s + m ≤ N → ∀ k, k < m → sortedOn x (B s) k = Y (s + k) := by
    intro s hs k hk
    have hxinj : Set.InjOn x (B s) := hx.injOn
    have hic : ((B s).image x).card = m := by rw [card_image_of_injOn hxinj, hcardB s hs]
    rw [sortedOn_eq hic, sortedExt_of_lt _ hk]
    set f : Fin m → ℝ := fun j => Y (s + j) with hf
    have hfs : ∀ j, f j ∈ (B s).image x := by
      intro j
      have hj : s + (j : ℕ) < N := by have := j.2; omega
      refine mem_image.mpr ⟨e ⟨s + j, hj⟩, ?_, ?_⟩
      · rw [hmemB, hposdef]
        simp only [Equiv.symm_apply_apply]
        have := j.2
        constructor <;> omega
      · rw [hxY, hposdef]
        simp only [hf, Equiv.symm_apply_apply]
    have hmono : StrictMono f := by
      intro j j' hj
      simp only [hf]
      have := j'.2
      exact hYlt _ _ (by have := Fin.lt_def.mp hj; omega) (by omega)
    have := Finset.orderEmbOfFin_unique hic hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]

  set St := range (N - m + 1) with hStdef
  have hmemSt : ∀ s, s ∈ St ↔ s + m ≤ N := by
    intro s; rw [hStdef, mem_range]; omega
  have hsumblock : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib] at h
    have hcast : ((N - m + 1 : ℕ) : ℝ) = (N : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith

  have hpress : ∑ s ∈ St, blkPress b x (B s) ≤ Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
    have hY0 : ∀ r : Fin (n - 1), ∀ i ∈ range (m - (n - 1)),
        Y (N - m + 1 + i + r) - Y (i + r) ≤ spanOf x univ := by
      intro r i hi
      rw [mem_range] at hi
      have hr := r.2
      have hi' : N - m + 1 + i + r < N := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨N - m + 1 + i + r, hi'⟩)
      obtain ⟨c, -, hc⟩ := mem_image.mp (hymem ⟨i + r, by omega⟩)
      rw [hYdef, sortedExt_of_lt y hi', sortedExt_of_lt y (by omega : i + r < N), ← ha, ← hc]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ a) (mem_univ c))
    have hblk : ∀ s ∈ St, blkPress b x (B s)
        = ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) := by
      intro s hs
      have hs' := (hmemSt s).mp hs
      unfold blkPress
      have hic : ((B s).image x).card = m := by
        rw [card_image_of_injOn hx.injOn, hcardB s hs']
      rw [hic]
      refine sum_congr rfl fun r _ => ?_
      have hr := r.2
      rw [hsortB s hs' _ (by omega), hsortB s hs' _ (by omega)]
    calc ∑ s ∈ St, blkPress b x (B s)
        = ∑ s ∈ St, ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) :=
          sum_congr rfl hblk
      _ = ∑ r : Fin (n - 1), b r * ∑ s ∈ St, (Y (s + (m - (n - 1)) + r) - Y (s + r)) := by
          rw [sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun s _ => ?_
          congr 3
          omega
      _ = ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), (Y (N - m + 1 + i + r) - Y (i + r)) := by
          refine sum_congr rfl fun r _ => ?_
          congr 1
          have := sum_shift_sub (fun t => Y (t + r)) (m - (n - 1)) (N - m + 1)
          simpa only [hStdef] using this
      _ ≤ ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), spanOf x univ := by
          refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (sum_le_sum (hY0 r)) (hb r)
      _ = Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
          rw [sum_const, card_range, nsmul_eq_mul, ← sum_mul, ← hBt]
          have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
            rw [Nat.cast_sub (by omega : n - 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          rw [hcast]; ring

  have hdefects : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j hj => ?_
          set β : ι → Fin (N + 1) := fun i =>
            ⟨blockStart N m j (pos i), Nat.lt_succ_of_le (blockStart_le N m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ N) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact blockStart_eq_iff hm0 hs hj
          set toFin' : ℕ → Fin (N + 1) := fun s => if h : s < N + 1 then ⟨s, h⟩ else 0 with htoFin'
          have hinj : Set.InjOn toFin' (St.filter (fun s => s % m = j)) := by
            intro s hs s' hs' h
            rw [mem_coe, mem_filter, hmemSt] at hs hs'
            simp only [htoFin', dif_pos (by omega : s < N + 1), dif_pos (by omega : s' < N + 1),
              Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = toFin' s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmemSt] at hs
                have hsn : s < N + 1 := by omega
                rw [← hclass s hs.1 hs.2]
                congr 2
                simp only [htoFin', dif_pos hsn]
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image toFin',
                  Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (N + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]

  have hmn : (m : ℝ) ≤ N := by exact_mod_cast hnm
  calc A * ((N : ℝ) - m) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ
      ≤ A * ((N : ℝ) - m + 1) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s)
          - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by linarith

end Abstract


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/MainW.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge
open Classical

def Phi_w (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - 1) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

theorem Phi_w_ofFixed (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 1 ≤ n) (hp : 0 < p) :
    Phi_w n c m (ofFixed n p).B = Phi_n n c m p := by
  unfold Phi_w Phi_n WCert.B ofFixed
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  rw [hcast]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  congr 1
  field_simp

theorem block_bound_eventually_w (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm) (hBpos : 0 < W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + W.B * spanOf (xret Z (mtParams T) T) B := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H (1 / W.B) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  by_cases hsp : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ W.B * spanOf x B
  · linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ 1 / W.B := by
      rw [le_div_iff₀ hBpos]; linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hR)
    have h13 := block_bound_w hn hm W hW hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      (xret_injective Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13

theorem pre_solve_w (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm) (hBpos : 0 < W.B) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - W.B * ((m : ℝ) - 1) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ W.B := hBpos.le

  set Cn : ℝ := (m : ℝ) + 3 + W.B * ((m : ℝ) - 1) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w Z H hn hm W hW hBpos hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    W.B
    hA' hq0 (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := W.B with hq
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : q * ((m : ℝ) - 1) * sp ≤ q * ((m : ℝ) - 1) * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 (by linarith))
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - q * ((m : ℝ) - 1) / m - ε) * N
      = ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem solve_linear_w {N N0 : ℝ → ℝ} {c : ℝ} {n m : ℕ} (K : ℝ) (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (K - ε) * N T ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (K / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have : K / Dn - ε = (K - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

theorem n_point_bound_w (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn : 2 ≤ n) (hm : n ≤ m)
    (hW : W.Adm) (hBpos : 0 < W.B) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := solve_linear_w (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - 1) / m) hn hm hA0 (by
      have := pre_solve_w zetaZeroConfig paperInputs_zeta hn hm W hW hBpos hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

def Phi_w' (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

section SpanPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spanOf_le_blkPress_div {n m : ℕ} (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (b : Fin (n - 1) → ℝ)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ b r)
    (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    spanOf x B ≤ blkPress b x B / bmin := by
  classical
  have hn : 2 ≤ n := by omega
  have hm0 : 0 < m := by omega
  have hne : B.Nonempty := by rw [← card_pos, hB]; exact hm0
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
  have hine : (B.image x).Nonempty := by rw [← card_pos, hic]; exact hm0
  set S := B.image x with hSdef
  set y : ℕ → ℝ := sortedOn x B with hydef
  have hyk : ∀ k (hk : k < m), y k = S.orderEmbOfFin hic ⟨k, hk⟩ := by
    intro k hk
    rw [hydef, sortedOn_eq hic, sortedExt_of_lt _ hk]
  have hmono : ∀ a c, a ≤ c → c < m → y a ≤ y c := by
    intro a c hac hc
    rw [hyk a (lt_of_le_of_lt hac hc), hyk c hc]
    exact (S.orderEmbOfFin hic).monotone (Fin.mk_le_mk.mpr hac)

  have hspan : spanOf x B ≤ y (m - 1) - y 0 := by
    unfold spanOf
    rw [dif_pos hne]
    have h1 : B.sup' hne x ≤ S.max' hine := by
      apply sup'_le
      intro i hi
      exact le_max' _ _ (mem_image_of_mem x hi)
    have h2 : S.min' hine ≤ B.inf' hne x := by
      apply le_inf'
      intro i hi
      exact min'_le _ _ (mem_image_of_mem x hi)
    have hlast : y (m - 1) = S.max' hine := by
      rw [hyk (m - 1) (by omega)]
      exact Finset.orderEmbOfFin_last hic hm0
    have hzero : y 0 = S.min' hine := by
      rw [hyk 0 hm0]
      exact Finset.orderEmbOfFin_zero hic hm0
    rw [hlast, hzero]
    linarith

  have hq1 : n - 1 - 1 < n - 1 := by omega
  have h0 : 0 < n - 1 := by omega
  set r0 : Fin (n - 1) := ⟨0, h0⟩ with hr0
  set r1 : Fin (n - 1) := ⟨n - 1 - 1, hq1⟩ with hr1
  have hterm : ∀ r : Fin (n - 1), 0 ≤ b r * (y (m - (n - 1) + r) - y r) := by
    intro r
    have hr := r.2
    exact mul_nonneg (hbmin.le.trans (hb r)) (sub_nonneg.mpr (hmono _ _ (by omega) (by omega)))
  have hsum : b r0 * (y (m - (n - 1) + r0) - y r0) + b r1 * (y (m - (n - 1) + r1) - y r1)
      ≤ blkPress b x B := by
    unfold blkPress
    rw [← hydef, hic]
    have hr01 : r0 ≠ r1 := by
      intro h; rw [hr0, hr1] at h
      have := Fin.mk.inj_iff.mp h; omega
    have := Finset.add_le_sum (s := univ) (f := fun r : Fin (n - 1) => b r * (y (m - (n - 1) + r) - y r))
      (fun r _ => hterm r) (mem_univ r0) (mem_univ r1) hr01
    simpa using this
  have hmid : y (m - 1) - y 0 ≤ (y (m - (n - 1) + r0) - y r0) + (y (m - (n - 1) + r1) - y r1) := by
    simp only [hr0, hr1]
    have e1 : m - (n - 1) + 0 = m - (n - 1) := by omega
    have e2 : m - (n - 1) + (n - 1 - 1) = m - 1 := by omega
    rw [e1, e2]
    have := hmono (n - 1 - 1) (m - (n - 1)) (by omega) (by omega)
    linarith
  have hb0 := hb r0
  have hb1 := hb r1
  have hnn0 : 0 ≤ y (m - (n - 1) + r0) - y r0 := by
    have := r0.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  have hnn1 : 0 ≤ y (m - (n - 1) + r1) - y r1 := by
    have := r1.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  rw [le_div_iff₀ hbmin]
  nlinarith [mul_le_mul_of_nonneg_right hb0 hnn0, mul_le_mul_of_nonneg_right hb1 hnn1]

end SpanPressure

theorem block_bound_eventually_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + blkPress W.b (xret Z (mtParams T) T) B := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H (1 / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ 1 / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w' hn hm W hW hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : 1 < blkPress W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [lt_div_iff₀ hbmin] at this
      rw [div_mul_cancel₀ _ hbmin.ne'] at this
      exact this
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]

theorem pre_solve_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hmq : (1 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ W.B := WCert.B_nonneg hW

  set Cn : ℝ := (m : ℝ) + 3 + W.B * ((m : ℝ) - ((n : ℝ) - 1)) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w' Z H hn3 h2n W hW hbmin hb hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average_w hn W.b hW.b_nonneg (xret Z (mtParams T) T)
    (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    hA' (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hBeq : (∑ r, W.b r) = W.B := rfl
  rw [hBeq] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := W.B with hq
  set mq : ℝ := (m : ℝ) - ((n : ℝ) - 1) with hmqdef
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q mq η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have hmq0 : (0 : ℝ) ≤ mq := by linarith
  have step2 : q * mq * sp ≤ q * mq * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 hmq0)
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + 3 + q * mq) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + 3 + q * mq) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * mq) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * mq - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - q * mq / m - ε) * N
      = ((m : ℝ) * HD 1 - q * mq - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem n_point_bound_w' (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have h := solve_linear_w (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn hm hA0
    (by
      have := pre_solve_w' zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/Fixed.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset Filter
open scoped BigOperators
open Zeta23 Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

theorem ofFixed_spanMass_le (n p : ℕ) (s : ℕ) : (ofFixed n p).spanMass s ≤ 2 := by
  classical
  set P : Finset (Fin n × Fin n) :=
    (univ ×ˢ univ).filter fun q : Fin n × Fin n => (q.1 : ℕ) < (q.2 : ℕ) ∧ (q.2 : ℕ) - (q.1 : ℕ) = s
    with hP
  have e : (ofFixed n p).spanMass s = ∑ q ∈ P, (2 / ((n : ℝ) - (((q.2 : ℕ) - (q.1 : ℕ) : ℕ) : ℝ))) := by
    unfold WCert.spanMass ofFixed
    rw [hP, sum_filter, sum_product]
  rw [e]
  by_cases hs : 0 < s ∧ s < n
  · obtain ⟨hs0, hsn⟩ := hs
    have hconst : ∀ q ∈ P, (2 / ((n : ℝ) - (((q.2 : ℕ) - (q.1 : ℕ) : ℕ) : ℝ))) = 2 / ((n : ℝ) - (s : ℝ)) := by
      intro q hq
      rw [hP, mem_filter] at hq
      rw [hq.2.2]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    have hcard : P.card ≤ n - s := by
      rw [← card_range (n - s)]
      refine card_le_card_of_injOn (fun q => (q.1 : ℕ)) ?_ ?_
      · intro q hq
        rw [mem_coe, hP, mem_filter] at hq
        have h2 := q.2.2
        simp only [coe_range, Set.mem_Iio]
        omega
      · intro q hq q' hq' h
        rw [mem_coe, hP, mem_filter] at hq hq'
        simp only at h
        have h1 : q.1 = q'.1 := Fin.ext h
        have h2 : q.2 = q'.2 := Fin.ext (by omega)
        exact Prod.ext h1 h2
    have hns : (s : ℝ) < (n : ℝ) := by exact_mod_cast hsn
    have hcardR : (P.card : ℝ) ≤ (n : ℝ) - (s : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hsn.le] at this
    have hpos : 0 < (n : ℝ) - (s : ℝ) := by linarith
    calc (P.card : ℝ) * (2 / ((n : ℝ) - (s : ℝ)))
        ≤ ((n : ℝ) - (s : ℝ)) * (2 / ((n : ℝ) - (s : ℝ))) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 2 := by field_simp
  · have hempty : P = ∅ := by
      rw [hP, filter_eq_empty_iff]
      intro q _
      have h2 := q.2.2
      intro hq
      apply hs
      omega
    rw [hempty, sum_empty]
    norm_num

theorem ofFixed_adm (n p : ℕ) : (ofFixed n p).Adm := by
  refine ⟨fun i j => ?_, fun _ => ?_, ofFixed_spanMass_le n p⟩
  · unfold ofFixed
    simp only
    have hj := j.2
    have h1 : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (j : ℕ) - (i : ℕ) ≤ n - 1 := by omega
      have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [← h3]; exact_mod_cast h2
    apply div_nonneg (by norm_num); linarith
  · unfold ofFixed; simp only; positivity

theorem ofFixed_B (n p : ℕ) (hn : 1 ≤ n) : (ofFixed n p).B = ((n : ℝ) - 1) / (p : ℝ) := by
  unfold WCert.B ofFixed
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_one]
  ring

theorem n_point_bound_fixed' (n : ℕ) (c : ℝ) (m p : ℕ) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m (((n : ℝ) - 1) / (p : ℝ)) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have hn1 : 1 ≤ n := by omega
  rw [← ofFixed_B n p hn1]
  have hp' : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  refine n_point_bound_w' n c m (ofFixed n p) hn3 h2n (ofFixed_adm n p) hp'
    (fun r => le_of_eq rfl) hc (fun g hg => ?_) hA0
  rw [Fw_ofFixed]; exact hCert g hg

theorem eight_point_bound_w'
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5228125) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have h := n_point_bound_fixed' 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hCert (by norm_num)
  have hPhi : Phi_w' 8 (41763 / 10000000) 246 (((8 : ℕ) - 1 : ℝ) / ((3200 : ℕ) : ℝ))
      = (2460000000 * HD 1 - 5228125) / 2450018643 := by
    unfold Phi_w'
    norm_num
    field_simp
    ring
  rw [hPhi] at h
  exact h

theorem eight_point_bound_w'_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5228125) / 2450018643 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := eight_point_bound_w' hCert ε hε
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1


end Zeta23Ext.BridgeW

end

/-! ###### source module: ThreePoint/Base.lean ###### -/



noncomputable section
open Real intervalIntegral

namespace Zeta23Ext.Bridge.ThreePoint

def taylorCos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800

def taylorSin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800

def taylorErr : ℝ := 13/5748019200

theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]

private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ taylorErr := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  unfold taylorErr; nlinarith

theorem cos_lower {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    taylorCos u - taylorErr ≤ Real.cos θ := by
  have h0u : 0 ≤ u := h0.trans hu
  have hmono : Real.cos u ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans one_le_pi) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).1
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem cos_upper {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ taylorCos l + taylorErr := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem sin_lower {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    taylorSin l - taylorErr ≤ Real.sin θ := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

theorem sin_upper {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    Real.sin θ ≤ taylorSin u + taylorErr := by
  have h0u : 0 ≤ u := h0.trans hu
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin θ ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).2
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

theorem integral_cos_mul_eq_sinc (c : ℝ) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; norm_num
  · have hc2 : c / 2 ≠ 0 := by simpa using hc
    rw [integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
      show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
      Real.sin_neg, smul_eq_mul]
    field_simp
    ring

private lemma cos_mul_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t)) MeasureTheory.volume a b :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem Kfun_eq_sinc (x : ℝ) :
    Kfun x =
      (Real.sinc ((Real.sqrt 2 - 2 * Real.pi * x) / 2)
        + Real.sinc ((Real.sqrt 2 + 2 * Real.pi * x) / 2)) / 2 := by
  have key : ∀ t : ℝ, Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
      = (Real.cos ((Real.sqrt 2 - 2 * Real.pi * x) * t)
          + Real.cos ((Real.sqrt 2 + 2 * Real.pi * x) * t)) / 2 := by
    intro t
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  unfold Kfun
  simp_rw [key]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (cos_mul_intervalIntegrable _ _ _)
      (cos_mul_intervalIntegrable _ _ _),
    integral_cos_mul_eq_sinc, integral_cos_mul_eq_sinc]

def gam : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)

private lemma sqrt2_half_bounds :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

private lemma sin_sqrt2_half_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hb.1]) ?_
  linarith [hb.2, Real.pi_gt_three]

theorem cos_sqrt2_half_bounds :
    (7602445947/10^10 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) ∧
      Real.cos (Real.sqrt 2 / 2) ≤ 7602445994/10^10 := by
  have hb := sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := cos_lower h0 hb.2 (by norm_num)
    have h : (7602445947/10^10 : ℝ)
        ≤ taylorCos (7071067811865475245/10^19) - taylorErr := by
      unfold taylorCos taylorErr; norm_num
    linarith
  · have := cos_upper (by norm_num) hb.1 (by linarith [hb.2])
    have h : taylorCos (7071067811865475244/10^19 : ℝ) + taylorErr
        ≤ 7602445994/10^10 := by
      unfold taylorCos taylorErr; norm_num
    linarith

theorem sin_sqrt2_half_bounds :
    (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) ∧
      Real.sin (Real.sqrt 2 / 2) ≤ 6496369414/10^10 := by
  have hb := sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := sin_lower (by norm_num) hb.1 (by linarith [hb.2])
    have h : (6496369368/10^10 : ℝ)
        ≤ taylorSin (7071067811865475244/10^19) - taylorErr := by
      unfold taylorSin taylorErr; norm_num
    linarith
  · have := sin_upper h0 hb.2 (by norm_num)
    have h : taylorSin (7071067811865475245/10^19 : ℝ) + taylorErr
        ≤ 6496369414/10^10 := by
      unfold taylorSin taylorErr; norm_num
    linarith

theorem gam_bounds : (8274992907/10^10 : ℝ) ≤ gam ∧ gam ≤ 8274993018/10^10 := by
  have hb := sqrt2_half_bounds
  have hc := cos_sqrt2_half_bounds
  have hs := sin_sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  have hprodl : (7071067811865475244/10^19 : ℝ) * (7602445947/10^10)
      ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
    mul_le_mul hb.1 hc.1 (by norm_num) h0
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2)
      ≤ (7071067811865475245/10^19 : ℝ) * (7602445994/10^10) :=
    mul_le_mul hb.2 hc.2 (by linarith [hc.1]) (by norm_num)
  constructor
  · rw [gam, le_div_iff₀ hspos]; nlinarith [hprodl, hs.2]
  · rw [gam, div_le_iff₀ hspos]; nlinarith [hprodu, hs.1]

private lemma kfun_aux (a b : ℝ) (ha : a ≠ 0) (hsa : Real.sin a ≠ 0)
    (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ((Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)) / 2) / (Real.sin a / a)
      = (a^2 * Real.cos b - a * b * (Real.cos a / Real.sin a) * Real.sin b) / (a^2 - b^2) := by
  have hab : a^2 - b^2 ≠ 0 := by
    have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [hfac]; exact mul_ne_zero h1 h2
  rw [Real.sin_sub, Real.sin_add]
  field_simp
  ring

theorem kfun_closed (x : ℝ) (h : 1 - 2*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := by
  have hb := sqrt2_half_bounds
  set a : ℝ := Real.sqrt 2 / 2 with ha_def
  set b : ℝ := Real.pi * x with hb_def
  have ha2 : a^2 = 1/2 := by
    rw [ha_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have ha : a ≠ 0 := by positivity
  have hsa : Real.sin a ≠ 0 := ne_of_gt sin_sqrt2_half_pos
  have h1 : a - b ≠ 0 := by
    intro hz
    apply h
    have : b = a := by linarith [sub_eq_zero.mp hz]
    rw [this]; nlinarith [ha2]
  have h2 : a + b ≠ 0 := by
    intro hz
    apply h
    have : b = -a := by linarith
    rw [this]; nlinarith [ha2]
  have hK : Kfun x = (Real.sin (a - b)/(a - b) + Real.sin (a + b)/(a + b))/2 := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*x)/2 = a - b by rw [ha_def, hb_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*x)/2 = a + b by rw [ha_def, hb_def]; ring,
      Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  have hK0 : Kfun 0 = Real.sin a / a := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      Real.sinc_of_ne_zero ha]
    ring
  have hgam : gam = a * (Real.cos a / Real.sin a) := by
    rw [gam, ← ha_def]; field_simp
  have hne1 : (1/2 : ℝ) - b^2 ≠ 0 := by
    intro hz; apply h; linarith
  rw [kfun, hK, hK0, kfun_aux a b ha hsa h1 h2, hgam, ha2,
    div_eq_div_iff hne1 h]
  ring

theorem pi_lo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20

theorem pi_hi : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

theorem wfun_ge (x nlo dhi : ℝ) (hnlo : 0 ≤ nlo) (hdhi : 0 < dhi)
    (hD0 : 1 < 2*(Real.pi*x)^2) (hD : 2*(Real.pi*x)^2 - 1 ≤ dhi)
    (hN : nlo ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)|) :
    (nlo/dhi)^2 ≤ wfun x := by
  have hne : 1 - 2*(Real.pi*x)^2 ≠ 0 := by intro hz; nlinarith
  have hk : kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := kfun_closed x hne
  have hw : wfun x = kfun x ^ 2 := rfl
  set N : ℝ := Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) with hN_def
  set Dd : ℝ := 1 - 2*(Real.pi*x)^2 with hD_def
  have hNsq : nlo^2 ≤ N^2 := by
    have := abs_nonneg N
    nlinarith [sq_abs N]
  have h1 : Dd < 0 := by rw [hD_def]; linarith
  have hDsq : Dd^2 ≤ dhi^2 := by nlinarith
  have hDpos : 0 < Dd^2 := by positivity
  rw [hw, hk, div_pow, div_pow, div_le_div_iff₀ (by positivity) hDpos]
  nlinarith [sq_nonneg nlo, sq_nonneg N, hNsq, hDsq, hDpos]

lemma abs_ge_of_le {N nlo : ℝ} (h : nlo ≤ N) : nlo ≤ |N| := h.trans (le_abs_self N)

lemma abs_ge_of_ge {N nlo : ℝ} (h : N ≤ -nlo) : nlo ≤ |N| :=
  le_trans (by linarith) (neg_le_abs N)

lemma cs_h1 : Real.cos (Real.pi*(1/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(1/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(1/2:ℝ) = Real.pi/2 by ring]; simp

lemma cs_1 : Real.cos (Real.pi*(1:ℝ)) = -1 ∧ Real.sin (Real.pi*(1:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(1:ℝ) = Real.pi by ring]; simp

lemma cs_h3 : Real.cos (Real.pi*(3/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(3/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(3/2:ℝ) = Real.pi/2 + Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_2 : Real.cos (Real.pi*(2:ℝ)) = 1 ∧ Real.sin (Real.pi*(2:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(2:ℝ) = 2*Real.pi by ring]; simp

lemma cs_h5 : Real.cos (Real.pi*(5/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(5/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(5/2:ℝ) = Real.pi/2 + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_3 : Real.cos (Real.pi*(3:ℝ)) = -1 ∧ Real.sin (Real.pi*(3:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(3:ℝ) = Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_h7 : Real.cos (Real.pi*(7/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(7/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(7/2:ℝ) = Real.pi/2 + Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_4 : Real.cos (Real.pi*(4:ℝ)) = 1 ∧ Real.sin (Real.pi*(4:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(4:ℝ) = 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_h9 : Real.cos (Real.pi*(9/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(9/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(9/2:ℝ) = Real.pi/2 + 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cos_flip (a x : ℝ) : Real.cos (Real.pi*(x-a)) = Real.cos (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.cos_neg]

lemma sin_flip (a x : ℝ) : Real.sin (Real.pi*(x-a)) = -Real.sin (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.sin_neg]

def taylorSinc (z : ℝ) : ℝ :=
  1 - z^2/6 + z^4/120 - z^6/5040 + z^8/362880 - z^10/39916800

theorem sinc_taylor (z : ℝ) (hz : |z| ≤ 1) : taylorSinc z - taylorErr ≤ Real.sinc z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · norm_num [Real.sinc_zero, taylorSinc, taylorErr]
  · have ht := (cos_sin_taylor12 z hz).2
    have hzpos : 0 < |z| := abs_pos.mpr hz0
    have hpow : |z|^12 * (13/5748019200) ≤ |z| * taylorErr := by
      have h11 : |z|^11 ≤ 1 := pow_le_one₀ (abs_nonneg z) hz
      have hsplit : |z|^12 = |z| * |z|^11 := by ring
      rw [hsplit]
      unfold taylorErr
      nlinarith [abs_nonneg z]
    have key : |Real.sin z - z * taylorSinc z| ≤ |z| * taylorErr := by
      have hpoly : z * taylorSinc z
          = z - z^3/6 + z^5/120 - z^7/5040 + z^9/362880 - z^11/39916800 := by
        unfold taylorSinc; ring
      rw [hpoly]
      exact le_trans ht hpow
    have habs : |(Real.sin z - z * taylorSinc z)/z| ≤ taylorErr := by
      rw [abs_div, div_le_iff₀ hzpos]
      exact le_of_le_of_eq key (mul_comm _ _)
    have hsplit : Real.sin z / z = (Real.sin z - z * taylorSinc z)/z + taylorSinc z := by
      field_simp; ring
    rw [Real.sinc_of_ne_zero hz0, hsplit]
    linarith [(abs_le.mp habs).1]

private lemma sqrt2_bounds : (14142135623/10^10 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 14142135624/10^10 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

theorem wfun_window (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : (19/100 : ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have h2 := sqrt2_bounds
  set A : ℝ := (Real.sqrt 2 - 2*Real.pi*x)/2 with hA
  set B : ℝ := (Real.sqrt 2 + 2*Real.pi*x)/2 with hB
  have hAlo : (-8637/10000 : ℝ) ≤ A := by rw [hA]; nlinarith
  have hAhi : A ≤ 7072/10000 := by rw [hA]; nlinarith
  have hAabs : |A| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hA2 : A^2 ≤ 7460/10000 := by nlinarith
  have hsincA : (87557/100000 : ℝ) ≤ Real.sinc A := by
    have h := sinc_taylor A hAabs
    have hq : (87557/100000 : ℝ) ≤ taylorSinc A - taylorErr := by
      unfold taylorSinc taylorErr
      nlinarith [sq_nonneg A, sq_nonneg (A^2), sq_nonneg (A^3), sq_nonneg (A^4),
        sq_nonneg (A^5), hA2, sq_nonneg (A^2 - 7460/10000)]
    linarith
  have hBlo : (7071/10000 : ℝ) < B := by rw [hB]; nlinarith
  have hBhi : B ≤ 22780/10000 := by rw [hB]; nlinarith
  have hsincB : (0:ℝ) ≤ Real.sinc B := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      (by linarith)
  have hK : (43778/100000 : ℝ) ≤ Kfun x := by
    rw [Kfun_eq_sinc, ← hA, ← hB]; linarith
  have hK0 : Kfun 0 = Real.sinc (Real.sqrt 2/2) := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring]
    ring
  have hK0le : Kfun 0 ≤ 1 := by rw [hK0]; exact Real.sinc_le_one _
  have hK0pos : 0 < Kfun 0 := by
    rw [hK0, Real.sinc_of_ne_zero (by positivity)]
    exact div_pos sin_sqrt2_half_pos (by linarith [sqrt2_bounds.1])
  have hk : (43778/100000 : ℝ) ≤ kfun x := by
    rw [kfun, le_div_iff₀ hK0pos]
    nlinarith
  have hw : wfun x = kfun x ^ 2 := rfl
  rw [hw]; nlinarith

lemma trig_shift (a y : ℝ) :
    Real.cos (Real.pi * (a + y)) =
        Real.cos (Real.pi*a) * Real.cos (Real.pi*y) - Real.sin (Real.pi*a) * Real.sin (Real.pi*y)
      ∧ Real.sin (Real.pi * (a + y)) =
        Real.sin (Real.pi*a) * Real.cos (Real.pi*y) + Real.cos (Real.pi*a) * Real.sin (Real.pi*y) := by
  constructor
  · rw [mul_add, Real.cos_add]
  · rw [mul_add, Real.sin_add]

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### helper lemmas for the cell certificates ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint

/-- Interval product, lower end, for a nonnegative first factor: `P s ≥ P c ≥ min (a c) (b c)`. -/
theorem prod_lo {P s a b c m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h3 : c ≤ s)
    (k1 : m ≤ a * c) (k3 : m ≤ b * c) : m ≤ P * s := by
  rcases le_total 0 c with hc | hc
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hc, mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hc), mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]

/-- Interval product, upper end, for a nonnegative first factor: `P s ≤ P d ≤ max (a d) (b d)`. -/
theorem prod_hi {P s a b d m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h4 : s ≤ d)
    (k2 : a * d ≤ m) (k4 : b * d ≤ m) : P * s ≤ m := by
  rcases le_total 0 d with hd | hd
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) hd, mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 hd), mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]

/-- Product of nonnegative lower bounds. -/
theorem mul_ge_of {P s a c m : ℝ} (h1 : a ≤ P) (h2 : c ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hm : m ≤ a * c) : m ≤ P * s :=
  hm.trans (mul_le_mul h1 h2 hc (ha.trans h1))

/-- Product of upper bounds of nonnegative factors. -/
theorem mul_le_of {P s b d m : ℝ} (h1 : P ≤ b) (h2 : s ≤ d) (hP : 0 ≤ P) (hs : 0 ≤ s)
    (hm : b * d ≤ m) : P * s ≤ m :=
  (mul_le_mul h1 h2 hs (hP.trans h1)).trans hm

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### verified rational certificate checker (cells, chains, boxes, cover): the four-point instance, kept
for the constants, the anchor table and the trig lemmas that the integer checker below reuses ###### -/

section CheckerDefs

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Rational mirrors of the enclosure constants -/

/-- Horner forms of the twelve-term Taylor polynomials (fewer rational operations for the kernel). -/
def taylorCosQ (t : ℚ) : ℚ :=
  let s := t * t
  1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
def taylorSinQ (t : ℚ) : ℚ :=
  let s := t * t
  t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
def errQ : ℚ := 13/5748019200
def piLoQ : ℚ := 314159265358979323846 / 10^20
def piHiQ : ℚ := 314159265358979323847 / 10^20
def gamLoQ : ℚ := 8274992907 / 10^10
def gamHiQ : ℚ := 8274993018 / 10^10

/-- rounding to `10⁻¹²`, downwards and upwards -/
def floorD (x : ℚ) : ℚ := ((⌊x * 1000000000000⌋ : ℤ) : ℚ) / 1000000000000
def ceilD (x : ℚ) : ℚ := ((⌈x * 1000000000000⌉ : ℤ) : ℚ) / 1000000000000

/-- `(cos (π k/2), sin (π k/2))` as integers. -/
def csA : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k+1 => (-(csA k).2, (csA k).1)

def imulZ (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
def isub (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)

/-- A table cell: the interval `[L, U]`, its anchor `A = k/2`, the side (`true`: `x − A`,
`false`: `A − x`), and the claimed lower bound `W ≤ wfun` on the cell. -/
structure Cell where
  (L U : ℚ) (k : ℕ) (side : Bool) (W : ℚ)

instance : Inhabited Cell := ⟨⟨0, 0, 0, true, 0⟩⟩

namespace Cell
def A (c : Cell) : ℚ := (c.k : ℚ) / 2
def rlo (c : Cell) : ℚ := if c.side then c.L - c.A else c.A - c.U
def rhi (c : Cell) : ℚ := if c.side then c.U - c.A else c.A - c.L
def TL (c : Cell) : ℚ := floorD (piLoQ * c.rlo)
def TU (c : Cell) : ℚ := ceilD (piHiQ * c.rhi)
def CI (c : Cell) : ℚ × ℚ := (floorD (taylorCosQ c.TU - errQ), ceilD (taylorCosQ c.TL + errQ))
def SI (c : Cell) : ℚ × ℚ := (floorD (taylorSinQ c.TL - errQ), ceilD (taylorSinQ c.TU + errQ))
def cA (c : Cell) : ℤ := (csA c.k).1
def sA (c : Cell) : ℤ := (csA c.k).2
def CX (c : Cell) : ℚ × ℚ :=
  if c.side then isub (imulZ c.cA c.CI) (imulZ c.sA c.SI) else iadd (imulZ c.cA c.CI) (imulZ c.sA c.SI)
def SX (c : Cell) : ℚ × ℚ :=
  if c.side then iadd (imulZ c.sA c.CI) (imulZ c.cA c.SI) else isub (imulZ c.sA c.CI) (imulZ c.cA c.SI)
def BL (c : Cell) : ℚ := floorD (piLoQ * c.L)
def BU (c : Cell) : ℚ := ceilD (piHiQ * c.U)
def P2L (c : Cell) : ℚ := floorD (2 * gamLoQ * c.BL)
def P2U (c : Cell) : ℚ := ceilD (2 * gamHiQ * c.BU)
def TLO (c : Cell) : ℚ := floorD (min (c.P2L * c.SX.1) (c.P2U * c.SX.1))
def THI (c : Cell) : ℚ := ceilD (max (c.P2L * c.SX.2) (c.P2U * c.SX.2))
def NLO (c : Cell) : ℚ := max 0 (max (c.CX.1 - c.THI) (c.TLO - c.CX.2))
def DHI (c : Cell) : ℚ := ceilD (2 * c.BU * c.BU - 1)
def Wc (c : Cell) : ℚ := (c.NLO / c.DHI)^2
def ok (c : Cell) : Bool :=
  decide (0 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.rlo) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL) && decide (0 ≤ c.P2L)
    && decide (1 < 2 * c.BL * c.BL) && decide (0 < c.DHI) && decide (c.W ≤ c.Wc)
end Cell

/-! ### Chains of cells covering an interval -/

def chainW (cs : List Cell) : List ℕ → ℚ
  | [] => 0
  | i :: rest => if rest.isEmpty then (cs.getD i default).W else min (cs.getD i default).W (chainW cs rest)

def chainCheck (cs : List Cell) : ℚ → ℚ → List ℕ → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, i :: rest =>
      decide (i < cs.length) && decide ((cs.getD i default).L ≤ lo)
        && chainCheck cs (cs.getD i default).U hi rest

def termW (cs : List Cell) (idxs : List ℕ) : ℚ := if idxs.isEmpty then 0 else chainW cs idxs
def termCheck (cs : List Cell) (lo hi : ℚ) (idxs : List ℕ) : Bool :=
  idxs.isEmpty || chainCheck cs lo hi idxs

/-! ### Boxes and bisection trees for the four-point functional (rational instance; not used by the weighted path) -/

structure Box where
  (xl xu yl yu zl zu : ℚ)
  deriving DecidableEq

inductive Tree
  | leaf (t0 t1 t2 t3 t4 t5 : List ℕ)
  | split (ax : ℕ) (q : ℚ) (lo hi : Tree)

def leafCheck (cs : List Cell) (c p : ℚ) (b : Box) (t0 t1 t2 t3 t4 t5 : List ℕ) : Bool :=
  termCheck cs b.xl b.xu t0 && termCheck cs b.yl b.yu t1 && termCheck cs b.zl b.zu t2
    && termCheck cs (b.xl + b.yl) (b.xu + b.yu) t3 && termCheck cs (b.yl + b.zl) (b.yu + b.zu) t4
    && termCheck cs (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) t5
    && decide (c ≤ (b.xl + b.yl + b.zl) / p
        + 2/3 * termW cs t0 + 2/3 * termW cs t1 + 2/3 * termW cs t2
        + termW cs t3 + termW cs t4 + 2 * termW cs t5)

def treeCheck (cs : List Cell) (c p : ℚ) : Box → Tree → Bool
  | b, .leaf t0 t1 t2 t3 t4 t5 => leafCheck cs c p b t0 t1 t2 t3 t4 t5
  | b, .split ax q lo hi =>
      if ax = 0 then treeCheck cs c p {b with xu := q} lo && treeCheck cs c p {b with xl := q} hi
      else if ax = 1 then treeCheck cs c p {b with yu := q} lo && treeCheck cs c p {b with yl := q} hi
      else if ax = 2 then treeCheck cs c p {b with zu := q} lo && treeCheck cs c p {b with zl := q} hi
      else false

/-! ### The one-dimensional cover and the trees over the bad triples -/

/-- segments `(a, b, chain)`, contiguous from `pos`; an empty chain marks a bad segment. -/
def coverCheck (cs : List Cell) (lvl : ℚ) : ℚ → ℚ → List (ℚ × ℚ × List ℕ) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, ch) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (ch.isEmpty || (chainCheck cs a b ch && decide (lvl ≤ chainW cs ch)))
        && coverCheck cs lvl b S rest

def badOf (cover : List (ℚ × ℚ × List ℕ)) : List (ℚ × ℚ) :=
  cover.filterMap fun s => if s.2.2.isEmpty then some (s.1, s.2.1) else none

def boxOf (bad : List (ℚ × ℚ)) (i j k : ℕ) : Box :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2⟩

def treesCheck (cs : List Cell) (c p : ℚ) (bad : List (ℚ × ℚ)) (trees : List Tree) : Bool :=
  let nb := bad.length
  (List.range nb).all fun i => (List.range nb).all fun j => (List.range nb).all fun k =>
    treeCheck cs c p (boxOf bad i j k) (trees.getD (i * nb * nb + j * nb + k) (.leaf [] [] [] [] [] []))

end Zeta23Ext.Bridge.ThreePoint

end CheckerDefs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness: the constants -/

theorem taylorCosQ_cast (q : ℚ) : taylorCos (q:ℝ) = ((taylorCosQ q : ℚ) : ℝ) := by
  simp only [taylorCos, taylorCosQ]; push_cast; ring

theorem taylorSinQ_cast (q : ℚ) : taylorSin (q:ℝ) = ((taylorSinQ q : ℚ) : ℝ) := by
  simp only [taylorSin, taylorSinQ]; push_cast; ring

theorem errQ_cast : taylorErr = ((errQ : ℚ) : ℝ) := by
  simp only [taylorErr, errQ]; push_cast; ring

theorem floorD_le (x : ℚ) : floorD x ≤ x := by
  unfold floorD
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

theorem le_ceilD (x : ℚ) : x ≤ ceilD x := by
  unfold ceilD
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

theorem floorD_le' (x : ℚ) : ((floorD x : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.mpr (floorD_le x)
theorem le_ceilD' (x : ℚ) : (x : ℝ) ≤ ((ceilD x : ℚ) : ℝ) := Rat.cast_le.mpr (le_ceilD x)

theorem piLoQ_le : ((piLoQ : ℚ) : ℝ) ≤ Real.pi := by
  have h := pi_lo
  simp only [piLoQ]; push_cast
  norm_num at h ⊢
  linarith

theorem piHiQ_ge : Real.pi ≤ ((piHiQ : ℚ) : ℝ) := by
  have h := pi_hi
  simp only [piHiQ]; push_cast
  norm_num at h ⊢
  linarith

theorem piLoQ_nonneg : (0:ℝ) ≤ ((piLoQ : ℚ) : ℝ) := by simp only [piLoQ]; push_cast; norm_num
theorem gamLoQ_le : ((gamLoQ : ℚ) : ℝ) ≤ gam := by
  have h := gam_bounds.1; simp only [gamLoQ]; push_cast; norm_num at h ⊢; linarith
theorem gamHiQ_ge : gam ≤ ((gamHiQ : ℚ) : ℝ) := by
  have h := gam_bounds.2; simp only [gamHiQ]; push_cast; norm_num at h ⊢; linarith
theorem gamLoQ_nonneg : (0:ℝ) ≤ ((gamLoQ : ℚ) : ℝ) := by simp only [gamLoQ]; push_cast; norm_num

theorem cos_sin_half (k : ℕ) :
    Real.cos (Real.pi * ((k:ℝ) / 2)) = ((csA k).1 : ℝ) ∧
      Real.sin (Real.pi * ((k:ℝ) / 2)) = ((csA k).2 : ℝ) := by
  induction k with
  | zero => simp [csA]
  | succ k ih =>
    have e : Real.pi * (((k + 1 : ℕ) : ℝ) / 2) = Real.pi * ((k:ℝ) / 2) + Real.pi / 2 := by
      push_cast; ring
    rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ih.1, ih.2]
    simp [csA]

theorem imulZ_sound (e : ℤ) (I : ℚ × ℚ) {f : ℝ} (h1 : (I.1 : ℝ) ≤ f) (h2 : f ≤ I.2) :
    ((imulZ e I).1 : ℝ) ≤ (e:ℝ) * f ∧ (e:ℝ) * f ≤ ((imulZ e I).2 : ℝ) := by
  unfold imulZ
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 he', mul_le_mul_of_nonneg_left h2 he'⟩
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 he', mul_le_mul_of_nonpos_left h1 he'⟩

theorem iadd_sound (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((iadd I J).1 : ℝ) ≤ f + g ∧ f + g ≤ ((iadd I J).2 : ℝ) := by
  unfold iadd; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isub_sound (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((isub I J).1 : ℝ) ≤ f - g ∧ f - g ≤ ((isub I J).2 : ℝ) := by
  unfold isub; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-! ### Soundness: one cell -/

set_option maxHeartbeats 4000000 in
theorem cell_sound (c : Cell) (h : c.ok = true) (x : ℝ) (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    (c.W : ℝ) ≤ wfun x := by
  simp only [Cell.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hLU⟩, hr0⟩, hTU⟩, hTL0q⟩, hBL0q⟩, hP2L0q⟩, hB⟩, hD⟩, hW⟩ := h
  have h0' : (0:ℝ) ≤ c.L := Rat.cast_nonneg.mpr h0
  have hr0' : (0:ℝ) ≤ c.rlo := Rat.cast_nonneg.mpr hr0
  have hTL0 : (0:ℝ) ≤ c.TL := Rat.cast_nonneg.mpr hTL0q
  have hBL0 : (0:ℝ) ≤ c.BL := Rat.cast_nonneg.mpr hBL0q
  have hP2L0 : (0:ℝ) ≤ c.P2L := Rat.cast_nonneg.mpr hP2L0q
  have hTU' : (c.TU : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hTU; simpa using this
  have hB' : (1:ℝ) < 2 * c.BL * c.BL := by
    have := (Rat.cast_lt (K := ℝ)).mpr hB; push_cast at this; exact this
  have hD' : (0:ℝ) < c.DHI := Rat.cast_pos.mpr hD
  have hW' : (c.W : ℝ) ≤ c.Wc := (Rat.cast_le (K := ℝ)).mpr hW
  -- the reduced offset
  set r : ℝ := if c.side then x - c.A else c.A - x with hr
  have hrlo : (c.rlo : ℝ) ≤ r := by
    simp only [Cell.rlo, hr]; split_ifs <;> push_cast <;> linarith
  have hrhi : r ≤ c.rhi := by
    simp only [Cell.rhi, hr]; split_ifs <;> push_cast <;> linarith
  have hr0r : 0 ≤ r := hr0'.trans hrlo
  have hTL : (c.TL : ℝ) ≤ Real.pi * r := by
    have h1 : (c.TL : ℝ) ≤ ((piLoQ * c.rlo : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (mul_ge_of piLoQ_le hrlo piLoQ_nonneg hr0' le_rfl)
  have hTUr : Real.pi * r ≤ c.TU := by
    have h1 : ((piHiQ * c.rhi : ℚ) : ℝ) ≤ (c.TU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (mul_le_of piHiQ_ge hrhi Real.pi_pos.le hr0r le_rfl).trans h1
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0r
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU'
  -- Taylor enclosures of cos (π r), sin (π r)
  have hc1 : ((c.CI).1 : ℝ) ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU'
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((c.CI).1 : ℝ) ≤ ((taylorCosQ c.TU - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CI).2 : ℝ) := by
    have h := cos_upper hTL0 hTL hθ1
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((taylorCosQ c.TL + errQ : ℚ) : ℝ) ≤ ((c.CI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hs1 : ((c.SI).1 : ℝ) ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((c.SI).1 : ℝ) ≤ ((taylorSinQ c.TL - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SI).2 : ℝ) := by
    have h := sin_upper hθ0 hTUr hTU'
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((taylorSinQ c.TU + errQ : ℚ) : ℝ) ≤ ((c.SI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  -- the shift to the anchor
  have hcs := cos_sin_half c.k
  have eA : (c.A : ℝ) = (c.k : ℝ) / 2 := by simp [Cell.A]
  have hCX : ((c.CX).1 : ℝ) ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, Bool.false_eq_true, if_false]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, if_true]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  have hSX : ((c.SX).1 : ℝ) ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, Bool.false_eq_true, if_false]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, if_true]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  -- π x and 2 γ π x
  have hb1 : (c.BL : ℝ) ≤ Real.pi * x := by
    have h1 : (c.BL : ℝ) ≤ ((piLoQ * c.L : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (mul_ge_of piLoQ_le hx1 piLoQ_nonneg h0' le_rfl)
  have hb2 : Real.pi * x ≤ c.BU := by
    have h1 : ((piHiQ * c.U : ℚ) : ℝ) ≤ (c.BU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (mul_le_of piHiQ_ge hx2 Real.pi_pos.le (h0'.trans hx1) le_rfl).trans h1
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := gamLoQ_nonneg.trans gamLoQ_le
  have hp1 : (c.P2L : ℝ) ≤ 2 * gam * (Real.pi * x) := by
    have h1 : (c.P2L : ℝ) ≤ ((2 * gamLoQ * c.BL : ℚ) : ℝ) := floorD_le' _
    push_cast at h1
    have := mul_le_mul gamLoQ_le hb1 hBL0 hgam0
    linarith
  have hp2 : 2 * gam * (Real.pi * x) ≤ c.P2U := by
    have h1 : ((2 * gamHiQ * c.BU : ℚ) : ℝ) ≤ (c.P2U : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul gamHiQ_ge hb2 hπx0 (gamLoQ_nonneg.trans (gamLoQ_le.trans gamHiQ_ge))
    linarith
  -- the product 2 γ π x · sin (π x)
  have hT1 : (c.TLO : ℝ) ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have h1 : (c.TLO : ℝ) ≤ ((min (c.P2L * c.SX.1) (c.P2U * c.SX.1) : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_min, Rat.cast_mul, Rat.cast_mul] at h1
    exact h1.trans (prod_lo hP2L0 hp1 hp2 hSX.1 (min_le_left _ _) (min_le_right _ _))
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ c.THI := by
    have h1 : ((max (c.P2L * c.SX.2) (c.P2U * c.SX.2) : ℚ) : ℝ) ≤ (c.THI : ℝ) := le_ceilD' _
    rw [Rat.cast_max, Rat.cast_mul, Rat.cast_mul] at h1
    exact (prod_hi hP2L0 hp1 hp2 hSX.2 (le_max_left _ _) (le_max_right _ _)).trans h1
  -- the numerator
  have eNLO : (c.NLO : ℝ) = max 0 (max (((c.CX).1 : ℝ) - c.THI) ((c.TLO : ℝ) - (c.CX).2)) := by
    rw [Cell.NLO, Rat.cast_max, Rat.cast_max]; push_cast; rfl
  have hN : (c.NLO : ℝ) ≤ |Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)| := by
    rw [eNLO]
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans (by linarith [hCX.1, hT2]) (le_abs_self _)
    · exact le_trans (by linarith [hCX.2, hT1]) (neg_le_abs _)
  have hNLO0 : (0:ℝ) ≤ c.NLO := by rw [eNLO]; exact le_max_left _ _
  -- the denominator
  have hD0 : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have := mul_le_mul hb1 hb1 hBL0 hπx0
    rw [pow_two]; linarith [this, hB']
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ c.DHI := by
    have h1 : ((2 * c.BU * c.BU - 1 : ℚ) : ℝ) ≤ (c.DHI : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    rw [pow_two]; linarith [this, h1]
  have hfin := wfun_ge x (c.NLO : ℝ) (c.DHI : ℝ) hNLO0 hD' hD0 hDD hN
  have eWc : (c.Wc : ℝ) = ((c.NLO : ℝ) / c.DHI)^2 := by rw [Cell.Wc]; push_cast; rfl
  rw [eWc] at hW'
  exact hW'.trans hfin

/-! ### Soundness: chains -/

theorem getD_mem_of_lt {cs : List Cell} {i : ℕ} (h : i < cs.length) : cs.getD i default ∈ cs := by
  rw [List.getD_eq_getElem cs default h]; exact List.getElem_mem h

theorem chain_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) :
    ∀ (idxs : List ℕ) (lo hi : ℚ), chainCheck cs lo hi idxs = true →
      ∀ e : ℝ, (lo : ℝ) ≤ e → e ≤ hi → (chainW cs idxs : ℝ) ≤ wfun e := by
  intro idxs
  induction idxs with
  | nil =>
    intro lo hi h e _ _
    simp only [chainW, Rat.cast_zero]; exact wfun_nonneg e
  | cons i rest ih =>
    intro lo hi h e he1 he2
    simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi_lt, hL⟩, hrest⟩ := h
    have hok : (cs.getD i default).ok = true :=
      List.all_eq_true.mp hcs _ (getD_mem_of_lt hi_lt)
    have hL' : ((cs.getD i default).L : ℝ) ≤ e := le_trans (by exact_mod_cast hL) he1
    simp only [chainW]
    split_ifs with hempty
    · -- the last cell: `chainCheck cs U hi [] = decide (hi ≤ U)`
      have hU : hi ≤ (cs.getD i default).U := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainCheck] using hrest
      exact cell_sound _ hok e hL' (he2.trans (by exact_mod_cast hU))
    · rw [Rat.cast_min]
      rcases le_total e ((cs.getD i default).U : ℝ) with hU | hU
      · exact (min_le_left _ _).trans (cell_sound _ hok e hL' hU)
      · exact (min_le_right _ _).trans (ih _ _ hrest e hU he2)

theorem term_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (idxs : List ℕ) (lo hi : ℚ)
    (h : termCheck cs lo hi idxs = true) (e : ℝ) (he1 : (lo : ℝ) ≤ e) (he2 : e ≤ hi) :
    (termW cs idxs : ℝ) ≤ wfun e := by
  simp only [termCheck, Bool.or_eq_true] at h
  simp only [termW]
  split_ifs with hempty
  · simp only [Rat.cast_zero]; exact wfun_nonneg e
  · rcases h with h | h
    · exact absurd h (by simpa using hempty)
    · exact chain_sound cs hcs idxs lo hi h e he1 he2

/-! ### Soundness: boxes and trees -/

/-- The four-point functional written out on the three gaps (rational instance). -/
def G4 (p : ℚ) (x y z : ℝ) : ℝ :=
  (1 / (p : ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z
    + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z)

theorem leaf_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) (b : Box)
    (t0 t1 t2 t3 t4 t5 : List ℕ) (h : leafCheck cs c p b t0 t1 t2 t3 t4 t5 = true)
    (x y z : ℝ) (hx1 : (b.xl : ℝ) ≤ x) (hx2 : x ≤ b.xu) (hy1 : (b.yl : ℝ) ≤ y) (hy2 : y ≤ b.yu)
    (hz1 : (b.zl : ℝ) ≤ z) (hz2 : z ≤ b.zu) : (c : ℝ) ≤ G4 p x y z := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hineq⟩ := h
  have w0 := term_sound cs hcs t0 _ _ h0 x hx1 hx2
  have w1 := term_sound cs hcs t1 _ _ h1 y hy1 hy2
  have w2 := term_sound cs hcs t2 _ _ h2 z hz1 hz2
  have w3 := term_sound cs hcs t3 _ _ h3 (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w4 := term_sound cs hcs t4 _ _ h4 (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := term_sound cs hcs t5 _ _ h5 (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr hineq
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G4
  linarith

theorem tree_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) :
    ∀ (t : Tree) (b : Box), treeCheck cs c p b t = true →
      ∀ x y z : ℝ, (b.xl : ℝ) ≤ x → x ≤ b.xu → (b.yl : ℝ) ≤ y → y ≤ b.yu →
        (b.zl : ℝ) ≤ z → z ≤ b.zu → (c : ℝ) ≤ G4 p x y z := by
  intro t
  induction t with
  | leaf t0 t1 t2 t3 t4 t5 =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    exact leaf_sound cs hcs c p hp b t0 t1 t2 t3 t4 t5 h x y z hx1 hx2 hy1 hy2 hz1 hz2
  | split ax q lo hi ihlo ihhi =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    simp only [treeCheck] at h
    split_ifs at h with h0 h1 h2
    · rw [Bool.and_eq_true] at h
      rcases le_total x (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hq hy1 hy2 hz1 hz2
      · exact ihhi _ h.2 x y z hq hx2 hy1 hy2 hz1 hz2
    · rw [Bool.and_eq_true] at h
      rcases le_total y (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hx2 hy1 hq hz1 hz2
      · exact ihhi _ h.2 x y z hx1 hx2 hq hy2 hz1 hz2
    · rw [Bool.and_eq_true] at h
      rcases le_total z (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hx2 hy1 hy2 hz1 hq
      · exact ihhi _ h.2 x y z hx1 hx2 hy1 hy2 hq hz2

/-! ### Soundness: the cover -/

theorem cover_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (lvl : ℚ) :
    ∀ (cover : List (ℚ × ℚ × List ℕ)) (pos S : ℚ), coverCheck cs lvl pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) ≤ v → v < S →
        (lvl : ℝ) ≤ wfun v ∨ ∃ s ∈ cover, s.2.2.isEmpty = true ∧ (s.1 : ℝ) ≤ v ∧ v ≤ s.2.1 := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) ≤ pos := by exact_mod_cast h
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, ch⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hch⟩, hrest⟩ := h
    rcases le_total v (b : ℝ) with hvb | hvb
    · rcases hch with hch | ⟨hchain, hlvl⟩
      · right
        refine ⟨(a, b, ch), List.mem_cons_self .., hch, ?_, hvb⟩
        rw [hpos]; exact hv1
      · left
        have hW := chain_sound cs hcs ch a b hchain v (by rw [hpos]; exact hv1) hvb
        exact le_trans (by exact_mod_cast hlvl) hW
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℚ × ℚ × List ℕ)} {s : ℚ × ℚ × List ℕ} (hs : s ∈ cover)
    (he : s.2.2.isEmpty = true) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

theorem trees_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p)
    (bad : List (ℚ × ℚ)) (trees : List Tree) (h : treesCheck cs c p bad trees = true)
    (i j k : ℕ) (hi : i < bad.length) (hj : j < bad.length) (hk : k < bad.length)
    (x y z : ℝ)
    (hx1 : ((bad.getD i (0, 0)).1 : ℝ) ≤ x) (hx2 : x ≤ (bad.getD i (0, 0)).2)
    (hy1 : ((bad.getD j (0, 0)).1 : ℝ) ≤ y) (hy2 : y ≤ (bad.getD j (0, 0)).2)
    (hz1 : ((bad.getD k (0, 0)).1 : ℝ) ≤ z) (hz2 : z ≤ (bad.getD k (0, 0)).2) :
    (c : ℝ) ≤ G4 p x y z := by
  simp only [treesCheck, List.all_eq_true, List.mem_range] at h
  have ht := h i hi j hj k hk
  exact tree_sound cs hcs c p hp _ (boxOf bad i j k) ht x y z hx1 hx2 hy1 hy2 hz1 hz2

/-! ### The four-point certificate from a checked rational table (not used by the weighted path) -/

theorem four_point_of_check (cs : List Cell) (cover : List (ℚ × ℚ × List ℕ)) (trees : List Tree)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 3/2 * c ≤ 19/100) (hcs : cs.all Cell.ok = true)
    (hcov : coverCheck cs (3/2 * c) (1/2) S cover = true)
    (htr : treesCheck cs c p (badOf cover) trees = true) :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (c : ℝ) ≤ G4 p x y z := by
  intro x y z hx hy hz
  have hw := fun t : ℝ => wfun_nonneg t
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G4; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  push_neg at hsum
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 2/3 * wfun v ∨ ∃ i, i < (badOf cover).length ∧
        (((badOf cover).getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ ((badOf cover).getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := wfun_window v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover_sound cs hcs _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := badOf_mem hs he
        obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hmem
        refine ⟨i, hi, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h1
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h2
  rcases key x hx (by linarith) with hxc | ⟨i, hi, hxi1, hxi2⟩
  · unfold G4; linarith [hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key y hy (by linarith) with hyc | ⟨j, hj, hyj1, hyj2⟩
  · unfold G4; linarith [hw x, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key z hz (by linarith) with hzc | ⟨k, hk, hzk1, hzk2⟩
  · unfold G4; linarith [hw x, hw y, hw (x + y), hw (y + z), hw (x + y + z)]
  exact trees_sound cs hcs c p hp _ trees htr i j k hi hj hk x y z hxi1 hxi2 hyj1 hyj2 hzk1 hzk2

private lemma sum3 (f : Fin (4 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := by
  show ∑ i : Fin 3, f i = f 0 + f 1 + f 2
  exact Fin.sum_univ_three f

/-- The four-point functional, written out (rational instance). -/
lemma F4_eq (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)
      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2) := by
  simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### natural-number checker for the 6-point weighted certificate `SixW6` ###### -/

section SixW6Defs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (key : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000
def SC4 : ℕ := 8192

/-- a cell's endpoints are packed into one key `LN * KB + UN` (every coordinate is below `KB`), so the table is
searched with one comparison per level -/
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

/-- the rational cell a natural-number cell denotes (the integer check `okZ` is what the table is verified by) -/
def CellN.toQ (c : CellN) : Cell := ⟨(c.LN : ℚ) / SC, (c.UN : ℚ) / SC, c.k, c.side, (c.WN : ℚ) / SW⟩

-- ZDEFS-BEGIN
/-- the scale of the integer bounds -/
def DZ : ℕ := 1000000000000000
def DZ2 : ℕ := 500000000000000
/-- π·10²⁰, below and above -/
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
/-- γ·10¹⁰, below and above -/
def GLN : ℕ := 8274992907
def GUN : ℕ := 8274993018
/-- the Taylor remainder, rounded up at scale `10¹⁵` -/
def ERRD : ℕ := 2262000

/-- floor and ceiling of `a / b` for naturals -/
def ndiv (a b : ℕ) : ℕ := a / b
def ndivc (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `cos (T / DZ)` by the twelve-term Taylor polynomial: positive and negative parts of the
numerator over `3628800 · DZ¹⁰`. -/
def cosP (T : ℕ) : ℕ := 3628800 * DZ^10 + 151200 * T^4 * DZ^6 + 90 * T^8 * DZ^2
def cosN (T : ℕ) : ℕ := 1814400 * T^2 * DZ^8 + 5040 * T^6 * DZ^4 + T^10
def sinP (T : ℕ) : ℕ := 39916800 * T * DZ^10 + 332640 * T^5 * DZ^6 + 110 * T^9 * DZ^2
def sinN (T : ℕ) : ℕ := 6652800 * T^3 * DZ^8 + 7920 * T^7 * DZ^4 + T^11
/-- lower / upper bounds of the polynomial values at scale `DZ` -/
def cosLo (T : ℕ) : ℕ := ndiv (cosP T - cosN T) (3628800 * DZ^9)
def cosHi (T : ℕ) : ℕ := ndivc (cosP T - cosN T) (3628800 * DZ^9)
def sinLo (T : ℕ) : ℕ := ndiv (sinP T - sinN T) (39916800 * DZ^10)
def sinHi (T : ℕ) : ℕ := ndivc (sinP T - sinN T) (39916800 * DZ^10)

/-- floor / ceiling division of an integer by `DZ` -/
def zfdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndiv z.toNat DZ : ℕ) : ℤ) else -((ndivc (-z).toNat DZ : ℕ) : ℤ)
def zcdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndivc z.toNat DZ : ℕ) : ℤ) else -((ndiv (-z).toNat DZ : ℕ) : ℤ)

def imulZZ (e : ℤ) (I : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ e then (e * I.1, e * I.2) else (e * I.2, e * I.1)
def iaddZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 + J.1, I.2 + J.2)
def isubZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 - J.2, I.2 - J.1)

namespace CellN
/-- lower/upper integer bounds (scale `DZ`) of the cell's endpoints -/
def LLO (c : CellN) : ℕ := ndiv (c.LN * DZ) SC
def UHI (c : CellN) : ℕ := ndivc (c.UN * DZ) SC
def AD (c : CellN) : ℕ := c.k * DZ2
def RLO (c : CellN) : ℕ := if c.side then c.LLO - c.AD else c.AD - c.UHI
def RHI (c : CellN) : ℕ := if c.side then c.UHI - c.AD else c.AD - c.LLO
def TLZ (c : CellN) : ℕ := ndiv (PLN * c.RLO) 100000000000000000000
def TUZ (c : CellN) : ℕ := ndivc (PUN * c.RHI) 100000000000000000000
def CLZ (c : CellN) : ℤ := (cosLo c.TUZ : ℤ) - ERRD
def CUZ (c : CellN) : ℤ := (cosHi c.TLZ : ℤ) + ERRD
def SLZ (c : CellN) : ℤ := (sinLo c.TLZ : ℤ) - ERRD
def SUZ (c : CellN) : ℤ := (sinHi c.TUZ : ℤ) + ERRD
def cAZ (c : CellN) : ℤ := (csA c.k).1
def sAZ (c : CellN) : ℤ := (csA c.k).2
def CXZ (c : CellN) : ℤ × ℤ :=
  if c.side then isubZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
  else iaddZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
def SXZ (c : CellN) : ℤ × ℤ :=
  if c.side then iaddZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
  else isubZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
def BLZ (c : CellN) : ℕ := ndiv (PLN * c.LLO) 100000000000000000000
def BUZ (c : CellN) : ℕ := ndivc (PUN * c.UHI) 100000000000000000000
def P2LZ (c : CellN) : ℕ := ndiv (2 * GLN * c.BLZ) 10000000000
def P2UZ (c : CellN) : ℕ := ndivc (2 * GUN * c.BUZ) 10000000000
def TLOZ (c : CellN) : ℤ := zfdiv (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
def THIZ (c : CellN) : ℤ := zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
def NLOZ (c : CellN) : ℤ := max 0 (max (c.CXZ.1 - c.THIZ) (c.TLOZ - c.CXZ.2))
def DHIZ (c : CellN) : ℤ := ((ndivc (2 * c.BUZ * c.BUZ) DZ : ℕ) : ℤ) - DZ
/-- the conditions of the integer check that do not involve the claimed bound -/
def okC (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (DZ * DZ < 2 * c.BLZ * c.BLZ) && decide (0 < c.DHIZ)
/-- the integer check of a claimed bound `WN` -/
def okZ (c : CellN) : Bool :=
  c.okC && decide ((c.WN : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
/-- the bound the pipeline certifies for the cell (0 outside its scope) -/
def WZ (c : CellN) : ℕ :=
  bif c.okC then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0
end CellN
-- ZDEFS-END

inductive CTN
  | nil
  | node (l : CTN) (c : CellN) (r : CTN)

namespace CTN
def toList : CTN → List CellN
  | nil => []
  | node l c r => l.toList ++ c :: r.toList
def allOk : CTN → Bool
  | nil => true
  | node l c r => l.allOk && c.okZ && r.allOk
def find : CTN → ℕ → Option CellN
  | nil, _ => none
  | node l c r, q =>
      bif Nat.blt q c.key then l.find q
      else bif Nat.blt c.key q then r.find q
      else some c
end CTN

/-- far pieces (start at or beyond `XFARN`) are rounded outward to the fine grid `2^FSH`; the chain check still
verifies coverage, so this only changes which cells are consulted -/
def XFARN : ℕ := 98304
def roundFar (a b : ℕ) : ℕ × ℕ :=
  bif Nat.ble XFARN a then ((a >>> 7) <<< 7, ((b + 127) >>> 7) <<< 7) else (a, b)

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(roundFar a hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 13) + 1) <<< 13
      bif Nat.blt q hi then (roundFar a q) :: piecesN fuel q hi else [(roundFar a hi)]

def lookupAllN (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      match t.find (a * KB + b), lookupAllN t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainOKN : ℕ → ℕ → List CellN → Bool
  | lo, hi, [] => Nat.ble hi lo
  | lo, hi, c :: rest => Nat.ble c.LN lo && chainOKN c.UN hi rest

def chainWN : List CellN → ℕ
  | [] => 0
  | c :: rest => bif rest.isEmpty then c.WN else bif Nat.ble c.WN (chainWN rest) then c.WN else chainWN rest

def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := piecesN 64 lo hi

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW6

def SA : ℕ := 100000000
def cN : ℕ := 336790

structure Box where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)
  deriving DecidableEq

def Box.widthArg (b : Box) : ℕ :=
  bif Nat.ble (b.u1 - b.l1) (b.u0 - b.l0) && Nat.ble (b.u2 - b.l2) (b.u0 - b.l0) && Nat.ble (b.u3 - b.l3) (b.u0 - b.l0) && Nat.ble (b.u4 - b.l4) (b.u0 - b.l0) then 0
  else bif Nat.ble (b.u2 - b.l2) (b.u1 - b.l1) && Nat.ble (b.u3 - b.l3) (b.u1 - b.l1) && Nat.ble (b.u4 - b.l4) (b.u1 - b.l1) then 1
  else bif Nat.ble (b.u3 - b.l3) (b.u2 - b.l2) && Nat.ble (b.u4 - b.l4) (b.u2 - b.l2) then 2
  else bif Nat.ble (b.u4 - b.l4) (b.u3 - b.l3) then 3
  else 4
def Box.mid (b : Box) : ℕ → ℕ
  | 0 => (b.l0 + b.u0) / 2
  | 1 => (b.l1 + b.u1) / 2
  | 2 => (b.l2 + b.u2) / 2
  | 3 => (b.l3 + b.u3) / 2
  | _ => (b.l4 + b.u4) / 2
def Box.setHi (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with u0 := q }
  | 1 => { b with u1 := q }
  | 2 => { b with u2 := q }
  | 3 => { b with u3 := q }
  | _ => { b with u4 := q }
def Box.setLo (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with l0 := q }
  | 1 => { b with l1 := q }
  | 2 => { b with l2 := q }
  | 3 => { b with l3 := q }
  | _ => { b with l4 := q }

def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((24896 * b.l0 + 42034 * b.l1 + 46137 * b.l2 + 42034 * b.l3 + 24896 * b.l4) * SW + (25326800 * termWN tb (b.l0) (b.u0) + 62369200 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 40126500 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 99999900 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) + 200000000 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l1) (b.u1) + 37630700 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 119746800 * termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) + 99999900 * termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) + 52857300 * termWN tb (b.l2) (b.u2) + 37630700 * termWN tb (b.l2 + b.l3) (b.u2 + b.u3) + 40126500 * termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l3) (b.u3) + 62369200 * termWN tb (b.l3 + b.l4) (b.u3 + b.u4) + 25326800 * termWN tb (b.l4) (b.u4)) * SC)

/-- the bisection axis stored in the three bits after a split marker -/
def axOf (bits pos : ℕ) : ℕ := (bits >>> (pos + 1)) &&& 7

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := axOf bits pos
        let q := b.mid ax
        match walk tb bits fuel (pos + 4) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheck tb b then some (pos + 1) else none

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear
segment's cell must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WN ≥ cN * SW`. -/
def coverCheck (tb : CTN) (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match tb.find (a * KB + b) with
            | some c => Nat.ble c.LN a && Nat.ble b c.UN && Nat.ble (cN * SW) (aAdjN * c.WN) | none => false))
        && coverCheck tb aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

def boxOf (bd0 bd1 bd2 bd3 bd4 : List (ℕ × ℕ)) (i0 i1 i2 i3 i4 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2, (bd3.getD i3 (0, 0)).1, (bd3.getD i3 (0, 0)).2, (bd4.getD i4 (0, 0)).1, (bd4.getD i4 (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint.SixW6

end SixW6Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the natural-number cell table (through the integer pipeline `cellN_soundZ`) -/

theorem SC_pos : (0:ℚ) < SC := by norm_num [SC]
theorem SW_pos : (0:ℚ) < SW := by norm_num [SW]

-- ZLEMMAS-BEGIN
/-! ### rounding lemmas -/

theorem DZ_pos : (0:ℝ) < DZ := by norm_num [DZ]
theorem DZ_ne : (DZ:ℝ) ≠ 0 := by norm_num [DZ]

theorem ndiv_le (a b : ℕ) (hb : 0 < b) : ((ndiv a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  unfold ndiv
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

theorem le_ndivc (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
  unfold ndivc
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h : a ≤ ((a + b - 1) / b) * b := by
    have := Nat.lt_div_mul_add (a := a + b - 1) hb
    omega
  exact_mod_cast h

theorem zfdiv_le (z : ℤ) : ((zfdiv z : ℤ) : ℝ) ≤ (z : ℝ) / DZ := by
  unfold zfdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact ndiv_le _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (le_ndivc _ _ (by norm_num [DZ]))

theorem le_zcdiv (z : ℤ) : (z : ℝ) / DZ ≤ ((zcdiv z : ℤ) : ℝ) := by
  unfold zcdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact le_ndivc _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (ndiv_le _ _ (by norm_num [DZ]))

/-! ### the Taylor polynomials at scale `DZ` -/

theorem taylorCos_eq (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) = ((cosP T - cosN T : ℕ) : ℝ) / (3628800 * (DZ : ℝ)^10) := by
  rw [Nat.cast_sub h]
  unfold taylorCos cosP cosN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem taylorSin_eq (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) = ((sinP T - sinN T : ℕ) : ℝ) / (39916800 * (DZ : ℝ)^11) := by
  rw [Nat.cast_sub h]
  unfold taylorSin sinP sinN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem cosLo_le (T : ℕ) (h : cosN T ≤ cosP T) :
    ((cosLo T : ℕ) : ℝ) / DZ ≤ taylorCos ((T : ℝ) / DZ) := by
  rw [taylorCos_eq T h]
  unfold cosLo
  have := ndiv_le (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ) ^ 10)
      = (((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ)) * (3628800 * (DZ:ℝ)^9) * DZ := by ring
    _ ≤ ((cosP T - cosN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_cosHi (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) ≤ ((cosHi T : ℕ) : ℝ) / DZ := by
  rw [taylorCos_eq T h]
  unfold cosHi
  have := le_ndivc (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((cosP T - cosN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ)^9) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem sinLo_le (T : ℕ) (h : sinN T ≤ sinP T) :
    ((sinLo T : ℕ) : ℝ) / DZ ≤ taylorSin ((T : ℝ) / DZ) := by
  rw [taylorSin_eq T h]
  unfold sinLo
  have := ndiv_le (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ) ^ 11)
      = (((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ)) * (39916800 * (DZ:ℝ)^10) * DZ := by ring
    _ ≤ ((sinP T - sinN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_sinHi (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) ≤ ((sinHi T : ℕ) : ℝ) / DZ := by
  rw [taylorSin_eq T h]
  unfold sinHi
  have := le_ndivc (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((sinP T - sinN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ)^10) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem ERRD_ge : taylorErr ≤ (ERRD : ℝ) / DZ := by norm_num [taylorErr, ERRD, DZ]

/-! ### interval operations at scale `DZ` -/

theorem imulZZ_sound (e : ℤ) (I : ℤ × ℤ) {f : ℝ} (h1 : (I.1 : ℝ) / DZ ≤ f) (h2 : f ≤ (I.2 : ℝ) / DZ) :
    ((imulZZ e I).1 : ℝ) / DZ ≤ (e : ℝ) * f ∧ (e : ℝ) * f ≤ ((imulZZ e I).2 : ℝ) / DZ := by
  unfold imulZZ
  have hD := DZ_pos
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 he'
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h2 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h1 he'

theorem iaddZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((iaddZ I J).1 : ℝ) / DZ ≤ f + g ∧ f + g ≤ ((iaddZ I J).2 : ℝ) / DZ := by
  unfold iaddZ; simp only; push_cast; rw [add_div, add_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isubZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((isubZ I J).1 : ℝ) / DZ ≤ f - g ∧ f - g ≤ ((isubZ I J).2 : ℝ) / DZ := by
  unfold isubZ; simp only; push_cast; rw [sub_div, sub_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-! ### the integer cell check is sound -/

theorem PLN_le : ((PLN : ℕ) : ℝ) / 100000000000000000000 ≤ Real.pi := by
  have h := pi_lo; norm_num [PLN] at h ⊢; linarith
theorem PUN_ge : Real.pi ≤ ((PUN : ℕ) : ℝ) / 100000000000000000000 := by
  have h := pi_hi; norm_num [PUN] at h ⊢; linarith
theorem GLN_le : ((GLN : ℕ) : ℝ) / 10000000000 ≤ gam := by
  have h := gam_bounds.1; norm_num [GLN] at h ⊢; linarith
theorem GUN_ge : gam ≤ ((GUN : ℕ) : ℝ) / 10000000000 := by
  have h := gam_bounds.2; norm_num [GUN] at h ⊢; linarith

/-- `ndiv a b / DZ ≤ (a / b) / DZ` packaged with a product bound: if `a = p * q` with
`p / P ≤ A` and `q / DZ ≤ B` (all nonnegative) then `ndiv (p*q) P / DZ ≤ A * B`. -/
theorem ndiv_prod_le (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : ((p : ℕ) : ℝ) / P ≤ A)
    (hB : ((q : ℕ) : ℝ) / DZ ≤ B) (hA0 : 0 ≤ ((p : ℕ) : ℝ) / P) (hB0 : 0 ≤ ((q : ℕ) : ℝ) / DZ) :
    ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ A * B := by
  have h := ndiv_le (p * q) P hP
  have hD := DZ_pos
  calc ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ (((p * q : ℕ) : ℝ) / P) / DZ :=
        div_le_div_of_nonneg_right h hD.le
    _ = (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := by push_cast; field_simp
    _ ≤ A * B := mul_le_mul hA hB hB0 (hA0.trans hA)

theorem le_ndivc_prod (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : A ≤ ((p : ℕ) : ℝ) / P)
    (hB : B ≤ ((q : ℕ) : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    A * B ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := by
  have h := le_ndivc (p * q) P hP
  have hD := DZ_pos
  calc A * B ≤ (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = (((p * q : ℕ) : ℝ) / P) / DZ := by push_cast; field_simp
    _ ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := div_le_div_of_nonneg_right h hD.le

set_option maxHeartbeats 4000000 in
theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.okC = true)
    (hW : (w : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 100000000000000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have nG0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 10000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  -- endpoints at scale DZ
  have hLLO : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := ndiv_le (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.LLO
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.UHI : ℕ) : ℝ) / DZ := by
    have := le_ndivc (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.UHI
    push_cast at this ⊢
    rw [le_div_iff₀ hD0]
    calc (c.UN : ℝ) / SC * DZ = (c.UN : ℝ) * DZ / SC := by ring
      _ ≤ _ := this
  have hAD : ((c.AD : ℕ) : ℝ) / DZ = (c.k : ℝ) / 2 := by
    unfold CellN.AD; simp only [DZ, DZ2]; push_cast; ring
  have hL0 : (0:ℝ) ≤ (c.LN : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := hL0.trans hx1
  have hLNUN : (c.LN : ℝ) / SC ≤ (c.UN : ℝ) / SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hLU) hSC.le
  have hkF : c.side = false → (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := fun hs => by
    have : (2 * c.UN : ℝ) ≤ (c.k * SC : ℝ) := by exact_mod_cast hsideF hs
    rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
  have hkT : c.side = true → (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := fun hs => by
    have : (c.k * SC : ℝ) ≤ (2 * c.LN : ℝ) := by exact_mod_cast hsideT hs
    rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
  -- the reduced offset r and the integer bounds RLO ≤ r ≤ RHI
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.RLO : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.RLO
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.UHI c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.LLO with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.RHI : ℕ) : ℝ) / DZ := by
    unfold CellN.RHI
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.LLO ≤ c.AD := by
        have h1 : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.UHI := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.UHI : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  -- θ = π r at scale DZ
  have hTL : ((c.TLZ : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.TLZ
    exact ndiv_prod_le PLN c.RLO _ (by norm_num) PLN_le hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.TUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.TUZ
    exact le_ndivc_prod PUN c.RHI _ (by norm_num) PUN_ge hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.TUZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.TLZ : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  -- Taylor enclosures at the integer endpoints
  have hc1 : ((c.CLZ : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU1
    have h1 := cosLo_le c.TUZ hcP1
    have h2 := ERRD_ge
    unfold CellN.CLZ; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CUZ : ℤ) : ℝ) / DZ := by
    have h := cos_upper hTL0 hTL hθ1
    have h1 := le_cosHi c.TLZ hcP2
    have h2 := ERRD_ge
    unfold CellN.CUZ; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.SLZ : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    have h1 := sinLo_le c.TLZ hsP1
    have h2 := ERRD_ge
    unfold CellN.SLZ; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SUZ : ℤ) : ℝ) / DZ := by
    have h := sin_upper hθ0 hTUr hTU1
    have h1 := le_sinHi c.TUZ hsP2
    have h2 := ERRD_ge
    unfold CellN.SUZ; push_cast; rw [add_div]
    linarith
  -- the shift to the anchor
  have hcs := cos_sin_half c.k
  have hCX : ((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, Bool.false_eq_true, if_false]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, if_true]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hSX : ((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, Bool.false_eq_true, if_false]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, if_true]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  -- π x and 2 γ π x
  have hb1 : ((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.BLZ
    exact ndiv_prod_le PLN c.LLO _ (by norm_num) PLN_le (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.BUZ
    exact le_ndivc_prod PUN c.UHI _ (by norm_num) PUN_ge (hx2.trans hUHI) Real.pi_pos.le hx0
  have hBL0 : (0:ℝ) ≤ ((c.BLZ : ℕ) : ℝ) / DZ := nd0 _
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := (nG0 GLN).trans GLN_le
  have hp1 : ((c.P2LZ : ℕ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) := by
    unfold CellN.P2LZ
    exact ndiv_prod_le (2 * GLN) c.BLZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GLN_le; linarith) hb1 (nG0 _) hBL0
  have hp2 : 2 * gam * (Real.pi * x) ≤ ((c.P2UZ : ℕ) : ℝ) / DZ := by
    unfold CellN.P2UZ
    exact le_ndivc_prod (2 * GUN) c.BUZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GUN_ge; linarith) hb2 (by linarith) hπx0
  have hP2L0 : (0:ℝ) ≤ ((c.P2LZ : ℕ) : ℝ) / DZ := nd0 _
  -- the product 2 γ π x · sin (π x)
  have hT1 : ((c.TLOZ : ℤ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have hz := zfdiv_le (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
    have hmA : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_left _ _
    have hmB : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.TLOZ
    refine (div_le_div_of_nonneg_right hz hD0.le).trans (prod_lo hP2L0 hp1 hp2 hSX.1 ?_ ?_)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ ((c.THIZ : ℤ) : ℝ) / DZ := by
    have hz := le_zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
    have hmA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hmB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.THIZ
    refine (prod_hi hP2L0 hp1 hp2 hSX.2 ?_ ?_).trans (div_le_div_of_nonneg_right hz hD0.le)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  -- the numerator and the denominator
  set N : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) with hNdef
  have hN : ((c.NLOZ : ℤ) : ℝ) / DZ ≤ |N| := by
    have hCX1 := (div_le_iff₀ hD0).mp hCX.1
    have hCX2 := (le_div_iff₀ hD0).mp hCX.2
    have hT1' := (div_le_iff₀ hD0).mp hT1
    have hT2' := (le_div_iff₀ hD0).mp hT2
    have ha1 := mul_le_mul_of_nonneg_right (le_abs_self N) hD0.le
    have ha2 := mul_le_mul_of_nonneg_right (neg_le_abs N) hD0.le
    rw [div_le_iff₀ hD0]
    unfold CellN.NLOZ
    rw [Int.cast_max, Int.cast_max, Int.cast_zero]
    refine max_le (mul_nonneg (abs_nonneg _) hD0.le) (max_le ?_ ?_)
    · push_cast; rw [hNdef] at ha1; linarith
    · push_cast; rw [hNdef] at ha2; linarith
  have hNLO0 : (0:ℝ) ≤ ((c.NLOZ : ℤ) : ℝ) / DZ := by
    unfold CellN.NLOZ; rw [Int.cast_max, Int.cast_zero]
    exact div_nonneg (le_max_left _ _) hD0.le
  have hD' : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
    exact div_pos this hD0
  have hD0' : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have h1 : ((DZ * DZ : ℕ) : ℝ) < ((2 * c.BLZ * c.BLZ : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    have h2 : ((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ) ≤ (Real.pi * x) * (Real.pi * x) :=
      mul_le_mul hb1 hb1 hBL0 hπx0
    have h3 : (1:ℝ) < 2 * (((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ)) := by
      rw [div_mul_div_comm, ← mul_div_assoc, lt_div_iff₀ (mul_pos hD0 hD0)]
      linarith
    rw [pow_two]; linarith
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have h1 := le_ndivc (2 * c.BUZ * c.BUZ) DZ (by norm_num [DZ])
    push_cast at h1
    have h2 : (Real.pi * x) * (Real.pi * x) ≤ ((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ) :=
      mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    have h3 : 2 * (((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ))
        = 2 * (c.BUZ : ℝ) * (c.BUZ : ℝ) / DZ / DZ := by ring
    have h4 := div_le_div_of_nonneg_right h1 hD0.le
    unfold CellN.DHIZ
    push_cast
    rw [sub_div, div_self DZ_ne, pow_two]
    linarith
  have hfin := wfun_ge x (((c.NLOZ : ℤ) : ℝ) / DZ) (((c.DHIZ : ℤ) : ℝ) / DZ) hNLO0 hD' hD0' hDD hN
  have hWr : ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)
      ≤ ((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ) * ((SW : ℕ) : ℝ) := by exact_mod_cast hW
  have hDHpos : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
  have e : (((c.NLOZ : ℤ) : ℝ) / DZ / (((c.DHIZ : ℤ) : ℝ) / DZ))^2
      = (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_div_div_cancel_right₀ DZ_ne]; ring
  have hle : ((w : ℕ) : ℝ) / SW
      ≤ (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_le_div_iff₀ hSW (mul_pos hDHpos hDHpos)]
    calc ((w : ℕ) : ℝ) * (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ))
        = ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) := by ring
      _ ≤ _ := hWr
  rw [← e] at hle
  exact hle.trans hfin

/-- a claimed bound that passes the integer check is sound -/
theorem cellN_soundZ (c : CellN) (h : c.okZ = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okZ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact cellN_soundZ' c c.WN h.1 h.2 x hx1 hx2

/-- the computed bound is sound: no claimed value, the pipeline's own quotient -/
theorem cellN_soundWZ (c : CellN) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WZ : ℝ) / SW ≤ wfun x := by
  have key : ∀ b : Bool, c.okC = b →
      ((bif b then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0 : ℕ) : ℝ) / SW ≤ wfun x := by
    intro b hb
    cases b
    · simp only [cond_false, Nat.cast_zero, zero_div]; exact wfun_nonneg x
    · simp only [cond_true]
      have hD : 0 < c.DHIZ := by
        simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.2
      have hN : 0 ≤ c.NLOZ := by unfold CellN.NLOZ; exact le_max_left _ _
      have hSWz : (0:ℤ) ≤ (SW : ℤ) := by positivity
      set q : ℤ := (c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ) with hq
      have hq0 : 0 ≤ q := by
        rw [hq]; exact Int.ediv_nonneg (mul_nonneg (mul_nonneg hN hN) hSWz) (mul_pos hD hD).le
      have hqe : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      have h1 : q * (c.DHIZ * c.DHIZ) ≤ c.NLOZ * c.NLOZ * SW := by
        rw [hq]; exact Int.ediv_mul_le _ (mul_pos hD hD).ne'
      rw [← hqe] at h1
      exact cellN_soundZ' c q.toNat hb (by linarith) x hx1 hx2
  exact key c.okC rfl
-- ZLEMMAS-END

theorem CTN.find_sound : ∀ (t : CTN) (q : ℕ) (c : CellN), t.find q = some c → c ∈ t.toList := by
  intro t
  induction t with
  | nil => intro q c h; simp [CTN.find] at h
  | node l c0 r ihl ihr =>
    intro q c h
    simp only [CTN.find, Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with h1 h2
    · simp [CTN.toList, ihl q c h]
    · simp [CTN.toList, ihr q c h]
    · simp only [Option.some.injEq] at h
      subst h
      simp [CTN.toList]

theorem CTN.allOk_sound : ∀ (t : CTN), t.allOk = true → ∀ c ∈ t.toList, c.okZ = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CTN.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CTN.allOk, Bool.and_eq_true] at h
    simp only [CTN.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc

theorem lookupAllN_sound (t : CTN) : ∀ (ps : List (ℕ × ℕ)) (cs : List CellN),
    lookupAllN t ps = some cs → ∀ c ∈ cs, c ∈ t.toList := by
  intro ps
  induction ps with
  | nil => intro cs h; simp [lookupAllN] at h; subst h; simp
  | cons ab rest ih =>
    intro cs h
    obtain ⟨a, b⟩ := ab
    cases hf : t.find (a * KB + b) with
    | none => simp [lookupAllN, hf] at h
    | some c =>
      cases hr : lookupAllN t rest with
      | none => simp [lookupAllN, hf, hr] at h
      | some cs' =>
        simp only [lookupAllN, hf, hr, Option.some.injEq] at h
        subst h
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact CTN.find_sound t _ d hf
        · exact ih cs' hr d hd

/-- a natural-number cell's bound holds on its interval, read in real coordinates -/
theorem cellN_sound (c : CellN) (hok : c.okZ = true) (x : ℝ)
    (h1 : (c.LN : ℝ) / SC ≤ x) (h2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x :=
  cellN_soundZ c hok x h1 h2

theorem chainOKN_sound (t : CTN) (hok : t.allOk = true) :
    ∀ (cs : List CellN), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℕ), chainOKN lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) / SC ≤ e → e ≤ (hi : ℝ) / SC → (chainWN cs : ℝ) / SW ≤ wfun e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWN, Nat.cast_zero, zero_div]; exact wfun_nonneg e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [chainOKN, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok := CTN.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.LN : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN, Bool.cond_eq_ite, Nat.ble_eq]
    split_ifs with hempty hle
    · have hU : hi ≤ c.UN := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKN, Nat.ble_eq] using hrest
      exact cellN_sound c hcok e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact cellN_sound c hcok e hL' hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num [SW]))
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (not_le.mp hle).le) (by norm_num [SW]))
          (cellN_sound c hcok e hL' hU)
      · exact ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2

theorem termWN_sound_gen (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (ps : List (ℕ × ℕ)) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) :
    (termWNcore t lo hi ps : ℝ) / SW ≤ wfun e := by
  unfold termWNcore
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact chainOKN_sound t hok cs (lookupAllN_sound t _ cs hcs) lo hi hch e he1 he2
    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e

theorem termWN_sound (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) : (termWN t lo hi : ℝ) / SW ≤ wfun e :=
  termWN_sound_gen t hok lo hi (piecesN' lo hi) e he1 he2

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW6

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)

def Box.mem (b : Box) (g0 g1 g2 g3 g4 : ℝ) : Prop :=
  (b.l0 : ℝ) / SC ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / SC ∧ (b.l1 : ℝ) / SC ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / SC ∧ (b.l2 : ℝ) / SC ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / SC ∧ (b.l3 : ℝ) / SC ≤ g3 ∧ g3 ≤ (b.u3 : ℝ) / SC ∧ (b.l4 : ℝ) / SC ≤ g4 ∧ g4 ≤ (b.u4 : ℝ) / SC

set_option maxHeartbeats 4000000 in
theorem leaf_sound (tb : CTN) (hok : tb.allOk = true) (b : Box) (h : leafCheck tb b = true)
    (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4) : (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  have w0 := termWN_sound tb hok (b.l0) (b.u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := termWN_sound tb hok (b.l0 + b.l1) (b.u0 + b.u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := termWN_sound tb hok (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := termWN_sound tb hok (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := termWN_sound tb hok (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := termWN_sound tb hok (b.l1) (b.u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w6 := termWN_sound tb hok (b.l1 + b.l2) (b.u1 + b.u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w7 := termWN_sound tb hok (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w8 := termWN_sound tb hok (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w9 := termWN_sound tb hok (b.l2) (b.u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w10 := termWN_sound tb hok (b.l2 + b.l3) (b.u2 + b.u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w11 := termWN_sound tb hok (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w12 := termWN_sound tb hok (b.l3) (b.u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w13 := termWN_sound tb hok (b.l3 + b.l4) (b.u3 + b.u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w14 := termWN_sound tb hok (b.l4) (b.u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  simp only [leafCheck, Nat.ble_eq] at h
  have hq := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hpos : (0:ℝ) < SC * SW := by positivity
  set L : ℝ := 24896 * ((b.l0 : ℝ) / SC) + 42034 * ((b.l1 : ℝ) / SC) + 46137 * ((b.l2 : ℝ) / SC) + 42034 * ((b.l3 : ℝ) / SC) + 24896 * ((b.l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25326800 * ((termWN tb (b.l0) (b.u0) : ℝ) / SW) + 62369200 * ((termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) / SW) + 40126500 * ((termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) / SW) + 99999900 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) / SW) + 200000000 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48244400 * ((termWN tb (b.l1) (b.u1) : ℝ) / SW) + 37630700 * ((termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) / SW) + 119746800 * ((termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) / SW) + 99999900 * ((termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 52857300 * ((termWN tb (b.l2) (b.u2) : ℝ) / SW) + 37630700 * ((termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) / SW) + 40126500 * ((termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48244400 * ((termWN tb (b.l3) (b.u3) : ℝ) / SW) + 62369200 * ((termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) / SW) + 25326800 * ((termWN tb (b.l4) (b.u4) : ℝ) / SW) with hWt
  have e : (L + Wt) * (SC * SW) = (24896 * (b.l0 : ℝ) + 42034 * (b.l1 : ℝ) + 46137 * (b.l2 : ℝ) + 42034 * (b.l3 : ℝ) + 24896 * (b.l4 : ℝ)) * SW + (25326800 * (termWN tb (b.l0) (b.u0) : ℝ) + 62369200 * (termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) + 40126500 * (termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) + 99999900 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) + 200000000 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 48244400 * (termWN tb (b.l1) (b.u1) : ℝ) + 37630700 * (termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) + 119746800 * (termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) + 99999900 * (termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 52857300 * (termWN tb (b.l2) (b.u2) : ℝ) + 37630700 * (termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) + 40126500 * (termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) + 48244400 * (termWN tb (b.l3) (b.u3) : ℝ) + 62369200 * (termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) + 25326800 * (termWN tb (b.l4) (b.u4) : ℝ)) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
      + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * wfun (g0) + 62369200 * wfun (g0 + g1) + 40126500 * wfun (g0 + g1 + g2) + 99999900 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48244400 * wfun (g1) + 37630700 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 99999900 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 37630700 * wfun (g2 + g3) + 40126500 * wfun (g2 + g3 + g4) + 48244400 * wfun (g3) + 62369200 * wfun (g3 + g4) + 25326800 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25326800)]

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hle : match ax with | 0 => g0 ≤ (q : ℝ) / SC | 1 => g1 ≤ (q : ℝ) / SC | 2 => g2 ≤ (q : ℝ) / SC | 3 => g3 ≤ (q : ℝ) / SC | _ => g4 ≤ (q : ℝ) / SC) :
    (b.setHi ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨h01, hle, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, h11, hle, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, h21, hle, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, h31, hle, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hge : match ax with | 0 => (q : ℝ) / SC ≤ g0 | 1 => (q : ℝ) / SC ≤ g1 | 2 => (q : ℝ) / SC ≤ g2 | 3 => (q : ℝ) / SC ≤ g3 | _ => (q : ℝ) / SC ≤ g4) :
    (b.setLo ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨hge, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, hge, h12, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, hge, h22, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, hge, h32, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, hge, h42⟩

theorem walk_split (tb : CTN) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk tb bits fuel (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) = some pos') :
    walk tb bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, cond_true, h1]
  exact h2

theorem walk_sound (tb : CTN) (hok : tb.allOk = true) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk tb bits fuel pos b = some pos' →
      ∀ g0 g1 g2 g3 g4 : ℝ, b.mem g0 g1 g2 g3 g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk] at h
  | succ fuel ih =>
    intro pos b pos' h g0 g1 g2 g3 g4 hm
    simp only [walk, Bool.cond_eq_ite] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) pos1 h1 g0 g1 g2 g3 g4
        have hhi := ih pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) pos' h g0 g1 g2 g3 g4
        set ax := axOf bits pos with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total g0 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 0 q g0 g1 g2 g3 g4 hm hs)
        | 1, hlo, hhi =>
          rcases le_total g1 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 1 q g0 g1 g2 g3 g4 hm hs)
        | 2, hlo, hhi =>
          rcases le_total g2 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 2 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 2 q g0 g1 g2 g3 g4 hm hs)
        | 3, hlo, hhi =>
          rcases le_total g3 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 3 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 3 q g0 g1 g2 g3 g4 hm hs)
        | n + 4, hlo, hhi =>
          rcases le_total g4 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 4) q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b (n + 4) q g0 g1 g2 g3 g4 hm hs)
    · simp only [Bool.or_eq_true, Nat.blt_eq] at hleaf
      rcases hleaf with hskip | hleaf
      · right
        obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
        have hsk : ((b.u4 : ℕ) : ℝ) / SC < ((b.l0 : ℕ) : ℝ) / SC :=
          div_lt_div_of_pos_right (by exact_mod_cast hskip) (by norm_num [SC])
        linarith
      · left; exact leaf_sound tb hok b hleaf g0 g1 g2 g3 g4 hm


theorem cover_sound (tb : CTN) (hok : tb.allOk = true) (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck tb aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        split at hcl
        · rename_i c hfind
          simp only [Bool.and_eq_true, Nat.ble_eq] at hcl
          obtain ⟨⟨hL, hU⟩, hq'⟩ := hcl
          have hmem := CTN.find_sound tb _ c hfind
          have hcok := CTN.allOk_sound tb hok c hmem
          have hW := cellN_sound c hcok v
            (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (hpos ▸ hL)) (by norm_num [SC])) hv1)
            (hvb.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
          have hq := (Nat.cast_le (α := ℝ)).mpr hq'
          push_cast at hq
          have hSA : (0:ℝ) < SA := by norm_num [SA]
          have hSW : (0:ℝ) < SW := by norm_num [SW]
          rw [div_le_iff₀ hSA]
          have hm2 : (aAdjN : ℝ) * ((c.WN : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
            mul_le_mul_of_nonneg_left hW (by positivity)
          have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
          rw [e]
          calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
            _ ≤ (aAdjN : ℝ) * c.WN / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
            _ = (aAdjN : ℝ) * ((c.WN : ℝ) / SW) := by ring
            _ ≤ _ := hm2
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (tb : CTN) (hok : tb.allOk = true) (bits fuel : ℕ)
    (cover0 cover1 cover2 cover3 cover4 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 : ℕ)
    (hS0 : cN * SC ≤ 24896 * S0) (hS1 : cN * SC ≤ 42034 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42034 * S3) (hS4 : cN * SC ≤ 24896 * S4)
    (hcov0 : coverCheck tb 25326800 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck tb 48244400 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck tb 52857300 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck tb 48244400 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck tb 25326800 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25326800)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      ∃ pos pos', walk tb bits fuel pos (boxOf (badOf cover0) (badOf cover1) (badOf cover2) (badOf cover3) (badOf cover4) i0 i1 i2 i3 i4) = some pos') :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (46137 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (52857300 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (24896 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (42034 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (46137 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (42034 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (24896 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25326800 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (62369200 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (48244400 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (37630700 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (52857300 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (37630700 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (48244400 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (62369200 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (25326800 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g0 * SA = 24896 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 24896 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g0 * SA = 25326800 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW0, hLin0]
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · left; rw [hG]; linarith [hclear0, haW0, hLin0]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g1 * SA = 42034 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 42034 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g1 * SA = 48244400 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW5, hLin0]
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW5, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (46137 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (46137 / (SA:ℝ)) * g2 * SA = 46137 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 46137 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 46137 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 46137 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (52857300 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (52857300 / (SA:ℝ)) * wfun g2 * SA = 52857300 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 52857300)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW9, hLin0]
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW9, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g3 * SA = 42034 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 42034 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g3 * SA = 48244400 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW12, hLin0]
  rcases cover_sound tb hok _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW12, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g4 * SA = 24896 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 24896 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g4 * SA = 25326800 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW14, hLin0]
  rcases cover_sound tb hok _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  exact walk_sound tb hok bits fuel pos _ pos' hwalk g0 g1 g2 g3 g4 ⟨hb01', hb02', hb11', hb12', hb21', hb22', hb31', hb32', hb41', hb42'⟩

end Zeta23Ext.Bridge.ThreePoint.SixW6

end

/-! ###### certificate data `SixW6`: 8220 cells, 32612 leaves (axis-coded walk) (half-space) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW6Data

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW6

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

noncomputable def tab0 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨17179893760,331038177865⟩ E) ⟨25769832448,242869129569⟩ E) ⟨30064800768,217716609437⟩ (N E ⟨30064801792,122761883704⟩ E)) ⟨31138543104,177515141421⟩ (N (N E ⟨31675414528,135790452388⟩ E) ⟨32212285952,100331164832⟩ (N E ⟨32212286048,93917126691⟩ E))) ⟨32212286464,69269436296⟩ (N (N (N E ⟨32212286656,59504641098⟩ E) ⟨32212287488,27393363819⟩ (N E ⟨32749157376,70831514211⟩ E)) ⟨32849820864,61025502253⟩ (N (N E ⟨33286029120,34548539408⟩ E) ⟨33286029312,28203622388⟩ (N E ⟨33487355376,47896897026⟩ E)))) ⟨33487355680,35832620095⟩ (N (N (N (N E ⟨33487355904,28296403112⟩ E) ⟨33806122784,36023083580⟩ (N E ⟨34124890112,28464081354⟩ E)) ⟨34158444544,28467564926⟩ (N (N E ⟨34359771216,25976114687⟩ E) ⟨34359771360,21788669253⟩ (N E ⟨34359771520,17601327427⟩ E))) ⟨34359771776,11891897536⟩ (N (N (N E ⟨34443657600,17601327427⟩ E) ⟨34594652592,16438965712⟩ (N E ⟨34594652800,11891897536⟩ E)) ⟨34762424856,14066726447⟩ (N (N E ⟨34762425008,10953811162⟩ E) ⟨34762425312,5952302335⟩ (N E ⟨34762425920,560103521⟩ E))))) ⟨34812756608,11891897536⟩ (N (N (N (N (N E ⟨34921808560,10953811162⟩ E) ⟨35030860520,9911220876⟩ (N E ⟨35030860624,8121431559⟩ E)) ⟨35030860832,5101426618⟩ (N (N E ⟨35030861248,1207853390⟩ E) ⟨35081192264,8252405001⟩ (N E ⟨35081192416,5952302335⟩ E))) ⟨35139912528,8121431559⟩ (N (N (N E ⟨35240575968,5952302335⟩ E) ⟨35248964536,6519258779⟩ (N E ⟨35248964640,5101426618⟩ E)) ⟨35358016544,5101426618⟩ (N (N E ⟨35399959672,4043273979⟩ E) ⟨35399959824,2515072630⟩ (N E ⟨35399960128,560103521⟩ E)))) ⟨35467068552,3864654916⟩ (N (N (N (N E ⟨35467068656,2805660000⟩ E) ⟨35467068864,1207853390⟩ (N E ⟨35559343376,2515072630⟩ E)) ⟨35576120508,3313140707⟩ (N (N E ⟨35576120560,2805660000⟩ E) ⟨35630646512,2805660000⟩ (N E ⟨35685172516,2341801940⟩ E))) ⟨35685172568,1921155551⟩ (N (N (N E ⟨35685172672,1207853390⟩ E) ⟨35718727080,1357438270⟩ (N E ⟨35718727232,560103521⟩ E)) ⟨35739698520,1921155551⟩ (N (N E ⟨35794224524,1543309743⟩ E) ⟨35794224576,1207853390⟩ (N E ⟨35848750528,1207853390⟩ E)))))) ⟨35878110784,560103521⟩ (N (N (N (N (N (N E ⟨35903276532,914375298⟩ E) ⟨35903276584,662464275⟩ (N E ⟨35903276688,281698711⟩ E)) ⟨35957802536,662464275⟩ (N (N E ⟨36012328592,281698711⟩ E) ⟨36339484720,861720⟩ (N E ⟨36339484928,840527⟩ E))) ⟨36356262048,5069528⟩ (N (N (N E ⟨36557588736,330776253⟩ E) ⟨36675029456,741120989⟩ (N E ⟨36675029760,715005325⟩ E)) ⟨36775692960,1209025102⟩ (N (N E ⟨36775693376,1151561664⟩ E) ⟨36775694208,1046595949⟩ (N E ⟨36775695872,870430129⟩ E)))) ⟨36993796864,2670280633⟩ (N (N (N (N E ⟨37211900992,4577595806⟩ E) ⟨37312564576,5517323674⟩ (N E ⟨37312565184,5147011177⟩ E)) ⟨37312566400,4495681621⟩ (N (N E ⟨37312568832,3476319374⟩ E) ⟨37648109440,9452356006⟩ (N E ⟨37950099392,14339196425⟩ E))) ⟨38520526336,22408627075⟩ (N (N (N E ⟨38587634816,24873411793⟩ E) ⟨39862705664,48862449799⟩ (N E ⟨40265357312,71849923330⟩ E)) ⟨40802230272,75832144115⟩ (N (N E ⟨42412843008,143033504697⟩ E) ⟨42949715968,138814108272⟩ (N E ⟨42949722112,80226784524⟩ E))))) ⟨45097201664,198611196246⟩ (N (N (N (N (N E ⟨47244689408,205420959916⟩ E) ⟨51539660800,198637449669⟩ (N E ⟨51539664896,86044756753⟩ E)) ⟨55834630144,180021136485⟩ (N (N E ⟨57982114816,163928295311⟩ E) ⟨59055857664,136793280978⟩ (N E ⟨60129601536,81450895201⟩ E))) ⟨60129602560,57130125805⟩ (N (N (N E ⟨60129605632,11530527128⟩ E) ⟨62277085696,76332532051⟩ (N E ⟨62813957120,65221550647⟩ E)) ⟨62813958464,37346344857⟩ (N (N E ⟨62813960320,12524178889⟩ E) ⟨63350828800,49400745629⟩ (N E ⟨63350829568,34938544932⟩ E)))) ⟨63350829760,31761760685⟩ (N (N (N (N E ⟨63350831104,14174468998⟩ E) ⟨63350831488,10561059564⟩ (N E ⟨64156135936,36196161573⟩ E)) ⟨64760116448,25219863798⟩ (N (N E ⟨64760117376,13822922534⟩ E) ⟨64961443072,24964447944⟩ (N E ⟨64961443840,15299899900⟩ E))) ⟨65162769952,21197196115⟩ (N (N (N E ⟨65162770816,11542172995⟩ E) ⟨65498316608,2161654633⟩ (N E ⟨65498316800,1506819731⟩ E)) ⟨65733195440,19784936895⟩ (N (N E ⟨65733195904,14382857067⟩ E) ⟨65766749824,20424671923⟩ (N E ⟨65766750208,15796209189⟩ E))))))) ⟨66068740048,16517231195⟩ (N (N (N (N (N (N (N E ⟨66068740480,11958745632⟩ E) ⟨66169403392,16025946064⟩ (N E ⟨66219735168,14637317128⟩ E)) ⟨66521725312,12146351030⟩ (N (N E ⟨66572056960,12166310592⟩ E) ⟨66572057344,8736281070⟩ (N E ⟨66572058112,3695924056⟩ E))) ⟨66572058624,1582848890⟩ (N (N (N E ⟨66706274664,12455181737⟩ E) ⟨66706274896,10274232917⟩ (N E ⟨66706275360,6599075710⟩ E)) ⟨66706276288,1804170120⟩ (N (N E ⟨66773385216,1593922516⟩ E) ⟨66949544528,10351402322⟩ (N E ⟨66974710360,10287535730⟩ E)))) ⟨66974710528,8846918746⟩ (N (N (N (N E ⟨66974710576,8457379249⟩ E) ⟨66974711008,5380608052⟩ (N E ⟨66974711808,1603951009⟩ E)) ⟨67192814276,9406551091⟩ (N (N E ⟨67192814392,8446267449⟩ E) ⟨67192814624,6695668958⟩ (N E ⟨67201202884,9408758780⟩ E))) ⟨67201202992,8512647331⟩ (N (N (N E ⟨67314449200,8539108601⟩ E) ⟨67314449208,8474496370⟩ (N E ⟨67377364096,6066152698⟩ E)) ⟨67377364480,3785019827⟩ (N (N E ⟨67427695516,7712665796⟩ E) ⟨67427695624,6909605630⟩ (N E ⟨67427695840,5447824625⟩ E))))) ⟨67436084140,7592259489⟩ (N (N (N (N (N E ⟨67436084256,6739185667⟩ E) ⟨67444473856,1623212765⟩ (N E ⟨67540941832,6929342825⟩ E)) ⟨67557719072,6759729845⟩ (N (N E ⟨67645800448,1629667415⟩ E) ⟨67654188148,6189035296⟩ (N E ⟨67654188256,5477660057⟩ E))) ⟨67679354004,5976774446⟩ (N (N (N E ⟨67679354120,5229205555⟩ E) ⟨67679354352,3895806887⟩ (N E ⟨67679354816,1850310580⟩ E)) ⟨67767434464,5491622117⟩ (N (N E ⟨67780017472,4898554551⟩ E) ⟨67780017664,3819698427⟩ (N E ⟨67800988936,5243238134⟩ E)))) ⟨67880680780,4836965686⟩ (N (N (N (N E ⟨67880680888,4215794124⟩ E) ⟨67880681104,3110902549⟩ (N E ⟨67880681472,1635815150⟩ E)) ⟨67922623868,4558943825⟩ (N (N E ⟨67922623984,3915022730⟩ E) ⟨67981344256,3834513416⟩ (N E ⟨67993927096,4224912015⟩ E))) ⟨68044258800,3923692751⟩ (N (N (N E ⟨68082008064,1639891309⟩ E) ⟨68107173412,3655290937⟩ (N E ⟨68107173520,3122730614⟩ E)) ⟨68165893732,3337264699⟩ (N (N E ⟨68165893848,2794987398⟩ E) ⟨68165894080,1863235879⟩ (N E ⟨68182671040,2903628000⟩ E)))))) ⟨68182671232,2100632176⟩ (N (N (N (N (N (N E ⟨68182671360,1641514388⟩ E) ⟨68220419728,3127916271⟩ (N E ⟨68283334656,1642860036⟩ E)) ⟨68287528664,2799418300⟩ (N (N E ⟨68316889088,1643246852⟩ E) ⟨68333666044,2642586011⟩ (N E ⟨68333666152,2196937193⟩ E))) ⟨68333666304,1643428677⟩ (N (N (N E ⟨68383997824,2104769793⟩ E) ⟨68409163596,2309891258⟩ (N E ⟨68409163712,1867112451⟩ E)) ⟨68446912360,2199082508⟩ (N (N E ⟨68530798528,1868400648⟩ E) ⟨68560158676,1797172682⟩ (N E ⟨68560158720,1645126676⟩ E)))) ⟨68585324544,1645228303⟩ (N (N (N (N E ⟨68652433408,1645414146⟩ E) ⟨68673404928,1645446815⟩ (N E ⟨68719542324,1474377683⟩ E)) ⟨68719542336,1436255057⟩ (N (N E ⟨68719542440,1127174177⟩ E) ⟨68719542464,1061259562⟩ (N E ⟨68719542528,895367555⟩ E))) ⟨68719542672,574380421⟩ (N (N (N E ⟨68719542688,543159341⟩ E) ⟨68719542720,483371336⟩ (N E ⟨68719542880,237237242⟩ E)) ⟨68719543136,24319712⟩ (N (N E ⟨68753097568,24319712⟩ E) ⟨68774068392,1127174177⟩ (N E ⟨68786651392,895367555⟩ E))))) ⟨68786651416,836853921⟩ (N (N (N (N (N E ⟨68786651632,400308901⟩ E) ⟨68786652064,5411364⟩ (N E ⟨68895703440,574380421⟩ E)) ⟨68987978368,198510502⟩ (N (N E ⟨69013144048,400308901⟩ E) ⟨69138973304,207865661⟩ (N E ⟨69138973536,24319712⟩ E))) ⟨69155750816,5411364⟩ (N (N (N E ⟨69239636680,124082051⟩ E) ⟨69239636896,5411364⟩ (N E ⟨69382243168,24319712⟩ E)) ⟨69466129312,5411364⟩ (N (N E ⟨69793285504,2414149⟩ E) ⟨69793285632,2395549⟩ (N E ⟨69793285840,2365704⟩ E)))) ⟨69793285888,2358883⟩ (N (N (N (N E ⟨69793285936,2352087⟩ E) ⟨69793286144,2322919⟩ (N E ⟨69793286544,2268088⟩ E)) ⟨69793286560,2265929⟩ (N (N E ⟨69793286656,2253027⟩ E) ⟨69793286752,2240217⟩ (N E ⟨69793287088,2196094⟩ E))) ⟨69793287168,2185750⟩ (N (N (N E ⟨69793287392,2157108⟩ E) ⟨69793287968,2085588⟩ (N E ⟨69793288000,2081703⟩ E)) ⟨69793288192,2058579⟩ (N (N E ⟨69793288384,2035776⟩ E) ⟨69793289216,1940543⟩ (N E ⟨69810063168,4693333⟩ E))))))))

noncomputable def tab1 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨69843617856,11614602⟩ E) ⟨69843618688,11053934⟩ E) ⟨69893949024,28883500⟩ (N E ⟨69910726256,36131620⟩ E)) ⟨69910726464,35682246⟩ (N (N E ⟨69994612624,83390467⟩ E) ⟨69994612720,82911860⟩ (N E ⟨69994612928,81886628⟩ E))) ⟨70011389648,96505337⟩ (N (N (N E ⟨70011389952,94759960⟩ E) ⟨70028167088,108011776⟩ (N E ⟨70028167392,106064860⟩ E)) ⟨70028167504,105358671⟩ (N (N E ⟨70028167808,103471352⟩ E) ⟨70061721248,138285081⟩ (N E ⟨70061721456,136566458⟩ E)))) ⟨70061721664,134874514⟩ (N (N (N (N E ⟨70061722080,131568687⟩ E) ⟨70061722496,128363755⟩ (N E ⟨70061722912,125256038⟩ E)) ⟨70061723328,122242010⟩ (N (N E ⟨70061724160,116481657⟩ E) ⟨70061724992,111057344⟩ (N E ⟨70061725824,105945771⟩ E))) ⟨70061727488,96576815⟩ (N (N (N E ⟨70061727744,95228999⟩ E) ⟨70112052992,186158274⟩ (N E ⟨70112053040,185621927⟩ E)) ⟨70112053248,183320007⟩ (N (N E ⟨70128830272,203249109⟩ E) ⟨70145607424,222733661⟩ (N E ⟨70195939072,283809384⟩ E))))) ⟨70195940320,263475724⟩ (N (N (N (N (N E ⟨70195940736,257105912⟩ E) ⟨70212716736,297726860⟩ (N E ⟨70229493512,328521270⟩ E)) ⟨70229493560,327574871⟩ (N (N E ⟨70229493664,325536030⟩ E) ⟨70229493872,321505826⟩ (N E ⟨70229493968,319666822⟩ E))) ⟨70229494176,315727311⟩ (N (N (N E ⟨70229494784,304555423⟩ E) ⟨70229496000,283658578⟩ (N E ⟨70263049056,352533813⟩ E)) ⟨70263049664,340141246⟩ (N (N E ⟨70263049888,335713460⟩ E) ⟨70263050496,324053974⟩ (N E ⟨70263051552,304983336⟩ E)))) ⟨70263052160,294639592⟩ (N (N (N (N E ⟨70279825264,399534449⟩ E) ⟨70279825472,394584551⟩ (N E ⟨70313380032,443377911⟩ E)) ⟨70330156952,478911471⟩ (N (N E ⟨70330157056,475935030⟩ E) ⟨70338545568,492790117⟩ (N E ⟨70346934496,497487919⟩ E))) ⟨70346934912,485323301⟩ (N (N (N E ⟨70388877216,581804688⟩ E) ⟨70430820448,654143399⟩ (N E ⟨70430820656,646068310⟩ E)) ⟨70430820752,642383481⟩ (N (N E ⟨70430820960,634489588⟩ E) ⟨70430821376,619063056⟩ (N E ⟨70430822208,589594224⟩ E)))))) ⟨70439208960,674424696⟩ (N (N (N (N (N (N E ⟨70447597528,692802516⟩ E) ⟨70447597680,686526830⟩ (N E ⟨70447597984,674187690⟩ E)) ⟨70464375424,698060319⟩ (N (N E ⟨70497929176,797737052⟩ E) ⟨70497929280,792783899⟩ (N E ⟨70497929488,782992656⟩ E))) ⟨70497929696,773352456⟩ (N (N (N E ⟨70497929904,763860504⟩ E) ⟨70497930112,754514068⟩ (N E ⟨70497930944,718530834⟩ E)) ⟨70548260816,910627921⟩ (N (N E ⟨70548260920,904973145⟩ E) ⟨70548260968,902378090⟩ (N E ⟨70548261072,896787379⟩ E)))) ⟨70548261280,885735549⟩ (N (N (N (N E ⟨70598592720,1015015205⟩ E) ⟨70598593024,996798203⟩ (N E ⟨70598593120,991130713⟩ E)) ⟨70598593184,987374804⟩ (N (N E ⟨70598593984,941896883⟩ E) ⟨70598594112,934865887⟩ (N E ⟨70598594304,924442220⟩ E))) ⟨70598595136,880920042⟩ (N (N (N E ⟨70598595520,861699413⟩ E) ⟨70598595712,852286103⟩ (N E ⟨70598595968,839934492⟩ E)) ⟨70598596352,821824466⟩ (N (N E ⟨70598596800,801309854⟩ E) ⟨70598597952,751428422⟩ (N E ⟨70598598016,748772886⟩ E))))) ⟨70598598656,722853285⟩ (N (N (N (N (N E ⟨70606981184,1044394840⟩ E) ⟨70606981232,1041400348⟩ (N E ⟨70632147536,1073153345⟩ E)) ⟨70632147744,1060003687⟩ (N (N E ⟨70632148144,1035278337⟩ E) ⟨70632148352,1022706643⟩ (N E ⟨70648924360,1141237552⟩ E))) ⟨70648924464,1134177194⟩ (N (N (N E ⟨70648924768,1113850670⟩ E) ⟨70657312824,1172974246⟩ (N E ⟨70657312976,1162364326⟩ E)) ⟨70665701696,1176357022⟩ (N (N E ⟨70665701752,1172438358⟩ E) ⟨70665701904,1161884123⟩ (N E ⟨70665702168,1143834430⟩ E)))) ⟨70665702208,1141130358⟩ (N (N (N (N E ⟨70665702320,1133601450⟩ E) ⟨70665702624,1113477271⟩ (N E ⟨70665702816,1100997602⟩ E)) ⟨70665703232,1074553868⟩ (N (N E ⟨70665704448,1001688603⟩ E) ⟨70707644520,1304841135⟩ (N E ⟨70707644624,1296756953⟩ E))) ⟨70716033192,1323040638⟩ (N (N (N E ⟨70716033296,1314851598⟩ E) ⟨70716033504,1298663154⟩ (N E ⟨70716033920,1267028524⟩ E)) ⟨70732814208,1098639492⟩ (N (N E ⟨70732816384,973352611⟩ E) ⟨70749587856,1398371502⟩ (N E ⟨70749588064,1381187693⟩ E))))))) ⟨70757976368,1430422877⟩ (N (N (N (N (N (N (N E ⟨70766364936,1458134824⟩ E) ⟨70766365088,1444986704⟩ (N E ⟨70816696528,1613660963⟩ E)) ⟨70825085096,1643421514⟩ (N (N E ⟨70825085200,1633249457⟩ E) ⟨70825085456,1608544589⟩ (N E ⟨70825085872,1569389271⟩ E))) ⟨70850251552,1658854628⟩ (N (N (N E ⟨70850252160,1600486554⟩ E) ⟨70867028328,1755843377⟩ (N E ⟨70867028376,1750831434⟩ E)) ⟨70867028480,1740033569⟩ (N (N E ⟨70867028688,1718686990⟩ E) ⟨70867028784,1708945411⟩ (N E ⟨70867028992,1688074859⟩ E)))) ⟨70883805712,1791752673⟩ (N (N (N (N E ⟨70900583456,1789151540⟩ E) ⟨70900583872,1745937500⟩ (N E ⟨70900584704,1663361889⟩ E)) ⟨70900586368,1512378518⟩ (N (N E ⟨70925748640,1941677713⟩ E) ⟨70934137104,1986865795⟩ (N E ⟨70934137208,1974587193⟩ E))) ⟨70934137312,1962403517⟩ (N (N (N E ⟨70934137416,1950313884⟩ E) ⟨70934137520,1938317424⟩ (N E ⟨70934137728,1914600582⟩ E)) ⟨70934137936,1891246201⟩ (N (N E ⟨70934138144,1868247640⟩ E) ⟨70934138560,1823292115⟩ (N E ⟨70934138976,1779683648⟩ E))))) ⟨70934139392,1737373987⟩ (N (N (N (N (N E ⟨70934140640,1617784893⟩ E) ⟨70934141056,1580226720⟩ (N E ⟨70934142976,1420381457⟩ E)) ⟨70967691872,2061158591⟩ (N (N E ⟨70976080384,2102028974⟩ E) ⟨70984469104,2117190646⟩ (N E ⟨70984469160,2110170001⟩ E))) ⟨70984469312,2091260458⟩ (N (N (N E ⟨70984469728,2040582806⟩ E) ⟨71026412032,2280878086⟩ (N E ⟨71043189112,2361179887⟩ E)) ⟨71043189216,2346610841⟩ (N (N E ⟨71043189424,2317809076⟩ E) ⟨71068355568,2365116209⟩ (N E ⟨71068355776,2336314258⟩ E)))) ⟨71068356192,2280016634⟩ (N (N (N (N E ⟨71068356384,2254606601⟩ E) ⟨71068356800,2200757334⟩ (N E ⟨71068357632,2097806599⟩ E)) ⟨71085132344,2490659729⟩ (N (N E ⟨71085132448,2475335912⟩ E) ⟨71085132496,2468303226⟩ (N E ⟨71085132800,2424339420⟩ E))) ⟨71101909936,2498367647⟩ (N (N (N E ⟨71101910240,2454015554⟩ E) ⟨71101910848,2368231463⟩ (N E ⟨71135465728,2425206911⟩ E)) ⟨71143852864,2675952866⟩ (N (N E ⟨71152241120,2765908458⟩ E) ⟨71152241224,2748868733⟩ (N E ⟨71152241328,2731960330⟩ E)))))) ⟨71152241432,2715182033⟩ (N (N (N (N (N (N E ⟨71152241536,2698532640⟩ E) ⟨71152241848,2649346056⟩ (N E ⟨71152241952,2633200514⟩ E)) ⟨71185795888,2844737817⟩ (N (N E ⟨71185796096,2809996363⟩ E) ⟨71202573120,2909913683⟩ (N E ⟨71244516048,3103672014⟩ E))) ⟨71261293232,3180900751⟩ (N (N (N E ⟨71261293440,3141979921⟩ E) ⟨71261293856,3065911830⟩ (N E ⟨71269682560,3083169201⟩ E)) ⟨71286459584,3188481743⟩ (N (N E ⟨71303236512,3315436926⟩ E) ⟨71303236720,3275014266⟩ (N E ⟨71303237024,3217039180⟩ E)))) ⟨71303237136,3196004429⟩ (N (N (N (N E ⟨71303237440,3139772410⟩ E) ⟨71336791488,3353558517⟩ (N E ⟨71370345240,3642238559⟩ E)) ⟨71370345344,3619904491⟩ (N (N E ⟨71370345552,3575748739⟩ E) ⟨71370345760,3532265730⟩ (N E ⟨71370345968,3489443174⟩ E))) ⟨71370346176,3447269043⟩ (N (N (N E ⟨71370347008,3284825021⟩ E) ⟨71370348672,2987709215⟩ (N E ⟨71403899904,3745497722⟩ E)) ⟨71403900160,3689472134⟩ (N (N E ⟨71403900928,3527578325⟩ E) ⟨71420677344,3773042578⟩ (N E ⟨71471009952,3789328716⟩ E))))) ⟨71471010368,3699325567⟩ (N (N (N (N (N E ⟨71471011584,3451160281⟩ E) ⟨71471013888,3035541833⟩ (N E ⟨71479397248,4132405831⟩ E)) ⟨71504563296,4199724892⟩ (N (N E ⟨71504563504,4148666078⟩ E) ⟨71504563600,4125362838⟩ (N E ⟨71504563648,4113772714⟩ E))) ⟨71504563808,4075432429⟩ (N (N (N E ⟨71504564208,3981522070⟩ E) ⟨71504564416,3933759813⟩ (N E ⟨71521340528,4277752557⟩ E)) ⟨71538118272,4227569083⟩ (N (N E ⟨71538118384,4200018034⟩ E) ⟨71538118688,4126362338⟩ (N E ⟨71538119296,3983842031⟩ E)))) ⟨71538119520,3932892559⟩ (N (N (N (N E ⟨71538120128,3798657876⟩ E) ⟨71538120512,3716828417⟩ (N E ⟨71538121344,3546971375⟩ E)) ⟨71538122752,3281075879⟩ (N (N E ⟨71571672640,4406916156⟩ E) ⟨71588449360,4622487389⟩ (N E ⟨71588449568,4566275481⟩ E))) ⟨71588449984,4456397484⟩ (N (N (N E ⟨71622004128,4701926177⟩ E) ⟨71622004544,4588995427⟩ (N E ⟨71705890384,5087720185⟩ E)) ⟨71705890592,5026315551⟩ (N (N E ⟨71705891008,4906266489⟩ E) ⟨71722667312,5264985379⟩ (N E ⟨71722667616,5172046085⟩ E))))))))

noncomputable def tab2 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨71739444752,5286596046⟩ E) ⟨71739445056,5193581166⟩ E) ⟨71806553376,5735836610⟩ (N E ⟨71806553584,5666299604⟩ E)) ⟨71806553792,5597815537⟩ (N (N E ⟨71806554208,5463930158⟩ E) ⟨71806554624,5334032333⟩ (N E ⟨71806555456,5085637335⟩ E))) ⟨71806556288,4851563615⟩ (N (N (N E ⟨71806557120,4630829728⟩ E) ⟨71806557952,4422531958⟩ (N E ⟨71806558208,4360811591⟩ E)) ⟨71823330912,5723111485⟩ (N (N E ⟨71856885792,5760774041⟩ E) ⟨71873663936,5549362183⟩ (N E ⟨71873664768,5292566695⟩ E)))) ⟨71873666432,4822112994⟩ (N (N (N (N E ⟨71907217984,5856992598⟩ E) ⟨71923994400,6232361261⟩ (N E ⟨71940771840,6248616222⟩ E)) ⟨71940772256,6099857213⟩ (N (N E ⟨71940772864,5890329606⟩ E) ⟨71974326912,6210711176⟩ (N E ⟨72007882624,5952087208⟩ E))) ⟨72024657600,6871892121⟩ (N (N (N E ⟨72058212160,7027041309⟩ E) ⟨72142098624,7389616249⟩ (N E ⟨72175653088,7587921710⟩ E)) ⟨72175653504,7407861677⟩ (N (N E ⟨72175654336,7063516044⟩ E) ⟨72209207296,7904995271⟩ (N E ⟨72242761824,8080762806⟩ E))))) ⟨72242762240,7888653193⟩ (N (N (N (N (N E ⟨72343425824,8409523390⟩ E) ⟨72343426016,8317444884⟩ (N E ⟨72343426432,8122234720⟩ E)) ⟨72343427264,7748731334⟩ (N (N E ⟨72343427648,7583607950⟩ E) ⟨72343428480,7240694588⟩ (N E ⟨72343429120,6990049945⟩ E))) ⟨72376979872,8825249880⟩ (N (N (N E ⟨72410535040,8681119975⟩ E) ⟨72410535360,8524215433⟩ (N E ⟨72410536576,7959429123⟩ E)) ⟨72544753024,9455518097⟩ (N (N E ⟨72578307072,9902332772⟩ E) ⟨72678970688,10439028257⟩ (N E ⟨72678971520,9958557075⟩ E)))) ⟨72678973184,9077905685⟩ (N (N (N (N E ⟨72746080000,10655959455⟩ E) ⟨72779634048,11139873131⟩ (N E ⟨72813188928,11105875671⟩ E)) ⟨72813189760,10598343178⟩ (N (N E ⟨72980960640,12693525987⟩ E) ⟨72980961472,12109810408⟩ (N E ⟨73014514432,13445461595⟩ E))) ⟨73014515200,12868277546⟩ (N (N (N E ⟨73014516736,11804078720⟩ E) ⟨73014517760,11155432404⟩ (N E ⟨73148735488,12104668324⟩ E)) ⟨73215841888,14448378430⟩ (N (N E ⟨73215842496,13960550597⟩ E) ⟨73215843712,13045242996⟩ (N E ⟨73282953216,13092218008⟩ E)))))) ⟨73551388416,15396192461⟩ (N (N (N (N (N (N E ⟨73551388672,15181324901⟩ E) ⟨73618496896,16291095525⟩ (N E ⟨73819821568,20095445537⟩ E)) ⟨74088259584,19807550595⟩ (N (N E ⟨74222477312,21055464219⟩ E) ⟨74490912768,23658131590⟩ (N E ⟨74625129472,26466336692⟩ E))) ⟨76235743232,43773716666⟩ (N (N (N E ⟨77309485184,58065467467⟩ E) ⟨77309485312,57660655940⟩ (N E ⟨77309485568,56861581616⟩ E)) ⟨77309485632,56663983892⟩ (N (N E ⟨77309486080,55304609886⟩ E) ⟨77309486464,54171800066⟩ (N E ⟨77309486848,53067900800⟩ E)))) ⟨77309487104,52347592259⟩ (N (N (N (N E ⟨77309487744,50599666909⟩ E) ⟨77309488128,49585936005⟩ (N E ⟨77309490176,44588844334⟩ E)) ⟨77309493248,38217750111⟩ (N (N E ⟨77846356608,64045713359⟩ E) ⟨77980574464,65523567941⟩ (N E ⟨78114792448,66530373098⟩ E))) ⟨78383228032,69899943388⟩ (N (N (N E ⟨78383228928,66621352329⟩ E) ⟨78517445888,71336461494⟩ (N E ⟨78651663872,72261787581⟩ E)) ⟨78920099840,74031506677⟩ (N (N E ⟨79456972800,73216762336⟩ E) ⟨79456976896,59530259720⟩ (N E ⟨81604460544,81183335634⟩ E))))) ⟨85899431936,79111303097⟩ (N (N (N (N (N E ⟨85899433984,58281169397⟩ E) ⟨85899436032,38423148027⟩ (N E ⟨90194400256,80671901826⟩ E)) ⟨90194401280,68661704304⟩ (N (N E ⟨91268143104,71306668495⟩ E) ⟨92341885440,67628919902⟩ (N E ⟨92341886976,49536554442⟩ E))) ⟨92878757888,50467184291⟩ (N (N (N E ⟨93415628800,51392597158⟩ E) ⟨94489371648,41549598057⟩ (N E ⟨94489374000,19643703773⟩ E)) ⟨94489374272,17615762145⟩ (N (N E ⟨94489374720,14518912047⟩ E) ⟨94489378816,160224349⟩ (N E ⟨95563115008,27369202267⟩ E)))) ⟨95563116544,15127084783⟩ (N (N (N (N E ⟨96099990272,2254255576⟩ E) ⟨96099991552,206735025⟩ (N E ⟨96636859520,8710439800⟩ E)) ⟨96636861056,2661412564⟩ (N (N E ⟨96636861184,2321429255⟩ E) ⟨96636861376,1857100291⟩ (N E ⟨96636861440,1714381431⟩ E))) ⟨96636862464,221539557⟩ (N (N (N E ⟨96972405248,3075186906⟩ E) ⟨97173728512,21925999151⟩ (N E ⟨97173729280,15992932385⟩ E)) ⟨97844822016,252482848⟩ (N (N E ⟨97979035648,16400592164⟩ E) ⟨98029367804,12946140206⟩ (N E ⟨98029369032,6301883961⟩ E))))))) ⟨98029371392,256850309⟩ (N (N (N (N (N (N (N E ⟨98046147328,2484663355⟩ E) ⟨98247472960,5830488137⟩ (N E ⟨98247473792,2865431441⟩ E)) ⟨98247475200,261869607⟩ (N (N E ⟨98314580232,14689684134⟩ E) ⟨98314580944,10212442777⟩ (N E ⟨98314582368,3776822187⟩ E))) ⟨98381690816,5327363783⟩ (N (N (N E ⟨98381691648,2520368323⟩ E) ⟨98381691840,2026775216⟩ (N E ⟨98381692928,264878549⟩ E)) ⟨98448800768,1880376436⟩ (N (N E ⟨98448801792,266359493⟩ E) ⟨98784342784,11595794536⟩ (N E ⟨98784343552,7396470194⟩ E)))) ⟨98784345088,1907667332⟩ (N (N (N (N E ⟨98918562944,1627877613⟩ E) ⟨98918563840,276266374⟩ (N E ⟨99019225856,2584484318⟩ E)) ⟨99061167056,10445252625⟩ (N (N E ⟨99119888608,4341612636⟩ E) ⟨99254106880,2606818251⟩ (N E ⟨99317019746,9687208967⟩ E))) ⟨99317020360,6572872093⟩ (N (N (N E ⟨99354770432,1951279355⟩ E) ⟨99522543584,316894800⟩ (N E ⟨99556096640,3007668394⟩ E)) ⟨99589649920,7576977730⟩ (N (N E ⟨99790978528,994774472⟩ E) ⟨99790979072,292343642⟩ (N E ⟨99807753880,6890494413⟩ E))))) ⟨99807754592,3974337117⟩ (N (N (N (N (N E ⟨99960846024,6695562123⟩ E) ⟨99992303904,4225002732⟩ (N E ⟨99992304320,2857710233⟩ E)) ⟨99992304672,1918346496⟩ (N (N E ⟨99992305088,1057879182⟩ E) ⟨99992305152,948949382⟩ (N E ⟨99992305312,703443749⟩ E))) ⟨99992305664,295590471⟩ (N (N (N E ⟨100126523392,297653366⟩ E) ⟨100193631040,2508955363⟩ (N E ⟨100193631648,1122832782⟩ E)) ⟨100193631968,621066521⟩ (N (N E ⟨100193632032,538984544⟩ E) ⟨100193632064,500195058⟩ (N E ⟨100193632256,298653847⟩ E)))) ⟨100260740960,464243722⟩ (N (N (N (N E ⟨100394957056,4391059422⟩ E) ⟨100394957824,2021162141⟩ (N E ⟨100428511936,2894867816⟩ E)) ⟨100428512704,1074421947⟩ (N (N E ⟨100495622144,302895926⟩ E) ⟨100554340348,5436229149⟩ (N E ⟨100554340704,4059317735⟩ E))) ⟨100604672302,4245476007⟩ (N (N (N E ⟨100604672916,2310708476⟩ E) ⟨100604674048,304321524⟩ (N E ⟨100730502880,633583378⟩ E)) ⟨100764056688,1774028868⟩ (N (N E ⟨100764056736,1664927879⟩ E) ⟨100764057152,869728447⟩ (N E ⟨100764057520,385221871⟩ E)))))) ⟨100764057600,306301864⟩ (N (N (N (N (N (N E ⟨100797611040,1965782878⟩ E) ⟨100797611456,1087079664⟩ (N E ⟨100797611904,437575721⟩ E)) ⟨100797612032,306703022⟩ (N (N E ⟨100831165392,2168025104⟩ E) ⟨100831165856,1146245184⟩ (N E ⟨100831166464,307098665⟩ E))) ⟨100864720384,977714950⟩ (N (N (N E ⟨100864720544,726190532⟩ E) ⟨100864720896,307488777⟩ (N E ⟨100927633760,4098118583⟩ E)) ⟨100965383936,595717302⟩ (N (N E ⟨100965384192,308625792⟩ E) ⟨101066047488,309712523⟩ (N E ⟨101099600880,2101279625⟩ E)))) ⟨101099601296,1184774355⟩ (N (N (N (N E ⟨101099601312,1154952112⟩ E) ⟨101099601728,517048284⟩ (N E ⟨101099601920,310063528⟩ E)) ⟨101133156192,479268296⟩ (N (N E ⟨101133156352,310408892⟩ E) ⟨101166710144,1217155555⟩ (N E ⟨101166710496,642263482⟩ E))) ⟨101166710640,461154861⟩ (N (N (N E ⟨101166710656,442935733⟩ E) ⟨101166710784,310748602⟩ (N E ⟨101200264192,2066106152⟩ E)) ⟨101200264640,1099445450⟩ (N (N E ⟨101200264768,880882926⟩ E) ⟨101233818688,1910086330⟩ (N E ⟨101233818864,1510115658⟩ E))))) ⟨101233819072,1100406794⟩ (N (N (N (N (N E ⟨101248498580,2349737210⟩ E) ⟨101250596000,1686512006⟩ (N E ⟨101250596416,882066557⟩ E)) ⟨101300927172,2948437239⟩ (N (N E ⟨101300927528,1971649217⟩ E) ⟨101300928160,735419311⟩ (N E ⟨101300928240,622934764⟩ E))) ⟨101300928512,312050644⟩ (N (N (N E ⟨101317705120,1161511801⟩ E) ⟨101451922880,1106392965⟩ (N E ⟨101451923456,313406087⟩ E)) ⟨101468700208,913047089⟩ (N (N E ⟨101468700672,313549502⟩ E) ⟨101535808912,1197718980⟩ (N E ⟨101535809344,523287287⟩ E)))) ⟨101552585936,1591130060⟩ (N (N (N (N E ⟨101552586144,1168052884⟩ E) ⟨101552586560,523502181⟩ (N E ⟨101552586752,314244900⟩ E)) ⟨101569363376,1138762920⟩ (N (N E ⟨101569363808,485016017⟩ E) ⟨101602917968,863959624⟩ (N E ⟨101602918176,564400687⟩ E))) ⟨101602918400,314644752⟩ (N (N (N E ⟨101636472256,1111099962⟩ E) ⟨101636472752,395599341⟩ (N E ⟨101636472832,314904055⟩ E)) ⟨101653250048,315031524⟩ (N (N E ⟨101670027104,486170326⟩ E) ⟨101670027136,448920922⟩ (N E ⟨101670027264,315157535⟩ E))))))))

noncomputable def tab3 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨101686804032,891412305⟩ E) ⟨101737135520,1172807480⟩ E) ⟨101737135728,816001416⟩ (N E ⟨101737136128,315646986⟩ E)) ⟨101770689952,1173635306⟩ (N (N E ⟨101804244848,468738973⟩ E) ⟨101804244992,316113030⟩ (N E ⟨101821021984,567134267⟩ E))) ⟨101821022208,316225876⟩ (N (N (N E ⟨101837799424,316337253⟩ E) ⟨101892324858,1013390233⟩ (N E ⟨101892325376,316689076⟩ E)) ⟨101938462720,316974623⟩ (N (N E ⟨101955239536,819623632⟩ E) ⟨101955239632,676851836⟩ (N E ⟨101955239704,579033157⟩ E)))) ⟨101955239936,317075694⟩ (N (N (N (N E ⟨101972017072,398427395⟩ E) ⟨101972017152,317175288⟩ (N E ⟨101988794176,528427774⟩ E)) ⟨102005571200,795598303⟩ (N (N E ⟨102005571408,508875017⟩ E) ⟨102005571584,317370043⟩ (N E ⟨102022348640,489694720⟩ E))) ⟨102039125616,820910037⟩ (N (N (N E ⟨102039125824,528913509⟩ E) ⟨102039126000,333068084⟩ (N E ⟨102039126016,317558881⟩ E)) ⟨102047514352,633482992⟩ (N (N E ⟨102072680448,317741796⟩ E) ⟨102106234792,408044956⟩ (N E ⟨102106234880,317918781⟩ E))))) ⟨102123011952,471568212⟩ (N (N (N (N (N E ⟨102123012096,318005047⟩ E) ⟨102173343320,860912065⟩ (N E ⟨102173343528,560519867⟩ E)) ⟨102173343552,530124571⟩ (N (N E ⟨102173343744,318254933⟩ E) ⟨102190120960,318335254⟩ (N E ⟨102198509568,318374856⟩ E))) ⟨102223675000,811028158⟩ (N (N (N E ⟨102223675216,510751953⟩ E) ⟨102223675248,472326304⟩ (N E ⟨102223675392,318491431⟩ E)) ⟨102232063824,510817785⟩ (N (N E ⟨102232064000,318529544⟩ E) ⟨102257229632,530819082⟩ (N E ⟨102257229824,318641649⟩ E)))) ⟨102274006808,582188410⟩ (N (N (N (N E ⟨102274006944,417896412⟩ E) ⟨102274007040,318714522⟩ (N E ⟨102290784256,318785903⟩ E)) ⟨102324338688,318924188⟩ (N (N E ⟨102349504352,492241570⟩ E) ⟨102349504512,319023980⟩ (N E ⟨102391447336,562339169⟩ E))) ⟨102391447552,319182826⟩ (N (N (N E ⟨102408224768,319243747⟩ E) ⟨102416613184,532005893⟩ (N E ⟨102416613376,319273646⟩ E)) ⟨102425001984,319303171⟩ (N (N E ⟨102441779016,522194809⟩ E) ⟨102441779032,502522449⟩ (N E ⟨102441779128,392648455⟩ E)))))) ⟨102441779184,334975590⟩ (N (N (N (N (N (N E ⟨102441779200,319361098⟩ E) ⟨102450167632,512363395⟩ (N E ⟨102458556416,319417527⟩ E)) ⟨102475333632,319472457⟩ (N (N E ⟨102492110848,319525889⟩ E) ⟨102517276520,483670040⟩ (N E ⟨102517276672,319603224⟩ E))) ⟨102536151040,319659011⟩ (N (N (N E ⟨102592774144,319814974⟩ E) ⟨102609551360,319857900⟩ (N E ⟨102626328576,319899323⟩ E)) ⟨102634717184,319919471⟩ (N (N E ⟨102659882944,384940427⟩ E) ⟨102659883008,319977661⟩ (N E ⟨102668271616,319996305⟩ E)))) ⟨102676660224,320014574⟩ (N (N (N (N E ⟨102685048792,359924468⟩ E) ⟨102685048832,320032467⟩ (N E ⟨102693437440,320049984⟩ E)) ⟨102710214656,320083889⟩ (N (N E ⟨102735380480,320131925⟩ E) ⟨102760546304,320176575⟩ (N E ⟨102768934912,320190706⟩ E))) ⟨102794100736,320230839⟩ (N (N (N E ⟨102819266560,320267583⟩ E) ⟨102836043776,320290197⟩ (N E ⟨102844432384,320300938⟩ E)) ⟨102852820992,320311303⟩ (N (N E ⟨102877986816,320340138⟩ E) ⟨102886375424,320348997⟩ (N E ⟨102894764032,320357478⟩ E))))) ⟨102903152640,320365582⟩ (N (N (N (N (N E ⟨102911541248,320373310⟩ E) ⟨102919929856,320380661⟩ (N E ⟨102928318464,320387635⟩ E)) ⟨102953484288,320406296⟩ (N (N E ⟨102957678592,320409076⟩ E) ⟨102978650112,320421564⟩ (N E ⟨102995427328,320429858⟩ E))) ⟨103003815936,320433440⟩ (N (N (N E ⟨103012204544,320436644⟩ E) ⟨103020593152,320439472⟩ (N E ⟨103033176064,320443006⟩ E)) ⟨103037370368,320443996⟩ (N (N E ⟨103062536192,320447955⟩ E) ⟨103079313536,208253265⟩ (N E ⟨103079313664,120294753⟩ E)))) ⟨103079313792,56434938⟩ (N (N (N (N E ⟨103079313920,16522152⟩ E) ⟨103079314048,391458⟩ (N E ⟨103213531520,56434938⟩ E)) ⟨103213531648,16522152⟩ (N (N E ⟨103213531776,391458⟩ E) ⟨103347749376,16522152⟩ (N E ⟨103347749504,391458⟩ E))) ⟨103481967232,391458⟩ (N (N (N E ⟨103884620800,7783588⟩ E) ⟨103884620928,7743374⟩ (N E ⟨103884621056,7703420⟩ E)) ⟨103884621184,7663724⟩ (N (N E ⟨103884621312,7624283⟩ E) ⟨103884621440,7585096⟩ (N E ⟨103884621568,7546161⟩ E))))))) ⟨103884621696,7507476⟩ (N (N (N (N (N (N (N E ⟨103884621824,7469038⟩ E) ⟨103884621952,7430847⟩ (N E ⟨103884622080,7392899⟩ E)) ⟨103884622336,7317728⟩ (N (N E ⟨103884622464,7280502⟩ E) ⟨103884622592,7243512⟩ (N E ⟨103884622720,7206757⟩ E))) ⟨103884622848,7170235⟩ (N (N (N E ⟨103884622976,7133944⟩ E) ⟨103884623104,7097883⟩ (N E ⟨103884623232,7062050⟩ E)) ⟨103884623488,6991060⟩ (N (N E ⟨103884623744,6920961⟩ E) ⟨103884623872,6886241⟩ (N E ⟨103884624000,6851738⟩ E)))) ⟨103884624128,6817452⟩ (N (N (N (N E ⟨103884624256,6783381⟩ E) ⟨103884624384,6749522⟩ (N E ⟨103884624512,6715874⟩ E)) ⟨103884624768,6649206⟩ (N (N E ⟨103884624896,6616182⟩ E) ⟨103884625152,6550749⟩ (N E ⟨103884625536,6454109⟩ E))) ⟨103884625664,6422292⟩ (N (N (N E ⟨103884625792,6390672⟩ E) ⟨103884625920,6359246⟩ (N E ⟨103884626304,6266122⟩ E)) ⟨103884626816,6144594⟩ (N (N E ⟨103884627200,6055379⟩ E) ⟨103884627328,6026001⟩ (N E ⟨103884627584,5967779⟩ E))))) ⟨103884627968,5881758⟩ (N (N (N (N (N E ⟨104018838656,38351576⟩ E) ⟨104018838784,38153692⟩ (N E ⟨104018838912,37957083⟩ E)) ⟨104018839040,37761741⟩ (N (N E ⟨104018839168,37567655⟩ E) ⟨104018839296,37374816⟩ (N E ⟨104018839424,37183214⟩ E))) ⟨104018839552,36992839⟩ (N (N (N E ⟨104018839680,36803682⟩ E) ⟨104018839808,36615735⟩ (N E ⟨104018839936,36428986⟩ E)) ⟨104018840064,36243429⟩ (N (N E ⟨104018840192,36059052⟩ E) ⟨104018840448,35693806⟩ (N E ⟨104018840576,35512919⟩ E)))) ⟨104018840704,35333178⟩ (N (N (N (N E ⟨104018840832,35154574⟩ E) ⟨104018840960,34977098⟩ (N E ⟨104018841472,34278307⟩ E)) ⟨104018841600,34106345⟩ (N (N E ⟨104018841856,33765649⟩ E) ⟨104018842752,32606248⟩ (N E ⟨104018843392,31808491⟩ E))) ⟨104018844160,30883143⟩ (N (N (N E ⟨104018844544,30433100⟩ E) ⟨104018845184,29701110⟩ (N E ⟨104018845696,29131321⟩ E)) ⟨104153056512,91890686⟩ (N (N E ⟨104153056640,91417168⟩ E) ⟨104153056768,90946698⟩ (N E ⟨104153056896,90479255⟩ E)))))) ⟨104153057024,90014814⟩ (N (N (N (N (N (N E ⟨104153057152,89553353⟩ E) ⟨104153057280,89094848⟩ (N E ⟨104153057408,88639277⟩ E)) ⟨104153057536,88186617⟩ (N (N E ⟨104153057664,87736846⟩ E) ⟨104153057792,87289942⟩ (N E ⟨104153057920,86845883⟩ E))) ⟨104153058048,86404646⟩ (N (N (N E ⟨104153058176,85966212⟩ E) ⟨104153058304,85530558⟩ (N E ⟨104153058432,85097663⟩ E)) ⟨104153058560,84667506⟩ (N (N E ⟨104153058688,84240066⟩ E) ⟨104153058816,83815324⟩ (N E ⟨104153058944,83393257⟩ E)))) ⟨104153059072,82973847⟩ (N (N (N (N E ⟨104153059328,82142915⟩ E) ⟨104153059456,81731354⟩ (N E ⟨104153059712,80915943⟩ E)) ⟨104153059968,80110686⟩ (N (N E ⟨104153060096,79711817⟩ E) ⟨104153060224,79315431⟩ (N E ⟨104153060480,78530030⟩ E))) ⟨104153062144,73655234⟩ (N (N (N E ⟨104153063296,70500857⟩ E) ⟨104153063424,70160892⟩ (N E ⟨104287274368,168187774⟩ E)) ⟨104287274496,167322213⟩ (N (N E ⟨104287274624,166462218⟩ E) ⟨104287274752,165607748⟩ (N E ⟨104287274880,164758759⟩ E))))) ⟨104287275008,163915209⟩ (N (N (N (N (N E ⟨104287275136,163077057⟩ E) ⟨104287275264,162244261⟩ (N E ⟨104287275392,161416780⟩ E)) ⟨104287275520,160594573⟩ (N (N E ⟨104287275648,159777600⟩ E) ⟨104287275776,158965821⟩ (N E ⟨104287275904,158159197⟩ E))) ⟨104287276032,157357688⟩ (N (N (N E ⟨104287276160,156561255⟩ E) ⟨104287276288,155769859⟩ (N E ⟨104287276416,154983463⟩ E)) ⟨104287276672,153425518⟩ (N (N E ⟨104287276800,152653895⟩ E) ⟨104287276928,151887121⟩ (N E ⟨104287277056,151125160⟩ E)))) ⟨104287277568,148124730⟩ (N (N (N (N E ⟨104287277696,147386298⟩ E) ⟨104287277952,145923201⟩ (N E ⟨104287278720,141641611⟩ E)) ⟨104287279872,135509667⟩ (N (N E ⟨104287281152,129080835⟩ E) ⟨104421492224,267017435⟩ (N E ⟨104421492352,265645031⟩ E))) ⟨104421492480,264281444⟩ (N (N (N E ⟨104421492608,262926604⟩ E) ⟨104421492736,261580444⟩ (N E ⟨104421492864,260242897⟩ E)) ⟨104421492992,258913898⟩ (N (N E ⟨104421493120,257593381⟩ E) ⟨104421493248,256281280⟩ (N E ⟨104421493376,254977533⟩ E))))))))

noncomputable def tab4 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨104421493632,252394840⟩ E) ⟨104421493760,251115769⟩ E) ⟨104421494016,248581868⟩ (N E ⟨104421494272,246079881⟩ E)) ⟨104421494528,243609325⟩ (N (N E ⟨104421494656,242385686⟩ E) ⟨104421494912,239961393⟩ (N E ⟨104421495168,237567365⟩ E))) ⟨104421495680,232868298⟩ (N (N (N E ⟨104421495808,231711749⟩ E) ⟨104421496320,227156804⟩ (N E ⟨104421497344,218378112⟩ E)) ⟨104555710208,386149818⟩ (N (N E ⟨104555710336,384170219⟩ E) ⟨104555710464,382203303⟩ (N E ⟨104555710592,380248972⟩ E)))) ⟨104555710720,378307131⟩ (N (N (N (N E ⟨104555710848,376377682⟩ E) ⟨104555710976,374460531⟩ (N E ⟨104555711104,372555585⟩ E)) ⟨104555711232,370662749⟩ (N (N E ⟨104555711360,368781933⟩ E) ⟨104555711488,366913043⟩ (N E ⟨104555711616,365055989⟩ E))) ⟨104555711744,363210682⟩ (N (N (N E ⟨104555712000,359554950⟩ E) ⟨104555712128,357744350⟩ (N E ⟨104555712384,354157247⟩ E)) ⟨104555712512,352380573⟩ (N (N E ⟨104555712640,350615038⟩ E) ⟨104555712896,347117049⟩ (N E ⟨104555713664,336881845⟩ E))))) ⟨104555713792,335212874⟩ (N (N (N (N (N E ⟨104555714176,330267653⟩ E) ⟨104555714304,328639557⟩ (N E ⟨104555716608,300979524⟩ E)) ⟨104689928064,528588957⟩ (N (N E ⟨104689928192,525882631⟩ E) ⟨104689928320,523193621⟩ (N E ⟨104689928448,520521794⟩ E))) ⟨104689928576,517867020⟩ (N (N (N E ⟨104689928704,515229167⟩ E) ⟨104689928832,512608105⟩ (N E ⟨104689928960,510003708⟩ E)) ⟨104689929088,507415847⟩ (N (N E ⟨104689929216,504844397⟩ E) ⟨104689929472,499750230⟩ (N E ⟨104689929728,494720222⟩ E)))) ⟨104689929856,492228974⟩ (N (N (N (N E ⟨104689929984,489753404⟩ E) ⟨104689930240,484848826⟩ (N E ⟨104689930368,482419584⟩ E)) ⟨104689930496,480005552⟩ (N (N E ⟨104689930624,477606617⟩ E) ⟨104689930752,475222665⟩ (N E ⟨104689931520,461227380⟩ E))) ⟨104689932032,452182996⟩ (N (N (N E ⟨104689932288,447744022⟩ E) ⟨104689932672,441187293⟩ (N E ⟨104689933184,432630731⟩ E)) ⟨104689934336,414124897⟩ (N (N E ⟨104824146048,689161212⟩ E) ⟨104824146176,685641829⟩ (N E ⟨104824146304,682144906⟩ E)))))) ⟨104824146432,678670273⟩ (N (N (N (N (N (N E ⟨104824146560,675217758⟩ E) ⟨104824146688,671787193⟩ (N E ⟨104824146816,668378410⟩ E)) ⟨104824146944,664991244⟩ (N (N E ⟨104824147072,661625530⟩ E) ⟨104824147200,658281105⟩ (N E ⟨104824147328,654957807⟩ E))) ⟨104824147456,651655476⟩ (N (N (N E ⟨104824147584,648373954⟩ E) ⟨104824147840,641872708⟩ (N E ⟨104824147968,638652674⟩ E)) ⟨104824148096,635452827⟩ (N (N E ⟨104824148224,632273016⟩ E) ⟨104824148480,625972900⟩ (N E ⟨104824148736,619751139⟩ E)))) ⟨104824148864,616669275⟩ (N (N (N (N E ⟨104824149120,610562862⟩ E) ⟨104824149248,607538028⟩ (N E ⟨104824149504,601544403⟩ E)) ⟨104824149632,598575336⟩ (N (N E ⟨104824150144,586880855⟩ E) ⟨104824150272,584002014⟩ (N E ⟨104824150528,578297144⟩ E))) ⟨104824151296,561595838⟩ (N (N (N E ⟨104824152064,545493685⟩ E) ⟨104958363904,873737158⟩ (N E ⟨104958364032,869280908⟩ E)) ⟨104958364160,864853062⟩ (N (N E ⟨104958364288,860453403⟩ E) ⟨104958364416,856081715⟩ (N E ⟨104958364544,851737785⟩ E))))) ⟨104958364672,847421402⟩ (N (N (N (N (N E ⟨104958364800,843132356⟩ E) ⟨104958364928,838870438⟩ (N E ⟨104958365056,834635445⟩ E)) ⟨104958365184,830427171⟩ (N (N E ⟨104958365312,826245413⟩ E) ⟨104958365440,822089973⟩ (N E ⟨104958365568,817960650⟩ E))) ⟨104958365824,809779573⟩ (N (N (N E ⟨104958366208,797698973⟩ E) ⟨104958366592,785843041⟩ (N E ⟨104958366848,778061427⟩ E)) ⟨105092581760,1079330537⟩ (N (N E ⟨105092581888,1073832764⟩ E) ⟨105092582016,1068369988⟩ (N E ⟨105092582144,1062941942⟩ E)))) ⟨105092582272,1057548362⟩ (N (N (N (N E ⟨105092582400,1052188985⟩ E) ⟨105092582528,1046863551⟩ (N E ⟨105092582656,1041571801⟩ E)) ⟨105092582912,1031088334⟩ (N (N E ⟨105092583040,1025896114⟩ E) ⟨105092583424,1010514521⟩ (N E ⟨105092583552,1005451532⟩ E))) ⟨105092583808,995420420⟩ (N (N (N E ⟨105092584192,980607380⟩ E) ⟨105092584576,966069138⟩ (N E ⟨105092585088,947101756⟩ E)) ⟨105092585472,933181255⟩ (N (N E ⟨105092586240,906099859⟩ E) ⟨105092587136,875735766⟩ (N E ⟨105092587520,863112789⟩ E))))))) ⟨105226799616,1305650518⟩ (N (N (N (N (N (N (N E ⟨105226799744,1299008444⟩ E) ⟨105226799872,1292408599⟩ (N E ⟨105226800000,1285850659⟩ E)) ⟨105226800128,1279334306⟩ (N (N E ⟨105226800256,1272859223⟩ E) ⟨105226800384,1266425096⟩ (N E ⟨105226800512,1260031615⟩ E))) ⟨105226800640,1253678471⟩ (N (N (N E ⟨105226800768,1247365360⟩ E) ⟨105226800896,1241091979⟩ (N E ⟨105226801024,1234858027⟩ E)) ⟨105226801152,1228663208⟩ (N (N E ⟨105226801280,1222507226⟩ E) ⟨105226801408,1216389790⟩ (N E ⟨105226801536,1210310610⟩ E)))) ⟨105226801664,1204269399⟩ (N (N (N (N E ⟨105226801792,1198265872⟩ E) ⟨105226801920,1192299748⟩ (N E ⟨105226802048,1186370747⟩ E)) ⟨105226802176,1180478592⟩ (N (N E ⟨105226802304,1174623007⟩ E) ⟨105226802688,1157272969⟩ (N E ⟨105226802816,1151560969⟩ E))) ⟨105226803200,1134635327⟩ (N (N (N E ⟨105226803712,1112549047⟩ E) ⟨105226804096,1096336493⟩ (N E ⟨105226804480,1080418470⟩ E)) ⟨105226804864,1064788573⟩ (N (N E ⟨105226805248,1049440563⟩ E) ⟨105361017600,1544508370⟩ (N E ⟨105361017728,1536671226⟩ E))))) ⟨105361017856,1528883780⟩ (N (N (N (N (N E ⟨105361017984,1521145654⟩ E) ⟨105361018112,1513456474⟩ (N E ⟨105361018240,1505815868⟩ E)) ⟨105361018368,1498223468⟩ (N (N E ⟨105361018496,1490678909⟩ E) ⟨105361018624,1483181829⟩ (N E ⟨105361018752,1475731870⟩ E))) ⟨105361018880,1468328677⟩ (N (N (N E ⟨105361019008,1460971898⟩ E) ⟨105361019136,1453661183⟩ (N E ⟨105361019392,1439176564⟩ E)) ⟨105361019648,1424872090⟩ (N (N E ⟨105361019776,1417786566⟩ E) ⟨105361020032,1403747289⟩ (N E ⟨105361020416,1383012918⟩ E)))) ⟨105361020544,1376186724⟩ (N (N (N (N E ⟨105361021056,1349299902⟩ E) ⟨105361021312,1336102965⟩ (N E ⟨105361022208,1291167028⟩ E)) ⟨105361022976,1254146509⟩ (N (N E ⟨105495235712,1791735219⟩ E) ⟨105495235840,1782678246⟩ (N E ⟨105495235968,1773678488⟩ E))) ⟨105495236096,1764735511⟩ (N (N (N E ⟨105495236224,1755848885⟩ E) ⟨105495236352,1747018185⟩ (N E ⟨105495236480,1738242987⟩ E)) ⟨105495236608,1729522875⟩ (N (N E ⟨105495236736,1720857432⟩ E) ⟨105495236992,1703688913⟩ (N E ⟨105495237248,1686734186⟩ E)))))) ⟨105495237376,1678335996⟩ (N (N (N (N (N (N E ⟨105495237504,1669990061⟩ E) ⟨105495237760,1653453401⟩ (N E ⟨105495238272,1620990215⟩ E)) ⟨105495238656,1597164902⟩ (N (N E ⟨105495239936,1520846759⟩ E) ⟨105629453568,2074088812⟩ (N E ⟨105629453696,2063617883⟩ E))) ⟨105629453824,2053213016⟩ (N (N (N E ⟨105629453952,2042873713⟩ E) ⟨105629454080,2032599477⟩ (N E ⟨105629454208,2022389817⟩ E)) ⟨105629454336,2012244247⟩ (N (N E ⟨105629454464,2002162282⟩ E) ⟨105629454592,1992143446⟩ (N E ⟨105629454848,1972293265⟩ E)))) ⟨105629454976,1962460984⟩ (N (N (N (N E ⟨105629455104,1952689959⟩ E) ⟨105629455232,1942979732⟩ (N E ⟨105629455360,1933329849⟩ E)) ⟨105629455616,1914209321⟩ (N (N E ⟨105629455872,1895324820⟩ E) ⟨105629456000,1885969988⟩ (N E ⟨105629456128,1876672858⟩ E))) ⟨105629456256,1867433004⟩ (N (N (N E ⟨105629456384,1858250002⟩ E) ⟨105629456512,1849123433⟩ (N E ⟨105629456640,1840052880⟩ E)) ⟨105629456896,1822078178⟩ (N (N E ⟨105629457024,1813173215⟩ E) ⟨105629457280,1795526053⟩ (N E ⟨105629457664,1769456296⟩ E))))) ⟨105629457792,1760871750⟩ (N (N (N (N (N E ⟨105629458048,1743858420⟩ E) ⟨105629458432,1718722202⟩ (N E ⟨105763671296,2387672593⟩ E)) ⟨105763671552,2363640563⟩ (N (N E ⟨105763671680,2351738049⟩ E) ⟨105763671808,2339910440⟩ (N E ⟨105763672064,2316477679⟩ E))) ⟨105763672192,2304871412⟩ (N (N (N E ⟨105763672960,2236740986⟩ E) ⟨105763673728,2171111876⟩ (N E ⟨105763676160,1978577712⟩ E)) ⟨105897889152,2709651032⟩ (N (N E ⟨105897889280,2695988834⟩ E) ⟨105897889408,2682412724⟩ (N E ⟨105897889536,2668922051⟩ E)))) ⟨105897889664,2655516170⟩ (N (N (N (N E ⟨105897889792,2642194442⟩ E) ⟨105897889920,2628956233⟩ (N E ⟨105897890048,2615800915⟩ E)) ⟨105897890176,2602727864⟩ (N (N E ⟨105897890304,2589736465⟩ E) ⟨105897890432,2576826105⟩ (N E ⟨105897890560,2563996177⟩ E))) ⟨105897890688,2551246081⟩ (N (N (N E ⟨105897890944,2525983004⟩ E) ⟨105897891072,2513468848⟩ (N E ⟨105897891456,2476388951⟩ E)) ⟨105897891584,2464181276⟩ (N (N E ⟨105897891840,2439990988⟩ E) ⟨105897892224,2404259947⟩ (N E ⟨105897892352,2392495267⟩ E))))))))

noncomputable def tab5 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨105897892736,2357630773⟩ E) ⟨105897893888,2256782822⟩ E) ⟨106032107136,3034854700⟩ (N E ⟨106032107264,3019591488⟩ E)) ⟨106032107392,3004424210⟩ (N (N E ⟨106032107520,2989352141⟩ E) ⟨106032107648,2974374565⟩ (N E ⟨106032107776,2959490771⟩ E))) ⟨106032107904,2944700053⟩ (N (N (N E ⟨106032108032,2930001715⟩ E) ⟨106032108160,2915395064⟩ (N E ⟨106032108288,2900879413⟩ E)) ⟨106032108416,2886454083⟩ (N (N E ⟨106032108800,2843713302⟩ E) ⟨106032109184,2801761481⟩ (N E ⟨106032109312,2787949840⟩ E)))) ⟨106032109696,2747022933⟩ (N (N (N (N E ⟨106032110080,2706845013⟩ E) ⟨106032110848,2628670937⟩ (N E ⟨106032111616,2553301322⟩ E)) ⟨106166324992,3391862090⟩ (N (N E ⟨106166325120,3374824912⟩ E) ⟨106166325248,3357894682⟩ (N E ⟨106166325504,3324351850⟩ E))) ⟨106166325632,3307737658⟩ (N (N (N E ⟨106166326144,3242310828⟩ E) ⟨106166326400,3210204655⟩ (N E ⟨106166326784,3162787592⟩ E)) ⟨106166327808,3040558638⟩ (N (N E ⟨106300542976,3747752238⟩ E) ⟨106300543104,3728974843⟩ (N E ⟨106300543232,3710315023⟩ E))))) ⟨106300543360,3691771894⟩ (N (N (N (N (N E ⟨106300543488,3673344580⟩ E) ⟨106300543616,3655032214⟩ (N E ⟨106300543744,3636833936⟩ E)) ⟨106300543872,3618748892⟩ (N (N E ⟨106300544128,3582915136⟩ E) ⟨106300544256,3565164754⟩ (N E ⟨106300544384,3547524270⟩ E))) ⟨106300544640,3512569736⟩ (N (N (N E ⟨106300545024,3460941988⟩ E) ⟨106300545152,3443943991⟩ (N E ⟨106300545408,3410260219⟩ E)) ⟨106300545792,3360503687⟩ (N (N E ⟨106300546688,3247890661⟩ E) ⟨106300546816,3232190868⟩ (N E ⟨106300547072,3201075113⟩ E)))) ⟨106434760832,4138004154⟩ (N (N (N (N E ⟨106434760960,4117297548⟩ E) ⟨106434761216,4076271836⟩ (N E ⟨106434761344,4055950796⟩ E)) ⟨106434761472,4035756358⟩ (N (N E ⟨106434761600,4015687576⟩ E) ⟨106434761728,3995743510⟩ (N E ⟨106434761856,3975923233⟩ E))) ⟨106434761984,3956225821⟩ (N (N (N E ⟨106434762240,3917195948⟩ E) ⟨106434762368,3897861683⟩ (N E ⟨106434762496,3878646676⟩ E)) ⟨106434762624,3859550045⟩ (N (N E ⟨106434763008,3802961692⟩ E) ⟨106434763264,3765812161⟩ (N E ⟨106434763648,3710935089⟩ E)))))) ⟨106434764160,3639312697⟩ (N (N (N (N (N (N E ⟨106434764416,3604150098⟩ E) ⟨106434764800,3552199377⟩ (N E ⟨106568978688,4545203054⟩ E)) ⟨106568978816,4522487385⟩ (N (N E ⟨106568978944,4499913592⟩ E) ⟨106568979200,4455187392⟩ (N E ⟨106568979328,4433032887⟩ E))) ⟨106568979584,4389135886⟩ (N (N (N E ⟨106568979712,4367391348⟩ E) ⟨106568979968,4324305150⟩ (N E ⟨106568980224,4281749501⟩ E)) ⟨106568980352,4260668180⟩ (N (N E ⟨106568980608,4218893720⟩ E) ⟨106568980864,4177630489⟩ (N E ⟨106568981376,4096607861⟩ E)))) ⟨106568981632,4056833852⟩ (N (N (N (N E ⟨106568981760,4037128038⟩ E) ⟨106568982272,3959492311⟩ (N E ⟨106568982400,3940375961⟩ E)) ⟨106568982528,3921374948⟩ (N (N E ⟨106703196800,4919513303⟩ E) ⟨106703196928,4895019217⟩ (N E ⟨106703197056,4870677540⟩ E))) ⟨106703197312,4822446873⟩ (N (N (N E ⟨106703197440,4798555637⟩ E) ⟨106703197824,4727765046⟩ (N E ⟨106703198208,4658276357⟩ E)) ⟨106703198336,4635397799⟩ (N (N E ⟨106703198720,4567600534⟩ E) ⟨106703200256,4308506924⟩ (N E ⟨106837414656,5355130656⟩ E))))) ⟨106837414912,5302036761⟩ (N (N (N (N (N E ⟨106837415040,5275736814⟩ E) ⟨106837415424,5197810335⟩ (N E ⟨106837415552,5172155289⟩ E)) ⟨106837415680,5146658489⟩ (N (N E ⟨106837415936,5096134953⟩ E) ⟨106837416320,5021507545⟩ (N E ⟨106837416704,4948242519⟩ E))) ⟨106837416832,4924118429⟩ (N (N (N E ⟨106837417600,4782423161⟩ E) ⟨106837417984,4713488648⟩ (N E ⟨106971632512,5806369308⟩ E)) ⟨106971632640,5777531754⟩ (N (N E ⟨106971632768,5748873187⟩ E) ⟨106971632896,5720392275⟩ (N E ⟨106971633152,5663958139⟩ E)))) ⟨106971633280,5636002308⟩ (N (N (N (N E ⟨106971633408,5608218915⟩ E) ⟨106971633792,5525890656⟩ (N E ⟨106971634176,5445069055⟩ E)) ⟨106971634944,5287814671⟩ (N (N E ⟨106971635712,5136201722⟩ E) ⟨107105850624,6210787836⟩ (N E ⟨107105851008,6119163319⟩ E))) ⟨107105851520,5999612058⟩ (N (N (N E ⟨107105852288,5825711562⟩ E) ⟨107105852672,5741126388⟩ (N E ⟨107105853184,5630722032⟩ E)) ⟨107240068480,6687374875⟩ (N (N E ⟨107240069120,6524160155⟩ E) ⟨107240069376,6460271584⟩ (N E ⟨107240069888,6334825702⟩ E))))))) ⟨107240070016,6303941624⟩ (N (N (N (N (N (N (N E ⟨107240070400,6212412891⟩ E) ⟨107240071168,6034289734⟩ (N E ⟨107374286720,7072586365⟩ E)) ⟨107374287360,6900812643⟩ (N (N E ⟨107374287744,6800250964⟩ E) ⟨107374288256,6669003657⟩ (N E ⟨107374288512,6604568550⟩ E))) ⟨107374288640,6572643104⟩ (N (N (N E ⟨107374288896,6509369379⟩ E) ⟨107508504960,7459132497⟩ (N E ⟨107508506240,7103987736⟩ E)) ⟨107508506624,7001589868⟩ (N (N E ⟨107642723072,7884846377⟩ E) ⟨107642723968,7620619198⟩ (N E ⟨107642724352,7510774532⟩ E)))) ⟨107776941312,8273967539⟩ (N (N (N (N E ⟨107776942080,8036735203⟩ E) ⟨107911159808,8579272269⟩ (N E ⟨108045377280,9227001531⟩ E)) ⟨108045377536,9138174746⟩ (N (N E ⟨108179595264,9713220361⟩ E) ⟨108313812992,10304175640⟩ (N E ⟨108448030720,10910796006⟩ E))) ⟨108582248448,11532825879⟩ (N (N (N E ⟨108716464896,12776121886⟩ E) ⟨108716466176,12169998792⟩ (N E ⟨109119119360,14169550279⟩ E)) ⟨109521772544,16294777226⟩ (N (N E ⟨109790208000,17777062538⟩ E) ⟨110192861184,20091624210⟩ (N E ⟨110461296640,21691026364⟩ E))))) ⟨111669256320,29210021225⟩ (N (N (N (N (N E ⟨111669256576,28929837604⟩ E) ⟨111669256704,28791006768⟩ (N E ⟨111669256960,28515836841⟩ E)) ⟨111669257088,28379485819⟩ (N (N E ⟨111669257216,28243949556⟩ E) ⟨111669257344,28109222210⟩ (N E ⟨111669257472,27975297990⟩ E))) ⟨111669257728,27709835999⟩ (N (N (N E ⟨111669257856,27578286886⟩ E) ⟨111669257984,27447518209⟩ (N E ⟨111669258240,27188299995⟩ E)) ⟨111669258368,27059839487⟩ (N (N E ⟨111669258624,26805188577⟩ E) ⟨111669258752,26678987475⟩ (N E ⟨111669258880,26553528882⟩ E)))) ⟨111669259008,26428807555⟩ (N (N (N (N E ⟨111669259136,26304818298⟩ E) ⟨111669259264,26181555955⟩ (N E ⟨111669259520,25937191605⟩ E)) ⟨111669259648,25816079498⟩ (N (N E ⟨111669259904,25575970478⟩ E) ⟨111669260032,25456963711⟩ (N E ⟨111669260288,25221021330⟩ E))) ⟨111669260416,25104076101⟩ (N (N (N E ⟨111669260544,24987808501⟩ E) ⟨111669260800,24757287385⟩ (N E ⟨111669261184,24416471402⟩ E)) ⟨111669261568,24081505030⟩ (N (N E ⟨111669261952,23752268098⟩ E) ⟨111669262080,23643775309⟩ (N E ⟨111669262336,23428643310⟩ E)))))) ⟨111669262848,23005676080⟩ (N (N (N (N (N (N E ⟨111669263232,22694705692⟩ E) ⟨111669263616,22388976217⟩ (N E ⟨111669263872,22188015873⟩ E)) ⟨111669264384,21792819594⟩ (N (N E ⟨112743006208,27176325579⟩ E) ⟨113414094848,30611303246⟩ (N E ⟨114890487808,40944904897⟩ E))) ⟨116232667136,44423594319⟩ (N (N (N E ⟨118111715328,51817339464⟩ E) ⟨119185457152,54949008951⟩ (N E ⟨120259199104,56844414277⟩ E)) ⟨120259199488,55960566098⟩ (N (N E ⟨120259199872,54943403955⟩ E) ⟨120259201536,49177312645⟩ (N E ⟨120259202432,45325013956⟩ E)))) ⟨120259203072,42337514840⟩ (N (N (N (N E ⟨120259204608,34656897120⟩ E) ⟨120259206528,24808899974⟩ (N E ⟨120259207168,21644686635⟩ E)) ⟨123748868096,24017847370⟩ (N (N E ⟨124554173440,30223324776⟩ E) ⟨124554174464,24570887349⟩ (N E ⟨125627916288,25306100736⟩ E))) ⟨126164787200,25671723688⟩ (N (N (N E ⟨127775399936,26755041422⟩ E) ⟨127909617664,26844133108⟩ (N E ⟨128178053120,27021662065⟩ E)) ⟨128849141888,26708226219⟩ (N (N E ⟨128849142272,24485611157⟩ E) ⟨128849143808,16289029010⟩ (N E ⟨128849144064,15052086325⟩ E))))) ⟨128849144320,13857021829⟩ (N (N (N (N (N E ⟨128849144960,11062741126⟩ E) ⟨128849145088,10538428373⟩ (N E ⟨128849145344,9525580614⟩ E)) ⟨128849145984,7208155569⟩ (N (N E ⟨128849146368,5969173862⟩ E) ⟨128849146496,5581931705⟩ (N E ⟨128849146624,5207672845⟩ E))) ⟨128849146752,4846449863⟩ (N (N (N E ⟨128849146880,4498307474⟩ E) ⟨128849147520,2954823681⟩ (N E ⟨128849147776,2429690184⟩ E)) ⟨128849148160,1740614904⟩ (N (N E ⟨128849148288,1537105649⟩ E) ⟨128849148416,1346617606⟩ (N E ⟨128849149696,142934785⟩ E)))) ⟨128849149952,50445805⟩ (N (N (N (N E ⟨129117583872,1364111067⟩ E) ⟨129386014720,16512765956⟩ (N E ⟨129386020864,55390359⟩ E)) ⟨129788672128,2034921410⟩ (N (N E ⟨129788673920,102542944⟩ E) ⟨130057105920,6193097978⟩ (N E ⟨130057107456,2294124330⟩ E))) ⟨130057107712,1832152454⟩ (N (N (N E ⟨130057109248,162390558⟩ E) ⟨130057109504,61498544⟩ (N E ⟨130459759232,5863119375⟩ E)) ⟨130459760000,3732371154⟩ (N (N E ⟨130459760896,1861338617⟩ E) ⟨130459761408,1087927839⟩ (N E ⟨130593976320,8034099532⟩ E))))))))

noncomputable def tab6 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨130593978624,1870903814⟩ E) ⟨130996628992,10088336288⟩ E) ⟨130996630528,4812633024⟩ (N E ⟨130996633600,69750581⟩ E)) ⟨131130846848,9609015681⟩ (N (N E ⟨131130848256,4831140569⟩ E) ⟨131265066112,4494637522⟩ (N E ⟨131265067392,1699413448⟩ E))) ⟨131265069056,72014168⟩ (N (N (N E ⟨131399282432,9169745826⟩ E) ⟨131399283456,5620512261⟩ (N E ⟨131533502080,3238517398⟩ E)) ⟨131533503488,821321555⟩ (N (N E ⟨131667719296,4545653664⟩ E) ⟨131667719424,4201423243⟩ (N E ⟨131667720192,2425841763⟩ E)))) ⟨131667720448,1944224752⟩ (N (N (N (N E ⟨131667721216,826144878⟩ E) ⟨131667721600,447610588⟩ (N E ⟨131667721984,186129097⟩ E)) ⟨131667722112,124453304⟩ (N (N E ⟨131801937408,3568122192⟩ E) ⟨131801939968,76380134⟩ (N E ⟨131936155264,3277114027⟩ E))) ⟨131936155904,1961602711⟩ (N (N (N E ⟨131936156416,1156702295⟩ E) ⟨131936157440,189749361⟩ (N E ⟨132204590592,3608632501⟩ E)) ⟨132204591360,1978573199⟩ (N (N E ⟨132338808448,3314513400⟩ E) ⟨132338809216,1763026526⟩ (N E ⟨132338810112,578456838⟩ E))))) ⟨132338810752,131395736⟩ (N (N (N (N (N E ⟨132338810880,80496339⟩ E) ⟨132473025664,4643480599⟩ (N E ⟨132473026560,2485924245⟩ E)) ⟨132473026944,1770543270⟩ (N (N E ⟨132607242496,7505860270⟩ E) ⟨132607243264,5024304284⟩ (N E ⟨132607244288,2495523884⟩ E))) ⟨132741460864,5420902248⟩ (N (N (N E ⟨132741462400,1785270441⟩ E) ⟨132875681024,591713365⟩ (N E ⟨132875681408,279375787⟩ E)) ⟨133009896960,3685730487⟩ (N (N E ⟨133009897728,2026914939⟩ E) ⟨133009898240,1200970767⟩ (N E ⟨133009898496,870752307⟩ E)))) ⟨133009898624,726068132⟩ (N (N (N (N E ⟨133009899264,203040122⟩ E) ⟨133009899520,85230236⟩ (N E ⟨133144115584,1806574257⟩ E)) ⟨133278333440,1598783991⟩ (N (N E ⟨133278333568,1398048695⟩ E) ⟨133278333696,1211191626⟩ (N E ⟨133278334208,601035112⟩ E))) ⟨133278334592,284989919⟩ (N (N (N E ⟨133278334848,140077613⟩ E) ⟨133278334976,86981035⟩ (N E ⟨133412549632,5120902355⟩ E)) ⟨133412550656,2550487919⟩ (N (N E ⟨133412552704,87823684⟩ E) ⟨133546769280,1046930430⟩ (N E ⟨133546769408,886594086⟩ E)))))) ⟨133546770176,208892132⟩ (N (N (N (N (N (N E ⟨133546770304,142309435⟩ E) ⟨133680986368,2064080127⟩ (N E ⟨133680986752,1414398270⟩ E)) ⟨133680987264,743260291⟩ (N (N E ⟨133680987392,609797909⟩ E) ⟨133680988160,89440943⟩ (N E ⟨133815204096,2071156309⟩ E))) ⟨133815204480,1419650546⟩ (N (N (N E ⟨133815204864,894053282⟩ E) ⟨133815205248,492263255⟩ (N E ⟨133815205504,291885065⟩ E)) ⟨133815205632,211601557⟩ (N (N E ⟨133815205760,144422286⟩ E) ⟨133815205888,90214579⟩ (N E ⟨133949422720,749642439⟩ E)))) ⟨133949423488,145432769⟩ (N (N (N (N E ⟨133949423616,90964259⟩ E) ⟨134083639552,2084941570⟩ (N E ⟨134083639808,1634080396⟩ E)) ⟨134083640576,617979164⟩ (N (N E ⟨134083640704,496860385⟩ E) ⟨134083641088,214160295⟩ (N E ⟨134083641344,91689533⟩ E))) ⟨134217857280,2091648218⟩ (N (N (N E ⟨134217857536,1639584925⟩ E) ⟨134217857664,1434799465⟩ (N E ⟨134217857792,1244096045⟩ E)) ⟨134217858048,904644104⟩ (N (N E ⟨134217858304,620573348⟩ E) ⟨134217858432,499069489⟩ (N E ⟨134217858560,391113173⟩ E))))) ⟨134217859072,92389963⟩ (N (N (N (N (N E ⟨134352076544,216563947⟩ E) ⟨134486293248,1252643901⟩ (N E ⟨134486293632,761521358⟩ E)) ⟨134486294272,217706316⟩ (N (N E ⟨134486294528,93714619⟩ E) ⟨134620510976,1256770849⟩ (N E ⟨134620511488,627946919⟩ E))) ⟨134620511616,505330842⟩ (N (N (N E ⟨134620511744,396346399⟩ E) ⟨134620512000,218808388⟩ (N E ⟨134620512256,94338048⟩ E)) ⟨134754729216,630266148⟩ (N (N E ⟨134754729344,507293842⟩ E) ⟨134754729856,150821679⟩ (N E ⟨134754729984,94935037⟩ E)))) ⟨134888946432,1264726435⟩ (N (N (N (N E ⟨134888946944,632514968⟩ E) ⟨134888947712,95505228⟩ (N E ⟨135023164160,1268553414⟩ E)) ⟨135023164416,923589843⟩ (N (N E ⟨135023164544,772179014⟩ E) ⟨135023164672,634692757⟩ (N E ⟨135023164928,401082838⟩ E))) ⟨135023165184,221868200⟩ (N (N (N E ⟨135023165440,96048277⟩ E) ⟨135157382272,774647354⟩ (N E ⟨135157382400,636798914⟩ E)) ⟨135157382528,512802130⟩ (N (N E ⟨135157382784,305923547⟩ E) ⟨135157383040,153063066⟩ (N E ⟨135157383168,96563856⟩ E))))))) ⟨135291600896,97051656⟩ (N (N (N (N (N (N (N E ⟨135425817728,779344307⟩ E) ⟨135425817856,640794050⟩ (N E ⟨135425817984,516151583⟩ E)) ⟨135425818112,405308227⟩ (N (N E ⟨135425818368,224549458⟩ E) ⟨135425818496,154382392⟩ (N E ⟨135425818624,97511382⟩ E))) ⟨135560035456,781571749⟩ (N (N (N E ⟨135560035584,642681946⟩ E) ⟨135560035712,517727960⟩ (N E ⟨135560035968,309184911⟩ E)) ⟨135560036096,225357276⟩ (N (N E ⟨135560036224,154988567⟩ E) ⟨135560036352,97942758⟩ (N E ⟨135694253568,407834962⟩ E)))) ⟨135694253696,310170411⟩ (N (N (N (N E ⟨135694254080,98345523⟩ E) ⟨135828471040,646235871⟩ (N E ⟨135828471296,409010007⟩ E)) ⟨135828471424,311104482⟩ (N (N E ⟨135828471552,226841938⟩ E) ⟨135828471808,98719435⟩ (N E ⟨135962688640,787763454⟩ E))) ⟨135962688768,647900962⟩ (N (N (N E ⟨135962688896,522058204⟩ E) ⟨135962689024,410125657⟩ (N E ⟨135962689152,311986785⟩ E)) ⟨135962689280,227518160⟩ (N (N E ⟨135962689408,156589595⟩ E) ⟨135962689536,99064269⟩ (N E ⟨136096906624,523367265⟩ E))))) ⟨136096906752,411181557⟩ (N (N (N (N (N E ⟨136096906880,312817000⟩ E) ⟨136096907008,228149927⟩ (N E ⟨136096907264,99379817⟩ E)) ⟨136231124352,524608512⟩ (N (N E ⟨136231124480,412177373⟩ E) ⟨136231124608,313594832⟩ (N E ⟨136231124864,157473116⟩ E))) ⟨136231124992,99665889⟩ (N (N (N E ⟨136365342336,314320003⟩ E) ⟨136365342464,229279073⟩ (N E ⟨136365342720,99922313⟩ E)) ⟨136499559936,413987531⟩ (N (N E ⟨136499560064,314992258⟩ E) ⟨136499560192,229775989⟩ (N E ⟨136499560320,158207513⟩ E)))) ⟨136499560448,100148933⟩ (N (N (N (N E ⟨136633777792,315611365⟩ E) ⟨136633777920,230227527⟩ (N E ⟨136633778048,158518332⟩ E)) ⟨136633778176,100345615⟩ (N (N E ⟨136767995648,230633505⟩ E) ⟨136767995776,158791360⟩ (N E ⟨136767995904,100512239⟩ E))) ⟨136902213504,159026466⟩ (N (N (N E ⟨136902213632,100648704⟩ E) ⟨137036431360,100754930⟩ (N E ⟨137170649088,100830851⟩ E)) ⟨137304866816,100876421⟩ (N (N E ⟨137439084672,55697681⟩ E) ⟨137439084800,23869645⟩ (N E ⟨137439084928,5347966⟩ E)))))) ⟨137975956608,64174⟩ (N (N (N (N (N (N E ⟨137975956736,63925⟩ E) ⟨137975956864,63678⟩ (N E ⟨137975956992,63431⟩ E)) ⟨137975957120,63186⟩ (N (N E ⟨137975957248,62942⟩ E) ⟨137975957376,62700⟩ (N E ⟨137975957504,62458⟩ E))) ⟨137975957632,62218⟩ (N (N (N E ⟨137975957760,61978⟩ E) ⟨137975957888,61740⟩ (N E ⟨137975958016,61503⟩ E)) ⟨137975958144,61268⟩ (N (N E ⟨137975958272,61033⟩ E) ⟨137975958400,60799⟩ (N E ⟨137975958528,60567⟩ E)))) ⟨137975958656,60336⟩ (N (N (N (N E ⟨137975958784,60105⟩ E) ⟨137975958912,59876⟩ (N E ⟨137975959040,59648⟩ E)) ⟨137975959168,59421⟩ (N (N E ⟨137975959424,58971⟩ E) ⟨137975959552,58747⟩ (N E ⟨137975959808,58303⟩ E))) ⟨137975959936,58082⟩ (N (N (N E ⟨137975960064,57863⟩ E) ⟨137975960192,57644⟩ (N E ⟨137975960448,57210⟩ E)) ⟨137975960576,56995⟩ (N (N E ⟨137975960704,56780⟩ E) ⟨137975961088,56143⟩ (N E ⟨137975961216,55933⟩ E))))) ⟨137975961600,55308⟩ (N (N (N (N (N E ⟨137975961856,54896⟩ E) ⟨137975961984,54691⟩ (N E ⟨137975962240,54285⟩ E)) ⟨137975962368,54083⟩ (N (N E ⟨137975963520,52309⟩ E) ⟨137975963648,52116⟩ (N E ⟨138110174464,7794156⟩ E))) ⟨138110174592,7763984⟩ (N (N (N E ⟨138110174720,7733958⟩ E) ⟨138110174848,7704077⟩ (N E ⟨138110174976,7674340⟩ E)) ⟨138110175104,7644747⟩ (N (N E ⟨138110175232,7615296⟩ E) ⟨138110175360,7585987⟩ (N E ⟨138110175488,7556819⟩ E)))) ⟨138110175616,7527791⟩ (N (N (N (N E ⟨138110175744,7498902⟩ E) ⟨138110175872,7470152⟩ (N E ⟨138110176000,7441540⟩ E)) ⟨138110176128,7413064⟩ (N (N E ⟨138110176256,7384725⟩ E) ⟨138110176384,7356521⟩ (N E ⟨138110176512,7328452⟩ E))) ⟨138110176640,7300517⟩ (N (N (N E ⟨138110176768,7272714⟩ E) ⟨138110176896,7245044⟩ (N E ⟨138110177024,7217506⟩ E)) ⟨138110177152,7190098⟩ (N (N E ⟨138110177280,7162820⟩ E) ⟨138110177408,7135672⟩ (N E ⟨138110177536,7108652⟩ E))))))))

noncomputable def tab7 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨138110177920,7028357⟩ E) ⟨138110178048,7001844⟩ E) ⟨138110178432,6923053⟩ (N E ⟨138110178560,6897036⟩ E)) ⟨138110178816,6845367⟩ (N (N E ⟨138110179200,6768769⟩ E) ⟨138110179328,6743475⟩ (N E ⟨138110179584,6693240⟩ E))) ⟨138110179712,6668298⟩ (N (N (N E ⟨138110180480,6521062⟩ E) ⟨138110180608,6496920⟩ (N E ⟨138110180864,6448970⟩ E)) ⟨138110180992,6425160⟩ (N (N E ⟨138110181248,6377871⟩ E) ⟨138110181376,6354389⟩ (N E ⟨138244392320,28354691⟩ E)))) ⟨138244392448,28245033⟩ (N (N (N (N E ⟨138244392576,28135904⟩ E) ⟨138244392704,28027303⟩ (N E ⟨138244392832,27919226⟩ E)) ⟨138244392960,27811669⟩ (N (N E ⟨138244393088,27704630⟩ E) ⟨138244393216,27598106⟩ (N E ⟨138244393344,27492093⟩ E))) ⟨138244393472,27386590⟩ (N (N (N E ⟨138244393600,27281592⟩ E) ⟨138244393728,27177098⟩ (N E ⟨138244393856,27073103⟩ E)) ⟨138244393984,26969606⟩ (N (N E ⟨138244394112,26866603⟩ E) ⟨138244394240,26764092⟩ (N E ⟨138244394368,26662069⟩ E))))) ⟨138244394496,26560533⟩ (N (N (N (N (N E ⟨138244394624,26459480⟩ E) ⟨138244394752,26358907⟩ (N E ⟨138244394880,26258811⟩ E)) ⟨138244395008,26159191⟩ (N (N E ⟨138244395136,26060043⟩ E) ⟨138244395392,25863153⟩ (N E ⟨138244395520,25765406⟩ E))) ⟨138244395648,25668120⟩ (N (N (N E ⟨138244395904,25474923⟩ E) ⟨138244396032,25379006⟩ (N E ⟨138244396160,25283541⟩ E)) ⟨138244396544,24999828⟩ (N (N E ⟨138244396672,24906142⟩ E) ⟨138244396800,24812895⟩ (N E ⟨138244396928,24720085⟩ E)))) ⟨138244397696,24172246⟩ (N (N (N (N E ⟨138244398464,23639509⟩ E) ⟨138244398720,23465199⟩ (N E ⟨138244399104,23206737⟩ E)) ⟨138378610176,61658446⟩ (N (N E ⟨138378610304,61420221⟩ E) ⟨138378610432,61183146⟩ (N E ⟨138378610560,60947215⟩ E))) ⟨138378610688,60712420⟩ (N (N (N E ⟨138378610816,60478756⟩ E) ⟨138378610944,60246216⟩ (N E ⟨138378611072,60014792⟩ E)) ⟨138378611200,59784480⟩ (N (N E ⟨138378611328,59555272⟩ E) ⟨138378611456,59327162⟩ (N E ⟨138378611584,59100144⟩ E)))))) ⟨138378611712,58874211⟩ (N (N (N (N (N (N E ⟨138378611840,58649357⟩ E) ⟨138378611968,58425577⟩ (N E ⟨138378612096,58202864⟩ E)) ⟨138378612224,57981211⟩ (N (N E ⟨138378612352,57760613⟩ E) ⟨138378612480,57541064⟩ (N E ⟨138378612608,57322558⟩ E))) ⟨138378612736,57105088⟩ (N (N (N E ⟨138378612864,56888649⟩ E) ⟨138378612992,56673236⟩ (N E ⟨138378613120,56458842⟩ E)) ⟨138378613248,56245461⟩ (N (N E ⟨138378613504,55821716⟩ E) ⟨138378613632,55611342⟩ (N E ⟨138378613888,55193558⟩ E)))) ⟨138378614272,54574216⟩ (N (N (N (N E ⟨138378614400,54369703⟩ E) ⟨138378614528,54166146⟩ (N E ⟨138378614656,53963542⟩ E)) ⟨138378614784,53761885⟩ (N (N E ⟨138378615168,53162543⟩ E) ⟨138378615552,52571534⟩ (N E ⟨138378616832,50659929⟩ E))) ⟨138512828032,107610860⟩ (N (N (N E ⟨138512828160,107195495⟩ E) ⟨138512828288,106782133⟩ (N E ⟨138512828416,106370763⟩ E)) ⟨138512828544,105961373⟩ (N (N E ⟨138512828672,105553952⟩ E) ⟨138512828800,105148488⟩ (N E ⟨138512828928,104744971⟩ E))))) ⟨138512829056,104343389⟩ (N (N (N (N (N E ⟨138512829184,103943730⟩ E) ⟨138512829312,103545985⟩ (N E ⟨138512829440,103150141⟩ E)) ⟨138512829568,102756188⟩ (N (N E ⟨138512829696,102364115⟩ E) ⟨138512829824,101973911⟩ (N E ⟨138512829952,101585567⟩ E))) ⟨138512830080,101199070⟩ (N (N (N E ⟨138512830208,100814410⟩ E) ⟨138512830336,100431578⟩ (N E ⟨138512830464,100050562⟩ E)) ⟨138512830592,99671352⟩ (N (N E ⟨138512830720,99293938⟩ E) ⟨138512830848,98918310⟩ (N E ⟨138512830976,98544458⟩ E)))) ⟨138512831232,97802040⟩ (N (N (N (N E ⟨138512831360,97433454⟩ E) ⟨138512831488,97066604⟩ (N E ⟨138512831616,96701480⟩ E)) ⟨138512831744,96338072⟩ (N (N E ⟨138512831872,95976371⟩ E) ⟨138512832000,95616366⟩ (N E ⟨138512832128,95258049⟩ E))) ⟨138512832256,94901410⟩ (N (N (N E ⟨138512832384,94546439⟩ E) ⟨138512832512,94193128⟩ (N E ⟨138512832640,93841466⟩ E)) ⟨138512832768,93491444⟩ (N (N E ⟨138512832896,93143054⟩ E) ⟨138512833152,92451132⟩ (N E ⟨138512833280,92107581⟩ E))))))) ⟨138512833408,91765626⟩ (N (N (N (N (N (N (N E ⟨138512833664,91086466⟩ E) ⟨138512833792,90749243⟩ (N E ⟨138512833920,90413581⟩ E)) ⟨138512834176,89746901⟩ (N (N E ⟨138512834304,89415867⟩ E) ⟨138512834432,89086358⟩ (N E ⟨138512834560,88758367⟩ E))) ⟨138647045760,166753871⟩ (N (N (N E ⟨138647045888,166110220⟩ E) ⟨138647046016,165469675⟩ (N E ⟨138647046144,164832215⟩ E)) ⟨138647046272,164197824⟩ (N (N E ⟨138647046400,163566485⟩ E) ⟨138647046528,162938178⟩ (N E ⟨138647046656,162312887⟩ E)))) ⟨138647046784,161690595⟩ (N (N (N (N E ⟨138647046912,161071284⟩ E) ⟨138647047040,160454937⟩ (N E ⟨138647047168,159841537⟩ E)) ⟨138647047296,159231067⟩ (N (N E ⟨138647047424,158623511⟩ E) ⟨138647047552,158018851⟩ (N E ⟨138647047680,157417072⟩ E))) ⟨138647047808,156818156⟩ (N (N (N E ⟨138647047936,156222087⟩ E) ⟨138647048064,155628850⟩ (N E ⟨138647048192,155038427⟩ E)) ⟨138647048320,154450803⟩ (N (N E ⟨138647048448,153865963⟩ E) ⟨138647048576,153283889⟩ (N E ⟨138647048704,152704567⟩ E))))) ⟨138647048832,152127981⟩ (N (N (N (N (N E ⟨138647048960,151554116⟩ E) ⟨138647049088,150982955⟩ (N E ⟨138647049216,150414484⟩ E)) ⟨138647049344,149848687⟩ (N (N E ⟨138647049600,148725058⟩ E) ⟨138647049728,148167195⟩ (N E ⟨138647049856,147611946⟩ E))) ⟨138647049984,147059298⟩ (N (N (N E ⟨138647050240,145961743⟩ E) ⟨138647050368,145416807⟩ (N E ⟨138647050496,144874414⟩ E)) ⟨138647051136,142200085⟩ (N (N E ⟨138647051264,141672649⟩ E) ⟨138647052032,138558896⟩ (N E ⟨138647052160,138048289⟩ E)))) ⟨138647052288,137540034⟩ (N (N (N (N E ⟨138781263616,237965386⟩ E) ⟨138781263744,237047756⟩ (N E ⟨138781263872,236134548⟩ E)) ⟨138781264000,235225735⟩ (N (N E ⟨138781264128,234321293⟩ E) ⟨138781264256,233421197⟩ (N E ⟨138781264384,232525421⟩ E))) ⟨138781264512,231633940⟩ (N (N (N E ⟨138781264640,230746731⟩ E) ⟨138781264768,229863767⟩ (N E ⟨138781264896,228985026⟩ E)) ⟨138781265024,228110482⟩ (N (N E ⟨138781265152,227240112⟩ E) ⟨138781265280,226373891⟩ (N E ⟨138781265408,225511797⟩ E)))))) ⟨138781265536,224653805⟩ (N (N (N (N (N (N E ⟨138781265664,223799892⟩ E) ⟨138781265792,222950034⟩ (N E ⟨138781265920,222104209⟩ E)) ⟨138781266048,221262394⟩ (N (N E ⟨138781266176,220424566⟩ E) ⟨138781266304,219590702⟩ (N E ⟨138781266432,218760780⟩ E))) ⟨138781266560,217934777⟩ (N (N (N E ⟨138781266688,217112671⟩ E) ⟨138781266944,215480063⟩ (N E ⟨138781267072,214669517⟩ E)) ⟨138781267328,213059833⟩ (N (N E ⟨138781267456,212260652⟩ E) ⟨138781267968,209101176⟩ (N E ⟨138781268224,207543496⟩ E)))) ⟨138781268352,206770098⟩ (N (N (N (N E ⟨138781268992,202956727⟩ E) ⟨138781269120,202204637⟩ (N E ⟨138781269888,197764559⟩ E)) ⟨138781270016,197036445⟩ (N (N E ⟨138915481472,321546460⟩ E) ⟨138915481600,320307727⟩ (N E ⟨138915481728,319074957⟩ E))) ⟨138915481856,317848115⟩ (N (N (N E ⟨138915481984,316627168⟩ E) ⟨138915482112,315412081⟩ (N E ⟨138915482240,314202821⟩ E)) ⟨138915482368,312999354⟩ (N (N E ⟨138915482496,311801647⟩ E) ⟨138915482624,310609667⟩ (N E ⟨138915482752,309423381⟩ E))))) ⟨138915482880,308242756⟩ (N (N (N (N (N E ⟨138915483008,307067760⟩ E) ⟨138915483136,305898361⟩ (N E ⟨138915483264,304734526⟩ E)) ⟨138915483392,303576225⟩ (N (N E ⟨138915483520,302423425⟩ E) ⟨138915483648,301276095⟩ (N E ⟨138915483776,300134204⟩ E))) ⟨138915483904,298997722⟩ (N (N (N E ⟨138915484032,297866616⟩ E) ⟨138915484160,296740857⟩ (N E ⟨138915484288,295620415⟩ E)) ⟨138915484416,294505259⟩ (N (N E ⟨138915484672,292290687⟩ E) ⟨138915484800,291191212⟩ (N E ⟨138915484928,290096904⟩ E)))) ⟨138915485056,289007735⟩ (N (N (N (N E ⟨138915485184,287923676⟩ E) ⟨138915485312,286844698⟩ (N E ⟨138915485440,285770772⟩ E)) ⟨138915485568,284701870⟩ (N (N E ⟨138915485696,283637965⟩ E) ⟨138915485824,282579027⟩ (N E ⟨138915485952,281525029⟩ E))) ⟨138915486080,280475944⟩ (N (N (N E ⟨138915486208,279431743⟩ E) ⟨138915486464,277357888⟩ (N E ⟨138915486592,276328179⟩ E)) ⟨138915486976,273267608⟩ (N (N E ⟨138915487232,271250759⟩ E) ⟨138915487360,270249317⟩ (N E ⟨138915487616,268260265⟩ E))))))))

noncomputable def tab8 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨139049699328,417373870⟩ E) ⟨139049699456,415767520⟩ E) ⟨139049699584,414168896⟩ (N E ⟨139049699712,412577953⟩ E)) ⟨139049699840,410994646⟩ (N (N E ⟨139049699968,409418931⟩ E) ⟨139049700096,407850765⟩ (N E ⟨139049700224,406290105⟩ E))) ⟨139049700352,404736907⟩ (N (N (N E ⟨139049700480,403191128⟩ E) ⟨139049700608,401652726⟩ (N E ⟨139049700736,400121659⟩ E)) ⟨139049700864,398597885⟩ (N (N E ⟨139049700992,397081362⟩ E) ⟨139049701120,395572049⟩ (N E ⟨139049701248,394069904⟩ E)))) ⟨139049701376,392574887⟩ (N (N (N (N E ⟨139049701504,391086957⟩ E) ⟨139049701632,389606074⟩ (N E ⟨139049701760,388132198⟩ E)) ⟨139049701888,386665289⟩ (N (N E ⟨139049702016,385205308⟩ E) ⟨139049702144,383752215⟩ (N E ⟨139049702272,382305971⟩ E))) ⟨139049702528,379433877⟩ (N (N (N E ⟨139049702656,378007950⟩ E) ⟨139049702784,376588719⟩ (N E ⟨139049702912,375176147⟩ E)) ⟨139049703040,373770195⟩ (N (N E ⟨139049703168,372370826⟩ E) ⟨139049703552,368211854⟩ (N E ⟨139049703680,366838452⟩ E))))) ⟨139049703808,365471452⟩ (N (N (N (N (N E ⟨139049703936,364110816⟩ E) ⟨139049704064,362756511⟩ (N E ⟨139049704192,361408500⟩ E)) ⟨139049704320,360066748⟩ (N (N E ⟨139049704704,356078700⟩ E) ⟨139049704832,354761639⟩ (N E ⟨139049705088,352145745⟩ E))) ⟨139049705216,350846844⟩ (N (N (N E ⟨139049705472,348266970⟩ E) ⟨139183917056,527347199⟩ (N E ⟨139183917184,525317595⟩ E)) ⟨139183917312,523297751⟩ (N (N E ⟨139183917440,521287612⟩ E) ⟨139183917568,519287121⟩ (N E ⟨139183917696,517296223⟩ E)))) ⟨139183917824,515314863⟩ (N (N (N (N E ⟨139183917952,513342986⟩ E) ⟨139183918080,511380538⟩ (N E ⟨139183918208,509427464⟩ E)) ⟨139183918336,507483711⟩ (N (N E ⟨139183918464,505549225⟩ E) ⟨139183918592,503623953⟩ (N E ⟨139183918720,501707843⟩ E))) ⟨139183918848,499800843⟩ (N (N (N E ⟨139183918976,497902900⟩ E) ⟨139183919104,496013963⟩ (N E ⟨139183919232,494133980⟩ E)) ⟨139183919360,492262901⟩ (N (N E ⟨139183919488,490400675⟩ E) ⟨139183919744,486702582⟩ (N E ⟨139183919872,484866616⟩ E)))))) ⟨139183920128,481220596⟩ (N (N (N (N (N (N E ⟨139183920256,479410445⟩ E) ⟨139183920384,477608802⟩ (N E ⟨139183920512,475815620⟩ E)) ⟨139183920640,474030850⟩ (N (N E ⟨139183920768,472254445⟩ E) ⟨139183920896,470486359⟩ (N E ⟨139183921024,468726544⟩ E))) ⟨139183921152,466974955⟩ (N (N (N E ⟨139183921280,465231544⟩ E) ⟨139183921536,461769076⟩ (N E ⟨139183921664,460049929⟩ E)) ⟨139183921792,458338779⟩ (N (N E ⟨139183922048,454940294⟩ E) ⟨139183922688,446580948⟩ (N E ⟨139183922944,443291049⟩ E)))) ⟨139183923200,440031407⟩ (N (N (N (N E ⟨139318134912,647731446⟩ E) ⟨139318135040,645240922⟩ (N E ⟨139318135168,642762364⟩ E)) ⟨139318135296,640295702⟩ (N (N E ⟨139318135424,637840869⟩ E) ⟨139318135552,635397796⟩ (N E ⟨139318135680,632966416⟩ E))) ⟨139318135808,630546662⟩ (N (N (N E ⟨139318135936,628138466⟩ E) ⟨139318136064,625741763⟩ (N E ⟨139318136192,623356488⟩ E)) ⟨139318136320,620982573⟩ (N (N E ⟨139318136448,618619956⟩ E) ⟨139318136576,616268570⟩ (N E ⟨139318136704,613928353⟩ E))))) ⟨139318136832,611599240⟩ (N (N (N (N (N E ⟨139318136960,609281168⟩ E) ⟨139318137088,606974075⟩ (N E ⟨139318137216,604677898⟩ E)) ⟨139318137344,602392575⟩ (N (N E ⟨139318137472,600118045⟩ E) ⟨139318137600,597854246⟩ (N E ⟨139318137728,595601118⟩ E))) ⟨139318137856,593358600⟩ (N (N (N E ⟨139318137984,591126633⟩ E) ⟨139318138112,588905156⟩ (N E ⟨139318138240,586694112⟩ E)) ⟨139318138368,584493440⟩ (N (N E ⟨139318138496,582303083⟩ E) ⟨139318138624,580122983⟩ (N E ⟨139318138752,577953081⟩ E)))) ⟨139318138880,575793322⟩ (N (N (N (N E ⟨139318139008,573643647⟩ E) ⟨139318139136,571504001⟩ (N E ⟨139318139520,565144673⟩ E)) ⟨139318139648,563044583⟩ (N (N E ⟨139318140032,556802605⟩ E) ⟨139318140160,554741196⟩ (N E ⟨139318140544,548613977⟩ E))) ⟨139318140800,544576144⟩ (N (N (N E ⟨139318140928,542571166⟩ E) ⟨139452352768,779996749⟩ (N E ⟨139452352896,777000554⟩ E)) ⟨139452353024,774018741⟩ (N (N E ⟨139452353152,771051226⟩ E) ⟨139452353280,768097928⟩ (N E ⟨139452353408,765158764⟩ E))))))) ⟨139452353536,762233654⟩ (N (N (N (N (N (N (N E ⟨139452353664,759322518⟩ E) ⟨139452353792,756425274⟩ (N E ⟨139452353920,753541843⟩ E)) ⟨139452354048,750672147⟩ (N (N E ⟨139452354176,747816106⟩ E) ⟨139452354304,744973644⟩ (N E ⟨139452354432,742144682⟩ E))) ⟨139452354560,739329144⟩ (N (N (N E ⟨139452354688,736526953⟩ E) ⟨139452354816,733738033⟩ (N E ⟨139452354944,730962309⟩ E)) ⟨139452355072,728199706⟩ (N (N E ⟨139452355200,725450150⟩ E) ⟨139452355328,722713566⟩ (N E ⟨139452355584,717279024⟩ E)))) ⟨139452355712,714580920⟩ (N (N (N (N E ⟨139452355840,711895497⟩ E) ⟨139452356096,706562413⟩ (N E ⟨139452356224,703914609⟩ E)) ⟨139452356608,696045312⟩ (N (N E ⟨139452356736,693446687⟩ E) ⟨139452356992,688285737⟩ (N E ⟨139452357120,685723278⟩ E))) ⟨139452357248,683172738⟩ (N (N (N E ⟨139452357376,680634054⟩ E) ⟨139452357504,678107157⟩ (N E ⟨139452357632,675591982⟩ E)) ⟨139452357760,673088464⟩ (N (N E ⟨139452358144,665647209⟩ E) ⟨139452358272,663189676⟩ (N E ⟨139452358400,660743480⟩ E))))) ⟨139452358656,655884850⟩ (N (N (N (N (N E ⟨139586570624,923992626⟩ E) ⟨139586570752,920446716⟩ (N E ⟨139586570880,916917811⟩ E)) ⟨139586571008,913405811⟩ (N (N E ⟨139586571136,909910620⟩ E) ⟨139586571264,906432141⟩ (N E ⟨139586571392,902970279⟩ E))) ⟨139586571520,899524937⟩ (N (N (N E ⟨139586571648,896096023⟩ E) ⟨139586571776,892683441⟩ (N E ⟨139586571904,889287098⟩ E)) ⟨139586572032,885906902⟩ (N (N E ⟨139586572160,882542760⟩ E) ⟨139586572288,879194582⟩ (N E ⟨139586572416,875862275⟩ E)))) ⟨139586572544,872545751⟩ (N (N (N (N E ⟨139586572672,869244919⟩ E) ⟨139586572800,865959690⟩ (N E ⟨139586572928,862689976⟩ E)) ⟨139586573056,859435688⟩ (N (N E ⟨139586573184,856196740⟩ E) ⟨139586573312,852973045⟩ (N E ⟨139586573440,849764517⟩ E))) ⟨139586573568,846571069⟩ (N (N (N E ⟨139586573696,843392618⟩ E) ⟨139586573824,840229078⟩ (N E ⟨139586574080,833946398⟩ E)) ⟨139586574208,830827091⟩ (N (N E ⟨139586574464,824632134⟩ E) ⟨139586574592,821556320⟩ (N E ⟨139586574720,818494842⟩ E)))))) ⟨139586575360,803399697⟩ (N (N (N (N (N (N E ⟨139586576000,788651136⟩ E) ⟨139586576256,782846616⟩ (N E ⟨139586576384,779964392⟩ E)) ⟨139720788480,1079562214⟩ (N (N E ⟨139720788608,1075423275⟩ E) ⟨139720788736,1071304164⟩ (N E ⟨139720788864,1067204767⟩ E))) ⟨139720788992,1063124972⟩ (N (N (N E ⟨139720789120,1059064665⟩ E) ⟨139720789248,1055023736⟩ (N E ⟨139720789376,1051002072⟩ E)) ⟨139720789504,1046999565⟩ (N (N E ⟨139720789632,1043016104⟩ E) ⟨139720789760,1039051582⟩ (N E ⟨139720789888,1035105889⟩ E)))) ⟨139720790016,1031178918⟩ (N (N (N (N E ⟨139720790144,1027270564⟩ E) ⟨139720790272,1023380719⟩ (N E ⟨139720790400,1019509280⟩ E)) ⟨139720790528,1015656141⟩ (N (N E ⟨139720790656,1011821199⟩ E) ⟨139720790784,1008004350⟩ (N E ⟨139720791040,1000424525⟩ E))) ⟨139720791168,996661346⟩ (N (N (N E ⟨139720791552,985477538⟩ E) ⟨139720791680,981784515⟩ (N E ⟨139720791936,974450252⟩ E)) ⟨139720792064,970808817⟩ (N (N E ⟨139720792192,967184386⟩ E) ⟨139720792320,963576864⟩ (N E ⟨139720792448,959986155⟩ E))))) ⟨139720792576,956412165⟩ (N (N (N (N (N E ⟨139720792704,952854802⟩ E) ⟨139720793088,942281546⟩ (N E ⟨139720793216,938789767⟩ E)) ⟨139720793344,935314156⟩ (N (N E ⟨139720793600,928411079⟩ E) ⟨139720793728,924983437⟩ (N E ⟨139720793984,918175502⟩ E))) ⟨139720794112,914795035⟩ (N (N (N E ⟨139855006336,1246542387⟩ E) ⟨139855006464,1241767851⟩ (N E ⟨139855006592,1237016167⟩ E)) ⟨139855006720,1232287203⟩ (N (N E ⟨139855006848,1227580829⟩ E) ⟨139855006976,1222896915⟩ (N E ⟨139855007104,1218235333⟩ E)))) ⟨139855007232,1213595956⟩ (N (N (N (N E ⟨139855007360,1208978655⟩ E) ⟨139855007488,1204383306⟩ (N E ⟨139855007616,1199809782⟩ E)) ⟨139855007744,1195257960⟩ (N (N E ⟨139855007872,1190727717⟩ E) ⟨139855008000,1186218928⟩ (N E ⟨139855008128,1181731474⟩ E))) ⟨139855008256,1177265231⟩ (N (N (N E ⟨139855008384,1172820081⟩ E) ⟨139855008512,1168395904⟩ (N E ⟨139855008768,1159609993⟩ E)) ⟨139855008896,1155248024⟩ (N (N E ⟨139855009024,1150906558⟩ E) ⟨139855009152,1146585479⟩ (N E ⟨139855009280,1142284672⟩ E))))))))

noncomputable def tab9 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨139855009664,1129502747⟩ E) ⟨139855009792,1125281895⟩ E) ⟨139855009920,1121080752⟩ (N E ⟨139855010048,1116899208⟩ E)) ⟨139855010176,1112737153⟩ (N (N E ⟨139855010304,1108594478⟩ E) ⟨139855010560,1100366836⟩ (N E ⟨139855010688,1096281654⟩ E))) ⟨139855010816,1092215424⟩ (N (N (N E ⟨139855010944,1088168040⟩ E) ⟨139855011328,1076137917⟩ (N E ⟨139855011584,1068210162⟩ E)) ⟨139855011712,1064273676⟩ (N (N E ⟨139855011840,1060355316⟩ E) ⟨139989224320,1419311945⟩ (N E ⟨139989224448,1413886087⟩ E)))) ⟨139989224576,1408486147⟩ (N (N (N (N E ⟨139989224704,1403111977⟩ E) ⟨139989224832,1397763430⟩ (N E ⟨139989224960,1392440360⟩ E)) ⟨139989225088,1387142620⟩ (N (N E ⟨139989225216,1381870066⟩ E) ⟨139989225344,1376622554⟩ (N E ⟨139989225472,1371399943⟩ E))) ⟨139989225600,1366202089⟩ (N (N (N E ⟨139989225728,1361028853⟩ E) ⟨139989225856,1355880094⟩ (N E ⟨139989225984,1350755673⟩ E)) ⟨139989226112,1345655453⟩ (N (N E ⟨139989226240,1340579296⟩ E) ⟨139989226368,1335527067⟩ (N E ⟨139989226496,1330498629⟩ E))))) ⟨139989226624,1325493849⟩ (N (N (N (N (N E ⟨139989226752,1320512592⟩ E) ⟨139989226880,1315554727⟩ (N E ⟨139989227008,1310620122⟩ E)) ⟨139989227136,1305708645⟩ (N (N E ⟨139989227264,1300820167⟩ E) ⟨139989227648,1286291437⟩ (N E ⟨139989227776,1281493669⟩ E))) ⟨139989227904,1276718263⟩ (N (N (N E ⟨139989228160,1267234035⟩ E) ⟨139989228672,1248528466⟩ (N E ⟨139989228928,1239305181⟩ E)) ⟨139989229568,1216617055⟩ (N (N E ⟨140123442176,1607881057⟩ E) ⟨140123442304,1601740208⟩ (N E ⟨140123442432,1595628665⟩ E)))) ⟨140123442560,1589546261⟩ (N (N (N (N E ⟨140123442688,1583492828⟩ E) ⟨140123442816,1577468201⟩ (N E ⟨140123442944,1571472217⟩ E)) ⟨140123443072,1565504710⟩ (N (N E ⟨140123443200,1559565520⟩ E) ⟨140123443328,1553654485⟩ (N E ⟨140123443456,1547771445⟩ E))) ⟨140123443584,1541916240⟩ (N (N (N E ⟨140123443712,1536088714⟩ E) ⟨140123443840,1530288708⟩ (N E ⟨140123443968,1524516067⟩ E)) ⟨140123444096,1518770637⟩ (N (N E ⟨140123444352,1507360792⟩ E) ⟨140123444480,1501696073⟩ (N E ⟨140123444608,1496057954⟩ E)))))) ⟨140123444736,1490446287⟩ (N (N (N (N (N (N E ⟨140123445248,1468261163⟩ E) ⟨140123445504,1457323483⟩ (N E ⟨140123445632,1451892858⟩ E)) ⟨140123446656,1409346442⟩ (N (N E ⟨140123446912,1398954390⟩ E) ⟨140123447296,1383545347⟩ (N E ⟨140257660160,1800398966⟩ E))) ⟨140257660288,1793535994⟩ (N (N (N E ⟨140257660416,1786705712⟩ E) ⟨140257660544,1779907933⟩ (N E ⟨140257660672,1773142471⟩ E)) ⟨140257660800,1766409142⟩ (N (N E ⟨140257660928,1759707763⟩ E) ⟨140257661056,1753038153⟩ (N E ⟨140257661184,1746400130⟩ E)))) ⟨140257661312,1739793515⟩ (N (N (N (N E ⟨140257661440,1733218130⟩ E) ⟨140257661568,1726673798⟩ (N E ⟨140257661696,1720160343⟩ E)) ⟨140257661824,1713677589⟩ (N (N E ⟨140257661952,1707225364⟩ E) ⟨140257662080,1700803495⟩ (N E ⟨140257662208,1694411811⟩ E))) ⟨140257662336,1688050141⟩ (N (N (N E ⟨140257662464,1681718317⟩ E) ⟨140257662592,1675416170⟩ (N E ⟨140257662720,1669143534⟩ E)) ⟨140257662848,1662900242⟩ (N (N E ⟨140257662976,1656686131⟩ E) ⟨140257663104,1650501037⟩ (N E ⟨140257663232,1644344796⟩ E))))) ⟨140257663360,1638217248⟩ (N (N (N (N (N E ⟨140257663744,1620005160⟩ E) ⟨140257663872,1613990788⟩ (N E ⟨140257664128,1602045592⟩ E)) ⟨140257664256,1596114459⟩ (N (N E ⟨140257664384,1590210763⟩ E) ⟨140257664640,1578485078⟩ (N E ⟨140257664768,1572662787⟩ E))) ⟨140257664896,1566867331⟩ (N (N (N E ⟨140257665024,1561098561⟩ E) ⟨140391878144,2002023664⟩ (N E ⟨140391878272,1994406676⟩ E)) ⟨140391878400,1986825901⟩ (N (N E ⟨140391878528,1979281131⟩ E) ⟨140391878656,1971772162⟩ (N E ⟨140391878784,1964298789⟩ E)))) ⟨140391878912,1956860810⟩ (N (N (N (N E ⟨140391879040,1949458024⟩ E) ⟨140391879168,1942090232⟩ (N E ⟨140391879296,1934757235⟩ E)) ⟨140391879424,1927458836⟩ (N (N E ⟨140391879680,1912965048⟩ E) ⟨140391879808,1905769273⟩ (N E ⟨140391879936,1898607319⟩ E))) ⟨140391880064,1891478997⟩ (N (N (N E ⟨140391880192,1884384118⟩ E) ⟨140391880320,1877322492⟩ (N E ⟨140391880448,1870293933⟩ E)) ⟨140391880576,1863298255⟩ (N (N E ⟨140391880704,1856335274⟩ E) ⟨140391880832,1849404807⟩ (N E ⟨140391880960,1842506671⟩ E))))))) ⟨140391881088,1835640685⟩ (N (N (N (N (N (N (N E ⟨140391881216,1828806669⟩ E) ⟨140391881472,1815233837⟩ (N E ⟨140391881600,1808494667⟩ E)) ⟨140391881856,1795109942⟩ (N (N E ⟨140391882368,1768710122⟩ E) ⟨140391882496,1762186180⟩ (N E ⟨140391882624,1755692307⟩ E))) ⟨140391882752,1749228337⟩ (N (N (N E ⟨140526096000,2220901632⟩ E) ⟨140526096128,2212459945⟩ (N E ⟨140526096256,2204058353⟩ E)) ⟨140526096384,2195696626⟩ (N (N E ⟨140526096512,2187374539⟩ E) ⟨140526096640,2179091866⟩ (N E ⟨140526096768,2170848383⟩ E)))) ⟨140526096896,2162643867⟩ (N (N (N (N E ⟨140526097024,2154478097⟩ E) ⟨140526097152,2146350854⟩ (N E ⟨140526097280,2138261920⟩ E)) ⟨140526097408,2130211079⟩ (N (N E ⟨140526097536,2122198114⟩ E) ⟨140526097664,2114222813⟩ (N E ⟨140526097792,2106284963⟩ E))) ⟨140526097920,2098384352⟩ (N (N (N E ⟨140526098048,2090520772⟩ E) ⟨140526098304,2074903872⟩ (N E ⟨140526098560,2059432613⟩ E)) ⟨140526098688,2051751090⟩ (N (N E ⟨140526099200,2021381015⟩ E) ⟨140526099328,2013876510⟩ (N E ⟨140526099456,2006406819⟩ E))))) ⟨140526099584,1998971747⟩ (N (N (N (N (N E ⟨140526100096,1969573830⟩ E) ⟨140526100352,1955077646⟩ (N E ⟨140526100480,1947879594⟩ E)) ⟨140660313984,2440670888⟩ (N (N E ⟨140660314112,2431411505⟩ E) ⟨140660314240,2422196016⟩ (N E ⟨140660314368,2413024171⟩ E))) ⟨140660314496,2403895724⟩ (N (N (N E ⟨140660314624,2394810428⟩ E) ⟨140660314752,2385768037⟩ (N E ⟨140660314880,2376768310⟩ E)) ⟨140660315008,2367811004⟩ (N (N E ⟨140660315136,2358895879⟩ E) ⟨140660315264,2350022698⟩ (N E ⟨140660315392,2341191223⟩ E)))) ⟨140660315520,2332401220⟩ (N (N (N (N E ⟨140660315648,2323652454⟩ E) ⟨140660315776,2314944695⟩ (N E ⟨140660316032,2297651272⟩ E)) ⟨140660316160,2289065152⟩ (N (N E ⟨140660316288,2280519125⟩ E) ⟨140660316416,2272012966⟩ (N E ⟨140660316544,2263546451⟩ E))) ⟨140660316928,2238382569⟩ (N (N (N E ⟨140660317184,2221800846⟩ E) ⟨140660317312,2213567596⟩ (N E ⟨140660317440,2205372470⟩ E)) ⟨140660317568,2197215256⟩ (N (N E ⟨140660317696,2189095743⟩ E) ⟨140660317824,2181013722⟩ (N E ⟨140660317952,2172968985⟩ E)))))) ⟨140660318080,2164961326⟩ (N (N (N (N (N (N E ⟨140660318208,2156990541⟩ E) ⟨140794531968,2668686306⟩ (N E ⟨140794532352,2638513874⟩ E)) ⟨140794532480,2628551302⟩ (N (N E ⟨140794532608,2618635734⟩ E) ⟨140794532864,2598944548⟩ (N E ⟨140794532992,2589168404⟩ E))) ⟨140794533248,2569753709⟩ (N (N (N E ⟨140794533376,2560114642⟩ E) ⟨140794533504,2550520753⟩ (N E ⟨140794534016,2512591929⟩ E)) ⟨140794534144,2503220156⟩ (N (N E ⟨140794534784,2457011621⟩ E) ⟨140794534912,2447898293⟩ (N E ⟨140794535680,2394097148⟩ E)))) ⟨140794535936,2376492688⟩ (N (N (N (N E ⟨140928749824,2915678576⟩ E) ⟨140928750208,2882744747⟩ (N E ⟨140928750336,2871870296⟩ E)) ⟨140928750464,2861047103⟩ (N (N E ⟨140928750592,2850274879⟩ E) ⟨140928750720,2839553335⟩ (N E ⟨140928750976,2818261147⟩ E))) ⟨140928751104,2807689935⟩ (N (N (N E ⟨140928751232,2797168272⟩ E) ⟨140928751360,2786695877⟩ (N E ⟨140928751488,2776272475⟩ E)) ⟨140928751616,2765897790⟩ (N (N E ⟨140928751744,2755571550⟩ E) ⟨140928751872,2745293482⟩ (N E ⟨140928752000,2735063317⟩ E))))) ⟨140928752128,2724880788⟩ (N (N (N (N (N E ⟨140928752512,2694616362⟩ E) ⟨140928752768,2674673422⟩ (N E ⟨140928753024,2654914744⟩ E)) ⟨140928753664,2606310863⟩ (N (N E ⟨141062967936,3148257866⟩ E) ⟨141062968320,3112797384⟩ (N E ⟨141062968448,3101088340⟩ E))) ⟨141062968576,3089434332⟩ (N (N (N E ⟨141062968704,3077835050⟩ E) ⟨141062968832,3066290185⟩ (N E ⟨141062969088,3043362484⟩ E)) ⟨141062969216,3031979042⟩ (N (N E ⟨141062969344,3020648805⟩ E) ⟨141062969600,2998146751⟩ (N E ⟨141062969728,2986974345⟩ E)))) ⟨141062970112,2953768102⟩ (N (N (N (N E ⟨141062970496,2921022282⟩ E) ⟨141062970624,2910207999⟩ (N E ⟨141062971008,2878064211⟩ E)) ⟨141062971136,2867448382⟩ (N (N E ⟨141062971264,2856881481⟩ E) ⟨141062971392,2846363239⟩ (N E ⟨141197186176,3373677043⟩ E))) ⟨141197186432,3348379765⟩ (N (N (N E ⟨141197186560,3335820096⟩ E) ⟨141197186944,3298492970⟩ (N E ⟨141197187072,3286166793⟩ E)) ⟨141197187584,3237434439⟩ (N (N E ⟨141197188352,3166018133⟩ E) ⟨141197188736,3131048874⟩ (N E ⟨141197188864,3119499903⟩ E))))))))

noncomputable def tab10 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨141331404288,3616177262⟩ E) ⟨141331404416,3602625836⟩ E) ⟨141331404672,3575712998⟩ (N E ⟨141331405056,3535813460⟩ E)) ⟨141331405568,3483476254⟩ (N (N E ⟨141331405952,3444858027⟩ E) ⟨141331406720,3369214663⟩ (N E ⟨141331406848,3356810152⟩ E))) ⟨141465621888,3921963369⟩ (N (N (N E ⟨141465622400,3863530874⟩ E) ⟨141465622656,3834722943⟩ (N E ⟨141465622784,3820419725⟩ E)) ⟨141465622912,3806183170⟩ (N (N E ⟨141465623296,3763869769⟩ E) ⟨141465623424,3749896165⟩ (N E ⟨141465623680,3722143067⟩ E)))) ⟨141465623808,3708362854⟩ (N (N (N (N E ⟨141465624192,3667403297⟩ E) ⟨141465624320,3653875967⟩ (N E ⟨141465624448,3640410984⟩ E)) ⟨141465624576,3627008003⟩ (N (N E ⟨141599840640,4100055911⟩ E) ⟨141599841024,4054475523⟩ (N E ⟨141599841280,4024440359⟩ E))) ⟨141599841408,4009527131⟩ (N (N (N E ⟨141599841536,3994682958⟩ E) ⟨141599841792,3965200244⟩ (N E ⟨141599841920,3950560942⟩ E)) ⟨141599842048,3935989176⟩ (N (N E ⟨141599842304,3907046756⟩ E) ⟨141734057856,4470492441⟩ (N E ⟨141734058368,4404135399⟩ E))))) ⟨141734059008,4322911840⟩ (N (N (N (N (N E ⟨141734059136,4306892578⟩ E) ⟨141734059776,4227900701⟩ (N E ⟨141734060032,4196811774⟩ E)) ⟨141868275968,4735942779⟩ (N (N E ⟨141868276224,4700728566⟩ E) ⟨141868276608,4648518996⟩ (N E ⟨141868276992,4597032668⟩ E))) ⟨141868277120,4580029200⟩ (N (N (N E ⟨141868277760,4496181990⟩ E) ⟨142002493952,5023627062⟩ (N E ⟨142002495360,4822786101⟩ E)) ⟨142002495488,4805029944⟩ (N (N E ⟨142136713216,5123221857⟩ E) ⟨142270930688,5490994485⟩ (N E ⟨142270930944,5450617679⟩ E)))) ⟨142405148672,5787071159⟩ (N (N (N (N E ⟨142539366400,6132429910⟩ E) ⟨142673584128,6486535485⟩ (N E ⟨142807801856,6849223449⟩ E)) ⟨142942019584,7220323464⟩ (N (N E ⟨143076237312,7599659374⟩ E) ⟨143210455040,7987049288⟩ (N E ⟨143344672768,8382305677⟩ E))) ⟨143478890496,8785235472⟩ (N (N (N E ⟨143613108224,9195640158⟩ E) ⟨143747325952,9613315884⟩ (N E ⟨143881543680,10038053565⟩ E)) ⟨144149979136,10907852980⟩ (N (N E ⟨144284196864,11352471411⟩ E) ⟨144552632320,12260001552⟩ (N E ⟨144821067776,13190343653⟩ E)))))) ⟨144955285504,13663460618⟩ (N (N (N (N (N (N E ⟨145089503232,14141541911⟩ E) ⟨146029027456,17540496856⟩ (N E ⟨146029027584,17476036621⟩ E)) ⟨146029027712,17411872388⟩ (N (N E ⟨146029027840,17348002527⟩ E) ⟨146029027968,17284425416⟩ (N E ⟨146029028096,17221139448⟩ E))) ⟨146029028224,17158143022⟩ (N (N (N E ⟨146029028352,17095434549⟩ E) ⟨146029028480,17033012451⟩ (N E ⟨146029028736,16909021113⟩ E)) ⟨146029028864,16847448766⟩ (N (N E ⟨146029028992,16786156578⟩ E) ⟨146029029120,16725143020⟩ (N E ⟨146029029248,16664406573⟩ E)))) ⟨146029029376,16603945726⟩ (N (N (N (N E ⟨146029029504,16543758980⟩ E) ⟨146029029632,16483844845⟩ (N E ⟨146029029760,16424201838⟩ E)) ⟨146029029888,16364828489⟩ (N (N E ⟨146029030016,16305723334⟩ E) ⟨146029030144,16246884921⟩ (N E ⟨146029030272,16188311805⟩ E))) ⟨146029030400,16130002552⟩ (N (N (N E ⟨146029030528,16071955735⟩ E) ⟨146029030656,16014169939⟩ (N E ⟨146029030912,15899375782⟩ E)) ⟨146029031168,15785608923⟩ (N (N E ⟨146029031296,15729107282⟩ E) ⟨146029031424,15672858345⟩ (N E ⟨146029031552,15616860755⟩ E))))) ⟨146029031680,15561113166⟩ (N (N (N (N (N E ⟨146029031808,15505614239⟩ E) ⟨146029031936,15450362643⟩ (N E ⟨146029032064,15395357056⟩ E)) ⟨146029032192,15340596165⟩ (N (N E ⟨146029032320,15286078662⟩ E) ⟨146029032448,15231803251⟩ (N E ⟨146029032576,15177768643⟩ E))) ⟨146029032704,15123973555⟩ (N (N (N E ⟨146029032832,15070416714⟩ E) ⟨146029032960,15017096854⟩ (N E ⟨146029033088,14964012717⟩ E)) ⟨146029033472,14806162186⟩ (N (N E ⟨146029033600,14754008520⟩ E) ⟨146029033728,14702084403⟩ (N E ⟨146029033856,14650388624⟩ E)))) ⟨146029033984,14598919978⟩ (N (N (N (N E ⟨146029034240,14496659306⟩ E) ⟨146029034496,14395292897⟩ (N E ⟨146029034624,14344942108⟩ E)) ⟨146029034752,14294811379⟩ (N (N E ⟨146029035136,14145728051⟩ E) ⟨146029035392,14047418502⟩ (N E ⟨146029035520,13998584151⟩ E))) ⟨146700124160,16037511992⟩ (N (N (N E ⟨147102773248,19342312110⟩ E) ⟨148444954624,21395201291⟩ (N E ⟨148713390080,22203018070⟩ E)) ⟨149518696448,24560117157⟩ (N (N E ⟨150324002816,26778460734⟩ E) ⟨152068833280,30881782148⟩ (N E ⟨154618970240,34309130482⟩ E))))))) ⟨154618970368,34174620589⟩ (N (N (N (N (N (N (N E ⟨154618970496,34030483220⟩ E) ⟨154618970880,33541516667⟩ (N E ⟨154618971008,33360104411⟩ E)) ⟨154618971392,32762527531⟩ (N (N E ⟨154618971648,32321172538⟩ E) ⟨154618971776,32088070159⟩ (N E ⟨154618971904,31846901215⟩ E))) ⟨154618972160,31341036723⟩ (N (N (N E ⟨154618972544,30526042292⟩ E) ⟨154618972928,29647981632⟩ (N E ⟨154618973184,29030101448⟩ E)) ⟨154618973312,28711997456⟩ (N (N E ⟨154618973440,28388051375⟩ E) ⟨154618973696,27723448008⟩ (N E ⟨154618973952,27037941846⟩ E)))) ⟨154618974208,26333212918⟩ (N (N (N (N E ⟨154618974976,24120840786⟩ E) ⟨154618975232,23356458401⟩ (N E ⟨154618975744,21797860699⟩ E)) ⟨154618975872,21403283349⟩ (N (N E ⟨154618976256,20211247886⟩ E) ⟨154618976640,19011352264⟩ (N E ⟨154618978048,14637876662⟩ E))) ⟨154618978304,13861447354⟩ (N (N (N E ⟨155155849216,14040504136⟩ E) ⟨155692720128,14220509370⟩ (N E ⟨156766458880,24459631073⟩ E)) ⟨156766461952,14582540172⟩ (N (N E ⟨157034897408,14673315167⟩ E) ⟨157840203776,14945852244⟩ (N E ⟨158377074688,15127448053⟩ E))))) ⟨158913945600,15308711174⟩ (N (N (N (N (N E ⟨159450816512,15489420729⟩ E) ⟨159987687424,15669355463⟩ (N E ⟨160792993792,15937321714⟩ E)) ⟨161061429248,16026017701⟩ (N (N E ⟨161195646976,16070232946⟩ E) ⟨161464082432,16158381002⟩ (N E ⟨161598300160,16202307066⟩ E))) ⟨162135171072,16376946761⟩ (N (N (N E ⟨162269388800,16420323930⟩ E) ⟨162806259712,16592603004⟩ (N E ⟨163074695168,16677959410⟩ E)) ⟨163208913664,14078312624⟩ (N (N E ⟨163208913792,13650348921⟩ E) ⟨163208913920,13226454308⟩ (N E ⟨163208914432,11575322320⟩ E)))) ⟨163208914560,11174556605⟩ (N (N (N (N E ⟨163208914688,10778946325⟩ E) ⟨163208915072,9624698905⟩ (N E ⟨163208915584,8167535505⟩ E)) ⟨163208915712,7818828574⟩ (N (N E ⟨163208915968,7141055887⟩ E) ⟨163208916864,4987473700⟩ (N E ⟨163208917248,4174759615⟩ E))) ⟨163208917376,3919189493⟩ (N (N (N E ⟨163208917504,3671406195⟩ E) ⟨163208917760,3199452127⟩ (N E ⟨163208917888,2975394930⟩ E)) ⟨163208918656,1800722553⟩ (N (N E ⟨163208918784,1633520237⟩ E) ⟨163208919040,1323785994⟩ (N E ⟨163208919808,592043860⟩ E)))))) ⟨163208919936,498772193⟩ (N (N (N (N (N (N E ⟨163208920064,413636898⟩ E) ⟨163208920192,336605342⟩ (N E ⟨163208920576,153739518⟩ E)) ⟨163208920704,108707281⟩ (N (N E ⟨163208920832,71549112⟩ E) ⟨163208920960,42206164⟩ (N E ⟨163208921088,20615427⟩ E))) ⟨163343137024,1052131443⟩ (N (N (N E ⟨163880005632,4784273473⟩ E) ⟨163880007040,2201824020⟩ (N E ⟨164014225792,948771927⟩ E)) ⟨164282658944,4552209571⟩ (N (N E ⟨164282660480,1859280029⟩ E) ⟨164282660608,1688171069⟩ (N E ⟨164282662144,284407100⟩ E)))) ⟨164282662784,48070499⟩ (N (N (N (N E ⟨164416876032,6026640001⟩ E) ⟨164416876800,4296954703⟩ (N E ⟨164551095424,2644908818⟩ E)) ⟨164551096192,1537656706⟩ (N (N E ⟨164551097856,168701117⟩ E) ⟨164685315584,170128683⟩ (N E ⟨164953751552,27082111⟩ E))) ⟨165222183168,4374733064⟩ (N (N (N E ⟨165222184832,1567425373⟩ E) ⟨165222185728,642192856⟩ (N E ⟨165222187008,28034818⟩ E)) ⟨165356402560,1573220670⟩ (N (N E ⟨165490620544,1270718938⟩ E) ⟨165490621312,549197685⟩ (N E ⟨165490622080,128916910⟩ E))))) ⟨165624838400,1133779146⟩ (N (N (N (N (N E ⟨165624839168,460820721⟩ E) ⟨165759054720,3168480922⟩ (N E ⟨165759055616,1757979055⟩ E)) ⟨165893273216,1940622941⟩ (N (N E ⟨165893274240,765916069⟩ E) ⟨165893274880,307291085⟩ (N E ⟨166027490304,2959518831⟩ E))) ⟨166027491072,1769918994⟩ (N (N (N E ⟨166027491840,886553265⟩ E) ⟨166027492096,660269932⟩ (N E ⟨166027493248,56838378⟩ E)) ⟨166161709440,1016350441⟩ (N (N E ⟨166161710208,386270569⟩ E) ⟨166295928192,245108382⟩ (N E ⟨166295928320,186023393⟩ E)))) ⟨166295928832,31644633⟩ (N (N (N (N E ⟨166430144000,2152688630⟩ E) ⟨166430144512,1456279812⟩ (N E ⟨166430145536,474604818⟩ E)) ⟨166564364160,59255203⟩ (N (N E ⟨166698579712,1798660734⟩ E) ⟨166698580480,903841177⟩ (N E ⟨166698580736,674316506⟩ E))) ⟨166698581504,189590858⟩ (N (N (N E ⟨166698582016,32896024⟩ E) ⟨166832797440,1804212308⟩ (N E ⟨166832799488,95634633⟩ E)) ⟨166832799744,33298690⟩ (N (N E ⟨166967016576,397672990⟩ E) ⟨166967016960,191867834⟩ (N E ⟨166967017344,60960126⟩ E))))))))

noncomputable def tab11 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨167235451776,581743186⟩ E) ⟨167235452672,97792220⟩ E) ⟨167369668992,1049233460⟩ (N E ⟨167369669888,325230237⟩ E)) ⟨167369670528,62564527⟩ (N (N E ⟨167369670656,34830601⟩ E) ⟨167503887744,257213756⟩ (N E ⟨167638104192,1341886732⟩ E))) ⟨167638104448,1055971760⟩ (N (N (N E ⟨167638104576,926065130⟩ E) ⟨167638105344,328131092⟩ (N E ⟨167638105472,258434129⟩ E)) ⟨167638105728,144330496⟩ (N (N E ⟨167638106112,35546092⟩ E) ⟨167772322432,807520352⟩ (N E ⟨167772322560,694677913⟩ E)))) ⟨167772323200,259628227⟩ (N (N (N (N E ⟨167772323328,198181054⟩ E) ⟨167772323456,145143006⟩ (N E ⟨167772323584,100456997⟩ E)) ⟨167772323840,35890453⟩ (N (N E ⟨167906541440,64535437⟩ E) ⟨168040757760,934838728⟩ (N E ⟨168040758272,498559423⟩ E))) ⟨168040759040,101693630⟩ (N (N (N E ⟨168174977024,36867527⟩ E) ⟨168443411456,503722235⟩ (N E ⟨168443411712,336107919⟩ E)) ⟨168443412352,66300202⟩ (N (N E ⟨168443412480,37470289⟩ E) ⟨168577629184,505365361⟩ (N E ⟨168577629312,417027637⟩ E))))) ⟨168577629568,266222427⟩ (N (N (N (N (N E ⟨168577629696,203662948⟩ E) ⟨168577630080,66707555⟩ (N E ⟨168577630208,37756530⟩ E)) ⟨168711847552,150265964⟩ (N (N E ⟨168711847680,104489929⟩ E) ⟨168711847808,67100971⟩ (N E ⟨168711847936,38032446⟩ E))) ⟨168846065536,67480260⟩ (N (N (N E ⟨168846065664,38297871⟩ E) ⟨168980282368,510056193⟩ (N E ⟨168980282880,206072326⟩ E)) ⟨168980283136,105485572⟩ (N (N E ⟨168980283264,67845240⟩ E) ⟨168980283392,38552644⟩ (N E ⟨169114500608,206824589⟩ E)))) ⟨169114500864,105956227⟩ (N (N (N (N E ⟨169114501120,38796613⟩ E) ⟨169248718592,106408517⟩ (N E ⟨169248718848,39029630⟩ E)) ⟨169382935680,424810589⟩ (N (N E ⟨169382936064,208251407⟩ E) ⟨169382936320,106842258⟩ (N E ⟨169382936448,68852609⟩ E))) ⟨169382936576,39251555⟩ (N (N (N E ⟨169517154176,69158670⟩ E) ⟨169517154304,39462254⟩ (N E ⟨169651371648,154340311⟩ E)) ⟨169651371776,107653406⟩ (N (N E ⟨169651371904,69449617⟩ E) ⟨169651372032,39661600⟩ (N E ⟨169785589248,210194131⟩ E)))))) ⟨169785589376,154832452⟩ (N (N (N (N (N (N E ⟨169785589504,108030487⟩ E) ⟨169785589632,69725309⟩ (N E ⟨169785589760,39849474⟩ E)) ⟨169919806976,210788238⟩ (N (N E ⟨169919807104,155301570⟩ E) ⟨169919807360,69985616⟩ (N E ⟨169919807488,40025762⟩ E))) ⟨170054024704,211355307⟩ (N (N (N E ⟨170054025088,70230413⟩ E) ⟨170054025216,40190358⟩ (N E ⟨170188242688,109045980⟩ E)) ⟨170188242944,40343163⟩ (N (N E ⟨170322460288,156569221⟩ E) ⟨170322460416,109345446⟩ (N E ⟨170322460544,70673019⟩ E)))) ⟨170322460672,40484085⟩ (N (N (N (N E ⟨170456678016,156944727⟩ E) ⟨170456678144,109625194⟩ (N E ⟨170456678272,70870618⟩ E)) ⟨170456678400,40613038⟩ (N (N E ⟨170590896000,71052286⟩ E) ⟨170590896128,40729946⟩ (N E ⟨170725113600,110125106⟩ E))) ⟨170725113728,71217940⟩ (N (N (N E ⟨170725113856,40834737⟩ E) ⟨170859331584,40927349⟩ (N E ⟨170993549184,71500897⟩ E)) ⟨170993549312,41007726⟩ (N (N E ⟨171127766912,71618069⟩ E) ⟨171127767040,41075819⟩ (N E ⟨171261984768,41131588⟩ E))))) ⟨171396202496,41174998⟩ (N (N (N (N (N E ⟨171530420224,41206024⟩ E) ⟨171664637952,41224648⟩ (N E ⟨171798855808,19042279⟩ E)) ⟨171798855936,5331210⟩ (N (N E ⟨171798856064,66057⟩ E) ⟨172335727488,3180391⟩ (N E ⟨172335727616,3170505⟩ E))) ⟨172335727744,3160659⟩ (N (N (N E ⟨172335727872,3150850⟩ E) ⟨172335728000,3141079⟩ (N E ⟨172335728128,3131346⟩ E)) ⟨172335728256,3121651⟩ (N (N E ⟨172335728384,3111994⟩ E) ⟨172335728512,3102374⟩ (N E ⟨172335728640,3092790⟩ E)))) ⟨172335728768,3083244⟩ (N (N (N (N E ⟨172335728896,3073735⟩ E) ⟨172335729024,3064262⟩ (N E ⟨172335729152,3054826⟩ E)) ⟨172335729280,3045426⟩ (N (N E ⟨172335729408,3036063⟩ E) ⟨172335729536,3026735⟩ (N E ⟨172335729664,3017443⟩ E))) ⟨172335729792,3008187⟩ (N (N (N E ⟨172335729920,2998966⟩ E) ⟨172335730048,2989781⟩ (N E ⟨172335730176,2980630⟩ E)) ⟨172335730304,2971515⟩ (N (N E ⟨172335730432,2962434⟩ E) ⟨172335730560,2953389⟩ (N E ⟨172335730688,2944377⟩ E))))))) ⟨172335730816,2935400⟩ (N (N (N (N (N (N (N E ⟨172335730944,2926458⟩ E) ⟨172335731072,2917549⟩ (N E ⟨172335731200,2908674⟩ E)) ⟨172335731328,2899833⟩ (N (N E ⟨172335731456,2891025⟩ E) ⟨172335731584,2882251⟩ (N E ⟨172335731712,2873511⟩ E))) ⟨172335731840,2864803⟩ (N (N (N E ⟨172335732096,2847486⟩ E) ⟨172335732224,2838877⟩ (N E ⟨172335732352,2830300⟩ E)) ⟨172335732480,2821756⟩ (N (N E ⟨172335732608,2813244⟩ E) ⟨172335732736,2804764⟩ (N E ⟨172335732864,2796316⟩ E)))) ⟨172335732992,2787899⟩ (N (N (N (N E ⟨172335733120,2779515⟩ E) ⟨172335733248,2771162⟩ (N E ⟨172335733376,2762840⟩ E)) ⟨172335733504,2754549⟩ (N (N E ⟨172335733632,2746290⟩ E) ⟨172335733760,2738062⟩ (N E ⟨172335734016,2721697⟩ E))) ⟨172335734144,2713560⟩ (N (N (N E ⟨172335734272,2705454⟩ E) ⟨172335734400,2697378⟩ (N E ⟨172335734528,2689333⟩ E)) ⟨172335734784,2673331⟩ (N (N E ⟨172469945344,14585475⟩ E) ⟨172469945472,14540176⟩ (N E ⟨172469945600,14495053⟩ E))))) ⟨172469945728,14450104⟩ (N (N (N (N (N E ⟨172469945856,14405330⟩ E) ⟨172469945984,14360729⟩ (N E ⟨172469946112,14316301⟩ E)) ⟨172469946240,14272044⟩ (N (N E ⟨172469946368,14227959⟩ E) ⟨172469946496,14184043⟩ (N E ⟨172469946624,14140297⟩ E))) ⟨172469946752,14096720⟩ (N (N (N E ⟨172469946880,14053310⟩ E) ⟨172469947008,14010067⟩ (N E ⟨172469947136,13966991⟩ E)) ⟨172469947264,13924080⟩ (N (N E ⟨172469947392,13881334⟩ E) ⟨172469947520,13838751⟩ (N E ⟨172469947648,13796332⟩ E)))) ⟨172469947776,13754076⟩ (N (N (N (N E ⟨172469947904,13711981⟩ E) ⟨172469948032,13670047⟩ (N E ⟨172469948160,13628274⟩ E)) ⟨172469948288,13586660⟩ (N (N E ⟨172469948416,13545204⟩ E) ⟨172469948544,13503907⟩ (N E ⟨172469948672,13462767⟩ E))) ⟨172469948800,13421784⟩ (N (N (N E ⟨172469948928,13380956⟩ E) ⟨172469949056,13340284⟩ (N E ⟨172469949184,13299766⟩ E)) ⟨172469949312,13259402⟩ (N (N E ⟨172469949440,13219191⟩ E) ⟨172469949568,13179133⟩ (N E ⟨172469949696,13139226⟩ E)))))) ⟨172469949824,13099470⟩ (N (N (N (N (N (N E ⟨172469950080,13020409⟩ E) ⟨172469950208,12981102⟩ (N E ⟨172469950336,12941943⟩ E)) ⟨172469950464,12902932⟩ (N (N E ⟨172469950592,12864067⟩ E) ⟨172469950720,12825350⟩ (N E ⟨172469950848,12786777⟩ E))) ⟨172469951744,12520793⟩ (N (N (N E ⟨172469952000,12446072⟩ E) ⟨172469952384,12335031⟩ (N E ⟨172469952512,12298293⟩ E)) ⟨172604163328,34128757⟩ (N (N E ⟨172604163456,34022926⟩ E) ⟨172604163584,33917505⟩ (N E ⟨172604163712,33812491⟩ E)))) ⟨172604163840,33707884⟩ (N (N (N (N E ⟨172604163968,33603682⟩ E) ⟨172604164096,33499882⟩ (N E ⟨172604164224,33396482⟩ E)) ⟨172604164352,33293481⟩ (N (N E ⟨172604164480,33190878⟩ E) ⟨172604164608,33088669⟩ (N E ⟨172604164736,32986854⟩ E))) ⟨172604164864,32885430⟩ (N (N (N E ⟨172604164992,32784395⟩ E) ⟨172604165120,32683749⟩ (N E ⟨172604165248,32583489⟩ E)) ⟨172604165376,32483613⟩ (N (N E ⟨172604165504,32384119⟩ E) ⟨172604165632,32285007⟩ (N E ⟨172604165760,32186273⟩ E))))) ⟨172604165888,32087917⟩ (N (N (N (N (N E ⟨172604166016,31989936⟩ E) ⟨172604166144,31892329⟩ (N E ⟨172604166272,31795094⟩ E)) ⟨172604166400,31698230⟩ (N (N E ⟨172604166528,31601734⟩ E) ⟨172604166656,31505605⟩ (N E ⟨172604166784,31409842⟩ E))) ⟨172604166912,31314443⟩ (N (N (N E ⟨172604167040,31219405⟩ E) ⟨172604167168,31124728⟩ (N E ⟨172604167296,31030410⟩ E)) ⟨172604167424,30936449⟩ (N (N E ⟨172604167552,30842843⟩ E) ⟨172604167680,30749591⟩ (N E ⟨172604167808,30656692⟩ E)))) ⟨172604167936,30564143⟩ (N (N (N (N E ⟨172604168064,30471943⟩ E) ⟨172604168320,30288585⟩ (N E ⟨172604168448,30197423⟩ E)) ⟨172604168576,30106604⟩ (N (N E ⟨172604168704,30016127⟩ E) ⟨172604168832,29925989⟩ (N E ⟨172604168960,29836189⟩ E))) ⟨172604169088,29746726⟩ (N (N (N E ⟨172604169216,29657598⟩ E) ⟨172604169600,29392211⟩ (N E ⟨172604169856,29216935⟩ E)) ⟨172604169984,29129787⟩ (N (N E ⟨172604170240,28956464⟩ E) ⟨172738381184,61885991⟩ (N E ⟨172738381312,61694234⟩ E))))))))

noncomputable def tab12 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨172738381568,61312946⟩ E) ⟨172738381696,61123406⟩ E) ⟨172738381824,60934599⟩ (N E ⟨172738381952,60746521⟩ E)) ⟨172738382080,60559168⟩ (N (N E ⟨172738382208,60372537⟩ E) ⟨172738382336,60186624⟩ (N E ⟨172738382464,60001427⟩ E))) ⟨172738382592,59816942⟩ (N (N (N E ⟨172738382720,59633166⟩ E) ⟨172738382848,59450095⟩ (N E ⟨172738382976,59267727⟩ E)) ⟨172738383104,59086058⟩ (N (N E ⟨172738383232,58905084⟩ E) ⟨172738383360,58724803⟩ (N E ⟨172738383488,58545211⟩ E)))) ⟨172738383616,58366306⟩ (N (N (N (N E ⟨172738383744,58188084⟩ E) ⟨172738383872,58010542⟩ (N E ⟨172738384000,57833677⟩ E)) ⟨172738384128,57657485⟩ (N (N E ⟨172738384256,57481964⟩ E) ⟨172738384384,57307111⟩ (N E ⟨172738384512,57132923⟩ E))) ⟨172738384640,56959396⟩ (N (N (N E ⟨172738384768,56786527⟩ E) ⟨172738384896,56614314⟩ (N E ⟨172738385024,56442754⟩ E)) ⟨172738385152,56271844⟩ (N (N E ⟨172738385280,56101580⟩ E) ⟨172738385408,55931959⟩ (N E ⟨172738385536,55762980⟩ E))))) ⟨172738385664,55594638⟩ (N (N (N (N (N E ⟨172738385920,55259857⟩ E) ⟨172738386176,54927594⟩ (N E ⟨172738386304,54762398⟩ E)) ⟨172738386432,54597824⟩ (N (N E ⟨172738386560,54433868⟩ E) ⟨172738386944,53945679⟩ (N E ⟨172738387072,53784167⟩ E))) ⟨172738387328,53462953⟩ (N (N (N E ⟨172738387456,53303246⟩ E) ⟨172738387584,53144135⟩ (N E ⟨172738387712,52985617⟩ E)) ⟨172738387840,52827690⟩ (N (N E ⟨172738387968,52670351⟩ E) ⟨172872599040,97756897⟩ (N E ⟨172872599168,97454229⟩ E)))) ⟨172872599296,97152731⟩ (N (N (N (N E ⟨172872599424,96852398⟩ E) ⟨172872599552,96553226⟩ (N E ⟨172872599680,96255209⟩ E)) ⟨172872599808,95958340⟩ (N (N E ⟨172872599936,95662616⟩ E) ⟨172872600064,95368031⟩ (N E ⟨172872600192,95074579⟩ E))) ⟨172872600320,94782256⟩ (N (N (N E ⟨172872600448,94491055⟩ E) ⟨172872600576,94200972⟩ (N E ⟨172872600704,93912003⟩ E)) ⟨172872600832,93624140⟩ (N (N E ⟨172872600960,93337381⟩ E) ⟨172872601088,93051719⟩ (N E ⟨172872601216,92767149⟩ E)))))) ⟨172872601344,92483667⟩ (N (N (N (N (N (N E ⟨172872601472,92201267⟩ E) ⟨172872601600,91919944⟩ (N E ⟨172872601728,91639694⟩ E)) ⟨172872601856,91360512⟩ (N (N E ⟨172872601984,91082393⟩ E) ⟨172872602112,90805331⟩ (N E ⟨172872602240,90529323⟩ E))) ⟨172872602368,90254363⟩ (N (N (N E ⟨172872602496,89980446⟩ E) ⟨172872602624,89707568⟩ (N E ⟨172872602752,89435724⟩ E)) ⟨172872602880,89164910⟩ (N (N E ⟨172872603008,88895120⟩ E) ⟨172872603136,88626350⟩ (N E ⟨172872603264,88358596⟩ E)))) ⟨172872603392,88091852⟩ (N (N (N (N E ⟨172872603520,87826114⟩ E) ⟨172872603776,87297640⟩ (N E ⟨172872604032,86773136⟩ E)) ⟨172872604160,86512361⟩ (N (N E ⟨172872604288,86252566⟩ E) ⟨172872604416,85993746⟩ (N E ⟨172872604544,85735896⟩ E))) ⟨172872604928,84968126⟩ (N (N (N E ⟨172872605184,84461052⟩ E) ⟨172872605696,83458205⟩ (N E ⟨173006817024,141243500⟩ E)) ⟨173006817152,140806868⟩ (N (N E ⟨173006817280,140371923⟩ E) ⟨173006817408,139938656⟩ (N E ⟨173006817536,139507060⟩ E))))) ⟨173006817664,139077128⟩ (N (N (N (N (N E ⟨173006817792,138648851⟩ E) ⟨173006817920,138222222⟩ (N E ⟨173006818048,137797234⟩ E)) ⟨173006818176,137373878⟩ (N (N E ⟨173006818304,136952147⟩ E) ⟨173006818432,136532034⟩ (N E ⟨173006818560,136113532⟩ E))) ⟨173006818688,135696632⟩ (N (N (N E ⟨173006818816,135281328⟩ E) ⟨173006818944,134867612⟩ (N E ⟨173006819072,134455477⟩ E)) ⟨173006819200,134044916⟩ (N (N E ⟨173006819328,133635921⟩ E) ⟨173006819456,133228486⟩ (N E ⟨173006819584,132822602⟩ E)))) ⟨173006819712,132418264⟩ (N (N (N (N E ⟨173006819840,132015464⟩ E) ⟨173006819968,131614195⟩ (N E ⟨173006820096,131214450⟩ E)) ⟨173006820224,130816221⟩ (N (N E ⟨173006820352,130419504⟩ E) ⟨173006820480,130024289⟩ (N E ⟨173006820608,129630571⟩ E))) ⟨173006820736,129238342⟩ (N (N (N E ⟨173006820864,128847597⟩ E) ⟨173006820992,128458327⟩ (N E ⟨173006821120,128070528⟩ E)) ⟨173006821248,127684191⟩ (N (N E ⟨173006821376,127299310⟩ E) ⟨173006821504,126915879⟩ (N E ⟨173006821632,126533891⟩ E))))))) ⟨173006821888,125774218⟩ (N (N (N (N (N (N (N E ⟨173006822016,125396520⟩ E) ⟨173006822144,125020240⟩ (N E ⟨173006822656,123529163⟩ E)) ⟨173006822784,123159874⟩ (N (N E ⟨173006823040,122425427⟩ E) ⟨173006823296,121696449⟩ (N E ⟨173006823424,121333996⟩ E))) ⟨173141034880,192998032⟩ (N (N (N E ⟨173141035008,192401870⟩ E) ⟨173141035136,191808010⟩ (N E ⟨173141035264,191216440⟩ E)) ⟨173141035392,190627150⟩ (N (N E ⟨173141035520,190040129⟩ E) ⟨173141035648,189455366⟩ (N E ⟨173141035776,188872852⟩ E)))) ⟨173141035904,188292576⟩ (N (N (N (N E ⟨173141036032,187714528⟩ E) ⟨173141036160,187138697⟩ (N E ⟨173141036288,186565073⟩ E)) ⟨173141036416,185993647⟩ (N (N E ⟨173141036544,185424407⟩ E) ⟨173141036672,184857344⟩ (N E ⟨173141036800,184292448⟩ E))) ⟨173141036928,183729709⟩ (N (N (N E ⟨173141037056,183169117⟩ E) ⟨173141037184,182610663⟩ (N E ⟨173141037312,182054335⟩ E)) ⟨173141037440,181500126⟩ (N (N E ⟨173141037568,180948025⟩ E) ⟨173141037696,180398022⟩ (N E ⟨173141037824,179850108⟩ E))))) ⟨173141037952,179304274⟩ (N (N (N (N (N E ⟨173141038080,178760509⟩ E) ⟨173141038208,178218805⟩ (N E ⟨173141038336,177679153⟩ E)) ⟨173141038464,177141542⟩ (N (N E ⟨173141038592,176605963⟩ E) ⟨173141038720,176072408⟩ (N E ⟨173141038848,175540867⟩ E))) ⟨173141038976,175011331⟩ (N (N (N E ⟨173141039232,173958239⟩ E) ⟨173141039360,173434664⟩ (N E ⟨173141039488,172913058⟩ E)) ⟨173141039616,172393412⟩ (N (N E ⟨173141039744,171875718⟩ E) ⟨173141039872,171359966⟩ (N E ⟨173141040000,170846148⟩ E)))) ⟨173141040128,170334255⟩ (N (N (N (N E ⟨173141040384,169316210⟩ E) ⟨173141040512,168810041⟩ (N E ⟨173141040640,168305763⟩ E)) ⟨173141041152,166307388⟩ (N (N E ⟨173275252736,252649249⟩ E) ⟨173275252864,251869431⟩ (N E ⟨173275252992,251092621⟩ E))) ⟨173275253120,250318805⟩ (N (N (N E ⟨173275253248,249547968⟩ E) ⟨173275253376,248780098⟩ (N E ⟨173275253504,248015179⟩ E)) ⟨173275253632,247253200⟩ (N (N E ⟨173275253760,246494146⟩ E) ⟨173275253888,245738003⟩ (N E ⟨173275254016,244984759⟩ E)))))) ⟨173275254144,244234399⟩ (N (N (N (N (N (N E ⟨173275254272,243486912⟩ E) ⟨173275254400,242742283⟩ (N E ⟨173275254528,242000499⟩ E)) ⟨173275254656,241261548⟩ (N (N E ⟨173275254784,240525416⟩ E) ⟨173275254912,239792091⟩ (N E ⟨173275255040,239061560⟩ E))) ⟨173275255168,238333809⟩ (N (N (N E ⟨173275255296,237608827⟩ E) ⟨173275255424,236886600⟩ (N E ⟨173275255552,236167116⟩ E)) ⟨173275255680,235450363⟩ (N (N E ⟨173275255808,234736328⟩ E) ⟨173275255936,234024998⟩ (N E ⟨173275256064,233316362⟩ E)))) ⟨173275256192,232610408⟩ (N (N (N (N E ⟨173275256320,231907122⟩ E) ⟨173275256448,231206493⟩ (N E ⟨173275256576,230508509⟩ E)) ⟨173275256704,229813158⟩ (N (N E ⟨173275256832,229120428⟩ E) ⟨173275256960,228430308⟩ (N E ⟨173275257088,227742784⟩ E))) ⟨173275257216,227057846⟩ (N (N (N E ⟨173275257472,225695681⟩ E) ⟨173275257600,225018430⟩ (N E ⟨173275257728,224343719⟩ E)) ⟨173275257856,223671535⟩ (N (N E ⟨173275257984,223001869⟩ E) ⟨173275258112,222334707⟩ (N E ⟨173275258240,221670039⟩ E))))) ⟨173275258496,220348142⟩ (N (N (N (N (N E ⟨173275258624,219690889⟩ E) ⟨173275258752,219036086⟩ (N E ⟨173275258880,218383722⟩ E)) ⟨173409470720,319136758⟩ (N (N E ⟨173409470848,318153244⟩ E) ⟨173409470976,317173516⟩ (N E ⟨173409471104,316197559⟩ E))) ⟨173409471232,315225354⟩ (N (N (N E ⟨173409471360,314256884⟩ E) ⟨173409471488,313292131⟩ (N E ⟨173409471616,312331080⟩ E)) ⟨173409471744,311373712⟩ (N (N E ⟨173409471872,310420012⟩ E) ⟨173409472000,309469961⟩ (N E ⟨173409472128,308523543⟩ E)))) ⟨173409472256,307580742⟩ (N (N (N (N E ⟨173409472384,306641541⟩ E) ⟨173409472512,305705923⟩ (N E ⟨173409472640,304773873⟩ E)) ⟨173409472768,303845373⟩ (N (N E ⟨173409472896,302920407⟩ E) ⟨173409473024,301998961⟩ (N E ⟨173409473152,301081016⟩ E))) ⟨173409473280,300166558⟩ (N (N (N E ⟨173409473408,299255570⟩ E) ⟨173409473536,298348037⟩ (N E ⟨173409473792,296543272⟩ E)) ⟨173409473920,295646009⟩ (N (N E ⟨173409474048,294752139⟩ E) ⟨173409474176,293861645⟩ (N E ⟨173409474304,292974513⟩ E))))))))

noncomputable def tab13 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨173409474560,291210273⟩ E) ⟨173409474688,290333135⟩ E) ⟨173409474816,289459298⟩ (N E ⟨173409474944,288588747⟩ E)) ⟨173409475072,287721468⟩ (N (N E ⟨173409475200,286857445⟩ E) ⟨173409475456,285139112⟩ (N E ⟨173409475584,284284772⟩ E))) ⟨173409475840,282585674⟩ (N (N (N E ⟨173409475968,281740887⟩ E) ⟨173409476480,278393153⟩ (N E ⟨173409476608,277564003⟩ E)) ⟨173543688576,394126626⟩ (N (N E ⟨173543688704,392912944⟩ E) ⟨173543688832,391703933⟩ (N E ⟨173543688960,390499570⟩ E)))) ⟨173543689088,389299835⟩ (N (N (N (N E ⟨173543689216,388104705⟩ E) ⟨173543689344,386914159⟩ (N E ⟨173543689472,385728177⟩ E)) ⟨173543689600,384546737⟩ (N (N E ⟨173543689728,383369819⟩ E) ⟨173543689856,382197402⟩ (N E ⟨173543689984,381029465⟩ E))) ⟨173543690112,379865987⟩ (N (N (N E ⟨173543690240,378706948⟩ E) ⟨173543690368,377552329⟩ (N E ⟨173543690496,376402108⟩ E)) ⟨173543690624,375256266⟩ (N (N E ⟨173543690752,374114782⟩ E) ⟨173543690880,372977637⟩ (N E ⟨173543691008,371844811⟩ E))))) ⟨173543691136,370716284⟩ (N (N (N (N (N E ⟨173543691264,369592036⟩ E) ⟨173543691392,368472049⟩ (N E ⟨173543691520,367356303⟩ E)) ⟨173543691648,366244778⟩ (N (N E ⟨173543691776,365137455⟩ E) ⟨173543691904,364034316⟩ (N E ⟨173543692032,362935342⟩ E))) ⟨173543692160,361840512⟩ (N (N (N E ⟨173543692288,360749810⟩ E) ⟨173543692416,359663216⟩ (N E ⟨173543692544,358580711⟩ E)) ⟨173543692672,357502277⟩ (N (N E ⟨173543692800,356427896⟩ E) ⟨173543692928,355357550⟩ (N E ⟨173543693056,354291219⟩ E)))) ⟨173543693184,353228887⟩ (N (N (N (N E ⟨173543693312,352170535⟩ E) ⟨173543693440,351116146⟩ (N E ⟨173543693568,350065701⟩ E)) ⟨173543693696,349019183⟩ (N (N E ⟨173543693952,346937856⟩ E) ⟨173543694080,345903013⟩ (N E ⟨173543694208,344872027⟩ E))) ⟨173543694336,343844881⟩ (N (N (N E ⟨173677906560,475290434⟩ E) ⟨173677906688,473829070⟩ (N E ⟨173677906816,472373320⟩ E)) ⟨173677906944,470923159⟩ (N (N E ⟨173677907072,469478560⟩ E) ⟨173677907200,468039499⟩ (N E ⟨173677907328,466605949⟩ E)))))) ⟨173677907456,465177886⟩ (N (N (N (N (N (N E ⟨173677907584,463755284⟩ E) ⟨173677907712,462338118⟩ (N E ⟨173677907840,460926364⟩ E)) ⟨173677907968,459519996⟩ (N (N E ⟨173677908096,458118990⟩ E) ⟨173677908224,456723321⟩ (N E ⟨173677908352,455332965⟩ E))) ⟨173677908480,453947898⟩ (N (N (N E ⟨173677908608,452568095⟩ E) ⟨173677908736,451193533⟩ (N E ⟨173677908864,449824187⟩ E)) ⟨173677908992,448460034⟩ (N (N E ⟨173677909120,447101051⟩ E) ⟨173677909248,445747213⟩ (N E ⟨173677909376,444398497⟩ E)))) ⟨173677909504,443054881⟩ (N (N (N (N E ⟨173677909632,441716341⟩ E) ⟨173677909760,440382854⟩ (N E ⟨173677909888,439054397⟩ E)) ⟨173677910016,437730947⟩ (N (N E ⟨173677910272,435098980⟩ E) ⟨173677910400,433790417⟩ (N E ⟨173677910656,431188021⟩ E))) ⟨173677911040,427320924⟩ (N (N (N E ⟨173677911168,426041536⟩ E) ⟨173677911296,424766934⟩ (N E ⟨173677911424,423497097⟩ E)) ⟨173677911552,422232004⟩ (N (N E ⟨173677911808,419715962⟩ E) ⟨173677911936,418464972⟩ (N E ⟨173677912064,417218641⟩ E))))) ⟨173812124416,565200125⟩ (N (N (N (N (N E ⟨173812124544,563463655⟩ E) ⟨173812124672,561733851⟩ (N E ⟨173812124800,560010683⟩ E)) ⟨173812124928,558294119⟩ (N (N E ⟨173812125056,556584131⟩ E) ⟨173812125184,554880686⟩ (N E ⟨173812125312,553183756⟩ E))) ⟨173812125440,551493311⟩ (N (N (N E ⟨173812125568,549809320⟩ E) ⟨173812125696,548131754⟩ (N E ⟨173812125824,546460584⟩ E)) ⟨173812125952,544795781⟩ (N (N E ⟨173812126080,543137315⟩ E) ⟨173812126208,541485158⟩ (N E ⟨173812126336,539839280⟩ E)))) ⟨173812126464,538199653⟩ (N (N (N (N E ⟨173812126592,536566249⟩ E) ⟨173812126720,534939039⟩ (N E ⟨173812126848,533317995⟩ E)) ⟨173812126976,531703090⟩ (N (N E ⟨173812127104,530094294⟩ E) ⟨173812127232,528491581⟩ (N E ⟨173812127360,526894923⟩ E))) ⟨173812127488,525304292⟩ (N (N (N E ⟨173812127616,523719661⟩ E) ⟨173812127744,522141004⟩ (N E ⟨173812128000,519001499⟩ E)) ⟨173812128128,517440599⟩ (N (N E ⟨173812128256,515885565⟩ E) ⟨173812128384,514336370⟩ (N E ⟨173812128768,509723558⟩ E))))))) ⟨173812129024,506677069⟩ (N (N (N (N (N (N (N E ⟨173812129152,505162362⟩ E) ⟨173812129280,503653314⟩ (N E ⟨173812129536,500652090⟩ E)) ⟨173812129664,499159865⟩ (N (N E ⟨173812129792,497673197⟩ E) ⟨173946342272,662552199⟩ (N E ⟨173946342400,660518198⟩ E))) ⟨173946342528,658492000⟩ (N (N (N E ⟨173946342656,656473569⟩ E) ⟨173946342784,654462868⟩ (N E ⟨173946342912,652459862⟩ E)) ⟨173946343040,650464517⟩ (N (N E ⟨173946343168,648476796⟩ E) ⟨173946343296,646496665⟩ (N E ⟨173946343424,644524089⟩ E)))) ⟨173946343552,642559034⟩ (N (N (N (N E ⟨173946343680,640601464⟩ E) ⟨173946343808,638651347⟩ (N E ⟨173946343936,636708648⟩ E)) ⟨173946344064,634773332⟩ (N (N E ⟨173946344192,632845367⟩ E) ⟨173946344320,630924719⟩ (N E ⟨173946344448,629011354⟩ E))) ⟨173946344576,627105240⟩ (N (N (N E ⟨173946344704,625206343⟩ E) ⟨173946344832,623314631⟩ (N E ⟨173946344960,621430071⟩ E)) ⟨173946345088,619552631⟩ (N (N E ⟨173946345216,617682278⟩ E) ⟨173946345344,615818980⟩ (N E ⟨173946345472,613962706⟩ E))))) ⟨173946345600,612113423⟩ (N (N (N (N (N E ⟨173946345728,610271100⟩ E) ⟨173946345856,608435706⟩ (N E ⟨173946345984,606607209⟩ E)) ⟨173946346112,604785579⟩ (N (N E ⟨173946346624,597567103⟩ E) ⟨173946346752,595779343⟩ (N E ⟨173946346880,593998266⟩ E))) ⟨173946347008,592223842⟩ (N (N (N E ⟨173946347264,588694835⟩ E) ⟨173946347520,585192084⟩ (N E ⟨174080560128,767252671⟩ E)) ⟨174080560256,764899055⟩ (N (N E ⟨174080560384,762554461⟩ E) ⟨174080560512,760218847⟩ (N E ⟨174080560640,757892172⟩ E)))) ⟨174080560768,755574395⟩ (N (N (N (N E ⟨174080560896,753265474⟩ E) ⟨174080561024,750965370⟩ (N E ⟨174080561152,748674041⟩ E)) ⟨174080561280,746391449⟩ (N (N E ⟨174080561408,744117552⟩ E) ⟨174080561536,741852311⟩ (N E ⟨174080561664,739595687⟩ E))) ⟨174080561792,737347640⟩ (N (N (N E ⟨174080561920,735108131⟩ E) ⟨174080562048,732877121⟩ (N E ⟨174080562176,730654572⟩ E)) ⟨174080562304,728440445⟩ (N (N E ⟨174080562432,726234702⟩ E) ⟨174080562560,724037304⟩ (N E ⟨174080562688,721848214⟩ E)))))) ⟨174080562816,719667394⟩ (N (N (N (N (N (N E ⟨174080562944,717494807⟩ E) ⟨174080563072,715330415⟩ (N E ⟨174080563328,711026070⟩ E)) ⟨174080563456,708886043⟩ (N (N E ⟨174080563584,706754063⟩ E) ⟨174080563712,704630096⟩ (N E ⟨174080563840,702514105⟩ E))) ⟨174080563968,700406053⟩ (N (N (N E ⟨174080564096,698305905⟩ E) ⟨174080564352,694129181⟩ (N E ⟨174080564480,692052533⟩ E)) ⟨174080564608,689983648⟩ (N (N E ⟨174080564736,687922492⟩ E) ⟨174080564864,685869029⟩ (N E ⟨174080564992,683823225⟩ E)))) ⟨174080565120,681785046⟩ (N (N (N (N E ⟨174080565248,679754458⟩ E) ⟨174214777984,879203461⟩ (N E ⟨174214778112,876508497⟩ E)) ⟨174214778240,873823856⟩ (N (N E ⟨174214778368,871149488⟩ E) ⟨174214778496,868485349⟩ (N E ⟨174214778624,865831389⟩ E))) ⟨174214778752,863187564⟩ (N (N (N E ⟨174214778880,860553826⟩ E) ⟨174214779008,857930129⟩ (N E ⟨174214779136,855316427⟩ E)) ⟨174214779264,852712675⟩ (N (N E ⟨174214779392,850118827⟩ E) ⟨174214779520,847534838⟩ (N E ⟨174214779648,844960663⟩ E))))) ⟨174214779776,842396257⟩ (N (N (N (N (N E ⟨174214779904,839841577⟩ E) ⟨174214780032,837296576⟩ (N E ⟨174214780160,834761213⟩ E)) ⟨174214780288,832235442⟩ (N (N E ⟨174214780416,829719221⟩ E) ⟨174214780544,827212505⟩ (N E ⟨174214780672,824715253⟩ E))) ⟨174214780800,822227420⟩ (N (N (N E ⟨174214780928,819748965⟩ E) ⟨174214781056,817279845⟩ (N E ⟨174214781184,814820018⟩ E)) ⟨174214781312,812369442⟩ (N (N E ⟨174214781568,807495875⟩ E) ⟨174214781696,805072802⟩ (N E ⟨174214781824,802658814⟩ E)))) ⟨174214781952,800253871⟩ (N (N (N (N E ⟨174214782208,795470955⟩ E) ⟨174214782336,793092902⟩ (N E ⟨174214782464,790723732⟩ E)) ⟨174214782592,788363405⟩ (N (N E ⟨174214782720,786011882⟩ E) ⟨174214782848,783669123⟩ (N E ⟨174214782976,781335090⟩ E))) ⟨174348995840,998302463⟩ (N (N (N E ⟨174348995968,995244781⟩ E) ⟨174348996096,992198801⟩ (N E ⟨174348996224,989164469⟩ E)) ⟨174348996352,986141733⟩ (N (N E ⟨174348996480,983130539⟩ E) ⟨174348996608,980130833⟩ (N E ⟨174348996736,977142564⟩ E))))))))

noncomputable def tab14 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨174348996992,971200127⟩ E) ⟨174348997120,968245854⟩ E) ⟨174348997248,965302811⟩ (N E ⟨174348997376,962370945⟩ E)) ⟨174348997504,959450206⟩ (N (N E ⟨174348997632,956540544⟩ E) ⟨174348997760,953641907⟩ (N E ⟨174348997888,950754245⟩ E))) ⟨174348998016,947877510⟩ (N (N (N E ⟨174348998144,945011651⟩ E) ⟨174348998272,942156618⟩ (N E ⟨174348998400,939312363⟩ E)) ⟨174348998528,936478838⟩ (N (N E ⟨174348998784,930843780⟩ E) ⟨174348998912,928042151⟩ (N E ⟨174348999168,922470454⟩ E)))) ⟨174348999296,919700292⟩ (N (N (N (N E ⟨174348999552,914191105⟩ E) ⟨174348999680,911451986⟩ (N E ⟨174348999808,908723122⟩ E)) ⟨174348999936,906004467⟩ (N (N E ⟨174349000064,903295975⟩ E) ⟨174349000192,900597600⟩ (N E ⟨174349000320,897909298⟩ E))) ⟨174349000448,895231022⟩ (N (N (N E ⟨174349000576,892562729⟩ E) ⟨174349000704,889904373⟩ (N E ⟨174483213696,1124443620⟩ E)) ⟨174483213824,1121002223⟩ (N (N E ⟨174483213952,1117573986⟩ E) ⟨174483214080,1114158849⟩ (N E ⟨174483214208,1110756753⟩ E))))) ⟨174483214336,1107367638⟩ (N (N (N (N (N E ⟨174483214464,1103991443⟩ E) ⟨174483214592,1100628111⟩ (N E ⟨174483214720,1097277581⟩ E)) ⟨174483214848,1093939797⟩ (N (N E ⟨174483214976,1090614699⟩ E) ⟨174483215104,1087302230⟩ (N E ⟨174483215232,1084002332⟩ E))) ⟨174483215360,1080714948⟩ (N (N (N E ⟨174483215488,1077440021⟩ E) ⟨174483215616,1074177495⟩ (N E ⟨174483215744,1070927312⟩ E)) ⟨174483215872,1067689418⟩ (N (N E ⟨174483216000,1064463756⟩ E) ⟨174483216128,1061250272⟩ (N E ⟨174483216256,1058048909⟩ E)))) ⟨174483216384,1054859613⟩ (N (N (N (N E ⟨174483216512,1051682329⟩ E) ⟨174483216640,1048517003⟩ (N E ⟨174483216768,1045363582⟩ E)) ⟨174483216896,1042222011⟩ (N (N E ⟨174483217024,1039092237⟩ E) ⟨174483217152,1035974207⟩ (N E ⟨174483217280,1032867868⟩ E))) ⟨174483217408,1029773167⟩ (N (N (N E ⟨174483217664,1023618472⟩ E) ⟨174483217792,1020558374⟩ (N E ⟨174483218304,1008431780⟩ E)) ⟨174483218432,1005428326⟩ (N (N E ⟨174617431552,1257516997⟩ E) ⟨174617431680,1253671273⟩ (N E ⟨174617431808,1249840244⟩ E)))))) ⟨174617431936,1246023843⟩ (N (N (N (N (N (N E ⟨174617432064,1242222003⟩ E) ⟨174617432192,1238434658⟩ (N E ⟨174617432320,1234661742⟩ E)) ⟨174617432448,1230903188⟩ (N (N E ⟨174617432576,1227158930⟩ E) ⟨174617432704,1223428905⟩ (N E ⟨174617432832,1219713046⟩ E))) ⟨174617432960,1216011289⟩ (N (N (N E ⟨174617433088,1212323570⟩ E) ⟨174617433216,1208649825⟩ (N E ⟨174617433344,1204989991⟩ E)) ⟨174617433472,1201344004⟩ (N (N E ⟨174617433600,1197711801⟩ E) ⟨174617433728,1194093321⟩ (N E ⟨174617433856,1190488501⟩ E)))) ⟨174617433984,1186897278⟩ (N (N (N (N E ⟨174617434112,1183319592⟩ E) ⟨174617434240,1179755381⟩ (N E ⟨174617434368,1176204585⟩ E)) ⟨174617434496,1172667142⟩ (N (N E ⟨174617434624,1169142993⟩ E) ⟨174617434880,1162134337⟩ (N E ⟨174617435008,1158649710⟩ E))) ⟨174617435136,1155178139⟩ (N (N (N E ⟨174617435264,1151719565⟩ E) ⟨174617435392,1148273930⟩ (N E ⟨174617435648,1141421244⟩ E)) ⟨174617436160,1127868602⟩ (N (N E ⟨174751649408,1397408863⟩ E) ⟨174751649536,1393138594⟩ (N E ⟨174751649664,1388884630⟩ E))))) ⟨174751649792,1384646897⟩ (N (N (N (N (N E ⟨174751649920,1380425320⟩ E) ⟨174751650048,1376219826⟩ (N E ⟨174751650176,1372030341⟩ E)) ⟨174751650304,1367856792⟩ (N (N E ⟨174751650432,1363699107⟩ E) ⟨174751650560,1359557212⟩ (N E ⟨174751650688,1355431036⟩ E))) ⟨174751650816,1351320508⟩ (N (N (N E ⟨174751650944,1347225556⟩ E) ⟨174751651072,1343146110⟩ (N E ⟨174751651200,1339082098⟩ E)) ⟨174751651328,1335033452⟩ (N (N E ⟨174751651456,1331000101⟩ E) ⟨174751651584,1326981976⟩ (N E ⟨174751651712,1322979007⟩ E)))) ⟨174751651840,1318991128⟩ (N (N (N (N E ⟨174751651968,1315018268⟩ E) ⟨174751652096,1311060361⟩ (N E ⟨174751652352,1303189135⟩ E)) ⟨174751652480,1299275681⟩ (N (N E ⟨174751652736,1291492761⟩ E) ⟨174751652864,1287623163⟩ (N E ⟨174751653248,1276101033⟩ E))) ⟨174751653376,1272288995⟩ (N (N (N E ⟨174751653632,1264707542⟩ E) ⟨174751653888,1257182497⟩ (N E ⟨174885867264,1544001766⟩ E)) ⟨174885867392,1539287140⟩ (N (N E ⟨174885867520,1534590502⟩ E) ⟨174885867648,1529911770⟩ (N E ⟨174885867776,1525250863⟩ E))))))) ⟨174885867904,1520607698⟩ (N (N (N (N (N (N (N E ⟨174885868032,1515982195⟩ E) ⟨174885868160,1511374273⟩ (N E ⟨174885868288,1506783852⟩ E)) ⟨174885868416,1502210852⟩ (N (N E ⟨174885868544,1497655194⟩ E) ⟨174885868672,1493116799⟩ (N E ⟨174885868800,1488595589⟩ E))) ⟨174885868928,1484091485⟩ (N (N (N E ⟨174885869056,1479604410⟩ E) ⟨174885869184,1475134287⟩ (N E ⟨174885869312,1470681038⟩ E)) ⟨174885869440,1466244588⟩ (N (N E ⟨174885869568,1461824860⟩ E) ⟨174885869696,1457421779⟩ (N E ⟨174885869824,1453035270⟩ E)))) ⟨174885869952,1448665257⟩ (N (N (N (N E ⟨174885870080,1444311667⟩ E) ⟨174885870208,1439974425⟩ (N E ⟨174885870336,1435653458⟩ E)) ⟨174885870464,1431348692⟩ (N (N E ⟨174885870592,1427060055⟩ E) ⟨174885870848,1418530876⟩ (N E ⟨174885870976,1414290191⟩ E))) ⟨174885871104,1410065347⟩ (N (N (N E ⟨174885871232,1405856272⟩ E) ⟨174885871488,1397485151⟩ (N E ⟨174885871616,1393322965⟩ E)) ⟨175020085248,1691996236⟩ (N (N E ⟨175020085504,1681698613⟩ E) ⟨175020085632,1676579190⟩ (N E ⟨175020085760,1671479241⟩ E))))) ⟨175020085888,1666398676⟩ (N (N (N (N (N E ⟨175020086016,1661337407⟩ E) ⟨175020086144,1656295346⟩ (N E ⟨175020086272,1651272406⟩ E)) ⟨175020086400,1646268500⟩ (N (N E ⟨175020086528,1641283541⟩ E) ⟨175020086656,1636317443⟩ (N E ⟨175020086784,1631370121⟩ E))) ⟨175020086912,1626441489⟩ (N (N (N E ⟨175020087040,1621531463⟩ E) ⟨175020087168,1616639958⟩ (N E ⟨175020087296,1611766891⟩ E)) ⟨175020087424,1606912178⟩ (N (N E ⟨175020087552,1602075736⟩ E) ⟨175020087680,1597257483⟩ (N E ⟨175020087808,1592457337⟩ E)))) ⟨175020087936,1587675217⟩ (N (N (N (N E ⟨175020088064,1582911040⟩ E) ⟨175020088320,1573436196⟩ (N E ⟨175020088576,1564032164⟩ E)) ⟨175020088704,1559356504⟩ (N (N E ⟨175020088832,1554698310⟩ E) ⟨175020088960,1550057503⟩ (N E ⟨175020089216,1540827741⟩ E))) ⟨175020089344,1536238631⟩ (N (N (N E ⟨175154303104,1851141665⟩ E) ⟨175154303232,1845502124⟩ (N E ⟨175154303360,1839884051⟩ E)) ⟨175154303488,1834287348⟩ (N (N E ⟨175154303616,1828711918⟩ E) ⟨175154303744,1823157663⟩ (N E ⟨175154303872,1817624488⟩ E)))))) ⟨175154304000,1812112295⟩ (N (N (N (N (N (N E ⟨175154304128,1806620990⟩ E) ⟨175154304384,1795700664⟩ (N E ⟨175154304512,1790271455⟩ E)) ⟨175154304640,1784862757⟩ (N (N E ⟨175154304768,1779474476⟩ E) ⟨175154305152,1763431220⟩ (N E ⟨175154305280,1758123692⟩ E))) ⟨175154305408,1752836124⟩ (N (N (N E ⟨175154305536,1747568426⟩ E) ⟨175154305792,1737092285⟩ (N E ⟨175154305920,1731883663⟩ E)) ⟨175154306048,1726694557⟩ (N (N E ⟨175154306176,1721524877⟩ E) ⟨175154306304,1716374538⟩ (N E ⟨175154306432,1711243452⟩ E)))) ⟨175154306560,1706131533⟩ (N (N (N (N E ⟨175154306688,1701038695⟩ E) ⟨175154306944,1690909921⟩ (N E ⟨175154307072,1685873815⟩ E)) ⟨175288521216,2004341269⟩ (N (N E ⟨175288521344,1998248949⟩ E) ⟨175288521472,1992179768⟩ (N E ⟨175288521600,1986133620⟩ E))) ⟨175288521728,1980110401⟩ (N (N (N E ⟨175288521856,1974110006⟩ E) ⟨175288521984,1968132331⟩ (N E ⟨175288522112,1962177274⟩ E)) ⟨175288522240,1956244731⟩ (N (N E ⟨175288522368,1950334600⟩ E) ⟨175288522496,1944446781⟩ (N E ⟨175288522624,1938581171⟩ E))))) ⟨175288522752,1932737670⟩ (N (N (N (N (N E ⟨175288522880,1926916179⟩ E) ⟨175288523008,1921116598⟩ (N E ⟨175288523136,1915338828⟩ E)) ⟨175288523264,1909582771⟩ (N (N E ⟨175288523392,1903848328⟩ E) ⟨175288523520,1898135403⟩ (N E ⟨175288523648,1892443898⟩ E))) ⟨175288523776,1886773717⟩ (N (N (N E ⟨175288524032,1875496946⟩ E) ⟨175288524160,1869890165⟩ (N E ⟨175288524288,1864304328⟩ E)) ⟨175288524416,1858739341⟩ (N (N E ⟨175288524544,1853195110⟩ E) ⟨175288524672,1847671543⟩ (N E ⟨175288524800,1842168548⟩ E)))) ⟨175422739072,2174940096⟩ (N (N (N (N E ⟨175422739200,2168334260⟩ E) ⟨175422739328,2161753494⟩ (N E ⟨175422739456,2155197683⟩ E)) ⟨175422739584,2148666715⟩ (N (N E ⟨175422739712,2142160477⟩ E) ⟨175422739840,2135678855⟩ (N E ⟨175422739968,2129221739⟩ E))) ⟨175422740096,2122789017⟩ (N (N (N E ⟨175422740224,2116380579⟩ E) ⟨175422740352,2109996314⟩ (N E ⟨175422740480,2103636114⟩ E)) ⟨175422740608,2097299870⟩ (N (N E ⟨175422740736,2090987472⟩ E) ⟨175422740864,2084698814⟩ (N E ⟨175422741248,2065974211⟩ E))))))))

noncomputable def tab15 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨175422741632,2047459442⟩ E) ⟨175422741888,2035231444⟩ (N E ⟨175422742016,2029151691⟩ E)) ⟨175422742400,2011048186⟩ (N (N E ⟨175422742528,2005058599⟩ E) ⟨175556957184,2337300549⟩ (N E ⟨175556957440,2323161767⟩ E))) ⟨175556957568,2316132482⟩ (N (N (N E ⟨175556957696,2309129774⟩ E) ⟨175556957952,2295203603⟩ (N E ⟨175556958080,2288279902⟩ E)) ⟨175556958208,2281382298⟩ (N (N E ⟨175556958336,2274510674⟩ E) ⟨175556958464,2267664912⟩ (N E ⟨175556958592,2260844896⟩ E)))) ⟨175556958720,2254050509⟩ (N (N (N (N E ⟨175556958976,2240538162⟩ E) ⟨175556959104,2233819972⟩ (N E ⟨175556959616,2207197794⟩ E)) ⟨175556959744,2200604333⟩ (N (N E ⟨175556960128,2180971177⟩ E) ⟨175556960256,2174475502⟩ (N E ⟨175691175296,2503460747⟩ E))) ⟨175691175552,2488351170⟩ (N (N (N E ⟨175691175680,2480839145⟩ E) ⟨175691175936,2465899976⟩ (N E ⟨175691176064,2458472577⟩ E)) ⟨175691176320,2443701514⟩ (N (N E ⟨175691176448,2436357598⟩ E) ⟨175691176576,2429041260⟩ (N E ⟨175691176832,2414490820⟩ E))))) ⟨175691176960,2407256471⟩ (N (N (N (N (N E ⟨175691177216,2392868906⟩ E) ⟨175691177344,2385715446⟩ (N E ⟨175691177472,2378588708⟩ E)) ⟨175691177600,2371488571⟩ (N (N E ⟨175691177728,2364414917⟩ E) ⟨175691177856,2357367627⟩ (N E ⟨175691177984,2350346583⟩ E))) ⟨175825393152,2689425795⟩ (N (N (N E ⟨175825393408,2673206091⟩ E) ⟨175825393792,2649105194⟩ (N E ⟨175825393920,2641131988⟩ E)) ⟨175825394304,2617391742⟩ (N (N E ⟨175825394560,2601713045⟩ E) ⟨175825394688,2593917737⟩ (N E ⟨175825395200,2563027044⟩ E)))) ⟨175825395328,2555376355⟩ (N (N (N (N E ⟨175825395584,2540160457⟩ E) ⟨175825395712,2532594994⟩ (N E ⟨175959611008,2880916087⟩ E)) ⟨175959611648,2837757025⟩ (N (N E ⟨175959611776,2829222453⟩ E) ⟨175959612288,2795403449⟩ (N E ⟨175959612416,2787027802⟩ E))) ⟨175959612544,2778683512⟩ (N (N (N E ⟨175959612672,2770370439⟩ E) ⟨175959612800,2762088442⟩ (N E ⟨175959613312,2729268440⟩ E)) ⟨175959613440,2721139749⟩ (N (N E ⟨176093829120,3059254043⟩ E) ⟨176093829632,3022603067⟩ (N E ⟨176093829888,3004483481⟩ E)))))) ⟨176093830016,2995474623⟩ (N (N (N (N (N (N E ⟨176093830144,2986499518⟩ E) ⟨176093830528,2959775211⟩ (N E ⟨176093831168,2915895760⟩ E)) ⟨176228046976,3260158804⟩ (N (N E ⟨176228048896,3116773877⟩ E) ⟨176362265600,3404158555⟩ (N E ⟨176362266624,3323680930⟩ E))) ⟨176496484224,3547084202⟩ (N (N (N E ⟨176496484352,3536519776⟩ E) ⟨176630702080,3755189350⟩ (N E ⟨176764919680,3991472674⟩ E)) ⟨176764919808,3979584708⟩ (N (N E ⟨176899137408,4222172155⟩ E) ⟨176899137536,4209597088⟩ (N E ⟨177033355264,4445113958⟩ E)))) ⟨177167572992,4686019082⟩ (N (N (N (N E ⟨177301790720,4932192574⟩ E) ⟨177436008448,5183510966⟩ (N E ⟨177570226176,5439847270⟩ E)) ⟨177704443904,5701071046⟩ (N (N E ⟨177838661632,5967048477⟩ E) ⟨177972879360,6237642433⟩ (N E ⟨178107097088,6512712553⟩ E))) ⟨178241314816,6792115318⟩ (N (N (N E ⟨178375532544,7075704133⟩ E) ⟨178509750272,7363329404⟩ (N E ⟨178912403456,8248884841⟩ E)) ⟨179315056640,9165113264⟩ (N (N E ⟨179583492096,9790771822⟩ E) ⟨179986145280,10748090468⟩ (N E ⟨180388798592,11688866092⟩ E))))) ⟨180388798720,11654104527⟩ (N (N (N (N (N E ⟨180388798848,11619472136⟩ E) ⟨180388798976,11584968342⟩ (N E ⟨180388799104,11550592573⟩ E)) ⟨180388799232,11516344258⟩ (N (N E ⟨180388799360,11482222831⟩ E) ⟨180388799488,11448227727⟩ (N E ⟨180388799616,11414358387⟩ E))) ⟨180388799744,11380614252⟩ (N (N (N E ⟨180388799872,11346994766⟩ E) ⟨180388800000,11313499377⟩ (N E ⟨180388800128,11280127536⟩ E)) ⟨180388800256,11246878697⟩ (N (N E ⟨180388800384,11213752314⟩ E) ⟨180388800512,11180747848⟩ (N E ⟨180388800640,11147864760⟩ E)))) ⟨180388800768,11115102515⟩ (N (N (N (N E ⟨180388800896,11082460580⟩ E) ⟨180388801024,11049938424⟩ (N E ⟨180388801152,11017535522⟩ E)) ⟨180388801280,10985251347⟩ (N (N E ⟨180388801408,10953085379⟩ E) ⟨180388801536,10921037098⟩ (N E ⟨180388801664,10889105988⟩ E))) ⟨180388801792,10857291534⟩ (N (N (N E ⟨180388801920,10825593226⟩ E) ⟨180388802048,10794010555⟩ (N E ⟨180388802176,10762543015⟩ E)) ⟨180388802304,10731190103⟩ (N (N E ⟨180388802432,10699951317⟩ E) ⟨180388802560,10668826159⟩ (N E ⟨180388802688,10637814134⟩ E))))))) ⟨180388802816,10606914747⟩ (N (N (N (N (N (N (N E ⟨180388802944,10576127510⟩ E) ⟨180388803072,10545451932⟩ (N E ⟨180388803200,10514887529⟩ E)) ⟨180388803328,10484433817⟩ (N (N E ⟨180388803456,10454090316⟩ E) ⟨180388803584,10423856546⟩ (N E ⟨180388803712,10393732032⟩ E))) ⟨180388803840,10363716300⟩ (N (N (N E ⟨180388803968,10333808879⟩ E) ⟨180388804096,10304009300⟩ (N E ⟨180388804224,10274317097⟩ E)) ⟨180388804352,10244731805⟩ (N (N E ⟨180388804480,10215252963⟩ E) ⟨180388804608,10185880112⟩ (N E ⟨180388804736,10156612794⟩ E)))) ⟨180388804864,10127450554⟩ (N (N (N (N E ⟨180388804992,10098392940⟩ E) ⟨180388805120,10069439501⟩ (N E ⟨180388805248,10040589791⟩ E)) ⟨180388805376,10011843362⟩ (N (N E ⟨180388805504,9983199771⟩ E) ⟨180388805632,9954658577⟩ (N E ⟨180388805888,9897881626⟩ E))) ⟨180388806016,9869644998⟩ (N (N (N E ⟨180388806144,9841509023⟩ E) ⟨180388806272,9813473271⟩ (N E ⟨180388806400,9785537314⟩ E)) ⟨180388806528,9757700727⟩ (N (N E ⟨180388806656,9729963084⟩ E) ⟨180657240576,10634778286⟩ (N E ⟨180925677568,10826248420⟩ E))))) ⟨182536290304,14133876590⟩ (N (N (N (N (N E ⟨183610032128,16252480520⟩ E) ⟨184281120768,17498649551⟩ (N E ⟨185354862592,19313017890⟩ E)) ⟨187368128512,21903972388⟩ (N (N E ⟨187904999424,22377432791⟩ E) ⟨188978741376,22943791073⟩ (N E ⟨188978741504,22868327409⟩ E))) ⟨188978741632,22786289547⟩ (N (N (N E ⟨188978741760,22697744874⟩ E) ⟨188978741888,22602764358⟩ (N E ⟨188978742016,22501422485⟩ E)) ⟨188978742272,22279969817⟩ (N (N E ⟨188978742400,22160024998⟩ E) ⟨188978742528,22034050636⟩ (N E ⟨188978742656,21902137809⟩ E)))) ⟨188978742784,21764380703⟩ (N (N (N (N E ⟨188978743040,21471725482⟩ E) ⟨188978743168,21317030601⟩ (N E ⟨188978743296,21156897754⟩ E)) ⟨188978743424,20991435527⟩ (N (N E ⟨188978743552,20820755150⟩ E) ⟨188978743680,20644970417⟩ (N E ⟨188978743808,20464197604⟩ E))) ⟨188978743936,20278555381⟩ (N (N (N E ⟨188978744064,20088164734⟩ E) ⟨188978744192,19893148878⟩ (N E ⟨188978744320,19693633166⟩ E)) ⟨188978744448,19489745009⟩ (N (N E ⟨188978744576,19281613785⟩ E) ⟨188978744832,18853148956⟩ (N E ⟨188978744960,18633083148⟩ E)))))) ⟨188978745088,18409309687⟩ (N (N (N (N (N (N E ⟨188978745216,18181966454⟩ E) ⟨188978745344,17951192761⟩ (N E ⟨188978745600,17479917837⟩ E)) ⟨188978745728,17239701561⟩ (N (N E ⟨188978745984,16750831874⟩ E) ⟨188978746112,16502469524⟩ (N E ⟨188978746368,15998623519⟩ E))) ⟨188978746496,15743435378⟩ (N (N (N E ⟨188978746752,15227271596⟩ E) ⟨188978746880,14966594275⟩ (N E ⟨188978747008,14704386007⟩ E)) ⟨188978747264,14175975540⟩ (N (N E ⟨188978747392,13910072854⟩ E) ⟨188978747648,13375620595⟩ (N E ⟨188978748032,12569561193⟩ E)))) ⟨188978748416,11761798053⟩ (N (N (N (N E ⟨188978748544,11492849466⟩ E) ⟨188978748672,11224295565⟩ (N E ⟨188978748928,10688945415⟩ E)) ⟨188978749184,10156883789⟩ (N (N E ⟨188978749312,9892436003⟩ E) ⟨188978749440,9629227507⟩ (N E ⟨189515620352,9730938999⟩ E))) ⟨190052491264,9833071082⟩ (N (N (N E ⟨190589362176,9935507894⟩ E) ⟨191663104000,10140823567⟩ (N E ⟨192199974912,10243462948⟩ E)) ⟨193139499008,10422590998⟩ (N (N E ⟨193273716736,10448099292⟩ E) ⟨193542152192,10499035773⟩ (N E ⟨193810587648,10549852767⟩ E))))) ⟨193944805376,10575211708⟩ (N (N (N (N (N E ⟨194079023104,10600535082⟩ E) ⟨194347458560,10651067562⟩ (N E ⟨194750111744,10726552306⟩ E)) ⟨194884329472,10751622640⟩ (N (N E ⟨195421200384,10851397910⟩ E) ⟨195689635840,10900955939⟩ (N E ⟨196092289024,10974839607⟩ E))) ⟨196763377664,11096649244⟩ (N (N (N E ⟨197031813120,11144865996⟩ E) ⟨197568684288,10648370487⟩ (N E ⟨197568684416,10354926600⟩ E)) ⟨197568684544,10063375652⟩ (N (N E ⟨197568685056,8918944300⟩ E) ⟨197568685184,8638972399⟩ (N E ⟨197568685312,8361724435⟩ E)))) ⟨197568685952,7020837345⟩ (N (N (N (N E ⟨197568686080,6762594557⟩ E) ⟨197568686336,6256984451⟩ (N E ⟨197568686592,5766613749⟩ E)) ⟨197568687104,4834930976⟩ (N (N E ⟨197568687232,4612801060⟩ E) ⟨197568687616,3973751300⟩ (N E ⟨197568687872,3571324368⟩ E))) ⟨197568688000,3377422809⟩ (N (N (N E ⟨197568688128,3188490500⟩ E) ⟨197568688768,2320591584⟩ (N E ⟨197568689152,1863247807⟩ E)) ⟨197568689280,1721645940⟩ (N (N E ⟨197568689664,1329888956⟩ E) ⟨197568690048,988290955⟩ (N E ⟨197568690176,885669736⟩ E))))))))

noncomputable def tab16 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨197568690432,697374939⟩ E) ⟨197568690560,611716331⟩ E) ⟨197568690688,531721289⟩ (N E ⟨197568691072,325691933⟩ E)) ⟨197568691200,268308993⟩ (N (N E ⟨197568691328,216552079⟩ E) ⟨197568691456,170403893⟩ (N E ⟨197568691840,65390837⟩ E))) ⟨197568692096,22965865⟩ (N (N (N E ⟨197568692224,9929527⟩ E) ⟨197702905984,3012826635⟩ (N E ⟨197702906752,2016398918⟩ E)) ⟨197702907136,1590663975⟩ (N (N E ⟨197702908672,390695493⟩ E) ⟨197837126144,536554969⟩ (N E ⟨197971345408,10659989⟩ E)))) ⟨198239778048,1610878366⟩ (N (N (N (N E ⟨198239780864,11145008⟩ E) ⟨198373996160,1235425251⟩ (N E ⟨198508213760,1360967890⟩ E)) ⟨198642429952,3256081002⟩ (N (N E ⟨198642430976,1908412003⟩ E) ⟨199045085568,639886289⟩ (N E ⟨199179304192,184037443⟩ E))) ⟨199179304960,12811918⟩ (N (N (N E ⟨199313519616,1935399304⟩ E) ⟨199313521024,644728024⟩ (N E ⟨199313521408,413244316⟩ E)) ⟨199313522688,13044239⟩ (N (N E ⟨199447738112,1149378260⟩ E) ⟨199447738880,563971012⟩ (N E ⟨199447740160,48473035⟩ E))))) ⟨199581956864,416758690⟩ (N (N (N (N (N E ⟨199581957504,144136285⟩ E) ⟨199581958144,13503116⟩ (N E ⟨199984610560,190256597⟩ E)) ⟨199984611328,14174948⟩ (N (N E ⟨200253045248,576515843⟩ E) ⟨200253046144,148407386⟩ (N E ⟨200387264512,14823774⟩ E))) ⟨200521481728,111668556⟩ (N (N (N E ⟨200655698944,300925421⟩ E) ⟨200789915904,760631337⟩ (N E ⟨200789916032,669583132⟩ E)) ⟨200789916672,302151852⟩ (N (N E ⟨200789916800,246175590⟩ E) ⟨200924134528,247229637⟩ (N E ⟨200924135296,31647849⟩ E)))) ⟨200924135424,15647032⟩ (N (N (N (N E ⟨201058352384,197804290⟩ E) ⟨201058352640,114251286⟩ (N E ⟨201058353152,15844541⟩ E)) ⟨201192569600,436135847⟩ (N (N E ⟨201461005184,370592617⟩ E) ⟨201461006080,54831888⟩ (N E ⟨201461006208,32788837⟩ E))) ⟨201461006336,16415226⟩ (N (N (N E ⟨201595223040,309116349⟩ E) ⟨201595223936,33059776⟩ (N E ⟨201595224064,16597792⟩ E)) ⟨201729441792,16776340⟩ (N (N E ⟨201863659008,117786539⟩ E) ⟨201863659520,16950765⟩ (N E ⟨202132093952,313366016⟩ E)))))) ⟨202132094464,118868951⟩ (N (N (N (N (N (N E ⟨202132094976,17286823⟩ E) ⟨202266311808,256814025⟩ (N E ⟨202266312448,56913228⟩ E)) ⟨202266312704,17448255⟩ (N (N E ⟨202400529664,205877199⟩ E) ⟨202400530176,57230749⟩ (N E ⟨202400530304,34555658⟩ E))) ⟨202534747648,120398077⟩ (N (N (N E ⟨202534748032,34782266⟩ E) ⟨202668965376,120881981⟩ (N E ⟨202668965760,35002095⟩ E)) ⟨202668965888,17905000⟩ (N (N E ⟨202803182848,207976235⟩ E) ⟨202803183360,58130471⟩ (N E ⟨202803183488,35215043⟩ E)))) ⟨202803183616,18047760⟩ (N (N (N (N E ⟨202937401216,35421011⟩ E) ⟨202937401344,18185629⟩ (N E ⟨203071618944,35619903⟩ E)) ⟨203071619072,18318526⟩ (N (N E ⟨203205836288,122684805⟩ E) ⟨203205836544,58948537⟩ (N E ⟨203205836800,18446369⟩ E))) ⟨203340054528,18569082⟩ (N (N (N E ⟨203474272256,18686590⟩ E) ⟨203608489472,123893850⟩ (N E ⟨203742707456,59907423⟩ E)) ⟨203742707584,36505115⟩ (N (N E ⟨203742707712,18905716⟩ E) ⟨203876925440,19007200⟩ (N E ⟨204145360512,89967292⟩ E))))) ⟨204145360896,19193707⟩ (N (N (N (N (N E ⟨204413796352,19357895⟩ E) ⟨204548014080,19431494⟩ (N E ⟨204682231808,19499370⟩ E)) ⟨204816449536,19561481⟩ (N (N E ⟨205084884992,19668264⟩ E) ⟨206158626944,7536840⟩ (N E ⟨206158627072,1073573⟩ E))) ⟨206561281280,442111⟩ (N (N (N E ⟨206561281408,440967⟩ E) ⟨206561281536,439827⟩ (N E ⟨206561281664,438691⟩ E)) ⟨206561281792,437558⟩ (N (N E ⟨206561281920,436429⟩ E) ⟨206561282048,435304⟩ (N E ⟨206561282176,434182⟩ E)))) ⟨206561282304,433064⟩ (N (N (N (N E ⟨206561282432,431950⟩ E) ⟨206561282560,430839⟩ (N E ⟨206561282688,429732⟩ E)) ⟨206561282816,428628⟩ (N (N E ⟨206561282944,427528⟩ E) ⟨206561283072,426431⟩ (N E ⟨206561283200,425338⟩ E))) ⟨206561283328,424248⟩ (N (N (N E ⟨206561283456,423162⟩ E) ⟨206561283584,422079⟩ (N E ⟨206561283712,421000⟩ E)) ⟨206561283840,419924⟩ (N (N E ⟨206561283968,418852⟩ E) ⟨206561284096,417783⟩ (N E ⟨206561284224,416718⟩ E))))))) ⟨206561284352,415656⟩ (N (N (N (N (N (N (N E ⟨206561284480,414597⟩ E) ⟨206561284608,413541⟩ (N E ⟨206561284736,412489⟩ E)) ⟨206561284864,411441⟩ (N (N E ⟨206561284992,410395⟩ E) ⟨206561285120,409353⟩ (N E ⟨206561285248,408315⟩ E))) ⟨206561285376,407279⟩ (N (N (N E ⟨206561285504,406247⟩ E) ⟨206561285632,405218⟩ (N E ⟨206561285760,404193⟩ E)) ⟨206561285888,403170⟩ (N (N E ⟨206561286016,402151⟩ E) ⟨206561286272,400123⟩ (N E ⟨206561286528,398107⟩ E)))) ⟨206561286656,397104⟩ (N (N (N (N E ⟨206561286784,396104⟩ E) ⟨206561286912,395107⟩ (N E ⟨206561287040,394113⟩ E)) ⟨206561287168,393122⟩ (N (N E ⟨206561287552,390169⟩ E) ⟨206561287680,389191⟩ (N E ⟨206561287808,388216⟩ E))) ⟨206561288192,385309⟩ (N (N (N E ⟨206695499136,5542695⟩ E) ⟨206695499264,5528367⟩ (N E ⟨206695499392,5514085⟩ E)) ⟨206695499520,5499850⟩ (N (N E ⟨206695499648,5485660⟩ E) ⟨206695499776,5471516⟩ (N E ⟨206695499904,5457417⟩ E))))) ⟨206695500032,5443364⟩ (N (N (N (N (N E ⟨206695500160,5429356⟩ E) ⟨206695500288,5415393⟩ (N E ⟨206695500416,5401475⟩ E)) ⟨206695500544,5387602⟩ (N (N E ⟨206695500672,5373773⟩ E) ⟨206695500800,5359988⟩ (N E ⟨206695500928,5346248⟩ E))) ⟨206695501056,5332552⟩ (N (N (N E ⟨206695501184,5318899⟩ E) ⟨206695501312,5305291⟩ (N E ⟨206695501440,5291725⟩ E)) ⟨206695501568,5278204⟩ (N (N E ⟨206695501696,5264725⟩ E) ⟨206695501824,5251289⟩ (N E ⟨206695501952,5237896⟩ E)))) ⟨206695502080,5224546⟩ (N (N (N (N E ⟨206695502208,5211238⟩ E) ⟨206695502336,5197973⟩ (N E ⟨206695502464,5184750⟩ E)) ⟨206695502592,5171569⟩ (N (N E ⟨206695502720,5158430⟩ E) ⟨206695502848,5145332⟩ (N E ⟨206695502976,5132276⟩ E))) ⟨206695503104,5119262⟩ (N (N (N E ⟨206695503232,5106288⟩ E) ⟨206695503360,5093356⟩ (N E ⟨206695503488,5080465⟩ E)) ⟨206695503616,5067614⟩ (N (N E ⟨206695503744,5054804⟩ E) ⟨206695503872,5042035⟩ (N E ⟨206695504000,5029306⟩ E)))))) ⟨206695504256,5003968⟩ (N (N (N (N (N (N E ⟨206695504384,4991359⟩ E) ⟨206695504512,4978789⟩ (N E ⟨206695504640,4966259⟩ E)) ⟨206695504768,4953769⟩ (N (N E ⟨206695505024,4928905⟩ E) ⟨206695505152,4916532⟩ (N E ⟨206695505280,4904198⟩ E))) ⟨206695505536,4879645⟩ (N (N (N E ⟨206695505664,4867426⟩ E) ⟨206695505792,4855246⟩ (N E ⟨206695505920,4843103⟩ E)) ⟨206829716864,16373069⟩ (N (N E ⟨206829716992,16330744⟩ E) ⟨206829717120,16288555⟩ (N E ⟨206829717248,16246503⟩ E)))) ⟨206829717376,16204586⟩ (N (N (N (N E ⟨206829717504,16162804⟩ E) ⟨206829717632,16121157⟩ (N E ⟨206829717760,16079645⟩ E)) ⟨206829717888,16038265⟩ (N (N E ⟨206829718016,15997019⟩ E) ⟨206829718144,15955905⟩ (N E ⟨206829718272,15914924⟩ E))) ⟨206829718400,15874073⟩ (N (N (N E ⟨206829718528,15833354⟩ E) ⟨206829718656,15792766⟩ (N E ⟨206829718784,15752307⟩ E)) ⟨206829718912,15711978⟩ (N (N E ⟨206829719040,15671778⟩ E) ⟨206829719168,15631706⟩ (N E ⟨206829719296,15591763⟩ E))))) ⟨206829719424,15551947⟩ (N (N (N (N (N E ⟨206829719552,15512258⟩ E) ⟨206829719680,15472695⟩ (N E ⟨206829719808,15433259⟩ E)) ⟨206829719936,15393948⟩ (N (N E ⟨206829720064,15354763⟩ E) ⟨206829720192,15315702⟩ (N E ⟨206829720320,15276765⟩ E))) ⟨206829720448,15237952⟩ (N (N (N E ⟨206829720576,15199262⟩ E) ⟨206829720704,15160695⟩ (N E ⟨206829720832,15122250⟩ E)) ⟨206829720960,15083927⟩ (N (N E ⟨206829721088,15045725⟩ E) ⟨206829721216,15007644⟩ (N E ⟨206829721344,14969684⟩ E)))) ⟨206829721472,14931844⟩ (N (N (N (N E ⟨206829721600,14894123⟩ E) ⟨206829721728,14856521⟩ (N E ⟨206829721856,14819038⟩ E)) ⟨206829721984,14781673⟩ (N (N E ⟨206829722112,14744425⟩ E) ⟨206829722240,14707295⟩ (N E ⟨206829722368,14670282⟩ E))) ⟨206829722496,14633385⟩ (N (N (N E ⟨206829722624,14596605⟩ E) ⟨206829722752,14559939⟩ (N E ⟨206829723008,14486953⟩ E)) ⟨206829723136,14450632⟩ (N (N E ⟨206829723392,14378330⟩ E) ⟨206829723520,14342349⟩ (N E ⟨206829723648,14306480⟩ E))))))))

noncomputable def tab17 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨206963934720,32862579⟩ E) ⟨206963934848,32777683⟩ E) ⟨206963934976,32693060⟩ (N E ⟨206963935104,32608710⟩ E)) ⟨206963935232,32524633⟩ (N (N E ⟨206963935360,32440826⟩ E) ⟨206963935488,32357289⟩ (N E ⟨206963935616,32274021⟩ E))) ⟨206963935744,32191020⟩ (N (N (N E ⟨206963935872,32108287⟩ E) ⟨206963936000,32025819⟩ (N E ⟨206963936128,31943615⟩ E)) ⟨206963936256,31861675⟩ (N (N E ⟨206963936384,31779998⟩ E) ⟨206963936512,31698583⟩ (N E ⟨206963936640,31617428⟩ E)))) ⟨206963936768,31536533⟩ (N (N (N (N E ⟨206963936896,31455896⟩ E) ⟨206963937024,31375517⟩ (N E ⟨206963937152,31295395⟩ E)) ⟨206963937280,31215528⟩ (N (N E ⟨206963937408,31135917⟩ E) ⟨206963937536,31056558⟩ (N E ⟨206963937664,30977453⟩ E))) ⟨206963937792,30898599⟩ (N (N (N E ⟨206963937920,30819996⟩ E) ⟨206963938048,30741643⟩ (N E ⟨206963938176,30663539⟩ E)) ⟨206963938304,30585683⟩ (N (N E ⟨206963938432,30508074⟩ E) ⟨206963938560,30430710⟩ (N E ⟨206963938688,30353592⟩ E))))) ⟨206963938816,30276719⟩ (N (N (N (N (N E ⟨206963938944,30200088⟩ E) ⟨206963939072,30123700⟩ (N E ⟨206963939200,30047553⟩ E)) ⟨206963939328,29971647⟩ (N (N E ⟨206963939712,29745362⟩ E) ⟨206963939840,29670409⟩ (N E ⟨206963939968,29595692⟩ E))) ⟨206963940096,29521210⟩ (N (N (N E ⟨206963940224,29446962⟩ E) ⟨206963940608,29225615⟩ (N E ⟨206963940736,29152295⟩ E)) ⟨206963940864,29079205⟩ (N (N E ⟨206963940992,29006344⟩ E) ⟨206963941376,28789126⟩ (N E ⟨207098152448,55136041⟩ E)))) ⟨207098152576,54993603⟩ (N (N (N (N E ⟨207098152704,54851626⟩ E) ⟨207098152832,54710106⟩ (N E ⟨207098152960,54569042⟩ E)) ⟨207098153088,54428433⟩ (N (N E ⟨207098153216,54288277⟩ E) ⟨207098153344,54148572⟩ (N E ⟨207098153472,54009316⟩ E))) ⟨207098153600,53870507⟩ (N (N (N E ⟨207098153728,53732144⟩ E) ⟨207098153856,53594225⟩ (N E ⟨207098153984,53456749⟩ E)) ⟨207098154112,53319713⟩ (N (N E ⟨207098154240,53183116⟩ E) ⟨207098154368,53046957⟩ (N E ⟨207098154496,52911233⟩ E)))))) ⟨207098154624,52775943⟩ (N (N (N (N (N (N E ⟨207098154752,52641085⟩ E) ⟨207098154880,52506657⟩ (N E ⟨207098155008,52372659⟩ E)) ⟨207098155136,52239088⟩ (N (N E ⟨207098155264,52105943⟩ E) ⟨207098155392,51973221⟩ (N E ⟨207098155520,51840923⟩ E))) ⟨207098155648,51709045⟩ (N (N (N E ⟨207098155776,51577586⟩ E) ⟨207098155904,51446544⟩ (N E ⟨207098156032,51315919⟩ E)) ⟨207098156160,51185708⟩ (N (N E ⟨207098156288,51055910⟩ E) ⟨207098156416,50926524⟩ (N E ⟨207098156544,50797547⟩ E)))) ⟨207098156672,50668978⟩ (N (N (N (N E ⟨207098156800,50540816⟩ E) ⟨207098156928,50413058⟩ (N E ⟨207098157056,50285705⟩ E)) ⟨207098157184,50158753⟩ (N (N E ⟨207098157312,50032202⟩ E) ⟨207098157440,49906050⟩ (N E ⟨207098157568,49780295⟩ E))) ⟨207098157696,49654936⟩ (N (N (N E ⟨207098157824,49529972⟩ E) ⟨207098157952,49405401⟩ (N E ⟨207098158080,49281221⟩ E)) ⟨207098158208,49157431⟩ (N (N E ⟨207098158336,49034030⟩ E) ⟨207098158464,48911016⟩ (N E ⟨207098158592,48788387⟩ E))))) ⟨207098158720,48666143⟩ (N (N (N (N (N E ⟨207098158848,48544281⟩ E) ⟨207098158976,48422801⟩ (N E ⟨207098159104,48301700⟩ E)) ⟨207232370304,82944991⟩ (N (N E ⟨207232370432,82730851⟩ E) ⟨207232370560,82517401⟩ (N E ⟨207232370688,82304640⟩ E))) ⟨207232370816,82092564⟩ (N (N (N E ⟨207232370944,81881171⟩ E) ⟨207232371072,81670458⟩ (N E ⟨207232371200,81460423⟩ E)) ⟨207232371328,81251062⟩ (N (N E ⟨207232371456,81042374⟩ E) ⟨207232371584,80834356⟩ (N E ⟨207232371712,80627005⟩ E)))) ⟨207232371840,80420319⟩ (N (N (N (N E ⟨207232371968,80214294⟩ E) ⟨207232372096,80008929⟩ (N E ⟨207232372224,79804221⟩ E)) ⟨207232372352,79600168⟩ (N (N E ⟨207232372480,79396766⟩ E) ⟨207232372608,79194014⟩ (N E ⟨207232372736,78991909⟩ E))) ⟨207232372864,78790449⟩ (N (N (N E ⟨207232372992,78589630⟩ E) ⟨207232373120,78389451⟩ (N E ⟨207232373248,78189909⟩ E)) ⟨207232373376,77991002⟩ (N (N E ⟨207232373504,77792727⟩ E) ⟨207232373632,77595082⟩ (N E ⟨207232373760,77398064⟩ E))))))) ⟨207232373888,77201672⟩ (N (N (N (N (N (N (N E ⟨207232374016,77005902⟩ E) ⟨207232374144,76810752⟩ (N E ⟨207232374272,76616220⟩ E)) ⟨207232374400,76422304⟩ (N (N E ⟨207232374528,76229002⟩ E) ⟨207232374656,76036310⟩ (N E ⟨207232374784,75844227⟩ E))) ⟨207232374912,75652750⟩ (N (N (N E ⟨207232375168,75271606⟩ E) ⟨207232375296,75081935⟩ (N E ⟨207232375424,74892860⟩ E)) ⟨207232375552,74704381⟩ (N (N E ⟨207232375680,74516494⟩ E) ⟨207232375808,74329198⟩ (N E ⟨207232375936,74142490⟩ E)))) ⟨207232376064,73956368⟩ (N (N (N (N E ⟨207232376192,73770830⟩ E) ⟨207232376320,73585873⟩ (N E ⟨207232376576,73217696⟩ E)) ⟨207232376832,72851820⟩ (N (N E ⟨207366588160,116335918⟩ E) ⟨207366588288,116035765⟩ (N E ⟨207366588416,115736581⟩ E))) ⟨207366588544,115438360⟩ (N (N (N E ⟨207366588672,115141100⟩ E) ⟨207366588800,114844796⟩ (N E ⟨207366588928,114549445⟩ E)) ⟨207366589056,114255043⟩ (N (N E ⟨207366589184,113961586⟩ E) ⟨207366589312,113669072⟩ (N E ⟨207366589440,113377495⟩ E))))) ⟨207366589568,113086853⟩ (N (N (N (N (N E ⟨207366589696,112797142⟩ E) ⟨207366589824,112508359⟩ (N E ⟨207366589952,112220499⟩ E)) ⟨207366590080,111933559⟩ (N (N E ⟨207366590208,111647537⟩ E) ⟨207366590336,111362427⟩ (N E ⟨207366590464,111078227⟩ E))) ⟨207366590592,110794934⟩ (N (N (N E ⟨207366590720,110512543⟩ E) ⟨207366590848,110231052⟩ (N E ⟨207366590976,109950457⟩ E)) ⟨207366591104,109670754⟩ (N (N E ⟨207366591232,109391940⟩ E) ⟨207366591360,109114012⟩ (N E ⟨207366591488,108836966⟩ E)))) ⟨207366591616,108560799⟩ (N (N (N (N E ⟨207366591744,108285508⟩ E) ⟨207366591872,108011089⟩ (N E ⟨207366592000,107737540⟩ E)) ⟨207366592128,107464855⟩ (N (N E ⟨207366592256,107193034⟩ E) ⟨207366592384,106922071⟩ (N E ⟨207366592512,106651964⟩ E))) ⟨207366592640,106382710⟩ (N (N (N E ⟨207366592768,106114305⟩ E) ⟨207366592896,105846746⟩ (N E ⟨207366593280,105049115⟩ E)) ⟨207366593408,104784910⟩ (N (N E ⟨207366593664,104258986⟩ E) ⟨207366593792,103997262⟩ (N E ⟨207366593920,103736358⟩ E)))))) ⟨207366594048,103476273⟩ (N (N (N (N (N (N E ⟨207366594176,103217002⟩ E) ⟨207366594304,102958543⟩ (N E ⟨207366594432,102700893⟩ E)) ⟨207366594560,102444049⟩ (N (N E ⟨207500806016,155266897⟩ E) ⟨207500806144,154866559⟩ (N E ⟨207500806272,154467512⟩ E))) ⟨207500806400,154069749⟩ (N (N (N E ⟨207500806528,153673267⟩ E) ⟨207500806656,153278059⟩ (N E ⟨207500806784,152884121⟩ E)) ⟨207500806912,152491448⟩ (N (N E ⟨207500807040,152100035⟩ E) ⟨207500807168,151709878⟩ (N E ⟨207500807296,151320972⟩ E)))) ⟨207500807424,150933311⟩ (N (N (N (N E ⟨207500807552,150546891⟩ E) ⟨207500807680,150161707⟩ (N E ⟨207500807808,149777755⟩ E)) ⟨207500807936,149395029⟩ (N (N E ⟨207500808064,149013525⟩ E) ⟨207500808192,148633239⟩ (N E ⟨207500808320,148254166⟩ E))) ⟨207500808448,147876300⟩ (N (N (N E ⟨207500808576,147499638⟩ E) ⟨207500808704,147124175⟩ (N E ⟨207500808832,146749906⟩ E)) ⟨207500808960,146376826⟩ (N (N E ⟨207500809088,146004932⟩ E) ⟨207500809216,145634218⟩ (N E ⟨207500809344,145264681⟩ E))))) ⟨207500809472,144896315⟩ (N (N (N (N (N E ⟨207500809600,144529117⟩ E) ⟨207500809728,144163081⟩ (N E ⟨207500809856,143798203⟩ E)) ⟨207500809984,143434480⟩ (N (N E ⟨207500810112,143071906⟩ E) ⟨207500810240,142710477⟩ (N E ⟨207500810368,142350190⟩ E))) ⟨207500810496,141991038⟩ (N (N (N E ⟨207500810624,141633020⟩ E) ⟨207500810752,141276129⟩ (N E ⟨207500810880,140920361⟩ E)) ⟨207500811008,140565714⟩ (N (N E ⟨207500811136,140212181⟩ E) ⟨207500811264,139859760⟩ (N E ⟨207500811520,139158233⟩ E)))) ⟨207500811648,138809119⟩ (N (N (N (N E ⟨207500811776,138461100⟩ E) ⟨207500812032,137768329⟩ (N E ⟨207500812160,137423569⟩ E)) ⟨207500812288,137079886⟩ (N (N E ⟨207635023744,200209013⟩ E) ⟨207635023872,199692797⟩ (N E ⟨207635024000,199178245⟩ E))) ⟨207635024128,198665350⟩ (N (N (N E ⟨207635024256,198154105⟩ E) ⟨207635024384,197644504⟩ (N E ⟨207635024512,197136540⟩ E)) ⟨207635024640,196630208⟩ (N (N E ⟨207635024768,196125501⟩ E) ⟨207635024896,195622412⟩ (N E ⟨207635025024,195120936⟩ E))))))))

noncomputable def tab18 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨207635025280,194122797⟩ E) ⟨207635025408,193626122⟩ E) ⟨207635025536,193131034⟩ (N E ⟨207635025664,192637528⟩ E)) ⟨207635025792,192145598⟩ (N (N E ⟨207635025920,191655238⟩ E) ⟨207635026048,191166441⟩ (N E ⟨207635026176,190679202⟩ E))) ⟨207635026304,190193515⟩ (N (N (N E ⟨207635026432,189709374⟩ E) ⟨207635026560,189226772⟩ (N E ⟨207635026688,188745705⟩ E)) ⟨207635026816,188266165⟩ (N (N E ⟨207635026944,187788149⟩ E) ⟨207635027072,187311648⟩ (N E ⟨207635027200,186836659⟩ E)))) ⟨207635027328,186363174⟩ (N (N (N (N E ⟨207635027456,185891189⟩ E) ⟨207635027584,185420698⟩ (N E ⟨207635027712,184951694⟩ E)) ⟨207635027840,184484173⟩ (N (N E ⟨207635027968,184018129⟩ E) ⟨207635028096,183553555⟩ (N E ⟨207635028224,183090448⟩ E))) ⟨207635028352,182628800⟩ (N (N (N E ⟨207635028480,182168606⟩ E) ⟨207635028736,181252561⟩ (N E ⟨207635028864,180796698⟩ E)) ⟨207635028992,180342268⟩ (N (N E ⟨207635029248,179437684⟩ E) ⟨207635029376,178987520⟩ (N E ⟨207635029504,178538766⟩ E))))) ⟨207635029632,178091419⟩ (N (N (N (N (N E ⟨207635029760,177645472⟩ E) ⟨207635029888,177200920⟩ (N E ⟨207635030016,176757759⟩ E)) ⟨207769241728,249565316⟩ (N (N E ⟨207769241856,248922671⟩ E) ⟨207769241984,248282094⟩ (N E ⟨207769242112,247643577⟩ E))) ⟨207769242240,247007111⟩ (N (N (N E ⟨207769242368,246372690⟩ E) ⟨207769242496,245740304⟩ (N E ⟨207769242624,245109947⟩ E)) ⟨207769242752,244481611⟩ (N (N E ⟨207769242880,243855286⟩ E) ⟨207769243008,243230967⟩ (N E ⟨207769243136,242608646⟩ E)))) ⟨207769243264,241988313⟩ (N (N (N (N E ⟨207769243392,241369963⟩ E) ⟨207769243520,240753587⟩ (N E ⟨207769243648,240139178⟩ E)) ⟨207769243776,239526728⟩ (N (N E ⟨207769243904,238916230⟩ E) ⟨207769244032,238307676⟩ (N E ⟨207769244160,237701059⟩ E))) ⟨207769244288,237096371⟩ (N (N (N E ⟨207769244416,236493606⟩ E) ⟨207769244544,235892755⟩ (N E ⟨207769244672,235293812⟩ E)) ⟨207769244800,234696769⟩ (N (N E ⟨207769244928,234101620⟩ E) ⟨207769245056,233508356⟩ (N E ⟨207769245184,232916970⟩ E)))))) ⟨207769245312,232327456⟩ (N (N (N (N (N (N E ⟨207769245440,231739807⟩ E) ⟨207769245568,231154014⟩ (N E ⟨207769245696,230570072⟩ E)) ⟨207769245824,229987974⟩ (N (N E ⟨207769245952,229407711⟩ E) ⟨207769246080,228829278⟩ (N E ⟨207769246336,227677873⟩ E))) ⟨207769246464,227104886⟩ (N (N (N E ⟨207769246592,226533702⟩ E) ⟨207769246720,225964312⟩ (N E ⟨207769246848,225396711⟩ E)) ⟨207769246976,224830891⟩ (N (N E ⟨207769247232,223704570⟩ E) ⟨207769247360,223144055⟩ (N E ⟨207769247744,221473012⟩ E)))) ⟨207903459456,305620004⟩ (N (N (N (N E ⟨207903459584,304833015⟩ E) ⟨207903459712,304048558⟩ (N E ⟨207903459840,303266624⟩ E)) ⟨207903459968,302487202⟩ (N (N E ⟨207903460096,301710284⟩ E) ⟨207903460224,300935859⟩ (N E ⟨207903460352,300163918⟩ E))) ⟨207903460480,299394451⟩ (N (N (N E ⟨207903460608,298627449⟩ E) ⟨207903460736,297862902⟩ (N E ⟨207903460864,297100800⟩ E)) ⟨207903460992,296341136⟩ (N (N E ⟨207903461120,295583898⟩ E) ⟨207903461248,294829078⟩ (N E ⟨207903461376,294076667⟩ E))))) ⟨207903461504,293326655⟩ (N (N (N (N (N E ⟨207903461632,292579034⟩ E) ⟨207903461760,291833793⟩ (N E ⟨207903461888,291090924⟩ E)) ⟨207903462016,290350418⟩ (N (N E ⟨207903462144,289612266⟩ E) ⟨207903462272,288876459⟩ (N E ⟨207903462400,288142988⟩ E))) ⟨207903462528,287411843⟩ (N (N (N E ⟨207903462656,286683017⟩ E) ⟨207903462784,285956501⟩ (N E ⟨207903462912,285232285⟩ E)) ⟨207903463040,284510360⟩ (N (N E ⟨207903463168,283790719⟩ E) ⟨207903463296,283073353⟩ (N E ⟨207903463424,282358252⟩ E)))) ⟨207903463552,281645409⟩ (N (N (N (N E ⟨207903463680,280934814⟩ E) ⟨207903463808,280226459⟩ (N E ⟨207903463936,279520337⟩ E)) ⟨207903464064,278816437⟩ (N (N E ⟨207903464192,278114753⟩ E) ⟨207903464320,277415275⟩ (N E ⟨207903464448,276717995⟩ E))) ⟨207903464704,275329997⟩ (N (N (N E ⟨207903464832,274639263⟩ E) ⟨207903464960,273950694⟩ (N E ⟨207903465088,273264282⟩ E)) ⟨207903465216,272580019⟩ (N (N E ⟨207903465344,271897897⟩ E) ⟨207903465472,271217907⟩ (N E ⟨208037677440,365441360⟩ E))))))) ⟨208037677568,364501539⟩ (N (N (N (N (N (N (N E ⟨208037677696,363564738⟩ E) ⟨208037677824,362630946⟩ (N E ⟨208037677952,361700151⟩ E)) ⟨208037678080,360772341⟩ (N (N E ⟨208037678208,359847505⟩ E) ⟨208037678336,358925632⟩ (N E ⟨208037678464,358006709⟩ E))) ⟨208037678592,357090726⟩ (N (N (N E ⟨208037678720,356177672⟩ E) ⟨208037678848,355267534⟩ (N E ⟨208037678976,354360303⟩ E)) ⟨208037679104,353455967⟩ (N (N E ⟨208037679232,352554514⟩ E) ⟨208037679360,351655934⟩ (N E ⟨208037679488,350760216⟩ E)))) ⟨208037679616,349867349⟩ (N (N (N (N E ⟨208037679744,348977322⟩ E) ⟨208037679872,348090124⟩ (N E ⟨208037680000,347205744⟩ E)) ⟨208037680128,346324172⟩ (N (N E ⟨208037680256,345445397⟩ E) ⟨208037680384,344569408⟩ (N E ⟨208037680640,342825746⟩ E))) ⟨208037680768,341958053⟩ (N (N (N E ⟨208037681024,340230888⟩ E) ⟨208037681152,339371396⟩ (N E ⟨208037681280,338514616⟩ E)) ⟨208037681408,337660540⟩ (N (N E ⟨208037681536,336809156⟩ E) ⟨208037681664,335960455⟩ (N E ⟨208037681792,335114426⟩ E))))) ⟨208037681920,334271059⟩ (N (N (N (N (N E ⟨208037682048,333430344⟩ E) ⟨208037682176,332592271⟩ (N E ⟨208037682304,331756830⟩ E)) ⟨208037682432,330924012⟩ (N (N E ⟨208037682560,330093806⟩ E) ⟨208037682688,329266202⟩ (N E ⟨208037682816,328441191⟩ E))) ⟨208037682944,327618763⟩ (N (N (N E ⟨208037683072,326798909⟩ E) ⟨208037683200,325981618⟩ (N E ⟨208171895296,431332761⟩ E)) ⟨208171895424,430224198⟩ (N (N E ⟨208171895552,429119196⟩ E) ⟨208171895680,428017739⟩ (N E ⟨208171895808,426919816⟩ E)))) ⟨208171895936,425825412⟩ (N (N (N (N E ⟨208171896064,424734513⟩ E) ⟨208171896192,423647106⟩ (N E ⟨208171896320,422563178⟩ E)) ⟨208171896448,421482715⟩ (N (N E ⟨208171896576,420405705⟩ E) ⟨208171896704,419332133⟩ (N E ⟨208171896832,418261987⟩ E))) ⟨208171896960,417195253⟩ (N (N (N E ⟨208171897088,416131919⟩ E) ⟨208171897216,415071972⟩ (N E ⟨208171897344,414015398⟩ E)) ⟨208171897472,412962184⟩ (N (N E ⟨208171897600,411912319⟩ E) ⟨208171897728,410865788⟩ (N E ⟨208171897856,409822580⟩ E)))))) ⟨208171897984,408782682⟩ (N (N (N (N (N (N E ⟨208171898112,407746081⟩ E) ⟨208171898240,406712764⟩ (N E ⟨208171898368,405682720⟩ E)) ⟨208171898496,404655935⟩ (N (N E ⟨208171898624,403632397⟩ E) ⟨208171898752,402612095⟩ (N E ⟨208171898880,401595015⟩ E))) ⟨208171899008,400581146⟩ (N (N (N E ⟨208171899136,399570475⟩ E) ⟨208171899264,398562990⟩ (N E ⟨208171899392,397558679⟩ E)) ⟨208171899520,396557531⟩ (N (N E ⟨208171899648,395559533⟩ E) ⟨208171899776,394564673⟩ (N E ⟨208171899904,393572940⟩ E)))) ⟨208171900032,392584322⟩ (N (N (N (N E ⟨208171900288,390616382⟩ E) ⟨208171900672,387687542⟩ (N E ⟨208171900800,386717367⟩ E)) ⟨208171900928,385750226⟩ (N (N E ⟨208306113280,501156115⟩ E) ⟨208306113408,499869755⟩ (N E ⟨208306113536,498587522⟩ E))) ⟨208306113664,497309398⟩ (N (N (N E ⟨208306113792,496035368⟩ E) ⟨208306113920,494765417⟩ (N E ⟨208306114048,493499528⟩ E)) ⟨208306114176,492237687⟩ (N (N E ⟨208306114304,490979877⟩ E) ⟨208306114432,489726083⟩ (N E ⟨208306114560,488476289⟩ E))))) ⟨208306114688,487230481⟩ (N (N (N (N (N E ⟨208306114816,485988644⟩ E) ⟨208306114944,484750761⟩ (N E ⟨208306115072,483516818⟩ E)) ⟨208306115200,482286800⟩ (N (N E ⟨208306115328,481060692⟩ E) ⟨208306115456,479838479⟩ (N E ⟨208306115584,478620146⟩ E))) ⟨208306115712,477405678⟩ (N (N (N E ⟨208306115840,476195061⟩ E) ⟨208306115968,474988280⟩ (N E ⟨208306116096,473785320⟩ E)) ⟨208306116224,472586168⟩ (N (N E ⟨208306116352,471390807⟩ E) ⟨208306116480,470199225⟩ (N E ⟨208306116608,469011406⟩ E)))) ⟨208306116736,467827337⟩ (N (N (N (N E ⟨208306116864,466647003⟩ E) ⟨208306116992,465470390⟩ (N E ⟨208306117120,464297485⟩ E)) ⟨208306117248,463128272⟩ (N (N E ⟨208306117376,461962738⟩ E) ⟨208306117504,460800870⟩ (N E ⟨208306117632,459642653⟩ E))) ⟨208306117760,458488074⟩ (N (N (N E ⟨208306117888,457337118⟩ E) ⟨208306118016,456189773⟩ (N E ⟨208306118144,455046024⟩ E)) ⟨208306118272,453905859⟩ (N (N E ⟨208306118528,451636224⟩ E) ⟨208306118656,450506728⟩ (N E ⟨208440331136,577233906⟩ E))))))))

noncomputable def tab19 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨208440331392,574277286⟩ E) ⟨208440331520,572806076⟩ E) ⟨208440331648,571339576⟩ (N E ⟨208440331776,569877768⟩ E)) ⟨208440331904,568420633⟩ (N (N E ⟨208440332032,566968153⟩ E) ⟨208440332160,565520311⟩ (N E ⟨208440332288,564077089⟩ E))) ⟨208440332416,562638469⟩ (N (N (N E ⟨208440332544,561204434⟩ E) ⟨208440332672,559774966⟩ (N E ⟨208440332800,558350048⟩ E)) ⟨208440332928,556929662⟩ (N (N E ⟨208440333056,555513790⟩ E) ⟨208440333184,554102417⟩ (N E ⟨208440333312,552695524⟩ E)))) ⟨208440333440,551293095⟩ (N (N (N (N E ⟨208440333568,549895112⟩ E) ⟨208440333696,548501559⟩ (N E ⟨208440333824,547112419⟩ E)) ⟨208440333952,545727675⟩ (N (N E ⟨208440334080,544347311⟩ E) ⟨208440334208,542971309⟩ (N E ⟨208440334336,541599653⟩ E))) ⟨208440334464,540232327⟩ (N (N (N E ⟨208440334592,538869315⟩ E) ⟨208440334720,537510599⟩ (N E ⟨208440334848,536156164⟩ E)) ⟨208440335104,533460073⟩ (N (N E ⟨208440335232,532118383⟩ E) ⟨208440335360,530780911⟩ (N E ⟨208440335488,529447639⟩ E))))) ⟨208440335616,528118552⟩ (N (N (N (N (N E ⟨208440335744,526793633⟩ E) ⟨208440335872,525472868⟩ (N E ⟨208440336000,524156241⟩ E)) ⟨208440336128,522843736⟩ (N (N E ⟨208440336256,521535338⟩ E) ⟨208440336384,520231031⟩ (N E ⟨208574548992,658391274⟩ E))) ⟨208574549120,656703495⟩ (N (N (N E ⟨208574549248,655021122⟩ E) ⟨208574549376,653344135⟩ (N E ⟨208574549504,651672512⟩ E)) ⟨208574549632,650006234⟩ (N (N E ⟨208574549760,648345280⟩ E) ⟨208574549888,646689628⟩ (N E ⟨208574550016,645039260⟩ E)))) ⟨208574550144,643394155⟩ (N (N (N (N E ⟨208574550272,641754292⟩ E) ⟨208574550400,640119652⟩ (N E ⟨208574550528,638490215⟩ E)) ⟨208574550656,636865960⟩ (N (N E ⟨208574550784,635246868⟩ E) ⟨208574550912,633632920⟩ (N E ⟨208574551040,632024096⟩ E))) ⟨208574551168,630420375⟩ (N (N (N E ⟨208574551296,628821740⟩ E) ⟨208574551424,627228170⟩ (N E ⟨208574551552,625639646⟩ E)) ⟨208574551680,624056149⟩ (N (N E ⟨208574551808,622477660⟩ E) ⟨208574551936,620904160⟩ (N E ⟨208574552064,619335630⟩ E)))))) ⟨208574552192,617772052⟩ (N (N (N (N (N (N E ⟨208574552320,616213406⟩ E) ⟨208574552448,614659673⟩ (N E ⟨208574552576,613110836⟩ E)) ⟨208574552704,611566875⟩ (N (N E ⟨208574552832,610027773⟩ E) ⟨208574552960,608493511⟩ (N E ⟨208574553088,606964071⟩ E))) ⟨208574553344,603919582⟩ (N (N (N E ⟨208574553472,602404498⟩ E) ⟨208574553600,600894163⟩ (N E ⟨208574553728,599388560⟩ E)) ⟨208574553856,597887671⟩ (N (N E ⟨208574553984,596391478⟩ E) ⟨208574554112,594899963⟩ (N E ⟨208708766848,744559049⟩ E)))) ⟨208708766976,742651604⟩ (N (N (N (N E ⟨208708767104,740750265⟩ E) ⟨208708767232,738855009⟩ (N E ⟨208708767360,736965811⟩ E)) ⟨208708767488,735082650⟩ (N (N E ⟨208708767616,733205501⟩ E) ⟨208708767744,731334342⟩ (N E ⟨208708767872,729469150⟩ E))) ⟨208708768000,727609902⟩ (N (N (N E ⟨208708768128,725756576⟩ E) ⟨208708768256,723909148⟩ (N E ⟨208708768384,722067596⟩ E)) ⟨208708768512,720231898⟩ (N (N E ⟨208708768640,718402031⟩ E) ⟨208708768768,716577974⟩ (N E ⟨208708768896,714759704⟩ E))))) ⟨208708769024,712947198⟩ (N (N (N (N (N E ⟨208708769152,711140436⟩ E) ⟨208708769280,709339395⟩ (N E ⟨208708769408,707544054⟩ E)) ⟨208708769536,705754391⟩ (N (N E ⟨208708769664,703970384⟩ E) ⟨208708769792,702192012⟩ (N E ⟨208708769920,700419253⟩ E))) ⟨208708770048,698652087⟩ (N (N (N E ⟨208708770304,695134448⟩ E) ⟨208708770432,693383932⟩ (N E ⟨208708770560,691638925⟩ E)) ⟨208708770688,689899405⟩ (N (N E ⟨208708770816,688165352⟩ E) ⟨208708770944,686436745⟩ (N E ⟨208708771072,684713563⟩ E)))) ⟨208708771200,682995787⟩ (N (N (N (N E ⟨208708771328,681283396⟩ E) ⟨208708771456,679576369⟩ (N E ⟨208708771584,677874687⟩ E)) ⟨208708771840,674487275⟩ (N (N E ⟨208842984832,833525772⟩ E) ⟨208842984960,831393144⟩ (N E ⟨208842985088,829267333⟩ E))) ⟨208842985216,827148315⟩ (N (N (N E ⟨208842985344,825036062⟩ E) ⟨208842985472,822930549⟩ (N E ⟨208842985600,820831751⟩ E)) ⟨208842985728,818739641⟩ (N (N E ⟨208842985856,816654193⟩ E) ⟨208842985984,814575384⟩ (N E ⟨208842986112,812503186⟩ E))))))) ⟨208842986240,810437576⟩ (N (N (N (N (N (N (N E ⟨208842986368,808378527⟩ E) ⟨208842986496,806326015⟩ (N E ⟨208842986624,804280014⟩ E)) ⟨208842986752,802240501⟩ (N (N E ⟨208842986880,800207451⟩ E) ⟨208842987008,798180838⟩ (N E ⟨208842987136,796160639⟩ E))) ⟨208842987264,794146828⟩ (N (N (N E ⟨208842987392,792139383⟩ E) ⟨208842987520,790138278⟩ (N E ⟨208842987648,788143490⟩ E)) ⟨208842987776,786154995⟩ (N (N E ⟨208842987904,784172768⟩ E) ⟨208842988032,782196787⟩ (N E ⟨208842988160,780227027⟩ E)))) ⟨208842988288,778263466⟩ (N (N (N (N E ⟨208842988416,776306079⟩ E) ⟨208842988544,774354844⟩ (N E ⟨208842988672,772409737⟩ E)) ⟨208842988800,770470735⟩ (N (N E ⟨208842988928,768537816⟩ E) ⟨208842989056,766610955⟩ (N E ⟨208842989184,764690132⟩ E))) ⟨208842989312,762775322⟩ (N (N (N E ⟨208842989440,760866503⟩ E) ⟨208842989568,758963653⟩ (N E ⟨208977202688,929251456⟩ E)) ⟨208977202816,926875429⟩ (N (N E ⟨208977202944,924506993⟩ E) ⟨208977203072,922146120⟩ (N E ⟨208977203200,919792780⟩ E))))) ⟨208977203328,917446945⟩ (N (N (N (N (N E ⟨208977203456,915108585⟩ E) ⟨208977203584,912777672⟩ (N E ⟨208977203712,910454178⟩ E)) ⟨208977203840,908138075⟩ (N (N E ⟨208977203968,905829333⟩ E) ⟨208977204096,903527926⟩ (N E ⟨208977204224,901233825⟩ E))) ⟨208977204352,898947003⟩ (N (N (N E ⟨208977204480,896667431⟩ E) ⟨208977204608,894395082⟩ (N E ⟨208977204736,892129929⟩ E)) ⟨208977204864,889871944⟩ (N (N E ⟨208977204992,887621100⟩ E) ⟨208977205120,885377370⟩ (N E ⟨208977205248,883140727⟩ E)))) ⟨208977205376,880911144⟩ (N (N (N (N E ⟨208977205504,878688595⟩ E) ⟨208977205632,876473053⟩ (N E ⟨208977205760,874264491⟩ E)) ⟨208977205888,872062882⟩ (N (N E ⟨208977206016,869868202⟩ E) ⟨208977206144,867680423⟩ (N E ⟨208977206400,863325466⟩ E))) ⟨208977206528,861158236⟩ (N (N (N E ⟨208977206656,858997803⟩ E) ⟨208977206912,854697231⟩ (N E ⟨208977207040,852557041⟩ E)) ⟨208977207168,850423546⟩ (N (N E ⟨208977207296,848296723⟩ E) ⟨209111420672,1027120088⟩ (N E ⟨209111420800,1024497176⟩ E)))))) ⟨209111420928,1021882633⟩ (N (N (N (N (N (N E ⟨209111421056,1019276428⟩ E) ⟨209111421184,1016678529⟩ (N E ⟨209111421312,1014088903⟩ E)) ⟨209111421440,1011507519⟩ (N (N E ⟨209111421568,1008934346⟩ E) ⟨209111421696,1006369352⟩ (N E ⟨209111421824,1003812507⟩ E))) ⟨209111421952,1001263779⟩ (N (N (N E ⟨209111422080,998723136⟩ E) ⟨209111422208,996190550⟩ (N E ⟨209111422336,993665988⟩ E)) ⟨209111422464,991149420⟩ (N (N E ⟨209111422592,988640816⟩ E) ⟨209111422720,986140146⟩ (N E ⟨209111422848,983647380⟩ E)))) ⟨209111422976,981162487⟩ (N (N (N (N E ⟨209111423104,978685438⟩ E) ⟨209111423232,976216203⟩ (N E ⟨209111423360,973754753⟩ E)) ⟨209111423488,971301057⟩ (N (N E ⟨209111423616,968855088⟩ E) ⟨209111423744,966416815⟩ (N E ⟨209111423872,963986209⟩ E))) ⟨209111424128,959147886⟩ (N (N (N E ⟨209111424256,956740110⟩ E) ⟨209111424384,954339887⟩ (N E ⟨209111424640,949561984⟩ E)) ⟨209111424768,947184249⟩ (N (N E ⟨209111424896,944813953⟩ E) ⟨209111425024,942451069⟩ (N E ⟨209245638528,1132047434⟩ E))))) ⟨209245638656,1129158421⟩ (N (N (N (N (N E ⟨209245638784,1126278620⟩ E) ⟨209245638912,1123407997⟩ (N E ⟨209245639040,1120546515⟩ E)) ⟨209245639168,1117694142⟩ (N (N E ⟨209245639296,1114850841⟩ E) ⟨209245639424,1112016578⟩ (N E ⟨209245639552,1109191318⟩ E))) ⟨209245639680,1106375028⟩ (N (N (N E ⟨209245639808,1103567673⟩ E) ⟨209245639936,1100769219⟩ (N E ⟨209245640064,1097979632⟩ E)) ⟨209245640192,1095198878⟩ (N (N E ⟨209245640320,1092426925⟩ E) ⟨209245640448,1089663738⟩ (N E ⟨209245640576,1086909285⟩ E)))) ⟨209245640704,1084163531⟩ (N (N (N (N E ⟨209245640832,1081426445⟩ E) ⟨209245640960,1078697993⟩ (N E ⟨209245641088,1075978143⟩ E)) ⟨209245641216,1073266863⟩ (N (N E ⟨209245641344,1070564119⟩ E) ⟨209245641472,1067869879⟩ (N E ⟨209245641600,1065184112⟩ E))) ⟨209245641728,1062506786⟩ (N (N (N E ⟨209245642112,1054525132⟩ E) ⟨209245642240,1051881251⟩ (N E ⟨209245642368,1049245653⟩ E)) ⟨209245642496,1046618306⟩ (N (N E ⟨209245642624,1043999180⟩ E) ⟨209245642752,1041388244⟩ (N E ⟨209379856640,1235252260⟩ E))))))))

noncomputable def tab20 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨209379857152,1222726734⟩ E) ⟨209379857280,1219620198⟩ E) ⟨209379857408,1216523523⟩ (N E ⟨209379857536,1213436673⟩ E)) ⟨209379857664,1210359611⟩ (N (N E ⟨209379857792,1207292298⟩ E) ⟨209379857920,1204234698⟩ (N E ⟨209379858176,1198148491⟩ E))) ⟨209379858304,1195119809⟩ (N (N (N E ⟨209379858432,1192100694⟩ E) ⟨209379858560,1189091109⟩ (N E ⟨209379858688,1186091018⟩ E)) ⟨209379858816,1183100385⟩ (N (N E ⟨209379858944,1180119175⟩ E) ⟨209379859072,1177147351⟩ (N E ⟨209379859200,1174184879⟩ E)))) ⟨209379859328,1171231722⟩ (N (N (N (N E ⟨209379859584,1165353217⟩ E) ⟨209379859840,1159511555⟩ (N E ⟨209379859968,1156604455⟩ E)) ⟨209379860096,1153706461⟩ (N (N E ⟨209379860224,1150817541⟩ E) ⟨209379860352,1147937660⟩ (N E ⟨209379860480,1145066785⟩ E))) ⟨209514074496,1348719205⟩ (N (N (N E ⟨209514074880,1338452348⟩ E) ⟨209514075008,1335051791⟩ (N E ⟨209514075264,1328283024⟩ E)) ⟨209514075392,1324914731⟩ (N (N E ⟨209514075520,1321557111⟩ E) ⟨209514075648,1318210123⟩ (N E ⟨209514075776,1314873727⟩ E))))) ⟨209514075904,1311547883⟩ (N (N (N (N (N E ⟨209514076032,1308232551⟩ E) ⟨209514076160,1304927690⟩ (N E ⟨209514076288,1301633261⟩ E)) ⟨209514076416,1298349225⟩ (N (N E ⟨209514076544,1295075542⟩ E) ⟨209514076672,1291812173⟩ (N E ⟨209514076800,1288559080⟩ E))) ⟨209514076928,1285316223⟩ (N (N (N E ⟨209514077056,1282083563⟩ E) ⟨209514077184,1278861063⟩ (N E ⟨209514077312,1275648683⟩ E)) ⟨209514077440,1272446387⟩ (N (N E ⟨209514077568,1269254135⟩ E) ⟨209514077696,1266071890⟩ (N E ⟨209514077952,1259737271⟩ E)))) ⟨209514078208,1253442231⟩ (N (N (N (N E ⟨209648293120,1444384438⟩ E) ⟨209648293376,1437075265⟩ (N E ⟨209648293504,1433438020⟩ E)) ⟨209648293632,1429812279⟩ (N (N E ⟨209648294016,1419003640⟩ E) ⟨209648294144,1415423477⟩ (N E ⟨209648294272,1411854601⟩ E))) ⟨209648294400,1408296969⟩ (N (N (N E ⟨209648294656,1401215267⟩ E) ⟨209648294784,1397691114⟩ (N E ⟨209648294912,1394178035⟩ E)) ⟨209648295168,1387184938⟩ (N (N E ⟨209648295296,1383704835⟩ E) ⟨209648295424,1380235642⟩ (N E ⟨209648295552,1376777318⟩ E)))))) ⟨209648295680,1373329821⟩ (N (N (N (N (N (N E ⟨209648295936,1366467147⟩ E) ⟨209782510976,1564740000⟩ (N E ⟨209782511360,1552888950⟩ E)) ⟨209782511488,1548963556⟩ (N (N E ⟨209782511616,1545050559⟩ E) ⟨209782511872,1537261575⟩ (N E ⟨209782512000,1533385494⟩ E))) ⟨209782512256,1525669922⟩ (N (N (N E ⟨209782512384,1521830339⟩ E) ⟨209782512512,1518002830⟩ (N E ⟨209782512640,1514187350⟩ E)) ⟨209782512768,1510383853⟩ (N (N E ⟨209782512896,1506592294⟩ E) ⟨209782513024,1502812628⟩ (N E ⟨209782513152,1499044811⟩ E)))) ⟨209782513408,1491544544⟩ (N (N (N (N E ⟨209782513664,1484091138⟩ E) ⟨209916728704,1693548722⟩ (N E ⟨209916729088,1680722099⟩ E)) ⟨209916729472,1668016711⟩ (N (N E ⟨209916729728,1659613126⟩ E) ⟨209916729856,1655431185⟩ (N E ⟨209916729984,1651262412⟩ E))) ⟨209916730240,1642964168⟩ (N (N (N E ⟨209916730496,1634717999⟩ E) ⟨209916730880,1622445533⟩ (N E ⟨209916731008,1618380326⟩ E)) ⟨209916731392,1606260880⟩ (N (N E ⟨210050947200,1799545632⟩ E) ⟨210050947584,1785967694⟩ (N E ⟨210050947840,1776986855⟩ E))))) ⟨210050947968,1772517609⟩ (N (N (N (N (N E ⟨210050948224,1763621202⟩ E) ⟨210050948352,1759193934⟩ (N E ⟨210050948480,1754780554⟩ E)) ⟨210050948736,1745995246⟩ (N (N E ⟨210050948864,1741623214⟩ E) ⟨210050949120,1732920140⟩ (N E ⟨210185165568,1911410019⟩ E))) ⟨210185165952,1897033299⟩ (N (N (N E ⟨210185166464,1878073998⟩ E) ⟨210185166592,1873371237⟩ (N E ⟨210185166720,1868683191⟩ E)) ⟨210185166848,1864009804⟩ (N (N E ⟨210319383680,2034891230⟩ E) ⟨210319383936,2024690765⟩ (N E ⟨210319384192,2014554151⟩ E)))) ⟨210319384320,2009509640⟩ (N (N (N (N E ⟨210319384448,2004480911⟩ E) ⟨210319384576,1999467908⟩ (N E ⟨210453601024,2193628496⟩ E)) ⟨210453601152,2188111368⟩ (N (N E ⟨210453601280,2182611578⟩ E) ⟨210453602304,2139229668⟩ (N E ⟨210587819648,2300454759⟩ E))) ⟨210587820032,2283227512⟩ (N (N (N E ⟨210722037760,2431391112⟩ E) ⟨210856255488,2583647426⟩ (N E ⟨210990473216,2739920731⟩ E)) ⟨211124690944,2900132663⟩ (N (N E ⟨211258908672,3064202262⟩ E) ⟨211393126400,3232046011⟩ (N E ⟨211527344128,3403577882⟩ E))))))) ⟨211661561856,3578709384⟩ (N (N (N (N (N (N (N E ⟨211795779584,3757349609⟩ E) ⟨211929997312,3939405282⟩ (N E ⟨212064215040,4124780812⟩ E)) ⟨212198432768,4313378347⟩ (N (N E ⟨212466868224,4699837030⟩ E) ⟨212601085952,4897491654⟩ (N E ⟨212735303680,5097955349⟩ E))) ⟨212869521408,5301119791⟩ (N (N (N E ⟨213003739136,5506874740⟩ E) ⟨213137956864,5715108105⟩ (N E ⟨213272174592,5925706003⟩ E)) ⟨213406392320,6138552830⟩ (N (N E ⟨213540610048,6353531323⟩ E) ⟨213674827776,6570522631⟩ (N E ⟨213943263232,7010060751⟩ E)))) ⟨214077480960,7232362537⟩ (N (N (N (N E ⟨214480134144,7907901185⟩ E) ⟨214748569728,8343278283⟩ (N E ⟨214748569856,8322438682⟩ E)) ⟨214748569984,8301664123⟩ (N (N E ⟨214748570112,8280954363⟩ E) ⟨214748570240,8260309158⟩ (N E ⟨214748570368,8239728268⟩ E))) ⟨214748570496,8219211452⟩ (N (N (N E ⟨214748570624,8198758471⟩ E) ⟨214748570752,8178369086⟩ (N E ⟨214748570880,8158043061⟩ E)) ⟨214748571008,8137780160⟩ (N (N E ⟨214748571136,8117580146⟩ E) ⟨214748571264,8097442786⟩ (N E ⟨214748571392,8077367847⟩ E))))) ⟨214748571520,8057355097⟩ (N (N (N (N (N E ⟨214748571648,8037404305⟩ E) ⟨214748571776,8017515240⟩ (N E ⟨214748571904,7997687674⟩ E)) ⟨214748572032,7977921378⟩ (N (N E ⟨214748572160,7958216125⟩ E) ⟨214748572288,7938571689⟩ (N E ⟨214748572416,7918987845⟩ E))) ⟨214748572544,7899464369⟩ (N (N (N E ⟨214748572672,7880001038⟩ E) ⟨214748572800,7860597628⟩ (N E ⟨214748572928,7841253920⟩ E)) ⟨214748573056,7821969692⟩ (N (N E ⟨214748573184,7802744726⟩ E) ⟨214748573312,7783578802⟩ (N E ⟨214748573440,7764471704⟩ E)))) ⟨214748573568,7745423214⟩ (N (N (N (N E ⟨214748573696,7726433117⟩ E) ⟨214748573824,7707501199⟩ (N E ⟨214748573952,7688627245⟩ E)) ⟨214748574080,7669811042⟩ (N (N E ⟨214748574208,7651052380⟩ E) ⟨214748574336,7632351046⟩ (N E ⟨214748574464,7613706830⟩ E))) ⟨214748574592,7595119523⟩ (N (N (N E ⟨214748574720,7576588917⟩ E) ⟨214748574848,7558114805⟩ (N E ⟨214748574976,7539696979⟩ E)) ⟨214748575104,7521335234⟩ (N (N E ⟨214748575232,7503029365⟩ E) ⟨214748575360,7484779168⟩ (N E ⟨214748575488,7466584440⟩ E)))))) ⟨214748575616,7448444979⟩ (N (N (N (N (N (N E ⟨214748575744,7430360584⟩ E) ⟨214748575872,7412331053⟩ (N E ⟨214748576000,7394356188⟩ E)) ⟨214748576128,7376435789⟩ (N (N E ⟨214748576256,7358569658⟩ E) ⟨214748576384,7340757599⟩ (N E ⟨214748576512,7322999415⟩ E))) ⟨214748576640,7305294910⟩ (N (N (N E ⟨214748576768,7287643890⟩ E) ⟨214748576896,7270046162⟩ (N E ⟨214748577024,7252501531⟩ E)) ⟨214748577152,7235009806⟩ (N (N E ⟨214748577280,7217570796⟩ E) ⟨214748577408,7200184310⟩ (N E ⟨214748577536,7182850157⟩ E)))) ⟨214748577664,7165568150⟩ (N (N (N (N E ⟨214748577792,7148338100⟩ E) ⟨215822319616,8729335268⟩ (N E ⟨216896061440,10300402336⟩ E)) ⟨222264770560,16051848000⟩ (N (N E ⟨223338512512,16418769270⟩ E) ⟨223338512640,16371937440⟩ (N E ⟨223338512768,16320343345⟩ E))) ⟨223338512896,16264029169⟩ (N (N (N E ⟨223338513024,16203039755⟩ E) ⟨223338513152,16137422570⟩ (N E ⟨223338513280,16067227664⟩ E)) ⟨223338513408,15992507623⟩ (N (N E ⟨223338513536,15913317533⟩ E) ⟨223338513664,15829714926⟩ (N E ⟨223338513920,15649514276⟩ E))))) ⟨223338514048,15553043132⟩ (N (N (N (N (N E ⟨223338514176,15452413173⟩ E) ⟨223338514432,15238955248⟩ (N E ⟨223338514560,15126271841⟩ E)) ⟨223338514688,15009718625⟩ (N (N E ⟨223338514816,14889372976⟩ E) ⟨223338514944,14765314206⟩ (N E ⟨223338515072,14637623509⟩ E))) ⟨223338515200,14506383906⟩ (N (N (N E ⟨223338515456,14233598825⟩ E) ⟨223338515584,14092227980⟩ (N E ⟨223338515712,13947657371⟩ E)) ⟨223338515840,13799978251⟩ (N (N E ⟨223338515968,13649283334⟩ E) ⟨223338516096,13495666739⟩ (N E ⟨223338516224,13339223920⟩ E)))) ⟨223338516480,13018247744⟩ (N (N (N (N E ⟨223338516608,12853911416⟩ E) ⟨223338516736,12687142798⟩ (N E ⟨223338516864,12518043076⟩ E)) ⟨223338516992,12346714390⟩ (N (N E ⟨223338517120,12173259767⟩ E) ⟨223338517248,11997783053⟩ (N E ⟨223338517376,11820388852⟩ E))) ⟨223338517504,11641182452⟩ (N (N (N E ⟨223338517632,11460269768⟩ E) ⟨223338517888,11093751909⟩ (N E ⟨223338518016,10908361077⟩ E)) ⟨223338518144,10721692510⟩ (N (N E ⟨223338518272,10533854239⟩ E) ⟨223338518784,9772971268⟩ (N E ⟨223338518912,9580910548⟩ E))))))))

noncomputable def tab21 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨223338519168,9195340124⟩ E) ⟨223338519552,8614981766⟩ E) ⟨223338519680,8421424628⟩ (N E ⟨223338519808,8227993137⟩ E)) ⟨223338519936,8034793215⟩ (N (N E ⟨223338520064,7841930177⟩ E) ⟨223338520320,7457632652⟩ (N E ⟨223338520448,7266405248⟩ E))) ⟨223338520576,7075928778⟩ (N (N (N E ⟨226425528320,7441069285⟩ E) ⟨226559746048,7456943857⟩ (N E ⟨227230834688,7536148169⟩ E)) ⟨227633486848,9208608829⟩ (N (N E ⟨227633487872,7583494155⟩ E) ⟨228707229696,7708831061⟩ (N E ⟨229244100608,7770860326⟩ E)))) ⟨229646753792,7817042914⟩ (N (N (N (N E ⟨229915189248,7847652861⟩ E) ⟨230049406976,7862900965⟩ (N E ⟨230183624704,7878109683⟩ E)) ⟨230452060160,7908404574⟩ (N (N E ⟨230854713344,7953524245⟩ E) ⟨230988931072,7968473783⟩ (N E ⟨231257366528,7998230943⟩ E))) ⟨231794237440,8057148254⟩ (N (N (N E ⟨231928455296,7860878833⟩ E) ⟨231928455424,7651001355⟩ (N E ⟨231928455680,7234651425⟩ E)) ⟨231928455808,7028392262⟩ (N (N E ⟨231928455936,6823550428⟩ E) ⟨231928456192,6418531221⟩ (N E ⟨231928456448,6020404688⟩ E))))) ⟨231928456576,5824173145⟩ (N (N (N (N (N E ⟨231928456704,5629958027⟩ E) ⟨231928456832,5437853764⟩ (N E ⟨231928456960,5247953102⟩ E)) ⟨231928457216,4875124875⟩ (N (N E ⟨231928457344,4692373975⟩ E) ⟨231928457472,4512179917⟩ (N E ⟨231928457856,3987765561⟩ E))) ⟨231928458240,3489255446⟩ (N (N (N E ⟨231928458368,3329189908⟩ E) ⟨231928458496,3172293833⟩ (N E ⟨231928458752,2868276071⟩ E)) ⟨231928458880,2721281800⟩ (N (N E ⟨231928459008,2577711767⟩ E) ⟨231928459776,1791284529⟩ (N E ⟨231928459904,1673176409⟩ E)))) ⟨231928460160,1448464874⟩ (N (N (N (N E ⟨231928460288,1341936689⟩ E) ⟨231928460416,1239339599⟩ (N E ⟨231928460672,1046061931⟩ E)) ⟨231928460800,955436740⟩ (N (N E ⟨231928461056,786333379⟩ E) ⟨231928461312,633556508⟩ (N E ⟨231928461440,563330048⟩ E))) ⟨231928461696,435258306⟩ (N (N (N E ⟨231928461824,377428442⟩ E) ⟨231928462080,274200677⟩ (N E ⟨231928462208,228803353⟩ E)) ⟨231928462336,187546703⟩ (N (N E ⟨231928462720,88550508⟩ E) ⟨231928463104,26466625⟩ (N E ⟨231928463360,5355706⟩ E)))))) ⟨232196894848,2178297713⟩ (N (N (N (N (N (N E ⟨232733768064,444936388⟩ E) ⟨232733768832,155364655⟩ (N E ⟨232867986816,92735134⟩ E)) ⟨233002201984,1478073812⟩ (N (N E ⟨233002203008,725678018⟩ E) ⟨233270640128,68653077⟩ (N E ⟨233673291264,990411898⟩ E))) ⟨233673292032,519487741⟩ (N (N (N E ⟨233673292160,455623901⟩ E) ⟨233941727744,398621424⟩ (N E ⟨234075947008,7405246⟩ E)) ⟨234478598400,528885342⟩ (N (N E ⟨234478599424,130081200⟩ E) ⟨234478599552,99256506⟩ (N E ⟨234478600192,7763692⟩ E)))) ⟨234612816384,405010027⟩ (N (N (N (N E ⟨234612817280,99756767⟩ E) ⟨234612817792,17958734⟩ (N E ⟨234747035008,100249773⟩ E)) ⟨234747035136,73451338⟩ (N (N E ⟨235015471104,8220996⟩ E) ⟨235418123392,169732714⟩ (N E ⟨235418123648,102601653⟩ E))) ⟨235552342016,8650706⟩ (N (N (N E ⟨235820777088,53270739⟩ E) ⟨236223430528,19930124⟩ (N E ⟨236223430656,9142762⟩ E)) ⟨236357647872,77824918⟩ (N (N E ⟨236357648384,9234561⟩ E) ⟨236626083840,9411094⟩ (N E ⟨236894519296,9577858⟩ E))))) ⟨237028737024,9657450⟩ (N (N (N (N (N E ⟨237297172096,55988702⟩ E) ⟨237297172480,9808813⟩ (N E ⟨237565607936,9949449⟩ E)) ⟨237834043392,10079018⟩ (N (N E ⟨237968260864,37089539⟩ E) ⟨237968261120,10139553⟩ (N E ⟨238102478720,21581093⟩ E))) ⟨238639349760,10398340⟩ (N (N (N E ⟨238773567488,10441100⟩ E) ⟨240518398080,3268915⟩ (N E ⟨240518398208,118725⟩ E)) ⟨240921052416,1229048⟩ (N (N E ⟨240921052544,1226321⟩ E) ⟨240921052672,1223601⟩ (N E ⟨240921052800,1220889⟩ E)))) ⟨240921052928,1218185⟩ (N (N (N (N E ⟨240921053056,1215488⟩ E) ⟨240921053184,1212798⟩ (N E ⟨240921053312,1210116⟩ E)) ⟨240921053440,1207441⟩ (N (N E ⟨240921053568,1204774⟩ E) ⟨240921053696,1202114⟩ (N E ⟨240921053824,1199461⟩ E))) ⟨240921053952,1196816⟩ (N (N (N E ⟨240921054080,1194177⟩ E) ⟨240921054208,1191547⟩ (N E ⟨240921054336,1188923⟩ E)) ⟨240921054464,1186307⟩ (N (N E ⟨240921054592,1183697⟩ E) ⟨240921054720,1181096⟩ (N E ⟨240921054848,1178501⟩ E))))))) ⟨240921054976,1175913⟩ (N (N (N (N (N (N (N E ⟨240921055104,1173332⟩ E) ⟨240921055232,1170759⟩ (N E ⟨240921055360,1168192⟩ E)) ⟨240921055488,1165633⟩ (N (N E ⟨240921055616,1163080⟩ E) ⟨240921055744,1160535⟩ (N E ⟨240921055872,1157996⟩ E))) ⟨240921056128,1152940⟩ (N (N (N E ⟨240921056256,1150422⟩ E) ⟨240921056384,1147911⟩ (N E ⟨240921056512,1145407⟩ E)) ⟨240921056640,1142910⟩ (N (N E ⟨240921056768,1140420⟩ E) ⟨240921056896,1137936⟩ (N E ⟨240921057024,1135459⟩ E)))) ⟨240921057152,1132989⟩ (N (N (N (N E ⟨240921057280,1130526⟩ E) ⟨240921057408,1128069⟩ (N E ⟨240921057536,1125619⟩ E)) ⟨240921057664,1123175⟩ (N (N E ⟨240921057792,1120739⟩ E) ⟨240921057920,1118308⟩ (N E ⟨240921058048,1115885⟩ E))) ⟨240921058176,1113468⟩ (N (N (N E ⟨240921058304,1111057⟩ E) ⟨240921058816,1101480⟩ (N E ⟨240921058944,1099102⟩ E)) ⟨240921059072,1096731⟩ (N (N E ⟨240921059328,1092006⟩ E) ⟨241055270272,6540105⟩ (N E ⟨241055270400,6525601⟩ E))))) ⟨241055270528,6511137⟩ (N (N (N (N (N E ⟨241055270656,6496714⟩ E) ⟨241055270784,6482330⟩ (N E ⟨241055270912,6467986⟩ E)) ⟨241055271040,6453681⟩ (N (N E ⟨241055271168,6439416⟩ E) ⟨241055271296,6425191⟩ (N E ⟨241055271424,6411004⟩ E))) ⟨241055271552,6396857⟩ (N (N (N E ⟨241055271680,6382749⟩ E) ⟨241055271808,6368680⟩ (N E ⟨241055271936,6354650⟩ E)) ⟨241055272064,6340658⟩ (N (N E ⟨241055272192,6326704⟩ E) ⟨241055272320,6312789⟩ (N E ⟨241055272448,6298913⟩ E)))) ⟨241055272576,6285074⟩ (N (N (N (N E ⟨241055272704,6271273⟩ E) ⟨241055272832,6257511⟩ (N E ⟨241055272960,6243786⟩ E)) ⟨241055273088,6230098⟩ (N (N E ⟨241055273216,6216448⟩ E) ⟨241055273344,6202836⟩ (N E ⟨241055273472,6189260⟩ E))) ⟨241055273600,6175722⟩ (N (N (N E ⟨241055273728,6162221⟩ E) ⟨241055273856,6148757⟩ (N E ⟨241055273984,6135329⟩ E)) ⟨241055274112,6121938⟩ (N (N E ⟨241055274240,6108584⟩ E) ⟨241055274368,6095266⟩ (N E ⟨241055274496,6081984⟩ E)))))) ⟨241055274624,6068739⟩ (N (N (N (N (N (N E ⟨241055274752,6055529⟩ E) ⟨241055274880,6042356⟩ (N E ⟨241055275008,6029218⟩ E)) ⟨241055275136,6016116⟩ (N (N E ⟨241055275264,6003050⟩ E) ⟨241055275392,5990019⟩ (N E ⟨241055275520,5977023⟩ E))) ⟨241055275648,5964063⟩ (N (N (N E ⟨241055275776,5951137⟩ E) ⟨241055275904,5938247⟩ (N E ⟨241055276032,5925392⟩ E)) ⟨241055276160,5912571⟩ (N (N E ⟨241055276288,5899785⟩ E) ⟨241055276416,5887034⟩ (N E ⟨241055276544,5874317⟩ E)))) ⟨241055276672,5861634⟩ (N (N (N (N E ⟨241055277056,5823791⟩ E) ⟨241189488128,16032890⟩ (N E ⟨241189488256,15997353⟩ E)) ⟨241189488384,15961915⟩ (N (N E ⟨241189488512,15926575⟩ E) ⟨241189488640,15891332⟩ (N E ⟨241189488768,15856187⟩ E))) ⟨241189488896,15821140⟩ (N (N (N E ⟨241189489024,15786189⟩ E) ⟨241189489152,15751334⟩ (N E ⟨241189489280,15716576⟩ E)) ⟨241189489408,15681913⟩ (N (N E ⟨241189489536,15647347⟩ E) ⟨241189489664,15612875⟩ (N E ⟨241189489792,15578498⟩ E))))) ⟨241189489920,15544216⟩ (N (N (N (N (N E ⟨241189490048,15510028⟩ E) ⟨241189490176,15475934⟩ (N E ⟨241189490304,15441933⟩ E)) ⟨241189490432,15408026⟩ (N (N E ⟨241189490560,15374212⟩ E) ⟨241189490688,15340491⟩ (N E ⟨241189490816,15306862⟩ E))) ⟨241189490944,15273325⟩ (N (N (N E ⟨241189491072,15239880⟩ E) ⟨241189491200,15206527⟩ (N E ⟨241189491328,15173265⟩ E)) ⟨241189491456,15140093⟩ (N (N E ⟨241189491584,15107013⟩ E) ⟨241189491712,15074022⟩ (N E ⟨241189491840,15041122⟩ E)))) ⟨241189491968,15008311⟩ (N (N (N (N E ⟨241189492096,14975590⟩ E) ⟨241189492224,14942958⟩ (N E ⟨241189492480,14877960⟩ E)) ⟨241189492608,14845594⟩ (N (N E ⟨241189492736,14813316⟩ E) ⟨241189492864,14781125⟩ (N E ⟨241189492992,14749022⟩ E))) ⟨241189493120,14717005⟩ (N (N (N E ⟨241189493376,14653233⟩ E) ⟨241189493504,14621477⟩ (N E ⟨241189493632,14589807⟩ E)) ⟨241189493760,14558222⟩ (N (N E ⟨241189493888,14526723⟩ E) ⟨241189494016,14495308⟩ (N E ⟨241189494144,14463979⟩ E))))))))

noncomputable def tab22 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨241189494528,14370498⟩ E) ⟨241189494656,14339506⟩ E) ⟨241189494784,14308597⟩ (N E ⟨241323706112,29621997⟩ E)) ⟨241323706240,29556413⟩ (N (N E ⟨241323706368,29491010⟩ E) ⟨241323706496,29425789⟩ (N E ⟨241323706624,29360747⟩ E))) ⟨241323706752,29295886⟩ (N (N (N E ⟨241323706880,29231203⟩ E) ⟨241323707008,29166699⟩ (N E ⟨241323707136,29102372⟩ E)) ⟨241323707264,29038223⟩ (N (N E ⟨241323707392,28974251⟩ E) ⟨241323707520,28910455⟩ (N E ⟨241323707648,28846834⟩ E)))) ⟨241323707776,28783388⟩ (N (N (N (N E ⟨241323707904,28720116⟩ E) ⟨241323708032,28657019⟩ (N E ⟨241323708160,28594094⟩ E)) ⟨241323708288,28531343⟩ (N (N E ⟨241323708416,28468763⟩ E) ⟨241323708544,28406355⟩ (N E ⟨241323708672,28344117⟩ E))) ⟨241323708800,28282051⟩ (N (N (N E ⟨241323708928,28220154⟩ E) ⟨241323709056,28158426⟩ (N E ⟨241323709184,28096867⟩ E)) ⟨241323709312,28035476⟩ (N (N E ⟨241323709440,27974253⟩ E) ⟨241323709568,27913196⟩ (N E ⟨241323709824,27791583⟩ E))))) ⟨241323709952,27731025⟩ (N (N (N (N (N E ⟨241323710080,27670631⟩ E) ⟨241323710208,27610402⟩ (N E ⟨241323710336,27550337⟩ E)) ⟨241323710464,27490435⟩ (N (N E ⟨241323710592,27430696⟩ E) ⟨241323710720,27371119⟩ (N E ⟨241323710848,27311704⟩ E))) ⟨241323711104,27193356⟩ (N (N (N E ⟨241323711232,27134423⟩ E) ⟨241323711360,27075649⟩ (N E ⟨241323711488,27017034⟩ E)) ⟨241323711616,26958578⟩ (N (N E ⟨241323711744,26900280⟩ E) ⟨241323712000,26784156⟩ (N E ⟨241323712128,26726329⟩ E)))) ⟨241323712256,26668658⟩ (N (N (N (N E ⟨241323712384,26611142⟩ E) ⟨241323712512,26553782⟩ (N E ⟨241457923968,47377506⟩ E)) ⟨241457924096,47272669⟩ (N (N E ⟨241457924224,47168122⟩ E) ⟨241457924352,47063864⟩ (N E ⟨241457924480,46959894⟩ E))) ⟨241457924608,46856210⟩ (N (N (N E ⟨241457924736,46752813⟩ E) ⟨241457924864,46649701⟩ (N E ⟨241457924992,46546873⟩ E)) ⟨241457925120,46444328⟩ (N (N E ⟨241457925248,46342066⟩ E) ⟨241457925376,46240085⟩ (N E ⟨241457925504,46138384⟩ E)))))) ⟨241457925632,46036963⟩ (N (N (N (N (N (N E ⟨241457925760,45935821⟩ E) ⟨241457925888,45834956⟩ (N E ⟨241457926016,45734368⟩ E)) ⟨241457926144,45634056⟩ (N (N E ⟨241457926272,45534018⟩ E) ⟨241457926400,45434255⟩ (N E ⟨241457926528,45334765⟩ E))) ⟨241457926656,45235547⟩ (N (N (N E ⟨241457926784,45136600⟩ E) ⟨241457926912,45037924⟩ (N E ⟨241457927040,44939517⟩ E)) ⟨241457927168,44841379⟩ (N (N E ⟨241457927296,44743509⟩ E) ⟨241457927424,44645906⟩ (N E ⟨241457927552,44548569⟩ E)))) ⟨241457927680,44451497⟩ (N (N (N (N E ⟨241457927808,44354689⟩ E) ⟨241457927936,44258145⟩ (N E ⟨241457928064,44161863⟩ E)) ⟨241457928192,44065843⟩ (N (N E ⟨241457928320,43970084⟩ E) ⟨241457928448,43874585⟩ (N E ⟨241457928576,43779346⟩ E))) ⟨241457928704,43684364⟩ (N (N (N E ⟨241457928832,43589640⟩ E) ⟨241457928960,43495173⟩ (N E ⟨241457929088,43400961⟩ E)) ⟨241457929216,43307005⟩ (N (N E ⟨241457929472,43119853⟩ E) ⟨241457929728,42933712⟩ (N E ⟨241457929856,42841018⟩ E))))) ⟨241457929984,42748574⟩ (N (N (N (N (N E ⟨241457930112,42656379⟩ E) ⟨241457930240,42564433⟩ (N E ⟨241592141824,69239427⟩ E)) ⟨241592141952,69086299⟩ (N (N E ⟨241592142080,68933594⟩ E) ⟨241592142208,68781311⟩ (N E ⟨241592142336,68629448⟩ E))) ⟨241592142464,68478004⟩ (N (N (N E ⟨241592142592,68326977⟩ E) ⟨241592142720,68176367⟩ (N E ⟨241592142848,68026172⟩ E)) ⟨241592142976,67876390⟩ (N (N E ⟨241592143104,67727020⟩ E) ⟨241592143232,67578061⟩ (N E ⟨241592143360,67429512⟩ E)))) ⟨241592143488,67281370⟩ (N (N (N (N E ⟨241592143616,67133635⟩ E) ⟨241592143744,66986305⟩ (N E ⟨241592143872,66839380⟩ E)) ⟨241592144000,66692857⟩ (N (N E ⟨241592144128,66546735⟩ E) ⟨241592144256,66401014⟩ (N E ⟨241592144384,66255691⟩ E))) ⟨241592144512,66110766⟩ (N (N (N E ⟨241592144640,65966237⟩ E) ⟨241592144768,65822102⟩ (N E ⟨241592144896,65678361⟩ E)) ⟨241592145024,65535013⟩ (N (N E ⟨241592145152,65392055⟩ E) ⟨241592145280,65249487⟩ (N E ⟨241592145408,65107307⟩ E))))))) ⟨241592145536,64965515⟩ (N (N (N (N (N (N (N E ⟨241592145664,64824108⟩ E) ⟨241592145792,64683086⟩ (N E ⟨241592145920,64542448⟩ E)) ⟨241592146048,64402191⟩ (N (N E ⟨241592146176,64262315⟩ E) ⟨241592146304,64122819⟩ (N E ⟨241592146432,63983702⟩ E))) ⟨241592146560,63844961⟩ (N (N (N E ⟨241592146688,63706596⟩ E) ⟨241592146816,63568606⟩ (N E ⟨241592147072,63293746⟩ E)) ⟨241592147328,63020369⟩ (N (N E ⟨241592147456,62884235⟩ E) ⟨241592147584,62748468⟩ (N E ⟨241592147712,62613067⟩ E)))) ⟨241592147840,62478031⟩ (N (N (N (N E ⟨241592147968,62343359⟩ E) ⟨241726359680,95180899⟩ (N E ⟨241726359808,94970516⟩ E)) ⟨241726359936,94760714⟩ (N (N E ⟨241726360064,94551491⟩ E) ⟨241726360192,94342845⟩ (N E ⟨241726360320,94134774⟩ E))) ⟨241726360448,93927277⟩ (N (N (N E ⟨241726360576,93720351⟩ E) ⟨241726360704,93513995⟩ (N E ⟨241726360832,93308207⟩ E)) ⟨241726360960,93102985⟩ (N (N E ⟨241726361088,92898326⟩ E) ⟨241726361216,92694230⟩ (N E ⟨241726361344,92490694⟩ E))))) ⟨241726361472,92287717⟩ (N (N (N (N (N E ⟨241726361600,92085296⟩ E) ⟨241726361728,91883430⟩ (N E ⟨241726361856,91682117⟩ E)) ⟨241726361984,91481355⟩ (N (N E ⟨241726362112,91281142⟩ E) ⟨241726362240,91081477⟩ (N E ⟨241726362368,90882357⟩ E))) ⟨241726362496,90683782⟩ (N (N (N E ⟨241726362624,90485749⟩ E) ⟨241726362752,90288256⟩ (N E ⟨241726362880,90091302⟩ E)) ⟨241726363008,89894884⟩ (N (N E ⟨241726363136,89699002⟩ E) ⟨241726363264,89503653⟩ (N E ⟨241726363392,89308836⟩ E)))) ⟨241726363520,89114548⟩ (N (N (N (N E ⟨241726363776,88727556⟩ E) ⟨241726363904,88534848⟩ (N E ⟨241726364032,88342663⟩ E)) ⟨241726364160,88150999⟩ (N (N E ⟨241726364288,87959854⟩ E) ⟨241726364416,87769228⟩ (N E ⟨241726364672,87389522⟩ E))) ⟨241726364800,87200440⟩ (N (N (N E ⟨241726364928,87011868⟩ E) ⟨241726365056,86823806⟩ (N E ⟨241726365184,86636252⟩ E)) ⟨241726365440,86262661⟩ (N (N E ⟨241726365568,86076621⟩ E) ⟨241726365696,85891082⟩ (N E ⟨241860577664,124896152⟩ E)))))) ⟨241860577792,124620392⟩ (N (N (N (N (N (N E ⟨241860577920,124345394⟩ E) ⟨241860578048,124071153⟩ (N E ⟨241860578176,123797669⟩ E)) ⟨241860578304,123524937⟩ (N (N E ⟨241860578432,123252957⟩ E) ⟨241860578560,122981724⟩ (N E ⟨241860578688,122711238⟩ E))) ⟨241860578816,122441495⟩ (N (N (N E ⟨241860578944,122172493⟩ E) ⟨241860579072,121904229⟩ (N E ⟨241860579200,121636702⟩ E)) ⟨241860579328,121369908⟩ (N (N E ⟨241860579456,121103845⟩ E) ⟨241860579584,120838511⟩ (N E ⟨241860579712,120573903⟩ E)))) ⟨241860579840,120310020⟩ (N (N (N (N E ⟨241860579968,120046858⟩ E) ⟨241860580096,119784416⟩ (N E ⟨241860580224,119522690⟩ E)) ⟨241860580352,119261679⟩ (N (N E ⟨241860580480,119001380⟩ E) ⟨241860580608,118741791⟩ (N E ⟨241860580736,118482910⟩ E))) ⟨241860580864,118224734⟩ (N (N (N E ⟨241860580992,117967261⟩ E) ⟨241860581120,117710488⟩ (N E ⟨241860581248,117454414⟩ E)) ⟨241860581376,117199036⟩ (N (N E ⟨241860581504,116944352⟩ E) ⟨241860581632,116690360⟩ (N E ⟨241860581760,116437057⟩ E))))) ⟨241860581888,116184441⟩ (N (N (N (N (N E ⟨241860582016,115932509⟩ E) ⟨241860582144,115681261⟩ (N E ⟨241860582272,115430692⟩ E)) ⟨241860582400,115180802⟩ (N (N E ⟨241860582528,114931588⟩ E) ⟨241860582656,114683048⟩ (N E ⟨241860582784,114435179⟩ E))) ⟨241860582912,114187980⟩ (N (N (N E ⟨241860583040,113941448⟩ E) ⟨241860583168,113695581⟩ (N E ⟨241860583296,113450377⟩ E)) ⟨241860583424,113205834⟩ (N (N E ⟨241994795648,158481188⟩ E) ⟨241994795776,158131662⟩ (N E ⟨241994795904,157783099⟩ E)))) ⟨241994796032,157435496⟩ (N (N (N (N E ⟨241994796160,157088851⟩ E) ⟨241994796288,156743159⟩ (N E ⟨241994796416,156398417⟩ E)) ⟨241994796544,156054623⟩ (N (N E ⟨241994796672,155711773⟩ E) ⟨241994796800,155369865⟩ (N E ⟨241994796928,155028895⟩ E))) ⟨241994797056,154688859⟩ (N (N (N E ⟨241994797184,154349756⟩ E) ⟨241994797312,154011581⟩ (N E ⟨241994797440,153674333⟩ E)) ⟨241994797568,153338007⟩ (N (N E ⟨241994797696,153002601⟩ E) ⟨241994797824,152668112⟩ (N E ⟨241994797952,152334536⟩ E))))))))

noncomputable def tab23 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨241994798208,151670114⟩ E) ⟨241994798336,151339262⟩ (N E ⟨241994798464,151009311⟩ E)) ⟨241994798592,150680260⟩ (N (N E ⟨241994798720,150352104⟩ E) ⟨241994798848,150024842⟩ (N E ⟨241994798976,149698469⟩ E))) ⟨241994799104,149372984⟩ (N (N (N E ⟨241994799232,149048383⟩ E) ⟨241994799360,148724663⟩ (N E ⟨241994799488,148401822⟩ E)) ⟨241994799616,148079857⟩ (N (N E ⟨241994799744,147758765⟩ E) ⟨241994799872,147438542⟩ (N E ⟨241994800000,147119187⟩ E)))) ⟨241994800128,146800696⟩ (N (N (N (N E ⟨241994800256,146483067⟩ E) ⟨241994800384,146166296⟩ (N E ⟨241994800512,145850382⟩ E)) ⟨241994800640,145535320⟩ (N (N E ⟨241994800768,145221109⟩ E) ⟨241994800896,144907746⟩ (N E ⟨241994801024,144595228⟩ E))) ⟨241994801152,144283552⟩ (N (N (N E ⟨242129013376,196743240⟩ E) ⟨242129013504,196309328⟩ (N E ⟨242129013632,195876612⟩ E)) ⟨242129013760,195445088⟩ (N (N E ⟨242129013888,195014752⟩ E) ⟨242129014016,194585599⟩ (N E ⟨242129014144,194157627⟩ E))))) ⟨242129014272,193730831⟩ (N (N (N (N (N E ⟨242129014400,193305207⟩ E) ⟨242129014528,192880752⟩ (N E ⟨242129014656,192457461⟩ E)) ⟨242129014784,192035331⟩ (N (N E ⟨242129014912,191614359⟩ E) ⟨242129015040,191194539⟩ (N E ⟨242129015168,190775868⟩ E))) ⟨242129015296,190358343⟩ (N (N (N E ⟨242129015424,189941960⟩ E) ⟨242129015552,189526715⟩ (N E ⟨242129015680,189112605⟩ E)) ⟨242129015808,188699625⟩ (N (N E ⟨242129015936,188287772⟩ E) ⟨242129016064,187877042⟩ (N E ⟨242129016192,187467432⟩ E)))) ⟨242129016320,187058937⟩ (N (N (N (N E ⟨242129016448,186651555⟩ E) ⟨242129016576,186245282⟩ (N E ⟨242129016704,185840113⟩ E)) ⟨242129016832,185436046⟩ (N (N E ⟨242129016960,185033077⟩ E) ⟨242129017088,184631202⟩ (N E ⟨242129017216,184230418⟩ E))) ⟨242129017344,183830721⟩ (N (N (N E ⟨242129017472,183432107⟩ E) ⟨242129017600,183034573⟩ (N E ⟨242129017728,182638116⟩ E)) ⟨242129017856,182242732⟩ (N (N E ⟨242129017984,181848418⟩ E) ⟨242129018112,181455169⟩ (N E ⟨242129018240,181062984⟩ E)))))) ⟨242129018368,180671857⟩ (N (N (N (N (N (N E ⟨242129018496,180281786⟩ E) ⟨242129018624,179892768⟩ (N E ⟨242129018752,179504798⟩ E)) ⟨242129018880,179117874⟩ (N (N E ⟨242263231232,238594663⟩ E) ⟨242263231360,238068739⟩ (N E ⟨242263231488,237544264⟩ E))) ⟨242263231616,237021232⟩ (N (N (N E ⟨242263231744,236499640⟩ E) ⟨242263231872,235979482⟩ (N E ⟨242263232000,235460753⟩ E)) ⟨242263232128,234943450⟩ (N (N E ⟨242263232256,234427566⟩ E) ⟨242263232384,233913098⟩ (N E ⟨242263232512,233400041⟩ E)))) ⟨242263232640,232888389⟩ (N (N (N (N E ⟨242263232768,232378140⟩ E) ⟨242263232896,231869287⟩ (N E ⟨242263233024,231361827⟩ E)) ⟨242263233152,230855754⟩ (N (N E ⟨242263233280,230351065⟩ E) ⟨242263233408,229847754⟩ (N E ⟨242263233536,229345818⟩ E))) ⟨242263233664,228845251⟩ (N (N (N E ⟨242263233792,228346049⟩ E) ⟨242263233920,227848208⟩ (N E ⟨242263234048,227351723⟩ E)) ⟨242263234176,226856591⟩ (N (N E ⟨242263234304,226362805⟩ E) ⟨242263234432,225870363⟩ (N E ⟨242263234560,225379259⟩ E))))) ⟨242263234688,224889490⟩ (N (N (N (N (N E ⟨242263234816,224401050⟩ E) ⟨242263234944,223913936⟩ (N E ⟨242263235072,223428144⟩ E)) ⟨242263235200,222943668⟩ (N (N E ⟨242263235328,222460505⟩ E) ⟨242263235456,221978651⟩ (N E ⟨242263235584,221498100⟩ E))) ⟨242263235712,221018850⟩ (N (N (N E ⟨242263235840,220540895⟩ E) ⟨242263235968,220064232⟩ (N E ⟨242263236096,219588856⟩ E)) ⟨242263236224,219114764⟩ (N (N E ⟨242263236352,218641950⟩ E) ⟨242263236480,218170411⟩ (N E ⟨242263236608,217700143⟩ E)))) ⟨242397448960,284975656⟩ (N (N (N (N E ⟨242397449088,284347497⟩ E) ⟨242397449216,283721068⟩ (N E ⟨242397449344,283096363⟩ E)) ⟨242397449472,282473377⟩ (N (N E ⟨242397449600,281852104⟩ E) ⟨242397449728,281232539⟩ (N E ⟨242397449856,280614675⟩ E))) ⟨242397449984,279998507⟩ (N (N (N E ⟨242397450112,279384031⟩ E) ⟨242397450240,278771239⟩ (N E ⟨242397450368,278160126⟩ E)) ⟨242397450496,277550688⟩ (N (N E ⟨242397450624,276942918⟩ E) ⟨242397450752,276336812⟩ (N E ⟨242397450880,275732362⟩ E))))))) ⟨242397451008,275129565⟩ (N (N (N (N (N (N (N E ⟨242397451136,274528415⟩ E) ⟨242397451264,273928906⟩ (N E ⟨242397451392,273331032⟩ E)) ⟨242397451520,272734790⟩ (N (N E ⟨242397451648,272140172⟩ E) ⟨242397451776,271547175⟩ (N E ⟨242397451904,270955792⟩ E))) ⟨242397452032,270366018⟩ (N (N (N E ⟨242397452288,269191278⟩ E) ⟨242397452416,268606301⟩ (N E ⟨242397452544,268022913⟩ E)) ⟨242397452672,267441108⟩ (N (N E ⟨242397452800,266860881⟩ E) ⟨242397452928,266282227⟩ (N E ⟨242397453056,265705141⟩ E)))) ⟨242397453184,265129617⟩ (N (N (N (N E ⟨242397453312,264555651⟩ E) ⟨242397453440,263983238⟩ (N E ⟨242397453568,263412373⟩ E)) ⟨242397453696,262843050⟩ (N (N E ⟨242397453824,262275265⟩ E) ⟨242397453952,261709012⟩ (N E ⟨242397454080,261144287⟩ E))) ⟨242397454208,260581085⟩ (N (N (N E ⟨242397454336,260019400⟩ E) ⟨242531666816,334698392⟩ (N E ⟨242531666944,333961037⟩ E)) ⟨242531667072,333225713⟩ (N (N E ⟨242531667200,332492411⟩ E) ⟨242531667328,331761126⟩ (N E ⟨242531667456,331031851⟩ E))))) ⟨242531667584,330304579⟩ (N (N (N (N (N E ⟨242531667712,329579304⟩ E) ⟨242531667840,328856018⟩ (N E ⟨242531667968,328134716⟩ E)) ⟨242531668096,327415391⟩ (N (N E ⟨242531668224,326698036⟩ E) ⟨242531668352,325982645⟩ (N E ⟨242531668480,325269212⟩ E))) ⟨242531668608,324557730⟩ (N (N (N E ⟨242531668736,323848192⟩ E) ⟨242531668864,323140593⟩ (N E ⟨242531668992,322434926⟩ E)) ⟨242531669120,321731184⟩ (N (N E ⟨242531669248,321029362⟩ E) ⟨242531669376,320329452⟩ (N E ⟨242531669504,319631449⟩ E)))) ⟨242531669632,318935347⟩ (N (N (N (N E ⟨242531669760,318241139⟩ E) ⟨242531669888,317548820⟩ (N E ⟨242531670016,316858382⟩ E)) ⟨242531670144,316169820⟩ (N (N E ⟨242531670272,315483128⟩ E) ⟨242531670400,314798300⟩ (N E ⟨242531670528,314115329⟩ E))) ⟨242531670656,313434210⟩ (N (N (N E ⟨242531670784,312754936⟩ E) ⟨242531670912,312077501⟩ (N E ⟨242531671168,310728127⟩ E)) ⟨242531671296,310056176⟩ (N (N E ⟨242531671424,309386040⟩ E) ⟨242531671552,308717714⟩ (N E ⟨242531671680,308051192⟩ E)))))) ⟨242531671808,307386468⟩ (N (N (N (N (N (N E ⟨242531671936,306723537⟩ E) ⟨242531672064,306062392⟩ (N E ⟨242665884544,389104420⟩ E)) ⟨242665884672,388247207⟩ (N (N E ⟨242665884800,387392354⟩ E) ⟨242665884928,386539853⟩ (N E ⟨242665885056,385689695⟩ E))) ⟨242665885184,384841875⟩ (N (N (N E ⟨242665885312,383996383⟩ E) ⟨242665885440,383153212⟩ (N E ⟨242665885568,382312355⟩ E)) ⟨242665885696,381473804⟩ (N (N E ⟨242665885824,380637550⟩ E) ⟨242665885952,379803588⟩ (N E ⟨242665886080,378971909⟩ E)))) ⟨242665886208,378142505⟩ (N (N (N (N E ⟨242665886336,377315370⟩ E) ⟨242665886464,376490495⟩ (N E ⟨242665886592,375667874⟩ E)) ⟨242665886720,374847499⟩ (N (N E ⟨242665886848,374029362⟩ E) ⟨242665886976,373213456⟩ (N E ⟨242665887104,372399775⟩ E))) ⟨242665887232,371588310⟩ (N (N (N E ⟨242665887360,370779055⟩ E) ⟨242665887488,369972002⟩ (N E ⟨242665887616,369167144⟩ E)) ⟨242665887744,368364474⟩ (N (N E ⟨242665887872,367563985⟩ E) ⟨242665888000,366765670⟩ (N E ⟨242665888128,365969521⟩ E))))) ⟨242665888256,365175531⟩ (N (N (N (N (N E ⟨242665888384,364383694⟩ E) ⟨242665888640,362806450⟩ (N E ⟨242665888768,362021029⟩ E)) ⟨242665888896,361237732⟩ (N (N E ⟨242665889024,360456553⟩ E) ⟨242665889280,358900521⟩ (N E ⟨242665889536,357352878⟩ E))) ⟨242665889792,355813570⟩ (N (N (N E ⟨242800102400,446560115⟩ E) ⟨242800102528,445576866⟩ (N E ⟨242800102656,444596323⟩ E)) ⟨242800102784,443618477⟩ (N (N E ⟨242800102912,442643317⟩ E) ⟨242800103040,441670837⟩ (N E ⟨242800103168,440701026⟩ E)))) ⟨242800103296,439733876⟩ (N (N (N (N E ⟨242800103424,438769378⟩ E) ⟨242800103552,437807523⟩ (N E ⟨242800103680,436848304⟩ E)) ⟨242800103808,435891710⟩ (N (N E ⟨242800103936,434937734⟩ E) ⟨242800104064,433986367⟩ (N E ⟨242800104192,433037600⟩ E))) ⟨242800104320,432091425⟩ (N (N (N E ⟨242800104448,431147833⟩ E) ⟨242800104576,430206816⟩ (N E ⟨242800104704,429268365⟩ E)) ⟨242800104832,428332473⟩ (N (N E ⟨242800104960,427399130⟩ E) ⟨242800105088,426468328⟩ (N E ⟨242800105216,425540060⟩ E))))))))

noncomputable def tab24 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨242800105472,423691089⟩ E) ⟨242800105600,422770370⟩ E) ⟨242800105728,421852151⟩ (N E ⟨242800105856,420936424⟩ E)) ⟨242800105984,420023181⟩ (N (N E ⟨242800106112,419112414⟩ E) ⟨242800106496,416394887⟩ (N E ⟨242800106624,415493943⟩ E))) ⟨242800106752,414595435⟩ (N (N (N E ⟨242800106880,413699355⟩ E) ⟨242800107008,412805694⟩ (N E ⟨242800107136,411914446⟩ E)) ⟨242800107392,410139156⟩ (N (N E ⟨242800107520,409255098⟩ E) ⟨242934320256,507757345⟩ (N E ⟨242934320384,506639966⟩ E)))) ⟨242934320512,505525661⟩ (N (N (N (N E ⟨242934320640,504414417⟩ E) ⟨242934320768,503306226⟩ (N E ⟨242934320896,502201078⟩ E)) ⟨242934321024,501098961⟩ (N (N E ⟨242934321152,499999867⟩ E) ⟨242934321280,498903786⟩ (N E ⟨242934321408,497810706⟩ E))) ⟨242934321536,496720620⟩ (N (N (N E ⟨242934321664,495633516⟩ E) ⟨242934321792,494549385⟩ (N E ⟨242934321920,493468217⟩ E)) ⟨242934322048,492390002⟩ (N (N E ⟨242934322176,491314732⟩ E) ⟨242934322304,490242396⟩ (N E ⟨242934322432,489172984⟩ E))))) ⟨242934322560,488106487⟩ (N (N (N (N (N E ⟨242934322688,487042896⟩ E) ⟨242934322816,485982200⟩ (N E ⟨242934322944,484924391⟩ E)) ⟨242934323072,483869460⟩ (N (N E ⟨242934323200,482817396⟩ E) ⟨242934323328,481768190⟩ (N E ⟨242934323456,480721833⟩ E))) ⟨242934323584,479678316⟩ (N (N (N E ⟨242934323712,478637630⟩ E) ⟨242934323840,477599765⟩ (N E ⟨242934323968,476564712⟩ E)) ⟨242934324096,475532462⟩ (N (N E ⟨242934324224,474503005⟩ E) ⟨242934324352,473476334⟩ (N E ⟨242934324480,472452439⟩ E)))) ⟨242934324608,471431310⟩ (N (N (N (N E ⟨242934324736,470412939⟩ E) ⟨242934324992,468384434⟩ (N E ⟨242934325248,466366854⟩ E)) ⟨243068538112,572646451⟩ (N (N E ⟨243068538240,571386970⟩ E) ⟨243068538368,570130951⟩ (N E ⟨243068538496,568878382⟩ E))) ⟨243068538624,567629251⟩ (N (N (N E ⟨243068538752,566383548⟩ E) ⟨243068538880,565141261⟩ (N E ⟨243068539008,563902378⟩ E)) ⟨243068539136,562666890⟩ (N (N E ⟨243068539264,561434783⟩ E) ⟨243068539392,560206048⟩ (N E ⟨243068539520,558980674⟩ E)))))) ⟨243068539648,557758648⟩ (N (N (N (N (N (N E ⟨243068539776,556539961⟩ E) ⟨243068539904,555324601⟩ (N E ⟨243068540032,554112558⟩ E)) ⟨243068540160,552903820⟩ (N (N E ⟨243068540288,551698377⟩ E) ⟨243068540416,550496218⟩ (N E ⟨243068540544,549297333⟩ E))) ⟨243068540672,548101709⟩ (N (N (N E ⟨243068540800,546909338⟩ E) ⟨243068540928,545720208⟩ (N E ⟨243068541056,544534309⟩ E)) ⟨243068541184,543351630⟩ (N (N E ⟨243068541312,542172161⟩ E) ⟨243068541440,540995891⟩ (N E ⟨243068541568,539822810⟩ E)))) ⟨243068541696,538652907⟩ (N (N (N (N E ⟨243068541824,537486172⟩ E) ⟨243068541952,536322596⟩ (N E ⟨243068542080,535162167⟩ E)) ⟨243068542208,534004875⟩ (N (N E ⟨243068542464,531699664⟩ E) ⟨243068542592,530551723⟩ (N E ⟨243068542720,529406880⟩ E))) ⟨243068542848,528265124⟩ (N (N (N E ⟨243068542976,527126444⟩ E) ⟨243202755840,642588983⟩ (N E ⟨243202755968,641175670⟩ E)) ⟨243202756096,639766242⟩ (N (N E ⟨243202756224,638360685⟩ E) ⟨243202756352,636958987⟩ (N E ⟨243202756480,635561135⟩ E))))) ⟨243202756608,634167116⟩ (N (N (N (N (N E ⟨243202756736,632776917⟩ E) ⟨243202756864,631390527⟩ (N E ⟨243202756992,630007933⟩ E)) ⟨243202757120,628629121⟩ (N (N E ⟨243202757248,627254080⟩ E) ⟨243202757376,625882798⟩ (N E ⟨243202757504,624515261⟩ E))) ⟨243202757632,623151458⟩ (N (N (N E ⟨243202757760,621791377⟩ E) ⟨243202757888,620435005⟩ (N E ⟨243202758016,619082330⟩ E)) ⟨243202758144,617733341⟩ (N (N E ⟨243202758272,616388024⟩ E) ⟨243202758400,615046369⟩ (N E ⟨243202758528,613708362⟩ E)))) ⟨243202758656,612373993⟩ (N (N (N (N E ⟨243202758784,611043249⟩ E) ⟨243202758912,609716119⟩ (N E ⟨243202759040,608392590⟩ E)) ⟨243202759168,607072652⟩ (N (N E ⟨243202759296,605756291⟩ E) ⟨243202759424,604443498⟩ (N E ⟨243202759552,603134259⟩ E))) ⟨243202759680,601828565⟩ (N (N (N E ⟨243202759936,599227760⟩ E) ⟨243202760064,597932627⟩ (N E ⟨243202760320,595352843⟩ E)) ⟨243202760448,594068169⟩ (N (N E ⟨243202760704,591509203⟩ E) ⟨243336973696,714862581⟩ (N E ⟨243336973824,713291174⟩ E))))))) ⟨243336973952,711724084⟩ (N (N (N (N (N (N (N E ⟨243336974080,710161296⟩ E) ⟨243336974208,708602796⟩ (N E ⟨243336974336,707048570⟩ E)) ⟨243336974464,705498604⟩ (N (N E ⟨243336974592,703952883⟩ E) ⟨243336974720,702411394⟩ (N E ⟨243336974848,700874123⟩ E))) ⟨243336974976,699341056⟩ (N (N (N E ⟨243336975104,697812179⟩ E) ⟨243336975232,696287479⟩ (N E ⟨243336975360,694766942⟩ E)) ⟨243336975488,693250553⟩ (N (N E ⟨243336975616,691738301⟩ E) ⟨243336975744,690230170⟩ (N E ⟨243336975872,688726149⟩ E)))) ⟨243336976000,687226222⟩ (N (N (N (N E ⟨243336976128,685730377⟩ E) ⟨243336976256,684238601⟩ (N E ⟨243336976384,682750879⟩ E)) ⟨243336976512,681267200⟩ (N (N E ⟨243336976640,679787550⟩ E) ⟨243336976768,678311915⟩ (N E ⟨243336976896,676840283⟩ E))) ⟨243336977024,675372641⟩ (N (N (N E ⟨243336977152,673908975⟩ E) ⟨243336977280,672449272⟩ (N E ⟨243336977408,670993521⟩ E)) ⟨243336977536,669541708⟩ (N (N E ⟨243336977664,668093819⟩ E) ⟨243336977792,666649844⟩ (N E ⟨243336977920,665209768⟩ E))))) ⟨243336978048,663773579⟩ (N (N (N (N (N E ⟨243336978176,662341265⟩ E) ⟨243336978304,660912813⟩ (N E ⟨243336978432,659488210⟩ E)) ⟨243471191552,790674201⟩ (N (N E ⟨243471191680,788937101⟩ E) ⟨243471191808,787204771⟩ (N E ⟨243471191936,785477193⟩ E))) ⟨243471192064,783754353⟩ (N (N (N E ⟨243471192192,782036235⟩ E) ⟨243471192320,780322823⟩ (N E ⟨243471192448,778614103⟩ E)) ⟨243471192576,776910057⟩ (N (N E ⟨243471192704,775210672⟩ E) ⟨243471192832,773515932⟩ (N E ⟨243471192960,771825821⟩ E)))) ⟨243471193088,770140324⟩ (N (N (N (N E ⟨243471193216,768459427⟩ E) ⟨243471193344,766783115⟩ (N E ⟨243471193472,765111371⟩ E)) ⟨243471193600,763444182⟩ (N (N E ⟨243471193728,761781532⟩ E) ⟨243471193856,760123407⟩ (N E ⟨243471193984,758469792⟩ E))) ⟨243471194112,756820672⟩ (N (N (N E ⟨243471194240,755176033⟩ E) ⟨243471194368,753535859⟩ (N E ⟨243471194496,751900137⟩ E)) ⟨243471194624,750268851⟩ (N (N E ⟨243471194752,748641988⟩ E) ⟨243471194880,747019533⟩ (N E ⟨243471195136,743787790⟩ E)))))) ⟨243471195392,740573507⟩ (N (N (N (N (N (N E ⟨243471195520,738972879⟩ E) ⟨243471195648,737376573⟩ (N E ⟨243471195776,735784576⟩ E)) ⟨243471195904,734196874⟩ (N (N E ⟨243471196160,731034299⟩ E) ⟨243605409536,868055598⟩ (N E ⟨243605409664,866150588⟩ E))) ⟨243605409792,864250802⟩ (N (N (N E ⟨243605409920,862356222⟩ E) ⟨243605410048,860466832⟩ (N E ⟨243605410176,858582615⟩ E)) ⟨243605410304,856703554⟩ (N (N E ⟨243605410432,854829631⟩ E) ⟨243605410560,852960830⟩ (N E ⟨243605410688,851097135⟩ E)))) ⟨243605410816,849238527⟩ (N (N (N (N E ⟨243605410944,847384992⟩ E) ⟨243605411072,845536511⟩ (N E ⟨243605411200,843693069⟩ E)) ⟨243605411328,841854649⟩ (N (N E ⟨243605411456,840021235⟩ E) ⟨243605411584,838192811⟩ (N E ⟨243605411712,836369359⟩ E))) ⟨243605411840,834550864⟩ (N (N (N E ⟨243605411968,832737310⟩ E) ⟨243605412096,830928680⟩ (N E ⟨243605412224,829124959⟩ E)) ⟨243605412352,827326130⟩ (N (N E ⟨243605412480,825532178⟩ E) ⟨243605412608,823743087⟩ (N E ⟨243605412736,821958841⟩ E))))) ⟨243605412864,820179423⟩ (N (N (N (N (N E ⟨243605412992,818404820⟩ E) ⟨243605413120,816635014⟩ (N E ⟨243605413248,814869991⟩ E)) ⟨243605413632,809603461⟩ (N (N E ⟨243605413760,807857412⟩ E) ⟨243605413888,806116070⟩ (N E ⟨243739627520,948501872⟩ E))) ⟨243739627648,946422601⟩ (N (N (N E ⟨243739627776,944349025⟩ E) ⟨243739627904,942281126⟩ (N E ⟨243739628032,940218885⟩ E)) ⟨243739628160,938162284⟩ (N (N E ⟨243739628288,936111304⟩ E) ⟨243739628416,934065926⟩ (N E ⟨243739628544,932026134⟩ E)))) ⟨243739628672,929991907⟩ (N (N (N (N E ⟨243739628800,927963228⟩ E) ⟨243739628928,925940079⟩ (N E ⟨243739629056,923922442⟩ E)) ⟨243739629184,921910299⟩ (N (N E ⟨243739629312,919903631⟩ E) ⟨243739629440,917902421⟩ (N E ⟨243739629568,915906651⟩ E))) ⟨243739629696,913916303⟩ (N (N (N E ⟨243739629824,911931360⟩ E) ⟨243739629952,909951804⟩ (N E ⟨243739630080,907977617⟩ E)) ⟨243739630208,906008783⟩ (N (N E ⟨243739630336,904045283⟩ E) ⟨243739630592,900134217⟩ (N E ⟨243739630720,898186617⟩ E))))))))

noncomputable def tab25 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨243739630976,894307197⟩ E) ⟨243739631104,892375343⟩ E) ⟨243739631360,888527262⟩ (N E ⟨243739631488,886611001⟩ E)) ⟨243739631616,884699904⟩ (N (N E ⟨243873845376,1034197051⟩ E) ⟨243873845504,1031931164⟩ (N E ⟨243873845632,1029671481⟩ E))) ⟨243873845760,1027417981⟩ (N (N (N E ⟨243873845888,1025170644⟩ E) ⟨243873846016,1022929449⟩ (N E ⟨243873846144,1020694377⟩ E)) ⟨243873846272,1018465407⟩ (N (N E ⟨243873846528,1014025694⟩ E) ⟨243873846656,1011814911⟩ (N E ⟨243873846784,1009610151⟩ E)))) ⟨243873846912,1007411394⟩ (N (N (N (N E ⟨243873847040,1005218621⟩ E) ⟨243873847168,1003031812⟩ (N E ⟨243873847296,1000850948⟩ E)) ⟨243873847424,998676008⟩ (N (N E ⟨243873847552,996506975⟩ E) ⟨243873847808,992186549⟩ (N E ⟨243873847936,990035118⟩ E))) ⟨243873848064,987889516⟩ (N (N (N E ⟨243873848192,985749725⟩ E) ⟨243873848320,983615725⟩ (N E ⟨243873848576,979365025⟩ E)) ⟨243873848704,977248288⟩ (N (N E ⟨243873848960,973031944⟩ E) ⟨243873849088,970932301⟩ (N E ⟨243873849216,968838320⟩ E))))) ⟨243873849344,966749982⟩ (N (N (N (N (N E ⟨244008063360,1120713201⟩ E) ⟨244008063488,1118260451⟩ (N E ⟨244008063616,1115814408⟩ E)) ⟨244008063744,1113375051⟩ (N (N E ⟨244008063872,1110942357⟩ E) ⟨244008064000,1108516306⟩ (N E ⟨244008064128,1106096874⟩ E))) ⟨244008064256,1103684041⟩ (N (N (N E ⟨244008064384,1101277785⟩ E) ⟨244008064512,1098878084⟩ (N E ⟨244008064640,1096484917⟩ E)) ⟨244008064768,1094098263⟩ (N (N E ⟨244008064896,1091718100⟩ E) ⟨244008065024,1089344408⟩ (N E ⟨244008065280,1084616349⟩ E)))) ⟨244008065408,1082261940⟩ (N (N (N (N E ⟨244008065664,1077572261⟩ E) ⟨244008065792,1075236949⟩ (N E ⟨244008065920,1072907962⟩ E)) ⟨244008066048,1070585278⟩ (N (N E ⟨244008066176,1068268877⟩ E) ⟨244008066304,1065958738⟩ (N E ⟨244008066432,1063654843⟩ E))) ⟨244008066560,1061357169⟩ (N (N (N E ⟨244008067072,1052228295⟩ E) ⟨244142281472,1207405600⟩ (N E ⟨244142281600,1204767452⟩ E)) ⟨244142281728,1202136507⟩ (N (N E ⟨244142281856,1199512742⟩ E) ⟨244142281984,1196896132⟩ (N E ⟨244142282112,1194286654⟩ E)))))) ⟨244142282240,1191684286⟩ (N (N (N (N (N (N E ⟨244142282368,1189089003⟩ E) ⟨244142282496,1186500783⟩ (N E ⟨244142282752,1181345439⟩ E)) ⟨244142282880,1178778269⟩ (N (N E ⟨244142283008,1176218070⟩ E) ⟨244142283136,1173664819⟩ (N E ⟨244142283392,1168579071⟩ E))) ⟨244142283520,1166046529⟩ (N (N (N E ⟨244142283648,1163520846⟩ E) ⟨244142283776,1161001999⟩ (N E ⟨244142284160,1153486251⟩ E)) ⟨244142284288,1150994526⟩ (N (N E ⟨244142284544,1146031233⟩ E) ⟨244142284672,1143559621⟩ (N E ⟨244142284800,1141094669⟩ E)))) ⟨244276499584,1296445633⟩ (N (N (N (N E ⟨244276499840,1290797224⟩ E) ⟨244276499968,1287984558⟩ (N E ⟨244276500096,1285179550⟩ E)) ⟨244276500224,1282382175⟩ (N (N E ⟨244276500352,1279592409⟩ E) ⟨244276500608,1274035603⟩ (N E ⟨244276500736,1271268513⟩ E))) ⟨244276500992,1265756839⟩ (N (N (N E ⟨244276501120,1263012205⟩ E) ⟨244276501248,1260275008⟩ (N E ⟨244276501376,1257545224⟩ E)) ⟨244276501504,1254822828⟩ (N (N E ⟨244276501632,1252107796⟩ E) ⟨244276501760,1249400105⟩ (N E ⟨244276501888,1246699731⟩ E))))) ⟨244276502016,1244006650⟩ (N (N (N (N (N E ⟨244276502400,1235970928⟩ E) ⟨244276502528,1233306783⟩ (N E ⟨244410717440,1393801746⟩ E)) ⟨244410717568,1390762974⟩ (N (N E ⟨244410717696,1387732481⟩ E) ⟨244410718208,1375692753⟩ (N E ⟨244410718464,1369721862⟩ E))) ⟨244410718720,1363783337⟩ (N (N (N E ⟨244410718848,1360826145⟩ E) ⟨244410718976,1357876966⟩ (N E ⟨244410719104,1354935774⟩ E)) ⟨244410719360,1349077245⟩ (N (N E ⟨244410719488,1346159857⟩ E) ⟨244410719616,1343250352⟩ (N E ⟨244410719872,1337454890⟩ E)))) ⟨244410720000,1334568883⟩ (N (N (N (N E ⟨244410720128,1331690657⟩ E) ⟨244410720256,1328820187⟩ (N E ⟨244544935680,1484394517⟩ E)) ⟨244544935808,1481165282⟩ (N (N E ⟨244544936064,1474733118⟩ E) ⟨244544936192,1471530132⟩ (N E ⟨244544936320,1468335838⟩ E))) ⟨244544936704,1458804832⟩ (N (N (N E ⟨244544937088,1449351047⟩ E) ⟨244544937344,1443091055⟩ (N E ⟨244544937472,1439973735⟩ E)) ⟨244544937856,1430672154⟩ (N (N E ⟨244544937984,1427588329⟩ E) ⟨244679154176,1569807544⟩ (N E ⟨244679154560,1559623396⟩ E))))))) ⟨244679154688,1556247046⟩ (N (N (N (N (N (N (N E ⟨244679155200,1542832686⟩ E) ⟨244679155328,1539501708⟩ (N E ⟨244679155712,1529562576⟩ E)) ⟨244813372032,1674065431⟩ (N (N E ⟨244813372928,1648874429⟩ E) ⟨244813373440,1634692240⟩ (N E ⟨244947590272,1769494433⟩ E))) ⟨244947590784,1754250168⟩ (N (N (N E ⟨244947591168,1742924605⟩ E) ⟨245081808896,1854204952⟩ (N E ⟨245216026624,1968476591⟩ E)) ⟨245350244352,2085680892⟩ (N (N E ⟨245484462080,2205757314⟩ E) ⟨245618679808,2328643438⟩ (N E ⟨245752897536,2454275003⟩ E)))) ⟨245887115264,2582585939⟩ (N (N (N (N E ⟨246021332992,2713508404⟩ E) ⟨246155550720,2846972824⟩ (N E ⟨246423986176,3121240784⟩ E)) ⟨246692421632,3404800031⟩ (N (N E ⟨246960857088,3697035617⟩ E) ⟨247095074816,3846208329⟩ (N E ⟨247229292544,3997308832⟩ E))) ⟨247766163456,4619303288⟩ (N (N (N E ⟨247900381184,4778767791⟩ E) ⟨248034598912,4939641699⟩ (N E ⟨249108340864,6252832886⟩ E)) ⟨249108340992,6239369381⟩ (N (N E ⟨249108341120,6225942100⟩ E) ⟨249108341248,6212550927⟩ (N E ⟨249108341376,6199195745⟩ E))))) ⟨249108341504,6185876437⟩ (N (N (N (N (N E ⟨249108341632,6172592889⟩ E) ⟨249108341760,6159344984⟩ (N E ⟨249108341888,6146132609⟩ E)) ⟨249108342016,6132955649⟩ (N (N E ⟨249108342144,6119813990⟩ E) ⟨249108342272,6106707518⟩ (N E ⟨249108342400,6093636122⟩ E))) ⟨249108342528,6080599687⟩ (N (N (N E ⟨249108342656,6067598102⟩ E) ⟨249108342784,6054631256⟩ (N E ⟨249108342912,6041699036⟩ E)) ⟨249108343040,6028801332⟩ (N (N E ⟨249108343168,6015938033⟩ E) ⟨249108343296,6003109029⟩ (N E ⟨249108343424,5990314211⟩ E)))) ⟨249108343552,5977553470⟩ (N (N (N (N E ⟨249108343680,5964826696⟩ E) ⟨249108343808,5952133780⟩ (N E ⟨249108343936,5939474616⟩ E)) ⟨249108344064,5926849095⟩ (N (N E ⟨249108344192,5914257110⟩ E) ⟨249108344320,5901698554⟩ (N E ⟨249108344448,5889173320⟩ E))) ⟨249108344576,5876681304⟩ (N (N (N E ⟨249108344704,5864222398⟩ E) ⟨249108344832,5851796498⟩ (N E ⟨249108344960,5839403498⟩ E)) ⟨249108345088,5827043295⟩ (N (N E ⟨249108345216,5814715784⟩ E) ⟨249108345344,5802420861⟩ (N E ⟨249108345472,5790158424⟩ E)))))) ⟨249108345600,5777928368⟩ (N (N (N (N (N (N E ⟨249108345728,5765730593⟩ E) ⟨249108345856,5753564994⟩ (N E ⟨249108345984,5741431471⟩ E)) ⟨249108346112,5729329922⟩ (N (N E ⟨249108346240,5717260246⟩ E) ⟨249108346368,5705222343⟩ (N E ⟨249108346496,5693216111⟩ E))) ⟨249108346624,5681241451⟩ (N (N (N E ⟨249108346752,5669298264⟩ E) ⟨249108346880,5657386450⟩ (N E ⟨249108347008,5645505910⟩ E)) ⟨249108347136,5633656546⟩ (N (N E ⟨249108347264,5621838259⟩ E) ⟨249108347392,5610050953⟩ (N E ⟨249108347520,5598294529⟩ E)))) ⟨249108347648,5586568890⟩ (N (N (N (N E ⟨249108347776,5574873941⟩ E) ⟨249108347904,5563209583⟩ (N E ⟨249108348032,5551575722⟩ E)) ⟨249108348160,5539972262⟩ (N (N E ⟨249108348288,5528399107⟩ E) ⟨249108348416,5516856162⟩ (N E ⟨249108348544,5505343334⟩ E))) ⟨249108348672,5493860527⟩ (N (N (N E ⟨249108348800,5482407647⟩ E) ⟨249108348928,5470984602⟩ (N E ⟨251792703488,8407872730⟩ E)) ⟨253403316224,9979161698⟩ (N (N E ⟨257698283648,12328914849⟩ E) ⟨257698283776,12297695318⟩ (N E ⟨257698283904,12262871751⟩ E))))) ⟨257698284032,12224472446⟩ (N (N (N (N (N E ⟨257698284160,12182527748⟩ E) ⟨257698284288,12137070023⟩ (N E ⟨257698284416,12088133631⟩ E)) ⟨257698284544,12035754896⟩ (N (N E ⟨257698284672,11979972077⟩ E) ⟨257698284800,11920825333⟩ (N E ⟨257698284928,11858356700⟩ E))) ⟨257698285056,11792610047⟩ (N (N (N E ⟨257698285184,11723631051⟩ E) ⟨257698285312,11651467159⟩ (N E ⟨257698285440,11576167549⟩ E)) ⟨257698285568,11497783098⟩ (N (N E ⟨257698285696,11416366344⟩ E) ⟨257698285824,11331971444⟩ (N E ⟨257698285952,11244654140⟩ E)))) ⟨257698286208,11061482951⟩ (N (N (N (N E ⟨257698286464,10867328815⟩ E) ⟨257698286592,10766288143⟩ (N E ⟨257698286720,10662690453⟩ E)) ⟨257698286848,10556601403⟩ (N (N E ⟨257698286976,10448087897⟩ E) ⟨257698287104,10337218034⟩ (N E ⟨257698287232,10224061067⟩ E))) ⟨257698287488,9991168320⟩ (N (N (N E ⟨257698287616,9871576391⟩ E) ⟨257698287872,9626468354⟩ (N E ⟨257698288000,9501101744⟩ E)) ⟨257698288128,9373961137⟩ (N (N E ⟨257698288256,9245123305⟩ E) ⟨257698288384,9114665747⟩ (N E ⟨257698288512,8982666632⟩ E))))))))

noncomputable def tab26 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨257698288768,8714359474⟩ E) ⟨257698288896,8578210688⟩ E) ⟨257698289152,8302324476⟩ (N E ⟨257698289408,8022193814⟩ E)) ⟨257698289536,7880740680⟩ (N (N E ⟨257698289920,7451814225⟩ E) ⟨257698290048,7307590603⟩ (N E ⟨257698290176,7162880181⟩ E))) ⟨257698290304,7017765309⟩ (N (N (N E ⟨257698290432,6872328267⟩ E) ⟨257698290560,6726651207⟩ (N E ⟨257698290688,6580816113⟩ E)) ⟨257698290816,6434904745⟩ (N (N E ⟨257698290944,6288998599⟩ E) ⟨257698291072,6143178849⟩ (N E ⟨257698291200,5997526311⟩ E)))) ⟨257698291328,5852121386⟩ (N (N (N (N E ⟨257698291456,5707044022⟩ E) ⟨257698291584,5562373662⟩ (N E ⟨257698291712,5418189199⟩ E)) ⟨260919517184,5670598354⟩ (N (N E ⟨261993259008,5754244595⟩ E) ⟨263738089472,5888098910⟩ (N E ⟨264006524928,5908378508⟩ E))) ⟨264140742656,5918481103⟩ (N (N (N E ⟨265214484480,5998314513⟩ E) ⟨266019790848,6056890828⟩ (N E ⟨266288226432,5918661125⟩ E)) ⟨266288226560,5761840971⟩ (N (N E ⟨266288227072,5142792756⟩ E) ⟨266288227328,4839337425⟩ (N E ⟨266288227456,4689402869⟩ E))))) ⟨266288227584,4540766178⟩ (N (N (N (N (N E ⟨266288227712,4393502857⟩ E) ⟨266288227840,4247687290⟩ (N E ⟨266288227968,4103392706⟩ E)) ⟨266288228096,3960691133⟩ (N (N E ⟨266288228352,3680348919⟩ E) ⟨266288228608,3407211498⟩ (N E ⟨266288228736,3273510876⟩ E))) ⟨266288228864,3141808217⟩ (N (N (N E ⟨266288228992,3012166152⟩ E) ⟨266288229376,2636207502⟩ (N E ⟨266288229632,2396951801⟩ E)) ⟨266288229888,2167311862⟩ (N (N E ⟨266288230016,2056225992⟩ E) ⟨266288230144,1947694536⟩ (N E ⟨266288230272,1841764121⟩ E)))) ⟨266288230400,1738479639⟩ (N (N (N (N E ⟨266288230656,1540019276⟩ E) ⟨266288230784,1444924345⟩ (N E ⟨266288230912,1352637219⟩ E)) ⟨266288231680,859762868⟩ (N (N E ⟨266288231808,788033622⟩ E) ⟨266288231936,719347841⟩ (N E ⟨266288232064,653726513⟩ E))) ⟨266288232704,372187771⟩ (N (N (N E ⟨266288232960,281544275⟩ E) ⟨266288233216,203553388⟩ (N E ⟨266288233472,138238021⟩ E)) ⟨266288233600,110332544⟩ (N (N E ⟨266288233728,85590854⟩ E) ⟨266288233984,45574600⟩ (N E ⟨266288234240,18122334⟩ E)))))) ⟨266288234368,9078775⟩ (N (N (N (N (N (N E ⟨266288234496,3137894⟩ E) ⟨266959321984,172829621⟩ (N E ⟨267630411264,48724240⟩ E)) ⟨268033064960,4122194⟩ (N (N E ⟨268569935744,11239370⟩ E) ⟨268569935872,4409498⟩ (N E ⟨268704153344,21393448⟩ E))) ⟨269106806400,35243188⟩ (N (N (N E ⟨269375241984,22183308⟩ E) ⟨270717419392,12880249⟩ (N E ⟨274878169216,1499244⟩ E)) ⟨275146606208,2983⟩ (N (N E ⟨275146606336,2977⟩ E) ⟨275146606464,2972⟩ (N E ⟨275146606592,2966⟩ E)))) ⟨275146606720,2960⟩ (N (N (N (N E ⟨275146606848,2954⟩ E) ⟨275146606976,2949⟩ (N E ⟨275146607104,2943⟩ E)) ⟨275146607232,2937⟩ (N (N E ⟨275146607360,2931⟩ E) ⟨275146607488,2926⟩ (N E ⟨275146607616,2920⟩ E))) ⟨275146607744,2915⟩ (N (N (N E ⟨275146607872,2909⟩ E) ⟨275146608000,2903⟩ (N E ⟨275146608128,2898⟩ E)) ⟨275146608256,2892⟩ (N (N E ⟨275146608384,2887⟩ E) ⟨275146608512,2881⟩ (N E ⟨275146608640,2875⟩ E))))) ⟨275146608768,2870⟩ (N (N (N (N (N E ⟨275146608896,2864⟩ E) ⟨275146609024,2859⟩ (N E ⟨275146609152,2853⟩ E)) ⟨275146609280,2848⟩ (N (N E ⟨275146609408,2842⟩ E) ⟨275146609536,2837⟩ (N E ⟨275146609664,2832⟩ E))) ⟨275146609792,2826⟩ (N (N (N E ⟨275146609920,2821⟩ E) ⟨275146610048,2815⟩ (N E ⟨275146610176,2810⟩ E)) ⟨275146610304,2805⟩ (N (N E ⟨275146610432,2799⟩ E) ⟨275146610560,2794⟩ (N E ⟨275146610688,2789⟩ E)))) ⟨275146610816,2783⟩ (N (N (N (N E ⟨275146610944,2778⟩ E) ⟨275146611072,2773⟩ (N E ⟨275146611200,2767⟩ E)) ⟨275146611328,2762⟩ (N (N E ⟨275146611456,2757⟩ E) ⟨275146611584,2752⟩ (N E ⟨275146611712,2746⟩ E))) ⟨275146611968,2736⟩ (N (N (N E ⟨275146612096,2731⟩ E) ⟨275146612224,2726⟩ (N E ⟨275146612352,2720⟩ E)) ⟨275146612608,2710⟩ (N (N E ⟨275146612736,2705⟩ E) ⟨275280823936,1744189⟩ (N E ⟨275280824064,1740805⟩ E))))))) ⟨275280824192,1737429⟩ (N (N (N (N (N (N (N E ⟨275280824320,1734062⟩ E) ⟨275280824448,1730703⟩ (N E ⟨275280824576,1727352⟩ E)) ⟨275280824704,1724009⟩ (N (N E ⟨275280824832,1720674⟩ E) ⟨275280824960,1717348⟩ (N E ⟨275280825088,1714029⟩ E))) ⟨275280825216,1710718⟩ (N (N (N E ⟨275280825344,1707415⟩ E) ⟨275280825472,1704121⟩ (N E ⟨275280825600,1700834⟩ E)) ⟨275280825728,1697555⟩ (N (N E ⟨275280825856,1694284⟩ E) ⟨275280825984,1691021⟩ (N E ⟨275280826112,1687766⟩ E)))) ⟨275280826240,1684518⟩ (N (N (N (N E ⟨275280826368,1681279⟩ E) ⟨275280826496,1678047⟩ (N E ⟨275280826624,1674823⟩ E)) ⟨275280826752,1671606⟩ (N (N E ⟨275280826880,1668398⟩ E) ⟨275280827136,1662004⟩ (N E ⟨275280827264,1658818⟩ E))) ⟨275280827392,1655640⟩ (N (N (N E ⟨275280827520,1652470⟩ E) ⟨275280827648,1649307⟩ (N E ⟨275280827776,1646152⟩ E)) ⟨275280827904,1643004⟩ (N (N E ⟨275280828032,1639864⟩ E) ⟨275280828160,1636731⟩ (N E ⟨275280828288,1633606⟩ E))))) ⟨275280828416,1630489⟩ (N (N (N (N (N E ⟨275280828544,1627378⟩ E) ⟨275280828672,1624276⟩ (N E ⟨275280828800,1621180⟩ E)) ⟨275280828928,1618092⟩ (N (N E ⟨275280829056,1615011⟩ E) ⟨275280829184,1611938⟩ (N E ⟨275280829312,1608872⟩ E))) ⟨275280829568,1602761⟩ (N (N (N E ⟨275280829696,1599717⟩ E) ⟨275280829824,1596680⟩ (N E ⟨275280830208,1587612⟩ E)) ⟨275280830464,1581602⟩ (N (N E ⟨275415041792,6683543⟩ E) ⟨275415041920,6670583⟩ (N E ⟨275415042048,6657655⟩ E)))) ⟨275415042176,6644758⟩ (N (N (N (N E ⟨275415042304,6631892⟩ E) ⟨275415042432,6619058⟩ (N E ⟨275415042560,6606254⟩ E)) ⟨275415042688,6593482⟩ (N (N E ⟨275415042816,6580740⟩ E) ⟨275415042944,6568029⟩ (N E ⟨275415043072,6555349⟩ E))) ⟨275415043200,6542699⟩ (N (N (N E ⟨275415043328,6530080⟩ E) ⟨275415043456,6517492⟩ (N E ⟨275415043584,6504933⟩ E)) ⟨275415043712,6492405⟩ (N (N E ⟨275415043840,6479907⟩ E) ⟨275415043968,6467439⟩ (N E ⟨275415044096,6455001⟩ E)))))) ⟨275415044224,6442593⟩ (N (N (N (N (N (N E ⟨275415044352,6430215⟩ E) ⟨275415044480,6417866⟩ (N E ⟨275415044608,6405547⟩ E)) ⟨275415044736,6393258⟩ (N (N E ⟨275415044864,6380998⟩ E) ⟨275415044992,6368768⟩ (N E ⟨275415045120,6356566⟩ E))) ⟨275415045248,6344394⟩ (N (N (N E ⟨275415045376,6332251⟩ E) ⟨275415045504,6320138⟩ (N E ⟨275415045632,6308053⟩ E)) ⟨275415045760,6295997⟩ (N (N E ⟨275415045888,6283969⟩ E) ⟨275415046016,6271971⟩ (N E ⟨275415046144,6260001⟩ E)))) ⟨275415046272,6248060⟩ (N (N (N (N E ⟨275415046400,6236147⟩ E) ⟨275415046528,6224262⟩ (N E ⟨275415046784,6200578⟩ E)) ⟨275415047040,6177006⟩ (N (N E ⟨275415047168,6165263⟩ E) ⟨275415047296,6153547⟩ (N E ⟨275415047808,6106961⟩ E))) ⟨275415048192,6072310⟩ (N (N (N E ⟨275549259520,14837557⟩ E) ⟨275549259648,14808787⟩ (N E ⟨275549259776,14780086⟩ E)) ⟨275549259904,14751455⟩ (N (N E ⟨275549260032,14722893⟩ E) ⟨275549260160,14694400⟩ (N E ⟨275549260288,14665976⟩ E))))) ⟨275549260416,14637621⟩ (N (N (N (N (N E ⟨275549260544,14609334⟩ E) ⟨275549260672,14581116⟩ (N E ⟨275549260800,14552966⟩ E)) ⟨275549260928,14524883⟩ (N (N E ⟨275549261056,14496869⟩ E) ⟨275549261184,14468922⟩ (N E ⟨275549261312,14441042⟩ E))) ⟨275549261440,14413229⟩ (N (N (N E ⟨275549261568,14385483⟩ E) ⟨275549261696,14357804⟩ (N E ⟨275549261824,14330192⟩ E)) ⟨275549261952,14302646⟩ (N (N E ⟨275549262080,14275166⟩ E) ⟨275549262208,14247752⟩ (N E ⟨275549262336,14220404⟩ E)))) ⟨275549262464,14193121⟩ (N (N (N (N E ⟨275549262592,14165904⟩ E) ⟨275549262720,14138752⟩ (N E ⟨275549262848,14111665⟩ E)) ⟨275549262976,14084643⟩ (N (N E ⟨275549263232,14030793⟩ E) ⟨275549263360,14003964⟩ (N E ⟨275549263488,13977200⟩ E))) ⟨275549263616,13950499⟩ (N (N (N E ⟨275549263744,13923862⟩ E) ⟨275549263872,13897289⟩ (N E ⟨275549264000,13870779⟩ E)) ⟨275549264128,13844332⟩ (N (N E ⟨275549264256,13817949⟩ E) ⟨275549264384,13791628⟩ (N E ⟨275549264512,13765369⟩ E))))))))

noncomputable def tab27 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨275549264768,13713040⟩ E) ⟨275549265024,13660959⟩ E) ⟨275549265152,13635012⟩ (N E ⟨275549265280,13609125⟩ E)) ⟨275549265408,13583301⟩ (N (N E ⟨275549265920,13480613⟩ E) ⟨275683477504,26105768⟩ (N E ⟨275683477632,26055198⟩ E))) ⟨275683477760,26004749⟩ (N (N (N E ⟨275683477888,25954423⟩ E) ⟨275683478016,25904219⟩ (N E ⟨275683478144,25854136⟩ E)) ⟨275683478272,25804173⟩ (N (N E ⟨275683478400,25754332⟩ E) ⟨275683478528,25704611⟩ (N E ⟨275683478656,25655009⟩ E)))) ⟨275683478784,25605528⟩ (N (N (N (N E ⟨275683478912,25556165⟩ E) ⟨275683479040,25506922⟩ (N E ⟨275683479168,25457797⟩ E)) ⟨275683479296,25408790⟩ (N (N E ⟨275683479424,25359901⟩ E) ⟨275683479552,25311130⟩ (N E ⟨275683479680,25262476⟩ E))) ⟨275683479808,25213939⟩ (N (N (N E ⟨275683479936,25165518⟩ E) ⟨275683480064,25117213⟩ (N E ⟨275683480192,25069025⟩ E)) ⟨275683480320,25020952⟩ (N (N E ⟨275683480448,24972994⟩ E) ⟨275683480576,24925151⟩ (N E ⟨275683480704,24877422⟩ E))))) ⟨275683480832,24829808⟩ (N (N (N (N (N E ⟨275683480960,24782307⟩ E) ⟨275683481088,24734921⟩ (N E ⟨275683481216,24687647⟩ E)) ⟨275683481344,24640486⟩ (N (N E ⟨275683481472,24593438⟩ E) ⟨275683481600,24546502⟩ (N E ⟨275683481728,24499678⟩ E))) ⟨275683481856,24452966⟩ (N (N (N E ⟨275683481984,24406365⟩ E) ⟨275683482112,24359874⟩ (N E ⟨275683482240,24313495⟩ E)) ⟨275683482368,24267226⟩ (N (N E ⟨275683482496,24221067⟩ E) ⟨275683482624,24175018⟩ (N E ⟨275683482752,24129078⟩ E)))) ⟨275683482880,24083247⟩ (N (N (N (N E ⟨275683483008,24037525⟩ E) ⟨275683483136,23991911⟩ (N E ⟨275683483264,23946406⟩ E)) ⟨275683483392,23901008⟩ (N (N E ⟨275683483648,23810535⟩ E) ⟨275817695104,40716091⟩ (N E ⟨275817695232,40637180⟩ E))) ⟨275817695360,40558460⟩ (N (N (N E ⟨275817695488,40479930⟩ E) ⟨275817695616,40401590⟩ (N E ⟨275817695744,40323440⟩ E)) ⟨275817695872,40245479⟩ (N (N E ⟨275817696000,40167706⟩ E) ⟨275817696128,40090121⟩ (N E ⟨275817696256,40012723⟩ E)))))) ⟨275817696384,39935512⟩ (N (N (N (N (N (N E ⟨275817696512,39858487⟩ E) ⟨275817696640,39781648⟩ (N E ⟨275817696768,39704993⟩ E)) ⟨275817696896,39628524⟩ (N (N E ⟨275817697024,39552238⟩ E) ⟨275817697152,39476136⟩ (N E ⟨275817697280,39400217⟩ E))) ⟨275817697408,39324480⟩ (N (N (N E ⟨275817697536,39248925⟩ E) ⟨275817697664,39173552⟩ (N E ⟨275817697792,39098359⟩ E)) ⟨275817697920,39023347⟩ (N (N E ⟨275817698048,38948515⟩ E) ⟨275817698176,38873862⟩ (N E ⟨275817698304,38799388⟩ E)))) ⟨275817698432,38725092⟩ (N (N (N (N E ⟨275817698560,38650974⟩ E) ⟨275817698688,38577033⟩ (N E ⟨275817698816,38503269⟩ E)) ⟨275817698944,38429681⟩ (N (N E ⟨275817699072,38356269⟩ E) ⟨275817699200,38283032⟩ (N E ⟨275817699328,38209970⟩ E))) ⟨275817699456,38137082⟩ (N (N (N E ⟨275817699584,38064368⟩ E) ⟨275817699712,37991827⟩ (N E ⟨275817699968,37847263⟩ E)) ⟨275817700096,37775238⟩ (N (N E ⟨275817700352,37631703⟩ E) ⟨275817700480,37560192⟩ (N E ⟨275817700608,37488850⟩ E))))) ⟨275817700736,37417677⟩ (N (N (N (N (N E ⟨275817701248,37134670⟩ E) ⟨275817701376,37064337⟩ (N E ⟨275951913088,58261776⟩ E)) ⟨275951913216,58148969⟩ (N (N E ⟨275951913344,58036435⟩ E) ⟨275951913472,57924173⟩ (N E ⟨275951913600,57812183⟩ E))) ⟨275951913728,57700463⟩ (N (N (N E ⟨275951913856,57589013⟩ E) ⟨275951913984,57477832⟩ (N E ⟨275951914112,57366919⟩ E)) ⟨275951914240,57256273⟩ (N (N E ⟨275951914368,57145894⟩ E) ⟨275951914496,57035781⟩ (N E ⟨275951914624,56925933⟩ E)))) ⟨275951914752,56816350⟩ (N (N (N (N E ⟨275951914880,56707030⟩ E) ⟨275951915008,56597973⟩ (N E ⟨275951915136,56489178⟩ E)) ⟨275951915264,56380645⟩ (N (N E ⟨275951915392,56272372⟩ E) ⟨275951915520,56164358⟩ (N E ⟨275951915648,56056604⟩ E))) ⟨275951915776,55949108⟩ (N (N (N E ⟨275951915904,55841870⟩ E) ⟨275951916032,55734889⟩ (N E ⟨275951916160,55628164⟩ E)) ⟨275951916288,55521694⟩ (N (N E ⟨275951916416,55415478⟩ E) ⟨275951916544,55309517⟩ (N E ⟨275951916672,55203809⟩ E))))))) ⟨275951916800,55098353⟩ (N (N (N (N (N (N (N E ⟨275951916928,54993149⟩ E) ⟨275951917056,54888196⟩ (N E ⟨275951917184,54783494⟩ E)) ⟨275951917312,54679041⟩ (N (N E ⟨275951917440,54574836⟩ E) ⟨275951917568,54470880⟩ (N E ⟨275951917696,54367172⟩ E))) ⟨275951917824,54263710⟩ (N (N (N E ⟨275951917952,54160494⟩ E) ⟨275951918080,54057523⟩ (N E ⟨275951918336,53852316⟩ E)) ⟨275951918464,53750077⟩ (N (N E ⟨275951918592,53648081⟩ E) ⟨275951918976,53343541⟩ (N E ⟨275951919104,53242508⟩ E)))) ⟨276086130944,79010464⟩ (N (N (N (N E ⟨276086131072,78857558⟩ E) ⟨276086131200,78705021⟩ (N E ⟨276086131328,78552853⟩ E)) ⟨276086131456,78401052⟩ (N (N E ⟨276086131584,78249618⟩ E) ⟨276086131712,78098550⟩ (N E ⟨276086131840,77947846⟩ E))) ⟨276086131968,77797505⟩ (N (N (N E ⟨276086132096,77647527⟩ E) ⟨276086132224,77497910⟩ (N E ⟨276086132352,77348653⟩ E)) ⟨276086132480,77199755⟩ (N (N E ⟨276086132608,77051216⟩ E) ⟨276086132736,76903034⟩ (N E ⟨276086132864,76755207⟩ E))))) ⟨276086132992,76607736⟩ (N (N (N (N (N E ⟨276086133120,76460619⟩ E) ⟨276086133248,76313855⟩ (N E ⟨276086133376,76167443⟩ E)) ⟨276086133504,76021383⟩ (N (N E ⟨276086133632,75875672⟩ E) ⟨276086133760,75730310⟩ (N E ⟨276086133888,75585296⟩ E))) ⟨276086134016,75440629⟩ (N (N (N E ⟨276086134144,75296308⟩ E) ⟨276086134272,75152332⟩ (N E ⟨276086134400,75008700⟩ E)) ⟨276086134528,74865411⟩ (N (N E ⟨276086134656,74722464⟩ E) ⟨276086134784,74579858⟩ (N E ⟨276086134912,74437592⟩ E)))) ⟨276086135040,74295666⟩ (N (N (N (N E ⟨276086135168,74154077⟩ E) ⟨276086135296,74012826⟩ (N E ⟨276086135424,73871911⟩ E)) ⟨276086135680,73591086⟩ (N (N E ⟨276086135808,73451173⟩ E) ⟨276086136064,73172345⟩ (N E ⟨276086136192,73033427⟩ E))) ⟨276086136320,72894839⟩ (N (N (N E ⟨276086136448,72756580⟩ E) ⟨276086136576,72618648⟩ (N E ⟨276086136704,72481042⟩ E)) ⟨276086136832,72343763⟩ (N (N E ⟨276220348800,102861621⟩ E) ⟨276220348928,102662653⟩ (N E ⟨276220349056,102464165⟩ E)))))) ⟨276220349184,102266156⟩ (N (N (N (N (N (N E ⟨276220349312,102068626⟩ E) ⟨276220349440,101871573⟩ (N E ⟨276220349568,101674995⟩ E)) ⟨276220349696,101478891⟩ (N (N E ⟨276220349824,101283259⟩ E) ⟨276220349952,101088099⟩ (N E ⟨276220350080,100893409⟩ E))) ⟨276220350208,100699188⟩ (N (N (N E ⟨276220350336,100505433⟩ E) ⟨276220350464,100312144⟩ (N E ⟨276220350592,100119320⟩ E)) ⟨276220350720,99926959⟩ (N (N E ⟨276220350848,99735060⟩ E) ⟨276220350976,99543622⟩ (N E ⟨276220351104,99352642⟩ E)))) ⟨276220351232,99162121⟩ (N (N (N (N E ⟨276220351360,98972056⟩ E) ⟨276220351488,98782446⟩ (N E ⟨276220351616,98593290⟩ E)) ⟨276220351744,98404587⟩ (N (N E ⟨276220351872,98216335⟩ E) ⟨276220352000,98028533⟩ (N E ⟨276220352128,97841180⟩ E))) ⟨276220352256,97654274⟩ (N (N (N E ⟨276220352384,97467814⟩ E) ⟨276220352512,97281800⟩ (N E ⟨276220352640,97096229⟩ E)) ⟨276220352768,96911100⟩ (N (N E ⟨276220352896,96726412⟩ E) ⟨276220353024,96542164⟩ (N E ⟨276220353152,96358355⟩ E))))) ⟨276220353280,96174983⟩ (N (N (N (N (N E ⟨276220353536,95809546⟩ E) ⟨276220353664,95627478⟩ (N E ⟨276220353792,95445843⟩ E)) ⟨276220353920,95264639⟩ (N (N E ⟨276220354048,95083865⟩ E) ⟨276220354176,94903519⟩ (N E ⟨276220354304,94723601⟩ E))) ⟨276220354560,94365042⟩ (N (N (N E ⟨276354566528,130043352⟩ E) ⟨276354566656,129791804⟩ (N E ⟨276354566784,129540865⟩ E)) ⟨276354566912,129290532⟩ (N (N E ⟨276354567040,129040803⟩ E) ⟨276354567168,128791678⟩ (N E ⟨276354567296,128543153⟩ E)))) ⟨276354567424,128295227⟩ (N (N (N (N E ⟨276354567552,128047899⟩ E) ⟨276354567680,127801167⟩ (N E ⟨276354567808,127555029⟩ E)) ⟨276354567936,127309483⟩ (N (N E ⟨276354568064,127064528⟩ E) ⟨276354568192,126820162⟩ (N E ⟨276354568320,126576383⟩ E))) ⟨276354568448,126333190⟩ (N (N (N E ⟨276354568576,126090580⟩ E) ⟨276354568704,125848553⟩ (N E ⟨276354568832,125607106⟩ E)) ⟨276354568960,125366238⟩ (N (N E ⟨276354569088,125125948⟩ E) ⟨276354569216,124886232⟩ (N E ⟨276354569344,124647091⟩ E))))))))

noncomputable def tab28 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨276354569600,124170523⟩ E) ⟨276354569728,123933094⟩ E) ⟨276354569984,123459935⟩ (N E ⟨276354570112,123224202⟩ E)) ⟨276354570240,122989032⟩ (N (N E ⟨276354570368,122754423⟩ E) ⟨276354570496,122520373⟩ (N E ⟨276354570624,122286881⟩ E))) ⟨276354570752,122053944⟩ (N (N (N E ⟨276354570880,121821562⟩ E) ⟨276354571008,121589733⟩ (N E ⟨276354571136,121358456⟩ E)) ⟨276354571392,120897548⟩ (N (N E ⟨276354571520,120667914⟩ E) ⟨276354571648,120438826⟩ (N E ⟨276354571904,119982279⟩ E)))) ⟨276354572032,119754816⟩ (N (N (N (N E ⟨276354572160,119527892⟩ E) ⟨276354572288,119301506⟩ (N E ⟨276488784512,159775768⟩ E)) ⟨276488784640,159467007⟩ (N (N E ⟨276488784768,159158992⟩ E) ⟨276488784896,158851720⟩ (N E ⟨276488785024,158545189⟩ E))) ⟨276488785152,158239398⟩ (N (N (N E ⟨276488785280,157934343⟩ E) ⟨276488785408,157630024⟩ (N E ⟨276488785536,157326437⟩ E)) ⟨276488785664,157023580⟩ (N (N E ⟨276488785792,156721453⟩ E) ⟨276488785920,156420051⟩ (N E ⟨276488786048,156119374⟩ E))))) ⟨276488786176,155819420⟩ (N (N (N (N (N E ⟨276488786304,155520185⟩ E) ⟨276488786432,155221668⟩ (N E ⟨276488786560,154923868⟩ E)) ⟨276488786688,154626781⟩ (N (N E ⟨276488786816,154330407⟩ E) ⟨276488786944,154034742⟩ (N E ⟨276488787072,153739785⟩ E))) ⟨276488787200,153445533⟩ (N (N (N E ⟨276488787328,153151986⟩ E) ⟨276488787456,152859140⟩ (N E ⟨276488787584,152566994⟩ E)) ⟨276488787712,152275546⟩ (N (N E ⟨276488787840,151984793⟩ E) ⟨276488787968,151694734⟩ (N E ⟨276488788096,151405367⟩ E)))) ⟨276488788224,151116690⟩ (N (N (N (N E ⟨276488788352,150828700⟩ E) ⟨276488788480,150541396⟩ (N E ⟨276488788608,150254776⟩ E)) ⟨276488788736,149968838⟩ (N (N E ⟨276488788864,149683580⟩ E) ⟨276488788992,149399000⟩ (N E ⟨276488789120,149115096⟩ E))) ⟨276488789248,148831866⟩ (N (N (N E ⟨276488789376,148549309⟩ E) ⟨276488789632,147986203⟩ (N E ⟨276488789888,147425763⟩ E)) ⟨276488790016,147146538⟩ (N (N E ⟨276623002368,192786483⟩ E) ⟨276623002496,192414110⟩ (N E ⟨276623002624,192042636⟩ E)))))) ⟨276623002752,191672058⟩ (N (N (N (N (N (N E ⟨276623002880,191302374⟩ E) ⟨276623003008,190933581⟩ (N E ⟨276623003136,190565676⟩ E)) ⟨276623003264,190198656⟩ (N (N E ⟨276623003392,189832521⟩ E) ⟨276623003520,189467265⟩ (N E ⟨276623003648,189102888⟩ E))) ⟨276623003776,188739387⟩ (N (N (N E ⟨276623003904,188376759⟩ E) ⟨276623004032,188015001⟩ (N E ⟨276623004160,187654112⟩ E)) ⟨276623004288,187294088⟩ (N (N E ⟨276623004416,186934928⟩ E) ⟨276623004544,186576628⟩ (N E ⟨276623004672,186219186⟩ E)))) ⟨276623004800,185862599⟩ (N (N (N (N E ⟨276623004928,185506867⟩ E) ⟨276623005056,185151984⟩ (N E ⟨276623005184,184797951⟩ E)) ⟨276623005312,184444763⟩ (N (N E ⟨276623005440,184092418⟩ E) ⟨276623005568,183740915⟩ (N E ⟨276623005696,183390250⟩ E))) ⟨276623005824,183040422⟩ (N (N (N E ⟨276623005952,182691428⟩ E) ⟨276623006080,182343265⟩ (N E ⟨276623006208,181995931⟩ E)) ⟨276623006336,181649424⟩ (N (N E ⟨276623006464,181303741⟩ E) ⟨276623006720,180614839⟩ (N E ⟨276623006848,180271616⟩ E))))) ⟨276623006976,179929207⟩ (N (N (N (N (N E ⟨276623007104,179587611⟩ E) ⟨276623007232,179246826⟩ (N E ⟨276623007360,178906848⟩ E)) ⟨276623007488,178567676⟩ (N (N E ⟨276623007616,178229308⟩ E) ⟨276623007744,177891741⟩ (N E ⟨276757220224,228795158⟩ E))) ⟨276757220352,228353446⟩ (N (N (N E ⟨276757220480,227912801⟩ E) ⟨276757220608,227473218⟩ (N E ⟨276757220736,227034694⟩ E)) ⟨276757220864,226597227⟩ (N (N E ⟨276757220992,226160813⟩ E) ⟨276757221120,225725449⟩ (N E ⟨276757221248,225291133⟩ E)))) ⟨276757221376,224857860⟩ (N (N (N (N E ⟨276757221504,224425629⟩ E) ⟨276757221632,223994437⟩ (N E ⟨276757221760,223564279⟩ E)) ⟨276757221888,223135154⟩ (N (N E ⟨276757222144,222279988⟩ E) ⟨276757222272,221853942⟩ (N E ⟨276757222400,221428916⟩ E))) ⟨276757222528,221004908⟩ (N (N (N E ⟨276757222656,220581914⟩ E) ⟨276757222784,220159932⟩ (N E ⟨276757222912,219738959⟩ E)) ⟨276757223040,219318991⟩ (N (N E ⟨276757223168,218900027⟩ E) ⟨276757223296,218482062⟩ (N E ⟨276757223424,218065095⟩ E))))))) ⟨276757223552,217649122⟩ (N (N (N (N (N (N (N E ⟨276757223680,217234141⟩ E) ⟨276757223808,216820149⟩ (N E ⟨276757223936,216407142⟩ E)) ⟨276757224064,215995118⟩ (N (N E ⟨276757224192,215584075⟩ E) ⟨276757224448,214764918⟩ (N E ⟨276757224576,214356799⟩ E))) ⟨276757224704,213949648⟩ (N (N (N E ⟨276757224832,213543465⟩ E) ⟨276757224960,213138244⟩ (N E ⟨276757225088,212733985⟩ E)) ⟨276757225216,212330684⟩ (N (N E ⟨276757225472,211526945⟩ E) ⟨276891438080,267771255⟩ (N E ⟨276891438208,267254546⟩ E)))) ⟨276891438336,266739083⟩ (N (N (N (N E ⟨276891438464,266224862⟩ E) ⟨276891438592,265711881⟩ (N E ⟨276891438720,265200134⟩ E)) ⟨276891438848,264689619⟩ (N (N E ⟨276891438976,264180332⟩ E) ⟨276891439104,263672269⟩ (N E ⟨276891439232,263165428⟩ E))) ⟨276891439360,262659804⟩ (N (N (N E ⟨276891439488,262155393⟩ E) ⟨276891439616,261652194⟩ (N E ⟨276891439744,261150201⟩ E)) ⟨276891439872,260649411⟩ (N (N E ⟨276891440000,260149822⟩ E) ⟨276891440128,259651429⟩ (N E ⟨276891440256,259154230⟩ E))))) ⟨276891440384,258658220⟩ (N (N (N (N (N E ⟨276891440512,258163396⟩ E) ⟨276891440640,257669755⟩ (N E ⟨276891440768,257177294⟩ E)) ⟨276891440896,256686009⟩ (N (N E ⟨276891441024,256195897⟩ E) ⟨276891441152,255706954⟩ (N E ⟨276891441280,255219177⟩ E))) ⟨276891441408,254732562⟩ (N (N (N E ⟨276891441536,254247107⟩ E) ⟨276891441664,253762809⟩ (N E ⟨276891441792,253279663⟩ E)) ⟨276891441920,252797666⟩ (N (N E ⟨276891442048,252316816⟩ E) ⟨276891442176,251837108⟩ (N E ⟨276891442432,250881109⟩ E)))) ⟨276891442560,250404811⟩ (N (N (N (N E ⟨276891442688,249929642⟩ E) ⟨276891442816,249455601⟩ (N E ⟨276891442944,248982683⟩ E)) ⟨276891443072,248510885⟩ (N (N E ⟨276891443200,248040204⟩ E) ⟨277025655936,309682517⟩ (N E ⟨277025656064,309085222⟩ E))) ⟨277025656192,308489366⟩ (N (N (N E ⟨277025656320,307894946⟩ E) ⟨277025656448,307301957⟩ (N E ⟨277025656576,306710395⟩ E)) ⟨277025656704,306120256⟩ (N (N E ⟨277025656832,305531536⟩ E) ⟨277025656960,304944231⟩ (N E ⟨277025657088,304358336⟩ E)))))) ⟨277025657216,303773849⟩ (N (N (N (N (N (N E ⟨277025657344,303190763⟩ E) ⟨277025657472,302609077⟩ (N E ⟨277025657600,302028785⟩ E)) ⟨277025657728,301449883⟩ (N (N E ⟨277025657856,300872368⟩ E) ⟨277025657984,300296236⟩ (N E ⟨277025658112,299721482⟩ E))) ⟨277025658240,299148102⟩ (N (N (N E ⟨277025658368,298576094⟩ E) ⟨277025658496,298005452⟩ (N E ⟨277025658624,297436173⟩ E)) ⟨277025658752,296868253⟩ (N (N E ⟨277025658880,296301687⟩ E) ⟨277025659008,295736473⟩ (N E ⟨277025659136,295172607⟩ E)))) ⟨277025659264,294610084⟩ (N (N (N (N E ⟨277025659392,294048900⟩ E) ⟨277025659520,293489052⟩ (N E ⟨277025659776,292373348⟩ E)) ⟨277025660160,290709716⟩ (N (N E ⟨277025660288,290157803⟩ E) ⟨277025660544,289057902⟩ (N E ⟨277025660672,288509905⟩ E))) ⟨277025660800,287963208⟩ (N (N (N E ⟨277025660928,287417804⟩ E) ⟨277159873920,353811590⟩ (N E ⟨277159874048,353129840⟩ E)) ⟨277159874176,352449731⟩ (N (N E ⟨277159874304,351771259⟩ E) ⟨277159874432,351094419⟩ (N E ⟨277159874560,350419206⟩ E))))) ⟨277159874688,349745616⟩ (N (N (N (N (N E ⟨277159874816,349073644⟩ E) ⟨277159874944,348403285⟩ (N E ⟨277159875072,347734535⟩ E)) ⟨277159875200,347067389⟩ (N (N E ⟨277159875328,346401842⟩ E) ⟨277159875456,345737890⟩ (N E ⟨277159875584,345075528⟩ E))) ⟨277159875712,344414752⟩ (N (N (N E ⟨277159875840,343755558⟩ E) ⟨277159875968,343097939⟩ (N E ⟨277159876096,342441893⟩ E)) ⟨277159876224,341787414⟩ (N (N E ⟨277159876352,341134499⟩ E) ⟨277159876480,340483142⟩ (N E ⟨277159876608,339833339⟩ E)))) ⟨277159876736,339185085⟩ (N (N (N (N E ⟨277159876864,338538377⟩ E) ⟨277159876992,337893210⟩ (N E ⟨277159877120,337249579⟩ E)) ⟨277159877248,336607480⟩ (N (N E ⟨277159877376,335966909⟩ E) ⟨277159877504,335327861⟩ (N E ⟨277159877632,334690332⟩ E))) ⟨277159877760,334054318⟩ (N (N (N E ⟨277159877888,333419814⟩ E) ⟨277159878656,329644265⟩ (N E ⟨277294091776,401398096⟩ E)) ⟨277294091904,400625025⟩ (N (N E ⟨277294092032,399853815⟩ E) ⟨277294092160,399084459⟩ (N E ⟨277294092288,398316954⟩ E))))))))

noncomputable def tab29 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨277294092544,396787471⟩ E) ⟨277294092672,396025483⟩ E) ⟨277294092800,395265323⟩ (N E ⟨277294092928,394506987⟩ E)) ⟨277294093056,393750469⟩ (N (N E ⟨277294093184,392995763⟩ E) ⟨277294093312,392242865⟩ (N E ⟨277294093440,391491770⟩ E))) ⟨277294093568,390742472⟩ (N (N (N E ⟨277294093696,389994965⟩ E) ⟨277294093824,389249246⟩ (N E ⟨277294093952,388505309⟩ E)) ⟨277294094080,387763148⟩ (N (N E ⟨277294094208,387022759⟩ E) ⟨277294094336,386284136⟩ (N E ⟨277294094464,385547275⟩ E)))) ⟨277294094592,384812171⟩ (N (N (N (N E ⟨277294094720,384078817⟩ E) ⟨277294094848,383347211⟩ (N E ⟨277294094976,382617345⟩ E)) ⟨277294095104,381889216⟩ (N (N E ⟨277294095232,381162819⟩ E) ⟨277294095360,380438148⟩ (N E ⟨277294095488,379715198⟩ E))) ⟨277294095744,378274445⟩ (N (N (N E ⟨277294095872,377556631⟩ E) ⟨277294096000,376840520⟩ (N E ⟨277294096256,375413383⟩ E)) ⟨277294096384,374702349⟩ (N (N E ⟨277428309632,451807537⟩ E) ⟨277428309760,450937799⟩ (N E ⟨277428309888,450070153⟩ E))))) ⟨277428310016,449204594⟩ (N (N (N (N (N E ⟨277428310144,448341115⟩ E) ⟨277428310272,447479709⟩ (N E ⟨277428310400,446620372⟩ E)) ⟨277428310528,445763097⟩ (N (N E ⟨277428310656,444907878⟩ E) ⟨277428310784,444054710⟩ (N E ⟨277428310912,443203586⟩ E))) ⟨277428311040,442354500⟩ (N (N (N E ⟨277428311168,441507447⟩ E) ⟨277428311296,440662421⟩ (N E ⟨277428311424,439819416⟩ E)) ⟨277428311552,438978426⟩ (N (N E ⟨277428311680,438139446⟩ E) ⟨277428311808,437302469⟩ (N E ⟨277428311936,436467490⟩ E)))) ⟨277428312064,435634504⟩ (N (N (N (N E ⟨277428312192,434803504⟩ E) ⟨277428312320,433974485⟩ (N E ⟨277428312448,433147441⟩ E)) ⟨277428312704,431499256⟩ (N (N E ⟨277428312832,430678103⟩ E) ⟨277428312960,429858904⟩ (N E ⟨277428313216,428226340⟩ E))) ⟨277428313344,427412966⟩ (N (N (N E ⟨277428313472,426601521⟩ E) ⟨277428313856,424178717⟩ (N E ⟨277428313984,423374940⟩ E)) ⟨277428314112,422573066⟩ (N (N E ⟨277562527488,505001086⟩ E) ⟨277562527616,504029418⟩ (N E ⟨277562527744,503060086⟩ E)))))) ⟨277562527872,502093084⟩ (N (N (N (N (N (N E ⟨277562528000,501128404⟩ E) ⟨277562528128,500166040⟩ (N E ⟨277562528256,499205985⟩ E)) ⟨277562528384,498248234⟩ (N (N E ⟨277562528512,497292778⟩ E) ⟨277562528640,496339612⟩ (N E ⟨277562528768,495388729⟩ E))) ⟨277562528896,494440122⟩ (N (N (N E ⟨277562529024,493493786⟩ E) ⟨277562529152,492549712⟩ (N E ⟨277562529280,491607895⟩ E)) ⟨277562529408,490668329⟩ (N (N E ⟨277562529536,489731006⟩ E) ⟨277562529664,488795921⟩ (N E ⟨277562529792,487863067⟩ E)))) ⟨277562529920,486932438⟩ (N (N (N (N E ⟨277562530048,486004027⟩ E) ⟨277562530176,485077828⟩ (N E ⟨277562530304,484153835⟩ E)) ⟨277562530432,483232041⟩ (N (N E ⟨277562530560,482312440⟩ E) ⟨277562530688,481395026⟩ (N E ⟨277562530816,480479793⟩ E))) ⟨277562530944,479566733⟩ (N (N (N E ⟨277562531072,478655842⟩ E) ⟨277562531200,477747113⟩ (N E ⟨277562531328,476840540⟩ E)) ⟨277562531456,475936117⟩ (N (N E ⟨277562531584,475033837⟩ E) ⟨277562531712,474133694⟩ (N E ⟨277562531840,473235683⟩ E))))) ⟨277696745984,555570288⟩ (N (N (N (N (N E ⟨277696746112,554504399⟩ E) ⟨277696746240,553441065⟩ (N E ⟨277696746368,552380279⟩ E)) ⟨277696746496,551322034⟩ (N (N E ⟨277696746624,550266322⟩ E) ⟨277696746752,549213136⟩ (N E ⟨277696746880,548162469⟩ E))) ⟨277696747008,547114314⟩ (N (N (N E ⟨277696747136,546068663⟩ E) ⟨277696747264,545025509⟩ (N E ⟨277696747392,543984846⟩ E)) ⟨277696747520,542946665⟩ (N (N E ⟨277696747648,541910961⟩ E) ⟨277696747776,540877725⟩ (N E ⟨277696748160,537792759⟩ E)))) ⟨277696748288,536769328⟩ (N (N (N (N E ⟨277696748416,535748331⟩ E) ⟨277696748544,534729760⟩ (N E ⟨277696748672,533713609⟩ E)) ⟨277696748800,532699872⟩ (N (N E ⟨277696749056,530679608⟩ E) ⟨277696749184,529673068⟩ (N E ⟨277696749440,527667137⟩ E))) ⟨277696749568,526667734⟩ (N (N (N E ⟨277830963328,618386286⟩ E) ⟨277830963840,613650904⟩ (N E ⟨277830963968,612474149⟩ E)) ⟨277830964096,611300214⟩ (N (N E ⟨277830964224,610129090⟩ E) ⟨277830964352,608960770⟩ (N E ⟨277830964480,607795246⟩ E))))))) ⟨277830964608,606632509⟩ (N (N (N (N (N (N (N E ⟨277830964736,605472552⟩ E) ⟨277830964864,604315366⟩ (N E ⟨277830964992,603160944⟩ E)) ⟨277830965120,602009277⟩ (N (N E ⟨277830965248,600860359⟩ E) ⟨277830965504,598570733⟩ (N E ⟨277830965632,597430011⟩ E))) ⟨277830965760,596292006⟩ (N (N (N E ⟨277830965888,595156709⟩ E) ⟨277830966016,594024113⟩ (N E ⟨277830966144,592894210⟩ E)) ⟨277830966400,590642454⟩ (N (N E ⟨277830966656,588401380⟩ E) ⟨277830966784,587284829⟩ (N E ⟨277830967040,585059662⟩ E)))) ⟨277830967296,582845026⟩ (N (N (N (N E ⟨277965181824,673072249⟩ E) ⟨277965182080,670496404⟩ (N E ⟨277965182208,669213103⟩ E)) ⟨277965182336,667932871⟩ (N (N E ⟨277965182592,665381580⟩ E) ⟨277965182720,664110503⟩ (N E ⟨277965182976,661577444⟩ E))) ⟨277965183360,657800459⟩ (N (N (N E ⟨277965183488,656547457⟩ E) ⟨277965183872,652806314⟩ (N E ⟨277965184000,651565191⟩ E)) ⟨277965184256,649091784⟩ (N (N E ⟨277965184384,647859482⟩ E) ⟨277965184768,644180083⟩ (N E ⟨277965184896,642959425⟩ E))))) ⟨277965185024,641741658⟩ (N (N (N (N (N E ⟨278099399936,733437922⟩ E) ⟨278099400064,732034826⟩ (N E ⟨278099400192,730635084⟩ E)) ⟨278099400320,729238686⟩ (N (N E ⟨278099400576,726455886⟩ E) ⟨278099400960,722306530⟩ (N E ⟨278099401088,720930000⟩ E))) ⟨278099401216,719556747⟩ (N (N (N E ⟨278099401344,718186763⟩ E) ⟨278099401472,716820038⟩ (N E ⟨278099401728,714096329⟩ E)) ⟨278099401856,712739327⟩ (N (N E ⟨278099402112,710034980⟩ E) ⟨278099402240,708687618⟩ (N E ⟨278099402624,704664662⟩ E)))) ⟨278099402752,703330025⟩ (N (N (N (N E ⟨278233618304,792819299⟩ E) ⟨278233618432,791306225⟩ (N E ⟨278233618688,788290891⟩ E)) ⟨278233618816,786788611⟩ (N (N E ⟨278233618944,785289908⟩ E) ⟨278233619200,782303195⟩ (N E ⟨278233619328,780815163⟩ E))) ⟨278233619584,777849702⟩ (N (N (N E ⟨278233620096,771960898⟩ E) ⟨278233620224,770497415⟩ (N E ⟨278233620352,769037398⟩ E)) ⟨278233620480,767580838⟩ (N (N E ⟨278367836160,860255808⟩ E) ⟨278367836544,855344556⟩ (N E ⟨278367836672,853715266⟩ E)))))) ⟨278367836928,850468309⟩ (N (N (N (N (N (N E ⟨278367837312,845626765⟩ E) ⟨278367837440,844020579⟩ (N E ⟨278367837696,840819631⟩ E)) ⟨278367837824,839224848⟩ (N (N E ⟨278367837952,837633845⟩ E) ⟨278367838208,834463136⟩ (N E ⟨278502055808,905659624⟩ E))) ⟨278502055936,903944301⟩ (N (N (N E ⟨278636272896,987168484⟩ E) ⟨278636273024,985294343⟩ (N E ⟨278636273408,979698546⟩ E)) ⟨278636273664,975990077⟩ (N (N E ⟨278770490624,1062597123⟩ E) ⟨278770491392,1050564584⟩ (N E ⟨278904709120,1127630341⟩ E)))) ⟨279038926848,1207148283⟩ (N (N (N (N E ⟨279173144576,1289077782⟩ E) ⟨279307362304,1373376670⟩ (N E ⟨279441580032,1460001260⟩ E)) ⟨279575797760,1548906371⟩ (N (N E ⟨279710015488,1640045351⟩ E) ⟨279978450944,1828831124⟩ (N E ⟨280112668672,1926377499⟩ E))) ⟨280246886400,2025956968⟩ (N (N (N E ⟨280515321856,2230999488⟩ E) ⟨280783757312,2443514451⟩ (N E ⟨281052192768,2663037788⟩ E)) ⟨281186410496,2775277410⟩ (N (N E ⟨281320628224,2889086649⟩ E) ⟨281857499136,3358742308⟩ (N E ⟨283468112000,4859954717⟩ E))))) ⟨283468112128,4850758660⟩ (N (N (N (N (N E ⟨283468112256,4841584346⟩ E) ⟨283468112384,4832431715⟩ (N E ⟨283468112512,4823300705⟩ E)) ⟨283468112640,4814191254⟩ (N (N E ⟨283468112768,4805103302⟩ E) ⟨283468112896,4796036788⟩ (N E ⟨283468113024,4786991651⟩ E))) ⟨283468113152,4777967830⟩ (N (N (N E ⟨283468113280,4768965266⟩ E) ⟨283468113408,4759983897⟩ (N E ⟨283468113536,4751023666⟩ E)) ⟨283468113664,4742084510⟩ (N (N E ⟨283468113792,4733166372⟩ E) ⟨283468113920,4724269192⟩ (N E ⟨283468114048,4715392911⟩ E)))) ⟨283468114176,4706537470⟩ (N (N (N (N E ⟨283468114304,4697702810⟩ E) ⟨283468114432,4688888873⟩ (N E ⟨283468114560,4680095600⟩ E)) ⟨283468114688,4671322934⟩ (N (N E ⟨283468114816,4662570816⟩ E) ⟨283468114944,4653839189⟩ (N E ⟨283468115072,4645127994⟩ E))) ⟨283468115200,4636437176⟩ (N (N (N E ⟨283468115328,4627766676⟩ E) ⟨283468115456,4619116438⟩ (N E ⟨283468115584,4610486405⟩ E)) ⟨283468115712,4601876519⟩ (N (N E ⟨283468115840,4593286726⟩ E) ⟨283468115968,4584716968⟩ (N E ⟨283468116096,4576167189⟩ E))))))))

noncomputable def tab30 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨283468116352,4559127347⟩ E) ⟨283468116480,4550637173⟩ E) ⟨283468116608,4542166755⟩ (N E ⟨283468116736,4533716039⟩ E)) ⟨283468116864,4525284970⟩ (N (N E ⟨283468116992,4516873494⟩ E) ⟨283468117120,4508481554⟩ (N E ⟨283468117248,4500109098⟩ E))) ⟨283468117376,4491756071⟩ (N (N (N E ⟨283468117504,4483422418⟩ E) ⟨283468117632,4475108086⟩ (N E ⟨283468117760,4466813021⟩ E)) ⟨283468117888,4458537170⟩ (N (N E ⟨283468118016,4450280479⟩ E) ⟨283468118144,4442042895⟩ (N E ⟨283468118272,4433824364⟩ E)))) ⟨283468118400,4425624835⟩ (N (N (N (N E ⟨283468118656,4409282568⟩ E) ⟨283468118912,4393015675⟩ (N E ⟨283468119040,4384910364⟩ E)) ⟨283468119168,4376823740⟩ (N (N E ⟨283468119296,4368755751⟩ E) ⟨283468119424,4360706347⟩ (N E ⟨283468119552,4352675475⟩ E))) ⟨283468119680,4344663085⟩ (N (N (N E ⟨283468119808,4336669126⟩ E) ⟨283468119936,4328693546⟩ (N E ⟨283468120064,4320736295⟩ E)) ⟨286689345536,7030445542⟩ (N (N E ⟨292058054784,9597161408⟩ E) ⟨292058054912,9575208023⟩ (N E ⟨292058055040,9550434133⟩ E))))) ⟨292058055296,9492506443⟩ (N (N (N (N (N E ⟨292058055424,9459397479⟩ E) ⟨292058055552,9423557641⟩ (N E ⟨292058055680,9385013290⟩ E)) ⟨292058055808,9343792325⟩ (N (N E ⟨292058055936,9299924162⟩ E) ⟨292058056064,9253439712⟩ (N E ⟨292058056192,9204371355⟩ E))) ⟨292058056320,9152752914⟩ (N (N (N E ⟨292058056704,8982956468⟩ E) ⟨292058056960,8857691173⟩ (N E ⟨292058057088,8791560142⟩ E)) ⟨292058057216,8723154014⟩ (N (N E ⟨292058057344,8652517190⟩ E) ⟨292058057472,8579695262⟩ (N E ⟨292058057600,8504734976⟩ E)))) ⟨292058057728,8427684207⟩ (N (N (N (N E ⟨292058057856,8348591922⟩ E) ⟨292058058240,8099571304⟩ (N E ⟨292058058368,8012823281⟩ E)) ⟨292058058496,7924293774⟩ (N (N E ⟨292058058752,7742110373⟩ E) ⟨292058058880,7648568596⟩ (N E ⟨292058059008,7553469500⟩ E))) ⟨292058059136,7456871066⟩ (N (N (N E ⟨292058059648,7056667314⟩ E) ⟨292058059776,6953465123⟩ (N E ⟨292058059904,6849124881⟩ E)) ⟨292058060416,6421631471⟩ (N (N E ⟨292058060544,6312540405⟩ E) ⟨292058060672,6202689544⟩ (N E ⟨292058060800,6092142989⟩ E)))))) ⟨292058060928,5980965038⟩ (N (N (N (N (N (N E ⟨292058061056,5869220150⟩ E) ⟨292058061184,5756972900⟩ (N E ⟨292058061312,5644287947⟩ E)) ⟨292058061440,5531229986⟩ (N (N E ⟨292058061568,5417863720⟩ E) ⟨292058061696,5304253811⟩ (N E ⟨292058061824,5190464847⟩ E))) ⟨292058061952,5076561304⟩ (N (N (N E ⟨292058062080,4962607504⟩ E) ⟨292058062208,4848667580⟩ (N E ⟨292058062336,4734805438⟩ E)) ⟨292058062720,4394320554⟩ (N (N E ⟨292058062848,4281402733⟩ E) ⟨299976908800,4705074877⟩ (N E ⟨300245344256,4718558612⟩ E)))) ⟨300647997568,4616538007⟩ (N (N (N (N E ⟨300647997824,4373868268⟩ E) ⟨300647997952,4253388679⟩ (N E ⟨300647998080,4133565213⟩ E)) ⟨300647998208,4014461555⟩ (N (N E ⟨300647998464,3778665077⟩ E) ⟨300647998592,3662096204⟩ (N E ⟨300647998720,3546494959⟩ E))) ⟨300647998976,3318434746⟩ (N (N (N E ⟨300647999232,3094954757⟩ E) ⟨300647999360,2985075450⟩ (N E ⟨300647999488,2876511055⟩ E)) ⟨300648000000,2456479654⟩ (N (N E ⟨300648000128,2355288468⟩ E) ⟨300648001024,1695116200⟩ (N E ⟨300648001152,1608221062⟩ E))))) ⟨300648001664,1280795340⟩ (N (N (N (N (N E ⟨300648001792,1204158305⟩ E) ⟨300648002304,919468625⟩ (N E ⟨300648002560,790642281⟩ E)) ⟨300648003072,561020055⟩ (N (N E ⟨300648003328,460550930⟩ E) ⟨300648003584,369821196⟩ (N E ⟨300648003840,288934345⟩ E))) ⟨300648004096,217969726⟩ (N (N (N E ⟨300648004608,106003817⟩ E) ⟨300648004736,84270785⟩ (N E ⟨300648004864,65040651⟩ E)) ⟨300648004992,48310569⟩ (N (N E ⟨300648005120,34076216⟩ E) ⟨300648005248,22331797⟩ (N E ⟨300648005632,1958320⟩ E)))) ⟨300916441088,2054410⟩ (N (N (N (N E ⟨303869230976,8205722⟩ E) ⟨304003448832,3085937⟩ (N E ⟨309237940352,707682⟩ E)) ⟨309506378240,84764⟩ (N (N E ⟨309506378496,84473⟩ E) ⟨309506379008,83894⟩ (N E ⟨309506379392,83463⟩ E))) ⟨309506379520,83320⟩ (N (N (N E ⟨309506379648,83177⟩ E) ⟨309506379776,83035⟩ (N E ⟨309506379904,82893⟩ E)) ⟨309506380160,82610⟩ (N (N E ⟨309506380288,82468⟩ E) ⟨309506380416,82327⟩ (N E ⟨309506380544,82187⟩ E))))))) ⟨309506381056,81627⟩ (N (N (N (N (N (N (N E ⟨309506381312,81349⟩ E) ⟨309506381440,81211⟩ (N E ⟨309506381696,80935⟩ E)) ⟨309506381952,80660⟩ (N (N E ⟨309506382080,80523⟩ E) ⟨309506382336,80249⟩ (N E ⟨309506382464,80113⟩ E))) ⟨309506382592,79977⟩ (N (N (N E ⟨309506383744,78767⟩ E) ⟨309506383872,78634⟩ (N E ⟨309640596992,1963017⟩ E)) ⟨309640597120,1959651⟩ (N (N E ⟨309640597504,1949598⟩ E) ⟨309640597632,1946261⟩ (N E ⟨309640597760,1942931⟩ E)))) ⟨309640597888,1939609⟩ (N (N (N (N E ⟨309640598016,1936293⟩ E) ⟨309640598528,1923102⟩ (N E ⟨309640598784,1916549⟩ E)) ⟨309640599168,1906771⟩ (N (N E ⟨309640599296,1903525⟩ E) ⟨309640599808,1890612⟩ (N E ⟨309640599936,1887401⟩ E))) ⟨309640600064,1884197⟩ (N (N (N E ⟨309640600192,1880999⟩ E) ⟨309640601216,1855662⟩ (N E ⟨309640601472,1849394⟩ E)) ⟨309640601600,1846271⟩ (N (N E ⟨309774813952,6384466⟩ E) ⟨309774814208,6362541⟩ (N E ⟨309774814336,6351614⟩ E))))) ⟨309774814464,6340710⟩ (N (N (N (N (N E ⟨309774814720,6318973⟩ E) ⟨309774814848,6308139⟩ (N E ⟨309774814976,6297328⟩ E)) ⟨309774815744,6232949⟩ (N (N E ⟨309774815872,6222300⟩ E) ⟨309774816000,6211673⟩ (N E ⟨309774817152,6117044⟩ E))) ⟨309774817536,6085902⟩ (N (N (N E ⟨309774817664,6075565⟩ E) ⟨309774817792,6065251⟩ (N E ⟨309774817920,6054958⟩ E)) ⟨309774818432,6014005⟩ (N (N E ⟨309774818816,5983517⟩ E) ⟨309774818944,5973397⟩ (N E ⟨309774819200,5953222⟩ E)))) ⟨309774819328,5943166⟩ (N (N (N (N E ⟨309909032832,13087753⟩ E) ⟨309909032960,13065343⟩ (N E ⟨309909033088,13042981⟩ E)) ⟨309909033344,12998401⟩ (N (N E ⟨309909033472,12976182⟩ E) ⟨309909034112,12865798⟩ (N E ⟨309909034496,12800131⟩ E))) ⟨309909034624,12778335⟩ (N (N (N E ⟨309909035264,12670048⟩ E) ⟨309909035520,12627055⟩ (N E ⟨309909035648,12605627⟩ E)) ⟨309909035776,12584244⟩ (N (N E ⟨309909035904,12562907⟩ E) ⟨309909036032,12541615⟩ (N E ⟨309909036160,12520367⟩ E)))))) ⟨309909036288,12499165⟩ (N (N (N (N (N (N E ⟨309909037056,12372891⟩ E) ⟨310043249792,22590303⟩ (N E ⟨310043249920,22551523⟩ E)) ⟨310043250304,22435680⟩ (N (N E ⟨310043250560,22358864⟩ E) ⟨310043250816,22282377⟩ (N E ⟨310043250944,22244256⟩ E))) ⟨310043251072,22206217⟩ (N (N (N E ⟨310043251200,22168259⟩ E) ⟨310043251328,22130382⟩ (N E ⟨310043251712,22017236⟩ E)) ⟨310043251968,21942206⟩ (N (N E ⟨310043252096,21904812⟩ E) ⟨310043252608,21756027⟩ (N E ⟨310043252736,21719028⟩ E)))) ⟨310043252992,21645266⟩ (N (N (N (N E ⟨310043253120,21608503⟩ E) ⟨310043253248,21571818⟩ (N E ⟨310043253632,21462228⟩ E)) ⟨310043253760,21425853⟩ (N (N E ⟨310043254016,21353333⟩ E) ⟨310043254144,21317188⟩ (N E ⟨310043254272,21281120⟩ E))) ⟨310043254400,21245128⟩ (N (N (N E ⟨310043254656,21173372⟩ E) ⟨310043254784,21137608⟩ (N E ⟨310177468800,33867861⟩ E)) ⟨310177468928,33809969⟩ (N (N E ⟨310177469056,33752201⟩ E) ⟨310177469312,33637035⟩ (N E ⟨310177469696,33465204⟩ E))))) ⟨310177469824,33408172⟩ (N (N (N (N (N E ⟨310177470080,33294470⟩ E) ⟨310177470464,33124823⟩ (N E ⟨310177470592,33068515⟩ E)) ⟨310177470848,32956256⟩ (N (N E ⟨310177471360,32733164⟩ E) ⟨310177472128,32402054⟩ (N E ⟨310177472512,32238069⟩ E))) ⟨310311685632,48561711⟩ (N (N (N E ⟨310311686144,48229748⟩ E) ⟨310311686656,47900618⟩ (N E ⟨310311686784,47818774⟩ E)) ⟨310311687296,47493143⟩ (N (N E ⟨310311687424,47412168⟩ E) ⟨310311687552,47331367⟩ (N E ⟨310311688192,46929930⟩ E)))) ⟨310311688320,46850154⟩ (N (N (N (N E ⟨310311688448,46770548⟩ E) ⟨310311688576,46691111⟩ (N E ⟨310311688960,46453808⟩ E)) ⟨310311689088,46375043⟩ (N (N E ⟨310311689216,46296444⟩ E) ⟨310311689600,46061645⟩ (N E ⟨310311689728,45983710⟩ E))) ⟨310311689856,45905939⟩ (N (N (N E ⟨310311689984,45828333⟩ E) ⟨310311690112,45750891⟩ (N E ⟨310311690240,45673612⟩ E)) ⟨310445904384,64438024⟩ (N (N E ⟨310445904768,64108430⟩ E) ⟨310445904896,63999034⟩ (N E ⟨310445905408,63563776⟩ E))))))))

noncomputable def tab31 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨310445905920,63132212⟩ E) ⟨310445906048,63024894⟩ (N E ⟨310445906816,62385753⟩ E)) ⟨310445906944,62280019⟩ (N (N E ⟨310445907072,62174509⟩ E) ⟨310445907200,62069222⟩ (N E ⟨310445907456,61859315⟩ E))) ⟨310445907968,61442158⟩ (N (N (N E ⟨310580121344,84280135⟩ E) ⟨310580121472,84135763⟩ (N E ⟨310580121600,83991700⟩ E)) ⟨310580122240,83275992⟩ (N (N E ⟨310580122368,83133766⟩ E) ⟨310580122496,82991844⟩ (N E ⟨310580122880,82567892⟩ E)))) ⟨310580123008,82427176⟩ (N (N (N (N E ⟨310580123264,82146643⟩ E) ⟨310580124032,81312176⟩ (N E ⟨310580124288,81036377⟩ E)) ⟨310580124416,80898916⟩ (N (N E ⟨310580124672,80624867⟩ E) ⟨310580124800,80488278⟩ (N E ⟨310580125312,79944807⟩ E))) ⟨310580125440,79809656⟩ (N (N (N E ⟨310580125696,79540211⟩ E) ⟨310714340224,104300727⟩ (N E ⟨310714340352,104122746⟩ E)) ⟨310714340480,103945144⟩ (N (N E ⟨310714340608,103767921⟩ E) ⟨310714342144,101670421⟩ (N E ⟨310714342528,101154348⟩ E))))) ⟨310714342784,100812119⟩ (N (N (N (N (N E ⟨310714343424,99962856⟩ E) ⟨310848557312,129127856⟩ (N E ⟨310848557440,128907038⟩ E)) ⟨310848557952,128028472⟩ (N (N E ⟨310848558208,127591996⟩ E) ⟨310848558592,126940764⟩ (N E ⟨310848558976,126293683⟩ E))) ⟨310848559360,125650720⟩ (N (N (N E ⟨310848559488,125437309⟩ E) ⟨310848559744,125011844⟩ (N E ⟨310848560256,124166312⟩ E)) ⟨310848560640,123536852⟩ (N (N E ⟨310848560768,123327919⟩ E) ⟨310848561024,122911376⟩ (N E ⟨310848561152,122703764⟩ E)))) ⟨310982776576,152337207⟩ (N (N (N (N E ⟨310982776832,151819403⟩ E) ⟨310982777216,151046816⟩ (N E ⟨310982778368,148758359⟩ E)) ⟨310982778880,147755186⟩ (N (N E ⟨311116992768,184275650⟩ E) ⟨311116993152,183332294⟩ (N E ⟨311116994432,180231061⟩ E))) ⟨311116995584,177495837⟩ (N (N (N E ⟨311116995968,176595642⟩ E) ⟨311116996096,176296846⟩ (N E ⟨311116996224,175998681⟩ E)) ⟨311116996352,175701147⟩ (N (N E ⟨311116996480,175404242⟩ E) ⟨311116996608,175107963⟩ (N E ⟨311251213056,208249087⟩ E)))))) ⟨311251214336,204751524⟩ (N (N (N (N (N (N E ⟨311385430528,241535659⟩ E) ⟨311385430784,240716753⟩ (N E ⟨311385431552,238280772⟩ E)) ⟨311385432064,236673892⟩ (N (N E ⟨311519648384,275956647⟩ E) ⟨311519649152,273162871⟩ (N E ⟨311519649792,270861689⟩ E))) ⟨311653866752,310436369⟩ (N (N (N E ⟨311653867008,309386532⟩ E) ⟨311653867136,308863279⟩ (N E ⟨311653867520,307300140⟩ E)) ⟨311788084864,347732938⟩ (N (N E ⟨311788085248,345973083⟩ E) ⟨311922302976,386862971⟩ (N E ⟨312056520704,429950886⟩ E)))) ⟨312190738432,475216546⟩ (N (N (N (N E ⟨312324956160,522638312⟩ E) ⟨312459173888,572193205⟩ (N E ⟨312593391616,623856911⟩ E)) ⟨312727609344,677603799⟩ (N (N E ⟨312861827072,733406929⟩ E) ⟨312996044800,791238073⟩ (N E ⟨313130262528,851067722⟩ E))) ⟨313264480256,912865110⟩ (N (N (N E ⟨313398697984,976598221⟩ E) ⟨313532915712,1042233817⟩ (N E ⟨313667133440,1109737447⟩ E)) ⟨313801351168,1179073469⟩ (N (N E ⟨314069786624,1323094300⟩ E) ⟨314204004352,1397702054⟩ (N E ⟨314472439808,1551911270⟩ E))))) ⟨317827883136,3885544523⟩ (N (N (N (N (N E ⟨317827883264,3878986917⟩ E) ⟨317827883392,3872443141⟩ (N E ⟨317827883520,3865913159⟩ E)) ⟨317827883648,3859396938⟩ (N (N E ⟨317827883776,3852894441⟩ E) ⟨317827883904,3846405636⟩ (N E ⟨317827884032,3839930486⟩ E))) ⟨317827884160,3833468957⟩ (N (N (N E ⟨317827884288,3827021016⟩ E) ⟨317827884416,3820586627⟩ (N E ⟨317827884544,3814165757⟩ E)) ⟨317827884672,3807758371⟩ (N (N E ⟨317827884800,3801364436⟩ E) ⟨317827884928,3794983918⟩ (N E ⟨317827885056,3788616783⟩ E)))) ⟨317827885312,3775922526⟩ (N (N (N (N E ⟨317827885440,3769595338⟩ E) ⟨317827885568,3763281398⟩ (N E ⟨317827885696,3756980674⟩ E)) ⟨317827885824,3750693133⟩ (N (N E ⟨317827885952,3744418741⟩ E) ⟨317827886080,3738157464⟩ (N E ⟨317827886208,3731909272⟩ E))) ⟨317827886336,3725674130⟩ (N (N (N E ⟨317827886464,3719452006⟩ E) ⟨317827886592,3713242867⟩ (N E ⟨317827886720,3707046681⟩ E)) ⟨317827886848,3700863415⟩ (N (N E ⟨317827886976,3694693037⟩ E) ⟨317827887104,3688535515⟩ (N E ⟨317827887232,3682390817⟩ E))))))) ⟨317827887360,3676258910⟩ (N (N (N (N (N (N (N E ⟨317827887488,3670139764⟩ E) ⟨317827887744,3657939622⟩ (N E ⟨317827887872,3651858563⟩ E)) ⟨317827888000,3645790137⟩ (N (N E ⟨317827888128,3639734313⟩ E) ⟨317827888384,3627660343⟩ (N E ⟨317827888512,3621642135⟩ E))) ⟨317827888640,3615636403⟩ (N (N (N E ⟨317827888768,3609643116⟩ E) ⟨317827888896,3603662244⟩ (N E ⟨317827889024,3597693755⟩ E)) ⟨317827889280,3585793805⟩ (N (N E ⟨317827889408,3579862283⟩ E) ⟨317827889536,3573943022⟩ (N E ⟨317827889664,3568035991⟩ E)))) ⟨317827889920,3556258500⟩ (N (N (N (N E ⟨317827890048,3550387980⟩ E) ⟨317827890176,3544529570⟩ (N E ⟨317827890432,3532848958⟩ E)) ⟨317827890560,3527026698⟩ (N (N E ⟨317827890816,3515418119⟩ E) ⟨317827891072,3503857266⟩ (N E ⟨317827891200,3498094663⟩ E))) ⟨326417826176,7647939783⟩ (N (N (N E ⟨326417826304,7627332364⟩ E) ⟨326417826432,7604489231⟩ (N E ⟨326417826560,7579427709⟩ E)) ⟨326417826816,7522725195⟩ (N (N E ⟨326417827328,7383602295⟩ E) ⟨326417827584,7301568583⟩ (N E ⟨326417827968,7163543985⟩ E))))) ⟨326417828096,7113663517⟩ (N (N (N (N (N E ⟨326417828224,7061900393⟩ E) ⟨326417828480,6952861776⟩ (N E ⟨326417828864,6776057395⟩ E)) ⟨326417829376,6517186090⟩ (N (N E ⟨326417829632,6378563223⟩ E) ⟨326417829760,6307103327⟩ (N E ⟨326417829888,6234269622⟩ E))) ⟨326417831296,5355658432⟩ (N (N (N E ⟨326417831424,5269996647⟩ E) ⟨326417831552,5183585664⟩ (N E ⟨326417831808,5008720248⟩ E)) ⟨326417831936,4920368510⟩ (N (N E ⟨326417832320,4652257523⟩ E) ⟨326417832448,4562041784⟩ (N E ⟨326417832704,4380654875⟩ E)))) ⟨326417832832,4289588075⟩ (N (N (N (N E ⟨326417832960,4198341943⟩ E) ⟨326417833088,4106968594⟩ (N E ⟨326417833216,4015520057⟩ E)) ⟨326417833728,3650009968⟩ (N (N E ⟨326417833984,3468145225⟩ E) ⟨335007769088,3411384587⟩ (N E ⟨335007769216,3315679503⟩ E))) ⟨335007769344,3220520518⟩ (N (N (N E ⟨335007769472,3125958757⟩ E) ⟨335007769600,3032044825⟩ (N E ⟨335007770112,2663859650⟩ E)) ⟨335007770880,2139240568⟩ (N (N E ⟨335007771136,1973195691⟩ E) ⟨335007771264,1892021380⟩ (N E ⟨335007772416,1223897629⟩ E)))))) ⟨335007772928,967282472⟩ (N (N (N (N (N (N E ⟨335007773952,538333500⟩ E) ⟨335007774208,449720404⟩ (N E ⟨335007774720,295826098⟩ E)) ⟨335007774976,230748790⟩ (N (N E ⟨335007775744,83809971⟩ E) ⟨335007776000,51040006⟩ (N E ⟨343866155008,178934⟩ E))) ⟨344000372736,1955558⟩ (N (N (N E ⟨344134590464,5637625⟩ E) ⟨344268808192,11227364⟩ (N E ⟨344403025920,18725853⟩ E)) ⟨344537243648,28133016⟩ (N (N E ⟨344671461376,39447622⟩ E) ⟨344805679104,52667281⟩ (N E ⟨345074114560,84806424⟩ E)))) ⟨345610985472,171711948⟩ (N (N (N (N E ⟨345745203200,198103059⟩ E) ⟨345879420928,226338585⟩ (N E ⟨346013638656,256405797⟩ E)) ⟨346818945024,474420342⟩ (N (N E ⟨347758469120,806151913⟩ E) ⟨348161122304,971925416⟩ (N E ⟨352187658496,3022374695⟩ E))) ⟨352187659264,2995225272⟩ (N (N (N E ⟨352187661056,2933052544⟩ E) ⟨352187661568,2915585897⟩ (N E ⟨352187662336,2889629010⟩ E)) ⟨360777597184,6276273068⟩ (N (N E ⟨360777597440,6246329562⟩ E) ⟨360777598464,6054275468⟩ (N E ⟨360777600256,5464392869⟩ E))))) ⟨360777600512,5357068919⟩ (N (N (N (N (N E ⟨360777601792,4750942621⟩ E) ⟨360777603584,3763669386⟩ (N E ⟨360777603840,3615114185⟩ E)) ⟨360777604224,3390784149⟩ (N (N E ⟨360777604864,3015769312⟩ E) ⟨360777605120,2866362512⟩ (N E ⟨369367539968,2954256535⟩ E))) ⟨369367541248,2185472455⟩ (N (N (N E ⟨369367541888,1825273223⟩ E) ⟨369367542144,1687251532⟩ (N E ⟨369367542528,1487607517⟩ E)) ⟨369367543296,1118197918⟩ (N (N E ⟨369367544320,696961024⟩ E) ⟨369367545344,368519653⟩ (N E ⟨369367545856,241988300⟩ E)))) ⟨369367546368,141626153⟩ (N (N (N (N E ⟨378225926144,262858⟩ E) ⟨378494361600,5262052⟩ (N E ⟨378628579328,10144358⟩ E)) ⟨379031232512,34324337⟩ (N (N E ⟨379433885696,72762379⟩ E) ⟨379970756608,145976685⟩ (N E ⟨380373409792,217089595⟩ E))) ⟨386547433472,2427023636⟩ (N (N (N E ⟨395137370112,4941983510⟩ E) ⟨395137370880,4733546129⟩ (N E ⟨395137373440,3755611719⟩ E)) ⟨395137374208,3402198575⟩ (N (N E ⟨395137376256,2408621223⟩ E) ⟨403727312128,1949742025⟩ (N E ⟨403727315456,582264530⟩ E))))))))

noncomputable def table : CTN :=
  (N (N (N (N (N tab0 ⟨69843617440,11908301⟩ tab1) ⟨71722668224,4992252331⟩ (N tab2 ⟨101674220584,1988345713⟩ tab3)) ⟨104421493504,253682074⟩ (N (N tab4 ⟨105897892608,2369181205⟩ tab5) ⟨130593977088,5495736718⟩ (N tab6 ⟨138110177664,7081760⟩ tab7))) ⟨138915487744,267272605⟩ (N (N (N tab8 ⟨139855009408,1138004023⟩ tab9) ⟨141197189120,3096561355⟩ (N tab10 ⟨166967017472,33693717⟩ tab11)) ⟨172738381440,61503221⟩ (N (N tab12 ⟨173409474432,292090727⟩ tab13) ⟨174348996864,974165679⟩ (N tab14 ⟨175422741504,2053607891⟩ tab15)))) ⟨197568690304,788694673⟩ (N (N (N (N tab16 ⟨206963934592,32947751⟩ tab17) ⟨207635025152,194621067⟩ (N tab18 ⟨208440331264,575753223⟩ tab19)) ⟨209379856896,1228969545⟩ (N (N tab20 ⟨223338519040,9388330754⟩ tab21) ⟨241189494400,14401574⟩ (N tab22 ⟨241994798080,152001871⟩ tab23))) ⟨242800105344,424614316⟩ (N (N (N tab24 ⟨243739630848,896244283⟩ tab25) ⟨257698288640,8849204752⟩ (N tab26 ⟨275549264640,13739174⟩ tab27)) ⟨276354569472,124408522⟩ (N (N tab28 ⟨277294092416,397551293⟩ tab29) ⟨283468116224,4567637334⟩ (N tab30 ⟨310445905536,63455540⟩ tab31)))))

theorem tab0_ok : tab0.allOk = true := by decide +kernel

theorem tab1_ok : tab1.allOk = true := by decide +kernel

theorem tab2_ok : tab2.allOk = true := by decide +kernel

theorem tab3_ok : tab3.allOk = true := by decide +kernel

theorem tab4_ok : tab4.allOk = true := by decide +kernel

theorem tab5_ok : tab5.allOk = true := by decide +kernel

theorem tab6_ok : tab6.allOk = true := by decide +kernel

theorem tab7_ok : tab7.allOk = true := by decide +kernel

theorem tab8_ok : tab8.allOk = true := by decide +kernel

theorem tab9_ok : tab9.allOk = true := by decide +kernel

theorem tab10_ok : tab10.allOk = true := by decide +kernel

theorem tab11_ok : tab11.allOk = true := by decide +kernel

theorem tab12_ok : tab12.allOk = true := by decide +kernel

theorem tab13_ok : tab13.allOk = true := by decide +kernel

theorem tab14_ok : tab14.allOk = true := by decide +kernel

theorem tab15_ok : tab15.allOk = true := by decide +kernel

theorem tab16_ok : tab16.allOk = true := by decide +kernel

theorem tab17_ok : tab17.allOk = true := by decide +kernel

theorem tab18_ok : tab18.allOk = true := by decide +kernel

theorem tab19_ok : tab19.allOk = true := by decide +kernel

theorem tab20_ok : tab20.allOk = true := by decide +kernel

theorem tab21_ok : tab21.allOk = true := by decide +kernel

theorem tab22_ok : tab22.allOk = true := by decide +kernel

theorem tab23_ok : tab23.allOk = true := by decide +kernel

theorem tab24_ok : tab24.allOk = true := by decide +kernel

theorem tab25_ok : tab25.allOk = true := by decide +kernel

theorem tab26_ok : tab26.allOk = true := by decide +kernel

theorem tab27_ok : tab27.allOk = true := by decide +kernel

theorem tab28_ok : tab28.allOk = true := by decide +kernel

theorem tab29_ok : tab29.allOk = true := by decide +kernel

theorem tab30_ok : tab30.allOk = true := by decide +kernel

theorem tab31_ok : tab31.allOk = true := by decide +kernel

theorem table_ok : table.allOk = true := by
  simp only [table, CTN.allOk, tab0_ok, tab1_ok, tab2_ok, tab3_ok, tab4_ok, tab5_ok, tab6_ok, tab7_ok, tab8_ok, tab9_ok, tab10_ok, tab11_ok, tab12_ok, tab13_ok, tab14_ok, tab15_ok, tab16_ok, tab17_ok, tab18_ok, tab19_ok, tab20_ok, tab21_ok, tab22_ok, tab23_ok, tab24_ok, tab25_ok, tab26_ok, tab27_ok, tab28_ok, tab29_ok, tab30_ok, tab31_ok, Bool.true_and, Bool.and_true]
  decide +kernel

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 450560, false)]

theorem cover0_ok : SixW6.coverCheck table 25326800 (SC / 2) 450560 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 74752, false),
  (74752, 74880, true),
  (74880, 75008, true),
  (75008, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 88064, true),
  (88064, 270336, false)]

theorem cover1_ok : SixW6.coverCheck table 48244400 (SC / 2) 270336 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 60416, true),
  (60416, 74240, false),
  (74240, 74368, true),
  (74368, 74496, true),
  (74496, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 245760, false)]

theorem cover2_ok : SixW6.coverCheck table 52857300 (SC / 2) 245760 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 74752, false),
  (74752, 74880, true),
  (74880, 75008, true),
  (75008, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 88064, true),
  (88064, 270336, false)]

theorem cover3_ok : SixW6.coverCheck table 48244400 (SC / 2) 270336 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 450560, false)]

theorem cover4_ok : SixW6.coverCheck table 25326800 (SC / 2) 450560 cover4 = true := by decide +kernel

def bits : ℕ := 240564627292496319244558808449695116540082194577160525234085999619037233937778043901204637489894910428586713112865206048634499012684897353665923511939356788128354208900030462671881941999649054878829906693213405118170297111114732347208927786635058569073006906650200896677299074920363924111579278171295568386642276706970501889943270415963445686356023183481444477733501002075218237474504306349526432143127087429798884778346902586384770072491074328224846857812350158910275295892638125056628193166831431033802859948244389968203771559607156453997772967811410616017276098978800809210847914916723862395611880651844372094436628986439913855855736546714811411558858306299014475697163685935552597589908347247594040141285658503258601133896803258065624345719212352902701875134439048454304614296637624588412789931638011694680643409493467710493176236744896771705129369400488324373212430966160003220000409337672691815758917358735632623002964345633800698878161723584592305837164105642541747966339037484000885295137378194435418540612900794330542888922636219100491027061687910778139035855332316974611087178845765915914662997771441717551767918880215302723543812791879893592934849879080857574626814169312389342648668909304036636345867396136822811953413337127717453130157600825101697271451387624772217295748113977589201923303225641239465025153148634155083342564650096108246136586526719160901192421649074441189293555124020932340645516616671473272598585588735566800855452980911829475842603087672712204185264399917330182991387613975737646790709990621853063956048205166164618372061252487146635783694158512814687444640395653398538283911070402723406610883840677528418926157482015564949744244076086105722128448466934924360523096601799318518418853982512747438456192339819211159726980089272300223627658199099862432382482436947122868700713317334324864512377331740203273554524504381663960095811312520997550274272889294297244355224183242470224410826267431554048360898902398483131765782452594978846464181099239411703017157441450854461719680798034516679445148333920994983588567691551284441101314933959058646112579595150181969129302568377841815028354934107989289055927562378856308095845277260335242837509816251083359092621939975812665338056438229194002473852190363340063932260727640580298073342889060426293627658393446857535283723770381010561073581607249971260546129885028360370629662898172310114725163044942064229014413748323844085999675152044585231573857138811903163070938007781514712799049094708292491640353619925023328311813502609343483257630073764625803359934148216827397103827253864844399819391876547058372784244858028092901813285833035511591591513891469008210696872415974791998250304868478955972046003321532525363896506019709318025719139151329404372017642286179182139149805881779558073728256033308622009732153438152102232126292683641410772882922762932934250983283528532918407122706315289559537735949397648555949585470944554158851751468644654143123425911090677847189594941063799782246871696036716741659859681316874405566756239175175773026785432091749392809455286997187803323030411593421194681939906176631423695982507782440405681532958590838539763858020115946890922904336245059108621316055428526625139204393020301762782887747776783978773097818380483387375004600870628774943842220293242316022880670676738750450966524768253574268625392365141670750362268672377641984700689811702794530544385427265825540790981117090412694432286618984824237839881800790049671781112002362967567199503497027717729955135074993155903239428767241048034431188677502328270723059142773624507643824853062570222765026536705640661371162466918348286809448030634311127697736968253491269318157472577255596146286849735281569280789689471053479853921317029073994063065063717166337827155562702465060340789375209745894720758365551531883866044255069747234915486328217525995580149253521481357287333547976203180316492419747457868776632980623274652706218222342196619377382295436004886269782000107131334346777521015243798402130423339218700120093161520877299194686461574161334983105350314923261788337147192663334728556308354775914075346620876495687869225790578646113394662666635938364018926132385394008763506291297121796696889349614007133296647079750447847582957544424258430703681523611412197049077338348486537269031011931068877500535733544970718104232096971074190426838519310709033462294414488075303073516481565120688222537023478201005922614935452588227058381380244966147995007217604546515021837780742350380758716856833392102951364128535530898258316737291006785703732940662718639817014771300625481539275211482314690885529172068330139082516348436928004527742177468329570803287934082775695909237833914984555027187593532200312064722228064482629785360812298651009995146055088426415348458019248089856777996387148787019903194653153266417108744959274499633776304101050657857036593157402478731805000666142036328944577049304016183701097669178827755965847337968208563212066562349835816083100633531271448959996473660858768429323267702654811651085656126765670961126691222678614656359048183427027086753534986284085140721346261558714740414681388027353280856512983992073432139054848258459097070554313809742758559382281795754688118742572624391377444175471751592628801262522228156395295210618911746574591057779006134751382299780198486384697735272089860203903960488852499143983779641428939866551561682743547409691054232607500723469507231820572420090256069627599026908364063606801509424196395227736983954597538106325798071598681080586152115581508114658696707730605018642449526076449686187517573320014606761149621339918768799073540041309907205019566649783741776135506713205246126461517575080047150418981661163618991143307028880518241318747084783833822858830291436499013674047280075332164951707817417515196649104050779467203582397755252359371728727568578537869774830574800900693710747068808994414730909287271478436833808802721771803946714738379001373925424120516464756486435949505270224448071713176646033633958478283500115020326356659840393523175964286151570503136954581817624047125549378698354319396277393407718747111061451240858656003310336092379118893883490396367305391214120129646085690398246886170974009672247640255719481951556899352839528366599551590638582020811936293503340143057178077595517786802562726184303028519872404717856109899701770124892801478859564709662408105649743218172001344025579945889849570493343126403206572320449597998661086914379887374610111372746764225291291470136940389863729926972280378308061069631400952285584551040737863546439358434972543995656975762967743067926057890934146384927403898645904520108567621183787831729537409374824817932800083457922301534606681021046038587174723843273409326859792618102175928380096487537559376921666557137785897830017748000633034187960566487529728537370337313955110501053284733856729925613585735572851892407795338436834626573440186655207755129180442310067907831847537400043727147744848937548004709175371501706482249816275159325385242074115918732133671257103103583135799005398626532942292627086639137319497084550568937369457762978078132065706679945433360334104899862788047549315467385733091275359956080349438298092716040820568350801682198132845589615217468626803078536563418362683927643277609010089960016741616687983426204738887808188526055954606304305462242470155432249834356127472762032943754250325154817816250741690312146852212382745150899316478176121910967836824432344520524466039194181543539010422917501581383976775238374869309951248479286601859244558963608515799656789773144956650868357612050554746612040833459582566899257533420423960012070449624728313506042673301085616300166331350911487235968573278947455654943017125559729729726092828624675082411426786973413307087785010282407426409809507748308803819546897055568667453156047097856867168025291679802964268343337949030796235242026065032335571904213808498095933090843848726864815633023347749622063556961995161232369562345188371569348182470856994891407461764227806333995894333936010360535635389792166947997958283703682581323434524455480657457023121230331424705817710477807100217909618643830635984514225876191478508679717194968712093372293738030132937197388938270278428771879085906711065793994929509911147828264817488586053097046731707695111673802207145103361263612755047725744916278074124295571126782488442323111080844574334552473013913404872636057249433080870941210428726070110373640533156982551286458398607188906516612959731971824941496119752003613196296307587272401727244223989020854447859655121484589728506577366533441116037557985819547975606597308976337584957251297039465699653458386441527366312751472053242845619917670453318366218622704888144405346726054631242683728484002723801037376214374563172222074917079853735818816528874992867269793678512762849752601307286417372024308109012695057381179857893916561039049352671638402238845106772220282619798548948721257577656860581594762111195969365648807979951537049399288033675161652130462530196057288035392299353098188937805717391365832393579041217961143481105698582119631306444209214171648711546680847047641529648682108389463546592658515055005778420901669376436729372016886646794777875986011227888644196328206844169882902464488990478643467794806800853513598185763761861938440609172341380612810453553171362950216463089792384724239666760693638368323348612698788929200235420113394295144134733622166571898064043579400871930338430777589573523202088931268617889084833023909068086359149024642058395208093908574871886940306432539053598881008983774103498946437753936439272213715629585522445216073534649922676454619387731336305631707040339211355374394537014168048659737481355847654469460815925275763052182963875521955192721140098742171316966945713204986231370126220311425425038264904392710251336863913690359627209524770361342479969064743290563574495160549887636782886506046352204663375881363820183567434887000838467145267851610555136331197908025756876237524982897268899428399642537117426626635868224758931591299840241037034477105544302510028269565906401723538480425271403306339900203512915140604426739089807890581747474853687263337862057318301828412575019629802645863779931097829974530700875368221196454832391113186079432639297092708268672224155131648083825689592565959344610564659784706876292762548755443632544338374667826524323733299691225698433604800679335218339567610892654352871057902642185706644312958988465804732531918590707939170221813059887956648764310656244910038214080890124542330005084046579743443689466557159879452024188596621666073894531677654495088559252346796936505458677275213638628116886779609987200747569593858204471415182726661288760734859952262436698462917111604806833453748009170439095548251701704978912831185265917304790834177697793844850843243156362851206449806680364407907939555255754885884020976931418209612612834524186916969350982037681251998722638263112620488212211170433998274393265388021031568834674471669297837141023888418827183177023554196668278725358208359112460300858050400694080757624837036327191780897391607570271643350726739432424528771003666929709036433109116033074139826227991548234863182642734600602016454204461781683230932148045946345477362623092448872210300730227315237580740547456549053387140856436286343081802066712944602221758438786101908074033720438223217409206457320937060858570466483689692141460152536469667054029200710390057025834074945311540931352004949191023372497692913270647647802822386252732655215443793027018631617604013826190800857935886978752554455430604494154787348336327756148854573247952111972899455648147506679042572020499510133607456640958838701242114667031060163650638561079396029021842115704156421732630816442997947359594930805126569647768467802109119349114478571376406269156604782219577913817416657893050751375376628514740538344271723465523292869078971428292339190675199529298452265150434118440265867914667879169720351708867895179984948254097312906255048879938237246519560083876367433046319001764630439151020980661040063476211403506067065355842131249290944186277657985826752157538798260775855916080902252749080975818544279708465813718057785425606583085007165085848358340233528796029274840107150779169361976153796460468138275797412673742015358673073139585203864507152223966470853824538906948986537081055353604736677961395256140221515079367383095587040473735970906357369618299283320071296486699735008772197019572945644970990146405723257624185612762647282940383591244378832426383117851798677790828071450938357915079495235319501348015476089028892792652873878984778547074046634056590975745499305731394896637862160288815943580087437582656605025463729931103042300678325327211276621065622518767826619064689336981630189112436885554650656255386186240073119152439114835533526009087670465268439365350595964020783768910376355707403291983063917901079282182953873916774615261738327413480909008407109012971586781661086416755769928335316382706907335348210838029004363675396371844660628854321514687031436275649308253085764278327480532126658579463807967856055289022567145106710953323572151943447444025131051870565907995571347583496979006244757392722997941200899182050623689967918034063858966632214257825913417206673713800922101394112207358893521097983168308087705406075840154241178612869124106177747565239718796405284648485257125801927108072267510137465045595373104478857026539429317747308173276392691355606227425995940409771271047636118542761815564312962025759828224302583615639406393255820517502994213660325574495804605353282504440982578722702414335423193574163085028055894426526753393468733741842617575186101083260886948516861791004303918135856471031168900519494287320501796149132432797737549449011013932046394351383142713140136899333936938581075170811695543064446291970002408789912142451324987631809277325837128279124605835095454470404143035172949335991275966089389537976335454549493912692084898063946740063377592147190750252381637206962080191117341981013640277082781581952869625340820699547407538904931846068535415419205707413793379582970051539564467443673981482503146532568824445920313500523282725139344255996857358918054296881088616108630849104786536798395090078767226719373469906445534999883043094067978827469668535535318078406946047772490509855481296138758657514723902096185972817723919750660952554154661900570328107684955590961629786363019647068179287201474645982656223076981609891503074333038397738125248443961599467178502106393515447274349293759238395813025254498721640521680790066445439602100074144226063055253725428826373042432265572271125167699559316121610351184420803882992761660364441328630245551296351276538081699732942140150420777779310813100552220761351991897653186563450643176512958553416159666602002366740174962224276749846975027032148598620193977812201726251974500946606062971427325723990777193245841081748154439270943110659688206715319630516985501793996180933334078012117120118815705739803728087548546234169822887147263159103696559253308999073897716612868521564372060925643028363660482742732820901589234661791742318709438588209538472217720779061077998383020953138172155091432813313670463334674717522563408236163966171852706751263566670574494229969282036734917487776729275009381672028109874258759099434713422475049780582721177341060331384188980885859824592428441551526337494104859126250907547726582941534352276450533432832059932533596561008464989708966526815563592192836022481534924306495109643698229643706179538258166370519087491303098032882081047061103259987339494525387165695006860472740892996037114861794560599317984901246614237058929157790863642675984714232295724965567852552717690995025983900805237603865996316862806207950446513457918634063294754806139916036873009564044243095482782905495221850996660796356247849996432786597199378373670745239570701484029220415414082805982634356015155089427840102742643284323792378802099501448162561780307128897780793062568084125819765182298064548240793595247405789252652390959642667691550258428709008784210614154761655443309909220092447543805003468873010817810822014833437915768561459103928115262228790389525657803886127528224047678395602760668053987256020167800901785223312007275191504877166015026826735819376236192423636706712102695380120014416946084826636597095339026095404673459349584104857653032279290778014008371109590350022509868580510317218222850543273521780894047755591037997052889972347256155167589421231454428425851175779154372754406445401931081343382623379071507834220765118423985249453371985786116524629169062028227240848097759161177566245342428784526506774468927315513277724918981446679152383818830007410925833315846103407805893828797462675894264582269335334221596366403279448791738556244003938106584879742516846382363512809258817551973256399669731206688115598509422352903260826161079852064965936911717939511448567530052896429761433302609710069339234276030951721103142769249692432093991692916792586509704488397922853282457577136448187580077887057072977751940390781905293386801588507524013281767312049092646789316039945550488381358107178830157159126769493238536150683760107853491644117332288793473726555517829644077842598688905793319653281132482784027836688285626847706918820725600072969217650925994522417503614542388832063375001874650840471044368244526961800275305017729775283226952703181611530855241607903140289300056080511666147910812711876866646127366353068643195163205901842514263662765230757719024743430580531402204180719868555143246402806087286935896910973408199433089942663246128540087502316547587389381671247466083502837034843213338566892658258909620826217378655807875225780849444957814092664218415284057317360242514067341071596688131984429534936783497515835941267969552376581280335938943818969333210103250308332207080650940309354674907442340299785425870711805548219290488348525409411277273176081417831924016945363241407511653946460103546941844056767822660645075870060287065085670901509872080590148328074820693581208617879458476482843259113910301323716153646404176673259748705727660762102911583119012394154903829899108459129913821140955941259853406741676039967588020391844350223444239931939605713606730136582807111790059231328808400019167070630957095748917129565427659217537951147759632465688506657512162267727417605459536445523579624243339636825418630809365068679758727883665013695216324762432080699970686054417977413212669112174477214223291108615917745647548163957897410777086511747204201122207448902474804799088623958108361000812376719052264597015515142620291624627192489751404411890179958436862739261578503596374418829470638003388879732084398389326190968243095131313555165065454692889109274286736305039913978355498176824024660022855379503070558323996937651219970789831376100129647613669163452380355747962003926069272058622011095570535821209573986204602339155124389409238095673411537315505940469085308743112552505466579649055476129195214598036544493407159535652349282399902626643546617410630452921331442449062075245290750501783428638897133812626554242420026442809041034682460954830229356074726464336436254257995504392642225492487557328472234116104128033974582148279697793067207876743207945113596540820484855964268819500986552418141741077878669436559001211292665869771467277827399318368993404024703506083636721531919759262696032982972007119991836997780335415616581410689588360932175063317761838260902027275016905227633394220623977458107677924671332538018796841011239910603665721410723940640702966487929725757621986235342393899696912269044428416473711703840910282298416035968102570306108346713868292234500328493388386365543900761813808121175712039528149410079005478222929980376194276741802167818352304262755262470253073128865472131394347263669498745660730355617116006733016200584432353996714201074945481863753465045591731624626464935691028829283767039781851530679607931845789908095021056517379966553823049778683036948484136525707152390960708720881381354798790665641840312562963114404931306247368397614421626588292933131605166965355321332110790950016524700975986620031104961156125211972080310984627552769557230604494237773698534151657191234157116596407162647405807704438247409501674747231423120114522529641253843064168634051996409115917916036132051041418108705596710093711660394812493010098455808737389937209002848331465764225712309216255112712737712172158653780344755844050026975342186552026862263339004420149394128567075354496536031263962155743019292412846539117765487808585382939970124547363613007805972945863028352324076591308081748076755174606628835830255186359439675374935140214044222898447015729756704540396577526987435585620733987876964219091987096605118254172026027217173762477371836267969485040185072162994270809504360929443725665699167780597071763997496511526317469705413768154024093635569082639533527524228455660764083598154439438912933599354957524025678848772397810180694299469260632961042476244865874842922157911991249752209275454909095360859995112185901839221797867192431898396224956808163992696903298649700468086005950394293912159766623268270936887716736970316620460057023849572003845135614248519886832994877313290449860710160536530568854555439244324471414300003033826494263226645576523054532332594220524321000056279019205296864701720093673545382278317915327057715826249898088411713225638502032201460923113013650000346396978706165667069840499612868040980667172728506164907839713124660397187030708075413038961276425509941766499346118006125611314994260912316237820498946717803367293273190884950125038684606561890216902444867692390728441072234213891132167212217071114126125207062313262580097382974739553649744103575632645003070629223164846664796192506103511442088915104784934293273552501120469219150184517030050453697735453082361928076346363183028019301777699993147298112954020227590594881956318203668328998570977012969982422349863319244236012956050289082269204836258657375143464675078702691240942426339321974228904804383498634648834548510344601518317047949852024480007203460371400861910936727345741088784926597400589531372134197310528282944528101194146294053195478918378059158102144029494657111812978448492952536702816005845908349034825891341263335474860937835211854292296097736982574867658083318752676104236355948226960587631610330812279525717411885123209132063159373481116207255637572732701595680869386551431681169645994153732665540078020429621031249051733084933346339685831335737626016713031396297694393882207707340204198590448735183544848580139023769701049301482215829378482210180274955589521581148934902359451954640980887295922299241211851971597632522323930980889055853725809304107770873767158128613562092718755927724808603993361245516427695275158200522084951504719025611108677167879839589815922534289744443326677625277486244193880086419094846825036207826875533894474199560556495993652367705878386494261812268238644749553349297956038495185553890540025186817165630181248948760998166182160729939303555390467122516597926396605756967207369009611163664877925989499119547074544158736361761286554161186701244832968005325467737983612324091842867223863339739152815356740685169308675550429440912259401047942672270114097080391984200305939977729681647419063809941210170279828765247148452129629642636824732473525474020853649890596255396718634050788980998524697852628770053913794245297532731823549136329227548673580109616693787104843837190794516371790342463537787337223363395094147368261833437899476504441846933028417596973122111561702019089303363890335503992327937152991086840177918329244334246221135783186513684577417877371088354531050046624021095656044276933378384379207059120564278518213361072073675949055990584132595816368135710090120341733373833748911391046921130914968178817640142125326594005363444531653342727978036619116188217061751750041202198679032313545984109540065480810795349446432778466664814131977547672243756247300380928303984679371952332777397029004466155082613934951352282356307912972220888817496854470460571409486485431375719440428740903825067956156383782192316819426380213389376043170656133871326974013746286437147677772892475655361706166336508751629713304475010843868830877187103899955531864606097553956337995896655995508303882844173352086911724947915834407972761121496514746191203008595295155250065852740207847024493066012856720401958409724929429223609765240651812259657254879977876084137545980879273802219887403603595675735370566579752398906210898954564297263349581359140547747873022795826330155318668170195790692622556866911449230863222791420466259293408178209712189280411822632175817838183312458580379400895669856258606788265498886433546841251906978672005153556388921364305442127936309737135597525178486894782395240279554312921523899971280104128902456806296414256489144532839392775198252500597871259704416198589222302325157013641772485922305144284038144303799786234768244196190117871289278626669451800069435707477527222708656454714928545372659896950159374058774498443538794117779360872435606273221758190795154764206242325773033288598519288342527779452499153226380445997514088076248432022087063639419628546723014130372396010091998264582898301924498737612698692411472748461696968466330422119156652994207568972342234624234196762275325017384333482818951952909300757244445389752635495146836533760724106974074371347732280354546585606900800541741747691618712210694040845820976420768300896606327577420596532242761393164674414884810718841119597225506990373184964346837210551304975629595042184474197945845801456706374145647037808838834609880550395087375004440261140079018485930344771331194413386801210243022389848392958346683325817462798412440990004185460301099586058018585959475544363741914192716470433908073681341568185418849893763143056290586737985262346500145394783441693699531155754715924677215525242775073942752670466088041963088350533663370141620856683288058418128515439306183573179658732038513648773523297557088904116812381795039559831617160759341339144376385888338673818689070439614573831031851072973258831045670191037800556333930665754517899032703233166331099167634763873403967378997532065494583326350914186789145765651174319012442724477883931723873877307461184600893335748224742261412470728394659484182021183504636649557003674086944642370654718007743872864998214959604139769046292122508847690674968828413594171557356132754092803533046162703773789159219108935055680834574022347590062007325481461387728656821372758618401910317808256105479181406413590953489403624718590977863873554359577726752158449853131846320842823209813338340067560570309172562731470019839341890210115167586522439496471341220426771750954402526561507664269205875001955715180019003248243129136801080376265459383648158657769427192923844843218092758329885361388625967275855057394431804210879487295888492166968612237648576099284306594910716091878737595315014879347650524670884629485562482175474973249392404871693331028647786357598174864091302639431569473123682637615886012212425236720364462387096282601636161791049725820188069287731902035426370997687147325048327679573127046809406848702347523737754659662504924138506579614005034394843657673705503223101449847051174522366130104727530518714367037055788862103907211977687461975292182236278393318158130723813642298556910129063329781016774610657985124830018098667133195597835275952197483035728153414299508460382484922600347165153070387789755050775354261504224442349682426743417127453596474532630696420175732967929823041479424770653790960489746263821211510806671108607315495161792144758086999260299987992434554039916005983378369808685884034511697953870991999753772529448608165113773026430051536419769267741684690887104303524543702667193557628759387641499537938089698101970417159874059641734538908082238843792165721232077284397107204157811530537130897483971293731336419442575333807144758852251109812024877776548809766384100518168878049566645013483056880991515032137080692838233816154161034846398098725830261875276763305348945149599624922824597393004241253698485342088906386611402938747289542599074197356643676711603933088647195238486249633146413010585309736924620094455842761281169497408855392588771586285709855222453788889204991531358771482797010243605651593067028232939795815401217178342697684297252003950439649077422480174785598304565637560085042242905227674452798968108657940275222399970150656575888636441430677952075278332708832469191178793514055169652481299481103922475109476073435930570453225782411169366047290436227185145218431373295325141982644762408429578601200629341457456046286066591254400133270569580922408729147846073519957624126090082039507774754881513687455223897904033213510209596435904348309752679969733784887459989026629726024722557520508350849462254624784061977488618417390222157612680582306284401182463471299408039602271131731107570933227028356803695442480069723516074094871950505288369080151664401714887847827086656235574046339724954375710542565140541836188623165644296719988615317252729836731587268243531782008779735885997689498961912699012763873196669105998444358373004612104448133812181519558609520607371062010316137140345984140068817139901267630742519028914512697684613990151511096349858007341874007669217368302987287887485486974770754619592250821386759225401722625360105511438912622499818283583567912974051970883834052754619935038857637964239116447915775749028295002412987166082346538074491215410300570244683684054843913916571247525048399596802336704563742781635096690973172697153024554912743715477698596043578414163106493174044462363779354135297484155575163240742438502704129737748179351473276269841236894568276175739973996951871961034399825715453973215835749731481224493596566973996310051051591894955462301313476491658331532725719807445204520748704687177723519278734301212853505473395870339036892879672649380491991977944717684168785635122742805558063972105018255877010668324866051923365815349608696841988360957604418790765764053205502243193984509516524116813294312066665050547381647437843792108056978185435350802626106939805326862125607458892218500549343581774396361952829557609799073566133225902773728597748856056034615426489825586935221404735039470204212181434128295536182003025049436939637745059272341168402211587589546804747364053729337000576309582728930866114698591844200040065515990069863771668137168181296053974367284763020655736231062191982086630115126735065846532900518134248293385614061137614413415331795988742948625243186305291037363562887290187831848078198714058537488775552259567351421525070554993005639280180106090839927468994001989182131480267199787979739744528690257754495896702342635369668278811434900163838788563914415067953802878577591956488953160684557376395634732001006763253298097675595407112085702128233313401031376123401182311479355655694806262212012915415684060834750594934988085349546642532373308169781529539411906718488758099341400193557544027823379188743711213358779244257212066882417059618933942808606708529248610250842058239581364266537828511231288051833252396884057255541792291916642997760910055521519511537164082740322789657637111653243245785383909151351544750806423368590445465028378020395107525211625638565523411271055384873512768913698663809982898473192844276130472313644557581755189984230669853590359587944787852679978365850521197626550433689117749754248550461072172892330241201864706430613757501743744084471756332594818373272103110071558644801661734465648889945793050589542005922588541556424126891469075925106817350466201991246672648206454548917911896579079912103114678219530836492238672718251675523084674746998391614383349517847407876555965378858718920184070467128962188353334362472635695852200111810321576391650469266844128492476959305246353795804863798286157279650699725867710393459632885417809847279794622246684617986240096310181592243634261619029058716028609087373477077569182570144770145671962584050368971514206168213950564159761554489094853538058242952337480340114585991783305528256476661255592466963745187598282678724460738851679823327114900375528076243973655448447449233883671494681421124480266710627322001064922166442120662952134926961073700814348887012426164680859489200126708970697842132148406217070361316161220596415982900533857418279972815974409750352681296895149922041063185833276035930739788087098365631744876125788135300145663493116692017344442589592758667554563017052119560563012470538253355016371995682658860529475310903442660302584424813782832116972811587965743175818018006837607427204649846955023270185762128208919405390481963913044066271260864306354393528929213584001776533370678283082429133367839094240435415517799887569898788292549989027764685626809352081995013967107214120884685512648544083326734110655190760676195537803650579213252423469413675993482642454688966907096396076177973357318670971822915353294211620485153782287128618425091747584614354980784417025916098088067969090539057232781315236302041742058522173923971291012667589130061172275663361247277775712196150832094565505388698691965687217123582249325181264167875600590866822372269989805345255473132310605400913061193755000271617935707613181400729778541562727869600705453557933939235854640531119273780624373153442148418531842248128222829708244098450672022597855109427045798074984610355206392797594152858917435107431060701474828804370500612608905827107253115903719906286641661205053180645043064887356104437693974358918979412528878538249622309024554330335560920620039656429432846687413168623948539347728495326353570347745915674884364001658869061352125493435337392809813489053070434228018668090169284680708643675057939411167248099921255877002331141517792009635742501807853352476362430853237371650927493151566240072650596340094252413062171028278392952475615095474166643608299960672942949515402464839872418146768053813639169658618492628741244072740427044947700304001240963151250826559106739829030301175109654376330094252031138865109833525859307635745696284333015095644273827026675960815715855322465415106972131589661964295572356395956846291445479112244789495199281195355667682486593332627980424046568470200444651184320589471955146779133810174532484952145000310137858479919818670334709585949002482588113613114951798741791026473316506908699059738790971635777081606585709015626423191932319831249683808442286979663578239791212422342336519454012653865091193299149445723701704126759449360993478231421659397558797065560419951703981240203349099180076953057699535673880389300953278025363330993402494571194179897236265849994239486753611412133242541576370333729659442020720013165961574227243677563691315735260956988834357302787964228567995931300243660353309372336403277012238541045859865697011447326346803046257821003927852532096041836983733989858172289695976074730927209422802633143244077717255351746185018111119358257407756733228547382570945179340037334463960496952004802324349140831525989348633364353452117520420161440963303548596913923626711262840433113112926473314471640219394305661685850862577326831207936273922038058588791193710696143804406025738183791331515633903648786119079729455236415448749510143901783365840312164651413505975041802316186474060869020463208057371836119754892414418053373464148839023723592016725014622215470844842731129086696977689143208610802410551080903614645723467941992926762796677723112990796136573204396927928120154710844989307123052037869404742823454155513366152706453264007766398866505104131299153520264316733371145253293788813644345435244574509729640692548117148332186109958734539487022273235444719496315780046215856510268459656742866457611649852094460531592721432589343591718610924214643766579857117483426862904434406962095305785358449682938692987397489087206070319449699619765007183109066181758467753388658059637451663272070333327178874517990701342069662571938267314290255411463234331649960885367910727463187377031067501367572335492541887592939850218355287899718943883891158937762792307898075574894229884944160119716752171967705171584764494364756684387178016251500292818978901646602163722283312550347900418917924646237350863737628800264086773940235515876738102174778467152971456142419026351922283327137910452015406261576914724035550370923401321374608664244363055992119966825163963728466416200694994694629883035467147781869280081907796565065910353578197403943442299161555337880721181341066865193032039069213026722396062070837405627456147618369121940727613402690823714476913179825218043082765361711132370742968390703156394919713240652688950455440941820450959321139058768900655518014238549347824965515771771952780850815332965874072919361826186699480462401858939257915567685872517887948749434423684164565752878851946501270558688629697467792603862310928795245746545721089474684555810701766939760766852384150117567778137605364994888267635254640895191610844390437167604213995552428662802143583906565185323076671954906732133980761837634991406035427338233144542794975097921469233081790077431630330630568413626838637236426469943074021928982377442621226998545347586781810357619214308126732229181367699499361234115843823665374249667365292300526688641039100551463955701045188782468621338679781931617890110540741153473547489231114596170855922402805789559339159067755562547911998025261390062130528321078007423500151172570220237101396358652329432680791096847722818046437483464203843791554786627813272534474980405439083378809435042107513437320086658434615672416044877377615844418007132878176834664620523315289727608844983455485249960376899784177456537391681269479286380898030792251156959679385389753298414479417349540486467859343510315492364952378808687216085644719374635660454794145225577351032628585703174265194781535386045054588260989666177775628749739376081872377867763696820752141423726095404258448631634266044117332493634333836389861012537398159518689857570574734816665827398033473482485064794229925332311679396719749247401750282229951435270100905598160541125472871158844015878102036034040071810093970303825835378279126848662470049189841942100513105235277821190733814348358511425775859539154507325802773102538398138279081287114919891144548080346352525039575028451323142047679905447071117213281791373003583310011867583088354024477644134125413461878455683249196309282070572956037746323864806462030733919588882764513150662371664603994979451426214854578902218727212918527751651226319432849585367543358284892388795455696955951689766678702975382397428981976441435138595644864215624335906753821750790754950644191261772276142302303600282528014308467585334935511515462985280917774580767699316238905422186929042637973073575586738148817678081597593512949218266259537887706780101590518258557128141515326635692176447570805801514444229507819389257060251326114068437236281342841594579527777068037101992130865264620273566560368260156396986319846263503455840992196146518861186286328871200307851328661763006721199284684550078614314003076848790845425273428303749660301061843687655769331783777814097700495136937033199442613156365018550033496358760849094520359914862273558992341364365496756194792773559384981276257609576505411211464357121911298202414985480938501219207916589294066783503833154298665925111661015334572575625879509783071425206618265061018289484720694209207882366011883890406905558808826635770331715445995531021587620283685934710372054434633044091183518216973844433289035023470510880377866482301964930977653437453255850659606063704566340228714724821047065292473011320278042141130482821379920770052283283036642521161166482529389898862394521686775744615821411071112614262879345353810971402437012711322649965454424319637095449780922637371950589238680220388496767345284911531558215260300137040633625272444837306202928195108167675429366223942763084799892829278161897717076859116811333563798740249740204512811830446505694096921989918823382997839217066809758820364088382414759797162707184190721273384984401201490230552448601761569734580895036496010043279424736462710587363458292388247548880278882145467442444962633876530664605250718334589221256412415794668672964710532827609941251867595828483557491862937798248956121206988290005307024122652294354024715513329463042847913084743839224384048580506756163434158205091423824782945835498238717519499355360573315182069595185437079830003949835399536154628111786214377571053789161475848403256431675260366519602226258922164981281035542606850576243050048863551048975031725193585039149340266162518456465310060202547210385932939264802881089521778081301253732525931019971045471395556573201388953143325360628653705707163408620411205139176532939467389722092657029983964471515917817126223955167758664944482078823261694060587346792160530053635607069362775520980314307966175827075104719137823677391491895627524430821224559577363485015167242282342542329358259470933492382132414608734489514019798310467271712840018361960878359507990569840590242862544167380228997278116713663383059504509494606471387813034306370175048033420666327398180825189286892214525053388907167923370006463381144874471312671802621676483102645614737089919950562338760247250512944100520834396957685342169431766712361761556266871133598966969051122238068521271758545648694604253426476814449444066556492973641739871572517843777730348908201940935440337458775589185821364372554062856952412217205526408597792647076258270045795083407527255328150841982912887085966361066416602793342808961584481057182014418324461551643387634028772144522969891526156779987093104865277199199491980991050334185033630199478533310551683327152337843663105455955881927887568802353857419316781028291320159452515698371193616214211389815771991901904121827157206151088526491661895756694768968363256735517874687637108767952584784368910885553684588215822615508598240608611609915548714140465286148320653190085124728528417142067304750945737126982959200050227703979312611103903739759989852047089313260289061082791743202721072673678425055780619593616286987816043003951557836879009330118456378758908780379098502940717973113870736955765246293866179964836098923331322870065046983637462317904721090063468307094793691840891514455278295651391957317867253000838899314708541880088643954199774261817865006414725573563365530651091731812277389669453329740826185763673039091070551508627563176968484391881832629960403634656830817025124514804602860603559090714425633527003282542012664828552627016001387032832119404915924650234776439375650995408688761381292610445380616560342470126471091922699698440507910451544380492554442968771431246090163665277021010764480772113459255442332257222223737882258120012208861439219274086576817111509504872806564248012352555713190149368577747801635506142401940734257869684531591010137603956980030071927632137783429126932956986275216208418199659839479112066981363337795348940972927423222824074809021840749252246775407271700285075974949057114874905321661354798743622094411851009672700633478158020542763697773045914573799480436788412498407340243669141499320386659202797854808208593847412730743962430070934196912753443276918047869700337796791474224243401021134464823765731185057049987325683456523388498141314793041935095021983156918821600774192061731478499163530452247327490366862967385188894991773661216890950563292559144926798501494008038213894367319269322317640951675234775424990026806106107899246024277684958565157378972404464218416005026515357142274290126467187789247245449794914196003648528535626703546961825073891082829031989724567896406037903862871551689373011957236396378340455736373362577250632901480579802224363347374619203258719257932873494280859756751987286111427596477854006072825861471226627087171444481815025632908181161095243165624991866898703063922969672459103548930065306032343025300631121647229099669563673102989826705122543619433902803986805473203004436092640563871438872309740044873999599151262977509067882275667908306748062791407819609321038689941452429926629490286337788142193346459528082899344067612720594583920700705195089357569332488238878027534328138619198469809943972711744048906632125019131347969925211585940855782074436169592488779459936137342531710799690338177631225076395020843409089104194894741925398024062278624816828585285029648435722986256432738731199387712352715367573537634392486319192491119874762995092433725175799898152444873608576936814253000539727666747991816627553537786735456472437960397595121303778839578783546276284118098840474709340479569391302560770827454083364273492426444599171273022385833412068334290319177207757579200764997938971907598721193633118595371175125230792739851142688943118314411233066822282370361468973505975408126132776818194272893935997440729627259352521852498719851603627613834781299323031798230671934648507095537093931663814984050754921954421747484332962267750066736742893025564374503681196969827183526690142158777105932606275496172588910285642988629725319375976490048962892534835244313553532732492536129739992389389459234486797998096879649815098295515394621131199407965747793198756747645974595880772673548021033997317688238260751033505631192303792872281118198348229935826291567746412447742157110732514654304733406792065044595486761663602135934630660966375219320263033941276185767149123676314268924529812521175638744638098937586038438630670578729668799943329048530791384546990626384718431516829266058338638413898229541519847469858535149952440644460310789423314532026782816508866069476380444773120914104125651497324399292168584224877981371023359147946537760505405726193789118860009829513121816121016679690840351638983397651902767415155300708546568788220125690245593456518051639580626619243904437291766066193527901657025048021470687790450433739680498334194295116003637950859864645757727547608158970686244374774072546898980783784930446906441407076568803525506904747413366123684912979620683976919966569488407761061077474404508317032464011038492286907946314148852357148316962421383135607541813149217001741151555298982675148619088868325680828195109168853198248985913505442563058292820661629524257978696578686002994724469051468441276565633730078396145644539007403483664886924533595096758447877332435338285979577274550273173169820340680774743018708042919002230939888728267228908337258843288985172726439639646657412113544925191499666929618776564080915804566283100496429330950108261178705419274090727397537577823926697440258617358070410053171164096772072880961960834939453881968369833907749332850399711243411839233982035455725051619561312773690713834428562978808925363350338942326356679913190165439097893732977515837561335263285536552987076980370992468588600740041314010582214028891539144815365780484399933848815819046367028814347594382145642160937202694955030946410767851232249514655416140334670047586137585174720459241987160213003713448013348493025810824712213741991193109027470140752071189114343093540905904523632004710261229559735516229591679940289392291838685162532513329823233172249448210880671572652158461157970339167870172901872480343493151770136029536052342730626954812114139060150925852059549205974886260820433079544896487773566953092833743523181459813439617015492797589259221477090115302959072927553578337696235351916852672665169065853858220265284186939603793897567760296221773953345419671797851634816790015483043062576998005214514827400411089517182914249064840951898779748579903501326590172161676676149139470594619985827575866280402242992579250858010512279998068755556350733237477114436395298675524797342212052843117550370469767001658730542819438358566420964968841541640387565763341127999325965987228183974045216940939973990604650622062613176269044826580297320703846292407667179901598966030531130793034345163754766441761951922678766753789351164030576686750022009374404376593907496431305695673408329628747738126846084970459066619014517315695392081343172825883985785212900676650255555648541682740997202762149337789686326600573344812176573749322499147168379458322994409355705158819010517137184632916159220147023642175655284328516740432968290437979766170422162588237039261098881981360551325720100563288309745090293247499674772991175195958946297681485413883131883589741897418956860969478061790050986245532639873191936019381982747392133546040253470465108248271891147744357606841930523633786015697420878469353163474886149387909402966330695477531436325241655441156940466385392929871498087711824260920461909679671594125898377358409150091918236220133484998437027812008351376763720145222665243575301379435315050985541189443069150690699925091828283043553058838174830901176535117981503444969168037784490416573492836557165882531457890240701324682182861244112200146260623276748109458450991193424132645058747065244663019235836011554124859770546076130582093296841827541594892254210612854770143623170874673270930650485615603687801766134446518274701347691123080939212248379809124414052678615673969110496147056809647654448642425364357163637716056796333181539677118737395832242500309681022080547103291764822337683459560860618048458314553333089561865925607457992555214695341653240915103541900982035831385510556397719091409987210831789004736643320441666099485212420774393877886999784592564587248240054239245715357961969303971803522926949479736537619507295028333957106960645338426759520665417662225465176654774675421676679797804572628559135187029804012856941048874683966557294764994666789676266235193663439753781954532612024793542178446750986744927222325198112697175231355944701532469097401672707641943502768893356198165051329576769188895985078341985785555257760265183531904055032495486324473217580441228997752397890350335493315430501297234356973184656380540737512045493029420220043681468925247562855019469094206642583739434559263153524622062835265013858179223135963418897

noncomputable def bx0 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 31744 38400 30720 40448)

theorem wk0 : SixW6.walk table bits 64 0 bx0 = some 1536 := by decide +kernel

noncomputable def bx1 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 31744 38400 57344 450560)

theorem wk1 : SixW6.walk table bits 64 1536 bx1 = some 5857 := by decide +kernel

noncomputable def bx2 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 59904 74752 30720 40448)

theorem wk2 : SixW6.walk table bits 64 5857 bx2 = some 10343 := by decide +kernel

noncomputable def bx3 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 59904 74752 57344 450560)

noncomputable def bx4 : SixW6.Box := (bx3).setHi (SixW6.axOf bits 10343) (SixW6.Box.mid bx3 (SixW6.axOf bits 10343))

noncomputable def bx5 : SixW6.Box := (bx4).setHi (SixW6.axOf bits 10347) (SixW6.Box.mid bx4 (SixW6.axOf bits 10347))

theorem wk5 : SixW6.walk table bits 62 10351 bx5 = some 15177 := by decide +kernel

noncomputable def bx6 : SixW6.Box := (bx4).setLo (SixW6.axOf bits 10347) (SixW6.Box.mid bx4 (SixW6.axOf bits 10347))

theorem wk6 : SixW6.walk table bits 62 15177 bx6 = some 15373 := by decide +kernel

theorem wk4 : SixW6.walk table bits 63 10347 bx4 = some 15373 :=
  SixW6.walk_split table bits 62 10347 bx4 15177 15373 (by decide +kernel) wk5 wk6

noncomputable def bx7 : SixW6.Box := (bx3).setLo (SixW6.axOf bits 10343) (SixW6.Box.mid bx3 (SixW6.axOf bits 10343))

theorem wk7 : SixW6.walk table bits 63 15373 bx7 = some 15374 := by decide +kernel

theorem wk3 : SixW6.walk table bits 64 10343 bx3 = some 15374 :=
  SixW6.walk_split table bits 63 10343 bx3 15373 15374 (by decide +kernel) wk4 wk7

noncomputable def bx8 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 88064 270336 30720 40448)

theorem wk8 : SixW6.walk table bits 64 15374 bx8 = some 17060 := by decide +kernel

noncomputable def bx9 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 31744 38400 88064 270336 57344 450560)

theorem wk9 : SixW6.walk table bits 64 17060 bx9 = some 18221 := by decide +kernel

noncomputable def bx10 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 31744 38400 30720 40448)

noncomputable def bx11 : SixW6.Box := (bx10).setHi (SixW6.axOf bits 18221) (SixW6.Box.mid bx10 (SixW6.axOf bits 18221))

noncomputable def bx12 : SixW6.Box := (bx11).setHi (SixW6.axOf bits 18225) (SixW6.Box.mid bx11 (SixW6.axOf bits 18225))

theorem wk12 : SixW6.walk table bits 62 18229 bx12 = some 19205 := by decide +kernel

noncomputable def bx13 : SixW6.Box := (bx11).setLo (SixW6.axOf bits 18225) (SixW6.Box.mid bx11 (SixW6.axOf bits 18225))

theorem wk13 : SixW6.walk table bits 62 19205 bx13 = some 23256 := by decide +kernel

theorem wk11 : SixW6.walk table bits 63 18225 bx11 = some 23256 :=
  SixW6.walk_split table bits 62 18225 bx11 19205 23256 (by decide +kernel) wk12 wk13

noncomputable def bx14 : SixW6.Box := (bx10).setLo (SixW6.axOf bits 18221) (SixW6.Box.mid bx10 (SixW6.axOf bits 18221))

theorem wk14 : SixW6.walk table bits 63 23256 bx14 = some 23387 := by decide +kernel

theorem wk10 : SixW6.walk table bits 64 18221 bx10 = some 23387 :=
  SixW6.walk_split table bits 63 18221 bx10 23256 23387 (by decide +kernel) wk11 wk14

noncomputable def bx15 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 31744 38400 57344 450560)

noncomputable def bx16 : SixW6.Box := (bx15).setHi (SixW6.axOf bits 23387) (SixW6.Box.mid bx15 (SixW6.axOf bits 23387))

noncomputable def bx17 : SixW6.Box := (bx16).setHi (SixW6.axOf bits 23391) (SixW6.Box.mid bx16 (SixW6.axOf bits 23391))

noncomputable def bx18 : SixW6.Box := (bx17).setHi (SixW6.axOf bits 23395) (SixW6.Box.mid bx17 (SixW6.axOf bits 23395))

noncomputable def bx19 : SixW6.Box := (bx18).setHi (SixW6.axOf bits 23399) (SixW6.Box.mid bx18 (SixW6.axOf bits 23399))

noncomputable def bx20 : SixW6.Box := (bx19).setHi (SixW6.axOf bits 23403) (SixW6.Box.mid bx19 (SixW6.axOf bits 23403))

noncomputable def bx21 : SixW6.Box := (bx20).setHi (SixW6.axOf bits 23407) (SixW6.Box.mid bx20 (SixW6.axOf bits 23407))

theorem wk21 : SixW6.walk table bits 58 23411 bx21 = some 23922 := by decide +kernel

noncomputable def bx22 : SixW6.Box := (bx20).setLo (SixW6.axOf bits 23407) (SixW6.Box.mid bx20 (SixW6.axOf bits 23407))

noncomputable def bx23 : SixW6.Box := (bx22).setHi (SixW6.axOf bits 23922) (SixW6.Box.mid bx22 (SixW6.axOf bits 23922))

noncomputable def bx24 : SixW6.Box := (bx23).setHi (SixW6.axOf bits 23926) (SixW6.Box.mid bx23 (SixW6.axOf bits 23926))

theorem wk24 : SixW6.walk table bits 56 23930 bx24 = some 24636 := by decide +kernel

noncomputable def bx25 : SixW6.Box := (bx23).setLo (SixW6.axOf bits 23926) (SixW6.Box.mid bx23 (SixW6.axOf bits 23926))

noncomputable def bx26 : SixW6.Box := (bx25).setHi (SixW6.axOf bits 24636) (SixW6.Box.mid bx25 (SixW6.axOf bits 24636))

noncomputable def bx27 : SixW6.Box := (bx26).setHi (SixW6.axOf bits 24640) (SixW6.Box.mid bx26 (SixW6.axOf bits 24640))

noncomputable def bx28 : SixW6.Box := (bx27).setHi (SixW6.axOf bits 24644) (SixW6.Box.mid bx27 (SixW6.axOf bits 24644))

theorem wk28 : SixW6.walk table bits 53 24648 bx28 = some 24814 := by decide +kernel

noncomputable def bx29 : SixW6.Box := (bx27).setLo (SixW6.axOf bits 24644) (SixW6.Box.mid bx27 (SixW6.axOf bits 24644))

noncomputable def bx30 : SixW6.Box := (bx29).setHi (SixW6.axOf bits 24814) (SixW6.Box.mid bx29 (SixW6.axOf bits 24814))

theorem wk30 : SixW6.walk table bits 52 24818 bx30 = some 25104 := by decide +kernel

noncomputable def bx31 : SixW6.Box := (bx29).setLo (SixW6.axOf bits 24814) (SixW6.Box.mid bx29 (SixW6.axOf bits 24814))

noncomputable def bx32 : SixW6.Box := (bx31).setHi (SixW6.axOf bits 25104) (SixW6.Box.mid bx31 (SixW6.axOf bits 25104))

theorem wk32 : SixW6.walk table bits 51 25108 bx32 = some 29719 := by decide +kernel

noncomputable def bx33 : SixW6.Box := (bx31).setLo (SixW6.axOf bits 25104) (SixW6.Box.mid bx31 (SixW6.axOf bits 25104))

theorem wk33 : SixW6.walk table bits 51 29719 bx33 = some 30170 := by decide +kernel

theorem wk31 : SixW6.walk table bits 52 25104 bx31 = some 30170 :=
  SixW6.walk_split table bits 51 25104 bx31 29719 30170 (by decide +kernel) wk32 wk33

theorem wk29 : SixW6.walk table bits 53 24814 bx29 = some 30170 :=
  SixW6.walk_split table bits 52 24814 bx29 25104 30170 (by decide +kernel) wk30 wk31

theorem wk27 : SixW6.walk table bits 54 24644 bx27 = some 30170 :=
  SixW6.walk_split table bits 53 24644 bx27 24814 30170 (by decide +kernel) wk28 wk29

noncomputable def bx34 : SixW6.Box := (bx26).setLo (SixW6.axOf bits 24640) (SixW6.Box.mid bx26 (SixW6.axOf bits 24640))

theorem wk34 : SixW6.walk table bits 54 30170 bx34 = some 30221 := by decide +kernel

theorem wk26 : SixW6.walk table bits 55 24640 bx26 = some 30221 :=
  SixW6.walk_split table bits 54 24640 bx26 30170 30221 (by decide +kernel) wk27 wk34

noncomputable def bx35 : SixW6.Box := (bx25).setLo (SixW6.axOf bits 24636) (SixW6.Box.mid bx25 (SixW6.axOf bits 24636))

theorem wk35 : SixW6.walk table bits 55 30221 bx35 = some 30322 := by decide +kernel

theorem wk25 : SixW6.walk table bits 56 24636 bx25 = some 30322 :=
  SixW6.walk_split table bits 55 24636 bx25 30221 30322 (by decide +kernel) wk26 wk35

theorem wk23 : SixW6.walk table bits 57 23926 bx23 = some 30322 :=
  SixW6.walk_split table bits 56 23926 bx23 24636 30322 (by decide +kernel) wk24 wk25

noncomputable def bx36 : SixW6.Box := (bx22).setLo (SixW6.axOf bits 23922) (SixW6.Box.mid bx22 (SixW6.axOf bits 23922))

theorem wk36 : SixW6.walk table bits 57 30322 bx36 = some 30383 := by decide +kernel

theorem wk22 : SixW6.walk table bits 58 23922 bx22 = some 30383 :=
  SixW6.walk_split table bits 57 23922 bx22 30322 30383 (by decide +kernel) wk23 wk36

theorem wk20 : SixW6.walk table bits 59 23407 bx20 = some 30383 :=
  SixW6.walk_split table bits 58 23407 bx20 23922 30383 (by decide +kernel) wk21 wk22

noncomputable def bx37 : SixW6.Box := (bx19).setLo (SixW6.axOf bits 23403) (SixW6.Box.mid bx19 (SixW6.axOf bits 23403))

theorem wk37 : SixW6.walk table bits 59 30383 bx37 = some 30414 := by decide +kernel

theorem wk19 : SixW6.walk table bits 60 23403 bx19 = some 30414 :=
  SixW6.walk_split table bits 59 23403 bx19 30383 30414 (by decide +kernel) wk20 wk37

noncomputable def bx38 : SixW6.Box := (bx18).setLo (SixW6.axOf bits 23399) (SixW6.Box.mid bx18 (SixW6.axOf bits 23399))

theorem wk38 : SixW6.walk table bits 60 30414 bx38 = some 32065 := by decide +kernel

theorem wk18 : SixW6.walk table bits 61 23399 bx18 = some 32065 :=
  SixW6.walk_split table bits 60 23399 bx18 30414 32065 (by decide +kernel) wk19 wk38

noncomputable def bx39 : SixW6.Box := (bx17).setLo (SixW6.axOf bits 23395) (SixW6.Box.mid bx17 (SixW6.axOf bits 23395))

theorem wk39 : SixW6.walk table bits 61 32065 bx39 = some 32706 := by decide +kernel

theorem wk17 : SixW6.walk table bits 62 23395 bx17 = some 32706 :=
  SixW6.walk_split table bits 61 23395 bx17 32065 32706 (by decide +kernel) wk18 wk39

noncomputable def bx40 : SixW6.Box := (bx16).setLo (SixW6.axOf bits 23391) (SixW6.Box.mid bx16 (SixW6.axOf bits 23391))

theorem wk40 : SixW6.walk table bits 62 32706 bx40 = some 32867 := by decide +kernel

theorem wk16 : SixW6.walk table bits 63 23391 bx16 = some 32867 :=
  SixW6.walk_split table bits 62 23391 bx16 32706 32867 (by decide +kernel) wk17 wk40

noncomputable def bx41 : SixW6.Box := (bx15).setLo (SixW6.axOf bits 23387) (SixW6.Box.mid bx15 (SixW6.axOf bits 23387))

theorem wk41 : SixW6.walk table bits 63 32867 bx41 = some 32868 := by decide +kernel

theorem wk15 : SixW6.walk table bits 64 23387 bx15 = some 32868 :=
  SixW6.walk_split table bits 63 23387 bx15 32867 32868 (by decide +kernel) wk16 wk41

noncomputable def bx42 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 59904 74752 30720 40448)

theorem wk42 : SixW6.walk table bits 64 32868 bx42 = some 37594 := by decide +kernel

noncomputable def bx43 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 59904 74752 57344 450560)

theorem wk43 : SixW6.walk table bits 64 37594 bx43 = some 39530 := by decide +kernel

noncomputable def bx44 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 88064 270336 30720 40448)

theorem wk44 : SixW6.walk table bits 64 39530 bx44 = some 39931 := by decide +kernel

noncomputable def bx45 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 60416 74240 88064 270336 57344 450560)

theorem wk45 : SixW6.walk table bits 64 39931 bx45 = some 40112 := by decide +kernel

noncomputable def bx46 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 31744 38400 30720 40448)

theorem wk46 : SixW6.walk table bits 64 40112 bx46 = some 41873 := by decide +kernel

noncomputable def bx47 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 31744 38400 57344 450560)

theorem wk47 : SixW6.walk table bits 64 41873 bx47 = some 43094 := by decide +kernel

noncomputable def bx48 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 59904 74752 30720 40448)

theorem wk48 : SixW6.walk table bits 64 43094 bx48 = some 43480 := by decide +kernel

noncomputable def bx49 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 59904 74752 57344 450560)

theorem wk49 : SixW6.walk table bits 64 43480 bx49 = some 43626 := by decide +kernel

noncomputable def bx50 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 88064 270336 30720 40448)

theorem wk50 : SixW6.walk table bits 64 43626 bx50 = some 43682 := by decide +kernel

noncomputable def bx51 : SixW6.Box := (SixW6.Box.mk 30720 40448 31744 38400 88576 245760 88064 270336 57344 450560)

theorem wk51 : SixW6.walk table bits 64 43682 bx51 = some 43683 := by decide +kernel

noncomputable def bx52 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 31744 38400 30720 40448)

theorem wk52 : SixW6.walk table bits 64 43683 bx52 = some 47889 := by decide +kernel

noncomputable def bx53 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 31744 38400 57344 450560)

noncomputable def bx54 : SixW6.Box := (bx53).setHi (SixW6.axOf bits 47889) (SixW6.Box.mid bx53 (SixW6.axOf bits 47889))

noncomputable def bx55 : SixW6.Box := (bx54).setHi (SixW6.axOf bits 47893) (SixW6.Box.mid bx54 (SixW6.axOf bits 47893))

noncomputable def bx56 : SixW6.Box := (bx55).setHi (SixW6.axOf bits 47897) (SixW6.Box.mid bx55 (SixW6.axOf bits 47897))

noncomputable def bx57 : SixW6.Box := (bx56).setHi (SixW6.axOf bits 47901) (SixW6.Box.mid bx56 (SixW6.axOf bits 47901))

noncomputable def bx58 : SixW6.Box := (bx57).setHi (SixW6.axOf bits 47905) (SixW6.Box.mid bx57 (SixW6.axOf bits 47905))

noncomputable def bx59 : SixW6.Box := (bx58).setHi (SixW6.axOf bits 47909) (SixW6.Box.mid bx58 (SixW6.axOf bits 47909))

theorem wk59 : SixW6.walk table bits 58 47913 bx59 = some 48439 := by decide +kernel

noncomputable def bx60 : SixW6.Box := (bx58).setLo (SixW6.axOf bits 47909) (SixW6.Box.mid bx58 (SixW6.axOf bits 47909))

noncomputable def bx61 : SixW6.Box := (bx60).setHi (SixW6.axOf bits 48439) (SixW6.Box.mid bx60 (SixW6.axOf bits 48439))

noncomputable def bx62 : SixW6.Box := (bx61).setHi (SixW6.axOf bits 48443) (SixW6.Box.mid bx61 (SixW6.axOf bits 48443))

theorem wk62 : SixW6.walk table bits 56 48447 bx62 = some 48613 := by decide +kernel

noncomputable def bx63 : SixW6.Box := (bx61).setLo (SixW6.axOf bits 48443) (SixW6.Box.mid bx61 (SixW6.axOf bits 48443))

noncomputable def bx64 : SixW6.Box := (bx63).setHi (SixW6.axOf bits 48613) (SixW6.Box.mid bx63 (SixW6.axOf bits 48613))

noncomputable def bx65 : SixW6.Box := (bx64).setHi (SixW6.axOf bits 48617) (SixW6.Box.mid bx64 (SixW6.axOf bits 48617))

theorem wk65 : SixW6.walk table bits 54 48621 bx65 = some 49042 := by decide +kernel

noncomputable def bx66 : SixW6.Box := (bx64).setLo (SixW6.axOf bits 48617) (SixW6.Box.mid bx64 (SixW6.axOf bits 48617))

noncomputable def bx67 : SixW6.Box := (bx66).setHi (SixW6.axOf bits 49042) (SixW6.Box.mid bx66 (SixW6.axOf bits 49042))

noncomputable def bx68 : SixW6.Box := (bx67).setHi (SixW6.axOf bits 49046) (SixW6.Box.mid bx67 (SixW6.axOf bits 49046))

theorem wk68 : SixW6.walk table bits 52 49050 bx68 = some 51106 := by decide +kernel

noncomputable def bx69 : SixW6.Box := (bx67).setLo (SixW6.axOf bits 49046) (SixW6.Box.mid bx67 (SixW6.axOf bits 49046))

theorem wk69 : SixW6.walk table bits 52 51106 bx69 = some 55967 := by decide +kernel

theorem wk67 : SixW6.walk table bits 53 49046 bx67 = some 55967 :=
  SixW6.walk_split table bits 52 49046 bx67 51106 55967 (by decide +kernel) wk68 wk69

noncomputable def bx70 : SixW6.Box := (bx66).setLo (SixW6.axOf bits 49042) (SixW6.Box.mid bx66 (SixW6.axOf bits 49042))

theorem wk70 : SixW6.walk table bits 53 55967 bx70 = some 57423 := by decide +kernel

theorem wk66 : SixW6.walk table bits 54 49042 bx66 = some 57423 :=
  SixW6.walk_split table bits 53 49042 bx66 55967 57423 (by decide +kernel) wk67 wk70

theorem wk64 : SixW6.walk table bits 55 48617 bx64 = some 57423 :=
  SixW6.walk_split table bits 54 48617 bx64 49042 57423 (by decide +kernel) wk65 wk66

noncomputable def bx71 : SixW6.Box := (bx63).setLo (SixW6.axOf bits 48613) (SixW6.Box.mid bx63 (SixW6.axOf bits 48613))

theorem wk71 : SixW6.walk table bits 55 57423 bx71 = some 57684 := by decide +kernel

theorem wk63 : SixW6.walk table bits 56 48613 bx63 = some 57684 :=
  SixW6.walk_split table bits 55 48613 bx63 57423 57684 (by decide +kernel) wk64 wk71

theorem wk61 : SixW6.walk table bits 57 48443 bx61 = some 57684 :=
  SixW6.walk_split table bits 56 48443 bx61 48613 57684 (by decide +kernel) wk62 wk63

noncomputable def bx72 : SixW6.Box := (bx60).setLo (SixW6.axOf bits 48439) (SixW6.Box.mid bx60 (SixW6.axOf bits 48439))

theorem wk72 : SixW6.walk table bits 57 57684 bx72 = some 57785 := by decide +kernel

theorem wk60 : SixW6.walk table bits 58 48439 bx60 = some 57785 :=
  SixW6.walk_split table bits 57 48439 bx60 57684 57785 (by decide +kernel) wk61 wk72

theorem wk58 : SixW6.walk table bits 59 47909 bx58 = some 57785 :=
  SixW6.walk_split table bits 58 47909 bx58 48439 57785 (by decide +kernel) wk59 wk60

noncomputable def bx73 : SixW6.Box := (bx57).setLo (SixW6.axOf bits 47905) (SixW6.Box.mid bx57 (SixW6.axOf bits 47905))

theorem wk73 : SixW6.walk table bits 59 57785 bx73 = some 57806 := by decide +kernel

theorem wk57 : SixW6.walk table bits 60 47905 bx57 = some 57806 :=
  SixW6.walk_split table bits 59 47905 bx57 57785 57806 (by decide +kernel) wk58 wk73

noncomputable def bx74 : SixW6.Box := (bx56).setLo (SixW6.axOf bits 47901) (SixW6.Box.mid bx56 (SixW6.axOf bits 47901))

theorem wk74 : SixW6.walk table bits 60 57806 bx74 = some 59907 := by decide +kernel

theorem wk56 : SixW6.walk table bits 61 47901 bx56 = some 59907 :=
  SixW6.walk_split table bits 60 47901 bx56 57806 59907 (by decide +kernel) wk57 wk74

noncomputable def bx75 : SixW6.Box := (bx55).setLo (SixW6.axOf bits 47897) (SixW6.Box.mid bx55 (SixW6.axOf bits 47897))

theorem wk75 : SixW6.walk table bits 61 59907 bx75 = some 60818 := by decide +kernel

theorem wk55 : SixW6.walk table bits 62 47897 bx55 = some 60818 :=
  SixW6.walk_split table bits 61 47897 bx55 59907 60818 (by decide +kernel) wk56 wk75

noncomputable def bx76 : SixW6.Box := (bx54).setLo (SixW6.axOf bits 47893) (SixW6.Box.mid bx54 (SixW6.axOf bits 47893))

theorem wk76 : SixW6.walk table bits 62 60818 bx76 = some 61064 := by decide +kernel

theorem wk54 : SixW6.walk table bits 63 47893 bx54 = some 61064 :=
  SixW6.walk_split table bits 62 47893 bx54 60818 61064 (by decide +kernel) wk55 wk76

noncomputable def bx77 : SixW6.Box := (bx53).setLo (SixW6.axOf bits 47889) (SixW6.Box.mid bx53 (SixW6.axOf bits 47889))

theorem wk77 : SixW6.walk table bits 63 61064 bx77 = some 61065 := by decide +kernel

theorem wk53 : SixW6.walk table bits 64 47889 bx53 = some 61065 :=
  SixW6.walk_split table bits 63 47889 bx53 61064 61065 (by decide +kernel) wk54 wk77

noncomputable def bx78 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 59904 74752 30720 40448)

noncomputable def bx79 : SixW6.Box := (bx78).setHi (SixW6.axOf bits 61065) (SixW6.Box.mid bx78 (SixW6.axOf bits 61065))

noncomputable def bx80 : SixW6.Box := (bx79).setHi (SixW6.axOf bits 61069) (SixW6.Box.mid bx79 (SixW6.axOf bits 61069))

theorem wk80 : SixW6.walk table bits 62 61073 bx80 = some 61169 := by decide +kernel

noncomputable def bx81 : SixW6.Box := (bx79).setLo (SixW6.axOf bits 61069) (SixW6.Box.mid bx79 (SixW6.axOf bits 61069))

noncomputable def bx82 : SixW6.Box := (bx81).setHi (SixW6.axOf bits 61169) (SixW6.Box.mid bx81 (SixW6.axOf bits 61169))

noncomputable def bx83 : SixW6.Box := (bx82).setHi (SixW6.axOf bits 61173) (SixW6.Box.mid bx82 (SixW6.axOf bits 61173))

theorem wk83 : SixW6.walk table bits 60 61177 bx83 = some 61248 := by decide +kernel

noncomputable def bx84 : SixW6.Box := (bx82).setLo (SixW6.axOf bits 61173) (SixW6.Box.mid bx82 (SixW6.axOf bits 61173))

noncomputable def bx85 : SixW6.Box := (bx84).setHi (SixW6.axOf bits 61248) (SixW6.Box.mid bx84 (SixW6.axOf bits 61248))

noncomputable def bx86 : SixW6.Box := (bx85).setHi (SixW6.axOf bits 61252) (SixW6.Box.mid bx85 (SixW6.axOf bits 61252))

theorem wk86 : SixW6.walk table bits 58 61256 bx86 = some 61657 := by decide +kernel

noncomputable def bx87 : SixW6.Box := (bx85).setLo (SixW6.axOf bits 61252) (SixW6.Box.mid bx85 (SixW6.axOf bits 61252))

noncomputable def bx88 : SixW6.Box := (bx87).setHi (SixW6.axOf bits 61657) (SixW6.Box.mid bx87 (SixW6.axOf bits 61657))

noncomputable def bx89 : SixW6.Box := (bx88).setHi (SixW6.axOf bits 61661) (SixW6.Box.mid bx88 (SixW6.axOf bits 61661))

theorem wk89 : SixW6.walk table bits 56 61665 bx89 = some 61996 := by decide +kernel

noncomputable def bx90 : SixW6.Box := (bx88).setLo (SixW6.axOf bits 61661) (SixW6.Box.mid bx88 (SixW6.axOf bits 61661))

noncomputable def bx91 : SixW6.Box := (bx90).setHi (SixW6.axOf bits 61996) (SixW6.Box.mid bx90 (SixW6.axOf bits 61996))

noncomputable def bx92 : SixW6.Box := (bx91).setHi (SixW6.axOf bits 62000) (SixW6.Box.mid bx91 (SixW6.axOf bits 62000))

theorem wk92 : SixW6.walk table bits 54 62004 bx92 = some 64695 := by decide +kernel

noncomputable def bx93 : SixW6.Box := (bx91).setLo (SixW6.axOf bits 62000) (SixW6.Box.mid bx91 (SixW6.axOf bits 62000))

noncomputable def bx94 : SixW6.Box := (bx93).setHi (SixW6.axOf bits 64695) (SixW6.Box.mid bx93 (SixW6.axOf bits 64695))

noncomputable def bx95 : SixW6.Box := (bx94).setHi (SixW6.axOf bits 64699) (SixW6.Box.mid bx94 (SixW6.axOf bits 64699))

theorem wk95 : SixW6.walk table bits 52 64703 bx95 = some 64724 := by decide +kernel

noncomputable def bx96 : SixW6.Box := (bx94).setLo (SixW6.axOf bits 64699) (SixW6.Box.mid bx94 (SixW6.axOf bits 64699))

noncomputable def bx97 : SixW6.Box := (bx96).setHi (SixW6.axOf bits 64724) (SixW6.Box.mid bx96 (SixW6.axOf bits 64724))

noncomputable def bx98 : SixW6.Box := (bx97).setHi (SixW6.axOf bits 64728) (SixW6.Box.mid bx97 (SixW6.axOf bits 64728))

theorem wk98 : SixW6.walk table bits 50 64732 bx98 = some 66273 := by decide +kernel

noncomputable def bx99 : SixW6.Box := (bx97).setLo (SixW6.axOf bits 64728) (SixW6.Box.mid bx97 (SixW6.axOf bits 64728))

noncomputable def bx100 : SixW6.Box := (bx99).setHi (SixW6.axOf bits 66273) (SixW6.Box.mid bx99 (SixW6.axOf bits 66273))

noncomputable def bx101 : SixW6.Box := (bx100).setHi (SixW6.axOf bits 66277) (SixW6.Box.mid bx100 (SixW6.axOf bits 66277))

theorem wk101 : SixW6.walk table bits 48 66281 bx101 = some 68602 := by decide +kernel

noncomputable def bx102 : SixW6.Box := (bx100).setLo (SixW6.axOf bits 66277) (SixW6.Box.mid bx100 (SixW6.axOf bits 66277))

theorem wk102 : SixW6.walk table bits 48 68602 bx102 = some 71473 := by decide +kernel

theorem wk100 : SixW6.walk table bits 49 66277 bx100 = some 71473 :=
  SixW6.walk_split table bits 48 66277 bx100 68602 71473 (by decide +kernel) wk101 wk102

noncomputable def bx103 : SixW6.Box := (bx99).setLo (SixW6.axOf bits 66273) (SixW6.Box.mid bx99 (SixW6.axOf bits 66273))

noncomputable def bx104 : SixW6.Box := (bx103).setHi (SixW6.axOf bits 71473) (SixW6.Box.mid bx103 (SixW6.axOf bits 71473))

theorem wk104 : SixW6.walk table bits 48 71477 bx104 = some 74528 := by decide +kernel

noncomputable def bx105 : SixW6.Box := (bx103).setLo (SixW6.axOf bits 71473) (SixW6.Box.mid bx103 (SixW6.axOf bits 71473))

theorem wk105 : SixW6.walk table bits 48 74528 bx105 = some 77594 := by decide +kernel

theorem wk103 : SixW6.walk table bits 49 71473 bx103 = some 77594 :=
  SixW6.walk_split table bits 48 71473 bx103 74528 77594 (by decide +kernel) wk104 wk105

theorem wk99 : SixW6.walk table bits 50 66273 bx99 = some 77594 :=
  SixW6.walk_split table bits 49 66273 bx99 71473 77594 (by decide +kernel) wk100 wk103

theorem wk97 : SixW6.walk table bits 51 64728 bx97 = some 77594 :=
  SixW6.walk_split table bits 50 64728 bx97 66273 77594 (by decide +kernel) wk98 wk99

noncomputable def bx106 : SixW6.Box := (bx96).setLo (SixW6.axOf bits 64724) (SixW6.Box.mid bx96 (SixW6.axOf bits 64724))

theorem wk106 : SixW6.walk table bits 51 77594 bx106 = some 80580 := by decide +kernel

theorem wk96 : SixW6.walk table bits 52 64724 bx96 = some 80580 :=
  SixW6.walk_split table bits 51 64724 bx96 77594 80580 (by decide +kernel) wk97 wk106

theorem wk94 : SixW6.walk table bits 53 64699 bx94 = some 80580 :=
  SixW6.walk_split table bits 52 64699 bx94 64724 80580 (by decide +kernel) wk95 wk96

noncomputable def bx107 : SixW6.Box := (bx93).setLo (SixW6.axOf bits 64695) (SixW6.Box.mid bx93 (SixW6.axOf bits 64695))

theorem wk107 : SixW6.walk table bits 53 80580 bx107 = some 80836 := by decide +kernel

theorem wk93 : SixW6.walk table bits 54 64695 bx93 = some 80836 :=
  SixW6.walk_split table bits 53 64695 bx93 80580 80836 (by decide +kernel) wk94 wk107

theorem wk91 : SixW6.walk table bits 55 62000 bx91 = some 80836 :=
  SixW6.walk_split table bits 54 62000 bx91 64695 80836 (by decide +kernel) wk92 wk93

noncomputable def bx108 : SixW6.Box := (bx90).setLo (SixW6.axOf bits 61996) (SixW6.Box.mid bx90 (SixW6.axOf bits 61996))

noncomputable def bx109 : SixW6.Box := (bx108).setHi (SixW6.axOf bits 80836) (SixW6.Box.mid bx108 (SixW6.axOf bits 80836))

noncomputable def bx110 : SixW6.Box := (bx109).setHi (SixW6.axOf bits 80840) (SixW6.Box.mid bx109 (SixW6.axOf bits 80840))

theorem wk110 : SixW6.walk table bits 53 80844 bx110 = some 80890 := by decide +kernel

noncomputable def bx111 : SixW6.Box := (bx109).setLo (SixW6.axOf bits 80840) (SixW6.Box.mid bx109 (SixW6.axOf bits 80840))

noncomputable def bx112 : SixW6.Box := (bx111).setHi (SixW6.axOf bits 80890) (SixW6.Box.mid bx111 (SixW6.axOf bits 80890))

theorem wk112 : SixW6.walk table bits 52 80894 bx112 = some 85095 := by decide +kernel

noncomputable def bx113 : SixW6.Box := (bx111).setLo (SixW6.axOf bits 80890) (SixW6.Box.mid bx111 (SixW6.axOf bits 80890))

theorem wk113 : SixW6.walk table bits 52 85095 bx113 = some 86021 := by decide +kernel

theorem wk111 : SixW6.walk table bits 53 80890 bx111 = some 86021 :=
  SixW6.walk_split table bits 52 80890 bx111 85095 86021 (by decide +kernel) wk112 wk113

theorem wk109 : SixW6.walk table bits 54 80840 bx109 = some 86021 :=
  SixW6.walk_split table bits 53 80840 bx109 80890 86021 (by decide +kernel) wk110 wk111

noncomputable def bx114 : SixW6.Box := (bx108).setLo (SixW6.axOf bits 80836) (SixW6.Box.mid bx108 (SixW6.axOf bits 80836))

theorem wk114 : SixW6.walk table bits 54 86021 bx114 = some 86117 := by decide +kernel

theorem wk108 : SixW6.walk table bits 55 80836 bx108 = some 86117 :=
  SixW6.walk_split table bits 54 80836 bx108 86021 86117 (by decide +kernel) wk109 wk114

theorem wk90 : SixW6.walk table bits 56 61996 bx90 = some 86117 :=
  SixW6.walk_split table bits 55 61996 bx90 80836 86117 (by decide +kernel) wk91 wk108

theorem wk88 : SixW6.walk table bits 57 61661 bx88 = some 86117 :=
  SixW6.walk_split table bits 56 61661 bx88 61996 86117 (by decide +kernel) wk89 wk90

noncomputable def bx115 : SixW6.Box := (bx87).setLo (SixW6.axOf bits 61657) (SixW6.Box.mid bx87 (SixW6.axOf bits 61657))

theorem wk115 : SixW6.walk table bits 57 86117 bx115 = some 86313 := by decide +kernel

theorem wk87 : SixW6.walk table bits 58 61657 bx87 = some 86313 :=
  SixW6.walk_split table bits 57 61657 bx87 86117 86313 (by decide +kernel) wk88 wk115

theorem wk85 : SixW6.walk table bits 59 61252 bx85 = some 86313 :=
  SixW6.walk_split table bits 58 61252 bx85 61657 86313 (by decide +kernel) wk86 wk87

noncomputable def bx116 : SixW6.Box := (bx84).setLo (SixW6.axOf bits 61248) (SixW6.Box.mid bx84 (SixW6.axOf bits 61248))

theorem wk116 : SixW6.walk table bits 59 86313 bx116 = some 86554 := by decide +kernel

theorem wk84 : SixW6.walk table bits 60 61248 bx84 = some 86554 :=
  SixW6.walk_split table bits 59 61248 bx84 86313 86554 (by decide +kernel) wk85 wk116

theorem wk82 : SixW6.walk table bits 61 61173 bx82 = some 86554 :=
  SixW6.walk_split table bits 60 61173 bx82 61248 86554 (by decide +kernel) wk83 wk84

noncomputable def bx117 : SixW6.Box := (bx81).setLo (SixW6.axOf bits 61169) (SixW6.Box.mid bx81 (SixW6.axOf bits 61169))

theorem wk117 : SixW6.walk table bits 61 86554 bx117 = some 86670 := by decide +kernel

theorem wk81 : SixW6.walk table bits 62 61169 bx81 = some 86670 :=
  SixW6.walk_split table bits 61 61169 bx81 86554 86670 (by decide +kernel) wk82 wk117

theorem wk79 : SixW6.walk table bits 63 61069 bx79 = some 86670 :=
  SixW6.walk_split table bits 62 61069 bx79 61169 86670 (by decide +kernel) wk80 wk81

noncomputable def bx118 : SixW6.Box := (bx78).setLo (SixW6.axOf bits 61065) (SixW6.Box.mid bx78 (SixW6.axOf bits 61065))

theorem wk118 : SixW6.walk table bits 63 86670 bx118 = some 86831 := by decide +kernel

theorem wk78 : SixW6.walk table bits 64 61065 bx78 = some 86831 :=
  SixW6.walk_split table bits 63 61065 bx78 86670 86831 (by decide +kernel) wk79 wk118

noncomputable def bx119 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 59904 74752 57344 450560)

noncomputable def bx120 : SixW6.Box := (bx119).setHi (SixW6.axOf bits 86831) (SixW6.Box.mid bx119 (SixW6.axOf bits 86831))

noncomputable def bx121 : SixW6.Box := (bx120).setHi (SixW6.axOf bits 86835) (SixW6.Box.mid bx120 (SixW6.axOf bits 86835))

noncomputable def bx122 : SixW6.Box := (bx121).setHi (SixW6.axOf bits 86839) (SixW6.Box.mid bx121 (SixW6.axOf bits 86839))

noncomputable def bx123 : SixW6.Box := (bx122).setHi (SixW6.axOf bits 86843) (SixW6.Box.mid bx122 (SixW6.axOf bits 86843))

noncomputable def bx124 : SixW6.Box := (bx123).setHi (SixW6.axOf bits 86847) (SixW6.Box.mid bx123 (SixW6.axOf bits 86847))

noncomputable def bx125 : SixW6.Box := (bx124).setHi (SixW6.axOf bits 86851) (SixW6.Box.mid bx124 (SixW6.axOf bits 86851))

theorem wk125 : SixW6.walk table bits 58 86855 bx125 = some 87011 := by decide +kernel

noncomputable def bx126 : SixW6.Box := (bx124).setLo (SixW6.axOf bits 86851) (SixW6.Box.mid bx124 (SixW6.axOf bits 86851))

noncomputable def bx127 : SixW6.Box := (bx126).setHi (SixW6.axOf bits 87011) (SixW6.Box.mid bx126 (SixW6.axOf bits 87011))

noncomputable def bx128 : SixW6.Box := (bx127).setHi (SixW6.axOf bits 87015) (SixW6.Box.mid bx127 (SixW6.axOf bits 87015))

theorem wk128 : SixW6.walk table bits 56 87019 bx128 = some 87025 := by decide +kernel

noncomputable def bx129 : SixW6.Box := (bx127).setLo (SixW6.axOf bits 87015) (SixW6.Box.mid bx127 (SixW6.axOf bits 87015))

noncomputable def bx130 : SixW6.Box := (bx129).setHi (SixW6.axOf bits 87025) (SixW6.Box.mid bx129 (SixW6.axOf bits 87025))

noncomputable def bx131 : SixW6.Box := (bx130).setHi (SixW6.axOf bits 87029) (SixW6.Box.mid bx130 (SixW6.axOf bits 87029))

theorem wk131 : SixW6.walk table bits 54 87033 bx131 = some 87039 := by decide +kernel

noncomputable def bx132 : SixW6.Box := (bx130).setLo (SixW6.axOf bits 87029) (SixW6.Box.mid bx130 (SixW6.axOf bits 87029))

noncomputable def bx133 : SixW6.Box := (bx132).setHi (SixW6.axOf bits 87039) (SixW6.Box.mid bx132 (SixW6.axOf bits 87039))

noncomputable def bx134 : SixW6.Box := (bx133).setHi (SixW6.axOf bits 87043) (SixW6.Box.mid bx133 (SixW6.axOf bits 87043))

theorem wk134 : SixW6.walk table bits 52 87047 bx134 = some 87088 := by decide +kernel

noncomputable def bx135 : SixW6.Box := (bx133).setLo (SixW6.axOf bits 87043) (SixW6.Box.mid bx133 (SixW6.axOf bits 87043))

noncomputable def bx136 : SixW6.Box := (bx135).setHi (SixW6.axOf bits 87088) (SixW6.Box.mid bx135 (SixW6.axOf bits 87088))

noncomputable def bx137 : SixW6.Box := (bx136).setHi (SixW6.axOf bits 87092) (SixW6.Box.mid bx136 (SixW6.axOf bits 87092))

theorem wk137 : SixW6.walk table bits 50 87096 bx137 = some 87627 := by decide +kernel

noncomputable def bx138 : SixW6.Box := (bx136).setLo (SixW6.axOf bits 87092) (SixW6.Box.mid bx136 (SixW6.axOf bits 87092))

noncomputable def bx139 : SixW6.Box := (bx138).setHi (SixW6.axOf bits 87627) (SixW6.Box.mid bx138 (SixW6.axOf bits 87627))

noncomputable def bx140 : SixW6.Box := (bx139).setHi (SixW6.axOf bits 87631) (SixW6.Box.mid bx139 (SixW6.axOf bits 87631))

theorem wk140 : SixW6.walk table bits 48 87635 bx140 = some 87636 := by decide +kernel

noncomputable def bx141 : SixW6.Box := (bx139).setLo (SixW6.axOf bits 87631) (SixW6.Box.mid bx139 (SixW6.axOf bits 87631))

noncomputable def bx142 : SixW6.Box := (bx141).setHi (SixW6.axOf bits 87636) (SixW6.Box.mid bx141 (SixW6.axOf bits 87636))

theorem wk142 : SixW6.walk table bits 47 87640 bx142 = some 90501 := by decide +kernel

noncomputable def bx143 : SixW6.Box := (bx141).setLo (SixW6.axOf bits 87636) (SixW6.Box.mid bx141 (SixW6.axOf bits 87636))

theorem wk143 : SixW6.walk table bits 47 90501 bx143 = some 93747 := by decide +kernel

theorem wk141 : SixW6.walk table bits 48 87636 bx141 = some 93747 :=
  SixW6.walk_split table bits 47 87636 bx141 90501 93747 (by decide +kernel) wk142 wk143

theorem wk139 : SixW6.walk table bits 49 87631 bx139 = some 93747 :=
  SixW6.walk_split table bits 48 87631 bx139 87636 93747 (by decide +kernel) wk140 wk141

noncomputable def bx144 : SixW6.Box := (bx138).setLo (SixW6.axOf bits 87627) (SixW6.Box.mid bx138 (SixW6.axOf bits 87627))

theorem wk144 : SixW6.walk table bits 49 93747 bx144 = some 93893 := by decide +kernel

theorem wk138 : SixW6.walk table bits 50 87627 bx138 = some 93893 :=
  SixW6.walk_split table bits 49 87627 bx138 93747 93893 (by decide +kernel) wk139 wk144

theorem wk136 : SixW6.walk table bits 51 87092 bx136 = some 93893 :=
  SixW6.walk_split table bits 50 87092 bx136 87627 93893 (by decide +kernel) wk137 wk138

noncomputable def bx145 : SixW6.Box := (bx135).setLo (SixW6.axOf bits 87088) (SixW6.Box.mid bx135 (SixW6.axOf bits 87088))

theorem wk145 : SixW6.walk table bits 51 93893 bx145 = some 96934 := by decide +kernel

theorem wk135 : SixW6.walk table bits 52 87088 bx135 = some 96934 :=
  SixW6.walk_split table bits 51 87088 bx135 93893 96934 (by decide +kernel) wk136 wk145

theorem wk133 : SixW6.walk table bits 53 87043 bx133 = some 96934 :=
  SixW6.walk_split table bits 52 87043 bx133 87088 96934 (by decide +kernel) wk134 wk135

noncomputable def bx146 : SixW6.Box := (bx132).setLo (SixW6.axOf bits 87039) (SixW6.Box.mid bx132 (SixW6.axOf bits 87039))

theorem wk146 : SixW6.walk table bits 53 96934 bx146 = some 97020 := by decide +kernel

theorem wk132 : SixW6.walk table bits 54 87039 bx132 = some 97020 :=
  SixW6.walk_split table bits 53 87039 bx132 96934 97020 (by decide +kernel) wk133 wk146

theorem wk130 : SixW6.walk table bits 55 87029 bx130 = some 97020 :=
  SixW6.walk_split table bits 54 87029 bx130 87039 97020 (by decide +kernel) wk131 wk132

noncomputable def bx147 : SixW6.Box := (bx129).setLo (SixW6.axOf bits 87025) (SixW6.Box.mid bx129 (SixW6.axOf bits 87025))

theorem wk147 : SixW6.walk table bits 55 97020 bx147 = some 97131 := by decide +kernel

theorem wk129 : SixW6.walk table bits 56 87025 bx129 = some 97131 :=
  SixW6.walk_split table bits 55 87025 bx129 97020 97131 (by decide +kernel) wk130 wk147

theorem wk127 : SixW6.walk table bits 57 87015 bx127 = some 97131 :=
  SixW6.walk_split table bits 56 87015 bx127 87025 97131 (by decide +kernel) wk128 wk129

noncomputable def bx148 : SixW6.Box := (bx126).setLo (SixW6.axOf bits 87011) (SixW6.Box.mid bx126 (SixW6.axOf bits 87011))

theorem wk148 : SixW6.walk table bits 57 97131 bx148 = some 97207 := by decide +kernel

theorem wk126 : SixW6.walk table bits 58 87011 bx126 = some 97207 :=
  SixW6.walk_split table bits 57 87011 bx126 97131 97207 (by decide +kernel) wk127 wk148

theorem wk124 : SixW6.walk table bits 59 86851 bx124 = some 97207 :=
  SixW6.walk_split table bits 58 86851 bx124 87011 97207 (by decide +kernel) wk125 wk126

noncomputable def bx149 : SixW6.Box := (bx123).setLo (SixW6.axOf bits 86847) (SixW6.Box.mid bx123 (SixW6.axOf bits 86847))

theorem wk149 : SixW6.walk table bits 59 97207 bx149 = some 97253 := by decide +kernel

theorem wk123 : SixW6.walk table bits 60 86847 bx123 = some 97253 :=
  SixW6.walk_split table bits 59 86847 bx123 97207 97253 (by decide +kernel) wk124 wk149

noncomputable def bx150 : SixW6.Box := (bx122).setLo (SixW6.axOf bits 86843) (SixW6.Box.mid bx122 (SixW6.axOf bits 86843))

theorem wk150 : SixW6.walk table bits 60 97253 bx150 = some 97929 := by decide +kernel

theorem wk122 : SixW6.walk table bits 61 86843 bx122 = some 97929 :=
  SixW6.walk_split table bits 60 86843 bx122 97253 97929 (by decide +kernel) wk123 wk150

noncomputable def bx151 : SixW6.Box := (bx121).setLo (SixW6.axOf bits 86839) (SixW6.Box.mid bx121 (SixW6.axOf bits 86839))

theorem wk151 : SixW6.walk table bits 61 97929 bx151 = some 98085 := by decide +kernel

theorem wk121 : SixW6.walk table bits 62 86839 bx121 = some 98085 :=
  SixW6.walk_split table bits 61 86839 bx121 97929 98085 (by decide +kernel) wk122 wk151

noncomputable def bx152 : SixW6.Box := (bx120).setLo (SixW6.axOf bits 86835) (SixW6.Box.mid bx120 (SixW6.axOf bits 86835))

theorem wk152 : SixW6.walk table bits 62 98085 bx152 = some 98086 := by decide +kernel

theorem wk120 : SixW6.walk table bits 63 86835 bx120 = some 98086 :=
  SixW6.walk_split table bits 62 86835 bx120 98085 98086 (by decide +kernel) wk121 wk152

noncomputable def bx153 : SixW6.Box := (bx119).setLo (SixW6.axOf bits 86831) (SixW6.Box.mid bx119 (SixW6.axOf bits 86831))

theorem wk153 : SixW6.walk table bits 63 98086 bx153 = some 98087 := by decide +kernel

theorem wk119 : SixW6.walk table bits 64 86831 bx119 = some 98087 :=
  SixW6.walk_split table bits 63 86831 bx119 98086 98087 (by decide +kernel) wk120 wk153

noncomputable def bx154 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 88064 270336 30720 40448)

theorem wk154 : SixW6.walk table bits 64 98087 bx154 = some 99358 := by decide +kernel

noncomputable def bx155 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 31744 38400 88064 270336 57344 450560)

theorem wk155 : SixW6.walk table bits 64 99358 bx155 = some 99614 := by decide +kernel

noncomputable def bx156 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 31744 38400 30720 40448)

theorem wk156 : SixW6.walk table bits 64 99614 bx156 = some 103955 := by decide +kernel

noncomputable def bx157 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 31744 38400 57344 450560)

noncomputable def bx158 : SixW6.Box := (bx157).setHi (SixW6.axOf bits 103955) (SixW6.Box.mid bx157 (SixW6.axOf bits 103955))

noncomputable def bx159 : SixW6.Box := (bx158).setHi (SixW6.axOf bits 103959) (SixW6.Box.mid bx158 (SixW6.axOf bits 103959))

noncomputable def bx160 : SixW6.Box := (bx159).setHi (SixW6.axOf bits 103963) (SixW6.Box.mid bx159 (SixW6.axOf bits 103963))

noncomputable def bx161 : SixW6.Box := (bx160).setHi (SixW6.axOf bits 103967) (SixW6.Box.mid bx160 (SixW6.axOf bits 103967))

noncomputable def bx162 : SixW6.Box := (bx161).setHi (SixW6.axOf bits 103971) (SixW6.Box.mid bx161 (SixW6.axOf bits 103971))

noncomputable def bx163 : SixW6.Box := (bx162).setHi (SixW6.axOf bits 103975) (SixW6.Box.mid bx162 (SixW6.axOf bits 103975))

theorem wk163 : SixW6.walk table bits 58 103979 bx163 = some 104135 := by decide +kernel

noncomputable def bx164 : SixW6.Box := (bx162).setLo (SixW6.axOf bits 103975) (SixW6.Box.mid bx162 (SixW6.axOf bits 103975))

noncomputable def bx165 : SixW6.Box := (bx164).setHi (SixW6.axOf bits 104135) (SixW6.Box.mid bx164 (SixW6.axOf bits 104135))

noncomputable def bx166 : SixW6.Box := (bx165).setHi (SixW6.axOf bits 104139) (SixW6.Box.mid bx165 (SixW6.axOf bits 104139))

theorem wk166 : SixW6.walk table bits 56 104143 bx166 = some 104149 := by decide +kernel

noncomputable def bx167 : SixW6.Box := (bx165).setLo (SixW6.axOf bits 104139) (SixW6.Box.mid bx165 (SixW6.axOf bits 104139))

noncomputable def bx168 : SixW6.Box := (bx167).setHi (SixW6.axOf bits 104149) (SixW6.Box.mid bx167 (SixW6.axOf bits 104149))

noncomputable def bx169 : SixW6.Box := (bx168).setHi (SixW6.axOf bits 104153) (SixW6.Box.mid bx168 (SixW6.axOf bits 104153))

theorem wk169 : SixW6.walk table bits 54 104157 bx169 = some 104158 := by decide +kernel

noncomputable def bx170 : SixW6.Box := (bx168).setLo (SixW6.axOf bits 104153) (SixW6.Box.mid bx168 (SixW6.axOf bits 104153))

noncomputable def bx171 : SixW6.Box := (bx170).setHi (SixW6.axOf bits 104158) (SixW6.Box.mid bx170 (SixW6.axOf bits 104158))

noncomputable def bx172 : SixW6.Box := (bx171).setHi (SixW6.axOf bits 104162) (SixW6.Box.mid bx171 (SixW6.axOf bits 104162))

theorem wk172 : SixW6.walk table bits 52 104166 bx172 = some 104197 := by decide +kernel

noncomputable def bx173 : SixW6.Box := (bx171).setLo (SixW6.axOf bits 104162) (SixW6.Box.mid bx171 (SixW6.axOf bits 104162))

noncomputable def bx174 : SixW6.Box := (bx173).setHi (SixW6.axOf bits 104197) (SixW6.Box.mid bx173 (SixW6.axOf bits 104197))

theorem wk174 : SixW6.walk table bits 51 104201 bx174 = some 108572 := by decide +kernel

noncomputable def bx175 : SixW6.Box := (bx173).setLo (SixW6.axOf bits 104197) (SixW6.Box.mid bx173 (SixW6.axOf bits 104197))

theorem wk175 : SixW6.walk table bits 51 108572 bx175 = some 112458 := by decide +kernel

theorem wk173 : SixW6.walk table bits 52 104197 bx173 = some 112458 :=
  SixW6.walk_split table bits 51 104197 bx173 108572 112458 (by decide +kernel) wk174 wk175

theorem wk171 : SixW6.walk table bits 53 104162 bx171 = some 112458 :=
  SixW6.walk_split table bits 52 104162 bx171 104197 112458 (by decide +kernel) wk172 wk173

noncomputable def bx176 : SixW6.Box := (bx170).setLo (SixW6.axOf bits 104158) (SixW6.Box.mid bx170 (SixW6.axOf bits 104158))

theorem wk176 : SixW6.walk table bits 53 112458 bx176 = some 112544 := by decide +kernel

theorem wk170 : SixW6.walk table bits 54 104158 bx170 = some 112544 :=
  SixW6.walk_split table bits 53 104158 bx170 112458 112544 (by decide +kernel) wk171 wk176

theorem wk168 : SixW6.walk table bits 55 104153 bx168 = some 112544 :=
  SixW6.walk_split table bits 54 104153 bx168 104158 112544 (by decide +kernel) wk169 wk170

noncomputable def bx177 : SixW6.Box := (bx167).setLo (SixW6.axOf bits 104149) (SixW6.Box.mid bx167 (SixW6.axOf bits 104149))

theorem wk177 : SixW6.walk table bits 55 112544 bx177 = some 112615 := by decide +kernel

theorem wk167 : SixW6.walk table bits 56 104149 bx167 = some 112615 :=
  SixW6.walk_split table bits 55 104149 bx167 112544 112615 (by decide +kernel) wk168 wk177

theorem wk165 : SixW6.walk table bits 57 104139 bx165 = some 112615 :=
  SixW6.walk_split table bits 56 104139 bx165 104149 112615 (by decide +kernel) wk166 wk167

noncomputable def bx178 : SixW6.Box := (bx164).setLo (SixW6.axOf bits 104135) (SixW6.Box.mid bx164 (SixW6.axOf bits 104135))

theorem wk178 : SixW6.walk table bits 57 112615 bx178 = some 112721 := by decide +kernel

theorem wk164 : SixW6.walk table bits 58 104135 bx164 = some 112721 :=
  SixW6.walk_split table bits 57 104135 bx164 112615 112721 (by decide +kernel) wk165 wk178

theorem wk162 : SixW6.walk table bits 59 103975 bx162 = some 112721 :=
  SixW6.walk_split table bits 58 103975 bx162 104135 112721 (by decide +kernel) wk163 wk164

noncomputable def bx179 : SixW6.Box := (bx161).setLo (SixW6.axOf bits 103971) (SixW6.Box.mid bx161 (SixW6.axOf bits 103971))

theorem wk179 : SixW6.walk table bits 59 112721 bx179 = some 112742 := by decide +kernel

theorem wk161 : SixW6.walk table bits 60 103971 bx161 = some 112742 :=
  SixW6.walk_split table bits 59 103971 bx161 112721 112742 (by decide +kernel) wk162 wk179

noncomputable def bx180 : SixW6.Box := (bx160).setLo (SixW6.axOf bits 103967) (SixW6.Box.mid bx160 (SixW6.axOf bits 103967))

theorem wk180 : SixW6.walk table bits 60 112742 bx180 = some 113358 := by decide +kernel

theorem wk160 : SixW6.walk table bits 61 103967 bx160 = some 113358 :=
  SixW6.walk_split table bits 60 103967 bx160 112742 113358 (by decide +kernel) wk161 wk180

noncomputable def bx181 : SixW6.Box := (bx159).setLo (SixW6.axOf bits 103963) (SixW6.Box.mid bx159 (SixW6.axOf bits 103963))

theorem wk181 : SixW6.walk table bits 61 113358 bx181 = some 113464 := by decide +kernel

theorem wk159 : SixW6.walk table bits 62 103963 bx159 = some 113464 :=
  SixW6.walk_split table bits 61 103963 bx159 113358 113464 (by decide +kernel) wk160 wk181

noncomputable def bx182 : SixW6.Box := (bx158).setLo (SixW6.axOf bits 103959) (SixW6.Box.mid bx158 (SixW6.axOf bits 103959))

theorem wk182 : SixW6.walk table bits 62 113464 bx182 = some 113465 := by decide +kernel

theorem wk158 : SixW6.walk table bits 63 103959 bx158 = some 113465 :=
  SixW6.walk_split table bits 62 103959 bx158 113464 113465 (by decide +kernel) wk159 wk182

noncomputable def bx183 : SixW6.Box := (bx157).setLo (SixW6.axOf bits 103955) (SixW6.Box.mid bx157 (SixW6.axOf bits 103955))

theorem wk183 : SixW6.walk table bits 63 113465 bx183 = some 113466 := by decide +kernel

theorem wk157 : SixW6.walk table bits 64 103955 bx157 = some 113466 :=
  SixW6.walk_split table bits 63 103955 bx157 113465 113466 (by decide +kernel) wk158 wk183

noncomputable def bx184 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 59904 74752 30720 40448)

theorem wk184 : SixW6.walk table bits 64 113466 bx184 = some 115082 := by decide +kernel

noncomputable def bx185 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 59904 74752 57344 450560)

theorem wk185 : SixW6.walk table bits 64 115082 bx185 = some 115263 := by decide +kernel

noncomputable def bx186 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 88064 270336 30720 40448)

theorem wk186 : SixW6.walk table bits 64 115263 bx186 = some 115304 := by decide +kernel

noncomputable def bx187 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 60416 74240 88064 270336 57344 450560)

theorem wk187 : SixW6.walk table bits 64 115304 bx187 = some 115305 := by decide +kernel

noncomputable def bx188 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 31744 38400 30720 40448)

theorem wk188 : SixW6.walk table bits 64 115305 bx188 = some 115681 := by decide +kernel

noncomputable def bx189 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 31744 38400 57344 450560)

theorem wk189 : SixW6.walk table bits 64 115681 bx189 = some 115827 := by decide +kernel

noncomputable def bx190 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 59904 74752 30720 40448)

theorem wk190 : SixW6.walk table bits 64 115827 bx190 = some 115863 := by decide +kernel

noncomputable def bx191 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 59904 74752 57344 450560)

theorem wk191 : SixW6.walk table bits 64 115863 bx191 = some 115864 := by decide +kernel

noncomputable def bx192 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 88064 270336 30720 40448)

theorem wk192 : SixW6.walk table bits 64 115864 bx192 = some 115865 := by decide +kernel

noncomputable def bx193 : SixW6.Box := (SixW6.Box.mk 30720 40448 59904 74752 88576 245760 88064 270336 57344 450560)

theorem wk193 : SixW6.walk table bits 64 115865 bx193 = some 115866 := by decide +kernel

noncomputable def bx194 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 31744 38400 30720 40448)

theorem wk194 : SixW6.walk table bits 64 115866 bx194 = some 117397 := by decide +kernel

noncomputable def bx195 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 31744 38400 57344 450560)

theorem wk195 : SixW6.walk table bits 64 117397 bx195 = some 119628 := by decide +kernel

noncomputable def bx196 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 59904 74752 30720 40448)

theorem wk196 : SixW6.walk table bits 64 119628 bx196 = some 120899 := by decide +kernel

noncomputable def bx197 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 59904 74752 57344 450560)

theorem wk197 : SixW6.walk table bits 64 120899 bx197 = some 121180 := by decide +kernel

noncomputable def bx198 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 88064 270336 30720 40448)

theorem wk198 : SixW6.walk table bits 64 121180 bx198 = some 121266 := by decide +kernel

noncomputable def bx199 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 31744 38400 88064 270336 57344 450560)

theorem wk199 : SixW6.walk table bits 64 121266 bx199 = some 121267 := by decide +kernel

noncomputable def bx200 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 31744 38400 30720 40448)

theorem wk200 : SixW6.walk table bits 64 121267 bx200 = some 121643 := by decide +kernel

noncomputable def bx201 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 31744 38400 57344 450560)

theorem wk201 : SixW6.walk table bits 64 121643 bx201 = some 121824 := by decide +kernel

noncomputable def bx202 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 59904 74752 30720 40448)

theorem wk202 : SixW6.walk table bits 64 121824 bx202 = some 121865 := by decide +kernel

noncomputable def bx203 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 59904 74752 57344 450560)

theorem wk203 : SixW6.walk table bits 64 121865 bx203 = some 121866 := by decide +kernel

noncomputable def bx204 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 88064 270336 30720 40448)

theorem wk204 : SixW6.walk table bits 64 121866 bx204 = some 121867 := by decide +kernel

noncomputable def bx205 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 60416 74240 88064 270336 57344 450560)

theorem wk205 : SixW6.walk table bits 64 121867 bx205 = some 121868 := by decide +kernel

noncomputable def bx206 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 31744 38400 30720 40448)

theorem wk206 : SixW6.walk table bits 64 121868 bx206 = some 121924 := by decide +kernel

noncomputable def bx207 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 31744 38400 57344 450560)

theorem wk207 : SixW6.walk table bits 64 121924 bx207 = some 121925 := by decide +kernel

noncomputable def bx208 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 59904 74752 30720 40448)

theorem wk208 : SixW6.walk table bits 64 121925 bx208 = some 121926 := by decide +kernel

noncomputable def bx209 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 59904 74752 57344 450560)

theorem wk209 : SixW6.walk table bits 64 121926 bx209 = some 121927 := by decide +kernel

noncomputable def bx210 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 88064 270336 30720 40448)

theorem wk210 : SixW6.walk table bits 64 121927 bx210 = some 121928 := by decide +kernel

noncomputable def bx211 : SixW6.Box := (SixW6.Box.mk 30720 40448 88064 270336 88576 245760 88064 270336 57344 450560)

theorem wk211 : SixW6.walk table bits 64 121928 bx211 = some 121929 := by decide +kernel

noncomputable def bx212 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 31744 38400 30720 40448)

theorem wk212 : SixW6.walk table bits 64 121929 bx212 = some 121930 := by decide +kernel

noncomputable def bx213 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 31744 38400 57344 450560)

noncomputable def bx214 : SixW6.Box := (bx213).setHi (SixW6.axOf bits 121930) (SixW6.Box.mid bx213 (SixW6.axOf bits 121930))

noncomputable def bx215 : SixW6.Box := (bx214).setHi (SixW6.axOf bits 121934) (SixW6.Box.mid bx214 (SixW6.axOf bits 121934))

noncomputable def bx216 : SixW6.Box := (bx215).setHi (SixW6.axOf bits 121938) (SixW6.Box.mid bx215 (SixW6.axOf bits 121938))

noncomputable def bx217 : SixW6.Box := (bx216).setHi (SixW6.axOf bits 121942) (SixW6.Box.mid bx216 (SixW6.axOf bits 121942))

noncomputable def bx218 : SixW6.Box := (bx217).setHi (SixW6.axOf bits 121946) (SixW6.Box.mid bx217 (SixW6.axOf bits 121946))

theorem wk218 : SixW6.walk table bits 59 121950 bx218 = some 126676 := by decide +kernel

noncomputable def bx219 : SixW6.Box := (bx217).setLo (SixW6.axOf bits 121946) (SixW6.Box.mid bx217 (SixW6.axOf bits 121946))

theorem wk219 : SixW6.walk table bits 59 126676 bx219 = some 126982 := by decide +kernel

theorem wk217 : SixW6.walk table bits 60 121946 bx217 = some 126982 :=
  SixW6.walk_split table bits 59 121946 bx217 126676 126982 (by decide +kernel) wk218 wk219

noncomputable def bx220 : SixW6.Box := (bx216).setLo (SixW6.axOf bits 121942) (SixW6.Box.mid bx216 (SixW6.axOf bits 121942))

theorem wk220 : SixW6.walk table bits 60 126982 bx220 = some 127413 := by decide +kernel

theorem wk216 : SixW6.walk table bits 61 121942 bx216 = some 127413 :=
  SixW6.walk_split table bits 60 121942 bx216 126982 127413 (by decide +kernel) wk217 wk220

noncomputable def bx221 : SixW6.Box := (bx215).setLo (SixW6.axOf bits 121938) (SixW6.Box.mid bx215 (SixW6.axOf bits 121938))

theorem wk221 : SixW6.walk table bits 61 127413 bx221 = some 127434 := by decide +kernel

theorem wk215 : SixW6.walk table bits 62 121938 bx215 = some 127434 :=
  SixW6.walk_split table bits 61 121938 bx215 127413 127434 (by decide +kernel) wk216 wk221

noncomputable def bx222 : SixW6.Box := (bx214).setLo (SixW6.axOf bits 121934) (SixW6.Box.mid bx214 (SixW6.axOf bits 121934))

theorem wk222 : SixW6.walk table bits 62 127434 bx222 = some 127435 := by decide +kernel

theorem wk214 : SixW6.walk table bits 63 121934 bx214 = some 127435 :=
  SixW6.walk_split table bits 62 121934 bx214 127434 127435 (by decide +kernel) wk215 wk222

noncomputable def bx223 : SixW6.Box := (bx213).setLo (SixW6.axOf bits 121930) (SixW6.Box.mid bx213 (SixW6.axOf bits 121930))

theorem wk223 : SixW6.walk table bits 63 127435 bx223 = some 127436 := by decide +kernel

theorem wk213 : SixW6.walk table bits 64 121930 bx213 = some 127436 :=
  SixW6.walk_split table bits 63 121930 bx213 127435 127436 (by decide +kernel) wk214 wk223

noncomputable def bx224 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 59904 74752 30720 40448)

theorem wk224 : SixW6.walk table bits 64 127436 bx224 = some 127437 := by decide +kernel

noncomputable def bx225 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 59904 74752 57344 450560)

noncomputable def bx226 : SixW6.Box := (bx225).setHi (SixW6.axOf bits 127437) (SixW6.Box.mid bx225 (SixW6.axOf bits 127437))

noncomputable def bx227 : SixW6.Box := (bx226).setHi (SixW6.axOf bits 127441) (SixW6.Box.mid bx226 (SixW6.axOf bits 127441))

noncomputable def bx228 : SixW6.Box := (bx227).setHi (SixW6.axOf bits 127445) (SixW6.Box.mid bx227 (SixW6.axOf bits 127445))

noncomputable def bx229 : SixW6.Box := (bx228).setHi (SixW6.axOf bits 127449) (SixW6.Box.mid bx228 (SixW6.axOf bits 127449))

noncomputable def bx230 : SixW6.Box := (bx229).setHi (SixW6.axOf bits 127453) (SixW6.Box.mid bx229 (SixW6.axOf bits 127453))

noncomputable def bx231 : SixW6.Box := (bx230).setHi (SixW6.axOf bits 127457) (SixW6.Box.mid bx230 (SixW6.axOf bits 127457))

noncomputable def bx232 : SixW6.Box := (bx231).setHi (SixW6.axOf bits 127461) (SixW6.Box.mid bx231 (SixW6.axOf bits 127461))

noncomputable def bx233 : SixW6.Box := (bx232).setHi (SixW6.axOf bits 127465) (SixW6.Box.mid bx232 (SixW6.axOf bits 127465))

noncomputable def bx234 : SixW6.Box := (bx233).setHi (SixW6.axOf bits 127469) (SixW6.Box.mid bx233 (SixW6.axOf bits 127469))

theorem wk234 : SixW6.walk table bits 55 127473 bx234 = some 127814 := by decide +kernel

noncomputable def bx235 : SixW6.Box := (bx233).setLo (SixW6.axOf bits 127469) (SixW6.Box.mid bx233 (SixW6.axOf bits 127469))

noncomputable def bx236 : SixW6.Box := (bx235).setHi (SixW6.axOf bits 127814) (SixW6.Box.mid bx235 (SixW6.axOf bits 127814))

theorem wk236 : SixW6.walk table bits 54 127818 bx236 = some 132204 := by decide +kernel

noncomputable def bx237 : SixW6.Box := (bx235).setLo (SixW6.axOf bits 127814) (SixW6.Box.mid bx235 (SixW6.axOf bits 127814))

theorem wk237 : SixW6.walk table bits 54 132204 bx237 = some 132955 := by decide +kernel

theorem wk235 : SixW6.walk table bits 55 127814 bx235 = some 132955 :=
  SixW6.walk_split table bits 54 127814 bx235 132204 132955 (by decide +kernel) wk236 wk237

theorem wk233 : SixW6.walk table bits 56 127469 bx233 = some 132955 :=
  SixW6.walk_split table bits 55 127469 bx233 127814 132955 (by decide +kernel) wk234 wk235

noncomputable def bx238 : SixW6.Box := (bx232).setLo (SixW6.axOf bits 127465) (SixW6.Box.mid bx232 (SixW6.axOf bits 127465))

theorem wk238 : SixW6.walk table bits 56 132955 bx238 = some 132996 := by decide +kernel

theorem wk232 : SixW6.walk table bits 57 127465 bx232 = some 132996 :=
  SixW6.walk_split table bits 56 127465 bx232 132955 132996 (by decide +kernel) wk233 wk238

noncomputable def bx239 : SixW6.Box := (bx231).setLo (SixW6.axOf bits 127461) (SixW6.Box.mid bx231 (SixW6.axOf bits 127461))

theorem wk239 : SixW6.walk table bits 57 132996 bx239 = some 133202 := by decide +kernel

theorem wk231 : SixW6.walk table bits 58 127461 bx231 = some 133202 :=
  SixW6.walk_split table bits 57 127461 bx231 132996 133202 (by decide +kernel) wk232 wk239

noncomputable def bx240 : SixW6.Box := (bx230).setLo (SixW6.axOf bits 127457) (SixW6.Box.mid bx230 (SixW6.axOf bits 127457))

theorem wk240 : SixW6.walk table bits 58 133202 bx240 = some 133648 := by decide +kernel

theorem wk230 : SixW6.walk table bits 59 127457 bx230 = some 133648 :=
  SixW6.walk_split table bits 58 127457 bx230 133202 133648 (by decide +kernel) wk231 wk240

noncomputable def bx241 : SixW6.Box := (bx229).setLo (SixW6.axOf bits 127453) (SixW6.Box.mid bx229 (SixW6.axOf bits 127453))

theorem wk241 : SixW6.walk table bits 59 133648 bx241 = some 133679 := by decide +kernel

theorem wk229 : SixW6.walk table bits 60 127453 bx229 = some 133679 :=
  SixW6.walk_split table bits 59 127453 bx229 133648 133679 (by decide +kernel) wk230 wk241

noncomputable def bx242 : SixW6.Box := (bx228).setLo (SixW6.axOf bits 127449) (SixW6.Box.mid bx228 (SixW6.axOf bits 127449))

theorem wk242 : SixW6.walk table bits 60 133679 bx242 = some 133730 := by decide +kernel

theorem wk228 : SixW6.walk table bits 61 127449 bx228 = some 133730 :=
  SixW6.walk_split table bits 60 127449 bx228 133679 133730 (by decide +kernel) wk229 wk242

noncomputable def bx243 : SixW6.Box := (bx227).setLo (SixW6.axOf bits 127445) (SixW6.Box.mid bx227 (SixW6.axOf bits 127445))

theorem wk243 : SixW6.walk table bits 61 133730 bx243 = some 133746 := by decide +kernel

theorem wk227 : SixW6.walk table bits 62 127445 bx227 = some 133746 :=
  SixW6.walk_split table bits 61 127445 bx227 133730 133746 (by decide +kernel) wk228 wk243

noncomputable def bx244 : SixW6.Box := (bx226).setLo (SixW6.axOf bits 127441) (SixW6.Box.mid bx226 (SixW6.axOf bits 127441))

theorem wk244 : SixW6.walk table bits 62 133746 bx244 = some 133747 := by decide +kernel

theorem wk226 : SixW6.walk table bits 63 127441 bx226 = some 133747 :=
  SixW6.walk_split table bits 62 127441 bx226 133746 133747 (by decide +kernel) wk227 wk244

noncomputable def bx245 : SixW6.Box := (bx225).setLo (SixW6.axOf bits 127437) (SixW6.Box.mid bx225 (SixW6.axOf bits 127437))

theorem wk245 : SixW6.walk table bits 63 133747 bx245 = some 133748 := by decide +kernel

theorem wk225 : SixW6.walk table bits 64 127437 bx225 = some 133748 :=
  SixW6.walk_split table bits 63 127437 bx225 133747 133748 (by decide +kernel) wk226 wk245

noncomputable def bx246 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 88064 270336 30720 40448)

theorem wk246 : SixW6.walk table bits 64 133748 bx246 = some 133749 := by decide +kernel

noncomputable def bx247 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 31744 38400 88064 270336 57344 450560)

theorem wk247 : SixW6.walk table bits 64 133749 bx247 = some 134400 := by decide +kernel

noncomputable def bx248 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 31744 38400 30720 40448)

theorem wk248 : SixW6.walk table bits 64 134400 bx248 = some 134401 := by decide +kernel

noncomputable def bx249 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 31744 38400 57344 450560)

noncomputable def bx250 : SixW6.Box := (bx249).setHi (SixW6.axOf bits 134401) (SixW6.Box.mid bx249 (SixW6.axOf bits 134401))

noncomputable def bx251 : SixW6.Box := (bx250).setHi (SixW6.axOf bits 134405) (SixW6.Box.mid bx250 (SixW6.axOf bits 134405))

noncomputable def bx252 : SixW6.Box := (bx251).setHi (SixW6.axOf bits 134409) (SixW6.Box.mid bx251 (SixW6.axOf bits 134409))

noncomputable def bx253 : SixW6.Box := (bx252).setHi (SixW6.axOf bits 134413) (SixW6.Box.mid bx252 (SixW6.axOf bits 134413))

noncomputable def bx254 : SixW6.Box := (bx253).setHi (SixW6.axOf bits 134417) (SixW6.Box.mid bx253 (SixW6.axOf bits 134417))

noncomputable def bx255 : SixW6.Box := (bx254).setHi (SixW6.axOf bits 134421) (SixW6.Box.mid bx254 (SixW6.axOf bits 134421))

noncomputable def bx256 : SixW6.Box := (bx255).setHi (SixW6.axOf bits 134425) (SixW6.Box.mid bx255 (SixW6.axOf bits 134425))

noncomputable def bx257 : SixW6.Box := (bx256).setHi (SixW6.axOf bits 134429) (SixW6.Box.mid bx256 (SixW6.axOf bits 134429))

noncomputable def bx258 : SixW6.Box := (bx257).setHi (SixW6.axOf bits 134433) (SixW6.Box.mid bx257 (SixW6.axOf bits 134433))

theorem wk258 : SixW6.walk table bits 55 134437 bx258 = some 134743 := by decide +kernel

noncomputable def bx259 : SixW6.Box := (bx257).setLo (SixW6.axOf bits 134433) (SixW6.Box.mid bx257 (SixW6.axOf bits 134433))

noncomputable def bx260 : SixW6.Box := (bx259).setHi (SixW6.axOf bits 134743) (SixW6.Box.mid bx259 (SixW6.axOf bits 134743))

noncomputable def bx261 : SixW6.Box := (bx260).setHi (SixW6.axOf bits 134747) (SixW6.Box.mid bx260 (SixW6.axOf bits 134747))

noncomputable def bx262 : SixW6.Box := (bx261).setHi (SixW6.axOf bits 134751) (SixW6.Box.mid bx261 (SixW6.axOf bits 134751))

theorem wk262 : SixW6.walk table bits 52 134755 bx262 = some 134971 := by decide +kernel

noncomputable def bx263 : SixW6.Box := (bx261).setLo (SixW6.axOf bits 134751) (SixW6.Box.mid bx261 (SixW6.axOf bits 134751))

noncomputable def bx264 : SixW6.Box := (bx263).setHi (SixW6.axOf bits 134971) (SixW6.Box.mid bx263 (SixW6.axOf bits 134971))

noncomputable def bx265 : SixW6.Box := (bx264).setHi (SixW6.axOf bits 134975) (SixW6.Box.mid bx264 (SixW6.axOf bits 134975))

theorem wk265 : SixW6.walk table bits 50 134979 bx265 = some 135030 := by decide +kernel

noncomputable def bx266 : SixW6.Box := (bx264).setLo (SixW6.axOf bits 134975) (SixW6.Box.mid bx264 (SixW6.axOf bits 134975))

noncomputable def bx267 : SixW6.Box := (bx266).setHi (SixW6.axOf bits 135030) (SixW6.Box.mid bx266 (SixW6.axOf bits 135030))

noncomputable def bx268 : SixW6.Box := (bx267).setHi (SixW6.axOf bits 135034) (SixW6.Box.mid bx267 (SixW6.axOf bits 135034))

theorem wk268 : SixW6.walk table bits 48 135038 bx268 = some 137919 := by decide +kernel

noncomputable def bx269 : SixW6.Box := (bx267).setLo (SixW6.axOf bits 135034) (SixW6.Box.mid bx267 (SixW6.axOf bits 135034))

noncomputable def bx270 : SixW6.Box := (bx269).setHi (SixW6.axOf bits 137919) (SixW6.Box.mid bx269 (SixW6.axOf bits 137919))

noncomputable def bx271 : SixW6.Box := (bx270).setHi (SixW6.axOf bits 137923) (SixW6.Box.mid bx270 (SixW6.axOf bits 137923))

theorem wk271 : SixW6.walk table bits 46 137927 bx271 = some 137943 := by decide +kernel

noncomputable def bx272 : SixW6.Box := (bx270).setLo (SixW6.axOf bits 137923) (SixW6.Box.mid bx270 (SixW6.axOf bits 137923))

noncomputable def bx273 : SixW6.Box := (bx272).setHi (SixW6.axOf bits 137943) (SixW6.Box.mid bx272 (SixW6.axOf bits 137943))

noncomputable def bx274 : SixW6.Box := (bx273).setHi (SixW6.axOf bits 137947) (SixW6.Box.mid bx273 (SixW6.axOf bits 137947))

theorem wk274 : SixW6.walk table bits 44 137951 bx274 = some 137957 := by decide +kernel

noncomputable def bx275 : SixW6.Box := (bx273).setLo (SixW6.axOf bits 137947) (SixW6.Box.mid bx273 (SixW6.axOf bits 137947))

noncomputable def bx276 : SixW6.Box := (bx275).setHi (SixW6.axOf bits 137957) (SixW6.Box.mid bx275 (SixW6.axOf bits 137957))

noncomputable def bx277 : SixW6.Box := (bx276).setHi (SixW6.axOf bits 137961) (SixW6.Box.mid bx276 (SixW6.axOf bits 137961))

theorem wk277 : SixW6.walk table bits 42 137965 bx277 = some 141236 := by decide +kernel

noncomputable def bx278 : SixW6.Box := (bx276).setLo (SixW6.axOf bits 137961) (SixW6.Box.mid bx276 (SixW6.axOf bits 137961))

theorem wk278 : SixW6.walk table bits 42 141236 bx278 = some 143297 := by decide +kernel

theorem wk276 : SixW6.walk table bits 43 137961 bx276 = some 143297 :=
  SixW6.walk_split table bits 42 137961 bx276 141236 143297 (by decide +kernel) wk277 wk278

noncomputable def bx279 : SixW6.Box := (bx275).setLo (SixW6.axOf bits 137957) (SixW6.Box.mid bx275 (SixW6.axOf bits 137957))

theorem wk279 : SixW6.walk table bits 43 143297 bx279 = some 146583 := by decide +kernel

theorem wk275 : SixW6.walk table bits 44 137957 bx275 = some 146583 :=
  SixW6.walk_split table bits 43 137957 bx275 143297 146583 (by decide +kernel) wk276 wk279

theorem wk273 : SixW6.walk table bits 45 137947 bx273 = some 146583 :=
  SixW6.walk_split table bits 44 137947 bx273 137957 146583 (by decide +kernel) wk274 wk275

noncomputable def bx280 : SixW6.Box := (bx272).setLo (SixW6.axOf bits 137943) (SixW6.Box.mid bx272 (SixW6.axOf bits 137943))

theorem wk280 : SixW6.walk table bits 45 146583 bx280 = some 146699 := by decide +kernel

theorem wk272 : SixW6.walk table bits 46 137943 bx272 = some 146699 :=
  SixW6.walk_split table bits 45 137943 bx272 146583 146699 (by decide +kernel) wk273 wk280

theorem wk270 : SixW6.walk table bits 47 137923 bx270 = some 146699 :=
  SixW6.walk_split table bits 46 137923 bx270 137943 146699 (by decide +kernel) wk271 wk272

noncomputable def bx281 : SixW6.Box := (bx269).setLo (SixW6.axOf bits 137919) (SixW6.Box.mid bx269 (SixW6.axOf bits 137919))

theorem wk281 : SixW6.walk table bits 47 146699 bx281 = some 146825 := by decide +kernel

theorem wk269 : SixW6.walk table bits 48 137919 bx269 = some 146825 :=
  SixW6.walk_split table bits 47 137919 bx269 146699 146825 (by decide +kernel) wk270 wk281

theorem wk267 : SixW6.walk table bits 49 135034 bx267 = some 146825 :=
  SixW6.walk_split table bits 48 135034 bx267 137919 146825 (by decide +kernel) wk268 wk269

noncomputable def bx282 : SixW6.Box := (bx266).setLo (SixW6.axOf bits 135030) (SixW6.Box.mid bx266 (SixW6.axOf bits 135030))

theorem wk282 : SixW6.walk table bits 49 146825 bx282 = some 148761 := by decide +kernel

theorem wk266 : SixW6.walk table bits 50 135030 bx266 = some 148761 :=
  SixW6.walk_split table bits 49 135030 bx266 146825 148761 (by decide +kernel) wk267 wk282

theorem wk264 : SixW6.walk table bits 51 134975 bx264 = some 148761 :=
  SixW6.walk_split table bits 50 134975 bx264 135030 148761 (by decide +kernel) wk265 wk266

noncomputable def bx283 : SixW6.Box := (bx263).setLo (SixW6.axOf bits 134971) (SixW6.Box.mid bx263 (SixW6.axOf bits 134971))

theorem wk283 : SixW6.walk table bits 51 148761 bx283 = some 148822 := by decide +kernel

theorem wk263 : SixW6.walk table bits 52 134971 bx263 = some 148822 :=
  SixW6.walk_split table bits 51 134971 bx263 148761 148822 (by decide +kernel) wk264 wk283

theorem wk261 : SixW6.walk table bits 53 134751 bx261 = some 148822 :=
  SixW6.walk_split table bits 52 134751 bx261 134971 148822 (by decide +kernel) wk262 wk263

noncomputable def bx284 : SixW6.Box := (bx260).setLo (SixW6.axOf bits 134747) (SixW6.Box.mid bx260 (SixW6.axOf bits 134747))

theorem wk284 : SixW6.walk table bits 53 148822 bx284 = some 148843 := by decide +kernel

theorem wk260 : SixW6.walk table bits 54 134747 bx260 = some 148843 :=
  SixW6.walk_split table bits 53 134747 bx260 148822 148843 (by decide +kernel) wk261 wk284

noncomputable def bx285 : SixW6.Box := (bx259).setLo (SixW6.axOf bits 134743) (SixW6.Box.mid bx259 (SixW6.axOf bits 134743))

theorem wk285 : SixW6.walk table bits 54 148843 bx285 = some 149969 := by decide +kernel

theorem wk259 : SixW6.walk table bits 55 134743 bx259 = some 149969 :=
  SixW6.walk_split table bits 54 134743 bx259 148843 149969 (by decide +kernel) wk260 wk285

theorem wk257 : SixW6.walk table bits 56 134433 bx257 = some 149969 :=
  SixW6.walk_split table bits 55 134433 bx257 134743 149969 (by decide +kernel) wk258 wk259

noncomputable def bx286 : SixW6.Box := (bx256).setLo (SixW6.axOf bits 134429) (SixW6.Box.mid bx256 (SixW6.axOf bits 134429))

theorem wk286 : SixW6.walk table bits 56 149969 bx286 = some 150005 := by decide +kernel

theorem wk256 : SixW6.walk table bits 57 134429 bx256 = some 150005 :=
  SixW6.walk_split table bits 56 134429 bx256 149969 150005 (by decide +kernel) wk257 wk286

noncomputable def bx287 : SixW6.Box := (bx255).setLo (SixW6.axOf bits 134425) (SixW6.Box.mid bx255 (SixW6.axOf bits 134425))

theorem wk287 : SixW6.walk table bits 57 150005 bx287 = some 150226 := by decide +kernel

theorem wk255 : SixW6.walk table bits 58 134425 bx255 = some 150226 :=
  SixW6.walk_split table bits 57 134425 bx255 150005 150226 (by decide +kernel) wk256 wk287

noncomputable def bx288 : SixW6.Box := (bx254).setLo (SixW6.axOf bits 134421) (SixW6.Box.mid bx254 (SixW6.axOf bits 134421))

theorem wk288 : SixW6.walk table bits 58 150226 bx288 = some 150562 := by decide +kernel

theorem wk254 : SixW6.walk table bits 59 134421 bx254 = some 150562 :=
  SixW6.walk_split table bits 58 134421 bx254 150226 150562 (by decide +kernel) wk255 wk288

noncomputable def bx289 : SixW6.Box := (bx253).setLo (SixW6.axOf bits 134417) (SixW6.Box.mid bx253 (SixW6.axOf bits 134417))

theorem wk289 : SixW6.walk table bits 59 150562 bx289 = some 150588 := by decide +kernel

theorem wk253 : SixW6.walk table bits 60 134417 bx253 = some 150588 :=
  SixW6.walk_split table bits 59 134417 bx253 150562 150588 (by decide +kernel) wk254 wk289

noncomputable def bx290 : SixW6.Box := (bx252).setLo (SixW6.axOf bits 134413) (SixW6.Box.mid bx252 (SixW6.axOf bits 134413))

theorem wk290 : SixW6.walk table bits 60 150588 bx290 = some 150634 := by decide +kernel

theorem wk252 : SixW6.walk table bits 61 134413 bx252 = some 150634 :=
  SixW6.walk_split table bits 60 134413 bx252 150588 150634 (by decide +kernel) wk253 wk290

noncomputable def bx291 : SixW6.Box := (bx251).setLo (SixW6.axOf bits 134409) (SixW6.Box.mid bx251 (SixW6.axOf bits 134409))

theorem wk291 : SixW6.walk table bits 61 150634 bx291 = some 150650 := by decide +kernel

theorem wk251 : SixW6.walk table bits 62 134409 bx251 = some 150650 :=
  SixW6.walk_split table bits 61 134409 bx251 150634 150650 (by decide +kernel) wk252 wk291

noncomputable def bx292 : SixW6.Box := (bx250).setLo (SixW6.axOf bits 134405) (SixW6.Box.mid bx250 (SixW6.axOf bits 134405))

theorem wk292 : SixW6.walk table bits 62 150650 bx292 = some 150651 := by decide +kernel

theorem wk250 : SixW6.walk table bits 63 134405 bx250 = some 150651 :=
  SixW6.walk_split table bits 62 134405 bx250 150650 150651 (by decide +kernel) wk251 wk292

noncomputable def bx293 : SixW6.Box := (bx249).setLo (SixW6.axOf bits 134401) (SixW6.Box.mid bx249 (SixW6.axOf bits 134401))

theorem wk293 : SixW6.walk table bits 63 150651 bx293 = some 150652 := by decide +kernel

theorem wk249 : SixW6.walk table bits 64 134401 bx249 = some 150652 :=
  SixW6.walk_split table bits 63 134401 bx249 150651 150652 (by decide +kernel) wk250 wk293

noncomputable def bx294 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 59904 74752 30720 40448)

theorem wk294 : SixW6.walk table bits 64 150652 bx294 = some 150653 := by decide +kernel

noncomputable def bx295 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 59904 74752 57344 450560)

theorem wk295 : SixW6.walk table bits 64 150653 bx295 = some 151764 := by decide +kernel

noncomputable def bx296 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 88064 270336 30720 40448)

theorem wk296 : SixW6.walk table bits 64 151764 bx296 = some 151765 := by decide +kernel

noncomputable def bx297 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 60416 74240 88064 270336 57344 450560)

theorem wk297 : SixW6.walk table bits 64 151765 bx297 = some 151851 := by decide +kernel

noncomputable def bx298 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 31744 38400 30720 40448)

theorem wk298 : SixW6.walk table bits 64 151851 bx298 = some 151852 := by decide +kernel

noncomputable def bx299 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 31744 38400 57344 450560)

theorem wk299 : SixW6.walk table bits 64 151852 bx299 = some 152383 := by decide +kernel

noncomputable def bx300 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 59904 74752 30720 40448)

theorem wk300 : SixW6.walk table bits 64 152383 bx300 = some 152384 := by decide +kernel

noncomputable def bx301 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 59904 74752 57344 450560)

theorem wk301 : SixW6.walk table bits 64 152384 bx301 = some 152460 := by decide +kernel

noncomputable def bx302 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 88064 270336 30720 40448)

theorem wk302 : SixW6.walk table bits 64 152460 bx302 = some 152461 := by decide +kernel

noncomputable def bx303 : SixW6.Box := (SixW6.Box.mk 57344 450560 31744 38400 88576 245760 88064 270336 57344 450560)

theorem wk303 : SixW6.walk table bits 64 152461 bx303 = some 152462 := by decide +kernel

noncomputable def bx304 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 31744 38400 30720 40448)

theorem wk304 : SixW6.walk table bits 64 152462 bx304 = some 152463 := by decide +kernel

noncomputable def bx305 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 31744 38400 57344 450560)

noncomputable def bx306 : SixW6.Box := (bx305).setHi (SixW6.axOf bits 152463) (SixW6.Box.mid bx305 (SixW6.axOf bits 152463))

noncomputable def bx307 : SixW6.Box := (bx306).setHi (SixW6.axOf bits 152467) (SixW6.Box.mid bx306 (SixW6.axOf bits 152467))

noncomputable def bx308 : SixW6.Box := (bx307).setHi (SixW6.axOf bits 152471) (SixW6.Box.mid bx307 (SixW6.axOf bits 152471))

noncomputable def bx309 : SixW6.Box := (bx308).setHi (SixW6.axOf bits 152475) (SixW6.Box.mid bx308 (SixW6.axOf bits 152475))

noncomputable def bx310 : SixW6.Box := (bx309).setHi (SixW6.axOf bits 152479) (SixW6.Box.mid bx309 (SixW6.axOf bits 152479))

noncomputable def bx311 : SixW6.Box := (bx310).setHi (SixW6.axOf bits 152483) (SixW6.Box.mid bx310 (SixW6.axOf bits 152483))

noncomputable def bx312 : SixW6.Box := (bx311).setHi (SixW6.axOf bits 152487) (SixW6.Box.mid bx311 (SixW6.axOf bits 152487))

noncomputable def bx313 : SixW6.Box := (bx312).setHi (SixW6.axOf bits 152491) (SixW6.Box.mid bx312 (SixW6.axOf bits 152491))

noncomputable def bx314 : SixW6.Box := (bx313).setHi (SixW6.axOf bits 152495) (SixW6.Box.mid bx313 (SixW6.axOf bits 152495))

theorem wk314 : SixW6.walk table bits 55 152499 bx314 = some 152770 := by decide +kernel

noncomputable def bx315 : SixW6.Box := (bx313).setLo (SixW6.axOf bits 152495) (SixW6.Box.mid bx313 (SixW6.axOf bits 152495))

theorem wk315 : SixW6.walk table bits 55 152770 bx315 = some 157571 := by decide +kernel

theorem wk313 : SixW6.walk table bits 56 152495 bx313 = some 157571 :=
  SixW6.walk_split table bits 55 152495 bx313 152770 157571 (by decide +kernel) wk314 wk315

noncomputable def bx316 : SixW6.Box := (bx312).setLo (SixW6.axOf bits 152491) (SixW6.Box.mid bx312 (SixW6.axOf bits 152491))

theorem wk316 : SixW6.walk table bits 56 157571 bx316 = some 157662 := by decide +kernel

theorem wk312 : SixW6.walk table bits 57 152491 bx312 = some 157662 :=
  SixW6.walk_split table bits 56 152491 bx312 157571 157662 (by decide +kernel) wk313 wk316

noncomputable def bx317 : SixW6.Box := (bx311).setLo (SixW6.axOf bits 152487) (SixW6.Box.mid bx311 (SixW6.axOf bits 152487))

theorem wk317 : SixW6.walk table bits 57 157662 bx317 = some 157873 := by decide +kernel

theorem wk311 : SixW6.walk table bits 58 152487 bx311 = some 157873 :=
  SixW6.walk_split table bits 57 152487 bx311 157662 157873 (by decide +kernel) wk312 wk317

noncomputable def bx318 : SixW6.Box := (bx310).setLo (SixW6.axOf bits 152483) (SixW6.Box.mid bx310 (SixW6.axOf bits 152483))

theorem wk318 : SixW6.walk table bits 58 157873 bx318 = some 158294 := by decide +kernel

theorem wk310 : SixW6.walk table bits 59 152483 bx310 = some 158294 :=
  SixW6.walk_split table bits 58 152483 bx310 157873 158294 (by decide +kernel) wk311 wk318

noncomputable def bx319 : SixW6.Box := (bx309).setLo (SixW6.axOf bits 152479) (SixW6.Box.mid bx309 (SixW6.axOf bits 152479))

theorem wk319 : SixW6.walk table bits 59 158294 bx319 = some 158325 := by decide +kernel

theorem wk309 : SixW6.walk table bits 60 152479 bx309 = some 158325 :=
  SixW6.walk_split table bits 59 152479 bx309 158294 158325 (by decide +kernel) wk310 wk319

noncomputable def bx320 : SixW6.Box := (bx308).setLo (SixW6.axOf bits 152475) (SixW6.Box.mid bx308 (SixW6.axOf bits 152475))

theorem wk320 : SixW6.walk table bits 60 158325 bx320 = some 158376 := by decide +kernel

theorem wk308 : SixW6.walk table bits 61 152475 bx308 = some 158376 :=
  SixW6.walk_split table bits 60 152475 bx308 158325 158376 (by decide +kernel) wk309 wk320

noncomputable def bx321 : SixW6.Box := (bx307).setLo (SixW6.axOf bits 152471) (SixW6.Box.mid bx307 (SixW6.axOf bits 152471))

theorem wk321 : SixW6.walk table bits 61 158376 bx321 = some 158392 := by decide +kernel

theorem wk307 : SixW6.walk table bits 62 152471 bx307 = some 158392 :=
  SixW6.walk_split table bits 61 152471 bx307 158376 158392 (by decide +kernel) wk308 wk321

noncomputable def bx322 : SixW6.Box := (bx306).setLo (SixW6.axOf bits 152467) (SixW6.Box.mid bx306 (SixW6.axOf bits 152467))

theorem wk322 : SixW6.walk table bits 62 158392 bx322 = some 158393 := by decide +kernel

theorem wk306 : SixW6.walk table bits 63 152467 bx306 = some 158393 :=
  SixW6.walk_split table bits 62 152467 bx306 158392 158393 (by decide +kernel) wk307 wk322

noncomputable def bx323 : SixW6.Box := (bx305).setLo (SixW6.axOf bits 152463) (SixW6.Box.mid bx305 (SixW6.axOf bits 152463))

theorem wk323 : SixW6.walk table bits 63 158393 bx323 = some 158394 := by decide +kernel

theorem wk305 : SixW6.walk table bits 64 152463 bx305 = some 158394 :=
  SixW6.walk_split table bits 63 152463 bx305 158393 158394 (by decide +kernel) wk306 wk323

noncomputable def bx324 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 59904 74752 30720 40448)

theorem wk324 : SixW6.walk table bits 64 158394 bx324 = some 158395 := by decide +kernel

noncomputable def bx325 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 59904 74752 57344 450560)

theorem wk325 : SixW6.walk table bits 64 158395 bx325 = some 160481 := by decide +kernel

noncomputable def bx326 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 88064 270336 30720 40448)

theorem wk326 : SixW6.walk table bits 64 160481 bx326 = some 160482 := by decide +kernel

noncomputable def bx327 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 31744 38400 88064 270336 57344 450560)

theorem wk327 : SixW6.walk table bits 64 160482 bx327 = some 160568 := by decide +kernel

noncomputable def bx328 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 31744 38400 30720 40448)

theorem wk328 : SixW6.walk table bits 64 160568 bx328 = some 160569 := by decide +kernel

noncomputable def bx329 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 31744 38400 57344 450560)

theorem wk329 : SixW6.walk table bits 64 160569 bx329 = some 161645 := by decide +kernel

noncomputable def bx330 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 59904 74752 30720 40448)

theorem wk330 : SixW6.walk table bits 64 161645 bx330 = some 161646 := by decide +kernel

noncomputable def bx331 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 59904 74752 57344 450560)

theorem wk331 : SixW6.walk table bits 64 161646 bx331 = some 161717 := by decide +kernel

noncomputable def bx332 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 88064 270336 30720 40448)

theorem wk332 : SixW6.walk table bits 64 161717 bx332 = some 161718 := by decide +kernel

noncomputable def bx333 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 60416 74240 88064 270336 57344 450560)

theorem wk333 : SixW6.walk table bits 64 161718 bx333 = some 161719 := by decide +kernel

noncomputable def bx334 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 31744 38400 30720 40448)

theorem wk334 : SixW6.walk table bits 64 161719 bx334 = some 161720 := by decide +kernel

noncomputable def bx335 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 31744 38400 57344 450560)

theorem wk335 : SixW6.walk table bits 64 161720 bx335 = some 161796 := by decide +kernel

noncomputable def bx336 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 59904 74752 30720 40448)

theorem wk336 : SixW6.walk table bits 64 161796 bx336 = some 161797 := by decide +kernel

noncomputable def bx337 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 59904 74752 57344 450560)

theorem wk337 : SixW6.walk table bits 64 161797 bx337 = some 161798 := by decide +kernel

noncomputable def bx338 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 88064 270336 30720 40448)

theorem wk338 : SixW6.walk table bits 64 161798 bx338 = some 161799 := by decide +kernel

noncomputable def bx339 : SixW6.Box := (SixW6.Box.mk 57344 450560 59904 74752 88576 245760 88064 270336 57344 450560)

theorem wk339 : SixW6.walk table bits 64 161799 bx339 = some 161800 := by decide +kernel

noncomputable def bx340 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 31744 38400 30720 40448)

theorem wk340 : SixW6.walk table bits 64 161800 bx340 = some 161801 := by decide +kernel

noncomputable def bx341 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 31744 38400 57344 450560)

theorem wk341 : SixW6.walk table bits 64 161801 bx341 = some 162442 := by decide +kernel

noncomputable def bx342 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 59904 74752 30720 40448)

theorem wk342 : SixW6.walk table bits 64 162442 bx342 = some 162443 := by decide +kernel

noncomputable def bx343 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 59904 74752 57344 450560)

theorem wk343 : SixW6.walk table bits 64 162443 bx343 = some 162529 := by decide +kernel

noncomputable def bx344 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 88064 270336 30720 40448)

theorem wk344 : SixW6.walk table bits 64 162529 bx344 = some 162530 := by decide +kernel

noncomputable def bx345 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 31744 38400 88064 270336 57344 450560)

theorem wk345 : SixW6.walk table bits 64 162530 bx345 = some 162531 := by decide +kernel

noncomputable def bx346 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 31744 38400 30720 40448)

theorem wk346 : SixW6.walk table bits 64 162531 bx346 = some 162532 := by decide +kernel

noncomputable def bx347 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 31744 38400 57344 450560)

theorem wk347 : SixW6.walk table bits 64 162532 bx347 = some 162618 := by decide +kernel

noncomputable def bx348 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 59904 74752 30720 40448)

theorem wk348 : SixW6.walk table bits 64 162618 bx348 = some 162619 := by decide +kernel

noncomputable def bx349 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 59904 74752 57344 450560)

theorem wk349 : SixW6.walk table bits 64 162619 bx349 = some 162620 := by decide +kernel

noncomputable def bx350 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 88064 270336 30720 40448)

theorem wk350 : SixW6.walk table bits 64 162620 bx350 = some 162621 := by decide +kernel

noncomputable def bx351 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 60416 74240 88064 270336 57344 450560)

theorem wk351 : SixW6.walk table bits 64 162621 bx351 = some 162622 := by decide +kernel

noncomputable def bx352 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 31744 38400 30720 40448)

theorem wk352 : SixW6.walk table bits 64 162622 bx352 = some 162623 := by decide +kernel

noncomputable def bx353 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 31744 38400 57344 450560)

theorem wk353 : SixW6.walk table bits 64 162623 bx353 = some 162624 := by decide +kernel

noncomputable def bx354 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 59904 74752 30720 40448)

theorem wk354 : SixW6.walk table bits 64 162624 bx354 = some 162625 := by decide +kernel

noncomputable def bx355 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 59904 74752 57344 450560)

theorem wk355 : SixW6.walk table bits 64 162625 bx355 = some 162626 := by decide +kernel

noncomputable def bx356 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 88064 270336 30720 40448)

theorem wk356 : SixW6.walk table bits 64 162626 bx356 = some 162627 := by decide +kernel

noncomputable def bx357 : SixW6.Box := (SixW6.Box.mk 57344 450560 88064 270336 88576 245760 88064 270336 57344 450560)

theorem wk357 : SixW6.walk table bits 64 162627 bx357 = some 162628 := by decide +kernel

theorem nb0_eq : (SixW6.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW6.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW6.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW6.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW6.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW6.walk table bits 64 0 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 0 0) = some 1536 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 0 0 = bx0 from by decide +kernel]; exact wk0

theorem root_00001 : SixW6.walk table bits 64 1536 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 0 1) = some 5857 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 0 1 = bx1 from by decide +kernel]; exact wk1

theorem root_00010 : SixW6.walk table bits 64 5857 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 1 0) = some 10343 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 1 0 = bx2 from by decide +kernel]; exact wk2

theorem root_00011 : SixW6.walk table bits 64 10343 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 1 1) = some 15374 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 1 1 = bx3 from by decide +kernel]; exact wk3

theorem root_00020 : SixW6.walk table bits 64 15374 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 2 0) = some 17060 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 2 0 = bx8 from by decide +kernel]; exact wk8

theorem root_00021 : SixW6.walk table bits 64 17060 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 2 1) = some 18221 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 0 2 1 = bx9 from by decide +kernel]; exact wk9

theorem root_00100 : SixW6.walk table bits 64 18221 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 0 0) = some 23387 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 0 0 = bx10 from by decide +kernel]; exact wk10

theorem root_00101 : SixW6.walk table bits 64 23387 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 0 1) = some 32868 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 0 1 = bx15 from by decide +kernel]; exact wk15

theorem root_00110 : SixW6.walk table bits 64 32868 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 1 0) = some 37594 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 1 0 = bx42 from by decide +kernel]; exact wk42

theorem root_00111 : SixW6.walk table bits 64 37594 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 1 1) = some 39530 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 1 1 = bx43 from by decide +kernel]; exact wk43

theorem root_00120 : SixW6.walk table bits 64 39530 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 2 0) = some 39931 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 2 0 = bx44 from by decide +kernel]; exact wk44

theorem root_00121 : SixW6.walk table bits 64 39931 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 2 1) = some 40112 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 1 2 1 = bx45 from by decide +kernel]; exact wk45

theorem root_00200 : SixW6.walk table bits 64 40112 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 0 0) = some 41873 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 0 0 = bx46 from by decide +kernel]; exact wk46

theorem root_00201 : SixW6.walk table bits 64 41873 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 0 1) = some 43094 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 0 1 = bx47 from by decide +kernel]; exact wk47

theorem root_00210 : SixW6.walk table bits 64 43094 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 1 0) = some 43480 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 1 0 = bx48 from by decide +kernel]; exact wk48

theorem root_00211 : SixW6.walk table bits 64 43480 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 1 1) = some 43626 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 1 1 = bx49 from by decide +kernel]; exact wk49

theorem root_00220 : SixW6.walk table bits 64 43626 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 2 0) = some 43682 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 2 0 = bx50 from by decide +kernel]; exact wk50

theorem root_00221 : SixW6.walk table bits 64 43682 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 2 1) = some 43683 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 0 2 2 1 = bx51 from by decide +kernel]; exact wk51

theorem root_01000 : SixW6.walk table bits 64 43683 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 0 0) = some 47889 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 0 0 = bx52 from by decide +kernel]; exact wk52

theorem root_01001 : SixW6.walk table bits 64 47889 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 0 1) = some 61065 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 0 1 = bx53 from by decide +kernel]; exact wk53

theorem root_01010 : SixW6.walk table bits 64 61065 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 1 0) = some 86831 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 1 0 = bx78 from by decide +kernel]; exact wk78

theorem root_01011 : SixW6.walk table bits 64 86831 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 1 1) = some 98087 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 1 1 = bx119 from by decide +kernel]; exact wk119

theorem root_01020 : SixW6.walk table bits 64 98087 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 2 0) = some 99358 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 2 0 = bx154 from by decide +kernel]; exact wk154

theorem root_01021 : SixW6.walk table bits 64 99358 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 2 1) = some 99614 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 0 2 1 = bx155 from by decide +kernel]; exact wk155

theorem root_01100 : SixW6.walk table bits 64 99614 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 0 0) = some 103955 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 0 0 = bx156 from by decide +kernel]; exact wk156

theorem root_01101 : SixW6.walk table bits 64 103955 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 0 1) = some 113466 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 0 1 = bx157 from by decide +kernel]; exact wk157

theorem root_01110 : SixW6.walk table bits 64 113466 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 1 0) = some 115082 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 1 0 = bx184 from by decide +kernel]; exact wk184

theorem root_01111 : SixW6.walk table bits 64 115082 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 1 1) = some 115263 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 1 1 = bx185 from by decide +kernel]; exact wk185

theorem root_01120 : SixW6.walk table bits 64 115263 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 2 0) = some 115304 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 2 0 = bx186 from by decide +kernel]; exact wk186

theorem root_01121 : SixW6.walk table bits 64 115304 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 2 1) = some 115305 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 1 2 1 = bx187 from by decide +kernel]; exact wk187

theorem root_01200 : SixW6.walk table bits 64 115305 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 0 0) = some 115681 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 0 0 = bx188 from by decide +kernel]; exact wk188

theorem root_01201 : SixW6.walk table bits 64 115681 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 0 1) = some 115827 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 0 1 = bx189 from by decide +kernel]; exact wk189

theorem root_01210 : SixW6.walk table bits 64 115827 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 1 0) = some 115863 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 1 0 = bx190 from by decide +kernel]; exact wk190

theorem root_01211 : SixW6.walk table bits 64 115863 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 1 1) = some 115864 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 1 1 = bx191 from by decide +kernel]; exact wk191

theorem root_01220 : SixW6.walk table bits 64 115864 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 2 0) = some 115865 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 2 0 = bx192 from by decide +kernel]; exact wk192

theorem root_01221 : SixW6.walk table bits 64 115865 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 2 1) = some 115866 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 1 2 2 1 = bx193 from by decide +kernel]; exact wk193

theorem root_02000 : SixW6.walk table bits 64 115866 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 0 0) = some 117397 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 0 0 = bx194 from by decide +kernel]; exact wk194

theorem root_02001 : SixW6.walk table bits 64 117397 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 0 1) = some 119628 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 0 1 = bx195 from by decide +kernel]; exact wk195

theorem root_02010 : SixW6.walk table bits 64 119628 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 1 0) = some 120899 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 1 0 = bx196 from by decide +kernel]; exact wk196

theorem root_02011 : SixW6.walk table bits 64 120899 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 1 1) = some 121180 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 1 1 = bx197 from by decide +kernel]; exact wk197

theorem root_02020 : SixW6.walk table bits 64 121180 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 2 0) = some 121266 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 2 0 = bx198 from by decide +kernel]; exact wk198

theorem root_02021 : SixW6.walk table bits 64 121266 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 2 1) = some 121267 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 0 2 1 = bx199 from by decide +kernel]; exact wk199

theorem root_02100 : SixW6.walk table bits 64 121267 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 0 0) = some 121643 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 0 0 = bx200 from by decide +kernel]; exact wk200

theorem root_02101 : SixW6.walk table bits 64 121643 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 0 1) = some 121824 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 0 1 = bx201 from by decide +kernel]; exact wk201

theorem root_02110 : SixW6.walk table bits 64 121824 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 1 0) = some 121865 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 1 0 = bx202 from by decide +kernel]; exact wk202

theorem root_02111 : SixW6.walk table bits 64 121865 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 1 1) = some 121866 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 1 1 = bx203 from by decide +kernel]; exact wk203

theorem root_02120 : SixW6.walk table bits 64 121866 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 2 0) = some 121867 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 2 0 = bx204 from by decide +kernel]; exact wk204

theorem root_02121 : SixW6.walk table bits 64 121867 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 2 1) = some 121868 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 1 2 1 = bx205 from by decide +kernel]; exact wk205

theorem root_02200 : SixW6.walk table bits 64 121868 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 0 0) = some 121924 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 0 0 = bx206 from by decide +kernel]; exact wk206

theorem root_02201 : SixW6.walk table bits 64 121924 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 0 1) = some 121925 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 0 1 = bx207 from by decide +kernel]; exact wk207

theorem root_02210 : SixW6.walk table bits 64 121925 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 1 0) = some 121926 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 1 0 = bx208 from by decide +kernel]; exact wk208

theorem root_02211 : SixW6.walk table bits 64 121926 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 1 1) = some 121927 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 1 1 = bx209 from by decide +kernel]; exact wk209

theorem root_02220 : SixW6.walk table bits 64 121927 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 2 0) = some 121928 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 2 0 = bx210 from by decide +kernel]; exact wk210

theorem root_02221 : SixW6.walk table bits 64 121928 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 2 1) = some 121929 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 0 2 2 2 1 = bx211 from by decide +kernel]; exact wk211

theorem root_10000 : SixW6.walk table bits 64 121929 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 0 0) = some 121930 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 0 0 = bx212 from by decide +kernel]; exact wk212

theorem root_10001 : SixW6.walk table bits 64 121930 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 0 1) = some 127436 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 0 1 = bx213 from by decide +kernel]; exact wk213

theorem root_10010 : SixW6.walk table bits 64 127436 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 1 0) = some 127437 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 1 0 = bx224 from by decide +kernel]; exact wk224

theorem root_10011 : SixW6.walk table bits 64 127437 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 1 1) = some 133748 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 1 1 = bx225 from by decide +kernel]; exact wk225

theorem root_10020 : SixW6.walk table bits 64 133748 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 2 0) = some 133749 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 2 0 = bx246 from by decide +kernel]; exact wk246

theorem root_10021 : SixW6.walk table bits 64 133749 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 2 1) = some 134400 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 0 2 1 = bx247 from by decide +kernel]; exact wk247

theorem root_10100 : SixW6.walk table bits 64 134400 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 0 0) = some 134401 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 0 0 = bx248 from by decide +kernel]; exact wk248

theorem root_10101 : SixW6.walk table bits 64 134401 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 0 1) = some 150652 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 0 1 = bx249 from by decide +kernel]; exact wk249

theorem root_10110 : SixW6.walk table bits 64 150652 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 1 0) = some 150653 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 1 0 = bx294 from by decide +kernel]; exact wk294

theorem root_10111 : SixW6.walk table bits 64 150653 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 1 1) = some 151764 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 1 1 = bx295 from by decide +kernel]; exact wk295

theorem root_10120 : SixW6.walk table bits 64 151764 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 2 0) = some 151765 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 2 0 = bx296 from by decide +kernel]; exact wk296

theorem root_10121 : SixW6.walk table bits 64 151765 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 2 1) = some 151851 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 1 2 1 = bx297 from by decide +kernel]; exact wk297

theorem root_10200 : SixW6.walk table bits 64 151851 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 0 0) = some 151852 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 0 0 = bx298 from by decide +kernel]; exact wk298

theorem root_10201 : SixW6.walk table bits 64 151852 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 0 1) = some 152383 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 0 1 = bx299 from by decide +kernel]; exact wk299

theorem root_10210 : SixW6.walk table bits 64 152383 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 1 0) = some 152384 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 1 0 = bx300 from by decide +kernel]; exact wk300

theorem root_10211 : SixW6.walk table bits 64 152384 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 1 1) = some 152460 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 1 1 = bx301 from by decide +kernel]; exact wk301

theorem root_10220 : SixW6.walk table bits 64 152460 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 2 0) = some 152461 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 2 0 = bx302 from by decide +kernel]; exact wk302

theorem root_10221 : SixW6.walk table bits 64 152461 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 2 1) = some 152462 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 0 2 2 1 = bx303 from by decide +kernel]; exact wk303

theorem root_11000 : SixW6.walk table bits 64 152462 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 0 0) = some 152463 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 0 0 = bx304 from by decide +kernel]; exact wk304

theorem root_11001 : SixW6.walk table bits 64 152463 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 0 1) = some 158394 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 0 1 = bx305 from by decide +kernel]; exact wk305

theorem root_11010 : SixW6.walk table bits 64 158394 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 1 0) = some 158395 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 1 0 = bx324 from by decide +kernel]; exact wk324

theorem root_11011 : SixW6.walk table bits 64 158395 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 1 1) = some 160481 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 1 1 = bx325 from by decide +kernel]; exact wk325

theorem root_11020 : SixW6.walk table bits 64 160481 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 2 0) = some 160482 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 2 0 = bx326 from by decide +kernel]; exact wk326

theorem root_11021 : SixW6.walk table bits 64 160482 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 2 1) = some 160568 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 0 2 1 = bx327 from by decide +kernel]; exact wk327

theorem root_11100 : SixW6.walk table bits 64 160568 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 0 0) = some 160569 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 0 0 = bx328 from by decide +kernel]; exact wk328

theorem root_11101 : SixW6.walk table bits 64 160569 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 0 1) = some 161645 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 0 1 = bx329 from by decide +kernel]; exact wk329

theorem root_11110 : SixW6.walk table bits 64 161645 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 1 0) = some 161646 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 1 0 = bx330 from by decide +kernel]; exact wk330

theorem root_11111 : SixW6.walk table bits 64 161646 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 1 1) = some 161717 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 1 1 = bx331 from by decide +kernel]; exact wk331

theorem root_11120 : SixW6.walk table bits 64 161717 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 2 0) = some 161718 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 2 0 = bx332 from by decide +kernel]; exact wk332

theorem root_11121 : SixW6.walk table bits 64 161718 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 2 1) = some 161719 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 1 2 1 = bx333 from by decide +kernel]; exact wk333

theorem root_11200 : SixW6.walk table bits 64 161719 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 0 0) = some 161720 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 0 0 = bx334 from by decide +kernel]; exact wk334

theorem root_11201 : SixW6.walk table bits 64 161720 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 0 1) = some 161796 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 0 1 = bx335 from by decide +kernel]; exact wk335

theorem root_11210 : SixW6.walk table bits 64 161796 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 1 0) = some 161797 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 1 0 = bx336 from by decide +kernel]; exact wk336

theorem root_11211 : SixW6.walk table bits 64 161797 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 1 1) = some 161798 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 1 1 = bx337 from by decide +kernel]; exact wk337

theorem root_11220 : SixW6.walk table bits 64 161798 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 2 0) = some 161799 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 2 0 = bx338 from by decide +kernel]; exact wk338

theorem root_11221 : SixW6.walk table bits 64 161799 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 2 1) = some 161800 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 1 2 2 1 = bx339 from by decide +kernel]; exact wk339

theorem root_12000 : SixW6.walk table bits 64 161800 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 0 0) = some 161801 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 0 0 = bx340 from by decide +kernel]; exact wk340

theorem root_12001 : SixW6.walk table bits 64 161801 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 0 1) = some 162442 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 0 1 = bx341 from by decide +kernel]; exact wk341

theorem root_12010 : SixW6.walk table bits 64 162442 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 1 0) = some 162443 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 1 0 = bx342 from by decide +kernel]; exact wk342

theorem root_12011 : SixW6.walk table bits 64 162443 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 1 1) = some 162529 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 1 1 = bx343 from by decide +kernel]; exact wk343

theorem root_12020 : SixW6.walk table bits 64 162529 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 2 0) = some 162530 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 2 0 = bx344 from by decide +kernel]; exact wk344

theorem root_12021 : SixW6.walk table bits 64 162530 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 2 1) = some 162531 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 0 2 1 = bx345 from by decide +kernel]; exact wk345

theorem root_12100 : SixW6.walk table bits 64 162531 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 0 0) = some 162532 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 0 0 = bx346 from by decide +kernel]; exact wk346

theorem root_12101 : SixW6.walk table bits 64 162532 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 0 1) = some 162618 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 0 1 = bx347 from by decide +kernel]; exact wk347

theorem root_12110 : SixW6.walk table bits 64 162618 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 1 0) = some 162619 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 1 0 = bx348 from by decide +kernel]; exact wk348

theorem root_12111 : SixW6.walk table bits 64 162619 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 1 1) = some 162620 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 1 1 = bx349 from by decide +kernel]; exact wk349

theorem root_12120 : SixW6.walk table bits 64 162620 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 2 0) = some 162621 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 2 0 = bx350 from by decide +kernel]; exact wk350

theorem root_12121 : SixW6.walk table bits 64 162621 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 2 1) = some 162622 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 1 2 1 = bx351 from by decide +kernel]; exact wk351

theorem root_12200 : SixW6.walk table bits 64 162622 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 0 0) = some 162623 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 0 0 = bx352 from by decide +kernel]; exact wk352

theorem root_12201 : SixW6.walk table bits 64 162623 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 0 1) = some 162624 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 0 1 = bx353 from by decide +kernel]; exact wk353

theorem root_12210 : SixW6.walk table bits 64 162624 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 1 0) = some 162625 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 1 0 = bx354 from by decide +kernel]; exact wk354

theorem root_12211 : SixW6.walk table bits 64 162625 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 1 1) = some 162626 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 1 1 = bx355 from by decide +kernel]; exact wk355

theorem root_12220 : SixW6.walk table bits 64 162626 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 2 0) = some 162627 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 2 0 = bx356 from by decide +kernel]; exact wk356

theorem root_12221 : SixW6.walk table bits 64 162627 (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 2 1) = some 162628 := by
  rw [show SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) 1 2 2 2 1 = bx357 from by decide +kernel]; exact wk357

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW6.badOf cover0).length → i1 < (SixW6.badOf cover1).length → i2 < (SixW6.badOf cover2).length → i3 < (SixW6.badOf cover3).length → i4 < (SixW6.badOf cover4).length →
    ∃ pos pos', SixW6.walk table bits 64 pos (SixW6.boxOf (SixW6.badOf cover0) (SixW6.badOf cover1) (SixW6.badOf cover2) (SixW6.badOf cover3) (SixW6.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  rw [nb3_eq] at hi3
  rw [nb4_eq] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00000⟩
  | 0, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00001⟩
  | 0, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00010⟩
  | 0, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00011⟩
  | 0, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00020⟩
  | 0, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00021⟩
  | 0, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00100⟩
  | 0, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00101⟩
  | 0, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00110⟩
  | 0, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00111⟩
  | 0, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00120⟩
  | 0, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00121⟩
  | 0, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00200⟩
  | 0, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00201⟩
  | 0, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00210⟩
  | 0, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00211⟩
  | 0, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00220⟩
  | 0, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00221⟩
  | 0, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01000⟩
  | 0, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01001⟩
  | 0, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01010⟩
  | 0, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01011⟩
  | 0, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01020⟩
  | 0, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01021⟩
  | 0, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01100⟩
  | 0, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01101⟩
  | 0, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01110⟩
  | 0, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01111⟩
  | 0, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01120⟩
  | 0, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01121⟩
  | 0, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01200⟩
  | 0, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01201⟩
  | 0, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01210⟩
  | 0, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01211⟩
  | 0, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01220⟩
  | 0, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01221⟩
  | 0, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02000⟩
  | 0, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02001⟩
  | 0, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02010⟩
  | 0, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02011⟩
  | 0, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02020⟩
  | 0, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02021⟩
  | 0, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02100⟩
  | 0, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02101⟩
  | 0, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02110⟩
  | 0, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02111⟩
  | 0, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02120⟩
  | 0, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02121⟩
  | 0, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02200⟩
  | 0, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02201⟩
  | 0, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02210⟩
  | 0, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02211⟩
  | 0, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02220⟩
  | 0, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02221⟩
  | 1, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10000⟩
  | 1, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10001⟩
  | 1, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10010⟩
  | 1, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10011⟩
  | 1, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10020⟩
  | 1, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10021⟩
  | 1, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10100⟩
  | 1, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10101⟩
  | 1, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10110⟩
  | 1, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10111⟩
  | 1, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10120⟩
  | 1, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10121⟩
  | 1, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10200⟩
  | 1, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10201⟩
  | 1, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10210⟩
  | 1, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10211⟩
  | 1, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10220⟩
  | 1, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10221⟩
  | 1, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11000⟩
  | 1, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11001⟩
  | 1, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11010⟩
  | 1, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11011⟩
  | 1, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11020⟩
  | 1, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11021⟩
  | 1, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11100⟩
  | 1, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11101⟩
  | 1, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11110⟩
  | 1, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11111⟩
  | 1, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11120⟩
  | 1, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11121⟩
  | 1, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11200⟩
  | 1, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11201⟩
  | 1, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11210⟩
  | 1, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11211⟩
  | 1, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11220⟩
  | 1, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11221⟩
  | 1, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12000⟩
  | 1, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12001⟩
  | 1, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12010⟩
  | 1, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12011⟩
  | 1, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12020⟩
  | 1, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12021⟩
  | 1, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12100⟩
  | 1, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12101⟩
  | 1, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12110⟩
  | 1, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12111⟩
  | 1, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12120⟩
  | 1, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12121⟩
  | 1, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12200⟩
  | 1, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12201⟩
  | 1, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12210⟩
  | 1, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12211⟩
  | 1, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12220⟩
  | 1, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12221⟩
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW6.cN : ℝ) / SixW6.SA ≤ SixW6.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW6.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 450560 270336 245760 270336 450560
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW6Data

/-! ###### submission layer: constant-independent part ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- `(√2)⁻¹ = √2/2`. -/
theorem inv_sqrt_two : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [inv_eq_one_div, div_eq_div_iff hne two_ne_zero, one_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- `HD 1 = 3/2 − γ` with `γ = (√2/2)·cot(√2/2)`, the constant `ThreePoint.gam`. -/
theorem HD_one_eq_gam : HD 1 = 3 / 2 - ThreePoint.gam := by
  rw [HD_one, inv_sqrt_two]
  unfold ThreePoint.gam
  ring

/-- `H = HD 1` enclosed to `1.1·10⁻⁸`, from `ThreePoint.gam_bounds`. -/
theorem HD_one_bounds :
    (6725006982 / 10000000000 : ℝ) ≤ HD 1 ∧ HD 1 ≤ 6725007093 / 10000000000 := by
  have hg := ThreePoint.gam_bounds
  rw [HD_one_eq_gam]
  norm_num at hg ⊢
  constructor <;> linarith [hg.1, hg.2]

/-- The library's Theorem-D constant `cStar 1` (division-safe form) equals the challenge's
`cMT` (the tan form at ϑ = 1/√2): by `cStar_eq_tan_form` and unfolding `theta 1 = 1/√2`. -/
theorem cStar_one_eq_cMT : Zeta23.ThmD.cStar 1 = cMT := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold cMT Zeta23.ThmD.theta
  rfl

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩


end RiemannFail

end

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
