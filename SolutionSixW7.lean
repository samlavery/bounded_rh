/-
Riemann.fail submission — an unconditional critical-line proportion of 6729357/10000000 = 0.6729357,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW7`: a table of 7486 interval cells, each certified by
an integer pipeline (Taylor enclosures of cos and sin at scale 10¹⁵, `cellN_soundZ`), and a
bisection over the gaps with 23519 leaves over the half-space
g₀ ≤ g₄; the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`.  The resulting constant is
`(305000000·H − 539991)/304000379 = 0.67293574…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is
enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places the exact rational
`6729357/10000000` strictly between the record and the proved constant.

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

/-! ###### natural-number checker for the 6-point weighted certificate `SixW7` ###### -/

section SixW7Defs

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

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

def SA : ℕ := 100000000
def cN : ℕ := 333207

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

end Zeta23Ext.Bridge.ThreePoint.SixW7

end SixW7Defs

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

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

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

end Zeta23Ext.Bridge.ThreePoint.SixW7

end

/-! ###### certificate data `SixW7`: 7486 cells, 23519 leaves (axis-coded walk) (half-space) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW7Data

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW7

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

noncomputable def tab0 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨17179893760,331038177865⟩ E) ⟨25769832448,242869129569⟩ (N E ⟨30064800768,217716609437⟩ E)) ⟨30064801792,122761883704⟩ (N (N E ⟨31138543616,131696313575⟩ E) ⟨32212286464,69269436296⟩ (N E ⟨32212286656,59504641098⟩ E))) ⟨32212287488,27393363819⟩ (N (N (N E ⟨33286029120,34548539408⟩ E) ⟨33286029312,28203622388⟩ (N E ⟨33487355376,47896897026⟩ E)) ⟨33487355680,35832620095⟩ (N (N E ⟨33487355904,28296403112⟩ E) ⟨33806122784,36023083580⟩ E))) ⟨34124890112,28464081354⟩ (N (N (N (N E ⟨34158444544,28467564926⟩ E) ⟨34359771152,27966906972⟩ (N E ⟨34359771216,25976114687⟩ E)) ⟨34359771360,21788669253⟩ (N (N E ⟨34359771520,17601327427⟩ E) ⟨34359771776,11891897536⟩ (N E ⟨34376548576,21788669253⟩ E))) ⟨34443657600,17601327427⟩ (N (N (N E ⟨34594652592,16438965712⟩ E) ⟨34594652800,11891897536⟩ (N E ⟨34762424856,14066726447⟩ E)) ⟨34762425008,10953811162⟩ (N (N E ⟨34762425312,5952302335⟩ E) ⟨34762425920,560103521⟩ E)))) ⟨34812756608,11891897536⟩ (N (N (N (N (N E ⟨34921808560,10953811162⟩ E) ⟨35030860520,9911220876⟩ (N E ⟨35030860624,8121431559⟩ E)) ⟨35030860832,5101426618⟩ (N (N E ⟨35030861248,1207853390⟩ E) ⟨35081192264,8252405001⟩ (N E ⟨35081192416,5952302335⟩ E))) ⟨35139912528,8121431559⟩ (N (N (N E ⟨35240575968,5952302335⟩ E) ⟨35248964536,6519258779⟩ (N E ⟨35248964640,5101426618⟩ E)) ⟨35358016544,5101426618⟩ (N (N E ⟨35399959672,4043273979⟩ E) ⟨35399959824,2515072630⟩ E))) ⟨35399960128,560103521⟩ (N (N (N (N E ⟨35467068552,3864654916⟩ E) ⟨35467068656,2805660000⟩ (N E ⟨35467068864,1207853390⟩ E)) ⟨35559343376,2515072630⟩ (N (N E ⟨35576120560,2805660000⟩ E) ⟨35685172568,1921155551⟩ E)) ⟨35685172672,1207853390⟩ (N (N (N E ⟨35718727080,1357438270⟩ E) ⟨35718727232,560103521⟩ (N E ⟨35794224576,1207853390⟩ E)) ⟨35878110784,560103521⟩ (N (N E ⟨35903276584,662464275⟩ E) ⟨35903276688,281698711⟩ E))))) ⟨36012328592,281698711⟩ (N (N (N (N (N (N E ⟨36339484720,861720⟩ E) ⟨36339484928,840527⟩ (N E ⟨36356262048,5069528⟩ E)) ⟨36557588736,330776253⟩ (N (N E ⟨36675029456,741120989⟩ E) ⟨36675029760,715005325⟩ (N E ⟨36775692960,1209025102⟩ E))) ⟨36775693376,1151561664⟩ (N (N (N E ⟨36775694208,1046595949⟩ E) ⟨36775695872,870430129⟩ (N E ⟨36993796864,2670280633⟩ E)) ⟨37211900992,4577595806⟩ (N (N E ⟨37312564576,5517323674⟩ E) ⟨37312565184,5147011177⟩ E))) ⟨37312566400,4495681621⟩ (N (N (N (N E ⟨37312568832,3476319374⟩ E) ⟨37648109440,9452356006⟩ (N E ⟨37950099392,14339196425⟩ E)) ⟨38520526336,22408627075⟩ (N (N E ⟨38587634208,26598494431⟩ E) ⟨38587634816,24873411793⟩ E)) ⟨39225169024,41723990006⟩ (N (N (N E ⟨39862705664,48862449799⟩ E) ⟨40265357312,71849923330⟩ (N E ⟨40802230272,75832144115⟩ E)) ⟨42412843008,143033504697⟩ (N (N E ⟨42949715968,138814108272⟩ E) ⟨42949722112,80226784524⟩ E)))) ⟨45097201664,198611196246⟩ (N (N (N (N (N E ⟨47244689408,205420959916⟩ E) ⟨51539660800,198637449669⟩ (N E ⟨51539664896,86044756753⟩ E)) ⟨55834630144,180021136485⟩ (N (N E ⟨57982114816,163928295311⟩ E) ⟨59055857664,136793280978⟩ (N E ⟨60129601536,81450895201⟩ E))) ⟨60129602496,58511094735⟩ (N (N (N E ⟨60129605504,12672374339⟩ E) ⟨62277085696,76332532051⟩ (N E ⟨62277086208,63653684247⟩ E)) ⟨62813958464,37346344857⟩ (N (N E ⟨62813960320,12524178889⟩ E) ⟨63283719856,50922109454⟩ E))) ⟨63283720608,36479946606⟩ (N (N (N (N E ⟨63283722112,15458596484⟩ E) ⟨63350829760,31761760685⟩ (N E ⟨63350831488,10561059564⟩ E)) ⟨64072249760,37767978682⟩ (N (N E ⟨64760116448,25219863798⟩ E) ⟨64760117376,13822922534⟩ E)) ⟨64860779664,26493414731⟩ (N (N (N E ⟨64860780416,16656309302⟩ E) ⟨65162769952,21197196115⟩ (N E ⟨65162770816,11542172995⟩ E)) ⟨65649309568,17189330366⟩ (N (N E ⟨65733195440,19784936895⟩ E) ⟨65733195904,14382857067⟩ E)))))) ⟨66068740048,16517231195⟩ (N (N (N (N (N (N (N E ⟨66068740480,11958745632⟩ E) ⟨66219735168,14637317128⟩ (N E ⟨66437839096,13475236602⟩ E)) ⟨66437839472,9904421098⟩ (N (N E ⟨66437840224,4533628375⟩ E) ⟨66437840896,1574893196⟩ (N E ⟨66521725312,12146351030⟩ E))) ⟨66572058624,1582848890⟩ (N (N (N E ⟨66706274664,12455181737⟩ E) ⟨66706274896,10274232917⟩ (N E ⟨66706275360,6599075710⟩ E)) ⟨66706276288,1804170120⟩ (N (N E ⟨66773385216,1593922516⟩ E) ⟨66832104048,10031012765⟩ E))) ⟨66949544528,10351402322⟩ (N (N (N (N E ⟨66974710360,10287535730⟩ E) ⟨66974710576,8457379249⟩ (N E ⟨66974711008,5380608052⟩ E)) ⟨66974711808,1603951009⟩ (N (N E ⟨67192814392,8446267449⟩ E) ⟨67192814624,6695668958⟩ (N E ⟨67201202884,9408758780⟩ E))) ⟨67201202992,8512647331⟩ (N (N (N E ⟨67226369000,7104322291⟩ E) ⟨67226369376,4646209556⟩ (N E ⟨67314449200,8539108601⟩ E)) ⟨67427695516,7712665796⟩ (N (N E ⟨67427695624,6909605630⟩ E) ⟨67427695840,5447824625⟩ E)))) ⟨67436084140,7592259489⟩ (N (N (N (N (N E ⟨67436084256,6739185667⟩ E) ⟨67444473856,1623212765⟩ (N E ⟨67540941832,6929342825⟩ E)) ⟨67557719072,6759729845⟩ (N (N E ⟨67620633952,4692075139⟩ E) ⟨67645800448,1629667415⟩ (N E ⟨67654188148,6189035296⟩ E))) ⟨67654188256,5477660057⟩ (N (N (N E ⟨67679354004,5976774446⟩ E) ⟨67679354120,5229205555⟩ (N E ⟨67679354352,3895806887⟩ E)) ⟨67679354816,1850310580⟩ (N (N E ⟨67767434464,5491622117⟩ E) ⟨67800988936,5243238134⟩ E))) ⟨67880680780,4836965686⟩ (N (N (N (N E ⟨67880680888,4215794124⟩ E) ⟨67880681104,3110902549⟩ (N E ⟨67880681472,1635815150⟩ E)) ⟨67922623868,4558943825⟩ (N (N E ⟨67922623984,3915022730⟩ E) ⟨67993927096,4224912015⟩ E)) ⟨68014898904,2788748804⟩ (N (N (N E ⟨68014899200,1638655395⟩ E) ⟨68044258800,3923692751⟩ (N E ⟨68082008064,1639891309⟩ E)) ⟨68107173412,3655290937⟩ (N (N E ⟨68107173520,3122730614⟩ E) ⟨68165893732,3337264699⟩ E))))) ⟨68165893848,2794987398⟩ (N (N (N (N (N (N E ⟨68165894080,1863235879⟩ E) ⟨68220419728,3127916271⟩ (N E ⟨68287528664,2799418300⟩ E)) ⟨68316889088,1643246852⟩ (N (N E ⟨68333666152,2196937193⟩ E) ⟨68333666304,1643428677⟩ (N E ⟨68409163668,2029161985⟩ E))) ⟨68409163712,1867112451⟩ (N (N (N E ⟨68409163776,1644151272⟩ E) ⟨68560158720,1645126676⟩ (N E ⟨68606296064,1645299686⟩ E)) ⟨68652433408,1645414146⟩ (N (N E ⟨68719542336,1436255057⟩ E) ⟨68719542352,1386217883⟩ E))) ⟨68719542440,1127174177⟩ (N (N (N (N E ⟨68719542464,1061259562⟩ E) ⟨68719542672,574380421⟩ (N E ⟨68719542688,543159341⟩ E)) ⟨68719542720,483371336⟩ (N (N E ⟨68719542880,237237242⟩ E) ⟨68719543104,38888271⟩ E)) ⟨68719543136,24319712⟩ (N (N (N E ⟨68753097568,24319712⟩ E) ⟨68786651416,836853921⟩ (N E ⟨68786651632,400308901⟩ E)) ⟨68786652064,5411364⟩ (N (N E ⟨68803428808,468976518⟩ E) ⟨68803429184,38888271⟩ E)))) ⟨68895703440,574380421⟩ (N (N (N (N (N E ⟨69013144048,400308901⟩ E) ⟨69138973304,207865661⟩ (N E ⟨69138973536,24319712⟩ E)) ⟨69197693760,38888271⟩ (N (N E ⟨69239636896,5411364⟩ E) ⟨69382243168,24319712⟩ (N E ⟨69793285632,2395549⟩ E))) ⟨69793285840,2365704⟩ (N (N (N E ⟨69793285936,2352087⟩ E) ⟨69793286144,2322919⟩ (N E ⟨69793286560,2265929⟩ E)) ⟨69793286752,2240217⟩ (N (N E ⟨69793287168,2185750⟩ E) ⟨69793287392,2157108⟩ E))) ⟨69793287968,2085588⟩ (N (N (N (N E ⟨69793288000,2081703⟩ E) ⟨69793288384,2035776⟩ (N E ⟨69793289216,1940543⟩ E)) ⟨69810063168,4693333⟩ (N (N E ⟨69843617440,11908301⟩ E) ⟨69843617856,11614602⟩ E)) ⟨69910726256,36131620⟩ (N (N (N E ⟨69910726464,35682246⟩ E) ⟨69994612720,82911860⟩ (N E ⟨69994612928,81886628⟩ E)) ⟨70011389648,96505337⟩ (N (N E ⟨70011389952,94759960⟩ E) ⟨70028167088,108011776⟩ E)))))))

noncomputable def tab1 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨70028167504,105358671⟩ E) ⟨70028167808,103471352⟩ (N E ⟨70061721248,138285081⟩ E)) ⟨70061721456,136566458⟩ (N (N E ⟨70061721664,134874514⟩ E) ⟨70061722080,131568687⟩ (N E ⟨70061722496,128363755⟩ E))) ⟨70061722704,126797969⟩ (N (N (N E ⟨70061722912,125256038⟩ E) ⟨70061723328,122242010⟩ (N E ⟨70061724160,116481657⟩ E)) ⟨70061724992,111057344⟩ (N (N E ⟨70061725824,105945771⟩ E) ⟨70061727488,96576815⟩ E))) ⟨70061727744,95228999⟩ (N (N (N (N E ⟨70112052992,186158274⟩ E) ⟨70112053040,185621927⟩ (N E ⟨70112053248,183320007⟩ E)) ⟨70128830272,203249109⟩ (N (N E ⟨70145607424,222733661⟩ E) ⟨70195940320,263475724⟩ (N E ⟨70195940736,257105912⟩ E))) ⟨70212716736,297726860⟩ (N (N (N E ⟨70229493664,325536030⟩ E) ⟨70229493872,321505826⟩ (N E ⟨70229494176,315727311⟩ E)) ⟨70229494784,304555423⟩ (N (N E ⟨70229496000,283658578⟩ E) ⟨70263049056,352533813⟩ E)))) ⟨70263049664,340141246⟩ (N (N (N (N (N E ⟨70263049888,335713460⟩ E) ⟨70263050496,324053974⟩ (N E ⟨70263051552,304983336⟩ E)) ⟨70263052160,294639592⟩ (N (N E ⟨70279825264,399534449⟩ E) ⟨70279825472,394584551⟩ (N E ⟨70279826720,366445045⟩ E))) ⟨70330157056,475935030⟩ (N (N (N E ⟨70346934496,497487919⟩ E) ⟨70346934912,485323301⟩ (N E ⟨70380488992,553587028⟩ E)) ⟨70430820344,658228367⟩ (N (N E ⟨70430820448,654143399⟩ E) ⟨70430820656,646068310⟩ E))) ⟨70430820752,642383481⟩ (N (N (N (N E ⟨70430820960,634489588⟩ E) ⟨70430821376,619063056⟩ (N E ⟨70430822208,589594224⟩ E)) ⟨70447597528,692802516⟩ (N (N E ⟨70447597680,686526830⟩ E) ⟨70464375424,698060319⟩ E)) ⟨70497929176,797737052⟩ (N (N (N E ⟨70497929280,792783899⟩ E) ⟨70497929488,782992656⟩ (N E ⟨70497929696,773352456⟩ E)) ⟨70497929904,763860504⟩ (N (N E ⟨70497930112,754514068⟩ E) ⟨70497930944,718530834⟩ E))))) ⟨70539872352,883700703⟩ (N (N (N (N (N (N E ⟨70548260920,904973145⟩ E) ⟨70548261072,896787379⟩ (N E ⟨70548261280,885735549⟩ E)) ⟨70598593120,991130713⟩ (N (N E ⟨70598593184,987374804⟩ E) ⟨70598593984,941896883⟩ (N E ⟨70598594112,934865887⟩ E))) ⟨70598594304,924442220⟩ (N (N (N E ⟨70598595136,880920042⟩ E) ⟨70598595520,861699413⟩ (N E ⟨70598595712,852286103⟩ E)) ⟨70598595968,839934492⟩ (N (N E ⟨70598596352,821824466⟩ E) ⟨70598596800,801309854⟩ E))) ⟨70598597952,751428422⟩ (N (N (N (N E ⟨70598598016,748772886⟩ E) ⟨70598598656,722853285⟩ (N E ⟨70606981184,1044394840⟩ E)) ⟨70606981232,1041400348⟩ (N (N E ⟨70632147536,1073153345⟩ E) ⟨70632147744,1060003687⟩ E)) ⟨70632148144,1035278337⟩ (N (N (N E ⟨70632148352,1022706643⟩ E) ⟨70648924464,1134177194⟩ (N E ⟨70648924768,1113850670⟩ E)) ⟨70665701752,1172438358⟩ (N (N E ⟨70665701904,1161884123⟩ E) ⟨70665702208,1141130358⟩ E)))) ⟨70665702320,1133601450⟩ (N (N (N (N (N E ⟨70665702624,1113477271⟩ E) ⟨70665703232,1074553868⟩ (N E ⟨70665704448,1001688603⟩ E)) ⟨70707644624,1296756953⟩ (N (N E ⟨70716033192,1323040638⟩ E) ⟨70716033296,1314851598⟩ (N E ⟨70716033504,1298663154⟩ E))) ⟨70716033920,1267028524⟩ (N (N (N E ⟨70732814208,1098639492⟩ E) ⟨70732816384,973352611⟩ (N E ⟨70749587856,1398371502⟩ E)) ⟨70749588064,1381187693⟩ (N (N E ⟨70766364936,1458134824⟩ E) ⟨70766365088,1444986704⟩ E))) ⟨70825085200,1633249457⟩ (N (N (N (N E ⟨70825085456,1608544589⟩ E) ⟨70850251552,1658854628⟩ (N E ⟨70850252160,1600486554⟩ E)) ⟨70867028480,1740033569⟩ (N (N E ⟨70867028688,1718686990⟩ E) ⟨70867028784,1708945411⟩ E)) ⟨70867028992,1688074859⟩ (N (N (N E ⟨70900583872,1745937500⟩ E) ⟨70900584704,1663361889⟩ (N E ⟨70900586368,1512378518⟩ E)) ⟨70925748640,1941677713⟩ (N (N E ⟨70934137104,1986865795⟩ E) ⟨70934137208,1974587193⟩ E)))))) ⟨70934137312,1962403517⟩ (N (N (N (N (N (N (N E ⟨70934137520,1938317424⟩ E) ⟨70934137728,1914600582⟩ (N E ⟨70934137936,1891246201⟩ E)) ⟨70934138144,1868247640⟩ (N (N E ⟨70934138560,1823292115⟩ E) ⟨70934138976,1779683648⟩ (N E ⟨70934139392,1737373987⟩ E))) ⟨70934140640,1617784893⟩ (N (N (N E ⟨70934141056,1580226720⟩ E) ⟨70934142976,1420381457⟩ (N E ⟨70967691872,2061158591⟩ E)) ⟨70984469104,2117190646⟩ (N (N E ⟨70984469160,2110170001⟩ E) ⟨70984469312,2091260458⟩ E))) ⟨70984469728,2040582806⟩ (N (N (N (N E ⟨71043189112,2361179887⟩ E) ⟨71043189216,2346610841⟩ (N E ⟨71068355568,2365116209⟩ E)) ⟨71068355776,2336314258⟩ (N (N E ⟨71068356192,2280016634⟩ E) ⟨71068356384,2254606601⟩ (N E ⟨71068356800,2200757334⟩ E))) ⟨71068357632,2097806599⟩ (N (N (N E ⟨71085132496,2468303226⟩ E) ⟨71085132800,2424339420⟩ (N E ⟨71101909936,2498367647⟩ E)) ⟨71101910240,2454015554⟩ (N (N E ⟨71101910848,2368231463⟩ E) ⟨71135465728,2425206911⟩ E)))) ⟨71143852864,2675952866⟩ (N (N (N (N (N E ⟨71152241224,2748868733⟩ E) ⟨71152241328,2731960330⟩ (N E ⟨71152241432,2715182033⟩ E)) ⟨71152241536,2698532640⟩ (N (N E ⟨71152241952,2633200514⟩ E) ⟨71169018896,2741114667⟩ (N E ⟨71169019648,2622862155⟩ E))) ⟨71185795888,2844737817⟩ (N (N (N E ⟨71185796096,2809996363⟩ E) ⟨71202573120,2909913683⟩ (N E ⟨71261293232,3180900751⟩ E)) ⟨71261293440,3141979921⟩ (N (N E ⟨71269682560,3083169201⟩ E) ⟨71286459584,3188481743⟩ E))) ⟨71303236568,3304492699⟩ (N (N (N (N E ⟨71303236720,3275014266⟩ E) ⟨71303237024,3217039180⟩ (N E ⟨71303237136,3196004429⟩ E)) ⟨71303237440,3139772410⟩ (N (N E ⟨71370345344,3619904491⟩ E) ⟨71370345448,3597741743⟩ E)) ⟨71370345552,3575748739⟩ (N (N (N E ⟨71370345760,3532265730⟩ E) ⟨71370345864,3510772653⟩ (N E ⟨71370345968,3489443174⟩ E)) ⟨71370346176,3447269043⟩ (N (N E ⟨71370347008,3284825021⟩ E) ⟨71370348672,2987709215⟩ E))))) ⟨71403899904,3745497722⟩ (N (N (N (N (N (N E ⟨71420677344,3773042578⟩ E) ⟨71462620272,3994351746⟩ (N E ⟨71471009952,3789328716⟩ E)) ⟨71471010368,3699325567⟩ (N (N E ⟨71471011584,3451160281⟩ E) ⟨71471013888,3035541833⟩ (N E ⟨71479397456,4081998565⟩ E))) ⟨71479397872,3983473972⟩ (N (N (N E ⟨71504563296,4199724892⟩ E) ⟨71504563600,4125362838⟩ (N E ⟨71504563648,4113772714⟩ E)) ⟨71504563808,4075432429⟩ (N (N E ⟨71504564416,3933759813⟩ E) ⟨71538118272,4227569083⟩ E))) ⟨71538118688,4126362338⟩ (N (N (N (N E ⟨71538119296,3983842031⟩ E) ⟨71538119520,3932892559⟩ (N E ⟨71538120128,3798657876⟩ E)) ⟨71538120512,3716828417⟩ (N (N E ⟨71538121344,3546971375⟩ E) ⟨71538122752,3281075879⟩ E)) ⟨71571672640,4406916156⟩ (N (N (N E ⟨71588449360,4622487389⟩ E) ⟨71588449568,4566275481⟩ (N E ⟨71588449984,4456397484⟩ E)) ⟨71622004128,4701926177⟩ (N (N E ⟨71622004544,4588995427⟩ E) ⟨71705890384,5087720185⟩ E)))) ⟨71705890592,5026315551⟩ (N (N (N (N (N E ⟨71705891008,4906266489⟩ E) ⟨71722667312,5264985379⟩ (N E ⟨71722667616,5172046085⟩ E)) ⟨71739445056,5193581166⟩ (N (N E ⟨71806553584,5666299604⟩ E) ⟨71806553792,5597815537⟩ (N E ⟨71806554208,5463930158⟩ E))) ⟨71806554624,5334032333⟩ (N (N (N E ⟨71806555456,5085637335⟩ E) ⟨71806556288,4851563615⟩ (N E ⟨71806557120,4630829728⟩ E)) ⟨71806557952,4422531958⟩ (N (N E ⟨71806558208,4360811591⟩ E) ⟨71823330912,5723111485⟩ E))) ⟨71873664768,5292566695⟩ (N (N (N (N E ⟨71873666432,4822112994⟩ E) ⟨71907217984,5856992598⟩ (N E ⟨71923994400,6232361261⟩ E)) ⟨71940771840,6248616222⟩ (N (N E ⟨71940772256,6099857213⟩ E) ⟨71940772864,5890329606⟩ E)) ⟨71957548800,6441628331⟩ (N (N (N E ⟨71974326304,6432896808⟩ E) ⟨71974326912,6210711176⟩ (N E ⟨72007882624,5952087208⟩ E)) ⟨72024657600,6871892121⟩ (N (N E ⟨72142098624,7389616249⟩ E) ⟨72175653088,7587921710⟩ E)))))))

noncomputable def tab2 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨72175654336,7063516044⟩ E) ⟨72242761824,8080762806⟩ (N E ⟨72242762240,7888653193⟩ E)) ⟨72343426016,8317444884⟩ (N (N E ⟨72343426432,8122234720⟩ E) ⟨72343427264,7748731334⟩ (N E ⟨72343427648,7583607950⟩ E))) ⟨72343428480,7240694588⟩ (N (N (N E ⟨72343429120,6990049945⟩ E) ⟨72376979872,8825249880⟩ (N E ⟨72410535040,8681119975⟩ E)) ⟨72410535360,8524215433⟩ (N (N E ⟨72410536576,7959429123⟩ E) ⟨72544753024,9455518097⟩ E))) ⟨72578307072,9902332772⟩ (N (N (N (N E ⟨72678970688,10439028257⟩ E) ⟨72678971520,9958557075⟩ (N E ⟨72678973184,9077905685⟩ E)) ⟨72746079456,10990530650⟩ (N (N E ⟨72746080000,10655959455⟩ E) ⟨72746080960,10096068313⟩ (N E ⟨72746082304,9372677031⟩ E))) ⟨72779634048,11139873131⟩ (N (N (N E ⟨72813188928,11105875671⟩ E) ⟨72813189760,10598343178⟩ (N E ⟨73148735488,12104668324⟩ E)) ⟨73215842496,13960550597⟩ (N (N E ⟨73215843712,13045242996⟩ E) ⟨73282953216,13092218008⟩ E)))) ⟨73551388416,15396192461⟩ (N (N (N (N (N E ⟨73551388672,15181324901⟩ E) ⟨73618496896,16291095525⟩ (N E ⟨74088259584,19807550595⟩ E)) ⟨74222477312,21055464219⟩ (N (N E ⟨74323139264,23714018079⟩ E) ⟨74490912768,23658131590⟩ (N E ⟨75900198912,39508252525⟩ E))) ⟨77309485184,58065467467⟩ (N (N (N E ⟨77309485312,57660655940⟩ E) ⟨77309485568,56861581616⟩ (N E ⟨77309485632,56663983892⟩ E)) ⟨77309486080,55304609886⟩ (N (N E ⟨77309486464,54171800066⟩ E) ⟨77309486720,53432710071⟩ E))) ⟨77309486848,53067900800⟩ (N (N (N (N E ⟨77309487744,50599666909⟩ E) ⟨77309488128,49585936005⟩ (N E ⟨77309490176,44588844334⟩ E)) ⟨77309492736,39196394389⟩ (N (N E ⟨77846356736,63602331360⟩ E) ⟨78114792448,66530373098⟩ E)) ⟨78383228160,69419392382⟩ (N (N (N E ⟨78383228928,66621352329⟩ E) ⟨78651663872,72261787581⟩ (N E ⟨78920099840,74031506677⟩ E)) ⟨79054323200,56833214558⟩ (N (N E ⟨79456972800,73216762336⟩ E) ⟨81604460544,81183335634⟩ E))))) ⟨85362556928,110311895384⟩ (N (N (N (N (N (N E ⟨85899431936,79111303097⟩ E) ⟨85899433344,64803250823⟩ (N E ⟨85899436032,38423148027⟩ E)) ⟨90194400256,80671901826⟩ (N (N E ⟨90194401280,68661704304⟩ E) ⟨91268143104,71306668495⟩ (N E ⟨91670798336,48367897901⟩ E))) ⟨92341885440,67628919902⟩ (N (N (N E ⟨92341886976,49536554442⟩ E) ⟨92878756608,65677920649⟩ (N E ⟨93147192320,63103400105⟩ E)) ⟨93415628800,51392597158⟩ (N (N E ⟨94489370944,49458108020⟩ E) ⟨94489373952,20013047782⟩ E))) ⟨94489374016,19521350956⟩ (N (N (N (N E ⟨94489374240,17848583852⟩ E) ⟨94489378816,160224349⟩ (N E ⟨94824916768,33643794541⟩ E)) ⟨94824918272,20261668579⟩ (N (N E ⟨96099990272,2254255576⟩ E) ⟨96099991552,206735025⟩ E)) ⟨96401976576,21395625128⟩ (N (N (N E ⟨96569750560,9189083277⟩ E) ⟨96569752064,3016013205⟩ (N E ⟨96569752224,2565230877⟩ E)) ⟨96636861376,1857100291⟩ (N (N E ⟨96636861440,1714381431⟩ E) ⟨96636862464,221539557⟩ E)))) ⟨96972405248,3075186906⟩ (N (N (N (N (N E ⟨97844822016,252482848⟩ E) ⟨97979036384,11505391687⟩ (N E ⟨97979037888,4280913909⟩ E)) ⟨98046145168,12019383510⟩ (N (N E ⟨98046146528,5136433970⟩ E) ⟨98046147328,2484663355⟩ (N E ⟨98046148608,257241968⟩ E))) ⟨98146809536,6363305765⟩ (N (N (N E ⟨98146810368,3237047870⟩ E) ⟨98146811904,259572619⟩ (N E ⟨98281026216,11958562382⟩ E)) ⟨98281027376,5905315798⟩ (N (N E ⟨98281029632,262627654⟩ E) ⟨98314581856,5709313651⟩ E))) ⟨98314581936,5379491981⟩ (N (N (N (N E ⟨98314582688,2780904498⟩ E) ⟨98314584064,263381846⟩ (N E ⟨98381692928,264878549⟩ E)) ⟨98448800768,1880376436⟩ (N (N E ⟨98448801792,266359493⟩ E) ⟨98918562944,1627877613⟩ E)) ⟨98918563232,1065129275⟩ (N (N (N E ⟨98918563840,276266374⟩ E) ⟨99019225184,4806279853⟩ (N E ⟨99019225856,2584484318⟩ E)) ⟨99103111840,2866507336⟩ (N (N E ⟨99186997920,2875130544⟩ E) ⟨99354770432,1951279355⟩ E)))))) ⟨99455433216,3395897956⟩ (N (N (N (N (N (N (N E ⟨99472209208,8567411725⟩ E) ⟨99472209888,5388263487⟩ (N E ⟨99497374956,8977577317⟩ E)) ⟨99497375536,6141282325⟩ (N (N E ⟨99522543584,316894800⟩ E) ⟨99556095440,7807867754⟩ (N E ⟨99556096192,4521716543⟩ E))) ⟨99790978528,994774472⟩ (N (N (N E ⟨99790979072,292343642⟩ E) ⟨99891640912,3188291103⟩ (N E ⟨99891641248,2229864842⟩ E)) ⟨99891641664,1289595007⟩ (N (N E ⟨99891641744,1139328223⟩ E) ⟨99891642368,293989719⟩ E))) ⟨99992305312,703443749⟩ (N (N (N (N E ⟨99992305664,295590471⟩ E) ⟨100059413984,1005190171⟩ (N E ⟨100059414528,296632190⟩ E)) ⟨100105549616,6248061920⟩ (N (N E ⟨100126523392,297653366⟩ E) ⟨100185241568,5499848469⟩ (N E ⟨100193631648,1122832782⟩ E))) ⟨100193632032,538984544⟩ (N (N (N E ⟨100193632064,500195058⟩ E) ⟨100193632256,298653847⟩ (N E ⟨100260740960,464243722⟩ E)) ⟨100327849280,1309429197⟩ (N (N E ⟨100344625344,4626030615⟩ E) ⟨100495622144,302895926⟩ E)))) ⟨100680170400,2283816286⟩ (N (N (N (N (N E ⟨100680170816,1324073794⟩ E) ⟨100680171520,305274943⟩ (N E ⟨100713724276,4004866175⟩ E)) ⟨100713724856,2223049757⟩ (N (N E ⟨100713725952,305689821⟩ E) ⟨100764056688,1774028868⟩ (N E ⟨100764056736,1664927879⟩ E))) ⟨100764056976,1173541128⟩ (N (N (N E ⟨100764057152,869728447⟩ E) ⟨100764057520,385221871⟩ (N E ⟨100764057600,306301864⟩ E)) ⟨100831165856,1146245184⟩ (N (N E ⟨100831166464,307098665⟩ E) ⟨100864720544,726190532⟩ E))) ⟨100864720896,307488777⟩ (N (N (N (N E ⟨100898273588,4255089520⟩ E) ⟨100898273928,3103105611⟩ (N E ⟨100898274608,1364569771⟩ E)) ⟨100898275328,307873346⟩ (N (N E ⟨100931829760,308252356⟩ E) ⟨100965383936,595717302⟩ E)) ⟨100965384192,308625792⟩ (N (N (N E ⟨101032493024,340041529⟩ E) ⟨101066047488,309712523⟩ (N E ⟨101099600880,2101279625⟩ E)) ⟨101099601296,1184774355⟩ (N (N E ⟨101099601312,1154952112⟩ E) ⟨101099601728,517048284⟩ E))))) ⟨101099601920,310063528⟩ (N (N (N (N (N (N E ⟨101116378432,1340450317⟩ E) ⟨101133155248,2268637311⟩ (N E ⟨101133156000,732043538⟩ E)) ⟨101133156192,479268296⟩ (N (N E ⟨101133156352,310408892⟩ E) ⟨101166710496,642263482⟩ (N E ⟨101166710784,310748602⟩ E))) ⟨101200264768,880882926⟩ (N (N (N E ⟨101250596000,1686512006⟩ E) ⟨101250596416,882066557⟩ (N E ⟨101250596864,311573054⟩ E)) ⟨101254789768,3130168317⟩ (N (N E ⟨101300928160,735419311⟩ E) ⟨101321898936,2257837150⟩ E))) ⟨101468700096,1106834497⟩ (N (N (N (N E ⟨101468700208,913047089⟩ E) ⟨101468700304,762325310⟩ (N E ⟨101468700672,313549502⟩ E)) ⟨101535808912,1197718980⟩ (N (N E ⟨101535809344,523287287⟩ E) ⟨101552586144,1168052884⟩ E)) ⟨101552586464,648793377⟩ (N (N (N E ⟨101552586560,523502181⟩ E) ⟨101552586752,314244900⟩ (N E ⟨101569363600,764164905⟩ E)) ⟨101569363808,485016017⟩ (N (N E ⟨101611306288,1389196497⟩ E) ⟨101636472752,395599341⟩ E)))) ⟨101636472832,314904055⟩ (N (N (N (N (N E ⟨101686804032,891412305⟩ E) ⟨101686804112,766208001⟩ (N E ⟨101686804480,315282088⟩ E)) ⟨101737135520,1172807480⟩ (N (N E ⟨101737135728,816001416⟩ E) ⟨101737136128,315646986⟩ (N E ⟨101787467616,487434542⟩ E))) ⟨101804244848,468738973⟩ (N (N (N E ⟨101804244992,316113030⟩ E) ⟨101837799424,316337253⟩ (N E ⟨101904907960,710523562⟩ E)) ⟨101904908128,488609486⟩ (N (N E ⟨101904908288,316768058⟩ E) ⟨101921685152,745983178⟩ E))) ⟨101930073596,1010656676⟩ (N (N (N (N E ⟨101930074112,316923535⟩ E) ⟨101938462720,316974623⟩ (N E ⟨101955239536,819623632⟩ E)) ⟨101955239632,676851836⟩ (N (N E ⟨101955239936,317075694⟩ E) ⟨101972017152,317175288⟩ E)) ⟨101988794176,528427774⟩ (N (N (N E ⟨101988794368,317273404⟩ E) ⟨102005571200,795598303⟩ (N E ⟨102005571408,508875017⟩ E)) ⟨102005571584,317370043⟩ (N (N E ⟨102039126016,317558881⟩ E) ⟨102106234792,408044956⟩ E)))))))

noncomputable def tab3 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨102123011952,471568212⟩ E) ⟨102123012096,318005047⟩ (N E ⟨102173343528,560519867⟩ E)) ⟨102173343552,530124571⟩ (N (N E ⟨102173343744,318254933⟩ E) ⟨102223675216,510751953⟩ (N E ⟨102223675248,472326304⟩ E))) ⟨102223675392,318491431⟩ (N (N (N E ⟨102257229624,540868356⟩ E) ⟨102257229824,318641649⟩ (N E ⟨102274006808,582188410⟩ E)) ⟨102274007040,318714522⟩ (N (N E ⟨102290784256,318785903⟩ E) ⟨102299172704,491895569⟩ E))) ⟨102299172864,318821034⟩ (N (N (N (N E ⟨102324338648,358606077⟩ E) ⟨102324338688,318924188⟩ (N E ⟨102341115904,318991089⟩ E)) ⟨102349504512,319023980⟩ (N (N E ⟨102391447336,562339169⟩ E) ⟨102391447552,319182826⟩ (N E ⟨102416613184,532005893⟩ E))) ⟨102416613376,319273646⟩ (N (N (N E ⟨102425001984,319303171⟩ E) ⟨102441779032,502522449⟩ (N E ⟨102441779128,392648455⟩ E)) ⟨102441779200,319361098⟩ (N (N E ⟨102458556416,319417527⟩ E) ⟨102475333632,319472457⟩ E)))) ⟨102492110848,319525889⟩ (N (N (N (N (N E ⟨102517276672,319603224⟩ E) ⟨102538248192,319665093⟩ (N E ⟨102584385536,319792947⟩ E)) ⟨102592774144,319814974⟩ (N (N E ⟨102609551360,319857900⟩ E) ⟨102634717184,319919471⟩ (N E ⟨102651494400,319958640⟩ E))) ⟨102659883008,319977661⟩ (N (N (N E ⟨102668271616,319996305⟩ E) ⟨102676660224,320014574⟩ (N E ⟨102685048832,320032467⟩ E)) ⟨102693437440,320049984⟩ (N (N E ⟨102710214656,320083889⟩ E) ⟨102760546304,320176575⟩ E))) ⟨102802489344,320243463⟩ (N (N (N (N E ⟨102836043776,320290197⟩ E) ⟨102852820992,320311303⟩ (N E ⟨102869598208,320330904⟩ E)) ⟨102877986816,320340138⟩ (N (N E ⟨102886375424,320348997⟩ E) ⟨102894764032,320357478⟩ E)) ⟨102903152640,320365582⟩ (N (N (N E ⟨102911541248,320373310⟩ E) ⟨102928318464,320387635⟩ (N E ⟨102978650112,320421564⟩ E)) ⟨103003815936,320433440⟩ (N (N E ⟨103012204544,320436644⟩ E) ⟨103020593152,320439472⟩ E))))) ⟨103037370368,320443996⟩ (N (N (N (N (N (N E ⟨103079313536,208253265⟩ E) ⟨103079313664,120294753⟩ (N E ⟨103079313792,56434938⟩ E)) ⟨103079313920,16522152⟩ (N (N E ⟨103079314048,391458⟩ E) ⟨103213531648,16522152⟩ (N E ⟨103213531776,391458⟩ E))) ⟨103347749504,391458⟩ (N (N (N E ⟨103884620928,7743374⟩ E) ⟨103884621056,7703420⟩ (N E ⟨103884621184,7663724⟩ E)) ⟨103884621312,7624283⟩ (N (N E ⟨103884621440,7585096⟩ E) ⟨103884621568,7546161⟩ E))) ⟨103884621696,7507476⟩ (N (N (N (N E ⟨103884621824,7469038⟩ E) ⟨103884621952,7430847⟩ (N E ⟨103884622080,7392899⟩ E)) ⟨103884622208,7355194⟩ (N (N E ⟨103884622336,7317728⟩ E) ⟨103884622464,7280502⟩ E)) ⟨103884622592,7243512⟩ (N (N (N E ⟨103884622720,7206757⟩ E) ⟨103884622848,7170235⟩ (N E ⟨103884622976,7133944⟩ E)) ⟨103884623104,7097883⟩ (N (N E ⟨103884623232,7062050⟩ E) ⟨103884623360,7026443⟩ E)))) ⟨103884623488,6991060⟩ (N (N (N (N (N E ⟨103884623744,6920961⟩ E) ⟨103884623872,6886241⟩ (N E ⟨103884624000,6851738⟩ E)) ⟨103884624128,6817452⟩ (N (N E ⟨103884624256,6783381⟩ E) ⟨103884624384,6749522⟩ (N E ⟨103884624512,6715874⟩ E))) ⟨103884624768,6649206⟩ (N (N (N E ⟨103884624896,6616182⟩ E) ⟨103884625152,6550749⟩ (N E ⟨103884625536,6454109⟩ E)) ⟨103884625664,6422292⟩ (N (N E ⟨103884625792,6390672⟩ E) ⟨103884625920,6359246⟩ E))) ⟨103884626304,6266122⟩ (N (N (N (N E ⟨103884626816,6144594⟩ E) ⟨103884627200,6055379⟩ (N E ⟨103884627328,6026001⟩ E)) ⟨103884627584,5967779⟩ (N (N E ⟨103884627968,5881758⟩ E) ⟨104018838656,38351576⟩ E)) ⟨104018838784,38153692⟩ (N (N (N E ⟨104018838912,37957083⟩ E) ⟨104018839040,37761741⟩ (N E ⟨104018839168,37567655⟩ E)) ⟨104018839296,37374816⟩ (N (N E ⟨104018839424,37183214⟩ E) ⟨104018839552,36992839⟩ E)))))) ⟨104018839680,36803682⟩ (N (N (N (N (N (N (N E ⟨104018839808,36615735⟩ E) ⟨104018839936,36428986⟩ (N E ⟨104018840064,36243429⟩ E)) ⟨104018840192,36059052⟩ (N (N E ⟨104018840448,35693806⟩ E) ⟨104018840576,35512919⟩ (N E ⟨104018840704,35333178⟩ E))) ⟨104018840832,35154574⟩ (N (N (N E ⟨104018840960,34977098⟩ E) ⟨104018841472,34278307⟩ (N E ⟨104018841600,34106345⟩ E)) ⟨104018841856,33765649⟩ (N (N E ⟨104018842752,32606248⟩ E) ⟨104018843392,31808491⟩ E))) ⟨104018844160,30883143⟩ (N (N (N (N E ⟨104018844544,30433100⟩ E) ⟨104018845184,29701110⟩ (N E ⟨104018845312,29557365⟩ E)) ⟨104018845696,29131321⟩ (N (N E ⟨104153056512,91890686⟩ E) ⟨104153056640,91417168⟩ (N E ⟨104153056768,90946698⟩ E))) ⟨104153056896,90479255⟩ (N (N (N E ⟨104153057024,90014814⟩ E) ⟨104153057152,89553353⟩ (N E ⟨104153057280,89094848⟩ E)) ⟨104153057408,88639277⟩ (N (N E ⟨104153057536,88186617⟩ E) ⟨104153057664,87736846⟩ E)))) ⟨104153057792,87289942⟩ (N (N (N (N (N E ⟨104153057920,86845883⟩ E) ⟨104153058048,86404646⟩ (N E ⟨104153058176,85966212⟩ E)) ⟨104153058304,85530558⟩ (N (N E ⟨104153058432,85097663⟩ E) ⟨104153058560,84667506⟩ (N E ⟨104153058688,84240066⟩ E))) ⟨104153058816,83815324⟩ (N (N (N E ⟨104153058944,83393257⟩ E) ⟨104153059072,82973847⟩ (N E ⟨104153059328,82142915⟩ E)) ⟨104153059456,81731354⟩ (N (N E ⟨104153059712,80915943⟩ E) ⟨104153059968,80110686⟩ E))) ⟨104153060096,79711817⟩ (N (N (N (N E ⟨104153060224,79315431⟩ E) ⟨104153060480,78530030⟩ (N E ⟨104153061376,75856633⟩ E)) ⟨104153062144,73655234⟩ (N (N E ⟨104153063424,70160892⟩ E) ⟨104287274496,167322213⟩ E)) ⟨104287274624,166462218⟩ (N (N (N E ⟨104287274752,165607748⟩ E) ⟨104287274880,164758759⟩ (N E ⟨104287275008,163915209⟩ E)) ⟨104287275136,163077057⟩ (N (N E ⟨104287275264,162244261⟩ E) ⟨104287275392,161416780⟩ E))))) ⟨104287275520,160594573⟩ (N (N (N (N (N (N E ⟨104287275648,159777600⟩ E) ⟨104287275776,158965821⟩ (N E ⟨104287276032,157357688⟩ E)) ⟨104287276160,156561255⟩ (N (N E ⟨104287276288,155769859⟩ E) ⟨104287276416,154983463⟩ (N E ⟨104287276544,154202029⟩ E))) ⟨104287276672,153425518⟩ (N (N (N E ⟨104287276928,151887121⟩ E) ⟨104287277184,150367976⟩ (N E ⟨104287277568,148124730⟩ E)) ⟨104287277952,145923201⟩ (N (N E ⟨104287278720,141641611⟩ E) ⟨104287280128,134192395⟩ E))) ⟨104421492352,265645031⟩ (N (N (N (N E ⟨104421492480,264281444⟩ E) ⟨104421492608,262926604⟩ (N E ⟨104421492736,261580444⟩ E)) ⟨104421492864,260242897⟩ (N (N E ⟨104421492992,258913898⟩ E) ⟨104421493120,257593381⟩ E)) ⟨104421493248,256281280⟩ (N (N (N E ⟨104421493376,254977533⟩ E) ⟨104421493504,253682074⟩ (N E ⟨104421493760,251115769⟩ E)) ⟨104421493888,249844799⟩ (N (N E ⟨104421494016,248581868⟩ E) ⟨104421494272,246079881⟩ E)))) ⟨104421494528,243609325⟩ (N (N (N (N (N E ⟨104421494656,242385686⟩ E) ⟨104421494912,239961393⟩ (N E ⟨104421495168,237567365⟩ E)) ⟨104421495680,232868298⟩ (N (N E ⟨104421496320,227156804⟩ E) ⟨104421497344,218378112⟩ (N E ⟨104555710208,386149818⟩ E))) ⟨104555710336,384170219⟩ (N (N (N E ⟨104555710464,382203303⟩ E) ⟨104555710592,380248972⟩ (N E ⟨104555710720,378307131⟩ E)) ⟨104555710848,376377682⟩ (N (N E ⟨104555710976,374460531⟩ E) ⟨104555711104,372555585⟩ E))) ⟨104555711232,370662749⟩ (N (N (N (N E ⟨104555711360,368781933⟩ E) ⟨104555711488,366913043⟩ (N E ⟨104555711616,365055989⟩ E)) ⟨104555711744,363210682⟩ (N (N E ⟨104555711872,361377031⟩ E) ⟨104555712000,359554950⟩ E)) ⟨104555712128,357744350⟩ (N (N (N E ⟨104555712256,355945144⟩ E) ⟨104555712384,354157247⟩ (N E ⟨104555712512,352380573⟩ E)) ⟨104555712640,350615038⟩ (N (N E ⟨104555712896,347117049⟩ E) ⟨104555713024,345384429⟩ E)))))))

noncomputable def tab4 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨104555713408,340251097⟩ E) ⟨104555713664,336881845⟩ (N E ⟨104555713792,335212874⟩ E)) ⟨104555714176,330267653⟩ (N (N E ⟨104555714560,325413379⟩ E) ⟨104555716608,300979524⟩ (N E ⟨104689928064,528588957⟩ E))) ⟨104689928192,525882631⟩ (N (N (N E ⟨104689928320,523193621⟩ E) ⟨104689928448,520521794⟩ (N E ⟨104689928576,517867020⟩ E)) ⟨104689928704,515229167⟩ (N (N E ⟨104689928832,512608105⟩ E) ⟨104689928960,510003708⟩ E))) ⟨104689929088,507415847⟩ (N (N (N (N E ⟨104689929216,504844397⟩ E) ⟨104689929344,502289233⟩ (N E ⟨104689929472,499750230⟩ E)) ⟨104689929728,494720222⟩ (N (N E ⟨104689929856,492228974⟩ E) ⟨104689930112,487293394⟩ (N E ⟨104689930240,484848826⟩ E))) ⟨104689930368,482419584⟩ (N (N (N E ⟨104689930496,480005552⟩ E) ⟨104689930624,477606617⟩ (N E ⟨104689930752,475222665⟩ E)) ⟨104689931520,461227380⟩ (N (N E ⟨104689932032,452182996⟩ E) ⟨104689932288,447744022⟩ E)))) ⟨104689932672,441187293⟩ (N (N (N (N (N E ⟨104689933184,432630731⟩ E) ⟨104689934336,414124897⟩ (N E ⟨104824146176,685641829⟩ E)) ⟨104824146304,682144906⟩ (N (N E ⟨104824146432,678670273⟩ E) ⟨104824146560,675217758⟩ (N E ⟨104824146688,671787193⟩ E))) ⟨104824146816,668378410⟩ (N (N (N E ⟨104824146944,664991244⟩ E) ⟨104824147072,661625530⟩ (N E ⟨104824147328,654957807⟩ E)) ⟨104824147456,651655476⟩ (N (N E ⟨104824147584,648373954⟩ E) ⟨104824147840,641872708⟩ E))) ⟨104824148096,635452827⟩ (N (N (N (N E ⟨104824148224,632273016⟩ E) ⟨104824148480,625972900⟩ (N E ⟨104824148736,619751139⟩ E)) ⟨104824148864,616669275⟩ (N (N E ⟨104824149248,607538028⟩ E) ⟨104824149632,598575336⟩ E)) ⟨104824150144,586880855⟩ (N (N (N E ⟨104824150528,578297144⟩ E) ⟨104824151296,561595838⟩ (N E ⟨104824152064,545493685⟩ E)) ⟨104958363904,873737158⟩ (N (N E ⟨104958364160,864853062⟩ E) ⟨104958364288,860453403⟩ E))))) ⟨104958364416,856081715⟩ (N (N (N (N (N (N E ⟨104958364544,851737785⟩ E) ⟨104958364672,847421402⟩ (N E ⟨104958364800,843132356⟩ E)) ⟨104958364928,838870438⟩ (N (N E ⟨104958365056,834635445⟩ E) ⟨104958365184,830427171⟩ (N E ⟨104958365312,826245413⟩ E))) ⟨104958365440,822089973⟩ (N (N (N E ⟨104958365568,817960650⟩ E) ⟨104958365824,809779573⟩ (N E ⟨104958366592,785843041⟩ E)) ⟨104958366848,778061427⟩ (N (N E ⟨104958366976,774206776⟩ E) ⟨104958369792,695141519⟩ E))) ⟨105092582016,1068369988⟩ (N (N (N (N E ⟨105092582144,1062941942⟩ E) ⟨105092582272,1057548362⟩ (N E ⟨105092582400,1052188985⟩ E)) ⟨105092582528,1046863551⟩ (N (N E ⟨105092582656,1041571801⟩ E) ⟨105092582784,1036313480⟩ E)) ⟨105092582912,1031088334⟩ (N (N (N E ⟨105092583040,1025896114⟩ E) ⟨105092583424,1010514521⟩ (N E ⟨105092583808,995420420⟩ E)) ⟨105092584192,980607380⟩ (N (N E ⟨105092584576,966069138⟩ E) ⟨105092585088,947101756⟩ E)))) ⟨105092585472,933181255⟩ (N (N (N (N (N E ⟨105092586240,906099859⟩ E) ⟨105092587136,875735766⟩ (N E ⟨105092587520,863112789⟩ E)) ⟨105226799872,1292408599⟩ (N (N E ⟨105226800000,1285850659⟩ E) ⟨105226800128,1279334306⟩ (N E ⟨105226800256,1272859223⟩ E))) ⟨105226800384,1266425096⟩ (N (N (N E ⟨105226800640,1253678471⟩ E) ⟨105226800768,1247365360⟩ (N E ⟨105226800896,1241091979⟩ E)) ⟨105226801024,1234858027⟩ (N (N E ⟨105226801280,1222507226⟩ E) ⟨105226801408,1216389790⟩ E))) ⟨105226801664,1204269399⟩ (N (N (N (N E ⟨105226801792,1198265872⟩ E) ⟨105226801920,1192299748⟩ (N E ⟨105226802048,1186370747⟩ E)) ⟨105226802304,1174623007⟩ (N (N E ⟨105226802432,1168803722⟩ E) ⟨105226802688,1157272969⟩ E)) ⟨105226802816,1151560969⟩ (N (N (N E ⟨105226802944,1145884202⟩ E) ⟨105226803584,1118019814⟩ (N E ⟨105226803712,1112549047⟩ E)) ⟨105226804096,1096336493⟩ (N (N E ⟨105226804480,1080418470⟩ E) ⟨105226804864,1064788573⟩ E)))))) ⟨105226805248,1049440563⟩ (N (N (N (N (N (N (N E ⟨105361017728,1536671226⟩ E) ⟨105361017856,1528883780⟩ (N E ⟨105361017984,1521145654⟩ E)) ⟨105361018112,1513456474⟩ (N (N E ⟨105361018240,1505815868⟩ E) ⟨105361018368,1498223468⟩ (N E ⟨105361018496,1490678909⟩ E))) ⟨105361018624,1483181829⟩ (N (N (N E ⟨105361018752,1475731870⟩ E) ⟨105361018880,1468328677⟩ (N E ⟨105361019008,1460971898⟩ E)) ⟨105361019136,1453661183⟩ (N (N E ⟨105361019392,1439176564⟩ E) ⟨105361019776,1417786566⟩ E))) ⟨105361020032,1403747289⟩ (N (N (N (N E ⟨105361020160,1396792882⟩ E) ⟨105361020416,1383012918⟩ (N E ⟨105361020544,1376186724⟩ E)) ⟨105361021312,1336102965⟩ (N (N E ⟨105361022208,1291167028⟩ E) ⟨105361022976,1254146509⟩ (N E ⟨105495235712,1791735219⟩ E))) ⟨105495235840,1782678246⟩ (N (N (N E ⟨105495235968,1773678488⟩ E) ⟨105495236096,1764735511⟩ (N E ⟨105495236224,1755848885⟩ E)) ⟨105495236352,1747018185⟩ (N (N E ⟨105495236480,1738242987⟩ E) ⟨105495236608,1729522875⟩ E)))) ⟨105495236736,1720857432⟩ (N (N (N (N (N E ⟨105495236992,1703688913⟩ E) ⟨105495237248,1686734186⟩ (N E ⟨105495237376,1678335996⟩ E)) ⟨105495237504,1669990061⟩ (N (N E ⟨105495237760,1653453401⟩ E) ⟨105495238272,1620990215⟩ (N E ⟨105495238656,1597164902⟩ E))) ⟨105495239936,1520846759⟩ (N (N (N E ⟨105629453696,2063617883⟩ E) ⟨105629453824,2053213016⟩ (N E ⟨105629453952,2042873713⟩ E)) ⟨105629454080,2032599477⟩ (N (N E ⟨105629454208,2022389817⟩ E) ⟨105629454336,2012244247⟩ E))) ⟨105629454464,2002162282⟩ (N (N (N (N E ⟨105629454592,1992143446⟩ E) ⟨105629454848,1972293265⟩ (N E ⟨105629455104,1952689959⟩ E)) ⟨105629455232,1942979732⟩ (N (N E ⟨105629455360,1933329849⟩ E) ⟨105629455616,1914209321⟩ E)) ⟨105629455872,1895324820⟩ (N (N (N E ⟨105629456000,1885969988⟩ E) ⟨105629456128,1876672858⟩ (N E ⟨105629456256,1867433004⟩ E)) ⟨105629456384,1858250002⟩ (N (N E ⟨105629456512,1849123433⟩ E) ⟨105629456896,1822078178⟩ E))))) ⟨105629457024,1813173215⟩ (N (N (N (N (N (N E ⟨105629457280,1795526053⟩ E) ⟨105629457664,1769456296⟩ (N E ⟨105629457792,1760871750⟩ E)) ⟨105629458048,1743858420⟩ (N (N E ⟨105629458432,1718722202⟩ E) ⟨105763671296,2387672593⟩ (N E ⟨105763671552,2363640563⟩ E))) ⟨105763671680,2351738049⟩ (N (N (N E ⟨105763671808,2339910440⟩ E) ⟨105763672064,2316477679⟩ (N E ⟨105763672192,2304871412⟩ E)) ⟨105763672448,2281876348⟩ (N (N E ⟨105763672960,2236740986⟩ E) ⟨105763676160,1978577712⟩ E))) ⟨105897889280,2695988834⟩ (N (N (N (N E ⟨105897889408,2682412724⟩ E) ⟨105897889536,2668922051⟩ (N E ⟨105897889664,2655516170⟩ E)) ⟨105897889792,2642194442⟩ (N (N E ⟨105897889920,2628956233⟩ E) ⟨105897890048,2615800915⟩ E)) ⟨105897890176,2602727864⟩ (N (N (N E ⟨105897890304,2589736465⟩ E) ⟨105897890432,2576826105⟩ (N E ⟨105897890560,2563996177⟩ E)) ⟨105897890688,2551246081⟩ (N (N E ⟨105897890944,2525983004⟩ E) ⟨105897891072,2513468848⟩ E)))) ⟨105897891456,2476388951⟩ (N (N (N (N (N E ⟨105897891584,2464181276⟩ E) ⟨105897891840,2439990988⟩ (N E ⟨105897892608,2369181205⟩ E)) ⟨105897892736,2357630773⟩ (N (N E ⟨105897893888,2256782822⟩ E) ⟨106032107264,3019591488⟩ (N E ⟨106032107392,3004424210⟩ E))) ⟨106032107520,2989352141⟩ (N (N (N E ⟨106032107648,2974374565⟩ E) ⟨106032107776,2959490771⟩ (N E ⟨106032107904,2944700053⟩ E)) ⟨106032108032,2930001715⟩ (N (N E ⟨106032108288,2900879413⟩ E) ⟨106032108416,2886454083⟩ E))) ⟨106032108672,2857871693⟩ (N (N (N (N E ⟨106032108800,2843713302⟩ E) ⟨106032109184,2801761481⟩ (N E ⟨106032109312,2787949840⟩ E)) ⟨106032109440,2774223287⟩ (N (N E ⟨106032109696,2747022933⟩ E) ⟨106032110080,2706845013⟩ E)) ⟨106032110848,2628670937⟩ (N (N (N E ⟨106032110976,2615917896⟩ E) ⟨106032111104,2603242176⟩ (N E ⟨106032111616,2553301322⟩ E)) ⟨106166325120,3374824912⟩ (N (N E ⟨106166325248,3357894682⟩ E) ⟨106166325632,3307737658⟩ E)))))))

noncomputable def tab5 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨106166325888,3274819800⟩ E) ⟨106166326144,3242310828⟩ (N E ⟨106166326400,3210204655⟩ E)) ⟨106166326528,3194300746⟩ (N (N E ⟨106166326784,3162787592⟩ E) ⟨106166327296,3100919687⟩ (N E ⟨106166327808,3040558638⟩ E))) ⟨106300542976,3747752238⟩ (N (N (N E ⟨106300543104,3728974843⟩ E) ⟨106300543232,3710315023⟩ (N E ⟨106300543360,3691771894⟩ E)) ⟨106300543488,3673344580⟩ (N (N E ⟨106300543616,3655032214⟩ E) ⟨106300543744,3636833936⟩ E))) ⟨106300543872,3618748892⟩ (N (N (N (N E ⟨106300544128,3582915136⟩ E) ⟨106300544256,3565164754⟩ (N E ⟨106300544384,3547524270⟩ E)) ⟨106300544640,3512569736⟩ (N (N E ⟨106300545024,3460941988⟩ E) ⟨106300545152,3443943991⟩ (N E ⟨106300545408,3410260219⟩ E))) ⟨106300545920,3344120276⟩ (N (N (N E ⟨106300546688,3247890661⟩ E) ⟨106300547072,3201075113⟩ (N E ⟨106434760832,4138004154⟩ E)) ⟨106434760960,4117297548⟩ (N (N E ⟨106434761216,4076271836⟩ E) ⟨106434761344,4055950796⟩ E)))) ⟨106434761472,4035756358⟩ (N (N (N (N (N E ⟨106434761600,4015687576⟩ E) ⟨106434761728,3995743510⟩ (N E ⟨106434761856,3975923233⟩ E)) ⟨106434761984,3956225821⟩ (N (N E ⟨106434762368,3897861683⟩ E) ⟨106434762496,3878646676⟩ (N E ⟨106434763264,3765812161⟩ E))) ⟨106434763648,3710935089⟩ (N (N (N E ⟨106434764160,3639312697⟩ E) ⟨106434764416,3604150098⟩ (N E ⟨106434764800,3552199377⟩ E)) ⟨106568978816,4522487385⟩ (N (N E ⟨106568978944,4499913592⟩ E) ⟨106568979200,4455187392⟩ E))) ⟨106568979712,4367391348⟩ (N (N (N (N E ⟨106568979968,4324305150⟩ E) ⟨106568980224,4281749501⟩ (N E ⟨106568980352,4260668180⟩ E)) ⟨106568980480,4239716573⟩ (N (N E ⟨106568980608,4218893720⟩ E) ⟨106568980864,4177630489⟩ E)) ⟨106568981376,4096607861⟩ (N (N (N E ⟨106568981632,4056833852⟩ E) ⟨106568981760,4037128038⟩ (N E ⟨106568982272,3959492311⟩ E)) ⟨106568982528,3921374948⟩ (N (N E ⟨106703196800,4919513303⟩ E) ⟨106703196928,4895019217⟩ E))))) ⟨106703197056,4870677540⟩ (N (N (N (N (N (N E ⟨106703197184,4846487135⟩ E) ⟨106703197312,4822446873⟩ (N E ⟨106703197440,4798555637⟩ E)) ⟨106703197824,4727765046⟩ (N (N E ⟨106703198208,4658276357⟩ E) ⟨106703198336,4635397799⟩ (N E ⟨106703200256,4308506924⟩ E))) ⟨106837414656,5355130656⟩ (N (N (N E ⟨106837415040,5275736814⟩ E) ⟨106837415552,5172155289⟩ (N E ⟨106837415680,5146658489⟩ E)) ⟨106837415808,5121318764⟩ (N (N E ⟨106837415936,5096134953⟩ E) ⟨106837416704,4948242519⟩ E))) ⟨106837416832,4924118429⟩ (N (N (N (N E ⟨106837417600,4782423161⟩ E) ⟨106837417984,4713488648⟩ (N E ⟨106971632512,5806369308⟩ E)) ⟨106971632768,5748873187⟩ (N (N E ⟨106971632896,5720392275⟩ E) ⟨106971633152,5663958139⟩ E)) ⟨106971633280,5636002308⟩ (N (N (N E ⟨106971633408,5608218915⟩ E) ⟨106971633664,5553164349⟩ (N E ⟨106971633792,5525890656⟩ E)) ⟨106971634176,5445069055⟩ (N (N E ⟨106971634944,5287814671⟩ E) ⟨106971635712,5136201722⟩ E)))) ⟨107105850624,6210787836⟩ (N (N (N (N (N E ⟨107105851008,6119163319⟩ E) ⟨107105851520,5999612058⟩ (N E ⟨107105852672,5741126388⟩ E)) ⟨107105853184,5630722032⟩ (N (N E ⟨107240069120,6524160155⟩ E) ⟨107240070016,6303941624⟩ (N E ⟨107240070400,6212412891⟩ E))) ⟨107240071168,6034289734⟩ (N (N (N E ⟨107374287360,6900812643⟩ E) ⟨107374287744,6800250964⟩ (N E ⟨107374287872,6767138362⟩ E)) ⟨107374288256,6669003657⟩ (N (N E ⟨107374288384,6636688260⟩ E) ⟨107374288640,6572643104⟩ E))) ⟨107374288896,6509369379⟩ (N (N (N (N E ⟨107508505984,7173295248⟩ E) ⟨107508506240,7103987736⟩ (N E ⟨107508506624,7001589868⟩ E)) ⟨107642723072,7884846377⟩ (N (N E ⟨107642723968,7620619198⟩ E) ⟨107642724352,7510774532⟩ E)) ⟨107776941312,8273967539⟩ (N (N (N E ⟨107776941568,8193928331⟩ E) ⟨107776942080,8036735203⟩ (N E ⟨107911158656,8962650776⟩ E)) ⟨107911159808,8579272269⟩ (N (N E ⟨108179595264,9713220361⟩ E) ⟨108313812992,10304175640⟩ E)))))) ⟨108582248448,11532825879⟩ (N (N (N (N (N (N (N E ⟨108716466176,12169998792⟩ E) ⟨109119119360,14169550279⟩ (N E ⟨109387554816,15572935848⟩ E)) ⟨109521772544,16294777226⟩ (N (N E ⟨110595514368,22506452254⟩ E) ⟨111669256320,29210021225⟩ (N E ⟨111669256576,28929837604⟩ E))) ⟨111669256704,28791006768⟩ (N (N (N E ⟨111669256960,28515836841⟩ E) ⟨111669257088,28379485819⟩ (N E ⟨111669257216,28243949556⟩ E)) ⟨111669257344,28109222210⟩ (N (N E ⟨111669257472,27975297990⟩ E) ⟨111669257856,27578286886⟩ E))) ⟨111669257984,27447518209⟩ (N (N (N (N E ⟨111669258240,27188299995⟩ E) ⟨111669258368,27059839487⟩ (N E ⟨111669258624,26805188577⟩ E)) ⟨111669258752,26678987475⟩ (N (N E ⟨111669258880,26553528882⟩ E) ⟨111669259008,26428807555⟩ (N E ⟨111669259136,26304818298⟩ E))) ⟨111669259264,26181555955⟩ (N (N (N E ⟨111669259520,25937191605⟩ E) ⟨111669259648,25816079498⟩ (N E ⟨111669259904,25575970478⟩ E)) ⟨111669260032,25456963711⟩ (N (N E ⟨111669260288,25221021330⟩ E) ⟨111669260416,25104076101⟩ E)))) ⟨111669260544,24987808501⟩ (N (N (N (N (N E ⟨111669260800,24757287385⟩ E) ⟨111669261184,24416471402⟩ (N E ⟨111669261568,24081505030⟩ E)) ⟨111669261952,23752268098⟩ (N (N E ⟨111669262080,23643775309⟩ E) ⟨111669262336,23428643310⟩ (N E ⟨111669262848,23005676080⟩ E))) ⟨111669263232,22694705692⟩ (N (N (N E ⟨111669263488,22490310296⟩ E) ⟨111669263616,22388976217⟩ (N E ⟨111669264384,21792819594⟩ E)) ⟨112340353024,25133773399⟩ (N (N E ⟨112877223936,27861269372⟩ E) ⟨115158925312,39402098031⟩ E))) ⟨116903755776,47302916815⟩ (N (N (N (N E ⟨118648586240,53496941759⟩ E) ⟨120259199104,56844414277⟩ (N E ⟨120259199488,55960566098⟩ E)) ⟨120259199872,54943403955⟩ (N (N E ⟨120259201536,49177312645⟩ E) ⟨120259201792,48121788892⟩ E)) ⟨120259204096,37272248449⟩ (N (N (N E ⟨120259204992,32677936973⟩ E) ⟨120259207168,21644686635⟩ (N E ⟨123211994880,36190949140⟩ E)) ⟨123211997184,23649247629⟩ (N (N E ⟨124956827648,24847047501⟩ E) ⟨125627916288,25306100736⟩ E))))) ⟨126030569472,25580482236⟩ (N (N (N (N (N (N E ⟨126164787200,25671723688⟩ E) ⟨126299004928,25762843408⟩ (N E ⟨126567440384,25944688403⟩ E)) ⟨126701658112,26035399071⟩ (N (N E ⟨127909617664,26844133108⟩ E) ⟨128043835392,26933009019⟩ (N E ⟨128849142400,23758033010⟩ E))) ⟨128849144704,12146402664⟩ (N (N (N E ⟨128849145088,10538428373⟩ E) ⟨128849145728,8097739006⟩ (N E ⟨128849145856,7646646621⟩ E)) ⟨128849145984,7208155569⟩ (N (N E ⟨128849146368,5969173862⟩ E) ⟨128849147392,3237164937⟩ E))) ⟨128849147520,2954823681⟩ (N (N (N (N E ⟨128849147776,2429690184⟩ E) ⟨128849148416,1346617606⟩ (N E ⟨128849149312,372502625⟩ E)) ⟨129251803136,54156829⟩ (N (N E ⟨129520232576,15935715654⟩ E) ⟨129520234112,9210807693⟩ E)) ⟨129520237056,1389933150⟩ (N (N (N E ⟨129654452096,8288261933⟩ E) ⟨129654453760,3332645796⟩ (N E ⟨129788671488,3348220198⟩ E)) ⟨129788672128,2034921410⟩ (N (N E ⟨129788673920,102542944⟩ E) ⟨129922889600,2532708814⟩ E)))) ⟨129922889984,1822266333⟩ (N (N (N (N (N E ⟨129922891392,228666500⟩ E) ⟨130057109504,61498544⟩ (N E ⟨130191325568,1630191318⟩ E)) ⟨130191326720,315670815⟩ (N (N E ⟨130996629120,9576919911⟩ E) ⟨131265067648,1304003826⟩ (N E ⟨131265067904,962342715⟩ E))) ⟨131399283456,5620512261⟩ (N (N (N E ⟨131399284224,3526376923⟩ E) ⟨131533501312,5256415511⟩ (N E ⟨131533501440,4885755032⟩ E)) ⟨131533502336,2676032046⟩ (N (N E ⟨131533502848,1715875020⟩ E) ⟨131533503616,682532583⟩ E))) ⟨131533503872,444401699⟩ (N (N (N (N E ⟨131533504128,258191355⟩ E) ⟨131533504384,122999467⟩ (N E ⟨131533504512,74225795⟩ E)) ⟨131667720576,1723970158⟩ (N (N E ⟨131667722112,124453304⟩ E) ⟨131801938304,1731972741⟩ E)) ⟨131801939968,76380134⟩ (N (N (N E ⟨131936155904,1961602711⟩ E) ⟨131936157312,264918319⟩ (N E ⟨131936157696,77434193⟩ E)) ⟨132070374272,994642477⟩ (N (N E ⟨132204589696,6142805078⟩ E) ⟨132204590592,3608632501⟩ E)))))))

noncomputable def tab6 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨132204592256,703239096⟩ E) ⟨132338807296,6581417155⟩ (N E ⟨132338809344,1552941570⟩ E)) ⟨132473025664,4643480599⟩ (N (N E ⟨132473026304,3032470956⟩ E) ⟨132473027712,711103381⟩ (N E ⟨132607243392,4659213540⟩ E))) ⟨132607244800,1566528576⟩ (N (N (N E ⟨132741462656,1374909210⟩ E) ⟨132741463552,367948078⟩ (N E ⟨133009897216,3076463958⟩ E)) ⟨133009897600,2268234980⟩ (N (N E ⟨133009897728,2026914939⟩ E) ⟨133009898496,870752307⟩ E))) ⟨133009898752,594881260⟩ (N (N (N (N E ⟨133009899136,281287949⟩ E) ⟨133009899392,137731278⟩ (N E ⟨133009899520,85230236⟩ E)) ⟨133144115584,1806574257⟩ (N (N E ⟨133144116352,729644308⟩ E) ⟨133144117120,138918472⟩ (N E ⟨133144117248,86116379⟩ E))) ⟨133278332800,2812564392⟩ (N (N (N E ⟨133278333952,878824520⟩ E) ⟨133278334336,482373629⟩ (N E ⟨133278334976,86981035⟩ E)) ⟨133412550912,2049566957⟩ (N (N E ⟨133412551680,882747624⟩ E) ⟨133412552320,286778319⟩ E)))) ⟨133412552704,87823684⟩ (N (N (N (N (N E ⟨133546768000,3419017088⟩ E) ⟨133680985984,2840904146⟩ (N E ⟨133680986368,2064080127⟩ E)) ⟨133680987264,743260291⟩ (N (N E ⟨133680987392,609797909⟩ E) ⟨133680988160,89440943⟩ (N E ⟨133815204864,894053282⟩ E))) ⟨133815205248,492263255⟩ (N (N (N E ⟨133815205888,90214579⟩ E) ⟨133949422592,897664173⟩ (N E ⟨133949423232,293499006⟩ E)) ⟨133949423616,90964259⟩ (N (N E ⟨134083639424,2331678402⟩ E) ⟨134083639552,2084941570⟩ E))) ⟨134083639936,1429852188⟩ (N (N (N (N E ⟨134083640192,1063483878⟩ E) ⟨134083640704,496860385⟩ (N E ⟨134083641344,91689533⟩ E)) ⟨134217857536,1639584925⟩ (N (N E ⟨134217858688,296590729⟩ E) ⟨134217859072,92389963⟩ E)) ⟨134352076544,216563947⟩ (N (N (N E ⟨134486293120,1444381910⟩ E) ⟨134486293248,1252643901⟩ (N E ⟨134486293376,1074974784⟩ E)) ⟨134486293504,911295922⟩ (N (N E ⟨134486293632,761521358⟩ E) ⟨134486293760,625557927⟩ E))))) ⟨134486293888,503305367⟩ (N (N (N (N (N (N E ⟨134486294016,394656437⟩ E) ⟨134486294144,299497034⟩ (N E ⟨134486294528,93714619⟩ E)) ⟨134620510976,1256770849⟩ (N (N E ⟨134620511488,627946919⟩ E) ⟨134620511744,396346399⟩ (N E ⟨134620511872,300879273⟩ E))) ⟨134620512128,150006047⟩ (N (N (N E ⟨134620512256,94338048⟩ E) ⟨134754729216,630266148⟩ (N E ⟨134754729856,150821679⟩ E)) ⟨134888946432,1264726435⟩ (N (N E ⟨134888946560,1085647256⟩ E) ⟨134888946944,632514968⟩ E))) ⟨134888947072,509193770⟩ (N (N (N (N E ⟨134888947200,399560138⟩ E) ⟨134888947712,95505228⟩ (N E ⟨135023164160,1268553414⟩ E)) ⟨135023164288,1089019110⟩ (N (N E ⟨135023164416,923589843⟩ E) ⟨135023164544,772179014⟩ E)) ⟨135023164672,634692757⟩ (N (N (N E ⟨135023164928,401082838⟩ E) ⟨135023165056,304736143⟩ (N E ⟨135023165184,221868200⟩ E)) ⟨135023165440,96048277⟩ (N (N E ⟨135157382656,402548740⟩ E) ⟨135157383040,153063066⟩ E)))) ⟨135157383168,96563856⟩ (N (N (N (N (N E ⟨135291599872,929220249⟩ E) ⟨135291600128,638832862⟩ (N E ⟨135291600256,514509477⟩ E)) ⟨135291600384,403957358⟩ (N (N E ⟨135291600512,307061088⟩ E) ⟨135291600896,97051656⟩ (N E ⟨135425818368,224549458⟩ E))) ⟨135425818624,97511382⟩ (N (N (N E ⟨135560035456,781571749⟩ E) ⟨135560035584,642681946⟩ (N E ⟨135560035840,406600902⟩ E)) ⟨135560035968,309184911⟩ (N (N E ⟨135560036352,97942758⟩ E) ⟨135694253184,783717765⟩ E))) ⟨135694253440,519238146⟩ (N (N (N (N E ⟨135694253696,310170411⟩ E) ⟨135694253952,155558677⟩ (N E ⟨135694254080,98345523⟩ E)) ⟨135828471168,520681700⟩ (N (N E ⟨135828471424,311104482⟩ E) ⟨135828471552,226841938⟩ E)) ⟨135828471808,98719435⟩ (N (N (N E ⟨135962688896,522058204⟩ E) ⟨135962689152,311986785⟩ (N E ⟨135962689280,227518160⟩ E)) ⟨135962689408,156589595⟩ (N (N E ⟨135962689536,99064269⟩ E) ⟨136096906752,411181557⟩ E)))))) ⟨136096907136,157049895⟩ (N (N (N (N (N (N (N E ⟨136096907264,99379817⟩ E) ⟨136231124352,524608512⟩ (N E ⟨136231124608,313594832⟩ E)) ⟨136231124736,228736979⟩ (N (N E ⟨136231124992,99665889⟩ E) ⟨136365342336,314320003⟩ (N E ⟨136365342464,229279073⟩ E))) ⟨136365342592,157859052⟩ (N (N (N E ⟨136365342720,99922313⟩ E) ⟨136499560064,314992258⟩ (N E ⟨136499560320,158207513⟩ E)) ⟨136499560448,100148933⟩ (N (N E ⟨136633778048,158518332⟩ E) ⟨136633778176,100345615⟩ E))) ⟨136767995776,158791360⟩ (N (N (N (N E ⟨136767995904,100512239⟩ E) ⟨136902213632,100648704⟩ (N E ⟨137036431360,100754930⟩ E)) ⟨137170649088,100830851⟩ (N (N E ⟨137439084672,55697681⟩ E) ⟨137439084800,23869645⟩ (N E ⟨137439084928,5347966⟩ E))) ⟨137975956736,63925⟩ (N (N (N E ⟨137975956864,63678⟩ E) ⟨137975956992,63431⟩ (N E ⟨137975957120,63186⟩ E)) ⟨137975957248,62942⟩ (N (N E ⟨137975957376,62700⟩ E) ⟨137975957504,62458⟩ E)))) ⟨137975957632,62218⟩ (N (N (N (N (N E ⟨137975957760,61978⟩ E) ⟨137975957888,61740⟩ (N E ⟨137975958016,61503⟩ E)) ⟨137975958144,61268⟩ (N (N E ⟨137975958272,61033⟩ E) ⟨137975958400,60799⟩ (N E ⟨137975958528,60567⟩ E))) ⟨137975958656,60336⟩ (N (N (N E ⟨137975958784,60105⟩ E) ⟨137975958912,59876⟩ (N E ⟨137975959040,59648⟩ E)) ⟨137975959168,59421⟩ (N (N E ⟨137975959296,59195⟩ E) ⟨137975959424,58971⟩ E))) ⟨137975959552,58747⟩ (N (N (N (N E ⟨137975959680,58524⟩ E) ⟨137975959808,58303⟩ (N E ⟨137975959936,58082⟩ E)) ⟨137975960064,57863⟩ (N (N E ⟨137975960192,57644⟩ E) ⟨137975960448,57210⟩ E)) ⟨137975960576,56995⟩ (N (N (N E ⟨137975960704,56780⟩ E) ⟨137975960960,56355⟩ (N E ⟨137975961088,56143⟩ E)) ⟨137975961216,55933⟩ (N (N E ⟨137975961472,55515⟩ E) ⟨137975961600,55308⟩ E))))) ⟨137975961856,54896⟩ (N (N (N (N (N (N E ⟨137975961984,54691⟩ E) ⟨137975962240,54285⟩ (N E ⟨137975962368,54083⟩ E)) ⟨137975963008,53088⟩ (N (N E ⟨137975963520,52309⟩ E) ⟨137975963648,52116⟩ (N E ⟨138110174592,7763984⟩ E))) ⟨138110174720,7733958⟩ (N (N (N E ⟨138110174848,7704077⟩ E) ⟨138110174976,7674340⟩ (N E ⟨138110175104,7644747⟩ E)) ⟨138110175232,7615296⟩ (N (N E ⟨138110175360,7585987⟩ E) ⟨138110175488,7556819⟩ E))) ⟨138110175616,7527791⟩ (N (N (N (N E ⟨138110175744,7498902⟩ E) ⟨138110175872,7470152⟩ (N E ⟨138110176000,7441540⟩ E)) ⟨138110176128,7413064⟩ (N (N E ⟨138110176256,7384725⟩ E) ⟨138110176384,7356521⟩ E)) ⟨138110176512,7328452⟩ (N (N (N E ⟨138110176640,7300517⟩ E) ⟨138110176768,7272714⟩ (N E ⟨138110176896,7245044⟩ E)) ⟨138110177024,7217506⟩ (N (N E ⟨138110177152,7190098⟩ E) ⟨138110177280,7162820⟩ E)))) ⟨138110177408,7135672⟩ (N (N (N (N (N E ⟨138110177536,7108652⟩ E) ⟨138110177664,7081760⟩ (N E ⟨138110177792,7054995⟩ E)) ⟨138110177920,7028357⟩ (N (N E ⟨138110178432,6923053⟩ E) ⟨138110178560,6897036⟩ (N E ⟨138110178816,6845367⟩ E))) ⟨138110179072,6794182⟩ (N (N (N E ⟨138110179200,6768769⟩ E) ⟨138110179328,6743475⟩ (N E ⟨138110179584,6693240⟩ E)) ⟨138110180224,6569685⟩ (N (N E ⟨138110180480,6521062⟩ E) ⟨138110181248,6377871⟩ E))) ⟨138110181376,6354389⟩ (N (N (N (N E ⟨138244392320,28354691⟩ E) ⟨138244392448,28245033⟩ (N E ⟨138244392576,28135904⟩ E)) ⟨138244392704,28027303⟩ (N (N E ⟨138244392832,27919226⟩ E) ⟨138244392960,27811669⟩ E)) ⟨138244393088,27704630⟩ (N (N (N E ⟨138244393216,27598106⟩ E) ⟨138244393344,27492093⟩ (N E ⟨138244393472,27386590⟩ E)) ⟨138244393600,27281592⟩ (N (N E ⟨138244393728,27177098⟩ E) ⟨138244393856,27073103⟩ E)))))))

noncomputable def tab7 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨138244394112,26866603⟩ E) ⟨138244394240,26764092⟩ (N E ⟨138244394368,26662069⟩ E)) ⟨138244394496,26560533⟩ (N (N E ⟨138244394624,26459480⟩ E) ⟨138244394752,26358907⟩ (N E ⟨138244394880,26258811⟩ E))) ⟨138244395008,26159191⟩ (N (N (N E ⟨138244395136,26060043⟩ E) ⟨138244395392,25863153⟩ (N E ⟨138244395520,25765406⟩ E)) ⟨138244395648,25668120⟩ (N (N E ⟨138244395904,25474923⟩ E) ⟨138244396032,25379006⟩ E))) ⟨138244396288,25188525⟩ (N (N (N (N E ⟨138244396416,25093954⟩ E) ⟨138244396544,24999828⟩ (N E ⟨138244396672,24906142⟩ E)) ⟨138244396800,24812895⟩ (N (N E ⟨138244396928,24720085⟩ E) ⟨138244397696,24172246⟩ (N E ⟨138244397952,23993014⟩ E))) ⟨138244398464,23639509⟩ (N (N (N E ⟨138244398720,23465199⟩ E) ⟨138244398976,23292494⟩ (N E ⟨138244399104,23206737⟩ E)) ⟨138378610176,61658446⟩ (N (N E ⟨138378610304,61420221⟩ E) ⟨138378610432,61183146⟩ E)))) ⟨138378610560,60947215⟩ (N (N (N (N (N E ⟨138378610688,60712420⟩ E) ⟨138378610816,60478756⟩ (N E ⟨138378610944,60246216⟩ E)) ⟨138378611072,60014792⟩ (N (N E ⟨138378611200,59784480⟩ E) ⟨138378611328,59555272⟩ (N E ⟨138378611456,59327162⟩ E))) ⟨138378611584,59100144⟩ (N (N (N E ⟨138378611712,58874211⟩ E) ⟨138378611968,58425577⟩ (N E ⟨138378612096,58202864⟩ E)) ⟨138378612224,57981211⟩ (N (N E ⟨138378612352,57760613⟩ E) ⟨138378612480,57541064⟩ E))) ⟨138378612608,57322558⟩ (N (N (N (N E ⟨138378612864,56888649⟩ E) ⟨138378612992,56673236⟩ (N E ⟨138378613120,56458842⟩ E)) ⟨138378613248,56245461⟩ (N (N E ⟨138378613376,56033088⟩ E) ⟨138378613632,55611342⟩ E)) ⟨138378613888,55193558⟩ (N (N (N E ⟨138378614400,54369703⟩ E) ⟨138378614784,53761885⟩ (N E ⟨138378615168,53162543⟩ E)) ⟨138378615552,52571534⟩ (N (N E ⟨138378616064,51796246⟩ E) ⟨138378616448,51224147⟩ E))))) ⟨138378616832,50659929⟩ (N (N (N (N (N (N E ⟨138512828032,107610860⟩ E) ⟨138512828160,107195495⟩ (N E ⟨138512828288,106782133⟩ E)) ⟨138512828416,106370763⟩ (N (N E ⟨138512828544,105961373⟩ E) ⟨138512828672,105553952⟩ (N E ⟨138512828800,105148488⟩ E))) ⟨138512828928,104744971⟩ (N (N (N E ⟨138512829056,104343389⟩ E) ⟨138512829184,103943730⟩ (N E ⟨138512829312,103545985⟩ E)) ⟨138512829440,103150141⟩ (N (N E ⟨138512829568,102756188⟩ E) ⟨138512829696,102364115⟩ E))) ⟨138512829824,101973911⟩ (N (N (N (N E ⟨138512829952,101585567⟩ E) ⟨138512830080,101199070⟩ (N E ⟨138512830208,100814410⟩ E)) ⟨138512830336,100431578⟩ (N (N E ⟨138512830464,100050562⟩ E) ⟨138512830592,99671352⟩ E)) ⟨138512830720,99293938⟩ (N (N (N E ⟨138512830848,98918310⟩ E) ⟨138512830976,98544458⟩ (N E ⟨138512831232,97802040⟩ E)) ⟨138512831488,97066604⟩ (N (N E ⟨138512831616,96701480⟩ E) ⟨138512831744,96338072⟩ E)))) ⟨138512831872,95976371⟩ (N (N (N (N (N E ⟨138512832000,95616366⟩ E) ⟨138512832128,95258049⟩ (N E ⟨138512832256,94901410⟩ E)) ⟨138512832384,94546439⟩ (N (N E ⟨138512832512,94193128⟩ E) ⟨138512832640,93841466⟩ (N E ⟨138512832768,93491444⟩ E))) ⟨138512832896,93143054⟩ (N (N (N E ⟨138512833152,92451132⟩ E) ⟨138512833280,92107581⟩ (N E ⟨138512833408,91765626⟩ E)) ⟨138512833664,91086466⟩ (N (N E ⟨138512833792,90749243⟩ E) ⟨138512834176,89746901⟩ E))) ⟨138512834304,89415867⟩ (N (N (N (N E ⟨138512834432,89086358⟩ E) ⟨138512834560,88758367⟩ (N E ⟨138647045760,166753871⟩ E)) ⟨138647045888,166110220⟩ (N (N E ⟨138647046016,165469675⟩ E) ⟨138647046144,164832215⟩ E)) ⟨138647046272,164197824⟩ (N (N (N E ⟨138647046400,163566485⟩ E) ⟨138647046528,162938178⟩ (N E ⟨138647046656,162312887⟩ E)) ⟨138647046784,161690595⟩ (N (N E ⟨138647046912,161071284⟩ E) ⟨138647047040,160454937⟩ E)))))) ⟨138647047168,159841537⟩ (N (N (N (N (N (N (N E ⟨138647047296,159231067⟩ E) ⟨138647047424,158623511⟩ (N E ⟨138647047552,158018851⟩ E)) ⟨138647047680,157417072⟩ (N (N E ⟨138647047808,156818156⟩ E) ⟨138647047936,156222087⟩ (N E ⟨138647048064,155628850⟩ E))) ⟨138647048192,155038427⟩ (N (N (N E ⟨138647048320,154450803⟩ E) ⟨138647048448,153865963⟩ (N E ⟨138647048576,153283889⟩ E)) ⟨138647048704,152704567⟩ (N (N E ⟨138647048832,152127981⟩ E) ⟨138647049088,150982955⟩ E))) ⟨138647049216,150414484⟩ (N (N (N (N E ⟨138647049344,149848687⟩ E) ⟨138647049600,148725058⟩ (N E ⟨138647049728,148167195⟩ E)) ⟨138647049856,147611946⟩ (N (N E ⟨138647049984,147059298⟩ E) ⟨138647050240,145961743⟩ (N E ⟨138647050368,145416807⟩ E))) ⟨138647050496,144874414⟩ (N (N (N E ⟨138647051136,142200085⟩ E) ⟨138647051264,141672649⟩ (N E ⟨138647051648,140104954⟩ E)) ⟨138647052032,138558896⟩ (N (N E ⟨138647052160,138048289⟩ E) ⟨138647052288,137540034⟩ E)))) ⟨138781263744,237047756⟩ (N (N (N (N (N E ⟨138781263872,236134548⟩ E) ⟨138781264000,235225735⟩ (N E ⟨138781264128,234321293⟩ E)) ⟨138781264256,233421197⟩ (N (N E ⟨138781264384,232525421⟩ E) ⟨138781264512,231633940⟩ (N E ⟨138781264640,230746731⟩ E))) ⟨138781264768,229863767⟩ (N (N (N E ⟨138781264896,228985026⟩ E) ⟨138781265024,228110482⟩ (N E ⟨138781265152,227240112⟩ E)) ⟨138781265280,226373891⟩ (N (N E ⟨138781265408,225511797⟩ E) ⟨138781265536,224653805⟩ E))) ⟨138781265664,223799892⟩ (N (N (N (N E ⟨138781265792,222950034⟩ E) ⟨138781265920,222104209⟩ (N E ⟨138781266048,221262394⟩ E)) ⟨138781266176,220424566⟩ (N (N E ⟨138781266304,219590702⟩ E) ⟨138781266432,218760780⟩ E)) ⟨138781266560,217934777⟩ (N (N (N E ⟨138781266688,217112671⟩ E) ⟨138781266944,215480063⟩ (N E ⟨138781267072,214669517⟩ E)) ⟨138781267328,213059833⟩ (N (N E ⟨138781267456,212260652⟩ E) ⟨138781267584,211465217⟩ E))))) ⟨138781267840,209885500⟩ (N (N (N (N (N (N E ⟨138781267968,209101176⟩ E) ⟨138781268224,207543496⟩ (N E ⟨138781268352,206770098⟩ E)) ⟨138781268608,205234086⟩ (N (N E ⟨138781268992,202956727⟩ E) ⟨138781269120,202204637⟩ (N E ⟨138781269632,199230911⟩ E))) ⟨138781269888,197764559⟩ (N (N (N E ⟨138781270016,197036445⟩ E) ⟨138915481600,320307727⟩ (N E ⟨138915481728,319074957⟩ E)) ⟨138915481856,317848115⟩ (N (N E ⟨138915481984,316627168⟩ E) ⟨138915482112,315412081⟩ E))) ⟨138915482240,314202821⟩ (N (N (N (N E ⟨138915482368,312999354⟩ E) ⟨138915482496,311801647⟩ (N E ⟨138915482624,310609667⟩ E)) ⟨138915482752,309423381⟩ (N (N E ⟨138915482880,308242756⟩ E) ⟨138915483008,307067760⟩ E)) ⟨138915483136,305898361⟩ (N (N (N E ⟨138915483264,304734526⟩ E) ⟨138915483392,303576225⟩ (N E ⟨138915483520,302423425⟩ E)) ⟨138915483648,301276095⟩ (N (N E ⟨138915483776,300134204⟩ E) ⟨138915483904,298997722⟩ E)))) ⟨138915484032,297866616⟩ (N (N (N (N (N E ⟨138915484160,296740857⟩ E) ⟨138915484288,295620415⟩ (N E ⟨138915484416,294505259⟩ E)) ⟨138915484800,291191212⟩ (N (N E ⟨138915485056,289007735⟩ E) ⟨138915485184,287923676⟩ (N E ⟨138915485312,286844698⟩ E))) ⟨138915485568,284701870⟩ (N (N (N E ⟨138915485696,283637965⟩ E) ⟨138915485952,281525029⟩ (N E ⟨138915486080,280475944⟩ E)) ⟨138915486208,279431743⟩ (N (N E ⟨138915486464,277357888⟩ E) ⟨138915487232,271250759⟩ E))) ⟨138915487360,270249317⟩ (N (N (N (N E ⟨138915487616,268260265⟩ E) ⟨138915487744,267272605⟩ (N E ⟨139049699328,417373870⟩ E)) ⟨139049699456,415767520⟩ (N (N E ⟨139049699584,414168896⟩ E) ⟨139049699712,412577953⟩ E)) ⟨139049699840,410994646⟩ (N (N (N E ⟨139049699968,409418931⟩ E) ⟨139049700096,407850765⟩ (N E ⟨139049700224,406290105⟩ E)) ⟨139049700352,404736907⟩ (N (N E ⟨139049700480,403191128⟩ E) ⟨139049700608,401652726⟩ E)))))))

noncomputable def tab8 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨139049700864,398597885⟩ E) ⟨139049700992,397081362⟩ (N E ⟨139049701120,395572049⟩ E)) ⟨139049701248,394069904⟩ (N (N E ⟨139049701376,392574887⟩ E) ⟨139049701504,391086957⟩ (N E ⟨139049701632,389606074⟩ E))) ⟨139049701760,388132198⟩ (N (N (N E ⟨139049701888,386665289⟩ E) ⟨139049702016,385205308⟩ (N E ⟨139049702272,382305971⟩ E)) ⟨139049702400,380866538⟩ (N (N E ⟨139049702528,379433877⟩ E) ⟨139049702656,378007950⟩ E))) ⟨139049702784,376588719⟩ (N (N (N (N E ⟨139049702912,375176147⟩ E) ⟨139049703040,373770195⟩ (N E ⟨139049703168,372370826⟩ E)) ⟨139049703552,368211854⟩ (N (N E ⟨139049703680,366838452⟩ E) ⟨139049703808,365471452⟩ (N E ⟨139049703936,364110816⟩ E))) ⟨139049704064,362756511⟩ (N (N (N E ⟨139049704320,360066748⟩ E) ⟨139049704832,354761639⟩ (N E ⟨139049705088,352145745⟩ E)) ⟨139049705216,350846844⟩ (N (N E ⟨139049705472,348266970⟩ E) ⟨139183917056,527347199⟩ E)))) ⟨139183917184,525317595⟩ (N (N (N (N (N E ⟨139183917312,523297751⟩ E) ⟨139183917440,521287612⟩ (N E ⟨139183917568,519287121⟩ E)) ⟨139183917696,517296223⟩ (N (N E ⟨139183917824,515314863⟩ E) ⟨139183917952,513342986⟩ (N E ⟨139183918080,511380538⟩ E))) ⟨139183918208,509427464⟩ (N (N (N E ⟨139183918336,507483711⟩ E) ⟨139183918464,505549225⟩ (N E ⟨139183918592,503623953⟩ E)) ⟨139183918720,501707843⟩ (N (N E ⟨139183918848,499800843⟩ E) ⟨139183918976,497902900⟩ E))) ⟨139183919104,496013963⟩ (N (N (N (N E ⟨139183919232,494133980⟩ E) ⟨139183919360,492262901⟩ (N E ⟨139183919488,490400675⟩ E)) ⟨139183919616,488547252⟩ (N (N E ⟨139183919744,486702582⟩ E) ⟨139183919872,484866616⟩ E)) ⟨139183920128,481220596⟩ (N (N (N E ⟨139183920256,479410445⟩ E) ⟨139183920384,477608802⟩ (N E ⟨139183920512,475815620⟩ E)) ⟨139183920640,474030850⟩ (N (N E ⟨139183920768,472254445⟩ E) ⟨139183920896,470486359⟩ E))))) ⟨139183921024,468726544⟩ (N (N (N (N (N (N E ⟨139183921152,466974955⟩ E) ⟨139183921280,465231544⟩ (N E ⟨139183921408,463496266⟩ E)) ⟨139183921536,461769076⟩ (N (N E ⟨139183921792,458338779⟩ E) ⟨139183922048,454940294⟩ (N E ⟨139183922688,446580948⟩ E))) ⟨139183922944,443291049⟩ (N (N (N E ⟨139183923200,440031407⟩ E) ⟨139318134912,647731446⟩ (N E ⟨139318135040,645240922⟩ E)) ⟨139318135168,642762364⟩ (N (N E ⟨139318135296,640295702⟩ E) ⟨139318135424,637840869⟩ E))) ⟨139318135552,635397796⟩ (N (N (N (N E ⟨139318135680,632966416⟩ E) ⟨139318135808,630546662⟩ (N E ⟨139318135936,628138466⟩ E)) ⟨139318136064,625741763⟩ (N (N E ⟨139318136192,623356488⟩ E) ⟨139318136320,620982573⟩ E)) ⟨139318136448,618619956⟩ (N (N (N E ⟨139318136576,616268570⟩ E) ⟨139318136704,613928353⟩ (N E ⟨139318136832,611599240⟩ E)) ⟨139318136960,609281168⟩ (N (N E ⟨139318137088,606974075⟩ E) ⟨139318137216,604677898⟩ E)))) ⟨139318137344,602392575⟩ (N (N (N (N (N E ⟨139318137472,600118045⟩ E) ⟨139318137600,597854246⟩ (N E ⟨139318137728,595601118⟩ E)) ⟨139318137984,591126633⟩ (N (N E ⟨139318138112,588905156⟩ E) ⟨139318138240,586694112⟩ (N E ⟨139318138368,584493440⟩ E))) ⟨139318138496,582303083⟩ (N (N (N E ⟨139318138752,577953081⟩ E) ⟨139318138880,575793322⟩ (N E ⟨139318139008,573643647⟩ E)) ⟨139318139136,571504001⟩ (N (N E ⟨139318139264,569374327⟩ E) ⟨139318139392,567254570⟩ E))) ⟨139318139648,563044583⟩ (N (N (N (N E ⟨139318140032,556802605⟩ E) ⟨139318140160,554741196⟩ (N E ⟨139318140288,552689324⟩ E)) ⟨139318140544,548613977⟩ (N (N E ⟨139318140800,544576144⟩ E) ⟨139318140928,542571166⟩ E)) ⟨139452352896,777000554⟩ (N (N (N E ⟨139452353024,774018741⟩ E) ⟨139452353152,771051226⟩ (N E ⟨139452353280,768097928⟩ E)) ⟨139452353408,765158764⟩ (N (N E ⟨139452353536,762233654⟩ E) ⟨139452353664,759322518⟩ E)))))) ⟨139452353792,756425274⟩ (N (N (N (N (N (N (N E ⟨139452353920,753541843⟩ E) ⟨139452354048,750672147⟩ (N E ⟨139452354176,747816106⟩ E)) ⟨139452354304,744973644⟩ (N (N E ⟨139452354432,742144682⟩ E) ⟨139452354560,739329144⟩ (N E ⟨139452354688,736526953⟩ E))) ⟨139452354816,733738033⟩ (N (N (N E ⟨139452354944,730962309⟩ E) ⟨139452355072,728199706⟩ (N E ⟨139452355200,725450150⟩ E)) ⟨139452355328,722713566⟩ (N (N E ⟨139452355584,717279024⟩ E) ⟨139452355712,714580920⟩ E))) ⟨139452355840,711895497⟩ (N (N (N (N E ⟨139452356096,706562413⟩ E) ⟨139452356224,703914609⟩ (N E ⟨139452356352,701279204⟩ E)) ⟨139452356608,696045312⟩ (N (N E ⟨139452356736,693446687⟩ E) ⟨139452356992,688285737⟩ (N E ⟨139452357248,683172738⟩ E))) ⟨139452357376,680634054⟩ (N (N (N E ⟨139452357504,678107157⟩ E) ⟨139452357632,675591982⟩ (N E ⟨139452357760,673088464⟩ E)) ⟨139452358144,665647209⟩ (N (N E ⟨139452358400,660743480⟩ E) ⟨139452358656,655884850⟩ E)))) ⟨139586570752,920446716⟩ (N (N (N (N (N E ⟨139586570880,916917811⟩ E) ⟨139586571008,913405811⟩ (N E ⟨139586571136,909910620⟩ E)) ⟨139586571264,906432141⟩ (N (N E ⟨139586571392,902970279⟩ E) ⟨139586571520,899524937⟩ (N E ⟨139586571648,896096023⟩ E))) ⟨139586571776,892683441⟩ (N (N (N E ⟨139586571904,889287098⟩ E) ⟨139586572032,885906902⟩ (N E ⟨139586572160,882542760⟩ E)) ⟨139586572288,879194582⟩ (N (N E ⟨139586572416,875862275⟩ E) ⟨139586572544,872545751⟩ E))) ⟨139586572672,869244919⟩ (N (N (N (N E ⟨139586572800,865959690⟩ E) ⟨139586572928,862689976⟩ (N E ⟨139586573056,859435688⟩ E)) ⟨139586573184,856196740⟩ (N (N E ⟨139586573312,852973045⟩ E) ⟨139586573440,849764517⟩ E)) ⟨139586573568,846571069⟩ (N (N (N E ⟨139586573696,843392618⟩ E) ⟨139586573824,840229078⟩ (N E ⟨139586573952,837080366⟩ E)) ⟨139586574080,833946398⟩ (N (N E ⟨139586574208,830827091⟩ E) ⟨139586574336,827722364⟩ E))))) ⟨139586574592,821556320⟩ (N (N (N (N (N (N E ⟨139586574720,818494842⟩ E) ⟨139586574976,812414572⟩ (N E ⟨139586575232,806390689⟩ E)) ⟨139586575872,791573583⟩ (N (N E ⟨139586576256,782846616⟩ E) ⟨139586576384,779964392⟩ (N E ⟨139720788608,1075423275⟩ E))) ⟨139720788736,1071304164⟩ (N (N (N E ⟨139720788864,1067204767⟩ E) ⟨139720788992,1063124972⟩ (N E ⟨139720789120,1059064665⟩ E)) ⟨139720789248,1055023736⟩ (N (N E ⟨139720789376,1051002072⟩ E) ⟨139720789504,1046999565⟩ E))) ⟨139720789632,1043016104⟩ (N (N (N (N E ⟨139720789760,1039051582⟩ E) ⟨139720789888,1035105889⟩ (N E ⟨139720790016,1031178918⟩ E)) ⟨139720790144,1027270564⟩ (N (N E ⟨139720790272,1023380719⟩ E) ⟨139720790528,1015656141⟩ E)) ⟨139720790656,1011821199⟩ (N (N (N E ⟨139720790784,1008004350⟩ E) ⟨139720791040,1000424525⟩ (N E ⟨139720791168,996661346⟩ E)) ⟨139720791424,989187952⟩ (N (N E ⟨139720791552,985477538⟩ E) ⟨139720791680,981784515⟩ E)))) ⟨139720791936,974450252⟩ (N (N (N (N (N E ⟨139720792064,970808817⟩ E) ⟨139720792320,963576864⟩ (N E ⟨139720792448,959986155⟩ E)) ⟨139720792576,956412165⟩ (N (N E ⟨139720793216,938789767⟩ E) ⟨139720793600,928411079⟩ (N E ⟨139720793728,924983437⟩ E))) ⟨139720793984,918175502⟩ (N (N (N E ⟨139720794112,914795035⟩ E) ⟨139855006464,1241767851⟩ (N E ⟨139855006592,1237016167⟩ E)) ⟨139855006720,1232287203⟩ (N (N E ⟨139855006848,1227580829⟩ E) ⟨139855006976,1222896915⟩ E))) ⟨139855007104,1218235333⟩ (N (N (N (N E ⟨139855007232,1213595956⟩ E) ⟨139855007360,1208978655⟩ (N E ⟨139855007488,1204383306⟩ E)) ⟨139855007616,1199809782⟩ (N (N E ⟨139855007744,1195257960⟩ E) ⟨139855007872,1190727717⟩ E)) ⟨139855008000,1186218928⟩ (N (N (N E ⟨139855008128,1181731474⟩ E) ⟨139855008256,1177265231⟩ (N E ⟨139855008384,1172820081⟩ E)) ⟨139855008512,1168395904⟩ (N (N E ⟨139855008768,1159609993⟩ E) ⟨139855008896,1155248024⟩ E)))))))

noncomputable def tab9 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨139855009280,1142284672⟩ E) ⟨139855009408,1138004023⟩ (N E ⟨139855009664,1129502747⟩ E)) ⟨139855009792,1125281895⟩ (N (N E ⟨139855009920,1121080752⟩ E) ⟨139855010048,1116899208⟩ (N E ⟨139855010176,1112737153⟩ E))) ⟨139855010560,1100366836⟩ (N (N (N E ⟨139855010944,1088168040⟩ E) ⟨139855011328,1076137917⟩ (N E ⟨139855011712,1064273676⟩ E)) ⟨139855011840,1060355316⟩ (N (N E ⟨139989224448,1413886087⟩ E) ⟨139989224576,1408486147⟩ E))) ⟨139989224704,1403111977⟩ (N (N (N (N E ⟨139989224832,1397763430⟩ E) ⟨139989224960,1392440360⟩ (N E ⟨139989225088,1387142620⟩ E)) ⟨139989225216,1381870066⟩ (N (N E ⟨139989225344,1376622554⟩ E) ⟨139989225472,1371399943⟩ (N E ⟨139989225600,1366202089⟩ E))) ⟨139989225728,1361028853⟩ (N (N (N E ⟨139989225856,1355880094⟩ E) ⟨139989225984,1350755673⟩ (N E ⟨139989226112,1345655453⟩ E)) ⟨139989226240,1340579296⟩ (N (N E ⟨139989226496,1330498629⟩ E) ⟨139989226624,1325493849⟩ E)))) ⟨139989226752,1320512592⟩ (N (N (N (N (N E ⟨139989226880,1315554727⟩ E) ⟨139989227008,1310620122⟩ (N E ⟨139989227136,1305708645⟩ E)) ⟨139989227264,1300820167⟩ (N (N E ⟨139989227648,1286291437⟩ E) ⟨139989227904,1276718263⟩ (N E ⟨139989228160,1267234035⟩ E))) ⟨139989228672,1248528466⟩ (N (N (N E ⟨139989228928,1239305181⟩ E) ⟨139989229568,1216617055⟩ (N E ⟨140123442304,1601740208⟩ E)) ⟨140123442432,1595628665⟩ (N (N E ⟨140123442560,1589546261⟩ E) ⟨140123442688,1583492828⟩ E))) ⟨140123442816,1577468201⟩ (N (N (N (N E ⟨140123442944,1571472217⟩ E) ⟨140123443072,1565504710⟩ (N E ⟨140123443200,1559565520⟩ E)) ⟨140123443328,1553654485⟩ (N (N E ⟨140123443456,1547771445⟩ E) ⟨140123443584,1541916240⟩ E)) ⟨140123443712,1536088714⟩ (N (N (N E ⟨140123443840,1530288708⟩ E) ⟨140123444096,1518770637⟩ (N E ⟨140123444224,1513052263⟩ E)) ⟨140123444352,1507360792⟩ (N (N E ⟨140123444480,1501696073⟩ E) ⟨140123444608,1496057954⟩ E))))) ⟨140123444736,1490446287⟩ (N (N (N (N (N (N E ⟨140123444864,1484860921⟩ E) ⟨140123444992,1479301710⟩ (N E ⟨140123445248,1468261163⟩ E)) ⟨140123445504,1457323483⟩ (N (N E ⟨140123445632,1451892858⟩ E) ⟨140123445760,1446487520⟩ (N E ⟨140123446016,1435752141⟩ E))) ⟨140123446528,1414578675⟩ (N (N (N E ⟨140123446656,1409346442⟩ E) ⟨140123446912,1398954390⟩ (N E ⟨140123447296,1383545347⟩ E)) ⟨140257660160,1800398966⟩ (N (N E ⟨140257660288,1793535994⟩ E) ⟨140257660416,1786705712⟩ E))) ⟨140257660544,1779907933⟩ (N (N (N (N E ⟨140257660672,1773142471⟩ E) ⟨140257660800,1766409142⟩ (N E ⟨140257660928,1759707763⟩ E)) ⟨140257661056,1753038153⟩ (N (N E ⟨140257661184,1746400130⟩ E) ⟨140257661312,1739793515⟩ E)) ⟨140257661440,1733218130⟩ (N (N (N E ⟨140257661568,1726673798⟩ E) ⟨140257661696,1720160343⟩ (N E ⟨140257661824,1713677589⟩ E)) ⟨140257661952,1707225364⟩ (N (N E ⟨140257662080,1700803495⟩ E) ⟨140257662208,1694411811⟩ E)))) ⟨140257662336,1688050141⟩ (N (N (N (N (N E ⟨140257662464,1681718317⟩ E) ⟨140257662592,1675416170⟩ (N E ⟨140257662848,1662900242⟩ E)) ⟨140257662976,1656686131⟩ (N (N E ⟨140257663104,1650501037⟩ E) ⟨140257663360,1638217248⟩ (N E ⟨140257663744,1620005160⟩ E))) ⟨140257663872,1613990788⟩ (N (N (N E ⟨140257664128,1602045592⟩ E) ⟨140257664256,1596114459⟩ (N E ⟨140257664384,1590210763⟩ E)) ⟨140257664640,1578485078⟩ (N (N E ⟨140257664768,1572662787⟩ E) ⟨140257664896,1566867331⟩ E))) ⟨140257665024,1561098561⟩ (N (N (N (N E ⟨140391878272,1994406676⟩ E) ⟨140391878400,1986825901⟩ (N E ⟨140391878528,1979281131⟩ E)) ⟨140391878656,1971772162⟩ (N (N E ⟨140391878784,1964298789⟩ E) ⟨140391878912,1956860810⟩ E)) ⟨140391879040,1949458024⟩ (N (N (N E ⟨140391879168,1942090232⟩ E) ⟨140391879296,1934757235⟩ (N E ⟨140391879424,1927458836⟩ E)) ⟨140391879680,1912965048⟩ (N (N E ⟨140391879808,1905769273⟩ E) ⟨140391879936,1898607319⟩ E)))))) ⟨140391880064,1891478997⟩ (N (N (N (N (N (N (N E ⟨140391880320,1877322492⟩ E) ⟨140391880448,1870293933⟩ (N E ⟨140391880576,1863298255⟩ E)) ⟨140391880832,1849404807⟩ (N (N E ⟨140391880960,1842506671⟩ E) ⟨140391881216,1828806669⟩ (N E ⟨140391881344,1822004446⟩ E))) ⟨140391881600,1808494667⟩ (N (N (N E ⟨140391881856,1795109942⟩ E) ⟨140391882368,1768710122⟩ (N E ⟨140391882496,1762186180⟩ E)) ⟨140391882624,1755692307⟩ (N (N E ⟨140391882752,1749228337⟩ E) ⟨140526096000,2220901632⟩ E))) ⟨140526096128,2212459945⟩ (N (N (N (N E ⟨140526096256,2204058353⟩ E) ⟨140526096384,2195696626⟩ (N E ⟨140526096512,2187374539⟩ E)) ⟨140526096640,2179091866⟩ (N (N E ⟨140526096768,2170848383⟩ E) ⟨140526096896,2162643867⟩ (N E ⟨140526097024,2154478097⟩ E))) ⟨140526097152,2146350854⟩ (N (N (N E ⟨140526097280,2138261920⟩ E) ⟨140526097408,2130211079⟩ (N E ⟨140526097536,2122198114⟩ E)) ⟨140526097664,2114222813⟩ (N (N E ⟨140526097792,2106284963⟩ E) ⟨140526097920,2098384352⟩ E)))) ⟨140526098048,2090520772⟩ (N (N (N (N (N E ⟨140526098304,2074903872⟩ E) ⟨140526098432,2067150140⟩ (N E ⟨140526098688,2051751090⟩ E)) ⟨140526098816,2044105367⟩ (N (N E ⟨140526099200,2021381015⟩ E) ⟨140526099328,2013876510⟩ (N E ⟨140526099456,2006406819⟩ E))) ⟨140526099584,1998971747⟩ (N (N (N E ⟨140526099712,1991571104⟩ E) ⟨140526099968,1976872334⟩ (N E ⟨140526100096,1969573830⟩ E)) ⟨140526100352,1955077646⟩ (N (N E ⟨140526100480,1947879594⟩ E) ⟨140660314112,2431411505⟩ E))) ⟨140660314368,2413024171⟩ (N (N (N (N E ⟨140660314496,2403895724⟩ E) ⟨140660314624,2394810428⟩ (N E ⟨140660314752,2385768037⟩ E)) ⟨140660314880,2376768310⟩ (N (N E ⟨140660315008,2367811004⟩ E) ⟨140660315136,2358895879⟩ E)) ⟨140660315392,2341191223⟩ (N (N (N E ⟨140660315520,2332401220⟩ E) ⟨140660315648,2323652454⟩ (N E ⟨140660315776,2314944695⟩ E)) ⟨140660316032,2297651272⟩ (N (N E ⟨140660316160,2289065152⟩ E) ⟨140660316288,2280519125⟩ E))))) ⟨140660316416,2272012966⟩ (N (N (N (N (N (N E ⟨140660316544,2263546451⟩ E) ⟨140660316928,2238382569⟩ (N E ⟨140660317312,2213567596⟩ E)) ⟨140660317440,2205372470⟩ (N (N E ⟨140660317696,2189095743⟩ E) ⟨140660317824,2181013722⟩ (N E ⟨140660318080,2164961326⟩ E))) ⟨140660318208,2156990541⟩ (N (N (N E ⟨140794532224,2648523719⟩ E) ⟨140794532352,2638513874⟩ (N E ⟨140794532480,2628551302⟩ E)) ⟨140794532608,2618635734⟩ (N (N E ⟨140794532864,2598944548⟩ E) ⟨140794532992,2589168404⟩ E))) ⟨140794533120,2579438211⟩ (N (N (N (N E ⟨140794533248,2569753709⟩ E) ⟨140794533504,2550520753⟩ (N E ⟨140794533632,2540971789⟩ E)) ⟨140794533760,2531467497⟩ (N (N E ⟨140794534016,2512591929⟩ E) ⟨140794534144,2503220156⟩ E)) ⟨140794534272,2493892063⟩ (N (N (N E ⟨140794534784,2457011621⟩ E) ⟨140794534912,2447898293⟩ (N E ⟨140794535680,2394097148⟩ E)) ⟨140794535936,2376492688⟩ (N (N E ⟨140928750208,2882744747⟩ E) ⟨140928750336,2871870296⟩ E)))) ⟨140928750464,2861047103⟩ (N (N (N (N (N E ⟨140928750592,2850274879⟩ E) ⟨140928750720,2839553335⟩ (N E ⟨140928750848,2828882186⟩ E)) ⟨140928750976,2818261147⟩ (N (N E ⟨140928751104,2807689935⟩ E) ⟨140928751232,2797168272⟩ (N E ⟨140928751360,2786695877⟩ E))) ⟨140928751616,2765897790⟩ (N (N (N E ⟨140928751872,2745293482⟩ E) ⟨140928752000,2735063317⟩ (N E ⟨140928752256,2714745628⟩ E)) ⟨140928752384,2704657574⟩ (N (N E ⟨140928753024,2654914744⟩ E) ⟨140928753152,2645103864⟩ E))) ⟨140928753664,2606310863⟩ (N (N (N (N E ⟨141062967936,3148257866⟩ E) ⟨141062968448,3101088340⟩ (N E ⟨141062968576,3089434332⟩ E)) ⟨141062968704,3077835050⟩ (N (N E ⟨141062968832,3066290185⟩ E) ⟨141062969088,3043362484⟩ E)) ⟨141062969216,3031979042⟩ (N (N (N E ⟨141062969344,3020648805⟩ E) ⟨141062969600,2998146751⟩ (N E ⟨141062969728,2986974345⟩ E)) ⟨141062970112,2953768102⟩ (N (N E ⟨141062970496,2921022282⟩ E) ⟨141062970624,2910207999⟩ E)))))))

noncomputable def tab10 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨141062971008,2878064211⟩ E) ⟨141062971264,2856881481⟩ (N E ⟨141062971392,2846363239⟩ E)) ⟨141197186176,3373677043⟩ (N (N E ⟨141197186304,3360998636⟩ E) ⟨141197186560,3335820096⟩ (N E ⟨141197186688,3323319293⟩ E))) ⟨141197186944,3298492970⟩ (N (N (N E ⟨141197187072,3286166793⟩ E) ⟨141197187584,3237434439⟩ (N E ⟨141197187712,3225392842⟩ E)) ⟨141197188352,3166018133⟩ (N (N E ⟨141197188736,3131048874⟩ E) ⟨141197188864,3119499903⟩ E))) ⟨141197189120,3096561355⟩ (N (N (N (N E ⟨141331404288,3616177262⟩ E) ⟨141331404416,3602625836⟩ (N E ⟨141331404672,3575712998⟩ E)) ⟨141331405056,3535813460⟩ (N (N E ⟨141331405184,3522637472⟩ E) ⟨141331405696,3470543628⟩ (N E ⟨141331405824,3457670997⟩ E))) ⟨141331405952,3444858027⟩ (N (N (N E ⟨141331406080,3432104387⟩ E) ⟨141331406720,3369214663⟩ (N E ⟨141331406848,3356810152⟩ E)) ⟨141465621504,3966514488⟩ (N (N E ⟨141465622016,3907252205⟩ E) ⟨141465622656,3834722943⟩ E)))) ⟨141465622784,3820419725⟩ (N (N (N (N (N E ⟨141465622912,3806183170⟩ E) ⟨141465623040,3792012905⟩ (N E ⟨141465623296,3763869769⟩ E)) ⟨141465623680,3722143067⟩ (N (N E ⟨141465623808,3708362854⟩ E) ⟨141465624448,3640410984⟩ (N E ⟨141465624576,3627008003⟩ E))) ⟨141599840640,4100055911⟩ (N (N (N E ⟨141599841024,4054475523⟩ E) ⟨141599841152,4039423026⟩ (N E ⟨141599841792,3965200244⟩ E)) ⟨141599841920,3950560942⟩ (N (N E ⟨141599842048,3935989176⟩ E) ⟨141599842304,3907046756⟩ E))) ⟨141734057984,4453786606⟩ (N (N (N (N E ⟨141734059008,4322911840⟩ E) ⟨141734059136,4306892578⟩ (N E ⟨141734059776,4227900701⟩ E)) ⟨141734060032,4196811774⟩ (N (N E ⟨141868276864,4614115163⟩ E) ⟨141868277760,4496181990⟩ E)) ⟨142002494976,4876549245⟩ (N (N (N E ⟨142002495360,4822786101⟩ E) ⟨142002495488,4805029944⟩ (N E ⟨142136712576,5218762442⟩ E)) ⟨142136713216,5123221857⟩ (N (N E ⟨142270930944,5450617679⟩ E) ⟨142405148672,5787071159⟩ E))))) ⟨142539366400,6132429910⟩ (N (N (N (N (N (N E ⟨142673584128,6486535485⟩ E) ⟨142807801856,6849223449⟩ (N E ⟨142942019584,7220323464⟩ E)) ⟨143210455040,7987049288⟩ (N (N E ⟨143344672768,8382305677⟩ E) ⟨143478890496,8785235472⟩ (N E ⟨143613108224,9195640158⟩ E))) ⟨143881543680,10038053565⟩ (N (N (N E ⟨144149979136,10907852980⟩ E) ⟨144552632320,12260001552⟩ (N E ⟨144686850048,12722441754⟩ E)) ⟨144821067776,13190343653⟩ (N (N E ⟨145089503232,14141541911⟩ E) ⟨145223720960,14624332832⟩ E))) ⟨145626374144,16098359934⟩ (N (N (N (N E ⟨146029027456,17540496856⟩ E) ⟨146029027584,17476036621⟩ (N E ⟨146029027712,17411872388⟩ E)) ⟨146029027840,17348002527⟩ (N (N E ⟨146029027968,17284425416⟩ E) ⟨146029028096,17221139448⟩ E)) ⟨146029028224,17158143022⟩ (N (N (N E ⟨146029028352,17095434549⟩ E) ⟨146029028480,17033012451⟩ (N E ⟨146029028608,16970875159⟩ E)) ⟨146029028736,16909021113⟩ (N (N E ⟨146029028864,16847448766⟩ E) ⟨146029028992,16786156578⟩ E)))) ⟨146029029120,16725143020⟩ (N (N (N (N (N E ⟨146029029248,16664406573⟩ E) ⟨146029029376,16603945726⟩ (N E ⟨146029029504,16543758980⟩ E)) ⟨146029029632,16483844845⟩ (N (N E ⟨146029029760,16424201838⟩ E) ⟨146029029888,16364828489⟩ (N E ⟨146029030016,16305723334⟩ E))) ⟨146029030144,16246884921⟩ (N (N (N E ⟨146029030272,16188311805⟩ E) ⟨146029030400,16130002552⟩ (N E ⟨146029030528,16071955735⟩ E)) ⟨146029030656,16014169939⟩ (N (N E ⟨146029030784,15956643754⟩ E) ⟨146029030912,15899375782⟩ E))) ⟨146029031296,15729107282⟩ (N (N (N (N E ⟨146029031424,15672858345⟩ E) ⟨146029031552,15616860755⟩ (N E ⟨146029031808,15505614239⟩ E)) ⟨146029031936,15450362643⟩ (N (N E ⟨146029032064,15395357056⟩ E) ⟨146029032192,15340596165⟩ E)) ⟨146029032320,15286078662⟩ (N (N (N E ⟨146029032448,15231803251⟩ E) ⟨146029032576,15177768643⟩ (N E ⟨146029032832,15070416714⟩ E)) ⟨146029032960,15017096854⟩ (N (N E ⟨146029033088,14964012717⟩ E) ⟨146029033344,14858546622⟩ E)))))) ⟨146029033472,14806162186⟩ (N (N (N (N (N (N (N E ⟨146029033600,14754008520⟩ E) ⟨146029033728,14702084403⟩ (N E ⟨146029033856,14650388624⟩ E)) ⟨146029033984,14598919978⟩ (N (N E ⟨146029034112,14547677269⟩ E) ⟨146029034240,14496659306⟩ (N E ⟨146029034624,14344942108⟩ E))) ⟨146029034752,14294811379⟩ (N (N (N E ⟨146029035136,14145728051⟩ E) ⟨146029035264,14096466096⟩ (N E ⟨146029035392,14047418502⟩ E)) ⟨146029035520,13998584151⟩ (N (N E ⟨147371212800,18104179779⟩ E) ⟨148176519168,20579495152⟩ E))) ⟨148444954624,21395201291⟩ (N (N (N (N E ⟨149384478720,24175554433⟩ E) ⟨151800397824,30325936625⟩ (N E ⟨151934615552,30607669583⟩ E)) ⟨154484752384,34332890835⟩ (N (N E ⟨154618970240,34309130482⟩ E) ⟨154618970368,34174620589⟩ (N E ⟨154618970496,34030483220⟩ E))) ⟨154618970880,33541516667⟩ (N (N (N E ⟨154618971008,33360104411⟩ E) ⟨154618971392,32762527531⟩ (N E ⟨154618971520,32546044844⟩ E)) ⟨154618971648,32321172538⟩ (N (N E ⟨154618971776,32088070159⟩ E) ⟨154618971904,31846901215⟩ E)))) ⟨154618972544,30526042292⟩ (N (N (N (N (N E ⟨154618972800,29947363174⟩ E) ⟨154618972928,29647981632⟩ (N E ⟨154618973312,28711997456⟩ E)) ⟨154618973440,28388051375⟩ (N (N E ⟨154618973696,27723448008⟩ E) ⟨154618974208,26333212918⟩ (N E ⟨154618974848,24498531262⟩ E))) ⟨154618974976,24120840786⟩ (N (N (N E ⟨154618975744,21797860699⟩ E) ⟨154618975872,21403283349⟩ (N E ⟨154618976000,21007175669⟩ E)) ⟨154618976256,20211247886⟩ (N (N E ⟨154618976640,19011352264⟩ E) ⟨154618976768,18610653819⟩ E))) ⟨154618977536,16213701980⟩ (N (N (N (N E ⟨154618978304,13861447354⟩ E) ⟨154753193984,20271880829⟩ (N E ⟨155558502400,14175430294⟩ E)) ⟨156498026496,14491845486⟩ (N (N E ⟨157571768320,14854998337⟩ E) ⟨158779727872,15263438651⟩ E)) ⟨158913945600,15308711174⟩ (N (N (N E ⟨159585034240,15534485693⟩ E) ⟨159987687424,15669355463⟩ (N E ⟨160792993792,15937321714⟩ E)) ⟨161061429248,16026017701⟩ (N (N E ⟨161195646976,16070232946⟩ E) ⟨161329864704,16114355173⟩ E))))) ⟨161464082432,16158381002⟩ (N (N (N (N (N (N E ⟨162806259712,16592603004⟩ E) ⟨163074695168,16677959410⟩ (N E ⟨163208913152,15826922482⟩ E)) ⟨163208913408,14945667049⟩ (N (N E ⟨163208913920,13226454308⟩ E) ⟨163208914176,12391630959⟩ (N E ⟨163208914304,11981072201⟩ E))) ⟨163208915456,8522614929⟩ (N (N (N E ⟨163208915712,7818828574⟩ E) ⟨163208915840,7476626219⟩ (N E ⟨163208916096,6812240347⟩ E)) ⟨163208916224,6490297652⟩ (N (N E ⟨163208916352,6175341094⟩ E) ⟨163208916608,5566815570⟩ E))) ⟨163208916864,4987473700⟩ (N (N (N (N E ⟨163208916992,4708978403⟩ E) ⟨163208917248,4174759615⟩ (N E ⟨163208917376,3919189493⟩ E)) ⟨163208917504,3671406195⟩ (N (N E ⟨163208918016,2759351698⟩ E) ⟨163208918144,2551366758⟩ E)) ⟨163208918400,2159724198⟩ (N (N (N E ⟨163208918912,1474538120⟩ E) ⟨163208919168,1181268800⟩ (N E ⟨163208919424,920934879⟩ E)) ⟨163208919808,592043860⟩ (N (N E ⟨163208920064,413636898⟩ E) ⟨163208920192,336605342⟩ E)))) ⟨163208920576,153739518⟩ (N (N (N (N (N E ⟨163208920704,108707281⟩ E) ⟨163208920960,42206164⟩ (N E ⟨163208921088,20615427⟩ E)) ⟨163477354752,1057242830⟩ (N (N E ⟨164148439552,8690210513⟩ E) ⟨164148440960,5097088553⟩ (N E ⟨164148444160,432898073⟩ E))) ⟨164282659072,4283690932⟩ (N (N (N E ⟨164551093888,5736041210⟩ E) ⟨164551094656,4048183235⟩ (N E ⟨164551096192,1537656706⟩ E)) ⟨164685313280,2448080764⟩ (N (N E ⟨164685314176,1240576115⟩ E) ⟨164685316096,26113825⟩ E))) ⟨164819531904,1245716800⟩ (N (N (N (N E ⟨164819533568,83105266⟩ E) ⟨164819533824,26599770⟩ (N E ⟨164953748480,2886910783⟩ E)) ⟨164953750016,856666414⟩ (N (N E ⟨164953751168,124450272⟩ E) ⟨164953751296,84017694⟩ E)) ⟨165087969280,27560556⟩ (N (N (N E ⟨165222187008,28034818⟩ E) ⟨165356401024,4121728685⟩ (N E ⟨165356403584,546455846⟩ E)) ⟨165624836864,3393363634⟩ (N (N E ⟨165624838272,1275573259⟩ E) ⟨165759053696,5274648617⟩ E)))))))

noncomputable def tab11 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨165893273856,1142557397⟩ E) ⟨165893273984,1008504899⟩ (N E ⟨165893274752,382238094⟩ E)) ⟨166027490304,2959518831⟩ (N (N E ⟨166027491200,1601355357⟩ E) ⟨166027491968,769165912⟩ (N E ⟨166295926016,2544560332⟩ E))) ⟨166295926784,1451351877⟩ (N (N (N E ⟨166295928320,186023393⟩ E) ⟨166295928448,135192947⟩ (N E ⟨166430145536,474604818⟩ E)) ⟨166430146304,93349461⟩ (N (N E ⟨166430146560,32068746⟩ E) ⟨166564361856,1971862304⟩ E))) ⟨166564362752,900474545⟩ (N (N (N (N E ⟨166564363392,392105677⟩ E) ⟨166564363520,315844763⟩ (N E ⟨166564364288,32485960⟩ E)) ⟨166698580736,674316506⟩ (N (N E ⟨166698582016,32896024⟩ E) ⟨166832798464,677007736⟩ (N E ⟨166832799744,33298690⟩ E))) ⟨166967015296,1638231375⟩ (N (N (N E ⟨167101233024,1643245980⟩ E) ⟨167101233152,1480026627⟩ (N E ⟨167101233664,913658177⟩ E)) ⟨167101235072,61506447⟩ (N (N E ⟨167101235200,34080866⟩ E) ⟨167235450368,2190920921⟩ E)))) ⟨167235451008,1329656496⟩ (N (N (N (N (N E ⟨167235451776,581743186⟩ E) ⟨167235452032,401229637⟩ (N E ⟨167235452672,97792220⟩ E)) ⟨167235452928,34459903⟩ (N (N E ⟨167369669376,687360586⟩ E) ⟨167369670656,34830601⟩ (N E ⟨167503887744,257213756⟩ E))) ⟨167503888384,35192737⟩ (N (N (N E ⟨167638104704,804841746⟩ E) ⟨167638105472,258434129⟩ (N E ⟨167638105728,144330496⟩ E)) ⟨167638106112,35546092⟩ (N (N E ⟨167772323328,198181054⟩ E) ⟨167772323584,100456997⟩ E))) ⟨167772323712,64061469⟩ (N (N (N (N E ⟨167772323840,35890453⟩ E) ⟨167906539648,1349734135⟩ (N E ⟨167906540032,931965908⟩ E)) ⟨167906541440,64535437⟩ (N (N E ⟨168040758528,332258276⟩ E) ⟨168040758912,146708882⟩ E)) ⟨168040759296,36551370⟩ (N (N (N E ⟨168174976128,412648101⟩ E) ⟨168174976896,65444475⟩ (N E ⟨168174977024,36867527⟩ E)) ⟨168309194752,37173895⟩ (N (N E ⟨168443411456,503722235⟩ E) ⟨168443411840,265192886⟩ E))))) ⟨168443412096,148905730⟩ (N (N (N (N (N (N E ⟨168443412352,66300202⟩ E) ⟨168443412480,37470289⟩ (N E ⟨168577629696,203662948⟩ E)) ⟨168577630080,66707555⟩ (N (N E ⟨168577630208,37756530⟩ E) ⟨168711847680,104489929⟩ (N E ⟨168711847936,38032446⟩ E))) ⟨168846065280,150914051⟩ (N (N (N E ⟨168846065536,67480260⟩ E) ⟨168846065664,38297871⟩ (N E ⟨168980282752,269138939⟩ E)) ⟨169114500736,152145026⟩ (N (N E ⟨169114500864,105956227⟩ E) ⟨169114501120,38796613⟩ E))) ⟨169248718208,270937140⟩ (N (N (N (N E ⟨169248718592,106408517⟩ E) ⟨169248718848,39029630⟩ (N E ⟨169382936064,208251407⟩ E)) ⟨169382936576,39251555⟩ (N (N E ⟨169517153920,153825315⟩ E) ⟨169517154304,39462254⟩ E)) ⟨169651371648,154340311⟩ (N (N (N E ⟨169651372032,39661600⟩ E) ⟨169785589248,210194131⟩ (N E ⟨169785589376,154832452⟩ E)) ⟨169785589504,108030487⟩ (N (N E ⟨169785589760,39849474⟩ E) ⟨169919807232,108388370⟩ E)))) ⟨169919807488,40025762⟩ (N (N (N (N (N E ⟨170054024960,108726912⟩ E) ⟨170054025088,70230413⟩ (N E ⟨170054025216,40190358⟩ E)) ⟨170188242944,40343163⟩ (N (N E ⟨170322460416,109345446⟩ E) ⟨170322460544,70673019⟩ (N E ⟨170322460672,40484085⟩ E))) ⟨170456678144,109625194⟩ (N (N (N E ⟨170456678400,40613038⟩ E) ⟨170590896128,40729946⟩ (N E ⟨170725113600,110125106⟩ E)) ⟨170725113728,71217940⟩ (N (N E ⟨170725113856,40834737⟩ E) ⟨170859331584,40927349⟩ E))) ⟨170993549312,41007726⟩ (N (N (N (N E ⟨171127767040,41075819⟩ E) ⟨171261984768,41131588⟩ (N E ⟨171396202496,41174998⟩ E)) ⟨171530420224,41206024⟩ (N (N E ⟨171798855808,19042279⟩ E) ⟨171798855936,5331210⟩ E)) ⟨171798856064,66057⟩ (N (N (N E ⟨172335727616,3170505⟩ E) ⟨172335727744,3160659⟩ (N E ⟨172335727872,3150850⟩ E)) ⟨172335728000,3141079⟩ (N (N E ⟨172335728128,3131346⟩ E) ⟨172335728256,3121651⟩ E)))))) ⟨172335728384,3111994⟩ (N (N (N (N (N (N (N E ⟨172335728512,3102374⟩ E) ⟨172335728640,3092790⟩ (N E ⟨172335728768,3083244⟩ E)) ⟨172335728896,3073735⟩ (N (N E ⟨172335729024,3064262⟩ E) ⟨172335729152,3054826⟩ (N E ⟨172335729280,3045426⟩ E))) ⟨172335729408,3036063⟩ (N (N (N E ⟨172335729536,3026735⟩ E) ⟨172335729664,3017443⟩ (N E ⟨172335729792,3008187⟩ E)) ⟨172335729920,2998966⟩ (N (N E ⟨172335730048,2989781⟩ E) ⟨172335730176,2980630⟩ E))) ⟨172335730304,2971515⟩ (N (N (N (N E ⟨172335730432,2962434⟩ E) ⟨172335730560,2953389⟩ (N E ⟨172335730688,2944377⟩ E)) ⟨172335730816,2935400⟩ (N (N E ⟨172335730944,2926458⟩ E) ⟨172335731072,2917549⟩ (N E ⟨172335731200,2908674⟩ E))) ⟨172335731328,2899833⟩ (N (N (N E ⟨172335731456,2891025⟩ E) ⟨172335731584,2882251⟩ (N E ⟨172335731712,2873511⟩ E)) ⟨172335731840,2864803⟩ (N (N E ⟨172335731968,2856128⟩ E) ⟨172335732096,2847486⟩ E)))) ⟨172335732224,2838877⟩ (N (N (N (N (N E ⟨172335732352,2830300⟩ E) ⟨172335732480,2821756⟩ (N E ⟨172335732608,2813244⟩ E)) ⟨172335732736,2804764⟩ (N (N E ⟨172335732864,2796316⟩ E) ⟨172335733120,2779515⟩ (N E ⟨172335733248,2771162⟩ E))) ⟨172335733376,2762840⟩ (N (N (N E ⟨172335733504,2754549⟩ E) ⟨172335733632,2746290⟩ (N E ⟨172335734016,2721697⟩ E)) ⟨172335734144,2713560⟩ (N (N E ⟨172335734272,2705454⟩ E) ⟨172335734400,2697378⟩ E))) ⟨172335734528,2689333⟩ (N (N (N (N E ⟨172335734656,2681317⟩ E) ⟨172335734784,2673331⟩ (N E ⟨172469945600,14495053⟩ E)) ⟨172469945728,14450104⟩ (N (N E ⟨172469945856,14405330⟩ E) ⟨172469945984,14360729⟩ E)) ⟨172469946112,14316301⟩ (N (N (N E ⟨172469946240,14272044⟩ E) ⟨172469946368,14227959⟩ (N E ⟨172469946496,14184043⟩ E)) ⟨172469946624,14140297⟩ (N (N E ⟨172469946752,14096720⟩ E) ⟨172469946880,14053310⟩ E))))) ⟨172469947008,14010067⟩ (N (N (N (N (N (N E ⟨172469947136,13966991⟩ E) ⟨172469947264,13924080⟩ (N E ⟨172469947392,13881334⟩ E)) ⟨172469947520,13838751⟩ (N (N E ⟨172469947648,13796332⟩ E) ⟨172469947776,13754076⟩ (N E ⟨172469947904,13711981⟩ E))) ⟨172469948032,13670047⟩ (N (N (N E ⟨172469948160,13628274⟩ E) ⟨172469948288,13586660⟩ (N E ⟨172469948416,13545204⟩ E)) ⟨172469948544,13503907⟩ (N (N E ⟨172469948672,13462767⟩ E) ⟨172469948800,13421784⟩ E))) ⟨172469948928,13380956⟩ (N (N (N (N E ⟨172469949056,13340284⟩ E) ⟨172469949184,13299766⟩ (N E ⟨172469949312,13259402⟩ E)) ⟨172469949440,13219191⟩ (N (N E ⟨172469949568,13179133⟩ E) ⟨172469949696,13139226⟩ E)) ⟨172469949824,13099470⟩ (N (N (N E ⟨172469950080,13020409⟩ E) ⟨172469950208,12981102⟩ (N E ⟨172469950336,12941943⟩ E)) ⟨172469950464,12902932⟩ (N (N E ⟨172469950592,12864067⟩ E) ⟨172469950848,12786777⟩ E)))) ⟨172469950976,12748350⟩ (N (N (N (N (N E ⟨172469951104,12710067⟩ E) ⟨172469951232,12671927⟩ (N E ⟨172469951744,12520793⟩ E)) ⟨172469952384,12335031⟩ (N (N E ⟨172469952512,12298293⟩ E) ⟨172604163456,34022926⟩ (N E ⟨172604163584,33917505⟩ E))) ⟨172604163712,33812491⟩ (N (N (N E ⟨172604163840,33707884⟩ E) ⟨172604163968,33603682⟩ (N E ⟨172604164096,33499882⟩ E)) ⟨172604164224,33396482⟩ (N (N E ⟨172604164352,33293481⟩ E) ⟨172604164480,33190878⟩ E))) ⟨172604164608,33088669⟩ (N (N (N (N E ⟨172604164736,32986854⟩ E) ⟨172604164864,32885430⟩ (N E ⟨172604164992,32784395⟩ E)) ⟨172604165120,32683749⟩ (N (N E ⟨172604165248,32583489⟩ E) ⟨172604165376,32483613⟩ E)) ⟨172604165504,32384119⟩ (N (N (N E ⟨172604165632,32285007⟩ E) ⟨172604165760,32186273⟩ (N E ⟨172604165888,32087917⟩ E)) ⟨172604166016,31989936⟩ (N (N E ⟨172604166144,31892329⟩ E) ⟨172604166272,31795094⟩ E)))))))

noncomputable def tab12 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨172604166528,31601734⟩ E) ⟨172604166656,31505605⟩ (N E ⟨172604166784,31409842⟩ E)) ⟨172604166912,31314443⟩ (N (N E ⟨172604167040,31219405⟩ E) ⟨172604167168,31124728⟩ (N E ⟨172604167296,31030410⟩ E))) ⟨172604167424,30936449⟩ (N (N (N E ⟨172604167552,30842843⟩ E) ⟨172604167808,30656692⟩ (N E ⟨172604167936,30564143⟩ E)) ⟨172604168064,30471943⟩ (N (N E ⟨172604168192,30380091⟩ E) ⟨172604168448,30197423⟩ E))) ⟨172604168704,30016127⟩ (N (N (N (N E ⟨172604168832,29925989⟩ E) ⟨172604168960,29836189⟩ (N E ⟨172604169216,29657598⟩ E)) ⟨172604169472,29480342⟩ (N (N E ⟨172604169600,29392211⟩ E) ⟨172604169728,29304409⟩ (N E ⟨172604169856,29216935⟩ E))) ⟨172604169984,29129787⟩ (N (N (N E ⟨172604170240,28956464⟩ E) ⟨172738381312,61694234⟩ (N E ⟨172738381440,61503221⟩ E)) ⟨172738381568,61312946⟩ (N (N E ⟨172738381696,61123406⟩ E) ⟨172738381824,60934599⟩ E)))) ⟨172738381952,60746521⟩ (N (N (N (N (N E ⟨172738382080,60559168⟩ E) ⟨172738382208,60372537⟩ (N E ⟨172738382336,60186624⟩ E)) ⟨172738382464,60001427⟩ (N (N E ⟨172738382592,59816942⟩ E) ⟨172738382720,59633166⟩ (N E ⟨172738382848,59450095⟩ E))) ⟨172738382976,59267727⟩ (N (N (N E ⟨172738383104,59086058⟩ E) ⟨172738383232,58905084⟩ (N E ⟨172738383360,58724803⟩ E)) ⟨172738383488,58545211⟩ (N (N E ⟨172738383616,58366306⟩ E) ⟨172738383744,58188084⟩ E))) ⟨172738383872,58010542⟩ (N (N (N (N E ⟨172738384000,57833677⟩ E) ⟨172738384128,57657485⟩ (N E ⟨172738384256,57481964⟩ E)) ⟨172738384384,57307111⟩ (N (N E ⟨172738384512,57132923⟩ E) ⟨172738384640,56959396⟩ E)) ⟨172738384768,56786527⟩ (N (N (N E ⟨172738384896,56614314⟩ E) ⟨172738385024,56442754⟩ (N E ⟨172738385152,56271844⟩ E)) ⟨172738385280,56101580⟩ (N (N E ⟨172738385408,55931959⟩ E) ⟨172738385536,55762980⟩ E))))) ⟨172738385920,55259857⟩ (N (N (N (N (N (N E ⟨172738386176,54927594⟩ E) ⟨172738386304,54762398⟩ (N E ⟨172738386560,54433868⟩ E)) ⟨172738386944,53945679⟩ (N (N E ⟨172738387200,53623259⟩ E) ⟨172738387328,53462953⟩ (N E ⟨172738387456,53303246⟩ E))) ⟨172738387584,53144135⟩ (N (N (N E ⟨172738387840,52827690⟩ E) ⟨172738387968,52670351⟩ (N E ⟨172872599296,97152731⟩ E)) ⟨172872599424,96852398⟩ (N (N E ⟨172872599552,96553226⟩ E) ⟨172872599680,96255209⟩ E))) ⟨172872599808,95958340⟩ (N (N (N (N E ⟨172872599936,95662616⟩ E) ⟨172872600064,95368031⟩ (N E ⟨172872600192,95074579⟩ E)) ⟨172872600320,94782256⟩ (N (N E ⟨172872600448,94491055⟩ E) ⟨172872600576,94200972⟩ E)) ⟨172872600704,93912003⟩ (N (N (N E ⟨172872600832,93624140⟩ E) ⟨172872600960,93337381⟩ (N E ⟨172872601088,93051719⟩ E)) ⟨172872601216,92767149⟩ (N (N E ⟨172872601344,92483667⟩ E) ⟨172872601472,92201267⟩ E)))) ⟨172872601600,91919944⟩ (N (N (N (N (N E ⟨172872601728,91639694⟩ E) ⟨172872601856,91360512⟩ (N E ⟨172872601984,91082393⟩ E)) ⟨172872602112,90805331⟩ (N (N E ⟨172872602240,90529323⟩ E) ⟨172872602368,90254363⟩ (N E ⟨172872602496,89980446⟩ E))) ⟨172872602624,89707568⟩ (N (N (N E ⟨172872602752,89435724⟩ E) ⟨172872602880,89164910⟩ (N E ⟨172872603008,88895120⟩ E)) ⟨172872603136,88626350⟩ (N (N E ⟨172872603264,88358596⟩ E) ⟨172872603392,88091852⟩ E))) ⟨172872603520,87826114⟩ (N (N (N (N E ⟨172872603648,87561378⟩ E) ⟨172872603776,87297640⟩ (N E ⟨172872603904,87034894⟩ E)) ⟨172872604032,86773136⟩ (N (N E ⟨172872604160,86512361⟩ E) ⟨172872604288,86252566⟩ E)) ⟨172872604416,85993746⟩ (N (N (N E ⟨172872604544,85735896⟩ E) ⟨172872604672,85479013⟩ (N E ⟨172872604928,84968126⟩ E)) ⟨172872605056,84714115⟩ (N (N E ⟨172872605184,84461052⟩ E) ⟨172872605696,83458205⟩ E)))))) ⟨173006817152,140806868⟩ (N (N (N (N (N (N (N E ⟨173006817280,140371923⟩ E) ⟨173006817408,139938656⟩ (N E ⟨173006817536,139507060⟩ E)) ⟨173006817664,139077128⟩ (N (N E ⟨173006817792,138648851⟩ E) ⟨173006817920,138222222⟩ (N E ⟨173006818048,137797234⟩ E))) ⟨173006818176,137373878⟩ (N (N (N E ⟨173006818304,136952147⟩ E) ⟨173006818432,136532034⟩ (N E ⟨173006818560,136113532⟩ E)) ⟨173006818688,135696632⟩ (N (N E ⟨173006818816,135281328⟩ E) ⟨173006818944,134867612⟩ E))) ⟨173006819072,134455477⟩ (N (N (N (N E ⟨173006819200,134044916⟩ E) ⟨173006819328,133635921⟩ (N E ⟨173006819456,133228486⟩ E)) ⟨173006819712,132418264⟩ (N (N E ⟨173006819840,132015464⟩ E) ⟨173006819968,131614195⟩ (N E ⟨173006820096,131214450⟩ E))) ⟨173006820224,130816221⟩ (N (N (N E ⟨173006820352,130419504⟩ E) ⟨173006820480,130024289⟩ (N E ⟨173006820608,129630571⟩ E)) ⟨173006820736,129238342⟩ (N (N E ⟨173006820864,128847597⟩ E) ⟨173006820992,128458327⟩ E)))) ⟨173006821120,128070528⟩ (N (N (N (N (N E ⟨173006821248,127684191⟩ E) ⟨173006821504,126915879⟩ (N E ⟨173006821632,126533891⟩ E)) ⟨173006821888,125774218⟩ (N (N E ⟨173006822016,125396520⟩ E) ⟨173006822400,124271905⟩ (N E ⟨173006822656,123529163⟩ E))) ⟨173006822784,123159874⟩ (N (N (N E ⟨173006823296,121696449⟩ E) ⟨173006823424,121333996⟩ (N E ⟨173141035008,192401870⟩ E)) ⟨173141035136,191808010⟩ (N (N E ⟨173141035264,191216440⟩ E) ⟨173141035392,190627150⟩ E))) ⟨173141035520,190040129⟩ (N (N (N (N E ⟨173141035648,189455366⟩ E) ⟨173141035776,188872852⟩ (N E ⟨173141035904,188292576⟩ E)) ⟨173141036032,187714528⟩ (N (N E ⟨173141036160,187138697⟩ E) ⟨173141036288,186565073⟩ E)) ⟨173141036416,185993647⟩ (N (N (N E ⟨173141036544,185424407⟩ E) ⟨173141036672,184857344⟩ (N E ⟨173141036800,184292448⟩ E)) ⟨173141036928,183729709⟩ (N (N E ⟨173141037056,183169117⟩ E) ⟨173141037184,182610663⟩ E))))) ⟨173141037312,182054335⟩ (N (N (N (N (N (N E ⟨173141037440,181500126⟩ E) ⟨173141037568,180948025⟩ (N E ⟨173141037696,180398022⟩ E)) ⟨173141037824,179850108⟩ (N (N E ⟨173141037952,179304274⟩ E) ⟨173141038080,178760509⟩ (N E ⟨173141038208,178218805⟩ E))) ⟨173141038336,177679153⟩ (N (N (N E ⟨173141038592,176605963⟩ E) ⟨173141038720,176072408⟩ (N E ⟨173141038848,175540867⟩ E)) ⟨173141038976,175011331⟩ (N (N E ⟨173141039104,174483792⟩ E) ⟨173141039232,173958239⟩ E))) ⟨173141039360,173434664⟩ (N (N (N (N E ⟨173141039744,171875718⟩ E) ⟨173141039872,171359966⟩ (N E ⟨173141040000,170846148⟩ E)) ⟨173141040384,169316210⟩ (N (N E ⟨173141040512,168810041⟩ E) ⟨173141040640,168305763⟩ E)) ⟨173141041152,166307388⟩ (N (N (N E ⟨173275252864,251869431⟩ E) ⟨173275252992,251092621⟩ (N E ⟨173275253120,250318805⟩ E)) ⟨173275253248,249547968⟩ (N (N E ⟨173275253376,248780098⟩ E) ⟨173275253504,248015179⟩ E)))) ⟨173275253632,247253200⟩ (N (N (N (N (N E ⟨173275253760,246494146⟩ E) ⟨173275253888,245738003⟩ (N E ⟨173275254016,244984759⟩ E)) ⟨173275254144,244234399⟩ (N (N E ⟨173275254272,243486912⟩ E) ⟨173275254400,242742283⟩ (N E ⟨173275254528,242000499⟩ E))) ⟨173275254656,241261548⟩ (N (N (N E ⟨173275254784,240525416⟩ E) ⟨173275254912,239792091⟩ (N E ⟨173275255040,239061560⟩ E)) ⟨173275255168,238333809⟩ (N (N E ⟨173275255296,237608827⟩ E) ⟨173275255424,236886600⟩ E))) ⟨173275255552,236167116⟩ (N (N (N (N E ⟨173275255680,235450363⟩ E) ⟨173275255808,234736328⟩ (N E ⟨173275255936,234024998⟩ E)) ⟨173275256064,233316362⟩ (N (N E ⟨173275256192,232610408⟩ E) ⟨173275256320,231907122⟩ E)) ⟨173275256448,231206493⟩ (N (N (N E ⟨173275256576,230508509⟩ E) ⟨173275256704,229813158⟩ (N E ⟨173275256832,229120428⟩ E)) ⟨173275256960,228430308⟩ (N (N E ⟨173275257216,227057846⟩ E) ⟨173275257472,225695681⟩ E)))))))

noncomputable def tab13 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨173275257728,224343719⟩ E) ⟨173275257856,223671535⟩ (N E ⟨173275257984,223001869⟩ E)) ⟨173275258112,222334707⟩ (N (N E ⟨173275258240,221670039⟩ E) ⟨173275258496,220348142⟩ (N E ⟨173275258624,219690889⟩ E))) ⟨173275258752,219036086⟩ (N (N (N E ⟨173275258880,218383722⟩ E) ⟨173409470720,319136758⟩ (N E ⟨173409470848,318153244⟩ E)) ⟨173409470976,317173516⟩ (N (N E ⟨173409471104,316197559⟩ E) ⟨173409471232,315225354⟩ E))) ⟨173409471360,314256884⟩ (N (N (N (N E ⟨173409471488,313292131⟩ E) ⟨173409471616,312331080⟩ (N E ⟨173409471744,311373712⟩ E)) ⟨173409471872,310420012⟩ (N (N E ⟨173409472000,309469961⟩ E) ⟨173409472128,308523543⟩ (N E ⟨173409472256,307580742⟩ E))) ⟨173409472384,306641541⟩ (N (N (N E ⟨173409472512,305705923⟩ E) ⟨173409472640,304773873⟩ (N E ⟨173409472768,303845373⟩ E)) ⟨173409472896,302920407⟩ (N (N E ⟨173409473024,301998961⟩ E) ⟨173409473152,301081016⟩ E)))) ⟨173409473280,300166558⟩ (N (N (N (N (N E ⟨173409473408,299255570⟩ E) ⟨173409473536,298348037⟩ (N E ⟨173409473664,297443943⟩ E)) ⟨173409473792,296543272⟩ (N (N E ⟨173409473920,295646009⟩ E) ⟨173409474176,293861645⟩ (N E ⟨173409474304,292974513⟩ E))) ⟨173409474432,292090727⟩ (N (N (N E ⟨173409474688,290333135⟩ E) ⟨173409474816,289459298⟩ (N E ⟨173409474944,288588747⟩ E)) ⟨173409475072,287721468⟩ (N (N E ⟨173409475200,286857445⟩ E) ⟨173409475584,284284772⟩ E))) ⟨173409475968,281740887⟩ (N (N (N (N E ⟨173409476352,279225402⟩ E) ⟨173409476480,278393153⟩ (N E ⟨173409476608,277564003⟩ E)) ⟨173543688832,391703933⟩ (N (N E ⟨173543688960,390499570⟩ E) ⟨173543689088,389299835⟩ E)) ⟨173543689216,388104705⟩ (N (N (N E ⟨173543689344,386914159⟩ E) ⟨173543689472,385728177⟩ (N E ⟨173543689600,384546737⟩ E)) ⟨173543689728,383369819⟩ (N (N E ⟨173543689856,382197402⟩ E) ⟨173543689984,381029465⟩ E))))) ⟨173543690112,379865987⟩ (N (N (N (N (N (N E ⟨173543690240,378706948⟩ E) ⟨173543690368,377552329⟩ (N E ⟨173543690496,376402108⟩ E)) ⟨173543690624,375256266⟩ (N (N E ⟨173543690752,374114782⟩ E) ⟨173543690880,372977637⟩ (N E ⟨173543691008,371844811⟩ E))) ⟨173543691136,370716284⟩ (N (N (N E ⟨173543691264,369592036⟩ E) ⟨173543691392,368472049⟩ (N E ⟨173543691520,367356303⟩ E)) ⟨173543691648,366244778⟩ (N (N E ⟨173543691776,365137455⟩ E) ⟨173543691904,364034316⟩ E))) ⟨173543692032,362935342⟩ (N (N (N (N E ⟨173543692160,361840512⟩ E) ⟨173543692288,360749810⟩ (N E ⟨173543692416,359663216⟩ E)) ⟨173543692544,358580711⟩ (N (N E ⟨173543692800,356427896⟩ E) ⟨173543692928,355357550⟩ E)) ⟨173543693056,354291219⟩ (N (N (N E ⟨173543693184,353228887⟩ E) ⟨173543693312,352170535⟩ (N E ⟨173543693440,351116146⟩ E)) ⟨173543693696,349019183⟩ (N (N E ⟨173543693824,347976574⟩ E) ⟨173543694208,344872027⟩ E)))) ⟨173543694336,343844881⟩ (N (N (N (N (N E ⟨173677906688,473829070⟩ E) ⟨173677906816,472373320⟩ (N E ⟨173677906944,470923159⟩ E)) ⟨173677907072,469478560⟩ (N (N E ⟨173677907200,468039499⟩ E) ⟨173677907328,466605949⟩ (N E ⟨173677907456,465177886⟩ E))) ⟨173677907584,463755284⟩ (N (N (N E ⟨173677907712,462338118⟩ E) ⟨173677907840,460926364⟩ (N E ⟨173677907968,459519996⟩ E)) ⟨173677908096,458118990⟩ (N (N E ⟨173677908224,456723321⟩ E) ⟨173677908352,455332965⟩ E))) ⟨173677908480,453947898⟩ (N (N (N (N E ⟨173677908608,452568095⟩ E) ⟨173677908736,451193533⟩ (N E ⟨173677908864,449824187⟩ E)) ⟨173677908992,448460034⟩ (N (N E ⟨173677909120,447101051⟩ E) ⟨173677909248,445747213⟩ E)) ⟨173677909376,444398497⟩ (N (N (N E ⟨173677909504,443054881⟩ E) ⟨173677909632,441716341⟩ (N E ⟨173677909760,440382854⟩ E)) ⟨173677909888,439054397⟩ (N (N E ⟨173677910016,437730947⟩ E) ⟨173677910144,436412482⟩ E)))))) ⟨173677910400,433790417⟩ (N (N (N (N (N (N (N E ⟨173677910656,431188021⟩ E) ⟨173677911040,427320924⟩ (N E ⟨173677911296,424766934⟩ E)) ⟨173677911424,423497097⟩ (N (N E ⟨173677911552,422232004⟩ E) ⟨173677911680,420971632⟩ (N E ⟨173677911936,418464972⟩ E))) ⟨173677912064,417218641⟩ (N (N (N E ⟨173812124544,563463655⟩ E) ⟨173812124672,561733851⟩ (N E ⟨173812124800,560010683⟩ E)) ⟨173812124928,558294119⟩ (N (N E ⟨173812125056,556584131⟩ E) ⟨173812125184,554880686⟩ E))) ⟨173812125312,553183756⟩ (N (N (N (N E ⟨173812125440,551493311⟩ E) ⟨173812125568,549809320⟩ (N E ⟨173812125696,548131754⟩ E)) ⟨173812125824,546460584⟩ (N (N E ⟨173812125952,544795781⟩ E) ⟨173812126080,543137315⟩ (N E ⟨173812126208,541485158⟩ E))) ⟨173812126336,539839280⟩ (N (N (N E ⟨173812126464,538199653⟩ E) ⟨173812126592,536566249⟩ (N E ⟨173812126720,534939039⟩ E)) ⟨173812126848,533317995⟩ (N (N E ⟨173812126976,531703090⟩ E) ⟨173812127104,530094294⟩ E)))) ⟨173812127232,528491581⟩ (N (N (N (N (N E ⟨173812127360,526894923⟩ E) ⟨173812127488,525304292⟩ (N E ⟨173812127616,523719661⟩ E)) ⟨173812127744,522141004⟩ (N (N E ⟨173812127872,520568292⟩ E) ⟨173812128000,519001499⟩ (N E ⟨173812128128,517440599⟩ E))) ⟨173812128256,515885565⟩ (N (N (N E ⟨173812128384,514336370⟩ E) ⟨173812128640,511255393⟩ (N E ⟨173812128768,509723558⟩ E)) ⟨173812129024,506677069⟩ (N (N E ⟨173812129152,505162362⟩ E) ⟨173812129280,503653314⟩ E))) ⟨173812129664,499159865⟩ (N (N (N (N E ⟨173812129792,497673197⟩ E) ⟨173946342400,660518198⟩ (N E ⟨173946342528,658492000⟩ E)) ⟨173946342656,656473569⟩ (N (N E ⟨173946342784,654462868⟩ E) ⟨173946342912,652459862⟩ E)) ⟨173946343040,650464517⟩ (N (N (N E ⟨173946343168,648476796⟩ E) ⟨173946343296,646496665⟩ (N E ⟨173946343424,644524089⟩ E)) ⟨173946343552,642559034⟩ (N (N E ⟨173946343680,640601464⟩ E) ⟨173946343808,638651347⟩ E))))) ⟨173946343936,636708648⟩ (N (N (N (N (N (N E ⟨173946344064,634773332⟩ E) ⟨173946344192,632845367⟩ (N E ⟨173946344320,630924719⟩ E)) ⟨173946344448,629011354⟩ (N (N E ⟨173946344576,627105240⟩ E) ⟨173946344704,625206343⟩ (N E ⟨173946344832,623314631⟩ E))) ⟨173946344960,621430071⟩ (N (N (N E ⟨173946345088,619552631⟩ E) ⟨173946345216,617682278⟩ (N E ⟨173946345344,615818980⟩ E)) ⟨173946345472,613962706⟩ (N (N E ⟨173946345600,612113423⟩ E) ⟨173946345728,610271100⟩ E))) ⟨173946345984,606607209⟩ (N (N (N (N E ⟨173946346112,604785579⟩ E) ⟨173946346240,602970783⟩ (N E ⟨173946346624,597567103⟩ E)) ⟨173946346880,593998266⟩ (N (N E ⟨173946347008,592223842⟩ E) ⟨173946347264,588694835⟩ E)) ⟨173946347520,585192084⟩ (N (N (N E ⟨174080560128,767252671⟩ E) ⟨174080560256,764899055⟩ (N E ⟨174080560384,762554461⟩ E)) ⟨174080560512,760218847⟩ (N (N E ⟨174080560640,757892172⟩ E) ⟨174080560768,755574395⟩ E)))) ⟨174080560896,753265474⟩ (N (N (N (N (N E ⟨174080561024,750965370⟩ E) ⟨174080561152,748674041⟩ (N E ⟨174080561280,746391449⟩ E)) ⟨174080561408,744117552⟩ (N (N E ⟨174080561536,741852311⟩ E) ⟨174080561664,739595687⟩ (N E ⟨174080561792,737347640⟩ E))) ⟨174080561920,735108131⟩ (N (N (N E ⟨174080562048,732877121⟩ E) ⟨174080562176,730654572⟩ (N E ⟨174080562304,728440445⟩ E)) ⟨174080562432,726234702⟩ (N (N E ⟨174080562560,724037304⟩ E) ⟨174080562688,721848214⟩ E))) ⟨174080562816,719667394⟩ (N (N (N (N E ⟨174080562944,717494807⟩ E) ⟨174080563072,715330415⟩ (N E ⟨174080563200,713174182⟩ E)) ⟨174080563328,711026070⟩ (N (N E ⟨174080563456,708886043⟩ E) ⟨174080563584,706754063⟩ E)) ⟨174080563712,704630096⟩ (N (N (N E ⟨174080563840,702514105⟩ E) ⟨174080563968,700406053⟩ (N E ⟨174080564096,698305905⟩ E)) ⟨174080564224,696213626⟩ (N (N E ⟨174080564352,694129181⟩ E) ⟨174080564480,692052533⟩ E)))))))

noncomputable def tab14 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨174080564736,687922492⟩ E) ⟨174080564864,685869029⟩ (N E ⟨174080564992,683823225⟩ E)) ⟨174080565248,679754458⟩ (N (N E ⟨174214777984,879203461⟩ E) ⟨174214778112,876508497⟩ (N E ⟨174214778240,873823856⟩ E))) ⟨174214778368,871149488⟩ (N (N (N E ⟨174214778496,868485349⟩ E) ⟨174214778624,865831389⟩ (N E ⟨174214778752,863187564⟩ E)) ⟨174214778880,860553826⟩ (N (N E ⟨174214779008,857930129⟩ E) ⟨174214779136,855316427⟩ E))) ⟨174214779264,852712675⟩ (N (N (N (N E ⟨174214779392,850118827⟩ E) ⟨174214779520,847534838⟩ (N E ⟨174214779648,844960663⟩ E)) ⟨174214779776,842396257⟩ (N (N E ⟨174214779904,839841577⟩ E) ⟨174214780032,837296576⟩ (N E ⟨174214780160,834761213⟩ E))) ⟨174214780288,832235442⟩ (N (N (N E ⟨174214780416,829719221⟩ E) ⟨174214780544,827212505⟩ (N E ⟨174214780672,824715253⟩ E)) ⟨174214780800,822227420⟩ (N (N E ⟨174214780928,819748965⟩ E) ⟨174214781056,817279845⟩ E)))) ⟨174214781184,814820018⟩ (N (N (N (N (N E ⟨174214781312,812369442⟩ E) ⟨174214781568,807495875⟩ (N E ⟨174214781696,805072802⟩ E)) ⟨174214781824,802658814⟩ (N (N E ⟨174214781952,800253871⟩ E) ⟨174214782208,795470955⟩ (N E ⟨174214782464,790723732⟩ E))) ⟨174214782592,788363405⟩ (N (N (N E ⟨174214782720,786011882⟩ E) ⟨174214782848,783669123⟩ (N E ⟨174214782976,781335090⟩ E)) ⟨174348995840,998302463⟩ (N (N E ⟨174348995968,995244781⟩ E) ⟨174348996096,992198801⟩ E))) ⟨174348996224,989164469⟩ (N (N (N (N E ⟨174348996352,986141733⟩ E) ⟨174348996480,983130539⟩ (N E ⟨174348996608,980130833⟩ E)) ⟨174348996736,977142564⟩ (N (N E ⟨174348996864,974165679⟩ E) ⟨174348996992,971200127⟩ E)) ⟨174348997120,968245854⟩ (N (N (N E ⟨174348997248,965302811⟩ E) ⟨174348997376,962370945⟩ (N E ⟨174348997504,959450206⟩ E)) ⟨174348997632,956540544⟩ (N (N E ⟨174348997760,953641907⟩ E) ⟨174348997888,950754245⟩ E))))) ⟨174348998016,947877510⟩ (N (N (N (N (N (N E ⟨174348998144,945011651⟩ E) ⟨174348998272,942156618⟩ (N E ⟨174348998400,939312363⟩ E)) ⟨174348998528,936478838⟩ (N (N E ⟨174348998656,933655993⟩ E) ⟨174348998784,930843780⟩ (N E ⟨174348998912,928042151⟩ E))) ⟨174348999040,925251058⟩ (N (N (N E ⟨174348999168,922470454⟩ E) ⟨174348999296,919700292⟩ (N E ⟨174348999424,916940525⟩ E)) ⟨174348999552,914191105⟩ (N (N E ⟨174348999680,911451986⟩ E) ⟨174348999808,908723122⟩ E))) ⟨174348999936,906004467⟩ (N (N (N (N E ⟨174349000064,903295975⟩ E) ⟨174349000192,900597600⟩ (N E ⟨174349000320,897909298⟩ E)) ⟨174349000448,895231022⟩ (N (N E ⟨174349000576,892562729⟩ E) ⟨174349000704,889904373⟩ E)) ⟨174483213824,1121002223⟩ (N (N (N E ⟨174483214080,1114158849⟩ E) ⟨174483214208,1110756753⟩ (N E ⟨174483214336,1107367638⟩ E)) ⟨174483214464,1103991443⟩ (N (N E ⟨174483214592,1100628111⟩ E) ⟨174483214720,1097277581⟩ E)))) ⟨174483214848,1093939797⟩ (N (N (N (N (N E ⟨174483214976,1090614699⟩ E) ⟨174483215104,1087302230⟩ (N E ⟨174483215232,1084002332⟩ E)) ⟨174483215360,1080714948⟩ (N (N E ⟨174483215488,1077440021⟩ E) ⟨174483215616,1074177495⟩ (N E ⟨174483215744,1070927312⟩ E))) ⟨174483215872,1067689418⟩ (N (N (N E ⟨174483216000,1064463756⟩ E) ⟨174483216128,1061250272⟩ (N E ⟨174483216256,1058048909⟩ E)) ⟨174483216384,1054859613⟩ (N (N E ⟨174483216640,1048517003⟩ E) ⟨174483216896,1042222011⟩ E))) ⟨174483217024,1039092237⟩ (N (N (N (N E ⟨174483217152,1035974207⟩ E) ⟨174483217664,1023618472⟩ (N E ⟨174483217920,1017509707⟩ E)) ⟨174483218304,1008431780⟩ (N (N E ⟨174483218432,1005428326⟩ E) ⟨174617431680,1253671273⟩ E)) ⟨174617431808,1249840244⟩ (N (N (N E ⟨174617431936,1246023843⟩ E) ⟨174617432064,1242222003⟩ (N E ⟨174617432192,1238434658⟩ E)) ⟨174617432320,1234661742⟩ (N (N E ⟨174617432448,1230903188⟩ E) ⟨174617432576,1227158930⟩ E)))))) ⟨174617432704,1223428905⟩ (N (N (N (N (N (N (N E ⟨174617432832,1219713046⟩ E) ⟨174617432960,1216011289⟩ (N E ⟨174617433088,1212323570⟩ E)) ⟨174617433216,1208649825⟩ (N (N E ⟨174617433344,1204989991⟩ E) ⟨174617433472,1201344004⟩ (N E ⟨174617433600,1197711801⟩ E))) ⟨174617433728,1194093321⟩ (N (N (N E ⟨174617433856,1190488501⟩ E) ⟨174617433984,1186897278⟩ (N E ⟨174617434112,1183319592⟩ E)) ⟨174617434240,1179755381⟩ (N (N E ⟨174617434368,1176204585⟩ E) ⟨174617434496,1172667142⟩ E))) ⟨174617434624,1169142993⟩ (N (N (N (N E ⟨174617434752,1165632078⟩ E) ⟨174617434880,1162134337⟩ (N E ⟨174617435008,1158649710⟩ E)) ⟨174617435136,1155178139⟩ (N (N E ⟨174617435392,1148273930⟩ E) ⟨174617435648,1141421244⟩ (N E ⟨174617435904,1134619620⟩ E))) ⟨174617436032,1131237814⟩ (N (N (N E ⟨174617436160,1127868602⟩ E) ⟨174751649536,1393138594⟩ (N E ⟨174751649792,1384646897⟩ E)) ⟨174751649920,1380425320⟩ (N (N E ⟨174751650048,1376219826⟩ E) ⟨174751650176,1372030341⟩ E)))) ⟨174751650304,1367856792⟩ (N (N (N (N (N E ⟨174751650432,1363699107⟩ E) ⟨174751650560,1359557212⟩ (N E ⟨174751650688,1355431036⟩ E)) ⟨174751650816,1351320508⟩ (N (N E ⟨174751650944,1347225556⟩ E) ⟨174751651072,1343146110⟩ (N E ⟨174751651200,1339082098⟩ E))) ⟨174751651328,1335033452⟩ (N (N (N E ⟨174751651456,1331000101⟩ E) ⟨174751651584,1326981976⟩ (N E ⟨174751651712,1322979007⟩ E)) ⟨174751651840,1318991128⟩ (N (N E ⟨174751651968,1315018268⟩ E) ⟨174751652096,1311060361⟩ E))) ⟨174751652224,1307117339⟩ (N (N (N (N E ⟨174751652352,1303189135⟩ E) ⟨174751652480,1299275681⟩ (N E ⟨174751652864,1287623163⟩ E)) ⟨174751652992,1283768053⟩ (N (N E ⟨174751653120,1279927364⟩ E) ⟨174751653248,1276101033⟩ E)) ⟨174751653376,1272288995⟩ (N (N (N E ⟨174751653632,1264707542⟩ E) ⟨174751653888,1257182497⟩ (N E ⟨174885867392,1539287140⟩ E)) ⟨174885867520,1534590502⟩ (N (N E ⟨174885867648,1529911770⟩ E) ⟨174885867776,1525250863⟩ E))))) ⟨174885867904,1520607698⟩ (N (N (N (N (N (N E ⟨174885868032,1515982195⟩ E) ⟨174885868160,1511374273⟩ (N E ⟨174885868288,1506783852⟩ E)) ⟨174885868416,1502210852⟩ (N (N E ⟨174885868544,1497655194⟩ E) ⟨174885868672,1493116799⟩ (N E ⟨174885868800,1488595589⟩ E))) ⟨174885868928,1484091485⟩ (N (N (N E ⟨174885869056,1479604410⟩ E) ⟨174885869184,1475134287⟩ (N E ⟨174885869312,1470681038⟩ E)) ⟨174885869440,1466244588⟩ (N (N E ⟨174885869568,1461824860⟩ E) ⟨174885869696,1457421779⟩ E))) ⟨174885869824,1453035270⟩ (N (N (N (N E ⟨174885870080,1444311667⟩ E) ⟨174885870208,1439974425⟩ (N E ⟨174885870336,1435653458⟩ E)) ⟨174885870464,1431348692⟩ (N (N E ⟨174885870592,1427060055⟩ E) ⟨174885870848,1418530876⟩ E)) ⟨174885870976,1414290191⟩ (N (N (N E ⟨174885871104,1410065347⟩ E) ⟨174885871488,1397485151⟩ (N E ⟨174885871616,1393322965⟩ E)) ⟨175020085248,1691996236⟩ (N (N E ⟨175020085504,1681698613⟩ E) ⟨175020085632,1676579190⟩ E)))) ⟨175020085760,1671479241⟩ (N (N (N (N (N E ⟨175020085888,1666398676⟩ E) ⟨175020086016,1661337407⟩ (N E ⟨175020086144,1656295346⟩ E)) ⟨175020086272,1651272406⟩ (N (N E ⟨175020086400,1646268500⟩ E) ⟨175020086528,1641283541⟩ (N E ⟨175020086656,1636317443⟩ E))) ⟨175020086784,1631370121⟩ (N (N (N E ⟨175020086912,1626441489⟩ E) ⟨175020087040,1621531463⟩ (N E ⟨175020087168,1616639958⟩ E)) ⟨175020087296,1611766891⟩ (N (N E ⟨175020087424,1606912178⟩ E) ⟨175020087552,1602075736⟩ E))) ⟨175020087680,1597257483⟩ (N (N (N (N E ⟨175020087808,1592457337⟩ E) ⟨175020087936,1587675217⟩ (N E ⟨175020088320,1573436196⟩ E)) ⟨175020088576,1564032164⟩ (N (N E ⟨175020088704,1559356504⟩ E) ⟨175020088960,1550057503⟩ E)) ⟨175020089088,1545434006⟩ (N (N (N E ⟨175020089216,1540827741⟩ E) ⟨175020089344,1536238631⟩ (N E ⟨175154303232,1845502124⟩ E)) ⟨175154303360,1839884051⟩ (N (N E ⟨175154303488,1834287348⟩ E) ⟨175154303616,1828711918⟩ E)))))))

noncomputable def tab15 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨175154303872,1817624488⟩ E) ⟨175154304000,1812112295⟩ (N E ⟨175154304128,1806620990⟩ E)) ⟨175154304256,1801150478⟩ (N (N E ⟨175154304384,1795700664⟩ E) ⟨175154304512,1790271455⟩ (N E ⟨175154304640,1784862757⟩ E))) ⟨175154304768,1779474476⟩ (N (N (N E ⟨175154304896,1774106521⟩ E) ⟨175154305024,1768758799⟩ (N E ⟨175154305152,1763431220⟩ E)) ⟨175154305280,1758123692⟩ (N (N E ⟨175154305408,1752836124⟩ E) ⟨175154305536,1747568426⟩ E))) ⟨175154305664,1742320510⟩ (N (N (N (N E ⟨175154305792,1737092285⟩ E) ⟨175154305920,1731883663⟩ (N E ⟨175154306048,1726694557⟩ E)) ⟨175154306176,1721524877⟩ (N (N E ⟨175154306304,1716374538⟩ E) ⟨175154306432,1711243452⟩ (N E ⟨175154306944,1690909921⟩ E))) ⟨175154307072,1685873815⟩ (N (N (N E ⟨175288521600,1986133620⟩ E) ⟨175288521728,1980110401⟩ (N E ⟨175288521856,1974110006⟩ E)) ⟨175288521984,1968132331⟩ (N (N E ⟨175288522112,1962177274⟩ E) ⟨175288522240,1956244731⟩ E)))) ⟨175288522368,1950334600⟩ (N (N (N (N (N E ⟨175288522752,1932737670⟩ E) ⟨175288522880,1926916179⟩ (N E ⟨175288523008,1921116598⟩ E)) ⟨175288523136,1915338828⟩ (N (N E ⟨175288523264,1909582771⟩ E) ⟨175288523392,1903848328⟩ (N E ⟨175288523520,1898135403⟩ E))) ⟨175288523776,1886773717⟩ (N (N (N E ⟨175288524032,1875496946⟩ E) ⟨175288524160,1869890165⟩ (N E ⟨175288524288,1864304328⟩ E)) ⟨175288524544,1853195110⟩ (N (N E ⟨175288524672,1847671543⟩ E) ⟨175288524800,1842168548⟩ E))) ⟨175422739200,2168334260⟩ (N (N (N (N E ⟨175422739328,2161753494⟩ E) ⟨175422739456,2155197683⟩ (N E ⟨175422739584,2148666715⟩ E)) ⟨175422739712,2142160477⟩ (N (N E ⟨175422739840,2135678855⟩ E) ⟨175422739968,2129221739⟩ E)) ⟨175422740096,2122789017⟩ (N (N (N E ⟨175422740224,2116380579⟩ E) ⟨175422740352,2109996314⟩ (N E ⟨175422740480,2103636114⟩ E)) ⟨175422740608,2097299870⟩ (N (N E ⟨175422740736,2090987472⟩ E) ⟨175422740864,2084698814⟩ E))))) ⟨175422741120,2072192290⟩ (N (N (N (N (N (N E ⟨175422741248,2065974211⟩ E) ⟨175422741376,2059779446⟩ (N E ⟨175422741504,2053607891⟩ E)) ⟨175422741632,2047459442⟩ (N (N E ⟨175422741760,2041333994⟩ E) ⟨175422741888,2035231444⟩ (N E ⟨175422742016,2029151691⟩ E))) ⟨175422742144,2023094631⟩ (N (N (N E ⟨175422742400,2011048186⟩ E) ⟨175422742528,2005058599⟩ (N E ⟨175556957184,2337300549⟩ E)) ⟨175556957568,2316132482⟩ (N (N E ⟨175556957696,2309129774⟩ E) ⟨175556957952,2295203603⟩ E))) ⟨175556958080,2288279902⟩ (N (N (N (N E ⟨175556958208,2281382298⟩ E) ⟨175556958336,2274510674⟩ (N E ⟨175556958464,2267664912⟩ E)) ⟨175556958592,2260844896⟩ (N (N E ⟨175556958720,2254050509⟩ E) ⟨175556958848,2247281636⟩ E)) ⟨175556959104,2233819972⟩ (N (N (N E ⟨175556959616,2207197794⟩ E) ⟨175556959744,2200604333⟩ (N E ⟨175556960256,2174475502⟩ E)) ⟨175691175296,2503460747⟩ (N (N E ⟨175691175552,2488351170⟩ E) ⟨175691175680,2480839145⟩ E)))) ⟨175691175936,2465899976⟩ (N (N (N (N (N E ⟨175691176320,2443701514⟩ E) ⟨175691176832,2414490820⟩ (N E ⟨175691176960,2407256471⟩ E)) ⟨175691177344,2385715446⟩ (N (N E ⟨175691177728,2364414917⟩ E) ⟨175691177856,2357367627⟩ (N E ⟨175691177984,2350346583⟩ E))) ⟨175825393408,2673206091⟩ (N (N (N E ⟨175825393792,2649105194⟩ E) ⟨175825393920,2641131988⟩ (N E ⟨175825394304,2617391742⟩ E)) ⟨175825394688,2593917737⟩ (N (N E ⟨175825394816,2586151614⟩ E) ⟨175825395072,2570706397⟩ E))) ⟨175825395456,2547754202⟩ (N (N (N (N E ⟨175825395584,2540160457⟩ E) ⟨175825395712,2532594994⟩ (N E ⟨175959611136,2872218956⟩ E)) ⟨175959611648,2837757025⟩ (N (N E ⟨175959611776,2829222453⟩ E) ⟨175959612032,2812249382⟩ E)) ⟨175959612288,2795403449⟩ (N (N (N E ⟨175959612416,2787027802⟩ E) ⟨175959612672,2770370439⟩ (N E ⟨175959612800,2762088442⟩ E)) ⟨175959613184,2737427518⟩ (N (N E ⟨175959613312,2729268440⟩ E) ⟨175959613440,2721139749⟩ E)))))) ⟨176093829632,3022603067⟩ (N (N (N (N (N (N (N E ⟨176093829888,3004483481⟩ E) ⟨176093830272,2977558015⟩ (N E ⟨176093830528,2959775211⟩ E)) ⟨176093831168,2915895760⟩ (N (N E ⟨176228048896,3116773877⟩ E) ⟨176362265600,3404158555⟩ (N E ⟨176362266496,3333609555⟩ E))) ⟨176362266624,3323680930⟩ (N (N (N E ⟨176496484352,3536519776⟩ E) ⟨176630702080,3755189350⟩ (N E ⟨176764919808,3979584708⟩ E)) ⟨176899137536,4209597088⟩ (N (N E ⟨177033355264,4445113958⟩ E) ⟨177167572992,4686019082⟩ E))) ⟨177301790720,4932192574⟩ (N (N (N (N E ⟨177436008448,5183510966⟩ E) ⟨177570226176,5439847270⟩ (N E ⟨177704443904,5701071046⟩ E)) ⟨177838661632,5967048477⟩ (N (N E ⟨177972879360,6237642433⟩ E) ⟨178107097088,6512712553⟩ (N E ⟨178241314816,6792115318⟩ E))) ⟨178375532544,7075704133⟩ (N (N (N E ⟨178509750272,7363329404⟩ E) ⟨178912403456,8248884841⟩ (N E ⟨179449274368,9476571417⟩ E)) ⟨179717709824,10107541899⟩ (N (N E ⟨179986145280,10748090468⟩ E) ⟨180388798592,11688866092⟩ E)))) ⟨180388798720,11654104527⟩ (N (N (N (N (N E ⟨180388798848,11619472136⟩ E) ⟨180388798976,11584968342⟩ (N E ⟨180388799104,11550592573⟩ E)) ⟨180388799232,11516344258⟩ (N (N E ⟨180388799360,11482222831⟩ E) ⟨180388799488,11448227727⟩ (N E ⟨180388799616,11414358387⟩ E))) ⟨180388799744,11380614252⟩ (N (N (N E ⟨180388799872,11346994766⟩ E) ⟨180388800000,11313499377⟩ (N E ⟨180388800128,11280127536⟩ E)) ⟨180388800256,11246878697⟩ (N (N E ⟨180388800384,11213752314⟩ E) ⟨180388800512,11180747848⟩ E))) ⟨180388800640,11147864760⟩ (N (N (N (N E ⟨180388800768,11115102515⟩ E) ⟨180388800896,11082460580⟩ (N E ⟨180388801024,11049938424⟩ E)) ⟨180388801152,11017535522⟩ (N (N E ⟨180388801280,10985251347⟩ E) ⟨180388801408,10953085379⟩ E)) ⟨180388801536,10921037098⟩ (N (N (N E ⟨180388801664,10889105988⟩ E) ⟨180388801792,10857291534⟩ (N E ⟨180388801920,10825593226⟩ E)) ⟨180388802048,10794010555⟩ (N (N E ⟨180388802176,10762543015⟩ E) ⟨180388802304,10731190103⟩ E))))) ⟨180388802432,10699951317⟩ (N (N (N (N (N (N E ⟨180388802560,10668826159⟩ E) ⟨180388802688,10637814134⟩ (N E ⟨180388802816,10606914747⟩ E)) ⟨180388802944,10576127510⟩ (N (N E ⟨180388803072,10545451932⟩ E) ⟨180388803200,10514887529⟩ (N E ⟨180388803328,10484433817⟩ E))) ⟨180388803456,10454090316⟩ (N (N (N E ⟨180388803584,10423856546⟩ E) ⟨180388803712,10393732032⟩ (N E ⟨180388803840,10363716300⟩ E)) ⟨180388803968,10333808879⟩ (N (N E ⟨180388804096,10304009300⟩ E) ⟨180388804224,10274317097⟩ E))) ⟨180388804352,10244731805⟩ (N (N (N (N E ⟨180388804480,10215252963⟩ E) ⟨180388804608,10185880112⟩ (N E ⟨180388804736,10156612794⟩ E)) ⟨180388804864,10127450554⟩ (N (N E ⟨180388804992,10098392940⟩ E) ⟨180388805248,10040589791⟩ E)) ⟨180388805376,10011843362⟩ (N (N (N E ⟨180388805504,9983199771⟩ E) ⟨180388805632,9954658577⟩ (N E ⟨180388805760,9926219341⟩ E)) ⟨180388805888,9897881626⟩ (N (N E ⟨180388806016,9869644998⟩ E) ⟨180388806144,9841509023⟩ E)))) ⟨180388806272,9813473271⟩ (N (N (N (N (N E ⟨180388806400,9785537314⟩ E) ⟨180388806528,9757700727⟩ (N E ⟨180388806656,9729963084⟩ E)) ⟨181194113024,11378732994⟩ (N (N E ⟨181596766208,12209343974⟩ E) ⟨181730983936,12486080212⟩ (N E ⟨182670508032,14404908213⟩ E))) ⟨185086427136,18883287715⟩ (N (N (N E ⟨186294386688,20670864005⟩ E) ⟨188039217152,22479958359⟩ (N E ⟨188844523520,22956748407⟩ E)) ⟨188978741376,22943791073⟩ (N (N E ⟨188978741504,22868327409⟩ E) ⟨188978741632,22786289547⟩ E))) ⟨188978741760,22697744874⟩ (N (N (N (N E ⟨188978741888,22602764358⟩ E) ⟨188978742016,22501422485⟩ (N E ⟨188978742144,22393797195⟩ E)) ⟨188978742272,22279969817⟩ (N (N E ⟨188978742400,22160024998⟩ E) ⟨188978742528,22034050636⟩ E)) ⟨188978742656,21902137809⟩ (N (N (N E ⟨188978742784,21764380703⟩ E) ⟨188978743040,21471725482⟩ (N E ⟨188978743168,21317030601⟩ E)) ⟨188978743296,21156897754⟩ (N (N E ⟨188978743424,20991435527⟩ E) ⟨188978743552,20820755150⟩ E)))))))

noncomputable def tab16 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨188978743808,20464197604⟩ E) ⟨188978743936,20278555381⟩ (N E ⟨188978744064,20088164734⟩ E)) ⟨188978744192,19893148878⟩ (N (N E ⟨188978744320,19693633166⟩ E) ⟨188978744448,19489745009⟩ (N E ⟨188978744704,19069370752⟩ E))) ⟨188978744832,18853148956⟩ (N (N (N E ⟨188978744960,18633083148⟩ E) ⟨188978745088,18409309687⟩ (N E ⟨188978745216,18181966454⟩ E)) ⟨188978745344,17951192761⟩ (N (N E ⟨188978745472,17717129255⟩ E) ⟨188978745600,17479917837⟩ E))) ⟨188978745728,17239701561⟩ (N (N (N (N E ⟨188978745984,16750831874⟩ E) ⟨188978746112,16502469524⟩ (N E ⟨188978746240,16251684254⟩ E)) ⟨188978746368,15998623519⟩ (N (N E ⟨188978746624,15486268406⟩ E) ⟨188978746752,15227271596⟩ (N E ⟨188978746880,14966594275⟩ E))) ⟨188978747008,14704386007⟩ (N (N (N E ⟨188978747264,14175975540⟩ E) ⟨188978747392,13910072854⟩ (N E ⟨188978747520,13643238069⟩ E)) ⟨188978747648,13375620595⟩ (N (N E ⟨188978748032,12569561193⟩ E) ⟨188978748160,12300299849⟩ E)))) ⟨188978748544,11492849466⟩ (N (N (N (N (N E ⟨188978748672,11224295565⟩ E) ⟨188978748928,10688945415⟩ (N E ⟨188978749056,10422433252⟩ E)) ⟨188978749184,10156883789⟩ (N (N E ⟨188978749312,9892436003⟩ E) ⟨188978749440,9629227507⟩ (N E ⟨189918273536,9807504934⟩ E))) ⟨190857797632,9986803866⟩ (N (N (N E ⟨192334192640,10269100417⟩ E) ⟨192602626432,13992487478⟩ (N E ⟨192602628096,10320335218⟩ E)) ⟨194347458560,10651067562⟩ (N (N E ⟨194615894016,10701435097⟩ E) ⟨194884329472,10751622640⟩ E))) ⟨195286982656,10826533721⟩ (N (N (N (N E ⟨195421200384,10851397910⟩ E) ⟨195689635840,10900955939⟩ (N E ⟨196092289024,10974839607⟩ E)) ⟨196226506752,10999339314⟩ (N (N E ⟨196763377664,11096649244⟩ E) ⟨196897595392,11120795606⟩ E)) ⟨197434466304,11216603951⟩ (N (N (N E ⟨197568684160,10943561779⟩ E) ⟨197568684288,10648370487⟩ (N E ⟨197568684416,10354926600⟩ E)) ⟨197568685184,8638972399⟩ (N (N E ⟨197568685312,8361724435⟩ E) ⟨197568685568,7815921159⟩ E))))) ⟨197568685824,7282552018⟩ (N (N (N (N (N (N E ⟨197568685952,7020837345⟩ E) ⟨197568686208,6507939289⟩ (N E ⟨197568687104,4834930976⟩ E)) ⟨197568687360,4395170829⟩ (N (N E ⟨197568687616,3973751300⟩ E) ⟨197568687872,3571324368⟩ (N E ⟨197568688000,3377422809⟩ E))) ⟨197568688128,3188490500⟩ (N (N (N E ⟨197568688640,2483741266⟩ E) ⟨197568688768,2320591584⟩ (N E ⟨197568689280,1721645940⟩ E)) ⟨197568689408,1585530720⟩ (N (N E ⟨197568689536,1454935186⟩ E) ⟨197568689664,1329888956⟩ E))) ⟨197568689920,1096545770⟩ (N (N (N (N E ⟨197568690176,885669736⟩ E) ⟨197568690304,788694673⟩ (N E ⟨197568690432,697374939⟩ E)) ⟨197568690560,611716331⟩ (N (N E ⟨197568690688,531721289⟩ E) ⟨197568690816,457388911⟩ E)) ⟨197568690944,388714969⟩ (N (N (N E ⟨197568691072,325691933⟩ E) ⟨197568691200,268308993⟩ (N E ⟨197568692224,9929527⟩ E)) ⟨197702905344,3983954954⟩ (N (N E ⟨197837124608,1874752748⟩ E) ⟨197837126144,536554969⟩ E)))) ⟨198508216320,11627099⟩ (N (N (N (N (N E ⟨199045083648,2559893941⟩ E) ⟨199179303040,825022945⟩ (N E ⟨199313520256,1263232580⟩ E)) ⟨199313521152,561799844⟩ (N (N E ⟨199313522688,13044239⟩ E) ⟨199581955968,1040704766⟩ (N E ⟨199581956736,488549031⟩ E))) ⟨199581958144,13503116⟩ (N (N (N E ⟨199716173184,1528239640⟩ E) ⟨199716175360,107486199⟩ (N E ⟨199850393472,29119488⟩ E)) ⟨199984609536,746204443⟩ (N (N E ⟨199984611072,50310684⟩ E) ⟨200118828800,50755346⟩ E))) ⟨200253043712,1971394340⟩ (N (N (N (N E ⟨200387263104,499761239⟩ E) ⟨200387264256,51625781⟩ (N E ⟨200655698048,854989792⟩ E)) ⟨200655698944,300925421⟩ (N (N E ⟨200655699200,195080240⟩ E) ⟨200789915008,1561318186⟩ E)) ⟨200789915904,760631337⟩ (N (N (N E ⟨200789916800,246175590⟩ E) ⟨200789917440,52881731⟩ (N E ⟨200924135168,53286484⟩ E)) ⟨201058351616,588177608⟩ (N (N E ⟨201058352384,197804290⟩ E) ⟨201058352768,81109366⟩ E)))))) ⟨201058353152,15844541⟩ (N (N (N (N (N (N (N E ⟨201326788096,115476336⟩ E) ⟨201326788608,16228754⟩ (N E ⟨201461005568,200393265⟩ E)) ⟨201461006080,54831888⟩ (N (N E ⟨201595222144,872128024⟩ E) ⟨201595223040,309116349⟩ (N E ⟨201595224064,16597792⟩ E))) ⟨201729440896,253195154⟩ (N (N (N E ⟨201729441792,16776340⟩ E) ⟨201863657472,981174150⟩ (N E ⟨201863657984,598883182⟩ E)) ⟨201863659520,16950765⟩ (N (N E ⟨201997876480,203625213⟩ E) ⟨201997876608,158064125⟩ E))) ⟨201997876992,56252492⟩ (N (N (N (N E ⟨201997877248,17120960⟩ E) ⟨202132094976,17286823⟩ (N E ⟨202266311936,205143294⟩ E)) ⟨202266312448,56913228⟩ (N (N E ⟨202400528896,605456107⟩ E) ⟨202400529408,315367323⟩ (N E ⟨202400529792,159961715⟩ E))) ⟨202400530176,57230749⟩ (N (N (N E ⟨202668965504,86454684⟩ E) ⟨202803183360,58130471⟩ (N E ⟨202803183616,18047760⟩ E)) ⟨202937400576,208641122⟩ (N (N E ⟨202937401344,18185629⟩ E) ⟨203205836160,163349824⟩ E)))) ⟨203205836544,58948537⟩ (N (N (N (N (N E ⟨203205836800,18446369⟩ E) ⟨203340054400,35996095⟩ (N E ⟨203340054528,18569082⟩ E)) ⟨203474271872,88546122⟩ (N (N E ⟨203608489344,164832278⟩ E) ⟨203608489728,59682118⟩ (N E ⟨204011143168,19103216⟩ E))) ⟨204145360640,60524474⟩ (N (N (N E ⟨204145360896,19193707⟩ E) ⟨204279578624,19278617⟩ (N E ⟨204413796352,19357895⟩ E)) ⟨204548014080,19431494⟩ (N (N E ⟨206158626944,7536840⟩ E) ⟨206158627072,1073573⟩ E))) ⟨206561281408,440967⟩ (N (N (N (N E ⟨206561281536,439827⟩ E) ⟨206561281664,438691⟩ (N E ⟨206561281792,437558⟩ E)) ⟨206561281920,436429⟩ (N (N E ⟨206561282048,435304⟩ E) ⟨206561282176,434182⟩ E)) ⟨206561282304,433064⟩ (N (N (N E ⟨206561282432,431950⟩ E) ⟨206561282560,430839⟩ (N E ⟨206561282688,429732⟩ E)) ⟨206561282816,428628⟩ (N (N E ⟨206561282944,427528⟩ E) ⟨206561283072,426431⟩ E))))) ⟨206561283200,425338⟩ (N (N (N (N (N (N E ⟨206561283328,424248⟩ E) ⟨206561283456,423162⟩ (N E ⟨206561283584,422079⟩ E)) ⟨206561283712,421000⟩ (N (N E ⟨206561283840,419924⟩ E) ⟨206561283968,418852⟩ (N E ⟨206561284096,417783⟩ E))) ⟨206561284224,416718⟩ (N (N (N E ⟨206561284352,415656⟩ E) ⟨206561284480,414597⟩ (N E ⟨206561284608,413541⟩ E)) ⟨206561284736,412489⟩ (N (N E ⟨206561284864,411441⟩ E) ⟨206561284992,410395⟩ E))) ⟨206561285120,409353⟩ (N (N (N (N E ⟨206561285248,408315⟩ E) ⟨206561285376,407279⟩ (N E ⟨206561285504,406247⟩ E)) ⟨206561285632,405218⟩ (N (N E ⟨206561285760,404193⟩ E) ⟨206561285888,403170⟩ E)) ⟨206561286016,402151⟩ (N (N (N E ⟨206561286272,400123⟩ E) ⟨206561286400,399113⟩ (N E ⟨206561286656,397104⟩ E)) ⟨206561286784,396104⟩ (N (N E ⟨206561286912,395107⟩ E) ⟨206561287040,394113⟩ E)))) ⟨206561287168,393122⟩ (N (N (N (N (N E ⟨206561287296,392135⟩ E) ⟨206561287552,390169⟩ (N E ⟨206561287808,388216⟩ E)) ⟨206561288064,386275⟩ (N (N E ⟨206561288192,385309⟩ E) ⟨206695499136,5542695⟩ (N E ⟨206695499264,5528367⟩ E))) ⟨206695499392,5514085⟩ (N (N (N E ⟨206695499520,5499850⟩ E) ⟨206695499648,5485660⟩ (N E ⟨206695499776,5471516⟩ E)) ⟨206695499904,5457417⟩ (N (N E ⟨206695500032,5443364⟩ E) ⟨206695500160,5429356⟩ E))) ⟨206695500288,5415393⟩ (N (N (N (N E ⟨206695500416,5401475⟩ E) ⟨206695500544,5387602⟩ (N E ⟨206695500672,5373773⟩ E)) ⟨206695500800,5359988⟩ (N (N E ⟨206695500928,5346248⟩ E) ⟨206695501056,5332552⟩ E)) ⟨206695501184,5318899⟩ (N (N (N E ⟨206695501312,5305291⟩ E) ⟨206695501440,5291725⟩ (N E ⟨206695501568,5278204⟩ E)) ⟨206695501696,5264725⟩ (N (N E ⟨206695501824,5251289⟩ E) ⟨206695501952,5237896⟩ E)))))))

noncomputable def tab17 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨206695502208,5211238⟩ E) ⟨206695502336,5197973⟩ (N E ⟨206695502464,5184750⟩ E)) ⟨206695502592,5171569⟩ (N (N E ⟨206695502720,5158430⟩ E) ⟨206695502848,5145332⟩ (N E ⟨206695502976,5132276⟩ E))) ⟨206695503104,5119262⟩ (N (N (N E ⟨206695503232,5106288⟩ E) ⟨206695503360,5093356⟩ (N E ⟨206695503488,5080465⟩ E)) ⟨206695503616,5067614⟩ (N (N E ⟨206695503744,5054804⟩ E) ⟨206695503872,5042035⟩ E))) ⟨206695504000,5029306⟩ (N (N (N (N E ⟨206695504128,5016617⟩ E) ⟨206695504256,5003968⟩ (N E ⟨206695504384,4991359⟩ E)) ⟨206695504512,4978789⟩ (N (N E ⟨206695504640,4966259⟩ E) ⟨206695504768,4953769⟩ (N E ⟨206695504896,4941318⟩ E))) ⟨206695505024,4928905⟩ (N (N (N E ⟨206695505280,4904198⟩ E) ⟨206695505408,4891902⟩ (N E ⟨206695505536,4879645⟩ E)) ⟨206695505664,4867426⟩ (N (N E ⟨206695505792,4855246⟩ E) ⟨206695505920,4843103⟩ E)))) ⟨206829716992,16330744⟩ (N (N (N (N (N E ⟨206829717120,16288555⟩ E) ⟨206829717248,16246503⟩ (N E ⟨206829717376,16204586⟩ E)) ⟨206829717504,16162804⟩ (N (N E ⟨206829717632,16121157⟩ E) ⟨206829717760,16079645⟩ (N E ⟨206829717888,16038265⟩ E))) ⟨206829718016,15997019⟩ (N (N (N E ⟨206829718144,15955905⟩ E) ⟨206829718272,15914924⟩ (N E ⟨206829718400,15874073⟩ E)) ⟨206829718528,15833354⟩ (N (N E ⟨206829718656,15792766⟩ E) ⟨206829718784,15752307⟩ E))) ⟨206829718912,15711978⟩ (N (N (N (N E ⟨206829719040,15671778⟩ E) ⟨206829719168,15631706⟩ (N E ⟨206829719296,15591763⟩ E)) ⟨206829719424,15551947⟩ (N (N E ⟨206829719552,15512258⟩ E) ⟨206829719680,15472695⟩ E)) ⟨206829719808,15433259⟩ (N (N (N E ⟨206829719936,15393948⟩ E) ⟨206829720064,15354763⟩ (N E ⟨206829720192,15315702⟩ E)) ⟨206829720320,15276765⟩ (N (N E ⟨206829720448,15237952⟩ E) ⟨206829720576,15199262⟩ E))))) ⟨206829720704,15160695⟩ (N (N (N (N (N (N E ⟨206829720960,15083927⟩ E) ⟨206829721088,15045725⟩ (N E ⟨206829721216,15007644⟩ E)) ⟨206829721344,14969684⟩ (N (N E ⟨206829721472,14931844⟩ E) ⟨206829721856,14819038⟩ (N E ⟨206829722112,14744425⟩ E))) ⟨206829722240,14707295⟩ (N (N (N E ⟨206829722368,14670282⟩ E) ⟨206829722624,14596605⟩ (N E ⟨206829723008,14486953⟩ E)) ⟨206829723136,14450632⟩ (N (N E ⟨206829723264,14414425⟩ E) ⟨206829723520,14342349⟩ E))) ⟨206829723648,14306480⟩ (N (N (N (N E ⟨206963934720,32862579⟩ E) ⟨206963934848,32777683⟩ (N E ⟨206963934976,32693060⟩ E)) ⟨206963935104,32608710⟩ (N (N E ⟨206963935232,32524633⟩ E) ⟨206963935360,32440826⟩ E)) ⟨206963935488,32357289⟩ (N (N (N E ⟨206963935616,32274021⟩ E) ⟨206963935744,32191020⟩ (N E ⟨206963935872,32108287⟩ E)) ⟨206963936000,32025819⟩ (N (N E ⟨206963936128,31943615⟩ E) ⟨206963936256,31861675⟩ E)))) ⟨206963936384,31779998⟩ (N (N (N (N (N E ⟨206963936512,31698583⟩ E) ⟨206963936640,31617428⟩ (N E ⟨206963936768,31536533⟩ E)) ⟨206963936896,31455896⟩ (N (N E ⟨206963937024,31375517⟩ E) ⟨206963937152,31295395⟩ (N E ⟨206963937280,31215528⟩ E))) ⟨206963937408,31135917⟩ (N (N (N E ⟨206963937536,31056558⟩ E) ⟨206963937664,30977453⟩ (N E ⟨206963937792,30898599⟩ E)) ⟨206963937920,30819996⟩ (N (N E ⟨206963938048,30741643⟩ E) ⟨206963938176,30663539⟩ E))) ⟨206963938304,30585683⟩ (N (N (N (N E ⟨206963938432,30508074⟩ E) ⟨206963938560,30430710⟩ (N E ⟨206963938688,30353592⟩ E)) ⟨206963938816,30276719⟩ (N (N E ⟨206963938944,30200088⟩ E) ⟨206963939072,30123700⟩ E)) ⟨206963939200,30047553⟩ (N (N (N E ⟨206963939456,29895980⟩ E) ⟨206963939584,29820552⟩ (N E ⟨206963939712,29745362⟩ E)) ⟨206963939840,29670409⟩ (N (N E ⟨206963940096,29521210⟩ E) ⟨206963940224,29446962⟩ E)))))) ⟨206963940480,29299165⟩ (N (N (N (N (N (N (N E ⟨206963940608,29225615⟩ E) ⟨206963940736,29152295⟩ (N E ⟨206963940864,29079205⟩ E)) ⟨206963940992,29006344⟩ (N (N E ⟨206963941120,28933711⟩ E) ⟨206963941248,28861305⟩ (N E ⟨206963941376,28789126⟩ E))) ⟨207098152576,54993603⟩ (N (N (N E ⟨207098152704,54851626⟩ E) ⟨207098152832,54710106⟩ (N E ⟨207098152960,54569042⟩ E)) ⟨207098153088,54428433⟩ (N (N E ⟨207098153216,54288277⟩ E) ⟨207098153344,54148572⟩ E))) ⟨207098153472,54009316⟩ (N (N (N (N E ⟨207098153600,53870507⟩ E) ⟨207098153728,53732144⟩ (N E ⟨207098153856,53594225⟩ E)) ⟨207098153984,53456749⟩ (N (N E ⟨207098154112,53319713⟩ E) ⟨207098154240,53183116⟩ (N E ⟨207098154368,53046957⟩ E))) ⟨207098154496,52911233⟩ (N (N (N E ⟨207098154624,52775943⟩ E) ⟨207098154752,52641085⟩ (N E ⟨207098154880,52506657⟩ E)) ⟨207098155008,52372659⟩ (N (N E ⟨207098155136,52239088⟩ E) ⟨207098155264,52105943⟩ E)))) ⟨207098155392,51973221⟩ (N (N (N (N (N E ⟨207098155520,51840923⟩ E) ⟨207098155648,51709045⟩ (N E ⟨207098155776,51577586⟩ E)) ⟨207098155904,51446544⟩ (N (N E ⟨207098156032,51315919⟩ E) ⟨207098156160,51185708⟩ (N E ⟨207098156288,51055910⟩ E))) ⟨207098156416,50926524⟩ (N (N (N E ⟨207098156544,50797547⟩ E) ⟨207098156672,50668978⟩ (N E ⟨207098156800,50540816⟩ E)) ⟨207098156928,50413058⟩ (N (N E ⟨207098157056,50285705⟩ E) ⟨207098157184,50158753⟩ E))) ⟨207098157312,50032202⟩ (N (N (N (N E ⟨207098157440,49906050⟩ E) ⟨207098157568,49780295⟩ (N E ⟨207098157696,49654936⟩ E)) ⟨207098157824,49529972⟩ (N (N E ⟨207098157952,49405401⟩ E) ⟨207098158080,49281221⟩ E)) ⟨207098158336,49034030⟩ (N (N (N E ⟨207098158464,48911016⟩ E) ⟨207098158592,48788387⟩ (N E ⟨207098158720,48666143⟩ E)) ⟨207098158848,48544281⟩ (N (N E ⟨207098158976,48422801⟩ E) ⟨207098159104,48301700⟩ E))))) ⟨207232370432,82730851⟩ (N (N (N (N (N (N E ⟨207232370560,82517401⟩ E) ⟨207232370688,82304640⟩ (N E ⟨207232370816,82092564⟩ E)) ⟨207232370944,81881171⟩ (N (N E ⟨207232371072,81670458⟩ E) ⟨207232371200,81460423⟩ (N E ⟨207232371328,81251062⟩ E))) ⟨207232371456,81042374⟩ (N (N (N E ⟨207232371584,80834356⟩ E) ⟨207232371712,80627005⟩ (N E ⟨207232371840,80420319⟩ E)) ⟨207232371968,80214294⟩ (N (N E ⟨207232372096,80008929⟩ E) ⟨207232372224,79804221⟩ E))) ⟨207232372352,79600168⟩ (N (N (N (N E ⟨207232372480,79396766⟩ E) ⟨207232372608,79194014⟩ (N E ⟨207232372736,78991909⟩ E)) ⟨207232372864,78790449⟩ (N (N E ⟨207232372992,78589630⟩ E) ⟨207232373120,78389451⟩ E)) ⟨207232373248,78189909⟩ (N (N (N E ⟨207232373376,77991002⟩ E) ⟨207232373504,77792727⟩ (N E ⟨207232373632,77595082⟩ E)) ⟨207232373760,77398064⟩ (N (N E ⟨207232373888,77201672⟩ E) ⟨207232374016,77005902⟩ E)))) ⟨207232374144,76810752⟩ (N (N (N (N (N E ⟨207232374272,76616220⟩ E) ⟨207232374528,76229002⟩ (N E ⟨207232374656,76036310⟩ E)) ⟨207232374784,75844227⟩ (N (N E ⟨207232374912,75652750⟩ E) ⟨207232375040,75461877⟩ (N E ⟨207232375168,75271606⟩ E))) ⟨207232375296,75081935⟩ (N (N (N E ⟨207232375424,74892860⟩ E) ⟨207232375552,74704381⟩ (N E ⟨207232375808,74329198⟩ E)) ⟨207232375936,74142490⟩ (N (N E ⟨207232376064,73956368⟩ E) ⟨207232376192,73770830⟩ E))) ⟨207232376448,73401496⟩ (N (N (N (N E ⟨207232376576,73217696⟩ E) ⟨207232376704,73034472⟩ (N E ⟨207232376832,72851820⟩ E)) ⟨207366588288,116035765⟩ (N (N E ⟨207366588416,115736581⟩ E) ⟨207366588544,115438360⟩ E)) ⟨207366588672,115141100⟩ (N (N (N E ⟨207366588800,114844796⟩ E) ⟨207366588928,114549445⟩ (N E ⟨207366589056,114255043⟩ E)) ⟨207366589184,113961586⟩ (N (N E ⟨207366589312,113669072⟩ E) ⟨207366589440,113377495⟩ E)))))))

noncomputable def tab18 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨207366589696,112797142⟩ E) ⟨207366589824,112508359⟩ (N E ⟨207366589952,112220499⟩ E)) ⟨207366590080,111933559⟩ (N (N E ⟨207366590208,111647537⟩ E) ⟨207366590464,111078227⟩ (N E ⟨207366590592,110794934⟩ E))) ⟨207366590720,110512543⟩ (N (N (N E ⟨207366590848,110231052⟩ E) ⟨207366590976,109950457⟩ (N E ⟨207366591104,109670754⟩ E)) ⟨207366591232,109391940⟩ (N (N E ⟨207366591360,109114012⟩ E) ⟨207366591488,108836966⟩ E))) ⟨207366591616,108560799⟩ (N (N (N (N E ⟨207366591744,108285508⟩ E) ⟨207366591872,108011089⟩ (N E ⟨207366592000,107737540⟩ E)) ⟨207366592128,107464855⟩ (N (N E ⟨207366592256,107193034⟩ E) ⟨207366592384,106922071⟩ (N E ⟨207366592512,106651964⟩ E))) ⟨207366592640,106382710⟩ (N (N (N E ⟨207366592768,106114305⟩ E) ⟨207366592896,105846746⟩ (N E ⟨207366593024,105580031⟩ E)) ⟨207366593152,105314155⟩ (N (N E ⟨207366593280,105049115⟩ E) ⟨207366593408,104784910⟩ E)))) ⟨207366593536,104521534⟩ (N (N (N (N (N E ⟨207366593664,104258986⟩ E) ⟨207366593792,103997262⟩ (N E ⟨207366593920,103736358⟩ E)) ⟨207366594048,103476273⟩ (N (N E ⟨207366594432,102700893⟩ E) ⟨207366594560,102444049⟩ (N E ⟨207500806144,154866559⟩ E))) ⟨207500806272,154467512⟩ (N (N (N E ⟨207500806400,154069749⟩ E) ⟨207500806528,153673267⟩ (N E ⟨207500806656,153278059⟩ E)) ⟨207500806784,152884121⟩ (N (N E ⟨207500806912,152491448⟩ E) ⟨207500807040,152100035⟩ E))) ⟨207500807168,151709878⟩ (N (N (N (N E ⟨207500807296,151320972⟩ E) ⟨207500807424,150933311⟩ (N E ⟨207500807552,150546891⟩ E)) ⟨207500807680,150161707⟩ (N (N E ⟨207500807808,149777755⟩ E) ⟨207500807936,149395029⟩ E)) ⟨207500808064,149013525⟩ (N (N (N E ⟨207500808192,148633239⟩ E) ⟨207500808320,148254166⟩ (N E ⟨207500808448,147876300⟩ E)) ⟨207500808576,147499638⟩ (N (N E ⟨207500808704,147124175⟩ E) ⟨207500808832,146749906⟩ E))))) ⟨207500808960,146376826⟩ (N (N (N (N (N (N E ⟨207500809088,146004932⟩ E) ⟨207500809216,145634218⟩ (N E ⟨207500809344,145264681⟩ E)) ⟨207500809472,144896315⟩ (N (N E ⟨207500809600,144529117⟩ E) ⟨207500809728,144163081⟩ (N E ⟨207500809856,143798203⟩ E))) ⟨207500809984,143434480⟩ (N (N (N E ⟨207500810112,143071906⟩ E) ⟨207500810240,142710477⟩ (N E ⟨207500810368,142350190⟩ E)) ⟨207500810496,141991038⟩ (N (N E ⟨207500810624,141633020⟩ E) ⟨207500810752,141276129⟩ E))) ⟨207500810880,140920361⟩ (N (N (N (N E ⟨207500811008,140565714⟩ E) ⟨207500811136,140212181⟩ (N E ⟨207500811264,139859760⟩ E)) ⟨207500811392,139508445⟩ (N (N E ⟨207500811520,139158233⟩ E) ⟨207500811648,138809119⟩ E)) ⟨207500811776,138461100⟩ (N (N (N E ⟨207500812032,137768329⟩ E) ⟨207500812160,137423569⟩ (N E ⟨207500812288,137079886⟩ E)) ⟨207635024000,199178245⟩ (N (N E ⟨207635024128,198665350⟩ E) ⟨207635024256,198154105⟩ E)))) ⟨207635024384,197644504⟩ (N (N (N (N (N E ⟨207635024512,197136540⟩ E) ⟨207635024640,196630208⟩ (N E ⟨207635024768,196125501⟩ E)) ⟨207635024896,195622412⟩ (N (N E ⟨207635025024,195120936⟩ E) ⟨207635025152,194621067⟩ (N E ⟨207635025280,194122797⟩ E))) ⟨207635025408,193626122⟩ (N (N (N E ⟨207635025536,193131034⟩ E) ⟨207635025664,192637528⟩ (N E ⟨207635025792,192145598⟩ E)) ⟨207635025920,191655238⟩ (N (N E ⟨207635026048,191166441⟩ E) ⟨207635026176,190679202⟩ E))) ⟨207635026304,190193515⟩ (N (N (N (N E ⟨207635026432,189709374⟩ E) ⟨207635026560,189226772⟩ (N E ⟨207635026688,188745705⟩ E)) ⟨207635026816,188266165⟩ (N (N E ⟨207635026944,187788149⟩ E) ⟨207635027072,187311648⟩ E)) ⟨207635027200,186836659⟩ (N (N (N E ⟨207635027328,186363174⟩ E) ⟨207635027456,185891189⟩ (N E ⟨207635027584,185420698⟩ E)) ⟨207635027712,184951694⟩ (N (N E ⟨207635027840,184484173⟩ E) ⟨207635027968,184018129⟩ E)))))) ⟨207635028096,183553555⟩ (N (N (N (N (N (N (N E ⟨207635028224,183090448⟩ E) ⟨207635028352,182628800⟩ (N E ⟨207635028480,182168606⟩ E)) ⟨207635028736,181252561⟩ (N (N E ⟨207635028864,180796698⟩ E) ⟨207635028992,180342268⟩ (N E ⟨207635029248,179437684⟩ E))) ⟨207635029376,178987520⟩ (N (N (N E ⟨207635029504,178538766⟩ E) ⟨207635029632,178091419⟩ (N E ⟨207635029760,177645472⟩ E)) ⟨207635029888,177200920⟩ (N (N E ⟨207635030016,176757759⟩ E) ⟨207769241856,248922671⟩ E))) ⟨207769241984,248282094⟩ (N (N (N (N E ⟨207769242112,247643577⟩ E) ⟨207769242240,247007111⟩ (N E ⟨207769242368,246372690⟩ E)) ⟨207769242496,245740304⟩ (N (N E ⟨207769242624,245109947⟩ E) ⟨207769242752,244481611⟩ (N E ⟨207769242880,243855286⟩ E))) ⟨207769243008,243230967⟩ (N (N (N E ⟨207769243136,242608646⟩ E) ⟨207769243264,241988313⟩ (N E ⟨207769243392,241369963⟩ E)) ⟨207769243520,240753587⟩ (N (N E ⟨207769243648,240139178⟩ E) ⟨207769243776,239526728⟩ E)))) ⟨207769243904,238916230⟩ (N (N (N (N (N E ⟨207769244032,238307676⟩ E) ⟨207769244160,237701059⟩ (N E ⟨207769244288,237096371⟩ E)) ⟨207769244416,236493606⟩ (N (N E ⟨207769244544,235892755⟩ E) ⟨207769244672,235293812⟩ (N E ⟨207769244800,234696769⟩ E))) ⟨207769244928,234101620⟩ (N (N (N E ⟨207769245056,233508356⟩ E) ⟨207769245184,232916970⟩ (N E ⟨207769245312,232327456⟩ E)) ⟨207769245440,231739807⟩ (N (N E ⟨207769245568,231154014⟩ E) ⟨207769245696,230570072⟩ E))) ⟨207769245824,229987974⟩ (N (N (N (N E ⟨207769245952,229407711⟩ E) ⟨207769246080,228829278⟩ (N E ⟨207769246208,228252668⟩ E)) ⟨207769246336,227677873⟩ (N (N E ⟨207769246464,227104886⟩ E) ⟨207769246720,225964312⟩ E)) ⟨207769246848,225396711⟩ (N (N (N E ⟨207769247104,224266846⟩ E) ⟨207769247232,223704570⟩ (N E ⟨207769247360,223144055⟩ E)) ⟨207769247488,222585294⟩ (N (N E ⟨207769247616,222028282⟩ E) ⟨207769247744,221473012⟩ E))))) ⟨207903459712,304048558⟩ (N (N (N (N (N (N E ⟨207903459840,303266624⟩ E) ⟨207903459968,302487202⟩ (N E ⟨207903460096,301710284⟩ E)) ⟨207903460224,300935859⟩ (N (N E ⟨207903460352,300163918⟩ E) ⟨207903460480,299394451⟩ (N E ⟨207903460608,298627449⟩ E))) ⟨207903460736,297862902⟩ (N (N (N E ⟨207903460864,297100800⟩ E) ⟨207903460992,296341136⟩ (N E ⟨207903461120,295583898⟩ E)) ⟨207903461248,294829078⟩ (N (N E ⟨207903461376,294076667⟩ E) ⟨207903461504,293326655⟩ E))) ⟨207903461632,292579034⟩ (N (N (N (N E ⟨207903461760,291833793⟩ E) ⟨207903461888,291090924⟩ (N E ⟨207903462016,290350418⟩ E)) ⟨207903462144,289612266⟩ (N (N E ⟨207903462272,288876459⟩ E) ⟨207903462400,288142988⟩ E)) ⟨207903462528,287411843⟩ (N (N (N E ⟨207903462656,286683017⟩ E) ⟨207903462784,285956501⟩ (N E ⟨207903462912,285232285⟩ E)) ⟨207903463040,284510360⟩ (N (N E ⟨207903463168,283790719⟩ E) ⟨207903463296,283073353⟩ E)))) ⟨207903463424,282358252⟩ (N (N (N (N (N E ⟨207903463552,281645409⟩ E) ⟨207903463680,280934814⟩ (N E ⟨207903463808,280226459⟩ E)) ⟨207903463936,279520337⟩ (N (N E ⟨207903464064,278816437⟩ E) ⟨207903464192,278114753⟩ (N E ⟨207903464320,277415275⟩ E))) ⟨207903464448,276717995⟩ (N (N (N E ⟨207903464576,276022906⟩ E) ⟨207903464704,275329997⟩ (N E ⟨207903464832,274639263⟩ E)) ⟨207903464960,273950694⟩ (N (N E ⟨207903465088,273264282⟩ E) ⟨207903465216,272580019⟩ E))) ⟨207903465344,271897897⟩ (N (N (N (N E ⟨207903465472,271217907⟩ E) ⟨208037677568,364501539⟩ (N E ⟨208037677696,363564738⟩ E)) ⟨208037677824,362630946⟩ (N (N E ⟨208037677952,361700151⟩ E) ⟨208037678080,360772341⟩ E)) ⟨208037678208,359847505⟩ (N (N (N E ⟨208037678336,358925632⟩ E) ⟨208037678464,358006709⟩ (N E ⟨208037678592,357090726⟩ E)) ⟨208037678720,356177672⟩ (N (N E ⟨208037678848,355267534⟩ E) ⟨208037678976,354360303⟩ E)))))))

noncomputable def tab19 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨208037679232,352554514⟩ E) ⟨208037679360,351655934⟩ (N E ⟨208037679488,350760216⟩ E)) ⟨208037679616,349867349⟩ (N (N E ⟨208037679744,348977322⟩ E) ⟨208037679872,348090124⟩ (N E ⟨208037680000,347205744⟩ E))) ⟨208037680128,346324172⟩ (N (N (N E ⟨208037680256,345445397⟩ E) ⟨208037680384,344569408⟩ (N E ⟨208037680512,343696195⟩ E)) ⟨208037680640,342825746⟩ (N (N E ⟨208037680768,341958053⟩ E) ⟨208037680896,341093103⟩ E))) ⟨208037681024,340230888⟩ (N (N (N (N E ⟨208037681152,339371396⟩ E) ⟨208037681280,338514616⟩ (N E ⟨208037681408,337660540⟩ E)) ⟨208037681536,336809156⟩ (N (N E ⟨208037681664,335960455⟩ E) ⟨208037681792,335114426⟩ (N E ⟨208037681920,334271059⟩ E))) ⟨208037682048,333430344⟩ (N (N (N E ⟨208037682176,332592271⟩ E) ⟨208037682304,331756830⟩ (N E ⟨208037682560,330093806⟩ E)) ⟨208037682688,329266202⟩ (N (N E ⟨208037682816,328441191⟩ E) ⟨208037682944,327618763⟩ E)))) ⟨208037683072,326798909⟩ (N (N (N (N (N E ⟨208037683200,325981618⟩ E) ⟨208171895424,430224198⟩ (N E ⟨208171895552,429119196⟩ E)) ⟨208171895680,428017739⟩ (N (N E ⟨208171895808,426919816⟩ E) ⟨208171895936,425825412⟩ (N E ⟨208171896064,424734513⟩ E))) ⟨208171896192,423647106⟩ (N (N (N E ⟨208171896320,422563178⟩ E) ⟨208171896448,421482715⟩ (N E ⟨208171896576,420405705⟩ E)) ⟨208171896704,419332133⟩ (N (N E ⟨208171896832,418261987⟩ E) ⟨208171896960,417195253⟩ E))) ⟨208171897088,416131919⟩ (N (N (N (N E ⟨208171897216,415071972⟩ E) ⟨208171897344,414015398⟩ (N E ⟨208171897472,412962184⟩ E)) ⟨208171897600,411912319⟩ (N (N E ⟨208171897728,410865788⟩ E) ⟨208171897856,409822580⟩ E)) ⟨208171897984,408782682⟩ (N (N (N E ⟨208171898112,407746081⟩ E) ⟨208171898240,406712764⟩ (N E ⟨208171898368,405682720⟩ E)) ⟨208171898496,404655935⟩ (N (N E ⟨208171898624,403632397⟩ E) ⟨208171898752,402612095⟩ E))))) ⟨208171898880,401595015⟩ (N (N (N (N (N (N E ⟨208171899008,400581146⟩ E) ⟨208171899136,399570475⟩ (N E ⟨208171899264,398562990⟩ E)) ⟨208171899392,397558679⟩ (N (N E ⟨208171899520,396557531⟩ E) ⟨208171899648,395559533⟩ (N E ⟨208171899776,394564673⟩ E))) ⟨208171899904,393572940⟩ (N (N (N E ⟨208171900032,392584322⟩ E) ⟨208171900160,391598806⟩ (N E ⟨208171900288,390616382⟩ E)) ⟨208171900672,387687542⟩ (N (N E ⟨208171900800,386717367⟩ E) ⟨208171900928,385750226⟩ E))) ⟨208306113408,499869755⟩ (N (N (N (N E ⟨208306113536,498587522⟩ E) ⟨208306113664,497309398⟩ (N E ⟨208306113792,496035368⟩ E)) ⟨208306113920,494765417⟩ (N (N E ⟨208306114048,493499528⟩ E) ⟨208306114176,492237687⟩ E)) ⟨208306114304,490979877⟩ (N (N (N E ⟨208306114432,489726083⟩ E) ⟨208306114560,488476289⟩ (N E ⟨208306114688,487230481⟩ E)) ⟨208306114816,485988644⟩ (N (N E ⟨208306114944,484750761⟩ E) ⟨208306115072,483516818⟩ E)))) ⟨208306115200,482286800⟩ (N (N (N (N (N E ⟨208306115328,481060692⟩ E) ⟨208306115456,479838479⟩ (N E ⟨208306115584,478620146⟩ E)) ⟨208306115712,477405678⟩ (N (N E ⟨208306115840,476195061⟩ E) ⟨208306115968,474988280⟩ (N E ⟨208306116096,473785320⟩ E))) ⟨208306116224,472586168⟩ (N (N (N E ⟨208306116352,471390807⟩ E) ⟨208306116480,470199225⟩ (N E ⟨208306116608,469011406⟩ E)) ⟨208306116736,467827337⟩ (N (N E ⟨208306116864,466647003⟩ E) ⟨208306116992,465470390⟩ E))) ⟨208306117120,464297485⟩ (N (N (N (N E ⟨208306117248,463128272⟩ E) ⟨208306117376,461962738⟩ (N E ⟨208306117504,460800870⟩ E)) ⟨208306117632,459642653⟩ (N (N E ⟨208306117760,458488074⟩ E) ⟨208306117888,457337118⟩ E)) ⟨208306118016,456189773⟩ (N (N (N E ⟨208306118144,455046024⟩ E) ⟨208306118272,453905859⟩ (N E ⟨208306118400,452769263⟩ E)) ⟨208306118528,451636224⟩ (N (N E ⟨208306118656,450506728⟩ E) ⟨208440331264,575753223⟩ E)))))) ⟨208440331392,574277286⟩ (N (N (N (N (N (N (N E ⟨208440331520,572806076⟩ E) ⟨208440331648,571339576⟩ (N E ⟨208440331776,569877768⟩ E)) ⟨208440331904,568420633⟩ (N (N E ⟨208440332032,566968153⟩ E) ⟨208440332160,565520311⟩ (N E ⟨208440332288,564077089⟩ E))) ⟨208440332416,562638469⟩ (N (N (N E ⟨208440332544,561204434⟩ E) ⟨208440332672,559774966⟩ (N E ⟨208440332800,558350048⟩ E)) ⟨208440332928,556929662⟩ (N (N E ⟨208440333056,555513790⟩ E) ⟨208440333184,554102417⟩ E))) ⟨208440333312,552695524⟩ (N (N (N (N E ⟨208440333440,551293095⟩ E) ⟨208440333568,549895112⟩ (N E ⟨208440333696,548501559⟩ E)) ⟨208440333824,547112419⟩ (N (N E ⟨208440333952,545727675⟩ E) ⟨208440334080,544347311⟩ (N E ⟨208440334208,542971309⟩ E))) ⟨208440334336,541599653⟩ (N (N (N E ⟨208440334464,540232327⟩ E) ⟨208440334592,538869315⟩ (N E ⟨208440334720,537510599⟩ E)) ⟨208440334848,536156164⟩ (N (N E ⟨208440335104,533460073⟩ E) ⟨208440335232,532118383⟩ E)))) ⟨208440335488,529447639⟩ (N (N (N (N (N E ⟨208440335616,528118552⟩ E) ⟨208440335744,526793633⟩ (N E ⟨208440335872,525472868⟩ E)) ⟨208440336000,524156241⟩ (N (N E ⟨208440336128,522843736⟩ E) ⟨208440336256,521535338⟩ (N E ⟨208440336384,520231031⟩ E))) ⟨208574549120,656703495⟩ (N (N (N E ⟨208574549248,655021122⟩ E) ⟨208574549376,653344135⟩ (N E ⟨208574549504,651672512⟩ E)) ⟨208574549632,650006234⟩ (N (N E ⟨208574549760,648345280⟩ E) ⟨208574549888,646689628⟩ E))) ⟨208574550016,645039260⟩ (N (N (N (N E ⟨208574550144,643394155⟩ E) ⟨208574550272,641754292⟩ (N E ⟨208574550400,640119652⟩ E)) ⟨208574550528,638490215⟩ (N (N E ⟨208574550656,636865960⟩ E) ⟨208574550784,635246868⟩ E)) ⟨208574550912,633632920⟩ (N (N (N E ⟨208574551040,632024096⟩ E) ⟨208574551168,630420375⟩ (N E ⟨208574551296,628821740⟩ E)) ⟨208574551424,627228170⟩ (N (N E ⟨208574551552,625639646⟩ E) ⟨208574551680,624056149⟩ E))))) ⟨208574551808,622477660⟩ (N (N (N (N (N (N E ⟨208574551936,620904160⟩ E) ⟨208574552064,619335630⟩ (N E ⟨208574552192,617772052⟩ E)) ⟨208574552320,616213406⟩ (N (N E ⟨208574552448,614659673⟩ E) ⟨208574552576,613110836⟩ (N E ⟨208574552704,611566875⟩ E))) ⟨208574552960,608493511⟩ (N (N (N E ⟨208574553088,606964071⟩ E) ⟨208574553216,605439434⟩ (N E ⟨208574553344,603919582⟩ E)) ⟨208574553472,602404498⟩ (N (N E ⟨208574553728,599388560⟩ E) ⟨208574553856,597887671⟩ E))) ⟨208574553984,596391478⟩ (N (N (N (N E ⟨208574554112,594899963⟩ E) ⟨208708767104,740750265⟩ (N E ⟨208708767232,738855009⟩ E)) ⟨208708767360,736965811⟩ (N (N E ⟨208708767488,735082650⟩ E) ⟨208708767616,733205501⟩ E)) ⟨208708767744,731334342⟩ (N (N (N E ⟨208708767872,729469150⟩ E) ⟨208708768000,727609902⟩ (N E ⟨208708768128,725756576⟩ E)) ⟨208708768256,723909148⟩ (N (N E ⟨208708768384,722067596⟩ E) ⟨208708768512,720231898⟩ E)))) ⟨208708768640,718402031⟩ (N (N (N (N (N E ⟨208708768768,716577974⟩ E) ⟨208708768896,714759704⟩ (N E ⟨208708769024,712947198⟩ E)) ⟨208708769152,711140436⟩ (N (N E ⟨208708769280,709339395⟩ E) ⟨208708769408,707544054⟩ (N E ⟨208708769536,705754391⟩ E))) ⟨208708769664,703970384⟩ (N (N (N E ⟨208708769792,702192012⟩ E) ⟨208708769920,700419253⟩ (N E ⟨208708770048,698652087⟩ E)) ⟨208708770176,696890493⟩ (N (N E ⟨208708770304,695134448⟩ E) ⟨208708770432,693383932⟩ E))) ⟨208708770560,691638925⟩ (N (N (N (N E ⟨208708770688,689899405⟩ E) ⟨208708770816,688165352⟩ (N E ⟨208708771200,682995787⟩ E)) ⟨208708771328,681283396⟩ (N (N E ⟨208708771456,679576369⟩ E) ⟨208708771584,677874687⟩ E)) ⟨208708771712,676178329⟩ (N (N (N E ⟨208708771840,674487275⟩ E) ⟨208842984960,831393144⟩ (N E ⟨208842985088,829267333⟩ E)) ⟨208842985216,827148315⟩ (N (N E ⟨208842985344,825036062⟩ E) ⟨208842985472,822930549⟩ E)))))))

noncomputable def tab20 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨208842985728,818739641⟩ E) ⟨208842985856,816654193⟩ (N E ⟨208842985984,814575384⟩ E)) ⟨208842986112,812503186⟩ (N (N E ⟨208842986240,810437576⟩ E) ⟨208842986368,808378527⟩ (N E ⟨208842986496,806326015⟩ E))) ⟨208842986624,804280014⟩ (N (N (N E ⟨208842986752,802240501⟩ E) ⟨208842986880,800207451⟩ (N E ⟨208842987008,798180838⟩ E)) ⟨208842987136,796160639⟩ (N (N E ⟨208842987264,794146828⟩ E) ⟨208842987392,792139383⟩ E))) ⟨208842987520,790138278⟩ (N (N (N (N E ⟨208842987648,788143490⟩ E) ⟨208842987776,786154995⟩ (N E ⟨208842988032,782196787⟩ E)) ⟨208842988160,780227027⟩ (N (N E ⟨208842988288,778263466⟩ E) ⟨208842988416,776306079⟩ (N E ⟨208842988544,774354844⟩ E))) ⟨208842988672,772409737⟩ (N (N (N E ⟨208842988800,770470735⟩ E) ⟨208842989056,766610955⟩ (N E ⟨208842989184,764690132⟩ E)) ⟨208842989312,762775322⟩ (N (N E ⟨208842989440,760866503⟩ E) ⟨208842989568,758963653⟩ E)))) ⟨208977202944,924506993⟩ (N (N (N (N (N E ⟨208977203072,922146120⟩ E) ⟨208977203200,919792780⟩ (N E ⟨208977203328,917446945⟩ E)) ⟨208977203456,915108585⟩ (N (N E ⟨208977203584,912777672⟩ E) ⟨208977203712,910454178⟩ (N E ⟨208977203840,908138075⟩ E))) ⟨208977203968,905829333⟩ (N (N (N E ⟨208977204096,903527926⟩ E) ⟨208977204224,901233825⟩ (N E ⟨208977204352,898947003⟩ E)) ⟨208977204480,896667431⟩ (N (N E ⟨208977204608,894395082⟩ E) ⟨208977204736,892129929⟩ E))) ⟨208977204864,889871944⟩ (N (N (N (N E ⟨208977204992,887621100⟩ E) ⟨208977205120,885377370⟩ (N E ⟨208977205248,883140727⟩ E)) ⟨208977205376,880911144⟩ (N (N E ⟨208977205504,878688595⟩ E) ⟨208977205632,876473053⟩ E)) ⟨208977205760,874264491⟩ (N (N (N E ⟨208977205888,872062882⟩ E) ⟨208977206016,869868202⟩ (N E ⟨208977206144,867680423⟩ E)) ⟨208977206272,865499519⟩ (N (N E ⟨208977206400,863325466⟩ E) ⟨208977206528,861158236⟩ E))))) ⟨208977206656,858997803⟩ (N (N (N (N (N (N E ⟨208977206784,856844144⟩ E) ⟨208977206912,854697231⟩ (N E ⟨208977207040,852557041⟩ E)) ⟨208977207168,850423546⟩ (N (N E ⟨208977207296,848296723⟩ E) ⟨209111420672,1027120088⟩ (N E ⟨209111420928,1021882633⟩ E))) ⟨209111421056,1019276428⟩ (N (N (N E ⟨209111421184,1016678529⟩ E) ⟨209111421312,1014088903⟩ (N E ⟨209111421440,1011507519⟩ E)) ⟨209111421568,1008934346⟩ (N (N E ⟨209111421696,1006369352⟩ E) ⟨209111421824,1003812507⟩ E))) ⟨209111421952,1001263779⟩ (N (N (N (N E ⟨209111422080,998723136⟩ E) ⟨209111422208,996190550⟩ (N E ⟨209111422336,993665988⟩ E)) ⟨209111422464,991149420⟩ (N (N E ⟨209111422592,988640816⟩ E) ⟨209111422720,986140146⟩ E)) ⟨209111422848,983647380⟩ (N (N (N E ⟨209111422976,981162487⟩ E) ⟨209111423104,978685438⟩ (N E ⟨209111423232,976216203⟩ E)) ⟨209111423360,973754753⟩ (N (N E ⟨209111423488,971301057⟩ E) ⟨209111423616,968855088⟩ E)))) ⟨209111423744,966416815⟩ (N (N (N (N (N E ⟨209111423872,963986209⟩ E) ⟨209111424000,961563243⟩ (N E ⟨209111424256,956740110⟩ E)) ⟨209111424384,954339887⟩ (N (N E ⟨209111424512,951947188⟩ E) ⟨209111424640,949561984⟩ (N E ⟨209111424768,947184249⟩ E))) ⟨209111424896,944813953⟩ (N (N (N E ⟨209111425024,942451069⟩ E) ⟨209245639040,1120546515⟩ (N E ⟨209245639168,1117694142⟩ E)) ⟨209245639424,1112016578⟩ (N (N E ⟨209245639552,1109191318⟩ E) ⟨209245639680,1106375028⟩ E))) ⟨209245639808,1103567673⟩ (N (N (N (N E ⟨209245639936,1100769219⟩ E) ⟨209245640064,1097979632⟩ (N E ⟨209245640192,1095198878⟩ E)) ⟨209245640320,1092426925⟩ (N (N E ⟨209245640448,1089663738⟩ E) ⟨209245640576,1086909285⟩ E)) ⟨209245640832,1081426445⟩ (N (N (N E ⟨209245640960,1078697993⟩ E) ⟨209245641088,1075978143⟩ (N E ⟨209245641216,1073266863⟩ E)) ⟨209245641344,1070564119⟩ (N (N E ⟨209245641472,1067869879⟩ E) ⟨209245641600,1065184112⟩ E)))))) ⟨209245641728,1062506786⟩ (N (N (N (N (N (N (N E ⟨209245642112,1054525132⟩ E) ⟨209245642368,1049245653⟩ (N E ⟨209245642496,1046618306⟩ E)) ⟨209245642624,1043999180⟩ (N (N E ⟨209245642752,1041388244⟩ E) ⟨209379857152,1222726734⟩ (N E ⟨209379857280,1219620198⟩ E))) ⟨209379857408,1216523523⟩ (N (N (N E ⟨209379857536,1213436673⟩ E) ⟨209379857664,1210359611⟩ (N E ⟨209379857792,1207292298⟩ E)) ⟨209379857920,1204234698⟩ (N (N E ⟨209379858048,1201186775⟩ E) ⟨209379858176,1198148491⟩ E))) ⟨209379858304,1195119809⟩ (N (N (N (N E ⟨209379858432,1192100694⟩ E) ⟨209379858560,1189091109⟩ (N E ⟨209379858688,1186091018⟩ E)) ⟨209379858816,1183100385⟩ (N (N E ⟨209379858944,1180119175⟩ E) ⟨209379859072,1177147351⟩ (N E ⟨209379859200,1174184879⟩ E))) ⟨209379859328,1171231722⟩ (N (N (N E ⟨209379859456,1168287846⟩ E) ⟨209379859712,1162427798⟩ (N E ⟨209379859840,1159511555⟩ E)) ⟨209379859968,1156604455⟩ (N (N E ⟨209379860096,1153706461⟩ E) ⟨209379860224,1150817541⟩ E)))) ⟨209379860480,1145066785⟩ (N (N (N (N (N E ⟨209514075264,1328283024⟩ E) ⟨209514075392,1324914731⟩ (N E ⟨209514075520,1321557111⟩ E)) ⟨209514075648,1318210123⟩ (N (N E ⟨209514075776,1314873727⟩ E) ⟨209514075904,1311547883⟩ (N E ⟨209514076032,1308232551⟩ E))) ⟨209514076160,1304927690⟩ (N (N (N E ⟨209514076288,1301633261⟩ E) ⟨209514076416,1298349225⟩ (N E ⟨209514076544,1295075542⟩ E)) ⟨209514076672,1291812173⟩ (N (N E ⟨209514076800,1288559080⟩ E) ⟨209514077056,1282083563⟩ E))) ⟨209514077184,1278861063⟩ (N (N (N (N E ⟨209514077312,1275648683⟩ E) ⟨209514077440,1272446387⟩ (N E ⟨209514077568,1269254135⟩ E)) ⟨209514077696,1266071890⟩ (N (N E ⟨209514077952,1259737271⟩ E) ⟨209514078080,1256584822⟩ E)) ⟨209514078208,1253442231⟩ (N (N (N E ⟨209648293120,1444384438⟩ E) ⟨209648293248,1440724056⟩ (N E ⟨209648293376,1437075265⟩ E)) ⟨209648293504,1433438020⟩ (N (N E ⟨209648293632,1429812279⟩ E) ⟨209648293888,1422595132⟩ E))))) ⟨209648294016,1419003640⟩ (N (N (N (N (N (N E ⟨209648294144,1415423477⟩ E) ⟨209648294400,1408296969⟩ (N E ⟨209648294656,1401215267⟩ E)) ⟨209648294784,1397691114⟩ (N (N E ⟨209648294912,1394178035⟩ E) ⟨209648295040,1390675990⟩ (N E ⟨209648295296,1383704835⟩ E))) ⟨209648295680,1373329821⟩ (N (N (N E ⟨209648295936,1366467147⟩ E) ⟨209782511360,1552888950⟩ (N E ⟨209782511616,1545050559⟩ E)) ⟨209782511872,1537261575⟩ (N (N E ⟨209782512000,1533385494⟩ E) ⟨209782512128,1529521625⟩ E))) ⟨209782512256,1525669922⟩ (N (N (N (N E ⟨209782512384,1521830339⟩ E) ⟨209782512512,1518002830⟩ (N E ⟨209782512640,1514187350⟩ E)) ⟨209782512768,1510383853⟩ (N (N E ⟨209782512896,1506592294⟩ E) ⟨209782513024,1502812628⟩ E)) ⟨209782513152,1499044811⟩ (N (N (N E ⟨209782513280,1495288797⟩ E) ⟨209782513408,1491544544⟩ (N E ⟨209782513664,1484091138⟩ E)) ⟨209916729088,1680722099⟩ (N (N E ⟨209916729216,1676473567⟩ E) ⟨209916729728,1659613126⟩ E)))) ⟨209916729856,1655431185⟩ (N (N (N (N (N E ⟨209916730240,1642964168⟩ E) ⟨209916730880,1622445533⟩ (N E ⟨209916731008,1618380326⟩ E)) ⟨209916731136,1614327847⟩ (N (N E ⟨209916731392,1606260880⟩ E) ⟨210050947200,1799545632⟩ (N E ⟨210050947584,1785967694⟩ E))) ⟨210050947840,1776986855⟩ (N (N (N E ⟨210050947968,1772517609⟩ E) ⟨210050948224,1763621202⟩ (N E ⟨210050948352,1759193934⟩ E)) ⟨210050948736,1745995246⟩ (N (N E ⟨210050948864,1741623214⟩ E) ⟨210050949120,1732920140⟩ E))) ⟨210185165568,1911410019⟩ (N (N (N (N E ⟨210185165824,1901810469⟩ E) ⟨210185165952,1897033299⟩ (N E ⟨210185166464,1878073998⟩ E)) ⟨210185166592,1873371237⟩ (N (N E ⟨210185166848,1864009804⟩ E) ⟨210319384320,2009509640⟩ E)) ⟨210319384448,2004480911⟩ (N (N (N E ⟨210319384576,1999467908⟩ E) ⟨210453602304,2139229668⟩ (N E ⟨210587820032,2283227512⟩ E)) ⟨210722037760,2431391112⟩ (N (N E ⟨210856255488,2583647426⟩ E) ⟨210990473216,2739920731⟩ E)))))))

noncomputable def tab21 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨211258908672,3064202262⟩ E) ⟨211393126400,3232046011⟩ (N E ⟨211527344128,3403577882⟩ E)) ⟨211661561856,3578709384⟩ (N (N E ⟨211795779584,3757349609⟩ E) ⟨211929997312,3939405282⟩ (N E ⟨212064215040,4124780812⟩ E))) ⟨212198432768,4313378347⟩ (N (N (N E ⟨212466868224,4699837030⟩ E) ⟨212601085952,4897491654⟩ (N E ⟨212735303680,5097955349⟩ E)) ⟨213003739136,5506874740⟩ (N (N E ⟨213272174592,5925706003⟩ E) ⟨213809045504,6789406381⟩ E))) ⟨213943263232,7010060751⟩ (N (N (N (N E ⟨214480134144,7907901185⟩ E) ⟨214614351872,8135535550⟩ (N E ⟨214748569728,8343278283⟩ E)) ⟨214748569856,8322438682⟩ (N (N E ⟨214748569984,8301664123⟩ E) ⟨214748570112,8280954363⟩ (N E ⟨214748570240,8260309158⟩ E))) ⟨214748570368,8239728268⟩ (N (N (N E ⟨214748570496,8219211452⟩ E) ⟨214748570624,8198758471⟩ (N E ⟨214748570752,8178369086⟩ E)) ⟨214748570880,8158043061⟩ (N (N E ⟨214748571008,8137780160⟩ E) ⟨214748571136,8117580146⟩ E)))) ⟨214748571264,8097442786⟩ (N (N (N (N (N E ⟨214748571392,8077367847⟩ E) ⟨214748571520,8057355097⟩ (N E ⟨214748571648,8037404305⟩ E)) ⟨214748571776,8017515240⟩ (N (N E ⟨214748571904,7997687674⟩ E) ⟨214748572032,7977921378⟩ (N E ⟨214748572160,7958216125⟩ E))) ⟨214748572288,7938571689⟩ (N (N (N E ⟨214748572416,7918987845⟩ E) ⟨214748572544,7899464369⟩ (N E ⟨214748572672,7880001038⟩ E)) ⟨214748572800,7860597628⟩ (N (N E ⟨214748572928,7841253920⟩ E) ⟨214748573056,7821969692⟩ E))) ⟨214748573184,7802744726⟩ (N (N (N (N E ⟨214748573312,7783578802⟩ E) ⟨214748573440,7764471704⟩ (N E ⟨214748573568,7745423214⟩ E)) ⟨214748573696,7726433117⟩ (N (N E ⟨214748573824,7707501199⟩ E) ⟨214748573952,7688627245⟩ E)) ⟨214748574080,7669811042⟩ (N (N (N E ⟨214748574208,7651052380⟩ E) ⟨214748574336,7632351046⟩ (N E ⟨214748574464,7613706830⟩ E)) ⟨214748574592,7595119523⟩ (N (N E ⟨214748574720,7576588917⟩ E) ⟨214748574848,7558114805⟩ E))))) ⟨214748574976,7539696979⟩ (N (N (N (N (N (N E ⟨214748575104,7521335234⟩ E) ⟨214748575232,7503029365⟩ (N E ⟨214748575360,7484779168⟩ E)) ⟨214748575488,7466584440⟩ (N (N E ⟨214748575616,7448444979⟩ E) ⟨214748575744,7430360584⟩ (N E ⟨214748575872,7412331053⟩ E))) ⟨214748576000,7394356188⟩ (N (N (N E ⟨214748576128,7376435789⟩ E) ⟨214748576256,7358569658⟩ (N E ⟨214748576384,7340757599⟩ E)) ⟨214748576512,7322999415⟩ (N (N E ⟨214748576640,7305294910⟩ E) ⟨214748576768,7287643890⟩ E))) ⟨214748576896,7270046162⟩ (N (N (N (N E ⟨214748577024,7252501531⟩ E) ⟨214748577152,7235009806⟩ (N E ⟨214748577280,7217570796⟩ E)) ⟨214748577408,7200184310⟩ (N (N E ⟨214748577536,7182850157⟩ E) ⟨214748577664,7165568150⟩ E)) ⟨214748577792,7148338100⟩ (N (N (N E ⟨215017013248,7541312377⟩ E) ⟨217835585536,11620730836⟩ (N E ⟨219580416000,13803461985⟩ E)) ⟨223338512512,16418769270⟩ (N (N E ⟨223338512640,16371937440⟩ E) ⟨223338512768,16320343345⟩ E)))) ⟨223338512896,16264029169⟩ (N (N (N (N (N E ⟨223338513024,16203039755⟩ E) ⟨223338513152,16137422570⟩ (N E ⟨223338513280,16067227664⟩ E)) ⟨223338513408,15992507623⟩ (N (N E ⟨223338513536,15913317533⟩ E) ⟨223338513664,15829714926⟩ (N E ⟨223338513792,15741759742⟩ E))) ⟨223338513920,15649514276⟩ (N (N (N E ⟨223338514048,15553043132⟩ E) ⟨223338514176,15452413173⟩ (N E ⟨223338514304,15347693469⟩ E)) ⟨223338514432,15238955248⟩ (N (N E ⟨223338514560,15126271841⟩ E) ⟨223338514688,15009718625⟩ E))) ⟨223338514816,14889372976⟩ (N (N (N (N E ⟨223338514944,14765314206⟩ E) ⟨223338515072,14637623509⟩ (N E ⟨223338515200,14506383906⟩ E)) ⟨223338515328,14371680180⟩ (N (N E ⟨223338515456,14233598825⟩ E) ⟨223338515584,14092227980⟩ E)) ⟨223338515712,13947657371⟩ (N (N (N E ⟨223338515840,13799978251⟩ E) ⟨223338515968,13649283334⟩ (N E ⟨223338516096,13495666739⟩ E)) ⟨223338516224,13339223920⟩ (N (N E ⟨223338516352,13180051607⟩ E) ⟨223338516480,13018247744⟩ E)))))) ⟨223338516608,12853911416⟩ (N (N (N (N (N (N (N E ⟨223338516736,12687142798⟩ E) ⟨223338516864,12518043076⟩ (N E ⟨223338516992,12346714390⟩ E)) ⟨223338517120,12173259767⟩ (N (N E ⟨223338517248,11997783053⟩ E) ⟨223338517376,11820388852⟩ (N E ⟨223338517504,11641182452⟩ E))) ⟨223338517632,11460269768⟩ (N (N (N E ⟨223338517760,11277757267⟩ E) ⟨223338517888,11093751909⟩ (N E ⟨223338518016,10908361077⟩ E)) ⟨223338518144,10721692510⟩ (N (N E ⟨223338518272,10533854239⟩ E) ⟨223338518528,10155101777⟩ E))) ⟨223338518656,9964404513⟩ (N (N (N (N E ⟨223338518784,9772971268⟩ E) ⟨223338518912,9580910548⟩ (N E ⟨223338519040,9388330754⟩ E)) ⟨223338519168,9195340124⟩ (N (N E ⟨223338519424,8808558093⟩ E) ⟨223338519552,8614981766⟩ (N E ⟨223338519680,8421424628⟩ E))) ⟨223338519808,8227993137⟩ (N (N (N E ⟨223338519936,8034793215⟩ E) ⟨223338520064,7841930177⟩ (N E ⟨223338520320,7457632652⟩ E)) ⟨223338520448,7266405248⟩ (N (N E ⟨223338520576,7075928778⟩ E) ⟨224143825536,9312323963⟩ E)))) ⟨224143826944,7170838102⟩ (N (N (N (N (N E ⟨224949133312,7266140465⟩ E) ⟨225620221952,7345683265⟩ (N E ⟨225888657408,7377497287⟩ E)) ⟨226157092864,7409295711⟩ (N (N E ⟨227767705600,7599239762⟩ E) ⟨227901923328,7614965248⟩ (N E ⟨228170358784,7646351236⟩ E))) ⟨228975665152,7739906568⟩ (N (N (N E ⟨229512536064,7801683290⟩ E) ⟨229646753792,7817042914⟩ (N E ⟨230049406976,7862900965⟩ E)) ⟨230452060160,7908404574⟩ (N (N E ⟨230720495616,7938528817⟩ E) ⟨231123148800,7983376368⟩ E))) ⟨231525801984,8027791871⟩ (N (N (N (N E ⟨231660019712,8042496146⟩ E) ⟨231928455296,7860878833⟩ (N E ⟨231928455424,7651001355⟩ E)) ⟨231928455552,7442223137⟩ (N (N E ⟨231928455680,7234651425⟩ E) ⟨231928456064,6620229385⟩ E)) ⟨231928456192,6418531221⟩ (N (N (N E ⟨231928456576,5824173145⟩ E) ⟨231928456704,5629958027⟩ (N E ⟨231928456832,5437853764⟩ E)) ⟨231928457088,5060347058⟩ (N (N E ⟨231928457216,4875124875⟩ E) ⟨231928457344,4692373975⟩ E))))) ⟨231928457600,4334626354⟩ (N (N (N (N (N (N E ⟨231928458240,3489255446⟩ E) ⟨231928458368,3329189908⟩ (N E ⟨231928458624,3018634276⟩ E)) ⟨231928458752,2868276071⟩ (N (N E ⟨231928458880,2721281800⟩ E) ⟨231928459008,2577711767⟩ (N E ⟨231928459136,2437623972⟩ E))) ⟨231928459520,2038798994⟩ (N (N (N E ⟨231928459776,1791284529⟩ E) ⟨231928460160,1448464874⟩ (N E ⟨231928460416,1239339599⟩ E)) ⟨231928460672,1046061931⟩ (N (N E ⟨231928460928,868853408⟩ E) ⟨231928461056,786333379⟩ E))) ⟨231928461184,707895599⟩ (N (N (N (N E ⟨231928461312,633556508⟩ E) ⟨231928462080,274200677⟩ (N E ⟨231928462336,187546703⟩ E)) ⟨231928462592,117429720⟩ (N (N E ⟨231928462976,43085526⟩ E) ⟨231928463104,26466625⟩ E)) ⟨231928463360,5355706⟩ (N (N (N E ⟨232465330560,1931602149⟩ E) ⟨232465332992,279021421⟩ (N E ⟨232867986688,122373632⟩ E)) ⟨233002203136,650034288⟩ (N (N E ⟨233270640128,68653077⟩ E) ⟨233270640256,46994889⟩ E)))) ⟨233404855424,1275293080⟩ (N (N (N (N (N E ⟨233539075200,160041560⟩ E) ⟨233807510784,127000076⟩ (N E ⟨234210163456,293534561⟩ E)) ⟨234210164352,49508916⟩ (N (N E ⟨234344382336,17589271⟩ E) ⟨234478600192,7763692⟩ (N E ⟨234612817920,7880369⟩ E))) ⟨234747034240,349794248⟩ (N (N (N E ⟨234747035264,50845870⟩ E) ⟨235015470720,51484412⟩ (N E ⟨235149687936,168464075⟩ E)) ⟨235552341376,103048563⟩ (N (N E ⟨235686559360,52987042⟩ E) ⟨235820777216,34278418⟩ E))) ⟨235820777472,8853908⟩ (N (N (N (N E ⟨235954994688,76825495⟩ E) ⟨236223430400,34903735⟩ (N E ⟨236357648128,35102651⟩ E)) ⟨236626083840,9411094⟩ (N (N E ⟨236760301312,35669806⟩ E) ⟨236760301568,9495723⟩ E)) ⟨236894519296,9577858⟩ (N (N (N E ⟨237162954752,9734450⟩ E) ⟨237297172480,9808813⟩ (N E ⟨237431390208,9880494⟩ E)) ⟨237968261120,10139553⟩ (N (N E ⟨238505132032,10352542⟩ E) ⟨240518398080,3268915⟩ E)))))))

noncomputable def tab22 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨240921052672,1223601⟩ E) ⟨240921052928,1218185⟩ (N E ⟨240921053056,1215488⟩ E)) ⟨240921053184,1212798⟩ (N (N E ⟨240921053312,1210116⟩ E) ⟨240921053440,1207441⟩ (N E ⟨240921053568,1204774⟩ E))) ⟨240921053696,1202114⟩ (N (N (N E ⟨240921053824,1199461⟩ E) ⟨240921053952,1196816⟩ (N E ⟨240921054080,1194177⟩ E)) ⟨240921054208,1191547⟩ (N (N E ⟨240921054336,1188923⟩ E) ⟨240921054464,1186307⟩ E))) ⟨240921054592,1183697⟩ (N (N (N (N E ⟨240921054720,1181096⟩ E) ⟨240921054848,1178501⟩ (N E ⟨240921054976,1175913⟩ E)) ⟨240921055104,1173332⟩ (N (N E ⟨240921055232,1170759⟩ E) ⟨240921055360,1168192⟩ (N E ⟨240921055488,1165633⟩ E))) ⟨240921055616,1163080⟩ (N (N (N E ⟨240921055744,1160535⟩ E) ⟨240921055872,1157996⟩ (N E ⟨240921056000,1155465⟩ E)) ⟨240921056128,1152940⟩ (N (N E ⟨240921056256,1150422⟩ E) ⟨240921056512,1145407⟩ E)))) ⟨240921056640,1142910⟩ (N (N (N (N (N E ⟨240921056896,1137936⟩ E) ⟨240921057024,1135459⟩ (N E ⟨240921057152,1132989⟩ E)) ⟨240921057280,1130526⟩ (N (N E ⟨240921057408,1128069⟩ E) ⟨240921057536,1125619⟩ (N E ⟨240921057792,1120739⟩ E))) ⟨240921057920,1118308⟩ (N (N (N E ⟨240921058048,1115885⟩ E) ⟨240921058176,1113468⟩ (N E ⟨240921058304,1111057⟩ E)) ⟨240921058432,1108653⟩ (N (N E ⟨240921058560,1106256⟩ E) ⟨240921058688,1103865⟩ E))) ⟨240921059072,1096731⟩ (N (N (N (N E ⟨240921059200,1094365⟩ E) ⟨240921059328,1092006⟩ (N E ⟨241055270528,6511137⟩ E)) ⟨241055270656,6496714⟩ (N (N E ⟨241055270784,6482330⟩ E) ⟨241055270912,6467986⟩ E)) ⟨241055271040,6453681⟩ (N (N (N E ⟨241055271168,6439416⟩ E) ⟨241055271296,6425191⟩ (N E ⟨241055271424,6411004⟩ E)) ⟨241055271552,6396857⟩ (N (N E ⟨241055271680,6382749⟩ E) ⟨241055271808,6368680⟩ E))))) ⟨241055271936,6354650⟩ (N (N (N (N (N (N E ⟨241055272064,6340658⟩ E) ⟨241055272192,6326704⟩ (N E ⟨241055272320,6312789⟩ E)) ⟨241055272448,6298913⟩ (N (N E ⟨241055272576,6285074⟩ E) ⟨241055272704,6271273⟩ (N E ⟨241055272832,6257511⟩ E))) ⟨241055272960,6243786⟩ (N (N (N E ⟨241055273088,6230098⟩ E) ⟨241055273216,6216448⟩ (N E ⟨241055273344,6202836⟩ E)) ⟨241055273472,6189260⟩ (N (N E ⟨241055273600,6175722⟩ E) ⟨241055273728,6162221⟩ E))) ⟨241055273856,6148757⟩ (N (N (N (N E ⟨241055273984,6135329⟩ E) ⟨241055274112,6121938⟩ (N E ⟨241055274240,6108584⟩ E)) ⟨241055274368,6095266⟩ (N (N E ⟨241055274496,6081984⟩ E) ⟨241055274624,6068739⟩ E)) ⟨241055274752,6055529⟩ (N (N (N E ⟨241055274880,6042356⟩ E) ⟨241055275008,6029218⟩ (N E ⟨241055275136,6016116⟩ E)) ⟨241055275264,6003050⟩ (N (N E ⟨241055275392,5990019⟩ E) ⟨241055275520,5977023⟩ E)))) ⟨241055275648,5964063⟩ (N (N (N (N (N E ⟨241055275776,5951137⟩ E) ⟨241055275904,5938247⟩ (N E ⟨241055276032,5925392⟩ E)) ⟨241055276288,5899785⟩ (N (N E ⟨241055276416,5887034⟩ E) ⟨241055276544,5874317⟩ (N E ⟨241055276672,5861634⟩ E))) ⟨241055277056,5823791⟩ (N (N (N E ⟨241189488384,15961915⟩ E) ⟨241189488512,15926575⟩ (N E ⟨241189488640,15891332⟩ E)) ⟨241189488768,15856187⟩ (N (N E ⟨241189488896,15821140⟩ E) ⟨241189489024,15786189⟩ E))) ⟨241189489152,15751334⟩ (N (N (N (N E ⟨241189489280,15716576⟩ E) ⟨241189489408,15681913⟩ (N E ⟨241189489536,15647347⟩ E)) ⟨241189489664,15612875⟩ (N (N E ⟨241189489792,15578498⟩ E) ⟨241189489920,15544216⟩ E)) ⟨241189490048,15510028⟩ (N (N (N E ⟨241189490176,15475934⟩ E) ⟨241189490304,15441933⟩ (N E ⟨241189490432,15408026⟩ E)) ⟨241189490560,15374212⟩ (N (N E ⟨241189490688,15340491⟩ E) ⟨241189490816,15306862⟩ E)))))) ⟨241189490944,15273325⟩ (N (N (N (N (N (N (N E ⟨241189491072,15239880⟩ E) ⟨241189491200,15206527⟩ (N E ⟨241189491328,15173265⟩ E)) ⟨241189491456,15140093⟩ (N (N E ⟨241189491584,15107013⟩ E) ⟨241189491712,15074022⟩ (N E ⟨241189491840,15041122⟩ E))) ⟨241189491968,15008311⟩ (N (N (N E ⟨241189492096,14975590⟩ E) ⟨241189492224,14942958⟩ (N E ⟨241189492352,14910415⟩ E)) ⟨241189492480,14877960⟩ (N (N E ⟨241189492608,14845594⟩ E) ⟨241189492736,14813316⟩ E))) ⟨241189492864,14781125⟩ (N (N (N (N E ⟨241189492992,14749022⟩ E) ⟨241189493120,14717005⟩ (N E ⟨241189493248,14685076⟩ E)) ⟨241189493376,14653233⟩ (N (N E ⟨241189493504,14621477⟩ E) ⟨241189493632,14589807⟩ (N E ⟨241189493760,14558222⟩ E))) ⟨241189494016,14495308⟩ (N (N (N E ⟨241189494144,14463979⟩ E) ⟨241189494656,14339506⟩ (N E ⟨241189494784,14308597⟩ E)) ⟨241323706240,29556413⟩ (N (N E ⟨241323706496,29425789⟩ E) ⟨241323706624,29360747⟩ E)))) ⟨241323706752,29295886⟩ (N (N (N (N (N E ⟨241323706880,29231203⟩ E) ⟨241323707008,29166699⟩ (N E ⟨241323707136,29102372⟩ E)) ⟨241323707264,29038223⟩ (N (N E ⟨241323707392,28974251⟩ E) ⟨241323707520,28910455⟩ (N E ⟨241323707648,28846834⟩ E))) ⟨241323707776,28783388⟩ (N (N (N E ⟨241323707904,28720116⟩ E) ⟨241323708032,28657019⟩ (N E ⟨241323708160,28594094⟩ E)) ⟨241323708288,28531343⟩ (N (N E ⟨241323708416,28468763⟩ E) ⟨241323708544,28406355⟩ E))) ⟨241323708672,28344117⟩ (N (N (N (N E ⟨241323708800,28282051⟩ E) ⟨241323708928,28220154⟩ (N E ⟨241323709056,28158426⟩ E)) ⟨241323709184,28096867⟩ (N (N E ⟨241323709312,28035476⟩ E) ⟨241323709440,27974253⟩ E)) ⟨241323709568,27913196⟩ (N (N (N E ⟨241323709696,27852307⟩ E) ⟨241323709824,27791583⟩ (N E ⟨241323709952,27731025⟩ E)) ⟨241323710080,27670631⟩ (N (N E ⟨241323710208,27610402⟩ E) ⟨241323710336,27550337⟩ E))))) ⟨241323710464,27490435⟩ (N (N (N (N (N (N E ⟨241323710592,27430696⟩ E) ⟨241323710720,27371119⟩ (N E ⟨241323710848,27311704⟩ E)) ⟨241323711104,27193356⟩ (N (N E ⟨241323711232,27134423⟩ E) ⟨241323711488,27017034⟩ (N E ⟨241323711616,26958578⟩ E))) ⟨241323711744,26900280⟩ (N (N (N E ⟨241323711872,26842139⟩ E) ⟨241323712000,26784156⟩ (N E ⟨241323712256,26668658⟩ E)) ⟨241323712384,26611142⟩ (N (N E ⟨241323712512,26553782⟩ E) ⟨241457924096,47272669⟩ E))) ⟨241457924224,47168122⟩ (N (N (N (N E ⟨241457924352,47063864⟩ E) ⟨241457924480,46959894⟩ (N E ⟨241457924608,46856210⟩ E)) ⟨241457924736,46752813⟩ (N (N E ⟨241457924864,46649701⟩ E) ⟨241457924992,46546873⟩ E)) ⟨241457925120,46444328⟩ (N (N (N E ⟨241457925248,46342066⟩ E) ⟨241457925376,46240085⟩ (N E ⟨241457925504,46138384⟩ E)) ⟨241457925632,46036963⟩ (N (N E ⟨241457925760,45935821⟩ E) ⟨241457925888,45834956⟩ E)))) ⟨241457926016,45734368⟩ (N (N (N (N (N E ⟨241457926144,45634056⟩ E) ⟨241457926272,45534018⟩ (N E ⟨241457926400,45434255⟩ E)) ⟨241457926528,45334765⟩ (N (N E ⟨241457926656,45235547⟩ E) ⟨241457926784,45136600⟩ (N E ⟨241457926912,45037924⟩ E))) ⟨241457927040,44939517⟩ (N (N (N E ⟨241457927168,44841379⟩ E) ⟨241457927296,44743509⟩ (N E ⟨241457927424,44645906⟩ E)) ⟨241457927552,44548569⟩ (N (N E ⟨241457927680,44451497⟩ E) ⟨241457927808,44354689⟩ E))) ⟨241457927936,44258145⟩ (N (N (N (N E ⟨241457928064,44161863⟩ E) ⟨241457928192,44065843⟩ (N E ⟨241457928320,43970084⟩ E)) ⟨241457928448,43874585⟩ (N (N E ⟨241457928576,43779346⟩ E) ⟨241457928704,43684364⟩ E)) ⟨241457928832,43589640⟩ (N (N (N E ⟨241457928960,43495173⟩ E) ⟨241457929088,43400961⟩ (N E ⟨241457929216,43307005⟩ E)) ⟨241457929472,43119853⟩ (N (N E ⟨241457929600,43026657⟩ E) ⟨241457929984,42748574⟩ E)))))))

noncomputable def tab23 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨241457930240,42564433⟩ E) ⟨241592142208,68781311⟩ (N E ⟨241592142336,68629448⟩ E)) ⟨241592142464,68478004⟩ (N (N E ⟨241592142592,68326977⟩ E) ⟨241592142720,68176367⟩ (N E ⟨241592142848,68026172⟩ E))) ⟨241592142976,67876390⟩ (N (N (N E ⟨241592143104,67727020⟩ E) ⟨241592143232,67578061⟩ (N E ⟨241592143360,67429512⟩ E)) ⟨241592143488,67281370⟩ (N (N E ⟨241592143616,67133635⟩ E) ⟨241592143744,66986305⟩ E))) ⟨241592143872,66839380⟩ (N (N (N (N E ⟨241592144000,66692857⟩ E) ⟨241592144128,66546735⟩ (N E ⟨241592144256,66401014⟩ E)) ⟨241592144384,66255691⟩ (N (N E ⟨241592144512,66110766⟩ E) ⟨241592144640,65966237⟩ (N E ⟨241592144768,65822102⟩ E))) ⟨241592144896,65678361⟩ (N (N (N E ⟨241592145024,65535013⟩ E) ⟨241592145152,65392055⟩ (N E ⟨241592145280,65249487⟩ E)) ⟨241592145408,65107307⟩ (N (N E ⟨241592145536,64965515⟩ E) ⟨241592145664,64824108⟩ E)))) ⟨241592145920,64542448⟩ (N (N (N (N (N E ⟨241592146176,64262315⟩ E) ⟨241592146304,64122819⟩ (N E ⟨241592146432,63983702⟩ E)) ⟨241592146560,63844961⟩ (N (N E ⟨241592146944,63430990⟩ E) ⟨241592147072,63293746⟩ (N E ⟨241592147200,63156873⟩ E))) ⟨241592147328,63020369⟩ (N (N (N E ⟨241592147456,62884235⟩ E) ⟨241592147584,62748468⟩ (N E ⟨241592147712,62613067⟩ E)) ⟨241592147968,62343359⟩ (N (N E ⟨241726359936,94760714⟩ E) ⟨241726360064,94551491⟩ E))) ⟨241726360192,94342845⟩ (N (N (N (N E ⟨241726360320,94134774⟩ E) ⟨241726360448,93927277⟩ (N E ⟨241726360576,93720351⟩ E)) ⟨241726360704,93513995⟩ (N (N E ⟨241726360832,93308207⟩ E) ⟨241726360960,93102985⟩ E)) ⟨241726361088,92898326⟩ (N (N (N E ⟨241726361216,92694230⟩ E) ⟨241726361344,92490694⟩ (N E ⟨241726361472,92287717⟩ E)) ⟨241726361600,92085296⟩ (N (N E ⟨241726361728,91883430⟩ E) ⟨241726361856,91682117⟩ E))))) ⟨241726361984,91481355⟩ (N (N (N (N (N (N E ⟨241726362112,91281142⟩ E) ⟨241726362240,91081477⟩ (N E ⟨241726362368,90882357⟩ E)) ⟨241726362496,90683782⟩ (N (N E ⟨241726362624,90485749⟩ E) ⟨241726362752,90288256⟩ (N E ⟨241726362880,90091302⟩ E))) ⟨241726363008,89894884⟩ (N (N (N E ⟨241726363136,89699002⟩ E) ⟨241726363264,89503653⟩ (N E ⟨241726363392,89308836⟩ E)) ⟨241726363520,89114548⟩ (N (N E ⟨241726363648,88920789⟩ E) ⟨241726363776,88727556⟩ E))) ⟨241726363904,88534848⟩ (N (N (N (N E ⟨241726364032,88342663⟩ E) ⟨241726364160,88150999⟩ (N E ⟨241726364288,87959854⟩ E)) ⟨241726364416,87769228⟩ (N (N E ⟨241726364544,87579118⟩ E) ⟨241726364672,87389522⟩ E)) ⟨241726364800,87200440⟩ (N (N (N E ⟨241726364928,87011868⟩ E) ⟨241726365056,86823806⟩ (N E ⟨241726365184,86636252⟩ E)) ⟨241726365312,86449204⟩ (N (N E ⟨241726365440,86262661⟩ E) ⟨241726365568,86076621⟩ E)))) ⟨241726365696,85891082⟩ (N (N (N (N (N E ⟨241860577920,124345394⟩ E) ⟨241860578048,124071153⟩ (N E ⟨241860578176,123797669⟩ E)) ⟨241860578304,123524937⟩ (N (N E ⟨241860578432,123252957⟩ E) ⟨241860578560,122981724⟩ (N E ⟨241860578688,122711238⟩ E))) ⟨241860578816,122441495⟩ (N (N (N E ⟨241860578944,122172493⟩ E) ⟨241860579072,121904229⟩ (N E ⟨241860579200,121636702⟩ E)) ⟨241860579328,121369908⟩ (N (N E ⟨241860579456,121103845⟩ E) ⟨241860579584,120838511⟩ E))) ⟨241860579712,120573903⟩ (N (N (N (N E ⟨241860579840,120310020⟩ E) ⟨241860579968,120046858⟩ (N E ⟨241860580096,119784416⟩ E)) ⟨241860580224,119522690⟩ (N (N E ⟨241860580352,119261679⟩ E) ⟨241860580480,119001380⟩ E)) ⟨241860580608,118741791⟩ (N (N (N E ⟨241860580736,118482910⟩ E) ⟨241860580864,118224734⟩ (N E ⟨241860580992,117967261⟩ E)) ⟨241860581120,117710488⟩ (N (N E ⟨241860581248,117454414⟩ E) ⟨241860581376,117199036⟩ E)))))) ⟨241860581504,116944352⟩ (N (N (N (N (N (N (N E ⟨241860581632,116690360⟩ E) ⟨241860581760,116437057⟩ (N E ⟨241860581888,116184441⟩ E)) ⟨241860582016,115932509⟩ (N (N E ⟨241860582144,115681261⟩ E) ⟨241860582272,115430692⟩ (N E ⟨241860582400,115180802⟩ E))) ⟨241860582528,114931588⟩ (N (N (N E ⟨241860582784,114435179⟩ E) ⟨241860582912,114187980⟩ (N E ⟨241860583040,113941448⟩ E)) ⟨241860583168,113695581⟩ (N (N E ⟨241860583296,113450377⟩ E) ⟨241860583424,113205834⟩ E))) ⟨241994795776,158131662⟩ (N (N (N (N E ⟨241994795904,157783099⟩ E) ⟨241994796032,157435496⟩ (N E ⟨241994796160,157088851⟩ E)) ⟨241994796288,156743159⟩ (N (N E ⟨241994796416,156398417⟩ E) ⟨241994796544,156054623⟩ (N E ⟨241994796672,155711773⟩ E))) ⟨241994796800,155369865⟩ (N (N (N E ⟨241994796928,155028895⟩ E) ⟨241994797056,154688859⟩ (N E ⟨241994797184,154349756⟩ E)) ⟨241994797312,154011581⟩ (N (N E ⟨241994797440,153674333⟩ E) ⟨241994797568,153338007⟩ E)))) ⟨241994797696,153002601⟩ (N (N (N (N (N E ⟨241994797824,152668112⟩ E) ⟨241994797952,152334536⟩ (N E ⟨241994798080,152001871⟩ E)) ⟨241994798208,151670114⟩ (N (N E ⟨241994798336,151339262⟩ E) ⟨241994798464,151009311⟩ (N E ⟨241994798592,150680260⟩ E))) ⟨241994798720,150352104⟩ (N (N (N E ⟨241994798848,150024842⟩ E) ⟨241994798976,149698469⟩ (N E ⟨241994799104,149372984⟩ E)) ⟨241994799232,149048383⟩ (N (N E ⟨241994799360,148724663⟩ E) ⟨241994799488,148401822⟩ E))) ⟨241994799616,148079857⟩ (N (N (N (N E ⟨241994799744,147758765⟩ E) ⟨241994799872,147438542⟩ (N E ⟨241994800000,147119187⟩ E)) ⟨241994800128,146800696⟩ (N (N E ⟨241994800256,146483067⟩ E) ⟨241994800384,146166296⟩ E)) ⟨241994800512,145850382⟩ (N (N (N E ⟨241994800768,145221109⟩ E) ⟨241994800896,144907746⟩ (N E ⟨241994801024,144595228⟩ E)) ⟨241994801152,144283552⟩ (N (N E ⟨242129013632,195876612⟩ E) ⟨242129013760,195445088⟩ E))))) ⟨242129013888,195014752⟩ (N (N (N (N (N (N E ⟨242129014016,194585599⟩ E) ⟨242129014144,194157627⟩ (N E ⟨242129014272,193730831⟩ E)) ⟨242129014400,193305207⟩ (N (N E ⟨242129014528,192880752⟩ E) ⟨242129014656,192457461⟩ (N E ⟨242129014784,192035331⟩ E))) ⟨242129014912,191614359⟩ (N (N (N E ⟨242129015040,191194539⟩ E) ⟨242129015168,190775868⟩ (N E ⟨242129015296,190358343⟩ E)) ⟨242129015424,189941960⟩ (N (N E ⟨242129015552,189526715⟩ E) ⟨242129015680,189112605⟩ E))) ⟨242129015808,188699625⟩ (N (N (N (N E ⟨242129015936,188287772⟩ E) ⟨242129016064,187877042⟩ (N E ⟨242129016192,187467432⟩ E)) ⟨242129016320,187058937⟩ (N (N E ⟨242129016448,186651555⟩ E) ⟨242129016576,186245282⟩ E)) ⟨242129016832,185436046⟩ (N (N (N E ⟨242129017088,184631202⟩ E) ⟨242129017216,184230418⟩ (N E ⟨242129017344,183830721⟩ E)) ⟨242129017472,183432107⟩ (N (N E ⟨242129017600,183034573⟩ E) ⟨242129017728,182638116⟩ E)))) ⟨242129017856,182242732⟩ (N (N (N (N (N E ⟨242129017984,181848418⟩ E) ⟨242129018240,181062984⟩ (N E ⟨242129018368,180671857⟩ E)) ⟨242129018496,180281786⟩ (N (N E ⟨242129018624,179892768⟩ E) ⟨242129018752,179504798⟩ (N E ⟨242129018880,179117874⟩ E))) ⟨242263231360,238068739⟩ (N (N (N E ⟨242263231488,237544264⟩ E) ⟨242263231616,237021232⟩ (N E ⟨242263231744,236499640⟩ E)) ⟨242263231872,235979482⟩ (N (N E ⟨242263232000,235460753⟩ E) ⟨242263232128,234943450⟩ E))) ⟨242263232256,234427566⟩ (N (N (N (N E ⟨242263232384,233913098⟩ E) ⟨242263232512,233400041⟩ (N E ⟨242263232640,232888389⟩ E)) ⟨242263232768,232378140⟩ (N (N E ⟨242263232896,231869287⟩ E) ⟨242263233024,231361827⟩ E)) ⟨242263233152,230855754⟩ (N (N (N E ⟨242263233280,230351065⟩ E) ⟨242263233408,229847754⟩ (N E ⟨242263233536,229345818⟩ E)) ⟨242263233664,228845251⟩ (N (N E ⟨242263233792,228346049⟩ E) ⟨242263233920,227848208⟩ E)))))))

noncomputable def tab24 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨242263234176,226856591⟩ E) ⟨242263234304,226362805⟩ (N E ⟨242263234432,225870363⟩ E)) ⟨242263234560,225379259⟩ (N (N E ⟨242263234688,224889490⟩ E) ⟨242263234816,224401050⟩ (N E ⟨242263234944,223913936⟩ E))) ⟨242263235072,223428144⟩ (N (N (N E ⟨242263235200,222943668⟩ E) ⟨242263235456,221978651⟩ (N E ⟨242263235584,221498100⟩ E)) ⟨242263235712,221018850⟩ (N (N E ⟨242263235840,220540895⟩ E) ⟨242263235968,220064232⟩ E))) ⟨242263236096,219588856⟩ (N (N (N (N E ⟨242263236352,218641950⟩ E) ⟨242263236480,218170411⟩ (N E ⟨242263236608,217700143⟩ E)) ⟨242397449088,284347497⟩ (N (N E ⟨242397449216,283721068⟩ E) ⟨242397449344,283096363⟩ (N E ⟨242397449472,282473377⟩ E))) ⟨242397449600,281852104⟩ (N (N (N E ⟨242397449728,281232539⟩ E) ⟨242397449856,280614675⟩ (N E ⟨242397449984,279998507⟩ E)) ⟨242397450112,279384031⟩ (N (N E ⟨242397450240,278771239⟩ E) ⟨242397450368,278160126⟩ E)))) ⟨242397450496,277550688⟩ (N (N (N (N (N E ⟨242397450624,276942918⟩ E) ⟨242397450752,276336812⟩ (N E ⟨242397450880,275732362⟩ E)) ⟨242397451008,275129565⟩ (N (N E ⟨242397451136,274528415⟩ E) ⟨242397451264,273928906⟩ (N E ⟨242397451392,273331032⟩ E))) ⟨242397451520,272734790⟩ (N (N (N E ⟨242397451648,272140172⟩ E) ⟨242397451776,271547175⟩ (N E ⟨242397451904,270955792⟩ E)) ⟨242397452032,270366018⟩ (N (N E ⟨242397452160,269777849⟩ E) ⟨242397452288,269191278⟩ E))) ⟨242397452416,268606301⟩ (N (N (N (N E ⟨242397452672,267441108⟩ E) ⟨242397452800,266860881⟩ (N E ⟨242397452928,266282227⟩ E)) ⟨242397453056,265705141⟩ (N (N E ⟨242397453184,265129617⟩ E) ⟨242397453312,264555651⟩ E)) ⟨242397453440,263983238⟩ (N (N (N E ⟨242397453568,263412373⟩ E) ⟨242397453696,262843050⟩ (N E ⟨242397453824,262275265⟩ E)) ⟨242397453952,261709012⟩ (N (N E ⟨242397454080,261144287⟩ E) ⟨242397454208,260581085⟩ E))))) ⟨242397454336,260019400⟩ (N (N (N (N (N (N E ⟨242531666944,333961037⟩ E) ⟨242531667072,333225713⟩ (N E ⟨242531667200,332492411⟩ E)) ⟨242531667328,331761126⟩ (N (N E ⟨242531667456,331031851⟩ E) ⟨242531667584,330304579⟩ (N E ⟨242531667712,329579304⟩ E))) ⟨242531667840,328856018⟩ (N (N (N E ⟨242531667968,328134716⟩ E) ⟨242531668096,327415391⟩ (N E ⟨242531668224,326698036⟩ E)) ⟨242531668352,325982645⟩ (N (N E ⟨242531668480,325269212⟩ E) ⟨242531668608,324557730⟩ E))) ⟨242531668736,323848192⟩ (N (N (N (N E ⟨242531668864,323140593⟩ E) ⟨242531668992,322434926⟩ (N E ⟨242531669120,321731184⟩ E)) ⟨242531669248,321029362⟩ (N (N E ⟨242531669376,320329452⟩ E) ⟨242531669504,319631449⟩ E)) ⟨242531669632,318935347⟩ (N (N (N E ⟨242531669888,317548820⟩ E) ⟨242531670016,316858382⟩ (N E ⟨242531670144,316169820⟩ E)) ⟨242531670272,315483128⟩ (N (N E ⟨242531670400,314798300⟩ E) ⟨242531670656,313434210⟩ E)))) ⟨242531670912,312077501⟩ (N (N (N (N (N E ⟨242531671296,310056176⟩ E) ⟨242531671424,309386040⟩ (N E ⟨242531671552,308717714⟩ E)) ⟨242531671680,308051192⟩ (N (N E ⟨242531671936,306723537⟩ E) ⟨242531672064,306062392⟩ (N E ⟨242665884672,388247207⟩ E))) ⟨242665884800,387392354⟩ (N (N (N E ⟨242665884928,386539853⟩ E) ⟨242665885056,385689695⟩ (N E ⟨242665885184,384841875⟩ E)) ⟨242665885312,383996383⟩ (N (N E ⟨242665885440,383153212⟩ E) ⟨242665885568,382312355⟩ E))) ⟨242665885696,381473804⟩ (N (N (N (N E ⟨242665885824,380637550⟩ E) ⟨242665885952,379803588⟩ (N E ⟨242665886080,378971909⟩ E)) ⟨242665886208,378142505⟩ (N (N E ⟨242665886336,377315370⟩ E) ⟨242665886464,376490495⟩ E)) ⟨242665886592,375667874⟩ (N (N (N E ⟨242665886720,374847499⟩ E) ⟨242665886848,374029362⟩ (N E ⟨242665886976,373213456⟩ E)) ⟨242665887104,372399775⟩ (N (N E ⟨242665887232,371588310⟩ E) ⟨242665887360,370779055⟩ E)))))) ⟨242665887488,369972002⟩ (N (N (N (N (N (N (N E ⟨242665887616,369167144⟩ E) ⟨242665887744,368364474⟩ (N E ⟨242665887872,367563985⟩ E)) ⟨242665888000,366765670⟩ (N (N E ⟨242665888128,365969521⟩ E) ⟨242665888256,365175531⟩ (N E ⟨242665888384,364383694⟩ E))) ⟨242665888512,363594003⟩ (N (N (N E ⟨242665888640,362806450⟩ E) ⟨242665888768,362021029⟩ (N E ⟨242665888896,361237732⟩ E)) ⟨242665889024,360456553⟩ (N (N E ⟨242665889408,358125654⟩ E) ⟨242665889664,356582186⟩ E))) ⟨242665889792,355813570⟩ (N (N (N (N E ⟨242800102528,445576866⟩ E) ⟨242800102656,444596323⟩ (N E ⟨242800102784,443618477⟩ E)) ⟨242800102912,442643317⟩ (N (N E ⟨242800103040,441670837⟩ E) ⟨242800103168,440701026⟩ (N E ⟨242800103296,439733876⟩ E))) ⟨242800103424,438769378⟩ (N (N (N E ⟨242800103552,437807523⟩ E) ⟨242800103680,436848304⟩ (N E ⟨242800103808,435891710⟩ E)) ⟨242800103936,434937734⟩ (N (N E ⟨242800104064,433986367⟩ E) ⟨242800104192,433037600⟩ E)))) ⟨242800104320,432091425⟩ (N (N (N (N (N E ⟨242800104448,431147833⟩ E) ⟨242800104576,430206816⟩ (N E ⟨242800104704,429268365⟩ E)) ⟨242800104832,428332473⟩ (N (N E ⟨242800104960,427399130⟩ E) ⟨242800105088,426468328⟩ (N E ⟨242800105216,425540060⟩ E))) ⟨242800105344,424614316⟩ (N (N (N E ⟨242800105472,423691089⟩ E) ⟨242800105600,422770370⟩ (N E ⟨242800105728,421852151⟩ E)) ⟨242800105856,420936424⟩ (N (N E ⟨242800105984,420023181⟩ E) ⟨242800106112,419112414⟩ E))) ⟨242800106240,418204115⟩ (N (N (N (N E ⟨242800106496,416394887⟩ E) ⟨242800106624,415493943⟩ (N E ⟨242800106752,414595435⟩ E)) ⟨242800106880,413699355⟩ (N (N E ⟨242800107008,412805694⟩ E) ⟨242800107136,411914446⟩ E)) ⟨242800107264,411025603⟩ (N (N (N E ⟨242800107392,410139156⟩ E) ⟨242800107520,409255098⟩ (N E ⟨242934320384,506639966⟩ E)) ⟨242934320512,505525661⟩ (N (N E ⟨242934320640,504414417⟩ E) ⟨242934320768,503306226⟩ E))))) ⟨242934320896,502201078⟩ (N (N (N (N (N (N E ⟨242934321024,501098961⟩ E) ⟨242934321152,499999867⟩ (N E ⟨242934321280,498903786⟩ E)) ⟨242934321408,497810706⟩ (N (N E ⟨242934321536,496720620⟩ E) ⟨242934321664,495633516⟩ (N E ⟨242934321792,494549385⟩ E))) ⟨242934321920,493468217⟩ (N (N (N E ⟨242934322048,492390002⟩ E) ⟨242934322176,491314732⟩ (N E ⟨242934322304,490242396⟩ E)) ⟨242934322432,489172984⟩ (N (N E ⟨242934322560,488106487⟩ E) ⟨242934322688,487042896⟩ E))) ⟨242934322816,485982200⟩ (N (N (N (N E ⟨242934322944,484924391⟩ E) ⟨242934323072,483869460⟩ (N E ⟨242934323200,482817396⟩ E)) ⟨242934323328,481768190⟩ (N (N E ⟨242934323584,479678316⟩ E) ⟨242934323712,478637630⟩ E)) ⟨242934323840,477599765⟩ (N (N (N E ⟨242934323968,476564712⟩ E) ⟨242934324096,475532462⟩ (N E ⟨242934324224,474503005⟩ E)) ⟨242934324352,473476334⟩ (N (N E ⟨242934324480,472452439⟩ E) ⟨242934324608,471431310⟩ E)))) ⟨242934324736,470412939⟩ (N (N (N (N (N E ⟨242934324864,469397317⟩ E) ⟨242934324992,468384434⟩ (N E ⟨242934325120,467374283⟩ E)) ⟨242934325248,466366854⟩ (N (N E ⟨243068538112,572646451⟩ E) ⟨243068538240,571386970⟩ (N E ⟨243068538368,570130951⟩ E))) ⟨243068538496,568878382⟩ (N (N (N E ⟨243068538624,567629251⟩ E) ⟨243068538752,566383548⟩ (N E ⟨243068538880,565141261⟩ E)) ⟨243068539008,563902378⟩ (N (N E ⟨243068539136,562666890⟩ E) ⟨243068539264,561434783⟩ E))) ⟨243068539392,560206048⟩ (N (N (N (N E ⟨243068539520,558980674⟩ E) ⟨243068539648,557758648⟩ (N E ⟨243068539776,556539961⟩ E)) ⟨243068539904,555324601⟩ (N (N E ⟨243068540032,554112558⟩ E) ⟨243068540160,552903820⟩ E)) ⟨243068540288,551698377⟩ (N (N (N E ⟨243068540416,550496218⟩ E) ⟨243068540544,549297333⟩ (N E ⟨243068540672,548101709⟩ E)) ⟨243068540928,545720208⟩ (N (N E ⟨243068541056,544534309⟩ E) ⟨243068541184,543351630⟩ E)))))))

noncomputable def tab25 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨243068541440,540995891⟩ E) ⟨243068541568,539822810⟩ (N E ⟨243068541696,538652907⟩ E)) ⟨243068541824,537486172⟩ (N (N E ⟨243068541952,536322596⟩ E) ⟨243068542080,535162167⟩ (N E ⟨243068542208,534004875⟩ E))) ⟨243068542592,530551723⟩ (N (N (N E ⟨243068542720,529406880⟩ E) ⟨243068542976,527126444⟩ (N E ⟨243202756096,639766242⟩ E)) ⟨243202756224,638360685⟩ (N (N E ⟨243202756352,636958987⟩ E) ⟨243202756480,635561135⟩ E))) ⟨243202756608,634167116⟩ (N (N (N (N E ⟨243202756736,632776917⟩ E) ⟨243202756864,631390527⟩ (N E ⟨243202756992,630007933⟩ E)) ⟨243202757120,628629121⟩ (N (N E ⟨243202757248,627254080⟩ E) ⟨243202757376,625882798⟩ (N E ⟨243202757504,624515261⟩ E))) ⟨243202757632,623151458⟩ (N (N (N E ⟨243202757760,621791377⟩ E) ⟨243202757888,620435005⟩ (N E ⟨243202758016,619082330⟩ E)) ⟨243202758144,617733341⟩ (N (N E ⟨243202758272,616388024⟩ E) ⟨243202758400,615046369⟩ E)))) ⟨243202758528,613708362⟩ (N (N (N (N (N E ⟨243202758656,612373993⟩ E) ⟨243202758784,611043249⟩ (N E ⟨243202758912,609716119⟩ E)) ⟨243202759040,608392590⟩ (N (N E ⟨243202759168,607072652⟩ E) ⟨243202759296,605756291⟩ (N E ⟨243202759424,604443498⟩ E))) ⟨243202759680,601828565⟩ (N (N (N E ⟨243202759808,600526402⟩ E) ⟨243202760064,597932627⟩ (N E ⟨243202760192,596640992⟩ E)) ⟨243202760320,595352843⟩ (N (N E ⟨243202760448,594068169⟩ E) ⟨243202760704,591509203⟩ E))) ⟨243336973952,711724084⟩ (N (N (N (N E ⟨243336974080,710161296⟩ E) ⟨243336974208,708602796⟩ (N E ⟨243336974336,707048570⟩ E)) ⟨243336974464,705498604⟩ (N (N E ⟨243336974592,703952883⟩ E) ⟨243336974720,702411394⟩ E)) ⟨243336974848,700874123⟩ (N (N (N E ⟨243336974976,699341056⟩ E) ⟨243336975104,697812179⟩ (N E ⟨243336975232,696287479⟩ E)) ⟨243336975360,694766942⟩ (N (N E ⟨243336975488,693250553⟩ E) ⟨243336975616,691738301⟩ E))))) ⟨243336975744,690230170⟩ (N (N (N (N (N (N E ⟨243336975872,688726149⟩ E) ⟨243336976000,687226222⟩ (N E ⟨243336976128,685730377⟩ E)) ⟨243336976256,684238601⟩ (N (N E ⟨243336976384,682750879⟩ E) ⟨243336976512,681267200⟩ (N E ⟨243336976640,679787550⟩ E))) ⟨243336976768,678311915⟩ (N (N (N E ⟨243336976896,676840283⟩ E) ⟨243336977152,673908975⟩ (N E ⟨243336977280,672449272⟩ E)) ⟨243336977408,670993521⟩ (N (N E ⟨243336977536,669541708⟩ E) ⟨243336977664,668093819⟩ E))) ⟨243336977920,665209768⟩ (N (N (N (N E ⟨243336978048,663773579⟩ E) ⟨243336978176,662341265⟩ (N E ⟨243336978304,660912813⟩ E)) ⟨243336978432,659488210⟩ (N (N E ⟨243471191680,788937101⟩ E) ⟨243471191936,785477193⟩ E)) ⟨243471192064,783754353⟩ (N (N (N E ⟨243471192192,782036235⟩ E) ⟨243471192320,780322823⟩ (N E ⟨243471192448,778614103⟩ E)) ⟨243471192576,776910057⟩ (N (N E ⟨243471192704,775210672⟩ E) ⟨243471192832,773515932⟩ E)))) ⟨243471192960,771825821⟩ (N (N (N (N (N E ⟨243471193088,770140324⟩ E) ⟨243471193216,768459427⟩ (N E ⟨243471193344,766783115⟩ E)) ⟨243471193472,765111371⟩ (N (N E ⟨243471193600,763444182⟩ E) ⟨243471193728,761781532⟩ (N E ⟨243471193856,760123407⟩ E))) ⟨243471193984,758469792⟩ (N (N (N E ⟨243471194112,756820672⟩ E) ⟨243471194240,755176033⟩ (N E ⟨243471194368,753535859⟩ E)) ⟨243471194496,751900137⟩ (N (N E ⟨243471194624,750268851⟩ E) ⟨243471194752,748641988⟩ E))) ⟨243471194880,747019533⟩ (N (N (N (N E ⟨243471195008,745401472⟩ E) ⟨243471195136,743787790⟩ (N E ⟨243471195392,740573507⟩ E)) ⟨243471195648,737376573⟩ (N (N E ⟨243471195776,735784576⟩ E) ⟨243471195904,734196874⟩ E)) ⟨243471196160,731034299⟩ (N (N (N E ⟨243605409792,864250802⟩ E) ⟨243605409920,862356222⟩ (N E ⟨243605410048,860466832⟩ E)) ⟨243605410176,858582615⟩ (N (N E ⟨243605410304,856703554⟩ E) ⟨243605410432,854829631⟩ E)))))) ⟨243605410560,852960830⟩ (N (N (N (N (N (N (N E ⟨243605410688,851097135⟩ E) ⟨243605410816,849238527⟩ (N E ⟨243605410944,847384992⟩ E)) ⟨243605411072,845536511⟩ (N (N E ⟨243605411200,843693069⟩ E) ⟨243605411328,841854649⟩ (N E ⟨243605411456,840021235⟩ E))) ⟨243605411584,838192811⟩ (N (N (N E ⟨243605411712,836369359⟩ E) ⟨243605411840,834550864⟩ (N E ⟨243605411968,832737310⟩ E)) ⟨243605412096,830928680⟩ (N (N E ⟨243605412224,829124959⟩ E) ⟨243605412352,827326130⟩ E))) ⟨243605412480,825532178⟩ (N (N (N (N E ⟨243605412608,823743087⟩ E) ⟨243605412736,821958841⟩ (N E ⟨243605412864,820179423⟩ E)) ⟨243605412992,818404820⟩ (N (N E ⟨243605413120,816635014⟩ E) ⟨243605413248,814869991⟩ (N E ⟨243605413632,809603461⟩ E))) ⟨243605413760,807857412⟩ (N (N (N E ⟨243605413888,806116070⟩ E) ⟨243739627648,946422601⟩ (N E ⟨243739627776,944349025⟩ E)) ⟨243739627904,942281126⟩ (N (N E ⟨243739628032,940218885⟩ E) ⟨243739628160,938162284⟩ E)))) ⟨243739628288,936111304⟩ (N (N (N (N (N E ⟨243739628416,934065926⟩ E) ⟨243739628544,932026134⟩ (N E ⟨243739628672,929991907⟩ E)) ⟨243739628800,927963228⟩ (N (N E ⟨243739628928,925940079⟩ E) ⟨243739629056,923922442⟩ (N E ⟨243739629184,921910299⟩ E))) ⟨243739629312,919903631⟩ (N (N (N E ⟨243739629440,917902421⟩ E) ⟨243739629568,915906651⟩ (N E ⟨243739629696,913916303⟩ E)) ⟨243739629824,911931360⟩ (N (N E ⟨243739629952,909951804⟩ E) ⟨243739630080,907977617⟩ E))) ⟨243739630208,906008783⟩ (N (N (N (N E ⟨243739630336,904045283⟩ E) ⟨243739630592,900134217⟩ (N E ⟨243739630720,898186617⟩ E)) ⟨243739630848,896244283⟩ (N (N E ⟨243739631360,888527262⟩ E) ⟨243739631488,886611001⟩ E)) ⟨243739631616,884699904⟩ (N (N (N E ⟨243873845632,1029671481⟩ E) ⟨243873845760,1027417981⟩ (N E ⟨243873845888,1025170644⟩ E)) ⟨243873846016,1022929449⟩ (N (N E ⟨243873846144,1020694377⟩ E) ⟨243873846272,1018465407⟩ E))))) ⟨243873846528,1014025694⟩ (N (N (N (N (N (N E ⟨243873846656,1011814911⟩ E) ⟨243873846784,1009610151⟩ (N E ⟨243873846912,1007411394⟩ E)) ⟨243873847040,1005218621⟩ (N (N E ⟨243873847168,1003031812⟩ E) ⟨243873847296,1000850948⟩ (N E ⟨243873847424,998676008⟩ E))) ⟨243873847552,996506975⟩ (N (N (N E ⟨243873847936,990035118⟩ E) ⟨243873848064,987889516⟩ (N E ⟨243873848192,985749725⟩ E)) ⟨243873848320,983615725⟩ (N (N E ⟨243873848448,981487498⟩ E) ⟨243873848576,979365025⟩ E))) ⟨243873848960,973031944⟩ (N (N (N (N E ⟨243873849088,970932301⟩ E) ⟨243873849344,966749982⟩ (N E ⟨244008063488,1118260451⟩ E)) ⟨244008063616,1115814408⟩ (N (N E ⟨244008063744,1113375051⟩ E) ⟨244008063872,1110942357⟩ E)) ⟨244008064000,1108516306⟩ (N (N (N E ⟨244008064128,1106096874⟩ E) ⟨244008064256,1103684041⟩ (N E ⟨244008064384,1101277785⟩ E)) ⟨244008064512,1098878084⟩ (N (N E ⟨244008064640,1096484917⟩ E) ⟨244008064896,1091718100⟩ E)))) ⟨244008065024,1089344408⟩ (N (N (N (N (N E ⟨244008065152,1086977164⟩ E) ⟨244008065280,1084616349⟩ (N E ⟨244008065408,1082261940⟩ E)) ⟨244008065792,1075236949⟩ (N (N E ⟨244008065920,1072907962⟩ E) ⟨244008066048,1070585278⟩ (N E ⟨244008066432,1063654843⟩ E))) ⟨244008066560,1061357169⟩ (N (N (N E ⟨244008066688,1059065697⟩ E) ⟨244008066816,1056780408⟩ (N E ⟨244008067072,1052228295⟩ E)) ⟨244142281472,1207405600⟩ (N (N E ⟨244142281600,1204767452⟩ E) ⟨244142281728,1202136507⟩ E))) ⟨244142281856,1199512742⟩ (N (N (N (N E ⟨244142281984,1196896132⟩ E) ⟨244142282112,1194286654⟩ (N E ⟨244142282240,1191684286⟩ E)) ⟨244142282368,1189089003⟩ (N (N E ⟨244142282496,1186500783⟩ E) ⟨244142282624,1183919603⟩ E)) ⟨244142282752,1181345439⟩ (N (N (N E ⟨244142282880,1178778269⟩ E) ⟨244142283008,1176218070⟩ (N E ⟨244142283136,1173664819⟩ E)) ⟨244142283264,1171118493⟩ (N (N E ⟨244142283392,1168579071⟩ E) ⟨244142283520,1166046529⟩ E)))))))

noncomputable def tab26 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨244142283776,1161001999⟩ E) ⟨244142283904,1158489965⟩ (N E ⟨244142284032,1155984723⟩ E)) ⟨244142284288,1150994526⟩ (N (N E ⟨244142284416,1148509528⟩ E) ⟨244142284544,1146031233⟩ (N E ⟨244142284800,1141094669⟩ E))) ⟨244276499840,1290797224⟩ (N (N (N E ⟨244276499968,1287984558⟩ E) ⟨244276500096,1285179550⟩ (N E ⟨244276500224,1282382175⟩ E)) ⟨244276500352,1279592409⟩ (N (N E ⟨244276500608,1274035603⟩ E) ⟨244276500736,1271268513⟩ E))) ⟨244276500992,1265756839⟩ (N (N (N (N E ⟨244276501120,1263012205⟩ E) ⟨244276501248,1260275008⟩ (N E ⟨244276501504,1254822828⟩ E)) ⟨244276501632,1252107796⟩ (N (N E ⟨244276501760,1249400105⟩ E) ⟨244276501888,1246699731⟩ (N E ⟨244276502016,1244006650⟩ E))) ⟨244276502272,1238642271⟩ (N (N (N E ⟨244276502528,1233306783⟩ E) ⟨244410717568,1390762974⟩ (N E ⟨244410718208,1375692753⟩ E)) ⟨244410718464,1369721862⟩ (N (N E ⟨244410718720,1363783337⟩ E) ⟨244410718848,1360826145⟩ E)))) ⟨244410719104,1354935774⟩ (N (N (N (N (N E ⟨244410719360,1349077245⟩ E) ⟨244410719488,1346159857⟩ (N E ⟨244410719616,1343250352⟩ E)) ⟨244410719872,1337454890⟩ (N (N E ⟨244410720128,1331690657⟩ E) ⟨244410720256,1328820187⟩ (N E ⟨244544936320,1468335838⟩ E))) ⟨244544937344,1443091055⟩ (N (N (N E ⟨244544937600,1436864830⟩ E) ⟨244544937984,1427588329⟩ (N E ⟨244679154560,1559623396⟩ E)) ⟨244679154688,1556247046⟩ (N (N E ⟨244679155712,1529562576⟩ E) ⟨244813373440,1634692240⟩ E))) ⟨244947591168,1742924605⟩ (N (N (N (N E ⟨245081808896,1854204952⟩ E) ⟨245216026624,1968476591⟩ (N E ⟨245350244352,2085680892⟩ E)) ⟨245484462080,2205757314⟩ (N (N E ⟨245618679808,2328643438⟩ E) ⟨245887115264,2582585939⟩ E)) ⟨246021332992,2713508404⟩ (N (N (N E ⟨246155550720,2846972824⟩ E) ⟨246289768448,2982907926⟩ (N E ⟨246423986176,3121240784⟩ E)) ⟨246558203904,3261896857⟩ (N (N E ⟨246692421632,3404800031⟩ E) ⟨246826639360,3549872660⟩ E))))) ⟨247229292544,3997308832⟩ (N (N (N (N (N (N E ⟨247900381184,4778767791⟩ E) ⟨248303034368,5265255281⟩ (N E ⟨249108340864,6252832886⟩ E)) ⟨249108340992,6239369381⟩ (N (N E ⟨249108341120,6225942100⟩ E) ⟨249108341248,6212550927⟩ (N E ⟨249108341376,6199195745⟩ E))) ⟨249108341504,6185876437⟩ (N (N (N E ⟨249108341632,6172592889⟩ E) ⟨249108341760,6159344984⟩ (N E ⟨249108341888,6146132609⟩ E)) ⟨249108342016,6132955649⟩ (N (N E ⟨249108342144,6119813990⟩ E) ⟨249108342272,6106707518⟩ E))) ⟨249108342400,6093636122⟩ (N (N (N (N E ⟨249108342528,6080599687⟩ E) ⟨249108342656,6067598102⟩ (N E ⟨249108342784,6054631256⟩ E)) ⟨249108342912,6041699036⟩ (N (N E ⟨249108343040,6028801332⟩ E) ⟨249108343168,6015938033⟩ E)) ⟨249108343296,6003109029⟩ (N (N (N E ⟨249108343424,5990314211⟩ E) ⟨249108343552,5977553470⟩ (N E ⟨249108343680,5964826696⟩ E)) ⟨249108343808,5952133780⟩ (N (N E ⟨249108343936,5939474616⟩ E) ⟨249108344064,5926849095⟩ E)))) ⟨249108344192,5914257110⟩ (N (N (N (N (N E ⟨249108344320,5901698554⟩ E) ⟨249108344448,5889173320⟩ (N E ⟨249108344576,5876681304⟩ E)) ⟨249108344704,5864222398⟩ (N (N E ⟨249108344832,5851796498⟩ E) ⟨249108344960,5839403498⟩ (N E ⟨249108345088,5827043295⟩ E))) ⟨249108345216,5814715784⟩ (N (N (N E ⟨249108345344,5802420861⟩ E) ⟨249108345472,5790158424⟩ (N E ⟨249108345600,5777928368⟩ E)) ⟨249108345728,5765730593⟩ (N (N E ⟨249108345856,5753564994⟩ E) ⟨249108345984,5741431471⟩ E))) ⟨249108346112,5729329922⟩ (N (N (N (N E ⟨249108346240,5717260246⟩ E) ⟨249108346368,5705222343⟩ (N E ⟨249108346496,5693216111⟩ E)) ⟨249108346624,5681241451⟩ (N (N E ⟨249108346752,5669298264⟩ E) ⟨249108346880,5657386450⟩ E)) ⟨249108347008,5645505910⟩ (N (N (N E ⟨249108347136,5633656546⟩ E) ⟨249108347264,5621838259⟩ (N E ⟨249108347392,5610050953⟩ E)) ⟨249108347520,5598294529⟩ (N (N E ⟨249108347648,5586568890⟩ E) ⟨249108347776,5574873941⟩ E)))))) ⟨249108347904,5563209583⟩ (N (N (N (N (N (N (N E ⟨249108348160,5539972262⟩ E) ⟨249108348288,5528399107⟩ (N E ⟨249108348416,5516856162⟩ E)) ⟨249108348544,5505343334⟩ (N (N E ⟨249108348672,5493860527⟩ E) ⟨249108348800,5482407647⟩ (N E ⟨249108348928,5470984602⟩ E))) ⟨249376784384,5767163520⟩ (N (N (N E ⟨251121614848,7692910359⟩ E) ⟨252866445312,9483711292⟩ (N E ⟨257429848064,12307821143⟩ E)) ⟨257698283648,12328914849⟩ (N (N E ⟨257698283776,12297695318⟩ E) ⟨257698283904,12262871751⟩ E))) ⟨257698284032,12224472446⟩ (N (N (N (N E ⟨257698284288,12137070023⟩ E) ⟨257698284416,12088133631⟩ (N E ⟨257698284544,12035754896⟩ E)) ⟨257698284672,11979972077⟩ (N (N E ⟨257698284800,11920825333⟩ E) ⟨257698284928,11858356700⟩ (N E ⟨257698285056,11792610047⟩ E))) ⟨257698285184,11723631051⟩ (N (N (N E ⟨257698285312,11651467159⟩ E) ⟨257698285440,11576167549⟩ (N E ⟨257698285568,11497783098⟩ E)) ⟨257698285696,11416366344⟩ (N (N E ⟨257698285952,11244654140⟩ E) ⟨257698286080,11154471714⟩ E)))) ⟨257698286208,11061482951⟩ (N (N (N (N (N E ⟨257698286464,10867328815⟩ E) ⟨257698286592,10766288143⟩ (N E ⟨257698286720,10662690453⟩ E)) ⟨257698286848,10556601403⟩ (N (N E ⟨257698286976,10448087897⟩ E) ⟨257698287232,10224061067⟩ (N E ⟨257698287360,10108687356⟩ E))) ⟨257698287488,9991168320⟩ (N (N (N E ⟨257698287616,9871576391⟩ E) ⟨257698287744,9749984964⟩ (N E ⟨257698288128,9373961137⟩ E)) ⟨257698288256,9245123305⟩ (N (N E ⟨257698288384,9114665747⟩ E) ⟨257698288512,8982666632⟩ E))) ⟨257698288640,8849204752⟩ (N (N (N (N E ⟨257698288768,8714359474⟩ E) ⟨257698288896,8578210688⟩ (N E ⟨257698289024,8440838759⟩ E)) ⟨257698289152,8302324476⟩ (N (N E ⟨257698289280,8162748999⟩ E) ⟨257698289408,8022193814⟩ E)) ⟨257698289664,7738471579⟩ (N (N (N E ⟨257698289792,7595468668⟩ E) ⟨257698289920,7451814225⟩ (N E ⟨257698290048,7307590603⟩ E)) ⟨257698290176,7162880181⟩ (N (N E ⟨257698290432,6872328267⟩ E) ⟨257698290560,6726651207⟩ E))))) ⟨257698290944,6288998599⟩ (N (N (N (N (N (N E ⟨257698291072,6143178849⟩ E) ⟨257698291200,5997526311⟩ (N E ⟨257698291584,5562373662⟩ E)) ⟨257698291712,5418189199⟩ (N (N E ⟨258235162624,5460129336⟩ E) ⟨261187952640,5691572279⟩ (N E ⟨262261694464,5775032015⟩ E))) ⟨262798565376,5816415634⟩ (N (N (N E ⟨264006524928,5908378508⟩ E) ⟨266288226560,5761840971⟩ (N E ⟨266288226688,5605762311⟩ E)) ⟨266288226816,5450507304⟩ (N (N E ⟨266288227072,5142792756⟩ E) ⟨266288227200,4990493261⟩ E))) ⟨266288227328,4839337425⟩ (N (N (N (N E ⟨266288227456,4689402869⟩ E) ⟨266288227712,4393502857⟩ (N E ⟨266288227840,4247687290⟩ E)) ⟨266288227968,4103392706⟩ (N (N E ⟨266288228224,3819653364⟩ E) ⟨266288228352,3680348919⟩ E)) ⟨266288228480,3542846008⟩ (N (N (N E ⟨266288228736,3273510876⟩ E) ⟨266288228864,3141808217⟩ (N E ⟨266288228992,3012166152⟩ E)) ⟨266288229120,2884645835⟩ (N (N E ⟨266288229248,2759306914⟩ E) ⟨266288229376,2636207502⟩ E)))) ⟨266288229632,2396951801⟩ (N (N (N (N (N E ⟨266288230016,2056225992⟩ E) ⟨266288230144,1947694536⟩ (N E ⟨266288230528,1637884235⟩ E)) ⟨266288230784,1444924345⟩ (N (N E ⟨266288231296,1092973053⟩ E) ⟨266288231424,1012258310⟩ (N E ⟨266288232064,653726513⟩ E))) ⟨266288232192,591188723⟩ (N (N (N E ⟨266288232320,531751646⟩ E) ⟨266288232832,325287065⟩ (N E ⟨266288232960,281544275⟩ E)) ⟨266288233216,203553388⟩ (N (N E ⟨266288233856,64007355⟩ E) ⟨266288234368,9078775⟩ E))) ⟨266556669952,3291863⟩ (N (N (N (N E ⟨274878169216,1499244⟩ E) ⟨275146606592,2966⟩ (N E ⟨275146606720,2960⟩ E)) ⟨275146606848,2954⟩ (N (N E ⟨275146606976,2949⟩ E) ⟨275146607104,2943⟩ E)) ⟨275146607232,2937⟩ (N (N (N E ⟨275146607360,2931⟩ E) ⟨275146607488,2926⟩ (N E ⟨275146607616,2920⟩ E)) ⟨275146607744,2915⟩ (N (N E ⟨275146607872,2909⟩ E) ⟨275146608000,2903⟩ E)))))))

noncomputable def tab27 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨275146608256,2892⟩ E) ⟨275146608384,2887⟩ (N E ⟨275146608512,2881⟩ E)) ⟨275146608640,2875⟩ (N (N E ⟨275146608768,2870⟩ E) ⟨275146608896,2864⟩ (N E ⟨275146609024,2859⟩ E))) ⟨275146609152,2853⟩ (N (N (N E ⟨275146609280,2848⟩ E) ⟨275146609408,2842⟩ (N E ⟨275146609664,2832⟩ E)) ⟨275146609792,2826⟩ (N (N E ⟨275146609920,2821⟩ E) ⟨275146610048,2815⟩ E))) ⟨275146610176,2810⟩ (N (N (N (N E ⟨275146610304,2805⟩ E) ⟨275146610560,2794⟩ (N E ⟨275146610688,2789⟩ E)) ⟨275146610816,2783⟩ (N (N E ⟨275146610944,2778⟩ E) ⟨275146611072,2773⟩ (N E ⟨275146611200,2767⟩ E))) ⟨275146611328,2762⟩ (N (N (N E ⟨275146611584,2752⟩ E) ⟨275146611712,2746⟩ (N E ⟨275146611840,2741⟩ E)) ⟨275146612096,2731⟩ (N (N E ⟨275146612736,2705⟩ E) ⟨275280824064,1740805⟩ E)))) ⟨275280824192,1737429⟩ (N (N (N (N (N E ⟨275280824320,1734062⟩ E) ⟨275280824448,1730703⟩ (N E ⟨275280824576,1727352⟩ E)) ⟨275280824704,1724009⟩ (N (N E ⟨275280824832,1720674⟩ E) ⟨275280824960,1717348⟩ (N E ⟨275280825088,1714029⟩ E))) ⟨275280825216,1710718⟩ (N (N (N E ⟨275280825344,1707415⟩ E) ⟨275280825472,1704121⟩ (N E ⟨275280825600,1700834⟩ E)) ⟨275280825728,1697555⟩ (N (N E ⟨275280825856,1694284⟩ E) ⟨275280825984,1691021⟩ E))) ⟨275280826112,1687766⟩ (N (N (N (N E ⟨275280826240,1684518⟩ E) ⟨275280826368,1681279⟩ (N E ⟨275280826496,1678047⟩ E)) ⟨275280826624,1674823⟩ (N (N E ⟨275280826880,1668398⟩ E) ⟨275280827008,1665197⟩ E)) ⟨275280827136,1662004⟩ (N (N (N E ⟨275280827264,1658818⟩ E) ⟨275280827392,1655640⟩ (N E ⟨275280827520,1652470⟩ E)) ⟨275280827648,1649307⟩ (N (N E ⟨275280827776,1646152⟩ E) ⟨275280828032,1639864⟩ E))))) ⟨275280828160,1636731⟩ (N (N (N (N (N (N E ⟨275280828288,1633606⟩ E) ⟨275280828416,1630489⟩ (N E ⟨275280828544,1627378⟩ E)) ⟨275280828672,1624276⟩ (N (N E ⟨275280828800,1621180⟩ E) ⟨275280828928,1618092⟩ (N E ⟨275280829056,1615011⟩ E))) ⟨275280829184,1611938⟩ (N (N (N E ⟨275280829312,1608872⟩ E) ⟨275280829696,1599717⟩ (N E ⟨275280829824,1596680⟩ E)) ⟨275280829952,1593650⟩ (N (N E ⟨275280830208,1587612⟩ E) ⟨275280830336,1584604⟩ E))) ⟨275280830464,1581602⟩ (N (N (N (N E ⟨275415041920,6670583⟩ E) ⟨275415042048,6657655⟩ (N E ⟨275415042176,6644758⟩ E)) ⟨275415042304,6631892⟩ (N (N E ⟨275415042432,6619058⟩ E) ⟨275415042560,6606254⟩ E)) ⟨275415042688,6593482⟩ (N (N (N E ⟨275415042816,6580740⟩ E) ⟨275415042944,6568029⟩ (N E ⟨275415043072,6555349⟩ E)) ⟨275415043200,6542699⟩ (N (N E ⟨275415043328,6530080⟩ E) ⟨275415043456,6517492⟩ E)))) ⟨275415043584,6504933⟩ (N (N (N (N (N E ⟨275415043712,6492405⟩ E) ⟨275415043840,6479907⟩ (N E ⟨275415043968,6467439⟩ E)) ⟨275415044096,6455001⟩ (N (N E ⟨275415044224,6442593⟩ E) ⟨275415044352,6430215⟩ (N E ⟨275415044480,6417866⟩ E))) ⟨275415044736,6393258⟩ (N (N (N E ⟨275415044864,6380998⟩ E) ⟨275415044992,6368768⟩ (N E ⟨275415045120,6356566⟩ E)) ⟨275415045248,6344394⟩ (N (N E ⟨275415045376,6332251⟩ E) ⟨275415045504,6320138⟩ E))) ⟨275415045632,6308053⟩ (N (N (N (N E ⟨275415045760,6295997⟩ E) ⟨275415045888,6283969⟩ (N E ⟨275415046016,6271971⟩ E)) ⟨275415046144,6260001⟩ (N (N E ⟨275415046272,6248060⟩ E) ⟨275415046400,6236147⟩ E)) ⟨275415046528,6224262⟩ (N (N (N E ⟨275415046656,6212406⟩ E) ⟨275415046784,6200578⟩ (N E ⟨275415047296,6153547⟩ E)) ⟨275415047552,6130198⟩ (N (N E ⟨275415047808,6106961⟩ E) ⟨275415047936,6095383⟩ E)))))) ⟨275415048192,6072310⟩ (N (N (N (N (N (N (N E ⟨275549259776,14780086⟩ E) ⟨275549259904,14751455⟩ (N E ⟨275549260032,14722893⟩ E)) ⟨275549260160,14694400⟩ (N (N E ⟨275549260288,14665976⟩ E) ⟨275549260416,14637621⟩ (N E ⟨275549260544,14609334⟩ E))) ⟨275549260672,14581116⟩ (N (N (N E ⟨275549260800,14552966⟩ E) ⟨275549260928,14524883⟩ (N E ⟨275549261056,14496869⟩ E)) ⟨275549261184,14468922⟩ (N (N E ⟨275549261312,14441042⟩ E) ⟨275549261440,14413229⟩ E))) ⟨275549261568,14385483⟩ (N (N (N (N E ⟨275549261696,14357804⟩ E) ⟨275549261824,14330192⟩ (N E ⟨275549262080,14275166⟩ E)) ⟨275549262208,14247752⟩ (N (N E ⟨275549262336,14220404⟩ E) ⟨275549262464,14193121⟩ (N E ⟨275549262592,14165904⟩ E))) ⟨275549262720,14138752⟩ (N (N (N E ⟨275549262848,14111665⟩ E) ⟨275549262976,14084643⟩ (N E ⟨275549263104,14057686⟩ E)) ⟨275549263232,14030793⟩ (N (N E ⟨275549263360,14003964⟩ E) ⟨275549263488,13977200⟩ E)))) ⟨275549263616,13950499⟩ (N (N (N (N (N E ⟨275549263744,13923862⟩ E) ⟨275549263872,13897289⟩ (N E ⟨275549264000,13870779⟩ E)) ⟨275549264128,13844332⟩ (N (N E ⟨275549264256,13817949⟩ E) ⟨275549264384,13791628⟩ (N E ⟨275549264512,13765369⟩ E))) ⟨275549264640,13739174⟩ (N (N (N E ⟨275549264768,13713040⟩ E) ⟨275549264896,13686969⟩ (N E ⟨275549265024,13660959⟩ E)) ⟨275549265152,13635012⟩ (N (N E ⟨275549265408,13583301⟩ E) ⟨275549265664,13531835⟩ E))) ⟨275549265920,13480613⟩ (N (N (N (N E ⟨275683477632,26055198⟩ E) ⟨275683477760,26004749⟩ (N E ⟨275683477888,25954423⟩ E)) ⟨275683478016,25904219⟩ (N (N E ⟨275683478144,25854136⟩ E) ⟨275683478272,25804173⟩ E)) ⟨275683478400,25754332⟩ (N (N (N E ⟨275683478528,25704611⟩ E) ⟨275683478656,25655009⟩ (N E ⟨275683478784,25605528⟩ E)) ⟨275683478912,25556165⟩ (N (N E ⟨275683479040,25506922⟩ E) ⟨275683479168,25457797⟩ E))))) ⟨275683479296,25408790⟩ (N (N (N (N (N (N E ⟨275683479424,25359901⟩ E) ⟨275683479552,25311130⟩ (N E ⟨275683479808,25213939⟩ E)) ⟨275683479936,25165518⟩ (N (N E ⟨275683480064,25117213⟩ E) ⟨275683480192,25069025⟩ (N E ⟨275683480320,25020952⟩ E))) ⟨275683480448,24972994⟩ (N (N (N E ⟨275683480576,24925151⟩ E) ⟨275683480704,24877422⟩ (N E ⟨275683480832,24829808⟩ E)) ⟨275683481088,24734921⟩ (N (N E ⟨275683481216,24687647⟩ E) ⟨275683481344,24640486⟩ E))) ⟨275683481472,24593438⟩ (N (N (N (N E ⟨275683481600,24546502⟩ E) ⟨275683481728,24499678⟩ (N E ⟨275683481984,24406365⟩ E)) ⟨275683482112,24359874⟩ (N (N E ⟨275683482240,24313495⟩ E) ⟨275683482368,24267226⟩ E)) ⟨275683482496,24221067⟩ (N (N (N E ⟨275683482624,24175018⟩ E) ⟨275683482752,24129078⟩ (N E ⟨275683482880,24083247⟩ E)) ⟨275683483008,24037525⟩ (N (N E ⟨275683483392,23901008⟩ E) ⟨275683483648,23810535⟩ E)))) ⟨275817695488,40479930⟩ (N (N (N (N (N E ⟨275817695616,40401590⟩ E) ⟨275817695744,40323440⟩ (N E ⟨275817695872,40245479⟩ E)) ⟨275817696000,40167706⟩ (N (N E ⟨275817696128,40090121⟩ E) ⟨275817696256,40012723⟩ (N E ⟨275817696384,39935512⟩ E))) ⟨275817696512,39858487⟩ (N (N (N E ⟨275817696640,39781648⟩ E) ⟨275817696768,39704993⟩ (N E ⟨275817696896,39628524⟩ E)) ⟨275817697024,39552238⟩ (N (N E ⟨275817697152,39476136⟩ E) ⟨275817697280,39400217⟩ E))) ⟨275817697408,39324480⟩ (N (N (N (N E ⟨275817697536,39248925⟩ E) ⟨275817697664,39173552⟩ (N E ⟨275817697792,39098359⟩ E)) ⟨275817697920,39023347⟩ (N (N E ⟨275817698048,38948515⟩ E) ⟨275817698176,38873862⟩ E)) ⟨275817698304,38799388⟩ (N (N (N E ⟨275817698432,38725092⟩ E) ⟨275817698688,38577033⟩ (N E ⟨275817698816,38503269⟩ E)) ⟨275817699200,38283032⟩ (N (N E ⟨275817699328,38209970⟩ E) ⟨275817699456,38137082⟩ E)))))))

noncomputable def tab28 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨275817699712,37991827⟩ E) ⟨275817699840,37919458⟩ (N E ⟨275817699968,37847263⟩ E)) ⟨275817700096,37775238⟩ (N (N E ⟨275817700224,37703386⟩ E) ⟨275817700352,37631703⟩ (N E ⟨275817700608,37488850⟩ E))) ⟨275817700736,37417677⟩ (N (N (N E ⟨275817700864,37346673⟩ E) ⟨275817700992,37275838⟩ (N E ⟨275817701120,37205170⟩ E)) ⟨275817701376,37064337⟩ (N (N E ⟨275951913344,58036435⟩ E) ⟨275951913472,57924173⟩ E))) ⟨275951913600,57812183⟩ (N (N (N (N E ⟨275951913728,57700463⟩ E) ⟨275951913856,57589013⟩ (N E ⟨275951913984,57477832⟩ E)) ⟨275951914112,57366919⟩ (N (N E ⟨275951914240,57256273⟩ E) ⟨275951914368,57145894⟩ (N E ⟨275951914496,57035781⟩ E))) ⟨275951914624,56925933⟩ (N (N (N E ⟨275951914752,56816350⟩ E) ⟨275951914880,56707030⟩ (N E ⟨275951915008,56597973⟩ E)) ⟨275951915136,56489178⟩ (N (N E ⟨275951915264,56380645⟩ E) ⟨275951915392,56272372⟩ E)))) ⟨275951915520,56164358⟩ (N (N (N (N (N E ⟨275951915648,56056604⟩ E) ⟨275951915776,55949108⟩ (N E ⟨275951915904,55841870⟩ E)) ⟨275951916032,55734889⟩ (N (N E ⟨275951916160,55628164⟩ E) ⟨275951916288,55521694⟩ (N E ⟨275951916416,55415478⟩ E))) ⟨275951916544,55309517⟩ (N (N (N E ⟨275951916672,55203809⟩ E) ⟨275951916800,55098353⟩ (N E ⟨275951917184,54783494⟩ E)) ⟨275951917312,54679041⟩ (N (N E ⟨275951917440,54574836⟩ E) ⟨275951917568,54470880⟩ E))) ⟨275951917696,54367172⟩ (N (N (N (N E ⟨275951917824,54263710⟩ E) ⟨275951917952,54160494⟩ (N E ⟨275951918080,54057523⟩ E)) ⟨275951918336,53852316⟩ (N (N E ⟨275951918464,53750077⟩ E) ⟨275951918592,53648081⟩ E)) ⟨275951918848,53444813⟩ (N (N (N E ⟨275951918976,53343541⟩ E) ⟨275951919104,53242508⟩ (N E ⟨276086131200,78705021⟩ E)) ⟨276086131328,78552853⟩ (N (N E ⟨276086131456,78401052⟩ E) ⟨276086131584,78249618⟩ E))))) ⟨276086131712,78098550⟩ (N (N (N (N (N (N E ⟨276086131840,77947846⟩ E) ⟨276086131968,77797505⟩ (N E ⟨276086132096,77647527⟩ E)) ⟨276086132224,77497910⟩ (N (N E ⟨276086132352,77348653⟩ E) ⟨276086132480,77199755⟩ (N E ⟨276086132608,77051216⟩ E))) ⟨276086132736,76903034⟩ (N (N (N E ⟨276086132864,76755207⟩ E) ⟨276086132992,76607736⟩ (N E ⟨276086133120,76460619⟩ E)) ⟨276086133248,76313855⟩ (N (N E ⟨276086133376,76167443⟩ E) ⟨276086133504,76021383⟩ E))) ⟨276086133632,75875672⟩ (N (N (N (N E ⟨276086133760,75730310⟩ E) ⟨276086133888,75585296⟩ (N E ⟨276086134016,75440629⟩ E)) ⟨276086134144,75296308⟩ (N (N E ⟨276086134528,74865411⟩ E) ⟨276086134656,74722464⟩ E)) ⟨276086134912,74437592⟩ (N (N (N E ⟨276086135040,74295666⟩ E) ⟨276086135168,74154077⟩ (N E ⟨276086135296,74012826⟩ E)) ⟨276086135424,73871911⟩ (N (N E ⟨276086135552,73731331⟩ E) ⟨276086135680,73591086⟩ E)))) ⟨276086135808,73451173⟩ (N (N (N (N (N E ⟨276086136192,73033427⟩ E) ⟨276086136320,72894839⟩ (N E ⟨276086136448,72756580⟩ E)) ⟨276086136576,72618648⟩ (N (N E ⟨276086136832,72343763⟩ E) ⟨276220348928,102662653⟩ (N E ⟨276220349056,102464165⟩ E))) ⟨276220349184,102266156⟩ (N (N (N E ⟨276220349312,102068626⟩ E) ⟨276220349440,101871573⟩ (N E ⟨276220349568,101674995⟩ E)) ⟨276220349696,101478891⟩ (N (N E ⟨276220349824,101283259⟩ E) ⟨276220349952,101088099⟩ E))) ⟨276220350080,100893409⟩ (N (N (N (N E ⟨276220350208,100699188⟩ E) ⟨276220350336,100505433⟩ (N E ⟨276220350464,100312144⟩ E)) ⟨276220350592,100119320⟩ (N (N E ⟨276220350720,99926959⟩ E) ⟨276220350848,99735060⟩ E)) ⟨276220350976,99543622⟩ (N (N (N E ⟨276220351104,99352642⟩ E) ⟨276220351232,99162121⟩ (N E ⟨276220351360,98972056⟩ E)) ⟨276220351488,98782446⟩ (N (N E ⟨276220351616,98593290⟩ E) ⟨276220351744,98404587⟩ E)))))) ⟨276220351872,98216335⟩ (N (N (N (N (N (N (N E ⟨276220352000,98028533⟩ E) ⟨276220352128,97841180⟩ (N E ⟨276220352384,97467814⟩ E)) ⟨276220352512,97281800⟩ (N (N E ⟨276220352640,97096229⟩ E) ⟨276220352896,96726412⟩ (N E ⟨276220353024,96542164⟩ E))) ⟨276220353152,96358355⟩ (N (N (N E ⟨276220353280,96174983⟩ E) ⟨276220353408,95992047⟩ (N E ⟨276220353664,95627478⟩ E)) ⟨276220353792,95445843⟩ (N (N E ⟨276220353920,95264639⟩ E) ⟨276220354048,95083865⟩ E))) ⟨276220354176,94903519⟩ (N (N (N (N E ⟨276220354304,94723601⟩ E) ⟨276220354560,94365042⟩ (N E ⟨276354566912,129290532⟩ E)) ⟨276354567040,129040803⟩ (N (N E ⟨276354567168,128791678⟩ E) ⟨276354567296,128543153⟩ (N E ⟨276354567424,128295227⟩ E))) ⟨276354567552,128047899⟩ (N (N (N E ⟨276354567680,127801167⟩ E) ⟨276354567808,127555029⟩ (N E ⟨276354567936,127309483⟩ E)) ⟨276354568064,127064528⟩ (N (N E ⟨276354568192,126820162⟩ E) ⟨276354568320,126576383⟩ E)))) ⟨276354568448,126333190⟩ (N (N (N (N (N E ⟨276354568576,126090580⟩ E) ⟨276354568704,125848553⟩ (N E ⟨276354568832,125607106⟩ E)) ⟨276354568960,125366238⟩ (N (N E ⟨276354569216,124886232⟩ E) ⟨276354569344,124647091⟩ (N E ⟨276354569472,124408522⟩ E))) ⟨276354569600,124170523⟩ (N (N (N E ⟨276354569728,123933094⟩ E) ⟨276354569856,123696232⟩ (N E ⟨276354569984,123459935⟩ E)) ⟨276354570112,123224202⟩ (N (N E ⟨276354570240,122989032⟩ E) ⟨276354570368,122754423⟩ E))) ⟨276354570496,122520373⟩ (N (N (N (N E ⟨276354570880,121821562⟩ E) ⟨276354571008,121589733⟩ (N E ⟨276354571136,121358456⟩ E)) ⟨276354571264,121127728⟩ (N (N E ⟨276354571520,120667914⟩ E) ⟨276354571648,120438826⟩ E)) ⟨276354571776,120210281⟩ (N (N (N E ⟨276354571904,119982279⟩ E) ⟨276354572032,119754816⟩ (N E ⟨276354572160,119527892⟩ E)) ⟨276354572288,119301506⟩ (N (N E ⟨276488784768,159158992⟩ E) ⟨276488784896,158851720⟩ E))))) ⟨276488785024,158545189⟩ (N (N (N (N (N (N E ⟨276488785152,158239398⟩ E) ⟨276488785280,157934343⟩ (N E ⟨276488785408,157630024⟩ E)) ⟨276488785536,157326437⟩ (N (N E ⟨276488785664,157023580⟩ E) ⟨276488785792,156721453⟩ (N E ⟨276488785920,156420051⟩ E))) ⟨276488786048,156119374⟩ (N (N (N E ⟨276488786176,155819420⟩ E) ⟨276488786304,155520185⟩ (N E ⟨276488786432,155221668⟩ E)) ⟨276488786560,154923868⟩ (N (N E ⟨276488786688,154626781⟩ E) ⟨276488786816,154330407⟩ E))) ⟨276488786944,154034742⟩ (N (N (N (N E ⟨276488787072,153739785⟩ E) ⟨276488787200,153445533⟩ (N E ⟨276488787328,153151986⟩ E)) ⟨276488787456,152859140⟩ (N (N E ⟨276488787584,152566994⟩ E) ⟨276488787712,152275546⟩ E)) ⟨276488787840,151984793⟩ (N (N (N E ⟨276488787968,151694734⟩ E) ⟨276488788096,151405367⟩ (N E ⟨276488788224,151116690⟩ E)) ⟨276488788480,150541396⟩ (N (N E ⟨276488788608,150254776⟩ E) ⟨276488788736,149968838⟩ E)))) ⟨276488789120,149115096⟩ (N (N (N (N (N E ⟨276488789248,148831866⟩ E) ⟨276488789376,148549309⟩ (N E ⟨276488789504,148267421⟩ E)) ⟨276488789632,147986203⟩ (N (N E ⟨276488789760,147705650⟩ E) ⟨276488790016,147146538⟩ (N E ⟨276623002496,192414110⟩ E))) ⟨276623002624,192042636⟩ (N (N (N E ⟨276623002752,191672058⟩ E) ⟨276623002880,191302374⟩ (N E ⟨276623003008,190933581⟩ E)) ⟨276623003136,190565676⟩ (N (N E ⟨276623003264,190198656⟩ E) ⟨276623003392,189832521⟩ E))) ⟨276623003520,189467265⟩ (N (N (N (N E ⟨276623003648,189102888⟩ E) ⟨276623003776,188739387⟩ (N E ⟨276623003904,188376759⟩ E)) ⟨276623004032,188015001⟩ (N (N E ⟨276623004160,187654112⟩ E) ⟨276623004288,187294088⟩ E)) ⟨276623004416,186934928⟩ (N (N (N E ⟨276623004544,186576628⟩ E) ⟨276623004672,186219186⟩ (N E ⟨276623004800,185862599⟩ E)) ⟨276623004928,185506867⟩ (N (N E ⟨276623005056,185151984⟩ E) ⟨276623005184,184797951⟩ E)))))))

noncomputable def tab29 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨276623005440,184092418⟩ E) ⟨276623005568,183740915⟩ (N E ⟨276623005696,183390250⟩ E)) ⟨276623005824,183040422⟩ (N (N E ⟨276623005952,182691428⟩ E) ⟨276623006080,182343265⟩ (N E ⟨276623006208,181995931⟩ E))) ⟨276623006464,181303741⟩ (N (N (N E ⟨276623006592,180958880⟩ E) ⟨276623006720,180614839⟩ (N E ⟨276623006848,180271616⟩ E)) ⟨276623006976,179929207⟩ (N (N E ⟨276623007104,179587611⟩ E) ⟨276623007232,179246826⟩ E))) ⟨276623007488,178567676⟩ (N (N (N (N E ⟨276623007616,178229308⟩ E) ⟨276623007744,177891741⟩ (N E ⟨276757220480,227912801⟩ E)) ⟨276757220608,227473218⟩ (N (N E ⟨276757220736,227034694⟩ E) ⟨276757220864,226597227⟩ (N E ⟨276757220992,226160813⟩ E))) ⟨276757221120,225725449⟩ (N (N (N E ⟨276757221248,225291133⟩ E) ⟨276757221376,224857860⟩ (N E ⟨276757221504,224425629⟩ E)) ⟨276757221632,223994437⟩ (N (N E ⟨276757221760,223564279⟩ E) ⟨276757221888,223135154⟩ E)))) ⟨276757222016,222707058⟩ (N (N (N (N (N E ⟨276757222144,222279988⟩ E) ⟨276757222272,221853942⟩ (N E ⟨276757222400,221428916⟩ E)) ⟨276757222528,221004908⟩ (N (N E ⟨276757222656,220581914⟩ E) ⟨276757222784,220159932⟩ (N E ⟨276757222912,219738959⟩ E))) ⟨276757223040,219318991⟩ (N (N (N E ⟨276757223168,218900027⟩ E) ⟨276757223296,218482062⟩ (N E ⟨276757223424,218065095⟩ E)) ⟨276757223552,217649122⟩ (N (N E ⟨276757223680,217234141⟩ E) ⟨276757223808,216820149⟩ E))) ⟨276757224064,215995118⟩ (N (N (N (N E ⟨276757224192,215584075⟩ E) ⟨276757224448,214764918⟩ (N E ⟨276757224704,213949648⟩ E)) ⟨276757224832,213543465⟩ (N (N E ⟨276757225088,212733985⟩ E) ⟨276757225472,211526945⟩ E)) ⟨276891438336,266739083⟩ (N (N (N E ⟨276891438464,266224862⟩ E) ⟨276891438592,265711881⟩ (N E ⟨276891438720,265200134⟩ E)) ⟨276891438848,264689619⟩ (N (N E ⟨276891438976,264180332⟩ E) ⟨276891439104,263672269⟩ E))))) ⟨276891439232,263165428⟩ (N (N (N (N (N (N E ⟨276891439360,262659804⟩ E) ⟨276891439488,262155393⟩ (N E ⟨276891439616,261652194⟩ E)) ⟨276891439744,261150201⟩ (N (N E ⟨276891439872,260649411⟩ E) ⟨276891440000,260149822⟩ (N E ⟨276891440128,259651429⟩ E))) ⟨276891440256,259154230⟩ (N (N (N E ⟨276891440384,258658220⟩ E) ⟨276891440512,258163396⟩ (N E ⟨276891440640,257669755⟩ E)) ⟨276891440768,257177294⟩ (N (N E ⟨276891440896,256686009⟩ E) ⟨276891441024,256195897⟩ E))) ⟨276891441152,255706954⟩ (N (N (N (N E ⟨276891441408,254732562⟩ E) ⟨276891441536,254247107⟩ (N E ⟨276891441664,253762809⟩ E)) ⟨276891441792,253279663⟩ (N (N E ⟨276891441920,252797666⟩ E) ⟨276891442048,252316816⟩ E)) ⟨276891442560,250404811⟩ (N (N (N E ⟨276891442944,248982683⟩ E) ⟨276891443072,248510885⟩ (N E ⟨276891443200,248040204⟩ E)) ⟨277025656192,308489366⟩ (N (N E ⟨277025656320,307894946⟩ E) ⟨277025656448,307301957⟩ E)))) ⟨277025656576,306710395⟩ (N (N (N (N (N E ⟨277025656704,306120256⟩ E) ⟨277025656832,305531536⟩ (N E ⟨277025656960,304944231⟩ E)) ⟨277025657088,304358336⟩ (N (N E ⟨277025657216,303773849⟩ E) ⟨277025657344,303190763⟩ (N E ⟨277025657472,302609077⟩ E))) ⟨277025657600,302028785⟩ (N (N (N E ⟨277025657728,301449883⟩ E) ⟨277025657856,300872368⟩ (N E ⟨277025657984,300296236⟩ E)) ⟨277025658112,299721482⟩ (N (N E ⟨277025658240,299148102⟩ E) ⟨277025658368,298576094⟩ E))) ⟨277025658624,297436173⟩ (N (N (N (N E ⟨277025658752,296868253⟩ E) ⟨277025658880,296301687⟩ (N E ⟨277025659008,295736473⟩ E)) ⟨277025659136,295172607⟩ (N (N E ⟨277025659264,294610084⟩ E) ⟨277025659392,294048900⟩ E)) ⟨277025659520,293489052⟩ (N (N (N E ⟨277025659648,292930536⟩ E) ⟨277025659776,292373348⟩ (N E ⟨277025660032,291262942⟩ E)) ⟨277025660416,289607200⟩ (N (N E ⟨277025660544,289057902⟩ E) ⟨277025660800,287963208⟩ E)))))) ⟨277025660928,287417804⟩ (N (N (N (N (N (N (N E ⟨277159874048,353129840⟩ E) ⟨277159874304,351771259⟩ (N E ⟨277159874432,351094419⟩ E)) ⟨277159874560,350419206⟩ (N (N E ⟨277159874688,349745616⟩ E) ⟨277159874816,349073644⟩ (N E ⟨277159874944,348403285⟩ E))) ⟨277159875072,347734535⟩ (N (N (N E ⟨277159875200,347067389⟩ E) ⟨277159875328,346401842⟩ (N E ⟨277159875456,345737890⟩ E)) ⟨277159875584,345075528⟩ (N (N E ⟨277159875712,344414752⟩ E) ⟨277159875840,343755558⟩ E))) ⟨277159875968,343097939⟩ (N (N (N (N E ⟨277159876096,342441893⟩ E) ⟨277159876224,341787414⟩ (N E ⟨277159876352,341134499⟩ E)) ⟨277159876480,340483142⟩ (N (N E ⟨277159876608,339833339⟩ E) ⟨277159876736,339185085⟩ (N E ⟨277159876864,338538377⟩ E))) ⟨277159876992,337893210⟩ (N (N (N E ⟨277159877120,337249579⟩ E) ⟨277159877248,336607480⟩ (N E ⟨277159877504,335327861⟩ E)) ⟨277159877632,334690332⟩ (N (N E ⟨277159877760,334054318⟩ E) ⟨277159877888,333419814⟩ E)))) ⟨277159878144,332155319⟩ (N (N (N (N (N E ⟨277159878400,330896814⟩ E) ⟨277159878656,329644265⟩ (N E ⟨277294092160,399084459⟩ E)) ⟨277294092416,397551293⟩ (N (N E ⟨277294092544,396787471⟩ E) ⟨277294092672,396025483⟩ (N E ⟨277294092800,395265323⟩ E))) ⟨277294092928,394506987⟩ (N (N (N E ⟨277294093056,393750469⟩ E) ⟨277294093184,392995763⟩ (N E ⟨277294093312,392242865⟩ E)) ⟨277294093440,391491770⟩ (N (N E ⟨277294093568,390742472⟩ E) ⟨277294093696,389994965⟩ E))) ⟨277294093824,389249246⟩ (N (N (N (N E ⟨277294094080,387763148⟩ E) ⟨277294094208,387022759⟩ (N E ⟨277294094336,386284136⟩ E)) ⟨277294094464,385547275⟩ (N (N E ⟨277294094592,384812171⟩ E) ⟨277294094720,384078817⟩ E)) ⟨277294094848,383347211⟩ (N (N (N E ⟨277294094976,382617345⟩ E) ⟨277294095104,381889216⟩ (N E ⟨277294095232,381162819⟩ E)) ⟨277294095488,379715198⟩ (N (N E ⟨277294095616,378993966⟩ E) ⟨277294095744,378274445⟩ E))))) ⟨277294095872,377556631⟩ (N (N (N (N (N (N E ⟨277294096384,374702349⟩ E) ⟨277428310144,448341115⟩ (N E ⟨277428310272,447479709⟩ E)) ⟨277428310400,446620372⟩ (N (N E ⟨277428310528,445763097⟩ E) ⟨277428310656,444907878⟩ (N E ⟨277428310784,444054710⟩ E))) ⟨277428310912,443203586⟩ (N (N (N E ⟨277428311040,442354500⟩ E) ⟨277428311168,441507447⟩ (N E ⟨277428311296,440662421⟩ E)) ⟨277428311424,439819416⟩ (N (N E ⟨277428311552,438978426⟩ E) ⟨277428311680,438139446⟩ E))) ⟨277428311808,437302469⟩ (N (N (N (N E ⟨277428311936,436467490⟩ E) ⟨277428312064,435634504⟩ (N E ⟨277428312192,434803504⟩ E)) ⟨277428312320,433974485⟩ (N (N E ⟨277428312448,433147441⟩ E) ⟨277428312704,431499256⟩ E)) ⟨277428312832,430678103⟩ (N (N (N E ⟨277428313216,428226340⟩ E) ⟨277428313728,424984402⟩ (N E ⟨277428314112,422573066⟩ E)) ⟨277562528128,500166040⟩ (N (N E ⟨277562528256,499205985⟩ E) ⟨277562528512,497292778⟩ E)))) ⟨277562528640,496339612⟩ (N (N (N (N (N E ⟨277562528768,495388729⟩ E) ⟨277562528896,494440122⟩ (N E ⟨277562529024,493493786⟩ E)) ⟨277562529280,491607895⟩ (N (N E ⟨277562529408,490668329⟩ E) ⟨277562529536,489731006⟩ (N E ⟨277562529664,488795921⟩ E))) ⟨277562529792,487863067⟩ (N (N (N E ⟨277562530048,486004027⟩ E) ⟨277562530176,485077828⟩ (N E ⟨277562530560,482312440⟩ E)) ⟨277562530688,481395026⟩ (N (N E ⟨277562530816,480479793⟩ E) ⟨277562531072,478655842⟩ E))) ⟨277562531200,477747113⟩ (N (N (N (N E ⟨277562531712,474133694⟩ E) ⟨277562531840,473235683⟩ (N E ⟨277696746112,554504399⟩ E)) ⟨277696746240,553441065⟩ (N (N E ⟨277696746368,552380279⟩ E) ⟨277696746496,551322034⟩ E)) ⟨277696746752,549213136⟩ (N (N (N E ⟨277696746880,548162469⟩ E) ⟨277696747136,546068663⟩ (N E ⟨277696747264,545025509⟩ E)) ⟨277696747520,542946665⟩ (N (N E ⟨277696747648,541910961⟩ E) ⟨277696747904,539846951⟩ E)))))))

noncomputable def tab30 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨277696748160,537792759⟩ E) ⟨277696748288,536769328⟩ (N E ⟨277696748416,535748331⟩ E)) ⟨277696748544,534729760⟩ (N (N E ⟨277696749056,530679608⟩ E) ⟨277696749184,529673068⟩ (N E ⟨277696749312,528668913⟩ E))) ⟨277696749568,526667734⟩ (N (N (N E ⟨277830964352,608960770⟩ E) ⟨277830964480,607795246⟩ (N E ⟨277830964736,605472552⟩ E)) ⟨277830965120,602009277⟩ (N (N E ⟨277830965248,600860359⟩ E) ⟨277830965632,597430011⟩ E))) ⟨277830965760,596292006⟩ (N (N (N (N E ⟨277830965888,595156709⟩ E) ⟨277830966400,590642454⟩ (N E ⟨277830966528,589520585⟩ E)) ⟨277830966784,587284829⟩ (N (N E ⟨277830966912,586170926⟩ E) ⟨277830967040,585059662⟩ (N E ⟨277830967296,582845026⟩ E))) ⟨277965182592,665381580⟩ (N (N (N E ⟨277965182848,662842461⟩ E) ⟨277965182976,661577444⟩ (N E ⟨277965183104,660315443⟩ E)) ⟨277965183360,657800459⟩ (N (N E ⟨277965183488,656547457⟩ E) ⟨277965183616,655297438⟩ E)))) ⟨277965183872,652806314⟩ (N (N (N (N (N E ⟨277965184128,650327017⟩ E) ⟨277965184384,647859482⟩ (N E ⟨277965184512,646630103⟩ E)) ⟨277965184896,642959425⟩ (N (N E ⟨277965185024,641741658⟩ E) ⟨278099400832,723686349⟩ (N E ⟨278099401600,715456563⟩ E))) ⟨278099401984,711385547⟩ (N (N (N E ⟨278099402112,710034980⟩ E) ⟨278099402752,703330025⟩ (N E ⟨278233619456,779330669⟩ E)) ⟨278233620480,767580838⟩ (N (N E ⟨278367836160,860255808⟩ E) ⟨278367836544,855344556⟩ E))) ⟨278367837696,840819631⟩ (N (N (N (N E ⟨278367838208,834463136⟩ E) ⟨278502054528,923038699⟩ (N E ⟨278502055040,916037465⟩ E)) ⟨278502055936,903944301⟩ (N (N E ⟨278636273536,977842113⟩ E) ⟨278636273664,975990077⟩ E)) ⟨278770491392,1050564584⟩ (N (N (N E ⟨278904709120,1127630341⟩ E) ⟨279038926848,1207148283⟩ (N E ⟨279173144576,1289077782⟩ E)) ⟨279307362304,1373376670⟩ (N (N E ⟨279441580032,1460001260⟩ E) ⟨279710015488,1640045351⟩ E))))) ⟨279844233216,1733370107⟩ (N (N (N (N (N (N E ⟨279978450944,1828831124⟩ E) ⟨280112668672,1926377499⟩ (N E ⟨280246886400,2025956968⟩ E)) ⟨280515321856,2230999488⟩ (N (N E ⟨280649539584,2336351466⟩ E) ⟨280917975040,2552429823⟩ (N E ⟨281052192768,2663037788⟩ E))) ⟨281186410496,2775277410⟩ (N (N (N E ⟨281589063680,3121160506⟩ E) ⟨282662805504,4099142367⟩ (N E ⟨283468112000,4859954717⟩ E)) ⟨283468112128,4850758660⟩ (N (N E ⟨283468112256,4841584346⟩ E) ⟨283468112384,4832431715⟩ E))) ⟨283468112512,4823300705⟩ (N (N (N (N E ⟨283468112640,4814191254⟩ E) ⟨283468112768,4805103302⟩ (N E ⟨283468112896,4796036788⟩ E)) ⟨283468113024,4786991651⟩ (N (N E ⟨283468113152,4777967830⟩ E) ⟨283468113280,4768965266⟩ E)) ⟨283468113408,4759983897⟩ (N (N (N E ⟨283468113536,4751023666⟩ E) ⟨283468113664,4742084510⟩ (N E ⟨283468113792,4733166372⟩ E)) ⟨283468113920,4724269192⟩ (N (N E ⟨283468114048,4715392911⟩ E) ⟨283468114176,4706537470⟩ E)))) ⟨283468114304,4697702810⟩ (N (N (N (N (N E ⟨283468114432,4688888873⟩ E) ⟨283468114560,4680095600⟩ (N E ⟨283468114688,4671322934⟩ E)) ⟨283468114816,4662570816⟩ (N (N E ⟨283468114944,4653839189⟩ E) ⟨283468115072,4645127994⟩ (N E ⟨283468115200,4636437176⟩ E))) ⟨283468115328,4627766676⟩ (N (N (N E ⟨283468115456,4619116438⟩ E) ⟨283468115584,4610486405⟩ (N E ⟨283468115712,4601876519⟩ E)) ⟨283468115840,4593286726⟩ (N (N E ⟨283468115968,4584716968⟩ E) ⟨283468116096,4576167189⟩ E))) ⟨283468116224,4567637334⟩ (N (N (N (N E ⟨283468116352,4559127347⟩ E) ⟨283468116480,4550637173⟩ (N E ⟨283468116608,4542166755⟩ E)) ⟨283468116736,4533716039⟩ (N (N E ⟨283468116864,4525284970⟩ E) ⟨283468116992,4516873494⟩ E)) ⟨283468117120,4508481554⟩ (N (N (N E ⟨283468117248,4500109098⟩ E) ⟨283468117376,4491756071⟩ (N E ⟨283468117504,4483422418⟩ E)) ⟨283468117632,4475108086⟩ (N (N E ⟨283468117760,4466813021⟩ E) ⟨283468117888,4458537170⟩ E)))))) ⟨283468118016,4450280479⟩ (N (N (N (N (N (N (N E ⟨283468118144,4442042895⟩ E) ⟨283468118272,4433824364⟩ (N E ⟨283468118400,4425624835⟩ E)) ⟨283468118528,4417444254⟩ (N (N E ⟨283468118656,4409282568⟩ E) ⟨283468118784,4401139726⟩ (N E ⟨283468118912,4393015675⟩ E))) ⟨283468119296,4368755751⟩ (N (N (N E ⟨283468119424,4360706347⟩ E) ⟨283468119552,4352675475⟩ (N E ⟨283468119680,4344663085⟩ E)) ⟨283468119808,4336669126⟩ (N (N E ⟨283468119936,4328693546⟩ E) ⟨283468120064,4320736295⟩ E))) ⟨284407644160,5132317230⟩ (N (N (N (N E ⟨292058054784,9597161408⟩ E) ⟨292058055168,9522859734⟩ (N E ⟨292058055296,9492506443⟩ E)) ⟨292058055424,9459397479⟩ (N (N E ⟨292058055552,9423557641⟩ E) ⟨292058055680,9385013290⟩ (N E ⟨292058055808,9343792325⟩ E))) ⟨292058055936,9299924162⟩ (N (N (N E ⟨292058056192,9204371355⟩ E) ⟨292058056320,9152752914⟩ (N E ⟨292058056448,9098619634⟩ E)) ⟨292058056576,9042008151⟩ (N (N E ⟨292058056704,8982956468⟩ E) ⟨292058056832,8921503925⟩ E)))) ⟨292058057088,8791560142⟩ (N (N (N (N (N E ⟨292058057216,8723154014⟩ E) ⟨292058057344,8652517190⟩ (N E ⟨292058057472,8579695262⟩ E)) ⟨292058057600,8504734976⟩ (N (N E ⟨292058057728,8427684207⟩ E) ⟨292058057984,8267508144⟩ (N E ⟨292058058112,8184483924⟩ E))) ⟨292058058240,8099571304⟩ (N (N (N E ⟨292058058368,8012823281⟩ E) ⟨292058058496,7924293774⟩ (N E ⟨292058058752,7742110373⟩ E)) ⟨292058058880,7648568596⟩ (N (N E ⟨292058059008,7553469500⟩ E) ⟨292058059136,7456871066⟩ E))) ⟨292058059264,7358831975⟩ (N (N (N (N E ⟨292058059392,7259411574⟩ E) ⟨292058059520,7158669834⟩ (N E ⟨292058059648,7056667314⟩ E)) ⟨292058059904,6849124881⟩ (N (N E ⟨292058060032,6743708678⟩ E) ⟨292058060160,6637279038⟩ E)) ⟨292058060416,6421631471⟩ (N (N (N E ⟨292058060544,6312540405⟩ E) ⟨292058060672,6202689544⟩ (N E ⟨292058060800,6092142989⟩ E)) ⟨292058061184,5756972900⟩ (N (N E ⟨292058061312,5644287947⟩ E) ⟨292058061440,5531229986⟩ E))))) ⟨292058061568,5417863720⟩ (N (N (N (N (N (N E ⟨292058061696,5304253811⟩ E) ⟨292058061824,5190464847⟩ (N E ⟨292058062080,4962607504⟩ E)) ⟨292058062208,4848667580⟩ (N (N E ⟨292058062336,4734805438⟩ E) ⟨292058062464,4621084718⟩ (N E ⟨292058062720,4394320554⟩ E))) ⟨292058062848,4281402733⟩ (N (N (N E ⟨300647997568,4616538007⟩ E) ⟨300647997824,4373868268⟩ (N E ⟨300647997952,4253388679⟩ E)) ⟨300647998080,4133565213⟩ (N (N E ⟨300647998336,3896140731⟩ E) ⟨300647998848,3431921397⟩ E))) ⟨300647998976,3318434746⟩ (N (N (N (N E ⟨300647999360,2985075450⟩ E) ⟨300647999488,2876511055⟩ (N E ⟨300647999616,2769316193⟩ E)) ⟨300648000384,2157834953⟩ (N (N E ⟨300648000768,1874681246⟩ E) ⟨300648001280,1523303918⟩ E)) ⟨300648001664,1280795340⟩ (N (N (N E ⟨300648001792,1204158305⟩ E) ⟨300648001920,1129676516⟩ (N E ⟨300648003072,561020055⟩ E)) ⟨300648003328,460550930⟩ (N (N E ⟨300648003584,369821196⟩ E) ⟨300648003840,288934345⟩ E)))) ⟨300648004480,130241109⟩ (N (N (N (N (N E ⟨300648004992,48310569⟩ E) ⟨300648005504,6282279⟩ (N E ⟨309506378624,84328⟩ E)) ⟨309506379392,83463⟩ (N (N E ⟨309506379904,82893⟩ E) ⟨309506380672,82047⟩ (N E ⟨309506381824,80797⟩ E))) ⟨309506382208,80386⟩ (N (N (N E ⟨309506382976,79571⟩ E) ⟨309506383744,78767⟩ (N E ⟨309506383872,78634⟩ E)) ⟨309640597248,1956293⟩ (N (N E ⟨309640597504,1949598⟩ E) ⟨309640597888,1939609⟩ E))) ⟨309640598272,1929683⟩ (N (N (N (N E ⟨309640599424,1900287⟩ E) ⟨309640599808,1890612⟩ (N E ⟨309640599936,1887401⟩ E)) ⟨309640600192,1880999⟩ (N (N E ⟨309640600576,1871447⟩ E) ⟨309640600832,1865113⟩ E)) ⟨309640601472,1849394⟩ (N (N (N E ⟨309640601600,1846271⟩ E) ⟨309774814336,6351614⟩ (N E ⟨309774815104,6286541⟩ E)) ⟨309774815744,6232949⟩ (N (N E ⟨309774816256,6190487⟩ E) ⟨309774816896,6137916⟩ E)))))))

noncomputable def tab31 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨309774817536,6085902⟩ E) ⟨309774817792,6065251⟩ (N E ⟨309774817920,6054958⟩ E)) ⟨309774818048,6044687⟩ (N (N E ⟨309774818176,6034438⟩ E) ⟨309774818304,6024210⟩ (N E ⟨309774818432,6014005⟩ E))) ⟨309774819200,5953222⟩ (N (N (N E ⟨309774819328,5943166⟩ E) ⟨309909032320,13177874⟩ (N E ⟨309909033216,13020667⟩ E)) ⟨309909033472,12976182⟩ (N (N E ⟨309909033728,12931887⟩ E) ⟨309909034752,12756585⟩ E))) ⟨309909034880,12734882⟩ (N (N (N (N E ⟨309909036032,12541615⟩ E) ⟨309909036544,12456896⟩ (N E ⟨309909037056,12372891⟩ E)) ⟨310043250816,22282377⟩ (N (N E ⟨310043251968,21942206⟩ E) ⟨310043252352,21830261⟩ (N E ⟨310043252608,21756027⟩ E))) ⟨310043252992,21645266⟩ (N (N (N E ⟨310043253248,21571818⟩ E) ⟨310043253376,21535210⟩ (N E ⟨310043253504,21498680⟩ E)) ⟨310043253888,21389554⟩ (N (N E ⟨310043254144,21317188⟩ E) ⟨310043254656,21173372⟩ E)))) ⟨310043254784,21137608⟩ (N (N (N (N (N E ⟨310177468032,34217826⟩ E) ⟨310177468800,33867861⟩ (N E ⟨310177469184,33694556⟩ E)) ⟨310177469312,33637035⟩ (N (N E ⟨310177469696,33465204⟩ E) ⟨310177470848,32956256⟩ (N E ⟨310177471104,32844473⟩ E))) ⟨310177472128,32402054⟩ (N (N (N E ⟨310177472384,32292615⟩ E) ⟨310177472512,32238069⟩ (N E ⟨310311685760,48478453⟩ E)) ⟨310311687168,47574290⟩ (N (N E ⟨310311687552,47331367⟩ E) ⟨310311688960,46453808⟩ E))) ⟨310311689088,46375043⟩ (N (N (N (N E ⟨310311689344,46218012⟩ E) ⟨310311689600,46061645⟩ (N E ⟨310311690112,45750891⟩ E)) ⟨310311690240,45673612⟩ (N (N E ⟨310445903744,64992069⟩ E) ⟨310445904640,64218060⟩ E)) ⟨310445905024,63889871⟩ (N (N (N E ⟨310445905792,63239759⟩ E) ⟨310445906048,63024894⟩ (N E ⟨310445906688,62491712⟩ E)) ⟨310445906944,62280019⟩ (N (N E ⟨310445907072,62174509⟩ E) ⟨310445907328,61964157⟩ E))))) ⟨310445907456,61859315⟩ (N (N (N (N (N (N E ⟨310445907968,61442158⟩ E) ⟨310580121472,84135763⟩ (N E ⟨310580122752,82708908⟩ E)) ⟨310580123264,82146643⟩ (N (N E ⟨310580124544,80761746⟩ E) ⟨310580124928,80351978⟩ (N E ⟨310580125696,79540211⟩ E))) ⟨310714339584,105196360⟩ (N (N (N E ⟨310714340864,103414606⟩ E) ⟨310714341760,102189788⟩ (N E ⟨310714342016,101843176⟩ E)) ⟨310714342784,100812119⟩ (N (N E ⟨310714343168,100301484⟩ E) ⟨310714343296,100131991⟩ E))) ⟨310714343424,99962856⟩ (N (N (N (N E ⟨310848559360,125650720⟩ E) ⟨310848560640,123536852⟩ (N E ⟨310848560896,123119427⟩ E)) ⟨310848561024,122911376⟩ (N (N E ⟨310848561152,122703764⟩ E) ⟨310982776320,152857220⟩ E)) ⟨310982778496,148506769⟩ (N (N (N E ⟨310982778880,147755186⟩ E) ⟨311116994816,179313502⟩ (N E ⟨311116996224,175998681⟩ E)) ⟨311116996608,175107963⟩ (N (N E ⟨311251213440,207192029⟩ E) ⟨311251214336,204751524⟩ E)))) ⟨311385431936,237074339⟩ (N (N (N (N (N E ⟨311385432064,236673892⟩ E) ⟨311519649536,271779243⟩ (N E ⟨311519649792,270861689⟩ E)) ⟨311653867264,308341130⟩ (N (N E ⟨311653867520,307300140⟩ E) ⟨311788085248,345973083⟩ (N E ⟨311922302976,386862971⟩ E))) ⟨312190738432,475216546⟩ (N (N (N E ⟨312324956160,522638312⟩ E) ⟨312459173888,572193205⟩ (N E ⟨312593391616,623856911⟩ E)) ⟨312727609344,677603799⟩ (N (N E ⟨312861827072,733406929⟩ E) ⟨313130262528,851067722⟩ E))) ⟨313264480256,912865110⟩ (N (N (N (N E ⟨313398697984,976598221⟩ E) ⟨313532915712,1042233817⟩ (N E ⟨313667133440,1109737447⟩ E)) ⟨313801351168,1179073469⟩ (N (N E ⟨314069786624,1323094300⟩ E) ⟨314472439808,1551911270⟩ E)) ⟨314875092992,1795074314⟩ (N (N (N E ⟨315277746176,2051385388⟩ E) ⟨315948834816,2504290395⟩ (N E ⟨317827883136,3885544523⟩ E)) ⟨317827883264,3878986917⟩ (N (N E ⟨317827883392,3872443141⟩ E) ⟨317827883520,3865913159⟩ E)))))) ⟨317827883648,3859396938⟩ (N (N (N (N (N (N (N E ⟨317827883776,3852894441⟩ E) ⟨317827883904,3846405636⟩ (N E ⟨317827884032,3839930486⟩ E)) ⟨317827884160,3833468957⟩ (N (N E ⟨317827884288,3827021016⟩ E) ⟨317827884416,3820586627⟩ (N E ⟨317827884544,3814165757⟩ E))) ⟨317827884672,3807758371⟩ (N (N (N E ⟨317827884800,3801364436⟩ E) ⟨317827884928,3794983918⟩ (N E ⟨317827885056,3788616783⟩ E)) ⟨317827885184,3782262996⟩ (N (N E ⟨317827885440,3769595338⟩ E) ⟨317827885568,3763281398⟩ E))) ⟨317827885696,3756980674⟩ (N (N (N (N E ⟨317827885824,3750693133⟩ E) ⟨317827885952,3744418741⟩ (N E ⟨317827886080,3738157464⟩ E)) ⟨317827886208,3731909272⟩ (N (N E ⟨317827886464,3719452006⟩ E) ⟨317827886592,3713242867⟩ E)) ⟨317827886720,3707046681⟩ (N (N (N E ⟨317827886976,3694693037⟩ E) ⟨317827887104,3688535515⟩ (N E ⟨317827887232,3682390817⟩ E)) ⟨317827887360,3676258910⟩ (N (N E ⟨317827887488,3670139764⟩ E) ⟨317827887616,3664033345⟩ E)))) ⟨317827887744,3657939622⟩ (N (N (N (N (N E ⟨317827888000,3645790137⟩ E) ⟨317827888128,3639734313⟩ (N E ⟨317827888384,3627660343⟩ E)) ⟨317827888512,3621642135⟩ (N (N E ⟨317827888896,3603662244⟩ E) ⟨317827889024,3597693755⟩ (N E ⟨317827889152,3591737619⟩ E))) ⟨317827889280,3585793805⟩ (N (N (N E ⟨317827889536,3573943022⟩ E) ⟨317827889920,3556258500⟩ (N E ⟨317827890048,3550387980⟩ E)) ⟨317827890176,3544529570⟩ (N (N E ⟨317827890304,3538683239⟩ E) ⟨317827890432,3532848958⟩ E))) ⟨317827890560,3527026698⟩ (N (N (N (N E ⟨317827890688,3521216428⟩ E) ⟨317827890816,3515418119⟩ (N E ⟨317827891072,3503857266⟩ E)) ⟨317827891200,3498094663⟩ (N (N E ⟨326417826304,7627332364⟩ E) ⟨326417826432,7604489231⟩ E)) ⟨326417826560,7579427709⟩ (N (N (N E ⟨326417826816,7522725195⟩ E) ⟨326417826944,7491125209⟩ (N E ⟨326417827712,7257527540⟩ E)) ⟨326417827968,7163543985⟩ (N (N E ⟨326417828096,7113663517⟩ E) ⟨326417828608,6895656581⟩ E))))) ⟨326417829120,6649794568⟩ (N (N (N (N (N (N E ⟨326417829504,6448605257⟩ E) ⟨326417829632,6378563223⟩ (N E ⟨326417829760,6307103327⟩ E)) ⟨326417829888,6234269622⟩ (N (N E ⟨326417830144,6084660428⟩ E) ⟨326417830272,6007976380⟩ (N E ⟨326417830656,5770967704⟩ E))) ⟨326417831040,5524532023⟩ (N (N (N E ⟨326417831168,5440520342⟩ E) ⟨326417831424,5269996647⟩ (N E ⟨326417831680,5096476453⟩ E)) ⟨326417831936,4920368510⟩ (N (N E ⟨326417833088,4106968594⟩ E) ⟨326417833344,3924048249⟩ E))) ⟨326417833600,3741241715⟩ (N (N (N (N E ⟨326417833856,3558960844⟩ E) ⟨326417833984,3468145225⟩ (N E ⟨335007768960,3507584150⟩ E)) ⟨335007769088,3411384587⟩ (N (N E ⟨335007770880,2139240568⟩ E) ⟨335007771264,1892021380⟩ E)) ⟨335007771520,1733571599⟩ (N (N (N E ⟨335007772032,1433344255⟩ E) ⟨335007772288,1292147533⟩ (N E ⟨335007772928,967282472⟩ E)) ⟨335007775232,173688169⟩ (N (N E ⟨335007775744,83809971⟩ E) ⟨344134590464,5637625⟩ E)))) ⟨344268808192,11227364⟩ (N (N (N (N (N E ⟨344805679104,52667281⟩ E) ⟨344939896832,67788449⟩ (N E ⟨345208332288,103715347⟩ E)) ⟨345342550016,124508209⟩ (N (N E ⟨345476767744,147176846⟩ E) ⟨345745203200,198103059⟩ (N E ⟨346013638656,256405797⟩ E))) ⟨346953162752,516859070⟩ (N (N (N E ⟨347087380480,560987671⟩ E) ⟨347221598208,606783556⟩ (N E ⟨352187659904,2972833296⟩ E)) ⟨352187660672,2946238439⟩ (N (N E ⟨352187661184,2928673646⟩ E) ⟨352187662336,2889629010⟩ E))) ⟨360777597568,6228596035⟩ (N (N (N (N E ⟨360777599104,5878393236⟩ E) ⟨360777600896,5186767810⟩ (N E ⟨360777602432,4412392185⟩ E)) ⟨360777604224,3390784149⟩ (N (N E ⟨360777605120,2866362512⟩ E) ⟨369367540352,2718556366⟩ E)) ⟨369367541376,2111851148⟩ (N (N (N E ⟨369367541888,1825273223⟩ E) ⟨369367543040,1236614491⟩ (N E ⟨369367543680,950077077⟩ E)) ⟨369367544576,605741958⟩ (N (N E ⟨369367544832,520501350⟩ E) ⟨369367547904,877209⟩ E)))))))

noncomputable def table : CTN :=
  (N (N (N (N (N tab0 ⟨70028167392,106064860⟩ tab1) ⟨72175653504,7407861677⟩ (N tab2 ⟨102106234880,317918781⟩ tab3)) ⟨104555713152,343662618⟩ (N (N tab4 ⟨106166325760,3291227234⟩ tab5) ⟨132204590976,2731061067⟩ (N tab6 ⟨138244393984,26969606⟩ tab7))) ⟨139049700736,400121659⟩ (N (N (N tab8 ⟨139855009024,1150906558⟩ tab9) ⟨141062970752,2899443745⟩ (N tab10 ⟨165759055104,2513546008⟩ tab11)) ⟨172604166400,31698230⟩ (N (N tab12 ⟨173275257600,225018430⟩ tab13) ⟨174080564608,689983648⟩ (N tab14 ⟨175154303744,1823157663⟩ tab15)))) ⟨188978743680,20644970417⟩ (N (N (N (N tab16 ⟨206695502080,5224546⟩ tab17) ⟨207366589568,113086853⟩ (N tab18 ⟨208037679104,353455967⟩ tab19)) ⟨208842985600,820831751⟩ (N (N tab20 ⟨211124690944,2900132663⟩ tab21) ⟨240518398208,118725⟩ (N tab22 ⟨241457930112,42656379⟩ tab23))) ⟨242263234048,227351723⟩ (N (N (N tab24 ⟨243068541312,542172161⟩ tab25) ⟨244142283648,1163520846⟩ (N tab26 ⟨275146608128,2898⟩ tab27)) ⟨275817699584,38064368⟩ (N (N tab28 ⟨276623005312,184444763⟩ tab29) ⟨277696748032,538818631⟩ (N tab30 ⟨309774817024,6127469⟩ tab31)))))

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
  (29696, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 442368, false)]

theorem cover0_ok : SixW7.coverCheck table 25326800 (SC / 2) 442368 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
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
  (59904, 74752, false),
  (74752, 75008, true),
  (75008, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 88064, true),
  (88064, 262144, false)]

theorem cover1_ok : SixW7.coverCheck table 48244400 (SC / 2) 262144 cover1 = true := by decide +kernel

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
  (59392, 60416, true),
  (60416, 74240, false),
  (74240, 74496, true),
  (74496, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 88832, true),
  (88832, 89088, true),
  (89088, 237568, false)]

theorem cover2_ok : SixW7.coverCheck table 52857300 (SC / 2) 237568 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
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
  (59904, 74752, false),
  (74752, 75008, true),
  (75008, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 88064, true),
  (88064, 262144, false)]

theorem cover3_ok : SixW7.coverCheck table 48244400 (SC / 2) 262144 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 442368, false)]

theorem cover4_ok : SixW7.coverCheck table 25326800 (SC / 2) 442368 cover4 = true := by decide +kernel

def bits : ℕ := 675589966764565074809173239005366589431324052014226072218935861227108833182929256289958597450162701684373418900020030755375095096072439983197996629923330929746822240898809506874132102425893094769836177917909930110387390128284649520199303330517575679950899770321091953319236221615979719862769247295185466055055579366817156670095136908777642842339924382692748272711709225945112643692052486128945495524301073056431275121064273720970258671383689772080202523265807328736116967594580665082264248018506170796422046105407149061667456633032798768161569192338970110456661694194790375477403074825484213259536220011541575823685315498394014491068061886484962648159471975266881215960424165987977226140624662454443102664805416364055904955641164115010625971885006188880240909096814845184037753664913250353436732261456340593628232664020692696246245403034397237365318681635050215014706135585005913527853386619521085783784037816931168056686075896909621071673994286299547332226547229797529846430574214255123916505429655472685635435815868232334886631694093710227306384814743626461973673248653219000402771489926208983503228112041671828529831493558468774203994983759237546812252270290572293754108247057385050900197629825294440823694457076182586464457627421559560138490414235559821500052226067664938172897716934192442223441797213054273354879919351322363973648686435984858802893991766446366924790754590911062040366137912962653558719141238380640403796037860427902518654470461845666760134586792830300200018446942840243855553585873179776692574615512043648119926092969608307231679593021421252301854699442403627557692571585595292787472429969576356227484904832408848787873807966295115490872418042293936603941309518704462727344633449918096463016857031014412415075688773641008739141431538211880128349335937041489524282283926046106468375524068042550880365402963048397434640101974595002628815145407325147799716002558084050384767115235920460004276465707224533982427316063738125653178557054819992437914923519582811852423252169460607759288565417463240911859600619479697622958575651797382238054136933023918585072361241721056676555121569441165492628531238026257033630448090003557101438706869308868289682208944704907411388058951917501336869297107762942543014534521168515783133198240652429289938645673555552096848328413892737158184902907661955721870324224555600298877636921317831177742717065485591904306888381080509014549022645376270714629448546632033855746941035224889689125561997990933798802430219538142152295066309677228625340475164202433913616005547240803409339162897174644894527093657392549116307390231255328496547169149576126464053579500498584851227937140666190870345652431463746479391499032525133018228792748028343247209721083566143272425845416891644389419250234623992324049257673949737551748122963325791266700756584300399341642616284897155928773903996972048271417810710784452739704404235696159329021935848023048218603882110378019054173756520618114708987402756757138900426526388588136956028734157992786168684864395122972806218210772702363620512810345122560382759552878214379270700003150886762778015223507622849326070863949869231279963512764127817677476571884533641763127021338431722477449783981212206676163372758987528090350523599788124755893294137251051355468461012171737380340886097743902559267314008630266844188995241059618428840419704929738757032121684876146060679269646829184575013424596510259033353698717449913822308601241284410092086722948484312002292850092363575218802343138333763879476351192220015997078562441379715171470499453611934945488429875062522876438186152840033605544173177269066396616004247877563481093425617309784423062245314787902418113465244038701434558501840262204853531057103459613690862539164004876234090580147840926865327691327040442880156125030484333184802099700439014591158556386993742670670434017342544042368011562860693060259887243055059386922691214180769729255190118135728543744964023151422617005643153428417279468450402546107300499627280966533312953031140324853812760265268061460480884373575240712787697466581719156430646880454081592939099312336750718754854885532412266586863138589168988137996534023370016381239480185805696884727141020490641838365972295908838372596268431739624617800169120926363374976715229987945090134138374310927435984458037612377458023323148668131153528058671177528353823100324019990031692957549848362175073434373222654029298017540796847392217732725765104257062545327283877649026069191256759167422403727445519611831655750780129853612546473282434106946602020742350091930745789426262624219047477300773416395800372867467264943077533929538490183325145614145172098502198493574185229239764055816817372718597042917213564801486832315729403169735025735838656562367565487480747969387481177648138876195340671018408119918670604473324533464529360991514735009062236569283152424425343596726586549445282893381306333070281272844781703035816049789884861810519483430517946291346937115615466539413379093611598709389895275723402053763394760117779888548492064396079999371798355702227692401530657254405500482068973287414327720315268957582620946196299487010435393510239905760211147667540392812328398474040790730823446065352586268258177742529564112267888403716637052633394993093972910211174823494260563614870369111146643934906958513399229624977177440184888665354840356519278071631754866787521232346309073007174859003598258349620941663794573996066126532009847765218191723403280434113756250244821622304388753027934034434407243048113564677389944965630892810380810313110540777907452985116985295826631771186366810549132052032031971721089331549864880948703062588862686981510270511445335417573137949620179098747042359459327019129270444819651142092876986815812223145914210007598908310911808280878177686629260728420836123710539646888750603920475166661638702520660391888145867201788266930575523595107118461279264475122358034918057947115166251093430435138828983021048919206825903499041901728015431655915156018480075333158318719570339217533050476283397608521338405749941863499765009995350402285000596000722098308528638260115347394079575596084908684850009111869866295334049252489753189269609096265387047322138775112857717960360582303223899394686295681924109261248593119467705392595801340505952403526939138494016877992137530679702435106211769225789395091309451495517285392923339035405119804622680120800481943144466586723131742901022600297419543731745600919331541197777422923898071613514574341874575443665110751482448080715229976910838057694754204353617713576204545898388869275468745558204746967454512805934474152300099114613707259746551957851190998560937491767637054215936232521496708901713202989657501843001567316026993296241660295007644372787897513848635316962319267553163497461644299368882600190755175067629899776030102010124421828891868928426274762848763982784657937479861197820178988205140171603651650331154377333415406564960825704026019029307752105312684632002903816586506245557263340927440323354385747335102531673026222268328615366688389685152604881181823242706464899271247695648762118608568647235707208130699742440574368102616137646849420952385746285783906062367447086111573742239158480775943964015122537180946696424032677493486742177456605483094944651739291281702891015463213025441878869787491630426647498438983145659506376287659179724473983839472754193866295225440332290907034795836324461307695581051357614820220663001648932220201094811010331779021274524298819460719434104253151140985970232370232704002496818129174679495714333377803854202164680006258976392650780299995213190005987245242249636415023684359098873147302069454633399358438592451167434866844442412956851675068962393114187042590598598715037506613595012623742191297272427404773093093050662299016051804352052986432303887675630658565733350081780229511470468530024381191444599153521151038615972860025068770271448853552963434666050929377599843041856030141893168651758515697518634973014653927864431671378583571951715273656439923136214039654725997790871410017735399323062910801543603913906901707315400884603341793202092045220583422640725222093928138992096566424543355294542066983200946760852782474502832660716555515359661344461443410445316938379973027801101822706301083004204419525221239798268371700776428670187231022150252127376153820078468120524198173663627232885905788229310280733442276906315630888259123865258258922076108138342166313251806647176974550164759789109547105064103182108344116420216634152212159131914812815660785210720156778578282299653655656294878273182821637304263277399230282335304205954166306734137948414834208781871583520890952741064640404114134018742709013891844289919101591924871937819260515769592457134246536429066595337402953555375647419762705923728310232148271713278044581702076950706792793405143485120102079982802201932400021173802974267468329379768808586021626602913838326809363094448154599475611288802550393887548936593201198004738339127367130488367286532308064549144138114321594305016897312079889404991930681777897144516621584495719329288106707083515667346346391978831336568505231240195034491379355532353506083472509225141292060208727893511361964821034791128331970251133765313852179042196225633879092312014437876664823597296037880449595487229445846591211575727753301372054617621532505408694146466503821631171783865815647527412983129954136735155778287872171905872788699569494327087335788618630326803291768054649179269456935132575165403702444086833459911078292366676771327898136225686514284354755696539973722289719515203690585994948610891087414625075482856168299304074276114061537151680329511626385518399487078237556839425959927548791241340581988399101258617628001852930578589571238151788059551398942391702209057050766062452879650465029559911461985570657138291813964314628931586413357637667817288555549902761600115815480931420662268756134457888573074898548655329729477781343785753246453242731093131970774421138479761542907049568262246790963143802116361314155616608111641515050754861684692249537060299008144545998318152429594044563873349100407494233301940823174164744159935062149288000866523136414768186627931001431525450976549018473670568873796235137848754625516414502815793056808536904533820430314587792554738038414397693656016656809082370472870586228542406822604464126583325403262727411935551442348412729424367676696874930762742407786116793680128059205562479732400782476939922572785987980294349282698947204834329001194035231346073053148412740103917094724695988351174625265556802653937653278783690964960801921315674085903275659745802443176536993668898437913365835629052671984332965412871896099160641856145987448128340559079145244191103346159621848141487420092353104241694951471915510526401856581313420274509015263766307976258230265550530302741649169203734806998288827666129474382053382152978914713598632512382084744595807384407988271619394813033896789952373216637719596522474743547314081269324048180916657746375686209209873151359334908841527226329395977034602800617360609723930127122288846643656974141090364625335257052872066864287022668409511669089847887748554153225296742419510759102102481336725720940972247769433081581074436898787249115751195727701022825220380841607920665372837888041822791235375042833239020967681773878537010680064846879985218531472604703114555612128285093561842950052654632954218918375362120948047933564270536691316640852371905515342703570001412894465956669273510013675638260503477931603239138623517439505536716598835403704140347575202617067103352528343761482704349013912981535095483791689384378542606340322731439899768056624292779402806457989256886287924393377841888044752387183420205719438550175822134277401021730558765600929173011401169666853764672803933667318666126538117407580289318637602397808673806130502261056858161479408783188115830326070603139702466662158125205907033395899411328815344545482381841506852481459140705660695658357037052585013916235466856631072778765101298942860492553538476250770738101866254652163455786559188113693663312168389658516822478849240246197710244503108748843511684048063367164190894262719777393757847663582423362687230531481452849483672898672606311462462199346330098070488246265573530746034760605973174434881065871762620270952879652148903807269022292278339916455830650909387327694486472715661047943728878208569939706245802534273977006169995492953006285015910032254204202401605703561875240495322494864385339165019725165005310235666983966755350058071148097693548523226895564845750330517365938052124184327329581324899141106386499340349483457934258152331625626165640956012684150895627990151598609915002729018034517800102964290540872484893992834417539610813914666759506472855386048351776827910953063008279396964878805738305829238709270205246024757897089342034051576530779185601716582044559596151422745032989739617580258162399842825924225344851904284064583370565961946359137333103161600557066128545810307716334630161216607297575961936145765040879650460347286524914127690545431737181622665095134484887438295013954895276954098940156086207988010449111267101610294679595312075811052708482179127352697126945856721339473644874384661763288768427254912900819919177847407379777489748177951594839710069945865816360835454204048094898351260617659476984426826207955549734437135917765761354751005774947997682077965670220317050555521065551625008264790438884564334114943476201035387934140725312637927780917744683525221174488512930055559196455248221005037192707447196739870337387517720007204883936272425685498061186553758943809514338470035099392722404843095347511508897757801312457602190830505669087158834183333341198402183745198422503559127353654858026781798382939747940015907391437256820596781559096657803605375648250815532462604138952841775514070494638506242493216342767706796840771190361350465813941827485983298035440212155135811246344386507366460482483421001920897673214146402007663029337223566176073739322845291362233038036872452747141849394619799614836726830676546833784227195747148908962330037652824574278157850894927407852357125644598231187615140728041834398621544089368186485578566221637339804141289969663097735546005399110404938311010056996072618628410686998380627578277033186843810414310875039214375995232428524289035724535017768480260632618897030146851686016079469335810266585052443364152764400144001678745181180495823289540891306173254728090897840494522847184527653698358962297235549576240672875514176153597602811506234446556512879961049139068577517180915334651719469554542621235402787700524373515144059346825795017131564199425513236800213875870323948422626533226072405743415220099773739959907901302837744573168042398185557020010171110457237754092732644292533520843531677132066683554506916549936209511927168574337511593037282651759926703205152346301889000105403302027466368982115304182193511773262140128898062637788804735245648997502730465305825610007527868812643657654495406946018227433320023228866800725397660389972030666571891098072379591173920684064984157665308405441679248617676603165813462552432533483361667324785861670925056062501397904509921488116287191088827592640296797912063287755714968801781120665184631917355572127748377644116593520795135066195294137053328279970121522202035393458668565678811086301220318731121020534117129811368410913852424308989079859768084854871884355160145614070379118997269519794584528471016614313439818913370271322112755040094233443559191871464843358442039609682101716536427323003780366635030221962727341435349037489148461166024020694450030435341231477011032229032065321336011423270798345225407141603222963262019624286172528023708733108421744108823834240945016358672794989403046009299337256076997933666012214822527610143301243298658884988358120195699402055912741712557920490137317058439259871379083742607725163007635855505967995352063982782672331803851881713336816806563636416604804201670106299387330264040178344301819438470443373582730908616400727817467206498856944287392878363681945316788207181109771386129731507787372979456826987793472645103870896748712369516489463220153955889521198155371003839805282563128665065340999246158289280770179385026655883430104809248334791034155966821201062449588315523852070172468563192947271150792769339698342282039167639972522831068596290135413369875551762918313220408553096465802525081441126093935909584953566880187105623008518475991092266095772046271272981739204237051761759750213292522087663204935257240840940880932815963754543231905712736497936577523440448868070542387414376919447373287353068728658554113956401510314227274897266275392370430270620978995648778047177161596738388305288464784116164693199007027960502382575381420385429364213357651301241986504299018460101951800587255803913849604879152652095981321590042668217696816422868073104508709856558574483503936987651352914258072145274005239699163201485366319623451240410159654464786699095997976424678419743509794819690552671220518936240177417910854582439347164219232335034346816372624475286867169269704104248642217266352044640194106307555485261330162102493068534922257920293436603734709607213483017077262581940182041820593326513266452453150666974589736392991077928272840628223873587787776160545837286063066149288760818808351714316206520104490870854626913907335938163610228967757903111988515821129423849493365498613153481726558965813851984675028158902651861711421897090740428555765350729821856278172998089598464181821676331698095580371538024088371663749164765803383902506853839072666002526406676657987627364322328252847508539660416992693226345947654701718344625507556117616493867783277169116975498475295484257987917479349230052213994873570936654469067587739011498854758864207982269244128793506602343013389467033311226664941390193714845400485600525807049696345892482850709665822263889299808547073952415425881278376729742805800502086898770300979066680423024815477532524339822819468714451685217282307053815106581055489907030309655158883669191622632104935273602002933507643452501269543458421537054259539549040445011466981329097623721223538602972890170028370520120968572498375385982629085590733206097138909780147876936460162443849756675579507156965166164170837813459603406327111935451312598531877635302897770984354608115242572558524244021371388232023350126241212049844568168212664535683367006277572337924971612613448140133616359595265037907991307415708568426164012728839600098917854093227137571406026667210212954700364532839089097411847514605279732934246245058153413938110856854812197106698093789826724422971998042114202839195259600325538347550789595524081528698692311060163681417308829056062104533067592980411596915344480875016146299573461374193797344253951860802079624018359884586687376310923969098588242225780927868191029511080841369168102101502387457852775206967186826692047635191076146092399637495888437686214531811113454777924885025020339693500500015659526616167799699193692201493205217665929065722559518880375255677913494769160906002535878221369023247479031802532489522890722192748223114789421388277005815201955679025020456997010352301746792088812817043296541962924267018547330540310087433884572628551540733586558603702867407526776549691317050726687575954118402617047776474890392058215587217263641255791992828065536875884195226906722185825923480076603430739338989873846865246734085063061289719897307883923859015063294695240249364978711789072431542935486887830237628861408211443538262314901790100379786639964891317155484882308241293771511858023077010240752899398221662620216321734694598677259028837300964509737459178115197096600561372924847141294556731208341208345135024536159333214240519661327250389992740978396316987075627848967993623000067824467253597917999353198527607908544696393638155690502572296081294235942893618853080200844922232805339983329374331834314069743196464114647929736187473412059888652677339283664229469693015087252419275258205309157997421316526979171964116334132496173329777572942933508944501869654613157119028709236973656706728291412577446305128170246572351431279343781669469714114862609389426160435562620374393585010025616824179953438188983995967814837585977974573531799600762290937114621322340275163088903947469833959929128768334844158377674219109190209384726091631080801816300678843389474040864933704267464749547306385647752386499446549427090298894383265138508405394017090296613574915658005770622771747422666652272478200758409844522519572366960487983387942893491227566923752045106735373001767136165233638554772447202702289284250611236804034785797950247338853299222964636606734830438609440595022350343032710426420153781308825629833175059811847030971072815964386076048927679167607616949097821829445827313223018376106719436272988960993160576174709187641414071934908844329336914070387193158374422906823687904174452157576377696335946984755068484849260252735061291838017962309289394508323478681951348875952627524086024088985340485735359515864461614973428619543866219834723562633205662332559648415481296781086246020677591055850400137205103738848119473842964455978566400716120812718752256352526709618379351055298724855503052463768156261897916393297976913233070885585103966822379282625249718204700971342119398255215992149625204942167290462571616481238589762921581168078949961544714574994892412804411194656011140262980524635819685556606175504343755687765678529693180349853486631281783234485472319375457378740302541398181953023641820920089970507799015742913981841571307681932400493891629705650746440834674826000010298034611503737226455362176823434097888926083760206887073041833492128337295826348602170749095052346110355497852515555466283125103469927565000164656143758185163807287895534793195323409103230367247792191043436013438410969472511242722671555168519338615367044137308921138660964949579897326191930571811925720581506818884488413267544794585460151947781614650357327449094842591641500821322702885715867858087202582790172146236977835235529980614050729429206356582435780315611139844651925428365192184532701083930557004132627867691733798431223444189933463443159177152566646344850918904577833274487906682175641199020005696765246881111653802019689583763366319995514477171722008844090452998170778259008643634625317624718238826932394607039589104299197107970267360614196040501544349289728049272291442186387247232843568365289181864601870334154672376411763300552735870589882061259462373462871208936869663422811254882764036279313438837778825591550801806116629868577864671723709079741983490000976955880016876783951619477895397076361434237741656494855219739932226057943909783381129341400358454920360753365791569239146661766268894670892239258383476208505830124245460817946084932250508140409554020887612725038973477320067113670309635056744427372202933155923666783460154935979319309453771152017838805454045850560565846137346799272028117653708532295811885426238692873343758911730652974090967193909593708083239575215665629764412431831467198960243936558061986264989513164069293111718924311612099192914026937249704097898394628218420754299326336379021827419968426179878827375703826078454061071735521349626647638930133407272730109953602950001344704872136033422966577358478199315628963781444082398334238016367597373531625773320257788267829664374162893438072764811303121451303810837618169548657117150479739138033970209434284175990917603025436570572255381558079916863391513390305379488718927288905836567290645744434708931042587325030196962934378786602704798231783867196214311812653613894981037988729868669250895040261350606547739512403987303299879744824120296848071198854799191081858232286633230313486235122792265776014032462688453080047669994832918107842594329074214891620487986286748103678970418227188214265596278989982812937078826050164398177402468148888584825437903300822758516869823751240216823214878798399174562948556716281811683895558310174395787263376526436070790455012255088903677092173317522628937993313703702240972182228221775532711683299304808468030564693023028797378518625653120464605593570649452899193317828375798224600956638713611229203268091178058372424008994184846289595423915668808853734585319186759992256988822830584735735688773552209094575856572155412352225265645179592757566927228789938409863919834646388749714410578644092679734831719258829244003279080087498294815614820084446831816765486748320605029350098959025789015431517796076609330924661248114940619852110556704689476362050115716387720774329206167495402018732464672442652945769907885037132297089413991776578340345416983155303656666999210301673509178111527625470254328692928353507320526056380680978645619286657049162840550624525270282516177080394729651973049376403718333719620886635682077384222238872719206021650445213276711415081535430213622866344349263424598543889023576484210920521775039171966924984014349953880519179988918636329432618671641232400273659044185437165843813415681965292782156836227267657464258530262153612333777998032599663753079643916237607905828326360030603021974026630405827555625539112256959112332888700045505492563730363928178454383091224688437838636977540609317864714960915637257168952768981645617559020383361410322039200287449191143756313528114426164990824458458373053556235961112250294864962367952003468998881603009296766531726808743773256218057157313539645811858805785615784727623465929890582874371757471722950324305186220739261375201208886172579988151042485574880539204360688023381528350358983414191011775724793650359175665491572520966585226391371304846993976444488232068501678431887807993768297346131284406232563831218914562755290685980253856798121784658359912136457124962348056161804285629172569102303233927298459466226020959166932772675509360697323666041545919109106352139728441478880191902347818964698938331422394898158166145149300158660680702939434189219243033323512796225553142203682908080427073205137615895489526980449539623532727869247281898153014108120239280466108569156595744099015059516725995400978277627576757397509056098599063574516002497596454419764078442412375834179392506342550460085555078723315232637016828437658415077101251727999520851838237485662821345770202832741518715677159820884720345539088550375829391693422294292917200109937366386408872273778026538046075635590760775028783303926852253494762722308632446934823817239829045745833784748568586126638118921585152618637960386678705754298463401318844098530206111496817222380434872328973088503318721934150271936475824307464244609813667499540487365058043200550073147906116754354422494331923988318905858709468013285348890199164504369089751775085016850846668329880492244098275903720808735380028360631604794552199088601492146292291406876652519686259834947846995079018937409308911983367214392109728319974788166827658788429576569990485818858663933668742864523518651076468945541794514159526296026625899989844952456823888041595519151441627755559794789189455135311864601067683713470783766894130427450208311971412012773740719855473819508050447159686978121119366624321189293318782859338471496986922676728207670904391293756274115474294191216254262255921885272830867834681145795711608734808027614815023582601616754047804651710161159962220165934537501168918185420099537468897913799142085611518667414881179055139625286303199804314608173610910867673528879503084703605677362058046009258252295009760608115747719301184767693740119595146692664708759683157688363972589556892932746852324972103992436027707398662182575729900595765813218883897012786995452636660399414048455783286418784354694608091082987414983846442611002365328975760995238220467586099802646052566323152336526412224239704847497654863417908744727790117078879649378680766917731935146543413120488254918341155270526748320709155965203276629021502813682490386873526762754036480657508167124151748042228750426620560526659141540792113553790862902593451111900507823615904072182753931787678049049441805503841084590040501222256505816854210911369212289386036944525475406845206525820909945585117052559376641986427426871948836169229811734869211902301463329178272085923924908059754943470968349413518597936322587964817937700605410322173559151925979311432877686679512882677861240275752165914222846167879800660744368077232534285505560029105784852522432853324357345133749743091803808741425580192049611403052431641871948493548600582335507787524259295367773314967726913799422648198496382585573758702036524380051015775379768049890205651486512156668826898637072881981301065665588506145762226577277720855078235790278323126268385193318938099923255103954706805418136179364886143888161636135663630606563798723636463690107158339431194520273529800893536438247377177557608636845075202173312891050375339548068042398242407470807626176002968970661334848489832084390335159561503427825662354951859102553283373478804408640925216204016846145435069111947453726825243393113031629318315764788408054330533250278627195118563804476035569403618827893811370214789720495223439623093759468043357429415157164567856041892638444880121583193374491088798045786175589954861630186451987915529547718479845438246412606174730435494086370970278679164294467594203629538584931591186069729792371252712057182281125415680003528161231414007888526810335394157263365574263514187702776867524437426640980979334777847766385126394441612229331694316341272554428890476764292080765780092699670492849859011054603186158001265822000587796002257722876674577145757522638082538054258719308322546836282287679060475639302912281946960150400425287042599349184241963688526416108234778862136431838673259826807846212002694790834169117877467253958921136788582452548729531047850863664087767056355824367065697807506731177700740681438604499284842805934963202607974479146451494454494796669072568459867944323225929816289937667634101889321673913559458243735450600405632989777445133152993981753058975026383264173938834237832711939907413669595384797101960002297109128370930129755060691011345550014567168935172542775199146463114900831715379926178904712280188379473893145578686360679844748676480066474262681217477829025751455480057286155907052065712437648445827541153993884963020793024415359808202030010628564224949982101096034694485549147866604013703731515195954720365983255109643102112139141080918057964001851615749571394509135745350702713231966386713479169912774242159740598556368959333792431507803704875473750649166057890006192387006772005004177123346422342229665428003546834037644501248162301578131290962390014892227176717699356367150252584086656643420734448351166268675024748776328519750701920007155601145577271619321744676503969828166746261829691546513095862698387782664418117340825656935895004602429899517963630979912763463286531680286901696886769854782075642155027391697712075990685802941945580980099293113932678755387852627877424437544546160224608908303886501348949567926924464138365315949325802244212531936555515075525814068069302488350367891577767970277089772250014751397506134313698586642826034088438014296381387238527428465402615370507557777060637771368271883693882462273318013266580746418616604432364474035195750871779005840644567160566582671948996780358835443376268202779264228968244541233262176491762884020912695901489304969267886864539654940318292608024694763303551738720361948118358648350441219777169249416341847045690108527462960925842124791244241353149763322046473708442130933645269866879658309408031362685708484401833962234150548445770356311271273903909841666145144157491840248840912426940435797935764129683217985299438659167004742749151724254358653687365886304943847548378622743243240673207892055668206768720800419971398468835643659888357626956002295035273952377668444483361168433409921120381788748134369630876064598841866066966902695468985181897542277190616310446428062528717027638196901654949537762999247947117895930866233881337612256205197130543971350462470640045744005008454360371841985800789898734079710383311951825323410111553100536535593184654196475026407766039160136551820213067850846796503254583037498662416039160794892843036952433397620626094446408974895782771425448329920113708739659684919457384809770884075034370324145229446738618713842933255038511632640285971349156547899888669026700571595371610118559090070321041944790294023346110079791526579795506966249943361074819595719320204302423074222159615818936722357924159169234960159761143300694766620377227413403071291404156317171164882902544445111429968093496660423941893081099037825979547479550821762363568612954428181747289153113735387185446409251174223083363544426208418769902460796592722341342053218942873853244333896454596770932588493718585736897094121284746420481359521638427657889977140094857413303320969859772094337045119096363865385280573896871196147790137360457951921132267275417311792713165244264817587108814176722262523394476775601977342441159002247389030869492325755201800949648469017769705354390057570360079665167313432573763463173970766911336023572024807434671616793606789810469708601780482023944073014536235963054582252203422649405920375716551408290988220325851498913745726204674297953570842565944796129722122961881193080658451778985408784451022054522768084138630831516336128945298954970783907272395259220279929031711701299282736033226954004359175467064818819903411637129589012223296916056361555076124455136994531792658452519825659300625905882440639648053011941208413821717075838950006618060343865546018270568052640049171198067824393013599133789061101087760437877931151356840070328505089340207941037923754896379726503761901563725803974163640172551007949142889540272961025672581782436882895564523291844737943072068994428600843683591450689876964468796373719310021381303246680324751143433768703476666505414746954557449613120635828701373764639368704352847908864878540779741908897193639673847567337453895074370734894912319955762500525762187980936367476615395009372683863702251958150893921504792879037152224508853757799768936125215725998119616683902067426681882262949921272029841451009410372066262381301509240069332251808816773859238940547516282722634475014376826469191656488438598426925858028501976352433275690429388723752759974571214786106125260148490705125240769256098189385557370291644069278785190035080590684657868659180215068775329324085407203706550713943845558453818362348231699633489231189112477032678289975097176277866224163543388165142666844810197595660189922659026702610199709912049793219099281839691901131021818733223807358535890893268600899499460182664766568269805468102795447859553547379215346154592442833270861207692118228647688801736212752108368240793685893723545747635337941441170832818743748565544035605052538893974008159526314331707620450648833577903604272907185905965549945325897043497074788134067288574789983383765665213426254480405791441849557047604231187494552097238093455178213431654187382581672950704126536135084243154542798962891072912356624203663783479767074748925602137430908878555461467979918744773702690582026750280748806523923682908981135360417541479182888463489391378026777035500586473066385967618073318114252132634365986786528731895313728377836554617821458071495980684555886131813065220167543105746116158330428251168139688553188181472316173477584812669799834477982276045086019433949502072810025294280349413355420944681636501925240856540012766863947065901719705437805594213993010653013527071775069475754689797286678711917026462353973647470675596777514820500168280850314126265234985282797544422759458649689695938567072836302372505008564233300419804626358081431058914761541864789754783708966254336311102457127956752981149499329317347835774353405143109464841717134424513752404457062393774607137368423043094740395170654303423703328724339795169701278286137959766385005064015831705023107803467718479540680009145761480805713260271519972056023546750345381621930004146244113868562397089377595951780113

noncomputable def bx0 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 31744 38400 30720 40448)

theorem wk0 : SixW7.walk table bits 64 0 bx0 = some 1431 := by decide +kernel

noncomputable def bx1 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 31744 38400 57344 442368)

theorem wk1 : SixW7.walk table bits 64 1431 bx1 = some 5407 := by decide +kernel

noncomputable def bx2 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 59904 74752 30720 40448)

theorem wk2 : SixW7.walk table bits 64 5407 bx2 = some 9188 := by decide +kernel

noncomputable def bx3 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 59904 74752 57344 442368)

theorem wk3 : SixW7.walk table bits 64 9188 bx3 = some 13399 := by decide +kernel

noncomputable def bx4 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 88064 262144 30720 40448)

theorem wk4 : SixW7.walk table bits 64 13399 bx4 = some 14830 := by decide +kernel

noncomputable def bx5 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 31744 38400 88064 262144 57344 442368)

theorem wk5 : SixW7.walk table bits 64 14830 bx5 = some 15791 := by decide +kernel

noncomputable def bx6 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 31744 38400 30720 40448)

theorem wk6 : SixW7.walk table bits 64 15791 bx6 = some 20022 := by decide +kernel

noncomputable def bx7 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 31744 38400 57344 442368)

noncomputable def bx8 : SixW7.Box := (bx7).setHi (SixW7.axOf bits 20022) (SixW7.Box.mid bx7 (SixW7.axOf bits 20022))

noncomputable def bx9 : SixW7.Box := (bx8).setHi (SixW7.axOf bits 20026) (SixW7.Box.mid bx8 (SixW7.axOf bits 20026))

noncomputable def bx10 : SixW7.Box := (bx9).setHi (SixW7.axOf bits 20030) (SixW7.Box.mid bx9 (SixW7.axOf bits 20030))

noncomputable def bx11 : SixW7.Box := (bx10).setHi (SixW7.axOf bits 20034) (SixW7.Box.mid bx10 (SixW7.axOf bits 20034))

noncomputable def bx12 : SixW7.Box := (bx11).setHi (SixW7.axOf bits 20038) (SixW7.Box.mid bx11 (SixW7.axOf bits 20038))

noncomputable def bx13 : SixW7.Box := (bx12).setHi (SixW7.axOf bits 20042) (SixW7.Box.mid bx12 (SixW7.axOf bits 20042))

theorem wk13 : SixW7.walk table bits 58 20046 bx13 = some 20362 := by decide +kernel

noncomputable def bx14 : SixW7.Box := (bx12).setLo (SixW7.axOf bits 20042) (SixW7.Box.mid bx12 (SixW7.axOf bits 20042))

theorem wk14 : SixW7.walk table bits 58 20362 bx14 = some 25358 := by decide +kernel

theorem wk12 : SixW7.walk table bits 59 20042 bx12 = some 25358 :=
  SixW7.walk_split table bits 58 20042 bx12 20362 25358 (by decide +kernel) wk13 wk14

noncomputable def bx15 : SixW7.Box := (bx11).setLo (SixW7.axOf bits 20038) (SixW7.Box.mid bx11 (SixW7.axOf bits 20038))

theorem wk15 : SixW7.walk table bits 59 25358 bx15 = some 25394 := by decide +kernel

theorem wk11 : SixW7.walk table bits 60 20038 bx11 = some 25394 :=
  SixW7.walk_split table bits 59 20038 bx11 25358 25394 (by decide +kernel) wk12 wk15

noncomputable def bx16 : SixW7.Box := (bx10).setLo (SixW7.axOf bits 20034) (SixW7.Box.mid bx10 (SixW7.axOf bits 20034))

theorem wk16 : SixW7.walk table bits 60 25394 bx16 = some 26640 := by decide +kernel

theorem wk10 : SixW7.walk table bits 61 20034 bx10 = some 26640 :=
  SixW7.walk_split table bits 60 20034 bx10 25394 26640 (by decide +kernel) wk11 wk16

noncomputable def bx17 : SixW7.Box := (bx9).setLo (SixW7.axOf bits 20030) (SixW7.Box.mid bx9 (SixW7.axOf bits 20030))

theorem wk17 : SixW7.walk table bits 61 26640 bx17 = some 27181 := by decide +kernel

theorem wk9 : SixW7.walk table bits 62 20030 bx9 = some 27181 :=
  SixW7.walk_split table bits 61 20030 bx9 26640 27181 (by decide +kernel) wk10 wk17

noncomputable def bx18 : SixW7.Box := (bx8).setLo (SixW7.axOf bits 20026) (SixW7.Box.mid bx8 (SixW7.axOf bits 20026))

theorem wk18 : SixW7.walk table bits 62 27181 bx18 = some 27342 := by decide +kernel

theorem wk8 : SixW7.walk table bits 63 20026 bx8 = some 27342 :=
  SixW7.walk_split table bits 62 20026 bx8 27181 27342 (by decide +kernel) wk9 wk18

noncomputable def bx19 : SixW7.Box := (bx7).setLo (SixW7.axOf bits 20022) (SixW7.Box.mid bx7 (SixW7.axOf bits 20022))

theorem wk19 : SixW7.walk table bits 63 27342 bx19 = some 27343 := by decide +kernel

theorem wk7 : SixW7.walk table bits 64 20022 bx7 = some 27343 :=
  SixW7.walk_split table bits 63 20022 bx7 27342 27343 (by decide +kernel) wk8 wk19

noncomputable def bx20 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 59904 74752 30720 40448)

theorem wk20 : SixW7.walk table bits 64 27343 bx20 = some 30879 := by decide +kernel

noncomputable def bx21 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 59904 74752 57344 442368)

theorem wk21 : SixW7.walk table bits 64 30879 bx21 = some 32420 := by decide +kernel

noncomputable def bx22 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 88064 262144 30720 40448)

theorem wk22 : SixW7.walk table bits 64 32420 bx22 = some 32796 := by decide +kernel

noncomputable def bx23 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 60416 74240 88064 262144 57344 442368)

theorem wk23 : SixW7.walk table bits 64 32796 bx23 = some 32952 := by decide +kernel

noncomputable def bx24 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 31744 38400 30720 40448)

theorem wk24 : SixW7.walk table bits 64 32952 bx24 = some 34388 := by decide +kernel

noncomputable def bx25 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 31744 38400 57344 442368)

theorem wk25 : SixW7.walk table bits 64 34388 bx25 = some 35419 := by decide +kernel

noncomputable def bx26 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 59904 74752 30720 40448)

theorem wk26 : SixW7.walk table bits 64 35419 bx26 = some 35710 := by decide +kernel

noncomputable def bx27 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 59904 74752 57344 442368)

theorem wk27 : SixW7.walk table bits 64 35710 bx27 = some 35826 := by decide +kernel

noncomputable def bx28 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 88064 262144 30720 40448)

theorem wk28 : SixW7.walk table bits 64 35826 bx28 = some 35877 := by decide +kernel

noncomputable def bx29 : SixW7.Box := (SixW7.Box.mk 30720 40448 31744 38400 89088 237568 88064 262144 57344 442368)

theorem wk29 : SixW7.walk table bits 64 35877 bx29 = some 35878 := by decide +kernel

noncomputable def bx30 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 31744 38400 30720 40448)

theorem wk30 : SixW7.walk table bits 64 35878 bx30 = some 39469 := by decide +kernel

noncomputable def bx31 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 31744 38400 57344 442368)

noncomputable def bx32 : SixW7.Box := (bx31).setHi (SixW7.axOf bits 39469) (SixW7.Box.mid bx31 (SixW7.axOf bits 39469))

noncomputable def bx33 : SixW7.Box := (bx32).setHi (SixW7.axOf bits 39473) (SixW7.Box.mid bx32 (SixW7.axOf bits 39473))

noncomputable def bx34 : SixW7.Box := (bx33).setHi (SixW7.axOf bits 39477) (SixW7.Box.mid bx33 (SixW7.axOf bits 39477))

noncomputable def bx35 : SixW7.Box := (bx34).setHi (SixW7.axOf bits 39481) (SixW7.Box.mid bx34 (SixW7.axOf bits 39481))

noncomputable def bx36 : SixW7.Box := (bx35).setHi (SixW7.axOf bits 39485) (SixW7.Box.mid bx35 (SixW7.axOf bits 39485))

noncomputable def bx37 : SixW7.Box := (bx36).setHi (SixW7.axOf bits 39489) (SixW7.Box.mid bx36 (SixW7.axOf bits 39489))

theorem wk37 : SixW7.walk table bits 58 39493 bx37 = some 39879 := by decide +kernel

noncomputable def bx38 : SixW7.Box := (bx36).setLo (SixW7.axOf bits 39489) (SixW7.Box.mid bx36 (SixW7.axOf bits 39489))

noncomputable def bx39 : SixW7.Box := (bx38).setHi (SixW7.axOf bits 39879) (SixW7.Box.mid bx38 (SixW7.axOf bits 39879))

noncomputable def bx40 : SixW7.Box := (bx39).setHi (SixW7.axOf bits 39883) (SixW7.Box.mid bx39 (SixW7.axOf bits 39883))

theorem wk40 : SixW7.walk table bits 56 39887 bx40 = some 40023 := by decide +kernel

noncomputable def bx41 : SixW7.Box := (bx39).setLo (SixW7.axOf bits 39883) (SixW7.Box.mid bx39 (SixW7.axOf bits 39883))

noncomputable def bx42 : SixW7.Box := (bx41).setHi (SixW7.axOf bits 40023) (SixW7.Box.mid bx41 (SixW7.axOf bits 40023))

noncomputable def bx43 : SixW7.Box := (bx42).setHi (SixW7.axOf bits 40027) (SixW7.Box.mid bx42 (SixW7.axOf bits 40027))

theorem wk43 : SixW7.walk table bits 54 40031 bx43 = some 40357 := by decide +kernel

noncomputable def bx44 : SixW7.Box := (bx42).setLo (SixW7.axOf bits 40027) (SixW7.Box.mid bx42 (SixW7.axOf bits 40027))

noncomputable def bx45 : SixW7.Box := (bx44).setHi (SixW7.axOf bits 40357) (SixW7.Box.mid bx44 (SixW7.axOf bits 40357))

theorem wk45 : SixW7.walk table bits 53 40361 bx45 = some 45207 := by decide +kernel

noncomputable def bx46 : SixW7.Box := (bx44).setLo (SixW7.axOf bits 40357) (SixW7.Box.mid bx44 (SixW7.axOf bits 40357))

theorem wk46 : SixW7.walk table bits 53 45207 bx46 = some 46418 := by decide +kernel

theorem wk44 : SixW7.walk table bits 54 40357 bx44 = some 46418 :=
  SixW7.walk_split table bits 53 40357 bx44 45207 46418 (by decide +kernel) wk45 wk46

theorem wk42 : SixW7.walk table bits 55 40027 bx42 = some 46418 :=
  SixW7.walk_split table bits 54 40027 bx42 40357 46418 (by decide +kernel) wk43 wk44

noncomputable def bx47 : SixW7.Box := (bx41).setLo (SixW7.axOf bits 40023) (SixW7.Box.mid bx41 (SixW7.axOf bits 40023))

theorem wk47 : SixW7.walk table bits 55 46418 bx47 = some 46659 := by decide +kernel

theorem wk41 : SixW7.walk table bits 56 40023 bx41 = some 46659 :=
  SixW7.walk_split table bits 55 40023 bx41 46418 46659 (by decide +kernel) wk42 wk47

theorem wk39 : SixW7.walk table bits 57 39883 bx39 = some 46659 :=
  SixW7.walk_split table bits 56 39883 bx39 40023 46659 (by decide +kernel) wk40 wk41

noncomputable def bx48 : SixW7.Box := (bx38).setLo (SixW7.axOf bits 39879) (SixW7.Box.mid bx38 (SixW7.axOf bits 39879))

theorem wk48 : SixW7.walk table bits 57 46659 bx48 = some 46750 := by decide +kernel

theorem wk38 : SixW7.walk table bits 58 39879 bx38 = some 46750 :=
  SixW7.walk_split table bits 57 39879 bx38 46659 46750 (by decide +kernel) wk39 wk48

theorem wk36 : SixW7.walk table bits 59 39489 bx36 = some 46750 :=
  SixW7.walk_split table bits 58 39489 bx36 39879 46750 (by decide +kernel) wk37 wk38

noncomputable def bx49 : SixW7.Box := (bx35).setLo (SixW7.axOf bits 39485) (SixW7.Box.mid bx35 (SixW7.axOf bits 39485))

theorem wk49 : SixW7.walk table bits 59 46750 bx49 = some 46796 := by decide +kernel

theorem wk35 : SixW7.walk table bits 60 39485 bx35 = some 46796 :=
  SixW7.walk_split table bits 59 39485 bx35 46750 46796 (by decide +kernel) wk36 wk49

noncomputable def bx50 : SixW7.Box := (bx34).setLo (SixW7.axOf bits 39481) (SixW7.Box.mid bx34 (SixW7.axOf bits 39481))

theorem wk50 : SixW7.walk table bits 60 46796 bx50 = some 48367 := by decide +kernel

theorem wk34 : SixW7.walk table bits 61 39481 bx34 = some 48367 :=
  SixW7.walk_split table bits 60 39481 bx34 46796 48367 (by decide +kernel) wk35 wk50

noncomputable def bx51 : SixW7.Box := (bx33).setLo (SixW7.axOf bits 39477) (SixW7.Box.mid bx33 (SixW7.axOf bits 39477))

theorem wk51 : SixW7.walk table bits 61 48367 bx51 = some 49048 := by decide +kernel

theorem wk33 : SixW7.walk table bits 62 39477 bx33 = some 49048 :=
  SixW7.walk_split table bits 61 39477 bx33 48367 49048 (by decide +kernel) wk34 wk51

noncomputable def bx52 : SixW7.Box := (bx32).setLo (SixW7.axOf bits 39473) (SixW7.Box.mid bx32 (SixW7.axOf bits 39473))

theorem wk52 : SixW7.walk table bits 62 49048 bx52 = some 49299 := by decide +kernel

theorem wk32 : SixW7.walk table bits 63 39473 bx32 = some 49299 :=
  SixW7.walk_split table bits 62 39473 bx32 49048 49299 (by decide +kernel) wk33 wk52

noncomputable def bx53 : SixW7.Box := (bx31).setLo (SixW7.axOf bits 39469) (SixW7.Box.mid bx31 (SixW7.axOf bits 39469))

theorem wk53 : SixW7.walk table bits 63 49299 bx53 = some 49300 := by decide +kernel

theorem wk31 : SixW7.walk table bits 64 39469 bx31 = some 49300 :=
  SixW7.walk_split table bits 63 39469 bx31 49299 49300 (by decide +kernel) wk32 wk53

noncomputable def bx54 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 59904 74752 30720 40448)

noncomputable def bx55 : SixW7.Box := (bx54).setHi (SixW7.axOf bits 49300) (SixW7.Box.mid bx54 (SixW7.axOf bits 49300))

noncomputable def bx56 : SixW7.Box := (bx55).setHi (SixW7.axOf bits 49304) (SixW7.Box.mid bx55 (SixW7.axOf bits 49304))

theorem wk56 : SixW7.walk table bits 62 49308 bx56 = some 49389 := by decide +kernel

noncomputable def bx57 : SixW7.Box := (bx55).setLo (SixW7.axOf bits 49304) (SixW7.Box.mid bx55 (SixW7.axOf bits 49304))

noncomputable def bx58 : SixW7.Box := (bx57).setHi (SixW7.axOf bits 49389) (SixW7.Box.mid bx57 (SixW7.axOf bits 49389))

noncomputable def bx59 : SixW7.Box := (bx58).setHi (SixW7.axOf bits 49393) (SixW7.Box.mid bx58 (SixW7.axOf bits 49393))

theorem wk59 : SixW7.walk table bits 60 49397 bx59 = some 49453 := by decide +kernel

noncomputable def bx60 : SixW7.Box := (bx58).setLo (SixW7.axOf bits 49393) (SixW7.Box.mid bx58 (SixW7.axOf bits 49393))

noncomputable def bx61 : SixW7.Box := (bx60).setHi (SixW7.axOf bits 49453) (SixW7.Box.mid bx60 (SixW7.axOf bits 49453))

noncomputable def bx62 : SixW7.Box := (bx61).setHi (SixW7.axOf bits 49457) (SixW7.Box.mid bx61 (SixW7.axOf bits 49457))

theorem wk62 : SixW7.walk table bits 58 49461 bx62 = some 49792 := by decide +kernel

noncomputable def bx63 : SixW7.Box := (bx61).setLo (SixW7.axOf bits 49457) (SixW7.Box.mid bx61 (SixW7.axOf bits 49457))

noncomputable def bx64 : SixW7.Box := (bx63).setHi (SixW7.axOf bits 49792) (SixW7.Box.mid bx63 (SixW7.axOf bits 49792))

noncomputable def bx65 : SixW7.Box := (bx64).setHi (SixW7.axOf bits 49796) (SixW7.Box.mid bx64 (SixW7.axOf bits 49796))

theorem wk65 : SixW7.walk table bits 56 49800 bx65 = some 50086 := by decide +kernel

noncomputable def bx66 : SixW7.Box := (bx64).setLo (SixW7.axOf bits 49796) (SixW7.Box.mid bx64 (SixW7.axOf bits 49796))

noncomputable def bx67 : SixW7.Box := (bx66).setHi (SixW7.axOf bits 50086) (SixW7.Box.mid bx66 (SixW7.axOf bits 50086))

noncomputable def bx68 : SixW7.Box := (bx67).setHi (SixW7.axOf bits 50090) (SixW7.Box.mid bx67 (SixW7.axOf bits 50090))

theorem wk68 : SixW7.walk table bits 54 50094 bx68 = some 51745 := by decide +kernel

noncomputable def bx69 : SixW7.Box := (bx67).setLo (SixW7.axOf bits 50090) (SixW7.Box.mid bx67 (SixW7.axOf bits 50090))

noncomputable def bx70 : SixW7.Box := (bx69).setHi (SixW7.axOf bits 51745) (SixW7.Box.mid bx69 (SixW7.axOf bits 51745))

noncomputable def bx71 : SixW7.Box := (bx70).setHi (SixW7.axOf bits 51749) (SixW7.Box.mid bx70 (SixW7.axOf bits 51749))

theorem wk71 : SixW7.walk table bits 52 51753 bx71 = some 51759 := by decide +kernel

noncomputable def bx72 : SixW7.Box := (bx70).setLo (SixW7.axOf bits 51749) (SixW7.Box.mid bx70 (SixW7.axOf bits 51749))

noncomputable def bx73 : SixW7.Box := (bx72).setHi (SixW7.axOf bits 51759) (SixW7.Box.mid bx72 (SixW7.axOf bits 51759))

noncomputable def bx74 : SixW7.Box := (bx73).setHi (SixW7.axOf bits 51763) (SixW7.Box.mid bx73 (SixW7.axOf bits 51763))

theorem wk74 : SixW7.walk table bits 50 51767 bx74 = some 52653 := by decide +kernel

noncomputable def bx75 : SixW7.Box := (bx73).setLo (SixW7.axOf bits 51763) (SixW7.Box.mid bx73 (SixW7.axOf bits 51763))

noncomputable def bx76 : SixW7.Box := (bx75).setHi (SixW7.axOf bits 52653) (SixW7.Box.mid bx75 (SixW7.axOf bits 52653))

theorem wk76 : SixW7.walk table bits 49 52657 bx76 = some 55378 := by decide +kernel

noncomputable def bx77 : SixW7.Box := (bx75).setLo (SixW7.axOf bits 52653) (SixW7.Box.mid bx75 (SixW7.axOf bits 52653))

theorem wk77 : SixW7.walk table bits 49 55378 bx77 = some 58704 := by decide +kernel

theorem wk75 : SixW7.walk table bits 50 52653 bx75 = some 58704 :=
  SixW7.walk_split table bits 49 52653 bx75 55378 58704 (by decide +kernel) wk76 wk77

theorem wk73 : SixW7.walk table bits 51 51763 bx73 = some 58704 :=
  SixW7.walk_split table bits 50 51763 bx73 52653 58704 (by decide +kernel) wk74 wk75

noncomputable def bx78 : SixW7.Box := (bx72).setLo (SixW7.axOf bits 51759) (SixW7.Box.mid bx72 (SixW7.axOf bits 51759))

theorem wk78 : SixW7.walk table bits 51 58704 bx78 = some 60695 := by decide +kernel

theorem wk72 : SixW7.walk table bits 52 51759 bx72 = some 60695 :=
  SixW7.walk_split table bits 51 51759 bx72 58704 60695 (by decide +kernel) wk73 wk78

theorem wk70 : SixW7.walk table bits 53 51749 bx70 = some 60695 :=
  SixW7.walk_split table bits 52 51749 bx70 51759 60695 (by decide +kernel) wk71 wk72

noncomputable def bx79 : SixW7.Box := (bx69).setLo (SixW7.axOf bits 51745) (SixW7.Box.mid bx69 (SixW7.axOf bits 51745))

theorem wk79 : SixW7.walk table bits 53 60695 bx79 = some 60916 := by decide +kernel

theorem wk69 : SixW7.walk table bits 54 51745 bx69 = some 60916 :=
  SixW7.walk_split table bits 53 51745 bx69 60695 60916 (by decide +kernel) wk70 wk79

theorem wk67 : SixW7.walk table bits 55 50090 bx67 = some 60916 :=
  SixW7.walk_split table bits 54 50090 bx67 51745 60916 (by decide +kernel) wk68 wk69

noncomputable def bx80 : SixW7.Box := (bx66).setLo (SixW7.axOf bits 50086) (SixW7.Box.mid bx66 (SixW7.axOf bits 50086))

theorem wk80 : SixW7.walk table bits 55 60916 bx80 = some 64397 := by decide +kernel

theorem wk66 : SixW7.walk table bits 56 50086 bx66 = some 64397 :=
  SixW7.walk_split table bits 55 50086 bx66 60916 64397 (by decide +kernel) wk67 wk80

theorem wk64 : SixW7.walk table bits 57 49796 bx64 = some 64397 :=
  SixW7.walk_split table bits 56 49796 bx64 50086 64397 (by decide +kernel) wk65 wk66

noncomputable def bx81 : SixW7.Box := (bx63).setLo (SixW7.axOf bits 49792) (SixW7.Box.mid bx63 (SixW7.axOf bits 49792))

theorem wk81 : SixW7.walk table bits 57 64397 bx81 = some 64563 := by decide +kernel

theorem wk63 : SixW7.walk table bits 58 49792 bx63 = some 64563 :=
  SixW7.walk_split table bits 57 49792 bx63 64397 64563 (by decide +kernel) wk64 wk81

theorem wk61 : SixW7.walk table bits 59 49457 bx61 = some 64563 :=
  SixW7.walk_split table bits 58 49457 bx61 49792 64563 (by decide +kernel) wk62 wk63

noncomputable def bx82 : SixW7.Box := (bx60).setLo (SixW7.axOf bits 49453) (SixW7.Box.mid bx60 (SixW7.axOf bits 49453))

theorem wk82 : SixW7.walk table bits 59 64563 bx82 = some 64774 := by decide +kernel

theorem wk60 : SixW7.walk table bits 60 49453 bx60 = some 64774 :=
  SixW7.walk_split table bits 59 49453 bx60 64563 64774 (by decide +kernel) wk61 wk82

theorem wk58 : SixW7.walk table bits 61 49393 bx58 = some 64774 :=
  SixW7.walk_split table bits 60 49393 bx58 49453 64774 (by decide +kernel) wk59 wk60

noncomputable def bx83 : SixW7.Box := (bx57).setLo (SixW7.axOf bits 49389) (SixW7.Box.mid bx57 (SixW7.axOf bits 49389))

theorem wk83 : SixW7.walk table bits 61 64774 bx83 = some 64880 := by decide +kernel

theorem wk57 : SixW7.walk table bits 62 49389 bx57 = some 64880 :=
  SixW7.walk_split table bits 61 49389 bx57 64774 64880 (by decide +kernel) wk58 wk83

theorem wk55 : SixW7.walk table bits 63 49304 bx55 = some 64880 :=
  SixW7.walk_split table bits 62 49304 bx55 49389 64880 (by decide +kernel) wk56 wk57

noncomputable def bx84 : SixW7.Box := (bx54).setLo (SixW7.axOf bits 49300) (SixW7.Box.mid bx54 (SixW7.axOf bits 49300))

theorem wk84 : SixW7.walk table bits 63 64880 bx84 = some 65031 := by decide +kernel

theorem wk54 : SixW7.walk table bits 64 49300 bx54 = some 65031 :=
  SixW7.walk_split table bits 63 49300 bx54 64880 65031 (by decide +kernel) wk55 wk84

noncomputable def bx85 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 59904 74752 57344 442368)

noncomputable def bx86 : SixW7.Box := (bx85).setHi (SixW7.axOf bits 65031) (SixW7.Box.mid bx85 (SixW7.axOf bits 65031))

noncomputable def bx87 : SixW7.Box := (bx86).setHi (SixW7.axOf bits 65035) (SixW7.Box.mid bx86 (SixW7.axOf bits 65035))

noncomputable def bx88 : SixW7.Box := (bx87).setHi (SixW7.axOf bits 65039) (SixW7.Box.mid bx87 (SixW7.axOf bits 65039))

noncomputable def bx89 : SixW7.Box := (bx88).setHi (SixW7.axOf bits 65043) (SixW7.Box.mid bx88 (SixW7.axOf bits 65043))

noncomputable def bx90 : SixW7.Box := (bx89).setHi (SixW7.axOf bits 65047) (SixW7.Box.mid bx89 (SixW7.axOf bits 65047))

noncomputable def bx91 : SixW7.Box := (bx90).setHi (SixW7.axOf bits 65051) (SixW7.Box.mid bx90 (SixW7.axOf bits 65051))

theorem wk91 : SixW7.walk table bits 58 65055 bx91 = some 65161 := by decide +kernel

noncomputable def bx92 : SixW7.Box := (bx90).setLo (SixW7.axOf bits 65051) (SixW7.Box.mid bx90 (SixW7.axOf bits 65051))

noncomputable def bx93 : SixW7.Box := (bx92).setHi (SixW7.axOf bits 65161) (SixW7.Box.mid bx92 (SixW7.axOf bits 65161))

noncomputable def bx94 : SixW7.Box := (bx93).setHi (SixW7.axOf bits 65165) (SixW7.Box.mid bx93 (SixW7.axOf bits 65165))

theorem wk94 : SixW7.walk table bits 56 65169 bx94 = some 65175 := by decide +kernel

noncomputable def bx95 : SixW7.Box := (bx93).setLo (SixW7.axOf bits 65165) (SixW7.Box.mid bx93 (SixW7.axOf bits 65165))

noncomputable def bx96 : SixW7.Box := (bx95).setHi (SixW7.axOf bits 65175) (SixW7.Box.mid bx95 (SixW7.axOf bits 65175))

noncomputable def bx97 : SixW7.Box := (bx96).setHi (SixW7.axOf bits 65179) (SixW7.Box.mid bx96 (SixW7.axOf bits 65179))

theorem wk97 : SixW7.walk table bits 54 65183 bx97 = some 65184 := by decide +kernel

noncomputable def bx98 : SixW7.Box := (bx96).setLo (SixW7.axOf bits 65179) (SixW7.Box.mid bx96 (SixW7.axOf bits 65179))

noncomputable def bx99 : SixW7.Box := (bx98).setHi (SixW7.axOf bits 65184) (SixW7.Box.mid bx98 (SixW7.axOf bits 65184))

noncomputable def bx100 : SixW7.Box := (bx99).setHi (SixW7.axOf bits 65188) (SixW7.Box.mid bx99 (SixW7.axOf bits 65188))

theorem wk100 : SixW7.walk table bits 52 65192 bx100 = some 65223 := by decide +kernel

noncomputable def bx101 : SixW7.Box := (bx99).setLo (SixW7.axOf bits 65188) (SixW7.Box.mid bx99 (SixW7.axOf bits 65188))

noncomputable def bx102 : SixW7.Box := (bx101).setHi (SixW7.axOf bits 65223) (SixW7.Box.mid bx101 (SixW7.axOf bits 65223))

theorem wk102 : SixW7.walk table bits 51 65227 bx102 = some 68903 := by decide +kernel

noncomputable def bx103 : SixW7.Box := (bx101).setLo (SixW7.axOf bits 65223) (SixW7.Box.mid bx101 (SixW7.axOf bits 65223))

theorem wk103 : SixW7.walk table bits 51 68903 bx103 = some 70859 := by decide +kernel

theorem wk101 : SixW7.walk table bits 52 65223 bx101 = some 70859 :=
  SixW7.walk_split table bits 51 65223 bx101 68903 70859 (by decide +kernel) wk102 wk103

theorem wk99 : SixW7.walk table bits 53 65188 bx99 = some 70859 :=
  SixW7.walk_split table bits 52 65188 bx99 65223 70859 (by decide +kernel) wk100 wk101

noncomputable def bx104 : SixW7.Box := (bx98).setLo (SixW7.axOf bits 65184) (SixW7.Box.mid bx98 (SixW7.axOf bits 65184))

theorem wk104 : SixW7.walk table bits 53 70859 bx104 = some 70935 := by decide +kernel

theorem wk98 : SixW7.walk table bits 54 65184 bx98 = some 70935 :=
  SixW7.walk_split table bits 53 65184 bx98 70859 70935 (by decide +kernel) wk99 wk104

theorem wk96 : SixW7.walk table bits 55 65179 bx96 = some 70935 :=
  SixW7.walk_split table bits 54 65179 bx96 65184 70935 (by decide +kernel) wk97 wk98

noncomputable def bx105 : SixW7.Box := (bx95).setLo (SixW7.axOf bits 65175) (SixW7.Box.mid bx95 (SixW7.axOf bits 65175))

theorem wk105 : SixW7.walk table bits 55 70935 bx105 = some 71036 := by decide +kernel

theorem wk95 : SixW7.walk table bits 56 65175 bx95 = some 71036 :=
  SixW7.walk_split table bits 55 65175 bx95 70935 71036 (by decide +kernel) wk96 wk105

theorem wk93 : SixW7.walk table bits 57 65165 bx93 = some 71036 :=
  SixW7.walk_split table bits 56 65165 bx93 65175 71036 (by decide +kernel) wk94 wk95

noncomputable def bx106 : SixW7.Box := (bx92).setLo (SixW7.axOf bits 65161) (SixW7.Box.mid bx92 (SixW7.axOf bits 65161))

theorem wk106 : SixW7.walk table bits 57 71036 bx106 = some 71112 := by decide +kernel

theorem wk92 : SixW7.walk table bits 58 65161 bx92 = some 71112 :=
  SixW7.walk_split table bits 57 65161 bx92 71036 71112 (by decide +kernel) wk93 wk106

theorem wk90 : SixW7.walk table bits 59 65051 bx90 = some 71112 :=
  SixW7.walk_split table bits 58 65051 bx90 65161 71112 (by decide +kernel) wk91 wk92

noncomputable def bx107 : SixW7.Box := (bx89).setLo (SixW7.axOf bits 65047) (SixW7.Box.mid bx89 (SixW7.axOf bits 65047))

theorem wk107 : SixW7.walk table bits 59 71112 bx107 = some 71163 := by decide +kernel

theorem wk89 : SixW7.walk table bits 60 65047 bx89 = some 71163 :=
  SixW7.walk_split table bits 59 65047 bx89 71112 71163 (by decide +kernel) wk90 wk107

noncomputable def bx108 : SixW7.Box := (bx88).setLo (SixW7.axOf bits 65043) (SixW7.Box.mid bx88 (SixW7.axOf bits 65043))

theorem wk108 : SixW7.walk table bits 60 71163 bx108 = some 71689 := by decide +kernel

theorem wk88 : SixW7.walk table bits 61 65043 bx88 = some 71689 :=
  SixW7.walk_split table bits 60 65043 bx88 71163 71689 (by decide +kernel) wk89 wk108

noncomputable def bx109 : SixW7.Box := (bx87).setLo (SixW7.axOf bits 65039) (SixW7.Box.mid bx87 (SixW7.axOf bits 65039))

theorem wk109 : SixW7.walk table bits 61 71689 bx109 = some 71790 := by decide +kernel

theorem wk87 : SixW7.walk table bits 62 65039 bx87 = some 71790 :=
  SixW7.walk_split table bits 61 65039 bx87 71689 71790 (by decide +kernel) wk88 wk109

noncomputable def bx110 : SixW7.Box := (bx86).setLo (SixW7.axOf bits 65035) (SixW7.Box.mid bx86 (SixW7.axOf bits 65035))

theorem wk110 : SixW7.walk table bits 62 71790 bx110 = some 71791 := by decide +kernel

theorem wk86 : SixW7.walk table bits 63 65035 bx86 = some 71791 :=
  SixW7.walk_split table bits 62 65035 bx86 71790 71791 (by decide +kernel) wk87 wk110

noncomputable def bx111 : SixW7.Box := (bx85).setLo (SixW7.axOf bits 65031) (SixW7.Box.mid bx85 (SixW7.axOf bits 65031))

theorem wk111 : SixW7.walk table bits 63 71791 bx111 = some 71792 := by decide +kernel

theorem wk85 : SixW7.walk table bits 64 65031 bx85 = some 71792 :=
  SixW7.walk_split table bits 63 65031 bx85 71791 71792 (by decide +kernel) wk86 wk111

noncomputable def bx112 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 88064 262144 30720 40448)

theorem wk112 : SixW7.walk table bits 64 71792 bx112 = some 72698 := by decide +kernel

noncomputable def bx113 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 31744 38400 88064 262144 57344 442368)

theorem wk113 : SixW7.walk table bits 64 72698 bx113 = some 72889 := by decide +kernel

noncomputable def bx114 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 31744 38400 30720 40448)

theorem wk114 : SixW7.walk table bits 64 72889 bx114 = some 76210 := by decide +kernel

noncomputable def bx115 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 31744 38400 57344 442368)

noncomputable def bx116 : SixW7.Box := (bx115).setHi (SixW7.axOf bits 76210) (SixW7.Box.mid bx115 (SixW7.axOf bits 76210))

noncomputable def bx117 : SixW7.Box := (bx116).setHi (SixW7.axOf bits 76214) (SixW7.Box.mid bx116 (SixW7.axOf bits 76214))

noncomputable def bx118 : SixW7.Box := (bx117).setHi (SixW7.axOf bits 76218) (SixW7.Box.mid bx117 (SixW7.axOf bits 76218))

noncomputable def bx119 : SixW7.Box := (bx118).setHi (SixW7.axOf bits 76222) (SixW7.Box.mid bx118 (SixW7.axOf bits 76222))

noncomputable def bx120 : SixW7.Box := (bx119).setHi (SixW7.axOf bits 76226) (SixW7.Box.mid bx119 (SixW7.axOf bits 76226))

noncomputable def bx121 : SixW7.Box := (bx120).setHi (SixW7.axOf bits 76230) (SixW7.Box.mid bx120 (SixW7.axOf bits 76230))

theorem wk121 : SixW7.walk table bits 58 76234 bx121 = some 76320 := by decide +kernel

noncomputable def bx122 : SixW7.Box := (bx120).setLo (SixW7.axOf bits 76230) (SixW7.Box.mid bx120 (SixW7.axOf bits 76230))

theorem wk122 : SixW7.walk table bits 58 76320 bx122 = some 81286 := by decide +kernel

theorem wk120 : SixW7.walk table bits 59 76230 bx120 = some 81286 :=
  SixW7.walk_split table bits 58 76230 bx120 76320 81286 (by decide +kernel) wk121 wk122

noncomputable def bx123 : SixW7.Box := (bx119).setLo (SixW7.axOf bits 76226) (SixW7.Box.mid bx119 (SixW7.axOf bits 76226))

theorem wk123 : SixW7.walk table bits 59 81286 bx123 = some 81307 := by decide +kernel

theorem wk119 : SixW7.walk table bits 60 76226 bx119 = some 81307 :=
  SixW7.walk_split table bits 59 76226 bx119 81286 81307 (by decide +kernel) wk120 wk123

noncomputable def bx124 : SixW7.Box := (bx118).setLo (SixW7.axOf bits 76222) (SixW7.Box.mid bx118 (SixW7.axOf bits 76222))

theorem wk124 : SixW7.walk table bits 60 81307 bx124 = some 81688 := by decide +kernel

theorem wk118 : SixW7.walk table bits 61 76222 bx118 = some 81688 :=
  SixW7.walk_split table bits 60 76222 bx118 81307 81688 (by decide +kernel) wk119 wk124

noncomputable def bx125 : SixW7.Box := (bx117).setLo (SixW7.axOf bits 76218) (SixW7.Box.mid bx117 (SixW7.axOf bits 76218))

theorem wk125 : SixW7.walk table bits 61 81688 bx125 = some 81754 := by decide +kernel

theorem wk117 : SixW7.walk table bits 62 76218 bx117 = some 81754 :=
  SixW7.walk_split table bits 61 76218 bx117 81688 81754 (by decide +kernel) wk118 wk125

noncomputable def bx126 : SixW7.Box := (bx116).setLo (SixW7.axOf bits 76214) (SixW7.Box.mid bx116 (SixW7.axOf bits 76214))

theorem wk126 : SixW7.walk table bits 62 81754 bx126 = some 81755 := by decide +kernel

theorem wk116 : SixW7.walk table bits 63 76214 bx116 = some 81755 :=
  SixW7.walk_split table bits 62 76214 bx116 81754 81755 (by decide +kernel) wk117 wk126

noncomputable def bx127 : SixW7.Box := (bx115).setLo (SixW7.axOf bits 76210) (SixW7.Box.mid bx115 (SixW7.axOf bits 76210))

theorem wk127 : SixW7.walk table bits 63 81755 bx127 = some 81756 := by decide +kernel

theorem wk115 : SixW7.walk table bits 64 76210 bx115 = some 81756 :=
  SixW7.walk_split table bits 63 76210 bx115 81755 81756 (by decide +kernel) wk116 wk127

noncomputable def bx128 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 59904 74752 30720 40448)

theorem wk128 : SixW7.walk table bits 64 81756 bx128 = some 82762 := by decide +kernel

noncomputable def bx129 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 59904 74752 57344 442368)

theorem wk129 : SixW7.walk table bits 64 82762 bx129 = some 82903 := by decide +kernel

noncomputable def bx130 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 88064 262144 30720 40448)

theorem wk130 : SixW7.walk table bits 64 82903 bx130 = some 82939 := by decide +kernel

noncomputable def bx131 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 60416 74240 88064 262144 57344 442368)

theorem wk131 : SixW7.walk table bits 64 82939 bx131 = some 82940 := by decide +kernel

noncomputable def bx132 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 31744 38400 30720 40448)

theorem wk132 : SixW7.walk table bits 64 82940 bx132 = some 83221 := by decide +kernel

noncomputable def bx133 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 31744 38400 57344 442368)

theorem wk133 : SixW7.walk table bits 64 83221 bx133 = some 83332 := by decide +kernel

noncomputable def bx134 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 59904 74752 30720 40448)

theorem wk134 : SixW7.walk table bits 64 83332 bx134 = some 83358 := by decide +kernel

noncomputable def bx135 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 59904 74752 57344 442368)

theorem wk135 : SixW7.walk table bits 64 83358 bx135 = some 83359 := by decide +kernel

noncomputable def bx136 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 88064 262144 30720 40448)

theorem wk136 : SixW7.walk table bits 64 83359 bx136 = some 83360 := by decide +kernel

noncomputable def bx137 : SixW7.Box := (SixW7.Box.mk 30720 40448 59904 74752 89088 237568 88064 262144 57344 442368)

theorem wk137 : SixW7.walk table bits 64 83360 bx137 = some 83361 := by decide +kernel

noncomputable def bx138 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 31744 38400 30720 40448)

theorem wk138 : SixW7.walk table bits 64 83361 bx138 = some 84702 := by decide +kernel

noncomputable def bx139 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 31744 38400 57344 442368)

theorem wk139 : SixW7.walk table bits 64 84702 bx139 = some 86468 := by decide +kernel

noncomputable def bx140 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 59904 74752 30720 40448)

theorem wk140 : SixW7.walk table bits 64 86468 bx140 = some 87374 := by decide +kernel

noncomputable def bx141 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 59904 74752 57344 442368)

theorem wk141 : SixW7.walk table bits 64 87374 bx141 = some 87570 := by decide +kernel

noncomputable def bx142 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 88064 262144 30720 40448)

theorem wk142 : SixW7.walk table bits 64 87570 bx142 = some 87641 := by decide +kernel

noncomputable def bx143 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 31744 38400 88064 262144 57344 442368)

theorem wk143 : SixW7.walk table bits 64 87641 bx143 = some 87642 := by decide +kernel

noncomputable def bx144 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 31744 38400 30720 40448)

theorem wk144 : SixW7.walk table bits 64 87642 bx144 = some 87993 := by decide +kernel

noncomputable def bx145 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 31744 38400 57344 442368)

theorem wk145 : SixW7.walk table bits 64 87993 bx145 = some 88144 := by decide +kernel

noncomputable def bx146 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 59904 74752 30720 40448)

theorem wk146 : SixW7.walk table bits 64 88144 bx146 = some 88180 := by decide +kernel

noncomputable def bx147 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 59904 74752 57344 442368)

theorem wk147 : SixW7.walk table bits 64 88180 bx147 = some 88181 := by decide +kernel

noncomputable def bx148 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 88064 262144 30720 40448)

theorem wk148 : SixW7.walk table bits 64 88181 bx148 = some 88182 := by decide +kernel

noncomputable def bx149 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 60416 74240 88064 262144 57344 442368)

theorem wk149 : SixW7.walk table bits 64 88182 bx149 = some 88183 := by decide +kernel

noncomputable def bx150 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 31744 38400 30720 40448)

theorem wk150 : SixW7.walk table bits 64 88183 bx150 = some 88234 := by decide +kernel

noncomputable def bx151 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 31744 38400 57344 442368)

theorem wk151 : SixW7.walk table bits 64 88234 bx151 = some 88235 := by decide +kernel

noncomputable def bx152 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 59904 74752 30720 40448)

theorem wk152 : SixW7.walk table bits 64 88235 bx152 = some 88236 := by decide +kernel

noncomputable def bx153 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 59904 74752 57344 442368)

theorem wk153 : SixW7.walk table bits 64 88236 bx153 = some 88237 := by decide +kernel

noncomputable def bx154 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 88064 262144 30720 40448)

theorem wk154 : SixW7.walk table bits 64 88237 bx154 = some 88238 := by decide +kernel

noncomputable def bx155 : SixW7.Box := (SixW7.Box.mk 30720 40448 88064 262144 89088 237568 88064 262144 57344 442368)

theorem wk155 : SixW7.walk table bits 64 88238 bx155 = some 88239 := by decide +kernel

noncomputable def bx156 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 31744 38400 30720 40448)

theorem wk156 : SixW7.walk table bits 64 88239 bx156 = some 88240 := by decide +kernel

noncomputable def bx157 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 31744 38400 57344 442368)

theorem wk157 : SixW7.walk table bits 64 88240 bx157 = some 92756 := by decide +kernel

noncomputable def bx158 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 59904 74752 30720 40448)

theorem wk158 : SixW7.walk table bits 64 92756 bx158 = some 92757 := by decide +kernel

noncomputable def bx159 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 59904 74752 57344 442368)

theorem wk159 : SixW7.walk table bits 64 92757 bx159 = some 97678 := by decide +kernel

noncomputable def bx160 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 88064 262144 30720 40448)

theorem wk160 : SixW7.walk table bits 64 97678 bx160 = some 97679 := by decide +kernel

noncomputable def bx161 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 31744 38400 88064 262144 57344 442368)

theorem wk161 : SixW7.walk table bits 64 97679 bx161 = some 98200 := by decide +kernel

noncomputable def bx162 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 31744 38400 30720 40448)

theorem wk162 : SixW7.walk table bits 64 98200 bx162 = some 98201 := by decide +kernel

noncomputable def bx163 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 31744 38400 57344 442368)

noncomputable def bx164 : SixW7.Box := (bx163).setHi (SixW7.axOf bits 98201) (SixW7.Box.mid bx163 (SixW7.axOf bits 98201))

noncomputable def bx165 : SixW7.Box := (bx164).setHi (SixW7.axOf bits 98205) (SixW7.Box.mid bx164 (SixW7.axOf bits 98205))

noncomputable def bx166 : SixW7.Box := (bx165).setHi (SixW7.axOf bits 98209) (SixW7.Box.mid bx165 (SixW7.axOf bits 98209))

noncomputable def bx167 : SixW7.Box := (bx166).setHi (SixW7.axOf bits 98213) (SixW7.Box.mid bx166 (SixW7.axOf bits 98213))

noncomputable def bx168 : SixW7.Box := (bx167).setHi (SixW7.axOf bits 98217) (SixW7.Box.mid bx167 (SixW7.axOf bits 98217))

noncomputable def bx169 : SixW7.Box := (bx168).setHi (SixW7.axOf bits 98221) (SixW7.Box.mid bx168 (SixW7.axOf bits 98221))

noncomputable def bx170 : SixW7.Box := (bx169).setHi (SixW7.axOf bits 98225) (SixW7.Box.mid bx169 (SixW7.axOf bits 98225))

noncomputable def bx171 : SixW7.Box := (bx170).setHi (SixW7.axOf bits 98229) (SixW7.Box.mid bx170 (SixW7.axOf bits 98229))

noncomputable def bx172 : SixW7.Box := (bx171).setHi (SixW7.axOf bits 98233) (SixW7.Box.mid bx171 (SixW7.axOf bits 98233))

theorem wk172 : SixW7.walk table bits 55 98237 bx172 = some 98443 := by decide +kernel

noncomputable def bx173 : SixW7.Box := (bx171).setLo (SixW7.axOf bits 98233) (SixW7.Box.mid bx171 (SixW7.axOf bits 98233))

noncomputable def bx174 : SixW7.Box := (bx173).setHi (SixW7.axOf bits 98443) (SixW7.Box.mid bx173 (SixW7.axOf bits 98443))

noncomputable def bx175 : SixW7.Box := (bx174).setHi (SixW7.axOf bits 98447) (SixW7.Box.mid bx174 (SixW7.axOf bits 98447))

noncomputable def bx176 : SixW7.Box := (bx175).setHi (SixW7.axOf bits 98451) (SixW7.Box.mid bx175 (SixW7.axOf bits 98451))

theorem wk176 : SixW7.walk table bits 52 98455 bx176 = some 98611 := by decide +kernel

noncomputable def bx177 : SixW7.Box := (bx175).setLo (SixW7.axOf bits 98451) (SixW7.Box.mid bx175 (SixW7.axOf bits 98451))

noncomputable def bx178 : SixW7.Box := (bx177).setHi (SixW7.axOf bits 98611) (SixW7.Box.mid bx177 (SixW7.axOf bits 98611))

noncomputable def bx179 : SixW7.Box := (bx178).setHi (SixW7.axOf bits 98615) (SixW7.Box.mid bx178 (SixW7.axOf bits 98615))

theorem wk179 : SixW7.walk table bits 50 98619 bx179 = some 98645 := by decide +kernel

noncomputable def bx180 : SixW7.Box := (bx178).setLo (SixW7.axOf bits 98615) (SixW7.Box.mid bx178 (SixW7.axOf bits 98615))

noncomputable def bx181 : SixW7.Box := (bx180).setHi (SixW7.axOf bits 98645) (SixW7.Box.mid bx180 (SixW7.axOf bits 98645))

noncomputable def bx182 : SixW7.Box := (bx181).setHi (SixW7.axOf bits 98649) (SixW7.Box.mid bx181 (SixW7.axOf bits 98649))

theorem wk182 : SixW7.walk table bits 48 98653 bx182 = some 100284 := by decide +kernel

noncomputable def bx183 : SixW7.Box := (bx181).setLo (SixW7.axOf bits 98649) (SixW7.Box.mid bx181 (SixW7.axOf bits 98649))

noncomputable def bx184 : SixW7.Box := (bx183).setHi (SixW7.axOf bits 100284) (SixW7.Box.mid bx183 (SixW7.axOf bits 100284))

noncomputable def bx185 : SixW7.Box := (bx184).setHi (SixW7.axOf bits 100288) (SixW7.Box.mid bx184 (SixW7.axOf bits 100288))

theorem wk185 : SixW7.walk table bits 46 100292 bx185 = some 100293 := by decide +kernel

noncomputable def bx186 : SixW7.Box := (bx184).setLo (SixW7.axOf bits 100288) (SixW7.Box.mid bx184 (SixW7.axOf bits 100288))

noncomputable def bx187 : SixW7.Box := (bx186).setHi (SixW7.axOf bits 100293) (SixW7.Box.mid bx186 (SixW7.axOf bits 100293))

theorem wk187 : SixW7.walk table bits 45 100297 bx187 = some 105233 := by decide +kernel

noncomputable def bx188 : SixW7.Box := (bx186).setLo (SixW7.axOf bits 100293) (SixW7.Box.mid bx186 (SixW7.axOf bits 100293))

theorem wk188 : SixW7.walk table bits 45 105233 bx188 = some 105334 := by decide +kernel

theorem wk186 : SixW7.walk table bits 46 100293 bx186 = some 105334 :=
  SixW7.walk_split table bits 45 100293 bx186 105233 105334 (by decide +kernel) wk187 wk188

theorem wk184 : SixW7.walk table bits 47 100288 bx184 = some 105334 :=
  SixW7.walk_split table bits 46 100288 bx184 100293 105334 (by decide +kernel) wk185 wk186

noncomputable def bx189 : SixW7.Box := (bx183).setLo (SixW7.axOf bits 100284) (SixW7.Box.mid bx183 (SixW7.axOf bits 100284))

theorem wk189 : SixW7.walk table bits 47 105334 bx189 = some 105450 := by decide +kernel

theorem wk183 : SixW7.walk table bits 48 100284 bx183 = some 105450 :=
  SixW7.walk_split table bits 47 100284 bx183 105334 105450 (by decide +kernel) wk184 wk189

theorem wk181 : SixW7.walk table bits 49 98649 bx181 = some 105450 :=
  SixW7.walk_split table bits 48 98649 bx181 100284 105450 (by decide +kernel) wk182 wk183

noncomputable def bx190 : SixW7.Box := (bx180).setLo (SixW7.axOf bits 98645) (SixW7.Box.mid bx180 (SixW7.axOf bits 98645))

theorem wk190 : SixW7.walk table bits 49 105450 bx190 = some 106891 := by decide +kernel

theorem wk180 : SixW7.walk table bits 50 98645 bx180 = some 106891 :=
  SixW7.walk_split table bits 49 98645 bx180 105450 106891 (by decide +kernel) wk181 wk190

theorem wk178 : SixW7.walk table bits 51 98615 bx178 = some 106891 :=
  SixW7.walk_split table bits 50 98615 bx178 98645 106891 (by decide +kernel) wk179 wk180

noncomputable def bx191 : SixW7.Box := (bx177).setLo (SixW7.axOf bits 98611) (SixW7.Box.mid bx177 (SixW7.axOf bits 98611))

theorem wk191 : SixW7.walk table bits 51 106891 bx191 = some 106937 := by decide +kernel

theorem wk177 : SixW7.walk table bits 52 98611 bx177 = some 106937 :=
  SixW7.walk_split table bits 51 98611 bx177 106891 106937 (by decide +kernel) wk178 wk191

theorem wk175 : SixW7.walk table bits 53 98451 bx175 = some 106937 :=
  SixW7.walk_split table bits 52 98451 bx175 98611 106937 (by decide +kernel) wk176 wk177

noncomputable def bx192 : SixW7.Box := (bx174).setLo (SixW7.axOf bits 98447) (SixW7.Box.mid bx174 (SixW7.axOf bits 98447))

theorem wk192 : SixW7.walk table bits 53 106937 bx192 = some 106958 := by decide +kernel

theorem wk174 : SixW7.walk table bits 54 98447 bx174 = some 106958 :=
  SixW7.walk_split table bits 53 98447 bx174 106937 106958 (by decide +kernel) wk175 wk192

noncomputable def bx193 : SixW7.Box := (bx173).setLo (SixW7.axOf bits 98443) (SixW7.Box.mid bx173 (SixW7.axOf bits 98443))

theorem wk193 : SixW7.walk table bits 54 106958 bx193 = some 107734 := by decide +kernel

theorem wk173 : SixW7.walk table bits 55 98443 bx173 = some 107734 :=
  SixW7.walk_split table bits 54 98443 bx173 106958 107734 (by decide +kernel) wk174 wk193

theorem wk171 : SixW7.walk table bits 56 98233 bx171 = some 107734 :=
  SixW7.walk_split table bits 55 98233 bx171 98443 107734 (by decide +kernel) wk172 wk173

noncomputable def bx194 : SixW7.Box := (bx170).setLo (SixW7.axOf bits 98229) (SixW7.Box.mid bx170 (SixW7.axOf bits 98229))

theorem wk194 : SixW7.walk table bits 56 107734 bx194 = some 107780 := by decide +kernel

theorem wk170 : SixW7.walk table bits 57 98229 bx170 = some 107780 :=
  SixW7.walk_split table bits 56 98229 bx170 107734 107780 (by decide +kernel) wk171 wk194

noncomputable def bx195 : SixW7.Box := (bx169).setLo (SixW7.axOf bits 98225) (SixW7.Box.mid bx169 (SixW7.axOf bits 98225))

theorem wk195 : SixW7.walk table bits 57 107780 bx195 = some 107951 := by decide +kernel

theorem wk169 : SixW7.walk table bits 58 98225 bx169 = some 107951 :=
  SixW7.walk_split table bits 57 98225 bx169 107780 107951 (by decide +kernel) wk170 wk195

noncomputable def bx196 : SixW7.Box := (bx168).setLo (SixW7.axOf bits 98221) (SixW7.Box.mid bx168 (SixW7.axOf bits 98221))

theorem wk196 : SixW7.walk table bits 58 107951 bx196 = some 108202 := by decide +kernel

theorem wk168 : SixW7.walk table bits 59 98221 bx168 = some 108202 :=
  SixW7.walk_split table bits 58 98221 bx168 107951 108202 (by decide +kernel) wk169 wk196

noncomputable def bx197 : SixW7.Box := (bx167).setLo (SixW7.axOf bits 98217) (SixW7.Box.mid bx167 (SixW7.axOf bits 98217))

theorem wk197 : SixW7.walk table bits 59 108202 bx197 = some 108228 := by decide +kernel

theorem wk167 : SixW7.walk table bits 60 98217 bx167 = some 108228 :=
  SixW7.walk_split table bits 59 98217 bx167 108202 108228 (by decide +kernel) wk168 wk197

noncomputable def bx198 : SixW7.Box := (bx166).setLo (SixW7.axOf bits 98213) (SixW7.Box.mid bx166 (SixW7.axOf bits 98213))

theorem wk198 : SixW7.walk table bits 60 108228 bx198 = some 108269 := by decide +kernel

theorem wk166 : SixW7.walk table bits 61 98213 bx166 = some 108269 :=
  SixW7.walk_split table bits 60 98213 bx166 108228 108269 (by decide +kernel) wk167 wk198

noncomputable def bx199 : SixW7.Box := (bx165).setLo (SixW7.axOf bits 98209) (SixW7.Box.mid bx165 (SixW7.axOf bits 98209))

theorem wk199 : SixW7.walk table bits 61 108269 bx199 = some 108285 := by decide +kernel

theorem wk165 : SixW7.walk table bits 62 98209 bx165 = some 108285 :=
  SixW7.walk_split table bits 61 98209 bx165 108269 108285 (by decide +kernel) wk166 wk199

noncomputable def bx200 : SixW7.Box := (bx164).setLo (SixW7.axOf bits 98205) (SixW7.Box.mid bx164 (SixW7.axOf bits 98205))

theorem wk200 : SixW7.walk table bits 62 108285 bx200 = some 108286 := by decide +kernel

theorem wk164 : SixW7.walk table bits 63 98205 bx164 = some 108286 :=
  SixW7.walk_split table bits 62 98205 bx164 108285 108286 (by decide +kernel) wk165 wk200

noncomputable def bx201 : SixW7.Box := (bx163).setLo (SixW7.axOf bits 98201) (SixW7.Box.mid bx163 (SixW7.axOf bits 98201))

theorem wk201 : SixW7.walk table bits 63 108286 bx201 = some 108287 := by decide +kernel

theorem wk163 : SixW7.walk table bits 64 98201 bx163 = some 108287 :=
  SixW7.walk_split table bits 63 98201 bx163 108286 108287 (by decide +kernel) wk164 wk201

noncomputable def bx202 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 59904 74752 30720 40448)

theorem wk202 : SixW7.walk table bits 64 108287 bx202 = some 108288 := by decide +kernel

noncomputable def bx203 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 59904 74752 57344 442368)

theorem wk203 : SixW7.walk table bits 64 108288 bx203 = some 109024 := by decide +kernel

noncomputable def bx204 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 88064 262144 30720 40448)

theorem wk204 : SixW7.walk table bits 64 109024 bx204 = some 109025 := by decide +kernel

noncomputable def bx205 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 60416 74240 88064 262144 57344 442368)

theorem wk205 : SixW7.walk table bits 64 109025 bx205 = some 109101 := by decide +kernel

noncomputable def bx206 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 31744 38400 30720 40448)

theorem wk206 : SixW7.walk table bits 64 109101 bx206 = some 109102 := by decide +kernel

noncomputable def bx207 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 31744 38400 57344 442368)

theorem wk207 : SixW7.walk table bits 64 109102 bx207 = some 109488 := by decide +kernel

noncomputable def bx208 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 59904 74752 30720 40448)

theorem wk208 : SixW7.walk table bits 64 109488 bx208 = some 109489 := by decide +kernel

noncomputable def bx209 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 59904 74752 57344 442368)

theorem wk209 : SixW7.walk table bits 64 109489 bx209 = some 109550 := by decide +kernel

noncomputable def bx210 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 88064 262144 30720 40448)

theorem wk210 : SixW7.walk table bits 64 109550 bx210 = some 109551 := by decide +kernel

noncomputable def bx211 : SixW7.Box := (SixW7.Box.mk 57344 442368 31744 38400 89088 237568 88064 262144 57344 442368)

theorem wk211 : SixW7.walk table bits 64 109551 bx211 = some 109552 := by decide +kernel

noncomputable def bx212 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 31744 38400 30720 40448)

theorem wk212 : SixW7.walk table bits 64 109552 bx212 = some 109553 := by decide +kernel

noncomputable def bx213 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 31744 38400 57344 442368)

theorem wk213 : SixW7.walk table bits 64 109553 bx213 = some 114074 := by decide +kernel

noncomputable def bx214 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 59904 74752 30720 40448)

theorem wk214 : SixW7.walk table bits 64 114074 bx214 = some 114075 := by decide +kernel

noncomputable def bx215 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 59904 74752 57344 442368)

theorem wk215 : SixW7.walk table bits 64 114075 bx215 = some 115501 := by decide +kernel

noncomputable def bx216 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 88064 262144 30720 40448)

theorem wk216 : SixW7.walk table bits 64 115501 bx216 = some 115502 := by decide +kernel

noncomputable def bx217 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 31744 38400 88064 262144 57344 442368)

theorem wk217 : SixW7.walk table bits 64 115502 bx217 = some 115588 := by decide +kernel

noncomputable def bx218 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 31744 38400 30720 40448)

theorem wk218 : SixW7.walk table bits 64 115588 bx218 = some 115589 := by decide +kernel

noncomputable def bx219 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 31744 38400 57344 442368)

theorem wk219 : SixW7.walk table bits 64 115589 bx219 = some 116325 := by decide +kernel

noncomputable def bx220 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 59904 74752 30720 40448)

theorem wk220 : SixW7.walk table bits 64 116325 bx220 = some 116326 := by decide +kernel

noncomputable def bx221 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 59904 74752 57344 442368)

theorem wk221 : SixW7.walk table bits 64 116326 bx221 = some 116387 := by decide +kernel

noncomputable def bx222 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 88064 262144 30720 40448)

theorem wk222 : SixW7.walk table bits 64 116387 bx222 = some 116388 := by decide +kernel

noncomputable def bx223 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 60416 74240 88064 262144 57344 442368)

theorem wk223 : SixW7.walk table bits 64 116388 bx223 = some 116389 := by decide +kernel

noncomputable def bx224 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 31744 38400 30720 40448)

theorem wk224 : SixW7.walk table bits 64 116389 bx224 = some 116390 := by decide +kernel

noncomputable def bx225 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 31744 38400 57344 442368)

theorem wk225 : SixW7.walk table bits 64 116390 bx225 = some 116451 := by decide +kernel

noncomputable def bx226 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 59904 74752 30720 40448)

theorem wk226 : SixW7.walk table bits 64 116451 bx226 = some 116452 := by decide +kernel

noncomputable def bx227 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 59904 74752 57344 442368)

theorem wk227 : SixW7.walk table bits 64 116452 bx227 = some 116453 := by decide +kernel

noncomputable def bx228 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 88064 262144 30720 40448)

theorem wk228 : SixW7.walk table bits 64 116453 bx228 = some 116454 := by decide +kernel

noncomputable def bx229 : SixW7.Box := (SixW7.Box.mk 57344 442368 59904 74752 89088 237568 88064 262144 57344 442368)

theorem wk229 : SixW7.walk table bits 64 116454 bx229 = some 116455 := by decide +kernel

noncomputable def bx230 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 31744 38400 30720 40448)

theorem wk230 : SixW7.walk table bits 64 116455 bx230 = some 116456 := by decide +kernel

noncomputable def bx231 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 31744 38400 57344 442368)

theorem wk231 : SixW7.walk table bits 64 116456 bx231 = some 116987 := by decide +kernel

noncomputable def bx232 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 59904 74752 30720 40448)

theorem wk232 : SixW7.walk table bits 64 116987 bx232 = some 116988 := by decide +kernel

noncomputable def bx233 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 59904 74752 57344 442368)

theorem wk233 : SixW7.walk table bits 64 116988 bx233 = some 117074 := by decide +kernel

noncomputable def bx234 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 88064 262144 30720 40448)

theorem wk234 : SixW7.walk table bits 64 117074 bx234 = some 117075 := by decide +kernel

noncomputable def bx235 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 31744 38400 88064 262144 57344 442368)

theorem wk235 : SixW7.walk table bits 64 117075 bx235 = some 117076 := by decide +kernel

noncomputable def bx236 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 31744 38400 30720 40448)

theorem wk236 : SixW7.walk table bits 64 117076 bx236 = some 117077 := by decide +kernel

noncomputable def bx237 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 31744 38400 57344 442368)

theorem wk237 : SixW7.walk table bits 64 117077 bx237 = some 117153 := by decide +kernel

noncomputable def bx238 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 59904 74752 30720 40448)

theorem wk238 : SixW7.walk table bits 64 117153 bx238 = some 117154 := by decide +kernel

noncomputable def bx239 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 59904 74752 57344 442368)

theorem wk239 : SixW7.walk table bits 64 117154 bx239 = some 117155 := by decide +kernel

noncomputable def bx240 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 88064 262144 30720 40448)

theorem wk240 : SixW7.walk table bits 64 117155 bx240 = some 117156 := by decide +kernel

noncomputable def bx241 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 60416 74240 88064 262144 57344 442368)

theorem wk241 : SixW7.walk table bits 64 117156 bx241 = some 117157 := by decide +kernel

noncomputable def bx242 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 31744 38400 30720 40448)

theorem wk242 : SixW7.walk table bits 64 117157 bx242 = some 117158 := by decide +kernel

noncomputable def bx243 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 31744 38400 57344 442368)

theorem wk243 : SixW7.walk table bits 64 117158 bx243 = some 117159 := by decide +kernel

noncomputable def bx244 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 59904 74752 30720 40448)

theorem wk244 : SixW7.walk table bits 64 117159 bx244 = some 117160 := by decide +kernel

noncomputable def bx245 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 59904 74752 57344 442368)

theorem wk245 : SixW7.walk table bits 64 117160 bx245 = some 117161 := by decide +kernel

noncomputable def bx246 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 88064 262144 30720 40448)

theorem wk246 : SixW7.walk table bits 64 117161 bx246 = some 117162 := by decide +kernel

noncomputable def bx247 : SixW7.Box := (SixW7.Box.mk 57344 442368 88064 262144 89088 237568 88064 262144 57344 442368)

theorem wk247 : SixW7.walk table bits 64 117162 bx247 = some 117163 := by decide +kernel

theorem nb0_eq : (SixW7.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW7.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW7.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW7.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW7.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW7.walk table bits 64 0 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 0 0) = some 1431 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 0 0 = bx0 from by decide +kernel]; exact wk0

theorem root_00001 : SixW7.walk table bits 64 1431 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 0 1) = some 5407 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 0 1 = bx1 from by decide +kernel]; exact wk1

theorem root_00010 : SixW7.walk table bits 64 5407 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 1 0) = some 9188 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 1 0 = bx2 from by decide +kernel]; exact wk2

theorem root_00011 : SixW7.walk table bits 64 9188 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 1 1) = some 13399 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 1 1 = bx3 from by decide +kernel]; exact wk3

theorem root_00020 : SixW7.walk table bits 64 13399 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 2 0) = some 14830 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 2 0 = bx4 from by decide +kernel]; exact wk4

theorem root_00021 : SixW7.walk table bits 64 14830 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 2 1) = some 15791 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 0 2 1 = bx5 from by decide +kernel]; exact wk5

theorem root_00100 : SixW7.walk table bits 64 15791 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 0 0) = some 20022 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 0 0 = bx6 from by decide +kernel]; exact wk6

theorem root_00101 : SixW7.walk table bits 64 20022 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 0 1) = some 27343 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 0 1 = bx7 from by decide +kernel]; exact wk7

theorem root_00110 : SixW7.walk table bits 64 27343 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 1 0) = some 30879 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 1 0 = bx20 from by decide +kernel]; exact wk20

theorem root_00111 : SixW7.walk table bits 64 30879 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 1 1) = some 32420 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 1 1 = bx21 from by decide +kernel]; exact wk21

theorem root_00120 : SixW7.walk table bits 64 32420 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 2 0) = some 32796 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 2 0 = bx22 from by decide +kernel]; exact wk22

theorem root_00121 : SixW7.walk table bits 64 32796 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 2 1) = some 32952 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 1 2 1 = bx23 from by decide +kernel]; exact wk23

theorem root_00200 : SixW7.walk table bits 64 32952 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 0 0) = some 34388 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 0 0 = bx24 from by decide +kernel]; exact wk24

theorem root_00201 : SixW7.walk table bits 64 34388 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 0 1) = some 35419 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 0 1 = bx25 from by decide +kernel]; exact wk25

theorem root_00210 : SixW7.walk table bits 64 35419 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 1 0) = some 35710 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 1 0 = bx26 from by decide +kernel]; exact wk26

theorem root_00211 : SixW7.walk table bits 64 35710 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 1 1) = some 35826 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 1 1 = bx27 from by decide +kernel]; exact wk27

theorem root_00220 : SixW7.walk table bits 64 35826 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 2 0) = some 35877 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 2 0 = bx28 from by decide +kernel]; exact wk28

theorem root_00221 : SixW7.walk table bits 64 35877 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 2 1) = some 35878 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 0 2 2 1 = bx29 from by decide +kernel]; exact wk29

theorem root_01000 : SixW7.walk table bits 64 35878 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 0 0) = some 39469 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 0 0 = bx30 from by decide +kernel]; exact wk30

theorem root_01001 : SixW7.walk table bits 64 39469 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 0 1) = some 49300 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 0 1 = bx31 from by decide +kernel]; exact wk31

theorem root_01010 : SixW7.walk table bits 64 49300 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 1 0) = some 65031 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 1 0 = bx54 from by decide +kernel]; exact wk54

theorem root_01011 : SixW7.walk table bits 64 65031 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 1 1) = some 71792 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 1 1 = bx85 from by decide +kernel]; exact wk85

theorem root_01020 : SixW7.walk table bits 64 71792 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 2 0) = some 72698 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 2 0 = bx112 from by decide +kernel]; exact wk112

theorem root_01021 : SixW7.walk table bits 64 72698 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 2 1) = some 72889 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 0 2 1 = bx113 from by decide +kernel]; exact wk113

theorem root_01100 : SixW7.walk table bits 64 72889 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 0 0) = some 76210 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 0 0 = bx114 from by decide +kernel]; exact wk114

theorem root_01101 : SixW7.walk table bits 64 76210 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 0 1) = some 81756 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 0 1 = bx115 from by decide +kernel]; exact wk115

theorem root_01110 : SixW7.walk table bits 64 81756 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 1 0) = some 82762 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 1 0 = bx128 from by decide +kernel]; exact wk128

theorem root_01111 : SixW7.walk table bits 64 82762 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 1 1) = some 82903 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 1 1 = bx129 from by decide +kernel]; exact wk129

theorem root_01120 : SixW7.walk table bits 64 82903 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 2 0) = some 82939 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 2 0 = bx130 from by decide +kernel]; exact wk130

theorem root_01121 : SixW7.walk table bits 64 82939 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 2 1) = some 82940 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 1 2 1 = bx131 from by decide +kernel]; exact wk131

theorem root_01200 : SixW7.walk table bits 64 82940 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 0 0) = some 83221 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 0 0 = bx132 from by decide +kernel]; exact wk132

theorem root_01201 : SixW7.walk table bits 64 83221 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 0 1) = some 83332 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 0 1 = bx133 from by decide +kernel]; exact wk133

theorem root_01210 : SixW7.walk table bits 64 83332 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 1 0) = some 83358 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 1 0 = bx134 from by decide +kernel]; exact wk134

theorem root_01211 : SixW7.walk table bits 64 83358 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 1 1) = some 83359 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 1 1 = bx135 from by decide +kernel]; exact wk135

theorem root_01220 : SixW7.walk table bits 64 83359 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 2 0) = some 83360 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 2 0 = bx136 from by decide +kernel]; exact wk136

theorem root_01221 : SixW7.walk table bits 64 83360 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 2 1) = some 83361 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 1 2 2 1 = bx137 from by decide +kernel]; exact wk137

theorem root_02000 : SixW7.walk table bits 64 83361 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 0 0) = some 84702 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 0 0 = bx138 from by decide +kernel]; exact wk138

theorem root_02001 : SixW7.walk table bits 64 84702 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 0 1) = some 86468 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 0 1 = bx139 from by decide +kernel]; exact wk139

theorem root_02010 : SixW7.walk table bits 64 86468 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 1 0) = some 87374 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 1 0 = bx140 from by decide +kernel]; exact wk140

theorem root_02011 : SixW7.walk table bits 64 87374 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 1 1) = some 87570 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 1 1 = bx141 from by decide +kernel]; exact wk141

theorem root_02020 : SixW7.walk table bits 64 87570 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 2 0) = some 87641 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 2 0 = bx142 from by decide +kernel]; exact wk142

theorem root_02021 : SixW7.walk table bits 64 87641 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 2 1) = some 87642 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 0 2 1 = bx143 from by decide +kernel]; exact wk143

theorem root_02100 : SixW7.walk table bits 64 87642 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 0 0) = some 87993 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 0 0 = bx144 from by decide +kernel]; exact wk144

theorem root_02101 : SixW7.walk table bits 64 87993 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 0 1) = some 88144 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 0 1 = bx145 from by decide +kernel]; exact wk145

theorem root_02110 : SixW7.walk table bits 64 88144 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 1 0) = some 88180 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 1 0 = bx146 from by decide +kernel]; exact wk146

theorem root_02111 : SixW7.walk table bits 64 88180 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 1 1) = some 88181 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 1 1 = bx147 from by decide +kernel]; exact wk147

theorem root_02120 : SixW7.walk table bits 64 88181 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 2 0) = some 88182 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 2 0 = bx148 from by decide +kernel]; exact wk148

theorem root_02121 : SixW7.walk table bits 64 88182 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 2 1) = some 88183 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 1 2 1 = bx149 from by decide +kernel]; exact wk149

theorem root_02200 : SixW7.walk table bits 64 88183 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 0 0) = some 88234 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 0 0 = bx150 from by decide +kernel]; exact wk150

theorem root_02201 : SixW7.walk table bits 64 88234 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 0 1) = some 88235 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 0 1 = bx151 from by decide +kernel]; exact wk151

theorem root_02210 : SixW7.walk table bits 64 88235 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 1 0) = some 88236 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 1 0 = bx152 from by decide +kernel]; exact wk152

theorem root_02211 : SixW7.walk table bits 64 88236 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 1 1) = some 88237 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 1 1 = bx153 from by decide +kernel]; exact wk153

theorem root_02220 : SixW7.walk table bits 64 88237 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 2 0) = some 88238 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 2 0 = bx154 from by decide +kernel]; exact wk154

theorem root_02221 : SixW7.walk table bits 64 88238 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 2 1) = some 88239 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 0 2 2 2 1 = bx155 from by decide +kernel]; exact wk155

theorem root_10000 : SixW7.walk table bits 64 88239 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 0 0) = some 88240 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 0 0 = bx156 from by decide +kernel]; exact wk156

theorem root_10001 : SixW7.walk table bits 64 88240 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 0 1) = some 92756 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 0 1 = bx157 from by decide +kernel]; exact wk157

theorem root_10010 : SixW7.walk table bits 64 92756 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 1 0) = some 92757 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 1 0 = bx158 from by decide +kernel]; exact wk158

theorem root_10011 : SixW7.walk table bits 64 92757 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 1 1) = some 97678 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 1 1 = bx159 from by decide +kernel]; exact wk159

theorem root_10020 : SixW7.walk table bits 64 97678 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 2 0) = some 97679 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 2 0 = bx160 from by decide +kernel]; exact wk160

theorem root_10021 : SixW7.walk table bits 64 97679 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 2 1) = some 98200 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 0 2 1 = bx161 from by decide +kernel]; exact wk161

theorem root_10100 : SixW7.walk table bits 64 98200 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 0 0) = some 98201 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 0 0 = bx162 from by decide +kernel]; exact wk162

theorem root_10101 : SixW7.walk table bits 64 98201 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 0 1) = some 108287 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 0 1 = bx163 from by decide +kernel]; exact wk163

theorem root_10110 : SixW7.walk table bits 64 108287 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 1 0) = some 108288 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 1 0 = bx202 from by decide +kernel]; exact wk202

theorem root_10111 : SixW7.walk table bits 64 108288 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 1 1) = some 109024 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 1 1 = bx203 from by decide +kernel]; exact wk203

theorem root_10120 : SixW7.walk table bits 64 109024 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 2 0) = some 109025 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 2 0 = bx204 from by decide +kernel]; exact wk204

theorem root_10121 : SixW7.walk table bits 64 109025 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 2 1) = some 109101 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 1 2 1 = bx205 from by decide +kernel]; exact wk205

theorem root_10200 : SixW7.walk table bits 64 109101 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 0 0) = some 109102 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 0 0 = bx206 from by decide +kernel]; exact wk206

theorem root_10201 : SixW7.walk table bits 64 109102 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 0 1) = some 109488 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 0 1 = bx207 from by decide +kernel]; exact wk207

theorem root_10210 : SixW7.walk table bits 64 109488 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 1 0) = some 109489 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 1 0 = bx208 from by decide +kernel]; exact wk208

theorem root_10211 : SixW7.walk table bits 64 109489 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 1 1) = some 109550 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 1 1 = bx209 from by decide +kernel]; exact wk209

theorem root_10220 : SixW7.walk table bits 64 109550 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 2 0) = some 109551 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 2 0 = bx210 from by decide +kernel]; exact wk210

theorem root_10221 : SixW7.walk table bits 64 109551 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 2 1) = some 109552 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 0 2 2 1 = bx211 from by decide +kernel]; exact wk211

theorem root_11000 : SixW7.walk table bits 64 109552 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 0 0) = some 109553 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 0 0 = bx212 from by decide +kernel]; exact wk212

theorem root_11001 : SixW7.walk table bits 64 109553 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 0 1) = some 114074 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 0 1 = bx213 from by decide +kernel]; exact wk213

theorem root_11010 : SixW7.walk table bits 64 114074 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 1 0) = some 114075 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 1 0 = bx214 from by decide +kernel]; exact wk214

theorem root_11011 : SixW7.walk table bits 64 114075 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 1 1) = some 115501 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 1 1 = bx215 from by decide +kernel]; exact wk215

theorem root_11020 : SixW7.walk table bits 64 115501 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 2 0) = some 115502 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 2 0 = bx216 from by decide +kernel]; exact wk216

theorem root_11021 : SixW7.walk table bits 64 115502 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 2 1) = some 115588 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 0 2 1 = bx217 from by decide +kernel]; exact wk217

theorem root_11100 : SixW7.walk table bits 64 115588 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 0 0) = some 115589 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 0 0 = bx218 from by decide +kernel]; exact wk218

theorem root_11101 : SixW7.walk table bits 64 115589 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 0 1) = some 116325 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 0 1 = bx219 from by decide +kernel]; exact wk219

theorem root_11110 : SixW7.walk table bits 64 116325 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 1 0) = some 116326 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 1 0 = bx220 from by decide +kernel]; exact wk220

theorem root_11111 : SixW7.walk table bits 64 116326 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 1 1) = some 116387 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 1 1 = bx221 from by decide +kernel]; exact wk221

theorem root_11120 : SixW7.walk table bits 64 116387 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 2 0) = some 116388 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 2 0 = bx222 from by decide +kernel]; exact wk222

theorem root_11121 : SixW7.walk table bits 64 116388 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 2 1) = some 116389 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 1 2 1 = bx223 from by decide +kernel]; exact wk223

theorem root_11200 : SixW7.walk table bits 64 116389 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 0 0) = some 116390 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 0 0 = bx224 from by decide +kernel]; exact wk224

theorem root_11201 : SixW7.walk table bits 64 116390 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 0 1) = some 116451 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 0 1 = bx225 from by decide +kernel]; exact wk225

theorem root_11210 : SixW7.walk table bits 64 116451 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 1 0) = some 116452 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 1 0 = bx226 from by decide +kernel]; exact wk226

theorem root_11211 : SixW7.walk table bits 64 116452 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 1 1) = some 116453 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 1 1 = bx227 from by decide +kernel]; exact wk227

theorem root_11220 : SixW7.walk table bits 64 116453 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 2 0) = some 116454 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 2 0 = bx228 from by decide +kernel]; exact wk228

theorem root_11221 : SixW7.walk table bits 64 116454 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 2 1) = some 116455 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 1 2 2 1 = bx229 from by decide +kernel]; exact wk229

theorem root_12000 : SixW7.walk table bits 64 116455 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 0 0) = some 116456 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 0 0 = bx230 from by decide +kernel]; exact wk230

theorem root_12001 : SixW7.walk table bits 64 116456 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 0 1) = some 116987 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 0 1 = bx231 from by decide +kernel]; exact wk231

theorem root_12010 : SixW7.walk table bits 64 116987 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 1 0) = some 116988 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 1 0 = bx232 from by decide +kernel]; exact wk232

theorem root_12011 : SixW7.walk table bits 64 116988 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 1 1) = some 117074 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 1 1 = bx233 from by decide +kernel]; exact wk233

theorem root_12020 : SixW7.walk table bits 64 117074 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 2 0) = some 117075 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 2 0 = bx234 from by decide +kernel]; exact wk234

theorem root_12021 : SixW7.walk table bits 64 117075 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 2 1) = some 117076 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 0 2 1 = bx235 from by decide +kernel]; exact wk235

theorem root_12100 : SixW7.walk table bits 64 117076 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 0 0) = some 117077 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 0 0 = bx236 from by decide +kernel]; exact wk236

theorem root_12101 : SixW7.walk table bits 64 117077 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 0 1) = some 117153 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 0 1 = bx237 from by decide +kernel]; exact wk237

theorem root_12110 : SixW7.walk table bits 64 117153 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 1 0) = some 117154 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 1 0 = bx238 from by decide +kernel]; exact wk238

theorem root_12111 : SixW7.walk table bits 64 117154 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 1 1) = some 117155 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 1 1 = bx239 from by decide +kernel]; exact wk239

theorem root_12120 : SixW7.walk table bits 64 117155 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 2 0) = some 117156 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 2 0 = bx240 from by decide +kernel]; exact wk240

theorem root_12121 : SixW7.walk table bits 64 117156 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 2 1) = some 117157 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 1 2 1 = bx241 from by decide +kernel]; exact wk241

theorem root_12200 : SixW7.walk table bits 64 117157 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 0 0) = some 117158 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 0 0 = bx242 from by decide +kernel]; exact wk242

theorem root_12201 : SixW7.walk table bits 64 117158 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 0 1) = some 117159 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 0 1 = bx243 from by decide +kernel]; exact wk243

theorem root_12210 : SixW7.walk table bits 64 117159 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 1 0) = some 117160 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 1 0 = bx244 from by decide +kernel]; exact wk244

theorem root_12211 : SixW7.walk table bits 64 117160 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 1 1) = some 117161 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 1 1 = bx245 from by decide +kernel]; exact wk245

theorem root_12220 : SixW7.walk table bits 64 117161 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 2 0) = some 117162 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 2 0 = bx246 from by decide +kernel]; exact wk246

theorem root_12221 : SixW7.walk table bits 64 117162 (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 2 1) = some 117163 := by
  rw [show SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) 1 2 2 2 1 = bx247 from by decide +kernel]; exact wk247

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW7.badOf cover0).length → i1 < (SixW7.badOf cover1).length → i2 < (SixW7.badOf cover2).length → i3 < (SixW7.badOf cover3).length → i4 < (SixW7.badOf cover4).length →
    ∃ pos pos', SixW7.walk table bits 64 pos (SixW7.boxOf (SixW7.badOf cover0) (SixW7.badOf cover1) (SixW7.badOf cover2) (SixW7.badOf cover3) (SixW7.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
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

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW7.cN : ℝ) / SixW7.SA ≤ SixW7.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW7.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 442368 262144 237568 262144 442368
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW7Data

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

/-! ###### the 6-point weighted bound from the checked certificate `SixW7` ###### -/

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

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW7.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW7.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW7.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW7.SA]
  try ring

theorem G_rev (x0 x1 x2 x3 x4 : ℝ) : SixW7.G x4 x3 x2 x1 x0 = SixW7.G x0 x1 x2 x3 x4 := by
  unfold SixW7.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (SixW7.cN : ℝ) / SixW7.SA ≤ SixW7.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases SixW7Data.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases SixW7Data.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (333207 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW7.cN, SixW7.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 305 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((333207 : ℝ) / 100000000) 305 ((179997 : ℝ) / 100000000)
    = (305000000 * HD 1 - 539991) / 304000379 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((305000000 * HD 1 - 539991) / 304000379 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((333207 : ℝ) / 100000000) 305 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (305000000 * HD 1 - 539991) / 304000379 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 304000379)]
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
      ≤ ((305000000 * HD 1 - 539991) / 304000379 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
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
