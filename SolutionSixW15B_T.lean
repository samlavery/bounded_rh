/-
Riemann.fail submission — an unconditional critical-line proportion of 0.6727382,
strictly above the pinned record 2 − 1/cMT = 0.67250070…

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned
Zeta23 development (the Montgomery–Taylor window at λ = 1), specialised to n = 3 and made
unconditional by a kernel-checked finite certificate (`three_point_cert`: 368 interval cell
lemmas and 487 leaves of a two-dimensional bisection), assembled with the window-count
pressure bookkeeping (`n_point_bound_w'`).  The resulting constant is
`(447000000·H − 297200)/446400399 = 0.67273822…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`,
and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places
the exact rational `3363691/5000000` strictly between the record and the proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib;
no placeholders, no `native_decide`, no additional axioms.  Sources: the Zeta Lab bridge
(`Zeta23Ext.Bridge`, `Zeta23Ext.BridgeW`, `ThreePoint`), MIT-licensed, ported here into one
file; the counting functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.ThmD.Mult
import Zeta23.ThmD.ZeroSideD
import Zeta23.PrimeSideA.EndsE1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Zeta23.Main
import Zeta23.Final
import Zeta23.Statement.SeamClosed
import Zeta23.ThmD.Functional

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

/-! ###### verified certificate checker: rational cells, chains, boxes, cover ###### -/

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

/-! ### Boxes and bisection trees for the four-point functional -/

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

/-- The four-point functional written out on the three gaps. -/
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

/-! ### The four-point certificate from a checked table -/

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

/-- The four-point functional, written out. -/
lemma F4_eq (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)
      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2) := by
  simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### natural-number checker for the 6-point weighted certificate `SixW15B` ###### -/

section SixW15BDefs

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

/-- the rational cell a natural-number cell denotes -/
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
/-- the integer check -/
def okZ (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (DZ * DZ < 2 * c.BLZ * c.BLZ) && decide (0 < c.DHIZ)
    && decide ((c.WN : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
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

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 13) + 1) <<< 13
      bif Nat.blt q hi then (a, q) :: piecesN fuel q hi else [(a, hi)]

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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15B

def SA : ℕ := 100000000
def cN : ℕ := 304544

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
  Nat.ble (cN * SC * SW) ((25232 * b.l0 + 42025 * b.l1 + 46137 * b.l2 + 42044 * b.l3 + 24559 * b.l4) * SW + (25715100 * termWN tb (b.l0) (b.u0) + 61242800 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 40905100 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 104929600 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) + 200000000 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) + 48318100 * termWN tb (b.l1) (b.u1) + 40072400 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 119746800 * termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) + 95070300 * termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) + 52857300 * termWN tb (b.l2) (b.u2) + 35189000 * termWN tb (b.l2 + b.l3) (b.u2 + b.u3) + 39348000 * termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) + 48170700 * termWN tb (b.l3) (b.u3) + 63495600 * termWN tb (b.l3 + b.l4) (b.u3 + b.u4) + 24938600 * termWN tb (b.l4) (b.u4)) * SC)

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
      else bif leafCheck tb b then some (pos + 1) else none

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

end Zeta23Ext.Bridge.ThreePoint.SixW15B

end SixW15BDefs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the natural-number cell table (through the rational cell) -/

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
theorem cellN_soundZ (c : CellN) (h : c.okZ = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩, hW⟩ := h
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
  have hWr : ((c.WN : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)
      ≤ ((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ) * ((SW : ℕ) : ℝ) := by exact_mod_cast hW
  have hDHpos : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
  have e : (((c.NLOZ : ℤ) : ℝ) / DZ / (((c.DHIZ : ℤ) : ℝ) / DZ))^2
      = (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_div_div_cancel_right₀ DZ_ne]; ring
  have hle : ((c.WN : ℕ) : ℝ) / SW
      ≤ (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_le_div_iff₀ hSW (mul_pos hDHpos hDHpos)]
    calc ((c.WN : ℕ) : ℝ) * (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ))
        = ((c.WN : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) := by ring
      _ ≤ _ := hWr
  rw [← e] at hle
  exact hle.trans hfin
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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15B

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (25232 / (SA:ℝ)) * g0 + (42025 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42044 / (SA:ℝ)) * g3 + (24559 / (SA:ℝ)) * g4
    + (25715100 / (SA:ℝ)) * wfun (g0) + (61242800 / (SA:ℝ)) * wfun (g0 + g1) + (40905100 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (104929600 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48318100 / (SA:ℝ)) * wfun (g1) + (40072400 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (95070300 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (35189000 / (SA:ℝ)) * wfun (g2 + g3) + (39348000 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48170700 / (SA:ℝ)) * wfun (g3) + (63495600 / (SA:ℝ)) * wfun (g3 + g4) + (24938600 / (SA:ℝ)) * wfun (g4)

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
  set L : ℝ := 25232 * ((b.l0 : ℝ) / SC) + 42025 * ((b.l1 : ℝ) / SC) + 46137 * ((b.l2 : ℝ) / SC) + 42044 * ((b.l3 : ℝ) / SC) + 24559 * ((b.l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25715100 * ((termWN tb (b.l0) (b.u0) : ℝ) / SW) + 61242800 * ((termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) / SW) + 40905100 * ((termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) / SW) + 104929600 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) / SW) + 200000000 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48318100 * ((termWN tb (b.l1) (b.u1) : ℝ) / SW) + 40072400 * ((termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) / SW) + 119746800 * ((termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) / SW) + 95070300 * ((termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 52857300 * ((termWN tb (b.l2) (b.u2) : ℝ) / SW) + 35189000 * ((termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) / SW) + 39348000 * ((termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48170700 * ((termWN tb (b.l3) (b.u3) : ℝ) / SW) + 63495600 * ((termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) / SW) + 24938600 * ((termWN tb (b.l4) (b.u4) : ℝ) / SW) with hWt
  have e : (L + Wt) * (SC * SW) = (25232 * (b.l0 : ℝ) + 42025 * (b.l1 : ℝ) + 46137 * (b.l2 : ℝ) + 42044 * (b.l3 : ℝ) + 24559 * (b.l4 : ℝ)) * SW + (25715100 * (termWN tb (b.l0) (b.u0) : ℝ) + 61242800 * (termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) + 40905100 * (termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) + 104929600 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) + 200000000 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 48318100 * (termWN tb (b.l1) (b.u1) : ℝ) + 40072400 * (termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) + 119746800 * (termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) + 95070300 * (termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 52857300 * (termWN tb (b.l2) (b.u2) : ℝ) + 35189000 * (termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) + 39348000 * (termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) + 48170700 * (termWN tb (b.l3) (b.u3) : ℝ) + 63495600 * (termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) + 24938600 * (termWN tb (b.l4) (b.u4) : ℝ)) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((25232 / (SA:ℝ)) * g0 + (42025 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42044 / (SA:ℝ)) * g3 + (24559 / (SA:ℝ)) * g4
      + (25715100 / (SA:ℝ)) * wfun (g0) + (61242800 / (SA:ℝ)) * wfun (g0 + g1) + (40905100 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (104929600 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48318100 / (SA:ℝ)) * wfun (g1) + (40072400 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (95070300 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (35189000 / (SA:ℝ)) * wfun (g2 + g3) + (39348000 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48170700 / (SA:ℝ)) * wfun (g3) + (63495600 / (SA:ℝ)) * wfun (g3 + g4) + (24938600 / (SA:ℝ)) * wfun (g4)) * SA
      = 25232 * g0 + 42025 * g1 + 46137 * g2 + 42044 * g3 + 24559 * g4 + 25715100 * wfun (g0) + 61242800 * wfun (g0 + g1) + 40905100 * wfun (g0 + g1 + g2) + 104929600 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48318100 * wfun (g1) + 40072400 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 95070300 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 35189000 * wfun (g2 + g3) + 39348000 * wfun (g2 + g3 + g4) + 48170700 * wfun (g3) + 63495600 * wfun (g3 + g4) + 24938600 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 25232), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42025), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42044), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24559), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25715100), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 61242800), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40905100), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 104929600), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48318100), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 40072400), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 95070300), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 35189000), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 39348000), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48170700), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 63495600), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 24938600)]

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
      ∀ g0 g1 g2 g3 g4 : ℝ, b.mem g0 g1 g2 g3 g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
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
    · exact leaf_sound tb hok b hleaf g0 g1 g2 g3 g4 hm

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
    (hS0 : cN * SC ≤ 25232 * S0) (hS1 : cN * SC ≤ 42025 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42044 * S3) (hS4 : cN * SC ≤ 24559 * S4)
    (hcov0 : coverCheck tb 25715100 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck tb 48318100 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck tb 52857300 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck tb 48170700 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck tb 24938600 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 24938600)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      ∃ pos pos', walk tb bits fuel pos (boxOf (badOf cover0) (badOf cover1) (badOf cover2) (badOf cover3) (badOf cover4) i0 i1 i2 i3 i4) = some pos') :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (25232 / (SA:ℝ)) * g0 + (42025 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42044 / (SA:ℝ)) * g3 + (24559 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25715100 / (SA:ℝ)) * wfun (g0) + (61242800 / (SA:ℝ)) * wfun (g0 + g1) + (40905100 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (104929600 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48318100 / (SA:ℝ)) * wfun (g1) + (40072400 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (95070300 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (35189000 / (SA:ℝ)) * wfun (g2 + g3) + (39348000 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48170700 / (SA:ℝ)) * wfun (g3) + (63495600 / (SA:ℝ)) * wfun (g3 + g4) + (24938600 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (25232 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (42025 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (46137 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (42044 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (24559 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25715100 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (61242800 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (40905100 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (104929600 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (48318100 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (40072400 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (95070300 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (52857300 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (35189000 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (39348000 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (48170700 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (63495600 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (24938600 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (25232 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (42025 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (46137 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (42044 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (24559 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25715100 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (61242800 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (40905100 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (104929600 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (48318100 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (40072400 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (95070300 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (52857300 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (35189000 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (39348000 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (48170700 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (63495600 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (24938600 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (25232 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (25232 / (SA:ℝ)) * g0 * SA = 25232 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 25232 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 25232 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 25232 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25715100 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25715100 / (SA:ℝ)) * wfun g0 * SA = 25715100 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25715100)
      linarith [hq, hm]
    rw [hG]; linarith [h1, haW0, hLin0]
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · rw [hG]; linarith [hclear0, haW0, hLin0]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (42025 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42025 / (SA:ℝ)) * g1 * SA = 42025 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42025 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42025 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 42025 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48318100 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (48318100 / (SA:ℝ)) * wfun g1 * SA = 48318100 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48318100)
      linarith [hq, hm]
    rw [hG]; linarith [h1, haW5, hLin0]
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · rw [hG]; linarith [hclear1, haW5, hLin0]
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
    rw [hG]; linarith [h1, hbL2, hWt0]
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
    rw [hG]; linarith [h1, haW9, hLin0]
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · rw [hG]; linarith [hclear2, haW9, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (42044 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42044 / (SA:ℝ)) * g3 * SA = 42044 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42044 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42044 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 42044 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48170700 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (48170700 / (SA:ℝ)) * wfun g3 * SA = 48170700 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48170700)
      linarith [hq, hm]
    rw [hG]; linarith [h1, haW12, hLin0]
  rcases cover_sound tb hok _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · rw [hG]; linarith [hclear3, haW12, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (24559 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24559 / (SA:ℝ)) * g4 * SA = 24559 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24559 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24559 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 24559 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (24938600 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (24938600 / (SA:ℝ)) * wfun g4 * SA = 24938600 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 24938600)
      linarith [hq, hm]
    rw [hG]; linarith [h1, haW14, hLin0]
  rcases cover_sound tb hok _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  exact walk_sound tb hok bits fuel pos _ pos' hwalk g0 g1 g2 g3 g4 ⟨hb01', hb02', hb11', hb12', hb21', hb22', hb31', hb32', hb41', hb42'⟩

end Zeta23Ext.Bridge.ThreePoint.SixW15B

end

/-! ###### certificate data `SixW15B`: 11109 cells, 14487 leaves (axis-coded walk) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW15BData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW15B

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

#eval IO.monoMsNow
noncomputable def tab0 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨17179893760,331038177865⟩ E) ⟨25769832448,242869129569⟩ E) ⟨30064801792,122761883704⟩ (N (N E ⟨32212286464,69269436296⟩ E) ⟨32212286592,62652449971⟩ E)) ⟨32212287488,27393363819⟩ (N (N (N E ⟨33286029056,36843158376⟩ E) ⟨33286029120,34548539408⟩ E) ⟨33286029312,28203622388⟩ (N E ⟨33420246720,39350240729⟩ E))) ⟨33420247040,28267587364⟩ (N (N (N (N E ⟨34024226816,28450417775⟩ E) ⟨34091335680,28460062200⟩ E) ⟨34158444544,28467564926⟩ (N (N E ⟨34359771360,21788669253⟩ E) ⟨34359771392,20912356297⟩ E)) ⟨34359771648,14596526138⟩ (N (N (N E ⟨34359771776,11891897536⟩ E) ⟨34594652800,11891897536⟩ E) ⟨34628207424,8384490092⟩ (N E ⟨34628208000,1626727581⟩ E)))) ⟨34896642944,7358852099⟩ (N (N (N (N (N E ⟨34896643328,2658307323⟩ E) ⟨35030860832,5101426618⟩ E) ⟨35030861248,1207853390⟩ (N (N E ⟨35232187776,1626727581⟩ E) ⟨35299296512,2658307323⟩ E)) ⟨35467068864,1207853390⟩ (N (N (N E ⟨36339484928,840527⟩ E) ⟨36440148480,76228626⟩ E) ⟨36507257600,189390231⟩ (N E ⟨36507258368,173234703⟩ E))) ⟨36507259904,145808985⟩ (N (N (N (N E ⟨36775693376,1151561664⟩ E) ⟨36775694208,1046595949⟩ E) ⟨36775695872,870430129⟩ (N (N E ⟨37044128832,2982576597⟩ E) ⟨37044129408,2790908306⟩ E)) ⟨37044130560,2451923401⟩ (N (N (N E ⟨37044132864,1916013694⟩ E) ⟨37312564736,5416703501⟩ E) ⟨37648109184,9732001830⟩ (N E ⟨37648109440,9452356006⟩ E))))) ⟨38117872640,15563604115⟩ (N (N (N (N (N (N E ⟨38252090112,18591409084⟩ E) ⟨38520526336,22408627075⟩ E) ⟨39460051968,40016092176⟩ (N (N E ⟨39728485504,58284410507⟩ E) ⟨39862703360,62313805310⟩ E)) ⟨39996921344,65509628502⟩ (N (N (N E ⟨40265357312,71849923330⟩ E) ⟨40802230272,75832144115⟩ E) ⟨41875971584,124701346738⟩ (N E ⟨42412843008,143033504697⟩ E))) ⟨42949715968,138814108272⟩ (N (N (N (N E ⟨42949722112,80226784524⟩ E) ⟨45097201664,198611196246⟩ E) ⟨47244689408,205420959916⟩ (N (N E ⟨51539660800,198637449669⟩ E) ⟨51539664896,86044756753⟩ E)) ⟨55834630144,180021136485⟩ (N (N (N E ⟨57982115840,129277608381⟩ E) ⟨60129600000,126832062122⟩ E) ⟨60129601536,81450895201⟩ (N E ⟨60666473596,56104174470⟩ E)))) ⟨60666473660,54744524444⟩ (N (N (N (N (N E ⟨60666476280,14490230268⟩ E) ⟨60666476408,13248302275⟩ E) ⟨62277086208,63653684247⟩ (N (N E ⟨63350829696,32801554392⟩ E) ⟨63350829760,31761760685⟩ E)) ⟨63350831360,11699544709⟩ (N (N (N E ⟨63350831488,10561059564⟩ E) ⟨63480852922,36353090489⟩ E) ⟨63480854264,17122242272⟩ (N E ⟨63547961882,34808283285⟩ E))) ⟨63547963256,15757039412⟩ (N (N (N (N E ⟨64888043256,18266655065⟩ E) ⟨64988706680,16837648072⟩ E) ⟨65095661824,12731502888⟩ (N E ⟨65162769952,21197196115⟩ E)) ⟨65162770816,11542172995⟩ (N (N (N E ⟨65498316544,2408056665⟩ E) ⟨65498316800,1506819731⟩ E) ⟨66068740480,11958745632⟩ (N E ⟨66295232919,11832935104⟩ E)))))) ⟨66295233590,6357569415⟩ (N (N (N (N (N (N (N E ⟨66295234560,1565943956⟩ E) ⟨66429450791,10546933738⟩ E) ⟨66429451478,5348283391⟩ (N (N E ⟨66429452288,1574380871⟩ E) ⟨66706276352,1590346721⟩ E)) ⟨66840492704,9616293499⟩ (N (N (N E ⟨66840493120,6405326128⟩ E) ⟨66840493952,2041289663⟩ E) ⟨66974710576,8457379249⟩ (N E ⟨66974711008,5380608052⟩ E))) ⟨66974711808,1603951009⟩ (N (N (N (N E ⟨66998828086,6505110531⟩ E) ⟨67149823190,5470768786⟩ E) ⟨67276700736,6486530866⟩ (N (N E ⟨67427695840,5447824625⟩ E) ⟨67578691584,1627636972⟩ E)) ⟨67702423253,2786489703⟩ (N (N (N E ⟨67702423552,1631286091⟩ E) ⟨67712908768,3983824195⟩ E) ⟨67712909184,2086096939⟩ (N E ⟨67870195589,2072780895⟩ E)))) ⟨67870195712,1635572606⟩ (N (N (N (N (N E ⟨67880681104,3110902549⟩ E) ⟨67880681472,1635815150⟩ E) ⟨68149116800,2099820129⟩ (N (N E ⟨68333666304,1643428677⟩ E) ⟨68406018048,1644124289⟩ E)) ⟨68585324544,1645228303⟩ (N (N (N E ⟨68590567424,1645247283⟩ E) ⟨68719542336,1436255057⟩ E) ⟨68719542560,817796385⟩ (N E ⟨68719542644,631150126⟩ E))) ⟨68719542836,296183929⟩ (N (N (N (N E ⟨68719542976,131485341⟩ E) ⟨68719543168,13164037⟩ E) ⟨68786651632,400308901⟩ (N (N E ⟨68786652064,5411364⟩ E) ⟨69021532864,131485341⟩ E)) ⟨69239636896,5411364⟩ (N (N (N E ⟨69793287488,2144977⟩ E) ⟨69793288320,2043342⟩ E) ⟨69793289856,1871060⟩ (N E ⟨69793291520,1704455⟩ E))))) ⟨69813208754,5267032⟩ (N (N (N (N (N (N E ⟨69826840576,7751317⟩ E) ⟨69860395648,15751742⟩ E) ⟨69927504160,42441413⟩ (N (N E ⟨69927504576,41404619⟩ E) ⟨69927505344,39572543⟩ E)) ⟨69927506176,37700926⟩ (N (N (N E ⟨69994613504,79129267⟩ E) ⟨69994613888,77355470⟩ E) ⟨70031312786,110700553⟩ (N E ⟨70061724032,117345383⟩ E))) ⟨70061725568,107486576⟩ (N (N (N (N E ⟨70061727232,97948609⟩ E) ⟨70061727744,95228999⟩ E) ⟨70095276288,164002603⟩ (N (N E ⟨70195941504,245844939⟩ E) ⟨70263048608,362028761⟩ E)) ⟨70263049024,353201598⟩ (N (N (N E ⟨70330158208,444465767⟩ E) ⟨70330158528,436190422⟩ E) ⟨70330159360,415560422⟩ (N E ⟨70330159872,403470914⟩ E)))) ⟨70330160512,388971858⟩ (N (N (N (N (N E ⟨70330162176,354216357⟩ E) ⟨70330163200,334751802⟩ E) ⟨70363711808,523183766⟩ (N (N E ⟨70363712192,511377759⟩ E) ⟨70516803921,820332143⟩ E)) ⟨70516804592,788334247⟩ (N (N (N E ⟨70531484320,835637430⟩ E) ⟨70531484736,815339532⟩ E) ⟨70531485312,788243580⟩ (N E ⟨70598593120,991130713⟩ E))) ⟨70598593984,941896883⟩ (N (N (N (N E ⟨70598595712,852286103⟩ E) ⟨70598598656,722853285⟩ E) ⟨70665703552,1054752212⟩ (N E ⟨70699256640,1227463388⟩ E)) ⟨70732811296,1299696151⟩ (N (N (N E ⟨70732811712,1268304108⟩ E) ⟨70732814080,1106621505⟩ E) ⟨70751685872,1334354826⟩ (N E ⟨70766365376,1420479279⟩ E))))))) ⟨70799919840,1514303517⟩ (N (N (N (N (N (N (N (N E ⟨70799920224,1480342169⟩ E) ⟨70799920640,1444620480⟩ E) ⟨70799921408,1381464137⟩ (N (N E ⟨70867028960,1691264844⟩ E) ⟨70867029376,1650376680⟩ E)) ⟨70867029952,1595784993⟩ (N (N (N E ⟨70867030784,1520862133⟩ E) ⟨70967692352,2003471324⟩ E) ⟨71135465088,2517166723⟩ (N E ⟨71169019328,2672385180⟩ E))) ⟨71202573408,2860864534⟩ (N (N (N (N E ⟨71202574592,2669775839⟩ E) ⟨71220399088,2952065098⟩ E) ⟨71236128256,2924410492⟩ (N (N E ⟨71303236992,3223080944⟩ E) ⟨71403901376,3437242548⟩ E)) ⟨71403902208,3277032161⟩ (N (N (N E ⟨71403902592,3206246751⟩ E) ⟨71403903360,3070329399⟩ E) ⟨71403905024,2799744336⟩ (N E ⟨71471009728,3838928819⟩ E)))) ⟨71504563648,4113772714⟩ (N (N (N (N (N E ⟨71538118848,4088246003⟩ E) ⟨71538119616,3911307061⟩ E) ⟨71538120064,3812514736⟩ (N (N E ⟨71538120448,3730312206⟩ E) ⟨71538121984,3422887433⟩ E)) ⟨71605227776,4390031577⟩ (N (N (N E ⟨71672338304,4290708233⟩ E) ⟨71739446016,4912999674⟩ E) ⟨71806557696,4485350389⟩ (N E ⟨71923994926,6044893012⟩ E))) ⟨71923996268,5597633759⟩ (N (N (N (N E ⟨71923998720,4882398868⟩ E) ⟨72074990336,6746069797⟩ E) ⟨72074991488,6317518618⟩ (N (N E ⟨72074992640,5922529203⟩ E) ⟨72192432044,6966292538⟩ E)) ⟨72192434176,6187227555⟩ (N (N (N E ⟨72276317440,7756885020⟩ E) ⟨72343425984,8332703272⟩ E) ⟨72410535040,8681119975⟩ (N E ⟨72410535680,8370847260⟩ E))))) ⟨72611862912,9364788646⟩ (N (N (N (N (N (N E ⟨72746082304,9372677031⟩ E) ⟨73148734720,12627844833⟩ E) ⟨73148735488,12104668324⟩ (N (N E ⟨73282952192,13853481102⟩ E) ⟨73282953216,13092218008⟩ E)) ⟨73331185260,15427701477⟩ (N (N (N E ⟨73819824128,17420620864⟩ E) ⟨74222477312,21055464219⟩ E) ⟨74738376704,26181050867⟩ (N E ⟨75073921024,29785550033⟩ E))) ⟨77309485288,57736288205⟩ (N (N (N (N E ⟨77309485312,57660655940⟩ E) ⟨77309485568,56861581616⟩ E) ⟨77309485672,56540921948⟩ (N (N E ⟨77309486336,54546146546⟩ E) ⟨77309487616,50943335175⟩ E)) ⟨77309489664,45776641928⟩ (N (N (N E ⟨77309490656,43510134591⟩ E) ⟨77309491168,42395280650⟩ E) ⟨77552760288,46130130415⟩ (N E ⟨77577921024,60643085590⟩ E)))) ⟨77846356736,63602331360⟩ (N (N (N (N (N E ⟨77846356992,62727040513⟩ E) ⟨77955413984,49264488826⟩ E) ⟨78114792448,66530373098⟩ (N (N E ⟨78383228928,66621352329⟩ E) ⟨79456972800,73216762336⟩ E)) ⟨81604460544,81183335634⟩ (N (N (N E ⟨83181518848,95435097263⟩ E) ⟨83718389760,99708153753⟩ E) ⟨85899431936,79111303097⟩ (N E ⟨85899435984,38860075235⟩ E))) ⟨85899436032,38423148027⟩ (N (N (N (N E ⟨90194401280,68661704304⟩ E) ⟨92341885440,67628919902⟩ E) ⟨92341885952,61427731673⟩ (N E ⟨92878756608,65677920649⟩ E)) ⟨93147192192,64676607906⟩ (N (N (N E ⟨93147192320,63103400105⟩ E) ⟨93281410048,63381401765⟩ E) ⟨93415628032,60519493235⟩ (N E ⟨93415628800,51392597158⟩ E)))))) ⟨93684063744,57931894547⟩ (N (N (N (N (N (N (N E ⟨93952499712,52311507142⟩ E) ⟨94439038976,53137584618⟩ E) ⟨94489371344,44898239526⟩ (N (N E ⟨94489373260,25713477686⟩ E) ⟨94489374224,17965572406⟩ E)) ⟨94489374240,17848583852⟩ (N (N (N E ⟨94489375944,7621693323⟩ E) ⟨94489376124,6800702072⟩ E) ⟨94489376188,6520655021⟩ (N E ⟨94489378336,608823085⟩ E))) ⟨94489378808,165286845⟩ (N (N (N (N E ⟨94489378816,160224349⟩ E) ⟨95244348812,19477292869⟩ E) ⟨95244351560,4182766391⟩ (N (N E ⟨95563119232,2510874330⟩ E) ⟨96636861120,2488359274⟩ E)) ⟨96636861312,2005828299⟩ (N (N (N E ⟨96636862464,221539557⟩ E) ⟨96766884216,3461637059⟩ E) ⟨96766885880,231189510⟩ (N E ⟨96833993208,3078815243⟩ E)))) ⟨96833994752,226834761⟩ (N (N (N (N (N E ⟨97253420938,16885861029⟩ E) ⟨97253422280,8536991830⟩ E) ⟨97442168832,242596132⟩ (N (N E ⟨97979038912,1427192342⟩ E) ⟨98125837034,11498381159⟩ E)) ⟨98125838408,4748454477⟩ (N (N (N E ⟨98264249880,7158732196⟩ E) ⟨98264251936,824867816⟩ E) ⟨98281026216,11958562382⟩ (N E ⟨98281027376,5905315798⟩ E))) ⟨98281029632,262627654⟩ (N (N (N (N E ⟨98381691776,2185018972⟩ E) ⟨98381692928,264878549⟩ E) ⟨98448800640,2191291061⟩ (N (N E ⟨98448801792,266359493⟩ E) ⟨98511715002,2728728717⟩ E)) ⟨98511716344,274562977⟩ (N (N (N E ⟨98578823962,2470133859⟩ E) ⟨98578825216,269183140⟩ E) ⟨98660611272,8948919475⟩ (N E ⟨99186998464,1509069493⟩ E))))) ⟨99186999296,281547652⟩ (N (N (N (N (N (N E ⟨99497375536,6141282325⟩ E) ⟨99566581145,8087907822⟩ E) ⟨99566581832,4984518345⟩ (N (N E ⟨99581262710,2315486609⟩ E) ⟨99581263542,660457891⟩ E)) ⟨99715480598,1924051839⟩ (N (N (N E ⟨99715481430,463889602⟩ E) ⟨99790977952,2222401197⟩ E) ⟨99790978816,569141180⟩ (N E ⟨99918904504,1568994808⟩ E))) ⟨99918905336,301693756⟩ (N (N (N (N E ⟨100019567928,1311222496⟩ E) ⟨100019568640,296016137⟩ E) ⟨100059414048,899130967⟩ (N (N E ⟨100059414528,296632190⟩ E) ⟨100067800935,5998708048⟩ E)) ⟨100067801606,3441937205⟩ (N (N (N E ⟨100067802948,492729421⟩ E) ⟨100126523072,662577731⟩ E) ⟨100126523392,297653366⟩ (N E ⟨100260741120,299633480⟩ E)))) ⟨100286953544,5088395683⟩ (N (N (N (N (N E ⟨100394958304,1017344218⟩ E) ⟨100420123164,3404954463⟩ E) ⟨100420124192,911071643⟩ (N (N E ⟨100453678774,684960813⟩ E) ⟨100587896662,482050048⟩ E)) ⟨100696948480,590452852⟩ (N (N (N E ⟨100713724276,4004866175⟩ E) ⟨100713724856,2223049757⟩ E) ⟨100713725952,305689821⟩ (N E ⟨100771396102,3509574532⟩ E))) ⟨100791320568,314108631⟩ (N (N (N (N E ⟨100891983872,307801662⟩ E) ⟨100965383808,775774854⟩ E) ⟨100965384192,308625792⟩ (N E ⟨100988452864,308879290⟩ E)) ⟨100998938304,683366334⟩ (N (N (N E ⟨100998938624,308993641⟩ E) ⟨101007325943,2776039722⟩ E) ⟨101007326630,1140980626⟩ (N E ⟨101156225024,310643051⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab1 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨101321898936,2257837150⟩ E) ⟨101326093751,1119360397⟩ E) ⟨101326094167,492628661⟩ (N (N E ⟨101326094336,312284618⟩ E) ⟨101460312039,337583423⟩ E)) ⟨101460312064,313477975⟩ (N (N (N E ⟨101474991269,1684190154⟩ E) ⟨101474991940,517581649⟩ E) ⟨101498060320,940202692⟩ (N E ⟨101602918000,813574295⟩ E))) ⟨101602918400,314644752⟩ (N (N (N (N E ⟨101727698342,1161337579⟩ E) ⟨101762301783,497944572⟩ E) ⟨101770690560,315882938⟩ (N (N E ⟨101860868096,316487997⟩ E) ⟨101871353856,316555598⟩ E)) ⟨101904908288,316768058⟩ (N (N (N E ⟨101930073596,1010656676⟩ E) ⟨101930074112,316923535⟩ E) ⟨102028640256,317500505⟩ (N E ⟨102029688832,317506369⟩ E)))) ⟨102055903232,317651080⟩ (N (N (N (N (N E ⟨102178586436,525188127⟩ E) ⟨102180683776,318290256⟩ E) ⟨102198509568,318374856⟩ (N (N E ⟨102206898176,318414087⟩ E) ⟨102307561472,318855792⟩ E)) ⟨102324338688,318924188⟩ (N (N (N E ⟨102448070656,319382434⟩ E) ⟨102465896448,319441743⟩ E) ⟨102508888064,319577821⟩ (N E ⟨102538248192,319665093⟩ E))) ⟨102575996928,319770546⟩ (N (N (N (N E ⟨102616891392,319876207⟩ E) ⟨102659883008,319977661⟩ E) ⟨102743769088,320147185⟩ (N (N E ⟨102777323520,320204460⟩ E) ⟨102882181120,320344615⟩ E)) ⟨103079313440,290120585⟩ (N (N (N E ⟨103079313456,275526942⟩ E) ⟨103079313472,261313260⟩ E) ⟨103079313493,243234019⟩ (N E ⟨103079313494,242389409⟩ E))))) ⟨103079313504,234024811⟩ (N (N (N (N (N (N E ⟨103079313528,214554052⟩ E) ⟨103079313584,172435688⟩ E) ⟨103079313588,169604524⟩ (N (N E ⟨103079313654,126296827⟩ E) ⟨103079313728,85361675⟩ E)) ⟨103079313749,75208942⟩ (N (N (N E ⟨103079313780,61402067⟩ E) ⟨103079313792,56434938⟩ E) ⟨103079313872,28693336⟩ (N E ⟨103079313888,24264110⟩ E))) ⟨103079313891,23475084⟩ (N (N (N (N E ⟨103079313910,18781711⟩ E) ⟨103079313920,16522152⟩ E) ⟨103079313925,15446813⟩ (N (N E ⟨103079313936,13208758⟩ E) ⟨103079313956,9589082⟩ E)) ⟨103079313984,5494867⟩ (N (N (N E ⟨103079314016,2204075⟩ E) ⟨103079314044,537295⟩ E) ⟨103079314070,1257⟩ (N E ⟨103079314071,74⟩ E)))) ⟨103802833712,468860⟩ (N (N (N (N (N E ⟨103802834544,453669⟩ E) ⟨103817514368,1065102⟩ E) ⟨103817515136,1033382⟩ (N (N E ⟨103867844320,5420886⟩ E) ⟨103873087284,6029627⟩ E)) ⟨103884623808,6903573⟩ (N (N (N E ⟨103884625344,6502204⟩ E) ⟨103884626048,6328014⟩ E) ⟨103884627072,6084936⟩ (N E ⟨103884627968,5881758⟩ E))) ⟨103888816226,8019845⟩ (N (N (N (N E ⟨103888817600,7593446⟩ E) ⟨103943343030,16962014⟩ E) ⟨103951731648,18688523⟩ (N E ⟨103971653938,23754795⟩ E)) ⟨104018839408,37207097⟩ (N (N (N E ⟨104018839840,36568936⟩ E) ⟨104018840416,35739208⟩ E) ⟨104018840832,35154574⟩ (N E ⟨104018841280,34538288⟩ E)))))) ⟨104018841920,33681141⟩ (N (N (N (N (N (N (N E ⟨104018842432,33014516⟩ E) ⟨104018842752,32606248⟩ E) ⟨104018844160,30883143⟩ (N (N E ⟨104018845440,29414489⟩ E) ⟨104018845696,29131321⟩ E)) ⟨104035616832,42159602⟩ (N (N (N E ⟨104037714992,41155299⟩ E) ⟨104037715824,39825264⟩ E) ⟨104041908181,44413468⟩ (N E ⟨104052393696,48452755⟩ E))) ⟨104052394112,47651021⟩ (N (N (N (N E ⟨104057636852,49751082⟩ E) ⟨104085948144,60873351⟩ E) ⟨104085949344,58024299⟩ (N (N E ⟨104085949760,57075718⟩ E) ⟨104085950528,55374913⟩ E)) ⟨104085951360,53603320⟩ (N (N (N E ⟨104136280224,80822934⟩ E) ⟨104140474419,83077338⟩ E) ⟨104140474835,81707323⟩ (N E ⟨104140475506,79556547⟩ E)))) ⟨104140476338,76987137⟩ (N (N (N (N (N E ⟨104140477680,73057653⟩ E) ⟨104153058432,85097663⟩ E) ⟨104153058688,84240066⟩ (N (N E ⟨104153059008,83183222⟩ E) ⟨104153059776,80713683⟩ E)) ⟨104153060608,78140978⟩ (N (N (N E ⟨104169834496,97202257⟩ E) ⟨104189757970,105042296⟩ E) ⟨104209680517,117255365⟩ (N E ⟨104220167616,116623709⟩ E))) ⟨104220167936,115161513⟩ (N (N (N (N E ⟨104220168384,113152760⟩ E) ⟨104220168704,111744728⟩ E) ⟨104220169216,109537168⟩ (N (N E ⟨104287275744,159168281⟩ E) ⟨104287275872,158360372⟩ E)) ⟨104287276288,155769859⟩ (N (N (N E ⟨104289372608,162331072⟩ E) ⟨104309295316,176861276⟩ E) ⟨104309295732,173949356⟩ (N E ⟨104320829584,185114570⟩ E))))) ⟨104320830016,181948659⟩ (N (N (N (N (N (N E ⟨104320830592,177832088⟩ E) ⟨104341801219,198758717⟩ E) ⟨104341801635,195487797⟩ (N (N E ⟨104341802322,190232138⟩ E) ⟨104341803154,184101672⟩ E)) ⟨104341804528,174508846⟩ (N (N (N E ⟨104354385216,198950885⟩ E) ⟨104362772816,213148695⟩ E) ⟨104387939136,227340587⟩ (N E ⟨104387939904,220532053⟩ E))) ⟨104421495488,234616700⟩ (N (N (N (N E ⟨104421496320,227156804⟩ E) ⟨104421497472,217310842⟩ E) ⟨104421498880,205990782⟩ (N (N E ⟨104471824672,300633146⟩ E) ⟨104478116629,300061667⟩ E)) ⟨104478117300,292188160⟩ (N (N (N E ⟨104478118132,282781007⟩ E) ⟨104488601728,317384433⟩ E) ⟨104488602096,312752430⟩ (N E ⟨104488602528,307422268⟩ E)))) ⟨104488602560,307031980⟩ (N (N (N (N (N E ⟨104488603072,300870864⟩ E) ⟨104488603392,297098627⟩ E) ⟨104488603648,294123368⟩ (N (N E ⟨104493845300,313321039⟩ E) ⟨104522157376,331662148⟩ E)) ⟨104555711584,365519148⟩ (N (N (N E ⟨104555712000,359554950⟩ E) ⟨104555712576,351496418⟩ E) ⟨104555713344,341099989⟩ (N E ⟨104555714176,330267653⟩ E))) ⟨104555715328,315969717⟩ (N (N (N (N E ⟨104576682451,395673743⟩ E) ⟨104589265920,399317400⟩ E) ⟨104589266688,387380859⟩ (N E ⟨104622819760,443428349⟩ E)) ⟨104622820192,435866312⟩ (N (N (N E ⟨104622820768,426032834⟩ E) ⟨104622821504,413868282⟩ E) ⟨104622821632,411797282⟩ (N E ⟨104622822784,393729601⟩ E))))))) ⟨104645890484,431597944⟩ (N (N (N (N (N (N (N (N E ⟨104675249776,476766646⟩ E) ⟨104689932544,443359438⟩ E) ⟨104689933184,432630731⟩ (N (N E ⟨104689934336,414124897⟩ E) ⟨104723483904,537318409⟩ E)) ⟨104731872816,540396104⟩ (N (N (N E ⟨104745503348,577473953⟩ E) ⟨104757038784,566159933⟩ E) ⟨104773814848,613152145⟩ (N E ⟨104778009251,615912991⟩ E))) ⟨104815761268,583459524⟩ (N (N (N (N E ⟨104824149568,600057572⟩ E) ⟨104824150400,581140820⟩ E) ⟨104824151936,548136874⟩ (N (N E ⟨104824152064,545493685⟩ E) ⟨104844069586,698997029⟩ E)) ⟨104844070002,687546529⟩ (N (N (N E ⟨104891256896,721760793⟩ E) ⟨104891257216,712768220⟩ E) ⟨104891257984,691751310⟩ (N E ⟨104910131056,752672926⟩ E)))) ⟨104924810368,795673983⟩ (N (N (N (N (N E ⟨104924810944,777773714⟩ E) ⟨104941587360,826540041⟩ E) ⟨104949979188,739400704⟩ (N (N E ⟨104958364992,836749589⟩ E) ⟨104958365408,823126377⟩ E)) ⟨104958365824,809779573⟩ (N (N (N E ⟨104958366144,799696668⟩ E) ⟨104958366592,785843041⟩ E) ⟨104958367424,760902277⟩ (N E ⟨104958367744,751573889⟩ E))) ⟨104958368256,736944104⟩ (N (N (N (N E ⟨104991919232,891979818⟩ E) ⟨104991919616,878538549⟩ E) ⟨105012890483,933119696⟩ (N (N E ⟨105012890899,917858272⟩ E) ⟨105012891570,893894114⟩ E)) ⟨105025474752,902676954⟩ (N (N (N E ⟨105025475072,891444374⟩ E) ⟨105025475840,865191378⟩ E) ⟨105062174034,990490154⟩ (N E ⟨105075805024,1031903613⟩ E))))) ⟨105092583424,1010514521⟩ (N (N (N (N (N (N E ⟨105092584448,970885066⟩ E) ⟨105092584512,968473356⟩ E) ⟨105092586112,910544466⟩ (N (N E ⟨105092587520,863112789⟩ E) ⟨105159691936,1132472430⟩ E)) ⟨105159692352,1114098133⟩ (N (N (N E ⟨105181711796,1179989487⟩ E) ⟨105193246272,1192957427⟩ E) ⟨105210026220,1098356621⟩ (N E ⟨105210027884,1030891070⟩ E))) ⟨105210028032,1025144869⟩ (N (N (N (N E ⟨105214217699,1233289191⟩ E) ⟨105214218386,1200401497⟩ E) ⟨105226800544,1258439559⟩ (N (N E ⟨105226801120,1230208260⟩ E) ⟨105226801984,1189330625⟩ E)) ⟨105226802624,1160142263⟩ (N (N (N E ⟨105226803136,1137434544⟩ E) ⟨105226803456,1123524283⟩ E) ⟨105226804608,1075176801⟩ (N E ⟨105226804864,1064788573⟩ E)))) ⟨105280277618,1369873080⟩ (N (N (N (N (N E ⟨105293910432,1324044746⟩ E) ⟨105293911296,1280238729⟩ E) ⟨105293911552,1267608622⟩ (N (N E ⟨105293912832,1206745625⟩ E) ⟨105329561024,1442577755⟩ E)) ⟨105350533364,1435031260⟩ (N (N (N E ⟨105361018624,1483181829⟩ E) ⟨105361018720,1477589962⟩ E) ⟨105361019136,1453661183⟩ (N E ⟨105361019712,1421323803⟩ E))) ⟨105361020288,1389881531⟩ (N (N (N (N E ⟨105361021952,1303810317⟩ E) ⟨105361022464,1278676770⟩ E) ⟨105361022976,1254146509⟩ (N E ⟨105394572800,1562791894⟩ E)) ⟨105394573024,1549052433⟩ (N (N (N E ⟨105394573056,1547102011⟩ E) ⟨105394573440,1523934906⟩ E) ⟨105428128064,1576334175⟩ (N E ⟨105428128640,1541289642⟩ E)))))) ⟨105428129408,1496066047⟩ (N (N (N (N (N (N (N E ⟨105449098515,1686362061⟩ E) ⟨105478461996,1532860579⟩ E) ⟨105478463488,1448348361⟩ (N (N E ⟨105495238080,1633069640⟩ E) ⟨105495240704,1477240831⟩ E)) ⟨105528791296,1780222889⟩ (N (N (N E ⟨105547665840,1806559499⟩ E) ⟨105547666672,1748967538⟩ E) ⟨105579123296,1858923806⟩ (N E ⟨105595899968,1934679827⟩ E))) ⟨105629457024,1813173215⟩ (N (N (N (N E ⟨105696562942,2183712163⟩ E) ⟨105696564284,2072061744⟩ E) ⟨105696564352,2066596714⟩ (N (N E ⟨105696565632,1967010743⟩ E) ⟨105696566400,1910134415⟩ E)) ⟨105696566968,1869388740⟩ (N (N (N E ⟨105696567296,1846354451⟩ E) ⟨105716486066,2213842817⟩ E) ⟨105763672544,2273327253⟩ (N E ⟨105763672704,2259167630⟩ E)))) ⟨105763672960,2236740986⟩ (N (N (N (N (N E ⟨105763673280,2209097958⟩ E) ⟨105763674048,2144478419⟩ E) ⟨105763674880,2077120175⟩ (N (N E ⟨105782547120,2298265595⟩ E) ⟨105782547952,2225178484⟩ E)) ⟨105797226752,2371961056⟩ (N (N (N E ⟨105830781056,2464244179⟩ E) ⟨105830781888,2385455058⟩ E) ⟨105830782656,2315505441⟩ (N E ⟨105830783488,2242598207⟩ E))) ⟨105885307634,2534862090⟩ (N (N (N (N E ⟨105885308466,2454302038⟩ E) ⟨105885309808,2330992945⟩ E) ⟨105885310976,2229922484⟩ (N E ⟨105934590098,2719369395⟩ E)) ⟨105964999072,2767610962⟩ (N (N (N E ⟨105964999488,2723042108⟩ E) ⟨106032108416,2886454083⟩ E) ⟨106032111616,2553301322⟩ (N E ⟨106086635282,2923150439⟩ E))))) ⟨106086636656,2773213133⟩ (N (N (N (N (N (N E ⟨106086637568,2678982505⟩ E) ⟨106099218688,2899610072⟩ E) ⟨106132771648,3159276748⟩ (N (N E ⟨106166326272,3226207768⟩ E) ⟨106166326848,3154970160⟩ E)) ⟨106166327616,3063020264⟩ (N (N (N E ⟨106166328448,2967159653⟩ E) ⟨106166329344,2868085299⟩ E) ⟨106199880576,3334493771⟩ (N E ⟨106199880960,3285118703⟩ E))) ⟨106233435776,3327380729⟩ (N (N (N (N E ⟨106300546304,3295566036⟩ E) ⟨106300547072,3201075113⟩ E) ⟨106367653056,3767517279⟩ (N (N E ⟨106401207104,3924302267⟩ E) ⟨106420081904,3914900861⟩ E)) ⟨106434762688,3850045846⟩ (N (N (N E ⟨106434764160,3639312697⟩ E) ⟨106434764672,3569411550⟩ E) ⟨106434764800,3552199377⟩ (N E ⟨106568979840,4345781435⟩ E)))) ⟨106568980416,4250176222⟩ (N (N (N (N (N E ⟨106568982528,3921374948⟩ E) ⟨106636089024,4501766648⟩ E) ⟨106636090112,4317534691⟩ (N (N E ⟨106654963184,4598367711⟩ E) ⟨106703198720,4567600534⟩ E)) ⟨106703200256,4308506924⟩ (N (N (N E ⟨106757723698,4920754322⟩ E) ⟨106770306624,4959771060⟩ E) ⟨106770307196,4851604973⟩ (N E ⟨106770309120,4508773694⟩ E))) ⟨106837417984,4713488648⟩ (N (N (N (N E ⟨106887749184,4953154248⟩ E) ⟨106904525568,5167807049⟩ E) ⟨106954858348,5110885390⟩ (N E ⟨106971633984,5485293606⟩ E)) ⟨106971635712,5136201722⟩ (N (N (N E ⟨107038743680,5539120202⟩ E) ⟨107038744192,5432471714⟩ E) ⟨107103753276,6250344236⟩ (N E ⟨107105852416,5797344305⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab2 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨107172960192,6289821688⟩ E) ⟨107223293952,5976118346⟩ E) ⟨107292498800,6499637230⟩ (N (N E ⟨107374288896,6509369379⟩ E) ⟨107508506624,7001589868⟩ E)) ⟨107527380080,7320929975⟩ (N (N (N E ⟨107630141440,7462322818⟩ E) ⟨107642724352,7510774532⟩ E) ⟨107776942080,8036735203⟩ (N E ⟨107831468032,8255153353⟩ E))) ⟨107911159808,8579272269⟩ (N (N (N (N E ⟨108011823104,8996926832⟩ E) ⟨108024406016,9049776332⟩ E) ⟨108359950336,10510947160⟩ (N (N E ⟨108448030720,10910796006⟩ E) ⟨108510944952,11340201862⟩ E)) ⟨108582248448,11532825879⟩ (N (N (N E ⟨108699688960,12089533415⟩ E) ⟨108968124416,13404539922⟩ E) ⟨109253337088,14864417181⟩ (N E ⟨109651795968,17006445976⟩ E)))) ⟨110058643456,19308445686⟩ (N (N (N (N (N E ⟨110595514368,22506452254⟩ E) ⟨110838784000,24009450743⟩ E) ⟨111199494144,26292713610⟩ (N (N E ⟨111241437184,26562119161⟩ E) ⟨111266603008,26724131235⟩ E)) ⟨111325323264,27103215591⟩ (N (N (N E ⟨111669256320,29210021225⟩ E) ⟨111669256364,29161623821⟩ E) ⟨111669256448,29069507059⟩ (N E ⟨111669256576,28929837604⟩ E))) ⟨111669256688,28808314968⟩ (N (N (N (N E ⟨111669256944,28532938299⟩ E) ⟨111669256960,28515836841⟩ E) ⟨111669257016,28456082639⟩ (N (N E ⟨111669257216,28243949556⟩ E) ⟨111669257344,28109222210⟩ E)) ⟨111669257728,27709835999⟩ (N (N (N E ⟨111669257984,27447518209⟩ E) ⟨111669258112,27317524415⟩ E) ⟨111669258240,27188299995⟩ (N E ⟨111669258368,27059839487⟩ E))))) ⟨111669258496,26932137472⟩ (N (N (N (N (N (N E ⟨111669258624,26805188577⟩ E) ⟨111669258728,26702593465⟩ E) ⟨111669259008,26428807555⟩ (N (N E ⟨111669259112,26328010758⟩ E) ⟨111669259264,26181555955⟩ E)) ⟨111669259520,25937191605⟩ (N (N (N E ⟨111669259648,25816079498⟩ E) ⟨111669260288,25221021330⟩ E) ⟨111669260416,25104076101⟩ (N E ⟨111669261056,24529420755⟩ E))) ⟨111669261232,24374283198⟩ (N (N (N (N E ⟨111669261312,24304171983⟩ E) ⟨111669261824,23861384437⟩ E) ⟨111669262056,23664070407⟩ (N (N E ⟨111669262440,23341945754⟩ E) ⟨111669262512,23282159409⟩ E)) ⟨111669262592,23215954651⟩ (N (N (N E ⟨111669263872,22188015873⟩ E) ⟨111669264384,21792819594⟩ E) ⟨112533289136,27894203484⟩ (N E ⟨112877223936,27861269372⟩ E)))) ⟨116467548160,45457472084⟩ (N (N (N (N (N E ⟨116954087424,47509172966⟩ E) ⟨117004419072,47713980868⟩ E) ⟨118296264704,52419279185⟩ (N (N E ⟨120259200512,52971284238⟩ E) ⟨120259202016,47167361783⟩ E)) ⟨120259202528,44887967968⟩ (N (N (N E ⟨120259202600,44557455791⟩ E) ⟨120259206560,24648331854⟩ E) ⟨120259206784,23530782628⟩ (N E ⟨120259207168,21644686635⟩ E))) ⟨124017303552,24202232921⟩ (N (N (N (N E ⟨124059246592,24231042862⟩ E) ⟨126701658112,26035399071⟩ E) ⟨127238529024,26396659657⟩ (N E ⟨127641182208,26665741080⟩ E)) ⟨127725068288,26721577863⟩ (N (N (N E ⟨128211607552,27043789676⟩ E) ⟨128446488576,27198271347⟩ E) ⟨128530374656,27253264256⟩ (N E ⟨128849142688,22147604092⟩ E)))))) ⟨128849143836,16151750382⟩ (N (N (N (N (N (N (N E ⟨128849145088,10538428373⟩ E) ⟨128849145488,8977146292⟩ E) ⟨128849145868,7605001289⟩ (N (N E ⟨128849145976,7235190293⟩ E) ⟨128849146104,6808597004⟩ E)) ⟨128849146496,5581931705⟩ (N (N (N E ⟨128849146520,5510767516⟩ E) ⟨128849146700,4991621461⟩ E) ⟨128849146748,4857540297⟩ (N E ⟨128849146812,4681627002⟩ E))) ⟨128849147344,3346442993⟩ (N (N (N (N E ⟨128849147532,2929030315⟩ E) ⟨128849148112,1820297442⟩ E) ⟨128849149308,375476713⟩ (N (N E ⟨128849149372,329343855⟩ E) ⟨128849149384,321038381⟩ E)) ⟨128849149432,288901182⟩ (N (N (N E ⟨128849149560,211650114⟩ E) ⟨128849149600,190016331⟩ E) ⟨128849149824,90715316⟩ (N E ⟨128849149952,50445805⟩ E)))) ⟨129646064692,4478212490⟩ (N (N (N (N (N E ⟨129646066420,1062010192⟩ E) ⟨129780282612,3996467573⟩ E) ⟨129780284340,836962056⟩ (N (N E ⟨129822222590,15439293191⟩ E) ⟨129822223964,9426588321⟩ E)) ⟨129822226712,1774501676⟩ (N (N (N E ⟨130052915200,61460790⟩ E) ⟨130191327104,107477872⟩ E) ⟨130275210892,3084021192⟩ (N E ⟨130325544960,63900346⟩ E))) ⟨130455566136,2730383297⟩ (N (N (N (N E ⟨130455567864,327264114⟩ E) ⟨130493315120,2239434579⟩ E) ⟨130493317120,65385376⟩ (N (N E ⟨130522675128,2474944039⟩ E) ⟨130522676856,244920728⟩ E)) ⟨130539452232,2704807073⟩ (N (N (N E ⟨130539453896,363897539⟩ E) ⟨131025988954,10778047436⟩ E) ⟨131025990296,5882181459⟩ (N E ⟨131214735820,1573424591⟩ E))))) ⟨131214737408,71593540⟩ (N (N (N (N (N (N E ⟨131262967388,9783734389⟩ E) ⟨131265069056,72014168⟩ E) ⟨131411866986,3898017251⟩ (N (N E ⟨131411868360,1209581981⟩ E) ⟨131411869696,73230433⟩ E)) ⟨131458005748,1151523021⟩ (N (N (N E ⟨131550279832,2124985266⟩ E) ⟨131550281496,172053248⟩ E) ⟨131567057200,1853619494⟩ (N E ⟨131567058736,160251988⟩ E))) ⟨131592223668,912272514⟩ (N (N (N (N E ⟨132020043020,558882680⟩ E) ⟨132267505850,2110559248⟩ E) ⟨132267507192,365293037⟩ (N (N E ⟨132284283018,2201896510⟩ E) ⟨132284284360,402692822⟩ E)) ⟨132334614810,1940054470⟩ (N (N (N E ⟨132334616184,276471509⟩ E) ⟨132338808336,3582671188⟩ E) ⟨132338810656,177878185⟩ (N E ⟨132433179288,6100155782⟩ E)))) ⟨132460445360,242929144⟩ (N (N (N (N (N E ⟨132661772208,113656390⟩ E) ⟨132703712186,5242173173⟩ E) ⟨132703713560,1965609435⟩ (N (N E ⟨132758240928,257064201⟩ E) ⟨132852611784,1274066330⟩ E)) ⟨132909235368,681014163⟩ (N (N (N E ⟨132909236224,84551849⟩ E) ⟨132926013440,84665722⟩ E) ⟨132959567872,84892501⟩ (N E ⟨133156698282,2196398730⟩ E))) ⟨133156699114,901534051⟩ (N (N (N (N E ⟨133156700160,86198362⟩ E) ⟨133177670312,1334081843⟩ E) ⟨133269944598,2001369989⟩ (N E ⟨133269945462,743824252⟩ E)) ⟨133269946368,86927634⟩ (N (N (N E ⟨133295111960,192858386⟩ E) ⟨133353831558,728588253⟩ E) ⟨133353832448,87457766⟩ (N E ⟨133404162486,1727293546⟩ E))))))) ⟨133404163350,582414218⟩ (N (N (N (N (N (N (N (N E ⟨133674696184,389557869⟩ E) ⟨133691472520,1402616746⟩ E) ⟨133691473352,428503626⟩ (N (N E ⟨133706153984,89587803⟩ E) ⟨133775358744,1195292976⟩ E)) ⟨133775359608,296846845⟩ (N (N (N E ⟨133815204960,782093825⟩ E) ⟨133815205824,115705527⟩ E) ⟨133840369622,2666109124⟩ (N E ⟨133840370964,593401922⟩ E))) ⟨134029114346,926645378⟩ (N (N (N (N E ⟨134125583536,701489509⟩ E) ⟨134125584384,91911106⟩ E) ⟨134144456984,2043263807⟩ (N (N E ⟨134175914455,1706402844⟩ E) ⟨134175915126,765926575⟩ E)) ⟨134272385024,92667319⟩ (N (N (N E ⟨134293355750,648393764⟩ E) ⟨134293356544,92772878⟩ E) ⟨134310132327,1477101510⟩ (N E ⟨134310133014,600419120⟩ E)))) ⟨134394018864,851368949⟩ (N (N (N (N (N E ⟨134394019632,189743459⟩ E) ⟨134473711616,93654831⟩ E) ⟨134563888584,441590588⟩ (N (N E ⟨134597442393,1130769507⟩ E) ⟨134597443080,389701776⟩ E)) ⟨134597443584,94232767⟩ (N (N (N E ⟨134677134261,1010402635⟩ E) ⟨134677134932,332790175⟩ E) ⟨134677135360,94593148⟩ (N E ⟨134681329272,307070972⟩ E))) ⟨134721174656,766337070⟩ (N (N (N (N E ⟨134721175488,121068939⟩ E) ⟨134761021060,299498690⟩ E) ⟨134761021440,94962366⟩ (N (N E ⟨134771506976,201488252⟩ E) ⟨134815547392,95196746⟩ E)) ⟨134844906597,799446031⟩ (N (N (N E ⟨134844907284,208871425⟩ E) ⟨134879509622,780743583⟩ E) ⟨135030504294,1124529355⟩ (N E ⟨135030504726,612571119⟩ E))))) ⟨135081884983,580734408⟩ (N (N (N (N (N (N E ⟨135081885654,113330538⟩ E) ⟨135098662183,596689196⟩ E) ⟨135098662854,120273884⟩ (N (N E ⟨135165771776,96595161⟩ E) ⟨135199326000,195348198⟩ E)) ⟨135216102855,450636249⟩ (N (N (N E ⟨135216103424,96780705⟩ E) ⟨135247559956,617852909⟩ E) ⟨135317814792,397767483⟩ (N E ⟨135333543936,97198350⟩ E))) ⟨135341932276,231274325⟩ (N (N (N (N E ⟨135341932544,97227358⟩ E) ⟨135380729428,339622409⟩ E) ⟨135450984412,112262503⟩ (N (N E ⟨135469858816,97656065⟩ E) ⟨135483489558,619180477⟩ E)) ⟨135560036256,139483549⟩ (N (N (N E ⟨135565278996,213507757⟩ E) ⟨135583104357,543206001⟩ E) ⟨135583104789,213021617⟩ (N E ⟨135583105024,98014026⟩ E)))) ⟨135585201782,316496761⟩ (N (N (N (N (N E ⟨135593590288,393982325⟩ E) ⟨135593590720,124932872⟩ E) ⟨135610367604,318122421⟩ (N (N E ⟨135610368000,98097161⟩ E) ⟨135627145184,111187747⟩ E)) ⟨135633436672,98166581⟩ (N (N (N E ⟨135750876693,391358277⟩ E) ⟨135750877125,123259018⟩ E) ⟨135785480150,115946918⟩ (N E ⟨135802256934,378302463⟩ E))) ⟨135802257350,122984215⟩ (N (N (N (N E ⟨135936474822,263961504⟩ E) ⟨135936475136,98999214⟩ E) ⟨135950106360,232336759⟩ (N E ⟨135950106624,99033182⟩ E)) ⟨136036089621,215290995⟩ (N (N (N E ⟨136038187008,99245381⟩ E) ⟨136046575136,384932355⟩ E) ⟨136046575552,126404598⟩ (N E ⟨136084324352,99351484⟩ E)))))) ⟨136203861957,124581014⟩ (N (N (N (N (N (N (N E ⟨136218542080,99640327⟩ E) ⟨136238464966,124219446⟩ E) ⟨136285650944,99773646⟩ (N (N E ⟨136286699520,99775670⟩ E) ⟨136389459968,99965234⟩ E)) ⟨136415674368,100010796⟩ (N (N (N E ⟨136466006016,100095080⟩ E) ⟨136471248896,100103618⟩ E) ⟨136482783168,127464677⟩ (N E ⟨136489074688,100132305⟩ E))) ⟨136499560400,120346737⟩ (N (N (N (N E ⟨136499560448,100148933⟩ E) ⟨136505851904,100158823⟩ E) ⟨136554086400,100232453⟩ (N (N E ⟨136558280704,100238673⟩ E) ⟨136656846848,100376396⟩ E)) ⟨136739684352,100479598⟩ (N (N (N E ⟨136918990848,100663638⟩ E) ⟨136935768064,100678099⟩ E) ⟨137439084548,99276454⟩ (N E ⟨137439084582,86076446⟩ E)))) ⟨137439084594,81643464⟩ (N (N (N (N (N E ⟨137439084620,72442612⟩ E) ⟨137439084662,58746422⟩ E) ⟨137439084704,46489813⟩ (N (N E ⟨137439084727,40387174⟩ E) ⟨137439084728,40131616⟩ E)) ⟨137439084740,37128430⟩ (N (N (N E ⟨137439084741,36883456⟩ E) ⟨137439084787,26494034⟩ E) ⟨137439084796,24662527⟩ (N E ⟨137439084818,20462462⟩ E))) ⟨137439084848,15368120⟩ (N (N (N (N E ⟨137439084856,14132891⟩ E) ⟨137439084860,13534729⟩ E) ⟨137439084864,12949532⟩ (N E ⟨137439084872,11818026⟩ E)) ⟨137439084880,10738357⟩ (N (N (N E ⟨137439084896,8734460⟩ E) ⟨137439084912,6937709⟩ E) ⟨137439084916,6520871⟩ (N E ⟨137439084917,6418683⟩ E))))) ⟨137439084920,6116970⟩ (N (N (N (N (N (N E ⟨137439084980,1609284⟩ E) ⟨137439084984,1412060⟩ E) ⟨137439084995,936196⟩ (N (N E ⟨137439084996,897771⟩ E) ⟨137967571094,8137⟩ E)) ⟨137967571894,7946⟩ (N (N (N E ⟨137967571926,7939⟩ E) ⟨137967573236,7640⟩ E) ⟨137967574836,7293⟩ (N E ⟨137975957376,62700⟩ E))) ⟨137975957792,61919⟩ (N (N (N (N E ⟨137975958208,61150⟩ E) ⟨137975959552,58747⟩ E) ⟨137975960320,57427⟩ (N (N E ⟨137975961152,56038⟩ E) ⟨137975963136,52892⟩ E)) ⟨137975963648,52116⟩ (N (N (N E ⟨138009511824,771550⟩ E) ⟨138009512208,762677⟩ E) ⟨138009512640,752846⟩ (N E ⟨138009513216,739985⟩ E)))) ⟨138009513984,723260⟩ (N (N (N (N (N E ⟨138017902768,999791⟩ E) ⟨138017904432,951961⟩ E) ⟨138034679254,1735796⟩ (N (N E ⟨138043066824,2231703⟩ E) ⟨138043067592,2180955⟩ E)) ⟨138043068752,2107010⟩ (N (N (N E ⟨138047261410,2449683⟩ E) ⟨138061940624,3460643⟩ E) ⟨138066135061,3744145⟩ (N E ⟨138066135445,3701129⟩ E))) ⟨138081863748,4961913⟩ (N (N (N (N E ⟨138089208424,4873526⟩ E) ⟨138097592451,6346024⟩ E) ⟨138097593138,6216430⟩ (N E ⟨138097594002,6058111⟩ E)) ⟨138097595376,5816583⟩ (N (N (N E ⟨138098641012,6447983⟩ E) ⟨138101789782,6165394⟩ E) ⟨138101791156,5922200⟩ (N E ⟨138101792628,5674822⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab3 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨138110176608,7307488⟩ E) ⟨138110177376,7142447⟩ E) ⟨138110178240,6962309⟩ (N (N E ⟨138110179392,6730872⟩ E) ⟨138110180928,6437051⟩ E)) ⟨138110181376,6354389⟩ (N (N (N E ⟨138143730112,11322883⟩ E) ⟨138146875122,11976262⟩ E) ⟨138160507136,13598607⟩ (N E ⟨138160507296,13533351⟩ E))) ⟨138160507552,13429754⟩ (N (N (N (N E ⟨138164702099,13904145⟩ E) ⟨138164702770,13628347⟩ E) ⟨138164703538,13321024⟩ (N (N E ⟨138167847414,14519572⟩ E) ⟨138177287104,14746045⟩ E)) ⟨138177287936,14389955⟩ (N (N (N E ⟨138199304388,19497310⟩ E) ⟨138210838464,21615453⟩ E) ⟨138210838880,21346411⟩ (N E ⟨138210838992,21274693⟩ E)))) ⟨138210839296,21081544⟩ (N (N (N (N (N E ⟨138210839424,21000874⟩ E) ⟨138210839744,20800883⟩ E) ⟨138210840000,20642603⟩ (N (N E ⟨138227616480,24055442⟩ E) ⟨138231811698,24155585⟩ E)) ⟨138233907397,25624583⟩ (N (N (N E ⟨138233907781,25330574⟩ E) ⟨138236010496,21843389⟩ E) ⟨138240198720,26936529⟩ (N E ⟨138244392912,27851942⟩ E))) ⟨138244393088,27704630⟩ (N (N (N (N E ⟨138244393296,27531788⟩ E) ⟨138244393376,27465670⟩ E) ⟨138244393504,27360293⟩ (N (N E ⟨138244393920,27021293⟩ E) ⟨138244394496,26560533⟩ E)) ⟨138244395328,25912200⟩ (N (N (N E ⟨138244396160,25283541⟩ E) ⟨138244397312,24444246⟩ E) ⟨138244398976,23292494⟩ (N E ⟨138244399104,23206737⟩ E))))) ⟨138250685316,28294285⟩ (N (N (N (N (N (N E ⟨138250686148,27600386⟩ E) ⟨138261170528,30899197⟩ E) ⟨138261170944,30515799⟩ (N (N E ⟨138266414068,31368948⟩ E) ⟨138277947840,34377065⟩ E)) ⟨138277948672,33531164⟩ (N (N (N E ⟨138283190580,35681741⟩ E) ⟨138298921394,36810321⟩ E) ⟨138301017908,37983679⟩ (N E ⟨138311502304,42058702⟩ E))) ⟨138311502384,41957807⟩ (N (N (N (N E ⟨138311502816,41418170⟩ E) ⟨138311502848,41378544⟩ E) ⟨138311503392,40712087⟩ (N (N E ⟨138311504160,39793895⟩ E) ⟨138311504192,39756202⟩ E)) ⟨138311505024,38791672⟩ (N (N (N E ⟨138311505536,38212641⟩ E) ⟨138311506176,37503970⟩ E) ⟨138318842518,43611953⟩ (N E ⟨138333522580,47291511⟩ E)))) ⟨138333522996,46706065⟩ (N (N (N (N (N E ⟨138345057600,49266914⟩ E) ⟨138349250467,52574198⟩ E) ⟨138349250483,52548834⟩ (N (N E ⟨138351348053,52457332⟩ E) ⟨138351348740,51387763⟩ E)) ⟨138361834080,54890345⟩ (N (N (N E ⟨138364979154,56868524⟩ E) ⟨138366028899,55194746⟩ E) ⟨138366029586,54075873⟩ (N E ⟨138366030354,52858454⟩ E))) ⟨138370222076,58289907⟩ (N (N (N (N E ⟨138374416960,58469708⟩ E) ⟨138378612544,57431681⟩ E) ⟨138378613120,56458842⟩ (N E ⟨138378613888,55193558⟩ E)) ⟨138378614016,54986139⟩ (N (N (N E ⟨138378614464,54267805⟩ E) ⟨138378614720,53862596⟩ E) ⟨138378615552,52571534⟩ (N E ⟨138397485457,65565082⟩ E)))))) ⟨138397486128,64259582⟩ (N (N (N (N (N (N (N E ⟨138412165392,70350547⟩ E) ⟨138412165408,70316700⟩ E) ⟨138412165824,69443791⟩ (N (N E ⟨138433138514,73480647⟩ E) ⟨138435234549,76652029⟩ E)) ⟨138435234965,75703801⟩ (N (N (N E ⟨138435235636,74205032⟩ E) ⟨138437332544,75412316⟩ E) ⟨138447817792,80002871⟩ (N E ⟨138462497088,86909521⟩ E))) ⟨138462497472,85913262⟩ (N (N (N (N E ⟨138466691378,88415465⟩ E) ⟨138466692752,84854825⟩ E) ⟨138468788629,88889857⟩ (N (N E ⟨138468790260,84663743⟩ E) ⟨138479274788,91519521⟩ E)) ⟨138496056044,86610382⟩ (N (N (N E ⟨138496057344,83412540⟩ E) ⟨138500248210,93670631⟩ E) ⟨138502343477,99849381⟩ (N E ⟨138502343893,98614778⟩ E)))) ⟨138502344564,96663346⟩ (N (N (N (N (N E ⟨138502345332,94488714⟩ E) ⟨138512829168,103993583⟩ E) ⟨138512829600,102657994⟩ (N (N E ⟨138512829856,101876651⟩ E) ⟨138512830176,100910403⟩ E)) ⟨138512830624,99576831⟩ (N (N (N E ⟨138512831456,97158154⟩ E) ⟨138512832320,94723717⟩ E) ⟨138512832960,92969468⟩ (N E ⟨138512833856,90581218⟩ E))) ⟨138512834496,88922174⟩ (N (N (N (N E ⟨138512834560,88758367⟩ E) ⟨138518072148,105673948⟩ E) ⟨138518072564,104367628⟩ (N (N E ⟨138546385088,112027258⟩ E) ⟨138579938144,130565134⟩ E)) ⟨138579938560,128951258⟩ (N (N (N E ⟨138579938784,128092580⟩ E) ⟨138579939136,126757627⟩ E) ⟨138579939968,123670788⟩ (N E ⟨138579941248,119103089⟩ E))))) ⟨138579942784,113896799⟩ (N (N (N (N (N (N E ⟨138579943424,111811675⟩ E) ⟨138588329284,124442896⟩ E) ⟨138596715168,138578043⟩ (N (N E ⟨138599860818,140288931⟩ E) ⟨138603006885,140250052⟩ E)) ⟨138603007301,138517354⟩ (N (N (N E ⟨138603007988,135714107⟩ E) ⟨138613492176,146948461⟩ E) ⟨138613492400,145963952⟩ (N E ⟨138613492560,145265779⟩ E))) ⟨138613492816,144157367⟩ (N (N (N (N E ⟨138613492992,143401466⟩ E) ⟨138613493248,142310800⟩ E) ⟨138613493568,140962017⟩ (N (N E ⟨138613494336,137789588⟩ E) ⟨138615590976,140800533⟩ E)) ⟨138616638018,147870258⟩ (N (N (N E ⟨138632367408,151651444⟩ E) ⟨138636560965,157034906⟩ E) ⟨138647046480,163173439⟩ (N E ⟨138647046496,163094971⟩ E)))) ⟨138647046912,161071284⟩ (N (N (N (N (N E ⟨138647047328,159078906⟩ E) ⟨138647047712,157267075⟩ E) ⟨138647047744,157117257⟩ (N (N E ⟨138647048576,153283889⟩ E) ⟨138647048832,152127981⟩ E)) ⟨138647049312,149989887⟩ (N (N (N E ⟨138647049408,149566787⟩ E) ⟨138647050176,146235168⟩ E) ⟨138647050240,145961743⟩ (N E ⟨138647051904,139071867⟩ E))) ⟨138647052288,137540034⟩ (N (N (N (N E ⟨138663824256,168446782⟩ E) ⟨138670115429,172954793⟩ E) ⟨138670116229,168865225⟩ (N E ⟨138670116916,165449427⟩ E)) ⟨138670117684,161732558⟩ (N (N (N E ⟨138680600944,179453920⟩ E) ⟨138680601120,178507735⟩ E) ⟨138680601328,177397547⟩ (N E ⟨138680601536,176295982⟩ E))))))) ⟨138680601744,175202959⟩ (N (N (N (N (N (N (N (N E ⟨138680602176,172959785⟩ E) ⟨138680602944,169059892⟩ E) ⟨138684796712,173790077⟩ (N (N E ⟨138697378176,187880050⟩ E) ⟨138697378560,185727380⟩ E)) ⟨138699477808,175507300⟩ (N (N (N E ⟨138699478640,171264679⟩ E) ⟨138705769972,174847611⟩ E) ⟨138714155792,194245360⟩ (N E ⟨138714156208,191842920⟩ E))) ⟨138714156384,190837697⟩ (N (N (N (N E ⟨138714156640,189387284⟩ E) ⟨138714157184,186350654⟩ E) ⟨138714157408,185117990⟩ (N (N E ⟨138714157760,183201478⟩ E) ⟨138714158240,180627868⟩ E)) ⟨138714158528,179105392⟩ (N (N (N E ⟨138714159104,176108286⟩ E) ⟨138714159360,174796383⟩ E) ⟨138714161152,165947180⟩ (N E ⟨138747711872,201892860⟩ E)))) ⟨138764487648,219870410⟩ (N (N (N (N (N E ⟨138764492800,189012513⟩ E) ⟨138769730228,224776864⟩ E) ⟨138769730612,222207363⟩ (N (N E ⟨138781266112,220842983⟩ E) ⟨138781266688,217112671⟩ E)) ⟨138781268032,208710389⟩ (N (N (N E ⟨138781269568,199599621⟩ E) ⟨138781270016,197036445⟩ E) ⟨138785459586,228695035⟩ (N E ⟨138802236850,237813514⟩ E))) ⟨138814819344,248101361⟩ (N (N (N (N E ⟨138814819776,244921823⟩ E) ⟨138814820352,240761295⟩ E) ⟨138817964850,251610074⟩ (N (N E ⟨138831598656,242449039⟩ E) ⟨138833696496,238752305⟩ E)) ⟨138839987158,247944775⟩ (N (N (N E ⟨138839987892,242653998⟩ E) ⟨138848373440,270818384⟩ E) ⟨138848373856,267466885⟩ (N E ⟨138848373960,266637129⟩ E))))) ⟨138848374272,264167102⟩ (N (N (N (N (N (N E ⟨138848375616,253848462⟩ E) ⟨138848376384,248178122⟩ E) ⟨138848376960,244029038⟩ (N (N E ⟨138848377216,242212861⟩ E) ⟨138848378496,233381371⟩ E)) ⟨138848378880,230810749⟩ (N (N (N E ⟨138865150656,281218144⟩ E) ⟨138865154656,249878334⟩ E) ⟨138868297266,275823781⟩ (N E ⟨138871442581,281194094⟩ E))) ⟨138898705934,295053942⟩ (N (N (N (N E ⟨138898706798,287579967⟩ E) ⟨138898708140,276434406⟩ E) ⟨138898709868,262866711⟩ (N (N E ⟨138898710528,257905061⟩ E) ⟨138902904832,260231189⟩ E)) ⟨138915482352,313149472⟩ (N (N (N E ⟨138915482736,309571356⟩ E) ⟨138915483168,305606882⟩ E) ⟨138915483744,300419169⟩ (N E ⟨138915484512,293672343⟩ E)))) ⟨138915485376,286307105⟩ (N (N (N (N (N E ⟨138915485440,285770772⟩ E) ⟨138915485888,282051412⟩ E) ⟨138915486528,276842435⟩ (N (N E ⟨138915486592,276328179⟩ E) ⟨138915486976,273267608⟩ E)) ⟨138915487424,269750329⟩ (N (N (N E ⟨138915487744,267272605⟩ E) ⟨138919677474,308296324⟩ E) ⟨138919678306,300772810⟩ (N E ⟨138919679680,288843910⟩ E))) ⟨138934359088,303605877⟩ (N (N (N (N E ⟨138934359920,296280329⟩ E) ⟨138938551509,323829602⟩ E) ⟨138940650528,307711834⟩ (N E ⟨138954279796,337945747⟩ E)) ⟨138954280180,334088103⟩ (N (N (N E ⟨138965814432,342797936⟩ E) ⟨138965814968,337363557⟩ E) ⟨138970009906,333860136⟩ (N E ⟨138974203584,342972146⟩ E)))))) ⟨138974204736,331464707⟩ (N (N (N (N (N (N (N E ⟨138982592200,348625893⟩ E) ⟨138982592896,341499699⟩ E) ⟨138982594236,328285369⟩ (N (N E ⟨138982595900,312753432⟩ E) ⟨138982596608,306424115⟩ E)) ⟨138990981968,342437812⟩ (N (N (N E ⟨139003563666,363757668⟩ E) ⟨139016145744,382039186⟩ E) ⟨139016146176,377136168⟩ (N E ⟨139016146560,372843836⟩ E))) ⟨139016147136,366519255⟩ (N (N (N (N E ⟨139016147904,358293741⟩ E) ⟨139037117747,391771257⟩ E) ⟨139037118163,386945483⟩ (N (N E ⟨139037118834,379317208⟩ E) ⟨139037119602,370815567⟩ E)) ⟨139037120434,361872643⟩ (N (N (N E ⟨139037121776,348008765⟩ E) ⟨139039214917,393097595⟩ E) ⟨139049700432,403769928⟩ (N E ⟨139049702208,383028239⟩ E)))) ⟨139049703168,372370826⟩ (N (N (N (N (N E ⟨139049704000,363432875⟩ E) ⟨139049704832,354761639⟩ E) ⟨139049705472,348266970⟩ (N (N E ⟨139066477664,416186400⟩ E) ⟨139066477824,414202128⟩ E)) ⟨139066478080,411051840⟩ (N (N (N E ⟨139068577776,382774402⟩ E) ⟨139071720452,421324177⟩ E) ⟨139072768997,422516358⟩ (N E ⟨139083254512,433741905⟩ E))) ⟨139083254528,433533978⟩ (N (N (N (N E ⟨139083254944,428171360⟩ E) ⟨139083255360,422891453⟩ E) ⟨139086401298,422630291⟩ (N E ⟨139100031744,446671253⟩ E)) ⟨139101080624,443445344⟩ (N (N (N E ⟨139104231424,384246896⟩ E) ⟨139106323845,443023378⟩ E) ⟨139116809360,454532817⟩ (N E ⟨139116809520,452366496⟩ E))))) ⟨139116809952,446581595⟩ (N (N (N (N (N (N E ⟨139116809984,446156775⟩ E) ⟨139116810528,439011560⟩ E) ⟨139116810560,438595726⟩ (N (N E ⟨139116811136,431194266⟩ E) ⟨139116811392,427954896⟩ E)) ⟨139116812800,410672362⟩ (N (N (N E ⟨139116813312,404604837⟩ E) ⟨139116814336,392802446⟩ E) ⟨139123101380,451861637⟩ (N E ⟨139133587008,461912681⟩ E))) ⟨139138829716,468471951⟩ (N (N (N (N E ⟨139138830132,462705543⟩ E) ⟨139150363440,486565677⟩ E) ⟨139150363824,481008723⟩ (N (N E ⟨139150363904,479861032⟩ E) ⟨139167141056,494519394⟩ E)) ⟨139167141472,488422779⟩ (N (N (N E ⟨139167143916,454442395⟩ E) ⟨139167145644,432188580⟩ E) ⟨139167145984,427971621⟩ (N E ⟨139171336722,478233063⟩ E)))) ⟨139171339632,439211072⟩ (N (N (N (N (N E ⟨139171340288,430970783⟩ E) ⟨139172383796,500944490⟩ E) ⟨139183918912,498850742⟩ (N (N E ⟨139183920064,482128877⟩ E) ⟨139183920256,479410445⟩ E)) ⟨139183921856,457486189⟩ (N (N (N E ⟨139183922688,446580948⟩ E) ⟨139205939060,516286241⟩ E) ⟨139217472912,533585719⟩ (N E ⟨139217473344,526767038⟩ E))) ⟨139217473920,517844095⟩ (N (N (N (N E ⟨139217474688,506238838⟩ E) ⟨139223765636,519067487⟩ E) ⟨139238444547,549764297⟩ (N E ⟨139238444963,543002832⟩ E)) ⟨139238445650,532062769⟩ (N (N (N E ⟨139238446418,520157153⟩ E) ⟨139238447250,507632960⟩ E) ⟨139238448624,487764359⟩ (N E ⟨139240543540,522336592⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab4 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨139251029952,520928691⟩ E) ⟨139251030656,510338701⟩ E) ⟨139251030784,508442271⟩ (N (N E ⟨139259416912,553990503⟩ E) ⟨139267804608,576626566⟩ E)) ⟨139284581472,597862628⟩ (N (N (N E ⟨139284581888,590486698⟩ E) ⟨139303456656,600358774⟩ E) ⟨139303457520,585194190⟩ (N E ⟨139307651029,602900845⟩ E))) ⟨139307651700,591037755⟩ (N (N (N (N E ⟨139318135920,628438861⟩ E) ⟨139318136992,608703368⟩ E) ⟨139318137120,606399010⟩ (N (N E ⟨139318137536,598984808⟩ E) ⟨139318138080,589459545⟩ E)) ⟨139318138944,574717227⟩ (N (N (N E ⟨139318140160,554741196⟩ E) ⟨139318140928,542571166⟩ E) ⟨139320233856,615837994⟩ (N E ⟨139320234688,600847966⟩ E)))) ⟨139323379284,624253358⟩ (N (N (N (N (N E ⟨139323379700,616580371⟩ E) ⟨139351692712,615510774⟩ E) ⟨139351694376,586332142⟩ (N (N E ⟨139351695360,569889733⟩ E) ⟨139356933364,662478264⟩ E)) ⟨139368468000,667534784⟩ (N (N (N E ⟨139372666480,594121313⟩ E) ⟨139372666880,587305762⟩ E) ⟨139374762228,620691117⟩ (N E ⟨139385246464,658800327⟩ E))) ⟨139385246688,654463077⟩ (N (N (N (N E ⟨139390488628,677898345⟩ E) ⟨139408315892,665463864⟩ E) ⟨139408316724,649459828⟩ (N (N E ⟨139418799696,715387397⟩ E) ⟨139418800128,706258477⟩ E)) ⟨139418800704,694312030⟩ (N (N (N E ⟨139418801152,685194673⟩ E) ⟨139418801984,668656196⟩ E) ⟨139443969652,655936975⟩ (N E ⟨139452354208,747104221⟩ E))))) ⟨139452354624,737926385⟩ (N (N (N (N (N (N E ⟨139452355200,725450150⟩ E) ⟨139452356032,707890986⟩ E) ⟨139452356864,690860185⟩ (N (N E ⟨139452357568,676848108⟩ E) ⟨139452358400,660743480⟩ E)) ⟨139452358656,655884850⟩ (N (N (N E ⟨139469132300,744502096⟩ E) ⟨139469134984,688241636⟩ E) ⟨139469135872,670806273⟩ (N E ⟨139473325779,767214920⟩ E))) ⟨139475423365,759502587⟩ (N (N (N (N E ⟨139475424052,744226017⟩ E) ⟨139485909312,765858291⟩ E) ⟨139502685696,802483171⟩ (N (N E ⟨139519462560,828796562⟩ E) ⟨139519462976,818576427⟩ E)) ⟨139519463088,815851823⟩ (N (N (N E ⟨139519463520,805448294⟩ E) ⟨139519463776,799361491⟩ E) ⟨139519463808,798604692⟩ (N E ⟨139519464096,791833662⟩ E)))) ⟨139519464640,779238697⟩ (N (N (N (N (N E ⟨139519464864,774125415⟩ E) ⟨139519464896,773398376⟩ E) ⟨139519465472,760456517⟩ (N (N E ⟨139519465728,754791564⟩ E) ⟨139527854340,762893197⟩ E)) ⟨139538338800,803232081⟩ (N (N (N E ⟨139542534580,773352393⟩ E) ⟨139553017008,864649867⟩ E) ⟨139553019840,795219611⟩ (N E ⟨139569794784,868448145⟩ E))) ⟨139571893872,822338708⟩ (N (N (N (N E ⟨139575037748,871966381⟩ E) ⟨139578187572,776446514⟩ E) ⟨139578187776,771894260⟩ (N E ⟨139586572416,875862275⟩ E)) ⟨139586572704,868422152⟩ (N (N (N E ⟨139586572832,865140810⟩ E) ⟨139586573248,854582992⟩ E) ⟨139586573472,848964744⟩ (N E ⟨139586573824,840229078⟩ E)))))) ⟨139586574592,821556320⟩ (N (N (N (N (N (N (N E ⟨139586575424,801909404⟩ E) ⟨139586576256,782846616⟩ E) ⟨139586576384,779964392⟩ (N (N E ⟨139603349088,908698536⟩ E) ⟨139620126912,910853484⟩ E)) ⟨139620127168,903975018⟩ (N (N (N E ⟨139620127936,883725771⟩ E) ⟨139620128768,862425114⟩ E) ⟨139636904256,925943726⟩ (N E ⟨139653682752,909697132⟩ E))) ⟨139653684560,863012440⟩ (N (N (N (N E ⟨139653685248,846037011⟩ E) ⟨139657877824,893925345⟩ E) ⟨139657879488,851824915⟩ (N (N E ⟨139670458176,978329376⟩ E) ⟨139674652579,980271819⟩ E)) ⟨139708209584,944919642⟩ (N (N (N E ⟨139708211200,901698480⟩ E) ⟨139712405504,906053519⟩ E) ⟨139720789504,1046999565⟩ (N E ⟨139720789872,1035598074⟩ E)))) ⟨139720790304,1022411138⟩ (N (N (N (N (N E ⟨139720790336,1021442706⟩ E) ⟨139720790880,1005153526⟩ E) ⟨139720792448,959986155⟩ (N (N E ⟨139720793664,926695276⟩ E) ⟨139720794112,914795035⟩ E)) ⟨139740712914,1056212021⟩ (N (N (N E ⟨139740713330,1043266268⟩ E) ⟨139754345152,1048974831⟩ E) ⟨139759587316,1077750328⟩ (N E ⟨139762734896,1024072962⟩ E))) ⟨139792093538,1105183716⟩ (N (N (N (N E ⟨139804676462,1120095271⟩ E) ⟨139806775152,1072969121⟩ E) ⟨139821453696,1140056468⟩ (N (N E ⟨139821454272,1120826646⟩ E) ⟨139821455040,1095813526⟩ E)) ⟨139842425299,1163156018⟩ (N (N (N E ⟨139842425970,1140354466⟩ E) ⟨139871784960,1216616750⟩ E) ⟨139888562240,1235814744⟩ (N E ⟨139907436176,1276515723⟩ E))))) ⟨139909534227,1245614855⟩ (N (N (N (N (N (N E ⟨139909534898,1221208289⟩ E) ⟨139909535666,1194002951⟩ E) ⟨139909536432,1167619341⟩ (N (N E ⟨139909537792,1122547815⟩ E) ⟨139922118432,1214714744⟩ E)) ⟨139922118464,1213577129⟩ (N (N (N E ⟨139922119232,1186669770⟩ E) ⟨139922119296,1184461327⟩ E) ⟨139922120064,1158356720⟩ (N E ⟨139922120448,1145574253⟩ E))) ⟨139922120704,1137150528⟩ (N (N (N (N E ⟨139958817362,1307237706⟩ E) ⟨139972448352,1344887569⟩ E) ⟨139989226624,1325493849⟩ (N (N E ⟨139989227392,1295954558⟩ E) ⟨139989228288,1262524966⟩ E)) ⟨139989229440,1221112853⟩ (N (N (N E ⟨139989229568,1216617055⟩ E) ⟨140011246196,1375626540⟩ E) ⟨140022780448,1394660283⟩ (N E ⟨140022780480,1393341760⟩ E)))) ⟨140022780864,1377640430⟩ (N (N (N (N (N E ⟨140022781056,1369872751⟩ E) ⟨140043752099,1417775830⟩ E) ⟨140043752786,1389371819⟩ (N (N E ⟨140056334976,1436500049⟩ E) ⟨140056337088,1350268023⟩ E)) ⟨140056337148,1347914199⟩ (N (N (N E ⟨140056337920,1318081261⟩ E) ⟨140056338432,1298750327⟩ E) ⟨140106670080,1362097342⟩ (N E ⟨140110861714,1477865436⟩ E))) ⟨140110862482,1444995991⟩ (N (N (N (N E ⟨140112959604,1449094105⟩ E) ⟨140123443872,1528842988⟩ E) ⟨140123446016,1435752141⟩ (N E ⟨140123446080,1433083882⟩ E)) ⟨140123446144,1430421821⟩ (N (N (N E ⟨140123446592,1411959527⟩ E) ⟨140123447232,1386098725⟩ E) ⟨140123447296,1383545347⟩ (N E ⟨140173775136,1619331385⟩ E))))))) ⟨140173777984,1489650854⟩ (N (N (N (N (N (N (N (N E ⟨140173778944,1448885146⟩ E) ⟨140176920946,1620012892⟩ E) ⟨140182164288,1605637963⟩ (N (N E ⟨140190552768,1623943057⟩ E) ⟨140190553184,1604148427⟩ E)) ⟨140190553600,1584654656⟩ (N (N (N E ⟨140190555216,1511682896⟩ E) ⟨140190555520,1498428639⟩ E) ⟨140190556160,1470996705⟩ (N E ⟨140192649920,1627007243⟩ E))) ⟨140195795764,1626032453⟩ (N (N (N (N E ⟨140207332448,1533864418⟩ E) ⟨140209427184,1649284853⟩ E) ⟨140224108608,1605519338⟩ (N (N E ⟨140224110592,1515716701⟩ E) ⟨140240887808,1538324947⟩ E)) ⟨140257664704,1575570569⟩ (N (N (N E ⟨140257665024,1561098561⟩ E) ⟨140280731956,1675069351⟩ E) ⟨140291217216,1715155652⟩ (N E ⟨140305897132,1744421151⟩ E)))) ⟨140324770656,1817202469⟩ (N (N (N (N (N E ⟨140324771232,1786658581⟩ E) ⟨140324771264,1784980596⟩ E) ⟨140324772096,1742036624⟩ (N (N E ⟨140324773632,1666095930⟩ E) ⟨140324773888,1653844664⟩ E)) ⟨140360423104,1825557454⟩ (N (N (N E ⟨140391879840,1903975621⟩ E) ⟨140391879872,1902184080⟩ E) ⟨140391880384,1873804091⟩ (N E ⟨140391880704,1856335274⟩ E))) ⟨140391880960,1842506671⟩ (N (N (N (N E ⟨140391882368,1768710122⟩ E) ⟨140391882752,1749228337⟩ E) ⟨140425434304,1955119362⟩ (N (N E ⟨140425435392,1893781209⟩ E) ⟨140444309168,1956507832⟩ E)) ⟨140444309936,1913082997⟩ (N (N (N E ⟨140444310768,1867390970⟩ E) ⟨140458988480,2023966768⟩ E) ⟨140458989888,1942117880⟩ (N E ⟨140458990656,1899216342⟩ E))))) ⟨140458991232,1867815890⟩ (N (N (N (N (N (N E ⟨140458991488,1854068651⟩ E) ⟨140492544000,2013403101⟩ E) ⟨140509323264,1922474841⟩ (N (N E ⟨140517711872,1935156779⟩ E) ⟨140526098784,2046013453⟩ E)) ⟨140526099648,1995267134⟩ (N (N (N E ⟨140526100160,1965937216⟩ E) ⟨140526100480,1947879594⟩ E) ⟨140546020466,2156185537⟩ (N E ⟨140593209344,2051131731⟩ E))) ⟨140613129394,2265298619⟩ (N (N (N (N E ⟨140626760800,2294161861⟩ E) ⟨140626761216,2266282978⟩ E) ⟨140626761408,2253558749⟩ (N (N E ⟨140647734706,2173648088⟩ E) ⟨140647735296,2136943856⟩ E)) ⟨140651929600,2143615933⟩ (N (N (N E ⟨140660318208,2156990541⟩ E) ⟨140664511808,2208129316⟩ E) ⟨140664512512,2163693069⟩ (N E ⟨140679191216,2275051555⟩ E)))) ⟨140679192048,2220814206⟩ (N (N (N (N (N E ⟨140710649196,2281147024⟩ E) ⟨140714842034,2387812871⟩ E) ⟨140727425600,2364100186⟩ (N (N E ⟨140727426364,2312241003⟩ E) ⟨140727427072,2265447257⟩ E)) ⟨140764124498,2518399235⟩ (N (N (N E ⟨140781953024,2355474918⟩ E) ⟨140794534528,2475365938⟩ E) ⟨140794535296,2420810796⟩ (N E ⟨140794535936,2376492688⟩ E))) ⟨140828088960,2534206708⟩ (N (N (N (N E ⟨140849061522,2494813197⟩ E) ⟨140849061888,2468616629⟩ E) ⟨140861643264,2603401114⟩ (N E ⟨140903587840,2562437838⟩ E)) ⟨140916168850,2730895123⟩ (N (N (N E ⟨140916170752,2584329339⟩ E) ⟨140928751008,2815613683⟩ E) ⟨140928753664,2606310863⟩ (N E ⟨140979084972,2721691938⟩ E)))))) ⟨140983279616,2702602693⟩ (N (N (N (N (N (N (N E ⟨140995860736,2870378285⟩ E) ⟨141062971392,2846363239⟩ E) ⟨141096524840,2991865569⟩ (N (N E ⟨141117497344,2946787818⟩ E) ⟨141130080000,2992202361⟩ E)) ⟨141130080256,2970199867⟩ (N (N (N E ⟨141197188992,3108004162⟩ E) ⟨141197189120,3096561355⟩ E) ⟨141249616304,3350273710⟩ (N E ⟨141264297024,3316186198⟩ E))) ⟨141297852416,3290811149⟩ (N (N (N (N E ⟨141306241024,3307252513⟩ E) ⟨141310435328,3315487799⟩ E) ⟨141316726000,3404081078⟩ (N (N E ⟨141331406720,3369214663⟩ E) ⟨141331406784,3363005254⟩ E)) ⟨141331406848,3356810152⟩ (N (N (N E ⟨141348182348,3562910225⟩ E) ⟨141348184064,3390042950⟩ E) ⟨141402709952,3505578450⟩ (N E ⟨141432069312,3645102712⟩ E)))) ⟨141465624576,3627008003⟩ (N (N (N (N (N E ⟨141507567616,3713468245⟩ E) ⟨141520150528,3739593216⟩ E) ⟨141532733440,3765804281⟩ (N (N E ⟨141551607280,3863707790⟩ E) ⟨141599841664,3979907456⟩ E)) ⟨141645979648,4005562410⟩ (N (N (N E ⟨141666951168,4050720899⟩ E) ⟨141713088512,4150899686⟩ E) ⟨141717282816,4160063320⟩ (N E ⟨141721477120,4169236350⟩ E))) ⟨141734060032,4196811774⟩ (N (N (N (N E ⟨141796974592,4335953225⟩ E) ⟨141801168896,4345304050⟩ E) ⟨141851500544,4458239724⟩ (N (N E ⟨141868277760,4496181990⟩ E) ⟨141985718272,4765910148⟩ E)) ⟨142002495488,4805029944⟩ (N (N (N E ⟨142048632832,4913361425⟩ E) ⟨142054924288,4928219142⟩ E) ⟨142069604352,4962966511⟩ (N E ⟨142086381568,5002813647⟩ E))))) ⟨142136713216,5123221857⟩ (N (N (N (N (N (N E ⟨142254153728,5409194802⟩ E) ⟨142258348032,5419537237⟩ E) ⟨142270930944,5450617679⟩ (N (N E ⟨142283512968,5624258188⟩ E) ⟨142289805312,5497387576⟩ E)) ⟨142338039808,5617721592⟩ (N (N (N E ⟨142405148672,5787071159⟩ E) ⟨142409342976,5797729633⟩ E) ⟨142459674624,5926307948⟩ (N E ⟨142472257536,5958647136⟩ E))) ⟨142522589184,6088778417⟩ (N (N (N (N E ⟨142539366400,6132429910⟩ E) ⟨142606475264,6308399481⟩ E) ⟨142623252480,6352731183⟩ (N (N E ⟨142791024640,6803423869⟩ E) ⟨142807801856,6849223449⟩ E)) ⟨142937825280,7208600993⟩ (N (N (N E ⟨142942019584,7220323464⟩ E) ⟨143076237312,7599659374⟩ E) ⟨143344672768,8382305677⟩ (N E ⟨143462113280,8734456341⟩ E)))) ⟨143545999360,8989516069⟩ (N (N (N (N (N E ⟨143613108224,9195640158⟩ E) ⟨143881543680,10038053565⟩ E) ⟨144124813312,10825193196⟩ (N (N E ⟨144149979136,10907852980⟩ E) ⟨144229670912,11171087318⟩ E)) ⟨144418414592,11803265435⟩ (N (N (N E ⟨144485523456,12030905505⟩ E) ⟨144527466496,12173921802⟩ E) ⟨144531660800,12188254433⟩ (N E ⟨144552632320,12260001552⟩ E))) ⟨144611352576,12461631464⟩ (N (N (N (N E ⟨144867205120,13352401972⟩ E) ⟨145097891840,14171581030⟩ E) ⟨145286635520,14852189218⟩ (N E ⟨145693483008,16347424240⟩ E)) ⟨145819312128,16816763875⟩ (N (N (N E ⟨146029027380,17578910843⟩ E) ⟨146029027440,17548575280⟩ E) ⟨146029027456,17540496856⟩ (N E ⟨146029027520,17508229636⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab5 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨146029027648,17443917607⟩ E) ⟨146029027692,17421878604⟩ E) ⟨146029027696,17419876786⟩ (N (N E ⟨146029027708,17413873056⟩ E) ⟨146029027712,17411872388⟩ E)) ⟨146029027840,17348002527⟩ (N (N (N E ⟨146029027884,17326114956⟩ E) ⟨146029027952,17292356600⟩ E) ⟨146029028080,17229034327⟩ (N E ⟨146029028096,17221139448⟩ E))) ⟨146029028208,17166001795⟩ (N (N (N (N E ⟨146029028224,17158143022⟩ E) ⟨146029028288,17126752890⟩ E) ⟨146029028336,17103257415⟩ (N (N E ⟨146029028352,17095434549⟩ E) ⟨146029028360,17091524795⟩ E)) ⟨146029028400,17071992787⟩ (N (N (N E ⟨146029028464,17040799606⟩ E) ⟨146029028480,17033012451⟩ E) ⟨146029028608,16970875159⟩ (N E ⟨146029028688,16932183286⟩ E)))) ⟨146029028736,16909021113⟩ (N (N (N (N (N E ⟨146029028864,16847448766⟩ E) ⟨146029028960,16801453444⟩ E) ⟨146029028992,16786156578⟩ (N (N E ⟨146029029120,16725143020⟩ E) ⟨146029029184,16694740252⟩ E)) ⟨146029029228,16673878437⟩ (N (N (N E ⟨146029029248,16664406573⟩ E) ⟨146029029304,16637921129⟩ E) ⟨146029029352,16615261211⟩ (N E ⟨146029029376,16603945726⟩ E))) ⟨146029029504,16543758980⟩ (N (N (N (N E ⟨146029029548,16523132823⟩ E) ⟨146029029616,16491319254⟩ E) ⟨146029029736,16435364317⟩ (N (N E ⟨146029029760,16424201838⟩ E) ⟨146029029872,16372235461⟩ E)) ⟨146029029888,16364828489⟩ (N (N (N E ⟨146029029948,16337089643⟩ E) ⟨146029030016,16305723334⟩ E) ⟨146029030128,16254225185⟩ (N E ⟨146029030144,16246884921⟩ E))))) ⟨146029030456,16104574861⟩ (N (N (N (N (N (N E ⟨146029030636,16023181821⟩ E) ⟨146029030656,16014169939⟩ E) ⟨146029030896,15906520205⟩ (N (N E ⟨146029030912,15899375782⟩ E) ⟨146029031008,15856593418⟩ E)) ⟨146029031152,15792689464⟩ (N (N (N E ⟨146029031168,15785608923⟩ E) ⟨146029031296,15729107282⟩ E) ⟨146029031424,15672858345⟩ (N E ⟨146029031680,15561113166⟩ E))) ⟨146029031808,15505614239⟩ (N (N (N (N E ⟨146029031912,15460703539⟩ E) ⟨146029031936,15450362643⟩ E) ⟨146029032064,15395357056⟩ (N (N E ⟨146029032192,15340596165⟩ E) ⟨146029032296,15296282214⟩ E)) ⟨146029032300,15294581031⟩ (N (N (N E ⟨146029032320,15286078662⟩ E) ⟨146029032448,15231803251⟩ E) ⟨146029032512,15204755927⟩ (N E ⟨146029032576,15177768643⟩ E)))) ⟨146029032620,15159249630⟩ (N (N (N (N (N E ⟨146029032632,15154203895⟩ E) ⟨146029032704,15123973555⟩ E) ⟨146029032832,15070416714⟩ (N (N E ⟨146029032944,15023748919⟩ E) ⟨146029032960,15017096854⟩ E)) ⟨146029033200,14917756482⟩ (N (N (N E ⟨146029033216,14911163054⟩ E) ⟨146029033472,14806162186⟩ E) ⟨146029033600,14754008520⟩ (N E ⟨146029033728,14702084403⟩ E))) ⟨146029033784,14679439475⟩ (N (N (N (N E ⟨146029033856,14650388624⟩ E) ⟨146029033984,14598919978⟩ E) ⟨146029034720,14307323494⟩ (N E ⟨146029034752,14294811379⟩ E)) ⟨146029034984,14204506596⟩ (N (N (N E ⟨146029035008,14195205494⟩ E) ⟨146029035136,14145728051⟩ E) ⟨146029035232,14108761445⟩ (N E ⟨146029035264,14096466096⟩ E)))))) ⟨146029035368,14056598649⟩ (N (N (N (N (N (N (N E ⟨146029035520,13998584151⟩ E) ⟨146163253248,14402771777⟩ E) ⟨147111164288,18107522110⟩ (N (N E ⟨150240116736,26555312413⟩ E) ⟨150726656000,27820300340⟩ E)) ⟨151582294016,29852336640⟩ (N (N (N E ⟨151800397824,30325936625⟩ E) ⟨152874139648,32356805476⟩ E) ⟨154082099200,33969258923⟩ (N E ⟨154618970240,34309130482⟩ E))) ⟨154618970624,33876836922⟩ (N (N (N (N E ⟨154618970880,33541516667⟩ E) ⟨154618971264,32970465137⟩ E) ⟨154618971392,32762527531⟩ (N (N E ⟨154618972592,30419630429⟩ E) ⟨154618972672,30240113596⟩ E)) ⟨154618972904,29704611913⟩ (N (N (N E ⟨154618973184,29030101448⟩ E) ⟨154618973288,28772093049⟩ E) ⟨154618973872,27254306961⟩ (N E ⟨154618973944,27059663693⟩ E)))) ⟨154618973952,27037941846⟩ (N (N (N (N (N E ⟨154618974720,24872928246⟩ E) ⟨154618976224,20310965624⟩ E) ⟨154618976736,18710837552⟩ (N (N E ⟨154618977136,17459341625⟩ E) ⟨154618977280,17009903431⟩ E)) ⟨154618978048,14637876662⟩ (N (N (N E ⟨154618978272,13958000492⟩ E) ⟨154618978304,13861447354⟩ E) ⟨156766461952,14582540172⟩ (N E ⟨157303332864,14764143575⟩ E))) ⟨157345275904,14778338584⟩ (N (N (N (N E ⟨157789872128,14928818458⟩ E) ⟨158595178496,15201138791⟩ E) ⟨158637121536,15215302554⟩ (N (N E ⟨158913945600,15308711174⟩ E) ⟨159710863360,15576687041⟩ E)) ⟨159845081088,15621648341⟩ (N (N (N E ⟨159987687424,15669355463⟩ E) ⟨160792993792,15937321714⟩ E) ⟨160834936832,15951202994⟩ (N E ⟨160927211520,15981712824⟩ E))))) ⟨161011097600,16009413693⟩ (N (N (N (N (N (N E ⟨161413750784,16141882826⟩ E) ⟨161497636864,16169372002⟩ E) ⟨161615077376,16207790642⟩ (N (N E ⟨161631854592,16213272601⟩ E) ⟨161816403968,16273465500⟩ E)) ⟨161984176128,16328008463⟩ (N (N (N E ⟨162219057152,16404071343⟩ E) ⟨162932088832,16632681460⟩ E) ⟨163066306560,16675300310⟩ (N E ⟨163108249600,16688590372⟩ E))) ⟨163208913376,15055097072⟩ (N (N (N (N E ⟨163208913960,13094851951⟩ E) ⟨163208914032,12859034356⟩ E) ⟨163208914412,11638396600⟩ (N (N E ⟨163208916128,6731105836⟩ E) ⟨163208916552,5697463721⟩ E)) ⟨163208917096,4488267008⟩ (N (N (N E ⟨163208917212,4248032345⟩ E) ⟨163208917276,4118191710⟩ E) ⟨163208917324,4022079525⟩ (N E ⟨163208917448,3778849012⟩ E)))) ⟨163208917920,2920630997⟩ (N (N (N (N (N E ⟨163208918048,2706598375⟩ E) ⟨163208918144,2551366758⟩ E) ⟨163208918156,2532282763⟩ (N (N E ⟨163208918288,2327064683⟩ E) ⟨163208918840,1562953401⟩ E)) ⟨163208918876,1518420333⟩ (N (N (N E ⟨163208918944,1436078251⟩ E) ⟨163208918968,1407570987⟩ E) ⟨163208919052,1310075146⟩ (N E ⟨163208919288,1055138091⟩ E))) ⟨163208919360,982932448⟩ (N (N (N (N E ⟨163208919456,890706929⟩ E) ⟨163208919568,788952566⟩ E) ⟨163208919824,579938940⟩ (N E ⟨163208919884,535680826⟩ E)) ⟨163208919932,501563617⟩ (N (N (N E ⟨163208919936,498772193⟩ E) ⟨163208919960,482190484⟩ E) ⟨163208919996,457853833⟩ (N E ⟨163208920008,449884421⟩ E))))))) ⟨163208920116,381367472⟩ (N (N (N (N (N (N (N (N E ⟨163208920192,336605342⟩ E) ⟨163208920308,273764269⟩ E) ⟨163208920500,184225501⟩ (N (N E ⟨163208920576,153739518⟩ E) ⟨163208920716,104890089⟩ E)) ⟨163208920904,54086008⟩ (N (N (N E ⟨163208921088,20615427⟩ E) ⟨163561240716,1182802510⟩ E) ⟨163607379832,46060394⟩ (N E ⟨163674487160,944899590⟩ E))) ⟨163741597496,61241851⟩ (N (N (N (N E ⟨163779346432,22761939⟩ E) ⟨163808704952,888416880⟩ E) ⟨163808706488,34648972⟩ (N (N E ⟨163825483592,57974267⟩ E) ⟨164228134152,2406446775⟩ E)) ⟨164228135880,471861935⟩ (N (N (N E ⟨164312020248,2386927665⟩ E) ⟨164312021912,506982941⟩ E) ⟨164400099116,5316586541⟩ (N E ⟨164400101864,862410075⟩ E)))) ⟨164551098368,25624568⟩ (N (N (N (N (N E ⟨164576262308,1196526169⟩ E) ⟨164697898184,321266994⟩ E) ⟨164710480228,999691119⟩ (N (N E ⟨164798558312,4656863911⟩ E) ⟨164853084670,3824653465⟩ E)) ⟨164853086044,1596690809⟩ (N (N (N E ⟨164878253492,204695050⟩ E) ⟨164987303836,1522145098⟩ E) ⟨164987305500,161975313⟩ (N E ⟨165037637324,100099113⟩ E))) ⟨165100548906,3276246397⟩ (N (N (N (N E ⟨165100550280,1247319128⟩ E) ⟨165100552008,65643485⟩ E) ⟨165121522992,271330424⟩ (N (N E ⟨165171854988,122121734⟩ E) ⟨165306072844,82932175⟩ E)) ⟨165352208954,814615617⟩ (N (N (N E ⟨165352210296,55424951⟩ E) ⟨165419317914,731631366⟩ E) ⟨165419319224,41920382⟩ (N E ⟨165419319288,30065678⟩ E))))) ⟨165553537016,30540193⟩ (N (N (N (N (N (N E ⟨165570314184,39384948⟩ E) ⟨165620645888,29415363⟩ E) ⟨165624839696,173038990⟩ (N (N E ⟨165989743512,541236561⟩ E) ⟨166040073866,1933454174⟩ E)) ⟨166040075208,507288359⟩ (N (N (N E ⟨166056851034,2002630407⟩ E) ⟨166056852376,542505923⟩ E) ⟨166293829468,1658895943⟩ (N E ⟨166308511082,256238613⟩ E))) ⟨166541292840,2493552969⟩ (N (N (N (N E ⟨166541293704,1298049156⟩ E) ⟨166597918172,204638671⟩ E) ⟨166732135964,177901668⟩ (N (N E ⟨166759399288,62050407⟩ E) ⟨166860062712,34838719⟩ E)) ⟨166912489962,930524565⟩ (N (N (N E ⟨166912491336,75189846⟩ E) ⟨166983794688,33742546⟩ E) ⟨167008959606,404615693⟩ (N E ⟨167042512614,1848680848⟩ E)))) ⟨167042513478,845637400⟩ (N (N (N (N (N E ⟨167042514820,60290931⟩ E) ⟨167097040896,34068889⟩ E) ⟨167126400916,56781713⟩ (N (N E ⟨167143176334,1310384600⟩ E) ⟨167164149760,34259564⟩ E)) ⟨167180926976,34306912⟩ (N (N (N E ⟨167231258624,34448183⟩ E) ⟨167281587338,2796565758⟩ E) ⟨167281588712,941454607⟩ (N E ⟨167447263368,1326727110⟩ E))) ⟨167447264200,530810871⟩ (N (N (N (N E ⟨167464040536,1384344033⟩ E) ⟨167464041368,567084046⟩ E) ⟨167612937638,2347190265⟩ (N E ⟨167612938980,715700068⟩ E)) ⟨167734573434,1064653931⟩ (N (N (N E ⟨167734574266,370938460⟩ E) ⟨167948483142,865123121⟩ E) ⟨167982037638,806105692⟩ (N E ⟨167982038502,211550071⟩ E)))))) ⟨168053342208,36581420⟩ (N (N (N (N (N (N (N E ⟨168057536512,36591418⟩ E) ⟨168166587958,177350961⟩ E) ⟨168166588416,36848052⟩ (N (N E ⟨168336456600,580206422⟩ E) ⟨168353233896,520052877⟩ E)) ⟨168353234760,81196264⟩ (N (N (N E ⟨168359525654,322552785⟩ E) ⟨168416148780,310527495⟩ E) ⟨168449702948,478139693⟩ (N E ⟨168583921132,212917245⟩ E))) ⟨168588115848,64686094⟩ (N (N (N (N E ⟨168606989498,380132340⟩ E) ⟨168722332136,972747913⟩ E) ⟨168854453670,248685973⟩ (N (N E ⟨168854454272,38314108⟩ E) ⟨168871230870,256949320⟩ E)) ⟨168871231488,38346457⟩ (N (N (N E ⟨168888008166,217635920⟩ E) ⟨169020127972,739240914⟩ E) ⟨169039003351,119544890⟩ (N E ⟨169039003648,38660719⟩ E)))) ⟨169072557783,119672598⟩ (N (N (N (N (N E ⟨169072558080,38721542⟩ E) ⟨169173221223,75069928⟩ E) ⟨169175318232,119706954⟩ (N (N E ⟨169206775655,75159066⟩ E) ⟨169259204424,84097564⟩ E)) ⟨169355673476,67737620⟩ (N (N (N E ⟨169422782436,45083213⟩ E) ⟨169494085632,39426844⟩ E) ⟨169573777408,39547745⟩ (N E ⟨169741549568,39789100⟩ E))) ⟨169742598102,48660107⟩ (N (N (N (N E ⟨169742598144,39790552⟩ E) ⟨169743646720,39792003⟩ E) ⟨169760423936,39815127⟩ (N E ⟨169776152576,39836642⟩ E)) ⟨169793978368,39860833⟩ (N (N (N E ⟨169856892928,39944577⟩ E) ⟨169893593088,39992247⟩ E) ⟨169927147520,40035067⟩ (N E ⟨170163076934,86841469⟩ E))))) ⟨170178805718,49283846⟩ (N (N (N (N (N (N E ⟨170328752128,40490397⟩ E) ⟨170427318272,40585856⟩ E) ⟨170615013376,40749670⟩ (N (N E ⟨171798855696,37992713⟩ E) ⟨171798855712,34887405⟩ E)) ⟨171798855714,34508579⟩ (N (N (N E ⟨171798855728,31914883⟩ E) ⟨171798855769,24903544⟩ E) ⟨171798855782,22862290⟩ (N E ⟨171798855798,20470104⟩ E))) ⟨171798855800,20180399⟩ (N (N (N (N E ⟨171798855818,17666198⟩ E) ⟨171798855829,16212258⟩ E) ⟨171798855850,13610303⟩ (N (N E ⟨171798855861,12338349⟩ E) ⟨171798855866,11780857⟩ E)) ⟨171798855893,8993528⟩ (N (N (N E ⟨171798855894,8897523⟩ E) ⟨171798855936,5331210⟩ E) ⟨171798855942,4896000⟩ (N E ⟨171798855958,3826145⟩ E)))) ⟨171798855962,3579290⟩ (N (N (N (N (N E ⟨171798855968,3224460⟩ E) ⟨171798856006,1407589⟩ E) ⟨171798856034,544145⟩ (N (N E ⟨171798856037,475533⟩ E) ⟨171798856054,174066⟩ E)) ⟨171798856069,31302⟩ (N (N (N E ⟨172224580629,8518⟩ E) ⟨172226677788,15200⟩ E) ⟨172226680480,14256⟩ (N E ⟨172226682144,13709⟩ E))) ⟨172232969092,46959⟩ (N (N (N (N E ⟨172235066148,61529⟩ E) ⟨172235066724,60684⟩ E) ⟨172235067556,59489⟩ (N E ⟨172235068584,58053⟩ E)) ⟨172235069736,56495⟩ (N (N (N E ⟨172251843444,246408⟩ E) ⟨172251844024,243003⟩ E) ⟨172251845304,235695⟩ (N E ⟨172251846464,229308⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab6 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨172256037176,316302⟩ E) ⟨172256037754,311931⟩ E) ⟨172256040256,293861⟩ (N (N E ⟨172258136180,337167⟩ E) ⟨172260231484,390578⟩ E)) ⟨172260232060,385200⟩ (N (N (N E ⟨172260232640,379877⟩ E) ⟨172260232679,379523⟩ E) ⟨172260233366,373344⟩ (N E ⟨172260234134,366585⟩ E))) ⟨172260234966,359435⟩ (N (N (N (N E ⟨172268620672,554902⟩ E) ⟨172268621024,550233⟩ E) ⟨172268621440,544778⟩ (N (N E ⟨172268622304,533664⟩ E) ⟨172268623168,522831⟩ E)) ⟨172268624060,511934⟩ (N (N (N E ⟨172268624704,504243⟩ E) ⟨172268625596,493828⟩ E) ⟨172268625920,490111⟩ (N E ⟨172273862948,686603⟩ E)))) ⟨172273863380,679496⟩ (N (N (N (N (N E ⟨172274912580,694920⟩ E) ⟨172274913348,682276⟩ E) ⟨172289591219,1141001⟩ (N (N E ⟨172289591635,1129599⟩ E) ⟨172291689173,1186022⟩ E)) ⟨172291689844,1167070⟩ (N (N (N E ⟨172291690612,1145841⟩ E) ⟨172302174480,1566528⟩ E) ⟨172302174912,1550310⟩ (N E ⟨172302175488,1529012⟩ E))) ⟨172302176256,1501180⟩ (N (N (N (N E ⟨172302176320,1498890⟩ E) ⟨172302177024,1473979⟩ E) ⟨172302177856,1445203⟩ (N (N E ⟨172304272032,1630134⟩ E) ⟨172304272896,1596679⟩ E)) ⟨172308467076,1761649⟩ (N (N (N E ⟨172318951296,2278561⟩ E) ⟨172318952632,2206419⟩ E) ⟨172318955948,2039323⟩ (N E ⟨172318957568,1963447⟩ E))))) ⟨172323148722,2294444⟩ (N (N (N (N (N (N E ⟨172323149554,2249696⟩ E) ⟨172323151728,2137820⟩ E) ⟨172335728944,3070179⟩ (N (N E ⟨172335729376,3038400⟩ E) ⟨172335729712,3013968⟩ E)) ⟨172335729952,2996666⟩ (N (N (N E ⟨172335730144,2982915⟩ E) ⟨172335730720,2942130⟩ E) ⟨172335731296,2902040⟩ (N E ⟨172335732160,2843177⟩ E))) ⟨172335733824,2733959⟩ (N (N (N (N E ⟨172335734272,2705454⟩ E) ⟨172335734336,2701413⟩ E) ⟨172335734784,2673331⟩ (N (N E ⟨172339923283,3290859⟩ E) ⟨172358798117,4343759⟩ E)) ⟨172358798149,4340418⟩ (N (N (N E ⟨172358798804,4272745⟩ E) ⟨172358798836,4269472⟩ E) ⟨172358799668,4185482⟩ (N E ⟨172360897300,4262549⟩ E)))) ⟨172360897364,4256075⟩ (N (N (N (N (N E ⟨172360899028,4091993⟩ E) ⟨172360900608,3943452⟩ E) ⟨172365090272,4663059⟩ (N (N E ⟨172365091104,4571316⟩ E) ⟨172369283200,5099581⟩ E)) ⟨172369283632,5046742⟩ (N (N (N E ⟨172369284064,4994585⟩ E) ⟨172369284096,4990748⟩ E) ⟨172369284416,4952584⟩ (N E ⟨172369284608,4929861⟩ E))) ⟨172369284928,4892278⟩ (N (N (N (N E ⟨172369285184,4862469⟩ E) ⟨172369285248,4855052⟩ E) ⟨172375575317,5446481⟩ (N E ⟨172375576004,5357430⟩ E)) ⟨172375576772,5260025⟩ (N (N (N E ⟨172375577604,5156988⟩ E) ⟨172386060480,6287592⟩ E) ⟨172386064320,5737187⟩ (N E ⟨172386066432,5460093⟩ E)))))) ⟨172388158928,6248235⟩ (N (N (N (N (N (N (N E ⟨172388158960,6243449⟩ E) ⟨172388159696,6134641⟩ E) ⟨172388159792,6120624⟩ (N (N E ⟨172388160560,6009918⟩ E) ⟨172388160624,6000806⟩ E)) ⟨172390260736,5736847⟩ (N (N (N E ⟨172392352965,6603095⟩ E) ⟨172393401110,6752516⟩ E) ⟨172393401526,6685392⟩ (N E ⟨172402837712,7606800⟩ E))) ⟨172402838272,7504874⟩ (N (N (N (N E ⟨172402838560,7453119⟩ E) ⟨172402838688,7430260⟩ E) ⟨172402839072,7362208⟩ (N (N E ⟨172402839104,7356573⟩ E) ⟨172402839392,7306093⟩ E)) ⟨172402839648,7261585⟩ (N (N (N E ⟨172402839680,7256045⟩ E) ⟨172402840416,7130080⟩ E) ⟨172402840512,7113852⟩ (N E ⟨172402841088,7017448⟩ E)))) ⟨172402841344,6975126⟩ (N (N (N (N (N E ⟨172402842752,6747977⟩ E) ⟨172402843264,6667676⟩ E) ⟨172402843648,6608234⟩ (N (N E ⟨172419615456,8940261⟩ E) ⟨172419618912,8234151⟩ E)) ⟨172432198880,9970961⟩ (N (N (N E ⟨172432199712,9774489⟩ E) ⟨172436392688,10490570⟩ E) ⟨172436393024,10406221⟩ (N E ⟨172436393104,10386263⟩ E))) ⟨172436393536,10279313⟩ (N (N (N (N E ⟨172436393856,10200978⟩ E) ⟨172436394112,10138847⟩ E) ⟨172436394880,9955271⟩ (N (N E ⟨172436395712,9761062⟩ E) ⟨172441635252,11085710⟩ E)) ⟨172446878768,11436733⟩ (N (N (N E ⟨172453173740,11108245⟩ E) ⟨172453175276,10716044⟩ E) ⟨172453175296,10711052⟩ (N E ⟨172457365810,12133881⟩ E))))) ⟨172457367104,11766959⟩ (N (N (N (N (N (N E ⟨172457368242,11455673⟩ E) ⟨172457369584,11101699⟩ E) ⟨172457369600,11097562⟩ (N (N E ⟨172458412116,12925604⟩ E) ⟨172458412532,12796570⟩ E)) ⟨172459461509,12784798⟩ (N (N (N E ⟨172459462196,12575905⟩ E) ⟨172459462964,12347409⟩ E) ⟨172460510054,12905984⟩ (N E ⟨172465752832,13504640⟩ E))) ⟨172469946592,14151218⟩ (N (N (N (N E ⟨172469947456,13860022⟩ E) ⟨172469948000,13680516⟩ E) ⟨172469948224,13607447⟩ (N (N E ⟨172469948320,13576281⟩ E) ⟨172469948576,13493607⟩ E)) ⟨172469949344,13249335⟩ (N (N (N E ⟨172469949696,13139226⟩ E) ⟨172469949952,13059864⟩ E) ⟨172469950016,13040118⟩ (N E ⟨172469950464,12902932⟩ E)))) ⟨172469951296,12652911⟩ (N (N (N (N (N E ⟨172469951680,12539561⟩ E) ⟨172469952128,12408920⟩ E) ⟨172469952512,12298293⟩ (N (N E ⟨172472045824,13688416⟩ E) ⟨172472046656,13420374⟩ E)) ⟨172478337988,14136641⟩ (N (N (N E ⟨172489870226,16212699⟩ E) ⟨172490918435,16483200⟩ E) ⟨172491967764,16312626⟩ (N E ⟨172491968180,16150961⟩ E))) ⟨172495116832,15418356⟩ (N (N (N (N E ⟨172503503808,17011626⟩ E) ⟨172503504640,16679886⟩ E) ⟨172520283712,17905733⟩ (N E ⟨172524475538,19512425⟩ E)) ⟨172524476370,19132386⟩ (N (N (N E ⟨172524477202,18761558⟩ E) ⟨172524478464,18216063⟩ E) ⟨172526573492,19409541⟩ (N E ⟨172526574324,19033275⟩ E))))))) ⟨172537059968,20407884⟩ (N (N (N (N (N (N (N (N E ⟨172537061376,19746721⟩ E) ⟨172541250083,23143895⟩ E) ⟨172542298628,23312082⟩ (N (N E ⟨172542298644,23303101⟩ E) ⟨172544396214,23370115⟩ E)) ⟨172544396630,23138023⟩ (N (N (N E ⟨172545447078,22271362⟩ E) ⟨172545449984,20801560⟩ E) ⟨172556978770,25428509⟩ (N E ⟨172556979186,25175436⟩ E))) ⟨172558027602,25429405⟩ (N (N (N (N E ⟨172559077108,25022831⟩ E) ⟨172570610544,27331819⟩ E) ⟨172570610592,27300313⟩ (N (N E ⟨172570610624,27279334⟩ E) ⟨172570611008,27029154⟩ E)) ⟨172574804866,27975560⟩ (N (N (N E ⟨172587387008,30550387⟩ E) ⟨172587387776,29990464⟩ E) ⟨172587388192,29692528⟩ (N E ⟨172590533186,30739043⟩ E)))) ⟨172590533618,30421397⟩ (N (N (N (N (N E ⟨172591583634,29557928⟩ E) ⟨172591584498,28957673⟩ E) ⟨172591585840,28055236⟩ (N (N E ⟨172591587328,27095347⟩ E) ⟨172593680149,30349256⟩ E)) ⟨172593680820,29867425⟩ (N (N (N E ⟨172604164240,33383585⟩ E) ⟨172604164656,33050442⟩ E) ⟨172604165088,32708874⟩ (N E ⟨172604166496,31625823⟩ E))) ⟨172604167360,30983385⟩ (N (N (N (N E ⟨172604167552,30842843⟩ E) ⟨172604168032,30494960⟩ E) ⟨172604168512,30151971⟩ (N (N E ⟨172604168896,29881047⟩ E) ⟨172604170112,29042964⟩ E)) ⟨172604170240,28956464⟩ (N (N (N E ⟨172612554406,33573179⟩ E) ⟨172623040208,35350893⟩ E) ⟨172623040976,34709185⟩ (N E ⟨172623041072,34629999⟩ E))))) ⟨172623041840,34004576⟩ (N (N (N (N (N (N E ⟨172623041904,33953098⟩ E) ⟨172626184820,36877794⟩ E) ⟨172633525408,37712491⟩ (N (N E ⟨172637719552,38627830⟩ E) ⟨172637719972,38240717⟩ E)) ⟨172637720128,38098169⟩ (N (N (N E ⟨172637720320,37923636⟩ E) ⟨172637720804,37488083⟩ E) ⟨172637720896,37406001⟩ (N E ⟨172637722284,36194472⟩ E))) ⟨172637722664,35871373⟩ (N (N (N (N E ⟨172637724328,34498290⟩ E) ⟨172637724672,34222676⟩ E) ⟨172642962100,39918858⟩ (N (N E ⟨172646109744,38698675⟩ E) ⟨172646111920,36758952⟩ E)) ⟨172646113280,35608173⟩ (N (N (N E ⟨172654497592,40969999⟩ E) ⟨172654498360,40226748⟩ E) ⟨172654499512,39143200⟩ (N E ⟨172654500672,38088754⟩ E)))) ⟨172658690744,42932945⟩ (N (N (N (N (N E ⟨172658692626,41042789⟩ E) ⟨172658695058,38751710⟩ E) ⟨172658696192,37738144⟩ (N (N E ⟨172660788245,42981636⟩ E) ⟨172660788661,42555021⟩ E)) ⟨172660789077,42133689⟩ (N (N (N E ⟨172660789748,41465020⟩ E) ⟨172660790516,40715891⟩ E) ⟨172660791348,39923332⟩ (N E ⟨172660792180,39149971⟩ E))) ⟨172662885052,43752153⟩ (N (N (N (N E ⟨172662885308,43483719⟩ E) ⟨172662885628,43151067⟩ E) ⟨172662885888,42883126⟩ (N E ⟨172662886208,42556204⟩ E)) ⟨172662886976,41784213⟩ (N (N (N E ⟨172667079360,44579050⟩ E) ⟨172671273950,45106844⟩ E) ⟨172671274814,44182883⟩ (N E ⟨172671274816,44180772⟩ E)))))) ⟨172671274824,44172328⟩ (N (N (N (N (N (N (N E ⟨172671275592,43371058⟩ E) ⟨172671276156,42794176⟩ E) ⟨172671276736,42210900⟩ (N (N E ⟨172671276744,42202924⟩ E) ⟨172671277248,41704248⟩ E)) ⟨172671277440,41516215⟩ (N (N (N E ⟨172671277884,41085434⟩ E) ⟨172671277904,41066161⟩ E) ⟨172671278080,40897048⟩ (N E ⟨172671278272,40713553⟩ E))) ⟨172671278976,40049483⟩ (N (N (N (N E ⟨172671279104,39930202⟩ E) ⟨172675468290,45908141⟩ E) ⟨172675469154,44967968⟩ (N (N E ⟨172675470528,43521871⟩ E) ⟨172675473408,40674687⟩ E)) ⟨172676517332,45606974⟩ (N (N (N E ⟨172676517748,45155508⟩ E) ⟨172679664934,44218896⟩ E) ⟨172679666308,42809086⟩ (N E ⟨172681760048,46842559⟩ E)))) ⟨172692245155,49765232⟩ (N (N (N (N (N E ⟨172692245587,49251275⟩ E) ⟨172692246258,48466067⟩ E) ⟨172694345844,46152582⟩ (N (N E ⟨172694346676,45258888⟩ E) ⟨172704829824,50288836⟩ E)) ⟨172704830592,49379670⟩ (N (N (N E ⟨172707974258,52542959⟩ E) ⟨172725799251,57542485⟩ E) ⟨172725799667,56968927⟩ (N E ⟨172725800083,56402499⟩ E))) ⟨172725800754,55503622⟩ (N (N (N (N E ⟨172725801586,54413798⟩ E) ⟨172725802418,53350602⟩ E) ⟨172725803760,51689839⟩ (N E ⟨172725805056,50146920⟩ E)) ⟨172726848212,57247793⟩ (N (N (N E ⟨172727898676,54946422⟩ E) ⟨172729994816,56754436⟩ E) ⟨172729995584,55723320⟩ (N E ⟨172729999360,50981156⟩ E))))) ⟨172738382864,59427261⟩ (N (N (N (N (N (N E ⟨172738383280,58837398⟩ E) ⟨172738383328,58769808⟩ E) ⟨172738383712,58232576⟩ (N (N E ⟨172738383744,58188084⟩ E) ⟨172738384288,57438189⟩ E)) ⟨172738384320,57394454⟩ (N (N (N E ⟨172738385056,56399966⟩ E) ⟨172738385152,56271844⟩ E) ⟨172738385888,55301567⟩ (N E ⟨172738385984,55176556⟩ E))) ⟨172738386752,54189086⟩ (N (N (N (N E ⟨172738386816,54107798⟩ E) ⟨172738387904,52748947⟩ E) ⟨172743626676,59296259⟩ (N (N E ⟨172755159744,63846095⟩ E) ⟨172755162252,60134854⟩ E)) ⟨172755163916,57820695⟩ (N (N (N E ⟨172755165184,56131647⟩ E) ⟨172761452485,63372940⟩ E) ⟨172761453172,62344145⟩ (N E ⟨172762501046,63641234⟩ E)))) ⟨172771938752,65058432⟩ (N (N (N (N (N E ⟨172771939520,63882691⟩ E) ⟨172775083218,67815790⟩ E) ⟨172788714208,72041939⟩ (N (N E ⟨172788714560,71435194⟩ E) ⟨172788714976,70726345⟩ E)) ⟨172792908547,73046404⟩ (N (N (N E ⟨172792908979,72292441⟩ E) ⟨172792909650,71140548⟩ E) ⟨172792910418,69850160⟩ (N E ⟨172792910450,69797032⟩ E))) ⟨172792911282,68433261⟩ (N (N (N (N E ⟨172792911314,68381477⟩ E) ⟨172792912624,66302986⟩ E) ⟨172792913920,64323871⟩ (N E ⟨172795008372,69036137⟩ E)) ⟨172805493984,71827047⟩ (N (N (N E ⟨172805495104,69952638⟩ E) ⟨172805495680,69012469⟩ E) ⟨172805496832,67179058⟩ (N E ⟨172808637218,77052939⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab7 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨172809685763,77385257⟩ E) ⟨172809686179,76615909⟩ E) ⟨172809686850,75395011⟩ (N (N E ⟨172809687618,74027324⟩ E) ⟨172809688450,72580489⟩ E)) ⟨172809689792,70320483⟩ (N (N (N E ⟨172813885440,69117095⟩ E) ⟨172822268464,81132764⟩ E) ⟨172822268896,80294278⟩ (N E ⟨172828560581,81530794⟩ E))) ⟨172828560997,80722410⟩ (N (N (N (N E ⟨172828561413,79924024⟩ E) ⟨172828562100,78627031⟩ E) ⟨172828562868,77208118⟩ (N (N E ⟨172828563700,75706906⟩ E) ⟨172828564532,74242017⟩ E)) ⟨172829609142,81841366⟩ (N (N (N E ⟨172829609974,80228331⟩ E) ⟨172839045744,85582797⟩ E) ⟨172839045888,85286807⟩ (N E ⟨172839046304,84438889⟩ E)))) ⟨172839046500,84043043⟩ (N (N (N (N (N E ⟨172839046720,83601486⟩ E) ⟨172839047744,81584001⟩ E) ⟨172855823392,89351199⟩ (N (N E ⟨172860018104,89652485⟩ E) ⟨172864211836,92086322⟩ E)) ⟨172864217088,81326433⟩ (N (N (N E ⟨172868406720,92000316⟩ E) ⟨172872600336,94745794⟩ E) ⟨172872600720,93875959⟩ (N E ⟨172872600800,93696002⟩ E))) ⟨172872601376,92412965⟩ (N (N (N (N E ⟨172872605696,83458205⟩ E) ⟨172889377952,98727240⟩ E) ⟨172889378368,97748135⟩ (N (N E ⟨172893571955,100693626⟩ E) ⟨172893572387,99654993⟩ E)) ⟨172893573074,98030717⟩ (N (N (N E ⟨172894620148,101942497⟩ E) ⟨172894620948,100001505⟩ E) ⟨172894620980,99924831⟩ (N E ⟨172895671028,96776109⟩ E))))) ⟨172906155264,103500547⟩ (N (N (N (N (N (N E ⟨172906155840,102083520⟩ E) ⟨172906156608,100231674⟩ E) ⟨172906156672,100079257⟩ (N (N E ⟨172906158060,96843880⟩ E) ⟨172906159016,94691313⟩ E)) ⟨172906160128,92262208⟩ (N (N (N E ⟨172911398148,105078564⟩ E) ⟨172913496150,103590007⟩ E) ⟨172922935616,100828171⟩ (N E ⟨172927126883,109665241⟩ E))) ⟨172927127570,107878487⟩ (N (N (N (N E ⟨172927128402,105763074⟩ E) ⟨172927129234,103699279⟩ E) ⟨172927130608,100400063⟩ (N (N E ⟨172927131648,97989758⟩ E) ⟨172928175796,109107153⟩ E)) ⟨172929223892,110695692⟩ (N (N (N E ⟨172931322614,107255985⟩ E) ⟨172939709728,113786810⟩ E) ⟨172939710064,112874973⟩ (N E ⟨172939710304,112229251⟩ E)))) ⟨172939710496,111715996⟩ (N (N (N (N (N E ⟨172939711072,110193742⟩ E) ⟨172939711104,110109935⟩ E) ⟨172939711936,107958664⟩ (N (N E ⟨172939712192,107307328⟩ E) ⟨172939712768,105859694⟩ E)) ⟨172939713536,103967291⟩ (N (N (N E ⟨172939714512,101622983⟩ E) ⟨172939714560,101509403⟩ E) ⟨172943905506,111138422⟩ (N E ⟨172943907648,105657698⟩ E))) ⟨172943908864,102696473⟩ (N (N (N (N E ⟨172962780724,114678513⟩ E) ⟨172973264960,122287516⟩ E) ⟨172973265600,120438176⟩ (N E ⟨172980604246,126927501⟩ E)) ⟨172980605078,124428224⟩ (N (N (N E ⟨172993186802,132289339⟩ E) ⟨172994235779,131378942⟩ E) ⟨172994236466,129238818⟩ (N E ⟨172994237234,126897713⟩ E)))))) ⟨172994238098,124327000⟩ (N (N (N (N (N (N (N E ⟨172994239408,120552228⟩ E) ⟨172994239472,120371509⟩ E) ⟨172994240512,117481749⟩ (N (N E ⟨172995284340,131782620⟩ E) ⟨172996335220,125090509⟩ E)) ⟨172998432310,125952125⟩ (N (N (N E ⟨172998434816,118758900⟩ E) ⟨173006818208,137268293⟩ E) ⟨173006818624,135904882⟩ (N E ⟨173006818992,134712877⟩ E))) ⟨173006819040,134558363⟩ (N (N (N (N E ⟨173006819424,133330199⟩ E) ⟨173006819456,133228486⟩ E) ⟨173006820544,129827243⟩ (N (N E ⟨173006820768,129140517⟩ E) ⟨173006821888,125774218⟩ E)) ⟨173006823424,121333996⟩ (N (N (N E ⟨173013112388,130707529⟩ E) ⟨173019406336,125248627⟩ E) ⟨173023595808,141875498⟩ (N E ⟨173031987104,135886242⟩ E)))) ⟨173040372272,150561849⟩ (N (N (N (N (N E ⟨173040373040,147809478⟩ E) ⟨173040373456,146344871⟩ E) ⟨173040373888,144843090⟩ (N (N E ⟨173040374464,142870564⟩ E) ⟨173040376064,137564873⟩ E)) ⟨173043518450,150086799⟩ (N (N (N E ⟨173044567904,147338455⟩ E) ⟨173048764848,139814749⟩ E) ⟨173048766464,134625406⟩ (N E ⟨173057149920,155167988⟩ E))) ⟨173057151928,147905370⟩ (N (N (N (N E ⟨173063442548,153154576⟩ E) ⟨173063444212,147224762⟩ E) ⟨173065540502,151008832⟩ (N (N E ⟨173065541696,146804178⟩ E) ⟨173073927808,158875835⟩ E)) ⟨173073928072,157876522⟩ (N (N (N E ⟨173073928352,156825218⟩ E) ⟨173073928840,155013782⟩ E) ⟨173073929672,151985346⟩ (N E ⟨173073930832,147885417⟩ E))))) ⟨173076024672,160762494⟩ (N (N (N (N (N (N E ⟨173076025536,157476993⟩ E) ⟨173079170516,161497976⟩ E) ⟨173079170548,161374294⟩ (N (N E ⟨173080219716,159496350⟩ E) ⟨173092801872,167196119⟩ E)) ⟨173092802704,163903812⟩ (N (N (N E ⟨173095947716,167937390⟩ E) ⟨173096996277,168400580⟩ E) ⟨173096996693,166733264⟩ (N E ⟨173096996980,165594998⟩ E))) ⟨173107482788,169388624⟩ (N (N (N (N E ⟨173107484992,160772817⟩ E) ⟨173112725364,172645881⟩ E) ⟨173132650198,172525387⟩ (N (N E ⟨173132652544,163288490⟩ E) ⟨173141037280,182193218⟩ E)) ⟨173141037856,179713455⟩ (N (N (N E ⟨173141038624,176472385⟩ E) ⟨173141038784,175806386⟩ E) ⟨173141039456,173043275⟩ (N E ⟨173141040320,169570007⟩ E)))) ⟨173141040576,168557666⟩ (N (N (N (N (N E ⟨173141041152,166307388⟩ E) ⟨173145230419,189052961⟩ E) ⟨173162007283,197643796⟩ (N (N E ⟨173162007699,195678675⟩ E) ⟨173164107572,184228481⟩ E)) ⟨173174590896,199579387⟩ (N (N (N E ⟨173174590976,199197461⟩ E) ⟨173174591360,197376883⟩ E) ⟨173174591552,196474397⟩ (N E ⟨173174591968,194536645⟩ E))) ⟨173174592832,190587854⟩ (N (N (N (N E ⟨173174593088,189437131⟩ E) ⟨173174595584,178660457⟩ E) ⟨173179833908,201143722⟩ (N E ⟨173180882453,201733589⟩ E)) ⟨173180883140,198450256⟩ (N (N (N E ⟨173191368128,206585936⟩ E) ⟨173191368544,204540685⟩ E) ⟨173193466064,203629991⟩ (N E ⟨173195563347,203872080⟩ E))))))) ⟨173195564018,200646340⟩ (N (N (N (N (N (N (N (N E ⟨173195564786,197032216⟩ E) ⟨173195565618,193208297⟩ E) ⟨173195566256,190338716⟩ (N (N E ⟨173195567104,186606590⟩ E) ⟨173197662004,197573199⟩ E)) ⟨173199760500,192250851⟩ (N (N (N E ⟨173208145440,213302108⟩ E) ⟨173208146016,210386786⟩ E) ⟨173208146208,209426098⟩ (N E ⟨173208146784,206576757⟩ E))) ⟨173208146848,206263164⟩ (N (N (N (N E ⟨173208147712,202087352⟩ E) ⟨173208148688,197496580⟩ E) ⟨173208149248,194921360⟩ (N (N E ⟨173208150016,191457522⟩ E) ⟨173210242560,214373740⟩ E)) ⟨173216537668,199123650⟩ (N (N (N E ⟨173224922592,220954443⟩ E) ⟨173231214900,219227048⟩ E) ⟨173231216564,210748538⟩ (N E ⟨173237506336,222072845⟩ E)))) ⟨173241699824,228316129⟩ (N (N (N (N (N E ⟨173241700160,226488776⟩ E) ⟨173241700240,226056391⟩ E) ⟨173241700316,225646580⟩ (N (N E ⟨173241700480,224765412⟩ E) ⟨173241700672,223739262⟩ E)) ⟨173241701248,220695760⟩ (N (N (N E ⟨173241701824,217703853⟩ E) ⟨173241703000,211751228⟩ E) ⟨173241704448,204698608⟩ (N E ⟨173245893795,232041386⟩ E))) ⟨173245893811,231952348⟩ (N (N (N (N E ⟨173247992068,226830933⟩ E) ⟨173247992836,222727081⟩ E) ⟨173260575024,232181934⟩ (N (N E ⟨173260575856,227636701⟩ E) ⟨173261622482,238951316⟩ E)) ⟨173262672946,228892620⟩ (N (N (N E ⟨173264768613,238089381⟩ E) ⟨173264769029,235734555⟩ E) ⟨173264769332,234037692⟩ (N E ⟨173266865404,241123163⟩ E))))) ⟨173266870272,214920817⟩ (N (N (N (N (N (N E ⟨173271059968,241552561⟩ E) ⟨173271060288,239711066⟩ E) ⟨173275253904,245643689⟩ (N (N E ⟨173275253920,245549421⟩ E) ⟨173275254336,243114241⟩ E)) ⟨173275254592,241630670⟩ (N (N (N E ⟨173275254624,241446021⟩ E) ⟨173275254752,240709186⟩ E) ⟨173275255168,238333809⟩ (N E ⟨173275255456,236706472⟩ E))) ⟨173275255712,235271600⟩ (N (N (N (N E ⟨173275255744,235093006⟩ E) ⟨173275256576,230508509⟩ E) ⟨173275256640,230160505⟩ (N (N E ⟨173275256832,229120428⟩ E) ⟨173275257312,226545833⟩ E)) ⟨173275257408,226035262⟩ (N (N (N E ⟨173275258176,222002062⟩ E) ⟨173275258240,221670039⟩ E) ⟨173275258880,218383722⟩ (N E ⟨173294128785,251413424⟩ E)))) ⟨173294129456,247418811⟩ (N (N (N (N (N E ⟨173294130224,242943643⟩ E) ⟨173297275316,248091138⟩ E) ⟨173304614944,253921167⟩ (N (N E ⟨173308809088,256870844⟩ E) ⟨173308809600,253753684⟩ E)) ⟨173308810176,250303206⟩ (N (N (N E ⟨173308810752,246911199⟩ E) ⟨173308810944,245793318⟩ E) ⟨173313004712,250854284⟩ (N E ⟨173325585984,266893339⟩ E))) ⟨173329782642,254295888⟩ (N (N (N (N E ⟨173329783474,249364307⟩ E) ⟨173333978420,247503382⟩ E) ⟨173342363216,274961550⟩ (N E ⟨173342363632,272241698⟩ E)) ⟨173342364064,269452751⟩ (N (N (N E ⟨173342364096,269247586⟩ E) ⟨173342364384,267409870⟩ E) ⟨173342364608,265991368⟩ (N E ⟨173342364640,265789494⟩ E)))))) ⟨173342365408,261001479⟩ (N (N (N (N (N (N (N E ⟨173342366240,255935538⟩ E) ⟨173342366528,254210634⟩ E) ⟨173342367104,250804215⟩ (N (N E ⟨173342367360,249308580⟩ E) ⟨173342367744,247085977⟩ E)) ⟨173344461888,266178378⟩ (N (N (N E ⟨173346557219,279027538⟩ E) ⟨173350756352,250798626⟩ E) ⟨173354950656,252665356⟩ (N E ⟨173364383412,285189623⟩ E))) ⟨173364383828,282370277⟩ (N (N (N (N E ⟨173364384244,279585698⟩ E) ⟨173365434356,270092006⟩ E) ⟨173375917984,289339706⟩ (N (N E ⟨173375918752,284093919⟩ E) ⟨173375919616,278333763⟩ E)) ⟨173375919680,277912920⟩ (N (N (N E ⟨173375919872,276655155⟩ E) ⟨173392694912,299869136⟩ E) ⟨173392695328,296903753⟩ (N E ⟨173395840754,300661752⟩ E)))) ⟨173396890147,295388053⟩ (N (N (N (N (N E ⟨173396890834,290609869⟩ E) ⟨173396891602,285382165⟩ E) ⟨173396892434,279850826⟩ (N (N E ⟨173398989556,281048346⟩ E) ⟨173401087348,277853197⟩ E)) ⟨173401088000,273657154⟩ (N (N (N E ⟨173409474112,294306471⟩ E) ⟨173409476032,281319677⟩ E) ⟨173409476096,280899255⟩ (N E ⟨173409476608,277564003⟩ E))) ⟨173417863044,296203282⟩ (N (N (N (N E ⟨173428347344,312029755⟩ E) ⟨173429395250,317606408⟩ E) ⟨173430445840,303297403⟩ (N E ⟨173430447504,291669037⟩ E)) ⟨173443026240,328711158⟩ (N (N (N E ⟨173443026656,325454353⟩ E) ⟨173443027072,322237797⟩ E) ⟨173443029288,305757670⟩ (N E ⟨173459804256,331405289⟩ E))))) ⟨173459804728,327700560⟩ (N (N (N (N (N (N E ⟨173459807808,304755516⟩ E) ⟨173459808256,301587550⟩ E) ⟨173463999762,324258245⟩ (N (N E ⟨173466095797,334104412⟩ E) ⟨173466096213,330811556⟩ E)) ⟨173466096884,325585297⟩ (N (N (N E ⟨173468193344,332093436⟩ E) ⟨173468194624,322173406⟩ E) ⟨173472387074,338935636⟩ (N E ⟨173476580688,346889877⟩ E))) ⟨173476581072,343716125⟩ (N (N (N (N E ⟨173476581152,343059503⟩ E) ⟨173476581960,336514750⟩ E) ⟨173476583616,323582017⟩ (N (N E ⟨173476585040,312954696⟩ E) ⟨173476585472,309817247⟩ E)) ⟨173480777600,328215330⟩ (N (N (N E ⟨173480779328,315168206⟩ E) ⟨173481824884,338978006⟩ E) ⟨173493358304,352834327⟩ (N E ⟨173493358720,349347168⟩ E)))) ⟨173493362688,318157845⟩ (N (N (N (N (N E ⟨173495457136,340131921⟩ E) ⟨173496504146,353617643⟩ E) ⟨173497553458,348039779⟩ (N (N E ⟨173497554162,342272550⟩ E) ⟨173497554832,336894423⟩ E)) ⟨173510135616,361376892⟩ (N (N (N E ⟨173510136036,357773235⟩ E) ⟨173510136868,350766267⟩ E) ⟨173510136960,350002035⟩ (N E ⟨173510137024,349471624⟩ E))) ⟨173510138560,337037997⟩ (N (N (N (N E ⟨173510139904,326609328⟩ E) ⟨173512235072,343265201⟩ E) ⟨173513281346,363126536⟩ (N E ⟨173526917120,335171679⟩ E)) ⟨173529010736,365433537⟩ (N (N (N E ⟨173529011504,358833753⟩ E) ⟨173531109458,353230824⟩ E) ⟨173531110290,346389537⟩ (N E ⟨173533204309,374247200⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab8 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨173533205812,361106093⟩ E) ⟨173533206580,354613983⟩ E) ⟨173533207412,347744705⟩ (N (N E ⟨173535301952,371073514⟩ E) ⟨173535305268,343156739⟩ E)) ⟨173535305728,339494425⟩ (N (N (N E ⟨173543690416,377120482⟩ E) ⟨173543690848,373261517⟩ E) ⟨173543691424,368192716⟩ (N E ⟨173543694336,343844881⟩ E))) ⟨173548932980,382995165⟩ (N (N (N (N E ⟨173548933396,379213249⟩ E) ⟨173548933812,375477916⟩ E) ⟨173566761908,365220320⟩ (N (N E ⟨173568859680,361082965⟩ E) ⟨173577244478,400027081⟩ E)) ⟨173577245888,386830029⟩ (N (N (N E ⟨173581438818,402160760⟩ E) ⟨173598216786,404826508⟩ E) ⟨173598216818,404518596⟩ (N E ⟨173598217650,396614670⟩ E)))) ⟨173610799344,415751352⟩ (N (N (N (N (N E ⟨173610799392,415276130⟩ E) ⟨173610799776,411498704⟩ E) ⟨173610799808,411185862⟩ (N (N E ⟨173610800320,406220595⟩ E) ⟨173610800352,405912761⟩ E)) ⟨173610800384,405605220⟩ (N (N (N E ⟨173610800896,400723951⟩ E) ⟨173610801120,398611504⟩ E) ⟨173610801216,397710433⟩ (N E ⟨173610802048,390006867⟩ E))) ⟨173610803200,379645803⟩ (N (N (N (N E ⟨173613944786,420495319⟩ E) ⟨173614993315,421601854⟩ E) ⟨173614993986,414914049⟩ (N (N E ⟨173627576160,429939680⟩ E) ⟨173633868133,428480632⟩ E)) ⟨173633868549,424262032⟩ (N (N (N E ⟨173633869236,417408324⟩ E) ⟨173644353392,440095447⟩ E) ⟨173644353808,435749586⟩ (N E ⟨173644354240,431293225⟩ E))))) ⟨173644354816,425439685⟩ (N (N (N (N (N (N E ⟨173644355584,417788628⟩ E) ⟨173644356416,409693130⟩ E) ⟨173647499282,440337761⟩ (N (N E ⟨173663229248,436143020⟩ E) ⟨173677907856,460750274⟩ E)) ⟨173677909280,445409555⟩ (N (N (N E ⟨173677910048,437400865⟩ E) ⟨173677911168,426041536⟩ E) ⟨173677911360,424131421⟩ (N E ⟨173677912000,417841225⟩ E))) ⟨173677912064,417218641⟩ (N (N (N (N E ⟨173682102914,455157497⟩ E) ⟨173682103682,446941254⟩ E) ⟨173682106368,419625740⟩ (N (N E ⟨173694685504,466596838⟩ E) ⟨173698880946,456750998⟩ E)) ⟨173698880978,456405369⟩ (N (N (N E ⟨173700976645,474138996⟩ E) ⟨173700977477,464840786⟩ E) ⟨173700978164,457334381⟩ (N E ⟨173700978932,449121486⟩ E)))) ⟨173700979764,440431220⟩ (N (N (N (N (N E ⟨173711461952,486118915⟩ E) ⟨173711462368,481309888⟩ E) ⟨173711462784,476560206⟩ (N (N E ⟨173711464512,457446981⟩ E) ⟨173711465344,448586330⟩ E)) ⟨173711466496,436669023⟩ (N (N (N E ⟨173714608178,482399896⟩ E) ⟨173715658792,460286841⟩ E) ⟨173730339888,458131587⟩ (N E ⟨173730340720,449309528⟩ E))) ⟨173745017632,493365267⟩ (N (N (N (N E ⟨173745019068,476891099⟩ E) ⟨173745020288,463432251⟩ E) ⟨173745020796,457968306⟩ (N E ⟨173745020928,456561745⟩ E)) ⟨173778571248,525449200⟩ (N (N (N E ⟨173778571328,524447129⟩ E) ⟨173778571904,517302311⟩ E) ⟨173795348896,531334784⟩ (N E ⟨173795350030,517230078⟩ E)))))) ⟨173795350894,506796804⟩ (N (N (N (N (N (N (N E ⟨173795352236,491107741⟩ E) ⟨173795352300,490374810⟩ E) ⟨173795352576,487229667⟩ (N (N E ⟨173799543602,529089264⟩ E) ⟨173799543634,528687373⟩ E)) ⟨173799544466,518370895⟩ (N (N (N E ⟨173800591444,539129233⟩ E) ⟨173800591860,533812640⟩ E) ⟨173803741184,492437631⟩ (N E ⟨173812125792,546877779⟩ E))) ⟨173812126560,536974018⟩ (N (N (N (N E ⟨173812128064,518220314⟩ E) ⟨173812128256,515885565⟩ E) ⟨173812129216,504407133⟩ (N (N E ⟨173812129792,497673197⟩ E) ⟨173816320802,540605025⟩ E)) ⟨173816321570,530855515⟩ (N (N (N E ⟨173816322402,520540357⟩ E) ⟨173816323776,504048109⟩ E) ⟨173828902944,559328457⟩ (N E ⟨173845680176,570847036⟩ E)))) ⟨173845680592,565216456⟩ (N (N (N (N (N E ⟨173845681024,559442626⟩ E) ⟨173845681600,551858427⟩ E) ⟨173862459064,560024763⟩ (N (N E ⟨173862460736,538441842⟩ E) ⟨173864558576,531218491⟩ E)) ⟨173870847680,565657656⟩ (N (N (N E ⟨173870848832,550523902⟩ E) ⟨173879234256,599695556⟩ E) ⟨173879234272,599466210⟩ (N E ⟨173879234688,593541520⟩ E))) ⟨173879235104,587689871⟩ (N (N (N (N E ⟨173879235208,586238245⟩ E) ⟨173879235520,581910185⟩ E) ⟨173879236296,571317536⟩ (N (N E ⟨173879237440,556137435⟩ E) ⟨173879237952,549507036⟩ E)) ⟨173879238332,544649852⟩ (N (N (N E ⟨173879238656,540550799⟩ E) ⟨173887626064,561568494⟩ E) ⟨173896015872,551545877⟩ (N E ⟨173899158514,595272499⟩ E))))) ⟨173900207762,586609684⟩ (N (N (N (N (N (N E ⟨173901254852,608424871⟩ E) ⟨173902303829,603396311⟩ E) ⟨173912788720,623736697⟩ (N (N E ⟨173912789104,618044162⟩ E) ⟨173912789520,611950366⟩ E)) ⟨173912789952,605701506⟩ (N (N (N E ⟨173912791296,586764147⟩ E) ⟨173929565952,635926493⟩ E) ⟨173929566336,630123260⟩ (N E ⟨173933764608,576687623⟩ E))) ⟨173937958912,579515563⟩ (N (N (N (N E ⟨173946343568,642313929⟩ E) ⟨173946343984,635982041⟩ E) ⟨173946344416,629489014⟩ (N (N E ⟨173946344904,622253688⟩ E) ⟨173946344960,621430071⟩ E)) ⟨173946344992,620960045⟩ (N (N (N E ⟨173946345760,609811603⟩ E) ⟨173946346592,598015091⟩ E) ⟨173946347456,586065323⟩ (N E ⟨173946347520,585192084⟩ E)))) ⟨173950541632,590678050⟩ (N (N (N (N (N E ⟨173950541824,588040663⟩ E) ⟨173965217936,656443232⟩ E) ⟨173965220336,620184259⟩ (N (N E ⟨173965221168,608201607⟩ E) ⟨173965221888,598064850⟩ E)) ⟨173971512608,612826061⟩ (N (N (N E ⟨173979901864,609421555⟩ E) ⟨173979901952,608173262⟩ E) ⟨173981995200,668365625⟩ (N E ⟨173985141012,669413873⟩ E))) ⟨173985141428,662820001⟩ (N (N (N (N E ⟨173986191876,634887121⟩ E) ⟨173996675264,679553542⟩ E) ⟨173996675680,672856456⟩ (N E ⟨173996679168,619828826⟩ E)) ⟨173997723952,678542840⟩ (N (N (N E ⟨173998774832,643303652⟩ E) ⟨174000871154,657553209⟩ E) ⟨174013454464,660650349⟩ (N E ⟨174013454688,657175545⟩ E))))))) ⟨174013456188,634486220⟩ (N (N (N (N (N (N (N (N E ⟨174013456384,631594310⟩ E) ⟨174047007008,716970261⟩ E) ⟨174047007424,709908451⟩ (N (N E ⟨174047009152,681489276⟩ E) ⟨174047009984,668313559⟩ E)) ⟨174053299204,709329504⟩ (N (N (N E ⟨174063784608,723558305⟩ E) ⟨174063788012,667860883⟩ E) ⟨174063788032,667549791⟩ (N E ⟨174067978995,725422123⟩ E))) ⟨174067979411,718296801⟩ (N (N (N (N E ⟨174067980082,706987216⟩ E) ⟨174067980850,694314612⟩ E) ⟨174067981682,680904825⟩ (N (N E ⟨174067982336,670590673⟩ E) ⟨174070076165,726758830⟩ E)) ⟨174078465148,726868076⟩ (N (N (N E ⟨174080561040,750678474⟩ E) ⟨174080561424,743833924⟩ E) ⟨174080562080,732320692⟩ (N E ⟨174080564288,695170427⟩ E)))) ⟨174080565248,679754458⟩ (N (N (N (N (N E ⟨174097338656,757020483⟩ E) ⟨174097339072,749564199⟩ E) ⟨174099436592,744705610⟩ (N (N E ⟨174099439616,693615791⟩ E) ⟨174105729492,724569245⟩ E)) ⟨174114117312,744731331⟩ (N (N (N E ⟨174114117376,743606568⟩ E) ⟨174116213952,755476403⟩ E) ⟨174117262546,755989609⟩ (N E ⟨174120409732,732855986⟩ E))) ⟨174132992752,740710512⟩ (N (N (N (N E ⟨174135091200,720176725⟩ E) ⟨174147670400,796326976⟩ E) ⟨174147670688,790889677⟩ (N (N E ⟨174147670768,789387561⟩ E) ⟨174147671200,781337498⟩ E)) ⟨174147671232,780745290⟩ (N (N (N E ⟨174147671776,770763090⟩ E) ⟨174147671808,770180886⟩ E) ⟨174147672640,755234758⟩ (N E ⟨174147672896,750709054⟩ E))))) ⟨174147673216,745099507⟩ (N (N (N (N (N (N E ⟨174147673472,740649566⟩ E) ⟨174147674112,729669240⟩ E) ⟨174156062720,736031785⟩ (N (N E ⟨174169691380,797695273⟩ E) ⟨174181225120,818653031⟩ E)) ⟨174181225152,818030649⟩ (N (N (N E ⟨174181225984,802054403⟩ E) ⟨174181227840,767797599⟩ E) ⟨174189617152,761755430⟩ (N E ⟨174200100752,809870985⟩ E))) ⟨174200101616,793571512⟩ (N (N (N (N E ⟨174202197970,810324023⟩ E) ⟨174202200064,771514533⟩ E) ⟨174214780128,835394153⟩ (N (N E ⟨174214780160,834761213⟩ E) ⟨174214780256,832865988⟩ E)) ⟨174214780672,824715253⟩ (N (N (N E ⟨174214780704,824092413⟩ E) ⟨174214781472,809319167⟩ E) ⟨174214782144,796663325⟩ (N E ⟨174214782592,788363405⟩ E)))) ⟨174214782976,781335090⟩ (N (N (N (N (N E ⟨174216877952,823956127⟩ E) ⟨174216878784,807978385⟩ E) ⟨174233656112,819446311⟩ (N (N E ⟨174236799476,869226686⟩ E) ⟨174236800308,852230189⟩ E)) ⟨174248334160,871947779⟩ (N (N (N E ⟨174248334592,863060823⟩ E) ⟨174248335168,851386989⟩ E) ⟨174248335936,836127296⟩ (N E ⟨174248336768,819979896⟩ E))) ⟨174248337408,807823477⟩ (N (N (N (N E ⟨174265114624,821231318⟩ E) ⟨174269305795,887630111⟩ E) ⟨174269306211,878922243⟩ (N E ⟨174269306898,864774258⟩ E)) ⟨174269307666,849293623⟩ (N (N (N E ⟨174269308498,832911953⟩ E) ⟨174269308928,824600314⟩ E) ⟨174281888208,909272005⟩ (N E ⟨174281889280,886439905⟩ E)))))) ⟨174281890752,856243734⟩ (N (N (N (N (N (N (N E ⟨174281891008,851124265⟩ E) ⟨174281891840,834748172⟩ E) ⟨174290278992,870705491⟩ (N (N E ⟨174290280448,841547457⟩ E) ⟨174298665440,923762476⟩ E)) ⟨174298665856,914674212⟩ (N (N (N E ⟨174298669056,848373970⟩ E) ⟨174307057664,855227704⟩ E) ⟨174315442288,946983261⟩ (N E ⟨174315442304,946621999⟩ E))) ⟨174315442720,937289376⟩ (N (N (N (N E ⟨174315443136,928071525⟩ E) ⟨174318588482,939342437⟩ E) ⟨174332219520,961822580⟩ (N (N E ⟨174334317872,936639688⟩ E) ⟨174338512948,923361243⟩ E)) ⟨174348997136,967877361⟩ (N (N (N E ⟨174349000160,901271248⟩ E) ⟨174349000448,895231022⟩ E) ⟨174349000640,891232311⟩ (N E ⟨174349000704,889904373⟩ E)))) ⟨174354240948,951374059⟩ (N (N (N (N (N E ⟨174365774784,973130747⟩ E) ⟨174367874032,928009254⟩ E) ⟨174382551216,1006987312⟩ (N (N E ⟨174382551600,997821484⟩ E) ⟨174382555136,918134784⟩ E)) ⟨174390943744,925260241⟩ (N (N (N E ⟨174399328832,1012953193⟩ E) ⟨174399329248,1002993107⟩ E) ⟨174403526656,935999278⟩ (N E ⟨174405622644,963659951⟩ E))) ⟨174416107488,994097904⟩ (N (N (N (N E ⟨174416109568,946799311⟩ E) ⟨174420303872,950412871⟩ E) ⟨174421349044,1030644353⟩ (N (N E ⟨174421349876,1010514313⟩ E) ⟨174432883296,1043534876⟩ E)) ⟨174434982896,986803866⟩ (N (N (N E ⟨174441275392,968582237⟩ E) ⟨174449660528,1058984436⟩ E) ⟨174449660944,1048574696⟩ (N E ⟨174449661376,1037899657⟩ E))))) ⟨174449661952,1023876774⟩ (N (N (N (N (N (N E ⟨174470632882,1057825527⟩ E) ⟨174470635520,994303521⟩ E) ⟨174483214608,1100208595⟩ (N (N E ⟨174483215040,1088956889⟩ E) ⟨174483215456,1078257588⟩ E)) ⟨174483215872,1067689418⟩ (N (N (N E ⟨174483216416,1054064168⟩ E) ⟨174483216448,1053269473⟩ E) ⟨174483217212,1034516658⟩ (N E ⟨174483217280,1032867868⟩ E))) ⟨174483218016,1015230677⟩ (N (N (N (N E ⟨174483218112,1012958027⟩ E) ⟨174483218432,1005428326⟩ E) ⟨174487410050,1074840674⟩ (N (N E ⟨174487411584,1036691220⟩ E) ⟨174487412736,1009150106⟩ E)) ⟨174499994380,1051059309⟩ (N (N (N E ⟨174504187027,1096960024⟩ E) ⟨174506285300,1070253477⟩ E) ⟨174516769872,1110812531⟩ (N E ⟨174516770304,1099508149⟩ E)))) ⟨174516770880,1084658468⟩ (N (N (N (N (N E ⟨174516771648,1065246820⟩ E) ⟨174533546688,1137811049⟩ E) ⟨174550323920,1153890654⟩ (N (N E ⟨174550324336,1142554434⟩ E) ⟨174550324768,1130929220⟩ E)) ⟨174550325312,1116499651⟩ (N (N (N E ⟨174550325344,1115658043⟩ E) ⟨174550326112,1095695338⟩ E) ⟨174550326464,1086695096⟩ (N E ⟨174550327232,1067376886⟩ E))) ⟨174550327296,1065786491⟩ (N (N (N (N E ⟨174554521600,1069616173⟩ E) ⟨174573394996,1111895828⟩ E) ⟨174583880576,1126540471⟩ (N E ⟨174583881728,1096612389⟩ E)) ⟨174592270336,1104386127⟩ (N (N (N E ⟨174596464640,1108283078⟩ E) ⟨174600656032,1190941271⟩ E) ⟨174602755952,1117886207⟩ (N E ⟨174604853248,1116097138⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab9 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨174621627938,1200927010⟩ E) ⟨174634212300,1172778186⟩ E) ⟨174634213376,1143657861⟩ (N (N E ⟨174650988288,1223933552⟩ E) ⟨174650990592,1159554438⟩ E)) ⟨174671962112,1179575939⟩ (N (N (N E ⟨174676156416,1183600328⟩ E) ⟨174684545024,1191669187⟩ E) ⟨174688737634,1244084667⟩ (N E ⟨174688738896,1207822375⟩ E))) ⟨174688739328,1195713652⟩ (N (N (N (N E ⟨174701319424,1290480074⟩ E) ⟨174701320558,1256395910⟩ E) ⟨174705513827,1291798181⟩ (N (N E ⟨174734873472,1337599979⟩ E) ⟨174743265280,1248899872⟩ E)) ⟨174751650336,1366815887⟩ (N (N (N E ⟨174751650752,1353373821⟩ E) ⟨174751651552,1327985083⟩ E) ⟨174751651584,1326981976⟩ (N E ⟨174751652128,1310073213⟩ E)))) ⟨174751653888,1257182497⟩ (N (N (N (N (N E ⟨174771574162,1359569403⟩ E) ⟨174771574578,1346268072⟩ E) ⟨174785204784,1402591460⟩ (N (N E ⟨174793596928,1298995399⟩ E) ⟨174806179840,1311669048⟩ E)) ⟨174818760480,1396878347⟩ (N (N (N E ⟨174818760608,1392665325⟩ E) ⟨174818761824,1353423455⟩ E) ⟨174818762752,1324402519⟩ (N E ⟨174835536864,1443018170⟩ E))) ⟨174837636400,1366388081⟩ (N (N (N (N E ⟨174837637120,1343614804⟩ E) ⟨174852314944,1431918568⟩ E) ⟨174852315520,1412615711⟩ (N (N E ⟨174852316288,1387381887⟩ E) ⟨174852317120,1360678006⟩ E)) ⟨174864900096,1371603053⟩ (N (N (N E ⟨174873287218,1429101938⟩ E) ⟨174877483008,1384615138⟩ E) ⟨174885868560,1497086952⟩ (N E ⟨174885871616,1393322965⟩ E))))) ⟨174890065744,1403431755⟩ (N (N (N (N (N (N E ⟨174902646208,1500452387⟩ E) ⟨174919423072,1531887832⟩ E) ⟨174919423488,1516873562⟩ (N (N E ⟨174919425216,1456441535⟩ E) ⟨174932008960,1441688754⟩ E)) ⟨174938298256,1523572103⟩ (N (N (N E ⟨174940396146,1499629590⟩ E) ⟨174940396914,1472879133⟩ E) ⟨174940397568,1450568379⟩ (N E ⟨174952980480,1463937278⟩ E))) ⟨174969755136,1573618499⟩ (N (N (N (N E ⟨174986531952,1607912761⟩ E) ⟨174989678610,1576506677⟩ E) ⟨174999117824,1513463656⟩ (N (N E ⟨175003309600,1610788659⟩ E) ⟨175003312128,1518005516⟩ E)) ⟨175007506432,1522553945⟩ (N (N (N E ⟨175011700736,1527108941⟩ E) ⟨175020087840,1591260121⟩ E) ⟨175020087872,1590064029⟩ (N E ⟨175020088704,1559356504⟩ E)))) ⟨175020088960,1550057503⟩ (N (N (N (N (N E ⟨175020089344,1536238631⟩ E) ⟨175053641728,1650356323⟩ E) ⟨175053642304,1628133845⟩ (N (N E ⟨175062032384,1582280537⟩ E) ⟨175070420992,1591567510⟩ E)) ⟨175074614034,1644020903⟩ (N (N (N E ⟨175078808384,1647041605⟩ E) ⟨175083003904,1605547021⟩ E) ⟨175087196224,1686838787⟩ (N E ⟨175087198208,1610219932⟩ E))) ⟨175089294016,1664048009⟩ (N (N (N (N E ⟨175106071280,1681521542⟩ E) ⟨175120750656,1726247115⟩ E) ⟨175120752000,1672635536⟩ (N E ⟨175137529856,1666803952⟩ E)) ⟨175141723730,1688410322⟩ (N (N (N E ⟨175141724160,1671561655⟩ E) ⟨175154305120,1764761232⟩ E) ⟨175154307072,1685873815⟩ (N E ⟨175175277968,1734938876⟩ E)))))) ⟨175200444416,1738852136⟩ (N (N (N (N (N (N (N E ⟨175202541228,1755138500⟩ E) ⟨175207782194,1842191082⟩ E) ⟨175221415936,1763192653⟩ (N (N E ⟨175229804544,1772974185⟩ E) ⟨175242387456,1787694995⟩ E)) ⟨175254968640,1876891573⟩ (N (N (N E ⟨175254970368,1802473973⟩ E) ⟨175257067200,1818460090⟩ E) ⟨175271747584,1822269667⟩ (N E ⟨175288524800,1842168548⟩ E))) ⟨175292718656,1866562487⟩ (N (N (N (N E ⟨175322078016,1936550252⟩ E) ⟨175322079232,1882275352⟩ E) ⟨175334662144,1897421469⟩ (N (N E ⟨175338856448,1902483014⟩ E) ⟨175355632480,1976752112⟩ E)) ⟨175355632512,1975269053⟩ (N (N (N E ⟨175355633344,1937193231⟩ E) ⟨175355633600,1925662582⟩ E) ⟨175355633664,1922793340⟩ (N E ⟨175372410880,1943206196⟩ E)))) ⟨175389188096,1963721449⟩ (N (N (N (N (N E ⟨175405965312,1984338961⟩ E) ⟨175422741376,2059779446⟩ E) ⟨175422742176,2021583900⟩ (N (N E ⟨175422742528,2005058599⟩ E) ⟨175426936832,2010254450⟩ E)) ⟨175456296960,2046803700⟩ (N (N (N E ⟨175475171328,2070464177⟩ E) ⟨175485657088,2083664436⟩ E) ⟨175489851392,2088955639⟩ (N E ⟨175540183040,2152943896⟩ E))) ⟨175556960124,2181174558⟩ (N (N (N (N E ⟨175556960256,2174475502⟩ E) ⟨175561154560,2179874167⟩ E) ⟨175569542920,2203391833⟩ (N (N E ⟨175569543168,2190690399⟩ E) ⟨175624069120,2261608976⟩ E)) ⟨175640846336,2283643367⟩ (N (N (N E ⟨175657622656,2354537999⟩ E) ⟨175674400768,2328012323⟩ E) ⟨175678595072,2333586536⟩ (N E ⟨175691177984,2350346583⟩ E))))) ⟨175695372288,2355945725⟩ (N (N (N (N (N (N E ⟨175710052352,2375591733⟩ E) ⟨175724732352,2398888254⟩ E) ⟨175724732416,2395313904⟩ (N (N E ⟨175745703282,2460897316⟩ E) ⟨175758286848,2440678588⟩ E)) ⟨175808618496,2509467912⟩ (N (N (N E ⟨175812812800,2515240450⟩ E) ⟨175825395712,2532594994⟩ E) ⟨175879921664,2608436646⟩ (N E ⟨175884115968,2614313502⟩ E))) ⟨175892504576,2626085552⟩ (N (N (N (N E ⟨175909281792,2649702926⟩ E) ⟨175926057500,2769428566⟩ E) ⟨175926059008,2673417863⟩ (N (N E ⟨175947030528,2703198475⟩ E) ⟨175959613440,2721139749⟩ E)) ⟨176014139392,2799515217⟩ (N (N (N E ⟨176026722304,2817746826⟩ E) ⟨176030916608,2823836078⟩ E) ⟨176056080984,2959052590⟩ (N E ⟨176077053952,2891214590⟩ E)))) ⟨176093831168,2915895760⟩ (N (N (N (N (N E ⟨176127385600,2965544913⟩ E) ⟨176135774208,2978016823⟩ E) ⟨176148357120,2996769313⟩ (N (N E ⟨176160940032,3015575285⟩ E) ⟨176215465984,3097683969⟩ E)) ⟨176223854592,3110404683⟩ (N (N (N E ⟨176228048896,3116773877⟩ E) ⟨176244826112,3142309504⟩ E) ⟨176295157760,3219479764⟩ (N E ⟨176299352064,3225948656⟩ E))) ⟨176347586560,3300759773⟩ (N (N (N (N E ⟨176353878016,3310574428⟩ E) ⟨176362266624,3323680930⟩ E) ⟨176379043840,3349963424⟩ (N E ⟨176395821056,3376338416⟩ E)) ⟨176416792576,3409436929⟩ (N (N (N E ⟨176429375488,3429365103⟩ E) ⟨176488095744,3523045458⟩ E) ⟨176496484352,3536519776⟩ (N E ⟨176563593216,3645132190⟩ E))))))) ⟨176626507776,3748268700⟩ (N (N (N (N (N (N (N (N E ⟨176630702080,3755189350⟩ E) ⟨176681033728,3838672377⟩ E) ⟨176697810944,3866678014⟩ (N (N E ⟨176748142592,3951225841⟩ E) ⟨176764919808,3979584708⟩ E)) ⟨176832028672,4093895715⟩ (N (N (N E ⟨176882360320,4180542169⟩ E) ⟨176890748928,4195058863⟩ E) ⟨177016578048,4415377260⟩ (N E ⟨177167572992,4686019082⟩ E))) ⟨177217904640,4777723307⟩ (N (N (N (N E ⟨177234681856,4808454914⟩ E) ⟨177285013504,4901136959⟩ E) ⟨177301790720,4932192574⟩ (N (N E ⟨177314373632,4955537057⟩ E) ⟨177368899584,5057216511⟩ E)) ⟨177410842624,5136002667⟩ (N (N (N E ⟨177436008448,5183510966⟩ E) ⟨177486340096,5279055973⟩ E) ⟨177515700224,5335113738⟩ (N E ⟨177704443904,5701071046⟩ E)))) ⟨177813495808,5916821880⟩ (N (N (N (N (N E ⟨177817690112,5925181669⟩ E) ⟨177838661632,5967048477⟩ E) ⟨177897381888,6084873485⟩ (N (N E ⟨177972879360,6237642433⟩ E) ⟨177989656576,6271784321⟩ E)) ⟨178086125568,6469443565⟩ (N (N (N E ⟨178107097088,6512712553⟩ E) ⟨178123874304,6547403934⟩ E) ⟨178153234432,6608275905⟩ (N E ⟨178220343296,6748178940⟩ E))) ⟨178304229376,6924535414⟩ (N (N (N (N E ⟨178354561024,7031123470⟩ E) ⟨178383921152,7093564025⟩ E) ⟨178421669888,7174127681⟩ (N (N E ⟨178492973056,7327160686⟩ E) ⟨178555887616,7463105406⟩ E)) ⟨178572664832,7499500159⟩ (N (N (N E ⟨178690105344,7755914000⟩ E) ⟨178761408512,7912973200⟩ E) ⟨178807545856,8015141234⟩ (N E ⟨178870460416,8155133328⟩ E))))) ⟨178979512320,8399577859⟩ (N (N (N (N (N (N E ⟨179029843968,8513144844⟩ E) ⟨179059204096,8579604990⟩ E) ⟨179105341440,8684354096⟩ (N (N E ⟨179298279424,9126382320⟩ E) ⟨179445080064,9466795949⟩ E)) ⟨180304912384,11519220240⟩ (N (N (N E ⟨180388798468,11722665085⟩ E) ⟨180388798508,11711748847⟩ E) ⟨180388798512,11710657922⟩ (N E ⟨180388798528,11706295495⟩ E))) ⟨180388798576,11693220399⟩ (N (N (N (N E ⟨180388798592,11688866092⟩ E) ⟨180388798642,11675271945⟩ E) ⟨180388798656,11671469127⟩ (N (N E ⟨180388798672,11667124946⟩ E) ⟨180388798704,11658442647⟩ E)) ⟨180388798708,11657357928⟩ (N (N (N E ⟨180388798720,11654104527⟩ E) ⟨180388798724,11653020313⟩ E) ⟨180388798760,11643268056⟩ (N E ⟨180388798768,11641102274⟩ E)))) ⟨180388798784,11636772221⟩ (N (N (N (N (N E ⟨180388798832,11623794141⟩ E) ⟨180388798848,11619472136⟩ E) ⟨180388798860,11616231951⟩ (N (N E ⟨180388798866,11614612283⟩ E) ⟨180388798896,11606518174⟩ E)) ⟨180388798900,11605439493⟩ (N (N (N E ⟨180388798912,11602204200⟩ E) ⟨180388798964,11588197625⟩ E) ⟨180388798976,11584968342⟩ (N E ⟨180388799016,11574212188⟩ E))) ⟨180388799040,11567764490⟩ (N (N (N (N E ⟨180388799052,11564542325⟩ E) ⟨180388799088,11554882562⟩ E) ⟨180388799092,11553809878⟩ (N E ⟨180388799104,11550592573⟩ E)) ⟨180388799144,11539876309⟩ (N (N (N E ⟨180388799152,11537734549⟩ E) ⟨180388799156,11536663855⟩ E) ⟨180388799168,11533452519⟩ (N E ⟨180388799228,11517412594⟩ E)))))) ⟨180388799232,11516344258⟩ (N (N (N (N (N (N (N E ⟨180388799284,11502467156⟩ E) ⟨180388799328,11490741322⟩ E) ⟨180388799360,11482222831⟩ (N (N E ⟨180388799468,11453531158⟩ E) ⟨180388799488,11448227727⟩ E)) ⟨180388799552,11431277372⟩ (N (N (N E ⟨180388799568,11427044687⟩ E) ⟨180388799584,11422813962⟩ E) ⟨180388799616,11414358387⟩ (N E ⟨180388799632,11410133534⟩ E))) ⟨180388799680,11397470704⟩ (N (N (N (N E ⟨180388799704,11391145878⟩ E) ⟨180388799744,11380614252⟩ E) ⟨180388799784,11370094798⟩ (N (N E ⟨180388799804,11364839631⟩ E) ⟨180388799808,11363788962⟩ E)) ⟨180388799852,11352239616⟩ (N (N (N E ⟨180388799880,11344897674⟩ E) ⟨180388799928,11332325296⟩ E) ⟨180388799984,11317679533⟩ (N E ⟨180388800000,11313499377⟩ E)))) ⟨180388800040,11303057431⟩ (N (N (N (N (N E ⟨180388800064,11296798048⟩ E) ⟨180388800080,11292627533⟩ E) ⟨180388800112,11284292279⟩ (N (N E ⟨180388800172,11268684402⟩ E) ⟨180388800192,11263487775⟩ E)) ⟨180388800240,11251028094⟩ (N (N (N E ⟨180388800256,11246878697⟩ E) ⟨180388800304,11234441982⟩ E) ⟨180388800320,11230300232⟩ (N E ⟨180388800336,11226160392⟩ E))) ⟨180388800368,11217886434⟩ (N (N (N (N E ⟨180388800372,11216852725⟩ E) ⟨180388800384,11213752314⟩ E) ⟨180388800448,11197234876⟩ (N E ⟨180388800496,11184866758⟩ E)) ⟨180388800512,11180747848⟩ (N (N (N E ⟨180388800524,11177659911⟩ E) ⟨180388800564,11167374485⟩ E) ⟨180388800576,11164291166⟩ (N E ⟨180388800624,11151968527⟩ E))))) ⟨180388800628,11150942408⟩ (N (N (N (N (N (N E ⟨180388800640,11147864760⟩ E) ⟨180388800704,11131468566⟩ E) ⟨180388800752,11119191205⟩ (N (N E ⟨180388800768,11115102515⟩ E) ⟨180388800820,11101827249⟩ E)) ⟨180388800880,11086534260⟩ (N (N (N E ⟨180388800892,11083478824⟩ E) ⟨180388800896,11082460580⟩ E) ⟨180388800960,11066184563⟩ (N E ⟨180388801004,11055012137⟩ E))) ⟨180388801012,11052982302⟩ (N (N (N (N E ⟨180388801024,11049938424⟩ E) ⟨180388801072,11037773389⟩ E) ⟨180388801080,11035747512⟩ (N (N E ⟨180388801132,11022590636⟩ E) ⟨180388801140,11020568242⟩ E)) ⟨180388801152,11017535522⟩ (N (N (N E ⟨180388801196,11006424471⟩ E) ⟨180388801204,11004405786⟩ E) ⟨180388801212,11002387564⟩ (N E ⟨180388801216,11001378626⟩ E)))) ⟨180388801280,10985251347⟩ (N (N (N (N (N E ⟨180388801324,10974180989⟩ E) ⟨180388801332,10972169696⟩ E) ⟨180388801344,10969153620⟩ (N (N E ⟨180388801392,10957099678⟩ E) ⟨180388801408,10953085379⟩ E)) ⟨180388801472,10937046560⟩ (N (N (N E ⟨180388801516,10926036905⟩ E) ⟨180388801536,10921037098⟩ E) ⟨180388801648,10893090986⟩ (N E ⟨180388801792,10857291534⟩ E))) ⟨180388801800,10855306993⟩ (N (N (N (N E ⟨180388801840,10845391085⟩ E) ⟨180388801856,10841427894⟩ E) ⟨180388801872,10837466513⟩ (N E ⟨180388801904,10829549181⟩ E)) ⟨180388801920,10825593226⟩ (N (N (N E ⟨180388802048,10794010555⟩ E) ⟨180388802096,10782196763⟩ E) ⟨180388802176,10762543015⟩ (N E ⟨180388802292,10734124582⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab10 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨180388802384,10711652519⟩ E) ⟨180388802400,10707750341⟩ E) ⟨180388802432,10699951317⟩ (N (N E ⟨180388802484,10687293045⟩ E) ⟨180388802488,10686320108⟩ E)) ⟨180388802496,10684374565⟩ (N (N (N E ⟨180388802536,10674653494⟩ E) ⟨180388802560,10668826159⟩ E) ⟨180388802624,10653306036⟩ (N E ⟨180388802656,10645556561⟩ E))) ⟨180388802668,10642652325⟩ (N (N (N (N E ⟨180388802672,10641684467⟩ E) ⟨180388802688,10637814134⟩ E) ⟨180388802816,10606914747⟩ (N (N E ⟨180388802876,10592469296⟩ E) ⟨180388802880,10591507141⟩ E)) ⟨180388802920,10581891597⟩ (N (N (N E ⟨180388802924,10580930643⟩ E) ⟨180388802928,10579969798⟩ E) ⟨180388802944,10576127510⟩ (N E ⟨180388802988,10565570210⟩ E)))) ⟨180388803008,10560775794⟩ (N (N (N (N (N E ⟨180388803056,10549280290⟩ E) ⟨180388803072,10545451932⟩ E) ⟨180388803132,10531111056⟩ (N (N E ⟨180388803180,10519655909⟩ E) ⟨180388803200,10514887529⟩ E)) ⟨180388803208,10512980935⟩ (N (N (N E ⟨180388803244,10504406605⟩ E) ⟨180388803312,10488234494⟩ E) ⟨180388803328,10484433817⟩ (N E ⟨180388803376,10473042115⟩ E))) ⟨180388803456,10454090316⟩ (N (N (N (N E ⟨180388803500,10443685104⟩ E) ⟨180388803520,10438959744⟩ E) ⟨180388803568,10427629782⟩ (N (N E ⟨180388803584,10423856546⟩ E) ⟨180388803640,10410663655⟩ E)) ⟨180388803696,10397491637⟩ (N (N (N E ⟨180388803712,10393732032⟩ E) ⟨180388803824,10367462333⟩ E) ⟨180388803952,10337541399⟩ (N E ⟨180388803956,10336608111⟩ E))))) ⟨180388803964,10334741851⟩ (N (N (N (N (N (N E ⟨180388804076,10308658394⟩ E) ⟨180388804080,10307728366⟩ E) ⟨180388804096,10304009300⟩ (N (N E ⟨180388804148,10291933918⟩ E) ⟨180388804192,10281730106⟩ E)) ⟨180388804332,10249347478⟩ (N (N (N E ⟨180388804352,10244731805⟩ E) ⟨180388804396,10234586470⟩ E) ⟨180388804544,10200553317⟩ (N E ⟨180388804608,10185880112⟩ E))) ⟨180388804652,10175807591⟩ (N (N (N (N E ⟨180388804736,10156612794⟩ E) ⟨180388804992,10098392940⟩ E) ⟨180388805120,10069439501⟩ (N (N E ⟨180388805128,10067633360⟩ E) ⟨180388805168,10058608728⟩ E)) ⟨180388805296,10029797800⟩ (N (N (N E ⟨180388805352,10017225470⟩ E) ⟨180388805376,10011843362⟩ E) ⟨180388805504,9983199771⟩ (N E ⟨180388805560,9970700425⟩ E)))) ⟨180388805608,9960002271⟩ (N (N (N (N (N E ⟨180388805632,9954658577⟩ E) ⟨180388805728,9933319616⟩ E) ⟨180388805736,9931543952⟩ (N (N E ⟨180388805740,9930656269⟩ E) ⟨180388805760,9926219341⟩ E)) ⟨180388805816,9913809125⟩ (N (N (N E ⟨180388805864,9903187235⟩ E) ⟨180388805888,9897881626⟩ E) ⟨180388805992,9874931686⟩ (N E ⟨180388805996,9874050325⟩ E))) ⟨180388806016,9869644998⟩ (N (N (N (N E ⟨180388806060,9859961925⟩ E) ⟨180388806208,9827478646⟩ E) ⟨180388806248,9818722360⟩ (N E ⟨180388806272,9813473271⟩ E)) ⟨180388806316,9803859051⟩ (N (N (N E ⟨180388806384,9789023866⟩ E) ⟨180388806528,9757700727⟩ E) ⟨180388806576,9747287538⟩ (N E ⟨180388806640,9733424893⟩ E)))))) ⟨180388806656,9729963084⟩ (N (N (N (N (N (N (N E ⟨180397195264,9746965609⟩ E) ⟨181168947200,11326866252⟩ E) ⟨181571600384,12157431795⟩ (N (N E ⟨181689039440,12809255123⟩ E) ⟨184012685312,17009071115⟩ E)) ⟨184499224576,17886733706⟩ (N (N (N E ⟨184868323328,18521822193⟩ E) ⟨186160168960,20491807052⟩ E) ⟨187452014592,21984511907⟩ (N E ⟨187854667776,22337328602⟩ E))) ⟨188659974144,22868790503⟩ (N (N (N (N E ⟨188978741296,22987588925⟩ E) ⟨188978741304,22983326253⟩ E) ⟨188978741312,22979037516⟩ (N (N E ⟨188978741488,22878121236⟩ E) ⟨188978741504,22868327409⟩ E)) ⟨188978741632,22786289547⟩ (N (N (N E ⟨188978741744,22709166408⟩ E) ⟨188978741856,22627108834⟩ E) ⟨188978742000,22514435475⟩ (N E ⟨188978742016,22501422485⟩ E)))) ⟨188978742272,22279969817⟩ (N (N (N (N (N E ⟨188978742400,22160024998⟩ E) ⟨188978743016,21500116735⟩ E) ⟨188978743040,21471725482⟩ (N (N E ⟨188978743168,21317030601⟩ E) ⟨188978743272,21187331923⟩ E)) ⟨188978743296,21156897754⟩ (N (N (N E ⟨188978743400,21022860560⟩ E) ⟨188978743424,20991435527⟩ E) ⟨188978743480,20917398287⟩ (N E ⟨188978743552,20820755150⟩ E))) ⟨188978743656,20678313545⟩ (N (N (N (N E ⟨188978743680,20644970417⟩ E) ⟨188978743784,20498467029⟩ E) ⟨188978743872,20371977659⟩ (N (N E ⟨188978743936,20278555381⟩ E) ⟨188978744168,19930060922⟩ E)) ⟨188978744304,19718814380⟩ (N (N (N E ⟨188978744320,19693633166⟩ E) ⟨188978744560,19307857762⟩ E) ⟨188978744576,19281613785⟩ (N E ⟨188978744632,19189255598⟩ E))))) ⟨188978744704,19069370752⟩ (N (N (N (N (N (N E ⟨188978744832,18853148956⟩ E) ⟨188978744960,18633083148⟩ E) ⟨188978745216,18181966454⟩ (N (N E ⟨188978745408,17834563394⟩ E) ⟨188978745568,17539508005⟩ E)) ⟨188978745728,17239701561⟩ (N (N (N E ⟨188978745824,17057654073⟩ E) ⟨188978745856,16996624543⟩ E) ⟨188978746080,16564793006⟩ (N E ⟨188978746336,16062093940⟩ E))) ⟨188978746344,16046238927⟩ (N (N (N (N E ⟨188978746368,15998623519⟩ E) ⟨188978746496,15743435378⟩ E) ⟨188978746728,15275966012⟩ (N (N E ⟨188978746800,15129706508⟩ E) ⟨188978746880,14966594275⟩ E)) ⟨188978747112,14490317855⟩ (N (N (N E ⟨188978747392,13910072854⟩ E) ⟨188978747496,13693333712⟩ E) ⟨188978747648,13375620595⟩ (N E ⟨188978747712,13241564962⟩ E)))) ⟨188978748000,12636852777⟩ (N (N (N (N (N E ⟨188978748032,12569561193⟩ E) ⟨188978748080,12468602409⟩ E) ⟨188978748160,12300299849⟩ (N (N E ⟨188978748512,11560055244⟩ E) ⟨188978748848,10855942113⟩ E)) ⟨188978748928,10688945415⟩ (N (N (N E ⟨188978749440,9629227507⟩ E) ⟨189515620352,9730938999⟩ E) ⟨190631305216,9943520182⟩ (N E ⟨191075901440,10028506045⟩ E))) ⟨191562440704,10121569207⟩ (N (N (N (N E ⟨191923150848,10190553534⟩ E) ⟨193173053440,10428970411⟩ E) ⟨193483431936,10487903100⟩ (N E ⟨194422956032,10665250754⟩ E)) ⟨194565562368,10692004442⟩ (N (N (N E ⟨194699780096,10717138745⟩ E) ⟨194783666176,10732824357⟩ E) ⟨195102433280,10792257141⟩ (N E ⟨195186319360,10807849829⟩ E))))))) ⟨195270205440,10823421840⟩ (N (N (N (N (N (N (N (N E ⟨195370868736,10842080322⟩ E) ⟨195412811776,10849845525⟩ E) ⟨195505086464,10866909622⟩ (N (N E ⟨195756744704,10913308617⟩ E) ⟨196394278912,11029869377⟩ E)) ⟨196796932096,11102692862⟩ (N (N (N E ⟨196847263744,11111749530⟩ E) ⟨197191196672,11173348504⟩ E) ⟨197379940352,11206932078⟩ (N E ⟨197514158080,11230715130⟩ E))) ⟨197568684264,10703590170⟩ (N (N (N (N E ⟨197568684648,9827983555⟩ E) ⟨197568684720,9665847445⟩ E) ⟨197568685304,8378970143⟩ (N (N E ⟨197568685376,8224162898⟩ E) ⟨197568685568,7815921159⟩ E)) ⟨197568686080,6762594557⟩ (N (N (N E ⟨197568686848,5292329246⟩ E) ⟨197568687072,4891156123⟩ E) ⟨197568687128,4792942938⟩ (N E ⟨197568687472,4208503414⟩ E)))) ⟨197568687584,4025402962⟩ (N (N (N (N (N E ⟨197568687672,3884075859⟩ E) ⟨197568687852,3602065857⟩ E) ⟨197568687900,3528487292⟩ (N (N E ⟨197568688496,2673581588⟩ E) ⟨197568688792,2290591866⟩ E)) ⟨197568689408,1585530720⟩ (N (N (N E ⟨197568689416,1577206465⟩ E) ⟨197568689500,1491105504⟩ E) ⟨197568689632,1360628775⟩ (N E ⟨197568689864,1145674799⟩ E))) ⟨197568690144,910796146⟩ (N (N (N (N E ⟨197568690176,885669736⟩ E) ⟨197568690216,854758010⟩ E) ⟨197568690312,782821429⟩ (N (N E ⟨197568690396,722486608⟩ E) ⟨197568690460,678153243⟩ E)) ⟨197568690508,645832146⟩ (N (N (N E ⟨197568690536,627345943⟩ E) ⟨197568690584,596285838⟩ E) ⟨197568690800,466370894⟩ (N E ⟨197568691168,282126683⟩ E))))) ⟨197568691340,211987719⟩ (N (N (N (N (N (N E ⟨197568691464,167705408⟩ E) ⟨197568691528,146902746⟩ E) ⟨197568691984,38832875⟩ (N (N E ⟨197568692060,27610655⟩ E) ⟨197568692128,19198372⟩ E)) ⟨197568692224,9929527⟩ (N (N (N E ⟨197598051608,162627172⟩ E) ⟨197686129068,2600124669⟩ E) ⟨197686130732,854605634⟩ (N E ⟨197845516288,10431959⟩ E))) ⟨197862293504,10462381⟩ (N (N (N (N E ⟨197979734016,10675179⟩ E) ⟨198000703896,604638393⟩ E) ⟨198084588264,2216727955⟩ (N (N E ⟨198084589928,637638845⟩ E) ⟨198139115868,646694258⟩ E)) ⟨198252362312,500738748⟩ (N (N (N E ⟨198273335196,21474097⟩ E) ⟨198348832644,24641540⟩ E) ⟨198386580104,465995707⟩ (N E ⟨198386581504,11409088⟩ E)))) ⟨198759873516,290664070⟩ (N (N (N (N (N E ⟨198977974268,3282502877⟩ E) ⟨198977977016,447917952⟩ E) ⟨199124778312,158980535⟩ (N (N E ⟨199288355380,529364540⟩ E) ⟨199326105032,120872767⟩ E)) ⟨199342882200,135158220⟩ (N (N (N E ⟨199430961196,895633242⟩ E) ⟨199678425432,678441207⟩ E) ⟨199678427136,13665979⟩ (N E ⟨199749728766,570035870⟩ E))) ⟨199829420392,670112585⟩ (N (N (N (N E ⟨199883947996,17720917⟩ E) ⟨199997193002,399554016⟩ E) ⟨199997193066,366485944⟩ (N E ⟨199997194240,14195591⟩ E)) ⟨200110440448,14380346⟩ (N (N (N E ⟨200198520832,14522728⟩ E) ⟨200567618664,254399069⟩ E) ⟨200815082836,166375311⟩ (N E ⟨200869609098,78055014⟩ E)))))) ⟨200898968932,161481021⟩ (N (N (N (N (N (N (N E ⟨200936717962,78308182⟩ E) ⟨200953495130,89925937⟩ E) ⟨201190473564,37795360⟩ (N (N E ⟨201385506996,827990647⟩ E) ⟨201437936936,185550021⟩ E)) ⟨201437937664,16383451⟩ (N (N (N E ⟨201490366464,16455500⟩ E) ⟨201574252520,19223037⟩ E) ⟨201859463864,484592607⟩ (N E ⟨201939155974,309062020⟩ E))) ⟨201939156710,61348390⟩ (N (N (N (N E ⟨201939156806,43157808⟩ E) ⟨202039820288,17173262⟩ E) ⟨202312449418,156223418⟩ (N (N E ⟨202343907328,17539522⟩ E) ⟨202360684544,17559055⟩ E)) ⟨202559913654,73392287⟩ (N (N (N E ⟨202627022550,66488771⟩ E) ⟨202643799718,77287526⟩ E) ⟨202811572038,44899262⟩ (N E ⟨202845126470,44959736⟩ E)))) ⟨203182768128,18424759⟩ (N (N (N (N (N E ⟨203249876992,18487203⟩ E) ⟨203346345984,18574707⟩ E) ⟨203751096320,18912217⟩ (N (N E ⟨206158626840,17101590⟩ E) ⟨206158626871,13845390⟩ E)) ⟨206158626904,10757353⟩ (N (N (N E ⟨206158626944,7536840⟩ E) ⟨206158626952,6961417⟩ E) ⟨206158626956,6682287⟩ (N E ⟨206158626958,6544867⟩ E))) ⟨206158626976,5372431⟩ (N (N (N (N E ⟨206158626980,5127615⟩ E) ⟨206158627016,3181467⟩ E) ⟨206158627048,1839977⟩ (N E ⟨206158627084,767374⟩ E)) ⟨206158627088,676712⟩ (N (N (N E ⟨206158627124,117204⟩ E) ⟨206158627140,16628⟩ E) ⟨206158627144,5716⟩ (N E ⟨206158627148,495⟩ E))))) ⟨206517242069,11868⟩ (N (N (N (N (N (N E ⟨206517242085,11865⟩ E) ⟨206517242501,11766⟩ E) ⟨206517242917,11668⟩ (N (N E ⟨206517243333,11571⟩ E) ⟨206517244020,11413⟩ E)) ⟨206517244852,11226⟩ (N (N (N E ⟨206517245588,11063⟩ E) ⟨206517245684,11042⟩ E) ⟨206517246452,10876⟩ (N E ⟨206517246516,10862⟩ E))) ⟨206518291062,14765⟩ (N (N (N (N E ⟨206518291862,14530⟩ E) ⟨206518291894,14520⟩ E) ⟨206527730268,54735⟩ (N (N E ⟨206527731456,53460⟩ E) ⟨206527731932,52960⟩ E)) ⟨206527733760,51091⟩ (N (N (N E ⟨206531928064,75826⟩ E) ⟨206534021188,97473⟩ E) ⟨206534022788,94423⟩ (N E ⟨206548703536,231238⟩ E)))) ⟨206548705280,223451⟩ (N (N (N (N (N E ⟨206550796533,278106⟩ E) ⟨206550797333,273670⟩ E) ⟨206550797765,271311⟩ (N (N E ⟨206550798452,267613⟩ E) ⟨206550799220,263552⟩ E)) ⟨206550799540,261883⟩ (N (N (N E ⟨206552899444,273280⟩ E) ⟨206552899584,272532⟩ E) ⟨206554992988,321850⟩ (N E ⟨206554995448,306549⟩ E))) ⟨206561287616,389680⟩ (N (N (N (N E ⟨206561288192,385309⟩ E) ⟨206565477666,494045⟩ E) ⟨206565478434,486518⟩ (N E ⟨206565479298,478220⟩ E)) ⟨206565480640,465679⟩ (N (N (N E ⟨206566525556,519506⟩ E) ⟨206567573765,542450⟩ E) ⟨206567574149,538275⟩ (N E ⟨206582254866,828274⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab11 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨206582256466,802251⟩ E) ⟨206582257808,781208⟩ E) ⟨206584351381,887338⟩ (N (N E ⟨206584351797,879958⟩ E) ⟨206584352229,872376⟩ E)) ⟨206584352773,862944⟩ (N (N (N E ⟨206584352916,860485⟩ E) ⟨206584353684,847432⟩ E) ⟨206584354804,828836⟩ (N E ⟨206584355380,819471⟩ E))) ⟨206585400918,894649⟩ (N (N (N (N E ⟨206603231232,1241610⟩ E) ⟨206615814144,1593589⟩ E) ⟨206616856884,1824384⟩ (N (N E ⟨206616857300,1809185⟩ E) ⟨206616857716,1794144⟩ E)) ⟨206620003975,1879798⟩ (N (N (N E ⟨206620008448,1720673⟩ E) ⟨206628397056,1989481⟩ E) ⟨206632586658,2338988⟩ (N E ⟨206632587490,2300435⟩ E)))) ⟨206634683812,2418671⟩ (N (N (N (N (N E ⟨206636785664,2277812⟩ E) ⟨206640979968,2429300⟩ E) ⟨206650411332,3129260⟩ (N (N E ⟨206650411716,3105187⟩ E) ⟨206651462277,3028672⟩ E)) ⟨206652508886,3196550⟩ (N (N (N E ⟨206655658872,3066944⟩ E) ⟨206661947968,3494398⟩ E) ⟨206661948544,3454630⟩ (N E ⟨206666140803,3798000⟩ E))) ⟨206666141090,3776228⟩ (N (N (N (N E ⟨206666141858,3718728⟩ E) ⟨206667188948,3882166⟩ E) ⟨206667189364,3849890⟩ (N (N E ⟨206669286966,3916940⟩ E) ⟨206669286998,3914434⟩ E)) ⟨206678728704,4012450⟩ (N (N (N E ⟨206682918072,4645226⟩ E) ⟨206682918648,4591989⟩ E) ⟨206682919218,4540055⟩ (N E ⟨206682920082,4462725⟩ E))))) ⟨206685016149,4670511⟩ (N (N (N (N (N (N E ⟨206686063750,4819262⟩ E) ⟨206686064166,4779283⟩ E) ⟨206687113430,4769955⟩ (N (N E ⟨206687113462,4766913⟩ E) ⟨206687113879,4727497⟩ E)) ⟨206687114294,4688673⟩ (N (N (N E ⟨206687115958,4536951⟩ E) ⟨206687117300,4419038⟩ E) ⟨206687117312,4418001⟩ (N E ⟨206695500448,5398003⟩ E))) ⟨206695501312,5305291⟩ (N (N (N (N E ⟨206695502464,5184750⟩ E) ⟨206695503040,5125764⟩ E) ⟨206695505536,4879645⟩ (N (N E ⟨206695505920,4843103⟩ E) ⟨206703890630,5710822⟩ E)) ⟨206703894404,5300602⟩ (N (N (N E ⟨206712283136,5751973⟩ E) ⟨206715424338,6486464⟩ E) ⟨206715424370,6482315⟩ (N E ⟨206716474842,6305748⟩ E)))) ⟨206716475664,6204110⟩ (N (N (N (N (N E ⟨206716476184,6140871⟩ E) ⟨206716477200,6019619⟩ E) ⟨206716477440,5991415⟩ (N (N E ⟨206718571892,6446696⟩ E) ⟨206720667894,6728216⟩ E)) ⟨206720668694,6621990⟩ (N (N (N E ⟨206729055376,7436819⟩ E) ⟨206729055808,7372768⟩ E) ⟨206729057472,7132405⟩ (N E ⟨206729058240,7024775⟩ E))) ⟨206736395894,7863668⟩ (N (N (N (N E ⟨206736396022,7843573⟩ E) ⟨206741638898,8209646⟩ E) ⟨206745832192,8681915⟩ (N E ⟨206745837568,7804477⟩ E)) ⟨206750031872,8083058⟩ (N (N (N E ⟨206751075124,9060675⟩ E) ⟨206752123685,9142013⟩ E) ⟨206752127092,8542402⟩ (N E ⟨206752127924,8403510⟩ E)))))) ⟨206754222807,8941248⟩ (N (N (N (N (N (N (N E ⟨206754223478,8822938⟩ E) ⟨206754226164,8368497⟩ E) ⟨206754226176,8366533⟩ (N (N E ⟨206762609424,9950990⟩ E) ⟨206762609840,9868285⟩ E)) ⟨206762610272,9783305⟩ (N (N (N E ⟨206762610352,9767669⟩ E) ⟨206762610400,9758302⟩ E) ⟨206762611936,9464405⟩ (N E ⟨206762613536,9169936⟩ E))) ⟨206762614400,9015683⟩ (N (N (N (N E ⟨206762614784,8948168⟩ E) ⟨206766807424,9553447⟩ E) ⟨206766808960,9269510⟩ (N (N E ⟨206766809088,9246328⟩ E) ⟨206768900917,10442633⟩ E)) ⟨206768901333,10355857⟩ (N (N (N E ⟨206770999590,10293696⟩ E) ⟨206771000326,10144096⟩ E) ⟨206771003332,9560598⟩ (N E ⟨206779392000,10170188⟩ E)))) ⟨206783584656,10832875⟩ (N (N (N (N (N E ⟨206783586192,10510938⟩ E) ⟨206784629636,11725169⟩ E) ⟨206784630964,11417769⟩ (N (N E ⟨206785677781,11917254⟩ E) ⟨206785678197,11818049⟩ E)) ⟨206785678613,11719875⟩ (N (N (N E ⟨206787777590,11472896⟩ E) ⟨206791970592,12131002⟩ E) ⟨206796163840,12760170⟩ (N E ⟨206796164272,12650051⟩ E))) ⟨206796164704,12541117⟩ (N (N (N (N E ⟨206796166048,12209628⟩ E) ⟨206796166144,12186371⟩ E) ⟨206796166912,12002302⟩ (N (N E ⟨206796166976,11987120⟩ E) ⟨206796169216,11470563⟩ E)) ⟨206801406868,13190849⟩ (N (N (N E ⟨206801407284,13081288⟩ E) ⟨206802454997,13405438⟩ E) ⟨206808752128,12497280⟩ (N E ⟨206817135875,14540021⟩ E))))) ⟨206817136307,14414863⟩ (N (N (N (N (N (N E ⟨206817136978,14223122⟩ E) ⟨206817140736,13206257⟩ E) ⟨206819232613,14861413⟩ (N (N E ⟨206821331318,14602347⟩ E) ⟨206821331350,14593043⟩ E)) ⟨206821331751,14477076⟩ (N (N (N E ⟨206821332182,14353714⟩ E) ⟨206821332438,14281064⟩ E) ⟨206821333750,13915861⟩ (N E ⟨206821333846,13889600⟩ E))) ⟨206821335040,13568097⟩ (N (N (N (N E ⟨206829722464,14642599⟩ E) ⟨206829722560,14614981⟩ E) ⟨206829723392,14378330⟩ (N (N E ⟨206829723648,14306480⟩ E) ⟨206834960900,16522845⟩ E)) ⟨206834961284,16395861⟩ (N (N (N E ⟨206836010261,16369340⟩ E) ⟨206836010564,16270362⟩ E) ⟨206838108518,16217953⟩ (N E ⟨206838109286,15972182⟩ E)))) ⟨206838110118,15711163⟩ (N (N (N (N (N E ⟨206846495968,17454274⟩ E) ⟨206851738516,18120951⟩ E) ⟨206851738532,18115133⟩ (N (N E ⟨206851738932,17970442⟩ E) ⟨206852787077,18237478⟩ E)) ⟨206852788485,17731045⟩ (N (N (N E ⟨206854885782,17896233⟩ E) ⟨206854885788,17894094⟩ E) ⟨206854888480,16966045⟩ (N E ⟨206854889472,16639286⟩ E))) ⟨206863278080,17456117⟩ (N (N (N (N E ⟨206865370720,19311924⟩ E) ⟨206869564709,19894210⟩ E) ⟨206869564725,19887835⟩ (N E ⟨206880053304,19913135⟩ E)) ⟨206880054456,19466461⟩ (N (N (N E ⟨206880055296,19148638⟩ E) ⟨206884244851,21513607⟩ E) ⟨206884245267,21335345⟩ (N E ⟨206884245906,21065106⟩ E))))))) ⟨206884245938,21051686⟩ (N (N (N (N (N (N (N (N E ⟨206884246674,20745950⟩ E) ⟨206884246770,20706482⟩ E) ⟨206884247602,20368326⟩ (N (N E ⟨206886344180,20831811⟩ E) ⟨206886345780,20184533⟩ E)) ⟨206888440679,21338683⟩ (N (N (N E ⟨206888441366,21049859⟩ E) ⟨206888443904,20024334⟩ E) ⟨206896828096,22828242⟩ (N E ⟨206896828672,22567290⟩ E))) ⟨206896829440,22225127⟩ (N (N (N (N E ⟨206896830304,21847912⟩ E) ⟨206896831168,21478667⟩ E) ⟨206896832320,20998393⟩ (N (N E ⟨206896832512,20919657⟩ E) ⟨206901021619,23692488⟩ E)) ⟨206905221120,21834610⟩ (N (N (N E ⟨206913604512,25247846⟩ E) ⟨206917798851,25756077⟩ E) ⟨206917799267,25542201⟩ (N E ⟨206917800370,24985775⟩ E)))) ⟨206917801138,24607277⟩ (N (N (N (N (N E ⟨206917801970,24205292⟩ E) ⟨206917803032,23704035⟩ E) ⟨206919896021,26011699⟩ (N (N E ⟨206919899444,24299405⟩ E) ⟨206919900276,23904688⟩ E)) ⟨206921994135,25776842⟩ (N (N (N E ⟨206921995478,25097044⟩ E) ⟨206930385024,25646808⟩ E) ⟨206933528370,27292301⟩ (N E ⟨206933528402,27274861⟩ E))) ⟨206936673253,28170979⟩ (N (N (N (N E ⟨206936673669,27937090⟩ E) ⟨206936673956,27777143⟩ E) ⟨206936673988,27759380⟩ (N (N E ⟨206936674820,27302493⟩ E) ⟨206938772516,27274477⟩ E)) ⟨206938774180,26391817⟩ (N (N (N E ⟨206938775552,25690771⟩ E) ⟨206942965714,28428729⟩ E) ⟨206947158928,29620404⟩ (N E ⟨206947159360,29364965⟩ E))))) ⟨206947160632,28628666⟩ (N (N (N (N (N (N E ⟨206951356722,28165184⟩ E) ⟨206951357554,27707668⟩ E) ⟨206953450101,30651276⟩ (N (N E ⟨206953450117,30641421⟩ E) ⟨206953450533,30386573⟩ E)) ⟨206953450949,30134369⟩ (N (N (N E ⟨206953451156,30009849⟩ E) ⟨206953451924,29553445⟩ E) ⟨206953452756,29068758⟩ (N E ⟨206953453876,28431881⟩ E))) ⟨206955551638,28358210⟩ (N (N (N (N E ⟨206955552768,27736695⟩ E) ⟨206961840836,30495083⟩ E) ⟨206963937568,31036758⟩ (N (N E ⟨206963939296,29990601⟩ E) ⟨206963940160,29484057⟩ E)) ⟨206963941312,28825188⟩ (N (N (N E ⟨206963941376,28789126⟩ E) ⟨206968132034,31510151⟩ E) ⟨206968132802,31032856⟩ (N E ⟨206968133634,30525942⟩ E)))) ⟨206968135680,29322710⟩ (N (N (N (N (N E ⟨206969180532,31703534⟩ E) ⟨206970227333,32999678⟩ E) ⟨206980718592,30952938⟩ (N (N E ⟨206985957204,34430405⟩ E) ⟨206987004949,35162068⟩ E)) ⟨206997491488,36154484⟩ (N (N (N E ⟨206997491520,36131379⟩ E) ⟨206997492064,35741395⟩ E) ⟨206997492096,35718619⟩ (N E ⟨206997492608,35356660⟩ E))) ⟨206997492928,35132763⟩ (N (N (N (N E ⟨206997495808,33195364⟩ E) ⟨207002733588,37516513⟩ E) ⟨207003782597,37350705⟩ (N E ⟨207014268332,38971284⟩ E)) ⟨207014271016,36946064⟩ (N (N (N E ⟨207014273024,35516421⟩ E) ⟨207018462675,39590562⟩ E) ⟨207018463107,39250128⟩ (N E ⟨207018463794,38716247⟩ E)))))) ⟨207018467328,36108973⟩ (N (N (N (N (N (N (N E ⟨207019510820,40098574⟩ E) ⟨207019511236,39765761⟩ E) ⟨207019511668,39423795⟩ (N (N E ⟨207020559029,40561321⟩ E) ⟨207020559413,40249868⟩ E)) ⟨207020560373,39484219⟩ (N (N (N E ⟨207020560789,39158096⟩ E) ⟨207021608950,39645585⟩ E) ⟨207022659190,38513054⟩ (N E ⟨207022661632,36706441⟩ E))) ⟨207031045984,41243304⟩ (N (N (N (N E ⟨207031046112,41138033⟩ E) ⟨207031046528,40798215⟩ E) ⟨207031046560,40772221⟩ (N (N E ⟨207031047072,40359116⟩ E) ⟨207031047104,40333471⟩ E)) ⟨207031047392,40103581⟩ (N (N (N E ⟨207031047680,39875327⟩ E) ⟨207031048416,39299349⟩ E) ⟨207031048892,38932375⟩ (N E ⟨207031049344,38587861⟩ E)))) ⟨207031050240,37916125⟩ (N (N (N (N (N E ⟨207033143040,41655417⟩ E) ⟨207033143872,40970021⟩ E) ⟨207037336645,42921697⟩ (N (N E ⟨207037337061,42565511⟩ E) ⟨207037338116,41678635⟩ E)) ⟨207053064900,45870711⟩ (N (N (N E ⟨207053064916,45855969⟩ E) ⟨207053065332,45474730⟩ E) ⟨207053065748,45097446⟩ (N E ⟨207053066164,44724068⟩ E))) ⟨207054116532,43325839⟩ (N (N (N (N E ⟨207054118132,41980891⟩ E) ⟨207056212007,45139484⟩ E) ⟨207060406304,45841150⟩ (N E ⟨207060406880,45318049⟩ E)) ⟨207060407712,44575564⟩ (N (N (N E ⟨207064600112,47005328⟩ E) ⟨207064600448,46690725⟩ E) ⟨207064601024,46157506⟩ (N E ⟨207064601856,45400671⟩ E))))) ⟨207064602112,45170925⟩ (N (N (N (N (N (N E ⟨207064603712,43767473⟩ E) ⟨207066697472,47164637⟩ E) ⟨207066698240,46447719⟩ (N (N E ⟨207081381888,45587265⟩ E) ⟨207085571640,50616303⟩ E)) ⟨207085571651,50605168⟩ (N (N (N E ⟨207085572067,50186287⟩ E) ⟨207085572216,50037311⟩ E) ⟨207085572722,49535500⟩ (N E ⟨207085572754,49503977⟩ E))) ⟨207085573490,48785819⟩ (N (N (N (N E ⟨207085573586,48693110⟩ E) ⟨207085573810,48477642⟩ E) ⟨207085574418,47898782⟩ (N (N E ⟨207085576192,46258495⟩ E) ⟨207086620164,50853633⟩ E)) ⟨207086620596,50416456⟩ (N (N (N E ⟨207087670612,49170945⟩ E) ⟨207089765948,51352040⟩ E) ⟨207089767447,49840788⟩ (N E ⟨207089768886,48441988⟩ E)))) ⟨207089770496,46934644⟩ (N (N (N (N (N E ⟨207093960256,52093042⟩ E) ⟨207093960832,51497181⟩ E) ⟨207098154880,52506657⟩ (N (N E ⟨207098155456,51907019⟩ E) ⟨207098156000,51348537⟩ E)) ⟨207098156224,51120758⟩ (N (N (N E ⟨207098156320,51023525⟩ E) ⟨207098157952,49405401⟩ E) ⟨207098158016,49343262⟩ (N E ⟨207098159104,48301700⟩ E))) ⟨207102350690,51685698⟩ (N (N (N (N E ⟨207102351522,50842089⟩ E) ⟨207102352354,50015625⟩ E) ⟨207103396596,54706915⟩ (N E ⟨207103396980,54286976⟩ E)) ⟨207119125651,57165676⟩ (N (N (N E ⟨207119126067,56691471⟩ E) ⟨207119126499,56204222⟩ E) ⟨207119127186,55440094⟩ (N E ⟨207119127954,54601185⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab12 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨207120174212,57379803⟩ E) ⟨207120175060,56414675⟩ E) ⟨207120175604,55806211⟩ (N (N E ⟨207121225076,55010292⟩ E) ⟨207121225908,54112498⟩ E)) ⟨207121226228,53772076⟩ (N (N (N E ⟨207121227060,52899427⟩ E) ⟨207122271782,57293107⟩ E) ⟨207123324928,52520949⟩ (N E ⟨207127518368,54150578⟩ E))) ⟨207129613188,57088934⟩ (N (N (N (N E ⟨207131711808,55829662⟩ E) ⟨207136951844,60074402⟩ E) ⟨207144296448,56172309⟩ (N (N E ⟨207148485712,62890923⟩ E) ⟨207148490752,56917346⟩ E)) ⟨207152681850,61429249⟩ (N (N (N E ⟨207152683538,59411520⟩ E) ⟨207152684370,58447491⟩ E) ⟨207154781492,58864058⟩ (N E ⟨207154782208,58044128⟩ E)))) ⟨207156877078,61103859⟩ (N (N (N (N (N E ⟨207156878196,59771244⟩ E) ⟨207165267968,59946710⟩ E) ⟨207170506772,66016755⟩ (N (N E ⟨207172604054,66264447⟩ E) ⟨207173655364,62970277⟩ E)) ⟨207173656576,61490925⟩ (N (N (N E ⟨207182040224,69560898⟩ E) ⟨207182040640,68983909⟩ E) ⟨207187283156,70576636⟩ (N E ⟨207187285108,67882283⟩ E))) ⟨207188332565,69625825⟩ (N (N (N (N E ⟨207188332709,69426116⟩ E) ⟨207188333125,68853187⟩ E) ⟨207188333236,68701315⟩ (N (N E ⟨207189381270,69661709⟩ E) ⟨207190431260,67940743⟩ E)) ⟨207198817456,73053181⟩ (N (N (N E ⟨207198818016,72239000⟩ E) ⟨207198818432,71641514⟩ E) ⟨207198819616,69974472⟩ (N E ⟨207200916128,71301596⟩ E))))) ⟨207200916992,70089331⟩ (N (N (N (N (N (N E ⟨207200917056,70000563⟩ E) ⟨207201963266,73600806⟩ E) ⟨207203013856,70919039⟩ (N (N E ⟨207203015520,68626047⟩ E) ⟨207204060388,74092058⟩ E)) ⟨207204060804,73477693⟩ (N (N (N E ⟨207204061236,72846424⟩ E) ⟨207205108949,74338407⟩ E) ⟨207215595104,75994540⟩ (N E ⟨207215595200,75848818⟩ E))) ⟨207215595616,75221376⟩ (N (N (N (N E ⟨207215599616,69507379⟩ E) ⟨207221885813,78522136⟩ E) ⟨207221886229,77869842⟩ (N (N E ⟨207221887029,76634362⟩ E) ⟨207221887061,76585454⟩ E)) ⟨207221887700,75616951⟩ (N (N (N E ⟨207221887732,75568854⟩ E) ⟨207221888149,74945571⟩ E) ⟨207221888564,74331646⟩ (N E ⟨207221889396,73119661⟩ E)))) ⟨207223985319,75360834⟩ (N (N (N (N (N E ⟨207223986774,73224210⟩ E) ⟨207223988224,71169751⟩ E) ⟨207232376032,74002844⟩ (N (N E ⟨207232376832,72851820⟩ E) ⟨207236571136,73700240⟩ E)) ⟨207237614468,82005355⟩ (N (N (N E ⟨207237614484,81979025⟩ E) ⟨207237614900,81298119⟩ E) ⟨207237615316,80624271⟩ (N E ⟨207237615732,79957391⟩ E))) ⟨207238664900,79248128⟩ (N (N (N (N E ⟨207249149104,84118212⟩ E) ⟨207249149536,83393840⟩ E) ⟨207253345616,81412715⟩ (N E ⟨207253345680,81309515⟩ E)) ⟨207253347344,78682822⟩ (N (N (N E ⟨207255442964,81555430⟩ E) ⟨207255443764,80276102⟩ E) ⟨207257541460,79867983⟩ (N E ⟨207265927396,86108356⟩ E)))))) ⟨207265927744,85513599⟩ (N (N (N (N (N (N (N E ⟨207265927972,85126714⟩ E) ⟨207265928320,84540414⟩ E) ⟨207265928804,83733355⟩ (N (N E ⟨207265930664,80720077⟩ E) ⟨207265931264,79777068⟩ E)) ⟨207270121139,88047146⟩ (N (N (N E ⟨207271169732,88260255⟩ E) ⟨207271170164,87502227⟩ E) ⟨207282704692,89830015⟩ (N E ⟨207282705272,88799294⟩ E))) ⟨207282708480,83357886⟩ (N (N (N (N E ⟨207286898424,91850418⟩ E) ⟨207286900626,87917516⟩ E) ⟨207286902784,84265403⟩ (N (N E ⟨207287946164,93653354⟩ E) ⟨207287946548,92935147⟩ E)) ⟨207288995669,92175613⟩ (N (N (N E ⟨207288995957,91647277⟩ E) ⟨207288996628,90430938⟩ E) ⟨207288997396,89063431⟩ (N E ⟨207288997428,89007014⟩ E)))) ⟨207288997748,88445301⟩ (N (N (N (N (N E ⟨207288998260,87555746⟩ E) ⟨207288998516,87115164⟩ E) ⟨207288999936,84721008⟩ (N (N E ⟨207291092732,92837572⟩ E) ⟨207291093308,91776650⟩ E)) ⟨207291093888,90723634⟩ (N (N (N E ⟨207299480800,95873024⟩ E) ⟨207299481232,95047625⟩ E) ⟨207299481664,94231092⟩ (N E ⟨207299482240,93155976⟩ E))) ⟨207299482272,93096698⟩ (N (N (N (N E ⟨207299482816,92096153⟩ E) ⟨207299483104,91571895⟩ E) ⟨207299485696,87017505⟩ (N (N E ⟨207304723780,96956428⟩ E) ⟨207304724196,96152858⟩ E)) ⟨207304724628,95327176⟩ (N (N (N E ⟨207304725172,94299997⟩ E) ⟨207305773828,94398767⟩ E) ⟨207305774596,92971146⟩ (N E ⟨207305775428,91454885⟩ E))))) ⟨207320452467,100738137⟩ (N (N (N (N (N (N E ⟨207320452883,99903420⟩ E) ⟨207322550421,99650457⟩ E) ⟨207322551092,98328110⟩ (N (N E ⟨207322551860,96841415⟩ E) ⟨207322552692,95262406⟩ E)) ⟨207322553844,93128848⟩ (N (N (N E ⟨207328845824,93611463⟩ E) ⟨207333035728,103168452⟩ E) ⟨207333036160,102282437⟩ (N E ⟨207333036736,101115830⟩ E))) ⟨207333037568,99459945⟩ (N (N (N (N E ⟨207333037824,98957274⟩ E) ⟨207333038400,97837827⟩ E) ⟨207339328324,102398977⟩ (N (N E ⟨207340376374,103738349⟩ E) ⟨207343522864,102953915⟩ E)) ⟨207349812544,108281690⟩ (N (N (N E ⟨207349814200,104763758⟩ E) ⟨207349814968,103180788⟩ E) ⟨207349817344,98469199⟩ (N E ⟨207354006883,109289674⟩ E)))) ⟨207354007634,107661531⟩ (N (N (N (N (N E ⟨207354011200,100331682⟩ E) ⟨207356104901,107949524⟩ E) ⟨207356105588,106483531⟩ (N (N E ⟨207356106676,104212397⟩ E) ⟨207358202816,106850766⟩ E)) ⟨207358203584,105236326⟩ (N (N (N E ⟨207358205952,100446772⟩ E) ⟨207366590192,111683239⟩ E) ⟨207366590288,111469236⟩ (N E ⟨207366590624,110724252⟩ E))) ⟨207366590704,110547793⟩ (N (N (N (N E ⟨207366590752,110442086⟩ E) ⟨207366591136,109600967⟩ E) ⟨207366591168,109531236⟩ (N E ⟨207366591200,109461560⟩ E)) ⟨207366591712,108354249⟩ (N (N (N E ⟨207366591744,108285508⟩ E) ⟨207366592032,107669288⟩ E) ⟨207366592320,107057445⟩ (N E ⟨207366593152,105314155⟩ E))))))) ⟨207366593888,103801507⟩ (N (N (N (N (N (N (N (N E ⟨207366593984,103606213⟩ E) ⟨207366594560,102444049⟩ E) ⟨207370784115,113642794⟩ (N (N E ⟨207370784531,112701149⟩ E) ⟨207370784802,112092966⟩ E)) ⟨207370784834,112021422⟩ (N (N (N E ⟨207370785666,110181161⟩ E) ⟨207370788864,103450075⟩ E) ⟨207371834676,109502603⟩ (N E ⟨207372881285,114156250⟩ E))) ⟨207387562002,116543846⟩ (N (N (N (N E ⟨207387562930,114410415⟩ E) ⟨207388611316,115117927⟩ E) ⟨207389658565,118488266⟩ (N (N E ⟨207389659365,116609976⟩ E) ⟨207389659397,116535622⟩ E)) ⟨207389660052,115026622⟩ (N (N (N E ⟨207389660084,114953528⟩ E) ⟨207389660485,114042469⟩ E) ⟨207389660916,113073296⟩ (N E ⟨207389661172,112502511⟩ E)))) ⟨207389661748,111231359⟩ (N (N (N (N (N E ⟨207390708470,115663736⟩ E) ⟨207391760384,108554093⟩ E) ⟨207395951520,116650695⟩ (N (N E ⟨207395953184,112873205⟩ E) ⟨207400144192,121654515⟩ E)) ⟨207400144624,120607658⟩ (N (N (N E ⟨207400145056,119572039⟩ E) ⟨207400145632,118208448⟩ E) ⟨207400146400,116420428⟩ (N E ⟨207400146496,116199310⟩ E))) ⟨207400146752,115612224⟩ (N (N (N (N E ⟨207400147264,114449136⟩ E) ⟨207400147328,114304780⟩ E) ⟨207406436149,122150726⟩ (N (N E ⟨207406437252,119495844⟩ E) ⟨207406438020,117689812⟩ E)) ⟨207406438852,115771620⟩ (N (N (N E ⟨207406439684,113892360⟩ E) ⟨207419020176,122846125⟩ E) ⟨207419020944,120989567⟩ (N E ⟨207419021040,120759971⟩ E))))) ⟨207419021776,119017710⟩ (N (N (N (N (N (N E ⟨207419021872,118792782⟩ E) ⟨207419022640,117012355⟩ E) ⟨207419022704,116865497⟩ (N (N E ⟨207423212597,128731375⟩ E) ⟨207423216116,120033836⟩ E)) ⟨207423216372,119430204⟩ (N (N (N E ⟨207433701984,122546376⟩ E) ⟨207433703424,119131542⟩ E) ⟨207454671698,132839154⟩ (N E ⟨207455718852,136963957⟩ E))) ⟨207456768005,135694186⟩ (N (N (N (N E ⟨207456768293,134917089⟩ E) ⟨207456768405,134616388⟩ E) ⟨207456768980,133085737⟩ (N (N E ⟨207456769748,131075103⟩ E) ⟨207456770100,130166259⟩ E)) ⟨207456770868,128210517⟩ (N (N (N E ⟨207456772096,125159081⟩ E) ⟨207457817974,132279321⟩ E) ⟨207467253728,138820464⟩ (N E ⟨207471447939,140300486⟩ E)))) ⟨207471448226,139499272⟩ (N (N (N (N (N E ⟨207471448962,137470583⟩ E) ⟨207472496084,141823539⟩ E) ⟨207472496500,140648956⟩ (N (N E ⟨207473544677,142084527⟩ E) ⟨207475646464,130201516⟩ E)) ⟨207484035072,132474608⟩ (N (N (N E ⟨207488227378,138969641⟩ E) ⟨207489272948,147852138⟩ E) ⟨207489273364,146625474⟩ (N E ⟨207489273780,145411509⟩ E))) ⟨207490322757,144562433⟩ (N (N (N (N E ⟨207490323444,142600466⟩ E) ⟨207490324212,140446424⟩ E) ⟨207490325044,138158586⟩ (N E ⟨207492423680,134767399⟩ E)) ⟨207500808144,148775704⟩ (N (N (N E ⟨207500808448,147876300⟩ E) ⟨207500810656,141543691⟩ E) ⟨207500811520,139158233⟩ (N E ⟨207500812288,137079886⟩ E)))))) ⟨207502907904,141875120⟩ (N (N (N (N (N (N (N E ⟨207502908736,139572810⟩ E) ⟨207505002722,149220782⟩ E) ⟨207505003554,146771356⟩ (N (N E ⟨207505004386,144371996⟩ E) ⟨207505005760,140515959⟩ E)) ⟨207505006592,138243516⟩ (N (N (N E ⟨207506050164,152964262⟩ E) ⟨207517585376,153810287⟩ E) ⟨207520731474,153634926⟩ (N E ⟨207521779267,156379296⟩ E))) ⟨207521779683,155084878⟩ (N (N (N (N E ⟨207523879028,149094808⟩ E) ⟨207525978112,144135524⟩ E) ⟨207534364608,152738434⟩ (N (N E ⟨207534366380,147505149⟩ E) ⟨207534366720,146526793⟩ E)) ⟨207539605428,160751374⟩ (N (N (N E ⟨207541703574,158243529⟩ E) ⟨207551143936,151368407⟩ E) ⟨207555333683,166982753⟩ (N E ⟨207556382244,167368314⟩ E)))) ⟨207559530614,159764152⟩ (N (N (N (N (N E ⟨207567917488,168007961⟩ E) ⟨207567917920,166570368⟩ E) ⟨207567918046,166153969⟩ (N (N E ⟨207567918910,163333450⟩ E) ⟨207567919072,162811285⟩ E)) ⟨207567919104,162708388⟩ (N (N (N E ⟨207567919936,160061385⟩ E) ⟨207567920316,158870335⟩ E) ⟨207567920768,157468006⟩ (N E ⟨207567921152,156288787⟩ E))) ⟨207572110915,172333583⟩ (N (N (N (N E ⟨207572111331,170907105⟩ E) ⟨207572111618,169931572⟩ E) ⟨207572112386,167355116⟩ (N E ⟨207572113250,164514710⟩ E)) ⟨207572114624,160120680⟩ (N (N (N E ⟨207573159876,171350911⟩ E) ⟨207573159892,171296192⟩ E) ⟨207573160884,167945849⟩ (N E ⟨207576309760,158778510⟩ E))))) ⟨207578404144,168333107⟩ (N (N (N (N (N (N E ⟨207584698368,161287921⟩ E) ⟨207587840018,175844242⟩ E) ⟨207587840434,174392053⟩ (N (N E ⟨207588889746,172194069⟩ E) ⟨207590988724,166741058⟩ E)) ⟨207593086976,163817019⟩ (N (N (N E ⟨207601470976,182242438⟩ E) ⟨207601471408,180675711⟩ E) ⟨207601471840,179125788⟩ (N E ⟨207601471872,179011642⟩ E))) ⟨207601472384,177197605⟩ (N (N (N (N E ⟨207601472960,175184201⟩ E) ⟨207608813078,177247423⟩ E) ⟨207618248256,187650757⟩ (N (N E ⟨207621394434,187029046⟩ E) ⟨207621394866,185425275⟩ E)) ⟨207622443056,187210399⟩ (N (N (N E ⟨207622445714,177602801⟩ E) ⟨207622446578,174613166⟩ E) ⟨207622447104,172823873⟩ (N E ⟨207624540741,185932118⟩ E)))) ⟨207624542388,179961268⟩ (N (N (N (N (N E ⟨207624543156,177259053⟩ E) ⟨207625589302,186337939⟩ E) ⟨207626640310,177920114⟩ (N (N E ⟨207626641408,174130248⟩ E) ⟨207635025488,193316506⟩ E)) ⟨207635026048,191166441⟩ (N (N (N E ⟨207635026336,190072335⟩ E) ⟨207635026848,188146519⟩ E) ⟨207635026880,188026967⟩ (N E ⟨207635027424,186009045⟩ E))) ⟨207635027456,185891189⟩ (N (N (N (N E ⟨207635028576,181824413⟩ E) ⟨207635028768,181138461⟩ E) ⟨207635029440,178762967⟩ (N E ⟨207635030016,176757759⟩ E)) ⟨207640268420,194920675⟩ (N (N (N E ⟨207643415654,190215010⟩ E) ⟨207651803232,197039401⟩ E) ⟨207653901456,193591309⟩ (N E ⟨207653902320,190307906⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab13 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨207653903920,184409300⟩ E) ⟨207653903984,184178145⟩ E) ⟨207657045652,200689171⟩ (N (N E ⟨207657046068,199028652⟩ E) ⟨207664386656,199364560⟩ E)) ⟨207668580464,202810742⟩ (N (N (N E ⟨207668580800,201457234⟩ E) ⟨207668582208,195906721⟩ E) ⟨207668582464,194918170⟩ (N E ⟨207668583232,191989707⟩ E))) ⟨207668584064,188879012⟩ (N (N (N (N E ⟨207673822516,208066394⟩ E) ⟨207673822932,206341812⟩ E) ⟨207673823348,204635066⟩ (N (N E ⟨207676971824,194842717⟩ E) ⟨207676973056,190190453⟩ E)) ⟨207685358840,203969764⟩ (N (N (N E ⟨207685360440,197624324⟩ E) ⟨207685361592,193207917⟩ E) ⟨207685361664,192936009⟩ (N E ⟨207687458816,193625471⟩ E)))) ⟨207689551992,210189680⟩ (N (N (N (N (N E ⟨207689553042,205844902⟩ E) ⟨207689554194,201206450⟩ E) ⟨207689555968,194316163⟩ (N (N E ⟨207690599732,214111556⟩ E) ⟨207693746300,211671008⟩ E)) ⟨207693746876,209256696⟩ (N (N (N E ⟨207693747456,206860309⟩ E) ⟨207693748224,203739711⟩ E) ⟨207693748502,202624644⟩ (N E ⟨207693749056,200425194⟩ E))) ⟨207697940608,213157416⟩ (N (N (N (N E ⟨207702134368,217010943⟩ E) ⟨207702135232,213301458⟩ E) ⟨207702135808,210872451⟩ (N (N E ⟨207702136072,209770717⟩ E) ⟨207702136352,208610064⟩ E)) ⟨207702136576,207687318⟩ (N (N (N E ⟨207702136840,206606339⟩ E) ⟨207702137440,204175608⟩ E) ⟨207702137672,203245318⟩ (N E ⟨207702138624,199482961⟩ E))))) ⟨207702138824,198703649⟩ (N (N (N (N (N (N E ⟨207702138880,198486124⟩ E) ⟨207706333184,199885944⟩ E) ⟨207710525350,209931739⟩ (N (N E ⟨207710527488,201290680⟩ E) ⟨207721012848,206434157⟩ E)) ⟨207723106403,222417447⟩ (N (N (N E ⟨207723106835,220511139⟩ E) ⟨207723107506,217590512⟩ E) ⟨207724154996,222726762⟩ (N E ⟨207724155540,220326434⟩ E))) ⟨207724155956,218512682⟩ (N (N (N (N E ⟨207725203701,222538685⟩ E) ⟨207727304704,206958777⟩ E) ⟨207735692160,214616784⟩ (N (N E ⟨207735692992,211140561⟩ E) ⟨207738835506,226129476⟩ E)) ⟨207740931812,230763039⟩ (N (N (N E ⟨207752466064,235505058⟩ E) ⟨207752466496,233481886⟩ E) ⟨207752470528,215608358⟩ (N E ⟨207756660499,236478490⟩ E)))) ⟨207756660915,234523083⟩ (N (N (N (N (N E ⟨207756661331,232587851⟩ E) ⟨207756662002,229508243⟩ E) ⟨207756662834,225760168⟩ (N (N E ⟨207756663666,222088313⟩ E) ⟨207756664498,218490825⟩ E)) ⟨207756664832,217067153⟩ (N (N (N E ⟨207757709460,235063200⟩ E) ⟨207758758292,234260403⟩ E) ⟨207758761844,218395730⟩ (N E ⟨207760858198,222586011⟩ E))) ⟨207760859136,218530860⟩ (N (N (N (N E ⟨207769245280,232474660⟩ E) ⟨207769247036,224566275⟩ E) ⟨207769247744,221473012⟩ (N E ⟨207773439170,235954329⟩ E)) ⟨207773442048,222951456⟩ (N (N (N E ⟨207776584406,239459680⟩ E) ⟨207786020992,245954446⟩ E) ⟨207786024204,230809870⟩ (N E ⟨207786024960,227416258⟩ E)))))) ⟨207790215763,245282141⟩ (N (N (N (N (N (N (N E ⟨207790216434,242034453⟩ E) ⟨207790217202,238382984⟩ E) ⟨207792314740,237349759⟩ (N (N E ⟨207792315508,233789171⟩ E) ⟨207792316340,230006903⟩ E)) ⟨207793362614,241057765⟩ (N (N (N E ⟨207802798320,251903986⟩ E) ⟨207802798368,251663114⟩ E) ⟨207802799968,243796272⟩ (N E ⟨207802800832,239675946⟩ E))) ⟨207802801088,238471859⟩ (N (N (N (N E ⟨207802802176,233438077⟩ E) ⟨207805944050,253121740⟩ E) ⟨207805944466,251033689⟩ (N (N E ⟨207806992147,255966845⟩ E) ⟨207819575456,258899527⟩ E)) ⟨207819575552,258404503⟩ (N (N (N E ⟨207819579392,239538451⟩ E) ⟨207823769379,262550195⟩ E) ⟨207823769795,260379378⟩ (N E ⟨207823770227,258148768⟩ E)))) ⟨207823770771,255373730⟩ (N (N (N (N (N E ⟨207823770898,254731258⟩ E) ⟨207823771666,250888842⟩ E) ⟨207823772530,246652340⟩ (N (N E ⟨207823772786,245414287⟩ E) ⟨207823773394,242504906⟩ E)) ⟨207823773696,241075816⟩ (N (N (N E ⟨207825867988,255859823⟩ E) ⟨207825869940,246189004⟩ E) ⟨207836354208,257596835⟩ (N E ⟨207836354784,254681414⟩ E))) ⟨207836356608,245717359⟩ (N (N (N (N E ⟨207839498466,266488592⟩ E) ⟨207839498898,264205997⟩ E) ⟨207840547011,267074249⟩ (N (N E ⟨207840547427,264870588⟩ E) ⟨207840548098,261363814⟩ E)) ⟨207840548866,257421041⟩ (N (N (N E ⟨207840549698,253233256⟩ E) ⟨207840550530,249130308⟩ E) ⟨207840550912,247274354⟩ (N E ⟨207842644181,267820944⟩ E))))) ⟨207844745216,248836257⟩ (N (N (N (N (N (N E ⟨207853129456,274699800⟩ E) ⟨207853129888,272341043⟩ E) ⟨207853133824,251974780⟩ (N (N E ⟨207869907664,276093040⟩ E) ⟨207869907748,275632346⟩ E)) ⟨207869908096,273733963⟩ (N (N (N E ⟨207869908160,273386617⟩ E) ⟨207869908672,270627593⟩ E) ⟨207869909248,267565174⟩ (N E ⟨207869909824,264545962⟩ E))) ⟨207872004608,278093900⟩ (N (N (N (N E ⟨207878299648,261508078⟩ E) ⟨207888783600,275132446⟩ E) ⟨207890879352,283727045⟩ (N (N E ⟨207890879858,280892422⟩ E) ⟨207890880946,274916364⟩ E)) ⟨207890882560,266340931⟩ (N (N (N E ⟨207891927732,285267478⟩ E) ⟨207892976021,287337215⟩ E) ⟨207892976037,287245670⟩ (N E ⟨207892976453,284878228⟩ E)))) ⟨207895073084,288720924⟩ (N (N (N (N (N E ⟨207895075254,276567497⟩ E) ⟨207895076864,267961688⟩ E) ⟨207899267968,287139735⟩ (N (N E ⟨207903461760,291833793⟩ E) ⟨207903462016,290350418⟩ E)) ⟨207903462048,290165660⟩ (N (N (N E ⟨207903462176,289428095⟩ E) ⟨207903462592,287047141⟩ E) ⟨207903462624,286865007⟩ (N E ⟨207903463168,283790719⟩ E))) ⟨207903463456,282179830⟩ (N (N (N (N E ⟨207903463712,280757516⟩ E) ⟨207903463744,280580357⟩ E) ⟨207903464576,276022906⟩ (N E ⟨207903465472,271217907⟩ E)) ⟨207905560768,282137294⟩ (N (N (N E ⟨207908704116,297123404⟩ E) ⟨207908705108,291309280⟩ E) ⟨207908705524,288913468⟩ (N E ⟨207920242688,277789161⟩ E))))))) ⟨207922339840,278616080⟩ (N (N (N (N (N (N (N (N E ⟨207924433203,301147024⟩ E) ⟨207924433635,298568601⟩ E) ⟨207924434322,294524780⟩ (N (N E ⟨207925480980,306443619⟩ E) ⟨207925481396,303906461⟩ E)) ⟨207925482196,299100699⟩ (N (N (N E ⟨207925482228,298910452⟩ E) ⟨207925483316,292531133⟩ E) ⟨207926534144,280273594⟩ (N E ⟨207932822944,297946370⟩ E))) ⟨207937016512,304116589⟩ (N (N (N (N E ⟨207937017024,301039664⟩ E) ⟨207937017088,300657791⟩ E) ⟨207937018752,290938279⟩ (N (N E ⟨207937018944,289842236⟩ E) ⟨207937019904,284438812⟩ E)) ⟨207944357718,300183423⟩ (N (N (N E ⟨207953793408,313299085⟩ E) ⟨207957987299,317727818⟩ E) ⟨207957987715,315103288⟩ (N E ⟨207957988131,312505809⟩ E)))) ⟨207957988818,308274558⟩ (N (N (N (N (N E ⟨207957989650,303245693⟩ E) ⟨207957990482,298318982⟩ E) ⟨207957990642,297383040⟩ (N (N E ⟨207957991314,293491945⟩ E) ⟨207957991424,292861086⟩ E)) ⟨207960088576,293710046⟩ (N (N (N E ⟨207962184950,299084934⟩ E) ⟨207962185728,294560230⟩ E) ⟨207970570640,320520663⟩ (N E ⟨207970570976,318384647⟩ E))) ⟨207970571056,317878698⟩ (N (N (N (N E ⟨207970571104,317575610⟩ E) ⟨207970572064,311589044⟩ E) ⟨207970572096,311391933⟩ (N (N E ⟨207970572384,309624928⟩ E) ⟨207970573408,303442903⟩ E)) ⟨207970574336,297973208⟩ (N (N (N E ⟨207972668768,315268464⟩ E) ⟨207972669632,309926817⟩ E) ⟨207974766754,311000285⟩ (N E ⟨207974767586,305944821⟩ E))))) ⟨207974768640,299687039⟩ (N (N (N (N (N (N E ⟨207989445968,322644525⟩ E) ⟨207989446800,317377883⟩ E) ⟨207991543250,322727411⟩ (N (N E ⟨207991544018,317863918⟩ E) ⟨207992590836,329600898⟩ E)) ⟨207992591124,327717972⟩ (N (N (N E ⟨207993641140,318953177⟩ E) ⟨207994688822,325102757⟩ E) ⟨207995738196,320462221⟩ (N E ⟨208004125408,333180902⟩ E))) ⟨208004125984,329392147⟩ (N (N (N (N E ⟨208004126752,324423874⟩ E) ⟨208004127616,318946036⟩ E) ⟨208004127680,318544887⟩ (N (N E ⟨208004127872,317345220⟩ E) ⟨208008318947,340199307⟩ E)) ⟨208020902336,342662533⟩ (N (N (N E ⟨208020902752,339838730⟩ E) ⟨208024048050,344186611⟩ E) ⟨208025096595,344876298⟩ (N E ⟨208025097027,341924871⟩ E)))) ⟨208025097571,338253036⟩ (N (N (N (N (N E ⟨208025097714,337296024⟩ E) ⟨208025098482,332213782⟩ E) ⟨208025099602,324972575⟩ (N (N E ⟨208025100178,321325358⟩ E) ⟨208025100288,320634671⟩ E)) ⟨208026145588,342500335⟩ (N (N (N E ⟨208027197440,321522773⟩ E) ⟨208029293142,331719174⟩ E) ⟨208037683168,326185701⟩ (N E ⟨208037683200,325981618⟩ E))) ⟨208054456240,361837635⟩ (N (N (N (N E ⟨208054456672,358733619⟩ E) ⟨208060748357,360016239⟩ E) ⟨208062849024,336807470⟩ (N E ⟨208071233520,369267276⟩ E)) ⟨208071233664,368207903⟩ (N (N (N E ⟨208071234080,365168764⟩ E) ⟨208074379698,367445137⟩ E) ⟨208075429984,355670857⟩ (N E ⟨208076477300,365147512⟩ E)))))) ⟨208088011168,374008493⟩ (N (N (N (N (N (N (N E ⟨208088014008,353581999⟩ E) ⟨208092207762,359328689⟩ E) ⟨208092209152,349659889⟩ (N (N E ⟨208093253684,379238678⟩ E) ⟨208094303637,369484976⟩ E)) ⟨208094303764,368556610⟩ (N (N (N E ⟨208094303796,368323152⟩ E) ⟨208094304628,362317606⟩ E) ⟨208094304884,360494416⟩ (N E ⟨208094306292,350669361⟩ E))) ⟨208096402838,355796185⟩ (N (N (N (N E ⟨208096403456,351515478⟩ E) ⟨208104788112,384076769⟩ E) ⟨208104788496,381149575⟩ (N (N E ⟨208104790144,368899244⟩ E) ⟨208104791008,362673371⟩ E)) ⟨208104791872,356578322⟩ (N (N (N E ⟨208104792064,355241300⟩ E) ⟨208106886656,374580129⟩ E) ⟨208110030964,386821096⟩ (N E ⟨208110031764,380709986⟩ E)))) ⟨208110031796,380468062⟩ (N (N (N (N (N E ⟨208110032884,372355796⟩ E) ⟨208111080964,376519736⟩ E) ⟨208113180672,358986641⟩ (N (N E ⟨208121565728,389083578⟩ E) ⟨208123664880,374947289⟩ E)) ⟨208123665176,372768145⟩ (N (N (N E ⟨208126808964,388855539⟩ E) ⟨208127858228,384082913⟩ E) ⟨208127860736,365587946⟩ (N E ⟨208138344036,388705548⟩ E))) ⟨208138344868,382369158⟩ (N (N (N (N E ⟨208138344960,381676455⟩ E) ⟨208138346496,370339742⟩ E) ⟨208145683926,393320208⟩ (N E ⟨208150929408,376082121⟩ E)) ⟨208155121336,396092960⟩ (N (N (N E ⟨208155123712,378005996⟩ E) ⟨208159317426,384350390⟩ E) ⟨208159317458,384109257⟩ (N E ⟨208159317808,381484172⟩ E))))) ⟨208159318016,379934745⟩ (N (N (N (N (N (N E ⟨208160363572,403740265⟩ E) ⟨208161411733,407600518⟩ E) ⟨208161413141,396382086⟩ (N (N E ⟨208161413492,393645772⟩ E) ⟨208161413812,391171678⟩ E)) ⟨208163509952,400076804⟩ (N (N (N E ⟨208163512320,381868366⟩ E) ⟨208171897840,409952800⟩ E) ⟨208171898848,401848983⟩ (N E ⟨208171900864,386233418⟩ E))) ⟨208171900928,385750226⟩ (N (N (N (N E ⟨208176091667,415949049⟩ E) ⟨208176095232,387698463⟩ E) ⟨208177140692,412771148⟩ (N (N E ⟨208177140820,411723539⟩ E) ⟨208178190660,402059739⟩ E)) ⟨208192868531,427348336⟩ (N (N (N E ⟨208192868947,423821953⟩ E) ⟨208192872448,395540112⟩ E) ⟨208194967924,409793423⟩ (N E ⟨208194969600,396525796⟩ E)))) ⟨208205451328,434753781⟩ (N (N (N (N (N E ⟨208205452192,427339925⟩ E) ⟨208205452224,427068386⟩ E) ⟨208205452736,422752951⟩ (N (N E ⟨208205452768,422485050⟩ E) ⟨208205452800,422217362⟩ E)) ⟨208205453632,415331310⟩ (N (N (N E ⟨208205453888,413240819⟩ E) ⟨208210695156,429268024⟩ E) ⟨208211744388,424243923⟩ (N E ⟨208224327312,430433202⟩ E))) ⟨208226426736,412617823⟩ (N (N (N (N E ⟨208226426880,411457054⟩ E) ⟨208228524032,412462202⟩ E) ⟨208239005984,450101821⟩ (N E ⟨208239006688,443842161⟩ E)) ⟨208239006816,442715761⟩ (N (N (N E ⟨208239007200,439357940⟩ E) ⟨208239007232,439079561⟩ E) ⟨208239007264,438801403⟩ (N E ⟨208239007776,434380687⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab14 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨208239008096,431646000⟩ E) ⟨208239008384,429203163⟩ E) ⟨208239009120,423038436⟩ (N (N E ⟨208239009216,422242525⟩ E) ⟨208239009792,417506173⟩ E)) ⟨208242152082,448423978⟩ (N (N (N E ⟨208243203904,421111265⟩ E) ⟨208243204096,419532271⟩ E) ⟨208255783584,455375657⟩ (N E ⟨208255785228,440784728⟩ E))) ⟨208259977411,461931129⟩ (N (N (N (N E ⟨208259981312,427685267⟩ E) ⟨208262075973,450246571⟩ E) ⟨208262076116,448974122⟩ (N (N E ⟨208262076148,448689994⟩ E) ⟨208262076980,441380943⟩ E)) ⟨208262077236,439162002⟩ (N (N (N E ⟨208262078464,428709859⟩ E) ⟨208268367584,452093479⟩ E) ⟨208268368416,444728264⟩ (N E ⟨208272560816,464012932⟩ E)))) ⟨208272561664,456268993⟩ (N (N (N (N (N E ⟨208272562396,449713919⟩ E) ⟨208272562560,448261474⟩ E) ⟨208272564224,433851033⟩ (N (N E ⟨208276755043,466936121⟩ E) ⟨208276755059,466787508⟩ E)) ⟨208278854084,450858890⟩ (N (N (N E ⟨208278854916,443540334⟩ E) ⟨208285147136,440060510⟩ E) ⟨208291436272,463872933⟩ (N E ⟨208291437008,457180420⟩ E))) ⟨208291437936,448913168⟩ (N (N (N (N E ⟨208292483730,474832944⟩ E) ⟨208293534514,455072739⟩ E) ⟨208293535664,444920119⟩ (N (N E ⟨208293535744,444224437⟩ E) ⟨208295630580,466020305⟩ E)) ⟨208297726652,477228094⟩ (N (N (N E ⟨208297730048,446313681⟩ E) ⟨208301921536,473976428⟩ E) ⟨208306116160,473185269⟩ (N E ⟨208306116928,466058232⟩ E))))) ⟨208306117280,462836544⟩ (N (N (N (N (N (N E ⟨208306118048,455903499⟩ E) ⟨208306118656,450506728⟩ E) ⟨208322892928,486354180⟩ (N (N E ⟨208322895872,458951035⟩ E) ⟨208324990033,487933413⟩ E)) ⟨208324990704,481489106⟩ (N (N (N E ⟨208324991472,474243259⟩ E) ⟨208324992304,466546771⟩ E) ⟨208327089936,463244693⟩ (N E ⟨208329184053,492960821⟩ E))) ⟨208329184469,488905946⟩ (N (N (N (N E ⟨208329185477,479252261⟩ E) ⟨208329186164,472809143⟩ E) ⟨208339670208,494756294⟩ (N (N E ⟨208339672512,472776118⟩ E) ⟨208339673088,467472925⟩ E)) ⟨208343866792,475166629⟩ (N (N (N E ⟨208344913140,497078715⟩ E) ⟨208348061696,471762950⟩ E) ⟨208356450304,476072355⟩ (N E ⟨208358547456,477152733⟩ E)))) ⟨208360644210,481974859⟩ (N (N (N (N (N E ⟨208360644242,481672763⟩ E) ⟨208360644608,478234323⟩ E) ⟨208362740276,493483972⟩ (N (N E ⟨208362741760,479317123⟩ E) ⟨208369031170,502374738⟩ E)) ⟨208369033216,482572786⟩ (N (N (N E ⟨208373225632,503068523⟩ E) ⟨208373227520,484749281⟩ E) ⟨208375323968,492586280⟩ (N E ⟨208377418467,520254776⟩ E))) ⟨208377418754,517296487⟩ (N (N (N (N E ⟨208377419618,508516760⟩ E) ⟨208377421696,488151432⟩ E) ⟨208381616128,489116790⟩ (N E ⟨208394195747,528955521⟩ E)) ⟨208394197554,510375650⟩ (N (N (N E ⟨208394198928,496791597⟩ E) ⟨208396296192,496806506⟩ E) ⟨208406778672,535892928⟩ (N E ⟨208406779136,530979095⟩ E)))))) ⟨208406781184,509951634⟩ (N (N (N (N (N (N (N E ⟨208423555904,545223817⟩ E) ⟨208423556320,540739294⟩ E) ⟨208423559168,511244579⟩ (N (N E ⟨208426702002,543010467⟩ E) ⟨208427751123,537765951⟩ E)) ⟨208427753472,513483946⟩ (N (N (N E ⟨208428798868,547295632⟩ E) ⟨208428799284,542795939⟩ E) ⟨208429849524,525826273⟩ (N E ⟨208431947776,515728144⟩ E))) ⟨208440334560,539209664⟩ (N (N (N (N E ⟨208440336384,520231031⟩ E) ⟨208448724992,524753234⟩ E) ⟨208457110368,564114819⟩ (N (N E ⟨208459208592,553444311⟩ E) ⟨208460256498,561436939⟩ E)) ⟨208461307904,531572743⟩ (N (N (N E ⟨208473887600,573674680⟩ E) ⟨208473888016,568957266⟩ E) ⟨208473888574,562705481⟩ (N E ⟨208473889600,551432782⟩ E)))) ⟨208473890816,538435678⟩ (N (N (N (N (N E ⟨208478081859,576637736⟩ E) ⟨208478082914,564704230⟩ E) ⟨208486473728,545342019⟩ (N (N E ⟨208490665976,570238907⟩ E) ⟨208490668032,547653775⟩ E)) ⟨208492765184,548811460⟩ (N (N (N E ⟨208493810930,580878799⟩ E) ⟨208494861330,560924843⟩ E) ⟨208494862336,549970350⟩ (N E ⟨208496956389,585837184⟩ E))) ⟨208496956805,581022544⟩ (N (N (N (N E ⟨208496957781,569919390⟩ E) ⟨208496959220,554028504⟩ E) ⟨208499054592,574977269⟩ (N (N E ⟨208507441680,597568103⟩ E) ⟨208507441696,597377834⟩ E)) ⟨208507442112,592457325⟩ (N (N (N E ⟨208507442368,589454495⟩ E) ⟨208507442400,589080480⟩ E) ⟨208507442528,587587386⟩ (N E ⟨208507442944,582767396⟩ E))))) ⟨208507443208,579734184⟩ (N (N (N (N (N (N E ⟨208507443520,576174882⟩ E) ⟨208507445248,556948987⟩ E) ⟨208515833856,561625495⟩ (N (N E ⟨208524222464,566321264⟩ E) ⟨208526318288,582479258⟩ E)) ⟨208526318384,581379834⟩ (N (N (N E ⟨208526319216,571959347⟩ E) ⟨208527365394,600265737⟩ E) ⟨208527366514,587118310⟩ (N E ⟨208528416242,574564030⟩ E))) ⟨208528416768,568676368⟩ (N (N (N (N E ⟨208530513920,569855725⟩ E) ⟨208540996864,608601553⟩ E) ⟨208540997376,602461472⟩ (N (N E ⟨208540997952,595646169⟩ E) ⟨208540999104,582302317⟩ E)) ⟨208540999296,580114817⟩ (N (N (N E ⟨208543096832,576957128⟩ E) ⟨208544142594,610459168⟩ E) ⟨208553582592,582908030⟩ (N E ⟨208557773760,622612460⟩ E)))) ⟨208557775672,599519426⟩ (N (N (N (N (N E ⟨208559871984,610776372⟩ E) ⟨208559872752,601596430⟩ E) ⟨208559873344,594637728⟩ (N (N E ⟨208559873584,591845318⟩ E) ⟨208561971026,589694470⟩ E)) ⟨208561971200,587690386⟩ (N (N (N E ⟨208566164288,604332714⟩ E) ⟨208566165504,590088774⟩ E) ⟨208574550992,632626806⟩ (N E ⟨208574551408,627427090⟩ E))) ⟨208574551840,622083818⟩ (N (N (N (N E ⟨208574551872,621690288⟩ E) ⟨208574552416,615047647⟩ E) ⟨208574552904,609164156⟩ (N E ⟨208574552992,608110700⟩ E)) ⟨208574553024,607728189⟩ (N (N (N E ⟨208574554112,594899963⟩ E) ⟨208578748416,597312763⟩ E) ⟨208593428336,607504397⟩ (N E ⟨208593428480,605795377⟩ E))))))) ⟨208595523570,632119956⟩ (N (N (N (N (N (N (N (N E ⟨208596571604,639574873⟩ E) ⟨208597621876,619151338⟩ E) ⟨208599719936,609448784⟩ (N (N E ⟨208608107104,631946377⟩ E) ⟨208608107968,621306060⟩ E)) ⟨208608108224,618196465⟩ (N (N (N E ⟨208608108544,614336786⟩ E) ⟨208613348852,649458250⟩ E) ⟨208620691456,621704760⟩ (N E ⟨208624882688,663121061⟩ E))) ⟨208624883104,657671999⟩ (N (N (N (N E ⟨208624885760,624170340⟩ E) ⟨208629077923,653580061⟩ E) ⟨208629078034,652148216⟩ (N (N E ⟨208629078066,651736160⟩ E) ⟨208629078898,641136058⟩ E)) ⟨208629079154,637917924⟩ (N (N (N E ⟨208629079730,630750643⟩ E) ⟨208629080064,626640714⟩ E) ⟨208637468672,631595836⟩ (N E ⟨208641662688,637664528⟩ E)))) ⟨208641662976,634080582⟩ (N (N (N (N (N E ⟨208644806034,670266972⟩ E) ⟨208645855234,662691215⟩ E) ⟨208662634496,646576139⟩ (N (N E ⟨208664730117,667597718⟩ E) ⟨208664731572,648796046⟩ E)) ⟨208675214016,699384366⟩ (N (N (N E ⟨208675214848,687931165⟩ E) ⟨208675217152,657416077⟩ E) ⟨208675217408,654130900⟩ (N E ⟨208678360530,690553415⟩ E))) ⟨208683604644,677179243⟩ (N (N (N (N E ⟨208691994624,664270860⟩ E) ⟨208696186419,700565750⟩ E) ⟨208696186962,693084112⟩ (N (N E ⟨208696187730,682672088⟩ E) ⟨208696188850,667835944⟩ E)) ⟨208696188928,666817798⟩ (N (N (N E ⟨208698283989,696126289⟩ E) ⟨208700383232,669369514⟩ E) ⟨208708768848,715440878⟩ (N E ⟨208708771840,674487275⟩ E))))) ⟨208712964930,693369181⟩ (N (N (N (N (N (N E ⟨208712965762,682135042⟩ E) ⟨208712966144,677053318⟩ E) ⟨208725546080,726128035⟩ (N (N E ⟨208727646208,686072056⟩ E) ⟨208729742194,703265232⟩ E)) ⟨208729743026,691873420⟩ (N (N (N E ⟨208729743058,691439898⟩ E) ⟨208742325312,708354837⟩ E) ⟨208745469426,733325912⟩ (N E ⟨208745470546,717281705⟩ E))) ⟨208763297792,708217917⟩ (N (N (N (N E ⟨208771686400,713478734⟩ E) ⟨208775878192,752403944⟩ E) ⟨208775878624,746002415⟩ (N (N E ⟨208775878688,745059841⟩ E) ⟨208775879200,737572600⟩ E)) ⟨208775879232,737107778⟩ (N (N (N E ⟨208775880640,717013293⟩ E) ⟨208775880704,716116283⟩ E) ⟨208781121172,754380188⟩ (N E ⟨208796850386,756192744⟩ E)))) ⟨208797899380,750671930⟩ (N (N (N (N (N E ⟨208809432544,775981915⟩ E) ⟨208809432576,775490250⟩ E) ⟨208809433120,767191229⟩ (N (N E ⟨208809433152,766706517⟩ E) ⟨208809433984,754237345⟩ E)) ⟨208826212110,751689025⟩ (N (N (N E ⟨208826212352,748137812⟩ E) ⟨208830404850,777952209⟩ E) ⟨208830404882,777461208⟩ (N E ⟨208830405714,764830108⟩ E))) ⟨208830405970,760995317⟩ (N (N (N (N E ⟨208830406546,752454550⟩ E) ⟨208830406656,750837154⟩ E) ⟨208832503808,752188605⟩ (N E ⟨208834600960,753541242⟩ E)) ⟨208842987040,797675188⟩ (N (N (N E ⟨208842987168,795656588⟩ E) ⟨208842987552,789638990⟩ E) ⟨208842987584,789140096⟩ (N E ⟨208842988128,780718885⟩ E)))))) ⟨208842988160,780227027⟩ (N (N (N (N (N (N (N E ⟨208842988704,771924415⟩ E) ⟨208842989472,760390232⟩ E) ⟨208842989568,758963653⟩ (N (N E ⟨208847182050,789437862⟩ E) ⟨208847182818,777586696⟩ E)) ⟨208847183650,764997863⟩ (N (N (N E ⟨208847183872,761681973⟩ E) ⟨208855572480,767132840⟩ E) ⟨208859763936,814280446⟩ (N E ⟨208859766784,769865383⟩ E))) ⟨208861862032,800632076⟩ (N (N (N (N E ⟨208865008308,794138897⟩ E) ⟨208866056325,803650656⟩ E) ⟨208868155392,775344687⟩ (N (N E ⟨208872349696,778091444⟩ E) ⟨208876541168,825629288⟩ E)) ⟨208876541584,818852890⟩ (N (N (N E ⟨208876542016,811889302⟩ E) ⟨208876542592,802719289⟩ E) ⟨208876544000,780842937⟩ (N E ⟨208878639296,811268926⟩ E)))) ⟨208893321144,793012279⟩ (N (N (N (N (N E ⟨208897513219,831460539⟩ E) ⟨208897514546,809990402⟩ E) ⟨208897515520,794671403⟩ (N (N E ⟨208901709760,798450179⟩ E) ⟨208901709824,797451289⟩ E)) ⟨208910095632,848545269⟩ (N (N (N E ⟨208910097280,821374484⟩ E) ⟨208910097544,817123528⟩ E) ⟨208910098376,803905296⟩ (N E ⟨208910098432,803025244⟩ E))) ⟨208918487040,808618104⟩ (N (N (N (N E ⟨208926873280,853054375⟩ E) ⟨208931069010,832269615⟩ E) ⟨208931069842,818802832⟩ (N E ⟨208943649728,878140498⟩ E)) ⟨208943650144,870922273⟩ (N (N (N E ⟨208943650560,863778082⟩ E) ⟨208943652864,825510025⟩ E) ⟨208945749184,840518329⟩ (N E ⟨208947845984,847803040⟩ E))))) ⟨208960430080,836865670⟩ (N (N (N (N (N (N E ⟨208964624384,839716367⟩ E) ⟨208966720948,850885971⟩ E) ⟨208968818688,842571775⟩ (N (N E ⟨208975109244,861934796⟩ E) ⟨208977207296,848296723⟩ E)) ⟨208981401600,851166260⟩ (N (N (N E ⟨208982448948,872653712⟩ E) ⟨209000275968,864137416⟩ E) ⟨209010759024,919029150⟩ (N E ⟨209010760672,889615174⟩ E))) ⟨209010761536,874664397⟩ (N (N (N (N E ⟨209010761728,871384765⟩ E) ⟨209012858048,887185441⟩ E) ⟨209027536672,923392049⟩ (N (N E ⟨209027538944,883041609⟩ E) ⟨209028585200,925034302⟩ E)) ⟨209029636096,884503998⟩ (N (N (N E ⟨209031733248,885967560⟩ E) ⟨209032779636,925678655⟩ E) ⟨209033830400,887432295⟩ (N E ⟨209044315488,906629974⟩ E)))) ⟨209044316160,894773569⟩ (N (N (N (N (N E ⟨209049557876,919201950⟩ E) ⟨209061090720,955240290⟩ E) ⟨209065286672,927697104⟩ (N (N E ⟨209065287680,909544038⟩ E) ⟨209077868368,959520359⟩ E)) ⟨209077868800,951368237⟩ (N (N (N E ⟨209077868864,950167891⟩ E) ⟨209077869376,940632975⟩ E) ⟨209077869952,930048746⟩ (N E ⟨209094647808,930419398⟩ E))) ⟨209103036416,936425887⟩ (N (N (N (N E ⟨209111422048,999357541⟩ E) ⟨209111422464,991149420⟩ E) ⟨209111422880,983025420⟩ (N E ⟨209111423296,974984507⟩ E)) ⟨209111423328,974369387⟩ (N (N (N E ⟨209111423872,963986209⟩ E) ⟨209111424160,958545232⟩ E) ⟨209111424416,953741008⟩ (N E ⟨209111424448,953142598⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab15 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨209130297840,985653816⟩ E) ⟨209132394451,997815959⟩ E) ⟨209134493300,966580534⟩ (N (N E ⟨209144977728,1000110383⟩ E) ⟨209144978304,988828653⟩ E)) ⟨209144979456,966738541⟩ (N (N (N E ⟨209151270148,985975074⟩ E) ⟨209161754112,1029580791⟩ E) ⟨209163852336,1009591828⟩ (N E ⟨209163853824,980531379⟩ E))) ⟨209168048128,983609261⟩ (N (N (N (N E ⟨209170145280,985149947⟩ E) ⟨209178531344,1042217761⟩ E) ⟨209178532192,1024897850⟩ (N (N E ⟨209178532768,1013338319⟩ E) ⟨209178533344,1001941343⟩ E)) ⟨209178533888,991324325⟩ (N (N (N E ⟨209182728192,994418491⟩ E) ⟨209195311104,1003728883⟩ E) ⟨209197407536,1019565343⟩ (N E ⟨209200552948,1028296830⟩ E)))) ⟨209201602560,1008399761⟩ (N (N (N (N (N E ⟨209212087456,1033561476⟩ E) ⟨209212088320,1016207776⟩ E) ⟨209217329204,1060934203⟩ (N (N E ⟨209228863456,1071694852⟩ E) ⟨209228865536,1028760925⟩ E)) ⟨209230962000,1044315794⟩ (N (N (N E ⟨209230962688,1030335285⟩ E) ⟨209233059840,1031910804⟩ E) ⟨209237254144,1035065318⟩ (N E ⟨209245642752,1041388244⟩ E))) ⟨209247739200,1057455807⟩ (N (N (N (N E ⟨209247739904,1042971870⟩ E) ⟨209249837056,1044556654⟩ E) ⟨209258225664,1050907358⟩ (N (N E ⟨209262419968,1054089651⟩ E) ⟨209264517120,1055682532⟩ E)) ⟨209279195200,1109283685⟩ (N (N (N E ⟨209295974400,1079714391⟩ E) ⟨209300166771,1124862602⟩ E) ⟨209302265588,1090254927⟩ (N E ⟨209312749200,1145825076⟩ E))))) ⟨209312751616,1092637553⟩ (N (N (N (N (N (N E ⟨209329526432,1159087578⟩ E) ⟨209329526848,1149594557⟩ E) ⟨209333721251,1150733502⟩ (N (N E ⟨209335820288,1110527296⟩ E) ⟨209342110936,1133231736⟩ E)) ⟨209342111744,1115430485⟩ (N (N (N E ⟨209363083264,1131849164⟩ E) ⟨209365179120,1162687306⟩ E) ⟨209367277568,1135146684⟩ (N E ⟨209369374720,1136797166⟩ E))) ⟨209379858976,1179375340⟩ (N (N (N (N E ⟨209379859552,1166086009⟩ E) ⟨209379859584,1165353217⟩ E) ⟨209379860128,1152983382⟩ (N (N E ⟨209379860480,1145066785⟩ E) ⟨209385102516,1168378356⟩ E)) ⟨209396637696,1158357798⟩ (N (N (N E ⟨209398734848,1160024330⟩ E) ⟨209399782002,1193710069⟩ E) ⟨209421803520,1178431732⟩ (N E ⟨209430192128,1185159642⟩ E)))) ⟨209432288816,1197675595⟩ (N (N (N (N (N E ⟨209434386432,1188530452⟩ E) ⟨209446967936,1232252630⟩ E) ⟨209446968512,1218373997⟩ (N (N E ⟨209446969088,1204690255⟩ E) ⟨209446969344,1198670290⟩ E)) ⟨209451163648,1202059367⟩ (N (N (N E ⟨209465843712,1213957057⟩ E) ⟨209470037940,1219177712⟩ E) ⟨209480521936,1271034473⟩ (N E ⟨209480522368,1260256092⟩ E))) ⟨209480522944,1246062060⟩ (N (N (N (N E ⟨209480523520,1232067349⟩ E) ⟨209501493987,1275422100⟩ E) ⟨209501494098,1272639379⟩ (N E ⟨209501494130,1271838563⟩ E)) ⟨209501494962,1251236740⟩ (N (N (N E ⟨209501495218,1244981794⟩ E) ⟨209501495296,1243083765⟩ E) ⟨209509883904,1249984866⟩ (N E ⟨209514078208,1253442231⟩ E)))))) ⟨209526661120,1263841564⟩ (N (N (N (N (N (N (N E ⟨209530853632,1312721170⟩ E) ⟨209530855424,1267317083⟩ E) ⟨209537146880,1272538863⟩ (N (N E ⟨209547630912,1325493777⟩ E) ⟨209547632640,1281264491⟩ E)) ⟨209564409856,1295284358⟩ (N (N (N E ⟨209566507008,1297041931⟩ E) ⟨209568604160,1298800635⟩ E) ⟨209581187072,1309376586⟩ (N E ⟨209585381376,1312910939⟩ E))) ⟨209602158258,1335797449⟩ (N (N (N (N E ⟨209614739376,1394930504⟩ E) ⟨209617886610,1356885474⟩ E) ⟨209631517024,1397878040⟩ (N (N E ⟨209631518720,1352086458⟩ E) ⟨209635713024,1355674888⟩ E)) ⟨209648295840,1369035614⟩ (N (N (N E ⟨209648295872,1368178788⟩ E) ⟨209648295936,1366467147⟩ E) ⟨209652489186,1398682132⟩ (N E ⟨209665073152,1380919699⟩ E)))) ⟨209681849152,1429128134⟩ (N (N (N (N (N E ⟨209681849728,1413047240⟩ E) ⟨209681850304,1397191952⟩ E) ⟨209681850368,1395444015⟩ (N (N E ⟨209702820946,1440046549⟩ E) ⟨209702821778,1416745454⟩ E)) ⟨209702821888,1413700169⟩ (N (N (N E ⟨209715403648,1457262291⟩ E) ⟨209715404224,1440869955⟩ E) ⟨209715404800,1424707523⟩ (N E ⟨209719598882,1434603876⟩ E))) ⟨209719599104,1428385575⟩ (N (N (N (N E ⟨209732182016,1439446509⟩ E) ⟨209736374803,1486762678⟩ E) ⟨209748958080,1487486818⟩ (N (N E ⟨209748958656,1470754495⟩ E) ⟨209748959232,1454256844⟩ E)) ⟨209765734464,1527551459⟩ (N (N (N E ⟨209765736448,1469138422⟩ E) ⟨209769930752,1472869936⟩ E) ⟨209778319360,1480346296⟩ (N E ⟨209782512544,1517047834⟩ E))))) ⟨209782513120,1499985657⟩ (N (N (N (N (N (N E ⟨209782513608,1485717584⟩ E) ⟨209782513664,1484091138⟩ E) ⟨209801388032,1500997843⟩ (N (N E ⟨209803485074,1506119302⟩ E) ⟨209807679488,1506653363⟩ E)) ⟨209820262400,1517994294⟩ (N (N (N E ⟨209828649000,1586986117⟩ E) ⟨209834942352,1534634317⟩ E) ⟨209837039616,1533177468⟩ (N E ⟨209849622528,1544611238⟩ E))) ⟨209862205440,1556084718⟩ (N (N (N (N E ⟨209883176960,1575295307⟩ E) ⟨209899954176,1590742961⟩ E) ⟨209904148480,1594615858⟩ (N (N E ⟨209908342784,1598493144⟩ E) ⟨209912537088,1602374819⟩ E)) ⟨209916731392,1606260880⟩ (N (N (N E ⟨209933507200,1667287204⟩ E) ⟨209950285824,1637507063⟩ E) ⟨209967063040,1653235100⟩ (N E ⟨209971257344,1657178022⟩ E)))) ⟨209983840256,1669032948⟩ (N (N (N (N (N E ⟨209988034560,1672993305⟩ E) ⟨210003762354,1716100512⟩ E) ⟨210017394688,1700837617⟩ (N (N E ⟨210029977600,1712836052⟩ E) ⟨210042560512,1724873511⟩ E)) ⟨210050948864,1741623214⟩ (N (N (N E ⟨210050949120,1732920140⟩ E) ⟨210067726336,1749065303⟩ E) ⟨210084502720,1794297190⟩ (N E ⟨210084503296,1774145168⟩ E))) ⟨210084503552,1765279577⟩ (N (N (N (N E ⟨210103377920,1783603095⟩ E) ⟨210105475072,1785644424⟩ E) ⟨210109669376,1789730309⟩ (N E ⟨210118057984,1797914978⟩ E)) ⟨210120155136,1799963831⟩ (N (N (N E ⟨210126446592,1806116834⟩ E) ⟨210136932352,1816393302⟩ E) ⟨210168389632,1847383399⟩ (N E ⟨210176778240,1855688061⟩ E))))))) ⟨210185166848,1864009804⟩ (N (N (N (N (N (N (N (N E ⟨210233401344,1912190518⟩ E) ⟨210235498496,1914298085⟩ E) ⟨210252275712,1931196784⟩ (N (N E ⟨210285830144,1965197336⟩ E) ⟨210287927296,1967331347⟩ E)) ⟨210298413056,1978017213⟩ (N (N (N E ⟨210306801664,1986584866⟩ E) ⟨210310995968,1990875007⟩ E) ⟨210319384576,1999467908⟩ (N E ⟨210338258944,2018863381⟩ E))) ⟨210352939008,2034007473⟩ (N (N (N (N E ⟨210365521920,2047028947⟩ E) ⟨210386493440,2068814990⟩ E) ⟨210436825088,2121526376⟩ (N (N E ⟨210441019392,2125945986⟩ E) ⟨210453602304,2139229668⟩ E)) ⟨210457796608,2143665839⟩ (N (N (N E ⟨210461990912,2148106145⟩ E) ⟨210503933952,2192736161⟩ E) ⟨210508128256,2197221811⟩ (N E ⟨210520711168,2210703411⟩ E)))) ⟨210571042816,2264998498⟩ (N (N (N (N (N E ⟨210575237120,2269549642⟩ E) ⟨210587820032,2283227512⟩ E) ⟨210592014336,2287794941⟩ (N (N E ⟨210600402944,2296941997⟩ E) ⟨210633957376,2333692515⟩ E)) ⟨210642345984,2342920630⟩ (N (N (N E ⟨210654928896,2356793094⟩ E) ⟨210688483328,2393963621⟩ E) ⟨210705260544,2412645318⟩ (N E ⟨210726232064,2436087559⟩ E))) ⟨210772369408,2488011624⟩ (N (N (N (N E ⟨210776563712,2492755856⟩ E) ⟨210789146624,2507012350⟩ E) ⟨210801729536,2521304486⟩ (N (N E ⟨210839478272,2564394129⟩ E) ⟨210856255488,2583647426⟩ E)) ⟨210973696000,2720169542⟩ (N (N (N E ⟨210977890304,2725101561⟩ E) ⟨210990473216,2739920731⟩ E) ⟨211007250432,2759733463⟩ (N E ⟨211057582080,2819539367⟩ E))))) ⟨211065970688,2829560435⟩ (N (N (N (N (N (N E ⟨211086942208,2854679603⟩ E) ⟨211112108032,2884947646⟩ E) ⟨211124690944,2900132663⟩ (N (N E ⟨211141468160,2920432085⟩ E) ⟨211179216896,2966325346⟩ E)) ⟨211183411200,2971443304⟩ (N (N (N E ⟨211191799808,2981690414⟩ E) ⟨211195994112,2986819561⟩ E) ⟨211204382720,2997089025⟩ (N E ⟨211233742848,3033149175⟩ E))) ⟨211242131456,3043485426⟩ (N (N (N (N E ⟨211246325760,3048659097⟩ E) ⟨211258908672,3064202262⟩ E) ⟨211275685888,3084978072⟩ (N (N E ⟨211313434624,3131938408⟩ E) ⟨211376349184,3210862060⟩ E)) ⟨211397320704,3237351010⟩ (N (N (N E ⟨211409903616,3253287592⟩ E) ⟨211447652352,3301290973⟩ E) ⟨211506372608,3376536470⟩ (N E ⟨211510566912,3381937705⟩ E)))) ⟨211527344128,3403577882⟩ (N (N (N (N (N E ⟨211590258688,3485228063⟩ E) ⟨211611230208,3512618957⟩ E) ⟨211640590336,3551111462⟩ (N (N E ⟨211644784640,3556624176⟩ E) ⟨211648978944,3562140328⟩ E)) ⟨211669950464,3589772560⟩ (N (N (N E ⟨211774808064,3729209537⟩ E) ⟨211841916928,3819550789⟩ E) ⟨211850305536,3830903156⟩ (N E ⟨211858694144,3842268715⟩ E))) ⟨211862888448,3847956435⟩ (N (N (N (N E ⟨211909025792,3910737789⟩ E) ⟨211917414400,3922195036⟩ E) ⟨211946774528,3962397654⟩ (N E ⟨211976134656,4002758560⟩ E)) ⟨211992911872,4025892612⟩ (N (N (N E ⟨212047437824,4101430639⟩ E) ⟨212076797952,4142326492⟩ E) ⟨212093575168,4165764645⟩ (N E ⟨212110352384,4189252805⟩ E)))))) ⟨212118740992,4201015576⟩ (N (N (N (N (N (N (N E ⟨212127129600,4212790777⟩ E) ⟨212156489728,4254101506⟩ E) ⟨212181655552,4289630850⟩ (N (N E ⟨212244570112,4378934904⟩ E) ⟨212265541632,4408854180⟩ E)) ⟨212315873280,4480965631⟩ (N (N (N E ⟨212345233408,4523227946⟩ E) ⟨212391370752,4589930760⟩ E) ⟨212450091008,4675333033⟩ (N E ⟨212533977088,4798306513⟩ E))) ⟨212584308736,4872629004⟩ (N (N (N (N E ⟨212643028992,4959839855⟩ E) ⟨212701749248,5047581965⟩ E) ⟨212718526464,5072747449⟩ (N (N E ⟨212731109376,5091649409⟩ E) ⟨212752080896,5123205450⟩ E)) ⟨212802412544,5199206823⟩ (N (N (N E ⟨212831772672,5243713164⟩ E) ⟨212852744192,5275580288⟩ E) ⟨212986961920,5481017517⟩ (N E ⟨212999544832,5500406795⟩ E)))) ⟨213133762560,5708564424⟩ (N (N (N (N (N E ⟨213171511296,5767540392⟩ E) ⟨213339283456,6031855592⟩ E) ⟨213607718912,6461782864⟩ (N (N E ⟨213683216384,6584148680⟩ E) ⟨214022955008,7141861699⟩ E)) ⟨214077480960,7232362537⟩ (N (N (N E ⟨214480134144,7907901185⟩ E) ⟨214748569648,8356336171⟩ E) ⟨214748569650,8356009412⟩ (N E ⟨214748569652,8355682670⟩ E))) ⟨214748569654,8355355943⟩ (N (N (N (N E ⟨214748569664,8353722550⟩ E) ⟨214748569676,8351763005⟩ E) ⟨214748569716,8345235339⟩ (N E ⟨214748569728,8343278283⟩ E)) ⟨214748569744,8340669767⟩ (N (N (N E ⟨214748569746,8340343774⟩ E) ⟨214748569760,8338062271⟩ E) ⟨214748569776,8335455795⟩ (N E ⟨214748569780,8334804335⟩ E))))) ⟨214748569788,8333501606⟩ (N (N (N (N (N (N E ⟨214748569792,8332850337⟩ E) ⟨214748569812,8329594946⟩ E) ⟨214748569814,8329269494⟩ (N (N E ⟨214748569824,8327642475⟩ E) ⟨214748569842,8324714841⟩ E)) ⟨214748569844,8324389628⟩ (N (N (N E ⟨214748569852,8323088934⟩ E) ⟨214748569856,8322438682⟩ E) ⟨214748569874,8319513335⟩ (N E ⟨214748569904,8314640613⟩ E))) ⟨214748569908,8313991187⟩ (N (N (N (N E ⟨214748569920,8312043287⟩ E) ⟨214748569984,8301664123⟩ E) ⟨214748570012,8297128334⟩ (N (N E ⟨214748570028,8294537846⟩ E) ⟨214748570032,8293890382⟩ E)) ⟨214748570034,8293566674⟩ (N (N (N E ⟨214748570036,8293242981⟩ E) ⟨214748570044,8291948369⟩ E) ⟨214748570048,8291301158⟩ (N E ⟨214748570066,8288389489⟩ E)))) ⟨214748570068,8288066049⟩ (N (N (N (N (N E ⟨214748570080,8286125741⟩ E) ⟨214748570112,8280954363⟩ E) ⟨214748570144,8275787019⟩ (N (N E ⟨214748570152,8274495813⟩ E) ⟨214748570164,8272559476⟩ E)) ⟨214748570176,8270623706⟩ (N (N (N E ⟨214748570210,8265142098⟩ E) ⟨214748570222,8263208498⟩ E) ⟨214748570240,8260309158⟩ (N E ⟨214748570258,8257411090⟩ E))) ⟨214748570284,8253227235⟩ (N (N (N (N E ⟨214748570288,8252583800⟩ E) ⟨214748570294,8251618766⟩ E) ⟨214748570304,8250010689⟩ (N E ⟨214748570348,8242939802⟩ E)) ⟨214748570354,8241976178⟩ (N (N (N E ⟨214748570356,8241655001⟩ E) ⟨214748570368,8239728268⟩ E) ⟨214748570380,8237802098⟩ (N E ⟨214748570384,8237160167⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab16 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨214748570400,8234593066⟩ E) ⟨214748570416,8232026966⟩ E) ⟨214748570428,8230103047⟩ (N (N E ⟨214748570432,8229461866⟩ E) ⟨214748570454,8225936484⟩ E)) ⟨214748570456,8225616088⟩ (N (N (N E ⟨214748570464,8224334662⟩ E) ⟨214748570484,8221132188⟩ E) ⟨214748570496,8219211452⟩ (N E ⟨214748570500,8218571331⟩ E))) ⟨214748570504,8217931273⟩ (N (N (N (N E ⟨214748570544,8211534116⟩ E) ⟨214748570560,8208976997⟩ E) ⟨214748570572,8207059811⟩ (N (N E ⟨214748570578,8206101428⟩ E) ⟨214748570608,8201311611⟩ E)) ⟨214748570656,8193655172⟩ (N (N (N E ⟨214748570672,8191105012⟩ E) ⟨214748570674,8190786311⟩ E) ⟨214748570676,8190467627⟩ (N E ⟨214748570688,8188555844⟩ E)))) ⟨214748570704,8186007668⟩ (N (N (N (N (N E ⟨214748570736,8180914290⟩ E) ⟨214748570752,8178369086⟩ E) ⟨214748570768,8175824873⟩ (N (N E ⟨214748570792,8172010409⟩ E) ⟨214748570800,8170739415⟩ E)) ⟨214748570802,8170421705⟩ (N (N (N E ⟨214748570816,8168198169⟩ E) ⟨214748570832,8165657911⟩ E) ⟨214748570864,8160580358⟩ (N E ⟨214748570868,8159945941⟩ E))) ⟨214748570898,8155189782⟩ (N (N (N (N E ⟨214748570944,8147903735⟩ E) ⟨214748570948,8147270550⟩ E) ⟨214748570976,8142839980⟩ (N (N E ⟨214748570992,8140309578⟩ E) ⟨214748570996,8139677132⟩ E)) ⟨214748571008,8137780160⟩ (N (N (N E ⟨214748571024,8135251724⟩ E) ⟨214748571026,8134935738⟩ E) ⟨214748571056,8130197797⟩ (N E ⟨214748571060,8129566333⟩ E))))) ⟨214748571072,8127672307⟩ (N (N (N (N (N (N E ⟨214748571100,8123255057⟩ E) ⟨214748571120,8120101717⟩ E) ⟨214748571136,8117580146⟩ (N (N E ⟨214748571186,8109706546⟩ E) ⟨214748571188,8109391800⟩ E)) ⟨214748571200,8107503649⟩ (N (N (N E ⟨214748571204,8106874387⟩ E) ⟨214748571216,8104986969⟩ E) ⟨214748571232,8102471265⟩ (N E ⟨214748571236,8101842492⟩ E))) ⟨214748571248,8099956538⟩ (N (N (N (N E ⟨214748571252,8099328009⟩ E) ⟨214748571264,8097442786⟩ E) ⟨214748571328,8087397529⟩ (N (N E ⟨214748571344,8084888649⟩ E) ⟨214748571360,8082380743⟩ E)) ⟨214748571376,8079873809⟩ (N (N (N E ⟨214748571392,8077367847⟩ E) ⟨214748571400,8076115231⟩ E) ⟨214748571410,8074549802⟩ (N E ⟨214748571424,8072358839⟩ E)))) ⟨214748571440,8069855791⟩ (N (N (N (N (N E ⟨214748571444,8069230181⟩ E) ⟨214748571456,8067353713⟩ E) ⟨214748571472,8064852606⟩ (N (N E ⟨214748571504,8059853298⟩ E) ⟨214748571506,8059540970⟩ E)) ⟨214748571516,8057979557⟩ (N (N (N E ⟨214748571520,8057355097⟩ E) ⟨214748571564,8050490036⟩ E) ⟨214748571580,8047995463⟩ (N E ⟨214748571584,8047371971⟩ E))) ⟨214748571604,8044255416⟩ (N (N (N (N E ⟨214748571628,8040517541⟩ E) ⟨214748571632,8039894774⟩ E) ⟨214748571636,8039272066⟩ (N E ⟨214748571648,8037404305⟩ E)) ⟨214748571708,8028073634⟩ (N (N (N E ⟨214748571712,8027452071⟩ E) ⟨214748571760,8019998005⟩ E) ⟨214748571764,8019377224⟩ (N E ⟨214748571772,8018135841⟩ E)))))) ⟨214748571776,8017515240⟩ (N (N (N (N (N (N (N E ⟨214748571788,8015653797⟩ E) ⟨214748571796,8014413135⟩ E) ⟨214748571816,8011312530⟩ (N (N E ⟨214748571828,8009452887⟩ E) ⟨214748571840,8007593784⟩ E)) ⟨214748571884,8000781686⟩ (N (N (N E ⟨214748571904,7997687674⟩ E) ⟨214748571908,7997069051⟩ E) ⟨214748571948,7990886110⟩ (N E ⟨214748571952,7990268145⟩ E))) ⟨214748571956,7989650239⟩ (N (N (N (N E ⟨214748571968,7987796881⟩ E) ⟨214748572016,7980388822⟩ E) ⟨214748572032,7977921378⟩ (N (N E ⟨214748572044,7976071420⟩ E) ⟨214748572048,7975454887⟩ E)) ⟨214748572092,7968676953⟩ (N (N (N E ⟨214748572096,7968061135⟩ E) ⟨214748572112,7965598455⟩ E) ⟨214748572144,7960675951⟩ (N E ⟨214748572160,7958216125⟩ E)))) ⟨214748572164,7957601317⟩ (N (N (N (N (N E ⟨214748572208,7950842346⟩ E) ⟨214748572224,7948386319⟩ E) ⟨214748572236,7946544921⟩ (N (N E ⟨214748572272,7941023925⟩ E) ⟨214748572288,7938571689⟩ E)) ⟨214748572328,7932445239⟩ (N (N (N E ⟨214748572332,7931832920⟩ E) ⟨214748572336,7931220659⟩ E) ⟨214748572338,7930914551⟩ (N E ⟨214748572352,7928772207⟩ E))) ⟨214748572368,7926324700⟩ (N (N (N (N E ⟨214748572400,7921432520⟩ E) ⟨214748572404,7920821263⟩ E) ⟨214748572424,7917765862⟩ (N (N E ⟨214748572456,7912880285⟩ E) ⟨214748572464,7911659479⟩ E)) ⟨214748572480,7909218575⟩ (N (N (N E ⟨214748572528,7901901510⟩ E) ⟨214748572544,7899464369⟩ E) ⟨214748572560,7897028168⟩ (N E ⟨214748572562,7896723709⟩ E))))) ⟨214748572592,7892158584⟩ (N (N (N (N (N (N E ⟨214748572596,7891550149⟩ E) ⟨214748572608,7889725199⟩ E) ⟨214748572652,7883038228⟩ (N (N E ⟨214748572660,7881823176⟩ E) ⟨214748572668,7880608358⟩ E)) ⟨214748572672,7880001038⟩ (N (N (N E ⟨214748572736,7870291856⟩ E) ⟨214748572784,7863019785⟩ E) ⟨214748572800,7860597628⟩ (N E ⟨214748572816,7858176404⟩ E))) ⟨214748572852,7852732059⟩ (N (N (N (N E ⟨214748572864,7850918325⟩ E) ⟨214748572928,7841253920⟩ E) ⟨214748572960,7836427295⟩ (N (N E ⟨214748572972,7834618269⟩ E) ⟨214748572992,7831604385⟩ E)) ⟨214748573008,7829194321⟩ (N (N (N E ⟨214748573024,7826785185⟩ E) ⟨214748573040,7824376975⟩ E) ⟨214748573056,7821969692⟩ (N E ⟨214748573064,7820766398⟩ E)))) ⟨214748573112,7813551490⟩ (N (N (N (N (N E ⟨214748573144,7808746175⟩ E) ⟨214748573160,7806344903⟩ E) ⟨214748573164,7805744729⟩ (N (N E ⟨214748573244,7793753361⟩ E) ⟨214748573248,7793154397⟩ E)) ⟨214748573280,7788364760⟩ (N (N (N E ⟨214748573292,7786569595⟩ E) ⟨214748573296,7785971321⟩ E) ⟨214748573300,7785373105⟩ (N E ⟨214748573312,7783578802⟩ E))) ⟨214748573356,7777004113⟩ (N (N (N (N E ⟨214748573376,7774017913⟩ E) ⟨214748573424,7766856881⟩ E) ⟨214748573440,7764471704⟩ (N E ⟨214748573452,7762683421⟩ E)) ⟨214748573480,7758512765⟩ (N (N (N E ⟨214748573492,7756726198⟩ E) ⟨214748573500,7755535440⟩ E) ⟨214748573504,7754940146⟩ (N E ⟨214748573612,7738888793⟩ E))))))) ⟨214748573632,7735920880⟩ (N (N (N (N (N (N (N (N E ⟨214748573680,7728803693⟩ E) ⟨214748573696,7726433117⟩ E) ⟨214748573708,7724655782⟩ (N (N E ⟨214748573728,7721694692⟩ E) ⟨214748573744,7719326842⟩ E)) ⟨214748573756,7717551550⟩ (N (N (N E ⟨214748573760,7716959899⟩ E) ⟨214748573776,7714593864⟩ E) ⟨214748573784,7713411187⟩ (N E ⟨214748573808,7709864514⟩ E))) ⟨214748573824,7707501199⟩ (N (N (N (N E ⟨214748573840,7705138789⟩ E) ⟨214748573888,7698056990⟩ E) ⟨214748573936,7690983326⟩ (N (N E ⟨214748573952,7688627245⟩ E) ⟨214748573984,7683917788⟩ E)) ⟨214748574000,7681564413⟩ (N (N (N E ⟨214748574016,7679211938⟩ E) ⟨214748574032,7676860364⟩ E) ⟨214748574064,7672159917⟩ (N E ⟨214748574068,7671572614⟩ E)))) ⟨214748574080,7669811042⟩ (N (N (N (N (N E ⟨214748574096,7667463067⟩ E) ⟨214748574192,7653394073⟩ E) ⟨214748574208,7651052380⟩ (N (N E ⟨214748574260,7643448061⟩ E) ⟨214748574264,7642863504⟩ E)) ⟨214748574272,7641694560⟩ (N (N (N E ⟨214748574288,7639357341⟩ E) ⟨214748574320,7634685584⟩ E) ⟨214748574324,7634101866⟩ (N E ⟨214748574332,7632934597⟩ E))) ⟨214748574336,7632351046⟩ (N (N (N (N E ⟨214748574380,7625935664⟩ E) ⟨214748574400,7623021811⟩ E) ⟨214748574448,7616034240⟩ (N (N E ⟨214748574452,7615452304⟩ E) ⟨214748574512,7606729932⟩ E)) ⟨214748574516,7606148885⟩ (N (N (N E ⟨214748574532,7603825251⟩ E) ⟨214748574544,7602083107⟩ E) ⟨214748574576,7597439831⟩ (N E ⟨214748574580,7596859671⟩ E))))) ⟨214748574588,7595699517⟩ (N (N (N (N (N (N E ⟨214748574592,7595119523⟩ E) ⟨214748574636,7588743242⟩ E) ⟨214748574644,7587584638⟩ (N (N E ⟨214748574652,7586426254⟩ E) ⟨214748574656,7585847146⟩ E)) ⟨214748574700,7579480595⟩ (N (N (N E ⟨214748574704,7578902149⟩ E) ⟨214748574708,7578323758⟩ E) ⟨214748574772,7569077007⟩ (N E ⟨214748574848,7558114805⟩ E))) ⟨214748574892,7551777339⟩ (N (N (N (N E ⟨214748574900,7550625786⟩ E) ⟨214748574908,7549474453⟩ E) ⟨214748574912,7548898869⟩ (N (N E ⟨214748574956,7542571062⟩ E) ⟨214748574960,7541996136⟩ E)) ⟨214748574964,7541421264⟩ (N (N (N E ⟨214748574976,7539696979⟩ E) ⟨214748574984,7538547729⟩ E) ⟨214748575016,7533952919⟩ (N E ⟨214748575020,7533378814⟩ E)))) ⟨214748575040,7530509109⟩ (N (N (N (N (N E ⟨214748575088,7523627392⟩ E) ⟨214748575156,7513891747⟩ E) ⟨214748575232,7503029365⟩ (N (N E ⟨214748575296,7493897320⟩ E) ⟨214748575308,7492186609⟩ E)) ⟨214748575312,7491616480⟩ (N (N (N E ⟨214748575328,7489336509⟩ E) ⟨214748575344,7487057405⟩ E) ⟨214748575360,7484779168⟩ (N E ⟨214748575400,7479087366⟩ E))) ⟨214748575424,7475674883⟩ (N (N (N (N E ⟨214748575492,7466016746⟩ E) ⟨214748575536,7459775676⟩ E) ⟨214748575552,7457507814⟩ (N E ⟨214748575600,7450709396⟩ E)) ⟨214748575616,7448444979⟩ (N (N (N E ⟨214748575744,7430360584⟩ E) ⟨214748575872,7412331053⟩ E) ⟨214748575888,7410081209⟩ (N E ⟨214748575928,7404460335⟩ E)))))) ⟨214748575976,7397722320⟩ (N (N (N (N (N (N (N E ⟨214748575984,7396600063⟩ E) ⟨214748575996,7394917077⟩ E) ⟨214748576000,7394356188⟩ (N (N E ⟨214748576032,7389870989⟩ E) ⟨214748576064,7385389192⟩ E)) ⟨214748576096,7380910793⟩ (N (N (N E ⟨214748576128,7376435789⟩ E) ⟨214748576136,7375317568⟩ E) ⟨214748576184,7368612691⟩ (N E ⟨214748576240,7360799963⟩ E))) ⟨214748576256,7358569658⟩ (N (N (N (N E ⟨214748576316,7350213535⟩ E) ⟨214748576320,7349656882⟩ E) ⟨214748576352,7345205555⟩ (N (N E ⟨214748576360,7344093250⟩ E) ⟨214748576364,7343537177⟩ E)) ⟨214748576372,7342425188⟩ (N (N (N E ⟨214748576384,7340757599⟩ E) ⟨214748576392,7339646136⟩ E) ⟨214748576440,7332981776⟩ (N E ⟨214748576472,7328543072⟩ E)))) ⟨214748576512,7322999415⟩ (N (N (N (N (N E ⟨214748576544,7318568264⟩ E) ⟨214748576564,7315800497⟩ E) ⟨214748576572,7314693756⟩ (N (N E ⟨214748576576,7314140465⟩ E) ⟨214748576620,7308057708⟩ E)) ⟨214748576628,7306952432⟩ (N (N (N E ⟨214748576640,7305294910⟩ E) ⟨214748576684,7299221349⟩ E) ⟨214748576704,7296462727⟩ (N E ⟨214748576748,7290398344⟩ E))) ⟨214748576752,7289847349⟩ (N (N (N (N E ⟨214748576816,7281038507⟩ E) ⟨214748576820,7280488397⟩ E) ⟨214748576896,7270046162⟩ (N (N E ⟨214748576940,7264009215⟩ E) ⟨214748576960,7261267221⟩ E)) ⟨214748577004,7255239387⟩ (N (N (N E ⟨214748577008,7254691713⟩ E) ⟨214748577024,7252501531⟩ E) ⟨214748577068,7246482793⟩ (N E ⟨214748577080,7244842403⟩ E))))) ⟨214748577132,7237739408⟩ (N (N (N (N (N (N E ⟨214748577136,7237193385⟩ E) ⟨214748577152,7235009806⟩ E) ⟨214748577216,7226283724⟩ (N (N E ⟨214748577264,7219747796⟩ E) ⟨214748577280,7217570796⟩ E)) ⟨214748577324,7211588276⟩ (N (N (N E ⟨214748577336,7209957756⟩ E) ⟨214748577388,7202897493⟩ E) ⟨214748577392,7202354754⟩ (N E ⟨214748577404,7200726844⟩ E))) ⟨214748577452,7194219801⟩ (N (N (N (N E ⟨214748577520,7185014071⟩ E) ⟨214748577536,7182850157⟩ E) ⟨214748577592,7175282874⟩ (N (N E ⟨214748577632,7169883774⟩ E) ⟨214748577648,7167725556⟩ E)) ⟨214748577652,7167186128⟩ (N (N (N E ⟨214748577660,7166107426⟩ E) ⟨214748577664,7165568150⟩ E) ⟨214748577708,7159639470⟩ (N E ⟨214748577728,7156946642⟩ E)))) ⟨214748577772,7151026878⟩ (N (N (N (N (N E ⟨214748577792,7148338100⟩ E) ⟨214941515776,7430534959⟩ E) ⟨214975070208,7479747351⟩ (N (N E ⟨217785253888,11551972317⟩ E) ⟨218271793152,12205051124⟩ E)) ⟨219446198272,13651975337⟩ (N (N (N E ⟨220738043904,14968078744⟩ E) ⟨221191028736,15347203445⟩ E) ⟨223338512436,16444306165⟩ (N E ⟨223338512496,16424286405⟩ E))) ⟨223338512512,16418769270⟩ (N (N (N (N E ⟨223338512576,16395951169⟩ E) ⟨223338512620,16379569867⟩ E) ⟨223338512640,16371937440⟩ (N E ⟨223338512648,16368851904⟩ E)) ⟨223338512684,16354737045⟩ (N (N (N E ⟨223338512688,16353145525⟩ E) ⟨223338512704,16346733102⟩ E) ⟨223338512832,16292773527⟩ (N E ⟨223338512880,16271325063⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab17 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨223338513024,16203039755⟩ E) ⟨223338513136,16145876113⟩ E) ⟨223338513260,16078495271⟩ (N (N E ⟨223338513268,16074001499⟩ E) ⟨223338513344,16030429901⟩ E)) ⟨223338513456,15963332136⟩ (N (N (N E ⟨223338513460,15960872564⟩ E) ⟨223338513520,15923458807⟩ E) ⟨223338513524,15920929959⟩ (N E ⟨223338513580,15885073860⟩ E))) ⟨223338513592,15877280860⟩ (N (N (N (N E ⟨223338513640,15845723799⟩ E) ⟨223338513648,15840404536⟩ E) ⟨223338513664,15829714926⟩ (N (N E ⟨223338513716,15794504608⟩ E) ⟨223338513744,15775249101⟩ E)) ⟨223338513776,15752990065⟩ (N (N (N E ⟨223338513792,15741759742⟩ E) ⟨223338513848,15701926500⟩ E) ⟨223338513896,15667134158⟩ (N E ⟨223338513904,15661277398⟩ E)))) ⟨223338513920,15649514276⟩ (N (N (N (N (N E ⟨223338513952,15625790073⟩ E) ⟨223338513984,15601802787⟩ E) ⟨223338514016,15577553457⟩ (N (N E ⟨223338514024,15571450303⟩ E) ⟨223338514028,15568392614⟩ E)) ⟨223338514048,15553043132⟩ (N (N (N E ⟨223338514056,15546874894⟩ E) ⟨223338514160,15465217013⟩ E) ⟨223338514176,15452413173⟩ (N E ⟨223338514280,15367636688⟩ E))) ⟨223338514284,15364322650⟩ (N (N (N (N E ⟨223338514304,15347693469⟩ E) ⟨223338514348,15310764305⟩ E) ⟨223338514360,15300610688⟩ (N (N E ⟨223338514408,15259646416⟩ E) ⟨223338514604,15086639292⟩ E)) ⟨223338514736,14965029214⟩ (N (N (N E ⟨223338514744,14957529418⟩ E) ⟨223338514880,14827802700⟩ E) ⟨223338514928,14781021856⟩ (N E ⟨223338514944,14765314206⟩ E))))) ⟨223338515000,14709891570⟩ (N (N (N (N (N (N E ⟨223338515056,14653780647⟩ E) ⟨223338515184,14522980056⟩ E) ⟨223338515200,14506383906⟩ (N (N E ⟨223338515296,14405676172⟩ E) ⟨223338515312,14388704650⟩ E)) ⟨223338515328,14371680180⟩ (N (N (N E ⟨223338515440,14251040712⟩ E) ⟨223338515456,14233598825⟩ E) ⟨223338515564,14114530394⟩ (N E ⟨223338515584,14092227980⟩ E))) ⟨223338515884,13748512307⟩ (N (N (N (N E ⟨223338515904,13725001916⟩ E) ⟨223338515952,13668281922⟩ E) ⟨223338515976,13639766909⟩ (N (N E ⟨223338516096,13495666739⟩ E) ⟨223338516144,13437326711⟩ E)) ⟨223338516208,13358930536⟩ (N (N (N E ⟨223338516400,13119678245⟩ E) ⟨223338516464,13038613763⟩ E) ⟨223338516480,13018247744⟩ (N E ⟨223338516560,12915827976⟩ E)))) ⟨223338516712,12718592543⟩ (N (N (N (N (N E ⟨223338516920,12443354988⟩ E) ⟨223338516968,12379003573⟩ E) ⟨223338517096,12205939677⟩ (N (N E ⟨223338517120,12173259767⟩ E) ⟨223338517224,12030834160⟩ E)) ⟨223338517248,11997783053⟩ (N (N (N E ⟨223338517352,11853791487⟩ E) ⟨223338517376,11820388852⟩ E) ⟨223338517424,11753393144⟩ (N E ⟨223338517480,11674916825⟩ E))) ⟨223338517608,11494315974⟩ (N (N (N (N E ⟨223338517632,11460269768⟩ E) ⟨223338517680,11392009324⟩ E) ⟨223338517688,11380611106⟩ (N E ⟨223338518000,10931607019⟩ E)) ⟨223338518064,10838504302⟩ (N (N (N E ⟨223338518072,10826844437⟩ E) ⟨223338518248,10569158034⟩ E) ⟨223338518256,10557394293⟩ (N E ⟨223338518272,10533854239⟩ E)))))) ⟨223338518400,10344954523⟩ (N (N (N (N (N (N (N E ⟨223338518512,10178881781⟩ E) ⟨223338518528,10155101777⟩ E) ⟨223338518624,10012152067⟩ (N (N E ⟨223338518632,10000219583⟩ E) ⟨223338518768,9796936964⟩ E)) ⟨223338518784,9772971268⟩ (N (N (N E ⟨223338519040,9388330754⟩ E) ⟨223338519168,9195340124⟩ E) ⟨223338519280,9026221224⟩ (N E ⟨223338519424,8808558093⟩ E))) ⟨223338519536,8639179947⟩ (N (N (N (N E ⟨223338519552,8614981766⟩ E) ⟨223338519776,8276333427⟩ E) ⟨223338519808,8227993137⟩ (N (N E ⟨223338520040,7878061509⟩ E) ⟨223338520248,7565489698⟩ E)) ⟨223338520424,7302206258⟩ (N (N (N E ⟨223338520448,7266405248⟩ E) ⟨223338520552,7111581235⟩ E) ⟨223338520576,7075928778⟩ (N E ⟨224072523776,7162415271⟩ E)))) ⟨224848470016,7254214482⟩ (N (N (N (N (N E ⟨227750928384,7597272638⟩ E) ⟨228472348672,7681547271⟩ E) ⟨228556234752,7691300998⟩ (N (N E ⟨229042774016,7747656776⟩ E) ⟨229948743680,7851468519⟩ E)) ⟨230082961408,7866706880⟩ (N (N (N E ⟨230800187392,7947437827⟩ E) ⟨230972153856,7966607637⟩ E) ⟨231370612736,8010726372⟩ (N E ⟨231928455400,7690272903⟩ E))) ⟨231928455528,7481280369⟩ (N (N (N (N E ⟨231928455680,7234651425⟩ E) ⟨231928455912,6861845531⟩ E) ⟨231928455992,6734404292⟩ (N (N E ⟨231928456064,6620229385⟩ E) ⟨231928456296,6255915968⟩ E)) ⟨231928456320,6218556595⟩ (N (N (N E ⟨231928456448,6020404688⟩ E) ⟨231928456576,5824173145⟩ E) ⟨231928456768,5533636203⟩ (N E ⟨231928456928,5295216672⟩ E))))) ⟨231928457184,4921202122⟩ (N (N (N (N (N (N E ⟨231928457200,4898144275⟩ E) ⟨231928457440,4556984120⟩ E) ⟨231928457456,4534561469⟩ (N (N E ⟨231928457472,4512179917⟩ E) ⟨231928457648,4268741260⟩ E)) ⟨231928457696,4203243235⟩ (N (N (N E ⟨231928457728,4159794995⟩ E) ⟨231928457760,4116521886⟩ E) ⟨231928457856,3987765561⟩ (N E ⟨231928457960,3850108483⟩ E))) ⟨231928458344,3358962831⟩ (N (N (N (N E ⟨231928458472,3201467306⟩ E) ⟨231928458848,2757711661⟩ E) ⟨231928458856,2748584181⟩ (N (N E ⟨231928458928,2667038594⟩ E) ⟨231928459072,2507229055⟩ E)) ⟨231928459240,2326405216⟩ (N (N (N E ⟨231928459360,2201015601⟩ E) ⟨231928459624,1936444831⟩ E) ⟨231928459776,1791284529⟩ (N E ⟨231928460208,1408058229⟩ E)))) ⟨231928460288,1341936689⟩ (N (N (N (N (N E ⟨231928460440,1220542878⟩ E) ⟨231928461036,798958492⟩ E) ⟨231928461056,786333379⟩ (N (N E ⟨231928461084,768825680⟩ E) ⟨231928461112,751513515⟩ E)) ⟨231928461488,538057829⟩ (N (N (N E ⟨231928461560,501238058⟩ E) ⟨231928461740,414912132⟩ E) ⟨231928462056,283173964⟩ (N E ⟨231928462144,250984162⟩ E))) ⟨231928462568,123302443⟩ (N (N (N (N E ⟨231928462684,96257478⟩ E) ⟨231928462704,91935740⟩ E) ⟨231928462772,77991129⟩ (N E ⟨231928462836,65923119⟩ E)) ⟨231928462952,46654088⟩ (N (N (N E ⟨231928463240,13245868⟩ E) ⟨231928463360,5355706⟩ E) ⟨232264005884,503706529⟩ (N E ⟨232545026048,5958270⟩ E))))))) ⟨232716991020,366855452⟩ (N (N (N (N (N (N (N (N E ⟨233115450216,246525385⟩ E) ⟨234101112660,21568241⟩ E) ⟨234155638784,7477133⟩ (N (N E ⟨234327605248,7630701⟩ E) ⟨234671536948,277071942⟩ E)) ⟨235145493816,118737632⟩ (N (N (N E ⟨240518397960,10120304⟩ E) ⟨240518397976,8988499⟩ E) ⟨240518397996,7668239⟩ (N E ⟨240518398154,925015⟩ E))) ⟨240518398184,382972⟩ (N (N (N (N E ⟨240518398208,118725⟩ E) ⟨240820392352,412⟩ E) ⟨240820392928,408⟩ (N (N E ⟨240820392960,407⟩ E) ⟨240820393792,402⟩ E)) ⟨240820396032,387⟩ (N (N (N E ⟨240824587338,4094⟩ E) ⟨240825634180,5785⟩ E) ⟨240826685316,7274⟩ (N E ⟨240832978944,21843⟩ E)))) ⟨240835074122,29584⟩ (N (N (N (N (N E ⟨240841363395,58373⟩ E) ⟨240841363427,58341⟩ E) ⟨240841367552,54390⟩ (N (N E ⟨240842411524,64333⟩ E) ⟨240843462548,67216⟩ E)) ⟨240843463380,66273⟩ (N (N (N E ⟨240844508262,76636⟩ E) ⟨240844508694,76069⟩ E) ⟨240844509110,75528⟩ (N E ⟨240845558263,80927⟩ E))) ⟨240845558934,80004⟩ (N (N (N (N E ⟨240845558966,79961⟩ E) ⟨240853950464,130579⟩ E) ⟨240858144768,163276⟩ (N (N E ⟨240861285974,205407⟩ E) ⟨240862336134,209822⟩ E)) ⟨240862339072,199623⟩ (N (N (N E ⟨240868628586,269710⟩ E) ⟨240874918002,353721⟩ E) ⟨240874918770,349103⟩ (N E ⟨240874919634,343997⟩ E))))) ⟨240877014581,384254⟩ (N (N (N (N (N (N E ⟨240877014629,383937⟩ E) ⟨240877015045,381205⟩ E) ⟨240877017044,368412⟩ (N (N E ⟨240878062774,400773⟩ E) ⟨240878063190,397917⟩ E)) ⟨240878063606,395085⟩ (N (N (N E ⟨240879112743,405199⟩ E) ⟨240879113430,400471⟩ E) ⟨240879115988,383462⟩ (N E ⟨240879116288,381527⟩ E))) ⟨240892743076,620027⟩ (N (N (N (N E ⟨240893791381,640640⟩ E) ⟨240893791397,640464⟩ E) ⟨240895893504,621870⟩ (N (N E ⟨240904282112,763963⟩ E) ⟨240908473008,890551⟩ E)) ⟨240908474672,865656⟩ (N (N (N E ⟨240908476050,845696⟩ E) ⟨240908476416,840491⟩ E) ⟨240910568629,957364⟩ (N E ⟨240910570037,934510⟩ E)))) ⟨240910570708,923859⟩ (N (N (N (N (N E ⟨240910572340,898579⟩ E) ⟨240911617606,972563⟩ E) ⟨240912667239,976728⟩ (N (N E ⟨240912667926,965335⟩ E) ⟨240912669494,939946⟩ E)) ⟨240912669590,938419⟩ (N (N (N E ⟨240912670422,925313⟩ E) ⟨240912670720,920674⟩ E) ⟨240921057088,1134223⟩ (N E ⟨240921059328,1092006⟩ E))) ⟨240925253504,1185712⟩ (N (N (N (N E ⟨240925253632,1183156⟩ E) ⟨240926298132,1293081⟩ E) ⟨240928394422,1363936⟩ (N E ⟨240929446694,1305066⟩ E)) ⟨240933642240,1376424⟩ (N (N (N E ⟨240942029618,1617592⟩ E) ⟨240943074820,1742673⟩ E) ⟨240944123493,1769186⟩ (N E ⟨240944125116,1720703⟩ E)))))) ⟨240944125948,1696493⟩ (N (N (N (N (N (N (N E ⟨240945171654,1811731⟩ E) ⟨240945172502,1785529⟩ E) ⟨240946221671,1796875⟩ (N (N E ⟨240946223126,1752843⟩ E) ⟨240946223196,1750758⟩ E)) ⟨240946225152,1693753⟩ (N (N (N E ⟨240950414634,1961457⟩ E) ⟨240954613760,1923594⟩ E) ⟨240959852052,2243163⟩ (N E ⟨240960901252,2252323⟩ E))) ⟨240960902884,2190406⟩ (N (N (N (N E ⟨240960903748,2158488⟩ E) ⟨240961949286,2306981⟩ E) ⟨240967191866,2491561⟩ (N (N E ⟨240967193010,2443126⟩ E) ⟨240967193778,2411269⟩ E)) ⟨240967194610,2377342⟩ (N (N (N E ⟨240971390976,2427180⟩ E) ⟨240973486704,2555014⟩ E) ⟨240975585280,2562224⟩ (N E ⟨240976629252,2808199⟩ E)))) ⟨240976629428,2799720⟩ (N (N (N (N (N E ⟨240977677589,2857297⟩ E) ⟨240977678005,2836938⟩ E) ⟨240977678421,2816759⟩ (N (N E ⟨240977678516,2812177⟩ E) ⟨240977678548,2810635⟩ E)) ⟨240977678997,2789116⟩ (N (N (N E ⟨240977679380,2770922⟩ E) ⟨240977679668,2757339⟩ E) ⟨240977680500,2718564⟩ (N E ⟨240977681236,2684829⟩ E))) ⟨240979776135,2863803⟩ (N (N (N (N E ⟨240979776822,2830401⟩ E) ⟨240979779584,2700929⟩ E) ⟨240983969098,3084897⟩ (N E ⟨240988168060,2995979⟩ E)) ⟨240988168192,2989319⟩ (N (N (N E ⟨240992362432,3142394⟩ E) ⟨240992362496,3139005⟩ E) ⟨240993406196,3452062⟩ (N E ⟨240993406676,3423696⟩ E))))) ⟨240993407060,3401213⟩ (N (N (N (N (N (N E ⟨240993407092,3399347⟩ E) ⟨240994455716,3437416⟩ E) ⟨240994455748,3435531⟩ (N (N E ⟨240994456580,3386985⟩ E) ⟨240994456836,3372221⟩ E)) ⟨240994457412,3339294⟩ (N (N (N E ⟨240995503366,3534279⟩ E) ⟨240995504214,3483178⟩ E) ⟨240998652944,3428270⟩ (N E ⟨241011232853,4130101⟩ E))) ⟨241011232916,4125643⟩ (N (N (N (N E ⟨241011234676,4003507⟩ E) ⟨241011234900,3988288⟩ E) ⟨241011235732,3932392⟩ (N (N E ⟨241013334016,3942359⟩ E) ⟨241021718560,4596148⟩ E)) ⟨241021719136,4551031⟩ (N (N (N E ⟨241025916928,4468319⟩ E) ⟨241026961092,4865462⟩ E) ⟨241028009237,4951104⟩ (N E ⟨241029057878,4995226⟩ E)))) ⟨241029058294,4959643⟩ (N (N (N (N (N E ⟨241029058710,4924377⟩ E) ⟨241038499840,5027250⟩ E) ⟨241042694144,5220888⟩ (N (N E ⟨241044786469,5774734⟩ E) ⟨241044786885,5733589⟩ E)) ⟨241046888448,5418191⟩ (N (N (N E ⟨241055274208,6111919⟩ E) ⟨241055275872,5941466⟩ E) ⟨241055277056,5823791⟩ (N E ⟨241059471360,6032088⟩ E))) ⟨241061563717,6659715⟩ (N (N (N (N E ⟨241061563989,6628647⟩ E) ⟨241061564101,6615907⟩ E) ⟨241061564644,6554572⟩ (N E ⟨241061564676,6550979⟩ E)) ⟨241061565412,6469030⟩ (N (N (N E ⟨241061566532,6346769⟩ E) ⟨241062612710,6669370⟩ E) ⟨241065760294,6628700⟩ (N E ⟨241065761894,6451068⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab18 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨241078342373,7425860⟩ E) ⟨241078342612,7395597⟩ E) ⟨241078342676,7387519⟩ (N (N E ⟨241078343060,7339283⟩ E) ⟨241078343444,7291441⟩ E)) ⟨241078343540,7279541⟩ (N (N (N E ⟨241079389142,7721746⟩ E) ⟨241079389510,7672983⟩ E) ⟨241080442880,7128564⟩ (N E ⟨241088827088,8182971⟩ E))) ⟨241088827520,8122547⟩ (N (N (N (N E ⟨241088828096,8042847⟩ E) ⟨241088828672,7964122⟩ E) ⟨241088829504,7852101⟩ (N (N E ⟨241093025792,7830449⟩ E) ⟨241095118165,8624595⟩ E)) ⟨241095118485,8577288⟩ (N (N (N E ⟨241095119172,8476816⟩ E) ⟨241095119876,8375379⟩ E) ⟨241095120708,8257448⟩ (N E ⟨241095120836,8239489⟩ E)))) ⟨241095121604,8132758⟩ (N (N (N (N (N E ⟨241095121668,8123941⟩ E) ⟨241096166742,8690008⟩ E) ⟨241096166758,8687617⟩ (N (N E ⟨241096167174,8625736⟩ E) ⟨241097219120,8205894⟩ E)) ⟨241097220096,8071745⟩ (N (N (N E ⟨241099314758,8546836⟩ E) ⟨241099315526,8435944⟩ E) ⟨241105605556,9035256⟩ (N E ⟨241105606136,8946299⟩ E))) ⟨241107704624,8873856⟩ (N (N (N (N E ⟨241109803008,8817641⟩ E) ⟨241111895829,9629014⟩ E) ⟨241113993596,9664833⟩ (N (N E ⟨241113995414,9369754⟩ E) ⟨241113997312,9073610⟩ E)) ⟨241122381520,10342444⟩ (N (N (N E ⟨241122381952,10266074⟩ E) ⟨241122382528,10165341⟩ E) ⟨241122383104,10065841⟩ (N E ⟨241122383136,10060349⟩ E))))) ⟨241122383968,9918862⟩ (N (N (N (N (N (N E ⟨241128673604,10660090⟩ E) ⟨241128674372,10521026⟩ E) ⟨241130774528,10134173⟩ (N (N E ⟨241144401700,11879979⟩ E) ⟨241145449493,12118688⟩ E)) ⟨241145449925,12028934⟩ (N (N (N E ⟨241145450341,11943288⟩ E) ⟨241145450757,11858404⟩ E) ⟨241145450868,11835882⟩ (N E ⟨241145450900,11829399⟩ E))) ⟨241145451732,11662392⟩ (N (N (N (N E ⟨241145452852,11442201⟩ E) ⟨241145453588,11300331⟩ E) ⟨241146498870,12029791⟩ (N (N E ⟨241146499286,11944274⟩ E) ⟨241146499318,11937727⟩ E)) ⟨241146499862,11827117⟩ (N (N (N E ⟨241146499894,11820650⟩ E) ⟨241147549878,11614423⟩ E) ⟨241158035624,12370129⟩ (N E ⟨241158036784,12129333⟩ E)))) ⟨241160134656,12131444⟩ (N (N (N (N (N E ⟨241161178996,13117837⟩ E) ⟨241162227381,13241665⟩ E) ⟨241162228836,12915882⟩ (N (N E ⟨241162229188,12838577⟩ E) ⟨241162230532,12548682⟩ E)) ⟨241162230788,12494395⟩ (N (N (N E ⟨241168519826,13500556⟩ E) ⟨241168520594,13324687⟩ E) ⟨241168521426,13137382⟩ (N E ⟨241172717568,13042479⟩ E))) ⟨241174812624,13674213⟩ (N (N (N (N E ⟨241174813488,13475153⟩ E) ⟨241174813552,13460552⟩ E) ⟨241176911872,13353501⟩ (N E ⟨241177955764,14546630⟩ E)) ⟨241179003941,14732515⟩ (N (N (N E ⟨241179005189,14420064⟩ E) ⟨241179007028,13974593⟩ E) ⟨241181106176,13668194⟩ (N E ⟨241189494784,14308597⟩ E)))))) ⟨241191589056,15195229⟩ (N (N (N (N (N (N (N E ⟨241191589792,15005915⟩ E) ⟨241191590656,14787424⟩ E) ⟨241191590720,14771398⟩ (N (N E ⟨241193689088,14634307⟩ E) ⟨241195781557,16026496⟩ E)) ⟨241195781573,16022088⟩ (N (N (N E ⟨241196830614,15983209⟩ E) ⟨241197879127,16089408⟩ E) ⟨241201025369,16214117⟩ (N E ⟨241206272000,15633473⟩ E))) ⟨241208367984,16118166⟩ (N (N (N (N E ⟨241212558805,17475558⟩ E) ⟨241212559221,17351140⟩ E) ⟨241217802185,17790778⟩ (N (N E ⟨241223049216,17017120⟩ E) ⟨241227243520,17372216⟩ E)) ⟨241230384614,19088678⟩ (N (N (N E ⟨241233533192,18460572⟩ E) ⟨241233534024,18202040⟩ E) ⟨241233534224,18140569⟩ (N E ⟨241234579001,19452105⟩ E)))) ⟨241237725876,19363223⟩ (N (N (N (N (N E ⟨241244016515,20230593⟩ E) ⟨241244016563,20213939⟩ E) ⟨241244016947,20081322⟩ (N (N E ⟨241245064724,20459072⟩ E) ⟨241246113669,20430029⟩ E)) ⟨241246115028,19960488⟩ (N (N (N E ⟨241246115348,19851895⟩ E) ⟨241246115892,19668976⟩ E) ⟨241247161846,20671627⟩ (N E ⟨241247162246,20530112⟩ E))) ⟨241248213302,19775740⟩ (N (N (N (N E ⟨241248215040,19202810⟩ E) ⟨241251356233,21048570⟩ E) ⟨241256603648,19960770⟩ (N (N E ⟨241260796162,20970788⟩ E) ⟨241260797952,20345264⟩ E)) ⟨241262890501,22212602⟩ (N (N (N E ⟨241264992256,20733432⟩ E) ⟨241268133881,22546080⟩ E) ⟨241280716294,24032240⟩ (N E ⟨241281767766,22976395⟩ E))))) ⟨241281769472,22322862⟩ (N (N (N (N (N (N E ⟨241284912200,23808578⟩ E) ⟨241295396372,25578843⟩ E) ⟨241297493526,25803700⟩ (N (N E ⟨241297494390,25424080⟩ E) ⟨241297494422,25410155⟩ E)) ⟨241302738696,25359523⟩ (N (N (N E ⟨241306935296,24817292⟩ E) ⟨241311126072,26804499⟩ E) ⟨241311129600,25245899⟩ (N E ⟨241313222245,27491057⟩ E))) ⟨241313222645,27302946⟩ (N (N (N (N E ⟨241313222661,27295455⟩ E) ⟨241313223605,26858004⟩ E) ⟨241313224308,26537915⟩ (N (N E ⟨241313225044,26207895⟩ E) ⟨241314270806,27614982⟩ E)) ⟨241314271174,27441069⟩ (N (N (N E ⟨241314271222,27418486⟩ E) ⟨241315321430,26777350⟩ E) ⟨241315321462,26762762⟩ (N E ⟨241315322294,26386920⟩ E)))) ⟨241315323904,25678183⟩ (N (N (N (N (N E ⟨241319514570,27778586⟩ E) ⟨241323708736,28313063⟩ E) ⟨241323709312,28035476⟩ (N (N E ⟨241323712512,26553782⟩ E) ⟨241328951268,29077447⟩ E)) ⟨241329999413,29414028⟩ (N (N (N E ⟨241329999845,29196688⟩ E) ⟨241332098630,28626649⟩ E) ⟨241332101120,27444090⟩ (N E ⟨241336291386,29876721⟩ E))) ⟨241340489728,28349110⟩ (N (N (N (N E ⟨241342585904,29052612⟩ E) ⟨241343631762,30550323⟩ E) ⟨241343632338,30250906⟩ (N E ⟨241343632370,30234380⟩ E)) ⟨241345728484,31022897⟩ (N (N (N E ⟨241345728916,30794091⟩ E) ⟨241346776277,31568415⟩ E) ⟨241346776645,31369276⟩ (N E ⟨241346776661,31360653⟩ E))))))) ⟨241346778069,30613336⟩ (N (N (N (N (N (N (N (N E ⟨241348874742,31110918⟩ E) ⟨241348875894,30505079⟩ E) ⟨241348876694,30093020⟩ (N (N E ⟨241348878336,29268840⟩ E) ⟨241357263232,32169082⟩ E)) ⟨241357263808,31853776⟩ (N (N (N E ⟨241357266944,30203283⟩ E) ⟨241360408450,32832098⟩ E) ⟨241361459808,31431934⟩ (N E ⟨241361461248,30676022⟩ E))) ⟨241363553893,33377827⟩ (N (N (N (N E ⟨241364602870,33276705⟩ E) ⟨241364603350,33004167⟩ E) ⟨241364603894,32698655⟩ (N (N E ⟨241369847624,32850975⟩ E) ⟨241369848392,32425211⟩ E)) ⟨241374044160,32116310⟩ (N (N (N E ⟨241378238464,32603763⟩ E) ⟨241380333144,34253815⟩ E) ⟨241381379686,35599248⟩ (N E ⟨241382432768,33094895⟩ E)))) ⟨241386622666,36204191⟩ (N (N (N (N (N E ⟨241390817696,36286960⟩ E) ⟨241390821376,34088195⟩ E) ⟨241392916904,35294981⟩ (N (N E ⟨241392918064,34608668⟩ E) ⟨241395015680,34590364⟩ E)) ⟨241397108757,37342140⟩ (N (N (N E ⟨241397111172,35834910⟩ E) ⟨241397112004,35333321⟩ E) ⟨241398157318,37487438⟩ (N E ⟨241398157334,37477154⟩ E))) ⟨241398157350,37466873⟩ (N (N (N (N E ⟨241399206470,37254015⟩ E) ⟨241399207590,36548700⟩ E) ⟨241399208326,36094284⟩ (N (N E ⟨241399209984,35096212⟩ E) ⟨241403399898,38366601⟩ E)) ⟨241403400730,37823331⟩ (N (N (N E ⟨241405498228,37870729⟩ E) ⟨241407598592,36118945⟩ E) ⟨241409694768,36981498⟩ (N E ⟨241409694832,36941471⟩ E))))) ⟨241412837044,39642288⟩ (N (N (N (N (N (N E ⟨241412837844,39102272⟩ E) ⟨241412837876,39080864⟩ E) ⟨241413885621,39781805⟩ (N (N E ⟨241413886005,39520526⟩ E) ⟨241413886037,39498850⟩ E)) ⟨241413887700,38392536⟩ (N (N (N E ⟨241415984438,38937532⟩ E) ⟨241415985270,38389974⟩ E) ⟨241415985590,38181941⟩ (N E ⟨241420177130,40591237⟩ E))) ⟨241420178016,39979556⟩ (N (N (N (N E ⟨241424372128,40673104⟩ E) ⟨241424373280,39880767⟩ E) ⟨241424373312,39859035⟩ (N (N E ⟨241424374048,39363247⟩ E) ⟨241424374144,39299148⟩ E)) ⟨241429614228,41938288⟩ (N (N (N E ⟨241429614292,41892216⟩ E) ⟨241431711398,42213976⟩ E) ⟨241432764416,39275453⟩ (N E ⟨241436957320,40767857⟩ E)))) ⟨241441153024,40357060⟩ (N (N (N (N (N E ⟨241445343315,43790849⟩ E) ⟨241445343731,43479930⟩ E) ⟨241445343747,43468027⟩ (N (N E ⟨241445343779,43444233⟩ E) ⟨241445347328,40903383⟩ E)) ⟨241446391460,44263844⟩ (N (N (N E ⟨241448488630,44546671⟩ E) ⟨241448489030,44241961⟩ E) ⟨241449539318,43110224⟩ (N E ⟨241449539350,43086753⟩ E))) ⟨241449540182,42482075⟩ (N (N (N (N E ⟨241449541632,41453386⟩ E) ⟨241460027392,42844495⟩ E) ⟨241462124544,43125477⟩ (N E ⟨241465266326,46569364⟩ E)) ⟨241466316518,45448816⟩ (N (N (N E ⟨241466317286,44859534⟩ E) ⟨241466318848,43690200⟩ E) ⟨241478898322,48135543⟩ (N E ⟨241478901760,45406453⟩ E)))))) ⟨241479945940,49088040⟩ (N (N (N (N (N (N (N E ⟨241480994501,49256713⟩ E) ⟨241480994933,48892978⟩ E) ⟨241480994981,48852771⟩ (N (N E ⟨241480996660,47472001⟩ E) ⟨241480997396,46882127⟩ E)) ⟨241480997492,46805865⟩ (N (N (N E ⟨241482042710,49725642⟩ E) ⟨241483093782,47797857⟩ E) ⟨241483093788,47792977⟩ (N E ⟨241483096064,45985898⟩ E))) ⟨241491484672,47155829⟩ (N (N (N (N E ⟨241495674851,51215107⟩ E) ⟨241495675522,50629892⟩ E) ⟨241497771749,51758402⟩ (N (N E ⟨241497772133,51418534⟩ E) ⟨241497772149,51404433⟩ E)) ⟨241497775428,48613929⟩ (N (N (N E ⟨241497776128,48042939⟩ E) ⟨241499870630,50561108⟩ E) ⟨241499873280,48340482⟩ (N E ⟨241508261888,49539858⟩ E)))) ⟨241512452275,53596661⟩ (N (N (N (N (N E ⟨241512452691,53216275⟩ E) ⟨241512452818,53100821⟩ E) ⟨241512453650,52352155⟩ (N (N E ⟨241512453906,52124455⟩ E) ⟨241512455346,50866457⟩ E)) ⟨241512456192,50145066⟩ (N (N (N E ⟨241514548981,54335665⟩ E) ⟨241514550405,53027253⟩ E) ⟨241515597974,54111278⟩ (N E ⟨241515598966,53200992⟩ E))) ⟨241516650496,50753955⟩ (N (N (N (N E ⟨241525036096,54703744⟩ E) ⟨241525037440,53466515⟩ E) ⟨241525038304,52689597⟩ (N E ⟨241529229347,56362421⟩ E)) ⟨241529230018,55718565⟩ (N (N (N E ⟨241529232514,53402796⟩ E) ⟨241529233408,52602707⟩ E) ⟨241530278052,56404228⟩ (N E ⟨241530278484,55988565⟩ E))))) ⟨241531326197,56990571⟩ (N (N (N (N (N (N E ⟨241531327908,55346661⟩ E) ⟨241532374774,57157627⟩ E) ⟨241532374790,57141928⟩ (N (N E ⟨241533427712,53226318⟩ E) ⟨241541811936,58703260⟩ E)) ⟨241541816320,54484584⟩ (N (N (N E ⟨241546006691,58929371⟩ E) ⟨241546010624,55119238⟩ E) ⟨241548103429,59692506⟩ (N E ⟨241548103845,59268078⟩ E))) ⟨241549152438,59421496⟩ (N (N (N (N E ⟨241549153430,58422015⟩ E) ⟨241550203478,57141227⟩ E) ⟨241550204278,56372591⟩ (N (N E ⟨241558592220,58328244⟩ E) ⟨241558593536,57045284⟩ E)) ⟨241561735794,61023237⟩ (N (N (N E ⟨241561736370,60425731⟩ E) ⟨241561736402,60392752⟩ E) ⟨241562784450,61112135⟩ (N E ⟨241562785218,60316201⟩ E)))) ⟨241562787840,57694661⟩ (N (N (N (N (N E ⟨241564881093,61995298⟩ E) ⟨241566982144,58347719⟩ E) ⟨241575366352,64302320⟩ (N (N E ⟨241575368632,61845150⟩ E) ⟨241575370752,59664876⟩ E)) ⟨241579561714,63850073⟩ (N (N (N E ⟨241579562482,63018648⟩ E) ⟨241579564210,61196873⟩ E) ⟨241579565056,60328976⟩ (N E ⟨241581657509,65714142⟩ E))) ⟨241581657525,65696067⟩ (N (N (N (N E ⟨241581658357,64764651⟩ E) ⟨241581658373,64746901⟩ E) ⟨241581658773,64305134⟩ (N E ⟨241583759360,60996756⟩ E)) ⟨241585855068,62847620⟩ (N (N (N E ⟨241592147296,63054461⟩ E) ⟨241592147968,62343359⟩ E) ⟨241596338914,66718714⟩ (N E ⟨241596339682,65849876⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab19 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨241596340802,64608020⟩ E) ⟨241596341378,63980752⟩ E) ⟨241596341634,63704410⟩ (N (N E ⟨241596342272,63022182⟩ E) ⟨241597386548,67987263⟩ E)) ⟨241597386612,67912627⟩ (N (N (N E ⟨241597387028,67429982⟩ E) ⟨241597387412,66988264⟩ E) ⟨241597387444,66951617⟩ (N E ⟨241599483718,68333293⟩ E))) ⟨241600536164,64148955⟩ (N (N (N (N E ⟨241600536576,63704685⟩ E) ⟨241608925184,65080733⟩ E) ⟨241613116114,69651282⟩ (N (N E ⟨241613116882,68744194⟩ E) ⟨241613117714,67778119⟩ E)) ⟨241613118546,66828958⟩ (N (N (N E ⟨241613119488,65774278⟩ E) ⟨241614163796,70913179⟩ E) ⟨241614165204,69225156⟩ (N E ⟨241615212357,71118791⟩ E)))) ⟨241615213205,70093028⟩ (N (N (N (N (N E ⟨241617311606,68977890⟩ E) ⟨241625698480,72552847⟩ E) ⟨241625698912,72018206⟩ (N (N E ⟨241625699488,71312990⟩ E) ⟨241625699520,71274065⟩ E)) ⟨241625700064,70616387⟩ (N (N (N E ⟨241630941028,73919446⟩ E) ⟨241631989205,74620298⟩ E) ⟨241631989589,74129737⟩ (N E ⟨241633039638,72471710⟩ E))) ⟨241634087159,73980840⟩ (N (N (N (N E ⟨241634089796,70730967⟩ E) ⟨241634090628,69742794⟩ E) ⟨241642479616,70732144⟩ (N (N E ⟨241646670531,75686398⟩ E) ⟨241646673920,71455132⟩ E)) ⟨241647718660,76461159⟩ (N (N (N E ⟨241648766821,77202327⟩ E) ⟨241648766837,77181133⟩ E) ⟨241648768828,74599563⟩ (N E ⟨241648768916,74487971⟩ E))))) ⟨241650866070,74862743⟩ (N (N (N (N (N (N E ⟨241650866102,74822012⟩ E) ⟨241650866934,73772671⟩ E) ⟨241650867766,72741665⟩ (N (N E ⟨241650868224,72181801⟩ E) ⟨241654010217,77493354⟩ E)) ⟨241659253408,78053886⟩ (N (N (N E ⟨241659253984,77289776⟩ E) ⟨241659256832,73646178⟩ E) ⟨241663447906,78574751⟩ (N E ⟨241663448642,77594353⟩ E))) ⟨241663448738,77467605⟩ (N (N (N (N E ⟨241663449570,76379895⟩ E) ⟨241663451136,74383886⟩ E) ⟨241665544453,79787433⟩ (N (N E ⟨241665544485,79743711⟩ E) ⟨241666593062,79940182⟩ E)) ⟨241667643270,77936749⟩ (N (N (N E ⟨241667645092,75567507⟩ E) ⟨241667645440,75125275⟩ E) ⟨241670787033,81196115⟩ (N E ⟨241680224595,82470815⟩ E)))) ⟨241680225138,81708372⟩ (N (N (N (N (N E ⟨241680226002,80513279⟩ E) ⟨241681272340,83858959⟩ E) ⟨241681272756,83262087⟩ (N (N E ⟨241681273172,82670517⟩ E) ⟨241681273588,82084193⟩ E)) ⟨241683369878,83711009⟩ (N (N (N E ⟨241684422166,78776169⟩ E) ⟨241687564265,84405820⟩ E) ⟨241688614304,82519720⟩ (N E ⟨241692807440,84997886⟩ E))) ⟨241692807872,84371794⟩ (N (N (N (N E ⟨241692808448,83545947⟩ E) ⟨241692809024,82730182⟩ E) ⟨241697001363,86378902⟩ (N E ⟨241697002338,84948866⟩ E)) ⟨241697003106,83843229⟩ (N (N (N E ⟨241697003938,82665681⟩ E) ⟨241699098517,86789411⟩ E) ⟨241699098533,86765589⟩ (N E ⟨241699101380,82653873⟩ E)))))) ⟨241699102212,81498505⟩ (N (N (N (N (N (N (N E ⟨241700147510,86376854⟩ E) ⟨241700147526,86353188⟩ E) ⟨241701199872,81188858⟩ (N (N E ⟨241704341913,87054134⟩ E) ⟨241709588480,82741549⟩ E)) ⟨241713779064,88971771⟩ (N (N (N E ⟨241713779075,88955016⟩ E) ⟨241713779491,88324246⟩ E) ⟨241713779634,88108711⟩ (N E ⟨241713779640,88099682⟩ E))) ⟨241713780466,86867649⟩ (N (N (N (N E ⟨241713780722,86490187⟩ E) ⟨241713780754,86443148⟩ E) ⟨241713782162,84404749⟩ (N (N E ⟨241713782784,83523414⟩ E) ⟨241714828020,88602706⟩ E)) ⟨241715875765,90083295⟩ (N (N (N E ⟨241715876181,89443263⟩ E) ⟨241715878612,85814641⟩ E) ⟨241717973372,89802406⟩ (N E ⟨241717973948,88922191⟩ E)))) ⟨241717975766,86213849⟩ (N (N (N (N (N E ⟨241717977088,84308957⟩ E) ⟨241722168256,89748467⟩ E) ⟨241722171392,85098180⟩ (N (N E ⟨241726361872,91656991⟩ E) ⟨241726362304,90981849⟩ E)) ⟨241726362880,90091302⟩ (N (N (N E ⟨241726364320,87912149⟩ E) ⟨241726365088,86776870⟩ E) ⟨241726365152,86683093⟩ (N E ⟨241726365696,85891082⟩ E))) ⟨241730558690,88628273⟩ (N (N (N (N E ⟨241730559522,87389549⟩ E) ⟨241730560000,86687663⟩ E) ⟨241731604404,93274961⟩ (N (N E ⟨241733701558,93701291⟩ E) ⟨241734752966,89488904⟩ E)) ⟨241734753798,88238004⟩ (N (N (N E ⟨241734754304,87487923⟩ E) ⟨241747333491,95783988⟩ E) ⟨241747336922,90357659⟩ (N E ⟨241747337216,89910774⟩ E))))) ⟨241748381636,96712420⟩ (N (N (N (N (N (N E ⟨241748382052,96025334⟩ E) ⟨241749429845,97543606⟩ E) ⟨241749429861,97516796⟩ (N (N E ⟨241749430261,96849526⟩ E) ⟨241749430693,96135273⟩ E)) ⟨241749431109,95453688⟩ (N (N (N E ⟨241749433076,92311513⟩ E) ⟨241749433908,91021407⟩ E) ⟨241750478838,97066462⟩ (N E ⟨241750479206,96456247⟩ E))) ⟨241750479638,95746014⟩ (N (N (N (N E ⟨241750479670,95693665⟩ E) ⟨241751529494,93890871⟩ E) ⟨241751531062,91429444⟩ (N (N E ⟨241762014816,96734263⟩ E) ⟨241765159268,99526504⟩ E)) ⟨241768308736,94022426⟩ (N (N (N E ⟨241772499418,100874006⟩ E) ⟨241772500146,99626875⟩ E) ⟨241776697344,95692833⟩ (N E ⟨241780888530,101777446⟩ E)))) ⟨241780889298,100453408⟩ (N (N (N (N (N E ⟨241780891026,97552171⟩ E) ⟨241780891648,96533554⟩ E) ⟨241781936116,103742573⟩ (N (N E ⟨241781936388,103260024⟩ E) ⟨241782984293,104683345⟩ E)) ⟨241782984309,104654574⟩ (N (N (N E ⟨241782985541,102468618⟩ E) ⟨241785083958,100720349⟩ E) ⟨241785083990,100665587⟩ (N E ⟨241785084822,99254755⟩ E))) ⟨241785085654,97868557⟩ (N (N (N (N E ⟨241793474560,99077780⟩ E) ⟨241797668864,99933209⟩ E) ⟨241798713332,107392096⟩ (N E ⟨241798714772,104780283⟩ E)) ⟨241799761541,108302366⟩ (N (N (N E ⟨241799761909,107620440⟩ E) ⟨241799761925,107590913⟩ E) ⟨241801861158,104280264⟩ (N E ⟨241801863168,100792316⟩ E))))))) ⟨241814446080,103391699⟩ (N (N (N (N (N (N (N (N E ⟨241815490884,110466752⟩ E) ⟨241816539157,111275847⟩ E) ⟨241816540565,108629190⟩ (N (N E ⟨241816541180,107497871⟩ E) ⟨241816541236,107395590⟩ E)) ⟨241816541268,107337199⟩ (N (N (N E ⟨241818639260,106264265⟩ E) ⟨241818640022,104904068⟩ E) ⟨241827027616,108518981⟩ (N E ⟨241832268228,113970720⟩ E))) ⟨241835417600,107797532⟩ (N (N (N (N E ⟨241839609842,112550414⟩ E) ⟨241839611904,108689727⟩ E) ⟨241843806208,109585597⟩ (N (N E ⟨241847996867,117541240⟩ E) ⟨241847998546,114223063⟩ E)) ⟨241847998578,114160967⟩ (N (N (N E ⟨241848000512,110485144⟩ E) ⟨241849044660,119372957⟩ E) ⟨241849045076,118523894⟩ (N E ⟨241849045492,117682367⟩ E)))) ⟨241850093653,118763476⟩ (N (N (N (N (N E ⟨241850094021,118017164⟩ E) ⟨241850094453,117148525⟩ E) ⟨241850094485,117084500⟩ (N (N E ⟨241850095061,115939492⟩ E) ⟨241850095732,114623233⟩ E)) ⟨241850096564,113016987⟩ (N (N (N E ⟨241850097396,111438784⟩ E) ⟨241851142614,118223100⟩ E) ⟨241852193654,113596742⟩ (N E ⟨241852194816,111388365⟩ E))) ⟨241864777728,114120081⟩ (N (N (N (N E ⟨241865822324,122352162⟩ E) ⟨241865822740,121483573⟩ E) ⟨241865823732,119443226⟩ (N (N E ⟨241866870853,122696399⟩ E) ⟨241866871780,120765588⟩ E)) ⟨241866871812,120699617⟩ (N (N (N E ⟨241866872644,119000084⟩ E) ⟨241866872900,118483178⟩ E) ⟨241866873412,117457761⟩ (N E ⟨241871067430,118976636⟩ E))))) ⟨241882599108,127248002⟩ (N (N (N (N (N (N E ⟨241882599492,126412318⟩ E) ⟨241882599780,125790054⟩ E) ⟨241883650964,120563399⟩ (N (N E ⟨241883651764,118943806⟩ E) ⟨241884696662,126872516⟩ E)) ⟨241885748950,119344698⟩ (N (N (N E ⟨241894135396,125756022⟩ E) ⟨241894137856,120622695⟩ E) ⟨241898328579,129188549⟩ (N E ⟨241899376724,130398931⟩ E))) ⟨241899377588,128485204⟩ (N (N (N (N E ⟨241901474294,129972127⟩ E) ⟨241901474742,128980441⟩ E) ⟨241901474774,128909969⟩ (N (N E ⟨241904621894,126623741⟩ E) ⟨241904623494,123241890⟩ E)) ⟨241910912692,129537622⟩ (N (N (N E ⟨241910913272,128266403⟩ E) ⟨241910915072,124419297⟩ E) ⟨241915105848,133118042⟩ (N E ⟨241915106424,131814303⟩ E)))) ⟨241915109376,125377630⟩ (N (N (N (N (N E ⟨241916153972,134409385⟩ E) ⟨241917203013,133598537⟩ E) ⟨241917203381,132760777⟩ (N (N E ⟨241917203413,132688239⟩ E) ⟨241917204628,129970352⟩ E)) ⟨241917205428,128218737⟩ (N (N (N E ⟨241917206260,126428252⟩ E) ⟨241918251526,133998310⟩ E) ⟨241919300732,132816630⟩ (N E ⟨241919303680,126339636⟩ E))) ⟨241921397768,133587998⟩ (N (N (N (N E ⟨241923497984,127305315⟩ E) ⟨241927688224,137450012⟩ E) ⟨241927689088,135432358⟩ (N E ⟨241927689664,134107803⟩ E)) ⟨241927690240,132799403⟩ (N (N (N E ⟨241927690272,132727184⟩ E) ⟨241927691104,130866583⟩ E) ⟨241927692288,128274666⟩ (N E ⟨241931885442,131783357⟩ E)))))) ⟨241931886592,129247689⟩ (N (N (N (N (N (N (N E ⟨241932931204,138516232⟩ E) ⟨241932931620,137532960⟩ E) ⟨241933980197,137789818⟩ (N (N E ⟨241933980740,136517089⟩ E) ⟨241933981828,134010867⟩ E)) ⟨241933982596,132276337⟩ (N (N (N E ⟨241936080896,130224384⟩ E) ⟨241938174584,138632123⟩ E) ⟨241938177126,132765153⟩ (N E ⟨241947612114,140150204⟩ E))) ⟨241948659891,142343327⟩ (N (N (N (N E ⟨241948663808,133176498⟩ E) ⟨241949708836,141709649⟩ E) ⟨241950756629,143890777⟩ (N (N E ⟨241950757413,141970334⟩ E) ⟨241950758421,139548035⟩ E)) ⟨241954951400,143803575⟩ (N (N (N E ⟨241961243152,144666808⟩ E) ⟨241961243584,143602361⟩ E) ⟨241961244160,142198282⟩ (N E ⟨241961244736,140811326⟩ E)))) ⟨241965441024,137164046⟩ (N (N (N (N (N E ⟨241967534245,147177819⟩ E) ⟨241967535204,144783598⟩ E) ⟨241967535236,144704550⟩ (N (N E ⟨241967535940,142979070⟩ E) ⟨241967536068,142668115⟩ E)) ⟨241967536324,142048738⟩ (N (N (N E ⟨241967536900,140667385⟩ E) ⟨241969635328,138170109⟩ E) ⟨241971729048,146994266⟩ (N E ⟨241971731590,140774236⟩ E))) ⟨241973826962,145623005⟩ (N (N (N (N E ⟨241973829632,139179842⟩ E) ⟨241978019968,149974082⟩ E) ⟨241978022200,144371112⟩ (N E ⟨241978022968,142503905⟩ E)) ⟨241978023936,140193245⟩ (N (N (N E ⟨241982218240,141210318⟩ E) ⟨241983262900,151199924⟩ E) ⟨241984311461,151511489⟩ (N E ⟨241984312404,149087479⟩ E))))) ⟨241984312901,147829433⟩ (N (N (N (N (N (N E ⟨241984313172,147149046⟩ E) ⟨241984313588,146112215⟩ E) ⟨241984314004,145084501⟩ (N (N E ⟨241984314836,143056044⟩ E) ⟨241986410816,146449763⟩ E)) ⟨241986412544,142231060⟩ (N (N (N E ⟨241992702916,146425875⟩ E) ⟨241994797200,154307433⟩ E) ⟨241994798048,152084952⟩ (N E ⟨241994798624,150598137⟩ E))) ⟨241994799200,149129450⟩ (N (N (N (N E ⟨241994800032,147039483⟩ E) ⟨241998991539,155317670⟩ E) ⟨242001088693,155865182⟩ (N (N E ⟨242001089109,154758988⟩ E) ⟨242005286912,146869803⟩ E)) ⟨242015772672,149478980⟩ (N (N (N E ⟨242016817812,158735707⟩ E) ⟨242016818772,156156223⟩ E) ⟨242017865557,161293877⟩ (N E ⟨242017865973,160147433⟩ E)))) ⟨242017866357,159098205⟩ (N (N (N (N (N E ⟨242017866789,157928076⟩ E) ⟨242017866821,157841828⟩ E) ⟨242017868916,152321200⟩ (N (N E ⟨242017869748,150195855⟩ E) ⟨242019965942,153181099⟩ E)) ⟨242024158368,159256087⟩ (N (N (N E ⟨242024159520,156163733⟩ E) ⟨242028351616,163289474⟩ E) ⟨242028352048,162085950⟩ (N E ⟨242028352480,160893496⟩ E))) ⟨242028353056,159320567⟩ (N (N (N (N E ⟨242028353632,157766816⟩ E) ⟨242028354400,155724498⟩ E) ⟨242028354496,155471538⟩ (N E ⟨242033594580,164472053⟩ E)) ⟨242033594644,164291818⟩ (N (N (N E ⟨242033595060,163126293⟩ E) ⟨242034642773,165841928⟩ E) ⟨242034643573,163584343⟩ (N E ⟨242034644900,159923636⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab20 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨242035691750,164989863⟩ E) ⟨242039886969,163550828⟩ E) ⟨242040936658,160756718⟩ (N (N E ⟨242045130412,163383640⟩ E) ⟨242047228176,162246139⟩ E)) ⟨242047228944,160147393⟩ (N (N (N E ⟨242047229040,159887442⟩ E) ⟨242049323651,167520638⟩ E) ⟨242049323667,167474806⟩ (N E ⟨242049324083,166288638⟩ E))) ⟨242049325362,162706936⟩ (N (N (N (N E ⟨242049326226,160341879⟩ E) ⟨242049327104,157982366⟩ E) ⟨242050371812,169002744⟩ (N (N E ⟨242050372228,167803552⟩ E) ⟨242051420389,169287909⟩ E)) ⟨242051424084,158981976⟩ (N (N (N E ⟨242051424116,158896201⟩ E) ⟨242051424256,158521618⟩ E) ⟨242052469398,168324014⟩ (N E ⟨242052469814,167131847⟩ E)))) ⟨242053521408,159061787⟩ (N (N (N (N (N E ⟨242056664201,168032648⟩ E) ⟨242057715712,160144873⟩ E) ⟨242061910016,161231625⟩ (N (N E ⟨242064005120,167482846⟩ E) ⟨242064005952,165134716⟩ E)) ⟨242067148676,174692309⟩ (N (N (N E ⟨242067149060,173545982⟩ E) ⟨242068198037,172648751⟩ E) ⟨242068200196,166418726⟩ (N E ⟨242070298624,163416122⟩ E))) ⟨242078683744,175719550⟩ (N (N (N (N E ⟨242080783152,169662830⟩ E) ⟨242082880912,168485267⟩ E) ⟨242082881536,166720348⟩ (N (N E ⟨242083926292,178195579⟩ E) ⟨242084974853,178537098⟩ E)) ⟨242084975717,175918868⟩ (N (N (N E ⟨242084975749,175822822⟩ E) ⟨242084976980,172177296⟩ E) ⟨242097558720,179155894⟩ (N E ⟨242097559488,176827577⟩ E))))) ⟨242097560320,174347763⟩ (N (N (N (N (N (N E ⟨242100703924,181657351⟩ E) ⟨242101752485,182001459⟩ E) ⟨242101752501,181951672⟩ (N (N E ⟨242106995065,184436991⟩ E) ⟨242106995897,181832812⟩ E)) ⟨242108047360,173427708⟩ (N (N (N E ⟨242112241664,174558419⟩ E) ⟨242116432627,185943911⟩ E) ⟨242116433043,184627471⟩ (N E ⟨242116435968,175692791⟩ E))) ⟨242117480372,188914007⟩ (N (N (N (N E ⟨242117480788,187571789⟩ E) ⟨242117481204,186241472⟩ E) ⟨242118529749,186641341⟩ (N (N E ⟨242118530757,183459237⟩ E) ⟨242118531412,181427812⟩ E)) ⟨242119578326,186939529⟩ (N (N (N E ⟨242120630272,176830825⟩ E) ⟨242123772297,189222441⟩ E) ⟨242123773800,184430561⟩ (N E ⟨242129015872,188493558⟩ E)))) ⟨242129018656,179795677⟩ (N (N (N (N (N E ⟨242129018880,179117874⟩ E) ⟨242131115904,180080089⟩ E) ⟨242131116032,179691925⟩ (N (N E ⟨242133209395,192253002⟩ E) ⟨242133212226,183207036⟩ E)) ⟨242133213058,180650203⟩ (N (N (N E ⟨242134258404,191138520⟩ E) ⟨242135306549,192860566⟩ E) ⟨242141601792,182575900⟩ (N E ⟨242145792288,196016443⟩ E))) ⟨242148938898,193999671⟩ (N (N (N (N E ⟨242148939474,192104521⟩ E) ⟨242149986627,197139661⟩ E) ⟨242149987107,195527368⟩ (N E ⟨242149989776,186856914⟩ E)) ⟨242152083781,197754693⟩ (N (N (N E ⟨242152083797,197700515⟩ E) ⟨242152085876,190815823⟩ E) ⟨242153132790,196603974⟩ (N E ⟨242154183830,188833047⟩ E)))))) ⟨242154184704,186066861⟩ (N (N (N (N (N (N (N E ⟨242158379008,187237832⟩ E) ⟨242160475268,190675059⟩ E) ⟨242162573312,188412461⟩ (N (N E ⟨242165716146,198817089⟩ E) ⟨242168861029,202652990⟩ E)) ⟨242168861445,201215817⟩ (N (N (N E ⟨242175154760,196768552⟩ E) ⟨242175156224,191958293⟩ E) ⟨242179346704,206113638⟩ (N E ⟨242179350528,193147551⟩ E))) ⟨242183543930,197323097⟩ (N (N (N (N E ⟨242183544832,194340466⟩ E) ⟨242184589668,207406893⟩ E) ⟨242185637861,209093477⟩ (N (N E ⟨242185637877,209036105⟩ E) ⟨242185637893,208978754⟩ E)) ⟨242185638293,207551334⟩ (N (N (N E ⟨242185638309,207494491⟩ E) ⟨242185638709,206079725⟩ E) ⟨242185638725,206023385⟩ (N E ⟨242185640372,200325537⟩ E)))) ⟨242185641204,197522103⟩ (N (N (N (N (N E ⟨242185641940,195082919⟩ E) ⟨242185641984,194938294⟩ E) ⟨242187739136,195537037⟩ (N (N E ⟨242196127744,197941146⟩ E) ⟨242199270018,210855528⟩ E)) ⟨242200318755,210595528⟩ (N (N (N E ⟨242200322048,199148684⟩ E) ⟨242201367300,211027152⟩ E) ⟨242201367316,210969448⟩ (N E ⟨242201367380,210738829⟩ E))) ⟨242201368340,207317067⟩ (N (N (N (N E ⟨242202415109,214141122⟩ E) ⟨242203464918,209990237⟩ E) ⟨242204516352,200359877⟩ (N (N E ⟨242208709224,206513870⟩ E) ⟨242216047858,213722268⟩ E)) ⟨242216048434,211635302⟩ (N (N (N E ⟨242218144148,217545372⟩ E) ⟨242219192725,217867807⟩ E) ⟨242219193125,216382210⟩ (N E ⟨242219195572,207564599⟩ E))))) ⟨242219196416,204627828⟩ (N (N (N (N (N (N E ⟨242229679264,218217920⟩ E) ⟨242229679296,218098809⟩ E) ⟨242229679872,215968655⟩ (N (N E ⟨242229680416,213980675⟩ E) ⟨242231778208,212300805⟩ E)) ⟨242231779072,209222927⟩ (N (N (N E ⟨242231779136,208997162⟩ E) ⟨242232824514,220989007⟩ E) ⟨242233876480,208940533⟩ (N E ⟨242234921364,222793175⟩ E))) ⟨242234921380,222732157⟩ (N (N (N (N E ⟨242234921796,221153012⟩ E) ⟨242235969941,223119409⟩ E) ⟨242235970373,221476851⟩ (N (N E ⟨242242264456,213692077⟩ E) ⟨242242265088,211425024⟩ E)) ⟨242249602290,224110380⟩ (N (N (N E ⟨242250650451,226034751⟩ E) ⟨242250650883,224373891⟩ E) ⟨242250653696,213924120⟩ (N E ⟨242251698596,228040720⟩ E)))) ⟨242251699012,226423937⟩ (N (N (N (N (N E ⟨242252746805,229815020⟩ E) ⟨242252747173,228370660⟩ E) ⟨242252747189,228308120⟩ (N (N E ⟨242252749268,220360751⟩ E) ⟨242254848000,215179144⟩ E)) ⟨242263233760,228470722⟩ (N (N (N E ⟨242263234336,226239569⟩ E) ⟨242263236576,217817591⟩ E) ⟨242263236608,217700143⟩ (N E ⟨242269524421,233617186⟩ E))) ⟨242269524837,231961100⟩ (N (N (N (N E ⟨242269526468,225608011⟩ E) ⟨242270573846,230585819⟩ E) ⟨242271623654,226130174⟩ (N E ⟨242275818920,223763169⟩ E)) ⟨242282109456,229242186⟩ (N (N (N E ⟨242282110320,225913105⟩ E) ⟨242282110976,223425762⟩ E) ⟨242285252676,240289020⟩ (N E ⟨242285252692,240223116⟩ E))))))) ⟨242285253492,236956537⟩ (N (N (N (N (N (N (N (N E ⟨242285253524,236827032⟩ E) ⟨242285253940,235151500⟩ E) ⟨242286303764,230542320⟩ (N (N E ⟨242288402432,225350719⟩ E) ⟨242292594656,234760678⟩ E)) ⟨242296788224,239076261⟩ (N (N (N E ⟨242296788800,236741856⟩ E) ⟨242296789376,234435879⟩ E) ⟨242296790208,231154373⟩ (N E ⟨242300981715,243797870⟩ E))) ⟨242302030356,243871428⟩ (N (N (N (N E ⟨242302030772,242143233⟩ E) ⟨242303078885,244412764⟩ E) ⟨242303079285,242746732⟩ (N (N E ⟨242304128310,241233873⟩ E) ⟨242305179648,230524054⟩ E)) ⟨242309373384,234059077⟩ (N (N (N E ⟨242309373952,231826504⟩ E) ⟨242313566840,238780214⟩ E) ⟨242313567608,235696137⟩ (N E ⟨242317759416,247287492⟩ E)))) ⟨242317759427,247241037⟩ (N (N (N (N (N E ⟨242317759843,245492176⟩ E) ⟨242317759992,244869545⟩ E) ⟨242317761042,240537395⟩ (N (N E ⟨242317762560,234442338⟩ E) ⟨242318807940,247853528⟩ E)) ⟨242318808372,246032726⟩ (N (N (N E ⟨242319856117,249899125⟩ E) ⟨242319858228,241071633⟩ E) ⟨242321953724,248655848⟩ (N E ⟨242321954300,246224563⟩ E))) ⟨242321955456,241434133⟩ (N (N (N (N E ⟨242321956864,235755722⟩ E) ⟨242326148608,247583201⟩ E) ⟨242330342224,251902219⟩ (N (N E ⟨242330342656,250051265⟩ E) ⟨242330343232,247609697⟩ E)) ⟨242330343808,245197862⟩ (N (N (N E ⟨242330343840,245064734⟩ E) ⟨242330344072,244102256⟩ E) ⟨242330344576,242027586⟩ (N E ⟨242330344672,241634913⟩ E))))) ⟨242330345440,238522035⟩ (N (N (N (N (N (N E ⟨242330345472,238393423⟩ E) ⟨242334539776,239717738⟩ E) ⟨242335584372,256849694⟩ (N (N E ⟨242335584756,255165981⟩ E) ⟨242338733350,244034250⟩ E)) ⟨242338734080,241045697⟩ (N (N (N E ⟨242349219840,244381529⟩ E) ⟨242351313427,260344872⟩ E) ⟨242351314259,256671306⟩ (N E ⟨242351316992,245051427⟩ E))) ⟨242352361988,260768011⟩ (N (N (N (N E ⟨242353410197,262770897⟩ E) ⟨242353411045,258986303⟩ E) ⟨242353413556,248172472⟩ (N (N E ⟨242353414144,245722235⟩ E) ⟨242354459558,259619366⟩ E)) ⟨242359705600,247740121⟩ (N (N (N E ⟨242367042930,261825752⟩ E) ⟨242367043506,259270451⟩ E) ⟨242368091586,261823066⟩ (N E ⟨242369139236,266355925⟩ E)))) ⟨242369139620,264613113⟩ (N (N (N (N (N E ⟨242370191360,251121466⟩ E) ⟨242374382616,265877613⟩ E) ⟨242374384944,255567489⟩ (N (N E ⟨242376482816,253161192⟩ E) ⟨242380673488,270720502⟩ E)) ⟨242380677120,254525558⟩ (N (N (N E ⟨242384867923,271566144⟩ E) ⟨242384868339,269642207⟩ E) ⟨242384868755,267735281⟩ (N E ⟨242384868850,267302173⟩ E))) ⟨242384868882,267156481⟩ (N (N (N (N E ⟨242384869714,263403095⟩ E) ⟨242384870002,262119224⟩ E) ⟨242384870834,258453956⟩ (N E ⟨242384871424,255893562⟩ E)) ⟨242385916884,270146155⟩ (N (N (N E ⟨242386965461,270502941⟩ E) ⟨242386967924,259417820⟩ E) ⟨242389065728,257265204⟩ (N E ⟨242391159432,273503018⟩ E)))))) ⟨242397454336,260019400⟩ (N (N (N (N (N (N (N E ⟨242401646050,273130600⟩ E) ⟨242401646082,272981721⟩ E) ⟨242401646914,269146235⟩ (N (N E ⟨242401647170,267979659⟩ E) ⟨242401647746,265377889⟩ E)) ⟨242401648640,261401954⟩ (N (N (N E ⟨242402693684,277926668⟩ E) ⟨242403742277,278213590⟩ E) ⟨242403742677,276317931⟩ (N E ⟨242407937080,277312111⟩ E))) ⟨242410037248,264177969⟩ (N (N (N (N E ⟨242414228000,282082759⟩ E) ⟨242414231552,265571429⟩ E) ⟨242418423187,279322749⟩ (N (N E ⟨242418423250,279022997⟩ E) ⟨242418425010,270809155⟩ E)) ⟨242419470932,283685825⟩ (N (N (N E ⟨242420519509,284052469⟩ E) ⟨242420521620,274022568⟩ E) ⟨242422620160,268369255⟩ (N E ⟨242431005232,287962907⟩ E)))) ⟨242431007968,274868936⟩ (N (N (N (N (N E ⟨242431008768,271181616⟩ E) ⟨242434151890,284532494⟩ E) ⟨242434152466,281756715⟩ (N (N E ⟨242435199571,289288626⟩ E) ⟨242436248164,289579530⟩ E)) ⟨242436248580,287528125⟩ (N (N (N E ⟨242437296725,290029193⟩ E) ⟨242443591680,275427405⟩ E) ⟨242447782880,291819187⟩ (N E ⟨242447785984,276849932⟩ E))) ⟨242451977651,290994826⟩ (N (N (N (N E ⟨242451980288,278276091⟩ E) ⟨242453025428,295369944⟩ E) ⟨242454073589,297857034⟩ (N (N E ⟨242454074005,295743684⟩ E) ⟨242454074805,291731977⟩ E)) ⟨242454074837,291572928⟩ (N (N (N E ⟨242454076052,285613437⟩ E) ⟨242456174592,279705879⟩ E) ⟨242464563200,282576347⟩ (N E ⟨242467706322,296464503⟩ E))))) ⟨242468754851,297079156⟩ (N (N (N (N (N (N E ⟨242468755746,292590222⟩ E) ⟨242468756866,287091571⟩ E) ⟨242468757504,284017026⟩ (N (N E ⟨242469802244,303530564⟩ E) ⟨242469802260,303447383⟩ E)) ⟨242469803092,299160985⟩ (N (N (N E ⟨242469803508,297046173⟩ E) ⟨242470851605,299863033⟩ E) ⟨242470851621,299781133⟩ (N E ⟨242472951808,285461333⟩ E))) ⟨242481336880,306205208⟩ (N (N (N (N E ⟨242481337312,303952480⟩ E) ⟨242485532946,298645390⟩ E) ⟨242485533010,298321055⟩ (N (N E ⟨242485533778,294463177⟩ E) ⟨242485533874,293985339⟩ E)) ⟨242486579460,309723995⟩ (N (N (N E ⟨242498115748,303733319⟩ E) ⟨242498116160,301616678⟩ E) ⟨242498117632,294203355⟩ (N E ⟨242502308915,311218714⟩ E)))) ⟨242502308931,311133724⟩ (N (N (N (N (N E ⟨242502309474,308266478⟩ E) ⟨242502311042,300170251⟩ E) ⟨242503357076,313823430⟩ (N (N E ⟨242503357492,311600733⟩ E) ⟨242503357508,311515639⟩ E)) ⟨242503357940,309229026⟩ (N (N (N E ⟨242506505860,299057041⟩ E) ⟨242506506240,297146371⟩ E) ⟨242514894848,300103886⟩ (N E ⟨242519086200,317071094⟩ E))) ⟨242519087352,310913330⟩ (N (N (N (N E ⟨242519087858,308255905⟩ E) ⟨242519089152,301588078⟩ E) ⟨242520133940,322031756⟩ (N E ⟨242520134324,319922488⟩ E)) ⟨242520135732,312334763⟩ (N (N (N E ⟨242521183733,315794365⟩ E) ⟨242521185748,305181223⟩ E) ⟨242523281084,315500770⟩ (N E ⟨242523283456,303075894⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab21 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨242531668576,324735418⟩ E) ⟨242531669440,319980213⟩ E) ⟨242531670016,316858382⟩ (N (N E ⟨242531670048,316686066⟩ E) ⟨242531670592,313774538⟩ E)) ⟨242531672064,306062392⟩ (N (N (N E ⟨242535863970,320311576⟩ E) ⟨242535864802,315814131⟩ E) ⟨242535866368,307561073⟩ (N E ⟨242536911556,326165395⟩ E))) ⟨242540060672,309063376⟩ (N (N (N (N E ⟨242544254976,310569299⟩ E) ⟨242548449280,312078842⟩ E) ⟨242551593042,323809970⟩ (N (N E ⟨242552640243,331889107⟩ E) ⟨242552641059,327299665⟩ E)) ⟨242553688820,332284388⟩ (N (N (N E ⟨242553689620,327778829⟩ E) ⟨242553689652,327600200⟩ E) ⟨242553690228,324405597⟩ (N E ⟨242554739444,321289032⟩ E)))) ⟨242556837888,315108785⟩ (N (N (N (N (N E ⟨242561030944,323377404⟩ E) ⟨242565223504,334715074⟩ E) ⟨242565223936,332258297⟩ (N (N E ⟨242565224512,329017556⟩ E) ⟨242565225088,325816239⟩ E)) ⟨242565226496,318153202⟩ (N (N (N E ⟨242569419170,328615779⟩ E) ⟨242571515013,336822427⟩ E) ⟨242582000320,343505846⟩ (N E ⟨242586194659,344932879⟩ E))) ⟨242586195139,342116863⟩ (N (N (N (N E ⟨242586195555,339699531⟩ E) ⟨242586195666,339058134⟩ E) ⟨242586195698,338873508⟩ (N (N E ⟨242586196530,334117045⟩ E) ⟨242586196818,332490045⟩ E)) ⟨242586198016,325827538⟩ (N (N (N E ⟨242587243252,345241261⟩ E) ⟨242588291813,345738753⟩ E) ⟨242598777968,347489006⟩ (N E ⟨242598778976,341574850⟩ E))))) ⟨242598780126,334980400⟩ (N (N (N (N (N (N E ⟨242598780384,333522869⟩ E) ⟨242598780928,330475519⟩ E) ⟨242602971891,351405096⟩ (N (N E ⟨242602972866,345608731⟩ E) ⟨242602974754,334720443⟩ E)) ⟨242602975232,332032073⟩ (N (N (N E ⟨242605069061,352121856⟩ E) ⟨242605069461,349724572⟩ E) ⟨242607168294,340667355⟩ (N E ⟨242607169536,333592239⟩ E))) ⟨242609266224,337001324⟩ (N (N (N (N E ⟨242619751250,345211838⟩ E) ⟨242619751826,341864074⟩ E) ⟨242620798580,353005023⟩ (N (N E ⟨242620799124,349753703⟩ E) ⟨242621846325,358460986⟩ E)) ⟨242621846341,358362987⟩ (N (N (N E ⟨242621846741,355923878⟩ E) ⟨242621847141,353505488⟩ E) ⟨242621847173,353312906⟩ (N E ⟨242621848404,346003060⟩ E)))) ⟨242621849140,341722821⟩ (N (N (N (N (N E ⟨242628141056,341447240⟩ E) ⟨242632331968,363360412⟩ E) ⟨242632332400,360688836⟩ (N (N E ⟨242632332832,358041774⟩ E) ⟨242632333408,354550023⟩ E)) ⟨242632333984,351100743⟩ (N (N (N E ⟨242632334752,346566701⟩ E) ⟨242632335360,343029069⟩ E) ⟨242637575412,361957152⟩ (N E ⟨242638623925,362763472⟩ E))) ⟨242641769751,363408192⟩ (N (N (N (N E ⟨242649112576,349392469⟩ E) ⟨242653304003,368539743⟩ E) ⟨242653304451,365736357⟩ (N E ⟨242653305136,361501276⟩ E)) ⟨242653305682,358169413⟩ (N (N (N E ⟨242653306880,350992336⟩ E) ⟨242654352580,368954003⟩ E) ⟨242654353012,366247250⟩ (N E ⟨242654353588,362676747⟩ E)))))) ⟨242655400373,374350502⟩ (N (N (N (N (N (N (N E ⟨242657501184,352595809⟩ E) ⟨242658546983,370013214⟩ E) ⟨242670084096,357427857⟩ (N (N E ⟨242671129028,380678296⟩ E) ⟨242672178389,376030426⟩ E)) ⟨242674277990,361537488⟩ (N (N (N E ⟨242674278400,359045747⟩ E) ⟨242675324215,376675057⟩ E) ⟨242686859826,373179692⟩ (N E ⟨242686860690,367761110⟩ E))) ⟨242687906628,385052765⟩ (N (N (N (N E ⟨242687906644,384947503⟩ E) ⟨242687907060,382223289⟩ E) ⟨242688955205,385477345⟩ (N (N E ⟨242688956069,379838154⟩ E) ⟨242688958100,366982884⟩ E)) ⟨242691055616,365553331⟩ (N (N (N E ⟨242692101863,380686168⟩ E) ⟨242703635715,388568644⟩ E) ⟨242704683860,391872835⟩ (N E ⟨242704684276,389099611⟩ E)))) ⟨242704685300,382377028⟩ (N (N (N (N (N E ⟨242705732453,392193750⟩ E) ⟨242705732853,389524743⟩ E) ⟨242716221440,375422711⟩ (N (N E ⟨242720412979,395176201⟩ E) ⟨242720414610,384373850⟩ E)) ⟨242720414642,384165627⟩ (N (N (N E ⟨242720415378,379415176⟩ E) ⟨242720415474,378800978⟩ E) ⟨242720415744,377080201⟩ (N E ⟨242721460724,401267080⟩ E))) ⟨242721461556,395604302⟩ (N (N (N (N E ⟨242722511764,385206953⟩ E) ⟨242722511796,384998280⟩ E) ⟨242722512628,379622049⟩ (N (N E ⟨242722512896,377910294⟩ E) ⟨242724610048,378741286⟩ E)) ⟨242732996224,398144251⟩ (N (N (N E ⟨242732998144,385389027⟩ E) ⟨242732998656,382074244⟩ E) ⟨242737189747,405249043⟩ (N E ⟨242737192960,383746115⟩ E))))) ⟨242738237940,408356588⟩ (N (N (N (N (N (N E ⟨242738239188,399750476⟩ E) ⟨242738239220,399532804⟩ E) ⟨242738239796,395639914⟩ (N (N E ⟨242739288964,392115134⟩ E) ⟨242743483494,392321505⟩ E)) ⟨242752919250,405885962⟩ (N (N (N E ⟨242753966979,412236501⟩ E) ⟨242753967043,411786083⟩ E) ⟨242753969074,397806547⟩ (N E ⟨242755016388,406861204⟩ E))) ⟨242756064149,413001028⟩ (N (N (N (N E ⟨242756064981,407182956⟩ E) ⟨242756066228,398653383⟩ E) ⟨242760259368,408365930⟩ (N (N E ⟨242766552036,402641293⟩ E) ⟨242766552868,397019823⟩ E)) ⟨242769697074,408692243⟩ (N (N (N E ⟨242771793204,416753411⟩ E) ⟨242772841797,417078861⟩ E) ⟨242777037958,405861680⟩ (N E ⟨242777038848,399808048⟩ E)))) ⟨242783327488,422050515⟩ (N (N (N (N (N E ⟨242783329336,409005665⟩ E) ⟨242783330304,402373756⟩ E) ⟨242787521459,426265235⟩ (N (N E ⟨242787524608,404088713⟩ E) ⟨242788570020,426827440⟩ E)) ⟨242789619077,423787992⟩ (N (N (N E ⟨242789619477,420910641⟩ E) ⟨242789619540,420459687⟩ E) ⟨242789621492,406781757⟩ (N E ⟨242791717952,412439916⟩ E))) ⟨242791718912,405807256⟩ (N (N (N (N E ⟨242800107520,409255098⟩ E) ⟨242804298691,433420896⟩ E) ⟨242804301506,413194434⟩ (N E ⟨242804301824,410984396⟩ E)) ⟨242805347652,431036143⟩ (N (N (N E ⟨242805347668,430918568⟩ E) ⟨242805348148,427409903⟩ E) ⟨242805348692,423476484⟩ (N E ⟨242806398660,414051108⟩ E))))))) ⟨242810592422,419620092⟩ (N (N (N (N (N (N (N (N E ⟨242810593190,414212990⟩ E) ⟨242812690432,414453742⟩ E) ⟨242816884736,416193789⟩ (N (N E ⟨242820027794,436828887⟩ E) ⟨242821076371,437277872⟩ E)) ⟨242823173909,435320164⟩ (N (N (N E ⟨242823175924,420707589⟩ E) ⟨242825273344,419684628⟩ E) ⟨242827367464,442754560⟩ (N E ⟨242833658752,446803668⟩ E))) ⟨242833659184,443521268⟩ (N (N (N (N E ⟨242833659616,440268960⟩ E) ⟨242833659648,440029236⟩ E) ⟨242833660192,435978791⟩ (N (N E ⟨242833660224,435741984⟩ E) ⟨242833660768,431740761⟩ E)) ⟨242833660800,431506828⟩ (N (N (N E ⟨242833661632,425479821⟩ E) ⟨242837856256,424947738⟩ E) ⟨242838901716,448480367⟩ (N E ⟨242838902148,445186827⟩ E)))) ⟨242838902580,441923470⟩ (N (N (N (N (N E ⟨242838903156,437618709⟩ E) ⟨242839950725,445639992⟩ E) ⟨242839952388,433227641⟩ (N (N E ⟨242844147654,428009600⟩ E) ⟨242850436032,453754174⟩ E)) ⟨242852535312,438531353⟩ (N (N (N E ⟨242853582210,451674186⟩ E) ⟨242854632498,439180365⟩ E) ⟨242854633472,432015314⟩ (N E ⟨242855678948,455810823⟩ E))) ⟨242856727541,456146200⟩ (N (N (N (N E ⟨242856728373,449722941⟩ E) ⟨242856729236,443179385⟩ E) ⟨242856730068,436983201⟩ (N (N E ⟨242856730624,432902785⟩ E) ⟨242858827776,433791149⟩ E)) ⟨242867213264,461127199⟩ (N (N (N E ⟨242867214112,454509013⟩ E) ⟨242867214688,450081282⟩ E) ⟨242867215264,445707348⟩ (N E ⟨242867216096,439482835⟩ E))))) ⟨242867216384,437353544⟩ (N (N (N (N (N (N E ⟨242871410688,439140102⟩ E) ⟨242872456196,463071001⟩ E) ⟨242873505189,460256518⟩ (N (N E ⟨242875604992,440930233⟩ E) ⟨242889233028,473738882⟩ E)) ⟨242889233428,470511843⟩ (N (N (N E ⟨242889233460,470254869⟩ E) ⟨242889233844,467184822⟩ E) ⟨242889233876,466930118⟩ (N E ⟨242889234868,459119677⟩ E))) ⟨242890284116,454379608⟩ (N (N (N (N E ⟨242890284148,454133663⟩ E) ⟨242890284980,447797115⟩ E) ⟨242890285056,447223821⟩ (N (N E ⟨242896575584,457040813⟩ E) ⟨242896576416,450663165⟩ E)) ⟨242900770560,453700345⟩ (N (N (N E ⟨242902865856,469130155⟩ E) ⟨242904965120,453561140⟩ E) ⟨242906010292,481023677⟩ (N E ⟨242906011124,474240882⟩ E)))) ⟨242907062084,455912868⟩ (N (N (N (N (N E ⟨242907062272,454470040⟩ E) ⟨242919644272,467080117⟩ E) ⟨242919645008,461308985⟩ (N (N E ⟨242919645184,459942162⟩ E) ⟨242921739779,481264482⟩ E)) ⟨242921742194,461961878⟩ (N (N (N E ⟨242921742336,460857302⟩ E) ⟨242922787508,488757646⟩ E) ⟨242922788292,482260087⟩ (N E ⟨242923837317,479062800⟩ E))) ⟨242923838580,468907973⟩ (N (N (N (N E ⟨242925934076,483236229⟩ E) ⟨242925934652,478522819⟩ E) ⟨242925936640,462690256⟩ (N E ⟨242930129536,475715364⟩ E)) ⟨242934322144,491583274⟩ (N (N (N E ⟨242934323008,484396566⟩ E) ⟨242934323584,479678316⟩ E) ⟨242934324160,475017385⟩ (N E ⟨242934324928,468890534⟩ E)))))) ⟨242934325248,466366854⟩ (N (N (N (N (N (N (N E ⟨242936422400,467288231⟩ E) ⟨242938519552,468210498⟩ E) ⟨242939565108,493305008⟩ (N (N E ⟨242951102464,473762796⟩ E) ⟨242953197457,492363924⟩ E)) ⟨242953198704,482058145⟩ (N (N (N E ⟨242955293779,500354105⟩ E) ⟨242955294179,496952478⟩ E) ⟨242955295890,482724218⟩ (N E ⟨242956342340,500971567⟩ E))) ⟨242956342772,497294294⟩ (N (N (N (N E ⟨242957391813,493855896⟩ E) ⟨242957393920,476550961⟩ E) ⟨242969975552,492694316⟩ (N (N E ⟨242971023282,500306370⟩ E) ⟨242972073984,483087810⟩ E)) ⟨242973119588,508554911⟩ (N (N (N E ⟨242976268288,484963484⟩ E) ⟨242984653840,514728792⟩ E) ⟨242986754048,489668220⟩ (N E ⟨242988848275,515561402⟩ E)))) ⟨242988848691,511917802⟩ (N (N (N (N (N E ⟨242988849107,508306338⟩ E) ⟨242989897236,512681111⟩ E) ⟨242990946245,509406157⟩ (N (N E ⟨242990948276,492186457⟩ E) ⟨242997239808,494395165⟩ E)) ⟨243001434112,496292159⟩ (N (N (N E ⟨243003530016,507839552⟩ E) ⟨243003531264,497241987⟩ E) ⟨243005628416,498192703⟩ (N E ⟨243009822720,500096798⟩ E))) ⟨243018208768,526256373⟩ (N (N (N (N E ⟨243020308048,508565189⟩ E) ⟨243020308480,504872560⟩ E) ⟨243022403171,527365926⟩ (N E ⟨243022403539,524073754⟩ E)) ⟨243023451284,532048398⟩ (N (N (N E ⟨243024500709,524906357⟩ E) ⟨243024501940,514062392⟩ E) ⟨243024502784,506789074⟩ (N E ⟨243034988320,513531811⟩ E))))) ⟨243034988544,511595872⟩ (N (N (N (N (N (N E ⟨243038131826,534748210⟩ E) ⟨243039179923,539639581⟩ E) ⟨243040228932,536174285⟩ (N (N E ⟨243041280000,514490586⟩ E) ⟨243051763232,542061483⟩ E)) ⟨243051765760,519332826⟩ (N (N (N E ⟨243054909426,539288403⟩ E) ⟨243054910002,534039435⟩ E) ⟨243055957155,547635348⟩ (N E ⟨243055957571,543765336⟩ E))) ⟨243055960018,521680241⟩ (N (N (N (N E ⟨243055960064,521275920⟩ E) ⟨243058056404,529457366⟩ E) ⟨243058056436,529170938⟩ (N (N E ⟨243058057216,522248795⟩ E) ⟨243060154368,523222555⟩ E)) ⟨243064348672,525172730⟩ (N (N (N E ⟨243071686242,551108145⟩ E) ⟨243071686674,547072157⟩ E) ⟨243072735203,548016629⟩ (N E ⟨243073782596,559697123⟩ E)))) ⟨243073783444,551659478⟩ (N (N (N (N (N E ⟨243073784436,542439221⟩ E) ⟨243074831957,552762705⟩ E) ⟨243074833604,537525519⟩ (N (N E ⟨243074834432,530063650⟩ E) ⟨243077977783,553373115⟩ E)) ⟨243081125888,533008814⟩ (N (N (N E ⟨243085317232,562518260⟩ E) ⟨243085317664,558389990⟩ E) ⟨243085320192,534976677⟩ (N E ⟨243087416592,542808797⟩ E))) ⟨243088463922,554905879⟩ (N (N (N (N E ⟨243088464498,549506364⟩ E) ⟨243091611648,537935101⟩ E) ⟨243093708800,538923009⟩ (N E ⟨243094755015,561426062⟩ E)) ⟨243102097408,542883475⟩ (N (N (N E ⟨243106289267,567911852⟩ E) ⟨243106291712,544869006⟩ E) ⟨243107337844,568420122⟩ (N E ⟨243107338868,558615265⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab22 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨243114680320,548850663⟩ E) ⟨243118873976,556903926⟩ E) ⟨243118874624,550846785⟩ (N (N E ⟨243122018930,565784284⟩ E) ⟨243123068928,552846437⟩ E)) ⟨243124114676,580525311⟩ (N (N (N E ⟨243125166080,553847586⟩ E) ⟨243127262592,560874940⟩ E) ⟨243135649360,582848679⟩ (N E ⟨243135649792,578579917⟩ E))) ⟨243135650368,572948851⟩ (N (N (N (N E ⟨243135650400,572638028⟩ E) ⟨243135650944,567386139⟩ E) ⟨243135651208,564859133⟩ (N (N E ⟨243135651840,558866557⟩ E) ⟨243137748736,562295099⟩ E)) ⟨243139846144,560880316⟩ (N (N (N E ⟨243140891892,588957485⟩ E) ⟨243140892324,584637604⟩ E) ⟨243141943296,561888518⟩ (N E ⟨243144040448,562897600⟩ E)))) ⟨243148234752,564918408⟩ (N (N (N (N (N E ⟨243152429056,566942738⟩ E) ⟨243154526208,567956224⟩ E) ⟨243155572818,587695477⟩ (N (N E ⟨243155573394,581977676⟩ E) ⟨243156620979,592386822⟩ E)) ⟨243156621011,592064209⟩ (N (N (N E ⟨243156621411,588050024⟩ E) ⟨243156623360,568970591⟩ E) ⟨243157668756,601049439⟩ (N E ⟨243157669172,596797063⟩ E))) ⟨243157669972,588724606⟩ (N (N (N (N E ⟨243157670004,588404556⟩ E) ⟨243158720512,569985838⟩ E) ⟨243169204288,594713052⟩ (N (N E ⟨243169204864,588926536⟩ E) ⟨243169205440,583210240⟩ E)) ⟨243169206272,575075275⟩ (N (N (N E ⟨243171303424,576095802⟩ E) ⟨243172350018,596276188⟩ E) ⟨243177594880,579162660⟩ (N E ⟨243185983488,583264114⟩ E))))) ⟨243188079984,590796448⟩ (N (N (N (N (N (N E ⟨243188080640,584291676⟩ E) ⟨243190175011,613576896⟩ E) ⟨243190175075,612907678⟩ (N (N E ⟨243190175491,608579934⟩ E) ⟨243190175907,604290328⟩ E)) ⟨243190177792,585320115⟩ (N (N (N E ⟨243192274292,592837038⟩ E) ⟨243194372096,587379631⟩ E) ⟨243198566400,589442660⟩ (N E ⟨243202758752,611375596⟩ E))) ⟨243202759904,599552091⟩ (N (N (N (N E ⟨243202760704,591509203⟩ E) ⟨243206952243,622065003⟩ E) ⟨243206955008,593579258⟩ (N (N E ⟨243221635072,600852094⟩ E) ⟨243223731570,608574751⟩ E)) ⟨243223732224,601894580⟩ (N (N (N E ⟨243225828756,609279524⟩ E) ⟨243225828788,608950181⟩ E) ⟨243225829376,602937943⟩ (N E ⟨243227926528,603982183⟩ E)))) ⟨243232120832,606073292⟩ (N (N (N (N (N E ⟨243236313184,628593799⟩ E) ⟨243236314336,616437308⟩ E) ⟨243236315104,608496011⟩ (N (N E ⟨243236315136,608167908⟩ E) ⟨243240506723,639029353⟩ E)) ⟨243242606592,611316403⟩ (N (N (N E ⟨243244703744,612367653⟩ E) ⟨243255189504,617637042⟩ E) ⟨243256235826,642216372⟩ (N E ⟨243257284371,643104444⟩ E))) ⟨243257284787,638571798⟩ (N (N (N (N E ⟨243257284803,638398264⟩ E) ⟨243257286034,625221970⟩ E) ⟨243257286066,624884007⟩ (N E ⟨243257286656,618693546⟩ E)) ⟨243259383808,619750925⟩ (N (N (N E ⟨243273013458,646438462⟩ E) ⟨243273014034,640152541⟩ E) ⟨243274063234,633966405⟩ (N E ⟨243274063872,627177077⟩ E)))))) ⟨243278258176,629306705⟩ (N (N (N (N (N (N (N E ⟨243286644016,664015620⟩ E) ⟨243286644448,659146445⟩ E) ⟨243290841088,635716564⟩ (N (N E ⟨243291886980,665865548⟩ E) ⟨243291887412,660984548⟩ E)) ⟨243292938240,636787932⟩ (N (N (N E ⟨243303421296,672275319⟩ E) ⟨243303424000,642157867⟩ E) ⟨243306567474,668820627⟩ (N E ⟨243306567954,663385921⟩ E))) ⟨243306568530,656936948⟩ (N (N (N (N E ⟨243308664628,669917683⟩ E) ⟨243311812608,646469525⟩ E) ⟨243320198944,676322990⟩ (N (N E ⟨243320201216,650795140⟩ E) ⟨243324393747,672844552⟩ E)) ⟨243324395520,652963179⟩ (N (N (N E ⟨243325441460,683362865⟩ E) ⟨243325441908,678170018⟩ E) ⟨243326492672,654048505⟩ (N E ⟨243336978432,659488210⟩ E)))) ⟨243339075584,660578764⟩ (N (N (N (N (N E ⟨243341172736,661670189⟩ E) ⟨243342219540,682367750⟩ E) ⟨243342219572,681997096⟩ (N (N E ⟨243345367040,663855651⟩ E) ⟨243353755648,668237019⟩ E)) ⟨243356900178,683581373⟩ (N (N (N E ⟨243357947747,695937294⟩ E) ⟨243357947811,695180107⟩ E) ⟨243357949952,670432923⟩ (N E ⟨243358996740,691588601⟩ E))) ⟨243360046580,677495533⟩ (N (N (N (N E ⟨243362142566,692136564⟩ E) ⟨243373677426,692201257⟩ E) ⟨243375773556,705461151⟩ (N (N E ⟨243378919382,706006438⟩ E) ⟨243378921472,681464612⟩ E)) ⟨243391501811,718792059⟩ (N (N (N E ⟨243391504384,688125324⟩ E) ⟨243392550372,719557212⟩ E) ⟨243395697030,709984863⟩ (N E ⟨243399892992,692583158⟩ E))))) ⟨243404086688,701982875⟩ (N (N (N (N (N (N E ⟨243404087296,694817280⟩ E) ⟨243408279443,722981442⟩ E) ⟨243408279459,722784729⟩ (N (N E ⟨243408280002,716148274⟩ E) ⟨243408280866,705744876⟩ E)) ⟨243408281600,697054870⟩ (N (N (N E ⟨243409328020,723549902⟩ E) ⟨243412475904,699295928⟩ E) ⟨243424009138,718732784⟩ (N E ⟨243425056307,736701336⟩ E))) ⟨243425056723,731504076⟩ (N (N (N (N E ⟨243425058386,711179846⟩ E) ⟨243425058816,706039898⟩ E) ⟨243427155968,707166924⟩ (N (N E ⟨243437639104,745229452⟩ E) ⟨243437639968,734356660⟩ E)) ⟨243437640000,733957785⟩ (N (N (N E ⟨243437640544,727218181⟩ E) ⟨243437640576,726824148⟩ E) ⟨243437641120,720166247⟩ (N E ⟨243437641152,719776985⟩ E)))) ⟨243437641728,712815042⟩ (N (N (N (N (N E ⟨243446030336,717349110⟩ E) ⟨243454418944,721897015⟩ E) ⟨243457563570,737202774⟩ (N (N E ⟨243458612850,729054149⟩ E) ⟨243458612882,728660433⟩ E)) ⟨243458613248,724176153⟩ (N (N (N E ⟨243459660148,745584685⟩ E) ⟨243471194464,752308651⟩ E) ⟨243471195040,744997641⟩ (N E ⟨243471196160,731034299⟩ E))) ⟨243474339858,758368623⟩ (N (N (N (N E ⟨243475389698,742871262⟩ E) ⟨243475390050,738466339⟩ E) ⟨243475390464,733327255⟩ (N E ⟨243487973376,740226831⟩ E)) ⟨243490070528,741379779⟩ (N (N (N E ⟨243492165187,774568728⟩ E) ⟨243492167680,742533589⟩ E) ⟨243493214196,769480141⟩ (N E ⟨243493214644,763647153⟩ E))))))) ⟨243504750592,749474547⟩ (N (N (N (N (N (N (N (N E ⟨243508942835,778485812⟩ E) ⟨243508944896,751795091⟩ E) ⟨243509991476,778226738⟩ (N (N E ⟨243513139200,754119079⟩ E) ⟨243521527808,758777383⟩ E)) ⟨243524671506,787113628⟩ (N (N (N E ⟨243525720547,781522018⟩ E) ⟨243525721746,765824691⟩ E) ⟨243525722112,761111697⟩ (N E ⟨243526769076,782745757⟩ E))) ⟨243527818932,766560345⟩ (N (N (N (N E ⟨243529916416,763449450⟩ E) ⟨243538305024,768135274⟩ E) ⟨243546693632,772834844⟩ (N (N E ⟨243557177809,799855604⟩ E) ⟨243559274979,800824383⟩ E)) ⟨243559276210,784315625⟩ (N (N (N E ⟨243559276544,779909958⟩ E) ⟨243560323540,801635201⟩ E) ⟨243580248064,791770435⟩ (N E ⟨243588634624,824635579⟩ E)))) ⟨243588636672,796538618⟩ (N (N (N (N (N E ⟨243590733824,797732805⟩ E) ⟨243592830706,802573696⟩ E) ⟨243592830976,798927847⟩ (N (N E ⟨243593877588,826547049⟩ E) ⟨243594928128,800123745⟩ E)) ⟨243597025280,801320499⟩ (N (N (N E ⟨243605413888,806116070⟩ E) ⟨243609606243,835631254⟩ E) ⟨243609608192,808518985⟩ (N E ⟨243615899558,813362791⟩ E))) ⟨243626383523,844681534⟩ (N (N (N (N E ⟨243626385408,818164829⟩ E) ⟨243638968320,825435072⟩ E) ⟨243642113170,839612765⟩ (N (N E ⟨243643160275,861467057⟩ E) ⟨243644209716,849522108⟩ E)) ⟨243655745536,835176486⟩ (N (N (N E ⟨243656793200,848757921⟩ E) ⟨243657842688,836397997⟩ E) ⟨243658889778,858303752⟩ (N E ⟨243659939602,840988614⟩ E))))) ⟨243659939840,837620360⟩ (N (N (N (N (N (N E ⟨243672522752,844972417⟩ E) ⟨243675667602,859462653⟩ E) ⟨243676717056,847429909⟩ (N (N E ⟨243677764212,868647532⟩ E) ⟨243680911360,849890804⟩ E)) ⟨243683008512,851122527⟩ (N (N (N E ⟨243692444274,877517954⟩ E) ⟨243706076864,869406901⟩ E) ⟨243710269635,894831994⟩ (N E ⟨243716562944,870945602⟩ E))) ⟨243718660096,872191756⟩ (N (N (N (N E ⟨243722854400,874686609⟩ E) ⟨243731243008,879686482⟩ E) ⟨243739630144,906992532⟩ (N (N E ⟨243739630720,898186617⟩ E) ⟨243739631296,889487334⟩ E)) ⟨243739631328,889007136⟩ (N (N (N E ⟨243739631616,884699904⟩ E) ⟨243744873108,908916447⟩ E) ⟨243748020224,889726867⟩ (N E ⟨243758505840,898207484⟩ E)))) ⟨243759553170,917977832⟩ (N (N (N (N (N E ⟨243760603026,898958091⟩ E) ⟨243760603136,897292681⟩ E) ⟨243773186048,904888911⟩ (N (N E ⟨243776330370,928602235⟩ E) ⟨243789963264,915064477⟩ E)) ⟨243792060336,917576744⟩ (N (N (N E ⟨243792060416,916340217⟩ E) ⟨243794157522,918328539⟩ E) ⟨243794157568,917616800⟩ (N E ⟨243802546176,922731556⟩ E))) ⟨243806740480,925293987⟩ (N (N (N (N E ⟨243810933011,956111189⟩ E) ⟨243815127414,957148530⟩ E) ⟨243815129088,930428948⟩ (N E ⟨243823517696,935577368⟩ E)) ⟨243825614848,936866574⟩ (N (N (N E ⟨243827712000,938156621⟩ E) ⟨243840294912,945914544⟩ E) ⟨243852877824,953702683⟩ (N E ⟨243857072128,956305440⟩ E)))))) ⟨243859169280,957608075⟩ (N (N (N (N (N (N (N E ⟨243861266418,959137837⟩ E) ⟨243861266432,958911549⟩ E) ⟨243865460736,961521010⟩ (N (N E ⟨243873849344,966749982⟩ E) ⟨243875946080,974876298⟩ E)) ⟨243875946496,968059317⟩ (N (N (N E ⟨243876993810,989594916⟩ E) ⟨243886432256,974618547⟩ E) ⟨243892723712,978564119⟩ (N E ⟨243907403776,987799695⟩ E))) ⟨243909500928,989122403⟩ (N (N (N (N E ⟨243910548306,1010023133⟩ E) ⟨243924180992,998404714⟩ E) ⟨243928375296,1001064305⟩ (N (N E ⟨243940958208,1009063069⟩ E) ⟨243949346816,1014412224⟩ E)) ⟨243961929728,1022460901⟩ (N (N (N E ⟨243974512640,1030539480⟩ E) ⟨243976609792,1031888815⟩ E) ⟨243987095552,1038647928⟩ (N E ⟨243991289856,1041357376⟩ E)))) ⟨243993387008,1042713343⟩ (N (N (N (N (N E ⟨243999678464,1046786213⟩ E) ⟨244005969920,1050866533⟩ E) ⟨244008067072,1052228295⟩ (N (N E ⟨244012261376,1054954299⟩ E) ⟨244026941440,1064521355⟩ E)) ⟨244041621472,1074708361⟩ (N (N (N E ⟨244041621504,1074128874⟩ E) ⟨244043718656,1075504677⟩ E) ⟨244050010112,1079637032⟩ (N E ⟨244054204416,1082396055⟩ E))) ⟨244060495872,1086540768⟩ (N (N (N (N E ⟨244062593024,1087923985⟩ E) ⟨244070981632,1093465085⟩ E) ⟨244075175936,1096240570⟩ (N E ⟨244079370240,1099019343⟩ E)) ⟨244082514965,1119917129⟩ (N (N (N E ⟨244087758848,1104586750⟩ E) ⟨244094050304,1108770927⟩ E) ⟨244099292868,1118206755⟩ (N E ⟨244115021824,1122771503⟩ E))))) ⟨244121313280,1126987653⟩ (N (N (N (N (N (N E ⟨244125507584,1129802514⟩ E) ⟨244127604736,1131211171⟩ E) ⟨244129701888,1132620647⟩ (N (N E ⟨244133896192,1135442051⟩ E) ⟨244142284800,1141094669⟩ E)) ⟨244161159168,1153860831⟩ (N (N (N E ⟨244163256320,1155283372⟩ E) ⟨244184227840,1169553596⟩ E) ⟨244188422144,1172417409⟩ (N E ⟨244192616448,1175284474⟩ E))) ⟨244196810752,1178154791⟩ (N (N (N (N E ⟨244209393664,1186785237⟩ E) ⟨244213587968,1189668547⟩ E) ⟨244217782272,1192555101⟩ (N (N E ⟨244230365184,1201234217⟩ E) ⟨244247142400,1212851715⟩ E)) ⟨244251336704,1215764178⟩ (N (N (N E ⟨244259725312,1221598797⟩ E) ⟨244263919616,1224520953⟩ E) ⟨244268113920,1227446336⟩ (N E ⟨244276502528,1233306783⟩ E)))) ⟨244280696832,1236241843⟩ (N (N (N (N (N E ⟨244293279744,1245066354⟩ E) ⟨244310056960,1256877421⟩ E) ⟨244314251264,1259838223⟩ (N (N E ⟨244322639872,1265769462⟩ E) ⟨244326834176,1268739895⟩ E)) ⟨244331028480,1271713535⟩ (N (N (N E ⟨244343611392,1280653685⟩ E) ⟨244347805696,1283640140⟩ E) ⟨244360388608,1292618700⟩ (N E ⟨244372971520,1301626024⟩ E))) ⟨244381360128,1307646867⟩ (N (N (N (N E ⟨244393943040,1316702044⟩ E) ⟨244396040192,1318214028⟩ E) ⟨244398137344,1319726806⟩ (N E ⟨244410720256,1328820187⟩ E)) ⟨244427497472,1340989189⟩ (N (N (N E ⟨244431691776,1344039375⟩ E) ⟨244444274688,1353208956⟩ E) ⟨244448468992,1356271818⟩ (N E ⟨244456857600,1362407039⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab23 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨244465246208,1368554909⟩ E) ⟨244477829120,1377800408⟩ E) ⟨244482023424,1380888553⟩ (N (N E ⟨244490412032,1387074302⟩ E) ⟨244515577856,1405707120⟩ E)) ⟨244519772160,1408823594⟩ (N (N (N E ⟨244528160768,1415065961⟩ E) ⟨244532355072,1418191851⟩ E) ⟨244544937984,1427588329⟩ (N E ⟨244549132288,1430726753⟩ E))) ⟨244561715200,1440160796⟩ (N (N (N (N E ⟨244565909504,1443311730⟩ E) ⟨244582686720,1455946682⟩ E) ⟨244595269632,1465455635⟩ (N (N E ⟨244620435456,1484557544⟩ E) ⟨244649795584,1506984292⟩ E)) ⟨244662378496,1516642175⟩ (N (N (N E ⟨244666572800,1519867648⟩ E) ⟨244679155712,1529562576⟩ E) ⟨244683350016,1532800385⟩ (N E ⟨244695932928,1542532284⟩ E)))) ⟨244698030080,1544156960⟩ (N (N (N (N (N E ⟨244716904448,1558813602⟩ E) ⟨244731584512,1570256162⟩ E) ⟨244733681664,1571893877⟩ (N (N E ⟨244737875968,1575171602⟩ E) ⟨244746264576,1581736229⟩ E)) ⟨244748361728,1583379297⟩ (N (N (N E ⟨244750458880,1585023128⟩ E) ⟨244765138944,1596551316⟩ E) ⟨244767236096,1598201251⟩ (N E ⟨244779819008,1608116853⟩ E))) ⟨244786110464,1613084928⟩ (N (N (N (N E ⟨244788207616,1614742474⟩ E) ⟨244796596224,1621380254⟩ E) ⟨244800790528,1624703700⟩ (N (N E ⟨244813373440,1634692240⟩ E) ⟨244819664896,1639696741⟩ E)) ⟨244830150656,1648052710⟩ (N (N (N E ⟨244861607936,1673233899⟩ E) ⟨244863705088,1674918675⟩ E) ⟨244865802240,1676604204⟩ (N E ⟨244867899392,1678290485⟩ E))))) ⟨244916133888,1717282122⟩ (N (N (N (N (N (N E ⟨244922425344,1722397189⟩ E) ⟨244930813952,1729227732⟩ E) ⟨244935008256,1732647479⟩ (N (N E ⟨244943396864,1739495918⟩ E) ⟨244947591168,1742924605⟩ E)) ⟨244951785472,1746356269⟩ (N (N (N E ⟨244955979776,1749790908⟩ E) ⟨244981145600,1770461124⟩ E) ⟨244989534208,1777374918⟩ (N E ⟨245000019968,1786033808⟩ E))) ⟨245002117120,1787767803⟩ (N (N (N (N E ⟨245014700032,1798187277⟩ E) ⟨245018894336,1801666336⟩ E) ⟨245056643072,1833110298⟩ (N (N E ⟨245065031680,1840130140⟩ E) ⟨245067128832,1841886932⟩ E)) ⟨245069225984,1843644455⟩ (N (N (N E ⟨245083906048,1855967592⟩ E) ⟨245086003200,1857730962⟩ E) ⟨245123751936,1889596225⟩ (N E ⟨245132140544,1896709381⟩ E)))) ⟨245136334848,1900270310⟩ (N (N (N (N (N E ⟨245148917760,1910970479⟩ E) ⟨245190860800,1946825478⟩ E) ⟨245195055104,1950426820⟩ (N (N E ⟨245199249408,1954031035⟩ E) ⟨245203443712,1957638122⟩ E)) ⟨245211832320,1964860901⟩ (N (N (N E ⟨245220220928,1972095145⟩ E) ⟨245232803840,1982967971⟩ E) ⟨245257969664,2004790710⟩ (N E ⟨245270552576,2015740523⟩ E))) ⟨245278941184,2023054602⟩ (N (N (N (N E ⟨245283135488,2026715898⟩ E) ⟨245302009856,2043226781⟩ E) ⟨245325078528,2063484459⟩ (N E ⟨245329272832,2067176835⟩ E)) ⟨245337661440,2074570028⟩ (N (N (N E ⟨245354438656,2089390126⟩ E) ⟨245362827264,2096817001⟩ E) ⟨245379604480,2111704326⟩ (N E ⟨245383798784,2115433142⟩ E)))))) ⟨245392187392,2122899141⟩ (N (N (N (N (N (N (N E ⟨245400576000,2130376285⟩ E) ⟨245413158912,2141612863⟩ E) ⟨245417353216,2145363945⟩ (N (N E ⟨245421547520,2149117802⟩ E) ⟨245442519040,2167928638⟩ E)) ⟨245471879168,2194379812⟩ (N (N (N E ⟨245530599424,2247685712⟩ E) ⟨245538988032,2255344528⟩ E) ⟨245547376640,2263014218⟩ (N E ⟨245551570944,2266853137⟩ E))) ⟨245606096896,2317005228⟩ (N (N (N (N E ⟨245631262720,2340305780⟩ E) ⟨245652234240,2359796494⟩ E) ⟨245664817152,2371522922⟩ (N (N E ⟨245673205760,2379353841⟩ E) ⟨245681594368,2387195380⟩ E)) ⟨245689982976,2395047524⟩ (N (N (N E ⟨245719343104,2422613309⟩ E) ⟨245736120320,2438423157⟩ E) ⟨245740314624,2442382187⟩ (N E ⟨245757091840,2458244512⟩ E)))) ⟨245765480448,2466191370⟩ (N (N (N (N (N E ⟨245807423488,2506081969⟩ E) ⟨245820006400,2518099748⟩ E) ⟨245849366528,2546231569⟩ (N (N E ⟨245870338048,2566402846⟩ E) ⟨245929058304,2623221909⟩ E)) ⟨245941641216,2635462120⟩ (N (N (N E ⟨245954224128,2647725038⟩ E) ⟨245987778560,2680536733⟩ E) ⟨246004555776,2697002640⟩ (N E ⟨246038110208,2730053889⟩ E))) ⟨246088441856,2779927284⟩ (N (N (N (N E ⟨246117801984,2809183125⟩ E) ⟨246138773504,2830153178⟩ E) ⟨246272991232,2965783399⟩ (N (N E ⟨246306545664,3000069919⟩ E) ⟨246356877312,3051779256⟩ E)) ⟨246419791872,3116882324⟩ (N (N (N E ⟨246428180480,3125601513⟩ E) ⟨246491095040,3191283139⟩ E) ⟨246524649472,3226519173⟩ (N E ⟨246554009600,3257466941⟩ E))))) ⟨246688227328,3400301060⟩ (N (N (N (N (N (N E ⟨246696615936,3409301120⟩ E) ⟨246725976064,3440867868⟩ E) ⟨246788890624,3508856262⟩ (N (N E ⟨246855999488,3581888716⟩ E) ⟨246893748224,3623197850⟩ E)) ⟨246969245696,3706300875⟩ (N (N (N E ⟨247027965952,3771375843⟩ E) ⟨247162183680,3921522783⟩ E) ⟨247195738112,3959357509⟩ (N E ⟨247308984320,4087902852⟩ E))) ⟨247464173568,4266122134⟩ (N (N (N (N E ⟨247577419776,4397612258⟩ E) ⟨247917158400,4798801796⟩ E) ⟨248185593856,5122196973⟩ (N (N E ⟨248227536896,5173185534⟩ E) ⟨248261091328,5214060013⟩ E)) ⟨248495972352,5502137806⟩ (N (N (N E ⟨249108340740,6265910311⟩ E) ⟨249108340754,6264432116⟩ E) ⟨249108340756,6264220981⟩ (N E ⟨249108340764,6263376529⟩ E)))) ⟨249108340768,6262954357⟩ (N (N (N (N (N E ⟨249108340788,6260844029⟩ E) ⟨249108340798,6259789198⟩ E) ⟨249108340800,6259578259⟩ (N (N E ⟨249108340804,6259156407⟩ E) ⟨249108340816,6257891063⟩ E)) ⟨249108340820,6257469353⟩ (N (N (N E ⟨249108340832,6256204436⟩ E) ⟨249108340834,6255993647⟩ E) ⟨249108340848,6254518377⟩ (N E ⟨249108340854,6253886251⟩ E))) ⟨249108340868,6252411602⟩ (N (N (N (N E ⟨249108340884,6250726821⟩ E) ⟨249108340912,6247779819⟩ E) ⟨249108340920,6246938138⟩ (N E ⟨249108340928,6246096598⟩ E)) ⟨249108340930,6245886235⟩ (N (N (N E ⟨249108340936,6245255200⟩ E) ⟨249108340946,6244203652⟩ E) ⟨249108340948,6243993369⟩ (N E ⟨249108340956,6243152325⟩ E))))))) ⟨249108340978,6240840185⟩ (N (N (N (N (N (N (N (N E ⟨249108340980,6240630044⟩ E) ⟨249108340992,6239369381⟩ E) ⟨249108340994,6239159301⟩ (N (N E ⟨249108341004,6238109036⟩ E) ⟨249108341014,6237058992⟩ E)) ⟨249108341032,6235169470⟩ (N (N (N E ⟨249108341044,6233910186⟩ E) ⟨249108341056,6232651220⟩ E) ⟨249108341088,6229295531⟩ (N E ⟨249108341090,6229085875⟩ E))) ⟨249108341104,6227618533⟩ (N (N (N (N E ⟨249108341120,6225942100⟩ E) ⟨249108341124,6225523080⟩ E) ⟨249108341136,6224266231⟩ (N (N E ⟨249108341156,6222172188⟩ E) ⟨249108341158,6221962833⟩ E)) ⟨249108341164,6221334818⟩ (N (N (N E ⟨249108341168,6220916185⟩ E) ⟨249108341170,6220706882⟩ E) ⟨249108341184,6219242008⟩ (N E ⟨249108341188,6218823551⟩ E)))) ⟨249108341202,6217359231⟩ (N (N (N (N (N E ⟨249108341220,6215477167⟩ E) ⟨249108341232,6214222853⟩ E) ⟨249108341234,6214013832⟩ (N (N E ⟨249108341236,6213804819⟩ E) ⟨249108341250,6212341976⟩ E)) ⟨249108341256,6211715175⟩ (N (N (N E ⟨249108341264,6210879563⟩ E) ⟨249108341266,6210670683⟩ E) ⟨249108341280,6209208762⟩ (N E ⟨249108341298,6207329782⟩ E))) ⟨249108341304,6206703613⟩ (N (N (N (N E ⟨249108341312,6205868844⟩ E) ⟨249108341316,6205451513⟩ E) ⟨249108341344,6202531173⟩ (N (N E ⟨249108341376,6199195745⟩ E) ⟨249108341380,6198778974⟩ E)) ⟨249108341392,6197528872⟩ (N (N (N E ⟨249108341412,6195446068⟩ E) ⟨249108341424,6194196806⟩ E) ⟨249108341428,6193780456⟩ (N E ⟨249108341440,6192531614⟩ E))))) ⟨249108341446,6191907311⟩ (N (N (N (N (N (N E ⟨249108341456,6190866981⟩ E) ⟨249108341458,6190658941⟩ E) ⟨249108341478,6188579024⟩ (N (N E ⟨249108341488,6187539393⟩ E) ⟨249108341490,6187331493⟩ E)) ⟨249108341508,6185460785⟩ (N (N (N E ⟨249108341510,6185252973⟩ E) ⟨249108341522,6184006280⟩ E) ⟨249108341542,6181929157⟩ (N E ⟨249108341544,6181721492⟩ E))) ⟨249108341554,6180683301⟩ (N (N (N (N E ⟨249108341556,6180475689⟩ E) ⟨249108341568,6179230200⟩ E) ⟨249108341572,6178815107⟩ (N (N E ⟨249108341600,6175910430⟩ E) ⟨249108341618,6174044039⟩ E)) ⟨249108341620,6173836705⟩ (N (N (N E ⟨249108341632,6172592889⟩ E) ⟨249108341648,6170934954⟩ E) ⟨249108341680,6167620754⟩ (N E ⟨249108341692,6166378502⟩ E)))) ⟨249108341700,6165550509⟩ (N (N (N (N (N E ⟨249108341712,6164308779⟩ E) ⟨249108341744,6160999027⟩ E) ⟨249108341746,6160792241⟩ (N (N E ⟨249108341748,6160585464⟩ E) ⟨249108341762,6159138268⟩ E)) ⟨249108341776,6157691497⟩ (N (N (N E ⟨249108341784,6156864961⟩ E) ⟨249108341792,6156038564⟩ E) ⟨249108341808,6154386186⟩ (N E ⟨249108341810,6154179678⟩ E))) ⟨249108341812,6153973178⟩ (N (N (N (N E ⟨249108341842,6150876724⟩ E) ⟨249108341844,6150670363⟩ E) ⟨249108341856,6149432378⟩ (N E ⟨249108341902,6144689656⟩ E)) ⟨249108341922,6142629030⟩ (N (N (N E ⟨249108341942,6140569267⟩ E) ⟨249108341952,6139539709⟩ E) ⟨249108341968,6137892866⟩ (N E ⟨249108341976,6137069651⟩ E)))))) ⟨249108341988,6135835089⟩ (N (N (N (N (N (N (N E ⟨249108342006,6133983826⟩ E) ⟨249108342020,6132544438⟩ E) ⟨249108342034,6131105473⟩ (N (N E ⟨249108342040,6130488902⟩ E) ⟨249108342064,6128023396⟩ E)) ⟨249108342072,6127201836⟩ (N (N (N E ⟨249108342080,6126380414⟩ E) ⟨249108342082,6126175080⟩ E) ⟨249108342088,6125559129⟩ (N E ⟨249108342098,6124532717⟩ E))) ⟨249108342102,6124122212⟩ (N (N (N (N E ⟨249108342130,6121249643⟩ E) ⟨249108342140,6120224133⟩ E) ⟨249108342144,6119813990⟩ (N (N E ⟨249108342156,6118583765⟩ E) ⟨249108342166,6117558814⟩ E)) ⟨249108342196,6114485248⟩ (N (N (N E ⟨249108342204,6113665957⟩ E) ⟨249108342208,6113256363⟩ E) ⟨249108342242,6109776197⟩ (N E ⟨249108342272,6106707518⟩ E)))) ⟨249108342284,6105480587⟩ (N (N (N (N (N E ⟨249108342288,6105071678⟩ E) ⟨249108342304,6103436385⟩ E) ⟨249108342320,6101801640⟩ (N (N E ⟨249108342322,6101597336⟩ E) ⟨249108342332,6100575941⟩ E)) ⟨249108342336,6100167443⟩ (N (N (N E ⟨249108342354,6098329625⟩ E) ⟨249108342364,6097308913⟩ E) ⟨249108342386,6095064101⟩ (N E ⟨249108342388,6094860078⟩ E))) ⟨249108342456,6087928386⟩ (N (N (N (N E ⟨249108342528,6080599687⟩ E) ⟨249108342530,6080396270⟩ E) ⟨249108342532,6080192861⟩ (N E ⟨249108342544,6078972585⟩ E)) ⟨249108342576,6075720015⟩ (N (N (N E ⟨249108342592,6074094545⟩ E) ⟨249108342610,6072266542⟩ E) ⟨249108342640,6069221398⟩ (N E ⟨249108342696,6063542236⟩ E))))) ⟨249108342700,6063136836⟩ (N (N (N (N (N (N E ⟨249108342720,6061110344⟩ E) ⟨249108342724,6060705147⟩ E) ⟨249108342754,6057667249⟩ (N (N E ⟨249108342766,6056452624⟩ E) ⟨249108342768,6056250215⟩ E)) ⟨249108342770,6056047816⟩ (N (N (N E ⟨249108342784,6054631256⟩ E) ⟨249108342788,6054226600⟩ E) ⟨249108342800,6053012837⟩ (N E ⟨249108342820,6050990574⟩ E))) ⟨249108342832,6049777621⟩ (N (N (N (N E ⟨249108342848,6048160824⟩ E) ⟨249108342852,6047756709⟩ E) ⟨249108342860,6046948581⟩ (N (N E ⟨249108342884,6044525006⟩ E) ⟨249108342896,6043313673⟩ E)) ⟨249108342912,6041699036⟩ (N (N (N E ⟨249108342914,6041497244⟩ E) ⟨249108342916,6041295461⟩ E) ⟨249108342928,6040084937⟩ (N E ⟨249108342960,6036858358⟩ E)))) ⟨249108342962,6036656768⟩ (N (N (N (N (N E ⟨249108342964,6036455187⟩ E) ⟨249108342976,6035245876⟩ E) ⟨249108342980,6034842840⟩ (N (N E ⟨249108342994,6033432478⟩ E) ⟨249108343024,6030411661⟩ E)) ⟨249108343088,6023973569⟩ (N (N (N E ⟨249108343104,6022365388⟩ E) ⟨249108343152,6017544067⟩ E) ⟨249108343156,6017142509⟩ (N E ⟨249108343172,6015536608⟩ E))) ⟨249108343184,6014332534⟩ (N (N (N (N E ⟨249108343186,6014131884⟩ E) ⟨249108343216,6011123143⟩ E) ⟨249108343224,6010321130⟩ (N E ⟨249108343228,6009920174⟩ E)) ⟨249108343232,6009519251⟩ (N (N (N E ⟨249108343236,6009118362⟩ E) ⟨249108343240,6008717506⟩ E) ⟨249108343252,6007515138⟩ (N E ⟨249108343280,6004710783⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab24 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨249108343292,6003509418⟩ E) ⟨249108343296,6003109029⟩ E) ⟨249108343300,6002708674⟩ (N (N E ⟨249108343344,5998306972⟩ E) ⟨249108343348,5997907018⟩ E)) ⟨249108343360,5996707354⟩ (N (N (N E ⟨249108343408,5991911698⟩ E) ⟨249108343440,5988717257⟩ E) ⟨249108343456,5987120836⟩ (N E ⟨249108343464,5986322824⟩ E))) ⟨249108343476,5985126057⟩ (N (N (N (N E ⟨249108343488,5983929588⟩ E) ⟨249108343508,5981936138⟩ E) ⟨249108343538,5978947520⟩ (N (N E ⟨249108343540,5978748345⟩ E) ⟨249108343548,5977951728⟩ E)) ⟨249108343552,5977553470⟩ (N (N (N E ⟨249108343568,5975960768⟩ E) ⟨249108343580,5974766589⟩ E) ⟨249108343600,5972776955⟩ (N E ⟨249108343616,5971185844⟩ E)))) ⟨249108343640,5968800170⟩ (N (N (N (N (N E ⟨249108343680,5964826696⟩ E) ⟨249108343688,5964032398⟩ E) ⟨249108343724,5960459692⟩ (N (N E ⟨249108343740,5958872682⟩ E) ⟨249108343744,5958476012⟩ E)) ⟨249108343762,5956691406⟩ (N (N (N E ⟨249108343808,5952133780⟩ E) ⟨249108343820,5950945552⟩ E) ⟨249108343840,5948965829⟩ (N E ⟨249108343848,5948174171⟩ E))) ⟨249108343860,5946986930⟩ (N (N (N (N E ⟨249108343868,5946195601⟩ E) ⟨249108343872,5945799986⟩ E) ⟨249108343876,5945404404⟩ (N (N E ⟨249108343904,5942636249⟩ E) ⟨249108343906,5942438585⟩ E)) ⟨249108343916,5941450390⟩ (N (N (N E ⟨249108343918,5941252776⟩ E) ⟨249108343924,5940659982⟩ E) ⟨249108343936,5939474616⟩ (N E ⟨249108343968,5936315086⟩ E))))) ⟨249108343980,5935130804⟩ (N (N (N (N (N (N E ⟨249108344012,5931974162⟩ E) ⟨249108344028,5930396628⟩ E) ⟨249108344032,5930002327⟩ (N (N E ⟨249108344044,5928819619⟩ E) ⟨249108344052,5928031311⟩ E)) ⟨249108344064,5926849095⟩ (N (N (N E ⟨249108344076,5925667173⟩ E) ⟨249108344096,5923697959⟩ E) ⟨249108344112,5922123176⟩ (N E ⟨249108344116,5921729562⟩ E))) ⟨249108344160,5917401968⟩ (N (N (N (N E ⟨249108344194,5914060625⟩ E) ⟨249108344196,5913864149⟩ E) ⟨249108344208,5912685464⟩ (N (N E ⟨249108344240,5909543739⟩ E) ⟨249108344256,5907973660⟩ E)) ⟨249108344284,5905227275⟩ (N (N (N E ⟨249108344304,5903266549⟩ E) ⟨249108344336,5900131079⟩ E) ⟨249108344360,5897780844⟩ (N E ⟨249108344368,5896997692⟩ E)))) ⟨249108344384,5895431778⟩ (N (N (N (N (N E ⟨249108344400,5893866385⟩ E) ⟨249108344432,5890737156⟩ E) ⟨249108344448,5889173320⟩ (N (N E ⟨249108344464,5887610004⟩ E) ⟨249108344484,5885656588⟩ E)) ⟨249108344488,5885266002⟩ (N (N (N E ⟨249108344496,5884484927⟩ E) ⟨249108344512,5882923166⟩ E) ⟨249108344548,5879411099⟩ (N E ⟨249108344560,5878240993⟩ E))) ⟨249108344592,5875122132⟩ (N (N (N (N E ⟨249108344624,5872005339⟩ E) ⟨249108344636,5870837075⟩ E) ⟨249108344640,5870447718⟩ (N E ⟨249108344644,5870058394⟩ E)) ⟨249108344656,5868890614⟩ (N (N (N E ⟨249108344672,5867334026⟩ E) ⟨249108344676,5866944959⟩ E) ⟨249108344688,5865777954⟩ (N E ⟨249108344692,5865389016⟩ E)))))) ⟨249108344736,5861112832⟩ (N (N (N (N (N (N (N E ⟨249108344752,5859558823⟩ E) ⟨249108344816,5853347934⟩ E) ⟨249108344836,5851408719⟩ (N (N E ⟨249108344840,5851020972⟩ E) ⟨249108344848,5850245575⟩ E)) ⟨249108344880,5847145273⟩ (N (N (N E ⟨249108344884,5846757879⟩ E) ⟨249108344896,5845595892⟩ E) ⟨249108344900,5845208627⟩ (N E ⟨249108344912,5844047024⟩ E))) ⟨249108344944,5840950827⟩ (N (N (N (N E ⟨249108344948,5840563947⟩ E) ⟨249108344956,5839790282⟩ E) ⟨249108344960,5839403498⟩ (N (N E ⟨249108344976,5837856681⟩ E) ⟨249108345008,5834764584⟩ E)) ⟨249108345024,5833219304⟩ (N (N (N E ⟨249108345040,5831674534⟩ E) ⟨249108345044,5831288422⟩ E) ⟨249108345056,5830130277⟩ (N E ⟨249108345072,5828586530⟩ E)))) ⟨249108345120,5823958356⟩ (N (N (N (N (N E ⟨249108345128,5823187441⟩ E) ⟨249108345136,5822416653⟩ E) ⟨249108345140,5822031307⟩ (N (N E ⟨249108345152,5820875459⟩ E) ⟨249108345168,5819334776⟩ E)) ⟨249108345200,5816254939⟩ (N (N (N E ⟨249108345212,5815100525⟩ E) ⟨249108345216,5814715784⟩ E) ⟨249108345228,5813561752⟩ (N E ⟨249108345236,5812792557⟩ E))) ⟨249108345260,5810485734⟩ (N (N (N (N E ⟨249108345268,5809717047⟩ E) ⟨249108345276,5808948488⟩ E) ⟨249108345280,5808564256⟩ (N (N E ⟨249108345300,5806643572⟩ E) ⟨249108345312,5805491543⟩ E)) ⟨249108345324,5804339799⟩ (N (N (N E ⟨249108345328,5803955948⟩ E) ⟨249108345404,5796668805⟩ E) ⟨249108345408,5796285588⟩ (N E ⟨249108345460,5791306650⟩ E))))) ⟨249108345484,5789010482⟩ (N (N (N (N (N (N E ⟨249108345492,5788245346⟩ E) ⟨249108345504,5787097878⟩ E) ⟨249108345512,5786333058⟩ (N (N E ⟨249108345524,5785186064⟩ E) ⟨249108345532,5784421560⟩ E)) ⟨249108345536,5784039355⟩ (N (N (N E ⟨249108345540,5783657182⟩ E) ⟨249108345568,5780982852⟩ E) ⟨249108345580,5779837184⟩ (N E ⟨249108345588,5779073563⟩ E))) ⟨249108345600,5777928368⟩ (N (N (N (N E ⟨249108345604,5777546700⟩ E) ⟨249108345608,5777165063⟩ E) ⟨249108345632,5774875902⟩ (N (N E ⟨249108345644,5773731747⟩ E) ⟨249108345648,5773350425⟩ E)) ⟨249108345652,5772969135⟩ (N (N (N E ⟨249108345664,5771825452⟩ E) ⟨249108345676,5770682053⟩ E) ⟨249108345696,5768777016⟩ (N E ⟨249108345712,5767253553⟩ E)))) ⟨249108345716,5766872766⟩ (N (N (N (N (N E ⟨249108345772,5761545044⟩ E) ⟨249108345792,5759643778⟩ E) ⟨249108345808,5758123329⟩ (N (N E ⟨249108345844,5754704155⟩ E) ⟨249108345860,5753185337⟩ E)) ⟨249108345892,5750149203⟩ (N (N (N E ⟨249108345900,5749390483⟩ E) ⟨249108345904,5749011170⟩ E) ⟨249108345920,5747494230⟩ (N E ⟨249108345956,5744082944⟩ E))) ⟨249108345968,5742946411⟩ (N (N (N (N E ⟨249108346000,5739917031⟩ E) ⟨249108346032,5736889649⟩ E) ⟨249108346048,5735376706⟩ (N E ⟨249108346064,5733864262⟩ E)) ⟨249108346148,5725932109⟩ (N (N (N E ⟨249108346152,5725554729⟩ E) ⟨249108346160,5724800064⟩ E) ⟨249108346176,5723291106⟩ (N E ⟨249108346212,5719897769⟩ E))))))) ⟨249108346220,5719144036⟩ (N (N (N (N (N (N (N (N E ⟨249108346224,5718767216⟩ E) ⟨249108346244,5716883581⟩ E) ⟨249108346256,5715753773⟩ (N (N E ⟨249108346288,5712742314⟩ E) ⟨249108346304,5711237329⟩ E)) ⟨249108346328,5708980780⟩ (N (N (N E ⟨249108346364,5705598047⟩ E) ⟨249108346368,5705222343⟩ E) ⟨249108346400,5702217819⟩ (N E ⟨249108346480,5694715161⟩ E))) ⟨249108346500,5692841425⟩ (N (N (N (N E ⟨249108346504,5692466771⟩ E) ⟨249108346544,5688721919⟩ E) ⟨249108346552,5687973318⟩ (N (N E ⟨249108346560,5687224841⟩ E) ⟨249108346588,5684606139⟩ E)) ⟨249108346600,5683484299⟩ (N (N (N E ⟨249108346608,5682736560⟩ E) ⟨249108346624,5681241451⟩ E) ⟨249108346640,5679746834⟩ (N E ⟨249108346652,5678626193⟩ E)))) ⟨249108346668,5677132436⟩ (N (N (N (N (N E ⟨249108346672,5676759073⟩ E) ⟨249108346688,5675265930⟩ E) ⟨249108346704,5673773277⟩ (N (N E ⟨249108346712,5673027135⟩ E) ⟨249108346720,5672281115⟩ E)) ⟨249108346752,5669298264⟩ (N (N (N E ⟨249108346760,5668552857⟩ E) ⟨249108346768,5667807573⟩ E) ⟨249108346792,5665572456⟩ (N E ⟨249108346864,5658873714⟩ E))) ⟨249108346892,5656271322⟩ (N (N (N (N E ⟨249108346912,5654413387⟩ E) ⟨249108346928,5652927588⟩ E) ⟨249108346940,5651813559⟩ (N (N E ⟨249108346944,5651442277⟩ E) ⟨249108346948,5651071025⟩ E)) ⟨249108346968,5649215225⟩ (N (N (N E ⟨249108346976,5648473118⟩ E) ⟨249108346984,5647731133⟩ E) ⟨249108346988,5647360187⟩ (N E ⟨249108346996,5646618384⟩ E))))) ⟨249108347040,5642540650⟩ (N (N (N (N (N (N E ⟨249108347148,5632547263⟩ E) ⟨249108347168,5630699064⟩ E) ⟨249108347176,5629959997⟩ (N (N E ⟨249108347188,5628851624⟩ E) ⟨249108347196,5628112860⟩ E)) ⟨249108347200,5627743524⟩ (N (N (N E ⟨249108347204,5627374218⟩ E) ⟨249108347232,5624789923⟩ E) ⟨249108347252,5622944906⟩ (N E ⟨249108347296,5618888532⟩ E))) ⟨249108347308,5617782883⟩ (N (N (N (N E ⟨249108347324,5616309108⟩ E) ⟨249108347328,5615940740⟩ E) ⟨249108347376,5611522675⟩ (N (N E ⟨249108347380,5611154700⟩ E) ⟨249108347424,5607108956⟩ E)) ⟨249108347440,5605638680⟩ (N (N (N E ⟨249108347444,5605271187⟩ E) ⟨249108347456,5604168887⟩ E) ⟨249108347472,5602699575⟩ (N E ⟨249108347564,5594260373⟩ E)))) ⟨249108347572,5593527281⟩ (N (N (N (N (N E ⟨249108347580,5592794309⟩ E) ⟨249108347584,5592427868⟩ E) ⟨249108347628,5588398996⟩ (N (N E ⟨249108347632,5588032915⟩ E) ⟨249108347704,5581448579⟩ E)) ⟨249108347708,5581083067⟩ (N (N (N E ⟨249108347712,5580717585⟩ E) ⟨249108347720,5579986711⟩ E) ⟨249108347728,5579255957⟩ (N E ⟨249108347756,5576699257⟩ E))) ⟨249108347760,5576334134⟩ (N (N (N (N E ⟨249108347776,5574873941⟩ E) ⟨249108347884,5565030126⟩ E) ⟨249108347888,5564665958⟩ (N E ⟨249108347904,5563209583⟩ E)) ⟨249108347908,5562845564⟩ (N (N (N E ⟨249108347948,5559207008⟩ E) ⟨249108347952,5558843317⟩ E) ⟨249108347964,5557752419⟩ (N E ⟨249108347968,5557388847⟩ E)))))) ⟨249108347984,5555934852⟩ (N (N (N (N (N (N (N E ⟨249108348012,5553391506⟩ E) ⟨249108348016,5553028290⟩ E) ⟨249108348028,5551938820⟩ (N (N E ⟨249108348076,5547583608⟩ E) ⟨249108348140,5541783302⟩ E)) ⟨249108348148,5541058797⟩ (N (N (N E ⟨249108348164,5539610142⟩ E) ⟨249108348188,5537438048⟩ E) ⟨249108348208,5535628782⟩ (N E ⟨249108348224,5534181902⟩ E))) ⟨249108348228,5533820256⟩ (N (N (N (N E ⟨249108348240,5532735494⟩ E) ⟨249108348252,5531650999⟩ E) ⟨249108348272,5529844097⟩ (N (N E ⟨249108348276,5529482805⟩ E) ⟨249108348284,5528760310⟩ E)) ⟨249108348304,5526954588⟩ (N (N (N E ⟨249108348316,5525871509⟩ E) ⟨249108348332,5524427817⟩ E) ⟨249108348336,5524066967⟩ (N E ⟨249108348340,5523706147⟩ E)))) ⟨249108348348,5522984596⟩ (N (N (N (N (N E ⟨249108348352,5522623864⟩ E) ⟨249108348404,5517937033⟩ E) ⟨249108348424,5516135729⟩ (N (N E ⟨249108348448,5513975135⟩ E) ⟨249108348456,5513255173⟩ E)) ⟨249108348460,5512895235⟩ (N (N (N E ⟨249108348464,5512535327⟩ E) ⟨249108348468,5512175449⟩ E) ⟨249108348528,5506780794⟩ (N E ⟨249108348576,5502469821⟩ E))) ⟨249108348592,5501033768⟩ (N (N (N (N E ⟨249108348596,5500674828⟩ E) ⟨249108348604,5499957036⟩ E) ⟨249108348608,5499598183⟩ (N (N E ⟨249108348640,5496728419⟩ E) ⟨249108348652,5495652740⟩ E)) ⟨249108348668,5494218911⟩ (N (N (N E ⟨249108348672,5493860527⟩ E) ⟨249108348680,5493143846⟩ E) ⟨249108348704,5490994505⟩ (N E ⟨249108348712,5490278291⟩ E))))) ⟨249108348736,5488130352⟩ (N (N (N (N (N (N E ⟨249108348748,5487056776⟩ E) ⟨249108348784,5483837624⟩ E) ⟨249108348796,5482765098⟩ (N (N E ⟨249108348832,5479549093⟩ E) ⟨249108348840,5478834745⟩ E)) ⟨249108348864,5476692401⟩ (N (N (N E ⟨249108348896,5473837572⟩ E) ⟨249108348912,5472410855⟩ E) ⟨249108348928,5470984602⟩ (N E ⟨254963597312,11205228276⟩ E))) ⟨255768903680,11688866540⟩ (N (N (N (N E ⟨257698283552,12349948495⟩ E) ⟨257698283568,12346585142⟩ E) ⟨257698283584,12343164825⟩ (N (N E ⟨257698283596,12340562231⟩ E) ⟨257698283600,12339687589⟩ E)) ⟨257698283616,12336153482⟩ (N (N (N E ⟨257698283644,12329832095⟩ E) ⟨257698283648,12328914849⟩ E) ⟨257698283760,12301795413⟩ (N E ⟨257698283780,12296661493⟩ E)))) ⟨257698283824,12285057354⟩ (N (N (N (N (N E ⟨257698283836,12281818839⟩ E) ⟨257698283844,12279642293⟩ E) ⟨257698283884,12268549382⟩ (N (N E ⟨257698283892,12266288813⟩ E) ⟨257698283920,12258266783⟩ E)) ⟨257698283928,12255943365⟩ (N (N (N E ⟨257698283992,12236854548⟩ E) ⟨257698284068,12213032487⟩ E) ⟨257698284084,12207858222⟩ (N E ⟨257698284100,12202628758⟩ E))) ⟨257698284148,12186609814⟩ (N (N (N (N E ⟨257698284168,12179789214⟩ E) ⟨257698284204,12167296205⟩ E) ⟨257698284216,12163070280⟩ (N E ⟨257698284224,12160235913⟩ E)) ⟨257698284264,12145859386⟩ (N (N (N E ⟨257698284272,12142943202⟩ E) ⟨257698284276,12141480007⟩ E) ⟨257698284320,12125160665⟩ (N E ⟨257698284340,12117607151⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab25 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨257698284416,12088133631⟩ E) ⟨257698284424,12084960423⟩ E) ⟨257698284468,12067267816⟩ (N (N E ⟨257698284472,12065639293⟩ E) ⟨257698284480,12062372211⟩ E)) ⟨257698284520,12045836385⟩ (N (N (N E ⟨257698284528,12042489202⟩ E) ⟨257698284544,12035754896⟩ E) ⟨257698284600,12011766450⟩ (N E ⟨257698284604,12010028144⟩ E))) ⟨257698284608,12008286531⟩ (N (N (N (N E ⟨257698284632,11997767492⟩ E) ⟨257698284648,11990688828⟩ E) ⟨257698284652,11988910928⟩ (N (N E ⟨257698284656,11987129735⟩ E) ⟨257698284672,11979972077⟩ E)) ⟨257698284688,11972761854⟩ (N (N (N E ⟨257698284784,11928401222⟩ E) ⟨257698284800,11920825333⟩ E) ⟨257698284804,11918923247⟩ (N E ⟨257698284860,11891954144⟩ E)))) ⟨257698284908,11868334640⟩ (N (N (N (N (N E ⟨257698284912,11866345463⟩ E) ⟨257698284924,11860358696⟩ E) ⟨257698284972,11836123755⟩ (N (N E ⟨257698285036,11803097212⟩ E) ⟨257698285060,11790503138⟩ E)) ⟨257698285088,11775666507⟩ (N (N (N E ⟨257698285104,11767119204⟩ E) ⟨257698285228,11699181498⟩ E) ⟨257698285248,11687944184⟩ (N E ⟨257698285344,11632934271⟩ E))) ⟨257698285356,11625934069⟩ (N (N (N (N E ⟨257698285368,11618906458⟩ E) ⟨257698285424,11585749762⟩ E) ⟨257698285504,11537357683⟩ (N (N E ⟨257698285528,11522606476⟩ E) ⟨257698285552,11507748077⟩ E)) ⟨257698285568,11497783098⟩ (N (N (N E ⟨257698285592,11482746822⟩ E) ⟨257698285600,11477711100⟩ E) ⟨257698285624,11462533227⟩ (N E ⟨257698285648,11447249572⟩ E))))) ⟨257698285656,11442131574⟩ (N (N (N (N (N (N E ⟨257698285680,11426707431⟩ E) ⟨257698285692,11418955982⟩ E) ⟨257698285808,11342681784⟩ (N (N E ⟨257698285824,11331971444⟩ E) ⟨257698285852,11313118536⟩ E)) ⟨257698285888,11288674548⟩ (N (N (N E ⟨257698285904,11277736995⟩ E) ⟨257698285920,11266754335⟩ E) ⟨257698285936,11255726679⟩ (N E ⟨257698285948,11247426476⟩ E))) ⟨257698285952,11244654140⟩ (N (N (N (N E ⟨257698285980,11225169539⟩ E) ⟨257698286064,11165899209⟩ E) ⟨257698286088,11148741515⟩ (N (N E ⟨257698286108,11134368152⟩ E) ⟨257698286128,11119926591⟩ E)) ⟨257698286140,11111229014⟩ (N (N (N E ⟨257698286188,11076195010⟩ E) ⟨257698286236,11040773484⟩ E) ⟨257698286344,10959674890⟩ (N E ⟨257698286376,10935277502⟩ E)))) ⟨257698286508,10832888533⟩ (N (N (N (N (N E ⟨257698286528,10817132160⟩ E) ⟨257698286576,10779059397⟩ E) ⟨257698286640,10727735161⟩ (N (N E ⟨257698286656,10714804851⟩ E) ⟨257698286720,10662690453⟩ E)) ⟨257698286784,10609953195⟩ (N (N (N E ⟨257698286816,10583353592⟩ E) ⟨257698286832,10569996506⟩ E) ⟨257698286960,10461782356⟩ (N E ⟨257698286976,10448087897⟩ E))) ⟨257698287088,10351203274⟩ (N (N (N (N E ⟨257698287104,10337218034⟩ E) ⟨257698287216,10238328368⟩ E) ⟨257698287228,10227631145⟩ (N E ⟨257698287248,10209759126⟩ E)) ⟨257698287288,10173853644⟩ (N (N (N E ⟨257698287320,10144975472⟩ E) ⟨257698287336,10130485507⟩ E) ⟨257698287408,10064865254⟩ (N E ⟨257698287496,9983753797⟩ E)))))) ⟨257698287544,9939097608⟩ (N (N (N (N (N (N (N E ⟨257698287552,9931626902⟩ E) ⟨257698287592,9894154408⟩ E) ⟨257698287648,9841363099⟩ (N (N E ⟨257698287672,9818621812⟩ E) ⟨257698287680,9811025991⟩ E)) ⟨257698287712,9780566225⟩ (N (N (N E ⟨257698287720,9772932254⟩ E) ⟨257698287800,9696178922⟩ E) ⟨257698287808,9688462628⟩ (N E ⟨257698287872,9626468354⟩ E))) ⟨257698287904,9595297185⟩ (N (N (N (N E ⟨257698287976,9524745415⟩ E) ⟨257698288000,9501101744⟩ E) ⟨257698288104,9397931607⟩ (N (N E ⟨257698288276,9224844104⟩ E) ⟨257698288432,9065342512⟩ E)) ⟨257698288440,9057101187⟩ (N (N (N E ⟨257698288576,8916113590⟩ E) ⟨257698288600,8891063937⟩ E) ⟨257698288696,8790375467⟩ (N E ⟨257698288728,8756642413⟩ E)))) ⟨257698288752,8731288062⟩ (N (N (N (N (N E ⟨257698288768,8714359474⟩ E) ⟨257698288824,8654950045⟩ E) ⟨257698288856,8620892362⟩ (N (N E ⟨257698288872,8603834184⟩ E) ⟨257698288880,8595297829⟩ E)) ⟨257698288928,8543979226⟩ (N (N (N E ⟨257698288952,8518256220⟩ E) ⟨257698288960,8509672577⟩ E) ⟨257698288984,8483894006⟩ (N E ⟨257698288992,8475292000⟩ E))) ⟨257698289008,8458074384⟩ (N (N (N (N E ⟨257698289024,8440838759⟩ E) ⟨257698289088,8371719348⟩ E) ⟨257698289136,8319698463⟩ (N (N E ⟨257698289152,8302324476⟩ E) ⟨257698289256,8188996488⟩ E)) ⟨257698289280,8162748999⟩ (N (N (N E ⟨257698289416,8013378450⟩ E) ⟨257698289472,7951574372⟩ E) ⟨257698289600,7809702995⟩ (N E ⟨257698289712,7684927063⟩ E))))) ⟨257698289856,7523717741⟩ (N (N (N (N (N (N E ⟨257698289888,7487784414⟩ E) ⟨257698289904,7469803846⟩ E) ⟨257698289976,7388781568⟩ (N (N E ⟨257698290000,7361735933⟩ E) ⟨257698290032,7325646867⟩ E)) ⟨257698290112,7235291093⟩ (N (N (N E ⟨257698290160,7180992790⟩ E) ⟨257698290176,7162880181⟩ E) ⟨257698290288,7035923973⟩ (N E ⟨257698290416,6890522706⟩ E))) ⟨257698290432,6872328267⟩ (N (N (N (N E ⟨257698290544,6744871161⟩ E) ⟨257698290616,6662862972⟩ E) ⟨257698290664,6608168465⟩ (N (N E ⟨257698290792,6462265182⟩ E) ⟨257698290824,6425784614⟩ E)) ⟨257698290880,6361945937⟩ (N (N (N E ⟨257698290920,6316351863⟩ E) ⟨257698291000,6225187053⟩ E) ⟨257698291024,6197845992⟩ (N E ⟨257698291048,6170509746⟩ E)))) ⟨257698291128,6079430538⟩ (N (N (N (N (N E ⟨257698291176,6024819718⟩ E) ⟨257698291304,5879362262⟩ E) ⟨257698291328,5852121386⟩ (N (N E ⟨257698291560,5589464713⟩ E) ⟨257698291712,5418189199⟩ E)) ⟨257845092352,5429643105⟩ (N (N (N E ⟨258650398720,5492648647⟩ E) ⟨261758377984,5736009697⟩ E) ⟨261842264064,5742526803⟩ (N E ⟨266288226352,6017013441⟩ E))) ⟨266288226360,6007167212⟩ (N (N (N (N E ⟨266288226488,5849966368⟩ E) ⟨266288226520,5810771500⟩ E) ⟨266288226536,5791190760⟩ (N E ⟨266288226648,5654452260⟩ E)) ⟨266288226792,5479551124⟩ (N (N (N E ⟨266288226800,5469866348⟩ E) ⟨266288226848,5411831800⟩ E) ⟨266288226880,5373214124⟩ (N E ⟨266288226912,5334655536⟩ E))))))) ⟨266288226920,5325025269⟩ (N (N (N (N (N (N (N (N E ⟨266288227056,5161906701⟩ E) ⟨266288227072,5142792756⟩ E) ⟨266288227176,5018964658⟩ (N (N E ⟨266288227336,4829929935⟩ E) ⟨266288227408,4745480325⟩ E)) ⟨266288227504,4633507938⟩ (N (N (N E ⟨266288227568,4559272196⟩ E) ⟨266288227632,4485377471⟩ E) ⟨266288227640,4476165075⟩ (N E ⟨266288227760,4338648401⟩ E))) ⟨266288227776,4320409500⟩ (N (N (N (N E ⟨266288227952,4121343877⟩ E) ⟨266288228080,3978439280⟩ E) ⟨266288228208,3837189707⟩ (N (N E ⟨266288228224,3819653364⟩ E) ⟨266288228336,3697664839⟩ E)) ⟨266288228536,3483272115⟩ (N (N (N E ⟨266288228688,3323417884⟩ E) ⟨266288228712,3298429467⟩ E) ⟨266288228784,3223884847⟩ (N E ⟨266288228800,3207405852⟩ E)))) ⟨266288228840,3166347375⟩ (N (N (N (N (N E ⟨266288229040,2964094154⟩ E) ⟨266288229048,2956111387⟩ E) ⟨266288229096,2908391511⟩ (N (N E ⟨266288229224,2782639106⟩ E) ⟨266288229376,2636207502⟩ E)) ⟨266288229688,2345881870⟩ (N (N (N E ⟨266288229816,2230902134⟩ E) ⟨266288229848,2202542455⟩ E) ⟨266288229864,2188420944⟩ (N E ⟨266288229976,2090668164⟩ E))) ⟨266288230120,1967847439⟩ (N (N (N (N E ⟨266288230200,1901027242⟩ E) ⟨266288230248,1861425857⟩ E) ⟨266288230272,1841764121⟩ (N (N E ⟨266288230464,1687843176⟩ E) ⟨266288230504,1656539113⟩ E)) ⟨266288230784,1444924345⟩ (N (N (N E ⟨266288230960,1318760832⟩ E) ⟨266288230968,1313153777⟩ E) ⟨266288231136,1197998146⟩ (N E ⟨266288231408,1022185846⟩ E))))) ⟨266288231520,953669250⟩ (N (N (N (N (N (N E ⟨266288231648,878168081⟩ E) ⟨266288231664,868941899⟩ E) ⟨266288231680,859762868⟩ (N (N E ⟨266288231936,719347841⟩ E) ⟨266288232016,677974142⟩ E)) ⟨266288232168,602678863⟩ (N (N (N E ⟨266288232552,431973312⟩ E) ⟨266288232832,325287065⟩ E) ⟨266288233144,224207583⟩ (N E ⟨266288233344,169311016⟩ E))) ⟨266288233348,168292016⟩ (N (N (N (N E ⟨266288233412,152408937⟩ E) ⟨266288233984,45574600⟩ E) ⟨266288234116,29855948⟩ (N (N E ⟨266288234180,23433802⟩ E) ⟨266288234296,13783017⟩ E)) ⟨266288234416,6488198⟩ (N (N (N E ⟨266288234476,3862282⟩ E) ⟨266288234496,3137894⟩ E) ⟨274878169116,4950243⟩ (N E ⟨274878169120,4773716⟩ E)))) ⟨275142415640,214⟩ (N (N (N (N (N E ⟨275142416408,212⟩ E) ⟨275142417240,209⟩ E) ⟨275154998406,16938⟩ (N (N E ⟨275154998438,16930⟩ E) ⟨275154999270,16721⟩ E)) ⟨275155000102,16515⟩ (N (N (N E ⟨275155001344,16213⟩ E) ⟨275159192904,28357⟩ E) ⟨275159194504,27688⟩ (N E ⟨275161290164,35142⟩ E))) ⟨275167584256,57752⟩ (N (N (N (N E ⟨275169678516,70112⟩ E) ⟨275171775606,80748⟩ E) ⟨275171778560,77273⟩ (N E ⟨275175970104,103810⟩ E)) ⟨275184361472,152865⟩ (N (N (N E ⟨275186455716,175378⟩ E) ⟨275186456580,173128⟩ E) ⟨275186457316,171240⟩ (N E ⟨275188555776,183739⟩ E)))))) ⟨275190648472,214016⟩ (N (N (N (N (N (N (N E ⟨275192747368,226408⟩ E) ⟨275192748136,223826⟩ E) ⟨275199040272,278521⟩ (N (N E ⟨275201138688,293395⟩ E) ⟨275203233012,327663⟩ E)) ⟨275205332992,335626⟩ (N (N (N E ⟨275207425288,384734⟩ E) ⟨275209525336,391949⟩ E) ⟨275209526168,387122⟩ (N E ⟨275209527296,380697⟩ E))) ⟨275217915904,479358⟩ (N (N (N (N E ⟨275220011244,519601⟩ E) ⟨275222107334,556247⟩ E) ⟨275222108102,549899⟩ (N (N E ⟨275222109766,536452⟩ E) ⟨275222110208,532950⟩ E)) ⟨275226303432,598902⟩ (N (N (N E ⟨275228399092,642797⟩ E) ⟨275228399860,635469⟩ E) ⟨275234691954,723174⟩ (N E ⟨275234693120,710769⟩ E)))) ⟨275240980120,864942⟩ (N (N (N (N (N E ⟨275243081728,843521⟩ E) ⟨275251470336,987641⟩ E) ⟨275255662566,1097276⟩ (N (N E ⟨275255664640,1063964⟩ E) ⟨275257756936,1186215⟩ E)) ⟨275264053248,1225138⟩ (N (N (N E ⟨275268247552,1309989⟩ E) ⟨275270341908,1410998⟩ E) ⟨275270343540,1377063⟩ (N E ⟨275272441856,1397684⟩ E))) ⟨275276636160,1488221⟩ (N (N (N (N E ⟨275285020707,1782629⟩ E) ⟨275285022690,1730462⟩ E) ⟨275285022786,1727985⟩ (N E ⟨275285024768,1677827⟩ E)) ⟨275289217220,1826471⟩ (N (N (N E ⟨275289218052,1803989⟩ E) ⟨275289218148,1801417⟩ E) ⟨275289219072,1776896⟩ (N E ⟨275293413376,1878809⟩ E))))) ⟨275301799186,2180098⟩ (N (N (N (N (N (N E ⟨275301800818,2127665⟩ E) ⟨275301801872,2094639⟩ E) ⟨275301801984,2091167⟩ (N (N E ⟨275305996288,2201614⟩ E) ⟨275318576386,2659104⟩ E)) ⟨275320672293,2773562⟩ (N (N (N E ⟨275322771684,2745084⟩ E) ⟨275322771780,2741159⟩ E) ⟨275322773504,2671850⟩ (N E ⟨275331161772,2938809⟩ E))) ⟨275339550720,3187616⟩ (N (N (N (N E ⟨275342692089,3510559⟩ E) ⟨275345839578,3526488⟩ E) ⟨275354226789,3902029⟩ (N (N E ⟨275356326980,3802467⟩ E) ⟨275356327654,3764620⟩ E)) ⟨275359468953,4140615⟩ (N (N (N E ⟨275359469321,4117731⟩ E) ⟨275359469369,4114758⟩ E) ⟨275360522240,3896370⟩ (N E ⟨275368909394,4291452⟩ E)))) ⟨275368910736,4206773⟩ (N (N (N (N (N E ⟨275368910800,4202787⟩ E) ⟨275368910848,4199801⟩ E) ⟨275376246185,4799731⟩ (N (N E ⟨275376246601,4769759⟩ E) ⟨275385686562,4950013⟩ E)) ⟨275385687904,4852321⟩ (N (N (N E ⟨275385688064,4840835⟩ E) ⟨275387785216,4924169⟩ E) ⟨275389882368,5008214⟩ (N E ⟨275396171380,5459536⟩ E))) ⟨275396172980,5330935⟩ (N (N (N (N E ⟨275402465074,5544335⟩ E) ⟨275402465280,5527442⟩ E) ⟨275403510484,5858980⟩ (N E ⟨275404560764,5757361⟩ E)) ⟨275406659584,5706216⟩ (N (N (N E ⟨275410853888,5887838⟩ E) ⟨275412949274,6138677⟩ E) ⟨275419240578,6440610⟩ (N E ⟨275419240674,6431398⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab26 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨275419242496,6259631⟩ E) ⟨275420287108,6691093⟩ E) ⟨275421338532,6460461⟩ (N (N E ⟨275426577833,7073378⟩ E) ⟨275427631104,6642822⟩ E)) ⟨275433922416,6952509⟩ (N (N (N E ⟨275436017938,7225350⟩ E) ⟨275443355465,7879552⟩ E) ⟨275443355481,7877655⟩ (N E ⟨275452795338,8048624⟩ E))) ⟨275453841604,8387769⟩ (N (N (N (N E ⟨275454890197,8441950⟩ E) ⟨275456988582,8398505⟩ E) ⟨275456991232,8073767⟩ (N (N E ⟨275458036023,8599385⟩ E) ⟨275460132697,8776395⟩ E)) ⟨275460132713,8774282⟩ (N (N (N E ⟨275473768448,8954164⟩ E) ⟨275474812839,9591407⟩ E) ⟨275482157056,9411469⟩ (N E ⟨275488444629,10343986⟩ E)))) ⟨275490543782,10160381⟩ (N (N (N (N (N E ⟨275490544742,10016228⟩ E) ⟨275490545574,9893359⟩ E) ⟨275490545664,9880181⟩ (N (N E ⟨275491590071,10577592⟩ E) ⟨275491590455,10516723⟩ E)) ⟨275492641990,10122381⟩ (N (N (N E ⟨275503126002,11018642⟩ E) ⟨275503127634,10753855⟩ E) ⟨275503128576,10604637⟩ (N E ⟨275508367255,11620234⟩ E))) ⟨275508368390,11423951⟩ (N (N (N (N E ⟨275511517184,11101868⟩ E) ⟨275519905792,11610509⟩ E) ⟨275520950500,12368216⟩ (N (N E ⟨275524097510,12334690⟩ E) ⟨275524099078,12049721⟩ E)) ⟨275524100096,11869108⟩ (N (N (N E ⟨275525144487,12703315⟩ E) ⟨275525144919,12621109⟩ E) ⟨275526196454,12141599⟩ (N E ⟨275528290202,12914851⟩ E))))) ⟨275536682130,12827986⟩ (N (N (N (N (N (N E ⟨275536682994,12664647⟩ E) ⟨275540877312,12932032⟩ E) ⟨275541922151,13744927⟩ (N (N E ⟨275541922822,13607311⟩ E) ⟨275545067434,14055264⟩ E)) ⟨275553460224,13759183⟩ (N (N (N E ⟨275555557376,13899538⟩ E) ⟨275557651974,14584390⟩ E) ⟨275557654438,14059333⟩ (N E ⟨275559749318,14689456⟩ E))) ⟨275559751680,14182388⟩ (N (N (N (N E ⟨275563943732,14960776⟩ E) ⟨275563945332,14608620⟩ E) ⟨275570237440,14901998⟩ (N (N E ⟨275571282244,15841382⟩ E) ⟨275572333116,15381489⟩ E)) ⟨275573379366,16003481⟩ (N (N (N E ⟨275582820352,15789073⟩ E) ⟨275587013162,16451408⟩ E) ⟨275587013994,16249171⟩ (N E ⟨275588059476,17097532⟩ E)))) ⟨275588060052,16950444⟩ (N (N (N (N (N E ⟨275589109252,16871799⟩ E) ⟨275589110884,16466384⟩ E) ⟨275591208960,16394726⟩ (N (N E ⟨275593301992,17597161⟩ E) ⟨275593303095,17308300⟩ E)) ⟨275593306112,16547923⟩ (N (N (N E ⟨275595401010,17271100⟩ E) ⟨275599597568,17011796⟩ E) ⟨275601694720,17167848⟩ (N E ⟨275603789362,17983752⟩ E))) ⟨275603790130,17778792⟩ (N (N (N (N E ⟨275603790994,17551691⟩ E) ⟨275603791872,17324613⟩ E) ⟨275604836676,18410207⟩ (N E ⟨275604837252,18251817⟩ E)) ⟨275605886516,18146680⟩ (N (N (N E ⟨275605886548,18138003⟩ E) ⟨275605887380,17914221⟩ E) ⟨275606933862,18567692⟩ (N E ⟨275607986176,17640284⟩ E)))))) ⟨275610079224,18923211⟩ (N (N (N (N (N (N (N E ⟨275616374784,18280189⟩ E) ⟨275620567330,19096708⟩ E) ⟨275620567426,19069408⟩ (N (N E ⟨275620568162,18861722⟩ E) ⟨275620569088,18604423⟩ E)) ⟨275622663716,19485728⟩ (N (N (N E ⟨275622663748,19476411⟩ E) ⟨275622664580,19236101⟩ E) ⟨275622665412,18999486⟩ (N E ⟨275624763392,18931512⟩ E))) ⟨275626856456,20297168⟩ (N (N (N (N E ⟨275626856504,20282526⟩ E) ⟨275626856888,20165868⟩ E) ⟨275626858278,19750539⟩ (N (N E ⟨275626859014,19534954⟩ E) ⟨275626859942,19267304⟩ E)) ⟨275626860544,19096127⟩ (N (N (N E ⟨275628957696,19261456⟩ E) ⟨275637346304,19929908⟩ E) ⟨275639440916,20872851⟩ (N E ⟨275639442676,20332628⟩ E)))) ⟨275643633320,21839579⟩ (N (N (N (N (N E ⟨275643633736,21703334⟩ E) ⟨275660410968,23171952⟩ E) ⟨275660411384,23027628⟩ (N (N E ⟨275660412710,22575035⟩ E) ⟨275660412742,22564251⟩ E)) ⟨275660413574,22286108⟩ (N (N (N E ⟨275660414976,21827036⟩ E) ⟨275662512128,22003785⟩ E) ⟨275670900736,22717919⟩ (N E ⟨275672996820,23263965⟩ E))) ⟨275674042758,24294688⟩ (N (N (N (N E ⟨275677190678,23789881⟩ E) ⟨275683483648,23810535⟩ E) ⟨275687677952,24180451⟩ (N (N E ⟨275689771413,25744982⟩ E) ⟨275689772644,25274644⟩ E)) ⟨275689772676,25262562⟩ (N (N (N E ⟨275689773412,24986644⟩ E) ⟨275691872256,24553223⟩ E) ⟨275693964968,26436365⟩ (N E ⟨275693965384,26271443⟩ E))))) ⟨275693966487,25840346⟩ (N (N (N (N (N (N E ⟨275693967174,25576303⟩ E) ⟨275693967942,25285110⟩ E) ⟨275693969408,24740680⟩ (N (N E ⟨275696066560,24928851⟩ E) ⟨275700260864,25307334⟩ E)) ⟨275706550612,26545436⟩ (N (N (N E ⟨275706550676,26520135⟩ E) ⟨275706551444,26218855⟩ E) ⟨275706551540,26181496⟩ (N E ⟨275708649472,26072867⟩ E))) ⟨275710742200,28059505⟩ (N (N (N (N E ⟨275710742600,27891174⟩ E) ⟨275723325909,28964580⟩ E) ⟨275723327172,28421958⟩ (N (N E ⟨275723327876,28125013⟩ E) ⟨275723328836,27726309⟩ E)) ⟨275723329536,27440036⟩ (N (N (N E ⟨275725426688,27638201⟩ E) ⟨275727519832,29552317⟩ E) ⟨275727520280,29354155⟩ (N E ⟨275729620992,28036674⟩ E)))) ⟨275735912448,28639739⟩ (N (N (N (N (N E ⟨275738008946,29123197⟩ E) ⟨275738009600,28842189⟩ E) ⟨275740105684,29509262⟩ (N (N E ⟨275742203904,29249229⟩ E) ⟨275744298838,30441359⟩ E)) ⟨275750592512,30071879⟩ (N (N (N E ⟨275754786816,30487487⟩ E) ⟨275756881604,31794811⟩ E) ⟨275756882372,31432644⟩ (N E ⟨275758981120,30905952⟩ E))) ⟨275761078272,31116255⟩ (N (N (N (N E ⟨275773658868,33528185⟩ E) ⟨275773658900,33512166⟩ E) ⟨275773659732,33098994⟩ (N E ⟨275777855488,32824386⟩ E)) ⟨275784146944,33476716⟩ (N (N (N E ⟨275786243624,33932121⟩ E) ⟨275786244096,33695587⟩ E) ⟨275788339978,34560530⟩ (N E ⟨275788340810,34136029⟩ E))))))) ⟨275790434805,36014708⟩ (N (N (N (N (N (N (N (N E ⟨275790435381,35705065⟩ E) ⟨275795676985,36986087⟩ E) ⟨275795677785,36544198⟩ (N (N E ⟨275795677817,36526660⟩ E) ⟨275795678424,36195972⟩ E)) ⟨275796727826,35866684⟩ (N (N (N E ⟨275796728594,35458640⟩ E) ⟨275803020624,35835949⟩ E) ⟨275803021312,35472262⟩ (N E ⟨275805116178,36931920⟩ E))) ⟨275805116946,36511359⟩ (N (N (N (N E ⟨275805117810,36045359⟩ E) ⟨275805118464,35697559⟩ E) ⟨275807215028,36238058⟩ (N (N E ⟨275812454569,38693101⟩ E) ⟨275812455017,38433725⟩ E)) ⟨275812455049,38415281⟩ (N (N (N E ⟨275812455688,38049292⟩ E) ⟨275812455720,38031078⟩ E) ⟨275819797056,38118723⟩ (N E ⟨275819797792,37703863⟩ E)))) ⟨275823992832,37757365⟩ (N (N (N (N (N E ⟨275826089984,37989802⟩ E) ⟨275829232217,40389843⟩ E) ⟨275830284288,38456819⟩ (N (N E ⟨275834478592,38926691⟩ E) ⟨275836575744,39162698⟩ E)) ⟨275842867200,39875004⟩ (N (N (N E ⟨275851255808,40834740⟩ E) ⟨275855450112,41318892⟩ E) ⟨275859643750,42220732⟩ (N E ⟨275859644416,41805899⟩ E))) ⟨275861741568,42050474⟩ (N (N (N (N E ⟨275863838720,42295762⟩ E) ⟨275865933876,43822691⟩ E) ⟨275872227328,43284056⟩ (N (N E ⟨275874323028,44481605⟩ E) ⟨275874323892,43914017⟩ E)) ⟨275876421632,43782487⟩ (N (N (N E ⟨275880613848,45679810⟩ E) ⟨275880615936,44283773⟩ E) ⟨275884810240,44787915⟩ (N E ⟨275889001059,47709693⟩ E))))) ⟨275889004544,45294912⟩ (N (N (N (N (N (N E ⟨275893198848,45804765⟩ E) ⟨275907876692,49209549⟩ E) ⟨275907877556,48579846⟩ (N (N E ⟨275911020871,50778665⟩ E) ⟨275914168312,49898729⟩ E)) ⟨275914170368,48396860⟩ (N (N (N E ⟨275924653892,51400508⟩ E) ⟨275927798103,53004793⟩ E) ⟨275930947584,50521931⟩ (N E ⟨275935141888,51060337⟩ E))) ⟨275939336192,51601597⟩ (N (N (N (N E ⟨275941433344,51873298⟩ E) ⟨275947723544,53684167⟩ E) ⟨275947724376,53024808⟩ (N (N E ⟨275947724800,52692683⟩ E) ⟨275958209220,55158944⟩ E)) ⟨275958210052,54481261⟩ (N (N (N E ⟨275958210560,54072598⟩ E) ⟨275960307712,54350722⟩ E) ⟨275961352103,58001717⟩ (N E ⟨275961352519,57640221⟩ E)))) ⟨275964500040,56545542⟩ (N (N (N (N (N E ⟨275964500072,56518559⟩ E) ⟨275964500904,55822619⟩ E) ⟨275970793472,55752046⟩ (N (N E ⟨275972890624,56034452⟩ E) ⟨275974987776,56317571⟩ E)) ⟨275977082742,58471216⟩ (N (N (N E ⟨275977084928,56601404⟩ E) ⟨275978129751,60009619⟩ E) ⟨275981277240,58889112⟩ (N E ⟨275981278008,58219245⟩ E))) ⟨275988616450,60663769⟩ (N (N (N (N E ⟨275989667840,58319386⟩ E) ⟨275991762820,60531668⟩ E) ⟨275991762852,60502762⟩ (N E ⟨275991763588,59842657⟩ E)) ⟨275993860422,60423798⟩ (N (N (N E ⟨275993862144,58897755⟩ E) ⟨275998054504,61222375⟩ E) ⟨275998056448,59478978⟩ (N E ⟨276006445056,60649986⟩ E)))))) ⟨276008540084,62899569⟩ (N (N (N (N (N (N (N E ⟨276008540852,62183732⟩ E) ⟨276008541144,61914239⟩ E) ⟨276010639360,61239770⟩ (N (N E ⟨276014832472,62935926⟩ E) ⟨276014833304,62163117⟩ E)) ⟨276014833664,61832408⟩ (N (N (N E ⟨276019027968,62427899⟩ E) ⟨276021125120,62726715⟩ E) ⟨276023222272,63026244⟩ (N E ⟨276024267460,66447615⟩ E))) ⟨276025317284,65373556⟩ (N (N (N (N E ⟨276025319424,63326487⟩ E) ⟨276027414470,65650918⟩ E) ⟨276027416576,63627443⟩ (N (N E ⟨276033706228,66287650⟩ E) ⟨276037902336,65142921⟩ E)) ⟨276042096640,65754105⟩ (N (N (N E ⟨276044192438,67402003⟩ E) ⟨276044193270,66573859⟩ E) ⟨276046287256,70119675⟩ (N E ⟨276048386936,67833906⟩ E)))) ⟨276056776704,67915716⟩ (N (N (N (N (N E ⟨276057821956,71527600⟩ E) ⟨276058872548,69564960⟩ E) ⟨276058872644,69465680⟩ (N (N E ⟨276058873476,68612627⟩ E) ⟨276063064488,72727329⟩ E)) ⟨276063064536,72674948⟩ (N (N (N E ⟨276065164200,70317318⟩ E) ⟨276065165312,69166611⟩ E) ⟨276073553920,70428916⟩ (N E ⟨276075649044,72911232⟩ E))) ⟨276075649076,72876433⟩ (N (N (N (N E ⟨276075649908,71978898⟩ E) ⟨276077748224,71064346⟩ E) ⟨276079841352,75799769⟩ (N E ⟨276079841720,75381921⟩ E)) ⟨276079841768,75327632⟩ (N (N (N E ⟨276081942528,71702629⟩ E) ⟨276090331136,72987749⟩ E) ⟨276092426244,75572287⟩ (N E ⟨276092427012,74712481⟩ E))))) ⟨276094525440,73634587⟩ (N (N (N (N (N (N E ⟨276096619000,78027180⟩ E) ⟨276105010800,75711598⟩ E) ⟨276107106322,77907784⟩ (N (N E ⟨276107108352,75592208⟩ E) ⟨276109204372,77207007⟩ E)) ⟨276109205504,75920973⟩ (N (N (N E ⟨276111302656,76250451⟩ E) ⟨276123882275,82176628⟩ E) ⟨276123883522,80658292⟩ (N E ⟨276123885568,78242285⟩ E))) ⟨276124930852,82350943⟩ (N (N (N (N E ⟨276128078630,80380024⟩ E) ⟨276132274176,79584427⟩ E) ⟨276140660818,83337697⟩ (N (N E ⟨276140661650,82311436⟩ E) ⟨276140662784,80937970⟩ E)) ⟨276144857088,81619017⟩ (N (N (N E ⟨276146950232,87010772⟩ E) ⟨276146950632,86489602⟩ E) ⟨276146950648,86468837⟩ (N E ⟨276149051392,82302914⟩ E)))) ⟨276153245696,82989660⟩ (N (N (N (N (N E ⟨276157436771,87802727⟩ E) ⟨276157438018,86180825⟩ E) ⟨276157440000,83679256⟩ (N (N E ⟨276161633284,85658138⟩ E) ⟨276161634212,84486738⟩ E)) ⟨276161634304,84371702⟩ (N (N (N E ⟨276163727864,89378945⟩ E) ⟨276163727880,89357487⟩ E) ⟨276174217216,86466133⟩ (N E ⟨276175262596,90866337⟩ E))) ⟨276176312436,89346432⟩ (N (N (N (N E ⟨276176313204,88330336⟩ E) ⟨276176314368,86817698⟩ E) ⟨276178408422,91286108⟩ (N E ⟨276190992450,91968148⟩ E)) ⟨276190993218,90922043⟩ (N (N (N E ⟨276190994432,89298592⟩ E) ⟨276192039828,93817393⟩ E) ⟨276195185238,94831174⟩ (N E ⟨276195186980,92392894⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab27 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨276195187844,91212631⟩ E) ⟨276195188580,90222056⟩ E) ⟨276199383040,90731910⟩ (N (N E ⟨276201478516,93388183⟩ E) ⟨276203577344,91452842⟩ E)) ⟨276207769714,94864273⟩ (N (N (N E ⟨276207770482,93785418⟩ E) ⟨276207771648,92176621⟩ E) ⟨276208817028,96861232⟩ (N E ⟨276211962854,97290103⟩ E))) ⟨276211965952,92903247⟩ (N (N (N (N E ⟨276214063068,93317363⟩ E) ⟨276216160256,93632721⟩ E) ⟨276224546914,97896466⟩ (N (N E ⟨276224548864,95100210⟩ E) ⟨276228741444,98324328⟩ E)) ⟨276228743168,95838225⟩ (N (N (N E ⟨276237131776,97322795⟩ E) ⟨276241324114,100977003⟩ E) ⟨276245517318,103435344⟩ (N E ⟨276245520384,98818749⟩ E)))) ⟨276248662601,104721836⟩ (N (N (N (N (N E ⟨276262295908,104436912⟩ E) ⟨276262297600,101844808⟩ E) ⟨276268588212,104288566⟩ (N (N E ⟨276274880512,104144227⟩ E) ⟨276276976828,105834005⟩ E)) ⟨276279074816,104916390⟩ (N (N (N E ⟨276287463424,106469248⟩ E) ⟨276291655906,110192916⟩ E) ⟨276291656642,108992091⟩ (N E ⟨276291656738,108836671⟩ E))) ⟨276291657728,107249943⟩ (N (N (N (N E ⟨276293751765,112752851⟩ E) ⟨276295852032,108033482⟩ E) ⟨276296897591,113202967⟩ (N (N E ⟨276300046336,108819864⟩ E) ⟨276308433138,113403551⟩ E)) ⟨276308434002,111954621⟩ (N (N (N E ⟨276313674391,117242511⟩ E) ⟨276321017856,112794423⟩ E) ⟨276325210338,116715025⟩ (N E ⟨276327306261,119299703⟩ E))))) ⟨276327309060,114427032⟩ (N (N (N (N (N (N E ⟨276329404646,117536422⟩ E) ⟨276330451623,120593030⟩ E) ⟨276330452055,119814883⟩ (N (N E ⟨276330452087,119757492⟩ E) ⟨276341987634,119903103⟩ E)) ⟨276341988466,118427782⟩ (N (N (N E ⟨276341989376,116840040⟩ E) ⟨276344086528,117248509⟩ E) ⟨276346183680,117657688⟩ (N E ⟨276347228903,123900558⟩ E))) ⟨276347229958,121959886⟩ (N (N (N (N E ⟨276347229990,121901618⟩ E) ⟨276358766592,120127676⟩ E) ⟨276362959110,124209103⟩ (N (N E ⟨276362960806,121118016⟩ E) ⟨276364006135,127340997⟩ E)) ⟨276364006551,126549859⟩ (N (N (N E ⟨276369250868,124928194⟩ E) ⟨276371349504,122623228⟩ E) ⟨276375543808,123460758⟩ (N E ⟨276379738112,124301127⟩ E)))) ⟨276380784454,128717081⟩ (N (N (N (N (N E ⟨276392321024,126839270⟩ E) ⟨276394415157,133116576⟩ E) ⟨276394418020,127559178⟩ (N (N E ⟨276396515328,127690994⟩ E) ⟨276397560135,135298755⟩ E)) ⟨276397560983,133589421⟩ (N (N (N E ⟨276398612480,128117921⟩ E) ⟨276400708146,131413388⟩ E) ⟨276400709632,128545557⟩ (N E ⟨276409096498,133678158⟩ E))) ⟨276409096530,133614424⟩ (N (N (N (N E ⟨276409097298,132096138⟩ E) ⟨276409098240,130263196⟩ E) ⟨276410144388,135277074⟩ (N E ⟨276413292544,131126271⟩ E)) ⟨276414337783,138037947⟩ (N (N (N E ⟨276414338183,137213213⟩ E) ⟨276414338886,135778614⟩ E) ⟨276425875456,133732520⟩ (N E ⟨276430068806,136525349⟩ E)))))) ⟨276430069760,134606943⟩ (N (N (N (N (N (N (N E ⟨276431114999,141699035⟩ E) ⟨276431115447,140751259⟩ E) ⟨276432166912,135045218⟩ (N (N E ⟨276436360564,137244122⟩ E) ⟨276442652658,137275683⟩ E)) ⟨276442652672,137247228⟩ (N (N (N E ⟨276443698308,143619398⟩ E) ⟨276443698884,142387616⟩ E) ⟨276444749180,139010627⟩ (N E ⟨276447893350,142959537⟩ E))) ⟨276459429226,142196065⟩ (N (N (N (N E ⟨276459429888,140807301⟩ E) ⟨276463624102,141893408⟩ E) ⟨276465719846,145351423⟩ (N (N E ⟨276467817842,143993733⟩ E) ⟨276472012800,143507116⟩ E)) ⟨276476207104,144412722⟩ (N (N (N E ⟨276480401408,145321161⟩ E) ⟨276482498560,145776443⟩ E) ⟨276492983394,150111194⟩ (N E ⟨276492983490,149897265⟩ E)))) ⟨276492984320,148063475⟩ (N (N (N (N (N E ⟨276495079780,152303140⟩ E) ⟨276495079812,152230539⟩ E) ⟨276495080644,150358020⟩ (N (N E ⟨276495081412,148655033⟩ E) ⟨276499274310,152732780⟩ E)) ⟨276499274342,152660035⟩ (N (N (N E ⟨276499275174,150783802⟩ E) ⟨276499275776,149444190⟩ E) ⟨276505567232,150831277⟩ (N E ⟨276509759890,155515426⟩ E))) ⟨276509761522,151791004⟩ (N (N (N (N E ⟨276510807780,157355746⟩ E) ⟨276516049384,161620432⟩ E) ⟨276516050184,159694425⟩ (N (N E ⟨276516050216,159617983⟩ E) ⟨276516051510,156564832⟩ E)) ⟨276526537090,159387370⟩ (N (N (N E ⟨276526538690,155643741⟩ E) ⟨276526538752,155500900⟩ E) ⟨276530733056,156443315⟩ (N E ⟨276532827384,163652359⟩ E))))) ⟨276532828774,160292204⟩ (N (N (N (N (N (N E ⟨276532828806,160215868⟩ E) ⟨276532829638,158247004⟩ E) ⟨276532830208,156915583⟩ (N (N E ⟨276547510272,160241266⟩ E) ⟨276549605974,164216771⟩ E)) ⟨276549606742,162352538⟩ (N (N (N E ⟨276549607424,160719192⟩ E) ⟨276555898880,162157212⟩ E) ⟨276562188740,167525731⟩ (N E ⟨276562189988,164447353⟩ E))) ⟨276564287488,164084468⟩ (N (N (N (N E ⟨276566383238,168029283⟩ E) ⟨276566384006,166122108⟩ E) ⟨276572676096,166023033⟩ (N (N E ⟨276576870400,166996555⟩ E) ⟨276583161206,170093357⟩ E)) ⟨276583161856,168462136⟩ (N (N (N E ⟨276589453312,169934075⟩ E) ⟨276593647616,170918899⟩ E) ⟨276595743204,175440216⟩ (N E ⟨276595743236,175356627⟩ E)))) ⟨276595743940,173530186⟩ (N (N (N (N (N E ⟨276595744068,173200665⟩ E) ⟨276595744768,171412370⟩ E) ⟨276599938470,173946831⟩ (N (N E ⟨276602034962,176166038⟩ E) ⟨276604133376,173393317⟩ E)) ⟨276610423314,178873339⟩ (N (N (N E ⟨276610424832,174886439⟩ E) ⟨276612520404,179549549⟩ E) ⟨276612521984,175385558⟩ (N E ⟨276614619136,175885384⟩ E))) ⟨276616715670,178009295⟩ (N (N (N (N E ⟨276616716288,176385914⟩ E) ⟨276620910592,177389093⟩ E) ⟨276627202048,178899154⟩ (N E ⟨276629299200,179403918⟩ E)) ⟨276631393270,188359493⟩ (N (N (N E ⟨276631396352,179909388⟩ E) ⟨276633492934,181946381⟩ E) ⟨276633493504,180415564⟩ (N E ⟨276639784960,181938323⟩ E))))))) ⟨276643979264,182957022⟩ (N (N (N (N (N (N (N (N E ⟨276648173568,183978541⟩ E) ⟨276660756042,188278161⟩ E) ⟨276660756480,187060021⟩ (N (N E ⟨276662852900,189623061⟩ E) ⟨276664950784,188092819⟩ E)) ⟨276669144658,190337463⟩ (N (N (N E ⟨276677533696,191208128⟩ E) ⟨276681728000,192252201⟩ E) ⟨276685922304,193299091⟩ (N E ⟨276690116608,194348798⟩ E))) ⟨276692213120,196732479⟩ (N (N (N (N E ⟨276692213760,194874708⟩ E) ⟨276694310912,195401322⟩ E) ⟨276696408064,195928640⟩ (N (N E ⟨276698505216,196456662⟩ E) ⟨276708990976,199107333⟩ E)) ⟨276711086706,203899137⟩ (N (N (N E ⟨276711087474,201584659⟩ E) ⟨276711088128,199639579⟩ E) ⟨276725766720,207879152⟩ (N E ⟨276725767488,205519060⟩ E)))) ⟨276727862627,212337602⟩ (N (N (N (N (N E ⟨276729962496,204461452⟩ E) ⟨276732059648,205000733⟩ E) ⟨276744642560,208251186⟩ (N (N E ⟨276748836864,209340294⟩ E) ⟨276753031168,210432214⟩ E)) ⟨276757225472,211526945⟩ (N (N (N E ⟨276761417123,221186460⟩ E) ⟨276761419776,212624487⟩ E) ⟨276763516928,213174312⟩ (N E ⟨276765614080,213724839⟩ E))) ⟨276766659655,223780054⟩ (N (N (N (N E ⟨276769808384,214828001⟩ E) ⟨276771905536,215380636⟩ E) ⟨276776099728,216847416⟩ (N (N E ⟨276778196992,217042754⟩ E) ⟨276780294144,217598198⟩ E)) ⟨276782391296,218154344⟩ (N (N (N E ⟨276783436887,228360205⟩ E) ⟨276783436935,228196156⟩ E) ⟨276786585600,219268742⟩ (N E ⟨276788682752,219826994⟩ E))))) ⟨276792876896,221469841⟩ (N (N (N (N (N (N E ⟨276794974208,221505961⟩ E) ⟨276797069956,226744336⟩ E) ⟨276797071360,222067021⟩ (N (N E ⟨276799168512,222628782⟩ E) ⟨276800214167,232817754⟩ E)) ⟨276803362482,224864457⟩ (N (N (N E ⟨276803362816,223754410⟩ E) ⟨276807557120,224882843⟩ E) ⟨276811751424,226014083⟩ (N E ⟨276813847220,231187919⟩ E))) ⟨276820140032,228284978⟩ (N (N (N (N E ⟨276827478018,237391962⟩ E) ⟨276828528640,230567093⟩ E) ⟨276830624420,235895396⟩ (N (N E ⟨276830625792,231139374⟩ E) ⟨276832722944,231712356⟩ E)) ⟨276853694072,238864190⟩ (N (N (N E ⟨276859985920,239224881⟩ E) ⟨276861032514,246676458⟩ E) ⟨276862083072,239807670⟩ (N E ⟨276867323031,251991495⟩ E)))) ⟨276867323047,251931149⟩ (N (N (N (N (N E ⟨276878860288,244495182⟩ E) ⟨276887248896,246855732⟩ E) ⟨276895637504,249227474⟩ (N (N E ⟨276897733380,254598645⟩ E) ⟨276897734116,251829762⟩ E)) ⟨276898780821,259252097⟩ (N (N (N E ⟨276899831808,250417540⟩ E) ⟨276908220416,252806061⟩ E) ⟨276914511380,256468129⟩ (N E ⟨276914511872,254604791⟩ E))) ⟨276915558724,261517588⟩ (N (N (N (N E ⟨276916609024,255205765⟩ E) ⟨276931289088,259432142⟩ E) ⟨276933386240,260038704⟩ (N E ⟨276943872000,263081985⟩ E)) ⟨276945969152,263692735⟩ (N (N (N E ⟨276950163456,264916328⟩ E) ⟨276954357760,266142713⟩ E) ⟨276962746368,268603853⟩ (N E ⟨276964843076,270998171⟩ E)))))) ⟨276966940672,269838607⟩ (N (N (N (N (N (N (N E ⟨276981619572,278959328⟩ E) ⟨276981620436,275403578⟩ E) ⟨276987912192,276054207⟩ (N (N E ⟨276994203648,277932474⟩ E) ⟨276996299586,283624187⟩ E)) ⟨276996300800,278559957⟩ (N (N (N E ⟨276998397540,280897882⟩ E) ⟨276998397952,279188135⟩ E) ⟨277000494116,283948371⟩ (N E ⟨277000495104,279817010⟩ E))) ⟨277002592256,280446582⟩ (N (N (N (N E ⟨277004689298,281535138⟩ E) ⟨277004689408,281076849⟩ E) ⟨277010980864,282971829⟩ (N (N E ⟨277013076850,288554754⟩ E) ⟨277013076882,288417474⟩ E)) ⟨277013077714,284876670⟩ (N (N (N E ⟨277013078016,283604880⟩ E) ⟨277015175168,284238628⟩ E) ⟨277017269990,294917242⟩ (N E ⟨277017272320,284873072⟩ E)))) ⟨277021466624,286144047⟩ (N (N (N (N (N E ⟨277027758080,288055726⟩ E) ⟨277029854050,293802949⟩ E) ⟨277029854082,293663163⟩ (N (N E ⟨277029854914,290057747⟩ E) ⟨277029855232,288694344⟩ E)) ⟨277034048580,294115084⟩ (N (N (N E ⟨277034049536,289973665⟩ E) ⟨277046631250,299098936⟩ E) ⟨277046632448,293828315⟩ (N E ⟨277047678660,304676645⟩ E))) ⟨277050824486,305232291⟩ (N (N (N (N E ⟨277050826752,295118758⟩ E) ⟨277067603044,304452538⟩ E) ⟨277067603076,304307824⟩ (N E ⟨277067603812,301003021⟩ E)) ⟨277067603908,300575274⟩ (N (N (N E ⟨277067603968,300308319⟩ E) ⟨277075992576,302919764⟩ E) ⟨277082283732,306243776⟩ (N E ⟨277082284032,304885635⟩ E))))) ⟨277084381184,305542313⟩ (N (N (N (N (N (N E ⟨277092769792,308175963⟩ E) ⟨277096963746,311106157⟩ E) ⟨277096964096,309496949⟩ (N (N E ⟨277101158276,311392069⟩ E) ⟨277101158400,310820709⟩ E)) ⟨277113740946,316520530⟩ (N (N (N E ⟨277113741010,316220343⟩ E) ⟨277113741312,314808624⟩ E) ⟨277117933382,326821310⟩ (N E ⟨277117935476,316799701⟩ E))) ⟨277130517474,325210590⟩ (N (N (N (N E ⟨277130518528,320164641⟩ E) ⟨277134710582,332449096⟩ E) ⟨277134711972,325637608⟩ (N (N E ⟨277134712740,321948931⟩ E) ⟨277147295744,325564966⟩ E)) ⟨277151489172,331197178⟩ (N (N (N E ⟨277164071970,335906740⟩ E) ⟨277164072802,331785118⟩ E) ⟨277164072960,331009563⟩ (N E ⟨277168267264,332377626⟩ E)))) ⟨277176655872,335122044⟩ (N (N (N (N (N E ⟨277180850176,336498398⟩ E) ⟨277193433088,340644033⟩ E) ⟨277197627170,343158091⟩ (N (N E ⟨277201821696,343421596⟩ E) ⟨277214403666,352499861⟩ E)) ⟨277214403698,352332298⟩ (N (N (N E ⟨277214404530,348010407⟩ E) ⟨277214404608,347608637⟩ E) ⟨277218598912,349009834⟩ (N E ⟨277226987520,351820500⟩ E))) ⟨277231180866,358285465⟩ (N (N (N (N E ⟨277235376128,354642191⟩ E) ⟨277237473280,355349336⟩ E) ⟨277245861888,358184803⟩ (N E ⟨277247959040,358895391⟩ E)) ⟨277268930560,366039118⟩ (N (N (N E ⟨277285707776,371803611⟩ E) ⟨277298290688,376155838⟩ E) ⟨277300387840,376883613⟩ (N E ⟨277315067026,387004191⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab28 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨277315067904,381997252⟩ E) ⟨277321358646,388288034⟩ E) ⟨277331844226,393060064⟩ (N (N E ⟨277336039424,389360750⟩ E) ⟨277348622336,393811742⟩ E)) ⟨277354913110,400071398⟩ (N (N (N E ⟨277361205248,398287384⟩ E) ⟨277365399552,399784739⟩ E) ⟨277369593856,401284830⟩ (N E ⟨277371690374,405832430⟩ E))) ⟨277388468224,408069087⟩ (N (N (N (N E ⟨277398953922,412240366⟩ E) ⟨277403148288,413383993⟩ E) ⟨277405244870,417660005⟩ (N (N E ⟨277405245440,414145997⟩ E) ⟨277415731200,417966251⟩ E)) ⟨277417827540,423805099⟩ (N (N (N E ⟨277419925504,419499128⟩ E) ⟨277422022656,420266590⟩ E) ⟨277428314112,422573066⟩ (N E ⟨277432508386,424302579⟩ E)))) ⟨277432508416,424114125⟩ (N (N (N (N (N E ⟨277445091328,428753655⟩ E) ⟨277449285632,430305614⟩ E) ⟨277453479936,431860296⟩ (N (N E ⟨277461868544,434977828⟩ E) ⟨277472354304,438890049⟩ E)) ⟨277482840064,442819267⟩ (N (N (N E ⟨277484937216,443607150⟩ E) ⟨277491228672,445974873⟩ E) ⟨277495422976,447556751⟩ (N E ⟨277499617280,449141345⟩ E))) ⟨277503811584,450728654⟩ (N (N (N (N E ⟨277505908736,451523326⟩ E) ⟨277516393842,459944851⟩ E) ⟨277528977408,460309487⟩ (N (N E ⟨277531073856,465950614⟩ E) ⟨277533171712,461915783⟩ E)) ⟨277547851776,467559152⟩ (N (N (N E ⟨277549948928,468368055⟩ E) ⟨277554143232,469987892⟩ E) ⟨277564628992,474049322⟩ (N E ⟨277575114752,478127653⟩ E))))) ⟨277579309056,479763716⟩ (N (N (N (N (N (N E ⟨277583503360,481402480⟩ E) ⟨277596086272,486334977⟩ E) ⟨277598183424,487159422⟩ (N (N E ⟨277602377728,488810336⟩ E) ⟨277612863488,492949421⟩ E)) ⟨277614960640,493779261⟩ (N (N (N E ⟨277617057792,494609774⟩ E) ⟨277625446400,497938565⟩ E) ⟨277631737856,500442230⟩ (N E ⟨277633835008,501278131⟩ E))) ⟨277635932160,502114705⟩ (N (N (N (N E ⟨277638029312,502951953⟩ E) ⟨277648515072,507148281⟩ E) ⟨277659000832,511361420⟩ (N (N E ⟨277663195136,513051380⟩ E) ⟨277669486592,515591359⟩ E)) ⟨277675778048,518137380⟩ (N (N (N E ⟨277679972352,519838085⟩ E) ⟨277700943872,528381851⟩ E) ⟨277717721088,535265113⟩ (N E ⟨277721915392,536992624⟩ E)))) ⟨277734498304,542191211⟩ (N (N (N (N (N E ⟨277747081216,547413865⟩ E) ⟨277759664128,552660564⟩ E) ⟨277765955584,555292925⟩ (N (N E ⟨277772247040,557931289⟩ E) ⟨277776441344,559693532⟩ E)) ⟨277782732800,562341895⟩ (N (N (N E ⟨277784829952,563226016⟩ E) ⟨277818384384,577462473⟩ E) ⟨277820481536,578357904⟩ (N E ⟨277822578688,579254000⟩ E))) ⟨277835161600,584644524⟩ (N (N (N (N E ⟨277843550208,588251482⟩ E) ⟨277849841664,590963666⟩ E) ⟨277851938816,591869053⟩ (N E ⟨277868716032,599136009⟩ E)) ⟨277870813184,600047359⟩ (N (N (N E ⟨277877104640,602785381⟩ E) ⟨277885493248,606445338⟩ E) ⟨277893881856,610115876⟩ (N E ⟨277898076160,611955111⟩ E)))))) ⟨277902270464,613796987⟩ (N (N (N (N (N (N (N E ⟨277904367616,614718916⟩ E) ⟨277906464768,615641506⟩ E) ⟨277919047680,621190902⟩ (N (N E ⟨277923241984,623045979⟩ E) ⟨277933727744,627695206⟩ E)) ⟨277935824896,628627029⟩ (N (N (N E ⟨277940019108,631352291⟩ E) ⟨277940019140,631053119⟩ E) ⟨277940019200,630492649⟩ (N E ⟨277956796308,639002746⟩ E))) ⟨277956796416,637981464⟩ (N (N (N (N E ⟨277969379328,643625698⟩ E) ⟨277973573632,645512367⟩ E) ⟨277986156544,651188131⟩ (N (N E ⟨277990350848,653085302⟩ E) ⟨278002933760,658792554⟩ E)) ⟨278007128064,660700215⟩ (N (N (N E ⟨278019710976,666438912⟩ E) ⟨278023905280,668357047⟩ E) ⟨278028099584,670277799⟩ (N E ⟨278032293888,672201166⟩ E)))) ⟨278036488002,676027084⟩ (N (N (N (N (N E ⟨278036488192,674127148⟩ E) ⟨278040682496,676055743⟩ E) ⟨278053265408,681857204⟩ (N (N E ⟨278065848320,687682156⟩ E) ⟨278067945472,688655264⟩ E)) ⟨278086819840,697442548⟩ (N (N (N E ⟨278091014144,699402438⟩ E) ⟨278099402752,703330025⟩ E) ⟨278103597056,705297719⟩ (N E ⟨278116179968,711216393⟩ E))) ⟨278120374272,713194479⟩ (N (N (N (N E ⟨278124568576,715175160⟩ E) ⟨278132957184,719144305⟩ E) ⟨278137151488,721132767⟩ (N (N E ⟨278158123008,731113937⟩ E) ⟨278166511616,735124522⟩ E)) ⟨278170705920,737133693⟩ (N (N (N E ⟨278187483136,745196209⟩ E) ⟨278200066048,751270196⟩ E) ⟨278204260352,753300014⟩ (N E ⟨278210551808,756349573⟩ E))))) ⟨278218940416,760424664⟩ (N (N (N (N (N (N E ⟨278235717632,768605720⟩ E) ⟨278250397696,775797869⟩ E) ⟨278271369216,786126887⟩ (N (N E ⟨278288146432,794436207⟩ E) ⟨278300729344,800695052⟩ E)) ⟨278304923648,802786443⟩ (N (N (N E ⟨278309117952,804880387⟩ E) ⟨278338478080,819609405⟩ E) ⟨278355255296,828082002⟩ (N E ⟨278372032512,836595258⟩ E))) ⟨278384615424,843006843⟩ (N (N (N (N E ⟨278393004032,847293905⟩ E) ⟨278405586944,853743484⟩ E) ⟨278422364160,862378322⟩ (N (N E ⟨278434947072,868880963⟩ E) ⟨278439141376,871053555⟩ E)) ⟨278443335680,873228667⟩ (N (N (N E ⟨278474792960,889622244⟩ E) ⟨278485278720,895118185⟩ E) ⟨278489473024,897320953⟩ (N E ⟨278502055936,903944301⟩ E)))) ⟨278504153088,905050385⟩ (N (N (N (N (N E ⟨278506250240,906157094⟩ E) ⟨278508347392,907264430⟩ E) ⟨278514638848,910590191⟩ (N (N E ⟨278518833152,912810491⟩ E) ⟨278520930304,913921579⟩ E)) ⟨278523027456,915033292⟩ (N (N (N E ⟨278537707520,922832771⟩ E) ⟨278541901824,925066810⟩ E) ⟨278552387584,930662819⟩ (N E ⟨278558679040,934027900⟩ E))) ⟨278569164800,939648817⟩ (N (N (N (N E ⟨278573359104,941901538⟩ E) ⟨278575456256,943028831⟩ E) ⟨278590136320,950937272⟩ (N E ⟨278592233472,952069532⟩ E)) ⟨278604816384,958876116⟩ (N (N (N E ⟨278611107840,962287772⟩ E) ⟨278632079360,973700179⟩ E) ⟨278634176512,974844819⟩ (N E ⟨278665633792,992088449⟩ E))))))) ⟨278671925248,995553806⟩ (N (N (N (N (N (N (N (N E ⟨278694993920,1008307444⟩ E) ⟨278703382528,1012963544⟩ E) ⟨278711771136,1017629450⟩ (N (N E ⟨278728548352,1026990643⟩ E) ⟨278745325568,1036390949⟩ E)) ⟨278762102784,1045830294⟩ (N (N (N E ⟨278772588544,1051749677⟩ E) ⟨278774685696,1052935379⟩ E) ⟨278787268608,1060062349⟩ (N E ⟨278791462912,1062442864⟩ E))) ⟨278812434432,1074381823⟩ (N (N (N (N E ⟨278829211648,1083976579⟩ E) ⟨278837600256,1088788461⟩ E) ⟨278839697408,1089992941⟩ (N (N E ⟨278841794560,1091198024⟩ E) ⟨278845988864,1093609999⟩ E)) ⟨278856474624,1099650487⟩ (N (N (N E ⟨278858571776,1100860391⟩ E) ⟨278896320512,1122741476⟩ E) ⟨278900514816,1125184711⟩ (N E ⟨278904709120,1127630341⟩ E)))) ⟨278908903424,1130078366⟩ (N (N (N (N (N E ⟨278921486336,1137436798⟩ E) ⟨278946652160,1152218158⟩ E) ⟨278967623680,1164601491⟩ (N (N E ⟨278971817984,1167085292⟩ E) ⟨279005372416,1187041101⟩ E)) ⟨279038926848,1207148283⟩ (N (N (N E ⟨279051509760,1214727371⟩ E) ⟨279055704064,1217258438⟩ E) ⟨279093452800,1240143644⟩ (N E ⟨279101841408,1245255003⟩ E))) ⟨279110230016,1250375707⟩ (N (N (N (N E ⟨279135395840,1265793778⟩ E) ⟨279160561664,1281295575⟩ E) ⟨279173144576,1289077782⟩ (N (N E ⟨279185727488,1296880815⟩ E) ⟨279189921792,1299486448⟩ E)) ⟨279194116096,1302094390⟩ (N (N (N E ⟨279198310400,1304704639⟩ E) ⟨279215087616,1315168683⟩ E) ⟨279227670528,1323040880⟩ (N E ⟨279240253440,1330933747⟩ E))))) ⟨279244447744,1333569291⟩ (N (N (N (N (N (N E ⟨279261224960,1344134366⟩ E) ⟨279273807872,1352082181⟩ E) ⟨279294779392,1365374165⟩ (N (N E ⟨279324139520,1384078469⟩ E) ⟨279363985408,1409640381⟩ E)) ⟨279378665472,1419109243⟩ (N (N (N E ⟨279397539840,1431323950⟩ E) ⟨279403831296,1435405614⟩ E) ⟨279462551552,1473743524⟩ (N E ⟨279491911680,1493075901⟩ E))) ⟨279494008832,1494460935⟩ (N (N (N (N E ⟨279500300288,1498619351⟩ E) ⟨279508688896,1504171631⟩ E) ⟨279512883200,1506951079⟩ (N (N E ⟨279521271808,1512516582⟩ E) ⟨279592574976,1560177550⟩ E)) ⟨279634518016,1588507606⟩ (N (N (N E ⟨279642906624,1594199599⟩ E) ⟨279777124352,1686437568⟩ E) ⟨279789707264,1695196449⟩ (N E ⟨279810678784,1709836685⟩ E)))) ⟨279831650304,1724529384⟩ (N (N (N (N (N E ⟨279861010432,1745186938⟩ E) ⟨279902953472,1774874411⟩ E) ⟨279995228160,1840911437⟩ (N (N E ⟨280079114240,1901798238⟩ E) ⟨280116862976,1929458859⟩ E)) ⟨280129445888,1938714835⟩ (N (N (N E ⟨280242692096,2022814864⟩ E) ⟨280397881344,2140347265⟩ E) ⟨280561459200,2267006360⟩ (N E ⟨280582430720,2283445483⟩ E))) ⟨280628568064,2319769368⟩ (N (N (N (N E ⟨280666316800,2349648990⟩ E) ⟨280850866176,2497756798⟩ E) ⟨280901197824,2538721601⟩ (N E ⟨280968306688,2593712708⟩ E)) ⟨281131884544,2729487227⟩ (N (N (N E ⟨281236742144,2817775302⟩ E) ⟨281471623168,3018919607⟩ E) ⟨281547120640,3084522572⟩ (N E ⟨281740058624,3254156315⟩ E)))))) ⟨282042048512,3524998765⟩ (N (N (N (N (N (N (N E ⟨282268540928,3731995009⟩ E) ⟨283468111874,4869028383⟩ E) ⟨283468111888,4868019153⟩ (N (N E ⟨283468111890,4867874998⟩ E) ⟨283468111892,4867730849⟩ E)) ⟨283468111910,4866433748⟩ (N (N (N E ⟨283468111922,4865569253⟩ E) ⟨283468111938,4864416893⟩ E) ⟨283468111942,4864128856⟩ (N E ⟨283468111970,4862113195⟩ E))) ⟨283468111990,4860674076⟩ (N (N (N (N E ⟨283468112000,4859954717⟩ E) ⟨283468112004,4859667010⟩ E) ⟨283468112016,4858804019⟩ (N (N E ⟨283468112022,4858372594⟩ E) ⟨283468112032,4857653661⟩ E)) ⟨283468112034,4857509890⟩ (N (N (N E ⟨283468112048,4856503643⟩ E) ⟨283468112054,4856072475⟩ E) ⟨283468112064,4855353966⟩ (N E ⟨283468112070,4854922925⟩ E)))) ⟨283468112082,4854060986⟩ (N (N (N (N (N E ⟨283468112086,4853773716⟩ E) ⟨283468112098,4852912032⟩ E) ⟨283468112102,4852624847⟩ (N (N E ⟨283468112134,4850328128⟩ E) ⟨283468112146,4849467209⟩ E)) ⟨283468112148,4849323741⟩ (N (N (N E ⟨283468112160,4848463045⟩ E) ⟨283468112166,4848032769⟩ E) ⟨283468112172,4847602540⟩ (N E ⟨283468112176,4847315747⟩ E))) ⟨283468112188,4846455496⟩ (N (N (N (N E ⟨283468112196,4845882102⟩ E) ⟨283468112226,4843732628⟩ E) ⟨283468112244,4842443516⟩ (N E ⟨283468112258,4841441170⟩ E)) ⟨283468112288,4839294158⟩ (N (N (N E ⟨283468112292,4839007980⟩ E) ⟨283468112304,4838149572⟩ E) ⟨283468112306,4838006522⟩ (N E ⟨283468112338,4835718450⟩ E))))) ⟨283468112358,4834289091⟩ (N (N (N (N (N (N E ⟨283468112364,4833860387⟩ E) ⟨283468112370,4833431730⟩ E) ⟨283468112378,4832860261⟩ (N (N E ⟨283468112380,4832717407⟩ E) ⟨283468112386,4832288877⟩ E)) ⟨283468112434,4828862344⟩ (N (N (N E ⟨283468112436,4828719638⟩ E) ⟨283468112478,4825724024⟩ E) ⟨283468112502,4824013288⟩ (N E ⟨283468112514,4823158204⟩ E))) ⟨283468112546,4820878907⟩ (N (N (N (N E ⟨283468112552,4820451689⟩ E) ⟨283468112560,4819882138⟩ E) ⟨283468112564,4819597394⟩ (N (N E ⟨283468112580,4818458629⟩ E) ⟨283468112594,4817462485⟩ E)) ⟨283468112596,4817320200⟩ (N (N (N E ⟨283468112612,4816182108⟩ E) ⟨283468112644,4813906931⟩ E) ⟨283468112658,4812911963⟩ (N E ⟨283468112674,4811775173⟩ E)))) ⟨283468112724,4808224865⟩ (N (N (N (N (N E ⟨283468112736,4807373278⟩ E) ⟨283468112772,4804819650⟩ E) ⟨283468112790,4803543471⟩ (N (N E ⟨283468112796,4803118173⟩ E) ⟨283468112802,4802692921⟩ E)) ⟨283468112808,4802267717⟩ (N (N (N E ⟨283468112822,4801275756⟩ E) ⟨283468112848,4799434223⟩ E) ⟨283468112854,4799009379⟩ (N E ⟨283468112860,4798584582⟩ E))) ⟨283468112864,4798301410⟩ (N (N (N (N E ⟨283468112866,4798159832⟩ E) ⟨283468112962,4791370223⟩ E) ⟨283468112964,4791228901⟩ (N E ⟨283468112986,4789674698⟩ E)) ⟨283468112988,4789533438⟩ (N (N (N E ⟨283468113008,4788121126⟩ E) ⟨283468113024,4786991651⟩ E) ⟨283468113090,4782336085⟩ (N E ⟨283468113092,4782195096⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab29 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨283468113122,4780080879⟩ E) ⟨283468113152,4777967830⟩ E) ⟨283468113154,4777827002⟩ (N (N E ⟨283468113156,4777686178⟩ E) ⟨283468113188,4775433713⟩ E)) ⟨283468113200,4774589381⟩ (N (N (N E ⟨283468113216,4773463895⟩ E) ⟨283468113252,4770932763⟩ E) ⟨283468113264,4770089426⟩ (N E ⟨283468113316,4766437116⟩ E))) ⟨283468113332,4765314032⟩ (N (N (N (N E ⟨283468113342,4764612272⟩ E) ⟨283468113348,4764191278⟩ E) ⟨283468113364,4763068856⟩ (N (N E ⟨283468113376,4762227256⟩ E) ⟨283468113378,4762087007⟩ E)) ⟨283468113380,4761946764⟩ (N (N (N E ⟨283468113396,4760825002⟩ E) ⟨283468113424,4758862714⟩ E) ⟨283468113428,4758582469⟩ (N E ⟨283468113444,4757461698⟩ E)))) ⟨283468113456,4756621337⟩ (N (N (N (N (N E ⟨283468113460,4756341257⟩ E) ⟨283468113476,4755221146⟩ E) ⟨283468113488,4754381279⟩ (N (N E ⟨283468113490,4754241320⟩ E) ⟨283468113508,4752981913⟩ E)) ⟨283468113520,4752142541⟩ (N (N (N E ⟨283468113524,4751862791⟩ E) ⟨283468113530,4751443205⟩ E) ⟨283468113538,4750883829⟩ (N E ⟨283468113540,4750743998⟩ E))) ⟨283468113552,4749905120⟩ (N (N (N (N E ⟨283468113586,4747529303⟩ E) ⟨283468113680,4740968595⟩ E) ⟨283468113712,4738737749⟩ (N (N E ⟨283468113728,4737622818⟩ E) ⟨283468113732,4737344136⟩ E)) ⟨283468113810,4731913941⟩ (N (N (N E ⟨283468113812,4731774808⟩ E) ⟨283468113860,4728437140⟩ E) ⟨283468113876,4727325238⟩ (N E ⟨283468113920,4724269192⟩ E))))) ⟨283468113924,4723991493⟩ (N (N (N (N (N (N E ⟨283468113968,4720938141⟩ E) ⟨283468113972,4720660686⟩ E) ⟨283468114004,4718441779⟩ (N (N E ⟨283468114098,4711931277⟩ E) ⟨283468114100,4711792878⟩ E)) ⟨283468114114,4710824226⟩ (N (N (N E ⟨283468114138,4709164258⟩ E) ⟨283468114164,4707366784⟩ E) ⟨283468114176,4706537470⟩ (N E ⟨283468114196,4705155686⟩ E))) ⟨283468114216,4703774409⟩ (N (N (N (N E ⟨283468114224,4703222040⟩ E) ⟨283468114228,4702945886⟩ E) ⟨283468114240,4702117546⟩ (N (N E ⟨283468114272,4699909530⟩ E) ⟨283468114292,4698530178⟩ E)) ⟨283468114300,4697978579⟩ (N (N (N E ⟨283468114304,4697702810⟩ E) ⟨283468114356,4694119652⟩ E) ⟨283468114368,4693293255⟩ (N E ⟨283468114396,4691365702⟩ E)))) ⟨283468114400,4691090418⟩ (N (N (N (N (N E ⟨283468114436,4688613771⟩ E) ⟨283468114444,4688063627⟩ E) ⟨283468114464,4686688620⟩ (N (N E ⟨283468114480,4685588977⟩ E) ⟨283468114494,4684627055⟩ E)) ⟨283468114496,4684489657⟩ (N (N (N E ⟨283468114500,4684214878⟩ E) ⟨283468114528,4682291984⟩ E) ⟨283468114530,4682154673⟩ (N E ⟨283468114544,4681193631⟩ E))) ⟨283468114592,4677900504⟩ (N (N (N (N E ⟨283468114608,4676803439⟩ E) ⟨283468114656,4673514172⟩ E) ⟨283468114688,4671322934⟩ (N E ⟨283468114690,4671186024⟩ E)) ⟨283468114736,4668038485⟩ (N (N (N E ⟨283468114752,4666944310⟩ E) ⟨283468114770,4665713747⟩ E) ⟨283468114784,4664756922⟩ (N E ⟨283468114788,4664483589⟩ E)))))) ⟨283468114800,4663663709⟩ (N (N (N (N (N (N (N E ⟨283468114816,4662570816⟩ E) ⟨283468114818,4662434227⟩ E) ⟨283468114820,4662297643⟩ (N (N E ⟨283468114832,4661478243⟩ E) ⟨283468114852,4660112977⟩ E)) ⟨283468114860,4659567011⟩ (N (N (N E ⟨283468114864,4659294057⟩ E) ⟨283468114880,4658202445⟩ E) ⟨283468114884,4657929591⟩ (N E ⟨283468114896,4657111151⟩ E))) ⟨283468114928,4654929523⟩ (N (N (N (N E ⟨283468114944,4653839189⟩ E) ⟨283468114960,4652749173⟩ E) ⟨283468115008,4649481041⟩ (N (N E ⟨283468115012,4649208826⟩ E) ⟨283468115040,4647303881⟩ E)) ⟨283468115060,4645943802⟩ (N (N (N E ⟨283468115072,4645127994⟩ E) ⟨283468115088,4644040529⟩ E) ⟨283468115108,4642681645⟩ (N E ⟨283468115120,4641866553⟩ E)))) ⟨283468115124,4641594895⟩ (N (N (N (N (N E ⟨283468115172,4638336554⟩ E) ⟨283468115184,4637522416⟩ E) ⟨283468115188,4637251076⟩ (N (N E ⟨283468115204,4636165916⟩ E) ⟨283468115216,4635352254⟩ E)) ⟨283468115236,4633996547⟩ (N (N (N E ⟨283468115248,4633183361⟩ E) ⟨283468115250,4633047847⟩ E) ⟨283468115356,4625872707⟩ (N E ⟨283468115376,4624520466⟩ E))) ⟨283468115388,4623709358⟩ (N (N (N (N E ⟨283468115396,4623168718⟩ E) ⟨283468115416,4621817464⟩ E) ⟨283468115456,4619116438⟩ (N (N E ⟨283468115460,4618846444⟩ E) ⟨283468115472,4618036580⟩ E)) ⟨283468115476,4617766665⟩ (N (N (N E ⟨283468115480,4617496769⟩ E) ⟨283468115504,4615877811⟩ E) ⟨283468115520,4614798899⟩ (N E ⟨283468115524,4614529221⟩ E))))) ⟨283468115538,4613585501⟩ (N (N (N (N (N (N E ⟨283468115540,4613450703⟩ E) ⟨283468115584,4610486405⟩ E) ⟨283468115612,4608601272⟩ (N (N E ⟨283468115676,4604296016⟩ E) ⟨283468115680,4604027105⟩ E)) ⟨283468115700,4602682842⟩ (N (N (N E ⟨283468115736,4600264404⟩ E) ⟨283468115760,4598652995⟩ E) ⟨283468115764,4598384496⟩ (N E ⟨283468115804,4595700578⟩ E))) ⟨283468115824,4594359353⟩ (N (N (N (N E ⟨283468115828,4594091167⟩ E) ⟨283468115836,4593554853⟩ E) ⟨283468115840,4593286726⟩ (N (N E ⟨283468115844,4593018618⟩ E) ⟨283468115852,4592482461⟩ E)) ⟨283468115872,4591142410⟩ (N (N (N E ⟨283468115892,4589802848⟩ E) ⟨283468115900,4589267161⟩ E) ⟨283468115904,4588999346⟩ (N E ⟨283468115936,4586857532⟩ E)))) ⟨283468115968,4584716968⟩ (N (N (N (N (N E ⟨283468115980,4583914578⟩ E) ⟨283468116016,4581508463⟩ E) ⟨283468116028,4580706775⟩ (N (N E ⟨283468116032,4580439585⟩ E) ⟨283468116080,4577234821⟩ E)) ⟨283468116100,4575900330⟩ (N (N (N E ⟨283468116116,4574833088⟩ E) ⟨283468116128,4574032860⟩ E) ⟨283468116144,4572966162⟩ (N E ⟨283468116164,4571633227⟩ E))) ⟨283468116180,4570567228⟩ (N (N (N (N E ⟨283468116192,4569767933⟩ E) ⟨283468116208,4568702479⟩ E) ⟨283468116224,4567637334⟩ (N E ⟨283468116228,4567371097⟩ E)) ⟨283468116240,4566572501⟩ (N (N (N E ⟨283468116256,4565507977⟩ E) ⟨283468116272,4564443764⟩ E) ⟨283468116276,4564177759⟩ (N E ⟨283468116288,4563379861⟩ E))))))) ⟨283468116384,4557002948⟩ (N (N (N (N (N (N (N (N E ⟨283468116396,4556206618⟩ E) ⟨283468116404,4555675828⟩ E) ⟨283468116420,4554614479⟩ (N (N E ⟨283468116468,4551432286⟩ E) ⟨283468116476,4550902191⟩ E)) ⟨283468116480,4550637173⟩ (N (N (N E ⟨283468116484,4550372173⟩ E) ⟨283468116496,4549577291⟩ E) ⟨283468116516,4548252873⟩ (N E ⟨283468116528,4547458454⟩ E))) ⟨283468116532,4547193686⟩ (N (N (N (N E ⟨283468116544,4546399498⟩ E) ⟨283468116580,4544017973⟩ E) ⟨283468116592,4543224479⟩ (N (N E ⟨283468116596,4542960019⟩ E) ⟨283468116608,4542166755⟩ E)) ⟨283468116612,4541902372⟩ (N (N (N E ⟨283468116624,4541109339⟩ E) ⟨283468116656,4538995431⟩ E) ⟨283468116660,4538731279⟩ (N E ⟨283468116672,4537938938⟩ E)))) ⟨283468116676,4537674863⟩ (N (N (N (N (N E ⟨283468116724,4534507458⟩ E) ⟨283468116772,4531342818⟩ E) ⟨283468116784,4530552089⟩ (N (N E ⟨283468116788,4530288551⟩ E) ⟨283468116804,4529234591⟩ E)) ⟨283468116836,4527127591⟩ (N (N (N E ⟨283468116848,4526337781⟩ E) ⟨283468116852,4526074550⟩ E) ⟨283468116864,4525284970⟩ (N E ⟨283468116868,4525021815⟩ E))) ⟨283468116880,4524232465⟩ (N (N (N (N E ⟨283468116912,4522128374⟩ E) ⟨283468116924,4521339655⟩ E) ⟨283468116928,4521076786⟩ (N (N E ⟨283468116948,4519762732⟩ E) ⟨283468116976,4517923859⟩ E)) ⟨283468116988,4517136056⟩ (N (N (N E ⟨283468117008,4515823434⟩ E) ⟨283468117020,4515036089⟩ E) ⟨283468117040,4513724230⟩ (N E ⟨283468117060,4512412847⟩ E))))) ⟨283468117080,4511101940⟩ (N (N (N (N (N (N E ⟨283468117128,4507957706⟩ E) ⟨283468117136,4507433933⟩ E) ⟨283468117148,4506648417⟩ (N (N E ⟨283468117164,4505601328⟩ E) ⟨283468117184,4504292894⟩ E)) ⟨283468117188,4504031265⟩ (N (N (N E ⟨283468117204,4502984936⟩ E) ⟨283468117212,4502461885⟩ E) ⟨283468117228,4501416012⟩ (N E ⟨283468117232,4501154592⟩ E))) ⟨283468117236,4500893190⟩ (N (N (N (N E ⟨283468117244,4500370443⟩ E) ⟨283468117248,4500109098⟩ E) ⟨283468117264,4499063908⟩ (N (N E ⟨283468117276,4498280215⟩ E) ⟨283468117288,4497496693⟩ E)) ⟨283468117300,4496713341⟩ (N (N (N E ⟨283468117312,4495930159⟩ E) ⟨283468117344,4493842509⟩ E) ⟨283468117468,4485764303⟩ (N E ⟨283468117488,4484463067⟩ E)))) ⟨283468117492,4484202876⟩ (N (N (N (N (N E ⟨283468117504,4483422418⟩ E) ⟨283468117516,4482642130⟩ E) ⟨283468117524,4482122032⟩ (N (N E ⟨283468117536,4481342026⟩ E) ⟨283468117552,4480302282⟩ E)) ⟨283468117556,4480042394⟩ (N (N (N E ⟨283468117564,4479522673⟩ E) ⟨283468117568,4479262840⟩ E) ⟨283468117572,4479003027⟩ (N E ⟨283468117588,4477963962⟩ E))) ⟨283468117600,4477184861⟩ (N (N (N (N E ⟨283468117612,4476405929⟩ E) ⟨283468117632,4475108086⟩ E) ⟨283468117708,4470180571⟩ (N E ⟨283468117724,4469144064⟩ E)) ⟨283468117728,4468884984⟩ (N (N (N E ⟨283468117744,4467848853⟩ E) ⟨283468117780,4465518654⟩ E) ⟨283468117792,4464742259⟩ (N E ⟨283468117808,4463707328⟩ E)))))) ⟨283468117828,4462414086⟩ (N (N (N (N (N (N (N E ⟨283468117844,4461379830⟩ E) ⟨283468117856,4460604335⟩ E) ⟨283468117904,4457504037⟩ (N (N E ⟨283468117920,4456471203⟩ E) ⟨283468117932,4455696774⟩ E)) ⟨283468117952,4454406433⟩ (N (N (N E ⟨283468117956,4454148421⟩ E) ⟨283468117996,4451569326⟩ E) ⟨283468118000,4451311519⟩ (N E ⟨283468118004,4451053731⟩ E))) ⟨283468118032,4449249737⟩ (N (N (N (N E ⟨283468118140,4442300030⟩ E) ⟨283468118148,4441785777⟩ E) ⟨283468118156,4441271599⟩ (N (N E ⟨283468118160,4441014537⟩ E) ⟨283468118196,4438701822⟩ E)) ⟨283468118204,4438188089⟩ (N (N (N E ⟨283468118208,4437931251⟩ E) ⟨283468118256,4434850640⟩ E) ⟨283468118288,4432798385⟩ (N E ⟨283468118320,4430747317⟩ E)))) ⟨283468118336,4429722228⟩ (N (N (N (N (N E ⟨283468118352,4428697435⟩ E) ⟨283468118372,4427416861⟩ E) ⟨283468118384,4426648739⟩ (N (N E ⟨283468118512,4418465792⟩ E) ⟨283468118528,4417444254⟩ E)) ⟨283468118532,4417188915⟩ (N (N (N E ⟨283468118536,4416933595⟩ E) ⟨283468118544,4416423011⟩ E) ⟨283468118576,4414381410⟩ (N E ⟨283468118592,4413361052⟩ E))) ⟨283468118608,4412340989⟩ (N (N (N (N E ⟨283468118640,4410301747⟩ E) ⟨283468118652,4409537335⟩ E) ⟨283468118708,4405972269⟩ (N E ⟨283468118784,4401139726⟩ E)) ⟨283468118788,4400885565⟩ (N (N (N E ⟨283468118800,4400123193⟩ E) ⟨283468118808,4399615037⟩ E) ⟨283468118828,4398344967⟩ (N E ⟨283468118876,4395298668⟩ E))))) ⟨283468118892,4394283822⟩ (N (N (N (N (N (N E ⟨283468118900,4393776508⟩ E) ⟨283468118908,4393269268⟩ E) ⟨283468118912,4393015675⟩ (N (N E ⟨283468118916,4392762101⟩ E) ⟨283468118924,4392255007⟩ E)) ⟨283468118928,4392001488⟩ (N (N (N E ⟨283468118940,4391241039⟩ E) ⟨283468118964,4389720636⟩ E) ⟨283468118976,4388960681⟩ (N E ⟨283468119048,4384404403⟩ E))) ⟨283468119064,4383392700⟩ (N (N (N (N E ⟨283468119104,4380864719⟩ E) ⟨283468119152,4377833547⟩ E) ⟨283468119156,4377581068⟩ (N (N E ⟨283468119180,4376066575⟩ E) ⟨283468119216,4373796063⟩ E)) ⟨283468119228,4373039553⟩ (N (N (N E ⟨283468119232,4372787419⟩ E) ⟨283468119252,4371527023⟩ E) ⟨283468119264,4370771004⟩ (N E ⟨283468119360,4364728729⟩ E)))) ⟨283468119372,4363974179⟩ (N (N (N (N (N E ⟨283468119408,4361711508⟩ E) ⟨283468119420,4360957610⟩ E) ⟨283468119440,4359701475⟩ (N (N E ⟨283468119456,4358696893⟩ E) ⟨283468119472,4357692601⟩ E)) ⟨283468119488,4356688597⟩ (N (N (N E ⟨283468119508,4355434000⟩ E) ⟨283468119520,4354681458⟩ E) ⟨283468119532,4353929079⟩ (N E ⟨283468119536,4353678322⟩ E))) ⟨283468119596,4349919134⟩ (N (N (N (N E ⟨283468119616,4348666973⟩ E) ⟨283468119648,4346664453⟩ E) ⟨283468119660,4345913805⟩ (N E ⟨283468119676,4344913193⟩ E)) ⟨283468119696,4343662833⟩ (N (N (N E ⟨283468119768,4339165261⟩ E) ⟨283468119792,4337667364⟩ E) ⟨283468119820,4335920635⟩ (N E ⟨283468119828,4335421731⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab30 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨283468119868,4332928287⟩ E) ⟨283468119876,4332429814⟩ E) ⟨283468119912,4330187569⟩ (N (N E ⟨283468119924,4329440477⟩ E) ⟨283468119952,4327697888⟩ E)) ⟨283468119984,4325707432⟩ (N (N (N E ⟨283468120012,4323966721⟩ E) ⟨283468120064,4320736295⟩ E) ⟨289541472256,8864094723⟩ (N E ⟨292058054672,9614042450⟩ E))) ⟨292058054676,9613477112⟩ (N (N (N (N E ⟨292058054688,9611764383⟩ E) ⟨292058054708,9608854144⟩ E) ⟨292058054724,9606475868⟩ (N (N E ⟨292058054732,9605270046⟩ E) ⟨292058054744,9603440469⟩ E)) ⟨292058054768,9599706332⟩ (N (N (N E ⟨292058054772,9599074261⟩ E) ⟨292058054792,9595872309⟩ E) ⟨292058054800,9594572124⟩ (N E ⟨292058054828,9589934243⟩ E)))) ⟨292058054832,9589260618⟩ (N (N (N (N (N E ⟨292058054848,9586538465⟩ E) ⟨292058054852,9585851016⟩ E) ⟨292058054868,9583073594⟩ (N (N E ⟨292058054896,9578106835⟩ E) ⟨292058054900,9577386266⟩ E)) ⟨292058054964,9565482705⟩ (N (N (N E ⟨292058054988,9560837450⟩ E) ⟨292058055000,9558477782⟩ E) ⟨292058055048,9548792563⟩ (N E ⟨292058055056,9547140058⟩ E))) ⟨292058055060,9546309707⟩ (N (N (N (N E ⟨292058055092,9539568604⟩ E) ⟨292058055104,9536995684⟩ E) ⟨292058055180,9520131814⟩ (N (N E ⟨292058055208,9513671785⟩ E) ⟨292058055228,9508976255⟩ E)) ⟨292058055232,9508029036⟩ (N (N (N E ⟨292058055264,9500354045⟩ E) ⟨292058055428,9458318687⟩ E) ⟨292058055436,9456153106⟩ (N E ⟨292058055484,9442936010⟩ E))))) ⟨292058055488,9441817308⟩ (N (N (N (N (N (N E ⟨292058055548,9424718715⟩ E) ⟨292058055612,9405825055⟩ E) ⟨292058055684,9383765501⟩ (N (N E ⟨292058055812,9342461357⟩ E) ⟨292058055824,9338452953⟩ E)) ⟨292058055872,9322187246⟩ (N (N (N E ⟨292058055984,9282797382⟩ E) ⟨292058055992,9279907266⟩ E) ⟨292058056016,9271175954⟩ (N E ⟨292058056104,9238381857⟩ E))) ⟨292058056148,9221527973⟩ (N (N (N (N E ⟨292058056152,9219980769⟩ E) ⟨292058056168,9213766956⟩ E) ⟨292058056240,9185311415⟩ (N (N E ⟨292058056268,9174028233⟩ E) ⟨292058056272,9172406461⟩ E)) ⟨292058056316,9154404244⟩ (N (N (N E ⟨292058056404,9117509353⟩ E) ⟨292058056428,9107242264⟩ E) ⟨292058056476,9086446334⟩ (N E ⟨292058056492,9079437069⟩ E)))) ⟨292058056528,9063525489⟩ (N (N (N (N (N E ⟨292058056572,9043814398⟩ E) ⟨292058056684,8992342568⟩ E) ⟨292058056712,8979185607⟩ (N (N E ⟨292058056716,8977296662⟩ E) ⟨292058056732,8969717485⟩ E)) ⟨292058056736,8967816847⟩ (N (N (N E ⟨292058056764,8954447076⟩ E) ⟨292058056872,8901814033⟩ E) ⟨292058056992,8841374088⟩ (N E ⟨292058057000,8837272255⟩ E))) ⟨292058057036,8818702732⟩ (N (N (N (N E ⟨292058057104,8783132897⟩ E) ⟨292058057128,8770425560⟩ E) ⟨292058057152,8757638718⟩ (N E ⟨292058057200,8731827694⟩ E)) ⟨292058057292,8681479539⟩ (N (N (N E ⟨292058057360,8643532999⟩ E) ⟨292058057408,8616376469⟩ E) ⟨292058057432,8602684040⟩ (N E ⟨292058057452,8591215845⟩ E)))))) ⟨292058057456,8588915914⟩ (N (N (N (N (N (N (N E ⟨292058057536,8542479447⟩ E) ⟨292058057552,8533092657⟩ E) ⟨292058057580,8516586550⟩ (N (N E ⟨292058057584,8514220328⟩ E) ⟨292058057712,8437428214⟩ E)) ⟨292058057808,8378487616⟩ (N (N (N E ⟨292058057840,8358588403⟩ E) ⟨292058057852,8351093963⟩ E) ⟨292058057864,8343582005⟩ (N E ⟨292058057912,8313359829⟩ E))) ⟨292058058000,8257235176⟩ (N (N (N (N E ⟨292058058072,8210634313⟩ E) ⟨292058058120,8179231664⟩ E) ⟨292058058128,8173972040⟩ (N (N E ⟨292058058168,8147563911⟩ E) ⟨292058058176,8142260373⟩ E)) ⟨292058058296,8061841726⟩ (N (N (N E ⟨292058058432,7968777808⟩ E) ⟨292058058560,7879378057⟩ E) ⟨292058058572,7870908863⟩ (N E ⟨292058058592,7856760480⟩ E)))) ⟨292058058852,7669165930⟩ (N (N (N (N (N E ⟨292058058896,7636765193⟩ E) ⟨292058059064,7511388731⟩ E) ⟨292058059152,7444693755⟩ (N (N E ⟨292058059176,7426385832⟩ E) ⟨292058059224,7389620376⟩ E)) ⟨292058059304,7327908677⟩ (N (N (N E ⟨292058059320,7315501994⟩ E) ⟨292058059352,7290625221⟩ E) ⟨292058059400,7253153301⟩ (N E ⟨292058059432,7228068886⟩ E))) ⟨292058059448,7215496092⟩ (N (N (N (N E ⟨292058059480,7190289920⟩ E) ⟨292058059608,7088674855⟩ E) ⟨292058059784,6946976558⟩ (N (N E ⟨292058059944,6816294970⟩ E) ⟨292058060040,6737085865⟩ E)) ⟨292058060064,6717193826⟩ (N (N (N E ⟨292058060072,6710555332⟩ E) ⟨292058060200,6603821877⟩ E) ⟨292058060320,6502912727⟩ (N E ⟨292058060328,6496157640⟩ E))))) ⟨292058060432,6408038825⟩ (N (N (N (N (N (N E ⟨292058060480,6367184911⟩ E) ⟨292058060576,6285146420⟩ E) ⟨292058060600,6264570370⟩ (N (N E ⟨292058060608,6257705948⟩ E) ⟨292058060624,6243968592⟩ E)) ⟨292058060656,6216460264⟩ (N (N (N E ⟨292058060736,6147499214⟩ E) ⟨292058060760,6126759638⟩ E) ⟨292058060784,6105997158⟩ (N E ⟨292058060880,6022726673⟩ E))) ⟨292058060912,5994894610⟩ (N (N (N (N E ⟨292058061040,5883217059⟩ E) ⟨292058061192,5749942243⟩ E) ⟨292058061240,5707723277⟩ (N (N E ⟨292058061320,5637232081⟩ E) ⟨292058061368,5594867171⟩ E)) ⟨292058061400,5566596758⟩ (N (N (N E ⟨292058061456,5517074737⟩ E) ⟨292058061496,5481666367⟩ E) ⟨292058061504,5474581348⟩ (N E ⟨292058061600,5389481559⟩ E)))) ⟨292058061632,5361085181⟩ (N (N (N (N (N E ⟨292058061760,5247377678⟩ E) ⟨292058061800,5211810948⟩ E) ⟨292058062224,4834429251⟩ (N (N E ⟨292058062392,4685031479⟩ E) ⟨292058062472,4613983316⟩ E)) ⟨292058062504,4585586016⟩ (N (N (N E ⟨292058062520,4571392567⟩ E) ⟨292058062552,4543016684⟩ E) ⟨292058062568,4528834498⟩ (N E ⟨292058062632,4472146979⟩ E))) ⟨292058062648,4457986019⟩ (N (N (N (N E ⟨292058062680,4429678062⟩ E) ⟨292058062776,4344874677⟩ E) ⟨292058062848,4281402733⟩ (N E ⟨292422967296,4301264662⟩ E)) ⟨295237345280,4454872555⟩ (N (N (N E ⟨300647997528,4654635218⟩ E) ⟨300647997544,4639391053⟩ E) ⟨300647997704,4487356597⟩ (N E ⟨300647997864,4336151789⟩ E))))))) ⟨300647997984,4223368803⟩ (N (N (N (N (N (N (N (N E ⟨300647997992,4215870359⟩ E) ⟨300647998240,3984805512⟩ E) ⟨300647998264,3962596178⟩ (N (N E ⟨300647998352,3881408783⟩ E) ⟨300647998520,3727551014⟩ E)) ⟨300647998528,3720263472⟩ (N (N (N E ⟨300647998544,3705699389⟩ E) ⟨300647998656,3604170856⟩ E) ⟨300647998680,3582512759⟩ (N E ⟨300647998704,3560890137⟩ E))) ⟨300647998752,3517752895⟩ (N (N (N (N E ⟨300647998800,3474762273⟩ E) ⟨300647998960,3332559134⟩ E) ⟨300647998984,3311379256⟩ (N (N E ⟨300647999112,3199111382⟩ E) ⟨300647999264,3067364681⟩ E)) ⟨300647999288,3046724305⟩ (N (N (N E ⟨300647999416,2937413488⟩ E) ⟨300647999552,2822739058⟩ E) ⟨300647999624,2762663216⟩ (N E ⟨300647999680,2716249128⟩ E)))) ⟨300647999848,2578689167⟩ (N (N (N (N (N E ⟨300648000032,2431032011⟩ E) ⟨300648000128,2355288468⟩ E) ⟨300648000144,2342752964⟩ (N (N E ⟨300648000392,2151773571⟩ E) ⟨300648000424,2127595540⟩ E)) ⟨300648000440,2115547180⟩ (N (N (N E ⟨300648000552,2031975898⟩ E) ⟨300648000696,1926535884⟩ E) ⟨300648001032,1689628045⟩ (N E ⟨300648001192,1581470155⟩ E))) ⟨300648001320,1497179022⟩ (N (N (N (N E ⟨300648001360,1471252164⟩ E) ⟨300648001592,1324838582⟩ E) ⟨300648001848,1171305448⟩ (N (N E ⟨300648001984,1093253679⟩ E) ⟨300648002096,1030840438⟩ E)) ⟨300648002312,915304170⟩ (N (N (N E ⟨300648002352,894615252⟩ E) ⟨300648002592,775188023⟩ E) ⟨300648002640,752279509⟩ (N E ⟨300648002744,703772922⟩ E))))) ⟨300648003008,587644695⟩ (N (N (N (N (N (N E ⟨300648003360,448674736⟩ E) ⟨300648003720,325618895⟩ E) ⟨300648004056,228401376⟩ (N (N E ⟨300648004072,224199490⟩ E) ⟨300648004176,197837495⟩ E)) ⟨300648004456,135064409⟩ (N (N (N E ⟨300648004692,91459105⟩ E) ⟨300648004756,81101145⟩ E) ⟨300648004992,48310569⟩ (N E ⟨300648005632,1958320⟩ E))) ⟨309237940232,3640140⟩ (N (N (N (N E ⟨309237940368,488698⟩ E) ⟨309237940384,310153⟩ E) ⟨309472829440,120⟩ (N (N E ⟨309481218048,6134⟩ E) ⟨309483313158,9304⟩ E)) ⟨309500092118,53058⟩ (N (N (N E ⟨309510578176,98661⟩ E) ⟨309516868454,135047⟩ E) ⟨309516869096,133904⟩ (N E ⟨309518966784,145526⟩ E)))) ⟨309523161088,172364⟩ (N (N (N (N (N E ⟨309531549696,232852⟩ E) ⟨309533646848,249393⟩ E) ⟨309550424064,402164⟩ (N (N E ⟨309565104128,565654⟩ E) ⟨309577687040,727942⟩ E)) ⟨309586075648,847497⟩ (N (N (N E ⟨309592367104,943129⟩ E) ⟨309615435776,1337546⟩ E) ⟨309619629832,1421296⟩ (N E ⟨309653183464,2161092⟩ E))) ⟨309653184512,2131341⟩ (N (N (N (N E ⟨309661573120,2332763⟩ E) ⟨309665767424,2436888⟩ E) ⟨309669960824,2573874⟩ (N E ⟨309686736328,3097256⟩ E)) ⟨309686737096,3065774⟩ (N (N (N E ⟨309686738944,2991645⟩ E) ⟨309699321716,3358015⟩ E) ⟨309720291560,4094936⟩ (N E ⟨309720292392,4049987⟩ E)))))) ⟨309720293224,4005654⟩ (N (N (N (N (N (N (N E ⟨309732876288,4412429⟩ E) ⟨309737068824,4663169⟩ E) ⟨309745459200,4847734⟩ (N (N E ⟨309749652358,5073734⟩ E) ⟨309753846024,5272435⟩ E)) ⟨309753846856,5214568⟩ (N (N (N E ⟨309764332468,5620319⟩ E) ⟨309764333332,5556422⟩ E) ⟨309766430720,5618795⟩ (N E ⟨309770624120,5849353⟩ E))) ⟨309783207936,6276650⟩ (N (N (N (N E ⟨309787402240,6446809⟩ E) ⟨309795790848,6793964⟩ E) ⟨309797887764,6903665⟩ (N (N E ⟨309799985152,6970959⟩ E) ⟨309814664932,7636987⟩ E)) ⟨309850316800,9272668⟩ (N (N (N E ⟨309854511104,9479293⟩ E) ⟨309862899712,9899382⟩ E) ⟨309867094016,10112846⟩ (N E ⟨309879676928,10766918⟩ E)))) ⟨309883871232,10989502⟩ (N (N (N (N (N E ⟨309900648448,11902640⟩ E) ⟨309917425664,12852263⟩ E) ⟨309921619968,13095369⟩ (N (N E ⟨309925814272,13340756⟩ E) ⟨309930008576,13588424⟩ E)) ⟨309946785792,14601901⟩ (N (N (N E ⟨309988728832,17295249⟩ E) ⟨309997117394,17872143⟩ E) ⟨309997117440,17861289⟩ (N E ⟨310001311060,18312570⟩ E))) ⟨310013894562,19044370⟩ (N (N (N (N E ⟨310034866176,20521384⟩ E) ⟨310051643392,21762956⟩ E) ⟨310060032000,22397430⟩ (N E ⟨310093586432,25026566⟩ E)) ⟨310101975040,25706660⟩ (N (N (N E ⟨310118752256,27094221⟩ E) ⟨310131335168,28158842⟩ E) ⟨310135529472,28518277⟩ (N E ⟨310143918080,29243990⟩ E))))) ⟨310148112384,29610268⟩ (N (N (N (N (N (N E ⟨310169083904,31475866⟩ E) ⟨310181666816,32622592⟩ E) ⟨310185861120,33009395⟩ (N (N E ⟨310198444032,34183485⟩ E) ⟨310238288630,38691697⟩ E)) ⟨310248775680,39085055⟩ (N (N (N E ⟨310255067136,39720834⟩ E) ⟨310265552896,40791863⟩ E) ⟨310271843094,42136925⟩ (N E ⟨310271844352,41441319⟩ E))) ⟨310286524416,42976657⟩ (N (N (N (N E ⟨310288620294,43932686⟩ E) ⟨310301204480,44539912⟩ E) ⟨310315884544,46131080⟩ (N (N E ⟨310322175590,47075900⟩ E) ⟨310328467456,47517153⟩ E)) ⟨310338952022,49463128⟩ (N (N (N E ⟨310355729222,51407096⟩ E) ⟨310355730054,50843947⟩ E) ⟨310355730432,50590642⟩ (N E ⟨310362021888,51313575⟩ E)))) ⟨310366216192,51798377⟩ (N (N (N (N (N E ⟨310368313344,52041632⟩ E) ⟨310372507318,52759374⟩ E) ⟨310382993408,53760355⟩ (N (N E ⟨310389284518,54755226⟩ E) ⟨310412353536,57281470⟩ E)) ⟨310502531072,68793446⟩ (N (N (N E ⟨310525599528,72112668⟩ E) ⟨310536085504,73345280⟩ E) ⟨310542376960,74214939⟩ (N E ⟨310554959872,75969590⟩ E))) ⟨310559153160,77594794⟩ (N (N (N (N E ⟨310559153992,76745310⟩ E) ⟨310588514304,80748581⟩ E) ⟨310592708608,81356172⟩ (N E ⟨310596902912,81966032⟩ E)) ⟨310622068422,86028988⟩ (N (N (N E ⟨310655623168,90742288⟩ E) ⟨310670302996,93296195⟩ E) ⟨310701760512,97949644⟩ (N E ⟨310722732032,101316318⟩ E))))))))

#eval IO.monoMsNow
noncomputable def tab31 : CTN :=
  (N (N (N (N (N (N (N (N (N E ⟨310752092160,106124728⟩ E) ⟨310773063680,109627172⟩ E) ⟨310789840896,112469826⟩ (N (N E ⟨310819201024,117531468⟩ E) ⟨310840172544,121214678⟩ E)) ⟨310856949760,124201875⟩ (N (N (N E ⟨310865338368,125709009⟩ E) ⟨310869532672,126465960⟩ E) ⟨310873726976,127225166⟩ (N E ⟨310877921280,127986627⟩ E))) ⟨310890504192,130284536⟩ (N (N (N (N E ⟨310907281408,133379967⟩ E) ⟨310924058624,136511441⟩ E) ⟨310949224448,141276196⟩ (N (N E ⟨310957613056,142882450⟩ E) ⟨310970195968,145308700⟩ E)) ⟨310991167488,149397415⟩ (N (N (N E ⟨311020527616,155215977⟩ E) ⟨311058276352,162858593⟩ E) ⟨311060373504,163288510⟩ (N E ⟨311093927936,170243364⟩ E)))) ⟨311108608000,173331185⟩ (N (N (N (N (N E ⟨311127482368,177341520⟩ E) ⟨311144259158,181965711⟩ E) ⟨311161036358,185664048⟩ (N (N E ⟨311161036800,184582800⟩ E) ⟨311175716864,187795821⟩ E)) ⟨311177814016,188257056⟩ (N (N (N E ⟨311188299776,190571604⟩ E) ⟨311190396928,191036187⟩ E) ⟨311194591232,191967026⟩ (N E ⟨311200882688,193367467⟩ E))) ⟨311205076992,194303882⟩ (N (N (N (N E ⟨311217659904,197126504⟩ E) ⟨311221854208,198071835⟩ E) ⟨311255408640,205714670⟩ (N (N E ⟨311263797248,207647638⟩ E) ⟨311347683328,227466146⟩ E)) ⟨311368654848,232559418⟩ (N (N (N E ⟨311385432064,236673892⟩ E) ⟨311404306432,241344988⟩ E) ⟨311421083648,245534652⟩ (N E ⟨311452540928,253485503⟩ E))))) ⟨311473512448,258855000⟩ (N (N (N (N (N (N E ⟨311486095360,262103140⟩ E) ⟨311528038400,273073316⟩ E) ⟨311532232704,274182425⟩ (N (N E ⟨311576272896,285960600⟩ E) ⟨311578370048,286527497⟩ E)) ⟨311595147264,291082386⟩ (N (N (N E ⟨311616118784,296825253⟩ E) ⟨311628701696,300297219⟩ E) ⟨311645478912,304957099⟩ (N E ⟨311674839040,313195924⟩ E))) ⟨311679033344,314381622⟩ (N (N (N (N E ⟨311691616256,317951788⟩ E) ⟨311695810560,319146199⟩ E) ⟨311712587776,323945608⟩ (N (N E ⟨311729364992,328779816⟩ E) ⟨311741947904,332428288⟩ E)) ⟨311762919424,338552489⟩ (N (N (N E ⟨311792279552,347217429⟩ E) ⟨311796473856,348463941⟩ E) ⟨311809056768,352216456⟩ (N E ⟨311859388416,367420971⟩ E)))) ⟨311863582720,368702038⟩ (N (N (N (N (N E ⟨311888748544,376433671⟩ E) ⟨311966343168,400759868⟩ E) ⟨311993606144,409481003⟩ (N (N E ⟨312022966272,418973928⟩ E) ⟨312060715008,431332583⟩ E)) ⟨312127823872,453728457⟩ (N (N (N E ⟨312157184000,463697128⟩ E) ⟨312257847296,498659321⟩ E) ⟨312287207424,509084320⟩ (N E ⟨312291401728,510581970⟩ E))) ⟨312362704896,536361047⟩ (N (N (N (N E ⟨312400453632,550251993⟩ E) ⟨312467562496,575360664⟩ E) ⟨312475951104,578536356⟩ (N E ⟨312496922624,586511558⟩ E)) ⟨312501116928,588112759⟩ (N (N (N E ⟨312534671360,600996170⟩ E) ⟨312559837184,610744663⟩ E) ⟨312597585920,625505106⟩ (N E ⟨312631140352,638763806⟩ E)))))) ⟨312664694784,652152247⟩ (N (N (N (N (N (N (N E ⟨312668889088,653834903⟩ E) ⟨312694054912,663973230⟩ E) ⟨312765358080,693091791⟩ (N (N E ⟨312828272640,719264896⟩ E) ⟨312866021376,735183605⟩ E)) ⟨312874409984,738742896⟩ (N (N (N E ⟨312933130240,763879059⟩ E) ⟨312958296064,774769769⟩ E) ⟨313063153664,820904978⟩ (N E ⟨313272868864,916792057⟩ E))) ⟨313281257472,920726559⟩ (N (N (N (N E ⟨313365143552,960485267⟩ E) ⟨313549692928,1050570332⟩ E) ⟨313604218880,1077864765⟩ (N (N E ⟨313633579008,1092688340⟩ E) ⟨314673766400,1671772511⟩ E)) ⟨317827883060,3889444660⟩ (N (N (N E ⟨317827883126,3886057420⟩ E) ⟨317827883140,3885339388⟩ E) ⟨317827883334,3875406578⟩ (N E ⟨317827883348,3874691006⟩ E)))) ⟨317827883366,3873771228⟩ (N (N (N (N (N E ⟨317827883398,3872136740⟩ E) ⟨317827883430,3870503114⟩ E) ⟨317827883446,3869686625⟩ (N (N E ⟨317827883666,3858481696⟩ E) ⟨317827883728,3855331271⟩ E)) ⟨317827883846,3849344182⟩ (N (N (N E ⟨317827883972,3842964014⟩ E) ⟨317827884020,3840536952⟩ E) ⟨317827884036,3839728357⟩ (N E ⟨317827884066,3838212815⟩ E))) ⟨317827884084,3837303849⟩ (N (N (N (N E ⟨317827884114,3835789503⟩ E) ⟨317827884134,3834780354⟩ E) ⟨317827884166,3833166406⟩ (N (N E ⟨317827884198,3831553308⟩ E) ⟨317827884500,3816371408⟩ E)) ⟨317827884740,3804359921⟩ (N (N (N E ⟨317827884788,3801963297⟩ E) ⟨317827884804,3801164842⟩ E) ⟨317827885040,3789411944⟩ (N E ⟨317827885220,3780478395⟩ E))))) ⟨317827885408,3771175891⟩ (N (N (N (N (N (N E ⟨317827885456,3768805371⟩ E) ⟨317827885508,3766239410⟩ E) ⟨317827885520,3765647575⟩ (N (N E ⟨317827885572,3763084301⟩ E) ⟨317827885584,3762493086⟩ E)) ⟨317827885616,3760917080⟩ (N (N (N E ⟨317827885636,3759932495⟩ E) ⟨317827885712,3756194011⟩ E) ⟨317827885808,3751478356⟩ (N E ⟨317827885872,3748338697⟩ E))) ⟨317827885940,3745006407⟩ (N (N (N (N E ⟨317827885952,3744418741⟩ E) ⟨317827886000,3742069227⟩ E) ⟨317827886404,3722367008⟩ (N (N E ⟨317827886428,3721200664⟩ E) ⟨317827886432,3721006318⟩ E)) ⟨317827886556,3714987876⟩ (N (N (N E ⟨317827886656,3710143157⟩ E) ⟨317827886720,3707046681⟩ E) ⟨317827886768,3704726444⟩ (N E ⟨317827886800,3703180628⟩ E)))) ⟨317827886804,3702987457⟩ (N (N (N (N (N E ⟨317827886884,3699126695⟩ E) ⟨317827887044,3691420255⟩ E) ⟨317827887072,3690073692⟩ (N (N E ⟨317827887172,3685269550⟩ E) ⟨317827887184,3684693578⟩ E)) ⟨317827887236,3682199002⟩ (N (N (N E ⟨317827887248,3681623630⟩ E) ⟨317827887300,3679131651⟩ E) ⟨317827887424,3673197744⟩ (N E ⟨317827887488,3670139764⟩ E))) ⟨317827887536,3667848367⟩ (N (N (N (N E ⟨317827887656,3662127694⟩ E) ⟨317827887712,3659461864⟩ E) ⟨317827887740,3658129859⟩ (N E ⟨317827887968,3647306061⟩ E)) ⟨317827888068,3642571414⟩ (N (N (N E ⟨317827888092,3641436242⟩ E) ⟨317827888140,3639167224⟩ E) ⟨317827888256,3633691059⟩ (N E ⟨317827888292,3631993654⟩ E))))))) ⟨317827888320,3630674135⟩ (N (N (N (N (N (N (N (N E ⟨317827888384,3627660343⟩ E) ⟨317827888480,3623145516⟩ E) ⟨317827888496,3622393728⟩ (N (N E ⟨317827888528,3620890736⟩ E) ⟨317827888548,3619951763⟩ E)) ⟨317827888572,3618825396⟩ (N (N (N E ⟨317827888580,3618450038⟩ E) ⟨317827888592,3617887092⟩ E) ⟨317827888608,3617136668⟩ (N E ⟨317827888644,3615448924⟩ E))) ⟨317827888688,3613387463⟩ (N (N (N (N E ⟨317827888732,3611327472⟩ E) ⟨317827888736,3611140273⟩ E) ⟨317827888784,3608894829⟩ (N (N E ⟨317827888832,3606651130⟩ E) ⟨317827888836,3606464234⟩ E)) ⟨317827888880,3604409175⟩ (N (N (N E ⟨317827888896,3603662244⟩ E) ⟨317827888900,3603475541⟩ E) ⟨317827888912,3602915506⟩ (N E ⟨317827889052,3596389796⟩ E)))) ⟨317827889088,3594714145⟩ (N (N (N (N (N E ⟨317827889112,3593597587⟩ E) ⟨317827889152,3591737619⟩ E) ⟨317827889200,3589507247⟩ (N (N E ⟨317827889276,3585979363⟩ E) ⟨317827889340,3583011876⟩ E)) ⟨317827889376,3581344013⟩ (N (N (N E ⟨317827889404,3580047457⟩ E) ⟨317827889452,3577826156⟩ E) ⟨317827889500,3575606577⟩ (N E ⟨317827889552,3573203975⟩ E))) ⟨317827889632,3569511604⟩ (N (N (N (N E ⟨317827889664,3568035991⟩ E) ⟨317827889728,3565087053⟩ E) ⟨317827889792,3562141161⟩ (N (N E ⟨317827889828,3560485434⟩ E) ⟨317827889840,3559933739⟩ E)) ⟨317827889920,3556258500⟩ (N (N (N E ⟨317827889984,3553321725⟩ E) ⟨317827889996,3552771417⟩ E) ⟨317827890016,3551854474⟩ (N E ⟨317827890048,3550387980⟩ E))))) ⟨317827890064,3549655017⟩ (N (N (N (N (N (N E ⟨317827890096,3548189659⟩ E) ⟨317827890172,3544712462⟩ E) ⟨317827890224,3542335782⟩ (N (N E ⟨317827890236,3541787600⟩ E) ⟨317827890272,3540143691⟩ E)) ⟨317827890320,3537953295⟩ (N (N (N E ⟨317827890396,3534488634⟩ E) ⟨317827890444,3532302611⟩ E) ⟨317827890496,3529936328⟩ (N E ⟨317827890560,3527026698⟩ E))) ⟨317827890576,3526299759⟩ (N (N (N (N E ⟨317827890608,3524846443⟩ E) ⟨317827890704,3520490986⟩ E) ⟨317827890716,3519947027⟩ (N (N E ⟨317827890728,3519403173⟩ E) ⟨317827890752,3518315780⟩ E)) ⟨317827890776,3517228808⟩ (N (N (N E ⟨317827890812,3515599136⟩ E) ⟨317827890816,3515418119⟩ E) ⟨317827890864,3513246831⟩ (N E ⟨317827890876,3512704271⟩ E)))) ⟨317827890940,3509812386⟩ (N (N (N (N (N E ⟨317827890992,3507464920⟩ E) ⟨317827891004,3506923476⟩ E) ⟨317827891040,3505299771⟩ (N (N E ⟨317827891164,3499714197⟩ E) ⟨317827891200,3498094663⟩ E)) ⟨326417825804,7694996611⟩ (N (N (N E ⟨326417825888,7686051254⟩ E) ⟨326417825920,7682384680⟩ E) ⟨326417826012,7671050236⟩ (N E ⟨326417826176,7647939783⟩ E))) ⟨326417826448,7601477490⟩ (N (N (N (N E ⟨326417826680,7553934313⟩ E) ⟨326417826728,7543199228⟩ E) ⟨326417827004,7475575871⟩ (N E ⟨326417827068,7458475179⟩ E)) ⟨326417827168,7430698629⟩ (N (N (N E ⟨326417827260,7404014908⟩ E) ⟨326417827292,7394481723⟩ E) ⟨326417827336,7381162472⟩ (N E ⟨326417827340,7379939541⟩ E)))))) ⟨326417827448,7346162789⟩ (N (N (N (N (N (N (N E ⟨326417827576,7304254818⟩ E) ⟨326417827772,7236200800⟩ E) ⟨326417828028,7140399025⟩ (N (N E ⟨326417828056,7129454955⟩ E) ⟨326417828216,7065190113⟩ E)) ⟨326417828344,7011692538⟩ (N (N (N E ⟨326417828440,6970375320⟩ E) ⟨326417828488,6949338187⟩ E) ⟨326417828648,6877420943⟩ (N E ⟨326417828696,6855315200⟩ E))) ⟨326417829752,6311610279⟩ (N (N (N (N E ⟨326417829776,6298073333⟩ E) ⟨326417829976,6183422759⟩ E) ⟨326417830008,6164780109⟩ (N (N E ⟨326417830024,6155428585⟩ E) ⟨326417830240,6027260879⟩ E)) ⟨326417830408,5925195688⟩ (N (N (N E ⟨326417830520,5856053822⟩ E) ⟨326417830648,5776006080⟩ E) ⟨326417830776,5694907543⟩ (N E ⟨326417831128,5466867682⟩ E)))) ⟨326417831288,5360986259⟩ (N (N (N (N (N E ⟨326417831416,5275372985⟩ E) ⟨326417831768,5036210458⟩ E) ⟨326417831976,4892644623⟩ (N (N E ⟨326417832848,4278191046⟩ E) ⟨326417833048,4135533285⟩ E)) ⟨326417833080,4112682170⟩ (N (N (N E ⟨326417833096,4101254723⟩ E) ⟨326417833352,3918331670⟩ E) ⟨326417833568,3764072198⟩ (N E ⟨326417833736,3644313518⟩ E))) ⟨326417833848,3564645100⟩ (N (N (N (N E ⟨326417833976,3473813401⟩ E) ⟨326417833984,3468145225⟩ E) ⟨335007769048,3441396271⟩ (N E ⟨335007769208,3321645605⟩ E)) ⟨335007769336,3226450986⟩ (N (N (N E ⟨335007769688,2967880823⟩ E) ⟨335007770968,2081621181⟩ E) ⟨335007771016,2050428903⟩ (N E ⟨335007771272,1886990282⟩ E))))) ⟨335007771488,1753085620⟩ (N (N (N (N (N (N E ⟨335007771768,1585275186⟩ E) ⟨335007771896,1510828826⟩ E) ⟨335007771936,1487864743⟩ (N (N E ⟨335007772376,1245054427⟩ E) ⟨335007772536,1161373428⟩ E)) ⟨335007772664,1096267502⟩ (N (N (N E ⟨335007773656,650268299⟩ E) ⟨335007774296,421041230⟩ E) ⟨335007774352,403269334⟩ (N E ⟨335007775520,119142818⟩ E))) ⟨335007776368,18139488⟩ (N (N (N (N E ⟨343824211968,14001⟩ E) ⟨343853572096,109955⟩ E) ⟨343891320832,367049⟩ (N (N E ⟨343916486656,622063⟩ E) ⟨344155561984,6385231⟩ E)) ⟨344193310720,7848312⟩ (N (N (N E ⟨344231059456,9462349⟩ E) ⟨344327528448,14273065⟩ E) ⟨344696627200,41781288⟩ (N E ⟨345158000640,96403325⟩ E)))) ⟨345225109504,106211584⟩ (N (N (N (N (N E ⟨345501933568,151635305⟩ E) ⟨345598402560,169332767⟩ E) ⟨345963307008,244916797⟩ (N (N E ⟨352187656564,3092045363⟩ E) ⟨352187656852,3081533279⟩ E)) ⟨352187657648,3052710541⟩ (N (N (N E ⟨352187658064,3037781477⟩ E) ⟨352187658832,3010459128⟩ E) ⟨352187659312,2993538576⟩ (N E ⟨352187659600,2983443296⟩ E))) ⟨352187659636,2982184380⟩ (N (N (N (N E ⟨352187659980,2970188170⟩ E) ⟨352187662336,2889629010⟩ E) ⟨360777597256,6268599833⟩ (N E ⟨360777604424,3273569067⟩ E)) ⟨360777605120,2866362512⟩ (N (N (N E ⟨369367542344,1582117934⟩ E) ⟨369367544872,507732170⟩ E) ⟨369367546944,60563652⟩ (N E ⟨369367547712,5298027⟩ E))))))))

#eval IO.monoMsNow
noncomputable def table : CTN :=
  (N (N (N (N (N tab0 ⟨101300928512,312050644⟩ tab1) ⟨107105853440,5576516022⟩ (N tab2 ⟨138110176032,7434408⟩ tab3)) ⟨139240544372,509757185⟩ (N (N tab4 ⟨146029027564,17486088980⟩ tab5) ⟨172251848000,221179⟩ (N tab6 ⟨172808637650,76257770⟩ tab7))) ⟨173533205141,366900306⟩ (N (N (N tab8 ⟨174617435392,1148273930⟩ tab9) ⟨180388802304,10731190103⟩ (N tab10 ⟨206582255634,815654⟩ tab11)) ⟨207119128786,53710199⟩ (N (N tab12 ⟨207653903056,187565689⟩ tab13) ⟨208239007808,434106245⟩ (N tab14 ⟨209111425024,942451069⟩ tab15)))) ⟨214748570396,8235234748⟩ (N (N (N (N tab16 ⟨223338512896,16264029169⟩ tab17) ⟨241072054272,6678975⟩ (N tab18 ⟨241596340034,65456388⟩ tab19)) ⟨242034646020,156913362⟩ (N (N tab20 ⟨242527475968,313942050⟩ tab21) ⟨243111532247,569533418⟩ (N tab22 ⟨244463149056,1367016756⟩ tab23))) ⟨249108343284,6004310295⟩ (N (N (N tab24 ⟨257698284352,12113034436⟩ tab25) ⟨275419241410,6361312⟩ (N tab26 ⟨276195187748,91342837⟩ tab27)) ⟨277315067826,382438769⟩ (N (N tab28 ⟨283468113104,4781349269⟩ tab29) ⟨283468119840,4334673510⟩ (N tab30 ⟨310726926336,101996445⟩ tab31)))))

#eval IO.monoMsNow
theorem tab0_ok : tab0.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab1_ok : tab1.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab2_ok : tab2.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab3_ok : tab3.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab4_ok : tab4.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab5_ok : tab5.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab6_ok : tab6.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab7_ok : tab7.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab8_ok : tab8.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab9_ok : tab9.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab10_ok : tab10.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab11_ok : tab11.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab12_ok : tab12.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab13_ok : tab13.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab14_ok : tab14.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab15_ok : tab15.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab16_ok : tab16.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab17_ok : tab17.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab18_ok : tab18.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab19_ok : tab19.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab20_ok : tab20.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab21_ok : tab21.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab22_ok : tab22.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab23_ok : tab23.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab24_ok : tab24.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab25_ok : tab25.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab26_ok : tab26.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab27_ok : tab27.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab28_ok : tab28.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab29_ok : tab29.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab30_ok : tab30.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem tab31_ok : tab31.allOk = true := by decide +kernel

#eval IO.monoMsNow
theorem table_ok : table.allOk = true := by
  simp only [table, CTN.allOk, tab0_ok, tab1_ok, tab2_ok, tab3_ok, tab4_ok, tab5_ok, tab6_ok, tab7_ok, tab8_ok, tab9_ok, tab10_ok, tab11_ok, tab12_ok, tab13_ok, tab14_ok, tab15_ok, tab16_ok, tab17_ok, tab18_ok, tab19_ok, tab20_ok, tab21_ok, tab22_ok, tab23_ok, tab24_ok, tab25_ok, tab26_ok, tab27_ok, tab28_ok, tab29_ok, tab30_ok, tab31_ok, Bool.true_and, Bool.and_true]
  decide +kernel

#eval IO.monoMsNow
def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 39936, false),
  (39936, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 57344, true),
  (57344, 57856, true),
  (57856, 401408, false)]

#eval IO.monoMsNow
theorem cover0_ok : SixW15B.coverCheck table 25715100 (SC / 2) 401408 cover0 = true := by decide +kernel

#eval IO.monoMsNow
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

#eval IO.monoMsNow
theorem cover1_ok : SixW15B.coverCheck table 48318100 (SC / 2) 237568 cover1 = true := by decide +kernel

#eval IO.monoMsNow
def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 37888, false),
  (37888, 38016, true),
  (38016, 38144, true),
  (38144, 38400, true),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 60416, true),
  (60416, 73728, false),
  (73728, 73984, true),
  (73984, 74240, true),
  (74240, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 89088, true),
  (89088, 89344, true),
  (89344, 89600, true),
  (89600, 221184, false)]

#eval IO.monoMsNow
theorem cover2_ok : SixW15B.coverCheck table 52857300 (SC / 2) 221184 cover2 = true := by decide +kernel

#eval IO.monoMsNow
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
  (88832, 88960, true),
  (88960, 89088, true),
  (89088, 237568, false)]

#eval IO.monoMsNow
theorem cover3_ok : SixW15B.coverCheck table 48170700 (SC / 2) 237568 cover3 = true := by decide +kernel

#eval IO.monoMsNow
def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 39936, false),
  (39936, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 57344, true),
  (57344, 57856, true),
  (57856, 409600, false)]

#eval IO.monoMsNow
theorem cover4_ok : SixW15B.coverCheck table 24938600 (SC / 2) 409600 cover4 = true := by decide +kernel

#eval IO.monoMsNow
def bits : ℕ := 6617345366883656859763357831932390164930723854604104414772017587160887731206702693961674513099952508296770572355593078618174482941222942969187985288542896217854906365040794889117494227743324033851714008930092909162048753972342093085198448230595833315795915977203892783453542936964065459764736171857024791081083885239783866661314425062384233699536283197679637349693853417862523627797282029058059985392911131892199231028032580732908673931731342185383002870768763560996835525810403082687515900832057274380201387683271322769812491029815985072633497552343424388132959781549954591806535821034936655581531386297214099581155691538014094155723303669445220231231088348513583171061955733809239256881239262362669947719262984530277406243525462502324625284902538269777767786006210975168275493035603164458526960458774990922451097659360250678717353993360274554178799160665396972317596732470140151818895284109719028530003765091733320626876278905484765398878099388770827152437663026452369949425441376963823067188153293650090917019544778056696485183960541504282001823282033904790785384389382987292780876626112214650894389178050451259487029303087049001336321743210221939209307350635888163229179842326167313584122743453755272380025294345493519896762653713472730245586127005511712417883864990847249719017950875204088924634187513322324472336394517481841566860214373594520350014846736242629606928673596083321019243207621986498341465913588273703953097621337333175858496242508029017508046116275526672321055471132809312109931050525206540050792044344832119007502324547906183263264940992371798672098389110448898144540628776365303319045902947737220599818212775181636689338440082281022321657343132345691356165121858334591622238473046727913046769393661049844847605967108225964129694133626718550003465945284719868521234228476525892511780515433628899914569226094265157989062411376850067324466843049849223192024432271551204461588123253191508474190714014064880771989707574112249368663836591335697124020716122789121352973390502407804352218727569720873316004626717825767491293970847353345543337277401752053375667230351410194087536633239024810015829723788405617847871886811999682699732155378958723467092737364308048299309508830595988224761441507313461616691496242629932555977377844322450080351071123428689229423855307889642020104017149973990251346905221427495644899977664388004900674676355992852603545075633448326752021895414226707811801712797258089974997852872327302812286093685432588147821082434310500234905962021133144962902315152452657438770108558284403354381811135658770603447592898808936469342129242901220457754346705030826560069467588993614974149684519214039624595642868045163348201391469055520127691529323758869382209450604851373054026742472003942552592701527082700416408610477672764748844947090935116792576950975486492540226985753488547908972822334524161148008244326786034991689675024149165264234446666623768618222445198281089328736552194061279800033649629707788509058243395837604928645548531599034779559668106053747245982361880740091867412111426629604172192131139959164861878513109460095870025652831320156259157366392977628055984769387301268624593538775968243116626510109203862726839667811636912101900595496849125491020888317092817985047270117238931488279823002838338238655881526282905599395042444207658024655284392836238335141685116472434494286077622409932889595305922415541547015774045075973762979081623161457558047953647489945309324462548171820224522326926395495558481115342948273914493972879662064164626259917156710943159486927918437675611143168319801625764647590857597184961304279526818646263932300136975802569916276944882487332218324145082239237674334154287585831309141916193481312451000343003972583685007591591935684733906919867976381226831747899549920771741399761391969490688707046624703278895702057027123465797417060216241083185638829290437400375212079494364330662964163434789741573436020960570438224700628862896494992877582727410513980959844654468794744047902525645171719850999483321621668863509511886773304936672262409295612628868407622795207162584262907693810664103937874574262944756998675098035753925618851328533081799906487997155241021138384738196696991576970607190395335093991358967249188507894954791157272814241936986183038406338044493051134483204244613152599723573316772561105275359187784247340918596412377074669673995017195615917844013133339745311558161854441589356960987239737571549772747394455484731801824846474449135021517093730317207753793094143467157182856709742671073423367359836070053964276630154397945629734187608990119978779458870997463280994673437350941949970676292908183633073026471698126441770371356634147581880504857909815568010840349746560371232523537840470909044884235217923486904734307290170308426127835896766855395008879567546627077130376113073238121536742459023611140670415169842502557730281130404615954010162262102299593003630029669153760620906146692763014487932389023065257806341730676589178002187281379063564983872552583702977961925889374846523827608548974260658913728847767014272654693413039166570753947738577580733351369275163445677881432286382356462910944327627188583219891315556978486369512035093779906319906649325121893285008971034238873410092708990971973710707727859896423740011978243476433043545167817809600421364831788796315395773319581035534270805043891316812910900829806075881389665925275910699220874587874810893829849278753133801049930385463789993376968284517552788220552906039103221572484402908413976905800439721305552736112991667547415888305974013832545001606132502552735675086964980461005785769865967393103003888876584507177754802333781361404147643385371729975788584454213533657019807565179133474160606516795020684836430221571677203368543979333931650418865635937278002893963848394412157877870832823134856837122339112137101290922815613154351522186506405519132897765708379403145246177275261012385667893559921560354383305545051315464823321957211386934800804636311312010949043636583658580357059658682921933051371019122033653402860638071969968292217697268288214451162576741040225717638166227572095937135453901497877665478227452931286388730505472215342060367214801462277542975855041836674117148606206473311650201132947986530957476040377598744706761459928283849201402438995084271443089734869614178426169644056435348452121873430527735567618792835776497977269040357627673141023713007617577198386160974452412611708397756094060560882203804745307185995308065403812066443310670523886427179626081091882924062178842504494706072582212362821188702368954473161627336203069098485798109141212988980376656853160482169779129964097746623713709161403707643618149093009442207374147551183115885905466521290163185270885188893649488362780175194771288826086348880583421008002450230722886617347610772590487526933430079041401159588536082341705823978053902286172955773785269552901509907016280887808627854440915497731472300994680158875256895437689611554049804335095031914456482669448775582743319627121828700897193106884788488763230918056850288979238872828725036189216418591334372280084546116409952406892700398174346968648240880719887439054895994782842044502630807785448170453589227474143571204951119073004106358252627528388805116759017715051602620187496282839440769867053262180239582035604755856116543977173630376170274802899818570666820368676034408096596808350852764728000105139750564602912486509923518889474779152132573241815825878387856396700234834500799026751485274851891686398270174999961727711525650445207419942544971500516856489940963161653750837799551198123873368460428165086280970538262537145667620396752719323204121673927339044569930396168698187382626930288694932223538767855427137086444482108143795577901792112804655365982225142445473891475054383420390880650973751789830989180723371598486021282660876767855878653537994904931917695767922747773672715350752477832047933246200855222567628879457316446222497866741375017028427579533937655487286751239245771421011735075310142740412360081153460209519294836978130828769086550003794476703204639408434064407210945626606245506202463736678650066425690843594694097968091071750920666174991951306265825478166508419412060444162754819528166783176138558432632812944191683470240284533602984406711518284215041841650714685904715164365662349738029613857090108808750439996878530497761405589146041955613537629718439511733142021141475086687022643676167433592462541915964942122763034235159688149523481187587340805070796262302167931502720602404618820669755520133168353011704916456524262412280352344135324432940098583449411723174657406523310824210373901581517660888135688772655352876344133428702221322113143924502149004269215035571699911774031598806581409310914369599936528319174739153612490742147271366862241239990627881912042241385307191258019012368486258798133956293420910161129749089632082114854262527004282183176988839691093332198869292984431914227473607284586351357725816602403012997032365203652774323857478550143004974739757566308497027653850351328004071053153177705595265299713446014440591529861461439583668020046164501273580790091297712142144599542397580283602247986593765196484722456912354166696594982169179408682584695401540647004630592471806677838775125004259886734446284984099198929652367213059138587877034323193312662160237667562310723450873794101130472276163549129128433545479538577850505752333788191265936772158999120971269356495677573155977102132987391170831474302470843458793046824343547279087873881179094938565891968953718121813359917423895511425274150730609135342712219981295559660878417717896796539500094570541836881155819885138248074361090781956598273612358481462745836242016570989477522118753410368151206691070198694309138984960373096208401528152683519767807099228644237267730632652127114036638564660336009421610338099603080236085458756273221967445709292306416523832966085664486250325104298377089460979315302293870010617107165124619074935116060675328949294956524718716712086555847021124629713471822914787808111119580868913943911717402576415465255836339007912336820254249969402096221586055093632331858796146695863824550178684352368118356237440687981943550741224473867456402424908480416008997755442141744258123220359862144113100479065460635898636982727335516642253497404072640570371611644850350097811221639326993443467744332165171579374519505465426607970510141830620505082433675844727981538454898460804168289801475204227694483721586544566593369852142904409499632028914713876909736126195659498108275103547942977087964408173802574051294538174601393129743125784053158773479427780278558159427148132127664262833834328624210975353162265687035080553353192100899635959155040514838484017224682814893229654845935083359662185570761572650083014290262304088312808811865658482306386169236373770801592894574334021095160532353474185418436204039564372088128575089368199704380463447124520449667690357909733668010327657630888368105787781679039975918822827102385364697875486030148381830130270055900946725856389689542109577718402736535907391665718172705582151050689455709317395390709054215884204123219912223608739417868862994640229299667170271260871648854902024125693909579192511354786698945998683927097479940170156074287857393439967349321498445683065576707697999799776006448262267943264926747810051213907349036115380257948114220855488415565749657940021760399122420479073235008030723996072286714281724233581385547018316828455109064824922215281750752491420673538592534683221800381645354411772870007127275002008980385682609579551385773082807466356907219338941067337459937579356338218555227633006800614404432708648218177957580804321496467773497346701269729276687052581593796174511064485810941590425773154650611274835892795061866863469495242996987597575316450755767246474948954822124580454114496279819233796018506282387026674152244073980717259127938799444999584721448482974283259510623287699696411054596150571536614303636321886568033503581282862825246766723485568981210741499041330350195826354481397559889606828079033631412160681542383907285825769493253869881277534816892594899164283724197965111905998341560004431884001794394996210355874919341694455785506270190215722051980375439312332413196767175180922424284609256623371476752055006252810082322522467521683188444301498746971859130763476624011843038027955441728117074456579424689734736386542494831016345445545812912518401024379044426207203650414074607221144601013622627263823367233279586180562996150134624552594121716760824849105441439093484051685281031376926629732690716700693829675632738464594733751287682414195994538258961981940501312502509234742658204359193768525698223446778084232075227755751478912686114313471068573714027164286509254405174415286124103443270248707348827759223557047945145850639114587825366719159016905470433489201400186866750923542756626699392907732860850599568188320329812006818354510429047009130036843644702243116898829705353012774293350675343468486433056188180087664453278614009049371526846375000307299358335200434842768205019396721598491987148193749739030168922498520564686332822299729174665342487437631758818349373761411310126796885222197415493791507571497873415272543430307746179650993416502161219881227041441000120272943507359706250950391507770585178228812813571045896924228719825117614349333553177511095130892553075361606183284584127430263932365622622838975202103184856668657550279988871649450950142396939705216257707651924323274597174945111017758326617158578021802753495859104097345713956980573347783966406823567846244734511999699649129961433610124003776827171803865370598296189830351168623259964482050908625330736192699896940710499001278001225958451926390588953387227101176139436540163101291914122648927057224692145726014859322202424546710984391432726739096993279007598749083734287927556876891335470354354894483177916969088721931346635075363967510924820118824131108943914356953673332736098925300587095907313950322362145131873756181594971148157382818530177155146083480689967754239269842124653114416503903806143830795255542229076889164838148357790202465893976138501773763571242534405242132208407366126472036362486313234846596299383297346109820839411939778355641590606273046853261911579326041559629907833169536566279428424178171571697412014943619943491700025714914032385632812445353369689917681966009654067488970984300337995113684520689139170692684572292581155254791128401869386276950416779117223362949660328200914591859604447372658421600072405133446124713511350651730728775364930027547230879149841484204737591707758756996008399105251682529502262844258479991739343974492738091854055823802388589000339302121997784584363339857315225668044871056242318869465518163466654970038531489777938084825642728529822348682134167430835110618421068547762107548676556652992484164623688538831741090288736596005974215530680049426192586568194263040063832249233353835448953578185777287628792115763101417668935175037914860026655518124996631504346700408429560002426601299915976198249252511245085555190931357226994463848820065194830835053316496506167762369253662215456688901426179667485093130040026164309568987604453740400092076969832002546659310727307848636077885232103354168299792215817525913947046751680122157920013249238131134061937977770732504603341432225311723938460233818840113870127760733562771293134175530583836897369534038602958487744497981836465219411011203154317912592043862636011471298511168497605793481285098661806801041281707249368508585075977714206847276075386903885422512839401028061192585732614931557800685634922086970132870921037880455250790485890282953275071389133348069469577147182446714975265669301544378679045490610636184787715662061438611337751240679132276531774050020092654810369172428528639613960889526665596303659810463991836477032440146857094714319590325479950257875380158656023104336079132753546334301775614737067737595779107653138925819831227554518472000560068054296508499878451302388590431669757454395844610228735901458654766118120457308349849776942499757306022084975191938782038544618542065043345718220304619882333648920782434213238688242866882095105405762238633904490146957605176327682649554377774686512839054240822181130669242267571894608958065511607915767010739926440287530979406864135365751738095880833049760361541930199765029827138210781841937840314188522536701357721843862655684668504536667963815051088727135405213447314177943424242332460749706765561908169862794808320620236593995681823076560794191492408854152429890852643892679090153024136176601009025946641448834592031590746092622107341277696231252567912332439271853038483599084482709003587894944233083249201626467269862121499242508724848865230876441753155548602934968518299552276187839545195251841551624670602165616508530708779596800913179395263774340138801498994631447487700322573248835253622661665954414046568048976530946912614726611261201116580576444746550350113304609856070775827993447877758412769819890880172210023782223175131026402413067112679587889561527707782420981416645376777969947500927265332399308737509701277130402729624381243014232447324674807203427217764908649970425247836581844983537863194591887926967838075432489192886710768316677512563622894785152833860136296147029083027202258286447425868260565240942359174658183696325235836525913768828962554728748943722693710291030377286935886147303905580032521267946097099145400972453541653248203106807761647187187214152400630150284905507171828364340675454619230218511134263408243909158672696592295849910105677360739370136129703606348089591792602571293058740628617593643868070719959087497986708172124217881969908395428019534395232204684916995910674979426096540939258476177626593842929294965020193128785449278374880701614481190423419952684722279657023725575257224457342908066772798496953816836974432874497178882327762671819262437327554292874508856141821888722670882272896463508217812118813883084539480492809663911388935415980911523900636250347647422140115577512199487699210825292853001617916383317762502529511303463314969933724876249815804200182188429577904436739691059853032005793129812937588421221393693410584823409405007081495795866735971564952029227030202221436751006442477542266899527376403216061541945261199838645836756734130513429855744028054497539498346697570893714782438786928309516176739507699844515323631415151260202944193997883268882029302886928058317758272915082947109988526214424037262917231057194764100553624980459830159141133777324750583300640628305333246944448039795982815695510795431164036243265269326467257448498514040151025063394839838520583746354791117903052076388668346788138714516434541240568471701965898656742529823905490656798894887364495181319927455718478933140477232779772413935626368418627102431256477279148666773770259528321320210026720505775563260725167496838575268644454738907177740511378669403970187013049292674923345201375351989447038436189943768529766944174008621173025266970140837338553734246529080927965037282487423054853824427381549900475243805320832237673780884248935445687475515051200549335211798604686367538094418581876234016012418314595144366104794723118483590081448715854230597457749186793565412147040102381410519529341314262710084758492713982789738281986920166780907275713302955139194343718900529616546008942243043148921004693497540132284704284442719753625383146220970167437733993853161330920600355855958701640306488474794682516815156480370633686031240960173970342918904787319315201738287983688522178625936649901286049448667091618872209387486515980891738667581179302224880435170819163057657580312326961118456223769230210098317137051379591213236625124292185667827748998047083471863705428124051831712186852836678299884509964836602184185072343538218811683953141843094602542673276202398763299133989063249425187875809745260963002943421147736779951673446786798704443107645555216853601088035258807779176249141953636907829581600644511735927576938470662241039134930521434462782916504775984779015711758791104119108323280063956363077100788365719437672164419859174530562238919820984097268123280640873000224090042653260657650697215134292300500261367030730364132793597473845966354143319910090928514788631447695240769705717099404456031736356237515975886428601427243631592563558853885832081657364546325158625419761917959398329604973873900372290860095965613126061732837968705975662248754201440952781444833436114629411830267284645176077684309985789597391059943060697904184610141097620129308144567584882465210002673216884584357719276679303403638606854118223769123579136585697416367408745090396606825868727998261153754008810067681812189111038139040257048040251293089438935354033684623918038651694985459953540577391638615637683509613670264488386844652337504852692458320629059211887250689479749121322916135371655460765721245268524271649270291114264825238405316792674059043159700925063523161111683780649815545849257701099575576347111697757789720468851701970111515831643973255548318626130589584406393189711352777217750573570096207030465693303854175958627524449002390303523693613213930743614148227949713241652508999367561727276415727731393969056191765824571170077746996021820131081958475080528761602674360577990498205580558122921362672132278839137876679068653635953011907142932413836359014952143246318064621476697218028332977341460375906397682980107900075695617876780230436747554279290014148920685601398143593391613238153018147999123039639306723088087883447049629640548730186843276825315877528557967701837815108872194403499178462735106582200596836941833074981333406106805615362820625398218318936500871911611508315001010955298822099784193345937616256124532374319663591916575297386949746171577066630338561288708469053575119674460840635271023777687308044360549706452681691905047027962833175973116886808887779206925037530113750622419662305944202935504333433630166328538637100514522114241072118450124460384585337327986837490374325174187108041985332586035211949571753843803742505179250527184726249415724750174710399386684301488996840337

#eval IO.monoMsNow
theorem wk0 : SixW15B.walk table bits 64 0 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936) = some 1451 := by decide +kernel

#eval IO.monoMsNow
theorem wk1 : SixW15B.walk table bits 64 1451 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 409600) = some 6167 := by decide +kernel

#eval IO.monoMsNow
theorem wk2 : SixW15B.walk table bits 64 6167 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936) = some 8513 := by decide +kernel

#eval IO.monoMsNow
theorem wk3 : SixW15B.walk table bits 64 8513 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 409600) = some 11854 := by decide +kernel

#eval IO.monoMsNow
theorem wk4 : SixW15B.walk table bits 64 11854 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936) = some 12865 := by decide +kernel

#eval IO.monoMsNow
theorem wk5 : SixW15B.walk table bits 64 12865 (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 409600) = some 13486 := by decide +kernel

#eval IO.monoMsNow
theorem wk6 : SixW15B.walk table bits 64 13486 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936) = some 15462 := by decide +kernel

#eval IO.monoMsNow
theorem wk7 : SixW15B.walk table bits 64 15462 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 409600) = some 18633 := by decide +kernel

#eval IO.monoMsNow
theorem wk8 : SixW15B.walk table bits 64 18633 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936) = some 19829 := by decide +kernel

#eval IO.monoMsNow
theorem wk9 : SixW15B.walk table bits 64 19829 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 409600) = some 20380 := by decide +kernel

#eval IO.monoMsNow
theorem wk10 : SixW15B.walk table bits 64 20380 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936) = some 20521 := by decide +kernel

#eval IO.monoMsNow
theorem wk11 : SixW15B.walk table bits 64 20521 (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 409600) = some 20522 := by decide +kernel

#eval IO.monoMsNow
theorem wk12 : SixW15B.walk table bits 64 20522 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936) = some 21228 := by decide +kernel

#eval IO.monoMsNow
theorem wk13 : SixW15B.walk table bits 64 21228 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 409600) = some 21639 := by decide +kernel

#eval IO.monoMsNow
theorem wk14 : SixW15B.walk table bits 64 21639 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936) = some 21715 := by decide +kernel

#eval IO.monoMsNow
theorem wk15 : SixW15B.walk table bits 64 21715 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 409600) = some 21716 := by decide +kernel

#eval IO.monoMsNow
theorem wk16 : SixW15B.walk table bits 64 21716 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936) = some 21717 := by decide +kernel

#eval IO.monoMsNow
theorem wk17 : SixW15B.walk table bits 64 21717 (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 409600) = some 21718 := by decide +kernel

#eval IO.monoMsNow
theorem wk18 : SixW15B.walk table bits 64 21718 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936) = some 24144 := by decide +kernel

#eval IO.monoMsNow
theorem wk19 : SixW15B.walk table bits 64 24144 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 409600) = some 28645 := by decide +kernel

#eval IO.monoMsNow
theorem wk20 : SixW15B.walk table bits 64 28645 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936) = some 30521 := by decide +kernel

#eval IO.monoMsNow
theorem wk21 : SixW15B.walk table bits 64 30521 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 409600) = some 31502 := by decide +kernel

#eval IO.monoMsNow
theorem wk22 : SixW15B.walk table bits 64 31502 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936) = some 31713 := by decide +kernel

#eval IO.monoMsNow
theorem wk23 : SixW15B.walk table bits 64 31713 (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 409600) = some 31769 := by decide +kernel

#eval IO.monoMsNow
theorem wk24 : SixW15B.walk table bits 64 31769 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936) = some 33035 := by decide +kernel

#eval IO.monoMsNow
theorem wk25 : SixW15B.walk table bits 64 33035 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 409600) = some 33651 := by decide +kernel

#eval IO.monoMsNow
theorem wk26 : SixW15B.walk table bits 64 33651 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936) = some 33832 := by decide +kernel

#eval IO.monoMsNow
theorem wk27 : SixW15B.walk table bits 64 33832 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 409600) = some 33833 := by decide +kernel

#eval IO.monoMsNow
theorem wk28 : SixW15B.walk table bits 64 33833 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936) = some 33834 := by decide +kernel

#eval IO.monoMsNow
theorem wk29 : SixW15B.walk table bits 64 33834 (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 409600) = some 33835 := by decide +kernel

#eval IO.monoMsNow
theorem wk30 : SixW15B.walk table bits 64 33835 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936) = some 33916 := by decide +kernel

#eval IO.monoMsNow
theorem wk31 : SixW15B.walk table bits 64 33916 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 409600) = some 33917 := by decide +kernel

#eval IO.monoMsNow
theorem wk32 : SixW15B.walk table bits 64 33917 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936) = some 33918 := by decide +kernel

#eval IO.monoMsNow
theorem wk33 : SixW15B.walk table bits 64 33918 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 409600) = some 33919 := by decide +kernel

#eval IO.monoMsNow
theorem wk34 : SixW15B.walk table bits 64 33919 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936) = some 33920 := by decide +kernel

#eval IO.monoMsNow
theorem wk35 : SixW15B.walk table bits 64 33920 (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 409600) = some 33921 := by decide +kernel

#eval IO.monoMsNow
theorem wk36 : SixW15B.walk table bits 64 33921 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936) = some 34987 := by decide +kernel

#eval IO.monoMsNow
theorem wk37 : SixW15B.walk table bits 64 34987 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 409600) = some 35678 := by decide +kernel

#eval IO.monoMsNow
theorem wk38 : SixW15B.walk table bits 64 35678 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936) = some 35884 := by decide +kernel

#eval IO.monoMsNow
theorem wk39 : SixW15B.walk table bits 64 35884 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 409600) = some 35940 := by decide +kernel

#eval IO.monoMsNow
theorem wk40 : SixW15B.walk table bits 64 35940 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936) = some 35941 := by decide +kernel

#eval IO.monoMsNow
theorem wk41 : SixW15B.walk table bits 64 35941 (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 409600) = some 35942 := by decide +kernel

#eval IO.monoMsNow
theorem wk42 : SixW15B.walk table bits 64 35942 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936) = some 36068 := by decide +kernel

#eval IO.monoMsNow
theorem wk43 : SixW15B.walk table bits 64 36068 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 409600) = some 36069 := by decide +kernel

#eval IO.monoMsNow
theorem wk44 : SixW15B.walk table bits 64 36069 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936) = some 36070 := by decide +kernel

#eval IO.monoMsNow
theorem wk45 : SixW15B.walk table bits 64 36070 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 409600) = some 36071 := by decide +kernel

#eval IO.monoMsNow
theorem wk46 : SixW15B.walk table bits 64 36071 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936) = some 36072 := by decide +kernel

#eval IO.monoMsNow
theorem wk47 : SixW15B.walk table bits 64 36072 (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 409600) = some 36073 := by decide +kernel

#eval IO.monoMsNow
theorem wk48 : SixW15B.walk table bits 64 36073 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936) = some 36074 := by decide +kernel

#eval IO.monoMsNow
theorem wk49 : SixW15B.walk table bits 64 36074 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 409600) = some 36075 := by decide +kernel

#eval IO.monoMsNow
theorem wk50 : SixW15B.walk table bits 64 36075 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936) = some 36076 := by decide +kernel

#eval IO.monoMsNow
theorem wk51 : SixW15B.walk table bits 64 36076 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 409600) = some 36077 := by decide +kernel

#eval IO.monoMsNow
theorem wk52 : SixW15B.walk table bits 64 36077 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936) = some 36078 := by decide +kernel

#eval IO.monoMsNow
theorem wk53 : SixW15B.walk table bits 64 36078 (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 409600) = some 36079 := by decide +kernel

#eval IO.monoMsNow
theorem wk54 : SixW15B.walk table bits 64 36079 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936) = some 40775 := by decide +kernel

#eval IO.monoMsNow
theorem wk62 : SixW15B.walk table bits 57 40803 (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 79840) = some 44199 := by decide +kernel

#eval IO.monoMsNow
theorem wk63 : SixW15B.walk table bits 57 44199 (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 79840 101824) = some 46145 := by decide +kernel

#eval IO.monoMsNow
theorem wk61 : SixW15B.walk table bits 58 40799 (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) = some 46145 :=
  SixW15B.walk_split table bits 57 40799 (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) 44199 46145 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) : SixW15B.Box).setHi (SixW15B.axOf bits 40799) (SixW15B.Box.mid (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) (SixW15B.axOf bits 40799)) = (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 79840) from by decide +kernel]; exact wk62)
    (by rw [show ((SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) : SixW15B.Box).setLo (SixW15B.axOf bits 40799) (SixW15B.Box.mid (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) (SixW15B.axOf bits 40799)) = (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 79840 101824) from by decide +kernel]; exact wk63)

#eval IO.monoMsNow
theorem wk64 : SixW15B.walk table bits 58 46145 (SixW15B.Box.mk 100800 143744 31744 38400 31744 37888 31744 38400 57856 101824) = some 47386 := by decide +kernel

#eval IO.monoMsNow
theorem wk60 : SixW15B.walk table bits 59 40795 (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) = some 47386 :=
  SixW15B.walk_split table bits 58 40795 (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) 46145 47386 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) : SixW15B.Box).setHi (SixW15B.axOf bits 40795) (SixW15B.Box.mid (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) (SixW15B.axOf bits 40795)) = (SixW15B.Box.mk 57856 100800 31744 38400 31744 37888 31744 38400 57856 101824) from by decide +kernel]; exact wk61)
    (by rw [show ((SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) : SixW15B.Box).setLo (SixW15B.axOf bits 40795) (SixW15B.Box.mid (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) (SixW15B.axOf bits 40795)) = (SixW15B.Box.mk 100800 143744 31744 38400 31744 37888 31744 38400 57856 101824) from by decide +kernel]; exact wk64)

#eval IO.monoMsNow
theorem wk65 : SixW15B.walk table bits 59 47386 (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 101824 145792) = some 48522 := by decide +kernel

#eval IO.monoMsNow
theorem wk59 : SixW15B.walk table bits 60 40791 (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) = some 48522 :=
  SixW15B.walk_split table bits 59 40791 (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) 47386 48522 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) : SixW15B.Box).setHi (SixW15B.axOf bits 40791) (SixW15B.Box.mid (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) (SixW15B.axOf bits 40791)) = (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 101824) from by decide +kernel]; exact wk60)
    (by rw [show ((SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) : SixW15B.Box).setLo (SixW15B.axOf bits 40791) (SixW15B.Box.mid (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) (SixW15B.axOf bits 40791)) = (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 101824 145792) from by decide +kernel]; exact wk65)

#eval IO.monoMsNow
theorem wk66 : SixW15B.walk table bits 60 48522 (SixW15B.Box.mk 143744 229632 31744 38400 31744 37888 31744 38400 57856 145792) = some 48733 := by decide +kernel

#eval IO.monoMsNow
theorem wk58 : SixW15B.walk table bits 61 40787 (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) = some 48733 :=
  SixW15B.walk_split table bits 60 40787 (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) 48522 48733 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) : SixW15B.Box).setHi (SixW15B.axOf bits 40787) (SixW15B.Box.mid (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) (SixW15B.axOf bits 40787)) = (SixW15B.Box.mk 57856 143744 31744 38400 31744 37888 31744 38400 57856 145792) from by decide +kernel]; exact wk59)
    (by rw [show ((SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) : SixW15B.Box).setLo (SixW15B.axOf bits 40787) (SixW15B.Box.mid (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) (SixW15B.axOf bits 40787)) = (SixW15B.Box.mk 143744 229632 31744 38400 31744 37888 31744 38400 57856 145792) from by decide +kernel]; exact wk66)

#eval IO.monoMsNow
theorem wk67 : SixW15B.walk table bits 61 48733 (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 145792 233728) = some 48979 := by decide +kernel

#eval IO.monoMsNow
theorem wk57 : SixW15B.walk table bits 62 40783 (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) = some 48979 :=
  SixW15B.walk_split table bits 61 40783 (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) 48733 48979 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) : SixW15B.Box).setHi (SixW15B.axOf bits 40783) (SixW15B.Box.mid (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) (SixW15B.axOf bits 40783)) = (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 145792) from by decide +kernel]; exact wk58)
    (by rw [show ((SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) : SixW15B.Box).setLo (SixW15B.axOf bits 40783) (SixW15B.Box.mid (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) (SixW15B.axOf bits 40783)) = (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 145792 233728) from by decide +kernel]; exact wk67)

#eval IO.monoMsNow
theorem wk68 : SixW15B.walk table bits 62 48979 (SixW15B.Box.mk 229632 401408 31744 38400 31744 37888 31744 38400 57856 233728) = some 48980 := by decide +kernel

#eval IO.monoMsNow
theorem wk56 : SixW15B.walk table bits 63 40779 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) = some 48980 :=
  SixW15B.walk_split table bits 62 40779 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) 48979 48980 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) : SixW15B.Box).setHi (SixW15B.axOf bits 40779) (SixW15B.Box.mid (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) (SixW15B.axOf bits 40779)) = (SixW15B.Box.mk 57856 229632 31744 38400 31744 37888 31744 38400 57856 233728) from by decide +kernel]; exact wk57)
    (by rw [show ((SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) : SixW15B.Box).setLo (SixW15B.axOf bits 40779) (SixW15B.Box.mid (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) (SixW15B.axOf bits 40779)) = (SixW15B.Box.mk 229632 401408 31744 38400 31744 37888 31744 38400 57856 233728) from by decide +kernel]; exact wk68)

#eval IO.monoMsNow
theorem wk69 : SixW15B.walk table bits 63 48980 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 233728 409600) = some 48981 := by decide +kernel

#eval IO.monoMsNow
theorem wk55 : SixW15B.walk table bits 64 40775 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) = some 48981 :=
  SixW15B.walk_split table bits 63 40775 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) 48980 48981 (by decide +kernel)
    (by rw [show ((SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) : SixW15B.Box).setHi (SixW15B.axOf bits 40775) (SixW15B.Box.mid (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) (SixW15B.axOf bits 40775)) = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 233728) from by decide +kernel]; exact wk56)
    (by rw [show ((SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) : SixW15B.Box).setLo (SixW15B.axOf bits 40775) (SixW15B.Box.mid (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) (SixW15B.axOf bits 40775)) = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 233728 409600) from by decide +kernel]; exact wk69)

#eval IO.monoMsNow
theorem wk70 : SixW15B.walk table bits 64 48981 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936) = some 53367 := by decide +kernel

#eval IO.monoMsNow
theorem wk71 : SixW15B.walk table bits 64 53367 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 409600) = some 56018 := by decide +kernel

#eval IO.monoMsNow
theorem wk72 : SixW15B.walk table bits 64 56018 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936) = some 56714 := by decide +kernel

#eval IO.monoMsNow
theorem wk73 : SixW15B.walk table bits 64 56714 (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 409600) = some 56860 := by decide +kernel

#eval IO.monoMsNow
theorem wk74 : SixW15B.walk table bits 64 56860 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936) = some 60216 := by decide +kernel

#eval IO.monoMsNow
theorem wk75 : SixW15B.walk table bits 64 60216 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 409600) = some 62352 := by decide +kernel

#eval IO.monoMsNow
theorem wk76 : SixW15B.walk table bits 64 62352 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936) = some 62928 := by decide +kernel

#eval IO.monoMsNow
theorem wk77 : SixW15B.walk table bits 64 62928 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 409600) = some 63029 := by decide +kernel

#eval IO.monoMsNow
theorem wk78 : SixW15B.walk table bits 64 63029 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936) = some 63030 := by decide +kernel

#eval IO.monoMsNow
theorem wk79 : SixW15B.walk table bits 64 63030 (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 409600) = some 63031 := by decide +kernel

#eval IO.monoMsNow
theorem wk80 : SixW15B.walk table bits 64 63031 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936) = some 63422 := by decide +kernel

#eval IO.monoMsNow
theorem wk81 : SixW15B.walk table bits 64 63422 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 409600) = some 63503 := by decide +kernel

#eval IO.monoMsNow
theorem wk82 : SixW15B.walk table bits 64 63503 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936) = some 63504 := by decide +kernel

#eval IO.monoMsNow
theorem wk83 : SixW15B.walk table bits 64 63504 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 409600) = some 63505 := by decide +kernel

#eval IO.monoMsNow
theorem wk84 : SixW15B.walk table bits 64 63505 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936) = some 63506 := by decide +kernel

#eval IO.monoMsNow
theorem wk85 : SixW15B.walk table bits 64 63506 (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 409600) = some 63507 := by decide +kernel

#eval IO.monoMsNow
theorem wk86 : SixW15B.walk table bits 64 63507 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936) = some 66683 := by decide +kernel

#eval IO.monoMsNow
theorem wk87 : SixW15B.walk table bits 64 66683 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 409600) = some 69354 := by decide +kernel

#eval IO.monoMsNow
theorem wk88 : SixW15B.walk table bits 64 69354 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936) = some 70275 := by decide +kernel

#eval IO.monoMsNow
theorem wk89 : SixW15B.walk table bits 64 70275 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 409600) = some 70401 := by decide +kernel

#eval IO.monoMsNow
theorem wk90 : SixW15B.walk table bits 64 70401 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936) = some 70447 := by decide +kernel

#eval IO.monoMsNow
theorem wk91 : SixW15B.walk table bits 64 70447 (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 409600) = some 70448 := by decide +kernel

#eval IO.monoMsNow
theorem wk92 : SixW15B.walk table bits 64 70448 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936) = some 71034 := by decide +kernel

#eval IO.monoMsNow
theorem wk93 : SixW15B.walk table bits 64 71034 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 409600) = some 71130 := by decide +kernel

#eval IO.monoMsNow
theorem wk94 : SixW15B.walk table bits 64 71130 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936) = some 71131 := by decide +kernel

#eval IO.monoMsNow
theorem wk95 : SixW15B.walk table bits 64 71131 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 409600) = some 71132 := by decide +kernel

#eval IO.monoMsNow
theorem wk96 : SixW15B.walk table bits 64 71132 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936) = some 71133 := by decide +kernel

#eval IO.monoMsNow
theorem wk97 : SixW15B.walk table bits 64 71133 (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 409600) = some 71134 := by decide +kernel

#eval IO.monoMsNow
theorem wk98 : SixW15B.walk table bits 64 71134 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936) = some 71135 := by decide +kernel

#eval IO.monoMsNow
theorem wk99 : SixW15B.walk table bits 64 71135 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 409600) = some 71136 := by decide +kernel

#eval IO.monoMsNow
theorem wk100 : SixW15B.walk table bits 64 71136 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936) = some 71137 := by decide +kernel

#eval IO.monoMsNow
theorem wk101 : SixW15B.walk table bits 64 71137 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 409600) = some 71138 := by decide +kernel

#eval IO.monoMsNow
theorem wk102 : SixW15B.walk table bits 64 71138 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936) = some 71139 := by decide +kernel

#eval IO.monoMsNow
theorem wk103 : SixW15B.walk table bits 64 71139 (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 409600) = some 71140 := by decide +kernel

#eval IO.monoMsNow
theorem wk104 : SixW15B.walk table bits 64 71140 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936) = some 71796 := by decide +kernel

#eval IO.monoMsNow
theorem wk105 : SixW15B.walk table bits 64 71796 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 409600) = some 71942 := by decide +kernel

#eval IO.monoMsNow
theorem wk106 : SixW15B.walk table bits 64 71942 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936) = some 71988 := by decide +kernel

#eval IO.monoMsNow
theorem wk107 : SixW15B.walk table bits 64 71988 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 409600) = some 71989 := by decide +kernel

#eval IO.monoMsNow
theorem wk108 : SixW15B.walk table bits 64 71989 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936) = some 71990 := by decide +kernel

#eval IO.monoMsNow
theorem wk109 : SixW15B.walk table bits 64 71990 (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 409600) = some 71991 := by decide +kernel

#eval IO.monoMsNow
theorem wk110 : SixW15B.walk table bits 64 71991 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936) = some 71992 := by decide +kernel

#eval IO.monoMsNow
theorem wk111 : SixW15B.walk table bits 64 71992 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 409600) = some 71993 := by decide +kernel

#eval IO.monoMsNow
theorem wk112 : SixW15B.walk table bits 64 71993 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936) = some 71994 := by decide +kernel

#eval IO.monoMsNow
theorem wk113 : SixW15B.walk table bits 64 71994 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 409600) = some 71995 := by decide +kernel

#eval IO.monoMsNow
theorem wk114 : SixW15B.walk table bits 64 71995 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936) = some 71996 := by decide +kernel

#eval IO.monoMsNow
theorem wk115 : SixW15B.walk table bits 64 71996 (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 409600) = some 71997 := by decide +kernel

#eval IO.monoMsNow
theorem wk116 : SixW15B.walk table bits 64 71997 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936) = some 71998 := by decide +kernel

#eval IO.monoMsNow
theorem wk117 : SixW15B.walk table bits 64 71998 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 409600) = some 71999 := by decide +kernel

#eval IO.monoMsNow
theorem wk118 : SixW15B.walk table bits 64 71999 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936) = some 72000 := by decide +kernel

#eval IO.monoMsNow
theorem wk119 : SixW15B.walk table bits 64 72000 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 409600) = some 72001 := by decide +kernel

#eval IO.monoMsNow
theorem wk120 : SixW15B.walk table bits 64 72001 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936) = some 72002 := by decide +kernel

#eval IO.monoMsNow
theorem wk121 : SixW15B.walk table bits 64 72002 (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 409600) = some 72003 := by decide +kernel

#eval IO.monoMsNow
theorem nb0_eq : (SixW15B.badOf cover0).length = 2 := by decide +kernel

#eval IO.monoMsNow
theorem nb1_eq : (SixW15B.badOf cover1).length = 3 := by decide +kernel

#eval IO.monoMsNow
theorem nb2_eq : (SixW15B.badOf cover2).length = 3 := by decide +kernel

#eval IO.monoMsNow
theorem nb3_eq : (SixW15B.badOf cover3).length = 3 := by decide +kernel

#eval IO.monoMsNow
theorem nb4_eq : (SixW15B.badOf cover4).length = 2 := by decide +kernel

#eval IO.monoMsNow
theorem root_00000 : SixW15B.walk table bits 64 0 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 0 0) = some 1451 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 0 0 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk0

#eval IO.monoMsNow
theorem root_00001 : SixW15B.walk table bits 64 1451 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 0 1) = some 6167 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 0 1 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk1

#eval IO.monoMsNow
theorem root_00010 : SixW15B.walk table bits 64 6167 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 1 0) = some 8513 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 1 0 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk2

#eval IO.monoMsNow
theorem root_00011 : SixW15B.walk table bits 64 8513 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 1 1) = some 11854 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 1 1 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk3

#eval IO.monoMsNow
theorem root_00020 : SixW15B.walk table bits 64 11854 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 2 0) = some 12865 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 2 0 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk4

#eval IO.monoMsNow
theorem root_00021 : SixW15B.walk table bits 64 12865 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 2 1) = some 13486 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 0 2 1 = (SixW15B.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk5

#eval IO.monoMsNow
theorem root_00100 : SixW15B.walk table bits 64 13486 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 0 0) = some 15462 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 0 0 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk6

#eval IO.monoMsNow
theorem root_00101 : SixW15B.walk table bits 64 15462 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 0 1) = some 18633 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 0 1 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk7

#eval IO.monoMsNow
theorem root_00110 : SixW15B.walk table bits 64 18633 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 1 0) = some 19829 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 1 0 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk8

#eval IO.monoMsNow
theorem root_00111 : SixW15B.walk table bits 64 19829 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 1 1) = some 20380 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 1 1 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk9

#eval IO.monoMsNow
theorem root_00120 : SixW15B.walk table bits 64 20380 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 2 0) = some 20521 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 2 0 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk10

#eval IO.monoMsNow
theorem root_00121 : SixW15B.walk table bits 64 20521 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 2 1) = some 20522 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 1 2 1 = (SixW15B.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk11

#eval IO.monoMsNow
theorem root_00200 : SixW15B.walk table bits 64 20522 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 0 0) = some 21228 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 0 0 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk12

#eval IO.monoMsNow
theorem root_00201 : SixW15B.walk table bits 64 21228 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 0 1) = some 21639 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 0 1 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk13

#eval IO.monoMsNow
theorem root_00210 : SixW15B.walk table bits 64 21639 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 1 0) = some 21715 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 1 0 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk14

#eval IO.monoMsNow
theorem root_00211 : SixW15B.walk table bits 64 21715 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 1 1) = some 21716 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 1 1 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk15

#eval IO.monoMsNow
theorem root_00220 : SixW15B.walk table bits 64 21716 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 2 0) = some 21717 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 2 0 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk16

#eval IO.monoMsNow
theorem root_00221 : SixW15B.walk table bits 64 21717 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 2 1) = some 21718 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 0 2 2 1 = (SixW15B.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk17

#eval IO.monoMsNow
theorem root_01000 : SixW15B.walk table bits 64 21718 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 0 0) = some 24144 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 0 0 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk18

#eval IO.monoMsNow
theorem root_01001 : SixW15B.walk table bits 64 24144 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 0 1) = some 28645 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 0 1 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk19

#eval IO.monoMsNow
theorem root_01010 : SixW15B.walk table bits 64 28645 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 1 0) = some 30521 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 1 0 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk20

#eval IO.monoMsNow
theorem root_01011 : SixW15B.walk table bits 64 30521 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 1 1) = some 31502 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 1 1 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk21

#eval IO.monoMsNow
theorem root_01020 : SixW15B.walk table bits 64 31502 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 2 0) = some 31713 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 2 0 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk22

#eval IO.monoMsNow
theorem root_01021 : SixW15B.walk table bits 64 31713 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 2 1) = some 31769 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 0 2 1 = (SixW15B.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk23

#eval IO.monoMsNow
theorem root_01100 : SixW15B.walk table bits 64 31769 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 0 0) = some 33035 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 0 0 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk24

#eval IO.monoMsNow
theorem root_01101 : SixW15B.walk table bits 64 33035 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 0 1) = some 33651 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 0 1 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk25

#eval IO.monoMsNow
theorem root_01110 : SixW15B.walk table bits 64 33651 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 1 0) = some 33832 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 1 0 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk26

#eval IO.monoMsNow
theorem root_01111 : SixW15B.walk table bits 64 33832 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 1 1) = some 33833 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 1 1 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk27

#eval IO.monoMsNow
theorem root_01120 : SixW15B.walk table bits 64 33833 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 2 0) = some 33834 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 2 0 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk28

#eval IO.monoMsNow
theorem root_01121 : SixW15B.walk table bits 64 33834 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 2 1) = some 33835 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 1 2 1 = (SixW15B.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk29

#eval IO.monoMsNow
theorem root_01200 : SixW15B.walk table bits 64 33835 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 0 0) = some 33916 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 0 0 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk30

#eval IO.monoMsNow
theorem root_01201 : SixW15B.walk table bits 64 33916 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 0 1) = some 33917 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 0 1 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk31

#eval IO.monoMsNow
theorem root_01210 : SixW15B.walk table bits 64 33917 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 1 0) = some 33918 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 1 0 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk32

#eval IO.monoMsNow
theorem root_01211 : SixW15B.walk table bits 64 33918 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 1 1) = some 33919 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 1 1 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk33

#eval IO.monoMsNow
theorem root_01220 : SixW15B.walk table bits 64 33919 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 2 0) = some 33920 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 2 0 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk34

#eval IO.monoMsNow
theorem root_01221 : SixW15B.walk table bits 64 33920 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 2 1) = some 33921 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 1 2 2 1 = (SixW15B.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk35

#eval IO.monoMsNow
theorem root_02000 : SixW15B.walk table bits 64 33921 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 0 0) = some 34987 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 0 0 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk36

#eval IO.monoMsNow
theorem root_02001 : SixW15B.walk table bits 64 34987 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 0 1) = some 35678 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 0 1 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk37

#eval IO.monoMsNow
theorem root_02010 : SixW15B.walk table bits 64 35678 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 1 0) = some 35884 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 1 0 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk38

#eval IO.monoMsNow
theorem root_02011 : SixW15B.walk table bits 64 35884 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 1 1) = some 35940 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 1 1 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk39

#eval IO.monoMsNow
theorem root_02020 : SixW15B.walk table bits 64 35940 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 2 0) = some 35941 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 2 0 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk40

#eval IO.monoMsNow
theorem root_02021 : SixW15B.walk table bits 64 35941 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 2 1) = some 35942 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 0 2 1 = (SixW15B.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk41

#eval IO.monoMsNow
theorem root_02100 : SixW15B.walk table bits 64 35942 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 0 0) = some 36068 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 0 0 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk42

#eval IO.monoMsNow
theorem root_02101 : SixW15B.walk table bits 64 36068 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 0 1) = some 36069 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 0 1 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk43

#eval IO.monoMsNow
theorem root_02110 : SixW15B.walk table bits 64 36069 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 1 0) = some 36070 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 1 0 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk44

#eval IO.monoMsNow
theorem root_02111 : SixW15B.walk table bits 64 36070 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 1 1) = some 36071 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 1 1 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk45

#eval IO.monoMsNow
theorem root_02120 : SixW15B.walk table bits 64 36071 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 2 0) = some 36072 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 2 0 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk46

#eval IO.monoMsNow
theorem root_02121 : SixW15B.walk table bits 64 36072 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 2 1) = some 36073 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 1 2 1 = (SixW15B.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk47

#eval IO.monoMsNow
theorem root_02200 : SixW15B.walk table bits 64 36073 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 0 0) = some 36074 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 0 0 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk48

#eval IO.monoMsNow
theorem root_02201 : SixW15B.walk table bits 64 36074 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 0 1) = some 36075 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 0 1 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk49

#eval IO.monoMsNow
theorem root_02210 : SixW15B.walk table bits 64 36075 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 1 0) = some 36076 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 1 0 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk50

#eval IO.monoMsNow
theorem root_02211 : SixW15B.walk table bits 64 36076 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 1 1) = some 36077 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 1 1 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk51

#eval IO.monoMsNow
theorem root_02220 : SixW15B.walk table bits 64 36077 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 2 0) = some 36078 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 2 0 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk52

#eval IO.monoMsNow
theorem root_02221 : SixW15B.walk table bits 64 36078 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 2 1) = some 36079 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 0 2 2 2 1 = (SixW15B.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk53

#eval IO.monoMsNow
theorem root_10000 : SixW15B.walk table bits 64 36079 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 0 0) = some 40775 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 0 0 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk54

#eval IO.monoMsNow
theorem root_10001 : SixW15B.walk table bits 64 40775 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 0 1) = some 48981 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 0 1 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk55

#eval IO.monoMsNow
theorem root_10010 : SixW15B.walk table bits 64 48981 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 1 0) = some 53367 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 1 0 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk70

#eval IO.monoMsNow
theorem root_10011 : SixW15B.walk table bits 64 53367 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 1 1) = some 56018 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 1 1 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk71

#eval IO.monoMsNow
theorem root_10020 : SixW15B.walk table bits 64 56018 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 2 0) = some 56714 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 2 0 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk72

#eval IO.monoMsNow
theorem root_10021 : SixW15B.walk table bits 64 56714 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 2 1) = some 56860 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 0 2 1 = (SixW15B.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk73

#eval IO.monoMsNow
theorem root_10100 : SixW15B.walk table bits 64 56860 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 0 0) = some 60216 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 0 0 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk74

#eval IO.monoMsNow
theorem root_10101 : SixW15B.walk table bits 64 60216 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 0 1) = some 62352 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 0 1 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk75

#eval IO.monoMsNow
theorem root_10110 : SixW15B.walk table bits 64 62352 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 1 0) = some 62928 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 1 0 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk76

#eval IO.monoMsNow
theorem root_10111 : SixW15B.walk table bits 64 62928 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 1 1) = some 63029 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 1 1 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk77

#eval IO.monoMsNow
theorem root_10120 : SixW15B.walk table bits 64 63029 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 2 0) = some 63030 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 2 0 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk78

#eval IO.monoMsNow
theorem root_10121 : SixW15B.walk table bits 64 63030 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 2 1) = some 63031 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 1 2 1 = (SixW15B.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk79

#eval IO.monoMsNow
theorem root_10200 : SixW15B.walk table bits 64 63031 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 0 0) = some 63422 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 0 0 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk80

#eval IO.monoMsNow
theorem root_10201 : SixW15B.walk table bits 64 63422 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 0 1) = some 63503 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 0 1 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk81

#eval IO.monoMsNow
theorem root_10210 : SixW15B.walk table bits 64 63503 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 1 0) = some 63504 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 1 0 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk82

#eval IO.monoMsNow
theorem root_10211 : SixW15B.walk table bits 64 63504 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 1 1) = some 63505 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 1 1 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk83

#eval IO.monoMsNow
theorem root_10220 : SixW15B.walk table bits 64 63505 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 2 0) = some 63506 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 2 0 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk84

#eval IO.monoMsNow
theorem root_10221 : SixW15B.walk table bits 64 63506 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 2 1) = some 63507 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 0 2 2 1 = (SixW15B.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk85

#eval IO.monoMsNow
theorem root_11000 : SixW15B.walk table bits 64 63507 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 0 0) = some 66683 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 0 0 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk86

#eval IO.monoMsNow
theorem root_11001 : SixW15B.walk table bits 64 66683 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 0 1) = some 69354 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 0 1 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk87

#eval IO.monoMsNow
theorem root_11010 : SixW15B.walk table bits 64 69354 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 1 0) = some 70275 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 1 0 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk88

#eval IO.monoMsNow
theorem root_11011 : SixW15B.walk table bits 64 70275 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 1 1) = some 70401 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 1 1 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk89

#eval IO.monoMsNow
theorem root_11020 : SixW15B.walk table bits 64 70401 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 2 0) = some 70447 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 2 0 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk90

#eval IO.monoMsNow
theorem root_11021 : SixW15B.walk table bits 64 70447 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 2 1) = some 70448 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 0 2 1 = (SixW15B.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk91

#eval IO.monoMsNow
theorem root_11100 : SixW15B.walk table bits 64 70448 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 0 0) = some 71034 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 0 0 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk92

#eval IO.monoMsNow
theorem root_11101 : SixW15B.walk table bits 64 71034 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 0 1) = some 71130 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 0 1 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk93

#eval IO.monoMsNow
theorem root_11110 : SixW15B.walk table bits 64 71130 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 1 0) = some 71131 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 1 0 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk94

#eval IO.monoMsNow
theorem root_11111 : SixW15B.walk table bits 64 71131 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 1 1) = some 71132 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 1 1 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk95

#eval IO.monoMsNow
theorem root_11120 : SixW15B.walk table bits 64 71132 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 2 0) = some 71133 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 2 0 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk96

#eval IO.monoMsNow
theorem root_11121 : SixW15B.walk table bits 64 71133 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 2 1) = some 71134 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 1 2 1 = (SixW15B.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk97

#eval IO.monoMsNow
theorem root_11200 : SixW15B.walk table bits 64 71134 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 0 0) = some 71135 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 0 0 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk98

#eval IO.monoMsNow
theorem root_11201 : SixW15B.walk table bits 64 71135 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 0 1) = some 71136 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 0 1 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk99

#eval IO.monoMsNow
theorem root_11210 : SixW15B.walk table bits 64 71136 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 1 0) = some 71137 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 1 0 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk100

#eval IO.monoMsNow
theorem root_11211 : SixW15B.walk table bits 64 71137 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 1 1) = some 71138 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 1 1 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk101

#eval IO.monoMsNow
theorem root_11220 : SixW15B.walk table bits 64 71138 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 2 0) = some 71139 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 2 0 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk102

#eval IO.monoMsNow
theorem root_11221 : SixW15B.walk table bits 64 71139 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 2 1) = some 71140 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 1 2 2 1 = (SixW15B.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk103

#eval IO.monoMsNow
theorem root_12000 : SixW15B.walk table bits 64 71140 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 0 0) = some 71796 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 0 0 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk104

#eval IO.monoMsNow
theorem root_12001 : SixW15B.walk table bits 64 71796 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 0 1) = some 71942 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 0 1 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk105

#eval IO.monoMsNow
theorem root_12010 : SixW15B.walk table bits 64 71942 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 1 0) = some 71988 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 1 0 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk106

#eval IO.monoMsNow
theorem root_12011 : SixW15B.walk table bits 64 71988 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 1 1) = some 71989 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 1 1 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk107

#eval IO.monoMsNow
theorem root_12020 : SixW15B.walk table bits 64 71989 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 2 0) = some 71990 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 2 0 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk108

#eval IO.monoMsNow
theorem root_12021 : SixW15B.walk table bits 64 71990 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 2 1) = some 71991 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 0 2 1 = (SixW15B.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk109

#eval IO.monoMsNow
theorem root_12100 : SixW15B.walk table bits 64 71991 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 0 0) = some 71992 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 0 0 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk110

#eval IO.monoMsNow
theorem root_12101 : SixW15B.walk table bits 64 71992 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 0 1) = some 71993 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 0 1 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk111

#eval IO.monoMsNow
theorem root_12110 : SixW15B.walk table bits 64 71993 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 1 0) = some 71994 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 1 0 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk112

#eval IO.monoMsNow
theorem root_12111 : SixW15B.walk table bits 64 71994 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 1 1) = some 71995 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 1 1 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk113

#eval IO.monoMsNow
theorem root_12120 : SixW15B.walk table bits 64 71995 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 2 0) = some 71996 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 2 0 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk114

#eval IO.monoMsNow
theorem root_12121 : SixW15B.walk table bits 64 71996 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 2 1) = some 71997 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 1 2 1 = (SixW15B.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk115

#eval IO.monoMsNow
theorem root_12200 : SixW15B.walk table bits 64 71997 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 0 0) = some 71998 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 0 0 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk116

#eval IO.monoMsNow
theorem root_12201 : SixW15B.walk table bits 64 71998 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 0 1) = some 71999 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 0 1 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk117

#eval IO.monoMsNow
theorem root_12210 : SixW15B.walk table bits 64 71999 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 1 0) = some 72000 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 1 0 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk118

#eval IO.monoMsNow
theorem root_12211 : SixW15B.walk table bits 64 72000 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 1 1) = some 72001 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 1 1 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk119

#eval IO.monoMsNow
theorem root_12220 : SixW15B.walk table bits 64 72001 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 2 0) = some 72002 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 2 0 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk120

#eval IO.monoMsNow
theorem root_12221 : SixW15B.walk table bits 64 72002 (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 2 1) = some 72003 := by
  rw [show SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) 1 2 2 2 1 = (SixW15B.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk121

#eval IO.monoMsNow
theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW15B.badOf cover0).length → i1 < (SixW15B.badOf cover1).length → i2 < (SixW15B.badOf cover2).length → i3 < (SixW15B.badOf cover3).length → i4 < (SixW15B.badOf cover4).length →
    ∃ pos pos', SixW15B.walk table bits 64 pos (SixW15B.boxOf (SixW15B.badOf cover0) (SixW15B.badOf cover1) (SixW15B.badOf cover2) (SixW15B.badOf cover3) (SixW15B.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
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

#eval IO.monoMsNow
theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW15B.cN : ℝ) / SixW15B.SA ≤ SixW15B.G g0 g1 g2 g3 g4 :=
  SixW15B.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 401408 237568 221184 237568 409600
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


#eval IO.monoMsNow
end Zeta23Ext.Bridge.ThreePoint.SixW15BData

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

/-- The pinned record is `HD 1`. -/
theorem currentRecordKappa_eq : currentRecordKappa = HD 1 := by
  unfold currentRecordKappa Zeta23.ThmD.HD
  rw [cStar_one_eq_cMT]

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩


end RiemannFail

end

/-! ###### the 6-point weighted bound from the checked certificate `SixW15B` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW Zeta23Ext.Bridge.ThreePoint

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW : Fin 6 → Fin 6 → ℝ
  | 0, 1 => (25715100 : ℝ) / 100000000
  | 0, 2 => (61242800 : ℝ) / 100000000
  | 0, 3 => (40905100 : ℝ) / 100000000
  | 0, 4 => (104929600 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (48318100 : ℝ) / 100000000
  | 1, 3 => (40072400 : ℝ) / 100000000
  | 1, 4 => (119746800 : ℝ) / 100000000
  | 1, 5 => (95070300 : ℝ) / 100000000
  | 2, 3 => (52857300 : ℝ) / 100000000
  | 2, 4 => (35189000 : ℝ) / 100000000
  | 2, 5 => (39348000 : ℝ) / 100000000
  | 3, 4 => (48170700 : ℝ) / 100000000
  | 3, 5 => (63495600 : ℝ) / 100000000
  | 4, 5 => (24938600 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ
  | 0 => (25232 : ℝ) / 100000000
  | 1 => (42025 : ℝ) / 100000000
  | 2 => (46137 : ℝ) / 100000000
  | 3 => (42044 : ℝ) / 100000000
  | 4 => (24559 : ℝ) / 100000000

def WW : WCert 6 := ⟨aW, bW⟩

theorem aW_0_0 : aW 0 0 = 0 := rfl
theorem aW_0_1 : aW 0 1 = (25715100 : ℝ) / 100000000 := rfl
theorem aW_0_2 : aW 0 2 = (61242800 : ℝ) / 100000000 := rfl
theorem aW_0_3 : aW 0 3 = (40905100 : ℝ) / 100000000 := rfl
theorem aW_0_4 : aW 0 4 = (104929600 : ℝ) / 100000000 := rfl
theorem aW_0_5 : aW 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW_1_0 : aW 1 0 = 0 := rfl
theorem aW_1_1 : aW 1 1 = 0 := rfl
theorem aW_1_2 : aW 1 2 = (48318100 : ℝ) / 100000000 := rfl
theorem aW_1_3 : aW 1 3 = (40072400 : ℝ) / 100000000 := rfl
theorem aW_1_4 : aW 1 4 = (119746800 : ℝ) / 100000000 := rfl
theorem aW_1_5 : aW 1 5 = (95070300 : ℝ) / 100000000 := rfl
theorem aW_2_0 : aW 2 0 = 0 := rfl
theorem aW_2_1 : aW 2 1 = 0 := rfl
theorem aW_2_2 : aW 2 2 = 0 := rfl
theorem aW_2_3 : aW 2 3 = (52857300 : ℝ) / 100000000 := rfl
theorem aW_2_4 : aW 2 4 = (35189000 : ℝ) / 100000000 := rfl
theorem aW_2_5 : aW 2 5 = (39348000 : ℝ) / 100000000 := rfl
theorem aW_3_0 : aW 3 0 = 0 := rfl
theorem aW_3_1 : aW 3 1 = 0 := rfl
theorem aW_3_2 : aW 3 2 = 0 := rfl
theorem aW_3_3 : aW 3 3 = 0 := rfl
theorem aW_3_4 : aW 3 4 = (48170700 : ℝ) / 100000000 := rfl
theorem aW_3_5 : aW 3 5 = (63495600 : ℝ) / 100000000 := rfl
theorem aW_4_0 : aW 4 0 = 0 := rfl
theorem aW_4_1 : aW 4 1 = 0 := rfl
theorem aW_4_2 : aW 4 2 = 0 := rfl
theorem aW_4_3 : aW 4 3 = 0 := rfl
theorem aW_4_4 : aW 4 4 = 0 := rfl
theorem aW_4_5 : aW 4 5 = (24938600 : ℝ) / 100000000 := rfl
theorem aW_5_0 : aW 5 0 = 0 := rfl
theorem aW_5_1 : aW 5 1 = 0 := rfl
theorem aW_5_2 : aW 5 2 = 0 := rfl
theorem aW_5_3 : aW 5 3 = 0 := rfl
theorem aW_5_4 : aW 5 4 = 0 := rfl
theorem aW_5_5 : aW 5 5 = 0 := rfl
theorem bW_0 : bW 0 = (25232 : ℝ) / 100000000 := rfl
theorem bW_1 : bW 1 = (42025 : ℝ) / 100000000 := rfl
theorem bW_2 : bW 2 = (46137 : ℝ) / 100000000 := rfl
theorem bW_3 : bW 3 = (42044 : ℝ) / 100000000 := rfl
theorem bW_4 : bW 4 = (24559 : ℝ) / 100000000 := rfl

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

theorem WW_bmin : ∀ r, ((24559 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((24559 : ℝ) / 100000000) ≤ bW 0; norm_num [bW_0]
  | 1 => show ((24559 : ℝ) / 100000000) ≤ bW 1; norm_num [bW_1]
  | 2 => show ((24559 : ℝ) / 100000000) ≤ bW 2; norm_num [bW_2]
  | 3 => show ((24559 : ℝ) / 100000000) ≤ bW 3; norm_num [bW_3]
  | 4 => show ((24559 : ℝ) / 100000000) ≤ bW 4; norm_num [bW_4]

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

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW15B.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW15B.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW15B.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW15B.SA]
  try ring

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (304544 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := SixW15BData.cert (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW15B.cN, SixW15B.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 333 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((304544 : ℝ) / 100000000) 333 ((179997 : ℝ) / 100000000)
    = (4162500000 * HD 1 - 7379877) / 4150013696 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((4162500000 * HD 1 - 7379877) / 4150013696 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((304544 : ℝ) / 100000000) 333 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24559 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (4162500000 * HD 1 - 7379877) / 4150013696 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4150013696)]
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
      ≤ ((4162500000 * HD 1 - 7379877) / 4150013696 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
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

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
