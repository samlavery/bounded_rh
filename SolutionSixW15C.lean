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

/-! ###### natural-number checker for the 6-point weighted certificate `SixW15C` ###### -/

section SixW15CDefs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (LN UN : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000
def SC4 : ℕ := 8192

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
def find : CTN → ℕ → ℕ → Option CellN
  | nil, _, _ => none
  | node l c r, a, b =>
      bif Nat.blt a c.LN then l.find a b
      else bif Nat.blt c.LN a then r.find a b
      else bif Nat.blt b c.UN then l.find a b
      else bif Nat.blt c.UN b then r.find a b
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
      match t.find a b, lookupAllN t rest with
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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15C

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

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk tb bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else bif leafCheck tb b then some (pos + 1) else none

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear
segment's cell must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WN ≥ cN * SW`. -/
def coverCheck (tb : CTN) (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match tb.find a b with | some c => decide (cN * SW ≤ aAdjN * c.WN) | none => false))
        && coverCheck tb aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

def boxOf (bd0 bd1 bd2 bd3 bd4 : List (ℕ × ℕ)) (i0 i1 i2 i3 i4 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2, (bd3.getD i3 (0, 0)).1, (bd3.getD i3 (0, 0)).2, (bd4.getD i4 (0, 0)).1, (bd4.getD i4 (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint.SixW15C

end SixW15CDefs

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

theorem CTN.find_sound : ∀ (t : CTN) (a b : ℕ) (c : CellN), t.find a b = some c →
    c ∈ t.toList ∧ c.LN = a ∧ c.UN = b := by
  intro t
  induction t with
  | nil => intro a b c h; simp [CTN.find] at h
  | node l c0 r ihl ihr =>
    intro a b c h
    simp only [CTN.find, Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with h1 h2 h3 h4
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp [CTN.toList], le_antisymm (not_lt.mp h1) (not_lt.mp h2),
        le_antisymm (not_lt.mp h3) (not_lt.mp h4)⟩

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
    cases hf : t.find a b with
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
        · subst hd; exact (CTN.find_sound t a b d hf).1
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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15C

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
    (h1 : walk tb bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
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
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 g0 g1 g2 g3 g4
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h g0 g1 g2 g3 g4
        set ax := b.widthArg with hax
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
          obtain ⟨hmem, hL, hU⟩ := CTN.find_sound tb a b c hfind
          have hcok := CTN.allOk_sound tb hok c hmem
          have hW := cellN_sound c hcok v (by rw [hL, hpos]; exact hv1) (by rw [hU]; exact hvb)
          have hq := (Nat.cast_le (α := ℝ)).mpr (decide_eq_true_eq.mp hcl)
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

end Zeta23Ext.Bridge.ThreePoint.SixW15C

end

/-! ###### certificate data `SixW15C`: 11109 cells, 14487 leaves ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW15CData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW15C

set_option maxRecDepth 100000

noncomputable def tab0 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨16384, 24576, 331038177865⟩ CTN.nil) ⟨24576, 28672, 242869129569⟩ CTN.nil) ⟨28672, 30720, 122761883704⟩ (CTN.node (CTN.node CTN.nil ⟨30720, 31744, 69269436296⟩ CTN.nil) ⟨30720, 31872, 62652449971⟩ CTN.nil)) ⟨30720, 32768, 27393363819⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨31744, 32512, 36843158376⟩ CTN.nil) ⟨31744, 32576, 34548539408⟩ CTN.nil) ⟨31744, 32768, 28203622388⟩ (CTN.node CTN.nil ⟨31872, 32448, 39350240729⟩ CTN.nil))) ⟨31872, 32768, 28267587364⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨32448, 32768, 28450417775⟩ CTN.nil) ⟨32512, 32768, 28460062200⟩ CTN.nil) ⟨32576, 32768, 28467564926⟩ (CTN.node (CTN.node CTN.nil ⟨32768, 32992, 21788669253⟩ CTN.nil) ⟨32768, 33024, 20912356297⟩ CTN.nil)) ⟨32768, 33280, 14596526138⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨32768, 33408, 11891897536⟩ CTN.nil) ⟨32992, 33408, 11891897536⟩ CTN.nil) ⟨33024, 33600, 8384490092⟩ (CTN.node CTN.nil ⟨33024, 34176, 1626727581⟩ CTN.nil)))) ⟨33280, 33664, 7358852099⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨33280, 34048, 2658307323⟩ CTN.nil) ⟨33408, 33824, 5101426618⟩ CTN.nil) ⟨33408, 34240, 1207853390⟩ (CTN.node (CTN.node CTN.nil ⟨33600, 34176, 1626727581⟩ CTN.nil) ⟨33664, 34048, 2658307323⟩ CTN.nil)) ⟨33824, 34240, 1207853390⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨34656, 35072, 840527⟩ CTN.nil) ⟨34752, 35328, 76228626⟩ CTN.nil) ⟨34816, 35584, 189390231⟩ (CTN.node CTN.nil ⟨34816, 36352, 173234703⟩ CTN.nil))) ⟨34816, 37888, 145808985⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨35072, 35904, 1151561664⟩ CTN.nil) ⟨35072, 36736, 1046595949⟩ CTN.nil) ⟨35072, 38400, 870430129⟩ (CTN.node (CTN.node CTN.nil ⟨35328, 35904, 2982576597⟩ CTN.nil) ⟨35328, 36480, 2790908306⟩ CTN.nil)) ⟨35328, 37632, 2451923401⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨35328, 39936, 1916013694⟩ CTN.nil) ⟨35584, 36352, 5416703501⟩ CTN.nil) ⟨35904, 36480, 9732001830⟩ (CTN.node CTN.nil ⟨35904, 36736, 9452356006⟩ CTN.nil))))) ⟨36352, 37888, 15563604115⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨36480, 37632, 18591409084⟩ CTN.nil) ⟨36736, 38400, 22408627075⟩ CTN.nil) ⟨37632, 39936, 40016092176⟩ (CTN.node (CTN.node CTN.nil ⟨37888, 38016, 58284410507⟩ CTN.nil) ⟨38016, 38144, 62313805310⟩ CTN.nil)) ⟨38144, 38400, 65509628502⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨38400, 38912, 71849923330⟩ CTN.nil) ⟨38912, 40960, 75832144115⟩ CTN.nil) ⟨39936, 40448, 124701346738⟩ (CTN.node CTN.nil ⟨40448, 40960, 143033504697⟩ CTN.nil))) ⟨40960, 43008, 138814108272⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨40960, 49152, 80226784524⟩ CTN.nil) ⟨43008, 45056, 198611196246⟩ CTN.nil) ⟨45056, 49152, 205420959916⟩ (CTN.node (CTN.node CTN.nil ⟨49152, 53248, 198637449669⟩ CTN.nil) ⟨49152, 57344, 86044756753⟩ CTN.nil)) ⟨53248, 55296, 180021136485⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨55296, 57344, 129277608381⟩ CTN.nil) ⟨57344, 57856, 126832062122⟩ CTN.nil) ⟨57344, 59392, 81450895201⟩ (CTN.node CTN.nil ⟨57856, 60540, 56104174470⟩ CTN.nil)))) ⟨57856, 60604, 54744524444⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨57856, 63224, 14490230268⟩ CTN.nil) ⟨57856, 63352, 13248302275⟩ CTN.nil) ⟨59392, 60416, 63653684247⟩ (CTN.node (CTN.node CTN.nil ⟨60416, 62080, 32801554392⟩ CTN.nil) ⟨60416, 62144, 31761760685⟩ CTN.nil)) ⟨60416, 63744, 11699544709⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨60416, 63872, 10561059564⟩ CTN.nil) ⟨60540, 61882, 36353090489⟩ CTN.nil) ⟨60540, 63224, 17122242272⟩ (CTN.node CTN.nil ⟨60604, 61978, 34808283285⟩ CTN.nil))) ⟨60604, 63352, 15757039412⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨61882, 63224, 18266655065⟩ CTN.nil) ⟨61978, 63352, 16837648072⟩ CTN.nil) ⟨62080, 63744, 12731502888⟩ (CTN.node CTN.nil ⟨62144, 63008, 21197196115⟩ CTN.nil)) ⟨62144, 63872, 11542172995⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨62464, 65280, 2408056665⟩ CTN.nil) ⟨62464, 65536, 1506819731⟩ CTN.nil) ⟨63008, 63872, 11958745632⟩ (CTN.node CTN.nil ⟨63224, 63895, 11832935104⟩ CTN.nil)))))) ⟨63224, 64566, 6357569415⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨63224, 65536, 1565943956⟩ CTN.nil) ⟨63352, 64039, 10546933738⟩ CTN.nil) ⟨63352, 64726, 5348283391⟩ (CTN.node (CTN.node CTN.nil ⟨63352, 65536, 1574380871⟩ CTN.nil) ⟨63616, 65536, 1590346721⟩ CTN.nil)) ⟨63744, 64160, 9616293499⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨63744, 64576, 6405326128⟩ CTN.nil) ⟨63744, 65408, 2041289663⟩ CTN.nil) ⟨63872, 64304, 8457379249⟩ (CTN.node CTN.nil ⟨63872, 64736, 5380608052⟩ CTN.nil))) ⟨63872, 65536, 1603951009⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨63895, 64566, 6505110531⟩ CTN.nil) ⟨64039, 64726, 5470768786⟩ CTN.nil) ⟨64160, 64576, 6486530866⟩ (CTN.node (CTN.node CTN.nil ⟨64304, 64736, 5447824625⟩ CTN.nil) ⟨64448, 65536, 1627636972⟩ CTN.nil)) ⟨64566, 65237, 2786489703⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨64566, 65536, 1631286091⟩ CTN.nil) ⟨64576, 64992, 3983824195⟩ CTN.nil) ⟨64576, 65408, 2086096939⟩ (CTN.node CTN.nil ⟨64726, 65413, 2072780895⟩ CTN.nil)))) ⟨64726, 65536, 1635572606⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨64736, 65168, 3110902549⟩ CTN.nil) ⟨64736, 65536, 1635815150⟩ CTN.nil) ⟨64992, 65408, 2099820129⟩ (CTN.node (CTN.node CTN.nil ⟨65168, 65536, 1643428677⟩ CTN.nil) ⟨65237, 65536, 1644124289⟩ CTN.nil)) ⟨65408, 65536, 1645228303⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨65413, 65536, 1645247283⟩ CTN.nil) ⟨65536, 65600, 1436255057⟩ CTN.nil) ⟨65536, 65824, 817796385⟩ (CTN.node CTN.nil ⟨65536, 65908, 631150126⟩ CTN.nil))) ⟨65536, 66100, 296183929⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨65536, 66240, 131485341⟩ CTN.nil) ⟨65536, 66432, 13164037⟩ CTN.nil) ⟨65600, 66032, 400308901⟩ (CTN.node (CTN.node CTN.nil ⟨65600, 66464, 5411364⟩ CTN.nil) ⟨65824, 66240, 131485341⟩ CTN.nil)) ⟨66032, 66464, 5411364⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨66560, 68928, 2144977⟩ CTN.nil) ⟨66560, 69760, 2043342⟩ CTN.nil) ⟨66560, 71296, 1871060⟩ (CTN.node CTN.nil ⟨66560, 72960, 1704455⟩ CTN.nil))))) ⟨66579, 67250, 5267032⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨66592, 67584, 7751317⟩ CTN.nil) ⟨66624, 68224, 15751742⟩ CTN.nil) ⟨66688, 67872, 42441413⟩ (CTN.node (CTN.node CTN.nil ⟨66688, 68288, 41404619⟩ CTN.nil) ⟨66688, 69056, 39572543⟩ CTN.nil)) ⟨66688, 69888, 37700926⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨66752, 68352, 79129267⟩ CTN.nil) ⟨66752, 68736, 77355470⟩ CTN.nil) ⟨66787, 67474, 110700553⟩ (CTN.node CTN.nil ⟨66816, 70016, 117345383⟩ CTN.nil))) ⟨66816, 71552, 107486576⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨66816, 73216, 97948609⟩ CTN.nil) ⟨66816, 73728, 95228999⟩ CTN.nil) ⟨66848, 67840, 164002603⟩ (CTN.node (CTN.node CTN.nil ⟨66944, 69760, 245844939⟩ CTN.nil) ⟨67008, 68000, 362028761⟩ CTN.nil)) ⟨67008, 68416, 353201598⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨67072, 68736, 444465767⟩ CTN.nil) ⟨67072, 69056, 436190422⟩ CTN.nil) ⟨67072, 69888, 415560422⟩ (CTN.node CTN.nil ⟨67072, 70400, 403470914⟩ CTN.nil)))) ⟨67072, 71040, 388971858⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨67072, 72704, 354216357⟩ CTN.nil) ⟨67072, 73728, 334751802⟩ CTN.nil) ⟨67104, 67904, 523183766⟩ (CTN.node (CTN.node CTN.nil ⟨67104, 68288, 511377759⟩ CTN.nil) ⟨67250, 67921, 820332143⟩ CTN.nil)) ⟨67250, 68592, 788334247⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨67264, 68256, 835637430⟩ CTN.nil) ⟨67264, 68672, 815339532⟩ CTN.nil) ⟨67264, 69248, 788243580⟩ (CTN.node CTN.nil ⟨67328, 68192, 991130713⟩ CTN.nil))) ⟨67328, 69056, 941896883⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨67328, 70784, 852286103⟩ CTN.nil) ⟨67328, 73728, 722853285⟩ CTN.nil) ⟨67392, 69760, 1054752212⟩ (CTN.node CTN.nil ⟨67424, 68416, 1227463388⟩ CTN.nil)) ⟨67456, 68640, 1299696151⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨67456, 69056, 1268304108⟩ CTN.nil) ⟨67456, 71424, 1106621505⟩ CTN.nil) ⟨67474, 68848, 1334354826⟩ (CTN.node CTN.nil ⟨67488, 68288, 1420479279⟩ CTN.nil))))))) ⟨67520, 68320, 1514303517⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨67520, 68704, 1480342169⟩ CTN.nil) ⟨67520, 69120, 1444620480⟩ CTN.nil) ⟨67520, 69888, 1381464137⟩ (CTN.node (CTN.node CTN.nil ⟨67584, 68576, 1691264844⟩ CTN.nil) ⟨67584, 68992, 1650376680⟩ CTN.nil)) ⟨67584, 69568, 1595784993⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨67584, 70400, 1520862133⟩ CTN.nil) ⟨67680, 68672, 2003471324⟩ CTN.nil) ⟨67840, 69248, 2517166723⟩ (CTN.node CTN.nil ⟨67872, 69056, 2672385180⟩ CTN.nil))) ⟨67904, 68704, 2860864534⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨67904, 69888, 2669775839⟩ CTN.nil) ⟨67921, 68592, 2952065098⟩ CTN.nil) ⟨67936, 69120, 2924410492⟩ (CTN.node (CTN.node CTN.nil ⟨68000, 68992, 3223080944⟩ CTN.nil) ⟨68096, 70080, 3437242548⟩ CTN.nil)) ⟨68096, 70912, 3277032161⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨68096, 71296, 3206246751⟩ CTN.nil) ⟨68096, 72064, 3070329399⟩ CTN.nil) ⟨68096, 73728, 2799744336⟩ (CTN.node CTN.nil ⟨68160, 69568, 3838928819⟩ CTN.nil)))) ⟨68192, 69056, 4113772714⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨68224, 69824, 4088246003⟩ CTN.nil) ⟨68224, 70592, 3911307061⟩ CTN.nil) ⟨68224, 71040, 3812514736⟩ (CTN.node (CTN.node CTN.nil ⟨68224, 71424, 3730312206⟩ CTN.nil) ⟨68224, 72960, 3422887433⟩ CTN.nil)) ⟨68288, 69888, 4390031577⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨68352, 71552, 4290708233⟩ CTN.nil) ⟨68416, 70400, 4912999674⟩ CTN.nil) ⟨68480, 73216, 4485350389⟩ (CTN.node CTN.nil ⟨68592, 69934, 6044893012⟩ CTN.nil))) ⟨68592, 71276, 5597633759⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨68592, 73728, 4882398868⟩ CTN.nil) ⟨68736, 70400, 6746069797⟩ CTN.nil) ⟨68736, 71552, 6317518618⟩ (CTN.node (CTN.node CTN.nil ⟨68736, 72704, 5922529203⟩ CTN.nil) ⟨68848, 71596, 6966292538⟩ CTN.nil)) ⟨68848, 73728, 6187227555⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨68928, 70912, 7756885020⟩ CTN.nil) ⟨68992, 70592, 8332703272⟩ CTN.nil) ⟨69056, 70784, 8681119975⟩ (CTN.node CTN.nil ⟨69056, 71424, 8370847260⟩ CTN.nil))))) ⟨69248, 72064, 9364788646⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨69376, 73728, 9372677031⟩ CTN.nil) ⟨69760, 72960, 12627844833⟩ CTN.nil) ⟨69760, 73728, 12104668324⟩ (CTN.node (CTN.node CTN.nil ⟨69888, 72704, 13853481102⟩ CTN.nil) ⟨69888, 73728, 13092218008⟩ CTN.nil)) ⟨69934, 71276, 15427701477⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨70400, 73728, 17420620864⟩ CTN.nil) ⟨70784, 73728, 21055464219⟩ CTN.nil) ⟨71276, 73728, 26181050867⟩ (CTN.node CTN.nil ⟨71596, 73728, 29785550033⟩ CTN.nil))) ⟨73728, 73960, 57736288205⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨73728, 73984, 57660655940⟩ CTN.nil) ⟨73728, 74240, 56861581616⟩ CTN.nil) ⟨73728, 74344, 56540921948⟩ (CTN.node (CTN.node CTN.nil ⟨73728, 75008, 54546146546⟩ CTN.nil) ⟨73728, 76288, 50943335175⟩ CTN.nil)) ⟨73728, 78336, 45776641928⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨73728, 79328, 43510134591⟩ CTN.nil) ⟨73728, 79840, 42395280650⟩ CTN.nil) ⟨73960, 79328, 46130130415⟩ (CTN.node CTN.nil ⟨73984, 74240, 60643085590⟩ CTN.nil)))) ⟨74240, 74496, 63602331360⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨74240, 74752, 62727040513⟩ CTN.nil) ⟨74344, 79840, 49264488826⟩ CTN.nil) ⟨74496, 74752, 66530373098⟩ (CTN.node (CTN.node CTN.nil ⟨74752, 75776, 66621352329⟩ CTN.nil) ⟨75776, 77824, 73216762336⟩ CTN.nil)) ⟨77824, 81920, 81183335634⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨79328, 81920, 95435097263⟩ CTN.nil) ⟨79840, 81920, 99708153753⟩ CTN.nil) ⟨81920, 86016, 79111303097⟩ (CTN.node CTN.nil ⟨81920, 90064, 38860075235⟩ CTN.nil))) ⟨81920, 90112, 38423148027⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨86016, 88064, 68661704304⟩ CTN.nil) ⟨88064, 88576, 67628919902⟩ CTN.nil) ⟨88064, 89088, 61427731673⟩ (CTN.node CTN.nil ⟨88576, 88832, 65677920649⟩ CTN.nil)) ⟨88832, 88960, 64676607906⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨88832, 89088, 63103400105⟩ CTN.nil) ⟨88960, 89088, 63381401765⟩ CTN.nil) ⟨89088, 89344, 60519493235⟩ (CTN.node CTN.nil ⟨89088, 90112, 51392597158⟩ CTN.nil)))))) ⟨89344, 89600, 57931894547⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨89600, 90112, 52311507142⟩ CTN.nil) ⟨90064, 90112, 53137584618⟩ CTN.nil) ⟨90112, 90832, 44898239526⟩ (CTN.node (CTN.node CTN.nil ⟨90112, 92748, 25713477686⟩ CTN.nil) ⟨90112, 93712, 17965572406⟩ CTN.nil)) ⟨90112, 93728, 17848583852⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨90112, 95432, 7621693323⟩ CTN.nil) ⟨90112, 95612, 6800702072⟩ CTN.nil) ⟨90112, 95676, 6520655021⟩ (CTN.node CTN.nil ⟨90112, 97824, 608823085⟩ CTN.nil))) ⟨90112, 98296, 165286845⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨90112, 98304, 160224349⟩ CTN.nil) ⟨90832, 93580, 19477292869⟩ CTN.nil) ⟨90832, 96328, 4182766391⟩ (CTN.node (CTN.node CTN.nil ⟨91136, 96896, 2510874330⟩ CTN.nil) ⟨92160, 96960, 2488359274⟩ CTN.nil)) ⟨92160, 97152, 2005828299⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨92160, 98304, 221539557⟩ CTN.nil) ⟨92284, 96632, 3461637059⟩ CTN.nil) ⟨92284, 98296, 231189510⟩ (CTN.node CTN.nil ⟨92348, 96760, 3078815243⟩ CTN.nil)))) ⟨92348, 98304, 226834761⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨92748, 94090, 16885861029⟩ CTN.nil) ⟨92748, 95432, 8536991830⟩ CTN.nil) ⟨92928, 98304, 242596132⟩ (CTN.node (CTN.node CTN.nil ⟨93440, 97472, 1427192342⟩ CTN.nil) ⟨93580, 94954, 11498381159⟩ CTN.nil)) ⟨93580, 96328, 4748454477⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨93712, 95768, 7158732196⟩ CTN.nil) ⟨93712, 97824, 824867816⟩ CTN.nil) ⟨93728, 94888, 11958562382⟩ (CTN.node CTN.nil ⟨93728, 96048, 5905315798⟩ CTN.nil))) ⟨93728, 98304, 262627654⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨93824, 97152, 2185018972⟩ CTN.nil) ⟨93824, 98304, 264878549⟩ CTN.nil) ⟨93888, 97152, 2191291061⟩ (CTN.node (CTN.node CTN.nil ⟨93888, 98304, 266359493⟩ CTN.nil) ⟨93948, 96954, 2728728717⟩ CTN.nil)) ⟨93948, 98296, 274562977⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨94012, 97050, 2470133859⟩ CTN.nil) ⟨94012, 98304, 269183140⟩ CTN.nil) ⟨94090, 95432, 8948919475⟩ (CTN.node CTN.nil ⟨94592, 97472, 1509069493⟩ CTN.nil))))) ⟨94592, 98304, 281547652⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨94888, 96048, 6141282325⟩ CTN.nil) ⟨94954, 95641, 8087907822⟩ CTN.nil) ⟨94954, 96328, 4984518345⟩ (CTN.node (CTN.node CTN.nil ⟨94968, 97142, 2315486609⟩ CTN.nil) ⟨94968, 97974, 660457891⟩ CTN.nil)) ⟨95096, 97302, 1924051839⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨95096, 98134, 463889602⟩ CTN.nil) ⟨95168, 97184, 2222401197⟩ CTN.nil) ⟨95168, 98048, 569141180⟩ (CTN.node CTN.nil ⟨95290, 97464, 1568994808⟩ CTN.nil))) ⟨95290, 98296, 301693756⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨95386, 97592, 1311222496⟩ CTN.nil) ⟨95386, 98304, 296016137⟩ CTN.nil) ⟨95424, 97824, 899130967⟩ (CTN.node (CTN.node CTN.nil ⟨95424, 98304, 296632190⟩ CTN.nil) ⟨95432, 96103, 5998708048⟩ CTN.nil)) ⟨95432, 96774, 3441937205⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨95432, 98116, 492729421⟩ CTN.nil) ⟨95488, 97984, 662577731⟩ CTN.nil) ⟨95488, 98304, 297653366⟩ (CTN.node CTN.nil ⟨95616, 98304, 299633480⟩ CTN.nil)))) ⟨95641, 96328, 5088395683⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨95744, 97760, 1017344218⟩ CTN.nil) ⟨95768, 96796, 3404954463⟩ CTN.nil) ⟨95768, 97824, 911071643⟩ (CTN.node (CTN.node CTN.nil ⟨95800, 97974, 684960813⟩ CTN.nil) ⟨95928, 98134, 482050048⟩ CTN.nil)) ⟨96032, 98048, 590452852⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨96048, 96628, 4004866175⟩ CTN.nil) ⟨96048, 97208, 2223049757⟩ CTN.nil) ⟨96048, 98304, 305689821⟩ (CTN.node CTN.nil ⟨96103, 96774, 3509574532⟩ CTN.nil))) ⟨96122, 98296, 314108631⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨96218, 98304, 307801662⟩ CTN.nil) ⟨96288, 97920, 775774854⟩ CTN.nil) ⟨96288, 98304, 308625792⟩ (CTN.node CTN.nil ⟨96310, 98304, 308879290⟩ CTN.nil)) ⟨96320, 97984, 683366334⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨96320, 98304, 308993641⟩ CTN.nil) ⟨96328, 97015, 2776039722⟩ CTN.nil) ⟨96328, 97702, 1140980626⟩ (CTN.node CTN.nil ⟨96470, 98304, 310643051⟩ CTN.nil))))))))

noncomputable def tab1 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨96628, 97208, 2257837150⟩ CTN.nil) ⟨96632, 97719, 1119360397⟩ CTN.nil) ⟨96632, 98135, 492628661⟩ (CTN.node (CTN.node CTN.nil ⟨96632, 98304, 312284618⟩ CTN.nil) ⟨96760, 98279, 337583423⟩ CTN.nil)) ⟨96760, 98304, 313477975⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨96774, 97445, 1684190154⟩ CTN.nil) ⟨96774, 98116, 517581649⟩ CTN.nil) ⟨96796, 97824, 940202692⟩ (CTN.node CTN.nil ⟨96896, 97904, 813574295⟩ CTN.nil))) ⟨96896, 98304, 314644752⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨97015, 97702, 1161337579⟩ CTN.nil) ⟨97048, 98135, 497944572⟩ CTN.nil) ⟨97056, 98304, 315882938⟩ (CTN.node (CTN.node CTN.nil ⟨97142, 98304, 316487997⟩ CTN.nil) ⟨97152, 98304, 316555598⟩ CTN.nil)) ⟨97184, 98304, 316768058⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨97208, 97788, 1010656676⟩ CTN.nil) ⟨97208, 98304, 316923535⟩ CTN.nil) ⟨97302, 98304, 317500505⟩ (CTN.node CTN.nil ⟨97303, 98304, 317506369⟩ CTN.nil)))) ⟨97328, 98304, 317651080⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨97445, 98116, 525188127⟩ CTN.nil) ⟨97447, 98304, 318290256⟩ CTN.nil) ⟨97464, 98304, 318374856⟩ (CTN.node (CTN.node CTN.nil ⟨97472, 98304, 318414087⟩ CTN.nil) ⟨97568, 98304, 318855792⟩ CTN.nil)) ⟨97584, 98304, 318924188⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨97702, 98304, 319382434⟩ CTN.nil) ⟨97719, 98304, 319441743⟩ CTN.nil) ⟨97760, 98304, 319577821⟩ (CTN.node CTN.nil ⟨97788, 98304, 319665093⟩ CTN.nil))) ⟨97824, 98304, 319770546⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨97863, 98304, 319876207⟩ CTN.nil) ⟨97904, 98304, 319977661⟩ CTN.nil) ⟨97984, 98304, 320147185⟩ (CTN.node (CTN.node CTN.nil ⟨98016, 98304, 320204460⟩ CTN.nil) ⟨98116, 98304, 320344615⟩ CTN.nil)) ⟨98304, 98336, 290120585⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨98304, 98352, 275526942⟩ CTN.nil) ⟨98304, 98368, 261313260⟩ CTN.nil) ⟨98304, 98389, 243234019⟩ (CTN.node CTN.nil ⟨98304, 98390, 242389409⟩ CTN.nil))))) ⟨98304, 98400, 234024811⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨98304, 98424, 214554052⟩ CTN.nil) ⟨98304, 98480, 172435688⟩ CTN.nil) ⟨98304, 98484, 169604524⟩ (CTN.node (CTN.node CTN.nil ⟨98304, 98550, 126296827⟩ CTN.nil) ⟨98304, 98624, 85361675⟩ CTN.nil)) ⟨98304, 98645, 75208942⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨98304, 98676, 61402067⟩ CTN.nil) ⟨98304, 98688, 56434938⟩ CTN.nil) ⟨98304, 98768, 28693336⟩ (CTN.node CTN.nil ⟨98304, 98784, 24264110⟩ CTN.nil))) ⟨98304, 98787, 23475084⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨98304, 98806, 18781711⟩ CTN.nil) ⟨98304, 98816, 16522152⟩ CTN.nil) ⟨98304, 98821, 15446813⟩ (CTN.node (CTN.node CTN.nil ⟨98304, 98832, 13208758⟩ CTN.nil) ⟨98304, 98852, 9589082⟩ CTN.nil)) ⟨98304, 98880, 5494867⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨98304, 98912, 2204075⟩ CTN.nil) ⟨98304, 98940, 537295⟩ CTN.nil) ⟨98304, 98966, 1257⟩ (CTN.node CTN.nil ⟨98304, 98967, 74⟩ CTN.nil)))) ⟨98994, 101168, 468860⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨98994, 102000, 453669⟩ CTN.nil) ⟨99008, 101760, 1065102⟩ CTN.nil) ⟨99008, 102528, 1033382⟩ (CTN.node (CTN.node CTN.nil ⟨99056, 100064, 5420886⟩ CTN.nil) ⟨99061, 100148, 6029627⟩ CTN.nil)) ⟨99072, 102336, 6903573⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99072, 103872, 6502204⟩ CTN.nil) ⟨99072, 104576, 6328014⟩ CTN.nil) ⟨99072, 105600, 6084936⟩ (CTN.node CTN.nil ⟨99072, 106496, 5881758⟩ CTN.nil))) ⟨99076, 100450, 8019845⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99076, 101824, 7593446⟩ CTN.nil) ⟨99128, 101302, 16962014⟩ CTN.nil) ⟨99136, 101312, 18688523⟩ (CTN.node CTN.nil ⟨99155, 100658, 23754795⟩ CTN.nil)) ⟨99200, 100208, 37207097⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99200, 100640, 36568936⟩ CTN.nil) ⟨99200, 101216, 35739208⟩ CTN.nil) ⟨99200, 101632, 35154574⟩ (CTN.node CTN.nil ⟨99200, 102080, 34538288⟩ CTN.nil)))))) ⟨99200, 102720, 33681141⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99200, 103232, 33014516⟩ CTN.nil) ⟨99200, 103552, 32606248⟩ CTN.nil) ⟨99200, 104960, 30883143⟩ (CTN.node (CTN.node CTN.nil ⟨99200, 106240, 29414489⟩ CTN.nil) ⟨99200, 106496, 29131321⟩ CTN.nil)) ⟨99216, 100416, 42159602⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99218, 101424, 41155299⟩ CTN.nil) ⟨99218, 102256, 39825264⟩ CTN.nil) ⟨99222, 100309, 44413468⟩ (CTN.node CTN.nil ⟨99232, 100064, 48452755⟩ CTN.nil))) ⟨99232, 100480, 47651021⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99237, 100340, 49751082⟩ CTN.nil) ⟨99264, 100080, 60873351⟩ CTN.nil) ⟨99264, 101280, 58024299⟩ (CTN.node (CTN.node CTN.nil ⟨99264, 101696, 57075718⟩ CTN.nil) ⟨99264, 102464, 55374913⟩ CTN.nil)) ⟨99264, 103296, 53603320⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99312, 100512, 80822934⟩ CTN.nil) ⟨99316, 100403, 83077338⟩ CTN.nil) ⟨99316, 100819, 81707323⟩ (CTN.node CTN.nil ⟨99316, 101490, 79556547⟩ CTN.nil)))) ⟨99316, 102322, 76987137⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99316, 103664, 73057653⟩ CTN.nil) ⟨99328, 101504, 85097663⟩ CTN.nil) ⟨99328, 101760, 84240066⟩ (CTN.node (CTN.node CTN.nil ⟨99328, 102080, 83183222⟩ CTN.nil) ⟨99328, 102848, 80713683⟩ CTN.nil)) ⟨99328, 103680, 78140978⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99344, 100352, 97202257⟩ CTN.nil) ⟨99363, 100882, 105042296⟩ CTN.nil) ⟨99382, 100485, 117255365⟩ (CTN.node CTN.nil ⟨99392, 101824, 116623709⟩ CTN.nil))) ⟨99392, 102144, 115161513⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99392, 102592, 113152760⟩ CTN.nil) ⟨99392, 102912, 111744728⟩ CTN.nil) ⟨99392, 103424, 109537168⟩ (CTN.node (CTN.node CTN.nil ⟨99456, 101088, 159168281⟩ CTN.nil) ⟨99456, 101216, 158360372⟩ CTN.nil)) ⟨99456, 101632, 155769859⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99458, 100800, 162331072⟩ CTN.nil) ⟨99477, 100564, 176861276⟩ CTN.nil) ⟨99477, 100980, 173949356⟩ (CTN.node CTN.nil ⟨99488, 100496, 185114570⟩ CTN.nil))))) ⟨99488, 100928, 181948659⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99488, 101504, 177832088⟩ CTN.nil) ⟨99508, 100611, 198758717⟩ CTN.nil) ⟨99508, 101027, 195487797⟩ (CTN.node (CTN.node CTN.nil ⟨99508, 101714, 190232138⟩ CTN.nil) ⟨99508, 102546, 184101672⟩ CTN.nil)) ⟨99508, 103920, 174508846⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99520, 101696, 198950885⟩ CTN.nil) ⟨99528, 100688, 213148695⟩ CTN.nil) ⟨99552, 101184, 227340587⟩ (CTN.node CTN.nil ⟨99552, 101952, 220532053⟩ CTN.nil))) ⟨99584, 103104, 234616700⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99584, 103936, 227156804⟩ CTN.nil) ⟨99584, 105088, 217310842⟩ CTN.nil) ⟨99584, 106496, 205990782⟩ (CTN.node (CTN.node CTN.nil ⟨99632, 100640, 300633146⟩ CTN.nil) ⟨99638, 101141, 300061667⟩ CTN.nil)) ⟨99638, 101812, 292188160⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99638, 102644, 282781007⟩ CTN.nil) ⟨99648, 100480, 317384433⟩ CTN.nil) ⟨99648, 100848, 312752430⟩ (CTN.node CTN.nil ⟨99648, 101280, 307422268⟩ CTN.nil)))) ⟨99648, 101312, 307031980⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99648, 101824, 300870864⟩ CTN.nil) ⟨99648, 102144, 297098627⟩ CTN.nil) ⟨99648, 102400, 294123368⟩ (CTN.node (CTN.node CTN.nil ⟨99653, 101172, 313321039⟩ CTN.nil) ⟨99680, 101696, 331662148⟩ CTN.nil)) ⟨99712, 101472, 365519148⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99712, 101888, 359554950⟩ CTN.nil) ⟨99712, 102464, 351496418⟩ CTN.nil) ⟨99712, 103232, 341099989⟩ (CTN.node CTN.nil ⟨99712, 104064, 330267653⟩ CTN.nil))) ⟨99712, 105216, 315969717⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99732, 100819, 395673743⟩ CTN.nil) ⟨99744, 101376, 399317400⟩ CTN.nil) ⟨99744, 102144, 387380859⟩ (CTN.node CTN.nil ⟨99776, 100784, 443428349⟩ CTN.nil)) ⟨99776, 101216, 435866312⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99776, 101792, 426032834⟩ CTN.nil) ⟨99776, 102528, 413868282⟩ CTN.nil) ⟨99776, 102656, 411797282⟩ (CTN.node CTN.nil ⟨99776, 103808, 393729601⟩ CTN.nil))))))) ⟨99798, 102836, 431597944⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99826, 102000, 476766646⟩ CTN.nil) ⟨99840, 104704, 443359438⟩ CTN.nil) ⟨99840, 105344, 432630731⟩ (CTN.node (CTN.node CTN.nil ⟨99840, 106496, 414124897⟩ CTN.nil) ⟨99872, 101632, 537318409⟩ CTN.nil)) ⟨99880, 101936, 540396104⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨99893, 100980, 577473953⟩ CTN.nil) ⟨99904, 102080, 566159933⟩ CTN.nil) ⟨99920, 100928, 613152145⟩ (CTN.node CTN.nil ⟨99924, 101027, 615912991⟩ CTN.nil))) ⟨99960, 104308, 583459524⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨99968, 104000, 600057572⟩ CTN.nil) ⟨99968, 104832, 581140820⟩ CTN.nil) ⟨99968, 106368, 548136874⟩ (CTN.node (CTN.node CTN.nil ⟨99968, 106496, 545493685⟩ CTN.nil) ⟨99987, 101074, 698997029⟩ CTN.nil)) ⟨99987, 101490, 687546529⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100032, 102464, 721760793⟩ CTN.nil) ⟨100032, 102784, 712768220⟩ CTN.nil) ⟨100032, 103552, 691751310⟩ (CTN.node CTN.nil ⟨100050, 102256, 752672926⟩ CTN.nil)))) ⟨100064, 101504, 795673983⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100064, 102080, 777773714⟩ CTN.nil) ⟨100080, 101280, 826540041⟩ CTN.nil) ⟨100088, 104500, 739400704⟩ (CTN.node (CTN.node CTN.nil ⟨100096, 101696, 836749589⟩ CTN.nil) ⟨100096, 102112, 823126377⟩ CTN.nil)) ⟨100096, 102528, 809779573⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100096, 102848, 799696668⟩ CTN.nil) ⟨100096, 103296, 785843041⟩ CTN.nil) ⟨100096, 104128, 760902277⟩ (CTN.node CTN.nil ⟨100096, 104448, 751573889⟩ CTN.nil))) ⟨100096, 104960, 736944104⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100128, 101504, 891979818⟩ CTN.nil) ⟨100128, 101888, 878538549⟩ CTN.nil) ⟨100148, 101235, 933119696⟩ (CTN.node (CTN.node CTN.nil ⟨100148, 101651, 917858272⟩ CTN.nil) ⟨100148, 102322, 893894114⟩ CTN.nil)) ⟨100160, 102592, 902676954⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100160, 102912, 891444374⟩ CTN.nil) ⟨100160, 103680, 865191378⟩ CTN.nil) ⟨100195, 101714, 990490154⟩ (CTN.node CTN.nil ⟨100208, 101216, 1031903613⟩ CTN.nil))))) ⟨100224, 102400, 1010514521⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100224, 103424, 970885066⟩ CTN.nil) ⟨100224, 103488, 968473356⟩ CTN.nil) ⟨100224, 105088, 910544466⟩ (CTN.node (CTN.node CTN.nil ⟨100224, 106496, 863112789⟩ CTN.nil) ⟨100288, 102048, 1132472430⟩ CTN.nil)) ⟨100288, 102464, 1114098133⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100309, 101812, 1179989487⟩ CTN.nil) ⟨100320, 101952, 1192957427⟩ CTN.nil) ⟨100336, 104684, 1098356621⟩ (CTN.node CTN.nil ⟨100336, 106348, 1030891070⟩ CTN.nil))) ⟨100336, 106496, 1025144869⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100340, 101859, 1233289191⟩ CTN.nil) ⟨100340, 102546, 1200401497⟩ CTN.nil) ⟨100352, 101792, 1258439559⟩ (CTN.node (CTN.node CTN.nil ⟨100352, 102368, 1230208260⟩ CTN.nil) ⟨100352, 103232, 1189330625⟩ CTN.nil)) ⟨100352, 103872, 1160142263⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100352, 104384, 1137434544⟩ CTN.nil) ⟨100352, 104704, 1123524283⟩ CTN.nil) ⟨100352, 105856, 1075176801⟩ (CTN.node CTN.nil ⟨100352, 106112, 1064788573⟩ CTN.nil)))) ⟨100403, 101490, 1369873080⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100416, 102816, 1324044746⟩ CTN.nil) ⟨100416, 103680, 1280238729⟩ CTN.nil) ⟨100416, 103936, 1267608622⟩ (CTN.node (CTN.node CTN.nil ⟨100416, 105216, 1206745625⟩ CTN.nil) ⟨100450, 101824, 1442577755⟩ CTN.nil)) ⟨100470, 102644, 1435031260⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100480, 102144, 1483181829⟩ CTN.nil) ⟨100480, 102240, 1477589962⟩ CTN.nil) ⟨100480, 102656, 1453661183⟩ (CTN.node CTN.nil ⟨100480, 103232, 1421323803⟩ CTN.nil))) ⟨100480, 103808, 1389881531⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100480, 105472, 1303810317⟩ CTN.nil) ⟨100480, 105984, 1278676770⟩ CTN.nil) ⟨100480, 106496, 1254146509⟩ (CTN.node CTN.nil ⟨100512, 101888, 1562791894⟩ CTN.nil)) ⟨100512, 102112, 1549052433⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100512, 102144, 1547102011⟩ CTN.nil) ⟨100512, 102528, 1523934906⟩ CTN.nil) ⟨100544, 102720, 1576334175⟩ (CTN.node CTN.nil ⟨100544, 103296, 1541289642⟩ CTN.nil)))))) ⟨100544, 104064, 1496066047⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100564, 101651, 1686362061⟩ CTN.nil) ⟨100592, 105004, 1532860579⟩ CTN.nil) ⟨100592, 106496, 1448348361⟩ (CTN.node (CTN.node CTN.nil ⟨100608, 103872, 1633069640⟩ CTN.nil) ⟨100608, 106496, 1477240831⟩ CTN.nil)) ⟨100640, 102656, 1780222889⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100658, 102832, 1806559499⟩ CTN.nil) ⟨100658, 103664, 1748967538⟩ CTN.nil) ⟨100688, 103008, 1858923806⟩ (CTN.node CTN.nil ⟨100704, 102464, 1934679827⟩ CTN.nil))) ⟨100736, 105088, 1813173215⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100800, 102142, 2183712163⟩ CTN.nil) ⟨100800, 103484, 2072061744⟩ CTN.nil) ⟨100800, 103552, 2066596714⟩ (CTN.node (CTN.node CTN.nil ⟨100800, 104832, 1967010743⟩ CTN.nil) ⟨100800, 105600, 1910134415⟩ CTN.nil)) ⟨100800, 106168, 1869388740⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100800, 106496, 1846354451⟩ CTN.nil) ⟨100819, 102322, 2213842817⟩ CTN.nil) ⟨100864, 102880, 2273327253⟩ (CTN.node CTN.nil ⟨100864, 103040, 2259167630⟩ CTN.nil)))) ⟨100864, 103296, 2236740986⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100864, 103616, 2209097958⟩ CTN.nil) ⟨100864, 104384, 2144478419⟩ CTN.nil) ⟨100864, 105216, 2077120175⟩ (CTN.node (CTN.node CTN.nil ⟨100882, 103088, 2298265595⟩ CTN.nil) ⟨100882, 103920, 2225178484⟩ CTN.nil)) ⟨100896, 102656, 2371961056⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨100928, 102528, 2464244179⟩ CTN.nil) ⟨100928, 103360, 2385455058⟩ CTN.nil) ⟨100928, 104128, 2315505441⟩ (CTN.node CTN.nil ⟨100928, 104960, 2242598207⟩ CTN.nil))) ⟨100980, 103154, 2534862090⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨100980, 103986, 2454302038⟩ CTN.nil) ⟨100980, 105328, 2330992945⟩ CTN.nil) ⟨100980, 106496, 2229922484⟩ (CTN.node CTN.nil ⟨101027, 102546, 2719369395⟩ CTN.nil)) ⟨101056, 102816, 2767610962⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨101056, 103232, 2723042108⟩ CTN.nil) ⟨101120, 103296, 2886454083⟩ CTN.nil) ⟨101120, 106496, 2553301322⟩ (CTN.node CTN.nil ⟨101172, 104210, 2923150439⟩ CTN.nil))))) ⟨101172, 105584, 2773213133⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨101172, 106496, 2678982505⟩ CTN.nil) ⟨101184, 104704, 2899610072⟩ CTN.nil) ⟨101216, 103232, 3159276748⟩ (CTN.node (CTN.node CTN.nil ⟨101248, 103424, 3226207768⟩ CTN.nil) ⟨101248, 104000, 3154970160⟩ CTN.nil)) ⟨101248, 104768, 3063020264⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨101248, 105600, 2967159653⟩ CTN.nil) ⟨101248, 106496, 2868085299⟩ CTN.nil) ⟨101280, 103296, 3334493771⟩ (CTN.node CTN.nil ⟨101280, 103680, 3285118703⟩ CTN.nil))) ⟨101312, 104064, 3327380729⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨101376, 105728, 3295566036⟩ CTN.nil) ⟨101376, 106496, 3201075113⟩ CTN.nil) ⟨101440, 103616, 3767517279⟩ (CTN.node (CTN.node CTN.nil ⟨101472, 103232, 3924302267⟩ CTN.nil) ⟨101490, 103664, 3914900861⟩ CTN.nil)) ⟨101504, 104384, 3850045846⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨101504, 105856, 3639312697⟩ CTN.nil) ⟨101504, 106368, 3569411550⟩ CTN.nil) ⟨101504, 106496, 3552199377⟩ (CTN.node CTN.nil ⟨101632, 103808, 4345781435⟩ CTN.nil)))) ⟨101632, 104384, 4250176222⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨101632, 106496, 3921374948⟩ CTN.nil) ⟨101696, 104128, 4501766648⟩ CTN.nil) ⟨101696, 105216, 4317534691⟩ (CTN.node (CTN.node CTN.nil ⟨101714, 103920, 4598367711⟩ CTN.nil) ⟨101760, 104960, 4567600534⟩ CTN.nil)) ⟨101760, 106496, 4308506924⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨101812, 103986, 4920754322⟩ CTN.nil) ⟨101824, 104000, 4959771060⟩ CTN.nil) ⟨101824, 104572, 4851604973⟩ (CTN.node CTN.nil ⟨101824, 106496, 4508773694⟩ CTN.nil))) ⟨101888, 106496, 4713488648⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨101936, 106048, 4953154248⟩ CTN.nil) ⟨101952, 105216, 5167807049⟩ CTN.nil) ⟨102000, 106348, 5110885390⟩ (CTN.node CTN.nil ⟨102016, 104768, 5485293606⟩ CTN.nil)) ⟨102016, 106496, 5136201722⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨102080, 105600, 5539120202⟩ CTN.nil) ⟨102080, 106112, 5432471714⟩ CTN.nil) ⟨102142, 103484, 6250344236⟩ (CTN.node CTN.nil ⟨102144, 105472, 5797344305⟩ CTN.nil))))))))

noncomputable def tab2 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨102208, 104384, 6289821688⟩ CTN.nil) ⟨102256, 106496, 5976118346⟩ CTN.nil) ⟨102322, 105328, 6499637230⟩ (CTN.node (CTN.node CTN.nil ⟨102400, 106496, 6509369379⟩ CTN.nil) ⟨102528, 106496, 7001589868⟩ CTN.nil)) ⟨102546, 105584, 7320929975⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨102644, 106496, 7462322818⟩ CTN.nil) ⟨102656, 106496, 7510774532⟩ CTN.nil) ⟨102784, 106496, 8036735203⟩ (CTN.node CTN.nil ⟨102836, 106496, 8255153353⟩ CTN.nil))) ⟨102912, 106496, 8579272269⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨103008, 106496, 8996926832⟩ CTN.nil) ⟨103020, 106496, 9049776332⟩ CTN.nil) ⟨103340, 106496, 10510947160⟩ (CTN.node (CTN.node CTN.nil ⟨103424, 106496, 10910796006⟩ CTN.nil) ⟨103484, 106168, 11340201862⟩ CTN.nil)) ⟨103552, 106496, 11532825879⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨103664, 106496, 12089533415⟩ CTN.nil) ⟨103920, 106496, 13404539922⟩ CTN.nil) ⟨104192, 106496, 14864417181⟩ (CTN.node CTN.nil ⟨104572, 106496, 17006445976⟩ CTN.nil)))) ⟨104960, 106496, 19308445686⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨105472, 106496, 22506452254⟩ CTN.nil) ⟨105704, 106496, 24009450743⟩ CTN.nil) ⟨106048, 106496, 26292713610⟩ (CTN.node (CTN.node CTN.nil ⟨106088, 106496, 26562119161⟩ CTN.nil) ⟨106112, 106496, 26724131235⟩ CTN.nil)) ⟨106168, 106496, 27103215591⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 106624, 29210021225⟩ CTN.nil) ⟨106496, 106668, 29161623821⟩ CTN.nil) ⟨106496, 106752, 29069507059⟩ (CTN.node CTN.nil ⟨106496, 106880, 28929837604⟩ CTN.nil))) ⟨106496, 106992, 28808314968⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 107248, 28532938299⟩ CTN.nil) ⟨106496, 107264, 28515836841⟩ CTN.nil) ⟨106496, 107320, 28456082639⟩ (CTN.node (CTN.node CTN.nil ⟨106496, 107520, 28243949556⟩ CTN.nil) ⟨106496, 107648, 28109222210⟩ CTN.nil)) ⟨106496, 108032, 27709835999⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 108288, 27447518209⟩ CTN.nil) ⟨106496, 108416, 27317524415⟩ CTN.nil) ⟨106496, 108544, 27188299995⟩ (CTN.node CTN.nil ⟨106496, 108672, 27059839487⟩ CTN.nil))))) ⟨106496, 108800, 26932137472⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 108928, 26805188577⟩ CTN.nil) ⟨106496, 109032, 26702593465⟩ CTN.nil) ⟨106496, 109312, 26428807555⟩ (CTN.node (CTN.node CTN.nil ⟨106496, 109416, 26328010758⟩ CTN.nil) ⟨106496, 109568, 26181555955⟩ CTN.nil)) ⟨106496, 109824, 25937191605⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 109952, 25816079498⟩ CTN.nil) ⟨106496, 110592, 25221021330⟩ CTN.nil) ⟨106496, 110720, 25104076101⟩ (CTN.node CTN.nil ⟨106496, 111360, 24529420755⟩ CTN.nil))) ⟨106496, 111536, 24374283198⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 111616, 24304171983⟩ CTN.nil) ⟨106496, 112128, 23861384437⟩ CTN.nil) ⟨106496, 112360, 23664070407⟩ (CTN.node (CTN.node CTN.nil ⟨106496, 112744, 23341945754⟩ CTN.nil) ⟨106496, 112816, 23282159409⟩ CTN.nil)) ⟨106496, 112896, 23215954651⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨106496, 114176, 22188015873⟩ CTN.nil) ⟨106496, 114688, 21792819594⟩ CTN.nil) ⟨107320, 112816, 27894203484⟩ (CTN.node CTN.nil ⟨107648, 114688, 27861269372⟩ CTN.nil)))) ⟨111072, 114688, 45457472084⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨111536, 114688, 47509172966⟩ CTN.nil) ⟨111584, 114688, 47713980868⟩ CTN.nil) ⟨112816, 114688, 52419279185⟩ (CTN.node (CTN.node CTN.nil ⟨114688, 116224, 52971284238⟩ CTN.nil) ⟨114688, 117728, 47167361783⟩ CTN.nil)) ⟨114688, 118240, 44887967968⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨114688, 118312, 44557455791⟩ CTN.nil) ⟨114688, 122272, 24648331854⟩ CTN.nil) ⟨114688, 122496, 23530782628⟩ (CTN.node CTN.nil ⟨114688, 122880, 21644686635⟩ CTN.nil))) ⟨118272, 122880, 24202232921⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨118312, 122880, 24231042862⟩ CTN.nil) ⟨120832, 122880, 26035399071⟩ CTN.nil) ⟨121344, 122880, 26396659657⟩ (CTN.node CTN.nil ⟨121728, 122880, 26665741080⟩ CTN.nil)) ⟨121808, 122880, 26721577863⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨122272, 122880, 27043789676⟩ CTN.nil) ⟨122496, 122880, 27198271347⟩ CTN.nil) ⟨122576, 122880, 27253264256⟩ (CTN.node CTN.nil ⟨122880, 123808, 22147604092⟩ CTN.nil)))))) ⟨122880, 124956, 16151750382⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨122880, 126208, 10538428373⟩ CTN.nil) ⟨122880, 126608, 8977146292⟩ CTN.nil) ⟨122880, 126988, 7605001289⟩ (CTN.node (CTN.node CTN.nil ⟨122880, 127096, 7235190293⟩ CTN.nil) ⟨122880, 127224, 6808597004⟩ CTN.nil)) ⟨122880, 127616, 5581931705⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨122880, 127640, 5510767516⟩ CTN.nil) ⟨122880, 127820, 4991621461⟩ CTN.nil) ⟨122880, 127868, 4857540297⟩ (CTN.node CTN.nil ⟨122880, 127932, 4681627002⟩ CTN.nil))) ⟨122880, 128464, 3346442993⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨122880, 128652, 2929030315⟩ CTN.nil) ⟨122880, 129232, 1820297442⟩ CTN.nil) ⟨122880, 130428, 375476713⟩ (CTN.node (CTN.node CTN.nil ⟨122880, 130492, 329343855⟩ CTN.nil) ⟨122880, 130504, 321038381⟩ CTN.nil)) ⟨122880, 130552, 288901182⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨122880, 130680, 211650114⟩ CTN.nil) ⟨122880, 130720, 190016331⟩ CTN.nil) ⟨122880, 130944, 90715316⟩ (CTN.node CTN.nil ⟨122880, 131072, 50445805⟩ CTN.nil)))) ⟨123640, 128052, 4478212490⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨123640, 129780, 1062010192⟩ CTN.nil) ⟨123768, 128244, 3996467573⟩ CTN.nil) ⟨123768, 129972, 836962056⟩ (CTN.node (CTN.node CTN.nil ⟨123808, 125182, 15439293191⟩ CTN.nil) ⟨123808, 126556, 9426588321⟩ CTN.nil)) ⟨123808, 129304, 1774501676⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨124028, 131072, 61460790⟩ CTN.nil) ⟨124160, 130944, 107477872⟩ CTN.nil) ⟨124240, 128652, 3084021192⟩ (CTN.node CTN.nil ⟨124288, 131072, 63900346⟩ CTN.nil))) ⟨124412, 128824, 2730383297⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨124412, 130552, 327264114⟩ CTN.nil) ⟨124448, 129072, 2239434579⟩ CTN.nil) ⟨124448, 131072, 65385376⟩ (CTN.node (CTN.node CTN.nil ⟨124476, 128952, 2474944039⟩ CTN.nil) ⟨124476, 130680, 244920728⟩ CTN.nil)) ⟨124492, 128840, 2704807073⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨124492, 130504, 363897539⟩ CTN.nil) ⟨124956, 126298, 10778047436⟩ CTN.nil) ⟨124956, 127640, 5882181459⟩ (CTN.node CTN.nil ⟨125136, 129484, 1573424591⟩ CTN.nil))))) ⟨125136, 131072, 71593540⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨125182, 126556, 9783734389⟩ CTN.nil) ⟨125184, 131072, 72014168⟩ CTN.nil) ⟨125324, 128362, 3898017251⟩ (CTN.node (CTN.node CTN.nil ⟨125324, 129736, 1209581981⟩ CTN.nil) ⟨125324, 131072, 73230433⟩ CTN.nil)) ⟨125368, 129780, 1151523021⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨125456, 129176, 2124985266⟩ CTN.nil) ⟨125456, 130840, 172053248⟩ CTN.nil) ⟨125472, 129328, 1853619494⟩ (CTN.node CTN.nil ⟨125472, 130864, 160251988⟩ CTN.nil))) ⟨125496, 129972, 912272514⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨125904, 130316, 558882680⟩ CTN.nil) ⟨126140, 129210, 2110559248⟩ CTN.nil) ⟨126140, 130552, 365293037⟩ (CTN.node (CTN.node CTN.nil ⟨126156, 129162, 2201896510⟩ CTN.nil) ⟨126156, 130504, 402692822⟩ CTN.nil)) ⟨126204, 129306, 1940054470⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨126204, 130680, 276471509⟩ CTN.nil) ⟨126208, 128528, 3582671188⟩ CTN.nil) ⟨126208, 130848, 177878185⟩ (CTN.node CTN.nil ⟨126298, 127640, 6100155782⟩ CTN.nil)))) ⟨126324, 130736, 242929144⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨126516, 130992, 113656390⟩ CTN.nil) ⟨126556, 127930, 5242173173⟩ CTN.nil) ⟨126556, 129304, 1965609435⟩ (CTN.node (CTN.node CTN.nil ⟨126608, 130720, 257064201⟩ CTN.nil) ⟨126698, 129736, 1274066330⟩ CTN.nil)) ⟨126752, 130216, 681014163⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨126752, 131072, 84551849⟩ CTN.nil) ⟨126768, 131072, 84665722⟩ CTN.nil) ⟨126800, 131072, 84892501⟩ (CTN.node CTN.nil ⟨126988, 129194, 2196398730⟩ CTN.nil))) ⟨126988, 130026, 901534051⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨126988, 131072, 86198362⟩ CTN.nil) ⟨127008, 129704, 1334081843⟩ CTN.nil) ⟨127096, 129302, 2001369989⟩ (CTN.node CTN.nil ⟨127096, 130166, 743824252⟩ CTN.nil)) ⟨127096, 131072, 86927634⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨127120, 130840, 192858386⟩ CTN.nil) ⟨127176, 130182, 728588253⟩ CTN.nil) ⟨127176, 131072, 87457766⟩ (CTN.node CTN.nil ⟨127224, 129462, 1727293546⟩ CTN.nil))))))) ⟨127224, 130326, 582414218⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨127482, 130552, 389557869⟩ CTN.nil) ⟨127498, 129672, 1402616746⟩ CTN.nil) ⟨127498, 130504, 428503626⟩ (CTN.node (CTN.node CTN.nil ⟨127512, 131072, 89587803⟩ CTN.nil) ⟨127578, 129816, 1195292976⟩ CTN.nil)) ⟨127578, 130680, 296846845⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨127616, 130144, 782093825⟩ CTN.nil) ⟨127616, 131008, 115705527⟩ CTN.nil) ⟨127640, 128982, 2666109124⟩ (CTN.node CTN.nil ⟨127640, 130324, 593401922⟩ CTN.nil))) ⟨127820, 130026, 926645378⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨127912, 130224, 701489509⟩ CTN.nil) ⟨127912, 131072, 91911106⟩ CTN.nil) ⟨127930, 129304, 2043263807⟩ (CTN.node (CTN.node CTN.nil ⟨127960, 129495, 1706402844⟩ CTN.nil) ⟨127960, 130166, 765926575⟩ CTN.nil)) ⟨128052, 131072, 92667319⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨128072, 130278, 648393764⟩ CTN.nil) ⟨128072, 131072, 92772878⟩ CTN.nil) ⟨128088, 129639, 1477101510⟩ (CTN.node CTN.nil ⟨128088, 130326, 600419120⟩ CTN.nil)))) ⟨128168, 130096, 851368949⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨128168, 130864, 189743459⟩ CTN.nil) ⟨128244, 131072, 93654831⟩ CTN.nil) ⟨128330, 130504, 441590588⟩ (CTN.node (CTN.node CTN.nil ⟨128362, 129881, 1130769507⟩ CTN.nil) ⟨128362, 130568, 389701776⟩ CTN.nil)) ⟨128362, 131072, 94232767⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨128438, 129973, 1010402635⟩ CTN.nil) ⟨128438, 130644, 332790175⟩ CTN.nil) ⟨128438, 131072, 94593148⟩ (CTN.node CTN.nil ⟨128442, 130680, 307070972⟩ CTN.nil))) ⟨128480, 130176, 766337070⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨128480, 131008, 121068939⟩ CTN.nil) ⟨128518, 130692, 299498690⟩ CTN.nil) ⟨128518, 131072, 94962366⟩ (CTN.node (CTN.node CTN.nil ⟨128528, 130848, 201488252⟩ CTN.nil) ⟨128570, 131072, 95196746⟩ CTN.nil)) ⟨128598, 130149, 799446031⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨128598, 130836, 208871425⟩ CTN.nil) ⟨128631, 130166, 780743583⟩ CTN.nil) ⟨128775, 129894, 1124529355⟩ (CTN.node CTN.nil ⟨128775, 130326, 612571119⟩ CTN.nil))))) ⟨128824, 130359, 580734408⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨128824, 131030, 113330538⟩ CTN.nil) ⟨128840, 130343, 596689196⟩ CTN.nil) ⟨128840, 131014, 120273884⟩ (CTN.node (CTN.node CTN.nil ⟨128904, 131072, 96595161⟩ CTN.nil) ⟨128936, 130864, 195348198⟩ CTN.nil)) ⟨128952, 130503, 450636249⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨128952, 131072, 96780705⟩ CTN.nil) ⟨128982, 130324, 617852909⟩ CTN.nil) ⟨129049, 130568, 397767483⟩ (CTN.node CTN.nil ⟨129064, 131072, 97198350⟩ CTN.nil))) ⟨129072, 130804, 231274325⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨129072, 131072, 97227358⟩ CTN.nil) ⟨129109, 130644, 339622409⟩ CTN.nil) ⟨129176, 131036, 112262503⟩ (CTN.node (CTN.node CTN.nil ⟨129194, 131072, 97656065⟩ CTN.nil) ⟨129207, 130326, 619180477⟩ CTN.nil)) ⟨129280, 130976, 139483549⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨129285, 130836, 213507757⟩ CTN.nil) ⟨129302, 130405, 543206001⟩ CTN.nil) ⟨129302, 130837, 213021617⟩ (CTN.node CTN.nil ⟨129302, 131072, 98014026⟩ CTN.nil)))) ⟨129304, 130678, 316496761⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨129312, 130576, 393982325⟩ CTN.nil) ⟨129312, 131008, 124932872⟩ CTN.nil) ⟨129328, 130676, 318122421⟩ (CTN.node (CTN.node CTN.nil ⟨129328, 131072, 98097161⟩ CTN.nil) ⟨129344, 131040, 111187747⟩ CTN.nil)) ⟨129350, 131072, 98166581⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨129462, 130581, 391358277⟩ CTN.nil) ⟨129462, 131013, 123259018⟩ CTN.nil) ⟨129495, 131030, 115946918⟩ (CTN.node CTN.nil ⟨129511, 130598, 378302463⟩ CTN.nil))) ⟨129511, 131014, 122984215⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨129639, 130758, 263961504⟩ CTN.nil) ⟨129639, 131072, 98999214⟩ CTN.nil) ⟨129652, 130808, 232336759⟩ (CTN.node CTN.nil ⟨129652, 131072, 99033182⟩ CTN.nil)) ⟨129734, 130837, 215290995⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨129736, 131072, 99245381⟩ CTN.nil) ⟨129744, 130592, 384932355⟩ CTN.nil) ⟨129744, 131008, 126404598⟩ (CTN.node CTN.nil ⟨129780, 131072, 99351484⟩ CTN.nil)))))) ⟨129894, 131013, 124581014⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨129908, 131072, 99640327⟩ CTN.nil) ⟨129927, 131014, 124219446⟩ CTN.nil) ⟨129972, 131072, 99773646⟩ (CTN.node (CTN.node CTN.nil ⟨129973, 131072, 99775670⟩ CTN.nil) ⟨130071, 131072, 99965234⟩ CTN.nil)) ⟨130096, 131072, 100010796⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨130144, 131072, 100095080⟩ CTN.nil) ⟨130149, 131072, 100103618⟩ CTN.nil) ⟨130160, 131008, 127464677⟩ (CTN.node CTN.nil ⟨130166, 131072, 100132305⟩ CTN.nil))) ⟨130176, 131024, 120346737⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨130176, 131072, 100148933⟩ CTN.nil) ⟨130182, 131072, 100158823⟩ CTN.nil) ⟨130228, 131072, 100232453⟩ (CTN.node (CTN.node CTN.nil ⟨130232, 131072, 100238673⟩ CTN.nil) ⟨130326, 131072, 100376396⟩ CTN.nil)) ⟨130405, 131072, 100479598⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨130576, 131072, 100663638⟩ CTN.nil) ⟨130592, 131072, 100678099⟩ CTN.nil) ⟨131072, 131076, 99276454⟩ (CTN.node CTN.nil ⟨131072, 131110, 86076446⟩ CTN.nil)))) ⟨131072, 131122, 81643464⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131072, 131148, 72442612⟩ CTN.nil) ⟨131072, 131190, 58746422⟩ CTN.nil) ⟨131072, 131232, 46489813⟩ (CTN.node (CTN.node CTN.nil ⟨131072, 131255, 40387174⟩ CTN.nil) ⟨131072, 131256, 40131616⟩ CTN.nil)) ⟨131072, 131268, 37128430⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131072, 131269, 36883456⟩ CTN.nil) ⟨131072, 131315, 26494034⟩ CTN.nil) ⟨131072, 131324, 24662527⟩ (CTN.node CTN.nil ⟨131072, 131346, 20462462⟩ CTN.nil))) ⟨131072, 131376, 15368120⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131072, 131384, 14132891⟩ CTN.nil) ⟨131072, 131388, 13534729⟩ CTN.nil) ⟨131072, 131392, 12949532⟩ (CTN.node CTN.nil ⟨131072, 131400, 11818026⟩ CTN.nil)) ⟨131072, 131408, 10738357⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131072, 131424, 8734460⟩ CTN.nil) ⟨131072, 131440, 6937709⟩ CTN.nil) ⟨131072, 131444, 6520871⟩ (CTN.node CTN.nil ⟨131072, 131445, 6418683⟩ CTN.nil))))) ⟨131072, 131448, 6116970⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131072, 131508, 1609284⟩ CTN.nil) ⟨131072, 131512, 1412060⟩ CTN.nil) ⟨131072, 131523, 936196⟩ (CTN.node (CTN.node CTN.nil ⟨131072, 131524, 897771⟩ CTN.nil) ⟨131576, 135318, 8137⟩ CTN.nil)) ⟨131576, 136118, 7946⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131576, 136150, 7939⟩ CTN.nil) ⟨131576, 137460, 7640⟩ CTN.nil) ⟨131576, 139060, 7293⟩ (CTN.node CTN.nil ⟨131584, 132992, 62700⟩ CTN.nil))) ⟨131584, 133408, 61919⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131584, 133824, 61150⟩ CTN.nil) ⟨131584, 135168, 58747⟩ CTN.nil) ⟨131584, 135936, 57427⟩ (CTN.node (CTN.node CTN.nil ⟨131584, 136768, 56038⟩ CTN.nil) ⟨131584, 138752, 52892⟩ CTN.nil)) ⟨131584, 139264, 52116⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131616, 133008, 771550⟩ CTN.nil) ⟨131616, 133392, 762677⟩ CTN.nil) ⟨131616, 133824, 752846⟩ (CTN.node CTN.nil ⟨131616, 134400, 739985⟩ CTN.nil)))) ⟨131616, 135168, 723260⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131624, 135344, 999791⟩ CTN.nil) ⟨131624, 137008, 951961⟩ CTN.nil) ⟨131640, 134614, 1735796⟩ (CTN.node (CTN.node CTN.nil ⟨131648, 133576, 2231703⟩ CTN.nil) ⟨131648, 134344, 2180955⟩ CTN.nil)) ⟨131648, 135504, 2107010⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131652, 133858, 2449683⟩ CTN.nil) ⟨131666, 133008, 3460643⟩ CTN.nil) ⟨131670, 133141, 3744145⟩ (CTN.node CTN.nil ⟨131670, 133525, 3701129⟩ CTN.nil))) ⟨131685, 133188, 4961913⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131692, 137832, 4873526⟩ CTN.nil) ⟨131700, 133251, 6346024⟩ CTN.nil) ⟨131700, 133938, 6216430⟩ (CTN.node CTN.nil ⟨131700, 134802, 6058111⟩ CTN.nil)) ⟨131700, 136176, 5816583⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131701, 133236, 6447983⟩ CTN.nil) ⟨131704, 136278, 6165394⟩ CTN.nil) ⟨131704, 137652, 5922200⟩ (CTN.node CTN.nil ⟨131704, 139124, 5674822⟩ CTN.nil))))))))

noncomputable def tab3 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131712, 134496, 7307488⟩ CTN.nil) ⟨131712, 135264, 7142447⟩ CTN.nil) ⟨131712, 136128, 6962309⟩ (CTN.node (CTN.node CTN.nil ⟨131712, 137280, 6730872⟩ CTN.nil) ⟨131712, 138816, 6437051⟩ CTN.nil)) ⟨131712, 139264, 6354389⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131744, 133568, 11322883⟩ CTN.nil) ⟨131747, 132850, 11976262⟩ CTN.nil) ⟨131760, 133376, 13598607⟩ (CTN.node CTN.nil ⟨131760, 133536, 13533351⟩ CTN.nil))) ⟨131760, 133792, 13429754⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131764, 134035, 13904145⟩ CTN.nil) ⟨131764, 134706, 13628347⟩ CTN.nil) ⟨131764, 135474, 13321024⟩ (CTN.node (CTN.node CTN.nil ⟨131767, 133622, 14519572⟩ CTN.nil) ⟨131776, 136128, 14746045⟩ CTN.nil)) ⟨131776, 136960, 14389955⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131797, 133316, 19497310⟩ CTN.nil) ⟨131808, 133056, 21615453⟩ CTN.nil) ⟨131808, 133472, 21346411⟩ (CTN.node CTN.nil ⟨131808, 133584, 21274693⟩ CTN.nil)))) ⟨131808, 133888, 21081544⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131808, 134016, 21000874⟩ CTN.nil) ⟨131808, 134336, 20800883⟩ CTN.nil) ⟨131808, 134592, 20642603⟩ (CTN.node (CTN.node CTN.nil ⟨131824, 133856, 24055442⟩ CTN.nil) ⟨131828, 134770, 24155585⟩ CTN.nil)) ⟨131830, 133317, 25624583⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131830, 133701, 25330574⟩ CTN.nil) ⟨131832, 139264, 21843389⟩ CTN.nil) ⟨131836, 133184, 26936529⟩ (CTN.node CTN.nil ⟨131840, 133072, 27851942⟩ CTN.nil))) ⟨131840, 133248, 27704630⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131840, 133456, 27531788⟩ CTN.nil) ⟨131840, 133536, 27465670⟩ CTN.nil) ⟨131840, 133664, 27360293⟩ (CTN.node (CTN.node CTN.nil ⟨131840, 134080, 27021293⟩ CTN.nil) ⟨131840, 134656, 26560533⟩ CTN.nil)) ⟨131840, 135488, 25912200⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131840, 136320, 25283541⟩ CTN.nil) ⟨131840, 137472, 24444246⟩ CTN.nil) ⟨131840, 139136, 23292494⟩ (CTN.node CTN.nil ⟨131840, 139264, 23206737⟩ CTN.nil))))) ⟨131846, 134020, 28294285⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131846, 134852, 27600386⟩ CTN.nil) ⟨131856, 133472, 30899197⟩ CTN.nil) ⟨131856, 133888, 30515799⟩ (CTN.node (CTN.node CTN.nil ⟨131861, 134132, 31368948⟩ CTN.nil) ⟨131872, 133568, 34377065⟩ CTN.nil)) ⟨131872, 134400, 33531164⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131877, 133428, 35681741⟩ CTN.nil) ⟨131892, 135602, 36810321⟩ CTN.nil) ⟨131894, 134964, 37983679⟩ (CTN.node CTN.nil ⟨131904, 133600, 42058702⟩ CTN.nil))) ⟨131904, 133680, 41957807⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131904, 134112, 41418170⟩ CTN.nil) ⟨131904, 134144, 41378544⟩ CTN.nil) ⟨131904, 134688, 40712087⟩ (CTN.node (CTN.node CTN.nil ⟨131904, 135456, 39793895⟩ CTN.nil) ⟨131904, 135488, 39756202⟩ CTN.nil)) ⟨131904, 136320, 38791672⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131904, 136832, 38212641⟩ CTN.nil) ⟨131904, 137472, 37503970⟩ CTN.nil) ⟨131911, 133782, 43611953⟩ (CTN.node CTN.nil ⟨131925, 133780, 47291511⟩ CTN.nil)))) ⟨131925, 134196, 46706065⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131936, 134464, 49266914⟩ CTN.nil) ⟨131940, 133027, 52574198⟩ CTN.nil) ⟨131940, 133043, 52548834⟩ (CTN.node (CTN.node CTN.nil ⟨131942, 133461, 52457332⟩ CTN.nil) ⟨131942, 134148, 51387763⟩ CTN.nil)) ⟨131952, 133728, 54890345⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131955, 133074, 56868524⟩ CTN.nil) ⟨131956, 134243, 55194746⟩ CTN.nil) ⟨131956, 134930, 54075873⟩ (CTN.node CTN.nil ⟨131956, 135698, 52858454⟩ CTN.nil))) ⟨131960, 133116, 58289907⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨131964, 133696, 58469708⟩ CTN.nil) ⟨131968, 134976, 57431681⟩ CTN.nil) ⟨131968, 135552, 56458842⟩ (CTN.node CTN.nil ⟨131968, 136320, 55193558⟩ CTN.nil)) ⟨131968, 136448, 54986139⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨131968, 136896, 54267805⟩ CTN.nil) ⟨131968, 137152, 53862596⟩ CTN.nil) ⟨131968, 137984, 52571534⟩ (CTN.node CTN.nil ⟨131986, 133521, 65565082⟩ CTN.nil)))))) ⟨131986, 134192, 64259582⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132000, 133392, 70350547⟩ CTN.nil) ⟨132000, 133408, 70316700⟩ CTN.nil) ⟨132000, 133824, 69443791⟩ (CTN.node (CTN.node CTN.nil ⟨132020, 134994, 73480647⟩ CTN.nil) ⟨132022, 133877, 76652029⟩ CTN.nil)) ⟨132022, 134293, 75703801⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132022, 134964, 74205032⟩ CTN.nil) ⟨132024, 134720, 75412316⟩ CTN.nil) ⟨132034, 134208, 80002871⟩ (CTN.node CTN.nil ⟨132048, 133440, 86909521⟩ CTN.nil))) ⟨132048, 133824, 85913262⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132052, 133426, 88415465⟩ CTN.nil) ⟨132052, 134800, 84854825⟩ CTN.nil) ⟨132054, 133525, 88889857⟩ (CTN.node (CTN.node CTN.nil ⟨132054, 135156, 84663743⟩ CTN.nil) ⟨132064, 133924, 91519521⟩ CTN.nil)) ⟨132080, 137964, 86610382⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132080, 139264, 83412540⟩ CTN.nil) ⟨132084, 135826, 93670631⟩ CTN.nil) ⟨132086, 133941, 99849381⟩ (CTN.node CTN.nil ⟨132086, 134357, 98614778⟩ CTN.nil)))) ⟨132086, 135028, 96663346⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132086, 135796, 94488714⟩ CTN.nil) ⟨132096, 133872, 103993583⟩ CTN.nil) ⟨132096, 134304, 102657994⟩ (CTN.node (CTN.node CTN.nil ⟨132096, 134560, 101876651⟩ CTN.nil) ⟨132096, 134880, 100910403⟩ CTN.nil)) ⟨132096, 135328, 99576831⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132096, 136160, 97158154⟩ CTN.nil) ⟨132096, 137024, 94723717⟩ CTN.nil) ⟨132096, 137664, 92969468⟩ (CTN.node CTN.nil ⟨132096, 138560, 90581218⟩ CTN.nil))) ⟨132096, 139200, 88922174⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132096, 139264, 88758367⟩ CTN.nil) ⟨132101, 133972, 105673948⟩ CTN.nil) ⟨132101, 134388, 104367628⟩ (CTN.node (CTN.node CTN.nil ⟨132128, 135360, 112027258⟩ CTN.nil) ⟨132160, 133984, 130565134⟩ CTN.nil)) ⟨132160, 134400, 128951258⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132160, 134624, 128092580⟩ CTN.nil) ⟨132160, 134976, 126757627⟩ CTN.nil) ⟨132160, 135808, 123670788⟩ (CTN.node CTN.nil ⟨132160, 137088, 119103089⟩ CTN.nil))))) ⟨132160, 138624, 113896799⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132160, 139264, 111811675⟩ CTN.nil) ⟨132168, 136516, 124442896⟩ CTN.nil) ⟨132176, 133792, 138578043⟩ (CTN.node (CTN.node CTN.nil ⟨132179, 133714, 140288931⟩ CTN.nil) ⟨132182, 134053, 140250052⟩ CTN.nil)) ⟨132182, 134469, 138517354⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132182, 135156, 135714107⟩ CTN.nil) ⟨132192, 133584, 146948461⟩ CTN.nil) ⟨132192, 133808, 145963952⟩ (CTN.node CTN.nil ⟨132192, 133968, 145265779⟩ CTN.nil))) ⟨132192, 134224, 144157367⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132192, 134400, 143401466⟩ CTN.nil) ⟨132192, 134656, 142310800⟩ CTN.nil) ⟨132192, 134976, 140962017⟩ (CTN.node (CTN.node CTN.nil ⟨132192, 135744, 137789588⟩ CTN.nil) ⟨132194, 135232, 140800533⟩ CTN.nil)) ⟨132195, 133698, 147870258⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132210, 134448, 151651444⟩ CTN.nil) ⟨132214, 133701, 157034906⟩ CTN.nil) ⟨132224, 133456, 163173439⟩ (CTN.node CTN.nil ⟨132224, 133472, 163094971⟩ CTN.nil)))) ⟨132224, 133888, 161071284⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132224, 134304, 159078906⟩ CTN.nil) ⟨132224, 134688, 157267075⟩ CTN.nil) ⟨132224, 134720, 157117257⟩ (CTN.node (CTN.node CTN.nil ⟨132224, 135552, 153283889⟩ CTN.nil) ⟨132224, 135808, 152127981⟩ CTN.nil)) ⟨132224, 136288, 149989887⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132224, 136384, 149566787⟩ CTN.nil) ⟨132224, 137152, 146235168⟩ CTN.nil) ⟨132224, 137216, 145961743⟩ (CTN.node CTN.nil ⟨132224, 138880, 139071867⟩ CTN.nil))) ⟨132224, 139264, 137540034⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132240, 134016, 168446782⟩ CTN.nil) ⟨132246, 133733, 172954793⟩ CTN.nil) ⟨132246, 134533, 168865225⟩ (CTN.node CTN.nil ⟨132246, 135220, 165449427⟩ CTN.nil)) ⟨132246, 135988, 161732558⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132256, 133488, 179453920⟩ CTN.nil) ⟨132256, 133664, 178507735⟩ CTN.nil) ⟨132256, 133872, 177397547⟩ (CTN.node CTN.nil ⟨132256, 134080, 176295982⟩ CTN.nil))))))) ⟨132256, 134288, 175202959⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132256, 134720, 172959785⟩ CTN.nil) ⟨132256, 135488, 169059892⟩ CTN.nil) ⟨132260, 134952, 173790077⟩ (CTN.node (CTN.node CTN.nil ⟨132272, 133504, 187880050⟩ CTN.nil) ⟨132272, 133888, 185727380⟩ CTN.nil)) ⟨132274, 135984, 175507300⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132274, 136816, 171264679⟩ CTN.nil) ⟨132280, 136692, 174847611⟩ CTN.nil) ⟨132288, 133904, 194245360⟩ (CTN.node CTN.nil ⟨132288, 134320, 191842920⟩ CTN.nil))) ⟨132288, 134496, 190837697⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132288, 134752, 189387284⟩ CTN.nil) ⟨132288, 135296, 186350654⟩ CTN.nil) ⟨132288, 135520, 185117990⟩ (CTN.node (CTN.node CTN.nil ⟨132288, 135872, 183201478⟩ CTN.nil) ⟨132288, 136352, 180627868⟩ CTN.nil)) ⟨132288, 136640, 179105392⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132288, 137216, 176108286⟩ CTN.nil) ⟨132288, 137472, 174796383⟩ CTN.nil) ⟨132288, 139264, 165947180⟩ (CTN.node CTN.nil ⟨132320, 135552, 201892860⟩ CTN.nil)))) ⟨132336, 134112, 219870410⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132336, 139264, 189012513⟩ CTN.nil) ⟨132341, 133812, 224776864⟩ CTN.nil) ⟨132341, 134196, 222207363⟩ (CTN.node (CTN.node CTN.nil ⟨132352, 135360, 220842983⟩ CTN.nil) ⟨132352, 135936, 217112671⟩ CTN.nil)) ⟨132352, 137280, 208710389⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132352, 138816, 199599621⟩ CTN.nil) ⟨132352, 139264, 197036445⟩ CTN.nil) ⟨132356, 134530, 228695035⟩ (CTN.node CTN.nil ⟨132372, 134578, 237813514⟩ CTN.nil))) ⟨132384, 134160, 248101361⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132384, 134592, 244921823⟩ CTN.nil) ⟨132384, 135168, 240761295⟩ CTN.nil) ⟨132387, 133938, 251610074⟩ (CTN.node (CTN.node CTN.nil ⟨132400, 136256, 242449039⟩ CTN.nil) ⟨132402, 136944, 238752305⟩ CTN.nil)) ⟨132408, 136150, 247944775⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132408, 136884, 242653998⟩ CTN.nil) ⟨132416, 133824, 270818384⟩ CTN.nil) ⟨132416, 134240, 267466885⟩ (CTN.node CTN.nil ⟨132416, 134344, 266637129⟩ CTN.nil))))) ⟨132416, 134656, 264167102⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132416, 136000, 253848462⟩ CTN.nil) ⟨132416, 136768, 248178122⟩ CTN.nil) ⟨132416, 137344, 244029038⟩ (CTN.node (CTN.node CTN.nil ⟨132416, 137600, 242212861⟩ CTN.nil) ⟨132416, 138880, 233381371⟩ CTN.nil)) ⟨132416, 139264, 230810749⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132432, 133824, 281218144⟩ CTN.nil) ⟨132432, 137824, 249878334⟩ CTN.nil) ⟨132435, 134706, 275823781⟩ (CTN.node CTN.nil ⟨132438, 134293, 281194094⟩ CTN.nil))) ⟨132464, 134670, 295053942⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132464, 135534, 287579967⟩ CTN.nil) ⟨132464, 136876, 276434406⟩ CTN.nil) ⟨132464, 138604, 262866711⟩ (CTN.node (CTN.node CTN.nil ⟨132464, 139264, 257905061⟩ CTN.nil) ⟨132468, 139264, 260231189⟩ CTN.nil)) ⟨132480, 133872, 313149472⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132480, 134256, 309571356⟩ CTN.nil) ⟨132480, 134688, 305606882⟩ CTN.nil) ⟨132480, 135264, 300419169⟩ (CTN.node CTN.nil ⟨132480, 136032, 293672343⟩ CTN.nil)))) ⟨132480, 136896, 286307105⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132480, 136960, 285770772⟩ CTN.nil) ⟨132480, 137408, 282051412⟩ CTN.nil) ⟨132480, 138048, 276842435⟩ (CTN.node (CTN.node CTN.nil ⟨132480, 138112, 276328179⟩ CTN.nil) ⟨132480, 138496, 273267608⟩ CTN.nil)) ⟨132480, 138944, 269750329⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132480, 139264, 267272605⟩ CTN.nil) ⟨132484, 134690, 308296324⟩ CTN.nil) ⟨132484, 135522, 300772810⟩ (CTN.node CTN.nil ⟨132484, 136896, 288843910⟩ CTN.nil))) ⟨132498, 136240, 303605877⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132498, 137072, 296280329⟩ CTN.nil) ⟨132502, 134357, 323829602⟩ CTN.nil) ⟨132504, 136224, 307711834⟩ (CTN.node CTN.nil ⟨132517, 134004, 337945747⟩ CTN.nil)) ⟨132517, 134388, 334088103⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132528, 134304, 342797936⟩ CTN.nil) ⟨132528, 134840, 337363557⟩ CTN.nil) ⟨132532, 135474, 333860136⟩ (CTN.node CTN.nil ⟨132536, 134848, 342972146⟩ CTN.nil)))))) ⟨132536, 136000, 331464707⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132544, 134856, 348625893⟩ CTN.nil) ⟨132544, 135552, 341499699⟩ CTN.nil) ⟨132544, 136892, 328285369⟩ (CTN.node (CTN.node CTN.nil ⟨132544, 138556, 312753432⟩ CTN.nil) ⟨132544, 139264, 306424115⟩ CTN.nil)) ⟨132552, 136016, 342437812⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132564, 134802, 363757668⟩ CTN.nil) ⟨132576, 133968, 382039186⟩ CTN.nil) ⟨132576, 134400, 377136168⟩ (CTN.node CTN.nil ⟨132576, 134784, 372843836⟩ CTN.nil))) ⟨132576, 135360, 366519255⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132576, 136128, 358293741⟩ CTN.nil) ⟨132596, 134451, 391771257⟩ CTN.nil) ⟨132596, 134867, 386945483⟩ (CTN.node (CTN.node CTN.nil ⟨132596, 135538, 379317208⟩ CTN.nil) ⟨132596, 136306, 370815567⟩ CTN.nil)) ⟨132596, 137138, 361872643⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132596, 138480, 348008765⟩ CTN.nil) ⟨132598, 134469, 393097595⟩ CTN.nil) ⟨132608, 134224, 403769928⟩ (CTN.node CTN.nil ⟨132608, 136000, 383028239⟩ CTN.nil)))) ⟨132608, 136960, 372370826⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132608, 137792, 363432875⟩ CTN.nil) ⟨132608, 138624, 354761639⟩ CTN.nil) ⟨132608, 139264, 348266970⟩ (CTN.node (CTN.node CTN.nil ⟨132624, 134240, 416186400⟩ CTN.nil) ⟨132624, 134400, 414202128⟩ CTN.nil)) ⟨132624, 134656, 411051840⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132626, 137200, 382774402⟩ CTN.nil) ⟨132629, 134148, 421324177⟩ CTN.nil) ⟨132630, 134117, 422516358⟩ (CTN.node CTN.nil ⟨132640, 133872, 433741905⟩ CTN.nil))) ⟨132640, 133888, 433533978⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132640, 134304, 428171360⟩ CTN.nil) ⟨132640, 134720, 422891453⟩ CTN.nil) ⟨132643, 134930, 422630291⟩ (CTN.node CTN.nil ⟨132656, 133888, 446671253⟩ CTN.nil)) ⟨132657, 134192, 443445344⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132660, 139264, 384246896⟩ CTN.nil) ⟨132662, 134533, 443023378⟩ CTN.nil) ⟨132672, 134288, 454532817⟩ (CTN.node CTN.nil ⟨132672, 134448, 452366496⟩ CTN.nil))))) ⟨132672, 134880, 446581595⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132672, 134912, 446156775⟩ CTN.nil) ⟨132672, 135456, 439011560⟩ CTN.nil) ⟨132672, 135488, 438595726⟩ (CTN.node (CTN.node CTN.nil ⟨132672, 136064, 431194266⟩ CTN.nil) ⟨132672, 136320, 427954896⟩ CTN.nil)) ⟨132672, 137728, 410672362⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132672, 138240, 404604837⟩ CTN.nil) ⟨132672, 139264, 392802446⟩ CTN.nil) ⟨132678, 134852, 451861637⟩ (CTN.node CTN.nil ⟨132688, 134720, 461912681⟩ CTN.nil))) ⟨132693, 134548, 468471951⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132693, 134964, 462705543⟩ CTN.nil) ⟨132704, 133936, 486565677⟩ CTN.nil) ⟨132704, 134320, 481008723⟩ (CTN.node (CTN.node CTN.nil ⟨132704, 134400, 479861032⟩ CTN.nil) ⟨132720, 134336, 494519394⟩ CTN.nil)) ⟨132720, 134752, 488422779⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132720, 137196, 454442395⟩ CTN.nil) ⟨132720, 138924, 432188580⟩ CTN.nil) ⟨132720, 139264, 427971621⟩ (CTN.node CTN.nil ⟨132724, 135698, 478233063⟩ CTN.nil)))) ⟨132724, 138608, 439211072⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132724, 139264, 430970783⟩ CTN.nil) ⟨132725, 134196, 500944490⟩ CTN.nil) ⟨132736, 134976, 498850742⟩ (CTN.node (CTN.node CTN.nil ⟨132736, 136128, 482128877⟩ CTN.nil) ⟨132736, 136320, 479410445⟩ CTN.nil)) ⟨132736, 137920, 457486189⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132736, 138752, 446580948⟩ CTN.nil) ⟨132757, 135028, 516286241⟩ CTN.nil) ⟨132768, 134544, 533585719⟩ (CTN.node CTN.nil ⟨132768, 134976, 526767038⟩ CTN.nil))) ⟨132768, 135552, 517844095⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132768, 136320, 506238838⟩ CTN.nil) ⟨132774, 135812, 519067487⟩ CTN.nil) ⟨132788, 134659, 549764297⟩ (CTN.node CTN.nil ⟨132788, 135075, 543002832⟩ CTN.nil)) ⟨132788, 135762, 532062769⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132788, 136530, 520157153⟩ CTN.nil) ⟨132788, 137362, 507632960⟩ CTN.nil) ⟨132788, 138736, 487764359⟩ (CTN.node CTN.nil ⟨132790, 136500, 522336592⟩ CTN.nil))))))))

noncomputable def tab4 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132800, 137152, 520928691⟩ CTN.nil) ⟨132800, 137856, 510338701⟩ CTN.nil) ⟨132800, 137984, 508442271⟩ (CTN.node (CTN.node CTN.nil ⟨132808, 135504, 553990503⟩ CTN.nil) ⟨132816, 134592, 576626566⟩ CTN.nil)) ⟨132832, 134240, 597862628⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132832, 134656, 590486698⟩ CTN.nil) ⟨132850, 135056, 600358774⟩ CTN.nil) ⟨132850, 135920, 585194190⟩ (CTN.node CTN.nil ⟨132854, 135125, 602900845⟩ CTN.nil))) ⟨132854, 135796, 591037755⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132864, 134256, 628438861⟩ CTN.nil) ⟨132864, 135328, 608703368⟩ CTN.nil) ⟨132864, 135456, 606399010⟩ (CTN.node (CTN.node CTN.nil ⟨132864, 135872, 598984808⟩ CTN.nil) ⟨132864, 136416, 589459545⟩ CTN.nil)) ⟨132864, 137280, 574717227⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132864, 138496, 554741196⟩ CTN.nil) ⟨132864, 139264, 542571166⟩ CTN.nil) ⟨132866, 135040, 615837994⟩ (CTN.node CTN.nil ⟨132866, 135872, 600847966⟩ CTN.nil)))) ⟨132869, 134740, 624253358⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132869, 135156, 616580371⟩ CTN.nil) ⟨132896, 136616, 615510774⟩ CTN.nil) ⟨132896, 138280, 586332142⟩ (CTN.node (CTN.node CTN.nil ⟨132896, 139264, 569889733⟩ CTN.nil) ⟨132901, 134388, 662478264⟩ CTN.nil)) ⟨132912, 134688, 667534784⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132916, 138864, 594121313⟩ CTN.nil) ⟨132916, 139264, 587305762⟩ CTN.nil) ⟨132918, 137460, 620691117⟩ (CTN.node CTN.nil ⟨132928, 135936, 658800327⟩ CTN.nil))) ⟨132928, 136160, 654463077⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132933, 135220, 677898345⟩ CTN.nil) ⟨132950, 136692, 665463864⟩ CTN.nil) ⟨132950, 137524, 649459828⟩ (CTN.node (CTN.node CTN.nil ⟨132960, 134736, 715387397⟩ CTN.nil) ⟨132960, 135168, 706258477⟩ CTN.nil)) ⟨132960, 135744, 694312030⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨132960, 136192, 685194673⟩ CTN.nil) ⟨132960, 137024, 668656196⟩ CTN.nil) ⟨132984, 138868, 655936975⟩ (CTN.node CTN.nil ⟨132992, 134816, 747104221⟩ CTN.nil))))) ⟨132992, 135232, 737926385⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨132992, 135808, 725450150⟩ CTN.nil) ⟨132992, 136640, 707890986⟩ CTN.nil) ⟨132992, 137472, 690860185⟩ (CTN.node (CTN.node CTN.nil ⟨132992, 138176, 676848108⟩ CTN.nil) ⟨132992, 139008, 660743480⟩ CTN.nil)) ⟨132992, 139264, 655884850⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133008, 135692, 744502096⟩ CTN.nil) ⟨133008, 138376, 688241636⟩ CTN.nil) ⟨133008, 139264, 670806273⟩ (CTN.node CTN.nil ⟨133012, 134867, 767214920⟩ CTN.nil))) ⟨133014, 135301, 759502587⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133014, 135988, 744226017⟩ CTN.nil) ⟨133024, 135488, 765858291⟩ CTN.nil) ⟨133040, 134656, 802483171⟩ (CTN.node (CTN.node CTN.nil ⟨133056, 134304, 828796562⟩ CTN.nil) ⟨133056, 134720, 818576427⟩ CTN.nil)) ⟨133056, 134832, 815851823⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133056, 135264, 805448294⟩ CTN.nil) ⟨133056, 135520, 799361491⟩ CTN.nil) ⟨133056, 135552, 798604692⟩ (CTN.node CTN.nil ⟨133056, 135840, 791833662⟩ CTN.nil)))) ⟨133056, 136384, 779238697⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133056, 136608, 774125415⟩ CTN.nil) ⟨133056, 136640, 773398376⟩ CTN.nil) ⟨133056, 137216, 760456517⟩ (CTN.node (CTN.node CTN.nil ⟨133056, 137472, 754791564⟩ CTN.nil) ⟨133064, 137476, 762893197⟩ CTN.nil)) ⟨133074, 136176, 803232081⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133078, 137652, 773352393⟩ CTN.nil) ⟨133088, 134320, 864649867⟩ CTN.nil) ⟨133088, 137152, 795219611⟩ (CTN.node CTN.nil ⟨133104, 134880, 868448145⟩ CTN.nil))) ⟨133106, 136816, 822338708⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133109, 134964, 871966381⟩ CTN.nil) ⟨133112, 139060, 776446514⟩ CTN.nil) ⟨133112, 139264, 771894260⟩ (CTN.node CTN.nil ⟨133120, 135296, 875862275⟩ CTN.nil)) ⟨133120, 135584, 868422152⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133120, 135712, 865140810⟩ CTN.nil) ⟨133120, 136128, 854582992⟩ CTN.nil) ⟨133120, 136352, 848964744⟩ (CTN.node CTN.nil ⟨133120, 136704, 840229078⟩ CTN.nil)))))) ⟨133120, 137472, 821556320⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133120, 138304, 801909404⟩ CTN.nil) ⟨133120, 139136, 782846616⟩ CTN.nil) ⟨133120, 139264, 779964392⟩ (CTN.node (CTN.node CTN.nil ⟨133136, 134752, 908698536⟩ CTN.nil) ⟨133152, 135360, 910853484⟩ CTN.nil)) ⟨133152, 135616, 903975018⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133152, 136384, 883725771⟩ CTN.nil) ⟨133152, 137216, 862425114⟩ CTN.nil) ⟨133168, 135488, 925943726⟩ (CTN.node CTN.nil ⟨133184, 136768, 909697132⟩ CTN.nil))) ⟨133184, 138576, 863012440⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133184, 139264, 846037011⟩ CTN.nil) ⟨133188, 137536, 893925345⟩ CTN.nil) ⟨133188, 139200, 851824915⟩ (CTN.node (CTN.node CTN.nil ⟨133200, 134976, 978329376⟩ CTN.nil) ⟨133204, 135075, 980271819⟩ CTN.nil)) ⟨133236, 137648, 944919642⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133236, 139264, 901698480⟩ CTN.nil) ⟨133240, 139264, 906053519⟩ CTN.nil) ⟨133248, 134656, 1046999565⟩ (CTN.node CTN.nil ⟨133248, 135024, 1035598074⟩ CTN.nil)))) ⟨133248, 135456, 1022411138⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133248, 135488, 1021442706⟩ CTN.nil) ⟨133248, 136032, 1005153526⟩ CTN.nil) ⟨133248, 137600, 959986155⟩ (CTN.node (CTN.node CTN.nil ⟨133248, 138816, 926695276⟩ CTN.nil) ⟨133248, 139264, 914795035⟩ CTN.nil)) ⟨133267, 135122, 1056212021⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133267, 135538, 1043266268⟩ CTN.nil) ⟨133280, 135872, 1048974831⟩ CTN.nil) ⟨133285, 135156, 1077750328⟩ (CTN.node CTN.nil ⟨133288, 137008, 1024072962⟩ CTN.nil))) ⟨133316, 135522, 1105183716⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133328, 135534, 1120095271⟩ CTN.nil) ⟨133330, 137072, 1072969121⟩ CTN.nil) ⟨133344, 135552, 1140056468⟩ (CTN.node (CTN.node CTN.nil ⟨133344, 136128, 1120826646⟩ CTN.nil) ⟨133344, 136896, 1095813526⟩ CTN.nil)) ⟨133364, 135635, 1163156018⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133364, 136306, 1140354466⟩ CTN.nil) ⟨133392, 135168, 1216616750⟩ CTN.nil) ⟨133408, 135232, 1235814744⟩ (CTN.node CTN.nil ⟨133426, 134800, 1276515723⟩ CTN.nil))))) ⟨133428, 135699, 1245614855⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133428, 136370, 1221208289⟩ CTN.nil) ⟨133428, 137138, 1194002951⟩ CTN.nil) ⟨133428, 137904, 1167619341⟩ (CTN.node (CTN.node CTN.nil ⟨133428, 139264, 1122547815⟩ CTN.nil) ⟨133440, 136992, 1214714744⟩ CTN.nil)) ⟨133440, 137024, 1213577129⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133440, 137792, 1186669770⟩ CTN.nil) ⟨133440, 137856, 1184461327⟩ CTN.nil) ⟨133440, 138624, 1158356720⟩ (CTN.node CTN.nil ⟨133440, 139008, 1145574253⟩ CTN.nil))) ⟨133440, 139264, 1137150528⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133475, 135762, 1307237706⟩ CTN.nil) ⟨133488, 135264, 1344887569⟩ CTN.nil) ⟨133504, 136320, 1325493849⟩ (CTN.node (CTN.node CTN.nil ⟨133504, 137088, 1295954558⟩ CTN.nil) ⟨133504, 137984, 1262524966⟩ CTN.nil)) ⟨133504, 139136, 1221112853⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133504, 139264, 1216617055⟩ CTN.nil) ⟨133525, 135796, 1375626540⟩ CTN.nil) ⟨133536, 135712, 1394660283⟩ (CTN.node CTN.nil ⟨133536, 135744, 1393341760⟩ CTN.nil)))) ⟨133536, 136128, 1377640430⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133536, 136320, 1369872751⟩ CTN.nil) ⟨133556, 135843, 1417775830⟩ CTN.nil) ⟨133556, 136530, 1389371819⟩ (CTN.node (CTN.node CTN.nil ⟨133568, 135808, 1436500049⟩ CTN.nil) ⟨133568, 137920, 1350268023⟩ CTN.nil)) ⟨133568, 137980, 1347914199⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133568, 138752, 1318081261⟩ CTN.nil) ⟨133568, 139264, 1298750327⟩ CTN.nil) ⟨133616, 139264, 1362097342⟩ (CTN.node CTN.nil ⟨133620, 136594, 1477865436⟩ CTN.nil))) ⟨133620, 137362, 1444995991⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133622, 137332, 1449094105⟩ CTN.nil) ⟨133632, 135840, 1528842988⟩ CTN.nil) ⟨133632, 137984, 1435752141⟩ (CTN.node CTN.nil ⟨133632, 138048, 1433083882⟩ CTN.nil)) ⟨133632, 138112, 1430421821⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133632, 138560, 1411959527⟩ CTN.nil) ⟨133632, 139200, 1386098725⟩ CTN.nil) ⟨133632, 139264, 1383545347⟩ (CTN.node CTN.nil ⟨133680, 135456, 1619331385⟩ CTN.nil))))))) ⟨133680, 138304, 1489650854⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133680, 139264, 1448885146⟩ CTN.nil) ⟨133683, 135538, 1620012892⟩ CTN.nil) ⟨133688, 136000, 1605637963⟩ (CTN.node (CTN.node CTN.nil ⟨133696, 135872, 1623943057⟩ CTN.nil) ⟨133696, 136288, 1604148427⟩ CTN.nil)) ⟨133696, 136704, 1584654656⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133696, 138320, 1511682896⟩ CTN.nil) ⟨133696, 138624, 1498428639⟩ CTN.nil) ⟨133696, 139264, 1470996705⟩ (CTN.node CTN.nil ⟨133698, 135872, 1627007243⟩ CTN.nil))) ⟨133701, 135988, 1626032453⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133712, 138336, 1533864418⟩ CTN.nil) ⟨133714, 135920, 1649284853⟩ CTN.nil) ⟨133728, 137280, 1605519338⟩ (CTN.node (CTN.node CTN.nil ⟨133728, 139264, 1515716701⟩ CTN.nil) ⟨133744, 139264, 1538324947⟩ CTN.nil)) ⟨133760, 138944, 1575570569⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133760, 139264, 1561098561⟩ CTN.nil) ⟨133782, 137524, 1675069351⟩ CTN.nil) ⟨133792, 137024, 1715155652⟩ (CTN.node CTN.nil ⟨133806, 136876, 1744421151⟩ CTN.nil)))) ⟨133824, 136032, 1817202469⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133824, 136608, 1786658581⟩ CTN.nil) ⟨133824, 136640, 1784980596⟩ CTN.nil) ⟨133824, 137472, 1742036624⟩ (CTN.node (CTN.node CTN.nil ⟨133824, 139008, 1666095930⟩ CTN.nil) ⟨133824, 139264, 1653844664⟩ CTN.nil)) ⟨133858, 136896, 1825557454⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133888, 136352, 1903975621⟩ CTN.nil) ⟨133888, 136384, 1902184080⟩ CTN.nil) ⟨133888, 136896, 1873804091⟩ (CTN.node CTN.nil ⟨133888, 137216, 1856335274⟩ CTN.nil))) ⟨133888, 137472, 1842506671⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133888, 138880, 1768710122⟩ CTN.nil) ⟨133888, 139264, 1749228337⟩ CTN.nil) ⟨133920, 136384, 1955119362⟩ (CTN.node (CTN.node CTN.nil ⟨133920, 137472, 1893781209⟩ CTN.nil) ⟨133938, 136880, 1956507832⟩ CTN.nil)) ⟨133938, 137648, 1913082997⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨133938, 138480, 1867390970⟩ CTN.nil) ⟨133952, 136128, 2023966768⟩ CTN.nil) ⟨133952, 137536, 1942117880⟩ (CTN.node CTN.nil ⟨133952, 138304, 1899216342⟩ CTN.nil))))) ⟨133952, 138880, 1867815890⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨133952, 139136, 1854068651⟩ CTN.nil) ⟨133984, 137216, 2013403101⟩ CTN.nil) ⟨134000, 139264, 1922474841⟩ (CTN.node (CTN.node CTN.nil ⟨134008, 139264, 1935156779⟩ CTN.nil) ⟨134016, 137568, 2046013453⟩ CTN.nil)) ⟨134016, 138432, 1995267134⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134016, 138944, 1965937216⟩ CTN.nil) ⟨134016, 139264, 1947879594⟩ CTN.nil) ⟨134035, 136306, 2156185537⟩ (CTN.node CTN.nil ⟨134080, 139264, 2051131731⟩ CTN.nil))) ⟨134099, 136370, 2265298619⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134112, 136288, 2294161861⟩ CTN.nil) ⟨134112, 136704, 2266282978⟩ CTN.nil) ⟨134112, 136896, 2253558749⟩ (CTN.node (CTN.node CTN.nil ⟨134132, 138674, 2173648088⟩ CTN.nil) ⟨134132, 139264, 2136943856⟩ CTN.nil)) ⟨134136, 139264, 2143615933⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134144, 139264, 2156990541⟩ CTN.nil) ⟨134148, 138560, 2208129316⟩ CTN.nil) ⟨134148, 139264, 2163693069⟩ (CTN.node CTN.nil ⟨134162, 137904, 2275051555⟩ CTN.nil)))) ⟨134162, 138736, 2220814206⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134192, 138604, 2281147024⟩ CTN.nil) ⟨134196, 137138, 2387812871⟩ CTN.nil) ⟨134208, 137792, 2364100186⟩ (CTN.node (CTN.node CTN.nil ⟨134208, 138556, 2312241003⟩ CTN.nil) ⟨134208, 139264, 2265447257⟩ CTN.nil)) ⟨134243, 136530, 2518399235⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134260, 139264, 2355474918⟩ CTN.nil) ⟨134272, 137856, 2475365938⟩ CTN.nil) ⟨134272, 138624, 2420810796⟩ (CTN.node CTN.nil ⟨134272, 139264, 2376492688⟩ CTN.nil))) ⟨134304, 137856, 2534206708⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134324, 138898, 2494813197⟩ CTN.nil) ⟨134324, 139264, 2468616629⟩ CTN.nil) ⟨134336, 137728, 2603401114⟩ (CTN.node CTN.nil ⟨134376, 139264, 2562437838⟩ CTN.nil)) ⟨134388, 137362, 2730895123⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134388, 139264, 2584329339⟩ CTN.nil) ⟨134400, 136608, 2815613683⟩ CTN.nil) ⟨134400, 139264, 2606310863⟩ (CTN.node CTN.nil ⟨134448, 138924, 2721691938⟩ CTN.nil)))))) ⟨134452, 139264, 2702602693⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134464, 137472, 2870378285⟩ CTN.nil) ⟨134528, 139264, 2846363239⟩ CTN.nil) ⟨134560, 138280, 2991865569⟩ (CTN.node (CTN.node CTN.nil ⟨134580, 139264, 2946787818⟩ CTN.nil) ⟨134592, 139008, 2992202361⟩ CTN.nil)) ⟨134592, 139264, 2970199867⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134656, 139136, 3108004162⟩ CTN.nil) ⟨134656, 139264, 3096561355⟩ CTN.nil) ⟨134706, 137648, 3350273710⟩ (CTN.node CTN.nil ⟨134720, 138304, 3316186198⟩ CTN.nil))) ⟨134752, 139264, 3290811149⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134760, 139264, 3307252513⟩ CTN.nil) ⟨134764, 139264, 3315487799⟩ CTN.nil) ⟨134770, 138480, 3404081078⟩ (CTN.node (CTN.node CTN.nil ⟨134784, 139136, 3369214663⟩ CTN.nil) ⟨134784, 139200, 3363005254⟩ CTN.nil)) ⟨134784, 139264, 3356810152⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨134800, 137548, 3562910225⟩ CTN.nil) ⟨134800, 139264, 3390042950⟩ CTN.nil) ⟨134852, 139200, 3505578450⟩ (CTN.node CTN.nil ⟨134880, 138432, 3645102712⟩ CTN.nil)))) ⟨134912, 139264, 3627008003⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨134952, 139264, 3713468245⟩ CTN.nil) ⟨134964, 139264, 3739593216⟩ CTN.nil) ⟨134976, 139264, 3765804281⟩ (CTN.node (CTN.node CTN.nil ⟨134994, 138736, 3863707790⟩ CTN.nil) ⟨135040, 138624, 3979907456⟩ CTN.nil)) ⟨135084, 139264, 4005562410⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨135104, 139264, 4050720899⟩ CTN.nil) ⟨135148, 139264, 4150899686⟩ CTN.nil) ⟨135152, 139264, 4160063320⟩ (CTN.node CTN.nil ⟨135156, 139264, 4169236350⟩ CTN.nil))) ⟨135168, 139264, 4196811774⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨135228, 139264, 4335953225⟩ CTN.nil) ⟨135232, 139264, 4345304050⟩ CTN.nil) ⟨135280, 139264, 4458239724⟩ (CTN.node (CTN.node CTN.nil ⟨135296, 139264, 4496181990⟩ CTN.nil) ⟨135408, 139264, 4765910148⟩ CTN.nil)) ⟨135424, 139264, 4805029944⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨135468, 139264, 4913361425⟩ CTN.nil) ⟨135474, 139264, 4928219142⟩ CTN.nil) ⟨135488, 139264, 4962966511⟩ (CTN.node CTN.nil ⟨135504, 139264, 5002813647⟩ CTN.nil))))) ⟨135552, 139264, 5123221857⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨135664, 139264, 5409194802⟩ CTN.nil) ⟨135668, 139264, 5419537237⟩ CTN.nil) ⟨135680, 139264, 5450617679⟩ (CTN.node (CTN.node CTN.nil ⟨135692, 138376, 5624258188⟩ CTN.nil) ⟨135698, 139264, 5497387576⟩ CTN.nil)) ⟨135744, 139264, 5617721592⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨135808, 139264, 5787071159⟩ CTN.nil) ⟨135812, 139264, 5797729633⟩ CTN.nil) ⟨135860, 139264, 5926307948⟩ (CTN.node CTN.nil ⟨135872, 139264, 5958647136⟩ CTN.nil))) ⟨135920, 139264, 6088778417⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨135936, 139264, 6132429910⟩ CTN.nil) ⟨136000, 139264, 6308399481⟩ CTN.nil) ⟨136016, 139264, 6352731183⟩ (CTN.node (CTN.node CTN.nil ⟨136176, 139264, 6803423869⟩ CTN.nil) ⟨136192, 139264, 6849223449⟩ CTN.nil)) ⟨136316, 139264, 7208600993⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨136320, 139264, 7220323464⟩ CTN.nil) ⟨136448, 139264, 7599659374⟩ CTN.nil) ⟨136704, 139264, 8382305677⟩ (CTN.node CTN.nil ⟨136816, 139264, 8734456341⟩ CTN.nil)))) ⟨136896, 139264, 8989516069⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨136960, 139264, 9195640158⟩ CTN.nil) ⟨137216, 139264, 10038053565⟩ CTN.nil) ⟨137448, 139264, 10825193196⟩ (CTN.node (CTN.node CTN.nil ⟨137472, 139264, 10907852980⟩ CTN.nil) ⟨137548, 139264, 11171087318⟩ CTN.nil)) ⟨137728, 139264, 11803265435⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨137792, 139264, 12030905505⟩ CTN.nil) ⟨137832, 139264, 12173921802⟩ CTN.nil) ⟨137836, 139264, 12188254433⟩ (CTN.node CTN.nil ⟨137856, 139264, 12260001552⟩ CTN.nil))) ⟨137912, 139264, 12461631464⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨138156, 139264, 13352401972⟩ CTN.nil) ⟨138376, 139264, 14171581030⟩ CTN.nil) ⟨138556, 139264, 14852189218⟩ (CTN.node CTN.nil ⟨138944, 139264, 16347424240⟩ CTN.nil)) ⟨139064, 139264, 16816763875⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 139316, 17578910843⟩ CTN.nil) ⟨139264, 139376, 17548575280⟩ CTN.nil) ⟨139264, 139392, 17540496856⟩ (CTN.node CTN.nil ⟨139264, 139456, 17508229636⟩ CTN.nil))))))))

noncomputable def tab5 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 139584, 17443917607⟩ CTN.nil) ⟨139264, 139628, 17421878604⟩ CTN.nil) ⟨139264, 139632, 17419876786⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 139644, 17413873056⟩ CTN.nil) ⟨139264, 139648, 17411872388⟩ CTN.nil)) ⟨139264, 139776, 17348002527⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 139820, 17326114956⟩ CTN.nil) ⟨139264, 139888, 17292356600⟩ CTN.nil) ⟨139264, 140016, 17229034327⟩ (CTN.node CTN.nil ⟨139264, 140032, 17221139448⟩ CTN.nil))) ⟨139264, 140144, 17166001795⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 140160, 17158143022⟩ CTN.nil) ⟨139264, 140224, 17126752890⟩ CTN.nil) ⟨139264, 140272, 17103257415⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 140288, 17095434549⟩ CTN.nil) ⟨139264, 140296, 17091524795⟩ CTN.nil)) ⟨139264, 140336, 17071992787⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 140400, 17040799606⟩ CTN.nil) ⟨139264, 140416, 17033012451⟩ CTN.nil) ⟨139264, 140544, 16970875159⟩ (CTN.node CTN.nil ⟨139264, 140624, 16932183286⟩ CTN.nil)))) ⟨139264, 140672, 16909021113⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 140800, 16847448766⟩ CTN.nil) ⟨139264, 140896, 16801453444⟩ CTN.nil) ⟨139264, 140928, 16786156578⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 141056, 16725143020⟩ CTN.nil) ⟨139264, 141120, 16694740252⟩ CTN.nil)) ⟨139264, 141164, 16673878437⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 141184, 16664406573⟩ CTN.nil) ⟨139264, 141240, 16637921129⟩ CTN.nil) ⟨139264, 141288, 16615261211⟩ (CTN.node CTN.nil ⟨139264, 141312, 16603945726⟩ CTN.nil))) ⟨139264, 141440, 16543758980⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 141484, 16523132823⟩ CTN.nil) ⟨139264, 141552, 16491319254⟩ CTN.nil) ⟨139264, 141672, 16435364317⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 141696, 16424201838⟩ CTN.nil) ⟨139264, 141808, 16372235461⟩ CTN.nil)) ⟨139264, 141824, 16364828489⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 141884, 16337089643⟩ CTN.nil) ⟨139264, 141952, 16305723334⟩ CTN.nil) ⟨139264, 142064, 16254225185⟩ (CTN.node CTN.nil ⟨139264, 142080, 16246884921⟩ CTN.nil))))) ⟨139264, 142392, 16104574861⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 142572, 16023181821⟩ CTN.nil) ⟨139264, 142592, 16014169939⟩ CTN.nil) ⟨139264, 142832, 15906520205⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 142848, 15899375782⟩ CTN.nil) ⟨139264, 142944, 15856593418⟩ CTN.nil)) ⟨139264, 143088, 15792689464⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 143104, 15785608923⟩ CTN.nil) ⟨139264, 143232, 15729107282⟩ CTN.nil) ⟨139264, 143360, 15672858345⟩ (CTN.node CTN.nil ⟨139264, 143616, 15561113166⟩ CTN.nil))) ⟨139264, 143744, 15505614239⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 143848, 15460703539⟩ CTN.nil) ⟨139264, 143872, 15450362643⟩ CTN.nil) ⟨139264, 144000, 15395357056⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 144128, 15340596165⟩ CTN.nil) ⟨139264, 144232, 15296282214⟩ CTN.nil)) ⟨139264, 144236, 15294581031⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 144256, 15286078662⟩ CTN.nil) ⟨139264, 144384, 15231803251⟩ CTN.nil) ⟨139264, 144448, 15204755927⟩ (CTN.node CTN.nil ⟨139264, 144512, 15177768643⟩ CTN.nil)))) ⟨139264, 144556, 15159249630⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 144568, 15154203895⟩ CTN.nil) ⟨139264, 144640, 15123973555⟩ CTN.nil) ⟨139264, 144768, 15070416714⟩ (CTN.node (CTN.node CTN.nil ⟨139264, 144880, 15023748919⟩ CTN.nil) ⟨139264, 144896, 15017096854⟩ CTN.nil)) ⟨139264, 145136, 14917756482⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 145152, 14911163054⟩ CTN.nil) ⟨139264, 145408, 14806162186⟩ CTN.nil) ⟨139264, 145536, 14754008520⟩ (CTN.node CTN.nil ⟨139264, 145664, 14702084403⟩ CTN.nil))) ⟨139264, 145720, 14679439475⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 145792, 14650388624⟩ CTN.nil) ⟨139264, 145920, 14598919978⟩ CTN.nil) ⟨139264, 146656, 14307323494⟩ (CTN.node CTN.nil ⟨139264, 146688, 14294811379⟩ CTN.nil)) ⟨139264, 146920, 14204506596⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 146944, 14195205494⟩ CTN.nil) ⟨139264, 147072, 14145728051⟩ CTN.nil) ⟨139264, 147168, 14108761445⟩ (CTN.node CTN.nil ⟨139264, 147200, 14096466096⟩ CTN.nil)))))) ⟨139264, 147304, 14056598649⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨139264, 147456, 13998584151⟩ CTN.nil) ⟨139392, 147456, 14402771777⟩ CTN.nil) ⟨140296, 145792, 18107522110⟩ (CTN.node (CTN.node CTN.nil ⟨143280, 147456, 26555312413⟩ CTN.nil) ⟨143744, 147456, 27820300340⟩ CTN.nil)) ⟨144560, 147456, 29852336640⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨144768, 147456, 30325936625⟩ CTN.nil) ⟨145792, 147456, 32356805476⟩ CTN.nil) ⟨146944, 147456, 33969258923⟩ (CTN.node CTN.nil ⟨147456, 147584, 34309130482⟩ CTN.nil))) ⟨147456, 147968, 33876836922⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨147456, 148224, 33541516667⟩ CTN.nil) ⟨147456, 148608, 32970465137⟩ CTN.nil) ⟨147456, 148736, 32762527531⟩ (CTN.node (CTN.node CTN.nil ⟨147456, 149936, 30419630429⟩ CTN.nil) ⟨147456, 150016, 30240113596⟩ CTN.nil)) ⟨147456, 150248, 29704611913⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨147456, 150528, 29030101448⟩ CTN.nil) ⟨147456, 150632, 28772093049⟩ CTN.nil) ⟨147456, 151216, 27254306961⟩ (CTN.node CTN.nil ⟨147456, 151288, 27059663693⟩ CTN.nil)))) ⟨147456, 151296, 27037941846⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨147456, 152064, 24872928246⟩ CTN.nil) ⟨147456, 153568, 20310965624⟩ CTN.nil) ⟨147456, 154080, 18710837552⟩ (CTN.node (CTN.node CTN.nil ⟨147456, 154480, 17459341625⟩ CTN.nil) ⟨147456, 154624, 17009903431⟩ CTN.nil)) ⟨147456, 155392, 14637876662⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨147456, 155616, 13958000492⟩ CTN.nil) ⟨147456, 155648, 13861447354⟩ CTN.nil) ⟨149504, 155648, 14582540172⟩ (CTN.node CTN.nil ⟨150016, 155648, 14764143575⟩ CTN.nil))) ⟨150056, 155648, 14778338584⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨150480, 155648, 14928818458⟩ CTN.nil) ⟨151248, 155648, 15201138791⟩ CTN.nil) ⟨151288, 155648, 15215302554⟩ (CTN.node (CTN.node CTN.nil ⟨151552, 155648, 15308711174⟩ CTN.nil) ⟨152312, 155648, 15576687041⟩ CTN.nil)) ⟨152440, 155648, 15621648341⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨152576, 155648, 15669355463⟩ CTN.nil) ⟨153344, 155648, 15937321714⟩ CTN.nil) ⟨153384, 155648, 15951202994⟩ (CTN.node CTN.nil ⟨153472, 155648, 15981712824⟩ CTN.nil))))) ⟨153552, 155648, 16009413693⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨153936, 155648, 16141882826⟩ CTN.nil) ⟨154016, 155648, 16169372002⟩ CTN.nil) ⟨154128, 155648, 16207790642⟩ (CTN.node (CTN.node CTN.nil ⟨154144, 155648, 16213272601⟩ CTN.nil) ⟨154320, 155648, 16273465500⟩ CTN.nil)) ⟨154480, 155648, 16328008463⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨154704, 155648, 16404071343⟩ CTN.nil) ⟨155384, 155648, 16632681460⟩ CTN.nil) ⟨155512, 155648, 16675300310⟩ (CTN.node CTN.nil ⟨155552, 155648, 16688590372⟩ CTN.nil))) ⟨155648, 156128, 15055097072⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 156712, 13094851951⟩ CTN.nil) ⟨155648, 156784, 12859034356⟩ CTN.nil) ⟨155648, 157164, 11638396600⟩ (CTN.node (CTN.node CTN.nil ⟨155648, 158880, 6731105836⟩ CTN.nil) ⟨155648, 159304, 5697463721⟩ CTN.nil)) ⟨155648, 159848, 4488267008⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 159964, 4248032345⟩ CTN.nil) ⟨155648, 160028, 4118191710⟩ CTN.nil) ⟨155648, 160076, 4022079525⟩ (CTN.node CTN.nil ⟨155648, 160200, 3778849012⟩ CTN.nil)))) ⟨155648, 160672, 2920630997⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 160800, 2706598375⟩ CTN.nil) ⟨155648, 160896, 2551366758⟩ CTN.nil) ⟨155648, 160908, 2532282763⟩ (CTN.node (CTN.node CTN.nil ⟨155648, 161040, 2327064683⟩ CTN.nil) ⟨155648, 161592, 1562953401⟩ CTN.nil)) ⟨155648, 161628, 1518420333⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 161696, 1436078251⟩ CTN.nil) ⟨155648, 161720, 1407570987⟩ CTN.nil) ⟨155648, 161804, 1310075146⟩ (CTN.node CTN.nil ⟨155648, 162040, 1055138091⟩ CTN.nil))) ⟨155648, 162112, 982932448⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 162208, 890706929⟩ CTN.nil) ⟨155648, 162320, 788952566⟩ CTN.nil) ⟨155648, 162576, 579938940⟩ (CTN.node CTN.nil ⟨155648, 162636, 535680826⟩ CTN.nil)) ⟨155648, 162684, 501563617⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 162688, 498772193⟩ CTN.nil) ⟨155648, 162712, 482190484⟩ CTN.nil) ⟨155648, 162748, 457853833⟩ (CTN.node CTN.nil ⟨155648, 162760, 449884421⟩ CTN.nil))))))) ⟨155648, 162868, 381367472⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 162944, 336605342⟩ CTN.nil) ⟨155648, 163060, 273764269⟩ CTN.nil) ⟨155648, 163252, 184225501⟩ (CTN.node (CTN.node CTN.nil ⟨155648, 163328, 153739518⟩ CTN.nil) ⟨155648, 163468, 104890089⟩ CTN.nil)) ⟨155648, 163656, 54086008⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨155648, 163840, 20615427⟩ CTN.nil) ⟨155984, 161932, 1182802510⟩ CTN.nil) ⟨156028, 163704, 46060394⟩ (CTN.node CTN.nil ⟨156092, 162168, 944899590⟩ CTN.nil))) ⟨156156, 163640, 61241851⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨156192, 163840, 22761939⟩ CTN.nil) ⟨156220, 162232, 888416880⟩ CTN.nil) ⟨156220, 163768, 34648972⟩ (CTN.node (CTN.node CTN.nil ⟨156236, 163656, 57974267⟩ CTN.nil) ⟨156620, 161032, 2406446775⟩ CTN.nil)) ⟨156620, 162760, 471861935⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨156700, 161048, 2386927665⟩ CTN.nil) ⟨156700, 162712, 506982941⟩ CTN.nil) ⟨156784, 159532, 5316586541⟩ (CTN.node CTN.nil ⟨156784, 162280, 862410075⟩ CTN.nil)))) ⟨156928, 163840, 25624568⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨156952, 161956, 1196526169⟩ CTN.nil) ⟨157068, 163016, 321266994⟩ CTN.nil) ⟨157080, 162148, 999691119⟩ (CTN.node (CTN.node CTN.nil ⟨157164, 159848, 4656863911⟩ CTN.nil) ⟨157216, 160254, 3824653465⟩ CTN.nil)) ⟨157216, 161628, 1596690809⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨157240, 163252, 204695050⟩ CTN.nil) ⟨157344, 161692, 1522145098⟩ CTN.nil) ⟨157344, 163356, 161975313⟩ (CTN.node CTN.nil ⟨157392, 163532, 100099113⟩ CTN.nil))) ⟨157452, 160554, 3276246397⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨157452, 161928, 1247319128⟩ CTN.nil) ⟨157452, 163656, 65643485⟩ CTN.nil) ⟨157472, 163120, 271330424⟩ (CTN.node (CTN.node CTN.nil ⟨157520, 163468, 122121734⟩ CTN.nil) ⟨157648, 163596, 82932175⟩ CTN.nil)) ⟨157692, 162362, 814615617⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨157692, 163704, 55424951⟩ CTN.nil) ⟨157756, 162458, 731631366⟩ CTN.nil) ⟨157756, 163768, 41920382⟩ (CTN.node CTN.nil ⟨157756, 163832, 30065678⟩ CTN.nil))))) ⟨157884, 163832, 30540193⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨157900, 163784, 39384948⟩ CTN.nil) ⟨157948, 163840, 29415363⟩ CTN.nil) ⟨157952, 163344, 173038990⟩ (CTN.node (CTN.node CTN.nil ⟨158300, 162712, 541236561⟩ CTN.nil) ⟨158348, 161418, 1933454174⟩ CTN.nil)) ⟨158348, 162760, 507288359⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨158364, 161370, 2002630407⟩ CTN.nil) ⟨158364, 162712, 542505923⟩ CTN.nil) ⟨158590, 161628, 1658895943⟩ (CTN.node CTN.nil ⟨158604, 163178, 256238613⟩ CTN.nil))) ⟨158826, 161064, 2493552969⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨158826, 161928, 1298049156⟩ CTN.nil) ⟨158880, 163292, 204638671⟩ CTN.nil) ⟨159008, 163356, 177901668⟩ (CTN.node (CTN.node CTN.nil ⟨159034, 163704, 62050407⟩ CTN.nil) ⟨159130, 163832, 34838719⟩ CTN.nil)) ⟨159180, 162282, 930524565⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨159180, 163656, 75189846⟩ CTN.nil) ⟨159248, 163840, 33742546⟩ CTN.nil) ⟨159272, 162934, 404615693⟩ (CTN.node CTN.nil ⟨159304, 161510, 1848680848⟩ CTN.nil)))) ⟨159304, 162374, 845637400⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨159304, 163716, 60290931⟩ CTN.nil) ⟨159356, 163840, 34068889⟩ CTN.nil) ⟨159384, 163732, 56781713⟩ (CTN.node (CTN.node CTN.nil ⟨159400, 161934, 1310384600⟩ CTN.nil) ⟨159420, 163840, 34259564⟩ CTN.nil)) ⟨159436, 163840, 34306912⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨159484, 163840, 34448183⟩ CTN.nil) ⟨159532, 160906, 2796565758⟩ CTN.nil) ⟨159532, 162280, 941454607⟩ (CTN.node CTN.nil ⟨159690, 161928, 1326727110⟩ CTN.nil))) ⟨159690, 162760, 530810871⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨159706, 161880, 1384344033⟩ CTN.nil) ⟨159706, 162712, 567084046⟩ CTN.nil) ⟨159848, 161190, 2347190265⟩ (CTN.node CTN.nil ⟨159848, 162532, 715700068⟩ CTN.nil)) ⟨159964, 162170, 1064653931⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨159964, 163002, 370938460⟩ CTN.nil) ⟨160168, 162374, 865123121⟩ CTN.nil) ⟨160200, 162438, 806105692⟩ (CTN.node CTN.nil ⟨160200, 163302, 211550071⟩ CTN.nil)))))) ⟨160268, 163840, 36581420⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨160272, 163840, 36591418⟩ CTN.nil) ⟨160376, 163382, 177350961⟩ CTN.nil) ⟨160376, 163840, 36848052⟩ (CTN.node (CTN.node CTN.nil ⟨160538, 162712, 580206422⟩ CTN.nil) ⟨160554, 162792, 520052877⟩ CTN.nil)) ⟨160554, 163656, 81196264⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨160560, 163094, 322552785⟩ CTN.nil) ⟨160614, 163116, 310527495⟩ CTN.nil) ⟨160646, 162852, 478139693⟩ (CTN.node CTN.nil ⟨160774, 163308, 212917245⟩ CTN.nil))) ⟨160778, 163720, 64686094⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨160796, 163002, 380132340⟩ CTN.nil) ⟨160906, 162280, 972747913⟩ CTN.nil) ⟨161032, 163238, 248685973⟩ (CTN.node (CTN.node CTN.nil ⟨161032, 163840, 38314108⟩ CTN.nil) ⟨161048, 163222, 256949320⟩ CTN.nil)) ⟨161048, 163840, 38346457⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨161064, 163302, 217635920⟩ CTN.nil) ⟨161190, 162532, 739240914⟩ CTN.nil) ⟨161208, 163543, 119544890⟩ (CTN.node CTN.nil ⟨161208, 163840, 38660719⟩ CTN.nil)))) ⟨161240, 163543, 119672598⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨161240, 163840, 38721542⟩ CTN.nil) ⟨161336, 163687, 75069928⟩ CTN.nil) ⟨161338, 163544, 119706954⟩ (CTN.node (CTN.node CTN.nil ⟨161368, 163687, 75159066⟩ CTN.nil) ⟨161418, 163656, 84097564⟩ CTN.nil)) ⟨161510, 163716, 67737620⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨161574, 163812, 45083213⟩ CTN.nil) ⟨161642, 163840, 39426844⟩ CTN.nil) ⟨161718, 163840, 39547745⟩ (CTN.node CTN.nil ⟨161878, 163840, 39789100⟩ CTN.nil))) ⟨161879, 163798, 48660107⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨161879, 163840, 39790552⟩ CTN.nil) ⟨161880, 163840, 39792003⟩ CTN.nil) ⟨161896, 163840, 39815127⟩ (CTN.node CTN.nil ⟨161911, 163840, 39836642⟩ CTN.nil)) ⟨161928, 163840, 39860833⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨161988, 163840, 39944577⟩ CTN.nil) ⟨162023, 163840, 39992247⟩ CTN.nil) ⟨162055, 163840, 40035067⟩ (CTN.node CTN.nil ⟨162280, 163654, 86841469⟩ CTN.nil))))) ⟨162295, 163798, 49283846⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨162438, 163840, 40490397⟩ CTN.nil) ⟨162532, 163840, 40585856⟩ CTN.nil) ⟨162711, 163840, 40749670⟩ (CTN.node (CTN.node CTN.nil ⟨163840, 163856, 37992713⟩ CTN.nil) ⟨163840, 163872, 34887405⟩ CTN.nil)) ⟨163840, 163874, 34508579⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨163840, 163888, 31914883⟩ CTN.nil) ⟨163840, 163929, 24903544⟩ CTN.nil) ⟨163840, 163942, 22862290⟩ (CTN.node CTN.nil ⟨163840, 163958, 20470104⟩ CTN.nil))) ⟨163840, 163960, 20180399⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨163840, 163978, 17666198⟩ CTN.nil) ⟨163840, 163989, 16212258⟩ CTN.nil) ⟨163840, 164010, 13610303⟩ (CTN.node (CTN.node CTN.nil ⟨163840, 164021, 12338349⟩ CTN.nil) ⟨163840, 164026, 11780857⟩ CTN.nil)) ⟨163840, 164053, 8993528⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨163840, 164054, 8897523⟩ CTN.nil) ⟨163840, 164096, 5331210⟩ CTN.nil) ⟨163840, 164102, 4896000⟩ (CTN.node CTN.nil ⟨163840, 164118, 3826145⟩ CTN.nil)))) ⟨163840, 164122, 3579290⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨163840, 164128, 3224460⟩ CTN.nil) ⟨163840, 164166, 1407589⟩ CTN.nil) ⟨163840, 164194, 544145⟩ (CTN.node (CTN.node CTN.nil ⟨163840, 164197, 475533⟩ CTN.nil) ⟨163840, 164214, 174066⟩ CTN.nil)) ⟨163840, 164229, 31302⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164246, 166933, 8518⟩ CTN.nil) ⟨164248, 166940, 15200⟩ CTN.nil) ⟨164248, 169632, 14256⟩ (CTN.node CTN.nil ⟨164248, 171296, 13709⟩ CTN.nil))) ⟨164254, 166788, 46959⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164256, 166692, 61529⟩ CTN.nil) ⟨164256, 167268, 60684⟩ CTN.nil) ⟨164256, 168100, 59489⟩ (CTN.node CTN.nil ⟨164256, 169128, 58053⟩ CTN.nil)) ⟨164256, 170280, 56495⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164272, 166772, 246408⟩ CTN.nil) ⟨164272, 167352, 243003⟩ CTN.nil) ⟨164272, 168632, 235695⟩ (CTN.node CTN.nil ⟨164272, 169792, 229308⟩ CTN.nil))))))))

noncomputable def tab6 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164276, 166200, 316302⟩ CTN.nil) ⟨164276, 166778, 311931⟩ CTN.nil) ⟨164276, 169280, 293861⟩ (CTN.node (CTN.node CTN.nil ⟨164278, 168052, 337167⟩ CTN.nil) ⟨164280, 166204, 390578⟩ CTN.nil)) ⟨164280, 166780, 385200⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164280, 167360, 379877⟩ CTN.nil) ⟨164280, 167399, 379523⟩ CTN.nil) ⟨164280, 168086, 373344⟩ (CTN.node CTN.nil ⟨164280, 168854, 366585⟩ CTN.nil))) ⟨164280, 169686, 359435⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164288, 166784, 554902⟩ CTN.nil) ⟨164288, 167136, 550233⟩ CTN.nil) ⟨164288, 167552, 544778⟩ (CTN.node (CTN.node CTN.nil ⟨164288, 168416, 533664⟩ CTN.nil) ⟨164288, 169280, 522831⟩ CTN.nil)) ⟨164288, 170172, 511934⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164288, 170816, 504243⟩ CTN.nil) ⟨164288, 171708, 493828⟩ CTN.nil) ⟨164288, 172032, 490111⟩ (CTN.node CTN.nil ⟨164293, 166180, 686603⟩ CTN.nil)))) ⟨164293, 166612, 679496⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164294, 167236, 694920⟩ CTN.nil) ⟨164294, 168004, 682276⟩ CTN.nil) ⟨164308, 165811, 1141001⟩ (CTN.node (CTN.node CTN.nil ⟨164308, 166227, 1129599⟩ CTN.nil) ⟨164310, 166613, 1186022⟩ CTN.nil)) ⟨164310, 167284, 1167070⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164310, 168052, 1145841⟩ CTN.nil) ⟨164320, 166160, 1566528⟩ CTN.nil) ⟨164320, 166592, 1550310⟩ (CTN.node CTN.nil ⟨164320, 167168, 1529012⟩ CTN.nil))) ⟨164320, 167936, 1501180⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164320, 168000, 1498890⟩ CTN.nil) ⟨164320, 168704, 1473979⟩ CTN.nil) ⟨164320, 169536, 1445203⟩ (CTN.node (CTN.node CTN.nil ⟨164322, 166560, 1630134⟩ CTN.nil) ⟨164322, 167424, 1596679⟩ CTN.nil)) ⟨164326, 167300, 1761649⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164336, 165760, 2278561⟩ CTN.nil) ⟨164336, 167096, 2206419⟩ CTN.nil) ⟨164336, 170412, 2039323⟩ (CTN.node CTN.nil ⟨164336, 172032, 1963447⟩ CTN.nil))))) ⟨164340, 168882, 2294444⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164340, 169714, 2249696⟩ CTN.nil) ⟨164340, 171888, 2137820⟩ CTN.nil) ⟨164352, 166192, 3070179⟩ (CTN.node (CTN.node CTN.nil ⟨164352, 166624, 3038400⟩ CTN.nil) ⟨164352, 166960, 3013968⟩ CTN.nil)) ⟨164352, 167200, 2996666⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164352, 167392, 2982915⟩ CTN.nil) ⟨164352, 167968, 2942130⟩ CTN.nil) ⟨164352, 168544, 2902040⟩ (CTN.node CTN.nil ⟨164352, 169408, 2843177⟩ CTN.nil))) ⟨164352, 171072, 2733959⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164352, 171520, 2705454⟩ CTN.nil) ⟨164352, 171584, 2701413⟩ CTN.nil) ⟨164352, 172032, 2673331⟩ (CTN.node (CTN.node CTN.nil ⟨164356, 166227, 3290859⟩ CTN.nil) ⟨164374, 166693, 4343759⟩ CTN.nil)) ⟨164374, 166725, 4340418⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164374, 167380, 4272745⟩ CTN.nil) ⟨164374, 167412, 4269472⟩ CTN.nil) ⟨164374, 168244, 4185482⟩ (CTN.node CTN.nil ⟨164376, 168724, 4262549⟩ CTN.nil)))) ⟨164376, 168788, 4256075⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164376, 170452, 4091993⟩ CTN.nil) ⟨164376, 172032, 3943452⟩ CTN.nil) ⟨164380, 167392, 4663059⟩ (CTN.node (CTN.node CTN.nil ⟨164380, 168224, 4571316⟩ CTN.nil) ⟨164384, 166016, 5099581⟩ CTN.nil)) ⟨164384, 166448, 5046742⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164384, 166880, 4994585⟩ CTN.nil) ⟨164384, 166912, 4990748⟩ CTN.nil) ⟨164384, 167232, 4952584⟩ (CTN.node CTN.nil ⟨164384, 167424, 4929861⟩ CTN.nil))) ⟨164384, 167744, 4892278⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164384, 168000, 4862469⟩ CTN.nil) ⟨164384, 168064, 4855052⟩ CTN.nil) ⟨164390, 166677, 5446481⟩ (CTN.node CTN.nil ⟨164390, 167364, 5357430⟩ CTN.nil)) ⟨164390, 168132, 5260025⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164390, 168964, 5156988⟩ CTN.nil) ⟨164400, 166080, 6287592⟩ CTN.nil) ⟨164400, 169920, 5737187⟩ (CTN.node CTN.nil ⟨164400, 172032, 5460093⟩ CTN.nil)))))) ⟨164402, 167376, 6248235⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164402, 167408, 6243449⟩ CTN.nil) ⟨164402, 168144, 6134641⟩ CTN.nil) ⟨164402, 168240, 6120624⟩ (CTN.node (CTN.node CTN.nil ⟨164402, 169008, 6009918⟩ CTN.nil) ⟨164402, 169072, 6000806⟩ CTN.nil)) ⟨164404, 172032, 5736847⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164406, 167109, 6603095⟩ CTN.nil) ⟨164407, 166678, 6752516⟩ CTN.nil) ⟨164407, 167094, 6685392⟩ (CTN.node CTN.nil ⟨164416, 166096, 7606800⟩ CTN.nil))) ⟨164416, 166656, 7504874⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164416, 166944, 7453119⟩ CTN.nil) ⟨164416, 167072, 7430260⟩ CTN.nil) ⟨164416, 167456, 7362208⟩ (CTN.node (CTN.node CTN.nil ⟨164416, 167488, 7356573⟩ CTN.nil) ⟨164416, 167776, 7306093⟩ CTN.nil)) ⟨164416, 168032, 7261585⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164416, 168064, 7256045⟩ CTN.nil) ⟨164416, 168800, 7130080⟩ CTN.nil) ⟨164416, 168896, 7113852⟩ (CTN.node CTN.nil ⟨164416, 169472, 7017448⟩ CTN.nil)))) ⟨164416, 169728, 6975126⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164416, 171136, 6747977⟩ CTN.nil) ⟨164416, 171648, 6667676⟩ CTN.nil) ⟨164416, 172032, 6608234⟩ (CTN.node (CTN.node CTN.nil ⟨164432, 166624, 8940261⟩ CTN.nil) ⟨164432, 170080, 8234151⟩ CTN.nil)) ⟨164444, 167136, 9970961⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164444, 167968, 9774489⟩ CTN.nil) ⟨164448, 166640, 10490570⟩ CTN.nil) ⟨164448, 166976, 10406221⟩ (CTN.node CTN.nil ⟨164448, 167056, 10386263⟩ CTN.nil))) ⟨164448, 167488, 10279313⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164448, 167808, 10200978⟩ CTN.nil) ⟨164448, 168064, 10138847⟩ CTN.nil) ⟨164448, 168832, 9955271⟩ (CTN.node (CTN.node CTN.nil ⟨164448, 169664, 9761062⟩ CTN.nil) ⟨164453, 166324, 11085710⟩ CTN.nil)) ⟨164458, 166960, 11436733⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164464, 170476, 11108245⟩ CTN.nil) ⟨164464, 172012, 10716044⟩ CTN.nil) ⟨164464, 172032, 10711052⟩ (CTN.node CTN.nil ⟨164468, 168242, 12133881⟩ CTN.nil))))) ⟨164468, 169536, 11766959⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164468, 170674, 11455673⟩ CTN.nil) ⟨164468, 172016, 11101699⟩ CTN.nil) ⟨164468, 172032, 11097562⟩ (CTN.node (CTN.node CTN.nil ⟨164469, 165972, 12925604⟩ CTN.nil) ⟨164469, 166388, 12796570⟩ CTN.nil)) ⟨164470, 166789, 12784798⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164470, 167476, 12575905⟩ CTN.nil) ⟨164470, 168244, 12347409⟩ CTN.nil) ⟨164471, 166758, 12905984⟩ (CTN.node CTN.nil ⟨164476, 166656, 13504640⟩ CTN.nil))) ⟨164480, 166112, 14151218⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164480, 166976, 13860022⟩ CTN.nil) ⟨164480, 167520, 13680516⟩ CTN.nil) ⟨164480, 167744, 13607447⟩ (CTN.node (CTN.node CTN.nil ⟨164480, 167840, 13576281⟩ CTN.nil) ⟨164480, 168096, 13493607⟩ CTN.nil)) ⟨164480, 168864, 13249335⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164480, 169216, 13139226⟩ CTN.nil) ⟨164480, 169472, 13059864⟩ CTN.nil) ⟨164480, 169536, 13040118⟩ (CTN.node CTN.nil ⟨164480, 169984, 12902932⟩ CTN.nil)))) ⟨164480, 170816, 12652911⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164480, 171200, 12539561⟩ CTN.nil) ⟨164480, 171648, 12408920⟩ CTN.nil) ⟨164480, 172032, 12298293⟩ (CTN.node (CTN.node CTN.nil ⟨164482, 168192, 13688416⟩ CTN.nil) ⟨164482, 169024, 13420374⟩ CTN.nil)) ⟨164488, 168900, 14136641⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164499, 166802, 16212699⟩ CTN.nil) ⟨164500, 166435, 16483200⟩ CTN.nil) ⟨164501, 167188, 16312626⟩ (CTN.node CTN.nil ⟨164501, 167604, 16150961⟩ CTN.nil))) ⟨164504, 170528, 15418356⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164512, 168896, 17011626⟩ CTN.nil) ⟨164512, 169728, 16679886⟩ CTN.nil) ⟨164528, 171584, 17905733⟩ (CTN.node CTN.nil ⟨164532, 169106, 19512425⟩ CTN.nil)) ⟨164532, 169938, 19132386⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164532, 170770, 18761558⟩ CTN.nil) ⟨164532, 172032, 18216063⟩ CTN.nil) ⟨164534, 169908, 19409541⟩ (CTN.node CTN.nil ⟨164534, 170740, 19033275⟩ CTN.nil))))))) ⟨164544, 170624, 20407884⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164544, 172032, 19746721⟩ CTN.nil) ⟨164548, 166435, 23143895⟩ CTN.nil) ⟨164549, 166404, 23312082⟩ (CTN.node (CTN.node CTN.nil ⟨164549, 166420, 23303101⟩ CTN.nil) ⟨164551, 166838, 23370115⟩ CTN.nil)) ⟨164551, 167254, 23138023⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164552, 169126, 22271362⟩ CTN.nil) ⟨164552, 172032, 20801560⟩ CTN.nil) ⟨164563, 166482, 25428509⟩ (CTN.node CTN.nil ⟨164563, 166898, 25175436⟩ CTN.nil))) ⟨164564, 166738, 25429405⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164565, 167668, 25022831⟩ CTN.nil) ⟨164576, 166768, 27331819⟩ CTN.nil) ⟨164576, 166816, 27300313⟩ (CTN.node (CTN.node CTN.nil ⟨164576, 166848, 27279334⟩ CTN.nil) ⟨164576, 167232, 27029154⟩ CTN.nil)) ⟨164580, 166786, 27975560⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164592, 166016, 30550387⟩ CTN.nil) ⟨164592, 166784, 29990464⟩ CTN.nil) ⟨164592, 167200, 29692528⟩ (CTN.node CTN.nil ⟨164595, 166466, 30739043⟩ CTN.nil)))) ⟨164595, 166898, 30421397⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164596, 168338, 29557928⟩ CTN.nil) ⟨164596, 169202, 28957673⟩ CTN.nil) ⟨164596, 170544, 28055236⟩ (CTN.node (CTN.node CTN.nil ⟨164596, 172032, 27095347⟩ CTN.nil) ⟨164598, 167701, 30349256⟩ CTN.nil)) ⟨164598, 168372, 29867425⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164608, 166032, 33383585⟩ CTN.nil) ⟨164608, 166448, 33050442⟩ CTN.nil) ⟨164608, 166880, 32708874⟩ (CTN.node CTN.nil ⟨164608, 168288, 31625823⟩ CTN.nil))) ⟨164608, 169152, 30983385⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164608, 169344, 30842843⟩ CTN.nil) ⟨164608, 169824, 30494960⟩ CTN.nil) ⟨164608, 170304, 30151971⟩ (CTN.node (CTN.node CTN.nil ⟨164608, 170688, 29881047⟩ CTN.nil) ⟨164608, 171904, 29042964⟩ CTN.nil)) ⟨164608, 172032, 28956464⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164616, 167590, 33573179⟩ CTN.nil) ⟨164626, 167632, 35350893⟩ CTN.nil) ⟨164626, 168400, 34709185⟩ (CTN.node CTN.nil ⟨164626, 168496, 34629999⟩ CTN.nil))))) ⟨164626, 169264, 34004576⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164626, 169328, 33953098⟩ CTN.nil) ⟨164629, 166516, 36877794⟩ CTN.nil) ⟨164636, 167072, 37712491⟩ (CTN.node (CTN.node CTN.nil ⟨164640, 166912, 38627830⟩ CTN.nil) ⟨164640, 167332, 38240717⟩ CTN.nil)) ⟨164640, 167488, 38098169⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164640, 167680, 37923636⟩ CTN.nil) ⟨164640, 168164, 37488083⟩ CTN.nil) ⟨164640, 168256, 37406001⟩ (CTN.node CTN.nil ⟨164640, 169644, 36194472⟩ CTN.nil))) ⟨164640, 170024, 35871373⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164640, 171688, 34498290⟩ CTN.nil) ⟨164640, 172032, 34222676⟩ CTN.nil) ⟨164645, 166580, 39918858⟩ (CTN.node (CTN.node CTN.nil ⟨164648, 168496, 38698675⟩ CTN.nil) ⟨164648, 170672, 36758952⟩ CTN.nil)) ⟨164648, 172032, 35608173⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164656, 167736, 40969999⟩ CTN.nil) ⟨164656, 168504, 40226748⟩ CTN.nil) ⟨164656, 169656, 39143200⟩ (CTN.node CTN.nil ⟨164656, 170816, 38088754⟩ CTN.nil)))) ⟨164660, 166584, 42932945⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164660, 168466, 41042789⟩ CTN.nil) ⟨164660, 170898, 38751710⟩ CTN.nil) ⟨164660, 172032, 37738144⟩ (CTN.node (CTN.node CTN.nil ⟨164662, 166933, 42981636⟩ CTN.nil) ⟨164662, 167349, 42555021⟩ CTN.nil)) ⟨164662, 167765, 42133689⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164662, 168436, 41465020⟩ CTN.nil) ⟨164662, 169204, 40715891⟩ CTN.nil) ⟨164662, 170036, 39923332⟩ (CTN.node CTN.nil ⟨164662, 170868, 39149971⟩ CTN.nil))) ⟨164664, 166588, 43752153⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164664, 166844, 43483719⟩ CTN.nil) ⟨164664, 167164, 43151067⟩ CTN.nil) ⟨164664, 167424, 42883126⟩ (CTN.node CTN.nil ⟨164664, 167744, 42556204⟩ CTN.nil)) ⟨164664, 168512, 41784213⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164668, 166592, 44579050⟩ CTN.nil) ⟨164672, 166878, 45106844⟩ CTN.nil) ⟨164672, 167742, 44182883⟩ (CTN.node CTN.nil ⟨164672, 167744, 44180772⟩ CTN.nil)))))) ⟨164672, 167752, 44172328⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164672, 168520, 43371058⟩ CTN.nil) ⟨164672, 169084, 42794176⟩ CTN.nil) ⟨164672, 169664, 42210900⟩ (CTN.node (CTN.node CTN.nil ⟨164672, 169672, 42202924⟩ CTN.nil) ⟨164672, 170176, 41704248⟩ CTN.nil)) ⟨164672, 170368, 41516215⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164672, 170812, 41085434⟩ CTN.nil) ⟨164672, 170832, 41066161⟩ CTN.nil) ⟨164672, 171008, 40897048⟩ (CTN.node CTN.nil ⟨164672, 171200, 40713553⟩ CTN.nil))) ⟨164672, 171904, 40049483⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164672, 172032, 39930202⟩ CTN.nil) ⟨164676, 166914, 45908141⟩ CTN.nil) ⟨164676, 167778, 44967968⟩ (CTN.node (CTN.node CTN.nil ⟨164676, 169152, 43521871⟩ CTN.nil) ⟨164676, 172032, 40674687⟩ CTN.nil)) ⟨164677, 167380, 45606974⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164677, 167796, 45155508⟩ CTN.nil) ⟨164680, 169254, 44218896⟩ CTN.nil) ⟨164680, 170628, 42809086⟩ (CTN.node CTN.nil ⟨164682, 167216, 46842559⟩ CTN.nil)))) ⟨164692, 166563, 49765232⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164692, 166995, 49251275⟩ CTN.nil) ⟨164692, 167666, 48466067⟩ CTN.nil) ⟨164694, 170100, 46152582⟩ (CTN.node (CTN.node CTN.nil ⟨164694, 170932, 45258888⟩ CTN.nil) ⟨164704, 168320, 50288836⟩ CTN.nil)) ⟨164704, 169088, 49379670⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164707, 167026, 52542959⟩ CTN.nil) ⟨164724, 166227, 57542485⟩ CTN.nil) ⟨164724, 166643, 56968927⟩ (CTN.node CTN.nil ⟨164724, 167059, 56402499⟩ CTN.nil))) ⟨164724, 167730, 55503622⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164724, 168562, 54413798⟩ CTN.nil) ⟨164724, 169394, 53350602⟩ CTN.nil) ⟨164724, 170736, 51689839⟩ (CTN.node CTN.nil ⟨164724, 172032, 50146920⟩ CTN.nil)) ⟨164725, 166612, 57247793⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164726, 168500, 54946422⟩ CTN.nil) ⟨164728, 167488, 56754436⟩ CTN.nil) ⟨164728, 168256, 55723320⟩ (CTN.node CTN.nil ⟨164728, 172032, 50981156⟩ CTN.nil))))) ⟨164736, 166928, 59427261⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164736, 167344, 58837398⟩ CTN.nil) ⟨164736, 167392, 58769808⟩ CTN.nil) ⟨164736, 167776, 58232576⟩ (CTN.node (CTN.node CTN.nil ⟨164736, 167808, 58188084⟩ CTN.nil) ⟨164736, 168352, 57438189⟩ CTN.nil)) ⟨164736, 168384, 57394454⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164736, 169120, 56399966⟩ CTN.nil) ⟨164736, 169216, 56271844⟩ CTN.nil) ⟨164736, 169952, 55301567⟩ (CTN.node CTN.nil ⟨164736, 170048, 55176556⟩ CTN.nil))) ⟨164736, 170816, 54189086⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164736, 170880, 54107798⟩ CTN.nil) ⟨164736, 171968, 52748947⟩ CTN.nil) ⟨164741, 167860, 59296259⟩ (CTN.node (CTN.node CTN.nil ⟨164752, 166592, 63846095⟩ CTN.nil) ⟨164752, 169100, 60134854⟩ CTN.nil)) ⟨164752, 170764, 57820695⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164752, 172032, 56131647⟩ CTN.nil) ⟨164758, 167877, 63372940⟩ CTN.nil) ⟨164758, 168564, 62344145⟩ (CTN.node CTN.nil ⟨164759, 167862, 63641234⟩ CTN.nil)))) ⟨164768, 168384, 65058432⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164768, 169152, 63882691⟩ CTN.nil) ⟨164771, 167122, 67815790⟩ CTN.nil) ⟨164784, 166624, 72041939⟩ (CTN.node (CTN.node CTN.nil ⟨164784, 166976, 71435194⟩ CTN.nil) ⟨164784, 167392, 70726345⟩ CTN.nil)) ⟨164788, 166659, 73046404⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164788, 167091, 72292441⟩ CTN.nil) ⟨164788, 167762, 71140548⟩ CTN.nil) ⟨164788, 168530, 69850160⟩ (CTN.node CTN.nil ⟨164788, 168562, 69797032⟩ CTN.nil))) ⟨164788, 169394, 68433261⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164788, 169426, 68381477⟩ CTN.nil) ⟨164788, 170736, 66302986⟩ CTN.nil) ⟨164788, 172032, 64323871⟩ (CTN.node CTN.nil ⟨164790, 169332, 69036137⟩ CTN.nil)) ⟨164800, 169184, 71827047⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164800, 170304, 69952638⟩ CTN.nil) ⟨164800, 170880, 69012469⟩ CTN.nil) ⟨164800, 172032, 67179058⟩ (CTN.node CTN.nil ⟨164803, 166690, 77052939⟩ CTN.nil))))))))

noncomputable def tab7 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164804, 166659, 77385257⟩ CTN.nil) ⟨164804, 167075, 76615909⟩ CTN.nil) ⟨164804, 167746, 75395011⟩ (CTN.node (CTN.node CTN.nil ⟨164804, 168514, 74027324⟩ CTN.nil) ⟨164804, 169346, 72580489⟩ CTN.nil)) ⟨164804, 170688, 70320483⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164808, 172032, 69117095⟩ CTN.nil) ⟨164816, 166448, 81132764⟩ CTN.nil) ⟨164816, 166880, 80294278⟩ (CTN.node CTN.nil ⟨164822, 167109, 81530794⟩ CTN.nil))) ⟨164822, 167525, 80722410⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164822, 167941, 79924024⟩ CTN.nil) ⟨164822, 168628, 78627031⟩ CTN.nil) ⟨164822, 169396, 77208118⟩ (CTN.node (CTN.node CTN.nil ⟨164822, 170228, 75706906⟩ CTN.nil) ⟨164822, 171060, 74242017⟩ CTN.nil)) ⟨164823, 167094, 81841366⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164823, 167926, 80228331⟩ CTN.nil) ⟨164832, 166512, 85582797⟩ CTN.nil) ⟨164832, 166656, 85286807⟩ (CTN.node CTN.nil ⟨164832, 167072, 84438889⟩ CTN.nil)))) ⟨164832, 167268, 84043043⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164832, 167488, 83601486⟩ CTN.nil) ⟨164832, 168512, 81584001⟩ CTN.nil) ⟨164848, 166944, 89351199⟩ (CTN.node (CTN.node CTN.nil ⟨164852, 167352, 89652485⟩ CTN.nil) ⟨164856, 166780, 92086322⟩ CTN.nil)) ⟨164856, 172032, 81326433⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164860, 167360, 92000316⟩ CTN.nil) ⟨164864, 166672, 94745794⟩ CTN.nil) ⟨164864, 167056, 93875959⟩ (CTN.node CTN.nil ⟨164864, 167136, 93696002⟩ CTN.nil))) ⟨164864, 167712, 92412965⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164864, 172032, 83458205⟩ CTN.nil) ⟨164880, 167072, 98727240⟩ CTN.nil) ⟨164880, 167488, 97748135⟩ (CTN.node (CTN.node CTN.nil ⟨164884, 166771, 100693626⟩ CTN.nil) ⟨164884, 167203, 99654993⟩ CTN.nil)) ⟨164884, 167890, 98030717⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164885, 166388, 101942497⟩ CTN.nil) ⟨164885, 167188, 100001505⟩ CTN.nil) ⟨164885, 167220, 99924831⟩ (CTN.node CTN.nil ⟨164886, 168692, 96776109⟩ CTN.nil))))) ⟨164896, 167168, 103500547⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164896, 167744, 102083520⟩ CTN.nil) ⟨164896, 168512, 100231674⟩ CTN.nil) ⟨164896, 168576, 100079257⟩ (CTN.node (CTN.node CTN.nil ⟨164896, 169964, 96843880⟩ CTN.nil) ⟨164896, 170920, 94691313⟩ CTN.nil)) ⟨164896, 172032, 92262208⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164901, 167172, 105078564⟩ CTN.nil) ⟨164903, 168022, 103590007⟩ CTN.nil) ⟨164912, 170304, 100828171⟩ (CTN.node CTN.nil ⟨164916, 167267, 109665241⟩ CTN.nil))) ⟨164916, 167954, 107878487⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164916, 168786, 105763074⟩ CTN.nil) ⟨164916, 169618, 103699279⟩ CTN.nil) ⟨164916, 170992, 100400063⟩ (CTN.node (CTN.node CTN.nil ⟨164916, 172032, 97989758⟩ CTN.nil) ⟨164917, 167604, 109107153⟩ CTN.nil)) ⟨164918, 167124, 110695692⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164920, 168694, 107255985⟩ CTN.nil) ⟨164928, 167200, 113786810⟩ CTN.nil) ⟨164928, 167536, 112874973⟩ (CTN.node CTN.nil ⟨164928, 167776, 112229251⟩ CTN.nil)))) ⟨164928, 167968, 111715996⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164928, 168544, 110193742⟩ CTN.nil) ⟨164928, 168576, 110109935⟩ CTN.nil) ⟨164928, 169408, 107958664⟩ (CTN.node (CTN.node CTN.nil ⟨164928, 169664, 107307328⟩ CTN.nil) ⟨164928, 170240, 105859694⟩ CTN.nil)) ⟨164928, 171008, 103967291⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164928, 171984, 101622983⟩ CTN.nil) ⟨164928, 172032, 101509403⟩ CTN.nil) ⟨164932, 168674, 111138422⟩ (CTN.node CTN.nil ⟨164932, 170816, 105657698⟩ CTN.nil))) ⟨164932, 172032, 102696473⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164950, 169524, 114678513⟩ CTN.nil) ⟨164960, 168000, 122287516⟩ CTN.nil) ⟨164960, 168640, 120438176⟩ (CTN.node CTN.nil ⟨164967, 167254, 126927501⟩ CTN.nil)) ⟨164967, 168086, 124428224⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164979, 166898, 132289339⟩ CTN.nil) ⟨164980, 167299, 131378942⟩ CTN.nil) ⟨164980, 167986, 129238818⟩ (CTN.node CTN.nil ⟨164980, 168754, 126897713⟩ CTN.nil)))))) ⟨164980, 169618, 124327000⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164980, 170928, 120552228⟩ CTN.nil) ⟨164980, 170992, 120371509⟩ CTN.nil) ⟨164980, 172032, 117481749⟩ (CTN.node (CTN.node CTN.nil ⟨164981, 167284, 131782620⟩ CTN.nil) ⟨164982, 169588, 125090509⟩ CTN.nil)) ⟨164984, 169526, 125952125⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164984, 172032, 118758900⟩ CTN.nil) ⟨164992, 166816, 137268293⟩ CTN.nil) ⟨164992, 167232, 135904882⟩ (CTN.node CTN.nil ⟨164992, 167600, 134712877⟩ CTN.nil))) ⟨164992, 167648, 134558363⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164992, 168032, 133330199⟩ CTN.nil) ⟨164992, 168064, 133228486⟩ CTN.nil) ⟨164992, 169152, 129827243⟩ (CTN.node (CTN.node CTN.nil ⟨164992, 169376, 129140517⟩ CTN.nil) ⟨164992, 170496, 125774218⟩ CTN.nil)) ⟨164992, 172032, 121333996⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨164998, 169540, 130707529⟩ CTN.nil) ⟨165004, 172032, 125248627⟩ CTN.nil) ⟨165008, 167200, 141875498⟩ (CTN.node CTN.nil ⟨165016, 169888, 135886242⟩ CTN.nil)))) ⟨165024, 166448, 150561849⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165024, 167216, 147809478⟩ CTN.nil) ⟨165024, 167632, 146344871⟩ CTN.nil) ⟨165024, 168064, 144843090⟩ (CTN.node (CTN.node CTN.nil ⟨165024, 168640, 142870564⟩ CTN.nil) ⟨165024, 170240, 137564873⟩ CTN.nil)) ⟨165027, 166898, 150086799⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165028, 167776, 147338455⟩ CTN.nil) ⟨165032, 170416, 139814749⟩ CTN.nil) ⟨165032, 172032, 134625406⟩ (CTN.node CTN.nil ⟨165040, 166880, 155167988⟩ CTN.nil))) ⟨165040, 168888, 147905370⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165046, 168052, 153154576⟩ CTN.nil) ⟨165046, 169716, 147224762⟩ CTN.nil) ⟨165048, 168854, 151008832⟩ (CTN.node (CTN.node CTN.nil ⟨165048, 170048, 146804178⟩ CTN.nil) ⟨165056, 167552, 158875835⟩ CTN.nil)) ⟨165056, 167816, 157876522⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165056, 168096, 156825218⟩ CTN.nil) ⟨165056, 168584, 155013782⟩ CTN.nil) ⟨165056, 169416, 151985346⟩ (CTN.node CTN.nil ⟨165056, 170576, 147885417⟩ CTN.nil))))) ⟨165058, 167264, 160762494⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165058, 168128, 157476993⟩ CTN.nil) ⟨165061, 167380, 161497976⟩ CTN.nil) ⟨165061, 167412, 161374294⟩ (CTN.node (CTN.node CTN.nil ⟨165062, 168004, 159496350⟩ CTN.nil) ⟨165074, 167248, 167196119⟩ CTN.nil)) ⟨165074, 168080, 163903812⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165077, 167364, 167937390⟩ CTN.nil) ⟨165078, 167349, 168400580⟩ CTN.nil) ⟨165078, 167765, 166733264⟩ (CTN.node CTN.nil ⟨165078, 168052, 165594998⟩ CTN.nil))) ⟨165088, 168100, 169388624⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165088, 170304, 160772817⟩ CTN.nil) ⟨165093, 167796, 172645881⟩ CTN.nil) ⟨165112, 169686, 172525387⟩ (CTN.node (CTN.node CTN.nil ⟨165112, 172032, 163288490⟩ CTN.nil) ⟨165120, 168160, 182193218⟩ CTN.nil)) ⟨165120, 168736, 179713455⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165120, 169504, 176472385⟩ CTN.nil) ⟨165120, 169664, 175806386⟩ CTN.nil) ⟨165120, 170336, 173043275⟩ (CTN.node CTN.nil ⟨165120, 171200, 169570007⟩ CTN.nil)))) ⟨165120, 171456, 168557666⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165120, 172032, 166307388⟩ CTN.nil) ⟨165124, 166995, 189052961⟩ CTN.nil) ⟨165140, 166643, 197643796⟩ (CTN.node (CTN.node CTN.nil ⟨165140, 167059, 195678675⟩ CTN.nil) ⟨165142, 169780, 184228481⟩ CTN.nil)) ⟨165152, 167344, 199579387⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165152, 167424, 199197461⟩ CTN.nil) ⟨165152, 167808, 197376883⟩ CTN.nil) ⟨165152, 168000, 196474397⟩ (CTN.node CTN.nil ⟨165152, 168416, 194536645⟩ CTN.nil))) ⟨165152, 169280, 190587854⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165152, 169536, 189437131⟩ CTN.nil) ⟨165152, 172032, 178660457⟩ CTN.nil) ⟨165157, 167476, 201143722⟩ (CTN.node CTN.nil ⟨165158, 167445, 201733589⟩ CTN.nil)) ⟨165158, 168132, 198450256⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165168, 167360, 206585936⟩ CTN.nil) ⟨165168, 167776, 204540685⟩ CTN.nil) ⟨165170, 168144, 203629991⟩ (CTN.node CTN.nil ⟨165172, 168275, 203872080⟩ CTN.nil))))))) ⟨165172, 168946, 200646340⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165172, 169714, 197032216⟩ CTN.nil) ⟨165172, 170546, 193208297⟩ CTN.nil) ⟨165172, 171184, 190338716⟩ (CTN.node (CTN.node CTN.nil ⟨165172, 172032, 186606590⟩ CTN.nil) ⟨165174, 169780, 197573199⟩ CTN.nil)) ⟨165176, 171124, 192250851⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165184, 167456, 213302108⟩ CTN.nil) ⟨165184, 168032, 210386786⟩ CTN.nil) ⟨165184, 168224, 209426098⟩ (CTN.node CTN.nil ⟨165184, 168800, 206576757⟩ CTN.nil))) ⟨165184, 168864, 206263164⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165184, 169728, 202087352⟩ CTN.nil) ⟨165184, 170704, 197496580⟩ CTN.nil) ⟨165184, 171264, 194921360⟩ (CTN.node (CTN.node CTN.nil ⟨165184, 172032, 191457522⟩ CTN.nil) ⟨165186, 167424, 214373740⟩ CTN.nil)) ⟨165192, 171076, 199123650⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165200, 167392, 220954443⟩ CTN.nil) ⟨165206, 168244, 219227048⟩ CTN.nil) ⟨165206, 169908, 210748538⟩ (CTN.node CTN.nil ⟨165212, 168224, 222072845⟩ CTN.nil)))) ⟨165216, 167408, 228316129⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165216, 167744, 226488776⟩ CTN.nil) ⟨165216, 167824, 226056391⟩ CTN.nil) ⟨165216, 167900, 225646580⟩ (CTN.node (CTN.node CTN.nil ⟨165216, 168064, 224765412⟩ CTN.nil) ⟨165216, 168256, 223739262⟩ CTN.nil)) ⟨165216, 168832, 220695760⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165216, 169408, 217703853⟩ CTN.nil) ⟨165216, 170584, 211751228⟩ CTN.nil) ⟨165216, 172032, 204698608⟩ (CTN.node CTN.nil ⟨165220, 167075, 232041386⟩ CTN.nil))) ⟨165220, 167091, 231952348⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165222, 168196, 226830933⟩ CTN.nil) ⟨165222, 168964, 222727081⟩ CTN.nil) ⟨165234, 168240, 232181934⟩ (CTN.node (CTN.node CTN.nil ⟨165234, 169072, 227636701⟩ CTN.nil) ⟨165235, 167122, 238951316⟩ CTN.nil)) ⟨165236, 169010, 228892620⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165238, 167525, 238089381⟩ CTN.nil) ⟨165238, 167941, 235734555⟩ CTN.nil) ⟨165238, 168244, 234037692⟩ (CTN.node CTN.nil ⟨165240, 167164, 241123163⟩ CTN.nil))))) ⟨165240, 172032, 214920817⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165244, 167424, 241552561⟩ CTN.nil) ⟨165244, 167744, 239711066⟩ CTN.nil) ⟨165248, 167056, 245643689⟩ (CTN.node (CTN.node CTN.nil ⟨165248, 167072, 245549421⟩ CTN.nil) ⟨165248, 167488, 243114241⟩ CTN.nil)) ⟨165248, 167744, 241630670⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165248, 167776, 241446021⟩ CTN.nil) ⟨165248, 167904, 240709186⟩ CTN.nil) ⟨165248, 168320, 238333809⟩ (CTN.node CTN.nil ⟨165248, 168608, 236706472⟩ CTN.nil))) ⟨165248, 168864, 235271600⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165248, 168896, 235093006⟩ CTN.nil) ⟨165248, 169728, 230508509⟩ CTN.nil) ⟨165248, 169792, 230160505⟩ (CTN.node (CTN.node CTN.nil ⟨165248, 169984, 229120428⟩ CTN.nil) ⟨165248, 170464, 226545833⟩ CTN.nil)) ⟨165248, 170560, 226035262⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165248, 171328, 222002062⟩ CTN.nil) ⟨165248, 171392, 221670039⟩ CTN.nil) ⟨165248, 172032, 218383722⟩ (CTN.node CTN.nil ⟨165266, 167569, 251413424⟩ CTN.nil)))) ⟨165266, 168240, 247418811⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165266, 169008, 242943643⟩ CTN.nil) ⟨165269, 168372, 248091138⟩ CTN.nil) ⟨165276, 167968, 253921167⟩ (CTN.node (CTN.node CTN.nil ⟨165280, 167808, 256870844⟩ CTN.nil) ⟨165280, 168320, 253753684⟩ CTN.nil)) ⟨165280, 168896, 250303206⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165280, 169472, 246911199⟩ CTN.nil) ⟨165280, 169664, 245793318⟩ CTN.nil) ⟨165284, 169128, 250854284⟩ (CTN.node CTN.nil ⟨165296, 167488, 266893339⟩ CTN.nil))) ⟨165300, 169842, 254295888⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165300, 170674, 249364307⟩ CTN.nil) ⟨165304, 171316, 247503382⟩ CTN.nil) ⟨165312, 167504, 274961550⟩ (CTN.node CTN.nil ⟨165312, 167920, 272241698⟩ CTN.nil)) ⟨165312, 168352, 269452751⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165312, 168384, 269247586⟩ CTN.nil) ⟨165312, 168672, 267409870⟩ CTN.nil) ⟨165312, 168896, 265991368⟩ (CTN.node CTN.nil ⟨165312, 168928, 265789494⟩ CTN.nil)))))) ⟨165312, 169696, 261001479⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165312, 170528, 255935538⟩ CTN.nil) ⟨165312, 170816, 254210634⟩ CTN.nil) ⟨165312, 171392, 250804215⟩ (CTN.node (CTN.node CTN.nil ⟨165312, 171648, 249308580⟩ CTN.nil) ⟨165312, 172032, 247085977⟩ CTN.nil)) ⟨165314, 169024, 266178378⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165316, 167203, 279027538⟩ CTN.nil) ⟨165320, 172032, 250798626⟩ CTN.nil) ⟨165324, 172032, 252665356⟩ (CTN.node CTN.nil ⟨165333, 167604, 285189623⟩ CTN.nil))) ⟨165333, 168020, 282370277⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165333, 168436, 279585698⟩ CTN.nil) ⟨165334, 169972, 270092006⟩ CTN.nil) ⟨165344, 167840, 289339706⟩ (CTN.node (CTN.node CTN.nil ⟨165344, 168608, 284093919⟩ CTN.nil) ⟨165344, 169472, 278333763⟩ CTN.nil)) ⟨165344, 169536, 277912920⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165344, 169728, 276655155⟩ CTN.nil) ⟨165360, 167552, 299869136⟩ CTN.nil) ⟨165360, 167968, 296903753⟩ (CTN.node CTN.nil ⟨165363, 167666, 300661752⟩ CTN.nil)))) ⟨165364, 168483, 295388053⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165364, 169170, 290609869⟩ CTN.nil) ⟨165364, 169938, 285382165⟩ CTN.nil) ⟨165364, 170770, 279850826⟩ (CTN.node (CTN.node CTN.nil ⟨165366, 170740, 281048346⟩ CTN.nil) ⟨165368, 171380, 277853197⟩ CTN.nil)) ⟨165368, 172032, 273657154⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165376, 169536, 294306471⟩ CTN.nil) ⟨165376, 171456, 281319677⟩ CTN.nil) ⟨165376, 171520, 280899255⟩ (CTN.node CTN.nil ⟨165376, 172032, 277564003⟩ CTN.nil))) ⟨165384, 169860, 296203282⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165394, 168400, 312029755⟩ CTN.nil) ⟨165395, 167730, 317606408⟩ CTN.nil) ⟨165396, 169744, 303297403⟩ (CTN.node CTN.nil ⟨165396, 171408, 291669037⟩ CTN.nil)) ⟨165408, 167232, 328711158⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165408, 167648, 325454353⟩ CTN.nil) ⟨165408, 168064, 322237797⟩ CTN.nil) ⟨165408, 170280, 305757670⟩ (CTN.node CTN.nil ⟨165424, 168032, 331405289⟩ CTN.nil))))) ⟨165424, 168504, 327700560⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165424, 171584, 304755516⟩ CTN.nil) ⟨165424, 172032, 301587550⟩ CTN.nil) ⟨165428, 169234, 324258245⟩ (CTN.node (CTN.node CTN.nil ⟨165430, 168117, 334104412⟩ CTN.nil) ⟨165430, 168533, 330811556⟩ CTN.nil)) ⟨165430, 169204, 325585297⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165432, 168512, 332093436⟩ CTN.nil) ⟨165432, 169792, 322173406⟩ CTN.nil) ⟨165436, 167938, 338935636⟩ (CTN.node CTN.nil ⟨165440, 167248, 346889877⟩ CTN.nil))) ⟨165440, 167632, 343716125⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165440, 167712, 343059503⟩ CTN.nil) ⟨165440, 168520, 336514750⟩ CTN.nil) ⟨165440, 170176, 323582017⟩ (CTN.node (CTN.node CTN.nil ⟨165440, 171600, 312954696⟩ CTN.nil) ⟨165440, 172032, 309817247⟩ CTN.nil)) ⟨165444, 169856, 328215330⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165444, 171584, 315168206⟩ CTN.nil) ⟨165445, 168564, 338978006⟩ CTN.nil) ⟨165456, 167648, 352834327⟩ (CTN.node CTN.nil ⟨165456, 168064, 349347168⟩ CTN.nil)))) ⟨165456, 172032, 318157845⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165458, 169328, 340131921⟩ CTN.nil) ⟨165459, 167762, 353617643⟩ CTN.nil) ⟨165460, 168498, 348039779⟩ (CTN.node (CTN.node CTN.nil ⟨165460, 169202, 342272550⟩ CTN.nil) ⟨165460, 169872, 336894423⟩ CTN.nil)) ⟨165472, 167744, 361376892⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165472, 168164, 357773235⟩ CTN.nil) ⟨165472, 168996, 350766267⟩ CTN.nil) ⟨165472, 169088, 350002035⟩ (CTN.node CTN.nil ⟨165472, 169152, 349471624⟩ CTN.nil))) ⟨165472, 170688, 337037997⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165472, 172032, 326609328⟩ CTN.nil) ⟨165474, 170048, 343265201⟩ CTN.nil) ⟨165475, 167746, 363126536⟩ (CTN.node CTN.nil ⟨165488, 172032, 335171679⟩ CTN.nil)) ⟨165490, 168496, 365433537⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165490, 169264, 358833753⟩ CTN.nil) ⟨165492, 170066, 353230824⟩ CTN.nil) ⟨165492, 170898, 346389537⟩ (CTN.node CTN.nil ⟨165494, 167765, 374247200⟩ CTN.nil))))))))

noncomputable def tab8 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165494, 169268, 361106093⟩ CTN.nil) ⟨165494, 170036, 354613983⟩ CTN.nil) ⟨165494, 170868, 347744705⟩ (CTN.node (CTN.node CTN.nil ⟨165496, 168256, 371073514⟩ CTN.nil) ⟨165496, 171572, 343156739⟩ CTN.nil)) ⟨165496, 172032, 339494425⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165504, 168112, 377120482⟩ CTN.nil) ⟨165504, 168544, 373261517⟩ CTN.nil) ⟨165504, 169120, 368192716⟩ (CTN.node CTN.nil ⟨165504, 172032, 343844881⟩ CTN.nil))) ⟨165509, 167796, 382995165⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165509, 168212, 379213249⟩ CTN.nil) ⟨165509, 168628, 375477916⟩ CTN.nil) ⟨165526, 170932, 365220320⟩ (CTN.node (CTN.node CTN.nil ⟨165528, 171552, 361082965⟩ CTN.nil) ⟨165536, 167742, 400027081⟩ CTN.nil)) ⟨165536, 169152, 386830029⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165540, 167778, 402160760⟩ CTN.nil) ⟨165556, 168530, 404826508⟩ CTN.nil) ⟨165556, 168562, 404518596⟩ (CTN.node CTN.nil ⟨165556, 169394, 396614670⟩ CTN.nil)))) ⟨165568, 168176, 415751352⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165568, 168224, 415276130⟩ CTN.nil) ⟨165568, 168608, 411498704⟩ CTN.nil) ⟨165568, 168640, 411185862⟩ (CTN.node (CTN.node CTN.nil ⟨165568, 169152, 406220595⟩ CTN.nil) ⟨165568, 169184, 405912761⟩ CTN.nil)) ⟨165568, 169216, 405605220⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165568, 169728, 400723951⟩ CTN.nil) ⟨165568, 169952, 398611504⟩ CTN.nil) ⟨165568, 170048, 397710433⟩ (CTN.node CTN.nil ⟨165568, 170880, 390006867⟩ CTN.nil))) ⟨165568, 172032, 379645803⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165571, 167890, 420495319⟩ CTN.nil) ⟨165572, 167843, 421601854⟩ CTN.nil) ⟨165572, 168514, 414914049⟩ (CTN.node (CTN.node CTN.nil ⟨165584, 167776, 429939680⟩ CTN.nil) ⟨165590, 168293, 428480632⟩ CTN.nil)) ⟨165590, 168709, 424262032⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165590, 169396, 417408324⟩ CTN.nil) ⟨165600, 167792, 440095447⟩ CTN.nil) ⟨165600, 168208, 435749586⟩ (CTN.node CTN.nil ⟨165600, 168640, 431293225⟩ CTN.nil))))) ⟨165600, 169216, 425439685⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165600, 169984, 417788628⟩ CTN.nil) ⟨165600, 170816, 409693130⟩ CTN.nil) ⟨165603, 167954, 440337761⟩ (CTN.node (CTN.node CTN.nil ⟨165618, 169280, 436143020⟩ CTN.nil) ⟨165632, 167824, 460750274⟩ CTN.nil)) ⟨165632, 169248, 445409555⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165632, 170016, 437400865⟩ CTN.nil) ⟨165632, 171136, 426041536⟩ CTN.nil) ⟨165632, 171328, 424131421⟩ (CTN.node CTN.nil ⟨165632, 171968, 417841225⟩ CTN.nil))) ⟨165632, 172032, 417218641⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165636, 168578, 455157497⟩ CTN.nil) ⟨165636, 169346, 446941254⟩ CTN.nil) ⟨165636, 172032, 419625740⟩ (CTN.node (CTN.node CTN.nil ⟨165648, 168256, 466596838⟩ CTN.nil) ⟨165652, 169394, 456750998⟩ CTN.nil)) ⟨165652, 169426, 456405369⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165654, 167941, 474138996⟩ CTN.nil) ⟨165654, 168773, 464840786⟩ CTN.nil) ⟨165654, 169460, 457334381⟩ (CTN.node CTN.nil ⟨165654, 170228, 449121486⟩ CTN.nil)))) ⟨165654, 171060, 440431220⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165664, 167488, 486118915⟩ CTN.nil) ⟨165664, 167904, 481309888⟩ CTN.nil) ⟨165664, 168320, 476560206⟩ (CTN.node (CTN.node CTN.nil ⟨165664, 170048, 457446981⟩ CTN.nil) ⟨165664, 170880, 448586330⟩ CTN.nil)) ⟨165664, 172032, 436669023⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165667, 167986, 482399896⟩ CTN.nil) ⟨165668, 170024, 460286841⟩ CTN.nil) ⟨165682, 171056, 458131587⟩ (CTN.node CTN.nil ⟨165682, 171888, 449309528⟩ CTN.nil))) ⟨165696, 168736, 493365267⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165696, 170172, 476891099⟩ CTN.nil) ⟨165696, 171392, 463432251⟩ CTN.nil) ⟨165696, 171900, 457968306⟩ (CTN.node CTN.nil ⟨165696, 172032, 456561745⟩ CTN.nil)) ⟨165728, 167920, 525449200⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165728, 168000, 524447129⟩ CTN.nil) ⟨165728, 168576, 517302311⟩ CTN.nil) ⟨165744, 168352, 531334784⟩ (CTN.node CTN.nil ⟨165744, 169486, 517230078⟩ CTN.nil)))))) ⟨165744, 170350, 506796804⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165744, 171692, 491107741⟩ CTN.nil) ⟨165744, 171756, 490374810⟩ CTN.nil) ⟨165744, 172032, 487229667⟩ (CTN.node (CTN.node CTN.nil ⟨165748, 168754, 529089264⟩ CTN.nil) ⟨165748, 168786, 528687373⟩ CTN.nil)) ⟨165748, 169618, 518370895⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165749, 168020, 539129233⟩ CTN.nil) ⟨165749, 168436, 533812640⟩ CTN.nil) ⟨165752, 172032, 492437631⟩ (CTN.node CTN.nil ⟨165760, 168032, 546877779⟩ CTN.nil))) ⟨165760, 168800, 536974018⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165760, 170304, 518220314⟩ CTN.nil) ⟨165760, 170496, 515885565⟩ CTN.nil) ⟨165760, 171456, 504407133⟩ (CTN.node (CTN.node CTN.nil ⟨165760, 172032, 497673197⟩ CTN.nil) ⟨165764, 168738, 540605025⟩ CTN.nil)) ⟨165764, 169506, 530855515⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165764, 170338, 520540357⟩ CTN.nil) ⟨165764, 171712, 504048109⟩ CTN.nil) ⟨165776, 167968, 559328457⟩ (CTN.node CTN.nil ⟨165792, 167984, 570847036⟩ CTN.nil)))) ⟨165792, 168400, 565216456⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165792, 168832, 559442626⟩ CTN.nil) ⟨165792, 169408, 551858427⟩ CTN.nil) ⟨165808, 169656, 560024763⟩ (CTN.node (CTN.node CTN.nil ⟨165808, 171328, 538441842⟩ CTN.nil) ⟨165810, 172016, 531218491⟩ CTN.nil)) ⟨165816, 169664, 565657656⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165816, 170816, 550523902⟩ CTN.nil) ⟨165824, 167632, 599695556⟩ CTN.nil) ⟨165824, 167648, 599466210⟩ (CTN.node CTN.nil ⟨165824, 168064, 593541520⟩ CTN.nil))) ⟨165824, 168480, 587689871⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165824, 168584, 586238245⟩ CTN.nil) ⟨165824, 168896, 581910185⟩ CTN.nil) ⟨165824, 169672, 571317536⟩ (CTN.node (CTN.node CTN.nil ⟨165824, 170816, 556137435⟩ CTN.nil) ⟨165824, 171328, 549507036⟩ CTN.nil)) ⟨165824, 171708, 544649852⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165824, 172032, 540550799⟩ CTN.nil) ⟨165832, 170832, 561568494⟩ CTN.nil) ⟨165840, 172032, 551545877⟩ (CTN.node CTN.nil ⟨165843, 168946, 595272499⟩ CTN.nil))))) ⟨165844, 169618, 586609684⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165845, 168132, 608424871⟩ CTN.nil) ⟨165846, 168533, 603396311⟩ CTN.nil) ⟨165856, 167664, 623736697⟩ (CTN.node (CTN.node CTN.nil ⟨165856, 168048, 618044162⟩ CTN.nil) ⟨165856, 168464, 611950366⟩ CTN.nil)) ⟨165856, 168896, 605701506⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165856, 170240, 586764147⟩ CTN.nil) ⟨165872, 167680, 635926493⟩ CTN.nil) ⟨165872, 168064, 630123260⟩ (CTN.node CTN.nil ⟨165876, 172032, 576687623⟩ CTN.nil))) ⟨165880, 172032, 579515563⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165888, 168080, 642313929⟩ CTN.nil) ⟨165888, 168496, 635982041⟩ CTN.nil) ⟨165888, 168928, 629489014⟩ (CTN.node (CTN.node CTN.nil ⟨165888, 169416, 622253688⟩ CTN.nil) ⟨165888, 169472, 621430071⟩ CTN.nil)) ⟨165888, 169504, 620960045⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165888, 170272, 609811603⟩ CTN.nil) ⟨165888, 171104, 598015091⟩ CTN.nil) ⟨165888, 171968, 586065323⟩ (CTN.node CTN.nil ⟨165888, 172032, 585192084⟩ CTN.nil)))) ⟨165892, 171840, 590678050⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165892, 172032, 588040663⟩ CTN.nil) ⟨165906, 168080, 656443232⟩ CTN.nil) ⟨165906, 170480, 620184259⟩ (CTN.node (CTN.node CTN.nil ⟨165906, 171312, 608201607⟩ CTN.nil) ⟨165906, 172032, 598064850⟩ CTN.nil)) ⟨165912, 171296, 612826061⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165920, 171944, 609421555⟩ CTN.nil) ⟨165920, 172032, 608173262⟩ CTN.nil) ⟨165922, 168128, 668365625⟩ (CTN.node CTN.nil ⟨165925, 168212, 669413873⟩ CTN.nil))) ⟨165925, 168628, 662820001⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165926, 170500, 634887121⟩ CTN.nil) ⟨165936, 168128, 679553542⟩ CTN.nil) ⟨165936, 168544, 672856456⟩ (CTN.node CTN.nil ⟨165936, 172032, 619828826⟩ CTN.nil)) ⟨165937, 168240, 678542840⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨165938, 170544, 643303652⟩ CTN.nil) ⟨165940, 169714, 657553209⟩ CTN.nil) ⟨165952, 170112, 660650349⟩ (CTN.node CTN.nil ⟨165952, 170336, 657175545⟩ CTN.nil))))))) ⟨165952, 171836, 634486220⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨165952, 172032, 631594310⟩ CTN.nil) ⟨165984, 168224, 716970261⟩ CTN.nil) ⟨165984, 168640, 709908451⟩ (CTN.node (CTN.node CTN.nil ⟨165984, 170368, 681489276⟩ CTN.nil) ⟨165984, 171200, 668313559⟩ CTN.nil)) ⟨165990, 168964, 709329504⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166000, 168608, 723558305⟩ CTN.nil) ⟨166000, 172012, 667860883⟩ CTN.nil) ⟨166000, 172032, 667549791⟩ (CTN.node CTN.nil ⟨166004, 168691, 725422123⟩ CTN.nil))) ⟨166004, 169107, 718296801⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166004, 169778, 706987216⟩ CTN.nil) ⟨166004, 170546, 694314612⟩ CTN.nil) ⟨166004, 171378, 680904825⟩ (CTN.node (CTN.node CTN.nil ⟨166004, 172032, 670590673⟩ CTN.nil) ⟨166006, 168709, 726758830⟩ CTN.nil)) ⟨166014, 169084, 726868076⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166016, 167824, 750678474⟩ CTN.nil) ⟨166016, 168208, 743833924⟩ CTN.nil) ⟨166016, 168864, 732320692⟩ (CTN.node CTN.nil ⟨166016, 171072, 695170427⟩ CTN.nil)))) ⟨166016, 172032, 679754458⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166032, 168224, 757020483⟩ CTN.nil) ⟨166032, 168640, 749564199⟩ CTN.nil) ⟨166034, 169008, 744705610⟩ (CTN.node (CTN.node CTN.nil ⟨166034, 172032, 693615791⟩ CTN.nil) ⟨166040, 170452, 724569245⟩ CTN.nil)) ⟨166048, 169664, 744731331⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166048, 169728, 743606568⟩ CTN.nil) ⟨166050, 169152, 755476403⟩ CTN.nil) ⟨166051, 169170, 755989609⟩ (CTN.node CTN.nil ⟨166054, 170628, 732855986⟩ CTN.nil))) ⟨166066, 170736, 740710512⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166068, 172032, 720176725⟩ CTN.nil) ⟨166080, 168320, 796326976⟩ CTN.nil) ⟨166080, 168608, 790889677⟩ (CTN.node (CTN.node CTN.nil ⟨166080, 168688, 789387561⟩ CTN.nil) ⟨166080, 169120, 781337498⟩ CTN.nil)) ⟨166080, 169152, 780745290⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166080, 169696, 770763090⟩ CTN.nil) ⟨166080, 169728, 770180886⟩ CTN.nil) ⟨166080, 170560, 755234758⟩ (CTN.node CTN.nil ⟨166080, 170816, 750709054⟩ CTN.nil))))) ⟨166080, 171136, 745099507⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166080, 171392, 740649566⟩ CTN.nil) ⟨166080, 172032, 729669240⟩ CTN.nil) ⟨166088, 172032, 736031785⟩ (CTN.node (CTN.node CTN.nil ⟨166101, 169204, 797695273⟩ CTN.nil) ⟨166112, 168608, 818653031⟩ CTN.nil)) ⟨166112, 168640, 818030649⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166112, 169472, 802054403⟩ CTN.nil) ⟨166112, 171328, 767797599⟩ CTN.nil) ⟨166120, 172032, 761755430⟩ (CTN.node CTN.nil ⟨166130, 169872, 809870985⟩ CTN.nil))) ⟨166130, 170736, 793571512⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166132, 169938, 810324023⟩ CTN.nil) ⟨166132, 172032, 771514533⟩ CTN.nil) ⟨166144, 169184, 835394153⟩ (CTN.node (CTN.node CTN.nil ⟨166144, 169216, 834761213⟩ CTN.nil) ⟨166144, 169312, 832865988⟩ CTN.nil)) ⟨166144, 169728, 824715253⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166144, 169760, 824092413⟩ CTN.nil) ⟨166144, 170528, 809319167⟩ CTN.nil) ⟨166144, 171200, 796663325⟩ (CTN.node CTN.nil ⟨166144, 171648, 788363405⟩ CTN.nil)))) ⟨166144, 172032, 781335090⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166146, 169856, 823956127⟩ CTN.nil) ⟨166146, 170688, 807978385⟩ CTN.nil) ⟨166162, 170800, 819446311⟩ (CTN.node (CTN.node CTN.nil ⟨166165, 168436, 869226686⟩ CTN.nil) ⟨166165, 169268, 852230189⟩ CTN.nil)) ⟨166176, 168784, 871947779⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166176, 169216, 863060823⟩ CTN.nil) ⟨166176, 169792, 851386989⟩ CTN.nil) ⟨166176, 170560, 836127296⟩ (CTN.node CTN.nil ⟨166176, 171392, 819979896⟩ CTN.nil))) ⟨166176, 172032, 807823477⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166192, 172032, 821231318⟩ CTN.nil) ⟨166196, 168899, 887630111⟩ CTN.nil) ⟨166196, 169315, 878922243⟩ (CTN.node CTN.nil ⟨166196, 170002, 864774258⟩ CTN.nil)) ⟨166196, 170770, 849293623⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166196, 171602, 832911953⟩ CTN.nil) ⟨166196, 172032, 824600314⟩ CTN.nil) ⟨166208, 168400, 909272005⟩ (CTN.node CTN.nil ⟨166208, 169472, 886439905⟩ CTN.nil)))))) ⟨166208, 170944, 856243734⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166208, 171200, 851124265⟩ CTN.nil) ⟨166208, 172032, 834748172⟩ CTN.nil) ⟨166216, 170576, 870705491⟩ (CTN.node (CTN.node CTN.nil ⟨166216, 172032, 841547457⟩ CTN.nil) ⟨166224, 168416, 923762476⟩ CTN.nil)) ⟨166224, 168832, 914674212⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166224, 172032, 848373970⟩ CTN.nil) ⟨166232, 172032, 855227704⟩ CTN.nil) ⟨166240, 168048, 946983261⟩ (CTN.node CTN.nil ⟨166240, 168064, 946621999⟩ CTN.nil))) ⟨166240, 168480, 937289376⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166240, 168896, 928071525⟩ CTN.nil) ⟨166243, 168514, 939342437⟩ CTN.nil) ⟨166256, 168064, 961822580⟩ (CTN.node (CTN.node CTN.nil ⟨166258, 169264, 936639688⟩ CTN.nil) ⟨166262, 170036, 923361243⟩ CTN.nil)) ⟨166272, 168464, 967877361⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166272, 171488, 901271248⟩ CTN.nil) ⟨166272, 171776, 895231022⟩ CTN.nil) ⟨166272, 171968, 891232311⟩ (CTN.node CTN.nil ⟨166272, 172032, 889904373⟩ CTN.nil)))) ⟨166277, 169396, 951374059⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166288, 168896, 973130747⟩ CTN.nil) ⟨166290, 170992, 928009254⟩ CTN.nil) ⟨166304, 168112, 1006987312⟩ (CTN.node (CTN.node CTN.nil ⟨166304, 168496, 997821484⟩ CTN.nil) ⟨166304, 172032, 918134784⟩ CTN.nil)) ⟨166312, 172032, 925260241⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166320, 168512, 1012953193⟩ CTN.nil) ⟨166320, 168928, 1002993107⟩ CTN.nil) ⟨166324, 172032, 935999278⟩ (CTN.node CTN.nil ⟨166326, 170868, 963659951⟩ CTN.nil))) ⟨166336, 169952, 994097904⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166336, 172032, 946799311⟩ CTN.nil) ⟨166340, 172032, 950412871⟩ CTN.nil) ⟨166341, 168628, 1030644353⟩ (CTN.node (CTN.node CTN.nil ⟨166341, 169460, 1010514313⟩ CTN.nil) ⟨166352, 168544, 1043534876⟩ CTN.nil)) ⟨166354, 170992, 986803866⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166360, 172032, 968582237⟩ CTN.nil) ⟨166368, 168560, 1058984436⟩ CTN.nil) ⟨166368, 168976, 1048574696⟩ (CTN.node CTN.nil ⟨166368, 169408, 1037899657⟩ CTN.nil))))) ⟨166368, 169984, 1023876774⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166388, 169394, 1057825527⟩ CTN.nil) ⟨166388, 172032, 994303521⟩ CTN.nil) ⟨166400, 168208, 1100208595⟩ (CTN.node (CTN.node CTN.nil ⟨166400, 168640, 1088956889⟩ CTN.nil) ⟨166400, 169056, 1078257588⟩ CTN.nil)) ⟨166400, 169472, 1067689418⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166400, 170016, 1054064168⟩ CTN.nil) ⟨166400, 170048, 1053269473⟩ CTN.nil) ⟨166400, 170812, 1034516658⟩ (CTN.node CTN.nil ⟨166400, 170880, 1032867868⟩ CTN.nil))) ⟨166400, 171616, 1015230677⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166400, 171712, 1012958027⟩ CTN.nil) ⟨166400, 172032, 1005428326⟩ CTN.nil) ⟨166404, 169346, 1074840674⟩ (CTN.node (CTN.node CTN.nil ⟨166404, 170880, 1036691220⟩ CTN.nil) ⟨166404, 172032, 1009150106⟩ CTN.nil)) ⟨166416, 170764, 1051059309⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166420, 169107, 1096960024⟩ CTN.nil) ⟨166422, 170228, 1070253477⟩ CTN.nil) ⟨166432, 169040, 1110812531⟩ (CTN.node CTN.nil ⟨166432, 169472, 1099508149⟩ CTN.nil)))) ⟨166432, 170048, 1084658468⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166432, 170816, 1065246820⟩ CTN.nil) ⟨166448, 168640, 1137811049⟩ CTN.nil) ⟨166464, 168656, 1153890654⟩ (CTN.node (CTN.node CTN.nil ⟨166464, 169072, 1142554434⟩ CTN.nil) ⟨166464, 169504, 1130929220⟩ CTN.nil)) ⟨166464, 170048, 1116499651⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166464, 170080, 1115658043⟩ CTN.nil) ⟨166464, 170848, 1095695338⟩ CTN.nil) ⟨166464, 171200, 1086695096⟩ (CTN.node CTN.nil ⟨166464, 171968, 1067376886⟩ CTN.nil))) ⟨166464, 172032, 1065786491⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166468, 172032, 1069616173⟩ CTN.nil) ⟨166486, 171060, 1111895828⟩ CTN.nil) ⟨166496, 170880, 1126540471⟩ (CTN.node CTN.nil ⟨166496, 172032, 1096612389⟩ CTN.nil)) ⟨166504, 172032, 1104386127⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166508, 172032, 1108283078⟩ CTN.nil) ⟨166512, 169120, 1190941271⟩ CTN.nil) ⟨166514, 171888, 1117886207⟩ (CTN.node CTN.nil ⟨166516, 172032, 1116097138⟩ CTN.nil))))))))

noncomputable def tab9 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166532, 169506, 1200927010⟩ CTN.nil) ⟨166544, 170956, 1172778186⟩ CTN.nil) ⟨166544, 172032, 1143657861⟩ (CTN.node (CTN.node CTN.nil ⟨166560, 169728, 1223933552⟩ CTN.nil) ⟨166560, 172032, 1159554438⟩ CTN.nil)) ⟨166580, 172032, 1179575939⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166584, 172032, 1183600328⟩ CTN.nil) ⟨166592, 172032, 1191669187⟩ CTN.nil) ⟨166596, 170338, 1244084667⟩ (CTN.node CTN.nil ⟨166596, 171600, 1207822375⟩ CTN.nil))) ⟨166596, 172032, 1195713652⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166608, 169216, 1290480074⟩ CTN.nil) ⟨166608, 170350, 1256395910⟩ CTN.nil) ⟨166612, 169315, 1291798181⟩ (CTN.node (CTN.node CTN.nil ⟨166640, 168832, 1337599979⟩ CTN.nil) ⟨166648, 172032, 1248899872⟩ CTN.nil)) ⟨166656, 168480, 1366815887⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166656, 168896, 1353373821⟩ CTN.nil) ⟨166656, 169696, 1327985083⟩ CTN.nil) ⟨166656, 169728, 1326981976⟩ (CTN.node CTN.nil ⟨166656, 170272, 1310073213⟩ CTN.nil)))) ⟨166656, 172032, 1257182497⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166675, 169362, 1359569403⟩ CTN.nil) ⟨166675, 169778, 1346268072⟩ CTN.nil) ⟨166688, 168496, 1402591460⟩ (CTN.node (CTN.node CTN.nil ⟨166696, 172032, 1298995399⟩ CTN.nil) ⟨166708, 172032, 1311669048⟩ CTN.nil)) ⟨166720, 169760, 1396878347⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166720, 169888, 1392665325⟩ CTN.nil) ⟨166720, 171104, 1353423455⟩ CTN.nil) ⟨166720, 172032, 1324402519⟩ (CTN.node CTN.nil ⟨166736, 168928, 1443018170⟩ CTN.nil))) ⟨166738, 171312, 1366388081⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166738, 172032, 1343614804⟩ CTN.nil) ⟨166752, 169792, 1431918568⟩ CTN.nil) ⟨166752, 170368, 1412615711⟩ (CTN.node (CTN.node CTN.nil ⟨166752, 171136, 1387381887⟩ CTN.nil) ⟨166752, 171968, 1360678006⟩ CTN.nil)) ⟨166764, 172032, 1371603053⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166772, 170546, 1429101938⟩ CTN.nil) ⟨166776, 172032, 1384615138⟩ CTN.nil) ⟨166784, 168976, 1497086952⟩ (CTN.node CTN.nil ⟨166784, 172032, 1393322965⟩ CTN.nil))))) ⟨166788, 171856, 1403431755⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166800, 169408, 1500452387⟩ CTN.nil) ⟨166816, 169056, 1531887832⟩ CTN.nil) ⟨166816, 169472, 1516873562⟩ (CTN.node (CTN.node CTN.nil ⟨166816, 171200, 1456441535⟩ CTN.nil) ⟨166828, 172032, 1441688754⟩ CTN.nil)) ⟨166834, 169872, 1523572103⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166836, 170610, 1499629590⟩ CTN.nil) ⟨166836, 171378, 1472879133⟩ CTN.nil) ⟨166836, 172032, 1450568379⟩ (CTN.node CTN.nil ⟨166848, 172032, 1463937278⟩ CTN.nil))) ⟨166864, 169472, 1573618499⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166880, 169072, 1607912761⟩ CTN.nil) ⟨166883, 170002, 1576506677⟩ CTN.nil) ⟨166892, 172032, 1513463656⟩ (CTN.node (CTN.node CTN.nil ⟨166896, 169504, 1610788659⟩ CTN.nil) ⟨166896, 172032, 1518005516⟩ CTN.nil)) ⟨166900, 172032, 1522553945⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166904, 172032, 1527108941⟩ CTN.nil) ⟨166912, 170528, 1591260121⟩ CTN.nil) ⟨166912, 170560, 1590064029⟩ (CTN.node CTN.nil ⟨166912, 171392, 1559356504⟩ CTN.nil)))) ⟨166912, 171648, 1550057503⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166912, 172032, 1536238631⟩ CTN.nil) ⟨166944, 169984, 1650356323⟩ CTN.nil) ⟨166944, 170560, 1628133845⟩ (CTN.node (CTN.node CTN.nil ⟨166952, 172032, 1582280537⟩ CTN.nil) ⟨166960, 172032, 1591567510⟩ CTN.nil)) ⟨166964, 170770, 1644020903⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166968, 170816, 1647041605⟩ CTN.nil) ⟨166972, 172032, 1605547021⟩ CTN.nil) ⟨166976, 170048, 1686838787⟩ (CTN.node CTN.nil ⟨166976, 172032, 1610219932⟩ CTN.nil))) ⟨166978, 170688, 1664048009⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨166994, 170736, 1681521542⟩ CTN.nil) ⟨167008, 170048, 1726247115⟩ CTN.nil) ⟨167008, 171392, 1672635536⟩ (CTN.node CTN.nil ⟨167024, 172032, 1666803952⟩ CTN.nil)) ⟨167028, 171602, 1688410322⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167028, 172032, 1671561655⟩ CTN.nil) ⟨167040, 170080, 1764761232⟩ CTN.nil) ⟨167040, 172032, 1685873815⟩ (CTN.node CTN.nil ⟨167060, 171408, 1734938876⟩ CTN.nil)))))) ⟨167084, 172032, 1738852136⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167086, 171692, 1755138500⟩ CTN.nil) ⟨167091, 169778, 1842191082⟩ CTN.nil) ⟨167104, 172032, 1763192653⟩ (CTN.node (CTN.node CTN.nil ⟨167112, 172032, 1772974185⟩ CTN.nil) ⟨167124, 172032, 1787694995⟩ CTN.nil)) ⟨167136, 170304, 1876891573⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167136, 172032, 1802473973⟩ CTN.nil) ⟨167138, 171712, 1818460090⟩ CTN.nil) ⟨167152, 172032, 1822269667⟩ (CTN.node CTN.nil ⟨167168, 172032, 1842168548⟩ CTN.nil))) ⟨167172, 171584, 1866562487⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167200, 170816, 1936550252⟩ CTN.nil) ⟨167200, 172032, 1882275352⟩ CTN.nil) ⟨167212, 172032, 1897421469⟩ (CTN.node (CTN.node CTN.nil ⟨167216, 172032, 1902483014⟩ CTN.nil) ⟨167232, 170848, 1976752112⟩ CTN.nil)) ⟨167232, 170880, 1975269053⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167232, 171712, 1937193231⟩ CTN.nil) ⟨167232, 171968, 1925662582⟩ CTN.nil) ⟨167232, 172032, 1922793340⟩ (CTN.node CTN.nil ⟨167248, 172032, 1943206196⟩ CTN.nil)))) ⟨167264, 172032, 1963721449⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167280, 172032, 1984338961⟩ CTN.nil) ⟨167296, 170880, 2059779446⟩ CTN.nil) ⟨167296, 171680, 2021583900⟩ (CTN.node (CTN.node CTN.nil ⟨167296, 172032, 2005058599⟩ CTN.nil) ⟨167300, 172032, 2010254450⟩ CTN.nil)) ⟨167328, 172032, 2046803700⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167346, 172032, 2070464177⟩ CTN.nil) ⟨167356, 172032, 2083664436⟩ CTN.nil) ⟨167360, 172032, 2088955639⟩ (CTN.node CTN.nil ⟨167408, 172032, 2152943896⟩ CTN.nil))) ⟨167424, 171900, 2181174558⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167424, 172032, 2174475502⟩ CTN.nil) ⟨167428, 172032, 2179874167⟩ CTN.nil) ⟨167436, 171784, 2203391833⟩ (CTN.node (CTN.node CTN.nil ⟨167436, 172032, 2190690399⟩ CTN.nil) ⟨167488, 172032, 2261608976⟩ CTN.nil)) ⟨167504, 172032, 2283643367⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167520, 171136, 2354537999⟩ CTN.nil) ⟨167536, 172032, 2328012323⟩ CTN.nil) ⟨167540, 172032, 2333586536⟩ (CTN.node CTN.nil ⟨167552, 172032, 2350346583⟩ CTN.nil))))) ⟨167556, 172032, 2355945725⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167570, 172032, 2375591733⟩ CTN.nil) ⟨167584, 171968, 2398888254⟩ CTN.nil) ⟨167584, 172032, 2395313904⟩ (CTN.node (CTN.node CTN.nil ⟨167604, 171378, 2460897316⟩ CTN.nil) ⟨167616, 172032, 2440678588⟩ CTN.nil)) ⟨167664, 172032, 2509467912⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167668, 172032, 2515240450⟩ CTN.nil) ⟨167680, 172032, 2532594994⟩ CTN.nil) ⟨167732, 172032, 2608436646⟩ (CTN.node CTN.nil ⟨167736, 172032, 2614313502⟩ CTN.nil))) ⟨167744, 172032, 2626085552⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167760, 172032, 2649702926⟩ CTN.nil) ⟨167776, 170524, 2769428566⟩ CTN.nil) ⟨167776, 172032, 2673417863⟩ (CTN.node (CTN.node CTN.nil ⟨167796, 172032, 2703198475⟩ CTN.nil) ⟨167808, 172032, 2721139749⟩ CTN.nil)) ⟨167860, 172032, 2799515217⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨167872, 172032, 2817746826⟩ CTN.nil) ⟨167876, 172032, 2823836078⟩ CTN.nil) ⟨167900, 170584, 2959052590⟩ (CTN.node CTN.nil ⟨167920, 172032, 2891214590⟩ CTN.nil)))) ⟨167936, 172032, 2915895760⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨167968, 172032, 2965544913⟩ CTN.nil) ⟨167976, 172032, 2978016823⟩ CTN.nil) ⟨167988, 172032, 2996769313⟩ (CTN.node (CTN.node CTN.nil ⟨168000, 172032, 3015575285⟩ CTN.nil) ⟨168052, 172032, 3097683969⟩ CTN.nil)) ⟨168060, 172032, 3110404683⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨168064, 172032, 3116773877⟩ CTN.nil) ⟨168080, 172032, 3142309504⟩ CTN.nil) ⟨168128, 172032, 3219479764⟩ (CTN.node CTN.nil ⟨168132, 172032, 3225948656⟩ CTN.nil))) ⟨168178, 172032, 3300759773⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨168184, 172032, 3310574428⟩ CTN.nil) ⟨168192, 172032, 3323680930⟩ CTN.nil) ⟨168208, 172032, 3349963424⟩ (CTN.node CTN.nil ⟨168224, 172032, 3376338416⟩ CTN.nil)) ⟨168244, 172032, 3409436929⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨168256, 172032, 3429365103⟩ CTN.nil) ⟨168312, 172032, 3523045458⟩ CTN.nil) ⟨168320, 172032, 3536519776⟩ (CTN.node CTN.nil ⟨168384, 172032, 3645132190⟩ CTN.nil))))))) ⟨168444, 172032, 3748268700⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨168448, 172032, 3755189350⟩ CTN.nil) ⟨168496, 172032, 3838672377⟩ CTN.nil) ⟨168512, 172032, 3866678014⟩ (CTN.node (CTN.node CTN.nil ⟨168560, 172032, 3951225841⟩ CTN.nil) ⟨168576, 172032, 3979584708⟩ CTN.nil)) ⟨168640, 172032, 4093895715⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨168688, 172032, 4180542169⟩ CTN.nil) ⟨168696, 172032, 4195058863⟩ CTN.nil) ⟨168816, 172032, 4415377260⟩ (CTN.node CTN.nil ⟨168960, 172032, 4686019082⟩ CTN.nil))) ⟨169008, 172032, 4777723307⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨169024, 172032, 4808454914⟩ CTN.nil) ⟨169072, 172032, 4901136959⟩ CTN.nil) ⟨169088, 172032, 4932192574⟩ (CTN.node (CTN.node CTN.nil ⟨169100, 172032, 4955537057⟩ CTN.nil) ⟨169152, 172032, 5057216511⟩ CTN.nil)) ⟨169192, 172032, 5136002667⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨169216, 172032, 5183510966⟩ CTN.nil) ⟨169264, 172032, 5279055973⟩ CTN.nil) ⟨169292, 172032, 5335113738⟩ (CTN.node CTN.nil ⟨169472, 172032, 5701071046⟩ CTN.nil)))) ⟨169576, 172032, 5916821880⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨169580, 172032, 5925181669⟩ CTN.nil) ⟨169600, 172032, 5967048477⟩ CTN.nil) ⟨169656, 172032, 6084873485⟩ (CTN.node (CTN.node CTN.nil ⟨169728, 172032, 6237642433⟩ CTN.nil) ⟨169744, 172032, 6271784321⟩ CTN.nil)) ⟨169836, 172032, 6469443565⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨169856, 172032, 6512712553⟩ CTN.nil) ⟨169872, 172032, 6547403934⟩ CTN.nil) ⟨169900, 172032, 6608275905⟩ (CTN.node CTN.nil ⟨169964, 172032, 6748178940⟩ CTN.nil))) ⟨170044, 172032, 6924535414⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨170092, 172032, 7031123470⟩ CTN.nil) ⟨170120, 172032, 7093564025⟩ CTN.nil) ⟨170156, 172032, 7174127681⟩ (CTN.node (CTN.node CTN.nil ⟨170224, 172032, 7327160686⟩ CTN.nil) ⟨170284, 172032, 7463105406⟩ CTN.nil)) ⟨170300, 172032, 7499500159⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨170412, 172032, 7755914000⟩ CTN.nil) ⟨170480, 172032, 7912973200⟩ CTN.nil) ⟨170524, 172032, 8015141234⟩ (CTN.node CTN.nil ⟨170584, 172032, 8155133328⟩ CTN.nil))))) ⟨170688, 172032, 8399577859⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨170736, 172032, 8513144844⟩ CTN.nil) ⟨170764, 172032, 8579604990⟩ CTN.nil) ⟨170808, 172032, 8684354096⟩ (CTN.node (CTN.node CTN.nil ⟨170992, 172032, 9126382320⟩ CTN.nil) ⟨171132, 172032, 9466795949⟩ CTN.nil)) ⟨171952, 172032, 11519220240⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172036, 11722665085⟩ CTN.nil) ⟨172032, 172076, 11711748847⟩ CTN.nil) ⟨172032, 172080, 11710657922⟩ (CTN.node CTN.nil ⟨172032, 172096, 11706295495⟩ CTN.nil))) ⟨172032, 172144, 11693220399⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172160, 11688866092⟩ CTN.nil) ⟨172032, 172210, 11675271945⟩ CTN.nil) ⟨172032, 172224, 11671469127⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 172240, 11667124946⟩ CTN.nil) ⟨172032, 172272, 11658442647⟩ CTN.nil)) ⟨172032, 172276, 11657357928⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172288, 11654104527⟩ CTN.nil) ⟨172032, 172292, 11653020313⟩ CTN.nil) ⟨172032, 172328, 11643268056⟩ (CTN.node CTN.nil ⟨172032, 172336, 11641102274⟩ CTN.nil)))) ⟨172032, 172352, 11636772221⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172400, 11623794141⟩ CTN.nil) ⟨172032, 172416, 11619472136⟩ CTN.nil) ⟨172032, 172428, 11616231951⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 172434, 11614612283⟩ CTN.nil) ⟨172032, 172464, 11606518174⟩ CTN.nil)) ⟨172032, 172468, 11605439493⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172480, 11602204200⟩ CTN.nil) ⟨172032, 172532, 11588197625⟩ CTN.nil) ⟨172032, 172544, 11584968342⟩ (CTN.node CTN.nil ⟨172032, 172584, 11574212188⟩ CTN.nil))) ⟨172032, 172608, 11567764490⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172620, 11564542325⟩ CTN.nil) ⟨172032, 172656, 11554882562⟩ CTN.nil) ⟨172032, 172660, 11553809878⟩ (CTN.node CTN.nil ⟨172032, 172672, 11550592573⟩ CTN.nil)) ⟨172032, 172712, 11539876309⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172720, 11537734549⟩ CTN.nil) ⟨172032, 172724, 11536663855⟩ CTN.nil) ⟨172032, 172736, 11533452519⟩ (CTN.node CTN.nil ⟨172032, 172796, 11517412594⟩ CTN.nil)))))) ⟨172032, 172800, 11516344258⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 172852, 11502467156⟩ CTN.nil) ⟨172032, 172896, 11490741322⟩ CTN.nil) ⟨172032, 172928, 11482222831⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 173036, 11453531158⟩ CTN.nil) ⟨172032, 173056, 11448227727⟩ CTN.nil)) ⟨172032, 173120, 11431277372⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173136, 11427044687⟩ CTN.nil) ⟨172032, 173152, 11422813962⟩ CTN.nil) ⟨172032, 173184, 11414358387⟩ (CTN.node CTN.nil ⟨172032, 173200, 11410133534⟩ CTN.nil))) ⟨172032, 173248, 11397470704⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173272, 11391145878⟩ CTN.nil) ⟨172032, 173312, 11380614252⟩ CTN.nil) ⟨172032, 173352, 11370094798⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 173372, 11364839631⟩ CTN.nil) ⟨172032, 173376, 11363788962⟩ CTN.nil)) ⟨172032, 173420, 11352239616⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173448, 11344897674⟩ CTN.nil) ⟨172032, 173496, 11332325296⟩ CTN.nil) ⟨172032, 173552, 11317679533⟩ (CTN.node CTN.nil ⟨172032, 173568, 11313499377⟩ CTN.nil)))) ⟨172032, 173608, 11303057431⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173632, 11296798048⟩ CTN.nil) ⟨172032, 173648, 11292627533⟩ CTN.nil) ⟨172032, 173680, 11284292279⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 173740, 11268684402⟩ CTN.nil) ⟨172032, 173760, 11263487775⟩ CTN.nil)) ⟨172032, 173808, 11251028094⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173824, 11246878697⟩ CTN.nil) ⟨172032, 173872, 11234441982⟩ CTN.nil) ⟨172032, 173888, 11230300232⟩ (CTN.node CTN.nil ⟨172032, 173904, 11226160392⟩ CTN.nil))) ⟨172032, 173936, 11217886434⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 173940, 11216852725⟩ CTN.nil) ⟨172032, 173952, 11213752314⟩ CTN.nil) ⟨172032, 174016, 11197234876⟩ (CTN.node CTN.nil ⟨172032, 174064, 11184866758⟩ CTN.nil)) ⟨172032, 174080, 11180747848⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174092, 11177659911⟩ CTN.nil) ⟨172032, 174132, 11167374485⟩ CTN.nil) ⟨172032, 174144, 11164291166⟩ (CTN.node CTN.nil ⟨172032, 174192, 11151968527⟩ CTN.nil))))) ⟨172032, 174196, 11150942408⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174208, 11147864760⟩ CTN.nil) ⟨172032, 174272, 11131468566⟩ CTN.nil) ⟨172032, 174320, 11119191205⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 174336, 11115102515⟩ CTN.nil) ⟨172032, 174388, 11101827249⟩ CTN.nil)) ⟨172032, 174448, 11086534260⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174460, 11083478824⟩ CTN.nil) ⟨172032, 174464, 11082460580⟩ CTN.nil) ⟨172032, 174528, 11066184563⟩ (CTN.node CTN.nil ⟨172032, 174572, 11055012137⟩ CTN.nil))) ⟨172032, 174580, 11052982302⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174592, 11049938424⟩ CTN.nil) ⟨172032, 174640, 11037773389⟩ CTN.nil) ⟨172032, 174648, 11035747512⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 174700, 11022590636⟩ CTN.nil) ⟨172032, 174708, 11020568242⟩ CTN.nil)) ⟨172032, 174720, 11017535522⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174764, 11006424471⟩ CTN.nil) ⟨172032, 174772, 11004405786⟩ CTN.nil) ⟨172032, 174780, 11002387564⟩ (CTN.node CTN.nil ⟨172032, 174784, 11001378626⟩ CTN.nil)))) ⟨172032, 174848, 10985251347⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 174892, 10974180989⟩ CTN.nil) ⟨172032, 174900, 10972169696⟩ CTN.nil) ⟨172032, 174912, 10969153620⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 174960, 10957099678⟩ CTN.nil) ⟨172032, 174976, 10953085379⟩ CTN.nil)) ⟨172032, 175040, 10937046560⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 175084, 10926036905⟩ CTN.nil) ⟨172032, 175104, 10921037098⟩ CTN.nil) ⟨172032, 175216, 10893090986⟩ (CTN.node CTN.nil ⟨172032, 175360, 10857291534⟩ CTN.nil))) ⟨172032, 175368, 10855306993⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 175408, 10845391085⟩ CTN.nil) ⟨172032, 175424, 10841427894⟩ CTN.nil) ⟨172032, 175440, 10837466513⟩ (CTN.node CTN.nil ⟨172032, 175472, 10829549181⟩ CTN.nil)) ⟨172032, 175488, 10825593226⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 175616, 10794010555⟩ CTN.nil) ⟨172032, 175664, 10782196763⟩ CTN.nil) ⟨172032, 175744, 10762543015⟩ (CTN.node CTN.nil ⟨172032, 175860, 10734124582⟩ CTN.nil))))))))

noncomputable def tab10 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 175952, 10711652519⟩ CTN.nil) ⟨172032, 175968, 10707750341⟩ CTN.nil) ⟨172032, 176000, 10699951317⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 176052, 10687293045⟩ CTN.nil) ⟨172032, 176056, 10686320108⟩ CTN.nil)) ⟨172032, 176064, 10684374565⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 176104, 10674653494⟩ CTN.nil) ⟨172032, 176128, 10668826159⟩ CTN.nil) ⟨172032, 176192, 10653306036⟩ (CTN.node CTN.nil ⟨172032, 176224, 10645556561⟩ CTN.nil))) ⟨172032, 176236, 10642652325⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 176240, 10641684467⟩ CTN.nil) ⟨172032, 176256, 10637814134⟩ CTN.nil) ⟨172032, 176384, 10606914747⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 176444, 10592469296⟩ CTN.nil) ⟨172032, 176448, 10591507141⟩ CTN.nil)) ⟨172032, 176488, 10581891597⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 176492, 10580930643⟩ CTN.nil) ⟨172032, 176496, 10579969798⟩ CTN.nil) ⟨172032, 176512, 10576127510⟩ (CTN.node CTN.nil ⟨172032, 176556, 10565570210⟩ CTN.nil)))) ⟨172032, 176576, 10560775794⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 176624, 10549280290⟩ CTN.nil) ⟨172032, 176640, 10545451932⟩ CTN.nil) ⟨172032, 176700, 10531111056⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 176748, 10519655909⟩ CTN.nil) ⟨172032, 176768, 10514887529⟩ CTN.nil)) ⟨172032, 176776, 10512980935⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 176812, 10504406605⟩ CTN.nil) ⟨172032, 176880, 10488234494⟩ CTN.nil) ⟨172032, 176896, 10484433817⟩ (CTN.node CTN.nil ⟨172032, 176944, 10473042115⟩ CTN.nil))) ⟨172032, 177024, 10454090316⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 177068, 10443685104⟩ CTN.nil) ⟨172032, 177088, 10438959744⟩ CTN.nil) ⟨172032, 177136, 10427629782⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 177152, 10423856546⟩ CTN.nil) ⟨172032, 177208, 10410663655⟩ CTN.nil)) ⟨172032, 177264, 10397491637⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 177280, 10393732032⟩ CTN.nil) ⟨172032, 177392, 10367462333⟩ CTN.nil) ⟨172032, 177520, 10337541399⟩ (CTN.node CTN.nil ⟨172032, 177524, 10336608111⟩ CTN.nil))))) ⟨172032, 177532, 10334741851⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 177644, 10308658394⟩ CTN.nil) ⟨172032, 177648, 10307728366⟩ CTN.nil) ⟨172032, 177664, 10304009300⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 177716, 10291933918⟩ CTN.nil) ⟨172032, 177760, 10281730106⟩ CTN.nil)) ⟨172032, 177900, 10249347478⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 177920, 10244731805⟩ CTN.nil) ⟨172032, 177964, 10234586470⟩ CTN.nil) ⟨172032, 178112, 10200553317⟩ (CTN.node CTN.nil ⟨172032, 178176, 10185880112⟩ CTN.nil))) ⟨172032, 178220, 10175807591⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 178304, 10156612794⟩ CTN.nil) ⟨172032, 178560, 10098392940⟩ CTN.nil) ⟨172032, 178688, 10069439501⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 178696, 10067633360⟩ CTN.nil) ⟨172032, 178736, 10058608728⟩ CTN.nil)) ⟨172032, 178864, 10029797800⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 178920, 10017225470⟩ CTN.nil) ⟨172032, 178944, 10011843362⟩ CTN.nil) ⟨172032, 179072, 9983199771⟩ (CTN.node CTN.nil ⟨172032, 179128, 9970700425⟩ CTN.nil)))) ⟨172032, 179176, 9960002271⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 179200, 9954658577⟩ CTN.nil) ⟨172032, 179296, 9933319616⟩ CTN.nil) ⟨172032, 179304, 9931543952⟩ (CTN.node (CTN.node CTN.nil ⟨172032, 179308, 9930656269⟩ CTN.nil) ⟨172032, 179328, 9926219341⟩ CTN.nil)) ⟨172032, 179384, 9913809125⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 179432, 9903187235⟩ CTN.nil) ⟨172032, 179456, 9897881626⟩ CTN.nil) ⟨172032, 179560, 9874931686⟩ (CTN.node CTN.nil ⟨172032, 179564, 9874050325⟩ CTN.nil))) ⟨172032, 179584, 9869644998⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 179628, 9859961925⟩ CTN.nil) ⟨172032, 179776, 9827478646⟩ CTN.nil) ⟨172032, 179816, 9818722360⟩ (CTN.node CTN.nil ⟨172032, 179840, 9813473271⟩ CTN.nil)) ⟨172032, 179884, 9803859051⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨172032, 179952, 9789023866⟩ CTN.nil) ⟨172032, 180096, 9757700727⟩ CTN.nil) ⟨172032, 180144, 9747287538⟩ (CTN.node CTN.nil ⟨172032, 180208, 9733424893⟩ CTN.nil)))))) ⟨172032, 180224, 9729963084⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨172040, 180224, 9746965609⟩ CTN.nil) ⟨172776, 180224, 11326866252⟩ CTN.nil) ⟨173160, 180224, 12157431795⟩ (CTN.node (CTN.node CTN.nil ⟨173272, 178768, 12809255123⟩ CTN.nil) ⟨175488, 180224, 17009071115⟩ CTN.nil)) ⟨175952, 180224, 17886733706⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨176304, 180224, 18521822193⟩ CTN.nil) ⟨177536, 180224, 20491807052⟩ CTN.nil) ⟨178768, 180224, 21984511907⟩ (CTN.node CTN.nil ⟨179152, 180224, 22337328602⟩ CTN.nil))) ⟨179920, 180224, 22868790503⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 180272, 22987588925⟩ CTN.nil) ⟨180224, 180280, 22983326253⟩ CTN.nil) ⟨180224, 180288, 22979037516⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 180464, 22878121236⟩ CTN.nil) ⟨180224, 180480, 22868327409⟩ CTN.nil)) ⟨180224, 180608, 22786289547⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 180720, 22709166408⟩ CTN.nil) ⟨180224, 180832, 22627108834⟩ CTN.nil) ⟨180224, 180976, 22514435475⟩ (CTN.node CTN.nil ⟨180224, 180992, 22501422485⟩ CTN.nil)))) ⟨180224, 181248, 22279969817⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 181376, 22160024998⟩ CTN.nil) ⟨180224, 181992, 21500116735⟩ CTN.nil) ⟨180224, 182016, 21471725482⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 182144, 21317030601⟩ CTN.nil) ⟨180224, 182248, 21187331923⟩ CTN.nil)) ⟨180224, 182272, 21156897754⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 182376, 21022860560⟩ CTN.nil) ⟨180224, 182400, 20991435527⟩ CTN.nil) ⟨180224, 182456, 20917398287⟩ (CTN.node CTN.nil ⟨180224, 182528, 20820755150⟩ CTN.nil))) ⟨180224, 182632, 20678313545⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 182656, 20644970417⟩ CTN.nil) ⟨180224, 182760, 20498467029⟩ CTN.nil) ⟨180224, 182848, 20371977659⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 182912, 20278555381⟩ CTN.nil) ⟨180224, 183144, 19930060922⟩ CTN.nil)) ⟨180224, 183280, 19718814380⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 183296, 19693633166⟩ CTN.nil) ⟨180224, 183536, 19307857762⟩ CTN.nil) ⟨180224, 183552, 19281613785⟩ (CTN.node CTN.nil ⟨180224, 183608, 19189255598⟩ CTN.nil))))) ⟨180224, 183680, 19069370752⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 183808, 18853148956⟩ CTN.nil) ⟨180224, 183936, 18633083148⟩ CTN.nil) ⟨180224, 184192, 18181966454⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 184384, 17834563394⟩ CTN.nil) ⟨180224, 184544, 17539508005⟩ CTN.nil)) ⟨180224, 184704, 17239701561⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 184800, 17057654073⟩ CTN.nil) ⟨180224, 184832, 16996624543⟩ CTN.nil) ⟨180224, 185056, 16564793006⟩ (CTN.node CTN.nil ⟨180224, 185312, 16062093940⟩ CTN.nil))) ⟨180224, 185320, 16046238927⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 185344, 15998623519⟩ CTN.nil) ⟨180224, 185472, 15743435378⟩ CTN.nil) ⟨180224, 185704, 15275966012⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 185776, 15129706508⟩ CTN.nil) ⟨180224, 185856, 14966594275⟩ CTN.nil)) ⟨180224, 186088, 14490317855⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 186368, 13910072854⟩ CTN.nil) ⟨180224, 186472, 13693333712⟩ CTN.nil) ⟨180224, 186624, 13375620595⟩ (CTN.node CTN.nil ⟨180224, 186688, 13241564962⟩ CTN.nil)))) ⟨180224, 186976, 12636852777⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 187008, 12569561193⟩ CTN.nil) ⟨180224, 187056, 12468602409⟩ CTN.nil) ⟨180224, 187136, 12300299849⟩ (CTN.node (CTN.node CTN.nil ⟨180224, 187488, 11560055244⟩ CTN.nil) ⟨180224, 187824, 10855942113⟩ CTN.nil)) ⟨180224, 187904, 10688945415⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨180224, 188416, 9629227507⟩ CTN.nil) ⟨180736, 188416, 9730938999⟩ CTN.nil) ⟨181800, 188416, 9943520182⟩ (CTN.node CTN.nil ⟨182224, 188416, 10028506045⟩ CTN.nil))) ⟨182688, 188416, 10121569207⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨183032, 188416, 10190553534⟩ CTN.nil) ⟨184224, 188416, 10428970411⟩ CTN.nil) ⟨184520, 188416, 10487903100⟩ (CTN.node CTN.nil ⟨185416, 188416, 10665250754⟩ CTN.nil)) ⟨185552, 188416, 10692004442⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨185680, 188416, 10717138745⟩ CTN.nil) ⟨185760, 188416, 10732824357⟩ CTN.nil) ⟨186064, 188416, 10792257141⟩ (CTN.node CTN.nil ⟨186144, 188416, 10807849829⟩ CTN.nil))))))) ⟨186224, 188416, 10823421840⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨186320, 188416, 10842080322⟩ CTN.nil) ⟨186360, 188416, 10849845525⟩ CTN.nil) ⟨186448, 188416, 10866909622⟩ (CTN.node (CTN.node CTN.nil ⟨186688, 188416, 10913308617⟩ CTN.nil) ⟨187296, 188416, 11029869377⟩ CTN.nil)) ⟨187680, 188416, 11102692862⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨187728, 188416, 11111749530⟩ CTN.nil) ⟨188056, 188416, 11173348504⟩ CTN.nil) ⟨188236, 188416, 11206932078⟩ (CTN.node CTN.nil ⟨188364, 188416, 11230715130⟩ CTN.nil))) ⟨188416, 188648, 10703590170⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 189032, 9827983555⟩ CTN.nil) ⟨188416, 189104, 9665847445⟩ CTN.nil) ⟨188416, 189688, 8378970143⟩ (CTN.node (CTN.node CTN.nil ⟨188416, 189760, 8224162898⟩ CTN.nil) ⟨188416, 189952, 7815921159⟩ CTN.nil)) ⟨188416, 190464, 6762594557⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 191232, 5292329246⟩ CTN.nil) ⟨188416, 191456, 4891156123⟩ CTN.nil) ⟨188416, 191512, 4792942938⟩ (CTN.node CTN.nil ⟨188416, 191856, 4208503414⟩ CTN.nil)))) ⟨188416, 191968, 4025402962⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 192056, 3884075859⟩ CTN.nil) ⟨188416, 192236, 3602065857⟩ CTN.nil) ⟨188416, 192284, 3528487292⟩ (CTN.node (CTN.node CTN.nil ⟨188416, 192880, 2673581588⟩ CTN.nil) ⟨188416, 193176, 2290591866⟩ CTN.nil)) ⟨188416, 193792, 1585530720⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 193800, 1577206465⟩ CTN.nil) ⟨188416, 193884, 1491105504⟩ CTN.nil) ⟨188416, 194016, 1360628775⟩ (CTN.node CTN.nil ⟨188416, 194248, 1145674799⟩ CTN.nil))) ⟨188416, 194528, 910796146⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 194560, 885669736⟩ CTN.nil) ⟨188416, 194600, 854758010⟩ CTN.nil) ⟨188416, 194696, 782821429⟩ (CTN.node (CTN.node CTN.nil ⟨188416, 194780, 722486608⟩ CTN.nil) ⟨188416, 194844, 678153243⟩ CTN.nil)) ⟨188416, 194892, 645832146⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 194920, 627345943⟩ CTN.nil) ⟨188416, 194968, 596285838⟩ CTN.nil) ⟨188416, 195184, 466370894⟩ (CTN.node CTN.nil ⟨188416, 195552, 282126683⟩ CTN.nil))))) ⟨188416, 195724, 211987719⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨188416, 195848, 167705408⟩ CTN.nil) ⟨188416, 195912, 146902746⟩ CTN.nil) ⟨188416, 196368, 38832875⟩ (CTN.node (CTN.node CTN.nil ⟨188416, 196444, 27610655⟩ CTN.nil) ⟨188416, 196512, 19198372⟩ CTN.nil)) ⟨188416, 196608, 9929527⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨188444, 195864, 162627172⟩ CTN.nil) ⟨188528, 192940, 2600124669⟩ CTN.nil) ⟨188528, 194604, 854605634⟩ (CTN.node CTN.nil ⟨188680, 196608, 10431959⟩ CTN.nil))) ⟨188696, 196608, 10462381⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨188808, 196608, 10675179⟩ CTN.nil) ⟨188828, 194968, 604638393⟩ CTN.nil) ⟨188908, 193256, 2216727955⟩ (CTN.node (CTN.node CTN.nil ⟨188908, 194920, 637638845⟩ CTN.nil) ⟨188960, 194908, 646694258⟩ CTN.nil)) ⟨189068, 195144, 500738748⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨189088, 196508, 21474097⟩ CTN.nil) ⟨189160, 196484, 24641540⟩ CTN.nil) ⟨189196, 195208, 465995707⟩ (CTN.node CTN.nil ⟨189196, 196608, 11409088⟩ CTN.nil)))) ⟨189552, 195564, 290664070⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨189760, 192508, 3282502877⟩ CTN.nil) ⟨189760, 195256, 447917952⟩ CTN.nil) ⟨189900, 195912, 158980535⟩ (CTN.node (CTN.node CTN.nil ⟨190056, 195124, 529364540⟩ CTN.nil) ⟨190092, 196040, 120872767⟩ CTN.nil)) ⟨190108, 195992, 135158220⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨190192, 194604, 895633242⟩ CTN.nil) ⟨190428, 194904, 678441207⟩ CTN.nil) ⟨190428, 196608, 13665979⟩ (CTN.node CTN.nil ⟨190496, 195070, 570035870⟩ CTN.nil))) ⟨190572, 194920, 670112585⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨190624, 196572, 17720917⟩ CTN.nil) ⟨190732, 195370, 399554016⟩ CTN.nil) ⟨190732, 195434, 366485944⟩ (CTN.node CTN.nil ⟨190732, 196608, 14195591⟩ CTN.nil)) ⟨190840, 196608, 14380346⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨190924, 196608, 14522728⟩ CTN.nil) ⟨191276, 195688, 254399069⟩ CTN.nil) ⟨191512, 195924, 166375311⟩ (CTN.node CTN.nil ⟨191564, 196234, 78055014⟩ CTN.nil)))))) ⟨191592, 195940, 161481021⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨191628, 196234, 78308182⟩ CTN.nil) ⟨191644, 196186, 89925937⟩ CTN.nil) ⟨191870, 196444, 37795360⟩ (CTN.node (CTN.node CTN.nil ⟨192056, 194740, 827990647⟩ CTN.nil) ⟨192106, 195880, 185550021⟩ CTN.nil)) ⟨192106, 196608, 16383451⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨192156, 196608, 16455500⟩ CTN.nil) ⟨192236, 196584, 19223037⟩ CTN.nil) ⟨192508, 195256, 484592607⟩ (CTN.node CTN.nil ⟨192584, 195590, 309062020⟩ CTN.nil))) ⟨192584, 196326, 61348390⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨192584, 196422, 43157808⟩ CTN.nil) ⟨192680, 196608, 17173262⟩ CTN.nil) ⟨192940, 195978, 156223418⟩ (CTN.node (CTN.node CTN.nil ⟨192970, 196608, 17539522⟩ CTN.nil) ⟨192986, 196608, 17559055⟩ CTN.nil)) ⟨193176, 196278, 73392287⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨193240, 196310, 66488771⟩ CTN.nil) ⟨193256, 196262, 77287526⟩ CTN.nil) ⟨193416, 196422, 44899262⟩ (CTN.node CTN.nil ⟨193448, 196422, 44959736⟩ CTN.nil)))) ⟨193770, 196608, 18424759⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨193834, 196608, 18487203⟩ CTN.nil) ⟨193926, 196608, 18574707⟩ CTN.nil) ⟨194312, 196608, 18912217⟩ (CTN.node (CTN.node CTN.nil ⟨196608, 196632, 17101590⟩ CTN.nil) ⟨196608, 196663, 13845390⟩ CTN.nil)) ⟨196608, 196696, 10757353⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196608, 196736, 7536840⟩ CTN.nil) ⟨196608, 196744, 6961417⟩ CTN.nil) ⟨196608, 196748, 6682287⟩ (CTN.node CTN.nil ⟨196608, 196750, 6544867⟩ CTN.nil))) ⟨196608, 196768, 5372431⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨196608, 196772, 5127615⟩ CTN.nil) ⟨196608, 196808, 3181467⟩ CTN.nil) ⟨196608, 196840, 1839977⟩ (CTN.node CTN.nil ⟨196608, 196876, 767374⟩ CTN.nil)) ⟨196608, 196880, 676712⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196608, 196916, 117204⟩ CTN.nil) ⟨196608, 196932, 16628⟩ CTN.nil) ⟨196608, 196936, 5716⟩ (CTN.node CTN.nil ⟨196608, 196940, 495⟩ CTN.nil))))) ⟨196950, 198869, 11868⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨196950, 198885, 11865⟩ CTN.nil) ⟨196950, 199301, 11766⟩ CTN.nil) ⟨196950, 199717, 11668⟩ (CTN.node (CTN.node CTN.nil ⟨196950, 200133, 11571⟩ CTN.nil) ⟨196950, 200820, 11413⟩ CTN.nil)) ⟨196950, 201652, 11226⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196950, 202388, 11063⟩ CTN.nil) ⟨196950, 202484, 11042⟩ CTN.nil) ⟨196950, 203252, 10876⟩ (CTN.node CTN.nil ⟨196950, 203316, 10862⟩ CTN.nil))) ⟨196951, 199286, 14765⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨196951, 200086, 14530⟩ CTN.nil) ⟨196951, 200118, 14520⟩ CTN.nil) ⟨196960, 201308, 54735⟩ (CTN.node (CTN.node CTN.nil ⟨196960, 202496, 53460⟩ CTN.nil) ⟨196960, 202972, 52960⟩ CTN.nil)) ⟨196960, 204800, 51091⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196964, 204800, 75826⟩ CTN.nil) ⟨196966, 200772, 97473⟩ CTN.nil) ⟨196966, 202372, 94423⟩ (CTN.node CTN.nil ⟨196980, 203056, 231238⟩ CTN.nil)))) ⟨196980, 204800, 223451⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨196982, 198901, 278106⟩ CTN.nil) ⟨196982, 199701, 273670⟩ CTN.nil) ⟨196982, 200133, 271311⟩ (CTN.node (CTN.node CTN.nil ⟨196982, 200820, 267613⟩ CTN.nil) ⟨196982, 201588, 263552⟩ CTN.nil)) ⟨196982, 201908, 261883⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196984, 204660, 273280⟩ CTN.nil) ⟨196984, 204800, 272532⟩ CTN.nil) ⟨196986, 201052, 321850⟩ (CTN.node CTN.nil ⟨196986, 203512, 306549⟩ CTN.nil))) ⟨196992, 204224, 389680⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨196992, 204800, 385309⟩ CTN.nil) ⟨196996, 199970, 494045⟩ CTN.nil) ⟨196996, 200738, 486518⟩ (CTN.node CTN.nil ⟨196996, 201602, 478220⟩ CTN.nil)) ⟨196996, 202944, 465679⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨196997, 199284, 519506⟩ CTN.nil) ⟨196998, 198917, 542450⟩ CTN.nil) ⟨196998, 199301, 538275⟩ (CTN.node CTN.nil ⟨197012, 199954, 828274⟩ CTN.nil))))))))

noncomputable def tab11 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197012, 201554, 802251⟩ CTN.nil) ⟨197012, 202896, 781208⟩ CTN.nil) ⟨197014, 199317, 887338⟩ (CTN.node (CTN.node CTN.nil ⟨197014, 199733, 879958⟩ CTN.nil) ⟨197014, 200165, 872376⟩ CTN.nil)) ⟨197014, 200709, 862944⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197014, 200852, 860485⟩ CTN.nil) ⟨197014, 201620, 847432⟩ CTN.nil) ⟨197014, 202740, 828836⟩ (CTN.node CTN.nil ⟨197014, 203316, 819471⟩ CTN.nil))) ⟨197015, 200278, 894649⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197032, 204800, 1241610⟩ CTN.nil) ⟨197044, 204800, 1593589⟩ CTN.nil) ⟨197045, 198964, 1824384⟩ (CTN.node (CTN.node CTN.nil ⟨197045, 199380, 1809185⟩ CTN.nil) ⟨197045, 199796, 1794144⟩ CTN.nil)) ⟨197048, 200327, 1879798⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197048, 204800, 1720673⟩ CTN.nil) ⟨197056, 204800, 1989481⟩ CTN.nil) ⟨197060, 200098, 2338988⟩ (CTN.node CTN.nil ⟨197060, 200930, 2300435⟩ CTN.nil)))) ⟨197062, 200100, 2418671⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197064, 204800, 2277812⟩ CTN.nil) ⟨197068, 204800, 2429300⟩ CTN.nil) ⟨197077, 198980, 3129260⟩ (CTN.node (CTN.node CTN.nil ⟨197077, 199364, 3105187⟩ CTN.nil) ⟨197078, 201349, 3028672⟩ CTN.nil)) ⟨197079, 199382, 3196550⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197082, 203640, 3066944⟩ CTN.nil) ⟨197088, 201280, 3494398⟩ CTN.nil) ⟨197088, 201856, 3454630⟩ (CTN.node CTN.nil ⟨197092, 199811, 3798000⟩ CTN.nil))) ⟨197092, 200098, 3776228⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197092, 200866, 3718728⟩ CTN.nil) ⟨197093, 199380, 3882166⟩ CTN.nil) ⟨197093, 199796, 3849890⟩ (CTN.node (CTN.node CTN.nil ⟨197095, 200246, 3916940⟩ CTN.nil) ⟨197095, 200278, 3914434⟩ CTN.nil)) ⟨197104, 204800, 4012450⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197108, 199864, 4645226⟩ CTN.nil) ⟨197108, 200440, 4591989⟩ CTN.nil) ⟨197108, 201010, 4540055⟩ (CTN.node CTN.nil ⟨197108, 201874, 4462725⟩ CTN.nil))))) ⟨197110, 200789, 4670511⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197111, 199814, 4819262⟩ CTN.nil) ⟨197111, 200230, 4779283⟩ CTN.nil) ⟨197112, 200918, 4769955⟩ (CTN.node (CTN.node CTN.nil ⟨197112, 200950, 4766913⟩ CTN.nil) ⟨197112, 201367, 4727497⟩ CTN.nil)) ⟨197112, 201782, 4688673⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197112, 203446, 4536951⟩ CTN.nil) ⟨197112, 204788, 4419038⟩ CTN.nil) ⟨197112, 204800, 4418001⟩ (CTN.node CTN.nil ⟨197120, 199328, 5398003⟩ CTN.nil))) ⟨197120, 200192, 5305291⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197120, 201344, 5184750⟩ CTN.nil) ⟨197120, 201920, 5125764⟩ CTN.nil) ⟨197120, 204416, 4879645⟩ (CTN.node (CTN.node CTN.nil ⟨197120, 204800, 4843103⟩ CTN.nil) ⟨197128, 200902, 5710822⟩ CTN.nil)) ⟨197128, 204676, 5300602⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197136, 204800, 5751973⟩ CTN.nil) ⟨197139, 200274, 6486464⟩ CTN.nil) ⟨197139, 200306, 6482315⟩ (CTN.node CTN.nil ⟨197140, 202202, 6305748⟩ CTN.nil)))) ⟨197140, 203024, 6204110⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197140, 203544, 6140871⟩ CTN.nil) ⟨197140, 204560, 6019619⟩ CTN.nil) ⟨197140, 204800, 5991415⟩ (CTN.node (CTN.node CTN.nil ⟨197142, 202100, 6446696⟩ CTN.nil) ⟨197144, 200950, 6728216⟩ CTN.nil)) ⟨197144, 201750, 6621990⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197152, 199824, 7436819⟩ CTN.nil) ⟨197152, 200256, 7372768⟩ CTN.nil) ⟨197152, 201920, 7132405⟩ (CTN.node CTN.nil ⟨197152, 202688, 7024775⟩ CTN.nil))) ⟨197159, 200310, 7863668⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197159, 200438, 7843573⟩ CTN.nil) ⟨197164, 200434, 8209646⟩ CTN.nil) ⟨197168, 199424, 8681915⟩ (CTN.node CTN.nil ⟨197168, 204800, 7804477⟩ CTN.nil)) ⟨197172, 204800, 8083058⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197173, 199476, 9060675⟩ CTN.nil) ⟨197174, 199461, 9142013⟩ CTN.nil) ⟨197174, 202868, 8542402⟩ (CTN.node CTN.nil ⟨197174, 203700, 8403510⟩ CTN.nil)))))) ⟨197176, 201431, 8941248⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197176, 202102, 8822938⟩ CTN.nil) ⟨197176, 204788, 8368497⟩ CTN.nil) ⟨197176, 204800, 8366533⟩ (CTN.node (CTN.node CTN.nil ⟨197184, 199440, 9950990⟩ CTN.nil) ⟨197184, 199856, 9868285⟩ CTN.nil)) ⟨197184, 200288, 9783305⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197184, 200368, 9767669⟩ CTN.nil) ⟨197184, 200416, 9758302⟩ CTN.nil) ⟨197184, 201952, 9464405⟩ (CTN.node CTN.nil ⟨197184, 203552, 9169936⟩ CTN.nil))) ⟨197184, 204416, 9015683⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197184, 204800, 8948168⟩ CTN.nil) ⟨197188, 203136, 9553447⟩ CTN.nil) ⟨197188, 204672, 9269510⟩ (CTN.node (CTN.node CTN.nil ⟨197188, 204800, 9246328⟩ CTN.nil) ⟨197190, 199477, 10442633⟩ CTN.nil)) ⟨197190, 199893, 10355857⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197192, 200998, 10293696⟩ CTN.nil) ⟨197192, 201734, 10144096⟩ CTN.nil) ⟨197192, 204740, 9560598⟩ (CTN.node CTN.nil ⟨197200, 204800, 10170188⟩ CTN.nil)))) ⟨197204, 203152, 10832875⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197204, 204688, 10510938⟩ CTN.nil) ⟨197205, 199556, 11725169⟩ CTN.nil) ⟨197205, 200884, 11417769⟩ (CTN.node (CTN.node CTN.nil ⟨197206, 199125, 11917254⟩ CTN.nil) ⟨197206, 199541, 11818049⟩ CTN.nil)) ⟨197206, 199957, 11719875⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197208, 201782, 11472896⟩ CTN.nil) ⟨197212, 200480, 12131002⟩ CTN.nil) ⟨197216, 199424, 12760170⟩ (CTN.node CTN.nil ⟨197216, 199856, 12650051⟩ CTN.nil))) ⟨197216, 200288, 12541117⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197216, 201632, 12209628⟩ CTN.nil) ⟨197216, 201728, 12186371⟩ CTN.nil) ⟨197216, 202496, 12002302⟩ (CTN.node (CTN.node CTN.nil ⟨197216, 202560, 11987120⟩ CTN.nil) ⟨197216, 204800, 11470563⟩ CTN.nil)) ⟨197221, 199572, 13190849⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197221, 199988, 13081288⟩ CTN.nil) ⟨197222, 199125, 13405438⟩ CTN.nil) ⟨197228, 204800, 12497280⟩ (CTN.node CTN.nil ⟨197236, 199939, 14540021⟩ CTN.nil))))) ⟨197236, 200371, 14414863⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197236, 201042, 14223122⟩ CTN.nil) ⟨197236, 204800, 13206257⟩ CTN.nil) ⟨197238, 199525, 14861413⟩ (CTN.node (CTN.node CTN.nil ⟨197240, 201078, 14602347⟩ CTN.nil) ⟨197240, 201110, 14593043⟩ CTN.nil)) ⟨197240, 201511, 14477076⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197240, 201942, 14353714⟩ CTN.nil) ⟨197240, 202198, 14281064⟩ CTN.nil) ⟨197240, 203510, 13915861⟩ (CTN.node CTN.nil ⟨197240, 203606, 13889600⟩ CTN.nil))) ⟨197240, 204800, 13568097⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197248, 203616, 14642599⟩ CTN.nil) ⟨197248, 203712, 14614981⟩ CTN.nil) ⟨197248, 204544, 14378330⟩ (CTN.node (CTN.node CTN.nil ⟨197248, 204800, 14306480⟩ CTN.nil) ⟨197253, 199172, 16522845⟩ CTN.nil)) ⟨197253, 199556, 16395861⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197254, 199957, 16369340⟩ CTN.nil) ⟨197254, 200260, 16270362⟩ CTN.nil) ⟨197256, 201062, 16217953⟩ (CTN.node CTN.nil ⟨197256, 201830, 15972182⟩ CTN.nil)))) ⟨197256, 202662, 15711163⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197264, 199904, 17454274⟩ CTN.nil) ⟨197269, 199572, 18120951⟩ CTN.nil) ⟨197269, 199588, 18115133⟩ (CTN.node (CTN.node CTN.nil ⟨197269, 199988, 17970442⟩ CTN.nil) ⟨197270, 199557, 18237478⟩ CTN.nil)) ⟨197270, 200965, 17731045⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197272, 201110, 17896233⟩ CTN.nil) ⟨197272, 201116, 17894094⟩ CTN.nil) ⟨197272, 203808, 16966045⟩ (CTN.node CTN.nil ⟨197272, 204800, 16639286⟩ CTN.nil))) ⟨197280, 204800, 17456117⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197282, 200288, 19311924⟩ CTN.nil) ⟨197286, 199973, 19894210⟩ CTN.nil) ⟨197286, 199989, 19887835⟩ (CTN.node CTN.nil ⟨197296, 202808, 19913135⟩ CTN.nil)) ⟨197296, 203960, 19466461⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197296, 204800, 19148638⟩ CTN.nil) ⟨197300, 200051, 21513607⟩ CTN.nil) ⟨197300, 200467, 21335345⟩ (CTN.node CTN.nil ⟨197300, 201106, 21065106⟩ CTN.nil))))))) ⟨197300, 201138, 21051686⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197300, 201874, 20745950⟩ CTN.nil) ⟨197300, 201970, 20706482⟩ CTN.nil) ⟨197300, 202802, 20368326⟩ (CTN.node (CTN.node CTN.nil ⟨197302, 202228, 20831811⟩ CTN.nil) ⟨197302, 203828, 20184533⟩ CTN.nil)) ⟨197304, 201575, 21338683⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197304, 202262, 21049859⟩ CTN.nil) ⟨197304, 204800, 20024334⟩ CTN.nil) ⟨197312, 200384, 22828242⟩ (CTN.node CTN.nil ⟨197312, 200960, 22567290⟩ CTN.nil))) ⟨197312, 201728, 22225127⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197312, 202592, 21847912⟩ CTN.nil) ⟨197312, 203456, 21478667⟩ CTN.nil) ⟨197312, 204608, 20998393⟩ (CTN.node (CTN.node CTN.nil ⟨197312, 204800, 20919657⟩ CTN.nil) ⟨197316, 199603, 23692488⟩ CTN.nil)) ⟨197320, 204800, 21834610⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197328, 199584, 25247846⟩ CTN.nil) ⟨197332, 199619, 25756077⟩ CTN.nil) ⟨197332, 200035, 25542201⟩ (CTN.node CTN.nil ⟨197332, 201138, 24985775⟩ CTN.nil)))) ⟨197332, 201906, 24607277⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197332, 202738, 24205292⟩ CTN.nil) ⟨197332, 203800, 23704035⟩ CTN.nil) ⟨197334, 199637, 26011699⟩ (CTN.node (CTN.node CTN.nil ⟨197334, 203060, 24299405⟩ CTN.nil) ⟨197334, 203892, 23904688⟩ CTN.nil)) ⟨197336, 200599, 25776842⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197336, 201942, 25097044⟩ CTN.nil) ⟨197344, 202880, 25646808⟩ CTN.nil) ⟨197347, 200498, 27292301⟩ (CTN.node CTN.nil ⟨197347, 200530, 27274861⟩ CTN.nil))) ⟨197350, 199653, 28170979⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197350, 200069, 27937090⟩ CTN.nil) ⟨197350, 200356, 27777143⟩ CTN.nil) ⟨197350, 200388, 27759380⟩ (CTN.node (CTN.node CTN.nil ⟨197350, 201220, 27302493⟩ CTN.nil) ⟨197352, 201764, 27274477⟩ CTN.nil)) ⟨197352, 203428, 26391817⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197352, 204800, 25690771⟩ CTN.nil) ⟨197356, 200658, 28428729⟩ CTN.nil) ⟨197360, 199568, 29620404⟩ (CTN.node CTN.nil ⟨197360, 200000, 29364965⟩ CTN.nil))))) ⟨197360, 201272, 28628666⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197364, 203058, 28165184⟩ CTN.nil) ⟨197364, 203890, 27707668⟩ CTN.nil) ⟨197366, 199285, 30651276⟩ (CTN.node (CTN.node CTN.nil ⟨197366, 199301, 30641421⟩ CTN.nil) ⟨197366, 199717, 30386573⟩ CTN.nil)) ⟨197366, 200133, 30134369⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197366, 200340, 30009849⟩ CTN.nil) ⟨197366, 201108, 29553445⟩ CTN.nil) ⟨197366, 201940, 29068758⟩ (CTN.node CTN.nil ⟨197366, 203060, 28431881⟩ CTN.nil))) ⟨197368, 203670, 28358210⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197368, 204800, 27736695⟩ CTN.nil) ⟨197374, 201412, 30495083⟩ CTN.nil) ⟨197376, 200992, 31036758⟩ (CTN.node (CTN.node CTN.nil ⟨197376, 202720, 29990601⟩ CTN.nil) ⟨197376, 203584, 29484057⟩ CTN.nil)) ⟨197376, 204736, 28825188⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197376, 204800, 28789126⟩ CTN.nil) ⟨197380, 201154, 31510151⟩ CTN.nil) ⟨197380, 201922, 31032856⟩ (CTN.node CTN.nil ⟨197380, 202754, 30525942⟩ CTN.nil)))) ⟨197380, 204800, 29322710⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197381, 201076, 31703534⟩ CTN.nil) ⟨197382, 199301, 32999678⟩ CTN.nil) ⟨197392, 204800, 30952938⟩ (CTN.node (CTN.node CTN.nil ⟨197397, 200532, 34430405⟩ CTN.nil) ⟨197398, 199701, 35162068⟩ CTN.nil)) ⟨197408, 200480, 36154484⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197408, 200512, 36131379⟩ CTN.nil) ⟨197408, 201056, 35741395⟩ CTN.nil) ⟨197408, 201088, 35718619⟩ (CTN.node CTN.nil ⟨197408, 201600, 35356660⟩ CTN.nil))) ⟨197408, 201920, 35132763⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197408, 204800, 33195364⟩ CTN.nil) ⟨197413, 199700, 37516513⟩ CTN.nil) ⟨197414, 200133, 37350705⟩ (CTN.node CTN.nil ⟨197424, 200108, 38971284⟩ CTN.nil)) ⟨197424, 202792, 36946064⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197424, 204800, 35516421⟩ CTN.nil) ⟨197428, 200147, 39590562⟩ CTN.nil) ⟨197428, 200579, 39250128⟩ (CTN.node CTN.nil ⟨197428, 201266, 38716247⟩ CTN.nil)))))) ⟨197428, 204800, 36108973⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197429, 199716, 40098574⟩ CTN.nil) ⟨197429, 200132, 39765761⟩ CTN.nil) ⟨197429, 200564, 39423795⟩ (CTN.node (CTN.node CTN.nil ⟨197430, 199349, 40561321⟩ CTN.nil) ⟨197430, 199733, 40249868⟩ CTN.nil)) ⟨197430, 200693, 39484219⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197430, 201109, 39158096⟩ CTN.nil) ⟨197431, 200694, 39645585⟩ CTN.nil) ⟨197432, 202358, 38513054⟩ (CTN.node CTN.nil ⟨197432, 204800, 36706441⟩ CTN.nil))) ⟨197440, 200544, 41243304⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197440, 200672, 41138033⟩ CTN.nil) ⟨197440, 201088, 40798215⟩ CTN.nil) ⟨197440, 201120, 40772221⟩ (CTN.node (CTN.node CTN.nil ⟨197440, 201632, 40359116⟩ CTN.nil) ⟨197440, 201664, 40333471⟩ CTN.nil)) ⟨197440, 201952, 40103581⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197440, 202240, 39875327⟩ CTN.nil) ⟨197440, 202976, 39299349⟩ CTN.nil) ⟨197440, 203452, 38932375⟩ (CTN.node CTN.nil ⟨197440, 203904, 38587861⟩ CTN.nil)))) ⟨197440, 204800, 37916125⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197442, 200448, 41655417⟩ CTN.nil) ⟨197442, 201280, 40970021⟩ CTN.nil) ⟨197446, 199749, 42921697⟩ (CTN.node (CTN.node CTN.nil ⟨197446, 200165, 42565511⟩ CTN.nil) ⟨197446, 201220, 41678635⟩ CTN.nil)) ⟨197461, 199364, 45870711⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197461, 199380, 45855969⟩ CTN.nil) ⟨197461, 199796, 45474730⟩ CTN.nil) ⟨197461, 200212, 45097446⟩ (CTN.node CTN.nil ⟨197461, 200628, 44724068⟩ CTN.nil))) ⟨197462, 202420, 43325839⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197462, 204020, 41980891⟩ CTN.nil) ⟨197464, 200743, 45139484⟩ CTN.nil) ⟨197468, 200736, 45841150⟩ (CTN.node CTN.nil ⟨197468, 201312, 45318049⟩ CTN.nil)) ⟨197468, 202144, 44575564⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197472, 200240, 47005328⟩ CTN.nil) ⟨197472, 200576, 46690725⟩ CTN.nil) ⟨197472, 201152, 46157506⟩ (CTN.node CTN.nil ⟨197472, 201984, 45400671⟩ CTN.nil))))) ⟨197472, 202240, 45170925⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197472, 203840, 43767473⟩ CTN.nil) ⟨197474, 200448, 47164637⟩ CTN.nil) ⟨197474, 201216, 46447719⟩ (CTN.node (CTN.node CTN.nil ⟨197488, 204800, 45587265⟩ CTN.nil) ⟨197492, 200248, 50616303⟩ CTN.nil)) ⟨197492, 200259, 50605168⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197492, 200675, 50186287⟩ CTN.nil) ⟨197492, 200824, 50037311⟩ CTN.nil) ⟨197492, 201330, 49535500⟩ (CTN.node CTN.nil ⟨197492, 201362, 49503977⟩ CTN.nil))) ⟨197492, 202098, 48785819⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197492, 202194, 48693110⟩ CTN.nil) ⟨197492, 202418, 48477642⟩ CTN.nil) ⟨197492, 203026, 47898782⟩ (CTN.node (CTN.node CTN.nil ⟨197492, 204800, 46258495⟩ CTN.nil) ⟨197493, 200196, 50853633⟩ CTN.nil)) ⟨197493, 200628, 50416456⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197494, 202068, 49170945⟩ CTN.nil) ⟨197496, 200252, 51352040⟩ CTN.nil) ⟨197496, 201751, 49840788⟩ (CTN.node CTN.nil ⟨197496, 203190, 48441988⟩ CTN.nil)))) ⟨197496, 204800, 46934644⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197500, 200256, 52093042⟩ CTN.nil) ⟨197500, 200832, 51497181⟩ CTN.nil) ⟨197504, 200576, 52506657⟩ (CTN.node (CTN.node CTN.nil ⟨197504, 201152, 51907019⟩ CTN.nil) ⟨197504, 201696, 51348537⟩ CTN.nil)) ⟨197504, 201920, 51120758⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197504, 202016, 51023525⟩ CTN.nil) ⟨197504, 203648, 49405401⟩ CTN.nil) ⟨197504, 203712, 49343262⟩ (CTN.node CTN.nil ⟨197504, 204800, 48301700⟩ CTN.nil))) ⟨197508, 202082, 51685698⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197508, 202914, 50842089⟩ CTN.nil) ⟨197508, 203746, 50015625⟩ CTN.nil) ⟨197509, 199412, 54706915⟩ (CTN.node CTN.nil ⟨197509, 199796, 54286976⟩ CTN.nil)) ⟨197524, 199827, 57165676⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197524, 200243, 56691471⟩ CTN.nil) ⟨197524, 200675, 56204222⟩ CTN.nil) ⟨197524, 201362, 55440094⟩ (CTN.node CTN.nil ⟨197524, 202130, 54601185⟩ CTN.nil))))))))

noncomputable def tab12 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197525, 199812, 57379803⟩ CTN.nil) ⟨197525, 200660, 56414675⟩ CTN.nil) ⟨197525, 201204, 55806211⟩ (CTN.node (CTN.node CTN.nil ⟨197526, 202100, 55010292⟩ CTN.nil) ⟨197526, 202932, 54112498⟩ CTN.nil)) ⟨197526, 203252, 53772076⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197526, 204084, 52899427⟩ CTN.nil) ⟨197527, 200230, 57293107⟩ CTN.nil) ⟨197528, 204800, 52520949⟩ (CTN.node CTN.nil ⟨197532, 203936, 54150578⟩ CTN.nil))) ⟨197534, 201604, 57088934⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197536, 203072, 55829662⟩ CTN.nil) ⟨197541, 200228, 60074402⟩ CTN.nil) ⟨197548, 204800, 56172309⟩ (CTN.node (CTN.node CTN.nil ⟨197552, 199760, 62890923⟩ CTN.nil) ⟨197552, 204800, 56917346⟩ CTN.nil)) ⟨197556, 201594, 61429249⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197556, 203282, 59411520⟩ CTN.nil) ⟨197556, 204114, 58447491⟩ CTN.nil) ⟨197558, 204084, 58864058⟩ (CTN.node CTN.nil ⟨197558, 204800, 58044128⟩ CTN.nil)))) ⟨197560, 202518, 61103859⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197560, 203636, 59771244⟩ CTN.nil) ⟨197568, 204800, 59946710⟩ CTN.nil) ⟨197573, 200724, 66016755⟩ (CTN.node (CTN.node CTN.nil ⟨197575, 200854, 66264447⟩ CTN.nil) ⟨197576, 203588, 62970277⟩ CTN.nil)) ⟨197576, 204800, 61490925⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197584, 199840, 69560898⟩ CTN.nil) ⟨197584, 200256, 68983909⟩ CTN.nil) ⟨197589, 199892, 70576636⟩ (CTN.node CTN.nil ⟨197589, 201844, 67882283⟩ CTN.nil))) ⟨197590, 200725, 69625825⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197590, 200869, 69426116⟩ CTN.nil) ⟨197590, 201285, 68853187⟩ CTN.nil) ⟨197590, 201396, 68701315⟩ (CTN.node (CTN.node CTN.nil ⟨197591, 200854, 69661709⟩ CTN.nil) ⟨197592, 202268, 67940743⟩ CTN.nil)) ⟨197600, 199856, 73053181⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197600, 200416, 72239000⟩ CTN.nil) ⟨197600, 200832, 71641514⟩ CTN.nil) ⟨197600, 202016, 69974472⟩ (CTN.node CTN.nil ⟨197602, 201376, 71301596⟩ CTN.nil))))) ⟨197602, 202240, 70089331⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197602, 202304, 70000563⟩ CTN.nil) ⟨197603, 199938, 73600806⟩ CTN.nil) ⟨197604, 201952, 70919039⟩ (CTN.node (CTN.node CTN.nil ⟨197604, 203616, 68626047⟩ CTN.nil) ⟨197605, 199908, 74092058⟩ CTN.nil)) ⟨197605, 200324, 73477693⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197605, 200756, 72846424⟩ CTN.nil) ⟨197606, 199893, 74338407⟩ CTN.nil) ⟨197616, 200288, 75994540⟩ (CTN.node CTN.nil ⟨197616, 200384, 75848818⟩ CTN.nil))) ⟨197616, 200800, 75221376⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197616, 204800, 69507379⟩ CTN.nil) ⟨197622, 199541, 78522136⟩ CTN.nil) ⟨197622, 199957, 77869842⟩ (CTN.node (CTN.node CTN.nil ⟨197622, 200757, 76634362⟩ CTN.nil) ⟨197622, 200789, 76585454⟩ CTN.nil)) ⟨197622, 201428, 75616951⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197622, 201460, 75568854⟩ CTN.nil) ⟨197622, 201877, 74945571⟩ CTN.nil) ⟨197622, 202292, 74331646⟩ (CTN.node CTN.nil ⟨197622, 203124, 73119661⟩ CTN.nil)))) ⟨197624, 201895, 75360834⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197624, 203350, 73224210⟩ CTN.nil) ⟨197624, 204800, 71169751⟩ CTN.nil) ⟨197632, 204000, 74002844⟩ (CTN.node (CTN.node CTN.nil ⟨197632, 204800, 72851820⟩ CTN.nil) ⟨197636, 204800, 73700240⟩ CTN.nil)) ⟨197637, 199556, 82005355⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197637, 199572, 81979025⟩ CTN.nil) ⟨197637, 199988, 81298119⟩ CTN.nil) ⟨197637, 200404, 80624271⟩ (CTN.node CTN.nil ⟨197637, 200820, 79957391⟩ CTN.nil))) ⟨197638, 201412, 79248128⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197648, 199856, 84118212⟩ CTN.nil) ⟨197648, 200288, 83393840⟩ CTN.nil) ⟨197652, 202064, 81412715⟩ (CTN.node CTN.nil ⟨197652, 202128, 81309515⟩ CTN.nil)) ⟨197652, 203792, 78682822⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197654, 202260, 81555430⟩ CTN.nil) ⟨197654, 203060, 80276102⟩ CTN.nil) ⟨197656, 203604, 79867983⟩ (CTN.node CTN.nil ⟨197664, 200932, 86108356⟩ CTN.nil)))))) ⟨197664, 201280, 85513599⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197664, 201508, 85126714⟩ CTN.nil) ⟨197664, 201856, 84540414⟩ CTN.nil) ⟨197664, 202340, 83733355⟩ (CTN.node (CTN.node CTN.nil ⟨197664, 204200, 80720077⟩ CTN.nil) ⟨197664, 204800, 79777068⟩ CTN.nil)) ⟨197668, 200371, 88047146⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197669, 200388, 88260255⟩ CTN.nil) ⟨197669, 200820, 87502227⟩ CTN.nil) ⟨197680, 201012, 89830015⟩ (CTN.node CTN.nil ⟨197680, 201592, 88799294⟩ CTN.nil))) ⟨197680, 204800, 83357886⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197684, 200440, 91850418⟩ CTN.nil) ⟨197684, 202642, 87917516⟩ CTN.nil) ⟨197684, 204800, 84265403⟩ (CTN.node (CTN.node CTN.nil ⟨197685, 199604, 93653354⟩ CTN.nil) ⟨197685, 199988, 92935147⟩ CTN.nil)) ⟨197686, 200533, 92175613⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197686, 200821, 91647277⟩ CTN.nil) ⟨197686, 201492, 90430938⟩ CTN.nil) ⟨197686, 202260, 89063431⟩ (CTN.node CTN.nil ⟨197686, 202292, 89007014⟩ CTN.nil)))) ⟨197686, 202612, 88445301⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197686, 203124, 87555746⟩ CTN.nil) ⟨197686, 203380, 87115164⟩ CTN.nil) ⟨197686, 204800, 84721008⟩ (CTN.node (CTN.node CTN.nil ⟨197688, 200444, 92837572⟩ CTN.nil) ⟨197688, 201020, 91776650⟩ CTN.nil)) ⟨197688, 201600, 90723634⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197696, 199904, 95873024⟩ CTN.nil) ⟨197696, 200336, 95047625⟩ CTN.nil) ⟨197696, 200768, 94231092⟩ (CTN.node CTN.nil ⟨197696, 201344, 93155976⟩ CTN.nil))) ⟨197696, 201376, 93096698⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197696, 201920, 92096153⟩ CTN.nil) ⟨197696, 202208, 91571895⟩ CTN.nil) ⟨197696, 204800, 87017505⟩ (CTN.node (CTN.node CTN.nil ⟨197701, 200004, 96956428⟩ CTN.nil) ⟨197701, 200420, 96152858⟩ CTN.nil)) ⟨197701, 200852, 95327176⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197701, 201396, 94299997⟩ CTN.nil) ⟨197702, 201476, 94398767⟩ CTN.nil) ⟨197702, 202244, 92971146⟩ (CTN.node CTN.nil ⟨197702, 203076, 91454885⟩ CTN.nil))))) ⟨197716, 200051, 100738137⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197716, 200467, 99903420⟩ CTN.nil) ⟨197718, 200853, 99650457⟩ CTN.nil) ⟨197718, 201524, 98328110⟩ (CTN.node (CTN.node CTN.nil ⟨197718, 202292, 96841415⟩ CTN.nil) ⟨197718, 203124, 95262406⟩ CTN.nil)) ⟨197718, 204276, 93128848⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197724, 204800, 93611463⟩ CTN.nil) ⟨197728, 200400, 103168452⟩ CTN.nil) ⟨197728, 200832, 102282437⟩ (CTN.node CTN.nil ⟨197728, 201408, 101115830⟩ CTN.nil))) ⟨197728, 202240, 99459945⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197728, 202496, 98957274⟩ CTN.nil) ⟨197728, 203072, 97837827⟩ CTN.nil) ⟨197734, 201540, 102398977⟩ (CTN.node (CTN.node CTN.nil ⟨197735, 201014, 103738349⟩ CTN.nil) ⟨197738, 201776, 102953915⟩ CTN.nil)) ⟨197744, 200000, 108281690⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197744, 201656, 104763758⟩ CTN.nil) ⟨197744, 202424, 103180788⟩ CTN.nil) ⟨197744, 204800, 98469199⟩ (CTN.node CTN.nil ⟨197748, 200035, 109289674⟩ CTN.nil)))) ⟨197748, 200786, 107661531⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197748, 204352, 100331682⟩ CTN.nil) ⟨197750, 200901, 107949524⟩ CTN.nil) ⟨197750, 201588, 106483531⟩ (CTN.node (CTN.node CTN.nil ⟨197750, 202676, 104212397⟩ CTN.nil) ⟨197752, 201664, 106850766⟩ CTN.nil)) ⟨197752, 202432, 105236326⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197752, 204800, 100446772⟩ CTN.nil) ⟨197760, 200432, 111683239⟩ CTN.nil) ⟨197760, 200528, 111469236⟩ (CTN.node CTN.nil ⟨197760, 200864, 110724252⟩ CTN.nil))) ⟨197760, 200944, 110547793⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197760, 200992, 110442086⟩ CTN.nil) ⟨197760, 201376, 109600967⟩ CTN.nil) ⟨197760, 201408, 109531236⟩ (CTN.node CTN.nil ⟨197760, 201440, 109461560⟩ CTN.nil)) ⟨197760, 201952, 108354249⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197760, 201984, 108285508⟩ CTN.nil) ⟨197760, 202272, 107669288⟩ CTN.nil) ⟨197760, 202560, 107057445⟩ (CTN.node CTN.nil ⟨197760, 203392, 105314155⟩ CTN.nil))))))) ⟨197760, 204128, 103801507⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197760, 204224, 103606213⟩ CTN.nil) ⟨197760, 204800, 102444049⟩ CTN.nil) ⟨197764, 200051, 113642794⟩ (CTN.node (CTN.node CTN.nil ⟨197764, 200467, 112701149⟩ CTN.nil) ⟨197764, 200738, 112092966⟩ CTN.nil)) ⟨197764, 200770, 112021422⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197764, 201602, 110181161⟩ CTN.nil) ⟨197764, 204800, 103450075⟩ CTN.nil) ⟨197765, 202036, 109502603⟩ (CTN.node CTN.nil ⟨197766, 200069, 114156250⟩ CTN.nil))) ⟨197780, 200722, 116543846⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197780, 201650, 114410415⟩ CTN.nil) ⟨197781, 201460, 115117927⟩ CTN.nil) ⟨197782, 200133, 118488266⟩ (CTN.node (CTN.node CTN.nil ⟨197782, 200933, 116609976⟩ CTN.nil) ⟨197782, 200965, 116535622⟩ CTN.nil)) ⟨197782, 201620, 115026622⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197782, 201652, 114953528⟩ CTN.nil) ⟨197782, 202053, 114042469⟩ CTN.nil) ⟨197782, 202484, 113073296⟩ (CTN.node CTN.nil ⟨197782, 202740, 112502511⟩ CTN.nil)))) ⟨197782, 203316, 111231359⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197783, 201462, 115663736⟩ CTN.nil) ⟨197784, 204800, 108554093⟩ CTN.nil) ⟨197788, 201632, 116650695⟩ (CTN.node (CTN.node CTN.nil ⟨197788, 203296, 112873205⟩ CTN.nil) ⟨197792, 200000, 121654515⟩ CTN.nil)) ⟨197792, 200432, 120607658⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197792, 200864, 119572039⟩ CTN.nil) ⟨197792, 201440, 118208448⟩ CTN.nil) ⟨197792, 202208, 116420428⟩ (CTN.node CTN.nil ⟨197792, 202304, 116199310⟩ CTN.nil))) ⟨197792, 202560, 115612224⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197792, 203072, 114449136⟩ CTN.nil) ⟨197792, 203136, 114304780⟩ CTN.nil) ⟨197798, 200501, 122150726⟩ (CTN.node (CTN.node CTN.nil ⟨197798, 201604, 119495844⟩ CTN.nil) ⟨197798, 202372, 117689812⟩ CTN.nil)) ⟨197798, 203204, 115771620⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197798, 204036, 113892360⟩ CTN.nil) ⟨197810, 201616, 122846125⟩ CTN.nil) ⟨197810, 202384, 120989567⟩ (CTN.node CTN.nil ⟨197810, 202480, 120759971⟩ CTN.nil))))) ⟨197810, 203216, 119017710⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197810, 203312, 118792782⟩ CTN.nil) ⟨197810, 204080, 117012355⟩ CTN.nil) ⟨197810, 204144, 116865497⟩ (CTN.node (CTN.node CTN.nil ⟨197814, 199733, 128731375⟩ CTN.nil) ⟨197814, 203252, 120033836⟩ CTN.nil)) ⟨197814, 203508, 119430204⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197824, 203360, 122546376⟩ CTN.nil) ⟨197824, 204800, 119131542⟩ CTN.nil) ⟨197844, 201554, 132839154⟩ (CTN.node CTN.nil ⟨197845, 200132, 136963957⟩ CTN.nil))) ⟨197846, 200709, 135694186⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197846, 200997, 134917089⟩ CTN.nil) ⟨197846, 201109, 134616388⟩ CTN.nil) ⟨197846, 201684, 133085737⟩ (CTN.node (CTN.node CTN.nil ⟨197846, 202452, 131075103⟩ CTN.nil) ⟨197846, 202804, 130166259⟩ CTN.nil)) ⟨197846, 203572, 128210517⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197846, 204800, 125159081⟩ CTN.nil) ⟨197847, 202102, 132279321⟩ CTN.nil) ⟨197856, 200672, 138820464⟩ (CTN.node CTN.nil ⟨197860, 200579, 140300486⟩ CTN.nil)))) ⟨197860, 200866, 139499272⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197860, 201602, 137470583⟩ CTN.nil) ⟨197861, 200148, 141823539⟩ CTN.nil) ⟨197861, 200564, 140648956⟩ (CTN.node (CTN.node CTN.nil ⟨197862, 200165, 142084527⟩ CTN.nil) ⟨197864, 204800, 130201516⟩ CTN.nil)) ⟨197872, 204800, 132474608⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197876, 202802, 138969641⟩ CTN.nil) ⟨197877, 199796, 147852138⟩ CTN.nil) ⟨197877, 200212, 146625474⟩ (CTN.node CTN.nil ⟨197877, 200628, 145411509⟩ CTN.nil))) ⟨197878, 201029, 144562433⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197878, 201716, 142600466⟩ CTN.nil) ⟨197878, 202484, 140446424⟩ CTN.nil) ⟨197878, 203316, 138158586⟩ (CTN.node CTN.nil ⟨197880, 204800, 134767399⟩ CTN.nil)) ⟨197888, 200656, 148775704⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197888, 200960, 147876300⟩ CTN.nil) ⟨197888, 203168, 141543691⟩ CTN.nil) ⟨197888, 204032, 139158233⟩ (CTN.node CTN.nil ⟨197888, 204800, 137079886⟩ CTN.nil)))))) ⟨197890, 203264, 141875120⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197890, 204096, 139572810⟩ CTN.nil) ⟨197892, 200930, 149220782⟩ CTN.nil) ⟨197892, 201762, 146771356⟩ (CTN.node (CTN.node CTN.nil ⟨197892, 202594, 144371996⟩ CTN.nil) ⟨197892, 203968, 140515959⟩ CTN.nil)) ⟨197892, 204800, 138243516⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197893, 199796, 152964262⟩ CTN.nil) ⟨197904, 200672, 153810287⟩ CTN.nil) ⟨197907, 201042, 153634926⟩ (CTN.node CTN.nil ⟨197908, 200259, 156379296⟩ CTN.nil))) ⟨197908, 200675, 155084878⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197910, 202868, 149094808⟩ CTN.nil) ⟨197912, 204800, 144135524⟩ CTN.nil) ⟨197920, 202688, 152738434⟩ (CTN.node (CTN.node CTN.nil ⟨197920, 204460, 147505149⟩ CTN.nil) ⟨197920, 204800, 146526793⟩ CTN.nil)) ⟨197925, 200628, 160751374⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197927, 201622, 158243529⟩ CTN.nil) ⟨197936, 204800, 151368407⟩ CTN.nil) ⟨197940, 200243, 166982753⟩ (CTN.node CTN.nil ⟨197941, 200228, 167368314⟩ CTN.nil)))) ⟨197944, 202870, 159764152⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197952, 201136, 168007961⟩ CTN.nil) ⟨197952, 201568, 166570368⟩ CTN.nil) ⟨197952, 201694, 166153969⟩ (CTN.node (CTN.node CTN.nil ⟨197952, 202558, 163333450⟩ CTN.nil) ⟨197952, 202720, 162811285⟩ CTN.nil)) ⟨197952, 202752, 162708388⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197952, 203584, 160061385⟩ CTN.nil) ⟨197952, 203964, 158870335⟩ CTN.nil) ⟨197952, 204416, 157468006⟩ (CTN.node CTN.nil ⟨197952, 204800, 156288787⟩ CTN.nil))) ⟨197956, 200259, 172333583⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197956, 200675, 170907105⟩ CTN.nil) ⟨197956, 200962, 169931572⟩ CTN.nil) ⟨197956, 201730, 167355116⟩ (CTN.node CTN.nil ⟨197956, 202594, 164514710⟩ CTN.nil)) ⟨197956, 203968, 160120680⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197957, 200644, 171350911⟩ CTN.nil) ⟨197957, 200660, 171296192⟩ CTN.nil) ⟨197957, 201652, 167945849⟩ (CTN.node CTN.nil ⟨197960, 204800, 158778510⟩ CTN.nil))))) ⟨197962, 202032, 168333107⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197968, 204800, 161287921⟩ CTN.nil) ⟨197971, 200722, 175844242⟩ CTN.nil) ⟨197971, 201138, 174392053⟩ (CTN.node (CTN.node CTN.nil ⟨197972, 201874, 172194069⟩ CTN.nil) ⟨197974, 203700, 166741058⟩ CTN.nil)) ⟨197976, 204800, 163817019⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨197984, 200192, 182242438⟩ CTN.nil) ⟨197984, 200624, 180675711⟩ CTN.nil) ⟨197984, 201056, 179125788⟩ (CTN.node CTN.nil ⟨197984, 201088, 179011642⟩ CTN.nil))) ⟨197984, 201600, 177197605⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨197984, 202176, 175184201⟩ CTN.nil) ⟨197991, 202262, 177247423⟩ CTN.nil) ⟨198000, 200256, 187650757⟩ (CTN.node (CTN.node CTN.nil ⟨198003, 200706, 187029046⟩ CTN.nil) ⟨198003, 201138, 185425275⟩ CTN.nil)) ⟨198004, 200752, 187210399⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198004, 203410, 177602801⟩ CTN.nil) ⟨198004, 204274, 174613166⟩ CTN.nil) ⟨198004, 204800, 172823873⟩ (CTN.node CTN.nil ⟨198006, 201285, 185932118⟩ CTN.nil)))) ⟨198006, 202932, 179961268⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198006, 203700, 177259053⟩ CTN.nil) ⟨198007, 201270, 186337939⟩ CTN.nil) ⟨198008, 203702, 177920114⟩ (CTN.node (CTN.node CTN.nil ⟨198008, 204800, 174130248⟩ CTN.nil) ⟨198016, 200272, 193316506⟩ CTN.nil)) ⟨198016, 200832, 191166441⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198016, 201120, 190072335⟩ CTN.nil) ⟨198016, 201632, 188146519⟩ CTN.nil) ⟨198016, 201664, 188026967⟩ (CTN.node CTN.nil ⟨198016, 202208, 186009045⟩ CTN.nil))) ⟨198016, 202240, 185891189⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198016, 203360, 181824413⟩ CTN.nil) ⟨198016, 203552, 181138461⟩ CTN.nil) ⟨198016, 204224, 178762967⟩ (CTN.node CTN.nil ⟨198016, 204800, 176757759⟩ CTN.nil)) ⟨198021, 200324, 194920675⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198024, 201830, 190215010⟩ CTN.nil) ⟨198032, 200800, 197039401⟩ CTN.nil) ⟨198034, 201872, 193591309⟩ (CTN.node CTN.nil ⟨198034, 202736, 190307906⟩ CTN.nil))))))))

noncomputable def tab13 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198034, 204336, 184409300⟩ CTN.nil) ⟨198034, 204400, 184178145⟩ CTN.nil) ⟨198037, 200340, 200689171⟩ (CTN.node (CTN.node CTN.nil ⟨198037, 200756, 199028652⟩ CTN.nil) ⟨198044, 201312, 199364560⟩ CTN.nil)) ⟨198048, 200816, 202810742⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198048, 201152, 201457234⟩ CTN.nil) ⟨198048, 202560, 195906721⟩ CTN.nil) ⟨198048, 202816, 194918170⟩ (CTN.node CTN.nil ⟨198048, 203584, 191989707⟩ CTN.nil))) ⟨198048, 204416, 188879012⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198053, 199988, 208066394⟩ CTN.nil) ⟨198053, 200404, 206341812⟩ CTN.nil) ⟨198053, 200820, 204635066⟩ (CTN.node (CTN.node CTN.nil ⟨198056, 203568, 194842717⟩ CTN.nil) ⟨198056, 204800, 190190453⟩ CTN.nil)) ⟨198064, 201976, 203969764⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198064, 203576, 197624324⟩ CTN.nil) ⟨198064, 204728, 193207917⟩ CTN.nil) ⟨198064, 204800, 192936009⟩ (CTN.node CTN.nil ⟨198066, 204800, 193625471⟩ CTN.nil)))) ⟨198068, 200824, 210189680⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198068, 201874, 205844902⟩ CTN.nil) ⟨198068, 203026, 201206450⟩ CTN.nil) ⟨198068, 204800, 194316163⟩ (CTN.node (CTN.node CTN.nil ⟨198069, 199988, 214111556⟩ CTN.nil) ⟨198072, 200828, 211671008⟩ CTN.nil)) ⟨198072, 201404, 209256696⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198072, 201984, 206860309⟩ CTN.nil) ⟨198072, 202752, 203739711⟩ CTN.nil) ⟨198072, 203030, 202624644⟩ (CTN.node CTN.nil ⟨198072, 203584, 200425194⟩ CTN.nil))) ⟨198076, 200832, 213157416⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198080, 200288, 217010943⟩ CTN.nil) ⟨198080, 201152, 213301458⟩ CTN.nil) ⟨198080, 201728, 210872451⟩ (CTN.node (CTN.node CTN.nil ⟨198080, 201992, 209770717⟩ CTN.nil) ⟨198080, 202272, 208610064⟩ CTN.nil)) ⟨198080, 202496, 207687318⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198080, 202760, 206606339⟩ CTN.nil) ⟨198080, 203360, 204175608⟩ CTN.nil) ⟨198080, 203592, 203245318⟩ (CTN.node CTN.nil ⟨198080, 204544, 199482961⟩ CTN.nil))))) ⟨198080, 204744, 198703649⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198080, 204800, 198486124⟩ CTN.nil) ⟨198084, 204800, 199885944⟩ CTN.nil) ⟨198088, 202662, 209931739⟩ (CTN.node (CTN.node CTN.nil ⟨198088, 204800, 201290680⟩ CTN.nil) ⟨198098, 204400, 206434157⟩ CTN.nil)) ⟨198100, 200803, 222417447⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198100, 201235, 220511139⟩ CTN.nil) ⟨198100, 201906, 217590512⟩ CTN.nil) ⟨198101, 200820, 222726762⟩ (CTN.node CTN.nil ⟨198101, 201364, 220326434⟩ CTN.nil))) ⟨198101, 201780, 218512682⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198102, 200949, 222538685⟩ CTN.nil) ⟨198104, 204800, 206958777⟩ CTN.nil) ⟨198112, 203648, 214616784⟩ (CTN.node (CTN.node CTN.nil ⟨198112, 204480, 211140561⟩ CTN.nil) ⟨198115, 201266, 226129476⟩ CTN.nil)) ⟨198117, 200420, 230763039⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198128, 200336, 235505058⟩ CTN.nil) ⟨198128, 200768, 233481886⟩ CTN.nil) ⟨198128, 204800, 215608358⟩ (CTN.node CTN.nil ⟨198132, 200467, 236478490⟩ CTN.nil)))) ⟨198132, 200883, 234523083⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198132, 201299, 232587851⟩ CTN.nil) ⟨198132, 201970, 229508243⟩ CTN.nil) ⟨198132, 202802, 225760168⟩ (CTN.node (CTN.node CTN.nil ⟨198132, 203634, 222088313⟩ CTN.nil) ⟨198132, 204466, 218490825⟩ CTN.nil)) ⟨198132, 204800, 217067153⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198133, 200852, 235063200⟩ CTN.nil) ⟨198134, 201108, 234260403⟩ CTN.nil) ⟨198134, 204660, 218395730⟩ (CTN.node CTN.nil ⟨198136, 203862, 222586011⟩ CTN.nil))) ⟨198136, 204800, 218530860⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198144, 202336, 232474660⟩ CTN.nil) ⟨198144, 204092, 224566275⟩ CTN.nil) ⟨198144, 204800, 221473012⟩ (CTN.node CTN.nil ⟨198148, 201922, 235954329⟩ CTN.nil)) ⟨198148, 204800, 222951456⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198151, 201430, 239459680⟩ CTN.nil) ⟨198160, 200832, 245954446⟩ CTN.nil) ⟨198160, 204044, 230809870⟩ (CTN.node CTN.nil ⟨198160, 204800, 227416258⟩ CTN.nil)))))) ⟨198164, 201299, 245282141⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198164, 201970, 242034453⟩ CTN.nil) ⟨198164, 202738, 238382984⟩ CTN.nil) ⟨198166, 203124, 237349759⟩ (CTN.node (CTN.node CTN.nil ⟨198166, 203892, 233789171⟩ CTN.nil) ⟨198166, 204724, 230006903⟩ CTN.nil)) ⟨198167, 202422, 241057765⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198176, 200944, 251903986⟩ CTN.nil) ⟨198176, 200992, 251663114⟩ CTN.nil) ⟨198176, 202592, 243796272⟩ (CTN.node CTN.nil ⟨198176, 203456, 239675946⟩ CTN.nil))) ⟨198176, 203712, 238471859⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198176, 204800, 233438077⟩ CTN.nil) ⟨198179, 200946, 253121740⟩ CTN.nil) ⟨198179, 201362, 251033689⟩ (CTN.node (CTN.node CTN.nil ⟨198180, 200467, 255966845⟩ CTN.nil) ⟨198192, 200864, 258899527⟩ CTN.nil)) ⟨198192, 200960, 258404503⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198192, 204800, 239538451⟩ CTN.nil) ⟨198196, 200483, 262550195⟩ CTN.nil) ⟨198196, 200899, 260379378⟩ (CTN.node CTN.nil ⟨198196, 201331, 258148768⟩ CTN.nil)))) ⟨198196, 201875, 255373730⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198196, 202002, 254731258⟩ CTN.nil) ⟨198196, 202770, 250888842⟩ CTN.nil) ⟨198196, 203634, 246652340⟩ (CTN.node (CTN.node CTN.nil ⟨198196, 203890, 245414287⟩ CTN.nil) ⟨198196, 204498, 242504906⟩ CTN.nil)) ⟨198196, 204800, 241075816⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198198, 201940, 255859823⟩ CTN.nil) ⟨198198, 203892, 246189004⟩ CTN.nil) ⟨198208, 202400, 257596835⟩ (CTN.node CTN.nil ⟨198208, 202976, 254681414⟩ CTN.nil))) ⟨198208, 204800, 245717359⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198211, 200930, 266488592⟩ CTN.nil) ⟨198211, 201362, 264205997⟩ CTN.nil) ⟨198212, 200899, 267074249⟩ (CTN.node (CTN.node CTN.nil ⟨198212, 201315, 264870588⟩ CTN.nil) ⟨198212, 201986, 261363814⟩ CTN.nil)) ⟨198212, 202754, 257421041⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198212, 203586, 253233256⟩ CTN.nil) ⟨198212, 204418, 249130308⟩ CTN.nil) ⟨198212, 204800, 247274354⟩ (CTN.node CTN.nil ⟨198214, 200917, 267820944⟩ CTN.nil))))) ⟨198216, 204800, 248836257⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198224, 200432, 274699800⟩ CTN.nil) ⟨198224, 200864, 272341043⟩ CTN.nil) ⟨198224, 204800, 251974780⟩ (CTN.node (CTN.node CTN.nil ⟨198240, 201424, 276093040⟩ CTN.nil) ⟨198240, 201508, 275632346⟩ CTN.nil)) ⟨198240, 201856, 273733963⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198240, 201920, 273386617⟩ CTN.nil) ⟨198240, 202432, 270627593⟩ CTN.nil) ⟨198240, 203008, 267565174⟩ (CTN.node CTN.nil ⟨198240, 203584, 264545962⟩ CTN.nil))) ⟨198242, 201216, 278093900⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198248, 204800, 261508078⟩ CTN.nil) ⟨198258, 202992, 275132446⟩ CTN.nil) ⟨198260, 201592, 283727045⟩ (CTN.node (CTN.node CTN.nil ⟨198260, 202098, 280892422⟩ CTN.nil) ⟨198260, 203186, 274916364⟩ CTN.nil)) ⟨198260, 204800, 266340931⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198261, 201396, 285267478⟩ CTN.nil) ⟨198262, 201109, 287337215⟩ CTN.nil) ⟨198262, 201125, 287245670⟩ (CTN.node CTN.nil ⟨198262, 201541, 284878228⟩ CTN.nil)))) ⟨198264, 201020, 288720924⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198264, 203190, 276567497⟩ CTN.nil) ⟨198264, 204800, 267961688⟩ CTN.nil) ⟨198268, 201600, 287139735⟩ (CTN.node (CTN.node CTN.nil ⟨198272, 201088, 291833793⟩ CTN.nil) ⟨198272, 201344, 290350418⟩ CTN.nil)) ⟨198272, 201376, 290165660⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198272, 201504, 289428095⟩ CTN.nil) ⟨198272, 201920, 287047141⟩ CTN.nil) ⟨198272, 201952, 286865007⟩ (CTN.node CTN.nil ⟨198272, 202496, 283790719⟩ CTN.nil))) ⟨198272, 202784, 282179830⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198272, 203040, 280757516⟩ CTN.nil) ⟨198272, 203072, 280580357⟩ CTN.nil) ⟨198272, 203904, 276022906⟩ (CTN.node CTN.nil ⟨198272, 204800, 271217907⟩ CTN.nil)) ⟨198274, 202944, 282137294⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198277, 200564, 297123404⟩ CTN.nil) ⟨198277, 201556, 291309280⟩ CTN.nil) ⟨198277, 201972, 288913468⟩ (CTN.node CTN.nil ⟨198288, 204800, 277789161⟩ CTN.nil))))))) ⟨198290, 204800, 278616080⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198292, 201011, 301147024⟩ CTN.nil) ⟨198292, 201443, 298568601⟩ CTN.nil) ⟨198292, 202130, 294524780⟩ (CTN.node (CTN.node CTN.nil ⟨198293, 200212, 306443619⟩ CTN.nil) ⟨198293, 200628, 303906461⟩ CTN.nil)) ⟨198293, 201428, 299100699⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198293, 201460, 298910452⟩ CTN.nil) ⟨198293, 202548, 292531133⟩ CTN.nil) ⟨198294, 204800, 280273594⟩ (CTN.node CTN.nil ⟨198300, 202144, 297946370⟩ CTN.nil))) ⟨198304, 201408, 304116589⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198304, 201920, 301039664⟩ CTN.nil) ⟨198304, 201984, 300657791⟩ CTN.nil) ⟨198304, 203648, 290938279⟩ (CTN.node (CTN.node CTN.nil ⟨198304, 203840, 289842236⟩ CTN.nil) ⟨198304, 204800, 284438812⟩ CTN.nil)) ⟨198311, 202582, 300183423⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198320, 201088, 313299085⟩ CTN.nil) ⟨198324, 200675, 317727818⟩ CTN.nil) ⟨198324, 201091, 315103288⟩ (CTN.node CTN.nil ⟨198324, 201507, 312505809⟩ CTN.nil)))) ⟨198324, 202194, 308274558⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198324, 203026, 303245693⟩ CTN.nil) ⟨198324, 203858, 298318982⟩ CTN.nil) ⟨198324, 204018, 297383040⟩ (CTN.node (CTN.node CTN.nil ⟨198324, 204690, 293491945⟩ CTN.nil) ⟨198324, 204800, 292861086⟩ CTN.nil)) ⟨198326, 204800, 293710046⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198328, 204022, 299084934⟩ CTN.nil) ⟨198328, 204800, 294560230⟩ CTN.nil) ⟨198336, 201104, 320520663⟩ (CTN.node CTN.nil ⟨198336, 201440, 318384647⟩ CTN.nil))) ⟨198336, 201520, 317878698⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198336, 201568, 317575610⟩ CTN.nil) ⟨198336, 202528, 311589044⟩ CTN.nil) ⟨198336, 202560, 311391933⟩ (CTN.node (CTN.node CTN.nil ⟨198336, 202848, 309624928⟩ CTN.nil) ⟨198336, 203872, 303442903⟩ CTN.nil)) ⟨198336, 204800, 297973208⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198338, 202080, 315268464⟩ CTN.nil) ⟨198338, 202944, 309926817⟩ CTN.nil) ⟨198340, 202914, 311000285⟩ (CTN.node CTN.nil ⟨198340, 203746, 305944821⟩ CTN.nil))))) ⟨198340, 204800, 299687039⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198354, 202064, 322644525⟩ CTN.nil) ⟨198354, 202896, 317377883⟩ CTN.nil) ⟨198356, 202194, 322727411⟩ (CTN.node (CTN.node CTN.nil ⟨198356, 202962, 317863918⟩ CTN.nil) ⟨198357, 201204, 329600898⟩ CTN.nil)) ⟨198357, 201492, 327717972⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198358, 202932, 318953177⟩ CTN.nil) ⟨198359, 202038, 325102757⟩ CTN.nil) ⟨198360, 202836, 320462221⟩ (CTN.node CTN.nil ⟨198368, 201440, 333180902⟩ CTN.nil))) ⟨198368, 202016, 329392147⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198368, 202784, 324423874⟩ CTN.nil) ⟨198368, 203648, 318946036⟩ CTN.nil) ⟨198368, 203712, 318544887⟩ (CTN.node (CTN.node CTN.nil ⟨198368, 203904, 317345220⟩ CTN.nil) ⟨198372, 200675, 340199307⟩ CTN.nil)) ⟨198384, 201152, 342662533⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198384, 201568, 339838730⟩ CTN.nil) ⟨198387, 201138, 344186611⟩ CTN.nil) ⟨198388, 201107, 344876298⟩ (CTN.node CTN.nil ⟨198388, 201539, 341924871⟩ CTN.nil)))) ⟨198388, 202083, 338253036⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198388, 202226, 337296024⟩ CTN.nil) ⟨198388, 202994, 332213782⟩ CTN.nil) ⟨198388, 204114, 324972575⟩ (CTN.node (CTN.node CTN.nil ⟨198388, 204690, 321325358⟩ CTN.nil) ⟨198388, 204800, 320634671⟩ CTN.nil)) ⟨198389, 201524, 342500335⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198390, 204800, 321522773⟩ CTN.nil) ⟨198392, 203350, 331719174⟩ CTN.nil) ⟨198400, 204768, 326185701⟩ (CTN.node CTN.nil ⟨198400, 204800, 325981618⟩ CTN.nil))) ⟨198416, 200624, 361837635⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198416, 201056, 358733619⟩ CTN.nil) ⟨198422, 201285, 360016239⟩ CTN.nil) ⟨198424, 204800, 336807470⟩ (CTN.node CTN.nil ⟨198432, 200688, 369267276⟩ CTN.nil)) ⟨198432, 200832, 368207903⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198432, 201248, 365168764⟩ CTN.nil) ⟨198435, 201138, 367445137⟩ CTN.nil) ⟨198436, 202848, 355670857⟩ (CTN.node CTN.nil ⟨198437, 201588, 365147512⟩ CTN.nil)))))) ⟨198448, 201120, 374008493⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198448, 203960, 353581999⟩ CTN.nil) ⟨198452, 203410, 359328689⟩ CTN.nil) ⟨198452, 204800, 349659889⟩ (CTN.node (CTN.node CTN.nil ⟨198453, 200756, 379238678⟩ CTN.nil) ⟨198454, 202133, 369484976⟩ CTN.nil)) ⟨198454, 202260, 368556610⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198454, 202292, 368323152⟩ CTN.nil) ⟨198454, 203124, 362317606⟩ CTN.nil) ⟨198454, 203380, 360494416⟩ (CTN.node CTN.nil ⟨198454, 204788, 350669361⟩ CTN.nil))) ⟨198456, 204182, 355796185⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198456, 204800, 351515478⟩ CTN.nil) ⟨198464, 200848, 384076769⟩ CTN.nil) ⟨198464, 201232, 381149575⟩ (CTN.node (CTN.node CTN.nil ⟨198464, 202880, 368899244⟩ CTN.nil) ⟨198464, 203744, 362673371⟩ CTN.nil)) ⟨198464, 204608, 356578322⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198464, 204800, 355241300⟩ CTN.nil) ⟨198466, 202240, 374580129⟩ CTN.nil) ⟨198469, 200820, 386821096⟩ (CTN.node CTN.nil ⟨198469, 201620, 380709986⟩ CTN.nil)))) ⟨198469, 201652, 380468062⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198469, 202740, 372355796⟩ CTN.nil) ⟨198470, 202244, 376519736⟩ CTN.nil) ⟨198472, 204800, 358986641⟩ (CTN.node (CTN.node CTN.nil ⟨198480, 201248, 389083578⟩ CTN.nil) ⟨198482, 203248, 374947289⟩ CTN.nil)) ⟨198482, 203544, 372768145⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198485, 201604, 388855539⟩ CTN.nil) ⟨198486, 202292, 384082913⟩ CTN.nil) ⟨198486, 204800, 365587946⟩ (CTN.node CTN.nil ⟨198496, 202340, 388705548⟩ CTN.nil))) ⟨198496, 203172, 382369158⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198496, 203264, 381676455⟩ CTN.nil) ⟨198496, 204800, 370339742⟩ CTN.nil) ⟨198503, 202198, 393320208⟩ (CTN.node CTN.nil ⟨198508, 204800, 376082121⟩ CTN.nil)) ⟨198512, 202424, 396092960⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198512, 204800, 378005996⟩ CTN.nil) ⟨198516, 204210, 384350390⟩ CTN.nil) ⟨198516, 204242, 384109257⟩ (CTN.node CTN.nil ⟨198516, 204592, 381484172⟩ CTN.nil))))) ⟨198516, 204800, 379934745⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198517, 201780, 403740265⟩ CTN.nil) ⟨198518, 201365, 407600518⟩ CTN.nil) ⟨198518, 202773, 396382086⟩ (CTN.node (CTN.node CTN.nil ⟨198518, 203124, 393645772⟩ CTN.nil) ⟨198518, 203444, 391171678⟩ CTN.nil)) ⟨198520, 202432, 400076804⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198520, 204800, 381868366⟩ CTN.nil) ⟨198528, 201712, 409952800⟩ CTN.nil) ⟨198528, 202720, 401848983⟩ (CTN.node CTN.nil ⟨198528, 204736, 386233418⟩ CTN.nil))) ⟨198528, 204800, 385750226⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198532, 201235, 415949049⟩ CTN.nil) ⟨198532, 204800, 387698463⟩ CTN.nil) ⟨198533, 201684, 412771148⟩ (CTN.node (CTN.node CTN.nil ⟨198533, 201812, 411723539⟩ CTN.nil) ⟨198534, 203076, 402059739⟩ CTN.nil)) ⟨198548, 200883, 427348336⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198548, 201299, 423821953⟩ CTN.nil) ⟨198548, 204800, 395540112⟩ CTN.nil) ⟨198550, 203124, 409793423⟩ (CTN.node CTN.nil ⟨198550, 204800, 396525796⟩ CTN.nil)))) ⟨198560, 200768, 434753781⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198560, 201632, 427339925⟩ CTN.nil) ⟨198560, 201664, 427068386⟩ CTN.nil) ⟨198560, 202176, 422752951⟩ (CTN.node (CTN.node CTN.nil ⟨198560, 202208, 422485050⟩ CTN.nil) ⟨198560, 202240, 422217362⟩ CTN.nil)) ⟨198560, 203072, 415331310⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198560, 203328, 413240819⟩ CTN.nil) ⟨198565, 201716, 429268024⟩ CTN.nil) ⟨198566, 202372, 424243923⟩ (CTN.node CTN.nil ⟨198578, 202384, 430433202⟩ CTN.nil))) ⟨198580, 204656, 412617823⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198580, 204800, 411457054⟩ CTN.nil) ⟨198582, 204800, 412462202⟩ CTN.nil) ⟨198592, 200992, 450101821⟩ (CTN.node CTN.nil ⟨198592, 201696, 443842161⟩ CTN.nil)) ⟨198592, 201824, 442715761⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198592, 202208, 439357940⟩ CTN.nil) ⟨198592, 202240, 439079561⟩ CTN.nil) ⟨198592, 202272, 438801403⟩ (CTN.node CTN.nil ⟨198592, 202784, 434380687⟩ CTN.nil))))))))

noncomputable def tab14 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198592, 203104, 431646000⟩ CTN.nil) ⟨198592, 203392, 429203163⟩ CTN.nil) ⟨198592, 204128, 423038436⟩ (CTN.node (CTN.node CTN.nil ⟨198592, 204224, 422242525⟩ CTN.nil) ⟨198592, 204800, 417506173⟩ CTN.nil)) ⟨198595, 201362, 448423978⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198596, 204608, 421111265⟩ CTN.nil) ⟨198596, 204800, 419532271⟩ CTN.nil) ⟨198608, 201376, 455375657⟩ (CTN.node CTN.nil ⟨198608, 203020, 440784728⟩ CTN.nil))) ⟨198612, 200899, 461931129⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198612, 204800, 427685267⟩ CTN.nil) ⟨198614, 202309, 450246571⟩ CTN.nil) ⟨198614, 202452, 448974122⟩ (CTN.node (CTN.node CTN.nil ⟨198614, 202484, 448689994⟩ CTN.nil) ⟨198614, 203316, 441380943⟩ CTN.nil)) ⟨198614, 203572, 439162002⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198614, 204800, 428709859⟩ CTN.nil) ⟨198620, 202464, 452093479⟩ CTN.nil) ⟨198620, 203296, 444728264⟩ (CTN.node CTN.nil ⟨198624, 201392, 464012932⟩ CTN.nil)))) ⟨198624, 202240, 456268993⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198624, 202972, 449713919⟩ CTN.nil) ⟨198624, 203136, 448261474⟩ CTN.nil) ⟨198624, 204800, 433851033⟩ (CTN.node (CTN.node CTN.nil ⟨198628, 201315, 466936121⟩ CTN.nil) ⟨198628, 201331, 466787508⟩ CTN.nil)) ⟨198630, 203204, 450858890⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198630, 204036, 443540334⟩ CTN.nil) ⟨198636, 204800, 440060510⟩ CTN.nil) ⟨198642, 202480, 463872933⟩ (CTN.node CTN.nil ⟨198642, 203216, 457180420⟩ CTN.nil))) ⟨198642, 204144, 448913168⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198643, 201362, 474832944⟩ CTN.nil) ⟨198644, 203570, 455072739⟩ CTN.nil) ⟨198644, 204720, 444920119⟩ (CTN.node (CTN.node CTN.nil ⟨198644, 204800, 444224437⟩ CTN.nil) ⟨198646, 202484, 466020305⟩ CTN.nil)) ⟨198648, 201404, 477228094⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198648, 204800, 446313681⟩ CTN.nil) ⟨198652, 201984, 473976428⟩ CTN.nil) ⟨198656, 202304, 473185269⟩ (CTN.node CTN.nil ⟨198656, 203072, 466058232⟩ CTN.nil))))) ⟨198656, 203424, 462836544⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198656, 204192, 455903499⟩ CTN.nil) ⟨198656, 204800, 450506728⟩ CTN.nil) ⟨198672, 201856, 486354180⟩ (CTN.node (CTN.node CTN.nil ⟨198672, 204800, 458951035⟩ CTN.nil) ⟨198674, 201809, 487933413⟩ CTN.nil)) ⟨198674, 202480, 481489106⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198674, 203248, 474243259⟩ CTN.nil) ⟨198674, 204080, 466546771⟩ CTN.nil) ⟨198676, 204560, 463244693⟩ (CTN.node CTN.nil ⟨198678, 201525, 492960821⟩ CTN.nil))) ⟨198678, 201941, 488905946⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198678, 202949, 479252261⟩ CTN.nil) ⟨198678, 203636, 472809143⟩ CTN.nil) ⟨198688, 201920, 494756294⟩ (CTN.node (CTN.node CTN.nil ⟨198688, 204224, 472776118⟩ CTN.nil) ⟨198688, 204800, 467472925⟩ CTN.nil)) ⟨198692, 204200, 475166629⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198693, 201972, 497078715⟩ CTN.nil) ⟨198696, 204800, 471762950⟩ CTN.nil) ⟨198704, 204800, 476072355⟩ (CTN.node CTN.nil ⟨198706, 204800, 477152733⟩ CTN.nil)))) ⟨198708, 204402, 481974859⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198708, 204434, 481672763⟩ CTN.nil) ⟨198708, 204800, 478234323⟩ CTN.nil) ⟨198710, 203316, 493483972⟩ (CTN.node (CTN.node CTN.nil ⟨198710, 204800, 479317123⟩ CTN.nil) ⟨198716, 202754, 502374738⟩ CTN.nil)) ⟨198716, 204800, 482572786⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198720, 202912, 503068523⟩ CTN.nil) ⟨198720, 204800, 484749281⟩ CTN.nil) ⟨198722, 204096, 492586280⟩ (CTN.node CTN.nil ⟨198724, 201443, 520254776⟩ CTN.nil))) ⟨198724, 201730, 517296487⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198724, 202594, 508516760⟩ CTN.nil) ⟨198724, 204672, 488151432⟩ CTN.nil) ⟨198728, 204800, 489116790⟩ (CTN.node CTN.nil ⟨198740, 201507, 528955521⟩ CTN.nil)) ⟨198740, 203314, 510375650⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198740, 204688, 496791597⟩ CTN.nil) ⟨198742, 204800, 496806506⟩ CTN.nil) ⟨198752, 201520, 535892928⟩ (CTN.node CTN.nil ⟨198752, 201984, 530979095⟩ CTN.nil)))))) ⟨198752, 204032, 509951634⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198768, 201536, 545223817⟩ CTN.nil) ⟨198768, 201952, 540739294⟩ CTN.nil) ⟨198768, 204800, 511244579⟩ (CTN.node (CTN.node CTN.nil ⟨198771, 201906, 543010467⟩ CTN.nil) ⟨198772, 202451, 537765951⟩ CTN.nil)) ⟨198772, 204800, 513483946⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198773, 201620, 547295632⟩ CTN.nil) ⟨198773, 202036, 542795939⟩ CTN.nil) ⟨198774, 203700, 525826273⟩ (CTN.node CTN.nil ⟨198776, 204800, 515728144⟩ CTN.nil))) ⟨198784, 202976, 539209664⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198784, 204800, 520231031⟩ CTN.nil) ⟨198792, 204800, 524753234⟩ CTN.nil) ⟨198800, 201568, 564114819⟩ (CTN.node (CTN.node CTN.nil ⟨198802, 202640, 553444311⟩ CTN.nil) ⟨198803, 201970, 561436939⟩ CTN.nil)) ⟨198804, 204800, 531572743⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198816, 201584, 573674680⟩ CTN.nil) ⟨198816, 202000, 568957266⟩ CTN.nil) ⟨198816, 202558, 562705481⟩ (CTN.node CTN.nil ⟨198816, 203584, 551432782⟩ CTN.nil)))) ⟨198816, 204800, 538435678⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198820, 201539, 576637736⟩ CTN.nil) ⟨198820, 202594, 564704230⟩ CTN.nil) ⟨198828, 204800, 545342019⟩ (CTN.node (CTN.node CTN.nil ⟨198832, 202744, 570238907⟩ CTN.nil) ⟨198832, 204800, 547653775⟩ CTN.nil)) ⟨198834, 204800, 548811460⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198835, 201970, 580878799⟩ CTN.nil) ⟨198836, 203794, 560924843⟩ CTN.nil) ⟨198836, 204800, 549970350⟩ (CTN.node CTN.nil ⟨198838, 201701, 585837184⟩ CTN.nil))) ⟨198838, 202117, 581022544⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198838, 203093, 569919390⟩ CTN.nil) ⟨198838, 204532, 554028504⟩ CTN.nil) ⟨198840, 202752, 574977269⟩ (CTN.node (CTN.node CTN.nil ⟨198848, 201232, 597568103⟩ CTN.nil) ⟨198848, 201248, 597377834⟩ CTN.nil)) ⟨198848, 201664, 592457325⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198848, 201920, 589454495⟩ CTN.nil) ⟨198848, 201952, 589080480⟩ CTN.nil) ⟨198848, 202080, 587587386⟩ (CTN.node CTN.nil ⟨198848, 202496, 582767396⟩ CTN.nil))))) ⟨198848, 202760, 579734184⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198848, 203072, 576174882⟩ CTN.nil) ⟨198848, 204800, 556948987⟩ CTN.nil) ⟨198856, 204800, 561625495⟩ (CTN.node (CTN.node CTN.nil ⟨198864, 204800, 566321264⟩ CTN.nil) ⟨198866, 203472, 582479258⟩ CTN.nil)) ⟨198866, 203568, 581379834⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198866, 204400, 571959347⟩ CTN.nil) ⟨198867, 202002, 600265737⟩ CTN.nil) ⟨198867, 203122, 587118310⟩ (CTN.node CTN.nil ⟨198868, 204274, 574564030⟩ CTN.nil))) ⟨198868, 204800, 568676368⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198870, 204800, 569855725⟩ CTN.nil) ⟨198880, 201984, 608601553⟩ CTN.nil) ⟨198880, 202496, 602461472⟩ (CTN.node (CTN.node CTN.nil ⟨198880, 203072, 595646169⟩ CTN.nil) ⟨198880, 204224, 582302317⟩ CTN.nil)) ⟨198880, 204416, 580114817⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198882, 204800, 576957128⟩ CTN.nil) ⟨198883, 201986, 610459168⟩ CTN.nil) ⟨198892, 204800, 582908030⟩ (CTN.node CTN.nil ⟨198896, 201664, 622612460⟩ CTN.nil)))) ⟨198896, 203576, 599519426⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198898, 202736, 610776372⟩ CTN.nil) ⟨198898, 203504, 601596430⟩ CTN.nil) ⟨198898, 204096, 594637728⟩ (CTN.node (CTN.node CTN.nil ⟨198898, 204336, 591845318⟩ CTN.nil) ⟨198900, 204626, 589694470⟩ CTN.nil)) ⟨198900, 204800, 587690386⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198904, 203584, 604332714⟩ CTN.nil) ⟨198904, 204800, 590088774⟩ CTN.nil) ⟨198912, 201680, 632626806⟩ (CTN.node CTN.nil ⟨198912, 202096, 627427090⟩ CTN.nil))) ⟨198912, 202528, 622083818⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198912, 202560, 621690288⟩ CTN.nil) ⟨198912, 203104, 615047647⟩ CTN.nil) ⟨198912, 203592, 609164156⟩ (CTN.node CTN.nil ⟨198912, 203680, 608110700⟩ CTN.nil)) ⟨198912, 203712, 607728189⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198912, 204800, 594899963⟩ CTN.nil) ⟨198916, 204800, 597312763⟩ CTN.nil) ⟨198930, 204656, 607504397⟩ (CTN.node CTN.nil ⟨198930, 204800, 605795377⟩ CTN.nil))))))) ⟨198932, 202738, 632119956⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198933, 202196, 639574873⟩ CTN.nil) ⟨198934, 203892, 619151338⟩ CTN.nil) ⟨198936, 204800, 609448784⟩ (CTN.node (CTN.node CTN.nil ⟨198944, 203360, 631946377⟩ CTN.nil) ⟨198944, 204224, 621306060⟩ CTN.nil)) ⟨198944, 204480, 618196465⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198944, 204800, 614336786⟩ CTN.nil) ⟨198949, 202228, 649458250⟩ CTN.nil) ⟨198956, 204800, 621704760⟩ (CTN.node CTN.nil ⟨198960, 201728, 663121061⟩ CTN.nil))) ⟨198960, 202144, 657671999⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198960, 204800, 624170340⟩ CTN.nil) ⟨198964, 202659, 653580061⟩ CTN.nil) ⟨198964, 202770, 652148216⟩ (CTN.node (CTN.node CTN.nil ⟨198964, 202802, 651736160⟩ CTN.nil) ⟨198964, 203634, 641136058⟩ CTN.nil)) ⟨198964, 203890, 637917924⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨198964, 204466, 630750643⟩ CTN.nil) ⟨198964, 204800, 626640714⟩ CTN.nil) ⟨198972, 204800, 631595836⟩ (CTN.node CTN.nil ⟨198976, 204512, 637664528⟩ CTN.nil)))) ⟨198976, 204800, 634080582⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨198979, 202130, 670266972⟩ CTN.nil) ⟨198980, 202754, 662691215⟩ CTN.nil) ⟨198996, 204800, 646576139⟩ (CTN.node (CTN.node CTN.nil ⟨198998, 203269, 667597718⟩ CTN.nil) ⟨198998, 204724, 648796046⟩ CTN.nil)) ⟨199008, 201408, 699384366⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199008, 202240, 687931165⟩ CTN.nil) ⟨199008, 204544, 657416077⟩ CTN.nil) ⟨199008, 204800, 654130900⟩ (CTN.node CTN.nil ⟨199011, 202194, 690553415⟩ CTN.nil))) ⟨199016, 203428, 677179243⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199024, 204800, 664270860⟩ CTN.nil) ⟨199028, 202291, 700565750⟩ CTN.nil) ⟨199028, 202834, 693084112⟩ (CTN.node (CTN.node CTN.nil ⟨199028, 203602, 682672088⟩ CTN.nil) ⟨199028, 204722, 667835944⟩ CTN.nil)) ⟨199028, 204800, 666817798⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199030, 202709, 696126289⟩ CTN.nil) ⟨199032, 204800, 669369514⟩ CTN.nil) ⟨199040, 201808, 715440878⟩ (CTN.node CTN.nil ⟨199040, 204800, 674487275⟩ CTN.nil))))) ⟨199044, 203586, 693369181⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199044, 204418, 682135042⟩ CTN.nil) ⟨199044, 204800, 677053318⟩ CTN.nil) ⟨199056, 201824, 726128035⟩ (CTN.node (CTN.node CTN.nil ⟨199058, 204800, 686072056⟩ CTN.nil) ⟨199060, 203634, 703265232⟩ CTN.nil)) ⟨199060, 204466, 691873420⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199060, 204498, 691439898⟩ CTN.nil) ⟨199072, 203840, 708354837⟩ CTN.nil) ⟨199075, 202226, 733325912⟩ (CTN.node CTN.nil ⟨199075, 203346, 717281705⟩ CTN.nil))) ⟨199092, 204800, 708217917⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199100, 204800, 713478734⟩ CTN.nil) ⟨199104, 202288, 752403944⟩ CTN.nil) ⟨199104, 202720, 746002415⟩ (CTN.node (CTN.node CTN.nil ⟨199104, 202784, 745059841⟩ CTN.nil) ⟨199104, 203296, 737572600⟩ CTN.nil)) ⟨199104, 203328, 737107778⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199104, 204736, 717013293⟩ CTN.nil) ⟨199104, 204800, 716116283⟩ CTN.nil) ⟨199109, 202388, 754380188⟩ (CTN.node CTN.nil ⟨199124, 202962, 756192744⟩ CTN.nil)))) ⟨199125, 203380, 750671930⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199136, 202208, 775981915⟩ CTN.nil) ⟨199136, 202240, 775490250⟩ CTN.nil) ⟨199136, 202784, 767191229⟩ (CTN.node (CTN.node CTN.nil ⟨199136, 202816, 766706517⟩ CTN.nil) ⟨199136, 203648, 754237345⟩ CTN.nil)) ⟨199152, 204558, 751689025⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199152, 204800, 748137812⟩ CTN.nil) ⟨199156, 202994, 777952209⟩ CTN.nil) ⟨199156, 203026, 777461208⟩ (CTN.node CTN.nil ⟨199156, 203858, 764830108⟩ CTN.nil))) ⟨199156, 204114, 760995317⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199156, 204690, 752454550⟩ CTN.nil) ⟨199156, 204800, 750837154⟩ CTN.nil) ⟨199158, 204800, 752188605⟩ (CTN.node CTN.nil ⟨199160, 204800, 753541242⟩ CTN.nil)) ⟨199168, 202272, 797675188⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199168, 202400, 795656588⟩ CTN.nil) ⟨199168, 202784, 789638990⟩ CTN.nil) ⟨199168, 202816, 789140096⟩ (CTN.node CTN.nil ⟨199168, 203360, 780718885⟩ CTN.nil)))))) ⟨199168, 203392, 780227027⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199168, 203936, 771924415⟩ CTN.nil) ⟨199168, 204704, 760390232⟩ CTN.nil) ⟨199168, 204800, 758963653⟩ (CTN.node (CTN.node CTN.nil ⟨199172, 202978, 789437862⟩ CTN.nil) ⟨199172, 203746, 777586696⟩ CTN.nil)) ⟨199172, 204578, 764997863⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199172, 204800, 761681973⟩ CTN.nil) ⟨199180, 204800, 767132840⟩ CTN.nil) ⟨199184, 201952, 814280446⟩ (CTN.node CTN.nil ⟨199184, 204800, 769865383⟩ CTN.nil))) ⟨199186, 202896, 800632076⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199189, 203444, 794138897⟩ CTN.nil) ⟨199190, 202885, 803650656⟩ CTN.nil) ⟨199192, 204800, 775344687⟩ (CTN.node (CTN.node CTN.nil ⟨199196, 204800, 778091444⟩ CTN.nil) ⟨199200, 201968, 825629288⟩ CTN.nil)) ⟨199200, 202384, 818852890⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199200, 202816, 811889302⟩ CTN.nil) ⟨199200, 203392, 802719289⟩ CTN.nil) ⟨199200, 204800, 780842937⟩ (CTN.node CTN.nil ⟨199202, 202944, 811268926⟩ CTN.nil)))) ⟨199216, 204728, 793012279⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199220, 202499, 831460539⟩ CTN.nil) ⟨199220, 203826, 809990402⟩ CTN.nil) ⟨199220, 204800, 794671403⟩ (CTN.node (CTN.node CTN.nil ⟨199224, 204736, 798450179⟩ CTN.nil) ⟨199224, 204800, 797451289⟩ CTN.nil)) ⟨199232, 202000, 848545269⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199232, 203648, 821374484⟩ CTN.nil) ⟨199232, 203912, 817123528⟩ CTN.nil) ⟨199232, 204744, 803905296⟩ (CTN.node CTN.nil ⟨199232, 204800, 803025244⟩ CTN.nil))) ⟨199240, 204800, 808618104⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199248, 202432, 853054375⟩ CTN.nil) ⟨199252, 203858, 832269615⟩ CTN.nil) ⟨199252, 204690, 818802832⟩ (CTN.node CTN.nil ⟨199264, 201664, 878140498⟩ CTN.nil)) ⟨199264, 202080, 870922273⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199264, 202496, 863778082⟩ CTN.nil) ⟨199264, 204800, 825510025⟩ CTN.nil) ⟨199266, 203968, 840518329⟩ (CTN.node CTN.nil ⟨199268, 203616, 847803040⟩ CTN.nil))))) ⟨199280, 204800, 836865670⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199284, 204800, 839716367⟩ CTN.nil) ⟨199286, 204212, 850885971⟩ CTN.nil) ⟨199288, 204800, 842571775⟩ (CTN.node (CTN.node CTN.nil ⟨199294, 203900, 861934796⟩ CTN.nil) ⟨199296, 204800, 848296723⟩ CTN.nil)) ⟨199300, 204800, 851166260⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199301, 203572, 872653712⟩ CTN.nil) ⟨199318, 204800, 864137416⟩ CTN.nil) ⟨199328, 202096, 919029150⟩ (CTN.node CTN.nil ⟨199328, 203744, 889615174⟩ CTN.nil))) ⟨199328, 204608, 874664397⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199328, 204800, 871384765⟩ CTN.nil) ⟨199330, 203968, 887185441⟩ CTN.nil) ⟨199344, 202528, 923392049⟩ (CTN.node (CTN.node CTN.nil ⟨199344, 204800, 883041609⟩ CTN.nil) ⟨199345, 202480, 925034302⟩ CTN.nil)) ⟨199346, 204800, 884503998⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199348, 204800, 885967560⟩ CTN.nil) ⟨199349, 202612, 925678655⟩ CTN.nil) ⟨199350, 204800, 887432295⟩ (CTN.node CTN.nil ⟨199360, 204128, 906629974⟩ CTN.nil)))) ⟨199360, 204800, 894773569⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199365, 203636, 919201950⟩ CTN.nil) ⟨199376, 202144, 955240290⟩ CTN.nil) ⟨199380, 203792, 927697104⟩ (CTN.node (CTN.node CTN.nil ⟨199380, 204800, 909544038⟩ CTN.nil) ⟨199392, 202576, 959520359⟩ CTN.nil)) ⟨199392, 203008, 951368237⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199392, 203072, 950167891⟩ CTN.nil) ⟨199392, 203584, 940632975⟩ CTN.nil) ⟨199392, 204160, 930048746⟩ (CTN.node CTN.nil ⟨199408, 204800, 930419398⟩ CTN.nil))) ⟨199416, 204800, 936425887⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199424, 201824, 999357541⟩ CTN.nil) ⟨199424, 202240, 991149420⟩ CTN.nil) ⟨199424, 202656, 983025420⟩ (CTN.node CTN.nil ⟨199424, 203072, 974984507⟩ CTN.nil)) ⟨199424, 203104, 974369387⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199424, 203648, 963986209⟩ CTN.nil) ⟨199424, 203936, 958545232⟩ CTN.nil) ⟨199424, 204192, 953741008⟩ (CTN.node CTN.nil ⟨199424, 204224, 953142598⟩ CTN.nil))))))))

noncomputable def tab15 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199442, 203248, 985653816⟩ CTN.nil) ⟨199444, 202707, 997815959⟩ CTN.nil) ⟨199446, 204404, 966580534⟩ (CTN.node (CTN.node CTN.nil ⟨199456, 203072, 1000110383⟩ CTN.nil) ⟨199456, 203648, 988828653⟩ CTN.nil)) ⟨199456, 204800, 966738541⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199462, 204036, 985975074⟩ CTN.nil) ⟨199472, 202240, 1029580791⟩ CTN.nil) ⟨199474, 203312, 1009591828⟩ (CTN.node CTN.nil ⟨199474, 204800, 980531379⟩ CTN.nil))) ⟨199478, 204800, 983609261⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199480, 204800, 985149947⟩ CTN.nil) ⟨199488, 202256, 1042217761⟩ CTN.nil) ⟨199488, 203104, 1024897850⟩ (CTN.node (CTN.node CTN.nil ⟨199488, 203680, 1013338319⟩ CTN.nil) ⟨199488, 204256, 1001941343⟩ CTN.nil)) ⟨199488, 204800, 991324325⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199492, 204800, 994418491⟩ CTN.nil) ⟨199504, 204800, 1003728883⟩ CTN.nil) ⟨199506, 204080, 1019565343⟩ (CTN.node CTN.nil ⟨199509, 203764, 1028296830⟩ CTN.nil)))) ⟨199510, 204800, 1008399761⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199520, 203936, 1033561476⟩ CTN.nil) ⟨199520, 204800, 1016207776⟩ CTN.nil) ⟨199525, 202804, 1060934203⟩ (CTN.node (CTN.node CTN.nil ⟨199536, 202720, 1071694852⟩ CTN.nil) ⟨199536, 204800, 1028760925⟩ CTN.nil)) ⟨199538, 204112, 1044315794⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199538, 204800, 1030335285⟩ CTN.nil) ⟨199540, 204800, 1031910804⟩ CTN.nil) ⟨199544, 204800, 1035065318⟩ (CTN.node CTN.nil ⟨199552, 204800, 1041388244⟩ CTN.nil))) ⟨199554, 204096, 1057455807⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199554, 204800, 1042971870⟩ CTN.nil) ⟨199556, 204800, 1044556654⟩ CTN.nil) ⟨199564, 204800, 1050907358⟩ (CTN.node (CTN.node CTN.nil ⟨199568, 204800, 1054089651⟩ CTN.nil) ⟨199570, 204800, 1055682532⟩ CTN.nil)) ⟨199584, 202816, 1109283685⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199600, 204800, 1079714391⟩ CTN.nil) ⟨199604, 202867, 1124862602⟩ CTN.nil) ⟨199606, 204532, 1090254927⟩ (CTN.node CTN.nil ⟨199616, 202384, 1145825076⟩ CTN.nil))))) ⟨199616, 204800, 1092637553⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199632, 202400, 1159087578⟩ CTN.nil) ⟨199632, 202816, 1149594557⟩ CTN.nil) ⟨199636, 202915, 1150733502⟩ (CTN.node (CTN.node CTN.nil ⟨199638, 204800, 1110527296⟩ CTN.nil) ⟨199644, 203992, 1133231736⟩ CTN.nil)) ⟨199644, 204800, 1115430485⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199664, 204800, 1131849164⟩ CTN.nil) ⟨199666, 203504, 1162687306⟩ CTN.nil) ⟨199668, 204800, 1135146684⟩ (CTN.node CTN.nil ⟨199670, 204800, 1136797166⟩ CTN.nil))) ⟨199680, 203296, 1179375340⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199680, 203872, 1166086009⟩ CTN.nil) ⟨199680, 203904, 1165353217⟩ CTN.nil) ⟨199680, 204448, 1152983382⟩ (CTN.node (CTN.node CTN.nil ⟨199680, 204800, 1145066785⟩ CTN.nil) ⟨199685, 203956, 1168378356⟩ CTN.nil)) ⟨199696, 204800, 1158357798⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199698, 204800, 1160024330⟩ CTN.nil) ⟨199699, 203378, 1193710069⟩ CTN.nil) ⟨199720, 204800, 1178431732⟩ (CTN.node CTN.nil ⟨199728, 204800, 1185159642⟩ CTN.nil)))) ⟨199730, 204336, 1197675595⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199732, 204800, 1188530452⟩ CTN.nil) ⟨199744, 203392, 1232252630⟩ CTN.nil) ⟨199744, 203968, 1218373997⟩ (CTN.node (CTN.node CTN.nil ⟨199744, 204544, 1204690255⟩ CTN.nil) ⟨199744, 204800, 1198670290⟩ CTN.nil)) ⟨199748, 204800, 1202059367⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199762, 204800, 1213957057⟩ CTN.nil) ⟨199766, 204724, 1219177712⟩ CTN.nil) ⟨199776, 202960, 1271034473⟩ (CTN.node CTN.nil ⟨199776, 203392, 1260256092⟩ CTN.nil))) ⟨199776, 203968, 1246062060⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199776, 204544, 1232067349⟩ CTN.nil) ⟨199796, 203491, 1275422100⟩ CTN.nil) ⟨199796, 203602, 1272639379⟩ (CTN.node CTN.nil ⟨199796, 203634, 1271838563⟩ CTN.nil)) ⟨199796, 204466, 1251236740⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199796, 204722, 1244981794⟩ CTN.nil) ⟨199796, 204800, 1243083765⟩ CTN.nil) ⟨199804, 204800, 1249984866⟩ (CTN.node CTN.nil ⟨199808, 204800, 1253442231⟩ CTN.nil)))))) ⟨199820, 204800, 1263841564⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199824, 203008, 1312721170⟩ CTN.nil) ⟨199824, 204800, 1267317083⟩ CTN.nil) ⟨199830, 204800, 1272538863⟩ (CTN.node (CTN.node CTN.nil ⟨199840, 203072, 1325493777⟩ CTN.nil) ⟨199840, 204800, 1281264491⟩ CTN.nil)) ⟨199856, 204800, 1295284358⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199858, 204800, 1297041931⟩ CTN.nil) ⟨199860, 204800, 1298800635⟩ CTN.nil) ⟨199872, 204800, 1309376586⟩ (CTN.node CTN.nil ⟨199876, 204800, 1312910939⟩ CTN.nil))) ⟨199892, 204466, 1335797449⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199904, 202672, 1394930504⟩ CTN.nil) ⟨199907, 204178, 1356885474⟩ CTN.nil) ⟨199920, 203104, 1397878040⟩ (CTN.node (CTN.node CTN.nil ⟨199920, 204800, 1352086458⟩ CTN.nil) ⟨199924, 204800, 1355674888⟩ CTN.nil)) ⟨199936, 204704, 1369035614⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨199936, 204736, 1368178788⟩ CTN.nil) ⟨199936, 204800, 1366467147⟩ CTN.nil) ⟨199940, 203746, 1398682132⟩ (CTN.node CTN.nil ⟨199952, 204800, 1380919699⟩ CTN.nil)))) ⟨199968, 203584, 1429128134⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨199968, 204160, 1413047240⟩ CTN.nil) ⟨199968, 204736, 1397191952⟩ CTN.nil) ⟨199968, 204800, 1395444015⟩ (CTN.node (CTN.node CTN.nil ⟨199988, 203858, 1440046549⟩ CTN.nil) ⟨199988, 204690, 1416745454⟩ CTN.nil)) ⟨199988, 204800, 1413700169⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200000, 203648, 1457262291⟩ CTN.nil) ⟨200000, 204224, 1440869955⟩ CTN.nil) ⟨200000, 204800, 1424707523⟩ (CTN.node CTN.nil ⟨200004, 204578, 1434603876⟩ CTN.nil))) ⟨200004, 204800, 1428385575⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200016, 204800, 1439446509⟩ CTN.nil) ⟨200020, 203283, 1486762678⟩ CTN.nil) ⟨200032, 203648, 1487486818⟩ (CTN.node (CTN.node CTN.nil ⟨200032, 204224, 1470754495⟩ CTN.nil) ⟨200032, 204800, 1454256844⟩ CTN.nil)) ⟨200048, 202816, 1527551459⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200048, 204800, 1469138422⟩ CTN.nil) ⟨200052, 204800, 1472869936⟩ CTN.nil) ⟨200060, 204800, 1480346296⟩ (CTN.node CTN.nil ⟨200064, 203680, 1517047834⟩ CTN.nil))))) ⟨200064, 204256, 1499985657⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200064, 204744, 1485717584⟩ CTN.nil) ⟨200064, 204800, 1484091138⟩ CTN.nil) ⟨200082, 204800, 1500997843⟩ (CTN.node (CTN.node CTN.nil ⟨200084, 204690, 1506119302⟩ CTN.nil) ⟨200088, 204800, 1506653363⟩ CTN.nil)) ⟨200100, 204800, 1517994294⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200108, 202792, 1586986117⟩ CTN.nil) ⟨200114, 204688, 1534634317⟩ CTN.nil) ⟨200116, 204800, 1533177468⟩ (CTN.node CTN.nil ⟨200128, 204800, 1544611238⟩ CTN.nil))) ⟨200140, 204800, 1556084718⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200160, 204800, 1575295307⟩ CTN.nil) ⟨200176, 204800, 1590742961⟩ CTN.nil) ⟨200180, 204800, 1594615858⟩ (CTN.node (CTN.node CTN.nil ⟨200184, 204800, 1598493144⟩ CTN.nil) ⟨200188, 204800, 1602374819⟩ CTN.nil)) ⟨200192, 204800, 1606260880⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200208, 203392, 1667287204⟩ CTN.nil) ⟨200224, 204800, 1637507063⟩ CTN.nil) ⟨200240, 204800, 1653235100⟩ (CTN.node CTN.nil ⟨200244, 204800, 1657178022⟩ CTN.nil)))) ⟨200256, 204800, 1669032948⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200260, 204800, 1672993305⟩ CTN.nil) ⟨200275, 203954, 1716100512⟩ CTN.nil) ⟨200288, 204800, 1700837617⟩ (CTN.node (CTN.node CTN.nil ⟨200300, 204800, 1712836052⟩ CTN.nil) ⟨200312, 204800, 1724873511⟩ CTN.nil)) ⟨200320, 204544, 1741623214⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200320, 204800, 1732920140⟩ CTN.nil) ⟨200336, 204800, 1749065303⟩ CTN.nil) ⟨200352, 203968, 1794297190⟩ (CTN.node CTN.nil ⟨200352, 204544, 1774145168⟩ CTN.nil))) ⟨200352, 204800, 1765279577⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200370, 204800, 1783603095⟩ CTN.nil) ⟨200372, 204800, 1785644424⟩ CTN.nil) ⟨200376, 204800, 1789730309⟩ (CTN.node CTN.nil ⟨200384, 204800, 1797914978⟩ CTN.nil)) ⟨200386, 204800, 1799963831⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200392, 204800, 1806116834⟩ CTN.nil) ⟨200402, 204800, 1816393302⟩ CTN.nil) ⟨200432, 204800, 1847383399⟩ (CTN.node CTN.nil ⟨200440, 204800, 1855688061⟩ CTN.nil))))))) ⟨200448, 204800, 1864009804⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200494, 204800, 1912190518⟩ CTN.nil) ⟨200496, 204800, 1914298085⟩ CTN.nil) ⟨200512, 204800, 1931196784⟩ (CTN.node (CTN.node CTN.nil ⟨200544, 204800, 1965197336⟩ CTN.nil) ⟨200546, 204800, 1967331347⟩ CTN.nil)) ⟨200556, 204800, 1978017213⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200564, 204800, 1986584866⟩ CTN.nil) ⟨200568, 204800, 1990875007⟩ CTN.nil) ⟨200576, 204800, 1999467908⟩ (CTN.node CTN.nil ⟨200594, 204800, 2018863381⟩ CTN.nil))) ⟨200608, 204800, 2034007473⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200620, 204800, 2047028947⟩ CTN.nil) ⟨200640, 204800, 2068814990⟩ CTN.nil) ⟨200688, 204800, 2121526376⟩ (CTN.node (CTN.node CTN.nil ⟨200692, 204800, 2125945986⟩ CTN.nil) ⟨200704, 204800, 2139229668⟩ CTN.nil)) ⟨200708, 204800, 2143665839⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200712, 204800, 2148106145⟩ CTN.nil) ⟨200752, 204800, 2192736161⟩ CTN.nil) ⟨200756, 204800, 2197221811⟩ (CTN.node CTN.nil ⟨200768, 204800, 2210703411⟩ CTN.nil)))) ⟨200816, 204800, 2264998498⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨200820, 204800, 2269549642⟩ CTN.nil) ⟨200832, 204800, 2283227512⟩ CTN.nil) ⟨200836, 204800, 2287794941⟩ (CTN.node (CTN.node CTN.nil ⟨200844, 204800, 2296941997⟩ CTN.nil) ⟨200876, 204800, 2333692515⟩ CTN.nil)) ⟨200884, 204800, 2342920630⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨200896, 204800, 2356793094⟩ CTN.nil) ⟨200928, 204800, 2393963621⟩ CTN.nil) ⟨200944, 204800, 2412645318⟩ (CTN.node CTN.nil ⟨200964, 204800, 2436087559⟩ CTN.nil))) ⟨201008, 204800, 2488011624⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨201012, 204800, 2492755856⟩ CTN.nil) ⟨201024, 204800, 2507012350⟩ CTN.nil) ⟨201036, 204800, 2521304486⟩ (CTN.node (CTN.node CTN.nil ⟨201072, 204800, 2564394129⟩ CTN.nil) ⟨201088, 204800, 2583647426⟩ CTN.nil)) ⟨201200, 204800, 2720169542⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨201204, 204800, 2725101561⟩ CTN.nil) ⟨201216, 204800, 2739920731⟩ CTN.nil) ⟨201232, 204800, 2759733463⟩ (CTN.node CTN.nil ⟨201280, 204800, 2819539367⟩ CTN.nil))))) ⟨201288, 204800, 2829560435⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨201308, 204800, 2854679603⟩ CTN.nil) ⟨201332, 204800, 2884947646⟩ CTN.nil) ⟨201344, 204800, 2900132663⟩ (CTN.node (CTN.node CTN.nil ⟨201360, 204800, 2920432085⟩ CTN.nil) ⟨201396, 204800, 2966325346⟩ CTN.nil)) ⟨201400, 204800, 2971443304⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨201408, 204800, 2981690414⟩ CTN.nil) ⟨201412, 204800, 2986819561⟩ CTN.nil) ⟨201420, 204800, 2997089025⟩ (CTN.node CTN.nil ⟨201448, 204800, 3033149175⟩ CTN.nil))) ⟨201456, 204800, 3043485426⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨201460, 204800, 3048659097⟩ CTN.nil) ⟨201472, 204800, 3064202262⟩ CTN.nil) ⟨201488, 204800, 3084978072⟩ (CTN.node (CTN.node CTN.nil ⟨201524, 204800, 3131938408⟩ CTN.nil) ⟨201584, 204800, 3210862060⟩ CTN.nil)) ⟨201604, 204800, 3237351010⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨201616, 204800, 3253287592⟩ CTN.nil) ⟨201652, 204800, 3301290973⟩ CTN.nil) ⟨201708, 204800, 3376536470⟩ (CTN.node CTN.nil ⟨201712, 204800, 3381937705⟩ CTN.nil)))) ⟨201728, 204800, 3403577882⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨201788, 204800, 3485228063⟩ CTN.nil) ⟨201808, 204800, 3512618957⟩ CTN.nil) ⟨201836, 204800, 3551111462⟩ (CTN.node (CTN.node CTN.nil ⟨201840, 204800, 3556624176⟩ CTN.nil) ⟨201844, 204800, 3562140328⟩ CTN.nil)) ⟨201864, 204800, 3589772560⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨201964, 204800, 3729209537⟩ CTN.nil) ⟨202028, 204800, 3819550789⟩ CTN.nil) ⟨202036, 204800, 3830903156⟩ (CTN.node CTN.nil ⟨202044, 204800, 3842268715⟩ CTN.nil))) ⟨202048, 204800, 3847956435⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨202092, 204800, 3910737789⟩ CTN.nil) ⟨202100, 204800, 3922195036⟩ CTN.nil) ⟨202128, 204800, 3962397654⟩ (CTN.node CTN.nil ⟨202156, 204800, 4002758560⟩ CTN.nil)) ⟨202172, 204800, 4025892612⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨202224, 204800, 4101430639⟩ CTN.nil) ⟨202252, 204800, 4142326492⟩ CTN.nil) ⟨202268, 204800, 4165764645⟩ (CTN.node CTN.nil ⟨202284, 204800, 4189252805⟩ CTN.nil)))))) ⟨202292, 204800, 4201015576⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨202300, 204800, 4212790777⟩ CTN.nil) ⟨202328, 204800, 4254101506⟩ CTN.nil) ⟨202352, 204800, 4289630850⟩ (CTN.node (CTN.node CTN.nil ⟨202412, 204800, 4378934904⟩ CTN.nil) ⟨202432, 204800, 4408854180⟩ CTN.nil)) ⟨202480, 204800, 4480965631⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨202508, 204800, 4523227946⟩ CTN.nil) ⟨202552, 204800, 4589930760⟩ CTN.nil) ⟨202608, 204800, 4675333033⟩ (CTN.node CTN.nil ⟨202688, 204800, 4798306513⟩ CTN.nil))) ⟨202736, 204800, 4872629004⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨202792, 204800, 4959839855⟩ CTN.nil) ⟨202848, 204800, 5047581965⟩ CTN.nil) ⟨202864, 204800, 5072747449⟩ (CTN.node (CTN.node CTN.nil ⟨202876, 204800, 5091649409⟩ CTN.nil) ⟨202896, 204800, 5123205450⟩ CTN.nil)) ⟨202944, 204800, 5199206823⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨202972, 204800, 5243713164⟩ CTN.nil) ⟨202992, 204800, 5275580288⟩ CTN.nil) ⟨203120, 204800, 5481017517⟩ (CTN.node CTN.nil ⟨203132, 204800, 5500406795⟩ CTN.nil)))) ⟨203260, 204800, 5708564424⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨203296, 204800, 5767540392⟩ CTN.nil) ⟨203456, 204800, 6031855592⟩ CTN.nil) ⟨203712, 204800, 6461782864⟩ (CTN.node (CTN.node CTN.nil ⟨203784, 204800, 6584148680⟩ CTN.nil) ⟨204108, 204800, 7141861699⟩ CTN.nil)) ⟨204160, 204800, 7232362537⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204544, 204800, 7907901185⟩ CTN.nil) ⟨204800, 204848, 8356336171⟩ CTN.nil) ⟨204800, 204850, 8356009412⟩ (CTN.node CTN.nil ⟨204800, 204852, 8355682670⟩ CTN.nil))) ⟨204800, 204854, 8355355943⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 204864, 8353722550⟩ CTN.nil) ⟨204800, 204876, 8351763005⟩ CTN.nil) ⟨204800, 204916, 8345235339⟩ (CTN.node CTN.nil ⟨204800, 204928, 8343278283⟩ CTN.nil)) ⟨204800, 204944, 8340669767⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 204946, 8340343774⟩ CTN.nil) ⟨204800, 204960, 8338062271⟩ CTN.nil) ⟨204800, 204976, 8335455795⟩ (CTN.node CTN.nil ⟨204800, 204980, 8334804335⟩ CTN.nil))))) ⟨204800, 204988, 8333501606⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 204992, 8332850337⟩ CTN.nil) ⟨204800, 205012, 8329594946⟩ CTN.nil) ⟨204800, 205014, 8329269494⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205024, 8327642475⟩ CTN.nil) ⟨204800, 205042, 8324714841⟩ CTN.nil)) ⟨204800, 205044, 8324389628⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205052, 8323088934⟩ CTN.nil) ⟨204800, 205056, 8322438682⟩ CTN.nil) ⟨204800, 205074, 8319513335⟩ (CTN.node CTN.nil ⟨204800, 205104, 8314640613⟩ CTN.nil))) ⟨204800, 205108, 8313991187⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205120, 8312043287⟩ CTN.nil) ⟨204800, 205184, 8301664123⟩ CTN.nil) ⟨204800, 205212, 8297128334⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205228, 8294537846⟩ CTN.nil) ⟨204800, 205232, 8293890382⟩ CTN.nil)) ⟨204800, 205234, 8293566674⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205236, 8293242981⟩ CTN.nil) ⟨204800, 205244, 8291948369⟩ CTN.nil) ⟨204800, 205248, 8291301158⟩ (CTN.node CTN.nil ⟨204800, 205266, 8288389489⟩ CTN.nil)))) ⟨204800, 205268, 8288066049⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205280, 8286125741⟩ CTN.nil) ⟨204800, 205312, 8280954363⟩ CTN.nil) ⟨204800, 205344, 8275787019⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205352, 8274495813⟩ CTN.nil) ⟨204800, 205364, 8272559476⟩ CTN.nil)) ⟨204800, 205376, 8270623706⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205410, 8265142098⟩ CTN.nil) ⟨204800, 205422, 8263208498⟩ CTN.nil) ⟨204800, 205440, 8260309158⟩ (CTN.node CTN.nil ⟨204800, 205458, 8257411090⟩ CTN.nil))) ⟨204800, 205484, 8253227235⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205488, 8252583800⟩ CTN.nil) ⟨204800, 205494, 8251618766⟩ CTN.nil) ⟨204800, 205504, 8250010689⟩ (CTN.node CTN.nil ⟨204800, 205548, 8242939802⟩ CTN.nil)) ⟨204800, 205554, 8241976178⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205556, 8241655001⟩ CTN.nil) ⟨204800, 205568, 8239728268⟩ CTN.nil) ⟨204800, 205580, 8237802098⟩ (CTN.node CTN.nil ⟨204800, 205584, 8237160167⟩ CTN.nil))))))))

noncomputable def tab16 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205600, 8234593066⟩ CTN.nil) ⟨204800, 205616, 8232026966⟩ CTN.nil) ⟨204800, 205628, 8230103047⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205632, 8229461866⟩ CTN.nil) ⟨204800, 205654, 8225936484⟩ CTN.nil)) ⟨204800, 205656, 8225616088⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205664, 8224334662⟩ CTN.nil) ⟨204800, 205684, 8221132188⟩ CTN.nil) ⟨204800, 205696, 8219211452⟩ (CTN.node CTN.nil ⟨204800, 205700, 8218571331⟩ CTN.nil))) ⟨204800, 205704, 8217931273⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205744, 8211534116⟩ CTN.nil) ⟨204800, 205760, 8208976997⟩ CTN.nil) ⟨204800, 205772, 8207059811⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205778, 8206101428⟩ CTN.nil) ⟨204800, 205808, 8201311611⟩ CTN.nil)) ⟨204800, 205856, 8193655172⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205872, 8191105012⟩ CTN.nil) ⟨204800, 205874, 8190786311⟩ CTN.nil) ⟨204800, 205876, 8190467627⟩ (CTN.node CTN.nil ⟨204800, 205888, 8188555844⟩ CTN.nil)))) ⟨204800, 205904, 8186007668⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 205936, 8180914290⟩ CTN.nil) ⟨204800, 205952, 8178369086⟩ CTN.nil) ⟨204800, 205968, 8175824873⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 205992, 8172010409⟩ CTN.nil) ⟨204800, 206000, 8170739415⟩ CTN.nil)) ⟨204800, 206002, 8170421705⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206016, 8168198169⟩ CTN.nil) ⟨204800, 206032, 8165657911⟩ CTN.nil) ⟨204800, 206064, 8160580358⟩ (CTN.node CTN.nil ⟨204800, 206068, 8159945941⟩ CTN.nil))) ⟨204800, 206098, 8155189782⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206144, 8147903735⟩ CTN.nil) ⟨204800, 206148, 8147270550⟩ CTN.nil) ⟨204800, 206176, 8142839980⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 206192, 8140309578⟩ CTN.nil) ⟨204800, 206196, 8139677132⟩ CTN.nil)) ⟨204800, 206208, 8137780160⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206224, 8135251724⟩ CTN.nil) ⟨204800, 206226, 8134935738⟩ CTN.nil) ⟨204800, 206256, 8130197797⟩ (CTN.node CTN.nil ⟨204800, 206260, 8129566333⟩ CTN.nil))))) ⟨204800, 206272, 8127672307⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206300, 8123255057⟩ CTN.nil) ⟨204800, 206320, 8120101717⟩ CTN.nil) ⟨204800, 206336, 8117580146⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 206386, 8109706546⟩ CTN.nil) ⟨204800, 206388, 8109391800⟩ CTN.nil)) ⟨204800, 206400, 8107503649⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206404, 8106874387⟩ CTN.nil) ⟨204800, 206416, 8104986969⟩ CTN.nil) ⟨204800, 206432, 8102471265⟩ (CTN.node CTN.nil ⟨204800, 206436, 8101842492⟩ CTN.nil))) ⟨204800, 206448, 8099956538⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206452, 8099328009⟩ CTN.nil) ⟨204800, 206464, 8097442786⟩ CTN.nil) ⟨204800, 206528, 8087397529⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 206544, 8084888649⟩ CTN.nil) ⟨204800, 206560, 8082380743⟩ CTN.nil)) ⟨204800, 206576, 8079873809⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206592, 8077367847⟩ CTN.nil) ⟨204800, 206600, 8076115231⟩ CTN.nil) ⟨204800, 206610, 8074549802⟩ (CTN.node CTN.nil ⟨204800, 206624, 8072358839⟩ CTN.nil)))) ⟨204800, 206640, 8069855791⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206644, 8069230181⟩ CTN.nil) ⟨204800, 206656, 8067353713⟩ CTN.nil) ⟨204800, 206672, 8064852606⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 206704, 8059853298⟩ CTN.nil) ⟨204800, 206706, 8059540970⟩ CTN.nil)) ⟨204800, 206716, 8057979557⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206720, 8057355097⟩ CTN.nil) ⟨204800, 206764, 8050490036⟩ CTN.nil) ⟨204800, 206780, 8047995463⟩ (CTN.node CTN.nil ⟨204800, 206784, 8047371971⟩ CTN.nil))) ⟨204800, 206804, 8044255416⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206828, 8040517541⟩ CTN.nil) ⟨204800, 206832, 8039894774⟩ CTN.nil) ⟨204800, 206836, 8039272066⟩ (CTN.node CTN.nil ⟨204800, 206848, 8037404305⟩ CTN.nil)) ⟨204800, 206908, 8028073634⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206912, 8027452071⟩ CTN.nil) ⟨204800, 206960, 8019998005⟩ CTN.nil) ⟨204800, 206964, 8019377224⟩ (CTN.node CTN.nil ⟨204800, 206972, 8018135841⟩ CTN.nil)))))) ⟨204800, 206976, 8017515240⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 206988, 8015653797⟩ CTN.nil) ⟨204800, 206996, 8014413135⟩ CTN.nil) ⟨204800, 207016, 8011312530⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 207028, 8009452887⟩ CTN.nil) ⟨204800, 207040, 8007593784⟩ CTN.nil)) ⟨204800, 207084, 8000781686⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207104, 7997687674⟩ CTN.nil) ⟨204800, 207108, 7997069051⟩ CTN.nil) ⟨204800, 207148, 7990886110⟩ (CTN.node CTN.nil ⟨204800, 207152, 7990268145⟩ CTN.nil))) ⟨204800, 207156, 7989650239⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207168, 7987796881⟩ CTN.nil) ⟨204800, 207216, 7980388822⟩ CTN.nil) ⟨204800, 207232, 7977921378⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 207244, 7976071420⟩ CTN.nil) ⟨204800, 207248, 7975454887⟩ CTN.nil)) ⟨204800, 207292, 7968676953⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207296, 7968061135⟩ CTN.nil) ⟨204800, 207312, 7965598455⟩ CTN.nil) ⟨204800, 207344, 7960675951⟩ (CTN.node CTN.nil ⟨204800, 207360, 7958216125⟩ CTN.nil)))) ⟨204800, 207364, 7957601317⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207408, 7950842346⟩ CTN.nil) ⟨204800, 207424, 7948386319⟩ CTN.nil) ⟨204800, 207436, 7946544921⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 207472, 7941023925⟩ CTN.nil) ⟨204800, 207488, 7938571689⟩ CTN.nil)) ⟨204800, 207528, 7932445239⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207532, 7931832920⟩ CTN.nil) ⟨204800, 207536, 7931220659⟩ CTN.nil) ⟨204800, 207538, 7930914551⟩ (CTN.node CTN.nil ⟨204800, 207552, 7928772207⟩ CTN.nil))) ⟨204800, 207568, 7926324700⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207600, 7921432520⟩ CTN.nil) ⟨204800, 207604, 7920821263⟩ CTN.nil) ⟨204800, 207624, 7917765862⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 207656, 7912880285⟩ CTN.nil) ⟨204800, 207664, 7911659479⟩ CTN.nil)) ⟨204800, 207680, 7909218575⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207728, 7901901510⟩ CTN.nil) ⟨204800, 207744, 7899464369⟩ CTN.nil) ⟨204800, 207760, 7897028168⟩ (CTN.node CTN.nil ⟨204800, 207762, 7896723709⟩ CTN.nil))))) ⟨204800, 207792, 7892158584⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207796, 7891550149⟩ CTN.nil) ⟨204800, 207808, 7889725199⟩ CTN.nil) ⟨204800, 207852, 7883038228⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 207860, 7881823176⟩ CTN.nil) ⟨204800, 207868, 7880608358⟩ CTN.nil)) ⟨204800, 207872, 7880001038⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 207936, 7870291856⟩ CTN.nil) ⟨204800, 207984, 7863019785⟩ CTN.nil) ⟨204800, 208000, 7860597628⟩ (CTN.node CTN.nil ⟨204800, 208016, 7858176404⟩ CTN.nil))) ⟨204800, 208052, 7852732059⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208064, 7850918325⟩ CTN.nil) ⟨204800, 208128, 7841253920⟩ CTN.nil) ⟨204800, 208160, 7836427295⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 208172, 7834618269⟩ CTN.nil) ⟨204800, 208192, 7831604385⟩ CTN.nil)) ⟨204800, 208208, 7829194321⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208224, 7826785185⟩ CTN.nil) ⟨204800, 208240, 7824376975⟩ CTN.nil) ⟨204800, 208256, 7821969692⟩ (CTN.node CTN.nil ⟨204800, 208264, 7820766398⟩ CTN.nil)))) ⟨204800, 208312, 7813551490⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208344, 7808746175⟩ CTN.nil) ⟨204800, 208360, 7806344903⟩ CTN.nil) ⟨204800, 208364, 7805744729⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 208444, 7793753361⟩ CTN.nil) ⟨204800, 208448, 7793154397⟩ CTN.nil)) ⟨204800, 208480, 7788364760⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208492, 7786569595⟩ CTN.nil) ⟨204800, 208496, 7785971321⟩ CTN.nil) ⟨204800, 208500, 7785373105⟩ (CTN.node CTN.nil ⟨204800, 208512, 7783578802⟩ CTN.nil))) ⟨204800, 208556, 7777004113⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208576, 7774017913⟩ CTN.nil) ⟨204800, 208624, 7766856881⟩ CTN.nil) ⟨204800, 208640, 7764471704⟩ (CTN.node CTN.nil ⟨204800, 208652, 7762683421⟩ CTN.nil)) ⟨204800, 208680, 7758512765⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208692, 7756726198⟩ CTN.nil) ⟨204800, 208700, 7755535440⟩ CTN.nil) ⟨204800, 208704, 7754940146⟩ (CTN.node CTN.nil ⟨204800, 208812, 7738888793⟩ CTN.nil))))))) ⟨204800, 208832, 7735920880⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208880, 7728803693⟩ CTN.nil) ⟨204800, 208896, 7726433117⟩ CTN.nil) ⟨204800, 208908, 7724655782⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 208928, 7721694692⟩ CTN.nil) ⟨204800, 208944, 7719326842⟩ CTN.nil)) ⟨204800, 208956, 7717551550⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 208960, 7716959899⟩ CTN.nil) ⟨204800, 208976, 7714593864⟩ CTN.nil) ⟨204800, 208984, 7713411187⟩ (CTN.node CTN.nil ⟨204800, 209008, 7709864514⟩ CTN.nil))) ⟨204800, 209024, 7707501199⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209040, 7705138789⟩ CTN.nil) ⟨204800, 209088, 7698056990⟩ CTN.nil) ⟨204800, 209136, 7690983326⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 209152, 7688627245⟩ CTN.nil) ⟨204800, 209184, 7683917788⟩ CTN.nil)) ⟨204800, 209200, 7681564413⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209216, 7679211938⟩ CTN.nil) ⟨204800, 209232, 7676860364⟩ CTN.nil) ⟨204800, 209264, 7672159917⟩ (CTN.node CTN.nil ⟨204800, 209268, 7671572614⟩ CTN.nil)))) ⟨204800, 209280, 7669811042⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209296, 7667463067⟩ CTN.nil) ⟨204800, 209392, 7653394073⟩ CTN.nil) ⟨204800, 209408, 7651052380⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 209460, 7643448061⟩ CTN.nil) ⟨204800, 209464, 7642863504⟩ CTN.nil)) ⟨204800, 209472, 7641694560⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209488, 7639357341⟩ CTN.nil) ⟨204800, 209520, 7634685584⟩ CTN.nil) ⟨204800, 209524, 7634101866⟩ (CTN.node CTN.nil ⟨204800, 209532, 7632934597⟩ CTN.nil))) ⟨204800, 209536, 7632351046⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209580, 7625935664⟩ CTN.nil) ⟨204800, 209600, 7623021811⟩ CTN.nil) ⟨204800, 209648, 7616034240⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 209652, 7615452304⟩ CTN.nil) ⟨204800, 209712, 7606729932⟩ CTN.nil)) ⟨204800, 209716, 7606148885⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209732, 7603825251⟩ CTN.nil) ⟨204800, 209744, 7602083107⟩ CTN.nil) ⟨204800, 209776, 7597439831⟩ (CTN.node CTN.nil ⟨204800, 209780, 7596859671⟩ CTN.nil))))) ⟨204800, 209788, 7595699517⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209792, 7595119523⟩ CTN.nil) ⟨204800, 209836, 7588743242⟩ CTN.nil) ⟨204800, 209844, 7587584638⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 209852, 7586426254⟩ CTN.nil) ⟨204800, 209856, 7585847146⟩ CTN.nil)) ⟨204800, 209900, 7579480595⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 209904, 7578902149⟩ CTN.nil) ⟨204800, 209908, 7578323758⟩ CTN.nil) ⟨204800, 209972, 7569077007⟩ (CTN.node CTN.nil ⟨204800, 210048, 7558114805⟩ CTN.nil))) ⟨204800, 210092, 7551777339⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210100, 7550625786⟩ CTN.nil) ⟨204800, 210108, 7549474453⟩ CTN.nil) ⟨204800, 210112, 7548898869⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 210156, 7542571062⟩ CTN.nil) ⟨204800, 210160, 7541996136⟩ CTN.nil)) ⟨204800, 210164, 7541421264⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210176, 7539696979⟩ CTN.nil) ⟨204800, 210184, 7538547729⟩ CTN.nil) ⟨204800, 210216, 7533952919⟩ (CTN.node CTN.nil ⟨204800, 210220, 7533378814⟩ CTN.nil)))) ⟨204800, 210240, 7530509109⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210288, 7523627392⟩ CTN.nil) ⟨204800, 210356, 7513891747⟩ CTN.nil) ⟨204800, 210432, 7503029365⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 210496, 7493897320⟩ CTN.nil) ⟨204800, 210508, 7492186609⟩ CTN.nil)) ⟨204800, 210512, 7491616480⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210528, 7489336509⟩ CTN.nil) ⟨204800, 210544, 7487057405⟩ CTN.nil) ⟨204800, 210560, 7484779168⟩ (CTN.node CTN.nil ⟨204800, 210600, 7479087366⟩ CTN.nil))) ⟨204800, 210624, 7475674883⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210692, 7466016746⟩ CTN.nil) ⟨204800, 210736, 7459775676⟩ CTN.nil) ⟨204800, 210752, 7457507814⟩ (CTN.node CTN.nil ⟨204800, 210800, 7450709396⟩ CTN.nil)) ⟨204800, 210816, 7448444979⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 210944, 7430360584⟩ CTN.nil) ⟨204800, 211072, 7412331053⟩ CTN.nil) ⟨204800, 211088, 7410081209⟩ (CTN.node CTN.nil ⟨204800, 211128, 7404460335⟩ CTN.nil)))))) ⟨204800, 211176, 7397722320⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211184, 7396600063⟩ CTN.nil) ⟨204800, 211196, 7394917077⟩ CTN.nil) ⟨204800, 211200, 7394356188⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 211232, 7389870989⟩ CTN.nil) ⟨204800, 211264, 7385389192⟩ CTN.nil)) ⟨204800, 211296, 7380910793⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211328, 7376435789⟩ CTN.nil) ⟨204800, 211336, 7375317568⟩ CTN.nil) ⟨204800, 211384, 7368612691⟩ (CTN.node CTN.nil ⟨204800, 211440, 7360799963⟩ CTN.nil))) ⟨204800, 211456, 7358569658⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211516, 7350213535⟩ CTN.nil) ⟨204800, 211520, 7349656882⟩ CTN.nil) ⟨204800, 211552, 7345205555⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 211560, 7344093250⟩ CTN.nil) ⟨204800, 211564, 7343537177⟩ CTN.nil)) ⟨204800, 211572, 7342425188⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211584, 7340757599⟩ CTN.nil) ⟨204800, 211592, 7339646136⟩ CTN.nil) ⟨204800, 211640, 7332981776⟩ (CTN.node CTN.nil ⟨204800, 211672, 7328543072⟩ CTN.nil)))) ⟨204800, 211712, 7322999415⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211744, 7318568264⟩ CTN.nil) ⟨204800, 211764, 7315800497⟩ CTN.nil) ⟨204800, 211772, 7314693756⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 211776, 7314140465⟩ CTN.nil) ⟨204800, 211820, 7308057708⟩ CTN.nil)) ⟨204800, 211828, 7306952432⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 211840, 7305294910⟩ CTN.nil) ⟨204800, 211884, 7299221349⟩ CTN.nil) ⟨204800, 211904, 7296462727⟩ (CTN.node CTN.nil ⟨204800, 211948, 7290398344⟩ CTN.nil))) ⟨204800, 211952, 7289847349⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212016, 7281038507⟩ CTN.nil) ⟨204800, 212020, 7280488397⟩ CTN.nil) ⟨204800, 212096, 7270046162⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 212140, 7264009215⟩ CTN.nil) ⟨204800, 212160, 7261267221⟩ CTN.nil)) ⟨204800, 212204, 7255239387⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212208, 7254691713⟩ CTN.nil) ⟨204800, 212224, 7252501531⟩ CTN.nil) ⟨204800, 212268, 7246482793⟩ (CTN.node CTN.nil ⟨204800, 212280, 7244842403⟩ CTN.nil))))) ⟨204800, 212332, 7237739408⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212336, 7237193385⟩ CTN.nil) ⟨204800, 212352, 7235009806⟩ CTN.nil) ⟨204800, 212416, 7226283724⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 212464, 7219747796⟩ CTN.nil) ⟨204800, 212480, 7217570796⟩ CTN.nil)) ⟨204800, 212524, 7211588276⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212536, 7209957756⟩ CTN.nil) ⟨204800, 212588, 7202897493⟩ CTN.nil) ⟨204800, 212592, 7202354754⟩ (CTN.node CTN.nil ⟨204800, 212604, 7200726844⟩ CTN.nil))) ⟨204800, 212652, 7194219801⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212720, 7185014071⟩ CTN.nil) ⟨204800, 212736, 7182850157⟩ CTN.nil) ⟨204800, 212792, 7175282874⟩ (CTN.node (CTN.node CTN.nil ⟨204800, 212832, 7169883774⟩ CTN.nil) ⟨204800, 212848, 7167725556⟩ CTN.nil)) ⟨204800, 212852, 7167186128⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212860, 7166107426⟩ CTN.nil) ⟨204800, 212864, 7165568150⟩ CTN.nil) ⟨204800, 212908, 7159639470⟩ (CTN.node CTN.nil ⟨204800, 212928, 7156946642⟩ CTN.nil)))) ⟨204800, 212972, 7151026878⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨204800, 212992, 7148338100⟩ CTN.nil) ⟨204984, 212992, 7430534959⟩ CTN.nil) ⟨205016, 212992, 7479747351⟩ (CTN.node (CTN.node CTN.nil ⟨207696, 212992, 11551972317⟩ CTN.nil) ⟨208160, 212992, 12205051124⟩ CTN.nil)) ⟨209280, 212992, 13651975337⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨210512, 212992, 14968078744⟩ CTN.nil) ⟨210944, 212992, 15347203445⟩ CTN.nil) ⟨212992, 213044, 16444306165⟩ (CTN.node CTN.nil ⟨212992, 213104, 16424286405⟩ CTN.nil))) ⟨212992, 213120, 16418769270⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 213184, 16395951169⟩ CTN.nil) ⟨212992, 213228, 16379569867⟩ CTN.nil) ⟨212992, 213248, 16371937440⟩ (CTN.node CTN.nil ⟨212992, 213256, 16368851904⟩ CTN.nil)) ⟨212992, 213292, 16354737045⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 213296, 16353145525⟩ CTN.nil) ⟨212992, 213312, 16346733102⟩ CTN.nil) ⟨212992, 213440, 16292773527⟩ (CTN.node CTN.nil ⟨212992, 213488, 16271325063⟩ CTN.nil))))))))

noncomputable def tab17 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 213632, 16203039755⟩ CTN.nil) ⟨212992, 213744, 16145876113⟩ CTN.nil) ⟨212992, 213868, 16078495271⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 213876, 16074001499⟩ CTN.nil) ⟨212992, 213952, 16030429901⟩ CTN.nil)) ⟨212992, 214064, 15963332136⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214068, 15960872564⟩ CTN.nil) ⟨212992, 214128, 15923458807⟩ CTN.nil) ⟨212992, 214132, 15920929959⟩ (CTN.node CTN.nil ⟨212992, 214188, 15885073860⟩ CTN.nil))) ⟨212992, 214200, 15877280860⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214248, 15845723799⟩ CTN.nil) ⟨212992, 214256, 15840404536⟩ CTN.nil) ⟨212992, 214272, 15829714926⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 214324, 15794504608⟩ CTN.nil) ⟨212992, 214352, 15775249101⟩ CTN.nil)) ⟨212992, 214384, 15752990065⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214400, 15741759742⟩ CTN.nil) ⟨212992, 214456, 15701926500⟩ CTN.nil) ⟨212992, 214504, 15667134158⟩ (CTN.node CTN.nil ⟨212992, 214512, 15661277398⟩ CTN.nil)))) ⟨212992, 214528, 15649514276⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214560, 15625790073⟩ CTN.nil) ⟨212992, 214592, 15601802787⟩ CTN.nil) ⟨212992, 214624, 15577553457⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 214632, 15571450303⟩ CTN.nil) ⟨212992, 214636, 15568392614⟩ CTN.nil)) ⟨212992, 214656, 15553043132⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214664, 15546874894⟩ CTN.nil) ⟨212992, 214768, 15465217013⟩ CTN.nil) ⟨212992, 214784, 15452413173⟩ (CTN.node CTN.nil ⟨212992, 214888, 15367636688⟩ CTN.nil))) ⟨212992, 214892, 15364322650⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 214912, 15347693469⟩ CTN.nil) ⟨212992, 214956, 15310764305⟩ CTN.nil) ⟨212992, 214968, 15300610688⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 215016, 15259646416⟩ CTN.nil) ⟨212992, 215212, 15086639292⟩ CTN.nil)) ⟨212992, 215344, 14965029214⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 215352, 14957529418⟩ CTN.nil) ⟨212992, 215488, 14827802700⟩ CTN.nil) ⟨212992, 215536, 14781021856⟩ (CTN.node CTN.nil ⟨212992, 215552, 14765314206⟩ CTN.nil))))) ⟨212992, 215608, 14709891570⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 215664, 14653780647⟩ CTN.nil) ⟨212992, 215792, 14522980056⟩ CTN.nil) ⟨212992, 215808, 14506383906⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 215904, 14405676172⟩ CTN.nil) ⟨212992, 215920, 14388704650⟩ CTN.nil)) ⟨212992, 215936, 14371680180⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 216048, 14251040712⟩ CTN.nil) ⟨212992, 216064, 14233598825⟩ CTN.nil) ⟨212992, 216172, 14114530394⟩ (CTN.node CTN.nil ⟨212992, 216192, 14092227980⟩ CTN.nil))) ⟨212992, 216492, 13748512307⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 216512, 13725001916⟩ CTN.nil) ⟨212992, 216560, 13668281922⟩ CTN.nil) ⟨212992, 216584, 13639766909⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 216704, 13495666739⟩ CTN.nil) ⟨212992, 216752, 13437326711⟩ CTN.nil)) ⟨212992, 216816, 13358930536⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 217008, 13119678245⟩ CTN.nil) ⟨212992, 217072, 13038613763⟩ CTN.nil) ⟨212992, 217088, 13018247744⟩ (CTN.node CTN.nil ⟨212992, 217168, 12915827976⟩ CTN.nil)))) ⟨212992, 217320, 12718592543⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 217528, 12443354988⟩ CTN.nil) ⟨212992, 217576, 12379003573⟩ CTN.nil) ⟨212992, 217704, 12205939677⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 217728, 12173259767⟩ CTN.nil) ⟨212992, 217832, 12030834160⟩ CTN.nil)) ⟨212992, 217856, 11997783053⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 217960, 11853791487⟩ CTN.nil) ⟨212992, 217984, 11820388852⟩ CTN.nil) ⟨212992, 218032, 11753393144⟩ (CTN.node CTN.nil ⟨212992, 218088, 11674916825⟩ CTN.nil))) ⟨212992, 218216, 11494315974⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 218240, 11460269768⟩ CTN.nil) ⟨212992, 218288, 11392009324⟩ CTN.nil) ⟨212992, 218296, 11380611106⟩ (CTN.node CTN.nil ⟨212992, 218608, 10931607019⟩ CTN.nil)) ⟨212992, 218672, 10838504302⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 218680, 10826844437⟩ CTN.nil) ⟨212992, 218856, 10569158034⟩ CTN.nil) ⟨212992, 218864, 10557394293⟩ (CTN.node CTN.nil ⟨212992, 218880, 10533854239⟩ CTN.nil)))))) ⟨212992, 219008, 10344954523⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 219120, 10178881781⟩ CTN.nil) ⟨212992, 219136, 10155101777⟩ CTN.nil) ⟨212992, 219232, 10012152067⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 219240, 10000219583⟩ CTN.nil) ⟨212992, 219376, 9796936964⟩ CTN.nil)) ⟨212992, 219392, 9772971268⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 219648, 9388330754⟩ CTN.nil) ⟨212992, 219776, 9195340124⟩ CTN.nil) ⟨212992, 219888, 9026221224⟩ (CTN.node CTN.nil ⟨212992, 220032, 8808558093⟩ CTN.nil))) ⟨212992, 220144, 8639179947⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 220160, 8614981766⟩ CTN.nil) ⟨212992, 220384, 8276333427⟩ CTN.nil) ⟨212992, 220416, 8227993137⟩ (CTN.node (CTN.node CTN.nil ⟨212992, 220648, 7878061509⟩ CTN.nil) ⟨212992, 220856, 7565489698⟩ CTN.nil)) ⟨212992, 221032, 7302206258⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨212992, 221056, 7266405248⟩ CTN.nil) ⟨212992, 221160, 7111581235⟩ CTN.nil) ⟨212992, 221184, 7075928778⟩ (CTN.node CTN.nil ⟨213692, 221184, 7162415271⟩ CTN.nil)))) ⟨214432, 221184, 7254214482⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨217200, 221184, 7597272638⟩ CTN.nil) ⟨217888, 221184, 7681547271⟩ CTN.nil) ⟨217968, 221184, 7691300998⟩ (CTN.node (CTN.node CTN.nil ⟨218432, 221184, 7747656776⟩ CTN.nil) ⟨219296, 221184, 7851468519⟩ CTN.nil)) ⟨219424, 221184, 7866706880⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨220108, 221184, 7947437827⟩ CTN.nil) ⟨220272, 221184, 7966607637⟩ CTN.nil) ⟨220652, 221184, 8010726372⟩ (CTN.node CTN.nil ⟨221184, 221416, 7690272903⟩ CTN.nil))) ⟨221184, 221544, 7481280369⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 221696, 7234651425⟩ CTN.nil) ⟨221184, 221928, 6861845531⟩ CTN.nil) ⟨221184, 222008, 6734404292⟩ (CTN.node (CTN.node CTN.nil ⟨221184, 222080, 6620229385⟩ CTN.nil) ⟨221184, 222312, 6255915968⟩ CTN.nil)) ⟨221184, 222336, 6218556595⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 222464, 6020404688⟩ CTN.nil) ⟨221184, 222592, 5824173145⟩ CTN.nil) ⟨221184, 222784, 5533636203⟩ (CTN.node CTN.nil ⟨221184, 222944, 5295216672⟩ CTN.nil))))) ⟨221184, 223200, 4921202122⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 223216, 4898144275⟩ CTN.nil) ⟨221184, 223456, 4556984120⟩ CTN.nil) ⟨221184, 223472, 4534561469⟩ (CTN.node (CTN.node CTN.nil ⟨221184, 223488, 4512179917⟩ CTN.nil) ⟨221184, 223664, 4268741260⟩ CTN.nil)) ⟨221184, 223712, 4203243235⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 223744, 4159794995⟩ CTN.nil) ⟨221184, 223776, 4116521886⟩ CTN.nil) ⟨221184, 223872, 3987765561⟩ (CTN.node CTN.nil ⟨221184, 223976, 3850108483⟩ CTN.nil))) ⟨221184, 224360, 3358962831⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 224488, 3201467306⟩ CTN.nil) ⟨221184, 224864, 2757711661⟩ CTN.nil) ⟨221184, 224872, 2748584181⟩ (CTN.node (CTN.node CTN.nil ⟨221184, 224944, 2667038594⟩ CTN.nil) ⟨221184, 225088, 2507229055⟩ CTN.nil)) ⟨221184, 225256, 2326405216⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 225376, 2201015601⟩ CTN.nil) ⟨221184, 225640, 1936444831⟩ CTN.nil) ⟨221184, 225792, 1791284529⟩ (CTN.node CTN.nil ⟨221184, 226224, 1408058229⟩ CTN.nil)))) ⟨221184, 226304, 1341936689⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 226456, 1220542878⟩ CTN.nil) ⟨221184, 227052, 798958492⟩ CTN.nil) ⟨221184, 227072, 786333379⟩ (CTN.node (CTN.node CTN.nil ⟨221184, 227100, 768825680⟩ CTN.nil) ⟨221184, 227128, 751513515⟩ CTN.nil)) ⟨221184, 227504, 538057829⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 227576, 501238058⟩ CTN.nil) ⟨221184, 227756, 414912132⟩ CTN.nil) ⟨221184, 228072, 283173964⟩ (CTN.node CTN.nil ⟨221184, 228160, 250984162⟩ CTN.nil))) ⟨221184, 228584, 123302443⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 228700, 96257478⟩ CTN.nil) ⟨221184, 228720, 91935740⟩ CTN.nil) ⟨221184, 228788, 77991129⟩ (CTN.node CTN.nil ⟨221184, 228852, 65923119⟩ CTN.nil)) ⟨221184, 228968, 46654088⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨221184, 229256, 13245868⟩ CTN.nil) ⟨221184, 229376, 5355706⟩ CTN.nil) ⟨221504, 227580, 503706529⟩ (CTN.node CTN.nil ⟨221772, 229376, 5958270⟩ CTN.nil))))))) ⟨221936, 227884, 366855452⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨222316, 228200, 246525385⟩ CTN.nil) ⟨223256, 229204, 21568241⟩ CTN.nil) ⟨223308, 229376, 7477133⟩ (CTN.node (CTN.node CTN.nil ⟨223472, 229376, 7630701⟩ CTN.nil) ⟨223800, 228148, 277071942⟩ CTN.nil)) ⟨224252, 228664, 118737632⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229376, 229384, 10120304⟩ CTN.nil) ⟨229376, 229400, 8988499⟩ CTN.nil) ⟨229376, 229420, 7668239⟩ (CTN.node CTN.nil ⟨229376, 229578, 925015⟩ CTN.nil))) ⟨229376, 229608, 382972⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229376, 229632, 118725⟩ CTN.nil) ⟨229664, 233888, 412⟩ CTN.nil) ⟨229664, 234464, 408⟩ (CTN.node (CTN.node CTN.nil ⟨229664, 234496, 407⟩ CTN.nil) ⟨229664, 235328, 402⟩ CTN.nil)) ⟨229664, 237568, 387⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229668, 234570, 4094⟩ CTN.nil) ⟨229669, 232836, 5785⟩ CTN.nil) ⟨229670, 235396, 7274⟩ (CTN.node CTN.nil ⟨229676, 237568, 21843⟩ CTN.nil)))) ⟨229678, 235594, 29584⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229684, 233411, 58373⟩ CTN.nil) ⟨229684, 233443, 58341⟩ CTN.nil) ⟨229684, 237568, 54390⟩ (CTN.node (CTN.node CTN.nil ⟨229685, 232964, 64333⟩ CTN.nil) ⟨229686, 235412, 67216⟩ CTN.nil)) ⟨229686, 236244, 66273⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229687, 232550, 76636⟩ CTN.nil) ⟨229687, 232982, 76069⟩ CTN.nil) ⟨229687, 233398, 75528⟩ (CTN.node CTN.nil ⟨229688, 233975, 80927⟩ CTN.nil))) ⟨229688, 234646, 80004⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229688, 234678, 79961⟩ CTN.nil) ⟨229696, 237568, 130579⟩ CTN.nil) ⟨229700, 237568, 163276⟩ (CTN.node (CTN.node CTN.nil ⟨229703, 233046, 205407⟩ CTN.nil) ⟨229704, 234630, 209822⟩ CTN.nil)) ⟨229704, 237568, 199623⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229710, 235626, 269710⟩ CTN.nil) ⟨229716, 233586, 353721⟩ CTN.nil) ⟨229716, 234354, 349103⟩ (CTN.node CTN.nil ⟨229716, 235218, 343997⟩ CTN.nil))))) ⟨229718, 233013, 384254⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229718, 233061, 383937⟩ CTN.nil) ⟨229718, 233477, 381205⟩ CTN.nil) ⟨229718, 235476, 368412⟩ (CTN.node (CTN.node CTN.nil ⟨229719, 232630, 400773⟩ CTN.nil) ⟨229719, 233046, 397917⟩ CTN.nil)) ⟨229719, 233462, 395085⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229720, 234023, 405199⟩ CTN.nil) ⟨229720, 234710, 400471⟩ CTN.nil) ⟨229720, 237268, 383462⟩ (CTN.node CTN.nil ⟨229720, 237568, 381527⟩ CTN.nil))) ⟨229733, 232868, 620027⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229734, 232597, 640640⟩ CTN.nil) ⟨229734, 232613, 640464⟩ CTN.nil) ⟨229736, 237568, 621870⟩ (CTN.node (CTN.node CTN.nil ⟨229744, 237568, 763963⟩ CTN.nil) ⟨229748, 234160, 890551⟩ CTN.nil)) ⟨229748, 235824, 865656⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229748, 237202, 845696⟩ CTN.nil) ⟨229748, 237568, 840491⟩ CTN.nil) ⟨229750, 232629, 957364⟩ (CTN.node CTN.nil ⟨229750, 234037, 934510⟩ CTN.nil)))) ⟨229750, 234708, 923859⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229750, 236340, 898579⟩ CTN.nil) ⟨229751, 233030, 972563⟩ CTN.nil) ⟨229752, 234087, 976728⟩ (CTN.node (CTN.node CTN.nil ⟨229752, 234774, 965335⟩ CTN.nil) ⟨229752, 236342, 939946⟩ CTN.nil)) ⟨229752, 236438, 938419⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229752, 237270, 925313⟩ CTN.nil) ⟨229752, 237568, 920674⟩ CTN.nil) ⟨229760, 235328, 1134223⟩ (CTN.node CTN.nil ⟨229760, 237568, 1092006⟩ CTN.nil))) ⟨229764, 237440, 1185712⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229764, 237568, 1183156⟩ CTN.nil) ⟨229765, 233492, 1293081⟩ CTN.nil) ⟨229767, 232630, 1363936⟩ (CTN.node CTN.nil ⟨229768, 236326, 1305066⟩ CTN.nil)) ⟨229772, 237568, 1376424⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229780, 236338, 1617592⟩ CTN.nil) ⟨229781, 232964, 1742673⟩ CTN.nil) ⟨229782, 233061, 1769186⟩ (CTN.node CTN.nil ⟨229782, 234684, 1720703⟩ CTN.nil)))))) ⟨229782, 235516, 1696493⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229783, 232646, 1811731⟩ CTN.nil) ⟨229783, 233494, 1785529⟩ CTN.nil) ⟨229784, 234087, 1796875⟩ (CTN.node (CTN.node CTN.nil ⟨229784, 235542, 1752843⟩ CTN.nil) ⟨229784, 235612, 1750758⟩ CTN.nil)) ⟨229784, 237568, 1693753⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229788, 232746, 1961457⟩ CTN.nil) ⟨229792, 237568, 1923594⟩ CTN.nil) ⟨229797, 232980, 2243163⟩ (CTN.node CTN.nil ⟨229798, 233604, 2252323⟩ CTN.nil))) ⟨229798, 235236, 2190406⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229798, 236100, 2158488⟩ CTN.nil) ⟨229799, 233062, 2306981⟩ CTN.nil) ⟨229804, 232762, 2491561⟩ (CTN.node (CTN.node CTN.nil ⟨229804, 233906, 2443126⟩ CTN.nil) ⟨229804, 234674, 2411269⟩ CTN.nil)) ⟨229804, 235506, 2377342⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229808, 237568, 2427180⟩ CTN.nil) ⟨229810, 236144, 2555014⟩ CTN.nil) ⟨229812, 237568, 2562224⟩ (CTN.node CTN.nil ⟨229813, 232964, 2808199⟩ CTN.nil)))) ⟨229813, 233140, 2799720⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229814, 232725, 2857297⟩ CTN.nil) ⟨229814, 233141, 2836938⟩ CTN.nil) ⟨229814, 233557, 2816759⟩ (CTN.node (CTN.node CTN.nil ⟨229814, 233652, 2812177⟩ CTN.nil) ⟨229814, 233684, 2810635⟩ CTN.nil)) ⟨229814, 234133, 2789116⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229814, 234516, 2770922⟩ CTN.nil) ⟨229814, 234804, 2757339⟩ CTN.nil) ⟨229814, 235636, 2718564⟩ (CTN.node CTN.nil ⟨229814, 236372, 2684829⟩ CTN.nil))) ⟨229816, 234119, 2863803⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229816, 234806, 2830401⟩ CTN.nil) ⟨229816, 237568, 2700929⟩ CTN.nil) ⟨229820, 232778, 3084897⟩ (CTN.node CTN.nil ⟨229824, 237436, 2995979⟩ CTN.nil)) ⟨229824, 237568, 2989319⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229828, 237504, 3142394⟩ CTN.nil) ⟨229828, 237568, 3139005⟩ CTN.nil) ⟨229829, 232692, 3452062⟩ (CTN.node CTN.nil ⟨229829, 233172, 3423696⟩ CTN.nil))))) ⟨229829, 233556, 3401213⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229829, 233588, 3399347⟩ CTN.nil) ⟨229830, 233636, 3437416⟩ CTN.nil) ⟨229830, 233668, 3435531⟩ (CTN.node (CTN.node CTN.nil ⟨229830, 234500, 3386985⟩ CTN.nil) ⟨229830, 234756, 3372221⟩ CTN.nil)) ⟨229830, 235332, 3339294⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229831, 232710, 3534279⟩ CTN.nil) ⟨229831, 233558, 3483178⟩ CTN.nil) ⟨229834, 236560, 3428270⟩ (CTN.node CTN.nil ⟨229846, 233557, 4130101⟩ CTN.nil))) ⟨229846, 233620, 4125643⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229846, 235380, 4003507⟩ CTN.nil) ⟨229846, 235604, 3988288⟩ CTN.nil) ⟨229846, 236436, 3932392⟩ (CTN.node (CTN.node CTN.nil ⟨229848, 237568, 3942359⟩ CTN.nil) ⟨229856, 233504, 4596148⟩ CTN.nil)) ⟨229856, 234080, 4551031⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229860, 237568, 4468319⟩ CTN.nil) ⟨229861, 233156, 4865462⟩ CTN.nil) ⟨229862, 232725, 4951104⟩ (CTN.node CTN.nil ⟨229863, 232790, 4995226⟩ CTN.nil)))) ⟨229863, 233206, 4959643⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229863, 233622, 4924377⟩ CTN.nil) ⟨229872, 237568, 5027250⟩ CTN.nil) ⟨229876, 237568, 5220888⟩ (CTN.node (CTN.node CTN.nil ⟨229878, 232741, 5774734⟩ CTN.nil) ⟨229878, 233157, 5733589⟩ CTN.nil)) ⟨229880, 237568, 5418191⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229888, 234720, 6111919⟩ CTN.nil) ⟨229888, 236384, 5941466⟩ CTN.nil) ⟨229888, 237568, 5823791⟩ (CTN.node CTN.nil ⟨229892, 237568, 6032088⟩ CTN.nil))) ⟨229894, 232773, 6659715⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229894, 233045, 6628647⟩ CTN.nil) ⟨229894, 233157, 6615907⟩ CTN.nil) ⟨229894, 233700, 6554572⟩ (CTN.node CTN.nil ⟨229894, 233732, 6550979⟩ CTN.nil)) ⟨229894, 234468, 6469030⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229894, 235588, 6346769⟩ CTN.nil) ⟨229895, 233190, 6669370⟩ CTN.nil) ⟨229898, 235046, 6628700⟩ (CTN.node CTN.nil ⟨229898, 236646, 6451068⟩ CTN.nil))))))))

noncomputable def tab18 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229910, 234213, 7425860⟩ CTN.nil) ⟨229910, 234452, 7395597⟩ CTN.nil) ⟨229910, 234516, 7387519⟩ (CTN.node (CTN.node CTN.nil ⟨229910, 234900, 7339283⟩ CTN.nil) ⟨229910, 235284, 7291441⟩ CTN.nil)) ⟨229910, 235380, 7279541⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229911, 232406, 7721746⟩ CTN.nil) ⟨229911, 232774, 7672983⟩ CTN.nil) ⟨229912, 237568, 7128564⟩ (CTN.node CTN.nil ⟨229920, 233168, 8182971⟩ CTN.nil))) ⟨229920, 233600, 8122547⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229920, 234176, 8042847⟩ CTN.nil) ⟨229920, 234752, 7964122⟩ CTN.nil) ⟨229920, 235584, 7852101⟩ (CTN.node (CTN.node CTN.nil ⟨229924, 237568, 7830449⟩ CTN.nil) ⟨229926, 232789, 8624595⟩ CTN.nil)) ⟨229926, 233109, 8577288⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229926, 233796, 8476816⟩ CTN.nil) ⟨229926, 234500, 8375379⟩ CTN.nil) ⟨229926, 235332, 8257448⟩ (CTN.node CTN.nil ⟨229926, 235460, 8239489⟩ CTN.nil)))) ⟨229926, 236228, 8132758⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229926, 236292, 8123941⟩ CTN.nil) ⟨229927, 232790, 8690008⟩ CTN.nil) ⟨229927, 232806, 8687617⟩ (CTN.node (CTN.node CTN.nil ⟨229927, 233222, 8625736⟩ CTN.nil) ⟨229928, 236592, 8205894⟩ CTN.nil)) ⟨229928, 237568, 8071745⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229930, 235078, 8546836⟩ CTN.nil) ⟨229930, 235846, 8435944⟩ CTN.nil) ⟨229936, 234420, 9035256⟩ (CTN.node CTN.nil ⟨229936, 235000, 8946299⟩ CTN.nil))) ⟨229938, 236336, 8873856⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229940, 237568, 8817641⟩ CTN.nil) ⟨229942, 233237, 9629014⟩ CTN.nil) ⟨229944, 233852, 9664833⟩ (CTN.node (CTN.node CTN.nil ⟨229944, 235670, 9369754⟩ CTN.nil) ⟨229944, 237568, 9073610⟩ CTN.nil)) ⟨229952, 233168, 10342444⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229952, 233600, 10266074⟩ CTN.nil) ⟨229952, 234176, 10165341⟩ CTN.nil) ⟨229952, 234752, 10065841⟩ (CTN.node CTN.nil ⟨229952, 234784, 10060349⟩ CTN.nil))))) ⟨229952, 235616, 9918862⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229958, 233796, 10660090⟩ CTN.nil) ⟨229958, 234564, 10521026⟩ CTN.nil) ⟨229960, 237568, 10134173⟩ (CTN.node (CTN.node CTN.nil ⟨229973, 233252, 11879979⟩ CTN.nil) ⟨229974, 232469, 12118688⟩ CTN.nil)) ⟨229974, 232901, 12028934⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229974, 233317, 11943288⟩ CTN.nil) ⟨229974, 233733, 11858404⟩ CTN.nil) ⟨229974, 233844, 11835882⟩ (CTN.node CTN.nil ⟨229974, 233876, 11829399⟩ CTN.nil))) ⟨229974, 234708, 11662392⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229974, 235828, 11442201⟩ CTN.nil) ⟨229974, 236564, 11300331⟩ CTN.nil) ⟨229975, 233270, 12029791⟩ (CTN.node (CTN.node CTN.nil ⟨229975, 233686, 11944274⟩ CTN.nil) ⟨229975, 233718, 11937727⟩ CTN.nil)) ⟨229975, 234262, 11827117⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229975, 234294, 11820650⟩ CTN.nil) ⟨229976, 235702, 11614423⟩ CTN.nil) ⟨229986, 235688, 12370129⟩ (CTN.node CTN.nil ⟨229986, 236848, 12129333⟩ CTN.nil)))) ⟨229988, 237568, 12131444⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨229989, 233332, 13117837⟩ CTN.nil) ⟨229990, 233141, 13241665⟩ CTN.nil) ⟨229990, 234596, 12915882⟩ (CTN.node (CTN.node CTN.nil ⟨229990, 234948, 12838577⟩ CTN.nil) ⟨229990, 236292, 12548682⟩ CTN.nil)) ⟨229990, 236548, 12494395⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨229996, 234130, 13500556⟩ CTN.nil) ⟨229996, 234898, 13324687⟩ CTN.nil) ⟨229996, 235730, 13137382⟩ (CTN.node CTN.nil ⟨230000, 237568, 13042479⟩ CTN.nil))) ⟨230002, 235472, 13674213⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230002, 236336, 13475153⟩ CTN.nil) ⟨230002, 236400, 13460552⟩ CTN.nil) ⟨230004, 237568, 13353501⟩ (CTN.node CTN.nil ⟨230005, 232884, 14546630⟩ CTN.nil)) ⟨230006, 232485, 14732515⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230006, 233733, 14420064⟩ CTN.nil) ⟨230006, 235572, 13974593⟩ CTN.nil) ⟨230008, 237568, 13668194⟩ (CTN.node CTN.nil ⟨230016, 237568, 14308597⟩ CTN.nil)))))) ⟨230018, 234688, 15195229⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230018, 235424, 15005915⟩ CTN.nil) ⟨230018, 236288, 14787424⟩ CTN.nil) ⟨230018, 236352, 14771398⟩ (CTN.node (CTN.node CTN.nil ⟨230020, 237568, 14634307⟩ CTN.nil) ⟨230022, 232885, 16026496⟩ CTN.nil)) ⟨230022, 232901, 16022088⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230023, 233366, 15983209⟩ CTN.nil) ⟨230024, 233303, 16089408⟩ CTN.nil) ⟨230027, 233817, 16214117⟩ (CTN.node CTN.nil ⟨230032, 237568, 15633473⟩ CTN.nil))) ⟨230034, 236400, 16118166⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230038, 232917, 17475558⟩ CTN.nil) ⟨230038, 233333, 17351140⟩ CTN.nil) ⟨230043, 233417, 17790778⟩ (CTN.node (CTN.node CTN.nil ⟨230048, 237568, 17017120⟩ CTN.nil) ⟨230052, 237568, 17372216⟩ CTN.nil)) ⟨230055, 232934, 19088678⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230058, 235784, 18460572⟩ CTN.nil) ⟨230058, 236616, 18202040⟩ CTN.nil) ⟨230058, 236816, 18140569⟩ (CTN.node CTN.nil ⟨230059, 233017, 19452105⟩ CTN.nil)))) ⟨230062, 234164, 19363223⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230068, 233347, 20230593⟩ CTN.nil) ⟨230068, 233395, 20213939⟩ CTN.nil) ⟨230068, 233779, 20081322⟩ (CTN.node (CTN.node CTN.nil ⟨230069, 232980, 20459072⟩ CTN.nil) ⟨230070, 233349, 20430029⟩ CTN.nil)) ⟨230070, 234708, 19960488⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230070, 235028, 19851895⟩ CTN.nil) ⟨230070, 235572, 19668976⟩ CTN.nil) ⟨230071, 232950, 20671627⟩ (CTN.node CTN.nil ⟨230071, 233350, 20530112⟩ CTN.nil))) ⟨230072, 235830, 19775740⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230072, 237568, 19202810⟩ CTN.nil) ⟨230075, 233033, 21048570⟩ CTN.nil) ⟨230080, 237568, 19960770⟩ (CTN.node (CTN.node CTN.nil ⟨230084, 235778, 20970788⟩ CTN.nil) ⟨230084, 237568, 20345264⟩ CTN.nil)) ⟨230086, 232965, 22212602⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230088, 237568, 20733432⟩ CTN.nil) ⟨230091, 233465, 22546080⟩ CTN.nil) ⟨230103, 232966, 24032240⟩ (CTN.node CTN.nil ⟨230104, 235862, 22976395⟩ CTN.nil))))) ⟨230104, 237568, 22322862⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230107, 234568, 23808578⟩ CTN.nil) ⟨230117, 232980, 25578843⟩ CTN.nil) ⟨230119, 232982, 25803700⟩ (CTN.node (CTN.node CTN.nil ⟨230119, 233846, 25424080⟩ CTN.nil) ⟨230119, 233878, 25410155⟩ CTN.nil)) ⟨230124, 235272, 25359523⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230128, 237568, 24817292⟩ CTN.nil) ⟨230132, 234040, 26804499⟩ CTN.nil) ⟨230132, 237568, 25245899⟩ (CTN.node CTN.nil ⟨230134, 233061, 27491057⟩ CTN.nil))) ⟨230134, 233461, 27302946⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230134, 233477, 27295455⟩ CTN.nil) ⟨230134, 234421, 26858004⟩ CTN.nil) ⟨230134, 235124, 26537915⟩ (CTN.node (CTN.node CTN.nil ⟨230134, 235860, 26207895⟩ CTN.nil) ⟨230135, 233046, 27614982⟩ CTN.nil)) ⟨230135, 233414, 27441069⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230135, 233462, 27418486⟩ CTN.nil) ⟨230136, 235094, 26777350⟩ CTN.nil) ⟨230136, 235126, 26762762⟩ (CTN.node CTN.nil ⟨230136, 235958, 26386920⟩ CTN.nil)))) ⟨230136, 237568, 25678183⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230140, 233930, 27778586⟩ CTN.nil) ⟨230144, 233792, 28313063⟩ CTN.nil) ⟨230144, 234368, 28035476⟩ (CTN.node (CTN.node CTN.nil ⟨230144, 237568, 26553782⟩ CTN.nil) ⟨230149, 233444, 29077447⟩ CTN.nil)) ⟨230150, 233013, 29414028⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230150, 233445, 29196688⟩ CTN.nil) ⟨230152, 235078, 28626649⟩ CTN.nil) ⟨230152, 237568, 27444090⟩ (CTN.node CTN.nil ⟨230156, 233530, 29876721⟩ CTN.nil))) ⟨230160, 237568, 28349110⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230162, 236592, 29052612⟩ CTN.nil) ⟨230163, 233874, 30550323⟩ CTN.nil) ⟨230163, 234450, 30250906⟩ (CTN.node CTN.nil ⟨230163, 234482, 30234380⟩ CTN.nil)) ⟨230165, 233444, 31022897⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230165, 233876, 30794091⟩ CTN.nil) ⟨230166, 232661, 31568415⟩ CTN.nil) ⟨230166, 233029, 31369276⟩ (CTN.node CTN.nil ⟨230166, 233045, 31360653⟩ CTN.nil))))))) ⟨230166, 234453, 30613336⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230168, 233974, 31110918⟩ CTN.nil) ⟨230168, 235126, 30505079⟩ CTN.nil) ⟨230168, 235926, 30093020⟩ (CTN.node (CTN.node CTN.nil ⟨230168, 237568, 29268840⟩ CTN.nil) ⟨230176, 233856, 32169082⟩ CTN.nil)) ⟨230176, 234432, 31853776⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230176, 237568, 30203283⟩ CTN.nil) ⟨230179, 233346, 32832098⟩ CTN.nil) ⟨230180, 236128, 31431934⟩ (CTN.node CTN.nil ⟨230180, 237568, 30676022⟩ CTN.nil))) ⟨230182, 233061, 33377827⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230183, 233462, 33276705⟩ CTN.nil) ⟨230183, 233942, 33004167⟩ CTN.nil) ⟨230183, 234486, 32698655⟩ (CTN.node (CTN.node CTN.nil ⟨230188, 235336, 32850975⟩ CTN.nil) ⟨230188, 236104, 32425211⟩ CTN.nil)) ⟨230192, 237568, 32116310⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230196, 237568, 32603763⟩ CTN.nil) ⟨230198, 235096, 34253815⟩ CTN.nil) ⟨230199, 233062, 35599248⟩ (CTN.node CTN.nil ⟨230200, 237568, 33094895⟩ CTN.nil)))) ⟨230204, 233162, 36204191⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230208, 233888, 36286960⟩ CTN.nil) ⟨230208, 237568, 34088195⟩ CTN.nil) ⟨230210, 235944, 35294981⟩ (CTN.node (CTN.node CTN.nil ⟨230210, 237104, 34608668⟩ CTN.nil) ⟨230212, 237568, 34590364⟩ CTN.nil)) ⟨230214, 233493, 37342140⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230214, 235908, 35834910⟩ CTN.nil) ⟨230214, 236740, 35333321⟩ CTN.nil) ⟨230215, 233478, 37487438⟩ (CTN.node CTN.nil ⟨230215, 233494, 37477154⟩ CTN.nil))) ⟨230215, 233510, 37466873⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230216, 234054, 37254015⟩ CTN.nil) ⟨230216, 235174, 36548700⟩ CTN.nil) ⟨230216, 235910, 36094284⟩ (CTN.node (CTN.node CTN.nil ⟨230216, 237568, 35096212⟩ CTN.nil) ⟨230220, 233178, 38366601⟩ CTN.nil)) ⟨230220, 234010, 37823331⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230222, 234356, 37870729⟩ CTN.nil) ⟨230224, 237568, 36118945⟩ CTN.nil) ⟨230226, 236592, 36981498⟩ (CTN.node CTN.nil ⟨230226, 236656, 36941471⟩ CTN.nil))))) ⟨230229, 233140, 39642288⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230229, 233940, 39102272⟩ CTN.nil) ⟨230229, 233972, 39080864⟩ CTN.nil) ⟨230230, 233141, 39781805⟩ (CTN.node (CTN.node CTN.nil ⟨230230, 233525, 39520526⟩ CTN.nil) ⟨230230, 233557, 39498850⟩ CTN.nil)) ⟨230230, 235220, 38392536⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230232, 234806, 38937532⟩ CTN.nil) ⟨230232, 235638, 38389974⟩ CTN.nil) ⟨230232, 235958, 38181941⟩ (CTN.node CTN.nil ⟨230236, 233194, 40591237⟩ CTN.nil))) ⟨230236, 234080, 39979556⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230240, 233888, 40673104⟩ CTN.nil) ⟨230240, 235040, 39880767⟩ CTN.nil) ⟨230240, 235072, 39859035⟩ (CTN.node (CTN.node CTN.nil ⟨230240, 235808, 39363247⟩ CTN.nil) ⟨230240, 235904, 39299148⟩ CTN.nil)) ⟨230245, 233108, 41938288⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230245, 233172, 41892216⟩ CTN.nil) ⟨230247, 233126, 42213976⟩ CTN.nil) ⟨230248, 237568, 39275453⟩ (CTN.node CTN.nil ⟨230252, 236168, 40767857⟩ CTN.nil)))) ⟨230256, 237568, 40357060⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230260, 233555, 43790849⟩ CTN.nil) ⟨230260, 233971, 43479930⟩ CTN.nil) ⟨230260, 233987, 43468027⟩ (CTN.node (CTN.node CTN.nil ⟨230260, 234019, 43444233⟩ CTN.nil) ⟨230260, 237568, 40903383⟩ CTN.nil)) ⟨230261, 233124, 44263844⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230263, 233142, 44546671⟩ CTN.nil) ⟨230263, 233542, 44241961⟩ CTN.nil) ⟨230264, 235254, 43110224⟩ (CTN.node CTN.nil ⟨230264, 235286, 43086753⟩ CTN.nil))) ⟨230264, 236118, 42482075⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230264, 237568, 41453386⟩ CTN.nil) ⟨230274, 237568, 42844495⟩ CTN.nil) ⟨230276, 237568, 43125477⟩ (CTN.node CTN.nil ⟨230279, 233622, 46569364⟩ CTN.nil)) ⟨230280, 235238, 45448816⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230280, 236006, 44859534⟩ CTN.nil) ⟨230280, 237568, 43690200⟩ CTN.nil) ⟨230292, 234130, 48135543⟩ (CTN.node CTN.nil ⟨230292, 237568, 45406453⟩ CTN.nil)))))) ⟨230293, 233172, 49088040⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230294, 233157, 49256713⟩ CTN.nil) ⟨230294, 233589, 48892978⟩ CTN.nil) ⟨230294, 233637, 48852771⟩ (CTN.node (CTN.node CTN.nil ⟨230294, 235316, 47472001⟩ CTN.nil) ⟨230294, 236052, 46882127⟩ CTN.nil)) ⟨230294, 236148, 46805865⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230295, 232790, 49725642⟩ CTN.nil) ⟨230296, 235286, 47797857⟩ CTN.nil) ⟨230296, 235292, 47792977⟩ (CTN.node CTN.nil ⟨230296, 237568, 45985898⟩ CTN.nil))) ⟨230304, 237568, 47155829⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230308, 233443, 51215107⟩ CTN.nil) ⟨230308, 234114, 50629892⟩ CTN.nil) ⟨230310, 233189, 51758402⟩ (CTN.node (CTN.node CTN.nil ⟨230310, 233573, 51418534⟩ CTN.nil) ⟨230310, 233589, 51404433⟩ CTN.nil)) ⟨230310, 236868, 48613929⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230310, 237568, 48042939⟩ CTN.nil) ⟨230312, 234918, 50561108⟩ CTN.nil) ⟨230312, 237568, 48340482⟩ (CTN.node CTN.nil ⟨230320, 237568, 49539858⟩ CTN.nil)))) ⟨230324, 233651, 53596661⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230324, 234067, 53216275⟩ CTN.nil) ⟨230324, 234194, 53100821⟩ CTN.nil) ⟨230324, 235026, 52352155⟩ (CTN.node (CTN.node CTN.nil ⟨230324, 235282, 52124455⟩ CTN.nil) ⟨230324, 236722, 50866457⟩ CTN.nil)) ⟨230324, 237568, 50145066⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230326, 233205, 54335665⟩ CTN.nil) ⟨230326, 234629, 53027253⟩ CTN.nil) ⟨230327, 233622, 54111278⟩ (CTN.node CTN.nil ⟨230327, 234614, 53200992⟩ CTN.nil))) ⟨230328, 237568, 50753955⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230336, 234560, 54703744⟩ CTN.nil) ⟨230336, 235904, 53466515⟩ CTN.nil) ⟨230336, 236768, 52689597⟩ (CTN.node CTN.nil ⟨230340, 233507, 56362421⟩ CTN.nil)) ⟨230340, 234178, 55718565⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230340, 236674, 53402796⟩ CTN.nil) ⟨230340, 237568, 52602707⟩ CTN.nil) ⟨230341, 233636, 56404228⟩ (CTN.node CTN.nil ⟨230341, 234068, 55988565⟩ CTN.nil))))) ⟨230342, 233205, 56990571⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230342, 234916, 55346661⟩ CTN.nil) ⟨230343, 233206, 57157627⟩ CTN.nil) ⟨230343, 233222, 57141928⟩ (CTN.node (CTN.node CTN.nil ⟨230344, 237568, 53226318⟩ CTN.nil) ⟨230352, 233184, 58703260⟩ CTN.nil)) ⟨230352, 237568, 54484584⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230356, 233635, 58929371⟩ CTN.nil) ⟨230356, 237568, 55119238⟩ CTN.nil) ⟨230358, 233221, 59692506⟩ (CTN.node CTN.nil ⟨230358, 233637, 59268078⟩ CTN.nil))) ⟨230359, 233654, 59421496⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230359, 234646, 58422015⟩ CTN.nil) ⟨230360, 236118, 57141227⟩ CTN.nil) ⟨230360, 236918, 56372591⟩ (CTN.node (CTN.node CTN.nil ⟨230368, 236252, 58328244⟩ CTN.nil) ⟨230368, 237568, 57045284⟩ CTN.nil)) ⟨230371, 234098, 61023237⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230371, 234674, 60425731⟩ CTN.nil) ⟨230371, 234706, 60392752⟩ CTN.nil) ⟨230372, 234178, 61112135⟩ (CTN.node CTN.nil ⟨230372, 234946, 60316201⟩ CTN.nil)))) ⟨230372, 237568, 57694661⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230374, 233669, 61995298⟩ CTN.nil) ⟨230376, 237568, 58347719⟩ CTN.nil) ⟨230384, 233168, 64302320⟩ (CTN.node (CTN.node CTN.nil ⟨230384, 235448, 61845150⟩ CTN.nil) ⟨230384, 237568, 59664876⟩ CTN.nil)) ⟨230388, 234226, 63850073⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230388, 234994, 63018648⟩ CTN.nil) ⟨230388, 236722, 61196873⟩ CTN.nil) ⟨230388, 237568, 60328976⟩ (CTN.node CTN.nil ⟨230390, 232869, 65714142⟩ CTN.nil))) ⟨230390, 232885, 65696067⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230390, 233717, 64764651⟩ CTN.nil) ⟨230390, 233733, 64746901⟩ CTN.nil) ⟨230390, 234133, 64305134⟩ (CTN.node CTN.nil ⟨230392, 237568, 60996756⟩ CTN.nil)) ⟨230394, 236124, 62847620⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230400, 236896, 63054461⟩ CTN.nil) ⟨230400, 237568, 62343359⟩ CTN.nil) ⟨230404, 234210, 66718714⟩ (CTN.node CTN.nil ⟨230404, 234978, 65849876⟩ CTN.nil))))))))

noncomputable def tab19 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230404, 236098, 64608020⟩ CTN.nil) ⟨230404, 236674, 63980752⟩ CTN.nil) ⟨230404, 236930, 63704410⟩ (CTN.node (CTN.node CTN.nil ⟨230404, 237568, 63022182⟩ CTN.nil) ⟨230405, 233268, 67987263⟩ CTN.nil)) ⟨230405, 233332, 67912627⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230405, 233748, 67429982⟩ CTN.nil) ⟨230405, 234132, 66988264⟩ CTN.nil) ⟨230405, 234164, 66951617⟩ (CTN.node CTN.nil ⟨230407, 233286, 68333293⟩ CTN.nil))) ⟨230408, 237156, 64148955⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230408, 237568, 63704685⟩ CTN.nil) ⟨230416, 237568, 65080733⟩ CTN.nil) ⟨230420, 234194, 69651282⟩ (CTN.node (CTN.node CTN.nil ⟨230420, 234962, 68744194⟩ CTN.nil) ⟨230420, 235794, 67778119⟩ CTN.nil)) ⟨230420, 236626, 66828958⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230420, 237568, 65774278⟩ CTN.nil) ⟨230421, 233300, 70913179⟩ CTN.nil) ⟨230421, 234708, 69225156⟩ (CTN.node CTN.nil ⟨230422, 233285, 71118791⟩ CTN.nil)))) ⟨230422, 234133, 70093028⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230424, 235382, 68977890⟩ CTN.nil) ⟨230432, 233648, 72552847⟩ CTN.nil) ⟨230432, 234080, 72018206⟩ (CTN.node (CTN.node CTN.nil ⟨230432, 234656, 71312990⟩ CTN.nil) ⟨230432, 234688, 71274065⟩ CTN.nil)) ⟨230432, 235232, 70616387⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230437, 233316, 73919446⟩ CTN.nil) ⟨230438, 232917, 74620298⟩ CTN.nil) ⟨230438, 233301, 74129737⟩ (CTN.node CTN.nil ⟨230439, 234774, 72471710⟩ CTN.nil))) ⟨230440, 233719, 73980840⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230440, 236356, 70730967⟩ CTN.nil) ⟨230440, 237188, 69742794⟩ CTN.nil) ⟨230448, 237568, 70732144⟩ (CTN.node (CTN.node CTN.nil ⟨230452, 234179, 75686398⟩ CTN.nil) ⟨230452, 237568, 71455132⟩ CTN.nil)) ⟨230453, 233732, 76461159⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230454, 233317, 77202327⟩ CTN.nil) ⟨230454, 233333, 77181133⟩ CTN.nil) ⟨230454, 235324, 74599563⟩ (CTN.node CTN.nil ⟨230454, 235412, 74487971⟩ CTN.nil))))) ⟨230456, 235414, 74862743⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230456, 235446, 74822012⟩ CTN.nil) ⟨230456, 236278, 73772671⟩ CTN.nil) ⟨230456, 237110, 72741665⟩ (CTN.node (CTN.node CTN.nil ⟨230456, 237568, 72181801⟩ CTN.nil) ⟨230459, 233833, 77493354⟩ CTN.nil)) ⟨230464, 234144, 78053886⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230464, 234720, 77289776⟩ CTN.nil) ⟨230464, 237568, 73646178⟩ CTN.nil) ⟨230468, 234338, 78574751⟩ (CTN.node CTN.nil ⟨230468, 235074, 77594353⟩ CTN.nil))) ⟨230468, 235170, 77467605⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230468, 236002, 76379895⟩ CTN.nil) ⟨230468, 237568, 74383886⟩ CTN.nil) ⟨230470, 233733, 79787433⟩ (CTN.node (CTN.node CTN.nil ⟨230470, 233765, 79743711⟩ CTN.nil) ⟨230471, 233766, 79940182⟩ CTN.nil)) ⟨230472, 235398, 77936749⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230472, 237220, 75567507⟩ CTN.nil) ⟨230472, 237568, 75125275⟩ CTN.nil) ⟨230475, 233433, 81196115⟩ (CTN.node CTN.nil ⟨230484, 233811, 82470815⟩ CTN.nil)))) ⟨230484, 234354, 81708372⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230484, 235218, 80513279⟩ CTN.nil) ⟨230485, 232980, 83858959⟩ CTN.nil) ⟨230485, 233396, 83262087⟩ (CTN.node (CTN.node CTN.nil ⟨230485, 233812, 82670517⟩ CTN.nil) ⟨230485, 234228, 82084193⟩ CTN.nil)) ⟨230487, 233366, 83711009⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230488, 237078, 78776169⟩ CTN.nil) ⟨230491, 233449, 84405820⟩ CTN.nil) ⟨230492, 234912, 82519720⟩ (CTN.node CTN.nil ⟨230496, 233744, 84997886⟩ CTN.nil))) ⟨230496, 234176, 84371794⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230496, 234752, 83545947⟩ CTN.nil) ⟨230496, 235328, 82730182⟩ CTN.nil) ⟨230500, 233363, 86378902⟩ (CTN.node CTN.nil ⟨230500, 234338, 84948866⟩ CTN.nil)) ⟨230500, 235106, 83843229⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230500, 235938, 82665681⟩ CTN.nil) ⟨230502, 233365, 86789411⟩ CTN.nil) ⟨230502, 233381, 86765589⟩ (CTN.node CTN.nil ⟨230502, 236228, 82653873⟩ CTN.nil)))))) ⟨230502, 237060, 81498505⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230503, 233782, 86376854⟩ CTN.nil) ⟨230503, 233798, 86353188⟩ CTN.nil) ⟨230504, 237568, 81188858⟩ (CTN.node (CTN.node CTN.nil ⟨230507, 233881, 87054134⟩ CTN.nil) ⟨230512, 237568, 82741549⟩ CTN.nil)) ⟨230516, 233848, 88971771⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230516, 233859, 88955016⟩ CTN.nil) ⟨230516, 234275, 88324246⟩ CTN.nil) ⟨230516, 234418, 88108711⟩ (CTN.node CTN.nil ⟨230516, 234424, 88099682⟩ CTN.nil))) ⟨230516, 235250, 86867649⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230516, 235506, 86490187⟩ CTN.nil) ⟨230516, 235538, 86443148⟩ CTN.nil) ⟨230516, 236946, 84404749⟩ (CTN.node (CTN.node CTN.nil ⟨230516, 237568, 83523414⟩ CTN.nil) ⟨230517, 234228, 88602706⟩ CTN.nil)) ⟨230518, 233397, 90083295⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230518, 233813, 89443263⟩ CTN.nil) ⟨230518, 236244, 85814641⟩ CTN.nil) ⟨230520, 233852, 89802406⟩ (CTN.node CTN.nil ⟨230520, 234428, 88922191⟩ CTN.nil)))) ⟨230520, 236246, 86213849⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230520, 237568, 84308957⟩ CTN.nil) ⟨230524, 234432, 89748467⟩ CTN.nil) ⟨230524, 237568, 85098180⟩ (CTN.node (CTN.node CTN.nil ⟨230528, 233744, 91656991⟩ CTN.nil) ⟨230528, 234176, 90981849⟩ CTN.nil)) ⟨230528, 234752, 90091302⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230528, 236192, 87912149⟩ CTN.nil) ⟨230528, 236960, 86776870⟩ CTN.nil) ⟨230528, 237024, 86683093⟩ (CTN.node CTN.nil ⟨230528, 237568, 85891082⟩ CTN.nil))) ⟨230532, 236258, 88628273⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230532, 237090, 87389549⟩ CTN.nil) ⟨230532, 237568, 86687663⟩ CTN.nil) ⟨230533, 233396, 93274961⟩ (CTN.node (CTN.node CTN.nil ⟨230535, 233398, 93701291⟩ CTN.nil) ⟨230536, 236230, 89488904⟩ CTN.nil)) ⟨230536, 237062, 88238004⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230536, 237568, 87487923⟩ CTN.nil) ⟨230548, 233843, 95783988⟩ CTN.nil) ⟨230548, 237274, 90357659⟩ (CTN.node CTN.nil ⟨230548, 237568, 89910774⟩ CTN.nil))))) ⟨230549, 233412, 96712420⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230549, 233828, 96025334⟩ CTN.nil) ⟨230550, 233045, 97543606⟩ CTN.nil) ⟨230550, 233061, 97516796⟩ (CTN.node (CTN.node CTN.nil ⟨230550, 233461, 96849526⟩ CTN.nil) ⟨230550, 233893, 96135273⟩ CTN.nil)) ⟨230550, 234309, 95453688⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230550, 236276, 92311513⟩ CTN.nil) ⟨230550, 237108, 91021407⟩ CTN.nil) ⟨230551, 233462, 97066462⟩ (CTN.node CTN.nil ⟨230551, 233830, 96456247⟩ CTN.nil))) ⟨230551, 234262, 95746014⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230551, 234294, 95693665⟩ CTN.nil) ⟨230552, 235542, 93890871⟩ CTN.nil) ⟨230552, 237110, 91429444⟩ (CTN.node (CTN.node CTN.nil ⟨230562, 235104, 96734263⟩ CTN.nil) ⟨230565, 233828, 99526504⟩ CTN.nil)) ⟨230568, 237568, 94022426⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230572, 233946, 100874006⟩ CTN.nil) ⟨230572, 234674, 99626875⟩ CTN.nil) ⟨230576, 237568, 95692833⟩ (CTN.node CTN.nil ⟨230580, 234450, 101777446⟩ CTN.nil)))) ⟨230580, 235218, 100453408⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230580, 236946, 97552171⟩ CTN.nil) ⟨230580, 237568, 96533554⟩ CTN.nil) ⟨230581, 233460, 103742573⟩ (CTN.node (CTN.node CTN.nil ⟨230581, 233732, 103260024⟩ CTN.nil) ⟨230582, 233061, 104683345⟩ CTN.nil)) ⟨230582, 233077, 104654574⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230582, 234309, 102468618⟩ CTN.nil) ⟨230584, 235574, 100720349⟩ CTN.nil) ⟨230584, 235606, 100665587⟩ (CTN.node CTN.nil ⟨230584, 236438, 99254755⟩ CTN.nil))) ⟨230584, 237270, 97868557⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230592, 237568, 99077780⟩ CTN.nil) ⟨230596, 237568, 99933209⟩ CTN.nil) ⟨230597, 233460, 107392096⟩ (CTN.node CTN.nil ⟨230597, 234900, 104780283⟩ CTN.nil)) ⟨230598, 233093, 108302366⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230598, 233461, 107620440⟩ CTN.nil) ⟨230598, 233477, 107590913⟩ CTN.nil) ⟨230600, 235558, 104280264⟩ (CTN.node CTN.nil ⟨230600, 237568, 100792316⟩ CTN.nil))))))) ⟨230612, 237568, 103391699⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230613, 233796, 110466752⟩ CTN.nil) ⟨230614, 233493, 111275847⟩ CTN.nil) ⟨230614, 234901, 108629190⟩ (CTN.node (CTN.node CTN.nil ⟨230614, 235516, 107497871⟩ CTN.nil) ⟨230614, 235572, 107395590⟩ CTN.nil)) ⟨230614, 235604, 107337199⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230616, 236444, 106264265⟩ CTN.nil) ⟨230616, 237206, 104904068⟩ CTN.nil) ⟨230624, 236192, 108518981⟩ (CTN.node CTN.nil ⟨230629, 233924, 113970720⟩ CTN.nil))) ⟨230632, 237568, 107797532⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230636, 235506, 112550414⟩ CTN.nil) ⟨230636, 237568, 108689727⟩ CTN.nil) ⟨230640, 237568, 109585597⟩ (CTN.node (CTN.node CTN.nil ⟨230644, 233923, 117541240⟩ CTN.nil) ⟨230644, 235602, 114223063⟩ CTN.nil)) ⟨230644, 235634, 114160967⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230644, 237568, 110485144⟩ CTN.nil) ⟨230645, 233140, 119372957⟩ CTN.nil) ⟨230645, 233556, 118523894⟩ (CTN.node CTN.nil ⟨230645, 233972, 117682367⟩ CTN.nil)))) ⟨230646, 233557, 118763476⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230646, 233925, 118017164⟩ CTN.nil) ⟨230646, 234357, 117148525⟩ CTN.nil) ⟨230646, 234389, 117084500⟩ (CTN.node (CTN.node CTN.nil ⟨230646, 234965, 115939492⟩ CTN.nil) ⟨230646, 235636, 114623233⟩ CTN.nil)) ⟨230646, 236468, 113016987⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230646, 237300, 111438784⟩ CTN.nil) ⟨230647, 233942, 118223100⟩ CTN.nil) ⟨230648, 236406, 113596742⟩ (CTN.node CTN.nil ⟨230648, 237568, 111388365⟩ CTN.nil))) ⟨230660, 237568, 114120081⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230661, 233588, 122352162⟩ CTN.nil) ⟨230661, 234004, 121483573⟩ CTN.nil) ⟨230661, 234996, 119443226⟩ (CTN.node (CTN.node CTN.nil ⟨230662, 233541, 122696399⟩ CTN.nil) ⟨230662, 234468, 120765588⟩ CTN.nil)) ⟨230662, 234500, 120699617⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230662, 235332, 119000084⟩ CTN.nil) ⟨230662, 235588, 118483178⟩ CTN.nil) ⟨230662, 236100, 117457761⟩ (CTN.node CTN.nil ⟨230666, 235814, 118976636⟩ CTN.nil))))) ⟨230677, 233156, 127248002⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230677, 233540, 126412318⟩ CTN.nil) ⟨230677, 233828, 125790054⟩ CTN.nil) ⟨230678, 236436, 120563399⟩ (CTN.node (CTN.node CTN.nil ⟨230678, 237236, 118943806⟩ CTN.nil) ⟨230679, 233558, 126872516⟩ CTN.nil)) ⟨230680, 237270, 119344698⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230688, 235108, 125756022⟩ CTN.nil) ⟨230688, 237568, 120622695⟩ CTN.nil) ⟨230692, 233987, 129188549⟩ (CTN.node CTN.nil ⟨230693, 233556, 130398931⟩ CTN.nil))) ⟨230693, 234420, 128485204⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230695, 233974, 129972127⟩ CTN.nil) ⟨230695, 234422, 128980441⟩ CTN.nil) ⟨230695, 234454, 128909969⟩ (CTN.node (CTN.node CTN.nil ⟨230698, 235846, 126623741⟩ CTN.nil) ⟨230698, 237446, 123241890⟩ CTN.nil)) ⟨230704, 235188, 129537622⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230704, 235768, 128266403⟩ CTN.nil) ⟨230704, 237568, 124419297⟩ CTN.nil) ⟨230708, 234040, 133118042⟩ (CTN.node CTN.nil ⟨230708, 234616, 131814303⟩ CTN.nil)))) ⟨230708, 237568, 125377630⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230709, 233588, 134409385⟩ CTN.nil) ⟨230710, 234053, 133598537⟩ CTN.nil) ⟨230710, 234421, 132760777⟩ (CTN.node (CTN.node CTN.nil ⟨230710, 234453, 132688239⟩ CTN.nil) ⟨230710, 235668, 129970352⟩ CTN.nil)) ⟨230710, 236468, 128218737⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230710, 237300, 126428252⟩ CTN.nil) ⟨230711, 233990, 133998310⟩ CTN.nil) ⟨230712, 234620, 132816630⟩ (CTN.node CTN.nil ⟨230712, 237568, 126339636⟩ CTN.nil))) ⟨230714, 234504, 133587998⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230716, 237568, 127305315⟩ CTN.nil) ⟨230720, 233504, 137450012⟩ CTN.nil) ⟨230720, 234368, 135432358⟩ (CTN.node CTN.nil ⟨230720, 234944, 134107803⟩ CTN.nil)) ⟨230720, 235520, 132799403⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230720, 235552, 132727184⟩ CTN.nil) ⟨230720, 236384, 130866583⟩ CTN.nil) ⟨230720, 237568, 128274666⟩ (CTN.node CTN.nil ⟨230724, 236418, 131783357⟩ CTN.nil)))))) ⟨230724, 237568, 129247689⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230725, 233604, 138516232⟩ CTN.nil) ⟨230725, 234020, 137532960⟩ CTN.nil) ⟨230726, 234021, 137789818⟩ (CTN.node (CTN.node CTN.nil ⟨230726, 234564, 136517089⟩ CTN.nil) ⟨230726, 235652, 134010867⟩ CTN.nil)) ⟨230726, 236420, 132276337⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230728, 237568, 130224384⟩ CTN.nil) ⟨230730, 234104, 138632123⟩ CTN.nil) ⟨230730, 236646, 132765153⟩ (CTN.node CTN.nil ⟨230739, 234450, 140150204⟩ CTN.nil))) ⟨230740, 233651, 142343327⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230740, 237568, 133176498⟩ CTN.nil) ⟨230741, 234020, 141709649⟩ CTN.nil) ⟨230742, 233237, 143890777⟩ (CTN.node (CTN.node CTN.nil ⟨230742, 234021, 141970334⟩ CTN.nil) ⟨230742, 235029, 139548035⟩ CTN.nil)) ⟨230746, 233704, 143803575⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230752, 234000, 144666808⟩ CTN.nil) ⟨230752, 234432, 143602361⟩ CTN.nil) ⟨230752, 235008, 142198282⟩ (CTN.node CTN.nil ⟨230752, 235584, 140811326⟩ CTN.nil)))) ⟨230756, 237568, 137164046⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230758, 233637, 147177819⟩ CTN.nil) ⟨230758, 234596, 144783598⟩ CTN.nil) ⟨230758, 234628, 144704550⟩ (CTN.node (CTN.node CTN.nil ⟨230758, 235332, 142979070⟩ CTN.nil) ⟨230758, 235460, 142668115⟩ CTN.nil)) ⟨230758, 235716, 142048738⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230758, 236292, 140667385⟩ CTN.nil) ⟨230760, 237568, 138170109⟩ CTN.nil) ⟨230762, 234136, 146994266⟩ (CTN.node CTN.nil ⟨230762, 236678, 140774236⟩ CTN.nil))) ⟨230764, 234898, 145623005⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230764, 237568, 139179842⟩ CTN.nil) ⟨230768, 233600, 149974082⟩ CTN.nil) ⟨230768, 235832, 144371112⟩ (CTN.node CTN.nil ⟨230768, 236600, 142503905⟩ CTN.nil)) ⟨230768, 237568, 140193245⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230772, 237568, 141210318⟩ CTN.nil) ⟨230773, 233652, 151199924⟩ CTN.nil) ⟨230774, 233637, 151511489⟩ (CTN.node CTN.nil ⟨230774, 234580, 149087479⟩ CTN.nil))))) ⟨230774, 235077, 147829433⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230774, 235348, 147149046⟩ CTN.nil) ⟨230774, 235764, 146112215⟩ CTN.nil) ⟨230774, 236180, 145084501⟩ (CTN.node (CTN.node CTN.nil ⟨230774, 237012, 143056044⟩ CTN.nil) ⟨230776, 235840, 146449763⟩ CTN.nil)) ⟨230776, 237568, 142231060⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230782, 236484, 146425875⟩ CTN.nil) ⟨230784, 233616, 154307433⟩ CTN.nil) ⟨230784, 234464, 152084952⟩ (CTN.node CTN.nil ⟨230784, 235040, 150598137⟩ CTN.nil))) ⟨230784, 235616, 149129450⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230784, 236448, 147039483⟩ CTN.nil) ⟨230788, 233651, 155317670⟩ CTN.nil) ⟨230790, 233653, 155865182⟩ (CTN.node (CTN.node CTN.nil ⟨230790, 234069, 154758988⟩ CTN.nil) ⟨230794, 237568, 146869803⟩ CTN.nil)) ⟨230804, 237568, 149478980⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230805, 234132, 158735707⟩ CTN.nil) ⟨230805, 235092, 156156223⟩ CTN.nil) ⟨230806, 233301, 161293877⟩ (CTN.node CTN.nil ⟨230806, 233717, 160147433⟩ CTN.nil)))) ⟨230806, 234101, 159098205⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230806, 234533, 157928076⟩ CTN.nil) ⟨230806, 234565, 157841828⟩ CTN.nil) ⟨230806, 236660, 152321200⟩ (CTN.node (CTN.node CTN.nil ⟨230806, 237492, 150195855⟩ CTN.nil) ⟨230808, 236534, 153181099⟩ CTN.nil)) ⟨230812, 234656, 159256087⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230812, 235808, 156163733⟩ CTN.nil) ⟨230816, 233600, 163289474⟩ CTN.nil) ⟨230816, 234032, 162085950⟩ (CTN.node CTN.nil ⟨230816, 234464, 160893496⟩ CTN.nil))) ⟨230816, 235040, 159320567⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230816, 235616, 157766816⟩ CTN.nil) ⟨230816, 236384, 155724498⟩ CTN.nil) ⟨230816, 236480, 155471538⟩ (CTN.node CTN.nil ⟨230821, 233684, 164472053⟩ CTN.nil)) ⟨230821, 233748, 164291818⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230821, 234164, 163126293⟩ CTN.nil) ⟨230822, 233301, 165841928⟩ CTN.nil) ⟨230822, 234101, 163584343⟩ (CTN.node CTN.nil ⟨230822, 235428, 159923636⟩ CTN.nil))))))))

noncomputable def tab20 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230823, 233702, 164989863⟩ CTN.nil) ⟨230827, 234617, 163550828⟩ CTN.nil) ⟨230828, 235730, 160756718⟩ (CTN.node (CTN.node CTN.nil ⟨230832, 235180, 163383640⟩ CTN.nil) ⟨230834, 235792, 162246139⟩ CTN.nil)) ⟨230834, 236560, 160147393⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230834, 236656, 159887442⟩ CTN.nil) ⟨230836, 234115, 167520638⟩ CTN.nil) ⟨230836, 234131, 167474806⟩ (CTN.node CTN.nil ⟨230836, 234547, 166288638⟩ CTN.nil))) ⟨230836, 235826, 162706936⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230836, 236690, 160341879⟩ CTN.nil) ⟨230836, 237568, 157982366⟩ CTN.nil) ⟨230837, 233700, 169002744⟩ (CTN.node (CTN.node CTN.nil ⟨230837, 234116, 167803552⟩ CTN.nil) ⟨230838, 233701, 169287909⟩ CTN.nil)) ⟨230838, 237396, 158981976⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230838, 237428, 158896201⟩ CTN.nil) ⟨230838, 237568, 158521618⟩ CTN.nil) ⟨230839, 234134, 168324014⟩ (CTN.node CTN.nil ⟨230839, 234550, 167131847⟩ CTN.nil)))) ⟨230840, 237568, 159061787⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230843, 234633, 168032648⟩ CTN.nil) ⟨230844, 237568, 160144873⟩ CTN.nil) ⟨230848, 237568, 161231625⟩ (CTN.node (CTN.node CTN.nil ⟨230850, 235520, 167482846⟩ CTN.nil) ⟨230850, 236352, 165134716⟩ CTN.nil)) ⟨230853, 233348, 174692309⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230853, 233732, 173545982⟩ CTN.nil) ⟨230854, 234133, 172648751⟩ CTN.nil) ⟨230854, 236292, 166418726⟩ (CTN.node CTN.nil ⟨230856, 237568, 163416122⟩ CTN.nil))) ⟨230864, 234080, 175719550⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230866, 236336, 169662830⟩ CTN.nil) ⟨230868, 236944, 168485267⟩ CTN.nil) ⟨230868, 237568, 166720348⟩ (CTN.node (CTN.node CTN.nil ⟨230869, 233748, 178195579⟩ CTN.nil) ⟨230870, 233733, 178537098⟩ CTN.nil)) ⟨230870, 234597, 175918868⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230870, 234629, 175822822⟩ CTN.nil) ⟨230870, 235860, 172177296⟩ CTN.nil) ⟨230882, 234688, 179155894⟩ (CTN.node CTN.nil ⟨230882, 235456, 176827577⟩ CTN.nil))))) ⟨230882, 236288, 174347763⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230885, 234164, 181657351⟩ CTN.nil) ⟨230886, 234149, 182001459⟩ CTN.nil) ⟨230886, 234165, 181951672⟩ (CTN.node (CTN.node CTN.nil ⟨230891, 233849, 184436991⟩ CTN.nil) ⟨230891, 234681, 181832812⟩ CTN.nil)) ⟨230892, 237568, 173427708⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230896, 237568, 174558419⟩ CTN.nil) ⟨230900, 234227, 185943911⟩ CTN.nil) ⟨230900, 234643, 184627471⟩ (CTN.node CTN.nil ⟨230900, 237568, 175692791⟩ CTN.nil))) ⟨230901, 233396, 188914007⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230901, 233812, 187571789⟩ CTN.nil) ⟨230901, 234228, 186241472⟩ CTN.nil) ⟨230902, 234197, 186641341⟩ (CTN.node (CTN.node CTN.nil ⟨230902, 235205, 183459237⟩ CTN.nil) ⟨230902, 235860, 181427812⟩ CTN.nil)) ⟨230903, 234198, 186939529⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230904, 237568, 176830825⟩ CTN.nil) ⟨230907, 233865, 189222441⟩ CTN.nil) ⟨230907, 235368, 184430561⟩ (CTN.node CTN.nil ⟨230912, 234560, 188493558⟩ CTN.nil)))) ⟨230912, 237344, 179795677⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230912, 237568, 179117874⟩ CTN.nil) ⟨230914, 237440, 180080089⟩ CTN.nil) ⟨230914, 237568, 179691925⟩ (CTN.node (CTN.node CTN.nil ⟨230916, 233779, 192253002⟩ CTN.nil) ⟨230916, 236610, 183207036⟩ CTN.nil)) ⟨230916, 237442, 180650203⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230917, 234212, 191138520⟩ CTN.nil) ⟨230918, 233781, 192860566⟩ CTN.nil) ⟨230924, 237568, 182575900⟩ (CTN.node CTN.nil ⟨230928, 233760, 196016443⟩ CTN.nil))) ⟨230931, 234642, 193999671⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230931, 235218, 192104521⟩ CTN.nil) ⟨230932, 233795, 197139661⟩ CTN.nil) ⟨230932, 234275, 195527368⟩ (CTN.node CTN.nil ⟨230932, 236944, 186856914⟩ CTN.nil)) ⟨230934, 233797, 197754693⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230934, 233813, 197700515⟩ CTN.nil) ⟨230934, 235892, 190815823⟩ CTN.nil) ⟨230935, 234230, 196603974⟩ (CTN.node CTN.nil ⟨230936, 236694, 188833047⟩ CTN.nil)))))) ⟨230936, 237568, 186066861⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230940, 237568, 187237832⟩ CTN.nil) ⟨230942, 236676, 190675059⟩ CTN.nil) ⟨230944, 237568, 188412461⟩ (CTN.node (CTN.node CTN.nil ⟨230947, 234674, 198817089⟩ CTN.nil) ⟨230950, 233829, 202652990⟩ CTN.nil)) ⟨230950, 234245, 201215817⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230956, 236104, 196768552⟩ CTN.nil) ⟨230956, 237568, 191958293⟩ CTN.nil) ⟨230960, 233744, 206113638⟩ (CTN.node CTN.nil ⟨230960, 237568, 193147551⟩ CTN.nil))) ⟨230964, 236666, 197323097⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230964, 237568, 194340466⟩ CTN.nil) ⟨230965, 233828, 207406893⟩ CTN.nil) ⟨230966, 233445, 209093477⟩ (CTN.node (CTN.node CTN.nil ⟨230966, 233461, 209036105⟩ CTN.nil) ⟨230966, 233477, 208978754⟩ CTN.nil)) ⟨230966, 233877, 207551334⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230966, 233893, 207494491⟩ CTN.nil) ⟨230966, 234293, 206079725⟩ CTN.nil) ⟨230966, 234309, 206023385⟩ (CTN.node CTN.nil ⟨230966, 235956, 200325537⟩ CTN.nil)))) ⟨230966, 236788, 197522103⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230966, 237524, 195082919⟩ CTN.nil) ⟨230966, 237568, 194938294⟩ CTN.nil) ⟨230968, 237568, 195537037⟩ (CTN.node (CTN.node CTN.nil ⟨230976, 237568, 197941146⟩ CTN.nil) ⟨230979, 234114, 210855528⟩ CTN.nil)) ⟨230980, 234275, 210595528⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230980, 237568, 199148684⟩ CTN.nil) ⟨230981, 234244, 211027152⟩ CTN.nil) ⟨230981, 234260, 210969448⟩ (CTN.node CTN.nil ⟨230981, 234324, 210738829⟩ CTN.nil))) ⟨230981, 235284, 207317067⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨230982, 233477, 214141122⟩ CTN.nil) ⟨230983, 234710, 209990237⟩ CTN.nil) ⟨230984, 237568, 200359877⟩ (CTN.node (CTN.node CTN.nil ⟨230988, 236136, 206513870⟩ CTN.nil) ⟨230995, 234738, 213722268⟩ CTN.nil)) ⟨230995, 235314, 211635302⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨230997, 233876, 217545372⟩ CTN.nil) ⟨230998, 233877, 217867807⟩ CTN.nil) ⟨230998, 234277, 216382210⟩ (CTN.node CTN.nil ⟨230998, 236724, 207564599⟩ CTN.nil))))) ⟨230998, 237568, 204627828⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231008, 234656, 218217920⟩ CTN.nil) ⟨231008, 234688, 218098809⟩ CTN.nil) ⟨231008, 235264, 215968655⟩ (CTN.node (CTN.node CTN.nil ⟨231008, 235808, 213980675⟩ CTN.nil) ⟨231010, 236448, 212300805⟩ CTN.nil)) ⟨231010, 237312, 209222927⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231010, 237376, 208997162⟩ CTN.nil) ⟨231011, 234178, 220989007⟩ CTN.nil) ⟨231012, 237568, 208940533⟩ (CTN.node CTN.nil ⟨231013, 233876, 222793175⟩ CTN.nil))) ⟨231013, 233892, 222732157⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231013, 234308, 221153012⟩ CTN.nil) ⟨231014, 233877, 223119409⟩ CTN.nil) ⟨231014, 234309, 221476851⟩ (CTN.node (CTN.node CTN.nil ⟨231020, 236936, 213692077⟩ CTN.nil) ⟨231020, 237568, 211425024⟩ CTN.nil)) ⟨231027, 234738, 224110380⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231028, 234323, 226034751⟩ CTN.nil) ⟨231028, 234755, 224373891⟩ CTN.nil) ⟨231028, 237568, 213924120⟩ (CTN.node CTN.nil ⟨231029, 233892, 228040720⟩ CTN.nil)))) ⟨231029, 234308, 226423937⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231030, 233525, 229815020⟩ CTN.nil) ⟨231030, 233893, 228370660⟩ CTN.nil) ⟨231030, 233909, 228308120⟩ (CTN.node (CTN.node CTN.nil ⟨231030, 235988, 220360751⟩ CTN.nil) ⟨231032, 237568, 215179144⟩ CTN.nil)) ⟨231040, 234720, 228470722⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231040, 235296, 226239569⟩ CTN.nil) ⟨231040, 237536, 217817591⟩ CTN.nil) ⟨231040, 237568, 217700143⟩ (CTN.node CTN.nil ⟨231046, 233925, 233617186⟩ CTN.nil))) ⟨231046, 234341, 231961100⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231046, 235972, 225608011⟩ CTN.nil) ⟨231047, 234774, 230585819⟩ CTN.nil) ⟨231048, 236006, 226130174⟩ (CTN.node CTN.nil ⟨231052, 236968, 223763169⟩ CTN.nil)) ⟨231058, 236048, 229242186⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231058, 236912, 225913105⟩ CTN.nil) ⟨231058, 237568, 223425762⟩ CTN.nil) ⟨231061, 233540, 240289020⟩ (CTN.node CTN.nil ⟨231061, 233556, 240223116⟩ CTN.nil))))))) ⟨231061, 234356, 236956537⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231061, 234388, 236827032⟩ CTN.nil) ⟨231061, 234804, 235151500⟩ CTN.nil) ⟨231062, 236052, 230542320⟩ (CTN.node (CTN.node CTN.nil ⟨231064, 237568, 225350719⟩ CTN.nil) ⟨231068, 235488, 234760678⟩ CTN.nil)) ⟨231072, 234752, 239076261⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231072, 235328, 236741856⟩ CTN.nil) ⟨231072, 235904, 234435879⟩ CTN.nil) ⟨231072, 236736, 231154373⟩ (CTN.node CTN.nil ⟨231076, 233939, 243797870⟩ CTN.nil))) ⟨231077, 234004, 243871428⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231077, 234420, 242143233⟩ CTN.nil) ⟨231078, 233957, 244412764⟩ CTN.nil) ⟨231078, 234357, 242746732⟩ (CTN.node (CTN.node CTN.nil ⟨231079, 234806, 241233873⟩ CTN.nil) ⟨231080, 237568, 230524054⟩ CTN.nil)) ⟨231084, 237000, 234059077⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231084, 237568, 231826504⟩ CTN.nil) ⟨231088, 236152, 238780214⟩ CTN.nil) ⟨231088, 236920, 235696137⟩ (CTN.node CTN.nil ⟨231092, 234424, 247287492⟩ CTN.nil)))) ⟨231092, 234435, 247241037⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231092, 234851, 245492176⟩ CTN.nil) ⟨231092, 235000, 244869545⟩ CTN.nil) ⟨231092, 236050, 240537395⟩ (CTN.node (CTN.node CTN.nil ⟨231092, 237568, 234442338⟩ CTN.nil) ⟨231093, 234372, 247853528⟩ CTN.nil)) ⟨231093, 234804, 246032726⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231094, 233973, 249899125⟩ CTN.nil) ⟨231094, 236084, 241071633⟩ CTN.nil) ⟨231096, 234428, 248655848⟩ (CTN.node CTN.nil ⟨231096, 235004, 246224563⟩ CTN.nil))) ⟨231096, 236160, 241434133⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231096, 237568, 235755722⟩ CTN.nil) ⟨231100, 235008, 247583201⟩ CTN.nil) ⟨231104, 234320, 251902219⟩ (CTN.node (CTN.node CTN.nil ⟨231104, 234752, 250051265⟩ CTN.nil) ⟨231104, 235328, 247609697⟩ CTN.nil)) ⟨231104, 235904, 245197862⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231104, 235936, 245064734⟩ CTN.nil) ⟨231104, 236168, 244102256⟩ CTN.nil) ⟨231104, 236672, 242027586⟩ (CTN.node CTN.nil ⟨231104, 236768, 241634913⟩ CTN.nil))))) ⟨231104, 237536, 238522035⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231104, 237568, 238393423⟩ CTN.nil) ⟨231108, 237568, 239717738⟩ CTN.nil) ⟨231109, 233588, 256849694⟩ (CTN.node (CTN.node CTN.nil ⟨231109, 233972, 255165981⟩ CTN.nil) ⟨231112, 236838, 244034250⟩ CTN.nil)) ⟨231112, 237568, 241045697⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231122, 237568, 244381529⟩ CTN.nil) ⟨231124, 234003, 260344872⟩ CTN.nil) ⟨231124, 234835, 256671306⟩ (CTN.node CTN.nil ⟨231124, 237568, 245051427⟩ CTN.nil))) ⟨231125, 233988, 260768011⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231126, 233621, 262770897⟩ CTN.nil) ⟨231126, 234469, 258986303⟩ CTN.nil) ⟨231126, 236980, 248172472⟩ (CTN.node (CTN.node CTN.nil ⟨231126, 237568, 245722235⟩ CTN.nil) ⟨231127, 234406, 259619366⟩ CTN.nil)) ⟨231132, 237568, 247740121⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231139, 234866, 261825752⟩ CTN.nil) ⟨231139, 235442, 259270451⟩ CTN.nil) ⟨231140, 234946, 261823066⟩ (CTN.node CTN.nil ⟨231141, 234020, 266355925⟩ CTN.nil)))) ⟨231141, 234404, 264613113⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231142, 237568, 251121466⟩ CTN.nil) ⟨231146, 234520, 265877613⟩ CTN.nil) ⟨231146, 236848, 255567489⟩ (CTN.node (CTN.node CTN.nil ⟨231148, 237568, 253161192⟩ CTN.nil) ⟨231152, 233936, 270720502⟩ CTN.nil)) ⟨231152, 237568, 254525558⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231156, 234067, 271566144⟩ CTN.nil) ⟨231156, 234483, 269642207⟩ CTN.nil) ⟨231156, 234899, 267735281⟩ (CTN.node CTN.nil ⟨231156, 234994, 267302173⟩ CTN.nil))) ⟨231156, 235026, 267156481⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231156, 235858, 263403095⟩ CTN.nil) ⟨231156, 236146, 262119224⟩ CTN.nil) ⟨231156, 236978, 258453956⟩ (CTN.node CTN.nil ⟨231156, 237568, 255893562⟩ CTN.nil)) ⟨231157, 234452, 270146155⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231158, 234453, 270502941⟩ CTN.nil) ⟨231158, 236916, 259417820⟩ CTN.nil) ⟨231160, 237568, 257265204⟩ (CTN.node CTN.nil ⟨231162, 234120, 273503018⟩ CTN.nil)))))) ⟨231168, 237568, 260019400⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231172, 234978, 273130600⟩ CTN.nil) ⟨231172, 235010, 272981721⟩ CTN.nil) ⟨231172, 235842, 269146235⟩ (CTN.node (CTN.node CTN.nil ⟨231172, 236098, 267979659⟩ CTN.nil) ⟨231172, 236674, 265377889⟩ CTN.nil)) ⟨231172, 237568, 261401954⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231173, 234036, 277926668⟩ CTN.nil) ⟨231174, 234053, 278213590⟩ CTN.nil) ⟨231174, 234453, 276317931⟩ (CTN.node CTN.nil ⟨231178, 234552, 277312111⟩ CTN.nil))) ⟨231180, 237568, 264177969⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231184, 234016, 282082759⟩ CTN.nil) ⟨231184, 237568, 265571429⟩ CTN.nil) ⟨231188, 234899, 279322749⟩ (CTN.node (CTN.node CTN.nil ⟨231188, 234962, 279022997⟩ CTN.nil) ⟨231188, 236722, 270809155⟩ CTN.nil)) ⟨231189, 234068, 283685825⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231190, 234069, 284052469⟩ CTN.nil) ⟨231190, 236180, 274022568⟩ CTN.nil) ⟨231192, 237568, 268369255⟩ (CTN.node CTN.nil ⟨231200, 234032, 287962907⟩ CTN.nil)))) ⟨231200, 236768, 274868936⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231200, 237568, 271181616⟩ CTN.nil) ⟨231203, 234962, 284532494⟩ CTN.nil) ⟨231203, 235538, 281756715⟩ (CTN.node (CTN.node CTN.nil ⟨231204, 234067, 289288626⟩ CTN.nil) ⟨231205, 234084, 289579530⟩ CTN.nil)) ⟨231205, 234500, 287528125⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231206, 234069, 290029193⟩ CTN.nil) ⟨231212, 237568, 275427405⟩ CTN.nil) ⟨231216, 234464, 291819187⟩ (CTN.node CTN.nil ⟨231216, 237568, 276849932⟩ CTN.nil))) ⟨231220, 234931, 290994826⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231220, 237568, 278276091⟩ CTN.nil) ⟨231221, 234132, 295369944⟩ CTN.nil) ⟨231222, 233717, 297857034⟩ (CTN.node (CTN.node CTN.nil ⟨231222, 234133, 295743684⟩ CTN.nil) ⟨231222, 234933, 291731977⟩ CTN.nil)) ⟨231222, 234965, 291572928⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231222, 236180, 285613437⟩ CTN.nil) ⟨231224, 237568, 279705879⟩ CTN.nil) ⟨231232, 237568, 282576347⟩ (CTN.node CTN.nil ⟨231235, 234962, 296464503⟩ CTN.nil))))) ⟨231236, 234915, 297079156⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231236, 235810, 292590222⟩ CTN.nil) ⟨231236, 236930, 287091571⟩ CTN.nil) ⟨231236, 237568, 284017026⟩ (CTN.node (CTN.node CTN.nil ⟨231237, 233732, 303530564⟩ CTN.nil) ⟨231237, 233748, 303447383⟩ CTN.nil)) ⟨231237, 234580, 299160985⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231237, 234996, 297046173⟩ CTN.nil) ⟨231238, 234517, 299863033⟩ CTN.nil) ⟨231238, 234533, 299781133⟩ (CTN.node CTN.nil ⟨231240, 237568, 285461333⟩ CTN.nil))) ⟨231248, 234032, 306205208⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231248, 234464, 303952480⟩ CTN.nil) ⟨231252, 235794, 298645390⟩ CTN.nil) ⟨231252, 235858, 298321055⟩ (CTN.node (CTN.node CTN.nil ⟨231252, 236626, 294463177⟩ CTN.nil) ⟨231252, 236722, 293985339⟩ CTN.nil)) ⟨231253, 233732, 309723995⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231264, 235684, 303733319⟩ CTN.nil) ⟨231264, 236096, 301616678⟩ CTN.nil) ⟨231264, 237568, 294203355⟩ (CTN.node CTN.nil ⟨231268, 234547, 311218714⟩ CTN.nil)))) ⟨231268, 234563, 311133724⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231268, 235106, 308266478⟩ CTN.nil) ⟨231268, 236674, 300170251⟩ CTN.nil) ⟨231269, 234132, 313823430⟩ (CTN.node (CTN.node CTN.nil ⟨231269, 234548, 311600733⟩ CTN.nil) ⟨231269, 234564, 311515639⟩ CTN.nil)) ⟨231269, 234996, 309229026⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231272, 237188, 299057041⟩ CTN.nil) ⟨231272, 237568, 297146371⟩ CTN.nil) ⟨231280, 237568, 300103886⟩ (CTN.node CTN.nil ⟨231284, 234616, 317071094⟩ CTN.nil))) ⟨231284, 235768, 310913330⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231284, 236274, 308255905⟩ CTN.nil) ⟨231284, 237568, 301588078⟩ CTN.nil) ⟨231285, 233780, 322031756⟩ (CTN.node CTN.nil ⟨231285, 234164, 319922488⟩ CTN.nil)) ⟨231285, 235572, 312334763⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231286, 234997, 315794365⟩ CTN.nil) ⟨231286, 237012, 305181223⟩ CTN.nil) ⟨231288, 235196, 315500770⟩ (CTN.node CTN.nil ⟨231288, 237568, 303075894⟩ CTN.nil))))))))

noncomputable def tab21 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231296, 234080, 324735418⟩ CTN.nil) ⟨231296, 234944, 319980213⟩ CTN.nil) ⟨231296, 235520, 316858382⟩ (CTN.node (CTN.node CTN.nil ⟨231296, 235552, 316686066⟩ CTN.nil) ⟨231296, 236096, 313774538⟩ CTN.nil)) ⟨231296, 237568, 306062392⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231300, 235170, 320311576⟩ CTN.nil) ⟨231300, 236002, 315814131⟩ CTN.nil) ⟨231300, 237568, 307561073⟩ (CTN.node CTN.nil ⟨231301, 234180, 326165395⟩ CTN.nil))) ⟨231304, 237568, 309063376⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231308, 237568, 310569299⟩ CTN.nil) ⟨231312, 237568, 312078842⟩ CTN.nil) ⟨231315, 235602, 323809970⟩ (CTN.node (CTN.node CTN.nil ⟨231316, 234227, 331889107⟩ CTN.nil) ⟨231316, 235043, 327299665⟩ CTN.nil)) ⟨231317, 234228, 332284388⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231317, 235028, 327778829⟩ CTN.nil) ⟨231317, 235060, 327600200⟩ CTN.nil) ⟨231317, 235636, 324405597⟩ (CTN.node CTN.nil ⟨231318, 236276, 321289032⟩ CTN.nil)))) ⟨231320, 237568, 315108785⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231324, 236320, 323377404⟩ CTN.nil) ⟨231328, 234576, 334715074⟩ CTN.nil) ⟨231328, 235008, 332258297⟩ (CTN.node (CTN.node CTN.nil ⟨231328, 235584, 329017556⟩ CTN.nil) ⟨231328, 236160, 325816239⟩ CTN.nil)) ⟨231328, 237568, 318153202⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231332, 235938, 328615779⟩ CTN.nil) ⟨231334, 234629, 336822427⟩ CTN.nil) ⟨231344, 234176, 343505846⟩ (CTN.node CTN.nil ⟨231348, 234211, 344932879⟩ CTN.nil))) ⟨231348, 234691, 342116863⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231348, 235107, 339699531⟩ CTN.nil) ⟨231348, 235218, 339058134⟩ CTN.nil) ⟨231348, 235250, 338873508⟩ (CTN.node (CTN.node CTN.nil ⟨231348, 236082, 334117045⟩ CTN.nil) ⟨231348, 236370, 332490045⟩ CTN.nil)) ⟨231348, 237568, 325827538⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231349, 234228, 345241261⟩ CTN.nil) ⟨231350, 234213, 345738753⟩ CTN.nil) ⟨231360, 234608, 347489006⟩ (CTN.node CTN.nil ⟨231360, 235616, 341574850⟩ CTN.nil))))) ⟨231360, 236766, 334980400⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231360, 237024, 333522869⟩ CTN.nil) ⟨231360, 237568, 330475519⟩ CTN.nil) ⟨231364, 234227, 351405096⟩ (CTN.node (CTN.node CTN.nil ⟨231364, 235202, 345608731⟩ CTN.nil) ⟨231364, 237090, 334720443⟩ CTN.nil)) ⟨231364, 237568, 332032073⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231366, 234245, 352121856⟩ CTN.nil) ⟨231366, 234645, 349724572⟩ CTN.nil) ⟨231368, 236326, 340667355⟩ (CTN.node CTN.nil ⟨231368, 237568, 333592239⟩ CTN.nil))) ⟨231370, 237104, 337001324⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231380, 236370, 345211838⟩ CTN.nil) ⟨231380, 236946, 341864074⟩ CTN.nil) ⟨231381, 235124, 353005023⟩ (CTN.node (CTN.node CTN.nil ⟨231381, 235668, 349753703⟩ CTN.nil) ⟨231382, 234293, 358460986⟩ CTN.nil)) ⟨231382, 234309, 358362987⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231382, 234709, 355923878⟩ CTN.nil) ⟨231382, 235109, 353505488⟩ CTN.nil) ⟨231382, 235141, 353312906⟩ (CTN.node CTN.nil ⟨231382, 236372, 346003060⟩ CTN.nil)))) ⟨231382, 237108, 341722821⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231388, 237568, 341447240⟩ CTN.nil) ⟨231392, 234176, 363360412⟩ CTN.nil) ⟨231392, 234608, 360688836⟩ (CTN.node (CTN.node CTN.nil ⟨231392, 235040, 358041774⟩ CTN.nil) ⟨231392, 235616, 354550023⟩ CTN.nil)) ⟨231392, 236192, 351100743⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231392, 236960, 346566701⟩ CTN.nil) ⟨231392, 237568, 343029069⟩ CTN.nil) ⟨231397, 234740, 361957152⟩ (CTN.node CTN.nil ⟨231398, 234677, 362763472⟩ CTN.nil))) ⟨231401, 234775, 363408192⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231408, 237568, 349392469⟩ CTN.nil) ⟨231412, 234691, 368539743⟩ CTN.nil) ⟨231412, 235139, 365736357⟩ (CTN.node CTN.nil ⟨231412, 235824, 361501276⟩ CTN.nil)) ⟨231412, 236370, 358169413⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231412, 237568, 350992336⟩ CTN.nil) ⟨231413, 234692, 368954003⟩ CTN.nil) ⟨231413, 235124, 366247250⟩ (CTN.node CTN.nil ⟨231413, 235700, 362676747⟩ CTN.nil)))))) ⟨231414, 233909, 374350502⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231416, 237568, 352595809⟩ CTN.nil) ⟨231417, 234791, 370013214⟩ CTN.nil) ⟨231428, 237568, 357427857⟩ (CTN.node (CTN.node CTN.nil ⟨231429, 233924, 380678296⟩ CTN.nil) ⟨231430, 234709, 376030426⟩ CTN.nil)) ⟨231432, 237158, 361537488⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231432, 237568, 359045747⟩ CTN.nil) ⟨231433, 234807, 376675057⟩ CTN.nil) ⟨231444, 236082, 373179692⟩ (CTN.node CTN.nil ⟨231444, 236946, 367761110⟩ CTN.nil))) ⟨231445, 234308, 385052765⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231445, 234324, 384947503⟩ CTN.nil) ⟨231445, 234740, 382223289⟩ CTN.nil) ⟨231446, 234309, 385477345⟩ (CTN.node (CTN.node CTN.nil ⟨231446, 235173, 379838154⟩ CTN.nil) ⟨231446, 237204, 366982884⟩ CTN.nil)) ⟨231448, 237568, 365553331⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231449, 235239, 380686168⟩ CTN.nil) ⟨231460, 234755, 388568644⟩ CTN.nil) ⟨231461, 234324, 391872835⟩ (CTN.node CTN.nil ⟨231461, 234740, 389099611⟩ CTN.nil)))) ⟨231461, 235764, 382377028⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231462, 234341, 392193750⟩ CTN.nil) ⟨231462, 234741, 389524743⟩ CTN.nil) ⟨231472, 237568, 375422711⟩ (CTN.node (CTN.node CTN.nil ⟨231476, 234803, 395176201⟩ CTN.nil) ⟨231476, 236434, 384373850⟩ CTN.nil)) ⟨231476, 236466, 384165627⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231476, 237202, 379415176⟩ CTN.nil) ⟨231476, 237298, 378800978⟩ CTN.nil) ⟨231476, 237568, 377080201⟩ (CTN.node CTN.nil ⟨231477, 233972, 401267080⟩ CTN.nil))) ⟨231477, 234804, 395604302⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231478, 236436, 385206953⟩ CTN.nil) ⟨231478, 236468, 384998280⟩ CTN.nil) ⟨231478, 237300, 379622049⟩ (CTN.node (CTN.node CTN.nil ⟨231478, 237568, 377910294⟩ CTN.nil) ⟨231480, 237568, 378741286⟩ CTN.nil)) ⟨231488, 235136, 398144251⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231488, 237056, 385389027⟩ CTN.nil) ⟨231488, 237568, 382074244⟩ CTN.nil) ⟨231492, 234355, 405249043⟩ (CTN.node CTN.nil ⟨231492, 237568, 383746115⟩ CTN.nil))))) ⟨231493, 233972, 408356588⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231493, 235220, 399750476⟩ CTN.nil) ⟨231493, 235252, 399532804⟩ CTN.nil) ⟨231493, 235828, 395639914⟩ (CTN.node (CTN.node CTN.nil ⟨231494, 236420, 392115134⟩ CTN.nil) ⟨231498, 236646, 392321505⟩ CTN.nil)) ⟨231507, 235218, 405885962⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231508, 234371, 412236501⟩ CTN.nil) ⟨231508, 234435, 411786083⟩ CTN.nil) ⟨231508, 236466, 397806547⟩ (CTN.node CTN.nil ⟨231509, 235204, 406861204⟩ CTN.nil))) ⟨231510, 234389, 413001028⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231510, 235221, 407182956⟩ CTN.nil) ⟨231510, 236468, 398653383⟩ CTN.nil) ⟨231514, 235304, 408365930⟩ (CTN.node (CTN.node CTN.nil ⟨231520, 236516, 402641293⟩ CTN.nil) ⟨231520, 237348, 397019823⟩ CTN.nil)) ⟨231523, 235826, 408692243⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231525, 234804, 416753411⟩ CTN.nil) ⟨231526, 234821, 417078861⟩ CTN.nil) ⟨231530, 236678, 405861680⟩ (CTN.node CTN.nil ⟨231530, 237568, 399808048⟩ CTN.nil)))) ⟨231536, 234752, 422050515⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231536, 236600, 409005665⟩ CTN.nil) ⟨231536, 237568, 402373756⟩ CTN.nil) ⟨231540, 234419, 426265235⟩ (CTN.node (CTN.node CTN.nil ⟨231540, 237568, 404088713⟩ CTN.nil) ⟨231541, 234404, 426827440⟩ CTN.nil)) ⟨231542, 234885, 423787992⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231542, 235285, 420910641⟩ CTN.nil) ⟨231542, 235348, 420459687⟩ CTN.nil) ⟨231542, 237300, 406781757⟩ (CTN.node CTN.nil ⟨231544, 236608, 412439916⟩ CTN.nil))) ⟨231544, 237568, 405807256⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231552, 237568, 409255098⟩ CTN.nil) ⟨231556, 234435, 433420896⟩ CTN.nil) ⟨231556, 237250, 413194434⟩ (CTN.node CTN.nil ⟨231556, 237568, 410984396⟩ CTN.nil)) ⟨231557, 234820, 431036143⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231557, 234836, 430918568⟩ CTN.nil) ⟨231557, 235316, 427409903⟩ CTN.nil) ⟨231557, 235860, 423476484⟩ (CTN.node CTN.nil ⟨231558, 237252, 414051108⟩ CTN.nil))))))) ⟨231562, 236710, 419620092⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231562, 237478, 414212990⟩ CTN.nil) ⟨231564, 237568, 414453742⟩ CTN.nil) ⟨231568, 237568, 416193789⟩ (CTN.node (CTN.node CTN.nil ⟨231571, 234898, 436828887⟩ CTN.nil) ⟨231572, 234899, 437277872⟩ CTN.nil)) ⟨231574, 235285, 435320164⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231574, 237300, 420707589⟩ CTN.nil) ⟨231576, 237568, 419684628⟩ CTN.nil) ⟨231578, 234536, 442754560⟩ (CTN.node CTN.nil ⟨231584, 234368, 446803668⟩ CTN.nil))) ⟨231584, 234800, 443521268⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231584, 235232, 440268960⟩ CTN.nil) ⟨231584, 235264, 440029236⟩ CTN.nil) ⟨231584, 235808, 435978791⟩ (CTN.node (CTN.node CTN.nil ⟨231584, 235840, 435741984⟩ CTN.nil) ⟨231584, 236384, 431740761⟩ CTN.nil)) ⟨231584, 236416, 431506828⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231584, 237248, 425479821⟩ CTN.nil) ⟨231588, 237568, 424947738⟩ CTN.nil) ⟨231589, 234452, 448480367⟩ (CTN.node CTN.nil ⟨231589, 234884, 445186827⟩ CTN.nil)))) ⟨231589, 235316, 441923470⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231589, 235892, 437618709⟩ CTN.nil) ⟨231590, 234885, 445639992⟩ CTN.nil) ⟨231590, 236548, 433227641⟩ (CTN.node (CTN.node CTN.nil ⟨231594, 237510, 428009600⟩ CTN.nil) ⟨231600, 234432, 453754174⟩ CTN.nil)) ⟨231602, 236560, 438531353⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231603, 234882, 451674186⟩ CTN.nil) ⟨231604, 236594, 439180365⟩ CTN.nil) ⟨231604, 237568, 432015314⟩ (CTN.node CTN.nil ⟨231605, 234468, 455810823⟩ CTN.nil))) ⟨231606, 234485, 456146200⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231606, 235317, 449722941⟩ CTN.nil) ⟨231606, 236180, 443179385⟩ CTN.nil) ⟨231606, 237012, 436983201⟩ (CTN.node (CTN.node CTN.nil ⟨231606, 237568, 432902785⟩ CTN.nil) ⟨231608, 237568, 433791149⟩ CTN.nil)) ⟨231616, 234448, 461127199⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231616, 235296, 454509013⟩ CTN.nil) ⟨231616, 235872, 450081282⟩ CTN.nil) ⟨231616, 236448, 445707348⟩ (CTN.node CTN.nil ⟨231616, 237280, 439482835⟩ CTN.nil))))) ⟨231616, 237568, 437353544⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231620, 237568, 439140102⟩ CTN.nil) ⟨231621, 234500, 463071001⟩ CTN.nil) ⟨231622, 234917, 460256518⟩ (CTN.node (CTN.node CTN.nil ⟨231624, 237568, 440930233⟩ CTN.nil) ⟨231637, 234116, 473738882⟩ CTN.nil)) ⟨231637, 234516, 470511843⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231637, 234548, 470254869⟩ CTN.nil) ⟨231637, 234932, 467184822⟩ CTN.nil) ⟨231637, 234964, 466930118⟩ (CTN.node CTN.nil ⟨231637, 235956, 459119677⟩ CTN.nil))) ⟨231638, 236628, 454379608⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231638, 236660, 454133663⟩ CTN.nil) ⟨231638, 237492, 447797115⟩ CTN.nil) ⟨231638, 237568, 447223821⟩ (CTN.node (CTN.node CTN.nil ⟨231644, 236640, 457040813⟩ CTN.nil) ⟨231644, 237472, 450663165⟩ CTN.nil)) ⟨231648, 237312, 453700345⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231650, 235456, 469130155⟩ CTN.nil) ⟨231652, 237568, 453561140⟩ CTN.nil) ⟨231653, 234164, 481023677⟩ (CTN.node CTN.nil ⟨231653, 234996, 474240882⟩ CTN.nil)))) ⟨231654, 237380, 455912868⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231654, 237568, 454470040⟩ CTN.nil) ⟨231666, 236656, 467080117⟩ CTN.nil) ⟨231666, 237392, 461308985⟩ (CTN.node (CTN.node CTN.nil ⟨231666, 237568, 459942162⟩ CTN.nil) ⟨231668, 235011, 481264482⟩ CTN.nil)) ⟨231668, 237426, 461961878⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231668, 237568, 460857302⟩ CTN.nil) ⟨231669, 234164, 488757646⟩ CTN.nil) ⟨231669, 234948, 482260087⟩ (CTN.node CTN.nil ⟨231670, 235397, 479062800⟩ CTN.nil))) ⟨231670, 236660, 468907973⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231672, 235004, 483236229⟩ CTN.nil) ⟨231672, 235580, 478522819⟩ CTN.nil) ⟨231672, 237568, 462690256⟩ (CTN.node CTN.nil ⟨231676, 236160, 475715364⟩ CTN.nil)) ⟨231680, 234464, 491583274⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231680, 235328, 484396566⟩ CTN.nil) ⟨231680, 235904, 479678316⟩ CTN.nil) ⟨231680, 236480, 475017385⟩ (CTN.node CTN.nil ⟨231680, 237248, 468890534⟩ CTN.nil)))))) ⟨231680, 237568, 466366854⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231682, 237568, 467288231⟩ CTN.nil) ⟨231684, 237568, 468210498⟩ CTN.nil) ⟨231685, 234548, 493305008⟩ (CTN.node (CTN.node CTN.nil ⟨231696, 237568, 473762796⟩ CTN.nil) ⟨231698, 235409, 492363924⟩ CTN.nil)) ⟨231698, 236656, 482058145⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231700, 234579, 500354105⟩ CTN.nil) ⟨231700, 234979, 496952478⟩ CTN.nil) ⟨231700, 236690, 482724218⟩ (CTN.node CTN.nil ⟨231701, 234564, 500971567⟩ CTN.nil))) ⟨231701, 234996, 497294294⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231702, 235461, 493855896⟩ CTN.nil) ⟨231702, 237568, 476550961⟩ CTN.nil) ⟨231714, 236288, 492694316⟩ (CTN.node (CTN.node CTN.nil ⟨231715, 235442, 500306370⟩ CTN.nil) ⟨231716, 237568, 483087810⟩ CTN.nil)) ⟨231717, 234596, 508554911⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231720, 237568, 484963484⟩ CTN.nil) ⟨231728, 234512, 514728792⟩ CTN.nil) ⟨231730, 237568, 489668220⟩ (CTN.node CTN.nil ⟨231732, 234643, 515561402⟩ CTN.nil)))) ⟨231732, 235059, 511917802⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231732, 235475, 508306338⟩ CTN.nil) ⟨231733, 235028, 512681111⟩ CTN.nil) ⟨231734, 235461, 509406157⟩ (CTN.node (CTN.node CTN.nil ⟨231734, 237492, 492186457⟩ CTN.nil) ⟨231740, 237568, 494395165⟩ CTN.nil)) ⟨231744, 237568, 496292159⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231746, 236320, 507839552⟩ CTN.nil) ⟨231746, 237568, 497241987⟩ CTN.nil) ⟨231748, 237568, 498192703⟩ (CTN.node CTN.nil ⟨231752, 237568, 500096798⟩ CTN.nil))) ⟨231760, 235008, 526256373⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231762, 237136, 508565189⟩ CTN.nil) ⟨231762, 237568, 504872560⟩ CTN.nil) ⟨231764, 235107, 527365926⟩ (CTN.node CTN.nil ⟨231764, 235475, 524073754⟩ CTN.nil)) ⟨231765, 234644, 532048398⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231766, 235493, 524906357⟩ CTN.nil) ⟨231766, 236724, 514062392⟩ CTN.nil) ⟨231766, 237568, 506789074⟩ (CTN.node CTN.nil ⟨231776, 237344, 513531811⟩ CTN.nil))))) ⟨231776, 237568, 511595872⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231779, 235122, 534748210⟩ CTN.nil) ⟨231780, 234643, 539639581⟩ CTN.nil) ⟨231781, 235076, 536174285⟩ (CTN.node (CTN.node CTN.nil ⟨231782, 237568, 514490586⟩ CTN.nil) ⟨231792, 235040, 542061483⟩ CTN.nil)) ⟨231792, 237568, 519332826⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231795, 235506, 539288403⟩ CTN.nil) ⟨231795, 236082, 534039435⟩ CTN.nil) ⟨231796, 234659, 547635348⟩ (CTN.node CTN.nil ⟨231796, 235075, 543765336⟩ CTN.nil))) ⟨231796, 237522, 521680241⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231796, 237568, 521275920⟩ CTN.nil) ⟨231798, 236756, 529457366⟩ CTN.nil) ⟨231798, 236788, 529170938⟩ (CTN.node (CTN.node CTN.nil ⟨231798, 237568, 522248795⟩ CTN.nil) ⟨231800, 237568, 523222555⟩ CTN.nil)) ⟨231804, 237568, 525172730⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231811, 235106, 551108145⟩ CTN.nil) ⟨231811, 235538, 547072157⟩ CTN.nil) ⟨231812, 235491, 548016629⟩ (CTN.node CTN.nil ⟨231813, 234308, 559697123⟩ CTN.nil)))) ⟨231813, 235156, 551659478⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231813, 236148, 542439221⟩ CTN.nil) ⟨231814, 235093, 552762705⟩ CTN.nil) ⟨231814, 236740, 537525519⟩ (CTN.node (CTN.node CTN.nil ⟨231814, 237568, 530063650⟩ CTN.nil) ⟨231817, 235191, 553373115⟩ CTN.nil)) ⟨231820, 237568, 533008814⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231824, 234608, 562518260⟩ CTN.nil) ⟨231824, 235040, 558389990⟩ CTN.nil) ⟨231824, 237568, 534976677⟩ (CTN.node CTN.nil ⟨231826, 236816, 542808797⟩ CTN.nil))) ⟨231827, 235570, 554905879⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231827, 236146, 549506364⟩ CTN.nil) ⟨231830, 237568, 537935101⟩ CTN.nil) ⟨231832, 237568, 538923009⟩ (CTN.node CTN.nil ⟨231833, 235207, 561426062⟩ CTN.nil)) ⟨231840, 237568, 542883475⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231844, 235123, 567911852⟩ CTN.nil) ⟨231844, 237568, 544869006⟩ CTN.nil) ⟨231845, 235124, 568420122⟩ (CTN.node CTN.nil ⟨231845, 236148, 558615265⟩ CTN.nil))))))))

noncomputable def tab22 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231852, 237568, 548850663⟩ CTN.nil) ⟨231856, 236920, 556903926⟩ CTN.nil) ⟨231856, 237568, 550846785⟩ (CTN.node (CTN.node CTN.nil ⟨231859, 236146, 565784284⟩ CTN.nil) ⟨231860, 237568, 552846437⟩ CTN.nil)) ⟨231861, 234740, 580525311⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231862, 237568, 553847586⟩ CTN.nil) ⟨231864, 236928, 560874940⟩ CTN.nil) ⟨231872, 235088, 582848679⟩ (CTN.node CTN.nil ⟨231872, 235520, 578579917⟩ CTN.nil))) ⟨231872, 236096, 572948851⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231872, 236128, 572638028⟩ CTN.nil) ⟨231872, 236672, 567386139⟩ CTN.nil) ⟨231872, 236936, 564859133⟩ (CTN.node (CTN.node CTN.nil ⟨231872, 237568, 558866557⟩ CTN.nil) ⟨231874, 237312, 562295099⟩ CTN.nil)) ⟨231876, 237568, 560880316⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231877, 234740, 588957485⟩ CTN.nil) ⟨231877, 235172, 584637604⟩ CTN.nil) ⟨231878, 237568, 561888518⟩ (CTN.node CTN.nil ⟨231880, 237568, 562897600⟩ CTN.nil)))) ⟨231884, 237568, 564918408⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231888, 237568, 566942738⟩ CTN.nil) ⟨231890, 237568, 567956224⟩ CTN.nil) ⟨231891, 235602, 587695477⟩ (CTN.node (CTN.node CTN.nil ⟨231891, 236178, 581977676⟩ CTN.nil) ⟨231892, 235187, 592386822⟩ CTN.nil)) ⟨231892, 235219, 592064209⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231892, 235619, 588050024⟩ CTN.nil) ⟨231892, 237568, 568970591⟩ CTN.nil) ⟨231893, 234388, 601049439⟩ (CTN.node CTN.nil ⟨231893, 234804, 596797063⟩ CTN.nil))) ⟨231893, 235604, 588724606⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231893, 235636, 588404556⟩ CTN.nil) ⟨231894, 237568, 569985838⟩ CTN.nil) ⟨231904, 235584, 594713052⟩ (CTN.node (CTN.node CTN.nil ⟨231904, 236160, 588926536⟩ CTN.nil) ⟨231904, 236736, 583210240⟩ CTN.nil)) ⟨231904, 237568, 575075275⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231906, 237568, 576095802⟩ CTN.nil) ⟨231907, 235586, 596276188⟩ CTN.nil) ⟨231912, 237568, 579162660⟩ (CTN.node CTN.nil ⟨231920, 237568, 583264114⟩ CTN.nil))))) ⟨231922, 236912, 590796448⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231922, 237568, 584291676⟩ CTN.nil) ⟨231924, 234787, 613576896⟩ CTN.nil) ⟨231924, 234851, 612907678⟩ (CTN.node (CTN.node CTN.nil ⟨231924, 235267, 608579934⟩ CTN.nil) ⟨231924, 235683, 604290328⟩ CTN.nil)) ⟨231924, 237568, 585320115⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231926, 236916, 592837038⟩ CTN.nil) ⟨231928, 237568, 587379631⟩ CTN.nil) ⟨231932, 237568, 589442660⟩ (CTN.node CTN.nil ⟨231936, 235616, 611375596⟩ CTN.nil))) ⟨231936, 236768, 599552091⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231936, 237568, 591509203⟩ CTN.nil) ⟨231940, 234803, 622065003⟩ CTN.nil) ⟨231940, 237568, 593579258⟩ (CTN.node (CTN.node CTN.nil ⟨231954, 237568, 600852094⟩ CTN.nil) ⟨231956, 236914, 608574751⟩ CTN.nil)) ⟨231956, 237568, 601894580⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231958, 236948, 609279524⟩ CTN.nil) ⟨231958, 236980, 608950181⟩ CTN.nil) ⟨231958, 237568, 602937943⟩ (CTN.node CTN.nil ⟨231960, 237568, 603982183⟩ CTN.nil)))) ⟨231964, 237568, 606073292⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231968, 235616, 628593799⟩ CTN.nil) ⟨231968, 236768, 616437308⟩ CTN.nil) ⟨231968, 237536, 608496011⟩ (CTN.node (CTN.node CTN.nil ⟨231968, 237568, 608167908⟩ CTN.nil) ⟨231972, 234851, 639029353⟩ CTN.nil)) ⟨231974, 237568, 611316403⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨231976, 237568, 612367653⟩ CTN.nil) ⟨231986, 237568, 617637042⟩ CTN.nil) ⟨231987, 235314, 642216372⟩ (CTN.node CTN.nil ⟨231988, 235283, 643104444⟩ CTN.nil))) ⟨231988, 235699, 638571798⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨231988, 235715, 638398264⟩ CTN.nil) ⟨231988, 236946, 625221970⟩ CTN.nil) ⟨231988, 236978, 624884007⟩ (CTN.node CTN.nil ⟨231988, 237568, 618693546⟩ CTN.nil)) ⟨231990, 237568, 619750925⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232003, 235730, 646438462⟩ CTN.nil) ⟨232003, 236306, 640152541⟩ CTN.nil) ⟨232004, 236930, 633966405⟩ (CTN.node CTN.nil ⟨232004, 237568, 627177077⟩ CTN.nil)))))) ⟨232008, 237568, 629306705⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232016, 234800, 664015620⟩ CTN.nil) ⟨232016, 235232, 659146445⟩ CTN.nil) ⟨232020, 237568, 635716564⟩ (CTN.node (CTN.node CTN.nil ⟨232021, 234884, 665865548⟩ CTN.nil) ⟨232021, 235316, 660984548⟩ CTN.nil)) ⟨232022, 237568, 636787932⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232032, 234864, 672275319⟩ CTN.nil) ⟨232032, 237568, 642157867⟩ CTN.nil) ⟨232035, 235314, 668820627⟩ (CTN.node CTN.nil ⟨232035, 235794, 663385921⟩ CTN.nil))) ⟨232035, 236370, 656936948⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232037, 235316, 669917683⟩ CTN.nil) ⟨232040, 237568, 646469525⟩ CTN.nil) ⟨232048, 235296, 676322990⟩ (CTN.node (CTN.node CTN.nil ⟨232048, 237568, 650795140⟩ CTN.nil) ⟨232052, 235795, 672844552⟩ CTN.nil)) ⟨232052, 237568, 652963179⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232053, 234932, 683362865⟩ CTN.nil) ⟨232053, 235380, 678170018⟩ CTN.nil) ⟨232054, 237568, 654048505⟩ (CTN.node CTN.nil ⟨232064, 237568, 659488210⟩ CTN.nil)))) ⟨232066, 237568, 660578764⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232068, 237568, 661670189⟩ CTN.nil) ⟨232069, 235796, 682367750⟩ CTN.nil) ⟨232069, 235828, 681997096⟩ (CTN.node (CTN.node CTN.nil ⟨232072, 237568, 663855651⟩ CTN.nil) ⟨232080, 237568, 668237019⟩ CTN.nil)) ⟨232083, 236370, 683581373⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232084, 235363, 695937294⟩ CTN.nil) ⟨232084, 235427, 695180107⟩ CTN.nil) ⟨232084, 237568, 670432923⟩ (CTN.node CTN.nil ⟨232085, 235780, 691588601⟩ CTN.nil))) ⟨232086, 237044, 677495533⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232088, 235878, 692136564⟩ CTN.nil) ⟨232099, 236402, 692201257⟩ CTN.nil) ⟨232101, 235380, 705461151⟩ (CTN.node (CTN.node CTN.nil ⟨232104, 235478, 706006438⟩ CTN.nil) ⟨232104, 237568, 681464612⟩ CTN.nil)) ⟨232116, 234995, 718792059⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232116, 237568, 688125324⟩ CTN.nil) ⟨232117, 234980, 719557212⟩ CTN.nil) ⟨232120, 235910, 709984863⟩ (CTN.node CTN.nil ⟨232124, 237568, 692583158⟩ CTN.nil))))) ⟨232128, 236960, 701982875⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232128, 237568, 694817280⟩ CTN.nil) ⟨232132, 235411, 722981442⟩ CTN.nil) ⟨232132, 235427, 722784729⟩ (CTN.node (CTN.node CTN.nil ⟨232132, 235970, 716148274⟩ CTN.nil) ⟨232132, 236834, 705744876⟩ CTN.nil)) ⟨232132, 237568, 697054870⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232133, 235412, 723549902⟩ CTN.nil) ⟨232136, 237568, 699295928⟩ CTN.nil) ⟨232147, 236466, 718732784⟩ (CTN.node CTN.nil ⟨232148, 235059, 736701336⟩ CTN.nil))) ⟨232148, 235475, 731504076⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232148, 237138, 711179846⟩ CTN.nil) ⟨232148, 237568, 706039898⟩ CTN.nil) ⟨232150, 237568, 707166924⟩ (CTN.node (CTN.node CTN.nil ⟨232160, 234944, 745229452⟩ CTN.nil) ⟨232160, 235808, 734356660⟩ CTN.nil)) ⟨232160, 235840, 733957785⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232160, 236384, 727218181⟩ CTN.nil) ⟨232160, 236416, 726824148⟩ CTN.nil) ⟨232160, 236960, 720166247⟩ (CTN.node CTN.nil ⟨232160, 236992, 719776985⟩ CTN.nil)))) ⟨232160, 237568, 712815042⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232168, 237568, 717349110⟩ CTN.nil) ⟨232176, 237568, 721897015⟩ CTN.nil) ⟨232179, 236466, 737202774⟩ (CTN.node (CTN.node CTN.nil ⟨232180, 237170, 729054149⟩ CTN.nil) ⟨232180, 237202, 728660433⟩ CTN.nil)) ⟨232180, 237568, 724176153⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232181, 235892, 745584685⟩ CTN.nil) ⟨232192, 235872, 752308651⟩ CTN.nil) ⟨232192, 236448, 744997641⟩ (CTN.node CTN.nil ⟨232192, 237568, 731034299⟩ CTN.nil))) ⟨232195, 235538, 758368623⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232196, 236802, 742871262⟩ CTN.nil) ⟨232196, 237154, 738466339⟩ CTN.nil) ⟨232196, 237568, 733327255⟩ (CTN.node CTN.nil ⟨232208, 237568, 740226831⟩ CTN.nil)) ⟨232210, 237568, 741379779⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232212, 235075, 774568728⟩ CTN.nil) ⟨232212, 237568, 742533589⟩ CTN.nil) ⟨232213, 235508, 769480141⟩ (CTN.node CTN.nil ⟨232213, 235956, 763647153⟩ CTN.nil))))))) ⟨232224, 237568, 749474547⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232228, 235507, 778485812⟩ CTN.nil) ⟨232228, 237568, 751795091⟩ CTN.nil) ⟨232229, 235572, 778226738⟩ (CTN.node (CTN.node CTN.nil ⟨232232, 237568, 754119079⟩ CTN.nil) ⟨232240, 237568, 758777383⟩ CTN.nil)) ⟨232243, 235538, 787113628⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232244, 236003, 781522018⟩ CTN.nil) ⟨232244, 237202, 765824691⟩ CTN.nil) ⟨232244, 237568, 761111697⟩ (CTN.node CTN.nil ⟨232245, 235956, 782745757⟩ CTN.nil))) ⟨232246, 237236, 766560345⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232248, 237568, 763449450⟩ CTN.nil) ⟨232256, 237568, 768135274⟩ CTN.nil) ⟨232264, 237568, 772834844⟩ (CTN.node (CTN.node CTN.nil ⟨232274, 235985, 799855604⟩ CTN.nil) ⟨232276, 236003, 800824383⟩ CTN.nil)) ⟨232276, 237234, 784315625⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232276, 237568, 779909958⟩ CTN.nil) ⟨232277, 235988, 801635201⟩ CTN.nil) ⟨232296, 237568, 791770435⟩ (CTN.node CTN.nil ⟨232304, 235520, 824635579⟩ CTN.nil)))) ⟨232304, 237568, 796538618⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232306, 237568, 797732805⟩ CTN.nil) ⟨232308, 237298, 802573696⟩ CTN.nil) ⟨232308, 237568, 798927847⟩ (CTN.node (CTN.node CTN.nil ⟨232309, 235604, 826547049⟩ CTN.nil) ⟨232310, 237568, 800123745⟩ CTN.nil)) ⟨232312, 237568, 801320499⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232320, 237568, 806116070⟩ CTN.nil) ⟨232324, 235619, 835631254⟩ CTN.nil) ⟨232324, 237568, 808518985⟩ (CTN.node CTN.nil ⟨232330, 237478, 813362791⟩ CTN.nil))) ⟨232340, 235683, 844681534⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232340, 237568, 818164829⟩ CTN.nil) ⟨232352, 237568, 825435072⟩ CTN.nil) ⟨232355, 236690, 839612765⟩ (CTN.node (CTN.node CTN.nil ⟨232356, 235219, 861467057⟩ CTN.nil) ⟨232357, 236084, 849522108⟩ CTN.nil)) ⟨232368, 237568, 835176486⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232369, 236656, 848757921⟩ CTN.nil) ⟨232370, 237568, 836397997⟩ CTN.nil) ⟨232371, 236082, 858303752⟩ (CTN.node CTN.nil ⟨232372, 237330, 840988614⟩ CTN.nil))))) ⟨232372, 237568, 837620360⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232384, 237568, 844972417⟩ CTN.nil) ⟨232387, 236690, 859462653⟩ CTN.nil) ⟨232388, 237568, 847429909⟩ (CTN.node (CTN.node CTN.nil ⟨232389, 236148, 868647532⟩ CTN.nil) ⟨232392, 237568, 849890804⟩ CTN.nil)) ⟨232394, 237568, 851122527⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232403, 236146, 877517954⟩ CTN.nil) ⟨232416, 237248, 869406901⟩ CTN.nil) ⟨232420, 235715, 894831994⟩ (CTN.node CTN.nil ⟨232426, 237568, 870945602⟩ CTN.nil))) ⟨232428, 237568, 872191756⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232432, 237568, 874686609⟩ CTN.nil) ⟨232440, 237568, 879686482⟩ CTN.nil) ⟨232448, 236096, 906992532⟩ (CTN.node (CTN.node CTN.nil ⟨232448, 236672, 898186617⟩ CTN.nil) ⟨232448, 237248, 889487334⟩ CTN.nil)) ⟨232448, 237280, 889007136⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232448, 237568, 884699904⟩ CTN.nil) ⟨232453, 236180, 908916447⟩ CTN.nil) ⟨232456, 237568, 889726867⟩ (CTN.node CTN.nil ⟨232466, 237424, 898207484⟩ CTN.nil)))) ⟨232467, 236178, 917977832⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232468, 237458, 898958091⟩ CTN.nil) ⟨232468, 237568, 897292681⟩ CTN.nil) ⟨232480, 237568, 904888911⟩ (CTN.node (CTN.node CTN.nil ⟨232483, 236162, 928602235⟩ CTN.nil) ⟨232496, 237568, 915064477⟩ CTN.nil)) ⟨232498, 237488, 917576744⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232498, 237568, 916340217⟩ CTN.nil) ⟨232500, 237522, 918328539⟩ CTN.nil) ⟨232500, 237568, 917616800⟩ (CTN.node CTN.nil ⟨232508, 237568, 922731556⟩ CTN.nil))) ⟨232512, 237568, 925293987⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232516, 235795, 956111189⟩ CTN.nil) ⟨232520, 235894, 957148530⟩ CTN.nil) ⟨232520, 237568, 930428948⟩ (CTN.node CTN.nil ⟨232528, 237568, 935577368⟩ CTN.nil)) ⟨232530, 237568, 936866574⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232532, 237568, 938156621⟩ CTN.nil) ⟨232544, 237568, 945914544⟩ CTN.nil) ⟨232556, 237568, 953702683⟩ (CTN.node CTN.nil ⟨232560, 237568, 956305440⟩ CTN.nil)))))) ⟨232562, 237568, 957608075⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232564, 237554, 959137837⟩ CTN.nil) ⟨232564, 237568, 958911549⟩ CTN.nil) ⟨232568, 237568, 961521010⟩ (CTN.node (CTN.node CTN.nil ⟨232576, 237568, 966749982⟩ CTN.nil) ⟨232578, 237152, 974876298⟩ CTN.nil)) ⟨232578, 237568, 968059317⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232579, 236306, 989594916⟩ CTN.nil) ⟨232588, 237568, 974618547⟩ CTN.nil) ⟨232594, 237568, 978564119⟩ (CTN.node CTN.nil ⟨232608, 237568, 987799695⟩ CTN.nil))) ⟨232610, 237568, 989122403⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232611, 236370, 1010023133⟩ CTN.nil) ⟨232624, 237568, 998404714⟩ CTN.nil) ⟨232628, 237568, 1001064305⟩ (CTN.node (CTN.node CTN.nil ⟨232640, 237568, 1009063069⟩ CTN.nil) ⟨232648, 237568, 1014412224⟩ CTN.nil)) ⟨232660, 237568, 1022460901⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232672, 237568, 1030539480⟩ CTN.nil) ⟨232674, 237568, 1031888815⟩ CTN.nil) ⟨232684, 237568, 1038647928⟩ (CTN.node CTN.nil ⟨232688, 237568, 1041357376⟩ CTN.nil)))) ⟨232690, 237568, 1042713343⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232696, 237568, 1046786213⟩ CTN.nil) ⟨232702, 237568, 1050866533⟩ CTN.nil) ⟨232704, 237568, 1052228295⟩ (CTN.node (CTN.node CTN.nil ⟨232708, 237568, 1054954299⟩ CTN.nil) ⟨232722, 237568, 1064521355⟩ CTN.nil)) ⟨232736, 237536, 1074708361⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232736, 237568, 1074128874⟩ CTN.nil) ⟨232738, 237568, 1075504677⟩ CTN.nil) ⟨232744, 237568, 1079637032⟩ (CTN.node CTN.nil ⟨232748, 237568, 1082396055⟩ CTN.nil))) ⟨232754, 237568, 1086540768⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232756, 237568, 1087923985⟩ CTN.nil) ⟨232764, 237568, 1093465085⟩ CTN.nil) ⟨232768, 237568, 1096240570⟩ (CTN.node CTN.nil ⟨232772, 237568, 1099019343⟩ CTN.nil)) ⟨232775, 236565, 1119917129⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232780, 237568, 1104586750⟩ CTN.nil) ⟨232786, 237568, 1108770927⟩ CTN.nil) ⟨232791, 237252, 1118206755⟩ (CTN.node CTN.nil ⟨232806, 237568, 1122771503⟩ CTN.nil))))) ⟨232812, 237568, 1126987653⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232816, 237568, 1129802514⟩ CTN.nil) ⟨232818, 237568, 1131211171⟩ CTN.nil) ⟨232820, 237568, 1132620647⟩ (CTN.node (CTN.node CTN.nil ⟨232824, 237568, 1135442051⟩ CTN.nil) ⟨232832, 237568, 1141094669⟩ CTN.nil)) ⟨232850, 237568, 1153860831⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232852, 237568, 1155283372⟩ CTN.nil) ⟨232872, 237568, 1169553596⟩ CTN.nil) ⟨232876, 237568, 1172417409⟩ (CTN.node CTN.nil ⟨232880, 237568, 1175284474⟩ CTN.nil))) ⟨232884, 237568, 1178154791⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232896, 237568, 1186785237⟩ CTN.nil) ⟨232900, 237568, 1189668547⟩ CTN.nil) ⟨232904, 237568, 1192555101⟩ (CTN.node (CTN.node CTN.nil ⟨232916, 237568, 1201234217⟩ CTN.nil) ⟨232932, 237568, 1212851715⟩ CTN.nil)) ⟨232936, 237568, 1215764178⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232944, 237568, 1221598797⟩ CTN.nil) ⟨232948, 237568, 1224520953⟩ CTN.nil) ⟨232952, 237568, 1227446336⟩ (CTN.node CTN.nil ⟨232960, 237568, 1233306783⟩ CTN.nil)))) ⟨232964, 237568, 1236241843⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨232976, 237568, 1245066354⟩ CTN.nil) ⟨232992, 237568, 1256877421⟩ CTN.nil) ⟨232996, 237568, 1259838223⟩ (CTN.node (CTN.node CTN.nil ⟨233004, 237568, 1265769462⟩ CTN.nil) ⟨233008, 237568, 1268739895⟩ CTN.nil)) ⟨233012, 237568, 1271713535⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233024, 237568, 1280653685⟩ CTN.nil) ⟨233028, 237568, 1283640140⟩ CTN.nil) ⟨233040, 237568, 1292618700⟩ (CTN.node CTN.nil ⟨233052, 237568, 1301626024⟩ CTN.nil))) ⟨233060, 237568, 1307646867⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233072, 237568, 1316702044⟩ CTN.nil) ⟨233074, 237568, 1318214028⟩ CTN.nil) ⟨233076, 237568, 1319726806⟩ (CTN.node CTN.nil ⟨233088, 237568, 1328820187⟩ CTN.nil)) ⟨233104, 237568, 1340989189⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233108, 237568, 1344039375⟩ CTN.nil) ⟨233120, 237568, 1353208956⟩ CTN.nil) ⟨233124, 237568, 1356271818⟩ (CTN.node CTN.nil ⟨233132, 237568, 1362407039⟩ CTN.nil))))))))

noncomputable def tab23 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233140, 237568, 1368554909⟩ CTN.nil) ⟨233152, 237568, 1377800408⟩ CTN.nil) ⟨233156, 237568, 1380888553⟩ (CTN.node (CTN.node CTN.nil ⟨233164, 237568, 1387074302⟩ CTN.nil) ⟨233188, 237568, 1405707120⟩ CTN.nil)) ⟨233192, 237568, 1408823594⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233200, 237568, 1415065961⟩ CTN.nil) ⟨233204, 237568, 1418191851⟩ CTN.nil) ⟨233216, 237568, 1427588329⟩ (CTN.node CTN.nil ⟨233220, 237568, 1430726753⟩ CTN.nil))) ⟨233232, 237568, 1440160796⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233236, 237568, 1443311730⟩ CTN.nil) ⟨233252, 237568, 1455946682⟩ CTN.nil) ⟨233264, 237568, 1465455635⟩ (CTN.node (CTN.node CTN.nil ⟨233288, 237568, 1484557544⟩ CTN.nil) ⟨233316, 237568, 1506984292⟩ CTN.nil)) ⟨233328, 237568, 1516642175⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233332, 237568, 1519867648⟩ CTN.nil) ⟨233344, 237568, 1529562576⟩ CTN.nil) ⟨233348, 237568, 1532800385⟩ (CTN.node CTN.nil ⟨233360, 237568, 1542532284⟩ CTN.nil)))) ⟨233362, 237568, 1544156960⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233380, 237568, 1558813602⟩ CTN.nil) ⟨233394, 237568, 1570256162⟩ CTN.nil) ⟨233396, 237568, 1571893877⟩ (CTN.node (CTN.node CTN.nil ⟨233400, 237568, 1575171602⟩ CTN.nil) ⟨233408, 237568, 1581736229⟩ CTN.nil)) ⟨233410, 237568, 1583379297⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233412, 237568, 1585023128⟩ CTN.nil) ⟨233426, 237568, 1596551316⟩ CTN.nil) ⟨233428, 237568, 1598201251⟩ (CTN.node CTN.nil ⟨233440, 237568, 1608116853⟩ CTN.nil))) ⟨233446, 237568, 1613084928⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233448, 237568, 1614742474⟩ CTN.nil) ⟨233456, 237568, 1621380254⟩ CTN.nil) ⟨233460, 237568, 1624703700⟩ (CTN.node (CTN.node CTN.nil ⟨233472, 237568, 1634692240⟩ CTN.nil) ⟨233478, 237568, 1639696741⟩ CTN.nil)) ⟨233488, 237568, 1648052710⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233518, 237568, 1673233899⟩ CTN.nil) ⟨233520, 237568, 1674918675⟩ CTN.nil) ⟨233522, 237568, 1676604204⟩ (CTN.node CTN.nil ⟨233524, 237568, 1678290485⟩ CTN.nil))))) ⟨233570, 237568, 1717282122⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233576, 237568, 1722397189⟩ CTN.nil) ⟨233584, 237568, 1729227732⟩ CTN.nil) ⟨233588, 237568, 1732647479⟩ (CTN.node (CTN.node CTN.nil ⟨233596, 237568, 1739495918⟩ CTN.nil) ⟨233600, 237568, 1742924605⟩ CTN.nil)) ⟨233604, 237568, 1746356269⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233608, 237568, 1749790908⟩ CTN.nil) ⟨233632, 237568, 1770461124⟩ CTN.nil) ⟨233640, 237568, 1777374918⟩ (CTN.node CTN.nil ⟨233650, 237568, 1786033808⟩ CTN.nil))) ⟨233652, 237568, 1787767803⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233664, 237568, 1798187277⟩ CTN.nil) ⟨233668, 237568, 1801666336⟩ CTN.nil) ⟨233704, 237568, 1833110298⟩ (CTN.node (CTN.node CTN.nil ⟨233712, 237568, 1840130140⟩ CTN.nil) ⟨233714, 237568, 1841886932⟩ CTN.nil)) ⟨233716, 237568, 1843644455⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233730, 237568, 1855967592⟩ CTN.nil) ⟨233732, 237568, 1857730962⟩ CTN.nil) ⟨233768, 237568, 1889596225⟩ (CTN.node CTN.nil ⟨233776, 237568, 1896709381⟩ CTN.nil)))) ⟨233780, 237568, 1900270310⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233792, 237568, 1910970479⟩ CTN.nil) ⟨233832, 237568, 1946825478⟩ CTN.nil) ⟨233836, 237568, 1950426820⟩ (CTN.node (CTN.node CTN.nil ⟨233840, 237568, 1954031035⟩ CTN.nil) ⟨233844, 237568, 1957638122⟩ CTN.nil)) ⟨233852, 237568, 1964860901⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233860, 237568, 1972095145⟩ CTN.nil) ⟨233872, 237568, 1982967971⟩ CTN.nil) ⟨233896, 237568, 2004790710⟩ (CTN.node CTN.nil ⟨233908, 237568, 2015740523⟩ CTN.nil))) ⟨233916, 237568, 2023054602⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨233920, 237568, 2026715898⟩ CTN.nil) ⟨233938, 237568, 2043226781⟩ CTN.nil) ⟨233960, 237568, 2063484459⟩ (CTN.node CTN.nil ⟨233964, 237568, 2067176835⟩ CTN.nil)) ⟨233972, 237568, 2074570028⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨233988, 237568, 2089390126⟩ CTN.nil) ⟨233996, 237568, 2096817001⟩ CTN.nil) ⟨234012, 237568, 2111704326⟩ (CTN.node CTN.nil ⟨234016, 237568, 2115433142⟩ CTN.nil)))))) ⟨234024, 237568, 2122899141⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨234032, 237568, 2130376285⟩ CTN.nil) ⟨234044, 237568, 2141612863⟩ CTN.nil) ⟨234048, 237568, 2145363945⟩ (CTN.node (CTN.node CTN.nil ⟨234052, 237568, 2149117802⟩ CTN.nil) ⟨234072, 237568, 2167928638⟩ CTN.nil)) ⟨234100, 237568, 2194379812⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨234156, 237568, 2247685712⟩ CTN.nil) ⟨234164, 237568, 2255344528⟩ CTN.nil) ⟨234172, 237568, 2263014218⟩ (CTN.node CTN.nil ⟨234176, 237568, 2266853137⟩ CTN.nil))) ⟨234228, 237568, 2317005228⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨234252, 237568, 2340305780⟩ CTN.nil) ⟨234272, 237568, 2359796494⟩ CTN.nil) ⟨234284, 237568, 2371522922⟩ (CTN.node (CTN.node CTN.nil ⟨234292, 237568, 2379353841⟩ CTN.nil) ⟨234300, 237568, 2387195380⟩ CTN.nil)) ⟨234308, 237568, 2395047524⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨234336, 237568, 2422613309⟩ CTN.nil) ⟨234352, 237568, 2438423157⟩ CTN.nil) ⟨234356, 237568, 2442382187⟩ (CTN.node CTN.nil ⟨234372, 237568, 2458244512⟩ CTN.nil)))) ⟨234380, 237568, 2466191370⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨234420, 237568, 2506081969⟩ CTN.nil) ⟨234432, 237568, 2518099748⟩ CTN.nil) ⟨234460, 237568, 2546231569⟩ (CTN.node (CTN.node CTN.nil ⟨234480, 237568, 2566402846⟩ CTN.nil) ⟨234536, 237568, 2623221909⟩ CTN.nil)) ⟨234548, 237568, 2635462120⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨234560, 237568, 2647725038⟩ CTN.nil) ⟨234592, 237568, 2680536733⟩ CTN.nil) ⟨234608, 237568, 2697002640⟩ (CTN.node CTN.nil ⟨234640, 237568, 2730053889⟩ CTN.nil))) ⟨234688, 237568, 2779927284⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨234716, 237568, 2809183125⟩ CTN.nil) ⟨234736, 237568, 2830153178⟩ CTN.nil) ⟨234864, 237568, 2965783399⟩ (CTN.node (CTN.node CTN.nil ⟨234896, 237568, 3000069919⟩ CTN.nil) ⟨234944, 237568, 3051779256⟩ CTN.nil)) ⟨235004, 237568, 3116882324⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨235012, 237568, 3125601513⟩ CTN.nil) ⟨235072, 237568, 3191283139⟩ CTN.nil) ⟨235104, 237568, 3226519173⟩ (CTN.node CTN.nil ⟨235132, 237568, 3257466941⟩ CTN.nil))))) ⟨235260, 237568, 3400301060⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨235268, 237568, 3409301120⟩ CTN.nil) ⟨235296, 237568, 3440867868⟩ CTN.nil) ⟨235356, 237568, 3508856262⟩ (CTN.node (CTN.node CTN.nil ⟨235420, 237568, 3581888716⟩ CTN.nil) ⟨235456, 237568, 3623197850⟩ CTN.nil)) ⟨235528, 237568, 3706300875⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨235584, 237568, 3771375843⟩ CTN.nil) ⟨235712, 237568, 3921522783⟩ CTN.nil) ⟨235744, 237568, 3959357509⟩ (CTN.node CTN.nil ⟨235852, 237568, 4087902852⟩ CTN.nil))) ⟨236000, 237568, 4266122134⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨236108, 237568, 4397612258⟩ CTN.nil) ⟨236432, 237568, 4798801796⟩ CTN.nil) ⟨236688, 237568, 5122196973⟩ (CTN.node (CTN.node CTN.nil ⟨236728, 237568, 5173185534⟩ CTN.nil) ⟨236760, 237568, 5214060013⟩ CTN.nil)) ⟨236984, 237568, 5502137806⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237572, 6265910311⟩ CTN.nil) ⟨237568, 237586, 6264432116⟩ CTN.nil) ⟨237568, 237588, 6264220981⟩ (CTN.node CTN.nil ⟨237568, 237596, 6263376529⟩ CTN.nil)))) ⟨237568, 237600, 6262954357⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237620, 6260844029⟩ CTN.nil) ⟨237568, 237630, 6259789198⟩ CTN.nil) ⟨237568, 237632, 6259578259⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 237636, 6259156407⟩ CTN.nil) ⟨237568, 237648, 6257891063⟩ CTN.nil)) ⟨237568, 237652, 6257469353⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237664, 6256204436⟩ CTN.nil) ⟨237568, 237666, 6255993647⟩ CTN.nil) ⟨237568, 237680, 6254518377⟩ (CTN.node CTN.nil ⟨237568, 237686, 6253886251⟩ CTN.nil))) ⟨237568, 237700, 6252411602⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237716, 6250726821⟩ CTN.nil) ⟨237568, 237744, 6247779819⟩ CTN.nil) ⟨237568, 237752, 6246938138⟩ (CTN.node CTN.nil ⟨237568, 237760, 6246096598⟩ CTN.nil)) ⟨237568, 237762, 6245886235⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237768, 6245255200⟩ CTN.nil) ⟨237568, 237778, 6244203652⟩ CTN.nil) ⟨237568, 237780, 6243993369⟩ (CTN.node CTN.nil ⟨237568, 237788, 6243152325⟩ CTN.nil))))))) ⟨237568, 237810, 6240840185⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237812, 6240630044⟩ CTN.nil) ⟨237568, 237824, 6239369381⟩ CTN.nil) ⟨237568, 237826, 6239159301⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 237836, 6238109036⟩ CTN.nil) ⟨237568, 237846, 6237058992⟩ CTN.nil)) ⟨237568, 237864, 6235169470⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237876, 6233910186⟩ CTN.nil) ⟨237568, 237888, 6232651220⟩ CTN.nil) ⟨237568, 237920, 6229295531⟩ (CTN.node CTN.nil ⟨237568, 237922, 6229085875⟩ CTN.nil))) ⟨237568, 237936, 6227618533⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 237952, 6225942100⟩ CTN.nil) ⟨237568, 237956, 6225523080⟩ CTN.nil) ⟨237568, 237968, 6224266231⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 237988, 6222172188⟩ CTN.nil) ⟨237568, 237990, 6221962833⟩ CTN.nil)) ⟨237568, 237996, 6221334818⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238000, 6220916185⟩ CTN.nil) ⟨237568, 238002, 6220706882⟩ CTN.nil) ⟨237568, 238016, 6219242008⟩ (CTN.node CTN.nil ⟨237568, 238020, 6218823551⟩ CTN.nil)))) ⟨237568, 238034, 6217359231⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238052, 6215477167⟩ CTN.nil) ⟨237568, 238064, 6214222853⟩ CTN.nil) ⟨237568, 238066, 6214013832⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238068, 6213804819⟩ CTN.nil) ⟨237568, 238082, 6212341976⟩ CTN.nil)) ⟨237568, 238088, 6211715175⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238096, 6210879563⟩ CTN.nil) ⟨237568, 238098, 6210670683⟩ CTN.nil) ⟨237568, 238112, 6209208762⟩ (CTN.node CTN.nil ⟨237568, 238130, 6207329782⟩ CTN.nil))) ⟨237568, 238136, 6206703613⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238144, 6205868844⟩ CTN.nil) ⟨237568, 238148, 6205451513⟩ CTN.nil) ⟨237568, 238176, 6202531173⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238208, 6199195745⟩ CTN.nil) ⟨237568, 238212, 6198778974⟩ CTN.nil)) ⟨237568, 238224, 6197528872⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238244, 6195446068⟩ CTN.nil) ⟨237568, 238256, 6194196806⟩ CTN.nil) ⟨237568, 238260, 6193780456⟩ (CTN.node CTN.nil ⟨237568, 238272, 6192531614⟩ CTN.nil))))) ⟨237568, 238278, 6191907311⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238288, 6190866981⟩ CTN.nil) ⟨237568, 238290, 6190658941⟩ CTN.nil) ⟨237568, 238310, 6188579024⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238320, 6187539393⟩ CTN.nil) ⟨237568, 238322, 6187331493⟩ CTN.nil)) ⟨237568, 238340, 6185460785⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238342, 6185252973⟩ CTN.nil) ⟨237568, 238354, 6184006280⟩ CTN.nil) ⟨237568, 238374, 6181929157⟩ (CTN.node CTN.nil ⟨237568, 238376, 6181721492⟩ CTN.nil))) ⟨237568, 238386, 6180683301⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238388, 6180475689⟩ CTN.nil) ⟨237568, 238400, 6179230200⟩ CTN.nil) ⟨237568, 238404, 6178815107⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238432, 6175910430⟩ CTN.nil) ⟨237568, 238450, 6174044039⟩ CTN.nil)) ⟨237568, 238452, 6173836705⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238464, 6172592889⟩ CTN.nil) ⟨237568, 238480, 6170934954⟩ CTN.nil) ⟨237568, 238512, 6167620754⟩ (CTN.node CTN.nil ⟨237568, 238524, 6166378502⟩ CTN.nil)))) ⟨237568, 238532, 6165550509⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238544, 6164308779⟩ CTN.nil) ⟨237568, 238576, 6160999027⟩ CTN.nil) ⟨237568, 238578, 6160792241⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238580, 6160585464⟩ CTN.nil) ⟨237568, 238594, 6159138268⟩ CTN.nil)) ⟨237568, 238608, 6157691497⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238616, 6156864961⟩ CTN.nil) ⟨237568, 238624, 6156038564⟩ CTN.nil) ⟨237568, 238640, 6154386186⟩ (CTN.node CTN.nil ⟨237568, 238642, 6154179678⟩ CTN.nil))) ⟨237568, 238644, 6153973178⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238674, 6150876724⟩ CTN.nil) ⟨237568, 238676, 6150670363⟩ CTN.nil) ⟨237568, 238688, 6149432378⟩ (CTN.node CTN.nil ⟨237568, 238734, 6144689656⟩ CTN.nil)) ⟨237568, 238754, 6142629030⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238774, 6140569267⟩ CTN.nil) ⟨237568, 238784, 6139539709⟩ CTN.nil) ⟨237568, 238800, 6137892866⟩ (CTN.node CTN.nil ⟨237568, 238808, 6137069651⟩ CTN.nil)))))) ⟨237568, 238820, 6135835089⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238838, 6133983826⟩ CTN.nil) ⟨237568, 238852, 6132544438⟩ CTN.nil) ⟨237568, 238866, 6131105473⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238872, 6130488902⟩ CTN.nil) ⟨237568, 238896, 6128023396⟩ CTN.nil)) ⟨237568, 238904, 6127201836⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238912, 6126380414⟩ CTN.nil) ⟨237568, 238914, 6126175080⟩ CTN.nil) ⟨237568, 238920, 6125559129⟩ (CTN.node CTN.nil ⟨237568, 238930, 6124532717⟩ CTN.nil))) ⟨237568, 238934, 6124122212⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 238962, 6121249643⟩ CTN.nil) ⟨237568, 238972, 6120224133⟩ CTN.nil) ⟨237568, 238976, 6119813990⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 238988, 6118583765⟩ CTN.nil) ⟨237568, 238998, 6117558814⟩ CTN.nil)) ⟨237568, 239028, 6114485248⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239036, 6113665957⟩ CTN.nil) ⟨237568, 239040, 6113256363⟩ CTN.nil) ⟨237568, 239074, 6109776197⟩ (CTN.node CTN.nil ⟨237568, 239104, 6106707518⟩ CTN.nil)))) ⟨237568, 239116, 6105480587⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239120, 6105071678⟩ CTN.nil) ⟨237568, 239136, 6103436385⟩ CTN.nil) ⟨237568, 239152, 6101801640⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 239154, 6101597336⟩ CTN.nil) ⟨237568, 239164, 6100575941⟩ CTN.nil)) ⟨237568, 239168, 6100167443⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239186, 6098329625⟩ CTN.nil) ⟨237568, 239196, 6097308913⟩ CTN.nil) ⟨237568, 239218, 6095064101⟩ (CTN.node CTN.nil ⟨237568, 239220, 6094860078⟩ CTN.nil))) ⟨237568, 239288, 6087928386⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239360, 6080599687⟩ CTN.nil) ⟨237568, 239362, 6080396270⟩ CTN.nil) ⟨237568, 239364, 6080192861⟩ (CTN.node CTN.nil ⟨237568, 239376, 6078972585⟩ CTN.nil)) ⟨237568, 239408, 6075720015⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239424, 6074094545⟩ CTN.nil) ⟨237568, 239442, 6072266542⟩ CTN.nil) ⟨237568, 239472, 6069221398⟩ (CTN.node CTN.nil ⟨237568, 239528, 6063542236⟩ CTN.nil))))) ⟨237568, 239532, 6063136836⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239552, 6061110344⟩ CTN.nil) ⟨237568, 239556, 6060705147⟩ CTN.nil) ⟨237568, 239586, 6057667249⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 239598, 6056452624⟩ CTN.nil) ⟨237568, 239600, 6056250215⟩ CTN.nil)) ⟨237568, 239602, 6056047816⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239616, 6054631256⟩ CTN.nil) ⟨237568, 239620, 6054226600⟩ CTN.nil) ⟨237568, 239632, 6053012837⟩ (CTN.node CTN.nil ⟨237568, 239652, 6050990574⟩ CTN.nil))) ⟨237568, 239664, 6049777621⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239680, 6048160824⟩ CTN.nil) ⟨237568, 239684, 6047756709⟩ CTN.nil) ⟨237568, 239692, 6046948581⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 239716, 6044525006⟩ CTN.nil) ⟨237568, 239728, 6043313673⟩ CTN.nil)) ⟨237568, 239744, 6041699036⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239746, 6041497244⟩ CTN.nil) ⟨237568, 239748, 6041295461⟩ CTN.nil) ⟨237568, 239760, 6040084937⟩ (CTN.node CTN.nil ⟨237568, 239792, 6036858358⟩ CTN.nil)))) ⟨237568, 239794, 6036656768⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239796, 6036455187⟩ CTN.nil) ⟨237568, 239808, 6035245876⟩ CTN.nil) ⟨237568, 239812, 6034842840⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 239826, 6033432478⟩ CTN.nil) ⟨237568, 239856, 6030411661⟩ CTN.nil)) ⟨237568, 239920, 6023973569⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 239936, 6022365388⟩ CTN.nil) ⟨237568, 239984, 6017544067⟩ CTN.nil) ⟨237568, 239988, 6017142509⟩ (CTN.node CTN.nil ⟨237568, 240004, 6015536608⟩ CTN.nil))) ⟨237568, 240016, 6014332534⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240018, 6014131884⟩ CTN.nil) ⟨237568, 240048, 6011123143⟩ CTN.nil) ⟨237568, 240056, 6010321130⟩ (CTN.node CTN.nil ⟨237568, 240060, 6009920174⟩ CTN.nil)) ⟨237568, 240064, 6009519251⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240068, 6009118362⟩ CTN.nil) ⟨237568, 240072, 6008717506⟩ CTN.nil) ⟨237568, 240084, 6007515138⟩ (CTN.node CTN.nil ⟨237568, 240112, 6004710783⟩ CTN.nil))))))))

noncomputable def tab24 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240124, 6003509418⟩ CTN.nil) ⟨237568, 240128, 6003109029⟩ CTN.nil) ⟨237568, 240132, 6002708674⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 240176, 5998306972⟩ CTN.nil) ⟨237568, 240180, 5997907018⟩ CTN.nil)) ⟨237568, 240192, 5996707354⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240240, 5991911698⟩ CTN.nil) ⟨237568, 240272, 5988717257⟩ CTN.nil) ⟨237568, 240288, 5987120836⟩ (CTN.node CTN.nil ⟨237568, 240296, 5986322824⟩ CTN.nil))) ⟨237568, 240308, 5985126057⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240320, 5983929588⟩ CTN.nil) ⟨237568, 240340, 5981936138⟩ CTN.nil) ⟨237568, 240370, 5978947520⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 240372, 5978748345⟩ CTN.nil) ⟨237568, 240380, 5977951728⟩ CTN.nil)) ⟨237568, 240384, 5977553470⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240400, 5975960768⟩ CTN.nil) ⟨237568, 240412, 5974766589⟩ CTN.nil) ⟨237568, 240432, 5972776955⟩ (CTN.node CTN.nil ⟨237568, 240448, 5971185844⟩ CTN.nil)))) ⟨237568, 240472, 5968800170⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240512, 5964826696⟩ CTN.nil) ⟨237568, 240520, 5964032398⟩ CTN.nil) ⟨237568, 240556, 5960459692⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 240572, 5958872682⟩ CTN.nil) ⟨237568, 240576, 5958476012⟩ CTN.nil)) ⟨237568, 240594, 5956691406⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240640, 5952133780⟩ CTN.nil) ⟨237568, 240652, 5950945552⟩ CTN.nil) ⟨237568, 240672, 5948965829⟩ (CTN.node CTN.nil ⟨237568, 240680, 5948174171⟩ CTN.nil))) ⟨237568, 240692, 5946986930⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240700, 5946195601⟩ CTN.nil) ⟨237568, 240704, 5945799986⟩ CTN.nil) ⟨237568, 240708, 5945404404⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 240736, 5942636249⟩ CTN.nil) ⟨237568, 240738, 5942438585⟩ CTN.nil)) ⟨237568, 240748, 5941450390⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240750, 5941252776⟩ CTN.nil) ⟨237568, 240756, 5940659982⟩ CTN.nil) ⟨237568, 240768, 5939474616⟩ (CTN.node CTN.nil ⟨237568, 240800, 5936315086⟩ CTN.nil))))) ⟨237568, 240812, 5935130804⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240844, 5931974162⟩ CTN.nil) ⟨237568, 240860, 5930396628⟩ CTN.nil) ⟨237568, 240864, 5930002327⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 240876, 5928819619⟩ CTN.nil) ⟨237568, 240884, 5928031311⟩ CTN.nil)) ⟨237568, 240896, 5926849095⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 240908, 5925667173⟩ CTN.nil) ⟨237568, 240928, 5923697959⟩ CTN.nil) ⟨237568, 240944, 5922123176⟩ (CTN.node CTN.nil ⟨237568, 240948, 5921729562⟩ CTN.nil))) ⟨237568, 240992, 5917401968⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241026, 5914060625⟩ CTN.nil) ⟨237568, 241028, 5913864149⟩ CTN.nil) ⟨237568, 241040, 5912685464⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 241072, 5909543739⟩ CTN.nil) ⟨237568, 241088, 5907973660⟩ CTN.nil)) ⟨237568, 241116, 5905227275⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241136, 5903266549⟩ CTN.nil) ⟨237568, 241168, 5900131079⟩ CTN.nil) ⟨237568, 241192, 5897780844⟩ (CTN.node CTN.nil ⟨237568, 241200, 5896997692⟩ CTN.nil)))) ⟨237568, 241216, 5895431778⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241232, 5893866385⟩ CTN.nil) ⟨237568, 241264, 5890737156⟩ CTN.nil) ⟨237568, 241280, 5889173320⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 241296, 5887610004⟩ CTN.nil) ⟨237568, 241316, 5885656588⟩ CTN.nil)) ⟨237568, 241320, 5885266002⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241328, 5884484927⟩ CTN.nil) ⟨237568, 241344, 5882923166⟩ CTN.nil) ⟨237568, 241380, 5879411099⟩ (CTN.node CTN.nil ⟨237568, 241392, 5878240993⟩ CTN.nil))) ⟨237568, 241424, 5875122132⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241456, 5872005339⟩ CTN.nil) ⟨237568, 241468, 5870837075⟩ CTN.nil) ⟨237568, 241472, 5870447718⟩ (CTN.node CTN.nil ⟨237568, 241476, 5870058394⟩ CTN.nil)) ⟨237568, 241488, 5868890614⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241504, 5867334026⟩ CTN.nil) ⟨237568, 241508, 5866944959⟩ CTN.nil) ⟨237568, 241520, 5865777954⟩ (CTN.node CTN.nil ⟨237568, 241524, 5865389016⟩ CTN.nil)))))) ⟨237568, 241568, 5861112832⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241584, 5859558823⟩ CTN.nil) ⟨237568, 241648, 5853347934⟩ CTN.nil) ⟨237568, 241668, 5851408719⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 241672, 5851020972⟩ CTN.nil) ⟨237568, 241680, 5850245575⟩ CTN.nil)) ⟨237568, 241712, 5847145273⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241716, 5846757879⟩ CTN.nil) ⟨237568, 241728, 5845595892⟩ CTN.nil) ⟨237568, 241732, 5845208627⟩ (CTN.node CTN.nil ⟨237568, 241744, 5844047024⟩ CTN.nil))) ⟨237568, 241776, 5840950827⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241780, 5840563947⟩ CTN.nil) ⟨237568, 241788, 5839790282⟩ CTN.nil) ⟨237568, 241792, 5839403498⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 241808, 5837856681⟩ CTN.nil) ⟨237568, 241840, 5834764584⟩ CTN.nil)) ⟨237568, 241856, 5833219304⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241872, 5831674534⟩ CTN.nil) ⟨237568, 241876, 5831288422⟩ CTN.nil) ⟨237568, 241888, 5830130277⟩ (CTN.node CTN.nil ⟨237568, 241904, 5828586530⟩ CTN.nil)))) ⟨237568, 241952, 5823958356⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 241960, 5823187441⟩ CTN.nil) ⟨237568, 241968, 5822416653⟩ CTN.nil) ⟨237568, 241972, 5822031307⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 241984, 5820875459⟩ CTN.nil) ⟨237568, 242000, 5819334776⟩ CTN.nil)) ⟨237568, 242032, 5816254939⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242044, 5815100525⟩ CTN.nil) ⟨237568, 242048, 5814715784⟩ CTN.nil) ⟨237568, 242060, 5813561752⟩ (CTN.node CTN.nil ⟨237568, 242068, 5812792557⟩ CTN.nil))) ⟨237568, 242092, 5810485734⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242100, 5809717047⟩ CTN.nil) ⟨237568, 242108, 5808948488⟩ CTN.nil) ⟨237568, 242112, 5808564256⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 242132, 5806643572⟩ CTN.nil) ⟨237568, 242144, 5805491543⟩ CTN.nil)) ⟨237568, 242156, 5804339799⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242160, 5803955948⟩ CTN.nil) ⟨237568, 242236, 5796668805⟩ CTN.nil) ⟨237568, 242240, 5796285588⟩ (CTN.node CTN.nil ⟨237568, 242292, 5791306650⟩ CTN.nil))))) ⟨237568, 242316, 5789010482⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242324, 5788245346⟩ CTN.nil) ⟨237568, 242336, 5787097878⟩ CTN.nil) ⟨237568, 242344, 5786333058⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 242356, 5785186064⟩ CTN.nil) ⟨237568, 242364, 5784421560⟩ CTN.nil)) ⟨237568, 242368, 5784039355⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242372, 5783657182⟩ CTN.nil) ⟨237568, 242400, 5780982852⟩ CTN.nil) ⟨237568, 242412, 5779837184⟩ (CTN.node CTN.nil ⟨237568, 242420, 5779073563⟩ CTN.nil))) ⟨237568, 242432, 5777928368⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242436, 5777546700⟩ CTN.nil) ⟨237568, 242440, 5777165063⟩ CTN.nil) ⟨237568, 242464, 5774875902⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 242476, 5773731747⟩ CTN.nil) ⟨237568, 242480, 5773350425⟩ CTN.nil)) ⟨237568, 242484, 5772969135⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242496, 5771825452⟩ CTN.nil) ⟨237568, 242508, 5770682053⟩ CTN.nil) ⟨237568, 242528, 5768777016⟩ (CTN.node CTN.nil ⟨237568, 242544, 5767253553⟩ CTN.nil)))) ⟨237568, 242548, 5766872766⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242604, 5761545044⟩ CTN.nil) ⟨237568, 242624, 5759643778⟩ CTN.nil) ⟨237568, 242640, 5758123329⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 242676, 5754704155⟩ CTN.nil) ⟨237568, 242692, 5753185337⟩ CTN.nil)) ⟨237568, 242724, 5750149203⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242732, 5749390483⟩ CTN.nil) ⟨237568, 242736, 5749011170⟩ CTN.nil) ⟨237568, 242752, 5747494230⟩ (CTN.node CTN.nil ⟨237568, 242788, 5744082944⟩ CTN.nil))) ⟨237568, 242800, 5742946411⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242832, 5739917031⟩ CTN.nil) ⟨237568, 242864, 5736889649⟩ CTN.nil) ⟨237568, 242880, 5735376706⟩ (CTN.node CTN.nil ⟨237568, 242896, 5733864262⟩ CTN.nil)) ⟨237568, 242980, 5725932109⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 242984, 5725554729⟩ CTN.nil) ⟨237568, 242992, 5724800064⟩ CTN.nil) ⟨237568, 243008, 5723291106⟩ (CTN.node CTN.nil ⟨237568, 243044, 5719897769⟩ CTN.nil))))))) ⟨237568, 243052, 5719144036⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243056, 5718767216⟩ CTN.nil) ⟨237568, 243076, 5716883581⟩ CTN.nil) ⟨237568, 243088, 5715753773⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 243120, 5712742314⟩ CTN.nil) ⟨237568, 243136, 5711237329⟩ CTN.nil)) ⟨237568, 243160, 5708980780⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243196, 5705598047⟩ CTN.nil) ⟨237568, 243200, 5705222343⟩ CTN.nil) ⟨237568, 243232, 5702217819⟩ (CTN.node CTN.nil ⟨237568, 243312, 5694715161⟩ CTN.nil))) ⟨237568, 243332, 5692841425⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243336, 5692466771⟩ CTN.nil) ⟨237568, 243376, 5688721919⟩ CTN.nil) ⟨237568, 243384, 5687973318⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 243392, 5687224841⟩ CTN.nil) ⟨237568, 243420, 5684606139⟩ CTN.nil)) ⟨237568, 243432, 5683484299⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243440, 5682736560⟩ CTN.nil) ⟨237568, 243456, 5681241451⟩ CTN.nil) ⟨237568, 243472, 5679746834⟩ (CTN.node CTN.nil ⟨237568, 243484, 5678626193⟩ CTN.nil)))) ⟨237568, 243500, 5677132436⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243504, 5676759073⟩ CTN.nil) ⟨237568, 243520, 5675265930⟩ CTN.nil) ⟨237568, 243536, 5673773277⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 243544, 5673027135⟩ CTN.nil) ⟨237568, 243552, 5672281115⟩ CTN.nil)) ⟨237568, 243584, 5669298264⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243592, 5668552857⟩ CTN.nil) ⟨237568, 243600, 5667807573⟩ CTN.nil) ⟨237568, 243624, 5665572456⟩ (CTN.node CTN.nil ⟨237568, 243696, 5658873714⟩ CTN.nil))) ⟨237568, 243724, 5656271322⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243744, 5654413387⟩ CTN.nil) ⟨237568, 243760, 5652927588⟩ CTN.nil) ⟨237568, 243772, 5651813559⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 243776, 5651442277⟩ CTN.nil) ⟨237568, 243780, 5651071025⟩ CTN.nil)) ⟨237568, 243800, 5649215225⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243808, 5648473118⟩ CTN.nil) ⟨237568, 243816, 5647731133⟩ CTN.nil) ⟨237568, 243820, 5647360187⟩ (CTN.node CTN.nil ⟨237568, 243828, 5646618384⟩ CTN.nil))))) ⟨237568, 243872, 5642540650⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 243980, 5632547263⟩ CTN.nil) ⟨237568, 244000, 5630699064⟩ CTN.nil) ⟨237568, 244008, 5629959997⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 244020, 5628851624⟩ CTN.nil) ⟨237568, 244028, 5628112860⟩ CTN.nil)) ⟨237568, 244032, 5627743524⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244036, 5627374218⟩ CTN.nil) ⟨237568, 244064, 5624789923⟩ CTN.nil) ⟨237568, 244084, 5622944906⟩ (CTN.node CTN.nil ⟨237568, 244128, 5618888532⟩ CTN.nil))) ⟨237568, 244140, 5617782883⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244156, 5616309108⟩ CTN.nil) ⟨237568, 244160, 5615940740⟩ CTN.nil) ⟨237568, 244208, 5611522675⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 244212, 5611154700⟩ CTN.nil) ⟨237568, 244256, 5607108956⟩ CTN.nil)) ⟨237568, 244272, 5605638680⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244276, 5605271187⟩ CTN.nil) ⟨237568, 244288, 5604168887⟩ CTN.nil) ⟨237568, 244304, 5602699575⟩ (CTN.node CTN.nil ⟨237568, 244396, 5594260373⟩ CTN.nil)))) ⟨237568, 244404, 5593527281⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244412, 5592794309⟩ CTN.nil) ⟨237568, 244416, 5592427868⟩ CTN.nil) ⟨237568, 244460, 5588398996⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 244464, 5588032915⟩ CTN.nil) ⟨237568, 244536, 5581448579⟩ CTN.nil)) ⟨237568, 244540, 5581083067⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244544, 5580717585⟩ CTN.nil) ⟨237568, 244552, 5579986711⟩ CTN.nil) ⟨237568, 244560, 5579255957⟩ (CTN.node CTN.nil ⟨237568, 244588, 5576699257⟩ CTN.nil))) ⟨237568, 244592, 5576334134⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244608, 5574873941⟩ CTN.nil) ⟨237568, 244716, 5565030126⟩ CTN.nil) ⟨237568, 244720, 5564665958⟩ (CTN.node CTN.nil ⟨237568, 244736, 5563209583⟩ CTN.nil)) ⟨237568, 244740, 5562845564⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244780, 5559207008⟩ CTN.nil) ⟨237568, 244784, 5558843317⟩ CTN.nil) ⟨237568, 244796, 5557752419⟩ (CTN.node CTN.nil ⟨237568, 244800, 5557388847⟩ CTN.nil)))))) ⟨237568, 244816, 5555934852⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244844, 5553391506⟩ CTN.nil) ⟨237568, 244848, 5553028290⟩ CTN.nil) ⟨237568, 244860, 5551938820⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 244908, 5547583608⟩ CTN.nil) ⟨237568, 244972, 5541783302⟩ CTN.nil)) ⟨237568, 244980, 5541058797⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 244996, 5539610142⟩ CTN.nil) ⟨237568, 245020, 5537438048⟩ CTN.nil) ⟨237568, 245040, 5535628782⟩ (CTN.node CTN.nil ⟨237568, 245056, 5534181902⟩ CTN.nil))) ⟨237568, 245060, 5533820256⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245072, 5532735494⟩ CTN.nil) ⟨237568, 245084, 5531650999⟩ CTN.nil) ⟨237568, 245104, 5529844097⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 245108, 5529482805⟩ CTN.nil) ⟨237568, 245116, 5528760310⟩ CTN.nil)) ⟨237568, 245136, 5526954588⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245148, 5525871509⟩ CTN.nil) ⟨237568, 245164, 5524427817⟩ CTN.nil) ⟨237568, 245168, 5524066967⟩ (CTN.node CTN.nil ⟨237568, 245172, 5523706147⟩ CTN.nil)))) ⟨237568, 245180, 5522984596⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245184, 5522623864⟩ CTN.nil) ⟨237568, 245236, 5517937033⟩ CTN.nil) ⟨237568, 245256, 5516135729⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 245280, 5513975135⟩ CTN.nil) ⟨237568, 245288, 5513255173⟩ CTN.nil)) ⟨237568, 245292, 5512895235⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245296, 5512535327⟩ CTN.nil) ⟨237568, 245300, 5512175449⟩ CTN.nil) ⟨237568, 245360, 5506780794⟩ (CTN.node CTN.nil ⟨237568, 245408, 5502469821⟩ CTN.nil))) ⟨237568, 245424, 5501033768⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245428, 5500674828⟩ CTN.nil) ⟨237568, 245436, 5499957036⟩ CTN.nil) ⟨237568, 245440, 5499598183⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 245472, 5496728419⟩ CTN.nil) ⟨237568, 245484, 5495652740⟩ CTN.nil)) ⟨237568, 245500, 5494218911⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245504, 5493860527⟩ CTN.nil) ⟨237568, 245512, 5493143846⟩ CTN.nil) ⟨237568, 245536, 5490994505⟩ (CTN.node CTN.nil ⟨237568, 245544, 5490278291⟩ CTN.nil))))) ⟨237568, 245568, 5488130352⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245580, 5487056776⟩ CTN.nil) ⟨237568, 245616, 5483837624⟩ CTN.nil) ⟨237568, 245628, 5482765098⟩ (CTN.node (CTN.node CTN.nil ⟨237568, 245664, 5479549093⟩ CTN.nil) ⟨237568, 245672, 5478834745⟩ CTN.nil)) ⟨237568, 245696, 5476692401⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨237568, 245728, 5473837572⟩ CTN.nil) ⟨237568, 245744, 5472410855⟩ CTN.nil) ⟨237568, 245760, 5470984602⟩ (CTN.node CTN.nil ⟨243152, 245760, 11205228276⟩ CTN.nil))) ⟨243920, 245760, 11688866540⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 245792, 12349948495⟩ CTN.nil) ⟨245760, 245808, 12346585142⟩ CTN.nil) ⟨245760, 245824, 12343164825⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 245836, 12340562231⟩ CTN.nil) ⟨245760, 245840, 12339687589⟩ CTN.nil)) ⟨245760, 245856, 12336153482⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 245884, 12329832095⟩ CTN.nil) ⟨245760, 245888, 12328914849⟩ CTN.nil) ⟨245760, 246000, 12301795413⟩ (CTN.node CTN.nil ⟨245760, 246020, 12296661493⟩ CTN.nil)))) ⟨245760, 246064, 12285057354⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246076, 12281818839⟩ CTN.nil) ⟨245760, 246084, 12279642293⟩ CTN.nil) ⟨245760, 246124, 12268549382⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 246132, 12266288813⟩ CTN.nil) ⟨245760, 246160, 12258266783⟩ CTN.nil)) ⟨245760, 246168, 12255943365⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246232, 12236854548⟩ CTN.nil) ⟨245760, 246308, 12213032487⟩ CTN.nil) ⟨245760, 246324, 12207858222⟩ (CTN.node CTN.nil ⟨245760, 246340, 12202628758⟩ CTN.nil))) ⟨245760, 246388, 12186609814⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246408, 12179789214⟩ CTN.nil) ⟨245760, 246444, 12167296205⟩ CTN.nil) ⟨245760, 246456, 12163070280⟩ (CTN.node CTN.nil ⟨245760, 246464, 12160235913⟩ CTN.nil)) ⟨245760, 246504, 12145859386⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246512, 12142943202⟩ CTN.nil) ⟨245760, 246516, 12141480007⟩ CTN.nil) ⟨245760, 246560, 12125160665⟩ (CTN.node CTN.nil ⟨245760, 246580, 12117607151⟩ CTN.nil))))))))

noncomputable def tab25 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246656, 12088133631⟩ CTN.nil) ⟨245760, 246664, 12084960423⟩ CTN.nil) ⟨245760, 246708, 12067267816⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 246712, 12065639293⟩ CTN.nil) ⟨245760, 246720, 12062372211⟩ CTN.nil)) ⟨245760, 246760, 12045836385⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246768, 12042489202⟩ CTN.nil) ⟨245760, 246784, 12035754896⟩ CTN.nil) ⟨245760, 246840, 12011766450⟩ (CTN.node CTN.nil ⟨245760, 246844, 12010028144⟩ CTN.nil))) ⟨245760, 246848, 12008286531⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 246872, 11997767492⟩ CTN.nil) ⟨245760, 246888, 11990688828⟩ CTN.nil) ⟨245760, 246892, 11988910928⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 246896, 11987129735⟩ CTN.nil) ⟨245760, 246912, 11979972077⟩ CTN.nil)) ⟨245760, 246928, 11972761854⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247024, 11928401222⟩ CTN.nil) ⟨245760, 247040, 11920825333⟩ CTN.nil) ⟨245760, 247044, 11918923247⟩ (CTN.node CTN.nil ⟨245760, 247100, 11891954144⟩ CTN.nil)))) ⟨245760, 247148, 11868334640⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247152, 11866345463⟩ CTN.nil) ⟨245760, 247164, 11860358696⟩ CTN.nil) ⟨245760, 247212, 11836123755⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 247276, 11803097212⟩ CTN.nil) ⟨245760, 247300, 11790503138⟩ CTN.nil)) ⟨245760, 247328, 11775666507⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247344, 11767119204⟩ CTN.nil) ⟨245760, 247468, 11699181498⟩ CTN.nil) ⟨245760, 247488, 11687944184⟩ (CTN.node CTN.nil ⟨245760, 247584, 11632934271⟩ CTN.nil))) ⟨245760, 247596, 11625934069⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247608, 11618906458⟩ CTN.nil) ⟨245760, 247664, 11585749762⟩ CTN.nil) ⟨245760, 247744, 11537357683⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 247768, 11522606476⟩ CTN.nil) ⟨245760, 247792, 11507748077⟩ CTN.nil)) ⟨245760, 247808, 11497783098⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247832, 11482746822⟩ CTN.nil) ⟨245760, 247840, 11477711100⟩ CTN.nil) ⟨245760, 247864, 11462533227⟩ (CTN.node CTN.nil ⟨245760, 247888, 11447249572⟩ CTN.nil))))) ⟨245760, 247896, 11442131574⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 247920, 11426707431⟩ CTN.nil) ⟨245760, 247932, 11418955982⟩ CTN.nil) ⟨245760, 248048, 11342681784⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 248064, 11331971444⟩ CTN.nil) ⟨245760, 248092, 11313118536⟩ CTN.nil)) ⟨245760, 248128, 11288674548⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 248144, 11277736995⟩ CTN.nil) ⟨245760, 248160, 11266754335⟩ CTN.nil) ⟨245760, 248176, 11255726679⟩ (CTN.node CTN.nil ⟨245760, 248188, 11247426476⟩ CTN.nil))) ⟨245760, 248192, 11244654140⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 248220, 11225169539⟩ CTN.nil) ⟨245760, 248304, 11165899209⟩ CTN.nil) ⟨245760, 248328, 11148741515⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 248348, 11134368152⟩ CTN.nil) ⟨245760, 248368, 11119926591⟩ CTN.nil)) ⟨245760, 248380, 11111229014⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 248428, 11076195010⟩ CTN.nil) ⟨245760, 248476, 11040773484⟩ CTN.nil) ⟨245760, 248584, 10959674890⟩ (CTN.node CTN.nil ⟨245760, 248616, 10935277502⟩ CTN.nil)))) ⟨245760, 248748, 10832888533⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 248768, 10817132160⟩ CTN.nil) ⟨245760, 248816, 10779059397⟩ CTN.nil) ⟨245760, 248880, 10727735161⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 248896, 10714804851⟩ CTN.nil) ⟨245760, 248960, 10662690453⟩ CTN.nil)) ⟨245760, 249024, 10609953195⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 249056, 10583353592⟩ CTN.nil) ⟨245760, 249072, 10569996506⟩ CTN.nil) ⟨245760, 249200, 10461782356⟩ (CTN.node CTN.nil ⟨245760, 249216, 10448087897⟩ CTN.nil))) ⟨245760, 249328, 10351203274⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 249344, 10337218034⟩ CTN.nil) ⟨245760, 249456, 10238328368⟩ CTN.nil) ⟨245760, 249468, 10227631145⟩ (CTN.node CTN.nil ⟨245760, 249488, 10209759126⟩ CTN.nil)) ⟨245760, 249528, 10173853644⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 249560, 10144975472⟩ CTN.nil) ⟨245760, 249576, 10130485507⟩ CTN.nil) ⟨245760, 249648, 10064865254⟩ (CTN.node CTN.nil ⟨245760, 249736, 9983753797⟩ CTN.nil)))))) ⟨245760, 249784, 9939097608⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 249792, 9931626902⟩ CTN.nil) ⟨245760, 249832, 9894154408⟩ CTN.nil) ⟨245760, 249888, 9841363099⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 249912, 9818621812⟩ CTN.nil) ⟨245760, 249920, 9811025991⟩ CTN.nil)) ⟨245760, 249952, 9780566225⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 249960, 9772932254⟩ CTN.nil) ⟨245760, 250040, 9696178922⟩ CTN.nil) ⟨245760, 250048, 9688462628⟩ (CTN.node CTN.nil ⟨245760, 250112, 9626468354⟩ CTN.nil))) ⟨245760, 250144, 9595297185⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 250216, 9524745415⟩ CTN.nil) ⟨245760, 250240, 9501101744⟩ CTN.nil) ⟨245760, 250344, 9397931607⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 250516, 9224844104⟩ CTN.nil) ⟨245760, 250672, 9065342512⟩ CTN.nil)) ⟨245760, 250680, 9057101187⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 250816, 8916113590⟩ CTN.nil) ⟨245760, 250840, 8891063937⟩ CTN.nil) ⟨245760, 250936, 8790375467⟩ (CTN.node CTN.nil ⟨245760, 250968, 8756642413⟩ CTN.nil)))) ⟨245760, 250992, 8731288062⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 251008, 8714359474⟩ CTN.nil) ⟨245760, 251064, 8654950045⟩ CTN.nil) ⟨245760, 251096, 8620892362⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 251112, 8603834184⟩ CTN.nil) ⟨245760, 251120, 8595297829⟩ CTN.nil)) ⟨245760, 251168, 8543979226⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 251192, 8518256220⟩ CTN.nil) ⟨245760, 251200, 8509672577⟩ CTN.nil) ⟨245760, 251224, 8483894006⟩ (CTN.node CTN.nil ⟨245760, 251232, 8475292000⟩ CTN.nil))) ⟨245760, 251248, 8458074384⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 251264, 8440838759⟩ CTN.nil) ⟨245760, 251328, 8371719348⟩ CTN.nil) ⟨245760, 251376, 8319698463⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 251392, 8302324476⟩ CTN.nil) ⟨245760, 251496, 8188996488⟩ CTN.nil)) ⟨245760, 251520, 8162748999⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 251656, 8013378450⟩ CTN.nil) ⟨245760, 251712, 7951574372⟩ CTN.nil) ⟨245760, 251840, 7809702995⟩ (CTN.node CTN.nil ⟨245760, 251952, 7684927063⟩ CTN.nil))))) ⟨245760, 252096, 7523717741⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 252128, 7487784414⟩ CTN.nil) ⟨245760, 252144, 7469803846⟩ CTN.nil) ⟨245760, 252216, 7388781568⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 252240, 7361735933⟩ CTN.nil) ⟨245760, 252272, 7325646867⟩ CTN.nil)) ⟨245760, 252352, 7235291093⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 252400, 7180992790⟩ CTN.nil) ⟨245760, 252416, 7162880181⟩ CTN.nil) ⟨245760, 252528, 7035923973⟩ (CTN.node CTN.nil ⟨245760, 252656, 6890522706⟩ CTN.nil))) ⟨245760, 252672, 6872328267⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 252784, 6744871161⟩ CTN.nil) ⟨245760, 252856, 6662862972⟩ CTN.nil) ⟨245760, 252904, 6608168465⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 253032, 6462265182⟩ CTN.nil) ⟨245760, 253064, 6425784614⟩ CTN.nil)) ⟨245760, 253120, 6361945937⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 253160, 6316351863⟩ CTN.nil) ⟨245760, 253240, 6225187053⟩ CTN.nil) ⟨245760, 253264, 6197845992⟩ (CTN.node CTN.nil ⟨245760, 253288, 6170509746⟩ CTN.nil)))) ⟨245760, 253368, 6079430538⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨245760, 253416, 6024819718⟩ CTN.nil) ⟨245760, 253544, 5879362262⟩ CTN.nil) ⟨245760, 253568, 5852121386⟩ (CTN.node (CTN.node CTN.nil ⟨245760, 253800, 5589464713⟩ CTN.nil) ⟨245760, 253952, 5418189199⟩ CTN.nil)) ⟨245900, 253952, 5429643105⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨246668, 253952, 5492648647⟩ CTN.nil) ⟨249632, 253952, 5736009697⟩ CTN.nil) ⟨249712, 253952, 5742526803⟩ (CTN.node CTN.nil ⟨253952, 254000, 6017013441⟩ CTN.nil))) ⟨253952, 254008, 6007167212⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 254136, 5849966368⟩ CTN.nil) ⟨253952, 254168, 5810771500⟩ CTN.nil) ⟨253952, 254184, 5791190760⟩ (CTN.node CTN.nil ⟨253952, 254296, 5654452260⟩ CTN.nil)) ⟨253952, 254440, 5479551124⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 254448, 5469866348⟩ CTN.nil) ⟨253952, 254496, 5411831800⟩ CTN.nil) ⟨253952, 254528, 5373214124⟩ (CTN.node CTN.nil ⟨253952, 254560, 5334655536⟩ CTN.nil))))))) ⟨253952, 254568, 5325025269⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 254704, 5161906701⟩ CTN.nil) ⟨253952, 254720, 5142792756⟩ CTN.nil) ⟨253952, 254824, 5018964658⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 254984, 4829929935⟩ CTN.nil) ⟨253952, 255056, 4745480325⟩ CTN.nil)) ⟨253952, 255152, 4633507938⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 255216, 4559272196⟩ CTN.nil) ⟨253952, 255280, 4485377471⟩ CTN.nil) ⟨253952, 255288, 4476165075⟩ (CTN.node CTN.nil ⟨253952, 255408, 4338648401⟩ CTN.nil))) ⟨253952, 255424, 4320409500⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 255600, 4121343877⟩ CTN.nil) ⟨253952, 255728, 3978439280⟩ CTN.nil) ⟨253952, 255856, 3837189707⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 255872, 3819653364⟩ CTN.nil) ⟨253952, 255984, 3697664839⟩ CTN.nil)) ⟨253952, 256184, 3483272115⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 256336, 3323417884⟩ CTN.nil) ⟨253952, 256360, 3298429467⟩ CTN.nil) ⟨253952, 256432, 3223884847⟩ (CTN.node CTN.nil ⟨253952, 256448, 3207405852⟩ CTN.nil)))) ⟨253952, 256488, 3166347375⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 256688, 2964094154⟩ CTN.nil) ⟨253952, 256696, 2956111387⟩ CTN.nil) ⟨253952, 256744, 2908391511⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 256872, 2782639106⟩ CTN.nil) ⟨253952, 257024, 2636207502⟩ CTN.nil)) ⟨253952, 257336, 2345881870⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 257464, 2230902134⟩ CTN.nil) ⟨253952, 257496, 2202542455⟩ CTN.nil) ⟨253952, 257512, 2188420944⟩ (CTN.node CTN.nil ⟨253952, 257624, 2090668164⟩ CTN.nil))) ⟨253952, 257768, 1967847439⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 257848, 1901027242⟩ CTN.nil) ⟨253952, 257896, 1861425857⟩ CTN.nil) ⟨253952, 257920, 1841764121⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 258112, 1687843176⟩ CTN.nil) ⟨253952, 258152, 1656539113⟩ CTN.nil)) ⟨253952, 258432, 1444924345⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 258608, 1318760832⟩ CTN.nil) ⟨253952, 258616, 1313153777⟩ CTN.nil) ⟨253952, 258784, 1197998146⟩ (CTN.node CTN.nil ⟨253952, 259056, 1022185846⟩ CTN.nil))))) ⟨253952, 259168, 953669250⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 259296, 878168081⟩ CTN.nil) ⟨253952, 259312, 868941899⟩ CTN.nil) ⟨253952, 259328, 859762868⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 259584, 719347841⟩ CTN.nil) ⟨253952, 259664, 677974142⟩ CTN.nil)) ⟨253952, 259816, 602678863⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 260200, 431973312⟩ CTN.nil) ⟨253952, 260480, 325287065⟩ CTN.nil) ⟨253952, 260792, 224207583⟩ (CTN.node CTN.nil ⟨253952, 260992, 169311016⟩ CTN.nil))) ⟨253952, 260996, 168292016⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 261060, 152408937⟩ CTN.nil) ⟨253952, 261632, 45574600⟩ CTN.nil) ⟨253952, 261764, 29855948⟩ (CTN.node (CTN.node CTN.nil ⟨253952, 261828, 23433802⟩ CTN.nil) ⟨253952, 261944, 13783017⟩ CTN.nil)) ⟨253952, 262064, 6488198⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨253952, 262124, 3862282⟩ CTN.nil) ⟨253952, 262144, 3137894⟩ CTN.nil) ⟨262144, 262172, 4950243⟩ (CTN.node CTN.nil ⟨262144, 262176, 4773716⟩ CTN.nil)))) ⟨262396, 267544, 214⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262396, 268312, 212⟩ CTN.nil) ⟨262396, 269144, 209⟩ CTN.nil) ⟨262408, 267398, 16938⟩ (CTN.node (CTN.node CTN.nil ⟨262408, 267430, 16930⟩ CTN.nil) ⟨262408, 268262, 16721⟩ CTN.nil)) ⟨262408, 269094, 16515⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262408, 270336, 16213⟩ CTN.nil) ⟨262412, 267592, 28357⟩ CTN.nil) ⟨262412, 269192, 27688⟩ (CTN.node CTN.nil ⟨262414, 267700, 35142⟩ CTN.nil))) ⟨262420, 270336, 57752⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262422, 267444, 70112⟩ CTN.nil) ⟨262424, 267382, 80748⟩ CTN.nil) ⟨262424, 270336, 77273⟩ (CTN.node CTN.nil ⟨262428, 267576, 103810⟩ CTN.nil)) ⟨262436, 270336, 152865⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262438, 267428, 175378⟩ CTN.nil) ⟨262438, 268292, 173128⟩ CTN.nil) ⟨262438, 269028, 171240⟩ (CTN.node CTN.nil ⟨262440, 270336, 183739⟩ CTN.nil)))))) ⟨262442, 265880, 214016⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262444, 267624, 226408⟩ CTN.nil) ⟨262444, 268392, 223826⟩ CTN.nil) ⟨262450, 269072, 278521⟩ (CTN.node (CTN.node CTN.nil ⟨262452, 270336, 293395⟩ CTN.nil) ⟨262454, 267508, 327663⟩ CTN.nil)) ⟨262456, 270336, 335626⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262458, 265480, 384734⟩ CTN.nil) ⟨262460, 268376, 391949⟩ CTN.nil) ⟨262460, 269208, 387122⟩ (CTN.node CTN.nil ⟨262460, 270336, 380697⟩ CTN.nil))) ⟨262468, 270336, 479358⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262470, 268524, 519601⟩ CTN.nil) ⟨262472, 267462, 556247⟩ CTN.nil) ⟨262472, 268230, 549899⟩ (CTN.node (CTN.node CTN.nil ⟨262472, 269894, 536452⟩ CTN.nil) ⟨262472, 270336, 532950⟩ CTN.nil)) ⟨262476, 269256, 598902⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262478, 267764, 642797⟩ CTN.nil) ⟨262478, 268532, 635469⟩ CTN.nil) ⟨262484, 269170, 723174⟩ (CTN.node CTN.nil ⟨262484, 270336, 710769⟩ CTN.nil)))) ⟨262490, 265880, 864942⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262492, 270336, 843521⟩ CTN.nil) ⟨262500, 270336, 987641⟩ CTN.nil) ⟨262504, 268262, 1097276⟩ (CTN.node (CTN.node CTN.nil ⟨262504, 270336, 1063964⟩ CTN.nil) ⟨262506, 265480, 1186215⟩ CTN.nil)) ⟨262512, 270336, 1225138⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262516, 270336, 1309989⟩ CTN.nil) ⟨262518, 267540, 1410998⟩ CTN.nil) ⟨262518, 269172, 1377063⟩ (CTN.node CTN.nil ⟨262520, 270336, 1397684⟩ CTN.nil))) ⟨262524, 270336, 1488221⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262532, 266275, 1782629⟩ CTN.nil) ⟨262532, 268258, 1730462⟩ CTN.nil) ⟨262532, 268354, 1727985⟩ (CTN.node CTN.nil ⟨262532, 270336, 1677827⟩ CTN.nil)) ⟨262536, 268484, 1826471⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262536, 269316, 1803989⟩ CTN.nil) ⟨262536, 269412, 1801417⟩ CTN.nil) ⟨262536, 270336, 1776896⟩ (CTN.node CTN.nil ⟨262540, 270336, 1878809⟩ CTN.nil))))) ⟨262548, 267538, 2180098⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262548, 269170, 2127665⟩ CTN.nil) ⟨262548, 270224, 2094639⟩ CTN.nil) ⟨262548, 270336, 2091167⟩ (CTN.node (CTN.node CTN.nil ⟨262552, 270336, 2201614⟩ CTN.nil) ⟨262564, 267522, 2659104⟩ CTN.nil)) ⟨262566, 266277, 2773562⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262568, 268516, 2745084⟩ CTN.nil) ⟨262568, 268612, 2741159⟩ CTN.nil) ⟨262568, 270336, 2671850⟩ (CTN.node CTN.nil ⟨262576, 269996, 2938809⟩ CTN.nil))) ⟨262584, 270336, 3187616⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262587, 265977, 3510559⟩ CTN.nil) ⟨262590, 267738, 3526488⟩ CTN.nil) ⟨262598, 266341, 3902029⟩ (CTN.node (CTN.node CTN.nil ⟨262600, 269380, 3802467⟩ CTN.nil) ⟨262600, 270054, 3764620⟩ CTN.nil)) ⟨262603, 265625, 4140615⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262603, 265993, 4117731⟩ CTN.nil) ⟨262603, 266041, 4114758⟩ CTN.nil) ⟨262604, 270336, 3896370⟩ (CTN.node CTN.nil ⟨262612, 268882, 4291452⟩ CTN.nil)))) ⟨262612, 270224, 4206773⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262612, 270288, 4202787⟩ CTN.nil) ⟨262612, 270336, 4199801⟩ CTN.nil) ⟨262619, 265641, 4799731⟩ (CTN.node (CTN.node CTN.nil ⟨262619, 266057, 4769759⟩ CTN.nil) ⟨262628, 268834, 4950013⟩ CTN.nil)) ⟨262628, 270176, 4852321⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262628, 270336, 4840835⟩ CTN.nil) ⟨262630, 270336, 4924169⟩ CTN.nil) ⟨262632, 270336, 5008214⟩ (CTN.node CTN.nil ⟨262638, 267892, 5459536⟩ CTN.nil))) ⟨262638, 269492, 5330935⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262644, 270130, 5544335⟩ CTN.nil) ⟨262644, 270336, 5527442⟩ CTN.nil) ⟨262645, 266964, 5858980⟩ (CTN.node CTN.nil ⟨262646, 268668, 5757361⟩ CTN.nil)) ⟨262648, 270336, 5706216⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262652, 270336, 5887838⟩ CTN.nil) ⟨262654, 268570, 6138677⟩ CTN.nil) ⟨262660, 268418, 6440610⟩ (CTN.node CTN.nil ⟨262660, 268514, 6431398⟩ CTN.nil))))))))

noncomputable def tab26 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262660, 270336, 6259631⟩ CTN.nil) ⟨262661, 266372, 6691093⟩ CTN.nil) ⟨262662, 269220, 6460461⟩ (CTN.node (CTN.node CTN.nil ⟨262667, 265641, 7073378⟩ CTN.nil) ⟨262668, 270336, 6642822⟩ CTN.nil)) ⟨262674, 270192, 6952509⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262676, 268562, 7225350⟩ CTN.nil) ⟨262683, 266057, 7879552⟩ CTN.nil) ⟨262683, 266073, 7877655⟩ (CTN.node CTN.nil ⟨262692, 268746, 8048624⟩ CTN.nil))) ⟨262693, 266436, 8387769⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262694, 266453, 8441950⟩ CTN.nil) ⟨262696, 267686, 8398505⟩ CTN.nil) ⟨262696, 270336, 8073767⟩ (CTN.node (CTN.node CTN.nil ⟨262697, 266551, 8599385⟩ CTN.nil) ⟨262699, 266073, 8776395⟩ CTN.nil)) ⟨262699, 266089, 8774282⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262712, 270336, 8954164⟩ CTN.nil) ⟨262713, 266151, 9591407⟩ CTN.nil) ⟨262720, 270336, 9411469⟩ (CTN.node CTN.nil ⟨262726, 266453, 10343986⟩ CTN.nil)))) ⟨262728, 268454, 10160381⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262728, 269414, 10016228⟩ CTN.nil) ⟨262728, 270246, 9893359⟩ CTN.nil) ⟨262728, 270336, 9880181⟩ (CTN.node (CTN.node CTN.nil ⟨262729, 266167, 10577592⟩ CTN.nil) ⟨262729, 266551, 10516723⟩ CTN.nil)) ⟨262730, 269510, 10122381⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262740, 267762, 11018642⟩ CTN.nil) ⟨262740, 269394, 10753855⟩ CTN.nil) ⟨262740, 270336, 10604637⟩ (CTN.node CTN.nil ⟨262745, 266135, 11620234⟩ CTN.nil))) ⟨262745, 267270, 11423951⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262748, 270336, 11101868⟩ CTN.nil) ⟨262756, 270336, 11610509⟩ CTN.nil) ⟨262757, 266468, 12368216⟩ (CTN.node (CTN.node CTN.nil ⟨262760, 267750, 12334690⟩ CTN.nil) ⟨262760, 269318, 12049721⟩ CTN.nil)) ⟨262760, 270336, 11869108⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262761, 266151, 12703315⟩ CTN.nil) ⟨262761, 266583, 12621109⟩ CTN.nil) ⟨262762, 269542, 12141599⟩ (CTN.node CTN.nil ⟨262764, 266138, 12914851⟩ CTN.nil))))) ⟨262772, 269458, 12827986⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262772, 270322, 12664647⟩ CTN.nil) ⟨262776, 270336, 12932032⟩ CTN.nil) ⟨262777, 266599, 13744927⟩ (CTN.node (CTN.node CTN.nil ⟨262777, 267270, 13607311⟩ CTN.nil) ⟨262780, 266154, 14055264⟩ CTN.nil)) ⟨262788, 270336, 13759183⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262790, 270336, 13899538⟩ CTN.nil) ⟨262792, 267782, 14584390⟩ CTN.nil) ⟨262792, 270246, 14059333⟩ (CTN.node CTN.nil ⟨262794, 267974, 14689456⟩ CTN.nil))) ⟨262794, 270336, 14182388⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262798, 268084, 14960776⟩ CTN.nil) ⟨262798, 269684, 14608620⟩ CTN.nil) ⟨262804, 270336, 14901998⟩ (CTN.node (CTN.node CTN.nil ⟨262805, 266564, 15841382⟩ CTN.nil) ⟨262806, 268860, 15381489⟩ CTN.nil)) ⟨262807, 266534, 16003481⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262816, 270336, 15789073⟩ CTN.nil) ⟨262820, 268842, 16451408⟩ CTN.nil) ⟨262820, 269674, 16249171⟩ (CTN.node CTN.nil ⟨262821, 266580, 17097532⟩ CTN.nil)))) ⟨262821, 267156, 16950444⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262822, 267780, 16871799⟩ CTN.nil) ⟨262822, 269412, 16466384⟩ CTN.nil) ⟨262824, 270336, 16394726⟩ (CTN.node (CTN.node CTN.nil ⟨262826, 266216, 17597161⟩ CTN.nil) ⟨262826, 267319, 17308300⟩ CTN.nil)) ⟨262826, 270336, 16547923⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262828, 268082, 17271100⟩ CTN.nil) ⟨262832, 270336, 17011796⟩ CTN.nil) ⟨262834, 270336, 17167848⟩ (CTN.node CTN.nil ⟨262836, 267826, 17983752⟩ CTN.nil))) ⟨262836, 268594, 17778792⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262836, 269458, 17551691⟩ CTN.nil) ⟨262836, 270336, 17324613⟩ CTN.nil) ⟨262837, 266564, 18410207⟩ (CTN.node CTN.nil ⟨262837, 267140, 18251817⟩ CTN.nil)) ⟨262838, 267828, 18146680⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262838, 267860, 18138003⟩ CTN.nil) ⟨262838, 268692, 17914221⟩ CTN.nil) ⟨262839, 266598, 18567692⟩ (CTN.node CTN.nil ⟨262840, 270336, 17640284⟩ CTN.nil)))))) ⟨262842, 266232, 18923211⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262848, 270336, 18280189⟩ CTN.nil) ⟨262852, 268578, 19096708⟩ CTN.nil) ⟨262852, 268674, 19069408⟩ (CTN.node (CTN.node CTN.nil ⟨262852, 269410, 18861722⟩ CTN.nil) ⟨262852, 270336, 18604423⟩ CTN.nil)) ⟨262854, 267812, 19485728⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262854, 267844, 19476411⟩ CTN.nil) ⟨262854, 268676, 19236101⟩ CTN.nil) ⟨262854, 269508, 18999486⟩ (CTN.node CTN.nil ⟨262856, 270336, 18931512⟩ CTN.nil))) ⟨262858, 266248, 20297168⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262858, 266296, 20282526⟩ CTN.nil) ⟨262858, 266680, 20165868⟩ CTN.nil) ⟨262858, 268070, 19750539⟩ (CTN.node (CTN.node CTN.nil ⟨262858, 268806, 19534954⟩ CTN.nil) ⟨262858, 269734, 19267304⟩ CTN.nil)) ⟨262858, 270336, 19096127⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262860, 270336, 19261456⟩ CTN.nil) ⟨262868, 270336, 19929908⟩ CTN.nil) ⟨262870, 267796, 20872851⟩ (CTN.node CTN.nil ⟨262870, 269556, 20332628⟩ CTN.nil)))) ⟨262874, 265896, 21839579⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262874, 266312, 21703334⟩ CTN.nil) ⟨262890, 266328, 23171952⟩ CTN.nil) ⟨262890, 266744, 23027628⟩ (CTN.node (CTN.node CTN.nil ⟨262890, 268070, 22575035⟩ CTN.nil) ⟨262890, 268102, 22564251⟩ CTN.nil)) ⟨262890, 268934, 22286108⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262890, 270336, 21827036⟩ CTN.nil) ⟨262892, 270336, 22003785⟩ CTN.nil) ⟨262900, 270336, 22717919⟩ (CTN.node CTN.nil ⟨262902, 269268, 23263965⟩ CTN.nil))) ⟨262903, 266630, 24294688⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262906, 268822, 23789881⟩ CTN.nil) ⟨262912, 270336, 23810535⟩ CTN.nil) ⟨262916, 270336, 24180451⟩ (CTN.node (CTN.node CTN.nil ⟨262918, 266645, 25744982⟩ CTN.nil) ⟨262918, 267876, 25274644⟩ CTN.nil)) ⟨262918, 267908, 25262562⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262918, 268644, 24986644⟩ CTN.nil) ⟨262920, 270336, 24553223⟩ CTN.nil) ⟨262922, 265896, 26436365⟩ (CTN.node CTN.nil ⟨262922, 266312, 26271443⟩ CTN.nil))))) ⟨262922, 267415, 25840346⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262922, 268102, 25576303⟩ CTN.nil) ⟨262922, 268870, 25285110⟩ CTN.nil) ⟨262922, 270336, 24740680⟩ (CTN.node (CTN.node CTN.nil ⟨262924, 270336, 24928851⟩ CTN.nil) ⟨262928, 270336, 25307334⟩ CTN.nil)) ⟨262934, 268628, 26545436⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262934, 268692, 26520135⟩ CTN.nil) ⟨262934, 269460, 26218855⟩ CTN.nil) ⟨262934, 269556, 26181496⟩ (CTN.node CTN.nil ⟨262936, 270336, 26072867⟩ CTN.nil))) ⟨262938, 265912, 28059505⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262938, 266312, 27891174⟩ CTN.nil) ⟨262950, 266709, 28964580⟩ CTN.nil) ⟨262950, 267972, 28421958⟩ (CTN.node (CTN.node CTN.nil ⟨262950, 268676, 28125013⟩ CTN.nil) ⟨262950, 269636, 27726309⟩ CTN.nil)) ⟨262950, 270336, 27440036⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262952, 270336, 27638201⟩ CTN.nil) ⟨262954, 266328, 29552317⟩ CTN.nil) ⟨262954, 266776, 29354155⟩ (CTN.node CTN.nil ⟨262956, 270336, 28036674⟩ CTN.nil)))) ⟨262962, 270336, 28639739⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262964, 269682, 29123197⟩ CTN.nil) ⟨262964, 270336, 28842189⟩ CTN.nil) ⟨262966, 269268, 29509262⟩ (CTN.node (CTN.node CTN.nil ⟨262968, 270336, 29249229⟩ CTN.nil) ⟨262970, 268118, 30441359⟩ CTN.nil)) ⟨262976, 270336, 30071879⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨262980, 270336, 30487487⟩ CTN.nil) ⟨262982, 267972, 31794811⟩ CTN.nil) ⟨262982, 268740, 31432644⟩ (CTN.node CTN.nil ⟨262984, 270336, 30905952⟩ CTN.nil))) ⟨262986, 270336, 31116255⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨262998, 268020, 33528185⟩ CTN.nil) ⟨262998, 268052, 33512166⟩ CTN.nil) ⟨262998, 268884, 33098994⟩ (CTN.node CTN.nil ⟨263002, 270336, 32824386⟩ CTN.nil)) ⟨263008, 270336, 33476716⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263010, 269864, 33932121⟩ CTN.nil) ⟨263010, 270336, 33695587⟩ CTN.nil) ⟨263012, 269066, 34560530⟩ (CTN.node CTN.nil ⟨263012, 269898, 34136029⟩ CTN.nil))))))) ⟨263014, 266741, 36014708⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263014, 267317, 35705065⟩ CTN.nil) ⟨263019, 266041, 36986087⟩ CTN.nil) ⟨263019, 266841, 36544198⟩ (CTN.node (CTN.node CTN.nil ⟨263019, 266873, 36526660⟩ CTN.nil) ⟨263019, 267480, 36195972⟩ CTN.nil)) ⟨263020, 268306, 35866684⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263020, 269074, 35458640⟩ CTN.nil) ⟨263026, 269648, 35835949⟩ CTN.nil) ⟨263026, 270336, 35472262⟩ (CTN.node CTN.nil ⟨263028, 268050, 36931920⟩ CTN.nil))) ⟨263028, 268818, 36511359⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263028, 269682, 36045359⟩ CTN.nil) ⟨263028, 270336, 35697559⟩ CTN.nil) ⟨263030, 269748, 36238058⟩ (CTN.node (CTN.node CTN.nil ⟨263035, 266409, 38693101⟩ CTN.nil) ⟨263035, 266857, 38433725⟩ CTN.nil)) ⟨263035, 266889, 38415281⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263035, 267528, 38049292⟩ CTN.nil) ⟨263035, 267560, 38031078⟩ CTN.nil) ⟨263042, 268864, 38118723⟩ (CTN.node CTN.nil ⟨263042, 269600, 37703863⟩ CTN.nil)))) ⟨263046, 270336, 37757365⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263048, 270336, 37989802⟩ CTN.nil) ⟨263051, 266841, 40389843⟩ CTN.nil) ⟨263052, 270336, 38456819⟩ (CTN.node (CTN.node CTN.nil ⟨263056, 270336, 38926691⟩ CTN.nil) ⟨263058, 270336, 39162698⟩ CTN.nil)) ⟨263064, 270336, 39875004⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263072, 270336, 40834740⟩ CTN.nil) ⟨263076, 270336, 41318892⟩ CTN.nil) ⟨263080, 269670, 42220732⟩ (CTN.node CTN.nil ⟨263080, 270336, 41805899⟩ CTN.nil))) ⟨263082, 270336, 42050474⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263084, 270336, 42295762⟩ CTN.nil) ⟨263086, 268340, 43822691⟩ CTN.nil) ⟨263092, 270336, 43284056⟩ (CTN.node (CTN.node CTN.nil ⟨263094, 268884, 44481605⟩ CTN.nil) ⟨263094, 269748, 43914017⟩ CTN.nil)) ⟨263096, 270336, 43782487⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263100, 268248, 45679810⟩ CTN.nil) ⟨263100, 270336, 44283773⟩ CTN.nil) ⟨263104, 270336, 44787915⟩ (CTN.node CTN.nil ⟨263108, 266851, 47709693⟩ CTN.nil))))) ⟨263108, 270336, 45294912⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263112, 270336, 45804765⟩ CTN.nil) ⟨263126, 268116, 49209549⟩ CTN.nil) ⟨263126, 268980, 48579846⟩ (CTN.node (CTN.node CTN.nil ⟨263129, 266567, 50778665⟩ CTN.nil) ⟨263132, 268280, 49898729⟩ CTN.nil)) ⟨263132, 270336, 48396860⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263142, 268100, 51400508⟩ CTN.nil) ⟨263145, 266583, 53004793⟩ CTN.nil) ⟨263148, 270336, 50521931⟩ (CTN.node CTN.nil ⟨263152, 270336, 51060337⟩ CTN.nil))) ⟨263156, 270336, 51601597⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263158, 270336, 51873298⟩ CTN.nil) ⟨263164, 269080, 53684167⟩ CTN.nil) ⟨263164, 269912, 53024808⟩ (CTN.node (CTN.node CTN.nil ⟨263164, 270336, 52692683⟩ CTN.nil) ⟨263174, 268996, 55158944⟩ CTN.nil)) ⟨263174, 269828, 54481261⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263174, 270336, 54072598⟩ CTN.nil) ⟨263176, 270336, 54350722⟩ CTN.nil) ⟨263177, 266151, 58001717⟩ (CTN.node CTN.nil ⟨263177, 266567, 57640221⟩ CTN.nil)))) ⟨263180, 268360, 56545542⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263180, 268392, 56518559⟩ CTN.nil) ⟨263180, 269224, 55822619⟩ CTN.nil) ⟨263186, 270336, 55752046⟩ (CTN.node (CTN.node CTN.nil ⟨263188, 270336, 56034452⟩ CTN.nil) ⟨263190, 270336, 56317571⟩ CTN.nil)) ⟨263192, 268150, 58471216⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263192, 270336, 56601404⟩ CTN.nil) ⟨263193, 266583, 60009619⟩ CTN.nil) ⟨263196, 268344, 58889112⟩ (CTN.node CTN.nil ⟨263196, 269112, 58219245⟩ CTN.nil))) ⟨263203, 267522, 60663769⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263204, 270336, 58319386⟩ CTN.nil) ⟨263206, 268164, 60531668⟩ CTN.nil) ⟨263206, 268196, 60502762⟩ (CTN.node CTN.nil ⟨263206, 268932, 59842657⟩ CTN.nil)) ⟨263208, 268614, 60423798⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263208, 270336, 58897755⟩ CTN.nil) ⟨263212, 268392, 61222375⟩ CTN.nil) ⟨263212, 270336, 59478978⟩ (CTN.node CTN.nil ⟨263220, 270336, 60649986⟩ CTN.nil)))))) ⟨263222, 268212, 62899569⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263222, 268980, 62183732⟩ CTN.nil) ⟨263222, 269272, 61914239⟩ CTN.nil) ⟨263224, 270336, 61239770⟩ (CTN.node (CTN.node CTN.nil ⟨263228, 269144, 62935926⟩ CTN.nil) ⟨263228, 269976, 62163117⟩ CTN.nil)) ⟨263228, 270336, 61832408⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263232, 270336, 62427899⟩ CTN.nil) ⟨263234, 270336, 62726715⟩ CTN.nil) ⟨263236, 270336, 63026244⟩ (CTN.node CTN.nil ⟨263237, 266948, 66447615⟩ CTN.nil))) ⟨263238, 268196, 65373556⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263238, 270336, 63326487⟩ CTN.nil) ⟨263240, 268230, 65650918⟩ CTN.nil) ⟨263240, 270336, 63627443⟩ (CTN.node (CTN.node CTN.nil ⟨263246, 268532, 66287650⟩ CTN.nil) ⟨263250, 270336, 65142921⟩ CTN.nil)) ⟨263254, 270336, 65754105⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263256, 268982, 67402003⟩ CTN.nil) ⟨263256, 269814, 66573859⟩ CTN.nil) ⟨263258, 266648, 70119675⟩ (CTN.node CTN.nil ⟨263260, 269176, 67833906⟩ CTN.nil)))) ⟨263268, 270336, 67915716⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263269, 267012, 71527600⟩ CTN.nil) ⟨263270, 269028, 69564960⟩ CTN.nil) ⟨263270, 269124, 69465680⟩ (CTN.node (CTN.node CTN.nil ⟨263270, 269956, 68612627⟩ CTN.nil) ⟨263274, 266664, 72727329⟩ CTN.nil)) ⟨263274, 266712, 72674948⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263276, 269224, 70317318⟩ CTN.nil) ⟨263276, 270336, 69166611⟩ CTN.nil) ⟨263284, 270336, 70428916⟩ (CTN.node CTN.nil ⟨263286, 268308, 72911232⟩ CTN.nil))) ⟨263286, 268340, 72876433⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263286, 269172, 71978898⟩ CTN.nil) ⟨263288, 270336, 71064346⟩ CTN.nil) ⟨263290, 266312, 75799769⟩ (CTN.node CTN.nil ⟨263290, 266680, 75381921⟩ CTN.nil)) ⟨263290, 266728, 75327632⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263292, 270336, 71702629⟩ CTN.nil) ⟨263300, 270336, 72987749⟩ CTN.nil) ⟨263302, 268292, 75572287⟩ (CTN.node CTN.nil ⟨263302, 269060, 74712481⟩ CTN.nil))))) ⟨263304, 270336, 73634587⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263306, 266744, 78027180⟩ CTN.nil) ⟨263314, 269936, 75711598⟩ CTN.nil) ⟨263316, 268306, 77907784⟩ (CTN.node (CTN.node CTN.nil ⟨263316, 270336, 75592208⟩ CTN.nil) ⟨263318, 269204, 77207007⟩ CTN.nil)) ⟨263318, 270336, 75920973⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263320, 270336, 76250451⟩ CTN.nil) ⟨263332, 267043, 82176628⟩ CTN.nil) ⟨263332, 268290, 80658292⟩ (CTN.node CTN.nil ⟨263332, 270336, 78242285⟩ CTN.nil))) ⟨263333, 267044, 82350943⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263336, 269094, 80380024⟩ CTN.nil) ⟨263340, 270336, 79584427⟩ CTN.nil) ⟨263348, 268370, 83337697⟩ (CTN.node (CTN.node CTN.nil ⟨263348, 269202, 82311436⟩ CTN.nil) ⟨263348, 270336, 80937970⟩ CTN.nil)) ⟨263352, 270336, 81619017⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263354, 266328, 87010772⟩ CTN.nil) ⟨263354, 266728, 86489602⟩ CTN.nil) ⟨263354, 266744, 86468837⟩ (CTN.node CTN.nil ⟨263356, 270336, 82302914⟩ CTN.nil)))) ⟨263360, 270336, 82989660⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263364, 267107, 87802727⟩ CTN.nil) ⟨263364, 268354, 86180825⟩ CTN.nil) ⟨263364, 270336, 83679256⟩ (CTN.node (CTN.node CTN.nil ⟨263368, 269316, 85658138⟩ CTN.nil) ⟨263368, 270244, 84486738⟩ CTN.nil)) ⟨263368, 270336, 84371702⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263370, 266744, 89378945⟩ CTN.nil) ⟨263370, 266760, 89357487⟩ CTN.nil) ⟨263380, 270336, 86466133⟩ (CTN.node CTN.nil ⟨263381, 267140, 90866337⟩ CTN.nil))) ⟨263382, 268404, 89346432⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263382, 269172, 88330336⟩ CTN.nil) ⟨263382, 270336, 86817698⟩ CTN.nil) ⟨263384, 267238, 91286108⟩ (CTN.node CTN.nil ⟨263396, 268354, 91968148⟩ CTN.nil)) ⟨263396, 269122, 90922043⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263396, 270336, 89298592⟩ CTN.nil) ⟨263397, 267156, 93817393⟩ CTN.nil) ⟨263400, 266838, 94831174⟩ (CTN.node CTN.nil ⟨263400, 268580, 92392894⟩ CTN.nil))))))))

noncomputable def tab27 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263400, 269444, 91212631⟩ CTN.nil) ⟨263400, 270180, 90222056⟩ CTN.nil) ⟨263404, 270336, 90731910⟩ (CTN.node (CTN.node CTN.nil ⟨263406, 268660, 93388183⟩ CTN.nil) ⟨263408, 270336, 91452842⟩ CTN.nil)) ⟨263412, 268402, 94864273⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263412, 269170, 93785418⟩ CTN.nil) ⟨263412, 270336, 92176621⟩ CTN.nil) ⟨263413, 267140, 96861232⟩ (CTN.node CTN.nil ⟨263416, 267238, 97290103⟩ CTN.nil))) ⟨263416, 270336, 92903247⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263418, 270300, 93317363⟩ CTN.nil) ⟨263420, 270336, 93632721⟩ CTN.nil) ⟨263428, 268386, 97896466⟩ (CTN.node (CTN.node CTN.nil ⟨263428, 270336, 95100210⟩ CTN.nil) ⟨263432, 268612, 98324328⟩ CTN.nil)) ⟨263432, 270336, 95838225⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263440, 270336, 97322795⟩ CTN.nil) ⟨263444, 268370, 100977003⟩ CTN.nil) ⟨263448, 267270, 103435344⟩ (CTN.node CTN.nil ⟨263448, 270336, 98818749⟩ CTN.nil)))) ⟨263451, 266825, 104721836⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263464, 268644, 104436912⟩ CTN.nil) ⟨263464, 270336, 101844808⟩ CTN.nil) ⟨263470, 269492, 104288566⟩ (CTN.node (CTN.node CTN.nil ⟨263476, 270336, 104144227⟩ CTN.nil) ⟨263478, 269500, 105834005⟩ CTN.nil)) ⟨263480, 270336, 104916390⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263488, 270336, 106469248⟩ CTN.nil) ⟨263492, 268514, 110192916⟩ CTN.nil) ⟨263492, 269250, 108992091⟩ (CTN.node CTN.nil ⟨263492, 269346, 108836671⟩ CTN.nil))) ⟨263492, 270336, 107249943⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263494, 267221, 112752851⟩ CTN.nil) ⟨263496, 270336, 108033482⟩ CTN.nil) ⟨263497, 267319, 113202967⟩ (CTN.node (CTN.node CTN.nil ⟨263500, 270336, 108819864⟩ CTN.nil) ⟨263508, 268530, 113403551⟩ CTN.nil)) ⟨263508, 269394, 111954621⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263513, 266903, 117242511⟩ CTN.nil) ⟨263520, 270336, 112794423⟩ CTN.nil) ⟨263524, 268514, 116715025⟩ (CTN.node CTN.nil ⟨263526, 267285, 119299703⟩ CTN.nil))))) ⟨263526, 270084, 114427032⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263528, 268518, 117536422⟩ CTN.nil) ⟨263529, 266919, 120593030⟩ CTN.nil) ⟨263529, 267351, 119814883⟩ (CTN.node (CTN.node CTN.nil ⟨263529, 267383, 119757492⟩ CTN.nil) ⟨263540, 268594, 119903103⟩ CTN.nil)) ⟨263540, 269426, 118427782⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263540, 270336, 116840040⟩ CTN.nil) ⟨263542, 270336, 117248509⟩ CTN.nil) ⟨263544, 270336, 117657688⟩ (CTN.node CTN.nil ⟨263545, 266983, 123900558⟩ CTN.nil))) ⟨263545, 268038, 121959886⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263545, 268070, 121901618⟩ CTN.nil) ⟨263556, 270336, 120127676⟩ CTN.nil) ⟨263560, 268550, 124209103⟩ (CTN.node (CTN.node CTN.nil ⟨263560, 270246, 121118016⟩ CTN.nil) ⟨263561, 266999, 127340997⟩ CTN.nil)) ⟨263561, 267415, 126549859⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263566, 268852, 124928194⟩ CTN.nil) ⟨263568, 270336, 122623228⟩ CTN.nil) ⟨263572, 270336, 123460758⟩ (CTN.node CTN.nil ⟨263576, 270336, 124301127⟩ CTN.nil)))) ⟨263577, 268102, 128717081⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263588, 270336, 126839270⟩ CTN.nil) ⟨263590, 267317, 133116576⟩ CTN.nil) ⟨263590, 270180, 127559178⟩ (CTN.node (CTN.node CTN.nil ⟨263592, 270336, 127690994⟩ CTN.nil) ⟨263593, 266567, 135298755⟩ CTN.nil)) ⟨263593, 267415, 133589421⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263594, 270336, 128117921⟩ CTN.nil) ⟨263596, 268850, 131413388⟩ CTN.nil) ⟨263596, 270336, 128545557⟩ (CTN.node CTN.nil ⟨263604, 268594, 133678158⟩ CTN.nil))) ⟨263604, 268626, 133614424⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263604, 269394, 132096138⟩ CTN.nil) ⟨263604, 270336, 130263196⟩ CTN.nil) ⟨263605, 267908, 135277074⟩ (CTN.node CTN.nil ⟨263608, 270336, 131126271⟩ CTN.nil)) ⟨263609, 266999, 138037947⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263609, 267399, 137213213⟩ CTN.nil) ⟨263609, 268102, 135778614⟩ CTN.nil) ⟨263620, 270336, 133732520⟩ (CTN.node CTN.nil ⟨263624, 269382, 136525349⟩ CTN.nil)))))) ⟨263624, 270336, 134606943⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263625, 266999, 141699035⟩ CTN.nil) ⟨263625, 267447, 140751259⟩ CTN.nil) ⟨263626, 270336, 135045218⟩ (CTN.node (CTN.node CTN.nil ⟨263630, 269684, 137244122⟩ CTN.nil) ⟨263636, 270322, 137275683⟩ CTN.nil)) ⟨263636, 270336, 137247228⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263637, 267396, 143619398⟩ CTN.nil) ⟨263637, 267972, 142387616⟩ CTN.nil) ⟨263638, 269692, 139010627⟩ (CTN.node CTN.nil ⟨263641, 268134, 142959537⟩ CTN.nil))) ⟨263652, 269674, 142196065⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263652, 270336, 140807301⟩ CTN.nil) ⟨263656, 270246, 141893408⟩ CTN.nil) ⟨263658, 268838, 145351423⟩ (CTN.node (CTN.node CTN.nil ⟨263660, 269682, 143993733⟩ CTN.nil) ⟨263664, 270336, 143507116⟩ CTN.nil)) ⟨263668, 270336, 144412722⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263672, 270336, 145321161⟩ CTN.nil) ⟨263674, 270336, 145776443⟩ CTN.nil) ⟨263684, 269410, 150111194⟩ (CTN.node CTN.nil ⟨263684, 269506, 149897265⟩ CTN.nil)))) ⟨263684, 270336, 148063475⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263686, 268644, 152303140⟩ CTN.nil) ⟨263686, 268676, 152230539⟩ CTN.nil) ⟨263686, 269508, 150358020⟩ (CTN.node (CTN.node CTN.nil ⟨263686, 270276, 148655033⟩ CTN.nil) ⟨263690, 268870, 152732780⟩ CTN.nil)) ⟨263690, 268902, 152660035⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263690, 269734, 150783802⟩ CTN.nil) ⟨263690, 270336, 149444190⟩ CTN.nil) ⟨263696, 270336, 150831277⟩ (CTN.node CTN.nil ⟨263700, 268690, 155515426⟩ CTN.nil))) ⟨263700, 270322, 151791004⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263701, 268004, 157355746⟩ CTN.nil) ⟨263706, 266728, 161620432⟩ CTN.nil) ⟨263706, 267528, 159694425⟩ (CTN.node (CTN.node CTN.nil ⟨263706, 267560, 159617983⟩ CTN.nil) ⟨263706, 268854, 156564832⟩ CTN.nil)) ⟨263716, 268674, 159387370⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263716, 270274, 155643741⟩ CTN.nil) ⟨263716, 270336, 155500900⟩ CTN.nil) ⟨263720, 270336, 156443315⟩ (CTN.node CTN.nil ⟨263722, 267512, 163652359⟩ CTN.nil))))) ⟨263722, 268902, 160292204⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263722, 268934, 160215868⟩ CTN.nil) ⟨263722, 269766, 158247004⟩ CTN.nil) ⟨263722, 270336, 156915583⟩ (CTN.node (CTN.node CTN.nil ⟨263736, 270336, 160241266⟩ CTN.nil) ⟨263738, 268886, 164216771⟩ CTN.nil)) ⟨263738, 269654, 162352538⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263738, 270336, 160719192⟩ CTN.nil) ⟨263744, 270336, 162157212⟩ CTN.nil) ⟨263750, 268740, 167525731⟩ (CTN.node CTN.nil ⟨263750, 269988, 164447353⟩ CTN.nil))) ⟨263752, 270336, 164084468⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263754, 268934, 168029283⟩ CTN.nil) ⟨263754, 269702, 166122108⟩ CTN.nil) ⟨263760, 270336, 166023033⟩ (CTN.node (CTN.node CTN.nil ⟨263764, 270336, 166996555⟩ CTN.nil) ⟨263770, 269686, 170093357⟩ CTN.nil)) ⟨263770, 270336, 168462136⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263776, 270336, 169934075⟩ CTN.nil) ⟨263780, 270336, 170918899⟩ CTN.nil) ⟨263782, 268772, 175440216⟩ (CTN.node CTN.nil ⟨263782, 268804, 175356627⟩ CTN.nil)))) ⟨263782, 269508, 173530186⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263782, 269636, 173200665⟩ CTN.nil) ⟨263782, 270336, 171412370⟩ CTN.nil) ⟨263786, 269734, 173946831⟩ (CTN.node (CTN.node CTN.nil ⟨263788, 269074, 176166038⟩ CTN.nil) ⟨263790, 270336, 173393317⟩ CTN.nil)) ⟨263796, 268818, 178873339⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263796, 270336, 174886439⟩ CTN.nil) ⟨263798, 268756, 179549549⟩ CTN.nil) ⟨263798, 270336, 175385558⟩ (CTN.node CTN.nil ⟨263800, 270336, 175885384⟩ CTN.nil))) ⟨263802, 269718, 178009295⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263802, 270336, 176385914⟩ CTN.nil) ⟨263806, 270336, 177389093⟩ CTN.nil) ⟨263812, 270336, 178899154⟩ (CTN.node CTN.nil ⟨263814, 270336, 179403918⟩ CTN.nil)) ⟨263816, 267254, 188359493⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263816, 270336, 179909388⟩ CTN.nil) ⟨263818, 269766, 181946381⟩ CTN.nil) ⟨263818, 270336, 180415564⟩ (CTN.node CTN.nil ⟨263824, 270336, 181938323⟩ CTN.nil))))))) ⟨263828, 270336, 182957022⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263832, 270336, 183978541⟩ CTN.nil) ⟨263844, 269898, 188278161⟩ CTN.nil) ⟨263844, 270336, 187060021⟩ (CTN.node (CTN.node CTN.nil ⟨263846, 269604, 189623061⟩ CTN.nil) ⟨263848, 270336, 188092819⟩ CTN.nil)) ⟨263852, 269906, 190337463⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263860, 270336, 191208128⟩ CTN.nil) ⟨263864, 270336, 192252201⟩ CTN.nil) ⟨263868, 270336, 193299091⟩ (CTN.node CTN.nil ⟨263872, 270336, 194348798⟩ CTN.nil))) ⟨263874, 269696, 196732479⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263874, 270336, 194874708⟩ CTN.nil) ⟨263876, 270336, 195401322⟩ CTN.nil) ⟨263878, 270336, 195928640⟩ (CTN.node (CTN.node CTN.nil ⟨263880, 270336, 196456662⟩ CTN.nil) ⟨263890, 270336, 199107333⟩ CTN.nil)) ⟨263892, 268914, 203899137⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263892, 269682, 201584659⟩ CTN.nil) ⟨263892, 270336, 199639579⟩ CTN.nil) ⟨263906, 268864, 207879152⟩ (CTN.node CTN.nil ⟨263906, 269632, 205519060⟩ CTN.nil)))) ⟨263908, 267619, 212337602⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263910, 270336, 204461452⟩ CTN.nil) ⟨263912, 270336, 205000733⟩ CTN.nil) ⟨263924, 270336, 208251186⟩ (CTN.node (CTN.node CTN.nil ⟨263928, 270336, 209340294⟩ CTN.nil) ⟨263932, 270336, 210432214⟩ CTN.nil)) ⟨263936, 270336, 211526945⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263940, 267683, 221186460⟩ CTN.nil) ⟨263940, 270336, 212624487⟩ CTN.nil) ⟨263942, 270336, 213174312⟩ (CTN.node CTN.nil ⟨263944, 270336, 213724839⟩ CTN.nil))) ⟨263945, 267335, 223780054⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263948, 270336, 214828001⟩ CTN.nil) ⟨263950, 270336, 215380636⟩ CTN.nil) ⟨263954, 270224, 216847416⟩ (CTN.node (CTN.node CTN.nil ⟨263956, 270336, 217042754⟩ CTN.nil) ⟨263958, 270336, 217598198⟩ CTN.nil)) ⟨263960, 270336, 218154344⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263961, 267351, 228360205⟩ CTN.nil) ⟨263961, 267399, 228196156⟩ CTN.nil) ⟨263964, 270336, 219268742⟩ (CTN.node CTN.nil ⟨263966, 270336, 219826994⟩ CTN.nil))))) ⟨263970, 270176, 221469841⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨263972, 270336, 221505961⟩ CTN.nil) ⟨263974, 268932, 226744336⟩ CTN.nil) ⟨263974, 270336, 222067021⟩ (CTN.node (CTN.node CTN.nil ⟨263976, 270336, 222628782⟩ CTN.nil) ⟨263977, 267415, 232817754⟩ CTN.nil)) ⟨263980, 270002, 224864457⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨263980, 270336, 223754410⟩ CTN.nil) ⟨263984, 270336, 224882843⟩ CTN.nil) ⟨263988, 270336, 226014083⟩ (CTN.node CTN.nil ⟨263990, 268980, 231187919⟩ CTN.nil))) ⟨263996, 270336, 228284978⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264003, 268290, 237391962⟩ CTN.nil) ⟨264004, 270336, 230567093⟩ CTN.nil) ⟨264006, 268964, 235895396⟩ (CTN.node (CTN.node CTN.nil ⟨264006, 270336, 231139374⟩ CTN.nil) ⟨264008, 270336, 231712356⟩ CTN.nil)) ⟨264028, 269944, 238864190⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264034, 270336, 239224881⟩ CTN.nil) ⟨264035, 268354, 246676458⟩ CTN.nil) ⟨264036, 270336, 239807670⟩ (CTN.node CTN.nil ⟨264041, 267415, 251991495⟩ CTN.nil)))) ⟨264041, 267431, 251931149⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264052, 270336, 244495182⟩ CTN.nil) ⟨264060, 270336, 246855732⟩ CTN.nil) ⟨264068, 270336, 249227474⟩ (CTN.node (CTN.node CTN.nil ⟨264070, 269060, 254598645⟩ CTN.nil) ⟨264070, 269796, 251829762⟩ CTN.nil)) ⟨264071, 267925, 259252097⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264072, 270336, 250417540⟩ CTN.nil) ⟨264080, 270336, 252806061⟩ CTN.nil) ⟨264086, 269844, 256468129⟩ (CTN.node CTN.nil ⟨264086, 270336, 254604791⟩ CTN.nil))) ⟨264087, 268612, 261517588⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264088, 270336, 255205765⟩ CTN.nil) ⟨264102, 270336, 259432142⟩ CTN.nil) ⟨264104, 270336, 260038704⟩ (CTN.node CTN.nil ⟨264114, 270336, 263081985⟩ CTN.nil)) ⟨264116, 270336, 263692735⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264120, 270336, 264916328⟩ CTN.nil) ⟨264124, 270336, 266142713⟩ CTN.nil) ⟨264132, 270336, 268603853⟩ (CTN.node CTN.nil ⟨264134, 269892, 270998171⟩ CTN.nil)))))) ⟨264136, 270336, 269838607⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264150, 269172, 278959328⟩ CTN.nil) ⟨264150, 270036, 275403578⟩ CTN.nil) ⟨264156, 270336, 276054207⟩ (CTN.node (CTN.node CTN.nil ⟨264162, 270336, 277932474⟩ CTN.nil) ⟨264164, 269122, 283624187⟩ CTN.nil)) ⟨264164, 270336, 278559957⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264166, 269924, 280897882⟩ CTN.nil) ⟨264166, 270336, 279188135⟩ CTN.nil) ⟨264168, 269348, 283948371⟩ (CTN.node CTN.nil ⟨264168, 270336, 279817010⟩ CTN.nil))) ⟨264170, 270336, 280446582⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264172, 270226, 281535138⟩ CTN.nil) ⟨264172, 270336, 281076849⟩ CTN.nil) ⟨264178, 270336, 282971829⟩ (CTN.node (CTN.node CTN.nil ⟨264180, 269170, 288554754⟩ CTN.nil) ⟨264180, 269202, 288417474⟩ CTN.nil)) ⟨264180, 270034, 284876670⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264180, 270336, 283604880⟩ CTN.nil) ⟨264182, 270336, 284238628⟩ CTN.nil) ⟨264184, 268006, 294917242⟩ (CTN.node CTN.nil ⟨264184, 270336, 284873072⟩ CTN.nil)))) ⟨264188, 270336, 286144047⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264194, 270336, 288055726⟩ CTN.nil) ⟨264196, 269154, 293802949⟩ CTN.nil) ⟨264196, 269186, 293663163⟩ (CTN.node (CTN.node CTN.nil ⟨264196, 270018, 290057747⟩ CTN.nil) ⟨264196, 270336, 288694344⟩ CTN.nil)) ⟨264200, 269380, 294115084⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264200, 270336, 289973665⟩ CTN.nil) ⟨264212, 269138, 299098936⟩ CTN.nil) ⟨264212, 270336, 293828315⟩ (CTN.node CTN.nil ⟨264213, 267972, 304676645⟩ CTN.nil))) ⟨264216, 268070, 305232291⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264216, 270336, 295118758⟩ CTN.nil) ⟨264232, 269412, 304452538⟩ CTN.nil) ⟨264232, 269444, 304307824⟩ (CTN.node CTN.nil ⟨264232, 270180, 301003021⟩ CTN.nil)) ⟨264232, 270276, 300575274⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264232, 270336, 300308319⟩ CTN.nil) ⟨264240, 270336, 302919764⟩ CTN.nil) ⟨264246, 270036, 306243776⟩ (CTN.node CTN.nil ⟨264246, 270336, 304885635⟩ CTN.nil))))) ⟨264248, 270336, 305542313⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264256, 270336, 308175963⟩ CTN.nil) ⟨264260, 269986, 311106157⟩ CTN.nil) ⟨264260, 270336, 309496949⟩ (CTN.node (CTN.node CTN.nil ⟨264264, 270212, 311392069⟩ CTN.nil) ⟨264264, 270336, 310820709⟩ CTN.nil)) ⟨264276, 269970, 316520530⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264276, 270034, 316220343⟩ CTN.nil) ⟨264276, 270336, 314808624⟩ CTN.nil) ⟨264280, 268102, 326821310⟩ (CTN.node CTN.nil ⟨264280, 270196, 316799701⟩ CTN.nil))) ⟨264292, 269282, 325210590⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264292, 270336, 320164641⟩ CTN.nil) ⟨264296, 268086, 332449096⟩ CTN.nil) ⟨264296, 269476, 325637608⟩ (CTN.node (CTN.node CTN.nil ⟨264296, 270244, 321948931⟩ CTN.nil) ⟨264308, 270336, 325564966⟩ CTN.nil)) ⟨264312, 269460, 331197178⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264324, 269346, 335906740⟩ CTN.nil) ⟨264324, 270178, 331785118⟩ CTN.nil) ⟨264324, 270336, 331009563⟩ (CTN.node CTN.nil ⟨264328, 270336, 332377626⟩ CTN.nil)))) ⟨264336, 270336, 335122044⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264340, 270336, 336498398⟩ CTN.nil) ⟨264352, 270336, 340644033⟩ CTN.nil) ⟨264356, 270114, 343158091⟩ (CTN.node (CTN.node CTN.nil ⟨264360, 270336, 343421596⟩ CTN.nil) ⟨264372, 269394, 352499861⟩ CTN.nil)) ⟨264372, 269426, 352332298⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264372, 270258, 348010407⟩ CTN.nil) ⟨264372, 270336, 347608637⟩ CTN.nil) ⟨264376, 270336, 349009834⟩ (CTN.node CTN.nil ⟨264384, 270336, 351820500⟩ CTN.nil))) ⟨264388, 269378, 358285465⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264392, 270336, 354642191⟩ CTN.nil) ⟨264394, 270336, 355349336⟩ CTN.nil) ⟨264402, 270336, 358184803⟩ (CTN.node CTN.nil ⟨264404, 270336, 358895391⟩ CTN.nil)) ⟨264424, 270336, 366039118⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264440, 270336, 371803611⟩ CTN.nil) ⟨264452, 270336, 376155838⟩ CTN.nil) ⟨264454, 270336, 376883613⟩ (CTN.node CTN.nil ⟨264468, 269458, 387004191⟩ CTN.nil))))))))

noncomputable def tab28 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264468, 270336, 381997252⟩ CTN.nil) ⟨264474, 269622, 388288034⟩ CTN.nil) ⟨264484, 269442, 393060064⟩ (CTN.node (CTN.node CTN.nil ⟨264488, 270336, 389360750⟩ CTN.nil) ⟨264500, 270336, 393811742⟩ CTN.nil)) ⟨264506, 269654, 400071398⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264512, 270336, 398287384⟩ CTN.nil) ⟨264516, 270336, 399784739⟩ CTN.nil) ⟨264520, 270336, 401284830⟩ (CTN.node CTN.nil ⟨264522, 269702, 405832430⟩ CTN.nil))) ⟨264538, 270336, 408069087⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264548, 270274, 412240366⟩ CTN.nil) ⟨264552, 270336, 413383993⟩ CTN.nil) ⟨264554, 269766, 417660005⟩ (CTN.node (CTN.node CTN.nil ⟨264554, 270336, 414145997⟩ CTN.nil) ⟨264564, 270336, 417966251⟩ CTN.nil)) ⟨264566, 269524, 423805099⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264568, 270336, 419499128⟩ CTN.nil) ⟨264570, 270336, 420266590⟩ CTN.nil) ⟨264576, 270336, 422573066⟩ (CTN.node CTN.nil ⟨264580, 270306, 424302579⟩ CTN.nil)))) ⟨264580, 270336, 424114125⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264592, 270336, 428753655⟩ CTN.nil) ⟨264596, 270336, 430305614⟩ CTN.nil) ⟨264600, 270336, 431860296⟩ (CTN.node (CTN.node CTN.nil ⟨264608, 270336, 434977828⟩ CTN.nil) ⟨264618, 270336, 438890049⟩ CTN.nil)) ⟨264628, 270336, 442819267⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264630, 270336, 443607150⟩ CTN.nil) ⟨264636, 270336, 445974873⟩ CTN.nil) ⟨264640, 270336, 447556751⟩ (CTN.node CTN.nil ⟨264644, 270336, 449141345⟩ CTN.nil))) ⟨264648, 270336, 450728654⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264650, 270336, 451523326⟩ CTN.nil) ⟨264660, 269682, 459944851⟩ CTN.nil) ⟨264672, 270336, 460309487⟩ (CTN.node (CTN.node CTN.nil ⟨264674, 269632, 465950614⟩ CTN.nil) ⟨264676, 270336, 461915783⟩ CTN.nil)) ⟨264690, 270336, 467559152⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264692, 270336, 468368055⟩ CTN.nil) ⟨264696, 270336, 469987892⟩ CTN.nil) ⟨264706, 270336, 474049322⟩ (CTN.node CTN.nil ⟨264716, 270336, 478127653⟩ CTN.nil))))) ⟨264720, 270336, 479763716⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264724, 270336, 481402480⟩ CTN.nil) ⟨264736, 270336, 486334977⟩ CTN.nil) ⟨264738, 270336, 487159422⟩ (CTN.node (CTN.node CTN.nil ⟨264742, 270336, 488810336⟩ CTN.nil) ⟨264752, 270336, 492949421⟩ CTN.nil)) ⟨264754, 270336, 493779261⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264756, 270336, 494609774⟩ CTN.nil) ⟨264764, 270336, 497938565⟩ CTN.nil) ⟨264770, 270336, 500442230⟩ (CTN.node CTN.nil ⟨264772, 270336, 501278131⟩ CTN.nil))) ⟨264774, 270336, 502114705⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264776, 270336, 502951953⟩ CTN.nil) ⟨264786, 270336, 507148281⟩ CTN.nil) ⟨264796, 270336, 511361420⟩ (CTN.node (CTN.node CTN.nil ⟨264800, 270336, 513051380⟩ CTN.nil) ⟨264806, 270336, 515591359⟩ CTN.nil)) ⟨264812, 270336, 518137380⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264816, 270336, 519838085⟩ CTN.nil) ⟨264836, 270336, 528381851⟩ CTN.nil) ⟨264852, 270336, 535265113⟩ (CTN.node CTN.nil ⟨264856, 270336, 536992624⟩ CTN.nil)))) ⟨264868, 270336, 542191211⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264880, 270336, 547413865⟩ CTN.nil) ⟨264892, 270336, 552660564⟩ CTN.nil) ⟨264898, 270336, 555292925⟩ (CTN.node (CTN.node CTN.nil ⟨264904, 270336, 557931289⟩ CTN.nil) ⟨264908, 270336, 559693532⟩ CTN.nil)) ⟨264914, 270336, 562341895⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨264916, 270336, 563226016⟩ CTN.nil) ⟨264948, 270336, 577462473⟩ CTN.nil) ⟨264950, 270336, 578357904⟩ (CTN.node CTN.nil ⟨264952, 270336, 579254000⟩ CTN.nil))) ⟨264964, 270336, 584644524⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨264972, 270336, 588251482⟩ CTN.nil) ⟨264978, 270336, 590963666⟩ CTN.nil) ⟨264980, 270336, 591869053⟩ (CTN.node CTN.nil ⟨264996, 270336, 599136009⟩ CTN.nil)) ⟨264998, 270336, 600047359⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265004, 270336, 602785381⟩ CTN.nil) ⟨265012, 270336, 606445338⟩ CTN.nil) ⟨265020, 270336, 610115876⟩ (CTN.node CTN.nil ⟨265024, 270336, 611955111⟩ CTN.nil)))))) ⟨265028, 270336, 613796987⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265030, 270336, 614718916⟩ CTN.nil) ⟨265032, 270336, 615641506⟩ CTN.nil) ⟨265044, 270336, 621190902⟩ (CTN.node (CTN.node CTN.nil ⟨265048, 270336, 623045979⟩ CTN.nil) ⟨265058, 270336, 627695206⟩ CTN.nil)) ⟨265060, 270336, 628627029⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265064, 270244, 631352291⟩ CTN.nil) ⟨265064, 270276, 631053119⟩ CTN.nil) ⟨265064, 270336, 630492649⟩ (CTN.node CTN.nil ⟨265080, 270228, 639002746⟩ CTN.nil))) ⟨265080, 270336, 637981464⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265092, 270336, 643625698⟩ CTN.nil) ⟨265096, 270336, 645512367⟩ CTN.nil) ⟨265108, 270336, 651188131⟩ (CTN.node (CTN.node CTN.nil ⟨265112, 270336, 653085302⟩ CTN.nil) ⟨265124, 270336, 658792554⟩ CTN.nil)) ⟨265128, 270336, 660700215⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265140, 270336, 666438912⟩ CTN.nil) ⟨265144, 270336, 668357047⟩ CTN.nil) ⟨265148, 270336, 670277799⟩ (CTN.node CTN.nil ⟨265152, 270336, 672201166⟩ CTN.nil)))) ⟨265156, 270146, 676027084⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265156, 270336, 674127148⟩ CTN.nil) ⟨265160, 270336, 676055743⟩ CTN.nil) ⟨265172, 270336, 681857204⟩ (CTN.node (CTN.node CTN.nil ⟨265184, 270336, 687682156⟩ CTN.nil) ⟨265186, 270336, 688655264⟩ CTN.nil)) ⟨265204, 270336, 697442548⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265208, 270336, 699402438⟩ CTN.nil) ⟨265216, 270336, 703330025⟩ CTN.nil) ⟨265220, 270336, 705297719⟩ (CTN.node CTN.nil ⟨265232, 270336, 711216393⟩ CTN.nil))) ⟨265236, 270336, 713194479⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265240, 270336, 715175160⟩ CTN.nil) ⟨265248, 270336, 719144305⟩ CTN.nil) ⟨265252, 270336, 721132767⟩ (CTN.node (CTN.node CTN.nil ⟨265272, 270336, 731113937⟩ CTN.nil) ⟨265280, 270336, 735124522⟩ CTN.nil)) ⟨265284, 270336, 737133693⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265300, 270336, 745196209⟩ CTN.nil) ⟨265312, 270336, 751270196⟩ CTN.nil) ⟨265316, 270336, 753300014⟩ (CTN.node CTN.nil ⟨265322, 270336, 756349573⟩ CTN.nil))))) ⟨265330, 270336, 760424664⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265346, 270336, 768605720⟩ CTN.nil) ⟨265360, 270336, 775797869⟩ CTN.nil) ⟨265380, 270336, 786126887⟩ (CTN.node (CTN.node CTN.nil ⟨265396, 270336, 794436207⟩ CTN.nil) ⟨265408, 270336, 800695052⟩ CTN.nil)) ⟨265412, 270336, 802786443⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265416, 270336, 804880387⟩ CTN.nil) ⟨265444, 270336, 819609405⟩ CTN.nil) ⟨265460, 270336, 828082002⟩ (CTN.node CTN.nil ⟨265476, 270336, 836595258⟩ CTN.nil))) ⟨265488, 270336, 843006843⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265496, 270336, 847293905⟩ CTN.nil) ⟨265508, 270336, 853743484⟩ CTN.nil) ⟨265524, 270336, 862378322⟩ (CTN.node (CTN.node CTN.nil ⟨265536, 270336, 868880963⟩ CTN.nil) ⟨265540, 270336, 871053555⟩ CTN.nil)) ⟨265544, 270336, 873228667⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265574, 270336, 889622244⟩ CTN.nil) ⟨265584, 270336, 895118185⟩ CTN.nil) ⟨265588, 270336, 897320953⟩ (CTN.node CTN.nil ⟨265600, 270336, 903944301⟩ CTN.nil)))) ⟨265602, 270336, 905050385⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265604, 270336, 906157094⟩ CTN.nil) ⟨265606, 270336, 907264430⟩ CTN.nil) ⟨265612, 270336, 910590191⟩ (CTN.node (CTN.node CTN.nil ⟨265616, 270336, 912810491⟩ CTN.nil) ⟨265618, 270336, 913921579⟩ CTN.nil)) ⟨265620, 270336, 915033292⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265634, 270336, 922832771⟩ CTN.nil) ⟨265638, 270336, 925066810⟩ CTN.nil) ⟨265648, 270336, 930662819⟩ (CTN.node CTN.nil ⟨265654, 270336, 934027900⟩ CTN.nil))) ⟨265664, 270336, 939648817⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265668, 270336, 941901538⟩ CTN.nil) ⟨265670, 270336, 943028831⟩ CTN.nil) ⟨265684, 270336, 950937272⟩ (CTN.node CTN.nil ⟨265686, 270336, 952069532⟩ CTN.nil)) ⟨265698, 270336, 958876116⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265704, 270336, 962287772⟩ CTN.nil) ⟨265724, 270336, 973700179⟩ CTN.nil) ⟨265726, 270336, 974844819⟩ (CTN.node CTN.nil ⟨265756, 270336, 992088449⟩ CTN.nil))))))) ⟨265762, 270336, 995553806⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265784, 270336, 1008307444⟩ CTN.nil) ⟨265792, 270336, 1012963544⟩ CTN.nil) ⟨265800, 270336, 1017629450⟩ (CTN.node (CTN.node CTN.nil ⟨265816, 270336, 1026990643⟩ CTN.nil) ⟨265832, 270336, 1036390949⟩ CTN.nil)) ⟨265848, 270336, 1045830294⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265858, 270336, 1051749677⟩ CTN.nil) ⟨265860, 270336, 1052935379⟩ CTN.nil) ⟨265872, 270336, 1060062349⟩ (CTN.node CTN.nil ⟨265876, 270336, 1062442864⟩ CTN.nil))) ⟨265896, 270336, 1074381823⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨265912, 270336, 1083976579⟩ CTN.nil) ⟨265920, 270336, 1088788461⟩ CTN.nil) ⟨265922, 270336, 1089992941⟩ (CTN.node (CTN.node CTN.nil ⟨265924, 270336, 1091198024⟩ CTN.nil) ⟨265928, 270336, 1093609999⟩ CTN.nil)) ⟨265938, 270336, 1099650487⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨265940, 270336, 1100860391⟩ CTN.nil) ⟨265976, 270336, 1122741476⟩ CTN.nil) ⟨265980, 270336, 1125184711⟩ (CTN.node CTN.nil ⟨265984, 270336, 1127630341⟩ CTN.nil)))) ⟨265988, 270336, 1130078366⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨266000, 270336, 1137436798⟩ CTN.nil) ⟨266024, 270336, 1152218158⟩ CTN.nil) ⟨266044, 270336, 1164601491⟩ (CTN.node (CTN.node CTN.nil ⟨266048, 270336, 1167085292⟩ CTN.nil) ⟨266080, 270336, 1187041101⟩ CTN.nil)) ⟨266112, 270336, 1207148283⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨266124, 270336, 1214727371⟩ CTN.nil) ⟨266128, 270336, 1217258438⟩ CTN.nil) ⟨266164, 270336, 1240143644⟩ (CTN.node CTN.nil ⟨266172, 270336, 1245255003⟩ CTN.nil))) ⟨266180, 270336, 1250375707⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨266204, 270336, 1265793778⟩ CTN.nil) ⟨266228, 270336, 1281295575⟩ CTN.nil) ⟨266240, 270336, 1289077782⟩ (CTN.node (CTN.node CTN.nil ⟨266252, 270336, 1296880815⟩ CTN.nil) ⟨266256, 270336, 1299486448⟩ CTN.nil)) ⟨266260, 270336, 1302094390⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨266264, 270336, 1304704639⟩ CTN.nil) ⟨266280, 270336, 1315168683⟩ CTN.nil) ⟨266292, 270336, 1323040880⟩ (CTN.node CTN.nil ⟨266304, 270336, 1330933747⟩ CTN.nil))))) ⟨266308, 270336, 1333569291⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨266324, 270336, 1344134366⟩ CTN.nil) ⟨266336, 270336, 1352082181⟩ CTN.nil) ⟨266356, 270336, 1365374165⟩ (CTN.node (CTN.node CTN.nil ⟨266384, 270336, 1384078469⟩ CTN.nil) ⟨266422, 270336, 1409640381⟩ CTN.nil)) ⟨266436, 270336, 1419109243⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨266454, 270336, 1431323950⟩ CTN.nil) ⟨266460, 270336, 1435405614⟩ CTN.nil) ⟨266516, 270336, 1473743524⟩ (CTN.node CTN.nil ⟨266544, 270336, 1493075901⟩ CTN.nil))) ⟨266546, 270336, 1494460935⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨266552, 270336, 1498619351⟩ CTN.nil) ⟨266560, 270336, 1504171631⟩ CTN.nil) ⟨266564, 270336, 1506951079⟩ (CTN.node (CTN.node CTN.nil ⟨266572, 270336, 1512516582⟩ CTN.nil) ⟨266640, 270336, 1560177550⟩ CTN.nil)) ⟨266680, 270336, 1588507606⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨266688, 270336, 1594199599⟩ CTN.nil) ⟨266816, 270336, 1686437568⟩ CTN.nil) ⟨266828, 270336, 1695196449⟩ (CTN.node CTN.nil ⟨266848, 270336, 1709836685⟩ CTN.nil)))) ⟨266868, 270336, 1724529384⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨266896, 270336, 1745186938⟩ CTN.nil) ⟨266936, 270336, 1774874411⟩ CTN.nil) ⟨267024, 270336, 1840911437⟩ (CTN.node (CTN.node CTN.nil ⟨267104, 270336, 1901798238⟩ CTN.nil) ⟨267140, 270336, 1929458859⟩ CTN.nil)) ⟨267152, 270336, 1938714835⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨267260, 270336, 2022814864⟩ CTN.nil) ⟨267408, 270336, 2140347265⟩ CTN.nil) ⟨267564, 270336, 2267006360⟩ (CTN.node CTN.nil ⟨267584, 270336, 2283445483⟩ CTN.nil))) ⟨267628, 270336, 2319769368⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨267664, 270336, 2349648990⟩ CTN.nil) ⟨267840, 270336, 2497756798⟩ CTN.nil) ⟨267888, 270336, 2538721601⟩ (CTN.node CTN.nil ⟨267952, 270336, 2593712708⟩ CTN.nil)) ⟨268108, 270336, 2729487227⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨268208, 270336, 2817775302⟩ CTN.nil) ⟨268432, 270336, 3018919607⟩ CTN.nil) ⟨268504, 270336, 3084522572⟩ (CTN.node CTN.nil ⟨268688, 270336, 3254156315⟩ CTN.nil)))))) ⟨268976, 270336, 3524998765⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨269192, 270336, 3731995009⟩ CTN.nil) ⟨270336, 270338, 4869028383⟩ CTN.nil) ⟨270336, 270352, 4868019153⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 270354, 4867874998⟩ CTN.nil) ⟨270336, 270356, 4867730849⟩ CTN.nil)) ⟨270336, 270374, 4866433748⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270386, 4865569253⟩ CTN.nil) ⟨270336, 270402, 4864416893⟩ CTN.nil) ⟨270336, 270406, 4864128856⟩ (CTN.node CTN.nil ⟨270336, 270434, 4862113195⟩ CTN.nil))) ⟨270336, 270454, 4860674076⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270464, 4859954717⟩ CTN.nil) ⟨270336, 270468, 4859667010⟩ CTN.nil) ⟨270336, 270480, 4858804019⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 270486, 4858372594⟩ CTN.nil) ⟨270336, 270496, 4857653661⟩ CTN.nil)) ⟨270336, 270498, 4857509890⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270512, 4856503643⟩ CTN.nil) ⟨270336, 270518, 4856072475⟩ CTN.nil) ⟨270336, 270528, 4855353966⟩ (CTN.node CTN.nil ⟨270336, 270534, 4854922925⟩ CTN.nil)))) ⟨270336, 270546, 4854060986⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270550, 4853773716⟩ CTN.nil) ⟨270336, 270562, 4852912032⟩ CTN.nil) ⟨270336, 270566, 4852624847⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 270598, 4850328128⟩ CTN.nil) ⟨270336, 270610, 4849467209⟩ CTN.nil)) ⟨270336, 270612, 4849323741⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270624, 4848463045⟩ CTN.nil) ⟨270336, 270630, 4848032769⟩ CTN.nil) ⟨270336, 270636, 4847602540⟩ (CTN.node CTN.nil ⟨270336, 270640, 4847315747⟩ CTN.nil))) ⟨270336, 270652, 4846455496⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270660, 4845882102⟩ CTN.nil) ⟨270336, 270690, 4843732628⟩ CTN.nil) ⟨270336, 270708, 4842443516⟩ (CTN.node CTN.nil ⟨270336, 270722, 4841441170⟩ CTN.nil)) ⟨270336, 270752, 4839294158⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270756, 4839007980⟩ CTN.nil) ⟨270336, 270768, 4838149572⟩ CTN.nil) ⟨270336, 270770, 4838006522⟩ (CTN.node CTN.nil ⟨270336, 270802, 4835718450⟩ CTN.nil))))) ⟨270336, 270822, 4834289091⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270828, 4833860387⟩ CTN.nil) ⟨270336, 270834, 4833431730⟩ CTN.nil) ⟨270336, 270842, 4832860261⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 270844, 4832717407⟩ CTN.nil) ⟨270336, 270850, 4832288877⟩ CTN.nil)) ⟨270336, 270898, 4828862344⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 270900, 4828719638⟩ CTN.nil) ⟨270336, 270942, 4825724024⟩ CTN.nil) ⟨270336, 270966, 4824013288⟩ (CTN.node CTN.nil ⟨270336, 270978, 4823158204⟩ CTN.nil))) ⟨270336, 271010, 4820878907⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271016, 4820451689⟩ CTN.nil) ⟨270336, 271024, 4819882138⟩ CTN.nil) ⟨270336, 271028, 4819597394⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 271044, 4818458629⟩ CTN.nil) ⟨270336, 271058, 4817462485⟩ CTN.nil)) ⟨270336, 271060, 4817320200⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271076, 4816182108⟩ CTN.nil) ⟨270336, 271108, 4813906931⟩ CTN.nil) ⟨270336, 271122, 4812911963⟩ (CTN.node CTN.nil ⟨270336, 271138, 4811775173⟩ CTN.nil)))) ⟨270336, 271188, 4808224865⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271200, 4807373278⟩ CTN.nil) ⟨270336, 271236, 4804819650⟩ CTN.nil) ⟨270336, 271254, 4803543471⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 271260, 4803118173⟩ CTN.nil) ⟨270336, 271266, 4802692921⟩ CTN.nil)) ⟨270336, 271272, 4802267717⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271286, 4801275756⟩ CTN.nil) ⟨270336, 271312, 4799434223⟩ CTN.nil) ⟨270336, 271318, 4799009379⟩ (CTN.node CTN.nil ⟨270336, 271324, 4798584582⟩ CTN.nil))) ⟨270336, 271328, 4798301410⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271330, 4798159832⟩ CTN.nil) ⟨270336, 271426, 4791370223⟩ CTN.nil) ⟨270336, 271428, 4791228901⟩ (CTN.node CTN.nil ⟨270336, 271450, 4789674698⟩ CTN.nil)) ⟨270336, 271452, 4789533438⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271472, 4788121126⟩ CTN.nil) ⟨270336, 271488, 4786991651⟩ CTN.nil) ⟨270336, 271554, 4782336085⟩ (CTN.node CTN.nil ⟨270336, 271556, 4782195096⟩ CTN.nil))))))))

noncomputable def tab29 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271586, 4780080879⟩ CTN.nil) ⟨270336, 271616, 4777967830⟩ CTN.nil) ⟨270336, 271618, 4777827002⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 271620, 4777686178⟩ CTN.nil) ⟨270336, 271652, 4775433713⟩ CTN.nil)) ⟨270336, 271664, 4774589381⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271680, 4773463895⟩ CTN.nil) ⟨270336, 271716, 4770932763⟩ CTN.nil) ⟨270336, 271728, 4770089426⟩ (CTN.node CTN.nil ⟨270336, 271780, 4766437116⟩ CTN.nil))) ⟨270336, 271796, 4765314032⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271806, 4764612272⟩ CTN.nil) ⟨270336, 271812, 4764191278⟩ CTN.nil) ⟨270336, 271828, 4763068856⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 271840, 4762227256⟩ CTN.nil) ⟨270336, 271842, 4762087007⟩ CTN.nil)) ⟨270336, 271844, 4761946764⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271860, 4760825002⟩ CTN.nil) ⟨270336, 271888, 4758862714⟩ CTN.nil) ⟨270336, 271892, 4758582469⟩ (CTN.node CTN.nil ⟨270336, 271908, 4757461698⟩ CTN.nil)))) ⟨270336, 271920, 4756621337⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271924, 4756341257⟩ CTN.nil) ⟨270336, 271940, 4755221146⟩ CTN.nil) ⟨270336, 271952, 4754381279⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 271954, 4754241320⟩ CTN.nil) ⟨270336, 271972, 4752981913⟩ CTN.nil)) ⟨270336, 271984, 4752142541⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 271988, 4751862791⟩ CTN.nil) ⟨270336, 271994, 4751443205⟩ CTN.nil) ⟨270336, 272002, 4750883829⟩ (CTN.node CTN.nil ⟨270336, 272004, 4750743998⟩ CTN.nil))) ⟨270336, 272016, 4749905120⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272050, 4747529303⟩ CTN.nil) ⟨270336, 272144, 4740968595⟩ CTN.nil) ⟨270336, 272176, 4738737749⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 272192, 4737622818⟩ CTN.nil) ⟨270336, 272196, 4737344136⟩ CTN.nil)) ⟨270336, 272274, 4731913941⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272276, 4731774808⟩ CTN.nil) ⟨270336, 272324, 4728437140⟩ CTN.nil) ⟨270336, 272340, 4727325238⟩ (CTN.node CTN.nil ⟨270336, 272384, 4724269192⟩ CTN.nil))))) ⟨270336, 272388, 4723991493⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272432, 4720938141⟩ CTN.nil) ⟨270336, 272436, 4720660686⟩ CTN.nil) ⟨270336, 272468, 4718441779⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 272562, 4711931277⟩ CTN.nil) ⟨270336, 272564, 4711792878⟩ CTN.nil)) ⟨270336, 272578, 4710824226⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272602, 4709164258⟩ CTN.nil) ⟨270336, 272628, 4707366784⟩ CTN.nil) ⟨270336, 272640, 4706537470⟩ (CTN.node CTN.nil ⟨270336, 272660, 4705155686⟩ CTN.nil))) ⟨270336, 272680, 4703774409⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272688, 4703222040⟩ CTN.nil) ⟨270336, 272692, 4702945886⟩ CTN.nil) ⟨270336, 272704, 4702117546⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 272736, 4699909530⟩ CTN.nil) ⟨270336, 272756, 4698530178⟩ CTN.nil)) ⟨270336, 272764, 4697978579⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272768, 4697702810⟩ CTN.nil) ⟨270336, 272820, 4694119652⟩ CTN.nil) ⟨270336, 272832, 4693293255⟩ (CTN.node CTN.nil ⟨270336, 272860, 4691365702⟩ CTN.nil)))) ⟨270336, 272864, 4691090418⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272900, 4688613771⟩ CTN.nil) ⟨270336, 272908, 4688063627⟩ CTN.nil) ⟨270336, 272928, 4686688620⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 272944, 4685588977⟩ CTN.nil) ⟨270336, 272958, 4684627055⟩ CTN.nil)) ⟨270336, 272960, 4684489657⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 272964, 4684214878⟩ CTN.nil) ⟨270336, 272992, 4682291984⟩ CTN.nil) ⟨270336, 272994, 4682154673⟩ (CTN.node CTN.nil ⟨270336, 273008, 4681193631⟩ CTN.nil))) ⟨270336, 273056, 4677900504⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273072, 4676803439⟩ CTN.nil) ⟨270336, 273120, 4673514172⟩ CTN.nil) ⟨270336, 273152, 4671322934⟩ (CTN.node CTN.nil ⟨270336, 273154, 4671186024⟩ CTN.nil)) ⟨270336, 273200, 4668038485⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273216, 4666944310⟩ CTN.nil) ⟨270336, 273234, 4665713747⟩ CTN.nil) ⟨270336, 273248, 4664756922⟩ (CTN.node CTN.nil ⟨270336, 273252, 4664483589⟩ CTN.nil)))))) ⟨270336, 273264, 4663663709⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273280, 4662570816⟩ CTN.nil) ⟨270336, 273282, 4662434227⟩ CTN.nil) ⟨270336, 273284, 4662297643⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 273296, 4661478243⟩ CTN.nil) ⟨270336, 273316, 4660112977⟩ CTN.nil)) ⟨270336, 273324, 4659567011⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273328, 4659294057⟩ CTN.nil) ⟨270336, 273344, 4658202445⟩ CTN.nil) ⟨270336, 273348, 4657929591⟩ (CTN.node CTN.nil ⟨270336, 273360, 4657111151⟩ CTN.nil))) ⟨270336, 273392, 4654929523⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273408, 4653839189⟩ CTN.nil) ⟨270336, 273424, 4652749173⟩ CTN.nil) ⟨270336, 273472, 4649481041⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 273476, 4649208826⟩ CTN.nil) ⟨270336, 273504, 4647303881⟩ CTN.nil)) ⟨270336, 273524, 4645943802⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273536, 4645127994⟩ CTN.nil) ⟨270336, 273552, 4644040529⟩ CTN.nil) ⟨270336, 273572, 4642681645⟩ (CTN.node CTN.nil ⟨270336, 273584, 4641866553⟩ CTN.nil)))) ⟨270336, 273588, 4641594895⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273636, 4638336554⟩ CTN.nil) ⟨270336, 273648, 4637522416⟩ CTN.nil) ⟨270336, 273652, 4637251076⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 273668, 4636165916⟩ CTN.nil) ⟨270336, 273680, 4635352254⟩ CTN.nil)) ⟨270336, 273700, 4633996547⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273712, 4633183361⟩ CTN.nil) ⟨270336, 273714, 4633047847⟩ CTN.nil) ⟨270336, 273820, 4625872707⟩ (CTN.node CTN.nil ⟨270336, 273840, 4624520466⟩ CTN.nil))) ⟨270336, 273852, 4623709358⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273860, 4623168718⟩ CTN.nil) ⟨270336, 273880, 4621817464⟩ CTN.nil) ⟨270336, 273920, 4619116438⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 273924, 4618846444⟩ CTN.nil) ⟨270336, 273936, 4618036580⟩ CTN.nil)) ⟨270336, 273940, 4617766665⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 273944, 4617496769⟩ CTN.nil) ⟨270336, 273968, 4615877811⟩ CTN.nil) ⟨270336, 273984, 4614798899⟩ (CTN.node CTN.nil ⟨270336, 273988, 4614529221⟩ CTN.nil))))) ⟨270336, 274002, 4613585501⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274004, 4613450703⟩ CTN.nil) ⟨270336, 274048, 4610486405⟩ CTN.nil) ⟨270336, 274076, 4608601272⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 274140, 4604296016⟩ CTN.nil) ⟨270336, 274144, 4604027105⟩ CTN.nil)) ⟨270336, 274164, 4602682842⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274200, 4600264404⟩ CTN.nil) ⟨270336, 274224, 4598652995⟩ CTN.nil) ⟨270336, 274228, 4598384496⟩ (CTN.node CTN.nil ⟨270336, 274268, 4595700578⟩ CTN.nil))) ⟨270336, 274288, 4594359353⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274292, 4594091167⟩ CTN.nil) ⟨270336, 274300, 4593554853⟩ CTN.nil) ⟨270336, 274304, 4593286726⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 274308, 4593018618⟩ CTN.nil) ⟨270336, 274316, 4592482461⟩ CTN.nil)) ⟨270336, 274336, 4591142410⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274356, 4589802848⟩ CTN.nil) ⟨270336, 274364, 4589267161⟩ CTN.nil) ⟨270336, 274368, 4588999346⟩ (CTN.node CTN.nil ⟨270336, 274400, 4586857532⟩ CTN.nil)))) ⟨270336, 274432, 4584716968⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274444, 4583914578⟩ CTN.nil) ⟨270336, 274480, 4581508463⟩ CTN.nil) ⟨270336, 274492, 4580706775⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 274496, 4580439585⟩ CTN.nil) ⟨270336, 274544, 4577234821⟩ CTN.nil)) ⟨270336, 274564, 4575900330⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274580, 4574833088⟩ CTN.nil) ⟨270336, 274592, 4574032860⟩ CTN.nil) ⟨270336, 274608, 4572966162⟩ (CTN.node CTN.nil ⟨270336, 274628, 4571633227⟩ CTN.nil))) ⟨270336, 274644, 4570567228⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274656, 4569767933⟩ CTN.nil) ⟨270336, 274672, 4568702479⟩ CTN.nil) ⟨270336, 274688, 4567637334⟩ (CTN.node CTN.nil ⟨270336, 274692, 4567371097⟩ CTN.nil)) ⟨270336, 274704, 4566572501⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274720, 4565507977⟩ CTN.nil) ⟨270336, 274736, 4564443764⟩ CTN.nil) ⟨270336, 274740, 4564177759⟩ (CTN.node CTN.nil ⟨270336, 274752, 4563379861⟩ CTN.nil))))))) ⟨270336, 274848, 4557002948⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274860, 4556206618⟩ CTN.nil) ⟨270336, 274868, 4555675828⟩ CTN.nil) ⟨270336, 274884, 4554614479⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 274932, 4551432286⟩ CTN.nil) ⟨270336, 274940, 4550902191⟩ CTN.nil)) ⟨270336, 274944, 4550637173⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 274948, 4550372173⟩ CTN.nil) ⟨270336, 274960, 4549577291⟩ CTN.nil) ⟨270336, 274980, 4548252873⟩ (CTN.node CTN.nil ⟨270336, 274992, 4547458454⟩ CTN.nil))) ⟨270336, 274996, 4547193686⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275008, 4546399498⟩ CTN.nil) ⟨270336, 275044, 4544017973⟩ CTN.nil) ⟨270336, 275056, 4543224479⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 275060, 4542960019⟩ CTN.nil) ⟨270336, 275072, 4542166755⟩ CTN.nil)) ⟨270336, 275076, 4541902372⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275088, 4541109339⟩ CTN.nil) ⟨270336, 275120, 4538995431⟩ CTN.nil) ⟨270336, 275124, 4538731279⟩ (CTN.node CTN.nil ⟨270336, 275136, 4537938938⟩ CTN.nil)))) ⟨270336, 275140, 4537674863⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275188, 4534507458⟩ CTN.nil) ⟨270336, 275236, 4531342818⟩ CTN.nil) ⟨270336, 275248, 4530552089⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 275252, 4530288551⟩ CTN.nil) ⟨270336, 275268, 4529234591⟩ CTN.nil)) ⟨270336, 275300, 4527127591⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275312, 4526337781⟩ CTN.nil) ⟨270336, 275316, 4526074550⟩ CTN.nil) ⟨270336, 275328, 4525284970⟩ (CTN.node CTN.nil ⟨270336, 275332, 4525021815⟩ CTN.nil))) ⟨270336, 275344, 4524232465⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275376, 4522128374⟩ CTN.nil) ⟨270336, 275388, 4521339655⟩ CTN.nil) ⟨270336, 275392, 4521076786⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 275412, 4519762732⟩ CTN.nil) ⟨270336, 275440, 4517923859⟩ CTN.nil)) ⟨270336, 275452, 4517136056⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275472, 4515823434⟩ CTN.nil) ⟨270336, 275484, 4515036089⟩ CTN.nil) ⟨270336, 275504, 4513724230⟩ (CTN.node CTN.nil ⟨270336, 275524, 4512412847⟩ CTN.nil))))) ⟨270336, 275544, 4511101940⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275592, 4507957706⟩ CTN.nil) ⟨270336, 275600, 4507433933⟩ CTN.nil) ⟨270336, 275612, 4506648417⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 275628, 4505601328⟩ CTN.nil) ⟨270336, 275648, 4504292894⟩ CTN.nil)) ⟨270336, 275652, 4504031265⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275668, 4502984936⟩ CTN.nil) ⟨270336, 275676, 4502461885⟩ CTN.nil) ⟨270336, 275692, 4501416012⟩ (CTN.node CTN.nil ⟨270336, 275696, 4501154592⟩ CTN.nil))) ⟨270336, 275700, 4500893190⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275708, 4500370443⟩ CTN.nil) ⟨270336, 275712, 4500109098⟩ CTN.nil) ⟨270336, 275728, 4499063908⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 275740, 4498280215⟩ CTN.nil) ⟨270336, 275752, 4497496693⟩ CTN.nil)) ⟨270336, 275764, 4496713341⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275776, 4495930159⟩ CTN.nil) ⟨270336, 275808, 4493842509⟩ CTN.nil) ⟨270336, 275932, 4485764303⟩ (CTN.node CTN.nil ⟨270336, 275952, 4484463067⟩ CTN.nil)))) ⟨270336, 275956, 4484202876⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 275968, 4483422418⟩ CTN.nil) ⟨270336, 275980, 4482642130⟩ CTN.nil) ⟨270336, 275988, 4482122032⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 276000, 4481342026⟩ CTN.nil) ⟨270336, 276016, 4480302282⟩ CTN.nil)) ⟨270336, 276020, 4480042394⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276028, 4479522673⟩ CTN.nil) ⟨270336, 276032, 4479262840⟩ CTN.nil) ⟨270336, 276036, 4479003027⟩ (CTN.node CTN.nil ⟨270336, 276052, 4477963962⟩ CTN.nil))) ⟨270336, 276064, 4477184861⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276076, 4476405929⟩ CTN.nil) ⟨270336, 276096, 4475108086⟩ CTN.nil) ⟨270336, 276172, 4470180571⟩ (CTN.node CTN.nil ⟨270336, 276188, 4469144064⟩ CTN.nil)) ⟨270336, 276192, 4468884984⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276208, 4467848853⟩ CTN.nil) ⟨270336, 276244, 4465518654⟩ CTN.nil) ⟨270336, 276256, 4464742259⟩ (CTN.node CTN.nil ⟨270336, 276272, 4463707328⟩ CTN.nil)))))) ⟨270336, 276292, 4462414086⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276308, 4461379830⟩ CTN.nil) ⟨270336, 276320, 4460604335⟩ CTN.nil) ⟨270336, 276368, 4457504037⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 276384, 4456471203⟩ CTN.nil) ⟨270336, 276396, 4455696774⟩ CTN.nil)) ⟨270336, 276416, 4454406433⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276420, 4454148421⟩ CTN.nil) ⟨270336, 276460, 4451569326⟩ CTN.nil) ⟨270336, 276464, 4451311519⟩ (CTN.node CTN.nil ⟨270336, 276468, 4451053731⟩ CTN.nil))) ⟨270336, 276496, 4449249737⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276604, 4442300030⟩ CTN.nil) ⟨270336, 276612, 4441785777⟩ CTN.nil) ⟨270336, 276620, 4441271599⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 276624, 4441014537⟩ CTN.nil) ⟨270336, 276660, 4438701822⟩ CTN.nil)) ⟨270336, 276668, 4438188089⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276672, 4437931251⟩ CTN.nil) ⟨270336, 276720, 4434850640⟩ CTN.nil) ⟨270336, 276752, 4432798385⟩ (CTN.node CTN.nil ⟨270336, 276784, 4430747317⟩ CTN.nil)))) ⟨270336, 276800, 4429722228⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 276816, 4428697435⟩ CTN.nil) ⟨270336, 276836, 4427416861⟩ CTN.nil) ⟨270336, 276848, 4426648739⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 276976, 4418465792⟩ CTN.nil) ⟨270336, 276992, 4417444254⟩ CTN.nil)) ⟨270336, 276996, 4417188915⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277000, 4416933595⟩ CTN.nil) ⟨270336, 277008, 4416423011⟩ CTN.nil) ⟨270336, 277040, 4414381410⟩ (CTN.node CTN.nil ⟨270336, 277056, 4413361052⟩ CTN.nil))) ⟨270336, 277072, 4412340989⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277104, 4410301747⟩ CTN.nil) ⟨270336, 277116, 4409537335⟩ CTN.nil) ⟨270336, 277172, 4405972269⟩ (CTN.node CTN.nil ⟨270336, 277248, 4401139726⟩ CTN.nil)) ⟨270336, 277252, 4400885565⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277264, 4400123193⟩ CTN.nil) ⟨270336, 277272, 4399615037⟩ CTN.nil) ⟨270336, 277292, 4398344967⟩ (CTN.node CTN.nil ⟨270336, 277340, 4395298668⟩ CTN.nil))))) ⟨270336, 277356, 4394283822⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277364, 4393776508⟩ CTN.nil) ⟨270336, 277372, 4393269268⟩ CTN.nil) ⟨270336, 277376, 4393015675⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 277380, 4392762101⟩ CTN.nil) ⟨270336, 277388, 4392255007⟩ CTN.nil)) ⟨270336, 277392, 4392001488⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277404, 4391241039⟩ CTN.nil) ⟨270336, 277428, 4389720636⟩ CTN.nil) ⟨270336, 277440, 4388960681⟩ (CTN.node CTN.nil ⟨270336, 277512, 4384404403⟩ CTN.nil))) ⟨270336, 277528, 4383392700⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277568, 4380864719⟩ CTN.nil) ⟨270336, 277616, 4377833547⟩ CTN.nil) ⟨270336, 277620, 4377581068⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 277644, 4376066575⟩ CTN.nil) ⟨270336, 277680, 4373796063⟩ CTN.nil)) ⟨270336, 277692, 4373039553⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277696, 4372787419⟩ CTN.nil) ⟨270336, 277716, 4371527023⟩ CTN.nil) ⟨270336, 277728, 4370771004⟩ (CTN.node CTN.nil ⟨270336, 277824, 4364728729⟩ CTN.nil)))) ⟨270336, 277836, 4363974179⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277872, 4361711508⟩ CTN.nil) ⟨270336, 277884, 4360957610⟩ CTN.nil) ⟨270336, 277904, 4359701475⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 277920, 4358696893⟩ CTN.nil) ⟨270336, 277936, 4357692601⟩ CTN.nil)) ⟨270336, 277952, 4356688597⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 277972, 4355434000⟩ CTN.nil) ⟨270336, 277984, 4354681458⟩ CTN.nil) ⟨270336, 277996, 4353929079⟩ (CTN.node CTN.nil ⟨270336, 278000, 4353678322⟩ CTN.nil))) ⟨270336, 278060, 4349919134⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 278080, 4348666973⟩ CTN.nil) ⟨270336, 278112, 4346664453⟩ CTN.nil) ⟨270336, 278124, 4345913805⟩ (CTN.node CTN.nil ⟨270336, 278140, 4344913193⟩ CTN.nil)) ⟨270336, 278160, 4343662833⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 278232, 4339165261⟩ CTN.nil) ⟨270336, 278256, 4337667364⟩ CTN.nil) ⟨270336, 278284, 4335920635⟩ (CTN.node CTN.nil ⟨270336, 278292, 4335421731⟩ CTN.nil))))))))

noncomputable def tab30 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 278332, 4332928287⟩ CTN.nil) ⟨270336, 278340, 4332429814⟩ CTN.nil) ⟨270336, 278376, 4330187569⟩ (CTN.node (CTN.node CTN.nil ⟨270336, 278388, 4329440477⟩ CTN.nil) ⟨270336, 278416, 4327697888⟩ CTN.nil)) ⟨270336, 278448, 4325707432⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨270336, 278476, 4323966721⟩ CTN.nil) ⟨270336, 278528, 4320736295⟩ CTN.nil) ⟨276128, 278528, 8864094723⟩ (CTN.node CTN.nil ⟨278528, 278544, 9614042450⟩ CTN.nil))) ⟨278528, 278548, 9613477112⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 278560, 9611764383⟩ CTN.nil) ⟨278528, 278580, 9608854144⟩ CTN.nil) ⟨278528, 278596, 9606475868⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 278604, 9605270046⟩ CTN.nil) ⟨278528, 278616, 9603440469⟩ CTN.nil)) ⟨278528, 278640, 9599706332⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 278644, 9599074261⟩ CTN.nil) ⟨278528, 278664, 9595872309⟩ CTN.nil) ⟨278528, 278672, 9594572124⟩ (CTN.node CTN.nil ⟨278528, 278700, 9589934243⟩ CTN.nil)))) ⟨278528, 278704, 9589260618⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 278720, 9586538465⟩ CTN.nil) ⟨278528, 278724, 9585851016⟩ CTN.nil) ⟨278528, 278740, 9583073594⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 278768, 9578106835⟩ CTN.nil) ⟨278528, 278772, 9577386266⟩ CTN.nil)) ⟨278528, 278836, 9565482705⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 278860, 9560837450⟩ CTN.nil) ⟨278528, 278872, 9558477782⟩ CTN.nil) ⟨278528, 278920, 9548792563⟩ (CTN.node CTN.nil ⟨278528, 278928, 9547140058⟩ CTN.nil))) ⟨278528, 278932, 9546309707⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 278964, 9539568604⟩ CTN.nil) ⟨278528, 278976, 9536995684⟩ CTN.nil) ⟨278528, 279052, 9520131814⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 279080, 9513671785⟩ CTN.nil) ⟨278528, 279100, 9508976255⟩ CTN.nil)) ⟨278528, 279104, 9508029036⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 279136, 9500354045⟩ CTN.nil) ⟨278528, 279300, 9458318687⟩ CTN.nil) ⟨278528, 279308, 9456153106⟩ (CTN.node CTN.nil ⟨278528, 279356, 9442936010⟩ CTN.nil))))) ⟨278528, 279360, 9441817308⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 279420, 9424718715⟩ CTN.nil) ⟨278528, 279484, 9405825055⟩ CTN.nil) ⟨278528, 279556, 9383765501⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 279684, 9342461357⟩ CTN.nil) ⟨278528, 279696, 9338452953⟩ CTN.nil)) ⟨278528, 279744, 9322187246⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 279856, 9282797382⟩ CTN.nil) ⟨278528, 279864, 9279907266⟩ CTN.nil) ⟨278528, 279888, 9271175954⟩ (CTN.node CTN.nil ⟨278528, 279976, 9238381857⟩ CTN.nil))) ⟨278528, 280020, 9221527973⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 280024, 9219980769⟩ CTN.nil) ⟨278528, 280040, 9213766956⟩ CTN.nil) ⟨278528, 280112, 9185311415⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 280140, 9174028233⟩ CTN.nil) ⟨278528, 280144, 9172406461⟩ CTN.nil)) ⟨278528, 280188, 9154404244⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 280276, 9117509353⟩ CTN.nil) ⟨278528, 280300, 9107242264⟩ CTN.nil) ⟨278528, 280348, 9086446334⟩ (CTN.node CTN.nil ⟨278528, 280364, 9079437069⟩ CTN.nil)))) ⟨278528, 280400, 9063525489⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 280444, 9043814398⟩ CTN.nil) ⟨278528, 280556, 8992342568⟩ CTN.nil) ⟨278528, 280584, 8979185607⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 280588, 8977296662⟩ CTN.nil) ⟨278528, 280604, 8969717485⟩ CTN.nil)) ⟨278528, 280608, 8967816847⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 280636, 8954447076⟩ CTN.nil) ⟨278528, 280744, 8901814033⟩ CTN.nil) ⟨278528, 280864, 8841374088⟩ (CTN.node CTN.nil ⟨278528, 280872, 8837272255⟩ CTN.nil))) ⟨278528, 280908, 8818702732⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 280976, 8783132897⟩ CTN.nil) ⟨278528, 281000, 8770425560⟩ CTN.nil) ⟨278528, 281024, 8757638718⟩ (CTN.node CTN.nil ⟨278528, 281072, 8731827694⟩ CTN.nil)) ⟨278528, 281164, 8681479539⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 281232, 8643532999⟩ CTN.nil) ⟨278528, 281280, 8616376469⟩ CTN.nil) ⟨278528, 281304, 8602684040⟩ (CTN.node CTN.nil ⟨278528, 281324, 8591215845⟩ CTN.nil)))))) ⟨278528, 281328, 8588915914⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 281408, 8542479447⟩ CTN.nil) ⟨278528, 281424, 8533092657⟩ CTN.nil) ⟨278528, 281452, 8516586550⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 281456, 8514220328⟩ CTN.nil) ⟨278528, 281584, 8437428214⟩ CTN.nil)) ⟨278528, 281680, 8378487616⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 281712, 8358588403⟩ CTN.nil) ⟨278528, 281724, 8351093963⟩ CTN.nil) ⟨278528, 281736, 8343582005⟩ (CTN.node CTN.nil ⟨278528, 281784, 8313359829⟩ CTN.nil))) ⟨278528, 281872, 8257235176⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 281944, 8210634313⟩ CTN.nil) ⟨278528, 281992, 8179231664⟩ CTN.nil) ⟨278528, 282000, 8173972040⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 282040, 8147563911⟩ CTN.nil) ⟨278528, 282048, 8142260373⟩ CTN.nil)) ⟨278528, 282168, 8061841726⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 282304, 7968777808⟩ CTN.nil) ⟨278528, 282432, 7879378057⟩ CTN.nil) ⟨278528, 282444, 7870908863⟩ (CTN.node CTN.nil ⟨278528, 282464, 7856760480⟩ CTN.nil)))) ⟨278528, 282724, 7669165930⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 282768, 7636765193⟩ CTN.nil) ⟨278528, 282936, 7511388731⟩ CTN.nil) ⟨278528, 283024, 7444693755⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 283048, 7426385832⟩ CTN.nil) ⟨278528, 283096, 7389620376⟩ CTN.nil)) ⟨278528, 283176, 7327908677⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 283192, 7315501994⟩ CTN.nil) ⟨278528, 283224, 7290625221⟩ CTN.nil) ⟨278528, 283272, 7253153301⟩ (CTN.node CTN.nil ⟨278528, 283304, 7228068886⟩ CTN.nil))) ⟨278528, 283320, 7215496092⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 283352, 7190289920⟩ CTN.nil) ⟨278528, 283480, 7088674855⟩ CTN.nil) ⟨278528, 283656, 6946976558⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 283816, 6816294970⟩ CTN.nil) ⟨278528, 283912, 6737085865⟩ CTN.nil)) ⟨278528, 283936, 6717193826⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 283944, 6710555332⟩ CTN.nil) ⟨278528, 284072, 6603821877⟩ CTN.nil) ⟨278528, 284192, 6502912727⟩ (CTN.node CTN.nil ⟨278528, 284200, 6496157640⟩ CTN.nil))))) ⟨278528, 284304, 6408038825⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 284352, 6367184911⟩ CTN.nil) ⟨278528, 284448, 6285146420⟩ CTN.nil) ⟨278528, 284472, 6264570370⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 284480, 6257705948⟩ CTN.nil) ⟨278528, 284496, 6243968592⟩ CTN.nil)) ⟨278528, 284528, 6216460264⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 284608, 6147499214⟩ CTN.nil) ⟨278528, 284632, 6126759638⟩ CTN.nil) ⟨278528, 284656, 6105997158⟩ (CTN.node CTN.nil ⟨278528, 284752, 6022726673⟩ CTN.nil))) ⟨278528, 284784, 5994894610⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 284912, 5883217059⟩ CTN.nil) ⟨278528, 285064, 5749942243⟩ CTN.nil) ⟨278528, 285112, 5707723277⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 285192, 5637232081⟩ CTN.nil) ⟨278528, 285240, 5594867171⟩ CTN.nil)) ⟨278528, 285272, 5566596758⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 285328, 5517074737⟩ CTN.nil) ⟨278528, 285368, 5481666367⟩ CTN.nil) ⟨278528, 285376, 5474581348⟩ (CTN.node CTN.nil ⟨278528, 285472, 5389481559⟩ CTN.nil)))) ⟨278528, 285504, 5361085181⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 285632, 5247377678⟩ CTN.nil) ⟨278528, 285672, 5211810948⟩ CTN.nil) ⟨278528, 286096, 4834429251⟩ (CTN.node (CTN.node CTN.nil ⟨278528, 286264, 4685031479⟩ CTN.nil) ⟨278528, 286344, 4613983316⟩ CTN.nil)) ⟨278528, 286376, 4585586016⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 286392, 4571392567⟩ CTN.nil) ⟨278528, 286424, 4543016684⟩ CTN.nil) ⟨278528, 286440, 4528834498⟩ (CTN.node CTN.nil ⟨278528, 286504, 4472146979⟩ CTN.nil))) ⟨278528, 286520, 4457986019⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨278528, 286552, 4429678062⟩ CTN.nil) ⟨278528, 286648, 4344874677⟩ CTN.nil) ⟨278528, 286720, 4281402733⟩ (CTN.node CTN.nil ⟨278876, 286720, 4301264662⟩ CTN.nil)) ⟨281560, 286720, 4454872555⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 286808, 4654635218⟩ CTN.nil) ⟨286720, 286824, 4639391053⟩ CTN.nil) ⟨286720, 286984, 4487356597⟩ (CTN.node CTN.nil ⟨286720, 287144, 4336151789⟩ CTN.nil))))))) ⟨286720, 287264, 4223368803⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 287272, 4215870359⟩ CTN.nil) ⟨286720, 287520, 3984805512⟩ CTN.nil) ⟨286720, 287544, 3962596178⟩ (CTN.node (CTN.node CTN.nil ⟨286720, 287632, 3881408783⟩ CTN.nil) ⟨286720, 287800, 3727551014⟩ CTN.nil)) ⟨286720, 287808, 3720263472⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 287824, 3705699389⟩ CTN.nil) ⟨286720, 287936, 3604170856⟩ CTN.nil) ⟨286720, 287960, 3582512759⟩ (CTN.node CTN.nil ⟨286720, 287984, 3560890137⟩ CTN.nil))) ⟨286720, 288032, 3517752895⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 288080, 3474762273⟩ CTN.nil) ⟨286720, 288240, 3332559134⟩ CTN.nil) ⟨286720, 288264, 3311379256⟩ (CTN.node (CTN.node CTN.nil ⟨286720, 288392, 3199111382⟩ CTN.nil) ⟨286720, 288544, 3067364681⟩ CTN.nil)) ⟨286720, 288568, 3046724305⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 288696, 2937413488⟩ CTN.nil) ⟨286720, 288832, 2822739058⟩ CTN.nil) ⟨286720, 288904, 2762663216⟩ (CTN.node CTN.nil ⟨286720, 288960, 2716249128⟩ CTN.nil)))) ⟨286720, 289128, 2578689167⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 289312, 2431032011⟩ CTN.nil) ⟨286720, 289408, 2355288468⟩ CTN.nil) ⟨286720, 289424, 2342752964⟩ (CTN.node (CTN.node CTN.nil ⟨286720, 289672, 2151773571⟩ CTN.nil) ⟨286720, 289704, 2127595540⟩ CTN.nil)) ⟨286720, 289720, 2115547180⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 289832, 2031975898⟩ CTN.nil) ⟨286720, 289976, 1926535884⟩ CTN.nil) ⟨286720, 290312, 1689628045⟩ (CTN.node CTN.nil ⟨286720, 290472, 1581470155⟩ CTN.nil))) ⟨286720, 290600, 1497179022⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 290640, 1471252164⟩ CTN.nil) ⟨286720, 290872, 1324838582⟩ CTN.nil) ⟨286720, 291128, 1171305448⟩ (CTN.node (CTN.node CTN.nil ⟨286720, 291264, 1093253679⟩ CTN.nil) ⟨286720, 291376, 1030840438⟩ CTN.nil)) ⟨286720, 291592, 915304170⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 291632, 894615252⟩ CTN.nil) ⟨286720, 291872, 775188023⟩ CTN.nil) ⟨286720, 291920, 752279509⟩ (CTN.node CTN.nil ⟨286720, 292024, 703772922⟩ CTN.nil))))) ⟨286720, 292288, 587644695⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 292640, 448674736⟩ CTN.nil) ⟨286720, 293000, 325618895⟩ CTN.nil) ⟨286720, 293336, 228401376⟩ (CTN.node (CTN.node CTN.nil ⟨286720, 293352, 224199490⟩ CTN.nil) ⟨286720, 293456, 197837495⟩ CTN.nil)) ⟨286720, 293736, 135064409⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨286720, 293972, 91459105⟩ CTN.nil) ⟨286720, 294036, 81101145⟩ CTN.nil) ⟨286720, 294272, 48310569⟩ (CTN.node CTN.nil ⟨286720, 294912, 1958320⟩ CTN.nil))) ⟨294912, 294920, 3640140⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨294912, 295056, 488698⟩ CTN.nil) ⟨294912, 295072, 310153⟩ CTN.nil) ⟨295136, 303104, 120⟩ (CTN.node (CTN.node CTN.nil ⟨295144, 303104, 6134⟩ CTN.nil) ⟨295146, 301062, 9304⟩ CTN.nil)) ⟨295162, 302806, 53058⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295172, 303104, 98661⟩ CTN.nil) ⟨295178, 301926, 135047⟩ CTN.nil) ⟨295178, 302568, 133904⟩ (CTN.node CTN.nil ⟨295180, 303104, 145526⟩ CTN.nil)))) ⟨295184, 303104, 172364⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295192, 303104, 232852⟩ CTN.nil) ⟨295194, 303104, 249393⟩ CTN.nil) ⟨295210, 303104, 402164⟩ (CTN.node (CTN.node CTN.nil ⟨295224, 303104, 565654⟩ CTN.nil) ⟨295236, 303104, 727942⟩ CTN.nil)) ⟨295244, 303104, 847497⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295250, 303104, 943129⟩ CTN.nil) ⟨295272, 303104, 1337546⟩ CTN.nil) ⟨295276, 302856, 1421296⟩ (CTN.node CTN.nil ⟨295308, 302056, 2161092⟩ CTN.nil))) ⟨295308, 303104, 2131341⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295316, 303104, 2332763⟩ CTN.nil) ⟨295320, 303104, 2436888⟩ CTN.nil) ⟨295324, 302200, 2573874⟩ (CTN.node CTN.nil ⟨295340, 300488, 3097256⟩ CTN.nil)) ⟨295340, 301256, 3065774⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295340, 303104, 2991645⟩ CTN.nil) ⟨295352, 302964, 3358015⟩ CTN.nil) ⟨295372, 301288, 4094936⟩ (CTN.node CTN.nil ⟨295372, 302120, 4049987⟩ CTN.nil)))))) ⟨295372, 302952, 4005654⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295384, 303104, 4412429⟩ CTN.nil) ⟨295388, 301336, 4663169⟩ CTN.nil) ⟨295396, 303104, 4847734⟩ (CTN.node (CTN.node CTN.nil ⟨295400, 301958, 5073734⟩ CTN.nil) ⟨295404, 301320, 5272435⟩ CTN.nil)) ⟨295404, 302152, 5214568⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295414, 302004, 5620319⟩ CTN.nil) ⟨295414, 302868, 5556422⟩ CTN.nil) ⟨295416, 303104, 5618795⟩ (CTN.node CTN.nil ⟨295420, 302200, 5849353⟩ CTN.nil))) ⟨295432, 303104, 6276650⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295436, 303104, 6446809⟩ CTN.nil) ⟨295444, 303104, 6793964⟩ CTN.nil) ⟨295446, 302868, 6903665⟩ (CTN.node (CTN.node CTN.nil ⟨295448, 303104, 6970959⟩ CTN.nil) ⟨295462, 302820, 7636987⟩ CTN.nil)) ⟨295496, 303104, 9272668⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295500, 303104, 9479293⟩ CTN.nil) ⟨295508, 303104, 9899382⟩ CTN.nil) ⟨295512, 303104, 10112846⟩ (CTN.node CTN.nil ⟨295524, 303104, 10766918⟩ CTN.nil)))) ⟨295528, 303104, 10989502⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295544, 303104, 11902640⟩ CTN.nil) ⟨295560, 303104, 12852263⟩ CTN.nil) ⟨295564, 303104, 13095369⟩ (CTN.node (CTN.node CTN.nil ⟨295568, 303104, 13340756⟩ CTN.nil) ⟨295572, 303104, 13588424⟩ CTN.nil)) ⟨295588, 303104, 14601901⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295628, 303104, 17295249⟩ CTN.nil) ⟨295636, 303058, 17872143⟩ CTN.nil) ⟨295636, 303104, 17861289⟩ (CTN.node CTN.nil ⟨295640, 302420, 18312570⟩ CTN.nil))) ⟨295652, 303010, 19044370⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295672, 303104, 20521384⟩ CTN.nil) ⟨295688, 303104, 21762956⟩ CTN.nil) ⟨295696, 303104, 22397430⟩ (CTN.node CTN.nil ⟨295728, 303104, 25026566⟩ CTN.nil)) ⟨295736, 303104, 25706660⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295752, 303104, 27094221⟩ CTN.nil) ⟨295764, 303104, 28158842⟩ CTN.nil) ⟨295768, 303104, 28518277⟩ (CTN.node CTN.nil ⟨295776, 303104, 29243990⟩ CTN.nil))))) ⟨295780, 303104, 29610268⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295800, 303104, 31475866⟩ CTN.nil) ⟨295812, 303104, 32622592⟩ CTN.nil) ⟨295816, 303104, 33009395⟩ (CTN.node (CTN.node CTN.nil ⟨295828, 303104, 34183485⟩ CTN.nil) ⟨295866, 301814, 38691697⟩ CTN.nil)) ⟨295876, 303104, 39085055⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295882, 303104, 39720834⟩ CTN.nil) ⟨295892, 303104, 40791863⟩ CTN.nil) ⟨295898, 301846, 42136925⟩ (CTN.node CTN.nil ⟨295898, 303104, 41441319⟩ CTN.nil))) ⟨295912, 303104, 42976657⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295914, 301830, 43932686⟩ CTN.nil) ⟨295926, 303104, 44539912⟩ CTN.nil) ⟨295940, 303104, 46131080⟩ (CTN.node (CTN.node CTN.nil ⟨295946, 302694, 47075900⟩ CTN.nil) ⟨295952, 303104, 47517153⟩ CTN.nil)) ⟨295962, 301910, 49463128⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨295978, 301894, 51407096⟩ CTN.nil) ⟨295978, 302726, 50843947⟩ CTN.nil) ⟨295978, 303104, 50590642⟩ (CTN.node CTN.nil ⟨295984, 303104, 51313575⟩ CTN.nil)))) ⟨295988, 303104, 51798377⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨295990, 303104, 52041632⟩ CTN.nil) ⟨295994, 302774, 52759374⟩ CTN.nil) ⟨296004, 303104, 53760355⟩ (CTN.node (CTN.node CTN.nil ⟨296010, 302758, 54755226⟩ CTN.nil) ⟨296032, 303104, 57281470⟩ CTN.nil)) ⟨296118, 303104, 68793446⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296140, 302888, 72112668⟩ CTN.nil) ⟨296150, 303104, 73345280⟩ CTN.nil) ⟨296156, 303104, 74214939⟩ (CTN.node CTN.nil ⟨296168, 303104, 75969590⟩ CTN.nil))) ⟨296172, 302088, 77594794⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨296172, 302920, 76745310⟩ CTN.nil) ⟨296200, 303104, 80748581⟩ CTN.nil) ⟨296204, 303104, 81356172⟩ (CTN.node CTN.nil ⟨296208, 303104, 81966032⟩ CTN.nil)) ⟨296232, 302790, 86028988⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296264, 303104, 90742288⟩ CTN.nil) ⟨296278, 302868, 93296195⟩ CTN.nil) ⟨296308, 303104, 97949644⟩ (CTN.node CTN.nil ⟨296328, 303104, 101316318⟩ CTN.nil))))))))

noncomputable def tab31 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨296356, 303104, 106124728⟩ CTN.nil) ⟨296376, 303104, 109627172⟩ CTN.nil) ⟨296392, 303104, 112469826⟩ (CTN.node (CTN.node CTN.nil ⟨296420, 303104, 117531468⟩ CTN.nil) ⟨296440, 303104, 121214678⟩ CTN.nil)) ⟨296456, 303104, 124201875⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296464, 303104, 125709009⟩ CTN.nil) ⟨296468, 303104, 126465960⟩ CTN.nil) ⟨296472, 303104, 127225166⟩ (CTN.node CTN.nil ⟨296476, 303104, 127986627⟩ CTN.nil))) ⟨296488, 303104, 130284536⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨296504, 303104, 133379967⟩ CTN.nil) ⟨296520, 303104, 136511441⟩ CTN.nil) ⟨296544, 303104, 141276196⟩ (CTN.node (CTN.node CTN.nil ⟨296552, 303104, 142882450⟩ CTN.nil) ⟨296564, 303104, 145308700⟩ CTN.nil)) ⟨296584, 303104, 149397415⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296612, 303104, 155215977⟩ CTN.nil) ⟨296648, 303104, 162858593⟩ CTN.nil) ⟨296650, 303104, 163288510⟩ (CTN.node CTN.nil ⟨296682, 303104, 170243364⟩ CTN.nil)))) ⟨296696, 303104, 173331185⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨296714, 303104, 177341520⟩ CTN.nil) ⟨296730, 302678, 181965711⟩ CTN.nil) ⟨296746, 302662, 185664048⟩ (CTN.node (CTN.node CTN.nil ⟨296746, 303104, 184582800⟩ CTN.nil) ⟨296760, 303104, 187795821⟩ CTN.nil)) ⟨296762, 303104, 188257056⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296772, 303104, 190571604⟩ CTN.nil) ⟨296774, 303104, 191036187⟩ CTN.nil) ⟨296778, 303104, 191967026⟩ (CTN.node CTN.nil ⟨296784, 303104, 193367467⟩ CTN.nil))) ⟨296788, 303104, 194303882⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨296800, 303104, 197126504⟩ CTN.nil) ⟨296804, 303104, 198071835⟩ CTN.nil) ⟨296836, 303104, 205714670⟩ (CTN.node (CTN.node CTN.nil ⟨296844, 303104, 207647638⟩ CTN.nil) ⟨296924, 303104, 227466146⟩ CTN.nil)) ⟨296944, 303104, 232559418⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨296960, 303104, 236673892⟩ CTN.nil) ⟨296978, 303104, 241344988⟩ CTN.nil) ⟨296994, 303104, 245534652⟩ (CTN.node CTN.nil ⟨297024, 303104, 253485503⟩ CTN.nil))))) ⟨297044, 303104, 258855000⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨297056, 303104, 262103140⟩ CTN.nil) ⟨297096, 303104, 273073316⟩ CTN.nil) ⟨297100, 303104, 274182425⟩ (CTN.node (CTN.node CTN.nil ⟨297142, 303104, 285960600⟩ CTN.nil) ⟨297144, 303104, 286527497⟩ CTN.nil)) ⟨297160, 303104, 291082386⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨297180, 303104, 296825253⟩ CTN.nil) ⟨297192, 303104, 300297219⟩ CTN.nil) ⟨297208, 303104, 304957099⟩ (CTN.node CTN.nil ⟨297236, 303104, 313195924⟩ CTN.nil))) ⟨297240, 303104, 314381622⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨297252, 303104, 317951788⟩ CTN.nil) ⟨297256, 303104, 319146199⟩ CTN.nil) ⟨297272, 303104, 323945608⟩ (CTN.node (CTN.node CTN.nil ⟨297288, 303104, 328779816⟩ CTN.nil) ⟨297300, 303104, 332428288⟩ CTN.nil)) ⟨297320, 303104, 338552489⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨297348, 303104, 347217429⟩ CTN.nil) ⟨297352, 303104, 348463941⟩ CTN.nil) ⟨297364, 303104, 352216456⟩ (CTN.node CTN.nil ⟨297412, 303104, 367420971⟩ CTN.nil)))) ⟨297416, 303104, 368702038⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨297440, 303104, 376433671⟩ CTN.nil) ⟨297514, 303104, 400759868⟩ CTN.nil) ⟨297540, 303104, 409481003⟩ (CTN.node (CTN.node CTN.nil ⟨297568, 303104, 418973928⟩ CTN.nil) ⟨297604, 303104, 431332583⟩ CTN.nil)) ⟨297668, 303104, 453728457⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨297696, 303104, 463697128⟩ CTN.nil) ⟨297792, 303104, 498659321⟩ CTN.nil) ⟨297820, 303104, 509084320⟩ (CTN.node CTN.nil ⟨297824, 303104, 510581970⟩ CTN.nil))) ⟨297892, 303104, 536361047⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨297928, 303104, 550251993⟩ CTN.nil) ⟨297992, 303104, 575360664⟩ CTN.nil) ⟨298000, 303104, 578536356⟩ (CTN.node CTN.nil ⟨298020, 303104, 586511558⟩ CTN.nil)) ⟨298024, 303104, 588112759⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨298056, 303104, 600996170⟩ CTN.nil) ⟨298080, 303104, 610744663⟩ CTN.nil) ⟨298116, 303104, 625505106⟩ (CTN.node CTN.nil ⟨298148, 303104, 638763806⟩ CTN.nil)))))) ⟨298180, 303104, 652152247⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨298184, 303104, 653834903⟩ CTN.nil) ⟨298208, 303104, 663973230⟩ CTN.nil) ⟨298276, 303104, 693091791⟩ (CTN.node (CTN.node CTN.nil ⟨298336, 303104, 719264896⟩ CTN.nil) ⟨298372, 303104, 735183605⟩ CTN.nil)) ⟨298380, 303104, 738742896⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨298436, 303104, 763879059⟩ CTN.nil) ⟨298460, 303104, 774769769⟩ CTN.nil) ⟨298560, 303104, 820904978⟩ (CTN.node CTN.nil ⟨298760, 303104, 916792057⟩ CTN.nil))) ⟨298768, 303104, 920726559⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨298848, 303104, 960485267⟩ CTN.nil) ⟨299024, 303104, 1050570332⟩ CTN.nil) ⟨299076, 303104, 1077864765⟩ (CTN.node (CTN.node CTN.nil ⟨299104, 303104, 1092688340⟩ CTN.nil) ⟨300096, 303104, 1671772511⟩ CTN.nil)) ⟨303104, 303156, 3889444660⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 303222, 3886057420⟩ CTN.nil) ⟨303104, 303236, 3885339388⟩ CTN.nil) ⟨303104, 303430, 3875406578⟩ (CTN.node CTN.nil ⟨303104, 303444, 3874691006⟩ CTN.nil)))) ⟨303104, 303462, 3873771228⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 303494, 3872136740⟩ CTN.nil) ⟨303104, 303526, 3870503114⟩ CTN.nil) ⟨303104, 303542, 3869686625⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 303762, 3858481696⟩ CTN.nil) ⟨303104, 303824, 3855331271⟩ CTN.nil)) ⟨303104, 303942, 3849344182⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 304068, 3842964014⟩ CTN.nil) ⟨303104, 304116, 3840536952⟩ CTN.nil) ⟨303104, 304132, 3839728357⟩ (CTN.node CTN.nil ⟨303104, 304162, 3838212815⟩ CTN.nil))) ⟨303104, 304180, 3837303849⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 304210, 3835789503⟩ CTN.nil) ⟨303104, 304230, 3834780354⟩ CTN.nil) ⟨303104, 304262, 3833166406⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 304294, 3831553308⟩ CTN.nil) ⟨303104, 304596, 3816371408⟩ CTN.nil)) ⟨303104, 304836, 3804359921⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 304884, 3801963297⟩ CTN.nil) ⟨303104, 304900, 3801164842⟩ CTN.nil) ⟨303104, 305136, 3789411944⟩ (CTN.node CTN.nil ⟨303104, 305316, 3780478395⟩ CTN.nil))))) ⟨303104, 305504, 3771175891⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 305552, 3768805371⟩ CTN.nil) ⟨303104, 305604, 3766239410⟩ CTN.nil) ⟨303104, 305616, 3765647575⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 305668, 3763084301⟩ CTN.nil) ⟨303104, 305680, 3762493086⟩ CTN.nil)) ⟨303104, 305712, 3760917080⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 305732, 3759932495⟩ CTN.nil) ⟨303104, 305808, 3756194011⟩ CTN.nil) ⟨303104, 305904, 3751478356⟩ (CTN.node CTN.nil ⟨303104, 305968, 3748338697⟩ CTN.nil))) ⟨303104, 306036, 3745006407⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 306048, 3744418741⟩ CTN.nil) ⟨303104, 306096, 3742069227⟩ CTN.nil) ⟨303104, 306500, 3722367008⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 306524, 3721200664⟩ CTN.nil) ⟨303104, 306528, 3721006318⟩ CTN.nil)) ⟨303104, 306652, 3714987876⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 306752, 3710143157⟩ CTN.nil) ⟨303104, 306816, 3707046681⟩ CTN.nil) ⟨303104, 306864, 3704726444⟩ (CTN.node CTN.nil ⟨303104, 306896, 3703180628⟩ CTN.nil)))) ⟨303104, 306900, 3702987457⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 306980, 3699126695⟩ CTN.nil) ⟨303104, 307140, 3691420255⟩ CTN.nil) ⟨303104, 307168, 3690073692⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 307268, 3685269550⟩ CTN.nil) ⟨303104, 307280, 3684693578⟩ CTN.nil)) ⟨303104, 307332, 3682199002⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 307344, 3681623630⟩ CTN.nil) ⟨303104, 307396, 3679131651⟩ CTN.nil) ⟨303104, 307520, 3673197744⟩ (CTN.node CTN.nil ⟨303104, 307584, 3670139764⟩ CTN.nil))) ⟨303104, 307632, 3667848367⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 307752, 3662127694⟩ CTN.nil) ⟨303104, 307808, 3659461864⟩ CTN.nil) ⟨303104, 307836, 3658129859⟩ (CTN.node CTN.nil ⟨303104, 308064, 3647306061⟩ CTN.nil)) ⟨303104, 308164, 3642571414⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 308188, 3641436242⟩ CTN.nil) ⟨303104, 308236, 3639167224⟩ CTN.nil) ⟨303104, 308352, 3633691059⟩ (CTN.node CTN.nil ⟨303104, 308388, 3631993654⟩ CTN.nil))))))) ⟨303104, 308416, 3630674135⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 308480, 3627660343⟩ CTN.nil) ⟨303104, 308576, 3623145516⟩ CTN.nil) ⟨303104, 308592, 3622393728⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 308624, 3620890736⟩ CTN.nil) ⟨303104, 308644, 3619951763⟩ CTN.nil)) ⟨303104, 308668, 3618825396⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 308676, 3618450038⟩ CTN.nil) ⟨303104, 308688, 3617887092⟩ CTN.nil) ⟨303104, 308704, 3617136668⟩ (CTN.node CTN.nil ⟨303104, 308740, 3615448924⟩ CTN.nil))) ⟨303104, 308784, 3613387463⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 308828, 3611327472⟩ CTN.nil) ⟨303104, 308832, 3611140273⟩ CTN.nil) ⟨303104, 308880, 3608894829⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 308928, 3606651130⟩ CTN.nil) ⟨303104, 308932, 3606464234⟩ CTN.nil)) ⟨303104, 308976, 3604409175⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 308992, 3603662244⟩ CTN.nil) ⟨303104, 308996, 3603475541⟩ CTN.nil) ⟨303104, 309008, 3602915506⟩ (CTN.node CTN.nil ⟨303104, 309148, 3596389796⟩ CTN.nil)))) ⟨303104, 309184, 3594714145⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 309208, 3593597587⟩ CTN.nil) ⟨303104, 309248, 3591737619⟩ CTN.nil) ⟨303104, 309296, 3589507247⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 309372, 3585979363⟩ CTN.nil) ⟨303104, 309436, 3583011876⟩ CTN.nil)) ⟨303104, 309472, 3581344013⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 309500, 3580047457⟩ CTN.nil) ⟨303104, 309548, 3577826156⟩ CTN.nil) ⟨303104, 309596, 3575606577⟩ (CTN.node CTN.nil ⟨303104, 309648, 3573203975⟩ CTN.nil))) ⟨303104, 309728, 3569511604⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 309760, 3568035991⟩ CTN.nil) ⟨303104, 309824, 3565087053⟩ CTN.nil) ⟨303104, 309888, 3562141161⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 309924, 3560485434⟩ CTN.nil) ⟨303104, 309936, 3559933739⟩ CTN.nil)) ⟨303104, 310016, 3556258500⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 310080, 3553321725⟩ CTN.nil) ⟨303104, 310092, 3552771417⟩ CTN.nil) ⟨303104, 310112, 3551854474⟩ (CTN.node CTN.nil ⟨303104, 310144, 3550387980⟩ CTN.nil))))) ⟨303104, 310160, 3549655017⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 310192, 3548189659⟩ CTN.nil) ⟨303104, 310268, 3544712462⟩ CTN.nil) ⟨303104, 310320, 3542335782⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 310332, 3541787600⟩ CTN.nil) ⟨303104, 310368, 3540143691⟩ CTN.nil)) ⟨303104, 310416, 3537953295⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 310492, 3534488634⟩ CTN.nil) ⟨303104, 310540, 3532302611⟩ CTN.nil) ⟨303104, 310592, 3529936328⟩ (CTN.node CTN.nil ⟨303104, 310656, 3527026698⟩ CTN.nil))) ⟨303104, 310672, 3526299759⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 310704, 3524846443⟩ CTN.nil) ⟨303104, 310800, 3520490986⟩ CTN.nil) ⟨303104, 310812, 3519947027⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 310824, 3519403173⟩ CTN.nil) ⟨303104, 310848, 3518315780⟩ CTN.nil)) ⟨303104, 310872, 3517228808⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 310908, 3515599136⟩ CTN.nil) ⟨303104, 310912, 3515418119⟩ CTN.nil) ⟨303104, 310960, 3513246831⟩ (CTN.node CTN.nil ⟨303104, 310972, 3512704271⟩ CTN.nil)))) ⟨303104, 311036, 3509812386⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨303104, 311088, 3507464920⟩ CTN.nil) ⟨303104, 311100, 3506923476⟩ CTN.nil) ⟨303104, 311136, 3505299771⟩ (CTN.node (CTN.node CTN.nil ⟨303104, 311260, 3499714197⟩ CTN.nil) ⟨303104, 311296, 3498094663⟩ CTN.nil)) ⟨311296, 311308, 7694996611⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 311392, 7686051254⟩ CTN.nil) ⟨311296, 311424, 7682384680⟩ CTN.nil) ⟨311296, 311516, 7671050236⟩ (CTN.node CTN.nil ⟨311296, 311680, 7647939783⟩ CTN.nil))) ⟨311296, 311952, 7601477490⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 312184, 7553934313⟩ CTN.nil) ⟨311296, 312232, 7543199228⟩ CTN.nil) ⟨311296, 312508, 7475575871⟩ (CTN.node CTN.nil ⟨311296, 312572, 7458475179⟩ CTN.nil)) ⟨311296, 312672, 7430698629⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 312764, 7404014908⟩ CTN.nil) ⟨311296, 312796, 7394481723⟩ CTN.nil) ⟨311296, 312840, 7381162472⟩ (CTN.node CTN.nil ⟨311296, 312844, 7379939541⟩ CTN.nil)))))) ⟨311296, 312952, 7346162789⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 313080, 7304254818⟩ CTN.nil) ⟨311296, 313276, 7236200800⟩ CTN.nil) ⟨311296, 313532, 7140399025⟩ (CTN.node (CTN.node CTN.nil ⟨311296, 313560, 7129454955⟩ CTN.nil) ⟨311296, 313720, 7065190113⟩ CTN.nil)) ⟨311296, 313848, 7011692538⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 313944, 6970375320⟩ CTN.nil) ⟨311296, 313992, 6949338187⟩ CTN.nil) ⟨311296, 314152, 6877420943⟩ (CTN.node CTN.nil ⟨311296, 314200, 6855315200⟩ CTN.nil))) ⟨311296, 315256, 6311610279⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 315280, 6298073333⟩ CTN.nil) ⟨311296, 315480, 6183422759⟩ CTN.nil) ⟨311296, 315512, 6164780109⟩ (CTN.node (CTN.node CTN.nil ⟨311296, 315528, 6155428585⟩ CTN.nil) ⟨311296, 315744, 6027260879⟩ CTN.nil)) ⟨311296, 315912, 5925195688⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 316024, 5856053822⟩ CTN.nil) ⟨311296, 316152, 5776006080⟩ CTN.nil) ⟨311296, 316280, 5694907543⟩ (CTN.node CTN.nil ⟨311296, 316632, 5466867682⟩ CTN.nil)))) ⟨311296, 316792, 5360986259⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 316920, 5275372985⟩ CTN.nil) ⟨311296, 317272, 5036210458⟩ CTN.nil) ⟨311296, 317480, 4892644623⟩ (CTN.node (CTN.node CTN.nil ⟨311296, 318352, 4278191046⟩ CTN.nil) ⟨311296, 318552, 4135533285⟩ CTN.nil)) ⟨311296, 318584, 4112682170⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 318600, 4101254723⟩ CTN.nil) ⟨311296, 318856, 3918331670⟩ CTN.nil) ⟨311296, 319072, 3764072198⟩ (CTN.node CTN.nil ⟨311296, 319240, 3644313518⟩ CTN.nil))) ⟨311296, 319352, 3564645100⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨311296, 319480, 3473813401⟩ CTN.nil) ⟨311296, 319488, 3468145225⟩ CTN.nil) ⟨319488, 319960, 3441396271⟩ (CTN.node CTN.nil ⟨319488, 320120, 3321645605⟩ CTN.nil)) ⟨319488, 320248, 3226450986⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨319488, 320600, 2967880823⟩ CTN.nil) ⟨319488, 321880, 2081621181⟩ CTN.nil) ⟨319488, 321928, 2050428903⟩ (CTN.node CTN.nil ⟨319488, 322184, 1886990282⟩ CTN.nil))))) ⟨319488, 322400, 1753085620⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨319488, 322680, 1585275186⟩ CTN.nil) ⟨319488, 322808, 1510828826⟩ CTN.nil) ⟨319488, 322848, 1487864743⟩ (CTN.node (CTN.node CTN.nil ⟨319488, 323288, 1245054427⟩ CTN.nil) ⟨319488, 323448, 1161373428⟩ CTN.nil)) ⟨319488, 323576, 1096267502⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨319488, 324568, 650268299⟩ CTN.nil) ⟨319488, 325208, 421041230⟩ CTN.nil) ⟨319488, 325264, 403269334⟩ (CTN.node CTN.nil ⟨319488, 326432, 119142818⟩ CTN.nil))) ⟨319488, 327280, 18139488⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨327896, 335872, 14001⟩ CTN.nil) ⟨327924, 335872, 109955⟩ CTN.nil) ⟨327960, 335872, 367049⟩ (CTN.node (CTN.node CTN.nil ⟨327984, 335872, 622063⟩ CTN.nil) ⟨328212, 335872, 6385231⟩ CTN.nil)) ⟨328248, 335872, 7848312⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨328284, 335872, 9462349⟩ CTN.nil) ⟨328376, 335872, 14273065⟩ CTN.nil) ⟨328728, 335872, 41781288⟩ (CTN.node CTN.nil ⟨329168, 335872, 96403325⟩ CTN.nil)))) ⟨329232, 335872, 106211584⟩ (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨329496, 335872, 151635305⟩ CTN.nil) ⟨329588, 335872, 169332767⟩ CTN.nil) ⟨329936, 335872, 244916797⟩ (CTN.node (CTN.node CTN.nil ⟨335872, 338292, 3092045363⟩ CTN.nil) ⟨335872, 338580, 3081533279⟩ CTN.nil)) ⟨335872, 339376, 3052710541⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨335872, 339792, 3037781477⟩ CTN.nil) ⟨335872, 340560, 3010459128⟩ CTN.nil) ⟨335872, 341040, 2993538576⟩ (CTN.node CTN.nil ⟨335872, 341328, 2983443296⟩ CTN.nil))) ⟨335872, 341364, 2982184380⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨335872, 341708, 2970188170⟩ CTN.nil) ⟨335872, 344064, 2889629010⟩ CTN.nil) ⟨344064, 344392, 6268599833⟩ (CTN.node CTN.nil ⟨344064, 351560, 3273569067⟩ CTN.nil)) ⟨344064, 352256, 2866362512⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨352256, 354888, 1582117934⟩ CTN.nil) ⟨352256, 357416, 507732170⟩ CTN.nil) ⟨352256, 359488, 60563652⟩ (CTN.node CTN.nil ⟨352256, 360256, 5298027⟩ CTN.nil))))))))

noncomputable def table : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node tab0 ⟨96608, 98304, 312050644⟩ tab1) ⟨102144, 106496, 5576516022⟩ (CTN.node tab2 ⟨131712, 133920, 7434408⟩ tab3)) ⟨132790, 137332, 509757185⟩ (CTN.node (CTN.node tab4 ⟨139264, 139500, 17486088980⟩ tab5) ⟨164272, 171328, 221179⟩ (CTN.node tab6 ⟨164803, 167122, 76257770⟩ tab7))) ⟨165494, 168597, 366900306⟩ (CTN.node (CTN.node (CTN.node tab8 ⟨166528, 171264, 1148273930⟩ tab9) ⟨172032, 175872, 10731190103⟩ (CTN.node tab10 ⟨197012, 200722, 815654⟩ tab11)) ⟨197524, 202962, 53710199⟩ (CTN.node (CTN.node tab12 ⟨198034, 203472, 187565689⟩ tab13) ⟨198592, 202816, 434106245⟩ (CTN.node tab14 ⟨199424, 204800, 942451069⟩ tab15)))) ⟨204800, 205596, 8235234748⟩ (CTN.node (CTN.node (CTN.node (CTN.node tab16 ⟨212992, 213504, 16264029169⟩ tab17) ⟨229904, 237568, 6678975⟩ (CTN.node tab18 ⟨230404, 235330, 65456388⟩ tab19)) ⟨230822, 236548, 156913362⟩ (CTN.node (CTN.node tab20 ⟨231292, 235776, 313942050⟩ tab21) ⟨231849, 235223, 569533418⟩ (CTN.node tab22 ⟨233138, 237568, 1367016756⟩ tab23))) ⟨237568, 240116, 6004310295⟩ (CTN.node (CTN.node (CTN.node tab24 ⟨245760, 246592, 12113034436⟩ tab25) ⟨262660, 269250, 6361312⟩ (CTN.node tab26 ⟨263400, 269348, 91342837⟩ tab27)) ⟨264468, 270258, 382438769⟩ (CTN.node (CTN.node tab28 ⟨270336, 271568, 4781349269⟩ tab29) ⟨270336, 278304, 4334673510⟩ (CTN.node tab30 ⟨296332, 303104, 101996445⟩ tab31)))))

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

theorem cover0_ok : SixW15C.coverCheck table 25715100 (SC / 2) 401408 cover0 = true := by decide +kernel

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

theorem cover1_ok : SixW15C.coverCheck table 48318100 (SC / 2) 237568 cover1 = true := by decide +kernel

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

theorem cover2_ok : SixW15C.coverCheck table 52857300 (SC / 2) 221184 cover2 = true := by decide +kernel

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

theorem cover3_ok : SixW15C.coverCheck table 48170700 (SC / 2) 237568 cover3 = true := by decide +kernel

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

theorem cover4_ok : SixW15C.coverCheck table 24938600 (SC / 2) 409600 cover4 = true := by decide +kernel

def bits : ℕ := 1012176073664863210891225084274042669998301567624084427068009972607261709429996921378645742978657817128953815516393166915676536272480430579471293776939736974495906003060448714844145280375207136596818794867570973056632115307664450943238433112864840767105865617298139922138084618674238121422300901194184985467622771540046146166828033833513480923007206838790212983650625888935752116561838471816641823319321920893300868910488230780189837912899034791418760778539207070707387616840473336478541080665181798575018620670223844583560993184086734651224095333382522147759205062486345454832944037165670559764450733750993527523287588061373974979764912887667428050593635930487531619199725902468679817111134034058211024682632097647937052126376570381189215581667240292027787437936042253518123367807340735920886842614898893967582790982593481208566039503038443829368489764227156434312868282157483303518069135618934033127598023441517622714298797244576337042376446955087075752965290086775336310348671327624988776843640448360654324296742710079195407613475528969235114918303116395758708660069765717032238907305205087109405631968518912532782455620759217187246932656067080621076156389764542552806293989986396908870636045759075528296878241246284519386991883683325219458711312953398351809886615973158456827400234793862933523085017925223723208860044751771747465762547494744584629538937506445176670309498804913831425882518477005990494004101753966112585789688339567497299051972262568782359900726759493163074031956516591153113179622302766000807124715537098872386266657242531009855633101009834261064961344430480567092865338716114944460991619522019145755330310698398585646570682277727878169933741789186526159439444157571383288347506631952720142514103373492421510198127969857827975916863941566913659833935377438909621103987335280607588321276205021756848317547024397747695653457415601666519425297497512451081237600554116245576133199994444838825625182530255667438579687827718966727821126873631494218898071881177121491939776337942973594583801636684153205318300124909162046006332146406535124458149816226839503791887473581749182743781672432597445512496480467834656695091163170263640240404321342115013001757071665234124018302088320183231422100625475230212389318165765099375955362490228282051949467907708225120191516979204582255645036761428862415821332036687174511392802855271774779745483047366044986212593154995759693637935374242461055574016655367707612569704595398164885019490553777067256139773750274063893661619464385074515940744868986519115192892217626747823283099079895469917418157449411778493856055857002511298853157508167807600327466462229995787752578040986026531464260756977276466814746478677242247173234273663400822805364316184137301677137722661693800910625996118272352382093624511116445101932391435925723622823273692391772946465888884728131022487451422167975112147825241479572709283898243335163325356093845275903735743677294958699048033551062986635439410177469270837161738023576324938418864499293352722794458948592160573044121777293527417434127296528977006866816362578008296779057475084472729177163643146389046301759145455354282141699209301937119914457486155295485129920986493778787448320047242677834874048284144139825585624833691082500748624829457826384870333860817171632337845217586202242008292845160871776746301716397560558218104123403224764045882127944739238560818586056658584057868580724611499733046335826384661269798832085331995589842653572079313971312155218649163971334877739944170381704938572295608956940187837489795588956732719941058865443253429167360015215608889063332384904269514232423390452315666253809185920831995509202956001570275777687709797527782278364701135381951015671661889009856529247985112818516405275114163843130560842779829888227012514105880060573764928404829035932707910964285849331775671882842845931948784237653195729030500231878293491063093208259042114066586220488776162051781766439074520684015753376097306740875516793406433087153778408134615921928300089220544351676756696575650588025349906841602503397754066768239671688000055415895589461577138150938529305073749846417276897218518950973868812491565116031382518418399045078855791942843080180118860812961888129124106726018544606608883823651560049485500546844708599649363956447436418899707819655730475347541559810298328047545737891611468269540007507138401516126264251296904146807997441450257662504375983591008724554427037888752151758879415919351673601539155607027630798022912637369680022565450508840236318731712407928210357983967795984072885024155854334787929679567283012945475804844867806700280812963314835573263509295053309104904192789255903031332169647874620781361454975376190047313171300262687627755251802793512201530458945218908178689288994325577964412415657350196952017383585795535309747421080702821269470612662694660176264642119952476265126751848231269801641920970030574834614069699064038230914413198590400066546704959034399202172069642613078706280167824222743444201537830907730472849668728784668886774937652953126222643157921834522103703950466409711570496267720836805996890795892243299155218790247640955425456537019990212972776779524949782806877050953901948284274585891499831178629933345544376155668042524570669216124851028061670353058639811899193987559762812120251568200011846558623298021971460082368447111369045650283637672642971992086322039550682048311268194811074815697494160095753825120676341044416016452284580294688491941718861699273311509239668030888316394801129050863044805238722187557709987051467314865311524653700097266520325848920022303212063016520078070890486684427321464031118308534711846631113612219692227474713962186804053389808878766274867474379327091911706840413551402450510503401128875836581240010515493779331980011096153601793420595407913987090066869720272006559748804013459103184747791200050879339441092605004042904588292164891188382010363894294710367069521507611017200056070984736469540751983470567671647572672610809258210646543387127847769034695004537838466993300806802458815708385610551530647063860995773771413562135749557711888691233663289541799431935153945253703539991740636338080366374222576105656086238087490652548526263005034175629226065556791172509537967460813524414053785541939772049906911965164900167688612075605037310561566601575883031978309755488961666886833983119954736597374677549529680033373559035926143624766053633413778291413856818846341952224140617320925454544714757429700073133864881320014141448947047021239691842038495937382926033754077699798293551271229542274105659649570338532691571959060734131932504314662227455108499772866784302056465975573181863644199679664484880768449167920803646297926168891633304249078491962724286514204205944884898850727707082814691045761067322870903222708364047483127121282746520121991012630541036415599931236841449786854185738161755436158929019738722444504695346711581482576096926460945681156653663551649691402574706105200163569274615606147389954211988257800728807224945820498510931888649166110174781967650707673732525736583951244273395135559261855614852581440931185211916427347700817317933912022011942346188431601412957245726246911640865968510882529123607047732167810316922291352813900956457876633588042775944274749218470890533599485386104536857245226721406897104814340791472860659959623243680050440378055786561877559765976391009018124768793130575176243301484596783957836677031699097794589519601158977479551819868821457093507897058573036715085882840826497421980629973346556608795385910983024266733458814530212624324743959884483141457860395402694162442003282754742606142714132223936062050793855181756007114985188264713230733676847760621913049883187080045847839129581322452195173421116334717989842730362917259187570905975306857630071472631784360617068593580218690449488752853765242106279673833982421139942484108125172584980769664328806450603114551767062177256030259624259530373284414052694160023897049416965863321541986653025280608502564265473683140440804325112484583952858788521589589121671340558029264951063332322848762901279570899630584794061285667121661259728092301355203957821807465542554191766296425707555342016700137423814433327804222866666477255189322033822626663227564853194608055334513639044937083586799045903038393735851044801450917117959492299687792485594104266295609612525032652033990079300874256220578493920069181009572062886293269735040512149099929741947116692226457504405635100419965401470150161464224357907091391631248921210522725173987745302313712965576094092733667786989468277987861691002315350465390436897727619330521009866244701412334812972493279591766372841374906816108704118459394341131818885150077429046043473223118871323207601172356303987916155550761524089956279824312951886586886969253938180210809647485488647657886357384395156389479492351

theorem wk0 : SixW15C.walk table bits 64 0 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936) = some 581 := by decide +kernel

theorem wk1 : SixW15C.walk table bits 64 581 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 409600) = some 2468 := by decide +kernel

theorem wk2 : SixW15C.walk table bits 64 2468 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936) = some 3407 := by decide +kernel

theorem wk3 : SixW15C.walk table bits 64 3407 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 409600) = some 4744 := by decide +kernel

theorem wk4 : SixW15C.walk table bits 64 4744 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936) = some 5149 := by decide +kernel

theorem wk5 : SixW15C.walk table bits 64 5149 (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 409600) = some 5398 := by decide +kernel

theorem wk6 : SixW15C.walk table bits 64 5398 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936) = some 6189 := by decide +kernel

theorem wk7 : SixW15C.walk table bits 64 6189 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 409600) = some 7458 := by decide +kernel

theorem wk8 : SixW15C.walk table bits 64 7458 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936) = some 7937 := by decide +kernel

theorem wk9 : SixW15C.walk table bits 64 7937 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 409600) = some 8158 := by decide +kernel

theorem wk10 : SixW15C.walk table bits 64 8158 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936) = some 8215 := by decide +kernel

theorem wk11 : SixW15C.walk table bits 64 8215 (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 409600) = some 8216 := by decide +kernel

theorem wk12 : SixW15C.walk table bits 64 8216 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936) = some 8499 := by decide +kernel

theorem wk13 : SixW15C.walk table bits 64 8499 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 409600) = some 8664 := by decide +kernel

theorem wk14 : SixW15C.walk table bits 64 8664 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936) = some 8695 := by decide +kernel

theorem wk15 : SixW15C.walk table bits 64 8695 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 409600) = some 8696 := by decide +kernel

theorem wk16 : SixW15C.walk table bits 64 8696 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936) = some 8697 := by decide +kernel

theorem wk17 : SixW15C.walk table bits 64 8697 (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 409600) = some 8698 := by decide +kernel

theorem wk18 : SixW15C.walk table bits 64 8698 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936) = some 9669 := by decide +kernel

theorem wk19 : SixW15C.walk table bits 64 9669 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 409600) = some 11470 := by decide +kernel

theorem wk20 : SixW15C.walk table bits 64 11470 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936) = some 12221 := by decide +kernel

theorem wk21 : SixW15C.walk table bits 64 12221 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 409600) = some 12614 := by decide +kernel

theorem wk22 : SixW15C.walk table bits 64 12614 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936) = some 12699 := by decide +kernel

theorem wk23 : SixW15C.walk table bits 64 12699 (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 409600) = some 12722 := by decide +kernel

theorem wk24 : SixW15C.walk table bits 64 12722 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936) = some 13229 := by decide +kernel

theorem wk25 : SixW15C.walk table bits 64 13229 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 409600) = some 13476 := by decide +kernel

theorem wk26 : SixW15C.walk table bits 64 13476 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936) = some 13549 := by decide +kernel

theorem wk27 : SixW15C.walk table bits 64 13549 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 409600) = some 13550 := by decide +kernel

theorem wk28 : SixW15C.walk table bits 64 13550 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936) = some 13551 := by decide +kernel

theorem wk29 : SixW15C.walk table bits 64 13551 (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 409600) = some 13552 := by decide +kernel

theorem wk30 : SixW15C.walk table bits 64 13552 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936) = some 13585 := by decide +kernel

theorem wk31 : SixW15C.walk table bits 64 13585 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 409600) = some 13586 := by decide +kernel

theorem wk32 : SixW15C.walk table bits 64 13586 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936) = some 13587 := by decide +kernel

theorem wk33 : SixW15C.walk table bits 64 13587 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 409600) = some 13588 := by decide +kernel

theorem wk34 : SixW15C.walk table bits 64 13588 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936) = some 13589 := by decide +kernel

theorem wk35 : SixW15C.walk table bits 64 13589 (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 409600) = some 13590 := by decide +kernel

theorem wk36 : SixW15C.walk table bits 64 13590 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936) = some 14017 := by decide +kernel

theorem wk37 : SixW15C.walk table bits 64 14017 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 409600) = some 14294 := by decide +kernel

theorem wk38 : SixW15C.walk table bits 64 14294 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936) = some 14377 := by decide +kernel

theorem wk39 : SixW15C.walk table bits 64 14377 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 409600) = some 14400 := by decide +kernel

theorem wk40 : SixW15C.walk table bits 64 14400 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936) = some 14401 := by decide +kernel

theorem wk41 : SixW15C.walk table bits 64 14401 (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 409600) = some 14402 := by decide +kernel

theorem wk42 : SixW15C.walk table bits 64 14402 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936) = some 14453 := by decide +kernel

theorem wk43 : SixW15C.walk table bits 64 14453 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 409600) = some 14454 := by decide +kernel

theorem wk44 : SixW15C.walk table bits 64 14454 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936) = some 14455 := by decide +kernel

theorem wk45 : SixW15C.walk table bits 64 14455 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 409600) = some 14456 := by decide +kernel

theorem wk46 : SixW15C.walk table bits 64 14456 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936) = some 14457 := by decide +kernel

theorem wk47 : SixW15C.walk table bits 64 14457 (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 409600) = some 14458 := by decide +kernel

theorem wk48 : SixW15C.walk table bits 64 14458 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936) = some 14459 := by decide +kernel

theorem wk49 : SixW15C.walk table bits 64 14459 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 409600) = some 14460 := by decide +kernel

theorem wk50 : SixW15C.walk table bits 64 14460 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936) = some 14461 := by decide +kernel

theorem wk51 : SixW15C.walk table bits 64 14461 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 409600) = some 14462 := by decide +kernel

theorem wk52 : SixW15C.walk table bits 64 14462 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936) = some 14463 := by decide +kernel

theorem wk53 : SixW15C.walk table bits 64 14463 (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 409600) = some 14464 := by decide +kernel

theorem wk54 : SixW15C.walk table bits 64 14464 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936) = some 16343 := by decide +kernel

theorem wk55 : SixW15C.walk table bits 64 16343 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) = some 19626 := by decide +kernel

theorem wk56 : SixW15C.walk table bits 64 19626 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936) = some 21381 := by decide +kernel

theorem wk57 : SixW15C.walk table bits 64 21381 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 409600) = some 22442 := by decide +kernel

theorem wk58 : SixW15C.walk table bits 64 22442 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936) = some 22721 := by decide +kernel

theorem wk59 : SixW15C.walk table bits 64 22721 (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 409600) = some 22780 := by decide +kernel

theorem wk60 : SixW15C.walk table bits 64 22780 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936) = some 24123 := by decide +kernel

theorem wk61 : SixW15C.walk table bits 64 24123 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 409600) = some 24978 := by decide +kernel

theorem wk62 : SixW15C.walk table bits 64 24978 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936) = some 25209 := by decide +kernel

theorem wk63 : SixW15C.walk table bits 64 25209 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 409600) = some 25250 := by decide +kernel

theorem wk64 : SixW15C.walk table bits 64 25250 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936) = some 25251 := by decide +kernel

theorem wk65 : SixW15C.walk table bits 64 25251 (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 409600) = some 25252 := by decide +kernel

theorem wk66 : SixW15C.walk table bits 64 25252 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936) = some 25409 := by decide +kernel

theorem wk67 : SixW15C.walk table bits 64 25409 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 409600) = some 25442 := by decide +kernel

theorem wk68 : SixW15C.walk table bits 64 25442 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936) = some 25443 := by decide +kernel

theorem wk69 : SixW15C.walk table bits 64 25443 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 409600) = some 25444 := by decide +kernel

theorem wk70 : SixW15C.walk table bits 64 25444 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936) = some 25445 := by decide +kernel

theorem wk71 : SixW15C.walk table bits 64 25445 (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 409600) = some 25446 := by decide +kernel

theorem wk72 : SixW15C.walk table bits 64 25446 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936) = some 26717 := by decide +kernel

theorem wk73 : SixW15C.walk table bits 64 26717 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 409600) = some 27786 := by decide +kernel

theorem wk74 : SixW15C.walk table bits 64 27786 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936) = some 28155 := by decide +kernel

theorem wk75 : SixW15C.walk table bits 64 28155 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 409600) = some 28206 := by decide +kernel

theorem wk76 : SixW15C.walk table bits 64 28206 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936) = some 28225 := by decide +kernel

theorem wk77 : SixW15C.walk table bits 64 28225 (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 409600) = some 28226 := by decide +kernel

theorem wk78 : SixW15C.walk table bits 64 28226 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936) = some 28461 := by decide +kernel

theorem wk79 : SixW15C.walk table bits 64 28461 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 409600) = some 28500 := by decide +kernel

theorem wk80 : SixW15C.walk table bits 64 28500 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936) = some 28501 := by decide +kernel

theorem wk81 : SixW15C.walk table bits 64 28501 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 409600) = some 28502 := by decide +kernel

theorem wk82 : SixW15C.walk table bits 64 28502 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936) = some 28503 := by decide +kernel

theorem wk83 : SixW15C.walk table bits 64 28503 (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 409600) = some 28504 := by decide +kernel

theorem wk84 : SixW15C.walk table bits 64 28504 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936) = some 28505 := by decide +kernel

theorem wk85 : SixW15C.walk table bits 64 28505 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 409600) = some 28506 := by decide +kernel

theorem wk86 : SixW15C.walk table bits 64 28506 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936) = some 28507 := by decide +kernel

theorem wk87 : SixW15C.walk table bits 64 28507 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 409600) = some 28508 := by decide +kernel

theorem wk88 : SixW15C.walk table bits 64 28508 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936) = some 28509 := by decide +kernel

theorem wk89 : SixW15C.walk table bits 64 28509 (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 409600) = some 28510 := by decide +kernel

theorem wk90 : SixW15C.walk table bits 64 28510 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936) = some 28773 := by decide +kernel

theorem wk91 : SixW15C.walk table bits 64 28773 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 409600) = some 28832 := by decide +kernel

theorem wk92 : SixW15C.walk table bits 64 28832 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936) = some 28851 := by decide +kernel

theorem wk93 : SixW15C.walk table bits 64 28851 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 409600) = some 28852 := by decide +kernel

theorem wk94 : SixW15C.walk table bits 64 28852 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936) = some 28853 := by decide +kernel

theorem wk95 : SixW15C.walk table bits 64 28853 (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 409600) = some 28854 := by decide +kernel

theorem wk96 : SixW15C.walk table bits 64 28854 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936) = some 28855 := by decide +kernel

theorem wk97 : SixW15C.walk table bits 64 28855 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 409600) = some 28856 := by decide +kernel

theorem wk98 : SixW15C.walk table bits 64 28856 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936) = some 28857 := by decide +kernel

theorem wk99 : SixW15C.walk table bits 64 28857 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 409600) = some 28858 := by decide +kernel

theorem wk100 : SixW15C.walk table bits 64 28858 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936) = some 28859 := by decide +kernel

theorem wk101 : SixW15C.walk table bits 64 28859 (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 409600) = some 28860 := by decide +kernel

theorem wk102 : SixW15C.walk table bits 64 28860 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936) = some 28861 := by decide +kernel

theorem wk103 : SixW15C.walk table bits 64 28861 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 409600) = some 28862 := by decide +kernel

theorem wk104 : SixW15C.walk table bits 64 28862 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936) = some 28863 := by decide +kernel

theorem wk105 : SixW15C.walk table bits 64 28863 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 409600) = some 28864 := by decide +kernel

theorem wk106 : SixW15C.walk table bits 64 28864 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936) = some 28865 := by decide +kernel

theorem wk107 : SixW15C.walk table bits 64 28865 (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 409600) = some 28866 := by decide +kernel

theorem nb0_eq : (SixW15C.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW15C.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW15C.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW15C.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW15C.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW15C.walk table bits 64 0 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 0 0) = some 581 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 0 0 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk0

theorem root_00001 : SixW15C.walk table bits 64 581 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 0 1) = some 2468 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 0 1 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk1

theorem root_00010 : SixW15C.walk table bits 64 2468 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 1 0) = some 3407 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 1 0 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk2

theorem root_00011 : SixW15C.walk table bits 64 3407 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 1 1) = some 4744 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 1 1 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk3

theorem root_00020 : SixW15C.walk table bits 64 4744 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 2 0) = some 5149 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 2 0 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk4

theorem root_00021 : SixW15C.walk table bits 64 5149 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 2 1) = some 5398 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 0 2 1 = (SixW15C.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk5

theorem root_00100 : SixW15C.walk table bits 64 5398 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 0 0) = some 6189 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 0 0 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk6

theorem root_00101 : SixW15C.walk table bits 64 6189 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 0 1) = some 7458 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 0 1 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk7

theorem root_00110 : SixW15C.walk table bits 64 7458 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 1 0) = some 7937 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 1 0 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk8

theorem root_00111 : SixW15C.walk table bits 64 7937 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 1 1) = some 8158 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 1 1 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk9

theorem root_00120 : SixW15C.walk table bits 64 8158 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 2 0) = some 8215 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 2 0 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk10

theorem root_00121 : SixW15C.walk table bits 64 8215 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 2 1) = some 8216 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 1 2 1 = (SixW15C.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk11

theorem root_00200 : SixW15C.walk table bits 64 8216 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 0 0) = some 8499 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 0 0 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk12

theorem root_00201 : SixW15C.walk table bits 64 8499 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 0 1) = some 8664 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 0 1 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk13

theorem root_00210 : SixW15C.walk table bits 64 8664 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 1 0) = some 8695 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 1 0 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk14

theorem root_00211 : SixW15C.walk table bits 64 8695 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 1 1) = some 8696 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 1 1 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk15

theorem root_00220 : SixW15C.walk table bits 64 8696 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 2 0) = some 8697 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 2 0 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk16

theorem root_00221 : SixW15C.walk table bits 64 8697 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 2 1) = some 8698 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 0 2 2 1 = (SixW15C.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk17

theorem root_01000 : SixW15C.walk table bits 64 8698 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 0 0) = some 9669 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 0 0 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk18

theorem root_01001 : SixW15C.walk table bits 64 9669 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 0 1) = some 11470 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 0 1 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk19

theorem root_01010 : SixW15C.walk table bits 64 11470 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 1 0) = some 12221 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 1 0 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk20

theorem root_01011 : SixW15C.walk table bits 64 12221 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 1 1) = some 12614 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 1 1 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk21

theorem root_01020 : SixW15C.walk table bits 64 12614 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 2 0) = some 12699 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 2 0 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk22

theorem root_01021 : SixW15C.walk table bits 64 12699 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 2 1) = some 12722 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 0 2 1 = (SixW15C.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk23

theorem root_01100 : SixW15C.walk table bits 64 12722 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 0 0) = some 13229 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 0 0 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk24

theorem root_01101 : SixW15C.walk table bits 64 13229 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 0 1) = some 13476 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 0 1 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk25

theorem root_01110 : SixW15C.walk table bits 64 13476 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 1 0) = some 13549 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 1 0 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk26

theorem root_01111 : SixW15C.walk table bits 64 13549 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 1 1) = some 13550 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 1 1 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk27

theorem root_01120 : SixW15C.walk table bits 64 13550 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 2 0) = some 13551 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 2 0 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk28

theorem root_01121 : SixW15C.walk table bits 64 13551 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 2 1) = some 13552 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 1 2 1 = (SixW15C.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk29

theorem root_01200 : SixW15C.walk table bits 64 13552 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 0 0) = some 13585 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 0 0 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk30

theorem root_01201 : SixW15C.walk table bits 64 13585 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 0 1) = some 13586 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 0 1 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk31

theorem root_01210 : SixW15C.walk table bits 64 13586 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 1 0) = some 13587 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 1 0 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk32

theorem root_01211 : SixW15C.walk table bits 64 13587 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 1 1) = some 13588 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 1 1 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk33

theorem root_01220 : SixW15C.walk table bits 64 13588 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 2 0) = some 13589 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 2 0 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk34

theorem root_01221 : SixW15C.walk table bits 64 13589 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 2 1) = some 13590 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 1 2 2 1 = (SixW15C.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk35

theorem root_02000 : SixW15C.walk table bits 64 13590 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 0 0) = some 14017 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 0 0 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk36

theorem root_02001 : SixW15C.walk table bits 64 14017 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 0 1) = some 14294 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 0 1 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk37

theorem root_02010 : SixW15C.walk table bits 64 14294 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 1 0) = some 14377 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 1 0 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk38

theorem root_02011 : SixW15C.walk table bits 64 14377 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 1 1) = some 14400 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 1 1 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk39

theorem root_02020 : SixW15C.walk table bits 64 14400 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 2 0) = some 14401 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 2 0 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk40

theorem root_02021 : SixW15C.walk table bits 64 14401 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 2 1) = some 14402 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 0 2 1 = (SixW15C.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk41

theorem root_02100 : SixW15C.walk table bits 64 14402 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 0 0) = some 14453 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 0 0 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk42

theorem root_02101 : SixW15C.walk table bits 64 14453 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 0 1) = some 14454 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 0 1 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk43

theorem root_02110 : SixW15C.walk table bits 64 14454 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 1 0) = some 14455 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 1 0 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk44

theorem root_02111 : SixW15C.walk table bits 64 14455 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 1 1) = some 14456 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 1 1 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk45

theorem root_02120 : SixW15C.walk table bits 64 14456 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 2 0) = some 14457 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 2 0 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk46

theorem root_02121 : SixW15C.walk table bits 64 14457 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 2 1) = some 14458 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 1 2 1 = (SixW15C.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk47

theorem root_02200 : SixW15C.walk table bits 64 14458 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 0 0) = some 14459 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 0 0 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk48

theorem root_02201 : SixW15C.walk table bits 64 14459 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 0 1) = some 14460 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 0 1 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk49

theorem root_02210 : SixW15C.walk table bits 64 14460 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 1 0) = some 14461 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 1 0 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk50

theorem root_02211 : SixW15C.walk table bits 64 14461 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 1 1) = some 14462 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 1 1 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk51

theorem root_02220 : SixW15C.walk table bits 64 14462 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 2 0) = some 14463 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 2 0 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk52

theorem root_02221 : SixW15C.walk table bits 64 14463 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 2 1) = some 14464 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 0 2 2 2 1 = (SixW15C.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk53

theorem root_10000 : SixW15C.walk table bits 64 14464 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 0 0) = some 16343 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 0 0 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk54

theorem root_10001 : SixW15C.walk table bits 64 16343 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 0 1) = some 19626 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 0 1 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk55

theorem root_10010 : SixW15C.walk table bits 64 19626 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 1 0) = some 21381 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 1 0 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk56

theorem root_10011 : SixW15C.walk table bits 64 21381 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 1 1) = some 22442 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 1 1 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk57

theorem root_10020 : SixW15C.walk table bits 64 22442 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 2 0) = some 22721 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 2 0 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk58

theorem root_10021 : SixW15C.walk table bits 64 22721 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 2 1) = some 22780 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 0 2 1 = (SixW15C.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk59

theorem root_10100 : SixW15C.walk table bits 64 22780 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 0 0) = some 24123 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 0 0 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk60

theorem root_10101 : SixW15C.walk table bits 64 24123 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 0 1) = some 24978 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 0 1 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk61

theorem root_10110 : SixW15C.walk table bits 64 24978 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 1 0) = some 25209 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 1 0 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk62

theorem root_10111 : SixW15C.walk table bits 64 25209 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 1 1) = some 25250 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 1 1 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk63

theorem root_10120 : SixW15C.walk table bits 64 25250 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 2 0) = some 25251 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 2 0 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk64

theorem root_10121 : SixW15C.walk table bits 64 25251 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 2 1) = some 25252 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 1 2 1 = (SixW15C.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk65

theorem root_10200 : SixW15C.walk table bits 64 25252 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 0 0) = some 25409 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 0 0 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk66

theorem root_10201 : SixW15C.walk table bits 64 25409 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 0 1) = some 25442 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 0 1 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk67

theorem root_10210 : SixW15C.walk table bits 64 25442 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 1 0) = some 25443 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 1 0 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk68

theorem root_10211 : SixW15C.walk table bits 64 25443 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 1 1) = some 25444 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 1 1 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk69

theorem root_10220 : SixW15C.walk table bits 64 25444 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 2 0) = some 25445 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 2 0 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk70

theorem root_10221 : SixW15C.walk table bits 64 25445 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 2 1) = some 25446 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 0 2 2 1 = (SixW15C.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk71

theorem root_11000 : SixW15C.walk table bits 64 25446 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 0 0) = some 26717 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 0 0 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk72

theorem root_11001 : SixW15C.walk table bits 64 26717 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 0 1) = some 27786 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 0 1 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk73

theorem root_11010 : SixW15C.walk table bits 64 27786 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 1 0) = some 28155 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 1 0 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk74

theorem root_11011 : SixW15C.walk table bits 64 28155 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 1 1) = some 28206 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 1 1 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk75

theorem root_11020 : SixW15C.walk table bits 64 28206 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 2 0) = some 28225 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 2 0 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk76

theorem root_11021 : SixW15C.walk table bits 64 28225 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 2 1) = some 28226 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 0 2 1 = (SixW15C.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk77

theorem root_11100 : SixW15C.walk table bits 64 28226 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 0 0) = some 28461 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 0 0 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk78

theorem root_11101 : SixW15C.walk table bits 64 28461 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 0 1) = some 28500 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 0 1 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk79

theorem root_11110 : SixW15C.walk table bits 64 28500 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 1 0) = some 28501 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 1 0 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk80

theorem root_11111 : SixW15C.walk table bits 64 28501 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 1 1) = some 28502 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 1 1 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk81

theorem root_11120 : SixW15C.walk table bits 64 28502 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 2 0) = some 28503 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 2 0 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk82

theorem root_11121 : SixW15C.walk table bits 64 28503 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 2 1) = some 28504 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 1 2 1 = (SixW15C.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk83

theorem root_11200 : SixW15C.walk table bits 64 28504 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 0 0) = some 28505 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 0 0 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk84

theorem root_11201 : SixW15C.walk table bits 64 28505 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 0 1) = some 28506 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 0 1 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk85

theorem root_11210 : SixW15C.walk table bits 64 28506 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 1 0) = some 28507 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 1 0 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk86

theorem root_11211 : SixW15C.walk table bits 64 28507 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 1 1) = some 28508 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 1 1 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk87

theorem root_11220 : SixW15C.walk table bits 64 28508 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 2 0) = some 28509 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 2 0 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk88

theorem root_11221 : SixW15C.walk table bits 64 28509 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 2 1) = some 28510 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 1 2 2 1 = (SixW15C.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk89

theorem root_12000 : SixW15C.walk table bits 64 28510 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 0 0) = some 28773 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 0 0 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936) from by decide +kernel]; exact wk90

theorem root_12001 : SixW15C.walk table bits 64 28773 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 0 1) = some 28832 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 0 1 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 409600) from by decide +kernel]; exact wk91

theorem root_12010 : SixW15C.walk table bits 64 28832 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 1 0) = some 28851 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 1 0 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936) from by decide +kernel]; exact wk92

theorem root_12011 : SixW15C.walk table bits 64 28851 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 1 1) = some 28852 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 1 1 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 409600) from by decide +kernel]; exact wk93

theorem root_12020 : SixW15C.walk table bits 64 28852 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 2 0) = some 28853 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 2 0 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936) from by decide +kernel]; exact wk94

theorem root_12021 : SixW15C.walk table bits 64 28853 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 2 1) = some 28854 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 0 2 1 = (SixW15C.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 409600) from by decide +kernel]; exact wk95

theorem root_12100 : SixW15C.walk table bits 64 28854 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 0 0) = some 28855 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 0 0 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936) from by decide +kernel]; exact wk96

theorem root_12101 : SixW15C.walk table bits 64 28855 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 0 1) = some 28856 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 0 1 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 409600) from by decide +kernel]; exact wk97

theorem root_12110 : SixW15C.walk table bits 64 28856 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 1 0) = some 28857 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 1 0 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936) from by decide +kernel]; exact wk98

theorem root_12111 : SixW15C.walk table bits 64 28857 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 1 1) = some 28858 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 1 1 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 409600) from by decide +kernel]; exact wk99

theorem root_12120 : SixW15C.walk table bits 64 28858 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 2 0) = some 28859 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 2 0 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936) from by decide +kernel]; exact wk100

theorem root_12121 : SixW15C.walk table bits 64 28859 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 2 1) = some 28860 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 1 2 1 = (SixW15C.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 409600) from by decide +kernel]; exact wk101

theorem root_12200 : SixW15C.walk table bits 64 28860 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 0 0) = some 28861 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 0 0 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936) from by decide +kernel]; exact wk102

theorem root_12201 : SixW15C.walk table bits 64 28861 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 0 1) = some 28862 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 0 1 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 409600) from by decide +kernel]; exact wk103

theorem root_12210 : SixW15C.walk table bits 64 28862 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 1 0) = some 28863 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 1 0 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936) from by decide +kernel]; exact wk104

theorem root_12211 : SixW15C.walk table bits 64 28863 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 1 1) = some 28864 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 1 1 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 409600) from by decide +kernel]; exact wk105

theorem root_12220 : SixW15C.walk table bits 64 28864 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 2 0) = some 28865 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 2 0 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936) from by decide +kernel]; exact wk106

theorem root_12221 : SixW15C.walk table bits 64 28865 (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 2 1) = some 28866 := by
  rw [show SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) 1 2 2 2 1 = (SixW15C.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 409600) from by decide +kernel]; exact wk107

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW15C.badOf cover0).length → i1 < (SixW15C.badOf cover1).length → i2 < (SixW15C.badOf cover2).length → i3 < (SixW15C.badOf cover3).length → i4 < (SixW15C.badOf cover4).length →
    ∃ pos pos', SixW15C.walk table bits 64 pos (SixW15C.boxOf (SixW15C.badOf cover0) (SixW15C.badOf cover1) (SixW15C.badOf cover2) (SixW15C.badOf cover3) (SixW15C.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
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

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW15C.cN : ℝ) / SixW15C.SA ≤ SixW15C.G g0 g1 g2 g3 g4 :=
  SixW15C.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 401408 237568 221184 237568 409600
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW15CData

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

/-! ###### the 6-point weighted bound from the checked certificate `SixW15C` ###### -/

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

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW15C.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW15C.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW15C.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW15C.SA]
  try ring

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (304544 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := SixW15CData.cert (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW15C.cN, SixW15C.SA] at h
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
