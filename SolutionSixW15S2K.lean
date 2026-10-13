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

/-! ###### natural-number checker for the 6-point weighted certificate `SixW15S2K` ###### -/

section SixW15S2KDefs

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
  bif Nat.ble XFARN a then ((a >>> 8) <<< 8, ((b + 255) >>> 8) <<< 8) else (a, b)

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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15S2K

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

end Zeta23Ext.Bridge.ThreePoint.SixW15S2K

end SixW15S2KDefs

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

namespace Zeta23Ext.Bridge.ThreePoint.SixW15S2K

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

end Zeta23Ext.Bridge.ThreePoint.SixW15S2K

end

/-! ###### certificate data `SixW15S2K`: 1946 cells, 4648 leaves (axis-coded walk) (half-space) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW15S2KData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW15S2K

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

noncomputable def tab0 : CTN :=
  (N (N (N (N (N (N E ⟨17179893760,331038177865⟩ E) ⟨25769832448,242869129569⟩ (N E ⟨30064801792,122761883704⟩ E)) ⟨32212286464,69269436296⟩ (N (N E ⟨32212286592,62652449971⟩ E) ⟨32212287488,27393363819⟩ (N E ⟨33286029056,36843158376⟩ E))) ⟨33286029120,34548539408⟩ (N (N (N E ⟨33286029312,28203622388⟩ E) ⟨33420246720,39350240729⟩ (N E ⟨33420247040,28267587364⟩ E)) ⟨34024226784,29477834588⟩ (N (N E ⟨34024226816,28450417775⟩ E) ⟨34091335680,28460062200⟩ (N E ⟨34158444544,28467564926⟩ E)))) ⟨34326216704,28476945188⟩ (N (N (N (N E ⟨34359771264,24535647482⟩ E) ⟨34359771360,21788669253⟩ (N E ⟨34359771392,20912356297⟩ E)) ⟨34359771648,14596526138⟩ (N (N E ⟨34359771776,11891897536⟩ E) ⟨34493989376,14596526138⟩ (N E ⟨34594652800,11891897536⟩ E))) ⟨34628207136,13892464743⟩ (N (N (N E ⟨34628207424,8384490092⟩ E) ⟨34628208000,1626727581⟩ (N E ⟨34896642752,10650250913⟩ E)) ⟨34896642944,7358852099⟩ (N (N E ⟨34896643328,2658307323⟩ E) ⟨34930197312,8384490092⟩ E)))) ⟨35030860624,8121431559⟩ (N (N (N (N (N E ⟨35030860832,5101426618⟩ E) ⟨35030861248,1207853390⟩ (N E ⟨35097969536,7358852099⟩ E)) ⟨35232187488,4319118251⟩ (N (N E ⟨35232187776,1626727581⟩ E) ⟨35248964640,5101426618⟩ (N E ⟨35299296320,4701749332⟩ E))) ⟨35299296512,2658307323⟩ (N (N (N E ⟨35467068656,2805660000⟩ E) ⟨35467068864,1207853390⟩ (N E ⟨35500623104,2658307323⟩ E)) ⟨35534177664,1626727581⟩ (N (N E ⟨35685172672,1207853390⟩ E) ⟨35701949888,1207853390⟩ E))) ⟨35701950080,329694637⟩ (N (N (N (N E ⟨35903276672,329694637⟩ E) ⟨36339484928,840527⟩ (N E ⟨36440148480,76228626⟩ E)) ⟨36507257216,198180864⟩ (N (N E ⟨36507257600,189390231⟩ E) ⟨36507258368,173234703⟩ (N E ⟨36507259904,145808985⟩ E))) ⟨36775693376,1151561664⟩ (N (N (N E ⟨36775694208,1046595949⟩ E) ⟨36775695872,870430129⟩ (N E ⟨36909910784,2032077427⟩ E)) ⟨37044128832,2982576597⟩ (N (N E ⟨37044129408,2790908306⟩ E) ⟨37044130560,2451923401⟩ E)))))

noncomputable def tab1 : CTN :=
  (N (N (N (N (N (N E ⟨37312564736,5416703501⟩ E) ⟨37648109184,9732001830⟩ (N E ⟨37648109440,9452356006⟩ E)) ⟨38117872640,15563604115⟩ (N (N E ⟨38252090112,18591409084⟩ E) ⟨38520526336,22408627075⟩ (N E ⟨39460051968,40016092176⟩ E))) ⟨39728485504,58284410507⟩ (N (N (N E ⟨39862703360,62313805310⟩ E) ⟨39996921344,65509628502⟩ (N E ⟨40265357312,71849923330⟩ E)) ⟨40802230272,75832144115⟩ (N (N E ⟨41875971584,124701346738⟩ E) ⟨42412843008,143033504697⟩ (N E ⟨42949715968,138814108272⟩ E)))) ⟨42949722112,80226784524⟩ (N (N (N (N E ⟨45097201664,198611196246⟩ E) ⟨47244689408,205420959916⟩ (N E ⟨51539660800,198637449669⟩ E)) ⟨51539664896,86044756753⟩ (N (N E ⟨55834630144,180021136485⟩ E) ⟨57982115840,129277608381⟩ (N E ⟨60129600000,126832062122⟩ E))) ⟨60129601536,81450895201⟩ (N (N (N E ⟨60666473596,56104174470⟩ E) ⟨60666476280,14490230268⟩ (N E ⟨62277086208,63653684247⟩ E)) ⟨63350829696,32801554392⟩ (N (N E ⟨63350829760,31761760685⟩ E) ⟨63350831360,11699544709⟩ E)))) ⟨63350831488,10561059564⟩ (N (N (N (N (N E ⟨63480852922,36353090489⟩ E) ⟨63480854264,17122242272⟩ (N E ⟨64888042585,27345176745⟩ E)) ⟨64888043256,18266655065⟩ (N (N E ⟨65095660992,22416910280⟩ E) ⟨65095661824,12731502888⟩ (N E ⟨65162769952,21197196115⟩ E))) ⟨65162770816,11542172995⟩ (N (N (N E ⟨65591637752,18783570843⟩ E) ⟨65968076640,17772222298⟩ (N E ⟨65968077056,13175739927⟩ E)) ⟨66068740048,16517231195⟩ (N (N E ⟨66068740480,11958745632⟩ E) ⟨66295232919,11832935104⟩ E))) ⟨66295233590,6357569415⟩ (N (N (N (N E ⟨66295234560,1565943956⟩ E) ⟨66370732032,1570745138⟩ (N E ⟨66404284672,13377854911⟩ E)) ⟨66521725312,12146351030⟩ (N (N E ⟨66706276352,1590346721⟩ E) ⟨66840492704,9616293499⟩ (N E ⟨66840493120,6405326128⟩ E))) ⟨66840493952,2041289663⟩ (N (N (N E ⟨66974710576,8457379249⟩ E) ⟨66974711008,5380608052⟩ (N E ⟨66974711808,1603951009⟩ E)) ⟨66998828086,6505110531⟩ (N (N E ⟨67276700736,6486530866⟩ E) ⟨67427695840,5447824625⟩ E)))))

noncomputable def tab2 : CTN :=
  (N (N (N (N (N (N E ⟨67702423253,2786489703⟩ E) ⟨67702423552,1631286091⟩ (N E ⟨67712908768,3983824195⟩ E)) ⟨67712909184,2086096939⟩ (N (N E ⟨67880681104,3110902549⟩ E) ⟨67880681472,1635815150⟩ (N E ⟨68149116800,2099820129⟩ E))) ⟨68333666304,1643428677⟩ (N (N (N E ⟨68406018048,1644124289⟩ E) ⟨68585324544,1645228303⟩ (N E ⟨68719542336,1436255057⟩ E)) ⟨68719542560,817796385⟩ (N (N E ⟨68719542644,631150126⟩ E) ⟨68719542976,131485341⟩ (N E ⟨68719543168,13164037⟩ E)))) ⟨68786652064,5411364⟩ (N (N (N (N E ⟨69021532864,131485341⟩ E) ⟨69793287488,2144977⟩ (N E ⟨69793288320,2043342⟩ E)) ⟨69793289024,1962016⟩ (N (N E ⟨69793289856,1871060⟩ E) ⟨69793291520,1704455⟩ (N E ⟨69793292288,1633839⟩ E))) ⟨69813208754,5267032⟩ (N (N (N E ⟨69826840576,7751317⟩ E) ⟨69860395232,16146559⟩ (N E ⟨69860395648,15751742⟩ E)) ⟨69877172064,22078531⟩ (N (N E ⟨69893949312,28387479⟩ E) ⟨69927503776,43427482⟩ E)))) ⟨69927504160,42441413⟩ (N (N (N (N (N E ⟨69927504192,42360513⟩ E) ⟨69927504384,41879149⟩ (N E ⟨69927504576,41404619⟩ E)) ⟨69927505024,40323308⟩ (N (N E ⟨69927505344,39572543⟩ E) ⟨69927505408,39424498⟩ (N E ⟨69927506176,37700926⟩ E))) ⟨69961058144,61988162⟩ (N (N (N E ⟨69961058240,61632132⟩ E) ⟨69994613472,79279373⟩ (N E ⟨69994613504,79129267⟩ E)) ⟨70061723264,122699745⟩ (N (N E ⟨70061724032,117345383⟩ E) ⟨70061724928,111463211⟩ E))) ⟨70061725568,107486576⟩ (N (N (N (N E ⟨70061725696,106712690⟩ E) ⟨70061727232,97948609⟩ (N E ⟨70061727744,95228999⟩ E)) ⟨70095276000,166851467⟩ (N (N E ⟨70095276288,164002603⟩ E) ⟨70095276864,158485379⟩ (N E ⟨70095278016,148131178⟩ E))) ⟨70195940928,254231101⟩ (N (N (N E ⟨70195941504,245844939⟩ E) ⟨70195942592,230928524⟩ (N E ⟨70195943168,223490173⟩ E)) ⟨70263048320,368302193⟩ (N (N E ⟨70263048400,366546001⟩ E) ⟨70263048608,362028761⟩ E)))))

noncomputable def tab3 : CTN :=
  (N (N (N (N (N (N E ⟨70263049856,336341561⟩ E) ⟨70296603264,406095250⟩ (N E ⟨70330157136,473661220⟩ E)) ⟨70330157344,467812693⟩ (N (N E ⟨70330157376,466920968⟩ E) ⟨70330157760,456384570⟩ (N E ⟨70330158208,444465767⟩ E))) ⟨70330158528,436190422⟩ (N (N (N E ⟨70330158592,434558582⟩ E) ⟨70330159360,415560422⟩ (N E ⟨70330159680,407952178⟩ E)) ⟨70330159872,403470914⟩ (N (N E ⟨70330160512,388971858⟩ E) ⟨70330161984,358022393⟩ (N E ⟨70330162176,354216357⟩ E)))) ⟨70330162816,341890120⟩ (N (N (N (N E ⟨70330163200,334751802⟩ E) ⟨70363711808,523183766⟩ (N E ⟨70363712192,511377759⟩ E)) ⟨70397266176,584920347⟩ (N (N E ⟨70397266688,567387984⟩ E) ⟨70430821504,614411191⟩ (N E ⟨70481152416,741452336⟩ E))) ⟨70516804592,788334247⟩ (N (N (N E ⟨70531484736,815339532⟩ E) ⟨70531485312,788243580⟩ (N E ⟨70531486464,737352761⟩ E)) ⟨70548261152,892516340⟩ (N (N E ⟨70565038496,923842834⟩ E) ⟨70598593984,941896883⟩ E)))) ⟨70598595712,852286103⟩ (N (N (N (N (N E ⟨70598598656,722853285⟩ E) ⟨70665703552,1054752212⟩ (N E ⟨70665704672,988948568⟩ E)) ⟨70665705088,965822379⟩ (N (N E ⟨70699256352,1248599733⟩ E) ⟨70699256640,1227463388⟩ (N E ⟨70732811088,1315757248⟩ E))) ⟨70732811296,1299696151⟩ (N (N (N E ⟨70732811712,1268304108⟩ E) ⟨70732812544,1208318578⟩ (N E ⟨70732816384,973352611⟩ E)) ⟨70766365184,1436759118⟩ (N (N E ⟨70766365376,1420479279⟩ E) ⟨70799920064,1494375553⟩ E))) ⟨70799920256,1477555333⟩ (N (N (N (N E ⟨70799920640,1444620480⟩ E) ⟨70799921280,1391746408⟩ (N E ⟨70799921408,1381464137⟩ E)) ⟨70799922944,1265194420⟩ (N (N E ⟨70867028960,1691264844⟩ E) ⟨70867029536,1634980687⟩ (N E ⟨70867029952,1595784993⟩ E))) ⟨70867030400,1554881604⟩ (N (N (N E ⟨70867030784,1520862133⟩ E) ⟨70867032064,1413993416⟩ (N E ⟨70934142976,1420381457⟩ E)) ⟨70950915104,1951528816⟩ (N (N E ⟨70967691968,2049456300⟩ E) ⟨71001246528,2149350120⟩ E)))))

noncomputable def tab4 : CTN :=
  (N (N (N (N (N (N E ⟨71101912704,2128595888⟩ E) ⟨71135465088,2517166723⟩ (N E ⟨71169018944,2733369542⟩ E)) ⟨71169019120,2705204276⟩ (N (N E ⟨71169019328,2672385180⟩ E) ⟨71202573440,2855478780⟩ (N E ⟨71202573632,2823429633⟩ E))) ⟨71202573824,2791829878⟩ (N (N (N E ⟨71202574176,2735039188⟩ E) ⟨71202574592,2669775839⟩ (N E ⟨71202575744,2498957102⟩ E)) ⟨71202578048,2196479585⟩ (N (N E ⟨71303236992,3223080944⟩ E) ⟨71303237568,3116466843⟩ (N E ⟨71387123136,3573308261⟩ E)))) ⟨71403900416,3634492537⟩ (N (N (N (N E ⟨71403900800,3553933353⟩ E) ⟨71403901376,3437242548⟩ (N E ⟨71403902208,3277032161⟩ E)) ⟨71403902528,3217910342⟩ (N (N E ⟨71403903360,3070329399⟩ E) ⟨71403903872,2983713065⟩ (N E ⟨71403904256,2920752234⟩ E))) ⟨71403905024,2799744336⟩ (N (N (N E ⟨71471009728,3838928819⟩ E) ⟨71538118048,4283353826⟩ (N E ⟨71538118432,4188279318⟩ E)) ⟨71538118848,4088246003⟩ (N (N E ⟨71538119616,3911307061⟩ E) ⟨71538119680,3896999142⟩ E)))) ⟨71538120064,3812514736⟩ (N (N (N (N (N E ⟨71538120448,3730312206⟩ E) ⟨71538121152,3585291399⟩ (N E ⟨71538121984,3422887433⟩ E)) ⟨71538122752,3281075879⟩ (N (N E ⟨71571672512,4440059959⟩ E) ⟨71605226784,4651423019⟩ (N E ⟨71605227392,4488976110⟩ E))) ⟨71605227776,4390031577⟩ (N (N (N E ⟨71638782208,4553028902⟩ E) ⟨71672336320,4807483618⟩ (N E ⟨71672337472,4498501637⟩ E)) ⟨71672337536,4482076077⟩ (N (N E ⟨71672338304,4290708233⟩ E) ⟨71672339200,4080197863⟩ E))) ⟨71672339968,3909966420⟩ (N (N (N (N E ⟨71739446016,4912999674⟩ E) ⟨71806553568,5671610975⟩ (N E ⟨71806556160,4886683049⟩ E)) ⟨71806558208,4360811591⟩ (N (N E ⟨71907217344,6078020781⟩ E) ⟨71923994255,6285316115⟩ (N E ⟨71923994926,6044893012⟩ E))) ⟨71923996268,5597633759⟩ (N (N (N E ⟨71923998720,4882398868⟩ E) ⟨71940772032,6179399992⟩ (N E ⟨71940773632,5638381643⟩ E)) ⟨71974326080,6517259194⟩ (N (N E ⟨71974326464,6373474386⟩ E) ⟨72007880960,6546294398⟩ E)))))

noncomputable def tab5 : CTN :=
  (N (N (N (N (N (N E ⟨72041435008,6897769194⟩ E) ⟨72074989888,6922529118⟩ (N E ⟨72074990336,6746069797⟩ E)) ⟨72074990656,6623467806⟩ (N (N E ⟨72074991488,6317518618⟩ E) ⟨72074992640,5922529203⟩ (N E ⟨72074993664,5597080107⟩ E))) ⟨72276317440,7756885020⟩ (N (N (N E ⟨72276318592,7267610129⟩ E) ⟨72343426816,7947109301⟩ (N E ⟨72410534912,8744893937⟩ E)) ⟨72410535040,8681119975⟩ (N (N E ⟨72410535296,8555310324⟩ E) ⟨72410535680,8370847260⟩ (N E ⟨72410537216,7680983870⟩ E)))) ⟨72477643840,9165553539⟩ (N (N (N (N E ⟨72477644672,8742181109⟩ E) ⟨72477646336,7966431815⟩ (N E ⟨72544753536,9184913721⟩ E)) ⟨72611862080,9814924171⟩ (N (N E ⟨72611862912,9364788646⟩ E) ⟨72611864576,8539479175⟩ (N E ⟨72627589422,10691116472⟩ E))) ⟨72746082304,9372677031⟩ (N (N (N E ⟨72947406720,12071904097⟩ E) ⟨72947408896,10695245768⟩ (N E ⟨73148734720,12627844833⟩ E)) ⟨73148735488,12104668324⟩ (N (N E ⟨73282952192,13853481102⟩ E) ⟨73282953216,13092218008⟩ E)))) ⟨73331185260,15427701477⟩ (N (N (N (N (N E ⟨73819824128,17420620864⟩ E) ⟨74222477312,21055464219⟩ (N E ⟨74490912768,23658131590⟩ E)) ⟨74738376704,26181050867⟩ (N (N E ⟨77309485120,58269208097⟩ E) ⟨77309485288,57736288205⟩ (N E ⟨77309485312,57660655940⟩ E))) ⟨77309485504,57060043124⟩ (N (N (N E ⟨77309485568,56861581616⟩ E) ⟨77309485952,55688794939⟩ (N E ⟨77309486080,55304609886⟩ E)) ⟨77309486208,54923738523⟩ (N (N E ⟨77309486336,54546146546⟩ E) ⟨77309487360,51639486278⟩ E))) ⟨77309487616,50943335175⟩ (N (N (N (N E ⟨77309489664,45776641928⟩ E) ⟨77309490656,43510134591⟩ (N E ⟨77552760288,46130130415⟩ E)) ⟨77577921024,60643085590⟩ (N (N E ⟨77846356736,63602331360⟩ E) ⟨77846356992,62727040513⟩ (N E ⟨78114792448,66530373098⟩ E))) ⟨78383228928,66621352329⟩ (N (N (N E ⟨79456972800,73216762336⟩ E) ⟨81604460544,81183335634⟩ (N E ⟨83181518848,95435097263⟩ E)) ⟨85899431936,79111303097⟩ (N (N E ⟨85899435984,38860075235⟩ E) ⟨90194401280,68661704304⟩ E)))))

noncomputable def tab6 : CTN :=
  (N (N (N (N (N (N E ⟨92341885952,61427731673⟩ E) ⟨92878756608,65677920649⟩ (N E ⟨93147192192,64676607906⟩ E)) ⟨93281410048,63381401765⟩ (N (N E ⟨93415628032,60519493235⟩ E) ⟨93415628800,51392597158⟩ (N E ⟨93684063744,57931894547⟩ E))) ⟨93952499712,52311507142⟩ (N (N (N E ⟨94439038976,53137584618⟩ E) ⟨94489371918,38665515103⟩ (N E ⟨94489373260,25713477686⟩ E)) ⟨94489374224,17965572406⟩ (N (N E ⟨94489374240,17848583852⟩ E) ⟨94489375944,7621693323⟩ (N E ⟨94489378336,608823085⟩ E)))) ⟨95846230604,26930134247⟩ (N (N (N (N E ⟨96766882874,9119089002⟩ E) ⟨96766884216,3461637059⟩ (N E ⟨97253420267,22155531513⟩ E)) ⟨97253420938,16885861029⟩ (N (N E ⟨97253422280,8536991830⟩ E) ⟨97375058560,2758510826⟩ (N E ⟨97957015434,17257371011⟩ E))) ⟨98174073208,3676528200⟩ (N (N (N E ⟨98247475200,261869607⟩ E) ⟨98264248852,12885293992⟩ (N E ⟨98264249880,7158732196⟩ E)) ⟨98281026216,11958562382⟩ (N (N E ⟨98281027376,5905315798⟩ E) ⟨98281029632,262627654⟩ E)))) ⟨98381691776,2185018972⟩ (N (N (N (N (N E ⟨98381692928,264878549⟩ E) ⟨98448800640,2191291061⟩ (N E ⟨98511715002,2728728717⟩ E)) ⟨98511716344,274562977⟩ (N (N E ⟨98660611272,8948919475⟩ E) ⟨99186999296,281547652⟩ (N E ⟨99254107008,2262540547⟩ E))) ⟨99342186008,7406076460⟩ (N (N (N E ⟨99497375536,6141282325⟩ E) ⟨99790979072,292343642⟩ (N E ⟨99918904504,1568994808⟩ E)) ⟨99918904665,1242847513⟩ (N (N E ⟨99918905336,301693756⟩ E) ⟨100059414048,899130967⟩ E))) ⟨100059414144,751540179⟩ (N (N (N (N E ⟨100059414528,296632190⟩ E) ⟨100067802948,492729421⟩ (N E ⟨100126523072,662577731⟩ E)) ⟨100126523392,297653366⟩ (N (N E ⟨100256546816,299572867⟩ E) ⟨100260740832,622739165⟩ (N E ⟨100420123164,3404954463⟩ E))) ⟨100420124192,911071643⟩ (N (N (N E ⟨100622499000,1605129102⟩ E) ⟨100696948736,305483065⟩ (N E ⟨100713724856,2223049757⟩ E)) ⟨100713725952,305689821⟩ (N (N E ⟨100791320568,314108631⟩ E) ⟨100864720896,307488777⟩ E)))))

noncomputable def tab7 : CTN :=
  (N (N (N (N (N (N E ⟨100965384144,355128528⟩ E) ⟨100998938304,683366334⟩ (N E ⟨100998938624,308993641⟩ E)) ⟨101326094167,492628661⟩ (N (N E ⟨101326094336,312284618⟩ E) ⟨101418368256,1482832699⟩ (N E ⟨101435145920,691665201⟩ E))) ⟨101435146240,313261231⟩ (N (N (N E ⟨101494915064,321390812⟩ E) ⟨101498060320,940202692⟩ (N E ⟨101602918400,314644752⟩ E)) ⟨101762301952,315824499⟩ (N (N E ⟨101770690560,315882938⟩ E) ⟨101821021824,792727160⟩ E))) ⟨101871353536,698515571⟩ (N (N (N (N E ⟨101871353856,316555598⟩ E) ⟨101930074112,316923535⟩ (N E ⟨102029688832,317506369⟩ E)) ⟨102206898176,318414087⟩ (N (N E ⟨102223675392,318491431⟩ E) ⟨102274007040,318714522⟩ (N E ⟨102307561472,318855792⟩ E))) ⟨102324338688,318924188⟩ (N (N (N E ⟨102465896448,319441743⟩ E) ⟨102475333632,319472457⟩ (N E ⟨102726991872,320116289⟩ E)) ⟨102743769088,320147185⟩ (N (N E ⟨102928318464,320387635⟩ E) ⟨103079313664,120294753⟩ E)))) ⟨103079313920,16522152⟩ (N (N (N (N (N E ⟨103884621312,7624283⟩ E) ⟨103884621568,7546161⟩ (N E ⟨103884621824,7469038⟩ E)) ⟨103884622080,7392899⟩ (N (N E ⟨103884622336,7317728⟩ E) ⟨103884622592,7243512⟩ (N E ⟨103884622848,7170235⟩ E))) ⟨103884623104,7097883⟩ (N (N (N E ⟨103884623360,7026443⟩ E) ⟨103884623616,6955900⟩ (N E ⟨103884623872,6886241⟩ E)) ⟨103884624128,6817452⟩ (N (N E ⟨103884624384,6749522⟩ E) ⟨103884624896,6616182⟩ E))) ⟨103884625152,6550749⟩ (N (N (N (N E ⟨103884625408,6486123⟩ E) ⟨103884625664,6422292⟩ (N E ⟨103884626176,6296973⟩ E)) ⟨103884626944,6114674⟩ (N (N E ⟨103884627200,6055379⟩ E) ⟨103884627712,5938932⟩ (N E ⟨103884627968,5881758⟩ E))) ⟨104153057024,90014814⟩ (N (N (N E ⟨104153057792,87289942⟩ E) ⟨104153058048,86404646⟩ (N E ⟨104153058304,85530558⟩ E)) ⟨104153058560,84667506⟩ (N (N E ⟨104153058816,83815324⟩ E) ⟨104153059072,82973847⟩ E)))))

noncomputable def tab8 : CTN :=
  (N (N (N (N (N (N E ⟨104153059584,81322370⟩ E) ⟨104153059840,80512055⟩ (N E ⟨104153060096,79711817⟩ E)) ⟨104153060352,78921508⟩ (N (N E ⟨104153060608,78140978⟩ E) ⟨104153062144,73655234⟩ (N E ⟨104153063424,70160892⟩ E))) ⟨104421492992,258913898⟩ (N (N (N E ⟨104421493248,256281280⟩ E) ⟨104421493504,253682074⟩ (N E ⟨104421493760,251115769⟩ E)) ⟨104421494016,248581868⟩ (N (N E ⟨104421494272,246079881⟩ E) ⟨104421494528,243609325⟩ (N E ⟨104421494784,241169728⟩ E)))) ⟨104421495040,238760624⟩ (N (N (N (N E ⟨104421495296,236381558⟩ E) ⟨104421495552,234032080⟩ (N E ⟨104421495808,231711749⟩ E)) ⟨104421496064,229420132⟩ (N (N E ⟨104421496320,227156804⟩ E) ⟨104421496576,224921345⟩ (N E ⟨104421496832,222713345⟩ E))) ⟨104421497600,216250090⟩ (N (N (N E ⟨104421498880,205990782⟩ E) ⟨104689928960,510003708⟩ (N E ⟨104689929216,504844397⟩ E)) ⟨104689929472,499750230⟩ (N (N E ⟨104689929728,494720222⟩ E) ⟨104689929984,489753404⟩ E)))) ⟨104689930240,484848826⟩ (N (N (N (N (N E ⟨104689930496,480005552⟩ E) ⟨104689930752,475222665⟩ (N E ⟨104689931264,465834458⟩ E)) ⟨104689931520,461227380⟩ (N (N E ⟨104689931776,456677173⟩ E) ⟨104689932032,452182996⟩ (N E ⟨104689932544,443359438⟩ E))) ⟨104689932800,439028447⟩ (N (N (N E ⟨104689933312,430524113⟩ E) ⟨104689933568,426349241⟩ (N E ⟨104689934336,414124897⟩ E)) ⟨104958364672,847421402⟩ (N (N E ⟨104958364928,838870438⟩ E) ⟨104958365184,830427171⟩ E))) ⟨104958365440,822089973⟩ (N (N (N (N E ⟨104958365696,813857248⟩ E) ⟨104958365952,805727429⟩ (N E ⟨104958366208,797698973⟩ E)) ⟨104958366464,789770367⟩ (N (N E ⟨104958366720,781940122⟩ E) ⟨104958366976,774206776⟩ (N E ⟨104958367232,766568892⟩ E))) ⟨104958367488,759025059⟩ (N (N (N E ⟨104958367744,751573889⟩ E) ⟨104958368000,744214017⟩ (N E ⟨104958368256,736944104⟩ E)) ⟨104958368512,729762831⟩ (N (N E ⟨104958369280,708738019⟩ E) ⟨104958369536,701898578⟩ E)))))

noncomputable def tab9 : CTN :=
  (N (N (N (N (N (N E ⟨105226800384,1266425096⟩ E) ⟨105226800640,1253678471⟩ (N E ⟨105226800896,1241091979⟩ E)) ⟨105226801152,1228663208⟩ (N (N E ⟨105226801408,1216389790⟩ E) ⟨105226801664,1204269399⟩ (N E ⟨105226801920,1192299748⟩ E))) ⟨105226802176,1180478592⟩ (N (N (N E ⟨105226802432,1168803722⟩ E) ⟨105226802688,1157272969⟩ (N E ⟨105226802944,1145884202⟩ E)) ⟨105226803200,1134635327⟩ (N (N E ⟨105226803456,1123524283⟩ E) ⟨105226803712,1112549047⟩ (N E ⟨105226803968,1101707631⟩ E)))) ⟨105226804224,1090998079⟩ (N (N (N (N E ⟨105226804736,1069966913⟩ E) ⟨105226804992,1059641553⟩ (N E ⟨105226805248,1049440563⟩ E)) ⟨105495236096,1764735511⟩ (N (N E ⟨105495236352,1747018185⟩ E) ⟨105495236608,1729522875⟩ (N E ⟨105495236864,1712246247⟩ E))) ⟨105495237120,1695185027⟩ (N (N (N E ⟨105495237376,1678335996⟩ E) ⟨105495237888,1645261907⟩ (N E ⟨105495238144,1629030689⟩ E)) ⟨105495238400,1612999337⟩ (N (N E ⟨105495238912,1581524485⟩ E) ⟨105495239168,1566075239⟩ E)))) ⟨105495239680,1535739104⟩ (N (N (N (N (N E ⟨105495239936,1520846759⟩ E) ⟨105495240448,1491600215⟩ (N E ⟨105495240704,1477240831⟩ E)) ⟨105763671808,2339910440⟩ (N (N E ⟨105763672064,2316477679⟩ E) ⟨105763672320,2293337816⟩ (N E ⟨105763672576,2270486464⟩ E))) ⟨105763672832,2247919313⟩ (N (N (N E ⟨105763673088,2225632127⟩ E) ⟨105763673344,2203620744⟩ (N E ⟨105763673600,2181881076⟩ E)) ⟨105763673856,2160409102⟩ (N (N E ⟨105763674112,2139200874⟩ E) ⟨105763674368,2118252510⟩ E))) ⟨105763674624,2097560193⟩ (N (N (N (N E ⟨105763674880,2077120175⟩ E) ⟨105763676160,1978577712⟩ (N E ⟨106032107776,2959490771⟩ E)) ⟨106032108032,2930001715⟩ (N (N E ⟨106032108288,2900879413⟩ E) ⟨106032108544,2872118399⟩ (N E ⟨106032108800,2843713302⟩ E))) ⟨106032109056,2815658845⟩ (N (N (N E ⟨106032109312,2787949840⟩ E) ⟨106032109568,2760581192⟩ (N E ⟨106032109824,2733547891⟩ E)) ⟨106032110080,2706845013⟩ (N (N E ⟨106032110336,2680467719⟩ E) ⟨106032110592,2654411252⟩ E)))))

noncomputable def tab10 : CTN :=
  (N (N (N (N (N (N E ⟨106032111616,2553301322⟩ E) ⟨106300544000,3600776238⟩ (N E ⟨106300544256,3565164754⟩ E)) ⟨106300544512,3529992867⟩ (N (N E ⟨106300545024,3460941988⟩ E) ⟨106300545280,3427050325⟩ (N E ⟨106300546304,3295566036⟩ E))) ⟨106300546816,3232190868⟩ (N (N (N E ⟨106300547072,3201075113⟩ E) ⟨106568979456,4411016060⟩ (N E ⟨106568979712,4367391348⟩ E)) ⟨106568980224,4281749501⟩ (N (N E ⟨106568980480,4239716573⟩ E) ⟨106568980736,4198198672⟩ (N E ⟨106568980992,4157188238⟩ E)))) ⟨106568981248,4116677837⟩ (N (N (N (N E ⟨106568982016,3998074401⟩ E) ⟨106568982528,3921374948⟩ (N E ⟨106837415168,5249599901⟩ E)) ⟨106837415680,5146658489⟩ (N (N E ⟨106837415936,5096134953⟩ E) ⟨106837416448,4996935979⟩ (N E ⟨106837416704,4948242519⟩ E))) ⟨106837417216,4852623744⟩ (N (N (N E ⟨106837417472,4805681311⟩ E) ⟨106837417728,4759305680⟩ (N E ⟨106837417984,4713488648⟩ E)) ⟨107105852416,5797344305⟩ (N (N E ⟨107105852672,5741126388⟩ E) ⟨107105853440,5576516022⟩ E)))) ⟨107374287360,6900812643⟩ (N (N (N (N (N E ⟨107374287616,6833566545⟩ E) ⟨107374288640,6572643104⟩ (N E ⟨107374288896,6509369379⟩ E)) ⟨107642724352,7510774532⟩ (N (N E ⟨107911159808,8579272269⟩ E) ⟨108179595264,9713220361⟩ (N E ⟨108448030464,11016853392⟩ E))) ⟨108448030720,10910796006⟩ (N (N (N E ⟨108716466176,12169998792⟩ E) ⟨110058643456,19308445686⟩ (N E ⟨110595514368,22506452254⟩ E)) ⟨111132385280,25863293140⟩ (N (N E ⟨111669256448,29069507059⟩ E) ⟨111669256704,28791006768⟩ E))) ⟨111669256960,28515836841⟩ (N (N (N (N E ⟨111669257216,28243949556⟩ E) ⟨111669257472,27975297990⟩ (N E ⟨111669257728,27709835999⟩ E)) ⟨111669257984,27447518209⟩ (N (N E ⟨111669258240,27188299995⟩ E) ⟨111669258496,26932137472⟩ (N E ⟨111669258752,26678987475⟩ E))) ⟨111669259008,26428807555⟩ (N (N (N E ⟨111669259264,26181555955⟩ E) ⟨111669259520,25937191605⟩ (N E ⟨111669259776,25695674104⟩ E)) ⟨111669260288,25221021330⟩ (N (N E ⟨111669260544,24987808501⟩ E) ⟨111669261056,24529420755⟩ E)))))

noncomputable def tab11 : CTN :=
  (N (N (N (N (N (N E ⟨111669261824,23861384437⟩ E) ⟨111669262080,23643775309⟩ (N E ⟨111669262592,23215954651⟩ E)) ⟨111669262848,23005676080⟩ (N (N E ⟨111669263616,22388976217⟩ E) ⟨111669263872,22188015873⟩ (N E ⟨111669264384,21792819594⟩ E))) ⟨112743006208,27176325579⟩ (N (N (N E ⟨116232667136,44423594319⟩ E) ⟨116769538048,46745960659⟩ (N E ⟨120259200512,52971284238⟩ E)) ⟨120259202048,47028779282⟩ (N (N E ⟨120259206656,24167967077⟩ E) ⟨120259206912,22897645630⟩ (N E ⟨120259207168,21644686635⟩ E)))) ⟨126701658112,26035399071⟩ (N (N (N (N E ⟨127506964480,26576239224⟩ E) ⟨128043835392,26933009019⟩ (N E ⟨128312270848,27110085185⟩ E)) ⟨128849144064,15052086325⟩ (N (N E ⟨128849145088,10538428373⟩ E) ⟨128849145600,8561332371⟩ (N E ⟨128849146112,6782358188⟩ E))) ⟨128849146624,5207672845⟩ (N (N (N E ⟨128849147392,3237164937⟩ E) ⟨128849148928,713719858⟩ (N E ⟨128849149952,50445805⟩ E)) ⟨129117582336,4539281356⟩ (N (N E ⟨129386020608,151706598⟩ E) ⟨130191325440,1841961107⟩ E)))) ⟨130191326720,315670815⟩ (N (N (N (N (N E ⟨130191327232,62703137⟩ E) ⟨130459759360,5474398739⟩ (N E ⟨130459760896,1861338617⟩ E)) ⟨130996628992,10088336288⟩ (N (N E ⟨130996630272,5558837948⟩ E) ⟨131265066496,3512197228⟩ (N E ⟨131533502720,1935387031⟩ E))) ⟨131801937920,2436142715⟩ (N (N (N E ⟨132070372864,3595269726⟩ E) ⟨132070373632,1970139690⟩ (N E ⟨132338807552,5758467505⟩ E)) ⟨132607244288,2495523884⟩ (N (N E ⟨132607244800,1566528576⟩ E) ⟨132607246080,198292048⟩ E))) ⟨132875680000,2019134457⟩ (N (N (N (N E ⟨132875681024,591713365⟩ E) ⟨133144115456,2034581445⟩ (N E ⟨133144116224,874825748⟩ E)) ⟨133144116992,204555724⟩ (N (N E ⟨133412551424,1216168677⟩ E) ⟨133412552192,379221544⟩ (N E ⟨133680986880,1225850533⟩ E))) ⟨133680987392,609797909⟩ (N (N (N E ⟨133680987648,383390472⟩ E) ⟨133680988160,89440943⟩ (N E ⟨133949422592,897664173⟩ E)) ⟨133949423104,387356150⟩ (N (N E ⟨133949423616,90964259⟩ E) ⟨134217858304,620573348⟩ E)))))

noncomputable def tab12 : CTN :=
  (N (N (N (N (N (N E ⟨134486293760,625557927⟩ E) ⟨134486294016,394656437⟩ (N E ⟨134486294528,93714619⟩ E)) ⟨134754729984,94935037⟩ (N (N E ⟨135023165440,96048277⟩ E) ⟨135560036352,97942758⟩ (N E ⟨135828471808,98719435⟩ E))) ⟨137439084800,23869645⟩ (N (N (N E ⟨137975957504,62458⟩ E) ⟨137975957760,61978⟩ (N E ⟨137975958016,61503⟩ E)) ⟨137975958272,61033⟩ (N (N E ⟨137975958528,60567⟩ E) ⟨137975958784,60105⟩ (N E ⟨137975959040,59648⟩ E)))) ⟨137975959296,59195⟩ (N (N (N (N E ⟨137975959552,58747⟩ E) ⟨137975959808,58303⟩ (N E ⟨137975960064,57863⟩ E)) ⟨137975960320,57427⟩ (N (N E ⟨137975960832,56567⟩ E) ⟨137975961088,56143⟩ (N E ⟨137975962368,54083⟩ E))) ⟨137975963136,52892⟩ (N (N (N E ⟨137975963392,52503⟩ E) ⟨137975963648,52116⟩ (N E ⟨138244393216,27598106⟩ E)) ⟨138244393472,27386590⟩ (N (N E ⟨138244393728,27177098⟩ E) ⟨138244393984,26969606⟩ E)))) ⟨138244394240,26764092⟩ (N (N (N (N (N E ⟨138244394496,26560533⟩ E) ⟨138244394752,26358907⟩ (N E ⟨138244395008,26159191⟩ E)) ⟨138244395264,25961364⟩ (N (N E ⟨138244395520,25765406⟩ E) ⟨138244395776,25571293⟩ (N E ⟨138244396032,25379006⟩ E))) ⟨138244396288,25188525⟩ (N (N (N E ⟨138244396544,24999828⟩ E) ⟨138244397056,24627708⟩ (N E ⟨138244397312,24444246⟩ E)) ⟨138244398336,23727271⟩ (N (N E ⟨138244398592,23552152⟩ E) ⟨138244399104,23206737⟩ E))) ⟨138512828672,105553952⟩ (N (N (N (N E ⟨138512828928,104744971⟩ E) ⟨138512829184,103943730⟩ (N E ⟨138512829440,103150141⟩ E)) ⟨138512829696,102364115⟩ (N (N E ⟨138512829952,101585567⟩ E) ⟨138512830208,100814410⟩ (N E ⟨138512830464,100050562⟩ E))) ⟨138512830720,99293938⟩ (N (N (N E ⟨138512830976,98544458⟩ E) ⟨138512831232,97802040⟩ (N E ⟨138512831488,97066604⟩ E)) ⟨138512831744,96338072⟩ (N (N E ⟨138512832000,95616366⟩ E) ⟨138512832256,94901410⟩ E)))))

noncomputable def tab13 : CTN :=
  (N (N (N (N (N (N E ⟨138512832768,93491444⟩ E) ⟨138512833024,92796286⟩ (N E ⟨138512833280,92107581⟩ E)) ⟨138512833536,91425257⟩ (N (N E ⟨138512834048,90079470⟩ E) ⟨138512834304,89415867⟩ (N E ⟨138512834560,88758367⟩ E))) ⟨138781264384,232525421⟩ (N (N (N E ⟨138781264640,230746731⟩ E) ⟨138781264896,228985026⟩ (N E ⟨138781265152,227240112⟩ E)) ⟨138781265408,225511797⟩ (N (N E ⟨138781265664,223799892⟩ E) ⟨138781265920,222104209⟩ (N E ⟨138781266176,220424566⟩ E)))) ⟨138781266432,218760780⟩ (N (N (N (N E ⟨138781266944,215480063⟩ E) ⟨138781267200,213862781⟩ (N E ⟨138781267456,212260652⟩ E)) ⟨138781267712,210673506⟩ (N (N E ⟨138781268224,207543496⟩ E) ⟨138781268480,206000301⟩ (N E ⟨138781268736,204471431⟩ E))) ⟨138781268992,202956727⟩ (N (N (N E ⟨138781269248,201456030⟩ E) ⟨138781269504,199969186⟩ (N E ⟨138781269760,198496041⟩ E)) ⟨138781270016,197036445⟩ (N (N E ⟨139049700096,407850765⟩ E) ⟨139049700352,404736907⟩ E)))) ⟨139049700608,401652726⟩ (N (N (N (N (N E ⟨139049700864,398597885⟩ E) ⟨139049701120,395572049⟩ (N E ⟨139049701376,392574887⟩ E)) ⟨139049701632,389606074⟩ (N (N E ⟨139049701888,386665289⟩ E) ⟨139049702144,383752215⟩ (N E ⟨139049702400,380866538⟩ E))) ⟨139049702656,378007950⟩ (N (N (N E ⟨139049702912,375176147⟩ E) ⟨139049703168,372370826⟩ (N E ⟨139049703424,369591693⟩ E)) ⟨139049703680,366838452⟩ (N (N E ⟨139049703936,364110816⟩ E) ⟨139049704192,361408500⟩ E))) ⟨139049704960,353450665⟩ (N (N (N (N E ⟨139049705472,348266970⟩ E) ⟨139318136064,625741763⟩ (N E ⟨139318136320,620982573⟩ E)) ⟨139318136576,616268570⟩ (N (N E ⟨139318136832,611599240⟩ E) ⟨139318137088,606974075⟩ (N E ⟨139318137344,602392575⟩ E))) ⟨139318137600,597854246⟩ (N (N (N E ⟨139318137856,593358600⟩ E) ⟨139318138112,588905156⟩ (N E ⟨139318138368,584493440⟩ E)) ⟨139318138624,580122983⟩ (N (N E ⟨139318138880,575793322⟩ E) ⟨139318139136,571504001⟩ E)))))

noncomputable def tab14 : CTN :=
  (N (N (N (N (N (N E ⟨139318139648,563044583⟩ E) ⟨139318139904,558873603⟩ (N E ⟨139318140160,554741196⟩ E)) ⟨139318140416,550646935⟩ (N (N E ⟨139318140672,546590397⟩ E) ⟨139318140928,542571166⟩ (N E ⟨139586571776,892683441⟩ E))) ⟨139586572288,879194582⟩ (N (N (N E ⟨139586572544,872545751⟩ E) ⟨139586572800,865959690⟩ (N E ⟨139586573056,859435688⟩ E)) ⟨139586573312,852973045⟩ (N (N E ⟨139586573568,846571069⟩ E) ⟨139586573824,840229078⟩ (N E ⟨139586574080,833946398⟩ E)))) ⟨139586574336,827722364⟩ (N (N (N (N E ⟨139586574592,821556320⟩ E) ⟨139586574848,815447619⟩ (N E ⟨139586575104,809395621⟩ E)) ⟨139586575360,803399697⟩ (N (N E ⟨139586575616,797459222⟩ E) ⟨139586575872,791573583⟩ (N E ⟨139586576384,779964392⟩ E))) ⟨139855007488,1204383306⟩ (N (N (N E ⟨139855007744,1195257960⟩ E) ⟨139855008000,1186218928⟩ (N E ⟨139855008256,1177265231⟩ E)) ⟨139855008512,1168395904⟩ (N (N E ⟨139855009024,1150906558⟩ E) ⟨139855009280,1142284672⟩ E)))) ⟨139855009536,1133743419⟩ (N (N (N (N (N E ⟨139855009792,1125281895⟩ E) ⟨139855010048,1116899208⟩ (N E ⟨139855010304,1108594478⟩ E)) ⟨139855010560,1100366836⟩ (N (N E ⟨139855010816,1092215424⟩ E) ⟨139855011072,1084139396⟩ (N E ⟨139855011328,1076137917⟩ E))) ⟨139855011584,1068210162⟩ (N (N (N E ⟨139855011840,1060355316⟩ E) ⟨140123443712,1536088714⟩ (N E ⟨140123444224,1513052263⟩ E)) ⟨140123444480,1501696073⟩ (N (N E ⟨140123444736,1490446287⟩ E) ⟨140123444992,1479301710⟩ E))) ⟨140123445248,1468261163⟩ (N (N (N (N E ⟨140123445504,1457323483⟩ E) ⟨140123445760,1446487520⟩ (N E ⟨140123446016,1435752141⟩ E)) ⟨140123446272,1425116228⟩ (N (N E ⟨140123446528,1414578675⟩ E) ⟨140123446784,1404138392⟩ (N E ⟨140123447040,1393794304⟩ E))) ⟨140123447296,1383545347⟩ (N (N (N E ⟨140391879168,1942090232⟩ E) ⟨140391879680,1912965048⟩ (N E ⟨140391879936,1898607319⟩ E)) ⟨140391880192,1884384118⟩ (N (N E ⟨140391880448,1870293933⟩ E) ⟨140391880704,1856335274⟩ E)))))

noncomputable def tab15 : CTN :=
  (N (N (N (N (N (N E ⟨140391881472,1815233837⟩ E) ⟨140391881728,1801786760⟩ (N E ⟨140391881984,1788464040⟩ E)) ⟨140391882240,1775264301⟩ (N (N E ⟨140391882496,1762186180⟩ E) ⟨140391882752,1749228337⟩ (N E ⟨140660315392,2341191223⟩ E))) ⟨140660315648,2323652454⟩ (N (N (N E ⟨140660316160,2289065152⟩ E) ⟨140660316416,2272012966⟩ (N E ⟨140660316672,2255119360⟩ E)) ⟨140660316928,2238382569⟩ (N (N E ⟨140660317184,2221800846⟩ E) ⟨140660317440,2205372470⟩ E))) ⟨140660317696,2189095743⟩ (N (N (N (N E ⟨140660317952,2172968985⟩ E) ⟨140660318208,2156990541⟩ (N E ⟨140928751104,2807689935⟩ E)) ⟨140928751872,2745293482⟩ (N (N E ⟨140928752640,2684621731⟩ E) ⟨140928753664,2606310863⟩ (N E ⟨141197186816,3310877028⟩ E))) ⟨141197187072,3286166793⟩ (N (N (N E ⟨141197187328,3261686787⟩ E) ⟨141197187584,3237434439⟩ (N E ⟨141197187840,3213407211⟩ E)) ⟨141197188352,3166018133⟩ (N (N E ⟨141197188608,3142651370⟩ E) ⟨141197188864,3119499903⟩ E)))) ⟨141197189120,3096561355⟩ (N (N (N (N (N E ⟨141465624064,3680993322⟩ E) ⟨141465624576,3627008003⟩ (N E ⟨141734060032,4196811774⟩ E)) ⟨142002494976,4876549245⟩ (N (N E ⟨142002495488,4805029944⟩ E) ⟨142270930176,5572876630⟩ (N E ⟨142270930944,5450617679⟩ E))) ⟨142539366400,6132429910⟩ (N (N (N E ⟨142807801856,6849223449⟩ E) ⟨143076237312,7599659374⟩ (N E ⟨143344672768,8382305677⟩ E)) ⟨143613108224,9195640158⟩ (N (N E ⟨143881543680,10038053565⟩ E) ⟨144149979136,10907852980⟩ E))) ⟨144418414592,11803265435⟩ (N (N (N (N E ⟨144955285504,13663460618⟩ E) ⟨145223720960,14624332832⟩ (N E ⟨145492156416,15603005798⟩ E)) ⟨146029027584,17476036621⟩ (N (N E ⟨146029027840,17348002527⟩ E) ⟨146029028096,17221139448⟩ (N E ⟨146029028352,17095434549⟩ E))) ⟨146029028608,16970875159⟩ (N (N (N E ⟨146029028864,16847448766⟩ E) ⟨146029029120,16725143020⟩ (N E ⟨146029029376,16603945726⟩ E)) ⟨146029029632,16483844845⟩ (N (N E ⟨146029029888,16364828489⟩ E) ⟨146029030144,16246884921⟩ E)))))

noncomputable def tab16 : CTN :=
  (N (N (N (N (N (N E ⟨146029030656,16014169939⟩ E) ⟨146029030912,15899375782⟩ (N E ⟨146029031168,15785608923⟩ E)) ⟨146029031424,15672858345⟩ (N (N E ⟨146029031680,15561113166⟩ E) ⟨146029031936,15450362643⟩ (N E ⟨146029032192,15340596165⟩ E))) ⟨146029032448,15231803251⟩ (N (N (N E ⟨146029032704,15123973555⟩ E) ⟨146029032960,15017096854⟩ (N E ⟨146029033216,14911163054⟩ E)) ⟨146029033472,14806162186⟩ (N (N E ⟨146029033728,14702084403⟩ E) ⟨146029033984,14598919978⟩ (N E ⟨146029034240,14496659306⟩ E)))) ⟨146029034496,14395292897⟩ (N (N (N (N E ⟨146029034752,14294811379⟩ E) ⟨146029035008,14195205494⟩ (N E ⟨146029035264,14096466096⟩ E)) ⟨146029035520,13998584151⟩ (N (N E ⟨146297470976,14808984781⟩ E) ⟨150055567360,26057484953⟩ (N E ⟨150592438272,27478592978⟩ E))) ⟨151666180096,30036764614⟩ (N (N (N E ⟨154618970368,34174620589⟩ E) ⟨154618970624,33876836922⟩ (N E ⟨154618970880,33541516667⟩ E)) ⟨154618971136,33169706406⟩ (N (N E ⟨154618971392,32762527531⟩ E) ⟨154618971648,32321172538⟩ E)))) ⟨154618972416,30804961588⟩ (N (N (N (N (N E ⟨154618972672,30240113596⟩ E) ⟨154618972928,29647981632⟩ (N E ⟨154618973184,29030101448⟩ E)) ⟨154618973952,27037941846⟩ (N (N E ⟨154618974720,24872928246⟩ E) ⟨154618974976,24120840786⟩ (N E ⟨154618975232,23356458401⟩ E))) ⟨154618975744,21797860699⟩ (N (N (N E ⟨154618976256,20211247886⟩ E) ⟨154618977280,17009903431⟩ (N E ⟨154618978048,14637876662⟩ E)) ⟨154618978304,13861447354⟩ (N (N E ⟨159450816512,15489420729⟩ E) ⟨160524558336,15848294430⟩ E))) ⟨161329864704,16114355173⟩ (N (N (N (N E ⟨161866735616,16289846493⟩ E) ⟨163208914432,11575322320⟩ (N E ⟨163208914688,10778946325⟩ E)) ⟨163208916736,5273449099⟩ (N (N E ⟨163208917248,4174759615⟩ E) ⟨163208918016,2759351698⟩ (N E ⟨163208918272,2351479462⟩ E))) ⟨163208919808,592043860⟩ (N (N (N E ⟨163208920064,413636898⟩ E) ⟨163208920576,153739518⟩ (N E ⟨163208920832,71549112⟩ E)) ⟨163208921088,20615427⟩ (N (N E ⟨164014225152,1674788633⟩ E) ⟨164014225920,828514821⟩ E)))))

noncomputable def tab17 : CTN :=
  (N (N (N (N (N (N E ⟨164551094528,4310135019⟩ E) ⟨165356403456,645293122⟩ (N E ⟨165624837632,2111880884⟩ E)) ⟨165893275648,30333473⟩ (N (N E ⟨166430146560,32068746⟩ E) ⟨166698582016,32896024⟩ (N E ⟨166967016960,191867834⟩ E))) ⟨166967017472,33693717⟩ (N (N (N E ⟨167235451136,1183388587⟩ E) ⟨167235451904,487219197⟩ (N E ⟨167503888384,35192737⟩ E)) ⟨167772323072,329537070⟩ (N (N E ⟨167772323840,35890453⟩ E) ⟨168040759296,36551370⟩ (N E ⟨168309193728,502039951⟩ E)))) ⟨168577630208,37756530⟩ (N (N (N (N E ⟨171798855936,5331210⟩ E) ⟨172335728384,3111994⟩ (N E ⟨172335728896,3073735⟩ E)) ⟨172335729152,3054826⟩ (N (N E ⟨172335729408,3036063⟩ E) ⟨172335729664,3017443⟩ (N E ⟨172335729920,2998966⟩ E))) ⟨172335730176,2980630⟩ (N (N (N E ⟨172335730432,2962434⟩ E) ⟨172335730688,2944377⟩ (N E ⟨172335730944,2926458⟩ E)) ⟨172335731200,2908674⟩ (N (N E ⟨172335731456,2891025⟩ E) ⟨172335731712,2873511⟩ E)))) ⟨172335731968,2856128⟩ (N (N (N (N (N E ⟨172335732224,2838877⟩ E) ⟨172335732480,2821756⟩ (N E ⟨172335732736,2804764⟩ E)) ⟨172335732992,2787899⟩ (N (N E ⟨172335733248,2771162⟩ E) ⟨172335733504,2754549⟩ (N E ⟨172335733760,2738062⟩ E))) ⟨172335734016,2721697⟩ (N (N (N E ⟨172335734272,2705454⟩ E) ⟨172335734528,2689333⟩ (N E ⟨172335734784,2673331⟩ E)) ⟨172604164608,33088669⟩ (N (N E ⟨172604164864,32885430⟩ E) ⟨172604165120,32683749⟩ E))) ⟨172604165376,32483613⟩ (N (N (N (N E ⟨172604165632,32285007⟩ E) ⟨172604165888,32087917⟩ (N E ⟨172604166144,31892329⟩ E)) ⟨172604166400,31698230⟩ (N (N E ⟨172604166656,31505605⟩ E) ⟨172604166912,31314443⟩ (N E ⟨172604167168,31124728⟩ E))) ⟨172604167424,30936449⟩ (N (N (N E ⟨172604167680,30749591⟩ E) ⟨172604167936,30564143⟩ (N E ⟨172604168192,30380091⟩ E)) ⟨172604168448,30197423⟩ (N (N E ⟨172604168960,29836189⟩ E) ⟨172604169216,29657598⟩ E)))))

noncomputable def tab18 : CTN :=
  (N (N (N (N (N (N E ⟨172604169984,29129787⟩ E) ⟨172604170240,28956464⟩ (N E ⟨172872600064,95368031⟩ E)) ⟨172872600576,94200972⟩ (N (N E ⟨172872600832,93624140⟩ E) ⟨172872601088,93051719⟩ (N E ⟨172872601344,92483667⟩ E))) ⟨172872601600,91919944⟩ (N (N (N E ⟨172872601856,91360512⟩ E) ⟨172872602112,90805331⟩ (N E ⟨172872602368,90254363⟩ E)) ⟨172872602624,89707568⟩ (N (N E ⟨172872602880,89164910⟩ E) ⟨172872603136,88626350⟩ (N E ⟨172872603392,88091852⟩ E)))) ⟨172872603648,87561378⟩ (N (N (N (N E ⟨172872603904,87034894⟩ E) ⟨172872604416,85993746⟩ (N E ⟨172872604928,84968126⟩ E)) ⟨172872605184,84461052⟩ (N (N E ⟨172872605440,83957756⟩ E) ⟨172872605696,83458205⟩ (N E ⟨173141036288,186565073⟩ E))) ⟨173141036544,185424407⟩ (N (N (N E ⟨173141036800,184292448⟩ E) ⟨173141037056,183169117⟩ (N E ⟨173141037312,182054335⟩ E)) ⟨173141037568,180948025⟩ (N (N E ⟨173141037824,179850108⟩ E) ⟨173141038080,178760509⟩ E)))) ⟨173141038336,177679153⟩ (N (N (N (N (N E ⟨173141038592,176605963⟩ E) ⟨173141038848,175540867⟩ (N E ⟨173141039104,174483792⟩ E)) ⟨173141039360,173434664⟩ (N (N E ⟨173141039616,172393412⟩ E) ⟨173141039872,171359966⟩ (N E ⟨173141040128,170334255⟩ E))) ⟨173141040384,169316210⟩ (N (N (N E ⟨173141040640,168305763⟩ E) ⟨173141040896,167302844⟩ (N E ⟨173141041152,166307388⟩ E)) ⟨173409472000,309469961⟩ (N (N E ⟨173409472256,307580742⟩ E) ⟨173409472512,305705923⟩ E))) ⟨173409472768,303845373⟩ (N (N (N (N E ⟨173409473024,301998961⟩ E) ⟨173409473280,300166558⟩ (N E ⟨173409473536,298348037⟩ E)) ⟨173409473792,296543272⟩ (N (N E ⟨173409474048,294752139⟩ E) ⟨173409474304,292974513⟩ (N E ⟨173409474560,291210273⟩ E))) ⟨173409474816,289459298⟩ (N (N (N E ⟨173409475072,287721468⟩ E) ⟨173409475328,285996665⟩ (N E ⟨173409475584,284284772⟩ E)) ⟨173409476096,280899255⟩ (N (N E ⟨173409476352,279225402⟩ E) ⟨173409476608,277564003⟩ E)))))

noncomputable def tab19 : CTN :=
  (N (N (N (N (N (N E ⟨173677907968,459519996⟩ E) ⟨173677908224,456723321⟩ (N E ⟨173677908480,453947898⟩ E)) ⟨173677908736,451193533⟩ (N (N E ⟨173677908992,448460034⟩ E) ⟨173677909248,445747213⟩ (N E ⟨173677909504,443054881⟩ E))) ⟨173677909760,440382854⟩ (N (N (N E ⟨173677910016,437730947⟩ E) ⟨173677910272,435098980⟩ (N E ⟨173677910528,432486771⟩ E)) ⟨173677910784,429894145⟩ (N (N E ⟨173677911040,427320924⟩ E) ⟨173677911552,422232004⟩ (N E ⟨173677911808,419715962⟩ E)))) ⟨173677912064,417218641⟩ (N (N (N (N E ⟨173946343168,648476796⟩ E) ⟨173946343680,640601464⟩ (N E ⟨173946343936,636708648⟩ E)) ⟨173946344192,632845367⟩ (N (N E ⟨173946344448,629011354⟩ E) ⟨173946344704,625206343⟩ (N E ⟨173946344960,621430071⟩ E))) ⟨173946345216,617682278⟩ (N (N (N E ⟨173946345472,613962706⟩ E) ⟨173946345728,610271100⟩ (N E ⟨173946345984,606607209⟩ E)) ⟨173946346240,602970783⟩ (N (N E ⟨173946346496,599361576⟩ E) ⟨173946346752,595779343⟩ E)))) ⟨173946347008,592223842⟩ (N (N (N (N (N E ⟨173946347264,588694835⟩ E) ⟨173946347520,585192084⟩ (N E ⟨174214778880,860553826⟩ E)) ⟨174214779136,855316427⟩ (N (N E ⟨174214779392,850118827⟩ E) ⟨174214779648,844960663⟩ (N E ⟨174214779904,839841577⟩ E))) ⟨174214780160,834761213⟩ (N (N (N E ⟨174214780416,829719221⟩ E) ⟨174214780672,824715253⟩ (N E ⟨174214780928,819748965⟩ E)) ⟨174214781184,814820018⟩ (N (N E ⟨174214781440,809928075⟩ E) ⟨174214781696,805072802⟩ E))) ⟨174214781952,800253871⟩ (N (N (N (N E ⟨174214782208,795470955⟩ E) ⟨174214782464,790723732⟩ (N E ⟨174214782720,786011882⟩ E)) ⟨174214782976,781335090⟩ (N (N E ⟨174483214592,1100628111⟩ E) ⟨174483214848,1093939797⟩ (N E ⟨174483215360,1080714948⟩ E))) ⟨174483215616,1074177495⟩ (N (N (N E ⟨174483215872,1067689418⟩ E) ⟨174483216128,1061250272⟩ (N E ⟨174483216384,1054859613⟩ E)) ⟨174483216640,1048517003⟩ (N (N E ⟨174483216896,1042222011⟩ E) ⟨174483217152,1035974207⟩ E)))))

noncomputable def tab20 : CTN :=
  (N (N (N (N (N (N E ⟨174483217664,1023618472⟩ E) ⟨174483218176,1011446461⟩ (N E ⟨174483218432,1005428326⟩ E)) ⟨174751650816,1351320508⟩ (N (N E ⟨174751651072,1343146110⟩ E) ⟨174751651328,1335033452⟩ (N E ⟨174751651584,1326981976⟩ E))) ⟨174751651840,1318991128⟩ (N (N (N E ⟨174751652096,1311060361⟩ E) ⟨174751652352,1303189135⟩ (N E ⟨174751652608,1295376912⟩ E)) ⟨174751652864,1287623163⟩ (N (N E ⟨174751653120,1279927364⟩ E) ⟨174751653376,1272288995⟩ (N E ⟨174751653632,1264707542⟩ E)))) ⟨174751653888,1257182497⟩ (N (N (N (N E ⟨175020087040,1621531463⟩ E) ⟨175020087808,1592457337⟩ (N E ⟨175020088064,1582911040⟩ E)) ⟨175020088320,1573436196⟩ (N (N E ⟨175020088576,1564032164⟩ E) ⟨175020088832,1554698310⟩ (N E ⟨175020089088,1545434006⟩ E))) ⟨175020089344,1536238631⟩ (N (N (N E ⟨175288522752,1932737670⟩ E) ⟨175288523008,1921116598⟩ (N E ⟨175288523264,1909582771⟩ E)) ⟨175288523776,1886773717⟩ (N (N E ⟨175288524032,1875496946⟩ E) ⟨175288524288,1864304328⟩ E)))) ⟨175288524544,1853195110⟩ (N (N (N (N (N E ⟨175288524800,1842168548⟩ E) ⟨175556959232,2227126953⟩ (N E ⟨175556959488,2213815976⟩ E)) ⟨175556959744,2200604333⟩ (N (N E ⟨175556960000,2187491135⟩ E) ⟨175556960256,2174475502⟩ (N E ⟨175825395712,2532594994⟩ E))) ⟨176093831168,2915895760⟩ (N (N (N E ⟨176362266624,3323680930⟩ E) ⟨176630702080,3755189350⟩ (N E ⟨176899137536,4209597088⟩ E)) ⟨177167572992,4686019082⟩ (N (N E ⟨177436008448,5183510966⟩ E) ⟨177704443904,5701071046⟩ E))) ⟨178241314816,6792115318⟩ (N (N (N (N E ⟨178509750272,7363329404⟩ E) ⟨178778185728,7950076462⟩ (N E ⟨179583492096,9790771822⟩ E)) ⟨180120363008,11071513823⟩ (N (N E ⟨180388798720,11654104527⟩ E) ⟨180388798976,11584968342⟩ (N E ⟨180388799232,11516344258⟩ E))) ⟨180388799488,11448227727⟩ (N (N (N E ⟨180388799744,11380614252⟩ E) ⟨180388800000,11313499377⟩ (N E ⟨180388800256,11246878697⟩ E)) ⟨180388800512,11180747848⟩ (N (N E ⟨180388800768,11115102515⟩ E) ⟨180388801024,11049938424⟩ E)))))

noncomputable def tab21 : CTN :=
  (N (N (N (N (N (N E ⟨180388801536,10921037098⟩ E) ⟨180388801792,10857291534⟩ (N E ⟨180388802048,10794010555⟩ E)) ⟨180388802304,10731190103⟩ (N (N E ⟨180388802560,10668826159⟩ E) ⟨180388802816,10606914747⟩ (N E ⟨180388803072,10545451932⟩ E))) ⟨180388803328,10484433817⟩ (N (N (N E ⟨180388803584,10423856546⟩ E) ⟨180388803840,10363716300⟩ (N E ⟨180388804096,10304009300⟩ E)) ⟨180388804352,10244731805⟩ (N (N E ⟨180388804608,10185880112⟩ E) ⟨180388804864,10127450554⟩ (N E ⟨180388805120,10069439501⟩ E)))) ⟨180388805376,10011843362⟩ (N (N (N (N E ⟨180388805632,9954658577⟩ E) ⟨180388805888,9897881626⟩ (N E ⟨180388806144,9841509023⟩ E)) ⟨180388806400,9785537314⟩ (N (N E ⟨180388806656,9729963084⟩ E) ⟨183878467584,16759686315⟩ (N E ⟨184415338496,17738545514⟩ E))) ⟨188978741504,22868327409⟩ (N (N (N E ⟨188978741760,22697744874⟩ E) ⟨188978742016,22501422485⟩ (N E ⟨188978742272,22279969817⟩ E)) ⟨188978742528,22034050636⟩ (N (N E ⟨188978742784,21764380703⟩ E) ⟨188978743040,21471725482⟩ E)))) ⟨188978743296,21156897754⟩ (N (N (N (N (N E ⟨188978743552,20820755150⟩ E) ⟨188978743808,20464197604⟩ (N E ⟨188978744064,20088164734⟩ E)) ⟨188978744320,19693633166⟩ (N (N E ⟨188978744576,19281613785⟩ E) ⟨188978744832,18853148956⟩ (N E ⟨188978745088,18409309687⟩ E))) ⟨188978745600,17479917837⟩ (N (N (N E ⟨188978745856,16996624543⟩ E) ⟨188978746112,16502469524⟩ (N E ⟨188978746368,15998623519⟩ E)) ⟨188978746624,15486268406⟩ (N (N E ⟨188978746880,14966594275⟩ E) ⟨188978747136,14440796504⟩ E))) ⟨188978747648,13375620595⟩ (N (N (N (N E ⟨188978747904,12838633661⟩ E) ⟨188978748160,12300299849⟩ (N E ⟨188978748672,11224295565⟩ E)) ⟨188978748928,10688945415⟩ (N (N E ⟨188978749440,9629227507⟩ E) ⟨193273716736,10448099292⟩ (N E ⟨195152764928,10801615209⟩ E))) ⟨197568684288,10648370487⟩ (N (N (N E ⟨197568686080,6762594557⟩ E) ⟨197568686336,6256984451⟩ (N E ⟨197568687104,4834930976⟩ E)) ⟨197568687872,3571324368⟩ (N (N E ⟨197568688640,2483741266⟩ E) ⟨197568689408,1585530720⟩ E)))))

noncomputable def tab22 : CTN :=
  (N (N (N (N (N (N E ⟨197568690176,885669736⟩ E) ⟨197568690688,531721289⟩ (N E ⟨197568690944,388714969⟩ E)) ⟨197568691200,268308993⟩ (N (N E ⟨197568692224,9929527⟩ E) ⟨197837124352,2175597807⟩ (N E ⟨198105563136,10902792⟩ E))) ⟨198642431744,1127433199⟩ (N (N (N E ⟨198642433024,280516761⟩ E) ⟨199716174336,568245959⟩ (N E ⟨200521480960,428434824⟩ E)) ⟨200521481728,111668556⟩ (N (N E ⟨201326788096,115476336⟩ E) ⟨201326788608,16228754⟩ (N E ⟨202132094976,17286823⟩ E)))) ⟨206158627072,1073573⟩ (N (N (N (N E ⟨206695500288,5415393⟩ E) ⟨206695500544,5387602⟩ (N E ⟨206695500800,5359988⟩ E)) ⟨206695501056,5332552⟩ (N (N E ⟨206695501312,5305291⟩ E) ⟨206695501568,5278204⟩ (N E ⟨206695501824,5251289⟩ E))) ⟨206695502080,5224546⟩ (N (N (N E ⟨206695502336,5197973⟩ E) ⟨206695502592,5171569⟩ (N E ⟨206695502848,5145332⟩ E)) ⟨206695503104,5119262⟩ (N (N E ⟨206695503360,5093356⟩ E) ⟨206695503616,5067614⟩ E)))) ⟨206695503872,5042035⟩ (N (N (N (N (N E ⟨206695504384,4991359⟩ E) ⟨206695504896,4941318⟩ (N E ⟨206695505152,4916532⟩ E)) ⟨206695505408,4891902⟩ (N (N E ⟨206695505920,4843103⟩ E) ⟨206963936000,32025819⟩ (N E ⟨206963936256,31861675⟩ E))) ⟨206963936512,31698583⟩ (N (N (N E ⟨206963936768,31536533⟩ E) ⟨206963937024,31375517⟩ (N E ⟨206963937280,31215528⟩ E)) ⟨206963937536,31056558⟩ (N (N E ⟨206963937792,30898599⟩ E) ⟨206963938048,30741643⟩ E))) ⟨206963938304,30585683⟩ (N (N (N (N E ⟨206963938560,30430710⟩ E) ⟨206963938816,30276719⟩ (N E ⟨206963939072,30123700⟩ E)) ⟨206963939584,29820552⟩ (N (N E ⟨206963939840,29670409⟩ E) ⟨206963940096,29521210⟩ (N E ⟨206963940352,29372947⟩ E))) ⟨206963940608,29225615⟩ (N (N (N E ⟨206963940864,29079205⟩ E) ⟨206963941376,28789126⟩ (N E ⟨207232371968,80214294⟩ E)) ⟨207232372224,79804221⟩ (N (N E ⟨207232372480,79396766⟩ E) ⟨207232372736,78991909⟩ E)))))

noncomputable def tab23 : CTN :=
  (N (N (N (N (N (N E ⟨207232373248,78189909⟩ E) ⟨207232373504,77792727⟩ (N E ⟨207232373760,77398064⟩ E)) ⟨207232374016,77005902⟩ (N (N E ⟨207232374272,76616220⟩ E) ⟨207232374528,76229002⟩ (N E ⟨207232374784,75844227⟩ E))) ⟨207232375040,75461877⟩ (N (N (N E ⟨207232375296,75081935⟩ E) ⟨207232375552,74704381⟩ (N E ⟨207232375808,74329198⟩ E)) ⟨207232376064,73956368⟩ (N (N E ⟨207232376576,73217696⟩ E) ⟨207232376832,72851820⟩ E))) ⟨207500807168,151709878⟩ (N (N (N (N E ⟨207500807680,150161707⟩ E) ⟨207500807936,149395029⟩ (N E ⟨207500808192,148633239⟩ E)) ⟨207500808448,147876300⟩ (N (N E ⟨207500808704,147124175⟩ E) ⟨207500808960,146376826⟩ (N E ⟨207500809216,145634218⟩ E))) ⟨207500809472,144896315⟩ (N (N (N E ⟨207500809728,144163081⟩ E) ⟨207500809984,143434480⟩ (N E ⟨207500810240,142710477⟩ E)) ⟨207500810496,141991038⟩ (N (N E ⟨207500810752,141276129⟩ E) ⟨207500811008,140565714⟩ E)))) ⟨207500811264,139859760⟩ (N (N (N (N (N E ⟨207500811520,139158233⟩ E) ⟨207500811776,138461100⟩ (N E ⟨207500812288,137079886⟩ E)) ⟨207769242880,243855286⟩ (N (N E ⟨207769243392,241369963⟩ E) ⟨207769243648,240139178⟩ (N E ⟨207769244160,237701059⟩ E))) ⟨207769244416,236493606⟩ (N (N (N E ⟨207769244672,235293812⟩ E) ⟨207769244928,234101620⟩ (N E ⟨207769245440,231739807⟩ E)) ⟨207769245696,230570072⟩ (N (N E ⟨207769245952,229407711⟩ E) ⟨207769246208,228252668⟩ E))) ⟨207769246720,225964312⟩ (N (N (N (N E ⟨207769246976,224830891⟩ E) ⟨207769247232,223704570⟩ (N E ⟨207769247488,222585294⟩ E)) ⟨207769247744,221473012⟩ (N (N E ⟨208037679616,349867349⟩ E) ⟨208037679872,348090124⟩ (N E ⟨208037680128,346324172⟩ E))) ⟨208037680384,344569408⟩ (N (N (N E ⟨208037680640,342825746⟩ E) ⟨208037680896,341093103⟩ (N E ⟨208037681152,339371396⟩ E)) ⟨208037681408,337660540⟩ (N (N E ⟨208037681664,335960455⟩ E) ⟨208037681920,334271059⟩ E)))))

noncomputable def tab24 : CTN :=
  (N (N (N (N (N (N E ⟨208037682432,330924012⟩ E) ⟨208037682688,329266202⟩ (N E ⟨208037682944,327618763⟩ E)) ⟨208037683200,325981618⟩ (N (N E ⟨208306114560,488476289⟩ E) ⟨208306115328,481060692⟩ (N E ⟨208306115584,478620146⟩ E))) ⟨208306115840,476195061⟩ (N (N (N E ⟨208306116096,473785320⟩ E) ⟨208306116352,471390807⟩ (N E ⟨208306116608,469011406⟩ E)) ⟨208306116864,466647003⟩ (N (N E ⟨208306117120,464297485⟩ E) ⟨208306117376,461962738⟩ (N E ⟨208306117632,459642653⟩ E)))) ⟨208306117888,457337118⟩ (N (N (N (N E ⟨208306118144,455046024⟩ E) ⟨208306118400,452769263⟩ (N E ⟨208306118656,450506728⟩ E)) ⟨208574551296,628821740⟩ (N (N E ⟨208574551552,625639646⟩ E) ⟨208574551808,622477660⟩ (N E ⟨208574552320,616213406⟩ E))) ⟨208574552576,613110836⟩ (N (N (N E ⟨208574552832,610027773⟩ E) ⟨208574553088,606964071⟩ (N E ⟨208574553344,603919582⟩ E)) ⟨208574553600,600894163⟩ (N (N E ⟨208574553856,597887671⟩ E) ⟨208574554112,594899963⟩ E)))) ⟨208842986496,806326015⟩ (N (N (N (N (N E ⟨208842987264,794146828⟩ E) ⟨208842987520,790138278⟩ (N E ⟨208842987776,786154995⟩ E)) ⟨208842988032,782196787⟩ (N (N E ⟨208842988288,778263466⟩ E) ⟨208842988544,774354844⟩ (N E ⟨208842988800,770470735⟩ E))) ⟨208842989056,766610955⟩ (N (N (N E ⟨208842989312,762775322⟩ E) ⟨208842989568,758963653⟩ (N E ⟨209111422464,991149420⟩ E)) ⟨209111422976,981162487⟩ (N (N E ⟨209111423232,976216203⟩ E) ⟨209111423488,971301057⟩ E))) ⟨209111423744,966416815⟩ (N (N (N (N E ⟨209111424000,961563243⟩ E) ⟨209111424256,956740110⟩ (N E ⟨209111424512,951947188⟩ E)) ⟨209111424768,947184249⟩ (N (N E ⟨209111425024,942451069⟩ E) ⟨209379858944,1180119175⟩ (N E ⟨209379859456,1168287846⟩ E))) ⟨209379859712,1162427798⟩ (N (N (N E ⟨209379859968,1156604455⟩ E) ⟨209379860480,1145066785⟩ (N E ⟨209648295168,1387184938⟩ E)) ⟨209648295936,1366467147⟩ (N (N E ⟨209916731392,1606260880⟩ E) ⟨210185166848,1864009804⟩ E)))))

noncomputable def tab25 : CTN :=
  (N (N (N (N (N (N E ⟨210722037760,2431391112⟩ E) ⟨210990473216,2739920731⟩ (N E ⟨211258908672,3064202262⟩ E)) ⟨211527344128,3403577882⟩ (N (N E ⟨211795779584,3757349609⟩ E) ⟨212064215040,4124780812⟩ (N E ⟨212332650496,4505097824⟩ E))) ⟨212601085952,4897491654⟩ (N (N (N E ⟨213943263232,7010060751⟩ E) ⟨214748569856,8322438682⟩ (N E ⟨214748570112,8280954363⟩ E)) ⟨214748570368,8239728268⟩ (N (N E ⟨214748570624,8198758471⟩ E) ⟨214748570880,8158043061⟩ (N E ⟨214748571136,8117580146⟩ E)))) ⟨214748571392,8077367847⟩ (N (N (N (N E ⟨214748571648,8037404305⟩ E) ⟨214748571904,7997687674⟩ (N E ⟨214748572160,7958216125⟩ E)) ⟨214748572416,7918987845⟩ (N (N E ⟨214748572672,7880001038⟩ E) ⟨214748572928,7841253920⟩ (N E ⟨214748573184,7802744726⟩ E))) ⟨214748573440,7764471704⟩ (N (N (N E ⟨214748573696,7726433117⟩ E) ⟨214748573952,7688627245⟩ (N E ⟨214748574208,7651052380⟩ E)) ⟨214748574464,7613706830⟩ (N (N E ⟨214748574720,7576588917⟩ E) ⟨214748574976,7539696979⟩ E)))) ⟨214748575232,7503029365⟩ (N (N (N (N (N E ⟨214748575488,7466584440⟩ E) ⟨214748575744,7430360584⟩ (N E ⟨214748576000,7394356188⟩ E)) ⟨214748576256,7358569658⟩ (N (N E ⟨214748576512,7322999415⟩ E) ⟨214748576768,7287643890⟩ (N E ⟨214748577024,7252501531⟩ E))) ⟨214748577280,7217570796⟩ (N (N (N E ⟨214748577536,7182850157⟩ E) ⟨214748577792,7148338100⟩ (N E ⟨217701367808,11436808593⟩ E)) ⟨218238238720,12160886856⟩ (N (N E ⟨223338512640,16371937440⟩ E) ⟨223338512896,16264029169⟩ E))) ⟨223338513152,16137422570⟩ (N (N (N (N E ⟨223338513408,15992507623⟩ E) ⟨223338513664,15829714926⟩ (N E ⟨223338513920,15649514276⟩ E)) ⟨223338514176,15452413173⟩ (N (N E ⟨223338514432,15238955248⟩ E) ⟨223338514688,15009718625⟩ (N E ⟨223338514944,14765314206⟩ E))) ⟨223338515200,14506383906⟩ (N (N (N E ⟨223338515456,14233598825⟩ E) ⟨223338515712,13947657371⟩ (N E ⟨223338515968,13649283334⟩ E)) ⟨223338516224,13339223920⟩ (N (N E ⟨223338516480,13018247744⟩ E) ⟨223338516736,12687142798⟩ E)))))

noncomputable def tab26 : CTN :=
  (N (N (N (N (N (N E ⟨223338517248,11997783053⟩ E) ⟨223338517504,11641182452⟩ (N E ⟨223338517760,11277757267⟩ E)) ⟨223338518016,10908361077⟩ (N (N E ⟨223338518272,10533854239⟩ E) ⟨223338518528,10155101777⟩ (N E ⟨223338518784,9772971268⟩ E))) ⟨223338519040,9388330754⟩ (N (N (N E ⟨223338519552,8614981766⟩ E) ⟨223338519808,8227993137⟩ (N E ⟨223338520320,7457632652⟩ E)) ⟨223338520576,7075928778⟩ (N (N E ⟨231928455680,7234651425⟩ E) ⟨231928455936,6823550428⟩ (N E ⟨231928456448,6020404688⟩ E)))) ⟨231928456704,5629958027⟩ (N (N (N (N E ⟨231928456960,5247953102⟩ E) ⟨231928457728,4159794995⟩ (N E ⟨231928457984,3818615749⟩ E)) ⟨231928458496,3172293833⟩ (N (N E ⟨231928458752,2868276071⟩ E) ⟨231928459264,2301074089⟩ (N E ⟨231928460032,1558890242⟩ E))) ⟨231928460288,1341936689⟩ (N (N (N E ⟨231928461056,786333379⟩ E) ⟨231928462592,117429720⟩ (N E ⟨231928462848,63774241⟩ E)) ⟨231928463360,5355706⟩ (N (N E ⟨233002204160,195021022⟩ E) ⟨234612817664,32164028⟩ E)))) ⟨240518398208,118725⟩ (N (N (N (N (N E ⟨241055273216,6216448⟩ E) ⟨241055274240,6108584⟩ (N E ⟨241055274496,6081984⟩ E)) ⟨241055274752,6055529⟩ (N (N E ⟨241055275008,6029218⟩ E) ⟨241055275264,6003050⟩ (N E ⟨241055275520,5977023⟩ E))) ⟨241055276032,5925392⟩ (N (N (N E ⟨241055276288,5899785⟩ E) ⟨241055276800,5848985⟩ (N E ⟨241055277056,5823791⟩ E)) ⟨241323708160,28594094⟩ (N (N E ⟨241323708416,28468763⟩ E) ⟨241323708672,28344117⟩ E))) ⟨241323708928,28220154⟩ (N (N (N (N E ⟨241323709184,28096867⟩ E) ⟨241323709440,27974253⟩ (N E ⟨241323709696,27852307⟩ E)) ⟨241323709952,27731025⟩ (N (N E ⟨241323710208,27610402⟩ E) ⟨241323710464,27490435⟩ (N E ⟨241323710720,27371119⟩ E))) ⟨241323710976,27252450⟩ (N (N (N E ⟨241323711232,27134423⟩ E) ⟨241323711488,27017034⟩ (N E ⟨241323711744,26900280⟩ E)) ⟨241323712000,26784156⟩ (N (N E ⟨241323712512,26553782⟩ E) ⟨241592144128,66546735⟩ E)))))

noncomputable def tab27 : CTN :=
  (N (N (N (N (N (N E ⟨241592145408,65107307⟩ E) ⟨241592145664,64824108⟩ (N E ⟨241592145920,64542448⟩ E)) ⟨241592146432,63983702⟩ (N (N E ⟨241592146688,63706596⟩ E) ⟨241592146944,63430990⟩ (N E ⟨241592147200,63156873⟩ E))) ⟨241592147456,62884235⟩ (N (N (N E ⟨241592147712,62613067⟩ E) ⟨241592147968,62343359⟩ (N E ⟨241860579584,120838511⟩ E)) ⟨241860579840,120310020⟩ (N (N E ⟨241860580352,119261679⟩ E) ⟨241860580608,118741791⟩ E))) ⟨241860580864,118224734⟩ (N (N (N (N E ⟨241860581120,117710488⟩ E) ⟨241860581376,117199036⟩ (N E ⟨241860581632,116690360⟩ E)) ⟨241860581888,116184441⟩ (N (N E ⟨241860582144,115681261⟩ E) ⟨241860582400,115180802⟩ (N E ⟨241860582656,114683048⟩ E))) ⟨241860582912,114187980⟩ (N (N (N E ⟨241860583424,113205834⟩ E) ⟨242129015040,191194539⟩ (N E ⟨242129015296,190358343⟩ E)) ⟨242129015552,189526715⟩ (N (N E ⟨242129015808,188699625⟩ E) ⟨242129016064,187877042⟩ E)))) ⟨242129016320,187058937⟩ (N (N (N (N (N E ⟨242129016576,186245282⟩ E) ⟨242129016832,185436046⟩ (N E ⟨242129017088,184631202⟩ E)) ⟨242129017344,183830721⟩ (N (N E ⟨242129017600,183034573⟩ E) ⟨242129017856,182242732⟩ (N E ⟨242129018112,181455169⟩ E))) ⟨242129018368,180671857⟩ (N (N (N E ⟨242129018624,179892768⟩ E) ⟨242129018880,179117874⟩ (N E ⟨242397451008,275129565⟩ E)) ⟨242397451520,272734790⟩ (N (N E ⟨242397451776,271547175⟩ E) ⟨242397452032,270366018⟩ E))) ⟨242397452288,269191278⟩ (N (N (N (N E ⟨242397452544,268022913⟩ E) ⟨242397452800,266860881⟩ (N E ⟨242397453568,263412373⟩ E)) ⟨242397454080,261144287⟩ (N (N E ⟨242397454336,260019400⟩ E) ⟨242665886208,378142505⟩ (N E ⟨242665886720,374847499⟩ E))) ⟨242665886976,373213456⟩ (N (N (N E ⟨242665887232,371588310⟩ E) ⟨242665887744,368364474⟩ (N E ⟨242665888000,366765670⟩ E)) ⟨242665888256,365175531⟩ (N (N E ⟨242665888512,363594003⟩ E) ⟨242665888768,362021029⟩ E)))))

noncomputable def tab28 : CTN :=
  (N (N (N (N (N (N E ⟨242665889536,357352878⟩ E) ⟨242665889792,355813570⟩ (N E ⟨242934321664,495633516⟩ E)) ⟨242934322944,484924391⟩ (N (N E ⟨242934323200,482817396⟩ E) ⟨242934323456,480721833⟩ (N E ⟨242934323712,478637630⟩ E))) ⟨242934323968,476564712⟩ (N (N (N E ⟨242934324224,474503005⟩ E) ⟨242934324480,472452439⟩ (N E ⟨242934324736,470412939⟩ E)) ⟨242934324992,468384434⟩ (N (N E ⟨242934325248,466366854⟩ E) ⟨243202758400,615046369⟩ (N E ⟨243202758656,612373993⟩ E)))) ⟨243202759168,607072652⟩ (N (N (N (N E ⟨243202759424,604443498⟩ E) ⟨243202759680,601828565⟩ (N E ⟨243202759936,599227760⟩ E)) ⟨243202760192,596640992⟩ (N (N E ⟨243202760704,591509203⟩ E) ⟨243471194880,747019533⟩ (N E ⟨243471195136,743787790⟩ E))) ⟨243471195392,740573507⟩ (N (N (N E ⟨243471196160,731034299⟩ E) ⟨243739630336,904045283⟩ (N E ⟨243739630592,900134217⟩ E)) ⟨243739631616,884699904⟩ (N (N E ⟨244008067072,1052228295⟩ E) ⟨244276502528,1233306783⟩ E)))) ⟨244544937984,1427588329⟩ (N (N (N (N (N E ⟨244813373440,1634692240⟩ E) ⟨245081808896,1854204952⟩ (N E ⟨245350244352,2085680892⟩ E)) ⟨245618679808,2328643438⟩ (N (N E ⟨245887115264,2582585939⟩ E) ⟨246155550720,2846972824⟩ (N E ⟨246423986176,3121240784⟩ E))) ⟨249108340992,6239369381⟩ (N (N (N E ⟨249108341248,6212550927⟩ E) ⟨249108341504,6185876437⟩ (N E ⟨249108341760,6159344984⟩ E)) ⟨249108342016,6132955649⟩ (N (N E ⟨249108342272,6106707518⟩ E) ⟨249108342528,6080599687⟩ E))) ⟨249108342784,6054631256⟩ (N (N (N (N E ⟨249108343040,6028801332⟩ E) ⟨249108343296,6003109029⟩ (N E ⟨249108343552,5977553470⟩ E)) ⟨249108343808,5952133780⟩ (N (N E ⟨249108344064,5926849095⟩ E) ⟨249108344320,5901698554⟩ (N E ⟨249108344576,5876681304⟩ E))) ⟨249108344832,5851796498⟩ (N (N (N E ⟨249108345088,5827043295⟩ E) ⟨249108345344,5802420861⟩ (N E ⟨249108345600,5777928368⟩ E)) ⟨249108345856,5753564994⟩ (N (N E ⟨249108346112,5729329922⟩ E) ⟨249108346368,5705222343⟩ E)))))

noncomputable def tab29 : CTN :=
  (N (N (N (N (N (N E ⟨249108346880,5657386450⟩ E) ⟨249108347136,5633656546⟩ (N E ⟨249108347392,5610050953⟩ E)) ⟨249108347648,5586568890⟩ (N (N E ⟨249108347904,5563209583⟩ E) ⟨249108348416,5516856162⟩ (N E ⟨249108348672,5493860527⟩ E))) ⟨249108348928,5470984602⟩ (N (N (N E ⟨257698283776,12297695318⟩ E) ⟨257698284032,12224472446⟩ (N E ⟨257698284288,12137070023⟩ E)) ⟨257698284544,12035754896⟩ (N (N E ⟨257698284800,11920825333⟩ E) ⟨257698285056,11792610047⟩ (N E ⟨257698285312,11651467159⟩ E)))) ⟨257698285568,11497783098⟩ (N (N (N (N E ⟨257698285824,11331971444⟩ E) ⟨257698286080,11154471714⟩ (N E ⟨257698286336,10965748097⟩ E)) ⟨257698286592,10766288143⟩ (N (N E ⟨257698286848,10556601403⟩ E) ⟨257698287104,10337218034⟩ (N E ⟨257698287616,9871576391⟩ E))) ⟨257698287872,9626468354⟩ (N (N (N E ⟨257698288128,9373961137⟩ E) ⟨257698288384,9114665747⟩ (N E ⟨257698288640,8849204752⟩ E)) ⟨257698288896,8578210688⟩ (N (N E ⟨257698289152,8302324476⟩ E) ⟨257698289664,7738471579⟩ E)))) ⟨257698289920,7451814225⟩ (N (N (N (N (N E ⟨257698290176,7162880181⟩ E) ⟨257698290432,6872328267⟩ (N E ⟨257698290944,6288998599⟩ E)) ⟨257698291200,5997526311⟩ (N (N E ⟨257698291456,5707044022⟩ E) ⟨257698291712,5418189199⟩ (N E ⟨266288226560,5761840971⟩ E))) ⟨266288227072,5142792756⟩ (N (N (N E ⟨266288227328,4839337425⟩ E) ⟨266288227584,4540766178⟩ (N E ⟨266288228096,3960691133⟩ E)) ⟨266288228864,3141808217⟩ (N (N E ⟨266288229120,2884645835⟩ E) ⟨266288229376,2636207502⟩ E))) ⟨266288229632,2396951801⟩ (N (N (N (N E ⟨266288229888,2167311862⟩ E) ⟨266288230656,1540019276⟩ (N E ⟨266288230912,1352637219⟩ E)) ⟨266288231168,1176628374⟩ (N (N E ⟨266288231424,1012258310⟩ E) ⟨266288231680,859762868⟩ (N E ⟨266288233216,203553388⟩ E))) ⟨266288234496,3137894⟩ (N (N (N E ⟨275146610432,2799⟩ E) ⟨275146612736,2705⟩ (N E ⟨275415046144,6260001⟩ E)) ⟨275415047424,6141859⟩ (N (N E ⟨275415048192,6072310⟩ E) ⟨275683481344,24640486⟩ E)))))

noncomputable def tab30 : CTN :=
  (N (N (N (N (N (N E ⟨275683482112,24359874⟩ E) ⟨275683483648,23810535⟩ (N E ⟨275951917312,54679041⟩ E)) ⟨275951917568,54470880⟩ (N (N E ⟨275951917824,54263710⟩ E) ⟨275951918080,54057523⟩ (N E ⟨275951918592,53648081⟩ E))) ⟨275951919104,53242508⟩ (N (N (N E ⟨276220353280,96174983⟩ E) ⟨276220353536,95809546⟩ (N E ⟨276220354048,95083865⟩ E)) ⟨276220354560,94365042⟩ (N (N E ⟨276488788992,149399000⟩ E) ⟨276488789504,148267421⟩ (N E ⟨276488790016,147146538⟩ E)))) ⟨276757225216,212330684⟩ (N (N (N (N E ⟨276757225472,211526945⟩ E) ⟨277025660928,287417804⟩ (N E ⟨277294096384,374702349⟩ E)) ⟨277830967296,582845026⟩ (N (N E ⟨278099402752,703330025⟩ E) ⟨278367838208,834463136⟩ (N E ⟨278636273664,975990077⟩ E))) ⟨278904709120,1127630341⟩ (N (N (N E ⟨279173144576,1289077782⟩ E) ⟨279710015488,1640045351⟩ (N E ⟨280515321856,2230999488⟩ E)) ⟨282931240960,4353297621⟩ (N (N E ⟨283468112128,4850758660⟩ E) ⟨283468112384,4832431715⟩ E)))) ⟨283468113152,4777967830⟩ (N (N (N (N (N E ⟨283468113408,4759983897⟩ E) ⟨283468113664,4742084510⟩ (N E ⟨283468114432,4688888873⟩ E)) ⟨283468114688,4671322934⟩ (N (N E ⟨283468114944,4653839189⟩ E) ⟨283468115456,4619116438⟩ (N E ⟨283468116480,4550637173⟩ E))) ⟨283468117248,4500109098⟩ (N (N (N E ⟨283468117760,4466813021⟩ E) ⟨283468118272,4433824364⟩ (N E ⟨283468118528,4417444254⟩ E)) ⟨283468118784,4401139726⟩ (N (N E ⟨283468119296,4368755751⟩ E) ⟨283468119552,4352675475⟩ E))) ⟨283468120064,4320736295⟩ (N (N (N (N E ⟨292058054912,9575208023⟩ E) ⟨292058055168,9522859734⟩ (N E ⟨292058055424,9459397479⟩ E)) ⟨292058055680,9385013290⟩ (N (N E ⟨292058055936,9299924162⟩ E) ⟨292058056704,8982956468⟩ (N E ⟨292058056960,8857691173⟩ E))) ⟨292058057216,8723154014⟩ (N (N (N E ⟨292058057472,8579695262⟩ E) ⟨292058057984,8267508144⟩ (N E ⟨292058058240,8099571304⟩ E)) ⟨292058058496,7924293774⟩ (N (N E ⟨292058058752,7742110373⟩ E) ⟨292058059008,7553469500⟩ E)))))

noncomputable def tab31 : CTN :=
  (N (N (N (N (N (N E ⟨292058060032,6743708678⟩ E) ⟨292058060288,6529898878⟩ (N E ⟨292058060544,6312540405⟩ E)) ⟨292058060800,6092142989⟩ (N (N E ⟨292058061312,5644287947⟩ E) ⟨292058061568,5417863720⟩ (N E ⟨292058061824,5190464847⟩ E))) ⟨292058062848,4281402733⟩ (N (N (N E ⟨300647997696,4494939674⟩ E) ⟨300647997952,4253388679⟩ (N E ⟨300647998208,4014461555⟩ E)) ⟨300647998464,3778665077⟩ (N (N E ⟨300647998720,3546494959⟩ E) ⟨300647999232,3094954757⟩ E))) ⟨300647999488,2876511055⟩ (N (N (N (N E ⟨300647999744,2663544470⟩ E) ⟨300648001536,1359554913⟩ (N E ⟨300648003840,288934345⟩ E)) ⟨300648004608,106003817⟩ (N (N E ⟨300648005120,34076216⟩ E) ⟨309774819328,5943166⟩ (N E ⟨310043254784,21137608⟩ E))) ⟨310311690240,45673612⟩ (N (N (N E ⟨310580125696,79540211⟩ E) ⟨310848561152,122703764⟩ (N E ⟨311116996608,175107963⟩ E)) ⟨311922302976,386862971⟩ (N (N E ⟨312459173888,572193205⟩ E) ⟨312727609344,677603799⟩ E)))) ⟨312996044800,791238073⟩ (N (N (N (N (N E ⟨314606657536,1631429101⟩ E) ⟨317827889152,3591737619⟩ (N E ⟨317827890944,3509631742⟩ E)) ⟨317827891200,3498094663⟩ (N (N E ⟨326417827072,7457388810⟩ E) ⟨326417828608,6895656581⟩ (N E ⟨326417829376,6517186090⟩ E))) ⟨326417830144,6084660428⟩ (N (N (N E ⟨326417830912,5607643480⟩ E) ⟨326417831936,4920368510⟩ (N E ⟨326417832192,4742085252⟩ E)) ⟨326417832960,4198341943⟩ (N (N E ⟨326417833472,3832604937⟩ E) ⟨326417833984,3468145225⟩ E))) ⟨335007768832,3604226111⟩ (N (N (N (N E ⟨335007769600,3032044825⟩ E) ⟨335007771136,1973195691⟩ (N E ⟨335007771904,1506224467⟩ E)) ⟨335007772160,1361974004⟩ (N (N E ⟨335007772672,1092253422⟩ E) ⟨335007772928,967282472⟩ (N E ⟨335007774464,368847381⟩ E))) ⟨335007775744,83809971⟩ (N (N (N E ⟨335007776256,26382087⟩ E) ⟨335007776512,9811531⟩ (N E ⟨344939896832,67788449⟩ E)) ⟨352187662336,2889629010⟩ (N (N E ⟨360777605120,2866362512⟩ E) ⟨369367546880,67894699⟩ E)))))

noncomputable def table : CTN :=
  (N (N (N (N (N tab0 ⟨37044132864,1916013694⟩ tab1) ⟨67578691584,1627636972⟩ (N tab2 ⟨70263049024,353201598⟩ tab3)) ⟨71001246848,2109142857⟩ (N (N tab4 ⟨72007881152,6474050494⟩ tab5) ⟨92341885440,67628919902⟩ (N tab6 ⟨100965383808,775774854⟩ tab7))) ⟨104153059328,82142915⟩ (N (N (N tab8 ⟨104958369792,695141519⟩ tab9) ⟨106032111104,2603242176⟩ (N tab10 ⟨111669261312,24304171983⟩ tab11)) ⟨134217859072,92389963⟩ (N (N tab12 ⟨138512832512,94193128⟩ tab13) ⟨139318139392,567254570⟩ (N tab14 ⟨140391880960,1842506671⟩ tab15)))) ⟨146029030400,16130002552⟩ (N (N (N (N tab16 ⟨164282660608,1688171069⟩ tab17) ⟨172604169472,29480342⟩ (N tab18 ⟨173677907712,462338118⟩ tab19)) ⟨174483217408,1029773167⟩ (N (N tab20 ⟨180388801280,10985251347⟩ tab21) ⟨197568689664,1329888956⟩ (N tab22 ⟨207232372992,78589630⟩ tab23))) ⟨208037682176,332592271⟩ (N (N (N tab24 ⟨210453602304,2139229668⟩ tab25) ⟨223338516992,12346714390⟩ (N tab26 ⟨241592144384,66255691⟩ tab27)) ⟨242665889280,358900521⟩ (N (N tab28 ⟨249108346624,5681241451⟩ tab29) ⟨275683481856,24452966⟩ (N tab30 ⟨292058059776,6953465123⟩ tab31)))))

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

theorem cover0_ok : SixW15S2K.coverCheck table 25326800 (SC / 2) 401408 cover0 = true := by decide +kernel

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
  (88832, 88960, true),
  (88960, 89088, true),
  (89088, 237568, false)]

theorem cover1_ok : SixW15S2K.coverCheck table 48244400 (SC / 2) 237568 cover1 = true := by decide +kernel

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

theorem cover2_ok : SixW15S2K.coverCheck table 52857300 (SC / 2) 221184 cover2 = true := by decide +kernel

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

theorem cover3_ok : SixW15S2K.coverCheck table 48244400 (SC / 2) 237568 cover3 = true := by decide +kernel

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
  (57856, 401408, false)]

theorem cover4_ok : SixW15S2K.coverCheck table 25326800 (SC / 2) 401408 cover4 = true := by decide +kernel

def bits : ℕ := 36435446301200517038870843188888535520745339622302846919411032139705188395953613569342312166293131815799709076525715448050775360700023232621979902737794858231909891019274862569988653486363694917211092232870350558739424355560876578473337140187559493655105380699115350638117361781910146692264423727079575377797230838004538266800072761574440952560326164041179591256210694621531137296150466355560669344407472385881536833991858704400368230474928823744478473552434139866105520259078550581122875838823904289904081283458099549418577364656598392125020595227871795750638387203074578252807357454617154030379534338562421431745514261736656021893363467574668123261293788947846874885731425903971372213857425729982638816561062801453622016930694603379951116124231508368216633538211694365432992843945117364855552227425847969222174150554445927107277490921726589952422680399498405829042499989471077961160390852504507444396304245466619357912782732849263541576574897032162507091438249047437903466515492636729098849597776861086645414648156742137903305924303569876925763649131132338998435080873779885270635534972559333873899984350999651668537519741529759045469820981319956997708300852011695797195024896360913815239348544750945633098208528007604144334968747512233076207320670117170856416856076921378644498763435888517559764144336885783536320169278290978374072126308683665615385707808627819319787636661121210260431962047274635492116483853446000012158513988672628961208867737881413388764282090221995748442077854614434138330065731247894927775399256779773155335439597327748630356413453880760515330024593727373329769027334434466505465180896207494120188818633725660365163171008394951444200112962375355812028206967699825160186784761235992991343164102466149050370964389341563147190845303104575200125046566202348915896682915576069899241180877433870405992621964606545735850823448629101104346350397209442114512167631137656787475537698575629079576790285311554909984533951907638902773395269594050722430709542870606681182471630965595949997149753389861040785554924959921152960444078154790228660045950675792257288294822704156042699658903487055992286021461401429767279389049138098559808648652533806553237080391030905066134861282522577988574034744394368166875485133668583175680751876303725836024714548031542093040224257782832916183359495729758552429518764490577642409706867882720995674898198507314473447852764896452986088691703643574524345483243840747540221246477862528296587462973708514236277453924524588188692759749969341643985418224089887186774271897686657692368654986184216572780867177715401349002047296815359067134777552892766976080963447537588374305898854500176798541386389281389143417779636045595274554240014246253858898686865801125419188853727023477746672996747337232222055049927221691224470747728998833555831526111723597293454624750271998598022445280979811610992658228025762248087157805195155474805726148575181648923252907596434360340316328153148101514761978427228387352753540861750232234347652962881987625605868377479271986847975557541755337331346720259017144959904593304209383987204796164938385228063582277281050607155478323725818645030481601125023308076259557022974629816600784976509396581261658710416740201916565195678591552724427173588886036025646867166386180555322489644428350536649615044067696131583754713444733918721365089413501524391596691753396002436210787074156085103728817059991689977504221899068759735353464157670024684585697889234342293218926361836746555284833733474462272172640635345396874596359653411528614761938152584985119355710494581579569025630729162264006355027887645917651145934952128548046392874904814096874657082496381289161145177282410936035882903394538729424196793046234395627738202288223575937352946870922439981303983577248229251282730409552867886529425167768045204210268615037831678805150650269776580217897855993443220403304120580138561683262729717544034102551332961368879211885835362377582803139313555435797754330512374054006062621953580696429518912291776544089728800596595421455568125236271321706201866699060585725278455590506806626703884063680299708756146548195337833669490343998360460696945979479565757398721232537856638611675220194702673339841679373203321803554139227585142384795696522349934205220300325287754630471228038924331730342794051423136274853613165070223876265498549889881288226213641694962623427209916956797494381145913360291655143170786805848644367510527689825697396632258575342368795676868386922311398513236155883532996186338490687263866723303198682435631505316816100451885791462918363769770155755122771549012277390723372487879491519640437294027829887033118768202435511701506667509694157198843391743060423876904834819550279271575403150454365714802755393000266351972268007006005671751415876922165945883158018426558159404230018822400135364974120899067195998500301024405800087726109420087374488902917272294810760615902726864531116063197221968567241149162195675379145668032526920841656650505729175411448052419217037538863968247159868273307874619264573971261182063451080721265233911960906449375297066783743334332435104873207180327223169231700999284126930007080366474237348525464552005277997843178279898568956818082818277144229317380083533687818577028015312567496260799974525015198748878223731452684063233921904837942927972714421741539328211346219192280062841754526211586427775456380154778302511224916787628609610244727841619012882437538337819643435228742900825228309336511855635110659302790576721772358233519466582983783444677038232001131117746842026748619751047947769633808272643943172699637470327177672484075392824785310944985892613776965029754463273197673951449546707929466944266792571602393800500508936405865403602383451175042349761731474667056426926736067214126018730690924276156891923055828252061184248104241742442603776778667981309887484535016785443938552318172963092403101707587493145812005730514258523770945667065870808716379949913122630539349435878003788720102302262330606157829316264032686083333366561642893335908846638165531137141538418838624881579038321844291833790188629610837831937413904141761175762444120090543783331030619112249321279607394780306650562273153829199140086907075120211268797207326441440976792492933353007727280406766442763544395553920961366498117979552313095123976704440931732705966156646025441260918882849679599798142079685757951644191424732009366491742010979132069542099153023111033326588557397589025258063646438762490673114941269297411460331429618184128591115378251234958113399553163981623605181946771784288601871129586911665216231643360468380224816064216734071030987247076164374582071590232770758530770479315258266242396415195196290921653144924452148367470644384886837837733680375189130186167842103771400303374763549883033163227666717971178791675349906032888116319596098470715971320882159674059093154040525573120206923035127197745769807575905178889769109056938989362880105865758652508265405481407430906966688746643729

noncomputable def bx0 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936)

theorem wk0 : SixW15S2K.walk table bits 64 0 bx0 = some 791 := by decide +kernel

noncomputable def bx1 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 401408)

theorem wk1 : SixW15S2K.walk table bits 64 791 bx1 = some 2667 := by decide +kernel

noncomputable def bx2 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936)

theorem wk2 : SixW15S2K.walk table bits 64 2667 bx2 = some 3883 := by decide +kernel

noncomputable def bx3 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 401408)

theorem wk3 : SixW15S2K.walk table bits 64 3883 bx3 = some 5244 := by decide +kernel

noncomputable def bx4 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936)

theorem wk4 : SixW15S2K.walk table bits 64 5244 bx4 = some 5780 := by decide +kernel

noncomputable def bx5 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 401408)

theorem wk5 : SixW15S2K.walk table bits 64 5780 bx5 = some 6116 := by decide +kernel

noncomputable def bx6 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936)

theorem wk6 : SixW15S2K.walk table bits 64 6116 bx6 = some 7557 := by decide +kernel

noncomputable def bx7 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 401408)

theorem wk7 : SixW15S2K.walk table bits 64 7557 bx7 = some 9038 := by decide +kernel

noncomputable def bx8 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936)

theorem wk8 : SixW15S2K.walk table bits 64 9038 bx8 = some 9604 := by decide +kernel

noncomputable def bx9 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 401408)

theorem wk9 : SixW15S2K.walk table bits 64 9604 bx9 = some 9870 := by decide +kernel

noncomputable def bx10 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936)

theorem wk10 : SixW15S2K.walk table bits 64 9870 bx10 = some 9951 := by decide +kernel

noncomputable def bx11 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 401408)

theorem wk11 : SixW15S2K.walk table bits 64 9951 bx11 = some 9952 := by decide +kernel

noncomputable def bx12 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936)

theorem wk12 : SixW15S2K.walk table bits 64 9952 bx12 = some 10338 := by decide +kernel

noncomputable def bx13 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 401408)

theorem wk13 : SixW15S2K.walk table bits 64 10338 bx13 = some 10534 := by decide +kernel

noncomputable def bx14 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936)

theorem wk14 : SixW15S2K.walk table bits 64 10534 bx14 = some 10580 := by decide +kernel

noncomputable def bx15 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 401408)

theorem wk15 : SixW15S2K.walk table bits 64 10580 bx15 = some 10581 := by decide +kernel

noncomputable def bx16 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936)

theorem wk16 : SixW15S2K.walk table bits 64 10581 bx16 = some 10582 := by decide +kernel

noncomputable def bx17 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 401408)

theorem wk17 : SixW15S2K.walk table bits 64 10582 bx17 = some 10583 := by decide +kernel

noncomputable def bx18 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936)

theorem wk18 : SixW15S2K.walk table bits 64 10583 bx18 = some 11774 := by decide +kernel

noncomputable def bx19 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 401408)

theorem wk19 : SixW15S2K.walk table bits 64 11774 bx19 = some 13720 := by decide +kernel

noncomputable def bx20 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936)

theorem wk20 : SixW15S2K.walk table bits 64 13720 bx20 = some 14986 := by decide +kernel

noncomputable def bx21 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 401408)

theorem wk21 : SixW15S2K.walk table bits 64 14986 bx21 = some 15407 := by decide +kernel

noncomputable def bx22 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936)

theorem wk22 : SixW15S2K.walk table bits 64 15407 bx22 = some 15528 := by decide +kernel

noncomputable def bx23 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 401408)

theorem wk23 : SixW15S2K.walk table bits 64 15528 bx23 = some 15574 := by decide +kernel

noncomputable def bx24 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936)

theorem wk24 : SixW15S2K.walk table bits 64 15574 bx24 = some 16100 := by decide +kernel

noncomputable def bx25 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 401408)

theorem wk25 : SixW15S2K.walk table bits 64 16100 bx25 = some 16421 := by decide +kernel

noncomputable def bx26 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936)

theorem wk26 : SixW15S2K.walk table bits 64 16421 bx26 = some 16482 := by decide +kernel

noncomputable def bx27 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 401408)

theorem wk27 : SixW15S2K.walk table bits 64 16482 bx27 = some 16483 := by decide +kernel

noncomputable def bx28 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936)

theorem wk28 : SixW15S2K.walk table bits 64 16483 bx28 = some 16484 := by decide +kernel

noncomputable def bx29 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 401408)

theorem wk29 : SixW15S2K.walk table bits 64 16484 bx29 = some 16485 := by decide +kernel

noncomputable def bx30 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936)

theorem wk30 : SixW15S2K.walk table bits 64 16485 bx30 = some 16531 := by decide +kernel

noncomputable def bx31 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 401408)

theorem wk31 : SixW15S2K.walk table bits 64 16531 bx31 = some 16532 := by decide +kernel

noncomputable def bx32 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936)

theorem wk32 : SixW15S2K.walk table bits 64 16532 bx32 = some 16533 := by decide +kernel

noncomputable def bx33 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 401408)

theorem wk33 : SixW15S2K.walk table bits 64 16533 bx33 = some 16534 := by decide +kernel

noncomputable def bx34 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936)

theorem wk34 : SixW15S2K.walk table bits 64 16534 bx34 = some 16535 := by decide +kernel

noncomputable def bx35 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 401408)

theorem wk35 : SixW15S2K.walk table bits 64 16535 bx35 = some 16536 := by decide +kernel

noncomputable def bx36 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936)

theorem wk36 : SixW15S2K.walk table bits 64 16536 bx36 = some 17062 := by decide +kernel

noncomputable def bx37 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 401408)

theorem wk37 : SixW15S2K.walk table bits 64 17062 bx37 = some 17408 := by decide +kernel

noncomputable def bx38 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936)

theorem wk38 : SixW15S2K.walk table bits 64 17408 bx38 = some 17529 := by decide +kernel

noncomputable def bx39 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 401408)

theorem wk39 : SixW15S2K.walk table bits 64 17529 bx39 = some 17575 := by decide +kernel

noncomputable def bx40 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936)

theorem wk40 : SixW15S2K.walk table bits 64 17575 bx40 = some 17576 := by decide +kernel

noncomputable def bx41 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 401408)

theorem wk41 : SixW15S2K.walk table bits 64 17576 bx41 = some 17577 := by decide +kernel

noncomputable def bx42 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936)

theorem wk42 : SixW15S2K.walk table bits 64 17577 bx42 = some 17658 := by decide +kernel

noncomputable def bx43 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 401408)

theorem wk43 : SixW15S2K.walk table bits 64 17658 bx43 = some 17659 := by decide +kernel

noncomputable def bx44 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936)

theorem wk44 : SixW15S2K.walk table bits 64 17659 bx44 = some 17660 := by decide +kernel

noncomputable def bx45 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 401408)

theorem wk45 : SixW15S2K.walk table bits 64 17660 bx45 = some 17661 := by decide +kernel

noncomputable def bx46 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936)

theorem wk46 : SixW15S2K.walk table bits 64 17661 bx46 = some 17662 := by decide +kernel

noncomputable def bx47 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 401408)

theorem wk47 : SixW15S2K.walk table bits 64 17662 bx47 = some 17663 := by decide +kernel

noncomputable def bx48 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936)

theorem wk48 : SixW15S2K.walk table bits 64 17663 bx48 = some 17664 := by decide +kernel

noncomputable def bx49 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 401408)

theorem wk49 : SixW15S2K.walk table bits 64 17664 bx49 = some 17665 := by decide +kernel

noncomputable def bx50 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936)

theorem wk50 : SixW15S2K.walk table bits 64 17665 bx50 = some 17666 := by decide +kernel

noncomputable def bx51 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 401408)

theorem wk51 : SixW15S2K.walk table bits 64 17666 bx51 = some 17667 := by decide +kernel

noncomputable def bx52 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936)

theorem wk52 : SixW15S2K.walk table bits 64 17667 bx52 = some 17668 := by decide +kernel

noncomputable def bx53 : SixW15S2K.Box := (SixW15S2K.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 401408)

theorem wk53 : SixW15S2K.walk table bits 64 17668 bx53 = some 17669 := by decide +kernel

noncomputable def bx54 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936)

theorem wk54 : SixW15S2K.walk table bits 64 17669 bx54 = some 17670 := by decide +kernel

noncomputable def bx55 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 401408)

theorem wk55 : SixW15S2K.walk table bits 64 17670 bx55 = some 19601 := by decide +kernel

noncomputable def bx56 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936)

theorem wk56 : SixW15S2K.walk table bits 64 19601 bx56 = some 19602 := by decide +kernel

noncomputable def bx57 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 401408)

theorem wk57 : SixW15S2K.walk table bits 64 19602 bx57 = some 20473 := by decide +kernel

noncomputable def bx58 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936)

theorem wk58 : SixW15S2K.walk table bits 64 20473 bx58 = some 20474 := by decide +kernel

noncomputable def bx59 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 401408)

theorem wk59 : SixW15S2K.walk table bits 64 20474 bx59 = some 20570 := by decide +kernel

noncomputable def bx60 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936)

theorem wk60 : SixW15S2K.walk table bits 64 20570 bx60 = some 20571 := by decide +kernel

noncomputable def bx61 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 401408)

theorem wk61 : SixW15S2K.walk table bits 64 20571 bx61 = some 21497 := by decide +kernel

noncomputable def bx62 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936)

theorem wk62 : SixW15S2K.walk table bits 64 21497 bx62 = some 21498 := by decide +kernel

noncomputable def bx63 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 401408)

theorem wk63 : SixW15S2K.walk table bits 64 21498 bx63 = some 21574 := by decide +kernel

noncomputable def bx64 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936)

theorem wk64 : SixW15S2K.walk table bits 64 21574 bx64 = some 21575 := by decide +kernel

noncomputable def bx65 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 401408)

theorem wk65 : SixW15S2K.walk table bits 64 21575 bx65 = some 21576 := by decide +kernel

noncomputable def bx66 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936)

theorem wk66 : SixW15S2K.walk table bits 64 21576 bx66 = some 21577 := by decide +kernel

noncomputable def bx67 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 401408)

theorem wk67 : SixW15S2K.walk table bits 64 21577 bx67 = some 21658 := by decide +kernel

noncomputable def bx68 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936)

theorem wk68 : SixW15S2K.walk table bits 64 21658 bx68 = some 21659 := by decide +kernel

noncomputable def bx69 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 401408)

theorem wk69 : SixW15S2K.walk table bits 64 21659 bx69 = some 21660 := by decide +kernel

noncomputable def bx70 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936)

theorem wk70 : SixW15S2K.walk table bits 64 21660 bx70 = some 21661 := by decide +kernel

noncomputable def bx71 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 401408)

theorem wk71 : SixW15S2K.walk table bits 64 21661 bx71 = some 21662 := by decide +kernel

noncomputable def bx72 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936)

theorem wk72 : SixW15S2K.walk table bits 64 21662 bx72 = some 21663 := by decide +kernel

noncomputable def bx73 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 401408)

theorem wk73 : SixW15S2K.walk table bits 64 21663 bx73 = some 22519 := by decide +kernel

noncomputable def bx74 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936)

theorem wk74 : SixW15S2K.walk table bits 64 22519 bx74 = some 22520 := by decide +kernel

noncomputable def bx75 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 401408)

theorem wk75 : SixW15S2K.walk table bits 64 22520 bx75 = some 22606 := by decide +kernel

noncomputable def bx76 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936)

theorem wk76 : SixW15S2K.walk table bits 64 22606 bx76 = some 22607 := by decide +kernel

noncomputable def bx77 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 401408)

theorem wk77 : SixW15S2K.walk table bits 64 22607 bx77 = some 22608 := by decide +kernel

noncomputable def bx78 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936)

theorem wk78 : SixW15S2K.walk table bits 64 22608 bx78 = some 22609 := by decide +kernel

noncomputable def bx79 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 401408)

theorem wk79 : SixW15S2K.walk table bits 64 22609 bx79 = some 22685 := by decide +kernel

noncomputable def bx80 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936)

theorem wk80 : SixW15S2K.walk table bits 64 22685 bx80 = some 22686 := by decide +kernel

noncomputable def bx81 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 401408)

theorem wk81 : SixW15S2K.walk table bits 64 22686 bx81 = some 22687 := by decide +kernel

noncomputable def bx82 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936)

theorem wk82 : SixW15S2K.walk table bits 64 22687 bx82 = some 22688 := by decide +kernel

noncomputable def bx83 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 401408)

theorem wk83 : SixW15S2K.walk table bits 64 22688 bx83 = some 22689 := by decide +kernel

noncomputable def bx84 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936)

theorem wk84 : SixW15S2K.walk table bits 64 22689 bx84 = some 22690 := by decide +kernel

noncomputable def bx85 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 401408)

theorem wk85 : SixW15S2K.walk table bits 64 22690 bx85 = some 22691 := by decide +kernel

noncomputable def bx86 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936)

theorem wk86 : SixW15S2K.walk table bits 64 22691 bx86 = some 22692 := by decide +kernel

noncomputable def bx87 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 401408)

theorem wk87 : SixW15S2K.walk table bits 64 22692 bx87 = some 22693 := by decide +kernel

noncomputable def bx88 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936)

theorem wk88 : SixW15S2K.walk table bits 64 22693 bx88 = some 22694 := by decide +kernel

noncomputable def bx89 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 401408)

theorem wk89 : SixW15S2K.walk table bits 64 22694 bx89 = some 22695 := by decide +kernel

noncomputable def bx90 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936)

theorem wk90 : SixW15S2K.walk table bits 64 22695 bx90 = some 22696 := by decide +kernel

noncomputable def bx91 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 401408)

theorem wk91 : SixW15S2K.walk table bits 64 22696 bx91 = some 22792 := by decide +kernel

noncomputable def bx92 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936)

theorem wk92 : SixW15S2K.walk table bits 64 22792 bx92 = some 22793 := by decide +kernel

noncomputable def bx93 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 401408)

theorem wk93 : SixW15S2K.walk table bits 64 22793 bx93 = some 22794 := by decide +kernel

noncomputable def bx94 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936)

theorem wk94 : SixW15S2K.walk table bits 64 22794 bx94 = some 22795 := by decide +kernel

noncomputable def bx95 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 401408)

theorem wk95 : SixW15S2K.walk table bits 64 22795 bx95 = some 22796 := by decide +kernel

noncomputable def bx96 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936)

theorem wk96 : SixW15S2K.walk table bits 64 22796 bx96 = some 22797 := by decide +kernel

noncomputable def bx97 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 401408)

theorem wk97 : SixW15S2K.walk table bits 64 22797 bx97 = some 22798 := by decide +kernel

noncomputable def bx98 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936)

theorem wk98 : SixW15S2K.walk table bits 64 22798 bx98 = some 22799 := by decide +kernel

noncomputable def bx99 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 401408)

theorem wk99 : SixW15S2K.walk table bits 64 22799 bx99 = some 22800 := by decide +kernel

noncomputable def bx100 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936)

theorem wk100 : SixW15S2K.walk table bits 64 22800 bx100 = some 22801 := by decide +kernel

noncomputable def bx101 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 401408)

theorem wk101 : SixW15S2K.walk table bits 64 22801 bx101 = some 22802 := by decide +kernel

noncomputable def bx102 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936)

theorem wk102 : SixW15S2K.walk table bits 64 22802 bx102 = some 22803 := by decide +kernel

noncomputable def bx103 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 401408)

theorem wk103 : SixW15S2K.walk table bits 64 22803 bx103 = some 22804 := by decide +kernel

noncomputable def bx104 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936)

theorem wk104 : SixW15S2K.walk table bits 64 22804 bx104 = some 22805 := by decide +kernel

noncomputable def bx105 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 401408)

theorem wk105 : SixW15S2K.walk table bits 64 22805 bx105 = some 22806 := by decide +kernel

noncomputable def bx106 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936)

theorem wk106 : SixW15S2K.walk table bits 64 22806 bx106 = some 22807 := by decide +kernel

noncomputable def bx107 : SixW15S2K.Box := (SixW15S2K.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 401408)

theorem wk107 : SixW15S2K.walk table bits 64 22807 bx107 = some 22808 := by decide +kernel

theorem nb0_eq : (SixW15S2K.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW15S2K.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW15S2K.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW15S2K.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW15S2K.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW15S2K.walk table bits 64 0 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 0 0) = some 791 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 0 0 = bx0 from by decide +kernel]; exact wk0

theorem root_00001 : SixW15S2K.walk table bits 64 791 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 0 1) = some 2667 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 0 1 = bx1 from by decide +kernel]; exact wk1

theorem root_00010 : SixW15S2K.walk table bits 64 2667 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 1 0) = some 3883 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 1 0 = bx2 from by decide +kernel]; exact wk2

theorem root_00011 : SixW15S2K.walk table bits 64 3883 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 1 1) = some 5244 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 1 1 = bx3 from by decide +kernel]; exact wk3

theorem root_00020 : SixW15S2K.walk table bits 64 5244 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 2 0) = some 5780 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 2 0 = bx4 from by decide +kernel]; exact wk4

theorem root_00021 : SixW15S2K.walk table bits 64 5780 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 2 1) = some 6116 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 0 2 1 = bx5 from by decide +kernel]; exact wk5

theorem root_00100 : SixW15S2K.walk table bits 64 6116 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 0 0) = some 7557 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 0 0 = bx6 from by decide +kernel]; exact wk6

theorem root_00101 : SixW15S2K.walk table bits 64 7557 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 0 1) = some 9038 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 0 1 = bx7 from by decide +kernel]; exact wk7

theorem root_00110 : SixW15S2K.walk table bits 64 9038 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 1 0) = some 9604 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 1 0 = bx8 from by decide +kernel]; exact wk8

theorem root_00111 : SixW15S2K.walk table bits 64 9604 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 1 1) = some 9870 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 1 1 = bx9 from by decide +kernel]; exact wk9

theorem root_00120 : SixW15S2K.walk table bits 64 9870 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 2 0) = some 9951 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 2 0 = bx10 from by decide +kernel]; exact wk10

theorem root_00121 : SixW15S2K.walk table bits 64 9951 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 2 1) = some 9952 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 1 2 1 = bx11 from by decide +kernel]; exact wk11

theorem root_00200 : SixW15S2K.walk table bits 64 9952 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 0 0) = some 10338 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 0 0 = bx12 from by decide +kernel]; exact wk12

theorem root_00201 : SixW15S2K.walk table bits 64 10338 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 0 1) = some 10534 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 0 1 = bx13 from by decide +kernel]; exact wk13

theorem root_00210 : SixW15S2K.walk table bits 64 10534 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 1 0) = some 10580 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 1 0 = bx14 from by decide +kernel]; exact wk14

theorem root_00211 : SixW15S2K.walk table bits 64 10580 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 1 1) = some 10581 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 1 1 = bx15 from by decide +kernel]; exact wk15

theorem root_00220 : SixW15S2K.walk table bits 64 10581 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 2 0) = some 10582 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 2 0 = bx16 from by decide +kernel]; exact wk16

theorem root_00221 : SixW15S2K.walk table bits 64 10582 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 2 1) = some 10583 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 0 2 2 1 = bx17 from by decide +kernel]; exact wk17

theorem root_01000 : SixW15S2K.walk table bits 64 10583 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 0 0) = some 11774 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 0 0 = bx18 from by decide +kernel]; exact wk18

theorem root_01001 : SixW15S2K.walk table bits 64 11774 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 0 1) = some 13720 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 0 1 = bx19 from by decide +kernel]; exact wk19

theorem root_01010 : SixW15S2K.walk table bits 64 13720 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 1 0) = some 14986 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 1 0 = bx20 from by decide +kernel]; exact wk20

theorem root_01011 : SixW15S2K.walk table bits 64 14986 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 1 1) = some 15407 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 1 1 = bx21 from by decide +kernel]; exact wk21

theorem root_01020 : SixW15S2K.walk table bits 64 15407 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 2 0) = some 15528 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 2 0 = bx22 from by decide +kernel]; exact wk22

theorem root_01021 : SixW15S2K.walk table bits 64 15528 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 2 1) = some 15574 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 0 2 1 = bx23 from by decide +kernel]; exact wk23

theorem root_01100 : SixW15S2K.walk table bits 64 15574 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 0 0) = some 16100 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 0 0 = bx24 from by decide +kernel]; exact wk24

theorem root_01101 : SixW15S2K.walk table bits 64 16100 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 0 1) = some 16421 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 0 1 = bx25 from by decide +kernel]; exact wk25

theorem root_01110 : SixW15S2K.walk table bits 64 16421 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 1 0) = some 16482 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 1 0 = bx26 from by decide +kernel]; exact wk26

theorem root_01111 : SixW15S2K.walk table bits 64 16482 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 1 1) = some 16483 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 1 1 = bx27 from by decide +kernel]; exact wk27

theorem root_01120 : SixW15S2K.walk table bits 64 16483 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 2 0) = some 16484 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 2 0 = bx28 from by decide +kernel]; exact wk28

theorem root_01121 : SixW15S2K.walk table bits 64 16484 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 2 1) = some 16485 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 1 2 1 = bx29 from by decide +kernel]; exact wk29

theorem root_01200 : SixW15S2K.walk table bits 64 16485 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 0 0) = some 16531 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 0 0 = bx30 from by decide +kernel]; exact wk30

theorem root_01201 : SixW15S2K.walk table bits 64 16531 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 0 1) = some 16532 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 0 1 = bx31 from by decide +kernel]; exact wk31

theorem root_01210 : SixW15S2K.walk table bits 64 16532 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 1 0) = some 16533 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 1 0 = bx32 from by decide +kernel]; exact wk32

theorem root_01211 : SixW15S2K.walk table bits 64 16533 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 1 1) = some 16534 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 1 1 = bx33 from by decide +kernel]; exact wk33

theorem root_01220 : SixW15S2K.walk table bits 64 16534 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 2 0) = some 16535 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 2 0 = bx34 from by decide +kernel]; exact wk34

theorem root_01221 : SixW15S2K.walk table bits 64 16535 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 2 1) = some 16536 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 1 2 2 1 = bx35 from by decide +kernel]; exact wk35

theorem root_02000 : SixW15S2K.walk table bits 64 16536 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 0 0) = some 17062 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 0 0 = bx36 from by decide +kernel]; exact wk36

theorem root_02001 : SixW15S2K.walk table bits 64 17062 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 0 1) = some 17408 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 0 1 = bx37 from by decide +kernel]; exact wk37

theorem root_02010 : SixW15S2K.walk table bits 64 17408 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 1 0) = some 17529 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 1 0 = bx38 from by decide +kernel]; exact wk38

theorem root_02011 : SixW15S2K.walk table bits 64 17529 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 1 1) = some 17575 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 1 1 = bx39 from by decide +kernel]; exact wk39

theorem root_02020 : SixW15S2K.walk table bits 64 17575 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 2 0) = some 17576 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 2 0 = bx40 from by decide +kernel]; exact wk40

theorem root_02021 : SixW15S2K.walk table bits 64 17576 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 2 1) = some 17577 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 0 2 1 = bx41 from by decide +kernel]; exact wk41

theorem root_02100 : SixW15S2K.walk table bits 64 17577 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 0 0) = some 17658 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 0 0 = bx42 from by decide +kernel]; exact wk42

theorem root_02101 : SixW15S2K.walk table bits 64 17658 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 0 1) = some 17659 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 0 1 = bx43 from by decide +kernel]; exact wk43

theorem root_02110 : SixW15S2K.walk table bits 64 17659 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 1 0) = some 17660 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 1 0 = bx44 from by decide +kernel]; exact wk44

theorem root_02111 : SixW15S2K.walk table bits 64 17660 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 1 1) = some 17661 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 1 1 = bx45 from by decide +kernel]; exact wk45

theorem root_02120 : SixW15S2K.walk table bits 64 17661 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 2 0) = some 17662 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 2 0 = bx46 from by decide +kernel]; exact wk46

theorem root_02121 : SixW15S2K.walk table bits 64 17662 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 2 1) = some 17663 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 1 2 1 = bx47 from by decide +kernel]; exact wk47

theorem root_02200 : SixW15S2K.walk table bits 64 17663 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 0 0) = some 17664 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 0 0 = bx48 from by decide +kernel]; exact wk48

theorem root_02201 : SixW15S2K.walk table bits 64 17664 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 0 1) = some 17665 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 0 1 = bx49 from by decide +kernel]; exact wk49

theorem root_02210 : SixW15S2K.walk table bits 64 17665 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 1 0) = some 17666 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 1 0 = bx50 from by decide +kernel]; exact wk50

theorem root_02211 : SixW15S2K.walk table bits 64 17666 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 1 1) = some 17667 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 1 1 = bx51 from by decide +kernel]; exact wk51

theorem root_02220 : SixW15S2K.walk table bits 64 17667 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 2 0) = some 17668 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 2 0 = bx52 from by decide +kernel]; exact wk52

theorem root_02221 : SixW15S2K.walk table bits 64 17668 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 2 1) = some 17669 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 0 2 2 2 1 = bx53 from by decide +kernel]; exact wk53

theorem root_10000 : SixW15S2K.walk table bits 64 17669 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 0 0) = some 17670 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 0 0 = bx54 from by decide +kernel]; exact wk54

theorem root_10001 : SixW15S2K.walk table bits 64 17670 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 0 1) = some 19601 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 0 1 = bx55 from by decide +kernel]; exact wk55

theorem root_10010 : SixW15S2K.walk table bits 64 19601 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 1 0) = some 19602 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 1 0 = bx56 from by decide +kernel]; exact wk56

theorem root_10011 : SixW15S2K.walk table bits 64 19602 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 1 1) = some 20473 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 1 1 = bx57 from by decide +kernel]; exact wk57

theorem root_10020 : SixW15S2K.walk table bits 64 20473 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 2 0) = some 20474 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 2 0 = bx58 from by decide +kernel]; exact wk58

theorem root_10021 : SixW15S2K.walk table bits 64 20474 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 2 1) = some 20570 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 0 2 1 = bx59 from by decide +kernel]; exact wk59

theorem root_10100 : SixW15S2K.walk table bits 64 20570 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 0 0) = some 20571 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 0 0 = bx60 from by decide +kernel]; exact wk60

theorem root_10101 : SixW15S2K.walk table bits 64 20571 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 0 1) = some 21497 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 0 1 = bx61 from by decide +kernel]; exact wk61

theorem root_10110 : SixW15S2K.walk table bits 64 21497 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 1 0) = some 21498 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 1 0 = bx62 from by decide +kernel]; exact wk62

theorem root_10111 : SixW15S2K.walk table bits 64 21498 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 1 1) = some 21574 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 1 1 = bx63 from by decide +kernel]; exact wk63

theorem root_10120 : SixW15S2K.walk table bits 64 21574 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 2 0) = some 21575 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 2 0 = bx64 from by decide +kernel]; exact wk64

theorem root_10121 : SixW15S2K.walk table bits 64 21575 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 2 1) = some 21576 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 1 2 1 = bx65 from by decide +kernel]; exact wk65

theorem root_10200 : SixW15S2K.walk table bits 64 21576 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 0 0) = some 21577 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 0 0 = bx66 from by decide +kernel]; exact wk66

theorem root_10201 : SixW15S2K.walk table bits 64 21577 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 0 1) = some 21658 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 0 1 = bx67 from by decide +kernel]; exact wk67

theorem root_10210 : SixW15S2K.walk table bits 64 21658 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 1 0) = some 21659 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 1 0 = bx68 from by decide +kernel]; exact wk68

theorem root_10211 : SixW15S2K.walk table bits 64 21659 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 1 1) = some 21660 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 1 1 = bx69 from by decide +kernel]; exact wk69

theorem root_10220 : SixW15S2K.walk table bits 64 21660 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 2 0) = some 21661 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 2 0 = bx70 from by decide +kernel]; exact wk70

theorem root_10221 : SixW15S2K.walk table bits 64 21661 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 2 1) = some 21662 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 0 2 2 1 = bx71 from by decide +kernel]; exact wk71

theorem root_11000 : SixW15S2K.walk table bits 64 21662 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 0 0) = some 21663 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 0 0 = bx72 from by decide +kernel]; exact wk72

theorem root_11001 : SixW15S2K.walk table bits 64 21663 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 0 1) = some 22519 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 0 1 = bx73 from by decide +kernel]; exact wk73

theorem root_11010 : SixW15S2K.walk table bits 64 22519 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 1 0) = some 22520 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 1 0 = bx74 from by decide +kernel]; exact wk74

theorem root_11011 : SixW15S2K.walk table bits 64 22520 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 1 1) = some 22606 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 1 1 = bx75 from by decide +kernel]; exact wk75

theorem root_11020 : SixW15S2K.walk table bits 64 22606 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 2 0) = some 22607 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 2 0 = bx76 from by decide +kernel]; exact wk76

theorem root_11021 : SixW15S2K.walk table bits 64 22607 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 2 1) = some 22608 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 0 2 1 = bx77 from by decide +kernel]; exact wk77

theorem root_11100 : SixW15S2K.walk table bits 64 22608 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 0 0) = some 22609 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 0 0 = bx78 from by decide +kernel]; exact wk78

theorem root_11101 : SixW15S2K.walk table bits 64 22609 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 0 1) = some 22685 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 0 1 = bx79 from by decide +kernel]; exact wk79

theorem root_11110 : SixW15S2K.walk table bits 64 22685 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 1 0) = some 22686 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 1 0 = bx80 from by decide +kernel]; exact wk80

theorem root_11111 : SixW15S2K.walk table bits 64 22686 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 1 1) = some 22687 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 1 1 = bx81 from by decide +kernel]; exact wk81

theorem root_11120 : SixW15S2K.walk table bits 64 22687 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 2 0) = some 22688 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 2 0 = bx82 from by decide +kernel]; exact wk82

theorem root_11121 : SixW15S2K.walk table bits 64 22688 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 2 1) = some 22689 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 1 2 1 = bx83 from by decide +kernel]; exact wk83

theorem root_11200 : SixW15S2K.walk table bits 64 22689 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 0 0) = some 22690 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 0 0 = bx84 from by decide +kernel]; exact wk84

theorem root_11201 : SixW15S2K.walk table bits 64 22690 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 0 1) = some 22691 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 0 1 = bx85 from by decide +kernel]; exact wk85

theorem root_11210 : SixW15S2K.walk table bits 64 22691 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 1 0) = some 22692 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 1 0 = bx86 from by decide +kernel]; exact wk86

theorem root_11211 : SixW15S2K.walk table bits 64 22692 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 1 1) = some 22693 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 1 1 = bx87 from by decide +kernel]; exact wk87

theorem root_11220 : SixW15S2K.walk table bits 64 22693 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 2 0) = some 22694 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 2 0 = bx88 from by decide +kernel]; exact wk88

theorem root_11221 : SixW15S2K.walk table bits 64 22694 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 2 1) = some 22695 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 1 2 2 1 = bx89 from by decide +kernel]; exact wk89

theorem root_12000 : SixW15S2K.walk table bits 64 22695 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 0 0) = some 22696 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 0 0 = bx90 from by decide +kernel]; exact wk90

theorem root_12001 : SixW15S2K.walk table bits 64 22696 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 0 1) = some 22792 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 0 1 = bx91 from by decide +kernel]; exact wk91

theorem root_12010 : SixW15S2K.walk table bits 64 22792 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 1 0) = some 22793 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 1 0 = bx92 from by decide +kernel]; exact wk92

theorem root_12011 : SixW15S2K.walk table bits 64 22793 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 1 1) = some 22794 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 1 1 = bx93 from by decide +kernel]; exact wk93

theorem root_12020 : SixW15S2K.walk table bits 64 22794 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 2 0) = some 22795 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 2 0 = bx94 from by decide +kernel]; exact wk94

theorem root_12021 : SixW15S2K.walk table bits 64 22795 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 2 1) = some 22796 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 0 2 1 = bx95 from by decide +kernel]; exact wk95

theorem root_12100 : SixW15S2K.walk table bits 64 22796 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 0 0) = some 22797 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 0 0 = bx96 from by decide +kernel]; exact wk96

theorem root_12101 : SixW15S2K.walk table bits 64 22797 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 0 1) = some 22798 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 0 1 = bx97 from by decide +kernel]; exact wk97

theorem root_12110 : SixW15S2K.walk table bits 64 22798 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 1 0) = some 22799 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 1 0 = bx98 from by decide +kernel]; exact wk98

theorem root_12111 : SixW15S2K.walk table bits 64 22799 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 1 1) = some 22800 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 1 1 = bx99 from by decide +kernel]; exact wk99

theorem root_12120 : SixW15S2K.walk table bits 64 22800 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 2 0) = some 22801 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 2 0 = bx100 from by decide +kernel]; exact wk100

theorem root_12121 : SixW15S2K.walk table bits 64 22801 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 2 1) = some 22802 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 1 2 1 = bx101 from by decide +kernel]; exact wk101

theorem root_12200 : SixW15S2K.walk table bits 64 22802 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 0 0) = some 22803 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 0 0 = bx102 from by decide +kernel]; exact wk102

theorem root_12201 : SixW15S2K.walk table bits 64 22803 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 0 1) = some 22804 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 0 1 = bx103 from by decide +kernel]; exact wk103

theorem root_12210 : SixW15S2K.walk table bits 64 22804 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 1 0) = some 22805 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 1 0 = bx104 from by decide +kernel]; exact wk104

theorem root_12211 : SixW15S2K.walk table bits 64 22805 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 1 1) = some 22806 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 1 1 = bx105 from by decide +kernel]; exact wk105

theorem root_12220 : SixW15S2K.walk table bits 64 22806 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 2 0) = some 22807 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 2 0 = bx106 from by decide +kernel]; exact wk106

theorem root_12221 : SixW15S2K.walk table bits 64 22807 (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 2 1) = some 22808 := by
  rw [show SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) 1 2 2 2 1 = bx107 from by decide +kernel]; exact wk107

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW15S2K.badOf cover0).length → i1 < (SixW15S2K.badOf cover1).length → i2 < (SixW15S2K.badOf cover2).length → i3 < (SixW15S2K.badOf cover3).length → i4 < (SixW15S2K.badOf cover4).length →
    ∃ pos pos', SixW15S2K.walk table bits 64 pos (SixW15S2K.boxOf (SixW15S2K.badOf cover0) (SixW15S2K.badOf cover1) (SixW15S2K.badOf cover2) (SixW15S2K.badOf cover3) (SixW15S2K.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
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

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW15S2K.cN : ℝ) / SixW15S2K.SA ≤ SixW15S2K.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW15S2K.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 401408 237568 221184 237568 401408
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW15S2KData

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

/-! ###### the 6-point weighted bound from the checked certificate `SixW15S2K` ###### -/

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

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW15S2K.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW15S2K.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW15S2K.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW15S2K.SA]
  try ring

theorem G_rev (x0 x1 x2 x3 x4 : ℝ) : SixW15S2K.G x4 x3 x2 x1 x0 = SixW15S2K.G x0 x1 x2 x3 x4 := by
  unfold SixW15S2K.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (SixW15S2K.cN : ℝ) / SixW15S2K.SA ≤ SixW15S2K.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases SixW15S2KData.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases SixW15S2KData.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (304544 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW15S2K.cN, SixW15S2K.SA] at h
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
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

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
