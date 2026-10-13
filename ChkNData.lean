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

/-! ###### natural-number checker for the 4-point weighted certificate `FourN` ###### -/

section FourNDefs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (LN UN : ℕ) (k : ℕ) (side : Bool) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0, 0, true, 0⟩⟩

def SC : ℕ := 79228162514264337593543950336
def SW : ℕ := 10000000000000
def SC4 : ℕ := 19807040628566084398385987584

/-- the rational cell a natural-number cell denotes -/
def CellN.toQ (c : CellN) : Cell := ⟨(c.LN : ℚ) / SC, (c.UN : ℚ) / SC, c.k, c.side, (c.WN : ℚ) / SW⟩

inductive CTN
  | nil
  | node (l : CTN) (c : CellN) (r : CTN)

namespace CTN
def toList : CTN → List CellN
  | nil => []
  | node l c r => l.toList ++ c :: r.toList
def allOk : CTN → Bool
  | nil => true
  | node l c r => l.allOk && c.toQ.ok && r.allOk
def find : CTN → ℕ → ℕ → Option CellN
  | nil, _, _ => none
  | node l c r, a, b =>
      if a < c.LN then l.find a b
      else if c.LN < a then r.find a b
      else if b < c.UN then l.find a b
      else if c.UN < b then r.find a b
      else some c
end CTN

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 94) + 1) <<< 94
      if q < hi then (a, q) :: piecesN fuel q hi else [(a, hi)]

def lookupAllN (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      match t.find a b, lookupAllN t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainOKN : ℕ → ℕ → List CellN → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, c :: rest => decide (c.LN ≤ lo) && chainOKN c.UN hi rest

def chainWN : List CellN → ℕ
  | [] => 0
  | c :: rest => if rest.isEmpty then c.WN else min c.WN (chainWN rest)

def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := piecesN 64 lo hi

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.FourN

def SA : ℕ := 600000000
def cN : ℕ := 1386000

structure Box where
  (l0 u0 l1 u1 l2 u2 : ℕ)
  deriving DecidableEq

def Box.widthArg (b : Box) : ℕ :=
  if (b.u1 - b.l1) ≤ (b.u0 - b.l0) ∧ (b.u2 - b.l2) ≤ (b.u0 - b.l0) then 0
  else if (b.u2 - b.l2) ≤ (b.u1 - b.l1) then 1
  else 2
def Box.mid (b : Box) : ℕ → ℕ
  | 0 => (b.l0 + b.u0) / 2
  | 1 => (b.l1 + b.u1) / 2
  | _ => (b.l2 + b.u2) / 2
def Box.setHi (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with u0 := q }
  | 1 => { b with u1 := q }
  | _ => { b with u2 := q }
def Box.setLo (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with l0 := q }
  | 1 => { b with l1 := q }
  | _ => { b with l2 := q }

def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((240000 * b.l0 + 240000 * b.l1 + 240000 * b.l2) * SW + (400000000 * termWN tb (b.l0) (b.u0) + 600000000 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 1200000000 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 400000000 * termWN tb (b.l1) (b.u1) + 600000000 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 400000000 * termWN tb (b.l2) (b.u2)) * SC)

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk tb bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else if leafCheck tb b then some (pos + 1) else none

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

def boxOf (bd0 bd1 bd2 : List (ℕ × ℕ)) (i0 i1 i2 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint.FourN

end FourNDefs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the natural-number cell table (through the rational cell) -/

theorem SC_pos : (0:ℚ) < SC := by norm_num [SC]
theorem SW_pos : (0:ℚ) < SW := by norm_num [SW]

theorem CTN.find_sound : ∀ (t : CTN) (a b : ℕ) (c : CellN), t.find a b = some c →
    c ∈ t.toList ∧ c.LN = a ∧ c.UN = b := by
  intro t
  induction t with
  | nil => intro a b c h; simp [CTN.find] at h
  | node l c0 r ihl ihr =>
    intro a b c h
    simp only [CTN.find] at h
    split_ifs at h with h1 h2 h3 h4
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp [CTN.toList], le_antisymm (not_lt.mp h1) (not_lt.mp h2),
        le_antisymm (not_lt.mp h3) (not_lt.mp h4)⟩

theorem CTN.allOk_sound : ∀ (t : CTN), t.allOk = true → ∀ c ∈ t.toList, c.toQ.ok = true := by
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
theorem cellN_sound (c : CellN) (hok : c.toQ.ok = true) (x : ℝ)
    (h1 : (c.LN : ℝ) / SC ≤ x) (h2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  have := cell_sound c.toQ hok x (by simp only [CellN.toQ]; push_cast; exact h1)
    (by simp only [CellN.toQ]; push_cast; exact h2)
  simp only [CellN.toQ] at this; push_cast at this; exact this

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
    simp only [chainOKN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok := CTN.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.LN : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN]
    split_ifs with hempty
    · have hU : hi ≤ c.UN := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKN] using hrest
      exact cellN_sound c hcok e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rw [Nat.cast_min, ← min_div_div_right (by norm_num [SW] : (0:ℝ) ≤ SW)]
      rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact (min_le_left _ _).trans (cellN_sound c hcok e hL' hU)
      · exact (min_le_right _ _).trans
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)

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

namespace Zeta23Ext.Bridge.ThreePoint.FourN

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 : ℝ) : ℝ :=
  (240000 / (SA:ℝ)) * g0 + (240000 / (SA:ℝ)) * g1 + (240000 / (SA:ℝ)) * g2
    + (400000000 / (SA:ℝ)) * wfun (g0) + (600000000 / (SA:ℝ)) * wfun (g0 + g1) + (1200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g1) + (600000000 / (SA:ℝ)) * wfun (g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g2)

def Box.mem (b : Box) (g0 g1 g2 : ℝ) : Prop :=
  (b.l0 : ℝ) / SC ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / SC ∧ (b.l1 : ℝ) / SC ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / SC ∧ (b.l2 : ℝ) / SC ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / SC

theorem leaf_sound (tb : CTN) (hok : tb.allOk = true) (b : Box) (h : leafCheck tb b = true)
    (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2) : (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  have w0 := termWN_sound tb hok (b.l0) (b.u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := termWN_sound tb hok (b.l0 + b.l1) (b.u0 + b.u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := termWN_sound tb hok (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := termWN_sound tb hok (b.l1) (b.u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w4 := termWN_sound tb hok (b.l1 + b.l2) (b.u1 + b.u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w5 := termWN_sound tb hok (b.l2) (b.u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  simp only [leafCheck, Nat.ble_eq] at h
  have hq := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hpos : (0:ℝ) < SC * SW := by positivity
  set L : ℝ := 240000 * ((b.l0 : ℝ) / SC) + 240000 * ((b.l1 : ℝ) / SC) + 240000 * ((b.l2 : ℝ) / SC) with hL
  set Wt : ℝ := 400000000 * ((termWN tb (b.l0) (b.u0) : ℝ) / SW) + 600000000 * ((termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) / SW) + 1200000000 * ((termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) / SW) + 400000000 * ((termWN tb (b.l1) (b.u1) : ℝ) / SW) + 600000000 * ((termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) / SW) + 400000000 * ((termWN tb (b.l2) (b.u2) : ℝ) / SW) with hWt
  have e : (L + Wt) * (SC * SW) = (240000 * (b.l0 : ℝ) + 240000 * (b.l1 : ℝ) + 240000 * (b.l2 : ℝ)) * SW + (400000000 * (termWN tb (b.l0) (b.u0) : ℝ) + 600000000 * (termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) + 1200000000 * (termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) + 400000000 * (termWN tb (b.l1) (b.u1) : ℝ) + 600000000 * (termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) + 400000000 * (termWN tb (b.l2) (b.u2) : ℝ)) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((240000 / (SA:ℝ)) * g0 + (240000 / (SA:ℝ)) * g1 + (240000 / (SA:ℝ)) * g2
      + (400000000 / (SA:ℝ)) * wfun (g0) + (600000000 / (SA:ℝ)) * wfun (g0 + g1) + (1200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g1) + (600000000 / (SA:ℝ)) * wfun (g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g2)) * SA
      = 240000 * g0 + 240000 * g1 + 240000 * g2 + 400000000 * wfun (g0) + 600000000 * wfun (g0 + g1) + 1200000000 * wfun (g0 + g1 + g2) + 400000000 * wfun (g1) + 600000000 * wfun (g1 + g2) + 400000000 * wfun (g2) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 400000000), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 600000000), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 1200000000), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 400000000), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 600000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 400000000)]

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2)
    (hle : match ax with | 0 => g0 ≤ (q : ℝ) / SC | 1 => g1 ≤ (q : ℝ) / SC | _ => g2 ≤ (q : ℝ) / SC) :
    (b.setHi ax q).mem g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  match ax with
  | 0 => exact ⟨h01, hle, h11, h12, h21, h22⟩
  | 1 => exact ⟨h01, h02, h11, hle, h21, h22⟩
  | n + 2 => exact ⟨h01, h02, h11, h12, h21, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2)
    (hge : match ax with | 0 => (q : ℝ) / SC ≤ g0 | 1 => (q : ℝ) / SC ≤ g1 | _ => (q : ℝ) / SC ≤ g2) :
    (b.setLo ax q).mem g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  match ax with
  | 0 => exact ⟨hge, h02, h11, h12, h21, h22⟩
  | 1 => exact ⟨h01, h02, hge, h12, h21, h22⟩
  | n + 2 => exact ⟨h01, h02, h11, h12, hge, h22⟩

theorem walk_split (tb : CTN) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk tb bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk tb bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, if_true, h1]
  exact h2

theorem walk_sound (tb : CTN) (hok : tb.allOk = true) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk tb bits fuel pos b = some pos' →
      ∀ g0 g1 g2 : ℝ, b.mem g0 g1 g2 → (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk] at h
  | succ fuel ih =>
    intro pos b pos' h g0 g1 g2 hm
    simp only [walk] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 g0 g1 g2
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h g0 g1 g2
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total g0 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b 0 q g0 g1 g2 hm hs)
        | 1, hlo, hhi =>
          rcases le_total g1 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b 1 q g0 g1 g2 hm hs)
        | n + 2, hlo, hhi =>
          rcases le_total g2 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 2) q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b (n + 2) q g0 g1 g2 hm hs)
    · exact leaf_sound tb hok b hleaf g0 g1 g2 hm

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

theorem of_check (tb : CTN) (hok : tb.allOk = true) (bits fuel : ℕ)
    (cover0 cover1 cover2 : List (ℕ × ℕ × Bool)) (S0 S1 S2 : ℕ)
    (hS0 : cN * SC ≤ 240000 * S0) (hS1 : cN * SC ≤ 240000 * S1) (hS2 : cN * SC ≤ 240000 * S2)
    (hcov0 : coverCheck tb 400000000 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck tb 400000000 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck tb 400000000 (SC / 2) S2 cover2 = true)
    (hwin : cN * 100 ≤ 19 * 400000000)
    (hrun : ∀ i0 i1 i2, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length →
      ∃ pos pos', walk tb bits fuel pos (boxOf (badOf cover0) (badOf cover1) (badOf cover2) i0 i1 i2) = some pos') :
    ∀ g0 g1 g2 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  intro g0 g1 g2 hg0 hg1 hg2
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g0 * SA = 240000 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 240000 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g0 * SA = 400000000 * wfun g0 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g1 * SA = 240000 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 240000 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g1 * SA = 400000000 * wfun g1 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g2 * SA = 240000 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 240000 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g2 * SA = 400000000 * wfun g2 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2))]
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2))]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 hi0 hi1 hi2
  exact walk_sound tb hok bits fuel pos _ pos' hwalk g0 g1 g2 ⟨hb01', hb02', hb11', hb12', hb21', hb22'⟩

end Zeta23Ext.Bridge.ThreePoint.FourN

end

/-! ###### certificate data `FourN`: 1022 cells, 3847 leaves ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.FourNData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.FourN

set_option maxRecDepth 100000

def tab0 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨39614081257132168796771975168, 59421121885698253195157962752, 1, true, 331038177865⟩ CTN.nil) ⟨59421121885698253195157962752, 69324642199981295394350956544, 2, false, 242869129569⟩ (CTN.node CTN.nil ⟨69324642199981295394350956544, 74276402357122816493947453440, 2, false, 122761883704⟩ CTN.nil)) ⟨74276402357122816493947453440, 76752282435693577043745701888, 2, false, 69269436296⟩ (CTN.node (CTN.node CTN.nil ⟨76752282435693577043745701888, 77990222474978957318644826112, 2, false, 46969344551⟩ CTN.nil) ⟨77990222474978957318644826112, 79228162514264337593543950336, 2, false, 28408650442⟩ (CTN.node CTN.nil ⟨79228162514264337593543950336, 79537647524085682662268731392, 2, true, 24535647482⟩ CTN.nil))) ⟨79228162514264337593543950336, 81085072573192408005892636672, 2, true, 9481368916⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨79537647524085682662268731392, 80311360048639045334080684032, 2, true, 16061026332⟩ CTN.nil) ⟨79537647524085682662268731392, 81085072573192408005892636672, 2, true, 9481368916⟩ (CTN.node CTN.nil ⟨80311360048639045334080684032, 81085072573192408005892636672, 2, true, 9481368916⟩ CTN.nil)) ⟨81085072573192408005892636672, 81471928835469089341798612992, 2, true, 6872510006⟩ (CTN.node (CTN.node CTN.nil ⟨81085072573192408005892636672, 81858785097745770677704589312, 2, true, 4701749332⟩ CTN.nil) ⟨81085072573192408005892636672, 82632497622299133349516541952, 2, true, 1626727581⟩ (CTN.node CTN.nil ⟨81471928835469089341798612992, 81858785097745770677704589312, 2, true, 4701749332⟩ CTN.nil)))) ⟨81858785097745770677704589312, 82052213228884111345657577472, 2, true, 3776924034⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨81858785097745770677704589312, 82245641360022452013610565632, 2, true, 2957142633⟩ CTN.nil) ⟨81858785097745770677704589312, 82632497622299133349516541952, 2, true, 1626727581⟩ (CTN.node CTN.nil ⟨82052213228884111345657577472, 82245641360022452013610565632, 2, true, 2957142633⟩ CTN.nil)) ⟨82245641360022452013610565632, 82342355425591622347587059712, 2, true, 2586175977⟩ (CTN.node (CTN.node CTN.nil ⟨82245641360022452013610565632, 82439069491160792681563553792, 2, true, 2240909316⟩ CTN.nil) ⟨82245641360022452013610565632, 82632497622299133349516541952, 2, true, 1626727581⟩ (CTN.node CTN.nil ⟨82342355425591622347587059712, 82439069491160792681563553792, 2, true, 2240909316⟩ CTN.nil))) ⟨82439069491160792681563553792, 82535783556729963015540047872, 2, true, 1921155551⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨82439069491160792681563553792, 82632497622299133349516541952, 2, true, 1626727581⟩ CTN.nil) ⟨82535783556729963015540047872, 82632497622299133349516541952, 2, true, 1626727581⟩ (CTN.node CTN.nil ⟨82632497622299133349516541952, 82680854655083718516504788992, 2, true, 1488952289⟩ CTN.nil)) ⟨82632497622299133349516541952, 82729211687868303683493036032, 2, true, 1357438270⟩ (CTN.node (CTN.node CTN.nil ⟨82632497622299133349516541952, 82825925753437474017469530112, 2, true, 1113100472⟩ CTN.nil) ⟨82632497622299133349516541952, 83019353884575814685422518272, 2, true, 698530738⟩ (CTN.node CTN.nil ⟨82632497622299133349516541952, 83406210146852496021328494592, 2, true, 160574441⟩ CTN.nil)))))

def tab1 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨82729211687868303683493036032, 82777568720652888850481283072, 2, true, 1232162133⟩ CTN.nil) ⟨82729211687868303683493036032, 82825925753437474017469530112, 2, true, 1113100472⟩ (CTN.node CTN.nil ⟨82777568720652888850481283072, 82825925753437474017469530112, 2, true, 1113100472⟩ CTN.nil)) ⟨82825925753437474017469530112, 82874282786222059184457777152, 2, true, 1000229897⟩ (CTN.node (CTN.node CTN.nil ⟨82825925753437474017469530112, 82922639819006644351446024192, 2, true, 893527014⟩ CTN.nil) ⟨82825925753437474017469530112, 83019353884575814685422518272, 2, true, 698530738⟩ (CTN.node CTN.nil ⟨82874282786222059184457777152, 82922639819006644351446024192, 2, true, 893527014⟩ CTN.nil))) ⟨82922639819006644351446024192, 82970996851791229518434271232, 2, true, 792968426⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨82922639819006644351446024192, 83019353884575814685422518272, 2, true, 698530738⟩ CTN.nil) ⟨82970996851791229518434271232, 83019353884575814685422518272, 2, true, 698530738⟩ (CTN.node CTN.nil ⟨83019353884575814685422518272, 83067710917360399852410765312, 2, true, 610190560⟩ CTN.nil)) ⟨83019353884575814685422518272, 83116067950144985019399012352, 2, true, 527924488⟩ (CTN.node (CTN.node CTN.nil ⟨83019353884575814685422518272, 83212782015714155353375506432, 2, true, 381521105⟩ CTN.nil) ⟨83019353884575814685422518272, 83406210146852496021328494592, 2, true, 160574441⟩ (CTN.node CTN.nil ⟨83067710917360399852410765312, 83116067950144985019399012352, 2, true, 527924488⟩ CTN.nil)))) ⟨83116067950144985019399012352, 83164424982929570186387259392, 2, true, 451709134⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨83116067950144985019399012352, 83212782015714155353375506432, 2, true, 381521105⟩ CTN.nil) ⟨83164424982929570186387259392, 83212782015714155353375506432, 2, true, 381521105⟩ (CTN.node CTN.nil ⟨83212782015714155353375506432, 83309496081283325687352000512, 2, true, 259133459⟩ CTN.nil)) ⟨83212782015714155353375506432, 83406210146852496021328494592, 2, true, 160574441⟩ (CTN.node (CTN.node CTN.nil ⟨83309496081283325687352000512, 83406210146852496021328494592, 2, true, 160574441⟩ CTN.nil) ⟨83406210146852496021328494592, 83502924212421666355304988672, 2, true, 85656967⟩ (CTN.node CTN.nil ⟨83406210146852496021328494592, 83599638277990836689281482752, 2, true, 34193995⟩ CTN.nil))) ⟨83502924212421666355304988672, 83599638277990836689281482752, 2, true, 34193995⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨83793066409129177357234470912, 83986494540267518025187459072, 2, true, 875097⟩ CTN.nil) ⟨83793066409129177357234470912, 84179922671405858693140447232, 2, true, 866706⟩ (CTN.node CTN.nil ⟨83986494540267518025187459072, 84179922671405858693140447232, 2, true, 58580630⟩ CTN.nil)) ⟨84179922671405858693140447232, 84566778933682540029046423552, 2, true, 203546885⟩ (CTN.node (CTN.node CTN.nil ⟨84179922671405858693140447232, 84953635195959221364952399872, 2, true, 199695620⟩ CTN.nil) ⟨84179922671405858693140447232, 85727347720512584036764352512, 2, true, 192264785⟩ (CTN.node CTN.nil ⟨84179922671405858693140447232, 87274772769619309380388257792, 2, true, 178419692⟩ CTN.nil)))))

def tab2 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨84566778933682540029046423552, 84953635195959221364952399872, 2, true, 753911279⟩ CTN.nil) ⟨84953635195959221364952399872, 85727347720512584036764352512, 2, true, 1609622259⟩ (CTN.node CTN.nil ⟨85727347720512584036764352512, 87274772769619309380388257792, 2, true, 4137262453⟩ CTN.nil)) ⟨87274772769619309380388257792, 90369622867832760067636068352, 2, true, 11778340313⟩ (CTN.node (CTN.node CTN.nil ⟨90369622867832760067636068352, 91607562907118140342535192576, 2, true, 41297698399⟩ CTN.nil) ⟨91607562907118140342535192576, 94083442985688900892333441024, 2, true, 52910124749⟩ (CTN.node CTN.nil ⟨94083442985688900892333441024, 99035203142830421991929937920, 2, true, 75832144115⟩ CTN.nil))) ⟨99035203142830421991929937920, 118842243771396506390315925504, 3, false, 80226784524⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨118842243771396506390315925504, 138649284399962590788701913088, 3, true, 86044756753⟩ CTN.nil) ⟨138649284399962590788701913088, 148552804714245632987894906880, 4, false, 37512836325⟩ (CTN.node CTN.nil ⟨148552804714245632987894906880, 149790744753531013262794031104, 4, false, 36601291682⟩ CTN.nil)) ⟨149790744753531013262794031104, 152885594851744463950041841664, 4, false, 18226279074⟩ (CTN.node (CTN.node CTN.nil ⟨149790744753531013262794031104, 155980444949957914637289652224, 4, false, 6365304312⟩ CTN.nil) ⟨152885594851744463950041841664, 154433019900851189293665746944, 4, false, 12057800702⟩ (CTN.node CTN.nil ⟨152885594851744463950041841664, 155980444949957914637289652224, 4, false, 6731724963⟩ CTN.nil)))) ⟨154433019900851189293665746944, 155206732425404551965477699584, 4, false, 9381492901⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨154433019900851189293665746944, 155980444949957914637289652224, 4, false, 6880655470⟩ CTN.nil) ⟨155206732425404551965477699584, 155593588687681233301383675904, 4, false, 8154586159⟩ (CTN.node CTN.nil ⟨155206732425404551965477699584, 155980444949957914637289652224, 4, false, 6946016030⟩ CTN.nil)) ⟨155593588687681233301383675904, 155787016818819573969336664064, 4, false, 7570031424⟩ (CTN.node (CTN.node CTN.nil ⟨155593588687681233301383675904, 155980444949957914637289652224, 4, false, 6976364870⟩ CTN.nil) ⟨155787016818819573969336664064, 155980444949957914637289652224, 4, false, 6990950273⟩ (CTN.node CTN.nil ⟨155980444949957914637289652224, 156173873081096255305242640384, 4, false, 6435510271⟩ CTN.nil))) ⟨155980444949957914637289652224, 156367301212234595973195628544, 4, false, 5892316906⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨155980444949957914637289652224, 156754157474511277309101604864, 4, false, 4884069333⟩ CTN.nil) ⟨155980444949957914637289652224, 157527869999064639980913557504, 4, false, 3171821528⟩ (CTN.node CTN.nil ⟨155980444949957914637289652224, 158456325028528675187087900672, 4, false, 1629667415⟩ CTN.nil)) ⟨156173873081096255305242640384, 156270587146665425639219134464, 4, false, 6172561523⟩ (CTN.node (CTN.node CTN.nil ⟨156173873081096255305242640384, 156367301212234595973195628544, 4, false, 5903663357⟩ CTN.nil) ⟨156270587146665425639219134464, 156367301212234595973195628544, 4, false, 5909199941⟩ (CTN.node CTN.nil ⟨156367301212234595973195628544, 156464015277803766307172122624, 4, false, 5651735354⟩ CTN.nil)))))

def tab3 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨156367301212234595973195628544, 156754157474511277309101604864, 4, false, 4902043129⟩ CTN.nil) ⟨156464015277803766307172122624, 156560729343372936641148616704, 4, false, 5400160624⟩ (CTN.node CTN.nil ⟨156560729343372936641148616704, 156657443408942106975125110784, 4, false, 5154468285⟩ CTN.nil)) ⟨156560729343372936641148616704, 156754157474511277309101604864, 4, false, 4910531508⟩ (CTN.node (CTN.node CTN.nil ⟨156657443408942106975125110784, 156754157474511277309101604864, 4, false, 4914650582⟩ CTN.nil) ⟨156754157474511277309101604864, 156802514507295862476089851904, 4, false, 4798888812⟩ (CTN.node CTN.nil ⟨156754157474511277309101604864, 156850871540080447643078098944, 4, false, 4680699447⟩ CTN.nil))) ⟨156754157474511277309101604864, 156947585605649617977054593024, 4, false, 4449125586⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨156754157474511277309101604864, 157141013736787958645007581184, 4, false, 4005065260⟩ CTN.nil) ⟨156754157474511277309101604864, 157527869999064639980913557504, 4, false, 3192232409⟩ (CTN.node CTN.nil ⟨156802514507295862476089851904, 156850871540080447643078098944, 4, false, 4682565917⟩ CTN.nil)) ⟨156850871540080447643078098944, 156899228572865032810066345984, 4, false, 4567709043⟩ (CTN.node (CTN.node CTN.nil ⟨156850871540080447643078098944, 156947585605649617977054593024, 4, false, 4452606511⟩ CTN.nil) ⟨156899228572865032810066345984, 156947585605649617977054593024, 4, false, 4454317100⟩ (CTN.node CTN.nil ⟨156947585605649617977054593024, 156995942638434203144042840064, 4, false, 4342388998⟩ CTN.nil)))) ⟨156947585605649617977054593024, 157044299671218788311031087104, 4, false, 4230363084⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨156947585605649617977054593024, 157141013736787958645007581184, 4, false, 4011070826⟩ CTN.nil) ⟨156995942638434203144042840064, 157044299671218788311031087104, 4, false, 4231923619⟩ (CTN.node CTN.nil ⟨157044299671218788311031087104, 157092656704003373478019334144, 4, false, 4122919829⟩ CTN.nil)) ⟨157044299671218788311031087104, 157141013736787958645007581184, 4, false, 4013960191⟩ (CTN.node (CTN.node CTN.nil ⟨157092656704003373478019334144, 157141013736787958645007581184, 4, false, 4015376474⟩ CTN.nil) ⟨157141013736787958645007581184, 157189370769572543811995828224, 4, false, 3909292386⟩ (CTN.node CTN.nil ⟨157141013736787958645007581184, 157237727802357128978984075264, 4, false, 3803388551⟩ CTN.nil))) ⟨157141013736787958645007581184, 157334441867926299312960569344, 4, false, 3596294550⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨157141013736787958645007581184, 157527869999064639980913557504, 4, false, 3200827096⟩ CTN.nil) ⟨157189370769572543811995828224, 157237727802357128978984075264, 4, false, 3804666362⟩ (CTN.node CTN.nil ⟨157237727802357128978984075264, 157334441867926299312960569344, 4, false, 3598638570⟩ CTN.nil)) ⟨157334441867926299312960569344, 157431155933495469646937063424, 4, false, 3399700370⟩ (CTN.node (CTN.node CTN.nil ⟨157334441867926299312960569344, 157527869999064639980913557504, 4, false, 3204719257⟩ CTN.nil) ⟨157431155933495469646937063424, 157527869999064639980913557504, 4, false, 3206563771⟩ (CTN.node CTN.nil ⟨157527869999064639980913557504, 157624584064633810314890051584, 4, false, 3019218286⟩ CTN.nil)))))

def tab4 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨157527869999064639980913557504, 157914726261341321316819533824, 4, false, 2488695770⟩ CTN.nil) ⟨157527869999064639980913557504, 158301582523618002652725510144, 4, false, 1865845891⟩ (CTN.node CTN.nil ⟨157527869999064639980913557504, 158456325028528675187087900672, 4, false, 1643246852⟩ CTN.nil)) ⟨157624584064633810314890051584, 157721298130202980648866545664, 4, false, 2837653144⟩ (CTN.node (CTN.node CTN.nil ⟨157721298130202980648866545664, 157818012195772150982843039744, 4, false, 2661857281⟩ CTN.nil) ⟨157721298130202980648866545664, 157914726261341321316819533824, 4, false, 2490837858⟩ (CTN.node CTN.nil ⟨157818012195772150982843039744, 157914726261341321316819533824, 4, false, 2491819326⟩ CTN.nil))) ⟨157914726261341321316819533824, 158108154392479661984772521984, 4, false, 2168353114⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨157914726261341321316819533824, 158301582523618002652725510144, 4, false, 1867963109⟩ CTN.nil) ⟨158108154392479661984772521984, 158301582523618002652725510144, 4, false, 1868712167⟩ (CTN.node CTN.nil ⟨158301582523618002652725510144, 158456325028528675187087900672, 4, false, 1645414146⟩ CTN.nil)) ⟨158456325028528675187087900672, 158495010654756343320678498304, 4, true, 1591808227⟩ (CTN.node (CTN.node CTN.nil ⟨158456325028528675187087900672, 158688438785894683988631486464, 4, true, 1337086167⟩ CTN.nil) ⟨158456325028528675187087900672, 159075295048171365324537462784, 4, true, 895367555⟩ (CTN.node CTN.nil ⟨158495010654756343320678498304, 158688438785894683988631486464, 4, true, 1337086167⟩ CTN.nil)))) ⟨158688438785894683988631486464, 158881866917033024656584474624, 4, true, 1104977691⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨158688438785894683988631486464, 159075295048171365324537462784, 4, true, 895367555⟩ CTN.nil) ⟨158881866917033024656584474624, 159075295048171365324537462784, 4, true, 895367555⟩ (CTN.node CTN.nil ⟨159075295048171365324537462784, 159268723179309705992490450944, 4, true, 708136113⟩ CTN.nil)) ⟨159075295048171365324537462784, 159462151310448046660443439104, 4, true, 543159341⟩ (CTN.node (CTN.node CTN.nil ⟨159075295048171365324537462784, 159849007572724727996349415424, 4, true, 279452190⟩ CTN.nil) ⟨159075295048171365324537462784, 160622720097278090668161368064, 4, true, 13164037⟩ (CTN.node CTN.nil ⟨159268723179309705992490450944, 159462151310448046660443439104, 4, true, 543159341⟩ CTN.nil))) ⟨159462151310448046660443439104, 159655579441586387328396427264, 4, true, 400308901⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨159462151310448046660443439104, 159849007572724727996349415424, 4, true, 279452190⟩ CTN.nil) ⟨159655579441586387328396427264, 159849007572724727996349415424, 4, true, 279452190⟩ (CTN.node CTN.nil ⟨159849007572724727996349415424, 160235863835001409332255391744, 4, true, 103168503⟩ CTN.nil)) ⟨159849007572724727996349415424, 160622720097278090668161368064, 4, true, 13164037⟩ (CTN.node (CTN.node CTN.nil ⟨160235863835001409332255391744, 160622720097278090668161368064, 4, true, 13164037⟩ CTN.nil) ⟨161009576359554772004067344384, 161396432621831453339973320704, 4, true, 8149981⟩ (CTN.node CTN.nil ⟨161396432621831453339973320704, 162170145146384816011785273344, 4, true, 85422324⟩ CTN.nil)))))

def tab5 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨161396432621831453339973320704, 163717570195491541355409178624, 4, true, 82200384⟩ CTN.nil) ⟨162170145146384816011785273344, 163717570195491541355409178624, 4, true, 472303465⟩ (CTN.node CTN.nil ⟨162170145146384816011785273344, 164491282720044904027221131264, 4, true, 463375292⟩ CTN.nil)) ⟨162170145146384816011785273344, 165264995244598266699033083904, 4, true, 454657575⟩ (CTN.node (CTN.node CTN.nil ⟨162170145146384816011785273344, 166812420293704992042656989184, 4, true, 437829947⟩ CTN.nil) ⟨162170145146384816011785273344, 168359845342811717386280894464, 4, true, 421775370⟩ (CTN.node CTN.nil ⟨162170145146384816011785273344, 171454695441025168073528705024, 4, true, 391818784⟩ CTN.nil))) ⟨162170145146384816011785273344, 174549545539238618760776515584, 4, true, 364480342⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨162170145146384816011785273344, 178263365657094759585473888256, 4, true, 334751802⟩ CTN.nil) ⟨162943857670938178683597225984, 164491282720044904027221131264, 4, true, 1167424076⟩ (CTN.node CTN.nil ⟨162943857670938178683597225984, 165264995244598266699033083904, 4, true, 1145460727⟩ CTN.nil)) ⟨163717570195491541355409178624, 164878138982321585363127107584, 4, true, 2178067720⟩ (CTN.node (CTN.node CTN.nil ⟨163717570195491541355409178624, 165264995244598266699033083904, 4, true, 2157506488⟩ CTN.nil) ⟨163717570195491541355409178624, 166038707769151629370845036544, 4, true, 2117108424⟩ (CTN.node CTN.nil ⟨163717570195491541355409178624, 166812420293704992042656989184, 4, true, 2077653608⟩ CTN.nil)))) ⟨163717570195491541355409178624, 168359845342811717386280894464, 4, true, 2001469121⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨164104426457768222691315154944, 165264995244598266699033083904, 4, true, 2785526926⟩ CTN.nil) ⟨164491282720044904027221131264, 166038707769151629370845036544, 4, true, 3430087390⟩ (CTN.node CTN.nil ⟨164491282720044904027221131264, 166812420293704992042656989184, 4, true, 3366163659⟩ CTN.nil)) ⟨165264995244598266699033083904, 168359845342811717386280894464, 4, true, 4789633321⟩ (CTN.node (CTN.node CTN.nil ⟨165264995244598266699033083904, 169907270391918442729904799744, 4, true, 4615617497⟩ CTN.nil) ⟨165264995244598266699033083904, 171454695441025168073528705024, 4, true, 4449449732⟩ (CTN.node CTN.nil ⟨165264995244598266699033083904, 174549545539238618760776515584, 4, true, 4138997472⟩ CTN.nil))) ⟨166812420293704992042656989184, 169907270391918442729904799744, 4, true, 8487232786⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨166812420293704992042656989184, 171454695441025168073528705024, 4, true, 8181682228⟩ CTN.nil) ⟨168359845342811717386280894464, 174549545539238618760776515584, 4, true, 12146120750⟩ (CTN.node CTN.nil ⟨168359845342811717386280894464, 178263365657094759585473888256, 4, true, 11155432404⟩ CTN.nil)) ⟨174549545539238618760776515584, 175787485578523999035675639808, 4, true, 39186989529⟩ (CTN.node (CTN.node CTN.nil ⟨175787485578523999035675639808, 178263365657094759585473888256, 4, true, 43773716666⟩ CTN.nil) ⟨178263365657094759585473888256, 180739245735665520135272136704, 5, false, 55304609886⟩ (CTN.node CTN.nil ⟨178263365657094759585473888256, 198070406285660843983859875840, 5, false, 38217750111⟩ CTN.nil)))))

def tab6 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨217877446914226928382245863424, 220353326992797688932044111872, 6, false, 41549598057⟩ CTN.nil) ⟨220353326992797688932044111872, 221591267032083069206943236096, 6, false, 37442452611⟩ (CTN.node CTN.nil ⟨221591267032083069206943236096, 231185302336544766337411448832, 6, false, 7285265055⟩ CTN.nil)) ⟨227780967228509970581438857216, 237065517523150322643182288896, 6, false, 539486562⟩ (CTN.node (CTN.node CTN.nil ⟨230875817326723421268686667776, 237065517523150322643182288896, 6, false, 577656718⟩ CTN.nil) ⟨231185302336544766337411448832, 232384556749602478478719975424, 6, false, 5990530514⟩ (CTN.node CTN.nil ⟨231185302336544766337411448832, 233583811162660190620028502016, 6, false, 4027054120⟩ CTN.nil))) ⟨231185302336544766337411448832, 235982319988775614902645555200, 6, false, 1306499045⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨232384556749602478478719975424, 233583811162660190620028502016, 6, false, 4083159655⟩ CTN.nil) ⟨233583811162660190620028502016, 234183438369189046690682765312, 6, false, 3285883949⟩ (CTN.node CTN.nil ⟨233583811162660190620028502016, 234783065575717902761337028608, 6, false, 2539642107⟩ CTN.nil)) ⟨233583811162660190620028502016, 235982319988775614902645555200, 6, false, 1346781940⟩ (CTN.node (CTN.node CTN.nil ⟨233970667424936871955934478336, 237065517523150322643182288896, 6, false, 604238840⟩ CTN.nil) ⟨233970667424936871955934478336, 237684487542793012780631851008, 6, false, 313549502⟩ (CTN.node CTN.nil ⟨234183438369189046690682765312, 234483251972453474726009896960, 6, false, 2917054281⟩ CTN.nil)))) ⟨234183438369189046690682765312, 234783065575717902761337028608, 6, false, 2554620136⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨234483251972453474726009896960, 234783065575717902761337028608, 6, false, 2561735901⟩ CTN.nil) ⟨234783065575717902761337028608, 235082879178982330796664160256, 6, false, 2229636307⟩ (CTN.node CTN.nil ⟨234783065575717902761337028608, 235382692782246758831991291904, 6, false, 1915826568⟩ CTN.nil)) ⟨234783065575717902761337028608, 235982319988775614902645555200, 6, false, 1362675081⟩ (CTN.node (CTN.node CTN.nil ⟨235082879178982330796664160256, 235382692782246758831991291904, 6, false, 1920764168⟩ CTN.nil) ⟨235382692782246758831991291904, 235682506385511186867318423552, 6, false, 1635115293⟩ (CTN.node CTN.nil ⟨235382692782246758831991291904, 235982319988775614902645555200, 6, false, 1369525210⟩ CTN.nil))) ⟨235518092474043597299558383616, 237684487542793012780631851008, 6, false, 318089829⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨235682506385511186867318423552, 235982319988775614902645555200, 6, false, 1372672698⟩ CTN.nil) ⟨235982319988775614902645555200, 236581947195304470973299818496, 6, false, 915534195⟩ (CTN.node CTN.nil ⟨235982319988775614902645555200, 237181574401833327043954081792, 6, false, 551690236⟩ CTN.nil)) ⟨235982319988775614902645555200, 237684487542793012780631851008, 6, false, 318991089⟩ (CTN.node (CTN.node CTN.nil ⟨236291804998596959971370336256, 237684487542793012780631851008, 6, false, 319472457⟩ CTN.nil) ⟨236581947195304470973299818496, 237181574401833327043954081792, 6, false, 553470300⟩ (CTN.node CTN.nil ⟨237065517523150322643182288896, 237684487542793012780631851008, 6, false, 320255712⟩ CTN.nil)))))

def tab7 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨237452373785427003979088265216, 237684487542793012780631851008, 6, false, 320421564⟩ CTN.nil) ⟨237684487542793012780631851008, 237839230047703685314994241536, 6, true, 261313260⟩ (CTN.node CTN.nil ⟨237684487542793012780631851008, 238226086309980366650900217856, 6, true, 140019498⟩ CTN.nil)) ⟨237684487542793012780631851008, 238380828814891039185262608384, 6, true, 102076243⟩ (CTN.node (CTN.node CTN.nil ⟨237684487542793012780631851008, 238612942572257047986806194176, 6, true, 56434938⟩ CTN.nil) ⟨237839230047703685314994241536, 238419514441118707318853206016, 6, true, 93531111⟩ (CTN.node CTN.nil ⟨237839230047703685314994241536, 238612942572257047986806194176, 6, true, 56434938⟩ CTN.nil))) ⟨237839230047703685314994241536, 238999798834533729322712170496, 6, true, 10266640⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨238032658178842025982947229696, 238612942572257047986806194176, 6, true, 56434938⟩ CTN.nil) ⟨238226086309980366650900217856, 238612942572257047986806194176, 6, true, 56434938⟩ (CTN.node CTN.nil ⟨238226086309980366650900217856, 238806370703395388654759182336, 6, true, 28693336⟩ CTN.nil)) ⟨238226086309980366650900217856, 238999798834533729322712170496, 6, true, 10266640⟩ (CTN.node (CTN.node CTN.nil ⟨238419514441118707318853206016, 238806370703395388654759182336, 6, true, 28693336⟩ CTN.nil) ⟨238419514441118707318853206016, 238999798834533729322712170496, 6, true, 10266640⟩ (CTN.node CTN.nil ⟨238612942572257047986806194176, 238999798834533729322712170496, 6, true, 10266640⟩ CTN.nil)))) ⟨238612942572257047986806194176, 239193226965672069990665158656, 6, true, 1113172⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨238806370703395388654759182336, 239096512900102899656688664576, 6, true, 4533435⟩ CTN.nil) ⟨238806370703395388654759182336, 239193226965672069990665158656, 6, true, 1113172⟩ (CTN.node CTN.nil ⟨238903084768964558988735676416, 239193226965672069990665158656, 6, true, 1113172⟩ CTN.nil)) ⟨238999798834533729322712170496, 239193226965672069990665158656, 6, true, 1113172⟩ (CTN.node (CTN.node CTN.nil ⟨239289941031241240324641652736, 239483369162379580992594640896, 6, true, 329⟩ CTN.nil) ⟨239289941031241240324641652736, 239580083227948751326571134976, 6, true, 328⟩ (CTN.node CTN.nil ⟨239386655096810410658618146816, 239531726195164166159582887936, 6, true, 1186366⟩ CTN.nil))) ⟨239386655096810410658618146816, 239580083227948751326571134976, 6, true, 1185403⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨239386655096810410658618146816, 239676797293517921660547629056, 6, true, 1183480⟩ CTN.nil) ⟨239386655096810410658618146816, 239773511359087091994524123136, 6, true, 1181561⟩ (CTN.node CTN.nil ⟨239386655096810410658618146816, 239966939490225432662477111296, 6, true, 1177735⟩ CTN.nil)) ⟨239386655096810410658618146816, 240160367621363773330430099456, 6, true, 1173924⟩ (CTN.node (CTN.node CTN.nil ⟨239386655096810410658618146816, 240547223883640454666336075776, 6, true, 1166349⟩ CTN.nil) ⟨239386655096810410658618146816, 240934080145917136002242052096, 6, true, 1158835⟩ (CTN.node CTN.nil ⟨239386655096810410658618146816, 241707792670470498674054004736, 6, true, 1143988⟩ CTN.nil)))))

def tab8 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨239483369162379580992594640896, 239628440260733336493559382016, 6, true, 4662827⟩ CTN.nil) ⟨239483369162379580992594640896, 239676797293517921660547629056, 6, true, 4659045⟩ (CTN.node CTN.nil ⟨239483369162379580992594640896, 239773511359087091994524123136, 6, true, 4651490⟩ CTN.nil)) ⟨239531726195164166159582887936, 239676797293517921660547629056, 6, true, 7258139⟩ (CTN.node (CTN.node CTN.nil ⟨239580083227948751326571134976, 239725154326302506827535876096, 6, true, 10423846⟩ CTN.nil) ⟨239580083227948751326571134976, 239773511359087091994524123136, 6, true, 10415393⟩ (CTN.node CTN.nil ⟨239580083227948751326571134976, 239870225424656262328500617216, 6, true, 10398512⟩ CTN.nil))) ⟨239580083227948751326571134976, 239966939490225432662477111296, 6, true, 10381665⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨239580083227948751326571134976, 240160367621363773330430099456, 6, true, 10348074⟩ CTN.nil) ⟨239628440260733336493559382016, 239725154326302506827535876096, 6, true, 14170688⟩ (CTN.node CTN.nil ⟨239628440260733336493559382016, 239773511359087091994524123136, 6, true, 14159196⟩ CTN.nil)) ⟨239676797293517921660547629056, 239773511359087091994524123136, 6, true, 18478412⟩ (CTN.node (CTN.node CTN.nil ⟨239676797293517921660547629056, 239821868391871677161512370176, 6, true, 18463430⟩ CTN.nil) ⟨239676797293517921660547629056, 239870225424656262328500617216, 6, true, 18448463⟩ (CTN.node CTN.nil ⟨239676797293517921660547629056, 239966939490225432662477111296, 6, true, 18418575⟩ CTN.nil)))) ⟨239725154326302506827535876096, 239821868391871677161512370176, 6, true, 23354711⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨239725154326302506827535876096, 239870225424656262328500617216, 6, true, 23335779⟩ CTN.nil) ⟨239773511359087091994524123136, 239870225424656262328500617216, 6, true, 28798809⟩ (CTN.node CTN.nil ⟨239773511359087091994524123136, 239918582457440847495488864256, 6, true, 28775469⟩ CTN.nil)) ⟨239773511359087091994524123136, 239966939490225432662477111296, 6, true, 28752152⟩ (CTN.node (CTN.node CTN.nil ⟨239773511359087091994524123136, 240063653555794602996453605376, 6, true, 28705590⟩ CTN.nil) ⟨239773511359087091994524123136, 240160367621363773330430099456, 6, true, 28659122⟩ (CTN.node CTN.nil ⟨239773511359087091994524123136, 240353795752502113998383087616, 6, true, 28566468⟩ CTN.nil))) ⟨239773511359087091994524123136, 240547223883640454666336075776, 6, true, 28474189⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨239773511359087091994524123136, 240934080145917136002242052096, 6, true, 28290747⟩ CTN.nil) ⟨239821868391871677161512370176, 239918582457440847495488864256, 6, true, 34809922⟩ (CTN.node CTN.nil ⟨239821868391871677161512370176, 239966939490225432662477111296, 6, true, 34781715⟩ CTN.nil)) ⟨239870225424656262328500617216, 239966939490225432662477111296, 6, true, 41387258⟩ (CTN.node (CTN.node CTN.nil ⟨239870225424656262328500617216, 240015296523010017829465358336, 6, true, 41353730⟩ CTN.nil) ⟨239870225424656262328500617216, 240063653555794602996453605376, 6, true, 41320235⟩ (CTN.node CTN.nil ⟨239870225424656262328500617216, 240160367621363773330430099456, 6, true, 41253346⟩ CTN.nil)))))

def tab9 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨239918582457440847495488864256, 240063653555794602996453605376, 6, true, 48490713⟩ CTN.nil) ⟨239966939490225432662477111296, 240063653555794602996453605376, 6, true, 56237401⟩ (CTN.node CTN.nil ⟨239966939490225432662477111296, 240112010588579188163441852416, 6, true, 56191860⟩ CTN.nil)) ⟨239966939490225432662477111296, 240160367621363773330430099456, 6, true, 56146365⟩ (CTN.node (CTN.node CTN.nil ⟨239966939490225432662477111296, 240257081686932943664406593536, 6, true, 56055514⟩ CTN.nil) ⟨239966939490225432662477111296, 240353795752502113998383087616, 6, true, 55964847⟩ (CTN.node CTN.nil ⟨239966939490225432662477111296, 240547223883640454666336075776, 6, true, 55784062⟩ CTN.nil))) ⟨240015296523010017829465358336, 240112010588579188163441852416, 6, true, 64508587⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨240015296523010017829465358336, 240160367621363773330430099456, 6, true, 64456359⟩ CTN.nil) ⟨240063653555794602996453605376, 240160367621363773330430099456, 6, true, 73342758⟩ (CTN.node CTN.nil ⟨240063653555794602996453605376, 240208724654148358497418346496, 6, true, 73283389⟩ CTN.nil)) ⟨240063653555794602996453605376, 240257081686932943664406593536, 6, true, 73224081⟩ (CTN.node (CTN.node CTN.nil ⟨240063653555794602996453605376, 240353795752502113998383087616, 6, true, 73105644⟩ CTN.nil) ⟨240112010588579188163441852416, 240208724654148358497418346496, 6, true, 82739084⟩ (CTN.node CTN.nil ⟨240112010588579188163441852416, 240257081686932943664406593536, 6, true, 82672123⟩ CTN.nil)))) ⟨240160367621363773330430099456, 240257081686932943664406593536, 6, true, 92696731⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨240160367621363773330430099456, 240305438719717528831394840576, 6, true, 92621726⟩ CTN.nil) ⟨240160367621363773330430099456, 240353795752502113998383087616, 6, true, 92546798⟩ (CTN.node CTN.nil ⟨240160367621363773330430099456, 240450509818071284332359581696, 6, true, 92397168⟩ CTN.nil)) ⟨240160367621363773330430099456, 240547223883640454666336075776, 6, true, 92247841⟩ (CTN.node (CTN.node CTN.nil ⟨240160367621363773330430099456, 240740652014778795334289063936, 6, true, 91950092⟩ CTN.nil) ⟨240160367621363773330430099456, 240934080145917136002242052096, 6, true, 91653544⟩ (CTN.node CTN.nil ⟨240160367621363773330430099456, 241320936408193817338148028416, 6, true, 91064031⟩ CTN.nil))) ⟨240160367621363773330430099456, 241707792670470498674054004736, 6, true, 90479255⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨240160367621363773330430099456, 242481505195023861345865957376, 6, true, 89323732⟩ CTN.nil) ⟨240160367621363773330430099456, 243255217719577224017677910016, 6, true, 88186617⟩ (CTN.node CTN.nil ⟨240160367621363773330430099456, 244802642768683949361301815296, 6, true, 85966212⟩ CTN.nil)) ⟨240160367621363773330430099456, 246350067817790674704925720576, 6, true, 83815324⟩ (CTN.node (CTN.node CTN.nil ⟨240160367621363773330430099456, 247897492866897400048549625856, 6, true, 81731354⟩ CTN.nil) ⟨240160367621363773330430099456, 249444917916004125392173531136, 6, true, 79711817⟩ (CTN.node CTN.nil ⟨240160367621363773330430099456, 252539768014217576079421341696, 6, true, 75856633⟩ CTN.nil)))))

def tab10 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨240208724654148358497418346496, 240353795752502113998383087616, 6, true, 103131356⟩ CTN.nil) ⟨240257081686932943664406593536, 240402152785286699165371334656, 6, true, 114200161⟩ (CTN.node CTN.nil ⟨240257081686932943664406593536, 240450509818071284332359581696, 6, true, 114107814⟩ CTN.nil)) ⟨240257081686932943664406593536, 240547223883640454666336075776, 6, true, 113923400⟩ (CTN.node (CTN.node CTN.nil ⟨240305438719717528831394840576, 240450509818071284332359581696, 6, true, 125827288⟩ CTN.nil) ⟨240353795752502113998383087616, 240547223883640454666336075776, 6, true, 137900312⟩ (CTN.node CTN.nil ⟨240353795752502113998383087616, 240643937949209625000312569856, 6, true, 137677536⟩ CTN.nil))) ⟨240353795752502113998383087616, 240740652014778795334289063936, 6, true, 137455210⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨240353795752502113998383087616, 240934080145917136002242052096, 6, true, 137011904⟩ CTN.nil) ⟨240450509818071284332359581696, 240643937949209625000312569856, 6, true, 163917355⟩ (CTN.node CTN.nil ⟨240450509818071284332359581696, 240740652014778795334289063936, 6, true, 163652657⟩ CTN.nil)) ⟨240547223883640454666336075776, 240740652014778795334289063936, 6, true, 192151891⟩ (CTN.node (CTN.node CTN.nil ⟨240547223883640454666336075776, 240837366080347965668265558016, 6, true, 191841724⟩ CTN.nil) ⟨240547223883640454666336075776, 240934080145917136002242052096, 6, true, 191532184⟩ (CTN.node CTN.nil ⟨240547223883640454666336075776, 241127508277055476670195040256, 6, true, 190914975⟩ CTN.nil)))) ⟨240547223883640454666336075776, 241320936408193817338148028416, 6, true, 190300253⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨240547223883640454666336075776, 241707792670470498674054004736, 6, true, 189078223⟩ CTN.nil) ⟨240643937949209625000312569856, 240837366080347965668265558016, 6, true, 222596750⟩ (CTN.node CTN.nil ⟨240643937949209625000312569856, 240934080145917136002242052096, 6, true, 222237586⟩ CTN.nil)) ⟨240740652014778795334289063936, 240934080145917136002242052096, 6, true, 255244651⟩ (CTN.node (CTN.node CTN.nil ⟨240740652014778795334289063936, 241030794211486306336218546176, 6, true, 254832975⟩ CTN.nil) ⟨240740652014778795334289063936, 241127508277055476670195040256, 6, true, 254422130⟩ (CTN.node CTN.nil ⟨240740652014778795334289063936, 241320936408193817338148028416, 6, true, 253602924⟩ CTN.nil))) ⟨240779337641006463467879661568, 245576355293237312033113767936, 6, true, 249212333⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨240779337641006463467879661568, 250373372945468160598347874304, 6, true, 230562378⟩ CTN.nil) ⟨240779337641006463467879661568, 257491528171359097179017838592, 6, true, 205990782⟩ (CTN.node CTN.nil ⟨240837366080347965668265558016, 241030794211486306336218546176, 6, true, 290088193⟩ CTN.nil)) ⟨240837366080347965668265558016, 241127508277055476670195040256, 6, true, 289620509⟩ (CTN.node (CTN.node CTN.nil ⟨240934080145917136002242052096, 241320936408193817338148028416, 6, true, 326066581⟩ CTN.nil) ⟨240934080145917136002242052096, 241514364539332158006101016576, 6, true, 325017537⟩ (CTN.node CTN.nil ⟨240934080145917136002242052096, 241707792670470498674054004736, 6, true, 323972714⟩ CTN.nil)))))

def tab11 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨240934080145917136002242052096, 242481505195023861345865957376, 6, true, 319835215⟩ CTN.nil) ⟨240934080145917136002242052096, 243255217719577224017677910016, 6, true, 315763626⟩ (CTN.node CTN.nil ⟨241127508277055476670195040256, 241514364539332158006101016576, 6, true, 406405247⟩ CTN.nil)) ⟨241127508277055476670195040256, 241707792670470498674054004736, 6, true, 405098789⟩ (CTN.node (CTN.node CTN.nil ⟨241320936408193817338148028416, 241707792670470498674054004736, 6, true, 495376037⟩ CTN.nil) ⟨241320936408193817338148028416, 241901220801608839342006992896, 6, true, 493784853⟩ (CTN.node CTN.nil ⟨241320936408193817338148028416, 242094648932747180009959981056, 6, true, 492200060⟩ CTN.nil))) ⟨241320936408193817338148028416, 242481505195023861345865957376, 6, true, 489049523⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨241514364539332158006101016576, 241901220801608839342006992896, 6, true, 592915084⟩ CTN.nil) ⟨241514364539332158006101016576, 242094648932747180009959981056, 6, true, 591012134⟩ (CTN.node CTN.nil ⟨241707792670470498674054004736, 242481505195023861345865957376, 6, true, 694482783⟩ CTN.nil)) ⟨241707792670470498674054004736, 242868361457300542681771933696, 6, true, 690044588⟩ (CTN.node (CTN.node CTN.nil ⟨241707792670470498674054004736, 243255217719577224017677910016, 6, true, 685641829⟩ CTN.nil) ⟨241707792670470498674054004736, 244028930244130586689489862656, 6, true, 676941261⟩ (CTN.node CTN.nil ⟨241707792670470498674054004736, 244802642768683949361301815296, 6, true, 668378410⟩ CTN.nil)))) ⟨241707792670470498674054004736, 245576355293237312033113767936, 6, true, 659950666⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨241707792670470498674054004736, 246350067817790674704925720576, 6, true, 651655476⟩ CTN.nil) ⟨241707792670470498674054004736, 247897492866897400048549625856, 6, true, 635452827⟩ (CTN.node CTN.nil ⟨242094648932747180009959981056, 242868361457300542681771933696, 6, true, 930293373⟩ CTN.nil)) ⟨242094648932747180009959981056, 243255217719577224017677910016, 6, true, 924357731⟩ (CTN.node (CTN.node CTN.nil ⟨242481505195023861345865957376, 243255217719577224017677910016, 6, true, 1199076992⟩ CTN.nil) ⟨242481505195023861345865957376, 244028930244130586689489862656, 6, true, 1183861102⟩ (CTN.node CTN.nil ⟨242481505195023861345865957376, 244802642768683949361301815296, 6, true, 1168886057⟩ CTN.nil))) ⟨242481505195023861345865957376, 245576355293237312033113767936, 6, true, 1154147292⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨242481505195023861345865957376, 246350067817790674704925720576, 6, true, 1139640342⟩ CTN.nil) ⟨243255217719577224017677910016, 244802642768683949361301815296, 6, true, 1810022563⟩ (CTN.node CTN.nil ⟨243255217719577224017677910016, 246350067817790674704925720576, 6, true, 1764735511⟩ CTN.nil)) ⟨243255217719577224017677910016, 247897492866897400048549625856, 6, true, 1720857432⟩ (CTN.node (CTN.node CTN.nil ⟨243255217719577224017677910016, 249444917916004125392173531136, 6, true, 1678335996⟩ CTN.nil) ⟨243255217719577224017677910016, 250992342965110850735797436416, 6, true, 1637121129⟩ (CTN.node CTN.nil ⟨243255217719577224017677910016, 252539768014217576079421341696, 6, true, 1597164902⟩ CTN.nil)))))

def tab12 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨243255217719577224017677910016, 257491528171359097179017838592, 6, true, 1477240831⟩ CTN.nil) ⟨244028930244130586689489862656, 247123780342344037376737673216, 6, true, 2495413140⟩ (CTN.node CTN.nil ⟨244802642768683949361301815296, 247897492866897400048549625856, 6, true, 3341070594⟩ CTN.nil)) ⟨244802642768683949361301815296, 249444917916004125392173531136, 6, true, 3258514586⟩ (CTN.node (CTN.node CTN.nil ⟨244802642768683949361301815296, 250992342965110850735797436416, 6, true, 3178495302⟩ CTN.nil) ⟨244802642768683949361301815296, 252539768014217576079421341696, 6, true, 3100919687⟩ (CTN.node CTN.nil ⟨245576355293237312033113767936, 250373372945468160598347874304, 6, true, 4180010322⟩ CTN.nil))) ⟨246350067817790674704925720576, 250992342965110850735797436416, 6, true, 5223624809⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨246350067817790674704925720576, 252539768014217576079421341696, 6, true, 5096134953⟩ CTN.nil) ⟨246350067817790674704925720576, 255634618112431026766669152256, 6, true, 4852623744⟩ (CTN.node CTN.nil ⟨246350067817790674704925720576, 257491528171359097179017838592, 6, true, 4713488648⟩ CTN.nil)) ⟨249444917916004125392173531136, 257491528171359097179017838592, 6, true, 9713220361⟩ (CTN.node (CTN.node CTN.nil ⟨250373372945468160598347874304, 257491528171359097179017838592, 6, true, 11532825879⟩ CTN.nil) ⟨257491528171359097179017838592, 258729468210644477453916962816, 7, false, 28791006768⟩ (CTN.node CTN.nil ⟨257491528171359097179017838592, 259967408249929857728816087040, 7, false, 28243949556⟩ CTN.nil)))) ⟨257491528171359097179017838592, 261824318308857928141164773376, 7, false, 27447518209⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨257491528171359097179017838592, 264919168407071378828412583936, 7, false, 26181555955⟩ CTN.nil) ⟨257491528171359097179017838592, 271108868603498280202908205056, 7, false, 23861384437⟩ (CTN.node CTN.nil ⟨259967408249929857728816087040, 260586378269572547866265649152, 7, false, 34886068921⟩ CTN.nil)) ⟨260586378269572547866265649152, 261205348289215238003715211264, 7, false, 36298653532⟩ (CTN.node (CTN.node CTN.nil ⟨261205348289215238003715211264, 262443288328500618278614335488, 7, false, 37331393477⟩ CTN.nil) ⟨262443288328500618278614335488, 267395048485642139378210832384, 7, false, 37813565000⟩ (CTN.node CTN.nil ⟨267395048485642139378210832384, 277298568799925181577403826176, 7, false, 43210796373⟩ CTN.nil))) ⟨277298568799925181577403826176, 287202089114208223776596819968, 7, true, 42337514840⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨287202089114208223776596819968, 292153849271349744876193316864, 7, true, 36042427684⟩ CTN.nil) ⟨292153849271349744876193316864, 293391789310635125151092441088, 7, true, 35001008619⟩ (CTN.node CTN.nil ⟨293391789310635125151092441088, 297105609428491265975789813760, 7, true, 26396659657⟩ CTN.nil)) ⟨297105609428491265975789813760, 304765363421569556426728144896, 8, false, 11195658215⟩ (CTN.node (CTN.node CTN.nil ⟨304765363421569556426728144896, 316138937532503987702363848704, 8, false, 229159249⟩ CTN.nil) ⟨309175524811523723656056274944, 316912650057057350374175801344, 8, false, 91689533⟩ (CTN.node CTN.nil ⟨311960889899915829274579304448, 315055739998129279961827115008, 8, false, 638832862⟩ CTN.nil)))))

def tab13 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨312270374909737174343304085504, 316216308784959323969545043968, 8, false, 244184786⟩ CTN.nil) ⟨312270374909737174343304085504, 316912650057057350374175801344, 8, false, 97511382⟩ (CTN.node CTN.nil ⟨313508314949022554618203209728, 315829452522682642633639067648, 8, false, 359339565⟩ CTN.nil)) ⟨313508314949022554618203209728, 316603165047236005305451020288, 8, false, 156589595⟩ (CTN.node (CTN.node CTN.nil ⟨313817799958843899686927990784, 316564479421008337171860422656, 8, false, 165200074⟩ CTN.nil) ⟨313817799958843899686927990784, 316912650057057350374175801344, 8, false, 99379817⟩ (CTN.node CTN.nil ⟨314282027473575917290015162368, 315829452522682642633639067648, 8, false, 361583136⟩ CTN.nil))) ⟨314282027473575917290015162368, 316603165047236005305451020288, 8, false, 157670757⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨314668883735852598625921138688, 316641850673463673439041617920, 8, false, 150134755⟩ CTN.nil) ⟨314668883735852598625921138688, 316912650057057350374175801344, 8, false, 100095080⟩ (CTN.node CTN.nil ⟨315017054371901611828236517376, 316912650057057350374175801344, 8, false, 100322671⟩ CTN.nil)) ⟨315055739998129279961827115008, 316216308784959323969545043968, 8, false, 250286237⟩ (CTN.node (CTN.node CTN.nil ⟨315055739998129279961827115008, 316603165047236005305451020288, 8, false, 158518332⟩ CTN.nil) ⟨315055739998129279961827115008, 316912650057057350374175801344, 8, false, 100345615⟩ (CTN.node CTN.nil ⟨315365225007950625030551896064, 316912650057057350374175801344, 8, false, 100512239⟩ CTN.nil)))) ⟨315442596260405961297733091328, 316216308784959323969545043968, 8, false, 250833039⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨315442596260405961297733091328, 316603165047236005305451020288, 8, false, 158853696⟩ CTN.nil) ⟨315442596260405961297733091328, 316815935991488180040199307264, 8, false, 117320305⟩ (CTN.node CTN.nil ⟨315442596260405961297733091328, 316912650057057350374175801344, 8, false, 100549186⟩ CTN.nil)) ⟨315790766896454974500048470016, 316912650057057350374175801344, 8, false, 100692086⟩ (CTN.node (CTN.node CTN.nil ⟨315829452522682642633639067648, 316603165047236005305451020288, 8, false, 159129764⟩ CTN.nil) ⟨315829452522682642633639067648, 316912650057057350374175801344, 8, false, 100705601⟩ (CTN.node CTN.nil ⟨315868138148910310767229665280, 316912650057057350374175801344, 8, false, 100718643⟩ CTN.nil))) ⟨316042223466934817368387354624, 316912650057057350374175801344, 8, false, 100771475⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨316216308784959323969545043968, 316912650057057350374175801344, 8, false, 100814714⟩ CTN.nil) ⟨316603165047236005305451020288, 316912650057057350374175801344, 8, false, 100876421⟩ (CTN.node CTN.nil ⟨316641850673463673439041617920, 316912650057057350374175801344, 8, false, 100879982⟩ CTN.nil)) ⟨316796593178374345973404008448, 316912650057057350374175801344, 8, false, 100889478⟩ (CTN.node (CTN.node CTN.nil ⟨316815935991488180040199307264, 316912650057057350374175801344, 8, false, 100890131⟩ CTN.nil) ⟨316912650057057350374175801344, 316990021309512686641356996608, 8, true, 88337112⟩ (CTN.node CTN.nil ⟨316912650057057350374175801344, 317067392561968022908538191872, 8, true, 76620491⟩ CTN.nil)))))

def tab14 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨316912650057057350374175801344, 317202792253764861376105283584, 8, true, 58130146⟩ CTN.nil) ⟨316912650057057350374175801344, 317376877571789367977262972928, 8, true, 38116466⟩ (CTN.node CTN.nil ⟨316912650057057350374175801344, 317415563198017036110853570560, 8, true, 34242453⟩ CTN.nil)) ⟨316912650057057350374175801344, 317589648516041542712011259904, 8, true, 19385182⟩ (CTN.node (CTN.node CTN.nil ⟨316912650057057350374175801344, 317628334142269210845601857536, 8, true, 16655234⟩ CTN.nil) ⟨316912650057057350374175801344, 317763733834066049313168949248, 8, true, 8734460⟩ (CTN.node CTN.nil ⟨316912650057057350374175801344, 317802419460293717446759546880, 8, true, 6937709⟩ CTN.nil))) ⟨316912650057057350374175801344, 317841105086521385580350144512, 8, true, 5347966⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨316912650057057350374175801344, 318015190404545892181507833856, 8, true, 752127⟩ CTN.nil) ⟨316912650057057350374175801344, 318111904470115062515484327936, 8, true, 4221⟩ (CTN.node CTN.nil ⟨316990021309512686641356996608, 317376877571789367977262972928, 8, true, 38116466⟩ CTN.nil)) ⟨316990021309512686641356996608, 317570305702927708645215961088, 8, true, 20828048⟩ (CTN.node (CTN.node CTN.nil ⟨316990021309512686641356996608, 317763733834066049313168949248, 8, true, 8734460⟩ CTN.nil) ⟨316990021309512686641356996608, 317976504778318224047917236224, 8, true, 1412060⟩ (CTN.node CTN.nil ⟨317028706935740354774947594240, 318015190404545892181507833856, 8, true, 752127⟩ CTN.nil)))) ⟨317183449440651027309309984768, 317570305702927708645215961088, 8, true, 20828048⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨317183449440651027309309984768, 317763733834066049313168949248, 8, true, 8734460⟩ CTN.nil) ⟨317202792253764861376105283584, 317889462119305970747338391552, 8, true, 3651685⟩ (CTN.node CTN.nil ⟨317376877571789367977262972928, 317763733834066049313168949248, 8, true, 8734460⟩ CTN.nil)) ⟨317376877571789367977262972928, 317957161965204389981121937408, 8, true, 1819408⟩ (CTN.node (CTN.node CTN.nil ⟨317415563198017036110853570560, 318102233063558145482086678528, 8, true, 21076⟩ CTN.nil) ⟨317570305702927708645215961088, 317957161965204389981121937408, 8, true, 1819408⟩ (CTN.node CTN.nil ⟨318150590096342730649074925568, 318924302620896093320886878208, 8, true, 64801⟩ CTN.nil))) ⟨318150590096342730649074925568, 319311158883172774656792854528, 8, true, 64486⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨318150590096342730649074925568, 319698015145449455992698830848, 8, true, 64174⟩ CTN.nil) ⟨318150590096342730649074925568, 320471727670002818664510783488, 8, true, 63554⟩ (CTN.node CTN.nil ⟨318150590096342730649074925568, 321245440194556181336322736128, 8, true, 62942⟩ CTN.nil)) ⟨318150590096342730649074925568, 322019152719109544008134688768, 8, true, 62338⟩ (CTN.node (CTN.node CTN.nil ⟨318150590096342730649074925568, 322792865243662906679946641408, 8, true, 61740⟩ CTN.nil) ⟨318150590096342730649074925568, 324340290292769632023570546688, 8, true, 60567⟩ (CTN.node CTN.nil ⟨318150590096342730649074925568, 325887715341876357367194451968, 8, true, 59421⟩ CTN.nil)))))

def tab15 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨318150590096342730649074925568, 330529990489196533398066167808, 8, true, 56143⟩ CTN.nil) ⟨318150590096342730649074925568, 336719690685623434772561788928, 8, true, 52116⟩ (CTN.node CTN.nil ⟨318189275722570398782665523200, 318875945588111508153898631168, 8, true, 329490⟩ CTN.nil)) ⟨318189275722570398782665523200, 319175759191375936189225762816, 8, true, 328250⟩ (CTN.node (CTN.node CTN.nil ⟨318189275722570398782665523200, 319562615453652617525131739136, 8, true, 326658⟩ CTN.nil) ⟨318189275722570398782665523200, 320162242660181473595786002432, 8, true, 324210⟩ (CTN.node CTN.nil ⟨318227961348798066916256120832, 319214444817603604322816360448, 8, true, 794884⟩ CTN.nil))) ⟨318266646975025735049846718464, 320239613912636809862967197696, 8, true, 1446360⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨318266646975025735049846718464, 321013326437190172534779150336, 8, true, 1432423⟩ CTN.nil) ⟨318315004007810320216834965504, 319001673873351429588068073472, 8, true, 2596042⟩ (CTN.node CTN.nil ⟨318363361040594905383823212544, 319736700771677124126289428480, 8, true, 4005086⟩ CTN.nil)) ⟨318402046666822573517413810176, 319088716532363682888646918144, 8, true, 5423250⟩ (CTN.node (CTN.node CTN.nil ⟨318402046666822573517413810176, 319388530135628110923974049792, 8, true, 5402852⟩ CTN.nil) ⟨318440732293050241651004407808, 319814072024132460393470623744, 8, true, 6949428⟩ (CTN.node CTN.nil ⟨318460075106164075717799706624, 326351942856608374970281623552, 8, true, 7203785⟩ CTN.nil)))) ⟨318489089325834826817992654848, 319175759191375936189225762816, 8, true, 9277676⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨318537446358619411984980901888, 319311158883172774656792854528, 8, true, 11849221⟩ CTN.nil) ⟨318537446358619411984980901888, 319698015145449455992698830848, 8, true, 11791793⟩ (CTN.node CTN.nil ⟨318537446358619411984980901888, 320510413296230486798101381120, 8, true, 11672323⟩ CTN.nil)) ⟨318576131984847080118571499520, 319562615453652617525131739136, 8, true, 14104212⟩ (CTN.node (CTN.node CTN.nil ⟨318614817611074748252162097152, 319601301079880285658722336768, 8, true, 16592229⟩ CTN.nil) ⟨318614817611074748252162097152, 319988157342156966994628313088, 8, true, 16511887⟩ (CTN.node CTN.nil ⟨318614817611074748252162097152, 320587784548685823065282576384, 8, true, 16388316⟩ CTN.nil))) ⟨318614817611074748252162097152, 321361497073239185737094529024, 8, true, 16230574⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨318614817611074748252162097152, 322560751486296897878403055616, 8, true, 15989808⟩ CTN.nil) ⟨318701860270087001552740941824, 319388530135628110923974049792, 8, true, 23012206⟩ (CTN.node CTN.nil ⟨318769560115985420786524487680, 326661427866429720039006404608, 8, true, 26208942⟩ CTN.nil)) ⟨318769560115985420786524487680, 329756277964643170726254215168, 8, true, 25235977⟩ (CTN.node (CTN.node CTN.nil ⟨318769560115985420786524487680, 334553295616874019291488321536, 8, true, 23815441⟩ CTN.nil) ⟨318769560115985420786524487680, 336719690685623434772561788928, 8, true, 23206737⟩ (CTN.node CTN.nil ⟨318788902929099254853319786496, 319775386397904792259880026112, 8, true, 30275949⟩ CTN.nil)))))

def tab16 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨318924302620896093320886878208, 319698015145449455992698830848, 8, true, 43842579⟩ CTN.nil) ⟨318924302620896093320886878208, 320471727670002818664510783488, 8, true, 43419407⟩ (CTN.node CTN.nil ⟨318924302620896093320886878208, 321245440194556181336322736128, 8, true, 43001332⟩ CTN.nil)) ⟨318924302620896093320886878208, 322019152719109544008134688768, 8, true, 42588280⟩ (CTN.node (CTN.node CTN.nil ⟨318962988247123761454477475840, 320935955184734836267597955072, 8, true, 47428865⟩ CTN.nil) ⟨318962988247123761454477475840, 321709667709288198939409907712, 8, true, 46972844⟩ (CTN.node CTN.nil ⟨319001673873351429588068073472, 319988157342156966994628313088, 8, true, 52510613⟩ CTN.nil))) ⟨319040359499579097721658671104, 321013326437190172534779150336, 8, true, 56500224⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨319175759191375936189225762816, 320162242660181473595786002432, 8, true, 75190749⟩ CTN.nil) ⟨319214444817603604322816360448, 320200928286409141729376600064, 8, true, 80777393⟩ (CTN.node CTN.nil ⟨319214444817603604322816360448, 320587784548685823065282576384, 8, true, 80386992⟩ CTN.nil)) ⟨319311158883172774656792854528, 320084871407726137328604807168, 8, true, 95866578⟩ (CTN.node (CTN.node CTN.nil ⟨319311158883172774656792854528, 320471727670002818664510783488, 8, true, 95403082⟩ CTN.nil) ⟨319311158883172774656792854528, 323257092758394924283033812992, 8, true, 92147329⟩ (CTN.node CTN.nil ⟨319388530135628110923974049792, 320761869866710329666440265728, 8, true, 107845387⟩ CTN.nil)))) ⟨319388530135628110923974049792, 321361497073239185737094529024, 8, true, 107040250⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨319465901388083447191155245056, 323411835263305596817396203520, 8, true, 117501198⟩ CTN.nil) ⟨319465901388083447191155245056, 324959260312412322161020108800, 8, true, 115272336⟩ (CTN.node CTN.nil ⟨319601301079880285658722336768, 320587784548685823065282576384, 8, true, 147518932⟩ CTN.nil)) ⟨319698015145449455992698830848, 321245440194556181336322736128, 8, true, 166110220⟩ (CTN.node (CTN.node CTN.nil ⟨319698015145449455992698830848, 321632296456832862672228712448, 8, true, 165310021⟩ CTN.nil) ⟨319698015145449455992698830848, 322019152719109544008134688768, 8, true, 164514637⟩ (CTN.node CTN.nil ⟨319698015145449455992698830848, 322792865243662906679946641408, 8, true, 162938178⟩ CTN.nil))) ⟨319698015145449455992698830848, 323566577768216269351758594048, 8, true, 161380568⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨319698015145449455992698830848, 324340290292769632023570546688, 8, true, 159841537⟩ CTN.nil) ⟨319698015145449455992698830848, 325887715341876357367194451968, 8, true, 156818156⟩ (CTN.node CTN.nil ⟨319698015145449455992698830848, 327435140390983082710818357248, 8, true, 153865963⟩ CTN.nil)) ⟨319736700771677124126289428480, 321709667709288198939409907712, 8, true, 173376282⟩ (CTN.node (CTN.node CTN.nil ⟨319814072024132460393470623744, 321787038961743535206591102976, 8, true, 190247446⟩ CTN.nil) ⟨319814072024132460393470623744, 322560751486296897878403055616, 8, true, 188423087⟩ (CTN.node CTN.nil ⟨319988157342156966994628313088, 321361497073239185737094529024, 8, true, 232757136⟩ CTN.nil)))))

def tab17 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨320084871407726137328604807168, 321632296456832862672228712448, 8, true, 256712194⟩ CTN.nil) ⟨320084871407726137328604807168, 322019152719109544008134688768, 8, true, 255477031⟩ (CTN.node CTN.nil ⟨320162242660181473595786002432, 324108176535403623222026960896, 8, true, 269007246⟩ CTN.nil)) ⟨320162242660181473595786002432, 325655601584510348565650866176, 8, true, 263915387⟩ (CTN.node (CTN.node CTN.nil ⟨320162242660181473595786002432, 328054110410625772848267919360, 8, true, 256258884⟩ CTN.nil) ⟨320162242660181473595786002432, 331148960508839223535515729920, 8, true, 246785359⟩ (CTN.node CTN.nil ⟨320471727670002818664510783488, 321438868325694522004275724288, 8, true, 369182634⟩ CTN.nil))) ⟨320471727670002818664510783488, 321632296456832862672228712448, 8, true, 368292602⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨320471727670002818664510783488, 322019152719109544008134688768, 8, true, 366520574⟩ CTN.nil) ⟨320471727670002818664510783488, 322406008981386225344040665088, 8, true, 364759198⟩ (CTN.node CTN.nil ⟨320471727670002818664510783488, 322792865243662906679946641408, 8, true, 363008396⟩ CTN.nil)) ⟨320471727670002818664510783488, 323566577768216269351758594048, 8, true, 359538212⟩ (CTN.node (CTN.node CTN.nil ⟨320471727670002818664510783488, 324340290292769632023570546688, 8, true, 356109420⟩ CTN.nil) ⟨320587784548685823065282576384, 322560751486296897878403055616, 8, true, 401042374⟩ (CTN.node CTN.nil ⟨320665155801141159332463771648, 321632296456832862672228712448, 8, true, 431662129⟩ CTN.nil)))) ⟨320858583932279500000416759808, 321632296456832862672228712448, 8, true, 500088775⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨320858583932279500000416759808, 321825724587971203340181700608, 8, true, 498883881⟩ CTN.nil) ⟨320858583932279500000416759808, 322019152719109544008134688768, 8, true, 497682615⟩ (CTN.node CTN.nil ⟨320858583932279500000416759808, 322406008981386225344040665088, 8, true, 495290917⟩ CTN.nil)) ⟨321013326437190172534779150336, 324959260312412322161020108800, 8, true, 535883118⟩ (CTN.node (CTN.node CTN.nil ⟨321052012063417840668369747968, 321825724587971203340181700608, 8, true, 572192259⟩ CTN.nil) ⟨321052012063417840668369747968, 322019152719109544008134688768, 8, true, 570814473⟩ (CTN.node CTN.nil ⟨321245440194556181336322736128, 321825724587971203340181700608, 8, true, 650547676⟩ CTN.nil))) ⟨321245440194556181336322736128, 322019152719109544008134688768, 8, true, 648981217⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨321245440194556181336322736128, 322212580850247884676087676928, 8, true, 647419474⟩ CTN.nil) ⟨321245440194556181336322736128, 322406008981386225344040665088, 8, true, 645862429⟩ (CTN.node CTN.nil ⟨321245440194556181336322736128, 322792865243662906679946641408, 8, true, 642762364⟩ CTN.nil)) ⟨321245440194556181336322736128, 323179721505939588015852617728, 8, true, 639680888⟩ (CTN.node (CTN.node CTN.nil ⟨321245440194556181336322736128, 323566577768216269351758594048, 8, true, 636617867⟩ CTN.nil) ⟨321245440194556181336322736128, 324340290292769632023570546688, 8, true, 630546662⟩ (CTN.node CTN.nil ⟨321245440194556181336322736128, 325114002817322994695382499328, 8, true, 624547701⟩ CTN.nil)))))

def tab18 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨321245440194556181336322736128, 327435140390983082710818357248, 8, true, 606974075⟩ CTN.nil) ⟨321245440194556181336322736128, 328982565440089808054442262528, 8, true, 595601118⟩ (CTN.node CTN.nil ⟨321245440194556181336322736128, 330529990489196533398066167808, 8, true, 584493440⟩ CTN.nil)) ⟨321245440194556181336322736128, 333624840587409984085313978368, 8, true, 563044583⟩ (CTN.node (CTN.node CTN.nil ⟨321245440194556181336322736128, 336719690685623434772561788928, 8, true, 542571166⟩ CTN.nil) ⟨321438868325694522004275724288, 322019152719109544008134688768, 8, true, 732182076⟩ (CTN.node CTN.nil ⟨321438868325694522004275724288, 322212580850247884676087676928, 8, true, 730420113⟩ CTN.nil))) ⟨321632296456832862672228712448, 322115866784678714342111182848, 8, true, 819427170⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨321632296456832862672228712448, 322212580850247884676087676928, 8, true, 818440768⟩ CTN.nil) ⟨321632296456832862672228712448, 322406008981386225344040665088, 8, true, 816472416⟩ (CTN.node CTN.nil ⟨321632296456832862672228712448, 322599437112524566011993653248, 8, true, 814509982⟩ CTN.nil)) ⟨321632296456832862672228712448, 322792865243662906679946641408, 8, true, 812553443⟩ (CTN.node (CTN.node CTN.nil ⟨321632296456832862672228712448, 323179721505939588015852617728, 8, true, 808657969⟩ CTN.nil) ⟨321632296456832862672228712448, 323566577768216269351758594048, 8, true, 804785826⟩ (CTN.node CTN.nil ⟨321709667709288198939409907712, 325655601584510348565650866176, 8, true, 819356975⟩ CTN.nil)))) ⟨321729010522402033006205206528, 322115866784678714342111182848, 8, true, 865374359⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨321729010522402033006205206528, 322212580850247884676087676928, 8, true, 864332647⟩ CTN.nil) ⟨321825724587971203340181700608, 322212580850247884676087676928, 8, true, 911478236⟩ (CTN.node CTN.nil ⟨321825724587971203340181700608, 322309294915817055010064171008, 8, true, 910381357⟩ CTN.nil)) ⟨321825724587971203340181700608, 322406008981386225344040665088, 8, true, 909286128⟩ (CTN.node (CTN.node CTN.nil ⟨321825724587971203340181700608, 322599437112524566011993653248, 8, true, 907100611⟩ CTN.nil) ⟨321825724587971203340181700608, 322792865243662906679946641408, 8, true, 904921660⟩ (CTN.node CTN.nil ⟨321864410214198871473772298240, 329756277964643170726254215168, 8, true, 848165913⟩ CTN.nil))) ⟨321922438653540373674158194688, 322212580850247884676087676928, 8, true, 959876941⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨321922438653540373674158194688, 322309294915817055010064171008, 8, true, 958721819⟩ CTN.nil) ⟨321922438653540373674158194688, 322406008981386225344040665088, 8, true, 957568435⟩ (CTN.node CTN.nil ⟨322019152719109544008134688768, 322309294915817055010064171008, 8, true, 1008313224⟩ CTN.nil)) ⟨322019152719109544008134688768, 322406008981386225344040665088, 8, true, 1007100179⟩ (CTN.node (CTN.node CTN.nil ⟨322019152719109544008134688768, 322502723046955395678017159168, 8, true, 1005888959⟩ CTN.nil) ⟨322019152719109544008134688768, 322599437112524566011993653248, 8, true, 1004679561⟩ (CTN.node CTN.nil ⟨322019152719109544008134688768, 322792865243662906679946641408, 8, true, 1002266215⟩ CTN.nil)))))

def tab19 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322019152719109544008134688768, 323179721505939588015852617728, 8, true, 997461236⟩ CTN.nil) ⟨322019152719109544008134688768, 323566577768216269351758594048, 8, true, 992685035⟩ (CTN.node CTN.nil ⟨322019152719109544008134688768, 323953434030492950687664570368, 8, true, 987937405⟩ CTN.nil)) ⟨322019152719109544008134688768, 324340290292769632023570546688, 8, true, 983218140⟩ (CTN.node (CTN.node CTN.nil ⟨322019152719109544008134688768, 325114002817322994695382499328, 8, true, 973863897⟩ CTN.nil) ⟨322019152719109544008134688768, 325887715341876357367194451968, 8, true, 964620700⟩ (CTN.node CTN.nil ⟨322115866784678714342111182848, 322406008981386225344040665088, 8, true, 1057880619⟩ CTN.nil))) ⟨322115866784678714342111182848, 322502723046955395678017159168, 8, true, 1056608326⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322115866784678714342111182848, 322599437112524566011993653248, 8, true, 1055337947⟩ CTN.nil) ⟨322212580850247884676087676928, 322454366014170810511028912128, 8, true, 1109241254⟩ (CTN.node CTN.nil ⟨322212580850247884676087676928, 322502723046955395678017159168, 8, true, 1108574073⟩ CTN.nil)) ⟨322212580850247884676087676928, 322599437112524566011993653248, 8, true, 1107241214⟩ (CTN.node (CTN.node CTN.nil ⟨322212580850247884676087676928, 322696151178093736345970147328, 8, true, 1105910359⟩ CTN.nil) ⟨322212580850247884676087676928, 322792865243662906679946641408, 8, true, 1104581504⟩ (CTN.node CTN.nil ⟨322212580850247884676087676928, 322986293374801247347899629568, 8, true, 1101929780⟩ CTN.nil)))) ⟨322212580850247884676087676928, 323179721505939588015852617728, 8, true, 1099286014⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322260937883032469843075923968, 322502723046955395678017159168, 8, true, 1135024061⟩ CTN.nil) ⟨322309294915817055010064171008, 322551080079739980845005406208, 8, true, 1161086624⟩ (CTN.node CTN.nil ⟨322309294915817055010064171008, 322599437112524566011993653248, 8, true, 1160388468⟩ CTN.nil)) ⟨322309294915817055010064171008, 322696151178093736345970147328, 8, true, 1158993733⟩ (CTN.node (CTN.node CTN.nil ⟨322309294915817055010064171008, 322792865243662906679946641408, 8, true, 1157601093⟩ CTN.nil) ⟨322357651948601640177052418048, 322599437112524566011993653248, 8, true, 1187428290⟩ (CTN.node CTN.nil ⟨322406008981386225344040665088, 322647794145309151178981900288, 8, true, 1214048412⟩ CTN.nil))) ⟨322406008981386225344040665088, 322696151178093736345970147328, 8, true, 1213318631⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322406008981386225344040665088, 322792865243662906679946641408, 8, true, 1211860715⟩ CTN.nil) ⟨322406008981386225344040665088, 322889579309232077013923135488, 8, true, 1210404990⟩ (CTN.node CTN.nil ⟨322406008981386225344040665088, 322986293374801247347899629568, 8, true, 1208951451⟩ CTN.nil)) ⟨322406008981386225344040665088, 323179721505939588015852617728, 8, true, 1206050917⟩ (CTN.node (CTN.node CTN.nil ⟨322406008981386225344040665088, 323373149637077928683805605888, 8, true, 1203159081⟩ CTN.nil) ⟨322406008981386225344040665088, 323566577768216269351758594048, 8, true, 1200275914⟩ (CTN.node CTN.nil ⟨322406008981386225344040665088, 323953434030492950687664570368, 8, true, 1194535456⟩ CTN.nil)))))

def tab20 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322454366014170810511028912128, 322647794145309151178981900288, 8, true, 1241692728⟩ CTN.nil) ⟨322454366014170810511028912128, 322696151178093736345970147328, 8, true, 1240946330⟩ (CTN.node CTN.nil ⟨322502723046955395678017159168, 322696151178093736345970147328, 8, true, 1268884014⟩ CTN.nil)) ⟨322502723046955395678017159168, 322744508210878321512958394368, 8, true, 1268121386⟩ (CTN.node (CTN.node CTN.nil ⟨322502723046955395678017159168, 322792865243662906679946641408, 8, true, 1267359331⟩ CTN.nil) ⟨322502723046955395678017159168, 322889579309232077013923135488, 8, true, 1265836939⟩ (CTN.node CTN.nil ⟨322502723046955395678017159168, 322986293374801247347899629568, 8, true, 1264316833⟩ CTN.nil))) ⟨322551080079739980845005406208, 322744508210878321512958394368, 8, true, 1296351934⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322551080079739980845005406208, 322792865243662906679946641408, 8, true, 1295572914⟩ CTN.nil) ⟨322560751486296897878403055616, 328054110410625772848267919360, 8, true, 1219525351⟩ (CTN.node CTN.nil ⟨322599437112524566011993653248, 322792865243662906679946641408, 8, true, 1324095821⟩ CTN.nil)) ⟨322599437112524566011993653248, 322841222276447491846934888448, 8, true, 1323300249⟩ (CTN.node (CTN.node CTN.nil ⟨322599437112524566011993653248, 322889579309232077013923135488, 8, true, 1322505275⟩ CTN.nil) ⟨322599437112524566011993653248, 322986293374801247347899629568, 8, true, 1320917118⟩ (CTN.node CTN.nil ⟨322599437112524566011993653248, 323083007440370417681876123648, 8, true, 1319331346⟩ CTN.nil)))) ⟨322599437112524566011993653248, 323179721505939588015852617728, 8, true, 1317747955⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322599437112524566011993653248, 323373149637077928683805605888, 8, true, 1314588295⟩ CTN.nil) ⟨322599437112524566011993653248, 323566577768216269351758594048, 8, true, 1311438106⟩ (CTN.node CTN.nil ⟨322647794145309151178981900288, 322841222276447491846934888448, 8, true, 1352115004⟩ CTN.nil)) ⟨322647794145309151178981900288, 322889579309232077013923135488, 8, true, 1351302719⟩ (CTN.node (CTN.node CTN.nil ⟨322696151178093736345970147328, 322889579309232077013923135488, 8, true, 1380408806⟩ CTN.nil) ⟨322696151178093736345970147328, 322937936342016662180911382528, 8, true, 1379579649⟩ (CTN.node CTN.nil ⟨322696151178093736345970147328, 322986293374801247347899629568, 8, true, 1378751115⟩ CTN.nil))) ⟨322696151178093736345970147328, 323083007440370417681876123648, 8, true, 1377095912⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322696151178093736345970147328, 323179721505939588015852617728, 8, true, 1375443195⟩ CTN.nil) ⟨322744508210878321512958394368, 322937936342016662180911382528, 8, true, 1408976552⟩ (CTN.node CTN.nil ⟨322744508210878321512958394368, 322986293374801247347899629568, 8, true, 1408130363⟩ CTN.nil)) ⟨322792865243662906679946641408, 322986293374801247347899629568, 8, true, 1437817558⟩ (CTN.node (CTN.node CTN.nil ⟨322792865243662906679946641408, 323034650407585832514887876608, 8, true, 1436954178⟩ CTN.nil) ⟨322792865243662906679946641408, 323083007440370417681876123648, 8, true, 1436091446⟩ (CTN.node CTN.nil ⟨322792865243662906679946641408, 323179721505939588015852617728, 8, true, 1434367925⟩ CTN.nil)))))

def tab21 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322792865243662906679946641408, 323373149637077928683805605888, 8, true, 1430928638⟩ CTN.nil) ⟨322792865243662906679946641408, 323566577768216269351758594048, 8, true, 1427499659⟩ (CTN.node CTN.nil ⟨322792865243662906679946641408, 323760005899354610019711582208, 8, true, 1424080951⟩ CTN.nil)) ⟨322792865243662906679946641408, 323953434030492950687664570368, 8, true, 1420672477⟩ (CTN.node (CTN.node CTN.nil ⟨322792865243662906679946641408, 324340290292769632023570546688, 8, true, 1413886087⟩ CTN.nil) ⟨322792865243662906679946641408, 324727146555046313359476523008, 8, true, 1407140194⟩ (CTN.node CTN.nil ⟨322792865243662906679946641408, 325114002817322994695382499328, 8, true, 1400434510⟩ CTN.nil))) ⟨322792865243662906679946641408, 325887715341876357367194451968, 8, true, 1387142620⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322792865243662906679946641408, 326661427866429720039006404608, 8, true, 1374008145⟩ CTN.nil) ⟨322792865243662906679946641408, 327435140390983082710818357248, 8, true, 1361028853⟩ (CTN.node CTN.nil ⟨322792865243662906679946641408, 328982565440089808054442262528, 8, true, 1335527067⟩ CTN.nil)) ⟨322792865243662906679946641408, 330529990489196533398066167808, 8, true, 1310620122⟩ (CTN.node (CTN.node CTN.nil ⟨322841222276447491846934888448, 323034650407585832514887876608, 8, true, 1466931139⟩ CTN.nil) ⟨322841222276447491846934888448, 323083007440370417681876123648, 8, true, 1466050409⟩ (CTN.node CTN.nil ⟨322889579309232077013923135488, 323083007440370417681876123648, 8, true, 1496316606⟩ CTN.nil)))) ⟨322889579309232077013923135488, 323131364473155002848864370688, 8, true, 1495418369⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨322889579309232077013923135488, 323179721505939588015852617728, 8, true, 1494520806⟩ CTN.nil) ⟨322889579309232077013923135488, 323276435571508758349829111808, 8, true, 1492727701⟩ (CTN.node CTN.nil ⟨322889579309232077013923135488, 323373149637077928683805605888, 8, true, 1490937285⟩ CTN.nil)) ⟨322937936342016662180911382528, 323131364473155002848864370688, 8, true, 1525973265⟩ (CTN.node (CTN.node CTN.nil ⟨322937936342016662180911382528, 323179721505939588015852617728, 8, true, 1525057363⟩ CTN.nil) ⟨322986293374801247347899629568, 323179721505939588015852617728, 8, true, 1555900420⟩ (CTN.node CTN.nil ⟨322986293374801247347899629568, 323228078538724173182840864768, 8, true, 1554966696⟩ CTN.nil))) ⟨322986293374801247347899629568, 323276435571508758349829111808, 8, true, 1554033673⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨322986293374801247347899629568, 323373149637077928683805605888, 8, true, 1552169725⟩ CTN.nil) ⟨322986293374801247347899629568, 323469863702647099017782099968, 8, true, 1550308574⟩ (CTN.node CTN.nil ⟨322986293374801247347899629568, 323566577768216269351758594048, 8, true, 1548450213⟩ CTN.nil)) ⟨322986293374801247347899629568, 323760005899354610019711582208, 8, true, 1544741841⟩ (CTN.node (CTN.node CTN.nil ⟨322986293374801247347899629568, 323953434030492950687664570368, 8, true, 1541044571⟩ CTN.nil) ⟨323034650407585832514887876608, 323228078538724173182840864768, 8, true, 1586097374⟩ (CTN.node CTN.nil ⟨323034650407585832514887876608, 323276435571508758349829111808, 8, true, 1585145671⟩ CTN.nil)))))

def tab22 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨323083007440370417681876123648, 323373149637077928683805605888, 8, true, 1614624474⟩ CTN.nil) ⟨323083007440370417681876123648, 323469863702647099017782099968, 8, true, 1612688435⟩ (CTN.node CTN.nil ⟨323083007440370417681876123648, 323566577768216269351758594048, 8, true, 1610755299⟩ CTN.nil)) ⟨323131364473155002848864370688, 323373149637077928683805605888, 8, true, 1646309728⟩ (CTN.node (CTN.node CTN.nil ⟨323179721505939588015852617728, 323421506669862513850793852928, 8, true, 1677293395⟩ CTN.nil) ⟨323179721505939588015852617728, 323469863702647099017782099968, 8, true, 1676287578⟩ (CTN.node CTN.nil ⟨323179721505939588015852617728, 323566577768216269351758594048, 8, true, 1674278205⟩ CTN.nil))) ⟨323179721505939588015852617728, 323663291833785439685735088128, 8, true, 1672271844⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨323179721505939588015852617728, 323760005899354610019711582208, 8, true, 1670268489⟩ CTN.nil) ⟨323179721505939588015852617728, 323953434030492950687664570368, 8, true, 1666270777⟩ (CTN.node CTN.nil ⟨323179721505939588015852617728, 324146862161631291355617558528, 8, true, 1662285025⟩ CTN.nil)) ⟨323179721505939588015852617728, 324340290292769632023570546688, 8, true, 1658311191⟩ (CTN.node (CTN.node CTN.nil ⟨323179721505939588015852617728, 324727146555046313359476523008, 8, true, 1650399104⟩ CTN.nil) ⟨323179721505939588015852617728, 325114002817322994695382499328, 8, true, 1642534177⟩ (CTN.node CTN.nil ⟨323228078538724173182840864768, 323469863702647099017782099968, 8, true, 1708543871⟩ CTN.nil)))) ⟨323257092758394924283033812992, 331148960508839223535515729920, 8, true, 1572805651⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨323276435571508758349829111808, 323566577768216269351758594048, 8, true, 1739017297⟩ CTN.nil) ⟨323276435571508758349829111808, 323663291833785439685735088128, 8, true, 1736933356⟩ (CTN.node CTN.nil ⟨323276435571508758349829111808, 323760005899354610019711582208, 8, true, 1734852538⟩ CTN.nil)) ⟨323373149637077928683805605888, 323663291833785439685735088128, 8, true, 1802807888⟩ (CTN.node (CTN.node CTN.nil ⟨323373149637077928683805605888, 323760005899354610019711582208, 8, true, 1800648153⟩ CTN.nil) ⟨323373149637077928683805605888, 323856719964923780353688076288, 8, true, 1798491653⟩ (CTN.node CTN.nil ⟨323373149637077928683805605888, 323953434030492950687664570368, 8, true, 1796338383⟩ CTN.nil))) ⟨323373149637077928683805605888, 324146862161631291355617558528, 8, true, 1792041507⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨323373149637077928683805605888, 324340290292769632023570546688, 8, true, 1787757479⟩ CTN.nil) ⟨323469863702647099017782099968, 323760005899354610019711582208, 8, true, 1867653558⟩ (CTN.node CTN.nil ⟨323469863702647099017782099968, 323856719964923780353688076288, 8, true, 1865416811⟩ CTN.nil)) ⟨323469863702647099017782099968, 323953434030492950687664570368, 8, true, 1863183413⟩ (CTN.node (CTN.node CTN.nil ⟨323566577768216269351758594048, 323953434030492950687664570368, 8, true, 1931233486⟩ CTN.nil) ⟨323566577768216269351758594048, 324050148096062121021641064448, 8, true, 1928921982⟩ (CTN.node CTN.nil ⟨323566577768216269351758594048, 324146862161631291355617558528, 8, true, 1926613938⟩ CTN.nil)))))

def tab23 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨323566577768216269351758594048, 324533718423907972691523534848, 8, true, 1917416231⟩ CTN.nil) ⟨323566577768216269351758594048, 324727146555046313359476523008, 8, true, 1912837973⟩ (CTN.node CTN.nil ⟨323566577768216269351758594048, 325114002817322994695382499328, 8, true, 1903722402⟩ CTN.nil)) ⟨323566577768216269351758594048, 325500859079599676031288475648, 8, true, 1894661098⟩ (CTN.node (CTN.node CTN.nil ⟨323566577768216269351758594048, 325887715341876357367194451968, 8, true, 1885653674⟩ CTN.nil) ⟨323566577768216269351758594048, 326661427866429720039006404608, 8, true, 1867798934⟩ (CTN.node CTN.nil ⟨323566577768216269351758594048, 327435140390983082710818357248, 8, true, 1850155147⟩ CTN.nil))) ⟨323566577768216269351758594048, 334553295616874019291488321536, 8, true, 1697224391⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨323663291833785439685735088128, 324050148096062121021641064448, 8, true, 1998092280⟩ CTN.nil) ⟨323663291833785439685735088128, 324146862161631291355617558528, 8, true, 1995701471⟩ (CTN.node CTN.nil ⟨323760005899354610019711582208, 324340290292769632023570546688, 8, true, 2061048329⟩ CTN.nil)) ⟨323760005899354610019711582208, 324533718423907972691523534848, 8, true, 2056124169⟩ (CTN.node (CTN.node CTN.nil ⟨323760005899354610019711582208, 324727146555046313359476523008, 8, true, 2051214715⟩ CTN.nil) ⟨323953434030492950687664570368, 324533718423907972691523534848, 8, true, 2199593882⟩ (CTN.node CTN.nil ⟨323953434030492950687664570368, 324727146555046313359476523008, 8, true, 2194341861⟩ CTN.nil)))) ⟨323953434030492950687664570368, 324920574686184654027429511168, 8, true, 2189105517⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨323953434030492950687664570368, 325114002817322994695382499328, 8, true, 2183884792⟩ CTN.nil) ⟨323953434030492950687664570368, 325500859079599676031288475648, 8, true, 2173489976⟩ (CTN.node CTN.nil ⟨323953434030492950687664570368, 325887715341876357367194451968, 8, true, 2163156970⟩ CTN.nil)) ⟨324146862161631291355617558528, 324920574686184654027429511168, 8, true, 2336612903⟩ (CTN.node (CTN.node CTN.nil ⟨324146862161631291355617558528, 325114002817322994695382499328, 8, true, 2331040392⟩ CTN.nil) ⟨324340290292769632023570546688, 325500859079599676031288475648, 8, true, 2471070080⟩ (CTN.node CTN.nil ⟨324340290292769632023570546688, 325887715341876357367194451968, 8, true, 2459322346⟩ CTN.nil))) ⟨324340290292769632023570546688, 326274571604153038703100428288, 8, true, 2447644383⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨324340290292769632023570546688, 326661427866429720039006404608, 8, true, 2436035694⟩ CTN.nil) ⟨324340290292769632023570546688, 327435140390983082710818357248, 8, true, 2413024171⟩ (CTN.node CTN.nil ⟨324340290292769632023570546688, 328982565440089808054442262528, 8, true, 2367811004⟩ CTN.nil)) ⟨324340290292769632023570546688, 330529990489196533398066167808, 8, true, 2323652454⟩ (CTN.node (CTN.node CTN.nil ⟨324340290292769632023570546688, 332077415538303258741690073088, 8, true, 2280519125⟩ CTN.nil) ⟨324340290292769632023570546688, 333624840587409984085313978368, 8, true, 2238382569⟩ (CTN.node CTN.nil ⟨324340290292769632023570546688, 336719690685623434772561788928, 8, true, 2156990541⟩ CTN.nil)))))

def tab24 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨324727146555046313359476523008, 326661427866429720039006404608, 8, true, 2747732905⟩ CTN.nil) ⟨324959260312412322161020108800, 336719690685623434772561788928, 8, true, 2606310863⟩ (CTN.node CTN.nil ⟨325114002817322994695382499328, 327435140390983082710818357248, 8, true, 3048526697⟩ CTN.nil)) ⟨325114002817322994695382499328, 328208852915536445382630309888, 8, true, 3019797449⟩ (CTN.node (CTN.node CTN.nil ⟨325114002817322994695382499328, 328982565440089808054442262528, 8, true, 2991406031⟩ CTN.nil) ⟨325887715341876357367194451968, 330529990489196533398066167808, 8, true, 3616177262⟩ (CTN.node CTN.nil ⟨325887715341876357367194451968, 332077415538303258741690073088, 8, true, 3549051145⟩ CTN.nil))) ⟨325887715341876357367194451968, 333624840587409984085313978368, 8, true, 3483476254⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨327435140390983082710818357248, 336719690685623434772561788928, 8, true, 4805029944⟩ CTN.nil) ⟨328363595420447117916992700416, 336719690685623434772561788928, 8, true, 5787071159⟩ (CTN.node CTN.nil ⟨330529990489196533398066167808, 336719690685623434772561788928, 8, true, 8382305677⟩ CTN.nil)) ⟨336719690685623434772561788928, 339814540783836885459809599488, 9, false, 16970875159⟩ (CTN.node (CTN.node CTN.nil ⟨336719690685623434772561788928, 340742995813300920665983942656, 9, false, 16786156578⟩ CTN.nil) ⟨336719690685623434772561788928, 342909390882050336147057410048, 9, false, 16364828489⟩ (CTN.node CTN.nil ⟨336719690685623434772561788928, 349099091078477237521553031168, 9, false, 15231803251⟩ CTN.nil)))) ⟨336719690685623434772561788928, 350337031117762617796452155392, 9, false, 15017096854⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨336719690685623434772561788928, 355288791274904138896048652288, 9, false, 14195205494⟩ CTN.nil) ⟨338886085754372850253635256320, 356526731314189519170947776512, 9, false, 16862475176⟩ (CTN.node CTN.nil ⟨356526731314189519170947776512, 376333771942755603569333764096, 9, true, 13861447354⟩ CTN.nil)) ⟨371382011785614082469737267200, 376333771942755603569333764096, 9, true, 16026017701⟩ (CTN.node (CTN.node CTN.nil ⟨376333771942755603569333764096, 384380382198110575356178071552, 10, false, 6490297652⟩ CTN.nil) ⟨376333771942755603569333764096, 393355447482929582349196722176, 10, false, 498772193⟩ (CTN.node CTN.nil ⟨376333771942755603569333764096, 395134986289402316494364213248, 10, false, 119224940⟩ CTN.nil))) ⟨397301381358151731975437680640, 400048060820316169460370112512, 10, true, 1593414⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨397301381358151731975437680640, 400821773344869532132182065152, 10, true, 1581122⟩ CTN.nil) ⟨397301381358151731975437680640, 402794740282480606945302544384, 10, true, 1550310⟩ (CTN.node CTN.nil ⟨397649551994200745177753059328, 400396231456365182662685491200, 10, true, 12478272⟩ CTN.nil)) ⟨397688237620428413311343656960, 399622518931811819990873538560, 10, true, 14438895⟩ (CTN.node (CTN.node CTN.nil ⟨397688237620428413311343656960, 400009375194088501326779514880, 10, true, 14383008⟩ CTN.nil) ⟨397688237620428413311343656960, 400783087718641863998591467520, 10, true, 14272044⟩ (CTN.node CTN.nil ⟨397688237620428413311343656960, 401556800243195226670403420160, 10, true, 14162149⟩ CTN.nil)))))

def tab25 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨397688237620428413311343656960, 403877937816855314685839278080, 10, true, 13838751⟩ CTN.nil) ⟨397688237620428413311343656960, 405425362865962040029463183360, 10, true, 13628274⟩ (CTN.node CTN.nil ⟨397997722630249758380068438016, 402291827141520921208624775168, 10, true, 33101423⟩ CTN.nil)) ⟨397997722630249758380068438016, 405038506603685358693557207040, 10, true, 32210921⟩ (CTN.node (CTN.node CTN.nil ⟨398075093882705094647249633280, 399622518931811819990873538560, 10, true, 40179364⟩ CTN.nil) ⟨398075093882705094647249633280, 400009375194088501326779514880, 10, true, 40023848⟩ (CTN.node CTN.nil ⟨398075093882705094647249633280, 400222146138340676061527801856, 10, true, 39938635⟩ CTN.nil))) ⟨398075093882705094647249633280, 400821773344869532132182065152, 10, true, 39699707⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨398152465135160430914430828544, 401672857121878231071175213056, 10, true, 45928559⟩ CTN.nil) ⟨398152465135160430914430828544, 402446569646431593742987165696, 10, true, 45575690⟩ (CTN.node CTN.nil ⟨398152465135160430914430828544, 409139182983818180854160556032, 10, true, 42660549⟩ CTN.nil)) ⟨398152465135160430914430828544, 412234033082031631541408366592, 10, true, 41391449⟩ (CTN.node (CTN.node CTN.nil ⟨398423264518754107849565011968, 401169943980918545334497443840, 10, true, 73274888⟩ CTN.nil) ⟨398461950144981775983155609600, 400009375194088501326779514880, 10, true, 78566750⟩ (CTN.node CTN.nil ⟨398461950144981775983155609600, 400396231456365182662685491200, 10, true, 78262948⟩ CTN.nil)))) ⟨398461950144981775983155609600, 400783087718641863998591467520, 10, true, 77960614⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨398461950144981775983155609600, 401556800243195226670403420160, 10, true, 77360314⟩ CTN.nil) ⟨398461950144981775983155609600, 402330512767748589342215372800, 10, true, 76765783⟩ (CTN.node CTN.nil ⟨398500635771209444116746207232, 401247315233373881601678639104, 10, true, 82109019⟩ CTN.nil)) ⟨398500635771209444116746207232, 402021027757927244273490591744, 10, true, 81477507⟩ (CTN.node (CTN.node CTN.nil ⟨398674721089233950717903896576, 400821773344869532132182065152, 10, true, 104426500⟩ CTN.nil) ⟨398848806407258457319061585920, 400009375194088501326779514880, 10, true, 130049736⟩ (CTN.node CTN.nil ⟨398848806407258457319061585920, 400396231456365182662685491200, 10, true, 129546860⟩ CTN.nil))) ⟨398848806407258457319061585920, 400609002400617357397433778176, 10, true, 129271314⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨398848806407258457319061585920, 401595485869422894803994017792, 10, true, 128003319⟩ CTN.nil) ⟨398848806407258457319061585920, 403142910918529620147617923072, 10, true, 126045476⟩ (CTN.node CTN.nil ⟨398848806407258457319061585920, 404342165331587332288926449664, 10, true, 124553850⟩ CTN.nil)) ⟨398926177659713793586242781184, 401672857121878231071175213056, 10, true, 139560919⟩ (CTN.node (CTN.node CTN.nil ⟨399196977043307470521376964608, 401943656505471908006309396480, 10, true, 183880022⟩ CTN.nil) ⟨399196977043307470521376964608, 403491081554578633349933301760, 10, true, 181069953⟩ (CTN.node CTN.nil ⟨399235662669535138654967562240, 400202803325226841994732503040, 10, true, 194122073⟩ CTN.nil)))))

def tab26 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨399235662669535138654967562240, 400609002400617357397433778176, 10, true, 193334388⟩ CTN.nil) ⟨399235662669535138654967562240, 400783087718641863998591467520, 10, true, 192998032⟩ (CTN.node CTN.nil ⟨399235662669535138654967562240, 401169943980918545334497443840, 10, true, 192253190⟩ CTN.nil)) ⟨399235662669535138654967562240, 401556800243195226670403420160, 10, true, 191511939⟩ (CTN.node (CTN.node CTN.nil ⟨399235662669535138654967562240, 402330512767748589342215372800, 10, true, 190040129⟩ CTN.nil) ⟨399235662669535138654967562240, 403104225292301952014027325440, 10, true, 188582435⟩ (CTN.node CTN.nil ⟨399235662669535138654967562240, 403877937816855314685839278080, 10, true, 187138697⟩ CTN.nil))) ⟨399235662669535138654967562240, 405425362865962040029463183360, 10, true, 184292448⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨399235662669535138654967562240, 406972787915068765373087088640, 10, true, 181500126⟩ CTN.nil) ⟨399235662669535138654967562240, 408520212964175490716710993920, 10, true, 178760509⟩ (CTN.node CTN.nil ⟨399235662669535138654967562240, 411615063062388941403958804480, 10, true, 173434664⟩ CTN.nil)) ⟨399235662669535138654967562240, 414709913160602392091206615040, 10, true, 168305763⟩ (CTN.node (CTN.node CTN.nil ⟨399274348295762806788558159872, 401034544289121706866930352128, 10, true, 199599042⟩ CTN.nil) ⟨399274348295762806788558159872, 402021027757927244273490591744, 10, true, 197643290⟩ (CTN.node CTN.nil ⟨399351719548218143055739355136, 402872111534935943212483739648, 10, true, 210267505⟩ CTN.nil)))) ⟨399351719548218143055739355136, 403645824059489305884295692288, 10, true, 208656825⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨399429090800673479322920550400, 400396231456365182662685491200, 10, true, 230694354⟩ CTN.nil) ⟨399448433613787313389715849216, 400821773344869532132182065152, 10, true, 233570434⟩ (CTN.node CTN.nil ⟨399545147679356483723692343296, 405038506603685358693557207040, 10, true, 242928173⟩ CTN.nil)) ⟨399545147679356483723692343296, 408133356701898809380805017600, 10, true, 235629296⟩ (CTN.node (CTN.node CTN.nil ⟨399545147679356483723692343296, 410531865528014233663422070784, 10, true, 230160505⟩ CTN.nil) ⟨399545147679356483723692343296, 415947853199887772366105739264, 10, true, 218383722⟩ (CTN.node CTN.nil ⟨399622518931811819990873538560, 400589659587503523330638479360, 10, true, 270351372⟩ CTN.nil))) ⟨399622518931811819990873538560, 400783087718641863998591467520, 10, true, 269828802⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨399622518931811819990873538560, 400995858662894038733339754496, 10, true, 269255433⟩ CTN.nil) ⟨399622518931811819990873538560, 401169943980918545334497443840, 10, true, 268787445⟩ (CTN.node CTN.nil ⟨399622518931811819990873538560, 401382714925170720069245730816, 10, true, 268216841⟩ CTN.nil)) ⟨399622518931811819990873538560, 401556800243195226670403420160, 10, true, 267751110⟩ (CTN.node (CTN.node CTN.nil ⟨399661204558039488124464136192, 401421400551398388202836328448, 10, true, 276451482⟩ CTN.nil) ⟨399699890184267156258054733824, 402446569646431593742987165696, 10, true, 282019961⟩ (CTN.node CTN.nil ⟨399699890184267156258054733824, 403220282170984956414799118336, 10, true, 279857365⟩ CTN.nil)))))

def tab27 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨399815947062950160658826526720, 400589659587503523330638479360, 10, true, 313680999⟩ CTN.nil) ⟨399815947062950160658826526720, 400783087718641863998591467520, 10, true, 313074675⟩ (CTN.node CTN.nil ⟨399835289876063994725621825536, 401208629607146213468088041472, 10, true, 316228476⟩ CTN.nil)) ⟨399854632689177828792417124352, 410841350537835578732146851840, 10, true, 291650084⟩ (CTN.node (CTN.node CTN.nil ⟨399873975502291662859212423168, 401634171495650562937584615424, 10, true, 323910624⟩ CTN.nil) ⟨400009375194088501326779514880, 400783087718641863998591467520, 10, true, 359539763⟩ (CTN.node CTN.nil ⟨400009375194088501326779514880, 400976515849780204666544455680, 10, true, 358845135⟩ CTN.nil))) ⟨400009375194088501326779514880, 401169943980918545334497443840, 10, true, 358152183⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨400009375194088501326779514880, 401382714925170720069245730816, 10, true, 357391868⟩ CTN.nil) ⟨400009375194088501326779514880, 401556800243195226670403420160, 10, true, 356771293⟩ (CTN.node CTN.nil ⟨400009375194088501326779514880, 401769571187447401405151707136, 10, true, 356014641⟩ CTN.nil)) ⟨400009375194088501326779514880, 401943656505471908006309396480, 10, true, 355397055⟩ (CTN.node (CTN.node CTN.nil ⟨400009375194088501326779514880, 402330512767748589342215372800, 10, true, 354029429⟩ CTN.nil) ⟨400009375194088501326779514880, 403104225292301952014027325440, 10, true, 351313864⟩ (CTN.node CTN.nil ⟨400009375194088501326779514880, 403877937816855314685839278080, 10, true, 348624296⟩ CTN.nil)))) ⟨400048060820316169460370112512, 401421400551398388202836328448, 10, true, 366871486⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨400048060820316169460370112512, 402195113075951750874648281088, 10, true, 364051049⟩ CTN.nil) ⟨400048060820316169460370112512, 402794740282480606945302544384, 10, true, 361883840⟩ (CTN.node CTN.nil ⟨400048060820316169460370112512, 403568452807033969617114497024, 10, true, 359111225⟩ CTN.nil)) ⟨400125432072771505727551307776, 403645824059489305884295692288, 10, true, 378024538⟩ (CTN.node (CTN.node CTN.nil ⟨400202803325226841994732503040, 400976515849780204666544455680, 10, true, 408431653⟩ CTN.nil) ⟨400202803325226841994732503040, 401169943980918545334497443840, 10, true, 407642947⟩ (CTN.node CTN.nil ⟨400222146138340676061527801856, 401295672266158466768666886144, 10, true, 412250136⟩ CTN.nil))) ⟨400222146138340676061527801856, 401595485869422894803994017792, 10, true, 411018015⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨400222146138340676061527801856, 401982342131699576139899994112, 10, true, 409434977⟩ CTN.nil) ⟨400260831764568344195118399488, 402021027757927244273490591744, 10, true, 419536166⟩ (CTN.node CTN.nil ⟨400396231456365182662685491200, 401169943980918545334497443840, 10, true, 460336147⟩ CTN.nil)) ⟨400396231456365182662685491200, 401363372112056886002450432000, 10, true, 459447640⟩ (CTN.node (CTN.node CTN.nil ⟨400396231456365182662685491200, 401556800243195226670403420160, 10, true, 458561277⟩ CTN.nil) ⟨400396231456365182662685491200, 401943656505471908006309396480, 10, true, 456794956⟩ (CTN.node CTN.nil ⟨400396231456365182662685491200, 402330512767748589342215372800, 10, true, 455037135⟩ CTN.nil)))))

def tab28 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨400396231456365182662685491200, 405889590380694057632550354944, 10, true, 439255509⟩ CTN.nil) ⟨400396231456365182662685491200, 407437015429800782976174260224, 10, true, 432607663⟩ (CTN.node CTN.nil ⟨400434917082592850796276088832, 401508443210410641503415173120, 10, true, 469668460⟩ CTN.nil)) ⟨400473602708820518929866686464, 402233798702179419008238878720, 10, true, 477217038⟩ (CTN.node (CTN.node CTN.nil ⟨400473602708820518929866686464, 403220282170984956414799118336, 10, true, 472554982⟩ CTN.nil) ⟨400521959741605104096854933504, 401595485869422894803994017792, 10, true, 494198099⟩ (CTN.node CTN.nil ⟨400550973961275855197047881728, 406044332885604730166912745472, 10, true, 480942433⟩ CTN.nil))) ⟨400589659587503523330638479360, 401363372112056886002450432000, 10, true, 515232065⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨400589659587503523330638479360, 401556800243195226670403420160, 10, true, 514238082⟩ CTN.nil) ⟨400609002400617357397433778176, 401682528528435148104572862464, 10, true, 519328881⟩ (CTN.node CTN.nil ⟨400609002400617357397433778176, 401982342131699576139899994112, 10, true, 517778224⟩ CTN.nil)) ⟨400647688026845025531024375808, 402021027757927244273490591744, 10, true, 529106123⟩ (CTN.node (CTN.node CTN.nil ⟨400647688026845025531024375808, 402794740282480606945302544384, 10, true, 525044520⟩ CTN.nil) ⟨400734730685857278831603220480, 401808256813675069538742304768, 10, true, 556686104⟩ (CTN.node CTN.nil ⟨400783087718641863998591467520, 401750228374333567338356408320, 10, true, 571992483⟩ CTN.nil)))) ⟨400783087718641863998591467520, 401943656505471908006309396480, 10, true, 570890065⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨400783087718641863998591467520, 402330512767748589342215372800, 10, true, 568693187⟩ CTN.nil) ⟨400783087718641863998591467520, 402717369030025270678121349120, 10, true, 566506871⟩ (CTN.node CTN.nil ⟨400783087718641863998591467520, 403104225292301952014027325440, 10, true, 564331055⟩ CTN.nil)) ⟨400783087718641863998591467520, 403877937816855314685839278080, 10, true, 560010683⟩ (CTN.node (CTN.node CTN.nil ⟨400783087718641863998591467520, 404651650341408677357651230720, 10, true, 555731592⟩ CTN.nil) ⟨400783087718641863998591467520, 405425362865962040029463183360, 10, true, 551493311⟩ (CTN.node CTN.nil ⟨400783087718641863998591467520, 406972787915068765373087088640, 10, true, 543137315⟩ CTN.nil))) ⟨400783087718641863998591467520, 408520212964175490716710993920, 10, true, 534939039⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨400821773344869532132182065152, 401895299472687322839321149440, 10, true, 583277850⟩ CTN.nil) ⟨400821773344869532132182065152, 402195113075951750874648281088, 10, true, 581537173⟩ (CTN.node CTN.nil ⟨400821773344869532132182065152, 402581969338228432210554257408, 10, true, 579300724⟩ CTN.nil)) ⟨400821773344869532132182065152, 403568452807033969617114497024, 10, true, 573646270⟩ (CTN.node (CTN.node CTN.nil ⟨400821773344869532132182065152, 404342165331587332288926449664, 10, true, 569259631⟩ CTN.nil) ⟨400860458971097200265772662784, 402620654964456100344144855040, 10, true, 591228612⟩ (CTN.node CTN.nil ⟨400899144597324868399363260416, 403645824059489305884295692288, 10, true, 597385578⟩ CTN.nil)))))

def tab29 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨400908816003881785432760909824, 401982342131699576139899994112, 10, true, 610463720⟩ CTN.nil) ⟨400976515849780204666544455680, 401943656505471908006309396480, 10, true, 632688406⟩ (CTN.node CTN.nil ⟨400995858662894038733339754496, 402369198393976257475805970432, 10, true, 636337738⟩ CTN.nil)) ⟨400995858662894038733339754496, 403142910918529620147617923072, 10, true, 631457210⟩ (CTN.node (CTN.node CTN.nil ⟨401034544289121706866930352128, 402108070416939497574069436416, 10, true, 650776829⟩ CTN.nil) ⟨401073229915349375000520949760, 403220282170984956414799118336, 10, true, 656377592⟩ (CTN.node CTN.nil ⟨401121586948133960167509196800, 402195113075951750874648281088, 10, true, 679406125⟩ CTN.nil))) ⟨401169943980918545334497443840, 402330512767748589342215372800, 10, true, 694962061⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨401169943980918545334497443840, 402717369030025270678121349120, 10, true, 692290309⟩ CTN.nil) ⟨401169943980918545334497443840, 403104225292301952014027325440, 10, true, 689631390⟩ (CTN.node CTN.nil ⟨401169943980918545334497443840, 403916623443082982819429875712, 10, true, 684089098⟩ CTN.nil)) ⟨401169943980918545334497443840, 404690335967636345491241828352, 10, true, 678862414⟩ (CTN.node (CTN.node CTN.nil ⟨401208629607146213468088041472, 402282155734964004175227125760, 10, true, 708622214⟩ CTN.nil) ⟨401208629607146213468088041472, 402581969338228432210554257408, 10, true, 706509509⟩ (CTN.node CTN.nil ⟨401247315233373881601678639104, 402620654964456100344144855040, 10, true, 719643154⟩ CTN.nil)))) ⟨401247315233373881601678639104, 403993994695538319086611070976, 10, true, 709888559⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨401247315233373881601678639104, 406740674157702756571543502848, 10, true, 690870382⟩ CTN.nil) ⟨401247315233373881601678639104, 408288099206809481915167408128, 10, true, 680436262⟩ (CTN.node CTN.nil ⟨401247315233373881601678639104, 412234033082031631541408366592, 10, true, 654707526⟩ CTN.nil)) ⟨401247315233373881601678639104, 415328883180245082228656177152, 10, true, 635374807⟩ (CTN.node (CTN.node CTN.nil ⟨401334357892386134902257483776, 402407884020203925609396568064, 10, true, 751854739⟩ CTN.nil) ⟨401421400551398388202836328448, 402494926679216178909975412736, 10, true, 782495959⟩ (CTN.node CTN.nil ⟨401421400551398388202836328448, 402794740282480606945302544384, 10, true, 780164241⟩ CTN.nil))) ⟨401421400551398388202836328448, 403181596544757288281208520704, 10, true, 777168395⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨401508443210410641503415173120, 402581969338228432210554257408, 10, true, 813716336⟩ CTN.nil) ⟨401556800243195226670403420160, 402717369030025270678121349120, 10, true, 830590517⟩ (CTN.node CTN.nil ⟨401556800243195226670403420160, 403104225292301952014027325440, 10, true, 827400419⟩ CTN.nil)) ⟨401556800243195226670403420160, 403491081554578633349933301760, 10, true, 824225629⟩ (CTN.node (CTN.node CTN.nil ⟨401556800243195226670403420160, 403877937816855314685839278080, 10, true, 821066057⟩ CTN.nil) ⟨401556800243195226670403420160, 404651650341408677357651230720, 10, true, 814792219⟩ (CTN.node CTN.nil ⟨401556800243195226670403420160, 405425362865962040029463183360, 10, true, 808578214⟩ CTN.nil)))))

def tab30 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨401595485869422894803994017792, 402968825600505113546460233728, 10, true, 842995185⟩ CTN.nil) ⟨401595485869422894803994017792, 403742538125058476218272186368, 10, true, 836539266⟩ (CTN.node CTN.nil ⟨401595485869422894803994017792, 404342165331587332288926449664, 10, true, 831578409⟩ CTN.nil)) ⟨401595485869422894803994017792, 405115877856140694960738402304, 10, true, 825231535⟩ (CTN.node (CTN.node CTN.nil ⟨401634171495650562937584615424, 403007511226732781680050831360, 10, true, 857269476⟩ CTN.nil) ⟨401672857121878231071175213056, 404419536584042668556107644928, 10, true, 859854046⟩ (CTN.node CTN.nil ⟨401672857121878231071175213056, 405193249108596031227919597568, 10, true, 853292617⟩ CTN.nil))) ⟨401721214154662816238163460096, 402794740282480606945302544384, 10, true, 892456752⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨401808256813675069538742304768, 403181596544757288281208520704, 10, true, 922898786⟩ CTN.nil) ⟨401808256813675069538742304768, 403568452807033969617114497024, 10, true, 919358242⟩ (CTN.node CTN.nil ⟨401846942439902737672332902400, 403607138433261637750705094656, 10, true, 934194520⟩ CTN.nil)) ⟨401943656505471908006309396480, 403491081554578633349933301760, 10, true, 973827598⟩ (CTN.node (CTN.node CTN.nil ⟨401943656505471908006309396480, 403877937816855314685839278080, 10, true, 970094545⟩ CTN.nil) ⟨401943656505471908006309396480, 407437015429800782976174260224, 10, true, 936576257⟩ (CTN.node CTN.nil ⟨401943656505471908006309396480, 410531865528014233663422070784, 10, true, 908599599⟩ CTN.nil)))) ⟨402021027757927244273490591744, 403394367489009463015956807680, 10, true, 1006191564⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨402021027757927244273490591744, 404168080013562825687768760320, 10, true, 998493958⟩ CTN.nil) ⟨402098399010382580540671787008, 407591757934711455510536650752, 10, true, 995925085⟩ (CTN.node CTN.nil ⟨402098399010382580540671787008, 409139182983818180854160556032, 10, true, 980914996⟩ CTN.nil)) ⟨402195113075951750874648281088, 404342165331587332288926449664, 10, true, 1068602158⟩ (CTN.node (CTN.node CTN.nil ⟨402233798702179419008238878720, 403993994695538319086611070976, 10, true, 1088650480⟩ CTN.nil) ⟨402330512767748589342215372800, 404651650341408677357651230720, 10, true, 1122721272⟩ (CTN.node CTN.nil ⟨402330512767748589342215372800, 405425362865962040029463183360, 10, true, 1114158849⟩ CTN.nil))) ⟨402330512767748589342215372800, 406972787915068765373087088640, 10, true, 1097277581⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨402330512767748589342215372800, 408520212964175490716710993920, 10, true, 1080714948⟩ CTN.nil) ⟨402330512767748589342215372800, 411615063062388941403958804480, 10, true, 1048517003⟩ (CTN.node CTN.nil ⟨402330512767748589342215372800, 414709913160602392091206615040, 10, true, 1017509707⟩ CTN.nil)) ⟨402330512767748589342215372800, 415947853199887772366105739264, 10, true, 1005428326⟩ (CTN.node (CTN.node CTN.nil ⟨402369198393976257475805970432, 405115877856140694960738402304, 10, true, 1134166649⟩ CTN.nil) ⟨402369198393976257475805970432, 405889590380694057632550354944, 10, true, 1125526841⟩ (CTN.node CTN.nil ⟨402446569646431593742987165696, 405966961633149393899731550208, 10, true, 1157931786⟩ CTN.nil)))))

def tab31 : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨402639997777569934410940153856, 413626715626227684350669881344, 10, true, 1153447231⟩ CTN.nil) ⟨402639997777569934410940153856, 415947853199887772366105739264, 10, true, 1127868602⟩ (CTN.node CTN.nil ⟨402794740282480606945302544384, 405541419744645044430234976256, 10, true, 1319026531⟩ CTN.nil)) ⟨402794740282480606945302544384, 408288099206809481915167408128, 10, true, 1283822406⟩ (CTN.node (CTN.node CTN.nil ⟨402794740282480606945302544384, 409835524255916207258791313408, 10, true, 1264506085⟩ CTN.nil) ⟨402949482787391279479664934912, 413936200636049029419394662400, 10, true, 1281845910⟩ (CTN.node CTN.nil ⟨402949482787391279479664934912, 415947853199887772366105739264, 10, true, 1257182497⟩ CTN.nil))) ⟨403220282170984956414799118336, 406740674157702756571543502848, 10, true, 1505067239⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨403645824059489305884295692288, 409139182983818180854160556032, 10, true, 1680579671⟩ CTN.nil) ⟨403645824059489305884295692288, 412234033082031631541408366592, 10, true, 1630584454⟩ (CTN.node CTN.nil ⟨404342165331587332288926449664, 415328883180245082228656177152, 10, true, 1934302493⟩ CTN.nil)) ⟨404342165331587332288926449664, 415947853199887772366105739264, 10, true, 1922793340⟩ (CTN.node (CTN.node CTN.nil ⟨405425362865962040029463183360, 415947853199887772366105739264, 10, true, 2532594994⟩ CTN.nil) ⟨406353817895426075235637526528, 415947853199887772366105739264, 10, true, 3116773877⟩ (CTN.node CTN.nil ⟨408520212964175490716710993920, 415947853199887772366105739264, 10, true, 4686019082⟩ CTN.nil)))) ⟨415947853199887772366105739264, 416721565724441135037917691904, 11, false, 11636772221⟩ (CTN.node (CTN.node (CTN.node (CTN.node CTN.nil ⟨415947853199887772366105739264, 417804763258815842778454425600, 11, false, 11516344258⟩ CTN.nil) ⟨415947853199887772366105739264, 418733218288279877984628768768, 11, false, 11414358387⟩ (CTN.node CTN.nil ⟨415947853199887772366105739264, 420899613357029293465702236160, 11, false, 11180747848⟩ CTN.nil)) ⟨415947853199887772366105739264, 421518583376671983603151798272, 11, false, 11115102515⟩ (CTN.node (CTN.node CTN.nil ⟨415947853199887772366105739264, 424922918484706779359124389888, 11, false, 10762543015⟩ CTN.nil) ⟨415947853199887772366105739264, 427089313553456194840197857280, 11, false, 10545451932⟩ (CTN.node CTN.nil ⟨415947853199887772366105739264, 431112618681133680733620011008, 11, false, 10156612794⟩ CTN.nil))) ⟨415947853199887772366105739264, 433279013749883096214693478400, 11, false, 9954658577⟩ (CTN.node (CTN.node (CTN.node CTN.nil ⟨415947853199887772366105739264, 435754893828453856764491726848, 11, false, 9729963084⟩ CTN.nil) ⟨416876308229351807572280082432, 435754893828453856764491726848, 11, false, 10550857177⟩ (CTN.node CTN.nil ⟨435754893828453856764491726848, 439468713946309997589189099520, 11, true, 21764380703⟩ CTN.nil)) ⟨435754893828453856764491726848, 440706653985595377864088223744, 11, true, 21156897754⟩ (CTN.node (CTN.node CTN.nil ⟨435754893828453856764491726848, 455561934457019941162877714432, 11, true, 9629227507⟩ CTN.nil) ⟨455561934457019941162877714432, 474750005065943335423814139904, 12, false, 41440954⟩ CTN.nil))))

def table : CTN :=
  (CTN.node (CTN.node (CTN.node (CTN.node (CTN.node tab0 ⟨82680854655083718516504788992, 82729211687868303683493036032, 2, true, 1357438270⟩ tab1) ⟨84179922671405858693140447232, 90369622867832760067636068352, 2, true, 154299290⟩ (CTN.node tab2 ⟨156367301212234595973195628544, 156560729343372936641148616704, 4, false, 5395356450⟩ tab3)) ⟨157527869999064639980913557504, 157721298130202980648866545664, 4, false, 2836262683⟩ (CTN.node (CTN.node tab4 ⟨161396432621831453339973320704, 162943857670938178683597225984, 4, true, 83791953⟩ tab5) ⟨198070406285660843983859875840, 217877446914226928382245863424, 5, true, 38423148027⟩ (CTN.node tab6 ⟨237181574401833327043954081792, 237684487542793012780631851008, 6, false, 320321292⟩ tab7))) ⟨239435012129594995825606393856, 239580083227948751326571134976, 6, true, 2638657⟩ (CTN.node (CTN.node (CTN.node tab8 ⟨239918582457440847495488864256, 240015296523010017829465358336, 6, true, 48530020⟩ tab9) ⟨240160367621363773330430099456, 257491528171359097179017838592, 6, true, 70160892⟩ (CTN.node tab10 ⟨240934080145917136002242052096, 242094648932747180009959981056, 6, true, 321895646⟩ tab11)) ⟨243255217719577224017677910016, 255634618112431026766669152256, 6, true, 1520846759⟩ (CTN.node (CTN.node tab12 ⟨311960889899915829274579304448, 316603165047236005305451020288, 8, false, 153740452⟩ tab13) ⟨316912650057057350374175801344, 317183449440651027309309984768, 8, true, 60614838⟩ (CTN.node tab14 ⟨318150590096342730649074925568, 327435140390983082710818357248, 8, true, 58303⟩ tab15)))) ⟨318788902929099254853319786496, 320162242660181473595786002432, 8, true, 30129428⟩ (CTN.node (CTN.node (CTN.node (CTN.node tab16 ⟨320084871407726137328604807168, 321245440194556181336322736128, 8, true, 257954834⟩ tab17) ⟨321245440194556181336322736128, 325887715341876357367194451968, 8, true, 618619956⟩ (CTN.node tab18 ⟨322019152719109544008134688768, 322986293374801247347899629568, 8, true, 999860115⟩ tab19)) ⟨322406008981386225344040665088, 324340290292769632023570546688, 8, true, 1188829296⟩ (CTN.node (CTN.node tab20 ⟨322792865243662906679946641408, 323276435571508758349829111808, 8, true, 1432646991⟩ tab21) ⟨323083007440370417681876123648, 323324792604293343516817358848, 8, true, 1615593584⟩ (CTN.node tab22 ⟨323566577768216269351758594048, 324340290292769632023570546688, 8, true, 1922008203⟩ tab23))) ⟨324727146555046313359476523008, 326274571604153038703100428288, 8, true, 2760826956⟩ (CTN.node (CTN.node (CTN.node tab24 ⟨397688237620428413311343656960, 402330512767748589342215372800, 10, true, 14053310⟩ tab25) ⟨399235662669535138654967562240, 400396231456365182662685491200, 10, true, 193746485⟩ (CTN.node tab26 ⟨399699890184267156258054733824, 405193249108596031227919597568, 10, true, 274435871⟩ tab27)) ⟨400396231456365182662685491200, 402543283712000764076963659776, 10, true, 454073938⟩ (CTN.node (CTN.node tab28 ⟨400899144597324868399363260416, 404419536584042668556107644928, 10, true, 592818281⟩ tab29) ⟨401556800243195226670403420160, 415947853199887772366105739264, 10, true, 729669240⟩ (CTN.node tab30 ⟨402620654964456100344144855040, 404767707220091681758423023616, 10, true, 1249238179⟩ tab31)))))

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
  (39614081257132168796771975168, 59421121885698253195157962752, true),
  (59421121885698253195157962752, 69324642199981295394350956544, true),
  (69324642199981295394350956544, 74276402357122816493947453440, true),
  (74276402357122816493947453440, 76752282435693577043745701888, true),
  (76752282435693577043745701888, 77990222474978957318644826112, true),
  (77990222474978957318644826112, 90369622867832760067636068352, false),
  (90369622867832760067636068352, 91607562907118140342535192576, true),
  (91607562907118140342535192576, 94083442985688900892333441024, true),
  (94083442985688900892333441024, 99035203142830421991929937920, true),
  (99035203142830421991929937920, 118842243771396506390315925504, true),
  (118842243771396506390315925504, 138649284399962590788701913088, true),
  (138649284399962590788701913088, 148552804714245632987894906880, true),
  (148552804714245632987894906880, 149790744753531013262794031104, true),
  (149790744753531013262794031104, 174549545539238618760776515584, false),
  (174549545539238618760776515584, 175787485578523999035675639808, true),
  (175787485578523999035675639808, 178263365657094759585473888256, true),
  (178263365657094759585473888256, 198070406285660843983859875840, true),
  (198070406285660843983859875840, 217877446914226928382245863424, true),
  (217877446914226928382245863424, 220353326992797688932044111872, true),
  (220353326992797688932044111872, 221591267032083069206943236096, true),
  (221591267032083069206943236096, 259967408249929857728816087040, false),
  (259967408249929857728816087040, 260586378269572547866265649152, true),
  (260586378269572547866265649152, 261205348289215238003715211264, true),
  (261205348289215238003715211264, 262443288328500618278614335488, true),
  (262443288328500618278614335488, 267395048485642139378210832384, true),
  (267395048485642139378210832384, 277298568799925181577403826176, true),
  (277298568799925181577403826176, 287202089114208223776596819968, true),
  (287202089114208223776596819968, 292153849271349744876193316864, true),
  (292153849271349744876193316864, 293391789310635125151092441088, true),
  (293391789310635125151092441088, 475368975085586025561263702016, false)]

theorem cover0_ok : FourN.coverCheck table 400000000 (SC / 2) 475368975085586025561263702016 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (39614081257132168796771975168, 59421121885698253195157962752, true),
  (59421121885698253195157962752, 69324642199981295394350956544, true),
  (69324642199981295394350956544, 74276402357122816493947453440, true),
  (74276402357122816493947453440, 76752282435693577043745701888, true),
  (76752282435693577043745701888, 77990222474978957318644826112, true),
  (77990222474978957318644826112, 90369622867832760067636068352, false),
  (90369622867832760067636068352, 91607562907118140342535192576, true),
  (91607562907118140342535192576, 94083442985688900892333441024, true),
  (94083442985688900892333441024, 99035203142830421991929937920, true),
  (99035203142830421991929937920, 118842243771396506390315925504, true),
  (118842243771396506390315925504, 138649284399962590788701913088, true),
  (138649284399962590788701913088, 148552804714245632987894906880, true),
  (148552804714245632987894906880, 149790744753531013262794031104, true),
  (149790744753531013262794031104, 174549545539238618760776515584, false),
  (174549545539238618760776515584, 175787485578523999035675639808, true),
  (175787485578523999035675639808, 178263365657094759585473888256, true),
  (178263365657094759585473888256, 198070406285660843983859875840, true),
  (198070406285660843983859875840, 217877446914226928382245863424, true),
  (217877446914226928382245863424, 220353326992797688932044111872, true),
  (220353326992797688932044111872, 221591267032083069206943236096, true),
  (221591267032083069206943236096, 259967408249929857728816087040, false),
  (259967408249929857728816087040, 260586378269572547866265649152, true),
  (260586378269572547866265649152, 261205348289215238003715211264, true),
  (261205348289215238003715211264, 262443288328500618278614335488, true),
  (262443288328500618278614335488, 267395048485642139378210832384, true),
  (267395048485642139378210832384, 277298568799925181577403826176, true),
  (277298568799925181577403826176, 287202089114208223776596819968, true),
  (287202089114208223776596819968, 292153849271349744876193316864, true),
  (292153849271349744876193316864, 293391789310635125151092441088, true),
  (293391789310635125151092441088, 475368975085586025561263702016, false)]

theorem cover1_ok : FourN.coverCheck table 400000000 (SC / 2) 475368975085586025561263702016 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (39614081257132168796771975168, 59421121885698253195157962752, true),
  (59421121885698253195157962752, 69324642199981295394350956544, true),
  (69324642199981295394350956544, 74276402357122816493947453440, true),
  (74276402357122816493947453440, 76752282435693577043745701888, true),
  (76752282435693577043745701888, 77990222474978957318644826112, true),
  (77990222474978957318644826112, 90369622867832760067636068352, false),
  (90369622867832760067636068352, 91607562907118140342535192576, true),
  (91607562907118140342535192576, 94083442985688900892333441024, true),
  (94083442985688900892333441024, 99035203142830421991929937920, true),
  (99035203142830421991929937920, 118842243771396506390315925504, true),
  (118842243771396506390315925504, 138649284399962590788701913088, true),
  (138649284399962590788701913088, 148552804714245632987894906880, true),
  (148552804714245632987894906880, 149790744753531013262794031104, true),
  (149790744753531013262794031104, 174549545539238618760776515584, false),
  (174549545539238618760776515584, 175787485578523999035675639808, true),
  (175787485578523999035675639808, 178263365657094759585473888256, true),
  (178263365657094759585473888256, 198070406285660843983859875840, true),
  (198070406285660843983859875840, 217877446914226928382245863424, true),
  (217877446914226928382245863424, 220353326992797688932044111872, true),
  (220353326992797688932044111872, 221591267032083069206943236096, true),
  (221591267032083069206943236096, 259967408249929857728816087040, false),
  (259967408249929857728816087040, 260586378269572547866265649152, true),
  (260586378269572547866265649152, 261205348289215238003715211264, true),
  (261205348289215238003715211264, 262443288328500618278614335488, true),
  (262443288328500618278614335488, 267395048485642139378210832384, true),
  (267395048485642139378210832384, 277298568799925181577403826176, true),
  (277298568799925181577403826176, 287202089114208223776596819968, true),
  (287202089114208223776596819968, 292153849271349744876193316864, true),
  (292153849271349744876193316864, 293391789310635125151092441088, true),
  (293391789310635125151092441088, 475368975085586025561263702016, false)]

theorem cover2_ok : FourN.coverCheck table 400000000 (SC / 2) 475368975085586025561263702016 cover2 = true := by decide +kernel

def bits : ℕ := 64600972208909331016391305011103080043954413644756777594332445984693851128991873848869816704584293613562513736336334395190107583363884535260719784545453348154642081010696537739957113968317490948889373450935659067901590076948996902970430621951580268246263227103890380013000505688999007795785322621250609613621157842042715819108774807420124631763542652541578294940597821077371745139307376370761554958883858391455599504202599147809975398205995998095037209221377166021043277174307761731244770810758016698250139850559271470023332897682965335927079816476143849749622051090635659383189838828967518952569750219661828978936308045007282689685042455015250580744145869213396032727005107577710489084845953026129898401313737772521544977372793616719625403818369456426355311383501517507713319095724231254646480316965341246765638993712480937868316907146077267465233512715821751634379821328972887014060047320848969267794976105568740447195146876406823470760159849456579247644465621288912792566518200571815791826590240337992455820158319429338704010008090411392853977336726502944903149699801232964393979072582129396355621824830462966439830677452207906617262352544715429451693482641383977956398082563407110784520431194354643564012982674402563876122227470599000667042905341614128810668766317419405023216522672899173598946079514141728227558097315106495309905295680820672283083956509632247493083722396575075127943649086884681691852987432434285477854890315312429766075969797260513027585939101474584427734787331852397363205173368773868898472120515113935256212091331839470046821426730028629861900070091185622113915302548771682981467567161110081126199475897904600050301656093037838453796455190745194728165891702602354271646077122934519427688741416513492843643154550453337208938116480742861963364794175070334784576864420376297032147370024854310535468484699321155843948260127375669246711329738754681939420957878988912962793899413545207254850317654975322078761471939694248951334654365450278853742204712006008071156406013846902688989270659673306751466769681209564121166569258869809568797549199716383772329584726297112156718286208659641884829354058428255785986441517873314497269309373530380943049533016676465835851481840549852711509930337415598371223269803055023873983423523588456245053122511848795595539164484306605308255583

theorem wk0 : FourN.walk table bits 64 0 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) = some 113 := by decide +kernel

theorem wk1 : FourN.walk table bits 64 113 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) = some 296 := by decide +kernel

theorem wk2 : FourN.walk table bits 64 296 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) = some 369 := by decide +kernel

theorem wk3 : FourN.walk table bits 64 369 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) = some 378 := by decide +kernel

theorem wk7 : FourN.walk table bits 61 381 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 155980444949957914637289652224 77990222474978957318644826112 90369622867832760067636068352) = some 578 := by decide +kernel

theorem wk10 : FourN.walk table bits 59 580 (FourN.Box.mk 77990222474978957318644826112 81085072573192408005892636672 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 599 := by decide +kernel

theorem wk13 : FourN.walk table bits 57 601 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 81085072573192408005892636672) = some 608 := by decide +kernel

theorem wk17 : FourN.walk table bits 54 611 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) = some 746 := by decide +kernel

theorem wk18 : FourN.walk table bits 54 746 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) = some 1233 := by decide +kernel

theorem wk16 : FourN.walk table bits 55 610 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) = some 1233 :=
  FourN.walk_split table bits 54 610 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) 746 1233 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) from by decide +kernel]; exact wk17)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk18)

theorem wk19 : FourN.walk table bits 55 1233 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) = some 1616 := by decide +kernel

theorem wk15 : FourN.walk table bits 56 609 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) = some 1616 :=
  FourN.walk_split table bits 55 609 (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) 1233 1616 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk16)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk19)

theorem wk23 : FourN.walk table bits 53 1619 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) = some 2102 := by decide +kernel

theorem wk24 : FourN.walk table bits 53 2102 (FourN.Box.mk 83406210146852496021328494592 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) = some 2193 := by decide +kernel

theorem wk22 : FourN.walk table bits 54 1618 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) = some 2193 :=
  FourN.walk_split table bits 53 1618 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) 2102 2193 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) from by decide +kernel]; exact wk23)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952))) = (FourN.Box.mk 83406210146852496021328494592 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) from by decide +kernel]; exact wk24)

theorem wk29 : FourN.walk table bits 50 2197 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) = some 2488 := by decide +kernel

theorem wk30 : FourN.walk table bits 50 2488 (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) = some 2769 := by decide +kernel

theorem wk28 : FourN.walk table bits 51 2196 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) = some 2769 :=
  FourN.walk_split table bits 50 2196 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) 2488 2769 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk29)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk30)

theorem wk31 : FourN.walk table bits 51 2769 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 83406210146852496021328494592 84179922671405858693140447232) = some 2834 := by decide +kernel

theorem wk27 : FourN.walk table bits 52 2195 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) = some 2834 :=
  FourN.walk_split table bits 51 2195 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) 2769 2834 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk28)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 83406210146852496021328494592 84179922671405858693140447232) from by decide +kernel]; exact wk31)

theorem wk36 : FourN.walk table bits 48 2838 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83019353884575814685422518272) = some 3165 := by decide +kernel

theorem wk37 : FourN.walk table bits 48 3165 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 83019353884575814685422518272 83406210146852496021328494592) = some 3358 := by decide +kernel

theorem wk35 : FourN.walk table bits 49 2837 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) = some 3358 :=
  FourN.walk_split table bits 48 2837 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) 3165 3358 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83019353884575814685422518272) from by decide +kernel]; exact wk36)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 83019353884575814685422518272 83406210146852496021328494592) from by decide +kernel]; exact wk37)

theorem wk38 : FourN.walk table bits 49 3358 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 157141013736787958645007581184 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) = some 3723 := by decide +kernel

theorem wk34 : FourN.walk table bits 50 2836 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) = some 3723 :=
  FourN.walk_split table bits 49 2836 (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) 3358 3723 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk35)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 157141013736787958645007581184 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk38)

theorem wk40 : FourN.walk table bits 49 3724 (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) = some 4043 := by decide +kernel

theorem wk41 : FourN.walk table bits 49 4043 (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 157141013736787958645007581184 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) = some 4224 := by decide +kernel

theorem wk39 : FourN.walk table bits 50 3723 (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) = some 4224 :=
  FourN.walk_split table bits 49 3723 (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) 4043 4224 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157141013736787958645007581184 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk40)
    (by rw [show ((FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 157141013736787958645007581184 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk41)

theorem wk33 : FourN.walk table bits 51 2835 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) = some 4224 :=
  FourN.walk_split table bits 50 2835 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) 3723 4224 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 82632497622299133349516541952 83019353884575814685422518272 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk34)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592))) = (FourN.Box.mk 83019353884575814685422518272 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk39)

theorem wk42 : FourN.walk table bits 51 4224 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 83406210146852496021328494592 84179922671405858693140447232) = some 4303 := by decide +kernel

theorem wk32 : FourN.walk table bits 52 2834 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) = some 4303 :=
  FourN.walk_split table bits 51 2834 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) 4224 4303 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 83406210146852496021328494592) from by decide +kernel]; exact wk33)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 83406210146852496021328494592 84179922671405858693140447232) from by decide +kernel]; exact wk42)

theorem wk26 : FourN.walk table bits 53 2194 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) = some 4303 :=
  FourN.walk_split table bits 52 2194 (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) 2834 4303 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 156754157474511277309101604864 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk27)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 156754157474511277309101604864 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk32)

theorem wk43 : FourN.walk table bits 53 4303 (FourN.Box.mk 83406210146852496021328494592 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) = some 4512 := by decide +kernel

theorem wk25 : FourN.walk table bits 54 2193 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) = some 4512 :=
  FourN.walk_split table bits 53 2193 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) 4303 4512 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 83406210146852496021328494592 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk26)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232))) = (FourN.Box.mk 83406210146852496021328494592 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk43)

theorem wk21 : FourN.walk table bits 55 1617 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) = some 4512 :=
  FourN.walk_split table bits 54 1617 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) 2193 4512 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 82632497622299133349516541952) from by decide +kernel]; exact wk22)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk25)

theorem wk45 : FourN.walk table bits 54 4513 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 82632497622299133349516541952) = some 4784 := by decide +kernel

theorem wk46 : FourN.walk table bits 54 4784 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 82632497622299133349516541952 84179922671405858693140447232) = some 5121 := by decide +kernel

theorem wk44 : FourN.walk table bits 55 4512 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) = some 5121 :=
  FourN.walk_split table bits 54 4512 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) 4784 5121 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 82632497622299133349516541952) from by decide +kernel]; exact wk45)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 82632497622299133349516541952 84179922671405858693140447232) from by decide +kernel]; exact wk46)

theorem wk20 : FourN.walk table bits 56 1616 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) = some 5121 :=
  FourN.walk_split table bits 55 1616 (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) 4512 5121 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 157527869999064639980913557504 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk21)
    (by rw [show ((FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 157527869999064639980913557504 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk44)

theorem wk14 : FourN.walk table bits 57 608 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) = some 5121 :=
  FourN.walk_split table bits 56 608 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) 1616 5121 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 82632497622299133349516541952 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk15)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232))) = (FourN.Box.mk 82632497622299133349516541952 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk20)

theorem wk12 : FourN.walk table bits 58 600 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) = some 5121 :=
  FourN.walk_split table bits 57 600 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) 608 5121 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 81085072573192408005892636672) from by decide +kernel]; exact wk13)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 81085072573192408005892636672 84179922671405858693140447232) from by decide +kernel]; exact wk14)

theorem wk47 : FourN.walk table bits 58 5121 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 159075295048171365324537462784 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 5202 := by decide +kernel

theorem wk11 : FourN.walk table bits 59 599 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 5202 :=
  FourN.walk_split table bits 58 599 (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) 5121 5202 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 159075295048171365324537462784 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk12)
    (by rw [show ((FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 159075295048171365324537462784 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk47)

theorem wk9 : FourN.walk table bits 60 579 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 5202 :=
  FourN.walk_split table bits 59 579 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) 599 5202 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 77990222474978957318644826112 81085072573192408005892636672 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk10)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 81085072573192408005892636672 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk11)

theorem wk48 : FourN.walk table bits 60 5202 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 84179922671405858693140447232 90369622867832760067636068352) = some 5267 := by decide +kernel

theorem wk8 : FourN.walk table bits 61 578 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 5267 :=
  FourN.walk_split table bits 60 578 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 5202 5267 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk9)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 84179922671405858693140447232 90369622867832760067636068352) from by decide +kernel]; exact wk48)

theorem wk6 : FourN.walk table bits 62 380 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 5267 :=
  FourN.walk_split table bits 61 380 (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 578 5267 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 155980444949957914637289652224 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk7)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk8)

theorem wk49 : FourN.walk table bits 62 5267 (FourN.Box.mk 84179922671405858693140447232 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 5390 := by decide +kernel

theorem wk5 : FourN.walk table bits 63 379 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 5390 :=
  FourN.walk_split table bits 62 379 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 5267 5390 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 84179922671405858693140447232 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk6)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 84179922671405858693140447232 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk49)

theorem wk50 : FourN.walk table bits 63 5390 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 162170145146384816011785273344 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 5407 := by decide +kernel

theorem wk4 : FourN.walk table bits 64 378 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 5407 :=
  FourN.walk_split table bits 63 378 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) 5390 5407 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk5)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 162170145146384816011785273344 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk50)

theorem wk52 : FourN.walk table bits 63 5408 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584) = some 5895 := by decide +kernel

theorem wk53 : FourN.walk table bits 63 5895 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 162170145146384816011785273344 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) = some 5912 := by decide +kernel

theorem wk51 : FourN.walk table bits 64 5407 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) = some 5912 :=
  FourN.walk_split table bits 63 5407 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) 5895 5912 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584))) = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk52)
    (by rw [show ((FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584)) (FourN.Box.mid (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) (FourN.Box.widthArg (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584))) = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 162170145146384816011785273344 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk53)

theorem wk54 : FourN.walk table bits 64 5912 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) = some 5919 := by decide +kernel

theorem wk55 : FourN.walk table bits 64 5919 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) = some 5920 := by decide +kernel

theorem wk56 : FourN.walk table bits 64 5920 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) = some 6295 := by decide +kernel

theorem wk57 : FourN.walk table bits 64 6295 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) = some 6302 := by decide +kernel

theorem wk58 : FourN.walk table bits 64 6302 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) = some 6303 := by decide +kernel

theorem wk59 : FourN.walk table bits 64 6303 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) = some 6304 := by decide +kernel

theorem wk60 : FourN.walk table bits 64 6304 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) = some 6313 := by decide +kernel

theorem wk61 : FourN.walk table bits 64 6313 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) = some 6314 := by decide +kernel

theorem wk62 : FourN.walk table bits 64 6314 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) = some 6315 := by decide +kernel

theorem wk63 : FourN.walk table bits 64 6315 (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) = some 6316 := by decide +kernel

theorem wk64 : FourN.walk table bits 64 6316 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) = some 6547 := by decide +kernel

theorem wk65 : FourN.walk table bits 64 6547 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) = some 6840 := by decide +kernel

theorem wk66 : FourN.walk table bits 64 6840 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) = some 6847 := by decide +kernel

theorem wk67 : FourN.walk table bits 64 6847 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) = some 6848 := by decide +kernel

theorem wk71 : FourN.walk table bits 61 6851 (FourN.Box.mk 149790744753531013262794031104 155980444949957914637289652224 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 6852 := by decide +kernel

theorem wk73 : FourN.walk table bits 60 6853 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 155980444949957914637289652224 77990222474978957318644826112 90369622867832760067636068352) = some 6854 := by decide +kernel

theorem wk76 : FourN.walk table bits 58 6856 (FourN.Box.mk 155980444949957914637289652224 159075295048171365324537462784 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 7055 := by decide +kernel

theorem wk77 : FourN.walk table bits 58 7055 (FourN.Box.mk 159075295048171365324537462784 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 7386 := by decide +kernel

theorem wk75 : FourN.walk table bits 59 6855 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) = some 7386 :=
  FourN.walk_split table bits 58 6855 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) 7055 7386 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 155980444949957914637289652224 159075295048171365324537462784 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk76)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232))) = (FourN.Box.mk 159075295048171365324537462784 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk77)

theorem wk78 : FourN.walk table bits 59 7386 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 84179922671405858693140447232 90369622867832760067636068352) = some 7431 := by decide +kernel

theorem wk74 : FourN.walk table bits 60 6854 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 7431 :=
  FourN.walk_split table bits 59 6854 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 7386 7431 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 84179922671405858693140447232) from by decide +kernel]; exact wk75)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 84179922671405858693140447232 90369622867832760067636068352) from by decide +kernel]; exact wk78)

theorem wk72 : FourN.walk table bits 61 6852 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 7431 :=
  FourN.walk_split table bits 60 6852 (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 6854 7431 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 155980444949957914637289652224 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk73)
    (by rw [show ((FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 155980444949957914637289652224 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk74)

theorem wk70 : FourN.walk table bits 62 6850 (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) = some 7431 :=
  FourN.walk_split table bits 61 6850 (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) 6852 7431 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 149790744753531013262794031104 155980444949957914637289652224 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk71)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 155980444949957914637289652224 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk72)

theorem wk79 : FourN.walk table bits 62 7431 (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 162170145146384816011785273344 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7450 := by decide +kernel

theorem wk69 : FourN.walk table bits 63 6849 (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7450 :=
  FourN.walk_split table bits 62 6849 (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) 7431 7450 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 162170145146384816011785273344 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk70)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 162170145146384816011785273344 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk79)

theorem wk80 : FourN.walk table bits 63 7450 (FourN.Box.mk 162170145146384816011785273344 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7479 := by decide +kernel

theorem wk68 : FourN.walk table bits 64 6848 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7479 :=
  FourN.walk_split table bits 63 6848 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) 7450 7479 (by decide +kernel)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setHi (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 149790744753531013262794031104 162170145146384816011785273344 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk69)
    (by rw [show ((FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) : FourN.Box).setLo (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352)) (FourN.Box.mid (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) (FourN.Box.widthArg (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352))) = (FourN.Box.mk 162170145146384816011785273344 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk80)

theorem wk81 : FourN.walk table bits 64 7479 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) = some 7490 := by decide +kernel

theorem wk82 : FourN.walk table bits 64 7490 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) = some 7491 := by decide +kernel

theorem wk83 : FourN.walk table bits 64 7491 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) = some 7492 := by decide +kernel

theorem wk84 : FourN.walk table bits 64 7492 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) = some 7499 := by decide +kernel

theorem wk85 : FourN.walk table bits 64 7499 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) = some 7500 := by decide +kernel

theorem wk86 : FourN.walk table bits 64 7500 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) = some 7501 := by decide +kernel

theorem wk87 : FourN.walk table bits 64 7501 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) = some 7502 := by decide +kernel

theorem wk88 : FourN.walk table bits 64 7502 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) = some 7503 := by decide +kernel

theorem wk89 : FourN.walk table bits 64 7503 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) = some 7504 := by decide +kernel

theorem wk90 : FourN.walk table bits 64 7504 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) = some 7505 := by decide +kernel

theorem wk91 : FourN.walk table bits 64 7505 (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) = some 7506 := by decide +kernel

theorem wk92 : FourN.walk table bits 64 7506 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) = some 7579 := by decide +kernel

theorem wk93 : FourN.walk table bits 64 7579 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) = some 7586 := by decide +kernel

theorem wk94 : FourN.walk table bits 64 7586 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) = some 7587 := by decide +kernel

theorem wk95 : FourN.walk table bits 64 7587 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) = some 7588 := by decide +kernel

theorem wk96 : FourN.walk table bits 64 7588 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7595 := by decide +kernel

theorem wk97 : FourN.walk table bits 64 7595 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) = some 7596 := by decide +kernel

theorem wk98 : FourN.walk table bits 64 7596 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) = some 7597 := by decide +kernel

theorem wk99 : FourN.walk table bits 64 7597 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) = some 7598 := by decide +kernel

theorem wk100 : FourN.walk table bits 64 7598 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) = some 7599 := by decide +kernel

theorem wk101 : FourN.walk table bits 64 7599 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) = some 7600 := by decide +kernel

theorem wk102 : FourN.walk table bits 64 7600 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) = some 7601 := by decide +kernel

theorem wk103 : FourN.walk table bits 64 7601 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) = some 7602 := by decide +kernel

theorem wk104 : FourN.walk table bits 64 7602 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) = some 7603 := by decide +kernel

theorem wk105 : FourN.walk table bits 64 7603 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) = some 7604 := by decide +kernel

theorem wk106 : FourN.walk table bits 64 7604 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) = some 7605 := by decide +kernel

theorem wk107 : FourN.walk table bits 64 7605 (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) = some 7606 := by decide +kernel

theorem wk108 : FourN.walk table bits 64 7606 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) = some 7615 := by decide +kernel

theorem wk109 : FourN.walk table bits 64 7615 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) = some 7616 := by decide +kernel

theorem wk110 : FourN.walk table bits 64 7616 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) = some 7617 := by decide +kernel

theorem wk111 : FourN.walk table bits 64 7617 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) = some 7618 := by decide +kernel

theorem wk112 : FourN.walk table bits 64 7618 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) = some 7619 := by decide +kernel

theorem wk113 : FourN.walk table bits 64 7619 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) = some 7620 := by decide +kernel

theorem wk114 : FourN.walk table bits 64 7620 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) = some 7621 := by decide +kernel

theorem wk115 : FourN.walk table bits 64 7621 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) = some 7622 := by decide +kernel

theorem wk116 : FourN.walk table bits 64 7622 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) = some 7623 := by decide +kernel

theorem wk117 : FourN.walk table bits 64 7623 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) = some 7624 := by decide +kernel

theorem wk118 : FourN.walk table bits 64 7624 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) = some 7625 := by decide +kernel

theorem wk119 : FourN.walk table bits 64 7625 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) = some 7626 := by decide +kernel

theorem wk120 : FourN.walk table bits 64 7626 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) = some 7627 := by decide +kernel

theorem wk121 : FourN.walk table bits 64 7627 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) = some 7628 := by decide +kernel

theorem wk122 : FourN.walk table bits 64 7628 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) = some 7629 := by decide +kernel

theorem wk123 : FourN.walk table bits 64 7629 (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) = some 7630 := by decide +kernel

theorem nb0_eq : (FourN.badOf cover0).length = 4 := by decide +kernel

theorem nb1_eq : (FourN.badOf cover1).length = 4 := by decide +kernel

theorem nb2_eq : (FourN.badOf cover2).length = 4 := by decide +kernel

theorem root_000 : FourN.walk table bits 64 0 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 0) = some 113 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 0 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk0

theorem root_001 : FourN.walk table bits 64 113 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 1) = some 296 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 1 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk1

theorem root_002 : FourN.walk table bits 64 296 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 2) = some 369 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 2 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk2

theorem root_003 : FourN.walk table bits 64 369 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 3) = some 378 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 0 3 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk3

theorem root_010 : FourN.walk table bits 64 378 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 0) = some 5407 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 0 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk4

theorem root_011 : FourN.walk table bits 64 5407 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 1) = some 5912 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 1 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk51

theorem root_012 : FourN.walk table bits 64 5912 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 2) = some 5919 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 2 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk54

theorem root_013 : FourN.walk table bits 64 5919 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 3) = some 5920 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 1 3 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk55

theorem root_020 : FourN.walk table bits 64 5920 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 0) = some 6295 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 0 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk56

theorem root_021 : FourN.walk table bits 64 6295 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 1) = some 6302 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 1 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk57

theorem root_022 : FourN.walk table bits 64 6302 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 2) = some 6303 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 2 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk58

theorem root_023 : FourN.walk table bits 64 6303 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 3) = some 6304 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 2 3 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk59

theorem root_030 : FourN.walk table bits 64 6304 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 0) = some 6313 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 0 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk60

theorem root_031 : FourN.walk table bits 64 6313 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 1) = some 6314 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 1 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk61

theorem root_032 : FourN.walk table bits 64 6314 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 2) = some 6315 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 2 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk62

theorem root_033 : FourN.walk table bits 64 6315 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 3) = some 6316 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 0 3 3 = (FourN.Box.mk 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk63

theorem root_100 : FourN.walk table bits 64 6316 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 0) = some 6547 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 0 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk64

theorem root_101 : FourN.walk table bits 64 6547 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 1) = some 6840 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 1 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk65

theorem root_102 : FourN.walk table bits 64 6840 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 2) = some 6847 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 2 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk66

theorem root_103 : FourN.walk table bits 64 6847 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 3) = some 6848 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 0 3 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk67

theorem root_110 : FourN.walk table bits 64 6848 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 0) = some 7479 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 0 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk68

theorem root_111 : FourN.walk table bits 64 7479 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 1) = some 7490 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 1 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk81

theorem root_112 : FourN.walk table bits 64 7490 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 2) = some 7491 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 2 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk82

theorem root_113 : FourN.walk table bits 64 7491 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 3) = some 7492 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 1 3 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk83

theorem root_120 : FourN.walk table bits 64 7492 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 0) = some 7499 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 0 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk84

theorem root_121 : FourN.walk table bits 64 7499 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 1) = some 7500 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 1 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk85

theorem root_122 : FourN.walk table bits 64 7500 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 2) = some 7501 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 2 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk86

theorem root_123 : FourN.walk table bits 64 7501 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 3) = some 7502 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 2 3 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk87

theorem root_130 : FourN.walk table bits 64 7502 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 0) = some 7503 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 0 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk88

theorem root_131 : FourN.walk table bits 64 7503 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 1) = some 7504 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 1 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk89

theorem root_132 : FourN.walk table bits 64 7504 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 2) = some 7505 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 2 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk90

theorem root_133 : FourN.walk table bits 64 7505 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 3) = some 7506 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 1 3 3 = (FourN.Box.mk 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk91

theorem root_200 : FourN.walk table bits 64 7506 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 0) = some 7579 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 0 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk92

theorem root_201 : FourN.walk table bits 64 7579 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 1) = some 7586 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 1 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk93

theorem root_202 : FourN.walk table bits 64 7586 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 2) = some 7587 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 2 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk94

theorem root_203 : FourN.walk table bits 64 7587 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 3) = some 7588 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 0 3 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk95

theorem root_210 : FourN.walk table bits 64 7588 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 0) = some 7595 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 0 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk96

theorem root_211 : FourN.walk table bits 64 7595 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 1) = some 7596 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 1 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk97

theorem root_212 : FourN.walk table bits 64 7596 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 2) = some 7597 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 2 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk98

theorem root_213 : FourN.walk table bits 64 7597 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 3) = some 7598 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 1 3 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk99

theorem root_220 : FourN.walk table bits 64 7598 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 0) = some 7599 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 0 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk100

theorem root_221 : FourN.walk table bits 64 7599 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 1) = some 7600 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 1 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk101

theorem root_222 : FourN.walk table bits 64 7600 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 2) = some 7601 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 2 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk102

theorem root_223 : FourN.walk table bits 64 7601 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 3) = some 7602 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 2 3 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk103

theorem root_230 : FourN.walk table bits 64 7602 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 0) = some 7603 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 0 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk104

theorem root_231 : FourN.walk table bits 64 7603 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 1) = some 7604 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 1 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk105

theorem root_232 : FourN.walk table bits 64 7604 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 2) = some 7605 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 2 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk106

theorem root_233 : FourN.walk table bits 64 7605 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 3) = some 7606 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 2 3 3 = (FourN.Box.mk 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk107

theorem root_300 : FourN.walk table bits 64 7606 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 0) = some 7615 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 0 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk108

theorem root_301 : FourN.walk table bits 64 7615 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 1) = some 7616 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 1 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk109

theorem root_302 : FourN.walk table bits 64 7616 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 2) = some 7617 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 2 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk110

theorem root_303 : FourN.walk table bits 64 7617 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 3) = some 7618 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 0 3 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk111

theorem root_310 : FourN.walk table bits 64 7618 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 0) = some 7619 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 0 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk112

theorem root_311 : FourN.walk table bits 64 7619 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 1) = some 7620 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 1 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk113

theorem root_312 : FourN.walk table bits 64 7620 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 2) = some 7621 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 2 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk114

theorem root_313 : FourN.walk table bits 64 7621 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 3) = some 7622 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 1 3 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk115

theorem root_320 : FourN.walk table bits 64 7622 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 0) = some 7623 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 0 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk116

theorem root_321 : FourN.walk table bits 64 7623 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 1) = some 7624 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 1 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk117

theorem root_322 : FourN.walk table bits 64 7624 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 2) = some 7625 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 2 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk118

theorem root_323 : FourN.walk table bits 64 7625 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 3) = some 7626 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 2 3 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk119

theorem root_330 : FourN.walk table bits 64 7626 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 0) = some 7627 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 0 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 77990222474978957318644826112 90369622867832760067636068352) from by decide +kernel]; exact wk120

theorem root_331 : FourN.walk table bits 64 7627 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 1) = some 7628 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 1 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 149790744753531013262794031104 174549545539238618760776515584) from by decide +kernel]; exact wk121

theorem root_332 : FourN.walk table bits 64 7628 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 2) = some 7629 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 2 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 221591267032083069206943236096 259967408249929857728816087040) from by decide +kernel]; exact wk122

theorem root_333 : FourN.walk table bits 64 7629 (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 3) = some 7630 := by
  rw [show FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) 3 3 3 = (FourN.Box.mk 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016 293391789310635125151092441088 475368975085586025561263702016) from by decide +kernel]; exact wk123

theorem run_ok : ∀ i0 i1 i2, i0 < (FourN.badOf cover0).length → i1 < (FourN.badOf cover1).length → i2 < (FourN.badOf cover2).length →
    ∃ pos pos', FourN.walk table bits 64 pos (FourN.boxOf (FourN.badOf cover0) (FourN.badOf cover1) (FourN.badOf cover2) i0 i1 i2) = some pos' := by
  intro i0 i1 i2 hi0 hi1 hi2
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  match i0, i1, i2, hi0, hi1, hi2 with
  | 0, 0, 0, _, _, _ => exact ⟨_, _, root_000⟩
  | 0, 0, 1, _, _, _ => exact ⟨_, _, root_001⟩
  | 0, 0, 2, _, _, _ => exact ⟨_, _, root_002⟩
  | 0, 0, 3, _, _, _ => exact ⟨_, _, root_003⟩
  | 0, 1, 0, _, _, _ => exact ⟨_, _, root_010⟩
  | 0, 1, 1, _, _, _ => exact ⟨_, _, root_011⟩
  | 0, 1, 2, _, _, _ => exact ⟨_, _, root_012⟩
  | 0, 1, 3, _, _, _ => exact ⟨_, _, root_013⟩
  | 0, 2, 0, _, _, _ => exact ⟨_, _, root_020⟩
  | 0, 2, 1, _, _, _ => exact ⟨_, _, root_021⟩
  | 0, 2, 2, _, _, _ => exact ⟨_, _, root_022⟩
  | 0, 2, 3, _, _, _ => exact ⟨_, _, root_023⟩
  | 0, 3, 0, _, _, _ => exact ⟨_, _, root_030⟩
  | 0, 3, 1, _, _, _ => exact ⟨_, _, root_031⟩
  | 0, 3, 2, _, _, _ => exact ⟨_, _, root_032⟩
  | 0, 3, 3, _, _, _ => exact ⟨_, _, root_033⟩
  | 1, 0, 0, _, _, _ => exact ⟨_, _, root_100⟩
  | 1, 0, 1, _, _, _ => exact ⟨_, _, root_101⟩
  | 1, 0, 2, _, _, _ => exact ⟨_, _, root_102⟩
  | 1, 0, 3, _, _, _ => exact ⟨_, _, root_103⟩
  | 1, 1, 0, _, _, _ => exact ⟨_, _, root_110⟩
  | 1, 1, 1, _, _, _ => exact ⟨_, _, root_111⟩
  | 1, 1, 2, _, _, _ => exact ⟨_, _, root_112⟩
  | 1, 1, 3, _, _, _ => exact ⟨_, _, root_113⟩
  | 1, 2, 0, _, _, _ => exact ⟨_, _, root_120⟩
  | 1, 2, 1, _, _, _ => exact ⟨_, _, root_121⟩
  | 1, 2, 2, _, _, _ => exact ⟨_, _, root_122⟩
  | 1, 2, 3, _, _, _ => exact ⟨_, _, root_123⟩
  | 1, 3, 0, _, _, _ => exact ⟨_, _, root_130⟩
  | 1, 3, 1, _, _, _ => exact ⟨_, _, root_131⟩
  | 1, 3, 2, _, _, _ => exact ⟨_, _, root_132⟩
  | 1, 3, 3, _, _, _ => exact ⟨_, _, root_133⟩
  | 2, 0, 0, _, _, _ => exact ⟨_, _, root_200⟩
  | 2, 0, 1, _, _, _ => exact ⟨_, _, root_201⟩
  | 2, 0, 2, _, _, _ => exact ⟨_, _, root_202⟩
  | 2, 0, 3, _, _, _ => exact ⟨_, _, root_203⟩
  | 2, 1, 0, _, _, _ => exact ⟨_, _, root_210⟩
  | 2, 1, 1, _, _, _ => exact ⟨_, _, root_211⟩
  | 2, 1, 2, _, _, _ => exact ⟨_, _, root_212⟩
  | 2, 1, 3, _, _, _ => exact ⟨_, _, root_213⟩
  | 2, 2, 0, _, _, _ => exact ⟨_, _, root_220⟩
  | 2, 2, 1, _, _, _ => exact ⟨_, _, root_221⟩
  | 2, 2, 2, _, _, _ => exact ⟨_, _, root_222⟩
  | 2, 2, 3, _, _, _ => exact ⟨_, _, root_223⟩
  | 2, 3, 0, _, _, _ => exact ⟨_, _, root_230⟩
  | 2, 3, 1, _, _, _ => exact ⟨_, _, root_231⟩
  | 2, 3, 2, _, _, _ => exact ⟨_, _, root_232⟩
  | 2, 3, 3, _, _, _ => exact ⟨_, _, root_233⟩
  | 3, 0, 0, _, _, _ => exact ⟨_, _, root_300⟩
  | 3, 0, 1, _, _, _ => exact ⟨_, _, root_301⟩
  | 3, 0, 2, _, _, _ => exact ⟨_, _, root_302⟩
  | 3, 0, 3, _, _, _ => exact ⟨_, _, root_303⟩
  | 3, 1, 0, _, _, _ => exact ⟨_, _, root_310⟩
  | 3, 1, 1, _, _, _ => exact ⟨_, _, root_311⟩
  | 3, 1, 2, _, _, _ => exact ⟨_, _, root_312⟩
  | 3, 1, 3, _, _, _ => exact ⟨_, _, root_313⟩
  | 3, 2, 0, _, _, _ => exact ⟨_, _, root_320⟩
  | 3, 2, 1, _, _, _ => exact ⟨_, _, root_321⟩
  | 3, 2, 2, _, _, _ => exact ⟨_, _, root_322⟩
  | 3, 2, 3, _, _, _ => exact ⟨_, _, root_323⟩
  | 3, 3, 0, _, _, _ => exact ⟨_, _, root_330⟩
  | 3, 3, 1, _, _, _ => exact ⟨_, _, root_331⟩
  | 3, 3, 2, _, _, _ => exact ⟨_, _, root_332⟩
  | 3, 3, 3, _, _, _ => exact ⟨_, _, root_333⟩
  | i + 4, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, i + 4, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, i + 4, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → (FourN.cN : ℝ) / FourN.SA ≤ FourN.G g0 g1 g2 :=
  FourN.of_check table table_ok bits 64 cover0 cover1 cover2 475368975085586025561263702016 475368975085586025561263702016 475368975085586025561263702016
    (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.FourNData
