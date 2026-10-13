/-
Riemann.fail submission — an unconditional critical-line proportion of 6730187/10000000 = 0.6730187,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW35RKF`: a table of 10345 interval cells, each certified by
an integer pipeline (Taylor enclosures of cos and sin at scale 10¹⁵, `cellN_soundZ`), and a
bisection over the gaps with 112490 leaves over the half-space
g₀ ≤ g₄; the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`.  The resulting constant is
`(9800000000·H − 17339711)/9766693039 = 0.67301870…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is
enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places the exact rational
`6730187/10000000` strictly between the record and the proved constant.

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
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder
namespace AH.AO
def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3
lemma EY (t : ℝ) : Psi t = gc 2 t + 1 := by
  unfold Psi
  split_ifs with h
  · rw [gc_of_le h]; ring
  · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring
@[simp] lemma ASN : Psi 0 = 1 := by norm_num [Psi]
lemma GI (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split_ifs with h
  · positivity
  · have : (2 : ℝ) < t := not_le.mp h
    linarith
lemma YO {p nu : ℝ} (hp : 0 ≤ p) (hnu : 0 ≤ nu) :
    2 * p - 1 + Psi p ≤ (p - nu) ^ 2 + 4 * nu := by
  have h := sq_sub_ge_gc (c := 2) hp hnu (by norm_num)
  rw [EY]
  linarith
lemma AEf (p : ℝ) :
    (p - max (p - 2) 0) ^ 2 + 4 * max (p - 2) 0 = 2 * p - 1 + Psi p := by
  unfold Psi
  rcases le_or_gt p 2 with h | h
  · rw [max_eq_right (by linarith), if_pos h]; ring
  · rw [max_eq_left (by linarith), if_neg (not_le.mpr h)]; ring
section Eigen
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
def Ep {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j
lemma Zd {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (Ep hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, Ep, Matrix.mul_diagonal]
  ring
lemma ZW {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Pmat hP.1.eigenvalues (Ep hP) = P := by
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
  rw [Zd hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
  conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl
lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (Ep hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, Ep, normSqMatrix] using hDS.2.2 j
end Eigen
section Main
variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]
lemma Cz (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp
lemma KD (V : Matrix n r 𝕜) :
    rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
        + (Fintype.card r : ℝ) := by
  rw [rtrace_specMap]
  have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := EY
  simp only [hshift]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  congr 1
  exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm
theorem Gh (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
  have hR := rank_trace_mult hm (Ep hP) hQ hb (c := 2) (by norm_num)
  rw [ZW hP] at hR
  have hx : ∀ j, hP.1.eigenvalues j * xsq (Ep hP) j = hP.1.eigenvalues j := by
    intro j; rw [xsq_eigCols hP j, mul_one]
  simp only [hx] at hR
  rw [KD V]
  have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
  linarith [hR]
theorem GA (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hsharp := Gh V hQ hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [Cz V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith
theorem YF (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hr : (V * Vᴴ).rank ≤ Fintype.card r := by
    rw [Matrix.rank_self_mul_conjTranspose]
    exact Matrix.rank_le_card_width V
  have h := rank_trace_ineq_two hP hQ hr hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [Cz V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith
theorem YN (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := GA V hV hQ hb
  have hpos : 0 ≤ rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi) := by
    rw [rtrace_specMap]
    exact Finset.sum_nonneg fun j _ => GI _
  linarith
theorem AD0 (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ)
      ≤ 2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) := by
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [Cz V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith
end Main
end AH.AO
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD AH.AO
namespace AH.Bridge
def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0
def BK (x : ℝ) : ℝ := kfun x ^ 2
def Ew (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0
def F (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * BK (Ew n g j - Ew n g i)
        else 0
def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0
def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * BK (pts g j - pts g i)
        else 0
theorem AFj (g : Fin 6 → ℝ) (i : Fin 7) : pts g i = Ew 7 g i := rfl
theorem AFl (p : ℕ) (g : Fin 6 → ℝ) : F6 p g = F 7 p g := rfl
section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def Bh (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else BK (x i - x j)
def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2
def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0
def GC (x : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, ∀ k, x i ≤ x k → x k ≤ x j → k ∈ B
lemma Bz (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
    |x i - x j| ≤ spanOf x B := by
  have hne : B.Nonempty := ⟨i, hi⟩
  unfold spanOf
  rw [dif_pos hne, abs_le]
  constructor
  · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
  · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]
lemma Dh (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
  unfold spanOf
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
  · exact le_rfl
def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)
lemma YK {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => GI _
def Bp {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))
lemma Cj {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ Bp hM B :=
  YK _
end Blocks
def GF (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)
def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)
theorem YW (c : ℝ) (m p : ℕ) : Phi c m p = GF 7 c m p := by
  unfold Phi GF
  norm_num
section BlockLevel
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
def Ci (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)
def P₁ (c : ℝ) : Matrix d d ℂ := Ci D c * (Ci D c)ᴴ
def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c
def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Ci D c)ᴴ * Ci D c
lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _
lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
  isHermitian_conjTranspose_mul_self _
lemma gramS₁_posSemidef (c : ℝ) : (gramS₁ D c).PosSemidef :=
  posSemidef_conjTranspose_mul_self _
lemma Jx (c : ℝ) : (D.blockP c).IsHermitian :=
  ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _
lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
  ((Jx D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1
lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
  unfold Q'; abel
end BlockLevel
section Concrete
open Classical
def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atD T
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
def FI (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)
def aL2 : ℝ := P.a T * P.L T ^ 2
def CJ : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj
def retained : Finset (ZI Z T) :=
  (CJ Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ FI P T z ∧ FI P T z ≤ (P.d T : ℝ) - P.L T ^ 2
lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (CJ Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1
def toS₁ : retained Z P T → (CJ Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩
lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (CJ Z P T).S₁ → ZI Z T) h)
def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (CJ Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)
lemma BZ : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _
lemma Eh : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _
def Ec : ℝ := defect (BZ Z P T)
def xret : retained Z P T → ℝ := fun z => FI P T (z.1 : ℂ)
lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (CJ Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (CJ Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h
lemma DG (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
  intro z z' h
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  unfold xret FI at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
    have h1 := (div_left_inj' hpi.ne').mp h
    have h2 := mul_left_cancel₀ hL.ne' h1
    linarith
  apply Subtype.ext; apply Subtype.ext
  exact Complex.ext (by rw [hz, hz']) him
end Concrete
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace AH.Bridge
lemma o8 (x : ℝ) : Kfun (-x) = Kfun x := by
  unfold Kfun
  simp only [mul_neg, neg_mul, Real.cos_neg]
lemma p7 (x : ℝ) : kfun (-x) = kfun x := by
  unfold kfun; rw [o8]
lemma q5 (x : ℝ) : BK (-x) = BK x := by
  unfold BK; rw [p7]
lemma Jk (a b : ℝ) : BK (a - b) = BK (b - a) := by
  rw [← q5, neg_sub]
lemma Bq (x : ℝ) : 0 ≤ BK x := sq_nonneg _
lemma C5 {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
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
lemma IT (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
  refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro t ht
    rw [abs_mul, abs_of_nonneg (C5 ht)]
    calc Real.cos (Real.sqrt 2 * t) * |Real.cos (2 * Real.pi * x * t)|
        ≤ Real.cos (Real.sqrt 2 * t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (C5 ht)
      _ = Real.cos (Real.sqrt 2 * t) := mul_one _
lemma Gq (x : ℝ) : |kfun x| ≤ 1 := by
  unfold kfun
  rw [abs_div]
  rcases eq_or_ne (Kfun 0) 0 with h | h
  · rw [h, abs_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact (IT x).trans (le_abs_self _)
lemma AFk (x : ℝ) : BK x ≤ 1 := by
  unfold BK
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (Gq x)
section Sorted
variable {m : ℕ}
def Bl (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0
lemma BT (y : Fin m → ℝ) {n : ℕ} (h : n < m) : Bl y n = y ⟨n, h⟩ := by
  unfold Bl; rw [dif_pos h]
lemma Bw {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    Bl y a ≤ Bl y b := by
  rw [BT y (lt_of_le_of_lt hab hb), BT y hb]
  exact hy.monotone (Fin.mk_le_mk.mpr hab)
def Br (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
  fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)
lemma Wb {N k : ℕ} (hk : k ≤ N) : ((range N).filter fun j => j < k) = range k := by
  ext j
  simp only [mem_filter, mem_range]
  omega
lemma Dm (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) (k : Fin n) :
    Ew n (Br n Y i) k = Y (i + k) - Y i := by
  have hk : (k : ℕ) ≤ n - 1 := by have := k.2; omega
  unfold Ew Br
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < (k : ℕ) then Y (i + (j + 1)) - Y (i + j) else 0) (n - 1),
    ← sum_filter, Wb hk]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (k : ℕ)
  simpa using this
lemma Xw (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    ∑ j, Br n Y i j = Y (i + (n - 1)) - Y i := by
  unfold Br
  rw [Fin.sum_univ_eq_sum_range (fun j => Y (i + (j + 1)) - Y (i + j)) (n - 1)]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (n - 1)
  simpa using this
lemma YU (n p : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    F n p (Br n Y i) = (1 / (p : ℝ)) * (Y (i + (n - 1)) - Y i)
      + ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then
            (2 / ((n : ℝ) - (((b : ℕ) - (a : ℕ) : ℕ) : ℝ))) * BK (Y (i + b) - Y (i + a))
          else 0 := by
  unfold F
  rw [Xw]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [Dm, Dm,
    show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
lemma Fy (f : ℕ → ℝ) (d N : ℕ) :
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
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace AH.Bridge
section PsiConvex
open AH.AO
lemma Ja {s x : ℝ} (hs : s ≤ 2) : 2 * (s - 1) * x - (s ^ 2 - 1) ≤ Psi x := by
  unfold Psi
  split_ifs with h
  · nlinarith [sq_nonneg (x - s)]
  · have hx : 2 < x := not_le.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0 : ℝ) ≤ 2 * x - 2 - s)]
lemma YI (x : ℝ) : 2 * (min x 2 - 1) * x - ((min x 2) ^ 2 - 1) = Psi x := by
  unfold Psi
  rcases le_or_gt x 2 with h | h
  · rw [min_eq_left h, if_pos h]; ring
  · rw [min_eq_right h.le, if_neg (not_le.mpr h)]; ring
theorem Ju : ConvexOn ℝ Set.univ Psi := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hz
  set t := min z 2 with ht
  have ht2 : t ≤ 2 := min_le_right _ _
  have hx := Ja (x := x) ht2
  have hy := Ja (x := y) ht2
  have hsplit : 2 * (t - 1) * z - (t ^ 2 - 1)
      = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := by
    rw [hz]; linear_combination (t ^ 2 - 1) * hab
  calc Psi z = 2 * (t - 1) * z - (t ^ 2 - 1) := (YI z).symm
    _ = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := hsplit
    _ ≤ a * Psi x + b * Psi y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
end PsiConvex
section Entries
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma Eb (Y : Matrix κ ι 𝕜) (j : κ) :
    RCLike.re ((Y * Yᴴ) j j) = ∑ i, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
  simp
lemma Cv (Y : Matrix κ ι 𝕜) (i : ι) :
    RCLike.re ((Yᴴ * Y) i i) = ∑ j, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp
lemma DY (Y : Matrix κ ι 𝕜) (d : ι → ℝ) (j : κ) :
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
lemma DB {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (i : ι) :
    ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 = 1 := by
  have h := Cv (hM.eigenvectorUnitary : Matrix ι ι 𝕜) i
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2] at h
  simpa using h.symm
end Entries
section Mix
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def Bn {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
  ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
lemma aO {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) :
    0 ≤ Bn hM g i :=
  Finset.sum_nonneg fun _ _ => by positivity
lemma IU {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) (i : ι) : Bn hM g i ≤ 1 := by
  unfold Bn
  calc ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
      = ∑ k ∈ univ.image g, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        (Finset.sum_image (f := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2)
          (s := univ) (g := g) hg.injOn).symm
    _ ≤ ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = 1 := DB hM i
lemma E5 {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (β : ι → κ) (i : ι) :
    ∑ b, Bn hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i = 1 := by
  unfold Bn
  have h : ∀ b : κ, ∑ j : (univ.filter fun i => β i = b),
      ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (j : ι) i‖ ^ 2
        = ∑ j ∈ univ.filter (fun i => β i = b), ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2 :=
    fun b => Finset.sum_coe_sort (univ.filter fun i => β i = b)
      (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)
  simp only [h]
  rw [Finset.sum_fiberwise univ β (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)]
  exact DB hM i
theorem Er {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) :
    ∃ S : κ → ι → ℝ, (∀ j i, 0 ≤ S j i) ∧ (∀ j, ∑ i, S j i = 1)
      ∧ (∀ i, ∑ j, S j i = Bn hM g i)
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
    have h := Eb Y j
    rw [hYY] at h
    simpa using h.symm
  · intro i
    show ∑ j, ‖Y j i‖ ^ 2 = Bn hM g i
    have h1 := Cv Y i
    have h2 := Cv Ug i
    rw [hYtY] at h1
    rw [← h1, h2]
    rfl
  · intro j
    show hP.eigenvalues j = ∑ i, ‖Y j i‖ ^ 2 * hM.eigenvalues i
    have h := DY Y hM.eigenvalues j
    rw [← hdiag, diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re] at h
    exact h
end Mix
section Pinching
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
theorem DQ {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ j, f ((hM.submatrix g).eigenvalues j)
      ≤ ∑ i, Bn hM g i * f (hM.eigenvalues i) := by
  obtain ⟨S, hS0, hSrow, hScol, hSeig⟩ := Er hM hg
  calc ∑ j, f ((hM.submatrix g).eigenvalues j)
      = ∑ j, f (∑ i, S j i * hM.eigenvalues i) := by simp only [hSeig]
    _ ≤ ∑ j, ∑ i, S j i * f (hM.eigenvalues i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := hf.map_sum_le (t := Finset.univ) (w := S j) (p := hM.eigenvalues)
          (fun i _ => hS0 j i) (hSrow j) (fun i _ => Set.mem_univ _)
        simpa only [smul_eq_mul] using h
    _ = ∑ i, (∑ j, S j i) * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, Bn hM g i * f (hM.eigenvalues i) := by simp only [hScol]
theorem Fk {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ i, f (hM.eigenvalues i) := by
  calc ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ b, ∑ i, Bn hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i
            * f (hM.eigenvalues i) :=
        Finset.sum_le_sum fun b _ => DQ hM Subtype.val_injective hf
    _ = ∑ i, (∑ b, Bn hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i)
            * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, f (hM.eigenvalues i) := by simp only [E5, one_mul]
theorem Dk {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    {g : κ → ι} (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∑ j, f ((hM.submatrix g).eigenvalues j) ≤ ∑ i, f (hM.eigenvalues i) :=
  (DQ hM hg hf).trans <| Finset.sum_le_sum fun i _ => by
    calc Bn hM g i * f (hM.eigenvalues i) ≤ 1 * f (hM.eigenvalues i) :=
          mul_le_mul_of_nonneg_right (IU hM hg i) (hf0 _)
      _ = f (hM.eigenvalues i) := one_mul _
theorem Fv {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, rtrace (specMap (hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)) f)
      ≤ rtrace (specMap hM f) := by
  simp only [rtrace_specMap]
  exact Fk hM hf β
theorem Fd {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ t, 0 ≤ f t) :
    rtrace (specMap (hM.submatrix g) f) ≤ rtrace (specMap hM f) := by
  rw [rtrace_specMap, rtrace_specMap]
  exact Dk hM hg hf hf0
end Pinching
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Filter Asymptotics Topology Real RHLinalg
open Zeta23 Zeta23.ThmD Zeta23.Assembly
namespace AH.Bridge
theorem KE {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
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
theorem Xo (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
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
    have hA := KE hT0 hTl haposD hLpos hcoreT
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
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.Bridge
open Classical
section GramEntry
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
lemma WO (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (CJ Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
  simp only [CJ, blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]
lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
    gram Z P T z z' =
      (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
        P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hentry : ∀ a b : (CJ Z P T).S₁, gramS₁ (CJ Z P T) (aL2 P T) a b
      = ∑ k, star (Ci (CJ Z P T) (aL2 P T) k a) * Ci (CJ Z P T) (aL2 P T) k b := by
    intro a b
    simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
  unfold gram
  rw [Matrix.submatrix_apply, hentry]
  have e : ∀ k : Fin (P.d T),
      star (Ci (CJ Z P T) (aL2 P T) k (toS₁ Z P T z))
        * Ci (CJ Z P T) (aL2 P T) k (toS₁ Z P T z')
      = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
          * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
    intro k
    have h1 : (CJ Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
      WO Z P T hreal hz k
    have h2 : (CJ Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
      WO Z P T hreal hz' k
    simp only [Ci]
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
lemma En : (P.atD T).phiHatR T = AdmWindow.vHatR (P.phiD T) := atD_phiHatR hP T
lemma Xt : PhiHatReal T (P.atD T) := fun r => GzGp.phiHat_ofReal _ T r
lemma YQ (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.atD T).phiHatR T r| * r ^ 2 ≤ cDT P.ϱ P.lam / P.w := by
  rw [En hP T]
  exact (admWindow_params hP h8).abs_vHatR_mul_sq_le r
lemma Zn (h8 : 8 * P.w ≤ P.L T) (τ τ' : ℝ) :
    HasSum (fun k : ℤ => (P.atD T).phiHatR T (τ - (P.atD T).tau T k)
        * (P.atD T).phiHatR T (τ' - (P.atD T).tau T k))
      (P.L T * AdmWindow.VPhiR (P.phiD T) (τ - τ')) := by
  have h := (admWindow_params hP h8).hasSum_vHatR_mul T τ τ'
  simp only [En hP T, atD_tau_eq]
  exact h
end Window
section Tail
lemma Gm {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
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
lemma Jh {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj := PrimeSide.rho_le_majorant hF hT hτ
  have hW1 := Gm hF h1
  have hW2 := Gm hF h2
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
lemma FJ {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
    (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
    |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
  have hρ := Jh hF hT h1 h2 h3
  have hρ' := Jh hF hT h1' h2' h3'
  calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
      ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
    _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
        gcongr
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring
end Tail
section Limit
lemma Jr : Kfun 0 = aStar 1 := by
  simp [Kfun, aStar, vStar]
lemma JO {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2)) :
    0 < Real.cos (Real.sqrt 2 * t) := by
  apply Real.cos_pos_of_mem_Ioo
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [mul_nonneg h0 (by linarith [ht.1] : (0:ℝ) ≤ t + 1 / 2),
    mul_nonneg h0 (by linarith [ht.2] : (0:ℝ) ≤ 1 / 2 - t)]
lemma YH : 0 < Kfun 0 := by
  unfold Kfun
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
  · intro t ht
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact JO ht
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
          rw [abs_mul, abs_of_nonneg (C5 ht)]
          exact mul_le_of_le_one_right (C5 ht) (Real.abs_cos_le_one _)
lemma Vq {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
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
lemma Vr {L : ℝ} : Integrable (sharpW 1 L) := by
  unfold sharpW
  rw [integrable_indicator_iff measurableSet_Icc]
  have hc : Continuous fun u : ℝ => vStar 1 (u / L) := by unfold vStar; fun_prop
  exact hc.integrableOn_Icc
lemma Gd {L : ℝ} (hL : 0 < L) (x : ℝ) :
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
lemma FL {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
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
lemma FK (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) - P.L T * Kfun x| ≤ 2 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (P.phiD T) r = ∫ u, P.phiD T u ^ 2 * Real.cos (r * u) :=
    Vq (hW.integrable_pow two_pos) r
  have hS : ∫ u, sharpW 1 (P.L T) u * Real.cos (r * u) = P.L T * Kfun x :=
    Gd hL x
  have hL1 : ∫ u, |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u| ≤ 2 * P.w :=
    integral_abs_phiDsq_sub_sharp hP.taper hP.lam_pos hP.lam_le_one hw (by linarith)
  rw [hlam] at hL1
  rw [hV, ← hS]
  exact (FL (hW.integrable_pow two_pos) Vr r).trans hL1
lemma Ek :
    |(P.atD T).a T * P.L T - P.L T * Kfun 0| ≤ 4 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have h : |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - aStar P.lam| ≤ 4 * P.w / P.L T :=
    aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8
  rw [hlam, ← Jr] at h
  have ha : (P.atD T).a T = (P.L T)⁻¹ * ∫ u, P.phiD T u ^ 2 := by rw [atD_a_eq_av hP]; rfl
  rw [ha]
  have e : (P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) * P.L T - P.L T * Kfun 0
      = ((P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0) * P.L T := by ring
  rw [e, abs_mul, abs_of_pos hL]
  calc |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0| * P.L T ≤ 4 * P.w / P.L T * P.L T :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = 4 * P.w := by field_simp
lemma GJ (h4π : 4 * Real.pi * P.w ≤ P.L T) (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) / ((P.atD T).a T * P.L T) - kfun x|
      ≤ 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have h1 := FK hP hlam h8 x
  have h2 := Ek hP hlam h8
  have hK0 : 0 < Kfun 0 := YH
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
lemma J9 {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    {z : ZI Z T} (hz : z ∈ retained Z P T) :
    P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
  unfold FI at h1 h2
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
lemma Zj {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
    PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'
      = ∑ k : Fin ((P.atD T).d T), (P.atD T).phiHatR T (γ - (P.atD T).tau T k)
          * (P.atD T).phiHatR T (γ' - (P.atD T).tau T k) := by
  rw [En hP T]; rfl
lemma AEN {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      = P.L T * AdmWindow.VPhiR (P.phiD T) (γ - γ') := rfl
theorem YL {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (hT : 0 < T)
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
  rw [gram_apply Z (P.atD T) T (Xt hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Zj hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'
  obtain ⟨g1, g2, g3⟩ := J9 (Z := Z) (P := P.atD T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := J9 (Z := Z) (P := P.atD T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    FJ hF hT g1 g2 g3 g1' g2' g3'
  have hx : 2 * Real.pi * (xret Z (P.atD T) T z - xret Z (P.atD T) T z') / P.L T = γ - γ' := by
    unfold xret FI
    rw [Params.atD_L]
    field_simp
    ring
  have hlim := GJ hP hlam h8 h4π (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
  rw [hx] at hlim
  set A : ℝ := (P.atD T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (P.phiD T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ' = P.L T * V := AEN T γ γ'
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
lemma F7 (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
  unfold ZeroConfig.N
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exact Z.one_le_mult ρ hρ.1
lemma Jm {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
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
lemma Dp {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
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
    _ ≤ n * A₀ * Real.log (|a| + n + 3) := Jm Z hA₀ hloc a n
    _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr
end Strips
section StripInclusion
lemma GO (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
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
    have hzS : z ∈ (CJ Z P T).S₁ := by
      simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
    by_cases hx : P.L T ^ 2 ≤ FI P T z ∧ FI P T z ≤ (P.d T : ℝ) - P.L T ^ 2
    · left; left
      rw [Finset.mem_coe, hR, Finset.mem_map]
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · left; right
        refine ⟨hρc, hT1, ?_⟩
        push Not at hx
        unfold FI at hx
        have h1 := (div_lt_iff₀ hπ).mp hx
        have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
        have := lt_of_mul_lt_mul_left this hL.le
        show ρ.im ≤ T + ℓ
        linarith
      · right
        refine ⟨hρc, ?_, hT2⟩
        push Not at hx
        unfold FI at hx
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
  have hlo := F7 Z T (T + ℓ)
  have hhi := F7 Z (2 * T - ℓ') (2 * T)
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
lemma o7 (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
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
  have h1 := Dp Z hA₀ hloc T hℓ0
  have h2 := Dp Z hA₀ hloc (2 * T - ℓ') hℓ'0
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
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide
namespace AH.Bridge
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
def EW (c : ℝ) : Matrix d d ℂ :=
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
lemma Jp {c : ℝ} (hc : 0 < c) : (EW D c).PosSemidef := by
  unfold EW
  refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
  simpa using this
lemma WH {c : ℝ} (hc : 0 < c) : (EW D c).rank ≤ D.s₂ := by
  unfold EW
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp [ZeroBlockData.s₂]
lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
    P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
  ext k l
  simp only [P₁, Ci, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
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
    Q' D c = EW D c + D.blockQ c := by
  unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart EW
  rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
  abel
theorem WI (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hR := Jp D hc
  have hH : (EW D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
  rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
  calc posIndex hH
      ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := by
        rw [posIndex_eq_rank_of_posSemidef hR]
        exact Nat.add_le_add (WH D hc) (D.posIndex_blockQ_le Pr hc)
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide AH.AO
namespace AH.Bridge
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
lemma Jw {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.S₁) :
    ∑ k, ‖Ci D c k z‖ ^ 2 ≤ 1 := by
  have hz : (z : ι) ∈ D.onLine := by
    have := z.2
    simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at this
    exact (D.mem_onLine).mpr this.1
  have hs : ∀ k, ‖Ci D c k z‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
    intro k
    simp only [Ci]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
      Real.sq_sqrt hc.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hc]
  exact hPois z hz
theorem ZP (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ)
      + defect (gramS₁_isHermitian D c) ≤ (D.s₁ : ℝ) := by
  classical
  have hb := WI D Pr hc
  have h := GA (Ci D c) (Jw D hc hPois) (Q'_isHermitian D c) hb
  have e : Ci D c * (Ci D c)ᴴ + Q' D c = D.blockP c + D.blockQ c := P₁_add_Q' D c
  rw [e] at h
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card D.S₁ : ℝ) = D.s₁ := by rw [Fintype.card_coe]; rfl
  have hdef : defect (gramS₁_isHermitian D c)
      = rtrace (specMap (isHermitian_conjTranspose_mul_self (Ci D c)) Psi) := rfl
  rw [hcard] at h
  push_cast at h
  linarith
end AH.Bridge
end
noncomputable section
open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.Bridge
theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Ec Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ε) * (Z.N T (2 * T) : ℝ) + Ec Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by
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
  have h := Xo Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
    (fun T => Ec Z (mtParams T) T) h7
  intro ε hε
  have h' := h ε hε
  have hHD : HD 1 = 2 - (cStar P.lam)⁻¹ := by rw [hlam, HD, one_div]
  rw [hHD]
  exact h'
end AH.Bridge
end
noncomputable section
open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.Bridge
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
  have h := YL hP hlam hT h8 h4π hF Z z z'
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
  have hincl := GO Z (mtParams T) T hLpos
  have hstrips := o7 Z hA₀ hloc hT1 hL1 hLT hlogT
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
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def DJ (n r : ℕ) : ℝ := 2 / ((n : ℝ) - (r : ℝ))
lemma FZ {m : ℕ} (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    Bh x univ = ∑ r : Fin m × Fin m,
      if r.1 = r.2 then 0 else BK ((univ.image x).orderEmbOfFin hS r.1
        - (univ.image x).orderEmbOfFin hS r.2) := by
  classical
  set S := univ.image x with hSdef
  set y := S.orderEmbOfFin hS with hydef
  have hy : Function.Injective y := y.injective
  have hSy : univ.image y = S := by
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin S hS
  unfold Bh
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else BK (x i - x j))
      = (if x i = x j then 0 else BK (x i - x j)) := by
    intro i j; simp [hx.eq_iff]
  simp_rw [h1]
  have e1 : ∀ i : ι, ∑ j, (if x i = x j then (0 : ℝ) else BK (x i - x j))
      = ∑ t ∈ S, (if x i = t then 0 else BK (x i - t)) := fun i =>
    (sum_image (f := fun t => if x i = t then (0 : ℝ) else BK (x i - t))
      (fun a _ b _ h => hx h)).symm
  simp_rw [e1]
  rw [← sum_image (f := fun s => ∑ t ∈ S, (if s = t then (0 : ℝ) else BK (s - t)))
    (fun a _ b _ h => hx h)]
  rw [← hSdef, ← hSy, sum_image (fun a _ b _ h => hy h)]
  simp_rw [sum_image (fun a _ b _ h => hy h)]
  simp only [hy.eq_iff]
  exact (Fintype.sum_prod_type' (f := fun k l => if k = l then (0 : ℝ) else BK (y k - y l))).symm
lemma IL {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (x : ι → ℝ)
    (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          DJ n ((b : ℕ) - (a : ℕ))
            * BK (Bl ((univ.image x).orderEmbOfFin hS) (i + b)
                - Bl ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ Bh x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := Bl y with hYdef
  have hm0 : 0 < m := by omega
  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    DJ n ((t.2.2 : ℕ) - (t.2.1 : ℕ)) * BK (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        DJ n ((b : ℕ) - (a : ℕ)) * BK (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      DJ n ((b : ℕ) - (a : ℕ)) * BK (Y (i + b) - Y (i + a)) else 0)).symm
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
  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q), f t = DJ n r * BK (Y q.2 - Y q.1) := by
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
    have hcoef : 0 ≤ DJ n r := by
      unfold DJ; apply div_nonneg (by norm_num); linarith
    have hcardR : ((T.filter (fun t => φ t = q)).card : ℝ) ≤ (n : ℝ) - (r : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hq3.le] at this
    calc ((T.filter (fun t => φ t = q)).card : ℝ) * (DJ n r * BK (Y q.2 - Y q.1))
        ≤ ((n : ℝ) - (r : ℝ)) * (DJ n r * BK (Y q.2 - Y q.1)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg hcoef (Bq _))
      _ = 2 * BK (Y q.2 - Y q.1) := by
          have h7 : (n : ℝ) - (r : ℝ) ≠ 0 := by linarith
          unfold DJ
          field_simp
  refine (sum_le_sum hfib).trans ?_
  rw [FZ x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else BK (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      BT y hq1m, BT y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), Jk]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      BT y hq1m, BT y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * BK (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
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
    · exact Bq _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r
theorem ZK {c : ℝ} {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ Bh x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := Bl y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ F n p (Br n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (Bw hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), F n p (Br n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [YU] at hsum
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), (Y (i + (n - 1)) - Y i)
      ≤ ((n : ℝ) - 1) * spanOf x univ := by
    rw [Fy]
    have hterm : ∀ i ∈ range (n - 1), Y (m - (n - 1) + i) - Y i ≤ Y (m - 1) - Y 0 := by
      intro i hi
      rw [mem_range] at hi
      have h1 := Bw hymono (a := m - (n - 1) + i) (b := m - 1) (by omega) (by omega)
      have h2 := Bw hymono (a := 0) (b := i) (by omega) (by omega)
      linarith
    have hspan : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, BT y (by omega : m - 1 < m), BT y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (Bz x (mem_univ i₀) (mem_univ j₀))
    calc ∑ i ∈ range (n - 1), (Y (m - (n - 1) + i) - Y i)
        ≤ ∑ i ∈ range (n - 1), (Y (m - 1) - Y 0) := sum_le_sum hterm
      _ = ((n : ℝ) - 1) * (Y (m - 1) - Y 0) := by
          rw [sum_const, card_range, nsmul_eq_mul, hcastn]
      _ ≤ ((n : ℝ) - 1) * spanOf x univ := by nlinarith
  have hquad := IL hn hm x hx hS
  simp only [DJ] at hquad
  rw [← hydef, ← hYdef] at hquad
  have hp' : 0 ≤ 1 / (p : ℝ) := by positivity
  calc c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ _ := hsum
    _ ≤ (1 / (p : ℝ)) * (((n : ℝ) - 1) * spanOf x univ) + Bh x univ := by
        gcongr
    _ = Bh x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by ring
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open AH.AO
namespace AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Vt {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp
lemma Wd {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun t => t - 1) = A - 1 := by
  have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
  rw [h, specMap_sub, specMap_id, Vt]
lemma El (A : Matrix ι ι ℂ) :
    offDiagSqOn A univ ≤ frobSq (A - 1) := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  unfold offDiagSqOn
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs with h
  · positivity
  · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]
theorem FQ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    min 1 (offDiagSqOn A univ) ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
  ·
    have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
      sum_congr rfl fun i _ => by simp [Psi, hall i]
    have hfrob := frobSq_specMap hA (fun t => t - 1)
    rw [Wd] at hfrob
    rw [hsum, ← hfrob]
    exact (min_le_right _ _).trans (El A)
  ·
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (min_le_left _ _).trans ?_
    calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
          unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
      _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
          single_le_sum (fun j _ => GI (hA.eigenvalues j)) (mem_univ i)
theorem GQ {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    min 1 (offDiagSqOn G univ) ≤ defect hG.1 :=
  FQ hG.1
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma JR {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (h : |b - a| ≤ δ) : a ^ 2 - 2 * δ ≤ b ^ 2 := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_or_gt a b with hab | hab
  · nlinarith
  · rcases le_or_gt δ a with hδa | hδa
    · nlinarith
    · nlinarith
lemma Dl {g : ℂ} {t δ : ℝ} (h : ‖g - (kfun t : ℂ)‖ ≤ δ) :
    BK t - 2 * δ ≤ ‖g‖ ^ 2 := by
  have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
  have htri : abs (‖g‖ - |kfun t|) ≤ δ := by
    rw [← hk]; exact (abs_norm_sub_norm_le g _).trans h
  have := JR (abs_nonneg _) (Gq t) (norm_nonneg g) htri
  rw [sq_abs] at this
  exact this
lemma DN (G : Matrix ι ι ℂ) (B : Finset ι) :
    offDiagSqOn (G.submatrix (Subtype.val : B → ι) Subtype.val) univ = offDiagSqOn G B := by
  unfold offDiagSqOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [submatrix_apply, Subtype.ext_iff]
lemma EO (x : ι → ℝ) (B : Finset ι) :
    Bh (fun i : B => x i) univ = Bh x B := by
  unfold Bh
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [Subtype.ext_iff]
lemma F9 (x : ι → ℝ) (B : Finset ι) :
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
    exact Dh x B
theorem Zm {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ Bp hG.1 B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
  classical
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have hS12 : min 1 (offDiagSqOn G B) ≤ Bp hG.1 B := by
    have h := GQ (hG.submatrix (Subtype.val : B → ι))
    rw [DN] at h
    exact h
  have hoff : Bh x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact Dl (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        = Bh x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold Bh
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ Bh x B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := ZK hn hp hCert hm hcard (fun i : B => x i) hinj
    rw [EO] at h
    have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
    have := mul_le_mul_of_nonneg_left (F9 x B) hp'
    linarith
  have hspan := Dh x B
  have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith [mul_nonneg hp' hspan]
  · rw [min_eq_right h1.le] at hS12
    nlinarith [mul_nonneg hp' hspan]
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem Dw {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
    ∑ b, Bp hM (univ.filter fun i => β i = b) ≤ defect hM := by
  unfold Bp defect
  exact Fv hM Ju β
theorem J8 {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
    defect (hM.submatrix f) ≤ defect hM := by
  unfold defect
  exact Fd hM hf Ju AH.AO.GI
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.Bridge
section Abstract
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma GZ {m s s' k : ℕ} (_hm : 0 < m) (h : s % m = s' % m)
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
def D6 (n m j k : ℕ) : ℕ :=
  if h : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m then h.choose else n
lemma Jb (n m j k : ℕ) : D6 n m j k ≤ n := by
  unfold D6
  split_ifs with h
  · have := h.choose_spec.1; omega
  · exact le_rfl
lemma Fz {n m j k s : ℕ} (hm : 0 < m) (hs : s + m ≤ n) (hj : s % m = j) :
    D6 n m j k = s ↔ (s ≤ k ∧ k < s + m) := by
  unfold D6
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
    exact GZ hm (h2.trans hj.symm) h3 hk
theorem Ih (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : 1 ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → GC x B → A ≤ Dblk B + q * spanOf x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ ≤ m * Dtot := by
  classical
  set n := Fintype.card ι with hndef
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := Dh x (univ : Finset ι)
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
  set Y := Bl y with hYdef
  have hpos_lt : ∀ i, pos i < n := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [BT y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [BT y (e.symm i).2, BT y (e.symm i').2, Fin.eta, Fin.eta,
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
  have hintB : ∀ s, GC x (B s) := by
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
      exact Bw hymono (by omega) (by omega)
    have h2 : Y s ≤ (B s).inf' hne x := by
      apply le_inf'
      intro i hi
      rw [hmemB] at hi
      rw [hxY]
      exact Bw hymono (by omega) (hpos_lt i)
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
      rw [hYdef, BT y hi', BT y (by omega : i < n), ← ha, ← hb]
      exact (le_abs_self _).trans (Bz x (mem_univ a) (mem_univ b))
    calc ∑ s ∈ St, spanOf x (B s)
        ≤ ∑ s ∈ St, (Y (s + (m - 1)) - Y s) :=
          sum_le_sum fun s hs => hspanB s ((hmemSt s).mp hs)
      _ = ∑ i ∈ range (m - 1), (Y (n - m + 1 + i) - Y i) := Fy Y (m - 1) (n - m + 1)
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
            ⟨D6 n m j (pos i), Nat.lt_succ_of_le (Jb n m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ n) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact Fz hm0 hs hj
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
lemma WJ (Z : ZeroConfig) (P : Params) (T : ℝ) :
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
  calc spanOf (xret Z (mtParams T) T) univ ≤ ((mtParams T).d T : ℝ) := WJ Z _ T
    _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]
end Analytic
end AH.Bridge
end
noncomputable section
open Filter
open Zeta23.ThmD
namespace AH.Bridge
lemma G8 {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith
theorem Zb {N N0 : ℝ → ℝ} {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (GF n c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := G8 hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : GF n c m p
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith
theorem Xy : Phi (19 / 5000) 269 3000 = (1345000 * HD 1 - 2680) / 1340003 := by
  unfold Phi
  norm_num
  field_simp
  ring
theorem Phi_paper' :
    Phi (19 / 5000) 269 3000
      = (1345000 * (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹))
          - 2680) / 1340003 := by
  rw [Xy, HD_one]
theorem AEO : Phi (34697 / 10000000) 294 3400
    = (520625000 * HD 1 - 915625) / 518855453 := by
  unfold Phi
  norm_num
  field_simp
  ring
theorem o9 : GF 8 (41763 / 10000000) 246 3200
    = (2460000000 * HD 1 - 5359375) / 2450018643 := by
  unfold GF
  norm_num
  field_simp
  ring
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.Bridge
open Classical
def P₀ : Params := paramsOf stdProfile 1
lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
  (tendsto_L P₀_valid).eventually_gt_atTop 0
theorem eventually_h7 (Z : ZeroConfig) :
    ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Ec Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
  filter_upwards [eventually_w8 P₀_valid, eventually_w4pi P₀_valid] with T h8 h4π
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (aD_range_of P₀_valid h8 h4π).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := poissonSqD P₀_valid h8
  have h7 := ZP (CJ Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj phiHatReal hPois)
  have hD : Ec Z P T ≤ defect (gramS₁_isHermitian (CJ Z P T) (aL2 P T)) :=
    J8 (gramS₁_isHermitian (CJ Z P T) (aL2 P T)) (toS₁ Z P T)
      (toS₁_injective Z P T)
  have hA : P.hat T (Z.Az P T) = (CJ Z P T).blockP (aL2 P T) + (CJ Z P T).blockQ (aL2 P T) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : (Z.NIprime T : ℝ) = ((CJ Z P T).Ncount : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs : (Z.s1 T : ℝ) = ((CJ Z P T).s₁ : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hA, hN, hs]
  linarith [h7, hD]
theorem block_bound_eventually (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ Bp (BZ Z (mtParams T) T) B
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
  · linarith [Cj (BZ Z (mtParams T) T) B]
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
      exact hclose i j ((Bz x hi hj).trans hR)
    have h13 := Zm hn hm hp hCert hA0 x (Eh Z (mtParams T) T) B hB
      (DG Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
theorem oz (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
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
  have h15 := Ih (xret Z (mtParams T) T) (DG Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (Bp (BZ Z (mtParams T) T))
    (Ec Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    (((n : ℝ) - 1) / (p : ℝ))
    hA' hq0 (Cj _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => Dw (BZ Z (mtParams T) T) κ β)
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
  set D : ℝ := Ec Z (mtParams T) T with hDdef
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
theorem Jg (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (GF n c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := Zb (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) hn hm hA0 (by
      have := oz zetaZeroConfig paperInputs_zeta hn hm hp hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)
theorem F8 (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h7 : ((7 : ℕ) : ℝ) - 1 = 6 := by norm_num
  rw [YW]
  refine Jg 7 c m p (by norm_num) hm hp hc (fun g hg => ?_) ?_
  · exact le_of_le_of_eq (hCert g hg) (AFl p g)
  · rw [h7]; exact hA0
theorem Zi
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * HD 1 - 2680) / 1340003 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Xy]
  exact F8 (19 / 5000) 269 3000 (by norm_num) (by norm_num) (by norm_num) hCert
    (by norm_num)
lemma DM : ∀ᶠ T in atTop, 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0
theorem Ip
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * HD 1 - 915625) / 518855453 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← AEO]
  exact F8 (34697 / 10000000) 294 3400 (by norm_num) (by norm_num) (by norm_num)
    hCert (by norm_num)
theorem YD
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * HD 1 - 915625) / 518855453 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := Ip hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp DM
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1
theorem Vm
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5359375) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← o9]
  exact Jg 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hCert (by norm_num)
theorem Ze
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5359375) / 2450018643 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := Vm hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp DM
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1
end AH.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace AH.AY
open AH.Bridge
structure WCert (n : ℕ) where
  a : Fin n → Fin n → ℝ
  b : Fin (n - 1) → ℝ
variable {n : ℕ}
def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
  ∑ r, W.b r * g r
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then W.a i j * BK (Ew n g j - Ew n g i) else 0
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
def DE (n p : ℕ) : WCert n :=
  ⟨fun i j => 2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)), fun _ => 1 / (p : ℝ)⟩
theorem aZ (n p : ℕ) (g : Fin (n - 1) → ℝ) : Fw (DE n p) g = F n p g := by
  unfold Fw F DE
  simp only
  rw [← mul_sum]
lemma JY (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
    Fw W (Br n Y i)
      = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
        + ∑ a : Fin n, ∑ b : Fin n,
            if (a : ℕ) < (b : ℕ) then W.a a b * BK (Y (i + b) - Y (i + a)) else 0 := by
  unfold Fw
  have hq : (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) < (b : ℕ) then
          W.a a b * BK (Ew n (Br n Y i) b - Ew n (Br n Y i) a) else 0)
      = ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * BK (Y (i + b) - Y (i + a)) else 0 := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [Dm, Dm,
      show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
  rw [hq]
  rfl
section BlockPressure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def Dz (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
  Bl (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))
def Bm (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ r : Fin (n - 1), b r * (Dz x B ((B.image x).card - (n - 1) + r) - Dz x B r)
end BlockPressure
end AH.AY
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace AH.AY
open AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma D5 {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * BK (Bl ((univ.image x).orderEmbOfFin hS) (i + b)
                - Bl ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ Bh x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := Bl y with hYdef
  have hm0 : 0 < m := by omega
  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * BK (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        W.a a b * BK (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      W.a a b * BK (Y (i + b) - Y (i + a)) else 0)).symm
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
  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * BK (Y q.2 - Y q.1) := by
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
    exact mul_le_mul_of_nonneg_right hmass (Bq _)
  refine (sum_le_sum hfib).trans ?_
  rw [FZ x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else BK (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      BT y hq1m, BT y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), Jk]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = BK (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      BT y hq1m, BT y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * BK (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
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
    · exact Bq _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r
lemma Jj (Y : ℕ → ℝ) (r N : ℕ) :
    ∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r)) = Y (N + r) - Y r := by
  have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
  simp_rw [h]
  have := Finset.sum_range_sub (fun i => Y (i + r)) N
  simpa using this
theorem Wg {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ Bh x univ + W.B * spanOf x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := Bl y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (Br n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (Bw hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (Br n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [JY] at hsum
  rw [sum_add_distrib] at hsum
  have hspan : ∀ r : Fin (n - 1), Y (m - (n - 1) + r) - Y r ≤ spanOf x univ := by
    intro r
    have hr := r.2
    have h1 := Bw hymono (a := m - (n - 1) + r) (b := m - 1) (by omega) (by omega)
    have h2 := Bw hymono (a := 0) (b := r) (by omega) (by omega)
    have hsp : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, BT y (by omega : m - 1 < m), BT y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (Bz x (mem_univ i₀) (mem_univ j₀))
    linarith
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      ≤ W.B * spanOf x univ := by
    rw [sum_comm]
    unfold WCert.B
    rw [sum_mul]
    refine sum_le_sum fun r _ => ?_
    rw [← mul_sum, Jj]
    exact mul_le_mul_of_nonneg_left (hspan r) (hW.b_nonneg r)
  have hquad := D5 hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith
lemma FH {x : ι → ℝ} {B : Finset ι} {m : ℕ} (hS : (B.image x).card = m) (k : ℕ) :
    Dz x B k = Bl (⇑((B.image x).orderEmbOfFin hS)) k := by
  unfold Dz Bl
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
lemma Xv {S S' : Finset ℝ} (h : S = S') :
    Bl (⇑(S.orderEmbOfFin (rfl : S.card = S.card)))
      = Bl (⇑(S'.orderEmbOfFin (rfl : S'.card = S'.card))) := by
  subst h; rfl
theorem block_energy_w' {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ Bh x univ + Bm W.b x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := Bl y with hYdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (Br n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (Bw hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (Br n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [JY] at hsum
  rw [sum_add_distrib] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      = Bm W.b x univ := by
    rw [sum_comm]
    unfold Bm
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, Jj, FH hS, FH hS]
  have hquad := D5 hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith
theorem V9 {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ Bh x B + Bm W.b x B := by
  classical
  have hcard : Fintype.card B = m := by simp [hB]
  have hinj : Function.Injective (fun i : B => x i) := by
    intro i j h
    exact Subtype.ext (hx i.2 j.2 h)
  have h := block_energy_w' hn W hW hCert hm hcard (fun i : B => x i) hinj
  rw [EO] at h
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hP : Bm W.b (fun i : B => x i) univ = Bm W.b x B := by
    unfold Bm Dz
    rw [Xv himg, himg]
  rw [hP] at h
  exact h
end AH.AY
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace AH.AY
open AH.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem YJ {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ Bp hG.1 B + W.B * spanOf x B := by
  classical
  have hBnn : 0 ≤ W.B := WCert.B_nonneg hW
  have hS12 : min 1 (offDiagSqOn G B) ≤ Bp hG.1 B := by
    have h := GQ (hG.submatrix (Subtype.val : B → ι))
    rw [DN] at h
    exact h
  have hoff : Bh x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact Dl (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        = Bh x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold Bh
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ Bh x B + W.B * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := Wg hn W hW hCert hm hcard (fun i : B => x i) hinj
    rw [EO] at h
    have := mul_le_mul_of_nonneg_left (F9 x B) hBnn
    linarith
  have hspan := Dh x B
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
      ≤ Bp hG.1 B + Bm W.b x B := by
  classical
  have hS12 : min 1 (offDiagSqOn G B) ≤ Bp hG.1 B := by
    have h := GQ (hG.submatrix (Subtype.val : B → ι))
    rw [DN] at h
    exact h
  have hoff : Bh x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact Dl (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else BK (x i - x j)) - 2 * δ)
        = Bh x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold Bh
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 := V9 hn W hW hCert hm x B hB hx
  have hP0 : 0 ≤ Bm W.b x B := by
    unfold Bm
    refine sum_nonneg fun r _ => mul_nonneg (hW.b_nonneg r) ?_
    unfold Dz
    have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
    have hr2 := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
    rw [sub_nonneg, BT _ hk, BT _ hr]
    exact hmono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith
  · rw [min_eq_right h1.le] at hS12
    nlinarith
end AH.AY
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
namespace AH.AY
open AH.Bridge
section Abstract
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem WG {n : ℕ} (hn : 2 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ r, 0 ≤ b r)
    (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : n ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A : ℝ) (hA : 0 ≤ A)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → GC x B → A ≤ Dblk B + Bm b x B)
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
  have hspan0 := Dh x (univ : Finset ι)
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
  set Y := Bl y with hYdef
  have hpos_lt : ∀ i, pos i < N := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [BT y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [BT y (e.symm i).2, BT y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := by
    intro a b hab hb
    rw [hYdef, BT y (lt_trans hab hb), BT y hb]
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
  have hintB : ∀ s, GC x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega
  have hsortB : ∀ s, s + m ≤ N → ∀ k, k < m → Dz x (B s) k = Y (s + k) := by
    intro s hs k hk
    have hxinj : Set.InjOn x (B s) := hx.injOn
    have hic : ((B s).image x).card = m := by rw [card_image_of_injOn hxinj, hcardB s hs]
    rw [FH hic, BT _ hk]
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
  have hsumblock : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, Bm b x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib] at h
    have hcast : ((N - m + 1 : ℕ) : ℝ) = (N : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith
  have hpress : ∑ s ∈ St, Bm b x (B s) ≤ Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
    have hY0 : ∀ r : Fin (n - 1), ∀ i ∈ range (m - (n - 1)),
        Y (N - m + 1 + i + r) - Y (i + r) ≤ spanOf x univ := by
      intro r i hi
      rw [mem_range] at hi
      have hr := r.2
      have hi' : N - m + 1 + i + r < N := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨N - m + 1 + i + r, hi'⟩)
      obtain ⟨c, -, hc⟩ := mem_image.mp (hymem ⟨i + r, by omega⟩)
      rw [hYdef, BT y hi', BT y (by omega : i + r < N), ← ha, ← hc]
      exact (le_abs_self _).trans (Bz x (mem_univ a) (mem_univ c))
    have hblk : ∀ s ∈ St, Bm b x (B s)
        = ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) := by
      intro s hs
      have hs' := (hmemSt s).mp hs
      unfold Bm
      have hic : ((B s).image x).card = m := by
        rw [card_image_of_injOn hx.injOn, hcardB s hs']
      rw [hic]
      refine sum_congr rfl fun r _ => ?_
      have hr := r.2
      rw [hsortB s hs' _ (by omega), hsortB s hs' _ (by omega)]
    calc ∑ s ∈ St, Bm b x (B s)
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
          have := Fy (fun t => Y (t + r)) (m - (n - 1)) (N - m + 1)
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
            ⟨D6 N m j (pos i), Nat.lt_succ_of_le (Jb N m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ N) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact Fz hm0 hs hj
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
    _ ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, Bm b x (B s)
          - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by linarith
end Abstract
end AH.AY
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace AH.AY
open AH.Bridge
open Classical
def bC (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - 1) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)
theorem AEb (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 1 ≤ n) (hp : 0 < p) :
    bC n c m (DE n p).B = GF n c m p := by
  unfold bC GF WCert.B DE
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
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ Bp (BZ Z (mtParams T) T) B
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
  · linarith [Cj (BZ Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ 1 / W.B := by
      rw [le_div_iff₀ hBpos]; linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((Bz x hi hj).trans hR)
    have h13 := YJ hn hm W hW hCert hA0 x (Eh Z (mtParams T) T) B hB
      (DG Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
theorem Zq (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
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
  have h15 := Ih (xret Z (mtParams T) T) (DG Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (Bp (BZ Z (mtParams T) T))
    (Ec Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    W.B
    hA' hq0 (Cj _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => Dw (BZ Z (mtParams T) T) κ β)
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
  set D : ℝ := Ec Z (mtParams T) T with hDdef
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
theorem Iw {N N0 : ℝ → ℝ} {c : ℝ} {n m : ℕ} (K : ℝ) (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (K - ε) * N T ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (K / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := G8 hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have : K / Dn - ε = (K - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith
theorem ADx (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn : 2 ≤ n) (hm : n ≤ m)
    (hW : W.Adm) (hBpos : 0 < W.B) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (bC n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := Iw (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - 1) / m) hn hm hA0 (by
      have := Zq zetaZeroConfig paperInputs_zeta hn hm W hW hBpos hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)
def Phi_w' (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)
section SpanPressure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma IG {n m : ℕ} (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (b : Fin (n - 1) → ℝ)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ b r)
    (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    spanOf x B ≤ Bm b x B / bmin := by
  classical
  have hn : 2 ≤ n := by omega
  have hm0 : 0 < m := by omega
  have hne : B.Nonempty := by rw [← card_pos, hB]; exact hm0
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
  have hine : (B.image x).Nonempty := by rw [← card_pos, hic]; exact hm0
  set S := B.image x with hSdef
  set y : ℕ → ℝ := Dz x B with hydef
  have hyk : ∀ k (hk : k < m), y k = S.orderEmbOfFin hic ⟨k, hk⟩ := by
    intro k hk
    rw [hydef, FH hic, BT _ hk]
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
      ≤ Bm b x B := by
    unfold Bm
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
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ Bp (BZ Z (mtParams T) T) B
        + Bm W.b (xret Z (mtParams T) T) B := by
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
  have hinj : Set.InjOn x B := (DG Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ 1 / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((Bz x hi hj).trans hsp)
    have h13 := block_bound_w' hn hm W hW hCert hA0 x (Eh Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := IG hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : 1 < Bm W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [lt_div_iff₀ hbmin] at this
      rw [div_mul_cancel₀ _ hbmin.ne'] at this
      exact this
    linarith [Cj (BZ Z (mtParams T) T) B]
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
  have h15 := WG hn W.b hW.b_nonneg (xret Z (mtParams T) T)
    (DG Z (mtParams T) T hL) hm
    (Bp (BZ Z (mtParams T) T))
    (Ec Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    hA' (Cj _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => Dw (BZ Z (mtParams T) T) κ β)
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
  set D : ℝ := Ec Z (mtParams T) T with hDdef
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
  have h := Iw (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn hm hA0
    (by
      have := pre_solve_w' zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)
end AH.AY
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset Filter
open scoped BigOperators
open Zeta23 Zeta23.ThmD
namespace AH.AY
open AH.Bridge
theorem Jq (n p : ℕ) (s : ℕ) : (DE n p).spanMass s ≤ 2 := by
  classical
  set P : Finset (Fin n × Fin n) :=
    (univ ×ˢ univ).filter fun q : Fin n × Fin n => (q.1 : ℕ) < (q.2 : ℕ) ∧ (q.2 : ℕ) - (q.1 : ℕ) = s
    with hP
  have e : (DE n p).spanMass s = ∑ q ∈ P, (2 / ((n : ℝ) - (((q.2 : ℕ) - (q.1 : ℕ) : ℕ) : ℝ))) := by
    unfold WCert.spanMass DE
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
theorem Zp (n p : ℕ) : (DE n p).Adm := by
  refine ⟨fun i j => ?_, fun _ => ?_, Jq n p⟩
  · unfold DE
    simp only
    have hj := j.2
    have h1 : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (j : ℕ) - (i : ℕ) ≤ n - 1 := by omega
      have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [← h3]; exact_mod_cast h2
    apply div_nonneg (by norm_num); linarith
  · unfold DE; simp only; positivity
theorem oq (n p : ℕ) (hn : 1 ≤ n) : (DE n p).B = ((n : ℝ) - 1) / (p : ℝ) := by
  unfold WCert.B DE
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
  rw [← oq n p hn1]
  have hp' : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  refine n_point_bound_w' n c m (DE n p) hn3 h2n (Zp n p) hp'
    (fun r => le_of_eq rfl) hc (fun g hg => ?_) hA0
  rw [aZ]; exact hCert g hg
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
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp DM
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1
end AH.AY
end
noncomputable section
open Real intervalIntegral
namespace AH.Bridge.AN
def B8 (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800
def B9 (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800
def taylorErr : ℝ := 13/5748019200
theorem DH (θ : ℝ) (hθ : |θ| ≤ 1) :
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
private lemma YC : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
private lemma G7 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ taylorErr := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  unfold taylorErr; nlinarith
theorem Jy {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    B8 u - taylorErr ≤ Real.cos θ := by
  have h0u : 0 ≤ u := h0.trans hu
  have hmono : Real.cos u ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans YC) hu
  have ht := (DH u (by rw [abs_of_nonneg h0u]; exact hu1)).1
  have he := G7 h0u hu1
  have := abs_le.mp ht
  unfold B8
  linarith [this.1, this.2]
theorem J5 {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ B8 l + taylorErr := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans YC) hl
  have ht := (DH l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := G7 h0 hl1
  have := abs_le.mp ht
  unfold B8
  linarith [this.1, this.2]
theorem KG {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    B9 l - taylorErr ≤ Real.sin θ := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := (DH l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := G7 h0 hl1
  have := abs_le.mp ht
  unfold B9
  linarith [this.1, this.2]
theorem KI {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    Real.sin θ ≤ B9 u + taylorErr := by
  have h0u : 0 ≤ u := h0.trans hu
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin θ ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
  have ht := (DH u (by rw [abs_of_nonneg h0u]; exact hu1)).2
  have he := G7 h0u hu1
  have := abs_le.mp ht
  unfold B9
  linarith [this.1, this.2]
theorem Dt (c : ℝ) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; norm_num
  · have hc2 : c / 2 ≠ 0 := by simpa using hc
    rw [integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
      show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
      Real.sin_neg, smul_eq_mul]
    field_simp
    ring
private lemma DX (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t)) MeasureTheory.volume a b :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
theorem Ed (x : ℝ) :
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
    intervalIntegral.integral_add (DX _ _ _)
      (DX _ _ _),
    Dt, Dt]
def gam : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
private lemma C8 :
    (0x62217ab5f4f0b8ac/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 0x62217ab5f4f0b8ad/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]
private lemma Fj : 0 < Real.sin (Real.sqrt 2 / 2) := by
  have hb := C8
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hb.1]) ?_
  linarith [hb.2, Real.pi_gt_three]
theorem IZ :
    (7602445947/10^10 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) ∧
      Real.cos (Real.sqrt 2 / 2) ≤ 7602445994/10^10 := by
  have hb := C8
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := Jy h0 hb.2 (by norm_num)
    have h : (7602445947/10^10 : ℝ)
        ≤ B8 (0x62217ab5f4f0b8ad/10^19) - taylorErr := by
      unfold B8 taylorErr; norm_num
    linarith
  · have := J5 (by norm_num) hb.1 (by linarith [hb.2])
    have h : B8 (0x62217ab5f4f0b8ac/10^19 : ℝ) + taylorErr
        ≤ 7602445994/10^10 := by
      unfold B8 taylorErr; norm_num
    linarith
theorem Iq :
    (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) ∧
      Real.sin (Real.sqrt 2 / 2) ≤ 6496369414/10^10 := by
  have hb := C8
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := KG (by norm_num) hb.1 (by linarith [hb.2])
    have h : (6496369368/10^10 : ℝ)
        ≤ B9 (0x62217ab5f4f0b8ac/10^19) - taylorErr := by
      unfold B9 taylorErr; norm_num
    linarith
  · have := KI h0 hb.2 (by norm_num)
    have h : B9 (0x62217ab5f4f0b8ad/10^19 : ℝ) + taylorErr
        ≤ 6496369414/10^10 := by
      unfold B9 taylorErr; norm_num
    linarith
theorem Ee : (8274992907/10^10 : ℝ) ≤ gam ∧ gam ≤ 8274993018/10^10 := by
  have hb := C8
  have hc := IZ
  have hs := Iq
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  have hprodl : (0x62217ab5f4f0b8ac/10^19 : ℝ) * (7602445947/10^10)
      ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
    mul_le_mul hb.1 hc.1 (by norm_num) h0
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2)
      ≤ (0x62217ab5f4f0b8ad/10^19 : ℝ) * (7602445994/10^10) :=
    mul_le_mul hb.2 hc.2 (by linarith [hc.1]) (by norm_num)
  constructor
  · rw [gam, le_div_iff₀ hspos]; nlinarith [hprodl, hs.2]
  · rw [gam, div_le_iff₀ hspos]; nlinarith [hprodu, hs.1]
private lemma pZ (a b : ℝ) (ha : a ≠ 0) (hsa : Real.sin a ≠ 0)
    (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ((Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)) / 2) / (Real.sin a / a)
      = (a^2 * Real.cos b - a * b * (Real.cos a / Real.sin a) * Real.sin b) / (a^2 - b^2) := by
  have hab : a^2 - b^2 ≠ 0 := by
    have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [hfac]; exact mul_ne_zero h1 h2
  rw [Real.sin_sub, Real.sin_add]
  field_simp
  ring
theorem Zo (x : ℝ) (h : 1 - 2*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := by
  have hb := C8
  set a : ℝ := Real.sqrt 2 / 2 with ha_def
  set b : ℝ := Real.pi * x with hb_def
  have ha2 : a^2 = 1/2 := by
    rw [ha_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have ha : a ≠ 0 := by positivity
  have hsa : Real.sin a ≠ 0 := ne_of_gt Fj
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
    rw [Ed, show (Real.sqrt 2 - 2*Real.pi*x)/2 = a - b by rw [ha_def, hb_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*x)/2 = a + b by rw [ha_def, hb_def]; ring,
      Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  have hK0 : Kfun 0 = Real.sin a / a := by
    rw [Ed, show (Real.sqrt 2 - 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      Real.sinc_of_ne_zero ha]
    ring
  have hgam : gam = a * (Real.cos a / Real.sin a) := by
    rw [gam, ← ha_def]; field_simp
  have hne1 : (1/2 : ℝ) - b^2 ≠ 0 := by
    intro hz; apply h; linarith
  rw [kfun, hK, hK0, pZ a b ha hsa h1 h2, hgam, ha2,
    div_eq_div_iff hne1 h]
  ring
theorem jU : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20
theorem jT : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20
lemma Bq (x : ℝ) : 0 ≤ BK x := sq_nonneg _
theorem aY (x nlo dhi : ℝ) (hnlo : 0 ≤ nlo) (hdhi : 0 < dhi)
    (hD0 : 1 < 2*(Real.pi*x)^2) (hD : 2*(Real.pi*x)^2 - 1 ≤ dhi)
    (hN : nlo ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)|) :
    (nlo/dhi)^2 ≤ BK x := by
  have hne : 1 - 2*(Real.pi*x)^2 ≠ 0 := by intro hz; nlinarith
  have hk : kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := Zo x hne
  have hw : BK x = kfun x ^ 2 := rfl
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
lemma AEi {N nlo : ℝ} (h : nlo ≤ N) : nlo ≤ |N| := h.trans (le_abs_self N)
lemma AEh {N nlo : ℝ} (h : N ≤ -nlo) : nlo ≤ |N| :=
  le_trans (by linarith) (neg_le_abs N)
lemma AUB : Real.cos (Real.pi*(1/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(1/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(1/2:ℝ) = Real.pi/2 by ring]; simp
lemma AUG : Real.cos (Real.pi*(1:ℝ)) = -1 ∧ Real.sin (Real.pi*(1:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(1:ℝ) = Real.pi by ring]; simp
lemma AUC : Real.cos (Real.pi*(3/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(3/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(3/2:ℝ) = Real.pi/2 + Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma AUH : Real.cos (Real.pi*(2:ℝ)) = 1 ∧ Real.sin (Real.pi*(2:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(2:ℝ) = 2*Real.pi by ring]; simp
lemma AUD : Real.cos (Real.pi*(5/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(5/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(5/2:ℝ) = Real.pi/2 + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma AUI : Real.cos (Real.pi*(3:ℝ)) = -1 ∧ Real.sin (Real.pi*(3:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(3:ℝ) = Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma AUE : Real.cos (Real.pi*(7/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(7/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(7/2:ℝ) = Real.pi/2 + Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma AUJ : Real.cos (Real.pi*(4:ℝ)) = 1 ∧ Real.sin (Real.pi*(4:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(4:ℝ) = 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma AUF : Real.cos (Real.pi*(9/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(9/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(9/2:ℝ) = Real.pi/2 + 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]
lemma ASP (a x : ℝ) : Real.cos (Real.pi*(x-a)) = Real.cos (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.cos_neg]
lemma ASQ (a x : ℝ) : Real.sin (Real.pi*(x-a)) = -Real.sin (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.sin_neg]
def taylorSinc (z : ℝ) : ℝ :=
  1 - z^2/6 + z^4/120 - z^6/5040 + z^8/362880 - z^10/39916800
theorem Zr (z : ℝ) (hz : |z| ≤ 1) : taylorSinc z - taylorErr ≤ Real.sinc z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · norm_num [Real.sinc_zero, taylorSinc, taylorErr]
  · have ht := (DH z hz).2
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
private lemma KJ : (14142135623/10^10 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 14142135624/10^10 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]
theorem Dj (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : (19/100 : ℝ) ≤ BK x := by
  have hpl := jU
  have hph := jT
  have h2 := KJ
  set A : ℝ := (Real.sqrt 2 - 2*Real.pi*x)/2 with hA
  set B : ℝ := (Real.sqrt 2 + 2*Real.pi*x)/2 with hB
  have hAlo : (-8637/10000 : ℝ) ≤ A := by rw [hA]; nlinarith
  have hAhi : A ≤ 7072/10000 := by rw [hA]; nlinarith
  have hAabs : |A| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hA2 : A^2 ≤ 7460/10000 := by nlinarith
  have hsincA : (87557/100000 : ℝ) ≤ Real.sinc A := by
    have h := Zr A hAabs
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
    rw [Ed, ← hA, ← hB]; linarith
  have hK0 : Kfun 0 = Real.sinc (Real.sqrt 2/2) := by
    rw [Ed, show (Real.sqrt 2 - 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring]
    ring
  have hK0le : Kfun 0 ≤ 1 := by rw [hK0]; exact Real.sinc_le_one _
  have hK0pos : 0 < Kfun 0 := by
    rw [hK0, Real.sinc_of_ne_zero (by positivity)]
    exact div_pos Fj (by linarith [KJ.1])
  have hk : (43778/100000 : ℝ) ≤ kfun x := by
    rw [kfun, le_div_iff₀ hK0pos]
    nlinarith
  have hw : BK x = kfun x ^ 2 := rfl
  rw [hw]; nlinarith
lemma AFp (a y : ℝ) :
    Real.cos (Real.pi * (a + y)) =
        Real.cos (Real.pi*a) * Real.cos (Real.pi*y) - Real.sin (Real.pi*a) * Real.sin (Real.pi*y)
      ∧ Real.sin (Real.pi * (a + y)) =
        Real.sin (Real.pi*a) * Real.cos (Real.pi*y) + Real.cos (Real.pi*a) * Real.sin (Real.pi*y) := by
  constructor
  · rw [mul_add, Real.cos_add]
  · rw [mul_add, Real.sin_add]
end AH.Bridge.AN
end
noncomputable section
namespace AH.Bridge.AN
theorem aR {P s a b c m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h3 : c ≤ s)
    (k1 : m ≤ a * c) (k3 : m ≤ b * c) : m ≤ P * s := by
  rcases le_total 0 c with hc | hc
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hc, mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hc), mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]
theorem aP {P s a b d m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h4 : s ≤ d)
    (k2 : a * d ≤ m) (k4 : b * d ≤ m) : P * s ≤ m := by
  rcases le_total 0 d with hd | hd
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) hd, mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 hd), mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]
theorem YA {P s a c m : ℝ} (h1 : a ≤ P) (h2 : c ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hm : m ≤ a * c) : m ≤ P * s :=
  hm.trans (mul_le_mul h1 h2 hc (ha.trans h1))
theorem YB {P s b d m : ℝ} (h1 : P ≤ b) (h2 : s ≤ d) (hP : 0 ≤ P) (hs : 0 ≤ s)
    (hm : b * d ≤ m) : P * s ≤ m :=
  (mul_le_mul h1 h2 hs (hP.trans h1)).trans hm
end AH.Bridge.AN
end
section CheckerDefs
namespace AH.Bridge.AN
def taylorCosQ (t : ℚ) : ℚ :=
  let s := t * t
  1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
def taylorSinQ (t : ℚ) : ℚ :=
  let s := t * t
  t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
def errQ : ℚ := 13/5748019200
def piLoQ : ℚ := 0x1107d5eb5b5ba4d7c6 / 10^20
def piHiQ : ℚ := 0x1107d5eb5b5ba4d7c7 / 10^20
def gamLoQ : ℚ := 8274992907 / 10^10
def gamHiQ : ℚ := 8274993018 / 10^10
def floorD (x : ℚ) : ℚ := ((⌊x * 0xe8d4a51000⌋ : ℤ) : ℚ) / 0xe8d4a51000
def ceilD (x : ℚ) : ℚ := ((⌈x * 0xe8d4a51000⌉ : ℤ) : ℚ) / 0xe8d4a51000
def V0 : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k+1 => (-(V0 k).2, (V0 k).1)
def Ej (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
def ZQ (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
def ZS (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)
structure Cell where
  (L U : ℚ) (k : ℕ) (side : Bool) (W : ℚ)
instance : Inhabited Cell := ⟨⟨0, 0, 0, true, 0⟩⟩
namespace Cell
def A (c : Cell) : ℚ := (c.k : ℚ) / 2
def aV (c : Cell) : ℚ := if c.side then c.L - c.A else c.A - c.U
def rhi (c : Cell) : ℚ := if c.side then c.U - c.A else c.A - c.L
def TL (c : Cell) : ℚ := floorD (piLoQ * c.aV)
def TU (c : Cell) : ℚ := ceilD (piHiQ * c.rhi)
def CI (c : Cell) : ℚ × ℚ := (floorD (taylorCosQ c.TU - errQ), ceilD (taylorCosQ c.TL + errQ))
def SI (c : Cell) : ℚ × ℚ := (floorD (taylorSinQ c.TL - errQ), ceilD (taylorSinQ c.TU + errQ))
def cA (c : Cell) : ℤ := (V0 c.k).1
def sA (c : Cell) : ℤ := (V0 c.k).2
def CX (c : Cell) : ℚ × ℚ :=
  if c.side then ZS (Ej c.cA c.CI) (Ej c.sA c.SI) else ZQ (Ej c.cA c.CI) (Ej c.sA c.SI)
def SX (c : Cell) : ℚ × ℚ :=
  if c.side then ZQ (Ej c.sA c.CI) (Ej c.cA c.SI) else ZS (Ej c.sA c.CI) (Ej c.cA c.SI)
def BL (c : Cell) : ℚ := floorD (piLoQ * c.L)
def BU (c : Cell) : ℚ := ceilD (piHiQ * c.U)
def Xx (c : Cell) : ℚ := floorD (2 * gamLoQ * c.BL)
def Zy (c : Cell) : ℚ := ceilD (2 * gamHiQ * c.BU)
def rD (c : Cell) : ℚ := floorD (min (c.Xx * c.SX.1) (c.Zy * c.SX.1))
def q9 (c : Cell) : ℚ := ceilD (max (c.Xx * c.SX.2) (c.Zy * c.SX.2))
def YV (c : Cell) : ℚ := max 0 (max (c.CX.1 - c.q9) (c.rD - c.CX.2))
def YS (c : Cell) : ℚ := ceilD (2 * c.BU * c.BU - 1)
def Wc (c : Cell) : ℚ := (c.YV / c.YS)^2
def ok (c : Cell) : Bool :=
  decide (0 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.aV) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL) && decide (0 ≤ c.Xx)
    && decide (1 < 2 * c.BL * c.BL) && decide (0 < c.YS) && decide (c.W ≤ c.Wc)
end Cell
def chainW (cs : List Cell) : List ℕ → ℚ
  | [] => 0
  | i :: rest => if rest.isEmpty then (cs.getD i default).W else min (cs.getD i default).W (chainW cs rest)
def chainCheck (cs : List Cell) : ℚ → ℚ → List ℕ → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, i :: rest =>
      decide (i < cs.length) && decide ((cs.getD i default).L ≤ lo)
        && chainCheck cs (cs.getD i default).U hi rest
def termW (cs : List Cell) (idxs : List ℕ) : ℚ := if idxs.isEmpty then 0 else chainW cs idxs
def DS (cs : List Cell) (lo hi : ℚ) (idxs : List ℕ) : Bool :=
  idxs.isEmpty || chainCheck cs lo hi idxs
structure Box where
  (xl xu yl yu zl zu : ℚ)
  deriving DecidableEq
inductive Tree
  | leaf (t0 t1 t2 t3 t4 t5 : List ℕ)
  | split (ax : ℕ) (q : ℚ) (lo hi : Tree)
def leafCheck (cs : List Cell) (c p : ℚ) (b : Box) (t0 t1 t2 t3 t4 t5 : List ℕ) : Bool :=
  DS cs b.xl b.xu t0 && DS cs b.yl b.yu t1 && DS cs b.zl b.zu t2
    && DS cs (b.xl + b.yl) (b.xu + b.yu) t3 && DS cs (b.yl + b.zl) (b.yu + b.zu) t4
    && DS cs (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) t5
    && decide (c ≤ (b.xl + b.yl + b.zl) / p
        + 2/3 * termW cs t0 + 2/3 * termW cs t1 + 2/3 * termW cs t2
        + termW cs t3 + termW cs t4 + 2 * termW cs t5)
def DK (cs : List Cell) (c p : ℚ) : Box → Tree → Bool
  | b, .leaf t0 t1 t2 t3 t4 t5 => leafCheck cs c p b t0 t1 t2 t3 t4 t5
  | b, .split ax q lo hi =>
      if ax = 0 then DK cs c p {b with xu := q} lo && DK cs c p {b with xl := q} hi
      else if ax = 1 then DK cs c p {b with yu := q} lo && DK cs c p {b with yl := q} hi
      else if ax = 2 then DK cs c p {b with zu := q} lo && DK cs c p {b with zl := q} hi
      else false
def Bd (cs : List Cell) (lvl : ℚ) : ℚ → ℚ → List (ℚ × ℚ × List ℕ) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, ch) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (ch.isEmpty || (chainCheck cs a b ch && decide (lvl ≤ chainW cs ch)))
        && Bd cs lvl b S rest
def Aw (cover : List (ℚ × ℚ × List ℕ)) : List (ℚ × ℚ) :=
  cover.filterMap fun s => if s.2.2.isEmpty then some (s.1, s.2.1) else none
def BJ (bad : List (ℚ × ℚ)) (i j k : ℕ) : Box :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2⟩
def JX (cs : List Cell) (c p : ℚ) (bad : List (ℚ × ℚ)) (trees : List Tree) : Bool :=
  let nb := bad.length
  (List.range nb).all fun i => (List.range nb).all fun j => (List.range nb).all fun k =>
    DK cs c p (BJ bad i j k) (trees.getD (i * nb * nb + j * nb + k) (.leaf [] [] [] [] [] []))
end AH.Bridge.AN
end CheckerDefs
noncomputable section
open Real
namespace AH.Bridge.AN
theorem G9 (q : ℚ) : B8 (q:ℝ) = ((taylorCosQ q : ℚ) : ℝ) := by
  simp only [B8, taylorCosQ]; push_cast; ring
theorem H7 (q : ℚ) : B9 (q:ℝ) = ((taylorSinQ q : ℚ) : ℝ) := by
  simp only [B9, taylorSinQ]; push_cast; ring
theorem Gv : taylorErr = ((errQ : ℚ) : ℝ) := by
  simp only [taylorErr, errQ]; push_cast; ring
theorem og (x : ℚ) : floorD x ≤ x := by
  unfold floorD
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _
theorem p8 (x : ℚ) : x ≤ ceilD x := by
  unfold ceilD
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _
theorem floorD_le' (x : ℚ) : ((floorD x : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.mpr (og x)
theorem le_ceilD' (x : ℚ) : (x : ℝ) ≤ ((ceilD x : ℚ) : ℝ) := Rat.cast_le.mpr (p8 x)
theorem ZV : ((piLoQ : ℚ) : ℝ) ≤ Real.pi := by
  have h := jU
  simp only [piLoQ]; push_cast
  norm_num at h ⊢
  linarith
theorem ZU : Real.pi ≤ ((piHiQ : ℚ) : ℝ) := by
  have h := jT
  simp only [piHiQ]; push_cast
  norm_num at h ⊢
  linarith
theorem J7 : (0:ℝ) ≤ ((piLoQ : ℚ) : ℝ) := by simp only [piLoQ]; push_cast; norm_num
theorem J6 : ((gamLoQ : ℚ) : ℝ) ≤ gam := by
  have h := Ee.1; simp only [gamLoQ]; push_cast; norm_num at h ⊢; linarith
theorem Xz : gam ≤ ((gamHiQ : ℚ) : ℝ) := by
  have h := Ee.2; simp only [gamHiQ]; push_cast; norm_num at h ⊢; linarith
theorem Je : (0:ℝ) ≤ ((gamLoQ : ℚ) : ℝ) := by simp only [gamLoQ]; push_cast; norm_num
theorem J4 (k : ℕ) :
    Real.cos (Real.pi * ((k:ℝ) / 2)) = ((V0 k).1 : ℝ) ∧
      Real.sin (Real.pi * ((k:ℝ) / 2)) = ((V0 k).2 : ℝ) := by
  induction k with
  | zero => simp [V0]
  | succ k ih =>
    have e : Real.pi * (((k + 1 : ℕ) : ℝ) / 2) = Real.pi * ((k:ℝ) / 2) + Real.pi / 2 := by
      push_cast; ring
    rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ih.1, ih.2]
    simp [V0]
theorem DA (e : ℤ) (I : ℚ × ℚ) {f : ℝ} (h1 : (I.1 : ℝ) ≤ f) (h2 : f ≤ I.2) :
    ((Ej e I).1 : ℝ) ≤ (e:ℝ) * f ∧ (e:ℝ) * f ≤ ((Ej e I).2 : ℝ) := by
  unfold Ej
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 he', mul_le_mul_of_nonneg_left h2 he'⟩
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 he', mul_le_mul_of_nonpos_left h1 he'⟩
theorem WT (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((ZQ I J).1 : ℝ) ≤ f + g ∧ f + g ≤ ((ZQ I J).2 : ℝ) := by
  unfold ZQ; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem Wa (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((ZS I J).1 : ℝ) ≤ f - g ∧ f - g ≤ ((ZS I J).2 : ℝ) := by
  unfold ZS; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
set_option maxHeartbeats 4000000 in
theorem WQ (c : Cell) (h : c.ok = true) (x : ℝ) (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    (c.W : ℝ) ≤ BK x := by
  simp only [Cell.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hLU⟩, hr0⟩, hTU⟩, hTL0q⟩, hBL0q⟩, hP2L0q⟩, hB⟩, hD⟩, hW⟩ := h
  have h0' : (0:ℝ) ≤ c.L := Rat.cast_nonneg.mpr h0
  have hr0' : (0:ℝ) ≤ c.aV := Rat.cast_nonneg.mpr hr0
  have hTL0 : (0:ℝ) ≤ c.TL := Rat.cast_nonneg.mpr hTL0q
  have hBL0 : (0:ℝ) ≤ c.BL := Rat.cast_nonneg.mpr hBL0q
  have hP2L0 : (0:ℝ) ≤ c.Xx := Rat.cast_nonneg.mpr hP2L0q
  have hTU' : (c.TU : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hTU; simpa using this
  have hB' : (1:ℝ) < 2 * c.BL * c.BL := by
    have := (Rat.cast_lt (K := ℝ)).mpr hB; push_cast at this; exact this
  have hD' : (0:ℝ) < c.YS := Rat.cast_pos.mpr hD
  have hW' : (c.W : ℝ) ≤ c.Wc := (Rat.cast_le (K := ℝ)).mpr hW
  set r : ℝ := if c.side then x - c.A else c.A - x with hr
  have hrlo : (c.aV : ℝ) ≤ r := by
    simp only [Cell.aV, hr]; split_ifs <;> push_cast <;> linarith
  have hrhi : r ≤ c.rhi := by
    simp only [Cell.rhi, hr]; split_ifs <;> push_cast <;> linarith
  have hr0r : 0 ≤ r := hr0'.trans hrlo
  have hTL : (c.TL : ℝ) ≤ Real.pi * r := by
    have h1 : (c.TL : ℝ) ≤ ((piLoQ * c.aV : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (YA ZV hrlo J7 hr0' le_rfl)
  have hTUr : Real.pi * r ≤ c.TU := by
    have h1 : ((piHiQ * c.rhi : ℚ) : ℝ) ≤ (c.TU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (YB ZU hrhi Real.pi_pos.le hr0r le_rfl).trans h1
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0r
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU'
  have hc1 : ((c.CI).1 : ℝ) ≤ Real.cos (Real.pi * r) := by
    have h := Jy hθ0 hTUr hTU'
    rw [G9, Gv] at h
    have h1 : ((c.CI).1 : ℝ) ≤ ((taylorCosQ c.TU - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CI).2 : ℝ) := by
    have h := J5 hTL0 hTL hθ1
    rw [G9, Gv] at h
    have h1 : ((taylorCosQ c.TL + errQ : ℚ) : ℝ) ≤ ((c.CI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hs1 : ((c.SI).1 : ℝ) ≤ Real.sin (Real.pi * r) := by
    have h := KG hTL0 hTL hθ1
    rw [H7, Gv] at h
    have h1 : ((c.SI).1 : ℝ) ≤ ((taylorSinQ c.TL - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SI).2 : ℝ) := by
    have h := KI hθ0 hTUr hTU'
    rw [H7, Gv] at h
    have h1 : ((taylorSinQ c.TU + errQ : ℚ) : ℝ) ≤ ((c.SI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hcs := J4 c.k
  have eA : (c.A : ℝ) = (c.k : ℝ) / 2 := by simp [Cell.A]
  have hCX : ((c.CX).1 : ℝ) ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, Bool.false_eq_true, if_false]
      exact WT _ _ (DA _ _ hc1 hc2) (DA _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, if_true]
      exact Wa _ _ (DA _ _ hc1 hc2) (DA _ _ hs1 hs2)
  have hSX : ((c.SX).1 : ℝ) ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, Bool.false_eq_true, if_false]
      exact Wa _ _ (DA _ _ hc1 hc2) (DA _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, if_true]
      exact WT _ _ (DA _ _ hc1 hc2) (DA _ _ hs1 hs2)
  have hb1 : (c.BL : ℝ) ≤ Real.pi * x := by
    have h1 : (c.BL : ℝ) ≤ ((piLoQ * c.L : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (YA ZV hx1 J7 h0' le_rfl)
  have hb2 : Real.pi * x ≤ c.BU := by
    have h1 : ((piHiQ * c.U : ℚ) : ℝ) ≤ (c.BU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (YB ZU hx2 Real.pi_pos.le (h0'.trans hx1) le_rfl).trans h1
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := Je.trans J6
  have hp1 : (c.Xx : ℝ) ≤ 2 * gam * (Real.pi * x) := by
    have h1 : (c.Xx : ℝ) ≤ ((2 * gamLoQ * c.BL : ℚ) : ℝ) := floorD_le' _
    push_cast at h1
    have := mul_le_mul J6 hb1 hBL0 hgam0
    linarith
  have hp2 : 2 * gam * (Real.pi * x) ≤ c.Zy := by
    have h1 : ((2 * gamHiQ * c.BU : ℚ) : ℝ) ≤ (c.Zy : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul Xz hb2 hπx0 (Je.trans (J6.trans Xz))
    linarith
  have hT1 : (c.rD : ℝ) ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have h1 : (c.rD : ℝ) ≤ ((min (c.Xx * c.SX.1) (c.Zy * c.SX.1) : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_min, Rat.cast_mul, Rat.cast_mul] at h1
    exact h1.trans (aR hP2L0 hp1 hp2 hSX.1 (min_le_left _ _) (min_le_right _ _))
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ c.q9 := by
    have h1 : ((max (c.Xx * c.SX.2) (c.Zy * c.SX.2) : ℚ) : ℝ) ≤ (c.q9 : ℝ) := le_ceilD' _
    rw [Rat.cast_max, Rat.cast_mul, Rat.cast_mul] at h1
    exact (aP hP2L0 hp1 hp2 hSX.2 (le_max_left _ _) (le_max_right _ _)).trans h1
  have eNLO : (c.YV : ℝ) = max 0 (max (((c.CX).1 : ℝ) - c.q9) ((c.rD : ℝ) - (c.CX).2)) := by
    rw [Cell.YV, Rat.cast_max, Rat.cast_max]; push_cast; rfl
  have hN : (c.YV : ℝ) ≤ |Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)| := by
    rw [eNLO]
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans (by linarith [hCX.1, hT2]) (le_abs_self _)
    · exact le_trans (by linarith [hCX.2, hT1]) (neg_le_abs _)
  have hNLO0 : (0:ℝ) ≤ c.YV := by rw [eNLO]; exact le_max_left _ _
  have hD0 : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have := mul_le_mul hb1 hb1 hBL0 hπx0
    rw [pow_two]; linarith [this, hB']
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ c.YS := by
    have h1 : ((2 * c.BU * c.BU - 1 : ℚ) : ℝ) ≤ (c.YS : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    rw [pow_two]; linarith [this, h1]
  have hfin := aY x (c.YV : ℝ) (c.YS : ℝ) hNLO0 hD' hD0 hDD hN
  have eWc : (c.Wc : ℝ) = ((c.YV : ℝ) / c.YS)^2 := by rw [Cell.Wc]; push_cast; rfl
  rw [eWc] at hW'
  exact hW'.trans hfin
theorem Xp {cs : List Cell} {i : ℕ} (h : i < cs.length) : cs.getD i default ∈ cs := by
  rw [List.getD_eq_getElem cs default h]; exact List.getElem_mem h
theorem Vz (cs : List Cell) (hcs : cs.all Cell.ok = true) :
    ∀ (idxs : List ℕ) (lo hi : ℚ), chainCheck cs lo hi idxs = true →
      ∀ e : ℝ, (lo : ℝ) ≤ e → e ≤ hi → (chainW cs idxs : ℝ) ≤ BK e := by
  intro idxs
  induction idxs with
  | nil =>
    intro lo hi h e _ _
    simp only [chainW, Rat.cast_zero]; exact Bq e
  | cons i rest ih =>
    intro lo hi h e he1 he2
    simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi_lt, hL⟩, hrest⟩ := h
    have hok : (cs.getD i default).ok = true :=
      List.all_eq_true.mp hcs _ (Xp hi_lt)
    have hL' : ((cs.getD i default).L : ℝ) ≤ e := le_trans (by exact_mod_cast hL) he1
    simp only [chainW]
    split_ifs with hempty
    ·
      have hU : hi ≤ (cs.getD i default).U := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainCheck] using hrest
      exact WQ _ hok e hL' (he2.trans (by exact_mod_cast hU))
    · rw [Rat.cast_min]
      rcases le_total e ((cs.getD i default).U : ℝ) with hU | hU
      · exact (min_le_left _ _).trans (WQ _ hok e hL' hU)
      · exact (min_le_right _ _).trans (ih _ _ hrest e hU he2)
theorem D7 (cs : List Cell) (hcs : cs.all Cell.ok = true) (idxs : List ℕ) (lo hi : ℚ)
    (h : DS cs lo hi idxs = true) (e : ℝ) (he1 : (lo : ℝ) ≤ e) (he2 : e ≤ hi) :
    (termW cs idxs : ℝ) ≤ BK e := by
  simp only [DS, Bool.or_eq_true] at h
  simp only [termW]
  split_ifs with hempty
  · simp only [Rat.cast_zero]; exact Bq e
  · rcases h with h | h
    · exact absurd h (by simpa using hempty)
    · exact Vz cs hcs idxs lo hi h e he1 he2
def G4 (p : ℚ) (x y z : ℝ) : ℝ :=
  (1 / (p : ℝ)) * (x + y + z) + 2/3 * BK x + 2/3 * BK y + 2/3 * BK z
    + BK (x + y) + BK (y + z) + 2 * BK (x + y + z)
theorem JQ (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) (b : Box)
    (t0 t1 t2 t3 t4 t5 : List ℕ) (h : leafCheck cs c p b t0 t1 t2 t3 t4 t5 = true)
    (x y z : ℝ) (hx1 : (b.xl : ℝ) ≤ x) (hx2 : x ≤ b.xu) (hy1 : (b.yl : ℝ) ≤ y) (hy2 : y ≤ b.yu)
    (hz1 : (b.zl : ℝ) ≤ z) (hz2 : z ≤ b.zu) : (c : ℝ) ≤ G4 p x y z := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hineq⟩ := h
  have w0 := D7 cs hcs t0 _ _ h0 x hx1 hx2
  have w1 := D7 cs hcs t1 _ _ h1 y hy1 hy2
  have w2 := D7 cs hcs t2 _ _ h2 z hz1 hz2
  have w3 := D7 cs hcs t3 _ _ h3 (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w4 := D7 cs hcs t4 _ _ h4 (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := D7 cs hcs t5 _ _ h5 (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr hineq
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G4
  linarith
theorem oM (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) :
    ∀ (t : Tree) (b : Box), DK cs c p b t = true →
      ∀ x y z : ℝ, (b.xl : ℝ) ≤ x → x ≤ b.xu → (b.yl : ℝ) ≤ y → y ≤ b.yu →
        (b.zl : ℝ) ≤ z → z ≤ b.zu → (c : ℝ) ≤ G4 p x y z := by
  intro t
  induction t with
  | leaf t0 t1 t2 t3 t4 t5 =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    exact JQ cs hcs c p hp b t0 t1 t2 t3 t4 t5 h x y z hx1 hx2 hy1 hy2 hz1 hz2
  | split ax q lo hi ihlo ihhi =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    simp only [DK] at h
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
theorem cover_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (lvl : ℚ) :
    ∀ (cover : List (ℚ × ℚ × List ℕ)) (pos S : ℚ), Bd cs lvl pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) ≤ v → v < S →
        (lvl : ℝ) ≤ BK v ∨ ∃ s ∈ cover, s.2.2.isEmpty = true ∧ (s.1 : ℝ) ≤ v ∧ v ≤ s.2.1 := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [Bd, decide_eq_true_eq] at h
    have : (S : ℝ) ≤ pos := by exact_mod_cast h
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, ch⟩ := s
    simp only [Bd, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hch⟩, hrest⟩ := h
    rcases le_total v (b : ℝ) with hvb | hvb
    · rcases hch with hch | ⟨hchain, hlvl⟩
      · right
        refine ⟨(a, b, ch), List.mem_cons_self .., hch, ?_, hvb⟩
        rw [hpos]; exact hv1
      · left
        have hW := Vz cs hcs ch a b hchain v (by rw [hpos]; exact hv1) hvb
        exact le_trans (by exact_mod_cast hlvl) hW
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩
theorem Dr {cover : List (ℚ × ℚ × List ℕ)} {s : ℚ × ℚ × List ℕ} (hs : s ∈ cover)
    (he : s.2.2.isEmpty = true) : (s.1, s.2.1) ∈ Aw cover := by
  simp only [Aw, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩
theorem Zt (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p)
    (bad : List (ℚ × ℚ)) (trees : List Tree) (h : JX cs c p bad trees = true)
    (i j k : ℕ) (hi : i < bad.length) (hj : j < bad.length) (hk : k < bad.length)
    (x y z : ℝ)
    (hx1 : ((bad.getD i (0, 0)).1 : ℝ) ≤ x) (hx2 : x ≤ (bad.getD i (0, 0)).2)
    (hy1 : ((bad.getD j (0, 0)).1 : ℝ) ≤ y) (hy2 : y ≤ (bad.getD j (0, 0)).2)
    (hz1 : ((bad.getD k (0, 0)).1 : ℝ) ≤ z) (hz2 : z ≤ (bad.getD k (0, 0)).2) :
    (c : ℝ) ≤ G4 p x y z := by
  simp only [JX, List.all_eq_true, List.mem_range] at h
  have ht := h i hi j hj k hk
  exact oM cs hcs c p hp _ (BJ bad i j k) ht x y z hx1 hx2 hy1 hy2 hz1 hz2
theorem oO (cs : List Cell) (cover : List (ℚ × ℚ × List ℕ)) (trees : List Tree)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 3/2 * c ≤ 19/100) (hcs : cs.all Cell.ok = true)
    (hcov : Bd cs (3/2 * c) (1/2) S cover = true)
    (htr : JX cs c p (Aw cover) trees = true) :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (c : ℝ) ≤ G4 p x y z := by
  intro x y z hx hy hz
  have hw := fun t : ℝ => Bq t
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G4; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  push_neg at hsum
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 2/3 * BK v ∨ ∃ i, i < (Aw cover).length ∧
        (((Aw cover).getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ ((Aw cover).getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := Dj v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover_sound cs hcs _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := Dr hs he
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
  exact Zt cs hcs c p hp _ trees htr i j k hi hj hk x y z hxi1 hxi2 hyj1 hyj2 hzk1 hzk2
private lemma ASR (f : Fin (4 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := by
  show ∑ i : Fin 3, f i = f 0 + f 1 + f 2
  exact Fin.sum_univ_three f
lemma AUA (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * BK (g 0) + 2/3 * BK (g 1) + 2/3 * BK (g 2)
      + BK (g 0 + g 1) + BK (g 1 + g 2) + 2 * BK (g 0 + g 1 + g 2) := by
  simp only [F, Ew, ASR, Fin.sum_univ_four, Fin.isValue]
  norm_num
  try ring
end AH.Bridge.AN
end
section SixW35RKFDefs
namespace AH.Bridge.AN
structure CellN where
  (key : ℕ) (WN : ℕ)
instance : Inhabited CellN := ⟨⟨0, 0⟩⟩
def SC : ℕ := 32768
def SW : ℕ := 0x9184e72a000
def SC4 : ℕ := 8192
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)
def CellN.toQ (c : CellN) : Cell := ⟨(c.LN : ℚ) / SC, (c.UN : ℚ) / SC, c.k, c.side, (c.WN : ℚ) / SW⟩
def DZ : ℕ := 0x38d7ea4c68000
def DZ2 : ℕ := 500000000000000
def PLN : ℕ := 0x1107d5eb5b5ba4d7c6
def PUN : ℕ := 0x1107d5eb5b5ba4d7c7
def GLN : ℕ := 8274992907
def GUN : ℕ := 8274993018
def ERRD : ℕ := 2262000
def ndiv (a b : ℕ) : ℕ := a / b
def ndivc (a b : ℕ) : ℕ := (a + b - 1) / b
def ED (T : ℕ) : ℕ := 3628800 * DZ^10 + 151200 * T^4 * DZ^6 + 90 * T^8 * DZ^2
def D9 (T : ℕ) : ℕ := 1814400 * T^2 * DZ^8 + 5040 * T^6 * DZ^4 + T^10
def EI (T : ℕ) : ℕ := 39916800 * T * DZ^10 + 332640 * T^5 * DZ^6 + 110 * T^9 * DZ^2
def EH (T : ℕ) : ℕ := 6652800 * T^3 * DZ^8 + 7920 * T^7 * DZ^4 + T^11
def cosLo (T : ℕ) : ℕ := ndiv (ED T - D9 T) (3628800 * DZ^9)
def cosHi (T : ℕ) : ℕ := ndivc (ED T - D9 T) (3628800 * DZ^9)
def sinLo (T : ℕ) : ℕ := ndiv (EI T - EH T) (39916800 * DZ^10)
def sinHi (T : ℕ) : ℕ := ndivc (EI T - EH T) (39916800 * DZ^10)
def zfdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndiv z.toNat DZ : ℕ) : ℤ) else -((ndivc (-z).toNat DZ : ℕ) : ℤ)
def zcdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndivc z.toNat DZ : ℕ) : ℤ) else -((ndiv (-z).toNat DZ : ℕ) : ℤ)
def Ds (e : ℤ) (I : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ e then (e * I.1, e * I.2) else (e * I.2, e * I.1)
def WS (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 + J.1, I.2 + J.2)
def WX (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 - J.2, I.2 - J.1)
namespace CellN
def WL (c : CellN) : ℕ := ndiv (c.LN * DZ) SC
def WM (c : CellN) : ℕ := ndivc (c.UN * DZ) SC
def AD (c : CellN) : ℕ := c.k * DZ2
def q8 (c : CellN) : ℕ := if c.side then c.WL - c.AD else c.AD - c.WM
def q7 (c : CellN) : ℕ := if c.side then c.WM - c.AD else c.AD - c.WL
def Jv (c : CellN) : ℕ := ndiv (PLN * c.q8) 0x56bc75e2d63100000
def JZ (c : CellN) : ℕ := ndivc (PUN * c.q7) 0x56bc75e2d63100000
def Zu (c : CellN) : ℤ := (cosLo c.JZ : ℤ) - ERRD
def Zv (c : CellN) : ℤ := (cosHi c.Jv : ℤ) + ERRD
def Zz (c : CellN) : ℤ := (sinLo c.Jv : ℤ) - ERRD
def Z8 (c : CellN) : ℤ := (sinHi c.JZ : ℤ) + ERRD
def cAZ (c : CellN) : ℤ := (V0 c.k).1
def sAZ (c : CellN) : ℤ := (V0 c.k).2
def Zw (c : CellN) : ℤ × ℤ :=
  if c.side then WX (Ds c.cAZ (c.Zu, c.Zv)) (Ds c.sAZ (c.Zz, c.Z8))
  else WS (Ds c.cAZ (c.Zu, c.Zv)) (Ds c.sAZ (c.Zz, c.Z8))
def C9 (c : CellN) : ℤ × ℤ :=
  if c.side then WS (Ds c.sAZ (c.Zu, c.Zv)) (Ds c.cAZ (c.Zz, c.Z8))
  else WX (Ds c.sAZ (c.Zu, c.Zv)) (Ds c.cAZ (c.Zz, c.Z8))
def IQ (c : CellN) : ℕ := ndiv (PLN * c.WL) 0x56bc75e2d63100000
def Gk (c : CellN) : ℕ := ndivc (PUN * c.WM) 0x56bc75e2d63100000
def Dq (c : CellN) : ℕ := ndiv (2 * GLN * c.IQ) 10000000000
def D8 (c : CellN) : ℕ := ndivc (2 * GUN * c.Gk) 10000000000
def pD (c : CellN) : ℤ := zfdiv (min ((c.Dq : ℤ) * c.C9.1) ((c.D8 : ℤ) * c.C9.1))
def pC (c : CellN) : ℤ := zcdiv (max ((c.Dq : ℤ) * c.C9.2) ((c.D8 : ℤ) * c.C9.2))
def C6 (c : CellN) : ℤ := max 0 (max (c.Zw.1 - c.pC) (c.pD - c.Zw.2))
def CZ (c : CellN) : ℤ := ((ndivc (2 * c.Gk * c.Gk) DZ : ℕ) : ℤ) - DZ
def ZT (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.JZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (D9 c.JZ ≤ ED c.JZ) && decide (D9 c.Jv ≤ ED c.Jv)
    && decide (EH c.Jv ≤ EI c.Jv) && decide (EH c.JZ ≤ EI c.JZ)
    && decide (DZ * DZ < 2 * c.IQ * c.IQ) && decide (0 < c.CZ)
def ow (c : CellN) : Bool :=
  c.ZT && decide ((c.WN : ℤ) * c.CZ * c.CZ ≤ c.C6 * c.C6 * SW)
def WZ (c : CellN) : ℕ :=
  bif c.ZT then ((c.C6 * c.C6 * SW) / (c.CZ * c.CZ)).toNat else 0
end CellN
inductive CTN
  | nil
  | node (l : CTN) (c : CellN) (r : CTN)
namespace CTN
def toList : CTN → List CellN
  | nil => []
  | node l c r => l.toList ++ c :: r.toList
def BX : CTN → Bool
  | nil => true
  | node l c r => l.BX && c.ow && r.BX
def find : CTN → ℕ → Option CellN
  | nil, _ => none
  | node l c r, q =>
      bif Nat.blt q c.key then l.find q
      else bif Nat.blt c.key q then r.find q
      else some c
end CTN
def AFo : ℕ := 98304
def E0 (a b : ℕ) : ℕ × ℕ :=
  bif Nat.ble AFo a then ((a >>> 7) <<< 7, ((b + 127) >>> 7) <<< 7) else (a, b)
def Ij : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(E0 a hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 13) + 1) <<< 13
      bif Nat.blt q hi then (E0 a q) :: Ij fuel q hi else [(E0 a hi)]
def lookupAllN (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      match t.find (a * KB + b), lookupAllN t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none
def Eo : ℕ → ℕ → List CellN → Bool
  | lo, hi, [] => Nat.ble hi lo
  | lo, hi, c :: rest => Nat.ble c.LN lo && Eo c.UN hi rest
def chainWN : List CellN → ℕ
  | [] => 0
  | c :: rest => bif rest.isEmpty then c.WN else bif Nat.ble c.WN (chainWN rest) then c.WN else chainWN rest
def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := Ij 64 lo hi
def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if Eo lo hi cs then chainWN cs else 0
  | none => 0
def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)
end AH.Bridge.AN
namespace AH.Bridge.AN.AG
def SA : ℕ := 100000000
def cN : ℕ := 345747
structure Box where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)
  deriving DecidableEq
def Box.ASU (b : Box) : ℕ :=
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
def Box.BG (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with u0 := q }
  | 1 => { b with u1 := q }
  | 2 => { b with u2 := q }
  | 3 => { b with u3 := q }
  | _ => { b with u4 := q }
def Box.BH (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with l0 := q }
  | 1 => { b with l1 := q }
  | 2 => { b with l2 := q }
  | 3 => { b with l3 := q }
  | _ => { b with l4 := q }
def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((24896 * b.l0 + 42034 * b.l1 + 46137 * b.l2 + 42034 * b.l3 + 24896 * b.l4) * SW + (25326800 * termWN tb (b.l0) (b.u0) + 62369200 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 40126500 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 99999900 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) + 200000000 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l1) (b.u1) + 37630700 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 119746800 * termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) + 99999900 * termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) + 52857300 * termWN tb (b.l2) (b.u2) + 37630700 * termWN tb (b.l2 + b.l3) (b.u2 + b.u3) + 40126500 * termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l3) (b.u3) + 62369200 * termWN tb (b.l3 + b.l4) (b.u3 + b.u4) + 25326800 * termWN tb (b.l4) (b.u4)) * SC)
def Ao (bits pos : ℕ) : ℕ := (bits >>> (pos + 1)) &&& 7
def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := Ao bits pos
        let q := b.mid ax
        match walk tb bits fuel (pos + 4) (b.BG ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.BH ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheck tb b then some (pos + 1) else none
def Bd (tb : CTN) (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match tb.find (a * KB + b) with
            | some c => Nat.ble c.LN a && Nat.ble b c.UN && Nat.ble (cN * SW) (aAdjN * c.WN) | none => false))
        && Bd tb aAdjN b S rest
def Aw (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)
def BJ (bd0 bd1 bd2 bd3 bd4 : List (ℕ × ℕ)) (i0 i1 i2 i3 i4 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2, (bd3.getD i3 (0, 0)).1, (bd3.getD i3 (0, 0)).2, (bd4.getD i4 (0, 0)).1, (bd4.getD i4 (0, 0)).2⟩
end AH.Bridge.AN.AG
end SixW35RKFDefs
section SixW35RKFForce
universe uF
namespace AH.Bridge.AN
def BW {α : Sort uF} (a : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (motive := fun _ => α) a (k 0) (fun n => k (Nat.succ n))
theorem EZ {α : Sort uF} (a : ℕ) (k : ℕ → α) : BW a k = k a := by cases a <;> rfl
def GW : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(E0 a hi)]
  | fuel + 1, a, hi =>
      BW (((a >>> 13) + 1) <<< 13) fun q =>
      bif Nat.blt q hi then (E0 a q) :: GW fuel q hi else [(E0 a hi)]
def EK (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      BW (a * KB + b) fun key =>
      match t.find key, EK t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none
def GS : List CellN → ℕ
  | [] => 0
  | c :: rest => BW (GS rest) fun m =>
      bif rest.isEmpty then c.WN else bif Nat.ble c.WN m then c.WN else m
def V8 (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match EK t ps with
  | some cs => if Eo lo hi cs then GS cs else 0
  | none => 0
def Cr (t : CTN) (lo hi : ℕ) : ℕ :=
  BW lo fun lo => BW hi fun hi => V8 t lo hi (GW 64 lo hi)
theorem V7 : ∀ fuel a hi, GW fuel a hi = Ij fuel a hi
  | 0, a, hi => by simp only [GW, Ij]
  | fuel + 1, a, hi => by simp only [GW, Ij, EZ, V7 fuel]
theorem Ie (t : CTN) : ∀ ps, EK t ps = lookupAllN t ps
  | [] => by simp only [EK, lookupAllN]
  | (a, b) :: rest => by simp only [EK, lookupAllN, EZ, Ie t rest]; (try rfl)
theorem Vw : ∀ cs, GS cs = chainWN cs
  | [] => by simp only [GS, chainWN]
  | c :: rest => by simp only [GS, chainWN, EZ, Vw rest]
theorem oL (t : CTN) (lo hi : ℕ) : Cr t lo hi = termWN t lo hi := by
  simp only [Cr, termWN, EZ, V8, termWNcore, V7, Ie, Vw, piecesN']; (try rfl)
end AH.Bridge.AN
namespace AH.Bridge.AN.AG
def leafCheckF (tb : CTN) (b : Box) : Bool :=
  BW b.l0 fun l0 =>
  BW b.l1 fun l1 =>
  BW b.l2 fun l2 =>
  BW b.l3 fun l3 =>
  BW b.l4 fun l4 =>
  BW b.u0 fun u0 =>
  BW b.u1 fun u1 =>
  BW b.u2 fun u2 =>
  BW b.u3 fun u3 =>
  BW b.u4 fun u4 =>
  BW (l0 + l1) fun l0_2 =>
  BW (l0_2 + l2) fun l0_3 =>
  BW (l0_3 + l3) fun l0_4 =>
  BW (l0_4 + l4) fun l0_5 =>
  BW (l1 + l2) fun l1_3 =>
  BW (l1_3 + l3) fun l1_4 =>
  BW (l1_4 + l4) fun l1_5 =>
  BW (l2 + l3) fun l2_4 =>
  BW (l2_4 + l4) fun l2_5 =>
  BW (l3 + l4) fun l3_5 =>
  BW (u0 + u1) fun u0_2 =>
  BW (u0_2 + u2) fun u0_3 =>
  BW (u0_3 + u3) fun u0_4 =>
  BW (u0_4 + u4) fun u0_5 =>
  BW (u1 + u2) fun u1_3 =>
  BW (u1_3 + u3) fun u1_4 =>
  BW (u1_4 + u4) fun u1_5 =>
  BW (u2 + u3) fun u2_4 =>
  BW (u2_4 + u4) fun u2_5 =>
  BW (u3 + u4) fun u3_5 =>
  Nat.ble (cN * SC * SW) ((24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) * SW + (25326800 * Cr tb l0 u0 + 62369200 * Cr tb l0_2 u0_2 + 40126500 * Cr tb l0_3 u0_3 + 99999900 * Cr tb l0_4 u0_4 + 200000000 * Cr tb l0_5 u0_5 + 48244400 * Cr tb l1 u1 + 37630700 * Cr tb l1_3 u1_3 + 119746800 * Cr tb l1_4 u1_4 + 99999900 * Cr tb l1_5 u1_5 + 52857300 * Cr tb l2 u2 + 37630700 * Cr tb l2_4 u2_4 + 40126500 * Cr tb l2_5 u2_5 + 48244400 * Cr tb l3 u3 + 62369200 * Cr tb l3_5 u3_5 + 25326800 * Cr tb l4 u4) * SC)
def Wf (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        BW (Ao bits pos) fun ax => BW (b.mid ax) fun q => BW (pos + 4) fun p4 =>
        match Wf tb bits fuel p4 (b.BG ax q) with
        | none => none
        | some pos' => Wf tb bits fuel pos' (b.BH ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheckF tb b then some (pos + 1) else none
theorem YM (tb : CTN) (b : Box) : leafCheckF tb b = leafCheck tb b := by
  simp only [leafCheckF, leafCheck, EZ, oL]
theorem A8 (tb : CTN) (bits : ℕ) : ∀ fuel pos b, Wf tb bits fuel pos b = walk tb bits fuel pos b
  | 0, _, _ => by simp only [Wf, walk]
  | fuel + 1, pos, b => by simp only [Wf, walk, EZ, YM, A8 tb bits fuel]; (try rfl)
end AH.Bridge.AN.AG
end SixW35RKFForce
noncomputable section
open Real
namespace AH.Bridge.AN
theorem ATy : (0:ℚ) < SC := by norm_num [SC]
theorem ATz : (0:ℚ) < SW := by norm_num [SW]
theorem DU : (0:ℝ) < DZ := by norm_num [DZ]
theorem YP : (DZ:ℝ) ≠ 0 := by norm_num [DZ]
theorem GK (a b : ℕ) (hb : 0 < b) : ((ndiv a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  unfold ndiv
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b
theorem EU (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
  unfold ndivc
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h : a ≤ ((a + b - 1) / b) * b := by
    have := Nat.lt_div_mul_add (a := a + b - 1) hb
    omega
  exact_mod_cast h
theorem q6 (z : ℤ) : ((zfdiv z : ℤ) : ℝ) ≤ (z : ℝ) / DZ := by
  unfold zfdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact GK _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (EU _ _ (by norm_num [DZ]))
theorem qB (z : ℤ) : (z : ℝ) / DZ ≤ ((zcdiv z : ℤ) : ℝ) := by
  unfold zcdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact EU _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (GK _ _ (by norm_num [DZ]))
theorem KO (T : ℕ) (h : D9 T ≤ ED T) :
    B8 ((T : ℝ) / DZ) = ((ED T - D9 T : ℕ) : ℝ) / (3628800 * (DZ : ℝ)^10) := by
  rw [Nat.cast_sub h]
  unfold B8 ED D9
  push_cast
  have hD := YP
  field_simp
  ring
theorem KQ (T : ℕ) (h : EH T ≤ EI T) :
    B9 ((T : ℝ) / DZ) = ((EI T - EH T : ℕ) : ℝ) / (39916800 * (DZ : ℝ)^11) := by
  rw [Nat.cast_sub h]
  unfold B9 EI EH
  push_cast
  have hD := YP
  field_simp
  ring
theorem pW (T : ℕ) (h : D9 T ≤ ED T) :
    ((cosLo T : ℕ) : ℝ) / DZ ≤ B8 ((T : ℝ) / DZ) := by
  rw [KO T h]
  unfold cosLo
  have := GK (ED T - D9 T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ DU (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DU
  calc ((ndiv (ED T - D9 T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ) ^ 10)
      = (((ndiv (ED T - D9 T) (3628800 * DZ ^ 9) : ℕ) : ℝ)) * (3628800 * (DZ:ℝ)^9) * DZ := by ring
    _ ≤ ((ED T - D9 T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this
theorem p9 (T : ℕ) (h : D9 T ≤ ED T) :
    B8 ((T : ℝ) / DZ) ≤ ((cosHi T : ℕ) : ℝ) / DZ := by
  rw [KO T h]
  unfold cosHi
  have := EU (ED T - D9 T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DU]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DU
  calc ((ED T - D9 T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (ED T - D9 T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ)^9) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring
theorem qE (T : ℕ) (h : EH T ≤ EI T) :
    ((sinLo T : ℕ) : ℝ) / DZ ≤ B9 ((T : ℝ) / DZ) := by
  rw [KQ T h]
  unfold sinLo
  have := GK (EI T - EH T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ DU (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DU
  calc ((ndiv (EI T - EH T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ) ^ 11)
      = (((ndiv (EI T - EH T) (39916800 * DZ ^ 10) : ℕ) : ℝ)) * (39916800 * (DZ:ℝ)^10) * DZ := by ring
    _ ≤ ((EI T - EH T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this
theorem qA (T : ℕ) (h : EH T ≤ EI T) :
    B9 ((T : ℝ) / DZ) ≤ ((sinHi T : ℕ) : ℝ) / DZ := by
  rw [KQ T h]
  unfold sinHi
  have := EU (EI T - EH T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DU]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DU
  calc ((EI T - EH T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (EI T - EH T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ)^10) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring
theorem KR : taylorErr ≤ (ERRD : ℝ) / DZ := by norm_num [taylorErr, ERRD, DZ]
theorem C7 (e : ℤ) (I : ℤ × ℤ) {f : ℝ} (h1 : (I.1 : ℝ) / DZ ≤ f) (h2 : f ≤ (I.2 : ℝ) / DZ) :
    ((Ds e I).1 : ℝ) / DZ ≤ (e : ℝ) * f ∧ (e : ℝ) * f ≤ ((Ds e I).2 : ℝ) / DZ := by
  unfold Ds
  have hD := DU
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
theorem V5 (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((WS I J).1 : ℝ) / DZ ≤ f + g ∧ f + g ≤ ((WS I J).2 : ℝ) / DZ := by
  unfold WS; simp only; push_cast; rw [add_div, add_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem V6 (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((WX I J).1 : ℝ) / DZ ≤ f - g ∧ f - g ≤ ((WX I J).2 : ℝ) / DZ := by
  unfold WX; simp only; push_cast; rw [sub_div, sub_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem oQ : ((PLN : ℕ) : ℝ) / 0x56bc75e2d63100000 ≤ Real.pi := by
  have h := jU; norm_num [PLN] at h ⊢; linarith
theorem oR : Real.pi ≤ ((PUN : ℕ) : ℝ) / 0x56bc75e2d63100000 := by
  have h := jT; norm_num [PUN] at h ⊢; linarith
theorem oP : ((GLN : ℕ) : ℝ) / 10000000000 ≤ gam := by
  have h := Ee.1; norm_num [GLN] at h ⊢; linarith
theorem AEd : gam ≤ ((GUN : ℕ) : ℝ) / 10000000000 := by
  have h := Ee.2; norm_num [GUN] at h ⊢; linarith
theorem GU (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : ((p : ℕ) : ℝ) / P ≤ A)
    (hB : ((q : ℕ) : ℝ) / DZ ≤ B) (hA0 : 0 ≤ ((p : ℕ) : ℝ) / P) (hB0 : 0 ≤ ((q : ℕ) : ℝ) / DZ) :
    ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ A * B := by
  have h := GK (p * q) P hP
  have hD := DU
  calc ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ (((p * q : ℕ) : ℝ) / P) / DZ :=
        div_le_div_of_nonneg_right h hD.le
    _ = (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := by push_cast; field_simp
    _ ≤ A * B := mul_le_mul hA hB hB0 (hA0.trans hA)
theorem Fo (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : A ≤ ((p : ℕ) : ℝ) / P)
    (hB : B ≤ ((q : ℕ) : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    A * B ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := by
  have h := EU (p * q) P hP
  have hD := DU
  calc A * B ≤ (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = (((p * q : ℕ) : ℝ) / P) / DZ := by push_cast; field_simp
    _ ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := div_le_div_of_nonneg_right h hD.le
set_option maxHeartbeats 4000000 in
theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.ZT = true)
    (hW : (w : ℤ) * c.CZ * c.CZ ≤ c.C6 * c.C6 * SW) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ BK x := by
  simp only [CellN.ZT, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DU
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 0x56bc75e2d63100000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have nG0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 10000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hLLO : ((c.WL : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := GK (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.WL
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.WM : ℕ) : ℝ) / DZ := by
    have := EU (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.WM
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
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.q8 : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.q8
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.WM c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.WL with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.q7 : ℕ) : ℝ) / DZ := by
    unfold CellN.q7
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.WL ≤ c.AD := by
        have h1 : ((c.WL : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.WM := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.WM : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  have hTL : ((c.Jv : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.Jv
    exact GU PLN c.q8 _ (by norm_num) oQ hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.JZ : ℕ) : ℝ) / DZ := by
    unfold CellN.JZ
    exact Fo PUN c.q7 _ (by norm_num) oR hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.JZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.Jv : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  have hc1 : ((c.Zu : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := Jy hθ0 hTUr hTU1
    have h1 := pW c.JZ hcP1
    have h2 := KR
    unfold CellN.Zu; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.Zv : ℤ) : ℝ) / DZ := by
    have h := J5 hTL0 hTL hθ1
    have h1 := p9 c.Jv hcP2
    have h2 := KR
    unfold CellN.Zv; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.Zz : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := KG hTL0 hTL hθ1
    have h1 := qE c.Jv hsP1
    have h2 := KR
    unfold CellN.Zz; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.Z8 : ℤ) : ℝ) / DZ := by
    have h := KI hθ0 hTUr hTU1
    have h1 := qA c.JZ hsP2
    have h2 := KR
    unfold CellN.Z8; push_cast; rw [add_div]
    linarith
  have hcs := J4 c.k
  have hCX : ((c.Zw).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.Zw).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.Zw, hsd, Bool.false_eq_true, if_false]
      exact V5 _ _ (C7 _ _ hc1 hc2) (C7 _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.Zw, hsd, if_true]
      exact V6 _ _ (C7 _ _ hc1 hc2) (C7 _ _ hs1 hs2)
  have hSX : ((c.C9).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.C9).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.C9, hsd, Bool.false_eq_true, if_false]
      exact V6 _ _ (C7 _ _ hc1 hc2) (C7 _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.C9, hsd, if_true]
      exact V5 _ _ (C7 _ _ hc1 hc2) (C7 _ _ hs1 hs2)
  have hb1 : ((c.IQ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.IQ
    exact GU PLN c.WL _ (by norm_num) oQ (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.Gk : ℕ) : ℝ) / DZ := by
    unfold CellN.Gk
    exact Fo PUN c.WM _ (by norm_num) oR (hx2.trans hUHI) Real.pi_pos.le hx0
  have hBL0 : (0:ℝ) ≤ ((c.IQ : ℕ) : ℝ) / DZ := nd0 _
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := (nG0 GLN).trans oP
  have hp1 : ((c.Dq : ℕ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) := by
    unfold CellN.Dq
    exact GU (2 * GLN) c.IQ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := oP; linarith) hb1 (nG0 _) hBL0
  have hp2 : 2 * gam * (Real.pi * x) ≤ ((c.D8 : ℕ) : ℝ) / DZ := by
    unfold CellN.D8
    exact Fo (2 * GUN) c.Gk 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := AEd; linarith) hb2 (by linarith) hπx0
  have hP2L0 : (0:ℝ) ≤ ((c.Dq : ℕ) : ℝ) / DZ := nd0 _
  have hT1 : ((c.pD : ℤ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have hz := q6 (min ((c.Dq : ℤ) * c.C9.1) ((c.D8 : ℤ) * c.C9.1))
    have hmA : ((min ((c.Dq : ℤ) * c.C9.1) ((c.D8 : ℤ) * c.C9.1) : ℤ) : ℝ)
        ≤ (((c.Dq : ℤ) * c.C9.1 : ℤ) : ℝ) := by exact_mod_cast min_le_left _ _
    have hmB : ((min ((c.Dq : ℤ) * c.C9.1) ((c.D8 : ℤ) * c.C9.1) : ℤ) : ℝ)
        ≤ (((c.D8 : ℤ) * c.C9.1 : ℤ) : ℝ) := by exact_mod_cast min_le_right _ _
    have eA : (((c.Dq : ℤ) * c.C9.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.Dq : ℕ) : ℝ) / DZ * ((((c.C9).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.D8 : ℤ) * c.C9.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.D8 : ℕ) : ℝ) / DZ * ((((c.C9).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.pD
    refine (div_le_div_of_nonneg_right hz hD0.le).trans (aR hP2L0 hp1 hp2 hSX.1 ?_ ?_)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ ((c.pC : ℤ) : ℝ) / DZ := by
    have hz := qB (max ((c.Dq : ℤ) * c.C9.2) ((c.D8 : ℤ) * c.C9.2))
    have hmA : (((c.Dq : ℤ) * c.C9.2 : ℤ) : ℝ)
        ≤ ((max ((c.Dq : ℤ) * c.C9.2) ((c.D8 : ℤ) * c.C9.2) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hmB : (((c.D8 : ℤ) * c.C9.2 : ℤ) : ℝ)
        ≤ ((max ((c.Dq : ℤ) * c.C9.2) ((c.D8 : ℤ) * c.C9.2) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have eA : (((c.Dq : ℤ) * c.C9.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.Dq : ℕ) : ℝ) / DZ * ((((c.C9).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.D8 : ℤ) * c.C9.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.D8 : ℕ) : ℝ) / DZ * ((((c.C9).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.pC
    refine (aP hP2L0 hp1 hp2 hSX.2 ?_ ?_).trans (div_le_div_of_nonneg_right hz hD0.le)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  set N : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) with hNdef
  have hN : ((c.C6 : ℤ) : ℝ) / DZ ≤ |N| := by
    have hCX1 := (div_le_iff₀ hD0).mp hCX.1
    have hCX2 := (le_div_iff₀ hD0).mp hCX.2
    have hT1' := (div_le_iff₀ hD0).mp hT1
    have hT2' := (le_div_iff₀ hD0).mp hT2
    have ha1 := mul_le_mul_of_nonneg_right (le_abs_self N) hD0.le
    have ha2 := mul_le_mul_of_nonneg_right (neg_le_abs N) hD0.le
    rw [div_le_iff₀ hD0]
    unfold CellN.C6
    rw [Int.cast_max, Int.cast_max, Int.cast_zero]
    refine max_le (mul_nonneg (abs_nonneg _) hD0.le) (max_le ?_ ?_)
    · push_cast; rw [hNdef] at ha1; linarith
    · push_cast; rw [hNdef] at ha2; linarith
  have hNLO0 : (0:ℝ) ≤ ((c.C6 : ℤ) : ℝ) / DZ := by
    unfold CellN.C6; rw [Int.cast_max, Int.cast_zero]
    exact div_nonneg (le_max_left _ _) hD0.le
  have hD' : (0:ℝ) < ((c.CZ : ℤ) : ℝ) / DZ := by
    have : (0:ℝ) < ((c.CZ : ℤ) : ℝ) := by exact_mod_cast hD
    exact div_pos this hD0
  have hD0' : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have h1 : ((DZ * DZ : ℕ) : ℝ) < ((2 * c.IQ * c.IQ : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    have h2 : ((c.IQ : ℕ) : ℝ) / DZ * (((c.IQ : ℕ) : ℝ) / DZ) ≤ (Real.pi * x) * (Real.pi * x) :=
      mul_le_mul hb1 hb1 hBL0 hπx0
    have h3 : (1:ℝ) < 2 * (((c.IQ : ℕ) : ℝ) / DZ * (((c.IQ : ℕ) : ℝ) / DZ)) := by
      rw [div_mul_div_comm, ← mul_div_assoc, lt_div_iff₀ (mul_pos hD0 hD0)]
      linarith
    rw [pow_two]; linarith
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ ((c.CZ : ℤ) : ℝ) / DZ := by
    have h1 := EU (2 * c.Gk * c.Gk) DZ (by norm_num [DZ])
    push_cast at h1
    have h2 : (Real.pi * x) * (Real.pi * x) ≤ ((c.Gk : ℕ) : ℝ) / DZ * (((c.Gk : ℕ) : ℝ) / DZ) :=
      mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    have h3 : 2 * (((c.Gk : ℕ) : ℝ) / DZ * (((c.Gk : ℕ) : ℝ) / DZ))
        = 2 * (c.Gk : ℝ) * (c.Gk : ℝ) / DZ / DZ := by ring
    have h4 := div_le_div_of_nonneg_right h1 hD0.le
    unfold CellN.CZ
    push_cast
    rw [sub_div, div_self YP, pow_two]
    linarith
  have hfin := aY x (((c.C6 : ℤ) : ℝ) / DZ) (((c.CZ : ℤ) : ℝ) / DZ) hNLO0 hD' hD0' hDD hN
  have hWr : ((w : ℕ) : ℝ) * ((c.CZ : ℤ) : ℝ) * ((c.CZ : ℤ) : ℝ)
      ≤ ((c.C6 : ℤ) : ℝ) * ((c.C6 : ℤ) : ℝ) * ((SW : ℕ) : ℝ) := by exact_mod_cast hW
  have hDHpos : (0:ℝ) < ((c.CZ : ℤ) : ℝ) := by exact_mod_cast hD
  have e : (((c.C6 : ℤ) : ℝ) / DZ / (((c.CZ : ℤ) : ℝ) / DZ))^2
      = (((c.C6 : ℤ) : ℝ) * ((c.C6 : ℤ) : ℝ)) / (((c.CZ : ℤ) : ℝ) * ((c.CZ : ℤ) : ℝ)) := by
    rw [div_div_div_cancel_right₀ YP]; ring
  have hle : ((w : ℕ) : ℝ) / SW
      ≤ (((c.C6 : ℤ) : ℝ) * ((c.C6 : ℤ) : ℝ)) / (((c.CZ : ℤ) : ℝ) * ((c.CZ : ℤ) : ℝ)) := by
    rw [div_le_div_iff₀ hSW (mul_pos hDHpos hDHpos)]
    calc ((w : ℕ) : ℝ) * (((c.CZ : ℤ) : ℝ) * ((c.CZ : ℤ) : ℝ))
        = ((w : ℕ) : ℝ) * ((c.CZ : ℤ) : ℝ) * ((c.CZ : ℤ) : ℝ) := by ring
      _ ≤ _ := hWr
  rw [← e] at hle
  exact hle.trans hfin
theorem ZO (c : CellN) (h : c.ow = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ BK x := by
  simp only [CellN.ow, Bool.and_eq_true, decide_eq_true_eq] at h
  exact cellN_soundZ' c c.WN h.1 h.2 x hx1 hx2
theorem AEc (c : CellN) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WZ : ℝ) / SW ≤ BK x := by
  have key : ∀ b : Bool, c.ZT = b →
      ((bif b then ((c.C6 * c.C6 * SW) / (c.CZ * c.CZ)).toNat else 0 : ℕ) : ℝ) / SW ≤ BK x := by
    intro b hb
    cases b
    · simp only [cond_false, Nat.cast_zero, zero_div]; exact Bq x
    · simp only [cond_true]
      have hD : 0 < c.CZ := by
        simp only [CellN.ZT, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.2
      have hN : 0 ≤ c.C6 := by unfold CellN.C6; exact le_max_left _ _
      have hSWz : (0:ℤ) ≤ (SW : ℤ) := by positivity
      set q : ℤ := (c.C6 * c.C6 * SW) / (c.CZ * c.CZ) with hq
      have hq0 : 0 ≤ q := by
        rw [hq]; exact Int.ediv_nonneg (mul_nonneg (mul_nonneg hN hN) hSWz) (mul_pos hD hD).le
      have hqe : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      have h1 : q * (c.CZ * c.CZ) ≤ c.C6 * c.C6 * SW := by
        rw [hq]; exact Int.ediv_mul_le _ (mul_pos hD hD).ne'
      rw [← hqe] at h1
      exact cellN_soundZ' c q.toNat hb (by linarith) x hx1 hx2
  exact key c.ZT rfl
theorem CTN.WR : ∀ (t : CTN) (q : ℕ) (c : CellN), t.find q = some c → c ∈ t.toList := by
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
theorem CTN.Vv : ∀ (t : CTN), t.BX = true → ∀ c ∈ t.toList, c.ow = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CTN.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CTN.BX, Bool.and_eq_true] at h
    simp only [CTN.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc
theorem WE (t : CTN) : ∀ (ps : List (ℕ × ℕ)) (cs : List CellN),
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
        · subst hd; exact CTN.WR t _ d hf
        · exact ih cs' hr d hd
theorem E9 (c : CellN) (hok : c.ow = true) (x : ℝ)
    (h1 : (c.LN : ℝ) / SC ≤ x) (h2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ BK x :=
  ZO c hok x h1 h2
theorem Xn (t : CTN) (hok : t.BX = true) :
    ∀ (cs : List CellN), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℕ), Eo lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) / SC ≤ e → e ≤ (hi : ℝ) / SC → (chainWN cs : ℝ) / SW ≤ BK e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWN, Nat.cast_zero, zero_div]; exact Bq e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [Eo, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok := CTN.Vv t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.LN : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN, Bool.cond_eq_ite, Nat.ble_eq]
    split_ifs with hempty hle
    · have hU : hi ≤ c.UN := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [Eo, Nat.ble_eq] using hrest
      exact E9 c hcok e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact E9 c hcok e hL' hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num [SW]))
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (not_le.mp hle).le) (by norm_num [SW]))
          (E9 c hcok e hL' hU)
      · exact ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2
theorem WK (t : CTN) (hok : t.BX = true) (lo hi : ℕ) (ps : List (ℕ × ℕ)) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) :
    (termWNcore t lo hi ps : ℝ) / SW ≤ BK e := by
  unfold termWNcore
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact Xn t hok cs (WE t _ cs hcs) lo hi hch e he1 he2
    · simp only [Nat.cast_zero, zero_div]; exact Bq e
  · simp only [Nat.cast_zero, zero_div]; exact Bq e
theorem Bk (t : CTN) (hok : t.BX = true) (lo hi : ℕ) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) : (termWN t lo hi : ℝ) / SW ≤ BK e :=
  WK t hok lo hi (piecesN' lo hi) e he1 he2
end AH.Bridge.AN
namespace AH.Bridge.AN.AG
open AH.Bridge.AN
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * BK (g0) + (62369200 / (SA:ℝ)) * BK (g0 + g1) + (40126500 / (SA:ℝ)) * BK (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g1) + (37630700 / (SA:ℝ)) * BK (g1 + g2) + (119746800 / (SA:ℝ)) * BK (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * BK (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * BK (g2) + (37630700 / (SA:ℝ)) * BK (g2 + g3) + (40126500 / (SA:ℝ)) * BK (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g3) + (62369200 / (SA:ℝ)) * BK (g3 + g4) + (25326800 / (SA:ℝ)) * BK (g4)
def Box.mem (b : Box) (g0 g1 g2 g3 g4 : ℝ) : Prop :=
  (b.l0 : ℝ) / SC ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / SC ∧ (b.l1 : ℝ) / SC ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / SC ∧ (b.l2 : ℝ) / SC ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / SC ∧ (b.l3 : ℝ) / SC ≤ g3 ∧ g3 ≤ (b.u3 : ℝ) / SC ∧ (b.l4 : ℝ) / SC ≤ g4 ∧ g4 ≤ (b.u4 : ℝ) / SC
set_option maxHeartbeats 4000000 in
theorem JQ (tb : CTN) (hok : tb.BX = true) (b : Box) (h : leafCheck tb b = true)
    (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4) : (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  have w0 := Bk tb hok (b.l0) (b.u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := Bk tb hok (b.l0 + b.l1) (b.u0 + b.u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := Bk tb hok (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := Bk tb hok (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := Bk tb hok (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := Bk tb hok (b.l1) (b.u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w6 := Bk tb hok (b.l1 + b.l2) (b.u1 + b.u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w7 := Bk tb hok (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w8 := Bk tb hok (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w9 := Bk tb hok (b.l2) (b.u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w10 := Bk tb hok (b.l2 + b.l3) (b.u2 + b.u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w11 := Bk tb hok (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w12 := Bk tb hok (b.l3) (b.u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w13 := Bk tb hok (b.l3 + b.l4) (b.u3 + b.u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w14 := Bk tb hok (b.l4) (b.u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
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
      + (25326800 / (SA:ℝ)) * BK (g0) + (62369200 / (SA:ℝ)) * BK (g0 + g1) + (40126500 / (SA:ℝ)) * BK (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g1) + (37630700 / (SA:ℝ)) * BK (g1 + g2) + (119746800 / (SA:ℝ)) * BK (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * BK (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * BK (g2) + (37630700 / (SA:ℝ)) * BK (g2 + g3) + (40126500 / (SA:ℝ)) * BK (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g3) + (62369200 / (SA:ℝ)) * BK (g3 + g4) + (25326800 / (SA:ℝ)) * BK (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * BK (g0) + 62369200 * BK (g0 + g1) + 40126500 * BK (g0 + g1 + g2) + 99999900 * BK (g0 + g1 + g2 + g3) + 200000000 * BK (g0 + g1 + g2 + g3 + g4) + 48244400 * BK (g1) + 37630700 * BK (g1 + g2) + 119746800 * BK (g1 + g2 + g3) + 99999900 * BK (g1 + g2 + g3 + g4) + 52857300 * BK (g2) + 37630700 * BK (g2 + g3) + 40126500 * BK (g2 + g3 + g4) + 48244400 * BK (g3) + 62369200 * BK (g3 + g4) + 25326800 * BK (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25326800)]
theorem Box.Fe (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hle : match ax with | 0 => g0 ≤ (q : ℝ) / SC | 1 => g1 ≤ (q : ℝ) / SC | 2 => g2 ≤ (q : ℝ) / SC | 3 => g3 ≤ (q : ℝ) / SC | _ => g4 ≤ (q : ℝ) / SC) :
    (b.BG ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨h01, hle, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, h11, hle, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, h21, hle, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, h31, hle, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, hle⟩
theorem Box.Fh (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hge : match ax with | 0 => (q : ℝ) / SC ≤ g0 | 1 => (q : ℝ) / SC ≤ g1 | 2 => (q : ℝ) / SC ≤ g2 | 3 => (q : ℝ) / SC ≤ g3 | _ => (q : ℝ) / SC ≤ g4) :
    (b.BH ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨hge, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, hge, h12, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, hge, h22, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, hge, h32, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, hge, h42⟩
theorem A9 (tb : CTN) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk tb bits fuel (pos + 4) (b.BG (Ao bits pos) (b.mid (Ao bits pos))) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.BH (Ao bits pos) (b.mid (Ao bits pos))) = some pos') :
    walk tb bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, cond_true, h1]
  exact h2
theorem oN (tb : CTN) (hok : tb.BX = true) (bits : ℕ) :
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
        have hlo := ih (pos + 4) (b.BG (Ao bits pos) (b.mid (Ao bits pos))) pos1 h1 g0 g1 g2 g3 g4
        have hhi := ih pos1 (b.BH (Ao bits pos) (b.mid (Ao bits pos))) pos' h g0 g1 g2 g3 g4
        set ax := Ao bits pos with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total g0 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.Fe b 0 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.Fh b 0 q g0 g1 g2 g3 g4 hm hs)
        | 1, hlo, hhi =>
          rcases le_total g1 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.Fe b 1 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.Fh b 1 q g0 g1 g2 g3 g4 hm hs)
        | 2, hlo, hhi =>
          rcases le_total g2 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.Fe b 2 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.Fh b 2 q g0 g1 g2 g3 g4 hm hs)
        | 3, hlo, hhi =>
          rcases le_total g3 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.Fe b 3 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.Fh b 3 q g0 g1 g2 g3 g4 hm hs)
        | n + 4, hlo, hhi =>
          rcases le_total g4 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.Fe b (n + 4) q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.Fh b (n + 4) q g0 g1 g2 g3 g4 hm hs)
    · simp only [Bool.or_eq_true, Nat.blt_eq] at hleaf
      rcases hleaf with hskip | hleaf
      · right
        obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
        have hsk : ((b.u4 : ℕ) : ℝ) / SC < ((b.l0 : ℕ) : ℝ) / SC :=
          div_lt_div_of_pos_right (by exact_mod_cast hskip) (by norm_num [SC])
        linarith
      · left; exact JQ tb hok b hleaf g0 g1 g2 g3 g4 hm
theorem cover_sound (tb : CTN) (hok : tb.BX = true) (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), Bd tb aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * BK v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [Bd, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [Bd, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
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
          have hmem := CTN.WR tb _ c hfind
          have hcok := CTN.Vv tb hok c hmem
          have hW := E9 c hcok v
            (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (hpos ▸ hL)) (by norm_num [SC])) hv1)
            (hvb.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
          have hq := (Nat.cast_le (α := ℝ)).mpr hq'
          push_cast at hq
          have hSA : (0:ℝ) < SA := by norm_num [SA]
          have hSW : (0:ℝ) < SW := by norm_num [SW]
          rw [div_le_iff₀ hSA]
          have hm2 : (aAdjN : ℝ) * ((c.WN : ℝ) / SW) ≤ (aAdjN : ℝ) * BK v :=
            mul_le_mul_of_nonneg_left hW (by positivity)
          have e : (aAdjN : ℝ) / SA * BK v * SA = (aAdjN : ℝ) * BK v := by field_simp
          rw [e]
          calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
            _ ≤ (aAdjN : ℝ) * c.WN / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
            _ = (aAdjN : ℝ) * ((c.WN : ℝ) / SW) := by ring
            _ ≤ _ := hm2
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩
theorem Dr {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ Aw cover := by
  simp only [Aw, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩
set_option maxHeartbeats 4000000 in
theorem qC (tb : CTN) (hok : tb.BX = true) (bits fuel : ℕ)
    (cover0 cover1 cover2 cover3 cover4 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 : ℕ)
    (hS0 : cN * SC ≤ 24896 * S0) (hS1 : cN * SC ≤ 42034 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42034 * S3) (hS4 : cN * SC ≤ 24896 * S4)
    (hcov0 : Bd tb 25326800 (SC / 2) S0 cover0 = true) (hcov1 : Bd tb 48244400 (SC / 2) S1 cover1 = true) (hcov2 : Bd tb 52857300 (SC / 2) S2 cover2 = true) (hcov3 : Bd tb 48244400 (SC / 2) S3 cover3 = true) (hcov4 : Bd tb 25326800 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25326800)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (Aw cover0).length → i1 < (Aw cover1).length → i2 < (Aw cover2).length → i3 < (Aw cover3).length → i4 < (Aw cover4).length →
      ∃ pos pos', walk tb bits fuel pos (BJ (Aw cover0) (Aw cover1) (Aw cover2) (Aw cover3) (Aw cover4) i0 i1 i2 i3 i4) = some pos') :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => Bq v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25326800 / (SA:ℝ)) * BK (g0) + (62369200 / (SA:ℝ)) * BK (g0 + g1) + (40126500 / (SA:ℝ)) * BK (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g1) + (37630700 / (SA:ℝ)) * BK (g1 + g2) + (119746800 / (SA:ℝ)) * BK (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * BK (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * BK (g2) + (37630700 / (SA:ℝ)) * BK (g2 + g3) + (40126500 / (SA:ℝ)) * BK (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * BK (g3) + (62369200 / (SA:ℝ)) * BK (g3 + g4) + (25326800 / (SA:ℝ)) * BK (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (46137 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * BK (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * BK (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * BK (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * BK (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * BK (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (119746800 / (SA:ℝ)) * BK (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * BK (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (52857300 / (SA:ℝ)) * BK (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * BK (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * BK (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * BK (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * BK (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * BK (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (24896 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (42034 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (46137 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (42034 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (24896 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25326800 / (SA:ℝ)) * BK (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (62369200 / (SA:ℝ)) * BK (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (40126500 / (SA:ℝ)) * BK (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (99999900 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * BK (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (48244400 / (SA:ℝ)) * BK (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (37630700 / (SA:ℝ)) * BK (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (119746800 / (SA:ℝ)) * BK (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (99999900 / (SA:ℝ)) * BK (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (52857300 / (SA:ℝ)) * BK (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (37630700 / (SA:ℝ)) * BK (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (40126500 / (SA:ℝ)) * BK (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (48244400 / (SA:ℝ)) * BK (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (62369200 / (SA:ℝ)) * BK (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (25326800 / (SA:ℝ)) * BK (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
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
  · have hw19 := Dj g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * BK g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * BK g0 * SA = 25326800 * BK g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW0, hLin0]
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · left; rw [hG]; linarith [hclear0, haW0, hLin0]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (Dr hs0 he0)
  have hb01' : (((Aw cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((Aw cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
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
  · have hw19 := Dj g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * BK g1 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * BK g1 * SA = 48244400 * BK g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW5, hLin0]
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW5, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (Dr hs1 he1)
  have hb11' : (((Aw cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((Aw cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
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
  · have hw19 := Dj g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (52857300 / (SA:ℝ)) * BK g2 := by
      rw [div_le_iff₀ hSA]
      have e : (52857300 / (SA:ℝ)) * BK g2 * SA = 52857300 * BK g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 52857300)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW9, hLin0]
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW9, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (Dr hs2 he2)
  have hb21' : (((Aw cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((Aw cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
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
  · have hw19 := Dj g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * BK g3 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * BK g3 * SA = 48244400 * BK g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW12, hLin0]
  rcases cover_sound tb hok _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW12, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (Dr hs3 he3)
  have hb31' : (((Aw cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((Aw cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
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
  · have hw19 := Dj g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * BK g4 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * BK g4 * SA = 25326800 * BK g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW14, hLin0]
  rcases cover_sound tb hok _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (Dr hs4 he4)
  have hb41' : (((Aw cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((Aw cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  exact oN tb hok bits fuel pos _ pos' hwalk g0 g1 g2 g3 g4 ⟨hb01', hb02', hb11', hb12', hb21', hb22', hb31', hb32', hb41', hb42'⟩
end AH.Bridge.AN.AG
end
namespace AH.Bridge.AN.Ak
open AH.Bridge.AN AH.Bridge.AN.AG
set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil
set_option hygiene false in
local notation:max "A" l:max a0:max a1:max r:max => CTN.node l ⟨a0, a1⟩ r
set_option hygiene false in
local notation:max "B" a0:max a1:max => CTN.node CTN.nil ⟨a0, a1⟩ CTN.nil
set_option hygiene false in
local notation:max "D" l:max a0:max a1:max => CTN.node l ⟨a0, a1⟩ CTN.nil
noncomputable def AFZ : CTN :=
  A A A A A A A D B 17179893760 331038177865 25769832448 242869129569 30064800768 217716609437 D B 30064801792 122761883704 31138543104 177515141421 31675414272 158216097062 A D B 31943849984 137735430025 32212285952 100331164832 32212286048 93917126691 B 32212286464 69269436296 32212286656 59504641098 A A D B 32212287488 27393363819 32749157120 85807535666 32849820864 61025502253 B 33017592704 78876253690 33151810560 71863213630 A D B 33286028704 51174756865 33286029120 34548539408 33286029312 28203622388 B 33487355376 47896897026 33487355680 35832620095 A A A D B 33487355904 28296403112 33722236736 34824218335 33806122784 36023083580 B 34124890112 28464081354 34158444544 28467564926 A D B 34359771152 27966906972 34359771216 25976114687 34359771360 21788669253 B 34359771520 17601327427 34359771776 11891897536 A A D B 34376548576 21788669253 34443657448 21567756195 34443657600 17601327427 B 34594652592 16438965712 34594652800 11891897536 A D B 34603041152 17601327427 34762424856 14066726447 34762425008 10953811162 B 34762425312 5952302335 34762425920 560103521 A A A A D B 34812756504 14066726447 34812756608 11891897536 34921808484 12458193372 B 34921808512 11891897536 34921808560 10953811162 A D B 35001500336 10953811162 35030860520 9911220876 35030860624 8121431559 B 35030860832 5101426618 35030861248 1207853390 A A D B 35081192188 9552306668 35081192264 8252405001 35081192416 5952302335 B 35139912528 8121431559 35160884040 8252405001 A D B 35240575892 7052829560 35240575968 5952302335 35248964484 7297097729 B 35248964536 6519258779 35248964640 5101426618 A A A D B 35303490488 6519258779 35320267744 5952302335 35358016492 5787505040 B 35358016544 5101426618 35399959596 4949543969 A D B 35399959672 4043273979 35399959824 2515072630 35399960128 560103521 B 35412542496 5101426618 35467068500 4460613374 A A D B 35467068552 3864654916 35467068656 2805660000 35467068864 1207853390 B 35479651448 4043273979 35521594478 4157052951 A D B 35521594504 3864654916 35548857480 3864654916 35559343300 3232210949 B 35559343376 2515072630 35576120508 3313140707 A A A A A D B 35576120560 2805660000 35630646486 3053921840 35630646512 2805660000 D B 35639035152 2515072630 35657909488 2805660000 35685172516 2341801940 A D B 35685172568 1921155551 35685172672 1207853390 35718727004 1890576181 B 35718727080 1357438270 35718727232 560103521 A A D B 35739698520 1921155551 35794224498 1726908269 35794224524 1543309743 B 35794224576 1207853390 35798418856 1357438270 A D B 35821487500 1543309743 35848750502 1370308581 35848750528 1207853390 B 35876013504 1207853390 35878110708 914375298 A A A D B 35878110784 560103521 35903276506 1055892761 35903276532 914375298 B 35903276584 662464275 35903276688 281698711 A D B 35930539508 914375298 35957802536 662464275 35957802560 560103521 B 36012328540 451709134 36012328592 281698711 A A D B 36037494488 112798943 36066854544 281698711 36121380600 62267711 B 36339484616 872569 36339484720 861720 A D B 36339484928 840527 36356261896 5162822 36356262048 5069528 B 36448536624 93088676 36515645600 223117644 A A A A D B 36557588736 330776253 36675029456 741120989 36675029760 715005325 B 36775692752 1239113067 36775692960 1209025102 A D B 36775693376 1151561664 36775694208 1046595949 36775695872 870430129 B 36993796768 2700605352 36993796864 2670280633 A A D B 37211900992 4577595806 37312564272 5715079640 37312564576 5517323674 B 37312565184 5147011177 37312566400 4495681621 A D B 37312568832 3476319374 37631331680 9798421528 37648109024 9912085987 B 37648109440 9452356006 37950099392 14339196425 A A A D B 38084317056 17019512019 38520526336 22408627075 38587634208 26598494431 B 38587634816 24873411793 39225169024 41723990006 A D B 39862705664 48862449799 40265357312 71849923330 40802230272 75832144115 B 42412843008 143033504697 42949715968 138814108272 A A D B 42949722112 80226784524 45097201664 198611196246 47244689408 205420959916 B 51539660800 198637449669 51539664896 86044756753 A D B 55834630144 180021136485 57982114816 163928295311 59055857664 136793280978 B 60129601056 94491638858 60129601536 81450895201 A A A A A A D B 60129602624 55767572482 60129605760 10448685156 61773769792 60693484172 D B 62277085696 76332532051 62813956864 71533874347 62813958528 36234418663 A D B 62813960448 11348727666 63082392576 65993682134 63350829824 30740987631 B 63350831616 9487281504 63417937744 47901760083 A A D B 63417938528 33431430089 63417940096 12950083817 64240022112 34657649806 B 64827224928 31175188639 64827225408 23925924771 A D B 64827226368 12584622363 65062106088 29280063970 65062106480 23481709949 B 65062107264 14003693814 65229878464 26165141479 A A A D B 65229878912 20013429693 65229879808 10415393765 65330541888 24406036390 B 65473148272 23857041585 65498316608 2161654633 A D B 65699640960 20374617289 65833858848 18459576293 65833859328 13110807511 B 65884190456 18986627967 65884190848 14463712935 A A D B 66169403232 17897871080 66169403456 15309687237 66169403904 10803550826 B 66295232640 14675204480 66337175568 15936112756 A D B 66337175808 13347660291 66404284480 15432336472 66572058624 1582848890 B 66588834048 13459174918 66639165728 13152038513 A A A A D B 66639165952 10976361005 66706274628 12814740276 66706274824 10926037622 B 66706275216 7643918118 66706276000 2946728362 A D B 66773385216 1593922516 66840492528 11194943188 66840492768 9075180072 B 66840493248 5559926330 66840494080 1597382173 A A D B 66874046864 12125198229 66874046976 11057207853 66911795720 10995580721 B 66991487488 11096214651 67092150888 10180019665 A D B 67092151008 9143346818 67108928112 10113854619 67108928224 9147750004 B 67108928448 7375432064 67108928896 4448654319 A A A D B 67108929536 1610049271 67117316812 9318555343 67117317008 7739338858 B 67217980128 9175937000 67226368736 9178074010 A D B 67322837904 7783388904 67343809304 8741472593 67343809308 8708696702 B 67343809360 8288808736 67343809368 8225229524 A A D B 67343809472 7423250095 67343809488 7303892679 67343809728 5640238273 B 67402529616 8301690467 67406723928 8238911471 A D B 67444473856 1623212765 67461249928 7873550154 67461249984 7445974946 B 67469638548 7782485830 67469638608 7327793443 A A A A A D B 67519970240 7457039161 67528358996 6389620907 67528359192 5112338736 D B 67528359584 3014641983 67532553168 7339404162 67578690552 7052143803 A D B 67578690608 6649469153 67578690720 5882978144 67578690944 4502618747 B 67595467788 6909649270 67595467848 6483499126 A A D B 67595467968 5675672665 67637410864 6658849147 67645800448 1629667415 B 67658382408 6493202326 67696131176 6277139081 A D B 67696131232 5899168453 67721297028 6090042938 67721297088 5692191388 B 67733880088 5136608560 67754851488 5906996256 A A A D B 67784211648 5700149103 67813571800 5548402149 67813571856 5194930705 B 67813571968 4525894726 67847126268 5323497268 A D B 67847126328 4953689762 67847126448 4257371715 67847126688 3034366931 B 67847127040 1635028490 67872292112 5201337041 A A D B 67910040888 4960062291 67931012424 4865780009 67931012480 4536594730 B 67939401082 4572011828 67939401180 4023529817 A D B 67939401376 3039374584 67972955508 4609817493 67972955568 4267788773 B 67989732736 4541708976 68035870128 4272734627 A A A A D B 68042161628 4031082298 68048453048 4229100667 68048453104 3923980516 B 68048453216 3350657150 68048453440 2348735452 A D B 68048453632 1639288723 68082008064 1639891309 68098784748 3948783922 B 68098784808 3634258234 68098784928 3047276581 A A D B 68107173332 4079146011 68107173360 3927930664 68136533488 3929850689 B 68144922174 3525059155 68144922272 3049386725 A D B 68161699368 3637934079 68165893672 3638173367 68165893728 3356889421 B 68224613984 3359802040 68224613988 3340152262 A A A D B 68224614048 3052843544 68247682720 3053799706 68283334296 3092788800 B 68283334352 2835104416 68283334464 2355626049 A D B 68283334656 1642860036 68287528608 3055404148 68316889088 1643246852 B 68342054608 2837104612 68350443228 2783653893 A A D B 68350443266 2617150557 68350443288 2523266003 68350443364 2213008870 B 68350443408 2043285208 68350443520 1643602777 A D B 68400774920 2592719328 68400774976 2358390270 68413357848 2524864183 B 68453203812 2214947727
noncomputable def AFa : CTN :=
  A A A A A A A D B 68476272468 2278996207 68476272528 2045223127 68518215544 2137719202 D B 68518215600 1926493811 68518215680 1644918596 68539187088 2046009702 A D B 68555964358 1847016775 68555964416 1645108045 68576935856 1927038462 B 68602101708 1825862929 68602101760 1645286377 A A D B 68635656168 1727524819 68635656192 1645379299 68658724864 1645425217 B 68665016320 1645435199 68694376448 1645467384 A D B 68719542280 1618528484 68719542304 1539049347 68719542312 1513010505 B 68719542400 1241535499 68719542464 1061259562 A A A D B 68719542528 895367555 68719542688 543159341 68719542704 512823329 B 68719542720 483371336 68719542880 237237242 A D B 68719542992 116894912 68719543104 38888271 68719543136 24319712 B 68727930948 1423660828 68727931008 1241535499 A A D B 68753096792 1361538899 68753096848 1195114728 68753096960 895367555 B 68753097568 24319712 68761485450 1212416788 A D B 68761485548 945667338 68761485744 512823329 68790845568 1241535499 B 68811817104 1195114728 68836983616 38888271 A A A A D B 68853760248 915319519 68853760368 639481934 68853760608 237237242 B 68864245996 945667338 68870537472 895367555 A D B 68967006542 712545145 68967006640 512823329 68979589488 639481934 B 68987978096 639481934 68987978208 427115186 A A D B 68987978432 131485341 69038310192 47455440 69069767088 512823329 B 69105418720 427115186 69105418728 413602006 A D B 69105418848 237237242 69155750816 5411364 69172527732 212624827 B 69172527928 43064821 69222859456 131485341 A A A D B 69231247968 237237242 69357077328 31176768 69378048824 43064821 B 69457740704 5411364 69776508704 811040 A D B 69793285632 2395549 69793285840 2365704 69793285936 2352087 B 69793286144 2322919 69793286544 2268088 A A D B 69793286560 2265929 69793286752 2240217 69793287088 2196094 B 69793287168 2185750 69793287392 2157108 A D B 69793287968 2085588 69793288000 2081703 69793288384 2035776 B 69793289216 1940543 69810063168 4693333 A A A A A D B 69843617232 12058639 69843617440 11908301 69860394528 16843388 D B 69860395008 16364291 69893949024 28883500 69910726256 36131620 A D B 69910726312 36009941 69910726464 35682246 69927503424 44356720 B 69927503872 43178297 69994612296 85052049 A A D B 69994612416 84439382 69994612624 83390467 69994612688 83071012 B 69994612720 82911860 69994612928 81886628 A D B 69994613472 79279373 69994615040 72324742 70011389496 97393132 B 70011389544 97111674 70011389648 96505337 A A A D B 70011389952 94759960 70028167088 108011776 70028167392 106064860 B 70028167504 105358671 70028167808 103471352 A D B 70061721248 138285081 70061721456 136566458 70061721664 134874514 B 70061722080 131568687 70061722496 128363755 A A D B 70061722704 126797969 70061722912 125256038 70061723328 122242010 B 70061724160 116481657 70061724992 111057344 A D B 70061725824 105945771 70061727488 96576815 70061727744 95228999 B 70070109808 146348098 70070110016 144527946 A A A A D B 70112052936 186786469 70112053040 185621927 70112053248 183320007 B 70120441552 195555862 70128830120 205115684 A D B 70128830272 203249109 70170773096 254658041 70170773200 253068030 B 70195940320 263475724 70195940736 257105912 A A D B 70212716328 305093958 70212716432 303194579 70212716736 297726860 B 70221104944 316236111 70229493512 328521270 A D B 70229493560 327574871 70229493664 325536030 70229493720 324444778 B 70229493872 321505826 70229493968 319666822 A A A D B 70229494176 315727311 70229494784 304555423 70229496000 283658578 B 70263049056 352533813 70263049664 340141246 A D B 70263049888 335713460 70263050496 324053974 70263051552 304983336 B 70263052160 294639592 70279825104 403395097 A A D B 70279825160 402038575 70279825264 399534449 70279825368 397049835 B 70279825472 394584551 70279826720 366445045 A D B 70288213824 413627040 70313380032 443377911 70321768336 465227136 B 70330156800 483303735 70330156904 480293078 A A A A A A D B 70330156952 478911471 70330157056 475935030 70338545568 492790117 D B 70346934344 502027825 70346934496 497487919 70346934760 489724393 A D B 70346934912 485323301 70363711488 533284000 70388877112 585448546 B 70388877168 583482927 70388877216 581804688 A A D B 70388877376 576254061 70397265920 593941094 70405654480 611378969 B 70430820344 658228367 70430820448 654143399 A D B 70430820648 646376573 70430820656 646068310 70430820752 642383481 B 70430820960 634489588 70430821376 619063056 A A A D B 70430822208 589594224 70439208808 680600276 70439208960 674424696 B 70447597528 692802516 70447597680 686526830 A D B 70447597984 674187690 70464375120 710792950 70464375424 698060319 B 70489540504 782724448 70489540608 777859807 A A D B 70497929072 802729041 70497929120 800420197 70497929176 797737052 B 70497929280 792783899 70497929384 787869220 A D B 70497929488 782992656 70497929696 773352456 70497929904 763860504 B 70497930112 754514068 70497930944 718530834 A A A A D B 70506318048 803172821 70506318464 783533570 70531483840 859851306 B 70539872352 883700703 70548260816 910627921 A D B 70548260920 904973145 70548260968 902378090 70548261072 896787379 B 70548261280 885735549 70598592512 1027720232 A A D B 70598594304 924442220 70598595136 880920042 70598595520 861699413 B 70598596352 821824466 70598597952 751428422 A D B 70598598016 748772886 70598598656 722853285 70606981080 1050920006 B 70606981128 1047902063 70606981184 1044394840 A A A D B 70606981232 1041400348 70606981392 1031496087 70632147536 1073153345 B 70632147744 1060003687 70632148144 1035278337 A D B 70632148352 1022706643 70648924208 1151655895 70648924312 1144514750 B 70648924360 1141237552 70648924464 1134177194 A A D B 70648924664 1120752726 70648924768 1113850670 70657312824 1172974246 B 70657312976 1162364326 70665701544 1187076428 A D B 70665701696 1176357022 70665701752 1172438358 70665701904 1161884123 B 70665702168 1143834430 70665702208 1141130358 A A A A A D B 70665702320 1133601450 70665702624 1113477271 70665703232 1074553868 B 70665704448 1001688603 70707644520 1304841135 A D B 70707644624 1296756953 70716033088 1331293683 70716033136 1327476594 B 70716033192 1323040638 70716033296 1314851598 A A D B 70716033504 1298663154 70716033920 1267028524 70732816384 973352611 B 70749587752 1407063859 70749587856 1398371502 A D B 70749588064 1381187693 70757976216 1443460589 70757976368 1430422877 B 70757976672 1404787090 70766364832 1467217348 A A A D B 70766364936 1458134824 70766365088 1444986704 70783142528 1474006013 B 70808307912 1588790038 70808308016 1578960862 A D B 70816696528 1613660963 70816697056 1563775751 70825085096 1643421514 B 70825085200 1633249457 70825085248 1628581271 A A D B 70825085456 1608544589 70825085872 1569389271 70850251552 1658854628 B 70850252160 1600486554 70858639760 1725085932 A D B 70867028224 1766764404 70867028328 1755843377 70867028376 1750831434 B 70867028416 1746668500 70867028448 1743347080 A A A A D B 70867028480 1740033569 70867028688 1718686990 70867028784 1708945411 B 70867028864 1700880224 70867028928 1694462386 A D B 70867028992 1688074859 70867029760 1613727322 70867029888 1601737870 B 70867031552 1455574872 70867031808 1434595441 A A D B 70867034112 1261829101 70875416840 1792926082 70883805712 1791752673 B 70883806016 1759748092 70900583456 1789151540 A D B 70900583568 1777386402 70900583872 1745937500 70900584704 1663361889 B 70900586368 1512378518 70917359920 1926484219 A A A D B 70925748536 1953744374 70925748640 1941677713 70934137052 1993040971 B 70934137104 1986865795 70934137208 1974587193 A D B 70934137312 1962403517 70934137416 1950313884 70934137520 1938317424 B 70934137728 1914600582 70934137832 1902878502 A A D B 70934137936 1891246201 70934138144 1868247640 70934138560 1823292115 B 70934138976 1779683648 70934139392 1737373987 A D B 70934140640 1617784893 70934141056 1580226720 70934142976 1420381457 B 70967691768 2073930708
noncomputable def AFb : CTN :=
  A A A A A A A D B 70976080232 2121127843 70976080384 2102028974 70984468952 2136394753 D B 70984469104 2117190646 70984469160 2110170001 70984469312 2091260458 A D B 70984469576 2058919357 70984469728 2040582806 70988663056 2176932026 B 71026411928 2295032188 71026412032 2280878086 A A D B 71034800544 2324647087 71043189112 2361179887 71043189216 2346610841 B 71043189264 2339924658 71043189424 2317809076 A D B 71043189840 2261522057 71068355568 2365116209 71068355776 2336314258 B 71068356176 2282150294 71068356192 2280016634 A A A D B 71068356384 2254606601 71068356800 2200757334 71068357632 2097806599 B 71076743776 2453155827 71085132240 2506102589 A D B 71085132344 2490659729 71085132392 2483572472 71085132496 2468303226 B 71085132800 2424339420 71101909784 2520920323 A A D B 71101909936 2498367647 71101910240 2454015554 71101910848 2368231463 B 71135463936 2693981632 71135465728 2425206911 A D B 71143852656 2709132836 71143852864 2675952866 71143853280 2611106324 B 71152241068 2774477950 71152241120 2765908458 A A A A D B 71152241224 2748868733 71152241328 2731960330 71152241432 2715182033 B 71152241536 2698532640 71152241848 2649346056 A D B 71152241952 2633200514 71185795736 2870466628 71185795784 2862310359 B 71185795888 2844737817 71185796096 2809996363 A A D B 71194184248 2921231723 71194184400 2895010348 71202572968 2936225632 B 71202573120 2909913683 71206767072 2988757687 A D B 71219350976 2868458953 71244516048 3103672014 71261293128 3200587696 B 71261293232 3180900751 71261293440 3141979921 A A A D B 71261293488 3133083064 71261293856 3065911830 71269682560 3083169201 B 71286459584 3188481743 71286460192 3076971327 A D B 71294847792 3300935012 71303236360 3345372451 71303236512 3315436926 B 71303236568 3304492699 71303236720 3275014266 A A D B 71303236816 3256565960 71303236984 3224593606 71303237024 3217039180 B 71303237136 3196004429 71303237440 3139772410 A D B 71336790912 3469172384 71336791488 3353558517 71345179440 3523175912 B 71361956672 3595494304 71370345136 3664745543 A A A A A D B 71370345240 3642238559 71370345344 3619904491 71370345408 3606245703 D B 71370345448 3597741743 71370345552 3575748739 71370345760 3532265730 A D B 71370345968 3489443174 71370346176 3447269043 71370347008 3284825021 B 71370348672 2987709215 71403899904 3745497722 A A D B 71420677192 3806946905 71420677344 3773042578 71462620064 4043653003 B 71462620272 3994351746 71462620688 3897987866 A D B 71471009952 3789328716 71471010368 3699325567 71471011168 3533643236 B 71471011584 3451160281 71471013888 3035541833 A A A D B 71479397144 4157901927 71479397248 4132405831 71479397456 4081998565 B 71504563296 4199724892 71504563504 4148666078 A D B 71504563600 4125362838 71504563808 4075432429 71504564208 3981522070 B 71504564416 3933759813 71521340528 4277752557 A A D B 71521340832 4202026757 71538117968 4303500244 71538118272 4227569083 B 71538118384 4200018034 71538118688 4126362338 A D B 71538118880 4080675741 71538119296 3983842031 71538119520 3932892559 B 71538120128 3798657876 71538120512 3716828417 A A A A D B 71538121344 3546971375 71538122752 3281075879 71580060896 4541047581 B 71588449152 4679568975 71588449256 4650918466 A D B 71588449360 4622487389 71588449464 4594273727 71588449568 4566275481 B 71588449984 4456397484 71622003920 4759697312 A A D B 71622004128 4701926177 71622004544 4588995427 71638781424 4765641438 B 71638782208 4553028902 71697501264 5197284847 A D B 71697501472 5134083095 71705890384 5087720185 71705890592 5026315551 B 71705891008 4906266489 71722667312 5264985379 A A A D B 71722667616 5172046085 71722668224 4992252331 71739444752 5286596046 B 71739445056 5193581166 71806553376 5735836610 A D B 71806553584 5666299604 71806553792 5597815537 71806553856 5576952381 B 71806554208 5463930158 71806554624 5334032333 A A D B 71806555456 5085637335 71806556288 4851563615 71806557120 4630829728 B 71806557952 4422531958 71806558208 4360811591 A D B 71823330704 5793228535 71823330912 5723111485 71840107936 5883473264 B 71856885376 5902067787 71856885792 5760774041 A A A A A A D B 71873662848 5909195206 71873663936 5549362183 71873664768 5292566695 D B 71873666432 4822112994 71907217984 5856992598 71907219200 5464082534 A D B 71923994400 6232361261 71940771840 6248616222 71940772256 6099857213 B 71940772864 5890329606 71974326304 6432896808 A A D B 71974326912 6210711176 72007882624 5952087208 72024657392 6955963330 B 72024657600 6871892121 72041434720 7014623377 A D B 72058212160 7027041309 72142098416 7479338237 72142098624 7389616249 B 72175653088 7587921710 72175653504 7407861677 A A A D B 72175654336 7063516044 72242761824 8080762806 72242762240 7888653193 B 72343425408 8613448571 72343426016 8317444884 A D B 72343426432 8122234720 72343427264 7748731334 72343428480 7240694588 B 72343429120 6990049945 72360202432 8824613493 A A D B 72376979872 8825249880 72410535360 8524215433 72410536576 7959429123 B 72460865792 9495088681 72578307072 9902332772 A D B 72678969856 10948895995 72678970688 10439028257 72678971520 9958557075 B 72678973184 9077905685 72746079744 10811791513 A A A A D B 72746080000 10655959455 72779633440 11533897614 72779634048 11139873131 B 72813188928 11105875671 72813189760 10598343178 A D B 72880297728 11647389636 72980961472 12109810408 73148735488 12104668324 B 73215841888 14448378430 73215842496 13960550597 A A D B 73282950944 14857838096 73282952512 13609766906 73282953216 13092218008 B 73551388416 15396192461 73551388672 15181324901 A D B 73618496896 16291095525 74088259584 19807550595 74625130496 25011984158 B 74893565952 27822280170 74927119680 29297129812 A A A D B 76571287552 48205106293 77309485184 58065467467 77309485312 57660655940 B 77309485632 56663983892 77309486080 55304609886 A D B 77309486464 54171800066 77309486592 53800665600 77309486848 53067900800 B 77309487488 51289931616 77309487744 50599666909 A A D B 77309488128 49585936005 77309490176 44588844334 77309493248 38217750111 B 78383228928 66621352329 78920099840 74031506677 A D B 79456972800 73216762336 79859630080 63659306163 81604460544 81183335634 B 85899428352 109765623306 85899431936 79111303097 A A A A A D B 86436305536 53004511037 86436306944 39318844855 90194400256 80671901826 D B 90194401280 68661704304 91268142592 77497786488 91805014016 72628020867 A D B 92341885440 67628919902 92341886976 49536554442 92878757888 50467184291 B 93012975616 50699076958 93415628800 51392597158 A A D B 94489370784 51327999103 94489371424 44006914778 94489372352 34217161524 B 94489374000 19643703773 94489374272 17615762145 A D B 94489375488 9922881374 94489377824 1423248691 94489378816 160224349 B 94657144512 34411146944 95059804160 176907171 A A A D B 95328235072 18172374418 96099990400 1945186969 96099991552 206735025 B 96301312464 28478145000 96301313248 21586571353 A D B 96301314816 10674030422 96636861440 1714381431 96636861568 1446849664 B 96703968480 8244503734 96703969360 4453887415 A A D B 96703970048 2329647804 96703970144 2090068266 97039513024 7256614180 B 97039514240 2715081608 97039515648 232263036 A D B 97123396832 22159224528 97526053728 2180022236 97844822016 252482848 B 97945481200 16500252866 97945481984 11300791054 A A A A D B 98029367804 12946140206 98029369032 6301883961 98029371392 256850309 B 98046147200 2841563738 98113256320 2159438981 A D B 98314580232 14689684134 98314580944 10212442777 98314582368 3776822187 B 98314582656 2873275307 98348136384 5321078872 A A D B 98348137216 2516857005 98348138496 264132154 98448799776 4958828936 B 98448799824 4773902876 98448800608 2272939221 A D B 98448801792 266359493 98515908864 4137723023 98515908928 3914581170 B 98515909760 1599277638 98767565568 11590074750 A A A D B 99052780864 1246402422 99052781568 278942769 99061167056 10445252625 B 99119889280 2251194927 99220551664 5281456119 A D B 99220552032 3900873562 99220552448 2603671412 99270884192 2347645316 B 99317019746 9687208967 99317020360 6572872093 A A D B 99321215840 2351954199 99388324096 4262812040 99455433856 1663487905 B 99589649936 7498406254 99589650720 4174152875 A D B 99589652064 783539446 99589652288 486187750 99589652480 288917761 B 99656760064 2643419676
noncomputable def AFc : CTN :=
  A A A A A A A D B 99807753880 6890494413 99807754592 3974337117 99858087008 1760442653 D B 99858087488 841589994 99858087936 293446035 99960846024 6695562123 A D B 100042636032 2676434431 100092967312 3840370491 100092967728 2545443724 B 100092968096 1630716019 100092968512 849511082 A A D B 100092968560 776217023 100092968960 297145356 100126523200 498744885 B 100126523392 297653366 100181046936 6960725554 A D B 100193631904 709186254 100193632256 298653847 100260740544 1068259502 B 100260740992 428360450 100260741056 361046284 A A A D B 100327848640 2886541577 100327848928 2096644761 100327849088 1714806949 B 100327849536 856999450 100327849888 395130974 A D B 100327849984 300592119 100361403968 858033367 100411734304 4274937711 B 100529174952 3804041658 100529175344 2578463764 A A D B 100529176128 863066882 100554340348 5436229149 100554340704 4059317735 B 100596285440 304213890 100604671995 5447376422 A D B 100604672302 4245476007 100604672916 2310708476 100604674048 304321524 B 100730502208 1885002765 100730503040 436514729 A A A A D B 100797611136 1738893226 100864719680 2556967943 100864720096 1529452436 B 100864720160 1395712871 100864720400 950811828 A D B 100864720576 680526958 100864720896 307488777 100915051288 2673896180 B 100915051680 1671921264 100915052096 873770218 A A D B 100915052536 315570708 100915052544 308063547 100926585134 4280119986 B 100927633760 4098118583 100940217136 2607118091 A D B 100965383264 1821171196 100965383440 1432544450 100965383744 875075196 B 100965383792 800017648 100965384192 308625792 A A A D B 100998938016 1151768401 100998938432 515432166 100998938624 308993641 B 101066047488 309712523 101099601120 1539169514 A D B 101099601728 517048284 101133156288 373441793 101200264288 1832176823 B 101200264704 987012771 101200264736 933162428 A A D B 101200265152 374224936 101200265216 311082644 101233818672 1948897568 B 101233819456 519100870 101248498273 3253072080 A D B 101248498580 2349737210 101267373664 831663358 101267374080 311733677 B 101284150368 1835943385 101284150848 882843632 A A A A A D B 101300927172 2948437239 101300927528 1971649217 101300927712 1547006103 D B 101300928016 962420428 101300928192 689264401 101300928240 622934764 A D B 101300928512 312050644 101326093264 2195231875 101326093472 1689612318 B 101326093888 883801430 101334482848 409652702 A A D B 101334482944 312361894 101351259320 1636716411 101351259504 1253660737 B 101351259712 884368870 101368036640 1414219921 A D B 101368037056 690481888 101368037376 312667416 101435145312 1842503771 B 101435145568 1287451772 101435145840 810329864 A A A D B 101435146048 521958689 101468699920 1450883267 101468700224 886944905 B 101519031824 967589563 101519032320 313971080 A D B 101544197280 1698187650 101569363520 889058122 101570411412 2367093389 B 101602917776 1199541435 101602918080 694473172 A A D B 101602918272 448212564 101602918400 314644752 101636472096 1422968634 B 101636472320 997580095 101636472560 628180272 A D B 101636472768 378703146 101653249856 524752165 101670026576 1326144669 B 101670026784 943909253 101670027200 379003222 A A A A D B 101674220584 1988345713 101686804352 449093663 101686804480 315282088 B 101703581248 891738801 101703581696 315405182 A D B 101737135448 1312070132 101737135656 931910293 101737135840 651527793 B 101737135936 525742082 101737136048 396516773 A A D B 101737136072 371260413 101737136128 315646986 101762301296 1265410928 B 101762301504 892862157 101787467328 893334352 A D B 101787467352 854659033 101787467744 347242848 101787467768 323667920 B 101787467776 315998717 101804244432 1086013216 A A A D B 101804244464 1029057751 101804244672 697557231 101837799424 316337253 B 101846188032 316392391 101854576576 380539005 A D B 101871353344 1002545820 101871353392 921190939 101871353600 609759252 B 101871353856 316555598 101888130592 948227998 A A D B 101892324551 1622558406 101892324858 1013390233 101892325376 316689076 B 101921684944 1088575222 101921685184 699211358 A D B 101938462320 819359215 101938462528 527924860 101955239464 936038427 B 101955239752 518197269 101955239856 398301651 A A A A A A D B 101972016880 632602659 101972017152 317175288 101980405312 896769545 D B 102005571456 452043142 102005571584 317370043 102022348480 700543698 A D B 102047513996 1218129496 102047514352 633482992 102055902912 700970219 B 102055903040 529071597 102064291760 399089354 A A D B 102072680448 317741796 102089457168 979064140 102089457408 612259304 B 102089457664 317831030 102106234496 797044926 A D B 102106234592 656231045 102106234608 634138386 102106234736 471435525 B 102106234816 382318507 102106234880 317918781 A A A D B 102123012096 318005047 102139788848 925817445 102139789056 612786881 B 102139789072 591463497 102139789280 349545719 A D B 102139789312 318089829 102148177632 656700394 102148177840 399647521 B 102148177920 318131662 102156566336 529979902 A A D B 102173343424 702393563 102173343480 623943145 102173343536 550290788 B 102173343688 374337307 102173343744 318254933 A D B 102198509536 349862968 102198509568 318374856 102206898176 318414087 B 102214237690 1019360321 102223675392 318491431 A A A A D B 102240452352 613786266 102240452464 472446304 102240452592 334131731 B 102240452608 318567285 102282395648 318750399 A D B 102290784048 551291016 102290784136 444960566 102290784256 318785903 B 102307561184 658361915 102307561392 400593178 A A D B 102307561424 366748182 102307561472 318855792 102324338624 383564587 B 102341115544 763402311 102341115632 636502420 A D B 102341115648 614711096 102341115840 383648990 102341115904 318991089 B 102357892824 670089558 102357892864 614857970 A A A D B 102357892976 473235408 102357893088 350627608 102357893120 319056497 B 102366281544 521679654 102366281648 400903526 A D B 102374670096 593592028 102374670112 572573511 102374670248 409657343 B 102374670304 350699877 102374670336 319120409 A A D B 102391447496 375467795 102391447552 319182826 102420807408 637210518 B 102425001752 583429158 102425001904 401193332 A D B 102425001984 319303171 102441779200 319361098 102450167552 615628606 B 102450167808 319389499 102475333552 401425366 A A A A A D B 102475333632 319472457 102483722016 573388557 102483722240 319499360 B 102492110712 464622289 102492110832 335152076 A D B 102492110848 319525889 102500499456 319552042 102508888064 319577821 B 102517276528 474163478 102525665200 401642270 A A D B 102525665280 319628253 102536151040 319659011 102542442496 319677185 B 102559219560 483892900 102559219648 384596801 A D B 102559219664 367801282 102559219712 319724616 102575996776 483978809 B 102575996880 367858623 102575996928 319770546 A A A D B 102584385336 543169143 102584385456 401876181 102584385536 319792947 B 102592774008 465125610 102592774024 446577839 A D B 102592774112 351496461 102592774128 335463568 102592774144 319814974 B 102609551240 446650842 102609551304 376323981 A A D B 102609551344 335510100 102609551360 319857900 102617939800 503520086 B 102617939952 335532790 102626328488 410774903 A D B 102626328576 319899323 102634717184 319919471 102643105792 319939243 B 102659883008 319977661 102668271568 368145181 A A A A D B 102668271616 319996305 102676660112 437786098 102676660224 320014574 B 102685048784 368192040 102693437440 320049984 A D B 102701826016 351794995 102701826032 335738508 102701826048 320067124 B 102710214576 402307893 102718603248 335775030 A A D B 102718603264 320100277 102735380480 320131925 102743769040 368343332 B 102743769088 320147185 102768934888 343862219 A D B 102768934912 320190706 102777323456 385266232 102777323504 335890714 B 102777323520 320204460 102794100736 320230839 A A A D B 102802489276 389598772 102802489344 320243463 102810877912 360211065 B 102810877952 320255712 102815072256 320261695 A D B 102827655168 320279078 102836043776 320290197 102844432384 320300938 B 102861209600 320321292 102869598204 324220577 A A D B 102869598208 320330904 102877986816 320340138 102882181120 320344615 B 102886375424 320348997 102894764032 320357478 A D B 102903152640 320365582 102911541248 320373310 102919929856 320380661 B 102928318464 320387635
noncomputable def AFd : CTN :=
  A A A A A A A D B 102945095680 320400452 102949289984 320403421 102953484288 320406296 D B 102961872896 320411762 102970261504 320416851 102987038720 320425900 A D B 102995427328 320429858 103008010240 320435089 103012204544 320436644 B 103020593152 320439472 103024787456 320440744 A A D B 103028981760 320441923 103037370368 320443996 103041564672 320444892 B 103045758976 320445693 103049953280 320446400 A D B 103054147584 320447012 103062536192 320447955 103075119104 320448662 B 103079313536 208253265 103079313664 120294753 A A A D B 103079313792 56434938 103079313920 16522152 103079314048 391458 B 103213531520 56434938 103213531648 16522152 A D B 103213531776 391458 103347749376 16522152 103347749504 391458 B 103481967104 16522152 103481967232 391458 A A D B 103616184960 391458 103884620672 7824063 103884620800 7783588 B 103884620928 7743374 103884621056 7703420 A D B 103884621184 7663724 103884621312 7624283 103884621440 7585096 B 103884621568 7546161 103884621696 7507476 A A A A D B 103884621824 7469038 103884621952 7430847 103884622080 7392899 B 103884622208 7355194 103884622336 7317728 A D B 103884622464 7280502 103884622592 7243512 103884622720 7206757 B 103884622848 7170235 103884622976 7133944 A A D B 103884623104 7097883 103884623232 7062050 103884623360 7026443 B 103884623488 6991060 103884623872 6886241 A D B 103884624000 6851738 103884624128 6817452 103884624256 6783381 B 103884624384 6749522 103884624768 6649206 A A A D B 103884625024 6583364 103884625152 6550749 103884625536 6454109 B 103884625664 6422292 103884625792 6390672 A D B 103884625920 6359246 103884626304 6266122 103884627200 6055379 B 103884627456 5996802 103884627968 5881758 A A D B 104018838528 38550747 104018838656 38351576 104018838784 38153692 B 104018838912 37957083 104018839040 37761741 A D B 104018839168 37567655 104018839296 37374816 104018839424 37183214 B 104018839552 36992839 104018839680 36803682 A A A A A D B 104018839808 36615735 104018840064 36243429 104018840192 36059052 D B 104018840448 35693806 104018840704 35333178 104018840832 35154574 A D B 104018840960 34977098 104018841088 34800741 104018841856 33765649 B 104018844160 30883143 104018844672 30284912 A A D B 104018845696 29131321 104153056384 92367279 104153056512 91890686 B 104153056640 91417168 104153056768 90946698 A D B 104153056896 90479255 104153057024 90014814 104153057152 89553353 B 104153057280 89094848 104153057408 88639277 A A A D B 104153057536 88186617 104153057664 87736846 104153057792 87289942 B 104153057920 86845883 104153058048 86404646 A D B 104153058176 85966212 104153058304 85530558 104153058432 85097663 B 104153058560 84667506 104153058688 84240066 A A D B 104153058816 83815324 104153058944 83393257 104153059072 82973847 B 104153059328 82142915 104153059456 81731354 A D B 104153059712 80915943 104153059840 80512055 104153059968 80110686 B 104153060096 79711817 104153060224 79315431 A A A A D B 104153060480 78530030 104153060608 78140978 104153060992 76988205 B 104153061376 75856633 104153061504 75484072 A D B 104153061760 74745794 104153062144 73655234 104153062528 72584511 B 104153063040 71186992 104153063168 70842885 A A D B 104153063424 70160892 104287274240 169058946 104287274368 168187774 B 104287274496 167322213 104287274624 166462218 A D B 104287274752 165607748 104287274880 164758759 104287275008 163915209 B 104287275136 163077057 104287275264 162244261 A A A D B 104287275392 161416780 104287275520 160594573 104287275648 159777600 B 104287275776 158965821 104287275904 158159197 A D B 104287276160 156561255 104287276288 155769859 104287276416 154983463 B 104287276544 154202029 104287276672 153425518 A A D B 104287276800 152653895 104287277056 151125160 104287277312 149615534 B 104287277568 148124730 104287277952 145923201 A D B 104287278208 144478233 104287278720 141641611 104287279872 135509667 B 104287280896 130335553 104287281152 129080835 A A A A A A D B 104421492096 268398722 104421492224 267017435 104421492352 265645031 D B 104421492480 264281444 104421492608 262926604 104421492736 261580444 A D B 104421492864 260242897 104421492992 258913898 104421493120 257593381 B 104421493248 256281280 104421493376 254977533 A A D B 104421493504 253682074 104421493632 252394840 104421493888 249844799 B 104421494016 248581868 104421494144 247326916 A D B 104421494272 246079881 104421494528 243609325 104421494784 241169728 B 104421494912 239961393 104421495168 237567365 A A A D B 104421495296 236381558 104421495680 232868298 104421496704 223813938 B 104421496960 221619516 104421497344 218378112 A D B 104555709952 390147459 104555710080 388142198 104555710208 386149818 B 104555710336 384170219 104555710464 382203303 A A D B 104555710592 380248972 104555710720 378307131 104555710848 376377682 B 104555710976 374460531 104555711104 372555585 A D B 104555711232 370662749 104555711360 368781933 104555711488 366913043 B 104555711616 365055989 104555711744 363210682 A A A A D B 104555711872 361377031 104555712000 359554950 104555712128 357744350 B 104555712256 355945144 104555712512 352380573 A D B 104555712640 350615038 104555712896 347117049 104555713280 341951534 B 104555713408 340251097 104555713664 336881845 A A D B 104555713792 335212874 104555714176 330267653 104555716608 300979524 B 104689927936 531312735 104689928064 528588957 A D B 104689928192 525882631 104689928320 523193621 104689928448 520521794 B 104689928576 517867020 104689928704 515229167 A A A D B 104689928832 512608105 104689928960 510003708 104689929088 507415847 B 104689929216 504844397 104689929344 502289233 A D B 104689929472 499750230 104689929600 497227267 104689929728 494720222 B 104689930240 484848826 104689930368 482419584 A A D B 104689930496 480005552 104689930624 477606617 104689931136 468159590 B 104689931520 461227380 104689931776 456677173 A D B 104689932032 452182996 104689932160 449956660 104689933184 432630731 B 104689934336 414124897 104824145792 696268059 A A A A A D B 104824145920 692703231 104824146048 689161212 104824146176 685641829 D B 104824146304 682144906 104824146432 678670273 104824146560 675217758 A D B 104824146688 671787193 104824146816 668378410 104824146944 664991244 B 104824147072 661625530 104824147200 658281105 A A D B 104824147328 654957807 104824147456 651655476 104824147584 648373954 B 104824147840 641872708 104824147968 638652674 A D B 104824148096 635452827 104824148224 632273016 104824148480 625972900 B 104824148736 619751139 104824148864 616669275 A A A D B 104824149248 607538028 104824149632 598575336 104824150144 586880855 B 104824150528 578297144 104824151296 561595838 A D B 104824152064 545493685 104958363648 882735747 104958363776 878222031 B 104958363904 873737158 104958364032 869280908 A A D B 104958364160 864853062 104958364288 860453403 104958364416 856081715 B 104958364544 851737785 104958364672 847421402 A D B 104958364800 843132356 104958364928 838870438 104958365056 834635445 B 104958365184 830427171 104958365312 826245413 A A A A D B 104958365440 822089973 104958365568 817960650 104958365824 809779573 B 104958365952 805727429 104958366080 801700626 A D B 104958366208 797698973 104958366592 785843041 104958366720 781940122 B 104958367104 770375990 104958367488 759025059 A A D B 104958368128 740567898 104958368256 736944104 105092581504 1090432157 B 105092581632 1084863577 105092581760 1079330537 A D B 105092581888 1073832764 105092582016 1068369988 105092582144 1062941942 B 105092582272 1057548362 105092582400 1052188985 A A A D B 105092582528 1046863551 105092582656 1041571801 105092582784 1036313480 B 105092582912 1031088334 105092583040 1025896114 A D B 105092583296 1015609453 105092583424 1010514521 105092583552 1005451532 B 105092583680 1000420244 105092583808 995420420 A A D B 105092584192 980607380 105092584576 966069138 105092584704 961283064 B 105092585088 947101756 105092585344 937792801 A D B 105092585472 933181255 105092585600 928598048 105092586240 906099859 B 105092587136 875735766
noncomputable def AFe : CTN :=
  A A A A A A A D B 105226799488 1312335144 105226799616 1305650518 105226799744 1299008444 D B 105226799872 1292408599 105226800000 1285850659 105226800128 1279334306 A D B 105226800256 1272859223 105226800384 1266425096 105226800512 1260031615 B 105226800640 1253678471 105226800768 1247365360 A A D B 105226800896 1241091979 105226801024 1234858027 105226801152 1228663208 B 105226801280 1222507226 105226801408 1216389790 A D B 105226801536 1210310610 105226801664 1204269399 105226801920 1192299748 B 105226802048 1186370747 105226802304 1174623007 A A A D B 105226802432 1168803722 105226802688 1157272969 105226802816 1151560969 B 105226802944 1145884202 105226803200 1134635327 A D B 105226803712 1112549047 105226804864 1064788573 105226805248 1049440563 B 105361017344 1560333284 105361017472 1552395595 A A D B 105361017600 1544508370 105361017728 1536671226 105361017856 1528883780 B 105361017984 1521145654 105361018112 1513456474 A D B 105361018240 1505815868 105361018368 1498223468 105361018496 1490678909 B 105361018624 1483181829 105361018752 1475731870 A A A A D B 105361018880 1468328677 105361019008 1460971898 105361019136 1453661183 B 105361019264 1446396186 105361019392 1439176564 A D B 105361019648 1424872090 105361019776 1417786566 105361020160 1396792882 B 105361020544 1376186724 105361020672 1369402636 A A D B 105361022080 1297469403 105361022464 1278676770 105495235328 1819253821 B 105495235584 1800849844 105495235712 1791735219 A D B 105495235840 1782678246 105495235968 1773678488 105495236096 1764735511 B 105495236224 1755848885 105495236352 1747018185 A A A D B 105495236480 1738242987 105495236608 1729522875 105495236736 1720857432 B 105495236864 1712246247 105495236992 1703688913 A D B 105495237376 1678335996 105495237760 1653453401 105495238656 1597164902 B 105629453440 2084626309 105629453568 2074088812 A A D B 105629453696 2063617883 105629453824 2053213016 105629453952 2042873713 B 105629454080 2032599477 105629454208 2022389817 A D B 105629454336 2012244247 105629454464 2002162282 105629454592 1992143446 B 105629454848 1972293265 105629455104 1952689959 A A A A A D B 105629455232 1942979732 105629455360 1933329849 105629455488 1923739861 D B 105629455616 1914209321 105629455872 1895324820 105629456000 1885969988 A D B 105629456128 1876672858 105629456256 1867433004 105629456384 1858250002 B 105629456512 1849123433 105629456896 1822078178 A A D B 105629457024 1813173215 105629457280 1795526053 105629457664 1769456296 B 105629457920 1752339251 105629458432 1718722202 A D B 105763671296 2387672593 105763671424 2375618552 105763671552 2363640563 B 105763671680 2351738049 105763671808 2339910440 A A A D B 105763671936 2328157170 105763672064 2316477679 105763672192 2304871412 B 105763672320 2293337816 105763672960 2236740986 A D B 105763673216 2214592217 105763673984 2149772264 105763675648 2017277360 B 105763676160 1978577712 105897889024 2723399975 A A D B 105897889152 2709651032 105897889280 2695988834 105897889408 2682412724 B 105897889536 2668922051 105897889664 2655516170 A D B 105897889792 2642194442 105897889920 2628956233 105897890048 2615800915 B 105897890176 2602727864 105897890304 2589736465 A A A A D B 105897890432 2576826105 105897890560 2563996177 105897890688 2551246081 B 105897890816 2538575220 105897890944 2525983004 A D B 105897891072 2513468848 105897891200 2501032169 105897891456 2476388951 B 105897891584 2464181276 105897891840 2439990988 A A D B 105897891968 2428007268 105897892224 2404259947 105897892352 2392495267 B 105897892608 2369181205 105897893120 2323399657 A D B 105897893632 2278719671 105897893888 2256782822 106032107008 3050214574 B 106032107136 3034854700 106032107264 3019591488 A A A D B 106032107392 3004424210 106032107520 2989352141 106032107648 2974374565 B 106032107776 2959490771 106032107904 2944700053 A D B 106032108032 2930001715 106032108160 2915395064 106032108288 2900879413 B 106032108416 2886454083 106032108672 2857871693 A A D B 106032108800 2843713302 106032109184 2801761481 106032109440 2774223287 B 106032109696 2747022933 106032109824 2733547891 A D B 106032110080 2706845013 106032110848 2628670937 106032111616 2553301322 B 106166324736 3426260545 106166324864 3409007027 A A A A A A D B 106166324992 3391862090 106166325120 3374824912 106166325248 3357894682 D B 106166325376 3341070594 106166325504 3324351850 106166325632 3307737658 A D B 106166325760 3291227234 106166326144 3242310828 106166326272 3226207768 B 106166326400 3210204655 106166327040 3131662481 A A D B 106166327296 3100919687 106166327808 3040558638 106166328448 2967159653 B 106166329344 2868085299 106300542720 3785663322 A D B 106300542848 3766648098 106300542976 3747752238 106300543104 3728974843 B 106300543232 3710315023 106300543360 3691771894 A A A D B 106300543488 3673344580 106300543744 3636833936 106300543872 3618748892 B 106300544000 3600776238 106300544128 3582915136 A D B 106300544256 3565164754 106300544640 3512569736 106300545024 3460941988 B 106300545152 3443943991 106300545536 3393572914 A A D B 106300545792 3360503687 106300547072 3201075113 106434760576 4179809768 B 106434760704 4158841231 106434760832 4138004154 A D B 106434760960 4117297548 106434761216 4076271836 106434761344 4055950796 B 106434761472 4035756358 106434761600 4015687576 A A A A D B 106434761856 3975923233 106434761984 3956225821 106434762240 3917195948 B 106434762368 3897861683 106434762624 3859550045 A D B 106434763264 3765812161 106434763648 3710935089 106434764800 3552199377 B 106568978432 4591064320 106568978560 4568061672 A A D B 106568978688 4545203054 106568978816 4522487385 106568978944 4499913592 B 106568979200 4455187392 106568979456 4411016060 A D B 106568979584 4389135886 106568979712 4367391348 106568979968 4324305150 B 106568980096 4302961499 106568980224 4281749501 A A A D B 106568980352 4260668180 106568980608 4218893720 106568980992 4157188238 B 106568981120 4136870992 106568981376 4096607861 A D B 106568981632 4056833852 106568981760 4037128038 106568982016 3998074401 B 106568982272 3959492311 106568982528 3921374948 A A D B 106703196800 4919513303 106703196928 4895019217 106703197056 4870677540 B 106703197184 4846487135 106703197312 4822446873 A D B 106703197440 4798555637 106703197824 4727765046 106703197952 4704458924 B 106703198080 4681296382 106703198208 4658276357 A A A A A D B 106703198336 4635397799 106703199616 4414167757 106703200256 4308506924 B 106837414272 5436025178 106837414400 5408891503 A D B 106837414656 5355130656 106837415040 5275736814 106837415296 5223624809 B 106837415424 5197810335 106837415552 5172155289 A A D B 106837415680 5146658489 106837415936 5096134953 106837416064 5071105905 B 106837416320 5021507545 106837416576 4972514672 A D B 106837416704 4948242519 106837416832 4924118429 106837417600 4782423161 B 106837417984 4713488648 106971632512 5806369308 A A A D B 106971632640 5777531754 106971632768 5748873187 106971632896 5720392275 B 106971633152 5663958139 106971633280 5636002308 A D B 106971633536 5580606683 106971633792 5525890656 106971634048 5471844237 B 106971634176 5445069055 106971634944 5287814671 A A D B 106971635712 5136201722 107105850496 6241710349 107105850624 6210787836 B 107105850752 6180056772 107105850880 6149515737 A D B 107105851008 6119163319 107105851136 6088998122 107105851392 6029223859 B 107105851520 5999612058 107105851904 5911861814 A A A A D B 107105853184 5630722032 107105853440 5576516022 107240068224 6754089566 B 107240069120 6524160155 107240069888 6334825702 A D B 107374286592 7107580749 107374286720 7072586365 107374287360 6900812643 B 107374287744 6800250964 107374288000 6734227255 A A D B 107374288128 6701516173 107374288384 6636688260 107374288512 6604568550 B 107374288640 6572643104 107374288896 6509369379 A D B 107508504704 7532807730 107508505088 7422632987 107642723072 7884846377 B 107642723968 7620619198 107642724352 7510774532 A A A D B 107776940032 8689166398 107776941312 8273967539 107776941696 8154272015 B 107776941824 8114855547 107776942080 8036735203 A D B 107911159808 8579272269 108179595264 9713220361 108313812352 10556872873 B 108313812992 10304175640 108582248448 11532825879 A A D B 109119119360 14169550279 109387554816 15572935848 109521772544 16294777226 B 109790208000 17777062538 109924425728 18536799524 A D B 110058643456 19308445686 110192861184 20091624210 111669256320 29210021225 B 111669256576 28929837604
noncomputable def AFf : CTN :=
  A A A A A A A D B 111669256960 28515836841 111669257088 28379485819 111669257216 28243949556 D B 111669257472 27975297990 111669257600 27842171151 111669257728 27709835999 A D B 111669257856 27578286886 111669257984 27447518209 111669258240 27188299995 B 111669258368 27059839487 111669258624 26805188577 A A D B 111669258752 26678987475 111669259136 26304818298 111669259264 26181555955 B 111669259520 25937191605 111669259648 25816079498 A D B 111669259904 25575970478 111669260032 25456963711 111669260288 25221021330 B 111669260416 25104076101 111669260544 24987808501 A A A D B 111669260800 24757287385 111669261184 24416471402 111669261568 24081505030 B 111669261952 23752268098 111669262080 23643775309 A D B 111669262848 23005676080 111669263232 22694705692 111669263360 22592218816 B 111669263616 22388976217 111669264256 21890787541 A A D B 111669264384 21792819594 112743005312 28046118234 112743006208 27176325579 B 113145659392 29235007733 113414094848 30611303246 A D B 116232667136 44423594319 119319674880 55274538443 119722328064 56157426798 B 120259199104 56844414277 120259199488 55960566098 A A A A D B 120259199872 54943403955 120259200000 54575929090 120259201536 49177312645 B 120259202432 45325013956 120259204352 35969075978 A D B 120259205120 32016833781 120259206528 24808899974 120259207168 21644686635 B 123748868096 24017847370 124554174464 24570887349 A A D B 125627916288 25306100736 125896351744 25489126375 126164787200 25671723688 B 126299004928 25762843408 127506964480 26576239224 A D B 127909617664 26844133108 128043835392 26933009019 128178053120 27021662065 B 128849141888 26708226219 128849142144 25220043614 A A A D B 128849144064 15052086325 128849144320 13857021829 128849145216 10025994745 B 128849145856 7646646621 128849145984 7208155569 A D B 128849146240 6369338828 128849146624 5207672845 128849146752 4846449863 B 128849146880 4498307474 128849147520 2954823681 A A D B 128849147648 2685668456 128849147776 2429690184 128849148288 1537105649 B 128849148672 1004487465 128849149184 473701470 A D B 128849149952 50445805 129117579136 17038558153 129117580672 10101842536 B 129520234368 8256895998 129520235904 3617728800 A A A A A D B 129520236032 3316970439 129520237568 742342444 129788673280 504500376 D B 129922890112 1612109866 129922891776 60287294 130191323904 5431283312 A D B 130191325440 1841961107 130191325824 1246550688 130191325952 1074565995 B 130191327232 62703137 130459760000 3732371154 A A D B 130459762432 168608237 130728192640 13923308555 130728193408 10541815373 B 131130846848 9609015681 131130848640 3810691495 A D B 131130850304 806489322 131265065728 5600117225 131265066112 4494637522 B 131265066496 3512197228 131265068032 811492537 A A A D B 131265069056 72014168 131399282432 9169745826 131399283456 5620512261 B 131399284352 3225395148 131533499776 10750680656 A D B 131533502080 3238517398 131533503488 821321555 131533504512 74225795 B 131667721728 347588353 131801936512 6080876184 A A D B 131801937280 3885705532 131801938176 1952963859 131801939328 450774976 B 131801939968 76380134 131936155264 3277114027 A D B 131936156160 1531861424 131936156416 1156702295 131936157056 453893875 B 131936157696 77434193 132070372864 3595269726 A A A A D B 132070373120 2998061195 132070374016 1343941861 132070375168 191517457 B 132204590592 3608632501 132204590720 3302183244 A D B 132204591744 1350310040 132204593152 79492915 132473025536 5007577032 B 132473026944 1770543270 132473027072 1559782648 A A D B 132473027584 853732521 132473027968 465895276 132607243136 5403333754 B 132607243264 5024304284 132607244544 2003237293 A D B 132741460864 5420902248 132875679232 3673256932 132875679616 2782987419 B 132875679872 2259746259 132875680000 2019134457 A A A D B 132875680256 1579729544 132875680768 866605215 132875681280 370297006 B 132875681792 84323140 133009897216 3076463958 A D B 133009897472 2523579717 133009897856 1799579749 133009898112 1386666425 B 133009898496 870752307 133009898624 726068132 A A D B 133009899008 372599597 133009899264 203040122 133009899520 85230236 B 133144114560 4024720930 133144116480 597988807 A D B 133278332672 3097620509 133278333056 2284848711 133278333440 1598783991 B 133278333568 1398048695 133278334208 601035112 A A A A A A D B 133278334464 377062630 133278334848 140077613 133278334976 86981035 D B 133412550912 2049566957 133412551168 1604931164 133412552704 87823684 A D B 133546768768 1826901260 133546770176 208892132 133546770432 88643818 B 133680985984 2840904146 133680986368 2064080127 A A D B 133680987136 890362949 133680988160 89440943 133815204096 2071156309 B 133815204608 1230553215 133815204864 894053282 A D B 133815205120 612590679 133815205248 492263255 133815205504 291885065 B 133815205632 211601557 133815205888 90214579 A A A D B 133949421696 2324195061 133949421824 2078110533 133949422208 1424802205 B 133949422464 1059475703 133949422720 749642439 A D B 133949423104 387356150 133949423616 90964259 134083639040 3157574027 B 134083639808 1634080396 134083640576 617979164 A A D B 134083640704 496860385 134083640960 295067759 134083641088 214160295 B 134083641344 91689533 134217857280 2091648218 A D B 134217857664 1434799465 134217857792 1244096045 134217858304 620573348 B 134217858432 499069489 134217859072 92389963 A A A A D B 134352074880 2346248909 134352075392 1439643031 134352076288 392911832 B 134486293120 1444381910 134486293632 761521358 A D B 134486293888 503305367 134486294400 149156825 134486294528 93714619 B 134620510976 1256770849 134620511104 1078624312 A A D B 134620511232 914496760 134620511360 764302075 134620511488 627946919 B 134620511616 505330842 134620512000 218808388 A D B 134620512128 150006047 134620512256 94338048 134754728576 1453541834 B 134754728704 1260798641 134754728832 1082182067 A A A D B 134754729088 767005716 134754729216 630266148 134754729344 507293842 B 134754729856 150821679 134754729984 94935037 A D B 134888946176 1665422750 134888946304 1457961065 134888946432 1264726435 B 134888946688 920644452 134888946816 769631586 A A D B 134888946944 632514968 134888947200 399560138 134888947712 95505228 B 135023164160 1268553414 135023164288 1089019110 A D B 135023164416 923589843 135023164544 772179014 135023164672 634692757 B 135023164800 511030051 135023165056 304736143 A A A A A D B 135023165184 221868200 135023165312 152350569 135023165440 96048277 B 135157382144 926448665 135157382272 774647354 A D B 135157382400 636798914 135157382528 512802130 135157382784 305923547 B 135157382912 222804551 135157383040 153063066 A A D B 135157383168 96563856 135291599616 1275901803 135291599744 1095479880 B 135291599872 929220249 135291600000 777035984 A D B 135291600256 514509477 135291600384 403957358 135291600512 307061088 B 135291600768 153740452 135291600896 97051656 A A A D B 135425817472 1098567395 135425817728 779344307 135425817856 640794050 B 135425817984 516151583 135425818112 405308227 A D B 135425818368 224549458 135425818496 154382392 135425818624 97511382 B 135560035072 1282837840 135560035200 1101558775 A A D B 135560035328 934499164 135560035456 781571749 135560035584 642681946 B 135560035712 517727960 135560035840 406600902 A D B 135560035968 309184911 135560036096 225357276 135560036224 154988567 B 135560036352 97942758 135694253184 783717765 A A A A D B 135694253440 519238146 135694253568 407834962 135694253696 310170411 B 135694253824 226121543 135694254080 98345523 A D B 135828470784 939421769 135828470912 785781832 135828471040 646235871 B 135828471168 520681700 135828471296 409010007 A A D B 135828471424 311104482 135828471552 226841938 135828471680 156092440 B 135828471808 98719435 135962688512 941748065 A D B 135962688640 787763454 135962688768 647900962 135962688896 522058204 B 135962689024 410125657 135962689152 311986785 A A A D B 135962689280 227518160 135962689408 156589595 135962689536 99064269 B 136096906368 789662160 136096906496 649490887 A D B 136096906624 523367265 136096906752 411181557 136096906880 312817000 B 136096907008 228149927 136096907136 157049895 A A D B 136096907264 99379817 136231124096 791477508 136231124224 651005240 B 136231124352 524608512 136231124480 412177373 A D B 136231124608 313594832 136231124736 228736979 136231124864 157473116 B 136231124992 99665889
noncomputable def AFg : CTN :=
  A A A A A A A D B 136365342080 525781599 136365342208 413112794 136365342336 314320003 D B 136365342464 229279073 136365342592 157859052 136365342720 99922313 A D B 136499559808 526886202 136499559936 413987531 136499560064 314992258 B 136499560192 229775989 136499560320 158207513 A A D B 136499560448 100148933 136633777664 414801318 136633777792 315611365 B 136633777920 230227527 136633778048 158518332 A D B 136633778176 100345615 136767995520 316177113 136767995648 230633505 B 136767995776 158791360 136767995904 100512239 A A A D B 136902213376 230993764 136902213504 159026466 136902213632 100648704 B 137036431232 159223541 137036431360 100754930 A D B 137170648960 159382492 137170649088 100830851 137304866816 100876421 B 137439084672 55697681 137439084800 23869645 A A D B 137439084928 5347966 137573302656 5347966 137975956480 64424 B 137975956608 64174 137975956736 63925 A D B 137975956864 63678 137975956992 63431 137975957120 63186 B 137975957248 62942 137975957376 62700 A A A A D B 137975957504 62458 137975957632 62218 137975957760 61978 B 137975957888 61740 137975958016 61503 A D B 137975958144 61268 137975958272 61033 137975958400 60799 B 137975958528 60567 137975958656 60336 A A D B 137975958784 60105 137975958912 59876 137975959040 59648 B 137975959168 59421 137975959296 59195 A D B 137975959424 58971 137975959552 58747 137975959680 58524 B 137975959808 58303 137975959936 58082 A A A D B 137975960064 57863 137975960192 57644 137975960320 57427 B 137975960448 57210 137975960576 56995 A D B 137975960704 56780 137975961088 56143 137975961344 55723 B 137975961472 55515 137975961600 55308 A A D B 137975961856 54896 137975962112 54487 137975962240 54285 B 137975962368 54083 137975963392 52503 A D B 137975963520 52309 137975963648 52116 138110174336 7824475 B 138110174464 7794156 138110174592 7763984 A A A A A D B 138110174720 7733958 138110174848 7704077 138110174976 7674340 D B 138110175104 7644747 138110175232 7615296 138110175360 7585987 A D B 138110175488 7556819 138110175616 7527791 138110175744 7498902 B 138110175872 7470152 138110176000 7441540 A A D B 138110176128 7413064 138110176256 7384725 138110176384 7356521 B 138110176512 7328452 138110176640 7300517 A D B 138110176768 7272714 138110176896 7245044 138110177024 7217506 B 138110177152 7190098 138110177280 7162820 A A A D B 138110177408 7135672 138110177536 7108652 138110177664 7081760 B 138110177792 7054995 138110177920 7028357 A D B 138110178048 7001844 138110178176 6975456 138110178304 6949193 B 138110178560 6897036 138110178688 6871141 A A D B 138110178816 6845367 138110179072 6794182 138110179200 6768769 B 138110179584 6693240 138110179712 6668298 A D B 138110179840 6643472 138110180352 6545317 138110180480 6521062 B 138110180608 6496920 138110181248 6377871 A A A A D B 138110181376 6354389 138244392192 28464882 138244392320 28354691 B 138244392448 28245033 138244392576 28135904 A D B 138244392704 28027303 138244392832 27919226 138244392960 27811669 B 138244393088 27704630 138244393216 27598106 A A D B 138244393344 27492093 138244393472 27386590 138244393600 27281592 B 138244393728 27177098 138244393856 27073103 A D B 138244393984 26969606 138244394112 26866603 138244394240 26764092 B 138244394368 26662069 138244394496 26560533 A A A D B 138244394624 26459480 138244394752 26358907 138244394880 26258811 B 138244395008 26159191 138244395136 26060043 A D B 138244395264 25961364 138244395392 25863153 138244395520 25765406 B 138244395648 25668120 138244395776 25571293 A A D B 138244395904 25474923 138244396160 25283541 138244396288 25188525 B 138244396416 25093954 138244396928 24720085 A D B 138244397312 24444246 138244398080 23904021 138244398720 23465199 B 138244399104 23206737 138378610048 61897828 A A A A A A D B 138378610176 61658446 138378610304 61420221 138378610432 61183146 D B 138378610560 60947215 138378610688 60712420 138378610816 60478756 A D B 138378610944 60246216 138378611072 60014792 138378611200 59784480 B 138378611328 59555272 138378611456 59327162 A A D B 138378611584 59100144 138378611712 58874211 138378611840 58649357 B 138378611968 58425577 138378612096 58202864 A D B 138378612224 57981211 138378612352 57760613 138378612480 57541064 B 138378612608 57322558 138378612864 56888649 A A A D B 138378612992 56673236 138378613248 56245461 138378613376 56033088 B 138378613504 55821716 138378613760 55401957 A D B 138378614272 54574216 138378614528 54166146 138378614656 53963542 B 138378614784 53761885 138378615552 52571534 A A D B 138378616704 50847134 138378616832 50659929 138512827776 108447647 B 138512827904 108028240 138512828032 107610860 A D B 138512828160 107195495 138512828288 106782133 138512828416 106370763 B 138512828544 105961373 138512828672 105553952 A A A A D B 138512828800 105148488 138512828928 104744971 138512829056 104343389 B 138512829184 103943730 138512829312 103545985 A D B 138512829440 103150141 138512829568 102756188 138512829696 102364115 B 138512829824 101973911 138512829952 101585567 A A D B 138512830080 101199070 138512830208 100814410 138512830336 100431578 B 138512830464 100050562 138512830592 99671352 A D B 138512830720 99293938 138512830848 98918310 138512830976 98544458 B 138512831232 97802040 138512831360 97433454 A A A D B 138512831488 97066604 138512831616 96701480 138512831872 95976371 B 138512832000 95616366 138512832256 94901410 A D B 138512832384 94546439 138512832512 94193128 138512832768 93491444 B 138512832896 93143054 138512833024 92796286 A A D B 138512833152 92451132 138512833280 92107581 138512833664 91086466 B 138512833920 90413581 138512834048 90079470 A D B 138512834304 89415867 138512834560 88758367 138647045632 167400643 B 138647045760 166753871 138647045888 166110220 A A A A A D B 138647046016 165469675 138647046144 164832215 138647046272 164197824 B 138647046400 163566485 138647046528 162938178 A D B 138647046656 162312887 138647046784 161690595 138647046912 161071284 B 138647047040 160454937 138647047168 159841537 A A D B 138647047296 159231067 138647047424 158623511 138647047552 158018851 B 138647047680 157417072 138647047808 156818156 A D B 138647047936 156222087 138647048064 155628850 138647048192 155038427 B 138647048320 154450803 138647048448 153865963 A A A D B 138647048576 153283889 138647048704 152704567 138647048832 152127981 B 138647048960 151554116 138647049088 150982955 A D B 138647049472 149285550 138647049600 148725058 138647049728 148167195 B 138647049856 147611946 138647049984 147059298 A A D B 138647050112 146509235 138647050368 145416807 138647050496 144874414 B 138647050752 143797197 138647050880 143262345 A D B 138647051136 142200085 138647051264 141672649 138647051648 140104954 B 138647051776 139587215 138647052032 138558896 A A A A D B 138647052160 138048289 138647052288 137540034 138781263488 238887464 B 138781263616 237965386 138781263744 237047756 A D B 138781263872 236134548 138781264000 235225735 138781264128 234321293 B 138781264256 233421197 138781264384 232525421 A A D B 138781264512 231633940 138781264640 230746731 138781264768 229863767 B 138781264896 228985026 138781265024 228110482 A D B 138781265152 227240112 138781265280 226373891 138781265408 225511797 B 138781265536 224653805 138781265664 223799892 A A A D B 138781265792 222950034 138781265920 222104209 138781266048 221262394 B 138781266176 220424566 138781266304 219590702 A D B 138781266432 218760780 138781266560 217934777 138781266688 217112671 B 138781266816 216294440 138781266944 215480063 A A D B 138781267072 214669517 138781267200 213862781 138781267328 213059833 B 138781267456 212260652 138781267840 209885500 A D B 138781268096 208320515 138781268224 207543496 138781268992 202956727 B 138781269888 197764559
noncomputable def AFh : CTN :=
  A A A A A A A D B 138915481472 321546460 138915481600 320307727 138915481728 319074957 D B 138915481856 317848115 138915481984 316627168 138915482112 315412081 A D B 138915482240 314202821 138915482368 312999354 138915482496 311801647 B 138915482624 310609667 138915482752 309423381 A A D B 138915482880 308242756 138915483008 307067760 138915483136 305898361 B 138915483264 304734526 138915483392 303576225 A D B 138915483520 302423425 138915483648 301276095 138915483776 300134204 B 138915483904 298997722 138915484032 297866616 A A A D B 138915484160 296740857 138915484288 295620415 138915484416 294505259 B 138915484544 293395360 138915484672 292290687 A D B 138915484800 291191212 138915485056 289007735 138915485184 287923676 B 138915485312 286844698 138915485440 285770772 A A D B 138915485568 284701870 138915485952 281525029 138915486080 280475944 B 138915486208 279431743 138915486336 278392400 A D B 138915486464 277357888 138915486848 274283066 138915486976 273267608 B 138915487104 272256848 138915487232 271250759 A A A A D B 138915487488 269252494 138915487616 268260265 138915487744 267272605 B 139049699072 420609924 139049699200 418987989 A D B 139049699328 417373870 139049699456 415767520 139049699584 414168896 B 139049699712 412577953 139049699840 410994646 A A D B 139049699968 409418931 139049700096 407850765 139049700224 406290105 B 139049700352 404736907 139049700480 403191128 A D B 139049700608 401652726 139049700736 400121659 139049700864 398597885 B 139049700992 397081362 139049701120 395572049 A A A D B 139049701248 394069904 139049701376 392574887 139049701504 391086957 B 139049701760 388132198 139049701888 386665289 A D B 139049702016 385205308 139049702144 383752215 139049702272 382305971 B 139049702400 380866538 139049702656 378007950 A A D B 139049702784 376588719 139049702912 375176147 139049703040 373770195 B 139049703168 372370826 139049703680 366838452 A D B 139049703936 364110816 139049704192 361408500 139049704448 358731220 B 139049704704 356078700 139049705088 352145745 A A A A A D B 139049705344 349553930 139049705472 348266970 139183916928 529386621 D B 139183917056 527347199 139183917184 525317595 139183917312 523297751 A D B 139183917440 521287612 139183917568 519287121 139183917696 517296223 B 139183917824 515314863 139183917952 513342986 A A D B 139183918080 511380538 139183918208 509427464 139183918336 507483711 B 139183918464 505549225 139183918592 503623953 A D B 139183918720 501707843 139183918848 499800843 139183918976 497902900 B 139183919104 496013963 139183919232 494133980 A A A D B 139183919360 492262901 139183919488 490400675 139183919616 488547252 B 139183919744 486702582 139183919872 484866616 A D B 139183920000 483039303 139183920128 481220596 139183920256 479410445 B 139183920384 477608802 139183920512 475815620 A A D B 139183920640 474030850 139183920896 470486359 139183921024 468726544 B 139183921152 466974955 139183921408 463496266 A D B 139183921536 461769076 139183921664 460049929 139183921792 458338779 B 139183921920 456635582 139183922304 451573266 A A A A D B 139183922688 446580948 139183923200 440031407 139318134784 650234006 B 139318134912 647731446 139318135040 645240922 A D B 139318135168 642762364 139318135296 640295702 139318135424 637840869 B 139318135552 635397796 139318135680 632966416 A A D B 139318135808 630546662 139318135936 628138466 139318136064 625741763 B 139318136192 623356488 139318136320 620982573 A D B 139318136448 618619956 139318136576 616268570 139318136704 613928353 B 139318136832 611599240 139318136960 609281168 A A A D B 139318137088 606974075 139318137216 604677898 139318137344 602392575 B 139318137472 600118045 139318137600 597854246 A D B 139318137728 595601118 139318137856 593358600 139318137984 591126633 B 139318138240 586694112 139318138368 584493440 A A D B 139318138496 582303083 139318138624 580122983 139318138752 577953081 B 139318138880 575793322 139318139136 571504001 A D B 139318139264 569374327 139318139392 567254570 139318139648 563044583 B 139318140032 556802605 139318140544 548613977 A A A A A A D B 139318140800 544576144 139318140928 542571166 139452352640 783007408 D B 139452352768 779996749 139452352896 777000554 139452353024 774018741 A D B 139452353152 771051226 139452353280 768097928 139452353408 765158764 B 139452353536 762233654 139452353664 759322518 A A D B 139452353792 756425274 139452353920 753541843 139452354048 750672147 B 139452354176 747816106 139452354304 744973644 A D B 139452354432 742144682 139452354560 739329144 139452354688 736526953 B 139452354816 733738033 139452354944 730962309 A A A D B 139452355072 728199706 139452355328 722713566 139452355456 719989882 B 139452355584 717279024 139452355712 714580920 A D B 139452355840 711895497 139452355968 709222686 139452356096 706562413 B 139452356224 703914609 139452356352 701279204 A A D B 139452356608 696045312 139452356736 693446687 139452356992 688285737 B 139452357120 685723278 139452357248 683172738 A D B 139452357376 680634054 139452357504 678107157 139452357632 675591982 B 139452357760 673088464 139452358016 668116142 A A A A D B 139452358144 665647209 139452358656 655884850 139586570496 927555637 B 139586570624 923992626 139586570752 920446716 A D B 139586570880 916917811 139586571008 913405811 139586571136 909910620 B 139586571264 906432141 139586571392 902970279 A A D B 139586571520 899524937 139586571648 896096023 139586571776 892683441 B 139586571904 889287098 139586572032 885906902 A D B 139586572160 882542760 139586572288 879194582 139586572416 875862275 B 139586572544 872545751 139586572672 869244919 A A A D B 139586572800 865959690 139586572928 862689976 139586573056 859435688 B 139586573184 856196740 139586573312 852973045 A D B 139586573440 849764517 139586573568 846571069 139586573696 843392618 B 139586573824 840229078 139586573952 837080366 A A D B 139586574208 830827091 139586574336 827722364 139586574464 824632134 B 139586574592 821556320 139586574720 818494842 A D B 139586575360 803399697 139586575488 800422567 139586575872 791573583 B 139586576128 785742172 139586576256 782846616 A A A A A D B 139586576384 779964392 139720788352 1083721097 139720788480 1079562214 D B 139720788608 1075423275 139720788736 1071304164 139720788864 1067204767 A D B 139720788992 1063124972 139720789120 1059064665 139720789248 1055023736 B 139720789376 1051002072 139720789504 1046999565 A A D B 139720789632 1043016104 139720789760 1039051582 139720789888 1035105889 B 139720790016 1031178918 139720790144 1027270564 A D B 139720790272 1023380719 139720790400 1019509280 139720790528 1015656141 B 139720790656 1011821199 139720790784 1008004350 A A A D B 139720790912 1004205493 139720791040 1000424525 139720791168 996661346 B 139720791424 989187952 139720791552 985477538 A D B 139720791680 981784515 139720791808 978108786 139720792064 970808817 B 139720792320 963576864 139720792448 959986155 A A D B 139720792576 956412165 139720792704 952854802 139720793088 942281546 B 139720793216 938789767 139720793344 935314156 A D B 139720793472 931854623 139720793600 928411079 139720794112 914795035 B 139855006208 1251339906 139855006336 1246542387 A A A A D B 139855006464 1241767851 139855006592 1237016167 139855006720 1232287203 B 139855006848 1227580829 139855006976 1222896915 A D B 139855007104 1218235333 139855007232 1213595956 139855007360 1208978655 B 139855007488 1204383306 139855007616 1199809782 A A D B 139855007744 1195257960 139855007872 1190727717 139855008000 1186218928 B 139855008128 1181731474 139855008256 1177265231 A D B 139855008384 1172820081 139855008512 1168395904 139855008640 1163992580 B 139855008768 1159609993 139855008896 1155248024 A A A D B 139855009024 1150906558 139855009280 1142284672 139855009408 1138004023 B 139855009536 1133743419 139855009664 1129502747 A D B 139855009792 1125281895 139855009920 1121080752 139855010048 1116899208 B 139855010176 1112737153 139855010304 1108594478 A A D B 139855010560 1100366836 139855010688 1096281654 139855010816 1092215424 B 139855010944 1088168040 139855011200 1080129390 A D B 139855011328 1076137917 139855011584 1068210162 139855011712 1064273676 B 139855011840 1060355316
noncomputable def AFi : CTN :=
  A A A A A A A D B 139989224192 1424763872 139989224320 1419311945 139989224448 1413886087 D B 139989224576 1408486147 139989224704 1403111977 139989224832 1397763430 A D B 139989224960 1392440360 139989225088 1387142620 139989225216 1381870066 B 139989225344 1376622554 139989225472 1371399943 A A D B 139989225600 1366202089 139989225728 1361028853 139989225856 1355880094 B 139989225984 1350755673 139989226112 1345655453 A D B 139989226240 1340579296 139989226368 1335527067 139989226496 1330498629 B 139989226624 1325493849 139989226752 1320512592 A A A D B 139989226880 1315554727 139989227008 1310620122 139989227136 1305708645 B 139989227264 1300820167 139989227392 1295954558 A D B 139989227520 1291111691 139989227776 1281493669 139989227904 1276718263 B 139989228032 1271965093 139989228160 1267234035 A A D B 139989228288 1262524966 139989228544 1253172302 139989228672 1248528466 B 139989228800 1243906132 139989229312 1225629448 A D B 139989229568 1216617055 140123441920 1620251351 140123442048 1614051381 B 140123442176 1607881057 140123442304 1601740208 A A A A D B 140123442432 1595628665 140123442560 1589546261 140123442688 1583492828 B 140123442816 1577468201 140123442944 1571472217 A D B 140123443072 1565504710 140123443200 1559565520 140123443328 1553654485 B 140123443456 1547771445 140123443584 1541916240 A A D B 140123443712 1536088714 140123443840 1530288708 140123443968 1524516067 B 140123444096 1518770637 140123444224 1513052263 A D B 140123444352 1507360792 140123444608 1496057954 140123444736 1490446287 B 140123444992 1479301710 140123445120 1473768506 A A A D B 140123445248 1468261163 140123445504 1457323483 140123445632 1451892858 B 140123446784 1404138392 140123447168 1388658000 A D B 140123447296 1383545347 140257659776 1821185907 140257659904 1814223733 B 140257660032 1807294816 140257660160 1800398966 A A D B 140257660288 1793535994 140257660416 1786705712 140257660544 1779907933 B 140257660672 1773142471 140257660800 1766409142 A D B 140257660928 1759707763 140257661056 1753038153 140257661184 1746400130 B 140257661312 1739793515 140257661440 1733218130 A A A A A D B 140257661568 1726673798 140257661696 1720160343 140257661824 1713677589 D B 140257661952 1707225364 140257662080 1700803495 140257662208 1694411811 A D B 140257662336 1688050141 140257662464 1681718317 140257662592 1675416170 B 140257662848 1662900242 140257662976 1656686131 A A D B 140257663232 1644344796 140257663360 1638217248 140257663616 1626047589 B 140257663744 1620005160 140257664128 1602045592 A D B 140257664640 1578485078 140257664768 1572662787 140257664896 1566867331 B 140257665024 1561098561 140391877760 2025093984 A A A D B 140391877888 2017367108 140391878016 2009677071 140391878144 2002023664 B 140391878272 1994406676 140391878400 1986825901 A D B 140391878528 1979281131 140391878656 1971772162 140391878784 1964298789 B 140391878912 1956860810 140391879040 1949458024 A A D B 140391879168 1942090232 140391879296 1934757235 140391879424 1927458836 B 140391879552 1920194838 140391879680 1912965048 A D B 140391879808 1905769273 140391879936 1898607319 140391880064 1891478997 B 140391880192 1884384118 140391880320 1877322492 A A A A D B 140391880448 1870293933 140391880960 1842506671 140391881216 1828806669 B 140391881344 1822004446 140391881600 1808494667 A D B 140391881856 1795109942 140391882240 1775264301 140391882624 1755692307 B 140391882752 1749228337 140526095616 2246469566 A A D B 140526095744 2237906210 140526095872 2229383643 140526096000 2220901632 B 140526096128 2212459945 140526096256 2204058353 A D B 140526096384 2195696626 140526096512 2187374539 140526096640 2179091866 B 140526096768 2170848383 140526096896 2162643867 A A A D B 140526097024 2154478097 140526097152 2146350854 140526097280 2138261920 B 140526097408 2130211079 140526097536 2122198114 A D B 140526097664 2114222813 140526097792 2106284963 140526097920 2098384352 B 140526098176 2082694015 140526098304 2074903872 A A D B 140526098560 2059432613 140526098688 2051751090 140526099072 2028920528 B 140526099200 2021381015 140526099456 2006406819 A D B 140526099840 1984204696 140526100352 1955077646 140526100480 1947879594 B 140660313728 2459322346 140660313856 2449974417 A A A A A A D B 140660313984 2440670888 140660314112 2431411505 140660314240 2422196016 D B 140660314368 2413024171 140660314496 2403895724 140660314624 2394810428 A D B 140660314752 2385768037 140660314880 2376768310 140660315008 2367811004 B 140660315136 2358895879 140660315264 2350022698 A A D B 140660315392 2341191223 140660315520 2332401220 140660315648 2323652454 B 140660315776 2314944695 140660315904 2306277710 A D B 140660316032 2297651272 140660316160 2289065152 140660316288 2280519125 B 140660316416 2272012966 140660316544 2263546451 A A A D B 140660316672 2255119360 140660316800 2246731472 140660316928 2238382569 B 140660317312 2213567596 140660317440 2205372470 A D B 140660317568 2197215256 140660317696 2189095743 140660317824 2181013722 B 140660318080 2164961326 140660318208 2156990541 A A D B 140794531584 2699291525 140794531840 2678839592 140794531968 2668686306 B 140794532096 2658581106 140794532224 2648523719 A D B 140794532352 2638513874 140794532480 2628551302 140794532608 2618635734 B 140794532736 2608766904 140794532864 2598944548 A A A A D B 140794532992 2589168404 140794533120 2579438211 140794533248 2569753709 B 140794533376 2560114642 140794533504 2550520753 A D B 140794533632 2540971789 140794533760 2531467497 140794534016 2512591929 B 140794534144 2503220156 140794534272 2493892063 A A D B 140794534400 2484607404 140794534784 2457011621 140794535040 2438827202 B 140794535168 2429798114 140794535296 2420810796 A D B 140794535808 2385274605 140794535936 2376492688 140928749568 2937896155 B 140928749696 2926760997 140928749824 2915678576 A A A D B 140928749952 2904648593 140928750080 2893670748 140928750208 2882744747 B 140928750336 2871870296 140928750464 2861047103 A D B 140928750592 2850274879 140928750720 2839553335 140928750848 2828882186 B 140928750976 2818261147 140928751104 2807689935 A A D B 140928751232 2797168272 140928751360 2786695877 140928751488 2776272475 B 140928751616 2765897790 140928751744 2755571550 A D B 140928751872 2745293482 140928752000 2735063317 140928752128 2724880788 B 140928752640 2684621731 140928752768 2674673422 A A A A A D B 140928752896 2664771179 140928753024 2654914744 140928753152 2645103864 B 140928753280 2635338285 140928753664 2606310863 A D B 141062967680 3172179149 141062967808 3160190198 141062968192 3124561776 B 141062968320 3112797384 141062968448 3101088340 A A D B 141062968576 3089434332 141062968704 3077835050 141062968832 3066290185 B 141062968960 3054799431 141062969088 3043362484 A D B 141062969216 3031979042 141062969344 3020648805 141062969600 2998146751 B 141062969728 2986974345 141062969856 2975853961 A A A D B 141062969984 2964785310 141062970112 2953768102 141062970496 2921022282 B 141062971264 2856881481 141062971392 2846363239 A D B 141197185792 3412072866 141197185920 3399213817 141197186048 3386415323 B 141197186176 3373677043 141197186304 3360998636 A A D B 141197186560 3335820096 141197186688 3323319293 141197186816 3310877028 B 141197186944 3298492970 141197187072 3286166793 A D B 141197187200 3273898173 141197187456 3249532315 141197187840 3213407211 B 141197188352 3166018133 141197188480 3154307690 A A A A D B 141197189120 3096561355 141331403648 3684898873 141331404288 3616177262 B 141331404416 3602625836 141331404544 3589137867 A D B 141331404672 3575712998 141331404928 3549051145 141331405056 3535813460 B 141331405184 3522637472 141331405312 3509522837 A A D B 141331405440 3496469211 141331406720 3369214663 141331406848 3356810152 B 141465621760 3936743876 141465622272 3878036344 A D B 141465622784 3820419725 141465622912 3806183170 141465623296 3763869769 B 141465623552 3735987384 141465623680 3722143067 A A A D B 141465623808 3708362854 141465623936 3694646391 141465624064 3680993322 B 141465624192 3667403297 141465624448 3640410984 A D B 141465624576 3627008003 141599840128 4161831392 141599840640 4100055911 B 141599840768 4084791571 141599841024 4054475523 A A D B 141599841152 4039423026 141599841408 4009527131 141599841536 3994682958 B 141599841664 3979907456 141599841792 3965200244 A D B 141599842048 3935989176 141599842304 3907046756 141734057600 4504139896 B 141734057856 4470492441
noncomputable def AD1 : CTN :=
  A A A A A A A D B 141734058368 4404135399 141734058496 4387738983 141734058624 4371418843 D B 141734059008 4322911840 141734059264 4290947491 141734059392 4275076168 A D B 141734059520 4259278199 141734060032 4196811774 141868275840 4753673612 B 141868276352 4683244265 141868276864 4614115163 A A D B 141868277760 4496181990 142002494592 4931064083 142002494720 4912808173 B 142002494976 4876549245 142002495360 4822786101 A D B 142002495488 4805029944 142136712832 5180281024 142136713088 5142153837 B 142136713216 5123221857 142270930560 5511323171 A A A D B 142270930944 5450617679 142405147776 5938863872 142405148544 5808456279 B 142405148672 5787071159 142539366400 6132429910 A D B 142673584128 6486535485 142807801856 6849223449 142942019584 7220323464 B 143076237312 7599659374 143210455040 7987049288 A A D B 143344672768 8382305677 143478890496 8785235472 143613108224 9195640158 B 144015761408 10469639000 144149979136 10907852980 A D B 144284196864 11352471411 144552632320 12260001552 144955285504 13663460618 B 145626374144 16098359934 145760591872 16597368179 A A A A D B 146029027456 17540496856 146029027584 17476036621 146029027712 17411872388 B 146029027840 17348002527 146029027968 17284425416 A D B 146029028096 17221139448 146029028224 17158143022 146029028352 17095434549 B 146029028480 17033012451 146029028608 16970875159 A A D B 146029028736 16909021113 146029028864 16847448766 146029028992 16786156578 B 146029029120 16725143020 146029029248 16664406573 A D B 146029029376 16603945726 146029029504 16543758980 146029029632 16483844845 B 146029029760 16424201838 146029029888 16364828489 A A A D B 146029030016 16305723334 146029030144 16246884921 146029030272 16188311805 B 146029030400 16130002552 146029030528 16071955735 A D B 146029030656 16014169939 146029030784 15956643754 146029030912 15899375782 B 146029031040 15842364632 146029031168 15785608923 A A D B 146029031296 15729107282 146029031424 15672858345 146029031552 15616860755 B 146029031680 15561113166 146029031808 15505614239 A D B 146029032064 15395357056 146029032192 15340596165 146029032320 15286078662 B 146029032448 15231803251 146029032704 15123973555 A A A A A D B 146029032832 15070416714 146029032960 15017096854 146029033088 14964012717 D B 146029033216 14911163054 146029033472 14806162186 146029033728 14702084403 A D B 146029033856 14650388624 146029033984 14598919978 146029034240 14496659306 B 146029034368 14445864907 146029034496 14395292897 A A D B 146029034624 14344942108 146029034752 14294811379 146029035008 14195205494 B 146029035136 14145728051 146029035392 14047418502 A D B 146029035520 13998584151 146431688704 15216997698 146700124160 16037511992 B 148444954624 21395201291 149250260992 23787364605 A A A D B 149518696448 24560117157 152068833280 30881782148 152203051008 31148097071 B 154618970240 34309130482 154618970624 33876836922 A D B 154618970880 33541516667 154618971008 33360104411 154618971392 32762527531 B 154618971648 32321172538 154618971776 32088070159 A A D B 154618971904 31846901215 154618972544 30526042292 154618972672 30240113596 B 154618972928 29647981632 154618973312 28711997456 A D B 154618973440 28388051375 154618973952 27037941846 154618974080 26687874192 B 154618974208 26333212918 154618974720 24872928246 A A A A D B 154618974976 24120840786 154618975616 22190687491 154618975872 21403283349 B 154618976256 20211247886 154618976640 19011352264 A D B 154618976768 18610653819 154618978304 13861447354 155692720128 14220509370 B 155826937856 14265634918 157034897408 14673315167 A A D B 158779726848 18662092948 158779727872 15263438651 158913945600 15308711174 B 159048163328 15353949102 159182381056 15399148975 A D B 159450816512 15489420729 159719251968 15579498773 159853469696 15624456513 B 160658776064 15892847778 161329864704 16114355173 A A A D B 161464082432 16158381002 161598300160 16202307066 161732517888 16246130011 B 162000953344 16333453182 162135171072 16376946761 A D B 162403606528 16463581401 162672041984 16549724183 163074695168 16677959410 B 163208913152 15826922482 163208913408 14945667049 A A D B 163208913664 14078312624 163208913792 13650348921 163208914688 10778946325 B 163208914944 10003856588 163208915072 9624698905 A D B 163208915456 8522614929 163208915584 8167535505 163208915712 7818828574 B 163208915968 7141055887 163208916352 6175341094 A A A A A A D B 163208916480 5867479175 163208916736 5273449099 163208916992 4708978403 D B 163208917120 4438047320 163208917248 4174759615 163208917888 2975394930 A D B 163208918272 2351479462 163208918400 2159724198 163208918656 1800722553 B 163208918784 1633520237 163208918912 1474538120 A A D B 163208919680 693479981 163208919808 592043860 163208919936 498772193 B 163208920064 413636898 163208920448 206700442 A D B 163208920832 71549112 163208920960 42206164 163208921088 20615427 B 163343134720 4724192192 163343135232 3683997339 A A A D B 163343138048 269790575 163477352704 4202440935 163477355776 271926323 B 163477356160 111228719 163611568128 10086395709 A D B 163745791232 276152313 164014223360 4799092032 164014225024 1844936076 B 164148440448 6304896315 164148441216 4538218731 A A D B 164148442752 1852133921 164148445184 24139880 164416878464 1531551050 B 164416880640 25132293 164551096448 1235390667 A D B 164551097984 120969526 164685312000 4871892984 164685312896 3090315844 B 164819531136 2258436006 164819532288 852752482 A A A A D B 164819533568 83105266 164953750528 448522840 165087965312 4634324819 B 165087965568 4097561355 165087966464 2473142955 A D B 165087968000 639059102 165087968128 540879267 165222185984 453525484 B 165356401792 2697953028 165356402688 1415284993 A A D B 165356403712 455985628 165356404736 28504610 165490622080 128916910 B 165490622464 28969651 165759053952 4700193321 A D B 165759054720 3168480922 165759055488 1934177316 165893272576 2950716087 B 165893273216 1940622941 165893273344 1763979811 A A A D B 165893273984 1008504899 165893274112 882962508 165893274880 307291085 B 166027490816 2132594262 166027493120 90945027 A D B 166027493248 56838378 166161708288 2536919930 166161709952 562418672 B 166161710720 134185074 166295926656 1612200180 A A D B 166295927296 893603569 166295927808 472385721 166295928064 312499688 B 166295928576 92560812 166295928832 31644633 A D B 166430145536 474604818 166430146176 136184726 166564361088 3223682595 B 166564363392 392105677 166564364160 59255203 A A A A A D B 166698579584 1977906153 166698579840 1628008199 166698579968 1465959380 B 166698580736 674316506 166698581760 94886683 A D B 166832797440 1804212308 166832798336 787795500 166832798592 574773826 B 166832798976 319083817 166832799488 95634633 A A D B 166832799744 33298690 166967017344 60960126 167101233920 682267646 B 167101234176 485202600 167101234304 399467100 A D B 167101234432 322213414 167101234816 140890114 167101234944 97087696 B 167101235072 61506447 167101235200 34080866 A A A D B 167235452544 141778158 167235452672 97792220 167369668608 1489094847 B 167369669120 919961072 167369669760 402960169 A D B 167369670016 255967459 167369670144 195124082 167369670400 98481688 B 167369670656 34830601 167503885952 2012669453 A A D B 167503886720 1052629498 167503886848 923038237 167503887104 689843142 B 167503887232 586196062 167503887616 326695355 A D B 167503887744 257213756 167503887872 196165657 167503888256 63075777 B 167638104320 1194575876 167638104448 1055971760 A A A A D B 167638104704 804841746 167638105216 406323528 167638105344 328131092 B 167638105472 258434129 167638105600 197184755 A D B 167638106112 35546092 167772322176 1059259666 167772322304 929041199 B 167772322560 694677913 167906540032 931965908 A A D B 167906540160 810151152 167906540416 592575765 167906540544 496761960 B 167906540928 260795707 167906541056 199154239 A D B 167906541184 145935895 167906541312 101083510 167906541440 64535437 B 167906541568 36225613 168040758272 498559423 A A A D B 168040758400 411118203 168040759040 101693630 168040759168 64996513 B 168040759296 36551370 168174975744 701596993 A D B 168174975872 596623870 168309193856 414143212 168309194752 37173895 B 168443411456 503722235 168443411584 415603174 A A D B 168443411712 336107919 168443411840 265192886 168443412096 148905730 B 168443412224 103423199 168443412480 37470289 A D B 168577629312 417027637 168577629440 337327874 168577630208 37756530 B 168711847296 267223470
noncomputable def AD2 : CTN :=
  A A A A A A A D B 168711847680 104489929 168711847936 38032446 168846064512 606001895 D B 168846064640 508532689 168846065024 268195732 168846065152 205294468 A D B 168846065280 150914051 168846065408 104996740 168846065536 67480260 B 168846065664 38297871 168980282880 206072326 A A D B 168980283008 151540478 168980283136 105485572 168980283264 67845240 B 168980283392 38552644 169114500096 511539143 A D B 169114500224 422363847 169114500608 206824589 169114500736 152145026 B 169114500864 105956227 169114500992 68195736 A A A D B 169114501120 38796613 169248717824 512981217 169248718080 342939204 B 169248718208 270937140 169248718464 152727482 A D B 169248718592 106408517 169248718720 68531579 169248718848 39029630 B 169382935552 514382105 169382935936 271791631 A A D B 169382936064 208251407 169382936192 153287643 169382936448 68852609 B 169382936576 39251555 169517153664 272616066 A D B 169517153920 153825315 169517154048 107257277 169517154304 39462254 B 169651371136 427106673 169651371264 345905083 A A A A D B 169651371392 273410216 169651371520 209573162 169651371648 154340311 B 169651371776 107653406 169651371904 69449617 A D B 169651372032 39661600 169785588992 346825346 169785589120 274173864 B 169785589376 154832452 169785589504 108030487 A A D B 169785589632 69725309 169785589760 39849474 169919806592 429250003 B 169919806848 274906804 169919806976 210788238 A D B 169919807104 155301570 169919807232 108388370 169919807360 69985616 B 169919807488 40025762 170054024576 275608838 A A A D B 170054024704 211355307 170054024832 155747504 170054024960 108726912 B 170054025088 70230413 170054025216 40190358 A D B 170188242304 276279778 170188242560 156170102 170188242688 109045980 B 170188242816 70459584 170188242944 40343163 A A D B 170322460032 276919447 170322460160 212407656 170322460288 156569221 B 170322460416 109345446 170322460544 70673019 A D B 170322460672 40484085 170456677888 212892627 170456678016 156944727 B 170456678144 109625194 170456678272 70870618 A A A A A D B 170456678400 40613038 170590895616 213349936 170590895744 157296496 D B 170590895872 109885114 170590896000 71052286 170590896128 40729946 A D B 170725113344 213779453 170725113472 157624410 170725113600 110125106 B 170725113728 71217940 170725113856 40834737 A A D B 170859331200 157928363 170859331328 110345078 170859331456 71367500 B 170859331584 40927349 170993548928 158208257 A D B 170993549056 110544946 170993549184 71500897 170993549312 41007726 B 171127766784 110724634 171127766912 71618069 A A A D B 171127767040 41075819 171261984640 71718964 171261984768 41131588 B 171396202496 41174998 171530420224 41206024 A D B 171664637952 41224648 171798855808 19042279 171798855936 5331210 B 171798856064 66057 171933073792 66057 A A D B 172335727360 3190314 172335727488 3180391 172335727616 3170505 B 172335727744 3160659 172335727872 3150850 A D B 172335728000 3141079 172335728128 3131346 172335728256 3121651 B 172335728384 3111994 172335728512 3102374 A A A A D B 172335728640 3092790 172335728768 3083244 172335728896 3073735 B 172335729024 3064262 172335729152 3054826 A D B 172335729280 3045426 172335729408 3036063 172335729536 3026735 B 172335729664 3017443 172335729792 3008187 A A D B 172335729920 2998966 172335730048 2989781 172335730176 2980630 B 172335730304 2971515 172335730432 2962434 A D B 172335730560 2953389 172335730688 2944377 172335730816 2935400 B 172335730944 2926458 172335731072 2917549 A A A D B 172335731200 2908674 172335731328 2899833 172335731456 2891025 B 172335731584 2882251 172335731712 2873511 A D B 172335731840 2864803 172335731968 2856128 172335732096 2847486 B 172335732224 2838877 172335732352 2830300 A A D B 172335732480 2821756 172335732608 2813244 172335732736 2804764 B 172335732864 2796316 172335733120 2779515 A D B 172335733248 2771162 172335733632 2746290 172335733888 2729864 B 172335734144 2713560 172335734784 2673331 A A A A A A D B 172469945216 14630951 172469945344 14585475 172469945472 14540176 D B 172469945600 14495053 172469945728 14450104 172469945856 14405330 A D B 172469945984 14360729 172469946112 14316301 172469946240 14272044 B 172469946368 14227959 172469946496 14184043 A A D B 172469946624 14140297 172469946752 14096720 172469946880 14053310 B 172469947008 14010067 172469947136 13966991 A D B 172469947264 13924080 172469947392 13881334 172469947520 13838751 B 172469947648 13796332 172469947776 13754076 A A A D B 172469947904 13711981 172469948032 13670047 172469948160 13628274 B 172469948288 13586660 172469948416 13545204 A D B 172469948544 13503907 172469948672 13462767 172469948800 13421784 B 172469948928 13380956 172469949056 13340284 A A D B 172469949184 13299766 172469949312 13259402 172469949440 13219191 B 172469949568 13179133 172469949696 13139226 A D B 172469949824 13099470 172469949952 13059864 172469950080 13020409 B 172469950208 12981102 172469950464 12902932 A A A A D B 172469950592 12864067 172469950720 12825350 172469950848 12786777 B 172469950976 12748350 172469951104 12710067 A D B 172469951360 12633931 172469951488 12596077 172469951616 12558365 B 172469951744 12520793 172469951872 12483362 A A D B 172469952000 12446072 172469952128 12408920 172469952384 12335031 B 172469952512 12298293 172604163072 34341658 A D B 172604163200 34235001 172604163328 34128757 172604163456 34022926 B 172604163584 33917505 172604163712 33812491 A A A D B 172604163840 33707884 172604163968 33603682 172604164096 33499882 B 172604164224 33396482 172604164352 33293481 A D B 172604164480 33190878 172604164608 33088669 172604164736 32986854 B 172604164864 32885430 172604164992 32784395 A A D B 172604165120 32683749 172604165248 32583489 172604165376 32483613 B 172604165504 32384119 172604165632 32285007 A D B 172604165760 32186273 172604165888 32087917 172604166016 31989936 B 172604166144 31892329 172604166272 31795094 A A A A A D B 172604166400 31698230 172604166528 31601734 172604166656 31505605 B 172604166784 31409842 172604166912 31314443 A D B 172604167040 31219405 172604167168 31124728 172604167296 31030410 B 172604167424 30936449 172604167552 30842843 A A D B 172604167680 30749591 172604167808 30656692 172604167936 30564143 B 172604168064 30471943 172604168192 30380091 A D B 172604168448 30197423 172604168576 30106604 172604168704 30016127 B 172604168960 29836189 172604169088 29746726 A A A D B 172604169344 29568804 172604169472 29480342 172604169600 29392211 B 172604170112 29042964 172604170240 28956464 A D B 172738380928 62271744 172738381056 62078493 172738381184 61885991 B 172738381312 61694234 172738381440 61503221 A A D B 172738381568 61312946 172738381696 61123406 172738381824 60934599 B 172738381952 60746521 172738382080 60559168 A D B 172738382208 60372537 172738382336 60186624 172738382464 60001427 B 172738382592 59816942 172738382720 59633166 A A A A D B 172738382848 59450095 172738382976 59267727 172738383104 59086058 B 172738383232 58905084 172738383360 58724803 A D B 172738383488 58545211 172738383616 58366306 172738383744 58188084 B 172738383872 58010542 172738384000 57833677 A A D B 172738384128 57657485 172738384256 57481964 172738384384 57307111 B 172738384512 57132923 172738384640 56959396 A D B 172738384768 56786527 172738384896 56614314 172738385024 56442754 B 172738385152 56271844 172738385280 56101580 A A A D B 172738385408 55931959 172738385536 55762980 172738385664 55594638 B 172738385792 55426932 172738385920 55259857 A D B 172738386048 55093412 172738386176 54927594 172738386304 54762398 B 172738386432 54597824 172738386560 54433868 A A D B 172738386688 54270527 172738386816 54107798 172738386944 53945679 B 172738387072 53784167 172738387200 53623259 A D B 172738387456 53303246 172738387584 53144135 172738387712 52985617 B 172738387968 52670351
noncomputable def AD3 : CTN :=
  A A A A A A A D B 172872598912 98060743 172872599040 97756897 172872599168 97454229 D B 172872599296 97152731 172872599424 96852398 172872599552 96553226 A D B 172872599680 96255209 172872599808 95958340 172872599936 95662616 B 172872600064 95368031 172872600192 95074579 A A D B 172872600320 94782256 172872600448 94491055 172872600576 94200972 B 172872600704 93912003 172872600832 93624140 A D B 172872600960 93337381 172872601088 93051719 172872601216 92767149 B 172872601344 92483667 172872601472 92201267 A A A D B 172872601600 91919944 172872601728 91639694 172872601856 91360512 B 172872601984 91082393 172872602112 90805331 A D B 172872602240 90529323 172872602368 90254363 172872602496 89980446 B 172872602624 89707568 172872602752 89435724 A A D B 172872602880 89164910 172872603008 88895120 172872603136 88626350 B 172872603264 88358596 172872603392 88091852 A D B 172872603520 87826114 172872603648 87561378 172872603776 87297640 B 172872603904 87034894 172872604032 86773136 A A A A D B 172872604160 86512361 172872604416 85993746 172872604544 85735896 B 172872604928 84968126 172872605056 84714115 A D B 172872605184 84461052 172872605312 84208934 172872605440 83957756 B 172872605696 83458205 173006816640 142563595 A A D B 173006816768 142121855 173006816896 141681827 173006817024 141243500 B 173006817152 140806868 173006817280 140371923 A D B 173006817408 139938656 173006817536 139507060 173006817664 139077128 B 173006817792 138648851 173006817920 138222222 A A A D B 173006818048 137797234 173006818176 137373878 173006818304 136952147 B 173006818432 136532034 173006818560 136113532 A D B 173006818688 135696632 173006818816 135281328 173006818944 134867612 B 173006819072 134455477 173006819200 134044916 A A D B 173006819328 133635921 173006819456 133228486 173006819584 132822602 B 173006819712 132418264 173006819840 132015464 A D B 173006819968 131614195 173006820096 131214450 173006820224 130816221 B 173006820352 130419504 173006820480 130024289 A A A A A D B 173006820608 129630571 173006820736 129238342 173006820864 128847597 D B 173006820992 128458327 173006821120 128070528 173006821248 127684191 A D B 173006821376 127299310 173006821504 126915879 173006821632 126533891 B 173006821760 126153339 173006821888 125774218 A A D B 173006822016 125396520 173006822144 125020240 173006822272 124645370 B 173006822528 123899838 173006822656 123529163 A D B 173006823168 122060258 173006823296 121696449 173006823424 121333996 B 173141034624 194197300 173141034752 193596505 A A A D B 173141034880 192998032 173141035008 192401870 173141035136 191808010 B 173141035264 191216440 173141035392 190627150 A D B 173141035520 190040129 173141035648 189455366 173141035776 188872852 B 173141035904 188292576 173141036032 187714528 A A D B 173141036160 187138697 173141036288 186565073 173141036416 185993647 B 173141036544 185424407 173141036672 184857344 A D B 173141036800 184292448 173141036928 183729709 173141037056 183169117 B 173141037184 182610663 173141037312 182054335 A A A A D B 173141037440 181500126 173141037568 180948025 173141037696 180398022 B 173141037824 179850108 173141037952 179304274 A D B 173141038080 178760509 173141038208 178218805 173141038336 177679153 B 173141038464 177141542 173141038592 176605963 A A D B 173141038720 176072408 173141038848 175540867 173141038976 175011331 B 173141039104 174483792 173141039232 173958239 A D B 173141039360 173434664 173141039616 172393412 173141039744 171875718 B 173141039872 171359966 173141040000 170846148 A A A D B 173141040128 170334255 173141040512 168810041 173141040768 167803366 B 173141040896 167302844 173141041152 166307388 A D B 173275252480 254217963 173275252608 253432088 173275252736 252649249 B 173275252864 251869431 173275252992 251092621 A A D B 173275253120 250318805 173275253248 249547968 173275253376 248780098 B 173275253504 248015179 173275253632 247253200 A D B 173275253760 246494146 173275253888 245738003 173275254016 244984759 B 173275254144 244234399 173275254272 243486912 A A A A A A D B 173275254400 242742283 173275254528 242000499 173275254656 241261548 D B 173275254784 240525416 173275254912 239792091 173275255040 239061560 A D B 173275255168 238333809 173275255296 237608827 173275255424 236886600 B 173275255552 236167116 173275255680 235450363 A A D B 173275255808 234736328 173275255936 234024998 173275256192 232610408 B 173275256320 231907122 173275256448 231206493 A D B 173275256576 230508509 173275256704 229813158 173275256832 229120428 B 173275256960 228430308 173275257088 227742784 A A A D B 173275257216 227057846 173275257344 226375482 173275257472 225695681 B 173275257600 225018430 173275257728 224343719 A D B 173275257856 223671535 173275257984 223001869 173275258240 221670039 B 173275258496 220348142 173275258624 219690889 A A D B 173275258752 219036086 173275258880 218383722 173409470336 322110202 B 173409470464 321115220 173409470592 320124078 A D B 173409470720 319136758 173409470848 318153244 173409470976 317173516 B 173409471104 316197559 173409471232 315225354 A A A A D B 173409471360 314256884 173409471488 313292131 173409471616 312331080 B 173409471744 311373712 173409471872 310420012 A D B 173409472000 309469961 173409472128 308523543 173409472256 307580742 B 173409472384 306641541 173409472512 305705923 A A D B 173409472640 304773873 173409472768 303845373 173409472896 302920407 B 173409473024 301998961 173409473152 301081016 A D B 173409473280 300166558 173409473408 299255570 173409473536 298348037 B 173409473664 297443943 173409473792 296543272 A A A D B 173409473920 295646009 173409474048 294752139 173409474176 293861645 B 173409474304 292974513 173409474432 292090727 A D B 173409474560 291210273 173409474688 290333135 173409474816 289459298 B 173409474944 288588747 173409475072 287721468 A A D B 173409475200 286857445 173409475328 285996665 173409475456 285139112 B 173409475584 284284772 173409475840 282585674 A D B 173409475968 281740887 173409476224 280060765 173409476608 277564003 B 173543688192 397795907 173543688320 396568085 A A A A A D B 173543688448 395344999 173543688576 394126626 173543688704 392912944 D B 173543688832 391703933 173543688960 390499570 173543689088 389299835 A D B 173543689216 388104705 173543689344 386914159 173543689472 385728177 B 173543689600 384546737 173543689728 383369819 A A D B 173543689856 382197402 173543689984 381029465 173543690112 379865987 B 173543690240 378706948 173543690368 377552329 A D B 173543690496 376402108 173543690624 375256266 173543690752 374114782 B 173543690880 372977637 173543691008 371844811 A A A D B 173543691136 370716284 173543691264 369592036 173543691392 368472049 B 173543691520 367356303 173543691648 366244778 A D B 173543691904 364034316 173543692032 362935342 173543692160 361840512 B 173543692288 360749810 173543692416 359663216 A A D B 173543692544 358580711 173543692672 357502277 173543692800 356427896 B 173543692928 355357550 173543693056 354291219 A D B 173543693312 352170535 173543693440 351116146 173543693568 350065701 B 173543693696 349019183 173543693952 346937856 A A A A D B 173543694336 343844881 173677906176 479708474 173677906304 478230110 B 173677906432 476757438 173677906560 475290434 A D B 173677906688 473829070 173677906816 472373320 173677906944 470923159 B 173677907072 469478560 173677907200 468039499 A A D B 173677907328 466605949 173677907456 465177886 173677907584 463755284 B 173677907712 462338118 173677907840 460926364 A D B 173677907968 459519996 173677908096 458118990 173677908224 456723321 B 173677908352 455332965 173677908480 453947898 A A A D B 173677908608 452568095 173677908736 451193533 173677908864 449824187 B 173677908992 448460034 173677909120 447101051 A D B 173677909248 445747213 173677909376 444398497 173677909504 443054881 B 173677909632 441716341 173677909760 440382854 A A D B 173677909888 439054397 173677910016 437730947 173677910144 436412482 B 173677910272 435098980 173677910400 433790417 A D B 173677910528 432486771 173677910656 431188021 173677910784 429894145 B 173677910912 428605119
noncomputable def AD4 : CTN :=
  A A A A A A A D B 173677911168 426041536 173677911296 424766934 173677911552 422232004 D B 173677911680 420971632 173677911808 419715962 173677911936 418464972 A D B 173677912064 417218641 173812124160 568693187 173812124288 566943292 B 173812124416 565200125 173812124544 563463655 A A D B 173812124672 561733851 173812124800 560010683 173812124928 558294119 B 173812125056 556584131 173812125184 554880686 A D B 173812125312 553183756 173812125440 551493311 173812125568 549809320 B 173812125696 548131754 173812125824 546460584 A A A D B 173812125952 544795781 173812126080 543137315 173812126208 541485158 B 173812126336 539839280 173812126464 538199653 A D B 173812126592 536566249 173812126720 534939039 173812126848 533317995 B 173812126976 531703090 173812127104 530094294 A A D B 173812127232 528491581 173812127360 526894923 173812127488 525304292 B 173812127616 523719661 173812127744 522141004 A D B 173812127872 520568292 173812128000 519001499 173812128128 517440599 B 173812128256 515885565 173812128384 514336370 A A A A D B 173812128512 512792988 173812128640 511255393 173812128768 509723558 B 173812128896 508197459 173812129024 506677069 A D B 173812129152 505162362 173812129280 503653314 173812129408 502149898 B 173812129536 500652090 173812129664 499159865 A A D B 173812129792 497673197 173946342016 666643751 173946342144 664594037 B 173946342272 662552199 173946342400 660518198 A D B 173946342528 658492000 173946342656 656473569 173946342784 654462868 B 173946342912 652459862 173946343040 650464517 A A A D B 173946343168 648476796 173946343296 646496665 173946343424 644524089 B 173946343552 642559034 173946343680 640601464 A D B 173946343808 638651347 173946343936 636708648 173946344064 634773332 B 173946344192 632845367 173946344320 630924719 A A D B 173946344448 629011354 173946344576 627105240 173946344704 625206343 B 173946344832 623314631 173946344960 621430071 A D B 173946345088 619552631 173946345216 617682278 173946345344 615818980 B 173946345472 613962706 173946345600 612113423 A A A A A D B 173946345728 610271100 173946345856 608435706 173946345984 606607209 D B 173946346112 604785579 173946346240 602970783 173946346368 601162793 A D B 173946346496 599361576 173946346624 597567103 173946346752 595779343 B 173946346880 593998266 173946347136 590456042 A A D B 173946347264 588694835 173946347392 586940192 173946347520 585192084 B 174080560000 769615349 174080560128 767252671 A D B 174080560256 764899055 174080560384 762554461 174080560512 760218847 B 174080560640 757892172 174080560768 755574395 A A A D B 174080560896 753265474 174080561024 750965370 174080561152 748674041 B 174080561280 746391449 174080561408 744117552 A D B 174080561536 741852311 174080561664 739595687 174080561792 737347640 B 174080561920 735108131 174080562048 732877121 A A D B 174080562176 730654572 174080562304 728440445 174080562432 726234702 B 174080562560 724037304 174080562688 721848214 A D B 174080562816 719667394 174080562944 717494807 174080563072 715330415 B 174080563200 713174182 174080563328 711026070 A A A A D B 174080563456 708886043 174080563584 706754063 174080563712 704630096 B 174080563840 702514105 174080563968 700406053 A D B 174080564096 698305905 174080564224 696213626 174080564352 694129181 B 174080564480 692052533 174080564736 687922492 A A D B 174080564864 685869029 174080564992 683823225 174080565120 681785046 B 174080565248 679754458 174214777728 884624545 A D B 174214777856 881908794 174214777984 879203461 174214778112 876508497 B 174214778240 873823856 174214778368 871149488 A A A D B 174214778496 868485349 174214778624 865831389 174214778752 863187564 B 174214778880 860553826 174214779008 857930129 A D B 174214779136 855316427 174214779264 852712675 174214779392 850118827 B 174214779520 847534838 174214779648 844960663 A A D B 174214779776 842396257 174214779904 839841577 174214780032 837296576 B 174214780160 834761213 174214780288 832235442 A D B 174214780416 829719221 174214780544 827212505 174214780672 824715253 B 174214780800 822227420 174214780928 819748965 A A A A A A D B 174214781184 814820018 174214781312 812369442 174214781440 809928075 D B 174214781568 807495875 174214781696 805072802 174214781824 802658814 A D B 174214781952 800253871 174214782080 797857931 174214782208 795470955 B 174214782336 793092902 174214782464 790723732 A A D B 174214782592 788363405 174214782720 786011882 174214782848 783669123 B 174214782976 781335090 174348995584 1004453150 A D B 174348995712 1001371902 174348995840 998302463 174348995968 995244781 B 174348996096 992198801 174348996224 989164469 A A A D B 174348996352 986141733 174348996480 983130539 174348996608 980130833 B 174348996736 977142564 174348996864 974165679 A D B 174348996992 971200127 174348997120 968245854 174348997248 965302811 B 174348997376 962370945 174348997504 959450206 A A D B 174348997632 956540544 174348997760 953641907 174348997888 950754245 B 174348998016 947877510 174348998144 945011651 A D B 174348998272 942156618 174348998400 939312363 174348998528 936478838 B 174348998656 933655993 174348998784 930843780 A A A A D B 174348998912 928042151 174348999040 925251058 174348999168 922470454 B 174348999296 919700292 174348999424 916940525 A D B 174348999552 914191105 174348999680 911451986 174348999808 908723122 B 174349000064 903295975 174349000192 900597600 A A D B 174349000320 897909298 174349000448 895231022 174349000704 889904373 B 174483213440 1131366140 174483213568 1127898239 A D B 174483213696 1124443620 174483213824 1121002223 174483213952 1117573986 B 174483214080 1114158849 174483214208 1110756753 A A A D B 174483214336 1107367638 174483214464 1103991443 174483214592 1100628111 B 174483214720 1097277581 174483214848 1093939797 A D B 174483214976 1090614699 174483215104 1087302230 174483215232 1084002332 B 174483215360 1080714948 174483215488 1077440021 A A D B 174483215616 1074177495 174483215744 1070927312 174483215872 1067689418 B 174483216000 1064463756 174483216128 1061250272 A D B 174483216256 1058048909 174483216384 1054859613 174483216512 1051682329 B 174483216640 1048517003 174483216768 1045363582 A A A A A D B 174483216896 1042222011 174483217024 1039092237 174483217152 1035974207 B 174483217280 1032867868 174483217408 1029773167 A D B 174483217536 1026690053 174483217664 1023618472 174483217792 1020558374 B 174483217920 1017509707 174483218048 1014472420 A A D B 174483218304 1008431780 174483218432 1005428326 174617431424 1261377485 B 174617431552 1257516997 174617431680 1253671273 A D B 174617431808 1249840244 174617431936 1246023843 174617432064 1242222003 B 174617432192 1238434658 174617432320 1234661742 A A A D B 174617432448 1230903188 174617432576 1227158930 174617432704 1223428905 B 174617432832 1219713046 174617432960 1216011289 A D B 174617433088 1212323570 174617433216 1208649825 174617433344 1204989991 B 174617433472 1201344004 174617433600 1197711801 A A D B 174617433728 1194093321 174617433856 1190488501 174617433984 1186897278 B 174617434112 1183319592 174617434240 1179755381 A D B 174617434368 1176204585 174617434496 1172667142 174617434624 1169142993 B 174617434752 1165632078 174617434880 1162134337 A A A A D B 174617435008 1158649710 174617435136 1155178139 174617435264 1151719565 B 174617435392 1148273930 174617435520 1144841176 A D B 174617435648 1141421244 174617435776 1138014078 174617435904 1134619620 B 174617436032 1131237814 174617436160 1127868602 A A D B 174751649280 1401695513 174751649408 1397408863 174751649536 1393138594 B 174751649664 1388884630 174751649792 1384646897 A D B 174751649920 1380425320 174751650048 1376219826 174751650176 1372030341 B 174751650304 1367856792 174751650432 1363699107 A A A D B 174751650560 1359557212 174751650688 1355431036 174751650816 1351320508 B 174751650944 1347225556 174751651072 1343146110 A D B 174751651200 1339082098 174751651328 1335033452 174751651456 1331000101 B 174751651584 1326981976 174751651712 1322979007 A A D B 174751651840 1318991128 174751651968 1315018268 174751652096 1311060361 B 174751652224 1307117339 174751652352 1303189135 A D B 174751652480 1299275681 174751652608 1295376912 174751652736 1291492761 B 174751652864 1287623163
noncomputable def AD5 : CTN :=
  A A A A A A A D B 174751653120 1279927364 174751653248 1276101033 174751653376 1272288995 D B 174751653504 1268491186 174751653632 1264707542 174751653888 1257182497 A D B 174885867136 1548734463 174885867264 1544001766 174885867392 1539287140 B 174885867520 1534590502 174885867648 1529911770 A A D B 174885867776 1525250863 174885867904 1520607698 174885868032 1515982195 B 174885868160 1511374273 174885868288 1506783852 A D B 174885868416 1502210852 174885868544 1497655194 174885868672 1493116799 B 174885868800 1488595589 174885868928 1484091485 A A A D B 174885869056 1479604410 174885869184 1475134287 174885869312 1470681038 B 174885869440 1466244588 174885869568 1461824860 A D B 174885869696 1457421779 174885869824 1453035270 174885869952 1448665257 B 174885870336 1435653458 174885870464 1431348692 A A D B 174885870592 1427060055 174885870848 1418530876 174885870976 1414290191 B 174885871104 1410065347 174885871232 1405856272 A D B 174885871360 1401662897 174885871488 1397485151 174885871616 1393322965 B 175020084992 1702372830 175020085120 1697174616 A A A A D B 175020085248 1691996236 175020085376 1686837598 175020085504 1681698613 B 175020085632 1676579190 175020085760 1671479241 A D B 175020085888 1666398676 175020086016 1661337407 175020086144 1656295346 B 175020086272 1651272406 175020086400 1646268500 A A D B 175020086528 1641283541 175020086656 1636317443 175020086784 1631370121 B 175020086912 1626441489 175020087040 1621531463 A D B 175020087168 1616639958 175020087296 1611766891 175020087424 1606912178 B 175020087552 1602075736 175020087680 1597257483 A A A D B 175020087808 1592457337 175020087936 1587675217 175020088064 1582911040 B 175020088192 1578164726 175020088320 1573436196 A D B 175020088448 1568725368 175020088704 1559356504 175020088832 1554698310 B 175020088960 1550057503 175020089216 1540827741 A A D B 175020089344 1536238631 175154302976 1856802773 175154303104 1851141665 B 175154303232 1845502124 175154303360 1839884051 A D B 175154303488 1834287348 175154303616 1828711918 175154303744 1823157663 B 175154303872 1817624488 175154304000 1812112295 A A A A A D B 175154304128 1806620990 175154304256 1801150478 175154304384 1795700664 D B 175154304512 1790271455 175154304640 1784862757 175154304768 1779474476 A D B 175154304896 1774106521 175154305024 1768758799 175154305152 1763431220 B 175154305280 1758123692 175154305408 1752836124 A A D B 175154305536 1747568426 175154305664 1742320510 175154305792 1737092285 B 175154305920 1731883663 175154306048 1726694557 A D B 175154306176 1721524877 175154306304 1716374538 175154306688 1701038695 B 175154306816 1695964853 175154307072 1685873815 A A A D B 175288520704 2028944063 175288520832 2022758123 175288520960 2016595749 B 175288521088 2010456833 175288521216 2004341269 A D B 175288521344 1998248949 175288521472 1992179768 175288521600 1986133620 B 175288521728 1980110401 175288521856 1974110006 A A D B 175288521984 1968132331 175288522112 1962177274 175288522240 1956244731 B 175288522368 1950334600 175288522496 1944446781 A D B 175288522624 1938581171 175288522752 1932737670 175288523008 1921116598 B 175288523136 1915338828 175288523264 1909582771 A A A A D B 175288523392 1903848328 175288523520 1898135403 175288523776 1886773717 B 175288524032 1875496946 175288524160 1869890165 A D B 175288524416 1858739341 175288524544 1853195110 175288524672 1847671543 B 175288524800 1842168548 175422738816 2188227438 A A D B 175422738944 2181571117 175422739072 2174940096 175422739200 2168334260 B 175422739328 2161753494 175422739456 2155197683 A D B 175422739584 2148666715 175422739712 2142160477 175422739840 2135678855 B 175422739968 2129221739 175422740096 2122789017 A A A D B 175422740224 2116380579 175422740352 2109996314 175422740480 2103636114 B 175422740608 2097299870 175422740736 2090987472 A D B 175422740864 2084698814 175422741120 2072192290 175422741248 2065974211 B 175422741376 2059779446 175422741632 2047459442 A A D B 175422742016 2029151691 175422742144 2023094631 175422742272 2017060163 B 175422742400 2011048186 175422742528 2005058599 A D B 175556956672 2365902399 175556956800 2358711091 175556956928 2351547097 B 175556957056 2344410291 175556957184 2337300549 A A A A A A D B 175556957312 2330217748 175556957440 2323161767 175556957568 2316132482 D B 175556957696 2309129774 175556957952 2295203603 175556958080 2288279902 A D B 175556958208 2281382298 175556958336 2274510674 175556958464 2267664912 B 175556958592 2260844896 175556958720 2254050509 A A D B 175556958848 2247281636 175556958976 2240538162 175556959104 2233819972 B 175556959360 2220458992 175556959488 2213815976 A D B 175556959744 2200604333 175556960128 2180971177 175556960256 2174475502 B 175691174528 2549483104 175691174784 2534025658 A A A D B 175691174912 2526340882 175691175040 2518685226 175691175168 2511058559 B 175691175296 2503460747 175691175424 2495891661 A D B 175691175552 2488351170 175691175680 2480839145 175691175936 2465899976 B 175691176064 2458472577 175691176192 2451073131 A A D B 175691176320 2443701514 175691176448 2436357598 175691176576 2429041260 B 175691176832 2414490820 175691176960 2407256471 A D B 175691177856 2357367627 175691177984 2350346583 175825392640 2722236081 B 175825392768 2713986798 175825392896 2705768750 A A A A D B 175825393152 2689425795 175825393280 2681300606 175825393408 2673206091 B 175825393792 2649105194 175825393920 2641131988 A D B 175825394048 2633188767 175825394304 2617391742 175825394432 2609537669 B 175825394688 2593917737 175825394816 2586151614 A A D B 175825395200 2563027044 175825395328 2555376355 175825395456 2547754202 B 175825395584 2540160457 175825395712 2532594994 A D B 175959611008 2880916087 175959611136 2872218956 175959611264 2863554633 B 175959611392 2854922968 175959611648 2837757025 A A A D B 175959611776 2829222453 175959612032 2812249382 175959612544 2778683512 B 175959612672 2770370439 175959612800 2762088442 A D B 175959613056 2745617120 175959613312 2729268440 175959613440 2721139749 B 176093828864 3077787930 176093828992 3068503488 A A D B 176093829120 3059254043 176093829504 3031714103 176093829632 3022603067 B 176093829760 3013526245 176093829888 3004483481 A D B 176093830144 2986499518 176093830272 2977558015 176093830400 2968649963 B 176093830528 2959775211 176093830784 2942125012 A A A A A D B 176093830912 2933349269 176093831168 2915895760 176228047232 3240571028 B 176228047616 3211464469 176228048000 3182684089 A D B 176228048256 3163676215 176228048384 3154225510 176228048640 3135429771 B 176228048896 3116773877 176362264832 3466120735 A A D B 176362265216 3434964942 176362265600 3404158555 176362266240 3353578317 B 176362266624 3323680930 176496483584 3600502270 A D B 176496484352 3536519776 176630702080 3755189350 176764919296 4027404008 B 176764919808 3979584708 176899137536 4209597088 A A A D B 177033355264 4445113958 177167572992 4686019082 177301790720 4932192574 B 177436008448 5183510966 177570226176 5439847270 A D B 177704443904 5701071046 177838661632 5967048477 177972879360 6237642433 B 178107097088 6512712553 178241314816 6792115318 A A D B 178375532544 7075704133 178509750272 7363329404 178643968000 7654838625 B 178778185728 7950076462 178912403456 8248884841 A D B 179046621184 8551103036 179180838912 8856567762 179315056640 9165113264 B 179717709824 10107541899 179986145280 10748090468 A A A A D B 180388798592 11688866092 180388798720 11654104527 180388798848 11619472136 B 180388798976 11584968342 180388799104 11550592573 A D B 180388799232 11516344258 180388799360 11482222831 180388799488 11448227727 B 180388799616 11414358387 180388799744 11380614252 A A D B 180388799872 11346994766 180388800000 11313499377 180388800128 11280127536 B 180388800256 11246878697 180388800384 11213752314 A D B 180388800512 11180747848 180388800640 11147864760 180388800768 11115102515 B 180388800896 11082460580 180388801024 11049938424 A A A D B 180388801152 11017535522 180388801280 10985251347 180388801408 10953085379 B 180388801536 10921037098 180388801664 10889105988 A D B 180388801792 10857291534 180388801920 10825593226 180388802048 10794010555 B 180388802176 10762543015 180388802304 10731190103 A A D B 180388802432 10699951317 180388802560 10668826159 180388802688 10637814134 B 180388802816 10606914747 180388802944 10576127510 A D B 180388803072 10545451932 180388803200 10514887529 180388803328 10484433817 B 180388803456 10454090316
noncomputable def AD6 : CTN :=
  A A A A A A A D B 180388803712 10393732032 180388803840 10363716300 180388803968 10333808879 D B 180388804096 10304009300 180388804224 10274317097 180388804352 10244731805 A D B 180388804480 10215252963 180388804608 10185880112 180388804736 10156612794 B 180388804864 10127450554 180388804992 10098392940 A A D B 180388805120 10069439501 180388805248 10040589791 180388805376 10011843362 B 180388805504 9983199771 180388805632 9954658577 A D B 180388805760 9926219341 180388805888 9897881626 180388806016 9869644998 B 180388806144 9841509023 180388806272 9813473271 A A A D B 180388806400 9785537314 180388806528 9757700727 180388806656 9729963084 B 181730980224 13571929850 182133637120 13313645890 A D B 184281120768 17498649551 185086427136 18883287715 185354862592 19313017890 B 185489080320 19521303807 187904999424 22377432791 A A D B 188307652608 22665492627 188576088064 22824575895 188710305792 22894052265 B 188978741504 22868327409 188978741632 22786289547 A D B 188978741760 22697744874 188978741888 22602764358 188978742016 22501422485 B 188978742272 22279969817 188978742400 22160024998 A A A A D B 188978742528 22034050636 188978742656 21902137809 188978742784 21764380703 B 188978742912 21620876535 188978743040 21471725482 A D B 188978743168 21317030601 188978743296 21156897754 188978743424 20991435527 B 188978743552 20820755150 188978743680 20644970417 A A D B 188978743808 20464197604 188978743936 20278555381 188978744064 20088164734 B 188978744192 19893148878 188978744320 19693633166 A D B 188978744448 19489745009 188978744576 19281613785 188978744832 18853148956 B 188978744960 18633083148 188978745088 18409309687 A A A D B 188978745216 18181966454 188978745344 17951192761 188978745600 17479917837 B 188978745856 16996624543 188978745984 16750831874 A D B 188978746112 16502469524 188978746240 16251684254 188978746368 15998623519 B 188978746496 15743435378 188978746880 14966594275 A A D B 188978747008 14704386007 188978747264 14175975540 188978747392 13910072854 B 188978747648 13375620595 188978747776 13107369549 A D B 188978747904 12838633661 188978748032 12569561193 188978748544 11492849466 B 188978748672 11224295565 188978748928 10688945415 A A A A A D B 188978749312 9892436003 188978749440 9629227507 189515620352 9730938999 D B 190455144448 9909876529 191260450816 10063803038 191528886272 10115150815 A D B 191663101568 15424237652 191663104000 10140823567 191931539456 10192157367 B 192065757184 10217814632 192468410368 10294725141 A A D B 192736845824 10345928746 192871063552 10371503821 193273716736 10448099292 B 194079023104 10600535082 194615894016 10701435097 A D B 194750111744 10726552306 194884329472 10751622640 195286982656 10826533721 B 195555418112 10876205930 195689635840 10900955939 A A A D B 195958071296 10950274600 196629159936 11072428665 196763377664 11096649244 B 197031813120 11144865996 197166030848 11168858670 A D B 197300248576 11192771896 197434466304 11216603951 197568684288 10648370487 B 197568684416 10354926600 197568684672 9773861290 A A D B 197568684800 9486525197 197568684928 9201507020 197568685184 8638972399 B 197568685312 8361724435 197568685440 8087331212 A D B 197568685696 7547620265 197568685952 7020837345 197568686464 6009840171 B 197568686592 5766613749 197568686720 5527409608 A A A A D B 197568686976 5061471195 197568687232 4612801060 197568687616 3973751300 B 197568688000 3377422809 197568688128 3188490500 A D B 197568688384 2825797799 197568688512 2652161165 197568688640 2483741266 B 197568688896 2162762215 197568689024 2010299858 A A D B 197568689280 1721645940 197568689536 1454935186 197568689792 1210418225 B 197568690048 988290955 197568690432 697374939 A D B 197568690560 611716331 197568690688 531721289 197568690944 388714969 B 197568691200 268308993 197568691456 170403893 A A A D B 197568691584 129843933 197568691712 94848521 197568691840 65390837 B 197568691968 41440954 197568692096 22965865 A D B 197568692224 9929527 197837127552 23726432 197971341568 2849245874 B 198239776512 3617811043 198239779584 398471301 A A D B 198239780224 134823818 198373996416 1009994263 198373997312 400376823 B 198642434048 11866683 198776649600 1020490969 A D B 198776651264 102192692 198910869504 12342206 199045084672 1378036534 B 199045085440 728133348 199179302528 1259356997 A A A A A A D B 199179302784 1030732330 199179303296 642318771 199179304192 184037443 D B 199179304448 104511627 199179304832 27399304 199313520256 1263232580 A D B 199313520768 827888775 199581954560 2586218556 199581955456 1523924476 B 199581958016 28442808 199716175872 13729394 A A D B 199850392704 238350679 199850393216 76211417 199984608896 1282093793 B 199984609792 572428551 199984610560 190256597 A D B 199984610688 146732828 199984611328 14174948 200118827392 658673170 B 200118827648 496112447 200118827904 356800250 A A A D B 200118828544 109621508 200118829056 14393956 200253045376 497948203 B 200387262976 578522852 200387264512 14823774 A D B 200521481344 244018390 200521481728 111668556 200655697280 1557328606 B 200789915264 1303523130 200789915648 960287395 A A D B 200789915904 760631337 200789916032 669583132 200789916800 246175590 B 200789917312 80081328 200789917568 31348955 A D B 200789917696 15446078 200924133120 1186490719 200924133760 671683101 B 200924134656 196910988 200924135296 31647849 A A A A D B 200924135424 15647032 201192569216 675798190 201192570368 114869492 B 201326788096 115476336 201461003520 1719441435 A D B 201461005056 439057306 201461006336 16415226 201595223168 252244760 B 201595223296 201225236 201595223936 33059776 A A D B 201595224064 16597792 201729439872 874443884 201729440128 683679561 B 201729440256 597168216 201729440896 253195154 A D B 201729441024 202041351 201729441664 33324737 201729441792 16776340 B 201863657984 598883182 201863658752 202841409 A A A D B 201863659008 117786539 201863659264 55909533 201863659520 16950765 B 202132094592 84837858 202132094976 17286823 A D B 202266311168 603856474 202266312704 17448255 202400529920 119901171 B 202400530304 34555658 202400530432 17605157 A A D B 202534747008 380087936 202534747264 258510980 202534747776 86066726 B 202534748032 34782266 202534748160 17757436 A D B 202668965120 207293841 202668965504 86454684 202668965760 35002095 B 202668965888 17905000 202803182336 452209979 A A A A A D B 202803182976 161725020 202803183232 86831591 202803183488 35215043 B 202803183616 18047760 202937401344 18185629 A D B 203071617792 454535861 203071617920 384279957 203071618304 209288342 B 203071618432 162823857 203071618688 87551757 A A D B 203071618816 58685102 203071619072 18318526 203205836032 209917739 B 203205836416 87894777 203205836672 35811628 A D B 203205836800 18446369 203340054016 123101652 203340054144 88226268 B 203340054400 35996095 203340054528 18569082 A A A D B 203474271488 211122470 203474271616 164354165 203474271872 88546122 B 203474272256 18686590 203608489728 59682118 A D B 203608489856 36342919 203608489984 18798824 203742706816 265173624 B 203742707328 89150501 203742707712 18905716 A A D B 203876924800 165739767 203876924928 124629964 203876925056 89434828 B 203876925440 19007200 204011142912 60328682 A D B 204011143168 19103216 204145360256 166581506 204145360512 89967292 B 204145360768 36945946 204279578240 90215257 A A A A D B 204279578368 60710275 204279578496 37077411 204279578624 19278617 B 204413795968 90450936 204413796224 37201032 A D B 204413796352 19357895 204548013696 90674254 204548013952 37316753 B 204548014080 19431494 204682231552 61207046 A A D B 204682231680 37424520 204682231808 19499370 204816449408 37524285 B 204816449536 19561481 204950667136 37616001 A D B 204950667264 19617790 205084884992 19668264 205219102592 37775124 B 205219102720 19712871 205353320448 19751585 A A A D B 205487538176 19784382 205621755904 19811243 205755973632 19832152 B 206158626944 7536840 206158627072 1073573 A D B 206561281024 444409 206561281152 443258 206561281280 442111 B 206561281408 440967 206561281536 439827 A A D B 206561281664 438691 206561281792 437558 206561281920 436429 B 206561282048 435304 206561282176 434182 A D B 206561282304 433064 206561282432 431950 206561282560 430839 B 206561282688 429732
noncomputable def AD7 : CTN :=
  A A A A A A A D B 206561282944 427528 206561283072 426431 206561283200 425338 D B 206561283328 424248 206561283456 423162 206561283584 422079 A D B 206561283712 421000 206561283840 419924 206561283968 418852 B 206561284096 417783 206561284224 416718 A A D B 206561284352 415656 206561284480 414597 206561284608 413541 B 206561284736 412489 206561284864 411441 A D B 206561284992 410395 206561285120 409353 206561285248 408315 B 206561285376 407279 206561285504 406247 A A A D B 206561285632 405218 206561285760 404193 206561285888 403170 B 206561286016 402151 206561286144 401135 A D B 206561286272 400123 206561286400 399113 206561286528 398107 B 206561286656 397104 206561286784 396104 A A D B 206561286912 395107 206561287040 394113 206561287168 393122 B 206561287296 392135 206561287424 391151 A D B 206561287680 389191 206561287808 388216 206561287936 387244 B 206561288064 386275 206561288192 385309 A A A A D B 206695498752 5585960 206695498880 5571491 206695499008 5557070 B 206695499136 5542695 206695499264 5528367 A D B 206695499392 5514085 206695499520 5499850 206695499648 5485660 B 206695499776 5471516 206695499904 5457417 A A D B 206695500032 5443364 206695500160 5429356 206695500288 5415393 B 206695500416 5401475 206695500544 5387602 A D B 206695500672 5373773 206695500800 5359988 206695500928 5346248 B 206695501056 5332552 206695501184 5318899 A A A D B 206695501312 5305291 206695501440 5291725 206695501568 5278204 B 206695501696 5264725 206695501824 5251289 A D B 206695501952 5237896 206695502080 5224546 206695502208 5211238 B 206695502336 5197973 206695502464 5184750 A A D B 206695502592 5171569 206695502720 5158430 206695502848 5145332 B 206695502976 5132276 206695503104 5119262 A D B 206695503232 5106288 206695503360 5093356 206695503488 5080465 B 206695503616 5067614 206695503744 5054804 A A A A A D B 206695503872 5042035 206695504000 5029306 206695504128 5016617 D B 206695504256 5003968 206695504384 4991359 206695504512 4978789 A D B 206695504640 4966259 206695504768 4953769 206695504896 4941318 B 206695505152 4916532 206695505536 4879645 A A D B 206695505792 4855246 206695505920 4843103 206829716608 16458132 B 206829716736 16415532 206829716864 16373069 A D B 206829716992 16330744 206829717120 16288555 206829717248 16246503 B 206829717376 16204586 206829717504 16162804 A A A D B 206829717632 16121157 206829717760 16079645 206829717888 16038265 B 206829718016 15997019 206829718144 15955905 A D B 206829718272 15914924 206829718400 15874073 206829718528 15833354 B 206829718656 15792766 206829718784 15752307 A A D B 206829718912 15711978 206829719040 15671778 206829719168 15631706 B 206829719296 15591763 206829719424 15551947 A D B 206829719552 15512258 206829719680 15472695 206829719808 15433259 B 206829719936 15393948 206829720064 15354763 A A A A D B 206829720192 15315702 206829720320 15276765 206829720448 15237952 B 206829720576 15199262 206829720704 15160695 A D B 206829720832 15122250 206829720960 15083927 206829721088 15045725 B 206829721216 15007644 206829721344 14969684 A A D B 206829721472 14931844 206829721600 14894123 206829721728 14856521 B 206829721856 14819038 206829721984 14781673 A D B 206829722112 14744425 206829722240 14707295 206829722368 14670282 B 206829722496 14633385 206829722624 14596605 A A A D B 206829722752 14559939 206829722880 14523389 206829723008 14486953 B 206829723136 14450632 206829723264 14414425 A D B 206829723520 14342349 206829723648 14306480 206963934464 33033199 B 206963934592 32947751 206963934720 32862579 A A D B 206963934848 32777683 206963934976 32693060 206963935104 32608710 B 206963935232 32524633 206963935360 32440826 A D B 206963935488 32357289 206963935616 32274021 206963935744 32191020 B 206963935872 32108287 206963936000 32025819 A A A A A A D B 206963936128 31943615 206963936256 31861675 206963936384 31779998 D B 206963936512 31698583 206963936640 31617428 206963936768 31536533 A D B 206963936896 31455896 206963937024 31375517 206963937152 31295395 B 206963937280 31215528 206963937408 31135917 A A D B 206963937536 31056558 206963937664 30977453 206963937792 30898599 B 206963937920 30819996 206963938048 30741643 A D B 206963938176 30663539 206963938304 30585683 206963938432 30508074 B 206963938560 30430710 206963938688 30353592 A A A D B 206963938816 30276719 206963938944 30200088 206963939072 30123700 B 206963939200 30047553 206963939328 29971647 A D B 206963939456 29895980 206963939584 29820552 206963939712 29745362 B 206963939840 29670409 206963939968 29595692 A A D B 206963940096 29521210 206963940224 29446962 206963940352 29372947 B 206963940480 29299165 206963940608 29225615 A D B 206963940736 29152295 206963940864 29079205 206963940992 29006344 B 206963941248 28861305 206963941376 28789126 A A A A D B 207098152192 55422303 207098152320 55278940 207098152448 55136041 B 207098152576 54993603 207098152704 54851626 A D B 207098152832 54710106 207098152960 54569042 207098153088 54428433 B 207098153216 54288277 207098153344 54148572 A A D B 207098153472 54009316 207098153600 53870507 207098153728 53732144 B 207098153856 53594225 207098153984 53456749 A D B 207098154112 53319713 207098154240 53183116 207098154368 53046957 B 207098154496 52911233 207098154624 52775943 A A A D B 207098154752 52641085 207098154880 52506657 207098155008 52372659 B 207098155136 52239088 207098155264 52105943 A D B 207098155392 51973221 207098155520 51840923 207098155648 51709045 B 207098155776 51577586 207098155904 51446544 A A D B 207098156032 51315919 207098156160 51185708 207098156288 51055910 B 207098156416 50926524 207098156544 50797547 A D B 207098156672 50668978 207098156800 50540816 207098156928 50413058 B 207098157056 50285705 207098157184 50158753 A A A A A D B 207098157312 50032202 207098157440 49906050 207098157568 49780295 D B 207098157696 49654936 207098157824 49529972 207098157952 49405401 A D B 207098158080 49281221 207098158208 49157431 207098158336 49034030 B 207098158464 48911016 207098158592 48788387 A A D B 207098158720 48666143 207098158848 48544281 207098158976 48422801 B 207098159104 48301700 207232370048 83375355 A D B 207232370176 83159825 207232370304 82944991 207232370432 82730851 B 207232370560 82517401 207232370688 82304640 A A A D B 207232370816 82092564 207232370944 81881171 207232371072 81670458 B 207232371200 81460423 207232371328 81251062 A D B 207232371456 81042374 207232371584 80834356 207232371712 80627005 B 207232371840 80420319 207232371968 80214294 A A D B 207232372096 80008929 207232372224 79804221 207232372352 79600168 B 207232372480 79396766 207232372608 79194014 A D B 207232372736 78991909 207232372864 78790449 207232372992 78589630 B 207232373120 78389451 207232373248 78189909 A A A A D B 207232373376 77991002 207232373504 77792727 207232373632 77595082 B 207232373760 77398064 207232373888 77201672 A D B 207232374016 77005902 207232374144 76810752 207232374272 76616220 B 207232374400 76422304 207232374528 76229002 A A D B 207232374656 76036310 207232374784 75844227 207232374912 75652750 B 207232375040 75461877 207232375168 75271606 A D B 207232375296 75081935 207232375424 74892860 207232375552 74704381 B 207232375808 74329198 207232375936 74142490 A A A D B 207232376064 73956368 207232376448 73401496 207232376576 73217696 B 207232376704 73034472 207232376832 72851820 A D B 207366587904 116939140 207366588032 116637041 207366588160 116335918 B 207366588288 116035765 207366588416 115736581 A A D B 207366588544 115438360 207366588672 115141100 207366588800 114844796 B 207366588928 114549445 207366589056 114255043 A D B 207366589184 113961586 207366589312 113669072 207366589440 113377495 B 207366589568 113086853
noncomputable def AD8 : CTN :=
  A A A A A A A D B 207366589824 112508359 207366589952 112220499 207366590080 111933559 D B 207366590208 111647537 207366590336 111362427 207366590464 111078227 A D B 207366590592 110794934 207366590720 110512543 207366590848 110231052 B 207366590976 109950457 207366591104 109670754 A A D B 207366591232 109391940 207366591360 109114012 207366591488 108836966 B 207366591616 108560799 207366591744 108285508 A D B 207366591872 108011089 207366592000 107737540 207366592128 107464855 B 207366592256 107193034 207366592384 106922071 A A A D B 207366592512 106651964 207366592640 106382710 207366592768 106114305 B 207366592896 105846746 207366593024 105580031 A D B 207366593152 105314155 207366593280 105049115 207366593408 104784910 B 207366593536 104521534 207366593664 104258986 A A D B 207366593792 103997262 207366593920 103736358 207366594048 103476273 B 207366594176 103217002 207366594304 102958543 A D B 207366594560 102444049 207500805760 156071461 207500805888 155668529 B 207500806016 155266897 207500806144 154866559 A A A A D B 207500806272 154467512 207500806400 154069749 207500806528 153673267 B 207500806656 153278059 207500806784 152884121 A D B 207500806912 152491448 207500807040 152100035 207500807168 151709878 B 207500807296 151320972 207500807424 150933311 A A D B 207500807552 150546891 207500807680 150161707 207500807808 149777755 B 207500807936 149395029 207500808064 149013525 A D B 207500808192 148633239 207500808320 148254166 207500808448 147876300 B 207500808576 147499638 207500808704 147124175 A A A D B 207500808832 146749906 207500808960 146376826 207500809088 146004932 B 207500809216 145634218 207500809344 145264681 A D B 207500809472 144896315 207500809600 144529117 207500809728 144163081 B 207500809856 143798203 207500809984 143434480 A A D B 207500810112 143071906 207500810240 142710477 207500810368 142350190 B 207500810496 141991038 207500810624 141633020 A D B 207500810752 141276129 207500810880 140920361 207500811008 140565714 B 207500811136 140212181 207500811264 139859760 A A A A A D B 207500811392 139508445 207500811520 139158233 207500811648 138809119 D B 207500811776 138461100 207500811904 138114172 207500812032 137768329 A D B 207500812160 137423569 207500812288 137079886 207635023488 201246458 B 207635023616 200726897 207635023744 200209013 A A D B 207635023872 199692797 207635024000 199178245 207635024128 198665350 B 207635024256 198154105 207635024384 197644504 A D B 207635024512 197136540 207635024640 196630208 207635024768 196125501 B 207635024896 195622412 207635025024 195120936 A A A D B 207635025152 194621067 207635025280 194122797 207635025408 193626122 B 207635025536 193131034 207635025664 192637528 A D B 207635025792 192145598 207635025920 191655238 207635026048 191166441 B 207635026176 190679202 207635026304 190193515 A A D B 207635026432 189709374 207635026560 189226772 207635026688 188745705 B 207635026816 188266165 207635026944 187788149 A D B 207635027072 187311648 207635027200 186836659 207635027328 186363174 B 207635027456 185891189 207635027584 185420698 A A A A D B 207635027712 184951694 207635027840 184484173 207635027968 184018129 B 207635028096 183553555 207635028224 183090448 A D B 207635028352 182628800 207635028480 182168606 207635028736 181252561 B 207635028992 180342268 207635029120 179889265 A A D B 207635029248 179437684 207635029376 178987520 207635029504 178538766 B 207635029632 178091419 207635029760 177645472 A D B 207635029888 177200920 207635030016 176757759 207769241344 251505738 B 207769241472 250856842 207769241600 250210037 A A A D B 207769241728 249565316 207769241856 248922671 207769241984 248282094 B 207769242112 247643577 207769242240 247007111 A D B 207769242368 246372690 207769242496 245740304 207769242624 245109947 B 207769242752 244481611 207769242880 243855286 A A D B 207769243008 243230967 207769243136 242608646 207769243264 241988313 B 207769243392 241369963 207769243520 240753587 A D B 207769243648 240139178 207769243776 239526728 207769243904 238916230 B 207769244032 238307676 207769244160 237701059 A A A A A A D B 207769244288 237096371 207769244416 236493606 207769244544 235892755 D B 207769244672 235293812 207769244800 234696769 207769244928 234101620 A D B 207769245056 233508356 207769245184 232916970 207769245312 232327456 B 207769245440 231739807 207769245568 231154014 A A D B 207769245696 230570072 207769245824 229987974 207769245952 229407711 B 207769246080 228829278 207769246208 228252668 A D B 207769246336 227677873 207769246464 227104886 207769246592 226533702 B 207769246720 225964312 207769246848 225396711 A A A D B 207769246976 224830891 207769247104 224266846 207769247232 223704570 B 207769247360 223144055 207769247488 222585294 A D B 207769247616 222028282 207769247744 221473012 207903459200 307201618 B 207903459328 306409535 207903459456 305620004 A A D B 207903459584 304833015 207903459712 304048558 207903459840 303266624 B 207903459968 302487202 207903460096 301710284 A D B 207903460224 300935859 207903460352 300163918 207903460480 299394451 B 207903460608 298627449 207903460736 297862902 A A A A D B 207903460864 297100800 207903460992 296341136 207903461120 295583898 B 207903461248 294829078 207903461376 294076667 A D B 207903461504 293326655 207903461632 292579034 207903461760 291833793 B 207903461888 291090924 207903462016 290350418 A A D B 207903462144 289612266 207903462272 288876459 207903462400 288142988 B 207903462528 287411843 207903462656 286683017 A D B 207903462784 285956501 207903462912 285232285 207903463040 284510360 B 207903463168 283790719 207903463296 283073353 A A A D B 207903463424 282358252 207903463552 281645409 207903463680 280934814 B 207903463808 280226459 207903463936 279520337 A D B 207903464064 278816437 207903464192 278114753 207903464320 277415275 B 207903464448 276717995 207903464576 276022906 A A D B 207903464704 275329997 207903464832 274639263 207903464960 273950694 B 207903465216 272580019 207903465344 271897897 A D B 207903465472 271217907 208037677184 367330108 208037677312 366384212 B 208037677440 365441360 208037677568 364501539 A A A A A D B 208037677696 363564738 208037677824 362630946 208037677952 361700151 B 208037678080 360772341 208037678208 359847505 A D B 208037678336 358925632 208037678464 358006709 208037678592 357090726 B 208037678720 356177672 208037678848 355267534 A A D B 208037678976 354360303 208037679104 353455967 208037679232 352554514 B 208037679360 351655934 208037679488 350760216 A D B 208037679616 349867349 208037679744 348977322 208037679872 348090124 B 208037680000 347205744 208037680128 346324172 A A A D B 208037680256 345445397 208037680384 344569408 208037680512 343696195 B 208037680640 342825746 208037680768 341958053 A D B 208037680896 341093103 208037681024 340230888 208037681152 339371396 B 208037681280 338514616 208037681408 337660540 A A D B 208037681536 336809156 208037681664 335960455 208037681792 335114426 B 208037681920 334271059 208037682048 333430344 A D B 208037682176 332592271 208037682304 331756830 208037682432 330924012 B 208037682560 330093806 208037682688 329266202 A A A A D B 208037682816 328441191 208037683072 326798909 208037683200 325981618 B 208171895040 433560621 208171895168 432444897 A D B 208171895296 431332761 208171895424 430224198 208171895552 429119196 B 208171895680 428017739 208171895808 426919816 A A D B 208171895936 425825412 208171896064 424734513 208171896192 423647106 B 208171896320 422563178 208171896448 421482715 A D B 208171896576 420405705 208171896704 419332133 208171896832 418261987 B 208171896960 417195253 208171897088 416131919 A A A D B 208171897216 415071972 208171897344 414015398 208171897472 412962184 B 208171897600 411912319 208171897728 410865788 A D B 208171897856 409822580 208171897984 408782682 208171898112 407746081 B 208171898240 406712764 208171898368 405682720 A A D B 208171898496 404655935 208171898624 403632397 208171898752 402612095 B 208171898880 401595015 208171899008 400581146 A D B 208171899136 399570475 208171899264 398562990 208171899392 397558679 B 208171899520 396557531
noncomputable def AD9 : CTN :=
  A A A A A A A D B 208171899776 394564673 208171899904 393572940 208171900032 392584322 D B 208171900160 391598806 208171900288 390616382 208171900416 389637038 A D B 208171900544 388660761 208171900800 386717367 208171900928 385750226 B 208306112896 505040107 208306113024 503741274 A A D B 208306113152 502446616 208306113280 501156115 208306113408 499869755 B 208306113536 498587522 208306113664 497309398 A D B 208306113792 496035368 208306113920 494765417 208306114048 493499528 B 208306114176 492237687 208306114304 490979877 A A A D B 208306114432 489726083 208306114560 488476289 208306114688 487230481 B 208306114816 485988644 208306114944 484750761 A D B 208306115072 483516818 208306115200 482286800 208306115328 481060692 B 208306115456 479838479 208306115584 478620146 A A D B 208306115712 477405678 208306115840 476195061 208306115968 474988280 B 208306116096 473785320 208306116224 472586168 A D B 208306116352 471390807 208306116480 470199225 208306116608 469011406 B 208306116736 467827337 208306116864 466647003 A A A A D B 208306116992 465470390 208306117120 464297485 208306117248 463128272 B 208306117376 461962738 208306117504 460800870 A D B 208306117632 459642653 208306117760 458488074 208306117888 457337118 B 208306118016 456189773 208306118272 453905859 A A D B 208306118400 452769263 208306118528 451636224 208306118656 450506728 B 208440330752 581704615 208440330880 580209584 A D B 208440331008 578719354 208440331136 577233906 208440331264 575753223 B 208440331392 574277286 208440331520 572806076 A A A D B 208440331648 571339576 208440331776 569877768 208440331904 568420633 B 208440332032 566968153 208440332160 565520311 A D B 208440332288 564077089 208440332416 562638469 208440332544 561204434 B 208440332672 559774966 208440332800 558350048 A A D B 208440332928 556929662 208440333056 555513790 208440333184 554102417 B 208440333312 552695524 208440333440 551293095 A D B 208440333568 549895112 208440333696 548501559 208440333824 547112419 B 208440333952 545727675 208440334080 544347311 A A A A A D B 208440334208 542971309 208440334336 541599653 208440334464 540232327 D B 208440334592 538869315 208440334720 537510599 208440334848 536156164 A D B 208440334976 534805994 208440335104 533460073 208440335232 532118383 B 208440335360 530780911 208440335488 529447639 A A D B 208440335616 528118552 208440335744 526793633 208440335872 525472868 B 208440336000 524156241 208440336128 522843736 A D B 208440336256 521535338 208440336384 520231031 208574548608 663487257 B 208574548736 661783134 208574548864 660084480 A A A D B 208574548992 658391274 208574549120 656703495 208574549248 655021122 B 208574549376 653344135 208574549504 651672512 A D B 208574549632 650006234 208574549760 648345280 208574549888 646689628 B 208574550016 645039260 208574550144 643394155 A A D B 208574550272 641754292 208574550400 640119652 208574550528 638490215 B 208574550656 636865960 208574550784 635246868 A D B 208574550912 633632920 208574551040 632024096 208574551168 630420375 B 208574551296 628821740 208574551424 627228170 A A A A D B 208574551552 625639646 208574551680 624056149 208574551808 622477660 B 208574551936 620904160 208574552064 619335630 A D B 208574552192 617772052 208574552320 616213406 208574552448 614659673 B 208574552576 613110836 208574552704 611566875 A A D B 208574552960 608493511 208574553088 606964071 208574553344 603919582 B 208574553472 602404498 208574553600 600894163 A D B 208574553728 599388560 208574553856 597887671 208574553984 596391478 B 208574554112 594899963 208708766464 750318256 A A A D B 208708766592 748392352 208708766720 746472624 208708766848 744559049 B 208708766976 742651604 208708767104 740750265 A D B 208708767232 738855009 208708767360 736965811 208708767488 735082650 B 208708767616 733205501 208708767744 731334342 A A D B 208708767872 729469150 208708768000 727609902 208708768128 725756576 B 208708768256 723909148 208708768384 722067596 A D B 208708768512 720231898 208708768640 718402031 208708768768 716577974 B 208708768896 714759704 208708769024 712947198 A A A A A A D B 208708769152 711140436 208708769280 709339395 208708769408 707544054 D B 208708769536 705754391 208708769664 703970384 208708769792 702192012 A D B 208708769920 700419253 208708770048 698652087 208708770176 696890493 B 208708770304 695134448 208708770432 693383932 A A D B 208708770560 691638925 208708770688 689899405 208708770816 688165352 B 208708770944 686436745 208708771072 684713563 A D B 208708771200 682995787 208708771328 681283396 208708771456 679576369 B 208708771584 677874687 208708771712 676178329 A A A D B 208708771840 674487275 208842984320 842124994 208842984448 839964830 B 208842984576 837811589 208842984704 835665245 A D B 208842984832 833525772 208842984960 831393144 208842985088 829267333 B 208842985216 827148315 208842985344 825036062 A A D B 208842985472 822930549 208842985600 820831751 208842985728 818739641 B 208842985856 816654193 208842985984 814575384 A D B 208842986112 812503186 208842986240 810437576 208842986368 808378527 B 208842986496 806326015 208842986624 804280014 A A A A D B 208842986752 802240501 208842986880 800207451 208842987008 798180838 B 208842987136 796160639 208842987264 794146828 A D B 208842987392 792139383 208842987520 790138278 208842987648 788143490 B 208842987776 786154995 208842987904 784172768 A A D B 208842988032 782196787 208842988160 780227027 208842988288 778263466 B 208842988416 776306079 208842988544 774354844 A D B 208842988672 772409737 208842988800 770470735 208842988928 768537816 B 208842989056 766610955 208842989184 764690132 A A A D B 208842989312 762775322 208842989440 760866503 208842989568 758963653 B 208977202304 936425378 208977202432 934026401 A D B 208977202560 931635103 208977202688 929251456 208977202816 926875429 B 208977202944 924506993 208977203072 922146120 A A D B 208977203200 919792780 208977203328 917446945 208977203456 915108585 B 208977203584 912777672 208977203712 910454178 A D B 208977203840 908138075 208977203968 905829333 208977204096 903527926 B 208977204224 901233825 208977204352 898947003 A A A A A D B 208977204480 896667431 208977204608 894395082 208977204736 892129929 D B 208977204864 889871944 208977204992 887621100 208977205120 885377370 A D B 208977205248 883140727 208977205376 880911144 208977205504 878688595 B 208977205632 876473053 208977205760 874264491 A A D B 208977205888 872062882 208977206016 869868202 208977206144 867680423 B 208977206272 865499519 208977206400 863325466 A D B 208977206528 861158236 208977206656 858997803 208977206784 856844144 B 208977207040 852557041 208977207168 850423546 A A A D B 208977207296 848296723 209111420160 1037696075 209111420288 1035039363 B 209111420416 1032391149 209111420544 1029751401 A D B 209111420672 1027120088 209111420800 1024497176 209111420928 1021882633 B 209111421056 1019276428 209111421184 1016678529 A A D B 209111421312 1014088903 209111421440 1011507519 209111421568 1008934346 B 209111421696 1006369352 209111421824 1003812507 A D B 209111421952 1001263779 209111422080 998723136 209111422208 996190550 B 209111422336 993665988 209111422464 991149420 A A A A D B 209111422592 988640816 209111422720 986140146 209111422848 983647380 B 209111422976 981162487 209111423104 978685438 A D B 209111423232 976216203 209111423360 973754753 209111423488 971301057 B 209111423616 968855088 209111423744 966416815 A A D B 209111423872 963986209 209111424000 961563243 209111424128 959147886 B 209111424256 956740110 209111424384 954339887 A D B 209111424512 951947188 209111424640 949561984 209111424768 947184249 B 209111424896 944813953 209111425024 942451069 A A A D B 209245638016 1143696325 209245638144 1140770105 209245638272 1137853241 B 209245638400 1134945696 209245638528 1132047434 A D B 209245638656 1129158421 209245638784 1126278620 209245638912 1123407997 B 209245639040 1120546515 209245639168 1117694142 A A D B 209245639296 1114850841 209245639424 1112016578 209245639552 1109191318 B 209245639680 1106375028 209245639808 1103567673 A D B 209245639936 1100769219 209245640064 1097979632 209245640192 1095198878 B 209245640320 1092426925
noncomputable def AEA : CTN :=
  A A A A A A A D B 209245640576 1086909285 209245640704 1084163531 209245640832 1081426445 D B 209245640960 1078697993 209245641088 1075978143 209245641216 1073266863 A D B 209245641344 1070564119 209245641472 1067869879 209245641600 1065184112 B 209245641728 1062506786 209245641856 1059837868 A A D B 209245641984 1057177328 209245642112 1054525132 209245642240 1051881251 B 209245642368 1049245653 209245642496 1046618306 A D B 209245642624 1043999180 209245642752 1041388244 209379856000 1251135644 B 209379856128 1247938630 209379856256 1244751823 A A A D B 209379856384 1241575185 209379856512 1238408677 209379856640 1235252260 B 209379856768 1232105896 209379856896 1228969545 A D B 209379857024 1225843171 209379857152 1222726734 209379857280 1219620198 B 209379857408 1216523523 209379857536 1213436673 A A D B 209379857664 1210359611 209379857792 1207292298 209379857920 1204234698 B 209379858048 1201186775 209379858176 1198148491 A D B 209379858304 1195119809 209379858432 1192100694 209379858560 1189091109 B 209379858688 1186091018 209379858816 1183100385 A A A A D B 209379858944 1180119175 209379859072 1177147351 209379859200 1174184879 B 209379859328 1171231722 209379859456 1168287846 A D B 209379859584 1165353217 209379859712 1162427798 209379859840 1159511555 B 209379860096 1153706461 209379860224 1150817541 A A D B 209379860352 1147937660 209379860480 1145066785 209514073984 1362562012 B 209514074240 1355618516 209514074368 1352163358 A D B 209514074496 1348719205 209514074624 1345286013 209514074752 1341863741 B 209514074880 1338452348 209514075008 1335051791 A A A D B 209514075136 1331662030 209514075264 1328283024 209514075392 1324914731 B 209514075520 1321557111 209514075648 1318210123 A D B 209514075776 1314873727 209514075904 1311547883 209514076032 1308232551 B 209514076160 1304927690 209514076288 1301633261 A A D B 209514076416 1298349225 209514076544 1295075542 209514076672 1291812173 B 209514076800 1288559080 209514076928 1285316223 A D B 209514077056 1282083563 209514077184 1278861063 209514077312 1275648683 B 209514077440 1272446387 209514077568 1269254135 A A A A A D B 209514077696 1266071890 209514077824 1262899615 209514078080 1256584822 D B 209514078208 1253442231 209648292096 1474090118 209648292224 1470335399 A D B 209648292352 1466592631 209648292480 1462861767 209648292608 1459142763 B 209648292736 1455435573 209648292864 1451740152 A A D B 209648292992 1448056455 209648293120 1444384438 209648293248 1440724056 B 209648293376 1437075265 209648293504 1433438020 A D B 209648293632 1429812279 209648293760 1426197998 209648293888 1422595132 B 209648294016 1419003640 209648294144 1415423477 A A A D B 209648294272 1411854601 209648294400 1408296969 209648294528 1404750538 B 209648294656 1401215267 209648294784 1397691114 A D B 209648294912 1394178035 209648295040 1390675990 209648295168 1387184938 B 209648295296 1383704835 209648295424 1380235642 A A D B 209648295552 1376777318 209648295680 1373329821 209648295936 1366467147 B 209782509952 1596900256 209782510464 1580717869 A D B 209782510720 1572703564 209782510848 1568715464 209782510976 1564740000 B 209782511104 1560777125 209782511232 1556826791 A A A A D B 209782511360 1552888950 209782511488 1548963556 209782511616 1545050559 B 209782511744 1541149915 209782511872 1537261575 A D B 209782512000 1533385494 209782512128 1529521625 209782512256 1525669922 B 209782512384 1521830339 209782512512 1518002830 A A D B 209782512640 1514187350 209782512768 1510383853 209782512896 1506592294 B 209782513024 1502812628 209782513152 1499044811 A D B 209782513408 1491544544 209782513536 1487812005 209782513664 1484091138 B 209916728576 1697851444 209916728960 1684984101 A A A D B 209916729088 1680722099 209916729216 1676473567 209916729344 1672238455 B 209916729472 1668016711 209916729600 1663808285 A D B 209916729728 1659613126 209916729856 1655431185 209916729984 1651262412 B 209916730112 1647106756 209916730240 1642964168 A A D B 209916730368 1638834599 209916730496 1634717999 209916730624 1630614321 B 209916730752 1626523515 209916730880 1622445533 A D B 209916731008 1618380326 209916731136 1614327847 209916731392 1606260880 B 210050946688 1817850960 210050946816 1813252884 A A A A A A D B 210050946944 1808669341 210050947072 1804100275 210050947200 1799545632 D B 210050947328 1795005357 210050947584 1785967694 210050947712 1781470198 A D B 210050947840 1776986855 210050947968 1772517609 210050948096 1768062409 B 210050948224 1763621202 210050948352 1759193934 A A D B 210050948480 1754780554 210050948736 1745995246 210050948864 1741623214 B 210050948992 1737264863 210050949120 1732920140 A D B 210185164544 1950419454 210185164672 1945489181 210185164800 1940574481 B 210185165056 1930791562 210185165440 1916232514 A A A D B 210185165568 1911410019 210185165696 1906602690 210185165824 1901810469 B 210185165952 1897033299 210185166080 1892271123 A D B 210185166208 1887523885 210185166336 1882791529 210185166464 1878073998 B 210185166592 1873371237 210185166848 1864009804 A A D B 210319382784 2071102715 210319383296 2050312710 210319383424 2045156032 B 210319383808 2029782986 210319383936 2024690765 A D B 210319384064 2019614506 210319384192 2014554151 210319384448 2004480911 B 210319384576 1999467908 210453600768 2204715030 A A A A D B 210453601920 2155370432 210453602304 2139229668 210587819520 2306233267 B 210587819648 2300454759 210587819904 2288951949 A D B 210587820032 2283227512 210722036608 2486948742 210722037120 2462062587 B 210722037760 2431391112 210856255488 2583647426 A A D B 210990473216 2739920731 211124690944 2900132663 211258908672 3064202262 B 211393126400 3232046011 211527344128 3403577882 A D B 211661561856 3578709384 211795779584 3757349609 211929997312 3939405282 B 212064215040 4124780812 212198432768 4313378347 A A A D B 212332650496 4505097824 212466868224 4699837030 212601085952 4897491654 B 212735303680 5097955349 213003739136 5506874740 A D B 213272174592 5925706003 213406392320 6138552830 213540610048 6353531323 B 213943263232 7010060751 214077480960 7232362537 A A D B 214614351872 8135535550 214748569728 8343278283 214748569856 8322438682 B 214748569984 8301664123 214748570112 8280954363 A D B 214748570240 8260309158 214748570368 8239728268 214748570496 8219211452 B 214748570624 8198758471 214748570752 8178369086 A A A A A D B 214748570880 8158043061 214748571008 8137780160 214748571136 8117580146 B 214748571264 8097442786 214748571392 8077367847 A D B 214748571520 8057355097 214748571648 8037404305 214748571776 8017515240 B 214748571904 7997687674 214748572032 7977921378 A A D B 214748572160 7958216125 214748572288 7938571689 214748572416 7918987845 B 214748572544 7899464369 214748572672 7880001038 A D B 214748572800 7860597628 214748572928 7841253920 214748573056 7821969692 B 214748573184 7802744726 214748573312 7783578802 A A A D B 214748573440 7764471704 214748573568 7745423214 214748573696 7726433117 B 214748573824 7707501199 214748573952 7688627245 A D B 214748574080 7669811042 214748574208 7651052380 214748574336 7632351046 B 214748574464 7613706830 214748574592 7595119523 A A D B 214748574720 7576588917 214748574848 7558114805 214748574976 7539696979 B 214748575104 7521335234 214748575232 7503029365 A D B 214748575360 7484779168 214748575488 7466584440 214748575616 7448444979 B 214748575744 7430360584 214748575872 7412331053 A A A A D B 214748576000 7394356188 214748576128 7376435789 214748576256 7358569658 B 214748576384 7340757599 214748576512 7322999415 A D B 214748576640 7305294910 214748576768 7287643890 214748576896 7270046162 B 214748577024 7252501531 214748577152 7235009806 A A D B 214748577280 7217570796 214748577408 7200184310 214748577536 7182850157 B 214748577664 7165568150 214748577792 7148338100 A D B 215017013248 7541312377 215285447552 8110669363 216493408256 9716154863 B 217969803264 11802790825 218238238720 12160886856 A A A D B 218372456448 12336706725 218640891904 12681357700 218775109632 12849979292 B 221862117376 15820891566 221996335104 15902427809 A D B 222398988288 16119631016 223338512512 16418769270 223338512640 16371937440 B 223338512768 16320343345 223338512896 16264029169 A A D B 223338513024 16203039755 223338513152 16137422570 223338513280 16067227664 B 223338513408 15992507623 223338513536 15913317533 A D B 223338513664 15829714926 223338513792 15741759742 223338513920 15649514276 B 223338514048 15553043132
noncomputable def AEB : CTN :=
  A A A A A A A D B 223338514304 15347693469 223338514432 15238955248 223338514560 15126271841 D B 223338514688 15009718625 223338514816 14889372976 223338514944 14765314206 A D B 223338515072 14637623509 223338515200 14506383906 223338515328 14371680180 B 223338515456 14233598825 223338515584 14092227980 A A D B 223338515712 13947657371 223338515840 13799978251 223338515968 13649283334 B 223338516096 13495666739 223338516224 13339223920 A D B 223338516352 13180051607 223338516480 13018247744 223338516608 12853911416 B 223338516736 12687142798 223338516864 12518043076 A A A D B 223338516992 12346714390 223338517120 12173259767 223338517248 11997783053 B 223338517376 11820388852 223338517504 11641182452 A D B 223338517632 11460269768 223338517760 11277757267 223338518016 10908361077 B 223338518144 10721692510 223338518272 10533854239 A A D B 223338518400 10344954523 223338518528 10155101777 223338518784 9772971268 B 223338519040 9388330754 223338519168 9195340124 A D B 223338519424 8808558093 223338519680 8421424628 223338519808 8227993137 B 223338519936 8034793215 223338520064 7841930177 A A A A D B 223338520320 7457632652 223338520576 7075928778 223875391488 7139146060 B 224546479360 8388653393 224814915584 7250239755 A D B 224949133312 7266140465 225217568768 7297953168 225351786496 7313862874 B 225754439680 7361591648 226022875136 7393399027 A A D B 226291310592 7425186183 226559746048 7456943857 227499270144 7567729581 B 228170358784 7646351236 228438794240 7677642902 A D B 228573011968 7693250493 228841447424 7724383466 229244100608 7770860326 B 229512536064 7801683290 230317842432 7893277917 A A A D B 230452060160 7908404574 230854713344 7953524245 231123148800 7983376368 B 231257366528 7998230943 231391584256 8013036458 A D B 231525801984 8027791871 231660019712 8042496146 231794237440 8057148254 B 231928455296 7860878833 231928455424 7651001355 A A D B 231928455680 7234651425 231928455808 7028392262 231928455936 6823550428 B 231928456192 6418531221 231928456320 6218556595 A D B 231928456448 6020404688 231928456704 5629958027 231928456832 5437853764 B 231928457088 5060347058 231928457216 4875124875 A A A A A D B 231928457600 4334626354 231928457728 4159794995 231928457856 3987765561 D B 231928458112 3652421196 231928458368 3329189908 231928458624 3018634276 A D B 231928458752 2868276071 231928459264 2301074089 231928459392 2168115445 B 231928459648 1913173302 231928459776 1791284529 A A D B 231928460160 1448464874 231928460416 1239339599 231928460544 1140705033 B 231928460672 1046061931 231928460800 955436740 A D B 231928460928 868853408 231928461056 786333379 231928461184 707895599 B 231928461312 633556508 231928461440 563330048 A A A D B 231928461696 435258306 231928462080 274200677 231928462208 228803353 B 231928462464 150424905 231928462592 117429720 A D B 231928462720 88550508 231928462848 63774241 231928462976 43085526 B 231928463232 13897474 231928463360 5355706 A A D B 232062678784 788784022 232062679552 378925558 232062681088 5487141 B 232196898048 118871492 232196898176 89770655 A D B 232196898816 5618498 232465333248 191347138 232867985280 723513996 B 232867985408 648029968 232867987072 45857289 A A A A D B 233002203648 389084038 233002203904 283685127 233136422272 93883500 B 233136422912 6529148 233270638592 653992495 A D B 233270640512 16018234 233404858368 6784141 233807510528 200268720 B 233807510912 96650856 233807511552 7159989 A A D B 234075946752 31121454 234210164608 17400749 234344381568 164419410 B 234612817152 130673180 234612817536 50518961 A D B 234612817920 7880369 234747035008 100249773 234747035264 50845870 B 234747035648 7995524 234881253376 8109089 A A A D B 235015470720 51484412 235015470976 18492753 235149688832 8331177 B 235283906176 52101919 235418123904 52402540 A D B 235418124288 8546097 235552341760 33838503 235552342016 8650706 B 235686559488 34060712 235686559744 8753330 A A D B 235820776832 103917999 235820777216 34278418 235820777344 19480436 B 235820777472 8853908 235954995200 8952379 A D B 236089212544 53820575 236223430400 34903735 236357648384 9234561 B 236491865344 138018870 236491866112 9324023 A A A A A A D B 236626083712 20347916 236760301056 78757358 236760301568 9495723 D B 236894518912 55323542 236894519296 9577858 237028736384 107407127 A D B 237028737024 9657450 237162954624 20852454 237162954752 9734450 B 237297171968 79892391 237297172224 36354416 A A D B 237297172352 20968826 237297172480 9808813 237431389952 36512357 B 237431390208 9880494 237565607936 9949449 A D B 237699825536 21293667 237699825664 10015637 237834042752 109324044 B 237834043136 36953539 237834043392 10079018 A A A D B 237968260608 81130267 237968260736 56962854 237968260864 37089539 B 237968260992 21489517 237968261120 10139553 A D B 238102478592 37219925 238102478720 21581093 238102478848 10197208 B 238236696576 10251945 238370914048 37463664 A A D B 238370914176 21751344 238370914304 10303734 238505131904 21829942 B 238505132032 10352542 238639349632 21904141 A D B 238639349760 10398340 238773567488 10441100 238907785088 22039211 B 238907785216 10480798 239042002944 10517408 A A A A D B 239176220672 10550909 239310438400 10581280 239444656128 10608504 B 239578873856 10632564 239713091584 10653445 A D B 239847309312 10671135 239981527040 10685624 240115744768 10696901 B 240518398080 3268915 240518398208 118725 A A D B 240921052032 1237275 240921052160 1234525 240921052288 1231783 B 240921052416 1229048 240921052544 1226321 A D B 240921052672 1223601 240921052800 1220889 240921052928 1218185 B 240921053056 1215488 240921053184 1212798 A A A D B 240921053312 1210116 240921053440 1207441 240921053568 1204774 B 240921053696 1202114 240921053824 1199461 A D B 240921053952 1196816 240921054080 1194177 240921054208 1191547 B 240921054336 1188923 240921054464 1186307 A A D B 240921054592 1183697 240921054720 1181096 240921054848 1178501 B 240921054976 1175913 240921055104 1173332 A D B 240921055232 1170759 240921055360 1168192 240921055488 1165633 B 240921055616 1163080 240921055744 1160535 A A A A A D B 240921055872 1157996 240921056000 1155465 240921056128 1152940 D B 240921056256 1150422 240921056384 1147911 240921056512 1145407 A D B 240921056640 1142910 240921056768 1140420 240921056896 1137936 B 240921057024 1135459 240921057152 1132989 A A D B 240921057280 1130526 240921057408 1128069 240921057536 1125619 B 240921057664 1123175 240921057792 1120739 A D B 240921057920 1118308 240921058048 1115885 240921058176 1113468 B 240921058304 1111057 240921058432 1108653 A A A D B 240921058816 1101480 240921058944 1099102 240921059072 1096731 B 240921059200 1094365 240921059328 1092006 A D B 241055269888 6583860 241055270016 6569235 241055270144 6554650 B 241055270272 6540105 241055270400 6525601 A A D B 241055270528 6511137 241055270656 6496714 241055270784 6482330 B 241055270912 6467986 241055271040 6453681 A D B 241055271168 6439416 241055271296 6425191 241055271424 6411004 B 241055271552 6396857 241055271680 6382749 A A A A D B 241055271808 6368680 241055271936 6354650 241055272064 6340658 B 241055272192 6326704 241055272320 6312789 A D B 241055272448 6298913 241055272576 6285074 241055272704 6271273 B 241055272832 6257511 241055272960 6243786 A A D B 241055273088 6230098 241055273216 6216448 241055273344 6202836 B 241055273472 6189260 241055273600 6175722 A D B 241055273728 6162221 241055273856 6148757 241055273984 6135329 B 241055274112 6121938 241055274240 6108584 A A A D B 241055274368 6095266 241055274496 6081984 241055274624 6068739 B 241055274752 6055529 241055274880 6042356 A D B 241055275008 6029218 241055275136 6016116 241055275264 6003050 B 241055275392 5990019 241055275520 5977023 A A D B 241055275648 5964063 241055275776 5951137 241055275904 5938247 B 241055276032 5925392 241055276160 5912571 A D B 241055276288 5899785 241055276544 5874317 241055276672 5861634 B 241055276928 5836371
noncomputable def AEC : CTN :=
  A A A A A A A D B 241189487744 16140093 241189487872 16104260 241189488000 16068525 D B 241189488128 16032890 241189488256 15997353 241189488384 15961915 A D B 241189488512 15926575 241189488640 15891332 241189488768 15856187 B 241189488896 15821140 241189489024 15786189 A A D B 241189489152 15751334 241189489280 15716576 241189489408 15681913 B 241189489536 15647347 241189489664 15612875 A D B 241189489792 15578498 241189489920 15544216 241189490048 15510028 B 241189490176 15475934 241189490304 15441933 A A A D B 241189490432 15408026 241189490560 15374212 241189490688 15340491 B 241189490816 15306862 241189490944 15273325 A D B 241189491072 15239880 241189491200 15206527 241189491328 15173265 B 241189491456 15140093 241189491584 15107013 A A D B 241189491712 15074022 241189491840 15041122 241189491968 15008311 B 241189492096 14975590 241189492224 14942958 A D B 241189492352 14910415 241189492480 14877960 241189492608 14845594 B 241189492736 14813316 241189492864 14781125 A A A A D B 241189492992 14749022 241189493120 14717005 241189493248 14685076 B 241189493376 14653233 241189493504 14621477 A D B 241189493632 14589807 241189493760 14558222 241189493888 14526723 B 241189494016 14495308 241189494144 14463979 A A D B 241189494272 14432735 241189494400 14401574 241189494656 14339506 B 241189494784 14308597 241323705600 29886159 A D B 241323705728 29819843 241323705856 29753711 241323705984 29687763 B 241323706112 29621997 241323706240 29556413 A A A D B 241323706368 29491010 241323706496 29425789 241323706624 29360747 B 241323706752 29295886 241323706880 29231203 A D B 241323707008 29166699 241323707136 29102372 241323707264 29038223 B 241323707392 28974251 241323707520 28910455 A A D B 241323707648 28846834 241323707776 28783388 241323707904 28720116 B 241323708032 28657019 241323708160 28594094 A D B 241323708288 28531343 241323708416 28468763 241323708544 28406355 B 241323708672 28344117 241323708800 28282051 A A A A A D B 241323708928 28220154 241323709056 28158426 241323709184 28096867 D B 241323709312 28035476 241323709440 27974253 241323709568 27913196 A D B 241323709696 27852307 241323709824 27791583 241323709952 27731025 B 241323710080 27670631 241323710208 27610402 A A D B 241323710336 27550337 241323710464 27490435 241323710592 27430696 B 241323710720 27371119 241323710848 27311704 A D B 241323710976 27252450 241323711104 27193356 241323711232 27134423 B 241323711360 27075649 241323711488 27017034 A A A D B 241323711616 26958578 241323711872 26842139 241323712000 26784156 B 241323712128 26726329 241323712256 26668658 A D B 241323712384 26611142 241323712512 26553782 241457923456 47799772 B 241457923584 47693766 241457923712 47588054 A A D B 241457923840 47482634 241457923968 47377506 241457924096 47272669 B 241457924224 47168122 241457924352 47063864 A D B 241457924480 46959894 241457924608 46856210 241457924736 46752813 B 241457924864 46649701 241457924992 46546873 A A A A D B 241457925120 46444328 241457925248 46342066 241457925376 46240085 B 241457925504 46138384 241457925632 46036963 A D B 241457925760 45935821 241457925888 45834956 241457926016 45734368 B 241457926144 45634056 241457926272 45534018 A A D B 241457926400 45434255 241457926528 45334765 241457926656 45235547 B 241457926784 45136600 241457926912 45037924 A D B 241457927040 44939517 241457927168 44841379 241457927296 44743509 B 241457927424 44645906 241457927552 44548569 A A A D B 241457927680 44451497 241457927808 44354689 241457927936 44258145 B 241457928064 44161863 241457928192 44065843 A D B 241457928320 43970084 241457928448 43874585 241457928576 43779346 B 241457928704 43684364 241457928832 43589640 A A D B 241457928960 43495173 241457929088 43400961 241457929216 43307005 B 241457929344 43213302 241457929472 43119853 A D B 241457929600 43026657 241457929728 42933712 241457929856 42841018 B 241457929984 42748574 241457930240 42564433 A A A A A A D B 241592141312 69856200 241592141440 69701365 241592141568 69546959 D B 241592141696 69392980 241592141824 69239427 241592141952 69086299 A D B 241592142080 68933594 241592142208 68781311 241592142336 68629448 B 241592142464 68478004 241592142592 68326977 A A D B 241592142720 68176367 241592142848 68026172 241592142976 67876390 B 241592143104 67727020 241592143232 67578061 A D B 241592143360 67429512 241592143488 67281370 241592143616 67133635 B 241592143744 66986305 241592143872 66839380 A A A D B 241592144000 66692857 241592144128 66546735 241592144256 66401014 B 241592144384 66255691 241592144512 66110766 A D B 241592144640 65966237 241592144768 65822102 241592144896 65678361 B 241592145024 65535013 241592145152 65392055 A A D B 241592145280 65249487 241592145408 65107307 241592145536 64965515 B 241592145664 64824108 241592145792 64683086 A D B 241592145920 64542448 241592146048 64402191 241592146176 64262315 B 241592146304 64122819 241592146432 63983702 A A A A D B 241592146560 63844961 241592146688 63706596 241592146816 63568606 B 241592146944 63430990 241592147072 63293746 A D B 241592147200 63156873 241592147328 63020369 241592147456 62884235 B 241592147584 62748468 241592147712 62613067 A A D B 241592147968 62343359 241726359168 96028282 241726359296 95815555 B 241726359424 95603417 241726359552 95391866 A D B 241726359680 95180899 241726359808 94970516 241726359936 94760714 B 241726360064 94551491 241726360192 94342845 A A A D B 241726360320 94134774 241726360448 93927277 241726360576 93720351 B 241726360704 93513995 241726360832 93308207 A D B 241726360960 93102985 241726361088 92898326 241726361216 92694230 B 241726361344 92490694 241726361472 92287717 A A D B 241726361600 92085296 241726361728 91883430 241726361856 91682117 B 241726361984 91481355 241726362112 91281142 A D B 241726362240 91081477 241726362368 90882357 241726362496 90683782 B 241726362624 90485749 241726362752 90288256 A A A A A D B 241726362880 90091302 241726363008 89894884 241726363136 89699002 B 241726363264 89503653 241726363392 89308836 A D B 241726363520 89114548 241726363648 88920789 241726363776 88727556 B 241726363904 88534848 241726364032 88342663 A A D B 241726364160 88150999 241726364288 87959854 241726364416 87769228 B 241726364544 87579118 241726364672 87389522 A D B 241726364800 87200440 241726364928 87011868 241726365056 86823806 B 241726365184 86636252 241726365312 86449204 A A A D B 241726365440 86262661 241726365568 86076621 241726365696 85891082 B 241860577024 126286450 241860577152 126006849 A D B 241860577280 125728020 241860577408 125449963 241860577536 125172675 B 241860577664 124896152 241860577792 124620392 A A D B 241860577920 124345394 241860578048 124071153 241860578176 123797669 B 241860578304 123524937 241860578432 123252957 A D B 241860578560 122981724 241860578688 122711238 241860578816 122441495 B 241860578944 122172493 241860579072 121904229 A A A A D B 241860579200 121636702 241860579328 121369908 241860579456 121103845 B 241860579584 120838511 241860579712 120573903 A D B 241860579840 120310020 241860579968 120046858 241860580096 119784416 B 241860580224 119522690 241860580352 119261679 A A D B 241860580480 119001380 241860580608 118741791 241860580736 118482910 B 241860580864 118224734 241860580992 117967261 A D B 241860581120 117710488 241860581248 117454414 241860581376 117199036 B 241860581504 116944352 241860581632 116690360 A A A D B 241860581760 116437057 241860581888 116184441 241860582016 115932509 B 241860582144 115681261 241860582272 115430692 A D B 241860582400 115180802 241860582528 114931588 241860582656 114683048 B 241860582784 114435179 241860582912 114187980 A A D B 241860583040 113941448 241860583168 113695581 241860583296 113450377 B 241860583424 113205834 241994795008 160243379 A D B 241994795136 159888988 241994795264 159535577 241994795392 159183142 B 241994795520 158831680
noncomputable def AED : CTN :=
  A A A A A A A D B 241994795776 158131662 241994795904 157783099 241994796032 157435496 D B 241994796160 157088851 241994796288 156743159 241994796416 156398417 A D B 241994796544 156054623 241994796672 155711773 241994796800 155369865 B 241994796928 155028895 241994797056 154688859 A A D B 241994797184 154349756 241994797312 154011581 241994797440 153674333 B 241994797568 153338007 241994797696 153002601 A D B 241994797824 152668112 241994797952 152334536 241994798080 152001871 B 241994798208 151670114 241994798336 151339262 A A A D B 241994798464 151009311 241994798592 150680260 241994798720 150352104 B 241994798848 150024842 241994798976 149698469 A D B 241994799104 149372984 241994799232 149048383 241994799360 148724663 B 241994799488 148401822 241994799616 148079857 A A D B 241994799744 147758765 241994799872 147438542 241994800000 147119187 B 241994800128 146800696 241994800256 146483067 A D B 241994800384 146166296 241994800512 145850382 241994800640 145535320 B 241994800768 145221109 241994800896 144907746 A A A A D B 241994801024 144595228 241994801152 144283552 242129012992 198052191 B 242129013120 197614667 242129013248 197178352 A D B 242129013376 196743240 242129013504 196309328 242129013632 195876612 B 242129013760 195445088 242129013888 195014752 A A D B 242129014016 194585599 242129014144 194157627 242129014272 193730831 B 242129014400 193305207 242129014528 192880752 A D B 242129014656 192457461 242129014784 192035331 242129014912 191614359 B 242129015040 191194539 242129015168 190775868 A A A D B 242129015296 190358343 242129015424 189941960 242129015552 189526715 B 242129015680 189112605 242129015808 188699625 A D B 242129015936 188287772 242129016064 187877042 242129016192 187467432 B 242129016320 187058937 242129016448 186651555 A A D B 242129016576 186245282 242129016704 185840113 242129016832 185436046 B 242129016960 185033077 242129017088 184631202 A D B 242129017216 184230418 242129017344 183830721 242129017472 183432107 B 242129017600 183034573 242129017728 182638116 A A A A A D B 242129017856 182242732 242129017984 181848418 242129018112 181455169 D B 242129018240 181062984 242129018368 180671857 242129018624 179892768 A D B 242129018752 179504798 242129018880 179117874 242263230848 240181174 B 242263230976 239650876 242263231104 239122040 A A D B 242263231232 238594663 242263231360 238068739 242263231488 237544264 B 242263231616 237021232 242263231744 236499640 A D B 242263231872 235979482 242263232000 235460753 242263232128 234943450 B 242263232256 234427566 242263232384 233913098 A A A D B 242263232512 233400041 242263232640 232888389 242263232768 232378140 B 242263232896 231869287 242263233024 231361827 A D B 242263233152 230855754 242263233280 230351065 242263233408 229847754 B 242263233536 229345818 242263233664 228845251 A A D B 242263233792 228346049 242263233920 227848208 242263234048 227351723 B 242263234176 226856591 242263234304 226362805 A D B 242263234432 225870363 242263234560 225379259 242263234688 224889490 B 242263234816 224401050 242263234944 223913936 A A A A D B 242263235072 223428144 242263235200 222943668 242263235328 222460505 B 242263235456 221978651 242263235584 221498100 A D B 242263235712 221018850 242263235840 220540895 242263235968 220064232 B 242263236096 219588856 242263236224 219114764 A A D B 242263236352 218641950 242263236480 218170411 242263236608 217700143 B 242397448704 286237189 242397448832 285605552 A D B 242397448960 284975656 242397449088 284347497 242397449216 283721068 B 242397449344 283096363 242397449472 282473377 A A A D B 242397449600 281852104 242397449728 281232539 242397449856 280614675 B 242397449984 279998507 242397450112 279384031 A D B 242397450240 278771239 242397450368 278160126 242397450496 277550688 B 242397450624 276942918 242397450752 276336812 A A D B 242397450880 275732362 242397451008 275129565 242397451136 274528415 B 242397451264 273928906 242397451392 273331032 A D B 242397451520 272734790 242397451648 272140172 242397451776 271547175 B 242397451904 270955792 242397452032 270366018 A A A A A A D B 242397452160 269777849 242397452288 269191278 242397452416 268606301 D B 242397452544 268022913 242397452672 267441108 242397452800 266860881 A D B 242397452928 266282227 242397453056 265705141 242397453184 265129617 B 242397453312 264555651 242397453440 263983238 A A D B 242397453568 263412373 242397453696 262843050 242397453824 262275265 B 242397453952 261709012 242397454080 261144287 A D B 242397454208 260581085 242397454336 260019400 242531666432 336922701 B 242531666560 336179217 242531666688 335437782 A A A D B 242531666816 334698392 242531666944 333961037 242531667072 333225713 B 242531667200 332492411 242531667328 331761126 A D B 242531667456 331031851 242531667584 330304579 242531667712 329579304 B 242531667840 328856018 242531667968 328134716 A A D B 242531668096 327415391 242531668224 326698036 242531668352 325982645 B 242531668480 325269212 242531668608 324557730 A D B 242531668736 323848192 242531668864 323140593 242531668992 322434926 B 242531669120 321731184 242531669248 321029362 A A A A D B 242531669376 320329452 242531669504 319631449 242531669632 318935347 B 242531669760 318241139 242531669888 317548820 A D B 242531670016 316858382 242531670144 316169820 242531670272 315483128 B 242531670400 314798300 242531670656 313434210 A A D B 242531670784 312754936 242531670912 312077501 242531671040 311401901 B 242531671168 310728127 242531671296 310056176 A D B 242531671424 309386040 242531671552 308717714 242531671680 308051192 B 242531671808 307386468 242531671936 306723537 A A A D B 242531672064 306062392 242665884288 390825957 242665884416 389964001 B 242665884544 389104420 242665884672 388247207 A D B 242665884800 387392354 242665884928 386539853 242665885056 385689695 B 242665885184 384841875 242665885312 383996383 A A D B 242665885440 383153212 242665885568 382312355 242665885696 381473804 B 242665885824 380637550 242665885952 379803588 A D B 242665886080 378971909 242665886208 378142505 242665886336 377315370 B 242665886464 376490495 242665886592 375667874 A A A A A D B 242665886720 374847499 242665886848 374029362 242665886976 373213456 B 242665887104 372399775 242665887232 371588310 A D B 242665887360 370779055 242665887488 369972002 242665887616 369167144 B 242665887744 368364474 242665887872 367563985 A A D B 242665888000 366765670 242665888128 365969521 242665888256 365175531 B 242665888384 364383694 242665888512 363594003 A D B 242665888640 362806450 242665888768 362021029 242665888896 361237732 B 242665889024 360456553 242665889152 359677485 A A A D B 242665889280 358900521 242665889408 358125654 242665889536 357352878 B 242665889664 356582186 242665889792 355813570 A D B 242800102016 449526181 242800102144 448534763 242800102272 447546077 B 242800102400 446560115 242800102528 445576866 A A D B 242800102656 444596323 242800102784 443618477 242800102912 442643317 B 242800103040 441670837 242800103168 440701026 A D B 242800103296 439733876 242800103424 438769378 242800103552 437807523 B 242800103680 436848304 242800103808 435891710 A A A A D B 242800103936 434937734 242800104064 433986367 242800104192 433037600 B 242800104320 432091425 242800104448 431147833 A D B 242800104576 430206816 242800104704 429268365 242800104832 428332473 B 242800104960 427399130 242800105088 426468328 A A D B 242800105216 425540060 242800105344 424614316 242800105472 423691089 B 242800105600 422770370 242800105728 421852151 A D B 242800105856 420936424 242800105984 420023181 242800106112 419112414 B 242800106240 418204115 242800106368 417298275 A A A D B 242800106496 416394887 242800106624 415493943 242800106752 414595435 B 242800106880 413699355 242800107008 412805694 A D B 242800107136 411914446 242800107264 411025603 242800107392 410139156 B 242800107520 409255098 242934319872 511128017 A A D B 242934320000 510001360 242934320128 508877806 242934320256 507757345 B 242934320384 506639966 242934320512 505525661 A D B 242934320640 504414417 242934320768 503306226 242934320896 502201078 B 242934321024 501098961
noncomputable def AEE : CTN :=
  A A A A A A A D B 242934321280 498903786 242934321408 497810706 242934321536 496720620 D B 242934321664 495633516 242934321792 494549385 242934321920 493468217 A D B 242934322048 492390002 242934322176 491314732 242934322304 490242396 B 242934322432 489172984 242934322560 488106487 A A D B 242934322688 487042896 242934322816 485982200 242934322944 484924391 B 242934323072 483869460 242934323200 482817396 A D B 242934323328 481768190 242934323456 480721833 242934323584 479678316 B 242934323712 478637630 242934323840 477599765 A A A D B 242934323968 476564712 242934324096 475532462 242934324224 474503005 B 242934324352 473476334 242934324480 472452439 A D B 242934324608 471431310 242934324736 470412939 242934324864 469397317 B 242934324992 468384434 242934325120 467374283 A A D B 242934325248 466366854 243068537728 576445776 243068537856 575175842 B 243068537984 573909404 243068538112 572646451 A D B 243068538240 571386970 243068538368 570130951 243068538496 568878382 B 243068538624 567629251 243068538752 566383548 A A A A D B 243068538880 565141261 243068539008 563902378 243068539136 562666890 B 243068539264 561434783 243068539392 560206048 A D B 243068539520 558980674 243068539648 557758648 243068539776 556539961 B 243068539904 555324601 243068540032 554112558 A A D B 243068540160 552903820 243068540288 551698377 243068540416 550496218 B 243068540544 549297333 243068540672 548101709 A D B 243068540800 546909338 243068540928 545720208 243068541056 544534309 B 243068541184 543351630 243068541312 542172161 A A A D B 243068541440 540995891 243068541568 539822810 243068541696 538652907 B 243068541824 537486172 243068541952 536322596 A D B 243068542080 535162167 243068542208 534004875 243068542336 532850711 B 243068542592 530551723 243068542720 529406880 A A D B 243068542848 528265124 243068542976 527126444 243202755584 645427312 B 243202755712 644006192 243202755840 642588983 A D B 243202755968 641175670 243202756096 639766242 243202756224 638360685 B 243202756352 636958987 243202756480 635561135 A A A A A D B 243202756608 634167116 243202756736 632776917 243202756864 631390527 D B 243202756992 630007933 243202757120 628629121 243202757248 627254080 A D B 243202757376 625882798 243202757504 624515261 243202757632 623151458 B 243202757760 621791377 243202757888 620435005 A A D B 243202758016 619082330 243202758144 617733341 243202758272 616388024 B 243202758400 615046369 243202758528 613708362 A D B 243202758656 612373993 243202758784 611043249 243202758912 609716119 B 243202759040 608392590 243202759168 607072652 A A A D B 243202759296 605756291 243202759424 604443498 243202759552 603134259 B 243202759680 601828565 243202759808 600526402 A D B 243202759936 599227760 243202760064 597932627 243202760192 596640992 B 243202760320 595352843 243202760448 594068169 A A D B 243202760576 592786960 243202760704 591509203 243336973312 719602840 B 243336973440 718018399 243336973568 716438317 A D B 243336973696 714862581 243336973824 713291174 243336973952 711724084 B 243336974080 710161296 243336974208 708602796 A A A A D B 243336974336 707048570 243336974464 705498604 243336974592 703952883 B 243336974720 702411394 243336974848 700874123 A D B 243336974976 699341056 243336975104 697812179 243336975232 696287479 B 243336975360 694766942 243336975488 693250553 A A D B 243336975616 691738301 243336975744 690230170 243336975872 688726149 B 243336976000 687226222 243336976128 685730377 A D B 243336976256 684238601 243336976384 682750879 243336976512 681267200 B 243336976640 679787550 243336976768 678311915 A A A D B 243336976896 676840283 243336977024 675372641 243336977152 673908975 B 243336977280 672449272 243336977408 670993521 A D B 243336977664 668093819 243336977792 666649844 243336977920 665209768 B 243336978048 663773579 243336978176 662341265 A A D B 243336978304 660912813 243336978432 659488210 243471191168 795914270 B 243471191296 794162769 243471191424 792416085 A D B 243471191552 790674201 243471191680 788937101 243471191808 787204771 B 243471191936 785477193 243471192064 783754353 A A A A A A D B 243471192192 782036235 243471192320 780322823 243471192448 778614103 D B 243471192576 776910057 243471192704 775210672 243471192832 773515932 A D B 243471192960 771825821 243471193088 770140324 243471193216 768459427 B 243471193344 766783115 243471193472 765111371 A A D B 243471193600 763444182 243471193728 761781532 243471193856 760123407 B 243471193984 758469792 243471194112 756820672 A D B 243471194240 755176033 243471194368 753535859 243471194496 751900137 B 243471194624 750268851 243471194752 748641988 A A A D B 243471194880 747019533 243471195008 745401472 243471195136 743787790 B 243471195264 742178473 243471195392 740573507 A D B 243471195520 738972879 243471195776 735784576 243471195904 734196874 B 243471196160 731034299 243605409024 875728226 A A D B 243605409152 873802147 243605409280 871881360 243605409408 869965850 B 243605409536 868055598 243605409664 866150588 A D B 243605409792 864250802 243605409920 862356222 243605410048 860466832 B 243605410176 858582615 243605410304 856703554 A A A A D B 243605410432 854829631 243605410560 852960830 243605410688 851097135 B 243605410816 849238527 243605410944 847384992 A D B 243605411072 845536511 243605411200 843693069 243605411328 841854649 B 243605411456 840021235 243605411584 838192811 A A D B 243605411712 836369359 243605411840 834550864 243605411968 832737310 B 243605412096 830928680 243605412224 829124959 A D B 243605412352 827326130 243605412480 825532178 243605412608 823743087 B 243605412736 821958841 243605412864 820179423 A A A D B 243605412992 818404820 243605413120 816635014 243605413248 814869991 B 243605413376 813109735 243605413504 811354230 A D B 243605413632 809603461 243605413888 806116070 243739627008 956876293 B 243739627136 954774050 243739627264 952677578 A A D B 243739627392 950586859 243739627520 948501872 243739627648 946422601 B 243739627776 944349025 243739627904 942281126 A D B 243739628032 940218885 243739628160 938162284 243739628288 936111304 B 243739628416 934065926 243739628544 932026134 A A A A A D B 243739628672 929991907 243739628800 927963228 243739628928 925940079 B 243739629056 923922442 243739629184 921910299 A D B 243739629312 919903631 243739629440 917902421 243739629568 915906651 B 243739629696 913916303 243739629824 911931360 A A D B 243739629952 909951804 243739630080 907977617 243739630208 906008783 B 243739630336 904045283 243739630464 902087100 A D B 243739630592 900134217 243739630720 898186617 243739630848 896244283 B 243739630976 894307197 243739631104 892375343 A A A D B 243739631232 890448704 243739631360 888527262 243739631488 886611001 B 243739631616 884699904 243873844864 1043323042 A D B 243873844992 1041032136 243873845120 1038747516 243873845248 1036469161 B 243873845376 1034197051 243873845504 1031931164 A A D B 243873845632 1029671481 243873845760 1027417981 243873845888 1025170644 B 243873846016 1022929449 243873846144 1020694377 A D B 243873846272 1018465407 243873846400 1016242519 243873846528 1014025694 B 243873846656 1011814911 243873846784 1009610151 A A A A D B 243873846912 1007411394 243873847040 1005218621 243873847168 1003031812 B 243873847296 1000850948 243873847424 998676008 A D B 243873847552 996506975 243873847680 994343828 243873847808 992186549 B 243873847936 990035118 243873848064 987889516 A A D B 243873848192 985749725 243873848320 983615725 243873848448 981487498 B 243873848576 979365025 243873848704 977248288 A D B 243873848832 975137267 243873848960 973031944 243873849088 970932301 B 243873849216 968838320 243873849344 966749982 A A A D B 244008062848 1130591723 244008062976 1128111920 244008063104 1125638914 B 244008063232 1123172682 244008063360 1120713201 A D B 244008063488 1118260451 244008063616 1115814408 244008063744 1113375051 B 244008063872 1110942357 244008064000 1108516306 A A D B 244008064128 1106096874 244008064256 1103684041 244008064384 1101277785 B 244008064512 1098878084 244008064640 1096484917 A D B 244008064768 1094098263 244008064896 1091718100 244008065024 1089344408 B 244008065152 1086977164
noncomputable def AEF : CTN :=
  A A A A A A A D B 244008065408 1082261940 244008065536 1079913918 244008065664 1077572261 D B 244008065792 1075236949 244008065920 1072907962 244008066048 1070585278 A D B 244008066176 1068268877 244008066304 1065958738 244008066432 1063654843 B 244008066560 1061357169 244008066688 1059065697 A A D B 244008066816 1056780408 244008066944 1054501280 244008067072 1052228295 B 244142280832 1220705213 244142280960 1218030694 A D B 244142281088 1215363497 244142281216 1212703598 244142281344 1210050974 B 244142281472 1207405600 244142281600 1204767452 A A A D B 244142281728 1202136507 244142281856 1199512742 244142281984 1196896132 B 244142282112 1194286654 244142282240 1191684286 A D B 244142282368 1189089003 244142282496 1186500783 244142282624 1183919603 B 244142282752 1181345439 244142282880 1178778269 A A D B 244142283008 1176218070 244142283136 1173664819 244142283264 1171118493 B 244142283392 1168579071 244142283520 1166046529 A D B 244142283648 1163520846 244142283776 1161001999 244142283904 1158489965 B 244142284032 1155984723 244142284160 1153486251 A A A A D B 244142284288 1150994526 244142284416 1148509528 244142284544 1146031233 B 244142284672 1143559621 244142284800 1141094669 A D B 244276498688 1316460025 244276498816 1313577291 244276498944 1310702446 B 244276499072 1307835462 244276499200 1304976314 A A D B 244276499328 1302124978 244276499456 1299281425 244276499584 1296445633 B 244276499712 1293617574 244276499840 1290797224 A D B 244276499968 1287984558 244276500096 1285179550 244276500224 1282382175 B 244276500352 1279592409 244276500480 1276810226 A A A D B 244276500608 1274035603 244276500736 1271268513 244276500864 1268508933 B 244276500992 1265756839 244276501120 1263012205 A D B 244276501376 1257545224 244276501504 1254822828 244276501632 1252107796 B 244276501760 1249400105 244276501888 1246699731 A A D B 244276502016 1244006650 244276502144 1241320838 244276502272 1238642271 B 244276502400 1235970928 244276502528 1233306783 A D B 244410716800 1409120737 244410716928 1406040163 244410717056 1402968005 B 244410717184 1399904234 244410717312 1396848823 A A A A A D B 244410717440 1393801746 244410717568 1390762974 244410717696 1387732481 D B 244410717824 1384710239 244410717952 1381696222 244410718080 1378690402 A D B 244410718208 1375692753 244410718336 1372703249 244410718464 1369721862 B 244410718592 1366748567 244410718720 1363783337 A A D B 244410718848 1360826145 244410719104 1354935774 244410719232 1352002542 B 244410719360 1349077245 244410719616 1343250352 A D B 244410719872 1337454890 244410720000 1334568883 244410720128 1331690657 B 244410720256 1328820187 244544935040 1500673377 A A A D B 244544935296 1494135181 244544935424 1490879438 244544935552 1487632560 B 244544935680 1484394517 244544935808 1481165282 A D B 244544935936 1477944825 244544936064 1474733118 244544936192 1471530132 B 244544936320 1468335838 244544936448 1465150209 A A D B 244544936704 1458804832 244544936960 1452493775 244544937088 1449351047 B 244544937216 1446216816 244544937344 1443091055 A D B 244544937472 1439973735 244544937984 1427588329 244679152896 1604360778 B 244679153536 1586966592 244679153664 1583516094 A A A A D B 244679153920 1576643191 244679154048 1573220726 244679154176 1569807544 B 244679154304 1566403615 244679154432 1563008909 A D B 244679154560 1559623396 244679155072 1546172679 244679155200 1542832686 B 244679155328 1539501708 244679155456 1536179716 A A D B 244679155584 1532866682 244679155712 1529562576 244813371520 1688676445 B 244813371648 1685008793 244813371776 1681351095 A D B 244813371904 1677703319 244813372032 1674065431 244813372160 1670437401 B 244813372416 1663210783 244813372544 1659612132 A A A D B 244813372672 1656023210 244813372800 1652443986 244813372928 1648874429 B 244813373056 1645314507 244813373184 1641764189 A D B 244813373440 1634692240 244947589632 1788783431 244947589888 1781036440 B 244947590912 1750464784 244947591168 1742924605 A A D B 245081807744 1890646037 245081808256 1874340469 245081808896 1854204952 B 245216026112 1985554610 245216026624 1968476591 A D B 245350244352 2085680892 245484462080 2205757314 245618679808 2328643438 B 245752897536 2454275003 245887115264 2582585939 A A A A A A D B 246021332992 2713508404 246155550720 2846972824 246289768448 2982907926 D B 246423986176 3121240784 246558203904 3261896857 246692421632 3404800031 A D B 246826639360 3549872660 246960857088 3697035617 247229292544 3997308832 B 247363510272 4150253813 247497728000 4304958658 A A D B 247631945728 4461337505 247900381184 4778767791 248303034368 5265255281 B 248571469824 5595409518 249108340864 6252832886 A D B 249108340992 6239369381 249108341120 6225942100 249108341248 6212550927 B 249108341376 6199195745 249108341504 6185876437 A A A D B 249108341632 6172592889 249108341760 6159344984 249108341888 6146132609 B 249108342016 6132955649 249108342144 6119813990 A D B 249108342272 6106707518 249108342400 6093636122 249108342528 6080599687 B 249108342656 6067598102 249108342784 6054631256 A A D B 249108342912 6041699036 249108343040 6028801332 249108343168 6015938033 B 249108343296 6003109029 249108343424 5990314211 A D B 249108343552 5977553470 249108343680 5964826696 249108343808 5952133780 B 249108343936 5939474616 249108344064 5926849095 A A A A D B 249108344192 5914257110 249108344320 5901698554 249108344448 5889173320 B 249108344576 5876681304 249108344704 5864222398 A D B 249108344832 5851796498 249108344960 5839403498 249108345088 5827043295 B 249108345216 5814715784 249108345344 5802420861 A A D B 249108345472 5790158424 249108345600 5777928368 249108345728 5765730593 B 249108345856 5753564994 249108345984 5741431471 A D B 249108346112 5729329922 249108346240 5717260246 249108346368 5705222343 B 249108346496 5693216111 249108346624 5681241451 A A A D B 249108346752 5669298264 249108346880 5657386450 249108347008 5645505910 B 249108347136 5633656546 249108347264 5621838259 A D B 249108347392 5610050953 249108347520 5598294529 249108347648 5586568890 B 249108347776 5574873941 249108347904 5563209583 A A D B 249108348032 5551575722 249108348160 5539972262 249108348288 5528399107 B 249108348416 5516856162 249108348544 5505343334 A D B 249108348672 5493860527 249108348800 5482407647 249108348928 5470984602 B 249242566656 5618869944 249376784384 5767163520 A A A A A D B 249779437568 6213637746 250853179136 7431651729 251255832576 7837850954 D B 251658485760 8266998639 257429848064 12307821143 257698283648 12328914849 A D B 257698283776 12297695318 257698283904 12262871751 257698284032 12224472446 B 257698284160 12182527748 257698284288 12137070023 A A D B 257698284416 12088133631 257698284544 12035754896 257698284672 11979972077 B 257698284800 11920825333 257698284928 11858356700 A D B 257698285056 11792610047 257698285184 11723631051 257698285312 11651467159 B 257698285440 11576167549 257698285568 11497783098 A A A D B 257698285696 11416366344 257698285824 11331971444 257698285952 11244654140 B 257698286080 11154471714 257698286208 11061482951 A D B 257698286336 10965748097 257698286464 10867328815 257698286592 10766288143 B 257698286720 10662690453 257698286848 10556601403 A A D B 257698286976 10448087897 257698287104 10337218034 257698287232 10224061067 B 257698287360 10108687356 257698287488 9991168320 A D B 257698287616 9871576391 257698287744 9749984964 257698287872 9626468354 B 257698288000 9501101744 257698288128 9373961137 A A A A D B 257698288256 9245123305 257698288512 8982666632 257698288640 8849204752 B 257698288768 8714359474 257698288896 8578210688 A D B 257698289024 8440838759 257698289152 8302324476 257698289280 8162748999 B 257698289408 8022193814 257698289536 7880740680 A A D B 257698289664 7738471579 257698289792 7595468668 257698289920 7451814225 B 257698290048 7307590603 257698290176 7162880181 A D B 257698290304 7017765309 257698290432 6872328267 257698290560 6726651207 B 257698290688 6580816113 257698290816 6434904745 A A A D B 257698290944 6288998599 257698291072 6143178849 257698291200 5997526311 B 257698291456 5707044022 257698291584 5562373662 A D B 257698291712 5418189199 257832509440 5428660892 258100944896 5449631692 B 258503598080 5481145436 261322170368 5702045547 A A D B 261456388096 5712508673 263738089472 5888098910 264006524928 5908378508 B 265348702208 6008159705 266288226432 5918661125 A D B 266288226560 5761840971 266288226816 5450507304 266288227072 5142792756 B 266288227200 4990493261
noncomputable def AEG : CTN :=
  A A A A A A A D B 266288227584 4540766178 266288227712 4393502857 266288227840 4247687290 D B 266288228224 3819653364 266288228352 3680348919 266288228608 3407211498 A D B 266288228736 3273510876 266288228864 3141808217 266288228992 3012166152 B 266288229120 2884645835 266288229632 2396951801 A A D B 266288229760 2280903808 266288229888 2167311862 266288230016 2056225992 B 266288230144 1947694536 266288230400 1738479639 A D B 266288230528 1637884235 266288230656 1540019276 266288230912 1352637219 B 266288231168 1176628374 266288231552 934512692 A A A D B 266288231680 859762868 266288231936 719347841 266288232192 591188723 B 266288232576 422238774 266288232704 372187771 A D B 266288233088 240965112 266288233600 110332544 266288234112 30283298 B 266288234240 18122334 266288234496 3137894 A A D B 266556668544 242745705 267093540864 3598318 267898846592 68558577 B 268838371328 4548727 269375242240 4816660 A D B 269777895424 5007135 270180548480 12516837 270180548608 5187481 B 270314766336 5245175 270717419520 5410505 A A A A D B 270851636608 75267996 271656943616 5746958 272328032256 5940737 B 272999120896 6092360 274878169216 1499244 A D B 275146605568 3012 275146605696 3006 275146605824 3001 B 275146605952 2995 275146606080 2989 A A D B 275146606208 2983 275146606336 2977 275146606464 2972 B 275146606592 2966 275146606720 2960 A D B 275146606848 2954 275146606976 2949 275146607104 2943 B 275146607232 2937 275146607360 2931 A A A D B 275146607488 2926 275146607616 2920 275146607744 2915 B 275146607872 2909 275146608000 2903 A D B 275146608128 2898 275146608256 2892 275146608384 2887 B 275146608512 2881 275146608640 2875 A A D B 275146608768 2870 275146608896 2864 275146609024 2859 B 275146609152 2853 275146609280 2848 A D B 275146609408 2842 275146609664 2832 275146609792 2826 B 275146609920 2821 275146610048 2815 A A A A A D B 275146610176 2810 275146610304 2805 275146610432 2799 D B 275146610560 2794 275146610688 2789 275146610816 2783 A D B 275146610944 2778 275146611072 2773 275146611200 2767 B 275146611328 2762 275146611456 2757 A A D B 275146611584 2752 275146611712 2746 275146611840 2741 B 275146611968 2736 275146612096 2731 A D B 275146612352 2720 275146612608 2710 275146612736 2705 B 275280823424 1757806 275280823552 1754389 A A A D B 275280823680 1750981 275280823808 1747580 275280823936 1744189 B 275280824064 1740805 275280824192 1737429 A D B 275280824320 1734062 275280824448 1730703 275280824576 1727352 B 275280824704 1724009 275280824832 1720674 A A D B 275280824960 1717348 275280825088 1714029 275280825216 1710718 B 275280825344 1707415 275280825472 1704121 A D B 275280825600 1700834 275280825728 1697555 275280825856 1694284 B 275280825984 1691021 275280826112 1687766 A A A A D B 275280826240 1684518 275280826368 1681279 275280826496 1678047 B 275280826624 1674823 275280826752 1671606 A D B 275280826880 1668398 275280827008 1665197 275280827136 1662004 B 275280827264 1658818 275280827392 1655640 A A D B 275280827520 1652470 275280827648 1649307 275280827776 1646152 B 275280827904 1643004 275280828032 1639864 A D B 275280828160 1636731 275280828288 1633606 275280828416 1630489 B 275280828544 1627378 275280828672 1624276 A A A D B 275280828800 1621180 275280828928 1618092 275280829056 1615011 B 275280829184 1611938 275280829312 1608872 A D B 275280829440 1605813 275280829568 1602761 275280829696 1599717 B 275280829824 1596680 275280830080 1590628 A A D B 275280830464 1581602 275415041280 6735697 275415041408 6722611 B 275415041536 6709556 275415041664 6696534 A D B 275415041792 6683543 275415041920 6670583 275415042048 6657655 B 275415042176 6644758 275415042304 6631892 A A A A A A D B 275415042432 6619058 275415042560 6606254 275415042688 6593482 D B 275415042816 6580740 275415042944 6568029 275415043072 6555349 A D B 275415043200 6542699 275415043328 6530080 275415043456 6517492 B 275415043584 6504933 275415043712 6492405 A A D B 275415043840 6479907 275415043968 6467439 275415044096 6455001 B 275415044224 6442593 275415044352 6430215 A D B 275415044480 6417866 275415044608 6405547 275415044736 6393258 B 275415044864 6380998 275415044992 6368768 A A A D B 275415045120 6356566 275415045248 6344394 275415045376 6332251 B 275415045504 6320138 275415045632 6308053 A D B 275415045760 6295997 275415045888 6283969 275415046016 6271971 B 275415046144 6260001 275415046272 6248060 A A D B 275415046400 6236147 275415046528 6224262 275415046656 6212406 B 275415046784 6200578 275415046912 6188778 A D B 275415047040 6177006 275415047168 6165263 275415047296 6153547 B 275415047424 6141859 275415047680 6118566 A A A A D B 275415047808 6106961 275415047936 6095383 275415048064 6083833 B 275415048192 6072310 275549259008 14953340 A D B 275549259136 14924289 275549259264 14895308 275549259392 14866397 B 275549259520 14837557 275549259648 14808787 A A D B 275549259776 14780086 275549259904 14751455 275549260032 14722893 B 275549260160 14694400 275549260288 14665976 A D B 275549260416 14637621 275549260544 14609334 275549260672 14581116 B 275549260800 14552966 275549260928 14524883 A A A D B 275549261056 14496869 275549261184 14468922 275549261312 14441042 B 275549261440 14413229 275549261568 14385483 A D B 275549261696 14357804 275549261824 14330192 275549261952 14302646 B 275549262080 14275166 275549262208 14247752 A A D B 275549262336 14220404 275549262464 14193121 275549262592 14165904 B 275549262720 14138752 275549262848 14111665 A D B 275549262976 14084643 275549263104 14057686 275549263232 14030793 B 275549263360 14003964 275549263488 13977200 A A A A A D B 275549263616 13950499 275549263744 13923862 275549263872 13897289 B 275549264000 13870779 275549264128 13844332 A D B 275549264256 13817949 275549264384 13791628 275549264512 13765369 B 275549264640 13739174 275549264768 13713040 A A D B 275549264896 13686969 275549265024 13660959 275549265152 13635012 B 275549265280 13609125 275549265408 13583301 A D B 275549265664 13531835 275549265920 13480613 275683476864 26360471 B 275683476992 26309283 275683477120 26258219 A A A D B 275683477248 26207279 275683477376 26156462 275683477504 26105768 B 275683477632 26055198 275683477760 26004749 A D B 275683477888 25954423 275683478016 25904219 275683478144 25854136 B 275683478272 25804173 275683478400 25754332 A A D B 275683478528 25704611 275683478656 25655009 275683478784 25605528 B 275683478912 25556165 275683479040 25506922 A D B 275683479168 25457797 275683479296 25408790 275683479424 25359901 B 275683479552 25311130 275683479680 25262476 A A A A D B 275683479808 25213939 275683479936 25165518 275683480064 25117213 B 275683480192 25069025 275683480320 25020952 A D B 275683480448 24972994 275683480576 24925151 275683480704 24877422 B 275683480832 24829808 275683480960 24782307 A A D B 275683481088 24734921 275683481216 24687647 275683481344 24640486 B 275683481472 24593438 275683481600 24546502 A D B 275683481728 24499678 275683481856 24452966 275683481984 24406365 B 275683482112 24359874 275683482240 24313495 A A A D B 275683482368 24267226 275683482496 24221067 275683482624 24175018 B 275683482752 24129078 275683482880 24083247 A D B 275683483008 24037525 275683483136 23991911 275683483264 23946406 B 275683483392 23901008 275683483520 23855718 A A D B 275683483648 23810535 275817694720 40953977 275817694848 40874489 B 275817694976 40795194 275817695104 40716091 A D B 275817695232 40637180 275817695360 40558460 275817695488 40479930 B 275817695616 40401590
noncomputable def AEH : CTN :=
  A A A A A A A D B 275817695872 40245479 275817696000 40167706 275817696128 40090121 D B 275817696256 40012723 275817696384 39935512 275817696512 39858487 A D B 275817696640 39781648 275817696768 39704993 275817696896 39628524 B 275817697024 39552238 275817697152 39476136 A A D B 275817697280 39400217 275817697408 39324480 275817697536 39248925 B 275817697664 39173552 275817697792 39098359 A D B 275817697920 39023347 275817698048 38948515 275817698176 38873862 B 275817698304 38799388 275817698432 38725092 A A A D B 275817698560 38650974 275817698688 38577033 275817698816 38503269 B 275817698944 38429681 275817699072 38356269 A D B 275817699200 38283032 275817699328 38209970 275817699456 38137082 B 275817699584 38064368 275817699712 37991827 A A D B 275817699840 37919458 275817699968 37847263 275817700096 37775238 B 275817700224 37703386 275817700352 37631703 A D B 275817700480 37560192 275817700608 37488850 275817700736 37417677 B 275817700864 37346673 275817700992 37275838 A A A A D B 275817701248 37134670 275817701376 37064337 275951912576 58715749 B 275951912704 58601843 275951912832 58488212 A D B 275951912960 58374857 275951913088 58261776 275951913216 58148969 B 275951913344 58036435 275951913472 57924173 A A D B 275951913600 57812183 275951913728 57700463 275951913856 57589013 B 275951913984 57477832 275951914112 57366919 A D B 275951914240 57256273 275951914368 57145894 275951914496 57035781 B 275951914624 56925933 275951914752 56816350 A A A D B 275951914880 56707030 275951915008 56597973 275951915136 56489178 B 275951915264 56380645 275951915392 56272372 A D B 275951915520 56164358 275951915648 56056604 275951915776 55949108 B 275951915904 55841870 275951916032 55734889 A A D B 275951916160 55628164 275951916288 55521694 275951916416 55415478 B 275951916544 55309517 275951916672 55203809 A D B 275951916800 55098353 275951916928 54993149 275951917056 54888196 B 275951917184 54783494 275951917312 54679041 A A A A A D B 275951917440 54574836 275951917568 54470880 275951917696 54367172 D B 275951917824 54263710 275951917952 54160494 275951918080 54057523 A D B 275951918208 53954797 275951918336 53852316 275951918464 53750077 B 275951918592 53648081 275951918720 53546326 A A D B 275951918976 53343541 275951919104 53242508 276086130304 79780582 B 276086130432 79625810 276086130560 79471414 A D B 276086130688 79317391 276086130816 79163742 276086130944 79010464 B 276086131072 78857558 276086131200 78705021 A A A D B 276086131328 78552853 276086131456 78401052 276086131584 78249618 B 276086131712 78098550 276086131840 77947846 A D B 276086131968 77797505 276086132096 77647527 276086132224 77497910 B 276086132352 77348653 276086132480 77199755 A A D B 276086132608 77051216 276086132736 76903034 276086132864 76755207 B 276086132992 76607736 276086133120 76460619 A D B 276086133248 76313855 276086133376 76167443 276086133504 76021383 B 276086133632 75875672 276086133760 75730310 A A A A D B 276086133888 75585296 276086134016 75440629 276086134144 75296308 B 276086134272 75152332 276086134400 75008700 A D B 276086134528 74865411 276086134656 74722464 276086134784 74579858 B 276086134912 74437592 276086135040 74295666 A A D B 276086135168 74154077 276086135296 74012826 276086135424 73871911 B 276086135552 73731331 276086135680 73591086 A D B 276086135808 73451173 276086135936 73311594 276086136064 73172345 B 276086136192 73033427 276086136320 72894839 A A A D B 276086136448 72756580 276086136576 72618648 276086136704 72481042 B 276086136832 72343763 276220348160 103863728 A D B 276220348288 103662334 276220348416 103461427 276220348544 103261007 B 276220348672 103061072 276220348800 102861621 A A D B 276220348928 102662653 276220349056 102464165 276220349184 102266156 B 276220349312 102068626 276220349440 101871573 A D B 276220349568 101674995 276220349696 101478891 276220349824 101283259 B 276220349952 101088099 276220350080 100893409 A A A A A A D B 276220350208 100699188 276220350336 100505433 276220350464 100312144 D B 276220350592 100119320 276220350720 99926959 276220350848 99735060 A D B 276220350976 99543622 276220351104 99352642 276220351232 99162121 B 276220351360 98972056 276220351488 98782446 A A D B 276220351616 98593290 276220351744 98404587 276220352000 98028533 B 276220352128 97841180 276220352256 97654274 A D B 276220352512 97281800 276220352640 97096229 276220352768 96911100 B 276220352896 96726412 276220353024 96542164 A A A D B 276220353152 96358355 276220353280 96174983 276220353408 95992047 B 276220353536 95809546 276220353664 95627478 A D B 276220353792 95445843 276220353920 95264639 276220354176 94903519 B 276220354304 94723601 276220354432 94544109 A A D B 276220354560 94365042 276354566016 131055657 276354566144 130801659 B 276354566272 130548277 276354566400 130295509 A D B 276354566528 130043352 276354566656 129791804 276354566784 129540865 B 276354566912 129290532 276354567040 129040803 A A A A D B 276354567168 128791678 276354567296 128543153 276354567424 128295227 B 276354567552 128047899 276354567680 127801167 A D B 276354567808 127555029 276354567936 127309483 276354568064 127064528 B 276354568192 126820162 276354568320 126576383 A A D B 276354568448 126333190 276354568576 126090580 276354568704 125848553 B 276354568832 125607106 276354568960 125366238 A D B 276354569088 125125948 276354569216 124886232 276354569344 124647091 B 276354569472 124408522 276354569600 124170523 A A A D B 276354569728 123933094 276354569856 123696232 276354569984 123459935 B 276354570112 123224202 276354570240 122989032 A D B 276354570368 122754423 276354570496 122520373 276354570624 122286881 B 276354570752 122053944 276354570880 121821562 A A D B 276354571008 121589733 276354571136 121358456 276354571264 121127728 B 276354571392 120897548 276354571520 120667914 A D B 276354571648 120438826 276354571776 120210281 276354571904 119982279 B 276354572032 119754816 276354572288 119301506 A A A A A D B 276488783872 161330832 276488784000 161018311 276488784128 160706546 B 276488784256 160395535 276488784384 160085277 A D B 276488784512 159775768 276488784640 159467007 276488784768 159158992 B 276488784896 158851720 276488785024 158545189 A A D B 276488785152 158239398 276488785280 157934343 276488785408 157630024 B 276488785536 157326437 276488785664 157023580 A D B 276488785792 156721453 276488785920 156420051 276488786048 156119374 B 276488786176 155819420 276488786304 155520185 A A A D B 276488786432 155221668 276488786560 154923868 276488786688 154626781 B 276488786816 154330407 276488786944 154034742 A D B 276488787072 153739785 276488787200 153445533 276488787328 153151986 B 276488787456 152859140 276488787584 152566994 A A D B 276488787712 152275546 276488787840 151984793 276488787968 151694734 B 276488788096 151405367 276488788224 151116690 A D B 276488788352 150828700 276488788480 150541396 276488788608 150254776 B 276488788736 149968838 276488788864 149683580 A A A A D B 276488788992 149399000 276488789120 149115096 276488789248 148831866 B 276488789376 148549309 276488789504 148267421 A D B 276488789632 147986203 276488789760 147705650 276488789888 147425763 B 276488790016 147146538 276623001728 194661921 A A D B 276623001856 194285015 276623001984 193909021 276623002112 193533936 B 276623002240 193159758 276623002368 192786483 A D B 276623002496 192414110 276623002624 192042636 276623002752 191672058 B 276623002880 191302374 276623003008 190933581 A A A D B 276623003136 190565676 276623003264 190198656 276623003392 189832521 B 276623003520 189467265 276623003648 189102888 A D B 276623003776 188739387 276623003904 188376759 276623004032 188015001 B 276623004160 187654112 276623004288 187294088 A A D B 276623004416 186934928 276623004544 186576628 276623004672 186219186 B 276623004800 185862599 276623004928 185506867 A D B 276623005056 185151984 276623005184 184797951 276623005312 184444763 B 276623005440 184092418
noncomputable def AEI : CTN :=
  A A A A A A A D B 276623005696 183390250 276623005824 183040422 276623005952 182691428 D B 276623006080 182343265 276623006208 181995931 276623006336 181649424 A D B 276623006592 180958880 276623006848 180271616 276623006976 179929207 B 276623007104 179587611 276623007232 179246826 A A D B 276623007360 178906848 276623007488 178567676 276623007616 178229308 B 276623007744 177891741 276757219584 231019807 A D B 276757219712 230572721 276757219840 230126716 276757219968 229681789 B 276757220096 229237938 276757220224 228795158 A A A D B 276757220352 228353446 276757220480 227912801 276757220608 227473218 B 276757220736 227034694 276757220864 226597227 A D B 276757220992 226160813 276757221120 225725449 276757221248 225291133 B 276757221376 224857860 276757221504 224425629 A A D B 276757221632 223994437 276757221760 223564279 276757221888 223135154 B 276757222016 222707058 276757222144 222279988 A D B 276757222272 221853942 276757222400 221428916 276757222528 221004908 B 276757222656 220581914 276757222784 220159932 A A A A D B 276757222912 219738959 276757223040 219318991 276757223168 218900027 B 276757223296 218482062 276757223424 218065095 A D B 276757223552 217649122 276757223680 217234141 276757223808 216820149 B 276757223936 216407142 276757224064 215995118 A A D B 276757224192 215584075 276757224320 215174009 276757224448 214764918 B 276757224576 214356799 276757224704 213949648 A D B 276757224832 213543465 276757224960 213138244 276757225088 212733985 B 276757225216 212330684 276757225472 211526945 A A A D B 276891437568 269850622 276891437696 269328893 276891437824 268808425 B 276891437952 268289213 276891438080 267771255 A D B 276891438208 267254546 276891438336 266739083 276891438464 266224862 B 276891438592 265711881 276891438720 265200134 A A D B 276891438848 264689619 276891438976 264180332 276891439104 263672269 B 276891439232 263165428 276891439360 262659804 A D B 276891439488 262155393 276891439616 261652194 276891439744 261150201 B 276891439872 260649411 276891440000 260149822 A A A A A D B 276891440128 259651429 276891440256 259154230 276891440384 258658220 D B 276891440512 258163396 276891440640 257669755 276891440768 257177294 A D B 276891440896 256686009 276891441024 256195897 276891441152 255706954 B 276891441280 255219177 276891441408 254732562 A A D B 276891441536 254247107 276891441664 253762809 276891441920 252797666 B 276891442048 252316816 276891442176 251837108 A D B 276891442304 251358540 276891442432 250881109 276891442560 250404811 B 276891442688 249929642 276891442816 249455601 A A A D B 276891443072 248510885 276891443200 248040204 277025655296 312690733 B 277025655424 312086177 277025655552 311483081 A D B 277025655680 310881442 277025655808 310281256 277025655936 309682517 B 277025656064 309085222 277025656192 308489366 A A D B 277025656320 307894946 277025656448 307301957 277025656576 306710395 B 277025656704 306120256 277025656832 305531536 A D B 277025656960 304944231 277025657088 304358336 277025657216 303773849 B 277025657344 303190763 277025657472 302609077 A A A A D B 277025657600 302028785 277025657728 301449883 277025657856 300872368 B 277025657984 300296236 277025658112 299721482 A D B 277025658240 299148102 277025658368 298576094 277025658496 298005452 B 277025658624 297436173 277025658752 296868253 A A D B 277025658880 296301687 277025659008 295736473 277025659136 295172607 B 277025659264 294610084 277025659392 294048900 A D B 277025659520 293489052 277025659648 292930536 277025659776 292373348 B 277025659904 291817485 277025660032 291262942 A A A D B 277025660160 290709716 277025660288 290157803 277025660416 289607200 B 277025660544 289057902 277025660672 288509905 A D B 277025660800 287963208 277025660928 287417804 277159873152 357936832 B 277159873280 357245132 277159873408 356555102 A A D B 277159873536 355866738 277159873664 355180035 277159873792 354494987 B 277159873920 353811590 277159874048 353129840 A D B 277159874176 352449731 277159874304 351771259 277159874432 351094419 B 277159874560 350419206 277159874688 349745616 A A A A A A D B 277159874816 349073644 277159874944 348403285 277159875072 347734535 D B 277159875200 347067389 277159875328 346401842 277159875456 345737890 A D B 277159875584 345075528 277159875712 344414752 277159875840 343755558 B 277159875968 343097939 277159876096 342441893 A A D B 277159876224 341787414 277159876352 341134499 277159876480 340483142 B 277159876608 339833339 277159876736 339185085 A D B 277159876864 338538377 277159876992 337893210 277159877120 337249579 B 277159877248 336607480 277159877376 335966909 A A A D B 277159877504 335327861 277159877632 334690332 277159877760 334054318 B 277159877888 333419814 277159878144 332155319 A D B 277159878272 331525320 277159878400 330896814 277159878528 330269797 B 277159878656 329644265 277294091136 405291548 A A D B 277294091264 404509093 277294091392 403728526 277294091520 402949841 B 277294091648 402173033 277294091776 401398096 A D B 277294091904 400625025 277294092032 399853815 277294092160 399084459 B 277294092288 398316954 277294092416 397551293 A A A A D B 277294092544 396787471 277294092672 396025483 277294092800 395265323 B 277294092928 394506987 277294093056 393750469 A D B 277294093184 392995763 277294093312 392242865 277294093440 391491770 B 277294093568 390742472 277294093696 389994965 A A D B 277294093824 389249246 277294093952 388505309 277294094080 387763148 B 277294094208 387022759 277294094336 386284136 A D B 277294094464 385547275 277294094592 384812171 277294094720 384078817 B 277294094848 383347211 277294094976 382617345 A A A D B 277294095104 381889216 277294095232 381162819 277294095360 380438148 B 277294095488 379715198 277294095616 378993966 A D B 277294095744 378274445 277294096000 376840520 277294096128 376126105 B 277294096384 374702349 277428308992 456187820 A A D B 277428309120 455307530 277428309248 454429363 277428309376 453553313 B 277428309504 452679373 277428309632 451807537 A D B 277428309760 450937799 277428309888 450070153 277428310016 449204594 B 277428310144 448341115 277428310272 447479709 A A A A A D B 277428310400 446620372 277428310528 445763097 277428310656 444907878 B 277428310784 444054710 277428310912 443203586 A D B 277428311040 442354500 277428311168 441507447 277428311296 440662421 B 277428311424 439819416 277428311552 438978426 A A D B 277428311680 438139446 277428311808 437302469 277428311936 436467490 B 277428312064 435634504 277428312192 434803504 A D B 277428312320 433974485 277428312448 433147441 277428312576 432322366 B 277428312704 431499256 277428312832 430678103 A A A D B 277428312960 429858904 277428313088 429041651 277428313216 428226340 B 277428313472 426601521 277428313600 425792002 A D B 277428313728 424984402 277428313984 423374940 277428314112 422573066 B 277562526976 508911257 277562527104 507930176 A A D B 277562527232 506951459 277562527360 505975098 277562527488 505001086 B 277562527616 504029418 277562527744 503060086 A D B 277562527872 502093084 277562528000 501128404 277562528128 500166040 B 277562528256 499205985 277562528384 498248234 A A A A D B 277562528512 497292778 277562528640 496339612 277562528768 495388729 B 277562528896 494440122 277562529024 493493786 A D B 277562529152 492549712 277562529280 491607895 277562529408 490668329 B 277562529536 489731006 277562529664 488795921 A A D B 277562529792 487863067 277562529920 486932438 277562530048 486004027 B 277562530176 485077828 277562530304 484153835 A D B 277562530432 483232041 277562530560 482312440 277562530688 481395026 B 277562530816 480479793 277562530944 479566733 A A A D B 277562531200 477747113 277562531328 476840540 277562531584 475033837 B 277562531712 474133694 277562531840 473235683 A D B 277696744832 565279509 277696744960 564190287 277696745088 563103687 B 277696745216 562019702 277696745344 560938325 A A D B 277696745472 559859547 277696745600 558783363 277696745728 557709763 B 277696745856 556638741 277696745984 555570288 A D B 277696746112 554504399 277696746240 553441065 277696746368 552380279 B 277696746496 551322034
noncomputable def AEJ : CTN :=
  A A A A A A A D B 277696746752 549213136 277696746880 548162469 277696747008 547114314 D B 277696747136 546068663 277696747264 545025509 277696747392 543984846 A D B 277696747520 542946665 277696747648 541910961 277696747776 540877725 B 277696747904 539846951 277696748032 538818631 A A D B 277696748160 537792759 277696748288 536769328 277696748416 535748331 B 277696748544 534729760 277696748672 533713609 A D B 277696748800 532699872 277696748928 531688540 277696749184 529673068 B 277696749312 528668913 277696749568 526667734 A A A D B 277830962944 621967831 277830963072 620771108 277830963200 619577262 B 277830963328 618386286 277830963456 617198170 A D B 277830963584 616012906 277830963712 614830487 277830963840 613650904 B 277830963968 612474149 277830964096 611300214 A A D B 277830964224 610129090 277830964352 608960770 277830964480 607795246 B 277830964608 606632509 277830964736 605472552 A D B 277830964864 604315366 277830964992 603160944 277830965120 602009277 B 277830965248 600860359 277830965376 599714180 A A A A D B 277830965504 598570733 277830965632 597430011 277830965760 596292006 B 277830965888 595156709 277830966016 594024113 A D B 277830966144 592894210 277830966272 591766993 277830966400 590642454 B 277830966528 589520585 277830966656 588401380 A A D B 277830966912 586170926 277830967040 585059662 277830967296 582845026 B 277965180800 683500179 277965180928 682185695 A D B 277965181056 680874370 277965181184 679566195 277965181312 678261160 B 277965181440 676959257 277965181568 675660477 A A A D B 277965181696 674364811 277965181824 673072249 277965181952 671782783 B 277965182080 670496404 277965182208 669213103 A D B 277965182336 667932871 277965182464 666655700 277965182592 665381580 B 277965182720 664110503 277965182848 662842461 A A D B 277965183104 660315443 277965183232 659056451 277965183360 657800459 B 277965183488 656547457 277965183616 655297438 A D B 277965183744 654050393 277965183872 652806314 277965184000 651565191 B 277965184128 650327017 277965184256 649091784 A A A A A D B 277965184384 647859482 277965184512 646630103 277965184768 644180083 D B 277965184896 642959425 277965185024 641741658 278099398784 746218329 A D B 278099398912 744784607 278099399040 743354328 278099399168 741927480 B 278099399296 740504055 278099399424 739084043 A A D B 278099399552 737667433 278099399680 736254216 278099399808 734844383 B 278099399936 733437922 278099400064 732034826 A D B 278099400192 730635084 278099400320 729238686 278099400448 727845623 B 278099400576 726455886 278099400832 723686349 A A A D B 278099400960 722306530 278099401216 719556747 278099401344 718186763 B 278099401472 716820038 278099401600 715456563 A D B 278099401728 714096329 278099401856 712739327 278099401984 711385547 B 278099402112 710034980 278099402240 708687618 A A D B 278099402368 707343450 278099402624 704664662 278099402752 703330025 B 278233616896 809704260 278233617024 808150802 A D B 278233617152 806601068 278233617280 805055047 278233617408 803512730 B 278233617536 801974105 278233617664 800439161 A A A A D B 278233617792 798907889 278233617920 797380277 278233618048 795856315 B 278233618176 794335993 278233618304 792819299 A D B 278233618432 791306225 278233618688 788290891 278233618816 786788611 B 278233619072 783794773 278233619200 782303195 A A D B 278233619456 779330669 278233619584 777849702 278233619712 776372251 B 278233619840 774898307 278233619968 773427859 A D B 278233620096 771960898 278233620352 769037398 278233620480 767580838 B 278367834752 878568118 278367834880 876883350 A A A D B 278367835264 871853221 278367835520 868519834 278367835648 866859115 B 278367835776 865202365 278367835904 863549571 A D B 278367836032 861900722 278367836160 860255808 278367836288 858614816 B 278367836416 856977736 278367836544 855344556 A A D B 278367836672 853715266 278367836800 852089854 278367836928 850468309 B 278367837056 848850620 278367837184 847236775 A D B 278367837312 845626765 278367837440 844020579 278367837696 840819631 B 278367837824 839224848 278367838080 836046611 A A A A A A D B 278367838208 834463136 278502052864 946259621 278502053248 940836714 D B 278502053504 937243017 278502053632 935452604 278502053760 933666465 A D B 278502053888 931884587 278502054016 930106959 278502054144 928333568 B 278502054400 924799450 278502054528 923038699 A A D B 278502054656 921282137 278502054912 917781531 278502055040 916037465 B 278502055424 910830066 278502055680 907379018 A D B 278502055808 905659624 278502055936 903944301 278636271488 1008081143 B 278636271744 1004237940 278636272000 1000413036 A A A D B 278636272768 989047084 278636272896 987168484 278636273024 985294343 B 278636273152 983424648 278636273536 977842113 A D B 278636273664 975990077 278770489472 1080970840 278770490240 1068678003 B 278770490368 1066646221 278770490624 1062597123 A A D B 278770490880 1058567224 278770491136 1054556414 278770491392 1050564584 B 278904708480 1138380218 278904708736 1134064958 A D B 278904709120 1127630341 279038926336 1216343694 279038926848 1207148283 B 279173144576 1289077782 279307362304 1373376670 A A A A D B 279441580032 1460001260 279575797760 1548906371 279710015488 1640045351 B 279844233216 1733370107 279978450944 1828831124 A D B 280112668672 1926377499 280246886400 2025956968 280381104128 2127515931 B 280515321856 2230999488 280917975040 2552429823 A A D B 281052192768 2663037788 281186410496 2775277410 281454845952 3004402395 B 281589063680 3121160506 281857499136 3358742308 A D B 282528587776 3973265939 282662805504 4099142367 283468112000 4859954717 B 283468112128 4850758660 283468112256 4841584346 A A A D B 283468112384 4832431715 283468112512 4823300705 283468112640 4814191254 B 283468112768 4805103302 283468112896 4796036788 A D B 283468113024 4786991651 283468113152 4777967830 283468113280 4768965266 B 283468113408 4759983897 283468113536 4751023666 A A D B 283468113664 4742084510 283468113792 4733166372 283468113920 4724269192 B 283468114048 4715392911 283468114176 4706537470 A D B 283468114304 4697702810 283468114432 4688888873 283468114560 4680095600 B 283468114688 4671322934 283468114816 4662570816 A A A A A D B 283468114944 4653839189 283468115072 4645127994 283468115200 4636437176 D B 283468115328 4627766676 283468115456 4619116438 283468115584 4610486405 A D B 283468115712 4601876519 283468115840 4593286726 283468115968 4584716968 B 283468116096 4576167189 283468116224 4567637334 A A D B 283468116352 4559127347 283468116480 4550637173 283468116608 4542166755 B 283468116736 4533716039 283468116864 4525284970 A D B 283468116992 4516873494 283468117120 4508481554 283468117248 4500109098 B 283468117376 4491756071 283468117504 4483422418 A A A D B 283468117632 4475108086 283468117760 4466813021 283468117888 4458537170 B 283468118016 4450280479 283468118144 4442042895 A D B 283468118272 4433824364 283468118400 4425624835 283468118528 4417444254 B 283468118656 4409282568 283468118784 4401139726 A A D B 283468118912 4393015675 283468119040 4384910364 283468119168 4376823740 B 283468119296 4368755751 283468119424 4360706347 A D B 283468119552 4352675475 283468119680 4344663085 283468119808 4336669126 B 283468119936 4328693546 283468120064 4320736295 A A A A D B 283736555520 4551924208 284139208704 4900082019 284541861888 5248270476 B 290715877376 9332768106 291118530560 9447129772 A D B 291789619200 9582162207 292058054784 9597161408 292058054912 9575208023 B 292058055040 9550434133 292058055168 9522859734 A A D B 292058055296 9492506443 292058055424 9459397479 292058055552 9423557641 B 292058055680 9385013290 292058055808 9343792325 A D B 292058055936 9299924162 292058056064 9253439712 292058056192 9204371355 B 292058056320 9152752914 292058056448 9098619634 A A A D B 292058056576 9042008151 292058056704 8982956468 292058056832 8921503925 B 292058056960 8857691173 292058057216 8723154014 A D B 292058057344 8652517190 292058057472 8579695262 292058057600 8504734976 B 292058057728 8427684207 292058057856 8348591922 A A D B 292058057984 8267508144 292058058112 8184483924 292058058240 8099571304 B 292058058496 7924293774 292058058624 7834037587 A D B 292058058752 7742110373 292058058880 7648568596 292058059008 7553469500 B 292058059136 7456871066
noncomputable def AEK : CTN :=
  A A A A A A A D B 292058059392 7259411574 292058059520 7158669834 292058059648 7056667314 D B 292058059776 6953465123 292058059904 6849124881 292058060032 6743708678 A D B 292058060160 6637279038 292058060288 6529898878 292058060544 6312540405 B 292058060672 6202689544 292058060800 6092142989 A A D B 292058060928 5980965038 292058061056 5869220150 292058061184 5756972900 B 292058061440 5531229986 292058061568 5417863720 A D B 292058061696 5304253811 292058061824 5190464847 292058061952 5076561304 B 292058062080 4962607504 292058062208 4848667580 A A A D B 292058062336 4734805438 292058062592 4507568757 292058062720 4394320554 B 292058062848 4281402733 296487247872 4522521227 A D B 299171602432 4664067590 300647997568 4616538007 300647997696 4494939674 B 300647997824 4373868268 300647997952 4253388679 A A D B 300647998080 4133565213 300647998208 4014461555 300647998336 3896140731 B 300647998464 3778665077 300647998592 3662096204 A D B 300647998720 3546494959 300647998848 3431921397 300647998976 3318434746 B 300647999104 3206093374 300647999360 2985075450 A A A A D B 300647999616 2769316193 300647999872 2559248457 300648000000 2456479654 B 300648000128 2355288468 300648000256 2255724188 A D B 300648000512 2061667736 300648000896 1783949855 300648001152 1608221062 B 300648001664 1280795340 300648001920 1129676516 A A D B 300648002048 1057381282 300648002176 987302496 300648002432 853906694 B 300648002560 790642281 300648002816 671101007 A D B 300648003072 561020055 300648003328 460550930 300648003584 369821196 B 300648003840 288934345 300648004224 186226443 A A A D B 300648004352 156982527 300648004608 106003817 300648004992 48310569 B 300648005248 22331797 300648005632 1958320 A D B 303198142464 2838803 309237940352 707682 309506377344 85794 B 309506377472 85646 309506377600 85498 A A D B 309506377728 85351 309506377856 85204 309506377984 85057 B 309506378112 84911 309506378240 84764 A D B 309506378496 84473 309506378624 84328 309506378752 84183 B 309506378880 84038 309506379008 83894 A A A A A D B 309506379136 83750 309506379264 83607 309506379392 83463 D B 309506379520 83320 309506379776 83035 309506380032 82751 A D B 309506380160 82610 309506380288 82468 309506380416 82327 B 309506380544 82187 309506380672 82047 A A D B 309506380800 81907 309506381184 81488 309506381312 81349 B 309506381440 81211 309506381568 81073 A D B 309506381696 80935 309506381824 80797 309506381952 80660 B 309506382080 80523 309506382208 80386 A A A D B 309506382336 80249 309506382592 79977 309506382720 79842 B 309506382848 79706 309506383104 79437 A D B 309506383232 79302 309506383616 78901 309506383872 78634 B 309640595200 2010902 309640595328 2007433 A A D B 309640595456 2003972 309640595584 2000519 309640595712 1997073 B 309640595840 1993634 309640595968 1990203 A D B 309640596352 1979953 309640596480 1976551 309640596608 1973157 B 309640596736 1969769 309640596864 1966389 A A A A D B 309640596992 1963017 309640597120 1959651 309640597248 1956293 B 309640597376 1952942 309640597504 1949598 A D B 309640597632 1946261 309640597760 1942931 309640597888 1939609 B 309640598144 1932985 309640598272 1929683 A A D B 309640598400 1926389 309640598528 1923102 309640598656 1919822 B 309640598784 1916549 309640598912 1913282 A D B 309640599296 1903525 309640599424 1900287 309640599552 1897055 B 309640599680 1893830 309640599808 1890612 A A A D B 309640599936 1887401 309640600064 1884197 309640600192 1880999 B 309640600320 1877809 309640600448 1874625 A D B 309640600576 1871447 309640601216 1855662 309640601472 1849394 B 309640601600 1846271 309774812928 6473116 A A D B 309774813056 6461951 309774813184 6450810 309774813312 6439693 B 309774813440 6428600 309774813568 6417530 A D B 309774813696 6406485 309774813824 6395464 309774813952 6384466 B 309774814080 6373491 309774814208 6362541 A A A A A A D B 309774814336 6351614 309774814464 6340710 309774814592 6329830 D B 309774814720 6318973 309774814848 6308139 309774814976 6297328 A D B 309774815104 6286541 309774815232 6275777 309774815360 6265036 B 309774815488 6254317 309774815616 6243622 A A D B 309774815744 6232949 309774815872 6222300 309774816000 6211673 B 309774816128 6201069 309774816256 6190487 A D B 309774816384 6179928 309774816768 6148385 309774816896 6137916 B 309774817152 6117044 309774817280 6106641 A A A D B 309774817408 6096261 309774817536 6085902 309774817792 6065251 B 309774817920 6054958 309774818432 6014005 A D B 309774818816 5983517 309774819072 5963299 309774819328 5943166 B 309909030656 13476176 309909030784 13452932 A A D B 309909030912 13429738 309909031040 13406594 309909031168 13383500 B 309909031296 13360455 309909031424 13337460 A D B 309909031552 13314515 309909031680 13291619 309909031808 13268772 B 309909031936 13245974 309909032064 13223225 A A A A D B 309909032192 13200525 309909032320 13177874 309909032448 13155271 B 309909032576 13132717 309909032704 13110210 A D B 309909032832 13087753 309909032960 13065343 309909033088 13042981 B 309909033216 13020667 309909033344 12998401 A A D B 309909033472 12976182 309909033600 12954011 309909033728 12931887 B 309909033856 12909810 309909033984 12887781 A D B 309909034112 12865798 309909034240 12843862 309909034368 12821973 B 309909034496 12800131 309909034624 12778335 A A A D B 309909034752 12756585 309909034880 12734882 309909035008 12713225 B 309909035136 12691614 309909035264 12670048 A D B 309909035520 12627055 309909035648 12605627 309909035776 12584244 B 309909035904 12562907 309909036032 12541615 A A D B 309909036160 12520367 309909036544 12456896 309909036800 12414804 B 309909037056 12372891 310043248512 22982730 A D B 310043248640 22943106 310043248768 22903567 310043248896 22864113 B 310043249024 22824744 310043249152 22785460 A A A A A D B 310043249280 22746261 310043249408 22707145 310043249536 22668114 B 310043249664 22629167 310043249792 22590303 A D B 310043249920 22551523 310043250048 22512825 310043250176 22474211 B 310043250304 22435680 310043250432 22397231 A A D B 310043250560 22358864 310043250688 22320580 310043250816 22282377 B 310043250944 22244256 310043251072 22206217 A D B 310043251200 22168259 310043251328 22130382 310043251456 22092586 B 310043251584 22054871 310043251840 21979681 A A A D B 310043251968 21942206 310043252096 21904812 310043252224 21867496 B 310043252352 21830261 310043252480 21793104 A D B 310043252864 21682108 310043252992 21645266 310043253120 21608503 B 310043253248 21571818 310043253376 21535210 A A D B 310043253504 21498680 310043253632 21462228 310043253760 21425853 B 310043253888 21389554 310043254016 21353333 A D B 310043254144 21317188 310043254784 21137608 310177466368 34991728 B 310177466496 34931425 310177466624 34871252 A A A A D B 310177466752 34811209 310177466880 34751295 310177467008 34691510 B 310177467136 34631853 310177467264 34572324 A D B 310177467392 34512923 310177467520 34453650 310177467648 34394504 B 310177467776 34335485 310177467904 34276593 A A D B 310177468032 34217826 310177468160 34159186 310177468288 34100671 B 310177468416 34042281 310177468544 33984017 A D B 310177468672 33925877 310177468800 33867861 310177468928 33809969 B 310177469056 33752201 310177469184 33694556 A A A D B 310177469312 33637035 310177469440 33579636 310177469568 33522359 B 310177469696 33465204 310177469824 33408172 A D B 310177469952 33351260 310177470080 33294470 310177470336 33181252 B 310177470464 33124823 310177470592 33068515 A A D B 310177470720 33012326 310177470848 32956256 310177470976 32900305 B 310177471232 32788760 310177471360 32733164 A D B 310177471488 32677686 310177471616 32622326 310177471744 32567083 B 310177471872 32511957
noncomputable def AEL : CTN :=
  A A A A A A A D B 310311684224 49489452 310311684352 49404201 310311684480 49319134 D B 310311684608 49234250 310311684736 49149549 310311684864 49065029 A D B 310311684992 48980692 310311685120 48896535 310311685248 48812559 B 310311685376 48728763 310311685504 48645148 A A D B 310311685632 48561711 310311685760 48478453 310311685888 48395374 B 310311686016 48312472 310311686144 48229748 A D B 310311686272 48147201 310311686400 48064831 310311686656 47900618 B 310311686784 47818774 310311686912 47737105 A A A D B 310311687040 47655611 310311687168 47574290 310311687296 47493143 B 310311687424 47412168 310311687552 47331367 A D B 310311687680 47250737 310311687936 47089992 310311688064 47009876 B 310311688320 46850154 310311688448 46770548 A A D B 310311688704 46611842 310311688832 46532741 310311688960 46453808 B 310311689088 46375043 310311689216 46296444 A D B 310311689344 46218012 310311689472 46139746 310311689600 46061645 B 310311689728 45983710 310311689856 45905939 A A A A D B 310311690240 45673612 310445902080 66460711 310445902208 66346275 B 310445902336 66232085 310445902464 66118141 A D B 310445902592 66004442 310445902720 65890987 310445902848 65777776 B 310445902976 65664808 310445903104 65552082 A A D B 310445903232 65439599 310445903360 65327356 310445903488 65215354 B 310445903616 65103592 310445903744 64992069 A D B 310445903872 64880785 310445904000 64769739 310445904128 64658931 B 310445904256 64548359 310445904384 64438024 A A A D B 310445904512 64327924 310445904640 64218060 310445904768 64108430 B 310445904896 63999034 310445905024 63889871 A D B 310445905152 63780941 310445905280 63672243 310445905408 63563776 B 310445905664 63347535 310445905792 63239759 A A D B 310445905920 63132212 310445906048 63024894 310445906560 62597896 B 310445906688 62491712 310445907072 62174509 A D B 310445907328 61964157 310445907584 61754695 310445907712 61650296 B 310445907840 61546117 310445907968 61442158 A A A A A D B 310580120064 85741032 310580120192 85593525 310580120320 85446335 D B 310580120448 85299462 310580120576 85152904 310580120704 85006660 A D B 310580120832 84860731 310580120960 84715114 310580121088 84569810 B 310580121216 84424817 310580121344 84280135 A A D B 310580121472 84135763 310580121600 83991700 310580121728 83847945 B 310580121856 83704497 310580121984 83561357 A D B 310580122112 83418522 310580122240 83275992 310580122368 83133766 B 310580122496 82991844 310580122624 82850225 A A A D B 310580122752 82708908 310580122880 82567892 310580123008 82427176 B 310580123136 82286760 310580123264 82146643 A D B 310580123648 81728078 310580123776 81589149 310580124416 80898916 B 310580124544 80761746 310580124672 80624867 A A D B 310580124800 80488278 310580124928 80351978 310580125056 80215967 B 310580125184 80080243 310580125312 79944807 A D B 310580125440 79809656 310580125568 79674791 310580125696 79540211 B 310714337792 107755792 310714337920 107570412 A A A A D B 310714338048 107385430 310714338176 107200845 310714338304 107016657 B 310714338432 106832865 310714338560 106649466 A D B 310714338688 106466462 310714338816 106283849 310714338944 106101629 B 310714339072 105919798 310714339200 105738357 A A D B 310714339456 105376639 310714339712 105016466 310714339840 104836957 B 310714340096 104479089 310714340224 104300727 A D B 310714340480 103945144 310714340608 103767921 310714340736 103591075 B 310714340864 103414606 310714340992 103238513 A A A D B 310714341120 103062794 310714341248 102887449 310714341376 102712477 B 310714341632 102363648 310714341760 102189788 A D B 310714341888 102016298 310714342016 101843176 310714342272 101498032 B 310714342400 101326008 310714342528 101154348 A A D B 310714342784 100812119 310714342912 100641547 310714343040 100471335 B 310714343296 100131991 310714343424 99962856 A D B 310848555648 132041989 310848555776 131814925 310848555904 131588348 B 310848556032 131362259 310848556288 130911535 A A A A A A D B 310848556416 130686897 310848556544 130462742 310848556672 130239067 D B 310848556800 130015871 310848556928 129793153 310848557056 129570912 A D B 310848557312 129127856 310848557440 128907038 310848557568 128686691 B 310848557824 128247410 310848557952 128028472 A A D B 310848558080 127810001 310848558208 127591996 310848558336 127374456 B 310848558464 127157379 310848558592 126940764 A D B 310848558848 126508918 310848558976 126293683 310848559232 125864585 B 310848559360 125650720 310848559488 125437309 A A A D B 310848559616 125224350 310848559744 125011844 310848560000 124588181 B 310848560128 124377023 310848560256 124166312 A D B 310848560384 123956048 310848560640 123536852 310848560768 123327919 B 310848560896 123119427 310848561024 122911376 A A D B 310848561152 122703764 310982773632 158453664 310982773760 158181415 B 310982773888 157909751 310982774016 157638670 A D B 310982774144 157368171 310982774272 157098251 310982774400 156828910 B 310982774528 156560147 310982774656 156291958 A A A A D B 310982774784 156024344 310982774912 155757303 310982775040 155490832 B 310982775168 155224932 310982775296 154959599 A D B 310982775424 154694833 310982775552 154430633 310982775680 154166996 B 310982775936 153641409 310982776064 153379455 A A D B 310982776192 153118059 310982776320 152857220 310982776448 152596937 B 310982776576 152337207 310982776704 152078030 A D B 310982776832 151819403 310982776960 151561327 310982777344 150790380 B 310982777472 150534488 310982777728 150024330 A A A D B 310982777856 149770061 310982777984 149516331 310982778112 149263139 B 310982778240 149010482 310982778496 148506769 A D B 310982778624 148255712 310982778752 148005184 310982778880 147755186 B 311116991616 187142364 311116991744 186821100 A A D B 311116991872 186500525 311116992000 186180638 311116992128 185861436 B 311116992384 185225082 311116992512 184907927 A D B 311116992640 184591450 311116992768 184275650 311116993024 183646073 B 311116993152 183332294 311116993280 183019184 A A A A A D B 311116993408 182706742 311116993536 182394967 311116993664 182083857 B 311116993792 181773410 311116993920 181463624 A D B 311116994048 181154498 311116994176 180846030 311116994304 180538218 B 311116994432 180231061 311116994560 179924558 A A D B 311116994816 179313502 311116994944 179008947 311116995200 178401775 B 311116995328 178099155 311116995456 177797176 A D B 311116995584 177495837 311116996096 176296846 311116996352 175701147 B 311116996480 175404242 311116996608 175107963 A A A D B 311251209600 218072703 311251209984 216952985 311251210240 216210498 B 311251210496 215471184 311251210624 215102713 A D B 311251211008 214002014 311251211136 213636680 311251211392 212908348 B 311251211520 212545346 311251211776 211821661 A A D B 311251211904 211460973 311251212032 211101053 311251212160 210741898 B 311251212288 210383507 311251212416 210025878 A D B 311251212672 209312896 311251212800 208957540 311251212928 208602937 B 311251213440 207192029 311251214208 205097959 A A A A D B 311251214336 204751524 311385427840 250348074 311385428096 249491663 B 311385428224 249064832 311385428352 248638912 A D B 311385428480 248213903 311385428608 247789802 311385428736 247366607 B 311385428864 246944314 311385428992 246522923 A A D B 311385429120 246102429 311385429376 245264130 311385429504 244846319 B 311385429632 244429397 311385429760 244013362 A D B 311385429888 243598213 311385430144 242770559 311385430400 241946418 B 311385430528 241535659 311385430656 241125771 A A A D B 311385430912 240308601 311385431552 238280772 311385431680 237877777 B 311385431936 237074339 311385432064 236673892 A D B 311519645952 285042513 311519646592 282615684 311519646976 281171981 B 311519647232 280214631 311519647616 278786235 A A D B 311519647744 278312127 311519648128 276895837 311519648256 276425743 B 311519648384 275956647 311519648512 275488545 A D B 311519648896 274090184 311519649024 273626036 311519649152 273162871 B 311519649408 272239476
noncomputable def AEM : CTN :=
  A A A A A A A D B 311519649792 270861689 311653863936 322283826 311653864192 321183685 D B 311653864448 320088236 311653864960 317911314 311653865472 315752870 A D B 311653865600 315216124 311653866240 312549438 311653866368 312019489 B 311653866496 311490663 311653866624 310962958 A A D B 311653866752 310436369 311653866880 309910895 311653867136 308863279 B 311653867392 307820085 311653867520 307300140 A D B 311788083584 353680532 311788083968 351882991 311788084480 349503998 B 311788084608 348912394 311788085248 345973083 A A A D B 311922300160 401588826 311922301440 394809929 311922301568 394139934 B 311922301696 393471359 311922301952 392138459 A D B 311922302336 390149674 311922302464 389489549 311922302976 386862971 B 312056518784 441026325 312056519040 439529159 A A D B 312056519808 435075621 312056520576 430678353 312056520704 429950886 B 312190736512 487458018 312190737664 480066488 A D B 312190738432 475216546 312324955904 524408768 312324956160 522638312 B 312459173760 573161343 312459173888 572193205 A A A A D B 312593391616 623856911 312727609344 677603799 312861827072 733406929 B 312996044800 791238073 313130262528 851067722 A D B 313264480256 912865110 313398697984 976598221 313532915712 1042233817 B 313667133440 1109737447 313801351168 1179073469 A A D B 313935568896 1250205074 314069786624 1323094300 314204004352 1397702054 B 314338222080 1473988139 315009310720 1879111914 A D B 315277746176 2051385388 315814617088 2411370272 316485705728 2886098058 B 317022576640 3281491105 317425229824 3584782803 A A A D B 317827883136 3885544523 317827883264 3878986917 317827883392 3872443141 B 317827883520 3865913159 317827883648 3859396938 A D B 317827883776 3852894441 317827883904 3846405636 317827884032 3839930486 B 317827884160 3833468957 317827884288 3827021016 A A D B 317827884416 3820586627 317827884544 3814165757 317827884672 3807758371 B 317827884800 3801364436 317827884928 3794983918 A D B 317827885056 3788616783 317827885184 3782262996 317827885312 3775922526 B 317827885568 3763281398 317827885696 3756980674 A A A A A D B 317827885824 3750693133 317827885952 3744418741 317827886080 3738157464 D B 317827886208 3731909272 317827886336 3725674130 317827886464 3719452006 A D B 317827886592 3713242867 317827886720 3707046681 317827886848 3700863415 B 317827886976 3694693037 317827887104 3688535515 A A D B 317827887232 3682390817 317827887360 3676258910 317827887488 3670139764 B 317827887616 3664033345 317827887744 3657939622 A D B 317827887872 3651858563 317827888000 3645790137 317827888128 3639734313 B 317827888256 3633691059 317827888384 3627660343 A A A D B 317827888512 3621642135 317827888640 3615636403 317827888768 3609643116 B 317827889024 3597693755 317827889152 3591737619 A D B 317827889280 3585793805 317827889536 3573943022 317827889792 3562141161 B 317827889920 3556258500 317827890048 3550387980 A A D B 317827890176 3544529570 317827890304 3538683239 317827890432 3532848958 B 317827890688 3521216428 317827890816 3515418119 A D B 317827890944 3509631742 317827891072 3503857266 317827891200 3498094663 B 326417826048 7666295460 326417826176 7647939783 A A A A D B 326417826304 7627332364 326417826432 7604489231 326417826560 7579427709 B 326417826688 7552166405 326417826944 7491125209 A D B 326417827200 7421539578 326417827456 7343602922 326417827584 7301568583 B 326417827712 7257527540 326417827840 7211509179 A A D B 326417827968 7163543985 326417828096 7113663517 326417828224 7061900393 B 326417828352 7008288261 326417828480 6952861776 A D B 326417828608 6895656581 326417828736 6836709276 326417828864 6776057395 B 326417829248 6584263132 326417829376 6517186090 A A A D B 326417829632 6378563223 326417829760 6307103327 326417829888 6234269622 B 326417830016 6160106854 326417830144 6084660428 A D B 326417830272 6007976380 326417830400 5930101347 326417830528 5851082538 B 326417830784 5689805104 326417830912 5607643480 A A D B 326417831040 5524532023 326417831168 5440520342 326417831296 5355658432 B 326417831552 5183585664 326417831680 5096476453 A D B 326417831808 5008720248 326417831936 4920368510 326417832064 4831472902 B 326417832576 4471490174 326417832704 4380654875 A A A A A A D B 326417832960 4198341943 326417833216 4015520057 326417833472 3832604937 D B 326417833984 3468145225 335007768832 3604226111 335007769088 3411384587 A D B 335007769216 3315679503 335007769472 3125958757 335007769600 3032044825 B 335007769728 2938828777 335007769984 2754687635 A A D B 335007770112 2663859650 335007770240 2573923713 335007770496 2396914845 B 335007770624 2309933539 335007770752 2224027481 A D B 335007770880 2139240568 335007771392 1812133475 335007771904 1506224467 B 335007772160 1361974004 335007772800 1028919399 A A A D B 335007772928 967282472 335007773184 849208411 335007773312 792822720 B 335007773568 685474088 335007774080 493067178 A D B 335007774848 262289444 335007774976 230748790 335007775616 103239414 B 335007776256 26382087 335007776512 9811531 A A D B 335007776640 4546071 335007776768 1284548 343597711488 335466 B 343866152832 183649 343866153984 181134 A D B 343866155008 178934 344000371584 1982632 344000372736 1955558 B 344134590464 5637625 344268807168 11365400 A A A A D B 344268808192 11227364 344403025920 18725853 344537242880 28391934 B 344537243648 28133016 344671460736 39749874 A D B 344671461376 39447622 344805679104 52667281 344939896832 67788449 B 345074114560 84806424 345208332288 103715347 A A D B 345342550016 124508209 345476767744 147176846 345610985472 171711948 B 345745203200 198103059 345879420928 226338585 A D B 346013638656 256405797 346147856384 288290837 346282074112 321978725 B 346416291840 357453368 346550509568 394697565 A A A D B 346818945024 474420342 346953162752 516859070 347087380480 560987671 B 347624251392 753933456 347892686848 859909317 A D B 348563775488 1150744662 348832210944 1276776586 350308605952 2053678650 B 351248130048 2604886892 352187654528 3167653101 A A D B 352187654912 3153217721 352187655040 3148424210 352187655168 3143639804 B 352187655552 3129341019 352187655680 3124592832 A D B 352187655808 3119853648 352187655936 3115123447 352187656064 3110402208 B 352187656192 3105689910 352187656448 3096292059 A A A A A D B 352187656576 3091606465 352187656832 3082261840 352187656960 3077602768 B 352187657088 3072952497 352187657344 3063678277 A D B 352187657472 3059054289 352187657856 3045234572 352187657984 3040645350 B 352187658368 3026929463 352187658496 3022374695 A A D B 352187658752 3013290833 352187659008 3004241077 352187659264 2995225272 B 352187659520 2986243265 352187659648 2981764889 A D B 352187659776 2977294906 352187659904 2972833296 352187660032 2968380041 B 352187660160 2963935123 352187660544 2950650199 A A A D B 352187660672 2946238439 352187661056 2933052544 352187661696 2911239567 B 352187661824 2906901335 352187662336 2889629010 A D B 360777597184 6276273068 360777597824 6187672120 360777597952 6164511584 B 360777598080 6139573634 360777599616 5709036411 A A D B 360777600512 5357068919 360777601280 5006134257 360777601408 4943797671 B 360777601536 4880461173 360777602304 4481627506 A D B 360777602944 4129059787 360777603968 3540494144 360777604736 3090685922 B 360777604864 3015769312 360777605120 2866362512 A A A A D B 369367539968 2954256535 369367540352 2718556366 369367540608 2563486011 B 369367541120 2259807421 369367541888 1825273223 A D B 369367542656 1423165980 369367542784 1359832320 369367544320 696961024 B 369367544448 650613837 369367544960 480168851 A A D B 369367545984 214421956 369367546112 188501172 369367547392 20996682 B 369367547904 877209 377957482624 155404 A D B 378360143872 1968681 378628579328 10144358 378897014784 24676516 B 379568103424 88725313 379702321152 106253672 A A A D B 380641845248 272054995 381178716160 399632768 381447151616 471987620 B 381849804800 590810373 382386675712 767554403 A D B 383191982080 1068748150 386547433472 2427023636 395137371264 4612561434 B 395137372800 4033411523 395137374464 3280735883 A A D B 395137376256 2408621223 403727311360 2334426415 403727312384 1825276152 B 403727312512 1763901740 403727313536 1297756140 A D B 403727313664 1243053903 403727315712 505956838 403727315840 469666645 B 403727318784 6045255
noncomputable def table : CTN :=
  A A A A A AFZ 68459495232 2359601656 AFa 70967691872 2061158591 A AFb 99807753524 8668677814 AFc 102936707072 320394232 A A AFd 105092587520 863112789 AFe 111669256704 28791006768 A AFf 136365341952 652443638 AFg 138915481344 322791191 A A A AFh 139989224064 1430242018 AFi 141734057984 4453786606 A AD1 168711847552 150265964 AD2 172872598784 98365770 A A AD3 173677911040 427320924 AD4 174751652992 1283768053 A AD5 180388803584 10423856546 AD6 206561282816 428628 A A A A AD7 207366589696 112797142 AD8 208171899648 395559533 A AD9 209245640448 1089663738 AEA 223338514176 15452413173 A A AEB 241055277056 5823791 AEC 241994795648 158481188 A AED 242934321152 499999867 AEE 244008065280 1084616349 A A A AEF 266288227328 4839337425 AEG 275817695744 40323440 A AEH 276623005568 183740915 AEI 277696746624 550266322 A A AEJ 292058059264 7358831975 AEK 310177472512 32238069 A AEL 311519649536 271779243 AEM
set_option hygiene false in
local macro "C " x0:ident x1:ident : command => `(command|
theorem $x0 : $x1 = true := by decide +kernel)
C AEQ AFZ.BX
C AER AFa.BX
C AET AFb.BX
C AEU AFc.BX
C AEV AFd.BX
C AEW AFe.BX
C AEX AFf.BX
C AEY AFg.BX
C AEZ AFh.BX
C AEa AFi.BX
C qG AD1.BX
C qH AD2.BX
C qI AD3.BX
C qJ AD4.BX
C qK AD5.BX
C qL AD6.BX
C qM AD7.BX
C qN AD8.BX
C qO AD9.BX
C qP AEA.BX
C qQ AEB.BX
C qU AEC.BX
C qV AED.BX
C qW AEE.BX
C qX AEF.BX
C qZ AEG.BX
C qd AEH.BX
C qg AEI.BX
C qo AEJ.BX
C qu AEK.BX
C qv AEL.BX
C qw AEM.BX
theorem qz : table.BX = true := by
  simp only [table, CTN.BX, AEQ, AER, AET, AEU, AEV, AEW, AEX, AEY, AEZ, AEa, qG, qH, qI, qJ, qK, qL, qM, qN, qO, qP, qQ, qU, qV, qW, qX, qZ, qd, qg, qo, qu, qv, qw, Bool.true_and, Bool.and_true]
  decide +kernel
def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30464, true),
  (30464, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 458752, false)]
theorem oW : AG.Bd table 25326800 (SC / 2) 458752 cover0 = true := by decide +kernel
def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 31488, true),
  (31488, 31616, true),
  (31616, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 75264, false),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 87552, true),
  (87552, 88064, true),
  (88064, 270336, false)]
theorem oX : AG.Bd table 48244400 (SC / 2) 270336 cover1 = true := by decide +kernel
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
  (59904, 60160, true),
  (60160, 60416, true),
  (60416, 74752, false),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 245760, false)]
theorem oY : AG.Bd table 52857300 (SC / 2) 245760 cover2 = true := by decide +kernel
def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 31488, true),
  (31488, 31616, true),
  (31616, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 75264, false),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 87552, true),
  (87552, 88064, true),
  (88064, 270336, false)]
theorem oZ : AG.Bd table 48244400 (SC / 2) 270336 cover3 = true := by decide +kernel
def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30464, true),
  (30464, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 458752, false)]
theorem oc : AG.Bd table 25326800 (SC / 2) 458752 cover4 = true := by decide +kernel
def bits : ℕ := 0x200ccaa9990889c89c89c8800022406333ba664222722722722006011390022332033088a532601a664222303394a4198440318c9883bc80ee553307750e3a9dcaa198ce494a6403ba80728ca99dcaa660753ba82bb812a272389388e1ce321ce2993970a28528c98a14a262ccc8791453944728e72887284e51930e510a72898f332ea772a83ba83b85152f2a772a8cc66252612772a8d2334ccc921010982318466990c8889c89c89c8800000c66999088c8aac8ac88001006332aa664223232322001190088a5324a4198440cc40cd451451c53954728ccee3392a92990019a9dc6a6a00225533b9981233053914534c92ab2ee0ef2492482084820722ae7204ab9c845d41092418a5d4dc298454199315127104899c4241153140871039a8c9ac812a72ae0909ac92e1100d4526a3b86708a64c384d2e2af2039c65e412262080af2628b8530e1e5440c5c18209b8c804dc4082484dc654dc28a38eb2489b8464c9082965c912208498b8310a298bc9b8902e0de4dd64126e59089a880e62a899c43822614c492a204404c6419c404c37195391c51224a9cb8492a61925c22638a4871063261a56492b982c9cc21151dc5c082a45c5060826e20413154b9829ba42113028513734829530454403149839a4d45730273088329cd21538b81288ef332384c84a214e2e2ccaa83bc848d440c209b8810c046ae1808a81537950e30a845c05971ab84c6400baa43aa4dd4310461310e65411c671071cc4e2186383a8c8e0564d641c6b2e0e4e111239384ce2a0ce20291a9c2099c5532f2071ce32f2144035790826e24ae11a882c860441370438e22e022e72022e08908bc81702f26ae24a3708441e4957184c902e25e4937254235190338ea2299c42c8e1c6471e4c70e3249ac8728e5c4964ea0e4e508859394267170045c73701171aa41104a150ca13106549ca119c5c53ccc854caa893c8655333b8ccaa069199553332084061199553219111919191000112073b8cd3321117917917910008c81de640661114a6419a5224c22008c64c40aa6602acbb8e033550239dc453a8650cee332ac9dc664a5320ef20053b899caea6600a33972abb8004eb226770246a32e1838e6b218444ee399aa8111321322081c4795703950402722127205c055c4a859145917391557041cc1813714aaba64c1240dc71c4b9c8931553700d2155734c89311917300a4c1791025261a5c6440e61cde643819132e2a07391049ac8144d44922649221d43ac8751c759135910c50748a9c860871c64d49041930a20c8a2b8a2b88a714e326b22ea638e0c054d452013514ba9a640b2715062484ac982482959051c654148e38832b262a08390b228b262ae60cce9979070de640ae1351c1a8648a2c9ac8931321d326ae0d437153033a54d320a254c2a64ba5e41a4f222260e24ce93c9845dc00548b98b964c400a19379372c828a26e1459705170b2057390537149055c1254924492455ce45cc5242c8a38e61ac8b9a8a1871417314b982a5cd53228e3862926f2189b8284dd4142e654c8611173029952e6159105142a4c34b9644c450a925ccb20e51caf2591c50b2e2125391412989105471e471e4492454e44912593141492b209471c419052b262e63859140996445145317351c14c437498ea9912214c0c8a0964c4c0c4dc13a932e4ac98a29cb214e5924e18932c9219b8e261cd472a64299ca972c981964c4440e59308bba8242e498c802171c2723203706e6220c4881139501b8c8122ea212ea04197041906a0d441a861a8cba8c8e2818632ae23920d22ea09248b859244514c514e4518a39175193570c314709575914470975909ab8440a23950f2080a8b920921510548a9210c3924545e5490e21445145e54dc3b8c2262029a5d430e085175102e04408ba9a55c1c6157088281574ab826131023199970514285c7099465e450a104dca20650ca62510c50a272025711492b81925430c430c6410655c64102517149082a249430e491242a2f26e1851144b94645145793750c15e4730b86a1103215c488a4945e5c1e5cc91a82260a8b85194408c05ca208ee69706ea1942215c6509945c1ca2f332a0c0e398aa434b8871a497139100c37951ce419c72f204408b899019173149152b208a0a722a1e430e4439873506e186eb21cc71cd431c6b22b2239214e29590438eb214579151c711c7190ce186ea28a62b88a2b8a71959170c10a39145449061a8a5430e430e44718e39a8a2b8a7228a628e454641a9219d2b208e31c54314e39a8e19d6431c6a2c8c8b9a860414a8820454d402a209aba53224450ea990471c54708a714540acc8a8911454c8750ea991321115312484549370d32e064506a112434a8691462ca895119503228a1106a0d422045332ae0414ca82e609c694c892454e34b9c8738e47149152159243a655d412b24ba98e311c690a64919c2971d2739088890e32c8732a454b86549ccb22203728a721cb2372c8925644882a1cc790c3912491591125904a38e20c8295917025124a187248921519125914349649117314096441704d492422099cae0829925c653985119d2519d32590e32c85938c253a4659088a849e4225770302e308c5d320328ba65404629929dcccaa7719897092a8d2673ba66649080980954e1718cd3219111919191012320202853b954673211191008cc8114a6408c92019cde420ee154701cde4aa339b821191199050a772a88cc24814aa66067750c30e33714519828b228898a3944394529919ba9dcaa3302330888820e91984523299019cde40a55330066772a88819dd430c38cdc514661451ca29930e51ca3239472885194c8cdd4ee55119c83ba46694ca4154d208c2908d26110152a3100655311c8c9883872a8ce6f203b954cc03b9a9dd4053577030104dd644333070cf238f238889871c33c88831de470e9531c6f219c718ef23888870ce3238e711e64cdc514514b228b228889850cb220c559142b98a3590ca28cb228888a28a511664cc28a2888851472c888a71d41d5263b8a7591c7514e3ac8e51cb222261472c8671d4514c7714eb22214729c833cb832c9d471d4591c75264c33a5c519d6428e4e3a8e548a63b8eb239472c8888e28e511ca29ca332394539447286728c8b3266ea772a86672072a9982ab82a8ae92a9dc7919a53207799002a899dc52aa9980ee185063ba8c871e64dcd43a9ddd40331450e5191c59335977033900414cba988912490e18c8950c220ccba80cb81901abc86110c4926ea184419975310c0230ab8c64015185d4620c633267238e073110321cc25c2621c43b87708871939507931c191c1388a704e23cc9ab89c818ee32243a54c4a83a544dc411d323824c5424735179009ac804d65c711071d262a1871d262ae0e6a0c2ae3888708cca870c8e11e6418710226b2181e45411271539702390e39708861d221d226a085492e2a38938a9b8e31c6e110e332a638e9901cc5641d65c1d6423b88e3871350dc3384e20a665471e4707150715390e3970e950ea691de541e54e1a4f211371907990e31c6e2383a82721838a8272ea38443a84c1e46a708dc4091514d41d453571c4730ea708dc408ce333266e1428a727224551122a88590a60a139114511c550aa110a3272e24a0945c51452825137053799513029b865510229c8a08824c5c0722ea0dc1ba8a23228a218510a26e0591705973506e38d42326e1453914510537154509464508514dca29464dd4428509513714292531750537061751445c5086152215226e28514b8a2a5cd451823508b98a14537154328b82b8a6e504a26a2142845c50a2e60a2e09a8cc8a142e315442811b8571a8a2e298a508d46402e39b82b8dd45114c508d4408ca33267248e14e23998e19472b88515c471cc28a72a38e63ab885388e515c4ce645020c9871c4dc28b262ba889093171222ba88a143220ef22814c65d418ef2388a105390ba898751422244244dc144c1c7531750a604dc710a611ca175130a290e3a844e64714e21e41465492b8e1e5422b898a29c4388538a8ae38ea105c4c70e26999714728850a2f23a8515e423a89828983944dc750a2b984a2144599914e504e510ce51ca299751309109712ea26145310ddc4886a195d4418a164c64105711c4a8957139704a88a1e43ca89c8628a63924b98e49cd465d40921390e384e5c2825390c71cc33acba8e3a888648e382b2228e38eb227208c70b2165c4712a255c4e5c3143c87951143c92a27238c72924b927511ca49c75139751230c8138e72e14721ca39751ca226187314530a6e32185388e29c4e541ce41cab830de429e5423942e238e2545711c5389c8e38a710e272a1c723ab871c86a7089b851261a8c839443944e5c28af2a0cb20e5c23a8850a32164e45147288a72e49d45384a2614539394139442c9ca137510548e3aa4c448ae22495152e26e247510e3a8a4c38ea2249724ea26ea4849098e09cdc0986a18435751c75088871d5221c751498515c5214571370e3a8a438ea261c75148728a4dd4908c71b8a3046ea288985388538985388538a4d432b8670d457088538a47498e91a8ae29c226e1ca21452604428a4dc750ca2b84a21452298a3728e51314e5144537510515c2214e1130a22c826a1c4131e4ae3321c61b8ea2286571c47314e11b8e33a8890b22098e29c4737145114c51446ea3946111ca131c653846e19ca119d46414522987148dc548c51ba8e5088a6194e11b8e508cea2046728cc99cba807353c898e3874994f214f211151c71c6710e714cc8e18e1194e2995199ddc505791429ca2e1643945c6638e69993b95541dd40dc1ba9dcaa319980ee553301cd4eea055770e3314194466a383388cc70a7130e3494e2335749dcaa90ccd333205533040aa193b95404aa39308cc08cd299080772a9983ba83b8a38a71d65d42a89dcaa0eea0ee0ee59509dcaa3308cc0aa660e772a8d2119a6643222323232200001cee999088c8aac8ac880008c854a6494821103bc80ee3355033b8cca52ac9320330773060209de44312390271cb89a9dc66aa00e389c89dccc01872e32ee041c72262067790015739151c289d4ee18591a8609c6a77198550ea7706a29dc6699907790aa0d4661d45199dc51dc719a66419d2191113b8cc004a727713301257197703311c04b222c8513a4ee29d2b2385938d251c98e48ce92c8444ee335154aa152554ccc820a12aa643222322ab22b22000201dcaa999088bc8bc8bc8800464022294c92924220775142860c22550ca7719c9dcaa4a640ef3200eea333aba804c955c66ee009dc15c4515c220aa899819882082492024838ca9b8802a6e29935240410f2135730ae9952445e5408e4011971c80932ae2890720375917510055c54c02975104d3203ac85d4331c69908b834b84e54c4031c898802ab8cbc920298ba4c2b83062b20f2618e492e722097390e64920a5ce455cc2830d452e699170520a513040c9202f261e471457931730224c398b9a8805cca29975900dc55971c83265c2b8105644c8e25e4438e4712e39c8ab8862819055c4c04157488269970c5041c879171c2a2094dc1446e94ca867262920a1931471c925ce472434bca8e4a89b82b985299702859737092157265640e5971c81e42e06e17514dc48dd321ca370a5472624b2198888602292c851c98a22aa06620275907492e723923849d4c7099512ae62a0ce954c980a267534bc88e049a841a85cd47924e9791c45490ce39030de47238e181ac8862545d440cea261c469902711a5c72a1c721c72242751a4971ca844c40618e44c42c80ea62925cc094d27590e714eb214471324b9920c39930993710993240a64c449893175302539a5320620a99d2e089302620b982a93ac8838c35915c72144307221862e1839105d44194e2604a2350e232a64288ca971c98729e413261b984c99d45389324952a3952f214e391ca1195271c98a31110a115502311caaee333b9541d2772aa66641081c2772aa6432223232322024640029dc665599088c881084408c80775114250072a8ce4ee08c9445664053b8cc4aa100cd540553b998155dc31c0c22e6a066228a38b8a188e30cf218b9892aa77199542a844440e550a44653203355033107790154ee66055770c70618b9a8a38a1170c54c8718e3910ce38e45108b98a3553b8ce44aa1d2554a6520c25548521105033195101dc66aa0154672779060aae1451c7170ee1dc5544ee660a1430a379310a38a393155770e0c317310511c71cf2238e791c45c4186390c31c8622218e30ce39c8a30dc38d2a71ce44519c1a54e39c8e38e4445cd40ee218628e4718a71cb89884ac82ac80d52e6093062ae2c9ac882ac80d52e6053255cd2b228b22229c48e9531de43828af26b22b80a8ae4c9920c409a86571e4d453a5e4438a7591dc0d4573481054c57265457914e254f222e0c0a298cba8a72180a881530e5c0a2e2017715030d45cc51ca861a9c830a3750ce41d4534b81055c530e5453914628e444061bc885188237590a3930a791b80a885170a2730ce99031054428b825398674ca8653a5c728d27390671467590cc71b8a71cc9914e39a545714e7229c629c7222e621418721872e26228a590a5902886ae692c88a714a790e5929c129d253c8b832964604461a8b251c8519e4a338a71a4a33cb98a504a92c8a538e5494f2e2946195251c8a3386929c72e629c6222aa7719c8a55503baa80aa3377032a8cc28cdcee3c95529903bcc80671cdcd5405513b802ac8bab80139bca88a0ef204ee092064544a81914992454451422ee7228a484c89dc514eea72121142a7238516451142a6395e5c54541544eee660559012373159140cc448cc90448ca81512228220cac8a2a64cdc451410119198a28cd5c40522a55c4145116454ab86531395957701dd640925c5d40ceea726203350082726a0e3357790277246122a0b927373122129390217014922e722a3811e4c4900dd64425424d5c5326082990159009acb83ac88484d4510105cd42e38664c5449226385139293c980c99c949e43a42622aee1890c5e4101cd46405405d4e41c88b924844254412ea269014ba8b21249baa4c3488bca861a64708e34923221c1a848abc88032a32018ac8b980d22a122ae29018a5441c7351749c860470ca80ca9c81e49159030dd64dc10c790d22a08e92455c90c20ca871ab98e30de6409e4730ce91ce445470e40eb220759130dc1d4429c4d21bca81d6429e4d4370639aa4f219c79088bb81065c30b230423170917182118814bcca863880d46406a32e3981ac851cb84731501a88518ba8e61c37508c418a664338c919e4718721177335910c12a2495315dc641c6f22434a869122950c3a455dc4186950d21a5432bb89c988e1815020455c53390a330e238e1151c0b880dc6450c2e2a3830c654ce4198e38e2a38e238e2a394ce5de42402e60890539173591731221412e2624490a254d22e6ae293903208a013970320817140ab81ab8c9ba9c83840f261759317015712a0922a491731d248820c8731c0b9a861cd64706ea0d645cd5cc052026e9573909082a5cc2a6e2c8c880ab2e20551909126a32040c5d640b22e0a320753903571c0b9817249245cd645cc15cc5141cc49a8b9c8a28e506e05d64dc3857570c29a848b81912e187391730e638e72186e1dc3122e722ae722b22e6048ab889048b9a820ea91703549208137312e14418a5cd52e26017097357126089335241d45c912a60a691731221522e15228a6971357348ab89a6401953901865c0a139753040326ea4820d4519304102ea38375130ea1d441244b9b8130b21e44b89ba8624dc4992484dd44e5c28a261d471d41cdc30c2eb262849b80bca98b849809ba9817240bba82083593040ab8150ae15c64dc0c8a28a32624c4988a388a2b92272ea6e0c29a98970aea4859312e28e193706e18e3791c791537195397121705498a2ea0a4285c595242381750eb21d459170c49a835106a28c81724902e6e60848ab80ca92124485cd5cd4702e605c9073573590c49b893040dd4dd4398e15cd645cc5091724055dd5c064c109533524910492455c904195249126ea0d459173075706a286ae615c524ae7214c504a6e15c505ce455cc08575712614d4102ae0d410552e61c7314ab9c890a6a605c2ba92254c3a924a8a26e18a370c3790ce91537075706a381730d2157391573145026085137037154b9cc8a142605490a61c70a9cb83710909b8a283725426f248a9cb8a2897243026a2cb98a286509b873950ca2e62a433222a12e20375906a079130e20af215c70e604dd644d643a860f2620f2248218a32248614e45cd65c4c1d522040dd2261d220c49a8638e6ae91350749880a626912414d226eae29390320eb2e032a0821d471930579141ab860837350472417357930f215c306ea18735793159039ca8e38a793079310262861a8951390c284e449141ac982c98bacb981524228ee15e42b8f22615c791d2214c102e6a1cc704173570c39a861cd5e430e6a18735706a2bc89a98750a730e721cd222873242a60527214269103530c430cba9b87026a9307534bcc8512132471c32618ac984864492e195370e124538f2615307509b8a799112523810a2a608915792415226a4891574c88398489ac8a1cc1d226b2e05139015c64d491c515e443a8e0c371591c09831751c4898624c5c488570c1bc898e498e064c5d644c2c8a2b823b87105d64450a6e0c4244d4244c24c55e41880c9a8489820f226ae38793066389139101911453c8a298791c7919135122264124338c89923832238a79141714579135791359038c9821c515c64d491c3ac88a02a722853970c09a848982485913590c09a81304389acb8987906a24c14c56451c35973140ac924ab82244c12451351221e430cf2260f22254924ea26b21cc11cd41881370a209cd65cc565c40aa1d5c90731304489b87112492e6261c1498ba9a441d477051305d522124a8a29a4c40a441d4729a44d44882986e913029105305d226ae91350353a441226089135488098489aa45cc05522a5c42441a44c48891d2a26a904370621baa5c4d5c532628298a320822845145ce54c4922615c305c384c3245d4c0a8e0ab857240cb98e498e498b9248924883514519730ae3927931c7064c5d4e470ce04c17531c702e6485cc51dc0b8971c4c724c3173591303ac85913145702e492175120b992157914570ae3b8173ac8861882064d41032608790b226ae28a628a6215c915cc703263228f2264471d47288350cae08a791935249114e29c41a8ae29c64c714f23832228ae0d457914e38eb226af21893512604d5c31c739072248452649135243c84c908e3c84d5e44cd6450e38983c9226b214320272e287590409a82492264844c879135930353140989353910b2488624d4098239cd641a861ac89bc811451390509cb8a082b228b2208193041242a6a492229c53c8e3c89924892488792454d640985350490982054d644c9032a086e086ea18429b8610dd64c514238eb262f2a6e1c913075302a4849245cc30e4348b98150aee081572424d5c912ae2615c138f2638e61c8b9a8e38e93052e61d42b8574982973591c71c26485cc51dc2b8571c4c3485cd419d26389339ac8983a8b22a44c0a8238554082e64855c51dc53ac8a3b8a751cb22489750ce3a9279324750475064c451645488370c3751c7591c750644d47492228ae29e4538f2263a474883515c53a64728b226ae28a61c9224845484d411d21304909ab88314820a4d49052604d2ae486a2b8c99a8105cc348543a82484c124913530660266a22861a98a3228409813514450c9b820a8b22892488a749226492248490a9a8130d444986a28c98a1043704375144c29865d4dc144c08266a90271d4d2f32081d4c4983384d6491391c90e19145706a2bc986272a28e18b22bc922382c84c9790a9b80983351642624515c23c9985429c219c2a6e29e64454392791243a81398e07223b9ac8829e45c04e606913126ea29152f2628750273042c92261cdd64c164dc505214293512ae6925e414f26714f22203a9c989504e1441c8a18eb2261226f204ce244516471e430e544c30a62f2a62013c81953170a083aa44c18a5c10a713482ea6290a297904138a11c31d643c898930bc98790c271471e471e54c4988a179351cae0e130e43730530a4cea93c8a509c93c88abb809c81cd443a80c65c1c82988530c1b897351975106a3818bc818c8248e2c8c8238571937513970350c640a83532410e618cb82186320dc3988e05d470c37531c3ba8e0dd4c65d410618bc8170e15e5c3b8c8208571c65cd4e451860a39751441a84e45c44881a898903548b8298872439ba9218249ba98ba54418518ba428e3aa5c52083a8ba4d44dc4a82914330a6214c31970a61886190ae48937506e19249ba98e0dd4706ea62383751c1ba987514c65d5c1a851b837106e19141b82957121710a970c83ab8f23a44d5cc1834ba8a2e06ae1311034820c5d2ae06a973146233208621890b2ae4819531041432ea08195314623206e01b8cba88a0dc0c519751309710917504314531906a18638e72a2189724d43032e38179303214c70e632e182e189179351970a228a648660e493519142b9879019750197038bca9892122ea25c925d4c3062e1dc3032e32123228a3114570621863232ea064089208e39197043246431462292628a632ea632ea2122e48348ba8218351914255c450ae263897501972410a32ea23897512e48397513970621d40b82bca88a18ea26e289510415324972414ba81906238e3197031902a08235975106e486ea1e44b9859246ea26f2a2720a19701b8632ea061970518632ea61841c861dc73951c61c72a2e1541a982183797240cb9821c81304104de5c305c32491793570c352490b92130431c32e1e491357190ca288350cc165c93514608d46405e4065d4065c9032ea6389751c4ba9882285c1054515c11790490c8590b220d432b820c8cba8190c215c7307232e092191460885724c718cba98e25e471244c922ea48197240cba98cba821d4628c84ab8a2032e4820cba8e25d4642b8e225c065d43a8c9b8209895144509c817059751c7530b22988190470c65c0c8a10430acba89712ea248e61e47350ca272ea720542b860d42f2124518a29cb85645123712e359244c45c052e12a192a614c11226e182e930520a42a44dc298118ba4d5c52e03514b849820a4d40926e0a54c520530453748831483a8e5348ba82907514d22e1462907514c52ea6297751034b818a5d4406a22414b829022975174851484b9218dd452e62124a8a40a428c52e0a4148314aba8a5c1122a1d215cc748e6a2e931573060cb81ab89505208326e38e23864dc4a8533244a98202ea608153970a648c3170c371c64dd430c34b8293714330a614d2e0a4dd6430c30b9213706a14c29862e3a426ea1c6170c0b8dd645c0d4511432e25490d2aa24937052a6286628d4450cc51a865190409a8e30d4118b821a921a922f228a22864398e39a861a8861a9232ea184191453146228c31970c218643a8a628c221945197530e290520a5d49052e482975390ae3c92248a90ba82485c4b854c11d453917751249b8e14a8352414b920832eae1dc25dd6451c75716445489712ea2c8a917324951445904191461065c10641482957512e3ac8171d4591715248e648e6a2cb857489ab98706ea2cb89146977514448c357098881452e0418bba5428d238d2ae628c46654706a1d5e470918a838d45e4c3a8353013ca819d64dc31c71ce44398e15ce430a6e122a082ae492a122ae722a48391241c8b8614e491cdc514c24541122a720d40a8753971570438c821c64c70ae2086e628ae032a48195710ea2541ab89ca891122e0641731c53c87931461b821cd43ab83539c8ab9c881d4539a4418209a8e2455c3052a089157314a83488314b824541122a6290150ae6297571071487149824549052ae2909506ae29351029052e0a4973121a887170620b9a545cd32017950618564c71c41a8a370c371914628a6e3924ba860654c7242a481953790c370ea054c0a895379150471c643c922628ae032a48195791c515e442b8950a6f238f226a723871c6541c8620e4317144a980ca824922a72164502b26228a60543a9c8591cc5d6438e159242484c90826e2823ac83930f249b85925c9315937145714e638e72186e2c8873040b9a8e4855c3052a08692455cc1a8a628a6f20d4571457314e39c8a861c86218419712152490a98a2988a298632054730c430cbab8e388f23a491302950414ab8a2bc8a2b8f22254371e47489a92125c1398351dc530cf238d22ae6082a906a930ea34bcc8a4843c8e61591470c3759245c1923590b2e389921a5421d42e0d4e131c7322228348839a45645121b88348acb870c57190370c30d5c6542b8a2b98950915704952448ab9c815019532428a820e32a6e2443c86492322a481911321c430ceb22ae0891902248e38d46541c8e1c88638e4338e39c8ab9c88a155c2a861ab992245c48822455d414922455410ae62447357390a20632606324819535243c8820e32aa485370321ba9b8a4c8910c71c8671c72322186a29d3228c514c42b8a2b9c8a8a70c9790c170a614de44938e0c88e19e433861bc8aab8a31c1311c930ae15cc64118648c8638c4718e398caa92383220640ab98e3c8e29e4410641055cd5ce45640c418bc8e18a298851795145304951475390b228759370448a821d54c90f220643386791504924541064114dd4e411d43a985104e6086e09cd65c450ae09d640a827122b26186a38c71acb921b81905d410dc324e2a64922081537241c88a18ba820c8209b820c64104dd4e4939261c49351220b8262441704d65c565c450711ce438e398ca88924c43a49315145724151435710a228351732495241aab820c64488e31c632a4820ca9248922b9ab8921a83570b248dc91cc91ba89c8a14c91a889524606545c71d433867513047312249a92398e9570419244ab9821c6451e4d49244925cc90f22492e6ae208c17241750324992e0649325d44e54642473190310de4538e1a8af218ea08e624473591472565c4288a182a324859173910938a6320462bc8a092b2482a19224922b2228b22925917145114128c9248b9c8ab980d22247348a83488194522ae1462903288a5419d220c3714ab98a40ea38ea691023a87289a4540d451ba441a4419d22aae0ea394c5224521c629550e91044ab98148822b9ab98a5440e9106748a922454148537530a21cd471d4dc5212214dc48829750521b8290dd4c1392609c6ae29517018a438c52a4829505215cd5d2212a48e6a192357149814920a985148a93512209cc148e6ae20464b88919c54d2a212398239a82e29022905cc40524a8a428a5c105522b98ab9a64186e0dc64706a186ae18ae32a0549054c1032a0870ca9b82386430c410dc0c8ca8611c9191c6088e3964718ca98e29e43c88670ce3966410cf22a384718e3219c71ce470cf22a6f22895312a054dc90f2152421642a64842c85490921537910a19045146541863208195530451c6410e1955243704375371c7514220d430d5c708a791906e19d4328a22486a19432cb8e19d4654714c51887514e638e63218470c92488e30c6554c315c1a8657914e28af2238323a443386791c791551c79244902ae638a79244915cd4de490541054c908aa382a6e28453864514f248a8e3c9224921557072488590a8610d5ce45643841390e30c654905450d5c515cc10c3208e30c65410419524215cd5c2c83750c3573914570490a821abc8e18af262186a48c91ab8e3a9820c857304192426a4847324239ab92305c919d4e4515c30d432bc8a2c98ac9830c641865c70c350c450bca8206544a9275302a2988790f2219c33c8e3c8a824922a48429ba982485451d4c6491d471d4c0a821ba8e09d4e4514c714e45c915c90dcc105c90dcd492441255c5164911451750419246e484375391c649c1391c609c72ae284531c751ca72492ae2b2043791c751821b921ba927228b23114990926f214379149082b2488a2c84c9254229bca9b861c8e910435047248c19151c791d2219c33c8671e455c30c430c8e31c6238c31951c6924471cc71c8670e455cc1052a0829530414a920a54de490d2152490ab9248541242ae628ae29ce44398e39a8638d6431c6a4864471cc71a8e54c8650ca21964541a865714f229c7911d2488671e4748aab8751ca628c4518632184191c6188619551d21245731d211c26ae60a414a829154c148aa19526f22a422a42a4845572422a8650b98a2b8a7391524910ce3c8e9150490a821ba981514c44a8a618c86515c5398e311c61972420d5c1486e64845724e6a38c71ab8e514ce238c3538e32ae083238c310c32a0921504735712a2bc81515c7911ca298a370cf219d2260a43a99211cdc148a608dd433867530ca2b8e4338ea30e45430d4e3c8e9124273152138e6ae61c4150465348e51a5e6451c70c8e3c98e308a71ce5640e43791279570e3256492b98e3984391c69524e570ca7324732164e398a34c888a8a1d44882e18638e722245d6442c87504671220986eb22606a2144dc0a4970e31492ea2152298ae26914697902a484170c71c8624bac8119e470467953146e18614a8ae29cd21bc8a3386791c4441c351904e187228c3a8a72219231790ce48a6492a492a621922f2a214f2392488260bc8e49220986f2a260320a88a6e0a31482e1462925d4408ce20ce2a6914697904e28c51c9222bc82724a298621bca8519e419e54c51b8e30a4e19d4539a4f228ce9088abb8304632083512370c1c643375190518c98e246e0470cb8173590c45098b8a12372428a5c1b9a8b828b98a4842a42ea054dc20988518cc806ae2e054918590e228e1a8cb80cb98897181914510c311c715971c2bc98abc824622455e4c0af2e29208350cb879099228a39712e249abc8a21642624854870d452e05d262e0c42831062ae915262ea194c0d2e388e6e0ae90b8d42310231995141a81924c71c30dc640c9a8c85106a49c6064971cd465c1d642cb98a484130679244135914508ae29cb8e229c262052498338a41351127188938c55c5398e3a42a298a3708e621c621ccc818eb2248c71c45383515c64704f26238c115c10541055e47064c56428c43041925c9310c1064971cc565c24495915cc14e2914c40945748e62a14e310e315748a749c8a31c53c922498e29e4209ac8938e438e55c539867484638d451ba47238d211150538e44e315233c8a71872110221a9c60a64948455dcce44114724499dc249731591241c6f21a428a6290ddc1a44349dd41a44349dca72262033066b228e14579198e38cd640ccf2577900a260793159710165c062f2a322825c4c12e26b20289cb80a272ea0b2e0c39ab835069124245cd5e4c298751c706e32080c9ba9b8a25c5032eae04c51226a38e615c515ce4298a29b857149245ce443c8e3c8820c8990490b2322e6ae7220b2e15c50320655e44288a24448a8c8730e6a384b898e12e26b21809cb860272ea0920645c1123226410a722e6089170324859173591735917300ae26e0428a4dc28a12a6e48549bab82126e6075706a244357348b8150a26145748851483986a917375348b9880e9317041452e60297029754881889150448b8514832a45cc25c4488548b9ab8a4dcc553203a4c64091319730164c641c65c11c28ae6323871d4e4515c39226245c4889175910c3502604d5c1122608913724489820e626eb20851304289a891243c898248ae6ae4848c88a4c8a1944724715913241164411232282e0d4579137242464411cb2486511429bc899238f22481910418ab9bac89c821cc298ae3228ae186a087130731591419465cc5041590471c4c704e6a48a71249114517304171220b9ac98a1cc153140986e0c54e5c65cc405498c824e632e60a3208e28e3a98c8a38eb219430d5c90951304189b8229813759314571260c5c905d6410a2608a289b82098209ba921644924490f22a6289512475247513724911221cd4c1054524a26eb263260e320a32165c90ca04c159314104c153143889105ccc0c4d644494c904193126a2f26e2a054988717028982e2441754880a440ca2913029103505d226e1ca910328a44c3a4448820ab9ba8a4c082a0d220851371c105cd4c50ce0a9b8a5cc41444041704ea05220a448a9851047537122082a62826ea62913020e39986a290620aa5cc5d53214a608271253249254c4144de4c38614c4f26a21c4ae0289a4e6204552797700c30d45e44018cbc89b80a2f22072260d221830d5c4514c1832e064c0c81935191c7512e25d4c905197241c65cc107197240de5cd44925c925d49052e48229ba98203232285111521821ca8cb8248a324819114930ea298cb9820323248651052285731970430c64112324879537351971037488a298e3a920e5c0de54450e59137149254490d2e1923750451c820c8a2c9b924981924dd45c506e4ab8a25c730f2ae27226f202832c8bc88046f226e0b220d222861a88e51c753040565c90f2e648ae25cd45c514c0b879304935124972454b9924b924b9a821464106410632ae281590435043597304190320dd5c9254504b2e6a2f22e0722244289823944b92a2e2924b92ae283903249bb83cba8c812b824922e05d64c5ce54061a8ba44922a4dc14982909173510118a40c35148b811483a82629730a348851ca69170a74882924157335174b881492624950e29244ab9920b8a4b9ab88912e39b8775134b898082ae9014b82930e911220d22ea492a0a491ab9b82498714920ba8971d4dd452e21428971cdc4ba8a5c1c52e0a989aa64073148c8206f2186a195c64138a0ba89504ae62a4925dc906ae48aeea1a448927370d24ba9c8a0e44104cc10ea608a66a3921b8819046e6392711226ae19429d2320c4518a31914571457391143114518c9248822454ddc51e4514f220832481957324706440c820ab9b98a288e08c9248822455cc906ae26490d5c5c10ea604411d4e430e470645cd64644245498c821445145e471cc5489171524b9c8a288193145104dc50af214c30d64491d491d45c10d410d649245ce4471cc939273904608dc92447245412b92505ce45645424930dc641865190519704a09c1591490564c0c82e244c48826a48391143172463a44c9244339ac8924a8a2c9820c920c9920c926a2f220671905105e432861ac82304e09c8608e544324622455e455c04171ce443a444899252464a88a092a2e2449325c925d410e3228f2609c30cb820c8e37519041514517249104917049105d64c6424e398c81186f20649064490722a494928b82504b20b9c8b838e444926239471d449392325c4724e2b238279032a632264124910545704e45d4c023a87289a440a44104153770291052492ea6052248ae6e614520a4105d4c1a4410d5dc2a441254c14b9a8a440691249351223ab8290d49731020a92608dc5522a0910dc1498249a8a4186a297103105520b8ab82449298297102925c5522441704ea931020aa45714e62e1220b82a91ca93102297534c8609c329230d441791013c8a808cf225315c09c4653a65dc295c924604ae0820abc82cb98b831c2bc8c5d647246394138eb2498c848c65424e3192b9dc1c8ee53010552e4988518a8728c5271d4ee924e4cc09179100c8c8244e40a32e06573145040b986ae7228a489371d4dc38eae186a08917032082ae638573573919173024a63260289c98510e60671391c305cc938a28a260c5ce440e4c398e14ce722a7220b260827244988915026579317122777004af22e097170b20dc1c72e218e49b823145165c3c9b8c838b8370c2b8dc655c64145c924608179032a25ca62f261251902590c71ce430dc138e722187238e39159124724910545791704304192545319062e677032719984c98209214c399641b940dcc359173911450931c791026a7220193173b8a280b8618c89757190119644e77048bc82e6335048b8818a41cae18710475370c514dd4d22e26043869398a41cc52a62025398b9dc4811c75712e629702b8c52ea204a313033882a910e2e0c52733b8cc039882ae931012989cee04a239dc7319aa65640661ac8a39271986b20cf25779010531465cdc0539731216451730353144712ea05c098618bc820272ea638e3864c7039735171450157304285cd4c901737041a98a298a298b81a98750323a9b853140c9b8c9895145970c228a618c859244508371d40c8c9b9ab8a18409a98a2b861b853146f238f22625c20e424819373571937900e53145e4dc0617932416491370ca2889244c484d430d46492541013970c04e5d4c11e4106549041930b2488a11ca28c9b8604e40c822864dd4e4524b20dc31261790c30de54c5cde540430d45179050bc9b8285e41c9830d5c510a2cb9260649350461a8c92247197244865cc112197041cb9a8a1249190ca088651cb2392a32e09228c851c9221d49314632e6086524643282219472c8e51970430c820c924a9b9ac89712e625c735242c85c9032e64819712e135917141b89751ca6e492a38e19242cb9864926eae28e3255ce42b8c50c1571ce44de416640ca28bc861a92165c915cc4b8e6ae492648d41243248410655c2c921ab98192495714973579147186ae18571cdc38dd6465c06f2e4872b830ddc7590b221e49509bc9a80b2e11bc8995199811c515cc394c64c38e3ac982c9882509537041149173249172491020c9bac820a3260859144d448853c8791303208a6eae29279141911c75242229c71d64725464c7264116445383525e4538a2bc89b8a114e08c8e3a8e511432b8a2b8c986188a30c6492441254ddd64c515c7082e09d640981350c215d5c908a1143264843c84dc0c87909922bbac989c870a62b8a71932420b85304905cc4986ea6082a18720e44102a6e09262826ea720e6604d410261b98335970e61cd451c23a9c8650cb2e272e1c50cae38c989254c51149081350453530451426604533571213242e18621863206411c326a082a48413a9b9920b861c9220926a04c3573590a604dc7243515ce4398e29ce544e40c20bc98a1c7330d450261b981359126513061c84c9579750432865714e3208e51464104cc10e6a184d40c8a17043730322b826ae39472c82194322486a28432cb8a195c64509219249255ccc5092192420826ae492248ae66e28b2489212493570470c923a998228649055c7484dd64118a350461ab923c922385c1b86e615c770ce6b23214571c64508a60946e18470c820ba8190d4c908ea09bc8a30dc92541724e72a19c138e491a8ca8718643282570323992172417590f24a88a71c759144e471c792545124e54c28642cb820b8260832095c909c82324209ca879186a206493246a48bc867249508a628de4c1381924c951443285e44c84d5c48e4e5199827124a8a260bc853ca8329e4230d4667770208a9145cdc924508b26e12a081757702a489353143ab8352421ab98a2b83524ae7228a61d4129b8a2b8a0b9c8b98225411c2aee05490d2a628ae29e4538f22284190c351cb219522e6e6a0573714530e398a5cc15dc34829026977359029b98a2b853146e186f23a44dc14cc708e90897099ba8a0d2e131c1b9ac8b9810a97144dc90a13165c51d248b8f218419492115248b8a106432a491730c379731217052082e492173730773950c38e66e066ea1cc35917350e3a8b261526208e15242e484484dd451645488370cea3964728322629d24883515c53c8a7489b8e548a9106e3a8e591ca9130d2188229bba98a71d4908a9098930b89308eea6229c750413026970d23ba98a38ea632609c10543492214dc30dd4c3995c394ce21ca670c9b8a10c20b86924412426a04c1bab98272421a8657351c539867510a730cea28c98399426915dd45394eee0c35145c285e490d2a0a4c14814b9a8a288a190e638d43288652465c5184190ea298a3114619730ca114321cc350ca219432e38479245733571461a829052e05d2605d219abc8a30d49052e25c2638433571430d5e45c91924a8e10642b98e39ab83729832b8e4195c691731523a4931c20c920a5d44b8735372460a4751ca6ea18a371c6b2146e38d459170372a5c2299a8731c6a392b2182a2c88a14921abb8a90823a99211cdcc348411cd4148aee4845305cd41486638dc519d64908ee19cc538d432c89210d45714e629c6a396432a454938c35144191429714eae08ce3a8b2488a9098a351c657314eee28c7728ccc0a26e901374a81748c51a8cc0994e194e3349de6403272012bc98790825122b987350ca2e0ca638392435731c515cd5c1cdc751939702bcb921c6e18e11bc922383790abc84946f2633012c9820cc372430d4c09bc8393898338533c9226b239253cb8a38e3925451907261e4237199dc70706f24a9922f21257918cc496431986e77512170521dc30c21ab9873906e911c2b9a49157305339942939dc15c6e54846284e33b8cc19a423b8e3350ce92ccac891c7065709370eeb2489cb8244986ae6197501b8375165cc20654b9854599090cb9459590a791c30b238f210f2a6618c849ce42e039254c324ba8394d26138a754c8e548545495e5c14ee39090c51cbbc8993092cb8d438d2e51a6416461925492b8e531ca34c9dc51a451a4ee219ca90a8e539311155039e54406791c544c30e53c8728cf2638c222553bb80ab2ee0318ac81c621cacb8e0ca3106538c5c33a664aa771998039964ee26600dca32ee0025739128292c964244e549cb2e24a92c8ae11100c8ca1194454cc8196422e6771994aaa03b8cd54051552a337702a99804626a0414a881482950cc4c2944294626aa9198154cc71c48ce26a04751ca3349c475548cdcee54aa6664066aa2814ee660e5509dc29dcc67250a8294c840199dd54051542a773302abb824f2ea2434856470d211d2151de5c2964294f2eaa1544ee055770c30271cba81bc921a8653b8e2390d542773199451502a1853b8cca90aa6643222323232200e0117901de640ee1114a65c074cc8444e0ee294921100332acbb8790335030d44665591dcee4a532073bcc8066a00cb22ae332abb80d466a0a6600acb886047218618e4430c72117130a28a29645c51452cb8a2220c45146590ca18cb21c7250ca919645c50cb219451965c311135199540cd40cc28a131519954ee77129724e749dd3332484042e02332a9c2774c864445e45e45e44048c8080a1466553bcc844644132222642110232480aae2072a8c84e1c0cd40440caa27719956411388bcc828519954ee21014aaee0e335147067730a29dc430a28b865164ee26a332a9dc09dc222200b8b880a52271794c81c6e62052abb807719956641c66a38e0cee628a770a2865908b832865910ca196451644227735199564ee224e93ba532903309dd21484448198c8806655770199540cd405515c5c6655990066ea33500aea2660e388eee20618622e218638e470cc3a5433911c649c3390c39111061c8622ee628a28a2c8a22e28e50e62ac88e524e5914591114517710618628e437711145144430d430d647186a286628d6445186a28c3590ca196445c70cc350ce1986b228ae19cc51a861a86e3c8e3498a91ac88a2b8661a86515d2198a3591ca31ca39111c650cb21945908bb89a8ccab23bb814aaee3814d4665512553ba4ee94c80199564f2f2005597198a5557700cc70a1c3359106188b9ba835199a80ee28a0cb2218a2eea2660ee2049211357902b8c820831e440a8e99152226a12262440ea623a647020b9a8e991d2226af238e1274a99e44704a9d26a790e79117710c301bcc89106e0269790720cc19a6430e45c540c5c32443247228c91c8622ea72e20e19c8920441830c8ab818a81823159739243088601795010dd64c412ea20975134c818617951c70c30c5e54c0dd43a54c3990ea39869911506910d218887072265d447018ca920472ae2624e20ce26991c18632086197524114209ca86182395730ce19cd32384730e4455c30c2201bca881a8981a8a43390c3072ea398e348e4348445430c43039503957106713061506ae10cc540c5463846299739103110670ce72181a92e2381ca92e26a1a641aa5c0c4ea349ce419c33900ca8aea06a2ba98721b8351a4e7238c349c72222ee61428ae2e204559022ac8510ae0a971914590c550aa991459171302524b2628a29492cb982b988acb815cc72ac8915c454805e4c0e326a1cc39aa644548e1642cb981464c144dd43986754c8b98515c45482b98aa2a4b222a428ae6514b22e6b205731cab22850159731471412bc9a82b98749a8b3262a470a28c8a2865cc50b22898a28a26ea29c93aa64dc50a2b98aa3964c14c57329259759057156450e63a8a99314338ea2c9b85164c54bac888a15267156429c7591449cc299d459315c52a4eb2214e3ac84986e60a6735164571527591ca2a4e5911771043243770c72865390a29c861b8515c5430dc35390a390ca29cbb888a24917061cb985145c5359051018bc9828c8a6b228548c81988a05791350e198a45482b8a4d65c1a8a99032032e60b2e061abc9a85712e61c857486549acb8a2c8430d430d532e2218a390620b22a094c3062a914e5c514720e428e54530c3549272e18a30e5c2226286590a164c4350a298a435970597032cb986a145374964328b228888a329232c8e328659089acb8a03519013026b2e145791ccc06e323a8e53590e28517912414e4302a054e5c4c02b22831062b2e238a2b860826e1823759135120a5c418697130a495c4186e38d44d5323821864a8c8a1861a8cb89270c28851390c0a815397131c50620c56450620acb88670ca082608d64328230d65c4d409d222461b8985388329c4d532e383714570ae7223851c8628e5c540dc438a9871cc428c5521952721860545390c51cb88618a39072e2a0ce21a983388ea34cb98502e3ac8819641965c4c28a62a1ca21c4d21ac850b22145c451432c8ae2608d451a4b2e1457119491964288ca9735914186b21c731c735970a2bc8e660c3791d4735902e28a2186a1945e43045390c1054509cb98a086b22861ac859171430d64328209823597350520a5c3246e625c751d23a9a861aa66450861a861a8c8a186b21645c3145390c51c882314539731430d645164412861acb8a186b2164450cb228b9a8293867314e49cd459970a390c51cb851c851c85d47298e31d4534c8628e4310c2e184ea298a34cb9832c859145c4c8590b986a3945349642c845714e650cb2e28ca2c8ae6b2141965c731c6b238450a8e1154c514d3249c238547298a34cb865164510ca9751461c86970c4a722228671cc35914729a4371469398671ac8186b22b867390a71ca821464970c51c86e628b22b8a2c9cd4329d321952e19ca349cc7195271ac88186b270ce7238d451645115c1c84e6284e29cd432a64571ca349cc32a4e3590a7919451a4e32c88bb89a8037518cb861830b9462146299950c30ce390639088863869394721153b8ccc505311428cb261441964cee186e1111995540cd41cc39a8ccaa73bb8066557703350331428c3513548ccaa066a06606651548ccaa7749dd33320557703956640cd41545308ccab213b8774a642093cbc8066557700dd466a0553306771451cb27750c31c72770c31472e147219c251c9dd4c5188ccaa11ddc0aaee06332a9c293ba66432223232322025232004ab32108c81255088a642529910198819a8285593b8ccaa3320c321100cd41466772ac819a829dc665505570332a9de479901c6e6a0ee60c156414d64156414d6444ee332acc821019a83b8ccaa190c888c88200aa3319901dcaa3314c888052a9de6640cd40aa7719954794c821a429910881191c2902ab872a9dc11488a41dc155c075119954ef2072a9de42110220aa770aa280aea2332a852a9ddc155c0ccaa770846446640aa331038dcd41dcc18e14597353b8ccaa20aa606772a8cc210880cc440e19b9a83b981982b88a2861a86590c350c75910c351c7590ca2c888b9a8553bb82a9dc6660533b8ccaaa066a280cd4ee332a8422220aae066553b8e791c22900ccaae05719954ee0aae154ef21dc13ba42111cf22329901dcaa19988066551dde40e19b9a83b980dcc2b8a2830d6430d64471d471cc71ac8650c35914445cd42a9ddc154ee3330299dc665559100ccaae383b8ccaa7714a532902a9de40ee5530c0ccee5519c82a986620aa60ee5519a4294c85211019880339531910550332a872a9dde40e39b9a814e6e615c7030e723839ac86222e61450eb228e3ac8a2c88b88a2861ac8a186b228b22220c514539110c351c731c7359061bc830de5471cc538a73591061bc861ba8770ce629c73591c638d471cc71ac888b9a8731471453c8a714f2229c53c8e2226a7770371431463947228c51c8445d4ee3330773028a2e2145111450cb239432c88e50cb2111733b8ccaab20332ab819a82a8614571571ccc5553b83955c1c66553bc8e74ca640ef32018eea38cdcd402a898a777301565dc1dc430c7021c5d40e541862ae722e6282ac8a12262471370a28b22628a28b226eb2e228a032e0439730a28a32e28a28a32e6a320731c735910370c375903590ea18735911c3ac8a2b89515e45c306a228a605453191c638e72186e38e721872111731430d6471d43086b2239471d6471d471d64516445c32861a8861a861a8851990ca19647286591445cd645cd470e1c7353c89871c753c8819e440c3599387914222862628a239a9e44d4eee1860c186ea319706186a3190718c838ea2230622a6451e5c516437518cba8653bb8ccc14ee628a14b228a2b965c428a2994640cb221cb228b228b21124517045915ccb22e67714666555018eee6a0ee60737030d44c29c4186a195c4d2ea2a4eee0c3aba4ee3330ae1429ba466772aaa53332072a9de40e373507730731451451cb84d437719825559055304c4155c1c66553b8e790a532103bcc81c33375033701b9838eb2e147228e3a8e539706e26a2846661c1a984667770a6142b984ee332aa81c6e6a0ee60c706e6a7719954794c81954c0cee55198694c8c86444646464400055539539003b80aa26624aa319c9aa9a98004cc9c9c9c8073ba8a0e1118ccee55333009930c067255480e337500553b9844cc0c440559771c13261ca839aa4ef23819c86e3a869992a9dc2228cc66550aa9999393939060a992a8c613238e0e394a9c672ea1dc00779132aa677089a4c265c38838a7597088309372a81e4d4771c3c992a525d5c9124ab9541d26a72493254a757908c8508838ea371c72119199dc3919c828ce554ccc000334ccb9cb9cb9c80004a77513304cbb814aa99089cee1dcc66e6e6e60132618c0c66772641de414528cd5c01dccaa113301954441433baa86061170c08443b98234cb9c832c808b82845c661c96541c3221e40844693c98096440a4b26a772a8441caa11198ccee066774ccc9c9c9c8301caa114c9dc6309142a5ca33597011c1404545774c9954226601d2b2a4870aa145313b98a64aa220550e72abcc804ca9b87069906997350333abbaa89900c22f260441844072a088848a8306f2a113732438440c22e61c9ccb80110a11379370c28442b80c92ae48885088a194220ca11973370c08850882845cc5937990c2923374caa8e187088e061bca844e4c38440e6a248204dc1026f2a4844490e91d262a041350209ab871c54709c92226604438443844c3939902218a3942218e5089c98494c111122506e38e32495450888650c371d4221c1328464cc4844094220446693990a628a334caa84c9874c89911033c8440e6a20c20ba8105d649110e114cc870ce1190ce18437088119c2324cc9984c98604a69924222147284649286925c750883320a119147284408ca64702294c999955c2642226449d32111c14c8ccc084451421119954eee551e643a6422203955e641c28ae312a8882871a9dd5408088111cb9332e282a46ee992a871c871c22a0464134c8a3a53232a8e3a53232b9dc265c339dc7532a84532044cc660ce6ee6660019cc9c980121139393390c07065538cde664032a844cc0883ba871d4ee5508866331e532618d2014ee551107750770a14d2f2a772a844088c664a666460e38a719abc8053b95422660a05533b954441ceea15c198e3867904e184f226e286506972c98a39472c8811c9ca28a693964dd4ee5508806772a8883ba83b8a28b2ea772a84466339015422660aae1caa771a46694c81de6404415441dd4072ac99dcaa0ee550889980eea14907706771d5464cee55110033abca9dd4092acbb82c80440c2326ae18624220c221c9bac9c87904922a620e08a8923857044408cac8e1e40d6414e5c71151c338350e6e388a874acc99870881388e38e138a981388704e2a63cc9bcb851ca395de4020cb98814322e48a0d45110a32f228a2861a8a232e286506e1a8a22e152f3266285153260b26220eb206f206f2a39422206f249d424e438272e14720e5d4728444c38ea2186e29d45088830dc47524131c6e19d450889870885088a6638e664c70e3c984471420b88a724a13898e284e204e2398f26993770a1114094404a326e04a2146e62cc98a0b26111470944514709464c51c2510a2334c98519a5dd654729ddc55507750770e50ca9dcaa11101dd42890ee550aa632772a8880eea77501565dc0184655c0223754c927238e38e384473950e38447354c8e931d2379705145088a72e145088a6e9914c51ac853c8711ca38ea1191c51464c51ca111451914d322a4c748dc519d65d4ee55088154441dd4194ee5508998cc03b95422693004ee551107750550aa7749dcaa110490e772a84466919a6664e4e4e403954ee99300aa113333077905571c1dc425449cc724a2b9ab8464aa77093b8453320ef2015c232553ba640898cc61c0ef260a3bc8e4d5c0441544102a8226095540954eee20772a8453266091ce4aae0c0e175103b8544672a38a10aa0e55971c5c40ee220559055977088513301c98195cc093173054b9aca83998398e1c227261439464d541cc39c98e04438e226044089c98a28e61c64d5643838a998e04e21c409c4e4c11c38c9aa804e2a1ce4c70271027131c73931471a4d565dc912a2a5dc2111032a9249564718e3c8c5550e91a87118f24aac8e31c791954748e919565dc3b8422214915dc530899c85288924ee5094647355012a9c4705591c39954715664e5509c410a72a84e2337704955c90939b920d263bb877554954ee1102ab850aa774a4aa77088cd3208cce4ccc00aab2b20044c14aa7719aaa8005519ca4012a8980e38ccee11550430708a643a472333b86a112954664a666655656409955143b812135029dca69099544c14066221dc31c339b863867379908a9dd2a132e1c41c7597088124c951211387919cc938e63aab924992a3a4e49c663955e4232770e772aa4aa199caaa801332f2f2f200c66a281a64e7719955ddc13206332aa400c22a7719a804c4c0155c232ee0c4480a54c232282052530c89540413864c40e19312a9dc3021148e40a4a392a834c94ee33089dc66550aa999999903b98033110f21877018a9dc33354c8454ee3350002a669913b84c4c00957708ca5e5c0a990c38a6234c988828315e4ef3204a655cc0824824820e470e722ae604d32b2e6025c20cb9ac8885025cc152e6a2e9930a9900e26e0a13759714245c0c8530a7215c3982b22e64832b832bc99248e50cb2e62ae048b982ae99931400c9b92a6e4cc89911101a644c280995d326112aa8024d4d322a64899038e2a72122a0e6a0e6b20c09ba890dd644c09a6654c0c1d2a134ca9922220991c39a5326260810c5714571391474880a98a29b8a28ae72186a186ae14c5791302699930e1cc194c984442451ca99313041ca7228e3c92a69907390e930d532261326111514484c2255500a74c9a8984c838a7193049a86e60d24b988332a61299308880674c989860a7931c29a4e6990539c85499d3226488824c4c0cc31308a955c7019862a61102112954eee00175708cab8204406957101950375037510e25cd408e6a32e25c222ae00552e115706664022183714422f2e4891c534b88a1864255c515cc51453711c751c7530ae298cb897088b824422e999011432845e5c9032b88a18620ab8440c2e3a8465c045d332a2814ba64aaa180e6b220e39aa4532a030dd40c37951950428eea249759060d5d4492eb26041350209ab813a8a7391502a999143a55321112438e721457148515c5269910514e4310a29c8a2f2182a095c928257324a2b92515ce4128a609453714e39c88294cc890a6422248648ca9910a791d249953228e92a64422a551214f20d2a1ba65440618a82f2a386905260d5221a42ea99244419233a64428e4e28d274c8e2a4e9910882a5571c30844a77700a308bacb80881a45c02ea39b870826f2488ab80845d332038c22f2e3828c5c30ae11b844142e308cb8332017970771e5d32a550214621c2a39845640e9524c5431c2485c3a86470a4d4220cc8704e308c85388c53846110a118465324a9540c71a6454712751a649108860894aae7730c0ee3caba6431d29939dc4a64a72a8ccd320889dc3330a3355001c6732abccc80d4d450451c12a8a333b84466551e5320019a8464ee3535071c6737900e773098980a77198880cc5032bc8cc35577008130c89a8e387904e052613c89ab850531914e1ca279730402a628c818a2e930a289a5451930470c871d4119381398275164513c9b8829212c988717550c30c9390619030c5d2a0552618c8a8e3827910ce38d2790e30c9c0a9d23a4c279157010881130a111ac8310a29b851b884450c2508a8608c225302251a66404e11022a044a7270c309c221c22a044a60a64f2e29d54338aa6677088ce4aa066a4849dc2291995529903bcc800771ce4d422771a9a80020ac8a9dcc5131300a6a770155e5c0e63212394c643553b8a0e3190518c954ee6622132065590065cd40c088693975091ab99920a1130a182951444e5c2c8a0c22044089ac85088308982390a11064284526b2e145971998044cae0111c95c660308995c044657198a3995597700138c9abc80898110925326200957301e5cd465cd4548208052ea649205c193517500aa5d64e40055cc32ea03242ae93515232226a0924544c249131249033ca814e62a3cc9883ca897020bc83c99248e38e32a620ea62893a98bca9838a820b8a1d45930753712a48e388f2a6482749b8a98a0620ba8f27323923839a875795307531147240a4d413ba98f23a46444d4044c0881c79531018e32a67013a9a4f2184e49e444d5de405089c808751444e41c232ef20a29dcc44b9226544c89951ddcc0a2425e544de4c9144a8e90971e454dc54c9c9228a4870537913243832bc89abc98a2428298b85791372406e3a8b22e6a60ca939952474c8e2871053c8a98a2475137912a0d220ce3c8a984a9b8674cc98a2921c29c89921c72c89ac86127130e6b2e63920a62c898549a84986a2e6152732a14ce19d3214e9357713122654c51323832a62bb80c2b8c9b850ea2e0547032a0298cb828b8216451c9531795301370c114913750c1059712e26e0c517015714592449ab82282f22e6b22e7212a126a2e2544b8171e54183a98b8a0d44516451c95317505170ae28537159372434a81065c148a255c4b88751c65cc11451712a3924b99208326ae286288a28cb89850b8a18a21cb814b89cab8982147054d2e0261c26a2cb89cc8a289254c1032a2f2029bc81bc82bca8b80c65c50722a380abc870c159704150410e3260c43026f2af260820eb215c5cc2b85710a648e3c99224dd5c1a92064c325d5c4e4490410565c0e322455c10d41b8604de4498e3c8abc985704728a2f2082bc925170ca28860de4706f2a24c9517931579309254dc0a5c0a5d4408175165c2a5c50c3510491d2261c4712e26ae144098135797301055c597052086a24c71d2621893157141886af2e6a15260ae615c44b9208f2e624c712e6ea4820a4dc31d2ea2628e21cc39a857489cb9215c511432e28651c74989357093706ea2e0657145e4d44c10a614d404dc3511432732a14254c64145139706a1d4491c0982f261e450a2e04c244d4098135793503238e214e61cea32638e38c8a1142e189350c49ab864a83571935190a60ea62387950724b8270c1a882f2a60819032e6064971420d451904197351973142a4c428a26e481305c33c98e3c813026a08135706a2bc9a820c8e29cc1388638c98e38832189350a6e186a2b88a71c64d4471d2a1a4970a271e54c90524b992285261a5d45cc106a14c4c1906134bcc8e2495315e404c064d643965c4386b20e61cd6447141790c51026e486a24c49a88531261a8bc98e14642882e1cc751261b867519350417145714e3228a228a2e0e430e5449813570c350c3571931c229c7191c7514e20e4950cae494571935190a61e41386289e4c90b24b9ac8398eb2064170c72c8591242e624c910dd645cc492a6092a2282e3c82244c31262a2861a8b860a82f261c43286515c4c09ca8a71c44989350c3570c3515c4c114e389c8a3886515c538982384e544c524289d2604d4c50a130dc390d2a62e0ca60ca620ba665410539c83054f2260b8228a71349e40cb2607253138a149e55dcc9032a28a2860e1379013700c9b8371957390284de44055c4a8290ee1064c70a1730e721a455cc29c8a148c81d4dc24153714298a24757391c29c88371c395ce41c8ab9c824a617910a170451450b985390e69170e394dd218a98b22a4654c0832614c52411c32648e28af260e454e411439927506a326e0a13915c450e930c429cc390c54c29c26e19d3229d2326041930a60943c8e29e4c1c8921e4c915391450ce1054e5c2864e2287348430a986574864d414c271e4c14abb88c80964044b27791c3b9228905193709375931405913925c33a99dc4c04ee614186320a9b892b923817906570c30c5c0bac9b890f25375303c992ae48170a179121704a0e4a48bc9b809861975319030c64c164704b2660820c8792922663208224c91395041ce41c898615705dcc28187248b992b26093929ccee388887054986a61267299dc4c3b89245c3952e1ca0dca2e0c9850b81b94517302722602660d262a0269306149886150c2573b98198ee53088804ca6110e113b8279990298980c27253088a04e53089dc04a61104ee995955060618622b20138acbbc818544312111211359012e03975379512470c3a5490398b83795375019bac8c824de406640272e28482f2ae0375706a384b88e1d44d5e4c9032648e25c4b8ca8791c24839706e32a6e32ea04909b893034ab88972491262026b2ea06ee1c8531c2b88972454b89b8618e398bca98e9241b89711c719750e1706430644b924b9921b88351c65d4c5d49043a82202ea1d44c09cbacc800bca922870acb9acb81cb886480ba8720c2a2864dd4390d232221861864921c71ce455c9141c62b2e62f2a0104e55c0472a0819301bab81bb864926122a164ddd6405641c81712e25cc90dc655c41c6ae0d43142cb859357903570c31c618abc89abc860c3037590f2135790c44430c51d20e498b8379570e1c6ea06eb2e62a1248a921371248b82930e39b8350ea3924ba88910419737506e18a38829375906170643249712e638e62e1c61795106e28c1052e254dd4712e35906e18e30c5d405d644dd43074a85c909a84441462a183a8a2e09a8441846664d49123a6549111c71c0f2a22470c379513095103c8a9bca88e19c1d2a24830dd43ac8985488538a4dd4419d23323811226a1862f20c298c8e383105d6419e430dc489248982054de54c385470c3724e2b23820ba820b8e724e625c371593191261cc490724ba9270c104e41cba9820649750c185640655cc65d411248a98e18531062ea04eb2086e292228a913040a9ba8e1a4375931c3986e192e2a38638ac8e39c739a8e0dc37511c350ea3262a1862486925d40826a2c8697302750640aa45731570530d22a2c8354bcc86143856470ea1935907092139570ce21d210ea909a834855c791c644544c871d32a48880d64430c3a8e1261b8ac8e38938e62b26b218648393a9273597100ac850c9a8924540654c70c3790c3724912415312a254de547041751c7124930dc338ac88e186ea19c2c92648dd643a8238413591359070c826a082648648272a072ae2835912ae22835925c2c9c4d65c50c50eb248921359123971c44428c431d20621b88338ca8e38d43ac9a853a543a54dc44922a186e48a2082a60a413751c9186eb238e228c370ce2a08e1591524219c11923750eb208e11a8b22a60891a8b22a5c549c54114e14a9b854854670888313850a8ce11023332a624220395138608a299c1a9c654770c27110ce18670c54e114ca81101ac89c142b2064c27150e38c2711e55326ef203088111ac851c75144438443ca9c8718eb2ef20e414dc1a895039cb849b8a1e490f2a6f2a2079170c0dc2b85739179070f262e18a29879079150ae0dc75937195379101ab8a2886189208839144d5e5c04e4098214517395020c5dc0a8a15cc2b92255cc5e4502605c7054e5c298624d4450eb225c925d443c8e25e4471c40b920b8ca9bca86082e387953702a12ae6489510b248795171220832e383791c525e454de4165c30a6e2820ab8a082ae72e2444898912491350448c879140cc8b8e25c4488910c20c8bca82145c4b8a4b8a924883114191724910a61847917593795302614c4b8860e5c1c89b8a124970b2492ae6164506b2e2e0d4310c514e4912ea4879537141ab85314537917390470b2638375170c49a8a2b8e3ac921e5c714979537095706e186f238f238f26ae321451706e18a29bc8e186f22e492a492a615c525e44b82065e542b8a4bc920932ea6e486a28a628a6e38ea38ea72e326a2f201abcb8390c12426e24970b82381790b9c850b8a28e1acb8a320dc524249bc89913579090d42f22220a6248492ae262a4287537053790a624c9122a6e19229bca88e18e25d42b8579371061d4549b8c869144a98e3c8e3ca8e3c8171e54dc298a91459379153712428b2ea183510ea3897531c925d44b923a5d4c5c298a1d4c3a8a93179144a98952454a988e3a875924972454ba88e3c8a2b8a7910e23c8a2c820a932e2a6e152e28a97114511c7489238ab9cab8692448a82249175312e48a9752474b8a91c7975112e48e97106e3c8a3b8a4bc8a9b81502a61d471d45910ea90ea91379709255c59724952451654490d223a4548a98a2b857914590c75265c40b817906a38a2e492f22a183170c17914590475265c430dc1a861710c37249719537144a8820a98e3a4471c5471d471d4410564de5d4c30e41480a832e6a0d451144ab8952434ab989524924d5c5c4a8770cea38eb2e492a082e282f2282e29e55cc90d2a28a2286471e470654dc54912a60d44925c90479752434b820b8a79530c514dc3a8e722e4926254749a862b8a790430b82795145714f20a454ba9b8648d471e471e54748e953715314215c71d4c50dc5c51ca971472a5cc50435165c54314471d43aa4c51a45c3a5c4ba8971d4c5146e3c8a9cb88950a4bb87228e9026ae2ca8e91d2a2e0e0cb8f238b85145371e5c91530c222203a8b8386a2e61c880b8229ab81ba5c18234bba98a242e18540b861537106970c64548446640cf22143a9c871261bc8830dc4284a898a29b8ca830dc425457095115cc640a6214dc4324950a2e483c8a89573195390514c640e4e20724b8a83925c18a29c892ea72e20eb21c50dd64c51c7302e082e6b2214c29b8150b22544c0a824922a6f224c04e54298624d45c0c82092326087190223871193512a492a6492a06471e54c5e544a815312a144dc9244104919524910e238751953122481915041904304654de4524a62542c988a164450b226e2443149719040c881724711950439c8649e5412471903248632a264927524e49d4c70e471e5471e493a98bca98618861712a28b26289537249098357190a6188350c5c9132a48e3ca989524953712a254c514dc64c0d64298861a89517244c98190e19352493240c9ab924a924a98624d5c643246a0d443246a28b820c89932470c8e3c9a92499249a8879032a492a6186a2f26a321d438675931c71d471d4e44188614c6430e32e185311453145398c8229e5d4704c512a228751390c30c65c3145311ca298e3a8e53190c11cba98610a628c821865c2c8a2187350ce320e491750c228a618c823865c518a2494530c6490ba98cb830d6470721bc8e486a1bca8e486f2392795324930f249a8c8672493246a28dc519c65c194327111073114498537142898298ba88338a751904a8ae212a22b9884986e321892544572418a8ae6214e298ca98e90ce950ce90ce95371245115248e951302a0891537042898937924912494899248829041913512a492a6492a48e95317052082a628a93795249124748a923a44114408ca9824922a0a492454dc28a428a4c514de4106413872248f209c19150c3088608c861c8e106454c91d434829510c950c9513704150495312229bca989514593145372454986e2186e49c6491d2a48e95312a29b89514c3710c370c64c905260a4949a89324935714549861ab88a915c338c9291c2950524a9861a8924a9253145c5184579351040a982e18a29882ea49c13ac8a288a28982e28c514c43750c153c98610ce28a861146153041514dc0a8a61bc8b82714ea2c8671d45931469114e90b8e22214530dc471d471d4c31c6a2185c11102708ccc830a2989e44e19c92549254c3790c5092679139213888670d2189c2714cbb80a6e320e61cd5c49879063ab8531c3c9920f226af22281b8e351706e186a1c791097151c38c8e3ca9b8c9b89302c8b8e194724c49ab8c850c95710c30d43c9263926ae326eb2228165c0af2e720ae0b2e7220ae15ce405c0b9c8ab830c5c28a6e145371906a28ae181370c18bacb8624c411226a24411232e389711222823c8bc98170448b982045c488e1c45ce55e430d450c3570417041730413041375972491249131248b820c9a820822e0819102e49222f208248b86288732471179302e08ef225c91c35791043045c30dc115c64d5e4c508a0dc1bac8790f2a2e24c24dd44992a248997241265cc71cc304137950c370c3790f238f26a2f218a215c310c3706ea18ea32e492a494c90d4472470bc8e482f26381791c79351c790f2638e3951793170618b8514dc0826e321941c64150719032a6e08260926a38f238f26385791c3bc989225cc3c8e3c98abc860a80bc87930c3157032099249a8e3c8e08af22492e38f226492638f2498abc98a103790f2a1cb22e186a19441b8e39c8e38e72a38721e545e450379254928b8610d471e43c98e1ca83928bc98bac8186b2e1857149086af215c50caf2616493172450ef2164c918bac8328644440cf221cc35061b88e2892898a29b8c81c839710c92549254c524a6e32648538861b86b2248a2b861b86b226b20c359061c92e20c3925c4c49c4935971060b8a2b9c871c4139c8871ce408e722a186a24c3510a6186a2e1e49524ae08f228f2a492ae606491c35930f249cdc3c823c98e39ba8c87103260826a08260826ae38f20922bc88e3c863c8a861c92a085791c79513249324e4989238826af260c415043572493249310c31704e09cd6412826195c9244171227304130dd64d44986a186ae16432b88190453c98190326a492638e6ae49261872a186ae3248c350cae1945710419032606493524a494dc9186a195c64c315c538924986a195c929c64538e249ca28c9a8c871ce4338820985114513914597145304a09c925731432c92e164e228450c82e63238c50e49724a7391c909c9391570ca38a791c993246248c2b22432571c4441944e0cf24882a138bb8298923a430d448ea21c7910e91537144986af22e283724950e3c8871e455c90371e45c91d2ea62e0c524ae15d262f26064926e38e6a2e0e57190430ee25cc71cd45c0ca2f26a2124ab8b2e24c9152622449244d471e42b8f2205c791432b924bc89924b920a5c40b8f205c7913570629062a1c521c41930520a4d5e5c28a6e3a4548924a44c91d2249226a085170417904350c51724179104128861845c10dc905c64c19441145c71c641b8f215c791357706570469046a38e20c8e1498290526aef26142e48e932493514171e4148614b9920a5c71e4d5c24dc7064749b8291c737517044b8e9306e951d23a8bc850b8a92549298290c29704e3c98e3c8e93572474b89730c71ba8b8a25c7306ea1945e4c40952e08913049351c791c7931c791c793124731c731570c104dc30dd65c495c1482638f238f223a47489b8971cc3246e2ae0c11b82af26142e186a3a47499249ab863a5c1ba8b8328a2f20863926e0dd41b945c3b864c542861abb851b98a3914622a461508883388524a614dc419c64324a494c514dc419c64c19c751644194526a0d2250d25371249515c148aa495cc14861064c90526a494929b88a29cc348ae321a474a869298a71e414982924d443246208d5c51865105e4c925264926a24c3570c3515c4538e320a493246a195c329c453864c430d220b8313a825904e0986a2c986538a710c2608e454104ce3c8a33a4c308d223a461571d23094e11102714bb81c93170d44152ee1ca9730a17188a30c54220ce238c253844ee2825089e665407514e45c14537112a2980e722e186385791c3ac98bc8612a15cc5c28a62185914570ee3ac88e3c871e454c5e541b86192165c731790e370a310791d449379537190c50470441c822af238171c2b26e06408a28cba860af20af26e28a2054c0a820ac820c8239232ae0820ab820b82385d64de4514c3146e2820ab8a082ae72e2444922ea492a6082a48e20822ae492205c72445c12443989117590415041570431c5c10c1175937950471cc918b8514dc310ae28af215c71d64c71e44a98bc8a10c51ce4718b89514c5188a2b89702eb215c71d64c71cb2494c5e545c0c819502bc8e6e0546492a2820acb8a15e4de438c2e18491d4731c62f2218e28af209b85714c515c105c38ac8e3964de44846e08a2c85c909c8ab9c871b92302e246e190c28de49150f24a84de41c888811c87514c186e218516440ab8925445731914628dc492a22495130a298bca8e30a7114e4338a71ce54e4431460c39125c18a39125d49392a722e1c30dd6438eb22145193015912a60a32054dc102321c431c654106411c71953249524951249512a26f224448a820a98a288253704911c388c8e3c823c8a924a8792545c907224922a484157395146188a30b9206544a989514dc514c371914530c45185c0c92a494c928a6e28c37195114171cc0c819514517145939c8a315c0c92a2b8273950ce124e39863219c9186544e429e4510413145104e430e5c1182504e49750c2286410c32a495c6450861c9c93a92538c9b8a0e43ca8a249c8591b844428c4e14f2388c271770514dc49254303570ae0ae324871e454dc418e914dc641b84ab8e524971c7951714925c3a455cc4314615222a4dc655c50c492a212a26e147255c44b9ab848dc71abc98869144a88a2544c90d2e48e9710a20c8691522ea25c748820c921a45d4dc288290e29570411d5ce5c0c3577247488e91522a0a414a9922a4438827104119704371417106e38ca820c861065c105c105e54ddc304a914c728e5116412a4dde542a9228ae38eb2e28e91d2ae618e3c8a6e2492a082e3c924bab8a392ae628e970ae62ae0a971cc1b8b872a4730c5d644902a29920b920a5d47254dc50ea37970c9254708f23a55c524ae6e0ae379524255c731c621865c15c209ba544c0dd2e1c6e95144509844430c492a22b8513988494412988a3750a7118e35310670d45317247488638832a0a410654c1482952415370411064348e9150524854c92925104dd44a8a628dc33892514c51b867151249515c53982538d471841513041338233a825388a137142338444146219d45310a31715229923724a2982ea28470a88e3284c508dc2320a5dc0e1a8b8a621c61a55c1288a130885189c508ce113b83089e664284439453105702e321c32a1c259314222e0a29b89218728a62e145310925c43ca883c92a26f2e481645c90e30d45e5d415c495c73970e0de5d4c410a08bc861a85704171d64504759371248b9260649350430b861b920b8c8171c719304171c3b8c8e3c9abc8a3861ac859170c3514471e4930f2351c61a8bc8b922921b8eae48c352491242608d5e5c90a171491b8e32e2a064324a371470641570ae7205c4b8e45c0dc91cb922a60f21728c22321ca310a3170e38c82a094c128dc71105186e2192515c5398c8e0ce32a21c71c92a26072728a62e082a298251b863c87912491504ae244e09d4e43082e49461b86719114e4945792454338a71c9224a9861c9c91054129b927088c82ee1863921c79170971510971d44dc0ca2195dd43946e1a98832b924882950c20822e38e323a4748ab8290417065c91d2ea6e08a3a49571ca639462e22920b82608d5c395c22a02e3a8e6e08c430a98a308881ca298b86a22980a5c151ca6e1dc2208543094c2320a71cc4751065130dc92925105c1298a70886150c25304a370883288ce184a338464ee28c128c223ba6654e40cb21c7253bc8a0cae482b832bc88570371d464dc4926eb220618cb922871055c498932493170430bacb9228e570438826e38d65cc1c8571c43b98a1e4ae15c49284e5c64065c1e4ae4980cb8c654246e192844450c16442c9c86a195c41863229c138eb20865930450c926321461950e39244ae4889dc0651748328a4c35107306e20ab8320e209b95260ca28b82530e4491854220ce51046189ca11141394232770a113a664286508b8110e3128e508ca11724650e5708ca11991c7088a70ca7088e51ca11993b8651423284523ba64c2921191dc991acaa839de4182995038d422e006b2e498ab8a08571c38dd6450357915702c855cc518446430461101a8b2e498838d45970a14b88a611501154cca890880b2a298c83c88dc118238e38d642c8c544854e4242b2371c61115022154e30350a9c73088e314e308ca93320a5dc02b295039549dce414ee39061432308b838379132ae22989506e0f237906e25c72a1e460e545c4942e6088c86704670881c92a22b8e638e392549288a1704e61193b838c3571182b8c71ab86511844518a118464538c509c6110232771d332061170c518251845c088a30c251845e6471c710c332770c51845274ca8e929c86755330ddc50770c853852192a9dc70e548c327719844431998a1425118ca6aa049dd2353504a4262603311030caa97707350234a8cc1422931c6548ccaa39253a8a319ba4ee1148ccaa999999903b987713200e39cba986220c2914cc819c532ee0cee335350701de4463bc9bc8045cc280665524246e64aac922e3219b98080405e544d42a84413b98980c2a8e6e622154198e0a117198a28cd564398e186e63aa8770308a8e6027151cdcc0e28c8982841731701710c1b8e221c221c4d64728cc09c438981388e6a39b981288e570e39c9463946e6ab2e0e3acb84222240c49839117500465c6a6628a29216549032a2e2628508c830c4430a370c45405c0e5cc30888492ae2888192ae0889acb922830892b2e49998053903222e61211750720c2224a110a11397132a499aa80e63889a824e09c44d5c088e498e0417590ae0d40d55e4c381795240cb988a838440c3750446541e54cc38444986e1e40ceb2618619124930c5c5470e20c271951ccdcc14443893511c0c80acb98105cc082a61472544de54502ae12e130a2b98e2b222609515c4c50389c8e14513951261e55cc7241ca8a2285cc45c7140cb8171102e18e371c44c704a08eae05c440b86195c711350208a72492a164cc9072a19248ab9229c47064cdc9092130f219862e220c0bc9218a8250dc3882b2e292571c444194128a722825924dc338444d6471c223a89192371c4419c22b21e4cc71c20b88e38417131c53841711c709c4d409c105e47088e1710a1c925704470b8a8938e6088e17112709c54e4388138c92a337304989815cc082a6041537930990b2e6223871cb26488a89398302724b98939844438455c714771c4471c2260324a924b8eae3844448ee11391c384472a3827112138c8e3c995c719ccd55c004d5c4d410126ea188b860622f2a0508b8d4022ea393302202120ab9aba40921570ab222618308a82a5c90d2e6484931101055d24844419524889ab8310918445c91848444089bac8a24222455c045cb249998092b98a2e261422a044959243a49504444844dc95011724cb2499aa8e03a54c1c1953113049cc93889ba891c0a89173054898224951375498a249731c42989371c54c39275144e444144892a62891054dcc49c26220e2320a73088119550a0e260a26a90ca97306509cc70c88809cc220c955d49090135754870a8f222a382452a4b829388ab80d4520826055d2e0c418aa4105c38aa5d4548e3cb8a2c8a9751c751110925c93a8a22320520a5c9088e171027484171502204565c0a495052571c4408c8e950a138a4aeaa484926a1d2ae15c2220e232a0849d420b8a808acb80a8a6914571cd2e492e11102514d209469724e1115070888115906925c27112709c5409c4b2e24e111e4a75530925c7115011590138aa5c48c91b84419c22a044b21c4a971d54749c93954ccde430caa3867324e49c663aab860866551c929c2a38e50a8c66f21088c80cc4e207489c9c70a111e64a75038aa64e02254c94ea1d32724a53a98cc27170ca0ee918c221c6118ac9c666e0154ee1314980c499552ee392022749ba81444c144408bb811022772aa5404540454ee9011101113ba474aa808a808a9dd20449502253ba4aa63a472a8ccd277088d27320ef20e32b981426712983b84a239839dc79284a21d25184a2727194dc59955009971ce0e771993213320504a7751300514672e112abb80cc440a3355010410cb898a02591412cb98a861b830c830c8230cb88088cb22812c8ba8ccaa11032a844ee7719893ba6665e5e5e43806554c8446673808a142653ba8984860a132a299845caa997700615150418550a2bc8cde422559902a831954c4400455cc1870887089ba83b8d4cd540880e993171321d32071526640e32a1c398aa65cdc10699074c9b8e2e22602642a65cc5cc70a990a61220a98332153228e54c8a3953226ee638990a99054c9b8a2e62238504ee611550c706990c1c73154cb8b834c80dd641244b99225cc5414cc82386188618bca8925d4492ea60c3950d2e20ccbb8990699069971c5c444c8e28654c8e19532e2e025726641c64a1cc30e4412a8a9991ca38e61aa6472864b95322ee053224a99132770b888571453b84554045c184408cc838c532037590e924d44926a20cc834c844418e34c88e31d239a64724e34c88222ee022e3892b84414cc850ca99104a384130d53248882a64450ca991322110c4c8422eee5530114c81102308a643242277712991454a64ee5519995431106114cc80655311030a299e4ab320a0cea335512132264e2608898a0a1399844aa0ce20c34ca899125c222861089caa1861089ca63301131c6330d5caa9908899773b871b99bbb803399901c061bc954223393bcc80898155dc306a38a751477199542277198f29900e5750989800cdc22559770e0318c954c438e066772acc81dc3062771ccd540208645cc387304409cd23a4644c044ddc50a2cb8a284a04a930441597130a3964c10a73044a04a61ba4148964c457750c30c3390619c8620209baa4046ea93046322e28650a91152659704a184b204a394e4312830c5c7548e32a4c30a44b2e2a1c73106710ce699018632a0bc811c9cc718839862a0b823398e3088e19911c0964570885089cca286128440844c088dd259524aee0c304722e0b2ea193253b9995642277198155dc06112aa46673ba53200f26e7979001dc4ce575050ba898980c1449542a99cb844aaee01dccaa280d46430328ca82ee55028c6430d4ee55331106264071c4564c015913770044482226eb200c2b22b218e48e97041711124b8861c869724e226b21860c275917702422e3590759121a4220452e39ac9dccd544c8045e4064404cba89899010425d40b2ea326ae0812ea6382a5d4c55c0bcc9819001753912a2ae0484d5c79505232622f2607044e443244b80af26a0e6a990e1324b89a833aa65cc64011dd64c0e1539190915053207135065c3883ac857060565490621c655e4c2417590175040a83514654488e0d441d4c3a8cabc98a8311c0d52a1d52e612ea48154a8714545973150714acc8e14f209214418cac8a1c79597350e601959032e142a49221cc53c87514f22b20543a8a228665cd4405261ba8e4815498697514cb992124324805d640b89245410c392455e4d438730ca88502a930a149ba8e20cc98e38990438f2a48c98190490c9ba9804cea620134a9cc29971913022049d4c5279020882f208164d4371208326a4b8983201353985220852f226ee0013791022a6f20089b8892424a6e125371e644dc2c8570a299020ac80b2e7228a2819032ae7220e5930c70e23a9c8ab831057498a2820ab857931704494c104a931751412a5e64dc0c8a114322863850b9c8094e55c064ae21c0ba4dc495d4591ca9193711302205164c5c502c832c8b986a025749965c0ae6128259711359141c4b21c9931c79028ae3260f26a1cc754c8e1324b898939a8e54cb98850ce524b262b2604b224973020b988a1590082a72071054e5c28642865c4728e2b21c448a8710553212f215c51451904150620acbc98e04c5245e410a28cb8a28861a865191c351c3590c351c359179310f23920e5c905d64c1032e2924882b22924882b2e62a385148254b98a0b8a5144191c514b988e3952604c29b8f22a09533261c7130e2a1645041504159932410a22cc9b892464105471e474a8e516464c0c8a11522a464dc493892c85973045242593142c9b8a98250a6938133a44149d4d32e3947049790492545190451cb228cb9870c812c850cb9a981026e63a88a14d204d2e3a42a619441991c0c8228b228c982064dcc03260b9a813994409cca14cb8820f262872c98994094d2590a189949970e670941915931072c8394d2272c982096402593044171d6410727244c99c4c09cd41906650a4414b827593177503040c099ab809b8c8bc92264911240c34cab922262640959120614e455e4d5c3097014c55c2bc9ab83799101862b2e1821248ba9c8a39214c3026b2eb205410b2086150439862b2eb22018cab80c519751061ce5c30c18ac873143a988a15cc4a8370357531975061865c0a86185643147350c39a889312a38975350e608173519751937505112a2544d43126248a90c09a8359751d22a44a83511432ea248734b860c5450ae6254912ea62e05430a6917952430a5c10c2a24c912a6a19249a8b820d45179513570695240a8e389872af320dc14e450410b248bac80ab890a92106a186b20e455e4dd40c1cd43197510c298285d40ac8150355145c0bc9ba837902985d5232221814e544983512e0e4906a1d44a9c8bac81ba81cb830e4430ea2989512a722eb26ae218924d43a4312254c5c1bcaa8e18612a298ba84baca9b881a5c6643070456412ea25c64dc0989502cba881ab80e5d44e4503046b2ae18350c514c654098710e27218e3988e15c4712e26a2864ab8e25d4c1b8a489357512e48697531957914141395707228a6082a15ce5411cc0c5c0b9c8150448ab8751457131c4ba8950c34ab88e1e5452495713957930c10350c65d41c820982384e5c30c4306aa0d46470aea18575312e4924aba897143165d4e4304135240ba82082ea722eb205430350c655c1c82098e11c272e18a29c8628e44706ea3817530ea298864b861872ea1864ba98238545098cbac98ba8624748a84ba8e91370a950a95106950695130c2885135244898a2b9225d4c74921a5d471d459315703150c314620cabc8628a209a89104c524451441971471064d5c1a8638d5e4c348618832e186a0d44902e3ca8e9052a6482a492a62e28451a4317950c104dc514c31244ba8a9312a498ba8e186175931750234a8638e2384d52f320504de5406eb206ae08590a92186a1d40a9ca81ca8bc80ba83707228c51cba895193570386546e2246a1c50d2ea15c470ca80dd5215371e430a46444de402214c0c159701bc86ae615c50988cb8286128cbac899141952f204597111454c832c815c6471c50c39c8614e55c64c3057101cb8ea272ae18548922861ab85791370c2a44394526ea0dca999104298a24157319142c8310d414c409acbc8186b2e1940986b2087131c9112e152e2720871302e4897139579301970b2164430d43288530a6a1cc5519790414e451714510c350ca323942b8ea61d4751c4ba89753914530e6a1d40a98e29ac8bc98b8608a289c8a48604e5c0e5d641b941c82098228e272e48a1465d64c2b8250720e4490abc812b9248861ce430e45c907248bac98ba922a4c50a2cb988a28530d45c0a5e40986a244712e261c491c4d5c31261abc9820a8530d411545c51429790a61a8952923a8ea6e194512a61cd5c450dc2b8c98b8530d220dd23a543049371e42ba54c0b8ea3c8371c4191d2a62ea0a43987314b830ba566404e45141c92ae15c64285c516430d4104c3597249255c64dc1c8e484159144b945193750190f26e0dd44498571c4191432b8e23c9b86195228ba8e590ca919117121114186b22888a186a088811997032b8828a63215c1b839072a04c35244898a29acb8c857061964451461a83514c51ac8bc9b8391c4830e45c495914387223ac9ba8808272e0b2e0450cb889255c2832e2722839c81bcab860827218209ca8e25c4512e2625c9152e2492e48a2cb89c8e25c41b8971312e492e2492e492e272af20830c6430ab86506e1ac8650c35910ae25cc5249571454b9c8e3989712e72a38e638d470542b98571cd645e4450e39c823570c104e4304139512e25c471c4c925c925c44b897139142b8871306a25c451c4e55e450c21ab86105430d4328c8e398971ce4718e3951ca29649298bc89b892925191432b86082721c43898a388a389cb8390c32cbac8171d410e431c7218722e4921759171251464328608dc30453792497591ca492372440bac8b9a8504e4508a2c8608e430e55c524ae323849243571c64dc08e50cb80cb9a8771944441944924c74832892498298ab8a2bc88e1949186ae215e4dc1952e24ae6a22a450832208260826a48e911d225c4c3883208f26ae19430d5e430d432887548e61a54924c3517142285e45c54829104648d491c414982924d5c50caf2194512461a8a31702f22e6494910c124dc790ae950430ba475171430dca970e571350450cae9245c385cc71a84440dca218e11b8ea110a1199973145053728692c8b85165c50c702e61acb8a18e4986b2e20a84995c195c52597051b95c228644409440a3971284965c265c42b8a26128b832b8508cae114c9aca80dc4181c739517939030dd4474c8730ae381ca9238739571903505357103912450ea61d4712ea722a25430e721d4702ea638ea38925c54e545e4d43981a8a41aa5c144a98a83590628a9351165cd434cc8e49cc938a48730e72b2069597100a632a248e3c8a702a2b98a70a2b89ca8c81a8850ea60d6465cd42a4126a2935126e9971071cd4425e4124b8ac980531915060ea1d4e545c187391072389751c25c54c7124b8a8972497539150c1ac8e398e39c817121b8a8925c4486e2a624971124b8a924b82925d4e545e40a29c8a860f2398ab861c7319061c88e12e2a38975309712497512e24971539150e398871cc643124b889125d4928ae621924b924ba92724ea632af26a218e1871d43a8b262a0d6450c748e93510e5d470c1d45915262a18748e62ae2549795310d3320e39a889925c18e49cd441a5430dc0d4457121a88ae6a19c4a8ae25457359190e0cf2a21c71cd440d4665d44c861c73150e398860945714e62a1c53a8875399503550a33872b2e62080d2a2950a3549869714cb9c80408272eb204102a61862eb2e0c1051970450b9ac8338a71cc5392731597301ba871a9c819d4719cb830de44643c8483975930e605c1020cab9c8804e54140a9cab8990a208715307530ea3857531950260e272387510ea38a2ba898e38ea638ea25c4a92ea632af248214c50ea632a0e721c2b8c8215c512ae326ae087130e238971390ae3897531c1b981ab83524357351144ab864b922a5d4c925c4a834aba921872e4893506a0d65d4c6543882245cc712e215c925c4e4512ae489550492555c43072a18395712606430e554912a618b228b22ae262549255c34862ca861a8b2e61a41a8b2a1a41aa55c0987248ea0d65429872486a2cab98cabc9818632a083a9830d6455c10c321cc39a8731c925cd6430e6a1cc72497359150c710e638c8a2b8351c15731c93a921a5490d2ae721cc70457351c731c925cd6455e410a1d4e4186b22a0c3191471d471457539142b8a2b9c8ab8730c4712e61cc642a920d55c9122e0d49026aea6492e3921a5d549041972434a920872aea72389730417040ab9a89724973040bb81704197359151c492ea638e6225c925cc71cc64105c0a9204d5d492449245c9241350324862aea6482e0921750490a921242ae62083248695505248695570419052e4821ca815165d4c925c4a8297524970419052ea632af262a38e931c749886144524751351c398e1d5262ae0a2a055e470e263a4712ea63a491dd474862b8f2a62a18628a620cac871249731d229c79312a2b85548a973152430c52b2e60a449923a4d43126a228532a1843a8e49d4c324ea2a242b2e1cc311d215c7951d2086e3ca992398e91d26a2a1a43106a915c2aa454b9861a8ae1c8ab8214d228a830abc98a8238e619c5533224f20e3cac899730c70a0bc9a873041390a20b8a15445145cc2882e289511451739590c714e6a38f2081530a6e04c3795970239c8e1c75910a2bc8e0c57951350e224428b98e3889105ce44a8ae0d4924549255c49072a192ae187228353ca922872ae2625457249515cc548a9512ae1a41a832a492ae632b20cf21c73914e14f262a04c370cf228a62895310c298b8628a621bcacb9a8990106564c1061cd64186f22a38e21cc7190ea3820ba98a2b920a8ae72181350a6e1893515e456470c438eb20ab22b98750a2bc98a8a724e60920aa824ab9248822ca824855cd44986e481550522a54c51526eb2186e082a48490a981502a6ea186e482a482a628a6eb2326a2641d2b2608670ce2a38530dd419d6419d43ac8c8610a29c86e19c54338a2986ea38a299d4470cea19c664d5c430c430261ba86748910a260c52ea60867145470ce9506a262a08a0986915906054d40826a20cb8332e381ca830e72af238106540e491579107390c51c7510ea28ae272a0e3202f2638e628ae3921ba88224544a82ac8b9cab871c541062e625c492ea212ea4869713912e4839750c24d5c31640c861caba88970c2cba8530c3cca92254c51451957132434b861c8a2cba8950a61cb85306b208735043597512434b861c8250e5d430e41b932a04c39047504b2ae272a29c306ae2292e1849ab89839072a0e450e72ae489530c714e5c924c5164410d431ca32ea20e431472a18229c82514519510f22831950a638e7209430de545cd4925c548697124970d21a5c4c31c6a186b218a35165c0985391c09a821aca8130e49026a0cab88690ce2ca8530e4115c995102a04c12a88a19465cd65e40c2b218751c75390570ae722a25c4b9871cd44492ea492e649263208137243524904d5d432413724350324862aea605c1242ea082e092175311260832e14c1ac9204c395750439043970a614e410540acba9920a5c92441065d4925c925c938a98cac871ce449882a862abc8e1543055e4c28af214579315040ab820b992484c0c9218aa92484c0a820acab92484c1a8a195249098151c32ae6a48a970520b98130e43082a0565409872082a2cab8130e410545950d22a55cd643a8753127524e7206490a921242ae092150490ab9829052a486ae08295152e72a32e2a3830e54182395790e09c828820abc8102eb26a383711c2b898325d430d2e225c325c4e42a860654490c3910b228a1915712e48397124910b20e45d4c90c3950c390464ca88690c3910ca2c823a8322ae492248691514328820acb9cac838c8e638a288a2545e410415145179350315241a8b8970c571307248b2a18e391c11ca88791479524911479517241ca923072a2486a064951735243489218b848a82e6054304ea2154328c8950c351145197143288a28c8a28832e6b32ea381065418430cabc830c6438eb20af2614539151c6188515e428af26145791cc55c0b8e6492e12ea7219209b92188a2cba864a864ab98690c39704190c597524950c5573951c731c739142082ae082a082af208ea28af26a2082e3992098a2ca92189248ab920a920ab9a924b8e61a414a869155c548ae6b238e6082a285c539a8e2a45750aa722f2a261a4371c4b8820a5cc4a8554b861a54315459711c750c750c7571041793524938820b98a90c55488a28832628c514c411cbab861c47351e430cea97950520b8e398e311c790d22a5d470c575164c71d2a38ea2c98a8e3985515c7914e9350c548a6a2e08a30c52a285e544324711451064514419751d238a2b88f2a6a1827145105d43ac8209d2a6ae0453486eb229c71c751e5491d2a618a924d443aa4531462ea0c2a79131c209a6640e61cac838c8105e4c2c82ac881032b26283510a28c9ba818a8317241a88517307248f2a18e3906a08272a21e491e54924451e544c3254488a2ca8924a924a89ba921882e48620b9924a86914195124950ca2c898a92495114513759950e990e39c8a30a29c88628ba82098a25445144d430c31570c28826a0d5e655c10692456438e721c72202b22b80ac8ae61457914e62a492e09cc904c0a8e1950c15724312491504957351c73243515c10545735124e49cc348a9524ae092a2b9a86724a2986ea332a121590c28e4375067510c514d41ab8353883538e332ae2061cac8271cc29e428af2238a7135249105c90d40c92a22925175041706a494428ba9820b8a91522285d411491502ae732a1c13a81535240a8ae09cc519e565c242b238c28af229a87514c413924a8aea38a7530a7514c4714ea29cc518cca838d43150a338541997130618a2a0d5c1aca81a9d228a88538d2a1544c11c8211a5d32e618e02ea72054908351c39ac8791590e150f2387351c39aca9238f2a32e03590a861c8638e6a38e6389735952430a72a320a29ca8621cc39c8e3a8e09d4c71d4724ea72a48610e5465cd430a190a1971c915c326a23a40d54510aa17061aa8a2152a1730a610de541a54220cc809c87508e91c33a8a7950e95190c19e54511c514c3751c33ac87516464d428434865410c229d21953701924d41710690aa4e14cb8092eb20a29ca8a21872381751c1531c4ba8e289ca921872a321871ce54510c3914571c2628ae384e541a835919750e1906a1246384628e541a8c8a3087514c0a8e431975309915d4623851a5420d42ea3c8553852614c8190e3508628e6a0d64348ca8509219570610d2195398430a65cc6440650caf22061a8c838ca32e60e398c956419432b88a74c8e15c50a7214c70d65e44492f214c186b2e28e3a98e12e2638a6b23853898e39a8e3a8925c47539791324724a495e44394418139254418724a8bc9a8e2a454b88e24c49a8930d5c453c98e90ce9350e6428650cb3221322e264186b238e61a8730d664418651e645cc1645710a4964497350a6925c354cb881c86a2061ac880e6321a8b8924c415c4186e2638e6a249710e2a489170e5153912493121b8830dc4c1382735124b88925c4c13866b22f2061ac88a15c731c6a218e3a85730e2351990e514c4145711d443944c49c7510e513997314187224ac860c3925465c5246591492cb9a88328839447254c41a4351714f21c61a88a371e4c53a4549a88b320ca207390d44904e09cc71a8e51ca72320ca20ca2c8cb832887187221a56428a991730a49644570b27351063389532e64850b26250cb21952e20b2312a457359141cc186f220c3195914186f2186e2082eb2e0e38c871c64c104d645041704e638d65cc394329c8728e72e19c4428c3791c4ab20a720871304389a8711c515c4c11c71359907130e6a1c471497130e238e26a1cc71457310e239271359970205ce408713951c4b8922b9204b2e26492e2a454b89228b2e28b208ea4cb89c8e25c425c450b2e26492e492e2492e2a432a5c4e564082f20448bc98730e39c8a92164490f22e164504b2228b209471d645cc9152248a917045904a4c88a904a2c8b9c922b8a2b9920b8590b2e62492e492e248291249173959730ca49443c8ea1c759171c2b987350ae2895731c4b9ac8e05cc39a82282e638e6b2238a2b98a2b89515ce47049731c925ce547041730c3751c2082e6186eb22f21c7390e6a0e721a88a482ae482a092ae625c9032e6a492a4829572414a815165cc925c548a973591457140ab98171c26a38e1502a2a5cc505c525cd64647020bc9871ce5438e720e72a2492a092ae06490a924a9251732497032165cd4516454b820a8b20552e6492e492e6b205490b92289217304e282e6a484172422b98e39ac8cb988251cae04c10e272187310c398cb820c643065d640c64350209c82ae1cc712e6238a625c7298c8e398e394c471cc724e632e0941056418832eb2609430e72187224922b2184a1cc39c861c89248acb86105471cc71ce430e4430e491590618c82a38e638e721872248565cc5470e620826a0a6430e623a54597249388e90ae91305238e20c9a820b8e388f263a4749ab8930d434bc98a1d4c39a923986a21cd23a8e928b87548a2ba4c39a54148e930d2a2392730d4338ea2e62852285260826f2204ca195c104c3714ea638a739043098209b86750cf22a18e20aa664328730d443986a3922b9873510e63927310260bacc8a194453865388513ccb871ce4714e621cc19e45490b22245c498a2c88a48b9924882e49220b9c8e3992724e621c4139cac830ce321a861882a095c329e65cc398ea38ea238a731261bc861b867950261b86750ce3ac8c8e09cc19e54186f21a8922892e28324b992724e6a18261b8675904130dc33c8671e5464c728a2194591ca9190ce51ca2194e3c8e548c9b88650620c92b229259702650c310e49591492cb98250d24882b209434922593141924dc5412a4348ea62852184c430c8618a5c30952754cb8105e4082f261c4389a821441465e419e428af22618e388e389cab8a06442c8a286322e16428e4450cb22861ac8b98a2c823a83221945904a28645c116412865910ca2c8251e45ce4315c2c819711c5398650b2e261c4790ca0b8a0bc88711e4505c7913951432c8650c15910439c8650c759170439c8650c359124950ca19645cc328b208ea0c88690ca91714e194431464504419739249704190cae2186e16457130524b82925c493924b89cabc871ce438e72a1c7390d4492540c8195704a28a197302a2c820a8b2e2a412a5ce40c81972497314e3c8e3c9ca82485c115cc2b8e6a48490b8a2b99271cd6464082f21e4c38e72a1c7391d4430e49288a1865c514321e5cc105459152e2a497390b24b920b992724e72a484972417304e39a92125c939867591971020bc871307104e540c859104391432c8b86488a08b9820c8e1c88e1c8651645c92441065ce4728a0b88e4a8e3c8c8e388e48c9ac8e14f221e5438e323a9924a9257145914597114e29c5453921b882753045106414b92724e2638e209accb8e30d432892065c4b98a9152e49ce4538e991d26a09c13c92a3a4a63238c350ca2492e399271ce471872a39459152632e26047390209cb86751c7288a3898e394451c4e471c412982704e5c1182390d2eb2184a38e638e7218722485643094718721a44159710ca2841905264ac8650461c965c12923096452425971351c1388724e32609c1350b27041925c490322245cc538a7104e6a49220b82905cc13826b3204f21a823386a19e65c5186e38d471944506493046e48cf238c3950ce3a8e59191ca11ca14cb8813c8e638d492441704e608d4138e61acc8650ca997146288e328b21a46497130ca08c392c82484b22485c5064273570a290a2971c5388f2638e20c82749a8271e413a4c71cd2ae29d2398e351c690d4433a4950ca2e219522b8a138c820b8f23a4c148d4748c35724650c450b88a13c9823492e3a8272883229c29351d25044130dc790d5c32a4f32628450b8730543982b238e63a861b8eb2e492a492ae32194208261a823986b20e49519061ac8471cc704e430e54349465cc70924b8ea39464124a190492865cd4508e92549191ca10ca2c864c1243249b81904ceae382e182e61a865710ca10ca13142284dc33c8a70a5432b8a711e64328411cc104e430e54928c86508e30d432c8a32e29251864124a19730a1925c6a28492864e32b9253886708d2538532622642cb89905cc51c2590322b989430952590ce18952e164e38826728a9930ce309522b22a039c89e425414391530dc40a4c8a9261b898721bc80618c82eb20467930c22185e40cea0d2b2a48e3862a04ea2cca99205450a65490470a8674ca988924d4348b80a9d409d2b2142a0a6443932a4899211b98671a644826a71852208ce14bc881453913c94249310dc3511231394c39396404e3ac833c94c313c94726450e4c10641064c430b8613a8a908ce531ca3088670a6414b96455dc01b84472f20c220c22990c3243a83707248a0d642c98bacab838e0c91b8acab9881640a8ca80dc31591428d5c914628a72a18209c8205d4388e38ac815041593579141855c3246a154395644a9b8950c2c926ae322ae0a1951c0dd44b9228b2e49aca870ae388272a2e60206ea1957184444870628dc547957101d52ae261522a45490a35040aa542a9b861bca9215c731c623ca8b815c6a970ee2605c61110220c22e999724039571182655c23088308a532e7207065708c8dcb206508b891448c43286597971038e5c4c065971cc544945191432b9249923502e1923208326083249abc832b8a12424ab8e1054e45c91c4b8ea29cb828e5c4c91491965c1cb2e215c26a0f2e518445c1422e0372b8e621a82192371c6a09462e0dc263846a111c650a17194232e0e2e9990511460946117749851ca2e91aca81838e3209a8464182718465c139c8e06f20d44926248e3a8e638ea29c8ac851a814571150538ac8750eb272ea2247189514c548de544c71249a891abc861c15914d43882638e209c820b82065d4105c148297591c71c54724eb26b23871c6540a98e388218541055d4105c125454bac8228e2a38a75939751c925e411c618a8e3c8a2b8a4bca9228f2a648a2ca926321d46388e29d43ac8a93145924c65d443c83524516544a9c8a302a2c9272ea0c908e541655c4c146a1909957184440a35146ea2398114e9512a6a0ea3570a30a82e219c26111c619c2308c9332241a83a8a6228e6542655c4072a7130704eb229a92085105d42a9e43a8f26b21c6a0d532e0e45184548c319525c4192395384c22182308a532e12751183938461126497390518230d4232147194232e32c830e51cb2249c8e28c51ccb881c86e260b22b88d4128a638e20a824b82b208324a9c8230d471c41504b2494e5c518e928a2284e43092508e5c448e41cb86713125925c5388d49184440d3271194519251c9220b8ca1170671194119c7119422286508c9d321852730d65430d271c811c9c71a4233c886aee662aa81cd54043260270c99dc294320250c99dd4046e190250ca811864a77199542220c2713bb838c227719980308a465357702a89806615150621cc1dccaa1c6e1dcaa3c8cd2112a8d26022608519d255384469373ba6666664043b8a01d45d2727155d4283a4c327285d44c4c2400d64c2e22aa80c2e912aa65e5c0cc0398ba64aa00e62e95950073917990495d4498730d5450aa6ee20aa38e5514eee1540caa2773134c86aa6220ee01bc995401bc9aa8e0253502e0dc755142ab99c8670aa18655146661541cab2337971d55e6406e600448bc8a9804922a720b8a9bb812064c655c0041957124e55cc0e7221c25c4e43013971c1c735731c486975390c08e13571c0b9c8c8a8670924c6431c186ea624e640a640a64c443044c98622eae38c0417911c30e39ab81711121112117991c9022e3cc9a862641c6a9924222045c4c9cd5cdcd54132080540a565cc12153704855ce4645cc0322e123202a5c4e40a089cb8e03c89860e455cc9241883154b9c8208790f2a4944dc12430d4591522e72322e60444c824a632025790244dcc09a80a5cc9590909b82a484b2322e6aa1547123824971357498c8930e990a14de425cc49a8e2497131c492e26ae99310e639448737348e95915531c1c7993092c9aa802eb260388089bac9b8305170915059524102b2a2e6a602ea0e261e412b2a1d43a565cc4a9238e208e38aca980ca823879150470e6a38735159371537014ab9204ab98a54700a54c05526e2a9739900c5c06e32b261645017300ac98082b26e20ae604c09b8ac9b8224542b84b9c821451370ae05405cc92455ce447245165cc5020a9b848982244153791530e25c4c71c5490a62a64c91c750a214de4dc11c751c75130a2285391263832a27208e388371c54c914451642a4dc398a2bc89cb892382a492b2648e0a8e0ac9b8a0c8e388e152491242b26283238e248e2a38e238564dc54dc5487240aa5cc414c492a6e2a93041548504154992082a93710a0a4953026971549bcc805ce40a2145e4dc05cd411c394e415cc398eb2261c4164c1c95c094c12b8132825791370912984894dd41ca260e513748674accaa989903854e428102aea389cb8208190c10272ae097351531c7030a9820ae48a9c8a1c71530410e638a9cba98e04770135242f2a62e08202e6388e193524121530909aba893ac983854d22f3261c0b8f32609706ea614c64508a04c284dc098537530171d4c65c3a8a2032614260853144e5c50a1370a62820a9bca837017392490ba8989712ea08e3a8a260920a9251391450c8a2b87511d249d4928c9b8228a262921054e411c20a98929853197531ca24c9112648b869092175317140989244dc298129ba98a08a489822a4dc284c49ba9b87254c49ca6f202e0a981398eae29e4664c24b261c39bc8ea0ae384b2638e096492b9b8731dc7990a734ac8e51264b8f24ac89aa888550c71c24c9754c988531320e3a8c89325c90dd532620a3953262aa6184c9954382380a988e1cc5d64c0417350620b921d43a564c90ea1d64dc10ea14ea2608238f238f22a7204105d4c50413a9cb8a98e01498a809ab9a664146428af23828a32622873150c09883157931c938820ba9238ea09457931471c471c54c488e91d451644e4490e229e4c5482704ea2841793170e530e5391471c4153141382a722152604c32c8ba98e50149881150620ab9a66409cca089324a2145cc19056554c295401505e54c70ce2871c54c10e95244e41c2a614c32ea6061539a664501305e429e54c71d438ea614c411459144e4284c29cb81298a19152ea60525315d33219493a4b2aa60e6020c92ea63a664c39448417324ea3a664caa2220441299310e9901882f2a085498730645448b833261cc052a734c874c888981c53a64c4c38a74c8a70d2515d32194e14c39254574c89984c8a724a74c99922220a1308aabbb8550c1043008272ea60861317910186322e0c3110a15cc404dc0c5d4302144e5c30209cba987514430d4513117906e194083737061710c2a32aae1818622e0251755024d45c1225cd45cc382c980ca828a8248951593757093503970620151506a0c31513702a08692430e5455c245490d2a4860dd4306eb2a2e72ae612153041b8054de40e5c5430c0a81537090ab81a5451739506046f2a26e22093122a2e144126e905374a8b992065429809b892152e614c4a849b820ca9b8c8608a289b8a2495730197240c92ae632ae0c09cb861ca8215c50c45c10c350b215cc5cc90c354b859142b88170c91597124348734ab822c8a28850b9837145319713904325410545c10c950c9517314910d21a54106414a8b8a48869052a18721a545ce55cc50809b860895144de404dc2b81055ce547013791c395172495144285c185cc52495145c12495145ce4285c2b98a48415712e389ca860de41c8545cc44126e212498b9849ba921832b8829b8370d465c1c828b87129892b925312e524a632e6032570192b9a850cb2e0c32cb98924dc4718544555c088924488e12e2a69570c3120a695711248374ab89aba4c92424dc390d22ea08052ae0297535023517034ab864c45c126188b81aa4245c48574b8982b8a492ae62a9702604d44824aa5c42a440823548b9850524ab88095d226ae93144b81065cc2b892b9ab8a48a0cb92285cc2a5c0b9ab983055c08cae621264ab891b86a628c6445c04a2e034945c3125104a6e60dc330c4428dc2a20620a8cbaacc80e6b22070c1d45cd645c1897240e62a97350973069107514b831471d4d4520c924973514b9ab8a643828981101bca828157951375903750418b8750514654404640d43026af208614dc306ae322a60a2bca8106e1d4654471c39829a8614d5c654082f21c450aa61853570c09a861ab8ca89bacb8731c39c8891240c8b8990404d6440c87306295907591c4ba892488e25cc1b8f22b22ea089191220dc3c83715103514820c8604dc398632a32a1cc1122e06490b22e6a3897305710a20c551734ac8604dc30a7216451c5593706e0d4502a6f22a0920b989706e3c9817241cd5cc2b8a255ce541b853140a9ba87302e482e6b22b22e6a24c90e3ca9b853127206470e15937104712a245cd471c39c8922b8e485975112a48195724156542c86386b2ae26a61cc70428b9a541c5414814ab982a8a2ab887249551064869551734a9c891042454c50448a9ba924b82144c102a6e9590448982244dc4a92165449072a0e41a861646544c4a922832a24861ca833c8730c51646544dd41cc39b8a412aa20a60dc74aa8982554418891d2a2a6e9593702e1e490b2e60dc714573915045098391262e285591471565c2a8208eab21e47085314655cc29861c26ae0547055c71c5150450ab9c8a987906e248593244a9b853140a9c8351453971506e1cc39bc92099249b8920861950471c644887314e32a606410c32a08e191c910e629c654dc0a8e0ac870a8171c7159302a38e1590e1502e38564dc54dc71c47249730a604dc70ae72a486970a614dc325e545449869124549861c8b8e0dcc0a8204d4d4702aa0a2e08e48aa9b81324549a92255490449aa9bc89302a28a26a3851512e487515370e6081735126092489abc8a9873249710c09a8a29b8a254c254de43026a2815370c49a864abc8a923a4c39872e24c390e61cb8817041550448b8191c9155302e482aa392248e48aa9b92255448829531c952474a9bc8e48a2a25c90ae2a63817324711c913572493049244d4398249abc8a9bc8ab8102e6a0295241026a957112081354a8314831c73514ab89aa4089135093170290e3a8a5441c4181350c49ab8aa44c08515c552082e0c49a869715498baa5e640893021c2a72e0dc56471c385410751c654c3854703506af2a1d44dd640e614c2eb22e2449ba820ea38a9890a82489752454e41d47151c20d43145397241cb8a982489751d22a1e49106e1813751c30dd64515c1bc8a9cba9218410ea1370909a890a87165426f2a2240c9a8130272e3841a8137243715061ba8e214c30d5c502ae0540ab9c922b895142e62a648470c3751c1bac8571e45490d2e18209a8150450a9b8624d43126af2a2542981370c37951391c2489531429cb860b8a893026e28a60541054e4514c0a820a9cba8e08a13049375131c1a853706a2bca9238f2a21a434b8150450a9860826ae189350c357951d204c370cf2a272ea486e38404d4263813a9862e25438f2a62543a54dc2986e32a2e1890a822a491572450832a48471cc391d22ae6a12e05d26b2186e48e2c8e2a383506aea1d643a8b2261d45106470c5750c450c9ba809a5437970131261750e4714730861751e5c6644405730e6b2228a072c8980c37931702c89851ca62eb22e242a45c2924ab8a4c2b8a0e63a8b9a540ca2910a1b8a5c28ae4949255cc5204e2497131c925cd452e615221c731d45260ca910930dc75149bab8a642c82140a8c9850e21c54e43041506e0dc41b8371539170a6281b86b26e14729c812c838e320ac9b8ac8a1831704175907105645140964c12871054de4c38e238e2b208614dc1c829cba861cdc30a6ea32620260c5e43a830c6411226e04c104dd64c70e60e72a0dc53a8c8e3a850ea721a8a5075929b85306ae0a7214dd464c5c7283026f206f2a614728c8a0dc186f22082eb2621c759013901397061bca9871c641506190c2e0417953175971434c837013750620dd532e1cc25cd43981354c848b819240c8b982245c0c8591459173502e08728b9a40b821222e6959731c510f21cd451429cb8983712ea4941c92ae224c90432c9b839242c9b889324503326e24c92450c9b8a9b9248921645430a6e182e186ea21cc39a837145751971c2b98e498e39ac83706ea1cc514d644515c5045573025724a244ae6a292e3a895254125454ab9c8a0986a054152415142a6e02ea4815730ae281573591739114702e61455c3126e165431c7390c371c2b9c88731c32c8ab9924a87348734ab87348734a820b8110a2e690e1a8a55ce410541b837106e38a983712e20dc1b8a924989914593712648993711c31d64924ae2a6e4922485470e41b837911263a455c31c4398731902e186540b920b98e05ce43126e38e72238e61ce41b8722ae722a04c11226e1226089137504389813026ea99244c88391c506644c91c0cc88a0d643a8250e33226e485910b238379170b228a2bc881ac8391c79517350a224a2e02e3a54424351173481109117091106548b9a564c4982c9b839019371126481937126481937150472c89112e18564c11c359071302e1cc31593704590c51464c3143228471d4519371141914714332638a0cc8571ca25c64dc1143208a28c98228640b821ac9b8a982b9861ca6ea38ea29452b9c8130d409813570a604dc505d64410549055c1b9248a823c9218ab982502e1854c0b94105450c9ba8951d21a54c925490d2a6e2a454b8a9152e6b20543145c308e48a875145cc508a2898a124a289ba8150415302a0a4153714170415142e6b22722080c898248191370490f226092289ba8289a409a5414c409aa5e42c8a066440d641d64105c48ac89859142cc88a1ce450dc12853791370b22872648a1c9b8a298750ce3a9c8a094c50ce3a9cb8a87054415222615220ce913748910692544d214418ea2697593242c99218b26e48193240c9b8922932648a0c9b92064c90b26e2a14c29b8530de4394c390261cba820981370261ba81305c10dd6464098970c2b2381350f21a8a396464c1a8a48c8e04d490dc50e464dc5143206471d4728c98228640c8371464dc45033208ea3841593142cc8571c23ac9b8e09643a8a48c98a0c8a292326e2a486a184790e618a98e1a8971c3153702e504a0c99238326ea2a490d2a62a4549a8a3a4c3a4d5e450923a8a26284509b8a114513142284dd40a82a482a2854c512a61abc8c98b8391c39c886164544b924b98614dc514c50ae6f2238e624c32b8a98e082e690e2950a2145c49444945cd21c7514a9c8930a6e24c49b88e2c922b8a8a2c8a0964c925450af26e2645264c52645064dc430dc1b8eb2186e49d454c30dc1bc861b837911c791c7915043994c102e6e24a624a6f24825324129b861bc88530dc30de430dc79153910ce3861bc883105d4924c298a094e44924491459137040c98209ba981348134b8714a8514a628a6e290a21ba54e42985370493126e238a791457150ca1b8a298a29bc8192495314929b88650dc2c92e2a61a434b861b8f22492e3a454914c514dc4986f224c370cf2228ae3c8e91539175705148710e2a970620c5521c4b98e25cd452e620524a8310552e0c4150731055d262a061b8735148924c924dc4986ea2931271d4521261b8675149b881882a90620aa4c40952082a9317574cc8a04c286438ea28c9b829c8114272eb21cb2075914640dc1bac872c89871d6451061b861bac872c89b812c87082b2628e530a62eb2e2844b87951ca260dc3ca8e3a8839072a181392493570c370f2a26e28b2488e1c821ca924a898371e411e54925443041370c09ba8604dc3026eb20dc751c75913791423945131c7524a2189371c44b854dc9082a38f24a925131c792541b83791d2a64947492a62f2a0e49507224d5c1b879510c09b820982484de49032648593751c30de470cf2a26186e186f2182e1ce5471d472c8820b8a105cc104c30ba86188209b82704e6b238e63c8e106544e404e41cb83925d43c9275103208e193240c9b92064c924dd41c86a0e435713043704ea186e3ac8e3c8e95104130d4104c35704130dc30dd64338ea39644e5c30dc711c2a49264926e395472898e3c92a186e19e474a98e524a632186e388e1524930dc751ca263a4950ce3c92a64949298cbab8a924471d4591522e186a288a190e61cd4591522e6284128b2e494510ca9245cd471d4591522186e3a8e591ca91314e10ce3a8a261865c92843484c30a5d5c702e690e6950ce9255e6640619702eb20c2185c338565c098a284dc4984908a2c84de430cae1865791c7915147254c548a9390c391147298a39c869170c32c862cb9271570c49b8e20dc2a19c23ab8253ccc8888651250e91254c448aa64094186320abc8195125704a1ccae6482971220a5cc71cd64124260649244dc30dd4124917041924a48b98e15cd64430e470e441550e91d261a8a414acc81b864a186171d43086171d6490892150c25484b322248186e3252497124a8925730d5322387302620c3195026502651790e5951ca186e5324a3a4a723861b9923a4e4924d5c9244a38e253249115248986b208e13242484e430e55c418829704ea990ce49c4754ac8315e4a18411c860cb92751d324ac8a4a4b2222eaa031c0d64dd464701370e0d4640d6402eb2261c50c357590405429835179510e0c4288513759041b86188a2983517591375904702284e40aea28c80dd451937503046f2a3222249306a91220ea38975314ab828a62a90c0dd22a9735102e0830c55cc2b81711221834a8b9c9218150326ea1860dc64114c304289ac8150448a9820aa2a14470c75153975706e192164dc30c1abc8a81ca9211248a9b8530aa28aa72286082ab215470470aac9b853140a9b860826a382605411d4d5e455c40c92032ae2920655cd4104c90b2e48957306e15c2b9c8a892065c9032e605410a2b2087150e21d470a322b2e05411491590471c5438c41b8e28a322b2e6a183706e7225c4b988a02ab2382a15c398638aacb8a02ab21e410431c5655cc50ab205410470aacb8a2b8150430abc98a8b98930620851374a922a5c38a4c154418aa262490d5441882ba454dd2ae0c5208517040ab9a540dc1b98a410e915069103748ab8910e915069103748ab9a55cc30e43041370ae25cc30a6e2a08e130ae15cc704c56540b8e190450b8e38c9861cdc4a9225d5d4312aa0b264860caab9897045145d4102aa244902eaae6205c4a8a9750c950260a55cc1b9224dd40b920832ea632ae0dc104e4712ea28ae6281570157311c4ba8a255cc702ea382a632a0861706e3898171c41b8e27224c9255490326244306555c49824aa860c821832aae6081550324922ae182a08628ab98860a5409829570c49b8290d2ea6082e4820cba8372417531957319512065d4702f2608628a6e18a9211c1ba861ac8a1c8ac8371c43145370c350c104d5e4298a29b8a8e1c860dd40a820a9b8e25d4702ea72a48e398a29ca8cb8618e39c862a38e6188571cc502ae281573912e25cc55c91473145395061ca8924982082ae2815731c0ba8e289ca9238c795179351c930357241a55e41b924bc98e3c9262a22202245d425c4c0a41873514a82098702ea381753154b88307514c55208261c0ba8e3a98aa5c4d5238e608628872a18750ea6a0d441a8a32e0d45924431c5351e4548b9a84b8547310c50dd23a4d43191199145019465c0e398bc981465c2865793519063ac83964102ea32147390170c2b226145304a082a6f23861b8371061bc837159114918104e5c304137590c3292524a6e186e0dd4644dc282519061b86b22860dc4359170e504a3202e3986b20411bc86a2e6b2284284509c831d4519061a86326e147095e428a1793506e1a8c888492a2144945c92924ab98ba425c9310748924b989724973517498650e25cc41cc55d20c3510971097130e398aba4d444b92065cc065c9032e6a4839712e25cd49072e183975110408c8710c524465c10c488c8a1d441a925072232e6085190a218731930a228a298c83a88710c31593750b204b2608930c2b20dc2b823acc9b8190b2638a19141a8a326e226450332628a0cc8591ca24c64dc4c83930450c8e0964dc545c0b828b9a40b82245cd2a0ca20263a545c18ea21260dd2a2e691220a9117091106548b9a55c14dc70657350c3514a294dc44b8ea25c4ba985712e62926a32492a092a61cc1065490c411e54dc928931d2ae24ca492a2a45cd40a8611c915704150470ab98a11426284509ba88951d263a434a83549b8a9152e2a412a5cd44a824ab8952424ab98a49824a8a937519719242465c90448cb992083197241165cd4165c3c889712e2a0af225d43c89751310a2289119075103512493032a32e14450a23228371147324a15cc65cc288a38b8228e2e628ae0d47186ae229257147186ae272a1864ac87504a286519971450c8751c648cb9850c820d451970b2082397311418c8591c20acb8591450cb88a2c8a386b2e48a0cb89a8b82145c10a2e690408b82245cd2a15c2b98571cc4195c7112e389a924b897312e39a89724c91cd464404c74a88188ea9170a910239a45cd212220d24a8b828883486a2e69504751d2188371e55c31d409863cab98932925245c10c9173514208e157142285d450c2e0c2ea622a410d52e2a454b98a9152e2a454b9a895254125454ab8a055c7531917930e21837191c28ca813041371c2b98a2b8a14dcc6430dc0b8e539570c924dc3126e20e43c8a8590b26282591412c9b92498990326e21861ac8e498ea2ae205c2b9a428a54288928b820a8298b9a41cc3514ab8e3987311c730e632186218632a48372b9224dcc095c095cc4124ae0925731c73190ae398e3988e398632ae3238c31c73190f249a820b8571492b8c820c8228a32e648917249735712e38897244c1c862a38e628a57145739242cb924b988591cc30e455c42b857348518a5428ae28ae6291ca39a55c708e131c730c64104c30ca822b8a2b98171cc40b8e638c64514c310c32ae326a492a2859730c72c8861b81304137924932493751c1bc8e3ca8b8a15e49298391240cb924b9924b8973524a398b98371c7351c7306eb2186a19644105c1242e6082608dd4105c105cc0b8e6b238e638d430d645c71cc71a8230d645164412825704a095cc0b8e638d6451865917390c248543072e388370ab8e3c92a494430dc790d2a4945e4328471cc35145c928a21a495145e4d450ca172454b8e3215c4bc922638c238472a222071cc40dc5521d2492e648c91ba8a5c41c730d45224971cc71cd452e260620a871882ae91020a831055d226a186a288a191c730d43288650cb8a348e30d45971d22609523852e3a426a38c20a888838d21a844666409441c739128209810564129b8ea15c2511903748748a8972a4c419454328e3995c12864895c431c7370430b8820ba982928692b820c8a1065c7512434b829052e238e2a7205c791d213246a1888e304721a854424e2244c11a8611054409466655431c3980e722a030a6f22ae070ae632a18638a2b8a2b9c8ab9ac88925c90915730371d215d26a29061b89152e215222a5cd452e1c4b988515d228ae9315124b924b9880aa40aa5c0aa454b98aba4d4532060826eb20811302201195371c39860c35910a618628e6b22eb2041390e2283530c50a66ae181350c08272ae32a21d471cc30751143a89c8506a322831d644dd643854708e1306a28835144c0a6b20d440d641a89bac8983026f20dc514c30ea183753911453029ca831d64c5e5408260826f20c37912a0c759112a0c7591312a0c75911419644de54c04e418632e1c71905350c14e54c0a8153105350614d64c0a815317951c30c430c5e430dc185359061cd64c185359060ac9b81506a6054537195317590624e5405d44922b220e2a1c93590e38a849862b22e072a0c175106950171e546438e6a1d23a4d6418430ba8924c748ac8b9891122e0649245cc90b2212f204c398238e6ab22a044906a32181391c09a8628e59191571320875911c4b88625d4714328c8ca8990431c735910e62817391449b8e298e38e46455cd406ea489573148498890e6951506910215cd22a60434a881b8734a8a890d2a20e228ae6915374ac9248921e44c92442c83ca89b848c8730e72a08e38e6b2085731c730c299e46544312f21cc50ae72a04c1b813246eb20d429b8e298670e7232a2618f21cc39ca8e3861bac82054c338e398ca8861a897142b9ac81324e38723208c29b8208d43245e544dd44883130e20c4dd22434a88925c09a545448e3a4d44144114dd22a69121a5441c74a88a839a44086e91534bacb861b839a82054de490f261e41e54dc4702f2384188371c565411c7191c2c89214dc70d4655c72470ac8190e60dc338aca8e10471c5647072238ea48ae615c9298cab9835043a8a2b21c315017506e18acb8238540b8611c71559041b862a38e228e638c565cc54192ea0848ab9897020ba9c8131249ab8e15ce4405cc489248aa8204dc32444b8691557244b986488131c32aa4847245470817324970d22aae604c28a54498314ab809a8314a82904134ab9c8970b21d4540b863c87515309751c790ea2a1a471249712a2a6e08e48a923a491570430832a49221a49157391590579147930f238a79370f21e4c3c8793711c215c3191c1c88a30a6e38e531951c31041b8e2b228471c4c1c9229b8571ca632a638e15041724370c564708e38c8370c490dc718ca988e10ae18c821c4c2c85371c531951220dc338c92702a6164371471c8ca9863864708730c654708e191c9114370c654c5d425d42454c704e44b81731c739724930a7238e61cb89225c4925c4b86915512e25443492e492e1a4554c7244925c4b8e915512e1a443486e25c748aa9b8290269505238a695312614d2a0a439a54de4905c4b89315247124571454c905c2b922a48e225c51537247245414820ca9920a549052a6f22b2e2083208319704190a2062b2e603220dc1b8a921861ba89214dc30dc70ae3191591c0988371429b8a8970e625c139a88750ae618ae38c1b8c8acb8e1883706e2a18638e6a2489571c6186f22b238ea04c50a6ea225c118638c89270ae6492751c1931597350531062e0c428c5cd20a6910a70ae6915121cd2a20e208ae691574829a441442b9a4541cd220a239a455d26b226410e35911320433ca8b8111238c5640e5438e3951730c11a864b8e3a922b9ac8e09861a8229ba921b8638e442b92530ce38e722b223867506e19429bac87304a14dd4938e19e44125449bac8b8638d4398e50ae6a20dc928573504618e319241502e6a3218a3512e48e6b204c10dd471cc728e6b22e6a0d221c62e1462062ae690971d2620a7104e69150e39a44186e9157484b827310239a45404d220d24b8aba4d65c0c8a3cb839147973032065c0c8197310ae08e1591c31041312e38c56547082186175924e05cc2c922b985724a632ae082351c7106e28ac820dc3151c71147314565c43c823856411cc31c430c2b32a08370ce32082648e628e39195704551c21e4915904151c228c2b2e26a026a032ae192e204c49b861b89820b85710c371c4e410272082604c70caa81302b23841304131c32aae1832082604c30caa8131c3238473026186555cc91c44b8951524710c571455c0b8570a92388370ab9882498134a82904534ab82498534a82902695730430654909248ab8248541242ae632b238e191c33c98e29e438f2a6e0643cb87925cc47244098618bc8a102a638b249cc51c7232a24430dc338c8e104c71cc50e4654c308648a8e388a39862b218e190430ca988e18813246f229c3a9921b8a1c8ca8625c91904131c209ca9863864708e19513218239531751248a89770261b98970d223841324970d22aa04c390d21b83706555c4b8e2384730e648aa8e488391455cd410cc924dc148e09a5434869530d21a549054dd6491dc105cc91c4325c5151c23855c708e15049573514e398248549255c105457359197135014a81cd440544ab815152e62a9502950620b8548a9324937154ab814a87104c25454b8a4b98aa5474872461ba8a55cc533238608618357506a32183146f2a06b226a18e38a298a29bca819e54470a3146f2a0d44d5e4104c499249b8a2981502a6e092150490ab82485410c2ae72a0c2a2540ab89502ae6a2492e05cc502ae08e15142f2281591450cb9a8e38f21e4d44d471cc924c924dc0a81530430a895144e4506a191450c9ba861b81524c924dd44105c5143228a19750450e42a255cc724e39a89ab890a861b81bac8228541242a608a150490a9b89502a62545144de5430e4515c3a98e39ca8a890a8e3c8e9304150415702a055cc508a1704173951c71e473515312150c390d2e08a150490a9820a820a9b81514262826f2a3a45186e19e5454308e39820a8ae29cd4304e39ac923a46a2a6f208628ae28ae6a1d641aa45438a30dd4711c32ae0c538e6a1c869150355485cc119d33320a30dd4719071a8e2cca83a8a9957124ba881a872a1a5c71324e30a6644440c35190e3ac81cc39ac8870c370c3759170638e638e6a3228a38e638e6b22e60732c881ce4a2e03712c8657359103a449122e6492e48917351484892e24448b9924b89125cd452e241a45c90d2e622448b92245cc5520d22522e4a49731034892e244973154b98492e2492e638e6a2912498924c5c30dd452e24971124b89871cc552245714e621c62a973514c8a186a08261abc8570638c6448838c9b8209891051937590a2bc851ce451a82bc92a0af23a9b829c86a382614539571911457071904c1c641c64dc48891305190a26eb228ae1c13903239b861472ea18c08272e18a37519131c38871c64c388e1e44de470a20a3261441464de54515c30ea15ce405643c9b8714e428a72ea08a61453970a29c8a3751911c70f22047193043c88713791c38a32044c04641379514570f22a8a511ca2944c728a51145137913714082720891370c3759030c8618bc8105e54470417020bc98e39ac830830cbc871ca898104e408272e0c37950618c8617020bca88114c51bc833ca811c86e3a89bac8a14e42b9250723222861cd64702ea386a19471d64645c51c1ba88624d431d472861a8c8c821a8e51457390ca28a6e1e470a825122e722e628ee14c90d5e43245391c731c929cb98570475304570c12b9b8e4887351c3106eae18f21cd44b8273047357391502055d22065488b828825748818ae911734812a440a448a8b8348e95107348239a8b9a564104c912a625c95191c3504751ca394664c7026a1649298a396464105c1ba8710cea38a60dca3326e2849254919032492a39464c524471d4728c9251443285371ca326e216492839191c752471032b261942cb8e388638ac8250b2e0dc710473593703248435904a29232615c92923215c9292326e2a281730e63a45454923a98791c6a2e28410d5c18867590c79247350ae19645cc7486950435498e9052a08ea93791c950e65124a1cca2e0941b96490d41b945cc2ba411d52e08ea90ae973950c911c2a48ea4945c324490a921a9251730a6394490d491324351ca214c26ea484152451704a285d4116454a92488a157391910c50ae7209429b83125451226f22186a38e608e6b2186e486ea0c491b869026eb22629c906af228ae486f262441ab83125410d5e40c82570261a5430d5e4c5c328910d64328a49c98219643286593704750c7530ca194dc0982e486ea04c91b921ba9860b89751c911d4de4541d22202619d52261457488348a97137483483750d20dd4c348ea19c753714ac8e1026a3927314514e464105c3ca8971c6a286e32619c18a8e29cc71cc6410542cb824a820abc9b8e488a1b8a3191ca188671d4728c98e18922b8a32382a49c9193711c20a8e11d4c11d4129b8e3889751c7112ea6384750ce3a9bc8750c9191452464c5143191459371515248ea61e471a88e102ea0d4728c98e1c8e4a8827064dc705521452605d23a4de492925104a24dcc1292e18ea6e2a45498a924de5491d49288a2c925131d228921370a62882531ca09ba820c82931423514930d5e4645c71429b89250ae61e415140cb98c8e3a861b921ba88e398239a87904e63844b9a8cb8a3043a988a298911cc5c90ea61e415247531122494c4b8e151c75317931ca0647511ca282e2e48e511ca3945cc90d470d5c728e57312e498239a89704e608e6ae392604d4306435731951c1ba823a8628c664105c10dd44b8e3524a398cb8a104c514c1c8c8e104c71445144e5cc524451cc3191ca1892298e51970c29864098648cb988171d4115dc2c827731c310e6a38621cd5c7086a38c357391452464114319704190419731510608dd2202619d522e0c51ba44482a492a62e69069026a1a409ab8690d47186ae6295142086ae0c433ac869126a1d432c8b8638860ac923245cc3254511459145c49922185cc412825924a05cdc92826386ae628450b8a105cc5410d521452e0a414b9857492570ca4b9a924892171527514171d4c646430d434823591c9124ea25c1398e11cd644328e1ac863a8e4882b22a28ae2445790722b864a861abc88a3964328912c8ab8a2981914c4388a6382a38ea632286511ca064a32a28c51c8a712239c88a2c8a0c8ab98905263a54419437171251cc439473173487186a20d23a8b87186a2145cd2b2082e1e541242e1862b2394731ca39c98250dc1286f209c3286f26e3945124a48c861864c708e19041937104a19c359147086b26094338eb2164dc51432064c5064937152435145910ce0cb8e32443730521a4c748de49186a2b8a732461bca8a908e170c27304e39a8a515c539c8c8b98590b2e28ee282a095e4428864946451cb2194489645cc92449245c10649245cd4082a1a41570d21a8690d5cc5214e2082e695914590ca096445164328259130b2064a21649289b82504a64926ea149504a6214413748230dd2b2e28a628a6e492a3849531c23a8e11d4de450645164c51645164dc4314724926e3861bc8a8a39825724a095cc9292e492e7209413041371c739114e3986591ca1c8ac8a29823a82539145924dc92549298a49b89230dc338a82514c514dc9186f248c370cf2219c791d22b2e228a2394928c8a288e524a32e144489642882597324a495c105cd4515c505492bc85925cc2c859724973124e398e3151121a925710a20b9a4138e69524a2b8a2b98271cc4138e638c64718621865464928a2c89248b820c82573041724e6a1441704e6924e39ac85924c91b9230dc41186ea29c730e47489215917350925c925cc9186ea2910919432b8a45c24e514e62906728a5c4c0c41548812a45c095220952e6a9990e3ac830dc30dd6438eb220861b8e351464c50c37061bcac872c88338eb2289b8728a32284c9284137590490c824864c1243228619370b2164c11642c84dd470c3790c37512451242e48430b982098237504130413704e39ac8e098e351c359190720e42e492e6492e484d49186a249c731c6a09ca394e451872326187228b264840c9b92124c924dd490dc33a881925c9398271cd43289820986e186ea08ca28de4329c72c88e30d471964913970c39249370cea394430dc79254928c8e3986a288692864c9186e12547494321a4a13751c730d45915223942970ca909217324271a8659990230dc7590ca2a6474b924b992718927185472a6644441c73912892a47495c349497314869591c1282510c2531c2504de4750e249cc71a64338e249232219c710c11972491242ea38c391c991052a1a4912b98271cc354c8232a56429e4a48c371d5259088aab99203a981d44dd644986e0ea910e14931093175149894881a86e293754c88082f2a0c417070ea32a38e186e143a9c8514e5c654c7043a875195020bc8e10c39a8a298830d64298bca98809e5470209c818cba98082f2a09c706a188a1795317592438f2a60643a893ac9886704244d430913575249705130a6e959040c989371224860c8a920e44498351c71915312248191524910f238519153750621ba4154418515134851015134bac987924e2289530c49ab8a492a62859371507224dc1c83971241064c11c321cc1b8a326a2820ac8191c238654c490c1952470654c9254904195317530c91242e14c370a62bc8a054c1ab83515e4543986208aa38471454c705471c2a62a18a154d4314535170c3105c4a922a98537144a98537159391524932438f2a6238604d41aba922a497591261b822454489224c54c0a821c54dd433a410a269026975931c7106a0d445145d433927112a48e9530c924d44512a60d45d4c1a54971c93a88214c315061570431454179391570931021452a09c1882ea931507482935174cc8e070ac818af2a1d44d43843a84d5e40981391c2183950b2e29c54306a186b2a19249ab8e0e4975131c315c53ca874a886925c514c370c37951c338f2a272a1893a8e2126a1b8751350c9384549c7135970c50a43a8526a1ba6640c20bac8228662927248a834a85c34cc8888a91ca2438eb2621cd414e261abc871d4521261b8930dd45261d220ca2b8a4dc395220ce3a8a4c2a44949baa6440c64096414e5c082720272e027204dd4c19437906515e44294529c830d65c50a61b8675913190453830d6432b98a714e219431142e632e19c72830de47531c23a860b8ea6228e531ca394c5e54925432b82c983950e60e55c418a409a5418a434abc8791c79107590ae38eb226492638e638e722e48793126e14c70457390c51cb8a8110a4b89a410e26970e2144d20c52eb2648a0c98937240c989371244a985372413026e2a14c390d2e1a434ba861a865914597190ea3923238ea39471930470c8e3864c450649126a61645064c5c925c50af2618a39cb8a0c8a0c99229b8a8a124313027248e61ca820986a1965c114261c86970a61c86ea326218e4a88917126187220926a19221ab9825482970269052a195ce4498622922a18415714939924988390c54328651732420a92570ca2c9251152e722e244970cea2449244c104dc0986ea60a4171d2a0c41748e95390724b8ea28ae3a8861964970c3525c4309d4c9392711c2a1a431052e09d4e44728e590ce524b2609ca09ca608ce1ac8ba82885389a441a4a2a0d220aba66470a790871d645131c2384de4194510de5490dc33a8a7124930dc924c3750c75130ca2b8a790ca2c8a9731ca3a4c645384329c2619c31971ca09ca6188e39945190d21750c2929d3320ce3ac861c849724ea9911114728653a4b2219ca48e930d4374964339430e4a2ba4b2239493a4b2111550d2380530de455438186e32aa6033a8833a9abc92254c186e2442a44c488913751489152a224925544c12aa20a2a6e9352449229a881a8ba540ce2145310dd5526e9910104d640c319570220e38ca980986f218a1d445063ac89c85144524a272ea0c32185c105c3a831d64c3a875310aa1d4c514c5e5440c642832c8c810564d40820aac816654dc18632185c0c75914e428a72e38a298a3791513504130c14453950628a6b2e04f214721b830de45442a855306ae1830c65430b89abc813a8325d6438e2a041759104190418c980ca820c9b8930c48c88e1ce411cc31c5319151c790e639232238a1bc8a1b8250de454c49860c88792471e4c543c861c88e3c8e3c8a9ba821c4c104dd20c970a9151124b8e9513483122a20475134bac8790f264926e1839ac861cb882386471cc938391950470c64538e649c1c8ca982186411c32a083208e1953104190a639232a187204c09ca9920832a4820ca98ba8e398e10e618a86724e38c54d41a8e385411c2a6a218e38547054d4314535170c91549154d431453570ce2a44a98a37519915061ba8325d6410638ac82022b26083208326e38f21cc18c88a724379243704a1bc8a8751c7590c93a86286eb22628e590c750c759114590ca18eb226ea0c4289a4104d2e0c97249751123a89811d44289ba56541841750f2164c924c4924c918b8609e4704c938272a18321872a606411c32a492a6218321872a486a6492a298baa81492ea18670cea182a6a1542a988628a6a28c5c25542a985514c451862f2b2261c795240c99249b8a2987514c4514c1a8a632082618a319750d2144289a5428d52f2a1c2a24c310c2e48e3ca923a54c4a8953112a298a317551c28a6a0d441a8a321852eb22381924c5144514641064d4303249aba9218209aa451a5d64104132475144509a8628d5d470430a8322bac89b8903515c52a0a714a9880a4541374cc8e1c28c37950ea2a033ac854c1d42a1c2a6f20893145914593524914d5c48d49715042a8553246e19c54c10c504c37506a2bc8a71e45428ce29e54913903515c7150a750987485413970e1548ce9990ce3a46105d322220a791050c370ceb22061bc867513905388e72e1ca29c86ea212499249b924992375148924c91b924986ea293061a8ae2906515c526e0c371d45219ca930d249ba8a640827212248e2720413970911227204139750a39c86a0a29c86b220c3591462e20e209c82370209c86ea0c319046a1843571390c1186a195c3082a0b886515c3389cb860461bc8ea0cf23a886728e51390e128272ea3927904e194579114790ca09e4545386790c570ca2bc8821c86504f22a638f21e4c71cc515c939c89216449244d5c09497106525c4d21c4389a5c39453148518a5d64928ae09c18ac921b8250de4c71c3238326228a618ae39c8a2c9262a38a791c793141924c43147228c55c32445398e104c4514c31504618861590461886150c2597910453c8a72457910f239279130b21e4a249226a49220832609493570a710e261446a0945374c8e29e43c98791a8792926e08324992352465711c61882350c2590c25165e44c104c31c6320926a48c3570c390d491944928a2e20c43548a9704a2c92e3248c350cae184a710d2724e326e4922492264926e08cea08c3749275924930dc919c413a861492e3ac88230dc309c470a869394939464c338e20a8a19142937502748871498235046574cc819c759144709c811cb811c9d4924c37246751ca219522b92321945714f24898a70a41371c292826750ca74cc8e524272a644443285189d2590ce524653a4b2394329d259108aa9860e4e243a44d4974c88208a19cc3a813a98ac81862b2e0c419d471220ba9813a8e18417531507512a7351270ce6a320c315065c13a664026b270219a87274c839111122194e48e93254574c88714e43515c1386730e721a5492ba6438a61ac8ae094e09cc71c8a9515d322194e1a4a74c844428455490514d64e14e950aa930dd3220353a853a9c86e0c324545750a33a98138e6b21a5d3201538e6b21b818545750a75324e390dd32219c11a4e990888910ca71d2329d3221c72538a7492653a64329c148ca74c8921112a9bbb8551c30c05c1350c222f215c088186b2205c13047350ca11179050ca11795571c045caa121a4349a8b84926ea1e493041a8324545c106a0d45cc906a972490c310c319571124926ae29248d5c4e55c303712179509753712e2222441a454a8e9254c5c304724926a0861a92514c5c50d21a55c0c8610d451465c64107228c5c50923246a2a4931793065706571143492ae2923255c64285c4b8e5193570ca05c485e4726543c92a6e246e222246e5240b82590b26e4892a2aae14aa0c718902a971057489ab83a546e111061a890a2971057130a9104d5c484ae29844408c251557018445c0611172accc8308806ae0359735102e39820d41854641850a2f202f26b21c615c711c71359170218c83a8e720c708d645cd4081a865d4730c44644926069150c38e691574848c543124b889135749a8820c31571220d408d45e47192032ea380cba9a820982cb857312e498a892245c0b98190472465410e3205c3a861c8cab8190448ca820c8310c2c8cab9a8791cc3c9262285590ea3862cacb859142acb8859144acb8590b2e26a2e0c52281571c0ba9a54388173482245c1a441cd22ea90448a822455d26ae38320a4c2b8e615c531144ab87530ea298ca8371e4915434862cab864a861a55e547142aba8e28aeb2638f249815045570ae6281570ae72a2e32a082e0830c55e431c4ba875350451c4135102e399206540c8205e55c4a920e55cd471862485970f2225c26a2e1a43aa4549a8e348150415748a055d26ae1c2a098608d6490ae3ca874a99238b2a498b8ca98e05e410c930c5431c70c8973512351724718b218a9230ea3c8e93512a31795061146175061242eb261c79508c44412e20c28c55208261c73154b8a870469046975131c54841aa42ea3984441c223332282bc82221940830d45e41ba828e5c7531061ac830c644302e398171cd6438c350c3519170608c8728a721c722e60ca28c87186b21c659170a19042e6a0430bc8ea394c31119092882b898925c425c4c25c44b9aba4428c38ea2394dd2260ca1c7310d5d228657498a820a8e5305170e2a0dc38a9c8790f2225c7150f2488e15310621863206a214c30d465c105c30dc30dc64c1062e05cc2b8648a6e238a7139513228a09cb920e5c490c39712e260e45165c925c471e47135170448b8173482055c2b9a542b8e2384c708e1351c751ca228a27220d220ca9174891040baba4c104c14c5c286e269515208f2e25c410dc71524971d47289922a5c711c2615c711cd645e470c159032605c71c64905d47064753724a28921312e3892151ca6e205d22a547492a62823748714a8e549b8292541298e514412c8a137193032098e350320832e492e625c73572424986151c7924c7188615710e20986a90e5104d23a46ae08c11c86951c23c9213246ae321943288e328251724652465724e31d464d4518471d4530c5c718b228c51cb864b8c8250cae384b2a05c70c92a64946222051885104dd221c6913061b95220a4d47484a308881199914328e5184a3238ca086171d473044a21c7128a6128c81184a2999551c0c17591c44300ae398caa83071ce4555c0e3590e357531040c55c3a8e39828c851465c0c828cb9ac87504130b20eb2e14579314571cc564408a4945640820aacb8055641655cc381ac8aeb21d4c3053c8e72a22ea0810457590759307518a31915071c8515e473550e314545cc0e3950a83a855c139862232240d22ae12e3988548a9710a9152e26a91221522249517512492aa205115734ba924b8e2457150e28aea2690aa155c3a9a5d4c448d43826a20d2a24935192491243c8b848a9248b98171c0c8c860dc490dc70c5791950c3106e18323218a3988a399251cc655c0b8e48c8310430c5e54188e38c86188618cab9a920e5c925cc9032e49cc410d4704c71432b20837504130c9159702a0861590320823957106a38195906a486b2e28b228b2e26a20c418b820b9a41a4408d22a0d2204691574891069150e212e2ae9350c370d20dc7951c608c33caba8750c34a921a55d6470c34a864aba8e28aeb263822a822aba8e28aea638c50815714e6b2232a1c7350e09a8921c39512426545c92449245cc30c41b8791914608e6208e64947319506a186a2382351c51cd465c50ca2386a386a3228a239470d465cd43c85972497124971c4c3046a38260826b2186a086b2e0d490d645165cc0c9235241572420b98a8a874926a0c428ba4105d2624620464b8a8910e2ae91221c5411d5d26aa24209a8e38c71a8e4aba8550aaf238a2ba8a79301550aae15457914e3c98a8cb830c541122e082e628ae0d457914570ea2bc8924b8e29e44d4708a2c8a2cb920b8a853a8a262a0d2a05d23a4c1062a082ae902a2ba4d5430a2ba87590ea2c88e909a8c86244171459145912491751c4882ea6a08e492ea1d445384d4492497043548a9751c53a9a8648e9524453519730470b24ba893a981518a84a8ae29cc31570431c2350ea29c8e3150a718a390c55e448490ca8297324e118888483a8a62950518aa5c4052a4b89834a84e30888119990518c828e398e3519071cc471acb8828e4371306515c47359061bc8ea0dc1122e082e6082e09cd6471451145171ca389c88e51220b827304171cd6438647304e35170e3a8a7204b2310e514e4518b9871cc3590e39288e32865171c20b9ac828c32185c7591cc222120a5c4492e2624971124b89aa4492e249cc492e239aa5c449c751ca691ca29a5c4c24e39886a91c654b883494971350c1189231ca298c8a188e524632a28c7188e298e514c6491c47292319570c31062e186e28a608dc6410a320832ea60dc92827228e639413970c19242e218721872e492e26386515e4925c4714f2389a889192a224a398ba438a61b8a5428c418ba429c52a6383228dc3492f228ae3ca9271e474a89271e474a8e92898c9228c45182298c8310c118cb8510625904197504192491724a0ba98628e41cb8593a92515cc925c751ca62214620c5c189d4189417348671e493a8e9288e928a2632e492e3867912417504e3a98711d520952721e4751ca2284c928a209c88271d47298e928e4708c11c8b9820c820cb820b99271a9271cc7188235104171cd248d47484130d464938e63a4721a54708ca08cb22e38c392545488a90b9a8e3a8a6188a918647187248b82549d49394c51110114d221462970497304a4b8d4728c22204666472853c8c2511c6504e5184a21ca30946532aae18e031c73591507557035539c8891271cc425445714e6a95033aaa5c4487514d2a2a5c4d320472081186f202b2298a37514e39875188a838d5438d44e43041a8ae19c54509cb871a92488a2c8a186b22a06410a32ae24490b22a082ae6a1d2a0820aa8553485514d2eb20c2a4924aa85570aa2b885515c5389a871a8551649724e629d2398ac88a492a298aea14230dd442a4ea49c65c5041515c5350a938e6b214235047220d5248b981119d3320c3271871a849938d32111071c89c731c6a1230d4432ba443a45c1a44e649c6a990138eb2394c3391c6e19d492449704e609c6a08c574c8a74b8a349cc32a4e354c8728e4e31d4938a628c4538e49724ea49ca699114609ca34c8444aa19c919d3219c548ce991c33a6442228e112abbb89900845e4184424931524285c1b9232a064c911700a8dc22046665c0628c22f2e0c51844518e128a6110571c41514c232ee02204a308bb833320a974caa8e1c460418632ea09822322451c6e951074a898790e350c0c926ae246a18e924d5e540d40a8dd408c71bac8871e5491315230888388c221c66640464728c10c2e0a8a6119062b88ea299231c6e0dc470a82530444494648dc3388a1514c23204a308a6642a655438828aea230a30a8550b8e611903a8d428d5c4730e3832a29a8538d5c48c37511c261103a545350a357046711cc232046114cc838c8e518613946119067128c51841728c22242728c2320a664aae38c138c2238c509c6110e308ca6450d32553bb99981212b9c894509939844e57008ba64a1321139cae264a3b98ccaaa077074a9dc7334aa8045cc02917301135507026551148a9770148b8088a4ee01114b808ba540444a93ba808b808b9552044089540882ae93b9808b808b9552044a749dc66692aa6640c19c25579901981854661bb85541326e074864dc265d541caae0e6141372ab860d2e55990a991142660690c9860f21524c34cc922330094c9990984c985428e492849098699928466a0e993072a64caa28849d429914709532550699254c2337099309932a844c9461199ddc255266422201954c440672ac9e406333aa81326113247064221c226331211281119466a72a9d32113bb80aa979701caaf32071954462073b8d5401174cb82192299069973b814c944c9ca77519546114c9dc66613202261819564206772aa4322330025531301954c41dd47075905759053b8e43b8a3952ea29c99dcaa1119ccc8553a520339b80cae6a072a89860c2b83ab8773390895463b9bccc80772a989815414ee55013b954cc4403353ba80cddc3b8a28a38ea38eb226ea18e18ee19e45c50c550cb2219c750ce590a61886e29d4308ee29d645d438671e45c50ca2c88a728672cba999dcaa183154ee5508886333038cae6a02260674844aa919cdd32990550e60198464aa30f237379002770554c4c04c1dcaa180519753b9541dd438a28328cba9dcaa662201dc3b99a8e7775050c514d4ddc1c7061505e45cc28a0a137142b2261438ea72228670ceb204179020bca83a8b260ea9310a930a62e1ca930a62285d644dd430c103045d4e441b870e9135073579010e193590730c65c15c791c540d41ab8f2a1c20ca89874a8338f2a61c73517917145051645cc514d6404509bc818415795015165c51143983750cb2e1420cb8985165c19459730a29b8ac88298737905315e5414c591241b861ba8e59130e9114e9370a910e51644c51bac821d471d4c514263238a2986e19c65c1cc310c2b20c2597504170429ba8e3ac82098e39b8a298209ba89724eb2605c70a8b238ea288a19310c3515c790461a8ae2c98a748a7498b8a0b9472c821b9492c982548254988672a4517591750a390239030ba827220c3790e950cc71bc87082721c23970628dc7951c47098674846f22e1942a5c53146b214209c851ca8a186a2cb8a2284c2a5c235910c51c7514441844e41427191b80944727506e19d4118e3714608dd472844451c75088f3228a308a4c5142711e46e28e128a4675975330e0453c8a98e39c73c88a394e094f22a333bb8a0a2832e62145910a2e333b95540ceea0dc0b877198228cc28472864c72847286466ea772a8444065511883ba81b8ea772a8c22333900ee5531300661712ab81c2a2a033110aa0caa154cc2a9c2a8ce6e14662bc8222553b82ab872a9de431998f29903bcc8080441773013b995544c0655304c9dc5550ee03b8a1cc39aba8c86ee1dcaaa0eea0c30e39b8770ee61dc7355191ddcaa6622070c198088398ba8918e37537935071ccd4eeea061544984cb891b982cb891b9aa9cbb80a055cd5e43b80c88648212e602e632a24839279530724f2a622ee6240c5c10953120a98bc898082e620548c9899075902e3c80b98f2b26164702ea384190521852eb26220e29e44c3c81515c348a95152f26164508ae0a490a8a9793117370a28492ae7228929c8898a0a49644c02f23a98548a9730e93590e131d411d23898909ac8898a0a2c988591c7505271d64c138ea04ce591137755900aa831de40c311905144654186105c6404e51957579049ca82120a45d640608cab8026a24e5d40c21cba8c9881d22b2123202f21c719101350624c55c102af206ea3c8e91195100de4544861cdc30de45643811226a0540e32a6f2a1c7950c48922544d412471e454124971c7915370c11226a08261cbcac8e25e470c20e6a18bc8924d43912a1c2a61cb861b8f232a2260e49e4540679150298a5434bc987907591dc0e26a1c833aa5e54724f22863820b9ac830ce32e0820ba824922245d4c1cd5320413505d2f2a61e43082e38419052f2a39279039ac862185c70ea690c430a5e54c45dc124ab8c80564082b22e4809b83790c24dc418cab923a49106e10655c64403519704502244dc0b80cb9ac8a18429862b22e248a187214c3951724950c9244914591371428b2e224957145165c4d40b848b9848b81749acb8951229b87215c2b9872a1a434a8b88c9838eb2248370c29ba8e3ac8c818c8244e5c122720a22859139750c164c4488571c79137062902697912225492544c905272287511c9512e492ea260820a98732eb20641cc32e14320e530c65d4498490c8e28ae61886197149254c391471d4c3970d214d2e2b222283126f23893145379510e3a88b2484a89921c791371261bc922495130e3a88e4a9b8930d2f2a3202208a28c9c862441465c7145790b2255c4e5c3026e0640ca8205e470f22a638ea25c3ca88a38eb2394305c13ac89bca8a2c8510a32248e3ca823a823ac89811147130e6491459112a28b22e28b20d45912434a8351645cc105d2082e93972471e444b8e3c8a8e3c8371e442b8f20dc791531c751c7592434b869152ea2286e19d4538eb218721a5c348297513704154820a8b2628a228a261cbcac8e485930f208ae6f20b2164e431c751c753975061bc8e182379511459244ba9869912a485c70827930d32e0a4952420a54c51a64708ea3847530e5d4348614b8a3046e3ca8c88982c8ae20c95164454bc811c71390238a713950139021bcab87124e492e2624e629c9292e62a1cd20c52b2187310261ba8b2f20e6190530ca8611c2ae24e638a7350ca2286431d4514bc888a0e721c73951030d645c51c9398e29cd442a464186a29790c938a2b88a4b85925c4e4398a2b85915c450b2228a2e72a182704e7238a2986f2ae29c591459152e228b24b83516454b8992515c516497124952495114917351c1348674ac82704e628a61ba8b2f224e29ce429c539ca861a88390d4517249724e629c539a86511432194297911377142495719051565c0812b985397065165d642c8105645492248565c44195c0a61c8b82a45d640c50b26f2e0659750d2244151248b8175314929cb81b86a2cbac80dc32e072ea1453165c31142b222603791d4418ae3c88748ac8e2820a982292513790139065975049244c11226a292531ca49c953170a69062979062504ae29e56414e414e5c3c882bc8e2a2825314729b8f229d2229d2159110e14c514de441cb22a38a494c51ca6e20c37190e51e45643142c89250f24a89c8532411122a39271032a72e04129c8104c359750f24a8e3c92a638f24a8e3c92a623a471e447245493924b88e48a9b820986a2c8654bc820986a08cae29e5642925391251ca72e0c37910e590a924986a91c730d52e19c453a42b222628e50d271d64404c15907197032750c310e6a2c82970527590539082e09d47285272c8881c89c75053149c7590c1382a09c75390279706593a82704e619d4590d2e19d6428e427286149cb2226eeab2061c72ef20908cb84846403579061911061c88245d405d4c246eb21a4311197500472115706e18608c220c232eb26030dc6549049a88924c5c186e32b23824542454e430e1e45411c71539752434b8248e3c8a824869153122492e492e2a092489248ba9b82904c148e6f2b208e190a390e29cb837124530e43a8a61cb8e3195110e110e111e640c371901514e4242b209b8e11114628dc4854130e38a826e3888e38c2332a603910dd40e39a8a5434bc83020ba871c54e5404e39cab863924882ea2545389a871a56408cea9790e30a86170e35484979110ce032350dc7110ce1c23538447993779032cc8286440c351906a122e122e60451465c04b2e6b20c322472151171490d2a05444126e21c8524c471ca9248a2c8b897069713091724272144924492455c4922e242ea615d229ca92914c2ba45350ca222f21640c351902390171ca8a11170a111c61a850b8c095c6a288b8a286508bcc9812886500965c129c83908832c8545c1462e1a84922e0a825370a3708832b854450ca28c251799145246128b8a286128ba64d640e111ce428e5404e239c8eaf203919071ce45c70a29882c8e5317950c10ea386a320eb206b2272047238a2bc8590359711c515e42c895713970c08272e28e3ac8790f2a20cb2392a261e493a861b833ca88e3a9271d44de54064939024b8e72e0b229c871d4539751c649d4444145911526224972497317124a924a98871d438ea262ea25c31e5470d470d644748e3ca8691d2a260d45906a2cb83516490d2ae228ae29e451644ab89b8371e41b8f2238f20dc79151ca39643492a2619c79249750d21a5c3492ea249c7524e513751c90a8a6484971cdc7254531ca3750ce3a888830dc4186e2a28a2284c105c137041504c128dd4328ae1110a2b8861a86571c2233320e438e5c05e47350a48c83c8e32e0417930a28c850cb8e6a1cb23088891dc4730a2b88d490d4511d238b92514450ba8271d4c728c22239471d461106119993071ce441c722a0c35171c628ae164971149105ce4718a494412b8a71c4e5429e461e46a288813c8260646a2845c449c7310e911a86571524b8a2c92e249220b992524a2095c129cd4728c2209c638d42e229c7194271027199914670e190545315c71114e09467088a714e1194c9b8e18a3146e3249d43243c882a094e431c71054129cb8515e47308851c8a371454449497114e63a8691d220a82531c71054129b8a7184433942a219ca28ce1288128ccc8a0944728a7184a3219470944504a329930ce5025924c20b8ea23945184e5114139465322a4dd65d4cc038e2a62793053c88729e429e438b261d2622854f226a1cf238724f2a1c795110f219c33c874a8899e41964e1c7910b271527904e2c8883164431d4e39527904e91130e908926a7951c09c438a6467914e38a1388f2329e54cceee0194e5dc39642451130a145931522260a113772c83b964514591444094409453260b2239472c8a9111470944284a29930a111bb96451522a4ee32c999dcaaa018cd4eea00d4c32ee0482ea6e190130c82032a0479531c7370cb809dc619331448aa606408b2e61413750ca66190e29c661901164c0a4dcc05266750ea1152190e5908e50c98a3c8e937141914cea29ca3330cba86ee5508880eea02a88e4ee5511880eea77501565dc020cba8e470638a830455323a5c72e0117153251c871c8a284430a532728e5d4ee551844666004ee2aa98980ee5501d44ee55141d22772a99888037353ba8051ba9bb8045513503370a110508b98570ae6aa18c2a5c61aa9980445535025571c1c22a61c7111c53822260c232144289a554718708a465530c09c525514dcdc50aa2998a70aa349cde4ee0d2772aa83ba8298e3aba42772a8444155c3954ef20839dcaa308a4666999999900eea60771303b88cb20e711965cd5e42830093753145c49390285ca323573507020b9813995544c020e25ce5c1b844d45404ba8693131002b26b209032e3260ae60e3a9881c644087244e45c085144e4490e3898531ca322ea72ae0a6a18602a2186a72a0473903988138ac871cc75935770720c2462b2e60c08ab8046e2e146ea602492262e0829860ac8ba86041911211370a1465c4b9a9ca80a88110a11330c15cc70ae62228730e621cc315151c70af202f22248791c44c512e388e1511438c9a9a811248a988112e25c5441c2204654cc25c2ba4c70ae628a2b9c888506ae91450b8570c888515c711023266247499238f26248e930c3915103704470a880882a3204a21c64cd5641813026ea20263924b9893126e2a321cc164c90b26212a628153171122a5c1aa41aa5cc51640a8b262545064dc46438e6224c351261ab8930d432b888925c750d24b927530c390d2e49d446554082e21c22649c2c85910b228b88e292e38898a72420a825711c38c9aa8492ea24975111271c44c186a914e971422c8297110a105c408c98309412b88139464749aac9bbc98638351c6e6e154314590b26a638925cc492e6aa0e43cb8224c320921951c3386492855d42a832ac892a8c2e66f21921cc19cbc884441944514186f2537044a20a329815c4ca0c2511cc09ca23729b8a1251714ca6022b89940832510251165c919cca6f21dc790844a32aa00cce62553880e6735509931450e0c880c92e2b26a155c70711d654082e20618a82e3238530262185c448a930d221b8c8e18a2710a1388732ab21caa04e239213892aa04e204e23c9566451c3c9542acc9983aa646e639465551c71c67314e264a339a84aa1138b80ee30a8a811882a83577184448a49654126471d324aa8e3c8e3c955dc90aa2bb9866088c95410a72a8c2717199b8013b82a6a29300693714aaae01ba4d543b8a28105c4082e2a6ea4804d44062a9177014b8828e6229030dc452ee06574881882a29020a8a5dd54314628d54046a20e221c4c09446aa044604e232abba4cd21dca14ee9194d25550ea154e386551a4e692a9ddc24aae0d41dc66146628e519ba852553b84440aae0ae91a4aa771844669399002aabcabc800cc055977025539dc5d55d5c002a9dc5206605285caae00cc5466150104ca233284aa7712533332ab2b2008aa8a0cc014ba81466570a5cab2e0a0779906638638dcc70c71b988a65466150113072061a89a640a779924170540a6460c4e370461b86aa6082e0a86118233b8655314c88cc18ccaa12a8eee2aaa0000cc5466114ccaac852c80704e551799906606330a83199425514a6419838a72abc8006e26a7751985430662820a9dc704608e411823973b86082390dceea623315425591043854749425514a640ef320c19454c0ee6180ce40e3221861dc3b88771c4e44d54ee33033b8cc22a00a32771330a77028e5dc307710ce430c72a77300811597701791c0a8953b981041953020832a677190e08c820a4149dc13a981064c0a4cee0a8ca9dc0104de5dc1811c86ef20e409813950c390621ca82ee083218430ca820c861065417710c30e54518727706a29dc4e4ee028a2e09cbb83b87711ce430c411c8618872770521ba8e39862186414a8823494272775311983041023915cee62332a80c290c9dc6652844aa20cc073ba8cc2950608149dca623328525514ccccaacac85019880c54c1dd41de430661dc12411524118e11ab9c89dd32a3308aa818cc225294a060232c8ab808d4406619894564c1275903b8ef2595703b98180b88618e082e241753917355018a9d4eee03ca8d4ee3330066a953b8cd3201dd42a333ba422a02815113b998144accbb870979511424ef238774ca88a127791c749272a266241c92ef21dc51641a8a991d2ef2a1dc4c835069591c9977912770ea186208d453bb8a90c1548aef32a0a79706a18a350caee19233b9249dc735993303590e14d6418eb2ee1c6628a119a821c2a0998a288e4a8e2299a8e09c66082330dd5dc082ee48a7712771524549220bb8a90ca93b87748a9249dc708d4ce644430662889ceee1c3b8b3233b8ccc02266099770e330771e6470ee3cc8e661d323883ba646622044088cd4ee3306335502624494527707104d293b9208d277531198332aa644b838cdc11412c84660c3925c21198249c2335793b8772aa4225591555009971c0ee25548033b89a83300caa3370b83041054c4771984ee2550aa99997979790e0a112a9ce02218606710a8cee26a0cc00331022aae334cb85c044c1c818a35134c81430665579991c05ccaa031750cc3062e0a94135304082a655030ba8c105c1528d4c5322153207320c353986714c89dc66389dc414ee2aaeee000c66112ac9de640eaea083020988cee6112a8f29900a11199d5d40cc414e6e02acb8dc0e7799061a9820b820b82aa0c118239750411c8230423970d54304608e541182392a9dcc646773089541255770508a4aa73ba53200ee5953bcc80066ea11199d5d40c11b9880209544ce6e0628a0231301198acba8ddc102e550c30c31ca86ee18186ae198c860c33190ddc30dd54c04020ca9b8ac82023224173040832a0b98ca82ee0232281065c0c41975302084197304104112432e6a320a628a232083106417062905d4c10420c8297304108320b9a8c82ee082504a3208208964eeaa0104d5e40620c65d408530c430cba8808c91cba808c397513900d6428645c08dce490220c4c488313970c39413710618ba6540832e05c0b9823104690c65c0941370c430ca8860c4608e5c08dc3950230e5c151390a2882720c3170e4a1852510c272aa18608861390e3844309c82144c09a6418872e041350c430c861065c4118721a5c11a4e272a1861473910a2bc8e2238c11390c104c430c53218621cb86082621a6414ba820a82608c430c8230832a28c24cb88230e41505c11a4e272084619c1128e5543047208c1044e09ca8e118211c955dcc4731ceee6142e0833146550c72a9dc6670b888a14319cae6115501c66953ba81988a0554b8dc306618886e91a4ee6112aa6666664066e0cc0880186e26ae3cc8748642220e39089987199dd5d40c0331938662e62099370a00bc9c81dcaa0809cdc1551064e44773709048498acba8554c9233797038550dcde642a8770c15326771453baa88370c71cdc3550660e9950dc2472a1b9b80d232e0a924de4c91c39a641a641cba88653b891c839712390dd4373712590ca60c37129c329cdd544d32006af2a383304388e66082335590aa046604661b8a75597799041c0b871993502644ceaee28a28214541122b272e2854c8874c8e14e69951c498389b8e9990c082a62cc8a1c1532665d44c1143a64151305ddc02b88919937014c9a8710e992412a642a65c4c08a82eeaa01b8732ea01192399753132183170c4926a214c3a83aa98b824c5411226f32a06990c38e6a4cc8a818abb834c8171cc18838d45c3a464105c793950c1c863a4722a1bb9b82cc830317590c4884a89b8924dc492ae1430565cc54026970a29ba54665c02a29cb8a039710c28b2e2a05c18a9b860871548a9379930c5122699126386734cb8649490d4d3224c71ca699750e39c87145739724915c4105428bb821c5470419530a228e43245dcc1482970623ba4e641d438eb272389310479524a398e1c8e951314129a66429e409e4c7292515c4524a20b98e34ccba8861a64350e609c139873218e34ca8831770c349272186924e5c3146924e430d239750c648c924c434c869391c628e2094c990d272a38c1186e4c869390c608d239571072192391054ee6e018bcb814dc492ae249573170110a26f321830ca2e0cca811b8712e209b811ba6641a654c314334c861a65c28a722441504130d4c34cc86086699710c1a64e2a192390c148e4430c5ca619c6eeaa6012ea72ea48700b9a8f32638e02ea3cc98a8153267504c9a9c5dc4c80564c48092a6ea624285d4c44829530aa332e3874ca80bc85144c11c71370520bcc81ac89254c492a620a6640c64728a710665d4c3c80bc8e488e38b8274cc982704392a6288299904328532e6a22814c81953014c99441777002537164e5c2a654050b9ba641510450c20a93320532e60a82853260b944177550c081862ae0648abccb87023704732e6a14303775035719704312a28326e02a28a32e4857041597350a12426e1822864909ba8b8a041370e42b81730e55c18235165c66406f2e140c82ae2819255cdc08d2f321850926e1cc8828dd3226455414229cb8a072e045975120ab88e509b872a46e1a4664712374c9225535040c31590212ea6a04335106950c6654304603248a826484732a6040b9c871447054e542b87590ae1d644925c4a98570af22638f238f2a38f23a544924c70e54924c951351421862628a2284d430d66640827214209ca8e25d43a88e1c922628e591522486a289a82098235166644319248921305321a4e4519231462924e5430c234c811a6544c08a7249220a924894c3990c51853221854315239094d541039ac8105d418e2a614d3321870a870a987322a486046a924e5414699513020bc8105e4c4a8ae25497114530dc9186e260826999020bc853c992515c929c4929c53898234cca811ce4525c7124e130d33208c5384709a6544718e104d23924608d23950291c944c518234c86251aab8304130e65418234ca8848e542619c1382734c8638d32a18234c9441c94261aa86118232abbb988724772a860946950c32a54e77314a66440ef23901865c461854c862251a80e542230992844a350611182528d5cee91c98e50f20cc273a6419d2795119ddcc02a8cd2f217050e333bcc838172a84cc3042646173500a8b32e283255c599132662644c8ccaa0d325150995034ca8cc3114082a64cc8a08c30a9332330c430aa84ca81a65466102990541a64a330955c3086553bb846699385c440cc40ce53702a5c725703349643703198625496470c253a4b2e23395cc5115501418cd21912a80a3355033102ab860ce406625902186e620aca9dc66112accc8e74a40a7570044665750ea06620c07731061159519844a75799900ee233550331004ee26605066aeae04430608e608e5d44c19821c438cb85104c104e4504e209cc089c139731066082e08c11c8230472e62aa77198054ee330888a55500a1711995d4701a8cc22929d5d3299002711cdcd5402770ccc40041515393b980ab2779060418104de44c50c08e4095c539135757008719751037506e181104e438e320417930ce0541710c3105ce5d44c70c2866320e39c8853883389cb9891140a8c8e04579101515cc08610654c0ab8cb862815106a0d44e430c104c3975061065c10a618861975106e08c395069704695139009ac8ae0430c5642865c428a6054632185cc188721c4389872a186ae18620c8e398621865450832e208c390e230e5411a411a54454862e72e6228628e4718518cb985146412820a8c8a704a7104a70293054e32e0cb20415910651464c30c4390d430c419054411a411054e40c415915c1864a710c25398628a620c82a0b8a308320a9c411a43129ce5cc5543043054c4eef228155dc1831c722ea0c11c8871c722e553b8e4cc1de4202a9dccc0aaee08e08e1865cd411c209c32e28a30c86708a71865cc71aa9dc6619110331061822820964573b9896466112aa806677550331029dccc061abab81dc4c7023306677103313aa8e19cab27719877088838cdc93bc8a5554a64093abcc8198110c08233102237735500677310c666200ab801139051ca272a2a044eee6600cd5e450b20a22182c80ac8b811451973130a0b2e22281c89957140c8195711140e41c8b89245d44cd65d5c00c379153790e24449cc032a6019537175103b8a80c3717530c7020ba9b81ca8604149ac8e1a65dc0430c65d410618c923a4c348ca813a9270c65dc42472a0c11ca8823071512a72041350e92454909c88a31c7238c11c8bb9a89c80a73719039bc8648395072189395241cabb88770c30e5430e432472a186aee2726071c65e40641069195312a1232097311c1d4c791953141c64138938ca9bb810909bc9820628cb82a4dc148c9a820c5191d23a464c10641457391c515e44702a055cc53c81502ae3c8c9a8104f2608a724e209c938c9abb8c808272140a8c8506a326143a8c831c64dde40e5c0a62e04e64105190a0d464dc90157164428b2e0c0826eae06af2272a18e0eb26248e3c88e906a1b8f227238e0540abc88515e470c48a8604d5e44c3aa43062a28a2e29e44515c790c350c91a8820826ae29d32272a04c371220a4c49bc86280ac9883170a9103514986979577029c839170a97035165cc0d5c39190c0564080cbac9b8302a086153971020c3175701579140c5c498e31570154bc9811c2ae2c830c2ae2c98ca82bc8105e4c30ae082e722082e3c81502ae49e4c515c0a82e619d32320448ac81242b2e28390c31591430c430c565cc704151451790351464086b2e6224432454124915714e99041324932462a186a186a2e2a4579312a2b8a711c32186a288a171e4c6542986e24ce214d21b89338c80ac810564c3702a2986e21441398721b8209a4e32aee20209cb818b8320d22720a183151970506a2f261a438c30c55c2bc88628c4193951c28af221c71931d20d4371e4470ce23c9c8515e470c11a8608d5e44338e29c7391306a1b8f208c11a8a29b8a79114538e620c9ca891382730d2704e4289c13983149c139577050cb82606ae915223a42720608d65c142f220350cb98a046e0826ae2c850ba4451a4272a0c1abc82bc88791c4c1a8a371e470a4433a491390230c3159141046b2e1432165c471461bc8e2608261862a086ae29e45082e9114e3484e54309c7324e11c85909c130ce11cabb89c9882893b87753190a1dce450c49c85312721bb861c861c9dd4430c91c8a324721bb861c8677513930229c28af22f204ee14490a93191438eb2228730e6a2c8c8338851977302770a215232287298923952320bb9a8190054e5c02b2e2020ab98b2020ab98b23260832027390105ce54386409e544082e604e6a2c8e11c2a2c8c98229c53882193770409640964412a4148c98204f23a9272882548e548c98149bba8c8e18a28825390259020ac881182b2628e5104a6ef20a29bc808715970488395793115206ae2c9818818bab8b20c348b830c5d492c98c871d6471c7593020ac810565c515c104c104dc104c18bac988e3a8f219c35264c1882e082ea29e430c4104dc104c17514f26321444944c370c514c4390de5dc502591140c3579131412a4492865489c8a394c082f23a833c8ea6228a6904e548672a4c64189c197750a064065d65c51430c430c55e4c30e1055c4843573910648b830c5d412c848dc918b830c5d412c9890921570617054c51c8c89246418632e3861882f2a28930c430c564186320c32ae60430ac810565c18640cb8338654c4924430c5c30c417514f21a4310c3150c31055c53c992105412b86728a7131c723209412986e08ce228a6938632ee121055e40c31055e4c12825310c20aa430a4a61952320641724ea0c320b8ea609ca094c413941394c39046548c8614bba88591c08c11abc8828651793061aba408dc11a8b222865149c833c8ea38209823790230de544329270d44c31d41186e19d4438c8511a4e4289c608e5dc50ca22983128e4524e5114c28a47277514046e08d5e4196442c84c0826e08d45904a91142722823046b204724ab812c8ae23942608c370cea91522484e4708d2ee194729dc7118e548472a27262aa1c32a98238e089e41550c1c54133c811c9c3054105443099e410467955313bb8048b8aa359770e39030c4540395244540c2a2ee39033b8e40d430d4ee2187208c11ca82304720c4608e5432bb834b86951c39046953b888e41de4618690d277089472aa771998280864086554ee6600cc0cc15750cabb83b86419813b920439525dc124ee66a19060663bcb8640c8124326a0490c98238474864d4902935770c30c814e5c20c2e90ca830c8430a4321c3249cc23847348654708321852aee4860ca8610e450a54ee6608c839dc3211420864094c22864ee0a17908614864128a7308614864ee3a4cc3b8e5198471a432a19553b8cc22206620113302770c30c7277300965dc05cb2041904ee650a1064c0a4cee5193b8046597706590625047218450c88613046b204e590ca1c8a1489c132cb9dcc4662844a25550246773550119880553b899802330a334abab805d4430209dd4082ea6260e39898771453b883512a77041502a77114619dc708c4cc408cc5386749472998e09c661a88aa8602313062aa38653abc9dc29d277199804ee66055771c33942a909dc661110188cc2512a818cdc93b96553333332066044304822b224279710148c64e6e6aa050349c9dc41833ba47226621321248203c8b9a8154a6454e4053aa4cf22ee602ac8e77790240319375975700e722e6038cb880e4641ce41b897072065c4112320e470645ce45cd43b837126249710a9152e26f260cc0b810a27218a388a389cb9b9216444c850eb26e05424915390139a820417359717022141a8b9895010655c4246ea48924dd44e40c5490e69591c0982ea19c4886eb2e083712e2a492238e61ce41b873915904170c310c2ea49c30e49750ce1a497519710c4b926a38c0c8e6a249263a4749a8231c7104d4718e104d6464718271cd44a8ae392753902a298608d5c709271c544a9ce45cdce440915cde445149152492aef221dc48a92495771933008a6e72285114728820a99c8130a228e3a8820a99cbb85164c082a624c244d6438ea60e20a9cbb89255c1a5c1a5d640b84b898638659150e398a428a62959093115c0982ea04d224dc149d65dc186ae0d2e48d6405e45312e49a87148e931d249ac8271cc149c9391c638e55dccc3a81701975039255ccc392261c71351c30de470c37911c515e471e4544b92205cc908d4cc38e2609d41c83910c3170c9105d4908c170cea66ee082a08e91d2261d261d262a24e49c4c70abb9218430cb830b830bca8e15cc71ce430dc71ce443986a38a7218ae1c8a8530e4970d24b88a9244eaee04608e5c2b8e2098e104e493846ee1a45083233ba99c8c8aa8551c504a67530990e5953a839a9c28b24bc893c9541872790caa67531c254f20954ea1239ca9c702a28649790693c98149e4a353a9889ddc03066ae97570223830e2082e6e2a60115dc4054105520a5dc42815186ee91331009dc1041770677330ee08cd4452aa9031149ddd3320e37901472aee15431492b8d5c044194546a06ea30a2882620462550e388c472ab8d5c30151892551a8086e2a309515220988708c5c4846253a8d5e64718a71a9ddc25dc3b8c1dc62548d52774c8e4cc0331de5e4025432a373701c3ba98a26a626430c70724926e72ae0a0cde5c198914ce4512151426625491d2a288a9099c8e1d422998a254e399833197790515e5c28cc51c9514cc38cc75771233247492661c66ee0cc19a4eeb321dc30ca770c33b8eb322aa1dc4927791d42a2383ab8f321199809983338199e4a13a84667770154ee660557701b9a8a1dc660ccaa196472a455213b8cd3321110188cc407790089dd253913053bc81332ee0f22093bc881dc64cc10119c819cbb9226497713219414c8e97706770ee3933023304908cc199ddc124277052184ee399c8c881de4492f222383b9643a64443899a86ee049046549dcc5321c653ba56414ee928e4cc1de405c9049394233793ba4b21112aa8007719979700155e5e5de4700aaee009546611939de641980aa330bb80ccaa3309dc4794cb8e7480cc401a89954661124e771d3332706601954661770553060cc10c50cb208c51cba98c8e02267972a8cc2771029552ee063308a4e774a64029543844ef277990618718ba982a85500aa72e550c6660665508bb82a980cd5409c51451465c17510c30dd40827204139022184e5c1964104c11ac85146412986082e20a861894e5d411823904650461aca8eee263aa85395466604c185352a8cc199dc2277106602a8cc2e9700466292a8cce149dc53332f2f2f200caa3308b80554cbbbb819882a9860672014726f3205408dc304a29ba9a644aa330119a642220662030a69912a8cc22265cee70603317050cc4e2ea61320ab24815499724aaa24aa33390199553211770086e25530e0349ac80cd2b277150c54855032a89a4e40673205510551334c859770030d54e5e641c5c1ca6e00bc9b8284dd4540ddc0dc306997170a0cb22eaa06e0dc5c31321861ccb89906997171450dc1c8baa8830395770c48e41c891cb8b9218391755048e541b8b8624721923970c3717143385d544cc102a099a533201514304130d564e643954104aa219c30c4e2aa8309d430e4e1882aa219c30c4e550c2184e5513306694cc814cf322822998ae997710a5914104665496443755092a8e4305510c1b95431544465548e490a32aa4727733050a1199566404aa60808dcc10e170ccc19aa84aa334c80a332acc82a9850aa33084aa334c9dc2249ddc5ddc2641982ab8319840caa330a64ee20ef20662154155c0a720ce414e62035398cb954677308ccc923ba521dc155c1c6655033105530531c106550dcc5caa330e55088c8eef3206621540caae0d40d4c7027750c30ddc50c350c359704a098230d6434bba98954331ddcc485c1022a9546670b88814aaee381844665515d2771e64999030c50cdd4c4029c9ca6ea0186b2eae00cdd65403303317979141b8618514c643775302770a2cb8a288a094642885197750608272e08313022186272082608272ee2861ac8104e4104d418861898209acb8e0c3220454302391054c74820b88a0a45411a411a4430a9c87104c11a820982359775319142861b9896554156462860c3913b828c51cb88518a3913ba9547261c199e4aa33bb9806655770a02e332ac84154c10419dcc114ee14219432e19421943277352a8cc32771100ccaaee066a02065153088ccaa066201544caa333845c1c66553c9dc794c80e022332ac809c64ef2f206066e0ce510651375310e0055cce229d4dd400d5e43370caaae00c3713755053ab8606721bb850651390539062a8830dc351390a6283289cbba9804640465dc022e1456428a3202e6145735020c820cb9851641165cd46428e5190a53027305465dd418110c0c39751379021c4e40e430e5d4704190c310c32ea21861c8230e5d430dc104c11a64104c11cba89c8388e389c8349d418620ca82e20c3950dc118721b89cbb804c026f2af20839c829b82284e45c18a49cb81c820992104e5dc4c286597012b820acb88518a3970650cb2e26b228e05c430608de44c50ae2186513590a6089539042898514cb8530a6228a614c64502a628a6214d214d232e219432c8130d432cb861882a1841590c3105490965c54288a61445390a2144c548a72e28a2284c51452284e430d4511426284134cb88a298a3904651472e08c350465904650d32e2a720c3591c1388670ce2638a711c26b2085130e4371453145310c2990c29710a2098721b8a104c3925c4c32a4e0952710d2189cd65dd4c419812c8a0964ee085104cb204725141104cb21bb989554067755002eae2390c11830dd4186ea23910c3182391770a39030e4348b88308a8e430ca39025918a30e451a5c11a43710c2a3910c1182728e45dd4aa3300a886186790ca704653ca89954e33bb980ccaa170054caa6019baa8086417706190c082ea0417530c8608c32ee6143228105cc09a864504a19770a1901065c1b9b8a350c81186b210c22c861065c30643731522b8d4320cb2114e32865dcd4aa1caa3331cee1711030c519dd4c406539ba81955c06eaa0aa218604137046a2a60aa21812a81531314eee031530667790d5429d25519872a8e4ee612550b87505508ccaa0a332a9dd270b88a6666664019ab80ce5c0672728818e4e51375310a1c005cd5c593905c40a932c89d4dd40c4926e246e5559704818137130e6997595000d644d470430730d654c5e5e404a8ba8804489c8b829b8186af203919120c197193121459719041872e15c32c8c9ab8a982ba8e384ac8e3ab8a890dc406f22472a20c370d45d4cc3887013ca89b87132a60939c98539ab84820cbc99238571c9519351c492320532e6142c898137571509591321532ee3829b8614de64506e0de41b8f2b2a18614c424c66410621ccb8a04c390d2b2283917575149020cabc8902604e5640d320d322aee05c098531453170c29b8a28a6e3320c319143a98a38ea6228a930a691990c514c3990c33a645dc5025970430c5c10c31790430c5c71c656450e64c86959143264959112590722eeaa21c4b8973590c4b860826e05c0b9cac883705170428bc80ab8a255e4e430209cb85114261d43a8875144dc51444a8a2e0545245ce644186f205c7502e3a98171d4729cc8a195c104c351c209823571c711c2608d664554492720d32e08c2885190a22c9c8628261ccb8a30524a925390c1c8baa86041350209acc8608c3997142098e3a87511462898a9144909cc862a49390c51a645c51d2524a7229232c88617551733170551c288517570c0826e04137550e20c4c05d220522a1c69104a9535072a8812a9d26ee6294cc872c8a2871cc4ae692c81caf2590a72b814e5ca1d2590dc48cb2732b98a0259315cae1229cb94524912c892c8a2609c6e573106294c96455403b8de4aa3900dc6eaa022e28a0c91909104e545d42a9860721a8a8924e470e3ca92722185712f23a4e47182285c70c8e72218e2c8e42a472388aa8832a891c860a4720aa891c891c8625511143062550aa22ee06a1139b8653955430c338dc5181129c6ea92aa647260199d2b2a24f20aa1d4cce99050a75393c8228251524110c30882aa186218625533042a8a66e3b93322552428caa748e4ceee6024664abac85c154198142abc85c71998e5559901c2e629554c0730baa8331451249c8924e55cd4104bac838f2a48c998484e4703571437990e3cc88e18a371c73990699133072986471c791d2b224b2228692564266aa38a714eaa127590a2987320e5c4964eaa264e247272a998330a330d5430caae2ee0a6a38332a8ae17106650a3309cae12aa8350aa30c72a9c2370954666025530ea066770a7714329dcd5212a8cd332008ccab279055305309c255199d32770b88801199991210119866440cc40ee551984474cc833055301564ee5519808cc3220aa60553b954660ea334c8295466148c881de64046620aa60eea029ac80a2c8b9ac8e39e5dc28a593baa860c1a8e4ee553303350506a193b8ccaa233320a5570284466553b8e794815477701995d419815450888118998094466aa06620e551984e2ef33202a863313101ca6ea60eea06628a18730e6a3873591735018722a6777004397133b95543060a314722ea772a8ccc04aa605405165cd4ee55198444062a9ab819a80e6a110cccaa77072ab838ccaa7790ee7994c80ee55033b954cc40e29d5d4c3b801ce45cc140acb8850c35910c29c8730e39ca817041731c7104173591735924388e38353861a9e454cf2ee2815c451432c87328e39965c4cb27755033b8e41dd4062e144314721c75918e3a8e45d4577155472660199547779081c557530775033145061ac8430d432e6a0e6a7770533b9554301ba9dcaa3330c8880aa1989882954c1dd438e2871d45cd43770e53b9554307519dcaa33301995d4705508ccaa7708880ccaae38384466553bc8773a6532014775979900e2ab8a8195446662071caaea6077571401d44dd640e05cc5cc1c38ab8862875371260851350438b9218861c722e625c50b2e218a196441c8a19645cd5c4d640a7951033c8833c853c821c4c11c7135146f22a6777140ee5910732c832c82098510a2e28a228a2e6e28d644c28a19cb2627772aa81dd5c3071bc805c5c182a238190c317106288830c45d5d470e575390e390c70ca71c8a9ddc2829c5c6593b95546660770ee5553075700e617930284de41d5c1a8e182e628ae282e6ae6065731950e628e194279353bb839641c6e612c9dcaaa0eea06e286394239753b95466611101454188ccc407154dd4c3b80dcc15c40d4430c374861ba545cd4199ceee037329dcaaa0eea053ba8cee5519981dcaa60eea0c30e5375144ee1dcaaa06772a8ccc2220332ab8e0e1119954ef24ccccccc8070e5957150c30938e5c18e5544cc4141de424e6595753024ef2ae2641de4198a286380b98172448b9ac8b9a8931450730473548b9aa64388e14098489ac8829e45d4c03514a986974c9de5c24af21c0172448b9c8b980659173501cdc5264aa64b2380e44ce5164e59775501457951bc82ba81c86144b80cba8c828c64d5c0e32e32955401056454e39954eee1dc03a8ba543aa4c53bb853b9555320cee93933016541654eef2030d4dd41980b8a28e0dc90dd43a8c9ba80eb21571c26333006e72170547332aa833006b261506a171466614665553bb81c557350ee0263830d5d2628a8350a4e777069094ee5550c1d52119dcaa3334cc819019954ee99111
set_option hygiene false in
local macro "F " x0:ident x1:num x2:num x3:num x4:num x5:num x6:num x7:num x8:num x9:num x10:num : command => `(command|
noncomputable def $x0 : AG.Box := (AG.Box.mk $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 $x10))
F bx0 30720 40448 31744 38400 31744 38400 31744 38400 30720 40448
set_option hygiene false in
local macro "H " x0:ident x1:num x2:num x3:ident x4:num : command => `(command|
theorem $x0 : AG.walk table bits $x1 $x2 $x3 = some $x4 :=
  (AG.A8 table bits $x1 $x2 $x3).symm.trans (by decide +kernel))
H wk0 64 0 bx0 2051
F ZL 30720 40448 31744 38400 31744 38400 31744 38400 57344 458752
set_option hygiene false in
local macro "I " x0:ident x1:ident x2:num : command => `(command|
noncomputable def $x0 : AG.Box := ($x1).BG (AG.Ao bits $x2) (AG.Box.mid $x1 (AG.Ao bits $x2)))
I aD ZL 2051
I aE aD 2055
I bx4 aE 2059
H wk4 61 2063 bx4 6079
set_option hygiene false in
local macro "J " x0:ident x1:ident x2:num : command => `(command|
noncomputable def $x0 : AG.Box := ($x1).BH (AG.Ao bits $x2) (AG.Box.mid $x1 (AG.Ao bits $x2)))
J bx5 aE 2059
H wk5 61 6079 bx5 7065
set_option hygiene false in
local macro "K " x0:ident x1:num x2:num x3:ident x4:num x5:num x6:num x7:ident x8:ident : command => `(command|
theorem $x0 : AG.walk table bits $x1 $x2 $x3 = some $x4 :=
  AG.A9 table bits $x5 $x2 $x3 $x6 $x4 (by decide +kernel) $x7 $x8)
K wk3 62 2059 aE 7065 61 6079 wk4 wk5
J bx6 aD 2055
H wk6 62 7065 bx6 7776
K wk2 63 2055 aD 7776 62 7065 wk3 wk6
J bx7 ZL 2051
H wk7 63 7776 bx7 7807
K wk1 64 2051 ZL 7807 63 7776 wk2 wk7
F ZM 30720 40448 31744 38400 31744 38400 59904 75264 30720 40448
I aF ZM 7807
I AEk aF 7811
H ASV 62 7815 AEk 9281
J Wh aF 7811
I Wi Wh 9281
I Wj Wi 9285
I AEl Wj 9289
H ASZ 59 9293 AEl 9689
J AEm Wj 9289
H ASa 59 9689 AEm 14640
K ASY 60 9289 Wj 14640 59 9689 ASZ ASa
J AEn Wi 9285
H ASb 60 14640 AEn 14706
K ASX 61 9285 Wi 14706 60 14640 ASY ASb
J AEo Wh 9281
H ASc 61 14706 AEo 14832
K ASW 62 9281 Wh 14832 61 14706 ASX ASc
K wk9 63 7811 aF 14832 62 9281 ASV ASW
J AEp ZM 7807
H ASd 63 14832 AEp 14958
K wk8 64 7807 ZM 14958 63 14832 wk9 ASd
F WA 30720 40448 31744 38400 31744 38400 59904 75264 57344 458752
I Wn WA 14958
I Wq Wn 14962
I Wr Wq 14966
I Ws Wr 14970
I Ww Ws 14974
I AEq Ww 14978
H ASk 58 14982 AEq 15528
J AEr Ww 14978
H ASl 58 15528 AEr 20089
K ASj 59 14978 Ww 20089 58 15528 ASk ASl
J AEs Ws 14974
H ASm 59 20089 AEs 20175
K ASi 60 14974 Ws 20175 59 20089 ASj ASm
J AEt Wr 14970
H ASn 60 20175 AEt 21916
K ASh 61 14970 Wr 21916 60 20175 ASi ASn
J AEu Wq 14966
H ASo 61 21916 AEu 22647
K ASg 62 14966 Wq 22647 61 21916 ASh ASo
J AEv Wn 14962
H ASp 62 22647 AEv 22953
K ASf 63 14962 Wn 22953 62 22647 ASg ASp
J AEw WA 14958
H ASq 63 22953 AEw 22954
K ASe 64 14958 WA 22954 63 22953 ASf ASq
F pQ 30720 40448 31744 38400 31744 38400 88064 270336 30720 40448
H ASr 64 22954 pQ 25665
F pU 30720 40448 31744 38400 31744 38400 88064 270336 57344 458752
H ASs 64 25665 pU 27411
F WB 30720 40448 31744 38400 60416 74752 31744 38400 30720 40448
I Wz WB 27411
I AEx Wz 27415
H ASv 62 27419 AEx 28360
J W7 Wz 27415
I W8 W7 28360
I AEy W8 28364
H ASy 60 28368 AEy 29594
J W9 W8 28364
I XB W9 29594
I AEz XB 29598
H AS1 58 29602 AEz 30233
J AE0 XB 29598
H AS2 58 30233 AE0 34949
K AS0 59 29598 XB 34949 58 30233 AS1 AS2
J AE1 W9 29594
H AS3 59 34949 AE1 35105
K ASz 60 29594 W9 35105 59 34949 AS0 AS3
K ASx 61 28364 W8 35105 60 29594 ASy ASz
J AE2 W7 28360
H AS4 61 35105 AE2 35201
K ASw 62 28360 W7 35201 61 35105 ASx AS4
K ASu 63 27415 Wz 35201 62 28360 ASv ASw
J AE3 WB 27411
H AS5 63 35201 AE3 35337
K ASt 64 27411 WB 35337 63 35201 ASu AS5
F WC 30720 40448 31744 38400 60416 74752 31744 38400 57344 458752
I XC WC 35337
I XD XC 35341
I XE XD 35345
I XG XE 35349
I XH XG 35353
I AE4 XH 35357
H ATC 58 35361 AE4 36252
J XI XH 35357
I XJ XI 36252
I AE5 XJ 36256
H ATF 56 36260 AE5 36801
J XK XJ 36256
I XM XK 36801
I AE6 XM 36805
H ATI 54 36809 AE6 37955
J XO XM 36805
I XP XO 37955
I AE7 XP 37959
H ATL 52 37963 AE7 38519
J XQ XP 37959
I XR XQ 38519
I AE8 XR 38523
H ATO 50 38527 AE8 38773
J XS XR 38523
I XT XS 38773
I XU XT 38777
I AE9 XU 38781
H ATS 47 38785 AE9 43596
J AFA XU 38781
H ATT 47 43596 AFA 43907
K ATR 48 38781 XU 43907 47 43596 ATS ATT
J XV XT 38777
I AFB XV 43907
H ATV 47 43911 AFB 48877
J AFC XV 43907
H ATW 47 48877 AFC 49143
K ATU 48 43907 XV 49143 47 48877 ATV ATW
K ATQ 49 38777 XT 49143 48 43907 ATR ATU
J AFD XS 38773
H ATY 49 49143 AFD 49874
K ATP 50 38773 XS 49874 49 49143 ATQ ATY
K ATN 51 38523 XR 49874 50 38773 ATO ATP
J AFE XQ 38519
H ATZ 51 49874 AFE 50225
K ATM 52 38519 XQ 50225 51 49874 ATN ATZ
K ATK 53 37959 XP 50225 52 38519 ATL ATM
J AFF XO 37955
H ATa 53 50225 AFF 50341
K ATJ 54 37955 XO 50341 53 50225 ATK ATa
K ATH 55 36805 XM 50341 54 37955 ATI ATJ
J AFG XK 36801
H ATb 55 50341 AFG 50392
K ATG 56 36801 XK 50392 55 50341 ATH ATb
K ATE 57 36256 XJ 50392 56 36801 ATF ATG
J AFH XI 36252
H ATc 57 50392 AFH 50483
K ATD 58 36252 XI 50483 57 50392 ATE ATc
K ATB 59 35357 XH 50483 58 36252 ATC ATD
J AFI XG 35353
H ATd 59 50483 AFI 50514
K ATA 60 35353 XG 50514 59 50483 ATB ATd
J AFJ XE 35349
H ATe 60 50514 AFJ 53680
K AS9 61 35349 XE 53680 60 50514 ATA ATe
J AFK XD 35345
H ATf 61 53680 AFK 54551
K AS8 62 35345 XD 54551 61 53680 AS9 ATf
J AFL XC 35341
H ATg 62 54551 AFL 54807
K AS7 63 35341 XC 54807 62 54551 AS8 ATg
J AFM WC 35337
H ATh 63 54807 AFM 54808
K AS6 64 35337 WC 54808 63 54807 AS7 ATh
F WD 30720 40448 31744 38400 60416 74752 59904 75264 30720 40448
I Xb WD 54808
I AFN Xb 54812
H ATk 62 54816 AFN 55062
J Xc Xb 54812
I Xd Xc 55062
I AFO Xd 55066
H ATn 60 55070 AFO 55786
J Xf Xd 55066
I Xg Xf 55786
I Xh Xg 55790
I AFQ Xh 55794
H ATr 57 55798 AFQ 55899
J Xj Xh 55794
I AFR Xj 55899
H ATt 56 55903 AFR 56154
J Xk Xj 55899
I Xl Xk 56154
I Xm Xl 56158
I AFS Xm 56162
H ATx 53 56166 AFS 56287
J KS Xm 56162
I rF KS 56287
H AFr 52 56291 rF 60957
J rG KS 56287
H AFs 52 60957 rG 64588
K AFq 53 56287 KS 64588 52 60957 AFr AFs
K ATw 54 56162 Xm 64588 53 56287 ATx AFq
J rH Xl 56158
H AFt 54 64588 rH 64789
K ATv 55 56158 Xl 64789 54 64588 ATw AFt
J rJ Xk 56154
H AFu 55 64789 rJ 65400
K ATu 56 56154 Xk 65400 55 64789 ATv AFu
K ATs 57 55899 Xj 65400 56 56154 ATt ATu
K ATq 58 55794 Xh 65400 57 55899 ATr ATs
J rO Xg 55790
H AFv 58 65400 rO 65496
K ATp 59 55790 Xg 65496 58 65400 ATq AFv
J rP Xf 55786
H AFw 59 65496 rP 65657
K ATo 60 55786 Xf 65657 59 65496 ATp AFw
K ATm 61 55066 Xd 65657 60 55786 ATn ATo
J rS Xc 55062
H AFx 61 65657 rS 65718
K ATl 62 55062 Xc 65718 61 65657 ATm AFx
K ATj 63 54812 Xb 65718 62 55062 ATk ATl
J rT WD 54808
H AFy 63 65718 rT 65914
K ATi 64 54808 WD 65914 63 65718 ATj AFy
F bF 30720 40448 31744 38400 60416 74752 59904 75264 57344 458752
H AFz 64 65914 bF 69865
F bR 30720 40448 31744 38400 60416 74752 88064 270336 30720 40448
H AF0 64 69865 bR 70596
F bU 30720 40448 31744 38400 60416 74752 88064 270336 57344 458752
H AF1 64 70596 bU 70872
F bY 30720 40448 31744 38400 88576 245760 31744 38400 30720 40448
H AF2 64 70872 bY 73683
F bZ 30720 40448 31744 38400 88576 245760 31744 38400 57344 458752
H AF3 64 73683 bZ 76069
F b9 30720 40448 31744 38400 88576 245760 59904 75264 30720 40448
H AF4 64 76069 b9 76705
F cD 30720 40448 31744 38400 88576 245760 59904 75264 57344 458752
H AF5 64 76705 cD 76946
F cE 30720 40448 31744 38400 88576 245760 88064 270336 30720 40448
H AF6 64 76946 cE 77047
F cO 30720 40448 31744 38400 88576 245760 88064 270336 57344 458752
H AF7 64 77047 cO 77088
F Iz 30720 40448 59904 75264 31744 38400 31744 38400 30720 40448
I KT Iz 77088
I rV KT 77092
H AGA 62 77096 rV 78147
J KV KT 77092
I KW KV 78147
I KX KW 78151
I rW KX 78155
H AGE 59 78159 rW 78515
J r7 KX 78155
H AGF 59 78515 r7 83186
K AGD 60 78155 KX 83186 59 78515 AGE AGF
J r8 KW 78151
H AGG 60 83186 r8 83252
K AGC 61 78151 KW 83252 60 83186 AGD AGG
J r9 KV 78147
H AGH 61 83252 r9 83378
K AGB 62 78147 KV 83378 61 83252 AGC AGH
K AF9 63 77092 KT 83378 62 78147 AGA AGB
J sI Iz 77088
H AGI 63 83378 sI 83504
K AF8 64 77088 Iz 83504 63 83378 AF9 AGI
F I7 30720 40448 59904 75264 31744 38400 31744 38400 57344 458752
I KZ I7 83504
I Kd KZ 83508
I Kh Kd 83512
I Kk Kh 83516
I Km Kk 83520
I sK Km 83524
H AGQ 58 83528 sK 84569
J Kq Km 83524
I Kt Kq 84569
I sO Kt 84573
H AGT 56 84577 sO 85003
J Ku Kt 84573
I Kw Ku 85003
I sP Kw 85007
H AGW 54 85011 sP 85717
J Ky Kw 85007
I Kz Ky 85717
I sW Kz 85721
H AGZ 52 85725 sW 86221
J K4 Kz 85721
I K5 K4 86221
I sw K5 86225
H AGc 50 86229 sw 86950
J K6 K5 86225
I K7 K6 86950
I K8 K7 86954
I K9 K8 86958
I s6 K9 86962
H AGh 46 86966 s6 91282
J s7 K9 86962
H AGi 46 91282 s7 92608
K AGg 47 86962 K9 92608 46 91282 AGh AGi
J s8 K8 86958
H AGj 47 92608 s8 94469
K AGf 48 86958 K8 94469 47 92608 AGg AGj
J LD K7 86954
I LG LD 94469
I LH LG 94473
I s9 LH 94477
H AGn 45 94481 s9 97332
J LI LH 94477
I tD LI 97332
H AGp 44 97336 tD 101967
J tJ LI 97332
H AGq 44 101967 tJ 102798
K AGo 45 97332 LI 102798 44 101967 AGp AGq
K AGm 46 94477 LH 102798 45 97332 AGn AGo
J tK LG 94473
H AGr 46 102798 tK 104464
K AGl 47 94473 LG 104464 46 102798 AGm AGr
J tL LD 94469
H AGs 47 104464 tL 104640
K AGk 48 94469 LD 104640 47 104464 AGl AGs
K AGe 49 86954 K7 104640 48 94469 AGf AGk
J tM K6 86950
H AGt 49 104640 tM 105871
K AGd 50 86950 K6 105871 49 104640 AGe AGt
K AGb 51 86225 K5 105871 50 86950 AGc AGd
J tO K4 86221
H AGu 51 105871 tO 105997
K AGa 52 86221 K4 105997 51 105871 AGb AGu
K AGY 53 85721 Kz 105997 52 86221 AGZ AGa
J tP Ky 85717
H AGv 53 105997 tP 106153
K AGX 54 85717 Ky 106153 53 105997 AGY AGv
K AGV 55 85007 Kw 106153 54 85717 AGW AGX
J tQ Ku 85003
H AGw 55 106153 tQ 106474
K AGU 56 85003 Ku 106474 55 106153 AGV AGw
K AGS 57 84573 Kt 106474 56 85003 AGT AGU
J tW Kq 84569
H AGx 57 106474 tW 106555
K AGR 58 84569 Kq 106555 57 106474 AGS AGx
K AGP 59 83524 Km 106555 58 84569 AGQ AGR
J tZ Kk 83520
H AGy 59 106555 tZ 106576
K AGO 60 83520 Kk 106576 59 106555 AGP AGy
J tj Kh 83516
H AGz 60 106576 tj 110992
K AGN 61 83516 Kh 110992 60 106576 AGO AGz
J tq Kd 83512
H AG0 61 110992 tq 112023
K AGL 62 83512 Kd 112023 61 110992 AGN AG0
J tw KZ 83508
H AG1 62 112023 tw 112384
K AGK 63 83508 KZ 112384 62 112023 AGL AG1
J uO I7 83504
H AG2 63 112384 uO 112385
K AGJ 64 83504 I7 112385 63 112384 AGK AG2
F I8 30720 40448 59904 75264 31744 38400 59904 75264 30720 40448
I LJ I8 112385
I uW LJ 112389
H AG5 62 112393 uW 112719
J LO LJ 112389
I LQ LO 112719
I uY LQ 112723
H AG8 60 112727 uY 113013
J LV LQ 112723
I LW LV 113013
I uZ LW 113017
H AHB 58 113021 uZ 113922
J LY LW 113017
I LZ LY 113922
I uj LZ 113926
H AHE 56 113930 uj 114501
J Lc LZ 113926
I Ld Lc 114501
I uq Ld 114505
H AHH 54 114509 uq 114715
J Lh Ld 114505
I Lk Lh 114715
I Ln Lk 114719
I u6 Ln 114723
H AHL 51 114727 u6 116823
J Ly Ln 114723
I Lz Ly 116823
I u7 Lz 116827
H AHO 49 116831 u7 119117
J L6 Lz 116827
I L7 L6 119117
I u9 L7 119121
H AHR 47 119125 u9 123056
J L8 L7 119121
I vE L8 123056
H AHT 46 123060 vE 127781
J vF L8 123056
H AHU 46 127781 vF 128752
K AHS 47 123056 L8 128752 46 127781 AHT AHU
K AHQ 48 119121 L7 128752 47 123056 AHR AHS
J L9 L6 119117
I vG L9 128752
H AHW 47 128756 vG 132497
J vH L9 128752
H AHX 47 132497 vH 135803
K AHV 48 128752 L9 135803 47 132497 AHW AHX
K AHP 49 119117 L6 135803 48 128752 AHQ AHV
K AHN 50 116827 Lz 135803 49 119117 AHO AHP
J vI Ly 116823
H AHY 50 135803 vI 137679
K AHM 51 116823 Ly 137679 50 135803 AHN AHY
K AHK 52 114723 Ln 137679 51 116823 AHL AHM
J MA Lk 114719
I ME MA 137679
I MG ME 137683
I vN MG 137687
H AHc 49 137691 vN 139327
J MH MG 137687
I MJ MH 139327
I vO MJ 139331
H AHf 47 139335 vO 143561
J MO MJ 139331
I MQ MO 143561
I vP MQ 143565
H AHi 45 143569 vP 144255
J MS MQ 143565
I vQ MS 144255
H AHk 44 144259 vQ 148275
J vT MS 144255
H AHl 44 148275 vT 149256
K AHj 45 144255 MS 149256 44 148275 AHk AHl
K AHh 46 143565 MQ 149256 45 144255 AHi AHj
J vW MO 143561
H AHm 46 149256 vW 149792
K AHg 47 143561 MO 149792 46 149256 AHh AHm
K AHe 48 139331 MJ 149792 47 143561 AHf AHg
J MW MH 139327
I vX MW 149792
H AHo 47 149796 vX 154267
J vY MW 149792
H AHp 47 154267 vY 158283
K AHn 48 149792 MW 158283 47 154267 AHo AHp
K AHd 49 139327 MH 158283 48 149792 AHe AHn
K AHb 50 137687 MG 158283 49 139327 AHc AHd
J MY ME 137683
I MZ MY 158283
I Mb MZ 158287
I Mc Mb 158291
I vZ Mc 158295
H AHu 46 158299 vZ 158930
J Md Mc 158295
I Me Md 158930
I vh Me 158934
H AHx 44 158938 vh 160944
J Mh Me 158934
I Mj Mh 160944
I vk Mj 160948
H AH0 42 160952 vk 161268
J Ml Mj 160948
I vq Ml 161268
H AH2 41 161272 vq 163843
J Mr Ml 161268
I v7 Mr 163843
H AH4 40 163847 v7 168238
J Mt Mr 163843
I v8 Mt 168238
H AH6 39 168242 v8 170908
J v9 Mt 168238
H AH7 39 170908 v9 173959
K AH5 40 168238 Mt 173959 39 170908 AH6 AH7
K AH3 41 163843 Mr 173959 40 168238 AH4 AH5
K AH1 42 161268 Ml 173959 41 163843 AH2 AH3
K AHz 43 160948 Mj 173959 42 161268 AH0 AH1
J wA Mh 160944
H AH8 43 173959 wA 175915
K AHy 44 160944 Mh 175915 43 173959 AHz AH8
K AHw 45 158934 Me 175915 44 160944 AHx AHy
J wB Md 158930
H AH9 45 175915 wB 177046
K AHv 46 158930 Md 177046 45 175915 AHw AH9
K AHt 47 158295 Mc 177046 46 158930 AHu AHv
J Mv Mb 158291
I Mw Mv 177046
I wC Mw 177050
H AIC 45 177054 wC 179665
J Mz Mw 177050
I M5 Mz 179665
I wI M5 179669
H AIF 43 179673 wI 180064
J M6 M5 179669
I M8 M6 180064
I M9 M8 180068
I wJ M9 180072
H AIK 40 180076 wJ 183502
J wL M9 180072
H AIL 40 183502 wL 185973
K AIJ 41 180072 M9 185973 40 183502 AIK AIL
J NA M8 180068
I wM NA 185973
H AIO 40 185977 wM 189683
J wN NA 185973
H AIP 40 189683 wN 191739
K AIN 41 185973 NA 191739 40 189683 AIO AIP
K AII 42 180068 M8 191739 41 185973 AIJ AIN
J wO M6 180064
H AIQ 42 191739 wO 192140
K AIH 43 180064 M6 192140 42 191739 AII AIQ
K AIE 44 179669 M5 192140 43 180064 AIF AIH
J wP Mz 179665
H AIR 44 192140 wP 193721
K AID 45 179665 Mz 193721 44 192140 AIE AIR
K AIB 46 177050 Mw 193721 45 179665 AIC AID
J wQ Mv 177046
H AIS 46 193721 wQ 194362
K AIA 47 177046 Mv 194362 46 193721 AIB AIS
K AHs 48 158291 Mb 194362 47 177046 AHt AIA
J NC MZ 158287
I ND NC 194362
I wR ND 194366
H AIV 46 194370 wR 195146
J NG ND 194366
I NR NG 195146
I wS NR 195150
H AIY 44 195154 wS 195825
J NU NR 195150
I NV NU 195825
I wT NV 195829
H AIb 42 195833 wT 197169
J NW NV 195829
I wW NW 197169
H AId 41 197173 wW 199024
J wX NW 197169
H AIe 41 199024 wX 203310
K AIc 42 197169 NW 203310 41 199024 AId AIe
K AIa 43 195829 NV 203310 42 197169 AIb AIc
J wY NU 195825
H AIf 43 203310 wY 203691
K AIZ 44 195825 NU 203691 43 203310 AIa AIf
K AIX 45 195150 NR 203691 44 195825 AIY AIZ
J wZ NG 195146
H AIg 45 203691 wZ 204712
K AIW 46 195146 NG 204712 45 203691 AIX AIg
K AIU 47 194366 ND 204712 46 195146 AIV AIW
J NX NC 194362
I NY NX 204712
I xB NY 204716
H AIj 45 204720 xB 205361
J xG NY 204716
H AIk 45 205361 xG 210277
K AIi 46 204716 NY 210277 45 205361 AIj AIk
J xO NX 204712
H AIl 46 210277 xO 210833
K AIh 47 204712 NX 210833 46 210277 AIi AIl
K AIT 48 194362 NC 210833 47 204712 AIU AIh
K AHr 49 158287 MZ 210833 48 194362 AHs AIT
J NZ MY 158283
I Nb NZ 210833
I xP Nb 210837
H AIo 47 210841 xP 212407
J Nc Nb 210837
I Nh Nc 212407
I xQ Nh 212411
H AIr 45 212415 xQ 216331
J Ni Nh 212411
I Nj Ni 216331
I xT Nj 216335
H AIu 43 216339 xT 216940
J Nk Nj 216335
I Nl Nk 216940
I xW Nl 216944
H AIx 41 216948 xW 218919
J xZ Nl 216944
H AIy 41 218919 xZ 223545
K AIw 42 216944 Nl 223545 41 218919 AIx AIy
J xd Nk 216940
H AIz 42 223545 xd 225996
K AIv 43 216940 Nk 225996 42 223545 AIw AIz
K AIt 44 216335 Nj 225996 43 216940 AIu AIv
J xg Ni 216331
H AI0 44 225996 xg 227382
K AIs 45 216331 Ni 227382 44 225996 AIt AI0
K AIq 46 212411 Nh 227382 45 216331 AIr AIs
J yA Nc 212407
H AI1 46 227382 yA 228038
K AIp 47 212407 Nc 228038 46 227382 AIq AI1
K AIn 48 210837 Nb 228038 47 212407 AIo AIp
J Nm NZ 210833
I Np Nm 228038
I yD Np 228042
H AI4 46 228046 yD 230842
J Nq Np 228042
I Nr Nq 230842
I yF Nr 230846
H AI7 44 230850 yF 231351
J yI Nr 230846
H AI8 44 231351 yI 236267
K AI6 45 230846 Nr 236267 44 231351 AI7 AI8
J yJ Nq 230842
H AI9 45 236267 yJ 236878
K AI5 46 230842 Nq 236878 45 236267 AI6 AI9
K AI3 47 228042 Np 236878 46 230842 AI4 AI5
J yP Nm 228038
H AJA 47 236878 yP 237199
K AI2 48 228038 Nm 237199 47 236878 AI3 AJA
K AIm 49 210833 NZ 237199 48 228038 AIn AI2
K AHq 50 158283 MY 237199 49 210833 AHr AIm
K AHa 51 137683 ME 237199 50 158283 AHb AHq
J yQ MA 137679
H AJB 51 237199 yQ 241695
K AHZ 52 137679 MA 241695 51 237199 AHa AJB
K AHJ 53 114719 Lk 241695 52 137679 AHK AHZ
J Nt Lh 114715
I Nu Nt 241695
I yT Nu 241699
H AJE 51 241703 yT 244519
J Nv Nu 241699
I yW Nv 244519
H AJG 50 244523 yW 249224
J yZ Nv 244519
H AJH 50 249224 yZ 249565
K AJF 51 244519 Nv 249565 50 249224 AJG AJH
K AJD 52 241699 Nu 249565 51 244519 AJE AJF
J zC Nt 241695
H AJI 52 249565 zC 250286
K AJC 53 241695 Nt 250286 52 249565 AJD AJI
K AHI 54 114715 Lh 250286 53 241695 AHJ AJC
K AHG 55 114505 Ld 250286 54 114715 AHH AHI
J zD Lc 114501
H AJJ 55 250286 zD 251242
K AHF 56 114501 Lc 251242 55 250286 AHG AJJ
K AHD 57 113926 LZ 251242 56 114501 AHE AHF
J zE LY 113922
H AJK 57 251242 zE 251553
K AHC 58 113922 LY 251553 57 251242 AHD AJK
K AHA 59 113017 LW 251553 58 113922 AHB AHC
J zF LV 113013
H AJL 59 251553 zF 251914
K AG9 60 113013 LV 251914 59 251553 AHA AJL
K AG7 61 112723 LQ 251914 60 113013 AG8 AG9
J zG LO 112719
H AJM 61 251914 zG 252030
K AG6 62 112719 LO 252030 61 251914 AG7 AJM
K AG4 63 112389 LJ 252030 62 112719 AG5 AG6
J zH I8 112385
H AJN 63 252030 zH 252186
K AG3 64 112385 I8 252186 63 252030 AG4 AJN
F I9 30720 40448 59904 75264 31744 38400 59904 75264 57344 458752
I Nw I9 252186
I Nz Nw 252190
I N4 Nz 252194
I N5 N4 252198
I N6 N5 252202
I zK N6 252206
H AJU 58 252210 zK 252551
J N7 N6 252206
I N8 N7 252551
I zL N8 252555
H AJX 56 252559 zL 252595
J N9 N8 252555
I OC N9 252595
I zO OC 252599
H AJa 54 252603 zO 252629
J OD OC 252599
I OE OD 252629
I zP OE 252633
H AJd 52 252637 zP 252883
J OH OE 252633
I OI OH 252883
I zQ OI 252887
H AJg 50 252891 zQ 252897
J OJ OI 252887
I OL OJ 252897
I OM OL 252901
I zR OM 252905
H AJk 47 252909 zR 256275
J zS OM 252905
H AJl 47 256275 zS 258786
K AJj 48 252905 OM 258786 47 256275 AJk AJl
J OO OL 252901
I OP OO 258786
I zU OP 258790
H AJo 46 258794 zU 260005
J OQ OP 258790
I OT OQ 260005
I OU OT 260009
I OV OU 260013
I zV OV 260017
H AJt 42 260021 zV 260297
J OW OV 260017
I zW OW 260297
H AJv 41 260301 zW 261577
J OX OW 260297
I OY OX 261577
I zX OY 261581
H AJy 39 261585 zX 262296
J OZ OY 261581
I zY OZ 262296
H AJ0 38 262300 zY 263276
J zj OZ 262296
H AJ1 38 263276 zj 267407
K AJz 39 262296 OZ 267407 38 263276 AJ0 AJ1
K AJx 40 261581 OY 267407 39 262296 AJy AJz
J Oa OX 261577
I z4 Oa 267407
H AJ3 39 267411 z4 269162
J z5 Oa 267407
H AJ4 39 269162 z5 273813
K AJ2 40 267407 Oa 273813 39 269162 AJ3 AJ4
K AJw 41 261577 OX 273813 40 267407 AJx AJ2
K AJu 42 260297 OW 273813 41 261577 AJv AJw
K AJs 43 260017 OV 273813 42 260297 AJt AJu
J z6 OU 260013
H AJ5 43 273813 z6 274224
K AJr 44 260013 OU 274224 43 273813 AJs AJ5
J z7 OT 260009
H AJ6 44 274224 z7 276970
K AJq 45 260009 OT 276970 44 274224 AJr AJ6
J Ob OQ 260005
I Oc Ob 276970
I Od Oc 276974
I z8 Od 276978
H AKB 42 276982 z8 279173
J Oe Od 276978
I Oi Oe 279173
I z9 Oi 279177
H AKE 40 279181 z9 281982
J Oj Oi 279177
I AAA Oj 281982
H AKG 39 281986 AAA 283337
J Ol Oj 281982
I AAC Ol 283337
H AKI 38 283341 AAC 285937
J AAD Ol 283337
H AKJ 38 285937 AAD 289833
K AKH 39 283337 Ol 289833 38 285937 AKI AKJ
K AKF 40 281982 Oj 289833 39 283337 AKG AKH
K AKD 41 279177 Oi 289833 40 281982 AKE AKF
J Om Oe 279173
I AAE Om 289833
H AKL 40 289837 AAE 292593
J AAF Om 289833
H AKM 40 292593 AAF 297274
K AKK 41 289833 Om 297274 40 292593 AKL AKM
K AKC 42 279173 Oe 297274 41 289833 AKD AKK
K AJ9 43 276978 Od 297274 42 279173 AKB AKC
J AAG Oc 276974
H AKN 43 297274 AAG 297635
K AJ8 44 276974 Oc 297635 43 297274 AJ9 AKN
J AAH Ob 276970
H AKO 44 297635 AAH 300731
K AJ7 45 276970 Ob 300731 44 297635 AJ8 AKO
K AJp 46 260005 OQ 300731 45 276970 AJq AJ7
K AJn 47 258790 OP 300731 46 260005 AJo AJp
J Oo OO 258786
I Oq Oo 300731
I Ot Oq 300735
I AAI Ot 300739
H AKS 44 300743 AAI 301244
J Ou Ot 300739
I AAJ Ou 301244
H AKU 43 301248 AAJ 305144
J AAK Ou 301244
H AKV 43 305144 AAK 308115
K AKT 44 301244 Ou 308115 43 305144 AKU AKV
K AKR 45 300739 Ot 308115 44 301244 AKS AKT
J AAL Oq 300735
H AKW 45 308115 AAL 308286
K AKQ 46 300735 Oq 308286 45 308115 AKR AKW
J Ov Oo 300731
I Ow Ov 308286
I Ox Ow 308290
I AAM Ox 308294
H AKa 43 308298 AAM 311989
J AAN Ox 308294
H AKb 43 311989 AAN 313925
K AKZ 44 308294 Ox 313925 43 311989 AKa AKb
J AAO Ow 308290
H AKc 44 313925 AAO 314011
K AKY 45 308290 Ow 314011 44 313925 AKZ AKc
J AAP Ov 308286
H AKd 45 314011 AAP 314092
K AKX 46 308286 Ov 314092 45 314011 AKY AKd
K AKP 47 300731 Oo 314092 46 308286 AKQ AKX
K AJm 48 258786 OO 314092 47 300731 AJn AKP
K AJi 49 252901 OL 314092 48 258786 AJj AJm
J Oy OJ 252897
I AAQ Oy 314092
H AKf 48 314096 AAQ 317917
J AAR Oy 314092
H AKg 48 317917 AAR 320258
K AKe 49 314092 Oy 320258 48 317917 AKf AKg
K AJh 50 252897 OJ 320258 49 314092 AJi AKe
K AJf 51 252887 OI 320258 50 252897 AJg AJh
J AAT OH 252883
H AKh 51 320258 AAT 320764
K AJe 52 252883 OH 320764 51 320258 AJf AKh
K AJc 53 252633 OE 320764 52 252883 AJd AJe
J AAU OD 252629
H AKi 53 320764 AAU 320945
K AJb 54 252629 OD 320945 53 320764 AJc AKi
K AJZ 55 252599 OC 320945 54 252629 AJa AJb
J AAV N9 252595
H AKj 55 320945 AAV 321031
K AJY 56 252595 N9 321031 55 320945 AJZ AKj
K AJW 57 252555 N8 321031 56 252595 AJX AJY
J AAW N7 252551
H AKk 57 321031 AAW 321112
K AJV 58 252551 N7 321112 57 321031 AJW AKk
K AJT 59 252206 N6 321112 58 252551 AJU AJV
J AAX N5 252202
H AKl 59 321112 AAX 321153
K AJS 60 252202 N5 321153 59 321112 AJT AKl
J AAY N4 252198
H AKm 60 321153 AAY 322824
K AJR 61 252198 N4 322824 60 321153 AJS AKm
J AAZ Nz 252194
H AKn 61 322824 AAZ 323060
K AJQ 62 252194 Nz 323060 61 322824 AJR AKn
J AAa Nw 252190
H AKo 62 323060 AAa 323086
K AJP 63 252190 Nw 323086 62 323060 AJQ AKo
J AAb I9 252186
H AKp 63 323086 AAb 323087
K AJO 64 252186 I9 323087 63 323086 AJP AKp
F cP 30720 40448 59904 75264 31744 38400 88064 270336 30720 40448
H AKq 64 323087 cP 326378
F cV 30720 40448 59904 75264 31744 38400 88064 270336 57344 458752
H AKr 64 326378 cV 326984
F JE 30720 40448 59904 75264 60416 74752 31744 38400 30720 40448
I Oz JE 326984
I AAc Oz 326988
H AKu 62 326992 AAc 327233
J O4 Oz 326988
I O5 O4 327233
I AAd O5 327237
H AKx 60 327241 AAd 327777
J O6 O5 327237
I O7 O6 327777
I O8 O7 327781
I AAe O8 327785
H AK1 57 327789 AAe 327880
J O9 O8 327785
I AAf O9 327880
H AK3 56 327884 AAf 328135
J PI O9 327880
I PL PI 328135
I PN PL 328139
I AAg PN 328143
H AK7 53 328147 AAg 328358
J PO PN 328143
I AAh PO 328358
H AK9 52 328362 AAh 331438
J AAi PO 328358
H ALA 52 331438 AAi 334884
K AK8 53 328358 PO 334884 52 331438 AK9 ALA
K AK6 54 328143 PN 334884 53 328358 AK7 AK8
J AAj PL 328139
H ALB 54 334884 AAj 334885
K AK5 55 328139 PL 334885 54 334884 AK6 ALB
J AAk PI 328135
H ALC 55 334885 AAk 335551
K AK4 56 328135 PI 335551 55 334885 AK5 ALC
K AK2 57 327880 O9 335551 56 328135 AK3 AK4
K AK0 58 327785 O8 335551 57 327880 AK1 AK2
J AAl O7 327781
H ALD 58 335551 AAl 335647
K AKz 59 327781 O7 335647 58 335551 AK0 ALD
J AAm O6 327777
H ALE 59 335647 AAm 335783
K AKy 60 327777 O6 335783 59 335647 AKz ALE
K AKw 61 327237 O5 335783 60 327777 AKx AKy
J AAn O4 327233
H ALG 61 335783 AAn 335844
K AKv 62 327233 O4 335844 61 335783 AKw ALG
K AKt 63 326988 Oz 335844 62 327233 AKu AKv
J AAo JE 326984
H ALH 63 335844 AAo 336040
K AKs 64 326984 JE 336040 63 335844 AKt ALH
F JG 30720 40448 59904 75264 60416 74752 31744 38400 57344 458752
I PS JG 336040
I PV PS 336044
I PW PV 336048
I PY PW 336052
I PZ PY 336056
I AAp PZ 336060
H ALP 58 336064 AAp 336405
J Pd PZ 336060
I Pe Pd 336405
I AAq Pe 336409
H ALS 56 336413 AAq 336459
J Ph Pe 336409
I Pk Ph 336459
I AAr Pk 336463
H ALV 54 336467 AAr 336478
J Pq Pk 336463
I Pv Pq 336478
I AAs Pv 336482
H ALY 52 336486 AAs 336622
J Pw Pv 336482
I Py Pw 336622
I AAt Py 336626
H ALb 50 336630 AAt 336636
J Pz Py 336626
I P7 Pz 336636
I AAu P7 336640
H ALe 48 336644 AAu 338515
J P8 P7 336640
I P9 P8 338515
I AAv P9 338519
H ALh 46 338523 AAv 340254
J QC P9 338519
I QD QC 340254
I QE QD 340258
I AAw QE 340262
H ALl 43 340266 AAw 343562
J QF QE 340262
I AAx QF 343562
H ALn 42 343566 AAx 346932
J AAy QF 343562
H ALo 42 346932 AAy 351438
K ALm 43 343562 QF 351438 42 346932 ALn ALo
K ALk 44 340262 QE 351438 43 343562 ALl ALm
J QG QD 340258
I QI QG 351438
I AAz QI 351442
H ALr 42 351446 AAz 355967
J QJ QI 351442
I AA0 QJ 355967
H ALt 41 355971 AA0 358662
J AA1 QJ 355967
H ALu 41 358662 AA1 362223
K ALs 42 355967 QJ 362223 41 358662 ALt ALu
K ALq 43 351442 QI 362223 42 355967 ALr ALs
J QK QG 351438
I QN QK 362223
I AA2 QN 362227
H ALx 41 362231 AA2 362467
J QO QN 362227
I AA3 QO 362467
H ALz 40 362471 AA3 365072
J AA4 QO 362467
H AL0 40 365072 AA4 368758
K ALy 41 362467 QO 368758 40 365072 ALz AL0
K ALw 42 362227 QN 368758 41 362467 ALx ALy
J QS QK 362223
I AA5 QS 368758
H AL2 41 368762 AA5 372773
J AA6 QS 368758
H AL3 41 372773 AA6 375769
K AL1 42 368758 QS 375769 41 372773 AL2 AL3
K ALv 43 362223 QK 375769 42 368758 ALw AL1
K ALp 44 351438 QG 375769 43 362223 ALq ALv
K ALj 45 340258 QD 375769 44 351438 ALk ALp
J AA7 QC 340254
H AL4 45 375769 AA7 375925
K ALi 46 340254 QC 375925 45 375769 ALj AL4
K ALg 47 338519 P9 375925 46 340254 ALh ALi
J QV P8 338515
I QW QV 375925
I AA8 QW 375929
H AL7 45 375933 AA8 379914
J AA9 QW 375929
H AL8 45 379914 AA9 382855
K AL6 46 375929 QW 382855 45 379914 AL7 AL8
J ABE QV 375925
H AL9 46 382855 ABE 382936
K AL5 47 375925 QV 382936 46 382855 AL6 AL9
K ALf 48 338515 P8 382936 47 375925 ALg AL5
K ALd 49 336640 P7 382936 48 338515 ALe ALf
J QX Pz 336636
I QY QX 382936
I ABF QY 382940
H AMD 47 382944 ABF 384615
J QZ QY 382940
I Qa QZ 384615
I Qb Qa 384619
I ABG Qb 384623
H AMH 44 384627 ABG 386118
J Qd Qb 384623
I Qe Qd 386118
I ABH Qe 386122
H AMK 42 386126 ABH 389377
J ABJ Qe 386122
H AML 42 389377 ABJ 392483
K AMJ 43 386122 Qe 392483 42 389377 AMK AML
J ABK Qd 386118
H AMM 43 392483 ABK 392564
K AMI 44 386118 Qd 392564 43 392483 AMJ AMM
K AMG 45 384623 Qb 392564 44 386118 AMH AMI
J ABL Qa 384619
H AMN 45 392564 ABL 393665
K AMF 46 384619 Qa 393665 45 392564 AMG AMN
J ABM QZ 384615
H AMO 46 393665 ABM 393766
K AME 47 384615 QZ 393766 46 393665 AMF AMO
K AMC 48 382940 QY 393766 47 384615 AMD AME
J ABN QX 382936
H AMP 48 393766 ABN 395112
K AMA 49 382936 QX 395112 48 393766 AMC AMP
K ALc 50 336636 Pz 395112 49 382936 ALd AMA
K ALa 51 336626 Py 395112 50 336636 ALb ALc
J ABO Pw 336622
H AMQ 51 395112 ABO 395713
K ALZ 52 336622 Pw 395713 51 395112 ALa AMQ
K ALX 53 336482 Pv 395713 52 336622 ALY ALZ
J ABP Pq 336478
H AMR 53 395713 ABP 395924
K ALW 54 336478 Pq 395924 53 395713 ALX AMR
K ALU 55 336463 Pk 395924 54 336478 ALV ALW
J ABR Ph 336459
H AMT 55 395924 ABR 395995
K ALT 56 336459 Ph 395995 55 395924 ALU AMT
K ALR 57 336409 Pe 395995 56 336459 ALS ALT
J ABS Pd 336405
H AMU 57 395995 ABS 396071
K ALQ 58 336405 Pd 396071 57 395995 ALR AMU
K ALO 59 336060 PZ 396071 58 336405 ALP ALQ
J ABT PY 336056
H AMV 59 396071 ABT 396092
K ALN 60 336056 PY 396092 59 396071 ALO AMV
J ABU PW 336052
H AMW 60 396092 ABU 397673
K ALM 61 336052 PW 397673 60 396092 ALN AMW
J ABV PV 336048
H AMX 61 397673 ABV 397854
K ALK 62 336048 PV 397854 61 397673 ALM AMX
J ABW PS 336044
H AMY 62 397854 ABW 397855
K ALJ 63 336044 PS 397855 62 397854 ALK AMY
J ABX JG 336040
H AMZ 63 397855 ABX 397856
K ALI 64 336040 JG 397856 63 397855 ALJ AMZ
F JH 30720 40448 59904 75264 60416 74752 59904 75264 30720 40448
I Qg JH 397856
I ABY Qg 397860
H AMc 62 397864 ABY 397880
J Qj Qg 397860
I Qk Qj 397880
I ABZ Qk 397884
H AMf 60 397888 ABZ 397894
J Ql Qk 397884
I Qn Ql 397894
I ABa Qn 397898
H AMi 58 397902 ABa 397903
J Qo Qn 397898
I Qr Qo 397903
I ABb Qr 397907
H AMl 56 397911 ABb 397917
J Qt Qr 397907
I Qv Qt 397917
I ABc Qv 397921
H AMo 54 397925 ABc 397926
J Qw Qv 397921
I ABd Qw 397926
H AMq 53 397930 ABd 401181
J ABe Qw 397926
H AMr 53 401181 ABe 403417
K AMp 54 397926 Qw 403417 53 401181 AMq AMr
K AMn 55 397921 Qv 403417 54 397926 AMo AMp
J ABf Qt 397917
H AMs 55 403417 ABf 403463
K AMm 56 397917 Qt 403463 55 403417 AMn AMs
K AMk 57 397907 Qr 403463 56 397917 AMl AMm
J ABg Qo 397903
H AMt 57 403463 ABg 403534
K AMj 58 397903 Qo 403534 57 403463 AMk AMt
K AMh 59 397898 Qn 403534 58 397903 AMi AMj
J ABh Ql 397894
H AMu 59 403534 ABh 403590
K AMg 60 397894 Ql 403590 59 403534 AMh AMu
K AMe 61 397884 Qk 403590 60 397894 AMf AMg
J ABi Qj 397880
H AMv 61 403590 ABi 403656
K AMd 62 397880 Qj 403656 61 403590 AMe AMv
K AMb 63 397860 Qg 403656 62 397880 AMc AMd
J ABj JH 397856
H AMw 63 403656 ABj 403812
K AMa 64 397856 JH 403812 63 403656 AMb AMw
F cZ 30720 40448 59904 75264 60416 74752 59904 75264 57344 458752
H AMx 64 403812 cZ 404338
F cw 30720 40448 59904 75264 60416 74752 88064 270336 30720 40448
H AMy 64 404338 cw 404429
F c7 30720 40448 59904 75264 60416 74752 88064 270336 57344 458752
H AMz 64 404429 c7 404475
F c8 30720 40448 59904 75264 88576 245760 31744 38400 30720 40448
H AM0 64 404475 c8 405086
F c9 30720 40448 59904 75264 88576 245760 31744 38400 57344 458752
H AM1 64 405086 c9 405367
F dD 30720 40448 59904 75264 88576 245760 59904 75264 30720 40448
H AM2 64 405367 dD 405433
F dG 30720 40448 59904 75264 88576 245760 59904 75264 57344 458752
H AM3 64 405433 dG 405464
F dH 30720 40448 59904 75264 88576 245760 88064 270336 30720 40448
H AM4 64 405464 dH 405465
F dK 30720 40448 59904 75264 88576 245760 88064 270336 57344 458752
H AM5 64 405465 dK 405466
F dM 30720 40448 88064 270336 31744 38400 31744 38400 30720 40448
H AM6 64 405466 dM 407902
F dN 30720 40448 88064 270336 31744 38400 31744 38400 57344 458752
H AM7 64 407902 dN 412573
F dO 30720 40448 88064 270336 31744 38400 59904 75264 30720 40448
H AM8 64 412573 dO 415819
F dQ 30720 40448 88064 270336 31744 38400 59904 75264 57344 458752
H AM9 64 415819 dQ 416485
F dV 30720 40448 88064 270336 31744 38400 88064 270336 30720 40448
H ANA 64 416485 dV 416651
F dW 30720 40448 88064 270336 31744 38400 88064 270336 57344 458752
H ANB 64 416651 dW 416722
F dY 30720 40448 88064 270336 60416 74752 31744 38400 30720 40448
H ANC 64 416722 dY 417388
F d5 30720 40448 88064 270336 60416 74752 31744 38400 57344 458752
H ANE 64 417388 d5 417804
F d6 30720 40448 88064 270336 60416 74752 59904 75264 30720 40448
H ANG 64 417804 d6 417895
F d7 30720 40448 88064 270336 60416 74752 59904 75264 57344 458752
H ANH 64 417895 d7 417941
F d8 30720 40448 88064 270336 60416 74752 88064 270336 30720 40448
H ANI 64 417941 d8 417942
F d9 30720 40448 88064 270336 60416 74752 88064 270336 57344 458752
H ANJ 64 417942 d9 417943
F eO 30720 40448 88064 270336 88576 245760 31744 38400 30720 40448
H ANK 64 417943 eO 418044
F eo 30720 40448 88064 270336 88576 245760 31744 38400 57344 458752
H ANL 64 418044 eo 418085
F e9 30720 40448 88064 270336 88576 245760 59904 75264 30720 40448
H ANM 64 418085 e9 418086
F fD 30720 40448 88064 270336 88576 245760 59904 75264 57344 458752
H ANN 64 418086 fD 418087
F fF 30720 40448 88064 270336 88576 245760 88064 270336 30720 40448
H ANO 64 418087 fF 418088
F fG 30720 40448 88064 270336 88576 245760 88064 270336 57344 458752
H ANP 64 418088 fG 418089
F fO 57344 458752 31744 38400 31744 38400 31744 38400 30720 40448
H ANQ 64 418089 fO 418090
F JI 57344 458752 31744 38400 31744 38400 31744 38400 57344 458752
I Qy JI 418090
I Qz Qy 418094
I Q0 Qz 418098
I Q7 Q0 418102
I Q8 Q7 418106
I Q9 Q8 418110
I ABk Q9 418114
H ANZ 57 418118 ABk 422924
J ABl Q9 418114
H ANa 57 422924 ABl 423680
K ANX 58 418114 Q9 423680 57 422924 ANZ ANa
J ABm Q8 418110
H ANb 58 423680 ABm 425016
K ANW 59 418110 Q8 425016 58 423680 ANX ANb
J ABn Q7 418106
H ANc 59 425016 ABn 425287
K ANV 60 418106 Q7 425287 59 425016 ANW ANc
J ABo Q0 418102
H ANd 60 425287 ABo 425953
K ANU 61 418102 Q0 425953 60 425287 ANV ANd
J ABp Qz 418098
H ANe 61 425953 ABp 425974
K ANT 62 418098 Qz 425974 61 425953 ANU ANe
J ABq Qy 418094
H ANf 62 425974 ABq 425975
K ANS 63 418094 Qy 425975 62 425974 ANT ANf
J ABr JI 418090
H ANg 63 425975 ABr 425976
K ANR 64 418090 JI 425976 63 425975 ANS ANg
F fq 57344 458752 31744 38400 31744 38400 59904 75264 30720 40448
H ANh 64 425976 fq 425977
F JK 57344 458752 31744 38400 31744 38400 59904 75264 57344 458752
I RB JK 425977
I RD RB 425981
I RI RD 425985
I RJ RI 425989
I RK RJ 425993
I RM RK 425997
I RO RM 426001
I RQ RO 426005
I ABs RQ 426009
H ANr 55 426013 ABs 426609
J RU RQ 426009
I RV RU 426609
I RW RV 426613
I ABt RW 426617
H ANv 52 426621 ABt 426847
J RY RW 426617
I RZ RY 426847
I ABu RZ 426851
H ANy 50 426855 ABu 426926
J Ra RZ 426851
I Rb Ra 426926
I ABv Rb 426930
H AN1 48 426934 ABv 427070
J Rd Rb 426930
I Rg Rd 427070
I ABw Rg 427074
H AN4 46 427078 ABw 427319
J Rh Rg 427074
I Ri Rh 427319
I Rj Ri 427323
I Rk Rj 427327
I ABx Rk 427331
H AN9 42 427335 ABx 431731
J ABy Rk 427331
H AOA 42 431731 ABy 432887
K AN8 43 427331 Rk 432887 42 431731 AN9 AOA
J ABz Rj 427327
H AOB 43 432887 ABz 433108
K AN7 44 427327 Rj 433108 43 432887 AN8 AOB
J AB0 Ri 427323
H AOC 44 433108 AB0 434849
K AN6 45 427323 Ri 434849 44 433108 AN7 AOC
J AB1 Rh 427319
H AOD 45 434849 AB1 437225
K AN5 46 427319 Rh 437225 45 434849 AN6 AOD
K AN3 47 427074 Rg 437225 46 427319 AN4 AN5
J AB2 Rd 427070
H AOE 47 437225 AB2 437311
K AN2 48 427070 Rd 437311 47 437225 AN3 AOE
K AN0 49 426930 Rb 437311 48 427070 AN1 AN2
J AB3 Ra 426926
H AOF 49 437311 AB3 437432
K ANz 50 426926 Ra 437432 49 437311 AN0 AOF
K ANx 51 426851 RZ 437432 50 426926 ANy ANz
J AB6 RY 426847
H AOG 51 437432 AB6 437493
K ANw 52 426847 RY 437493 51 437432 ANx AOG
K ANu 53 426617 RW 437493 52 426847 ANv ANw
J AB7 RV 426613
H AOH 53 437493 AB7 437539
K ANt 54 426613 RV 437539 53 437493 ANu AOH
J AB8 RU 426609
H AOI 54 437539 AB8 438995
K ANs 55 426609 RU 438995 54 437539 ANt AOI
K ANq 56 426009 RQ 438995 55 426609 ANr ANs
J AB9 RO 426005
H AOJ 56 438995 AB9 439026
K ANp 57 426005 RO 439026 56 438995 ANq AOJ
J ACA RM 426001
H AOK 57 439026 ACA 439467
K ANo 58 426001 RM 439467 57 439026 ANp AOK
J ACE RK 425997
H AOL 58 439467 ACE 440013
K ANn 59 425997 RK 440013 58 439467 ANo AOL
J ACG RJ 425993
H AOM 59 440013 ACG 440074
K ANm 60 425993 RJ 440074 59 440013 ANn AOM
J ACH RI 425989
H AON 60 440074 ACH 440155
K ANl 61 425989 RI 440155 60 440074 ANm AON
J ACI RD 425985
H AOO 61 440155 ACI 440171
K ANk 62 425985 RD 440171 61 440155 ANl AOO
J ACJ RB 425981
H AOP 62 440171 ACJ 440172
K ANj 63 425981 RB 440172 62 440171 ANk AOP
J ACK JK 425977
H AOQ 63 440172 ACK 440173
K ANi 64 425977 JK 440173 63 440172 ANj AOQ
F f5 57344 458752 31744 38400 31744 38400 88064 270336 30720 40448
H AOR 64 440173 f5 440174
F f6 57344 458752 31744 38400 31744 38400 88064 270336 57344 458752
H AOS 64 440174 f6 441380
F f7 57344 458752 31744 38400 60416 74752 31744 38400 30720 40448
H AOT 64 441380 f7 441381
F JL 57344 458752 31744 38400 60416 74752 31744 38400 57344 458752
I Ro JL 441381
I Rq Ro 441385
I Rr Rq 441389
I Ru Rr 441393
I Ry Ru 441397
I Rz Ry 441401
I R4 Rz 441405
I R5 R4 441409
I ACN R5 441413
H AOd 55 441417 ACN 442138
J R6 R5 441413
I R7 R6 442138
I R8 R7 442142
I ACO R8 442146
H AOh 52 442150 ACO 442581
J R9 R8 442146
I SD R9 442581
I ACP SD 442585
H AOk 50 442589 ACP 442955
J SF SD 442585
I SH SF 442955
I ACQ SH 442959
H AOn 48 442963 ACQ 443159
J SJ SH 442959
I SK SJ 443159
I ACR SK 443163
H AOq 46 443167 ACR 443328
J SM SK 443163
I SN SM 443328
I SO SN 443332
I SY SO 443336
I SZ SY 443340
I ACS SZ 443344
H AOw 41 443348 ACS 444279
J Sb SZ 443344
I Se Sb 444279
I ACT Se 444283
H AOz 39 444287 ACT 445538
J Sh Se 444283
I ACU Sh 445538
H AO1 38 445542 ACU 450288
J Sj Sh 445538
I ACV Sj 450288
H AO3 37 450292 ACV 454623
J ACW Sj 450288
H AO4 37 454623 ACW 457904
K AO2 38 450288 Sj 457904 37 454623 AO3 AO4
K AO0 39 445538 Sh 457904 38 450288 AO1 AO2
K AOy 40 444283 Se 457904 39 445538 AOz AO0
J ACX Sb 444279
H AO5 40 457904 ACX 458010
K AOx 41 444279 Sb 458010 40 457904 AOy AO5
K AOv 42 443344 SZ 458010 41 444279 AOw AOx
J Sl SY 443340
I Sz Sl 458010
I ACY Sz 458014
H AO8 40 458018 ACY 460514
J S9 Sz 458014
I TA S9 460514
I ACZ TA 460518
H APB 38 460522 ACZ 460978
J TD TA 460518
I ACa TD 460978
H APD 37 460982 ACa 465298
J ACb TD 460978
H APE 37 465298 ACb 468524
K APC 38 460978 TD 468524 37 465298 APD APE
K APA 39 460518 TA 468524 38 460978 APB APC
J TI S9 460514
I ACc TI 468524
H APG 38 468528 ACc 471909
J ACd TI 468524
H APH 38 471909 ACd 473780
K APF 39 468524 TI 473780 38 471909 APG APH
K AO9 40 460514 S9 473780 39 468524 APA APF
K AO7 41 458014 Sz 473780 40 460514 AO8 AO9
J ACe Sl 458010
H APJ 41 473780 ACe 473921
K AO6 42 458010 Sl 473921 41 473780 AO7 APJ
K AOu 43 443340 SY 473921 42 458010 AOv AO6
J ACf SO 443336
H APK 43 473921 ACf 474182
K AOt 44 443336 SO 474182 43 473921 AOu APK
J TK SN 443332
I TN TK 474182
I TP TN 474186
I TQ TP 474190
I ACg TQ 474194
H APP 40 474198 ACg 476979
J TW TQ 474194
I Tj TW 476979
I ACh Tj 476983
H APS 38 476987 ACh 478423
J Tv Tj 476983
I Tz Tv 478423
I T7 Tz 478427
I ACi T7 478431
H APW 35 478435 ACi 478786
J T8 T7 478431
I ACj T8 478786
H APY 34 478790 ACj 481231
J ACk T8 478786
H APZ 34 481231 ACk 485022
K APX 35 478786 T8 485022 34 481231 APY APZ
K APV 36 478431 T7 485022 35 478786 APW APX
J UA Tz 478427
I ACl UA 485022
H APb 35 485026 ACl 486507
J ACm UA 485022
H APc 35 486507 ACm 490873
K APa 36 485022 UA 490873 35 486507 APb APc
K APU 37 478427 Tz 490873 36 485022 APV APa
J ACn Tv 478423
H APd 37 490873 ACn 494574
K APT 38 478423 Tv 494574 37 490873 APU APd
K APR 39 476983 Tj 494574 38 478423 APS APT
J UC TW 476979
I UE UC 494574
I ACo UE 494578
H APg 37 494582 ACo 497858
J ACp UE 494578
H APh 37 497858 ACp 501669
K APf 38 494578 UE 501669 37 497858 APg APh
J ACq UC 494574
H APi 38 501669 ACq 503475
K APe 39 494574 UC 503475 38 501669 APf APi
K APQ 40 476979 TW 503475 39 494574 APR APe
K APO 41 474194 TQ 503475 40 476979 APP APQ
J UG TP 474190
I UH UG 503475
I ACr UH 503479
H APl 39 503483 ACr 504754
J UJ UH 503479
I UK UJ 504754
I UL UK 504758
I ACs UL 504762
H APp 36 504766 ACs 505217
J ACt UL 504762
H APq 36 505217 ACt 509913
K APo 37 504762 UL 509913 36 505217 APp APq
J ACu UK 504758
H APr 37 509913 ACu 512564
K APn 38 504758 UK 512564 37 509913 APo APr
J ACv UJ 504754
H APs 38 512564 ACv 514485
K APm 39 504754 UJ 514485 38 512564 APn APs
K APk 40 503479 UH 514485 39 504754 APl APm
J ACw UG 503475
H APt 40 514485 ACw 519306
K APj 41 503475 UG 519306 40 514485 APk APt
K APN 42 474190 TP 519306 41 503475 APO APj
J ACx TN 474186
H APu 42 519306 ACx 519647
K APM 43 474186 TN 519647 42 519306 APN APu
J ACy TK 474182
H APv 43 519647 ACy 519908
K APL 44 474182 TK 519908 43 519647 APM APv
K AOs 45 443332 SN 519908 44 474182 AOt APL
J ACz SM 443328
H APw 45 519908 ACz 522344
K AOr 46 443328 SM 522344 45 519908 AOs APw
K AOp 47 443163 SK 522344 46 443328 AOq AOr
J AC0 SJ 443159
H APx 47 522344 AC0 522765
K AOo 48 443159 SJ 522765 47 522344 AOp APx
K AOm 49 442959 SH 522765 48 443159 AOn AOo
J AC1 SF 442955
H APy 49 522765 AC1 523266
K AOl 50 442955 SF 523266 49 522765 AOm APy
K AOj 51 442585 SD 523266 50 442955 AOk AOl
J AC2 R9 442581
H APz 51 523266 AC2 523307
K AOi 52 442581 R9 523307 51 523266 AOj APz
K AOg 53 442146 R8 523307 52 442581 AOh AOi
J AC3 R7 442142
H AP0 53 523307 AC3 523328
K AOf 54 442142 R7 523328 53 523307 AOg AP0
J AC4 R6 442138
H AP1 54 523328 AC4 526444
K AOe 55 442138 R6 526444 54 523328 AOf AP1
K AOc 56 441413 R5 526444 55 442138 AOd AOe
J AC5 R4 441409
H AP2 56 526444 AC5 526480
K AOb 57 441409 R4 526480 56 526444 AOc AP2
J AC6 Rz 441405
H AP3 57 526480 AC6 526901
K AOa 58 441405 Rz 526901 57 526480 AOb AP3
J AC7 Ry 441401
H AP4 58 526901 AC7 527407
K AOZ 59 441401 Ry 527407 58 526901 AOa AP4
J AC8 Ru 441397
H AP5 59 527407 AC8 527443
K AOY 60 441397 Ru 527443 59 527407 AOZ AP5
J AC9 Rr 441393
H AP6 60 527443 AC9 527514
K AOX 61 441393 Rr 527514 60 527443 AOY AP6
J ADA Rq 441389
H AP7 61 527514 ADA 527530
K AOW 62 441389 Rq 527530 61 527514 AOX AP7
J ADB Ro 441385
H AP8 62 527530 ADB 527531
K AOV 63 441385 Ro 527531 62 527530 AOW AP8
J ADC JL 441381
H AP9 63 527531 ADC 527532
K AOU 64 441381 JL 527532 63 527531 AOV AP9
F f8 57344 458752 31744 38400 60416 74752 59904 75264 30720 40448
H AQA 64 527532 f8 527533
F f9 57344 458752 31744 38400 60416 74752 59904 75264 57344 458752
H AQB 64 527533 f9 531914
F gC 57344 458752 31744 38400 60416 74752 88064 270336 30720 40448
H AQC 64 531914 gC 531915
F gI 57344 458752 31744 38400 60416 74752 88064 270336 57344 458752
H AQD 64 531915 gI 532016
F gJ 57344 458752 31744 38400 88576 245760 31744 38400 30720 40448
H AQE 64 532016 gJ 532017
F gN 57344 458752 31744 38400 88576 245760 31744 38400 57344 458752
H AQF 64 532017 gN 533358
F gO 57344 458752 31744 38400 88576 245760 59904 75264 30720 40448
H AQG 64 533358 gO 533359
F gP 57344 458752 31744 38400 88576 245760 59904 75264 57344 458752
H AQH 64 533359 gP 533450
F gQ 57344 458752 31744 38400 88576 245760 88064 270336 30720 40448
H AQI 64 533450 gQ 533451
F gT 57344 458752 31744 38400 88576 245760 88064 270336 57344 458752
H AQJ 64 533451 gT 533452
F gW 57344 458752 59904 75264 31744 38400 31744 38400 30720 40448
H AQK 64 533452 gW 533453
F JM 57344 458752 59904 75264 31744 38400 31744 38400 57344 458752
I UO JM 533453
I UQ UO 533457
I UR UQ 533461
I UZ UR 533465
I Ud UZ 533469
I Ue Ud 533473
I Uh Ue 533477
I Uj Uh 533481
I ADE Uj 533485
H AQU 55 533489 ADE 533965
J Um Uj 533485
I Uq Um 533965
I Ur Uq 533969
I ADF Ur 533973
H AQY 52 533977 ADF 534263
J Uv Ur 533973
I Uw Uv 534263
I ADG Uw 534267
H AQb 50 534271 ADG 534342
J Uz Uw 534267
I U3 Uz 534342
I ADH U3 534346
H AQe 48 534350 ADH 534486
J U5 U3 534346
I U6 U5 534486
I ADI U6 534490
H AQh 46 534494 ADI 534735
J U7 U6 534490
I U8 U7 534735
I VA U8 534739
I ADJ VA 534743
H AQl 43 534747 ADJ 539518
J ADK VA 534743
H AQm 43 539518 ADK 539749
K AQk 44 534743 VA 539749 43 539518 AQl AQm
J ADL U8 534739
H AQn 44 539749 ADL 541305
K AQj 45 534739 U8 541305 44 539749 AQk AQn
J ADM U7 534735
H AQo 45 541305 ADM 543496
K AQi 46 534735 U7 543496 45 541305 AQj AQo
K AQg 47 534490 U6 543496 46 534735 AQh AQi
J ADN U5 534486
H AQp 47 543496 ADN 543582
K AQf 48 534486 U5 543582 47 543496 AQg AQp
K AQd 49 534346 U3 543582 48 534486 AQe AQf
J ADO Uz 534342
H AQq 49 543582 ADO 543703
K AQc 50 534342 Uz 543703 49 543582 AQd AQq
K AQa 51 534267 Uw 543703 50 534342 AQb AQc
J ADP Uv 534263
H AQr 51 543703 ADP 543764
K AQZ 52 534263 Uv 543764 51 543703 AQa AQr
K AQX 53 533973 Ur 543764 52 534263 AQY AQZ
J ADQ Uq 533969
H AQs 53 543764 ADQ 543785
K AQW 54 533969 Uq 543785 53 543764 AQX AQs
J ADR Um 533965
H AQt 54 543785 ADR 545451
K AQV 55 533965 Um 545451 54 543785 AQW AQt
K AQT 56 533485 Uj 545451 55 533965 AQU AQV
J ADS Uh 533481
H AQu 56 545451 ADS 545532
K AQS 57 533481 Uh 545532 56 545451 AQT AQu
J ADT Ue 533477
H AQv 57 545532 ADT 545988
K AQR 58 533477 Ue 545988 57 545532 AQS AQv
J ADU Ud 533473
H AQw 58 545988 ADU 546519
K AQQ 59 533473 Ud 546519 58 545988 AQR AQw
J ADV UZ 533469
H AQx 59 546519 ADV 546580
K AQP 60 533469 UZ 546580 59 546519 AQQ AQx
J ADW UR 533465
H AQy 60 546580 ADW 546661
K AQO 61 533465 UR 546661 60 546580 AQP AQy
J ADX UQ 533461
H AQz 61 546661 ADX 546677
K AQN 62 533461 UQ 546677 61 546661 AQO AQz
J ADY UO 533457
H AQ0 62 546677 ADY 546678
K AQM 63 533457 UO 546678 62 546677 AQN AQ0
J ADZ JM 533453
H AQ1 63 546678 ADZ 546679
K AQL 64 533453 JM 546679 63 546678 AQM AQ1
F gX 57344 458752 59904 75264 31744 38400 59904 75264 30720 40448
H AQ2 64 546679 gX 546680
F JN 57344 458752 59904 75264 31744 38400 59904 75264 57344 458752
I VE JN 546680
I VF VE 546684
I VG VF 546688
I VJ VG 546692
I VK VJ 546696
I VL VK 546700
I VN VL 546704
I VO VN 546708
I ADa VO 546712
H ARC 55 546716 ADa 546802
J VQ VO 546712
I VR VQ 546802
I VT VR 546806
I ADb VT 546810
H ARH 52 546814 ADb 546875
J VY VT 546810
I VZ VY 546875
I ADc VZ 546879
H ARK 50 546883 ADc 546884
J Vc VZ 546879
I Vd Vc 546884
I ADd Vd 546888
H ARN 48 546892 ADd 546893
J Ve Vd 546888
I Vf Ve 546893
I ADe Vf 546897
H ARQ 46 546901 ADe 546902
J Vg Vf 546897
I Vh Vg 546902
I ADf Vh 546906
H ART 44 546910 ADf 547036
J Vi Vh 546906
I ADg Vi 547036
H ARV 43 547040 ADg 549961
J ADh Vi 547036
H ARW 43 549961 ADh 552067
K ARU 44 547036 Vi 552067 43 549961 ARV ARW
K ARS 45 546906 Vh 552067 44 547036 ART ARU
J ADi Vg 546902
H ARX 45 552067 ADi 555523
K ARR 46 546902 Vg 555523 45 552067 ARS ARX
K ARP 47 546897 Vf 555523 46 546902 ARQ ARR
J ADj Ve 546893
H ARY 47 555523 ADj 555679
K ARO 48 546893 Ve 555679 47 555523 ARP ARY
K ARM 49 546888 Vd 555679 48 546893 ARN ARO
J ADk Vc 546884
H ARZ 49 555679 ADk 555725
K ARL 50 546884 Vc 555725 49 555679 ARM ARZ
K ARJ 51 546879 VZ 555725 50 546884 ARK ARL
J ADl VY 546875
H ARa 51 555725 ADl 555781
K ARI 52 546875 VY 555781 51 555725 ARJ ARa
K ARG 53 546810 VT 555781 52 546875 ARH ARI
J ADm VR 546806
H ARb 53 555781 ADm 555797
K ARF 54 546806 VR 555797 53 555781 ARG ARb
J ADn VQ 546802
H ARc 54 555797 ADn 555998
K ARD 55 546802 VQ 555998 54 555797 ARF ARc
K ARB 56 546712 VO 555998 55 546802 ARC ARD
J ADo VN 546708
H ARd 56 555998 ADo 556029
K ARA 57 546708 VN 556029 56 555998 ARB ARd
J ADp VL 546704
H ARe 57 556029 ADp 556070
K AQ9 58 546704 VL 556070 57 556029 ARA ARe
J ADq VK 546700
H ARf 58 556070 ADq 556131
K AQ8 59 546700 VK 556131 58 556070 AQ9 ARf
J ADr VJ 546696
H ARg 59 556131 ADr 556147
K AQ7 60 546696 VJ 556147 59 556131 AQ8 ARg
J ADs VG 546692
H ARh 60 556147 ADs 556148
K AQ6 61 546692 VG 556148 60 556147 AQ7 ARh
J ADt VF 546688
H ARi 61 556148 ADt 556149
K AQ5 62 546688 VF 556149 61 556148 AQ6 ARi
J ADu VE 546684
H ARj 62 556149 ADu 556150
K AQ4 63 546684 VE 556150 62 556149 AQ5 ARj
J ADv JN 546680
H ARk 63 556150 ADv 556151
K AQ3 64 546680 JN 556151 63 556150 AQ4 ARk
F gY 57344 458752 59904 75264 31744 38400 88064 270336 30720 40448
H ARl 64 556151 gY 556152
F gd 57344 458752 59904 75264 31744 38400 88064 270336 57344 458752
H ARm 64 556152 gd 556263
F g5 57344 458752 59904 75264 60416 74752 31744 38400 30720 40448
H ARn 64 556263 g5 556264
F g6 57344 458752 59904 75264 60416 74752 31744 38400 57344 458752
H ARo 64 556264 g6 560440
F g7 57344 458752 59904 75264 60416 74752 59904 75264 30720 40448
H ARp 64 560440 g7 560441
F g8 57344 458752 59904 75264 60416 74752 59904 75264 57344 458752
H ARq 64 560441 g8 560532
F g9 57344 458752 59904 75264 60416 74752 88064 270336 30720 40448
H ARr 64 560532 g9 560533
F iJ 57344 458752 59904 75264 60416 74752 88064 270336 57344 458752
H ARs 64 560533 iJ 560534
F iO 57344 458752 59904 75264 88576 245760 31744 38400 30720 40448
H ARt 64 560534 iO 560535
F iQ 57344 458752 59904 75264 88576 245760 31744 38400 57344 458752
H ARu 64 560535 iQ 560626
F iW 57344 458752 59904 75264 88576 245760 59904 75264 30720 40448
H ARv 64 560626 iW 560627
F iw 57344 458752 59904 75264 88576 245760 59904 75264 57344 458752
H ARw 64 560627 iw 560628
F i6 57344 458752 59904 75264 88576 245760 88064 270336 30720 40448
H ARx 64 560628 i6 560629
F i7 57344 458752 59904 75264 88576 245760 88064 270336 57344 458752
H ARy 64 560629 i7 560630
F i9 57344 458752 88064 270336 31744 38400 31744 38400 30720 40448
H ARz 64 560630 i9 560631
F jA 57344 458752 88064 270336 31744 38400 31744 38400 57344 458752
H AR0 64 560631 jA 561792
F jB 57344 458752 88064 270336 31744 38400 59904 75264 30720 40448
H AR1 64 561792 jB 561793
F jC 57344 458752 88064 270336 31744 38400 59904 75264 57344 458752
H AR2 64 561793 jC 561904
F jD 57344 458752 88064 270336 31744 38400 88064 270336 30720 40448
H AR3 64 561904 jD 561905
F jE 57344 458752 88064 270336 31744 38400 88064 270336 57344 458752
H AR4 64 561905 jE 561906
F jF 57344 458752 88064 270336 60416 74752 31744 38400 30720 40448
H AR5 64 561906 jF 561907
F jG 57344 458752 88064 270336 60416 74752 31744 38400 57344 458752
H AR6 64 561907 jG 562008
F jI 57344 458752 88064 270336 60416 74752 59904 75264 30720 40448
H AR7 64 562008 jI 562009
F jK 57344 458752 88064 270336 60416 74752 59904 75264 57344 458752
H AR8 64 562009 jK 562010
F jL 57344 458752 88064 270336 60416 74752 88064 270336 30720 40448
H AR9 64 562010 jL 562011
F jM 57344 458752 88064 270336 60416 74752 88064 270336 57344 458752
H ASB 64 562011 jM 562012
F jN 57344 458752 88064 270336 88576 245760 31744 38400 30720 40448
H ASC 64 562012 jN 562013
F jO 57344 458752 88064 270336 88576 245760 31744 38400 57344 458752
H ASD 64 562013 jO 562014
F jP 57344 458752 88064 270336 88576 245760 59904 75264 30720 40448
H ASE 64 562014 jP 562015
F jQ 57344 458752 88064 270336 88576 245760 59904 75264 57344 458752
H ASF 64 562015 jQ 562016
F jR 57344 458752 88064 270336 88576 245760 88064 270336 30720 40448
H ASG 64 562016 jR 562017
F jS 57344 458752 88064 270336 88576 245760 88064 270336 57344 458752
H ASH 64 562017 jS 562018
theorem AFT : (AG.Aw cover0).length = 2 := by decide +kernel
theorem AFU : (AG.Aw cover1).length = 3 := by decide +kernel
theorem AFV : (AG.Aw cover2).length = 3 := by decide +kernel
theorem AFW : (AG.Aw cover3).length = 3 := by decide +kernel
theorem AFX : (AG.Aw cover4).length = 2 := by decide +kernel
set_option hygiene false in
local macro "L " x0:ident x1:num x2:num x3:num x4:num x5:num x6:num x7:num x8:ident x9:ident : command => `(command|
theorem $x0 : AG.walk table bits 64 $x1 (AG.BJ (AG.Aw cover0) (AG.Aw cover1) (AG.Aw cover2) (AG.Aw cover3) (AG.Aw cover4) $x2 $x3 $x4 $x5 $x6) = some $x7 := by
  rw [show AG.BJ (AG.Aw cover0) (AG.Aw cover1) (AG.Aw cover2) (AG.Aw cover3) (AG.Aw cover4) $x2 $x3 $x4 $x5 $x6 = $x8 from by decide +kernel]; exact $x9)
L jV 0 0 0 0 0 0 2051 bx0 wk0
L jW 2051 0 0 0 0 1 7807 ZL wk1
L jX 7807 0 0 0 1 0 14958 ZM wk8
L jY 14958 0 0 0 1 1 22954 WA ASe
L jZ 22954 0 0 0 2 0 25665 pQ ASr
L jc 25665 0 0 0 2 1 27411 pU ASs
L jd 27411 0 0 1 0 0 35337 WB ASt
L je 35337 0 0 1 0 1 54808 WC AS6
L jf 54808 0 0 1 1 0 65914 WD ATi
L jg 65914 0 0 1 1 1 69865 bF AFz
L jo 69865 0 0 1 2 0 70596 bR AF0
L jt 70596 0 0 1 2 1 70872 bU AF1
L ju 70872 0 0 2 0 0 73683 bY AF2
L jv 73683 0 0 2 0 1 76069 bZ AF3
L jw 76069 0 0 2 1 0 76705 b9 AF4
L jz 76705 0 0 2 1 1 76946 cD AF5
L j3 76946 0 0 2 2 0 77047 cE AF6
L j4 77047 0 0 2 2 1 77088 cO AF7
L j5 77088 0 1 0 0 0 83504 Iz AF8
L j6 83504 0 1 0 0 1 112385 I7 AGJ
L j7 112385 0 1 0 1 0 252186 I8 AG3
L j8 252186 0 1 0 1 1 323087 I9 AJO
L j9 323087 0 1 0 2 0 326378 cP AKq
L kA 326378 0 1 0 2 1 326984 cV AKr
L kB 326984 0 1 1 0 0 336040 JE AKs
L kC 336040 0 1 1 0 1 397856 JG ALI
L kD 397856 0 1 1 1 0 403812 JH AMa
L kF 403812 0 1 1 1 1 404338 cZ AMx
L kG 404338 0 1 1 2 0 404429 cw AMy
L kJ 404429 0 1 1 2 1 404475 c7 AMz
L kL 404475 0 1 2 0 0 405086 c8 AM0
L kM 405086 0 1 2 0 1 405367 c9 AM1
L kN 405367 0 1 2 1 0 405433 dD AM2
L kO 405433 0 1 2 1 1 405464 dG AM3
L kP 405464 0 1 2 2 0 405465 dH AM4
L kQ 405465 0 1 2 2 1 405466 dK AM5
L kR 405466 0 2 0 0 0 407902 dM AM6
L kS 407902 0 2 0 0 1 412573 dN AM7
L kT 412573 0 2 0 1 0 415819 dO AM8
L kV 415819 0 2 0 1 1 416485 dQ AM9
L kW 416485 0 2 0 2 0 416651 dV ANA
L kZ 416651 0 2 0 2 1 416722 dW ANB
L kd 416722 0 2 1 0 0 417388 dY ANC
L ko 417388 0 2 1 0 1 417804 d5 ANE
L kq 417804 0 2 1 1 0 417895 d6 ANG
L k5 417895 0 2 1 1 1 417941 d7 ANH
L k6 417941 0 2 1 2 0 417942 d8 ANI
L k7 417942 0 2 1 2 1 417943 d9 ANJ
L k8 417943 0 2 2 0 0 418044 eO ANK
L k9 418044 0 2 2 0 1 418085 eo ANL
L lA 418085 0 2 2 1 0 418086 e9 ANM
L lB 418086 0 2 2 1 1 418087 fD ANN
L lC 418087 0 2 2 2 0 418088 fF ANO
L lD 418088 0 2 2 2 1 418089 fG ANP
L lG 418089 1 0 0 0 0 418090 fO ANQ
L lH 418090 1 0 0 0 1 425976 JI ANR
L lJ 425976 1 0 0 1 0 425977 fq ANh
L lK 425977 1 0 0 1 1 440173 JK ANi
L lN 440173 1 0 0 2 0 440174 f5 AOR
L lO 440174 1 0 0 2 1 441380 f6 AOS
L lP 441380 1 0 1 0 0 441381 f7 AOT
L lQ 441381 1 0 1 0 1 527532 JL AOU
L lU 527532 1 0 1 1 0 527533 f8 AQA
L lV 527533 1 0 1 1 1 531914 f9 AQB
L lW 531914 1 0 1 2 0 531915 gC AQC
L lX 531915 1 0 1 2 1 532016 gI AQD
L lY 532016 1 0 2 0 0 532017 gJ AQE
L lZ 532017 1 0 2 0 1 533358 gN AQF
L l8 533358 1 0 2 1 0 533359 gO AQG
L l9 533359 1 0 2 1 1 533450 gP AQH
L mC 533450 1 0 2 2 0 533451 gQ AQI
L mD 533451 1 0 2 2 1 533452 gT AQJ
L mJ 533452 1 1 0 0 0 533453 gW AQK
L mL 533453 1 1 0 0 1 546679 JM AQL
L mO 546679 1 1 0 1 0 546680 gX AQ2
L m4 546680 1 1 0 1 1 556151 JN AQ3
L m5 556151 1 1 0 2 0 556152 gY ARl
L m6 556152 1 1 0 2 1 556263 gd ARm
L m7 556263 1 1 1 0 0 556264 g5 ARn
L m8 556264 1 1 1 0 1 560440 g6 ARo
L m9 560440 1 1 1 1 0 560441 g7 ARp
L nC 560441 1 1 1 1 1 560532 g8 ARq
L nD 560532 1 1 1 2 0 560533 g9 ARr
L nF 560533 1 1 1 2 1 560534 iJ ARs
L nI 560534 1 1 2 0 0 560535 iO ARt
L nJ 560535 1 1 2 0 1 560626 iQ ARu
L nL 560626 1 1 2 1 0 560627 iW ARv
L nO 560627 1 1 2 1 1 560628 iw ARw
L nP 560628 1 1 2 2 0 560629 i6 ARx
L nQ 560629 1 1 2 2 1 560630 i7 ARy
L nS 560630 1 2 0 0 0 560631 i9 ARz
L nT 560631 1 2 0 0 1 561792 jA AR0
L nU 561792 1 2 0 1 0 561793 jB AR1
L nV 561793 1 2 0 1 1 561904 jC AR2
L nW 561904 1 2 0 2 0 561905 jD AR3
L nY 561905 1 2 0 2 1 561906 jE AR4
L nZ 561906 1 2 1 0 0 561907 jF AR5
L n5 561907 1 2 1 0 1 562008 jG AR6
L n6 562008 1 2 1 1 0 562009 jI AR7
L n7 562009 1 2 1 1 1 562010 jK AR8
L n8 562010 1 2 1 2 0 562011 jL AR9
L n9 562011 1 2 1 2 1 562012 jM ASB
L oD 562012 1 2 2 0 0 562013 jN ASC
L oF 562013 1 2 2 0 1 562014 jO ASD
L oG 562014 1 2 2 1 0 562015 jP ASE
L oH 562015 1 2 2 1 1 562016 jQ ASF
L oI 562016 1 2 2 2 0 562017 jR ASG
L oK 562017 1 2 2 2 1 562018 jS ASH
theorem AFY : ∀ i0 i1 i2 i3 i4, i0 < (AG.Aw cover0).length → i1 < (AG.Aw cover1).length → i2 < (AG.Aw cover2).length → i3 < (AG.Aw cover3).length → i4 < (AG.Aw cover4).length →
    ∃ pos pos', AG.walk table bits 64 pos (AG.BJ (AG.Aw cover0) (AG.Aw cover1) (AG.Aw cover2) (AG.Aw cover3) (AG.Aw cover4) i0 i1 i2 i3 i4) = some pos' := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [AFT] at hi0
  rw [AFU] at hi1
  rw [AFV] at hi2
  rw [AFW] at hi3
  rw [AFX] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, jV⟩
  | 0, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, jW⟩
  | 0, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, jX⟩
  | 0, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, jY⟩
  | 0, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, jZ⟩
  | 0, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, jc⟩
  | 0, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, jd⟩
  | 0, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, je⟩
  | 0, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, jf⟩
  | 0, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, jg⟩
  | 0, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, jo⟩
  | 0, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, jt⟩
  | 0, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, ju⟩
  | 0, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, jv⟩
  | 0, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, jw⟩
  | 0, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, jz⟩
  | 0, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, j3⟩
  | 0, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, j4⟩
  | 0, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, j5⟩
  | 0, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, j6⟩
  | 0, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, j7⟩
  | 0, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, j8⟩
  | 0, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, j9⟩
  | 0, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, kA⟩
  | 0, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, kB⟩
  | 0, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, kC⟩
  | 0, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, kD⟩
  | 0, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, kF⟩
  | 0, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, kG⟩
  | 0, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, kJ⟩
  | 0, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, kL⟩
  | 0, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, kM⟩
  | 0, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, kN⟩
  | 0, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, kO⟩
  | 0, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, kP⟩
  | 0, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, kQ⟩
  | 0, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, kR⟩
  | 0, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, kS⟩
  | 0, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, kT⟩
  | 0, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, kV⟩
  | 0, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, kW⟩
  | 0, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, kZ⟩
  | 0, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, kd⟩
  | 0, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, ko⟩
  | 0, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, kq⟩
  | 0, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, k5⟩
  | 0, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, k6⟩
  | 0, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, k7⟩
  | 0, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, k8⟩
  | 0, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, k9⟩
  | 0, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, lA⟩
  | 0, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, lB⟩
  | 0, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, lC⟩
  | 0, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, lD⟩
  | 1, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, lG⟩
  | 1, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, lH⟩
  | 1, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, lJ⟩
  | 1, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, lK⟩
  | 1, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, lN⟩
  | 1, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, lO⟩
  | 1, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, lP⟩
  | 1, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, lQ⟩
  | 1, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, lU⟩
  | 1, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, lV⟩
  | 1, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, lW⟩
  | 1, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, lX⟩
  | 1, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, lY⟩
  | 1, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, lZ⟩
  | 1, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, l8⟩
  | 1, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, l9⟩
  | 1, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, mC⟩
  | 1, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, mD⟩
  | 1, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, mJ⟩
  | 1, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, mL⟩
  | 1, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, mO⟩
  | 1, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, m4⟩
  | 1, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, m5⟩
  | 1, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, m6⟩
  | 1, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, m7⟩
  | 1, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, m8⟩
  | 1, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, m9⟩
  | 1, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, nC⟩
  | 1, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, nD⟩
  | 1, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, nF⟩
  | 1, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, nI⟩
  | 1, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, nJ⟩
  | 1, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, nL⟩
  | 1, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, nO⟩
  | 1, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, nP⟩
  | 1, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, nQ⟩
  | 1, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, nS⟩
  | 1, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, nT⟩
  | 1, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, nU⟩
  | 1, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, nV⟩
  | 1, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, nW⟩
  | 1, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, nY⟩
  | 1, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, nZ⟩
  | 1, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, n5⟩
  | 1, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, n6⟩
  | 1, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, n7⟩
  | 1, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, n8⟩
  | 1, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, n9⟩
  | 1, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, oD⟩
  | 1, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, oF⟩
  | 1, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, oG⟩
  | 1, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, oH⟩
  | 1, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, oI⟩
  | 1, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, oK⟩
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)
theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (AG.cN : ℝ) / AG.SA ≤ AG.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  AG.qC table qz bits 64 cover0 cover1 cover2 cover3 cover4 458752 270336 245760 270336 458752
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) oW oX oY oZ oc (by decide +kernel) AFY
end AH.Bridge.AN.Ak
noncomputable section
namespace Aa
open Filter
open Zeta23 Zeta23.ThmD AH.Bridge AH.AY
theorem ZR : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [inv_eq_one_div, div_eq_div_iff hne two_ne_zero, one_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
theorem YG : HD 1 = 3 / 2 - AN.gam := by
  rw [HD_one, ZR]
  unfold AN.gam
  ring
theorem HD_one_bounds :
    (6725006982 / 10000000000 : ℝ) ≤ HD 1 ∧ HD 1 ≤ 6725007093 / 10000000000 := by
  have hg := AN.Ee
  rw [YG]
  norm_num at hg ⊢
  constructor <;> linarith [hg.1, hg.2]
theorem cStar_one_eq_cMT : Zeta23.ThmD.cStar 1 = cMT := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold cMT Zeta23.ThmD.theta
  rfl
theorem Jt (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩
end Aa
end
noncomputable section
namespace Aa
open Filter
open Zeta23 Zeta23.ThmD AH.Bridge AH.AY AH.Bridge.AN
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
def bW : Fin 5 → ℝ
  | 0 => (24896 : ℝ) / 100000000
  | 1 => (42034 : ℝ) / 100000000
  | 2 => (46137 : ℝ) / 100000000
  | 3 => (42034 : ℝ) / 100000000
  | 4 => (24896 : ℝ) / 100000000
def WW : WCert 6 := ⟨aW, bW⟩
set_option hygiene false in
local macro "M " x0:ident x1:num x2:num : command => `(command|
theorem $x0 : aW $x1 $x2 = 0 := rfl)
M Yb 0 0
set_option hygiene false in
local macro "O " x0:ident x1:num x2:num x3:num : command => `(command|
theorem $x0 : aW $x1 $x2 = ($x3 : ℝ) / 100000000 := rfl)
O Yc 0 1 25326800
O Yd 0 2 62369200
O Yf 0 3 40126500
O Yh 0 4 99999900
O Yj 0 5 200000000
M Yk 1 0
M Yl 1 1
O Ym 1 2 48244400
O Yn 1 3 37630700
O Yo 1 4 119746800
O Yp 1 5 99999900
M Yq 2 0
M Yr 2 1
M Yt 2 2
O Yv 2 3 52857300
O Yw 2 4 37630700
O Yx 2 5 40126500
M Yy 3 0
M Yz 3 1
M Y1 3 2
M Y3 3 3
O Y4 3 4 48244400
O Y5 3 5 62369200
M Y6 4 0
M Y7 4 1
M Y8 4 2
M Y9 4 3
M ZA 4 4
O ZB 4 5 25326800
M ZD 5 0
M ZE 5 1
M ZF 5 2
M ZG 5 3
M ZH 5 4
M ZJ 5 5
theorem pH : bW 0 = (24896 : ℝ) / 100000000 := rfl
theorem pI : bW 1 = (42034 : ℝ) / 100000000 := rfl
theorem pJ : bW 2 = (46137 : ℝ) / 100000000 := rfl
theorem pL : bW 3 = (42034 : ℝ) / 100000000 := rfl
theorem pN : bW 4 = (24896 : ℝ) / 100000000 := rfl
theorem ASO : WW.B = (179997 : ℝ) / 100000000 := by
  show (∑ r : Fin 5, bW r) = _
  norm_num [Fin.sum_univ_five, pH, pI, pJ, pL, pN]
theorem Zk : ∀ i j, 0 ≤ WW.a i j := by
  intro i j
  unfold WW
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW 0 0; norm_num [Yb]
  | 0, 1 => show (0:ℝ) ≤ aW 0 1; norm_num [Yc]
  | 0, 2 => show (0:ℝ) ≤ aW 0 2; norm_num [Yd]
  | 0, 3 => show (0:ℝ) ≤ aW 0 3; norm_num [Yf]
  | 0, 4 => show (0:ℝ) ≤ aW 0 4; norm_num [Yh]
  | 0, 5 => show (0:ℝ) ≤ aW 0 5; norm_num [Yj]
  | 1, 0 => show (0:ℝ) ≤ aW 1 0; norm_num [Yk]
  | 1, 1 => show (0:ℝ) ≤ aW 1 1; norm_num [Yl]
  | 1, 2 => show (0:ℝ) ≤ aW 1 2; norm_num [Ym]
  | 1, 3 => show (0:ℝ) ≤ aW 1 3; norm_num [Yn]
  | 1, 4 => show (0:ℝ) ≤ aW 1 4; norm_num [Yo]
  | 1, 5 => show (0:ℝ) ≤ aW 1 5; norm_num [Yp]
  | 2, 0 => show (0:ℝ) ≤ aW 2 0; norm_num [Yq]
  | 2, 1 => show (0:ℝ) ≤ aW 2 1; norm_num [Yr]
  | 2, 2 => show (0:ℝ) ≤ aW 2 2; norm_num [Yt]
  | 2, 3 => show (0:ℝ) ≤ aW 2 3; norm_num [Yv]
  | 2, 4 => show (0:ℝ) ≤ aW 2 4; norm_num [Yw]
  | 2, 5 => show (0:ℝ) ≤ aW 2 5; norm_num [Yx]
  | 3, 0 => show (0:ℝ) ≤ aW 3 0; norm_num [Yy]
  | 3, 1 => show (0:ℝ) ≤ aW 3 1; norm_num [Yz]
  | 3, 2 => show (0:ℝ) ≤ aW 3 2; norm_num [Y1]
  | 3, 3 => show (0:ℝ) ≤ aW 3 3; norm_num [Y3]
  | 3, 4 => show (0:ℝ) ≤ aW 3 4; norm_num [Y4]
  | 3, 5 => show (0:ℝ) ≤ aW 3 5; norm_num [Y5]
  | 4, 0 => show (0:ℝ) ≤ aW 4 0; norm_num [Y6]
  | 4, 1 => show (0:ℝ) ≤ aW 4 1; norm_num [Y7]
  | 4, 2 => show (0:ℝ) ≤ aW 4 2; norm_num [Y8]
  | 4, 3 => show (0:ℝ) ≤ aW 4 3; norm_num [Y9]
  | 4, 4 => show (0:ℝ) ≤ aW 4 4; norm_num [ZA]
  | 4, 5 => show (0:ℝ) ≤ aW 4 5; norm_num [ZB]
  | 5, 0 => show (0:ℝ) ≤ aW 5 0; norm_num [ZD]
  | 5, 1 => show (0:ℝ) ≤ aW 5 1; norm_num [ZE]
  | 5, 2 => show (0:ℝ) ≤ aW 5 2; norm_num [ZF]
  | 5, 3 => show (0:ℝ) ≤ aW 5 3; norm_num [ZG]
  | 5, 4 => show (0:ℝ) ≤ aW 5 4; norm_num [ZH]
  | 5, 5 => show (0:ℝ) ≤ aW 5 5; norm_num [ZJ]
theorem Z9 : ∀ r, ((24896 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((24896 : ℝ) / 100000000) ≤ bW 0; norm_num [pH]
  | 1 => show ((24896 : ℝ) / 100000000) ≤ bW 1; norm_num [pI]
  | 2 => show ((24896 : ℝ) / 100000000) ≤ bW 2; norm_num [pJ]
  | 3 => show ((24896 : ℝ) / 100000000) ≤ bW 3; norm_num [pL]
  | 4 => show ((24896 : ℝ) / 100000000) ≤ bW 4; norm_num [pN]
theorem Zl : ∀ s : ℕ, WW.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass WW
  rcases lt_or_ge s 6 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_six, Yb, Yc, Yd, Yf, Yh, Yj, Yk, Yl, Ym, Yn, Yo, Yp, Yq, Yr, Yt, Yv, Yw, Yx, Yy, Yz, Y1, Y3, Y4, Y5, Y6, Y7, Y8, Y9, ZA, ZB, ZD, ZE, ZF, ZG, ZH, ZJ, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 6, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num
theorem AEg : WW.Adm := ⟨Zk, fun r => le_trans (by norm_num) (Z9 r), Zl⟩
private lemma ASS (f : Fin (6 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4
  exact Fin.sum_univ_five f
theorem AFm (g : Fin (6 - 1) → ℝ) : Fw WW g = AG.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * BK (Ew 6 g j - Ew 6 g i) else 0) = _
  unfold AG.G Ew
  simp only [ASS, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, Yb, Yc, Yd, Yf, Yh, Yj, Yk, Yl, Ym, Yn, Yo, Yp, Yq, Yr, Yt, Yv, Yw, Yx, Yy, Yz, Y1, Y3, Y4, Y5, Y6, Y7, Y8, Y9, ZA, ZB, ZD, ZE, ZF, ZG, ZH, ZJ, pH, pI, pJ, pL, pN]
  norm_num [AG.SA]
  try ring
theorem AFn (x0 x1 x2 x3 x4 : ℝ) : AG.G x4 x3 x2 x1 x0 = AG.G x0 x1 x2 x3 x4 := by
  unfold AG.G; ring_nf
theorem oT : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (AG.cN : ℝ) / AG.SA ≤ AG.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases Ak.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← AFn]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases Ak.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)
theorem AEP : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (345747 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [AFm]
  have h := oT (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [AG.cN, AG.SA] at h
  push_cast at h
  exact h
theorem AEe : Phi_w' 6 ((345747 : ℝ) / 100000000) 294 ((179997 : ℝ) / 100000000)
    = (9800000000 * HD 1 - 17339711) / 9766693039 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring
theorem pO :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((9800000000 * HD 1 - 17339711) / 9766693039 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← AEe, ← ASO]
  exact n_point_bound_w' 6 ((345747 : ℝ) / 100000000) 294 WW (by norm_num) (by norm_num) AEg
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) Z9 (by norm_num) AEP (by norm_num)
theorem Vk : candidateKappa ≤ (9800000000 * HD 1 - 17339711) / 9766693039 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9766693039)]
  linarith [HD_one_bounds.1]
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := pO ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast Jt T (2 * T)
  have h0 : (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ ((9800000000 * HD 1 - 17339711) / 9766693039 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [Vk]) hN
  linarith
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic
theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  first
    | (norm_num; done)
    | (rw [← cStar_one_eq_cMT]
       have h := HD_one_bounds.2
       unfold Zeta23.ThmD.HD at h
       linarith)
end Aa
end
noncomputable section
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  Aa.strict
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  Aa.dyadic
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  Aa.cumulative
end
#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative

example : currentRecordKappa = (67291431 : ℝ) / 100000000 := rfl
example : candidateKappa = (6730187 : ℝ) / 10000000 := rfl
#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
