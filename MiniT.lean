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
no `sorry`, no `native_decide`, no additional axioms.  Sources: the Zeta Lab bridge
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

/-! ###### source module: Zeta23Ext/StableRankTrace.lean ###### -/

/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/


/-!
# The stability-enhanced rank–trace inequality (Ainta, §2)

This file states and proves S2 of `hunts/ainta_seven_point/TRUST-MAP.md` §4: the one
piece of linear algebra that the `ainta/zeta-simple-zeros` note adds to the rank–trace
lemma of `[L23]` §3.  It carries a nonnegative *spectral defect* `tr Psi(VᴴV)` through
the inequality, where

  `Psi t = (t − 1)²` for `t ≤ 2`,   `Psi t = 2t − 3` for `t > 2`.

## What this file found, and it changes the picture

`Psi` is not new to this Lean development.  It is upstream's own `gc 2`, shifted:

  `Psi = fun t => gc 2 t + 1`   (`Psi_eq_gc_two_add_one`, kernel-checked below),

where `gc c x = x² − cx − ((x − c)⁺)²` is
`Zeta23.ZeroSide.RankTraceMult.gc`.  The additive `1` is exactly `Psi 0`, and it is
what converts a defect summed over the *nonzero* spectrum against a rank count into a
defect summed over *all* of `r` against `Fintype.card r`.  Everything else Ainta's
lemma needs, the sharpened termwise estimate (`sq_sub_ge_gc`) and the transfer of the
nonzero spectrum between `V Vᴴ` and `VᴴV` (`sum_eigenvalues_comm`), is already a
kernel-checked declaration upstream.

So `stable_rank_trace` is proved here as a **corollary** of the upstream multiplicity-aware
`rank_trace_mult`, evaluated at the eigenbasis presentation of `P = V Vᴴ` (which is the
presentation at which upstream's Schur–Jensen step `sum_gc_eigenvalues_ge` is an equality).
No new analysis, no new scalar estimate, and no copied proof skeleton.

## The two forms

* `stable_rank_trace_sharp`: no hypothesis on the columns of `V` at all,
    `2·tr(V Vᴴ) + 4·tr Q − card r − 4b + tr Psi(VᴴV) ≤ ‖V Vᴴ + Q‖_F²`.
* `stable_rank_trace`: the trust map's statement, which is the sharp form weakened by
  `2·(card r − tr(V Vᴴ)) ≥ 0`.  That is the only place the column bound `hV` is used.

## Non-vacuity

`stable_rank_trace_collapse` is the trust map's built-in test: with the defect set to `0`
the statement is `stable_rank_trace_no_defect`, which is proved independently from
`RHLinalg.rank_trace_ineq_two`.  The defect is nonnegative (`Psi_nonneg`), so the
enhanced form really is a strengthening of the existing theorem and not a different one.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder

namespace Zeta23Ext.StableRankTrace

/-! ### The scalar profile `Psi` -/

/-- Ainta's spectral-defect profile: `Psi t = (t−1)²` for `t ≤ 2`, `2t − 3` beyond. -/
def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

/-- **The identification.**  `Psi` is upstream's `gc 2` shifted by `Psi 0 = 1`. -/
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

/-- The sharpened termwise estimate, in Ainta's own form: for `p, ν ≥ 0`,
`(p − ν)² + 4ν ≥ 2p − 1 + Psi p`.  This is upstream's `sq_sub_ge_gc` at `c = 2`. -/
lemma two_mul_sub_one_add_Psi_le {p nu : ℝ} (hp : 0 ≤ p) (hnu : 0 ≤ nu) :
    2 * p - 1 + Psi p ≤ (p - nu) ^ 2 + 4 * nu := by
  have h := sq_sub_ge_gc (c := 2) hp hnu (by norm_num)
  rw [Psi_eq_gc_two_add_one]
  linarith

/-- … and the estimate is exact: the minimum over `ν ≥ 0` is attained at `ν = (p − 2)⁺`,
so `Psi p = min_{ν ≥ 0} ((p − ν)² + 4ν) − 2p + 1`.  (This is the one-variable calculus
fact the trust map names; it is recorded because the sharpness is the whole point of the
defect term, and an inequality with no attainment claim would not pin it.) -/
lemma Psi_attained (p : ℝ) :
    (p - max (p - 2) 0) ^ 2 + 4 * max (p - 2) 0 = 2 * p - 1 + Psi p := by
  unfold Psi
  rcases le_or_gt p 2 with h | h
  · rw [max_eq_right (by linarith), if_pos h]; ring
  · rw [max_eq_left (by linarith), if_neg (not_le.mpr h)]; ring

/-! ### The eigenbasis presentation of a PSD matrix -/

section Eigen

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvector columns of a Hermitian matrix, in the `Wmat`/`Pmat` column indexing. -/
def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j

lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (eigCols hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, eigCols, Matrix.mul_diagonal]
  ring

/-- **`P` is `Pmat` of its own spectral data.**  This is the presentation at which the
Schur–Jensen step of `rank_trace_mult` is an equality, so it is the one that exposes the
full spectral defect rather than its diagonal shadow. -/
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

/-- The eigenvector columns are unit vectors, so the `Pmat` weight `m j * x_j` is `λ j`. -/
lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (eigCols hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j

end Eigen

/-! ### The theorem -/

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

/-- `tr(V Vᴴ)` is the total squared column mass of `V`. -/
lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

/-- The `Psi`-trace on the Gram side, in terms of upstream's `gc 2` on the `V Vᴴ` side. -/
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

/-- **Stability-enhanced rank–trace inequality, sharp form.**  No hypothesis on the
columns of `V`.  Strengthens `RHLinalg.rank_trace_ineq` at `c = 2` by the spectral defect
`tr Psi(VᴴV) − card r`, which by `rtrace_specMap_Psi` is `∑ᵢ gc 2 (λᵢ(V Vᴴ))`. -/
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

/-- **Stability-enhanced rank–trace inequality** (the trust map's statement, S2).
Strengthens `RHLinalg.rank_trace_ineq_two` by the spectral defect `tr Psi(VᴴV)`.

The column bound `hV` is used for exactly one thing: `tr(V Vᴴ) ≤ card r`, which is what
turns the sharp form's `2·tr(V Vᴴ) − card r` into `4·tr(V Vᴴ) − 3·card r`. -/
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

/-! ### Non-vacuity: the `Psi = 0` collapse -/

/-- The `Psi := 0` shadow of `stable_rank_trace`, proved **independently** from the
existing `RHLinalg.rank_trace_ineq_two`.  This is the trust map's built-in test: the
enhanced statement must reduce to the existing theorem when the defect is dropped. -/
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

/-- … and `stable_rank_trace` implies it, because the defect is nonnegative.  Together
with `stable_rank_trace_no_defect` this is the statement-level check that S2 is a
strengthening of `rank_trace_ineq_two` and not a different inequality. -/
theorem stable_rank_trace_collapse (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := stable_rank_trace V hV hQ hb
  have hpos : 0 ≤ rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi) := by
    rw [rtrace_specMap]
    exact Finset.sum_nonneg fun j _ => Psi_nonneg _
  linarith

/-- The sharp form is strictly stronger than the trust map's form: their difference is
`2·(card r − tr(V Vᴴ)) ≥ 0`, and that gap is the whole content of `hV` here. -/
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

/-! ### Standing axiom audit

Same idiom as `Zeta23Ext/TruncEst/Axioms.lean`: the audit runs on every `lake build`
rather than living in a document that can drift from the tree. Anything other than
`propext`, `Classical.choice`, `Quot.sound` is a defect. -/


end Zeta23Ext.StableRankTrace

end

/-! ###### source module: Zeta23Ext/Bridge/Defs.lean ###### -/

/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/


/-!
# Bridge definitions: the `n`-point simple-zero bound (Ainta, `riemann.tex`, `n = 7`)

The objects of `hunts/ainta_seven_point/TRUST-MAP.md` steps S6–S16, written in the vocabulary of
the vendored `anthropics/zeta-23-lean` (`[L23]`) wherever that vocabulary exists:

* `RHLinalg.rtrace / frobSq / posIndex / specMap` (`Zeta23/LinAlg/`),
* `Zeta23.ZeroSide.ZeroBlockData` with its `S₁, s₁, s₂, Zeta23.Ncount, blockP, blockQ, PairReps`
  (`Zeta23/ZeroSide.lean`), instantiated at height `T` by `Zeta23.ZeroSide.blockData`,
* the window parameters `Zeta23.Params` (`L, d, tau, a, phiHat, hat`) and the Montgomery–Taylor
  window-realizing family `Params.atD` (`Zeta23/ThmD/ParamsD.lean`),
* the counting functions `ZeroConfig.N / N0s / NIprime / s1` and the constant `ThmD.HD 1`
  (`= 3/2 − (1/√2)cot(1/√2)`, `Zeta23/ThmD/Functional.lean`, `HD_one`),
* Ainta's profile `Psi` from `Zeta23Ext/StableRankTrace.lean` (`= gc 2 + 1`, kernel-checked there).

What is new here and has no upstream counterpart: the overlap kernel `k`, `w = k²`, the `n`-point
functional `F` (with `F6 = F 7`) with pressure denominator `p`, the block objects (defect `D = tr Psi`, energy, span,
off-diagonal mass), the retained central simple zeros and their Gram matrix `M°`, the simple-zero
factor `P₁ = V Vᴴ` with its complement `Q' = Â − P₁`, and the bound constant `Phi_n n c m p`
(with `Phi = Phi_n 7`).

Nothing in this file is a theorem about ζ; the only proofs are bookkeeping (Hermitian-ness,
positivity, injectivity) that the step files and `Bridge/Main.lean` consume.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

/-! ### 1. The Montgomery–Taylor overlap kernel  ([A] §3, eq:kdef, eq:Kexplicit) -/

/-- `K(x) := ∫_{-1/2}^{1/2} cos(√2 t) cos(2π x t) dt`  ([A] eq:Kexplicit, the integral that defines
it; the closed sinc form printed there is a consequence and is what the Arb verifier evaluates). -/
def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

/-- `k(x) := K(x)/K(0)`  ([A] eq:kdef). -/
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

/-- `w(x) := k(x)²`  ([A] end of §3). -/
def wfun (x : ℝ) : ℝ := kfun x ^ 2

/-! ### 2. The n-point functional  ([A] §4, eq:F6 at `n = 7`)

The paper writes the seven-point case.  Everything below is stated for `n` points and `n − 1`
gaps; `n = 7` is recovered definitionally (`pts_eq_ptsN`, `F6_eq`).  The two seven-point
definitions `pts` and `F6` are kept verbatim because the Palomar surface
(`BridgeSolution.lean`) re-states them and checks the match by `rfl`. -/

/-- The `n` ordered points `y₀ = 0, yᵢ = g₀ + ⋯ + g_{i−1}` determined by `n − 1` gaps. -/
def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0

/-- `F n p (g) := (1/p) Σ gᵢ + Σ_{s=1}^{n−1} (2/(n−s)) Σ_{i=1}^{n−s} w(gᵢ + ⋯ + g_{i+s−1})`, the
`n`-point functional at pressure denominator `p`, written as a sum over the `n(n−1)/2` pairs
`i < j` of the `n` points with coefficient `2/(n − (j−i))`.  [A] eq:F6 is `F 7 3000`. -/
def F (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (ptsN n g j - ptsN n g i)
        else 0

/-- The seven ordered points `y₀ = 0, yᵢ = g₀ + ⋯ + g_{i−1}` determined by six gaps. -/
def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0

/-- `F6(g) := (1/p) Σ gᵢ + Σ_{r=1}^{6} (2/(7−r)) Σ_{i=1}^{7−r} w(gᵢ + ⋯ + g_{i+r−1})`  ([A] eq:F6),
written as a sum over the 21 pairs `i < j` of the seven points with coefficient `2/(7 − (j−i))`.
`p` is the pressure denominator (`p = 3000` in both published runs). -/
def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (pts g j - pts g i)
        else 0

/-- The seven-point points are the `n = 7` case, definitionally. -/
theorem pts_eq_ptsN (g : Fin 6 → ℝ) (i : Fin 7) : pts g i = ptsN 7 g i := rfl

/-- **`F6` is `F` at `n = 7`, definitionally.**  This is what makes every seven-point statement
of `Bridge/Main.lean` a corollary of its `n`-point original with no change of statement. -/
theorem F6_eq (p : ℕ) (g : Fin 6 → ℝ) : F6 p g = F 7 p g := rfl

/-! ### 3. Block quantities on an abstract finite index set -/

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `E := Σ_{i ≠ j ∈ B} w(xᵢ − xⱼ) = 2 Σ_{i<j} w(yⱼ − yᵢ)`  ([A] Lemma 4.2, `E_m`; `w` is even). -/
def energyOn (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else wfun (x i - x j)

/-- `Σ_{i ≠ j ∈ B} |G_{ij}|² = 2 Σ_{i<j} |G_{ij}|²`  ([A] Lemma 4.3, for Hermitian `G`). -/
def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2

/-- `span(B) := max_B x − min_B x`  ([A] §4 after eq:mA; `0` for the empty block). -/
def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0

/-- `B` is a set of *consecutive* points in the order given by `x`. -/
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

/-! ### 4. The spectral defect `D(M) := tr Psi(M)`  ([A] §2, eq:Psi and the line after it) -/

/-- `D(M) := tr Psi(M)` for Hermitian `M`, through `[L23]`'s `specMap` (S5). -/
def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)

lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => Psi_nonneg _

/-- `D(G_B)`: the defect of the principal submatrix of `M` on the block `B`. -/
def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))

lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ blockDefect hM B :=
  defect_nonneg _

end Blocks

/-! ### 5. The bound constant  ([A] §5, TRUST-MAP §1.1) -/

/-- `Phi_n(n, c, m, p) := (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m)`, the `n`-point bound
constant, with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`.  The block size `m` is capped by
`c(m − (n−1)) ≤ 1`, i.e. `m ≤ (n−1) + ⌊1/c⌋`. -/
def Phi_n (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

/-- `Phi(c, m, p) := (H − 6(m−1)/(pm)) / (1 − c(m−6)/m)` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`. -/
def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

/-- **`Phi` is `Phi_n` at `n = 7`.** -/
theorem Phi_eq_Phi_n (c : ℝ) (m p : ℕ) : Phi c m p = Phi_n 7 c m p := by
  unfold Phi Phi_n
  norm_num

/-! ### 6. The simple-zero factor at the block level  ([A] §1: `P₁ = V Vᵀ`, `Q' = Â − P₁`) -/

section BlockLevel

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

/-- `V`: the `d × s₁` matrix whose columns are `v_ρ = u_ρ/√c`, `ρ ∈ 𝒮₁` (`c = aL²`). -/
def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)

/-- `P₁ := V Vᴴ = Σ_{ρ ∈ 𝒮₁} v_ρ v_ρ*`. -/
def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ

/-- `Q' := Â − P₁` with `Â = blockP + blockQ` (`[L23]` prop:block (ii)). -/
def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c

/-- `M := Vᴴ V`, the Gram matrix of the simple on-line zeros of `𝒵(I′)`. -/
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

/-! ### 7. The concrete objects at height `T`  ([A] §§1, 3, 5) -/

section Concrete

open Classical

/-- The Montgomery–Taylor window of height `T` at `λ = 1`: `[L23]`'s window-realizing family
`Params.atD` of the §6 parameters `paramsOf stdProfile 1` (`w = 1`, `L = ℓ`).  This is the
"optimised test family of Theorem D, `L = ℓ`" of [A] §1. -/
def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atD T

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- The normalised ordinate `x_ρ := L(γ_ρ − T)/(2π)`  ([A] §3). -/
def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)

/-- `c := aL²`, the normalisation of the hat units ([L23] eq:hatunits). -/
def aL2 : ℝ := P.a T * P.L T ^ 2

/-- The block data of `𝒵(I′)` for the window `P` at height `T`: `[L23]`'s `blockData` with its
conjugation input discharged by `[L23]`'s `phiHatConj`. -/
def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj

/-- The retained central simple zeros ([A] Lemma 3.1, §5): `𝒮₁` minus the two strips of normalised
width `L²` at the ends of the grid.  (`L² ≤ x_ρ ≤ d − L²` already forces `T < γ_ρ < 2T`.) -/
def retained : Finset (ZI Z T) :=
  (bdata Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2

lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1

/-- The inclusion of the retained zeros into `𝒮₁`. -/
def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩

lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)

/-- `M°`: the Gram matrix of the retained central simple zeros, the principal submatrix of the
full Gram matrix `M = Vᴴ V` of `𝒮₁` ([A] Corollary 2.2 and §5). -/
def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)

lemma gram_isHermitian : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _

lemma gram_posSemidef : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _

/-- `D(M°)`. -/
def Dcirc : ℝ := defect (gram_isHermitian Z P T)

/-- The normalised ordinates of the retained zeros. -/
def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)

lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (bdata Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h

/-- Distinct retained zeros have distinct normalised ordinates (they share `β = 1/2`). -/
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

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/


end Zeta23Ext.Bridge

end

/-! ###### source module: ThreePoint/Base.lean ###### -/

/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/


/-!
# The three-point certificate: enclosure machinery

`Zeta23Ext.Bridge.n_point_bound` is proved for every `n`, conditional on the finite inequality
`hCert`.  The `ThreePoint` library discharges `hCert` at `n = 3`, so that the `n = 3` instance
of that theorem becomes **unconditional**.

This module is the numerical layer.  Sections 1–3 are carried over **verbatim** from
`hunts/ainta_seven_point/lean/CertRoute.lean` (pull request #117, branch `bridge/certificate`,
not merged at the time of writing): the twelve-term Taylor enclosure of `sin` and `cos`, the
monotone one-sided corollaries, and the closed form of the kernel.  They are reproduced here
rather than imported because #117 is not on `main`; when #117 lands, the two should be unified
and this copy deleted.  What is new here starts at section 4.

The library is a `lean_lib` of this package rather than a package of its own, so that it sees
the very definitions `n_point_bound` consumes without a `path` dependency.  It adds nothing to
this package's dependency set and no other library here imports it: `Zeta23Ext`,
`BridgeChallenge`/`BridgeSolution` are untouched by it, and only `V2Solution` imports it.
-/

noncomputable section
open Real intervalIntegral

namespace Zeta23Ext.Bridge.ThreePoint

/-! ## 1. Twelve-term Taylor enclosure of `cos` and `sin`  (from CertRoute, #117) -/

/-- Degree-10 Taylor polynomial of `cos`. -/
def taylorCos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800

/-- Degree-11 Taylor polynomial of `sin`. -/
def taylorSin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800

/-- The remainder bound `13 / (12! * 12)` that `Complex.exp_bound` supplies at `n = 12`. -/
def taylorErr : ℝ := 13/5748019200

/-- Twelve-term Taylor bound for `cos` and `sin` on `|θ| ≤ 1`, from `Complex.exp_bound`. -/
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

/-! ## 2. The kernel in closed form  (from CertRoute, #117) -/

/-- `∫_{-1/2}^{1/2} cos (c t) dt = sinc (c/2)`, with no case split needed at `c = 0`. -/
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

/-- **The sinc form of the Montgomery–Taylor overlap kernel.** -/
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

/-- `γ := (1/√2) cot (1/√2)`, the single transcendental constant of the closed form. -/
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

/-- Enclosures of `cos(1/√2)` and `sin(1/√2)` to the width the Taylor remainder allows. -/
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

/-- `γ` to the width the twelve-term Taylor remainder allows, `1.1 · 10⁻⁸`.  (CertRoute's
`gam_bounds` gives `10⁻⁶`; the cell table wants the extra two digits, and they are free once
`√2/2` is pinned to nineteen.) -/
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

/-- **The closed form of the normalised kernel.** `k(x) = (cos b − 2γ b sin b)/(1 − 2b²)`,
`b = πx`, valid off the two removable singularities `b² = 1/2`. -/
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

/-! ## 3. `π` to twenty places -/

theorem pi_lo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20

theorem pi_hi : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20

/-! ## 4. The cell bound

New from here on.  `w = k²` and `k = N/D` with `N = cos b − 2γ b sin b`, `D = 1 − 2b²`,
`b = πx`.  For `x ≥ 1/2` we have `b ≥ π/2` and so `D < 0`; a lower bound `nlo ≤ |N|` and an
upper bound `|D| ≤ dhi` give `(nlo/dhi)² ≤ w(x)`. -/

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

/-- **The cell bound.**  Everything the generated table needs about the kernel. -/
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

/-- `nlo ≤ N` gives `nlo ≤ |N|`. -/
lemma abs_ge_of_le {N nlo : ℝ} (h : nlo ≤ N) : nlo ≤ |N| := h.trans (le_abs_self N)

/-- `N ≤ -nlo` gives `nlo ≤ |N|`. -/
lemma abs_ge_of_ge {N nlo : ℝ} (h : N ≤ -nlo) : nlo ≤ |N| :=
  le_trans (by linarith) (neg_le_abs N)

/-! ## 5. Reduction of `cos (π x)` and `sin (π x)` to a quarter window

Every cell of the table sits inside `[a, a + 1/4]` or `[a − 1/4, a]` for a half-integer anchor
`a`, so the reduced angle `θ = π|x − a|` satisfies `0 ≤ θ ≤ π/4 < 1` and the Taylor enclosures
of section 1 apply. -/


/-! ### Anchor values.  `cos (π a)` and `sin (π a)` at the nine half-integers the table uses. -/

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

/-- Evenness / oddness, for cells that sit to the left of their anchor. -/
lemma cos_flip (a x : ℝ) : Real.cos (Real.pi*(x-a)) = Real.cos (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.cos_neg]

lemma sin_flip (a x : ℝ) : Real.sin (Real.pi*(x-a)) = -Real.sin (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.sin_neg]

/-! ## 6. The window `[0, 1/2]`

`kfun_closed` is silent at the removable singularity `b² = 1/2`, i.e. at
`x = √2/(2π) = 0.2250…`, which lies inside `[0,1/2]`.  That window is therefore handled from
the sinc form instead, where the singularity is not visible at all: the left sinc is enclosed
by its own Taylor polynomial and the right sinc is merely shown to be nonnegative.  The bound
obtained, `w ≥ 19/100`, is enormously more than the table needs, it only has to beat `c`. -/

/-- The degree-10 Taylor polynomial of `sinc`. -/
def taylorSinc (z : ℝ) : ℝ :=
  1 - z^2/6 + z^4/120 - z^6/5040 + z^8/362880 - z^10/39916800

/-- `sinc` from the twelve-term enclosure, valid at `z = 0` as well. -/
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

/-- **The window `[0,1/2]`.** -/
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

/-! ###### source module: ThreePoint/Cells0.lean ###### -/



noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint


theorem wc_0 (x : ℝ) (h₁ : (1/2:ℝ) ≤ x) (h₂ : x ≤ (3/4:ℝ)) : (66207635573/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1/2:ℝ)) := by linarith only [mul_le_mul hpl (show (0:ℝ) ≤ (x - (1/2:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1/2:ℝ)) ≤ (1/4:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1/2:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1/2:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1/2:ℝ))) := by
    have h := (trig_shift (1/2:ℝ) (x - (1/2:ℝ))).1
    rw [show (1/2:ℝ) + (x - (1/2:ℝ)) = x by ring, cs_h1.1, cs_h1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (1/2:ℝ))) := by
    have h := (trig_shift (1/2:ℝ) (x - (1/2:ℝ))).2
    rw [show (1/2:ℝ) + (x - (1/2:ℝ)) = x by ring, cs_h1.1, cs_h1.2] at h
    rw [h]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (785398163397/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (2356194490193/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (81239552891/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (97487464777/25000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (1838241233809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3899498599901/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (1838241231547/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157864139863/15625000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (1838241231547/1000000000000:ℝ) (157864139863/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (66207635573/2000000000000:ℝ) ≤ ((1838241231547/1000000000000:ℝ)/(157864139863/15625000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_1 (x : ℝ) (h₁ : (3/4:ℝ) ≤ x) (h₂ : x ≤ (1:ℝ)) : (14238606443/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by linarith only [mul_le_mul hpl (show (0:ℝ) ≤ ((1:ℝ) - x) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by linarith only [mul_le_mul hph (show ((1:ℝ) - x) ≤ (1/4:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ ((1:ℝ) - x) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (147262155637/62500000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (314159265359/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (389949853877/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1299832863693/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-11761/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (919120635261/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (707106767047/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9369604401091/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (707106767047/1000000000000:ℝ) (9369604401091/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14238606443/10000000000000:ℝ) ≤ ((707106767047/1000000000000:ℝ)/(9369604401091/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_2 (x : ℝ) (h₁ : (1:ℝ) ≤ x) (h₂ : x ≤ (65/64:ℝ)) : (7298263069/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (490873853/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (1/64:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-998795453939/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-49067676677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3141592653589/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3190680038803/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2599665692513/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2640285504377/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-16194084433/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2389/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (739690103011/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75628430547/3906250000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (739690103011/1000000000000:ℝ) (75628430547/3906250000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7298263069/5000000000000:ℝ) ≤ ((739690103011/1000000000000:ℝ)/(75628430547/3906250000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_3 (x : ℝ) (h₁ : (65/64:ℝ) ≤ x) (h₂ : x ≤ (263/256:ℝ)) : (7358852099/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (1/64:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (429514621/5000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (7/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-249698864617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-498156304957/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-17159462937/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-49067672053/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1595340019401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (201718473607/62500000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2640285468959/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5341500674239/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-229143207119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-129552661517/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (134506548919/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9916727704151/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (134506548919/250000000000:ℝ) (9916727704151/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7358852099/10000000000000:ℝ) ≤ ((134506548919/250000000000:ℝ)/(9916727704151/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_4 (x : ℝ) (h₁ : (65/64:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (1/64:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (5/128:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-249698864617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-49067672053/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1595340019401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2640285468959/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-129552661517/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_5 (x : ℝ) (_h₁ : (65/64:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_6 (x : ℝ) (_h₁ : (65/64:ℝ) ≤ x) (_h₂ : x ≤ (71/64:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_7 (x : ℝ) (h₁ : (263/256:ℝ) ≤ x) (h₂ : x ≤ (529/512:ℝ)) : (1175437333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (7/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (130388367/1250000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (17/512:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (996312614447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (859029241/10000000000:ℝ) + taylorErr ≤ (996312614447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (85797310061/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (85797310061/1000000000000:ℝ) ≤ taylorSin (859029241/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-996312614447/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-99456456847/100000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-85797310061/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3227495577711/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3245903347167/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2670750301293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2685982753491/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-139834459493/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-458286383391/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (217613365249/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (200717770783/10000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (217613365249/500000000000:ℝ) (200717770783/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175437333/2500000000000:ℝ) ≤ ((217613365249/500000000000:ℝ)/(200717770783/10000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_8 (x : ℝ) (h₁ : (263/256:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (7/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (5/128:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (996312614447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (859029241/10000000000:ℝ) + taylorErr ≤ (996312614447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (85797310061/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (85797310061/1000000000000:ℝ) ≤ taylorSin (859029241/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-996312614447/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-85797310061/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3227495577711/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2670750301293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-458286383391/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_9 (x : ℝ) (h₁ : (529/512:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (208621387/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (17/512:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (5/128:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (248641143251/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (208621387/2000000000:ℝ) + taylorErr ≤ (248641143251/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (52060815767/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (52060815767/500000000000:ℝ) ≤ taylorSin (208621387/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-248641143251/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-52060815767/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1622951673583/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5371965434921/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-139834451407/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_10 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (1067/1024:ℝ)) : (930124941/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (5/128:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (659611739/5000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (43/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (495655428789/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (495655428789/500000000000:ℝ) ≤ taylorCos (659611739/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (131540031007/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (659611739/5000000000:ℝ) + taylorErr ≤ (131540031007/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-495655428789/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-131540031007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (818378750337/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1083532551219/200000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-712639526923/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (55734266131/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20431800928101/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (55734266131/200000000000:ℝ) (20431800928101/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (930124941/5000000000000:ℝ) ≤ ((55734266131/200000000000:ℝ)/(20431800928101/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_11 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (5/128:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (23/512:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_12 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (5/128:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_13 (x : ℝ) (_h₁ : (133/128:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_14 (x : ℝ) (h₁ : (1067/1024:ℝ) ≤ x) (h₂ : x ≤ (2137/2048:ℝ)) : (1516005697/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1319223477/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (43/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (682621451/5000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (89/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (99069502317/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (99069502317/100000000000:ℝ) ≤ taylorCos (682621451/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247827715529/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1319223477/10000000000:ℝ) + taylorErr ≤ (247827715529/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (131540026383/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (131540026383/1000000000000:ℝ) ≤ taylorSin (1319223477/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27220115503/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (682621451/5000000000:ℝ) + taylorErr ≤ (27220115503/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247827715529/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-99069502317/100000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-27220115503/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-131540026383/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3273515001347/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (102441154491/31250000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (270883134171/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5425278964281/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-738383600219/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-712639492311/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (252311422951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2561512674163/125000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (252311422951/1000000000000:ℝ) (2561512674163/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1516005697/10000000000000:ℝ) ≤ ((252311422951/1000000000000:ℝ)/(2561512674163/125000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_15 (x : ℝ) (h₁ : (1067/1024:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1319223477/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (43/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (23/512:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247827715529/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1319223477/10000000000:ℝ) + taylorErr ≤ (247827715529/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (131540026383/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (131540026383/1000000000000:ℝ) ≤ taylorSin (1319223477/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247827715529/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-131540026383/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3273515001347/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (270883134171/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-712639492311/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_16 (x : ℝ) (h₁ : (2137/2048:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1365242901/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (89/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (23/512:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247673756927/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1365242901/10000000000:ℝ) + taylorErr ≤ (247673756927/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (34025143223/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (34025143223/250000000000:ℝ) ≤ taylorSin (1365242901/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247673756927/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-34025143223/250000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3278116943711/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1085055778301/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-46148972827/62500000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_17 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (4283/4096:ℝ)) : (533605311/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (23/512:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1434272037/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (187/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (989731936811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (989731936811/1000000000000:ℝ) ≤ taylorCos (1434272037/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8933497667/62500000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1434272037/10000000000:ℝ) + taylorErr ≤ (8933497667/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-989731936811/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-8933497667/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1642509928629/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5436703276561/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-388550208299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (212631520213/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20582710925159/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (212631520213/1000000000000:ℝ) (20582710925159/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (533605311/5000000000000:ℝ) ≤ ((212631520213/1000000000000:ℝ)/(20582710925159/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_18 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (2143/2048:ℝ)) : (467734771/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (23/512:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1457281749/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (95/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494700212761/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-29042585393/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3287320828439/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1360127845163/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-790032581771/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (199367843751/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10306478229089/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (199367843751/1000000000000:ℝ) (10306478229089/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (467734771/5000000000000:ℝ) ≤ ((199367843751/1000000000000:ℝ)/(10306478229089/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_19 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (23/512:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (49/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_20 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (23/512:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_21 (x : ℝ) (h₁ : (4283/4096:ℝ) ≤ x) (h₂ : x ≤ (2143/2048:ℝ)) : (467734771/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (358568009/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (187/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1457281749/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (95/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (19794638827/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (358568009/2500000000:ℝ) + taylorErr ≤ (19794638827/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (142935958049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (142935958049/1000000000000:ℝ) ≤ taylorSin (358568009/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-19794638827/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494700212761/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-29042585393/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-142935958049/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3285019857257/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3287320828439/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5436703203631/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1360127845163/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-790032581771/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-777100381039/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (199367843751/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10306478229089/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (199367843751/1000000000000:ℝ) (10306478229089/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (467734771/5000000000000:ℝ) ≤ ((199367843751/1000000000000:ℝ)/(10306478229089/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_22 (x : ℝ) (h₁ : (2143/2048:ℝ) ≤ x) (h₂ : x ≤ (4289/4096:ℝ)) : (812589723/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (95/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1480291461/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (193/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494531837943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494531837943/500000000000:ℝ) ≤ taylorCos (1480291461/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (73744561217/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1480291461/10000000000:ℝ) + taylorErr ≤ (73744561217/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494531837943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-73744561217/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1643660414219/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3289621799621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5440511307671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1088863896949/200000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-50186118941/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-790032546021/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (18608577283/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5160805792271/250000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (18608577283/100000000000:ℝ) (5160805792271/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (812589723/10000000000000:ℝ) ≤ ((18608577283/100000000000:ℝ)/(5160805792271/250000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_23 (x : ℝ) (h₁ : (2143/2048:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (95/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (49/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1643660414219/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5440511307671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-790032546021/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_24 (x : ℝ) (h₁ : (4289/4096:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (74014573/500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (193/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (49/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39562547217/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (74014573/500000000:ℝ) + taylorErr ≤ (39562547217/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (14748911781/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (14748911781/100000000000:ℝ) ≤ taylorSin (74014573/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-39562547217/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-14748911781/100000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (164481089981/50000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5444319411713/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-802977867109/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_25 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (8587/8192:ℝ)) : (322398213/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (49/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1514806029/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (395/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494274366719/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494274366719/500000000000:ℝ) ≤ taylorCos (1514806029/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (9431371733/62500000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1514806029/10000000000:ℝ) + taylorErr ≤ (9431371733/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494274366719/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-9431371733/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1646536628197/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1090006328177/200000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-822420389789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (166128343649/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4137732588791/200000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (166128343649/1000000000000:ℝ) (4137732588791/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (322398213/5000000000000:ℝ) ≤ ((166128343649/1000000000000:ℝ)/(4137732588791/200000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_26 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (4295/4096:ℝ)) : (296626083/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (49/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (381577721/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (199/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (38009789649/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (381577721/2500000000:ℝ) + taylorErr ≤ (38009789649/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494187234373/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-38009789649/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (658844748397/200000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362983923233/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-828907715473/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (159466753273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5175955031129/250000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (159466753273/1000000000000:ℝ) (5175955031129/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (296626083/5000000000000:ℝ) ≤ ((159466753273/1000000000000:ℝ)/(5175955031129/250000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_27 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (49/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (101/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_28 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (49/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_29 (x : ℝ) (h₁ : (8587/8192:ℝ) ≤ x) (h₂ : x ≤ (4295/4096:ℝ)) : (296626083/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (378701507/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (395/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (381577721/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (199/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988548737977/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (378701507/2500000000:ℝ) + taylorErr ≤ (988548737977/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (30180388621/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (30180388621/200000000000:ℝ) ≤ taylorSin (378701507/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (38009789649/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (381577721/2500000000:ℝ) + taylorErr ≤ (38009789649/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988548737977/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494187234373/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-38009789649/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-30180388621/200000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3293073256393/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (658844748397/200000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (170313486493/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362983923233/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-828907715473/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-20560508839/25000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (159466753273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5175955031129/250000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (159466753273/1000000000000:ℝ) (5175955031129/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (296626083/5000000000000:ℝ) ≤ ((159466753273/1000000000000:ℝ)/(5175955031129/250000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_30 (x : ℝ) (h₁ : (4295/4096:ℝ) ≤ x) (h₂ : x ≤ (8593/8192:ℝ)) : (543892897/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1526310883/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (199/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (76890787/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (401/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (98819889581/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (98819889581/100000000000:ℝ) ≤ taylorCos (76890787/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494187236643/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1526310883/10000000000:ℝ) + taylorErr ≤ (494187236643/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (152039153973/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (152039153973/1000000000000:ℝ) ≤ taylorSin (1526310883/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (239337763/1562500000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (76890787/500000000:ℝ) + taylorErr ≤ (239337763/1562500000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494187236643/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-98819889581/100000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-239337763/1562500000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-152039153973/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (102944491937/31250000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (411921778447/125000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5451935619797/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2726919872489/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-52212392173/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-828907679149/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (76400310521/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4143796519909/200000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (76400310521/500000000000:ℝ) (4143796519909/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (543892897/10000000000000:ℝ) ≤ ((76400310521/500000000000:ℝ)/(4143796519909/200000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_31 (x : ℝ) (h₁ : (4295/4096:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1526310883/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (199/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (101/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494187236643/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1526310883/10000000000:ℝ) + taylorErr ≤ (494187236643/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (152039153973/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (152039153973/1000000000000:ℝ) ≤ taylorSin (1526310883/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494187236643/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-152039153973/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (102944491937/31250000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5451935619797/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-828907679149/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_32 (x : ℝ) (h₁ : (8593/8192:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1537815739/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (401/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (101/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (19763978007/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1537815739/10000000000:ℝ) + taylorErr ≤ (19763978007/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (153176163697/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (153176163697/1000000000000:ℝ) ≤ taylorSin (1537815739/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-19763978007/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-153176163697/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (131814969103/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2726919835909/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-835398238347/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_33 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (8599/8192:ℝ)) : (225854567/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (101/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (390206363/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (407/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493921913091/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493921913091/500000000000:ℝ) ≤ taylorCos (390206363/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (6217983121/40000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (390206363/2500000000:ℝ) + taylorErr ≤ (6217983121/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493921913091/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-6217983121/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1648837599379/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5457647849071/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-212097263787/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (69727385517/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1296832714563/62500000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (69727385517/500000000000:ℝ) (1296832714563/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (225854567/5000000000000:ℝ) ≤ ((69727385517/500000000000:ℝ)/(1296832714563/62500000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_34 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (4301/4096:ℝ)) : (81774907/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (101/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (393082577/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (205/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (24691608249/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (24691608249/25000000000:ℝ) ≤ taylorCos (393082577/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39146493749/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (393082577/2500000000:ℝ) + taylorErr ≤ (39146493749/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-24691608249/25000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-39146493749/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3298825684349/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2729775950559/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-427444628739/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (66387536241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10382250895721/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (66387536241/500000000000:ℝ) (10382250895721/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81774907/2000000000000:ℝ) ≤ ((66387536241/500000000000:ℝ)/(10382250895721/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_35 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (101/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_36 (x : ℝ) (h₁ : (8599/8192:ℝ) ≤ x) (h₂ : x ≤ (4301/4096:ℝ)) : (81774907/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1560825451/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (407/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (393082577/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (205/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (24691608249/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (24691608249/25000000000:ℝ) ≤ taylorCos (393082577/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493921915361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1560825451/10000000000:ℝ) + taylorErr ≤ (493921915361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (77724786701/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (77724786701/500000000000:ℝ) ≤ taylorSin (1560825451/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39146493749/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (393082577/2500000000:ℝ) + taylorErr ≤ (39146493749/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493921915361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-24691608249/25000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-39146493749/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-77724786701/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3297675198757/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3298825684349/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (272882388793/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2729775950559/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-427444628739/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-169677803707/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (66387536241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10382250895721/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (66387536241/500000000000:ℝ) (10382250895721/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81774907/2000000000000:ℝ) ≤ ((66387536241/500000000000:ℝ)/(10382250895721/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_37 (x : ℝ) (h₁ : (4301/4096:ℝ) ≤ x) (h₂ : x ≤ (8605/8192:ℝ)) : (4602559/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1572330307/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (205/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395958791/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (413/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (61717720403/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (61717720403/62500000000:ℝ) ≤ taylorCos (395958791/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (987664334499/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1572330307/10000000000:ℝ) + taylorErr ≤ (987664334499/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (156585970373/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (156585970373/1000000000000:ℝ) ≤ taylorSin (1572330307/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39430541177/250000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (395958791/2500000000:ℝ) + taylorErr ≤ (39430541177/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-987664334499/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-61717720403/62500000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-39430541177/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-156585970373/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (824706421087/250000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3299976169939/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5459551827881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5461455953163/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-861392655391/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-85488922077/100000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (126090871057/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20779685444331/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (126090871057/1000000000000:ℝ) (20779685444331/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4602559/125000000000:ℝ) ≤ ((126090871057/1000000000000:ℝ)/(20779685444331/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_38 (x : ℝ) (h₁ : (4301/4096:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1572330307/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (205/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (987664334499/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1572330307/10000000000:ℝ) + taylorErr ≤ (987664334499/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (156585970373/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (156585970373/1000000000000:ℝ) ≤ taylorSin (1572330307/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-987664334499/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-156585970373/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (824706421087/250000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5459551827881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-85488922077/100000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_39 (x : ℝ) (h₁ : (8605/8192:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1583835163/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (413/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (13/256:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246870882747/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1583835163/10000000000:ℝ) + taylorErr ≤ (246870882747/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (31544432017/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (31544432017/200000000000:ℝ) ≤ taylorSin (1583835163/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246870882747/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-31544432017/200000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1649988084969/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5461455879901/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-430696309293/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_40 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (8611/8192:ℝ)) : (146669617/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (13/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (401711219/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (419/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (246779499629/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (246779499629/250000000000:ℝ) ≤ taylorCos (401711219/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31998783267/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (401711219/2500000000:ℝ) + taylorErr ≤ (31998783267/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-246779499629/250000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-31998783267/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3302277141121/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (683158007157/125000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-437204500163/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (11270899819/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20810068633541/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (11270899819/100000000000:ℝ) (20810068633541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (146669617/5000000000000:ℝ) ≤ ((11270899819/100000000000:ℝ)/(20810068633541/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_41 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (13/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (211/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_42 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (13/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (107/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_43 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (13/256:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (55/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_44 (x : ℝ) (_h₁ : (269/256:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_45 (x : ℝ) (h₁ : (8611/8192:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (12854759/80000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (419/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (211/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61694875191/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (12854759/80000000:ℝ) + taylorErr ≤ (61694875191/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (4999809741/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (4999809741/31250000000:ℝ) ≤ taylorSin (12854759/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61694875191/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-4999809741/31250000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (5159808033/1562500000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5465263983943/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-874408963329/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_46 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (8617/8192:ℝ)) : (11353613/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (211/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (407463647/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (425/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986747244321/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986747244321/1000000000000:ℝ) ≤ taylorCos (407463647/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (162264820881/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (407463647/2500000000:ℝ) + taylorErr ≤ (162264820881/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986747244321/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-162264820881/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3304578112303/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5469072161349/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-887438014647/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (49654614837/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33344756801/1600000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (49654614837/500000000000:ℝ) (33344756801/1600000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11353613/500000000000:ℝ) ≤ ((49654614837/500000000000:ℝ)/(33344756801/1600000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_47 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (211/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (107/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_48 (x : ℝ) (h₁ : (8617/8192:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1629854587/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (425/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (107/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986747248861/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1629854587/10000000000:ℝ) + taylorErr ≤ (986747248861/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (81132408129/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (81132408129/500000000000:ℝ) ≤ taylorSin (1629854587/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986747248861/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-81132408129/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1652289056151/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1093814417597/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-443718988729/500000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_49 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (8623/8192:ℝ)) : (169363387/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (107/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1652864299/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (431/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (493185632921/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (493185632921/500000000000:ℝ) ≤ taylorCos (1652864299/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (82267433111/500000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1652864299/10000000000:ℝ) + taylorErr ≤ (82267433111/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-493185632921/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-82267433111/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (661375816697/200000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736440132721/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-225119905581/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (42945821759/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10435449272791/500000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (42945821759/500000000000:ℝ) (10435449272791/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (169363387/10000000000000:ℝ) ≤ ((42945821759/500000000000:ℝ)/(10435449272791/500000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_50 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (4313/4096:ℝ)) : (143705609/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (107/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (332873831/2000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (217/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986181318103/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986181318103/1000000000000:ℝ) ≤ taylorCos (332873831/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (165669563021/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (332873831/2000000000:ℝ) + taylorErr ≤ (165669563021/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986181318103/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-165669563021/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (827007392269/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5474784317489/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-907005125513/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (7917619259/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20886119259763/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (7917619259/100000000000:ℝ) (20886119259763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143705609/10000000000000:ℝ) ≤ ((7917619259/100000000000:ℝ)/(20886119259763/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_51 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (107/2048:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (55/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_52 (x : ℝ) (h₁ : (8623/8192:ℝ) ≤ x) (h₂ : x ≤ (4313/4096:ℝ)) : (143705609/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (826432149/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (431/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (332873831/2000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (217/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (986181318103/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (986181318103/1000000000000:ℝ) ≤ taylorCos (332873831/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986371270383/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (826432149/5000000000:ℝ) + taylorErr ≤ (986371270383/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (164534861599/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (164534861599/1000000000000:ℝ) ≤ taylorSin (826432149/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (165669563021/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (332873831/2000000000:ℝ) + taylorErr ≤ (165669563021/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986371270383/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-986181318103/1000000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-165669563021/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-164534861599/1000000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (826719770871/250000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (827007392269/250000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5472880192027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5474784317489/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-907005125513/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-900479584943/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (7917619259/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20886119259763/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (7917619259/100000000000:ℝ) (20886119259763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143705609/10000000000000:ℝ) ≤ ((7917619259/100000000000:ℝ)/(20886119259763/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_53 (x : ℝ) (h₁ : (4313/4096:ℝ) ≤ x) (h₂ : x ≤ (8629/8192:ℝ)) : (60086101/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (832184577/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (217/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1675874011/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (437/8192:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (492995032519/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (492995032519/500000000000:ℝ) ≤ taylorCos (1675874011/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246545330661/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (832184577/5000000000:ℝ) + taylorErr ≤ (246545330661/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (82834779199/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (82834779199/500000000000:ℝ) ≤ taylorSin (832184577/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (166804040537/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1675874011/10000000000:ℝ) + taylorErr ≤ (166804040537/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246545330661/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-492995032519/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-166804040537/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-82834779199/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (132321182763/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3309180054667/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (342174015253/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1095337673907/200000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-913533748801/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-181401017607/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (72456316237/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5225336317103/250000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (72456316237/1000000000000:ℝ) (5225336317103/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60086101/5000000000000:ℝ) ≤ ((72456316237/1000000000000:ℝ)/(5225336317103/250000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_54 (x : ℝ) (h₁ : (4313/4096:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (832184577/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (217/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (55/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246545330661/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (832184577/5000000000:ℝ) + taylorErr ≤ (246545330661/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (82834779199/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (82834779199/500000000000:ℝ) ≤ taylorSin (832184577/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246545330661/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-82834779199/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (132321182763/40000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (342174015253/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-181401017607/200000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_55 (x : ℝ) (h₁ : (8629/8192:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (167587401/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (437/8192:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (55/1024:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985990069579/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (167587401/1000000000:ℝ) + taylorErr ≤ (985990069579/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (33360807183/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (33360807183/200000000000:ℝ) ≤ taylorSin (167587401/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985990069579/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-33360807183/200000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (1654590027333/500000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (5476688296069/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7136982119/7812500000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_56 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (4319/4096:ℝ)) : (62267711/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (55/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1710388579/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (223/4096:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (39416339057/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (39416339057/40000000000:ℝ) ≤ taylorCos (1710388579/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (170206142373/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1710388579/10000000000:ℝ) + taylorErr ≤ (170206142373/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-39416339057/40000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-170206142373/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (41407893893/12500000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (219296021027/40000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-933138244419/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (26135116003/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20947055061171/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (26135116003/500000000000:ℝ) (20947055061171/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (62267711/10000000000000:ℝ) ≤ ((26135116003/500000000000:ℝ)/(20947055061171/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_57 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (55/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (113/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (172473086327/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1733398291/10000000000:ℝ) + taylorErr ≤ (172473086327/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_58 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (541/512:ℝ)) : (1567539/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (55/1024:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (889708857/5000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (29/512:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (246052522531/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (246052522531/250000000000:ℝ) ≤ taylorCos (889708857/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (177004222679/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (889708857/5000000000:ℝ) + taylorErr ≤ (177004222679/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-246052522531/250000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-177004222679/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (663906884997/200000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5493824837953/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-972430194977/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (11779895147/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21038617597321/1000000000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (11779895147/1000000000000:ℝ) (21038617597321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1567539/5000000000000:ℝ) ≤ ((11779895147/1000000000000:ℝ)/(21038617597321/1000000000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

theorem wc_59 (x : ℝ) (h₁ : (4319/4096:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (855194289/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by linarith only [mul_le_mul hpl (show (223/4096:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num) Real.pi_pos.le]
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by linarith only [mul_le_mul hph (show (x - (1:ℝ)) ≤ (113/2048:ℝ) by linarith only [h₁, h₂]) (show (0:ℝ) ≤ (x - (1:ℝ)) by linarith only [h₁, h₂]) (by norm_num)]
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (492704240483/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])
    have h2 : taylorCos (855194289/5000000000:ℝ) + taylorErr ≤ (492704240483/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith only [h, h2]
  have hs1 : (680824551/4000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])
    have h2 : (680824551/4000000000:ℝ) ≤ taylorSin (855194289/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (172473086327/1000000000000:ℝ) := by
    have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)
    have h2 : taylorSin (1733398291/10000000000:ℝ) + taylorErr ≤ (172473086327/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith only [h, h2]
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-492704240483/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith only [hc1, hc2]
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith only [hc1, hc2]
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith only [hs1, hs2]
  have hsxu : Real.sin (Real.pi*x) ≤ (-680824551/4000000000:ℝ) := by rw [hsx]; linarith only [hs1, hs2]
  have hb1 : (3312631511439/1000000000000:ℝ) ≤ Real.pi*x := by linarith only [mul_le_mul hpl h₁ (by norm_num) Real.pi_pos.le]
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by linarith only [mul_le_mul hph h₂ (by linarith only [h₁]) (by norm_num)]
  have hp1 : (1370600113033/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-233284551639/250000000000:ℝ) := by linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith only [hcxl, hcxu, hT1, hT2])
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith only [hfin, hsq]

end Zeta23Ext.Bridge.ThreePoint

end
