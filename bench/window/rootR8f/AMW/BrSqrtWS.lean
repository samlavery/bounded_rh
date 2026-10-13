import AMW.BrProf

/-! ###### AMW/BrSqrtWS — the √ branch of the band profile, and the block chain under it

√ branch of AMTOPA's band profile (Gebendorfer 2026, Lemma 3.3), derived independently; this branch was first used on
riemannzeta.fun by dani-ani0 (dani-bound-2026).

* `gtau τ E = E` for `E ≤ τ` and `2√(τE) − τ` for `E > τ`: nondecreasing (`gtau_mono`), with increments at most those of
  the identity (`gtau_lip`), `gtau ≤ id` (`gtau_le_self`), `gtau ≥ 0` on `E ≥ 0` (`gtau_nonneg`).
* `band_profile_sqrt`: `gtau ((q+1)/q) (bandSq G r q) ≤ defect`, for Hermitian `G` and injective `r`.  With `Y` the band
  part of `G` and `E` its mass, the Fenchel bound `bp_fenchel` with `A = 2αY` gives `defect ≥ (2α − α²) E` whenever
  `α ≥ 0` and `α² E ≤ τ` (the band form is at most `E/τ` on unit vectors, `bp_band_quad`, so `A`'s eigenbasis diagonal
  is `≤ 2`).  `α = 1` for `E ≤ τ`; for `E > τ`, `α = √(τE)/E` (`α² E = τ`; the multiplier at `αρ = 1`, `ρ = √(E/τ)`,
  without a diagonal shift), giving `2√(τE) − τ`.
* The block chain of `AMW/BrTau` with `min τ ·` replaced by `gtau τ` and no cap on `c (m − q)`: `block_bound_w'_g`,
  `block_bound_eventually_w'_g`, `pre_solve_w'_g`, `n_point_bound_w'_g` with `Phi_g`, and `AMW.am_dyadic_n_g`,
  `AMW.am_cumulative_n_g`.
* The final κ step in rational form: `two_mul_sub_le_gtau` (`s ≥ 0`, `s² ≤ τA`, `τ < A` ⇒ `2s − τ ≤ gtau τ A`),
  `Phi_g_ge_sqrt`, `Phi_g_ge_lin`. ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

/-! ### the profile `gtau` -/

/-- the band profile with its √ branch: `E` up to `τ`, `2√(τE) − τ` beyond -/
def gtau (τ E : ℝ) : ℝ := if E ≤ τ then E else 2 * Real.sqrt (τ * E) - τ

/-- the band constant `τ = (q+1)/q` of the `n`-point chain (`q = n − 1`) -/
def tauq (n : ℕ) : ℝ := (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)

lemma tauq_pos {n : ℕ} (hn : 2 ≤ n) : 0 < tauq n := by
  unfold tauq
  have : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
  positivity

lemma gtau_of_le {τ E : ℝ} (h : E ≤ τ) : gtau τ E = E := by
  simp [gtau, h]

lemma gtau_of_gt {τ E : ℝ} (h : τ < E) : gtau τ E = 2 * Real.sqrt (τ * E) - τ := by
  simp [gtau, not_le.mpr h]

/-- on the √ branch, `√(τE) ≥ τ` -/
lemma tau_le_sqrt_mul {τ E : ℝ} (hτ : 0 < τ) (h : τ < E) : τ ≤ Real.sqrt (τ * E) := by
  have hs0 := Real.sqrt_nonneg (τ * E)
  have hs2 := Real.sq_sqrt (show 0 ≤ τ * E by nlinarith)
  nlinarith [mul_lt_mul_of_pos_left h hτ]

lemma gtau_le_self {τ E : ℝ} (hτ : 0 < τ) : gtau τ E ≤ E := by
  unfold gtau
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have hs2 := Real.sq_sqrt (show 0 ≤ τ * E by nlinarith)
    nlinarith [sq_nonneg (Real.sqrt (τ * E) - τ)]

lemma gtau_pos {τ E : ℝ} (hτ : 0 < τ) (hE : 0 < E) : 0 < gtau τ E := by
  rcases le_or_gt E τ with h | h
  · rw [gtau_of_le h]; exact hE
  · rw [gtau_of_gt h]; linarith [tau_le_sqrt_mul hτ h]

lemma gtau_nonneg {τ E : ℝ} (hτ : 0 < τ) (hE : 0 ≤ E) : 0 ≤ gtau τ E := by
  rcases hE.lt_or_eq with h | h
  · exact (gtau_pos hτ h).le
  · rw [← h, gtau_of_le hτ.le]

lemma gtau_mono {τ x y : ℝ} (hτ : 0 < τ) (hxy : x ≤ y) : gtau τ x ≤ gtau τ y := by
  rcases le_or_gt y τ with hy | hy
  · rw [gtau_of_le hy, gtau_of_le (hxy.trans hy)]; exact hxy
  rcases le_or_gt x τ with hx | hx
  · rw [gtau_of_le hx, gtau_of_gt hy]; linarith [tau_le_sqrt_mul hτ hy]
  · rw [gtau_of_gt hx, gtau_of_gt hy]
    have := Real.sqrt_le_sqrt (show τ * x ≤ τ * y by nlinarith)
    linarith

/-- the increments of `gtau` are at most those of the identity -/
lemma gtau_lip {τ x y : ℝ} (hτ : 0 < τ) (hxy : x ≤ y) : gtau τ y - gtau τ x ≤ y - x := by
  rcases le_or_gt y τ with hy | hy
  · rw [gtau_of_le hy, gtau_of_le (hxy.trans hy)]
  rcases le_or_gt x τ with hx | hx
  · rw [gtau_of_le hx]; linarith [gtau_le_self (E := y) hτ]
  · rw [gtau_of_gt hx, gtau_of_gt hy]
    set a := Real.sqrt (τ * x) with ha
    set b := Real.sqrt (τ * y) with hb
    have ha2 : a ^ 2 = τ * x := Real.sq_sqrt (by nlinarith)
    have hb2 : b ^ 2 = τ * y := Real.sq_sqrt (by nlinarith)
    have haτ : τ ≤ a := tau_le_sqrt_mul hτ hx
    have hbτ : τ ≤ b := tau_le_sqrt_mul hτ hy
    have hab : a ≤ b := Real.sqrt_le_sqrt (by nlinarith)
    have h1 : 0 ≤ (b - a) * (a + b - 2 * τ) := mul_nonneg (by linarith) (by linarith)
    -- `τ (y − x) = b² − a² ≥ 2τ (b − a)`
    have h2 : 2 * τ * (b - a) ≤ τ * (y - x) := by nlinarith
    nlinarith

/-- **the rational form of the final κ step**: `s ≥ 0`, `s² ≤ τA`, `τ < A` give `2s − τ ≤ gtau τ A` -/
lemma two_mul_sub_le_gtau {τ A s : ℝ} (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ τ * A) (hA : τ < A) :
    2 * s - τ ≤ gtau τ A := by
  rw [gtau_of_gt hA]
  have : s ≤ Real.sqrt (τ * A) := by
    calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs).symm
      _ ≤ Real.sqrt (τ * A) := Real.sqrt_le_sqrt hs2
  linarith

/-! ### the band profile with its √ branch -/

section BandProfileSqrt

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The band profile with its √ branch** (AMTOPA, after Gebendorfer Lemma 3.3), for any Hermitian `G`, injective
ranking `r` and `q ≥ 1`: `gtau ((q+1)/q) (bandSq G r q) ≤ defect`. -/
theorem band_profile_sqrt {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (r : κ → ℕ) (hr : Function.Injective r)
    (q : ℕ) (hq : 1 ≤ q) : gtau (((q : ℝ) + 1) / q) (bandSq G r q) ≤ defect hG := by
  obtain ⟨U, hUU, hUU', hG1⟩ : ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      G - 1 = U * diagonal (fun i => ((hG.eigenvalues i - 1 : ℝ) : ℂ)) * star U :=
    ⟨_, Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2, Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2,
      by rw [← specMap_sub_one hG]; unfold specMap; rw [Unitary.conjStarAlgAut_apply]; rfl⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- the two traces of the band part
  have hYG : rtrace (bpBand G r q * (G - 1)) = bandSq G r q := by
    unfold rtrace bandSq
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, RCLike.re_to_complex]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bpBand]
    split_ifs with hb
    · rw [Matrix.sub_apply, Matrix.one_apply_ne (Ne.symm hb.1), sub_zero, ← hG.apply j i, RCLike.star_def,
        RCLike.mul_conj]
      norm_cast
    · simp
  have hYY : rtrace (bpBand G r q * (bpBand G r q)ᴴ) = bandSq G r q := by
    rw [rtrace_self_mul_conjTranspose, sum_comm]
    unfold bandSq
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bpBand]
    split_ifs <;> simp
  obtain ⟨E, hE⟩ : ∃ E, bandSq G r q = E := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, ((q : ℝ) + 1) / q = τ := ⟨_, rfl⟩
  rw [hE, hτ]
  rw [hE] at hYG hYY
  have hτ0 : 0 < τ := by rw [← hτ]; positivity
  -- each eigenvector is a unit vector, and the band form on it is at most `E/τ`
  have hcol : ∀ i, ∑ j, ‖U j i‖ ^ 2 = 1 := by
    intro i
    have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have h := congrArg Complex.re (congrFun (congrFun hUU' i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum, Complex.one_re] at h
    simpa only [hre] using h
  have hz : ∀ i, ‖(star U * bpBand G r q * U) i i‖ ^ 2 * τ ≤ E := by
    intro i
    have hexp : (star U * bpBand G r q * U) i i = ∑ j, ∑ k, star (U j i) * bpBand G r q j k * U k i := by
      simp only [Matrix.mul_apply, Matrix.star_apply, sum_mul]
      exact sum_comm
    have hb := bp_band_quad G r hr q (fun j => U j i)
    beta_reduce at hb
    rw [hcol i, one_pow, mul_one, hE] at hb
    rw [hexp]
    calc ‖∑ j, ∑ k, star (U j i) * bpBand G r q j k * U k i‖ ^ 2 * τ ≤ E * ((q : ℝ) / (q + 1)) * τ := by
          gcongr
      _ = E := by rw [← hτ]; field_simp
  -- `A = 2αY` with `α² E ≤ τ` gives `defect ≥ (2α − α²) E`
  have key : ∀ α : ℝ, 0 ≤ α → α ^ 2 * E ≤ τ → (2 * α - α ^ 2) * E ≤ defect hG := by
    intro α hα hαE
    have hF := bp_fenchel hG U hUU hG1 ((((2 * α : ℝ)) : ℂ) • bpBand G r q) (fun i => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      have h1 := Complex.re_le_norm ((star U * bpBand G r q * U) i i)
      have h2 : (α * ‖(star U * bpBand G r q * U) i i‖) ^ 2 ≤ 1 := by
        have h4 : α ^ 2 * (‖(star U * bpBand G r q * U) i i‖ ^ 2 * τ) ≤ α ^ 2 * E :=
          mul_le_mul_of_nonneg_left (hz i) (sq_nonneg α)
        have h5 : (α * ‖(star U * bpBand G r q * U) i i‖) ^ 2 * τ ≤ 1 * τ := by nlinarith
        exact le_of_mul_le_mul_right h5 hτ0
      have h3 : α * ‖(star U * bpBand G r q * U) i i‖ ≤ 1 := by
        nlinarith [mul_nonneg hα (norm_nonneg ((star U * bpBand G r q * U) i i))]
      nlinarith)
    have h1 : rtrace ((((2 * α : ℝ)) : ℂ) • bpBand G r q * (G - 1)) = 2 * α * E := by
      rw [Matrix.smul_mul]
      unfold rtrace at hYG ⊢
      rw [Matrix.trace_smul, smul_eq_mul, RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, hYG]
    have h2 : rtrace ((((2 * α : ℝ)) : ℂ) • bpBand G r q * ((((2 * α : ℝ)) : ℂ) • bpBand G r q)ᴴ)
        = 4 * α ^ 2 * E := by
      rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      unfold rtrace at hYY ⊢
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.re_ofReal_mul,
        ← RCLike.re_to_complex, hYY]
      ring
    rw [h1, h2] at hF
    linarith
  rcases le_or_gt E τ with h | h
  · -- `α = 1`
    rw [gtau_of_le h]
    have := key 1 zero_le_one (by simpa using h)
    linarith
  · -- `α = √(τE)/E`: `α² E = τ` and `(2α − α²) E = 2√(τE) − τ`
    rw [gtau_of_gt h]
    have hEpos : 0 < E := hτ0.trans h
    have hE0 : E ≠ 0 := hEpos.ne'
    set s := Real.sqrt (τ * E) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = τ * E := Real.sq_sqrt (by positivity)
    have hα2 : (s / E) ^ 2 * E = τ := by
      rw [div_pow, hs2]; field_simp
    have := key (s / E) (div_nonneg hs0 hEpos.le) hα2.le
    have e : (2 * (s / E) - (s / E) ^ 2) * E = 2 * s - τ := by
      calc (2 * (s / E) - (s / E) ^ 2) * E = 2 * (s / E * E) - (s / E) ^ 2 * E := by ring
        _ = 2 * s - τ := by rw [hα2, div_mul_cancel₀ s hE0]
    linarith

end BandProfileSqrt

/-! ### the block bound under the profile -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The block bound with the √ branch**: `gtau τ (c (m − q)) − 2 m² δ ≤ blockDefect + pressure`, `τ = (q+1)/q`,
`q = n − 1`, with no cap on `c (m − q)` (monotonicity of `gtau`, and its increments at most the identity's). -/
theorem block_bound_w'_g {κ : Type} [Fintype κ] [DecidableEq κ] {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (x : κ → ℝ) {G : Matrix κ κ ℂ} (hG : G.PosSemidef) (B : Finset κ) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + blkPress W.b x B := by
  classical
  set x' : B → ℝ := fun i => x i with hx'def
  have hx' : Function.Injective x' := fun i j h => Subtype.ext (hx i.2 j.2 h)
  have hcard : Fintype.card B = m := by simp [hB]
  have hS : (univ.image x').card = m := by rw [card_image_of_injective _ hx', card_univ, hcard]
  have hE := block_energy_band hn W hW hCert hm x' hx' hS
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hPe : blkPress W.b x' univ = blkPress W.b x B := by
    unfold blkPress sortedOn
    rw [sortedOn_congr himg, himg]
  rw [hPe] at hE
  have hcl' : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ) i j - (kfun (x' i - x' j) : ℂ)‖ ≤ δ :=
    fun i j h => hclose i i.2 j j.2 (fun e => h (Subtype.ext e))
  have hC := band_close hx' hS hcard (n - 1) (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) hδ hcl'
  have hprof : gtau (tauq n)
      (bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1))
        ≤ blockDefect hG.1 B :=
    band_profile_sqrt (hG.1.submatrix (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ))
      (fun i j h => sRank_injective hx' hS (Fin.ext h)) (n - 1) (by omega)
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
  have hτ : 0 < tauq n := tauq_pos hn
  set Bq := bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1)
    with hBq
  set K : ℝ := 2 * (m : ℝ) ^ 2 * δ + blkPress W.b x B with hK
  have hA : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ Bq + K := by rw [hK]; linarith
  have h1 := gtau_mono hτ hA
  have h2 := gtau_lip hτ (show Bq ≤ Bq + K by rw [hK]; linarith)
  linarith

open Filter Zeta23 Zeta23.ZeroSide Zeta23.ThmD
open Classical

theorem block_bound_eventually_w'_g (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + blkPress W.b (xret Z (mtParams T) T) B := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  have hτ : 0 < tauq n := tauq_pos hn
  set A : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H ((|A| + 1) / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ (|A| + 1) / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w'_g hn hm W hW hCert x (gram_posSemidef Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : |A| + 1 < blkPress W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [div_lt_div_iff_of_pos_right hbmin] at this
      exact this
    have hg : gtau (tauq n) A ≤ |A| := (gtau_le_self hτ).trans (le_abs_self A)
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]

theorem pre_solve_w'_g (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hmq : (1 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith
  have hτ : 0 < tauq n := tauq_pos hn
  have hA₀pos : 0 < gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) :=
    gtau_pos hτ (mul_pos hc (by linarith))
  have hq0 : (0 : ℝ) ≤ W.B := WCert.B_nonneg hW
  set A₀ : ℝ := gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) with hA₀
  set Cn : ℝ := (m : ℝ) + (2 * A₀ + 1) + W.B * ((m : ℝ) - ((n : ℝ) - 1)) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    rw [hCn]; nlinarith
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ A₀ := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ A₀ ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ A₀ ≤ A₀ := min_le_right _ _
  have hA' : 0 ≤ A₀ - min ε₀ A₀ := by linarith
  filter_upwards [block_bound_eventually_w'_g Z H hn3 h2n W hW hbmin hb hCert hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop ((m : ℝ) / min ε₀ A₀),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL
  have h15 := offset_average_w hn W.b hW.b_nonneg (xret Z (mtParams T) T)
    (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (A₀ - min ε₀ A₀)
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
  have hmN : (m : ℝ) ≤ min ε₀ A₀ * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith
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
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - (2 * A₀ + 1) * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by nlinarith [e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (AMW.HW - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + (2 * A₀ + 1) + q * mq) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + (2 * A₀ + 1) + q * mq) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + (2 * A₀ + 1) + q * mq) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * AMW.HW - q * mq - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (AMW.HW - q * mq / m - ε) * N
      = ((m : ℝ) * AMW.HW - q * mq - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

/-- the n-point constant under the √-branch profile -/
def Phi_g (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (AMW.HW - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) / m)

lemma one_sub_gtau_div_pos {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m) :
    0 < 1 - gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have := gtau_le_self (E := c * ((m : ℝ) - ((n : ℝ) - 1))) (tauq_pos hn)
  rw [sub_pos, div_lt_one hmpos]
  linarith

theorem n_point_bound_w'_g (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_g n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have hn : 2 ≤ n := by omega
  have hD := one_sub_gtau_div_pos hn (by omega : 0 < m) hcm
  set Dn : ℝ := 1 - gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) / m with hDn
  set K : ℝ := AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m with hK
  have hpre := pre_solve_w'_g zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at hpre
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hpre (ε * Dn) (mul_pos hε hD))
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hPhi : Phi_g n c m W.B - ε = (K - ε * Dn) / Dn := by
    unfold Phi_g
    rw [← hK, ← hDn]
    field_simp
  rw [hPhi, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

/-- the final κ step on the √ branch: rational data `s ≥ 0` with `s² ≤ τ A` and `τ < A` (`A = c (m − q)`), and
`κ (1 − (2s − τ)/m) ≤ h − B (m − q)/m` with `h ≤ H_W`, give `κ ≤ Phi_g` -/
theorem Phi_g_ge_sqrt {n : ℕ} {c B κ h s : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hH : h ≤ AMW.HW)
    (hκ0 : 0 ≤ κ) (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ tauq n * (c * ((m : ℝ) - ((n : ℝ) - 1))))
    (hA : tauq n < c * ((m : ℝ) - ((n : ℝ) - 1))) (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hk : κ * (1 - (2 * s - tauq n) / m) ≤ h - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) :
    κ ≤ Phi_g n c m B := by
  have hD := one_sub_gtau_div_pos hn hm hcm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hg := two_mul_sub_le_gtau hs hs2 hA
  have h1 : 1 - gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) / m ≤ 1 - (2 * s - tauq n) / m := by
    have := div_le_div_of_nonneg_right hg hmpos.le
    linarith
  unfold Phi_g
  rw [le_div_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ0]

/-- the final κ step on the linear branch (`c (m − q) ≤ τ`) -/
theorem Phi_g_ge_lin {n : ℕ} {c B κ h : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hH : h ≤ AMW.HW)
    (hA : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ tauq n) (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hk : κ * (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) ≤ h - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) :
    κ ≤ Phi_g n c m B := by
  have hD := one_sub_gtau_div_pos hn hm hcm
  rw [gtau_of_le hA] at hD
  unfold Phi_g
  rw [gtau_of_le hA, le_div_iff₀ hD]
  linarith

end Zeta23Ext.BridgeW

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- **The n-point bound for the AM window under the √-branch band profile**, from a certificate; no cap on
`c (m − q)` beyond `c (m − q) < m`. -/
theorem am_dyadic_n_g {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hκ : κ ≤ Phi_g n c m W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w'_g n c m W hn hm hW hbmin hb hc hcm hCert ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_g n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- the cumulative form -/
theorem am_cumulative_n_g {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hκ : κ ≤ Phi_g n c m W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic_n_g hn hW hbmin hb hc hm hcm hκ hCert)

end AMW

end
