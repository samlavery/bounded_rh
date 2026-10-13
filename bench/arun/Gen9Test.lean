import CandMOPX

/-! n-generic copy of the Opeth AM chain (band width n − 1), developed against the compiled skeleton. -/

noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW

namespace OpethN

/-- Knausgard's `card_near_le` (Pantera.Transfer, k = 7), with the band width `k` as a parameter. -/
theorem card_near_le_k (ℓ k : ℕ) (i : Fin ℓ) :
    (univ.filter fun j : Fin ℓ =>
      i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + k ∧ (j : ℕ) ≤ (i : ℕ) + k).card ≤ 2 * k := by
  have h1 : (univ.filter fun j : Fin ℓ =>
        i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + k ∧ (j : ℕ) ≤ (i : ℕ) + k).card
      ≤ ((Icc ((i : ℕ) - k) ((i : ℕ) + k)).erase (i : ℕ)).card := by
    refine card_le_card_of_injOn (fun j : Fin ℓ => (j : ℕ)) ?_ ?_
    · intro j hj
      have hj' := (mem_filter.mp (mem_coe.mp hj)).2
      refine mem_coe.mpr (mem_erase.mpr ⟨fun h => hj'.1 (Fin.ext h.symm), mem_Icc.mpr ?_⟩)
      have := hj'.2
      show (i : ℕ) - k ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + k
      omega
    · intro a _ b _ hab
      exact Fin.ext hab
  have h2 : ((Icc ((i : ℕ) - k) ((i : ℕ) + k)).erase (i : ℕ)).card ≤ 2 * k := by
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Nat.card_Icc]
    omega
  exact h1.trans h2

section Sparse
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `AMSparseDefect.seven_band_close` with band width `n − 1`: error `4(n − 1)δ` per point. -/
theorem band_close_n (n : ℕ) {x : ι → ℝ} (hx : Function.Injective x)
    {m : ℕ} (hS : (univ.image x).card = m) (hcard : Fintype.card ι = m)
    (G : Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0)
      ≤ offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
  classical
  set e := Equiv.ofBijective _ (sRank_bijective hx hS hcard) with he
  set R : ι → ℕ := fun i => (sRank x hS i : ℕ) with hR
  set C : ι → ι → Prop := fun i j =>
    i ≠ j ∧ R i ≤ R j + (n - 1) ∧ R j ≤ R i + (n - 1) with hC
  set F : ι → ι → ℝ := fun i j =>
    if C i j then wfun (x i - x j) else 0 with hF
  have hsum : (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0) =
      ∑ i, ∑ j, F i j := by
    rw [Fintype.sum_prod_type, ← e.sum_comp]
    apply sum_congr rfl
    intro i _
    rw [← e.sum_comp]
    apply sum_congr rfl
    intro j _
    simp only [he, Equiv.ofBijective_apply, sRank_val, hF, hC, hR,
      ne_eq, (sRank_injective hx hS).eq_iff]
  have hnear (i : ι) : (univ.filter (C i)).card ≤ 2 * (n - 1) := by
    have hinj : (univ.filter (C i)).card ≤
        (univ.filter fun j : Fin m => sRank x hS i ≠ j ∧
          (sRank x hS i : ℕ) ≤ (j : ℕ) + (n - 1) ∧
          (j : ℕ) ≤ (sRank x hS i : ℕ) + (n - 1)).card := by
      apply card_le_card_of_injOn (fun j : ι => sRank x hS j)
      · intro j hj
        have hj' := (mem_filter.mp (mem_coe.mp hj)).2
        refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, ?_⟩)
        exact ⟨fun h => hj'.1 (sRank_injective hx hS h), hj'.2⟩
      · intro a _ b _ hab
        exact sRank_injective hx hS hab
    exact hinj.trans (card_near_le_k m (n - 1) (sRank x hS i))
  have hterm (i j : ι) : F i j ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) +
        (if C i j then 2 * δ else 0) := by
    change (if C i j then wfun (x i - x j) else 0) ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) + (if C i j then 2 * δ else 0)
    by_cases hc : C i j
    · simp only [if_pos hc, if_pos hc.1]
      exact sub_le_iff_le_add.mp (wfun_sub_le_norm_sq (hclose i j hc.1))
    · simp only [if_neg hc, add_zero]
      split_ifs <;> positivity
  have hcount (i : ι) :
      (∑ j, if C i j then 2 * δ else 0) ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc : ((univ.filter (C i)).card : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnear i
    have h2δ : (0 : ℝ) ≤ 2 * δ := mul_nonneg (by norm_num) hδ
    have h := mul_le_mul_of_nonneg_right hc h2δ
    nlinarith only [h]
  rw [hsum]
  calc
    (∑ i, ∑ j, F i j) ≤ ∑ i, ∑ j,
        ((if i ≠ j then ‖G i j‖ ^ 2 else 0) +
          (if C i j then 2 * δ else 0)) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hterm i j))
    _ = offDiagSqOn G univ + ∑ i, ∑ j,
        (if C i j then 2 * δ else 0) := by
      simp only [sum_add_distrib, offDiagSqOn, ne_eq, ite_not]
    _ ≤ offDiagSqOn G univ + ∑ _i : ι, 4 * ((n - 1 : ℕ) : ℝ) * δ :=
      add_le_add le_rfl (sum_le_sum (fun i _ => hcount i))
    _ = offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
      rw [sum_const, card_univ, hcard, nsmul_eq_mul]
      ring

/-- `AMRemainder.pressure_le` for `WCert n`. -/
theorem pressure_le_n {n : ℕ} {x : ι → ℝ} {m : ℕ}
    (hm : n ≤ m) (hS : (univ.image x).card = m)
    (W : WCert n) (hb : ∀ r, 0 ≤ W.b r) {R : ℝ}
    (hspan : ∀ i j, x i - x j ≤ R) :
    blkPress W.b x univ ≤ W.B * R := by
  classical
  have hmem (k : ℕ) (hk : k < m) : sortedOn x univ k ∈ univ.image x := by
    rw [sortedOn_eq hS, sortedExt_of_lt _ hk]
    exact Finset.orderEmbOfFin_mem _ hS _
  unfold blkPress
  rw [hS]
  calc
    (∑ r : Fin (n - 1), W.b r *
        (sortedOn x univ (m - (n - 1) + r) - sortedOn x univ r))
        ≤ ∑ r : Fin (n - 1), W.b r * R := by
      apply sum_le_sum
      intro r _
      have hr := r.isLt
      obtain ⟨i, _, hi⟩ := mem_image.mp (hmem (m - (n - 1) + r) (by omega))
      obtain ⟨j, _, hj⟩ := mem_image.mp (hmem r (by omega))
      apply mul_le_mul_of_nonneg_left _ (hb r)
      rw [← hi, ← hj]
      exact hspan i j
    _ = W.B * R := by rw [← sum_mul]; rfl

/-- `AMRemainder.remainder_bound` for `WCert n`: `(c − 4(n−1)δ)·m − B·R − (n−1)·c ≤ defect`. -/
theorem remainder_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  classical
  set m := Fintype.card ι with hmdef
  have hcard : Fintype.card ι = m := rfl
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  have hB : 0 ≤ W.B := WCert.B_nonneg hW
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hk0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hm : n ≤ m
  · have he := block_energy_band hn W hW hCert hm x hx hS
    have hb := band_close_n n hx hS hcard G hδ hclose
    have hp := pressure_le_n hm hS W hW.b_nonneg hspan
    have hd := Opeth.AMSparseDefect.offdiag_le_defect_of_spectrum_le_two hG hcap
    rw [← hk] at he
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG
    nlinarith only [he, hb, hp, hd]
  · have hmk : m ≤ n - 1 := by omega
    have hmk' : (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmk
    have hcm := mul_le_mul_of_nonneg_left hmk' hc
    have hbr : 0 ≤ W.B * R := mul_nonneg hB hR
    have hdm : 0 ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ * (m : ℝ) := by positivity
    have hd := Opeth.AMSparseDefect.defect_nonneg hG
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG
    nlinarith only [hcm, hbr, hdm, hd]

/-- `AMRemainder.block_remainder_bound` for `WCert n`. -/
theorem block_remainder_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (B : Finset ι)
    (hcap : ∀ i, (hG.submatrix (Subtype.val : B → ι)).eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (B.card : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ blockDefect hG B := by
  classical
  have hxB : Function.Injective (fun i : B => x i) := fun i j h =>
    Subtype.ext (hx h)
  have hcloseB : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) i j -
        (kfun (x i - x j) : ℂ)‖ ≤ δ := fun i j hij =>
    hclose i j (fun h => hij (Subtype.ext h))
  have h := remainder_bound_n hn hxB (hG.submatrix (Subtype.val : B → ι)) hc W hW hCert
    hδ hcloseB hcap hR (fun i j => hspan i j)
  simpa only [Fintype.card_coe, blockDefect] using h

end Sparse

section Matching
open Meshuggah.Gram
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `AMMatching.matching_defect_bound` for `WCert n`. -/
theorem matching_defect_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (hcPair : c ≤ 1 / 64)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → 17 / 20 ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  classical
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  obtain ⟨σ, hσ, hσsep⟩ := exists_maximal_matching x (17 / 20)
  let S : Option (Sym2 ι) → Finset ι :=
    fun z => univ.filter (fun i => matchLabel σ i = z)
  have hpinch : (∑ z, blockDefect hG (S z)) ≤ defect hG :=
    pinching_partition hG (Option (Sym2 ι)) (matchLabel σ)
  have hblock (z : Option (Sym2 ι)) :
      (c - 4 * k * δ) * ((S z).card : ℝ) -
        (if z = none then W.B * R + k * c else 0) ≤ blockDefect hG (S z) := by
    cases z with
    | none =>
      rw [if_pos rfl]
      have hfixed (i : S none) : σ i = i :=
        matchLabel_eq_none.mp ((mem_filter.mp i.property).2)
      have hsep : ∀ i j : S none, i ≠ j → 17 / 20 ≤ |x i - x j| := by
        intro i j hij
        exact hσsep i j (hfixed i) (hfixed j)
          (fun h => hij (Subtype.ext h))
      have hb := block_remainder_bound_n hn hx hG hc W hW hCert
        hδ hclose (S none) (hcap (S none) hsep) hR hspan
      linarith only [hb]
    | some z =>
      rw [if_neg (Option.some_ne_none z), sub_zero]
      by_cases hne : (S (some z)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have hiLabel : matchLabel σ i = some z := (mem_filter.mp hi).2
        obtain ⟨hiMove, hiPair⟩ := matchLabel_eq_some.mp hiLabel
        subst z
        have hpair : S (some s(i, σ i)) = {i, σ i} := by
          ext l
          change l ∈ univ.filter (fun j => matchLabel σ j = some s(i, σ i)) ↔
            l ∈ ({i, σ i} : Finset ι)
          simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
          constructor
          · exact eq_or_eq_of_matchLabel
          · intro hl
            rcases hl with rfl | rfl
            · exact matchLabel_eq_some.mpr ⟨hiMove, rfl⟩
            · exact matchLabel_partner hσ.invol hiMove
        have hij : i ≠ σ i := fun h => hiMove h.symm
        have hb := Opeth.AMMatching.close_pair_block_bound hG hcPair hδ hclose hij
          (hσ.close i hiMove).le
        rw [hpair]
        have hcard : ({i, σ i} : Finset ι).card = 2 := by simp [hij]
        rw [hcard]
        have hkδ : δ ≤ k * δ := le_mul_of_one_le_left hδ hk1
        norm_num only [Nat.cast_ofNat]
        linarith only [hb, hδ, hkδ]
      · have hempty : S (some z) = ∅ := not_nonempty_iff_eq_empty.mp hne
        rw [hempty, card_empty, Nat.cast_zero, mul_zero]
        exact blockDefect_nonneg hG ∅
  have hcardsNat : (∑ z : Option (Sym2 ι), (S z).card) = Fintype.card ι := by
    simpa only [S, mem_univ, filter_true, card_univ] using
      (sum_card_fiberwise_eq_card_filter (univ : Finset ι)
        (univ : Finset (Option (Sym2 ι))) (matchLabel σ))
  have hcards : (∑ z : Option (Sym2 ι), ((S z).card : ℝ)) =
      (Fintype.card ι : ℝ) := by
    exact_mod_cast hcardsNat
  have hcharge : (∑ z : Option (Sym2 ι),
      if z = none then W.B * R + k * c else 0) = W.B * R + k * c := by
    simp
  calc
    (c - 4 * k * δ) * (Fintype.card ι : ℝ) - W.B * R - k * c =
        ∑ z : Option (Sym2 ι), ((c - 4 * k * δ) * ((S z).card : ℝ) -
          (if z = none then W.B * R + k * c else 0)) := by
      rw [sum_sub_distrib, ← mul_sum, hcards, hcharge]
      ring
    _ ≤ ∑ z, blockDefect hG (S z) := sum_le_sum (fun z _ => hblock z)
    _ ≤ defect hG := hpinch

end Matching

end OpethN

end

noncomputable section
open Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge

namespace OpethN.Counting

open Classical

/-- `AMCounting.ActualDefectEstimate` for band width `n − 1` and constants `c`, `B`. -/
def ActualDefectEstimate (Z : ZeroConfig) (n : ℕ) (c B : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * ((retained Z (mtParams T) T).card : ℝ) -
        B * spanOf (xret Z (mtParams T) T) Finset.univ - ((n - 1 : ℕ) : ℝ) * c
      ≤ Dcirc Z (mtParams T) T

/-- `AMCounting.defect_to_dyadic` with `κ = (H⁻ − B)/(1 − c)`, `H⁻ = 67216841/10⁸`;
`δ = min (c/(8(n−1))) ((1 − c)ε/C)`, `C = 4(n − 1) + 2 + c + B`. -/
theorem defect_to_dyadic (Z : ZeroConfig) (H : PaperInputs Z) {n : ℕ} (hn : 2 ≤ n)
    {c B : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hB : 0 ≤ B)
    (hdef : ActualDefectEstimate Z n c B) :
    ∀ ε > (0 : ℝ), ∀ᶠ T in atTop,
      ((67216841 / 100000000 - B) / (1 - c) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  have hk0 : 0 < k := by linarith
  have hmu : 0 < 1 - c := sub_pos.mpr hc1
  set C : ℝ := 4 * k + 2 + c + B with hCdef
  have hC : 0 < C := by
    dsimp [C]
    linarith
  set δ : ℝ := min (c / (8 * k)) ((1 - c) * ε / C) with hδdef
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc0 (by positivity)) (div_pos (mul_pos hmu hε) hC)
  have hδcap : δ ≤ c / (8 * k) := min_le_left _ _
  have hδeps : δ ≤ (1 - c) * ε / C := min_le_right _ _
  have hbudget : C * δ ≤ (1 - c) * ε := by
    have h := (le_div_iff₀ hC).mp hδeps
    linarith only [h]
  have hcoef : 0 ≤ c - 4 * k * δ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mp hδcap
    nlinarith only [h, hc0]
  filter_upwards [hdef δ hδ, deleted_strips Z H δ hδ,
    span_retained_le Z H δ hδ, tail_passage Z H (eventually_h7 Z) δ hδ,
    (Zeta23.Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop (k * c / δ)]
    with T hd hstrip hspan htail hNlarge
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ)
  set m : ℝ := ((retained Z (mtParams T) T).card : ℝ)
  set R : ℝ := spanOf (xret Z (mtParams T) T) Finset.univ
  set D : ℝ := Dcirc Z (mtParams T) T
  change (c - 4 * k * δ) * m - B * R - k * c ≤ D at hd
  change n0 - δ * N ≤ m at hstrip
  change R ≤ (1 + δ) * N at hspan
  change (AMW.HW - δ) * N + D ≤ n0 at htail
  change k * c / δ ≤ N at hNlarge
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hn0N : n0 ≤ N := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    change (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ)
    exact_mod_cast h
  have hn := mul_le_mul_of_nonneg_left hstrip hcoef
  have hR := mul_le_mul_of_nonneg_left hspan hB
  have herr := mul_le_mul_of_nonneg_left hn0N
    (show 0 ≤ 4 * k * δ by positivity)
  have hδ2N : 0 ≤ 4 * k * δ * δ * N := by positivity
  have hD : c * n0 - B * N - (4 * k + c + B) * δ * N - k * c ≤ D := by
    nlinarith only [hd, hn, hR, herr, hδ2N]
  have hend : k * c ≤ δ * N := by
    have h := (div_le_iff₀ hδ).mp hNlarge
    nlinarith only [h]
  have hHW : (67216841 / 100000000 : ℝ) * N ≤ AMW.HW * N := by
    have h := AMW.HW_ge
    norm_num at h
    exact mul_le_mul_of_nonneg_right h hN0
  have hmain : ((67216841 / 100000000 : ℝ) - B - C * δ) * N ≤ (1 - c) * n0 := by
    dsimp [C]
    nlinarith only [hD, htail, hend, hHW]
  have hid : (1 - c) * ((67216841 / 100000000 - B) / (1 - c)) = 67216841 / 100000000 - B := by
    field_simp
  have hcoeff : (1 - c) * ((67216841 / 100000000 - B) / (1 - c) - ε) ≤
      (67216841 / 100000000 : ℝ) - B - C * δ := by
    rw [mul_sub, hid]
    linarith only [hbudget]
  have hscaled : (1 - c) * (((67216841 / 100000000 - B) / (1 - c) - ε) * N) ≤ (1 - c) * n0 := by
    calc
      _ = ((1 - c) * ((67216841 / 100000000 - B) / (1 - c) - ε)) * N := by ring
      _ ≤ ((67216841 / 100000000 : ℝ) - B - C * δ) * N :=
        mul_le_mul_of_nonneg_right hcoeff hN0
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_left hscaled hmu

end OpethN.Counting

end

noncomputable section
open Filter Topology Zeta23
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators

namespace OpethN.ActualDefect

open Classical

/-- `AMActualDefect.actual_defect_estimate` for `WCert n`. -/
theorem actual_defect_estimate (Z : ZeroConfig) {n : ℕ} (hn : 2 ≤ n) (W : WCert n)
    (hW : W.Adm) {c B : ℝ} (hc0 : 0 ≤ c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    OpethN.Counting.ActualDefectEstimate Z n c B := by
  intro δ hδ
  filter_upwards [Opeth.AMUniformKernel.kernel_limit_uniform Z δ hδ,
    Opeth.AMSeparatedSpectrum.eventually_principal_eigenvalues_le_two Z,
    eventually_L_pos] with T hclose hcap hL
  have hx := xret_injective Z (mtParams T) T hL
  have hspan : ∀ i j : retained Z (mtParams T) T,
      xret Z (mtParams T) T i - xret Z (mtParams T) T j ≤
        spanOf (xret Z (mtParams T) T) Finset.univ := by
    intro i j
    exact (le_abs_self _).trans
      (abs_sub_le_spanOf (xret Z (mtParams T) T)
        (Finset.mem_univ i) (Finset.mem_univ j))
  have h := OpethN.matching_defect_bound_n hn hx
    (gram_isHermitian Z (mtParams T) T) hc0 hc64
    W hW hCert hδ.le (fun i j _ => hclose i j) hcap
    (spanOf_nonneg (xret Z (mtParams T) T) Finset.univ) hspan
  simpa only [Fintype.card_coe, hB, Dcirc] using h

/-- the dyadic count for any admissible `n`-point certificate with floor `c ∈ (0, 1/64]` and pressure `B` -/
theorem actual_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm) {c B : ℝ}
    (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((67216841 / 100000000 - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
  have hdef := actual_defect_estimate zetaZeroConfig hn W hW hc0.le hc64 hB hCert
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (OpethN.Counting.defect_to_dyadic zetaZeroConfig paperInputs_zeta hn hc0
      (by linarith) hB0 hdef ε hε)
  refine ⟨T₀, fun T hT => ?_⟩
  have hs : ((67216841 / 100000000 - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
      (Zeta23.N0simple T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hT₀ T hT
  have hline : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast AMW.N0simple_le_N0star' T (2 * T)
  exact hs.trans hline

/-- the cumulative count -/
theorem actual_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm) {c B : ℝ}
    (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((67216841 / 100000000 - B) / (1 - c) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (actual_dyadic hn W hW hc0 hc64 hB hCert)

end OpethN.ActualDefect

end

/-! the current eight-point certificate through the generic chain -/
noncomputable section
open Zeta23 Zeta23Ext.BridgeW

namespace OpethN.Final

theorem actual_dyadic :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((66812491 / 99194876 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  have h := OpethN.ActualDefect.actual_dyadic (by norm_num : 2 ≤ 8) RiemannFail.W8 RiemannFail.W8_adm
    (by norm_num : (0 : ℝ) < 805124 / 100000000) (by norm_num) RiemannFail.W8_B RiemannFail.cert_AM
  have e : ((67216841 / 100000000 - (404350 : ℝ) / 100000000) / (1 - (805124 : ℝ) / 100000000))
      = 66812491 / 99194876 := by norm_num
  simpa only [e] using h

theorem actual_cumulative :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((66812491 / 99194876 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T := by
  have h := OpethN.ActualDefect.actual_cumulative (by norm_num : 2 ≤ 8) RiemannFail.W8 RiemannFail.W8_adm
    (by norm_num : (0 : ℝ) < 805124 / 100000000) (by norm_num) RiemannFail.W8_B RiemannFail.cert_AM
  have e : ((67216841 / 100000000 - (404350 : ℝ) / 100000000) / (1 - (805124 : ℝ) / 100000000))
      = 66812491 / 99194876 := by norm_num
  simpa only [e] using h

/-- the nine-point instantiation typechecks against an abstract certificate -/
example (W : WCert 9) (hW : W.Adm) {c B : ℝ} (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : ∀ g : Fin (9 - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((67216841 / 100000000 - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) :=
  OpethN.ActualDefect.actual_dyadic (by norm_num) W hW hc0 hc64 hB hCert

end OpethN.Final

end

#print axioms OpethN.Final.actual_dyadic
#print axioms OpethN.Final.actual_cumulative
