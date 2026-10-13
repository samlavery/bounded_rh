
/-- **`block_bound_w'` with the band profile**: the same block bound under `c (m − q) ≤ (q+1)/q` (`q = n − 1`) in
place of `c (m − q) ≤ 1`. The certificate's windows are rank-consecutive, so their pairs lie in the band `q` of the
sorted block, and `min ((q+1)/q) (band mass) ≤ defect` replaces `min 1 (off-diagonal mass) ≤ defect`. -/
theorem block_bound_w'_τ (hP : BandProfile) {κ : Type} [Fintype κ] [DecidableEq κ] {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
    (x : κ → ℝ) {G : Matrix κ κ ℂ} (hG : G.PosSemidef) (B : Finset κ) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
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
  have hcl' : ∀ i j : B, i ≠ j → ‖G.submatrix (Subtype.val : B → κ) i j - (kfun (x' i - x' j) : ℂ)‖ ≤ δ :=
    fun i j h => hclose i i.2 j j.2 (fun e => h (Subtype.ext e))
  have hC := band_close hx' hS hcard (n - 1) (G.submatrix (Subtype.val : B → κ)) hδ hcl'
  have hprof : min ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
      (bandSq (G.submatrix (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1))
        ≤ blockDefect hG.1 B :=
    hP B (G.submatrix (Subtype.val : B → κ)) (hG.submatrix _) (fun i => (sRank x' hS i : ℕ))
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
  rcases le_or_gt ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
      (bandSq (G.submatrix (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1)) with h1 | h1
  · rw [min_eq_left h1] at hprof
    linarith
  · rw [min_eq_right h1.le] at hprof
    linarith
