
/-! ### the band mass of a matrix, and the band profile (the `τ` version of `block_defect`) -/

/-- the band off-diagonal mass of `G` for a ranking `r`: the pairs at rank distance `1 … q` -/
def bandSq {κ : Type*} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℂ) (r : κ → ℕ) (q : ℕ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ r i ≤ r j + q ∧ r j ≤ r i + q then ‖G i j‖ ^ 2 else 0

/-- the band profile with `τ = (q+1)/q` (AMTOPA's band bound, after Gebendorfer): the hypothesis consumed by
`block_bound_w'_τ`; discharged by the band-profile theorem. -/
def BandProfile : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℂ) (hG : G.PosSemidef) (r : κ → ℕ),
    Function.Injective r → ∀ q : ℕ, 1 ≤ q → min (((q : ℝ) + 1) / q) (bandSq G r q) ≤ defect hG.1

/-- the rank of `i` in the sorted values of an injective `x` -/
def sRank (x : ι → ℝ) {m : ℕ} (hS : (univ.image x).card = m) (i : ι) : Fin m :=
  ((univ.image x).orderIsoOfFin hS).symm ⟨x i, mem_image_of_mem x (mem_univ i)⟩

lemma sRank_val (x : ι → ℝ) {m : ℕ} (hS : (univ.image x).card = m) (i : ι) :
    (univ.image x).orderEmbOfFin hS (sRank x hS i) = x i := by
  unfold sRank
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

lemma sRank_injective {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ} (hS : (univ.image x).card = m) :
    Function.Injective (sRank x hS) := by
  intro i j h
  apply hx
  rw [← sRank_val x hS i, ← sRank_val x hS j, h]

lemma sRank_bijective {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ} (hS : (univ.image x).card = m)
    (hcard : Fintype.card ι = m) : Function.Bijective (sRank x hS) :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨sRank_injective hx hS, by simp [hcard]⟩

/-- the sorted band energy is within `2 m² δ` of the band mass of a Gram matrix `δ`-close to `kfun` -/
theorem band_close {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ} (hS : (univ.image x).card = m)
    (hcard : Fintype.card ι = m) (q : ℕ) (G : Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    (∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + q ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + q
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0))
      - 2 * (m : ℝ) ^ 2 * δ ≤ bandSq G (fun i => (sRank x hS i : ℕ)) q := by
  classical
  set e := Equiv.ofBijective _ (sRank_bijective hx hS hcard) with he
  set R : ι → ℕ := fun i => (sRank x hS i : ℕ) with hR
  set C : ι → ι → Prop := fun i j => i ≠ j ∧ R i ≤ R j + q ∧ R j ≤ R i + q with hC
  set F : ι → ι → ℝ := fun i j => if C i j then wfun (x i - x j) else 0 with hF
  have hsum : (∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + q ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + q
        then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0))
      = ∑ i, ∑ j, F i j := by
    rw [Fintype.sum_prod_type, ← e.sum_comp]
    refine sum_congr rfl fun i _ => ?_
    rw [← e.sum_comp]
    refine sum_congr rfl fun j _ => ?_
    simp only [he, Equiv.ofBijective_apply, sRank_val, hF, hC, hR, ne_eq, (sRank_injective hx hS).eq_iff]
  rw [hsum]
  have hterm : ∀ i j, F i j - 2 * δ ≤ (if C i j then ‖G i j‖ ^ 2 else 0) := by
    intro i j
    simp only [hF]
    split_ifs with h
    · exact wfun_sub_le_norm_sq (hclose i j h.1)
    · linarith
  have hle : ∑ i, ∑ j, (F i j - 2 * δ) ≤ bandSq G R q :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
  have hsplit : ∑ i, ∑ j, (F i j - 2 * δ) = (∑ i, ∑ j, F i j) - 2 * (m : ℝ) ^ 2 * δ := by
    simp only [sum_sub_distrib, sum_const, card_univ, hcard, nsmul_eq_mul]; ring
  linarith
