import AMW.DEObjA

/-! ###### AMW/DEObjB — the block lower bound (bridge-port)

For a finite configuration with weights `m ≥ 0` and a kernel `K_T` within `δ` of `kfun(x − x')` on a sub-family `S'`
whose points lie in blocks `[a + jΛ, a + (j+1)Λ)` (`j < J`):
  `Σ_{ρ,ρ'} m m' K_T² ≥ [(1 − η)(ĥ(0) − ε)/(Λ + R) − δ²/η] Σ_j n_j² + (1 − η) g(0) Σ_{S'} m²`  (`block_bound`),
`n_j` the block masses.  Only intra-block pairs are kept (all terms are squares); on each block
`K_T² ≥ (1 − η) kfun² − δ²/η` (`sq_ge_of_close`) and the dip certificate `cert_T_free` applies to the block shifted
to `[0, Λ]`. ###### -/

noncomputable section

open Finset Real

namespace AMW.DE

/-- `G² ≥ (1 − η) k² − δ²/η` when `|G − k| ≤ δ` -/
theorem sq_ge_of_close {G k δ η : ℝ} (hη : 0 < η) (h : |G - k| ≤ δ) :
    (1 - η) * k ^ 2 - δ ^ 2 / η ≤ G ^ 2 := by
  set e := G - k with he
  have hG : G = k + e := by rw [he]; ring
  have he2 : e ^ 2 ≤ δ ^ 2 := by
    have := sq_abs e; rw [← this]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hcs : -(η * k ^ 2 + e ^ 2 / η) ≤ 2 * k * e := by
    have : 0 ≤ (η * k + e) ^ 2 / η := by positivity
    have e' : (η * k + e) ^ 2 / η = η * k ^ 2 + 2 * k * e + e ^ 2 / η := by field_simp; ring
    linarith
  have hd : e ^ 2 / η ≤ δ ^ 2 / η := div_le_div_of_nonneg_right he2 hη.le
  rw [hG]
  nlinarith [sq_nonneg e]

/-- only intra-block pairs: `Σ_j Σ_{B_j × B_j} F ≤ Σ_{I × I} F` for `F ≥ 0` -/
theorem sum_blocks_le {ι : Type*} [DecidableEq ι] (I S : Finset ι) (hS : S ⊆ I) (blk : ι → ℕ) (J : ℕ)
    (hJ : ∀ ρ ∈ S, blk ρ < J) (F : ι → ι → ℝ) (hF : ∀ ρ ρ', 0 ≤ F ρ ρ') :
    ∑ j ∈ range J, ∑ ρ ∈ S.filter (fun ρ => blk ρ = j), ∑ ρ' ∈ S.filter (fun ρ => blk ρ = j), F ρ ρ'
      ≤ ∑ ρ ∈ I, ∑ ρ' ∈ I, F ρ ρ' := by
  have h1 : ∑ j ∈ range J, ∑ ρ ∈ S.filter (fun ρ => blk ρ = j), ∑ ρ' ∈ S.filter (fun ρ => blk ρ = j), F ρ ρ'
      = ∑ ρ ∈ S, ∑ ρ' ∈ S.filter (fun ρ' => blk ρ' = blk ρ), F ρ ρ' := by
    rw [← sum_fiberwise_of_maps_to (g := blk) (t := range J) (fun ρ hρ => mem_range.mpr (hJ ρ hρ))
      (fun ρ => ∑ ρ' ∈ S.filter (fun ρ' => blk ρ' = blk ρ), F ρ ρ')]
    refine sum_congr rfl fun j _ => sum_congr rfl fun ρ hρ => ?_
    rw [(mem_filter.mp hρ).2]
  rw [h1]
  calc ∑ ρ ∈ S, ∑ ρ' ∈ S.filter (fun ρ' => blk ρ' = blk ρ), F ρ ρ'
      ≤ ∑ ρ ∈ S, ∑ ρ' ∈ I, F ρ ρ' :=
        sum_le_sum fun ρ _ => sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hS)
          fun ρ' _ _ => hF ρ ρ'
    _ ≤ ∑ ρ ∈ I, ∑ ρ' ∈ I, F ρ ρ' :=
        sum_le_sum_of_subset_of_nonneg hS fun ρ _ _ => sum_nonneg fun ρ' _ => hF ρ ρ'

/-- **the block lower bound** -/
theorem block_bound (c : PLCert) (hD : 0 < c.DkInv) (hG : CertGNonneg c) (hH : CertHNonneg c)
    {ε R : ℝ}
    (hR : ∀ (ι : Type) (s : Finset ι) (m x : ι → ℝ) (W : ℝ), 0 ≤ W → (∀ a, 0 ≤ m a) →
      (∀ a ∈ s, 0 ≤ x a ∧ x a ≤ W) →
      (qfAM 0 - c.y 0 - ε) * (∑ a ∈ s, m a) ^ 2 / (W + R) + gPL c 0 * ∑ a ∈ s, m a ^ 2
        ≤ ∑ a ∈ s, ∑ b ∈ s, m a * m b * wfunAM (x a - x b))
    {ι : Type} [DecidableEq ι] (I S : Finset ι) (hS : S ⊆ I) (m : ι → ℝ) (hm : ∀ ρ, 0 ≤ m ρ) (x : ι → ℝ)
    (Kt : ι → ι → ℝ) {a Λ δ η : ℝ} (hΛ : 0 < Λ) (hη : 0 < η) (hη1 : η ≤ 1) (J : ℕ)
    (hSx : ∀ ρ ∈ S, a ≤ x ρ ∧ ⌊(x ρ - a) / Λ⌋₊ < J)
    (hclose : ∀ ρ ∈ S, ∀ ρ' ∈ S, |Kt ρ ρ' - kfunAM (x ρ - x ρ')| ≤ δ) :
    ((1 - η) * (qfAM 0 - c.y 0 - ε) / (Λ + R) - δ ^ 2 / η)
        * ∑ j ∈ range J, (∑ ρ ∈ S.filter (fun ρ => ⌊(x ρ - a) / Λ⌋₊ = j), m ρ) ^ 2
      + (1 - η) * gPL c 0 * ∑ ρ ∈ S, m ρ ^ 2
      ≤ ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * Kt ρ ρ' ^ 2 := by
  set blk : ι → ℕ := fun ρ => ⌊(x ρ - a) / Λ⌋₊ with hblk
  set B : ℕ → Finset ι := fun j => S.filter (fun ρ => blk ρ = j) with hB
  set h0 := qfAM 0 - c.y 0 - ε with hh0
  -- the block coordinates lie in `[0, Λ]`
  have hpos : ∀ j, ∀ ρ ∈ B j, 0 ≤ x ρ - (a + j * Λ) ∧ x ρ - (a + j * Λ) ≤ Λ := by
    intro j ρ hρ
    obtain ⟨hρS, hρj⟩ := mem_filter.mp hρ
    have ha := (hSx ρ hρS).1
    have hq : 0 ≤ (x ρ - a) / Λ := div_nonneg (by linarith) hΛ.le
    have hfl := Nat.floor_le hq
    have hfl' := Nat.lt_floor_add_one ((x ρ - a) / Λ)
    simp only [hblk] at hρj
    rw [hρj] at hfl hfl'
    constructor
    · have := (le_div_iff₀ hΛ).mp hfl; linarith
    · have := (div_lt_iff₀ hΛ).mp hfl'; linarith
  -- one block
  have hblock : ∀ j, ((1 - η) * h0 / (Λ + R) - δ ^ 2 / η) * (∑ ρ ∈ B j, m ρ) ^ 2
      + (1 - η) * gPL c 0 * ∑ ρ ∈ B j, m ρ ^ 2
      ≤ ∑ ρ ∈ B j, ∑ ρ' ∈ B j, m ρ * m ρ' * Kt ρ ρ' ^ 2 := by
    intro j
    have hcert := hR ι (B j) m (fun ρ => x ρ - (a + j * Λ)) Λ hΛ.le hm (hpos j)
    simp only [sub_sub_sub_cancel_right] at hcert
    have hsq : ∀ ρ ∈ B j, ∀ ρ' ∈ B j, (1 - η) * wfunAM (x ρ - x ρ') - δ ^ 2 / η ≤ Kt ρ ρ' ^ 2 := by
      intro ρ hρ ρ' hρ'
      have := sq_ge_of_close hη (hclose ρ (mem_filter.mp hρ).1 ρ' (mem_filter.mp hρ').1)
      unfold wfunAM
      exact this
    have hlow : ∑ ρ ∈ B j, ∑ ρ' ∈ B j, m ρ * m ρ' * ((1 - η) * wfunAM (x ρ - x ρ') - δ ^ 2 / η)
        ≤ ∑ ρ ∈ B j, ∑ ρ' ∈ B j, m ρ * m ρ' * Kt ρ ρ' ^ 2 :=
      sum_le_sum fun ρ hρ => sum_le_sum fun ρ' hρ' =>
        mul_le_mul_of_nonneg_left (hsq ρ hρ ρ' hρ') (mul_nonneg (hm ρ) (hm ρ'))
    have hexp : ∑ ρ ∈ B j, ∑ ρ' ∈ B j, m ρ * m ρ' * ((1 - η) * wfunAM (x ρ - x ρ') - δ ^ 2 / η)
        = (1 - η) * ∑ ρ ∈ B j, ∑ ρ' ∈ B j, m ρ * m ρ' * wfunAM (x ρ - x ρ')
          - δ ^ 2 / η * (∑ ρ ∈ B j, m ρ) ^ 2 := by
      rw [sq (∑ ρ ∈ B j, m ρ), sum_mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun ρ _ => ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun ρ' _ => by ring
    have h1η : 0 ≤ 1 - η := by linarith
    have hc' := mul_le_mul_of_nonneg_left hcert h1η
    have e : ((1 - η) * h0 / (Λ + R) - δ ^ 2 / η) * (∑ ρ ∈ B j, m ρ) ^ 2
        + (1 - η) * gPL c 0 * ∑ ρ ∈ B j, m ρ ^ 2
        = (1 - η) * (h0 * (∑ ρ ∈ B j, m ρ) ^ 2 / (Λ + R) + gPL c 0 * ∑ ρ ∈ B j, m ρ ^ 2)
          - δ ^ 2 / η * (∑ ρ ∈ B j, m ρ) ^ 2 := by ring
    rw [e]
    linarith
  -- sum over the blocks
  have hsum := sum_le_sum fun j (_ : j ∈ range J) => hblock j
  have hdrop := sum_blocks_le I S hS blk J (fun ρ hρ => (hSx ρ hρ).2)
    (fun ρ ρ' => m ρ * m ρ' * Kt ρ ρ' ^ 2) (fun ρ ρ' => by have := hm ρ; have := hm ρ'; positivity)
  have hfib : ∑ j ∈ range J, ∑ ρ ∈ B j, m ρ ^ 2 = ∑ ρ ∈ S, m ρ ^ 2 :=
    sum_fiberwise_of_maps_to (g := blk) (t := range J) (fun ρ hρ => mem_range.mpr (hSx ρ hρ).2) _
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hfib] at hsum
  exact hsum.trans hdrop

end AMW.DE

end
