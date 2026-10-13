import AMW.AMTail

/-! ###### AMW/BrTau — the bridge's block bound under the band profile (stage G, track 1)

`block_defect` is the `τ = 1` case of AMTOPA's band bound (`min 1 (off-diagonal mass) ≤ defect`), which forces
`c (m − q) ≤ 1`.  With the band profile `min ((q+1)/q) (band mass) ≤ defect` (`BandProfile`; AMTOPA,
zeta-exact-pressure (MIT), as presented in Gebendorfer, "Zeta Geometry and Class Cap", Lemma 3.3) the block bound,
and with it `n_point_bound_w'`, holds under `c (m − q) ≤ (q+1)/q` (`n_point_bound_w'_τ`, `AMW.am_dyadic_n_τ`).
The certificate's windows are rank-consecutive, so only band pairs enter (`window_pairs_le_band`).  Every result
here takes the profile as a hypothesis `hP : BandProfile`. ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma window_pairs_le_band {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ ∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0) := by
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

  set G : Fin m × Fin m → ℝ := fun r => if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
    then wfun (y r.1 - y r.2) else 0 with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne, by omega, by omega⟩,
      wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne', by omega, by omega⟩]
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
    · exact wfun_nonneg _
    · exact le_rfl
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r


theorem block_energy_band {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (∑ r : Fin m × Fin m,
        (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0))
      + blkPress W.b x univ := by
  classical
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
  have hquad := window_pairs_le_band hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith



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
  have hcl' : ∀ i j : B, i ≠ j → ‖G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ) i j - (kfun (x' i - x' j) : ℂ)‖ ≤ δ :=
    fun i j h => hclose i i.2 j j.2 (fun e => h (Subtype.ext e))
  have hC := band_close hx' hS hcard (n - 1) (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) hδ hcl'
  have hprof : min ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
      (bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1))
        ≤ blockDefect hG.1 B :=
    hP B (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (hG.submatrix _) (fun i => (sRank x' hS i : ℕ))
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
      (bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1)) with h1 | h1
  · rw [min_eq_left h1] at hprof
    linarith
  · rw [min_eq_right h1.le] at hprof
    linarith


section TauChain

open Filter Zeta23 Zeta23.ZeroSide Zeta23.ThmD
open Classical

lemma one_sub_div_pos_τ {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (h2n : 2 * n ≤ m)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast (by omega : 4 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  have hq : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
  have hτ : (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith

theorem solve_linear_w_τ {N N0 : ℝ → ℝ} {c : ℝ} {n m : ℕ} (K : ℝ) (hn : 2 ≤ n) (h2n : 2 * n ≤ m)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (K - ε) * N T ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (K / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos_τ hn h2n hA0τ
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have : K / Dn - ε = (K - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith



theorem block_bound_eventually_w'_τ (hP : BandProfile) (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
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
  filter_upwards [kernel_limit Z H ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w'_τ hP hn hm W hW hCert hA0τ x (gram_posSemidef Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) < blkPress W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [lt_div_iff₀ hbmin] at this
      rw [div_mul_cancel₀ _ hbmin.ne'] at this
      exact this
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]


theorem pre_solve_w'_τ (hP : BandProfile) (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
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

  have hτ0 : (0 : ℝ) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) := by positivity
  set Cn : ℝ := (m : ℝ) + (2 * ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) + 1) + W.B * ((m : ℝ) - ((n : ℝ) - 1)) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    rw [hCn]; nlinarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w'_τ hP Z H hn3 h2n W hW hbmin hb hCert hA0τ hηpos,
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
  have e1 : A₀ * (η * N) ≤ ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) * (η * N) := mul_le_mul_of_nonneg_right hA0τ hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - (2 * ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) + 1) * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by nlinarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (AMW.HW - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + (2 * ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) + 1) + q * mq) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + (2 * ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) + 1) + q * mq) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + (2 * ((((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) + 1) + q * mq) * N ≤ m * ε * N :=
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


theorem n_point_bound_w'_τ (hP : BandProfile) (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have h := solve_linear_w_τ (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn h2n hA0τ
    (by
      have := pre_solve_w'_τ hP zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert hA0τ
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)



end TauChain

end Zeta23Ext.BridgeW

end


noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- **The n-point bound for the AM window under the band profile** (`c (m − q) ≤ (q+1)/q`), from a certificate. -/
theorem am_dyadic_n_τ (hP : BandProfile) {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
    (hκ : κ ≤ Phi_w' n c m W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w'_τ hP n c m W hn hm hW hbmin hb hc hCert hA0τ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

end AMW

end
