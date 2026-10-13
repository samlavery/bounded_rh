import AMW.BrTau

/-! ###### AMW/BrEdge — edge windows for the window certificate (bridge-port, clean-room)

The certificate's windows sit at the offsets `0 … m − n` of the sorted block, so the pairs near the block ends are
covered by fewer windows than interior pairs. A *virtual window* at any integer offset `o` is the full window shifted
to `o`, keeping only the pairs whose points exist (`vwin`). Distinct offsets put a pair `(p, q)` at distinct positions
`(p − o, q − o)` of span `q − p` in the certificate, so the windows at any finite set of offsets together give each
pair at most its span mass, `≤ 2`, and their pair sums stay below the band sum (`vwin_sum_le_band`). This is
`window_pairs_le_band`'s injection argument with integer offsets and truncation.

The edge windows are virtual windows past the ends: on the right, the offset `m − 1 − k` keeps the prefix of `k + 1`
points of the certificate; on the left, the offset `k − (n − 1)` keeps the suffix, which for a reversal-symmetric
certificate is the reflection `x ↦ −x` of the prefix (`window_pairs_edge_le_band`). ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the virtual window at the integer offset `o`: the pairs of the full window whose points `o + a`, `o + b` exist -/
def vwin {n : ℕ} (W : WCert n) (Y : ℕ → ℝ) (m : ℕ) (o : ℤ) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n,
    if (a : ℕ) < (b : ℕ) ∧ 0 ≤ o + (a : ℤ) ∧ o + (b : ℤ) < m then
      W.a a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + (a : ℤ)).toNat)
    else 0

/-- (E1₀) the windows at any finite set of offsets: each pair collects at most its span mass -/
lemma vwin_sum_le_band {n m : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) (O : Finset ℤ) :
    ∑ o ∈ O, vwin W (sortedExt ((univ.image x).orderEmbOfFin hS)) m o
      ≤ ∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0) := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- no points: every virtual window is empty
    have h0 : ∀ o, vwin W Y m o = 0 := by
      intro o
      unfold vwin
      refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
      rw [if_neg]
      omega
    rw [sum_congr rfl fun o _ => h0 o, sum_const_zero]
    refine sum_nonneg fun r _ => ?_
    split_ifs
    · exact wfun_nonneg _
    · exact le_rfl
  set T : Finset (ℤ × (Fin n × Fin n)) :=
    (O ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t =>
      (t.2.1 : ℕ) < t.2.2 ∧ 0 ≤ t.1 + (t.2.1 : ℤ) ∧ t.1 + (t.2.2 : ℤ) < m
    with hTdef
  set f : ℤ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * wfun (Y (t.1 + (t.2.2 : ℤ)).toNat - Y (t.1 + (t.2.1 : ℤ)).toNat) with hfdef
  have hLHS : ∑ o ∈ O, vwin W Y m o = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun o _ => ?_
    unfold vwin
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) =>
      if (a : ℕ) < (b : ℕ) ∧ 0 ≤ o + (a : ℤ) ∧ o + (b : ℤ) < m then
        W.a a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + (a : ℤ)).toNat) else 0)).symm
  rw [hLHS]

  set φ : ℤ × (Fin n × Fin n) → ℕ × ℕ := fun t => ((t.1 + (t.2.1 : ℤ)).toNat, (t.1 + (t.2.2 : ℤ)).toNat)
    with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, (t.2.1 : ℕ) < t.2.2 ∧ 0 ≤ t.1 + (t.2.1 : ℤ) ∧ t.1 + (t.2.2 : ℤ) < m := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_univ, and_true] at ht
    exact ht.2
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2, h3⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨-, hφt⟩ := ht
      have e1 : (t.1 + (t.2.1 : ℤ)).toNat = q.1 := congrArg Prod.fst hφt
      have e2 : (t.1 + (t.2.2 : ℤ)).toNat = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2]
    rw [sum_congr rfl hconst, ← sum_mul]
    set ψ : ℤ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
    have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' hee
      rw [mem_coe, mem_filter] at ht ht'
      have e1 : (t.1 + (t.2.1 : ℤ)).toNat = q.1 := congrArg Prod.fst ht.2
      have e1' : (t'.1 + (t'.2.1 : ℤ)).toNat = q.1 := congrArg Prod.fst ht'.2
      obtain ⟨-, h2, -⟩ := hmem t ht.1
      obtain ⟨-, h2', -⟩ := hmem t' ht'.1
      simp only [hψdef] at hee
      have ha : ((t.2.1 : ℕ) : ℤ) = ((t'.2.1 : ℕ) : ℤ) := by rw [hee]
      have hi : t.1 = t'.1 := by omega
      exact Prod.ext hi hee
    have hsub : (T.filter (fun t => φ t = q)).image ψ
        ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
            (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      rw [mem_filter] at ht
      have e1 : (t.1 + (t.2.1 : ℤ)).toNat = q.1 := congrArg Prod.fst ht.2
      have e2 : (t.1 + (t.2.2 : ℤ)).toNat = q.2 := congrArg Prod.snd ht.2
      obtain ⟨hlt, h2, h3⟩ := hmem t ht.1
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

/-! ### the prefix truncation, and the windows as virtual windows -/

/-- the certificate's weight at natural positions (zero outside) -/
def Wn {n : ℕ} (W : WCert n) (a b : ℕ) : ℝ := if h : a < n ∧ b < n then W.a ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

lemma Wn_fin {n : ℕ} (W : WCert n) (a b : Fin n) : Wn W a b = W.a a b := by
  simp [Wn, a.2, b.2]

/-- the prefix truncation: the first `k + 1` points of the certificate, with their `k` gap weights -/
def WCert.pre {n : ℕ} (W : WCert n) (k : ℕ) : WCert (k + 1) where
  a := fun a b => Wn W a b
  b := fun r => if h : (r : ℕ) < n - 1 then W.b ⟨r, h⟩ else 0

lemma Wn_pre {n k : ℕ} (W : WCert n) {a b : ℕ} (ha : a < k + 1) (hb : b < k + 1) : Wn (W.pre k) a b = Wn W a b := by
  simp [Wn, WCert.pre, ha, hb]

/-- a reversal-symmetric certificate, at natural positions -/
lemma Wn_sym {n : ℕ} {W : WCert n} (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) {a b : ℕ} (ha : a < n)
    (hb : b < n) : Wn W (n - 1 - b) (n - 1 - a) = Wn W a b := by
  have h1 : Wn W a b = W.a ⟨a, ha⟩ ⟨b, hb⟩ := by simp [Wn, ha, hb]
  have h2 : Wn W (n - 1 - b) (n - 1 - a) = W.a (Fin.rev ⟨b, hb⟩) (Fin.rev ⟨a, ha⟩) := by
    unfold Wn
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega
  rw [h1, h2, ← hsym]

lemma pairs_range {N : ℕ} (V : WCert N) (F : ℕ → ℕ → ℝ) :
    ∑ a : Fin N, ∑ b : Fin N, (if (a : ℕ) < (b : ℕ) then V.a a b * F a b else 0)
      = ∑ a ∈ range N, ∑ b ∈ range N, (if a < b then Wn V a b * F a b else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range N, if a < b then Wn V a b * F a b else 0)]
  refine sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => if (a : ℕ) < b then Wn V a b * F a b else 0)]
  refine sum_congr rfl fun b _ => ?_
  rw [Wn_fin]

lemma vwin_range {n : ℕ} (W : WCert n) (Y : ℕ → ℝ) (m : ℕ) (o : ℤ) :
    vwin W Y m o = ∑ a ∈ range n, ∑ b ∈ range n,
      (if a < b ∧ 0 ≤ o + (a : ℤ) ∧ o + (b : ℤ) < m then
        Wn W a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + (a : ℤ)).toNat) else 0) := by
  unfold vwin
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range n,
    if a < b ∧ 0 ≤ o + (a : ℤ) ∧ o + (b : ℤ) < m then
      Wn W a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + (a : ℤ)).toNat) else 0)]
  refine sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => if (a : ℕ) < b ∧ 0 ≤ o + ((a : ℕ) : ℤ) ∧ o + (b : ℤ) < m then
      Wn W a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + ((a : ℕ) : ℤ)).toNat) else 0)]
  refine sum_congr rfl fun b _ => ?_
  rw [Wn_fin]

lemma sum_range_ext {K N : ℕ} (h : K ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range K, f j = ∑ j ∈ range N, if j < K then f j else 0 := by
  rw [← sum_filter, range_filter_lt h]

lemma double_reflect (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ a ∈ range N, ∑ b ∈ range N, G a b = ∑ a ∈ range N, ∑ b ∈ range N, G (N - 1 - b) (N - 1 - a) := by
  rw [sum_comm, ← sum_range_reflect (fun b => ∑ a ∈ range N, G a b) N]
  refine sum_congr rfl fun a' _ => ?_
  exact (sum_range_reflect (fun a => G a (N - 1 - a')) N).symm

/-- a full window is the virtual window at its offset -/
lemma vwin_full {n m i : ℕ} (W : WCert n) (Y : ℕ → ℝ) (hi : i + n ≤ m) :
    vwin W Y m (i : ℤ) = ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0) := by
  unfold vwin
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have ha := a.2
  have hb := b.2
  by_cases hab : (a : ℕ) < (b : ℕ)
  · rw [if_pos ⟨hab, by omega, by omega⟩, if_pos hab]
    have e1 : ((i : ℤ) + ((b : ℕ) : ℤ)).toNat = i + b := by omega
    have e2 : ((i : ℤ) + ((a : ℕ) : ℤ)).toNat = i + a := by omega
    rw [e1, e2]
  · rw [if_neg (fun h => hab h.1), if_neg hab]

/-- the right edge window with `k` gaps (`k + 2 ≤ n`) is the virtual window at `m − 1 − k`: the prefix truncation -/
lemma vwin_right {n m k : ℕ} (W : WCert n) (Y : ℕ → ℝ) (hk : k + 2 ≤ n) (hkm : k + 1 ≤ m) :
    vwin W Y m ((m - 1 - k : ℕ) : ℤ) = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)) else 0) := by
  rw [vwin_range, pairs_range (W.pre k) (fun a b => wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a))),
    sum_range_ext (by omega : k + 1 ≤ n)]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  by_cases hak : a < k + 1
  · rw [if_pos hak, sum_range_ext (by omega : k + 1 ≤ n)]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    by_cases hbk : b < k + 1
    · rw [if_pos hbk, Wn_pre W hak hbk]
      by_cases hab : a < b
      · rw [if_pos ⟨hab, by omega, by omega⟩, if_pos hab]
        have e1 : (((m - 1 - k : ℕ) : ℤ) + (b : ℤ)).toNat = m - 1 - k + b := by omega
        have e2 : (((m - 1 - k : ℕ) : ℤ) + (a : ℤ)).toNat = m - 1 - k + a := by omega
        rw [e1, e2]
      · rw [if_neg (fun h => hab h.1), if_neg hab]
    · rw [if_neg hbk, if_neg (fun h => hbk (by omega))]
  · rw [if_neg hak]
    refine sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h => hak (by omega))]

/-- the left edge window with `k` gaps is the virtual window at `k − (n − 1)`: for a reversal-symmetric certificate,
the reflection `x ↦ −x` of the prefix truncation -/
lemma vwin_left {n m k : ℕ} {W : WCert n} (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) (Y : ℕ → ℝ)
    (hk : k + 2 ≤ n) (hkm : k + 1 ≤ m) :
    vwin W Y m ((k : ℤ) - ((n - 1 : ℕ) : ℤ)) = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0) := by
  rw [vwin_range, double_reflect, pairs_range (W.pre k) (fun a b => wfun (Y (k - a) - Y (k - b))),
    sum_range_ext (by omega : k + 1 ≤ n)]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  by_cases hak : a < k + 1
  · rw [if_pos hak, sum_range_ext (by omega : k + 1 ≤ n)]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    by_cases hbk : b < k + 1
    · rw [if_pos hbk, Wn_pre W hak hbk]
      by_cases hab : a < b
      · rw [if_pos ⟨by omega, by omega, by omega⟩, if_pos hab, Wn_sym hsym ha hb]
        have e1 : ((k : ℤ) - ((n - 1 : ℕ) : ℤ) + ((n - 1 - a : ℕ) : ℤ)).toNat = k - a := by omega
        have e2 : ((k : ℤ) - ((n - 1 : ℕ) : ℤ) + ((n - 1 - b : ℕ) : ℤ)).toNat = k - b := by omega
        rw [e1, e2]
      · rw [if_neg (fun h => hab (by omega)), if_neg hab]
    · rw [if_neg hbk, if_neg (fun h => hbk (by omega))]
  · rw [if_neg hak]
    refine sum_eq_zero fun b hb => ?_
    rw [mem_range] at hb
    rw [if_neg (fun h => hak (by omega))]

/-- (E1) the full windows and, for each `k ∈ S`, the right and left edge windows with `k` gaps: every pair collects at
most its span mass, so the pair sums stay below the band sum -/
theorem window_pairs_edge_le_band {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      + ∑ k ∈ S, ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
        (if (a : ℕ) < (b : ℕ) then
          (W.pre k).a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (m - 1 - k + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (m - 1 - k + a))
        else 0)
      + ∑ k ∈ S, ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
        (if (a : ℕ) < (b : ℕ) then
          (W.pre k).a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (k - a)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (k - b))
        else 0)
      ≤ ∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0) := by
  classical
  set Y := sortedExt ((univ.image x).orderEmbOfFin hS) with hYdef
  set O1 : Finset ℤ := (range (m - (n - 1))).image (fun i : ℕ => (i : ℤ)) with hO1
  set O2 : Finset ℤ := S.image (fun k : ℕ => ((m - 1 - k : ℕ) : ℤ)) with hO2
  set O3 : Finset ℤ := S.image (fun k : ℕ => (k : ℤ) - ((n - 1 : ℕ) : ℤ)) with hO3
  have h12 : Disjoint O1 O2 := by
    rw [disjoint_left]
    intro o h1 h2
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h1
    obtain ⟨k, hk, hk'⟩ := mem_image.mp h2
    have := hSk k hk
    rw [mem_range] at hi
    omega
  have h123 : Disjoint (O1 ∪ O2) O3 := by
    rw [disjoint_left]
    intro o h12' h3
    obtain ⟨k, hk, rfl⟩ := mem_image.mp h3
    have := hSk k hk
    rcases mem_union.mp h12' with h1 | h2
    · obtain ⟨i, -, hi⟩ := mem_image.mp h1
      omega
    · obtain ⟨k', -, hk'⟩ := mem_image.mp h2
      omega
  have hcore := vwin_sum_le_band hn W hW x hx hS (O1 ∪ O2 ∪ O3)
  rw [← hYdef, sum_union h123, sum_union h12] at hcore
  have e1 : ∑ o ∈ O1, vwin W Y m o = ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0) := by
    rw [hO1, sum_image (fun i _ j _ h => by exact_mod_cast h)]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    exact vwin_full W Y (by omega)
  have e2 : ∑ o ∈ O2, vwin W Y m o = ∑ k ∈ S, ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)) else 0) := by
    rw [hO2, sum_image (fun k hk k' hk' h => by
      have := hSk k hk; have := hSk k' hk'
      have h' : m - 1 - k = m - 1 - k' := by exact_mod_cast h
      omega)]
    refine sum_congr rfl fun k hk => ?_
    have := hSk k hk
    exact vwin_right W Y this (by omega)
  have e3 : ∑ o ∈ O3, vwin W Y m o = ∑ k ∈ S, ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0) := by
    rw [hO3, sum_image (fun k _ k' _ h => by
      have h' : (k : ℤ) = k' := by linarith
      exact_mod_cast h')]
    refine sum_congr rfl fun k hk => ?_
    have := hSk k hk
    exact vwin_left hsym Y this (by omega)
  rw [e1, e2, e3] at hcore
  exact hcore

/-! ### (E2) the block energy with the edge windows -/

/-- the gaps of the first `k + 1` points read from the right end: the reflection `x ↦ −x` of the left edge window -/
def revGaps (k : ℕ) (Y : ℕ → ℝ) : Fin k → ℝ := fun r => Y (k - r) - Y (k - ((r : ℕ) + 1))

lemma ptsN_revGaps (k : ℕ) (Y : ℕ → ℝ) (j : Fin (k + 1)) : ptsN (k + 1) (revGaps k Y) j = Y k - Y (k - j) := by
  have hj : (j : ℕ) ≤ k := by have := j.2; omega
  unfold ptsN revGaps
  rw [Fin.sum_univ_eq_sum_range
    (fun r => if r < (j : ℕ) then Y (k - r) - Y (k - (r + 1)) else 0) (k + 1 - 1),
    ← sum_filter, range_filter_lt (by omega : (j : ℕ) ≤ k + 1 - 1)]
  have := Finset.sum_range_sub' (fun r => Y (k - r)) (j : ℕ)
  simpa using this

/-- the pressure of the two edge windows with `k` gaps -/
def edgePress {n : ℕ} (W : WCert n) (k m : ℕ) (Y : ℕ → ℝ) : ℝ :=
  ∑ r : Fin (k + 1 - 1), (W.pre k).b r * ((Y (m - 1 - k + ((r : ℕ) + 1)) - Y (m - 1 - k + r))
    + (Y (k - r) - Y (k - ((r : ℕ) + 1))))

/-- (E2) the block energy with the edge windows: the full windows' floor `c` on each of the `m − (n − 1)` full
windows, and the floor `ct k` of the prefix truncation on each of the two edge windows with `k ∈ S` gaps -/
theorem block_energy_band_edge {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, ct k ≤ (∑ r : Fin m × Fin m,
        (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
          then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0))
      + blkPress W.b x univ + ∑ k ∈ S, edgePress W k m (sortedExt ((univ.image x).orderEmbOfFin hS)) := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  -- the full windows (as in `block_energy_band`)
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
  -- the edge windows
  have hedge : ∀ k ∈ S, 2 * ct k ≤ edgePress W k m Y
      + (∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
          (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)) else 0))
      + (∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
          (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0)) := by
    intro k hk
    have hk2 := hSk k hk
    have hR := hCt k hk (windowGaps (k + 1) Y (m - 1 - k)) (by
      intro j
      have hj := j.2
      have hlt : m - 1 - k + ((j : ℕ) + 1) < m := by omega
      exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt))
    have hL := hCt k hk (revGaps k Y) (by
      intro j
      have hj := j.2
      exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) (by omega)))
    rw [Fw_windowGaps] at hR
    have hFL : Fw (W.pre k) (revGaps k Y) = ∑ r : Fin (k + 1 - 1), (W.pre k).b r * revGaps k Y r
        + ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
          (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0) := by
      unfold Fw
      congr 1
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [ptsN_revGaps, ptsN_revGaps, show Y k - Y (k - b) - (Y k - Y (k - a)) = Y (k - a) - Y (k - b) by ring]
    rw [hFL] at hL
    have hP : edgePress W k m Y = ∑ r : Fin (k + 1 - 1), (W.pre k).b r * (Y (m - 1 - k + ((r : ℕ) + 1)) - Y (m - 1 - k + r))
        + ∑ r : Fin (k + 1 - 1), (W.pre k).b r * revGaps k Y r := by
      unfold edgePress revGaps
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      ring
    rw [hP]
    linarith
  have hedges := sum_le_sum hedge
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at hedges
  have hquad := window_pairs_edge_le_band hn hm W hW hsym S hSk x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

end Zeta23Ext.BridgeW

end
