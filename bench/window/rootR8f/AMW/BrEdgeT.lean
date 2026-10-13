import AMW.BrTau

/-! ###### AMW/BrEdgeT — edge windows for the window certificate (bridge-port, clean-room; the trimmed AMW/BrEdge)

Same declarations and statements as AMW/BrEdge, with shorter proofs: one termwise lemma for both edge identifications
(`edge_aux`) and one window-floor lemma for the full and the right edge windows (`wfloor`). A virtual window at an
integer offset `o` is the full window shifted to `o`, keeping the pairs whose points exist (`vwin`); distinct offsets put
a pair at distinct positions of its span, so any set of them stays below the band sum (`vwin_sum_le_band`). The edge
windows are the virtual windows past the ends: the prefix truncation on the right, and for a reversal-symmetric
certificate its reflection on the left (`window_pairs_edge_le_band`, `block_energy_band_edge`). ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the virtual window at the integer offset `o` -/
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
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS)
  set Y := sortedExt y with hY
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [sum_congr rfl fun o _ => show vwin W Y m o = 0 from sum_eq_zero fun a _ => sum_eq_zero fun b _ => if_neg (by omega),
      sum_const_zero]
    exact sum_nonneg fun r _ => by split_ifs <;> simp [wfun_nonneg]
  set T := (O ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t : ℤ × (Fin n × Fin n) =>
      (t.2.1 : ℕ) < t.2.2 ∧ 0 ≤ t.1 + (t.2.1 : ℤ) ∧ t.1 + (t.2.2 : ℤ) < m with hT
  set f := fun t : ℤ × (Fin n × Fin n) => W.a t.2.1 t.2.2 * wfun (Y (t.1 + (t.2.2 : ℤ)).toNat - Y (t.1 + (t.2.1 : ℤ)).toNat)
    with hf
  have hL : ∑ o ∈ O, vwin W Y m o = ∑ t ∈ T, f t := by
    rw [hT, sum_filter, sum_product]
    refine sum_congr rfl fun o _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) =>
      if (a : ℕ) < (b : ℕ) ∧ 0 ≤ o + (a : ℤ) ∧ o + (b : ℤ) < m then
        W.a a b * wfun (Y (o + (b : ℤ)).toNat - Y (o + (a : ℤ)).toNat) else 0)).symm
  rw [hL]
  set φ := fun t : ℤ × (Fin n × Fin n) => ((t.1 + (t.2.1 : ℤ)).toNat, (t.1 + (t.2.2 : ℤ)).toNat) with hφ
  set I := T.image φ
  have hm : ∀ t ∈ T, (t.2.1 : ℕ) < t.2.2 ∧ 0 ≤ t.1 + (t.2.1 : ℤ) ∧ t.1 + (t.2.2 : ℤ) < m := fun t ht => by
    simp only [hT, mem_filter, mem_product, mem_univ, and_true] at ht; exact ht.2
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    have := hm t ht; have := t.2.2.2
    simp only [hφ]; omega
  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]
  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q _
    have e : ∀ t ∈ T.filter (fun t => φ t = q), (t.1 + (t.2.1 : ℤ)).toNat = q.1 ∧ (t.1 + (t.2.2 : ℤ)).toNat = q.2 :=
      fun t ht => ⟨congrArg Prod.fst (mem_filter.mp ht).2, congrArg Prod.snd (mem_filter.mp ht).2⟩
    rw [sum_congr rfl fun t ht => by simp only [hf]; rw [(e t ht).1, (e t ht).2], ← sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (wfun_nonneg _)
    have hinj : Set.InjOn (fun t : ℤ × (Fin n × Fin n) => t.2) (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' h
      have := e t ht; have := e t' ht'; have := hm t (mem_filter.mp ht).1; have := hm t' (mem_filter.mp ht').1
      have ha : ((t.2.1 : ℕ) : ℤ) = ((t'.2.1 : ℕ) : ℤ) := by simp only at h; rw [h]
      exact Prod.ext (by omega) h
    have hsub : (T.filter (fun t => φ t = q)).image (fun t => t.2) ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
        (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = q.2 - q.1 := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      have := e t ht; have := hm t (mem_filter.mp ht).1
      rw [mem_filter, mem_product]
      exact ⟨⟨mem_univ _, mem_univ _⟩, this.1, by omega⟩
    rw [← sum_image (f := fun p : Fin n × Fin n => W.a p.1 p.2) hinj]
    refine (sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2).trans ?_
    have h3 := hW.capacity (q.2 - q.1)
    unfold WCert.spanMass at h3
    rwa [sum_filter, sum_product]
  refine (sum_le_sum hfib).trans ?_
  set G := fun r : Fin m × Fin m => if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
    then wfun (y r.1 - y r.2) else 0 with hG
  set F := fun k : ℕ => if h : k < m then (⟨k, h⟩ : Fin m) else ⟨0, h0⟩ with hF
  have hF' : ∀ k (h : k < m), F k = ⟨k, h⟩ := fun k h => by simp only [hF, dif_pos h]
  have hG1 : ∀ q ∈ I, G (F q.1, F q.2) = wfun (Y q.2 - Y q.1) ∧ G (F q.2, F q.1) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hI q hq
    simp only [hG, hF' _ (by omega : q.1 < m), hF' _ h2, hY, sortedExt_of_lt y (by omega : q.1 < m),
      sortedExt_of_lt y h2]
    rw [if_pos ⟨fun h => absurd (Fin.mk.inj_iff.mp h) h1.ne, by omega, by omega⟩,
      if_pos ⟨fun h => absurd (Fin.mk.inj_iff.mp h) h1.ne', by omega, by omega⟩, wfun_sub_comm]
    exact ⟨rfl, rfl⟩
  have hinj : ∀ (s : Bool), Set.InjOn (fun q : ℕ × ℕ => if s then (F q.1, F q.2) else (F q.2, F q.1)) I := by
    intro s q hq q' hq' h
    obtain ⟨h1, h2, -⟩ := hI q hq
    obtain ⟨h1', h2', -⟩ := hI q' hq'
    cases s <;> simp only [hF' _ (by omega : q.1 < m), hF' _ h2, hF' _ (by omega : q'.1 < m), hF' _ h2',
      Prod.mk.injEq, Fin.mk.injEq, if_true, Bool.false_eq_true, if_false] at h <;> exact Prod.ext (by omega) (by omega)
  have hdisj : Disjoint (I.image fun q : ℕ × ℕ => if true then (F q.1, F q.2) else (F q.2, F q.1))
      (I.image fun q : ℕ × ℕ => if false then (F q.1, F q.2) else (F q.2, F q.1)) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', h⟩ := mem_image.mp hr2
    obtain ⟨h1, h2, -⟩ := hI q hq
    obtain ⟨h1', h2', -⟩ := hI q' hq'
    simp only [hF' _ (by omega : q.1 < m), hF' _ h2, hF' _ (by omega : q'.1 < m), hF' _ h2',
      Prod.mk.injEq, Fin.mk.injEq, if_true, Bool.false_eq_true, if_false] at h
    omega
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1)
      = ∑ q ∈ I, G (if true then (F q.1, F q.2) else (F q.2, F q.1))
        + ∑ q ∈ I, G (if false then (F q.1, F q.2) else (F q.2, F q.1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    simp only [if_true, Bool.false_eq_true, if_false, (hG1 q hq).1, (hG1 q hq).2]; ring
  rw [hsplit, ← sum_image (hinj true), ← sum_image (hinj false), ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => by
    simp only [hG]; split_ifs <;> simp [wfun_nonneg]

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
  exact sum_congr rfl fun b _ => by rw [Wn_fin]

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
  exact sum_congr rfl fun b _ => by rw [Wn_fin]

lemma double_reflect (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ a ∈ range N, ∑ b ∈ range N, G a b = ∑ a ∈ range N, ∑ b ∈ range N, G (N - 1 - b) (N - 1 - a) := by
  rw [sum_comm, ← sum_range_reflect (fun b => ∑ a ∈ range N, G a b) N]
  exact sum_congr rfl fun a' _ => (sum_range_reflect (fun a => G a (N - 1 - a')) N).symm

/-- the edge identifications, termwise: a double sum over `range n` that is the prefix sum on `range (k + 1)` -/
lemma edge_aux {n k : ℕ} (hk : k + 1 ≤ n) (L R : ℕ → ℕ → ℝ)
    (h : ∀ a b, a < n → b < n → L a b = if a < k + 1 ∧ b < k + 1 ∧ a < b then R a b else 0) :
    ∑ a ∈ range n, ∑ b ∈ range n, L a b = ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1), if a < b then R a b else 0 := by
  rw [← range_filter_lt hk]
  simp only [sum_filter]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  split_ifs with hak
  · refine sum_congr rfl fun b hb => ?_
    rw [h a b ha (mem_range.mp hb)]
    by_cases hbk : b < k + 1 <;> by_cases hab : a < b <;> simp [hak, hbk, hab]
  · exact sum_eq_zero fun b hb => by rw [h a b ha (mem_range.mp hb), if_neg fun h' => hak h'.1]

/-- a full window is the virtual window at its offset -/
lemma vwin_full {n m i : ℕ} (W : WCert n) (Y : ℕ → ℝ) (hi : i + n ≤ m) :
    vwin W Y m (i : ℤ) = ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0) := by
  unfold vwin
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have := a.2; have := b.2
  by_cases h : (a : ℕ) < (b : ℕ)
  · rw [if_pos ⟨h, by omega, by omega⟩, if_pos h, show ((i : ℤ) + ((b : ℕ) : ℤ)).toNat = i + b by omega,
      show ((i : ℤ) + ((a : ℕ) : ℤ)).toNat = i + a by omega]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/-- the right edge window with `k` gaps (`k + 2 ≤ n`) is the virtual window at `m − 1 − k`: the prefix truncation -/
lemma vwin_right {n m k : ℕ} (W : WCert n) (Y : ℕ → ℝ) (hk : k + 2 ≤ n) (hkm : k + 1 ≤ m) :
    vwin W Y m ((m - 1 - k : ℕ) : ℤ) = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)) else 0) := by
  rw [vwin_range, pairs_range (W.pre k) (fun a b => wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)))]
  refine edge_aux (by omega) _ _ fun a b ha hb => ?_
  by_cases hc : a < k + 1 ∧ b < k + 1 ∧ a < b
  · rw [if_pos ⟨hc.2.2, by omega, by omega⟩, if_pos hc, Wn_pre W hc.1 hc.2.1,
      show (((m - 1 - k : ℕ) : ℤ) + (b : ℤ)).toNat = m - 1 - k + b by omega,
      show (((m - 1 - k : ℕ) : ℤ) + (a : ℤ)).toNat = m - 1 - k + a by omega]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨by omega, by omega, h'.1⟩)]

/-- the left edge window with `k` gaps is the virtual window at `k − (n − 1)`: for a reversal-symmetric certificate,
the reflection `x ↦ −x` of the prefix truncation -/
lemma vwin_left {n m k : ℕ} {W : WCert n} (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) (Y : ℕ → ℝ)
    (hk : k + 2 ≤ n) (hkm : k + 1 ≤ m) :
    vwin W Y m ((k : ℤ) - ((n - 1 : ℕ) : ℤ)) = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
      (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0) := by
  rw [vwin_range, double_reflect, pairs_range (W.pre k) (fun a b => wfun (Y (k - a) - Y (k - b)))]
  refine edge_aux (by omega) _ _ fun a b ha hb => ?_
  by_cases hc : a < k + 1 ∧ b < k + 1 ∧ a < b
  · rw [if_pos ⟨by omega, by omega, by omega⟩, if_pos hc, Wn_pre W hc.1 hc.2.1, Wn_sym hsym ha hb,
      show ((k : ℤ) - ((n - 1 : ℕ) : ℤ) + ((n - 1 - a : ℕ) : ℤ)).toNat = k - a by omega,
      show ((k : ℤ) - ((n - 1 : ℕ) : ℤ) + ((n - 1 - b : ℕ) : ℤ)).toNat = k - b by omega]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨by omega, by omega, by omega⟩)]

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
  set Y := sortedExt ((univ.image x).orderEmbOfFin hS) with hY
  set O1 := (range (m - (n - 1))).image (fun i : ℕ => (i : ℤ))
  set O2 := S.image (fun k : ℕ => ((m - 1 - k : ℕ) : ℤ))
  set O3 := S.image (fun k : ℕ => (k : ℤ) - ((n - 1 : ℕ) : ℤ))
  have h12 : Disjoint O1 O2 := disjoint_left.mpr fun o h1 h2 => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h1
    obtain ⟨k, hk, h⟩ := mem_image.mp h2
    have := hSk k hk; rw [mem_range] at hi; omega
  have h3 : Disjoint (O1 ∪ O2) O3 := disjoint_left.mpr fun o h h3 => by
    obtain ⟨k, hk, rfl⟩ := mem_image.mp h3
    have := hSk k hk
    rcases mem_union.mp h with h | h <;> obtain ⟨i, -, h⟩ := mem_image.mp h <;> omega
  have hc := vwin_sum_le_band hn W hW x hx hS (O1 ∪ O2 ∪ O3)
  rw [← hY, sum_union h3, sum_union h12, sum_image (fun i _ j _ h => by exact_mod_cast h),
    sum_image (fun k hk k' hk' h => by
      have := hSk k hk; have := hSk k' hk'; have : m - 1 - k = m - 1 - k' := (by exact_mod_cast h); omega),
    sum_image (fun k _ k' _ h => by have : (k : ℤ) = k' := (by linarith); exact_mod_cast this)] at hc
  rw [sum_congr rfl fun i hi => (vwin_full (m := m) (i := i) W Y (by rw [mem_range] at hi; omega)).symm,
    sum_congr rfl fun k hk => (vwin_right (m := m) W Y (hSk k hk) (by have := hSk k hk; omega)).symm,
    sum_congr rfl fun k hk => (vwin_left (m := m) hsym Y (hSk k hk) (by have := hSk k hk; omega)).symm]
  exact hc

/-! ### (E2) the block energy with the edge windows -/

/-- the gaps of the first `k + 1` points read from the right end: the reflection `x ↦ −x` of the left edge window -/
def revGaps (k : ℕ) (Y : ℕ → ℝ) : Fin k → ℝ := fun r => Y (k - r) - Y (k - ((r : ℕ) + 1))

lemma ptsN_revGaps (k : ℕ) (Y : ℕ → ℝ) (j : Fin (k + 1)) : ptsN (k + 1) (revGaps k Y) j = Y k - Y (k - j) := by
  have hj : (j : ℕ) ≤ k := by have := j.2; omega
  unfold ptsN revGaps
  rw [Fin.sum_univ_eq_sum_range
    (fun r => if r < (j : ℕ) then Y (k - r) - Y (k - (r + 1)) else 0) (k + 1 - 1),
    ← sum_filter, range_filter_lt (by omega : (j : ℕ) ≤ k + 1 - 1)]
  simpa using Finset.sum_range_sub' (fun r => Y (k - r)) (j : ℕ)

/-- the pressure of the two edge windows with `k` gaps -/
def edgePress {n : ℕ} (W : WCert n) (k m : ℕ) (Y : ℕ → ℝ) : ℝ :=
  ∑ r : Fin (k + 1 - 1), (W.pre k).b r * ((Y (m - 1 - k + ((r : ℕ) + 1)) - Y (m - 1 - k + r))
    + (Y (k - r) - Y (k - ((r : ℕ) + 1))))

/-- a window's floor: on the sorted points `i … i + N − 1`, pressure plus pairs -/
lemma wfloor {N m i : ℕ} (V : WCert N) {c : ℝ} (hC : ∀ g : Fin (N - 1) → ℝ, (∀ j, 0 ≤ g j) → c ≤ Fw V g)
    {y : Fin m → ℝ} (hy : StrictMono y) (hi : i + N ≤ m) :
    c ≤ ∑ r : Fin (N - 1), V.b r * (sortedExt y (i + ((r : ℕ) + 1)) - sortedExt y (i + r))
      + ∑ a : Fin N, ∑ b : Fin N, (if (a : ℕ) < (b : ℕ) then V.a a b * wfun (sortedExt y (i + b) - sortedExt y (i + a))
        else 0) :=
  Fw_windowGaps V (sortedExt y) i ▸ hC _ fun j => sub_nonneg.mpr (sortedExt_mono hy (by omega) (by have := j.2; omega))

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
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hy
  have hmo : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hY
  have hsum := sum_le_sum fun i (hi : i ∈ range (m - (n - 1))) =>
    wfloor W hCert hmo (i := i) (by rw [mem_range] at hi; omega)
  rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, Nat.cast_sub (by omega : n - 1 ≤ m),
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      = blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    exact sum_congr rfl fun r _ => by rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hedge : ∀ k ∈ S, 2 * ct k ≤ edgePress W k m Y
      + (∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
          (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (m - 1 - k + b) - Y (m - 1 - k + a)) else 0))
      + (∑ a : Fin (k + 1), ∑ b : Fin (k + 1),
          (if (a : ℕ) < (b : ℕ) then (W.pre k).a a b * wfun (Y (k - a) - Y (k - b)) else 0)) := by
    intro k hk
    have := hSk k hk
    have hR := wfloor (W.pre k) (hCt k hk) hmo (i := m - 1 - k) (by omega)
    have hL := hCt k hk (revGaps k Y) fun j => by
      have := j.2; exact sub_nonneg.mpr (sortedExt_mono hmo (by omega) (by omega))
    unfold Fw at hL
    simp_rw [ptsN_revGaps, show ∀ a b : ℕ, Y k - Y (k - b) - (Y k - Y (k - a)) = Y (k - a) - Y (k - b) from
      fun a b => by ring] at hL
    unfold edgePress revGaps at *
    rw [← hY] at hR
    simp only [mul_add, sum_add_distrib]
    linarith
  have hq := window_pairs_edge_le_band hn hm W hW hsym S hSk x hx hS
  rw [← hy, ← hY] at hq
  have := sum_le_sum hedge
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at this
  linarith

end Zeta23Ext.BridgeW

end
