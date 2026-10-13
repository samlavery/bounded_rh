import AMW.BrSqrtWS
import AMW.BrEdgeT

/-! ###### AMW/BrEdgeChainT — the √-branch block chain with edge windows (bridge-port, clean-room; the trimmed
AMW/BrEdgeChain)

Same declarations and statements as AMW/BrEdgeChain, with shorter proofs. With `A = c (m − q) + 2 Σ_{k∈S} ct k` and
`P = B (m − q) + 2 Σ_{k∈S} Bt k`, the chain of AMW/BrSqrtWS runs with `(A, P)` in place of `(c (m − q), B (m − q))`.
Every pressure term is a run of gaps at a fixed block position, which over the sliding blocks telescopes to at most its
length times the span (`offset_average_edge`). ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the gap weight of the edge windows with `k` gaps: `Bt k = Σ_{r<k} b_r` -/
def edgeB {n : ℕ} (W : WCert n) (k : ℕ) : ℝ := ∑ r : Fin (k + 1 - 1), (W.pre k).b r

lemma pre_b_nonneg {n : ℕ} {W : WCert n} (hW : W.Adm) (k : ℕ) (r : Fin (k + 1 - 1)) : 0 ≤ (W.pre k).b r := by
  simp only [WCert.pre]; split_ifs
  · exact hW.b_nonneg _
  · exact le_rfl

lemma edgeB_nonneg {n : ℕ} {W : WCert n} (hW : W.Adm) (k : ℕ) : 0 ≤ edgeB W k :=
  sum_nonneg fun r _ => pre_b_nonneg hW k r

/-- the edge windows' pressure on a block `B` -/
def edgePressOn {n : ℕ} (W : WCert n) (S : Finset ℕ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ k ∈ S, edgePress W k (B.image x).card (sortedOn x B)

lemma edgePressOn_nonneg {n m : ℕ} {W : WCert n} (hW : W.Adm) {S : Finset ℕ} (hSk : ∀ k ∈ S, k + 2 ≤ n)
    (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hic : (B.image x).card = m) : 0 ≤ edgePressOn W S x B := by
  refine sum_nonneg fun k hk => sum_nonneg fun r _ => mul_nonneg (pre_b_nonneg hW k r) ?_
  have := hSk k hk; have := r.2
  have hg : ∀ a b, a ≤ b → b < m → sortedOn x B a ≤ sortedOn x B b := fun a b h hb => by
    unfold sortedOn
    rw [← hic] at hb
    rw [sortedExt_of_lt _ (lt_of_le_of_lt h hb), sortedExt_of_lt _ hb]
    exact ((B.image x).orderEmbOfFin rfl).strictMono.monotone (Fin.mk_le_mk.mpr h)
  rw [hic]
  linarith [hg (m - 1 - k + r) (m - 1 - k + ((r : ℕ) + 1)) (by omega) (by omega),
    hg (k - ((r : ℕ) + 1)) (k - r) (by omega) (by omega)]

/-- `offset_average_w` with the edge windows' pressure in each block: it costs `2 Σ_{k∈S} Bt k` times the span -/
theorem offset_average_edge {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm) (S : Finset ℕ)
    (hSk : ∀ k ∈ S, k + 2 ≤ n)
    (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : n ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A : ℝ) (hA : 0 ≤ A)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B →
      A ≤ Dblk B + blkPress W.b x B + edgePressOn W S x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m)
      - ((∑ r, W.b r) * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, edgeB W k) * spanOf x univ ≤ m * Dtot := by
  classical
  set N := Fintype.card ι with hN
  set Bt : ℝ := ∑ r, W.b r with hBt
  set Be : ℝ := ∑ k ∈ S, edgeB W k with hBe
  have hB0 : 0 ≤ Bt := sum_nonneg fun r _ => hW.b_nonneg r
  have hE0 : 0 ≤ Be := sum_nonneg fun k _ => edgeB_nonneg hW k
  have hD : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hsp := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := by omega
  have hmq : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by
    have : (n : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rcases lt_or_ge N m with hNm | hNm
  · have : (N : ℝ) < m := by exact_mod_cast hNm
    nlinarith [mul_nonneg hB0 (mul_nonneg hmq hsp), mul_nonneg hE0 hsp,
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - N), mul_nonneg (by positivity : (0:ℝ) ≤ m) hD]
  have hS : (univ.image x).card = N := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin N → ℝ := ⇑((univ.image x).orderEmbOfFin hS)
  have hym : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hy : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hym k)
  have hbij : Function.Bijective ι' := (Fintype.bijective_iff_injective_and_card ι').mpr
    ⟨fun k k' h => hy.injective (by rw [← (hι' k).2, ← (hι' k').2, h]), by simp [hN]⟩
  set e : Fin N ≃ ι := Equiv.ofBijective ι' hbij
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hpos
  set Y := sortedExt y with hY
  have hxY : ∀ i, x i = Y (pos i) := fun i => by
    rw [hY, hpos]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    exact congrArg x (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hle : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := fun i i' => by
    rw [hxY, hxY, hY, hpos]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta, hy.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := fun a b hab hb => by
    rw [hY, sortedExt_of_lt y (lt_trans hab hb), sortedExt_of_lt y hb]
    exact hy (Fin.mk_lt_mk.mpr hab)
  have hsp' : ∀ a c, a < N → c < N → Y a - Y c ≤ spanOf x univ := fun a c ha hc => by
    obtain ⟨i, -, hi⟩ := mem_image.mp (hym ⟨a, ha⟩)
    obtain ⟨j, -, hj⟩ := mem_image.mp (hym ⟨c, hc⟩)
    rw [hY, sortedExt_of_lt y ha, sortedExt_of_lt y hc, ← hi, ← hj]
    exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i) (mem_univ j))
  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBd
  have hmB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := fun s i => by simp [hBd]
  set F : ℕ → Fin N := fun t => if h : t < N then ⟨t, h⟩ else ⟨0, by omega⟩ with hF
  have hcB : ∀ s, s + m ≤ N → (B s).card = m := fun s hs => by
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (F t)) (fun i hi => ?_) (fun t ht => ?_) (fun i _ => ?_) (fun t ht => ?_)
      · rw [mem_coe, hmB] at hi; rw [mem_coe, mem_Ico]; exact hi
      · rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmB]
        simp only [hpos, hF, dif_pos (by omega : t < N), Equiv.symm_apply_apply]
        exact ht
      · simp only [hF, dif_pos ((e.symm i).2), hpos, Fin.eta, Equiv.apply_symm_apply]
      · rw [mem_coe, mem_Ico] at ht
        simp only [hpos, hF, dif_pos (by omega : t < N), Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hiB : ∀ s, IsInterval x (B s) := fun s i hi j hj k hik hkj => by
    rw [hmB] at hi hj ⊢; rw [hle] at hik hkj; omega
  have hsB : ∀ s, s + m ≤ N → ∀ k, k < m → sortedOn x (B s) k = Y (s + k) := fun s hs k hk => by
    have hic : ((B s).image x).card = m := by rw [card_image_of_injOn hx.injOn, hcB s hs]
    rw [sortedOn_eq hic, sortedExt_of_lt _ hk]
    have hfs : ∀ j : Fin m, Y (s + j) ∈ (B s).image x := fun j => by
      have := j.2
      refine mem_image.mpr ⟨e ⟨s + j, by omega⟩, ?_, ?_⟩
      · rw [hmB, hpos]; simp only [Equiv.symm_apply_apply]; constructor <;> omega
      · rw [hxY, hpos]; simp only [Equiv.symm_apply_apply]
    have hmo : StrictMono fun j : Fin m => Y (s + j) := fun j j' h => by
      have := j'.2; exact hYlt _ _ (by have := Fin.lt_def.mp h; omega) (by omega)
    exact (congrFun (Finset.orderEmbOfFin_unique hic hfs hmo) ⟨k, hk⟩).symm
  set St := range (N - m + 1) with hSt
  have hmS : ∀ s, s ∈ St ↔ s + m ≤ N := fun s => by rw [hSt, mem_range]; omega
  have hsum : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress W.b x (B s)
      + ∑ s ∈ St, edgePressOn W S x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) => hblock (B s) (hcB s ((hmS s).mp hs)) (hiB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, sum_add_distrib, Nat.cast_add,
      Nat.cast_sub hNm, Nat.cast_one] at h
    linarith
  -- a run of `d` gaps at block position `p`: over the sliding blocks, at most `d` spans
  have hrun : ∀ p d, p + d < m → ∑ s ∈ St, (Y (s + (p + d)) - Y (s + p)) ≤ d * spanOf x univ := fun p d h => by
    have e := sum_shift_sub (fun t => Y (t + p)) d (N - m + 1)
    simp only [show ∀ s, s + d + p = s + (p + d) from fun s => by omega] at e
    rw [hSt, e]
    calc _ ≤ ∑ i ∈ range d, spanOf x univ :=
          sum_le_sum fun i hi => hsp' _ _ (by rw [mem_range] at hi; omega) (by rw [mem_range] at hi; omega)
      _ = d * spanOf x univ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hP : ∑ s ∈ St, blkPress W.b x (B s) ≤ Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
    have e1 : ∀ s ∈ St, blkPress W.b x (B s) = ∑ r : Fin (n - 1), W.b r * (Y (s + (r + (m - (n - 1)))) - Y (s + r)) :=
      fun s hs => by
        have hs' := (hmS s).mp hs
        unfold blkPress
        rw [card_image_of_injOn hx.injOn, hcB s hs']
        refine sum_congr rfl fun r _ => ?_
        have := r.2
        rw [hsB s hs' _ (by omega), hsB s hs' _ (by omega), show s + (m - (n - 1) + r) = s + (r + (m - (n - 1))) by omega]
    rw [sum_congr rfl e1, sum_comm, hBt, sum_mul, sum_mul]
    refine sum_le_sum fun r _ => ?_
    rw [← mul_sum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hW.b_nonneg r)
    have := r.2
    have h := hrun r (m - (n - 1)) (by omega)
    rwa [Nat.cast_sub (by omega : n - 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
  have hQ : ∑ s ∈ St, edgePressOn W S x (B s) ≤ 2 * Be * spanOf x univ := by
    have e1 : ∀ s ∈ St, edgePressOn W S x (B s) = ∑ k ∈ S, ∑ r : Fin (k + 1 - 1), (W.pre k).b r *
        ((Y (s + ((m - 1 - k + r) + 1)) - Y (s + (m - 1 - k + r)))
          + (Y (s + ((k - ((r : ℕ) + 1)) + 1)) - Y (s + (k - ((r : ℕ) + 1))))) := fun s hs => by
      have hs' := (hmS s).mp hs
      unfold edgePressOn
      rw [card_image_of_injOn hx.injOn, hcB s hs']
      refine sum_congr rfl fun k hk => sum_congr rfl fun r _ => ?_
      have := hSk k hk; have := r.2
      rw [hsB s hs' _ (by omega), hsB s hs' _ (by omega), hsB s hs' _ (by omega), hsB s hs' _ (by omega),
        show (k : ℕ) - (r : ℕ) = k - ((r : ℕ) + 1) + 1 by omega, show m - 1 - k + ((r : ℕ) + 1) = m - 1 - k + r + 1 by omega]
    rw [sum_congr rfl e1, sum_comm, hBe, mul_sum, sum_mul]
    refine sum_le_sum fun k hk => ?_
    rw [sum_comm]
    unfold edgeB
    rw [mul_sum, sum_mul]
    refine sum_le_sum fun r _ => ?_
    rw [← mul_sum, sum_add_distrib]
    have := hSk k hk; have := r.2
    have h1 := hrun (m - 1 - k + r) 1 (by omega)
    have h2 := hrun (k - ((r : ℕ) + 1)) 1 (by omega)
    rw [Nat.cast_one, one_mul] at h1 h2
    nlinarith [pre_b_nonneg hW k r]
  have hDb : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j _ => ?_
          set β : ι → Fin (N + 1) := fun i =>
            ⟨blockStart N m j (pos i), Nat.lt_succ_of_le (blockStart_le N m j (pos i))⟩ with hβ
          set G : ℕ → Fin (N + 1) := fun s => if h : s < N + 1 then ⟨s, h⟩ else 0 with hG
          have hinj : Set.InjOn G (St.filter (fun s => s % m = j)) := fun s hs s' hs' h => by
            rw [mem_coe, mem_filter, hmS] at hs hs'
            simp only [hG, dif_pos (by omega : s < N + 1), dif_pos (by omega : s' < N + 1), Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = G s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmS] at hs
                congr 1
                ext i
                simp only [hBd, mem_filter, mem_univ, true_and, hβ, hG, dif_pos (by omega : s < N + 1), Fin.mk.injEq]
                exact (blockStart_eq_iff hm0 hs.1 hs.2).symm
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image G, Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (N + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]
  linarith

/-! ### the chain with `A = c (m − q) + 2 Σ ct` and `P = B (m − q) + 2 Σ Bt` -/

/-- the block energy constant with the edge windows -/
def edgeA (c : ℝ) (n m : ℕ) (S : Finset ℕ) (ct : ℕ → ℝ) : ℝ :=
  c * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, ct k

/-- the pressure weight with the edge windows -/
def edgeP {n : ℕ} (W : WCert n) (m : ℕ) (S : Finset ℕ) : ℝ :=
  W.B * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, edgeB W k

/-- **the block bound with the edge windows**: `gtau τ A − 2 m² δ ≤ blockDefect + pressure + edge pressure` -/
theorem block_bound_w'_g_edge {κ : Type} [Fintype κ] [DecidableEq κ] {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    (x : κ → ℝ) {G : Matrix κ κ ℂ} (hG : G.PosSemidef) (B : Finset κ) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    gtau (tauq n) (edgeA c n m S ct) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + blkPress W.b x B + edgePressOn W S x B := by
  classical
  set x' : B → ℝ := fun i => x i
  have hx' : Function.Injective x' := fun i j h => Subtype.ext (hx i.2 j.2 h)
  have hcard : Fintype.card B = m := by simp [hB]
  have hS : (univ.image x').card = m := by rw [card_image_of_injective _ hx', card_univ, hcard]
  have hE := block_energy_band_edge hn W hW hsym hCert S hSk ct hCt hm x' hx' hS
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨i, h⟩ => ⟨i.1, i.2, h⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩
  have h1 : blkPress W.b x' univ = blkPress W.b x B := by
    unfold blkPress sortedOn; rw [sortedOn_congr himg, himg]
  have h2 : edgePressOn W S x' univ = edgePressOn W S x B := by
    unfold edgePressOn sortedOn; rw [sortedOn_congr himg, himg]
  have h3 : ∑ k ∈ S, edgePress W k m (sortedExt ((univ.image x').orderEmbOfFin hS)) = edgePressOn W S x' univ := by
    unfold edgePressOn
    rw [hS]
    exact sum_congr rfl fun k _ => by congr 1; funext j; exact (sortedOn_eq hS j).symm
  rw [h1, h3, h2] at hE
  have hC := band_close hx' hS hcard (n - 1) (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) hδ
    fun i j h => hclose i i.2 j j.2 (fun e => h (Subtype.ext e))
  have hprof : gtau (tauq n)
      (bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1))
        ≤ blockDefect hG.1 B :=
    band_profile_sqrt (hG.1.submatrix (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ))
      (fun i j h => sRank_injective hx' hS (Fin.ext h)) (n - 1) (by omega)
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
  have hP0 : 0 ≤ blkPress W.b x B := by
    unfold blkPress
    refine sum_nonneg fun r _ => mul_nonneg (hW.b_nonneg r) ?_
    unfold sortedOn
    have := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    rw [sub_nonneg, sortedExt_of_lt _ hk, sortedExt_of_lt _ hr]
    exact ((B.image x).orderEmbOfFin rfl).strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hE0 := edgePressOn_nonneg hW hSk hm x B hic
  have hτ : 0 < tauq n := tauq_pos hn
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  set Bq := bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1)
  set K : ℝ := 2 * (m : ℝ) ^ 2 * δ + blkPress W.b x B + edgePressOn W S x B with hK
  have := gtau_mono hτ (show edgeA c n m S ct ≤ Bq + K by unfold edgeA; linarith)
  have := gtau_lip hτ (show Bq ≤ Bq + K by linarith)
  linarith

open Filter Zeta23 Zeta23.ZeroSide Zeta23.ThmD
open Classical

theorem block_bound_eventually_w'_g_edge (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      gtau (tauq n) (edgeA c n m S ct) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + blkPress W.b (xret Z (mtParams T) T) B + edgePressOn W S (xret Z (mtParams T) T) B := by
  have hm : n ≤ m := by omega
  have hm' : (m : ℝ) ≠ 0 := by have : (0 : ℝ) < m := (by exact_mod_cast (by omega : 0 < m)); positivity
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set A : ℝ := edgeA c n m S ct
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδ0 : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H ((|A| + 1) / bmin) δ hδ0, eventually_L_pos] with T hcl hL
  intro B hB
  set x := xret Z (mtParams T) T
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  have hE0 := edgePressOn_nonneg hW hSk hm x B (by rw [card_image_of_injOn hinj, hB])
  by_cases hsp : spanOf x B ≤ (|A| + 1) / bmin
  · have h13 := block_bound_w'_g_edge (by omega) hm W hW hsym hCert S hSk ct hCt x (gram_posSemidef Z (mtParams T) T)
      B hB hinj hδ0.le fun i hi j hj _ => hcl i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    rwa [show 2 * (m : ℝ) ^ 2 * δ = η by rw [hδ]; field_simp] at h13
  · have hP := (lt_of_lt_of_le (not_le.mp hsp) (spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj))
    rw [div_lt_div_iff_of_pos_right hbmin] at hP
    have : gtau (tauq n) A ≤ |A| := (gtau_le_self (tauq_pos (by omega))).trans (le_abs_self A)
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]

theorem pre_solve_w'_g_edge (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ) (hct0 : ∀ k ∈ S, 0 ≤ ct k)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (AMW.HW - edgeP W m S / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - gtau (tauq n) (edgeA c n m S ct) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hA₀ : 0 < gtau (tauq n) (edgeA c n m S ct) := gtau_pos (tauq_pos hn) (by
    unfold edgeA
    nlinarith [mul_pos hc (by linarith : (0 : ℝ) < (m : ℝ) - ((n : ℝ) - 1)), sum_nonneg hct0])
  have hP0 : (0 : ℝ) ≤ edgeP W m S := by
    unfold edgeP
    nlinarith [mul_nonneg (WCert.B_nonneg hW) (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1)),
      sum_nonneg fun k (_ : k ∈ S) => edgeB_nonneg hW k]
  set A₀ : ℝ := gtau (tauq n) (edgeA c n m S ct)
  set Cn : ℝ := (m : ℝ) + (2 * A₀ + 1) + edgeP W m S with hCn
  have hCn0 : 0 < Cn := by rw [hCn]; linarith
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; positivity
  have hη0 : 0 < min ε₀ A₀ := lt_min hε₀0 hA₀
  have hηε : min ε₀ A₀ ≤ ε₀ := min_le_left _ _
  have hA' : 0 ≤ A₀ - min ε₀ A₀ := by linarith [min_le_right ε₀ A₀]
  filter_upwards [block_bound_eventually_w'_g_edge Z H hn3 h2n W hW hsym hbmin hb hCert S hSk ct hCt hη0,
    deleted_strips Z H _ hη0, span_retained_le Z H _ hη0,
    tail_passage Z H (eventually_h7 Z) _ hη0,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop ((m : ℝ) / min ε₀ A₀),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL
  have h15 := offset_average_edge hn W hW S hSk (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T)) (Dcirc Z (mtParams T) T) (A₀ - min ε₀ A₀)
    hA' (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe, show (∑ r, W.b r) * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, edgeB W k = edgeP W m S from rfl]
    at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ A₀ * (Z.N T (2 * T) : ℝ) := by have := (div_le_iff₀ hη0).mp hNbig; linarith
  set P : ℝ := edgeP W m S
  set η : ℝ := min ε₀ A₀
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ)
  set Sr : ℝ := ((retained Z (mtParams T) T).card : ℝ)
  set D : ℝ := Dcirc Z (mtParams T) T
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ
  clear_value A₀ P η N n0 Sr D sp
  have s1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (Sr - m) := mul_le_mul_of_nonneg_left (by linarith) hA'
  have s2 : P * sp ≤ P * ((1 + η) * N) := mul_le_mul_of_nonneg_left hspan hP0
  have s3 : A₀ * n0 - (2 * A₀ + 1) * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by
    nlinarith [mul_le_mul_of_nonneg_left hn0N hη0.le, mul_nonneg (mul_nonneg hη0.le hη0.le) hN0]
  have s4 : (m : ℝ) * D ≤ m * (n0 - (AMW.HW - η) * N) := mul_le_mul_of_nonneg_left (by linarith) hm0.le
  have s5 : η * ((m : ℝ) + (2 * A₀ + 1) + P) * N ≤ m * ε * N := by
    refine mul_le_mul_of_nonneg_right ?_ hN0
    have h1 := mul_le_mul_of_nonneg_right hηε hCn0.le
    have h2 : ε₀ * Cn = ε * (m : ℝ) := by rw [hε₀]; field_simp
    rw [hCn] at h1 h2
    linarith
  have key : ((m : ℝ) * AMW.HW - P - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by linarith
  rw [show (AMW.HW - P / m - ε) * N = ((m : ℝ) * AMW.HW - P - m * ε) * N / m by field_simp,
    show (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m by field_simp]
  exact div_le_div_of_nonneg_right key hm0.le

/-- the n-point constant with the edge windows, from `A = c (m − q) + 2 Σ ct` and `P = B (m − q) + 2 Σ Bt` -/
def Phi_g_edge (n : ℕ) (A : ℝ) (m : ℕ) (P : ℝ) : ℝ :=
  (AMW.HW - P / m) / (1 - gtau (tauq n) A / m)

lemma one_sub_gtau_div_pos_edge {A : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hAm : A < m) :
    0 < 1 - gtau (tauq n) A / m := by
  have := gtau_le_self (E := A) (tauq_pos hn)
  rw [sub_pos, div_lt_one (by exact_mod_cast hm)]
  linarith

theorem n_point_bound_w'_g_edge (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ) (hct0 : ∀ k ∈ S, 0 ≤ ct k)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    (hAm : edgeA c n m S ct < m) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have hD := one_sub_gtau_div_pos_edge (by omega : 2 ≤ n) (by omega : 0 < m) hAm
  set Dn : ℝ := 1 - gtau (tauq n) (edgeA c n m S ct) / m with hDn
  set K : ℝ := AMW.HW - edgeP W m S / m with hK
  have hpre := pre_solve_w'_g_edge zetaZeroConfig paperInputs_zeta hn3 h2n W hW hsym hbmin hb hc hCert
    S hSk ct hct0 hCt
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at hpre
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hpre (ε * Dn) (mul_pos hε hD))
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  rw [show Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S) - ε = (K - ε * Dn) / Dn by
    unfold Phi_g_edge; rw [← hK, ← hDn]; field_simp, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

/-- the final κ step on the √ branch, with the edge windows: rational `s ≥ 0` with `s² ≤ τ A` and `τ < A`, and
`κ (1 − (2s − τ)/m) ≤ h − P/m` with `h ≤ H_W`, give `κ ≤ Phi_g_edge` -/
theorem Phi_g_edge_ge_sqrt {n : ℕ} {A P κ h s : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hH : h ≤ AMW.HW)
    (hκ0 : 0 ≤ κ) (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ tauq n * A) (hA : tauq n < A) (hAm : A < m)
    (hk : κ * (1 - (2 * s - tauq n) / m) ≤ h - P / m) :
    κ ≤ Phi_g_edge n A m P := by
  have hD := one_sub_gtau_div_pos_edge hn hm hAm
  have h1 : 1 - gtau (tauq n) A / m ≤ 1 - (2 * s - tauq n) / m := by
    linarith [div_le_div_of_nonneg_right (two_mul_sub_le_gtau hs hs2 hA) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  unfold Phi_g_edge
  rw [le_div_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ0]

/-- the final κ step on the linear branch (`A ≤ τ`), with the edge windows -/
theorem Phi_g_edge_ge_lin {n : ℕ} {A P κ h : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hH : h ≤ AMW.HW)
    (hA : A ≤ tauq n) (hAm : A < m) (hk : κ * (1 - A / m) ≤ h - P / m) :
    κ ≤ Phi_g_edge n A m P := by
  have hD := one_sub_gtau_div_pos_edge hn hm hAm
  rw [gtau_of_le hA] at hD
  unfold Phi_g_edge
  rw [gtau_of_le hA, le_div_iff₀ hD]
  linarith

end Zeta23Ext.BridgeW

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- **The n-point bound for the AM window under the √-branch band profile, with edge windows**, from a
reversal-symmetric certificate and certified floors `ct k` of its prefix truncations, `k ∈ S` -/
theorem am_dyadic_n_edge {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ) (hct0 : ∀ k ∈ S, 0 ≤ ct k)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    (hAm : edgeA c n m S ct < m)
    (hκ : κ ≤ Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w'_g_edge n c m W hn hm hW hsym hbmin hb hc hCert S hSk ct hct0 hCt hAm ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 := mul_le_mul_of_nonneg_right (by linarith : κ - ε ≤ Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S) - ε)
    (Nat.cast_nonneg (Zeta23.Ncount T (2 * T)) : (0 : ℝ) ≤ Zeta23.Ncount T (2 * T))
  linarith [hT₀ T hT]

/-- the cumulative form -/
theorem am_cumulative_n_edge {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm)
    (hsym : ∀ a b : Fin n, W.a a b = W.a b.rev a.rev) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (S : Finset ℕ) (hSk : ∀ k ∈ S, k + 2 ≤ n) (ct : ℕ → ℝ) (hct0 : ∀ k ∈ S, 0 ≤ ct k)
    (hCt : ∀ k ∈ S, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ct k ≤ Fw (W.pre k) g)
    (hAm : edgeA c n m S ct < m)
    (hκ : κ ≤ Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
    (am_dyadic_n_edge hn hW hsym hbmin hb hc hm hCert S hSk ct hct0 hCt hAm hκ)

end AMW

end
