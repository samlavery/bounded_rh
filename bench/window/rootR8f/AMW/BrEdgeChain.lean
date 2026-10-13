import AMW.BrSqrtWS
import AMW.BrEdge

/-! ###### AMW/BrEdgeChain — the √-branch block chain with edge windows (bridge-port, clean-room)

`block_energy_band_edge` (AMW/BrEdge) adds, for each `k ∈ S`, two edge windows with `k` gaps and floor `ct k` to the
block energy: `A = c (m − q) + 2 Σ_{k∈S} ct k` (`q = n − 1`), at the extra pressure `edgePressOn`. Each edge pressure
term is one gap at a fixed position of the block, so over the sliding blocks of `offset_average_w` it telescopes to at
most the configuration's span (`offset_average_edge`): the pressure weight becomes
`P = B (m − q) + 2 Σ_{k∈S} Bt k` with `Bt k = Σ_{r<k} b_r`. The chain of AMW/BrSqrtWS then runs with `(A, P)` in
place of `(c (m − q), B (m − q))`: `block_bound_w'_g_edge`, `block_bound_eventually_w'_g_edge`, `pre_solve_w'_g_edge`,
`Phi_g_edge`, `n_point_bound_w'_g_edge`, `Phi_g_edge_ge_sqrt`, `Phi_g_edge_ge_lin`, and `AMW.am_dyadic_n_edge`,
`AMW.am_cumulative_n_edge`. Everything is parameterised over `S`, the floors `ct` and their certificates. ###### -/

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
  simp only [WCert.pre]
  split_ifs with h
  · exact hW.b_nonneg _
  · exact le_rfl

lemma edgeB_nonneg {n : ℕ} {W : WCert n} (hW : W.Adm) (k : ℕ) : 0 ≤ edgeB W k :=
  sum_nonneg fun r _ => pre_b_nonneg hW k r

/-- the edge windows' pressure on a block `B` -/
def edgePressOn {n : ℕ} (W : WCert n) (S : Finset ℕ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ k ∈ S, edgePress W k (B.image x).card (sortedOn x B)

/-- the edge pressure on a block is nonnegative (its gaps are gaps of the sorted block) -/
lemma edgePressOn_nonneg {n m : ℕ} {W : WCert n} (hW : W.Adm) {S : Finset ℕ} (hSk : ∀ k ∈ S, k + 2 ≤ n)
    (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hic : (B.image x).card = m) : 0 ≤ edgePressOn W S x B := by
  unfold edgePressOn
  refine sum_nonneg fun k hk => ?_
  have hk2 := hSk k hk
  unfold edgePress
  refine sum_nonneg fun r _ => mul_nonneg (pre_b_nonneg hW k r) ?_
  have hr := r.2
  have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
  have hg : ∀ a b, a ≤ b → b < (B.image x).card → sortedOn x B a ≤ sortedOn x B b := by
    intro a b hab hb
    unfold sortedOn
    rw [sortedExt_of_lt _ (lt_of_le_of_lt hab hb), sortedExt_of_lt _ hb]
    exact hmono.monotone (Fin.mk_le_mk.mpr hab)
  rw [hic] at hg ⊢
  have h1 := hg (m - 1 - k + r) (m - 1 - k + ((r : ℕ) + 1)) (by omega) (by omega)
  have h2 := hg (k - ((r : ℕ) + 1)) (k - r) (by omega) (by omega)
  linarith

/-! ### the offset average with the edge pressure -/

section Abstract

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
  set b := W.b with hbdef
  have hb : ∀ r, 0 ≤ b r := hW.b_nonneg
  set N := Fintype.card ι with hNdef
  set Bt : ℝ := ∑ r, b r with hBt
  set Be : ℝ := ∑ k ∈ S, edgeB W k with hBe
  have hBt0 : 0 ≤ Bt := sum_nonneg fun r _ => hb r
  have hBe0 : 0 ≤ Be := sum_nonneg fun k _ => edgeB_nonneg hW k
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hmn' : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hmq0 : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith

  rcases lt_or_ge N m with hnm | hnm
  · have : (N : ℝ) - m ≤ 0 := by
      have : (N : ℝ) < m := by exact_mod_cast hnm
      linarith
    nlinarith [mul_nonneg hBt0 (mul_nonneg hmq0 hspan0), mul_nonneg hBe0 hspan0,
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - N), mul_nonneg (by positivity : (0:ℝ) ≤ m) hDtot]

  have hS : (univ.image x).card = N := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin N → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hymem k)
  have hι'inj : Function.Injective ι' := by
    intro k k' h
    apply hymono.injective
    rw [← (hι' k).2, ← (hι' k').2, h]
  have hbij : Function.Bijective ι' :=
    (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, by simp [hNdef]⟩
  set e : Fin N ≃ ι := Equiv.ofBijective ι' hbij with hedef
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hposdef
  set Y := sortedExt y with hYdef
  have hpos_lt : ∀ i, pos i < N := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := by
    intro a b hab hb
    rw [hYdef, sortedExt_of_lt y (lt_trans hab hb), sortedExt_of_lt y hb]
    exact hymono (Fin.mk_lt_mk.mpr hab)
  -- two points of the configuration differ by at most the span
  have hYspan : ∀ a c, a < N → c < N → Y a - Y c ≤ spanOf x univ := by
    intro a c ha hc
    obtain ⟨i, -, hi⟩ := mem_image.mp (hymem ⟨a, ha⟩)
    obtain ⟨j, -, hj⟩ := mem_image.mp (hymem ⟨c, hc⟩)
    rw [hYdef, sortedExt_of_lt y ha, sortedExt_of_lt y hc, ← hi, ← hj]
    exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i) (mem_univ j))

  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBdef
  have hmemB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := by
    intro s i; simp [hBdef]
  set toFin : ℕ → Fin N := fun t => if h : t < N then ⟨t, h⟩ else ⟨0, by omega⟩ with htoFin
  have hcardB : ∀ s, s + m ≤ N → (B s).card = m := by
    intro s hs
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (toFin t)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_coe, hmemB] at hi
        rw [mem_coe, mem_Ico]; exact hi
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmemB]
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
        exact ht
      · intro i hi
        have h := hpos_lt i
        simp only [htoFin, dif_pos h]
        simp only [hposdef, Fin.eta, Equiv.apply_symm_apply]
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hintB : ∀ s, IsInterval x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega

  have hsortB : ∀ s, s + m ≤ N → ∀ k, k < m → sortedOn x (B s) k = Y (s + k) := by
    intro s hs k hk
    have hxinj : Set.InjOn x (B s) := hx.injOn
    have hic : ((B s).image x).card = m := by rw [card_image_of_injOn hxinj, hcardB s hs]
    rw [sortedOn_eq hic, sortedExt_of_lt _ hk]
    set f : Fin m → ℝ := fun j => Y (s + j) with hf
    have hfs : ∀ j, f j ∈ (B s).image x := by
      intro j
      have hj : s + (j : ℕ) < N := by have := j.2; omega
      refine mem_image.mpr ⟨e ⟨s + j, hj⟩, ?_, ?_⟩
      · rw [hmemB, hposdef]
        simp only [Equiv.symm_apply_apply]
        have := j.2
        constructor <;> omega
      · rw [hxY, hposdef]
        simp only [hf, Equiv.symm_apply_apply]
    have hmono : StrictMono f := by
      intro j j' hj
      simp only [hf]
      have := j'.2
      exact hYlt _ _ (by have := Fin.lt_def.mp hj; omega) (by omega)
    have := Finset.orderEmbOfFin_unique hic hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]

  set St := range (N - m + 1) with hStdef
  have hmemSt : ∀ s, s ∈ St ↔ s + m ≤ N := by
    intro s; rw [hStdef, mem_range]; omega
  have hsumblock : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s)
      + ∑ s ∈ St, edgePressOn W S x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, sum_add_distrib] at h
    have hcast : ((N - m + 1 : ℕ) : ℝ) = (N : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith

  have hpress : ∑ s ∈ St, blkPress b x (B s) ≤ Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
    have hY0 : ∀ r : Fin (n - 1), ∀ i ∈ range (m - (n - 1)),
        Y (N - m + 1 + i + r) - Y (i + r) ≤ spanOf x univ := by
      intro r i hi
      rw [mem_range] at hi
      have hr := r.2
      exact hYspan _ _ (by omega) (by omega)
    have hblk : ∀ s ∈ St, blkPress b x (B s)
        = ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) := by
      intro s hs
      have hs' := (hmemSt s).mp hs
      unfold blkPress
      have hic : ((B s).image x).card = m := by
        rw [card_image_of_injOn hx.injOn, hcardB s hs']
      rw [hic]
      refine sum_congr rfl fun r _ => ?_
      have hr := r.2
      rw [hsortB s hs' _ (by omega), hsortB s hs' _ (by omega)]
    calc ∑ s ∈ St, blkPress b x (B s)
        = ∑ s ∈ St, ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) :=
          sum_congr rfl hblk
      _ = ∑ r : Fin (n - 1), b r * ∑ s ∈ St, (Y (s + (m - (n - 1)) + r) - Y (s + r)) := by
          rw [sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun s _ => ?_
          congr 3
          omega
      _ = ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), (Y (N - m + 1 + i + r) - Y (i + r)) := by
          refine sum_congr rfl fun r _ => ?_
          congr 1
          have := sum_shift_sub (fun t => Y (t + r)) (m - (n - 1)) (N - m + 1)
          simpa only [hStdef] using this
      _ ≤ ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), spanOf x univ := by
          refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (sum_le_sum (hY0 r)) (hb r)
      _ = Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
          rw [sum_const, card_range, nsmul_eq_mul, ← sum_mul, ← hBt]
          have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
            rw [Nat.cast_sub (by omega : n - 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          rw [hcast]; ring

  -- the edge pressure: one gap at a fixed block position telescopes over the sliding blocks
  have hgap : ∀ p, p + 1 < m → ∑ s ∈ St, (Y (s + (p + 1)) - Y (s + p)) ≤ spanOf x univ := by
    intro p hp
    have htel := Finset.sum_range_sub (fun s => Y (s + p)) (N - m + 1)
    have e : ∑ s ∈ St, (Y (s + (p + 1)) - Y (s + p)) = ∑ s ∈ range (N - m + 1), (Y (s + 1 + p) - Y (s + p)) := by
      rw [hStdef]
      refine sum_congr rfl fun s _ => ?_
      congr 2
      omega
    rw [e, htel]
    simp only [zero_add]
    exact hYspan _ _ (by omega) (by omega)
  have hepress : ∑ s ∈ St, edgePressOn W S x (B s) ≤ 2 * Be * spanOf x univ := by
    have hedge : ∀ s ∈ St, edgePressOn W S x (B s) = ∑ k ∈ S, ∑ r : Fin (k + 1 - 1), (W.pre k).b r *
        ((Y (s + (m - 1 - k + ((r : ℕ) + 1))) - Y (s + (m - 1 - k + r)))
          + (Y (s + ((k - ((r : ℕ) + 1)) + 1)) - Y (s + (k - ((r : ℕ) + 1))))) := by
      intro s hs
      have hs' := (hmemSt s).mp hs
      have hic : ((B s).image x).card = m := by
        rw [card_image_of_injOn hx.injOn, hcardB s hs']
      unfold edgePressOn
      rw [hic]
      refine sum_congr rfl fun k hk => ?_
      have hk2 := hSk k hk
      unfold edgePress
      refine sum_congr rfl fun r _ => ?_
      have hr := r.2
      rw [hsortB s hs' _ (by omega), hsortB s hs' _ (by omega), hsortB s hs' _ (by omega),
        hsortB s hs' _ (by omega), show (k : ℕ) - (r : ℕ) = k - ((r : ℕ) + 1) + 1 by omega]
    calc ∑ s ∈ St, edgePressOn W S x (B s)
        = ∑ s ∈ St, ∑ k ∈ S, ∑ r : Fin (k + 1 - 1), (W.pre k).b r *
            ((Y (s + (m - 1 - k + ((r : ℕ) + 1))) - Y (s + (m - 1 - k + r)))
              + (Y (s + ((k - ((r : ℕ) + 1)) + 1)) - Y (s + (k - ((r : ℕ) + 1))))) := sum_congr rfl hedge
      _ = ∑ k ∈ S, ∑ r : Fin (k + 1 - 1), (W.pre k).b r *
            (∑ s ∈ St, (Y (s + ((m - 1 - k + r) + 1)) - Y (s + (m - 1 - k + r)))
              + ∑ s ∈ St, (Y (s + ((k - ((r : ℕ) + 1)) + 1)) - Y (s + (k - ((r : ℕ) + 1))))) := by
          rw [sum_comm]
          refine sum_congr rfl fun k _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun s _ => ?_
          rw [show m - 1 - k + ((r : ℕ) + 1) = (m - 1 - k + r) + 1 by omega]
      _ ≤ ∑ k ∈ S, ∑ r : Fin (k + 1 - 1), (W.pre k).b r * (spanOf x univ + spanOf x univ) := by
          refine sum_le_sum fun k hk => sum_le_sum fun r _ => ?_
          have hk2 := hSk k hk
          have hr := r.2
          refine mul_le_mul_of_nonneg_left (add_le_add (hgap _ (by omega)) (hgap _ (by omega)))
            (pre_b_nonneg hW k r)
      _ = 2 * Be * spanOf x univ := by
          rw [hBe, mul_sum, sum_mul]
          refine sum_congr rfl fun k _ => ?_
          unfold edgeB
          rw [mul_sum, sum_mul]
          refine sum_congr rfl fun r _ => ?_
          ring

  have hdefects : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j hj => ?_
          set β : ι → Fin (N + 1) := fun i =>
            ⟨blockStart N m j (pos i), Nat.lt_succ_of_le (blockStart_le N m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ N) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact blockStart_eq_iff hm0 hs hj
          set toFin' : ℕ → Fin (N + 1) := fun s => if h : s < N + 1 then ⟨s, h⟩ else 0 with htoFin'
          have hinj : Set.InjOn toFin' (St.filter (fun s => s % m = j)) := by
            intro s hs s' hs' h
            rw [mem_coe, mem_filter, hmemSt] at hs hs'
            simp only [htoFin', dif_pos (by omega : s < N + 1), dif_pos (by omega : s' < N + 1),
              Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = toFin' s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmemSt] at hs
                have hsn : s < N + 1 := by omega
                rw [← hclass s hs.1 hs.2]
                congr 2
                simp only [htoFin', dif_pos hsn]
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image toFin',
                  Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (N + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]

  have hmn : (m : ℝ) ≤ N := by exact_mod_cast hnm
  have hA1 : A * ((N : ℝ) - m) ≤ A * ((N : ℝ) - m + 1) := by linarith
  have e1 : (Bt * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * Be) * spanOf x univ
      = Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ + 2 * Be * spanOf x univ := by ring
  rw [e1]
  linarith

end Abstract

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
  set x' : B → ℝ := fun i => x i with hx'def
  have hx' : Function.Injective x' := fun i j h => Subtype.ext (hx i.2 j.2 h)
  have hcard : Fintype.card B = m := by simp [hB]
  have hS : (univ.image x').card = m := by rw [card_image_of_injective _ hx', card_univ, hcard]
  have hE := block_energy_band_edge hn W hW hsym hCert S hSk ct hCt hm x' hx' hS
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
  have hEe : edgePressOn W S x' univ = edgePressOn W S x B := by
    unfold edgePressOn sortedOn
    rw [sortedOn_congr himg, himg]
  have hEe2 : ∑ k ∈ S, edgePress W k m (sortedExt ((univ.image x').orderEmbOfFin hS)) = edgePressOn W S x' univ := by
    unfold edgePressOn
    rw [hS]
    refine sum_congr rfl fun k _ => ?_
    congr 1
    funext j
    exact (sortedOn_eq hS j).symm
  rw [hPe, hEe2, hEe] at hE
  have hcl' : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ) i j - (kfun (x' i - x' j) : ℂ)‖ ≤ δ :=
    fun i j h => hclose i i.2 j j.2 (fun e => h (Subtype.ext e))
  have hC := band_close hx' hS hcard (n - 1) (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) hδ hcl'
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
    have hr2 := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
    rw [sub_nonneg, sortedExt_of_lt _ hk, sortedExt_of_lt _ hr]
    exact hmono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hE0 := edgePressOn_nonneg hW hSk hm x B hic
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  have hτ : 0 < tauq n := tauq_pos hn
  set Bq := bandSq (G.submatrix (Subtype.val : B → κ) (Subtype.val : B → κ)) (fun i => (sRank x' hS i : ℕ)) (n - 1)
    with hBq
  set K : ℝ := 2 * (m : ℝ) ^ 2 * δ + blkPress W.b x B + edgePressOn W S x B with hK
  have hA : edgeA c n m S ct ≤ Bq + K := by rw [hK]; unfold edgeA; linarith
  have h1 := gtau_mono hτ hA
  have h2 := gtau_lip hτ (show Bq ≤ Bq + K by rw [hK]; linarith)
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
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  have hτ : 0 < tauq n := tauq_pos hn
  set A : ℝ := edgeA c n m S ct with hA
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H ((|A| + 1) / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hinj, hB]
  have hE0 := edgePressOn_nonneg hW hSk hm x B hic
  by_cases hsp : spanOf x B ≤ (|A| + 1) / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w'_g_edge hn hm W hW hsym hCert S hSk ct hCt x (gram_posSemidef Z (mtParams T) T) B hB
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
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hmq : (1 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith
  have hτ : 0 < tauq n := tauq_pos hn
  have hct : 0 ≤ ∑ k ∈ S, ct k := sum_nonneg hct0
  have hApos : 0 < edgeA c n m S ct := by
    unfold edgeA
    have := mul_pos hc (by linarith : (0 : ℝ) < (m : ℝ) - ((n : ℝ) - 1))
    linarith
  have hA₀pos : 0 < gtau (tauq n) (edgeA c n m S ct) := gtau_pos hτ hApos
  have hq0 : (0 : ℝ) ≤ W.B := WCert.B_nonneg hW
  have hP0 : (0 : ℝ) ≤ edgeP W m S := by
    unfold edgeP
    have h1 := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    have h2 : 0 ≤ ∑ k ∈ S, edgeB W k := sum_nonneg fun k _ => edgeB_nonneg hW k
    linarith
  set A₀ : ℝ := gtau (tauq n) (edgeA c n m S ct) with hA₀
  set Cn : ℝ := (m : ℝ) + (2 * A₀ + 1) + edgeP W m S with hCn
  have hCnpos : 0 < Cn := by rw [hCn]; linarith
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ A₀ := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ A₀ ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ A₀ ≤ A₀ := min_le_right _ _
  have hA' : 0 ≤ A₀ - min ε₀ A₀ := by linarith
  filter_upwards [block_bound_eventually_w'_g_edge Z H hn3 h2n W hW hsym hbmin hb hCert S hSk ct hCt hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop ((m : ℝ) / min ε₀ A₀),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL
  have h15 := offset_average_edge hn W hW S hSk (xret Z (mtParams T) T)
    (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (A₀ - min ε₀ A₀)
    hA' (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hPeq : (∑ r, W.b r) * ((m : ℝ) - ((n : ℝ) - 1)) + 2 * ∑ k ∈ S, edgeB W k = edgeP W m S := rfl
  rw [hPeq] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ A₀ * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith
  set P : ℝ := edgeP W m S with hP
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set Sr : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ P η N n0 Sr D sp
  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (Sr - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : P * sp ≤ P * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan hP0
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - (2 * A₀ + 1) * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by nlinarith [e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (AMW.HW - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + (2 * A₀ + 1) + P) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + (2 * A₀ + 1) + P) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + (2 * A₀ + 1) + P) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * AMW.HW - P - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (AMW.HW - P / m - ε) * N
      = ((m : ℝ) * AMW.HW - P - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

/-- the n-point constant with the edge windows, from `A = c (m − q) + 2 Σ ct` and `P = B (m − q) + 2 Σ Bt` -/
def Phi_g_edge (n : ℕ) (A : ℝ) (m : ℕ) (P : ℝ) : ℝ :=
  (AMW.HW - P / m) / (1 - gtau (tauq n) A / m)

lemma one_sub_gtau_div_pos_edge {A : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hAm : A < m) :
    0 < 1 - gtau (tauq n) A / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have := gtau_le_self (E := A) (tauq_pos hn)
  rw [sub_pos, div_lt_one hmpos]
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
  have hn : 2 ≤ n := by omega
  have hD := one_sub_gtau_div_pos_edge hn (by omega : 0 < m) hAm
  set Dn : ℝ := 1 - gtau (tauq n) (edgeA c n m S ct) / m with hDn
  set K : ℝ := AMW.HW - edgeP W m S / m with hK
  have hpre := pre_solve_w'_g_edge zetaZeroConfig paperInputs_zeta hn3 h2n W hW hsym hbmin hb hc hCert
    S hSk ct hct0 hCt
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at hpre
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hpre (ε * Dn) (mul_pos hε hD))
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hPhi : Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S) - ε = (K - ε * Dn) / Dn := by
    unfold Phi_g_edge
    rw [← hK, ← hDn]
    field_simp
  rw [hPhi, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

/-- the final κ step on the √ branch, with the edge windows: rational `s ≥ 0` with `s² ≤ τ A` and `τ < A`, and
`κ (1 − (2s − τ)/m) ≤ h − P/m` with `h ≤ H_W`, give `κ ≤ Phi_g_edge` -/
theorem Phi_g_edge_ge_sqrt {n : ℕ} {A P κ h s : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (hH : h ≤ AMW.HW)
    (hκ0 : 0 ≤ κ) (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ tauq n * A) (hA : tauq n < A) (hAm : A < m)
    (hk : κ * (1 - (2 * s - tauq n) / m) ≤ h - P / m) :
    κ ≤ Phi_g_edge n A m P := by
  have hD := one_sub_gtau_div_pos_edge hn hm hAm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hg := two_mul_sub_le_gtau hs hs2 hA
  have h1 : 1 - gtau (tauq n) A / m ≤ 1 - (2 * s - tauq n) / m := by
    have := div_le_div_of_nonneg_right hg hmpos.le
    linarith
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
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (Phi_g_edge n (edgeA c n m S ct) m (edgeP W m S) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

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
