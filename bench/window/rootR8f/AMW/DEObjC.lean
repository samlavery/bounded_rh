import AMW.DEObjB

/-! ###### AMW/DEObjC — counting for the on-line instance (bridge-port)

* `N_le_short`: `N(t, t + H] ≤ (H + 1) A₀ log(|t| + H + 4)` from the local count.
* `bulkFin`: the zeros of `(T, 2T]` at normalised distance `≥ L²` from the walls;
  `sum_mult_le_bulk_add`: `N(T, 2T) ≤ Σ_bulk m + N(T, T + ℓ] + N(2T − ℓ', 2T]`, and `sum_sq_le_bulk_add` for `Σ m²`.
* `ordSq_eq_of_online`: on an on-line window the ordinate classes are single zeros, `ordSq = Σ m²`. ###### -/

noncomputable section

open Finset Real Filter Topology
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

open Classical

/-! ### Short intervals -/

theorem N_nat_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (t : ℝ) (n : ℕ) :
    (Z.N t (t + n) : ℝ) ≤ n * A₀ * Real.log (|t| + n + 3) := by
  induction n with
  | zero => simp [Assembly.N_self]
  | succ n ih =>
    have hadd := Assembly.N_add Z (a := t) (b := t + n) (c := t + (n + 1 : ℕ))
      (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (by push_cast; linarith)
    have h1 := hloc (t + n)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    set X : ℝ := Real.log (|t| + ((n : ℝ) + 1) + 3) with hX
    have hlog1 : Real.log (|t| + n + 3) ≤ X := by
      apply Real.log_le_log (by positivity); linarith
    have hlog2 : Real.log (|t + n| + 3) ≤ X := by
      apply Real.log_le_log (by positivity)
      have := abs_add_le t (n : ℝ)
      rw [abs_of_nonneg hn0] at this
      linarith
    rw [hadd]
    push_cast
    rw [show t + ((n : ℝ) + 1) = t + n + 1 by ring]
    have a1 : (Z.N t (t + n) : ℝ) ≤ n * A₀ * X :=
      ih.trans (mul_le_mul_of_nonneg_left hlog1 (mul_nonneg hn0 hA₀))
    have a2 : (Z.N (t + n) (t + n + 1) : ℝ) ≤ A₀ * X :=
      h1.trans (mul_le_mul_of_nonneg_left hlog2 hA₀)
    calc (Z.N t (t + n) : ℝ) + Z.N (t + n) (t + n + 1) ≤ n * A₀ * X + A₀ * X := add_le_add a1 a2
      _ = ((n : ℝ) + 1) * A₀ * X := by ring

theorem N_mono_right (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.N a b ≤ Z.N a c := by
  rw [Assembly.N_add Z hab hbc]; exact Nat.le_add_right _ _

/-- **a short interval**: `N(t, t + H] ≤ (H + 1) A₀ log(|t| + H + 4)` -/
theorem N_le_short (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (t : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (Z.N t (t + H) : ℝ) ≤ (H + 1) * A₀ * Real.log (|t| + H + 4) := by
  set n := ⌈H⌉₊ with hn
  have hn1 : H ≤ n := Nat.le_ceil H
  have hn2 : (n : ℝ) < H + 1 := Nat.ceil_lt_add_one hH
  have hm := N_mono_right Z (a := t) (b := t + H) (c := t + n) (by linarith) (by linarith)
  have hb := N_nat_le Z hA₀ hloc t n
  have hlog : Real.log (|t| + n + 3) ≤ Real.log (|t| + H + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log (|t| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  calc (Z.N t (t + H) : ℝ) ≤ Z.N t (t + n) := by exact_mod_cast hm
    _ ≤ n * A₀ * Real.log (|t| + n + 3) := hb
    _ ≤ (H + 1) * A₀ * Real.log (|t| + H + 4) := by
        have h1 : (n : ℝ) * A₀ ≤ (H + 1) * A₀ := mul_le_mul_of_nonneg_right hn2.le hA₀
        calc (n : ℝ) * A₀ * Real.log (|t| + n + 3) ≤ (H + 1) * A₀ * Real.log (|t| + n + 3) :=
              mul_le_mul_of_nonneg_right h1 hl0
          _ ≤ (H + 1) * A₀ * Real.log (|t| + H + 4) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)

/-! ### The bulk -/

/-- the zeros of `(T, 2T]` at normalised distance `≥ L²` from the walls -/
def bulkFin (Z : ZeroConfig) (P : Params) (T : ℝ) : Finset ℂ :=
  (winFin Z T).filter fun ρ => P.L T ^ 2 ≤ xr P T ρ.im ∧ xr P T ρ.im ≤ (P.d T : ℝ) - P.L T ^ 2

theorem winFin_subset_ZI (Z : ZeroConfig) (T : ℝ) : winFin Z T ⊆ ZI Z T := by
  intro ρ hρ
  have h := mem_winFin.mp hρ
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  rw [mem_ZI]
  exact ⟨h.1, by linarith [h.2.1], by linarith [h.2.2]⟩

theorem bulkFin_subset (Z : ZeroConfig) (P : Params) (T : ℝ) : bulkFin Z P T ⊆ winFin Z T :=
  filter_subset _ _

/-- a zero of `(T, 2T]` outside the bulk is within `ℓ` of `T` or within `ℓ'` of `2T` -/
theorem not_bulk_near_wall {P : Params} {T : ℝ} (hL : 0 < P.L T) {γ : ℝ}
    (h : ¬(P.L T ^ 2 ≤ xr P T γ ∧ xr P T γ ≤ (P.d T : ℝ) - P.L T ^ 2)) :
    γ ≤ T + 2 * Real.pi * P.L T ∨ 2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T) < γ := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [not_and_or] at h
  rcases h with h | h
  · left
    push Not at h
    unfold xr at h
    have h1 := (div_lt_iff₀ hπ).mp h
    have : P.L T * (γ - T) < P.L T * (2 * Real.pi * P.L T) := by nlinarith
    have := lt_of_mul_lt_mul_left this hL.le
    linarith
  · right
    push Not at h
    unfold xr at h
    have h1 := (lt_div_iff₀ hπ).mp h
    have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd' := (div_lt_iff₀ hπ).mp hd
    have e : P.L T * (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T))
        = 2 * P.L T * T - 2 * Real.pi * P.L T ^ 2 - 2 * Real.pi := by
      field_simp
      ring
    have : P.L T * (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) < P.L T * γ := by
      rw [e]; nlinarith
    exact lt_of_mul_lt_mul_left this hL.le

/-- the sum over a sub-family of a window is at most `N` -/
theorem sum_mult_le_N (Z : ZeroConfig) (s : Finset ℂ) {a b : ℝ}
    (hs : ∀ ρ ∈ s, ρ ∈ Z.carrier ∧ a < ρ.im ∧ ρ.im ≤ b) :
    ∑ ρ ∈ s, (Z.mult ρ : ℝ) ≤ Z.N a b := by
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  have hN : (Z.N a b : ℝ) = ∑ ρ ∈ hfin.toFinset, (Z.mult ρ : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast; rfl
  rw [hN]
  refine sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) fun _ _ _ => Nat.cast_nonneg _
  rw [Set.Finite.mem_toFinset]
  exact hs ρ hρ

/-- the edge part of the window -/
def edgeFin (Z : ZeroConfig) (P : Params) (T : ℝ) : Finset ℂ :=
  (winFin Z T).filter fun ρ => ¬(P.L T ^ 2 ≤ xr P T ρ.im ∧ xr P T ρ.im ≤ (P.d T : ℝ) - P.L T ^ 2)

/-- the edge mass is at most the two wall counts -/
theorem edge_le (Z : ZeroConfig) {P : Params} {T : ℝ} (hL : 0 < P.L T) :
    ∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ)
      ≤ Z.N T (T + 2 * Real.pi * P.L T) + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
  set E := edgeFin Z P T with hE
  set E1 := E.filter fun ρ => ρ.im ≤ T + 2 * Real.pi * P.L T with hE1
  set E2 := E.filter fun ρ => ¬ρ.im ≤ T + 2 * Real.pi * P.L T with hE2
  rw [← sum_filter_add_sum_filter_not E (fun ρ => ρ.im ≤ T + 2 * Real.pi * P.L T)]
  have hmem : ∀ ρ ∈ E, ρ ∈ Z.carrier ∧ T < ρ.im ∧ ρ.im ≤ 2 * T := fun ρ hρ =>
    mem_winFin.mp (mem_filter.mp hρ).1
  refine add_le_add (sum_mult_le_N Z _ fun ρ hρ => ?_) (sum_mult_le_N Z _ fun ρ hρ => ?_)
  · obtain ⟨h1, h2⟩ := mem_filter.mp hρ
    exact ⟨(hmem ρ h1).1, (hmem ρ h1).2.1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_filter.mp hρ
    have hw := not_bulk_near_wall hL (mem_filter.mp h1).2
    rcases hw with hw | hw
    · exact absurd hw h2
    · exact ⟨(hmem ρ h1).1, hw, (hmem ρ h1).2.2⟩

theorem N_eq_bulk_add_edge (Z : ZeroConfig) (P : Params) (T : ℝ) :
    (Z.N T (2 * T) : ℝ) = ∑ ρ ∈ bulkFin Z P T, (Z.mult ρ : ℝ) + ∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ) := by
  rw [N_eq_sum_winFin, bulkFin, edgeFin, sum_filter_add_sum_filter_not]
  push_cast; rfl

/-- `N(T, 2T] ≤ Σ_bulk m + (wall counts)` -/
theorem sum_mult_le_bulk_add (Z : ZeroConfig) {P : Params} {T : ℝ} (hL : 0 < P.L T) :
    (Z.N T (2 * T) : ℝ) ≤ ∑ ρ ∈ bulkFin Z P T, (Z.mult ρ : ℝ)
      + (Z.N T (T + 2 * Real.pi * P.L T) + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T)) := by
  rw [N_eq_bulk_add_edge Z P T]
  linarith [edge_le Z hL]

/-- `Σ_{(T,2T]} m² ≤ Σ_bulk m² + (wall counts)²` -/
theorem sum_sq_le_bulk_add (Z : ZeroConfig) {P : Params} {T : ℝ} (hL : 0 < P.L T) :
    ∑ ρ ∈ winFin Z T, (Z.mult ρ : ℝ) ^ 2 ≤ ∑ ρ ∈ bulkFin Z P T, (Z.mult ρ : ℝ) ^ 2
      + ((Z.N T (T + 2 * Real.pi * P.L T) : ℝ)
        + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T)) ^ 2 := by
  rw [← sum_filter_add_sum_filter_not (winFin Z T)
    (fun ρ => P.L T ^ 2 ≤ xr P T ρ.im ∧ xr P T ρ.im ≤ (P.d T : ℝ) - P.L T ^ 2)]
  refine add_le_add le_rfl ?_
  show ∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ) ^ 2 ≤ _
  have hsq : ∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ) ^ 2 ≤ (∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ)) ^ 2 := by
    rw [sq (∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ)), sum_mul_sum]
    refine sum_le_sum fun ρ hρ => ?_
    rw [sq]
    exact single_le_sum (f := fun ρ' => (Z.mult ρ : ℝ) * (Z.mult ρ' : ℝ))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hρ
  have he := edge_le Z hL
  have he0 : 0 ≤ ∑ ρ ∈ edgeFin Z P T, (Z.mult ρ : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  exact hsq.trans (pow_le_pow_left₀ he0 he 2)

/-- on an on-line window the ordinate classes are single zeros -/
theorem ordSq_eq_of_online (Z : ZeroConfig) (T : ℝ) (hon : ∀ ρ ∈ winFin Z T, ρ.re = 1 / 2) :
    (ordSq Z T : ℝ) = ∑ ρ ∈ winFin Z T, (Z.mult ρ : ℝ) ^ 2 := by
  have hinj : Set.InjOn Complex.im (winFin Z T : Set ℂ) := by
    intro ρ hρ ρ' hρ' h
    exact Complex.ext ((hon ρ hρ).trans (hon ρ' hρ').symm) h
  unfold ordSq
  rw [sum_image hinj]
  push_cast
  refine sum_congr rfl fun ρ hρ => ?_
  unfold ordMult
  have : (winFin Z T).filter (fun ρ' => ρ'.im = ρ.im) = {ρ} := by
    ext ρ'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact hinj h1 hρ h2
    · rintro rfl; exact ⟨hρ, rfl⟩
  rw [this, sum_singleton]

end Zeta23Ext.Bridge

end
