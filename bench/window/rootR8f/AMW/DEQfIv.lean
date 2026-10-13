import AMW.Trig
import AMW.DEQf

/-! ###### AMW/DEQfIv — rational interval enclosures for the closed form of `qf` (mvt-engine; D track, step 6)

Intervals are pairs of rationals read with `AMW.InI` (`lo ≤ x ≤ hi`), rounded outwards to `10⁻¹⁵` after each product.
On top of the exact operations: `sin`, `cos` on `[0, 1]` from `Trig`'s twelve-term Taylor bound, `π` and `√2` to
twenty digits, the frequencies `ωAM`, the per-pair coefficients of `AMW/DEQf` (`axq` … `byq`, through the exact
values of `sin`, `cos` at `θ₀ ± kπ` and `kπ`), the collected coefficients `Aq`, `Bq`, `Cq`, and their images under
the derivative map.  Every enclosure is a function with a soundness theorem; nothing here is decided. ###### -/

noncomputable section

open Real

namespace AMW.DQ

open AMW

abbrev IQ := ℚ × ℚ

/-! ## Outward rounding -/

def SCL : ℚ := 1000000000000000

def rdn (x : ℚ) : ℚ := ((⌊x * SCL⌋ : ℤ) : ℚ) / SCL
def rup (x : ℚ) : ℚ := ((⌈x * SCL⌉ : ℤ) : ℚ) / SCL

theorem SCL_pos : (0 : ℚ) < SCL := by norm_num [SCL]

theorem rdn_le (x : ℚ) : ((rdn x : ℚ) : ℝ) ≤ (x : ℝ) := by
  refine Rat.cast_le.mpr ?_
  unfold rdn; rw [div_le_iff₀ SCL_pos]; exact Int.floor_le _

theorem le_rup (x : ℚ) : (x : ℝ) ≤ ((rup x : ℚ) : ℝ) := by
  refine Rat.cast_le.mpr ?_
  unfold rup; rw [le_div_iff₀ SCL_pos]; exact Int.le_ceil _

def rnd (X : IQ) : IQ := (rdn X.1, rup X.2)

theorem iv_rnd {X : IQ} {x : ℝ} (h : InI X x) : InI (rnd X) x :=
  ⟨(rdn_le _).trans h.1, h.2.trans (le_rup _)⟩

/-! ## Exact and rounded operations -/

def pt (q : ℚ) : IQ := (q, q)
theorem iv_pt (q : ℚ) : InI (DQ.pt q) (q : ℝ) := ⟨le_rfl, le_rfl⟩

def add (X Y : IQ) : IQ := (X.1 + Y.1, X.2 + Y.2)
def sub (X Y : IQ) : IQ := (X.1 - Y.2, X.2 - Y.1)
def neg (X : IQ) : IQ := (-X.2, -X.1)

theorem iv_add {X Y : IQ} {x y : ℝ} (hx : InI X x) (hy : InI Y y) : InI (DQ.add X Y) (x + y) := by
  unfold DQ.add InI at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
theorem iv_sub {X Y : IQ} {x y : ℝ} (hx : InI X x) (hy : InI Y y) : InI (DQ.sub X Y) (x - y) := by
  unfold DQ.sub InI at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
theorem iv_neg {X : IQ} {x : ℝ} (hx : InI X x) : InI (DQ.neg X) (-x) := by
  unfold DQ.neg InI at *; push_cast; constructor <;> linarith [hx.1, hx.2]

theorem mul_bounds {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have k1 : min (a * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact min_le_of_left_le (mul_le_mul_of_nonneg_right ha hy)
    · exact min_le_of_right_le (mul_le_mul_of_nonpos_right hb hy)
  have k2 : x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hb hy)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ha hy)
  have k3 : ∀ e : ℝ, min (e * c) (e * d) ≤ e * y ∧ e * y ≤ max (e * c) (e * d) := by
    intro e
    rcases le_total 0 e with he | he
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left hc he),
        le_max_of_le_right (mul_le_mul_of_nonneg_left hd he)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left hd he),
        le_max_of_le_left (mul_le_mul_of_nonpos_left hc he)⟩
  constructor
  · refine le_trans ?_ k1
    exact le_min (min_le_of_left_le (k3 a).1) (min_le_of_right_le (k3 b).1)
  · refine k2.trans ?_
    exact max_le (le_max_of_le_left (k3 a).2) (le_max_of_le_right (k3 b).2)

/-- the product, rounded outwards -/
def mul (X Y : IQ) : IQ :=
  rnd (min (min (X.1 * Y.1) (X.1 * Y.2)) (min (X.2 * Y.1) (X.2 * Y.2)),
       max (max (X.1 * Y.1) (X.1 * Y.2)) (max (X.2 * Y.1) (X.2 * Y.2)))

theorem iv_mul {X Y : IQ} {x y : ℝ} (hx : InI X x) (hy : InI Y y) : InI (DQ.mul X Y) (x * y) := by
  refine iv_rnd ?_
  have h := mul_bounds hx.1 hx.2 hy.1 hy.2
  unfold InI; push_cast
  exact h

/-- the reciprocal of an interval that does not contain `0`, rounded outwards -/
def inv (Y : IQ) : IQ := rnd (1 / Y.2, 1 / Y.1)

def invOk (Y : IQ) : Bool := decide (0 < Y.1) || decide (Y.2 < 0)

theorem iv_inv {Y : IQ} {y : ℝ} (hy : InI Y y) (hok : invOk Y = true) : InI (DQ.inv Y) y⁻¹ := by
  refine iv_rnd ?_
  obtain ⟨h1, h2⟩ := hy
  simp only [invOk, Bool.or_eq_true, decide_eq_true_eq] at hok
  unfold InI; push_cast
  rcases hok with hp | hn
  · have hp' : (0 : ℝ) < Y.1 := by exact_mod_cast hp
    have hy0 : 0 < y := hp'.trans_le h1
    constructor
    · rw [one_div]; exact inv_anti₀ hy0 h2
    · rw [one_div]; exact inv_anti₀ hp' h1
  · have hn' : ((Y.2 : ℚ) : ℝ) < 0 := by exact_mod_cast hn
    have hy0 : y < 0 := h2.trans_lt hn'
    constructor
    · rw [one_div, inv_le_inv_of_neg hn' hy0]; exact h2
    · rw [one_div, inv_le_inv_of_neg hy0 (h1.trans_lt hy0)]; exact h1

def div (X Y : IQ) : IQ := DQ.mul X (DQ.inv Y)

theorem iv_div {X Y : IQ} {x y : ℝ} (hx : InI X x) (hy : InI Y y) (hok : invOk Y = true) :
    InI (DQ.div X Y) (x / y) := by
  rw [div_eq_mul_inv]; exact iv_mul hx (iv_inv hy hok)

/-- a finite sum `Σ_{i<n} F i` -/
def isum (F : ℕ → IQ) : ℕ → IQ
  | 0 => (0, 0)
  | n + 1 => DQ.add (isum F n) (F n)

theorem iv_isum {F : ℕ → IQ} {f : ℕ → ℝ} (h : ∀ i, InI (F i) (f i)) :
    ∀ n, InI (DQ.isum F n) (∑ i ∈ Finset.range n, f i)
  | 0 => by simp [DQ.isum, InI]
  | n + 1 => by rw [Finset.sum_range_succ]; exact iv_add (iv_isum h n) (h n)

/-- a sign `(-1)^k` -/
def sgn (k : ℕ) (X : IQ) : IQ := if k % 2 = 0 then X else DQ.neg X

theorem iv_sgn {X : IQ} {x : ℝ} (hx : InI X x) (k : ℕ) : InI (DQ.sgn k X) ((-1) ^ k * x) := by
  unfold DQ.sgn
  rcases Nat.even_or_odd k with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow, one_mul]; exact hx
  · rw [if_neg (by have := Nat.odd_iff.mp ho; omega), ho.neg_one_pow, neg_one_mul]; exact iv_neg hx

/-! ## `sin`, `cos` on `[0, 1]` -/

def sin01 (X : IQ) : IQ := (rdn (tSinQ X.1 - errQ), rup (tSinQ X.2 + errQ))
def cos01 (X : IQ) : IQ := (rdn (tCosQ X.2 - errQ), rup (tCosQ X.1 + errQ))
def ok01 (X : IQ) : Bool := decide (0 ≤ X.1) && decide (X.2 ≤ 1)

theorem iv_sin01 {X : IQ} {x : ℝ} (hx : InI X x) (hok : ok01 X = true) : InI (DQ.sin01 X) (Real.sin x) := by
  simp only [ok01, Bool.and_eq_true, decide_eq_true_eq] at hok
  have h0 : (0 : ℝ) ≤ X.1 := by exact_mod_cast hok.1
  have h1 : ((X.2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hok.2
  exact ⟨(rdn_le _).trans (sin_ge_of h0 hx.1 (hx.2.trans h1)),
    (sin_le_of (h0.trans hx.1) hx.2 h1).trans (le_rup _)⟩

theorem iv_cos01 {X : IQ} {x : ℝ} (hx : InI X x) (hok : ok01 X = true) : InI (DQ.cos01 X) (Real.cos x) := by
  simp only [ok01, Bool.and_eq_true, decide_eq_true_eq] at hok
  have h0 : (0 : ℝ) ≤ X.1 := by exact_mod_cast hok.1
  have h1 : ((X.2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hok.2
  exact ⟨(rdn_le _).trans (cos_ge_of (h0.trans hx.1) hx.2 h1),
    (cos_le_of h0 hx.1 (hx.2.trans h1)).trans (le_rup _)⟩

/-! ## `π`, `√2`, `θ₀` -/

def piI : IQ := (314159265358979323846 / 10 ^ 20, 314159265358979323847 / 10 ^ 20)

theorem iv_piI : InI DQ.piI Real.pi := by
  unfold DQ.piI InI
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · push_cast; norm_num at h1 ⊢; linarith
  · push_cast; norm_num at h2 ⊢; linarith

def s2I : IQ := (14142135623730950488 / 10 ^ 19, 14142135623730950489 / 10 ^ 19)

theorem iv_s2I : InI DQ.s2I (Real.sqrt 2) := by
  unfold DQ.s2I InI
  constructor
  · push_cast
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · push_cast
    have hu : (0 : ℝ) ≤ 14142135623730950489 / 10 ^ 19 := by norm_num
    calc Real.sqrt 2 ≤ Real.sqrt ((14142135623730950489 / 10 ^ 19) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 14142135623730950489 / 10 ^ 19 := Real.sqrt_sq hu

/-- `θ₀ = √2/2` -/
def t0I : IQ := DQ.mul s2I (DQ.pt (1 / 2))

theorem iv_t0I : InI DQ.t0I (Real.sqrt 2 / 2) := by
  have h := iv_mul iv_s2I (iv_pt (1 / 2 : ℚ))
  have e : Real.sqrt 2 * (((1 / 2 : ℚ)) : ℝ) = Real.sqrt 2 / 2 := by push_cast; ring
  rw [e] at h; exact h

def sthI : IQ := DQ.sin01 t0I
def cthI : IQ := DQ.cos01 t0I

theorem ok01_t0I : ok01 t0I = true := by decide +kernel

theorem iv_sthI : InI sthI (Real.sin (Real.sqrt 2 / 2)) := iv_sin01 iv_t0I ok01_t0I
theorem iv_cthI : InI cthI (Real.cos (Real.sqrt 2 / 2)) := iv_cos01 iv_t0I ok01_t0I

/-! ## The frequencies and their halves -/

def ωI (k : ℕ) : IQ := if k = 0 then s2I else DQ.mul (DQ.pt (2 * k)) piI

theorem iv_ωI (k : ℕ) : InI (ωI k) (ωAM k) := by
  unfold ωI ωAM
  split_ifs with hk
  · exact iv_s2I
  · have h := iv_mul (iv_pt (2 * k : ℚ)) iv_piI
    have e : (((2 * k : ℚ)) : ℝ) * Real.pi = 2 * Real.pi * k := by push_cast; ring
    rw [e] at h; exact h

/-- `sin`, `cos` of `ω_j / 2` (`θ₀` for `j = 0`, `πj` otherwise) -/
def haS (j : ℕ) : IQ := if j = 0 then sthI else DQ.pt 0
def haC (j : ℕ) : IQ := if j = 0 then cthI else DQ.pt ((-1) ^ j)

theorem ωAM_half (j : ℕ) (hj : j ≠ 0) : ωAM j / 2 = (j : ℝ) * Real.pi := by
  unfold ωAM; rw [if_neg hj]; ring

theorem iv_haS (j : ℕ) : InI (haS j) (Real.sin (ωAM j / 2)) := by
  unfold haS
  split_ifs with hj
  · subst hj; rw [ωAM_zero]; exact iv_sthI
  · rw [ωAM_half j hj, Real.sin_nat_mul_pi]
    have := iv_pt (0 : ℚ); simpa using this

theorem iv_haC (j : ℕ) : InI (haC j) (Real.cos (ωAM j / 2)) := by
  unfold haC
  split_ifs with hj
  · subst hj; rw [ωAM_zero]; exact iv_cthI
  · rw [ωAM_half j hj, Real.cos_nat_mul_pi]
    have := iv_pt ((-1) ^ j : ℚ); push_cast at this; exact this

/-! ## The per-pair coefficients -/

def sinHmI (j k : ℕ) : IQ := DQ.sub (DQ.mul (haS j) (haC k)) (DQ.mul (haC j) (haS k))
def cosHmI (j k : ℕ) : IQ := DQ.add (DQ.mul (haC j) (haC k)) (DQ.mul (haS j) (haS k))
def sinHpI (j k : ℕ) : IQ := DQ.add (DQ.mul (haS j) (haC k)) (DQ.mul (haC j) (haS k))
def cosHpI (j k : ℕ) : IQ := DQ.sub (DQ.mul (haC j) (haC k)) (DQ.mul (haS j) (haS k))
def sinWI (k : ℕ) : IQ := DQ.mul (DQ.pt 2) (DQ.mul (haS k) (haC k))
def cosWI (k : ℕ) : IQ := DQ.sub (DQ.mul (haC k) (haC k)) (DQ.mul (haS k) (haS k))

theorem hmq_eq (j k : ℕ) : hmq j k = ωAM j / 2 - ωAM k / 2 := by unfold hmq; ring
theorem hpq_eq (j k : ℕ) : hpq j k = ωAM j / 2 + ωAM k / 2 := by unfold hpq; ring

theorem iv_sinHm (j k : ℕ) : InI (sinHmI j k) (Real.sin (hmq j k)) := by
  rw [hmq_eq, Real.sin_sub]
  exact iv_sub (iv_mul (iv_haS j) (iv_haC k)) (iv_mul (iv_haC j) (iv_haS k))
theorem iv_cosHm (j k : ℕ) : InI (cosHmI j k) (Real.cos (hmq j k)) := by
  rw [hmq_eq, Real.cos_sub]
  exact iv_add (iv_mul (iv_haC j) (iv_haC k)) (iv_mul (iv_haS j) (iv_haS k))
theorem iv_sinHp (j k : ℕ) : InI (sinHpI j k) (Real.sin (hpq j k)) := by
  rw [hpq_eq, Real.sin_add]
  exact iv_add (iv_mul (iv_haS j) (iv_haC k)) (iv_mul (iv_haC j) (iv_haS k))
theorem iv_cosHp (j k : ℕ) : InI (cosHpI j k) (Real.cos (hpq j k)) := by
  rw [hpq_eq, Real.cos_add]
  exact iv_sub (iv_mul (iv_haC j) (iv_haC k)) (iv_mul (iv_haS j) (iv_haS k))
theorem iv_sinW (k : ℕ) : InI (sinWI k) (Real.sin (ωAM k)) := by
  have e : ωAM k = 2 * (ωAM k / 2) := by ring
  rw [e, Real.sin_two_mul]
  have h := iv_mul (iv_pt (2 : ℚ)) (iv_mul (iv_haS k) (iv_haC k))
  push_cast at h; rw [mul_assoc]; exact h
theorem iv_cosW (k : ℕ) : InI (cosWI k) (Real.cos (ωAM k)) := by
  have e : ωAM k = 2 * (ωAM k / 2) := by ring
  rw [e, Real.cos_two_mul, Real.cos_sq']
  have h := iv_sub (iv_mul (iv_haC k) (iv_haC k)) (iv_mul (iv_haS k) (iv_haS k))
  have e2 : Real.cos (ωAM k / 2) * Real.cos (ωAM k / 2) - Real.sin (ωAM k / 2) * Real.sin (ωAM k / 2)
      = 2 * (1 - Real.sin (ωAM k / 2) ^ 2) - 1 := by nlinarith [Real.sin_sq_add_cos_sq (ωAM k / 2)]
  rw [e2] at h; exact h

/-- the denominators `2(ω_j − ω_k)`, `2(ω_j + ω_k)`, `2ω_k` -/
def dmI (j k : ℕ) : IQ := DQ.mul (DQ.pt 2) (DQ.sub (ωI j) (ωI k))
def dpI (j k : ℕ) : IQ := DQ.mul (DQ.pt 2) (DQ.add (ωI j) (ωI k))
def dwI (k : ℕ) : IQ := DQ.mul (DQ.pt 2) (ωI k)

theorem iv_dm (j k : ℕ) : InI (dmI j k) (2 * (ωAM j - ωAM k)) := by
  have h := iv_mul (iv_pt (2 : ℚ)) (iv_sub (iv_ωI j) (iv_ωI k)); push_cast at h; exact h
theorem iv_dp (j k : ℕ) : InI (dpI j k) (2 * (ωAM j + ωAM k)) := by
  have h := iv_mul (iv_pt (2 : ℚ)) (iv_add (iv_ωI j) (iv_ωI k)); push_cast at h; exact h
theorem iv_dw (k : ℕ) : InI (dwI k) (2 * ωAM k) := by
  have h := iv_mul (iv_pt (2 : ℚ)) (iv_ωI k); push_cast at h; exact h

/-- every denominator used is bounded away from `0` (checked once) -/
def denOk : Bool :=
  (List.range 13).all fun j => (List.range 13).all fun k =>
    (decide (j = k) || invOk (dmI j k)) && invOk (dpI j k) && invOk (dwI k)

theorem denOk_true : denOk = true := by decide +kernel

theorem den_ok {j k : ℕ} (hj : j < 13) (hk : k < 13) :
    (j = k ∨ invOk (dmI j k) = true) ∧ invOk (dpI j k) = true ∧ invOk (dwI k) = true := by
  have h := denOk_true
  simp only [denOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j hj k hk
  exact ⟨h1, h2, h3⟩

def axqI (j k : ℕ) : IQ :=
  if j = k then DQ.add (DQ.pt (1 / 2)) (DQ.div (sinWI k) (dwI k))
  else DQ.add (DQ.div (sinHmI j k) (dmI j k)) (DQ.div (sinHpI j k) (dpI j k))
def bxqI (j k : ℕ) : IQ :=
  if j = k then DQ.neg (DQ.div (cosWI k) (dwI k))
  else DQ.sub (DQ.neg (DQ.div (cosHmI j k) (dmI j k))) (DQ.div (cosHpI j k) (dpI j k))
def cxqI (j k : ℕ) : IQ := if j = k then DQ.pt (-(1 / 2)) else DQ.pt 0
def ayqI (j k : ℕ) : IQ :=
  if j = k then DQ.pt 0
  else DQ.add (DQ.div (sinHmI j k) (dmI j k)) (DQ.div (sinHpI j k) (dpI j k))
def byqI (j k : ℕ) : IQ :=
  if j = k then DQ.pt 0
  else DQ.sub (DQ.div (cosHmI j k) (dmI j k)) (DQ.div (cosHpI j k) (dpI j k))

theorem iv_axq {j k : ℕ} (hj : j < 13) (hk : k < 13) : InI (axqI j k) (axq j k) := by
  obtain ⟨h1, h2, h3⟩ := den_ok hj hk
  unfold axqI axq
  split_ifs with hjk
  · have h := iv_add (iv_pt (1 / 2 : ℚ)) (iv_div (iv_sinW k) (iv_dw k) h3); push_cast at h; exact h
  · exact iv_add (iv_div (iv_sinHm j k) (iv_dm j k) (h1.resolve_left hjk)) (iv_div (iv_sinHp j k) (iv_dp j k) h2)

theorem iv_bxq {j k : ℕ} (hj : j < 13) (hk : k < 13) : InI (bxqI j k) (bxq j k) := by
  obtain ⟨h1, h2, h3⟩ := den_ok hj hk
  unfold bxqI bxq
  split_ifs with hjk
  · exact iv_neg (iv_div (iv_cosW k) (iv_dw k) h3)
  · exact iv_sub (iv_neg (iv_div (iv_cosHm j k) (iv_dm j k) (h1.resolve_left hjk))) (iv_div (iv_cosHp j k) (iv_dp j k) h2)

theorem iv_cxq (j k : ℕ) : InI (cxqI j k) (cxq j k) := by
  unfold cxqI cxq
  split_ifs
  · have h := iv_pt (-(1 / 2) : ℚ); push_cast at h; exact h
  · have h := iv_pt (0 : ℚ); push_cast at h; exact h

theorem iv_ayq {j k : ℕ} (hj : j < 13) (hk : k < 13) : InI (ayqI j k) (ayq j k) := by
  obtain ⟨h1, h2, _⟩ := den_ok hj hk
  unfold ayqI ayq
  split_ifs with hjk
  · have h := iv_pt (0 : ℚ); push_cast at h; exact h
  · exact iv_add (iv_div (iv_sinHm j k) (iv_dm j k) (h1.resolve_left hjk)) (iv_div (iv_sinHp j k) (iv_dp j k) h2)

theorem iv_byq {j k : ℕ} (hj : j < 13) (hk : k < 13) : InI (byqI j k) (byq j k) := by
  obtain ⟨h1, h2, _⟩ := den_ok hj hk
  unfold byqI byq
  split_ifs with hjk
  · have h := iv_pt (0 : ℚ); push_cast at h; exact h
  · exact iv_sub (iv_div (iv_cosHm j k) (iv_dm j k) (h1.resolve_left hjk)) (iv_div (iv_cosHp j k) (iv_dp j k) h2)

/-! ## The collected coefficients and the coefficients of `qf` -/

theorem iv_isumB {F : ℕ → IQ} {f : ℕ → ℝ} :
    ∀ n, (∀ i < n, InI (F i) (f i)) → InI (DQ.isum F n) (∑ i ∈ Finset.range n, f i)
  | 0, _ => by simp [DQ.isum, InI]
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    exact iv_add (iv_isumB n fun i hi => h i (by omega)) (h n (by omega))

def AqI (i : ℕ) : IQ :=
  DQ.add (DQ.isum (fun k => DQ.mul (DQ.pt (cAM i * cAM k)) (axqI i k)) 13)
    (DQ.isum (fun j => DQ.mul (DQ.pt (cAM j * cAM i)) (ayqI j i)) 13)
def BqI (i : ℕ) : IQ :=
  DQ.add (DQ.isum (fun k => DQ.mul (DQ.pt (cAM i * cAM k)) (bxqI i k)) 13)
    (DQ.isum (fun j => DQ.mul (DQ.pt (cAM j * cAM i)) (byqI j i)) 13)
def CqI (i : ℕ) : IQ := DQ.isum (fun k => DQ.mul (DQ.pt (cAM i * cAM k)) (cxqI i k)) 13

theorem iv_AqI {i : ℕ} (hi : i < 13) : InI (AqI i) (Aq i) := by
  unfold AqI Aq
  refine iv_add (iv_isumB 13 fun k hk => ?_) (iv_isumB 13 fun j hj => ?_)
  · have h := iv_mul (iv_pt (cAM i * cAM k)) (iv_axq hi hk); push_cast at h; exact h
  · have h := iv_mul (iv_pt (cAM j * cAM i)) (iv_ayq hj hi); push_cast at h; exact h

theorem iv_BqI {i : ℕ} (hi : i < 13) : InI (BqI i) (Bq i) := by
  unfold BqI Bq
  refine iv_add (iv_isumB 13 fun k hk => ?_) (iv_isumB 13 fun j hj => ?_)
  · have h := iv_mul (iv_pt (cAM i * cAM k)) (iv_bxq hi hk); push_cast at h; exact h
  · have h := iv_mul (iv_pt (cAM j * cAM i)) (iv_byq hj hi); push_cast at h; exact h

theorem iv_CqI (i : ℕ) : InI (CqI i) (Cq i) := by
  unfold CqI Cq
  refine iv_isumB 13 fun k _ => ?_
  have h := iv_mul (iv_pt (cAM i * cAM k)) (iv_cxq i k); push_cast at h; exact h

def ZI : IQ := DQ.mul (DQ.pt 2) (DQ.mul sthI sthI)

theorem iv_ZI : InI ZI ZQ := by
  have h := iv_mul (iv_pt (2 : ℚ)) (iv_mul iv_sthI iv_sthI)
  unfold ZQ; push_cast at h; rw [sq]; exact h

theorem ZI_ok : invOk ZI = true := by decide +kernel

def qA0I (i : ℕ) : IQ := DQ.div (AqI i) ZI
def qB0I (i : ℕ) : IQ := DQ.div (BqI i) ZI
def qC0I (i : ℕ) : IQ := DQ.div (CqI i) ZI

/-! ## Tables (computed once) -/

def qA0L : List IQ :=
  [(1007026102399118 / 10 ^ 15, 1007026121811456 / 10 ^ 15),
    (804849336778 / 10 ^ 15, 804849370110 / 10 ^ 15),
    (344044668158 / 10 ^ 15, 344044685946 / 10 ^ 15),
    (32692272850 / 10 ^ 15, 32692275523 / 10 ^ 15),
    (2512562645 / 10 ^ 15, 2512565462 / 10 ^ 15),
    (-1609888841 / 10 ^ 15, -1609888475 / 10 ^ 15),
    (9885900981 / 10 ^ 15, 9885902710 / 10 ^ 15),
    (20054543435 / 10 ^ 15, 20054545389 / 10 ^ 15),
    (5209398203 / 10 ^ 15, 5209399088 / 10 ^ 15),
    (15184042874 / 10 ^ 15, 15184044165 / 10 ^ 15),
    (4817160294 / 10 ^ 15, 4817160936 / 10 ^ 15),
    (-85163445 / 10 ^ 15, -85163371 / 10 ^ 15),
    (111970671 / 10 ^ 15, 111970708 / 10 ^ 15)]
def qB0L : List IQ :=
  [(-66372762253037 / 10 ^ 15, -66372755939884 / 10 ^ 15),
    (3724746908055 / 10 ^ 15, 3724746982075 / 10 ^ 15),
    (2123111825274 / 10 ^ 15, 2123111867865 / 10 ^ 15),
    (344549731272 / 10 ^ 15, 344549738312 / 10 ^ 15),
    (-434041575835 / 10 ^ 15, -434041566983 / 10 ^ 15),
    (-53688753528 / 10 ^ 15, -53688752411 / 10 ^ 15),
    (-249905800522 / 10 ^ 15, -249905795421 / 10 ^ 15),
    (-271952412928 / 10 ^ 15, -271952407440 / 10 ^ 15),
    (-134283895640 / 10 ^ 15, -134283892934 / 10 ^ 15),
    (-182827980123 / 10 ^ 15, -182827976470 / 10 ^ 15),
    (-101095763951 / 10 ^ 15, -101095761941 / 10 ^ 15),
    (-12392999630 / 10 ^ 15, -12392999358 / 10 ^ 15),
    (5412963696 / 10 ^ 15, 5412963835 / 10 ^ 15)]
def qC0L : List IQ :=
  [(-592377546833376 / 10 ^ 15, -592377538584148 / 10 ^ 15),
    (-89778221853 / 10 ^ 15, -89778220600 / 10 ^ 15),
    (-134026703835 / 10 ^ 15, -134026701966 / 10 ^ 15),
    (-8861271950 / 10 ^ 15, -8861271824 / 10 ^ 15),
    (-24950432524 / 10 ^ 15, -24950432174 / 10 ^ 15),
    (-583321798 / 10 ^ 15, -583321788 / 10 ^ 15),
    (-18445145516 / 10 ^ 15, -18445145257 / 10 ^ 15),
    (-27767211076 / 10 ^ 15, -27767210687 / 10 ^ 15),
    (-8469936790 / 10 ^ 15, -8469936670 / 10 ^ 15),
    (-19046657890 / 10 ^ 15, -19046657622 / 10 ^ 15),
    (-6668170244 / 10 ^ 15, -6668170149 / 10 ^ 15),
    (-120235448 / 10 ^ 15, -120235444 / 10 ^ 15),
    (-28277037 / 10 ^ 15, -28277035 / 10 ^ 15)]
def qA1L : List IQ :=
  [(-686242807383786 / 10 ^ 15, -686242790206411 / 10 ^ 15),
    (23313496823800 / 10 ^ 15, 23313497290136 / 10 ^ 15),
    (26545783348286 / 10 ^ 15, 26545783885370 / 10 ^ 15),
    (6485748155412 / 10 ^ 15, 6485748288240 / 10 ^ 15),
    (-10933605040491 / 10 ^ 15, -10933604817665 / 10 ^ 15),
    (-1687265258438 / 10 ^ 15, -1687265223335 / 10 ^ 15),
    (-9439671869629 / 10 ^ 15, -9439671677066 / 10 ^ 15),
    (-11988859047205 / 10 ^ 15, -11988858805440 / 10 ^ 15),
    (-6758314737399 / 10 ^ 15, -6758314601260 / 10 ^ 15),
    (-10357725363942 / 10 ^ 15, -10357725157101 / 10 ^ 15),
    (-6358702356995 / 10 ^ 15, -6358702230607 / 10 ^ 15),
    (-856662880507 / 10 ^ 15, -856662861702 / 10 ^ 15),
    (408099570519 / 10 ^ 15, 408099581002 / 10 ^ 15)]
def qB1L : List IQ :=
  [(-1424149999129742 / 10 ^ 15, -1424149971676549 / 10 ^ 15),
    (-5057017736768 / 10 ^ 15, -5057017527336 / 10 ^ 15),
    (-4323393031499 / 10 ^ 15, -4323392807967 / 10 ^ 15),
    (-616234875674 / 10 ^ 15, -616234825288 / 10 ^ 15),
    (-63147657577 / 10 ^ 15, -63147586777 / 10 ^ 15),
    (50576138061 / 10 ^ 15, 50576149560 / 10 ^ 15),
    (-372689751935 / 10 ^ 15, -372689686752 / 10 ^ 15),
    (-882044974513 / 10 ^ 15, -882044888570 / 10 ^ 15),
    (-261852958472 / 10 ^ 15, -261852913986 / 10 ^ 15),
    (-858637468810 / 10 ^ 15, -858637395805 / 10 ^ 15),
    (-302671148154 / 10 ^ 15, -302671107815 / 10 ^ 15),
    (5886069655 / 10 ^ 15, 5886074770 / 10 ^ 15),
    (-8442392489 / 10 ^ 15, -8442389698 / 10 ^ 15)]
def qC1L : List IQ :=
  [(0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15),
    (0 / 10 ^ 15, 0 / 10 ^ 15)]
def qD1L : List IQ :=
  [(837748349110893 / 10 ^ 15, 837748360777064 / 10 ^ 15),
    (564093196578 / 10 ^ 15, 564093204452 / 10 ^ 15),
    (1684229209125 / 10 ^ 15, 1684229232612 / 10 ^ 15),
    (167031038782 / 10 ^ 15, 167031041158 / 10 ^ 15),
    (627072755373 / 10 ^ 15, 627072764171 / 10 ^ 15),
    (18325594438 / 10 ^ 15, 18325594753 / 10 ^ 15),
    (695365594005 / 10 ^ 15, 695365603770 / 10 ^ 15),
    (1221265711469 / 10 ^ 15, 1221265728579 / 10 ^ 15),
    (425745453101 / 10 ^ 15, 425745459134 / 10 ^ 15),
    (1077063113892 / 10 ^ 15, 1077063129048 / 10 ^ 15),
    (418973487059 / 10 ^ 15, 418973493029 / 10 ^ 15),
    (8310077326 / 10 ^ 15, 8310077604 / 10 ^ 15),
    (2132038210 / 10 ^ 15, 2132038361 / 10 ^ 15)]

def qA0T (i : ℕ) : IQ := qA0L.getD i (0, 0)
def qB0T (i : ℕ) : IQ := qB0L.getD i (0, 0)
def qC0T (i : ℕ) : IQ := qC0L.getD i (0, 0)
def qD0T (_ : ℕ) : IQ := DQ.pt 0

/-- `X ⊆ Y` -/
def subI (X Y : IQ) : Bool := decide (Y.1 ≤ X.1) && decide (X.2 ≤ Y.2)

theorem iv_widen {X Y : IQ} {x : ℝ} (h : subI X Y = true) (hx : InI X x) : InI Y x := by
  simp only [subI, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : ((Y.1 : ℚ) : ℝ) ≤ X.1 := by exact_mod_cast h.1
  have h2 : ((X.2 : ℚ) : ℝ) ≤ Y.2 := by exact_mod_cast h.2
  exact ⟨h1.trans hx.1, hx.2.trans h2⟩

def tabOk : Bool :=
  (List.range 13).all fun i => subI (qA0I i) (qA0T i) && subI (qB0I i) (qB0T i) && subI (qC0I i) (qC0T i)

theorem tabOk_true : tabOk = true := by decide +kernel

theorem tab_ok {i : ℕ} (hi : i < 13) :
    subI (qA0I i) (qA0T i) = true ∧ subI (qB0I i) (qB0T i) = true ∧ subI (qC0I i) (qC0T i) = true := by
  have h := tabOk_true
  simp only [tabOk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h i hi
  exact ⟨h1, h2, h3⟩

theorem iv_qA0T {i : ℕ} (hi : i < 13) : InI (qA0T i) (qA0 i) :=
  iv_widen (tab_ok hi).1 (iv_div (iv_AqI hi) iv_ZI ZI_ok)
theorem iv_qB0T {i : ℕ} (hi : i < 13) : InI (qB0T i) (qB0 i) :=
  iv_widen (tab_ok hi).2.1 (iv_div (iv_BqI hi) iv_ZI ZI_ok)
theorem iv_qC0T {i : ℕ} (hi : i < 13) : InI (qC0T i) (qC0 i) :=
  iv_widen (tab_ok hi).2.2 (iv_div (iv_CqI i) iv_ZI ZI_ok)
theorem iv_qD0T (i : ℕ) : InI (qD0T i) (qD0 i) := by
  have h := iv_pt (0 : ℚ); push_cast at h; exact h

/-! ## The derivative map on enclosures -/

def dAI (_A B C _D : ℕ → IQ) (i : ℕ) : IQ := DQ.add (DQ.mul (B i) (ωI i)) (C i)
def dBI (A _B _C D : ℕ → IQ) (i : ℕ) : IQ := DQ.add (DQ.neg (DQ.mul (A i) (ωI i))) (D i)
def dCI (_A _B _C D : ℕ → IQ) (i : ℕ) : IQ := DQ.mul (D i) (ωI i)
def dDI (_A _B C _D : ℕ → IQ) (i : ℕ) : IQ := DQ.neg (DQ.mul (C i) (ωI i))

/-- four coefficient enclosures, sound below `13` -/
def Sound4 (A B C D : ℕ → IQ) (a b c d : ℕ → ℝ) : Prop :=
  ∀ i < 13, InI (A i) (a i) ∧ InI (B i) (b i) ∧ InI (C i) (c i) ∧ InI (D i) (d i)

theorem Sound4.d {A B C D : ℕ → IQ} {a b c d : ℕ → ℝ} (h : Sound4 A B C D a b c d) :
    Sound4 (dAI A B C D) (dBI A B C D) (dCI A B C D) (dDI A B C D) (AMW.dA a b c d) (AMW.dB a b c d)
      (AMW.dC a b c d) (AMW.dD a b c d) := by
  intro i hi
  obtain ⟨ha, hb, hc, hd⟩ := h i hi
  exact ⟨iv_add (iv_mul hb (iv_ωI i)) hc, iv_add (iv_neg (iv_mul ha (iv_ωI i))) hd,
    iv_mul hd (iv_ωI i), iv_neg (iv_mul hc (iv_ωI i))⟩

theorem sound_q0 : Sound4 qA0T qB0T qC0T qD0T qA0 qB0 qC0 qD0 :=
  fun _ hi => ⟨iv_qA0T hi, iv_qB0T hi, iv_qC0T hi, iv_qD0T _⟩

def qA1D := dAI qA0T qB0T qC0T qD0T
def qB1D := dBI qA0T qB0T qC0T qD0T
def qC1D := dCI qA0T qB0T qC0T qD0T
def qD1D := dDI qA0T qB0T qC0T qD0T

theorem sound_q1D : Sound4 qA1D qB1D qC1D qD1D qA1 qB1 qC1 qD1 := sound_q0.d

def qA1T (i : ℕ) : IQ := qA1L.getD i (0, 0)
def qB1T (i : ℕ) : IQ := qB1L.getD i (0, 0)
def qC1T (i : ℕ) : IQ := qC1L.getD i (0, 0)
def qD1T (i : ℕ) : IQ := qD1L.getD i (0, 0)

def tab1Ok : Bool :=
  (List.range 13).all fun i => subI (qA1D i) (qA1T i) && subI (qB1D i) (qB1T i) && subI (qC1D i) (qC1T i)
    && subI (qD1D i) (qD1T i)

theorem tab1Ok_true : tab1Ok = true := by decide +kernel

theorem sound_q1 : Sound4 qA1T qB1T qC1T qD1T qA1 qB1 qC1 qD1 := by
  intro i hi
  have h := tab1Ok_true
  simp only [tab1Ok, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h i hi
  obtain ⟨a, b, c, d⟩ := sound_q1D i hi
  exact ⟨iv_widen h1 a, iv_widen h2 b, iv_widen h3 c, iv_widen h4 d⟩

def qA2T := dAI qA1T qB1T qC1T qD1T
def qB2T := dBI qA1T qB1T qC1T qD1T
def qC2T := dCI qA1T qB1T qC1T qD1T
def qD2T := dDI qA1T qB1T qC1T qD1T

theorem sound_q2 : Sound4 qA2T qB2T qC2T qD2T qA2 qB2 qC2 qD2 := sound_q1.d

end AMW.DQ
