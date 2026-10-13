import PyrBase

/-! ###### convex-basin layer ###### -/

section

/-!
# Derivatives of `wfun` and a second-order lower bound

Away from the poles of the closed form (`1 − 2(πx)² ≠ 0`), `kfun x = N(πx) / D(πx)` with
`N θ = cos θ − 2γ θ sin θ` and `D θ = 1 − 2θ²`. This file differentiates that twice and proves
`w s ≥ w t + w'(t)(s − t) + l(s − t)²/2` on intervals where `w'' ≥ l`.
-/

noncomputable section

namespace Riemann.Deriv

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint

def Nf (θ : ℝ) : ℝ := Real.cos θ - 2 * gam * θ * Real.sin θ
def N1f (θ : ℝ) : ℝ := -(1 + 2 * gam) * Real.sin θ - 2 * gam * θ * Real.cos θ
def N2f (θ : ℝ) : ℝ := -(1 + 4 * gam) * Real.cos θ + 2 * gam * θ * Real.sin θ
def Df (θ : ℝ) : ℝ := 1 - 2 * θ ^ 2

/-- `d/dθ (N/D)` and `d²/dθ² (N/D)`. -/
def K1f (θ : ℝ) : ℝ := N1f θ / Df θ + 4 * θ * Nf θ / Df θ ^ 2
def K2f (θ : ℝ) : ℝ :=
  N2f θ / Df θ + 8 * θ * N1f θ / Df θ ^ 2 + 4 * Nf θ / Df θ ^ 2 + 32 * θ ^ 2 * Nf θ / Df θ ^ 3

lemma hasDerivAt_Nf (θ : ℝ) : HasDerivAt Nf (N1f θ) θ := by
  unfold Nf
  refine ((Real.hasDerivAt_cos θ).sub
    (((hasDerivAt_id' θ).const_mul (2 * gam)).mul (Real.hasDerivAt_sin θ))).congr_deriv ?_
  simp only [N1f]; ring

lemma hasDerivAt_N1f (θ : ℝ) : HasDerivAt N1f (N2f θ) θ := by
  unfold N1f
  refine (((Real.hasDerivAt_sin θ).const_mul (-(1 + 2 * gam))).sub
    (((hasDerivAt_id' θ).const_mul (2 * gam)).mul (Real.hasDerivAt_cos θ))).congr_deriv ?_
  simp only [N2f]; ring

lemma hasDerivAt_Df (θ : ℝ) : HasDerivAt Df (-4 * θ) θ := by
  unfold Df
  refine (((hasDerivAt_pow 2 θ).const_mul 2).const_sub 1).congr_deriv ?_
  simp; ring

lemma hasDerivAt_Kf {θ : ℝ} (hD : Df θ ≠ 0) : HasDerivAt (fun t => Nf t / Df t) (K1f θ) θ := by
  refine ((hasDerivAt_Nf θ).div (hasDerivAt_Df θ) hD).congr_deriv ?_
  unfold K1f
  field_simp
  ring

lemma hasDerivAt_K1f {θ : ℝ} (hD : Df θ ≠ 0) : HasDerivAt K1f (K2f θ) θ := by
  have hD2 : Df θ ^ 2 ≠ 0 := pow_ne_zero 2 hD
  unfold K1f
  refine (((hasDerivAt_N1f θ).div (hasDerivAt_Df θ) hD).add
    ((((hasDerivAt_id' θ).const_mul 4).mul (hasDerivAt_Nf θ)).div
      ((hasDerivAt_Df θ).pow 2) hD2)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  unfold K2f
  field_simp
  ring

/-- The closed form agrees with `kfun` near every non-pole. -/
lemma kfun_eventually {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) :
    (fun y => Nf (Real.pi * y) / Df (Real.pi * y)) =ᶠ[nhds x] kfun := by
  have hc : Continuous fun y => Df (Real.pi * y) := by unfold Df; fun_prop
  filter_upwards [hc.continuousAt.eventually_ne hD] with y hy
  rw [kfun_closed y (by simpa [Df] using hy)]
  simp [Nf, Df]

def k1 (x : ℝ) : ℝ := Real.pi * K1f (Real.pi * x)
def k2 (x : ℝ) : ℝ := Real.pi ^ 2 * K2f (Real.pi * x)

lemma hasDerivAt_kfun {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt kfun (k1 x) x := by
  have h := (hasDerivAt_Kf hD).comp x ((hasDerivAt_id' x).const_mul Real.pi)
  have h' : HasDerivAt (fun y => Nf (Real.pi * y) / Df (Real.pi * y)) (k1 x) x :=
    h.congr_deriv (by unfold k1; ring)
  exact h'.congr_of_eventuallyEq (kfun_eventually hD).symm

lemma hasDerivAt_k1 {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt k1 (k2 x) x := by
  have h := ((hasDerivAt_K1f hD).comp x ((hasDerivAt_id' x).const_mul Real.pi)).const_mul Real.pi
  unfold k1
  exact h.congr_deriv (by unfold k2; ring)

def w1 (x : ℝ) : ℝ := 2 * kfun x * k1 x
def w2 (x : ℝ) : ℝ := 2 * (k1 x * k1 x + kfun x * k2 x)

lemma hasDerivAt_wfun {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt wfun (w1 x) x := by
  unfold wfun
  exact ((hasDerivAt_kfun hD).pow 2).congr_deriv (by unfold w1; simp)

lemma hasDerivAt_w1 {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt w1 (w2 x) x := by
  unfold w1
  exact (((hasDerivAt_kfun hD).const_mul 2).mul (hasDerivAt_k1 hD)).congr_deriv (by unfold w2; ring)

/-- No poles from `1/2` on: `2(πx)² ≥ π²/2 > 1`. -/
lemma Df_ne {x : ℝ} (hx : 1 / 2 ≤ x) : Df (Real.pi * x) ≠ 0 := by
  have hpi := Real.pi_gt_three
  have : (3 / 2 : ℝ) ≤ Real.pi * x := by nlinarith
  unfold Df; nlinarith

/-- Second-order lower bound from a lower bound on the second derivative. -/
theorem taylor2_lower {f f1 f2 : ℝ → ℝ} {a b l : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Set.Icc a b, HasDerivAt f1 (f2 x) x)
    (hl : ∀ x ∈ Set.Icc a b, l ≤ f2 x) {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    f t + f1 t * (s - t) + l / 2 * (s - t) ^ 2 ≤ f s := by
  set g : ℝ → ℝ := fun u => f u - f t - f1 t * (u - t) - l / 2 * (u - t) ^ 2 with hg
  set g1 : ℝ → ℝ := fun u => f1 u - f1 t - l * (u - t) with hg1
  have hgd : ∀ u ∈ Set.Icc a b, HasDerivAt g (g1 u) u := by
    intro u hu
    exact ((((hf u hu).sub_const (f t)).sub
      (((hasDerivAt_id' u).sub_const t).const_mul (f1 t))).sub
      ((((hasDerivAt_id' u).sub_const t).pow 2).const_mul (l / 2))).congr_deriv (by simp [hg1]; ring)
  have hg1d : ∀ u ∈ Set.Icc a b, HasDerivAt g1 (f2 u - l) u := by
    intro u hu
    exact (((hf1 u hu).sub_const (f1 t)).sub
      (((hasDerivAt_id' u).sub_const t).const_mul l)).congr_deriv (by simp)
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hint : interior (Set.Icc a b) ⊆ Set.Icc a b := interior_subset
  -- `g1` is monotone, vanishing at `t`
  have hmono1 : MonotoneOn g1 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg hconv
      (fun u hu => (hg1d u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hg1d u (hint hu)).differentiableAt.differentiableWithinAt)
      (fun u hu => by rw [(hg1d u (hint hu)).deriv]; linarith [hl u (hint hu)])
  have hg1t : g1 t = 0 := by simp [hg1]
  have hgt : g t = 0 := by simp [hg]
  -- `g` decreases up to `t` and increases after it
  rcases le_total t s with hts | hst
  · have hD : Convex ℝ (Set.Icc t b) := convex_Icc t b
    have hsub : Set.Icc t b ⊆ Set.Icc a b := Set.Icc_subset_Icc ht.1 le_rfl
    have hint2 : interior (Set.Icc t b) ⊆ Set.Icc t b := interior_subset
    have hm : MonotoneOn g (Set.Icc t b) :=
      monotoneOn_of_deriv_nonneg hD
        (fun u hu => (hgd u (hsub hu)).continuousAt.continuousWithinAt)
        (fun u hu => (hgd u (hsub (hint2 hu))).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          rw [(hgd u (hsub (hint2 hu))).deriv, ← hg1t]
          exact hmono1 ht (hsub (hint2 hu)) (hint2 hu).1)
    have := hm ⟨le_rfl, ht.2⟩ ⟨hts, hs.2⟩ hts
    rw [hgt] at this
    simp only [hg] at this
    linarith
  · have hD : Convex ℝ (Set.Icc a t) := convex_Icc a t
    have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
    have hint2 : interior (Set.Icc a t) ⊆ Set.Icc a t := interior_subset
    have hm : AntitoneOn g (Set.Icc a t) :=
      antitoneOn_of_deriv_nonpos hD
        (fun u hu => (hgd u (hsub hu)).continuousAt.continuousWithinAt)
        (fun u hu => (hgd u (hsub (hint2 hu))).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          rw [(hgd u (hsub (hint2 hu))).deriv, ← hg1t]
          exact hmono1 (hsub (hint2 hu)) ht (hint2 hu).2)
    have := hm ⟨hs.1, hst⟩ ⟨ht.1, le_rfl⟩ hst
    rw [hgt] at this
    simp only [hg] at this
    linarith

/-- The bound for `wfun` on `[a, b] ⊆ [1/2, ∞)`. -/
theorem wfun_taylor2 {a b l : ℝ} (ha : 1 / 2 ≤ a) (hl : ∀ x ∈ Set.Icc a b, l ≤ w2 x)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    wfun t + w1 t * (s - t) + l / 2 * (s - t) ^ 2 ≤ wfun s :=
  taylor2_lower (fun x hx => hasDerivAt_wfun (Df_ne (ha.trans hx.1)))
    (fun x hx => hasDerivAt_w1 (Df_ne (ha.trans hx.1))) hl hs ht

end Riemann.Deriv

end

section

/-!
# Enclosures of `w`, `w'` and `w''` on a cell

Rational interval arithmetic, rounded outward to `10⁻¹²` after products, over the record's
cos/sin enclosures of a `Cell` (anchor `k/2`, side, Taylor bounds). `Encl.sound` gives
`kfun x ∈ K`, `w1 x ∈ W1` and `w2 x ∈ W2` for every `x` in a cell passing `okD`.
-/

noncomputable section

namespace Riemann.Encl

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint Riemann.Deriv

abbrev IQ := ℚ × ℚ

def Mem (I : IQ) (x : ℝ) : Prop := (I.1 : ℝ) ≤ x ∧ x ≤ I.2

def cst (q : ℚ) : IQ := (q, q)
def ineg (I : IQ) : IQ := (-I.2, -I.1)
def iscale (q : ℚ) (I : IQ) : IQ := if 0 ≤ q then (q * I.1, q * I.2) else (q * I.2, q * I.1)
def imul (I J : IQ) : IQ :=
  (floorD (min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2))),
    ceilD (max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2))))
/-- Reciprocal of an interval of negative numbers. -/
def iinvN (J : IQ) : IQ := (floorD (1 / J.2), ceilD (1 / J.1))

lemma mem_congr {I : IQ} {x y : ℝ} (h : Mem I x) (e : x = y) : Mem I y := e ▸ h

lemma mem_cst (q : ℚ) : Mem (cst q) q := ⟨le_rfl, le_rfl⟩

lemma mem_ineg {I : IQ} {x : ℝ} (h : Mem I x) : Mem (ineg I) (-x) := by
  unfold ineg Mem; push_cast; exact ⟨by linarith [h.2], by linarith [h.1]⟩

lemma mem_iadd {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (iadd I J) (x + y) :=
  iadd_sound I J hx hy

lemma mem_isub {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (isub I J) (x - y) :=
  isub_sound I J hx hy

lemma mem_iscale (q : ℚ) {I : IQ} {x : ℝ} (h : Mem I x) : Mem (iscale q I) (q * x) := by
  unfold iscale Mem
  split_ifs with hq
  · have : (0 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h.1 this, mul_le_mul_of_nonneg_left h.2 this⟩
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hq).le
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h.2 this, mul_le_mul_of_nonpos_left h.1 this⟩

lemma mul_between {x a b y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy),
      (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy),
      (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)⟩

lemma mul_between' {y c d a : ℝ} (h1 : c ≤ y) (h2 : y ≤ d) :
    min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) := by
  obtain ⟨h3, h4⟩ := mul_between (y := a) h1 h2
  rw [mul_comm c, mul_comm d, mul_comm y] at *
  exact ⟨h3, h4⟩

lemma mem_imul {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (imul I J) (x * y) := by
  obtain ⟨hx1, hx2⟩ := mul_between (y := y) hx.1 hx.2
  obtain ⟨ha1, ha2⟩ := mul_between' (a := (I.1 : ℝ)) hy.1 hy.2
  obtain ⟨hb1, hb2⟩ := mul_between' (a := (I.2 : ℝ)) hy.1 hy.2
  constructor
  · refine (floorD_le' _).trans ?_
    rw [Rat.cast_min, Rat.cast_min, Rat.cast_min, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul,
      Rat.cast_mul]
    exact (min_le_min ha1 hb1).trans hx1
  · refine le_trans ?_ (le_ceilD' _)
    rw [Rat.cast_max, Rat.cast_max, Rat.cast_max, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul,
      Rat.cast_mul]
    exact hx2.trans (max_le_max ha2 hb2)

lemma mem_iinvN {J : IQ} {y : ℝ} (hy : Mem J y) (hneg : J.2 < 0) : Mem (iinvN J) (1 / y) := by
  have h2 : (J.2 : ℝ) < 0 := by exact_mod_cast hneg
  have hy0 : y < 0 := hy.2.trans_lt h2
  have hJ1 : (J.1 : ℝ) < 0 := hy.1.trans_lt hy0
  constructor
  · refine (floorD_le' _).trans ?_
    push_cast
    exact (one_div_le_one_div_of_neg h2 hy0).mpr hy.2
  · refine le_trans ?_ (le_ceilD' _)
    push_cast
    exact (one_div_le_one_div_of_neg hy0 hJ1).mpr hy.1

/-! ### Cells -/

/-- The record's cell conditions (without its bound `W`), from `1/2` on. -/
def okD (c : Cell) : Bool :=
  decide (1 / 2 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.rlo) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL)

/-- `cos (πx)`, `sin (πx)` and `πx` on a cell, as in `cell_sound`. -/
theorem cell_cs (c : Cell) (h : okD c = true) (x : ℝ) (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    Mem c.CX (Real.cos (Real.pi * x)) ∧ Mem c.SX (Real.sin (Real.pi * x))
      ∧ Mem (c.BL, c.BU) (Real.pi * x) := by
  simp only [okD, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hL, hLU⟩, hr0⟩, hTU⟩, hTL0q⟩, hBL0q⟩ := h
  have h0 : (0 : ℚ) ≤ c.L := le_trans (by norm_num) hL
  have h0' : (0:ℝ) ≤ c.L := Rat.cast_nonneg.mpr h0
  have hr0' : (0:ℝ) ≤ c.rlo := Rat.cast_nonneg.mpr hr0
  have hTL0 : (0:ℝ) ≤ c.TL := Rat.cast_nonneg.mpr hTL0q
  have hBL0 : (0:ℝ) ≤ c.BL := Rat.cast_nonneg.mpr hBL0q
  have hTU' : (c.TU : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hTU; simpa using this
  set r : ℝ := if c.side then x - c.A else c.A - x with hr
  have hrlo : (c.rlo : ℝ) ≤ r := by
    simp only [Cell.rlo, hr]; split_ifs <;> push_cast <;> linarith
  have hrhi : r ≤ c.rhi := by
    simp only [Cell.rhi, hr]; split_ifs <;> push_cast <;> linarith
  have hr0r : 0 ≤ r := hr0'.trans hrlo
  have hTL : (c.TL : ℝ) ≤ Real.pi * r := by
    have h1 : (c.TL : ℝ) ≤ ((piLoQ * c.rlo : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (mul_ge_of piLoQ_le hrlo piLoQ_nonneg hr0' le_rfl)
  have hTUr : Real.pi * r ≤ c.TU := by
    have h1 : ((piHiQ * c.rhi : ℚ) : ℝ) ≤ (c.TU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (mul_le_of piHiQ_ge hrhi Real.pi_pos.le hr0r le_rfl).trans h1
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0r
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU'
  have hc1 : ((c.CI).1 : ℝ) ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU'
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((c.CI).1 : ℝ) ≤ ((taylorCosQ c.TU - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CI).2 : ℝ) := by
    have h := cos_upper hTL0 hTL hθ1
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((taylorCosQ c.TL + errQ : ℚ) : ℝ) ≤ ((c.CI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hs1 : ((c.SI).1 : ℝ) ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((c.SI).1 : ℝ) ≤ ((taylorSinQ c.TL - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SI).2 : ℝ) := by
    have h := sin_upper hθ0 hTUr hTU'
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((taylorSinQ c.TU + errQ : ℚ) : ℝ) ≤ ((c.SI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hcs := cos_sin_half c.k
  have eA : (c.A : ℝ) = (c.k : ℝ) / 2 := by simp [Cell.A]
  refine ⟨?_, ?_, ?_⟩
  · cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, Bool.false_eq_true, if_false]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, if_true]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  · cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, Bool.false_eq_true, if_false]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, if_true]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  · constructor
    · have h1 : (c.BL : ℝ) ≤ ((piLoQ * c.L : ℚ) : ℝ) := floorD_le' _
      rw [Rat.cast_mul] at h1
      exact h1.trans (mul_ge_of piLoQ_le hx1 piLoQ_nonneg h0' le_rfl)
    · have h1 : ((piHiQ * c.U : ℚ) : ℝ) ≤ (c.BU : ℝ) := le_ceilD' _
      rw [Rat.cast_mul] at h1
      exact (mul_le_of piHiQ_ge hx2 Real.pi_pos.le (h0'.trans hx1) le_rfl).trans h1

/-! ### The enclosures, from the cell's `cos`, `sin` and `θ = πx` -/

def Gq : IQ := (gamLoQ, gamHiQ)
def Pq : IQ := (piLoQ, piHiQ)

/-- `(K, W1, W2)` enclosing `kfun`, `w1`, `w2` from enclosures `C, S, T` of `cos θ, sin θ, θ`. -/
def enc (C S T : IQ) : IQ × IQ × IQ :=
  let G2T := iscale 2 (imul Gq T)
  let N := isub C (imul G2T S)
  let N1 := isub (imul (ineg (iadd (cst 1) (iscale 2 Gq))) S) (imul G2T C)
  let N2 := iadd (imul (ineg (iadd (cst 1) (iscale 4 Gq))) C) (imul G2T S)
  let T2 := imul T T
  let iD := iinvN (isub (cst 1) (iscale 2 T2))
  let iD2 := imul iD iD
  let K := imul N iD
  let K1 := iadd (imul N1 iD) (imul (iscale 4 (imul T N)) iD2)
  let K2 := iadd (iadd (iadd (imul N2 iD) (imul (iscale 8 (imul T N1)) iD2))
    (imul (iscale 4 N) iD2)) (imul (iscale 32 (imul T2 N)) (imul iD2 iD))
  (K, iscale 2 (imul Pq (imul K K1)), iscale 2 (imul (imul Pq Pq) (iadd (imul K1 K1) (imul K K2))))

/-- The denominator enclosure is negative. -/
def negD (T : IQ) : Bool := decide ((isub (cst 1) (iscale 2 (imul T T))).2 < 0)

theorem enc_sound {C S T : IQ} {x : ℝ} (hC : Mem C (Real.cos (Real.pi * x)))
    (hS : Mem S (Real.sin (Real.pi * x))) (hT : Mem T (Real.pi * x)) (hneg : negD T = true) :
    Mem (enc C S T).1 (kfun x) ∧ Mem (enc C S T).2.1 (w1 x) ∧ Mem (enc C S T).2.2 (w2 x) := by
  simp only [negD, decide_eq_true_eq] at hneg
  set θ := Real.pi * x with hθ
  have hG : Mem Gq gam := ⟨gamLoQ_le, gamHiQ_ge⟩
  have hP : Mem Pq Real.pi := ⟨piLoQ_le, piHiQ_ge⟩
  have hG2T := mem_iscale 2 (mem_imul hG hT)
  have hN : Mem (isub C (imul (iscale 2 (imul Gq T)) S)) (Nf θ) := by
    have := mem_isub hC (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold Nf; push_cast; ring
  have hN1 : Mem (isub (imul (ineg (iadd (cst 1) (iscale 2 Gq))) S) (imul (iscale 2 (imul Gq T)) C))
      (N1f θ) := by
    have := mem_isub (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale 2 hG))) hS)
      (mem_imul hG2T hC)
    refine mem_congr this ?_; unfold N1f; push_cast; ring
  have hN2 : Mem (iadd (imul (ineg (iadd (cst 1) (iscale 4 Gq))) C) (imul (iscale 2 (imul Gq T)) S))
      (N2f θ) := by
    have := mem_iadd (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale 4 hG))) hC)
      (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold N2f; push_cast; ring
  have hT2 := mem_imul hT hT
  have hDm : Mem (isub (cst 1) (iscale 2 (imul T T))) (Df θ) := by
    have := mem_isub (mem_cst 1) (mem_iscale 2 hT2)
    refine mem_congr this ?_; unfold Df; push_cast; ring
  have hiD := mem_iinvN hDm hneg
  have hD0 : Df θ ≠ 0 := by
    have : Df θ < 0 := hDm.2.trans_lt (by exact_mod_cast hneg)
    exact this.ne
  have hiD2 := mem_imul hiD hiD
  have hK := mem_imul hN hiD
  have hK1 := mem_iadd (mem_imul hN1 hiD) (mem_imul (mem_iscale 4 (mem_imul hT hN)) hiD2)
  have hK2 := mem_iadd (mem_iadd (mem_iadd (mem_imul hN2 hiD)
    (mem_imul (mem_iscale 8 (mem_imul hT hN1)) hiD2)) (mem_imul (mem_iscale 4 hN) hiD2))
    (mem_imul (mem_iscale 32 (mem_imul hT2 hN)) (mem_imul hiD2 hiD))
  have ek : kfun x = Nf θ * (1 / Df θ) := by
    rw [kfun_closed x (by simpa [Df, hθ] using hD0)]; simp [Nf, Df, hθ]; ring
  have ek1 : k1 x = Real.pi * (N1f θ * (1 / Df θ) + 4 * (θ * Nf θ) * (1 / Df θ * (1 / Df θ))) := by
    unfold k1 K1f; rw [← hθ]; field_simp
  have ek2 : k2 x = Real.pi ^ 2 * (N2f θ * (1 / Df θ) + 8 * (θ * N1f θ) * (1 / Df θ * (1 / Df θ))
      + 4 * Nf θ * (1 / Df θ * (1 / Df θ)) + 32 * (θ * θ * Nf θ) * (1 / Df θ * (1 / Df θ) * (1 / Df θ))) := by
    unfold k2 K2f; rw [← hθ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [ek]; exact hK
  · refine mem_congr (mem_iscale 2 (mem_imul hP (mem_imul hK hK1))) ?_
    unfold w1; rw [ek, ek1]; push_cast; ring
  · refine mem_congr (mem_iscale 2 (mem_imul (mem_imul hP hP)
      (mem_iadd (mem_imul hK1 hK1) (mem_imul hK hK2)))) ?_
    unfold w2; rw [ek, ek1, ek2]; push_cast; ring

/-- Enclosures on a cell. -/
def cellEnc (c : Cell) : IQ × IQ × IQ := enc c.CX c.SX (c.BL, c.BU)

theorem cellEnc_sound (c : Cell) (h : okD c = true) (hn : negD (c.BL, c.BU) = true) (x : ℝ)
    (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    Mem (cellEnc c).1 (kfun x) ∧ Mem (cellEnc c).2.1 (w1 x) ∧ Mem (cellEnc c).2.2 (w2 x) := by
  obtain ⟨hC, hS, hT⟩ := cell_cs c h x hx1 hx2
  exact enc_sound hC hS hT hn

end Riemann.Encl

end

section

/-!
# Convex-basin certificates: dimension-free parts

Grid cells of `2⁻³²`, chains of cells carrying `l ≤ w''`, the second-order bound of one pair at an
expansion point, and positive semidefinite quadratic forms by `LDLᵀ`.
-/

noncomputable section

namespace Riemann.BasinC

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint Riemann.Deriv Riemann.Encl

def Dq : ℕ := 4294967296

/-- Grid coordinates over `2³²`. -/
def toRq (n : ℕ) : ℝ := (n : ℝ) / Dq

lemma Dq_pos : (0 : ℝ) < Dq := by norm_num [Dq]

lemma toRq_le_toRq {a b : ℕ} : toRq a ≤ toRq b ↔ a ≤ b := by
  unfold toRq
  rw [div_le_div_iff_of_pos_right Dq_pos]
  exact Nat.cast_le

lemma toRq_add (a b : ℕ) : toRq (a + b) = toRq a + toRq b := by
  unfold toRq; push_cast; ring

/-! ### Grid cells and chains -/

/-- The cell `[a, b]` (grid units), anchored at the half-integer nearest its midpoint. -/
def segCell (a b : ℕ) : Cell :=
  ⟨(a : ℚ) / 4294967296, (b : ℚ) / 4294967296, (a + b + 2147483648) / 4294967296,
    decide ((a + b + 2147483648) / 4294967296 * 4294967296 ≤ 2 * a), 0⟩

lemma segCell_L (a b : ℕ) : (((segCell a b).L : ℚ) : ℝ) = toRq a := by
  simp [segCell, toRq, Dq]

lemma segCell_U (a b : ℕ) : (((segCell a b).U : ℚ) : ℝ) = toRq b := by
  simp [segCell, toRq, Dq]

def cellOk (c : Cell) : Bool := okD c && negD (c.BL, c.BU)

/-- Every cell of the chain `a = x₀ < x₁ < … ` has `l ≤ w''`. -/
def chainGe (l : ℚ) : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: rest => cellOk (segCell a b) && decide (l ≤ (cellEnc (segCell a b)).2.2.1)
      && chainGe l b rest

def chainLast : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: rest => chainLast b rest

theorem chainGe_sound (l : ℚ) :
    ∀ (rest : List ℕ) (a b : ℕ), chainGe l a (b :: rest) = true →
      ∀ x : ℝ, toRq a ≤ x → x ≤ toRq (chainLast b rest) → (l : ℝ) ≤ w2 x := by
  intro rest
  induction rest with
  | nil =>
    intro a b h x h1 h2
    simp only [chainGe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [cellOk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hok, hneg⟩, hl⟩, -⟩ := h
    have hx1 : (((segCell a b).L : ℚ) : ℝ) ≤ x := by rw [segCell_L]; exact h1
    have hx2 : x ≤ (((segCell a b).U : ℚ) : ℝ) := by rw [segCell_U]; simpa [chainLast] using h2
    exact (Rat.cast_le.mpr hl).trans (cellEnc_sound _ hok hneg x hx1 hx2).2.2.1
  | cons c rest ih =>
    intro a b h x h1 h2
    rw [chainGe, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hl⟩, hrest⟩ := h
    rw [cellOk, Bool.and_eq_true] at hc
    obtain ⟨hok, hneg⟩ := hc
    rcases le_total x (toRq b) with hxb | hxb
    · have hx1 : (((segCell a b).L : ℚ) : ℝ) ≤ x := by rw [segCell_L]; exact h1
      have hx2 : x ≤ (((segCell a b).U : ℚ) : ℝ) := by rw [segCell_U]; exact hxb
      exact (Rat.cast_le.mpr hl).trans (cellEnc_sound _ hok hneg x hx1 hx2).2.2.1
    · exact ih b c hrest x hxb (by simpa [chainLast] using h2)

/-! ### One pair: the second-order bound at an expansion point -/

def wloK (K : IQ) : ℚ := if 0 ≤ K.1 then K.1 * K.1 else if K.2 ≤ 0 then K.2 * K.2 else 0

lemma wloK_le {K : IQ} {k : ℝ} (h : Mem K k) : (wloK K : ℝ) ≤ k ^ 2 := by
  unfold wloK
  split_ifs with h1 h2
  · have : (0 : ℝ) ≤ K.1 := by exact_mod_cast h1
    push_cast; nlinarith [h.1]
  · have : (K.2 : ℝ) ≤ 0 := by exact_mod_cast h2
    push_cast; nlinarith [h.2]
  · push_cast; positivity

def ptCell (T : ℕ) : Cell := segCell T T

def encK (T : ℕ) : IQ := (cellEnc (ptCell T)).1
def encW1 (T : ℕ) : IQ := (cellEnc (ptCell T)).2.1

/-- A pair's data: the chain `a, b :: rest` with `l ≤ w''` on it. -/
structure Chain where
  (a b : ℕ) (rest : List ℕ) (l : ℚ)

def Chain.last (c : Chain) : ℕ := chainLast c.b c.rest

/-- The chain is valid, covers `[lo, hi]` and the expansion point `T`, from `1/2` on. -/
def pairOk (c : Chain) (lo hi T : ℕ) : Bool :=
  chainGe c.l c.a (c.b :: c.rest) && Nat.ble 2147483648 c.a && Nat.ble c.a lo && Nat.ble hi c.last
    && Nat.ble c.a T && Nat.ble T c.last && cellOk (ptCell T)

theorem pair_sound {c : Chain} {lo hi T : ℕ} (h : pairOk c lo hi T = true) :
    Mem (encW1 T) (w1 (toRq T)) ∧
      ∀ s : ℝ, toRq lo ≤ s → s ≤ toRq hi →
        (wloK (encK T) : ℝ) + w1 (toRq T) * (s - toRq T)
          + (c.l : ℝ) / 2 * (s - toRq T) ^ 2 ≤ wfun s := by
  simp only [pairOk, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hch, ha⟩, halo⟩, hhi⟩, haT⟩, hTl⟩, hpt⟩ := h
  rw [cellOk, Bool.and_eq_true] at hpt
  have hT1 : (((ptCell T).L : ℚ) : ℝ) ≤ toRq T := by rw [ptCell, segCell_L]
  have hT2 : toRq T ≤ (((ptCell T).U : ℚ) : ℝ) := by rw [ptCell, segCell_U]
  have henc := cellEnc_sound _ hpt.1 hpt.2 (toRq T) hT1 hT2
  refine ⟨henc.2.1, fun s hs1 hs2 => ?_⟩
  have ha' : (1 / 2 : ℝ) ≤ toRq c.a :=
    le_trans (le_of_eq (by norm_num [toRq, Dq])) (toRq_le_toRq.mpr ha)
  have hl : ∀ x ∈ Set.Icc (toRq c.a) (toRq c.last), (c.l : ℝ) ≤ w2 x :=
    fun x hx => chainGe_sound c.l c.rest c.a c.b hch x hx.1 hx.2
  have hsI : s ∈ Set.Icc (toRq c.a) (toRq c.last) :=
    ⟨(toRq_le_toRq.mpr halo).trans hs1, hs2.trans (toRq_le_toRq.mpr hhi)⟩
  have htI : toRq T ∈ Set.Icc (toRq c.a) (toRq c.last) :=
    ⟨toRq_le_toRq.mpr haT, toRq_le_toRq.mpr hTl⟩
  have htay := wfun_taylor2 ha' hl hsI htI
  have hw : (wloK (encK T) : ℝ) ≤ wfun (toRq T) := by
    have := wloK_le henc.1; simpa [wfun, encK] using this
  linarith

/-! ### Positive semidefinite 4×4 forms -/

def form2 (p q r x y : ℝ) : ℝ := p * x ^ 2 + 2 * q * x * y + r * y ^ 2
def form3 (a11 a12 a13 a22 a23 a33 x y z : ℝ) : ℝ :=
  a11 * x ^ 2 + a22 * y ^ 2 + a33 * z ^ 2 + 2 * (a12 * x * y + a13 * x * z + a23 * y * z)
def form4 (m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3 : ℝ) : ℝ :=
  m00 * d0 ^ 2 + m11 * d1 ^ 2 + m22 * d2 ^ 2 + m33 * d3 ^ 2
    + 2 * (m01 * d0 * d1 + m02 * d0 * d2 + m03 * d0 * d3 + m12 * d1 * d2 + m13 * d1 * d3
      + m23 * d2 * d3)

lemma form2_nonneg {p q r : ℝ} (hp : 0 < p) (hs : 0 ≤ r - q * q / p) (x y : ℝ) :
    0 ≤ form2 p q r x y := by
  have e : form2 p q r x y = p * (x + q / p * y) ^ 2 + (r - q * q / p) * y ^ 2 := by
    unfold form2; field_simp; ring
  rw [e]; positivity

lemma form3_nonneg {a11 a12 a13 a22 a23 a33 : ℝ} (h1 : 0 < a11)
    (h2 : 0 < a22 - a12 * a12 / a11)
    (h3 : 0 ≤ (a33 - a13 * a13 / a11) - (a23 - a12 * a13 / a11) * (a23 - a12 * a13 / a11)
      / (a22 - a12 * a12 / a11))
    (x y z : ℝ) : 0 ≤ form3 a11 a12 a13 a22 a23 a33 x y z := by
  have e : form3 a11 a12 a13 a22 a23 a33 x y z = a11 * (x + (a12 * y + a13 * z) / a11) ^ 2
      + form2 (a22 - a12 * a12 / a11) (a23 - a12 * a13 / a11) (a33 - a13 * a13 / a11) y z := by
    unfold form3 form2; field_simp; ring
  rw [e]
  have := form2_nonneg h2 h3 y z
  positivity

/-- LDLᵀ on the upper triangle: positive leading pivots, nonnegative last one. -/
def psd4 (m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 : ℚ) : Bool :=
  let a11 := m11 - m01 * m01 / m00
  let a12 := m12 - m01 * m02 / m00
  let a13 := m13 - m01 * m03 / m00
  let a22 := m22 - m02 * m02 / m00
  let a23 := m23 - m02 * m03 / m00
  let a33 := m33 - m03 * m03 / m00
  let b22 := a22 - a12 * a12 / a11
  let b23 := a23 - a12 * a13 / a11
  let b33 := a33 - a13 * a13 / a11
  decide (0 < m00) && decide (0 < a11) && decide (0 < b22) && decide (0 ≤ b33 - b23 * b23 / b22)

theorem psd4_sound {m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 : ℚ}
    (h : psd4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 = true) (d0 d1 d2 d3 : ℝ) :
    0 ≤ form4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3 := by
  simp only [psd4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have h0' : (0 : ℝ) < m00 := by exact_mod_cast h0
  have h1' : (0 : ℝ) < (m11 : ℝ) - m01 * m01 / m00 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2' := (Rat.cast_lt (K := ℝ)).mpr h2
  have h3' := (Rat.cast_le (K := ℝ)).mpr h3
  push_cast at h2' h3'
  have e : form4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3
      = m00 * (d0 + (m01 * d1 + m02 * d2 + m03 * d3) / m00) ^ 2
        + form3 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
          (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00) (m33 - m03 * m03 / m00) d1 d2 d3 := by
    unfold form4 form3; field_simp; ring
  rw [e]
  have := form3_nonneg h1' h2' h3' d1 d2 d3
  have hsq : 0 ≤ (m00 : ℝ) * (d0 + (m01 * d1 + m02 * d2 + m03 * d3) / m00) ^ 2 := by positivity
  linarith


/-! ### Sums of gradient terms, offsets, and five-dimensional forms -/

def sumI : List (ℕ × ℕ) → IQ
  | [] => cst 0
  | (w, T) :: rest => iadd (iscale w (encW1 T)) (sumI rest)

def sumR : List (ℕ × ℕ) → ℝ
  | [] => 0
  | (w, T) :: rest => (w : ℝ) * w1 (toRq T) + sumR rest

lemma mem_sumI : ∀ ts : List (ℕ × ℕ), (∀ wt ∈ ts, Mem (encW1 wt.2) (w1 (toRq wt.2))) →
    Mem (sumI ts) (sumR ts)
  | [], _ => by simpa [sumI, sumR] using mem_cst 0
  | (w, T) :: rest, h => by
    simp only [sumI, sumR]
    have h1 := mem_iscale (w : ℚ) (h (w, T) List.mem_cons_self)
    push_cast at h1
    exact mem_iadd h1 (mem_sumI rest fun wt hwt => h wt (List.mem_cons_of_mem _ hwt))

/-- Enclosure of `P + Σ w · w1(T)`. -/
def gradI (P : ℕ) (ts : List (ℕ × ℕ)) : IQ := iadd (cst (P : ℚ)) (sumI ts)

lemma mem_gradI (P : ℕ) (ts : List (ℕ × ℕ)) (h : ∀ wt ∈ ts, Mem (encW1 wt.2) (w1 (toRq wt.2))) :
    Mem (gradI P ts) ((P : ℝ) + sumR ts) := by
  have := mem_iadd (mem_cst (P : ℚ)) (mem_sumI ts h)
  unfold gradI; refine mem_congr this ?_; push_cast; ring

/-- The offsets `g − q` on `[lo, hi]` (grid units). -/
def offI (lo hi q : ℕ) : IQ := (((lo : ℚ) - q) / 4294967296, ((hi : ℚ) - q) / 4294967296)

lemma mem_offI {lo hi q : ℕ} {x : ℝ} (h1 : toRq lo ≤ x) (h2 : x ≤ toRq hi) :
    Mem (offI lo hi q) (x - toRq q) := by
  unfold offI Mem toRq Dq at *
  push_cast at *
  constructor <;> [skip; skip] <;> rw [sub_div] <;> linarith

def form5 (m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4 : ℝ) : ℝ :=
  m00 * d0 ^ 2 + 2 * (m01 * d0 * d1 + m02 * d0 * d2 + m03 * d0 * d3 + m04 * d0 * d4)
    + form4 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d1 d2 d3 d4

/-- One elimination step, then `psd4` on the Schur complement. -/
def psd5 (m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 : ℚ) : Bool :=
  decide (0 < m00) && psd4 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
    (m14 - m01 * m04 / m00) (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00)
    (m24 - m02 * m04 / m00) (m33 - m03 * m03 / m00) (m34 - m03 * m04 / m00)
    (m44 - m04 * m04 / m00)

theorem psd5_sound {m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 : ℚ}
    (h : psd5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 = true)
    (d0 d1 d2 d3 d4 : ℝ) :
    0 ≤ form5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4 := by
  simp only [psd5, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h4⟩ := h
  have h0' : (0 : ℝ) < m00 := by exact_mod_cast h0
  have hs := psd4_sound h4 d1 d2 d3 d4
  push_cast at hs
  have e : form5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4
      = m00 * (d0 + (m01 * d1 + m02 * d2 + m03 * d3 + m04 * d4) / m00) ^ 2
        + form4 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
          (m14 - m01 * m04 / m00) (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00)
          (m24 - m02 * m04 / m00) (m33 - m03 * m03 / m00) (m34 - m03 * m04 / m00)
          (m44 - m04 * m04 / m00) d1 d2 d3 d4 := by
    unfold form5 form4; field_simp; ring
  rw [e]
  have hsq : 0 ≤ (m00 : ℝ) * (d0 + (m01 * d1 + m02 * d2 + m03 * d3 + m04 * d4) / m00) ^ 2 := by
    positivity
  linarith

end Riemann.BasinC

end

