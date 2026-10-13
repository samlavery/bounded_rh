/-
AMW/Trig.lean — rational enclosures of sin and cos for kernel-checked certificates.

The twelve-term Taylor bound (|e^{iθ} − Σ_{m<12}(iθ)^m/m!| ≤ |θ|^12·13/5748019200 for |θ| ≤ 1, from
`Complex.exp_bound`) with monotonicity of sin and cos on [0, 1], in rational Horner form, rounded
outwards to 10⁻¹⁰.  `sinPiI t` encloses sin(πt) for t ∈ ℚ: t = k/2 + r with |r| ≤ 1/4 and
(cos, sin)(πk/2) ∈ {0, ±1}².  Adapted from the ThreePoint layer of the Zeta Lab bridge (MIT), as
carried in SolutionSevW10D.lean.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real

namespace AMW

theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

/-! ### rational Horner forms and outward rounding -/

def tCosQ (t : ℚ) : ℚ :=
  let s := t * t
  1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
def tSinQ (t : ℚ) : ℚ :=
  let s := t * t
  t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
def errQ : ℚ := 13/5748019200

/-- rounding to 10⁻¹⁰, down and up. -/
def fl (x : ℚ) : ℚ := ((⌊x * 10000000000⌋ : ℤ) : ℚ) / 10000000000
def cl (x : ℚ) : ℚ := ((⌈x * 10000000000⌉ : ℤ) : ℚ) / 10000000000

theorem fl_le (x : ℚ) : ((fl x : ℚ) : ℝ) ≤ (x : ℝ) := by
  refine Rat.cast_le.mpr ?_
  unfold fl; rw [div_le_iff₀ (by norm_num)]; exact Int.floor_le _

theorem le_cl (x : ℚ) : (x : ℝ) ≤ ((cl x : ℚ) : ℝ) := by
  refine Rat.cast_le.mpr ?_
  unfold cl; rw [le_div_iff₀ (by norm_num)]; exact Int.le_ceil _

theorem tCosQ_cast (q : ℚ) : ((tCosQ q : ℚ) : ℝ)
    = 1 - (q:ℝ)^2/2 + (q:ℝ)^4/24 - (q:ℝ)^6/720 + (q:ℝ)^8/40320 - (q:ℝ)^10/3628800 := by
  simp only [tCosQ]; push_cast; ring

theorem tSinQ_cast (q : ℚ) : ((tSinQ q : ℚ) : ℝ)
    = (q:ℝ) - (q:ℝ)^3/6 + (q:ℝ)^5/120 - (q:ℝ)^7/5040 + (q:ℝ)^9/362880 - (q:ℝ)^11/39916800 := by
  simp only [tSinQ]; push_cast; ring

theorem errQ_cast : ((errQ : ℚ) : ℝ) = 13/5748019200 := by simp only [errQ]; push_cast; ring

private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ 13/5748019200 := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  nlinarith

private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]

/-! ### monotone enclosures on [0, 1] -/

theorem cos_ge_of {θ : ℝ} {u : ℚ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : (u : ℝ) ≤ 1) :
    ((tCosQ u - errQ : ℚ) : ℝ) ≤ Real.cos θ := by
  have h0u : (0:ℝ) ≤ u := h0.trans hu
  have hmono : Real.cos u ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans one_le_pi) hu
  have ht := abs_le.mp (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).1
  have he := err_scale h0u hu1
  push_cast; rw [tCosQ_cast, errQ_cast]
  linarith [ht.1, ht.2]

theorem cos_le_of {θ : ℝ} {l : ℚ} (h0 : (0:ℝ) ≤ l) (hl : (l:ℝ) ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ ((tCosQ l + errQ : ℚ) : ℝ) := by
  have hl1 : (l:ℝ) ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
  have ht := abs_le.mp (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := err_scale h0 hl1
  push_cast; rw [tCosQ_cast, errQ_cast]
  linarith [ht.1, ht.2]

theorem sin_ge_of {θ : ℝ} {l : ℚ} (h0 : (0:ℝ) ≤ l) (hl : (l:ℝ) ≤ θ) (hθ1 : θ ≤ 1) :
    ((tSinQ l - errQ : ℚ) : ℝ) ≤ Real.sin θ := by
  have hl1 : (l:ℝ) ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := abs_le.mp (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := err_scale h0 hl1
  push_cast; rw [tSinQ_cast, errQ_cast]
  linarith [ht.1, ht.2]

theorem sin_le_of {θ : ℝ} {u : ℚ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : (u:ℝ) ≤ 1) :
    Real.sin θ ≤ ((tSinQ u + errQ : ℚ) : ℝ) := by
  have h0u : (0:ℝ) ≤ u := h0.trans hu
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin θ ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
  have ht := abs_le.mp (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).2
  have he := err_scale h0u hu1
  push_cast; rw [tSinQ_cast, errQ_cast]
  linarith [ht.1, ht.2]

/-! ### π and √2 -/

def piLoQ : ℚ := 3141592 / 10 ^ 6
def piHiQ : ℚ := 3141593 / 10 ^ 6
def s2LoQ : ℚ := 14142135 / 10 ^ 7
def s2HiQ : ℚ := 14142136 / 10 ^ 7

theorem piLoQ_le : ((piLoQ : ℚ) : ℝ) ≤ Real.pi := by
  have h := Real.pi_gt_d6; simp only [piLoQ]; push_cast; norm_num at h ⊢; linarith

theorem piHiQ_ge : Real.pi ≤ ((piHiQ : ℚ) : ℝ) := by
  have h := Real.pi_lt_d6; simp only [piHiQ]; push_cast; norm_num at h ⊢; linarith

theorem s2LoQ_le : ((s2LoQ : ℚ) : ℝ) ≤ Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  simp only [s2LoQ]; push_cast; nlinarith

theorem s2HiQ_ge : Real.sqrt 2 ≤ ((s2HiQ : ℚ) : ℝ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  simp only [s2HiQ]; push_cast; nlinarith

/-! ### interval helpers -/

def imulZ (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
def isub (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)

/-- `x ∈ I` for a rational interval. -/
def InI (I : ℚ × ℚ) (x : ℝ) : Prop := ((I.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((I.2 : ℚ) : ℝ)

theorem imulZ_sound (e : ℤ) {I : ℚ × ℚ} {f : ℝ} (h : InI I f) : InI (imulZ e I) ((e:ℝ) * f) := by
  obtain ⟨h1, h2⟩ := h
  unfold imulZ InI
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 he', mul_le_mul_of_nonneg_left h2 he'⟩
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 he', mul_le_mul_of_nonpos_left h1 he'⟩

theorem iadd_sound {I J : ℚ × ℚ} {f g : ℝ} (hI : InI I f) (hJ : InI J g) : InI (iadd I J) (f + g) := by
  unfold iadd InI at *; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isub_sound {I J : ℚ × ℚ} {f g : ℝ} (hI : InI I f) (hJ : InI J g) : InI (isub I J) (f - g) := by
  unfold isub InI at *; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-- multiplication of an enclosure of `x` by `π`. -/
def piMul (S : ℚ × ℚ) : ℚ × ℚ := (min (piLoQ * S.1) (piHiQ * S.1), max (piLoQ * S.2) (piHiQ * S.2))

theorem piMul_sound {S : ℚ × ℚ} {x : ℝ} (h : InI S x) : InI (piMul S) (Real.pi * x) := by
  obtain ⟨h1, h2⟩ := h
  have hlo := piLoQ_le; have hhi := piHiQ_ge
  have hp0 : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  unfold piMul InI
  simp only; push_cast
  constructor
  · rcases le_or_gt 0 (S.1 : ℝ) with hs | hs
    · refine (min_le_left _ _).trans ?_
      calc (piLoQ : ℝ) * S.1 ≤ Real.pi * S.1 := mul_le_mul_of_nonneg_right hlo hs
        _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left h1 hp0
    · refine (min_le_right _ _).trans ?_
      calc (piHiQ : ℝ) * S.1 ≤ Real.pi * S.1 := mul_le_mul_of_nonpos_right hhi hs.le
        _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left h1 hp0
  · rcases le_or_gt 0 (S.2 : ℝ) with hs | hs
    · refine le_trans ?_ (le_max_right _ _)
      calc Real.pi * x ≤ Real.pi * S.2 := mul_le_mul_of_nonneg_left h2 hp0
        _ ≤ (piHiQ : ℝ) * S.2 := mul_le_mul_of_nonneg_right hhi hs
    · refine le_trans ?_ (le_max_left _ _)
      calc Real.pi * x ≤ Real.pi * S.2 := mul_le_mul_of_nonneg_left h2 hp0
        _ ≤ (piLoQ : ℝ) * S.2 := mul_le_mul_of_nonpos_right hlo hs.le

/-! ### sin(πt) and cos(πt) for small t ≥ 0, and sin(πt) for any rational t -/

def TLo (a : ℚ) : ℚ := fl (piLoQ * a)
def THi (a : ℚ) : ℚ := cl (piHiQ * a)
def cosI (a : ℚ) : ℚ × ℚ := (fl (tCosQ (THi a) - errQ), cl (tCosQ (TLo a) + errQ))
def sinI (a : ℚ) : ℚ × ℚ := (fl (tSinQ (TLo a) - errQ), cl (tSinQ (THi a) + errQ))

theorem TLo_le {a : ℚ} (ha : 0 ≤ a) : ((TLo a : ℚ) : ℝ) ≤ Real.pi * a :=
  (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right piLoQ_le (by exact_mod_cast ha))

theorem le_THi {a : ℚ} (ha : 0 ≤ a) : Real.pi * a ≤ ((THi a : ℚ) : ℝ) :=
  le_trans (by push_cast; exact mul_le_mul_of_nonneg_right piHiQ_ge (by exact_mod_cast ha)) (le_cl _)

theorem cosI_sound {a : ℚ} (ha : 0 ≤ a) (h0 : 0 ≤ TLo a) (h1 : THi a ≤ 1) :
    InI (cosI a) (Real.cos (Real.pi * a)) := by
  have hθ0 : 0 ≤ Real.pi * a := mul_nonneg Real.pi_pos.le (by exact_mod_cast ha)
  have h1' : ((THi a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
  have h0' : (0:ℝ) ≤ ((TLo a : ℚ) : ℝ) := by exact_mod_cast h0
  exact ⟨(fl_le _).trans (cos_ge_of hθ0 (le_THi ha) h1'),
    (cos_le_of h0' (TLo_le ha) ((le_THi ha).trans h1')).trans (le_cl _)⟩

theorem sinI_sound {a : ℚ} (ha : 0 ≤ a) (h0 : 0 ≤ TLo a) (h1 : THi a ≤ 1) :
    InI (sinI a) (Real.sin (Real.pi * a)) := by
  have hθ0 : 0 ≤ Real.pi * a := mul_nonneg Real.pi_pos.le (by exact_mod_cast ha)
  have h1' : ((THi a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
  have h0' : (0:ℝ) ≤ ((TLo a : ℚ) : ℝ) := by exact_mod_cast h0
  exact ⟨(fl_le _).trans (sin_ge_of h0' (TLo_le ha) ((le_THi ha).trans h1')),
    (sin_le_of hθ0 (le_THi ha) h1').trans (le_cl _)⟩

/-- `(cos (π k/2), sin (π k/2))` as integers. -/
def csA : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k+1 => (-(csA k).2, (csA k).1)

theorem cos_sin_half (k : ℕ) :
    Real.cos (Real.pi * ((k:ℝ) / 2)) = ((csA k).1 : ℝ) ∧
      Real.sin (Real.pi * ((k:ℝ) / 2)) = ((csA k).2 : ℝ) := by
  induction k with
  | zero => simp [csA]
  | succ k ih =>
    have e : Real.pi * (((k + 1 : ℕ) : ℝ) / 2) = Real.pi * ((k:ℝ) / 2) + Real.pi / 2 := by
      push_cast; ring
    rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ih.1, ih.2]
    simp [csA]

def kOf (t : ℚ) : ℕ := (⌊2 * t + 1 / 2⌋).toNat
def rOf (t : ℚ) : ℚ := t - (kOf t : ℚ) / 2

/-- an enclosure of sin(πt). -/
def sinPiI (t : ℚ) : ℚ × ℚ :=
  if 0 ≤ rOf t then iadd (imulZ (csA (kOf t)).2 (cosI (rOf t))) (imulZ (csA (kOf t)).1 (sinI (rOf t)))
  else isub (imulZ (csA (kOf t)).2 (cosI (-rOf t))) (imulZ (csA (kOf t)).1 (sinI (-rOf t)))

/-- its validity condition (π|r| ≤ 1 after rounding, and the rounded lower end nonnegative). -/
def sinPiOk (t : ℚ) : Bool := decide (0 ≤ TLo |rOf t|) && decide (THi |rOf t| ≤ 1)

theorem sinPiI_sound (t : ℚ) (h : sinPiOk t = true) : InI (sinPiI t) (Real.sin (Real.pi * t)) := by
  simp only [sinPiOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hcs := cos_sin_half (kOf t)
  have ht : (t : ℝ) = (kOf t : ℝ) / 2 + (rOf t : ℚ) := by
    simp only [rOf]; push_cast; ring
  unfold sinPiI
  split_ifs with hr
  · rw [abs_of_nonneg hr] at h0 h1
    have e : Real.sin (Real.pi * t) = ((csA (kOf t)).2 : ℝ) * Real.cos (Real.pi * (rOf t : ℚ))
        + ((csA (kOf t)).1 : ℝ) * Real.sin (Real.pi * (rOf t : ℚ)) := by
      rw [ht, mul_add, Real.sin_add, hcs.1, hcs.2]
    rw [e]
    exact iadd_sound (imulZ_sound _ (cosI_sound hr h0 h1)) (imulZ_sound _ (sinI_sound hr h0 h1))
  · push_neg at hr
    rw [abs_of_neg hr] at h0 h1
    have hr' : 0 ≤ -rOf t := by linarith
    have e : Real.sin (Real.pi * t) = ((csA (kOf t)).2 : ℝ) * Real.cos (Real.pi * ((-rOf t : ℚ) : ℝ))
        - ((csA (kOf t)).1 : ℝ) * Real.sin (Real.pi * ((-rOf t : ℚ) : ℝ)) := by
      have e2 : Real.pi * ((-rOf t : ℚ) : ℝ) = -(Real.pi * (rOf t : ℚ)) := by push_cast; ring
      rw [e2, Real.cos_neg, Real.sin_neg, ht, mul_add, Real.sin_add, hcs.1, hcs.2]; ring
    rw [e]
    exact isub_sound (imulZ_sound _ (cosI_sound hr' h0 h1)) (imulZ_sound _ (sinI_sound hr' h0 h1))

end AMW

end
