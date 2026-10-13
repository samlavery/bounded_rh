import AMW.Window

/-!
# AMW/Kernel — the pair kernel of the AMTOPA window

  `KfunAM x = ∫_{-½}^{½} vAM(t) cos(2πxt) dt`,  `kfunAM x = KfunAM x / KfunAM 0`,  `wfunAM x = kfunAM x²`.

The analogue of the record file's `Kfun/kfun/wfun` (which use `cos(√2 t)` in place of `vAM`). Facts: evenness,
`0 < KfunAM 0 = ∫ vAM`, `|KfunAM x| ≤ KfunAM 0` (`vAM > 0` on the window), so `|kfunAM| ≤ 1`, `0 ≤ wfunAM ≤ 1`; and
the closed form `KfunAM x = Σ_j cAM j · (sinc((ωAM j − 2πx)/2) + sinc((ωAM j + 2πx)/2))/2`, with
`KfunAM 0 = Σ_j cAM j · sinc(ωAM j / 2)`.  The normalisation `MAM` does not enter (`kfunAM` is scale-free).
-/

noncomputable section

open Real Set MeasureTheory

namespace AMW

/-- the unnormalised pair kernel. -/
def KfunAM (x : ℝ) : ℝ := ∫ t in (-(1:ℝ)/2)..(1/2), vAM t * Real.cos (2 * π * x * t)

/-- the normalised pair kernel. -/
def kfunAM (x : ℝ) : ℝ := KfunAM x / KfunAM 0

/-- the pair weight `w = k²`. -/
def wfunAM (x : ℝ) : ℝ := kfunAM x ^ 2

theorem KfunAM_neg (x : ℝ) : KfunAM (-x) = KfunAM x := by
  unfold KfunAM
  congr 1; funext t
  rw [show 2 * π * -x * t = -(2 * π * x * t) by ring, Real.cos_neg]

theorem kfunAM_neg (x : ℝ) : kfunAM (-x) = kfunAM x := by
  unfold kfunAM; rw [KfunAM_neg]

theorem wfunAM_neg (x : ℝ) : wfunAM (-x) = wfunAM x := by
  unfold wfunAM; rw [kfunAM_neg]

theorem wfunAM_sub_comm (a b : ℝ) : wfunAM (a - b) = wfunAM (b - a) := by
  rw [← neg_sub, wfunAM_neg]

theorem wfunAM_nonneg (x : ℝ) : 0 ≤ wfunAM x := sq_nonneg _

theorem vAM_pos_on {t : ℝ} (ht : t ∈ Icc (-(1:ℝ)/2) (1/2)) : 0 < vAM t :=
  lt_of_lt_of_le (by norm_num) (vAM_ge_core (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩))

theorem KfunAM_zero : KfunAM 0 = ∫ t in (-(1:ℝ)/2)..(1/2), vAM t := by
  unfold KfunAM; simp

theorem KfunAM_zero_pos : 0 < KfunAM 0 := by
  rw [KfunAM_zero]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact vAM_continuous.intervalIntegrable _ _
  · intro t ht; exact vAM_pos_on ⟨ht.1.le, ht.2.le⟩
  · norm_num

theorem abs_KfunAM_le (x : ℝ) : |KfunAM x| ≤ KfunAM 0 := by
  rw [KfunAM_zero]
  unfold KfunAM
  have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  calc |∫ t in (-(1:ℝ)/2)..(1/2), vAM t * Real.cos (2 * π * x * t)|
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |vAM t * Real.cos (2 * π * x * t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), vAM t := by
        apply intervalIntegral.integral_mono_on hab
        · exact ((vAM_continuous.mul (by fun_prop : Continuous fun t : ℝ =>
            Real.cos (2 * π * x * t))).abs).intervalIntegrable _ _
        · exact vAM_continuous.intervalIntegrable _ _
        · intro t ht
          rw [abs_mul, abs_of_pos (vAM_pos_on ht)]
          exact mul_le_of_le_one_right (vAM_pos_on ht).le (Real.abs_cos_le_one _)

theorem abs_kfunAM_le_one (x : ℝ) : |kfunAM x| ≤ 1 := by
  unfold kfunAM
  rw [abs_div, abs_of_pos KfunAM_zero_pos, div_le_one KfunAM_zero_pos]
  exact abs_KfunAM_le x

theorem wfunAM_le_one (x : ℝ) : wfunAM x ≤ 1 := by
  unfold wfunAM
  rw [← sq_abs]
  calc |kfunAM x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_kfunAM_le_one x) 2
    _ = 1 := one_pow 2

/-! ## Closed form -/

theorem integral_cos_mul_sinc (c : ℝ) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; norm_num
  · have hc2 : c / 2 ≠ 0 := by simpa using hc
    rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
      show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
      Real.sin_neg, smul_eq_mul]
    field_simp
    ring

/-- **closed form**: `KfunAM x = Σ_j cAM j · (sinc((ωAM j − 2πx)/2) + sinc((ωAM j + 2πx)/2))/2`. -/
theorem KfunAM_eq_sinc (x : ℝ) :
    KfunAM x = ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
      ((Real.sinc ((ωAM j - 2 * π * x) / 2) + Real.sinc ((ωAM j + 2 * π * x) / 2)) / 2) := by
  unfold KfunAM vAM
  have hpt : ∀ t, (∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.cos (ωAM j * t)) * Real.cos (2 * π * x * t)
      = ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
          ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2) := by
    intro t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpt]
  have hI : ∀ j ∈ Finset.range 13, IntervalIntegrable (fun t => (cAM j : ℝ) *
      ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2))
      volume (-(1:ℝ)/2) (1/2) := fun j _ =>
    (by fun_prop : Continuous fun t => (cAM j : ℝ) *
      ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : IntervalIntegrable (fun t => Real.cos ((ωAM j - 2 * π * x) * t)) volume (-(1:ℝ)/2) (1/2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => Real.cos ((ωAM j + 2 * π * x) * t)) volume (-(1:ℝ)/2) (1/2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add h1 h2, integral_cos_mul_sinc, integral_cos_mul_sinc]

theorem KfunAM_zero_eq_sinc :
    KfunAM 0 = ∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.sinc (ωAM j / 2) := by
  rw [KfunAM_eq_sinc]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-! ## The MT term plus the harmonic correction -/

/-- the Montgomery–Taylor kernel (the `j = 0` term, `c₀ = 1`):
`KMT x = (sinc((√2 − 2πx)/2) + sinc((√2 + 2πx)/2))/2 = ∫_{-½}^{½} cos(√2 t) cos(2πxt) dt`. -/
def KMT (x : ℝ) : ℝ :=
  (Real.sinc ((Real.sqrt 2 - 2 * π * x) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * x) / 2)) / 2

/-- the `j`-th harmonic term (`j = n + 1 ≥ 1`) in sinc form, centred at `±j`. -/
theorem term_sinc (n : ℕ) (x : ℝ) :
    (Real.sinc ((ωAM (n + 1) - 2 * π * x) / 2) + Real.sinc ((ωAM (n + 1) + 2 * π * x) / 2)) / 2
      = (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2 := by
  rw [ωAM_succ]
  have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
  have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
  rw [e1, e2, Real.sinc_neg]

/-- away from the poles: `(sinc(π(x−k)) + sinc(π(x+k)))/2 = (−1)^k x sin(πx)/(π(x² − k²))`, `k = n + 1`. -/
theorem term_closed (n : ℕ) {x : ℝ} (hx : x ^ 2 ≠ ((n : ℝ) + 1) ^ 2) :
    (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2
      = (-1) ^ (n + 1) * x * Real.sin (π * x) / (π * (x ^ 2 - ((n : ℝ) + 1) ^ 2)) := by
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  have h1 : x - ((n : ℝ) + 1) ≠ 0 := by
    intro h; apply hx; rw [show x = (n : ℝ) + 1 by linarith]
  have h2 : x + ((n : ℝ) + 1) ≠ 0 := by
    intro h; apply hx; rw [show x = -((n : ℝ) + 1) by linarith]; ring
  have hd : x ^ 2 - ((n : ℝ) + 1) ^ 2 ≠ 0 := sub_ne_zero.mpr hx
  rw [Real.sinc_of_ne_zero (mul_ne_zero hπ h1), Real.sinc_of_ne_zero (mul_ne_zero hπ h2)]
  have s1 : Real.sin (π * (x - ((n : ℝ) + 1))) = (-1) ^ (n + 1) * Real.sin (π * x) := by
    rw [show π * (x - ((n : ℝ) + 1)) = π * x - ((n + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_sub_nat_mul_pi]
  have s2 : Real.sin (π * (x + ((n : ℝ) + 1))) = (-1) ^ (n + 1) * Real.sin (π * x) := by
    rw [show π * (x + ((n : ℝ) + 1)) = π * x + ((n + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_add_nat_mul_pi]
  rw [s1, s2]
  have hprod : x ^ 2 - ((n : ℝ) + 1) ^ 2 = (x - ((n : ℝ) + 1)) * (x + ((n : ℝ) + 1)) := by ring
  rw [hprod]
  field_simp
  ring

/-- the harmonic correction `x sin(πx)/π · Σ_{j=1}^{12} (−1)^j c_j/(x² − j²)`. -/
def corrAM (x : ℝ) : ℝ :=
  x * Real.sin (π * x) / π *
    ∑ n ∈ Finset.range 12, (-1) ^ (n + 1) * (cAM (n + 1) : ℝ) / (x ^ 2 - ((n : ℝ) + 1) ^ 2)

/-- **closed form away from the poles**: `KfunAM x = KMT x + corrAM x` when `x² ≠ j²`, `j = 1, …, 12`. -/
theorem KfunAM_closed {x : ℝ} (hx : ∀ n : ℕ, n < 12 → x ^ 2 ≠ ((n : ℝ) + 1) ^ 2) :
    KfunAM x = KMT x + corrAM x := by
  rw [KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
  congr 1
  unfold corrAM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [term_sinc, term_closed n (hx n (Finset.mem_range.mp hn))]
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  have hd : x ^ 2 - ((n : ℝ) + 1) ^ 2 ≠ 0 := sub_ne_zero.mpr (hx n (Finset.mem_range.mp hn))
  field_simp

/-- `KfunAM 0 = √2 · sin(√2/2)`. -/
theorem KfunAM_zero_closed : KfunAM 0 = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
  have h0 : ∀ n : ℕ, n < 12 → (0:ℝ) ^ 2 ≠ ((n : ℝ) + 1) ^ 2 := by
    intro n _; have := Nat.cast_nonneg (α := ℝ) n; nlinarith
  rw [KfunAM_closed h0]
  unfold KMT corrAM
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [mul_zero, sub_zero, add_zero, zero_mul, zero_div]
  rw [Real.sinc_of_ne_zero (by positivity)]
  field_simp
  rw [hsq]
  ring

/-- the removable-pole values: `KfunAM j = KMT j + c_j/2`, `j = m + 1 ≤ 12`. -/
theorem KfunAM_at_int {m : ℕ} (hm : m < 12) :
    KfunAM ((m : ℝ) + 1) = KMT ((m : ℝ) + 1) + (cAM (m + 1) : ℝ) / 2 := by
  rw [KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
  congr 1
  have hsincZ : ∀ z : ℤ, z ≠ 0 → Real.sinc (π * z) = 0 := by
    intro z hz
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_pos.ne' (by exact_mod_cast hz)), mul_comm,
      Real.sin_int_mul_pi, zero_div]
  have hterm : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
      ((Real.sinc ((ωAM (n + 1) - 2 * π * ((m : ℝ) + 1)) / 2)
        + Real.sinc ((ωAM (n + 1) + 2 * π * ((m : ℝ) + 1)) / 2)) / 2)
      = if n = m then (cAM (m + 1) : ℝ) / 2 else 0 := by
    intro n _
    rw [term_sinc]
    have e2 : π * ((m : ℝ) + 1 + ((n : ℝ) + 1)) = π * (((m + n + 2 : ℕ) : ℤ) : ℝ) := by push_cast; ring
    rw [e2, hsincZ _ (by positivity)]
    split_ifs with h
    · subst h
      rw [show π * ((n : ℝ) + 1 - ((n : ℝ) + 1)) = 0 by ring, Real.sinc_zero]
      ring
    · have e1 : π * ((m : ℝ) + 1 - ((n : ℝ) + 1)) = π * (((m : ℤ) - n : ℤ) : ℝ) := by push_cast; ring
      rw [e1, hsincZ _ (by omega)]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range 12) m,
    if_pos (Finset.mem_range.mpr hm)]

/-- the record file's MT shape: for `1 − 2(πx)² ≠ 0`,
`KMT x = √2 sin(√2/2) · (cos(πx) − 2γ·πx·sin(πx))/(1 − 2(πx)²)`, `γ = (√2/2) cos(√2/2)/sin(√2/2)`. -/
theorem KMT_eq_gamma {x : ℝ} (h : 1 - 2 * (π * x) ^ 2 ≠ 0) :
    KMT x = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)
      * ((Real.cos (π * x) - 2 * ((Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2))
          * (π * x) * Real.sin (π * x)) / (1 - 2 * (π * x) ^ 2)) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsa : Real.sin (Real.sqrt 2 / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    have : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith [Real.pi_gt_three]
  generalize hb : π * x = b at h ⊢
  have hx2 : 2 * π * x = 2 * b := by rw [← hb]; ring
  have h1 : Real.sqrt 2 / 2 - b ≠ 0 := by
    intro hz; apply h
    have : b = Real.sqrt 2 / 2 := by linarith
    rw [this, div_pow, hsq]; norm_num
  have h2 : Real.sqrt 2 / 2 + b ≠ 0 := by
    intro hz; apply h
    have : b = -(Real.sqrt 2 / 2) := by linarith
    rw [this, neg_sq, div_pow, hsq]; norm_num
  unfold KMT
  rw [hx2, show (Real.sqrt 2 - 2 * b) / 2 = Real.sqrt 2 / 2 - b by ring,
    show (Real.sqrt 2 + 2 * b) / 2 = Real.sqrt 2 / 2 + b by ring,
    Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2, Real.sin_sub, Real.sin_add]
  generalize Real.sin (Real.sqrt 2 / 2) = S at hsa ⊢
  generalize Real.cos (Real.sqrt 2 / 2) = C
  have hprod : (Real.sqrt 2 / 2 - b) * (Real.sqrt 2 / 2 + b) = (1 - 2 * b ^ 2) / 2 := by
    have : (Real.sqrt 2 / 2 - b) * (Real.sqrt 2 / 2 + b) = Real.sqrt 2 ^ 2 / 4 - b ^ 2 := by ring
    rw [this, hsq]; ring
  rw [div_add_div _ _ h1 h2, hprod]
  field_simp
  linear_combination (2 * C * Real.sin b * b) * hsq

theorem sin_sqrt2_half_pos' : 0 < Real.sin (Real.sqrt 2 / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  have : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith [Real.pi_gt_three]

/-- **the normalised kernel in sinc form** (no case split):
`kfunAM x = KMT x/(√2 sin(√2/2)) + ρ·Σ_{n<12} c_{n+1}·(sinc(π(x−(n+1))) + sinc(π(x+(n+1))))/2`,
`ρ = (√2/2)/sin(√2/2)`. -/
theorem kfunAM_eq_sinc_form (x : ℝ) :
    kfunAM x = KMT x / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      + (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
        * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ)
            * ((Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2) := by
  have hs := sin_sqrt2_half_pos'
  have hr : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold kfunAM
  rw [KfunAM_zero_closed, KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
  have hS : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
        ((Real.sinc ((ωAM (n + 1) - 2 * π * x) / 2) + Real.sinc ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
      = ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ)
          * ((Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2) :=
    Finset.sum_congr rfl fun n _ => by rw [term_sinc]
  rw [hS]
  generalize ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ)
      * ((Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2) = S
  unfold KMT
  generalize (Real.sinc ((Real.sqrt 2 - 2 * π * x) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = K
  generalize Real.sin (Real.sqrt 2 / 2) = s at hs ⊢
  field_simp
  linear_combination (-S) * hsq

/-- the MT part, normalised, is exactly the record file's closed form:
`KMT x/(√2 sin(√2/2)) = (cos(πx) − 2γ·πx·sin(πx))/(1 − 2(πx)²)` when `1 − 2(πx)² ≠ 0`. -/
theorem KMT_div_eq {x : ℝ} (h : 1 - 2 * (π * x) ^ 2 ≠ 0) :
    KMT x / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      = (Real.cos (π * x) - 2 * ((Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2))
          * (π * x) * Real.sin (π * x)) / (1 - 2 * (π * x) ^ 2) := by
  have hs := sin_sqrt2_half_pos'
  have hr : (0:ℝ) < Real.sqrt 2 := by positivity
  have hne : Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) ≠ 0 := by positivity
  rw [KMT_eq_gamma h, mul_div_cancel_left₀ _ hne]

end AMW
