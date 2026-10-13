import AMW.Swap

/-!
# AMW/Constant — the constant of the AMTOPA window in closed form (stage E3)

With `θ₀ = √2/2`, `d n = cAM (n+1)`, `k n = n + 1`:
* `∫_{-½}^{½} |s − t| cos(ωt) dt = sin(ω/2)/ω + 2cos(ω/2)/ω² − 2cos(ωs)/ω²` on `[-½, ½]` (`ω ≠ 0`);
* hence `vAM + K = βv + rv` on `[-½,½]` (`K(s) = ∫|s−t| vAM(t) dt`): the `cos(√2·)` terms cancel, because
  `cos(√2·)` is the optimiser of the functional (`2/ω₀² = 1`);
* `∫ vAM = √2 sin θ₀`, `∫ vAM·cos(2πk·) = X_k + d_k/2`, `X_k = ∫ cos(√2·)cos(2πk·)`;
* the cross terms cancel (`(1 − 1/(2π²k²))X_k + (−1)^k √2 sin θ₀/(2π²k²) = 0`), leaving
  **`H_W = 3/2 − cos θ₀/(√2 sin θ₀) − PAM/(2 sin² θ₀)`**, `PAM = Σ_k d_k²(½ − 1/(4π²k²))`,
  where `H_W := 2 − (cRatio 1 aInf bInf JInf)⁻¹`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace AMW

open Zeta23

/-! ## Elementary integrals on `[-1/2, 1/2]` -/

theorem integral_cos_half {c : ℝ} (hc : c ≠ 0) :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (c * t) = 2 * Real.sin (c / 2) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos, smul_eq_mul,
    show c * (1/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring, Real.sin_neg]
  field_simp
  ring

theorem cos_mul_cos_eq (a b t : ℝ) :
    Real.cos (a * t) * Real.cos (b * t) = (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2 := by
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring

theorem cos_lin_intervalIntegrable (c : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t)) volume (-(1:ℝ)/2) (1/2) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem integral_cos_cos {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (a * t) * Real.cos (b * t)
      = Real.sin ((a - b) / 2) / (a - b) + Real.sin ((a + b) / 2) / (a + b) := by
  simp_rw [cos_mul_cos_eq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (cos_lin_intervalIntegrable _)
    (cos_lin_intervalIntegrable _), integral_cos_half h1, integral_cos_half h2]
  field_simp

/-- `k n = n + 1` as a real, and the frequency `2π k`. -/
theorem two_pi_k_pos (n : ℕ) : 0 < 2 * π * ((n : ℝ) + 1) := by positivity

theorem integral_cos_k (n : ℕ) :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * ((n : ℝ) + 1) * t) = 0 := by
  rw [integral_cos_half (two_pi_k_pos n).ne']
  have : 2 * π * ((n : ℝ) + 1) / 2 = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  rw [this, Real.sin_nat_mul_pi]; simp

theorem integral_cos_sqrt2 :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (Real.sqrt 2 * t) = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [integral_cos_half hs.ne']
  field_simp
  rw [hsq]

theorem integral_cos_k_cos_k (m n : ℕ) :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * ((m : ℝ) + 1) * t) * Real.cos (2 * π * ((n : ℝ) + 1) * t)
      = if m = n then 1 / 2 else 0 := by
  split_ifs with h
  · subst h
    simp_rw [cos_mul_cos_eq, sub_self, zero_mul, Real.cos_zero]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
      (cos_lin_intervalIntegrable _), intervalIntegral.integral_const]
    have hc : 2 * π * ((m : ℝ) + 1) + 2 * π * ((m : ℝ) + 1) ≠ 0 := by
      have := two_pi_k_pos m; linarith
    rw [integral_cos_half hc]
    have : (2 * π * ((m : ℝ) + 1) + 2 * π * ((m : ℝ) + 1)) / 2 = ((2 * m + 2 : ℕ) : ℝ) * π := by
      push_cast; ring
    rw [this, Real.sin_nat_mul_pi]
    norm_num
  · have h1 : 2 * π * ((m : ℝ) + 1) - 2 * π * ((n : ℝ) + 1) ≠ 0 := by
      have hmn : (m : ℝ) ≠ n := by exact_mod_cast h
      intro h0
      apply hmn
      have hπ := Real.pi_pos
      have : 2 * π * ((m : ℝ) - n) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    have h2 : 2 * π * ((m : ℝ) + 1) + 2 * π * ((n : ℝ) + 1) ≠ 0 := by
      have := two_pi_k_pos m; have := two_pi_k_pos n; linarith
    rw [integral_cos_cos h1 h2]
    have e1 : (2 * π * ((m : ℝ) + 1) - 2 * π * ((n : ℝ) + 1)) / 2 = (((m : ℤ) - n : ℤ) : ℝ) * π := by
      push_cast; ring
    have e2 : (2 * π * ((m : ℝ) + 1) + 2 * π * ((n : ℝ) + 1)) / 2 = ((m + n + 2 : ℕ) : ℝ) * π := by
      push_cast; ring
    rw [e1, e2, Real.sin_int_mul_pi, Real.sin_nat_mul_pi]
    simp

/-- `X_k = ∫ cos(√2 t) cos(2πk t) dt = (−1)^k sin θ₀ · 2√2/(2 − 4π²k²)`. -/
def Xk (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) * Real.sin (Real.sqrt 2 / 2) * (2 * Real.sqrt 2) / (2 - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)

theorem two_sub_ne (n : ℕ) : (2 : ℝ) - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 ≠ 0 := by
  have hπ := Real.pi_gt_three
  have hn : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith
  have : (9:ℝ) ≤ π ^ 2 := by nlinarith
  nlinarith

theorem integral_cos_sqrt2_cos_k (n : ℕ) :
    ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * π * ((n : ℝ) + 1) * t) = Xk n := by
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk := two_pi_k_pos n
  have hπ := Real.pi_gt_three
  have h2 : Real.sqrt 2 + 2 * π * ((n : ℝ) + 1) ≠ 0 := by linarith
  have h1 : Real.sqrt 2 - 2 * π * ((n : ℝ) + 1) ≠ 0 := by
    have hs2 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have : (2:ℝ) * π * 1 ≤ 2 * π * ((n : ℝ) + 1) := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    linarith
  rw [integral_cos_cos h1 h2]
  have e1 : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) / 2 = Real.sqrt 2 / 2 - ((n + 1 : ℕ) : ℝ) * π := by
    push_cast; ring
  have e2 : (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1)) / 2 = Real.sqrt 2 / 2 + ((n + 1 : ℕ) : ℝ) * π := by
    push_cast; ring
  rw [e1, e2, Real.sin_sub_nat_mul_pi, Real.sin_add_nat_mul_pi]
  unfold Xk
  have hd := two_sub_ne n
  have hprod : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) * (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1))
      = 2 - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    have e : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) * (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1))
        = Real.sqrt 2 ^ 2 - (2 * π * ((n : ℝ) + 1)) ^ 2 := by ring
    rw [e, hsq]; ring
  rw [div_add_div _ _ h1 h2, hprod]
  congr 1
  ring

/-! ## The kernel identity -/

private theorem hasDerivAt_left' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (s - x) * Real.sin (ω * x) / ω - Real.cos (ω * x) / ω ^ 2)
      ((s - x) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).sub (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

private theorem hasDerivAt_right' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (x - s) * Real.sin (ω * x) / ω + Real.cos (ω * x) / ω ^ 2)
      ((x - s) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
    simpa using (hasDerivAt_id x).sub_const s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).add (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

/-- **kernel identity**: on `[-1/2, 1/2]`,
`∫ |s − t| cos(ωt) dt = sin(ω/2)/ω + 2cos(ω/2)/ω² − 2cos(ωs)/ω²`. -/
theorem kernel_cos {ω s : ℝ} (hω : ω ≠ 0) (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
    ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * Real.cos (ω * t)
      = Real.sin (ω / 2) / ω + 2 * Real.cos (ω / 2) / ω ^ 2 - 2 * Real.cos (ω * s) / ω ^ 2 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable
      (fun t => |s - t| * Real.cos (ω * t)) MeasureTheory.volume a b := fun a b =>
    (Continuous.intervalIntegrable (by fun_prop) a b)
  have hsplit : ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * Real.cos (ω * t)
      = (∫ t in (-(1:ℝ)/2)..s, |s - t| * Real.cos (ω * t))
        + ∫ t in s..(1/2), |s - t| * Real.cos (ω * t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  have hleft : ∫ t in (-(1:ℝ)/2)..s, |s - t| * Real.cos (ω * t)
      = ∫ t in (-(1:ℝ)/2)..s, (s - t) * Real.cos (ω * t) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs1] at hx
    show |s - x| * Real.cos (ω * x) = (s - x) * Real.cos (ω * x)
    rw [abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ s - x)]
  have hleft2 : ∫ t in (-(1:ℝ)/2)..s, (s - t) * Real.cos (ω * t)
      = ((s - s) * Real.sin (ω * s) / ω - Real.cos (ω * s) / ω ^ 2)
        - ((s - (-(1:ℝ)/2)) * Real.sin (ω * (-(1:ℝ)/2)) / ω - Real.cos (ω * (-(1:ℝ)/2)) / ω ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_left' ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hright : ∫ t in s..(1/2), |s - t| * Real.cos (ω * t)
      = ∫ t in s..(1/2), (t - s) * Real.cos (ω * t) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs2] at hx
    show |s - x| * Real.cos (ω * x) = (x - s) * Real.cos (ω * x)
    rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
  have hright2 : ∫ t in s..(1/2), (t - s) * Real.cos (ω * t)
      = (((1:ℝ)/2 - s) * Real.sin (ω * (1/2)) / ω + Real.cos (ω * (1/2)) / ω ^ 2)
        - ((s - s) * Real.sin (ω * s) / ω + Real.cos (ω * s) / ω ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_right' ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hsplit, hleft, hleft2, hright, hright2,
    show ω * (1/2) = ω / 2 by ring, show ω * (-(1:ℝ)/2) = -(ω / 2) by ring, Real.sin_neg, Real.cos_neg]
  field_simp
  ring

/-! ## The profile as `cos(√2·) + Σ d_n cos(2π(n+1)·)` -/

/-- `d n = cAM (n+1)`. -/
def dAM (n : ℕ) : ℝ := (cAM (n + 1) : ℝ)

/-- the `n`-th harmonic `cos(2π(n+1)t)`. -/
def ek (n : ℕ) (t : ℝ) : ℝ := Real.cos (2 * π * ((n : ℝ) + 1) * t)

theorem ek_continuous (n : ℕ) : Continuous (ek n) := by unfold ek; fun_prop

theorem vAM_eq' (t : ℝ) :
    vAM t = Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range 12, dAM n * ek n t := by
  rw [vAM_eq]
  unfold pAM dAM ek
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ωAM_succ]

/-- the inner kernel of the profile, on `[-1/2, 1/2]`. -/
theorem kernel_vAM {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
    ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t
      = (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2) - Real.cos (Real.sqrt 2 * s))
        + ∑ n ∈ Finset.range 12,
            dAM n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ t, |s - t| * vAM t
      = |s - t| * Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range 12, dAM n * (|s - t| * ek n t) := by
    intro t
    rw [vAM_eq', mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hpt]
  have hI0 : IntervalIntegrable (fun t => |s - t| * Real.cos (Real.sqrt 2 * t)) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun t => |s - t| * Real.cos (Real.sqrt 2 * t)).intervalIntegrable _ _
  have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * (|s - t| * ek n t))
      volume (-(1:ℝ)/2) (1/2) := fun n _ =>
    ((continuous_const.mul ((continuous_const.sub continuous_id).abs.mul (ek_continuous n)))).intervalIntegrable _ _
  have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * (|s - t| * ek n t))
      volume (-(1:ℝ)/2) (1/2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul
      ((continuous_const.sub continuous_id).abs.mul (ek_continuous n))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hI0 hS,
    intervalIntegral.integral_finsetSum hIn, kernel_cos hs.ne' hs1 hs2, hsq]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    congr 1
    unfold ek
    rw [kernel_cos (two_pi_k_pos n).ne' hs1 hs2]
    have e1 : 2 * π * ((n : ℝ) + 1) / 2 = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
    rw [e1, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    have hk := two_pi_k_pos n
    have hπ := Real.pi_pos
    field_simp
    ring

/-- `βv`: the constant part of `vAM + K`. -/
def betaV : ℝ :=
  Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2)
    + ∑ n ∈ Finset.range 12, dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))

/-- `rv`: the oscillating part of `vAM + K` (no `cos(√2·)` term). -/
def rV (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 12, dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s

theorem rV_continuous : Continuous rV := by
  unfold rV
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)

/-- **`vAM + K = βv + rv`** on `[-1/2, 1/2]` (the `cos(√2·)` terms cancel). -/
theorem vAM_add_kernel {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
    vAM s + ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t = betaV + rV s := by
  rw [kernel_vAM hs1 hs2, vAM_eq']
  unfold betaV rV
  have e : ∀ n ∈ Finset.range 12, dAM n * ek n s
      + dAM n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
      = dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
        + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s := by
    intro n _
    have hk := two_pi_k_pos n
    have hπ := Real.pi_pos
    field_simp
    ring
  have hsum := Finset.sum_congr rfl e
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

/-! ## The integrals of the profile against the harmonics -/

theorem integral_vAM :
    ∫ t in (-(1:ℝ)/2)..(1/2), vAM t = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
  simp_rw [vAM_eq']
  have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * ek n t)
      volume (-(1:ℝ)/2) (1/2) := fun n _ =>
    (continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
  have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * ek n t)
      volume (-(1:ℝ)/2) (1/2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (cos_lin_intervalIntegrable _) hS,
    intervalIntegral.integral_finsetSum hIn, integral_cos_sqrt2]
  have h0 : ∀ n ∈ Finset.range 12, ∫ t in (-(1:ℝ)/2)..(1/2), dAM n * ek n t = 0 := by
    intro n _
    rw [intervalIntegral.integral_const_mul]
    unfold ek
    rw [integral_cos_k, mul_zero]
  rw [Finset.sum_eq_zero h0, add_zero]

theorem integral_vAM_ek {m : ℕ} (hm : m ∈ Finset.range 12) :
    ∫ t in (-(1:ℝ)/2)..(1/2), vAM t * ek m t = Xk m + dAM m / 2 := by
  have hpt : ∀ t, vAM t * ek m t
      = Real.cos (Real.sqrt 2 * t) * ek m t + ∑ n ∈ Finset.range 12, dAM n * (ek n t * ek m t) := by
    intro t
    rw [vAM_eq', add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hpt]
  have hI0 : IntervalIntegrable (fun t => Real.cos (Real.sqrt 2 * t) * ek m t) volume (-(1:ℝ)/2) (1/2) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul (ek_continuous m)).intervalIntegrable _ _
  have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * (ek n t * ek m t))
      volume (-(1:ℝ)/2) (1/2) := fun n _ =>
    (continuous_const.mul ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
  have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * (ek n t * ek m t))
      volume (-(1:ℝ)/2) (1/2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul
      ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hI0 hS, intervalIntegral.integral_finsetSum hIn]
  unfold ek
  rw [integral_cos_sqrt2_cos_k]
  congr 1
  have h : ∀ n ∈ Finset.range 12, ∫ t in (-(1:ℝ)/2)..(1/2),
      dAM n * (Real.cos (2 * π * ((n : ℝ) + 1) * t) * Real.cos (2 * π * ((m : ℝ) + 1) * t))
      = if n = m then dAM n / 2 else 0 := by
    intro n _
    rw [intervalIntegral.integral_const_mul, integral_cos_k_cos_k]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range 12) m (fun n => dAM n / 2), if_pos hm]

/-- the Euler–Lagrange cancellation of the cross terms. -/
theorem euler_lagrange (n : ℕ) :
    (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * Xk n
      + (-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) = 0 := by
  unfold Xk
  have hd := two_sub_ne n
  have hD : (2:ℝ) - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 = 2 * (1 - 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) := by ring
  rw [hD] at hd ⊢
  set E : ℝ := 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 with hEdef
  have hE : 0 < E := by rw [hEdef]; positivity
  have h1E : 1 - E ≠ 0 := fun h => hd (by rw [h]; ring)
  field_simp
  ring

/-! ## The constant -/

/-- `PAM = Σ_n d_n² (1/2 − 1/(4π²(n+1)²))`. -/
def PAM : ℝ := ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))

/-- `∫ v² + ∫ v·K = sin²θ₀ + √2 sin θ₀ cos θ₀ + PAM`. -/
theorem energy_total :
    (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2)
      + (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t)
      = Real.sin (Real.sqrt 2 / 2) ^ 2
        + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) + PAM := by
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- replace the kernel by βv + rv − vAM on the window
  have hK : ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t
      = ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * (betaV + rV s - vAM s) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [Set.uIcc_of_le (by norm_num)] at hs'
    have := vAM_add_kernel hs'.1 hs'.2
    show vAM s * _ = vAM s * (betaV + rV s - vAM s)
    congr 1
    linarith
  have hA : IntervalIntegrable (fun t => vAM t ^ 2) volume (-(1:ℝ)/2) (1/2) :=
    (vAM_continuous.pow 2).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun s => vAM s * (betaV + rV s - vAM s)) volume (-(1:ℝ)/2) (1/2) :=
    (vAM_continuous.mul ((continuous_const.add rV_continuous).sub vAM_continuous)).intervalIntegrable _ _
  rw [hK, ← intervalIntegral.integral_add hA hB]
  have hpt : ∀ s, vAM s ^ 2 + vAM s * (betaV + rV s - vAM s)
      = betaV * vAM s + ∑ n ∈ Finset.range 12,
          dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s) := by
    intro s
    have alg : ∀ a b S : ℝ, a ^ 2 + a * (b + S - a) = b * a + a * S := fun a b S => by ring
    rw [alg, rV, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hpt]
  have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable
      (fun s => dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s))
      volume (-(1:ℝ)/2) (1/2) := fun n _ =>
    (continuous_const.mul (vAM_continuous.mul (ek_continuous n))).intervalIntegrable _ _
  have hS : IntervalIntegrable (fun s => ∑ n ∈ Finset.range 12,
      dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s)) volume (-(1:ℝ)/2) (1/2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul
      (vAM_continuous.mul (ek_continuous n))).intervalIntegrable _ _
  have hC : IntervalIntegrable (fun s => betaV * vAM s) volume (-(1:ℝ)/2) (1/2) :=
    (continuous_const.mul vAM_continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hC hS,
    intervalIntegral.integral_finsetSum hIn, intervalIntegral.integral_const_mul, integral_vAM]
  have hterm : ∀ n ∈ Finset.range 12,
      ∫ s in (-(1:ℝ)/2)..(1/2), dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s)
        = dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2) := by
    intro n hn
    rw [intervalIntegral.integral_const_mul, integral_vAM_ek hn]
  rw [Finset.sum_congr rfl hterm]
  -- assemble with the Euler–Lagrange cancellation
  unfold betaV PAM
  have hEL : ∀ n ∈ Finset.range 12,
      dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
        + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2)
      = dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
    intro n _
    have h := euler_lagrange n
    have hk2 : (0:ℝ) < 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
    have e : dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
        + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2)
        = dAM n * ((1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * Xk n
            + (-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)))
          + dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
      field_simp
      ring
    rw [e, h, mul_zero, zero_add]
  have hsum := Finset.sum_congr rfl hEL
  rw [Finset.sum_add_distrib] at hsum
  rw [add_mul, Finset.sum_mul]
  have e2 : (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2))
        * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      = Real.sin (Real.sqrt 2 / 2) ^ 2 + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) := by
    field_simp
  rw [e2]
  linarith

/-- the Theorem-D constant of the AMTOPA window. -/
def HW : ℝ := 2 - (ThmD.cRatio 1 aInf bInf JInf)⁻¹

theorem sin_theta0_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith [Real.pi_gt_three]

/-- **`H_W = 3/2 − cos θ₀/(√2 sin θ₀) − PAM/(2 sin² θ₀)`**, `θ₀ = √2/2`. -/
theorem HW_eq :
    HW = 3 / 2 - Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      - PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) := by
  have hs : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsin := sin_theta0_pos
  have hM := MAM_pos
  have hJ := JInf_eq_energy
  have hE := energy_total
  have hb : bInf = (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2) / MAM ^ 2 := by
    unfold bInf
    rw [← intervalIntegral.integral_div]
    congr 1; funext t; ring
  have ha : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
    unfold aInf; rw [integral_vAM]
  have hJ' : JInf = (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t) / MAM ^ 2 := by
    rw [← hJ]; field_simp
  unfold HW ThmD.cRatio
  rw [hb, ha, hJ']
  have hden : (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2) / MAM ^ 2 + 1 ^ 2
      * ((∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t) / MAM ^ 2)
      = (Real.sin (Real.sqrt 2 / 2) ^ 2
        + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) + PAM) / MAM ^ 2 := by
    rw [← hE]; ring
  rw [hden]
  generalize Real.sin (Real.sqrt 2 / 2) = S at hsin ⊢
  generalize Real.cos (Real.sqrt 2 / 2) = C
  have key : (1 * (Real.sqrt 2 * S / MAM) ^ 2 / ((S ^ 2 + Real.sqrt 2 * S * C + PAM) / MAM ^ 2))⁻¹
      = (S ^ 2 + Real.sqrt 2 * S * C + PAM) / (2 * S ^ 2) := by
    rw [div_pow, mul_pow, hsq, inv_div]
    field_simp
  have hcs : C / (Real.sqrt 2 * S) = Real.sqrt 2 * C / (2 * S) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-(C * S)) * hsq
  rw [key, hcs]
  field_simp
  ring

end AMW
