import AMW.Kernel

/-!
# AMW/GSinc — the derivatives of `sinc` and of the AM pair kernel (stage G)

`sinc' = sc1`, `sc1' = sc2` everywhere, with
  `sc1 θ = (θ cos θ − sin θ)/θ²` (`0` at `0`),  `sc2 θ = (−θ² sin θ − 2θ cos θ + 2 sin θ)/θ³` (`−1/3` at `0`).
At `θ = 0` the derivatives come from the Taylor bounds `Real.sin_bound`, `Real.cos_bound`.
Hence, from the closed form `KfunAM_eq_sinc`, `KfunAM` is twice differentiable everywhere with
  `KfunAM' = K1AM`, `K1AM' = K2AM` (sums over the 13 window terms), and so are `kfunAM`, `wfunAM`.
-/

noncomputable section

open Real Filter Topology Asymptotics

namespace AMW

/-- `sinc'` -/
def sc1 (θ : ℝ) : ℝ := if θ = 0 then 0 else (θ * Real.cos θ - Real.sin θ) / θ ^ 2

/-- `sinc''` -/
def sc2 (θ : ℝ) : ℝ := if θ = 0 then -1 / 3 else (-θ ^ 2 * Real.sin θ - 2 * θ * Real.cos θ + 2 * Real.sin θ) / θ ^ 3

theorem hasDerivAt_sinc_of_ne {θ : ℝ} (h : θ ≠ 0) : HasDerivAt Real.sinc (sc1 θ) θ := by
  have hev : Real.sinc =ᶠ[𝓝 θ] fun t => Real.sin t / t := by
    filter_upwards [isOpen_ne.mem_nhds h] with t ht
    rw [Real.sinc_of_ne_zero ht]
  have hd := (Real.hasDerivAt_sin θ).div (hasDerivAt_id θ) h
  rw [sc1, if_neg h]
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [id]
  ring

/-- `|sin h − h| ≤ |h|³` for `|h| ≤ 1` -/
theorem abs_sin_sub_self_le {h : ℝ} (hh : |h| ≤ 1) : |Real.sin h - h| ≤ |h| ^ 3 := by
  have hb := Real.sin_bound hh
  have h0 := abs_nonneg h
  have e : Real.sin h - h = (Real.sin h - (h - h ^ 3 / 6)) - h ^ 3 / 6 := by ring
  rw [e]
  have h3 : |h ^ 3 / 6| = |h| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have h5 : |h| ^ 5 ≤ |h| ^ 3 := by
    calc |h| ^ 5 = |h| ^ 3 * (|h| * |h|) := by ring
      _ ≤ |h| ^ 3 * (1 * 1) := by gcongr
      _ = |h| ^ 3 := by ring
  calc |Real.sin h - (h - h ^ 3 / 6) - h ^ 3 / 6| ≤ |Real.sin h - (h - h ^ 3 / 6)| + |h ^ 3 / 6| := abs_sub _ _
    _ ≤ |h| ^ 5 / 100 + |h| ^ 3 / 6 := by rw [h3]; linarith
    _ ≤ |h| ^ 3 := by nlinarith [pow_nonneg h0 3]

theorem abs_sinc_sub_one_le {h : ℝ} (hh : |h| ≤ 1) : |Real.sinc h - 1| ≤ h ^ 2 := by
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  rw [Real.sinc_of_ne_zero h0]
  have hp : 0 < |h| := abs_pos.mpr h0
  have e : Real.sin h / h - 1 = (Real.sin h - h) / h := by field_simp
  rw [e, abs_div, div_le_iff₀ hp]
  have := abs_sin_sub_self_le hh
  calc |Real.sin h - h| ≤ |h| ^ 3 := this
    _ = h ^ 2 * |h| := by rw [← sq_abs h]; ring

theorem hasDerivAt_sinc_zero : HasDerivAt Real.sinc 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h : ℝ => Real.sinc (0 + h) - Real.sinc 0 - h • (0 : ℝ)) =O[𝓝 0] fun h => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    simp only [zero_add, Real.sinc_zero, smul_zero, sub_zero, Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (sq_nonneg h)]
    exact abs_sinc_sub_one_le hh.le
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

theorem hasDerivAt_sinc (θ : ℝ) : HasDerivAt Real.sinc (sc1 θ) θ := by
  rcases eq_or_ne θ 0 with rfl | h
  · have : sc1 0 = 0 := by simp [sc1]
    rw [this]; exact hasDerivAt_sinc_zero
  · exact hasDerivAt_sinc_of_ne h

theorem hasDerivAt_sc1_of_ne {θ : ℝ} (h : θ ≠ 0) : HasDerivAt sc1 (sc2 θ) θ := by
  have hev : sc1 =ᶠ[𝓝 θ] fun t => (t * Real.cos t - Real.sin t) / t ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds h] with t ht
    rw [sc1, if_neg ht]
  have hn : HasDerivAt (fun t => t * Real.cos t - Real.sin t) (1 * Real.cos θ + θ * (-Real.sin θ) - Real.cos θ) θ :=
    ((hasDerivAt_id θ).mul (Real.hasDerivAt_cos θ)).sub (Real.hasDerivAt_sin θ)
  have hd : HasDerivAt (fun t : ℝ => t ^ 2) (((2 : ℕ) : ℝ) * θ ^ (2 - 1)) θ := hasDerivAt_pow 2 θ
  have hq := hn.div hd (pow_ne_zero 2 h)
  rw [sc2, if_neg h]
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp
  ring

/-- `|θ cos θ − sin θ + θ³/3| ≤ |θ|⁴ / 8` for `|θ| ≤ 1` -/
theorem abs_sc1_num_le {h : ℝ} (hh : |h| ≤ 1) : |h * Real.cos h - Real.sin h + h ^ 3 / 3| ≤ |h| ^ 4 / 8 := by
  have hc := Real.cos_bound hh
  have hs := Real.sin_bound hh
  have h0 := abs_nonneg h
  have e : h * Real.cos h - Real.sin h + h ^ 3 / 3
      = h * (Real.cos h - (1 - h ^ 2 / 2)) - (Real.sin h - (h - h ^ 3 / 6)) := by ring
  rw [e]
  have h5 : |h| ^ 5 ≤ |h| ^ 4 := by
    calc |h| ^ 5 = |h| ^ 4 * |h| := by ring
      _ ≤ |h| ^ 4 * 1 := by gcongr
      _ = |h| ^ 4 := by ring
  calc |h * (Real.cos h - (1 - h ^ 2 / 2)) - (Real.sin h - (h - h ^ 3 / 6))|
      ≤ |h * (Real.cos h - (1 - h ^ 2 / 2))| + |Real.sin h - (h - h ^ 3 / 6)| := abs_sub _ _
    _ = |h| * |Real.cos h - (1 - h ^ 2 / 2)| + |Real.sin h - (h - h ^ 3 / 6)| := by rw [abs_mul]
    _ ≤ |h| * (|h| ^ 4 * (5 / 96)) + |h| ^ 5 / 100 := by gcongr
    _ ≤ |h| ^ 4 / 8 := by nlinarith [pow_nonneg h0 4]

theorem hasDerivAt_sc1_zero : HasDerivAt sc1 (-1 / 3) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h : ℝ => sc1 (0 + h) - sc1 0 - h • (-1 / 3 : ℝ)) =O[𝓝 0] fun h => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    simp only [zero_add, smul_eq_mul, Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (sq_nonneg h)]
    have hs0 : sc1 0 = 0 := by simp [sc1]
    rw [hs0]
    rcases eq_or_ne h 0 with rfl | h0
    · simp [sc1]
    rw [sc1, if_neg h0]
    have hp : 0 < h ^ 2 := by positivity
    have e : (h * Real.cos h - Real.sin h) / h ^ 2 - 0 - h * (-1 / 3)
        = (h * Real.cos h - Real.sin h + h ^ 3 / 3) / h ^ 2 := by field_simp; ring
    rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have := abs_sc1_num_le hh.le
    have hq : |h| ^ 4 = h ^ 2 * h ^ 2 := by rw [← sq_abs h]; ring
    have hh2 : h ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg h]
    nlinarith [sq_nonneg h]
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

theorem hasDerivAt_sc1 (θ : ℝ) : HasDerivAt sc1 (sc2 θ) θ := by
  rcases eq_or_ne θ 0 with rfl | h
  · have : sc2 0 = -1 / 3 := by simp [sc2]
    rw [this]; exact hasDerivAt_sc1_zero
  · exact hasDerivAt_sc1_of_ne h

/-! ## The derivatives of the pair kernel -/

/-- `KfunAM'` -/
def K1AM (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
    ((-(π * sc1 ((ωAM j - 2 * π * x) / 2)) + π * sc1 ((ωAM j + 2 * π * x) / 2)) / 2)

/-- `KfunAM''` -/
def K2AM (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
    ((π ^ 2 * sc2 ((ωAM j - 2 * π * x) / 2) + π ^ 2 * sc2 ((ωAM j + 2 * π * x) / 2)) / 2)

theorem hasDerivAt_lin_m (w x : ℝ) : HasDerivAt (fun y : ℝ => (w - 2 * π * y) / 2) (-π) x := by
  have := ((hasDerivAt_id x).const_mul (2 * π)).const_sub w |>.div_const 2
  simpa using this.congr_deriv (by ring)

theorem hasDerivAt_lin_p (w x : ℝ) : HasDerivAt (fun y : ℝ => (w + 2 * π * y) / 2) π x := by
  have := ((hasDerivAt_id x).const_mul (2 * π)).const_add w |>.div_const 2
  simpa using this.congr_deriv (by ring)

theorem hasDerivAt_KfunAM (x : ℝ) : HasDerivAt KfunAM (K1AM x) x := by
  have hK : KfunAM = fun y => ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
      ((Real.sinc ((ωAM j - 2 * π * y) / 2) + Real.sinc ((ωAM j + 2 * π * y) / 2)) / 2) :=
    funext KfunAM_eq_sinc
  rw [hK, K1AM]
  apply HasDerivAt.fun_sum
  intro j _
  have h1 := (hasDerivAt_sinc ((ωAM j - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (ωAM j) x)
  have h2 := (hasDerivAt_sinc ((ωAM j + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (ωAM j) x)
  exact ((h1.add h2).div_const 2).const_mul _ |>.congr_deriv (by ring)

theorem hasDerivAt_K1AM (x : ℝ) : HasDerivAt K1AM (K2AM x) x := by
  rw [show K1AM = fun y => ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
      ((-(π * sc1 ((ωAM j - 2 * π * y) / 2)) + π * sc1 ((ωAM j + 2 * π * y) / 2)) / 2) from rfl, K2AM]
  apply HasDerivAt.fun_sum
  intro j _
  have h1 := (hasDerivAt_sc1 ((ωAM j - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (ωAM j) x)
  have h2 := (hasDerivAt_sc1 ((ωAM j + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (ωAM j) x)
  exact ((((h1.const_mul π).neg).add (h2.const_mul π)).div_const 2).const_mul _ |>.congr_deriv (by ring)

/-- `kfunAM' = k1AM`, `k1AM' = k2AM`, `wfunAM' = w1AM`, `w1AM' = w2AM` -/
def k1AM (x : ℝ) : ℝ := K1AM x / KfunAM 0
def k2AM (x : ℝ) : ℝ := K2AM x / KfunAM 0
def w1AM (x : ℝ) : ℝ := 2 * kfunAM x * k1AM x
def w2AM (x : ℝ) : ℝ := 2 * (k1AM x ^ 2 + kfunAM x * k2AM x)

theorem hasDerivAt_kfunAM (x : ℝ) : HasDerivAt kfunAM (k1AM x) x :=
  (hasDerivAt_KfunAM x).div_const _

theorem hasDerivAt_k1AM (x : ℝ) : HasDerivAt k1AM (k2AM x) x :=
  (hasDerivAt_K1AM x).div_const _

theorem hasDerivAt_wfunAM (x : ℝ) : HasDerivAt wfunAM (w1AM x) x := by
  have h := (hasDerivAt_kfunAM x).pow 2
  refine h.congr_deriv ?_
  simp only [w1AM]; push_cast; ring

theorem hasDerivAt_w1AM (x : ℝ) : HasDerivAt w1AM (w2AM x) x := by
  have h := ((hasDerivAt_kfunAM x).const_mul 2).mul (hasDerivAt_k1AM x)
  refine (h.congr_deriv ?_ : HasDerivAt (fun y => 2 * kfunAM y * k1AM y) _ x)
  simp only [w2AM]; ring

end AMW
