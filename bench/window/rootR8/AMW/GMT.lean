import AMW.GSinc

/-!
# AMW/GMT — the closed forms of the AM kernel and of its first two derivatives (stage G)

With `b = πx`, `γ = (√2/2) cos(√2/2)/sin(√2/2)`, `ρ = 1/(√2 sin(√2/2))`:
  `kfunAM x = N/D + ρ Σ_{j=1}^{12} c_j T_j(x)`,
  `k1AM x  = π M/D² + ρ π Σ c_j T1_j(x)`,
  `k2AM x  = π² P/D³ + ρ π² Σ c_j T2_j(x)`   (where `D = 1 − 2b² ≠ 0`),
with `N = cos b − 2γ b sin b`, `Nb = −(1+2γ) sin b − 2γ b cos b`, `M = Nb D + 4bN`,
`N₂ = −(1+4γ) cos b + 2γ b sin b`, `P = N₂ D² + 4ND + 8bM`, and
`T_j = (sinc(π(x−j)) + sinc(π(x+j)))/2`, `T1_j`, `T2_j` the same with `sc1`, `sc2`.
The Montgomery–Taylor parts come from `KMT_eq_gamma` and uniqueness of derivatives on `{D ≠ 0}`.
-/

noncomputable section

open Real Filter Topology

namespace AMW

def gamAM : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
def mN (x : ℝ) : ℝ := Real.cos (π * x) - 2 * gamAM * (π * x) * Real.sin (π * x)
def mD (x : ℝ) : ℝ := 1 - 2 * (π * x) ^ 2
def mNb (x : ℝ) : ℝ := -(1 + 2 * gamAM) * Real.sin (π * x) - 2 * gamAM * (π * x) * Real.cos (π * x)
def mM (x : ℝ) : ℝ := mNb x * mD x + 4 * (π * x) * mN x
def mN2 (x : ℝ) : ℝ := -(1 + 4 * gamAM) * Real.cos (π * x) + 2 * gamAM * (π * x) * Real.sin (π * x)
def mP (x : ℝ) : ℝ := mN2 x * mD x ^ 2 + 4 * mN x * mD x + 8 * (π * x) * mM x

/-- `K(0) = √2 sin(√2/2)` -/
def K0AM : ℝ := Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)

theorem K0AM_eq : KfunAM 0 = K0AM := KfunAM_zero_closed

theorem K0AM_pos : 0 < K0AM := by rw [← K0AM_eq]; exact KfunAM_zero_pos

theorem hasDerivAt_pix (x : ℝ) : HasDerivAt (fun y : ℝ => π * y) π x := by
  simpa using (hasDerivAt_id x).const_mul π

theorem hasDerivAt_mN (x : ℝ) : HasDerivAt mN (π * mNb x) x := by
  have hc := (Real.hasDerivAt_cos (π * x)).comp x (hasDerivAt_pix x)
  have hs := (Real.hasDerivAt_sin (π * x)).comp x (hasDerivAt_pix x)
  have h := hc.sub (((hasDerivAt_pix x).const_mul (2 * gamAM)).mul hs)
  have e : mN = fun y => Real.cos (π * y) - 2 * gamAM * (π * y) * Real.sin (π * y) := rfl
  rw [e]; refine h.congr_deriv ?_
  simp only [Function.comp, mNb]; ring

theorem hasDerivAt_mD (x : ℝ) : HasDerivAt mD (-(4 * π * (π * x))) x := by
  have h := ((hasDerivAt_pix x).pow 2).const_mul 2 |>.const_sub 1
  have e : mD = fun y => 1 - 2 * (π * y) ^ 2 := rfl
  rw [e]; refine h.congr_deriv ?_
  push_cast; ring

theorem hasDerivAt_mNb (x : ℝ) : HasDerivAt mNb (π * mN2 x) x := by
  have hc := (Real.hasDerivAt_cos (π * x)).comp x (hasDerivAt_pix x)
  have hs := (Real.hasDerivAt_sin (π * x)).comp x (hasDerivAt_pix x)
  have h := (hs.const_mul (-(1 + 2 * gamAM))).sub (((hasDerivAt_pix x).const_mul (2 * gamAM)).mul hc)
  have e : mNb = fun y => -(1 + 2 * gamAM) * Real.sin (π * y) - 2 * gamAM * (π * y) * Real.cos (π * y) := rfl
  rw [e]; refine h.congr_deriv ?_
  simp only [Function.comp, mN2]; ring

theorem hasDerivAt_mM (x : ℝ) : HasDerivAt mM (π * (mN2 x * mD x + 4 * mN x)) x := by
  have h := ((hasDerivAt_mNb x).mul (hasDerivAt_mD x)).add (((hasDerivAt_pix x).const_mul 4).mul (hasDerivAt_mN x))
  have e : mM = fun y => mNb y * mD y + 4 * (π * y) * mN y := rfl
  rw [e]; refine h.congr_deriv ?_
  ring

theorem continuous_mD : Continuous mD := by unfold mD; fun_prop

/-- `(N/D)' = π M / D²` -/
theorem hasDerivAt_mND {x : ℝ} (hx : mD x ≠ 0) : HasDerivAt (fun y => mN y / mD y) (π * mM x / mD x ^ 2) x := by
  refine ((hasDerivAt_mN x).div (hasDerivAt_mD x) hx).congr_deriv ?_
  simp only [mM]; field_simp; ring

/-- `(π M / D²)' = π² P / D³` -/
theorem hasDerivAt_mMD {x : ℝ} (hx : mD x ≠ 0) :
    HasDerivAt (fun y => π * mM y / mD y ^ 2) (π ^ 2 * mP x / mD x ^ 3) x := by
  have h := ((hasDerivAt_mM x).const_mul π).div ((hasDerivAt_mD x).pow 2) (pow_ne_zero 2 hx)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, mP, mM]; push_cast; field_simp; ring

/-! ## The Montgomery–Taylor part -/

/-- `KMT'` and `KMT''` in sinc form -/
def KMT1 (x : ℝ) : ℝ :=
  (-(π * sc1 ((Real.sqrt 2 - 2 * π * x) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2
def KMT2 (x : ℝ) : ℝ :=
  (π ^ 2 * sc2 ((Real.sqrt 2 - 2 * π * x) / 2) + π ^ 2 * sc2 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2

theorem hasDerivAt_KMT (x : ℝ) : HasDerivAt KMT (KMT1 x) x := by
  have h1 := (hasDerivAt_sinc ((Real.sqrt 2 - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (Real.sqrt 2) x)
  have h2 := (hasDerivAt_sinc ((Real.sqrt 2 + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (Real.sqrt 2) x)
  have e : KMT = fun y => (Real.sinc ((Real.sqrt 2 - 2 * π * y) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * y) / 2)) / 2 := rfl
  rw [e]; exact ((h1.add h2).div_const 2).congr_deriv (by simp only [KMT1]; ring)

theorem hasDerivAt_KMT1 (x : ℝ) : HasDerivAt KMT1 (KMT2 x) x := by
  have h1 := (hasDerivAt_sc1 ((Real.sqrt 2 - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (Real.sqrt 2) x)
  have h2 := (hasDerivAt_sc1 ((Real.sqrt 2 + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (Real.sqrt 2) x)
  have e : KMT1 = fun y => (-(π * sc1 ((Real.sqrt 2 - 2 * π * y) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * y) / 2)) / 2 := rfl
  rw [e]; exact ((((h1.const_mul π).neg).add (h2.const_mul π)).div_const 2).congr_deriv (by simp only [KMT2]; ring)

theorem KMT_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT x = K0AM * (mN x / mD x) := by
  have h := KMT_eq_gamma (x := x) hx
  rw [h]; rfl

theorem isOpen_mD_ne : IsOpen {y : ℝ | mD y ≠ 0} := isOpen_ne_fun continuous_mD continuous_const

theorem KMT1_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT1 x = K0AM * (π * mM x / mD x ^ 2) := by
  have hev : KMT =ᶠ[𝓝 x] fun y => K0AM * (mN y / mD y) := by
    filter_upwards [isOpen_mD_ne.mem_nhds hx] with y hy using KMT_eq_ND hy
  have h2 := ((hasDerivAt_mND hx).const_mul K0AM).congr_of_eventuallyEq hev
  exact (hasDerivAt_KMT x).unique h2

theorem KMT2_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT2 x = K0AM * (π ^ 2 * mP x / mD x ^ 3) := by
  have hev : KMT1 =ᶠ[𝓝 x] fun y => K0AM * (π * mM y / mD y ^ 2) := by
    filter_upwards [isOpen_mD_ne.mem_nhds hx] with y hy using KMT1_eq_ND hy
  have h2 := ((hasDerivAt_mMD hx).const_mul K0AM).congr_of_eventuallyEq hev
  exact (hasDerivAt_KMT1 x).unique h2

/-! ## The harmonic terms -/

theorem sc1_neg (θ : ℝ) : sc1 (-θ) = -sc1 θ := by
  unfold sc1
  rcases eq_or_ne θ 0 with rfl | h
  · simp
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.cos_neg, Real.sin_neg]; ring

theorem sc2_neg (θ : ℝ) : sc2 (-θ) = sc2 θ := by
  unfold sc2
  rcases eq_or_ne θ 0 with rfl | h
  · simp
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.cos_neg, Real.sin_neg]; ring

/-- the harmonic terms `T_j`, `T1_j`, `T2_j` at `j = n + 1` -/
def Tj (n : ℕ) (x : ℝ) : ℝ := (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2
def T1j (n : ℕ) (x : ℝ) : ℝ := (sc1 (π * (x - ((n : ℝ) + 1))) + sc1 (π * (x + ((n : ℝ) + 1)))) / 2
def T2j (n : ℕ) (x : ℝ) : ℝ := (sc2 (π * (x - ((n : ℝ) + 1))) + sc2 (π * (x + ((n : ℝ) + 1)))) / 2

/-- `ρ = 1/K(0)` -/
def rhoAM : ℝ := 1 / K0AM

theorem kfunAM_eq {x : ℝ} (hx : mD x ≠ 0) :
    kfunAM x = mN x / mD x + rhoAM * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * Tj n x := by
  have h0 := K0AM_pos.ne'
  unfold kfunAM
  rw [K0AM_eq, KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
  have hk : (Real.sinc ((Real.sqrt 2 - 2 * π * x) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT x := rfl
  rw [hk, KMT_eq_ND hx]
  have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
      ((Real.sinc ((ωAM (n + 1) - 2 * π * x) / 2) + Real.sinc ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
      = (cAM (n + 1) : ℝ) * Tj n x := by
    intro n _; rw [term_sinc]; rfl
  rw [Finset.sum_congr rfl hs, rhoAM]
  field_simp
  ring

theorem k1AM_eq {x : ℝ} (hx : mD x ≠ 0) :
    k1AM x = π * mM x / mD x ^ 2 + rhoAM * π * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T1j n x := by
  have h0 := K0AM_pos.ne'
  unfold k1AM K1AM
  rw [K0AM_eq, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
  have hk : (-(π * sc1 ((Real.sqrt 2 - 2 * π * x) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT1 x := rfl
  rw [hk, KMT1_eq_ND hx]
  have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
      ((-(π * sc1 ((ωAM (n + 1) - 2 * π * x) / 2)) + π * sc1 ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
      = π * ((cAM (n + 1) : ℝ) * T1j n x) := by
    intro n _
    rw [ωAM_succ]
    have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
    have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
    rw [e1, e2, sc1_neg, T1j]; ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, rhoAM]
  field_simp
  ring

theorem k2AM_eq {x : ℝ} (hx : mD x ≠ 0) :
    k2AM x = π ^ 2 * mP x / mD x ^ 3 + rhoAM * π ^ 2 * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T2j n x := by
  have h0 := K0AM_pos.ne'
  unfold k2AM K2AM
  rw [K0AM_eq, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
  have hk : (π ^ 2 * sc2 ((Real.sqrt 2 - 2 * π * x) / 2) + π ^ 2 * sc2 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT2 x := rfl
  rw [hk, KMT2_eq_ND hx]
  have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
      ((π ^ 2 * sc2 ((ωAM (n + 1) - 2 * π * x) / 2) + π ^ 2 * sc2 ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
      = π ^ 2 * ((cAM (n + 1) : ℝ) * T2j n x) := by
    intro n _
    rw [ωAM_succ]
    have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
    have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
    rw [e1, e2, sc2_neg, T2j]; ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, rhoAM]
  field_simp
  ring

end AMW
