import Zeta23.ThmD.Window
import Zeta23.ThmD.WindowCore

/-!
# AMW/Window — the R window and its elementary facts (stage A)

The window profile is a 13-term cosine sum in AMTOPA's family
  `vAM s = ∑_{j<13} cAM j · cos(ωAM j · s)`, `ωAM 0 = √2`, `ωAM j = 2πj` (`j ≥ 1`),
with `cAM j = cAMn j / 10⁹` (`cAM 0 = 1`), the corrections re-optimised for the six-point bound.
The test function has exactly the shape of `ThmD.phiD`, with `vStar` replaced by `vAM / MAM`:
  `phiW ϱ L w u = √(vAM (u/L) / MAM) · Taper.phi ϱ L w u`,  `MAM = 5/4`.
Dividing by `MAM` changes no ratio the argument reads (`cRatio` and the normalised kernel are
invariant under `φ ↦ φ/√M`); it makes `phiW ≤ 1` and leaves room in the total-variation fields.

Facts proved here: the split `vAM = cos(√2·) + pAM` with `|pAM| ≤ 13/200`; the bounds
`vAM ≤ 5/4` (everywhere), `vAM ≥ 137/200` on `|s| ≤ 1/2`, `vAM > 0` on `|s| < 3/5`; explicit first and
second derivatives of `vAM` with `|vAM′| ≤ 7/2`, `|vAM″| ≤ 78`; for the factor `fW L u = √(vAM(u/L)/MAM)`:
evenness, `0 ≤ fW ≤ 1`, `C²` on `|u| < L/2 + L/10`, `|fW′| ≤ 2/L` and `|fW″| ≤ 52/L²` on `|u| ≤ L/2`;
for `phiW`: evenness, `0 ≤ phiW ≤ 1`, support in `[-L/2, L/2]`, `C²`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

/-! ## The coefficients and the profile -/

/-- the R window's 13 numerators (denominator `10⁹`): AMTOPA's cosine family with the twelve
corrections re-optimised for the weighted six-point bound at `ω₀ = √2`. -/
def cAMn : ℕ → ℤ
  | 0 => 1000000000
  | 1 => 11417303
  | 2 => -12082749
  | 3 => 1119320
  | 4 => 7768774
  | 5 => -2270835
  | 6 => 8614841
  | 7 => -7848066
  | 8 => 1839062
  | 9 => 679183
  | 10 => -378738
  | 11 => 274196
  | 12 => -211190
  | _ => 0

/-- the window coefficients `cAM j = cAMn j / 10⁹`. -/
def cAM (j : ℕ) : ℚ := (cAMn j : ℚ) / 10 ^ 9

/-- the frequencies: `ωAM 0 = √2`, `ωAM j = 2πj` for `j ≥ 1`. -/
def ωAM (j : ℕ) : ℝ := if j = 0 then Real.sqrt 2 else 2 * π * j

/-- the AMTOPA profile (13 terms). -/
def vAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.cos (ωAM j * s)

/-- the scale `M = 5/4`. -/
def MAM : ℝ := 5 / 4

/-- the AMTOPA window, in the shape of `ThmD.phiD`. -/
def phiW (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (vAM (u / L) / MAM) * Taper.phi ϱ L w u

/-- the modulating factor of `phiW` (so `phiW ϱ L w u = fW L u * Taper.phi ϱ L w u` by `rfl`). -/
def fW (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (vAM (u / L) / MAM)

theorem phiW_eq_mul (ϱ : ℝ → ℝ) (L w u : ℝ) : phiW ϱ L w u = fW L u * Taper.phi ϱ L w u := rfl

/-- the abstract local data of the window at a height (the AM analogue of `Params.localFunD`). -/
def localFunW (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
  AdmWindow.localFun (phiW P.ϱ (P.L T) P.w) (P.L T)

theorem MAM_pos : (0 : ℝ) < MAM := by norm_num [MAM]

theorem cAM_zero : (cAM 0 : ℝ) = 1 := by norm_num [cAM, cAMn]

theorem ωAM_zero : ωAM 0 = Real.sqrt 2 := by simp [ωAM]

theorem ωAM_succ (j : ℕ) : ωAM (j + 1) = 2 * π * ((j : ℝ) + 1) := by
  simp [ωAM]

/-! ## The split `vAM = cos(√2·) + pAM` -/

/-- the perturbation: the terms `j = 1, …, 12`. -/
def pAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 12, (cAM (j + 1) : ℝ) * Real.cos (ωAM (j + 1) * s)

theorem vAM_eq (s : ℝ) : vAM s = Real.cos (Real.sqrt 2 * s) + pAM s := by
  rw [vAM, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
  rfl

/-- `∑_{j ≥ 1} |cAM j| = 54504257 / 10⁹ ≤ 13/200`. -/
theorem sum_abs_cAM_succ :
    ∑ j ∈ Finset.range 12, |(cAM (j + 1) : ℝ)| ≤ 13 / 200 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
  norm_num [abs_div]

theorem abs_pAM_le (s : ℝ) : |pAM s| ≤ 13 / 200 := by
  unfold pAM
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) sum_abs_cAM_succ
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem vAM_even (s : ℝ) : vAM (-s) = vAM s := by
  unfold vAM
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, Real.cos_neg]

theorem vAM_le (s : ℝ) : vAM s ≤ 5 / 4 := by
  rw [vAM_eq]
  have h1 := Real.cos_le_one (Real.sqrt 2 * s)
  have h2 := (abs_le.mp (abs_pAM_le s)).2
  linarith

/-- on `|s| ≤ 3/5`: `cos(√2 s) ≥ 1 - s² ≥ 16/25`. -/
theorem cos_sqrt2_ge {s : ℝ} : 1 - s ^ 2 ≤ Real.cos (Real.sqrt 2 * s) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * s)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : (Real.sqrt 2 * s) ^ 2 / 2 = s ^ 2 := by rw [mul_pow, hsq]; ring
  linarith

theorem vAM_ge_core {s : ℝ} (hs : |s| ≤ 1 / 2) : 137 / 200 ≤ vAM s := by
  rw [vAM_eq]
  have h1 := cos_sqrt2_ge (s := s)
  have h2 := (abs_le.mp (abs_pAM_le s)).1
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hs; nlinarith
  linarith

theorem vAM_pos_wide {s : ℝ} (hs : |s| ≤ 3 / 5) : 0 < vAM s := by
  rw [vAM_eq]
  have h1 := cos_sqrt2_ge (s := s)
  have h2 := (abs_le.mp (abs_pAM_le s)).1
  have hs2 : s ^ 2 ≤ 9 / 25 := by
    have := abs_le.mp hs; nlinarith
  linarith

/-- `vAM 0 = ∑ cAM j = 1008921101 / 10⁹`. -/
theorem vAM_zero : vAM 0 = 1008921101 / 10 ^ 9 := by
  simp only [vAM, mul_zero, Real.cos_zero, mul_one, Finset.sum_range_succ, Finset.sum_range_zero,
    cAM, cAMn]
  norm_num

theorem vAM_continuous : Continuous vAM := by
  unfold vAM; fun_prop

theorem vAM_contDiff : ContDiff ℝ ⊤ vAM := by
  unfold vAM
  exact ContDiff.sum fun j _ => contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

/-! ## Derivatives of the profile -/

/-- `vAM′ s = -∑ cAM j · ωAM j · sin(ωAM j · s)`. -/
def vAMd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))

/-- `vAM″ s = -∑ cAM j · ωAM j² · cos(ωAM j · s)`. -/
def vAMdd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))

theorem hasDerivAt_vAM (s : ℝ) : HasDerivAt vAM (vAMd s) s := by
  unfold vAM vAMd
  have h : ∀ j ∈ Finset.range 13, HasDerivAt (fun s => (cAM j : ℝ) * Real.cos (ωAM j * s))
      (-((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))) s := by
    intro j _
    have h1 : HasDerivAt (fun s => ωAM j * s) (ωAM j) s := by
      simpa using (hasDerivAt_id s).const_mul (ωAM j)
    have h2 := ((Real.hasDerivAt_cos (ωAM j * s)).comp s h1).const_mul (cAM j : ℝ)
    exact h2.congr_deriv (by ring)
  have := HasDerivAt.fun_sum h
  simpa using this

theorem hasDerivAt_vAMd (s : ℝ) : HasDerivAt vAMd (vAMdd s) s := by
  unfold vAMd vAMdd
  have h : ∀ j ∈ Finset.range 13, HasDerivAt (fun s => -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s)))
      (-((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))) s := by
    intro j _
    have h1 : HasDerivAt (fun s => ωAM j * s) (ωAM j) s := by
      simpa using (hasDerivAt_id s).const_mul (ωAM j)
    have h2 := (((Real.hasDerivAt_sin (ωAM j * s)).comp s h1).const_mul
      ((cAM j : ℝ) * ωAM j)).neg
    exact h2.congr_deriv (by ring)
  have := HasDerivAt.fun_sum h
  simpa using this

theorem deriv_vAM : deriv vAM = vAMd := funext fun s => (hasDerivAt_vAM s).deriv

theorem deriv_vAMd : deriv vAMd = vAMdd := funext fun s => (hasDerivAt_vAMd s).deriv

theorem ωAM_nonneg (j : ℕ) : 0 ≤ ωAM j := by
  unfold ωAM; split_ifs <;> positivity

/-- `ωAM 0 ≤ 3/2` and `ωAM j ≤ (63/10)·j` for `j ≥ 1`. -/
theorem ωAM_le (j : ℕ) : ωAM j ≤ if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ) := by
  by_cases h : j = 0
  · subst h
    rw [if_pos rfl, ωAM_zero, Real.sqrt_le_left (by norm_num)]; norm_num
  · rw [if_neg h]
    unfold ωAM
    rw [if_neg h]
    have := Real.pi_lt_d2
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith

theorem abs_vAMd_le (s : ℝ) : |vAMd s| ≤ 7 / 2 := by
  unfold vAMd
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ j ∈ Finset.range 13, |-((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))|
      ≤ |(cAM j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
    intro j _
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (ωAM_nonneg j)]
    calc |(cAM j : ℝ)| * ωAM j * |Real.sin (ωAM j * s)| ≤ |(cAM j : ℝ)| * ωAM j * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity [ωAM_nonneg j])
      _ ≤ |(cAM j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (ωAM_le j) (abs_nonneg _)
  refine (Finset.sum_le_sum hb).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
  norm_num [abs_div]

theorem ωAM_sq_le (j : ℕ) :
    ωAM j ^ 2 ≤ if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2 := by
  by_cases h : j = 0
  · subst h
    rw [if_pos rfl, ωAM_zero, Real.sq_sqrt (by norm_num)]
  · rw [if_neg h]
    unfold ωAM
    rw [if_neg h]
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    have : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
    have hj2 : (0 : ℝ) ≤ (j : ℝ) ^ 2 := sq_nonneg _
    have e : (2 * π * (j : ℝ)) ^ 2 = 4 * π ^ 2 * (j : ℝ) ^ 2 := by ring
    rw [e]
    nlinarith

theorem abs_vAMdd_le (s : ℝ) : |vAMdd s| ≤ 78 := by
  unfold vAMdd
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ j ∈ Finset.range 13, |-((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))|
      ≤ |(cAM j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
    intro j _
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (ωAM j))]
    calc |(cAM j : ℝ)| * ωAM j ^ 2 * |Real.cos (ωAM j * s)| ≤ |(cAM j : ℝ)| * ωAM j ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
      _ ≤ |(cAM j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (ωAM_sq_le j) (abs_nonneg _)
  refine (Finset.sum_le_sum hb).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
  norm_num [abs_div]

/-! ## Product rules on an open set (private copies; `XiPrime/QuarticWindow/ModWindow` has the same) -/

theorem deriv2_mul_eq_on {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) {u : ℝ} (hu : u ∈ U) :
    deriv (deriv (fun v => F v * G v)) u
      = deriv (deriv F) u * G u + 2 * (deriv F u * deriv G u) + F u * deriv (deriv G) u := by
  have hFd : ∀ v ∈ U, DifferentiableAt ℝ F v := fun v hv =>
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hv)
  have hGd : ∀ v ∈ U, DifferentiableAt ℝ G v := fun v hv =>
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hv)
  have hF' : ContDiffOn ℝ 1 (deriv F) U := hF.deriv_of_isOpen hU (by norm_num)
  have hG' : ContDiffOn ℝ 1 (deriv G) U := hG.deriv_of_isOpen hU (by norm_num)
  have hF'd : DifferentiableAt ℝ (deriv F) u :=
    (hF'.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
  have hG'd : DifferentiableAt ℝ (deriv G) u :=
    (hG'.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
  have h1 : deriv (fun v => F v * G v) =ᶠ[nhds u] fun v => deriv F v * G v + F v * deriv G v := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact deriv_mul (hFd v hv) (hGd v hv)
  rw [h1.deriv_eq]
  have hA : HasDerivAt (fun v => deriv F v * G v) (deriv (deriv F) u * G u + deriv F u * deriv G u) u :=
    hF'd.hasDerivAt.mul (hGd u hu).hasDerivAt
  have hB : HasDerivAt (fun v => F v * deriv G v) (deriv F u * deriv G u + F u * deriv (deriv G) u) u :=
    (hFd u hu).hasDerivAt.mul hG'd.hasDerivAt
  have hAB : HasDerivAt (fun v => deriv F v * G v + F v * deriv G v)
      ((deriv (deriv F) u * G u + deriv F u * deriv G u)
        + (deriv F u * deriv G u + F u * deriv (deriv G) u)) u := hA.add hB
  rw [hAB.deriv]; ring

theorem deriv_mul_eq_on {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) {u : ℝ} (hu : u ∈ U) :
    deriv (fun v => F v * G v) u = deriv F u * G u + F u * deriv G u :=
  deriv_mul ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))
    ((hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))

/-! ## The factor `fW` -/

/-- `hW L u = vAM(u/L)/MAM`, so that `fW L u = √(hW L u)` by `rfl`. -/
def hW (L : ℝ) (u : ℝ) : ℝ := vAM (u / L) / MAM

variable {L : ℝ}

theorem fW_eq_sqrt (u : ℝ) : fW L u = Real.sqrt (hW L u) := rfl

theorem fW_even (u : ℝ) : fW L (-u) = fW L u := by
  simp only [fW, neg_div, vAM_even]

theorem fW_nonneg (u : ℝ) : 0 ≤ fW L u := Real.sqrt_nonneg _

theorem hW_le_one (u : ℝ) : hW L u ≤ 1 := by
  unfold hW
  rw [div_le_one MAM_pos]
  exact vAM_le _

theorem fW_le_one (u : ℝ) : fW L u ≤ 1 := by
  rw [fW_eq_sqrt, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (hW_le_one u)

/-- on the core `|u| ≤ L/2`: `|u/L| ≤ 1/2`. -/
theorem abs_div_le_half (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith

theorem hW_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 137 / 250 ≤ hW L u := by
  have h := vAM_ge_core (abs_div_le_half hL hu)
  unfold hW MAM
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem fW_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 7 / 10 ≤ fW L u := by
  rw [fW_eq_sqrt]
  refine Real.le_sqrt_of_sq_le ?_
  have := hW_core_ge hL hu
  linarith

/-- the smooth region `U = (-(L/2 + L/10), L/2 + L/10)`: there `vAM(u/L) > 0`. -/
theorem hW_pos_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
    0 < hW L u := by
  unfold hW
  refine div_pos (vAM_pos_wide ?_) MAM_pos
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
  constructor <;> linarith [hu.1, hu.2]

theorem hW_contDiff : ContDiff ℝ ⊤ (hW L) := by
  unfold hW
  exact (vAM_contDiff.comp (contDiff_id.div_const L)).div_const MAM

theorem fW_contDiffOn (hL : 0 < L) :
    ContDiffOn ℝ 2 (fW L) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :=
  (hW_contDiff.of_le le_top).contDiffOn.sqrt fun _ hu => (hW_pos_of_mem hL hu).ne'

theorem fW_mul_self_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
    fW L u * fW L u = hW L u := by
  rw [fW_eq_sqrt, ← sq, Real.sq_sqrt (hW_pos_of_mem hL hu).le]

theorem hasDerivAt_hW (u : ℝ) : HasDerivAt (hW L) (vAMd (u / L) / L / MAM) u := by
  unfold hW
  have h1 : HasDerivAt (fun u : ℝ => u / L) (1 / L) u := by
    simpa using (hasDerivAt_id u).div_const L
  have h2 := ((hasDerivAt_vAM (u / L)).comp u h1).div_const MAM
  exact h2.congr_deriv (by ring)

theorem deriv_hW : deriv (hW L) = fun u => vAMd (u / L) / L / MAM :=
  funext fun u => (hasDerivAt_hW u).deriv

theorem hasDerivAt_deriv_hW (u : ℝ) :
    HasDerivAt (deriv (hW L)) (vAMdd (u / L) / L / L / MAM) u := by
  rw [deriv_hW]
  have h1 : HasDerivAt (fun u : ℝ => u / L) (1 / L) u := by
    simpa using (hasDerivAt_id u).div_const L
  have h2 := (((hasDerivAt_vAMd (u / L)).comp u h1).div_const L).div_const MAM
  exact h2.congr_deriv (by ring)

theorem abs_deriv_hW_le (hL : 0 < L) (u : ℝ) : |deriv (hW L) u| ≤ 14 / 5 / L := by
  rw [deriv_hW]
  simp only
  rw [abs_div, abs_div, abs_of_pos hL, abs_of_pos MAM_pos, div_div, div_le_div_iff₀ (by
    unfold MAM; positivity) hL]
  have := abs_vAMd_le (u / L)
  unfold MAM
  nlinarith

theorem abs_deriv2_hW_le (hL : 0 < L) (u : ℝ) : |deriv (deriv (hW L)) u| ≤ 312 / 5 / L ^ 2 := by
  rw [(hasDerivAt_deriv_hW u).deriv]
  rw [abs_div, abs_div, abs_div, abs_of_pos hL, abs_of_pos MAM_pos, div_div, div_div,
    div_le_div_iff₀ (by unfold MAM; positivity) (by positivity)]
  have := abs_vAMdd_le (u / L)
  unfold MAM
  have hL2 : 0 < L ^ 2 := by positivity
  nlinarith

theorem abs_deriv_fW_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (fW L) u| ≤ 2 / L := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm := fW_contDiffOn hL
  have hev : (fun v => fW L v * fW L v) =ᶠ[nhds u] hW L := by
    filter_upwards [hU.mem_nhds huU] with v hv using fW_mul_self_of_mem hL hv
  have hd : deriv (hW L) u = deriv (fW L) u * fW L u + fW L u * deriv (fW L) u := by
    rw [← hev.deriv_eq]; exact deriv_mul_eq_on hU hsm hsm huU
  have hf := fW_core_ge hL hu
  have hh := abs_deriv_hW_le hL u
  have e : deriv (fW L) u = deriv (hW L) u / (2 * fW L u) := by
    rw [hd]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fW L u)]
  rw [div_le_div_iff₀ (by linarith) hL]
  calc |deriv (hW L) u| * L ≤ 14 / 5 / L * L := by gcongr
    _ = 14 / 5 := by field_simp
    _ ≤ 2 * (2 * (7 / 10)) := by norm_num
    _ ≤ 2 * (2 * fW L u) := by gcongr

theorem abs_deriv2_fW_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (deriv (fW L)) u| ≤ 52 / L ^ 2 := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hmemU : ∀ v, |v| < L / 2 + L / 10 → v ∈ U := fun v hv => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
  have huU : u ∈ U := hmemU u (by linarith)
  have hsm := fW_contDiffOn hL
  have hd1 : ∀ v ∈ U, deriv (fun x => fW L x * fW L x) v = deriv (hW L) v := by
    intro v hv
    have hev : (fun x => fW L x * fW L x) =ᶠ[nhds v] hW L := by
      filter_upwards [hU.mem_nhds hv] with x hx using fW_mul_self_of_mem hL hx
    exact hev.deriv_eq
  have hev2 : deriv (fun x => fW L x * fW L x) =ᶠ[nhds u] deriv (hW L) := by
    filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
  have hd2 : deriv (deriv (hW L)) u
      = deriv (deriv (fW L)) u * fW L u + 2 * (deriv (fW L) u * deriv (fW L) u)
        + fW L u * deriv (deriv (fW L)) u := by
    rw [← hev2.deriv_eq]; exact deriv2_mul_eq_on hU hsm hsm huU
  have hf := fW_core_ge hL hu
  have h1 := abs_deriv_fW_le hL hu
  have h2 := abs_deriv2_hW_le hL u
  have e : deriv (deriv (fW L)) u
      = (deriv (deriv (hW L)) u - 2 * (deriv (fW L) u * deriv (fW L) u)) / (2 * fW L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fW L u), div_le_div_iff₀ (by linarith) (by positivity)]
  have hsq : |deriv (fW L) u| ^ 2 ≤ (2 / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hL2 : 0 < L ^ 2 := by positivity
  calc |deriv (deriv (hW L)) u - 2 * (deriv (fW L) u * deriv (fW L) u)| * L ^ 2
      ≤ (|deriv (deriv (hW L)) u| + 2 * |deriv (fW L) u| ^ 2) * L ^ 2 := by
        gcongr
        calc |deriv (deriv (hW L)) u - 2 * (deriv (fW L) u * deriv (fW L) u)|
            ≤ |deriv (deriv (hW L)) u| + |2 * (deriv (fW L) u * deriv (fW L) u)| := abs_sub _ _
          _ = |deriv (deriv (hW L)) u| + 2 * |deriv (fW L) u| ^ 2 := by
              rw [abs_mul, abs_two, abs_mul, sq]
    _ ≤ (312 / 5 / L ^ 2 + 2 * (2 / L) ^ 2) * L ^ 2 := by gcongr
    _ = 352 / 5 := by field_simp; ring
    _ ≤ 52 * (2 * (7 / 10)) := by norm_num
    _ ≤ 52 * (2 * fW L u) := by gcongr

/-! ## The window `phiW` -/

variable {ϱ : ℝ → ℝ} {w : ℝ}

theorem phiW_even (u : ℝ) : phiW ϱ L w (-u) = phiW ϱ L w u := by
  rw [phiW_eq_mul, phiW_eq_mul, fW_even, Taper.phi_even]

theorem phiW_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiW ϱ L w u :=
  mul_nonneg (fW_nonneg u) (Taper.phi_nonneg hϱ u)

theorem phiW_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phiW ϱ L w u ≤ 1 := by
  rw [phiW_eq_mul]
  calc fW L u * Taper.phi ϱ L w u ≤ 1 * 1 :=
        mul_le_mul (fW_le_one u) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
    _ = 1 := one_mul 1

theorem phiW_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phiW ϱ L w u = 0 := by
  rw [phiW_eq_mul, Taper.phi_eq_zero hϱ hw hu, mul_zero]

/-- `phiW ∈ C²`: the factor is `C²` on `|u| < L/2 + L/10`, the ramp vanishes off `[-L/2, L/2]`. -/
theorem phiW_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (phiW ϱ L w) := by
  have hL : 0 < L := by linarith
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge |u| (L / 2 + L / 10) with hu | hu
  · have hmem : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) := by
      rw [mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
    have hf : ContDiffAt ℝ 2 (fW L) u := (fW_contDiffOn hL).contDiffAt (isOpen_Ioo.mem_nhds hmem)
    exact hf.mul (((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt)
  · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := by
      have : {v : ℝ | L / 2 < |v|} = (fun v : ℝ => |v|) ⁻¹' Set.Ioi (L / 2) := rfl
      rw [this]
      exact (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
      show L / 2 < |u|; linarith
    apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0))
    filter_upwards [hopen.mem_nhds hmem] with v hv
    exact phiW_eq_zero hϱ hw (le_of_lt hv)

theorem phiW_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiW ϱ L w) :=
  (phiW_contDiff hϱ hw hwL).continuous

/-- `phiW² = (vAM(u/L)/MAM) · φ²` everywhere (on the support `vAM(u/L) > 0`; off it both vanish). -/
theorem phiW_sq_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
    phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := by
  rw [phiW_eq_mul, fW_eq_sqrt, mul_pow]
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [Taper.phi_eq_zero hϱ hw hu]; ring
  · rw [Real.sq_sqrt]
    refine (hW_pos_of_mem hL ?_).le
    rw [mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]

end AMW
