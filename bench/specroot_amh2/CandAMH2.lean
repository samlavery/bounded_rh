/-
AMW assembly: the AMTOPA-window bridge layer (AMW window, moments, constant, admissibility, zero side, prime
side; the Zeta23Ext bridge retargeted to the AM window; AMTail), the certificate taken as a hypothesis of the scored theorems (budget measurement only).
Modules: Window, Kernel, Moments, Swap, Constant, Floor, Params, Trig, Adm, Profile, PV, ZeroSide, Concrete, BHalf, BrA, BrB, BrC, AMTail.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.ThmD.Window
import Zeta23.ThmD.WindowCore
import Zeta23.ThmD.Limit
import Zeta23.ThmD.ZeroSideD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Zeta23.Taper.Norms
import Zeta23.ThmD.Concrete
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.ThmD.Mult
import Zeta23.PrimeSideA.EndsE1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option linter.all false

set_option Elab.async false

/-! ###### AMW module: Window ###### -/

/-!
# AMW/Window — the AMTOPA window and its elementary facts (stage A)

The window profile is AMTOPA's 13-term cosine sum
  `vAM s = ∑_{j<13} cAM j · cos(ωAM j · s)`, `ωAM 0 = √2`, `ωAM j = 2πj` (`j ≥ 1`),
with `cAM j` the first 13 numerators of AMTOPA's `candidate.json` over `10⁹` (`cAM 0 = 1`).
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

/-- AMTOPA's first 13 window numerators (`candidate.json`, denominator `10⁹`). -/
def cAMn : ℕ → ℤ
  | 0 => 1000000000
  | 1 => 12378982
  | 2 => -12602495
  | 3 => 4164033
  | 4 => 5741405
  | 5 => -1724025
  | 6 => 6219280
  | 7 => -8047828
  | 8 => 6321519
  | 9 => -5241981
  | 10 => -892658
  | 11 => 560544
  | 12 => -431207
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

/-- `∑_{j ≥ 1} |cAM j| = 64325957 / 10⁹ ≤ 13/200`. -/
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

/-- `vAM 0 = ∑ cAM j = 1006445569 / 10⁹`. -/
theorem vAM_zero : vAM 0 = 1006445569 / 10 ^ 9 := by
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

end

/-! ###### AMW module: Kernel ###### -/

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

end

/-! ###### AMW module: Moments ###### -/

/-!
# AMW/Moments — the a/b/J limits of the AMTOPA window (stage E1)

For `phiW ϱ L w` (`AMW/Window`) with `1 ≤ w`, `8w ≤ L`:
  `|L⁻¹∫ phiW² − aInf| ≤ 2w/L`,   `|L⁻¹∫ phiW⁴ − bInf| ≤ 2w/L`,
  `|(2/L³)∫₀ᴸ (phiW²⋆phiW²)(y)·y dy − JInf| ≤ 4w/L`,
with the scale-free limits
  `aInf = (∫_{-½}^{½} vAM)/MAM`, `bInf = ∫_{-½}^{½} (vAM/MAM)²`,
  `JInf = 2∫₀¹ r·vConvAM(r) dr / MAM²`, `vConvAM r = ∫_{-½}^{½-r} vAM(s)·vAM(s+r) ds`.
Hence `tendsto_cRatio_W`: `cRatio(λ₁(T); a_T, b_T, J_T) → cRatio(λ; aInf, bInf, JInf)` (the shape of
`ThmD.tendsto_cRatio_concrete`).  Method as in `ThmD/Window.lean` (`aD_close`, `bD_close`, `jD_close`): the
window differs from the sharp cutoff only on the two ramps; the sharp autocorrelation is evaluated by scaling
rather than in closed form (the closed form of the constant is `AMW/Constant`).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

/-! ## Scale-free limits -/

/-- the overlap function of the profile. -/
def vConvAM (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2 - r), vAM s * vAM (s + r)

def aInf : ℝ := (∫ s in (-(1:ℝ)/2)..(1/2), vAM s) / MAM

def bInf : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s / MAM) ^ 2

def JInf : ℝ := 2 * (∫ r in (0:ℝ)..1, vConvAM r * r) / MAM ^ 2

/-! ## Ramp estimates (copies of the private `ThmD/Window.lean` lemmas) -/

theorem edge_est {h p : ℝ → ℝ} {L w : ℝ} (hw0 : 0 < w)
    (hwL : 2 * w ≤ L) (hh : ∀ u, |h u| ≤ 1) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpl : ∀ u : ℝ, |u| ≤ L/2 - w → p u = 1) (hsupp : ∀ u : ℝ, L/2 ≤ |u| → p u = 0)
    (hpc : Continuous p) (hhc : Continuous h) :
    |(∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u| ≤ 2 * w := by
  have hrestr : ∫ u, h u * p u = ∫ u in Set.Icc (-(L/2)) (L/2), h u * p u := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have : L / 2 ≤ |x| := by
      rcases hx with hc | hc
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    rw [hsupp x this, mul_zero]
  have hIhp : MeasureTheory.IntegrableOn (fun u => h u * p u) (Set.Icc (-(L/2)) (L/2)) :=
    ((hhc.mul hpc).continuousOn).integrableOn_compact isCompact_Icc
  have hIh : MeasureTheory.IntegrableOn h (Set.Icc (-(L/2)) (L/2)) :=
    (hhc.continuousOn).integrableOn_compact isCompact_Icc
  have hsub : (∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u
      = ∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u) := by
    rw [hrestr, ← MeasureTheory.integral_sub hIhp hIh]
  rw [hsub]
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hptw : ∀ u ∈ Set.Icc (-(L/2)) (L/2), |h u * p u - h u| ≤ maj u := by
    intro u hu
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    rcases le_or_gt |u| (L/2 - w) with hpl' | hedge
    · rw [hpl u hpl', mul_one, sub_self, abs_zero]
      exact hmaj0
    · have hbound : |h u * p u - h u| ≤ 1 := by
        have e : h u * p u - h u = h u * (p u - 1) := by ring
        rw [e, abs_mul]
        calc |h u| * |p u - 1| ≤ 1 * 1 := by
              apply mul_le_mul (hh u) ?_ (abs_nonneg _) zero_le_one
              rw [abs_le]
              exact ⟨by linarith [hp0 u], by linarith [hp1 u]⟩
          _ = 1 := mul_one 1
      have hone : (1:ℝ) ≤ maj u := by
        rw [hmaj]
        show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
          + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
        rcases le_or_gt u 0 with hneg | hpos
        · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
            refine ⟨hu.1, ?_⟩
            have habs : |u| = -u := abs_of_nonpos hneg
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (L/2 - w) (L/2)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
        · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
            refine ⟨?_, hu.2⟩
            have habs : |u| = u := abs_of_pos hpos
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
      linarith
  calc |∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u)|
      ≤ ∫ u in Set.Icc (-(L/2)) (L/2), |h u * p u - h u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-(L/2)) (L/2), maj u := by
        apply MeasureTheory.setIntegral_mono_on
          (((hhc.mul hpc).sub hhc).abs.continuousOn.integrableOn_compact isCompact_Icc)
          hImaj.integrableOn measurableSet_Icc hptw
    _ ≤ ∫ u, maj u :=
        MeasureTheory.setIntegral_le_integral hImaj
          (MeasureTheory.ae_of_all _ fun u => by
            rw [hmaj]
            apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => zero_le_one) u)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))]
        rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

theorem integral_scale {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L) :
    ∫ u in (-(L/2))..(L/2), v (u / L) = L * ∫ s in (-(1:ℝ)/2)..(1/2), v s := by
  rw [intervalIntegral.integral_comp_div (f := v) hL.ne', smul_eq_mul,
    show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
    show L/2 / L = (1:ℝ)/2 by rw [div_div]; rw [div_eq_div_iff (by positivity) (by norm_num)]; ring]

/-! ## Global bounds on the profile -/

theorem abs_vAM_le (s : ℝ) : |vAM s| ≤ 5 / 4 := by
  rw [vAM_eq]
  have h1 := Real.abs_cos_le_one (Real.sqrt 2 * s)
  have h2 := abs_pAM_le s
  calc |Real.cos (Real.sqrt 2 * s) + pAM s| ≤ |Real.cos (Real.sqrt 2 * s)| + |pAM s| := abs_add_le _ _
    _ ≤ 5 / 4 := by linarith

theorem abs_hW_le (L u : ℝ) : |hW L u| ≤ 1 := by
  unfold hW
  rw [abs_div, abs_of_pos MAM_pos, div_le_one MAM_pos]
  exact abs_vAM_le _

theorem hW_continuous (L : ℝ) : Continuous (hW L) :=
  (vAM_continuous.comp (continuous_id.div_const L)).div_const MAM

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- the interval integral of `hW L` over the core is `L · aInf`. -/
theorem integral_hW (hL : 0 < L) :
    ∫ u in Set.Icc (-(L/2)) (L/2), hW L u = L * aInf := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
  unfold hW aInf
  rw [integral_scale (v := fun s => vAM s / MAM) hL, intervalIntegral.integral_div]

theorem integral_hW_sq (hL : 0 < L) :
    ∫ u in Set.Icc (-(L/2)) (L/2), hW L u ^ 2 = L * bInf := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
  unfold hW bInf
  exact integral_scale (v := fun s => (vAM s / MAM) ^ 2) hL

/-! ## a and b -/

theorem aW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiW ϱ L w u ^ 2) - aInf| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hwin : ∫ u, phiW ϱ L w u ^ 2 = ∫ u, hW L u * Taper.phi ϱ L w u ^ 2 := by
    congr 1; funext u; exact phiW_sq_eq hϱ hw0 hL u
  have hcore := edge_est (h := hW L) (p := fun u => Taper.phi ϱ L w u ^ 2) hw0 hwL'
    (abs_hW_le L) (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 2 = 1
      rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 2 = 0
      rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2) (hW_continuous L)
  rw [integral_hW hL] at hcore
  rw [hwin]
  have e : L⁻¹ * (∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - aInf
      = L⁻¹ * ((∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc L⁻¹ * |(∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf| ≤ L⁻¹ * (2 * w) :=
        mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
    _ = 2 * w / L := by field_simp

theorem bW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiW ϱ L w u ^ 4) - bInf| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hwin : ∫ u, phiW ϱ L w u ^ 4 = ∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
    congr 1; funext u
    have := phiW_sq_eq hϱ hw0 hL u (ϱ := ϱ) (w := w)
    calc phiW ϱ L w u ^ 4 = (phiW ϱ L w u ^ 2) ^ 2 := by ring
      _ = (hW L u * Taper.phi ϱ L w u ^ 2) ^ 2 := by rw [this]
      _ = hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by ring
  have hcore := edge_est (h := fun u => hW L u ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hw0 hwL'
    (fun u => by
      rw [abs_pow]
      calc |hW L u| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_hW_le L u) 2
        _ = 1 := one_pow 2)
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 4 = 1
      rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 4 = 0
      rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow (by norm_num : (4:ℕ) ≠ 0)])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 4) ((hW_continuous L).pow 2)
  rw [integral_hW_sq hL] at hcore
  rw [hwin]
  have e : L⁻¹ * (∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - bInf
      = L⁻¹ * ((∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc L⁻¹ * |(∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf| ≤ L⁻¹ * (2 * w) :=
        mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
    _ = 2 * w / L := by field_simp

/-! ## J: the sharp cutoff and the autocorrelation -/

/-- the sharp cutoff of `phiW²`. -/
def sW (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (hW L) u

theorem sW_nonneg (hL : 0 < L) (u : ℝ) : 0 ≤ sW L u := by
  unfold sW
  apply Set.indicator_nonneg
  intro x hx
  have := hW_core_ge hL (abs_le.mpr ⟨hx.1, hx.2⟩)
  linarith

theorem abs_sW_le (L u : ℝ) : |sW L u| ≤ 1 := by
  unfold sW
  by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
  · rw [Set.indicator_of_mem hm]; exact abs_hW_le L u
  · rw [Set.indicator_of_notMem hm, abs_zero]; exact zero_le_one

theorem sW_measurable (L : ℝ) : Measurable (sW L) :=
  Measurable.indicator (hW_continuous L).measurable measurableSet_Icc

theorem sW_integrable (L : ℝ) : Integrable (sW L) :=
  (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    ((hW_continuous L).continuousOn.integrableOn_compact isCompact_Icc)

/-- the window and the sharp cutoff differ by at most `2w` in `L¹`. -/
theorem integral_abs_phiWsq_sub_sharp (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |phiW ϱ L w u ^ 2 - sW L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |phiW ϱ L w u ^ 2 - sW L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := phiW_sq_eq hϱ hw hL u
    rcases le_or_gt |u| (L/2 - w) with hpl | hedge
    · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
        rw [abs_le] at hpl
        constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
      rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one]
      unfold sW
      rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L/2) with hin | hout
      · have hbound : |phiW ϱ L w u ^ 2 - sW L u| ≤ 1 := by
          have h1' : 0 ≤ phiW ϱ L w u ^ 2 := sq_nonneg _
          have h2' : phiW ϱ L w u ^ 2 ≤ 1 := by
            calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 :=
                  pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
              _ = 1 := one_pow 2
          have h3' : 0 ≤ sW L u := sW_nonneg hL u
          have h4' : sW L u ≤ 1 := (abs_le.mp (abs_sW_le L u)).2
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          rw [hmaj]
          show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
            + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
              have : |u| = -u := abs_of_nonpos hneg
              rw [this] at hin hedge
              exact ⟨by linarith, by linarith⟩
            have := hind0 (Set.Icc (L/2 - w) (L/2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
              have : |u| = u := abs_of_pos hpos
              rw [this] at hin hedge
              exact ⟨by linarith, by linarith⟩
            have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · have h1' : phiW ϱ L w u = 0 := phiW_eq_zero hϱ hw (le_of_lt hout)
        have h2' : sW L u = 0 := by
          unfold sW
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1', h2']
        norm_num
        exact hmaj0
  calc ∫ u, |phiW ϱ L w u ^ 2 - sW L u|
      ≤ ∫ u, maj u := by
        apply MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
          (MeasureTheory.ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

theorem phiW_sq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) :
    HasCompactSupport (fun u => phiW ϱ L w u ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L/2)) (b := L/2))
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hmem
  apply hx
  show phiW ϱ L w x ^ 2 = 0
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  have : L / 2 ≤ |x| := by
    rcases hmem with hc | hc
    · rw [abs_of_neg (by linarith : x < 0)]; linarith
    · rw [abs_of_pos (by linarith : 0 < x)]; linarith
  rw [phiW_eq_zero hϱ hw this, zero_pow two_ne_zero]

/-- pointwise comparison of the window autocorrelation with the sharp one: `≤ 4w`. -/
theorem autocorr_phiWsq_close (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    |Params.autocorr (fun u => phiW ϱ L w u ^ 2) y - ∫ u, sW L u * sW L (u + y)| ≤ 4 * w := by
  set h : ℝ → ℝ := fun u => phiW ϱ L w u ^ 2 with hhdef
  set k : ℝ → ℝ := sW L with hkdef
  have hh_cont : Continuous h := (phiW_continuous hϱ hw hwL).pow 2
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    rw [hhdef]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
      _ = 1 := one_pow 2
  have hk_meas : Measurable k := sW_measurable L
  have hk1 : ∀ u, |k u| ≤ 1 := abs_sW_le L
  have hint_h : Integrable h :=
    hh_cont.integrable_of_hasCompactSupport (phiW_sq_hasCompactSupport hϱ hw (by linarith))
  have hint_k : Integrable k := sW_integrable L
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
    hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
    exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) := by
    exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hdecomp : Params.autocorr h y - ∫ u, k u * k (u + y)
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - ∫ u, k u * k (u + y)
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl,
        MeasureTheory.integral_sub hint_hh hint_kk]
    rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    ring
  have hd2w := integral_abs_phiWsq_sub_sharp hϱ hw hwL
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  calc |Params.autocorr h y - ∫ u, k u * k (u + y)|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by
        rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

/-- the sharp autocorrelation, by scaling: `∫ sW(u)·sW(u+y) du = L·vConvAM(y/L)/MAM²` on `[0, L]`. -/
theorem sharp_overlap (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sW L u * sW L (u + y) = L * vConvAM (y / L) / MAM ^ 2 := by
  have hind : ∀ u : ℝ, sW L u * sW L (u + y)
      = (Set.Icc (-(L/2)) (L/2 - y)).indicator (fun u => hW L u * hW L (u + y)) u := by
    intro u
    unfold sW
    by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
    · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
  have hF : ∀ u, hW L u * hW L (u + y) = (fun s => vAM s * vAM (s + y / L) / MAM ^ 2) (u / L) := by
    intro u
    simp only [hW]
    rw [show (u + y) / L = u / L + y / L by ring]
    ring
  simp_rw [hF]
  rw [intervalIntegral.integral_comp_div (f := fun s => vAM s * vAM (s + y / L) / MAM ^ 2) hL.ne',
    smul_eq_mul, intervalIntegral.integral_div,
    show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
    show (L/2 - y) / L = 1/2 - y / L by field_simp]
  unfold vConvAM
  ring

theorem continuous_vConvAM : Continuous vConvAM := by
  unfold vConvAM
  have h : Continuous (Function.uncurry fun (r s : ℝ) => vAM s * vAM (s + r)) :=
    (vAM_continuous.comp continuous_snd).mul (vAM_continuous.comp (continuous_snd.add continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous h
    (continuous_const.sub continuous_id)

/-- `J_T := (2/L³)∫₀ᴸ (phiW²⋆phiW²)(y)·y dy` is within `8w/L` of `JInf`. -/
theorem JW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |2 / L ^ 3 * (∫ y in (0:ℝ)..L, Params.autocorr (fun u => phiW ϱ L w u ^ 2) y * y) - JInf|
      ≤ 8 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set A : ℝ → ℝ := Params.autocorr (fun u => phiW ϱ L w u ^ 2) with hAdef
  set C : ℝ → ℝ := fun y => L * vConvAM (y / L) / MAM ^ 2 with hCdef
  have hAcont : Continuous A := by
    rw [hAdef]
    refine Taper.autocorr_continuous_of_support _ (M := L/2) ((phiW_continuous hϱ hw0 hwL').pow 2) ?_
    intro u hu
    show phiW ϱ L w u ^ 2 = 0
    rw [phiW_eq_zero hϱ hw0 hu, zero_pow two_ne_zero]
  have hCcont : Continuous C := by
    rw [hCdef]
    exact ((continuous_const.mul (continuous_vConvAM.comp (continuous_id.div_const L))).div_const _)
  have hIA : IntervalIntegrable (fun y => A y * y) MeasureTheory.volume 0 L :=
    (hAcont.mul continuous_id).intervalIntegrable 0 L
  have hIC : IntervalIntegrable (fun y => C y * y) MeasureTheory.volume 0 L :=
    (hCcont.mul continuous_id).intervalIntegrable 0 L
  have hsplit : ∫ y in (0:ℝ)..L, A y * y
      = (∫ y in (0:ℝ)..L, (A y - C y) * y) + ∫ y in (0:ℝ)..L, C y * y := by
    have e1 : ∫ y in (0:ℝ)..L, (A y - C y) * y = ∫ y in (0:ℝ)..L, (A y * y - C y * y) :=
      intervalIntegral.integral_congr (fun y _ => by ring)
    rw [e1, intervalIntegral.integral_sub hIA hIC]
    ring
  have hcmp : |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * L := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * w * L)
      (f := fun y => (A y - C y) * y) (a := 0) (b := L) ?_
    · rw [Real.norm_eq_abs] at hb
      calc |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * |L - 0| := hb
        _ = 4 * w * L * L := by rw [sub_zero, abs_of_pos hL]
    · intro y hy
      rw [Set.uIoc_of_le hL.le] at hy
      rw [Real.norm_eq_abs]
      show |(A y - C y) * y| ≤ 4 * w * L
      rw [abs_mul]
      have hAC : |A y - C y| ≤ 4 * w := by
        have h1 := autocorr_phiWsq_close hϱ hw0 hwL' y (L := L)
        rw [sharp_overlap hL hy.1.le hy.2] at h1
        exact h1
      calc |A y - C y| * |y| ≤ (4 * w) * L := by
            apply mul_le_mul hAC ?_ (abs_nonneg _) (by positivity)
            rw [abs_of_pos hy.1]
            exact hy.2
        _ = 4 * w * L := rfl
  have hmain : 2 / L ^ 3 * ∫ y in (0:ℝ)..L, C y * y = JInf := by
    have hG : ∀ y, C y * y = (L ^ 2 / MAM ^ 2) * ((fun r => vConvAM r * r) (y / L)) := by
      intro y
      simp only [hCdef]
      field_simp
    simp_rw [hG]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (f := fun r => vConvAM r * r) hL.ne', smul_eq_mul,
      zero_div, div_self hL.ne']
    unfold JInf
    field_simp
  have e : 2 / L ^ 3 * (∫ y in (0:ℝ)..L, A y * y) - JInf
      = 2 / L ^ 3 * (∫ y in (0:ℝ)..L, (A y - C y) * y) := by
    rw [hsplit, mul_add, hmain]; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / L ^ 3)]
  calc 2 / L ^ 3 * |∫ y in (0:ℝ)..L, (A y - C y) * y|
      ≤ 2 / L ^ 3 * (4 * w * L * L) := mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 8 * w / L := by field_simp; ring

/-! ## Positivity of the limits -/

theorem vAM_pos_core {s : ℝ} (hs : s ∈ Set.Icc (-(1:ℝ)/2) (1/2)) : 0 < vAM s :=
  lt_of_lt_of_le (by norm_num) (vAM_ge_core (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩))

theorem vConvAM_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ vConvAM r := by
  unfold vConvAM
  apply intervalIntegral.integral_nonneg (by linarith)
  intro s hs
  exact mul_nonneg (vAM_pos_core ⟨hs.1, by linarith [hs.2]⟩).le
    (vAM_pos_core ⟨by linarith [hs.1], by linarith [hs.2]⟩).le

theorem JInf_nonneg : 0 ≤ JInf := by
  unfold JInf
  apply div_nonneg _ (sq_nonneg _)
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg zero_le_one
  intro r hr
  exact mul_nonneg (vConvAM_nonneg hr.1 hr.2) hr.1

theorem bInf_pos : 0 < bInf := by
  unfold bInf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((vAM_continuous.div_const _).pow 2).intervalIntegrable _ _
  · intro s hs
    have h1 := vAM_pos_core ⟨hs.1.le, hs.2.le⟩
    have h2 := MAM_pos
    positivity
  · norm_num

theorem aInf_pos : 0 < aInf := by
  unfold aInf
  apply div_pos _ MAM_pos
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact vAM_continuous.intervalIntegrable _ _
  · intro s hs
    exact vAM_pos_core ⟨hs.1.le, hs.2.le⟩
  · norm_num

/-! ## The limit theorem (shape of `ThmD.tendsto_cRatio_concrete`) -/

theorem tendsto_aW {P : Params} (hP : P.Valid) :
    Tendsto (fun T => (localFunW P T).a) atTop (𝓝 aInf) := by
  apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
  exact aW_close hP.taper hP.one_le_w hT

theorem tendsto_bW {P : Params} (hP : P.Valid) :
    Tendsto (fun T => (localFunW P T).b) atTop (𝓝 bInf) := by
  apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
  exact bW_close hP.taper hP.one_le_w hT

theorem tendsto_JW {P : Params} (hP : P.Valid) :
    Tendsto (fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y) atTop
      (𝓝 JInf) := by
  apply ThmD.tendsto_of_close hP.lam_pos (C := 8)
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
  exact JW_close hP.taper hP.one_le_w hT

/-- **The AM window ratio converges**: `cRatio(λ₁(T); a_T, b_T, J_T) → cRatio(λ; aInf, bInf, JInf)`,
for the data `localFunW P T` (`a = L⁻¹∫φ²`, `b = L⁻¹∫φ⁴`, `J = (2/L³)∫₀ᴸ g(y)y dy`). -/
theorem tendsto_cRatio_W {P : Params} (hP : P.Valid) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (localFunW P T).a (localFunW P T).b
      (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y)) atTop
      (𝓝 (ThmD.cRatio P.lam aInf bInf JInf)) := by
  have hden : 0 < bInf + P.lam ^ 2 * JInf := by
    have h1 := JInf_nonneg
    have h2 := bInf_pos
    positivity
  have hl1 := ThmD.tendsto_lam1 hP.lam_pos
  have hnum := hl1.mul ((tendsto_aW hP).pow 2)
  have hdenT := (tendsto_bW hP).add ((hl1.pow 2).mul (tendsto_JW hP))
  exact hnum.div hdenT hden.ne'

theorem cRatio_W_pos {lam : ℝ} (hlam : 0 < lam) : 0 < ThmD.cRatio lam aInf bInf JInf := by
  unfold ThmD.cRatio
  have h1 := JInf_nonneg
  have h2 := bInf_pos
  have h3 := aInf_pos
  positivity

end AMW

end

/-! ###### AMW module: Swap ###### -/

/-!
# AMW/Swap — the overlap moment is the `|s − t|` energy (stage E2)

For continuous `q` with `|q| ≤ B`:
  `2 ∫₀¹ (∫_{-½}^{½-r} q(s) q(s+r) ds) · r dr = ∫_{-½}^{½} q(s) (∫_{-½}^{½} |s − t| q(t) dt) ds`.
Proof on the line, with `e = 1_{[-½,½]} q`: substitute `t = s + r` in the inner integral, swap the order
(Fubini; the integrand is bounded and supported in `[-½,½] × [-1,1]`), use that `r ↦ ∫ e(s)e(s+r) ds` is even
and vanishes for `r > 1`, and fold `∫_ℝ |r| A(r) dr = 2∫₀¹ r A(r) dr`.
Consequence: `JInf · MAM² = ∫ vAM(s) K(s) ds` with `K(s) = ∫ |s − t| vAM(t) dt`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace AMW

section Swap

variable {q : ℝ → ℝ} {B : ℝ}

/-- the extension of `q` by zero off `[-1/2, 1/2]`. -/
def ext0 (q : ℝ → ℝ) : ℝ → ℝ := (Icc (-(1:ℝ)/2) (1/2)).indicator q

theorem ext0_measurable (hq : Continuous q) : Measurable (ext0 q) :=
  hq.measurable.indicator measurableSet_Icc

theorem abs_ext0_le (hB : ∀ s, |q s| ≤ B) (s : ℝ) : |ext0 q s| ≤ B := by
  unfold ext0
  by_cases h : s ∈ Icc (-(1:ℝ)/2) (1/2)
  · rw [Set.indicator_of_mem h]; exact hB s
  · rw [Set.indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hB s)

theorem intervalIntegral_eq_indicator (f : ℝ → ℝ) :
    ∫ s in (-(1:ℝ)/2)..(1/2), f s = ∫ s, (Icc (-(1:ℝ)/2) (1/2)).indicator f s := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

/-- the autocorrelation of the extension. -/
def acor (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s, ext0 q s * ext0 q (s + r)

theorem acor_neg (r : ℝ) : acor q (-r) = acor q r := by
  unfold acor
  have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun x => ext0 q (x + r) * ext0 q x) r
  simp only [sub_add_cancel] at h
  calc ∫ s, ext0 q s * ext0 q (s + -r) = ∫ x, ext0 q x * ext0 q (x - r) := by
        simp only [sub_eq_add_neg]
    _ = ∫ x, ext0 q (x + r) * ext0 q x := h
    _ = ∫ s, ext0 q s * ext0 q (s + r) := by
        congr 1; funext s; ring

theorem acor_eq_zero {r : ℝ} (hr : 1 < r) : acor q r = 0 := by
  unfold acor
  have : ∀ s, ext0 q s * ext0 q (s + r) = 0 := by
    intro s
    unfold ext0
    by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2)
    · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r), mul_zero]
      intro h; linarith [hs.1, h.2]
    · rw [Set.indicator_of_notMem hs, zero_mul]
  simp only [this, integral_zero]

/-- on `[0, 1]` the autocorrelation is the overlap integral. -/
theorem acor_eq_overlap {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    acor q r = ∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r) := by
  unfold acor
  have hind : ∀ s : ℝ, ext0 q s * ext0 q (s + r)
      = (Icc (-(1:ℝ)/2) (1/2 - r)).indicator (fun s => q s * q (s + r)) s := by
    intro s
    unfold ext0
    by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2 - r)
    · have hs1 : s ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨hs.1, by linarith [hs.2]⟩
      have hs2 : s + r ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs1, Set.indicator_of_mem hs2]
    · rw [Set.indicator_of_notMem hs]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1:ℝ)/2 ≤ 1/2 - r)]

/-- the integrand of the double integral is integrable on the plane. -/
theorem integrable_swap (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
    Integrable (fun p : ℝ × ℝ => ext0 q p.1 * (|p.2| * ext0 q (p.1 + p.2)))
      (volume.prod volume) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set K : Set (ℝ × ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-1:ℝ) 1 with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hKf : (volume.prod volume) K ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hg : Integrable (K.indicator (fun _ => B ^ 2)) (volume.prod volume) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hKf)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((ext0_measurable hq).comp measurable_fst).mul
      ((continuous_abs.measurable.comp measurable_snd).mul
        ((ext0_measurable hq).comp (measurable_fst.add measurable_snd))) |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    by_cases h1 : p.1 ∈ Icc (-(1:ℝ)/2) (1/2)
    · by_cases h2 : p.1 + p.2 ∈ Icc (-(1:ℝ)/2) (1/2)
      · have hpK : p ∈ K := ⟨h1, by constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
        rw [Set.indicator_of_mem hpK, abs_mul, abs_mul, abs_abs]
        have hr : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
          by linarith [h1.1, h1.2, h2.1, h2.2]⟩
        have e1 := abs_ext0_le hB p.1 (q := q)
        have e2 := abs_ext0_le hB (p.1 + p.2) (q := q)
        calc |ext0 q p.1| * (|p.2| * |ext0 q (p.1 + p.2)|) ≤ B * (1 * B) := by
              apply mul_le_mul e1 (mul_le_mul hr e2 (abs_nonneg _) zero_le_one)
                (by positivity) hB0
          _ = B ^ 2 := by ring
      · have : ext0 q (p.1 + p.2) = 0 := Set.indicator_of_notMem h2 _
        rw [this, mul_zero, mul_zero, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p
    · have : ext0 q p.1 = 0 := Set.indicator_of_notMem h1 _
      rw [this, zero_mul, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p

/-- **The swap identity.** -/
theorem swap_identity (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
    2 * ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
      = ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t := by
  -- right side on the line
  have hR1 : ∀ s, ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t = ∫ t, |s - t| * ext0 q t := by
    intro s
    rw [intervalIntegral_eq_indicator]
    congr 1; funext t
    unfold ext0
    exact Set.indicator_mul_right _ (fun t => |s - t|) q
  have hR2 : ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t
      = ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r)) := by
    simp_rw [hR1]
    rw [intervalIntegral_eq_indicator]
    congr 1; funext s
    have e1 : (Icc (-(1:ℝ)/2) (1/2)).indicator (fun s => q s * ∫ t, |s - t| * ext0 q t) s
        = ext0 q s * ∫ t, |s - t| * ext0 q t := by
      unfold ext0
      exact Set.indicator_mul_left _ q (fun s => ∫ t, |s - t| * ext0 q t)
    rw [e1, ← integral_const_mul]
    have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
      (fun t => ext0 q s * (|s - t| * ext0 q t)) s
    rw [← h]
    congr 1; funext r
    rw [show s - (s + r) = -r by ring, abs_neg]
  -- swap
  have hS : ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r))
      = ∫ r, |r| * acor q r := by
    rw [MeasureTheory.integral_integral_swap (integrable_swap hq hB)]
    congr 1; funext r
    unfold acor
    rw [← integral_const_mul]
    congr 1; funext s
    ring
  -- fold the even function
  have hE : ∫ r, |r| * acor q r = 2 * ∫ r in Ioi 0, r * acor q r := by
    have e : (fun r => |r| * acor q r) = fun r => (fun x => x * acor q x) |r| := by
      funext r
      simp only
      rcases le_or_gt 0 r with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, acor_neg]
    rw [e]
    exact integral_comp_abs (f := fun x => x * acor q x)
  have hI : ∫ r in Ioi 0, r * acor q r = ∫ r in (0:ℝ)..1, r * acor q r := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
      (f := fun r => r * acor q r) measurableSet_Ioi
      (Ioc_subset_Ioi_self : Ioc (0:ℝ) 1 ⊆ Ioi 0) ?_)
    intro x hx
    have hx1 : 1 < x := by
      rcases hx with ⟨hx0, hx1⟩
      simp only [mem_Ioc, not_and_or, not_le] at hx1
      rcases hx1 with h | h
      · exact absurd (mem_Ioi.mp hx0) h
      · exact h
    rw [acor_eq_zero hx1, mul_zero]
  have hO : ∫ r in (0:ℝ)..1, r * acor q r
      = ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    show r * acor q r = (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
    rw [acor_eq_overlap hr.1 hr.2, mul_comm]
  rw [hR2, hS, hE, hI, hO]

end Swap

/-- **`JInf` as an energy**: `JInf·MAM² = ∫_{-½}^{½} vAM(s) ∫_{-½}^{½} |s−t| vAM(t) dt ds`. -/
theorem JInf_eq_energy :
    JInf * MAM ^ 2
      = ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t := by
  rw [← swap_identity vAM_continuous abs_vAM_le]
  unfold JInf vConvAM
  have h := MAM_pos
  field_simp

end AMW

end

/-! ###### AMW module: Constant ###### -/

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

end

/-! ###### AMW module: Floor ###### -/

/-!
# AMW/Floor — a rational floor for `H_W` and the ranges of `a`, `b` (stage E4)

* `HW_ge : 6721883/10⁷ ≤ HW` (`HW = 0.6721883029…`; the floor is `2.9·10⁻⁹` below);
* `1/2 < aInf < 1`, `1/2 < bInf` (Cauchy–Schwarz `bInf ≥ aInf²`), hence eventually
  `1/2 ≤ a_T ≤ 1` and `1/2 ≤ b_T` for the data `localFunW P T`.
Enclosures of `sin θ₀, cos θ₀` (`θ₀ = √2/2`) by the twelve-term Taylor bound (the argument of the record
file's `cos_sin_taylor12`).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

theorem taylor12_F (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
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

theorem sqrt2_half_bounds :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

theorem cos_theta0_le : Real.cos (Real.sqrt 2 / 2) ≤ 76024459708 / 10 ^ 11 := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475244/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.cos (Real.sqrt 2 / 2) ≤ Real.cos r :=
    Real.cos_le_cos_of_nonneg_of_le_pi hr0 (by linarith [hb.2, Real.pi_gt_three]) hb.1
  have ht := (abs_le.mp (taylor12_F r hr1).1).2
  rw [abs_of_nonneg hr0] at ht
  have hv : (1 - r^2/2 + r^4/24 - r^6/720 + r^8/40320 - r^10/3628800) + r ^ 12 * (13/5748019200)
      ≤ 76024459708 / 10 ^ 11 := by
    rw [hr]; norm_num
  linarith

theorem sin_theta0_ge : 64963693904 / 10 ^ 11 ≤ Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475244/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.sin r ≤ Real.sin (Real.sqrt 2 / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
      (by linarith [hb.2, Real.pi_gt_three]) hb.1
  have ht := (abs_le.mp (taylor12_F r hr1).2).1
  rw [abs_of_nonneg hr0] at ht
  have hv : 64963693904 / 10 ^ 11
      ≤ (r - r^3/6 + r^5/120 - r^7/5040 + r^9/362880 - r^11/39916800) - r ^ 12 * (13/5748019200) := by
    rw [hr]; norm_num
  linarith

theorem sin_theta0_le : Real.sin (Real.sqrt 2 / 2) ≤ 64963693912 / 10 ^ 11 := by
  have hb := sqrt2_half_bounds
  set r : ℝ := 7071067811865475245/10^19 with hr
  have hr0 : 0 ≤ r := by rw [hr]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
  have hmono : Real.sin (Real.sqrt 2 / 2) ≤ Real.sin r :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hb.1, Real.pi_gt_three])
      (by rw [hr]; linarith [Real.pi_gt_three]) hb.2
  have ht := (abs_le.mp (taylor12_F r hr1).2).2
  rw [abs_of_nonneg hr0] at ht
  have hv : (r - r^3/6 + r^5/120 - r^7/5040 + r^9/362880 - r^11/39916800) + r ^ 12 * (13/5748019200)
      ≤ 64963693912 / 10 ^ 11 := by
    rw [hr]; norm_num
  linarith

/-- `PAM` with `π` replaced by its upper bound `π_hi` (an upper bound for `PAM`). -/
def PAMhi : ℝ :=
  ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * (314159265358979323847 / 10 ^ 20) ^ 2 * ((n : ℝ) + 1) ^ 2))

theorem PAM_le : PAM ≤ PAMhi := by
  unfold PAM PAMhi
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply sub_le_sub_left
  have hπ := Real.pi_lt_d20
  have hπ0 := Real.pi_pos
  have hk : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  apply one_div_le_one_div_of_le (by positivity)
  have : π ^ 2 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ hπ0.le; linarith
  have := mul_le_mul_of_nonneg_right this hk.le
  nlinarith

theorem PAMhi_nonneg : 0 ≤ PAMhi := by
  unfold PAMhi
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg (sq_nonneg _)
  have hk : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith
  have : 1 / (4 * (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem floor_numeric :
    (6721883 / 10 ^ 7 : ℝ) ≤ 3 / 2 - (76024459708 / 10 ^ 11) / (2 * (7071067811865475244/10^19) * (64963693904 / 10 ^ 11))
      - PAMhi / (2 * (64963693904 / 10 ^ 11) ^ 2) := by
  unfold PAMhi dAM
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
  norm_num

/-- **The rational floor**: `0.6721883 ≤ H_W`. -/
theorem HW_ge : (6721883 / 10 ^ 7 : ℝ) ≤ HW := by
  rw [HW_eq]
  have hc := cos_theta0_le
  have hs := sin_theta0_ge
  have hb := sqrt2_half_bounds
  have hP := PAM_le
  have hP0 := PAMhi_nonneg
  have hs0 : (0:ℝ) < 64963693904 / 10 ^ 11 := by norm_num
  have hr0 : (0:ℝ) < 7071067811865475244/10^19 := by norm_num
  have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
  have hden : 2 * (7071067811865475244/10^19 : ℝ) * (64963693904 / 10 ^ 11)
      ≤ Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
    have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
    exact mul_le_mul h2 hs hs0.le (Real.sqrt_nonneg 2)
  have h1 : Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
      ≤ (76024459708 / 10 ^ 11) / (2 * (7071067811865475244/10^19) * (64963693904 / 10 ^ 11)) :=
    div_le_div₀ (by norm_num) hc (by positivity) hden
  have hsq : (64963693904 / 10 ^ 11 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 :=
    pow_le_pow_left₀ hs0.le hs 2
  have h2 : PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤ PAMhi / (2 * (64963693904 / 10 ^ 11) ^ 2) :=
    div_le_div₀ hP0 hP (by positivity) (by linarith)
  have := floor_numeric
  linarith

/-! ## Ranges of `a` and `b` -/

theorem aInf_eq : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
  unfold aInf; rw [integral_vAM]

theorem aInf_gt_half : 1 / 2 < aInf := by
  rw [aInf_eq]
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_ge
  unfold MAM
  rw [lt_div_iff₀ (by norm_num)]
  have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
  nlinarith

theorem aInf_lt_one : aInf < 1 := by
  rw [aInf_eq]
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_le
  have hs0 := sin_theta0_pos
  unfold MAM
  rw [div_lt_iff₀ (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 * (7071067811865475245/10^19 : ℝ) := by linarith [hb.2]
  nlinarith [Real.sqrt_nonneg 2]

/-- Cauchy–Schwarz on the unit window: `bInf ≥ aInf²`. -/
theorem aInf_sq_le_bInf : aInf ^ 2 ≤ bInf := by
  set q : ℝ → ℝ := fun s => vAM s / MAM with hq
  have hqc : Continuous q := vAM_continuous.div_const _
  have ha : aInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s := by
    unfold aInf; rw [hq, intervalIntegral.integral_div]
  have hb : bInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s ^ 2 := rfl
  have h0 : 0 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have hexp : ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 = bInf - aInf ^ 2 := by
    have e : (fun s => (q s - aInf) ^ 2) = fun s => q s ^ 2 - 2 * aInf * q s + aInf ^ 2 := by
      funext s; ring
    have i1 : IntervalIntegrable (fun s => q s ^ 2 - 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
      ((hqc.pow 2).sub (continuous_const.mul hqc)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => q s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
      (hqc.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun s => 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
      (continuous_const.mul hqc).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← ha, ← hb]
    simp only [smul_eq_mul]
    ring
  linarith

theorem bInf_gt_half : 1 / 2 < bInf := by
  have h1 := aInf_gt_half
  have h2 := aInf_sq_le_bInf
  have hb := sqrt2_half_bounds
  have hs := sin_theta0_ge
  -- aInf ≥ 2·r_lo·s_lo/(5/4) > 0.734, so aInf² > 1/2
  have ha : (734 / 1000 : ℝ) < aInf := by
    rw [aInf_eq]
    unfold MAM
    rw [lt_div_iff₀ (by norm_num)]
    have h2' : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
    nlinarith
  nlinarith

theorem eventually_aW_range {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).a ∧ (localFunW P T).a ≤ 1 := by
  have h := tendsto_aW hP
  filter_upwards [h.eventually (lt_mem_nhds aInf_gt_half), h.eventually (gt_mem_nhds aInf_lt_one)]
    with T h1 h2
  exact ⟨h1.le, h2.le⟩

theorem eventually_bW_ge_half {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).b := by
  filter_upwards [(tendsto_bW hP).eventually (lt_mem_nhds bInf_gt_half)] with T h
  exact h.le

end AMW

end

/-! ###### AMW module: Params ###### -/

/-
AMW/Params.lean — the window-realizing parameter family for an arbitrary window family.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/ThmD/ParamsD.lean and Zeta23/XiPrime/QuarticWindow/Params.lean, generic in the window: for a
family W : ℝ → (ℝ → ℝ) (height T ↦ window), `atW P W T := ⟨x ↦ W T (L/2 − w·x), λ, w⟩`.  Its λ, w
— hence L, X, λ₁, d, τ_k, h, 𝓔_T, toSetting — are P's by rfl, and its window AT HEIGHT T is W T
whenever W T is even (`atW_phi`), so its local data and prime-side traces are the AdmWindow data
of W T.
-/

noncomputable section

open Real

namespace AMW

open Zeta23

/-- the parameter set realizing the window `W T` at height `T`. -/
def atW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : Params := ⟨fun x => W T (P.L T / 2 - P.w * x), P.lam, P.w⟩

section rfl
variable (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ)

@[simp] theorem atW_lam : (atW P W T).lam = P.lam := rfl
@[simp] theorem atW_w : (atW P W T).w = P.w := rfl
@[simp] theorem atW_L : (atW P W T).L = P.L := rfl
@[simp] theorem atW_X : (atW P W T).X = P.X := rfl
@[simp] theorem atW_lam1 : (atW P W T).lam1 = P.lam1 := rfl
@[simp] theorem atW_hgrid : (atW P W T).hgrid = P.hgrid := rfl
@[simp] theorem atW_d : (atW P W T).d = P.d := rfl
@[simp] theorem atW_tau : (atW P W T).tau = P.tau := rfl
@[simp] theorem atW_calE : (atW P W T).calE = P.calE := rfl
@[simp] theorem atW_toSetting : (atW P W T).toSetting = P.toSetting := rfl

theorem atW_tau_eq (k : ℤ) : (atW P W T).tau T k = T + k * (2 * π / P.L T) := rfl

end rfl

variable {P : Params} {W : ℝ → ℝ → ℝ}

/-- **the window of `atW P W T` at height T is `W T`** (W T even, w ≠ 0). -/
theorem atW_phi (T : ℝ) (hw : P.w ≠ 0) (hev : ∀ u, W T (-u) = W T u) : (atW P W T).phi T = W T := by
  funext u
  show W T (P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w)) = W T u
  have e : P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w) = |u| := by
    simp only [Params.L]; field_simp; ring
  rw [e]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]; exact hev u

theorem atW_phi_valid (T : ℝ) (hP : P.Valid) (hev : ∀ u, W T (-u) = W T u) : (atW P W T).phi T = W T :=
  atW_phi T (by linarith [hP.one_le_w]) hev

section
variable (T : ℝ) (hP : P.Valid) (hev : ∀ u, W T (-u) = W T u)
include hP hev

theorem atW_localFun : (atW P W T).localFun T = AdmWindow.localFun (W T) (P.L T) := by
  rw [Params.localFun_eq_admWindow, atW_phi_valid T hP hev]; rfl

theorem atW_a : (atW P W T).a T = AdmWindow.av (W T) (P.L T) := by
  rw [show (atW P W T).a T = ((atW P W T).localFun T).a from rfl, atW_localFun T hP hev]; rfl

theorem atW_b : (atW P W T).b T = AdmWindow.bv (W T) (P.L T) := by
  rw [show (atW P W T).b T = ((atW P W T).localFun T).b from rfl, atW_localFun T hP hev]; rfl

theorem atW_phiHat : (atW P W T).phiHat T = AdmWindow.vHat (W T) := by
  show AdmWindow.vHat ((atW P W T).phi T) = _
  rw [atW_phi_valid T hP hev]

theorem atW_phiHatR : (atW P W T).phiHatR T = AdmWindow.vHatR (W T) := by
  show AdmWindow.vHatR ((atW P W T).phi T) = _
  rw [atW_phi_valid T hP hev]

/-- the prime-side traces of `atW P W T` at height T are the abstract-layer traces of `W T`. -/
theorem atW_trGtilde :
    (atW P W T).trGtilde T = PrimeSide.trGtA (P.toSetting T) (AdmWindow.localFun (W T) (P.L T)) := by
  rw [← PrimeSide.trGtA_concrete (atW P W T) T, atW_localFun T hP hev]; rfl

theorem atW_trGtildeSq :
    (atW P W T).trGtildeSq T = PrimeSide.trGt2A (P.toSetting T) (AdmWindow.localFun (W T) (P.L T)) := by
  rw [← PrimeSide.trGt2A_concrete (atW P W T) T, atW_localFun T hP hev]; rfl

end

end AMW

end

/-! ###### AMW module: Trig ###### -/

/-
AMW/Trig.lean — rational enclosures of sin and cos for kernel-checked certificates.

The twelve-term Taylor bound (|e^{iθ} − Σ_{m<12}(iθ)^m/m!| ≤ |θ|^12·13/5748019200 for |θ| ≤ 1, from
`Complex.exp_bound`) with monotonicity of sin and cos on [0, 1], in rational Horner form, rounded
outwards to 10⁻¹⁰.  `sinPiI t` encloses sin(πt) for t ∈ ℚ: t = k/2 + r with |r| ≤ 1/4 and
(cos, sin)(πk/2) ∈ {0, ±1}².  Adapted from the ThreePoint layer of the Zeta Lab bridge (MIT), as
carried in SolutionSevW10D.lean.
-/

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

/-! ###### AMW module: Adm ###### -/

/-
AMW/Adm.lean — a modulated ramp taper whose factor has small POSITIVE VARIATION is an admissible window.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/XiPrime/QuarticWindow/ModWindow.lean, with the hypothesis `ModFactor.antitone` replaced by a
positive-variation budget.  For the tree's ramp taper φ = Taper.phi ϱ L w and a factor f that is even,
nonnegative, ≤ 1 on the core [−L/2, L/2], C² near it, with |f′| ≤ A/L, |f″| ≤ B/L² there, and
    ∫₀^{L/2} max(f′, 0) ≤ ρ,   f(0) + 2ρ ≤ 1,   f(0)² + 4ρ ≤ 1,
the window φ_f := f·φ satisfies `AdmWindow φ_f L w (cMod ϱ A B)`.
Mechanism for the first-derivative norms: |x| = 2·max(x,0) − x and the FTC give
‖g′‖₁ = 2(2∫₀^{L/2} max(g′,0) + g(0)) for an even C¹ g supported in [−L/2, L/2]; the taper is
nonincreasing in [0,1], so max((fφ)′,0) ≤ max(f′,0), and (φ_f²)′ = 2φ_f φ_f′ with 0 ≤ φ_f ≤ 1.
The second-derivative norms are ModWindow's (they never used monotonicity).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

/-- hypotheses on a modulating factor (in the u-variable), positive-variation form. -/
structure PVFactor (f : ℝ → ℝ) (L A B ρ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  even : ∀ u, f (-u) = f u
  nonneg : ∀ u, 0 ≤ f u
  le_one : ∀ u, |u| ≤ L / 2 → f u ≤ 1
  smooth : ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ 2 f (Ioo (-(L / 2 + δ)) (L / 2 + δ))
  deriv_le : ∀ u, |u| ≤ L / 2 → |deriv f u| ≤ A / L
  deriv2_le : ∀ u, |u| ≤ L / 2 → |deriv (deriv f) u| ≤ B / L ^ 2
  posVar : ∫ u in (0:ℝ)..(L / 2), max (deriv f u) 0 ≤ ρ
  budget : f 0 + 2 * ρ ≤ 1
  budget_sq : f 0 ^ 2 + 4 * ρ ≤ 1

/-- the modulated window φ_f := f · φ. -/
def phiM (f : ℝ → ℝ) (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := f u * Taper.phi ϱ L w u

/-- its window constant. -/
def cMod (ϱ : ℝ → ℝ) (A B : ℝ) : ℝ := Taper.cRho ϱ + A + A ^ 2 + B

variable {f : ℝ → ℝ} {ϱ : ℝ → ℝ} {L w A B ρ : ℝ}

/-! ### pointwise / support facts -/

theorem phiM_even (hf : PVFactor f L A B ρ) (u : ℝ) : phiM f ϱ L w (-u) = phiM f ϱ L w u := by
  simp only [phiM, hf.even, Taper.phi_even]

theorem phiM_nonneg (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiM f ϱ L w u :=
  mul_nonneg (hf.nonneg u) (Taper.phi_nonneg hϱ u)

theorem phiM_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phiM f ϱ L w u = 0 := by
  simp only [phiM, Taper.phi_eq_zero hϱ hw hu, mul_zero]

theorem phiM_le_one (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) :
    phiM f ϱ L w u ≤ 1 := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [phiM_eq_zero hϱ hw hu]; exact zero_le_one
  · calc phiM f ϱ L w u ≤ 1 * 1 :=
          mul_le_mul (hf.le_one u hu.le) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
      _ = 1 := mul_one 1

theorem phiM_zero_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) : phiM f ϱ L w 0 ≤ f 0 :=
  mul_le_of_le_one_right (hf.nonneg 0) (Taper.phi_le_one hϱ 0)

/-- φ_f is C² (f is C² near the core; beyond the core φ_f vanishes identically). -/
theorem phiM_contDiff (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (phiM f ϱ L w) := by
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge |u| (L / 2 + δ) with hu | hu
  · have hmem : u ∈ Ioo (-(L / 2 + δ)) (L / 2 + δ) := by
      constructor <;> linarith [neg_abs_le u, le_abs_self u]
    have hfu : ContDiffAt ℝ 2 f u := hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    exact hfu.mul ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt
  · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
    have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
      simp only [mem_setOf_eq]; linarith
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0)) ?_
    filter_upwards [hopen.mem_nhds hmem] with v hv
    exact phiM_eq_zero hϱ hw hv.le

/-- the ramp taper is nonincreasing on [0, ∞). -/
theorem phi_antitoneOn (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    AntitoneOn (Taper.phi ϱ L w) (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  unfold Taper.phi
  apply hϱ.monotone
  rw [abs_of_nonneg hx, abs_of_nonneg hy]
  gcongr

theorem deriv_phi_nonpos (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : 0 < u) :
    deriv (Taper.phi ϱ L w) u ≤ 0 := by
  rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hu)]
  exact (phi_antitoneOn hϱ hw).derivWithin_nonpos

/-! ### total variation from positive variation -/

/-- an even C¹ function supported in [−M, M] whose positive variation on [0, M] is at most ρ, with
f(0) + 2ρ ≤ 1, has ∫|f′| ≤ 2. -/
theorem integral_abs_deriv_le_two_of_posVar {g : ℝ → ℝ} {M ρ : ℝ} (hM : 0 < M)
    (hg : ContDiff ℝ 1 g) (heven : ∀ x, g (-x) = g x)
    (hsupp : ∀ x, M ≤ |x| → g x = 0)
    (hpos : ∫ u in (0:ℝ)..M, max (deriv g u) 0 ≤ ρ) (hbud : g 0 + 2 * ρ ≤ 1) :
    ∫ u, |deriv g u| ≤ 2 := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd' : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hderiv0 : ∀ x : ℝ, M < |x| → deriv g x = 0 := by
    intro x hx
    have hopen : IsOpen {v : ℝ | M < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hEq : g =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds hx] with v hv
      exact hsupp v (le_of_lt hv)
    rw [hEq.deriv_eq, deriv_const]
  have hodd : ∀ x : ℝ, |deriv g (-x)| = |deriv g x| := by
    intro x
    have hfe : (fun y : ℝ => g (-y)) = g := funext heven
    have h := deriv_comp_neg (f := g) (x := x)
    rw [hfe] at h
    have h' : deriv g (-x) = -deriv g x := by linarith
    rw [h', abs_neg]
  have habs : (fun u : ℝ => |deriv g u|) = fun u => (fun t => |deriv g t|) |u| := by
    funext u
    show |deriv g u| = |deriv g (|u|)|
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hodd]
  have hhalf : ∫ u, |deriv g u| = 2 * ∫ u in Set.Ioi 0, |deriv g u| := by
    conv_lhs => rw [habs]
    exact integral_comp_abs (f := fun t => |deriv g t|)
  have hcs : HasCompactSupport (deriv g) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    apply hderiv0
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    rcases hmem with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hint : Integrable (fun u => |deriv g u|) := (hd'.integrable_of_hasCompactSupport hcs).abs
  have hsplit : ∫ u in Set.Ioi 0, |deriv g u|
      = (∫ u in Set.Ioc 0 M, |deriv g u|) + ∫ u in Set.Ioi M, |deriv g u| := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hM.le]
  have hfar : ∫ u in Set.Ioi M, |deriv g u| = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hderiv0 x (by rw [abs_of_pos (lt_trans hM hx)]; exact hx), abs_zero]
  have hpt : ∀ x : ℝ, |deriv g x| = 2 * max (deriv g x) 0 - deriv g x := by
    intro x
    rcases le_or_gt 0 (deriv g x) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have hmaxc : Continuous fun x => max (deriv g x) 0 := hd'.max continuous_const
  have hFTC : ∫ u in (0:ℝ)..M, deriv g u = g M - g 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) ((hd'.intervalIntegrable) 0 M)
  have hnear : ∫ u in Set.Ioc 0 M, |deriv g u|
      = 2 * (∫ u in (0:ℝ)..M, max (deriv g u) 0) - (g M - g 0) := by
    rw [← intervalIntegral.integral_of_le hM.le]
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub ((hmaxc.intervalIntegrable 0 M).const_mul 2)
        (hd'.intervalIntegrable 0 M), intervalIntegral.integral_const_mul, hFTC]
  have hgM : g M = 0 := hsupp M (by rw [abs_of_pos hM])
  rw [hhalf, hsplit, hfar, hnear, hgM]
  linarith

/-- the product step: where f ≥ 0 and the taper τ is in [0, 1] and nonincreasing, the positive part
of (f·τ)′ is at most that of f′. -/
theorem max_deriv_mul_le {f τ : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hτ : DifferentiableAt ℝ τ x) (hf0 : 0 ≤ f x) (hτ0 : 0 ≤ τ x) (hτ1 : τ x ≤ 1)
    (hτ' : deriv τ x ≤ 0) :
    max (deriv (fun u => f u * τ u) x) 0 ≤ max (deriv f x) 0 := by
  rw [deriv_fun_mul hf hτ]
  refine max_le ?_ (le_max_right _ _)
  have h1 : f x * deriv τ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0 hτ'
  have h2 : deriv f x * τ x ≤ max (deriv f x) 0 := by
    rcases le_or_gt 0 (deriv f x) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h.le]; nlinarith
  linarith

/-- positive variation of φ_f on [0, L/2] is at most that of f. -/
theorem posVar_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u in (0:ℝ)..(L / 2), max (deriv (phiM f ϱ L w) u) 0 ≤ ρ := by
  have hL : 0 < L := by linarith
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  have hU : IsOpen (Ioo (-(L / 2 + δ)) (L / 2 + δ)) := isOpen_Ioo
  have hφ := phiM_contDiff hf hϱ hw hwL
  have hτ : ContDiff ℝ 2 (Taper.phi ϱ L w) := (Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)
  have hcore : Icc (0:ℝ) (L / 2) ⊆ Ioo (-(L / 2 + δ)) (L / 2 + δ) := fun u hu => by
    constructor <;> linarith [hu.1, hu.2]
  have hf'c : ContinuousOn (deriv f) (Icc (0:ℝ) (L / 2)) :=
    ((hsm.continuousOn_deriv_of_isOpen hU (by norm_num))).mono hcore
  refine le_trans ?_ hf.posVar
  refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) ?_ ?_ ?_
  · exact ((hφ.continuous_deriv (by norm_num)).max continuous_const).intervalIntegrable _ _
  · exact (ContinuousOn.sup hf'c continuousOn_const).intervalIntegrable_of_Icc (by linarith)
  · intro u hu
    have huU : u ∈ Ioo (-(L / 2 + δ)) (L / 2 + δ) := hcore (Ioo_subset_Icc_self hu)
    have hfd : DifferentiableAt ℝ f u :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds huU)
    exact max_deriv_mul_le hfd (hτ.differentiable (by norm_num) u) (hf.nonneg u)
      (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) (deriv_phi_nonpos hϱ hw hu.1)

/-! ### first-derivative norms -/

theorem integral_abs_deriv_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ∫ u, |deriv (phiM f ϱ L w) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  refine integral_abs_deriv_le_two_of_posVar (by positivity : (0:ℝ) < L / 2)
    ((phiM_contDiff hf hϱ hw hwL).of_le (by norm_num)) (phiM_even hf)
    (fun x hx => phiM_eq_zero hϱ hw hx) (posVar_phiM_le hf hϱ hw hwL) ?_
  linarith [phiM_zero_le (w := w) hf hϱ, hf.budget]

theorem integral_abs_deriv_phiM_sq_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ∫ u, |deriv (fun u => phiM f ϱ L w u ^ 2) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  have hφ := phiM_contDiff hf hϱ hw hwL
  have hφd : Differentiable ℝ (phiM f ϱ L w) := hφ.differentiable (by norm_num)
  have hφ'c : Continuous (deriv (phiM f ϱ L w)) := hφ.continuous_deriv (by norm_num)
  have hdsq : ∀ u, deriv (fun u => phiM f ϱ L w u ^ 2) u = 2 * phiM f ϱ L w u * deriv (phiM f ϱ L w) u :=
    fun u => by
      rw [((hφd u).hasDerivAt.fun_pow 2).deriv]; push_cast; ring
  have hpos : ∫ u in (0:ℝ)..(L / 2), max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0 ≤ 2 * ρ := by
    have hpt : ∀ u, max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0
        ≤ 2 * max (deriv (phiM f ϱ L w) u) 0 := fun u => by
      rw [hdsq]
      have h0 := phiM_nonneg (w := w) hf hϱ u
      have h1 := phiM_le_one hf hϱ hw u
      refine max_le ?_ (by positivity)
      rcases le_or_gt 0 (deriv (phiM f ϱ L w) u) with h | h
      · rw [max_eq_left h]; nlinarith
      · rw [max_eq_right h.le]; nlinarith
    have hc1 : Continuous fun u => max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0 := by
      simp_rw [hdsq]
      exact ((continuous_const.mul hφ.continuous).mul hφ'c).max continuous_const
    have hc2 : Continuous fun u => 2 * max (deriv (phiM f ϱ L w) u) 0 :=
      continuous_const.mul (hφ'c.max continuous_const)
    calc ∫ u in (0:ℝ)..(L / 2), max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0
        ≤ ∫ u in (0:ℝ)..(L / 2), 2 * max (deriv (phiM f ϱ L w) u) 0 :=
          intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
            (hc2.intervalIntegrable _ _) fun u _ => hpt u
      _ = 2 * ∫ u in (0:ℝ)..(L / 2), max (deriv (phiM f ϱ L w) u) 0 :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * ρ := by linarith [posVar_phiM_le hf hϱ hw hwL]
  refine integral_abs_deriv_le_two_of_posVar (by positivity : (0:ℝ) < L / 2)
    ((hφ.pow 2).of_le (by norm_num)) (fun x => by rw [phiM_even hf])
    (fun x hx => by rw [phiM_eq_zero hϱ hw hx, zero_pow two_ne_zero]) hpos ?_
  have h0 := phiM_zero_le (w := w) hf hϱ
  have h00 := phiM_nonneg (w := w) hf hϱ 0
  have : phiM f ϱ L w 0 ^ 2 ≤ f 0 ^ 2 := pow_le_pow_left₀ h00 h0 2
  linarith [hf.budget_sq]

/-! ### second derivatives of products (the factor C² only near the core) -/

/-- product rule, twice, on an open set where both factors are C². -/
theorem deriv2_mul_eq {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
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

/-- first product rule on the open set. -/
theorem deriv_mul_eq {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) {u : ℝ} (hu : u ∈ U) :
    deriv (fun v => F v * G v) u = deriv F u * G u + F u * deriv G u :=
  deriv_mul ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))
    ((hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))

/-- a function vanishing on an open set has vanishing first and second derivatives there. -/
theorem deriv2_eq_zero_of_eqOn {H : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) (hz : ∀ v ∈ V, H v = 0)
    {u : ℝ} (hu : u ∈ V) : deriv H u = 0 ∧ deriv (deriv H) u = 0 := by
  have hd : ∀ v ∈ V, deriv H v = 0 := by
    intro v hv
    have : H =ᶠ[nhds v] fun _ => (0:ℝ) := by
      filter_upwards [hV.mem_nhds hv] with x hx using hz x hx
    rw [this.deriv_eq, deriv_const]
  refine ⟨hd u hu, ?_⟩
  have : deriv H =ᶠ[nhds u] fun _ => (0:ℝ) := by
    filter_upwards [hV.mem_nhds hu] with x hx using hd x hx
  rw [this.deriv_eq, deriv_const]

/-- integrability of |h| for a continuous compactly supported h. -/
theorem integrable_abs_of_cs {h : ℝ → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    Integrable (fun u => |h u|) :=
  (hc.abs).integrable_of_hasCompactSupport (hcs.comp_left (g := fun t => |t|) abs_zero)

/-- **‖(F·G)″‖₁ ≤ B′‖G‖₁ + 2A′‖G′‖₁ + ‖G″‖₁** for G ∈ C_c²[−L/2, L/2] and F C² near [−L/2, L/2] with
|F| ≤ 1, |F′| ≤ A′, |F″| ≤ B′ there. -/
theorem integral_abs_deriv2_mul_le {F G : ℝ → ℝ} {L δ A' B' : ℝ} (hδ : 0 < δ)
    (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hF : ContDiffOn ℝ 2 F (Ioo (-(L / 2 + δ)) (L / 2 + δ)))
    (hF0 : ∀ u, |u| ≤ L / 2 → |F u| ≤ 1) (hF1 : ∀ u, |u| ≤ L / 2 → |deriv F u| ≤ A')
    (hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv F) u| ≤ B')
    (hG : ContDiff ℝ 2 G) (hGcs : HasCompactSupport G) (hGzero : ∀ u, L / 2 < |u| → G u = 0)
    (hH : ContDiff ℝ 2 (fun u => F u * G u)) (hHcs : HasCompactSupport (fun u => F u * G u)) :
    ∫ u, |deriv (deriv (fun u => F u * G u)) u|
      ≤ B' * (∫ u, |G u|) + 2 * A' * (∫ u, |deriv G u|) + ∫ u, |deriv (deriv G) u| := by
  set U : Set ℝ := Ioo (-(L / 2 + δ)) (L / 2 + δ) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  set H : ℝ → ℝ := fun u => F u * G u with hHdef
  have hpt : ∀ u, |deriv (deriv H) u| ≤ B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u| := by
    intro u
    rcases le_or_gt |u| (L / 2) with hu | hu
    · have huU : u ∈ U := by
        simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
      rw [deriv2_mul_eq hU hF hG.contDiffOn huU]
      have h0 := hF0 u hu; have h1 := hF1 u hu; have h2 := hF2 u hu
      calc |deriv (deriv F) u * G u + 2 * (deriv F u * deriv G u) + F u * deriv (deriv G) u|
          ≤ |deriv (deriv F) u * G u| + |2 * (deriv F u * deriv G u)| + |F u * deriv (deriv G) u| :=
            abs_add_three _ _ _
        _ ≤ B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
            have hg0 := abs_nonneg (G u); have hg1 := abs_nonneg (deriv G u)
            have hg2 := abs_nonneg (deriv (deriv G) u)
            have e1 : |deriv (deriv F) u| * |G u| ≤ B' * |G u| := mul_le_mul_of_nonneg_right h2 hg0
            have e2 : 2 * (|deriv F u| * |deriv G u|) ≤ 2 * A' * |deriv G u| := by
              nlinarith [mul_le_mul_of_nonneg_right h1 hg1]
            have e3 : |F u| * |deriv (deriv G) u| ≤ |deriv (deriv G) u| := by
              nlinarith [mul_le_mul_of_nonneg_right h0 hg2]
            linarith
    · have hV : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      have hz : ∀ v ∈ {v : ℝ | L / 2 < |v|}, H v = 0 := fun v hv => by
        simp only [hHdef, hGzero v hv, mul_zero]
      rw [(deriv2_eq_zero_of_eqOn hV hz hu).2, abs_zero]
      positivity
  have hH2c : Continuous (deriv (deriv H)) := (hH.deriv' (n := 1)).continuous_deriv le_rfl
  have hG1c : Continuous (deriv G) := (hG.deriv' (n := 1)).continuous
  have hG2c : Continuous (deriv (deriv G)) := (hG.deriv' (n := 1)).continuous_deriv le_rfl
  have iH : Integrable (fun u => |deriv (deriv H) u|) := integrable_abs_of_cs hH2c hHcs.deriv.deriv
  have iG : Integrable (fun u => |G u|) := integrable_abs_of_cs hG.continuous hGcs
  have iG1 : Integrable (fun u => |deriv G u|) := integrable_abs_of_cs hG1c hGcs.deriv
  have iG2 : Integrable (fun u => |deriv (deriv G) u|) := integrable_abs_of_cs hG2c hGcs.deriv.deriv
  have iR : Integrable (fun u => B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|) :=
    ((iG.const_mul B').add (iG1.const_mul (2 * A'))).add iG2
  calc ∫ u, |deriv (deriv H) u|
      ≤ ∫ u, (B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|) := integral_mono iH iR hpt
    _ = B' * (∫ u, |G u|) + 2 * A' * (∫ u, |deriv G u|) + ∫ u, |deriv (deriv G) u| := by
        have s1 : ∫ u, (B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|)
            = (∫ u, (B' * |G u| + 2 * A' * |deriv G u|)) + ∫ u, |deriv (deriv G) u| :=
          integral_add ((iG.const_mul B').add (iG1.const_mul (2 * A'))) iG2
        have s2 : ∫ u, (B' * |G u| + 2 * A' * |deriv G u|)
            = (∫ u, B' * |G u|) + ∫ u, 2 * A' * |deriv G u| :=
          integral_add (iG.const_mul B') (iG1.const_mul (2 * A'))
        rw [s1, s2, integral_const_mul, integral_const_mul]

/-! ### the L¹ size of the taper and its square -/

theorem integral_abs_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |Taper.phi ϱ L w u| ≤ L := by
  have hL : 0 < L := by linarith
  have heq : ∫ u, |Taper.phi ϱ L w u| = ∫ u in Icc (-(L / 2)) (L / 2), |Taper.phi ϱ L w u| := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    have habs : L / 2 ≤ |u| := by
      rcases hu with h | h
      · linarith [neg_le_abs u]
      · linarith [le_abs_self u]
    rw [Taper.phi_eq_zero hϱ hw habs, abs_zero]
  rw [heq]
  calc ∫ u in Icc (-(L / 2)) (L / 2), |Taper.phi ϱ L w u|
      ≤ ∫ u in Icc (-(L / 2)) (L / 2), (1:ℝ) := by
        refine setIntegral_mono_on ?_ (by simp) measurableSet_Icc fun u _ => ?_
        · exact ((Taper.phi_continuous hϱ hw hwL).abs.integrableOn_Icc)
        · rw [abs_of_nonneg (Taper.phi_nonneg hϱ u)]; exact Taper.phi_le_one hϱ u
    _ = L := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

theorem integral_abs_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ L := by
  have hL : 0 < L := by linarith
  have ha := Taper.aConst_le_one hϱ hw hwL
  unfold Taper.aConst at ha
  have habs : (fun u => |Taper.phi ϱ L w u ^ 2|) = fun u => Taper.phi ϱ L w u ^ 2 :=
    funext fun u => abs_of_nonneg (sq_nonneg _)
  rw [habs]
  rwa [inv_mul_le_iff₀ hL, mul_one] at ha

/-! ### second-derivative norms of φ_f and φ_f² -/

theorem l1Deriv2_nonneg' (ϱ : ℝ → ℝ) : 0 ≤ Taper.l1Deriv2 ϱ := integral_nonneg fun _ => abs_nonneg _

theorem phiM_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) : HasCompactSupport (phiM f ϱ L w) :=
  (Taper.phi_hasCompactSupport hϱ (L := L) hw).mul_left

/-- |f| ≤ 1 on the core. -/
theorem PVFactor.abs_le_one (hf : PVFactor f L A B ρ) (u : ℝ) (hu : |u| ≤ L / 2) : |f u| ≤ 1 := by
  rw [abs_of_nonneg (hf.nonneg u)]; exact hf.le_one u hu

/-- **‖φ_f″‖₁ ≤ cMod/w.** -/
theorem integral_abs_deriv2_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : ∫ u, |deriv (deriv (phiM f ϱ L w)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  have hmain := integral_abs_deriv2_mul_le (F := f) (G := Taper.phi ϱ L w) (L := L) hδ
    (div_nonneg hf.A_nonneg hL.le) (div_nonneg hf.B_nonneg (sq_nonneg L)) hsm hf.abs_le_one hf.deriv_le
    hf.deriv2_le ((Taper.phi_contDiff hϱ hw0 h2wL).of_le (by norm_num)) (Taper.phi_hasCompactSupport hϱ hw0)
    (fun u hu => Taper.phi_eq_zero hϱ hw0 hu.le) (phiM_contDiff hf hϱ hw0 h2wL)
    (phiM_hasCompactSupport hϱ hw0)
  have hI0 := integral_abs_phi_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (Taper.phi ϱ L w) u| = 2 := Taper.integral_abs_deriv_phi hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (Taper.phi ϱ L w)) u| = 2 * Taper.l1Deriv2 ϱ / w :=
    Taper.integral_abs_deriv2_phi hϱ hw0 h2wL
  rw [hI1, hI2] at hmain
  have hc := Taper.two_mul_l1Deriv2_le_cRho hϱ
  have hl1 := l1Deriv2_nonneg' ϱ
  have hA := hf.A_nonneg; have hB := hf.B_nonneg
  refine hmain.trans ?_
  have e1 : B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / w := by
    calc B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / L ^ 2 * L := by gcongr
      _ = B / L := by field_simp
      _ ≤ B / w := div_le_div_of_nonneg_left hB hw0 (by linarith)
  have e2 : 2 * (A / L) * 2 ≤ A / w := by
    rw [show 2 * (A / L) * 2 = 4 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  have e3 : 2 * Taper.l1Deriv2 ϱ / w ≤ Taper.cRho ϱ / w := div_le_div_of_nonneg_right hc hw0.le
  have e4 : 0 ≤ A ^ 2 / w := by positivity
  calc B / L ^ 2 * (∫ u, |Taper.phi ϱ L w u|) + 2 * (A / L) * 2 + 2 * Taper.l1Deriv2 ϱ / w
      ≤ B / w + A / w + Taper.cRho ϱ / w + A ^ 2 / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-- φ_f² as a product of the squared factor and the squared taper. -/
theorem phiM_sq_eq : (fun u => phiM f ϱ L w u ^ 2) = fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2) := by
  funext u; simp only [phiM]; ring

/-- **‖(φ_f²)″‖₁ ≤ cMod/w.** -/
theorem integral_abs_deriv2_phiM_sq_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : ∫ u, |deriv (deriv (fun u => phiM f ϱ L w u ^ 2)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  set U : Set ℝ := Ioo (-(L / 2 + δ)) (L / 2 + δ) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hcore : ∀ u, |u| ≤ L / 2 → u ∈ U := fun u hu => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm2 : ContDiffOn ℝ 2 (fun u => f u * f u) U := hsm.mul hsm
  have hA := hf.A_nonneg; have hB := hf.B_nonneg
  have hF0 : ∀ u, |u| ≤ L / 2 → |f u * f u| ≤ 1 := fun u hu => by
    rw [abs_mul]; have := hf.abs_le_one u hu; nlinarith [abs_nonneg (f u)]
  have hF1 : ∀ u, |u| ≤ L / 2 → |deriv (fun u => f u * f u) u| ≤ 2 * A / L := fun u hu => by
    rw [deriv_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu
    calc |deriv f u * f u + f u * deriv f u| = 2 * (|f u| * |deriv f u|) := by
          rw [show deriv f u * f u + f u * deriv f u = 2 * (f u * deriv f u) by ring, abs_mul, abs_mul,
            abs_two]
      _ ≤ 2 * (1 * (A / L)) := by gcongr
      _ = 2 * A / L := by ring
  have hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv (fun u => f u * f u)) u| ≤ (2 * B + 2 * A ^ 2) / L ^ 2 :=
    fun u hu => by
    rw [deriv2_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu; have h2 := hf.deriv2_le u hu
    have hd0 := abs_nonneg (deriv f u)
    calc |deriv (deriv f) u * f u + 2 * (deriv f u * deriv f u) + f u * deriv (deriv f) u|
        ≤ |deriv (deriv f) u * f u| + |2 * (deriv f u * deriv f u)| + |f u * deriv (deriv f) u| :=
          abs_add_three _ _ _
      _ = 2 * (|deriv (deriv f) u| * |f u|) + 2 * (|deriv f u| * |deriv f u|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
      _ ≤ 2 * (B / L ^ 2 * 1) + 2 * (A / L * (A / L)) := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L ^ 2 := by field_simp
  have hφ := Taper.phi_contDiff hϱ hw0 h2wL
  have hG : ContDiff ℝ 2 (fun u => Taper.phi ϱ L w u ^ 2) := (hφ.pow 2).of_le (by norm_num)
  have hGcs : HasCompactSupport (fun u => Taper.phi ϱ L w u ^ 2) :=
    (Taper.phi_hasCompactSupport hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hGzero : ∀ u, L / 2 < |u| → Taper.phi ϱ L w u ^ 2 = 0 := fun u hu => by
    rw [Taper.phi_eq_zero hϱ hw0 hu.le, zero_pow two_ne_zero]
  have hH : ContDiff ℝ 2 (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (phiM_contDiff hf hϱ hw0 h2wL).pow 2
  have hHcs : HasCompactSupport (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (phiM_hasCompactSupport hϱ hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hmain := integral_abs_deriv2_mul_le (F := fun u => f u * f u) (G := fun u => Taper.phi ϱ L w u ^ 2)
    (L := L) hδ (by positivity : (0:ℝ) ≤ 2 * A / L) (by positivity : (0:ℝ) ≤ (2 * B + 2 * A ^ 2) / L ^ 2)
    hsm2 hF0 hF1 hF2 hG hGcs hGzero hH hHcs
  rw [phiM_sq_eq]
  have hI0 := integral_abs_phi_sq_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (fun u => Taper.phi ϱ L w u ^ 2) u| = 2 := Taper.integral_abs_deriv_phi_sq hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u| ≤ Taper.cRho ϱ / w :=
    Taper.integral_abs_deriv2_phi_sq_le hϱ hw h2wL
  rw [hI1] at hmain
  refine hmain.trans ?_
  have e1 : (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ (B + A ^ 2) / w := by
    calc (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2|
        ≤ (2 * B + 2 * A ^ 2) / L ^ 2 * L := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L := by field_simp
      _ ≤ (B + A ^ 2) / w := by rw [div_le_div_iff₀ hL hw0]; nlinarith
  have e2 : 2 * (2 * A / L) * 2 ≤ A / w := by
    rw [show 2 * (2 * A / L) * 2 = 8 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  calc (2 * B + 2 * A ^ 2) / L ^ 2 * (∫ u, |Taper.phi ϱ L w u ^ 2|) + 2 * (2 * A / L) * 2
        + ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u|
      ≤ (B + A ^ 2) / w + A / w + Taper.cRho ϱ / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-! ### the admissible-window instance -/

theorem four_le_cMod (hϱ : TaperProfile ϱ) (hA : 0 ≤ A) (hB : 0 ≤ B) : 4 ≤ cMod ϱ A B := by
  have := Taper.four_le_cRho hϱ
  simp only [cMod]; nlinarith [sq_nonneg A]

/-- **A modulated ramp taper with a positive-variation factor is an admissible window.** -/
theorem admWindow_phiM (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (phiM f ϱ L w) L w (cMod ϱ A B) where
  one_le_w := hw
  w8 := hwL
  four_le_c := four_le_cMod hϱ hf.A_nonneg hf.B_nonneg
  even := phiM_even hf
  nonneg := phiM_nonneg hf hϱ
  le_one := phiM_le_one hf hϱ (by linarith)
  contDiff := phiM_contDiff hf hϱ (by linarith) (by linarith)
  support := fun _ hu => phiM_eq_zero hϱ (by linarith) hu
  l1_deriv := integral_abs_deriv_phiM_le hf hϱ (by linarith) (by linarith)
  l1_deriv_sq := integral_abs_deriv_phiM_sq_le hf hϱ (by linarith) (by linarith)
  l1_deriv2 := integral_abs_deriv2_phiM_le hf hϱ hw hwL
  l1_deriv2_sq := integral_abs_deriv2_phiM_sq_le hf hϱ hw hwL

end AMW

end

/-! ###### AMW module: Profile ###### -/

/-
AMW/Profile.lean — a profile p on the unit window gives a positive-variation factor.

f_p(u) := √(p(u/L)) (Real.sqrt is 0 on negatives, so no guard is needed).  If p is even, C², positive on |s| ≤ 1/2 + δ, with 1/4 ≤ p ≤ 1, |p′| ≤ A₁,
|p″| ≤ A₂ on the core |s| ≤ 1/2, positive variation ∫₀^{1/2} max(p′,0) ≤ ρ and the budgets
√p(0) + 2ρ ≤ 1, p(0) + 4ρ ≤ 1, then f_p is a `PVFactor` with constants (A₁, A₂ + 2A₁², ρ):
h := p(·/L) = f_p² on the smooth region, f_p ≥ 1/2 on the core, f_p′ = h′/(2f_p) and
f_p″ = (h″ − 2f_p′²)/(2f_p); the positive variation of f_p is at most that of p since 2f_p ≥ 1.
Pattern of Zeta23/XiPrime/QuarticWindow/Quartic.lean (anthropics/zeta-23-lean, Apache-2.0).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace AMW

open Zeta23

/-- hypotheses on a profile on the unit window. -/
structure Profile (p : ℝ → ℝ) (δ A₁ A₂ ρ : ℝ) : Prop where
  δ_pos : 0 < δ
  A₁_nonneg : 0 ≤ A₁
  A₂_nonneg : 0 ≤ A₂
  even : ∀ s, p (-s) = p s
  contDiff : ContDiff ℝ 2 p
  pos : ∀ s, |s| ≤ 1 / 2 + δ → 0 < p s
  ge_quarter : ∀ s, |s| ≤ 1 / 2 → 1 / 4 ≤ p s
  le_one : ∀ s, |s| ≤ 1 / 2 → p s ≤ 1
  deriv_le : ∀ s, |s| ≤ 1 / 2 → |deriv p s| ≤ A₁
  deriv2_le : ∀ s, |s| ≤ 1 / 2 → |deriv (deriv p) s| ≤ A₂
  posVar : ∫ s in (0:ℝ)..(1 / 2), max (deriv p s) 0 ≤ ρ
  budget : Real.sqrt (p 0) + 2 * ρ ≤ 1
  budget_sq : p 0 + 4 * ρ ≤ 1

/-- the factor of a profile, in the u-variable. -/
def fP (p : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (p (u / L))

variable {p : ℝ → ℝ} {δ A₁ A₂ ρ L : ℝ}

section
variable (hp : Profile p δ A₁ A₂ ρ) (hL : 0 < L)
include hp hL

/-- the smooth region U := (−(L/2 + δL), L/2 + δL). -/
lemma pos_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) : 0 < p (u / L) := by
  apply hp.pos
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
  constructor <;> nlinarith [hu.1, hu.2]

lemma fP_eq_sqrt_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
    fP p L u = Real.sqrt (p (u / L)) := by
  rfl

lemma hasDerivAt_comp_div (u : ℝ) : HasDerivAt (fun u => p (u / L)) (deriv p (u / L) / L) u := by
  have h1 : HasDerivAt (fun x : ℝ => x / L) (1 / L) u := by
    simpa using (hasDerivAt_id u).div_const L
  exact (((hp.contDiff.differentiable (by norm_num)) (u / L)).hasDerivAt.comp u h1).congr_deriv (by ring)

lemma deriv_comp_div : deriv (fun u => p (u / L)) = fun u => deriv p (u / L) / L :=
  funext fun u => (hasDerivAt_comp_div hp hL u).deriv

lemma deriv2_comp_div (u : ℝ) :
    deriv (deriv (fun u => p (u / L))) u = deriv (deriv p) (u / L) / L ^ 2 := by
  rw [deriv_comp_div hp hL]
  have hd : Differentiable ℝ (deriv p) := (hp.contDiff.deriv' (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun x : ℝ => x / L) (1 / L) u := by
    simpa using (hasDerivAt_id u).div_const L
  have h2 : HasDerivAt (fun u => deriv p (u / L) / L) (deriv (deriv p) (u / L) / L ^ 2) u := by
    exact (((hd (u / L)).hasDerivAt.comp u h1).div_const L).congr_deriv
      (show deriv (deriv p) (u / L) * (1 / L) / L = deriv (deriv p) (u / L) / L ^ 2 by ring)
  exact h2.deriv

lemma fP_contDiffOn : ContDiffOn ℝ 2 (fP p L) (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := by
  have hc : ContDiff ℝ 2 (fun u => p (u / L)) := hp.contDiff.comp (contDiff_id.div_const L)
  have h1 : ContDiffOn ℝ 2 (fun u => Real.sqrt (p (u / L))) (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :=
    hc.contDiffOn.sqrt fun u hu => (pos_of_mem hp hL hu).ne'
  exact h1.congr fun u hu => fP_eq_sqrt_of_mem hp hL hu

lemma fP_mul_self_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
    fP p L u * fP p L u = p (u / L) := by
  rw [fP_eq_sqrt_of_mem hp hL hu, ← sq, Real.sq_sqrt (pos_of_mem hp hL hu).le]

lemma core_abs {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith

lemma core_mem {u : ℝ} (hu : |u| ≤ L / 2) : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) := by
  have := hp.δ_pos
  have hδL : 0 < δ * L := mul_pos this hL
  constructor <;> linarith [neg_abs_le u, le_abs_self u]

lemma fP_core_ge {u : ℝ} (hu : |u| ≤ L / 2) : 1 / 2 ≤ fP p L u := by
  have h := hp.ge_quarter _ (core_abs hp hL hu)
  rw [fP]
  refine Real.le_sqrt_of_sq_le ?_
  linarith

lemma fP_le_one {u : ℝ} (hu : |u| ≤ L / 2) : fP p L u ≤ 1 := by
  rw [fP, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (hp.le_one _ (core_abs hp hL hu))

/-- f_p′ = h′/(2 f_p) on the smooth region. -/
lemma deriv_fP_eq {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
    deriv (fP p L) u * (2 * fP p L u) = deriv p (u / L) / L := by
  have hU : IsOpen (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := isOpen_Ioo
  have hsm := fP_contDiffOn hp hL
  have hev : (fun v => fP p L v * fP p L v) =ᶠ[nhds u] fun v => p (v / L) := by
    filter_upwards [hU.mem_nhds hu] with v hv using fP_mul_self_of_mem hp hL hv
  have hd := deriv_mul_eq hU hsm hsm hu
  rw [hev.deriv_eq, (hasDerivAt_comp_div hp hL u).deriv] at hd
  rw [hd]; ring

lemma abs_deriv_fP_le {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (fP p L) u| ≤ A₁ / L := by
  have hf := fP_core_ge hp hL hu
  have e := deriv_fP_eq hp hL (core_mem hp hL hu)
  have hd := hp.deriv_le _ (core_abs hp hL hu)
  have e' : deriv (fP p L) u = deriv p (u / L) / L / (2 * fP p L u) := by
    rw [← e]; field_simp
  rw [e', abs_div, abs_div, abs_of_pos hL, abs_of_pos (by linarith : 0 < 2 * fP p L u)]
  calc |deriv p (u / L)| / L / (2 * fP p L u) ≤ |deriv p (u / L)| / L / 1 := by
        gcongr; linarith
    _ ≤ A₁ / L := by rw [div_one]; gcongr

lemma abs_deriv2_fP_le {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (deriv (fP p L)) u| ≤ (A₂ + 2 * A₁ ^ 2) / L ^ 2 := by
  set U : Set ℝ := Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := core_mem hp hL hu
  have hsm := fP_contDiffOn hp hL
  have hd1 : ∀ v ∈ U, deriv (fun x => fP p L x * fP p L x) v = deriv (fun x => p (x / L)) v := by
    intro v hv
    have hev : (fun x => fP p L x * fP p L x) =ᶠ[nhds v] fun x => p (x / L) := by
      filter_upwards [hU.mem_nhds hv] with x hx using fP_mul_self_of_mem hp hL hx
    exact hev.deriv_eq
  have hev2 : deriv (fun x => fP p L x * fP p L x) =ᶠ[nhds u] deriv (fun x => p (x / L)) := by
    filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
  have hd2 : deriv (deriv (fun x => p (x / L))) u
      = deriv (deriv (fP p L)) u * fP p L u + 2 * (deriv (fP p L) u * deriv (fP p L) u)
        + fP p L u * deriv (deriv (fP p L)) u := by
    rw [← hev2.deriv_eq]; exact deriv2_mul_eq hU hsm hsm huU
  rw [deriv2_comp_div hp hL] at hd2
  have hf := fP_core_ge hp hL hu
  have h1 := abs_deriv_fP_le hp hL hu
  have h2 := hp.deriv2_le _ (core_abs hp hL hu)
  have e : deriv (deriv (fP p L)) u
      = (deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)) / (2 * fP p L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fP p L u),
    div_le_div_iff₀ (by linarith) (by positivity)]
  have hsq : |deriv (fP p L) u| ^ 2 ≤ (A₁ / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hL2 : 0 < L ^ 2 := by positivity
  have hA := hp.A₁_nonneg; have hB := hp.A₂_nonneg
  calc |deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)| * L ^ 2
      ≤ (|deriv (deriv p) (u / L)| / L ^ 2 + 2 * |deriv (fP p L) u| ^ 2) * L ^ 2 := by
        gcongr
        calc |deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)|
            ≤ |deriv (deriv p) (u / L) / L ^ 2| + |2 * (deriv (fP p L) u * deriv (fP p L) u)| :=
              abs_sub _ _
          _ = |deriv (deriv p) (u / L)| / L ^ 2 + 2 * |deriv (fP p L) u| ^ 2 := by
              rw [abs_div, abs_of_pos hL2, abs_mul, abs_two, abs_mul]; ring
    _ ≤ (A₂ / L ^ 2 + 2 * (A₁ / L) ^ 2) * L ^ 2 := by gcongr
    _ = (A₂ + 2 * A₁ ^ 2) * 1 := by field_simp
    _ ≤ (A₂ + 2 * A₁ ^ 2) * (2 * fP p L u) := by
        gcongr; linarith

/-- the positive variation of f_p on [0, L/2] is at most that of p on [0, 1/2]. -/
lemma posVar_fP_le : ∫ u in (0:ℝ)..(L / 2), max (deriv (fP p L) u) 0 ≤ ρ := by
  have hU : IsOpen (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := isOpen_Ioo
  have hsm := fP_contDiffOn hp hL
  have hcore : Icc (0:ℝ) (L / 2) ⊆ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) := fun u hu =>
    core_mem hp hL (by rw [abs_of_nonneg hu.1]; exact hu.2)
  have hf'c : ContinuousOn (deriv (fP p L)) (Icc (0:ℝ) (L / 2)) :=
    (hsm.continuousOn_deriv_of_isOpen hU (by norm_num)).mono hcore
  have hp'c : Continuous (deriv p) := hp.contDiff.continuous_deriv (by norm_num)
  have hg : Continuous fun u => max (deriv p (u / L)) 0 / L :=
    ((hp'c.comp (continuous_id.div_const L)).max continuous_const).div_const L
  have hpt : ∀ u ∈ Icc (0:ℝ) (L / 2), max (deriv (fP p L) u) 0 ≤ max (deriv p (u / L)) 0 / L := by
    intro u hu
    have hu' : |u| ≤ L / 2 := by rw [abs_of_nonneg hu.1]; exact hu.2
    have hf := fP_core_ge hp hL hu'
    have e := deriv_fP_eq hp hL (hcore hu)
    refine max_le ?_ (by positivity)
    rcases le_or_gt (deriv (fP p L) u) 0 with h | h
    · exact h.trans (by positivity)
    · have : deriv (fP p L) u ≤ deriv p (u / L) / L := by nlinarith
      exact this.trans (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
  calc ∫ u in (0:ℝ)..(L / 2), max (deriv (fP p L) u) 0
      ≤ ∫ u in (0:ℝ)..(L / 2), max (deriv p (u / L)) 0 / L :=
        intervalIntegral.integral_mono_on (by linarith)
          ((ContinuousOn.sup hf'c continuousOn_const).intervalIntegrable_of_Icc (by linarith))
          (hg.intervalIntegrable _ _) hpt
    _ = ∫ s in (0:ℝ)..(1 / 2), max (deriv p s) 0 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div (fun s => max (deriv p s) 0)
          hL.ne', smul_eq_mul, zero_div, show L / 2 / L = 1 / 2 by field_simp]
        field_simp
    _ ≤ ρ := hp.posVar

/-- **the factor of a profile is a positive-variation factor.** -/
theorem pvFactor_fP : PVFactor (fP p L) L A₁ (A₂ + 2 * A₁ ^ 2) ρ where
  A_nonneg := hp.A₁_nonneg
  B_nonneg := by have := hp.A₂_nonneg; positivity
  even := fun u => by simp only [fP, neg_div, hp.even]
  nonneg := fun u => Real.sqrt_nonneg _
  le_one := fun u hu => fP_le_one hp hL hu
  smooth := ⟨δ * L, mul_pos hp.δ_pos hL, fP_contDiffOn hp hL⟩
  deriv_le := fun u hu => abs_deriv_fP_le hp hL hu
  deriv2_le := fun u hu => abs_deriv2_fP_le hp hL hu
  posVar := posVar_fP_le hp hL
  budget := by
    have h0 : 0 < p 0 := hp.pos 0 (by rw [abs_zero]; linarith [hp.δ_pos])
    rw [fP, zero_div]; exact hp.budget
  budget_sq := by
    have h0 : 0 < p 0 := hp.pos 0 (by rw [abs_zero]; linarith [hp.δ_pos])
    rw [fP, zero_div, Real.sq_sqrt h0.le]; exact hp.budget_sq

end

/-- **the profile window is admissible** (at the ramp taper's scale). -/
theorem admWindow_fP {ϱ : ℝ → ℝ} {w : ℝ} (hp : Profile p δ A₁ A₂ ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : AdmWindow (phiM (fP p L) ϱ L w) L w (cMod ϱ A₁ (A₂ + 2 * A₁ ^ 2)) :=
  admWindow_phiM (pvFactor_fP hp (by linarith)) hϱ hw hwL

end AMW

end

/-! ###### AMW module: PV ###### -/

/-
AMW/PV.lean — the positive-variation certificate for the AMTOPA profile, and its admissible window.

p := vAM/MAM.  On each of the 64 cells [i/128, (i+1)/128] of [0, 1/2], p′ = vAMd/MAM is bounded above by
its value at the midpoint m_i = (2i+1)/256 plus 78/256 (|vAMd′| = |vAMdd| ≤ 78, the mean value
theorem).  The midpoint value is bounded term by term: sin(√2 m_i) from the Taylor enclosure, and
sin(2πj m_i) = sin(π·j(2i+1)/128) from a table of outward enclosures of sin(πq/128), q ≤ 64, each
checked once against `sinPiI` (AMW/Trig.lean), and periodicity/reflection.  Hence
∫₀^{1/2} max(p′,0) ≤ Σ_i max(U_i,0)/160 = 0.03920 ≤ ρ = 9/200, a rational the kernel evaluates
(`pvCheck`); the budgets √p(0) + 2ρ ≤ 1, p(0) + 4ρ ≤ 1 hold with p(0) = 0.80516.
Hence `admWindow_phiW`.
-/

noncomputable section

open Real Set MeasureTheory

namespace AMW

open Zeta23

/-! ### the rational checker -/

def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumQ f n + f n

def allQ (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allQ f n && f n

theorem sumQ_eq (f : ℕ → ℚ) (n : ℕ) : sumQ f n = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumQ, ih, Finset.sum_range_succ]

theorem allQ_iff (f : ℕ → Bool) (n : ℕ) : allQ f n = true ↔ ∀ j < n, f j = true := by
  induction n with
  | zero => simp [allQ]
  | succ n ih =>
    rw [allQ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · exact h ▸ h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

/-- outward enclosures of sin(πq/128), q = 0, …, 64, in units of 10⁻¹⁰. -/
def sinTabZ : List (ℤ × ℤ) := [(-23, 23), (245412211, 245412336), (490676618, 490676821), (735645460, 735645741), (980171177, 980171535), (1224106475, 1224106910), (1467304418, 1467304929), (1709618512, 1709619097), (1950902796, 1950903456), (2191011930, 2191012663), (2429801281, 2429802085), (2667127010, 2667127885), (2902846163, 2902847107), (3136816751, 3136817762), (3368897838, 3368898914), (3598949628, 3598950767), (3826833546, 3826834747), (4052412323, 4052413585), (4275550080, 4275551398), (4496112407, 4496113780), (4713966444, 4713967869), (4928980966, 4928982440), (5141026455, 5141027976), (5349975184, 5349976748), (5555701288, 5555702893), (5758080847, 5758082491), (5956991955, 5956993634), (6152314796, 6152316505), (6343931713, 6343933451), (6531727285, 6531729047), (6715588390, 6715590173), (6895404278, 6895406078), (7071067175, 7071068989), (7242470227, 7242471943), (7409510684, 7409512305), (7572087929, 7572089455), (7730104029, 7730105464), (7883463803, 7883465147), (8032074872, 8032076129), (8175847718, 8175848890), (8314695739, 8314696827), (8448535296, 8448536304), (8577285771, 8577286701), (8700869608, 8700870463), (8819212365, 8819213148), (8932242757, 8932243471), (9039892700, 9039893347), (9142097347, 9142097932), (9238795136, 9238795661), (9329927819, 9329928287), (9415440501, 9415440916), (9495281672, 9495282037), (9569403240, 9569403558), (9637760555, 9637760831), (9700312443, 9700312679), (9757021224, 9757021424), (9807852739, 9807852907), (9852776368, 9852776508), (9891765053, 9891765168), (9924795306, 9924795400), (9951847233, 9951847310), (9972904538, 9972904601), (9987954536, 9987954590), (9996988163, 9996988211), (9999999977, 10000000023)]

def tabI (q : ℕ) : ℚ × ℚ :=
  (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)

def tabOk : Bool :=
  allQ (fun q => sinPiOk ((q : ℚ) / 128) && decide ((tabI q).1 ≤ (sinPiI ((q : ℚ) / 128)).1)
    && decide ((sinPiI ((q : ℚ) / 128)).2 ≤ (tabI q).2)) 65

def ineg (I : ℚ × ℚ) : ℚ × ℚ := (-I.2, -I.1)

/-- an enclosure of sin(πr/128). -/
def sinLook (r : ℕ) : ℚ × ℚ :=
  if r % 256 ≤ 64 then tabI (r % 256)
  else if r % 256 ≤ 128 then tabI (128 - r % 256)
  else if r % 256 ≤ 192 then ineg (tabI (r % 256 - 128))
  else ineg (tabI (256 - r % 256))

def midQ (i : ℕ) : ℚ := (2 * i + 1) / 256

/-- upper bound for the j-th term `−cAM j·ωAM j·sin(ωAM j·m_i)` of `vAMd m_i`. -/
def termU (i j : ℕ) : ℚ :=
  if j = 0 then -(s2LoQ * max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)))
  else if 0 ≤ -(2 * j * cAM j) then -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).2
  else -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).1

def termOk (i : ℕ) : Bool := decide (0 ≤ fl (s2LoQ * midQ i)) && decide (s2HiQ * midQ i ≤ 1)

def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + 78 / 256

def pvCheck (ρ : ℚ) : Bool :=
  tabOk && allQ termOk 64 && decide (sumQ (fun i => max (cellU i) 0) 64 / 160 ≤ ρ)

/-! ### soundness -/

theorem tabI_sound (h : tabOk = true) {q : ℕ} (hq : q < 65) :
    InI (tabI q) (Real.sin (Real.pi * ((q : ℝ) / 128))) := by
  rw [tabOk, allQ_iff] at h
  have hq' := h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
  obtain ⟨⟨hok, h1⟩, h2⟩ := hq'
  have hs := sinPiI_sound _ hok
  push_cast at hs
  exact ⟨(Rat.cast_le.mpr h1).trans hs.1, hs.2.trans (Rat.cast_le.mpr h2)⟩

theorem ineg_sound {I : ℚ × ℚ} {x : ℝ} (h : InI I x) : InI (ineg I) (-x) := by
  obtain ⟨h1, h2⟩ := h
  unfold ineg InI; push_cast; exact ⟨neg_le_neg h2, neg_le_neg h1⟩

theorem sinLook_sound (h : tabOk = true) (r : ℕ) :
    InI (sinLook r) (Real.sin (Real.pi * ((r : ℝ) / 128))) := by
  have hper : Real.sin (Real.pi * ((r : ℝ) / 128)) = Real.sin (Real.pi * (((r % 256 : ℕ) : ℝ) / 128)) := by
    have hr : (r : ℝ) = ((r % 256 : ℕ) : ℝ) + ((r / 256 : ℕ) : ℝ) * 256 := by
      exact_mod_cast (by omega : r = r % 256 + r / 256 * 256)
    rw [hr, show Real.pi * ((((r % 256 : ℕ) : ℝ) + ((r / 256 : ℕ) : ℝ) * 256) / 128)
      = Real.pi * (((r % 256 : ℕ) : ℝ) / 128) + ((r / 256 : ℕ) : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_nat_mul_two_pi _ _
  rw [hper]
  unfold sinLook
  have hq256 : r % 256 < 256 := Nat.mod_lt _ (by norm_num)
  generalize r % 256 = q at hq256 ⊢
  split_ifs with h1 h2 h3
  · exact tabI_sound h (by omega)
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = Real.sin (Real.pi * (((128 - q : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub h2, show Real.pi * ((((128 : ℕ) : ℝ) - (q : ℝ)) / 128)
        = Real.pi - Real.pi * ((q : ℝ) / 128) by push_cast; ring, Real.sin_pi_sub]
    rw [e]; exact tabI_sound h (by omega)
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = -Real.sin (Real.pi * (((q - 128 : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub (by omega : 128 ≤ q), show Real.pi * (((q : ℝ) - ((128 : ℕ) : ℝ)) / 128)
        = Real.pi * ((q : ℝ) / 128) - Real.pi by push_cast; ring, Real.sin_sub_pi]; ring
    rw [e]; exact ineg_sound (tabI_sound h (by omega))
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = -Real.sin (Real.pi * (((256 - q : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub (by omega : q ≤ 256), show Real.pi * ((((256 : ℕ) : ℝ) - (q : ℝ)) / 128)
        = 2 * Real.pi - Real.pi * ((q : ℝ) / 128) by push_cast; ring, Real.sin_two_pi_sub]; ring
    rw [e]; exact ineg_sound (tabI_sound h (by omega))

theorem termU_sound (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) (j : ℕ) :
    -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ))) ≤ ((termU i j : ℚ) : ℝ) := by
  unfold termU
  have hm0 : (0:ℚ) ≤ midQ i := by unfold midQ; positivity
  by_cases hj : j = 0
  · subst hj
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [if_true]
    obtain ⟨h0, h1⟩ := hok
    rw [cAM_zero, ωAM_zero, one_mul]
    have hm' : (0:ℝ) ≤ midQ i := by exact_mod_cast hm0
    have hs2 := s2LoQ_le
    have hθ0 : 0 ≤ Real.sqrt 2 * midQ i := mul_nonneg (Real.sqrt_nonneg 2) hm'
    have hθ1 : Real.sqrt 2 * midQ i ≤ 1 := by
      have : ((s2HiQ * midQ i : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
      push_cast at this
      nlinarith [s2HiQ_ge]
    have hl0 : (0:ℝ) ≤ ((fl (s2LoQ * midQ i) : ℚ) : ℝ) := by exact_mod_cast h0
    have hlθ : ((fl (s2LoQ * midQ i) : ℚ) : ℝ) ≤ Real.sqrt 2 * midQ i :=
      (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right hs2 hm')
    have hsin := sin_ge_of hl0 hlθ hθ1
    have hsin0 : 0 ≤ Real.sin (Real.sqrt 2 * midQ i) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (hθ1.trans (by linarith [Real.pi_gt_three]))
    have hlb : ((max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)) : ℚ) : ℝ)
        ≤ Real.sin (Real.sqrt 2 * midQ i) := by
      push_cast
      exact max_le hsin0 ((fl_le _).trans (by exact_mod_cast hsin))
    have hs2lo0 : (0:ℝ) ≤ ((s2LoQ : ℚ) : ℝ) := by simp only [s2LoQ]; push_cast; norm_num
    push_cast at hlb ⊢
    nlinarith
  · simp only [hj, if_false]
    have hω : ωAM j = 2 * Real.pi * j := by simp [ωAM, hj]
    have hS := piMul_sound (sinLook_sound htab (j * (2 * i + 1)))
    have e : -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ)))
        = ((-(2 * j * cAM j) : ℚ) : ℝ)
          * (Real.pi * Real.sin (Real.pi * (((j * (2 * i + 1) : ℕ) : ℝ) / 128))) := by
      rw [hω]; simp only [midQ]; push_cast; ring_nf
    rw [e]
    obtain ⟨h1, h2⟩ := hS
    split_ifs with he
    · have he' : (0:ℝ) ≤ ((-(2 * j * cAM j) : ℚ) : ℝ) := by exact_mod_cast he
      push_cast at he' h2 ⊢
      exact mul_le_mul_of_nonneg_left h2 he'
    · have he' : ((-(2 * j * cAM j) : ℚ) : ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
      push_cast at he' h1 ⊢
      exact mul_le_mul_of_nonpos_left h1 he'

theorem vAMd_mid_le (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) :
    vAMd (midQ i) ≤ ((sumQ (termU i) 13 : ℚ) : ℝ) := by
  rw [sumQ_eq, Rat.cast_sum, vAMd]
  exact Finset.sum_le_sum fun j _ => termU_sound htab hok j

theorem vAMd_lipschitz (x y : ℝ) : vAMd y ≤ vAMd x + 78 * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := vAMd) (s := Set.univ) (C := 78)
    (fun x _ => (hasDerivAt_vAMd x).differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs, (hasDerivAt_vAMd x).deriv]; exact abs_vAMdd_le x)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  linarith [le_abs_self (vAMd y - vAMd x)]

theorem deriv_vAM_div : deriv (fun s => vAM s / MAM) = fun s => vAMd s / MAM :=
  funext fun s => ((hasDerivAt_vAM s).div_const MAM).deriv

/-- **positive variation of vAM/MAM from a passing check.** -/
theorem posVar_of_check {ρ : ℚ} (h : pvCheck ρ = true) :
    ∫ s in (0:ℝ)..(1 / 2), max (deriv (fun s => vAM s / MAM) s) 0 ≤ (ρ : ℝ) := by
  simp only [pvCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨htab, hcells⟩, hsum⟩ := h
  rw [allQ_iff] at hcells
  rw [deriv_vAM_div]
  have hM : (0:ℝ) < MAM := MAM_pos
  set a : ℕ → ℝ := fun k => (k : ℝ) / 128 with ha
  have hcont : Continuous fun s => max (vAMd s / MAM) 0 :=
    (((continuous_iff_continuousAt.mpr fun x => (hasDerivAt_vAMd x).continuousAt)).div_const MAM).max
      continuous_const
  have hcell : ∀ i < 64, ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
      ≤ 1 / 128 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
    intro i hi
    have hab : a i ≤ a (i + 1) := by simp only [ha]; gcongr; push_cast; linarith
    have hmid : ((midQ i : ℚ) : ℝ) = (2 * i + 1) / 256 := by simp only [midQ]; push_cast; ring
    have hvm := vAMd_mid_le htab (hcells i hi)
    have hpt : ∀ s ∈ Set.Icc (a i) (a (i + 1)), max (vAMd s / MAM) 0
        ≤ ((max (cellU i) 0 : ℚ) : ℝ) / MAM := by
      intro s hs
      have hd : |s - (midQ i : ℝ)| ≤ 1 / 256 := by
        rw [hmid, abs_le]
        simp only [ha, Set.mem_Icc] at hs
        push_cast at hs
        obtain ⟨hs1, hs2⟩ := hs
        constructor <;> linarith
      have hlip := vAMd_lipschitz (midQ i : ℝ) s
      have hU : vAMd s ≤ ((cellU i : ℚ) : ℝ) := by
        simp only [cellU]; push_cast
        linarith
      push_cast
      exact max_le ((div_le_div_of_nonneg_right hU hM.le).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hM.le)) (div_nonneg (le_max_right _ _) hM.le)
    calc ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
        ≤ ∫ s in a i..a (i + 1), ((max (cellU i) 0 : ℚ) : ℝ) / MAM :=
          intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _) hpt
      _ = 1 / 128 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          simp only [ha]; push_cast; ring
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := fun s => max (vAMd s / MAM) 0) (a := a) (n := 64) (fun k _ => hcont.intervalIntegrable _ _)
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a 64 = 1 / 2 := by simp only [ha]; norm_num
  rw [ha0, haN] at hsplit
  rw [← hsplit]
  refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
  have hq : ((sumQ (fun i => max (cellU i) 0) 64 / 160 : ℚ) : ℝ) ≤ (ρ : ℝ) := by
    exact_mod_cast hsum
  refine le_of_eq_of_le ?_ hq
  rw [sumQ_eq, ← Finset.mul_sum, ← Finset.sum_div]
  push_cast
  simp only [MAM]
  ring

/-! ### the AMTOPA profile and its admissible window -/

set_option maxRecDepth 100000 in
theorem pvCheck_AM : pvCheck (9 / 200) = true := by decide +kernel

theorem deriv2_vAM_div : deriv (deriv (fun s => vAM s / MAM)) = fun s => vAMdd s / MAM := by
  rw [deriv_vAM_div]
  exact funext fun s => ((hasDerivAt_vAMd s).div_const MAM).deriv

theorem vAM_zero_div_le : vAM 0 / MAM ≤ 81 / 100 := by
  rw [vAM_zero, MAM]; norm_num

theorem profile_AM : Profile (fun s => vAM s / MAM) (1 / 10) (14 / 5) (312 / 5) (9 / 200) where
  δ_pos := by norm_num
  A₁_nonneg := by norm_num
  A₂_nonneg := by norm_num
  even := fun s => by simp only [vAM_even]
  contDiff := (vAM_contDiff.of_le le_top).div_const MAM
  pos := fun s hs => div_pos (vAM_pos_wide (by linarith)) MAM_pos
  ge_quarter := fun s hs => by
    have := vAM_ge_core hs
    rw [MAM, le_div_iff₀ (by norm_num)]; linarith
  le_one := fun s _ => by rw [div_le_one MAM_pos]; exact vAM_le s
  deriv_le := fun s _ => by
    rw [deriv_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
    linarith [abs_vAMd_le s]
  deriv2_le := fun s _ => by
    rw [deriv2_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
    linarith [abs_vAMdd_le s]
  posVar := by
    have h := posVar_of_check pvCheck_AM
    push_cast at h
    exact h
  budget := by
    have h0 : Real.sqrt (vAM 0 / MAM) ≤ 9 / 10 := by
      rw [show (9 / 10 : ℝ) = Real.sqrt (81 / 100) by
        rw [show (81 / 100 : ℝ) = (9 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt vAM_zero_div_le
    linarith
  budget_sq := by linarith [vAM_zero_div_le]

/-- the window constant of the AMTOPA window. -/
def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (14 / 5) (312 / 5 + 2 * (14 / 5) ^ 2)

/-- **The AMTOPA window is admissible.** -/
theorem admWindow_phiW {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (phiW ϱ L w) L w (cAMW ϱ) :=
  admWindow_fP profile_AM hϱ hw hwL

end AMW

end

/-! ###### AMW module: ZeroSide ###### -/

/-
AMW/ZeroSide.lean — the zero side for a window family `atW P W`, and the AMTOPA instance.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/XiPrime/QuarticWindow/ZeroSide.lean §1 and Zeta23/ThmD/ZeroSideD.lean, generic in the window:
from an admissibility witness T ↦ AdmWindow (W T) (L_T) w c (for 8w ≤ L_T) and 1/2 ≤ a eventually,
the fixed-T producers `ZeroSide.blockInputsAt`, `Tail.TailHyp.tailInputs`, `ZeroConfig.Gz_eq_Gp`
give prop:block, prop:tail (θ₀ ≤ C·l·T^{λ/2−1}) and the H-EF bridge for `atW P W T`.
The AMTOPA instance W T = phiW ϱ L_T w adds 1/2 ≤ a ≤ 1 for 32w ≤ L_T (vAM/MAM ≥ 137/250).
-/

noncomputable section

open Filter Complex Real Set MeasureTheory

namespace AMW

open Zeta23

section generic

variable {P : Params} {W : ℝ → ℝ → ℝ} {cW : ℝ} (hP : P.Valid) (hev : ∀ T u, W T (-u) = W T u)
  (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w cW)
include hP hev hW

/-! ### lem:poisson and prop:block -/

theorem poissonSqW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ZeroSide.PoissonSq T (atW P W T) := by
  intro γ
  have h := (hW T h8).hasSum_vHatR_mul T γ γ
  rw [sub_self, (hW T h8).VPhiR_zero] at h
  simp only [atW_phiHatR T hP (hev T), atW_a T hP (hev T), atW_tau_eq, atW_L, sq]
  convert h using 1
  ring

theorem blockInputsW (Z : ZeroConfig) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (haT : 0 < (atW P W T).a T) :
    Assembly.BlockInputs Z (atW P W T) T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  exact ZeroSide.blockInputsAt Z (atW P W T) T (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqW hP hev hW h8) hL (mul_pos haT (pow_pos hL 2))

/-! ### the H-EF bridge -/

theorem GzGpW (Z : ZeroConfig) (H : PaperInputs Z) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    Z.Gz (atW P W T) T = (atW P W T).Gp T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  refine Z.Gz_eq_Gp (atW P W T) T H.EF hL ?_ ?_
  · rw [atW_phi_valid T hP (hev T)]; exact (hW T h8).vC_contDiff
  · rw [atW_phi_valid T hP (hev T)]; exact closure_minimal (hW T h8).support_subset isClosed_Icc

/-! ### prop:tail -/

omit hP hev hW in
/-- C₁(T) := ‖(W T)″‖₁. -/
lemma C1W_nonneg (W : ℝ → ℝ → ℝ) (T : ℝ) : 0 ≤ ∫ u, |deriv (deriv (W T)) u| :=
  integral_nonneg fun _ => abs_nonneg _

omit hev in
lemma C1W_le {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ∫ u, |deriv (deriv (W T)) u| ≤ cW :=
  (hW T h8).l1_deriv2.trans (div_le_self (hW T h8).c_nonneg hP.one_le_w)

theorem hdecayW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖(atW P W T).phiHat T (r - I * y)‖
      ≤ Real.exp ((atW P W T).L T / 4) * (∫ u, |deriv (deriv (W T)) u|) / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hL : 0 ≤ P.L T := (hW T h8).L_pos.le
  rw [atW_phiHat T hP (hev T), atW_L, le_div_iff₀ (by positivity)]
  refine le_trans ((hW T h8).norm_vHat_mul_sq_le _) ?_
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

theorem eventually_tailPackageW (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (atW P W T).a T) (Z : ZeroConfig)
    (H : PaperInputs Z) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atW P W T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * ∫ u, |deriv (deriv (W T)) u|) T, ?_, ?_⟩
  · have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (ThmD.tendsto_L hP).eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop Tail.T₀, hL2, ThmD.eventually_w8 hP, ha] with T hT hL h8 haT
    have HT : Tail.TailHyp Z (atW P W T) T A₀ (∫ u, |deriv (deriv (W T)) u|) :=
      { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := C1W_nonneg W T,
        hdecay := fun r y hy hz => hdecayW hP hev hW h8 r y hy hz }
    exact HT.tailInputs (by linarith) (fun z => GzGp.phiHat_conj _ T z)
  · exact Tail.eventually_theta0_le P hP hA₀ (fun T => ∫ u, |deriv (deriv (W T)) u|)
      (C1W_nonneg W) (R := cW / 2) ((ThmD.eventually_w8 hP).mono fun T h8 => by linarith [C1W_le hP hW h8])

/-! ### the eventual exports -/

theorem eventually_blockInputsW (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (atW P W T).a T) (Z : ZeroConfig) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (atW P W T) T := by
  filter_upwards [ThmD.eventually_w8 hP, ha] with T h8 haT
  exact blockInputsW hP hev hW Z h8 (by linarith)

theorem eventually_GzGpW (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ᶠ T in atTop, Z.Gz (atW P W T) T = (atW P W T).Gp T := by
  filter_upwards [ThmD.eventually_w8 hP] with T h8
  exact GzGpW hP hev hW Z H h8

omit hW in
theorem eventually_a_le_one (hW' : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w cW) :
    ∀ᶠ T in atTop, (atW P W T).a T ≤ 1 := by
  filter_upwards [ThmD.eventually_w8 hP] with T h8
  rw [atW_a T hP (hev T)]; exact (hW' T h8).av_le_one

end generic

/-! ## The AMTOPA instance -/

/-- the AMTOPA window family of `P`. -/
def WAM (P : Params) (T : ℝ) : ℝ → ℝ := phiW P.ϱ (P.L T) P.w

/-- the per-height parameter set realizing it (the AM analogue of `Params.atD`). -/
def atAM (P : Params) (T : ℝ) : Params := atW P (WAM P) T

variable {P : Params}

theorem WAM_even (P : Params) (T u : ℝ) : WAM P T (-u) = WAM P T u := phiW_even u

theorem admWindow_WAM (hP : P.Valid) (T : ℝ) (h8 : 8 * P.w ≤ P.L T) :
    AdmWindow (WAM P T) (P.L T) P.w (cAMW P.ϱ) :=
  admWindow_phiW hP.taper hP.one_le_w h8

theorem atAM_a (hP : P.Valid) (T : ℝ) : (atAM P T).a T = AdmWindow.av (WAM P T) (P.L T) :=
  atW_a T hP (WAM_even P T)

theorem localFunW_eq (P : Params) (T : ℝ) : localFunW P T = AdmWindow.localFun (WAM P T) (P.L T) := rfl

/-- `phiW² ≥ (137/250)·φ²` pointwise. -/
lemma phiW_sq_ge (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
    137 / 250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ WAM P T u ^ 2 := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [WAM, phiW_sq_eq hP.taper hw0 hL]
  rcases le_or_gt (P.L T / 2) |u| with hu | hu
  · rw [Taper.phi_eq_zero hP.taper hw0 hu]; simp
  · exact mul_le_mul_of_nonneg_right (hW_core_ge hL hu.le) (sq_nonneg _)

/-- **1/2 ≤ a ≤ 1 for the AMTOPA window**, as soon as 32w ≤ L. -/
theorem aAM_range_of (hP : P.Valid) {T : ℝ} (h32 : 32 * P.w ≤ P.L T) :
    1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
  have h8 : 8 * P.w ≤ P.L T := by linarith [hP.one_le_w]
  have hW := admWindow_WAM hP T h8
  rw [atAM_a hP]
  refine ⟨?_, hW.av_le_one⟩
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2 : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hb : 1 - 2 * P.w / P.L T ≤ Taper.aConst P.ϱ (P.L T) P.w :=
    (Taper.one_sub_le_bConst hP.taper hw0 h2).trans (Taper.bConst_le_aConst hP.taper hw0 h2)
  have hwL : 2 * P.w / P.L T ≤ 1 / 16 := by rw [div_le_iff₀ hL]; linarith
  have hint : Integrable (fun u => WAM P T u ^ 2) := hW.integrable_pow two_pos
  have hint' : Integrable (fun u => 137 / 250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2) :=
    (((Taper.phi_continuous hP.taper hw0 h2).fun_pow 2).integrable_of_hasCompactSupport
      ((Taper.phi_hasCompactSupport hP.taper hw0).comp_left (g := fun t => t ^ 2) (by norm_num))).const_mul _
  have hcmp : 137 / 250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ ∫ u, WAM P T u ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono hint' hint (phiW_sq_ge hP h8)
  unfold AdmWindow.av
  unfold Taper.aConst at hb
  have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
  calc (1:ℝ) / 2 ≤ 137 / 250 * (1 - 2 * P.w / P.L T) := by nlinarith
    _ ≤ 137 / 250 * ((P.L T)⁻¹ * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by gcongr
    _ = (P.L T)⁻¹ * (137 / 250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by ring
    _ ≤ (P.L T)⁻¹ * ∫ u, WAM P T u ^ 2 := mul_le_mul_of_nonneg_left hcmp hLi.le

theorem eventually_w32 (hP : P.Valid) : ∀ᶠ T in atTop, 32 * P.w ≤ P.L T :=
  (ThmD.tendsto_L hP).eventually_ge_atTop _

theorem eventually_aAM_range (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
  filter_upwards [eventually_w32 hP] with T h32
  exact aAM_range_of hP h32

/-! ### the AMTOPA exports (instances of the generic section) -/

theorem eventually_blockInputsAM (Z : ZeroConfig) (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (atAM P T) T :=
  eventually_blockInputsW hP (WAM_even P) (admWindow_WAM hP)
    ((eventually_aAM_range hP).mono fun _ h => h.1) Z

theorem eventually_GzGpAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∀ᶠ T in atTop, Z.Gz (atAM P T) T = (atAM P T).Gp T :=
  eventually_GzGpW hP (WAM_even P) (admWindow_WAM hP) Z H

theorem eventually_tailPackageAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atAM P T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) :=
  eventually_tailPackageW hP (WAM_even P) (admWindow_WAM hP)
    ((eventually_aAM_range hP).mono fun _ h => h.1) Z H

end AMW

end

/-! ###### AMW module: Concrete ###### -/

/-
AMW/Concrete.lean — the concrete FactsD instance for an arbitrary admissible window family.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/ThmD/Concrete.lean and the eventual-LocalHypsCore step of Zeta23/ThmD/BridgeD.lean, with the
Montgomery–Taylor data `P.localFunD T` replaced by `lfW P W T := AdmWindow.localFun (W T) (L_T)` for a
window family W admissible at (L_T, w) with constant c.  The window enters only through
`AdmWindow.localHypsCore` (needs b ≥ 1/2 eventually), the C¹ facts of g = (W T)² ⋆ (W T)²
(`ThmD.autocorr_deriv_facts`, from ‖((W T)²)′‖₁ ≤ 2) and the support of g.
End product: `tracesBoundsW_concrete`, via `ThmD.tracesBoundsD_of_factsD`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace AMW

open Zeta23 ThmD PrimeSide PaperParams

/-- the abstract local data of the window `W T` at height `T`. -/
def lfW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : PrimeSide.LocalFun := AdmWindow.localFun (W T) (P.L T)

variable (P : Params) (W : ℝ → ℝ → ℝ)

/-- the concrete D-data of the window family W. -/
def concreteDataW (Z : ZeroConfig) : DataD P where
  aT := fun T => (lfW P W T).a
  bT := fun T => (lfW P W T).b
  trG := fun T => trGtA (P.toSetting T) (lfW P W T)
  trG2 := fun T => trGt2A (P.toSetting T) (lfW P W T)
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (lfW P W T)
  Mmumu := fun T => Mform (lfW P W T).Phi T Zeta23.mu Zeta23.mu
  MPP := fun T => Mform (lfW P W T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PX (P.X T))
  MmuP := fun T => Mform (lfW P W T).Phi T Zeta23.mu (Zeta23.PX (P.X T))
  MmuPi := fun T => Mform (lfW P W T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
  MPPi := fun T => Mform (lfW P W T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PiX (P.X T))
  MPiPi := fun T => Mform (lfW P W T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (lfW P W T).g
  JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y

/-- `LocalHypsCore` for the W-data, eventually. -/
def LocalHypsCoreWEventually (c : ℝ) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → PrimeSide.LocalHypsCore c (P.toSetting T) (lfW P W T)

variable {P W}

/-- **eventual `LocalHypsCore` from admissibility and b ≥ 1/2.** -/
theorem localHypsCoreW_eventually {c : ℝ} (hP : P.Valid)
    (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
    (hb : ∀ᶠ T in atTop, 1 / 2 ≤ AdmWindow.bv (W T) (P.L T)) : LocalHypsCoreWEventually P W c := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and (hb.and hX)))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h8, hbT, hX1⟩ := hT₀ T hT
  exact AdmWindow.localHypsCore (P.toSetting T) (hW T h8) hP.lam_pos hP.lam_le_one h1 hX1 hbT

/-- the CoreW analogue of PrimeSide.evBound_of_eventuallyAt. -/
lemma evBound_of_eventuallyAtCoreW {c : ℝ} (hLoc : LocalHypsCoreWEventually P W c)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAtCore c P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (lfW P W T)) :
    EvBound (fun T => f (P.toSetting T) (lfW P W T)) (fun T => g (P.toSetting T) (lfW P W T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have := hT₁ (P.toSetting T) (lfW P W T) rfl h1 (hT₀ T h0)
  calc |f (P.toSetting T) (lfW P W T)| ≤ C * g (P.toSetting T) (lfW P W T) := this
    _ ≤ max C 1 * g (P.toSetting T) (lfW P W T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)

/-- the C¹ facts of g = (W T)² ⋆ (W T)² that the partial-summation step consumes. -/
theorem gW_deriv_facts {c L w : ℝ} {v : ℝ → ℝ} (hW : AdmWindow v L w c) :
    Differentiable ℝ (Params.autocorr (fun u => v u ^ 2))
      ∧ Continuous (deriv (Params.autocorr (fun u => v u ^ 2)))
      ∧ ∀ y : ℝ, |deriv (Params.autocorr (fun u => v u ^ 2)) y| ≤ 2 := by
  apply ThmD.autocorr_deriv_facts
  · exact (hW.contDiff.pow 2).of_le (by norm_num)
  · exact hW.sq_hasCompactSupport
  · intro x; exact hW.sq_even x
  · intro u
    rw [abs_of_nonneg (sq_nonneg _)]
    calc v u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hW.nonneg u) (hW.le_one u) 2
      _ = 1 := one_pow 2
  · exact hW.l1_deriv_sq

/-- **FactsD for the concrete W-data.**  Inputs: P.Valid, PaperInputs Z, the admissibility witness and
the eventual LocalHypsCore. -/
theorem concreteFactsW {Z : ZeroConfig} {c : ℝ} (hP : P.Valid) (inp : PaperInputs Z)
    (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
    (hLoc : LocalHypsCoreWEventually P W c) : FactsD (concreteDataW P W Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.lem_ends c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_mumu c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_PP (cϱ := c) (lam := P.lam) hcheb inp.MV hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_cross_muP c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_cross_muPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_cross_PPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAtCoreW hLoc
    (PrimeSide.prop_cross_PiPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?ab_range, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP, e_muPi, e_PPi, e_PiPi⟩
  case ab_range =>
    filter_upwards [eventually_ge_atTop T₀, ThmD.eventually_w8 hP] with T hT h8
    have hF := hT₀ T hT
    have hL0 : 0 < P.L T := by linarith [hP.one_le_w]
    refine ⟨hF.b_ge_half, hF.b_le_a, hF.a_le_one, ?_, ?_⟩
    · apply mul_nonneg (by positivity)
      apply intervalIntegral.integral_nonneg (by linarith : (0:ℝ) ≤ P.L T)
      intro y hy
      exact mul_nonneg (hF.g_nonneg y) hy.1
    · have hgcont : Continuous (lfW P W T).g := (gW_deriv_facts (hW T h8)).1.continuous
      have hgle : ∀ y ∈ Set.Icc (0:ℝ) (P.L T), (lfW P W T).g y * y ≤ P.L T * y := by
        intro y hy
        apply mul_le_mul_of_nonneg_right _ hy.1
        calc (lfW P W T).g y ≤ (lfW P W T).Aphi y := hF.g_le_Aphi y
          _ ≤ max ((P.toSetting T).L - |y|) 0 := hF.Aphi_le y
          _ ≤ P.L T := by
              apply max_le _ hL0.le
              have := abs_nonneg y
              show (P.toSetting T).L - |y| ≤ P.L T
              have e : (P.toSetting T).L = P.L T := rfl
              rw [e]
              linarith
      have hIle : ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y
          ≤ ∫ y in (0:ℝ)..(P.L T), P.L T * y := by
        apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ P.L T) ?_ ?_ hgle
        · exact (hgcont.mul continuous_id).intervalIntegrable 0 (P.L T)
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (P.L T)
      have hIval : ∫ y in (0:ℝ)..(P.L T), P.L T * y = P.L T ^ 3 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      calc 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y
          ≤ 2 / P.L T ^ 3 * (P.L T ^ 3 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hIval]
            exact hIle
        _ = 1 := by field_simp
  case muints2 =>
    obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace c P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (lfW P W T) rfl h2 hF (Z.N T (2 * T) : ℝ) (hN T h1)
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit c hΓ (P.toSetting T) (lfW P W T) (hT₀ T hT)
  case sumJ =>
    obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close hcheb
    refine ⟨C, hC0, ?_⟩
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos 8)
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (ThmD.eventually_w8 hP)
    refine ⟨max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hL8 : 8 ≤ P.L T := hT₁ T h1
    have h8 : 8 * P.w ≤ P.L T := hT₂ T h2
    have hg := gW_deriv_facts (hW T h8)
    have hgsupp : ∀ y : ℝ, P.L T ≤ y → (lfW P W T).g y = 0 := by
      intro y hy
      exact (hW T h8).gv_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hy)
    have key := hC (P.L T) (P.X T) (lfW P W T).g hL8 (by
        show P.X T = Real.exp (P.L T)
        rfl) hg.1 hg.2.1 hg.2.2 hgsupp
    have e : P.L T ^ 3 / 2 * ((concreteDataW P W Z).JT T)
        = ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y := by
      show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y) = _
      have hL0 : 0 < P.L T := by linarith
      field_simp
    show |sumA2g (P.X T) (lfW P W T).g - P.L T ^ 3 / 2 * ((concreteDataW P W Z).JT T)|
      ≤ C * P.L T ^ 2
    rw [e]
    exact key

/-- **TracesBoundsD for the concrete W-data.** -/
theorem tracesBoundsW_concrete {Z : ZeroConfig} {c : ℝ} (hP : P.Valid) (inp : PaperInputs Z)
    (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
    (hLoc : LocalHypsCoreWEventually P W c) :
    TracesBoundsD P (concreteDataW P W Z).aT (concreteDataW P W Z).bT (concreteDataW P W Z).JT
      (concreteDataW P W Z).trG (concreteDataW P W Z).trG2 (concreteDataW P W Z).Ncnt :=
  tracesBoundsD_of_factsD _ (concreteFactsW hP inp hW hLoc)

/-- the identification of the zero-side parameter family's traces with the concrete W-data. -/
theorem atW_ident (Z : ZeroConfig) (hP : P.Valid) (hev : ∀ T u, W T (-u) = W T u) (T : ℝ) :
    (atW P W T).trGtilde T = (concreteDataW P W Z).trG T ∧
      (atW P W T).trGtildeSq T = (concreteDataW P W Z).trG2 T ∧
      (atW P W T).a T = (concreteDataW P W Z).aT T :=
  ⟨atW_trGtilde T hP (hev T), atW_trGtildeSq T hP (hev T), atW_a T hP (hev T)⟩

end AMW

end

/-! ###### AMW module: BHalf ###### -/

/-
AMW/BHalf.lean — the AMTOPA prime side: eventual LocalHypsCore and TracesBoundsD.
b ≥ 1/2 eventually is `eventually_bW_ge_half` (AMW/Floor: b_T → bInf > 1/2).
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace AMW

open Zeta23

variable {P : Params}

theorem eventually_bAM_ge_half (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ AdmWindow.bv (WAM P T) (P.L T) :=
  eventually_bW_ge_half hP

/-- eventual `LocalHypsCore` for the AMTOPA data. -/
theorem localHypsCoreAM_eventually (hP : P.Valid) : LocalHypsCoreWEventually P (WAM P) (cAMW P.ϱ) :=
  localHypsCoreW_eventually hP (admWindow_WAM hP) (eventually_bAM_ge_half hP)

/-- **TracesBoundsD for the AMTOPA window.** -/
theorem tracesBoundsAM_concrete {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z) :
    ThmD.TracesBoundsD P (concreteDataW P (WAM P) Z).aT (concreteDataW P (WAM P) Z).bT
      (concreteDataW P (WAM P) Z).JT (concreteDataW P (WAM P) Z).trG (concreteDataW P (WAM P) Z).trG2
      (concreteDataW P (WAM P) Z).Ncnt :=
  tracesBoundsW_concrete hP inp (admWindow_WAM hP) (localHypsCoreAM_eventually hP)

end AMW

end

/-! ###### AMW module: BrA ###### -/

/-
AMW/BrA.lean — bridge part A (StableRankTrace, Defs, Helpers_finite/pinching/S8).
Retargeted copy of the Zeta Lab bridge (MIT) as carried in SolutionSevW10D.lean, lines 55-1025:
the Montgomery–Taylor window replaced by the AMTOPA window (AMW.atAM, AMW.KfunAM, AMW.HW).
-/

set_option linter.all false

/-! ###### source module: Zeta23Ext/StableRankTrace.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder

namespace Zeta23Ext.StableRankTrace

def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

lemma Psi_eq_gc_two_add_one (t : ℝ) : Psi t = gc 2 t + 1 := by
  unfold Psi
  split_ifs with h
  · rw [gc_of_le h]; ring
  · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring


lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split_ifs with h
  · positivity
  · have : (2 : ℝ) < t := not_le.mp h
    linarith


section Eigen

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j

lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (eigCols hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, eigCols, Matrix.mul_diagonal]
  ring

lemma pmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Pmat hP.1.eigenvalues (eigCols hP) = P := by
  have hdd : (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)
        * ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜))
      = RCLike.ofReal ∘ hP.1.eigenvalues := by
    funext j
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    rw [Real.mul_self_sqrt (hP.eigenvalues_nonneg j)]
  have hstar : (diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)))ᴴ
      = diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
    rw [diagonal_conjTranspose]
    simp [RCLike.star_def]
  unfold Pmat
  rw [wmat_eigCols hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
  conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (eigCols hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j

end Eigen

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma rtrace_specMap_Psi (V : Matrix n r 𝕜) :
    rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
        + (Fintype.card r : ℝ) := by
  rw [rtrace_specMap]
  have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := Psi_eq_gc_two_add_one
  simp only [hshift]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  congr 1
  exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm

theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
  have hR := rank_trace_mult hm (eigCols hP) hQ hb (c := 2) (by norm_num)
  rw [pmat_eigCols hP] at hR
  have hx : ∀ j, hP.1.eigenvalues j * xsq (eigCols hP) j = hP.1.eigenvalues j := by
    intro j; rw [xsq_eigCols hP j, mul_one]
  simp only [hx] at hR
  rw [rtrace_specMap_Psi V]
  have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
  linarith [hR]

theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hsharp := stable_rank_trace_sharp V hQ hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith


end Main


end Zeta23Ext.StableRankTrace

end

/-! ###### source module: Zeta23Ext/Bridge/Defs.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

/-- the pair kernel of the AMTOPA window, `∫_{-½}^{½} vAM(t) cos(2πxt) dt` (so `kfun = AMW.kfunAM` and
`wfun = AMW.wfunAM` by rfl). -/
def Kfun (x : ℝ) : ℝ := AMW.KfunAM x

def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

def wfun (x : ℝ) : ℝ := kfun x ^ 2

def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0


section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def energyOn (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else wfun (x i - x j)

def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2

def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0

def IsInterval (x : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, ∀ k, x i ≤ x k → x k ≤ x j → k ∈ B

lemma abs_sub_le_spanOf (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
    |x i - x j| ≤ spanOf x B := by
  have hne : B.Nonempty := ⟨i, hi⟩
  unfold spanOf
  rw [dif_pos hne, abs_le]
  constructor
  · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
  · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]

lemma spanOf_nonneg (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
  unfold spanOf
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
  · exact le_rfl

def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)

lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => Psi_nonneg _

def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))

lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ blockDefect hM B :=
  defect_nonneg _

end Blocks


section BlockLevel

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)

def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ

def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c

def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c

lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _

lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
  isHermitian_conjTranspose_mul_self _

lemma gramS₁_posSemidef (c : ℝ) : (gramS₁ D c).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

lemma blockP_isHermitian (c : ℝ) : (D.blockP c).IsHermitian :=
  ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _

lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
  ((blockP_isHermitian D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1

lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
  unfold Q'; abel

end BlockLevel

section Concrete

open Classical

def mtParams (T : ℝ) : Params := AMW.atAM (paramsOf stdProfile 1) T

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)

def aL2 : ℝ := P.a T * P.L T ^ 2

def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj

def retained : Finset (ZI Z T) :=
  (bdata Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2

lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1

def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩

lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)

def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)

lemma gram_isHermitian : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _

lemma gram_posSemidef : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _

def Dcirc : ℝ := defect (gram_isHermitian Z P T)

def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)

lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (bdata Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h

lemma xret_injective (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
  intro z z' h
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  unfold xret xnorm at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
    have h1 := (div_left_inj' hpi.ne').mp h
    have h2 := mul_left_cancel₀ hL.ne' h1
    linarith
  apply Subtype.ext; apply Subtype.ext
  exact Complex.ext (by rw [hz, hz']) him

end Concrete


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_finite.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

lemma Kfun_neg (x : ℝ) : Kfun (-x) = Kfun x := AMW.KfunAM_neg x

lemma kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
  unfold kfun; rw [Kfun_neg]

lemma wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
  unfold wfun; rw [kfun_neg]

lemma wfun_sub_comm (a b : ℝ) : wfun (a - b) = wfun (b - a) := by
  rw [← wfun_neg, neg_sub]

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

lemma abs_Kfun_le_Kfun_zero (x : ℝ) : |Kfun x| ≤ Kfun 0 := AMW.abs_KfunAM_le x

lemma abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := by
  unfold kfun
  rw [abs_div]
  rcases eq_or_ne (Kfun 0) 0 with h | h
  · rw [h, abs_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact (abs_Kfun_le_Kfun_zero x).trans (le_abs_self _)

lemma wfun_le_one (x : ℝ) : wfun x ≤ 1 := by
  unfold wfun
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_kfun_le_one x)

section Sorted

variable {m : ℕ}

def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0

lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
  unfold sortedExt; rw [dif_pos h]

lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    sortedExt y a ≤ sortedExt y b := by
  rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
  exact hy.monotone (Fin.mk_le_mk.mpr hab)

def windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
  fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)

lemma range_filter_lt {N k : ℕ} (hk : k ≤ N) : ((range N).filter fun j => j < k) = range k := by
  ext j
  simp only [mem_filter, mem_range]
  omega

lemma ptsN_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) (k : Fin n) :
    ptsN n (windowGaps n Y i) k = Y (i + k) - Y i := by
  have hk : (k : ℕ) ≤ n - 1 := by have := k.2; omega
  unfold ptsN windowGaps
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < (k : ℕ) then Y (i + (j + 1)) - Y (i + j) else 0) (n - 1),
    ← sum_filter, range_filter_lt hk]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (k : ℕ)
  simpa using this


lemma sum_shift_sub (f : ℕ → ℝ) (d N : ℕ) :
    ∑ i ∈ range N, (f (i + d) - f i) = ∑ i ∈ range d, (f (N + i) - f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 : ∑ i ∈ range d, (f (N + 1 + i) - f i) = ∑ i ∈ range d, (f (N + (i + 1)) - f i) :=
      sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    have h2 : ∑ i ∈ range d, f (N + (i + 1)) = ∑ i ∈ range d, f (N + i) + f (N + d) - f (N + 0) := by
      have := sum_range_succ' (fun i => f (N + i)) d
      rw [sum_range_succ] at this
      linarith
    rw [h1, sum_sub_distrib, sum_sub_distrib, h2]
    simp only [add_zero]
    ring

end Sorted


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_pinching.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

section PsiConvex
open Zeta23Ext.StableRankTrace

lemma affine_le_Psi {s x : ℝ} (hs : s ≤ 2) : 2 * (s - 1) * x - (s ^ 2 - 1) ≤ Psi x := by
  unfold Psi
  split_ifs with h
  · nlinarith [sq_nonneg (x - s)]
  · have hx : 2 < x := not_le.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0 : ℝ) ≤ 2 * x - 2 - s)]

lemma affine_eq_Psi (x : ℝ) : 2 * (min x 2 - 1) * x - ((min x 2) ^ 2 - 1) = Psi x := by
  unfold Psi
  rcases le_or_gt x 2 with h | h
  · rw [min_eq_left h, if_pos h]; ring
  · rw [min_eq_right h.le, if_neg (not_le.mpr h)]; ring

theorem Psi_convexOn : ConvexOn ℝ Set.univ Psi := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hz
  set t := min z 2 with ht
  have ht2 : t ≤ 2 := min_le_right _ _
  have hx := affine_le_Psi (x := x) ht2
  have hy := affine_le_Psi (x := y) ht2
  have hsplit : 2 * (t - 1) * z - (t ^ 2 - 1)
      = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := by
    rw [hz]; linear_combination (t ^ 2 - 1) * hab
  calc Psi z = 2 * (t - 1) * z - (t ^ 2 - 1) := (affine_eq_Psi z).symm
    _ = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := hsplit
    _ ≤ a * Psi x + b * Psi y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

end PsiConvex

section Entries

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma re_mul_conjTranspose_apply_self (Y : Matrix κ ι 𝕜) (j : κ) :
    RCLike.re ((Y * Yᴴ) j j) = ∑ i, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
  simp

lemma re_conjTranspose_mul_apply_self (Y : Matrix κ ι 𝕜) (i : ι) :
    RCLike.re ((Yᴴ * Y) i i) = ∑ j, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma re_mul_diagonal_mul_conjTranspose_apply (Y : Matrix κ ι 𝕜) (d : ι → ℝ) (j : κ) :
    RCLike.re ((Y * (diagonal (RCLike.ofReal ∘ d) : Matrix ι ι 𝕜) * Yᴴ : Matrix κ κ 𝕜) j j)
      = ∑ i, ‖Y j i‖ ^ 2 * d i := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, conjTranspose_apply, Function.comp_apply, RCLike.star_def,
    show Y j i * (d i : 𝕜) * starRingEnd 𝕜 (Y j i) = (d i : 𝕜) * (Y j i * starRingEnd 𝕜 (Y j i))
      by ring,
    RCLike.mul_conj,
    show ((d i : 𝕜) * ((‖Y j i‖ : 𝕜) ^ 2) : 𝕜) = ((‖Y j i‖ ^ 2 * d i : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

lemma sum_normSq_col_eigenvectorUnitary {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (i : ι) :
    ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 = 1 := by
  have h := re_conjTranspose_mul_apply_self (hM.eigenvectorUnitary : Matrix ι ι 𝕜) i
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2] at h
  simpa using h.symm

end Entries

section Mix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def compressWeight {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
  ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2


lemma compressWeight_le_one {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) (i : ι) : compressWeight hM g i ≤ 1 := by
  unfold compressWeight
  calc ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
      = ∑ k ∈ univ.image g, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        (Finset.sum_image (f := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2)
          (s := univ) (g := g) hg.injOn).symm
    _ ≤ ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = 1 := sum_normSq_col_eigenvectorUnitary hM i

lemma sum_compressWeight_fiberwise {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (β : ι → κ) (i : ι) :
    ∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i = 1 := by
  unfold compressWeight
  have h : ∀ b : κ, ∑ j : (univ.filter fun i => β i = b),
      ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (j : ι) i‖ ^ 2
        = ∑ j ∈ univ.filter (fun i => β i = b), ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2 :=
    fun b => Finset.sum_coe_sort (univ.filter fun i => β i = b)
      (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)
  simp only [h]
  rw [Finset.sum_fiberwise univ β (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)]
  exact sum_normSq_col_eigenvectorUnitary hM i

theorem eigenvalues_submatrix_eq_mix {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) :
    ∃ S : κ → ι → ℝ, (∀ j i, 0 ≤ S j i) ∧ (∀ j, ∑ i, S j i = 1)
      ∧ (∀ i, ∑ j, S j i = compressWeight hM g i)
      ∧ ∀ j, (hM.submatrix g).eigenvalues j = ∑ i, S j i * hM.eigenvalues i := by
  set U : Matrix ι ι 𝕜 := (hM.eigenvectorUnitary : Matrix ι ι 𝕜) with hUdef
  have hP : (M.submatrix g g).IsHermitian := hM.submatrix g
  set V : Matrix κ κ 𝕜 := (hP.eigenvectorUnitary : Matrix κ κ 𝕜) with hVdef
  set Ug : Matrix κ ι 𝕜 := U.submatrix g id with hUgdef
  set Y : Matrix κ ι 𝕜 := star V * Ug with hYdef
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have hVsV : star V * V = 1 := Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
  have hVVs : V * star V = 1 := Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2

  have hM' : M = U * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]

  have hUgUg : Ug * Ugᴴ = 1 := by
    rw [hUgdef, conjTranspose_submatrix, ← star_eq_conjTranspose,
      ← Matrix.submatrix_mul _ _ g id g Function.bijective_id, hUU, submatrix_one _ hg]
  have hPsub : M.submatrix g g = Ug * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Ugᴴ := by
    conv_lhs => rw [hM']
    rw [Matrix.submatrix_mul _ _ g id g Function.bijective_id,
      Matrix.submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id, hUgdef,
      conjTranspose_submatrix, star_eq_conjTranspose]

  have hdiag0 : diagonal (RCLike.ofReal ∘ hP.eigenvalues) = star V * M.submatrix g g * V := by
    rw [← hP.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_star_apply]
  have hdiag : diagonal (RCLike.ofReal ∘ hP.eigenvalues)
      = Y * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Yᴴ := by
    rw [hdiag0, hPsub, hYdef, conjTranspose_mul, star_eq_conjTranspose V,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hYY : Y * Yᴴ = 1 := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Ug, hUgUg, Matrix.one_mul, ← star_eq_conjTranspose,
      hVsV]
  have hYtY : Yᴴ * Y = Ugᴴ * Ug := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, ← star_eq_conjTranspose V, hVVs, Matrix.one_mul]
  refine ⟨fun j i => ‖Y j i‖ ^ 2, fun j i => by positivity, ?_, ?_, ?_⟩
  · intro j
    show ∑ i, ‖Y j i‖ ^ 2 = 1
    have h := re_mul_conjTranspose_apply_self Y j
    rw [hYY] at h
    simpa using h.symm
  · intro i
    show ∑ j, ‖Y j i‖ ^ 2 = compressWeight hM g i
    have h1 := re_conjTranspose_mul_apply_self Y i
    have h2 := re_conjTranspose_mul_apply_self Ug i
    rw [hYtY] at h1
    rw [← h1, h2]
    rfl
  · intro j
    show hP.eigenvalues j = ∑ i, ‖Y j i‖ ^ 2 * hM.eigenvalues i
    have h := re_mul_diagonal_mul_conjTranspose_apply Y hM.eigenvalues j
    rw [← hdiag, diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re] at h
    exact h

end Mix

section Pinching

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sum_eigenvalues_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ j, f ((hM.submatrix g).eigenvalues j)
      ≤ ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by
  obtain ⟨S, hS0, hSrow, hScol, hSeig⟩ := eigenvalues_submatrix_eq_mix hM hg
  calc ∑ j, f ((hM.submatrix g).eigenvalues j)
      = ∑ j, f (∑ i, S j i * hM.eigenvalues i) := by simp only [hSeig]
    _ ≤ ∑ j, ∑ i, S j i * f (hM.eigenvalues i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := hf.map_sum_le (t := Finset.univ) (w := S j) (p := hM.eigenvalues)
          (fun i _ => hS0 j i) (hSrow j) (fun i _ => Set.mem_univ _)
        simpa only [smul_eq_mul] using h
    _ = ∑ i, (∑ j, S j i) * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by simp only [hScol]

theorem sum_eigenvalues_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ i, f (hM.eigenvalues i) := by
  calc ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ b, ∑ i, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i
            * f (hM.eigenvalues i) :=
        Finset.sum_le_sum fun b _ => sum_eigenvalues_submatrix_le hM Subtype.val_injective hf
    _ = ∑ i, (∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i)
            * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, f (hM.eigenvalues i) := by simp only [sum_compressWeight_fiberwise, one_mul]

theorem sum_eigenvalues_submatrix_le_of_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    {g : κ → ι} (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∑ j, f ((hM.submatrix g).eigenvalues j) ≤ ∑ i, f (hM.eigenvalues i) :=
  (sum_eigenvalues_submatrix_le hM hg hf).trans <| Finset.sum_le_sum fun i _ => by
    calc compressWeight hM g i * f (hM.eigenvalues i) ≤ 1 * f (hM.eigenvalues i) :=
          mul_le_mul_of_nonneg_right (compressWeight_le_one hM hg i) (hf0 _)
      _ = f (hM.eigenvalues i) := one_mul _

theorem rtrace_specMap_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, rtrace (specMap (hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)) f)
      ≤ rtrace (specMap hM f) := by
  simp only [rtrace_specMap]
  exact sum_eigenvalues_pinching_le hM hf β

theorem rtrace_specMap_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ t, 0 ≤ f t) :
    rtrace (specMap (hM.submatrix g) f) ≤ rtrace (specMap hM f) := by
  rw [rtrace_specMap, rtrace_specMap]
  exact sum_eigenvalues_submatrix_le_of_nonneg hM hg hf hf0

end Pinching


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S8.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real RHLinalg
open Zeta23 Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

theorem seamA_mult2_defect {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {D : ℝ}
    (hcore : 4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) + D ≤ (Z.s1 T : ℝ)) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      + D ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le

  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (AMW.atAM P T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (AMW.atAM P T) T = (AMW.atAM P T).Gp T)
    (hId : ∀ᶠ T in atTop, (AMW.atAM P T).trGtilde T = trG T ∧ (AMW.atAM P T).trGtildeSq T = trG2 T ∧
      (AMW.atAM P T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0))
    (D : ℝ → ℝ)
    (hcore : ∀ᶠ T in atTop,
      4 * rtrace ((AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T))
        - frobSq ((AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T))
        - 2 * (Z.NIprime T : ℝ) + D T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) + D T ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII

  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr

  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'

  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T - err T ≤ (Z.N0s T (2 * T) : ℝ) - D T := by
    filter_upwards [hcore, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hcoreT hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (AMW.atAM P T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity

    have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT

    have hrt : rtrace ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (AMW.atAM P T).a T * (AMW.atAM P T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA

    have hA' : 4 * ((aT T * P.L T)⁻¹ * trG T) - ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
        - θ₀ T / (aT T * P.L T)
            * (4 + 2 * Real.sqrt (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + θ₀ T / (aT T * P.L T))
        ≤ (Z.N0s T (2 * T) : ℝ) - D T := by linarith [hA]

    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)

    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA' htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith

  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM

  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring

  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2

  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]

  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)

  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1

  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6

  have hfin := eps_form_of_isLittleO (lower := fun T => (Z.N0s T (2 * T) : ℝ) - D T) hmain
    (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hfin ε hε
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have := hT₀ T hT
  simp only [hNdef] at this
  linarith


end Zeta23Ext.Bridge

end

/-! ###### AMW module: BrB ###### -/

/-
AMW/BrB.lean — bridge part B (Helpers_S9: gram entries, window, tail, limit, assembly, strips).
Retargeted copy of the Zeta Lab bridge (MIT) as carried in SolutionSevW10D.lean, lines 1029-1739:
the Montgomery–Taylor window replaced by the AMTOPA window (AMW.atAM, AMW.KfunAM, AMW.HW).
-/

set_option linter.all false

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S9.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

section GramEntry

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

lemma bdata_v_eq (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (bdata Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
  simp only [bdata, blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]

lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
    gram Z P T z z' =
      (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
        P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hentry : ∀ a b : (bdata Z P T).S₁, gramS₁ (bdata Z P T) (aL2 P T) a b
      = ∑ k, star (Vsimple (bdata Z P T) (aL2 P T) k a) * Vsimple (bdata Z P T) (aL2 P T) k b := by
    intro a b
    simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
  unfold gram
  rw [Matrix.submatrix_apply, hentry]
  have e : ∀ k : Fin (P.d T),
      star (Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z))
        * Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z')
      = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
          * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
    intro k
    have h1 : (bdata Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz k
    have h2 : (bdata Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz' k
    simp only [Vsimple]
    rw [h1, h2]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq]
    push_cast
    ring
  simp_rw [e]
  rw [← Complex.ofReal_sum, Finset.mul_sum]

end GramEntry

section Window

@[simp] lemma atAM_L (P : Params) (T : ℝ) : (AMW.atAM P T).L = P.L := rfl


variable {P : Params} (hP : P.Valid) (T : ℝ)
include hP

lemma atAM_phiHatR_eq : (AMW.atAM P T).phiHatR T = AdmWindow.vHatR (AMW.WAM P T) :=
  AMW.atW_phiHatR T hP (AMW.WAM_even P T)

lemma phiHatReal_atAM : PhiHatReal T (AMW.atAM P T) := fun r => GzGp.phiHat_ofReal _ T r


end Window

section Tail

lemma Wfun_le_of_L_le {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Δ : ℝ} (hΔ : p.L ≤ Δ) :
    PrimeSide.Wfun c p Δ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h8 := hF.eight_le_L
  have hL : 0 < p.L := hF.L_pos
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hL hΔ
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  set K : ℝ := (c / p.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hπ := Real.pi_pos

  have hψ : PrimeSide.psiA c p Δ ^ 2 ≤ K / Δ ^ 4 := by
    have h1 : PrimeSide.psiA c p Δ ≤ c / (p.w * Δ ^ 2) := PrimeSide.psiA_le_div_sq hΔ0.ne'
    calc PrimeSide.psiA c p Δ ^ 2 ≤ (c / (p.w * Δ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Δ) h1 2
      _ = K / Δ ^ 4 := by rw [hK]; field_simp

  have hint : ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2 ≤ K / (3 * Δ ^ 3) :=
    PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ0
  have hh : (p.h)⁻¹ = p.L / (2 * Real.pi) := by
    unfold PrimeSide.Setting.h; rw [inv_div]
  have hhpos : 0 ≤ (p.h)⁻¹ := by rw [hh]; positivity

  have hΔ4 : p.L ^ 2 ≤ Δ ^ 4 := by
    have : p.L ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hL.le hΔ 2
    have h2 : (1 : ℝ) ≤ Δ ^ 2 := by nlinarith
    calc p.L ^ 2 ≤ Δ ^ 2 := this
      _ = Δ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Δ ^ 2 * Δ ^ 2 := by gcongr
      _ = Δ ^ 4 := by ring
  have hA : K / Δ ^ 4 ≤ K / p.L ^ 2 :=
    div_le_div_of_nonneg_left hK0 (by positivity) hΔ4
  have hB : (p.h)⁻¹ * (K / (3 * Δ ^ 3)) ≤ K / p.L ^ 2 := by
    rw [hh]
    have e : p.L / (2 * Real.pi) * (K / (3 * Δ ^ 3)) = K * (p.L / (6 * Real.pi * Δ ^ 3)) := by
      field_simp; ring
    rw [e]
    have hΔ3 : p.L ^ 3 ≤ Δ ^ 3 := pow_le_pow_left₀ hL.le hΔ 3
    have h3 : p.L / (6 * Real.pi * Δ ^ 3) ≤ 1 / p.L ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : p.L * p.L ^ 2 = p.L ^ 3 := by ring
      rw [this]
      nlinarith [Real.pi_gt_three, pow_pos hΔ0 3]
    calc K * (p.L / (6 * Real.pi * Δ ^ 3)) ≤ K * (1 / p.L ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = K / p.L ^ 2 := by ring
  unfold PrimeSide.Wfun
  calc PrimeSide.psiA c p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2
      ≤ K / Δ ^ 4 + (p.h)⁻¹ * (K / (3 * Δ ^ 3)) := by
        gcongr
    _ ≤ K / p.L ^ 2 + K / p.L ^ 2 := add_le_add hA hB
    _ = 2 * K / p.L ^ 2 := by ring

lemma rho_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj := PrimeSide.rho_le_majorant hF hT hτ
  have hW1 := Wfun_le_of_L_le hF h1
  have hW2 := Wfun_le_of_L_le hF h2
  have hψ : PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / p.w) ^ 2 / p.L ^ 2 := by
    have hΔ0 : 0 < p.tau p.d - τ := lt_of_lt_of_le hL h3
    have hw : 0 < p.w := by linarith [hF.one_le_w]
    have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
    have hb : PrimeSide.psiA c p (p.tau p.d - τ) ≤ c / (p.w * (p.tau p.d - τ) ^ 2) :=
      PrimeSide.psiA_le_div_sq hΔ0.ne'
    have hΔ4 : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 4 := by
      have h8 := hF.eight_le_L
      have : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := pow_le_pow_left₀ hL.le h3 2
      have h2' : (1 : ℝ) ≤ (p.tau p.d - τ) ^ 2 := by nlinarith
      calc p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := this
        _ = (p.tau p.d - τ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (p.tau p.d - τ) ^ 2 * (p.tau p.d - τ) ^ 2 := by gcongr
        _ = (p.tau p.d - τ) ^ 4 := by ring
    calc PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF _) hb 2
      _ = (c / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by field_simp
      _ ≤ (c / p.w) ^ 2 / p.L ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΔ4
  calc PrimeSide.rho p F τ
      ≤ PrimeSide.Wfun c p (τ - p.T) + PrimeSide.Wfun c p (2 * p.T - τ)
          + PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 := hmaj
    _ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 + 2 * (c / p.w) ^ 2 / p.L ^ 2 + (c / p.w) ^ 2 / p.L ^ 2 :=
        add_le_add (add_le_add hW1 hW2) hψ
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

lemma abs_Kinf_sub_Kfun_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
    (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
    |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
  have hρ := rho_le_of_far hF hT h1 h2 h3
  have hρ' := rho_le_of_far hF hT h1' h2' h3'
  calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
      ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
    _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
        gcongr
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

end Tail

section Limit

lemma Kfun_zero_pos : 0 < Kfun 0 := AMW.KfunAM_zero_pos

lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := AMW.abs_KfunAM_le x

lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  unfold paperFT
  have hexp : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by fun_prop
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine hg.ofReal.mul_bdd (c := 1) hexp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]
    simp
  rw [← integral_re_C hint]
  congr 1 with u
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- the sharp cutoff against the frequency `2πx/L` is `(L/MAM)·K(x)`. -/
lemma integral_sW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, AMW.sW L u * Real.cos (2 * Real.pi * x / L * u) = L / AMW.MAM * Kfun x := by
  set f : ℝ → ℝ := fun s => AMW.vAM s / AMW.MAM * Real.cos (2 * Real.pi * x * s) with hf
  have hind : ∀ u, AMW.sW L u * Real.cos (2 * Real.pi * x / L * u)
      = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
    intro u
    unfold AMW.sW
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
      simp only [AMW.hW]
      rw [show 2 * Real.pi * x / L * u = 2 * Real.pi * x * (u / L) by ring]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), AMW.integral_scale (v := f) hL]
  have e : (fun s => f s) = fun s => AMW.vAM s * Real.cos (2 * Real.pi * x * s) / AMW.MAM := by
    funext s; simp only [hf]; ring
  rw [e, intervalIntegral.integral_div]
  unfold Kfun AMW.KfunAM
  ring

lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
  have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
  have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hfi : Integrable fun u => f u * Real.cos (r * u) :=
    hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hgi : Integrable fun u => g u * Real.cos (r * u) :=
    hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  rw [← integral_sub hfi hgi]
  calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
      ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
        refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

variable {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP h8

lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) - P.L T / AMW.MAM * Kfun x| ≤ 2 * P.w := by
  have hW := AMW.admWindow_WAM hP T h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (AMW.WAM P T) r = ∫ u, AMW.WAM P T u ^ 2 * Real.cos (r * u) :=
    re_paperFT_ofReal (hW.integrable_pow two_pos) r
  have hS : ∫ u, AMW.sW (P.L T) u * Real.cos (r * u) = P.L T / AMW.MAM * Kfun x :=
    integral_sW_mul_cos hL x
  have hL1 : ∫ u, |AMW.WAM P T u ^ 2 - AMW.sW (P.L T) u| ≤ 2 * P.w :=
    AMW.integral_abs_phiWsq_sub_sharp hP.taper hw (by linarith)
  rw [hV, ← hS]
  exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) (AMW.sW_integrable _) r).trans hL1

lemma abs_aL_sub_L_mul_Kfun_zero_le :
    |(AMW.atAM P T).a T * P.L T - P.L T / AMW.MAM * Kfun 0| ≤ 2 * P.w := by
  have hW := AMW.admWindow_WAM hP T h8
  have h := abs_VPhiR_sub_L_mul_Kfun_le hP h8 0
  rw [mul_zero, zero_div, hW.VPhiR_zero] at h
  rw [AMW.atAM_a hP T]
  exact h

lemma abs_VPhiR_div_sub_kfun_le (h32 : 32 * P.w ≤ P.L T) (x : ℝ) :
    |AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) / ((AMW.atAM P T).a T * P.L T) - kfun x|
      ≤ 12 * P.w / P.L T := by
  have hW := AMW.admWindow_WAM hP T h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have hM := AMW.MAM_pos
  have ha : 1 / 2 ≤ (AMW.atAM P T).a T := (AMW.aAM_range_of hP h32).1
  have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP h8 x
  have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP h8
  have hK0 : 0 < Kfun 0 := Kfun_zero_pos
  have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
  set V := AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) with hV
  set A := (AMW.atAM P T).a T * P.L T with hA
  set K := Kfun x with hK'
  set K0 := Kfun 0 with hK0'
  set c := P.L T / AMW.MAM with hc
  have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have e : V / A - K / K0 = (V - c * K) / A + K * (c * K0 - A) / (A * K0) := by
    field_simp
    ring
  unfold kfun
  rw [e]
  have h2' : |c * K0 - A| ≤ 2 * P.w := by rw [abs_sub_comm]; exact h2
  calc |(V - c * K) / A + K * (c * K0 - A) / (A * K0)|
      ≤ |(V - c * K) / A| + |K * (c * K0 - A) / (A * K0)| := abs_add_le _ _
    _ = |V - c * K| / A + |K| * |c * K0 - A| / (A * K0) := by
        rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
    _ ≤ 2 * P.w / A + K0 * (2 * P.w) / (A * K0) := by gcongr
    _ = 4 * P.w / A := by field_simp; ring
    _ ≤ 12 * P.w / P.L T := by
        rw [div_le_div_iff₀ hApos hL]
        nlinarith

end Limit

section Assembly

lemma retained_far {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    {z : ZI Z T} (hz : z ∈ retained Z P T) :
    P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
  unfold xnorm at h1 h2
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * ((z : ℂ).im - T) := by
    have := (le_div_iff₀ hπ).mp h1; linarith
  have h2' : P.L T * ((z : ℂ).im - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
    have := (div_le_iff₀ hπ).mp h2; linarith
  have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
    have := (le_div_iff₀ hπ).mp hd; linarith
  have g1 : 2 * Real.pi * P.L T ≤ (z : ℂ).im - T := by
    have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * ((z : ℂ).im - T) := by nlinarith
    exact le_of_mul_le_mul_left this hL
  have g2 : 2 * Real.pi * P.L T ≤ 2 * T - (z : ℂ).im := by
    have : P.L T * ((z : ℂ).im - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
    have := le_of_mul_le_mul_left this hL
    linarith
  have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩

  have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
    simp only [Params.tau, Params.hgrid, Int.cast_natCast]
  rw [htau]
  have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - (z : ℂ).im
      = (2 * Real.pi * (P.d T : ℝ) - P.L T * ((z : ℂ).im - T)) / P.L T := by
    field_simp
    ring
  rw [e, le_div_iff₀ hL]
  nlinarith

lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
    PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
      = ∑ k : Fin ((AMW.atAM P T).d T), (AMW.atAM P T).phiHatR T (γ - (AMW.atAM P T).tau T k)
          * (AMW.atAM P T).phiHatR T (γ' - (AMW.atAM P T).tau T k) := by
  rw [atAM_phiHatR_eq hP T]; rfl

lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
      = P.L T * AdmWindow.VPhiR (AMW.WAM P T) (γ - γ') := rfl

theorem gram_close_of {P : Params} (hP : P.Valid) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T) (h32 : 32 * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (AMW.cAMW P.ϱ) (P.toSetting T) (AMW.lfW P (AMW.WAM P) T))
    (Z : ZeroConfig) (z z' : retained Z (AMW.atAM P T) T) :
    ‖gram Z (AMW.atAM P T) T z z'
        - (kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z') : ℂ)‖
      ≤ 10 * (AMW.cAMW P.ϱ / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := AMW.admWindow_WAM hP T h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (AMW.atAM P T).a T := (AMW.aAM_range_of hP h32).1
  have hc : 0 < aL2 (AMW.atAM P T) T := by
    unfold aL2; rw [atAM_L]; exact mul_pos (by linarith) (pow_pos hL 2)
  set K : ℝ := (AMW.cAMW P.ϱ / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  rw [gram_apply Z (AMW.atAM P T) T (phiHatReal_atAM hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'

  obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := AMW.atAM P T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := AMW.atAM P T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'

  have hx : 2 * Real.pi * (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z') / P.L T
      = γ - γ' := by
    unfold xret xnorm
    rw [atAM_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP h8 h32
    (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')
  rw [hx] at hlim

  set A : ℝ := (AMW.atAM P T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (AMW.WAM P T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' = P.L T * V :=
    Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (AMW.atAM P T) T = A * P.L T ^ 2 := by unfold aL2; rw [atAM_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z'))|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
        + |V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')| :=
          abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
        + |V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
    _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
        gcongr
    _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
        field_simp
        ring

end Assembly

section Strips

variable (Z : ZeroConfig)

lemma window_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by
  ext ρ
  simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hc⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hc⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 hb, hc⟩

lemma N_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
  unfold ZeroConfig.N
  rw [window_union Z h1 h2]
  refine finsum_mem_union ?_ (Z.finite_window a b) (Z.finite_window b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, hb', _⟩
  exact absurd hb (not_le.2 hb')

lemma N_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Z.N a b ≤ Z.N c d := by
  unfold ZeroConfig.N
  have hsub : Z.window a b ⊆ Z.window c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  have hfab : (Z.window a b).Finite := Z.finite_window a b
  have hfcd : (Z.window c d).Finite := Z.finite_window c d
  rw [finsum_mem_eq_finite_toFinset_sum _ hfab, finsum_mem_eq_finite_toFinset_sum _ hfcd]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

lemma ncard_window_le_N (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
  unfold ZeroConfig.N
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exact Z.one_le_mult ρ hρ.1

lemma N_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
    (Z.N a (a + n) : ℝ) ≤ n * A₀ * Real.log (|a| + n + 3) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul]
    have : Z.N a a = 0 := by
      unfold ZeroConfig.N
      have : Z.window a a = ∅ := by
        ext ρ
        simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨_, h1, h2⟩; linarith
      rw [this, finsum_mem_empty]
    rw [this]; simp
  | succ n ih =>
    have hsplit : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc]
      exact N_add Z (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) (by linarith)
    rw [hsplit]
    push_cast
    have h1 := hloc (a + n)
    have hlogmono : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogmono' : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith [abs_add_le a (n : ℝ), abs_of_nonneg (n.cast_nonneg : (0:ℝ) ≤ n)])
    have hA : 0 ≤ A₀ := by linarith
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    calc ((Z.N a (a + n) : ℕ) : ℝ) + ((Z.N (a + n) (a + n + 1) : ℕ) : ℝ)
        ≤ n * A₀ * Real.log (|a| + n + 3) + A₀ * Real.log (|a + n| + 3) := add_le_add ih h1
      _ ≤ n * A₀ * Real.log (|a| + (n + 1) + 3) + A₀ * Real.log (|a| + (n + 1) + 3) := by
          gcongr
      _ = (n + 1) * A₀ * Real.log (|a| + (n + 1) + 3) := by ring

lemma N_le_of_local_count_real {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (Z.N a (a + ℓ) : ℝ) ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by
  set n : ℕ := ⌈ℓ⌉₊ with hn
  have hn1 : ℓ ≤ n := Nat.le_ceil ℓ
  have hn2 : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ
  have hA : 0 ≤ A₀ := by linarith
  have hmono : (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := by
    exact_mod_cast N_mono Z le_rfl (by linarith)
  have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + ℓ + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg a, (n.cast_nonneg : (0:ℝ) ≤ n)])
  calc (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := hmono
    _ ≤ n * A₀ * Real.log (|a| + n + 3) := N_le_of_local_count Z hA₀ hloc a n
    _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr

end Strips

section StripInclusion

lemma N0s_le_card_retained_add (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
    (Z.N0s T (2 * T) : ℝ) ≤ (retained Z P T).card
      + Z.N T (T + 2 * Real.pi * P.L T)
      + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
  classical
  set ℓ : ℝ := 2 * Real.pi * P.L T with hℓ
  set ℓ' : ℝ := 2 * Real.pi * P.L T + 2 * Real.pi / P.L T with hℓ'
  set A : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple with hA
  set R : Finset ℂ := (retained Z P T).map (Function.Embedding.subtype _) with hR
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have hsub : A ⊆ (↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T) := by
    rintro ρ ⟨⟨⟨hρc, hT1, hT2⟩, hre⟩, hm⟩
    have hre' : ρ.re = 1 / 2 := hre
    have hm' : Z.mult ρ = 1 := hm
    have hρZ : ρ ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      exact ⟨hρc, by linarith, by linarith⟩
    set z : ZI Z T := ⟨ρ, hρZ⟩ with hz
    have hzS : z ∈ (bdata Z P T).S₁ := by
      simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
    by_cases hx : P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
    · left; left
      rw [Finset.mem_coe, hR, Finset.mem_map]
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · left; right
        refine ⟨hρc, hT1, ?_⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (div_lt_iff₀ hπ).mp hx
        have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
        have := lt_of_mul_lt_mul_left this hL.le
        show ρ.im ≤ T + ℓ
        linarith
      · right
        refine ⟨hρc, ?_, hT2⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (lt_div_iff₀ hπ).mp hx
        have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
        have hd' := (div_lt_iff₀ hπ).mp hd
        have hLℓ' : P.L T * ℓ' = 2 * Real.pi * P.L T ^ 2 + 2 * Real.pi := by
          rw [hℓ']; field_simp
        have : P.L T * (2 * T - ℓ') < P.L T * ρ.im := by nlinarith
        exact lt_of_mul_lt_mul_left this hL.le
  have hfin : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).Finite :=
    ((R.finite_toSet).union (Z.finite_window _ _)).union (Z.finite_window _ _)
  have hN0s : Z.N0s T (2 * T) = A.ncard := rfl
  have hcard : ((↑R : Set ℂ).ncard : ℝ) = (retained Z P T).card := by
    rw [Set.ncard_coe_finset, hR, Finset.card_map]
  have hlo := ncard_window_le_N Z T (T + ℓ)
  have hhi := ncard_window_le_N Z (2 * T - ℓ') (2 * T)
  have hu : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).ncard
      ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_union_le _ _).trans (by gcongr; exact Set.ncard_union_le _ _)
  have hle : A.ncard ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard
      + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_le_ncard hsub hfin).trans hu
  rw [hN0s]
  calc (A.ncard : ℝ) ≤ ((↑R : Set ℂ).ncard : ℝ) + (Z.window T (T + ℓ)).ncard
        + (Z.window (2 * T - ℓ') (2 * T)).ncard := by exact_mod_cast hle
    _ ≤ (retained Z P T).card + Z.N T (T + ℓ) + Z.N (2 * T - ℓ') (2 * T) := by
        rw [hcard]
        have hlo' : ((Z.window T (T + ℓ)).ncard : ℝ) ≤ Z.N T (T + ℓ) := by exact_mod_cast hlo
        have hhi' : ((Z.window (2 * T - ℓ') (2 * T)).ncard : ℝ) ≤ Z.N (2 * T - ℓ') (2 * T) := by
          exact_mod_cast hhi
        linarith

end StripInclusion

section StripCount

lemma strips_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T L : ℝ} (hT : 1 ≤ T)
    (hL1 : 1 ≤ L) (hLT : L ≤ T) (hlogT : Real.log T ≤ L + 2 * Real.pi) :
    (Z.N T (T + 2 * Real.pi * L) : ℝ) + Z.N (2 * T - (2 * Real.pi * L + 2 * Real.pi / L)) (2 * T)
      ≤ 1600 * A₀ * L ^ 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hπ3 := Real.pi_gt_three
  have hA : 0 ≤ A₀ := by linarith
  set ℓ : ℝ := 2 * Real.pi * L with hℓ
  set ℓ' : ℝ := 2 * Real.pi * L + 2 * Real.pi / L with hℓ'
  have hLpos : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by positivity
  have h2πL : 2 * Real.pi / L ≤ 2 * Real.pi * L := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hℓ'0 : 0 ≤ ℓ' := by positivity
  have hℓ'le : ℓ' ≤ 4 * Real.pi * L := by rw [hℓ']; linarith
  have hℓle : ℓ ≤ ℓ' := by
    have : 0 ≤ 2 * Real.pi / L := by positivity
    rw [hℓ, hℓ']; linarith
  have h1 := N_le_of_local_count_real Z hA₀ hloc T hℓ0
  have h2 := N_le_of_local_count_real Z hA₀ hloc (2 * T - ℓ') hℓ'0
  rw [sub_add_cancel] at h2

  set M : ℝ := (6 + 8 * Real.pi) * T with hM
  have hM1 : |T| + ℓ + 4 ≤ M := by
    rw [abs_of_pos (by linarith), hM]; nlinarith
  have hM2 : |2 * T - ℓ'| + ℓ' + 4 ≤ M := by
    have : |2 * T - ℓ'| ≤ 2 * T + ℓ' := by
      rw [abs_le]; constructor <;> linarith
    rw [hM]; nlinarith
  have hlogM : Real.log M ≤ (6 + 10 * Real.pi) * L := by
    have hT0 : 0 < T := by linarith
    rw [hM, Real.log_mul (by positivity) hT0.ne']
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
    nlinarith
  have hlog1 : Real.log (|T| + ℓ + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM1).trans hlogM
  have hlog2 : Real.log (|2 * T - ℓ'| + ℓ' + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM2).trans hlogM
  have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith
  have hcoef' : ℓ + 1 ≤ (4 * Real.pi + 1) * L := by linarith
  have hb1 : (Z.N T (T + ℓ) : ℝ) ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h1.trans ?_
    have h0 : 0 ≤ Real.log (|T| + ℓ + 4) := Real.log_nonneg (by linarith [abs_nonneg T])
    gcongr
  have hb2 : (Z.N (2 * T - ℓ') (2 * T) : ℝ)
      ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h2.trans ?_
    have h0 : 0 ≤ Real.log (|2 * T - ℓ'| + ℓ' + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * T - ℓ')])
    gcongr
  have hL2 : 0 ≤ A₀ * L ^ 2 := by positivity
  have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith
  calc (Z.N T (T + ℓ) : ℝ) + Z.N (2 * T - ℓ') (2 * T)
      ≤ 2 * ((4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L)) := by linarith
    _ = 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) * (A₀ * L ^ 2) := by ring
    _ ≤ 1600 * (A₀ * L ^ 2) := by
        gcongr
    _ = 1600 * A₀ * L ^ 2 := by ring

end StripCount

end Zeta23Ext.Bridge

end

/-! ###### AMW module: BrC ###### -/

/-
AMW/BrC.lean — bridge part C (S6–S15, BridgeW).
Retargeted copy of the Zeta Lab bridge (MIT) as carried in SolutionSevW10D.lean, lines 1743-4583:
the Montgomery–Taylor window replaced by the AMTOPA window (AMW.atAM, AMW.KfunAM, AMW.HW).
-/

set_option linter.all false

/-! ###### source module: Zeta23Ext/Bridge/S6.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def multPart (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma mem_S₂_σ {z : ι} (hz : z ∈ D.S₂) : D.σ z = z := by
  simp only [ZeroBlockData.S₂, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_σ {z : ι} (hz : z ∈ D.S₁) : D.σ z = z := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_m {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.2

lemma multPart_posSemidef {c : ℝ} (hc : 0 < c) : (multPart D c).PosSemidef := by
  unfold multPart
  refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rank_multPart_le {c : ℝ} (hc : 0 < c) : (multPart D c).rank ≤ D.s₂ := by
  unfold multPart
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp [ZeroBlockData.s₂]

lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
    P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
  ext k l
  simp only [P₁, Vsimple, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort D.S₁, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  have hσ := mem_S₁_σ D z.2
  have hm := mem_S₁_m D z.2
  have hstar : star (D.v z l) = D.v z l := congrFun (D.star_v_of_onLine hσ) l
  rw [hm, star_div₀, hstar, Nat.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt c : ℂ)) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [div_mul_div_comm, hsq, Complex.ofReal_inv, inv_mul_eq_div]

lemma Q'_eq_multPart_add_blockQ {c : ℝ} (hc : 0 < c) :
    Q' D c = multPart D c + D.blockQ c := by
  unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart multPart
  rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
  abel

theorem regroup_posIndex (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hR := multPart_posSemidef D hc
  have hH : (multPart D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
  rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
  calc posIndex hH
      ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := by
        rw [posIndex_eq_rank_of_posSemidef hR]
        exact Nat.add_le_add (rank_multPart_le D hc) (D.posIndex_blockQ_le Pr hc)


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S7.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

lemma Vsimple_col_le_one {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.S₁) :
    ∑ k, ‖Vsimple D c k z‖ ^ 2 ≤ 1 := by
  have hz : (z : ι) ∈ D.onLine := by
    have := z.2
    simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at this
    exact (D.mem_onLine).mpr this.1
  have hs : ∀ k, ‖Vsimple D c k z‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
    intro k
    simp only [Vsimple]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
      Real.sq_sqrt hc.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hc]
  exact hPois z hz

theorem count_defect (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ)
      + defect (gramS₁_isHermitian D c) ≤ (D.s₁ : ℝ) := by
  classical
  have hb := regroup_posIndex D Pr hc
  have h := stable_rank_trace (Vsimple D c) (Vsimple_col_le_one D hc hPois) (Q'_isHermitian D c) hb
  have e : Vsimple D c * (Vsimple D c)ᴴ + Q' D c = D.blockP c + D.blockQ c := P₁_add_Q' D c
  rw [e] at h
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card D.S₁ : ℝ) = D.s₁ := by rw [Fintype.card_coe]; rfl
  have hdef : defect (gramS₁_isHermitian D c)
      = rtrace (specMap (isHermitian_conjTranspose_mul_self (Vsimple D c)) Psi) := rfl
  rw [hcard] at h
  push_cast at h
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S8.lean ###### -/


noncomputable section

open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (AMW.HW - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by

  set P : Params := paramsOf stdProfile 1 with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := rfl

  have hLoc := AMW.localHypsCoreAM_eventually hP
  have hTr := AMW.tracesBoundsAM_concrete (Z := Z) hP H
  have hc : Tendsto (fun T => cRatio (P.lam1 T) ((AMW.concreteDataW P (AMW.WAM P) Z).aT T)
      ((AMW.concreteDataW P (AMW.WAM P) Z).bT T) ((AMW.concreteDataW P (AMW.WAM P) Z).JT T)) atTop
      (𝓝 (cRatio P.lam AMW.aInf AMW.bInf AMW.JInf)) := AMW.tendsto_cRatio_W hP
  have hc0 := AMW.cRatio_W_pos hP.lam_pos
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (AMW.concreteDataW P (AMW.WAM P) Z).aT T
      ∧ (AMW.concreteDataW P (AMW.WAM P) Z).aT T ≤ 1 :=
    (AMW.concreteFactsW hP H (AMW.admWindow_WAM hP) hLoc).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := AMW.eventually_tailPackageAM Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := AMW.eventually_GzGpAM Z H hP
  have hId : ∀ᶠ T in atTop,
      (AMW.atAM P T).trGtilde T = (AMW.concreteDataW P (AMW.WAM P) Z).trG T ∧
      (AMW.atAM P T).trGtildeSq T = (AMW.concreteDataW P (AMW.WAM P) Z).trG2 T ∧
      (AMW.atAM P T).a T = (AMW.concreteDataW P (AMW.WAM P) Z).aT T :=
    Eventually.of_forall fun T => AMW.atW_ident Z hP (AMW.WAM_even P) T
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)

  have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
    (fun T => Dcirc Z (mtParams T) T) h7
  intro ε hε
  exact h ε hε


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S9.lean ###### -/


noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

set_option linter.unusedVariables false in

theorem kernel_limit (Z : ZeroConfig) (H : PaperInputs Z) (R₀ : ℝ) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      |xret Z (mtParams T) T z - xret Z (mtParams T) T z'| ≤ R₀ →
      ‖gram Z (mtParams T) T z z'
          - (kfun (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨T₀, hT₀⟩ := AMW.localHypsCoreAM_eventually hP
  set K : ℝ := (AMW.cAMW (paramsOf stdProfile 1).ϱ / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, AMW.eventually_w32 hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h32 hTT₀ hL1 hLδ
  intro z z' _
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hT h8 h32 hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
      ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2

theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
        ≤ ((retained Z (mtParams T) T).card : ℝ) := by
  intro ε hε
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hA0 : 0 < A₀ := by linarith
  have hπ := Real.pi_pos
  set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
  have hcpos : 0 < c := by positivity
  have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.def hcpos
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
    (tendsto_L hP).eventually_ge_atTop 1, hlittle,
    eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
  have hT0 : 0 < T := by linarith
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef

  have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
    rw [hLdef]
    show 1 * Real.log (T / (2 * Real.pi)) = _
    rw [one_mul, Real.log_div hT0.ne' (by positivity)]
  have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
  have hLlogT : L ≤ Real.log T := by linarith
  have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
  have hLT : L ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogc : Real.log T ≤ c * T := by
    have h := hlog
    simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
    exact h

  have hLpos : 0 < (mtParams T).L T := by show 0 < L; linarith
  have hincl := N0s_le_card_retained_add Z (mtParams T) T hLpos
  have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
  have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
    have e1 : (mtParams T).L T = L := rfl
    rw [e1] at hincl
    linarith

  have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have h := hRvM T hTT₀
    have hℓ₁ : L ≤ ell1 T := by
      show 1 * l T ≤ l T + 2 * Real.log 2 - 1
      have := Real.log_two_gt_d9
      linarith
    have h1 := (abs_le.mp h).1
    have h2 : C * Real.log T ≤ |C| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
    have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith

  have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
    have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
        have : L * L ≤ L * (c * T) := by
          have : L ≤ c * T := hLlogT.trans hlogc
          exact mul_le_mul_of_nonneg_left this (by linarith)
        nlinarith
      have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
        rw [hc]; field_simp
      linarith
    have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        nlinarith
      have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
      have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have hL0 : 0 ≤ L := by linarith
        nlinarith
      calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
        _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
        _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
        _ = ε * T * L / (4 * Real.pi) := by ring
    have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
      field_simp
      ring
    linarith
  have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hN hε.le
    nlinarith [hkey]
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S11.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma energyOn_eq_sorted {m : ℕ} (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    energyOn x univ = ∑ r : Fin m × Fin m,
      if r.1 = r.2 then 0 else wfun ((univ.image x).orderEmbOfFin hS r.1
        - (univ.image x).orderEmbOfFin hS r.2) := by
  classical
  set S := univ.image x with hSdef
  set y := S.orderEmbOfFin hS with hydef
  have hy : Function.Injective y := y.injective
  have hSy : univ.image y = S := by
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin S hS
  unfold energyOn
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else wfun (x i - x j))
      = (if x i = x j then 0 else wfun (x i - x j)) := by
    intro i j; simp [hx.eq_iff]
  simp_rw [h1]
  have e1 : ∀ i : ι, ∑ j, (if x i = x j then (0 : ℝ) else wfun (x i - x j))
      = ∑ t ∈ S, (if x i = t then 0 else wfun (x i - t)) := fun i =>
    (sum_image (f := fun t => if x i = t then (0 : ℝ) else wfun (x i - t))
      (fun a _ b _ h => hx h)).symm
  simp_rw [e1]
  rw [← sum_image (f := fun s => ∑ t ∈ S, (if s = t then (0 : ℝ) else wfun (s - t)))
    (fun a _ b _ h => hx h)]
  rw [← hSdef, ← hSy, sum_image (fun a _ b _ h => hy h)]
  simp_rw [sum_image (fun a _ b _ h => hy h)]
  simp only [hy.eq_iff]
  exact (Fintype.sum_prod_type' (f := fun k l => if k = l then (0 : ℝ) else wfun (y k - y l))).symm


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S12.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma specMap_const_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp

lemma specMap_sub_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun t => t - 1) = A - 1 := by
  have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
  rw [h, specMap_sub, specMap_id, specMap_const_one]

lemma offDiagSqOn_le_frobSq_sub_one (A : Matrix ι ι ℂ) :
    offDiagSqOn A univ ≤ frobSq (A - 1) := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  unfold offDiagSqOn
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs with h
  · positivity
  · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]

theorem block_defect_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    min 1 (offDiagSqOn A univ) ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
  ·
    have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
      sum_congr rfl fun i _ => by simp [Psi, hall i]
    have hfrob := frobSq_specMap hA (fun t => t - 1)
    rw [specMap_sub_one] at hfrob
    rw [hsum, ← hfrob]
    exact (min_le_right _ _).trans (offDiagSqOn_le_frobSq_sub_one A)
  ·
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (min_le_left _ _).trans ?_
    calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
          unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
      _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
          single_le_sum (fun j _ => Psi_nonneg (hA.eigenvalues j)) (mem_univ i)

theorem block_defect {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    min 1 (offDiagSqOn G univ) ≤ defect hG.1 :=
  block_defect_of_isHermitian hG.1


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S13.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sq_sub_two_mul_le_sq {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (h : |b - a| ≤ δ) : a ^ 2 - 2 * δ ≤ b ^ 2 := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_or_gt a b with hab | hab
  · nlinarith
  · rcases le_or_gt δ a with hδa | hδa
    · nlinarith
    · nlinarith

lemma wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ} (h : ‖g - (kfun t : ℂ)‖ ≤ δ) :
    wfun t - 2 * δ ≤ ‖g‖ ^ 2 := by
  have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
  have htri : abs (‖g‖ - |kfun t|) ≤ δ := by
    rw [← hk]; exact (abs_norm_sub_norm_le g _).trans h
  have := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
  rw [sq_abs] at this
  exact this

lemma offDiagSqOn_submatrix (G : Matrix ι ι ℂ) (B : Finset ι) :
    offDiagSqOn (G.submatrix (Subtype.val : B → ι) Subtype.val) univ = offDiagSqOn G B := by
  unfold offDiagSqOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [submatrix_apply, Subtype.ext_iff]

lemma energyOn_subtype (x : ι → ℝ) (B : Finset ι) :
    energyOn (fun i : B => x i) univ = energyOn x B := by
  unfold energyOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [Subtype.ext_iff]


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S14.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pinching_partition {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
    ∑ b, blockDefect hM (univ.filter fun i => β i = b) ≤ defect hM := by
  unfold blockDefect defect
  exact rtrace_specMap_pinching_le hM Psi_convexOn β

theorem pinching_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
    defect (hM.submatrix f) ≤ defect hM := by
  unfold defect
  exact rtrace_specMap_submatrix_le hM hf Psi_convexOn Zeta23Ext.StableRankTrace.Psi_nonneg


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S15.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma eq_of_mod_eq_of_overlap {m s s' k : ℕ} (_hm : 0 < m) (h : s % m = s' % m)
    (hs : s ≤ k ∧ k < s + m) (hs' : s' ≤ k ∧ k < s' + m) : s = s' := by
  rcases le_total s s' with h1 | h1
  · have hd : m ∣ s' - s := (Nat.modEq_iff_dvd' h1).mp h
    rcases Nat.eq_zero_or_pos (s' - s) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega
  · have hd : m ∣ s - s' := (Nat.modEq_iff_dvd' h1).mp h.symm
    rcases Nat.eq_zero_or_pos (s - s') with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega

open Classical in

def blockStart (n m j k : ℕ) : ℕ :=
  if h : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m then h.choose else n

lemma blockStart_le (n m j k : ℕ) : blockStart n m j k ≤ n := by
  unfold blockStart
  split_ifs with h
  · have := h.choose_spec.1; omega
  · exact le_rfl

lemma blockStart_eq_iff {n m j k s : ℕ} (hm : 0 < m) (hs : s + m ≤ n) (hj : s % m = j) :
    blockStart n m j k = s ↔ (s ≤ k ∧ k < s + m) := by
  unfold blockStart
  constructor
  · intro h
    split_ifs at h with hex
    · obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      rw [h] at h3; exact h3
    · omega
  · intro hk
    have hex : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m := ⟨s, hs, hj, hk⟩
    rw [dif_pos hex]
    obtain ⟨h1, h2, h3⟩ := hex.choose_spec
    exact eq_of_mod_eq_of_overlap hm (h2.trans hj.symm) h3 hk


end Abstract

section Analytic

open Classical

lemma spanOf_xret_le_d (Z : ZeroConfig) (P : Params) (T : ℝ) :
    spanOf (xret Z P T) univ ≤ (P.d T : ℝ) := by
  have hb : ∀ z : retained Z P T,
      P.L T ^ 2 ≤ xret Z P T z ∧ xret Z P T z ≤ (P.d T : ℝ) - P.L T ^ 2 :=
    fun z => (Finset.mem_filter.mp z.2).2
  unfold spanOf
  split_ifs with h
  · have h1 : (univ : Finset (retained Z P T)).sup' h (xret Z P T) ≤ (P.d T : ℝ) - P.L T ^ 2 :=
      sup'_le _ _ fun z _ => (hb z).2
    have h2 : P.L T ^ 2 ≤ (univ : Finset (retained Z P T)).inf' h (xret Z P T) :=
      le_inf' _ _ fun z _ => (hb z).1
    have : 0 ≤ P.L T ^ 2 := sq_nonneg _
    linarith
  · exact Nat.cast_nonneg _

theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      spanOf (xret Z (mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hV : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hLpos : ∀ᶠ T in atTop, 0 < (mtParams T).L T := (tendsto_L hV).eventually_gt_atTop 0
  set K : ℝ := max ((1 + ε) * C / ε) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hc : (0 : ℝ) < 1 / (2 * Real.pi * (K + 1)) := by positivity
  have hlogT : ∀ᶠ T in atTop, ‖Real.log T‖ ≤ (1 / (2 * Real.pi * (K + 1))) * ‖id T‖ :=
    Real.isLittleO_log_id_atTop.def hc
  have hell : ∀ᶠ T in atTop, 1 ≤ ell1 T := by
    have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    have h' : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1))
        atTop atTop := h.atTop_add tendsto_const_nhds
    exact (h'.eventually_ge_atTop 1).mono fun T hT => by unfold ell1 l; linarith
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * Real.pi), hLpos, hlogT, hell]
    with T hT₀ h2π hL hlog hel
  have hpi : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := lt_of_lt_of_le hpi h2π
  have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
  have hLg0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hl0 : 0 ≤ l T := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
  have hN := abs_le.mp (hRvM T hT₀)

  have hLle : (mtParams T).L T ≤ l T := by
    show (paramsOf stdProfile 1).lam * l T ≤ l T
    exact mul_le_of_le_one_left hl0 hV.lam_le_one
  have hl_ell : l T ≤ ell1 T := by
    unfold ell1; linarith [Real.log_two_gt_d9]
  have hd : ((mtParams T).d T : ℝ) ≤ T / (2 * Real.pi) * ell1 T := by
    have h0 : 0 ≤ (mtParams T).L T * T / (2 * Real.pi) := by positivity
    calc ((mtParams T).d T : ℝ) ≤ (mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le h0
      _ = T / (2 * Real.pi) * (mtParams T).L T := by ring
      _ ≤ T / (2 * Real.pi) * ell1 T := by gcongr; exact hLle.trans hl_ell

  have hKA : K * Real.log T ≤ T / (2 * Real.pi) * ell1 T := by
    simp only [Real.norm_eq_abs, id, abs_of_nonneg hLg0, abs_of_pos hT0] at hlog
    have h1 : K * Real.log T ≤ K * (1 / (2 * Real.pi * (K + 1)) * T) :=
      mul_le_mul_of_nonneg_left hlog hK0
    have h2 : K * (1 / (2 * Real.pi * (K + 1)) * T) ≤ T / (2 * Real.pi) := by
      rw [show K * (1 / (2 * Real.pi * (K + 1)) * T) = T / (2 * Real.pi) * (K / (K + 1)) by
        field_simp]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_right (by positivity) this
    have h3 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T :=
      le_mul_of_one_le_right (by positivity) hel
    linarith
  have h1 : (1 + ε) * C / ε * Real.log T ≤ T / (2 * Real.pi) * ell1 T :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hLg0).trans hKA
  have h2 : (1 + ε) * C * Real.log T ≤ ε * (T / (2 * Real.pi) * ell1 T) := by
    have e : (1 + ε) * C * Real.log T = ε * ((1 + ε) * C / ε * Real.log T) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hε.le
  calc spanOf (xret Z (mtParams T) T) univ ≤ ((mtParams T).d T : ℝ) := spanOf_xret_le_d Z _ T
    _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]

end Analytic


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S16.lean ###### -/


noncomputable section

open Filter
open Zeta23.ThmD

namespace Zeta23Ext.Bridge

lemma one_sub_div_pos {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Main.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

def P₀ : Params := paramsOf stdProfile 1

lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl

lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
  (tendsto_L P₀_valid).eventually_gt_atTop 0

theorem eventually_h7 (Z : ZeroConfig) :
    ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
  filter_upwards [eventually_w8 P₀_valid, AMW.eventually_w32 P₀_valid] with T h8 h32
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (AMW.aAM_range_of P₀_valid h32).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := AMW.poissonSqW P₀_valid (AMW.WAM_even P₀) (AMW.admWindow_WAM P₀_valid) h8
  have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj phiHatReal hPois)
  have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
    pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
      (toS₁_injective Z P T)
  have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hA, hN, hs]
  linarith [h7, hD]


lemma eventually_Ncount_pos : ∀ᶠ T in atTop, 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/BridgeW/DefsW.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

structure WCert (n : ℕ) where
  a : Fin n → Fin n → ℝ
  b : Fin (n - 1) → ℝ

variable {n : ℕ}

def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
  ∑ r, W.b r * g r
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then W.a i j * wfun (ptsN n g j - ptsN n g i) else 0

def WCert.B (W : WCert n) : ℝ := ∑ r, W.b r

def WCert.spanMass (W : WCert n) (s : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then W.a i j else 0

structure WCert.Adm (W : WCert n) : Prop where
  a_nonneg : ∀ i j, 0 ≤ W.a i j
  b_nonneg : ∀ r, 0 ≤ W.b r
  capacity : ∀ s : ℕ, W.spanMass s ≤ 2

lemma WCert.B_nonneg {W : WCert n} (hW : W.Adm) : 0 ≤ W.B :=
  sum_nonneg fun r _ => hW.b_nonneg r


lemma Fw_windowGaps (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
    Fw W (windowGaps n Y i)
      = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
        + ∑ a : Fin n, ∑ b : Fin n,
            if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
  unfold Fw
  have hq : (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (ptsN n (windowGaps n Y i) b - ptsN n (windowGaps n Y i) a) else 0)
      = ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [ptsN_windowGaps, ptsN_windowGaps,
      show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
  rw [hq]
  rfl

section BlockPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sortedOn (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
  sortedExt (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))

def blkPress (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ r : Fin (n - 1), b r * (sortedOn x B ((B.image x).card - (n - 1) + r) - sortedOn x B r)

end BlockPressure


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S11W.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma window_pairs_le_energy_w {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega

  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]

  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2]
    rw [sum_congr rfl hconst, ← sum_mul]

    set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
    have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' hee
      rw [mem_coe, mem_filter] at ht ht'
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
      simp only [hψdef] at hee
      have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
      have hi : t.1 = t'.1 := by omega
      exact Prod.ext hi hee
    have hsub : (T.filter (fun t => φ t = q)).image ψ
        ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
            (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      rw [mem_filter] at ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
      obtain ⟨-, hlt⟩ := hmem t ht.1
      rw [mem_filter, mem_product]
      refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
      simp only [hψdef]
      omega
    have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
      have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
          = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
        rw [sum_image hψinj]
      have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
          ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
      have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
          = W.spanMass r := by
        unfold WCert.spanMass
        rw [sum_filter, sum_product]
      rw [h1]
      exact h2.trans (h3 ▸ hW.capacity r)
    exact mul_le_mul_of_nonneg_right hmass (wfun_nonneg _)
  refine (sum_le_sum hfib).trans ?_

  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

lemma sum_gap_shift (Y : ℕ → ℝ) (r N : ℕ) :
    ∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r)) = Y (N + r) - Y r := by
  have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
  simp_rw [h]
  have := Finset.sum_range_sub (fun i => Y (i + r)) N
  simpa using this


lemma sortedOn_eq {x : ι → ℝ} {B : Finset ι} {m : ℕ} (hS : (B.image x).card = m) (k : ℕ) :
    sortedOn x B k = sortedExt (⇑((B.image x).orderEmbOfFin hS)) k := by
  unfold sortedOn sortedExt
  by_cases hk : k < (B.image x).card
  · have hk' : k < m := hS ▸ hk
    rw [dif_pos hk, dif_pos hk']
    set f : Fin (B.image x).card → ℝ := fun j => (B.image x).orderEmbOfFin hS ⟨j, hS ▸ j.2⟩
      with hf
    have hfs : ∀ j, f j ∈ B.image x := fun j => Finset.orderEmbOfFin_mem _ hS _
    have hmono : StrictMono f := by
      intro j j' hj
      exact ((B.image x).orderEmbOfFin hS).strictMono (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hj))
    have := Finset.orderEmbOfFin_unique rfl hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]
  · have hk' : ¬ k < m := hS ▸ hk
    rw [dif_neg hk, dif_neg hk']

lemma sortedOn_congr {S S' : Finset ℝ} (h : S = S') :
    sortedExt (⇑(S.orderEmbOfFin (rfl : S.card = S.card)))
      = sortedExt (⇑(S'.orderEmbOfFin (rfl : S'.card = S'.card))) := by
  subst h; rfl

theorem block_energy_w' {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x univ + blkPress W.b x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      = blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hquad := window_pairs_le_energy_w hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

theorem block_energy_blk {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x B + blkPress W.b x B := by
  classical
  have hcard : Fintype.card B = m := by simp [hB]
  have hinj : Function.Injective (fun i : B => x i) := by
    intro i j h
    exact Subtype.ext (hx i.2 j.2 h)
  have h := block_energy_w' hn W hW hCert hm hcard (fun i : B => x i) hinj
  rw [energyOn_subtype] at h
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hP : blkPress W.b (fun i : B => x i) univ = blkPress W.b x B := by
    unfold blkPress sortedOn
    rw [sortedOn_congr himg, himg]
  rw [hP] at h
  exact h


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S13W.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem block_bound_w' {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + blkPress W.b x B := by
  classical
  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h
  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 := block_energy_blk hn W hW hCert hm x B hB hx
  have hP0 : 0 ≤ blkPress W.b x B := by
    unfold blkPress
    refine sum_nonneg fun r _ => mul_nonneg (hW.b_nonneg r) ?_

    unfold sortedOn
    have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
    have hr2 := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
    rw [sub_nonneg, sortedExt_of_lt _ hk, sortedExt_of_lt _ hr]
    exact hmono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith
  · rw [min_eq_right h1.le] at hS12
    nlinarith


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S15W.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem offset_average_w {n : ℕ} (hn : 2 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ r, 0 ≤ b r)
    (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : n ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A : ℝ) (hA : 0 ≤ A)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + blkPress b x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m)
      - (∑ r, b r) * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ ≤ m * Dtot := by
  classical
  set N := Fintype.card ι with hNdef
  set Bt : ℝ := ∑ r, b r with hBt
  have hBt0 : 0 ≤ Bt := sum_nonneg fun r _ => hb r
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
    nlinarith [mul_nonneg hBt0 (mul_nonneg hmq0 hspan0),
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
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := by
    intro a b hab hb
    rw [hYdef, sortedExt_of_lt y (lt_trans hab hb), sortedExt_of_lt y hb]
    exact hymono (Fin.mk_lt_mk.mpr hab)

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
  have hsumblock : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib] at h
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
      have hi' : N - m + 1 + i + r < N := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨N - m + 1 + i + r, hi'⟩)
      obtain ⟨c, -, hc⟩ := mem_image.mp (hymem ⟨i + r, by omega⟩)
      rw [hYdef, sortedExt_of_lt y hi', sortedExt_of_lt y (by omega : i + r < N), ← ha, ← hc]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ a) (mem_univ c))
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
  calc A * ((N : ℝ) - m) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ
      ≤ A * ((N : ℝ) - m + 1) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s)
          - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by linarith

end Abstract


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/MainW.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge
open Classical


theorem solve_linear_w {N N0 : ℝ → ℝ} {c : ℝ} {n m : ℕ} (K : ℝ) (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (K - ε) * N T ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (K / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have : K / Dn - ε = (K - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith


def Phi_w' (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (AMW.HW - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

section SpanPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spanOf_le_blkPress_div {n m : ℕ} (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (b : Fin (n - 1) → ℝ)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ b r)
    (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    spanOf x B ≤ blkPress b x B / bmin := by
  classical
  have hn : 2 ≤ n := by omega
  have hm0 : 0 < m := by omega
  have hne : B.Nonempty := by rw [← card_pos, hB]; exact hm0
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
  have hine : (B.image x).Nonempty := by rw [← card_pos, hic]; exact hm0
  set S := B.image x with hSdef
  set y : ℕ → ℝ := sortedOn x B with hydef
  have hyk : ∀ k (hk : k < m), y k = S.orderEmbOfFin hic ⟨k, hk⟩ := by
    intro k hk
    rw [hydef, sortedOn_eq hic, sortedExt_of_lt _ hk]
  have hmono : ∀ a c, a ≤ c → c < m → y a ≤ y c := by
    intro a c hac hc
    rw [hyk a (lt_of_le_of_lt hac hc), hyk c hc]
    exact (S.orderEmbOfFin hic).monotone (Fin.mk_le_mk.mpr hac)

  have hspan : spanOf x B ≤ y (m - 1) - y 0 := by
    unfold spanOf
    rw [dif_pos hne]
    have h1 : B.sup' hne x ≤ S.max' hine := by
      apply sup'_le
      intro i hi
      exact le_max' _ _ (mem_image_of_mem x hi)
    have h2 : S.min' hine ≤ B.inf' hne x := by
      apply le_inf'
      intro i hi
      exact min'_le _ _ (mem_image_of_mem x hi)
    have hlast : y (m - 1) = S.max' hine := by
      rw [hyk (m - 1) (by omega)]
      exact Finset.orderEmbOfFin_last hic hm0
    have hzero : y 0 = S.min' hine := by
      rw [hyk 0 hm0]
      exact Finset.orderEmbOfFin_zero hic hm0
    rw [hlast, hzero]
    linarith

  have hq1 : n - 1 - 1 < n - 1 := by omega
  have h0 : 0 < n - 1 := by omega
  set r0 : Fin (n - 1) := ⟨0, h0⟩ with hr0
  set r1 : Fin (n - 1) := ⟨n - 1 - 1, hq1⟩ with hr1
  have hterm : ∀ r : Fin (n - 1), 0 ≤ b r * (y (m - (n - 1) + r) - y r) := by
    intro r
    have hr := r.2
    exact mul_nonneg (hbmin.le.trans (hb r)) (sub_nonneg.mpr (hmono _ _ (by omega) (by omega)))
  have hsum : b r0 * (y (m - (n - 1) + r0) - y r0) + b r1 * (y (m - (n - 1) + r1) - y r1)
      ≤ blkPress b x B := by
    unfold blkPress
    rw [← hydef, hic]
    have hr01 : r0 ≠ r1 := by
      intro h; rw [hr0, hr1] at h
      have := Fin.mk.inj_iff.mp h; omega
    have := Finset.add_le_sum (s := univ) (f := fun r : Fin (n - 1) => b r * (y (m - (n - 1) + r) - y r))
      (fun r _ => hterm r) (mem_univ r0) (mem_univ r1) hr01
    simpa using this
  have hmid : y (m - 1) - y 0 ≤ (y (m - (n - 1) + r0) - y r0) + (y (m - (n - 1) + r1) - y r1) := by
    simp only [hr0, hr1]
    have e1 : m - (n - 1) + 0 = m - (n - 1) := by omega
    have e2 : m - (n - 1) + (n - 1 - 1) = m - 1 := by omega
    rw [e1, e2]
    have := hmono (n - 1 - 1) (m - (n - 1)) (by omega) (by omega)
    linarith
  have hb0 := hb r0
  have hb1 := hb r1
  have hnn0 : 0 ≤ y (m - (n - 1) + r0) - y r0 := by
    have := r0.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  have hnn1 : 0 ≤ y (m - (n - 1) + r1) - y r1 := by
    have := r1.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  rw [le_div_iff₀ hbmin]
  nlinarith [mul_le_mul_of_nonneg_right hb0 hnn0, mul_le_mul_of_nonneg_right hb1 hnn1]

end SpanPressure

theorem block_bound_eventually_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + blkPress W.b (xret Z (mtParams T) T) B := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H (1 / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ 1 / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w' hn hm W hW hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : 1 < blkPress W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [lt_div_iff₀ hbmin] at this
      rw [div_mul_cancel₀ _ hbmin.ne'] at this
      exact this
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]

theorem pre_solve_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hmq : (1 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ W.B := WCert.B_nonneg hW

  set Cn : ℝ := (m : ℝ) + 3 + W.B * ((m : ℝ) - ((n : ℝ) - 1)) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w' Z H hn3 h2n W hW hbmin hb hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average_w hn W.b hW.b_nonneg (xret Z (mtParams T) T)
    (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    hA' (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hBeq : (∑ r, W.b r) = W.B := rfl
  rw [hBeq] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := W.B with hq
  set mq : ℝ := (m : ℝ) - ((n : ℝ) - 1) with hmqdef
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q mq η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have hmq0 : (0 : ℝ) ≤ mq := by linarith
  have step2 : q * mq * sp ≤ q * mq * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 hmq0)
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (AMW.HW - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + 3 + q * mq) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + 3 + q * mq) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * mq) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * AMW.HW - q * mq - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (AMW.HW - q * mq / m - ε) * N
      = ((m : ℝ) * AMW.HW - q * mq - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem n_point_bound_w' (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have h := solve_linear_w (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (AMW.HW - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn hm hA0
    (by
      have := pre_solve_w' zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/Fixed.lean ###### -/


noncomputable section
set_option linter.unusedSectionVars false

open Finset Filter
open scoped BigOperators
open Zeta23 Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge


end Zeta23Ext.BridgeW

end

/-! ###### AMW module: AMTail ###### -/

/-
AMW/AMTail.lean — the end state of the retargeted bridge: the seven-point weighted bound for the AMTOPA
window from a certificate hypothesis.

For any admissible weight certificate W : WCert 7 and c, m with `∀ g ≥ 0, c ≤ Fw W g` (Fw over
`wfun = AMW.wfunAM`), `n_point_bound_w'` gives (Phi_w' 7 c m B − ε)·N ≤ N0simple ≤ N0star, with
Phi_w' 7 c m B = (HW − B(m−6)/m)/(1 − c(m−6)/m); `Phi_w'_ge` reduces κ ≤ Phi_w' to a rational inequality
through `HW_ge : 6721883/10⁷ ≤ HW`.  `WAMT` is the certificate with AMTOPA's pair weights and per-gap
pressures (B = 93/23000).  Adapted from the submission layer of SolutionSevW10D.lean.
-/

noncomputable section

open Filter

namespace AMW

open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star' (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩

/-- `κ ≤ Phi_w' 7 c m B` from the floor of `HW`. -/
theorem Phi_w'_ge {c B κ : ℝ} {m : ℕ} (hm : 0 < m) (hD : c * ((m : ℝ) - 6) < m)
    (h : κ * (1 - c * ((m : ℝ) - 6) / m) ≤ 6721883 / 10 ^ 7 - B * ((m : ℝ) - 6) / m) :
    κ ≤ Phi_w' 7 c m B := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : 0 < 1 - c * ((m : ℝ) - 6) / m := by
    rw [sub_pos, div_lt_one hm']; exact hD
  unfold Phi_w'
  rw [show ((7 : ℕ) : ℝ) - 1 = 6 by norm_num, le_div_iff₀ hD']
  linarith [HW_ge]

/-- **The seven-point bound for the AMTOPA window**, from a certificate for `Fw W`. -/
theorem am_dyadic {W : WCert 7} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 14 ≤ m) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (hκ : κ ≤ Phi_w' 7 c m W.B)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w' 7 c m W (by norm_num) (by omega) hW hbmin hb hc hCert
    (by push_cast; linarith) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_w' 7 c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- The cumulative form. -/
theorem am_cumulative {W : WCert 7} (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 14 ≤ m) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (hκ : κ ≤ Phi_w' 7 c m W.B)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic hW hbmin hb hc hm hA0 hκ hCert)

/-! ### AMTOPA's pair weights and per-gap pressures -/

/-- the pair weights `a_ij` (zero unless `i < j`), over `10⁹` (AMTOPA_PAIRS). -/
def aAMT : Fin 7 → Fin 7 → ℝ :=
  ![![0, 244109993 / 10 ^ 9, 0, 254223074 / 10 ^ 9, 1, 1, 2],
    ![0, 0, 346264551 / 10 ^ 9, 368129744 / 10 ^ 9, 745776926 / 10 ^ 9, 0, 1],
    ![0, 0, 0, 409625456 / 10 ^ 9, 1263740512 / 10 ^ 9, 745776926 / 10 ^ 9, 1],
    ![0, 0, 0, 0, 409625456 / 10 ^ 9, 368129744 / 10 ^ 9, 254223074 / 10 ^ 9],
    ![0, 0, 0, 0, 0, 346264551 / 10 ^ 9, 0],
    ![0, 0, 0, 0, 0, 0, 244109993 / 10 ^ 9],
    ![0, 0, 0, 0, 0, 0, 0]]

/-- the per-gap pressures, over `46·10⁹` (AMTOPA_B). -/
def bAMT : Fin 6 → ℝ :=
  ![22420713 / 46000000000, 32878293 / 46000000000, 37700994 / 46000000000,
    37700994 / 46000000000, 32878293 / 46000000000, 22420713 / 46000000000]

def WAMT : WCert 7 := ⟨aAMT, bAMT⟩

theorem WAMT_B : WAMT.B = 93 / 23000 := by
  show (∑ r : Fin 6, bAMT r) = _
  simp [Fin.sum_univ_six, bAMT]; norm_num

theorem WAMT_bmin : ∀ r, (22420713 / 46000000000 : ℝ) ≤ WAMT.b r := by
  intro r
  show _ ≤ bAMT r
  fin_cases r <;> simp [bAMT] <;> norm_num

theorem WAMT_adm : WAMT.Adm where
  a_nonneg := by
    intro i j
    show 0 ≤ aAMT i j
    fin_cases i <;> fin_cases j <;> simp [aAMT] <;> norm_num
  b_nonneg := fun r => le_trans (by norm_num) (WAMT_bmin r)
  capacity := by
    intro s
    unfold WCert.spanMass
    show (∑ i : Fin 7, ∑ j : Fin 7, if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then aAMT i j else 0) ≤ 2
    rcases lt_or_ge s 7 with hs | hs
    · interval_cases s <;> simp [Fin.sum_univ_seven, aAMT] <;> norm_num
    · have h0 : ∀ i j : Fin 7, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
        intro i j ⟨_, h⟩
        have := j.2
        omega
      simp only [h0, if_false, Finset.sum_const_zero]
      norm_num

end AMW

end

/-! ###### tail: the n = 7 AM bound (AMTOPA weights `AMW.WAMT`, `AMW.am_dyadic`) ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW

/-- the certificate statement: `c ≤ Fw WAMT g` on the nonnegative orthant (`Fw` over `wfun = AMW.wfunAM`). -/
def CertHyp : Prop := ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → ((78927 : ℝ) / 10000000) ≤ Fw WAMT g

theorem kappa_le : candidateKappa ≤ Phi_w' 7 ((78927 : ℝ) / 10000000) 132 WAMT.B := by
  rw [WAMT_B]
  exact Phi_w'_ge (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)

theorem dyadic (hCert : CertHyp) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  exact am_dyadic WAMT_adm (by norm_num) WAMT_bmin (by norm_num) (m := 132) (by norm_num) (by norm_num)
    kappa_le hCert

theorem cumulative (hCert : CertHyp) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (dyadic hCert)

theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  norm_num

end RiemannFail

end

/-! ###### the three scored theorems ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound (hCert : RiemannFail.CertHyp) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic hCert

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative (hCert : RiemannFail.CertHyp) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative hCert

end

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative

example : currentRecordKappa = (6731631 : ℝ) / 10000000 := rfl
example : candidateKappa = (6734 : ℝ) / 10000 := rfl
