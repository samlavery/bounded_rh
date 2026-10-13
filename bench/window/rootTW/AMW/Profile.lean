/-
AMW/Profile.lean — a profile p on the unit window gives a positive-variation factor.

f_p(u) := √(p(u/L)) (Real.sqrt is 0 on negatives, so no guard is needed).  If p is even, C², positive on |s| ≤ 1/2 + δ, with 1/4 ≤ p ≤ 1, |p′| ≤ A₁,
|p″| ≤ A₂ on the core |s| ≤ 1/2, positive variation ∫₀^{1/2} max(p′,0) ≤ ρ and the budgets
√p(0) + 2ρ ≤ 1, p(0) + 4ρ ≤ 1, then f_p is a `PVFactor` with constants (A₁, A₂ + 2A₁², ρ):
h := p(·/L) = f_p² on the smooth region, f_p ≥ 1/2 on the core, f_p′ = h′/(2f_p) and
f_p″ = (h″ − 2f_p′²)/(2f_p); the positive variation of f_p is at most that of p since 2f_p ≥ 1.
Pattern of Zeta23/XiPrime/QuarticWindow/Quartic.lean (anthropics/zeta-23-lean, Apache-2.0).
-/
import AMW.Adm

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
