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
import Zeta23.ThmD.WindowCore
import Zeta23.Taper.Norms

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
