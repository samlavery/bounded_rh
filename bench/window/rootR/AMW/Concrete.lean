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
import AMW.ZeroSide
import Zeta23.ThmD.Concrete

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
