import Mathlib

/-! Experiment (stage B of SCOPE.md): the `l1_deriv ≤ 2` field of `AdmWindow` for a NON-monotone window.
Zeta23 proves `‖φ'‖₁ ≤ 2` from antitonicity on `[0, ∞)` (`ThmD/Window.lean`, private
`integral_abs_deriv_le_two`; `XiPrime/QuarticWindow/ModWindow.lean`, `integral_abs_deriv_le_two`).
Replacement: an even C¹ function supported in `[-M, M]` whose positive variation on `[0, M]` is at most
`ρ`, with `f 0 + 2ρ ≤ 1`, has `∫ |f'| ≤ 2`.  The proof is the same FTC argument with
`|x| = 2·max x 0 - x` in place of `|x| = -x`. -/

open MeasureTheory Set

theorem integral_abs_deriv_le_two_of_posVar {f : ℝ → ℝ} {M ρ : ℝ} (hM : 0 < M)
    (hf : ContDiff ℝ 1 f) (heven : ∀ x, f (-x) = f x)
    (hsupp : ∀ x, M ≤ |x| → f x = 0)
    (hpos : ∫ u in (0:ℝ)..M, max (deriv f u) 0 ≤ ρ) (hbud : f 0 + 2 * ρ ≤ 1) :
    ∫ u, |deriv f u| ≤ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hderiv0 : ∀ x : ℝ, M < |x| → deriv f x = 0 := by
    intro x hx
    have hopen : IsOpen {v : ℝ | M < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hEq : f =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds hx] with v hv
      exact hsupp v (le_of_lt hv)
    rw [hEq.deriv_eq, deriv_const]
  have hodd : ∀ x : ℝ, |deriv f (-x)| = |deriv f x| := by
    intro x
    have hfe : (fun y : ℝ => f (-y)) = f := funext heven
    have h := deriv_comp_neg (f := f) (x := x)
    rw [hfe] at h
    have h' : deriv f (-x) = -deriv f x := by linarith
    rw [h', abs_neg]
  have habs : (fun u : ℝ => |deriv f u|) = fun u => (fun t => |deriv f t|) |u| := by
    funext u
    show |deriv f u| = |deriv f (|u|)|
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hodd]
  have hhalf : ∫ u, |deriv f u| = 2 * ∫ u in Set.Ioi 0, |deriv f u| := by
    conv_lhs => rw [habs]
    exact integral_comp_abs (f := fun t => |deriv f t|)
  have hcs : HasCompactSupport (deriv f) := by
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
  have hint : Integrable (fun u => |deriv f u|) := (hd'.integrable_of_hasCompactSupport hcs).abs
  have hsplit : ∫ u in Set.Ioi 0, |deriv f u|
      = (∫ u in Set.Ioc 0 M, |deriv f u|) + ∫ u in Set.Ioi M, |deriv f u| := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hM.le]
  have hfar : ∫ u in Set.Ioi M, |deriv f u| = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hderiv0 x (by rw [abs_of_pos (lt_trans hM hx)]; exact hx), abs_zero]
  -- the new step: |f'| = 2·max f' 0 − f', then FTC
  have hpt : ∀ x : ℝ, |deriv f x| = 2 * max (deriv f x) 0 - deriv f x := by
    intro x
    rcases le_or_gt 0 (deriv f x) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have hmaxc : Continuous fun x => max (deriv f x) 0 := hd'.max continuous_const
  have hFTC : ∫ u in (0:ℝ)..M, deriv f u = f M - f 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) ((hd'.intervalIntegrable) 0 M)
  have hnear : ∫ u in Set.Ioc 0 M, |deriv f u|
      = 2 * (∫ u in (0:ℝ)..M, max (deriv f u) 0) - (f M - f 0) := by
    rw [← intervalIntegral.integral_of_le hM.le]
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub ((hmaxc.intervalIntegrable 0 M).const_mul 2)
        (hd'.intervalIntegrable 0 M), intervalIntegral.integral_const_mul, hFTC]
  have hfM : f M = 0 := hsupp M (by rw [abs_of_pos hM])
  rw [hhalf, hsplit, hfar, hnear, hfM]
  linarith

/-- the product step: on `(0, M)`, a window `φ = f·τ` with `f ≥ 0` and `τ` nonincreasing in `[0, 1]`
has positive part of `φ'` at most that of `f'`. -/
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

#print axioms integral_abs_deriv_le_two_of_posVar
#print axioms max_deriv_mul_le
