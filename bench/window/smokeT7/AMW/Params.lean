/-
AMW/Params.lean — the window-realizing parameter family for an arbitrary window family.

Ported from anthropics/zeta-23-lean (Apache-2.0, Copyright (c) 2026 Anthropic, PBC),
Zeta23/ThmD/ParamsD.lean and Zeta23/XiPrime/QuarticWindow/Params.lean, generic in the window: for a
family W : ℝ → (ℝ → ℝ) (height T ↦ window), `atW P W T := ⟨x ↦ W T (L/2 − w·x), λ, w⟩`.  Its λ, w
— hence L, X, λ₁, d, τ_k, h, 𝓔_T, toSetting — are P's by rfl, and its window AT HEIGHT T is W T
whenever W T is even (`atW_phi`), so its local data and prime-side traces are the AdmWindow data
of W T.
-/
import Zeta23.ThmD.ZeroSideD

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
