/-
AMW/LeverAM.lean — the generic minorant and basin tests (AMW/Minorant, AMW/PSDBasin) for the AMTOPA kernel.

`Fw W = Gk wfun n W.a W.b` (bridge `wfun = AMW.wfunAM`), and `wfunAM` is twice differentiable with
w′ = w1AM, w″ = w2AM (AMW/GSinc).  For a weight certificate whose weights are the casts of rational
tables, a passing leaf or basin test bounds `Fw W` below on its box.
-/
import AMW.PSDBasin
import AMW.GSinc
import AMW.BrC

noncomputable section

namespace AMW.Min

open Zeta23Ext.Bridge Zeta23Ext.BridgeW

theorem Fw_eq_Gk {n : ℕ} (W : WCert n) (g : Fin (n - 1) → ℝ) : Fw W g = Gk AMW.wfunAM n W.a W.b g := rfl

/-- a weight certificate given by rational tables. -/
def RatW {n : ℕ} (W : WCert n) (aQ : ℕ → ℕ → ℚ) (bQ : ℕ → ℚ) : Prop :=
  (∀ i j : Fin n, W.a i j = (aQ i j : ℝ)) ∧ ∀ r : Fin (n - 1), W.b r = (bQ r : ℝ)

theorem Fw_eq_Gk_rat {n : ℕ} {W : WCert n} {aQ : ℕ → ℕ → ℚ} {bQ : ℕ → ℚ} (hW : RatW W aQ bQ)
    (g : Fin (n - 1) → ℝ) :
    Fw W g = Gk AMW.wfunAM n (fun i j => (aQ i j : ℝ)) (fun r => (bQ r : ℝ)) g := by
  rw [Fw_eq_Gk]
  have ha : W.a = fun (i j : Fin n) => (aQ i j : ℝ) := funext fun i => funext fun j => hW.1 i j
  have hb : W.b = fun (r : Fin (n - 1)) => (bQ r : ℝ) := funext fun r => hW.2 r
  rw [ha, hb]

/-- **the minorant leaf test bounds `Fw` on its box.** -/
theorem minCheck_Fw {n : ℕ} {W : WCert n} {aQ : ℕ → ℕ → ℚ} {bQ : ℕ → ℚ} (hW : RatW W aQ bQ)
    {α β : ℕ → ℕ → ℚ} {lo hi : ℕ → ℚ} {C : ℚ} {lineOk : ℚ → ℚ → ℚ → ℚ → Bool}
    (hline : ∀ l h α β, lineOk l h α β = true → ∀ s : ℝ, (l : ℝ) ≤ s → s ≤ h →
      (α : ℝ) + β * s ≤ AMW.wfunAM s)
    (hc : minCheck n aQ α β bQ lo hi C lineOk = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) : (C : ℝ) ≤ Fw W g := by
  rw [Fw_eq_Gk_rat hW]
  exact minCheck_sound AMW.wfunAM hline hc g hg

/-- **the basin test bounds `Fw` on its box.** -/
theorem basinCheck_Fw {n : ℕ} {W : WCert n} {aQ : ℕ → ℕ → ℚ} {bQ : ℕ → ℚ} (hW : RatW W aQ bQ)
    {ℓ v u U : ℕ → ℕ → ℚ} {lo hi q : ℕ → ℚ} {C : ℚ}
    {w2Ok : ℚ → ℚ → ℚ → Bool} {valOk : ℚ → ℚ → Bool} {d1Ok : ℚ → ℚ → ℚ → Bool}
    {psd : (ℕ → ℕ → ℚ) → Bool}
    (hw2 : ∀ L H ℓ, w2Ok L H ℓ = true → ∀ x : ℝ, (L : ℝ) ≤ x → x ≤ H → (ℓ : ℝ) ≤ AMW.w2AM x)
    (hval : ∀ s v, valOk s v = true → (v : ℝ) ≤ AMW.wfunAM s)
    (hd1o : ∀ s u U, d1Ok s u U = true → (u : ℝ) ≤ AMW.w1AM s ∧ AMW.w1AM s ≤ U)
    (hpsdS : ∀ M : ℕ → ℕ → ℚ, psd M = true → SymmK (n - 1) (fun i j => (M i j : ℝ)) →
      ∀ d, 0 ≤ qf (n - 1) (fun i j => (M i j : ℝ)) d)
    (hc : basinCheck n aQ ℓ v u U bQ lo hi q C w2Ok valOk d1Ok psd = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) : (C : ℝ) ≤ Fw W g := by
  rw [Fw_eq_Gk_rat hW]
  exact basinCheck_sound AMW.hasDerivAt_wfunAM AMW.hasDerivAt_w1AM hw2 hval hd1o hpsdS hc g hg

/-- a line through (p, v) with slope β from value and one-sided derivative bounds of `wfunAM`. -/
theorem line_wfunAM {l p h v β : ℝ} (hv : v ≤ AMW.wfunAM p) (hL : ∀ x ∈ Set.Ioo l p, AMW.w1AM x ≤ β)
    (hR : ∀ x ∈ Set.Ioo p h, β ≤ AMW.w1AM x) : ∀ s ∈ Set.Icc l h, v + β * (s - p) ≤ AMW.wfunAM s :=
  line_of_deriv AMW.hasDerivAt_wfunAM hv hL hR

end AMW.Min

end
