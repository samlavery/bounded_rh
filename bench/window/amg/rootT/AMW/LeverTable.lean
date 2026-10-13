/-
AMW/LeverTable.lean — lines below the AM pair kernel from the engine's verified tables.

On a pair range [L, H]/SC (grid units), from the w pyramid (`LBSound`), the w′ pair pyramid (`LBSoundD`: lower
bounds of w′ + 2 and 2 − w′) and the point triples (`PT3Sound`):
  constant  w(s) ≥ lb(L, H)/10¹⁰,
  left      w(s) ≥ v_L + (lo32(lbDr L H)/U1 − 2)(s − L/SC)   (the least slope on [L, H]),
  right     w(s) ≥ v_H + (2 − hi32(lbDr L H)/U1)(s − H/SC)   (the greatest slope on [L, H]),
with v_L ≤ w(L/SC), v_H ≤ w(H/SC) from the point table (`lo32 (pt3 pb x)/10¹⁰`).
-/
import AMW.Minorant
import AMW.GSinc
import AMW.CEngine

noncomputable section

namespace AMW.Min

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

theorem wfun_eq (x : ℝ) : AMW.Cert.wfun x = AMW.wfunAM x := rfl
theorem w1_eq (x : ℝ) : AMW.Cert.w1 x = AMW.w1AM x := rfl

/-- the point value from the table. -/
theorem ptValue_sound {pb : ℕ → ℕ} (hpt : PT3Sound pb) (x : ℕ) :
    (lo32 (pt3 pb x) : ℝ) / 10000000000 ≤ AMW.wfunAM ((x : ℝ) / SC) :=
  (hpt x).1

/-- the constant line from the pyramid. -/
theorem constLine_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (L H : ℕ) :
    ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (H : ℝ) / SC → (lb top bk L H : ℝ) / 10000000000 ≤ AMW.wfunAM s :=
  fun s h1 h2 => hlb L H s h1 h2

/-- the least slope on [L, H] from the derivative pair read. -/
theorem slopeLo_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {L H : ℕ}
    (hne : lo32 (lbDr tD bD L H) ≠ 0) :
    ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (H : ℝ) / SC → (lo32 (lbDr tD bD L H) : ℝ) / U1 - 2 ≤ AMW.w1AM x := by
  intro x h1 h2
  have h := (hD L H x h1 h2).1 hne
  have e : fD true x = AMW.w1AM x + 2 := by simp [fD, w1_eq]
  rw [e] at h
  linarith [h.2]

/-- the greatest slope on [L, H] from the derivative pair read. -/
theorem slopeHi_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {L H : ℕ}
    (hne : hi32 (lbDr tD bD L H) ≠ 0) :
    ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (H : ℝ) / SC → AMW.w1AM x ≤ 2 - (hi32 (lbDr tD bD L H) : ℝ) / U1 := by
  intro x h1 h2
  have h := (hD L H x h1 h2).2 hne
  have e : fD false x = 2 - AMW.w1AM x := by simp [fD, w1_eq]
  rw [e] at h
  linarith [h.2]

/-- **the left line**: through (L/SC, v) with the least slope on [L, H]. -/
theorem leftLine_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {L H : ℕ}
    (hne : lo32 (lbDr tD bD L H) ≠ 0) {v : ℝ} (hv : v ≤ AMW.wfunAM ((L : ℝ) / SC)) :
    ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (H : ℝ) / SC →
      v + ((lo32 (lbDr tD bD L H) : ℝ) / U1 - 2) * (s - (L : ℝ) / SC) ≤ AMW.wfunAM s := by
  intro s h1 h2
  exact line_of_deriv AMW.hasDerivAt_wfunAM hv (fun x hx => absurd hx.2 (not_lt.mpr hx.1.le))
    (fun x hx => slopeLo_sound hD hne x hx.1.le hx.2.le) s ⟨h1, h2⟩

/-- **the right line**: through (H/SC, v) with the greatest slope on [L, H]. -/
theorem rightLine_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {L H : ℕ}
    (hne : hi32 (lbDr tD bD L H) ≠ 0) {v : ℝ} (hv : v ≤ AMW.wfunAM ((H : ℝ) / SC)) :
    ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (H : ℝ) / SC →
      v + (2 - (hi32 (lbDr tD bD L H) : ℝ) / U1) * (s - (H : ℝ) / SC) ≤ AMW.wfunAM s := by
  intro s h1 h2
  exact line_of_deriv AMW.hasDerivAt_wfunAM hv
    (fun x hx => slopeHi_sound hD hne x hx.1.le hx.2.le) (fun x hx => absurd hx.2 (not_lt.mpr hx.1.le))
    s ⟨h1, h2⟩

end AMW.Min

end
