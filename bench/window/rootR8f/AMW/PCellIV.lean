import AMW.PCDZ
import AMW.PCellCloseB

/-! ###### precertified tangent intervals (am-cert, lever 1)

A tangent's value-form claim `TVal f L U p` depends on the range `[L, U]` only through `L ≤ p ≤ U` and the
inequality on `[L/SC, U/SC]`, so it passes to every subrange that still contains `p` (`TVal_mono`).  Each point word of
the table carries, above its 96 triple bits, one interval `[a, b]` (`a + 2^24·b`, `b = 0`: none) on which the tangent
claim is checked ONCE, with the same coarse-first check as before (`ivOk`, `ptlI_sound`).  A minorant leaf then needs,
per tangent point, only `a ≤ L ≤ p ≤ U ≤ b` (`ivIn`, `mokI`, `mtermTI`) in place of `mokTZC`'s per-leaf derivative
reads and Z extension.  Every triple decoder reads the word through `trip` (the low 96 bits). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the triple (low 96 bits) of a point word -/
def trip (v : ℕ) : ℕ := Nat.land v 79228162514264337593543950335
/-- the interval's lower end (bits 96–119) -/
def ivA (v : ℕ) : ℕ := Nat.land (Nat.shiftRight v 96) 16777215
/-- the interval's upper end (bits 120–); `0` means no interval -/
def ivB (v : ℕ) : ℕ := Nat.shiftRight v 120
/-- the point function the decoders see -/
def tf (g : ℕ → ℕ) (x : ℕ) : ℕ := trip (g x)

theorem trip_zero : trip 0 = 0 := rfl
theorem ivB_zero : ivB 0 = 0 := rfl

/-- `TVal` reads `f` only at `p` -/
theorem TVal_congr {f f' : ℕ → ℕ} {L U p : ℕ} (h : f p = f' p) : TVal f L U p ↔ TVal f' L U p := by
  unfold TVal; rw [h]

/-- **monotonicity**: a tangent valid on `[a, b]` is valid on every `[L, U] ⊆ [a, b]` that contains `p` -/
theorem TVal_mono {f : ℕ → ℕ} {a b L U p : ℕ} (h : TVal f a b p) (haL : a ≤ L) (hUb : U ≤ b) (hLp : L ≤ p)
    (hpU : p ≤ U) : TVal f L U p := by
  obtain ⟨-, -, h1, h2, h3⟩ := h
  refine ⟨hLp, hpU, h1, h2, fun s hs1 hs2 => h3 s ?_ ?_⟩
  · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast haL) SC_pos.le) hs1
  · exact le_trans hs2 (div_le_div_of_nonneg_right (by exact_mod_cast hUb) SC_pos.le)

/-- the pointwise soundness of a point word: the triple's claims, and the interval's tangent claim -/
def PVI (x v : ℕ) : Prop := PV x (trip v) ∧ (ivB v ≠ 0 → TVal (fun _ => trip v) (ivA v) (ivB v) x)

theorem pvi_zero (x : ℕ) : PVI x 0 := by
  refine ⟨?_, fun h => absurd ivB_zero h⟩
  rw [trip_zero]; exact pv_zero x
theorem pvi_dsel {x j m a b : ℕ} (ha : PVI x a) (hb : PVI x b) : PVI x (dsel j m a b) := by
  unfold dsel; cases Nat.ble m j <;> assumption
theorem pvi_dpk {x j k v : ℕ} (hv : PVI x v) : PVI x (dpk j k v) := by
  unfold dpk; cases Nat.beq j k
  · exact pvi_zero x
  · exact hv

/-- the point function `tf g` is a sound triple table -/
theorem ptf_tf {g : ℕ → ℕ} (hg : ∀ x, PVI x (g x)) : PTF (tf g) := fun x => (hg x).1

/-- a point function equal to `w` at `p` and `0` elsewhere -/
def fpt (p w y : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 w (Nat.beq y p)
theorem fpt_self (p w : ℕ) : fpt p w p = w := by simp [fpt]
theorem fpt_ptf {p w : ℕ} (h : PV p w) : PTF (fpt p w) := by
  intro y
  unfold fpt
  cases hb : Nat.beq y p
  · exact pv_zero y
  · have hy : y = p := by simpa using hb
    subst hy; exact h

/-- the one-time check of a point word's interval: none, or the coarse-first tangent check on it -/
def ivOk (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh x v : ℕ) : Bool :=
  Nat.beq (ivB v) 0 || tcheckPZC R top bk tD bD n csh (ivA v) (ivB v) x (trip v) (treadUF R tD bD (ivB v) x)
    (treadDF R tD bD (ivA v) x)

theorem ivOk_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh x v : ℕ} (hn : 0 < n)
    (hpv : PV x (trip v)) (h : ivOk R top bk tD bD n csh x v = true) :
    ivB v ≠ 0 → TVal (fun _ => trip v) (ivA v) (ivB v) x := by
  intro hb
  unfold ivOk at h
  have hb' : Nat.beq (ivB v) 0 = false := by
    cases hc : Nat.beq (ivB v) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) hb
  rw [hb', Bool.false_or] at h
  rw [← fpt_self x (trip v)] at h
  have ht := tangent_valZC hlb hD (fpt_ptf hpv) hR hn h
  exact (TVal_congr (fpt_self x (trip v))).mp ht

/-- the block check: every entry's triple (through `trip`) and its interval -/
def ptlOkI (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh : ℕ)
    (L : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => pt3e e.1 (trip e.2) && ivOk R top bk tD bD n csh e.1 e.2 && ih) L

theorem ptlI_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) :
    ∀ (L : List (ℕ × ℕ)), ptlOkI R top bk tD bD n csh L = true → ∀ x, PVI x (ptl L x) := by
  intro L
  induction L with
  | nil => intro _ x; exact pvi_zero x
  | cons e r ih =>
    intro h x
    have h' : (pt3e e.1 (trip e.2) && ivOk R top bk tD bD n csh e.1 e.2 && ptlOkI R top bk tD bD n csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨he, hiv⟩, hr⟩ := h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptl r x) e.2 (Nat.beq e.1 x))
    cases hb : Nat.beq e.1 x
    · exact ih hr x
    · have hx : e.1 = x := by simpa using hb
      simp only [pt3e, Bool.and_eq_true] at he
      have hpv : PV e.1 (trip e.2) := ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩
      rw [← hx]
      exact ⟨hpv, ivOk_sound hlb hD hR hn hpv hiv⟩

/-- the per-leaf interval test of one tangent point `p` on the range `[L, U]` -/
def ivIn (v L U p : ℕ) : Bool :=
  Nat.ble 1 (ivB v) && Nat.ble (ivA v) L && Nat.ble L p && Nat.ble p U && Nat.ble U (ivB v)

theorem tval_of_ivIn {g : ℕ → ℕ} (hg : ∀ x, PVI x (g x)) {L U p : ℕ} (h : ivIn (g p) L U p = true) :
    TVal (tf g) L U p := by
  unfold ivIn at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨h1, haL⟩, hLp⟩, hpU⟩, hUb⟩ := h
  have hb : ivB (g p) ≠ 0 := by omega
  have ht := TVal_mono ((hg p).2 hb) haL hUb hLp hpU
  exact (TVal_congr (f := fun _ => trip (g p)) (f' := tf g) rfl).mp ht

/-- a term's side conditions by precertified intervals (in place of `mokTZC`) -/
def mokI (g : ℕ → ℕ) (L U k m p r : ℕ) : Bool :=
  Nat.ble m 1024 && ((Nat.beq (mw1 k m) 0 || ivIn (g p) L U p) && (Nat.beq (mw2 k m) 0 || ivIn (g r) L U r))

end AMW.Cert.PCell

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- `mterm_okZC` with the tangents' validity from precertified intervals -/
theorem mterm_okI {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVI x (g x))
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : ((Nat.beq (mw1 κ lam) 0 || ivIn (g p1) L U p1) && (Nat.beq (mw2 κ lam) 0 || ivIn (g p2) L U p2)) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl (tf g) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk (tf g) L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  have tv : ∀ (lk pk : ℕ), (lk = 0 ∨ ivIn (g pk) L U pk = true) → lk = 0 ∨ TVal (tf g) L U pk :=
    fun lk pk h => h.imp id (tval_of_ivIn hg)
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_minV hlb L0 L U Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 hL0 hUc
    (mw_sum κ lam hl) (tv _ _ h1) (tv _ _ h2) s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal (tf g) L U pk) →
      (lk : ℝ) * (((hi32 (hi32 (tf g pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (tf g pk)) : ℕ) : ℝ))
        * ((pk - L0 : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (tf g pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (hL0.trans h.1)]
  have e1 := pk _ _ (tv _ _ h1)
  have e2 := pk _ _ (tv _ _ h2)
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

end AMW.Cert.PyrD

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- `mtermTZC` with `mokI`: the per-term bound `mcheckGX_sound` consumes -/
theorem mtermTI {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVI x (g x))
    (L0 L U k m p r : ℕ) (hL0 : L0 ≤ L) (hok : mokI g L U k m p r = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT (tf g) k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk (tf g) L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT (tf g) L0 k m p r : ℝ) - 10 * (mcnT (tf g) L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokI at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okI hlb hg L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1
    (by simp only [Bool.and_eq_true]; exact hok.2) s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

end AMW.Cert.PCell

end
