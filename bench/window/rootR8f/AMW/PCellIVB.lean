import AMW.PCellIV

/-! ###### lever 1, leaner per-leaf test (am-cert, time lever T2)

As `PCellIV`, with "no interval" encoded as `a > b` instead of `b = 0`: `PVIB x v` claims the tangent only when
`ivA v ≤ ivB v`, so the per-leaf test `ivInB` is the chain `a ≤ L ≤ p ≤ U ≤ b` (four comparisons, no `1 ≤ b`).  A missing
lookup returns the sentinel word `SENT = 2^96` (empty triple, `a = 1 > b = 0`). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the missing-point word: empty triple, empty interval (`a = 1 > b = 0`) -/
def SENT : ℕ := 79228162514264337593543950336

def PVIB (x v : ℕ) : Prop := PV x (trip v) ∧ (ivA v ≤ ivB v → TVal (fun _ => trip v) (ivA v) (ivB v) x)

theorem pvib_sent (x : ℕ) : PVIB x SENT := by
  refine ⟨?_, fun h => absurd h (by decide)⟩
  show PV x (trip SENT); rw [show trip SENT = 0 from rfl]; exact pv_zero x

theorem ptf_tfB {g : ℕ → ℕ} (hg : ∀ x, PVIB x (g x)) : PTF (tf g) := fun x => (hg x).1

/-- the one-time interval check: empty (`b < a`), or the coarse-first tangent check on it -/
def ivOkB (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh x v : ℕ) : Bool :=
  Nat.blt (ivB v) (ivA v) || tcheckPZC R top bk tD bD n csh (ivA v) (ivB v) x (trip v) (treadUF R tD bD (ivB v) x)
    (treadDF R tD bD (ivA v) x)

theorem ivOkB_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh x v : ℕ} (hn : 0 < n)
    (hpv : PV x (trip v)) (h : ivOkB R top bk tD bD n csh x v = true) :
    ivA v ≤ ivB v → TVal (fun _ => trip v) (ivA v) (ivB v) x := by
  intro hab
  unfold ivOkB at h
  have hb' : Nat.blt (ivB v) (ivA v) = false := by
    cases hc : Nat.blt (ivB v) (ivA v)
    · rfl
    · exact absurd (Nat.blt_eq.mp hc) (by omega)
  rw [hb', Bool.false_or] at h
  rw [← fpt_self x (trip v)] at h
  have ht := tangent_valZC hlb hD (fpt_ptf hpv) hR hn h
  exact (TVal_congr (fpt_self x (trip v))).mp ht

/-- the per-leaf interval test: `a ≤ L ≤ p ≤ U ≤ b` -/
def ivInB (v L U p : ℕ) : Bool :=
  Nat.ble (ivA v) L && Nat.ble L p && Nat.ble p U && Nat.ble U (ivB v)

theorem tval_of_ivInB {g : ℕ → ℕ} (hg : ∀ x, PVIB x (g x)) {L U p : ℕ} (h : ivInB (g p) L U p = true) :
    TVal (tf g) L U p := by
  unfold ivInB at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨haL, hLp⟩, hpU⟩, hUb⟩ := h
  have hab : ivA (g p) ≤ ivB (g p) := by omega
  have ht := TVal_mono ((hg p).2 hab) haL hUb hLp hpU
  exact (TVal_congr (f := fun _ => trip (g p)) (f' := tf g) rfl).mp ht

def mokIB (g : ℕ → ℕ) (L U k m p r : ℕ) : Bool :=
  Nat.ble m 1024 && ((Nat.beq (mw1 k m) 0 || ivInB (g p) L U p) && (Nat.beq (mw2 k m) 0 || ivInB (g r) L U r))

end AMW.Cert.PCell

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

theorem mterm_okIB {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVIB x (g x))
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : ((Nat.beq (mw1 κ lam) 0 || ivInB (g p1) L U p1) && (Nat.beq (mw2 κ lam) 0 || ivInB (g p2) L U p2)) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl (tf g) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk (tf g) L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  have tv : ∀ (lk pk : ℕ), (lk = 0 ∨ ivInB (g pk) L U pk = true) → lk = 0 ∨ TVal (tf g) L U pk :=
    fun lk pk h => h.imp id (tval_of_ivInB hg)
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

theorem mtermTIB {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVIB x (g x))
    (L0 L U k m p r : ℕ) (hL0 : L0 ≤ L) (hok : mokIB g L U k m p r = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT (tf g) k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk (tf g) L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT (tf g) L0 k m p r : ℝ) - 10 * (mcnT (tf g) L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokIB at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okIB hlb hg L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1
    (by simp only [Bool.and_eq_true]; exact hok.2) s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

end AMW.Cert.PCell

end
