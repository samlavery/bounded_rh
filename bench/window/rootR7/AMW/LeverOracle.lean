/-
AMW/LeverOracle.lean — the table oracles of the minorant and basin tests, from the AM cell evaluator.

A cell [LN, UN]/SC (AMW/GCell, `CellA`) with `ok` encloses k = kfunAM (K0), k′ (K1, needs E2L > 0) and
k″ (K2, needs E2L, E3L > 0) at scale DZ (AMW/GCellSound).  Hence on the cell
    w = k² ≥ sqLo(K0),   w′ = 2kk′ ∈ 2·(K0 × K1),   w″ = 2(k′² + kk″) ≥ 2(sqLo(K1) + lo(K0 × K2)).
Intervals [A, B]/SC are covered by a chain of cells cut at the quarter-integers (so that each cell lies
on one side of its half-integer anchor) and every `st` grid units.  The oracles:
  `valOkA s v`     v ≤ w(s)                      (degenerate cell at s),
  `d1OkA s u U`    u ≤ w′(s) ≤ U                  (degenerate cell at s),
  `w2OkA st L H ℓ` ℓ ≤ w″ on [L, H]               (chain),
  `lineOkA st l h α β`  α + βs ≤ w(s) on [l, h]: the line through (l, w(l)) with β ≤ w′ on [l, h], or
                    through (h, w(h)) with w′ ≤ β on [l, h], or the constant α ≤ w on [l, h] (β = 0).
All arguments are rationals on the grid 1/SC.
-/
import AMW.LeverAM
import AMW.GCellSound

noncomputable section

open AMW.G

namespace AMW.Min

/-! ### rational ends of the cell intervals -/

def ivLo (I : IV) : ℚ := ((I.lo.p : ℚ) - I.lo.n) / (DZ : ℚ)
def ivHi (I : IV) : ℚ := ((I.hi.p : ℚ) - I.hi.n) / (DZ : ℚ)

theorem enc_q {I : IV} {a : ℝ} (h : I.Enc a) : ((ivLo I : ℚ) : ℝ) ≤ a ∧ a ≤ ((ivHi I : ℚ) : ℝ) := by
  unfold IV.Enc SZ.v at h
  unfold ivLo ivHi
  push_cast
  exact h

/-- lower bound of t² for t ∈ [lo, hi]. -/
def sqLo (lo hi : ℚ) : ℚ := if 0 ≤ lo then lo * lo else if hi ≤ 0 then hi * hi else 0

theorem sqLo_le {lo hi : ℚ} {t : ℝ} (h : (lo : ℝ) ≤ t ∧ t ≤ hi) : ((sqLo lo hi : ℚ) : ℝ) ≤ t ^ 2 := by
  unfold sqLo
  split_ifs with h1 h2
  · have : (0 : ℝ) ≤ lo := by exact_mod_cast h1
    push_cast; nlinarith [h.1]
  · have : (hi : ℝ) ≤ 0 := by exact_mod_cast h2
    push_cast; nlinarith [h.2]
  · push_cast; positivity

/-- upper end of a product of two intervals. -/
def imulHi (x1 x2 y1 y2 : ℚ) : ℚ := max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2))

theorem le_imulHi {x1 x2 y1 y2 : ℚ} {x y : ℝ} (hx : (x1 : ℝ) ≤ x ∧ x ≤ x2) (hy : (y1 : ℝ) ≤ y ∧ y ≤ y2) :
    x * y ≤ ((imulHi x1 x2 y1 y2 : ℚ) : ℝ) := by
  unfold imulHi
  push_cast
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  have hcol : ∀ c : ℝ, c * y ≤ max (c * y1) (c * y2) := fun c => by
    rcases le_total 0 c with hc | hc
    · exact (mul_le_mul_of_nonneg_left hy2 hc).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy1 hc).trans (le_max_left _ _)
  have hrow : x * y ≤ max ((x1 : ℝ) * y) (x2 * y) := by
    rcases le_total 0 y with hy0 | hy0
    · exact (mul_le_mul_of_nonneg_right hx2 hy0).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hx1 hy0).trans (le_max_left _ _)
  exact hrow.trans (max_le_max (hcol x1) (hcol x2))

/-! ### per-cell bounds -/

section cells
variable (c : CellA)

def cOk1 : Bool := c.ok && Nat.blt 0 c.E2L
def cOk2 : Bool := c.ok && Nat.blt 0 c.E2L && Nat.blt 0 c.E3L

/-- w = k² on the cell, below. -/
def cWLo : ℚ := sqLo (ivLo c.K0) (ivHi c.K0)
/-- w′ = 2kk′ on the cell. -/
def cW1Lo : ℚ := 2 * imulLo (ivLo c.K0) (ivHi c.K0) (ivLo c.K1) (ivHi c.K1)
def cW1Hi : ℚ := 2 * imulHi (ivLo c.K0) (ivHi c.K0) (ivLo c.K1) (ivHi c.K1)
/-- w″ = 2(k′² + kk″) on the cell, below. -/
def cW2Lo : ℚ := 2 * (sqLo (ivLo c.K1) (ivHi c.K1) + imulLo (ivLo c.K0) (ivHi c.K0) (ivLo c.K2) (ivHi c.K2))

theorem cWLo_sound (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    ((cWLo c : ℚ) : ℝ) ≤ AMW.wfunAM x :=
  sqLo_le (enc_q (c.K0_enc hc hx1 hx2))

theorem cW1_sound (hc : cOk1 c = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    ((cW1Lo c : ℚ) : ℝ) ≤ AMW.w1AM x ∧ AMW.w1AM x ≤ ((cW1Hi c : ℚ) : ℝ) := by
  simp only [cOk1, Bool.and_eq_true, Nat.blt_eq] at hc
  have h0 := enc_q (c.K0_enc hc.1 hx1 hx2)
  have h1 := enc_q (c.K1_enc hc.1 hc.2 hx1 hx2)
  have hl := imulLo_le h0 h1
  have hh := le_imulHi h0 h1
  unfold cW1Lo cW1Hi AMW.w1AM
  push_cast
  constructor <;> nlinarith

theorem cW2_sound (hc : cOk2 c = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    ((cW2Lo c : ℚ) : ℝ) ≤ AMW.w2AM x := by
  simp only [cOk2, Bool.and_eq_true, Nat.blt_eq] at hc
  have h0 := enc_q (c.K0_enc hc.1.1 hx1 hx2)
  have h1 := enc_q (c.K1_enc hc.1.1 hc.1.2 hx1 hx2)
  have h2 := enc_q (c.K2_enc hc.1.1 hc.1.2 hc.2 hx1 hx2)
  have hs := sqLo_le h1
  have hp := imulLo_le h0 h2
  unfold cW2Lo AMW.w2AM
  push_cast
  nlinarith

end cells

/-! ### chains of cells -/

/-- quarter-integers in grid units. -/
def QS : ℕ := 8192

/-- the next cut after A: the next quarter-integer, at most A + st, at most B. -/
def nextCut (st A B : ℕ) : ℕ := min B (min (A + st) ((A / QS + 1) * QS))

/-- every cell of the chain from A to B satisfies P. -/
def chainAll (P : CellA → Bool) (st : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, A, B =>
    if B ≤ A then P ⟨A, A⟩
    else P ⟨A, nextCut st A B⟩ && (nextCut st A B == B || chainAll P st fuel (nextCut st A B) B)

theorem nextCut_gt {st A B : ℕ} (hst : 0 < st) (hAB : A < B) : A < nextCut st A B := by
  unfold nextCut
  have h1 : A < (A / QS + 1) * QS := by
    have := Nat.lt_div_mul_add (a := A) (b := QS) (by norm_num [QS]); unfold QS at *; nlinarith
  omega

theorem nextCut_le {st A B : ℕ} : nextCut st A B ≤ B := by unfold nextCut; omega

theorem chainAll_sound {P : CellA → Bool} {st : ℕ} (hst : 0 < st) :
    ∀ (fuel A B : ℕ), chainAll P st fuel A B = true → A ≤ B →
      ∀ x : ℝ, (A : ℝ) / SC ≤ x → x ≤ (B : ℝ) / SC →
        ∃ c : CellA, P c = true ∧ (c.LN : ℝ) / SC ≤ x ∧ x ≤ (c.UN : ℝ) / SC := by
  intro fuel
  induction fuel with
  | zero => intro A B h; simp [chainAll] at h
  | succ fuel ih =>
    intro A B h hAB x hx1 hx2
    simp only [chainAll] at h
    split_ifs at h with hBA
    · exact ⟨⟨A, A⟩, h, hx1, by
        have : (B : ℝ) ≤ A := by exact_mod_cast hBA
        simp only; linarith [div_le_div_of_nonneg_right this (by norm_num [SC] : (0:ℝ) ≤ SC)]⟩
    · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hP, hrest⟩ := h
      set C := nextCut st A B with hC
      rcases le_or_gt x ((C : ℝ) / SC) with hxC | hxC
      · exact ⟨⟨A, C⟩, hP, hx1, hxC⟩
      · rcases hrest with hCB | hrec
        · exact ⟨⟨A, C⟩, hP, hx1, by rw [hCB]; exact hx2⟩
        · exact ih C B hrec nextCut_le x hxC.le hx2

/-! ### the grid -/

/-- a rational on the grid 1/SC, nonnegative. -/
def onGrid (s : ℚ) : Bool := (s * (SC : ℚ)).den == 1 && decide (0 ≤ s)
def toGrid (s : ℚ) : ℕ := (s * (SC : ℚ)).num.toNat

theorem toGrid_eq {s : ℚ} (h : onGrid s = true) : ((toGrid s : ℕ) : ℝ) / SC = s := by
  simp only [onGrid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hd, hs⟩ := h
  have hSC : (0 : ℚ) < SC := by norm_num [SC]
  have hnn : 0 ≤ (s * SC).num := Rat.num_nonneg.mpr (mul_nonneg hs hSC.le)
  have e : ((toGrid s : ℕ) : ℚ) = s * SC := by
    unfold toGrid
    rw [show ((s * (SC : ℚ)).num.toNat : ℚ) = ((s * SC).num : ℚ) by
      exact_mod_cast Int.toNat_of_nonneg hnn]
    exact (Rat.coe_int_num_of_den_eq_one hd)
  have e' : ((toGrid s : ℕ) : ℝ) = (s : ℝ) * SC := by exact_mod_cast e
  have hS : (SC : ℝ) ≠ 0 := by norm_num [SC]
  rw [e']; field_simp

/-! ### the oracles -/

def valOkA (s v : ℚ) : Bool :=
  onGrid s && (⟨toGrid s, toGrid s⟩ : CellA).ok && decide (v ≤ cWLo ⟨toGrid s, toGrid s⟩)

def d1OkA (s u U : ℚ) : Bool :=
  onGrid s && cOk1 ⟨toGrid s, toGrid s⟩
    && decide (u ≤ cW1Lo ⟨toGrid s, toGrid s⟩) && decide (cW1Hi ⟨toGrid s, toGrid s⟩ ≤ U)

/-- a chain check over [l, h] (grid rationals). -/
def chainQ (P : CellA → Bool) (st : ℕ) (l h : ℚ) : Bool :=
  onGrid l && onGrid h && decide (l ≤ h) && decide (0 < st)
    && chainAll P st (toGrid h - toGrid l + 2) (toGrid l) (toGrid h)

theorem chainQ_sound {P : CellA → Bool} {st : ℕ} {l h : ℚ} (hc : chainQ P st l h = true) :
    ∀ x : ℝ, (l : ℝ) ≤ x → x ≤ h → ∃ c : CellA, P c = true ∧ (c.LN : ℝ) / SC ≤ x ∧ x ≤ (c.UN : ℝ) / SC := by
  simp only [chainQ, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hl, hh⟩, hlh⟩, hst⟩, hch⟩ := hc
  intro x hx1 hx2
  have hAB : toGrid l ≤ toGrid h := by
    have e1 := toGrid_eq hl; have e2 := toGrid_eq hh
    have : ((toGrid l : ℕ) : ℝ) / SC ≤ ((toGrid h : ℕ) : ℝ) / SC := by
      rw [e1, e2]; exact_mod_cast hlh
    rw [div_le_div_iff_of_pos_right (by norm_num [SC])] at this
    exact_mod_cast this
  exact chainAll_sound hst _ _ _ hch hAB x (by rw [toGrid_eq hl]; exact hx1) (by rw [toGrid_eq hh]; exact hx2)

def w2OkA (st : ℕ) (L H ℓ : ℚ) : Bool := chainQ (fun c => cOk2 c && decide (ℓ ≤ cW2Lo c)) st L H

def lineOkA (st : ℕ) (l h α β : ℚ) : Bool :=
  (valOkA l (α + β * l) && chainQ (fun c => cOk1 c && decide (β ≤ cW1Lo c)) st l h)
  || (valOkA h (α + β * h) && chainQ (fun c => cOk1 c && decide (cW1Hi c ≤ β)) st l h)
  || (decide (β = 0) && chainQ (fun c => c.ok && decide (α ≤ cWLo c)) st l h)

/-! ### soundness of the oracles -/

theorem valOkA_sound (s v : ℚ) (h : valOkA s v = true) : (v : ℝ) ≤ AMW.wfunAM s := by
  simp only [valOkA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hg, hok⟩, hv⟩ := h
  have e := toGrid_eq hg
  have := cWLo_sound _ hok (x := s) (by simp only; rw [e]) (by simp only; rw [e])
  exact (Rat.cast_le.mpr hv).trans this

theorem d1OkA_sound (s u U : ℚ) (h : d1OkA s u U = true) :
    (u : ℝ) ≤ AMW.w1AM s ∧ AMW.w1AM s ≤ U := by
  simp only [d1OkA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hok⟩, hu⟩, hU⟩ := h
  have e := toGrid_eq hg
  have := cW1_sound _ hok (x := s) (by simp only; rw [e]) (by simp only; rw [e])
  exact ⟨(Rat.cast_le.mpr hu).trans this.1, this.2.trans (Rat.cast_le.mpr hU)⟩

theorem w2OkA_sound (st : ℕ) (L H ℓ : ℚ) (h : w2OkA st L H ℓ = true) :
    ∀ x : ℝ, (L : ℝ) ≤ x → x ≤ H → (ℓ : ℝ) ≤ AMW.w2AM x := by
  intro x hx1 hx2
  obtain ⟨c, hP, hc1, hc2⟩ := chainQ_sound h x hx1 hx2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  exact (Rat.cast_le.mpr hP.2).trans (cW2_sound c hP.1 hc1 hc2)

theorem lineOkA_sound (st : ℕ) (l h α β : ℚ) (hl : lineOkA st l h α β = true) :
    ∀ s : ℝ, (l : ℝ) ≤ s → s ≤ h → (α : ℝ) + β * s ≤ AMW.wfunAM s := by
  simp only [lineOkA, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
  intro s hs1 hs2
  rcases hl with (⟨hv, hch⟩ | ⟨hv, hch⟩) | ⟨hβ, hch⟩
  · -- the line through (l, w(l)), slope β ≤ w′ on [l, h]
    have hv' := valOkA_sound _ _ hv
    have hline := line_wfunAM (l := l) (p := l) (h := h) (v := ((α + β * l : ℚ) : ℝ)) (β := β) hv'
      (fun x hx => absurd hx.2 (not_lt.mpr hx.1.le))
      (fun x hx => by
        obtain ⟨c, hP, hc1, hc2⟩ := chainQ_sound hch x hx.1.le hx.2.le
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        exact (Rat.cast_le.mpr hP.2).trans (cW1_sound c hP.1 hc1 hc2).1) s ⟨hs1, hs2⟩
    push_cast at hline; linarith
  · -- the line through (h, w(h)), slope β ≥ w′ on [l, h]
    have hv' := valOkA_sound _ _ hv
    have hline := line_wfunAM (l := l) (p := h) (h := h) (v := ((α + β * h : ℚ) : ℝ)) (β := β) hv'
      (fun x hx => by
        obtain ⟨c, hP, hc1, hc2⟩ := chainQ_sound hch x hx.1.le hx.2.le
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        exact (cW1_sound c hP.1 hc1 hc2).2.trans (Rat.cast_le.mpr hP.2))
      (fun x hx => absurd hx.2 (not_lt.mpr hx.1.le)) s ⟨hs1, hs2⟩
    push_cast at hline; linarith
  · -- the constant line
    obtain ⟨c, hP, hc1, hc2⟩ := chainQ_sound hch s hs1 hs2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    rw [hβ]; push_cast; rw [zero_mul, add_zero]
    exact (Rat.cast_le.mpr hP.2).trans (cWLo_sound c hP.1 hc1 hc2)

/-! ### the AMTOPA leaf and basin tests with the table oracles -/

open Zeta23Ext.BridgeW in
/-- **a passing minorant leaf bounds `Fw W` on its box** (lines certified by the AM cell tables). -/
theorem minCheckA_Fw {n : ℕ} {W : WCert n} {aQ : ℕ → ℕ → ℚ} {bQ : ℕ → ℚ} (hW : RatW W aQ bQ)
    (st : ℕ) {α β : ℕ → ℕ → ℚ} {lo hi : ℕ → ℚ} {C : ℚ}
    (hc : minCheck n aQ α β bQ lo hi C (lineOkA st) = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) : (C : ℝ) ≤ Fw W g :=
  minCheck_Fw hW (lineOkA_sound st) hc g hg

open Zeta23Ext.BridgeW in
/-- **a passing basin bounds `Fw W` on its box** (w″, w, w′ bounds from the AM cell tables). -/
theorem basinCheckA_Fw {n : ℕ} {W : WCert n} {aQ : ℕ → ℕ → ℚ} {bQ : ℕ → ℚ} (hW : RatW W aQ bQ)
    (st : ℕ) {ℓ v u U : ℕ → ℕ → ℚ} {lo hi q : ℕ → ℚ} {C : ℚ} {psd : (ℕ → ℕ → ℚ) → Bool}
    (hpsdS : ∀ M : ℕ → ℕ → ℚ, psd M = true → SymmK (n - 1) (fun i j => (M i j : ℝ)) →
      ∀ d, 0 ≤ qf (n - 1) (fun i j => (M i j : ℝ)) d)
    (hc : basinCheck n aQ ℓ v u U bQ lo hi q C (w2OkA st) valOkA d1OkA psd = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) : (C : ℝ) ≤ Fw W g :=
  basinCheck_Fw hW (w2OkA_sound st) valOkA_sound d1OkA_sound hpsdS hc g hg

end AMW.Min

end
