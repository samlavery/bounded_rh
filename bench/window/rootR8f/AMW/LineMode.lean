/-
AMW/LineMode.lean — per-term lines for the slope test of the seven-point engine (the minorant lever).

The slope test bounds each pair term by `SC·val + SC·U·d·(s − q) − (U/U1)·charge ≤ SC·U·w(s)` with `d` inside the
term's slope claims `[P/U1 − 2, 2 − M/U1]`, all read from a packed triple `X` (value, P, M).  Besides zero order
(mode 0) and the tangent at the shared expansion point with its charge (mode 1), a term may now use its own line:
  mode 2 (left)   through (L, w(L)) with the least certified slope on [L, U]: D = lo32(lbDr L U), slope D/U1 − 2;
  mode 3 (right)  through (U, w(U)) with the greatest certified slope:        D = hi32(lbDr L U), slope 2 − D/U1;
(any mode ≥ 2 other than 3 reads as left).  The line is re-expressed at the term's expansion point QS as the triple
(value at QS, P, M) with P − 2U1 = 2U1 − M = U1·slope: its slope interval is one point and it carries no charge, so the
engine's per-term inequality and the generated leaf check are unchanged; only the per-term reads change (`lmX`,
`lmCv`, by mode).  An uncertified line, or one whose value at QS would be negative, gives the triple 0, which fails the
check `1 ≤ P`.  Soundness: `lterm_bound`, with the conclusion of `rterm_boundc`, for every mode.
-/
import AMW.LeverTable

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-! ### the line triples -/

/-- a lower bound of `w` at the grid point `x` (units `10⁻¹⁰`): the point function, else the pyramid read at `x`. -/
def lmV (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  forceR (lo32 (f x)) fun a => Bool.rec (motive := fun _ => ℕ) (lb top bk x x) a (Nat.ble 1 a)

/-- the triple `(v, P, M)` packed as the point table packs it, the value capped below `2³²`. -/
def lmPk (v P M : ℕ) : ℕ :=
  Nat.add (Nat.min v 4294967295) (Nat.shiftLeft (Nat.add P (Nat.shiftLeft M 32)) 32)

/-- the value `v` raised by `⌊a/SC⌋`, packed with the slope claims `P`, `M`. -/
def lmUp (v a P M : ℕ) : ℕ := lmPk (Nat.add v (Nat.div a 32768)) P M

/-- the value `v` lowered by `⌊a/SC⌋ + 1`, packed with the slope claims `P`, `M`; `0` if that would be negative. -/
def lmDn (v a P M : ℕ) : ℕ :=
  forceR (Nat.add (Nat.div a 32768) 1) fun c => Bool.rec (motive := fun _ => ℕ) 0 (lmPk (Nat.sub v c) P M) (Nat.ble c v)

/-- the left line at `QS`: anchor `L`, slope `D/U1 − 2`, `D = lo32 (lbDr L U)`; `0` when not certified. -/
def lmL (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  forceR (lo32 (lbDr tD bD L U)) fun D =>
  forceR (lmV top bk f L) fun v =>
  Bool.rec (motive := fun _ => ℕ) 0
    (Bool.rec (motive := fun _ => ℕ)
      (lmDn v (Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub 2000000000 D))) D (Nat.sub 4000000000 D))
      (lmUp v (Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub D 2000000000))) D (Nat.sub 4000000000 D))
      (Nat.ble 2000000000 D))
    (Nat.ble 1 D && Nat.blt D 4000000000)

/-- the right line at `QS`: anchor `U`, slope `2 − D/U1`, `D = hi32 (lbDr L U)`; `0` when not certified. -/
def lmR (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  forceR (hi32 (lbDr tD bD L U)) fun D =>
  forceR (lmV top bk f U) fun v =>
  Bool.rec (motive := fun _ => ℕ) 0
    (Bool.rec (motive := fun _ => ℕ)
      (lmDn v (Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub 2000000000 D))) (Nat.sub 4000000000 D) D)
      (lmUp v (Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub D 2000000000))) (Nat.sub 4000000000 D) D)
      (Nat.ble 2000000000 D))
    (Nat.ble 1 D && Nat.blt D 4000000000)

/-- the mean value term at `QS`: the point value with the derivative pair of the whole range `[L, U]` as slope claims. -/
def lmM (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  forceR (lbDr tD bD L U) fun D2 => lmPk (lmV top bk f QS) (lo32 D2) (hi32 D2)

/-! ### the per-term reads by mode (0 zero order, 1 tangent with charge, 2 left line, 3 right line, 4 mean value) -/

/-- the expansion bit of a mode -/
def lmBit (m : ℕ) : Bool := Nat.ble 1 m
/-- the no-charge flag of a mode: a line always, the tangent when its range is convex (`c`) -/
def lmCv (m : ℕ) (c : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false c (Nat.beq m 1)) true (Nat.ble 2 m)
/-- the packed read of a mode -/
def lmX (m : ℕ) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (selXf (lmBit m) top bk f L U QS)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (lmL top bk f tD bD L U QS) (lmR top bk f tD bD L U QS) (Nat.beq m 3))
      (lmM top bk f tD bD L U QS) (Nat.ble 4 m))
    (Nat.ble 2 m)
/-- the mode of a term from its expansion bit `b` and the 2-bit field `t` of `E` (`0` tangent, `1` left line,
`2` right line, `3` mean value) -/
def mdOf (b : Bool) (E t : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add 1 (Nat.land (Nat.shiftRight E (Nat.mul 2 t)) 3)) b

theorem lmBit_md (b : Bool) (E t : ℕ) : lmBit (mdOf b E t) = b := by
  cases b
  · rfl
  · show Nat.ble 1 (Nat.add 1 _) = true
    rw [Nat.ble_eq]; exact Nat.le_add_right 1 _

/-! ### soundness -/

theorem lmV_sound {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk) (hpt : PTF f) (x : ℕ) :
    (lmV top bk f x : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) := by
  unfold lmV
  simp only [forceR_eq]
  cases Nat.ble 1 (lo32 (f x))
  · exact hlb x x _ le_rfl le_rfl
  · exact (hpt x).1

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem lmPk_eq (v P M : ℕ) : lmPk v P M = Nat.min v 4294967295 + (P + M * 2 ^ 32) * 2 ^ 32 := by
  show Nat.min v 4294967295 + (P + M <<< 32) <<< 32 = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]

theorem lmPk_min (v : ℕ) : Nat.min v 4294967295 < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.min_le_right v 4294967295) (by norm_num)

theorem lmPk_lo (v P M : ℕ) : lo32 (lmPk v P M) ≤ v := by
  rw [lmPk_eq, lo32_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lmPk_min v)]
  exact Nat.min_le_left v 4294967295

theorem lmPk_hi (v P M : ℕ) : hi32 (lmPk v P M) = P + M * 2 ^ 32 := by
  rw [lmPk_eq, hi32_eq, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lmPk_min v), Nat.zero_add]

theorem lmPk_P {v P M : ℕ} (hP : P < 2 ^ 32) : lo32 (hi32 (lmPk v P M)) = P := by
  rw [lmPk_hi, lo32_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hP]

theorem lmPk_M {v P M : ℕ} (hP : P < 2 ^ 32) : hi32 (hi32 (lmPk v P M)) = M := by
  rw [lmPk_hi, hi32_eq, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt hP, Nat.zero_add]

theorem lmUp_val (v a P M : ℕ) :
    ∃ val : ℕ, lmUp v a P M = lmPk val P M ∧ 32768 * (val : ℝ) ≤ 32768 * (v : ℝ) + a := by
  refine ⟨Nat.add v (Nat.div a 32768), rfl, ?_⟩
  have h : 32768 * (a / 32768) ≤ a := Nat.mul_div_le a 32768
  have h' : (32768 : ℝ) * ((a / 32768 : ℕ) : ℝ) ≤ a := by exact_mod_cast h
  simp only [Nat.add_eq, nat_div_eq]
  push_cast
  linarith

theorem lmDn_val (v a P M : ℕ) :
    lmDn v a P M = 0 ∨ ∃ val : ℕ, lmDn v a P M = lmPk val P M ∧ 32768 * (val : ℝ) + a ≤ 32768 * (v : ℝ) := by
  unfold lmDn
  simp only [forceR_eq]
  by_cases h : Nat.ble (Nat.add (Nat.div a 32768) 1) v = true
  · right
    rw [h]
    refine ⟨Nat.sub v (Nat.add (Nat.div a 32768) 1), rfl, ?_⟩
    rw [Nat.ble_eq] at h
    simp only [Nat.add_eq, nat_div_eq, Nat.sub_eq] at h ⊢
    have hlt : a < 32768 * (a / 32768 + 1) := by
      have := Nat.lt_div_mul_add (a := a) (b := 32768) (by norm_num)
      linarith
    have hlt' : (a : ℝ) < 32768 * (((a / 32768 + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [Nat.cast_sub h]
    linarith
  · left
    rw [Bool.not_eq_true] at h
    rw [h]

theorem tP_t (X : ℕ) : tP true X = lo32 (hi32 X) := rfl
theorem tM_t (X : ℕ) : tM true X = hi32 (hi32 X) := rfl
theorem tK_t : tK true = 2000000000 := rfl
theorem tval_t (X : ℕ) : tval true X = lo32 X := rfl
theorem mchg_tt (L U QS X EU ED : ℕ) : mchg true true L U QS X EU ED = 0 := rfl

/-- what a packed triple `(val, P, M)` must certify on `[L, U]`: at every point a slope `d` inside the claims with
`SC·val + SC·U·d·(s − QS/SC) ≤ SC·U·w(s)` (once the claims are nonzero, as the check requires). -/
def PkOK (L U QS val P M : ℕ) : Prop :=
  1 ≤ P → 1 ≤ M → ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC → ∃ d : ℝ,
    (P : ℝ) - 2000000000 ≤ 1000000000 * d ∧ 1000000000 * d ≤ 2000000000 - (M : ℝ) ∧
    32768 * (val : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768)) ≤ 327680000000000 * wfun s

/-- a certified packed triple gives the engine's per-term inequality (no charge). -/
theorem pk_term {X L U QS EU ED : ℕ}
    (hX : X = 0 ∨ ∃ val P M : ℕ, X = lmPk val P M ∧ P < 2 ^ 32 ∧ PkOK L U QS val P M)
    (hok : (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP true X : ℝ) - (tK true : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK true : ℝ) - (tM true X : ℝ) ∧
      32768 * (tval true X : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg true true L U QS X EU ED : ℝ) ≤ 327680000000000 * wfun s := by
  rw [tP_t, tK_t, tM_t, tval_t, mchg_tt]
  rcases hX with hX | ⟨val, P, M, hX, hP, hpk⟩
  · rw [hX] at hok; simp only [hi32_zero, lo32_zero] at hok; exact absurd hok (by decide)
  · rw [hX] at hok ⊢
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    rw [lmPk_P hP, lmPk_M hP] at hok ⊢
    obtain ⟨d, hd1, hd2, hline⟩ := hpk hok.1 hok.2 s hs1 hs2
    refine ⟨d, ?_, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
    · have h1 : (lo32 (lmPk val P M) : ℝ) ≤ val := by exact_mod_cast lmPk_lo val P M
      push_cast
      linarith

/-- the mean value form: `w(s) = w(q) + d·(s − q)` with `d` inside any enclosure of `w′` on `[a, b]`. -/
theorem mvt_slope {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {a b lo hi : ℝ}
    (hb : ∀ x, a ≤ x → x ≤ b → lo ≤ f' x ∧ f' x ≤ hi) {q s : ℝ} (hq1 : a ≤ q) (hq2 : q ≤ b)
    (hs1 : a ≤ s) (hs2 : s ≤ b) : ∃ d, lo ≤ d ∧ d ≤ hi ∧ f s = f q + d * (s - q) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  rcases lt_trichotomy s q with h | h | h
  · obtain ⟨c, hc1, hcd⟩ := exists_hasDerivAt_eq_slope f f' h hc.continuousOn (fun x _ => hf x)
    have hcb := hb c (by linarith [hc1.1]) (by linarith [hc1.2])
    refine ⟨f' c, hcb.1, hcb.2, ?_⟩
    have hne : q - s ≠ 0 := sub_ne_zero.mpr h.ne'
    rw [hcd]; field_simp; ring
  · subst h; exact ⟨f' s, (hb s hs1 hs2).1, (hb s hs1 hs2).2, by ring⟩
  · obtain ⟨c, hc1, hcd⟩ := exists_hasDerivAt_eq_slope f f' h hc.continuousOn (fun x _ => hf x)
    have hcb := hb c (by linarith [hc1.1]) (by linarith [hc1.2])
    refine ⟨f' c, hcb.1, hcb.2, ?_⟩
    have hne : s - q ≠ 0 := sub_ne_zero.mpr h.ne'
    rw [hcd]; field_simp; ring

/-- **the mean value term**: the point value at `QS` with the derivative enclosure on the whole range `[L, U]`. -/
theorem lmM_spec {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U) :
    ∃ val P M : ℕ, lmM top bk f tD bD L U QS = lmPk val P M ∧ P < 2 ^ 32 ∧ PkOK L U QS val P M := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  refine ⟨lmV top bk f QS, lo32 (lbDr tD bD L U), hi32 (lbDr tD bD L U), by unfold lmM; rw [forceR_eq], ?_, ?_⟩
  · rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  intro hP hM s hs1 hs2
  have hv := lmV_sound hlb hpt QS
  have hlo := AMW.Min.slopeLo_sound hD (by omega : lo32 (lbDr tD bD L U) ≠ 0)
  have hhi := AMW.Min.slopeHi_sound hD (by omega : hi32 (lbDr tD bD L U) ≠ 0)
  have hq1 : (L : ℝ) / SC ≤ (QS : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hLQ) (by positivity)
  have hq2 : (QS : ℝ) / SC ≤ (U : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hQU) (by positivity)
  obtain ⟨d, hd1, hd2, hds⟩ := mvt_slope AMW.hasDerivAt_wfunAM (fun x h1 h2 => ⟨hlo x h1 h2, hhi x h1 h2⟩)
    hq1 hq2 hs1 hs2
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [hU1] at hd1
    have := mul_le_mul_of_nonneg_left hd1 (by norm_num : (0 : ℝ) ≤ 1000000000)
    rw [mul_sub, mul_div_cancel₀ _ (by norm_num)] at this
    linarith
  · rw [hU1] at hd2
    have := mul_le_mul_of_nonneg_left hd2 (by norm_num : (0 : ℝ) ≤ 1000000000)
    rw [mul_sub, mul_div_cancel₀ _ (by norm_num)] at this
    linarith
  · have hw : wfun s = wfun ((QS : ℝ) / SC) + d * (s - (QS : ℝ) / SC) := hds
    rw [hw, hSC]
    rw [hSC] at hv
    have e : (327680000000000 : ℝ) * (d * (s - (QS : ℝ) / 32768))
        = 327680000000000 * (d * (s - (QS : ℝ) / 32768)) := rfl
    nlinarith [hv]

theorem lmL_spec {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (L U QS : ℕ) (hLQ : L ≤ QS) :
    lmL top bk f tD bD L U QS = 0 ∨ ∃ val P M : ℕ, lmL top bk f tD bD L U QS = lmPk val P M ∧ P < 2 ^ 32 ∧
      PkOK L U QS val P M := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hv := lmV_sound hlb hpt L
  have hline := fun hne : lo32 (lbDr tD bD L U) ≠ 0 => AMW.Min.leftLine_sound hD hne hv
  unfold lmL
  simp only [forceR_eq]
  generalize lo32 (lbDr tD bD L U) = D at hline ⊢
  generalize lmV top bk f L = v at hline ⊢
  by_cases h1 : (Nat.ble 1 D && Nat.blt D 4000000000) = true
  · rw [h1]
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
    obtain ⟨hD1, hD4⟩ := h1
    have hP : D < 2 ^ 32 := by norm_num; omega
    have hl := hline (by omega)
    have hM : ((Nat.sub 4000000000 D : ℕ) : ℝ) = 4000000000 - (D : ℝ) := by
      rw [Nat.sub_eq, Nat.cast_sub (by omega)]; push_cast; ring
    have hLQr : ((Nat.sub QS L : ℕ) : ℝ) = (QS : ℝ) - L := by rw [Nat.sub_eq, Nat.cast_sub hLQ]
    have hd1 : (D : ℝ) - 2000000000 = 1000000000 * ((D : ℝ) / U1 - 2) := by rw [hU1]; field_simp; ring
    have hd2 : 1000000000 * ((D : ℝ) / U1 - 2) = 2000000000 - ((Nat.sub 4000000000 D : ℕ) : ℝ) := by
      rw [hM, hU1]; field_simp; ring
    have key : ∀ s : ℝ, 327680000000000 * (((D : ℝ) / U1 - 2) * (s - (QS : ℝ) / 32768))
        = 327680000000000 * (((D : ℝ) / U1 - 2) * (s - (L : ℝ) / 32768))
          - 10 * ((D : ℝ) - 2000000000) * ((QS : ℝ) - L) := by
      intro s; rw [hU1]; ring
    have hl' : ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
        (v : ℝ) / 10000000000 + ((D : ℝ) / U1 - 2) * (s - (L : ℝ) / 32768) ≤ wfun s := by
      intro s hs1 hs2; have h := hl s hs1 hs2; rw [hSC] at h; exact h
    by_cases h2 : Nat.ble 2000000000 D = true
    · rw [h2]
      rw [Nat.ble_eq] at h2
      right
      obtain ⟨val, hval, hle⟩ := lmUp_val v (Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub D 2000000000))) D
        (Nat.sub 4000000000 D)
      refine ⟨val, D, _, hval, hP, fun _ _ s hs1 hs2 => ⟨(D : ℝ) / U1 - 2, hd1.le, hd2.le, ?_⟩⟩
      have h := hl' s hs1 hs2
      have ea : ((Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub D 2000000000)) : ℕ) : ℝ)
          = 10 * ((D : ℝ) - 2000000000) * ((QS : ℝ) - L) := by
        simp only [Nat.mul_eq]; push_cast; rw [hLQr, Nat.sub_eq, Nat.cast_sub h2]; push_cast; ring
      rw [ea] at hle
      rw [key s]
      linarith
    · have h2f : Nat.ble 2000000000 D = false := Bool.eq_false_iff.mpr h2
      rw [h2f]
      rw [Nat.ble_eq] at h2
      rcases lmDn_val v (Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub 2000000000 D))) D (Nat.sub 4000000000 D) with
        h0 | ⟨val, hval, hle⟩
      · left; exact h0
      · right
        refine ⟨val, D, _, hval, hP, fun _ _ s hs1 hs2 => ⟨(D : ℝ) / U1 - 2, hd1.le, hd2.le, ?_⟩⟩
        have h := hl' s hs1 hs2
        have ea : ((Nat.mul 10 (Nat.mul (Nat.sub QS L) (Nat.sub 2000000000 D)) : ℕ) : ℝ)
            = 10 * (2000000000 - (D : ℝ)) * ((QS : ℝ) - L) := by
          simp only [Nat.mul_eq]; push_cast; rw [hLQr, Nat.sub_eq, Nat.cast_sub (by omega)]; push_cast; ring
        rw [ea] at hle
        rw [key s]
        linarith
  · left
    rw [Bool.not_eq_true] at h1
    rw [h1]

theorem lmR_spec {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (L U QS : ℕ) (hQU : QS ≤ U) :
    lmR top bk f tD bD L U QS = 0 ∨ ∃ val P M : ℕ, lmR top bk f tD bD L U QS = lmPk val P M ∧ P < 2 ^ 32 ∧
      PkOK L U QS val P M := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hv := lmV_sound hlb hpt U
  have hline := fun hne : hi32 (lbDr tD bD L U) ≠ 0 => AMW.Min.rightLine_sound hD hne hv
  unfold lmR
  simp only [forceR_eq]
  generalize hi32 (lbDr tD bD L U) = D at hline ⊢
  generalize lmV top bk f U = v at hline ⊢
  by_cases h1 : (Nat.ble 1 D && Nat.blt D 4000000000) = true
  · rw [h1]
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
    obtain ⟨hD1, hD4⟩ := h1
    have hP : Nat.sub 4000000000 D < 2 ^ 32 := by simp only [Nat.sub_eq]; norm_num; omega
    have hl := hline (by omega)
    have hM : ((Nat.sub 4000000000 D : ℕ) : ℝ) = 4000000000 - (D : ℝ) := by
      rw [Nat.sub_eq, Nat.cast_sub (by omega)]; push_cast; ring
    have hUQr : ((Nat.sub U QS : ℕ) : ℝ) = (U : ℝ) - QS := by rw [Nat.sub_eq, Nat.cast_sub hQU]
    have hd1 : ((Nat.sub 4000000000 D : ℕ) : ℝ) - 2000000000 = 1000000000 * (2 - (D : ℝ) / U1) := by
      rw [hM, hU1]; field_simp; ring
    have hd2 : 1000000000 * (2 - (D : ℝ) / U1) = 2000000000 - (D : ℝ) := by rw [hU1]; field_simp; ring
    have key : ∀ s : ℝ, 327680000000000 * ((2 - (D : ℝ) / U1) * (s - (QS : ℝ) / 32768))
        = 327680000000000 * ((2 - (D : ℝ) / U1) * (s - (U : ℝ) / 32768))
          + 10 * (2000000000 - (D : ℝ)) * ((U : ℝ) - QS) := by
      intro s; rw [hU1]; ring
    have hl' : ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
        (v : ℝ) / 10000000000 + (2 - (D : ℝ) / U1) * (s - (U : ℝ) / 32768) ≤ wfun s := by
      intro s hs1 hs2; have h := hl s hs1 hs2; rw [hSC] at h; exact h
    by_cases h2 : Nat.ble 2000000000 D = true
    · rw [h2]
      rw [Nat.ble_eq] at h2
      right
      obtain ⟨val, hval, hle⟩ := lmUp_val v (Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub D 2000000000)))
        (Nat.sub 4000000000 D) D
      refine ⟨val, _, D, hval, hP, fun _ _ s hs1 hs2 => ⟨2 - (D : ℝ) / U1, hd1.le, hd2.le, ?_⟩⟩
      have h := hl' s hs1 hs2
      have ea : ((Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub D 2000000000)) : ℕ) : ℝ)
          = 10 * ((D : ℝ) - 2000000000) * ((U : ℝ) - QS) := by
        simp only [Nat.mul_eq]; push_cast; rw [hUQr, Nat.sub_eq, Nat.cast_sub h2]; push_cast; ring
      rw [ea] at hle
      rw [key s]
      linarith
    · have h2f : Nat.ble 2000000000 D = false := Bool.eq_false_iff.mpr h2
      rw [h2f]
      rw [Nat.ble_eq] at h2
      rcases lmDn_val v (Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub 2000000000 D))) (Nat.sub 4000000000 D) D with
        h0 | ⟨val, hval, hle⟩
      · left; exact h0
      · right
        refine ⟨val, _, D, hval, hP, fun _ _ s hs1 hs2 => ⟨2 - (D : ℝ) / U1, hd1.le, hd2.le, ?_⟩⟩
        have h := hl' s hs1 hs2
        have ea : ((Nat.mul 10 (Nat.mul (Nat.sub U QS) (Nat.sub 2000000000 D)) : ℕ) : ℝ)
            = 10 * (2000000000 - (D : ℝ)) * ((U : ℝ) - QS) := by
          simp only [Nat.mul_eq]; push_cast; rw [hUQr, Nat.sub_eq, Nat.cast_sub (by omega)]; push_cast; ring
        rw [ea] at hle
        rw [key s]
        linarith
  · left
    rw [Bool.not_eq_true] at h1
    rw [h1]

/-- **one pair term of the slope test in mode `m`**: zero order (0), the tangent at `QS` charged or convex (1), or a
line through an end of the range (2 left, 3 right; no charge, no derivative reads beyond the line's one read).  The
conclusion is that of `rterm_boundc`, so a generated leaf test uses it term by term. -/
theorem lterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (m : ℕ) (bit : Bool) (hb : lmBit m = bit) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : rtok (lmCv m (inRg R L U)) bit L U QS (lmX m top bk f tD bD L U QS)
      (selUv (lmCv m (inRg R L U)) bit tD bD QS U) (selDv (lmCv m (inRg R L U)) bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (lmX m top bk f tD bD L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (lmX m top bk f tD bD L U QS) : ℝ) ∧
      32768 * (tval bit (lmX m top bk f tD bD L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg (lmCv m (inRg R L U)) bit L U QS (lmX m top bk f tD bD L U QS)
          (selUv (lmCv m (inRg R L U)) bit tD bD QS U) (selDv (lmCv m (inRg R L U)) bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  subst hb
  rcases m with _ | _ | m
  · exact rterm_boundc hlb hD hpt false L U QS false (fun h => absurd h (by decide)) hLQ hQU hok s hs1 hs2
  · exact rterm_boundc hlb hD hpt true L U QS (inRg R L U) (fun h => inRg_sound hR h) hLQ hQU hok s hs1 hs2
  · have hX : lmX (m + 2) top bk f tD bD L U QS
        = Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (lmL top bk f tD bD L U QS) (lmR top bk f tD bD L U QS)
            (Nat.beq (m + 2) 3))
          (lmM top bk f tD bD L U QS) (Nat.ble 4 (m + 2)) := rfl
    have hspec : lmX (m + 2) top bk f tD bD L U QS = 0 ∨ ∃ val P M : ℕ,
        lmX (m + 2) top bk f tD bD L U QS = lmPk val P M ∧ P < 2 ^ 32 ∧ PkOK L U QS val P M := by
      rw [hX]
      cases Nat.ble 4 (m + 2)
      · cases Nat.beq (m + 2) 3
        · exact lmL_spec hlb hD hpt L U QS hLQ
        · exact lmR_spec hlb hD hpt L U QS hQU
      · exact Or.inr (lmM_spec hlb hD hpt L U QS hLQ hQU)
    exact pk_term hspec hok s hs1 hs2

end AMW.Cert.PyrD

end
