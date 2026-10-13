import AMW.GCell
import AMW.GTaylor
-- engine speed-ups by typh (riemannzeta-fun dc788ef, seven-point-optimised-window, Apache-2.0); for this window his GCell is exact


/-!
# AMW/GBase — soundness of the trigonometric base of a cell (stage G)

For `c.ok = true` and `x ∈ [LN, UN] / SC`: the endpoints are exact (`DZ / SC = 5¹⁵`), the offset `r = |x − k/2|`
satisfies `TLZ ≤ π r · DZ ≤ TUZ ≤ DZ`, the Taylor enclosures give `cos (π r)`, `sin (π r)`, the anchor `k/2` gives
`cos (πx)`, `sin (πx)`, and `πx`, `E = 2(πx)² − 1` are enclosed.
-/

noncomputable section

open Real

namespace AMW.G

theorem DZ_eq : DZ = SC * 30517578125 := by norm_num [DZ, SC]

theorem pi_lo20 : ((PLN : ℕ) : ℝ) / E20 ≤ π := by
  have h := Real.pi_gt_d20; norm_num [PLN, E20] at h ⊢; linarith
theorem pi_hi20 : π ≤ ((PUN : ℕ) : ℝ) / E20 := by
  have h := Real.pi_lt_d20; norm_num [PUN, E20] at h ⊢; linarith

theorem ERRD_ge : terr ≤ (ERRD : ℝ) / DZ := by norm_num [terr, ERRD, DZ]

namespace CellA
variable (c : CellA)

theorem div_cancel_aux (u s q : ℕ) (hs : 0 < s) : u * (s * q) / s = u * q := by
  rw [show u * (s * q) = u * q * s by ring]; exact Nat.mul_div_cancel _ hs

theorem divc_cancel_aux (u s q : ℕ) (hs : 0 < s) : (u * (s * q) + s - 1) / s = u * q := by
  have h1 : u * (s * q) + s - 1 = (s - 1) + u * q * s := by
    have : 1 ≤ s := hs
    rw [show u * (s * q) = u * q * s by ring]; omega
  rw [h1, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem LLO_eq : c.LLO = c.LN * 30517578125 := by
  unfold LLO; rw [show Nat.mul c.LN DZ = c.LN * DZ from rfl, DZ_eq]
  exact div_cancel_aux _ _ _ (by norm_num [SC])

theorem UHI_eq : c.UHI = c.UN * 30517578125 := by
  unfold UHI ndivc; rw [show Nat.mul c.UN DZ = c.UN * DZ from rfl, DZ_eq]
  exact divc_cancel_aux _ _ _ (by norm_num [SC])

theorem LLO_div : (c.LLO : ℝ) / DZ = (c.LN : ℝ) / SC := by
  rw [LLO_eq]; push_cast; rw [DZ_eq]; push_cast; field_simp

theorem UHI_div : (c.UHI : ℝ) / DZ = (c.UN : ℝ) / SC := by
  rw [UHI_eq]; push_cast; rw [DZ_eq]; push_cast; field_simp

theorem AD_div : (c.AD : ℝ) / DZ = (c.k : ℝ) / 2 := by
  unfold AD; simp only [Nat.mul_eq]; push_cast; norm_num [DZ2, DZ]; ring

/-- the offset from the anchor `k/2` -/
def roff (x : ℝ) : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x

theorem cosP_sub_cosN {T : ℕ} (hT : T ≤ DZ) : cosN T ≤ cosP T := by
  unfold cosP cosN DZp
  simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
  have h2 : T ^ 2 ≤ DZ ^ 2 := Nat.pow_le_pow_left hT 2
  have h6 : T ^ 6 ≤ DZ ^ 6 := Nat.pow_le_pow_left hT 6
  have h10 : T ^ 10 ≤ DZ ^ 10 := Nat.pow_le_pow_left hT 10
  have a1 : 1814400 * T ^ 2 * DZ ^ 8 ≤ 1814400 * DZ ^ 10 := by
    calc 1814400 * T ^ 2 * DZ ^ 8 ≤ 1814400 * DZ ^ 2 * DZ ^ 8 := by gcongr
      _ = 1814400 * DZ ^ 10 := by ring
  have a2 : 5040 * T ^ 6 * DZ ^ 4 ≤ 5040 * DZ ^ 10 := by
    calc 5040 * T ^ 6 * DZ ^ 4 ≤ 5040 * DZ ^ 6 * DZ ^ 4 := by gcongr
      _ = 5040 * DZ ^ 10 := by ring
  have : 0 ≤ 151200 * T ^ 4 * DZ ^ 6 + 90 * T ^ 8 * DZ ^ 2 := Nat.zero_le _
  omega

theorem sinP_sub_sinN {T : ℕ} (hT : T ≤ DZ) : sinN T ≤ sinP T := by
  unfold sinP sinN DZp
  simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
  have a1 : 6652800 * T ^ 3 * DZ ^ 8 ≤ 6652800 * T * DZ ^ 10 := by
    calc 6652800 * T ^ 3 * DZ ^ 8 = 6652800 * T * (T ^ 2 * DZ ^ 8) := by ring
      _ ≤ 6652800 * T * (DZ ^ 2 * DZ ^ 8) := by gcongr
      _ = 6652800 * T * DZ ^ 10 := by ring
  have a2 : 7920 * T ^ 7 * DZ ^ 4 ≤ 7920 * T * DZ ^ 10 := by
    calc 7920 * T ^ 7 * DZ ^ 4 = 7920 * T * (T ^ 6 * DZ ^ 4) := by ring
      _ ≤ 7920 * T * (DZ ^ 6 * DZ ^ 4) := by gcongr
      _ = 7920 * T * DZ ^ 10 := by ring
  have a3 : T ^ 11 ≤ T * DZ ^ 10 := by
    calc T ^ 11 = T * T ^ 10 := by ring
      _ ≤ T * DZ ^ 10 := by gcongr
  have : 0 ≤ 332640 * T ^ 5 * DZ ^ 6 + 110 * T ^ 9 * DZ ^ 2 := Nat.zero_le _
  nlinarith

theorem tcos_eq (T : ℕ) (h : cosN T ≤ cosP T) :
    tcos ((T : ℝ) / DZ) = ((Nat.sub (cosP T) (cosN T) : ℕ) : ℝ) / CDEN / DZ := by
  rw [show Nat.sub (cosP T) (cosN T) = cosP T - cosN T from rfl, Nat.cast_sub h]
  unfold tcos cosP cosN CDEN DZp
  simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
  push_cast
  have hD : (DZ : ℝ) ≠ 0 := by norm_num [DZ]
  field_simp
  ring

theorem tsin_eq (T : ℕ) (h : sinN T ≤ sinP T) :
    tsin ((T : ℝ) / DZ) = ((Nat.sub (sinP T) (sinN T) : ℕ) : ℝ) / SDEN / DZ := by
  rw [show Nat.sub (sinP T) (sinN T) = sinP T - sinN T from rfl, Nat.cast_sub h]
  unfold tsin sinP sinN SDEN DZp
  simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
  push_cast
  have hD : (DZ : ℝ) ≠ 0 := by norm_num [DZ]
  field_simp
  ring

theorem cos_le_cos01 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : Real.cos b ≤ Real.cos a :=
  Real.cos_le_cos_of_nonneg_of_le_pi ha (hb.trans (by linarith [Real.pi_gt_three])) hab

theorem sin_le_sin01 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : Real.sin a ≤ Real.sin b :=
  Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (hb.trans (by linarith [Real.pi_gt_three])) hab

theorem abs_le_one_of {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1

/-- the base enclosures of a checked cell -/
structure Base (x : ℝ) : Prop where
  xlo : (c.LLO : ℝ) / DZ ≤ x
  xhi : x ≤ (c.UHI : ℝ) / DZ
  cx : c.CX.Enc (Real.cos (π * x))
  sx : c.SX.Enc (Real.sin (π * x))
  blo : (c.BLZ : ℝ) / DZ ≤ π * x
  bhi : π * x ≤ (c.BUZ : ℝ) / DZ
  e0 : 0 < c.E0
  elo : (c.E0 : ℝ) / DZ ≤ 2 * (π * x) ^ 2 - 1
  ehi : 2 * (π * x) ^ 2 - 1 ≤ (c.E1 : ℝ) / DZ
  r0 : 0 ≤ c.roff x
  tlo : (c.TLZ : ℝ) / DZ ≤ π * c.roff x
  thi : π * c.roff x ≤ (c.TUZ : ℝ) / DZ
  t1 : (c.TUZ : ℝ) / DZ ≤ 1

end CellA

theorem cos_sin_half (k : ℕ) :
    (Real.cos (π * ((k : ℝ) / 2)) = if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0) ∧
    (Real.sin (π * ((k : ℝ) / 2)) = if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0) := by
  have hk : (k : ℝ) = 4 * ((k / 4 : ℕ) : ℝ) + ((k % 4 : ℕ) : ℝ) := by
    have := Nat.div_add_mod k 4; exact_mod_cast this.symm
  have e : π * ((k : ℝ) / 2) = π * (((k % 4 : ℕ) : ℝ) / 2) + ((k / 4 : ℕ) : ℝ) * (2 * π) := by rw [hk]; ring
  rw [e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  have hm : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> simp <;> norm_num
  all_goals first
    | (rw [show π * (3 / 2) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp)
    | (rw [show π * (3 / 2) = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two])
    | (rw [show π * (1 / 2) = π / 2 by ring]; simp)
    | skip


namespace CellA
variable (c : CellA)

theorem beq_val (m n : ℕ) : Nat.beq m n = decide (m = n) := by
  cases h : Nat.beq m n
  · have := Nat.ne_of_beq_eq_false h; simp [this]
  · have := Nat.eq_of_beq_eq_true h; simp [this]

theorem CX_val : c.CX = if c.km4 = 0 then c.CI else if c.km4 = 1 then (if c.side then c.SI.neg else c.SI)
    else if c.km4 = 2 then c.CI.neg else (if c.side then c.SI else c.SI.neg) := by
  unfold CX; simp only [beq_val]
  by_cases h0 : c.km4 = 0 <;> by_cases h1 : c.km4 = 1 <;> by_cases h2 : c.km4 = 2 <;> simp_all <;> cases c.side <;> rfl

theorem SX_val : c.SX = if c.km4 = 0 then (if c.side then c.SI else c.SI.neg) else if c.km4 = 1 then c.CI
    else if c.km4 = 2 then (if c.side then c.SI.neg else c.SI) else c.CI.neg := by
  unfold SX; simp only [beq_val]
  by_cases h0 : c.km4 = 0 <;> by_cases h1 : c.km4 = 1 <;> by_cases h2 : c.km4 = 2 <;> simp_all <;> cases c.side <;> rfl

/-- `cos (πx)`, `sin (πx)` from the anchor, given the enclosures at the offset angle `t` -/
theorem cx_sx_enc {x t : ℝ} (hx : π * x = π * ((c.k : ℝ) / 2) + (if c.side then t else -t))
    (hci : c.CI.Enc (Real.cos t)) (hsi : c.SI.Enc (Real.sin t)) :
    c.CX.Enc (Real.cos (π * x)) ∧ c.SX.Enc (Real.sin (π * x)) := by
  have hcs := cos_sin_half c.k
  have hkm : c.km4 = c.k % 4 := rfl
  rw [CX_val, SX_val, hx, Real.cos_add, Real.sin_add, hcs.1, hcs.2, hkm]
  have hm : c.k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hsn := IV.enc_neg hsi
  have hcn := IV.enc_neg hci
  cases hs : c.side <;>
  · simp only [Bool.false_eq_true, if_true, if_false, Real.cos_neg, Real.sin_neg]
    interval_cases h4 : (c.k % 4)
    all_goals
      simp only [one_ne_zero, if_true, if_false,
        show ¬ ((1:ℕ) = 0) by norm_num, show ¬ ((2:ℕ) = 0) by norm_num, show ¬ ((3:ℕ) = 0) by norm_num,
        show ¬ ((2:ℕ) = 1) by norm_num, show ¬ ((3:ℕ) = 1) by norm_num, show ¬ ((3:ℕ) = 2) by norm_num,
        show ¬ ((0:ℕ) = 1) by norm_num, show ¬ ((0:ℕ) = 3) by norm_num, show ¬ ((1:ℕ) = 3) by norm_num,
        show ¬ ((2:ℕ) = 3) by norm_num, show ¬ ((0:ℕ) = 2) by norm_num, show ¬ ((1:ℕ) = 2) by norm_num]
      constructor
    all_goals first
      | (convert hci using 1; ring)
      | (convert hsi using 1; ring)
      | (convert hcn using 1; ring)
      | (convert hsn using 1; ring)

end CellA

namespace CellA
variable (c : CellA)

theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; have : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [Nat.cast_zero]; linarith

theorem nd_nonneg (a : ℕ) : (0 : ℝ) ≤ (a : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) DZ_pos.le

theorem err12 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |u| ^ 12 * terr ≤ terr :=
  mul_le_of_le_one_left terr_pos.le (pow_le_one₀ (abs_nonneg _) (abs_le_one_of h0 h1))

set_option maxHeartbeats 4000000 in
theorem base_sound (h : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.Base x := by
  unfold ok at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hLU, hTU⟩, hside⟩, hE0⟩ := h
  have hD := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have xlo : (c.LLO : ℝ) / DZ ≤ x := by rw [LLO_div]; exact hx1
  have xhi : x ≤ (c.UHI : ℝ) / DZ := by rw [UHI_div]; exact hx2
  have hL0 := nd_nonneg c.LLO
  have hx0 : 0 ≤ x := hL0.trans xlo
  have hAD := c.AD_div
  -- the offset
  have hrlo : (c.RLO : ℝ) / DZ ≤ c.roff x ∧ c.roff x ≤ (c.RHI : ℝ) / DZ ∧ 0 ≤ c.roff x := by
    cases hs : c.side
    · rw [hs] at hside; simp only [Nat.ble_eq] at hside
      have hk : (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := by
        have : ((2 * c.UN : ℕ) : ℝ) ≤ ((SC * c.k : ℕ) : ℝ) := by exact_mod_cast hside
        push_cast at this; rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
      have h1 : c.UHI ≤ c.AD := by
        have : (c.UHI : ℝ) / DZ ≤ (c.AD : ℝ) / DZ := by rw [UHI_div, hAD]; exact hk
        exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
      have h2 : c.LLO ≤ c.AD := le_trans (by
        have : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := xlo.trans xhi
        exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this) h1
      have er : c.roff x = (c.k : ℝ) / 2 - x := by simp [roff, hs]
      refine ⟨?_, ?_, ?_⟩
      · simp only [RLO, hs]; rw [show Nat.sub c.AD c.UHI = c.AD - c.UHI from rfl, Nat.cast_sub h1, sub_div, hAD, er]
        linarith
      · simp only [RHI, hs]; rw [show Nat.sub c.AD c.LLO = c.AD - c.LLO from rfl, Nat.cast_sub h2, sub_div, hAD, er]
        linarith
      · rw [er]; linarith
    · rw [hs] at hside; simp only [Nat.ble_eq] at hside
      have hk : (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := by
        have : ((SC * c.k : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by exact_mod_cast hside
        push_cast at this; rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
      have h1 : c.AD ≤ c.LLO := by
        have : (c.AD : ℝ) / DZ ≤ (c.LLO : ℝ) / DZ := by rw [LLO_div, hAD]; exact hk
        exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
      have h2 : c.AD ≤ c.UHI := le_trans h1 (by
        have : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := xlo.trans xhi
        exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this)
      have er : c.roff x = x - (c.k : ℝ) / 2 := by simp [roff, hs]
      refine ⟨?_, ?_, ?_⟩
      · simp only [RLO, hs]; rw [show Nat.sub c.LLO c.AD = c.LLO - c.AD from rfl, Nat.cast_sub h1, sub_div, hAD, er]
        linarith
      · simp only [RHI, hs]; rw [show Nat.sub c.UHI c.AD = c.UHI - c.AD from rfl, Nat.cast_sub h2, sub_div, hAD, er]
        linarith
      · rw [er]; rw [LLO_div] at xlo; linarith
  obtain ⟨hr1, hr2, hr0⟩ := hrlo
  have tlo : (c.TLZ : ℝ) / DZ ≤ π * c.roff x := by
    unfold TLZ
    have h1 := ndiv_le (Nat.mul PLN c.RLO) E20 (by norm_num [E20])
    have e : ((Nat.mul PLN c.RLO : ℕ) : ℝ) = (PLN : ℝ) * c.RLO := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    calc ((Nat.div (Nat.mul PLN c.RLO) E20 : ℕ) : ℝ) / DZ ≤ ((PLN : ℝ) * c.RLO / E20) / DZ :=
          div_le_div_of_nonneg_right h1 hD.le
      _ = ((PLN : ℝ) / E20) * ((c.RLO : ℝ) / DZ) := by ring
      _ ≤ π * c.roff x := mul_le_mul pi_lo20 hr1 (nd_nonneg _) Real.pi_pos.le
  have thi : π * c.roff x ≤ (c.TUZ : ℝ) / DZ := by
    unfold TUZ
    have h1 := le_ndivc (Nat.mul PUN c.RHI) E20 (by norm_num [E20])
    have e : ((Nat.mul PUN c.RHI : ℕ) : ℝ) = (PUN : ℝ) * c.RHI := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    have hP0 : (0 : ℝ) ≤ (PUN : ℝ) / E20 := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc π * c.roff x ≤ ((PUN : ℝ) / E20) * ((c.RHI : ℝ) / DZ) := mul_le_mul pi_hi20 hr2 hr0 hP0
      _ = ((PUN : ℝ) * c.RHI / E20) / DZ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
  have t1 : (c.TUZ : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD]; exact_mod_cast hTU
  have hTL1 : c.TLZ ≤ DZ := by
    have : (c.TLZ : ℝ) / DZ ≤ 1 := tlo.trans (thi.trans t1)
    rw [div_le_one hD] at this; exact_mod_cast this
  -- cos, sin of the offset angle
  have hTL0 := nd_nonneg c.TLZ
  have ht0 : 0 ≤ π * c.roff x := mul_nonneg Real.pi_pos.le hr0
  have ht1 : π * c.roff x ≤ 1 := thi.trans t1
  have hTU0 : 0 ≤ (c.TUZ : ℝ) / DZ := ht0.trans thi
  have hTL1' : (c.TLZ : ℝ) / DZ ≤ 1 := tlo.trans ht1
  have hu' := err12 hTU0 t1
  have hl' := err12 hTL0 hTL1'
  have hcu := (cos_sin_taylor12' _ (abs_le_one_of hTU0 t1))
  have hcl := (cos_sin_taylor12' _ (abs_le_one_of hTL0 hTL1'))
  have hERR := ERRD_ge
  have hci : c.CI.Enc (Real.cos (π * c.roff x)) := by
    have hm1 := cos_le_cos01 ht0 thi t1
    have hm2 := cos_le_cos01 hTL0 tlo ht1
    have e1 := tcos_eq c.TUZ (cosP_sub_cosN hTU)
    have e2 := tcos_eq c.TLZ (cosP_sub_cosN hTL1)
    have f1 := div_le_div_of_nonneg_right (ndiv_le (Nat.sub (cosP c.TUZ) (cosN c.TUZ)) CDEN (by norm_num [CDEN, DZ])) hD.le
    have f2 := div_le_div_of_nonneg_right (le_ndivc (Nat.sub (cosP c.TLZ) (cosN c.TLZ)) CDEN (by norm_num [CDEN, DZ])) hD.le
    have a1 := (abs_le.mp hcu.1).1
    have a2 := (abs_le.mp hcl.1).2
    constructor
    · simp only [CI, SZ.v]; rw [sub_div]; linarith
    · simp only [CI, SZ.v, Nat.add_eq]; push_cast; rw [sub_zero, add_div]; linarith
  have hsi : c.SI.Enc (Real.sin (π * c.roff x)) := by
    have hm1 := sin_le_sin01 ht0 thi t1
    have hm2 := sin_le_sin01 hTL0 tlo ht1
    have e1 := tsin_eq c.TUZ (sinP_sub_sinN hTU)
    have e2 := tsin_eq c.TLZ (sinP_sub_sinN hTL1)
    have f1 := div_le_div_of_nonneg_right (ndiv_le (Nat.sub (sinP c.TLZ) (sinN c.TLZ)) SDEN (by norm_num [SDEN, DZ])) hD.le
    have f2 := div_le_div_of_nonneg_right (le_ndivc (Nat.sub (sinP c.TUZ) (sinN c.TUZ)) SDEN (by norm_num [SDEN, DZ])) hD.le
    have a1 := (abs_le.mp hcl.2).1
    have a2 := (abs_le.mp hcu.2).2
    constructor
    · simp only [SI, SZ.v]; rw [sub_div]; linarith
    · simp only [SI, SZ.v, Nat.add_eq]; push_cast; rw [sub_zero, add_div]; linarith
  have hx_eq : π * x = π * ((c.k : ℝ) / 2) + (if c.side then π * c.roff x else -(π * c.roff x)) := by
    cases hs : c.side <;> simp [roff, hs] <;> ring
  have hcxsx := c.cx_sx_enc hx_eq hci hsi
  -- πx and E
  have blo : (c.BLZ : ℝ) / DZ ≤ π * x := by
    unfold BLZ
    have h1 := ndiv_le (Nat.mul PLN c.LLO) E20 (by norm_num [E20])
    have e : ((Nat.mul PLN c.LLO : ℕ) : ℝ) = (PLN : ℝ) * c.LLO := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    calc ((Nat.div (Nat.mul PLN c.LLO) E20 : ℕ) : ℝ) / DZ ≤ ((PLN : ℝ) * c.LLO / E20) / DZ :=
          div_le_div_of_nonneg_right h1 hD.le
      _ = ((PLN : ℝ) / E20) * ((c.LLO : ℝ) / DZ) := by ring
      _ ≤ π * x := mul_le_mul pi_lo20 xlo hL0 Real.pi_pos.le
  have bhi : π * x ≤ (c.BUZ : ℝ) / DZ := by
    unfold BUZ
    have h1 := le_ndivc (Nat.mul PUN c.UHI) E20 (by norm_num [E20])
    have e : ((Nat.mul PUN c.UHI : ℕ) : ℝ) = (PUN : ℝ) * c.UHI := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    have hP0 : (0 : ℝ) ≤ (PUN : ℝ) / E20 := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc π * x ≤ ((PUN : ℝ) / E20) * ((c.UHI : ℝ) / DZ) := mul_le_mul pi_hi20 xhi hx0 hP0
      _ = ((PUN : ℝ) * c.UHI / E20) / DZ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
  have hB0 := nd_nonneg c.BLZ
  have hpx0 : 0 ≤ π * x := hB0.trans blo
  have elo : (c.E0 : ℝ) / DZ ≤ 2 * (π * x) ^ 2 - 1 := by
    unfold E0 at hE0 ⊢
    have hle : DZ ≤ Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ := by
      by_contra hc; push_neg at hc
      rw [show Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ = Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ - DZ
        from rfl, Nat.sub_eq_zero_of_le hc.le] at hE0
      exact absurd hE0 (lt_irrefl 0)
    rw [show Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ = Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ - DZ
      from rfl, Nat.cast_sub hle, sub_div, div_self hD.ne']
    have h1 := ndiv_le (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ (by norm_num [DZ])
    have e : ((Nat.mul 2 (Nat.mul c.BLZ c.BLZ) : ℕ) : ℝ) = 2 * (c.BLZ : ℝ) * c.BLZ := by
      rw [Nat.mul_eq, Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    have hsq : ((c.BLZ : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ) ≤ (π * x) * (π * x) := mul_le_mul blo blo hB0 hpx0
    have : ((Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ : ℕ) : ℝ) / DZ ≤ 2 * (((c.BLZ : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ)) := by
      calc _ ≤ (2 * (c.BLZ : ℝ) * c.BLZ / DZ) / DZ := div_le_div_of_nonneg_right h1 hD.le
        _ = _ := by ring
    have hpq : (π * x) ^ 2 = (π * x) * (π * x) := sq _
    linarith
  have hE0r : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast hE0) hD
  have ehi : 2 * (π * x) ^ 2 - 1 ≤ (c.E1 : ℝ) / DZ := by
    unfold E1
    have h1 := le_ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ (by norm_num [DZ])
    have e : ((Nat.mul 2 (Nat.mul c.BUZ c.BUZ) : ℕ) : ℝ) = 2 * (c.BUZ : ℝ) * c.BUZ := by
      rw [Nat.mul_eq, Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    have hsq : (π * x) * (π * x) ≤ ((c.BUZ : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ) := mul_le_mul bhi bhi hpx0 (hpx0.trans bhi)
    have h2 : 2 * (((c.BUZ : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ)) ≤ ((ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ : ℕ) : ℝ) / DZ := by
      calc _ = (2 * (c.BUZ : ℝ) * c.BUZ / DZ) / DZ := by ring
        _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
    have hcast := natsub_ge (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ
    have h3 := div_le_div_of_nonneg_right hcast hD.le
    rw [sub_div, div_self hD.ne'] at h3
    have hpq : (π * x) ^ 2 = (π * x) * (π * x) := sq _
    have e3 : ((ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ - DZ : ℕ) : ℝ) = ((Nat.sub (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ : ℕ) : ℝ) := rfl
    rw [e3] at h3
    linarith
  exact ⟨xlo, xhi, hcxsx.1, hcxsx.2, blo, bhi, hE0, elo, ehi, hr0, tlo, thi, t1⟩

end CellA

end AMW.G

end

