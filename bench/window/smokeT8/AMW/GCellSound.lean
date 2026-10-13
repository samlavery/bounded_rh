import AMW.GAsm2

/-!
# AMW/GCellSound — soundness of the AM cell evaluator (stage G)

For a cell with `c.ok = true` and every `x ∈ [LN, UN] / SC`: `K0 ∋ kfunAM x`, and (with the denominators of `E²`,
`E³` positive) `K1 ∋ k1AM x`, `K2 ∋ k2AM x`.
-/

noncomputable section

open Real

namespace AMW.G

namespace CellA
variable (c : CellA)

/-- the anchor facts used by the assembly -/
theorem x_pos (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : 0 < x := by
  have b := c.base_sound hc hx1 hx2
  have hE0 : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast b.e0) DZ_pos
  have hB0 : (0 : ℝ) ≤ (c.BLZ : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) DZ_pos.le
  have h1 := b.elo; have h2 := b.blo
  have hpx : 0 < π * x := by nlinarith
  exact pos_of_mul_pos_right hpx Real.pi_pos.le

theorem sepx (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    ∀ j : ℕ, 1 ≤ j → 2 * j ≠ c.k → x ≠ j := by
  have b := c.base_sound hc hx1 hx2
  intro j _ hj
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · have := (c.sep hc j).1 h; linarith [b.xlo]
  · have := (c.sep hc j).2 h; linarith [b.xhi]

theorem PG_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.PG.Enc (2 * gamAM * (π * x)) := by
  have b := c.base_sound hc hx1 hx2
  have hD := DZ_pos
  have hg := GAM_bounds
  have hB0 : (0 : ℝ) ≤ (c.BLZ : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  have hG0 : (0 : ℝ) ≤ (GAM0 : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  refine enc_ofN ?_ ?_
  · have h1 := ndiv_le (Nat.mul GAM0 c.BLZ) DZ (by norm_num [DZ])
    have e : ((Nat.mul GAM0 c.BLZ : ℕ) : ℝ) = (GAM0 : ℝ) * c.BLZ := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    calc ((Nat.div (Nat.mul GAM0 c.BLZ) DZ : ℕ) : ℝ) / DZ ≤ ((GAM0 : ℝ) * c.BLZ / DZ) / DZ :=
          div_le_div_of_nonneg_right h1 hD.le
      _ = ((GAM0 : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ) := by ring
      _ ≤ 2 * gamAM * (π * x) := mul_le_mul hg.1 b.blo hB0 (hG0.trans hg.1)
  · have h1 := le_ndivc (Nat.mul GAM1 c.BUZ) DZ (by norm_num [DZ])
    have e : ((Nat.mul GAM1 c.BUZ : ℕ) : ℝ) = (GAM1 : ℝ) * c.BUZ := by rw [Nat.mul_eq]; push_cast; ring
    rw [e] at h1
    have hpx : 0 ≤ π * x := hB0.trans b.blo
    calc 2 * gamAM * (π * x) ≤ ((GAM1 : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ) :=
          mul_le_mul hg.2 b.bhi hpx (hG0.trans (hg.1.trans hg.2))
      _ = ((GAM1 : ℝ) * c.BUZ / DZ) / DZ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le

theorem NI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.NI.Enc (mN x) := by
  have b := c.base_sound hc hx1 hx2
  have h := IV.enc_sub b.cx (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.sx)
  unfold mN; exact h

theorem EI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.EI.Enc (-mD x) := by
  have b := c.base_sound hc hx1 hx2
  refine enc_ofN ?_ ?_ <;> unfold mD
  · linarith [b.elo]
  · linarith [b.ehi]

theorem BI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.BI.Enc (π * x) := by
  have b := c.base_sound hc hx1 hx2
  exact enc_ofN b.blo b.bhi

theorem mD_neg (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : mD x < 0 := by
  have b := c.base_sound hc hx1 hx2
  have hE0 : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast b.e0) DZ_pos
  unfold mD; linarith [b.elo]

/-- the near terms -/
theorem nearOn_iff : c.nearOn = true ↔ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := by
  unfold nearOn; simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem roff_near (hk : c.k % 2 = 0) (x : ℝ) :
    π * (x - ((c.k / 2 : ℕ) : ℝ)) = if c.side then π * c.roff x else -(π * c.roff x) := by
  have e : ((c.k / 2 : ℕ) : ℝ) = (c.k : ℝ) / 2 := by
    have := Nat.div_add_mod c.k 2; rw [hk] at this
    have h2 : ((2 * (c.k / 2) : ℕ) : ℝ) = (c.k : ℝ) := by exact_mod_cast (by omega : 2 * (c.k / 2) = c.k)
    push_cast at h2; linarith
  rw [e]; unfold roff; split_ifs <;> ring

theorem B0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.B0.Enc (nsel c.k (fun j => Real.sinc (π * (x - j)))) := by
  rw [nsel_eq]
  unfold B0
  cases hn : c.nearOn
  · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
    rw [if_neg this]; exact IV.enc_zero
  · have h := (c.nearOn_iff).mp hn
    rw [if_pos h]
    simp only
    have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9]) (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (c.S0_enc hc hx1 hx2))
    have hj0' : c.j0 = c.k / 2 := rfl
    have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
    have hr := c.roff_near h.1 x
    have hs : Real.sinc (π * (x - ((c.k / 2 : ℕ) : ℝ))) = Real.sinc (π * c.roff x) := by
      rw [hr]; split_ifs
      · rfl
      · exact Real.sinc_neg _
    rw [hj0'] at hv
    convert hS using 1
    rw [hs, hj0', ← hv, Nat.mul_eq]; push_cast; ring

theorem B1_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.B1.Enc (π * nsel c.k (fun j => sc1 (π * (x - j)))) := by
  rw [nsel_eq]
  unfold B1
  cases hn : c.nearOn
  · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
    rw [if_neg this, mul_zero]; exact IV.enc_zero
  · have h := (c.nearOn_iff).mp hn
    rw [if_pos h]
    simp only
    have hG : (Bool.rec (motive := fun _ => IV) c.G1.neg c.G1 c.side).Enc (sc1 (π * (x - ((c.k / 2 : ℕ) : ℝ)))) := by
      rw [c.roff_near h.1 x]
      cases hs : c.side
      · simp only [Bool.false_eq_true, if_false, sc1_neg]; exact IV.enc_neg (c.G1_enc hc hx1 hx2)
      · simp only [if_true]; exact c.G1_enc hc hx1 hx2
    have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9])
      (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (IV.enc_mulc PIC_enc (by simp [PIC, IV.ofN, SZ.v]) hG))
    have hj0' : c.j0 = c.k / 2 := rfl
    have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
    rw [hj0'] at hv
    convert hS using 1
    rw [hj0', ← hv, Nat.mul_eq]; push_cast; ring

theorem B2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.B2.Enc (π ^ 2 * nsel c.k (fun j => sc2 (π * (x - j)))) := by
  rw [nsel_eq]
  unfold B2
  cases hn : c.nearOn
  · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
    rw [if_neg this, mul_zero]; exact IV.enc_zero
  · have h := (c.nearOn_iff).mp hn
    rw [if_pos h]
    simp only
    have hG : c.G2.Enc (sc2 (π * (x - ((c.k / 2 : ℕ) : ℝ)))) := by
      rw [c.roff_near h.1 x]
      split_ifs
      · exact c.G2_enc hc hx1 hx2
      · rw [sc2_neg]; exact c.G2_enc hc hx1 hx2
    have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9])
      (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (IV.enc_mulc PI2C_enc (by simp [PI2C, IV.ofN, SZ.v]) hG))
    have hj0' : c.j0 = c.k / 2 := rfl
    have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
    rw [hj0'] at hv
    convert hS using 1
    rw [hj0', ← hv, Nat.mul_eq]; push_cast; ring

/-- **the cell enclosure of `k`** -/
theorem K0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.K0.Enc (kfunAM x) := by
  have b := c.base_sound hc hx1 hx2
  have hD := c.mD_neg hc hx1 hx2
  have hx0 := c.x_pos hc hx1 hx2
  have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
  have h1 := IV.enc_divp (I := c.NI.neg) b.e0 b.elo b.ehi (IV.enc_neg (c.NI_enc hc hx1 hx2))
  have h2 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF0)
  have h3 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B0_enc hc hx1 hx2)
  have h := IV.enc_add h1 (IV.enc_add h2 h3)
  unfold K0 SF0
  convert h using 1
  rw [kfunAM_eq hD.ne, sum_T0 hx0 (c.sepx hc hx1 hx2)]
  have hE : 2 * (π * x) ^ 2 - 1 = -mD x := by unfold mD; ring
  rw [hE]
  have hπ := Real.pi_pos.ne'
  field_simp

end CellA

theorem prod_lo_nat (a b : ℕ) {A B : ℝ} (hA : (a : ℝ) / DZ ≤ A) (hB : (b : ℝ) / DZ ≤ B) :
    ((Nat.div (Nat.mul a b) DZ : ℕ) : ℝ) / DZ ≤ A * B := by
  have hD := DZ_pos
  have h1 := ndiv_le (Nat.mul a b) DZ (by norm_num [DZ])
  have e : ((Nat.mul a b : ℕ) : ℝ) = (a : ℝ) * b := by rw [Nat.mul_eq]; push_cast; ring
  rw [e] at h1
  have ha : (0 : ℝ) ≤ (a : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  have hb : (0 : ℝ) ≤ (b : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  calc ((Nat.div (Nat.mul a b) DZ : ℕ) : ℝ) / DZ ≤ ((a : ℝ) * b / DZ) / DZ := div_le_div_of_nonneg_right h1 hD.le
    _ = ((a : ℝ) / DZ) * ((b : ℝ) / DZ) := by ring
    _ ≤ A * B := mul_le_mul hA hB hb (ha.trans hA)

theorem prod_hi_nat (a b : ℕ) {A B : ℝ} (hA : A ≤ (a : ℝ) / DZ) (hB : B ≤ (b : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    A * B ≤ ((ndivc (Nat.mul a b) DZ : ℕ) : ℝ) / DZ := by
  have hD := DZ_pos
  have h1 := le_ndivc (Nat.mul a b) DZ (by norm_num [DZ])
  have e : ((Nat.mul a b : ℕ) : ℝ) = (a : ℝ) * b := by rw [Nat.mul_eq]; push_cast; ring
  rw [e] at h1
  calc A * B ≤ ((a : ℝ) / DZ) * ((b : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = ((a : ℝ) * b / DZ) / DZ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le

namespace CellA
variable (c : CellA)

theorem E_bounds (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    (c.E2L : ℝ) / DZ ≤ mD x ^ 2 ∧ mD x ^ 2 ≤ (c.E2U : ℝ) / DZ ∧
      (c.E3L : ℝ) / DZ ≤ (-mD x) ^ 3 ∧ (-mD x) ^ 3 ≤ (c.E3U : ℝ) / DZ := by
  have hEI := c.EI_enc hc hx1 hx2
  have b := c.base_sound hc hx1 hx2
  have hD := DZ_pos
  have e0 : (c.E0 : ℝ) / DZ ≤ -mD x := by unfold mD; linarith [b.elo]
  have e1 : -mD x ≤ (c.E1 : ℝ) / DZ := by unfold mD; linarith [b.ehi]
  have hE0 : (0 : ℝ) ≤ (c.E0 : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  have hm : 0 ≤ -mD x := hE0.trans e0
  have s2 : mD x ^ 2 = (-mD x) * (-mD x) := by ring
  have l2 : (c.E2L : ℝ) / DZ ≤ mD x ^ 2 := by rw [s2]; exact prod_lo_nat c.E0 c.E0 e0 e0
  have u2 : mD x ^ 2 ≤ (c.E2U : ℝ) / DZ := by rw [s2]; exact prod_hi_nat c.E1 c.E1 e1 e1 hm hm
  have s3 : (-mD x) ^ 3 = mD x ^ 2 * (-mD x) := by ring
  refine ⟨l2, u2, ?_, ?_⟩
  · rw [s3]; exact prod_lo_nat c.E2L c.E0 l2 e0
  · rw [s3]; exact prod_hi_nat c.E2U c.E1 u2 e1 (sq_nonneg _) hm

theorem MI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.MI.Enc (mM x) := by
  have b := c.base_sound hc hx1 hx2
  have hX := IV.enc_add (IV.enc_mulc G1C_enc (by simp [G1C, IV.ofN, SZ.v]) b.sx)
    (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.cx)
  have h1 := IV.enc_mulc (c.EI_enc hc hx1 hx2) (by simp only [EI, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact Nat.cast_nonneg _) hX
  have h2 := IV.enc_mulc (IV.enc_muln 4 (c.BI_enc hc hx1 hx2)) (by simp [BI, IV.muln, IV.ofN, SZ.muln, SZ.v])
    (c.NI_enc hc hx1 hx2)
  have h := IV.enc_add h1 h2
  unfold MI; convert h using 1; unfold mM mNb; push_cast; ring

/-- **the cell enclosure of `k'`** -/
theorem K1_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.K1.Enc (k1AM x) := by
  have b := c.base_sound hc hx1 hx2
  have hD := c.mD_neg hc hx1 hx2
  have hx0 := c.x_pos hc hx1 hx2
  have hEb := c.E_bounds hc hx1 hx2
  have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
  have hF1 := c.FA_enc hc (n := 1) (by norm_num) b.xlo b.xhi
  have h1 := IV.enc_mulc PIC_enc (by simp [PIC, IV.ofN, SZ.v]) (IV.enc_divp (I := c.MI) hE2 hEb.1 hEb.2.1 (c.MI_enc hc hx1 hx2))
  have h2 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (IV.enc_mul b.cx hF0)
  have h3 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF1)
  have h4 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B1_enc hc hx1 hx2)
  have h := IV.enc_add h1 (IV.enc_add (IV.enc_add h2 h3) h4)
  unfold K1
  convert h using 1
  rw [k1AM_eq hD.ne, sum_T1 hx0 (c.sepx hc hx1 hx2)]
  have hπ := Real.pi_pos.ne'
  have hmD := hD.ne
  field_simp

theorem N2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.N2.Enc (mN2 x) := by
  have b := c.base_sound hc hx1 hx2
  have h := IV.enc_sub (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.sx)
    (IV.enc_mulc G2C_enc (by simp [G2C, IV.ofN, SZ.v]) b.cx)
  unfold N2; convert h using 1; unfold mN2; ring

/-- **the cell enclosure of `k''`** -/
theorem K2_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x)
    (hx2 : x ≤ (c.UN : ℝ) / SC) : c.K2.Enc (k2AM x) := by
  have b := c.base_sound hc hx1 hx2
  have hD := c.mD_neg hc hx1 hx2
  have hx0 := c.x_pos hc hx1 hx2
  have hEb := c.E_bounds hc hx1 hx2
  have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
  have hF1 := c.FA_enc hc (n := 1) (by norm_num) b.xlo b.xhi
  have hF2 := c.FA_enc hc (n := 2) (by norm_num) b.xlo b.xhi
  have hE2enc : (IV.ofN c.E2L c.E2U).Enc (mD x ^ 2) := enc_ofN hEb.1 hEb.2.1
  have hP : c.PP.Enc (mP x) := by
    have h1 := IV.enc_mulc hE2enc (by simp [IV.ofN, SZ.v]) (c.N2_enc hc hx1 hx2)
    have h2 := IV.enc_muln 4 (IV.enc_mulc (c.EI_enc hc hx1 hx2) (by simp only [EI, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact Nat.cast_nonneg _) (c.NI_enc hc hx1 hx2))
    have h3 := IV.enc_muln 8 (IV.enc_mulc (c.BI_enc hc hx1 hx2) (by simp [BI, IV.ofN, SZ.v]) (c.MI_enc hc hx1 hx2))
    have h := IV.enc_add (IV.enc_sub h1 h2) h3
    unfold PP; convert h using 1; unfold mP; push_cast; ring
  have h1 := IV.enc_neg (IV.enc_mulc PI2C_enc (by simp [PI2C, IV.ofN, SZ.v])
    (IV.enc_divp (I := c.PP) hE3 hEb.2.2.1 hEb.2.2.2 hP))
  have h2 := IV.enc_muln 2 (IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (IV.enc_mul b.cx hF1))
  have h3 := IV.enc_mulc TAUC_enc (by simp [TAUC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF0)
  have h4 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF2)
  have h5 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B2_enc hc hx1 hx2)
  have h := IV.enc_add h1 (IV.enc_add (IV.enc_sub h2 h3) (IV.enc_add h4 h5))
  unfold K2 SF0
  convert h using 1
  rw [k2AM_eq hD.ne, sum_T2 hx0 (c.sepx hc hx1 hx2)]
  have hπ := Real.pi_pos.ne'
  have hmD := hD.ne
  push_cast
  field_simp
  ring

end CellA

/-! ## The three cell bounds: `w`, `w'`, `w''` -/

theorem SZ.max_le {a b : SZ} {c : ℝ} (ha : a.v ≤ c) (hb : b.v ≤ c) : (SZ.max a b).v ≤ c := by
  unfold SZ.max; cases a.le b
  · exact ha
  · exact hb

/-- `max(0, lo, −hi)` bounds `|a|` (scale `DZ`) -/
def mabs (I : IV) : SZ := SZ.max (SZ.ofN 0) (SZ.max I.lo I.hi.neg)

theorem mabs_nonneg (I : IV) : 0 ≤ (mabs I).v :=
  (SZ.le_v_max_left _ _).trans' (by simp [SZ.ofN, SZ.v])

theorem mabs_le {I : IV} {a : ℝ} (h : I.Enc a) : (mabs I).v ≤ |a| * DZ := by
  have hD := DZ_pos
  unfold mabs
  refine SZ.max_le (by simp [SZ.ofN, SZ.v]; positivity) (SZ.max_le ?_ ?_)
  · have := (div_le_iff₀ hD).mp h.1; nlinarith [le_abs_self a]
  · rw [SZ.v_neg]; have := (le_div_iff₀ hD).mp h.2; nlinarith [neg_abs_le a]

namespace CellA
variable (c : CellA)

theorem KA_eq : c.KA = mabs c.K0 := rfl

/-- `|k| ≥ KAn / DZ` on the cell (`KA ≥ 0` as a natural) -/
def KAn (c : CellA) : ℕ := Nat.sub c.KA.p c.KA.n

theorem KAn_eq : (c.KAn : ℝ) = c.KA.v := by
  have h := c.KA_eq ▸ mabs_nonneg c.K0
  unfold KAn SZ.v at *
  have hle : c.KA.n ≤ c.KA.p := by exact_mod_cast (sub_nonneg.mp h)
  rw [show Nat.sub c.KA.p c.KA.n = c.KA.p - c.KA.n from rfl, Nat.cast_sub hle]

/-- **zero order**: `(KAn / DZ)² ≤ wfunAM x` -/
theorem w_lower (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    ((c.KAn : ℝ) / DZ) ^ 2 ≤ wfunAM x := by
  have hD := DZ_pos
  have hA : (c.KAn : ℝ) / DZ ≤ |kfunAM x| := by
    rw [KAn_eq, KA_eq, div_le_iff₀ hD]; exact mabs_le (c.K0_enc hc hx1 hx2)
  have hA0 : (0 : ℝ) ≤ (c.KAn : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  unfold wfunAM
  calc ((c.KAn : ℝ) / DZ) ^ 2 ≤ |kfunAM x| ^ 2 := pow_le_pow_left₀ hA0 hA 2
    _ = kfunAM x ^ 2 := sq_abs _

/-- **first order**: `W1 ∋ w1AM x` -/
theorem w1_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.W1.Enc (w1AM x) := by
  have h := IV.enc_muln 2 (IV.enc_mul (c.K0_enc hc hx1 hx2) (c.K1_enc hc hE2 hx1 hx2))
  unfold W1 w1AM; convert h using 1; push_cast; ring

theorem W2L_eq : c.W2L = SZ.add (SZ.mul (mabs c.K1) (mabs c.K1)) ((c.K0.mul c.K2).lo.muln DZ) := rfl

/-- **second order**: `W2L ≥ 0` gives `w2AM x ≥ 0` -/
theorem w2_nonneg (hc : c.ok = true) (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L) (hW : c.W2L.nonneg = true) {x : ℝ}
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : 0 ≤ w2AM x := by
  have hD := DZ_pos
  have hK1 := c.K1_enc hc hE2 hx1 hx2
  have hKK := IV.enc_mul (c.K0_enc hc hx1 hx2) (c.K2_enc hc hE2 hE3 hx1 hx2)
  have hW' := (SZ.nonneg_iff _).mp hW
  rw [W2L_eq, SZ.v_add, SZ.v_mul, SZ.v_muln] at hW'
  have hs0 := mabs_nonneg c.K1
  have hsk := mabs_le hK1
  have hsq : (mabs c.K1).v * (mabs c.K1).v ≤ (k1AM x) ^ 2 * DZ ^ 2 := by
    have := mul_le_mul hsk hsk hs0 (hs0.trans hsk)
    rw [show |k1AM x| * DZ * (|k1AM x| * DZ) = |k1AM x| ^ 2 * DZ ^ 2 by ring, sq_abs] at this; exact this
  have hq := hKK.1
  have hD2 : (0 : ℝ) < DZ ^ 2 := by positivity
  unfold w2AM
  generalize (c.K0.mul c.K2).lo.v = q at hq hW'
  generalize (mabs c.K1).v = sv at hsq hW'
  generalize kfunAM x * k2AM x = kk at hq ⊢
  generalize k1AM x = a at hsq ⊢
  have hq' : q ≤ kk * DZ := (div_le_iff₀ hD).mp hq
  have hkk : q * DZ ≤ kk * DZ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hq' hD.le; linarith [show kk * DZ * DZ = kk * DZ ^ 2 by ring]
  have h3 : 0 ≤ (a ^ 2 + kk) * DZ ^ 2 := by linarith
  have := nonneg_of_mul_nonneg_left h3 hD2
  linarith

end CellA

end AMW.G
