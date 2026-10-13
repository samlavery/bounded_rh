import MvtDefs

-- MVTPROOFS-BEGIN
noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### the derivative of `wfun` -/

/-- the pieces of `w' = 2π N M / D³` at `b = π x` -/
def kN (x : ℝ) : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)
def kD (x : ℝ) : ℝ := 1 - 2 * (Real.pi * x) ^ 2
def kNb (x : ℝ) : ℝ := -(1 + 2 * gam) * Real.sin (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)
def kM (x : ℝ) : ℝ := kNb x * kD x + 4 * (Real.pi * x) * kN x
/-- the derivative of `wfun` where `2 (π x)² ≠ 1` -/
def w1 (x : ℝ) : ℝ := 2 * Real.pi * kN x * kM x / kD x ^ 3

theorem hasDerivAt_pix (x : ℝ) : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
  simpa using (hasDerivAt_id x).const_mul Real.pi

theorem hasDerivAt_kN (x : ℝ) : HasDerivAt kN (Real.pi * kNb x) x := by
  have h := (hasDerivAt_pix x).cos.sub (((hasDerivAt_pix x).const_mul (2 * gam)).mul (hasDerivAt_pix x).sin)
  have e : kN = fun y : ℝ => Real.cos (Real.pi * y) - 2 * gam * (Real.pi * y) * Real.sin (Real.pi * y) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kNb; ring

theorem hasDerivAt_kD (x : ℝ) : HasDerivAt kD (-(4 * Real.pi * (Real.pi * x))) x := by
  have h := (((hasDerivAt_pix x).pow 2).const_mul 2).const_sub 1
  have e : kD = fun y : ℝ => 1 - 2 * (Real.pi * y) ^ 2 := rfl
  rw [e]
  refine h.congr_deriv ?_
  rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
  push_cast; ring

theorem continuous_kD : Continuous kD := by
  unfold kD; fun_prop

theorem hasDerivAt_wfun (x : ℝ) (hx : kD x ≠ 0) : HasDerivAt wfun (w1 x) x := by
  have hsq := ((hasDerivAt_kN x).div (hasDerivAt_kD x) hx).pow 2
  have hev : ∀ᶠ y in nhds x, kD y ≠ 0 := continuous_kD.continuousAt.eventually_ne hx
  have heq : wfun =ᶠ[nhds x] fun y => (kN y / kD y) ^ 2 := by
    filter_upwards [hev] with y hy
    unfold wfun
    rw [kfun_closed y hy]
    rfl
  refine (hsq.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [Pi.div_apply]
  unfold w1 kM
  rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  field_simp
  ring

/-! ### interval products at scale `DZ` -/

theorem mul_ge_min4 {a b A1 A2 B1 B2 : ℝ} (ha1 : A1 ≤ a) (ha2 : a ≤ A2) (hb1 : B1 ≤ b) (hb2 : b ≤ B2) :
    min (min (A1 * B1) (A1 * B2)) (min (A2 * B1) (A2 * B2)) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · have h1 : A1 * b ≤ a * b := mul_le_mul_of_nonneg_right ha1 hb
    rcases le_total 0 A1 with hA | hA
    · have : A1 * B1 ≤ A1 * b := mul_le_mul_of_nonneg_left hb1 hA
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (this.trans h1)
    · have : A1 * B2 ≤ A1 * b := mul_le_mul_of_nonpos_left hb2 hA
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (this.trans h1)
  · have h1 : A2 * b ≤ a * b := mul_le_mul_of_nonpos_right ha2 hb
    rcases le_total 0 A2 with hA | hA
    · have : A2 * B1 ≤ A2 * b := mul_le_mul_of_nonneg_left hb1 hA
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (this.trans h1)
    · have : A2 * B2 ≤ A2 * b := mul_le_mul_of_nonpos_left hb2 hA
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (this.trans h1)

theorem mul_le_max4 {a b A1 A2 B1 B2 : ℝ} (ha1 : A1 ≤ a) (ha2 : a ≤ A2) (hb1 : B1 ≤ b) (hb2 : b ≤ B2) :
    a * b ≤ max (max (A1 * B1) (A1 * B2)) (max (A2 * B1) (A2 * B2)) := by
  rcases le_total 0 b with hb | hb
  · have h1 : a * b ≤ A2 * b := mul_le_mul_of_nonneg_right ha2 hb
    rcases le_total 0 A2 with hA | hA
    · have : A2 * b ≤ A2 * B2 := mul_le_mul_of_nonneg_left hb2 hA
      exact (h1.trans this).trans (le_trans (le_max_right _ _) (le_max_right _ _))
    · have : A2 * b ≤ A2 * B1 := mul_le_mul_of_nonpos_left hb1 hA
      exact (h1.trans this).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · have h1 : a * b ≤ A1 * b := mul_le_mul_of_nonpos_right ha1 hb
    rcases le_total 0 A1 with hA | hA
    · have : A1 * b ≤ A1 * B2 := mul_le_mul_of_nonneg_left hb2 hA
      exact (h1.trans this).trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · have : A1 * b ≤ A1 * B1 := mul_le_mul_of_nonpos_left hb1 hA
      exact (h1.trans this).trans (le_trans (le_max_left _ _) (le_max_left _ _))

theorem imulD_sound (I J : ℤ × ℤ) {a b : ℝ} (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ)
    (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulD I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulD I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hdd : ∀ u v : ℤ, u ≤ v → (u : ℝ) / DZ / DZ ≤ (v : ℝ) / DZ / DZ := fun u v h =>
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le) hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    refine le_trans ?_ (mul_ge_min4 ha.1 ha.2 hb.1 hb.2)
    unfold imin4
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_left _ _) (min_le_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_left _ _) (min_le_right _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_right _ _) (min_le_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_right _ _) (min_le_right _ _))
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    refine le_trans (mul_le_max4 ha.1 ha.2 hb.1 hb.2) ?_
    unfold imax4
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_right _ _) (le_max_right _ _))

theorem zfdiv_nonneg {z : ℤ} (h : 0 ≤ z) : 0 ≤ zfdiv z := by
  unfold zfdiv; rw [if_pos h]; exact Int.natCast_nonneg _

theorem imulP_sound (I J : ℤ × ℤ) (h0 : 0 ≤ I.1) {a b : ℝ} (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ)
    (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulP I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulP I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hdd : ∀ u v : ℤ, u ≤ v → (u : ℝ) / DZ / DZ ≤ (v : ℝ) / DZ / DZ := fun u v h =>
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le) hD.le
  have hA0 : (0:ℝ) ≤ (I.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0) hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    exact prod_lo hA0 ha.1 ha.2 hb.1 (by rw [← ec]; exact hdd _ _ (min_le_left _ _))
      (by rw [← ec]; exact hdd _ _ (min_le_right _ _))
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    exact prod_hi hA0 ha.1 ha.2 hb.2 (by rw [← ec]; exact hdd _ _ (le_max_left _ _))
      (by rw [← ec]; exact hdd _ _ (le_max_right _ _))

theorem imulPP_sound (I J : ℤ × ℤ) (h0 : 0 ≤ I.1) (h0' : 0 ≤ J.1) {a b : ℝ}
    (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ) (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulPP I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulPP I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hA0 : (0:ℝ) ≤ (I.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0) hD.le
  have hB0 : (0:ℝ) ≤ (J.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0') hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    rw [ec]
    exact mul_le_mul ha.1 hb.1 hB0 (hA0.trans ha.1)
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    rw [ec]
    exact mul_le_mul ha.2 hb.2 (hB0.trans hb.1) ((hA0.trans ha.1).trans ha.2)

theorem gami_sound : ((GAMI.1 : ℤ) : ℝ) / DZ ≤ 2 * gam ∧ 2 * gam ≤ ((GAMI.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [GAMI, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

theorem g1i_sound : ((G1I.1 : ℤ) : ℝ) / DZ ≤ 1 + 2 * gam ∧ 1 + 2 * gam ≤ ((G1I.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [G1I, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

/-! ### the trigonometric enclosures of a cell (the first half of `cellN_soundZ'`) -/

set_option maxHeartbeats 4000000 in
theorem cellN_trig (c : CellN) (hc : c.okC = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    (((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ) ∧
    (((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ) ∧
    (((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ) ∧
    ((DZ * DZ : ℕ) : ℝ) < ((2 * c.BLZ * c.BLZ : ℕ) : ℝ) := by
  simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 100000000000000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hLLO : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := ndiv_le (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.LLO
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.UHI : ℕ) : ℝ) / DZ := by
    have := le_ndivc (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.UHI
    push_cast at this ⊢
    rw [le_div_iff₀ hD0]
    calc (c.UN : ℝ) / SC * DZ = (c.UN : ℝ) * DZ / SC := by ring
      _ ≤ _ := this
  have hAD : ((c.AD : ℕ) : ℝ) / DZ = (c.k : ℝ) / 2 := by
    unfold CellN.AD; simp only [DZ, DZ2]; push_cast; ring
  have hL0 : (0:ℝ) ≤ (c.LN : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := hL0.trans hx1
  have hkF : c.side = false → (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := fun hs => by
    have : (2 * c.UN : ℝ) ≤ (c.k * SC : ℝ) := by exact_mod_cast hsideF hs
    rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
  have hkT : c.side = true → (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := fun hs => by
    have : (c.k * SC : ℝ) ≤ (2 * c.LN : ℝ) := by exact_mod_cast hsideT hs
    rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.RLO : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.RLO
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.UHI c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.LLO with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.RHI : ℕ) : ℝ) / DZ := by
    unfold CellN.RHI
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.LLO ≤ c.AD := by
        have h1 : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.UHI := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.UHI : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  have hTL : ((c.TLZ : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.TLZ
    exact ndiv_prod_le PLN c.RLO _ (by norm_num) PLN_le hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.TUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.TUZ
    exact le_ndivc_prod PUN c.RHI _ (by norm_num) PUN_ge hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.TUZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.TLZ : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  have hc1 : ((c.CLZ : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU1
    have h1 := cosLo_le c.TUZ hcP1
    have h2 := ERRD_ge
    unfold CellN.CLZ; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CUZ : ℤ) : ℝ) / DZ := by
    have h := cos_upper hTL0 hTL hθ1
    have h1 := le_cosHi c.TLZ hcP2
    have h2 := ERRD_ge
    unfold CellN.CUZ; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.SLZ : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    have h1 := sinLo_le c.TLZ hsP1
    have h2 := ERRD_ge
    unfold CellN.SLZ; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SUZ : ℤ) : ℝ) / DZ := by
    have h := sin_upper hθ0 hTUr hTU1
    have h1 := le_sinHi c.TUZ hsP2
    have h2 := ERRD_ge
    unfold CellN.SUZ; push_cast; rw [add_div]
    linarith
  have hcs := cos_sin_half c.k
  have hCX : ((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, Bool.false_eq_true, if_false]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, if_true]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hSX : ((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, Bool.false_eq_true, if_false]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, if_true]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hb1 : ((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.BLZ
    exact ndiv_prod_le PLN c.LLO _ (by norm_num) PLN_le (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.BUZ
    exact le_ndivc_prod PUN c.UHI _ (by norm_num) PUN_ge (hx2.trans hUHI) Real.pi_pos.le hx0
  exact ⟨hCX, hSX, ⟨hb1, hb2⟩, by exact_mod_cast hB⟩

/-! ### the final quotient `2π q / d³` -/

theorem quot_mono {p P a A e E : ℝ} (hp : 0 ≤ p) (hP : p ≤ P) (ha : 0 ≤ a) (hA : a ≤ A) (he : 0 < e)
    (hE : e ≤ E) : p * a / E ^ 3 ≤ P * A / e ^ 3 := by
  have he3 : 0 < e ^ 3 := by positivity
  have hE0 : 0 < E := lt_of_lt_of_le he hE
  have hE3 : 0 < E ^ 3 := by positivity
  rw [div_le_div_iff₀ hE3 he3]
  have h1 : p * a ≤ P * A := mul_le_mul hP hA ha (hp.trans hP)
  have h2 : e ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ he.le hE 3
  exact mul_le_mul h1 h2 he3.le (mul_nonneg (hp.trans hP) (ha.trans hA))

theorem PLN_pos : (0:ℝ) ≤ ((PLN : ℕ) : ℝ) / 100000000000000000000 := by positivity

/-- the rounded quotient: `w1lo ≤ 2π q / d³ · U1 ≤ w1hi` -/
theorem w1lohi_sound (q1 q2 d1 d2 : ℤ) {q d : ℝ} (hq1 : (q1 : ℝ) / DZ ≤ q) (hq2 : q ≤ (q2 : ℝ) / DZ)
    (hd1 : (d1 : ℝ) / DZ ≤ d) (hd2 : d ≤ (d2 : ℝ) / DZ) (hneg : d2 < 0) :
    (w1lo q2 d1 d2 : ℝ) / U1 ≤ 2 * Real.pi * q / d ^ 3 ∧ 2 * Real.pi * q / d ^ 3 ≤ (w1hi q1 d1 d2 : ℝ) / U1 := by
  have hD := DZ_pos
  have hU1 : (0:ℝ) < U1 := by norm_num [U1]
  have hd2r : (d2 : ℝ) < 0 := by exact_mod_cast hneg
  have hd0 : d < 0 := lt_of_le_of_lt hd2 (div_neg_of_neg_of_pos hd2r hD)
  have hd12 : (d1 : ℝ) ≤ d2 := by
    have := hd1.trans hd2
    exact (div_le_div_iff_of_pos_right hD).mp this
  have hd1n : d1 < 0 := by have : (d1 : ℝ) < 0 := lt_of_le_of_lt hd12 hd2r; exact_mod_cast this
  set e := -d with he
  have he0 : 0 < e := by rw [he]; linarith
  have hfe : 2 * Real.pi * q / d ^ 3 = -(2 * Real.pi * q / e ^ 3) := by
    rw [he]; have : d ≠ 0 := hd0.ne; field_simp; (try ring)
  -- E2 = -d1 ≥ e, E1 = -d2 ≤ e, at scale DZ
  have hE2 : (((-d1).toNat : ℕ) : ℝ) = -(d1 : ℝ) := by
    have h := Int.toNat_of_nonneg (show 0 ≤ -d1 by omega); exact_mod_cast h
  have hE1 : (((-d2).toNat : ℕ) : ℝ) = -(d2 : ℝ) := by
    have h := Int.toNat_of_nonneg (show 0 ≤ -d2 by omega); exact_mod_cast h
  have heE2 : e ≤ (((-d1).toNat : ℕ) : ℝ) / DZ := by rw [hE2, neg_div]; linarith
  have heE1 : (((-d1).toNat : ℕ) : ℝ) / DZ > 0 := lt_of_lt_of_le he0 heE2
  have hE1e : (((-d2).toNat : ℕ) : ℝ) / DZ ≤ e := by rw [hE1, neg_div]; linarith
  have hE1p : 0 < (((-d2).toNat : ℕ) : ℝ) / DZ := by rw [hE1, neg_div]; have := div_neg_of_neg_of_pos hd2r hD; linarith
  have hPLN := PLN_le
  have hPUN := PUN_ge
  -- the rounded values as quotients
  have key_lo : ∀ (A E : ℕ), 0 < E → ((ndiv (2 * PLN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) : ℕ) : ℝ) / U1
      ≤ 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * ((A : ℝ) / DZ) / (((E : ℕ) : ℝ) / DZ) ^ 3 := by
    intro A E hE
    have h := ndiv_le (2 * PLN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) (by positivity)
    refine (div_le_div_of_nonneg_right h hU1.le).trans (le_of_eq ?_)
    have hEr : (0:ℝ) < E := by exact_mod_cast hE
    push_cast; field_simp; try ring
  have key_hi : ∀ (A E : ℕ), 0 < E → 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((A : ℝ) / DZ) / (((E : ℕ) : ℝ) / DZ) ^ 3
      ≤ ((ndivc (2 * PUN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) : ℕ) : ℝ) / U1 := by
    intro A E hE
    have h := le_ndivc (2 * PUN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) (by positivity)
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right h hU1.le)
    have hEr : (0:ℝ) < E := by exact_mod_cast hE
    push_cast; field_simp; try ring
  have hE2pos : 0 < (-d1).toNat := by omega
  have hE1pos : 0 < (-d2).toNat := by omega
  constructor
  · unfold w1lo
    rw [hfe]
    split_ifs with hq
    · -- q ≤ q2/DZ ≤ 0: the bound 2 p_lo |q2| / E2³ ≤ 2 π (-q) / e³
      have hA : ((((-q2).toNat : ℕ) : ℝ)) = -(q2 : ℝ) := by
        have h := Int.toNat_of_nonneg (show 0 ≤ -q2 by omega); exact_mod_cast h
      rw [Int.cast_natCast]
      refine (key_lo _ _ hE2pos).trans ?_
      have hm := quot_mono (p := ((PLN : ℕ) : ℝ) / 100000000000000000000) (a := (((-q2).toNat : ℕ) : ℝ) / DZ)
        (P := Real.pi) (A := -q) PLN_pos hPLN (by positivity) (by rw [hA, neg_div]; linarith) he0 heE2
      have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * (Real.pi * -q / e ^ 3) := by ring
      have e2 : 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * ((((-q2).toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3
          = 2 * ((((PLN : ℕ) : ℝ) / 100000000000000000000) * ((((-q2).toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
      rw [e1, e2]; linarith
    · -- q2 > 0: the bound -2 p_hi q2 / E1³ ≤ -2 π q / e³
      push_neg at hq
      have hA : (((q2.toNat : ℕ) : ℝ)) = (q2 : ℝ) := by
        have h := Int.toNat_of_nonneg hq.le; exact_mod_cast h
      have hk := key_hi q2.toNat (-d2).toNat hE1pos
      push_cast
      have hq2r : (0:ℝ) < (q2 : ℝ) / DZ := div_pos (by exact_mod_cast hq) hD
      rcases le_total q 0 with hq0 | hq0
      · have : 0 ≤ 2 * Real.pi * -q / e ^ 3 := by
          apply div_nonneg _ (by positivity); nlinarith [Real.pi_pos]
        have h2 : 0 ≤ 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3 := by
          rw [hA]; positivity
        have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * Real.pi * -q / e ^ 3 := by ring
        rw [e1, neg_div]; linarith
      · have hm := quot_mono (p := Real.pi) (a := q) (P := ((PUN : ℕ) : ℝ) / 100000000000000000000)
          (A := ((q2.toNat : ℕ) : ℝ) / DZ) Real.pi_pos.le hPUN hq0 (by rw [hA]; exact hq2) hE1p hE1e
        have e1 : 2 * Real.pi * q / e ^ 3 = 2 * (Real.pi * q / e ^ 3) := by ring
        have e2 : 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3
            = 2 * ((((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
        rw [e1, neg_div]; rw [e2] at hk; linarith
  · unfold w1hi
    rw [hfe]
    split_ifs with hq
    · -- 0 ≤ q1/DZ ≤ q: -(2π q / e³) ≤ -2 p_lo q1 / E2³
      have hA : (((q1.toNat : ℕ) : ℝ)) = (q1 : ℝ) := by
        have h := Int.toNat_of_nonneg hq; exact_mod_cast h
      have hk := key_lo q1.toNat (-d1).toNat hE2pos
      push_cast
      have hm := quot_mono (p := ((PLN : ℕ) : ℝ) / 100000000000000000000) (a := ((q1.toNat : ℕ) : ℝ) / DZ)
        (P := Real.pi) (A := q) PLN_pos hPLN (by positivity) (by rw [hA]; exact hq1) he0 heE2
      have e1 : 2 * Real.pi * q / e ^ 3 = 2 * (Real.pi * q / e ^ 3) := by ring
      have e2 : 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * (((q1.toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3
          = 2 * ((((PLN : ℕ) : ℝ) / 100000000000000000000) * (((q1.toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
      rw [e1, neg_div]; rw [e2] at hk; linarith
    · -- q1 < 0
      push_neg at hq
      have hA : ((((-q1).toNat : ℕ) : ℝ)) = -(q1 : ℝ) := by
        have h := Int.toNat_of_nonneg (show 0 ≤ -q1 by omega); exact_mod_cast h
      have hk := key_hi (-q1).toNat (-d2).toNat hE1pos
      rw [Int.cast_natCast]
      rcases le_total 0 q with hq0 | hq0
      · have : 0 ≤ 2 * Real.pi * q / e ^ 3 := by positivity
        have h2 : 0 ≤ 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3 := by
          positivity
        linarith
      · have hm := quot_mono (p := Real.pi) (a := -q) (P := ((PUN : ℕ) : ℝ) / 100000000000000000000)
          (A := (((-q1).toNat : ℕ) : ℝ) / DZ) Real.pi_pos.le hPUN (by linarith) (by rw [hA, neg_div]; linarith) hE1p hE1e
        have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * (Real.pi * -q / e ^ 3) := by ring
        have e2 : 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3
            = 2 * ((((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
        rw [e1]; rw [e2] at hk; linarith

/-! ### the derivative cell is sound -/

set_option maxHeartbeats 4000000 in
theorem cellD_sound (c : CellN) (hc : c.okD = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    kD x < 0 ∧ (c.W1LO : ℝ) / U1 ≤ w1 x ∧ w1 x ≤ (c.W1HI : ℝ) / U1 := by
  simp only [CellN.okD, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hcC, hD2⟩ := hc
  obtain ⟨⟨hC1, hC2⟩, ⟨hS1, hS2⟩, ⟨hB1, hB2⟩, hBB0⟩ := cellN_trig c hcC x hx1 hx2
  have hD0 := DZ_pos
  have hBI : ((c.BI.1 : ℤ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BI.2 : ℤ) : ℝ) / DZ := by
    simp only [CellN.BI, Int.cast_natCast]; exact ⟨hB1, hB2⟩
  have hBI0 : (0:ℤ) ≤ c.BI.1 := Int.natCast_nonneg _
  have hP := imulPP_sound GAMI c.BI (by decide) hBI0 gami_sound hBI
  have hP0 : (0:ℤ) ≤ c.PGI.1 := by
    show (0:ℤ) ≤ zfdiv (GAMI.1 * c.BI.1)
    exact zfdiv_nonneg (mul_nonneg (by decide) hBI0)
  have hT := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hN : ((c.NI.1 : ℤ) : ℝ) / DZ ≤ kN x ∧ kN x ≤ ((c.NI.2 : ℤ) : ℝ) / DZ :=
    isubZ_sound _ _ ⟨hC1, hC2⟩ hT
  have hG1S := imulP_sound G1I c.SXZ (by decide) g1i_sound ⟨hS1, hS2⟩
  have hPC := imulP_sound c.PGI c.CXZ hP0 hP ⟨hC1, hC2⟩
  have h00 : (((0, 0) : ℤ × ℤ).1 : ℝ) / DZ ≤ (0:ℝ) ∧ (0:ℝ) ≤ (((0, 0) : ℤ × ℤ).2 : ℝ) / DZ := by simp
  have hNb0 := isubZ_sound (0, 0) _ h00 (iaddZ_sound _ _ hG1S hPC)
  have hNb : ((c.NbI.1 : ℤ) : ℝ) / DZ ≤ kNb x ∧ kNb x ≤ ((c.NbI.2 : ℤ) : ℝ) / DZ := by
    have e : kNb x = 0 - ((1 + 2 * gam) * Real.sin (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)) := by
      unfold kNb; ring
    rw [e]; exact hNb0
  have hBB := imulPP_sound c.BI c.BI hBI0 hBI0 hBI hBI
  have h2BB := imulZZ_sound 2 _ hBB.1 hBB.2
  have h11 : ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).1 : ℝ) / DZ ≤ (1:ℝ) ∧ (1:ℝ) ≤ ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).2 : ℝ) / DZ := by
    simp only [Int.cast_natCast, div_self DZ_ne]; exact ⟨le_rfl, le_rfl⟩
  have hDD0 := isubZ_sound _ _ h11 h2BB
  have hDD : ((c.DI.1 : ℤ) : ℝ) / DZ ≤ kD x ∧ kD x ≤ ((c.DI.2 : ℤ) : ℝ) / DZ := by
    have e : kD x = 1 - ((2 : ℤ) : ℝ) * ((Real.pi * x) * (Real.pi * x)) := by unfold kD; push_cast; ring
    rw [e]; exact hDD0
  have hNbD := imulD_sound c.NbI c.DI hNb hDD
  have h4B := imulZZ_sound 4 c.BI hBI.1 hBI.2
  have h4B0 : (0:ℤ) ≤ (imulZZ 4 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 4 then ((4:ℤ) * c.BI.1, (4:ℤ) * c.BI.2) else ((4:ℤ) * c.BI.2, (4:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h4BN := imulP_sound (imulZZ 4 c.BI) c.NI h4B0 h4B hN
  have hM0 := iaddZ_sound _ _ hNbD h4BN
  have hM : ((c.MI.1 : ℤ) : ℝ) / DZ ≤ kM x ∧ kM x ≤ ((c.MI.2 : ℤ) : ℝ) / DZ := by
    have e : kM x = kNb x * kD x + ((4 : ℤ) : ℝ) * (Real.pi * x) * kN x := by unfold kM; push_cast; ring
    rw [e]; exact hM0
  have hQ := imulD_sound c.NI c.MI hN hM
  have hkD : kD x < 0 := by
    have : ((c.DI.2 : ℤ) : ℝ) < 0 := by exact_mod_cast hD2
    linarith [hDD.2, div_neg_of_neg_of_pos this hD0]
  have hw := w1lohi_sound c.QI.1 c.QI.2 c.DI.1 c.DI.2 hQ.1 hQ.2 hDD.1 hDD.2 hD2
  have e : w1 x = 2 * Real.pi * (kN x * kM x) / kD x ^ 3 := by unfold w1; ring
  rw [e]
  exact ⟨hkD, hw.1, hw.2⟩

end Zeta23Ext.Bridge.ThreePoint

end
-- MVTPROOFS-END
