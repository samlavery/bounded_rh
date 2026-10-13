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
  have hP := imulD_sound GAMI c.BI gami_sound hBI
  have hT := imulD_sound c.PGI c.SXZ hP ⟨hS1, hS2⟩
  have hN : ((c.NI.1 : ℤ) : ℝ) / DZ ≤ kN x ∧ kN x ≤ ((c.NI.2 : ℤ) : ℝ) / DZ :=
    isubZ_sound _ _ ⟨hC1, hC2⟩ hT
  have hG1S := imulD_sound G1I c.SXZ g1i_sound ⟨hS1, hS2⟩
  have hPC := imulD_sound c.PGI c.CXZ hP ⟨hC1, hC2⟩
  have h00 : (((0, 0) : ℤ × ℤ).1 : ℝ) / DZ ≤ (0:ℝ) ∧ (0:ℝ) ≤ (((0, 0) : ℤ × ℤ).2 : ℝ) / DZ := by simp
  have hNb0 := isubZ_sound (0, 0) _ h00 (iaddZ_sound _ _ hG1S hPC)
  have hNb : ((c.NbI.1 : ℤ) : ℝ) / DZ ≤ kNb x ∧ kNb x ≤ ((c.NbI.2 : ℤ) : ℝ) / DZ := by
    have e : kNb x = 0 - ((1 + 2 * gam) * Real.sin (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)) := by
      unfold kNb; ring
    rw [e]; exact hNb0
  have hBB := imulD_sound c.BI c.BI hBI hBI
  have h2BB := imulZZ_sound 2 _ hBB.1 hBB.2
  have h11 : ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).1 : ℝ) / DZ ≤ (1:ℝ) ∧ (1:ℝ) ≤ ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).2 : ℝ) / DZ := by
    simp only [Int.cast_natCast, div_self DZ_ne]; exact ⟨le_rfl, le_rfl⟩
  have hDD0 := isubZ_sound _ _ h11 h2BB
  have hDD : ((c.DI.1 : ℤ) : ℝ) / DZ ≤ kD x ∧ kD x ≤ ((c.DI.2 : ℤ) : ℝ) / DZ := by
    have e : kD x = 1 - ((2 : ℤ) : ℝ) * ((Real.pi * x) * (Real.pi * x)) := by unfold kD; push_cast; ring
    rw [e]; exact hDD0
  have hNbD := imulD_sound c.NbI c.DI hNb hDD
  have h4B := imulZZ_sound 4 c.BI hBI.1 hBI.2
  have h4BN := imulD_sound (imulZZ 4 c.BI) c.NI h4B hN
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

/-! ### the derivative tables: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the function the derivative table of sign `sgn` bounds below: `w' + 2` (`true`) or `2 − w'` (`false`) -/
def fD (sgn : Bool) (x : ℝ) : ℝ := if sgn then w1 x + 2 else 2 - w1 x

/-- a nonzero `v / U1` bounds `fD sgn` below on the level-`l` cell `i`, which lies where `2 (π x)² > 1` -/
def CSD (sgn : Bool) (l i v : ℕ) : Prop :=
  v ≠ 0 → ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC →
    kD x < 0 ∧ (v : ℝ) / U1 ≤ fD sgn x

theorem forceB_eq (a : ℕ) (k : ℕ → Bool) : forceB a k = k a := by cases a <;> rfl

theorem CSD_zero (sgn : Bool) (l i : ℕ) : CSD sgn l i 0 := fun h => absurd rfl h

theorem U1_posR : (0:ℝ) < U1 := by norm_num [U1]

/-- a derivative cell claim that passes `cellOkD` is sound -/
theorem cellOkD_sound {sgn : Bool} {l i v : ℕ} (h : cellOkD sgn l i v = true) : CSD sgn l i v := by
  unfold cellOkD at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
          (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hok, hvb⟩ := h'
      have hK' : (i + 1) * 2 ^ l < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
      have hLN : (cellAt l i).LN = i * 2 ^ l := by
        simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
        simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      intro _ x h1 h2
      obtain ⟨hk, hlo, hhi⟩ := cellD_sound (cellAt l i) hok x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
      refine ⟨hk, ?_⟩
      have hU1 := U1_posR
      have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
      cases sgn
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((cellAt l i).W1HI : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte, Bool.false_eq_true]
        rw [div_le_iff₀ hU1]
        have := (le_div_iff₀ hU1).mp hhi
        rw [eK] at hvr
        nlinarith
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((cellAt l i).W1LO : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte]
        rw [div_le_iff₀ hU1]
        have := (div_le_iff₀ hU1).mp hlo
        rw [eK] at hvr
        nlinarith
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; exact CSD_zero sgn l i


/-! ### the point table -/

/-- a point claim that passes `ptOk` is sound -/
theorem ptOk_sound {x v : ℕ} (h : ptOk x v = true) : (v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) := by
  unfold ptOk at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add x 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v = true := h
      simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨hc, hW⟩ := h'
      have hK' : x < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq] at hK; omega
      have hLN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).LN = x := by
        simp only [CellN.LN, Nat.add_eq, Nat.mul_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).UN = x := by
        simp only [CellN.UN, Nat.add_eq, Nat.mul_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      have := cellN_soundZ' ⟨Nat.add (Nat.mul x KB) x, 0⟩ (Nat.mul v 1000) hc hW ((x : ℝ) / SC)
        (by rw [hLN]) (by rw [hUN])
      have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
        simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
      rw [e] at this; exact this
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _

/-- the point table's soundness: every read bounds `w` at its point -/
def PTSound (pb : ℕ → ℕ) : Prop := ∀ x : ℕ, (ptv pb x : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)

theorem ptv_sound {pb : ℕ → ℕ} (hb : ∀ j < 512, ptBlockOk (pb j) j = true) : PTSound pb := by
  intro x
  unfold ptv
  cases h5 : Nat.ble 524288 x
  · have hx : x < 524288 := by
      have : ¬ 524288 ≤ x := by rw [← Nat.ble_eq, h5]; decide
      omega
    show ((forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0) : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
    simp only [forceR_eq]
    set j := Nat.shiftRight x 10 with hj
    have hj' : j = x / 1024 := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; (try rfl)
    have hj512 : j < 512 := by rw [hj']; omega
    have hB := hb j hj512
    set X := pb j
    have hr : Nat.land X 15 = X % 16 := by
      rw [Nat.land_eq, show (15:ℕ) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have hx1023 : Nat.land x 1023 = x % 1024 := by
      rw [Nat.land_eq, show (1023:ℕ) = 2 ^ 10 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [hr, hx1023]
    set r := X % 16
    cases hal : Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 r) 1)) 0
    · show ((0 : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _
    · show ((fld (Nat.shiftRight X 4) (Nat.shiftRight (x % 1024) r) : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      have hal' : x % 2 ^ r = 0 := by
        have h0 := hal
        rw [Nat.beq_eq, Nat.land_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul,
          Nat.and_two_pow_sub_one_eq_mod] at h0
        exact h0
      cases hX : Nat.beq X 0
      · have hB' : ptBlockOkX X j = true := by
          unfold ptBlockOk at hB; rw [hX] at hB; exact hB
        unfold ptBlockOkX at hB'
        rw [hr, Bool.and_eq_true, Nat.ble_eq] at hB'
        obtain ⟨hr10, hall⟩ := hB'
        have hall' := allBelow_spec hall
        set t := Nat.shiftRight (x % 1024) r with ht
        have ht' : t = x % 1024 / 2 ^ r := by rw [ht, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ r * 2 ^ (10 - r) = 1024 := by rw [← pow_add, show r + (10 - r) = 10 by omega]; norm_num
        have htlt : t < 2 ^ (10 - r) := by
          rw [ht', Nat.div_lt_iff_lt_mul (by positivity)]
          have := Nat.mod_lt x (show 0 < 1024 by norm_num)
          rw [mul_comm] at hpow; omega
        have hpt := ptOk_sound (hall' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq]; exact htlt))
        have hxe : Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r) = x := by
          simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
          rw [hj', ht']
          have hdvd : 2 ^ r ∣ 1024 := ⟨2 ^ (10 - r), hpow.symm⟩
          have hm : x % 1024 % 2 ^ r = 0 := by rw [Nat.mod_mod_of_dvd _ hdvd]; exact hal'
          have e1 := Nat.div_add_mod (x % 1024) (2 ^ r)
          have e2 := Nat.div_add_mod x 1024
          rw [hm, Nat.add_zero] at e1
          calc x / 1024 * 2 ^ 10 + x % 1024 / 2 ^ r * 2 ^ r
              = 1024 * (x / 1024) + 2 ^ r * (x % 1024 / 2 ^ r) := by ring
            _ = x := by rw [e1, e2]
        rw [hxe] at hpt
        simpa only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] using hpt
      · have : X = 0 := by rw [← Nat.beq_eq, hX]
        rw [this, show Nat.shiftRight 0 4 = 0 from rfl, fld_zero]
        simp only [Nat.cast_zero, zero_div]
        exact wfun_nonneg _
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ### the pyramid of pairs: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- a pair `v` at the point `x`: each nonzero half bounds its function below (`w' + 2`, `2 − w'`), at a point
where `2 (π x)² > 1` -/
def PS (v : ℕ) (x : ℝ) : Prop :=
  (lo32 v ≠ 0 → kD x < 0 ∧ (lo32 v : ℝ) / U1 ≤ fD true x) ∧
    (hi32 v ≠ 0 → kD x < 0 ∧ (hi32 v : ℝ) / U1 ≤ fD false x)

theorem lo32_eq (v : ℕ) : lo32 v = v % 2 ^ 32 := by
  unfold lo32
  rw [Nat.land_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem hi32_eq (v : ℕ) : hi32 v = v / 2 ^ 32 := by
  unfold hi32
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem pmin_lo (a b : ℕ) : lo32 (pmin a b) = min (lo32 a) (lo32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, lo32_eq (min _ _ + _),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha)]

theorem pmin_hi (a b : ℕ) : hi32 (pmin a b) = min (hi32 a) (hi32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hi32_eq (min _ _ + _),
    Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha), Nat.zero_add]

theorem PS_zero (x : ℝ) : PS 0 x := ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩

theorem PS_mono {v v' : ℕ} {x : ℝ} (h : ple v' v = true) (hv : PS v x) : PS v' x := by
  unfold ple at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := hv.1 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h1) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := hv.2 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) U1_posR.le) hb⟩

theorem PS_pmin_left {a b : ℕ} {x : ℝ} (h : PS a x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩

theorem PS_pmin_right {a b : ℕ} {x : ℝ} (h : PS b x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩

/-- the pair `v` holds on the level-`l` cell `i` -/
def CS2 (l i v : ℕ) : Prop :=
  ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → PS v x

theorem CS2_zero (l i : ℕ) : CS2 l i 0 := fun x _ _ => PS_zero x

theorem CS2_mono {l i v v' : ℕ} (hv : ple v' v = true) (h : CS2 l i v) : CS2 l i v' :=
  fun x h1 h2 => PS_mono hv (h x h1 h2)

theorem CS2_min {l i a b : ℕ} (ha : CS2 l (2 * i) a) (hb : CS2 l (2 * i + 1) b) : CS2 (l + 1) i (pmin a b) := by
  intro x h1 h2
  have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
  · exact PS_pmin_left (ha x (by rw [e1]; exact h1) hx)
  · exact PS_pmin_right (hb x hx (by rw [e2]; exact h2))

theorem CS2_anc {l m i v : ℕ} (h : CS2 (l + m) (i / 2 ^ m) v) : CS2 l i v := by
  intro x h1 h2
  have hp : 0 < 2 ^ m := by positivity
  apply h x
  · refine le_trans (castdiv_le ?_) h1
    calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
      _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
  · refine le_trans h2 (castdiv_le ?_)
    have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
      have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
    calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
      _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring

/-- a pair claim that passes `cellOk2` is sound -/
theorem cellOk2_sound {l i v : ℕ} (h : cellOk2 l i v = true) : CS2 l i v := by
  unfold cellOk2 at h
  rw [Bool.and_eq_true] at h
  have hP := cellOkD_sound h.1
  have hM := cellOkD_sound h.2
  intro x h1 h2
  exact ⟨fun h0 => hP h0 x h1 h2, fun h0 => hM h0 x h1 h2⟩

theorem fld2_zero (i : ℕ) : fld2 0 i = 0 := by
  simp [fld2]

def BlockSound2 (X j : ℕ) : Prop :=
  X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS2 (10 - d) (j * 2 ^ d + t) (fld2 (X / 32) (2 ^ d - 1 + t))

theorem blockOk2X_sound {X j : ℕ} (h : blockOk2X X j = true) : BlockSound2 X j := by
  have hr : Nat.land X 31 = X % 32 := by
    rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  unfold blockOk2X at h
  simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h10, hfin⟩, hint⟩ := h
  refine ⟨h10, ?_⟩
  set D := Nat.sub 10 (X % 32) with hD
  have hD' : D = 10 - X % 32 := rfl
  have hfin' := allBelow_spec hfin
  have hint' := allBelow_spec hint
  -- downward induction on the depth
  suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS2 (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld2 (X / 32) (2 ^ (D - e) - 1 + t)) by
    intro d hd t ht
    have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
    rwa [Nat.sub_sub_self (by omega)] at this
  intro e
  induction e with
  | zero =>
    intro _ t ht
    have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
    simp only [Nat.sub_zero]
    have hc := cellOk2_sound this
    simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
    have e10 : 10 - D = X % 32 := by omega
    rw [e10]; exact hc
  | succ e ih =>
    intro he t ht
    set d := D - (e + 1) with hd
    have hdD : d < D := by omega
    have hde : D - e = d + 1 := by omega
    have hc := hint' d hdD
    have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
    have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
    have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
    rw [hde] at h0 h1
    have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
    have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
    rw [e0] at h0; rw [e1] at h1
    have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
    have hm := CS2_min h0 h1
    rw [hlev] at hm
    exact CS2_mono hct hm

theorem blockOk2_sound {X j : ℕ} (h : blockOk2 X j = true) : BlockSound2 X j := by
  unfold blockOk2 at h
  cases hX : Nat.beq X 0
  · rw [hX] at h
    exact blockOk2X_sound h
  · have : X = 0 := by rw [← Nat.beq_eq, hX]
    subst this
    refine ⟨by norm_num, fun d _ t _ => ?_⟩
    simp only [Nat.zero_div, fld2_zero]; exact CS2_zero _ _

theorem topv2_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv2 top bk 10 i = fld2 (bk i / 32) 0 := by
  unfold topv2
  rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem topv2_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
    topv2 top bk l i = fld2 top (2 ^ (19 - l) + i) := by
  unfold topv2
  have : Nat.beq l 10 = false := by
    cases h : Nat.beq l 10
    · rfl
    · exact absurd (by rw [← Nat.beq_eq, h]) hl
  rw [this]
  simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]

/-- the top levels and the blocks' own entries bound their cells -/
theorem top2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS2 (10 + e) i (topv2 top bk (10 + e) i) := by
  have ht' := allFrom_spec ht
  intro e
  induction e with
  | zero =>
    intro _ i hi
    rw [Nat.add_zero, topv2_ten]
    have hB := blockOk2_sound (hb i (by simpa using hi))
    have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
    simpa using this
  | succ e ih =>
    intro he i hi
    have hl := ht' e (by omega) |> allBelow_spec
    have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
    have e1 : 11 + e - 1 = 10 + e := by omega
    rw [e1] at hle
    have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have hm := CS2_min h0 h1
    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
    rw [topv2_top top bk (by omega)]
    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
    exact CS2_mono hle hm

/-- every entry the oracle reads bounds its cell -/
theorem entry2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS2 l i (entry2 top bk l i) := by
  unfold entry2
  cases h11 : Nat.ble 11 l
  · -- a block level
    have hl : l ≤ 10 := by
      have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
      omega
    show CS2 l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
    rw [forceR_eq]
    set j := Nat.shiftRight i (Nat.sub 10 l) with hj
    have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
    have hj512 : j < 512 := by
      rw [hj']
      have hi' := hi (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
      rwa [show 9 + (10 - l) = 19 - l by omega]
    have hB := blockOk2_sound (hb j hj512)
    set X := bk j
    unfold entB2
    have hr : Nat.land X 31 = X % 32 := by
      rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    simp only [hr]
    set r := X % 32
    have hr10 : r ≤ 10 := hB.1
    -- kk = max l r
    have hkk : Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r) = max l r := by
      cases hc : Nat.ble l r
      · have : ¬ l ≤ r := by rw [← Nat.ble_eq, hc]; decide
        show l = max l r; omega
      · have : l ≤ r := by rw [← Nat.ble_eq, hc]
        show r = max l r; omega
    simp only [hkk]
    set kk := max l r with hkkdef
    have hkk10 : kk ≤ 10 := by omega
    have hlkk : l ≤ kk := le_max_left _ _
    set d := Nat.sub 10 kk with hd
    have hd' : d = 10 - kk := rfl
    set q := i / 2 ^ (kk - l) with hq
    have hqj : q / 2 ^ d = j := by
      rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
      congr 2; omega
    have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
    have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
        = 2 ^ d - 1 + q % 2 ^ d := by
      simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      rw [← hq]
      have := Nat.div_add_mod' q (2 ^ d)
      rw [hqj] at this
      congr 1; omega
    have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    rw [hidx, hY]
    have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
    have e1 : j * 2 ^ d + q % 2 ^ d = q := by
      have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
    rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
    exact CS2_anc hcs
  · cases h20 : Nat.ble 20 l
    · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
      have hl' : l ≤ 19 := by
        have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
        omega
      show CS2 l i (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      have := top2_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
      rw [show 10 + (l - 10) = l by omega, topv2_top top bk (by omega)] at this
      simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
    · exact CS2_zero l i

theorem dcov2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ fuel g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      PS (dcov2 top bk k ib fuel g) x := by
  intro fuel
  induction fuel with
  | zero =>
    intro g _ x _ _
    exact PS_zero x
  | succ fuel ih =>
    intro g hg x h1 h2
    show PS (let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry2 top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (pmin v (dcov2 top bk k ib fuel g')) (Nat.ble g' ib)) x
    simp only [forceR_eq]
    set t := alignK4 g ib
    set h := Nat.shiftRight g t with hh
    have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
    have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    -- the block read covers [g, g') at level k
    have hcell : CS2 (Nat.add k t) h (entry2 top bk (Nat.add k t) h) := by
      apply entry2_sound hb ht
      intro hkt
      have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
      have hgib : g * 2 ^ k < 2 ^ 19 := by
        have := hk hk'
        calc g * 2 ^ k < (ib + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ ≤ 2 ^ 19 := this
      rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
      have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
        rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
      by_contra hcon
      push_neg at hcon
      have := Nat.mul_le_mul_right (2 ^ k) hcon
      rw [e] at this; omega
    have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
        PS (entry2 top bk (Nat.add k t) h) y := by
      intro y hy1 hy2
      apply hcell y
      · refine le_trans (castdiv_le ?_) hy1
        rw [hh', Nat.add_eq, pow_add]
        calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
          _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
      · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
        rw [hg'', Nat.add_eq, pow_add]; ring
    cases hc : Nat.ble g' ib
    · -- the block reaches past ib
      have hgt : ib + 1 ≤ g' := by
        have : ¬ g' ≤ ib := by rw [← Nat.ble_eq, hc]; decide
        omega
      exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
    · have hle : g' ≤ ib := by rw [← Nat.ble_eq, hc]
      show PS (pmin _ _) x
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact PS_pmin_left (hcellx x h1 hx)
      · exact PS_pmin_right (ih g' hle x hx h2)

/-- the oracle's soundness: what a verified table certifies -/
def LBSound2 (top : ℕ) (bk : ℕ → ℕ) : Prop :=
  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → PS (lb2 top bk lo hi) x

theorem lb2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
    LBSound2 top bk := by
  intro lo hi x h1 h2
  unfold lb2
  cases hlo : Nat.ble hi lo
  · cases hhi : Nat.ble 524289 hi
    · have hlh : lo < hi := by
        have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
        omega
      have hhi' : hi ≤ 524288 := by
        have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
        omega
      show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5)))) x
      set k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
      have hp : 0 < 2 ^ k := by positivity
      apply dcov2_sound hb ht k ((hi - 1) / 2 ^ k)
      · intro hk
        have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
          rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
        calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
          _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
      · exact Nat.div_le_div_right (by omega)
      · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
      · refine le_trans h2 (castdiv_le ?_)
        have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
        have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
        rw [e]
        generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
        generalize 2 ^ k = P at h5 ⊢
        omega
    · exact PS_zero x
  · exact PS_zero x


theorem blocks2_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk2 (bk j) j) = true) :
    ∀ j < 512, blockOk2 (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ### the mean-value step for one pair term, and the per-gap bound -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the mean value theorem on a pair-sum interval read with nonzero derivative bounds `p`, `q`: the increment of `w`
between two points of `[lo, hi] / SC` is `d` times the increment of the argument, `p − 2 U1 ≤ U1 d ≤ 2 U1 − q` -/
theorem mvt_pair {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSound2 tD bD) (lo hi : ℕ) (hp : 1 ≤ lo32 (lb2 tD bD lo hi))
    (hq : 1 ≤ hi32 (lb2 tD bD lo hi)) (y z : ℝ)
    (hy1 : (lo : ℝ) / SC ≤ y) (hy2 : y ≤ (hi : ℝ) / SC) (hz1 : (lo : ℝ) / SC ≤ z) (hz2 : z ≤ (hi : ℝ) / SC) :
    ∃ d : ℝ, wfun z = wfun y + d * (z - y) ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * d ∧
      1000000000 * d ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
  have hp0 : lo32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hq0 : hi32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hb : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC →
      kD ξ < 0 ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * w1 ξ ∧
        1000000000 * w1 ξ ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
    intro ξ h1 h2
    obtain ⟨hk, hPb⟩ := (hD lo hi ξ h1 h2).1 hp0
    obtain ⟨_, hMb⟩ := (hD lo hi ξ h1 h2).2 hq0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPb hMb
    rw [div_le_iff₀ U1_posR] at hPb hMb
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    rw [eU] at hPb hMb
    exact ⟨hk, by linarith, by linarith⟩
  have hderiv : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC → HasDerivAt wfun (w1 ξ) ξ :=
    fun ξ h1 h2 => hasDerivAt_wfun ξ (hb ξ h1 h2).1.ne
  rcases lt_trichotomy y z with hyz | hyz | hyz
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hy1.trans hξ.1) (hξ.2.trans hz2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring
  · subst hyz
    obtain ⟨_, h1, h2⟩ := hb y hy1 hy2
    exact ⟨w1 y, by ring, h1, h2⟩
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hz1.trans hξ.1) (hξ.2.trans hy2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring

/-- one gap's term of the mean-value expansion: `e ∈ [−lo, hi]`, `U1 E ≤ P`, `−U1 E ≤ N` -/
theorem mterm {e E lo hi P N : ℝ} (he1 : -lo ≤ e) (he2 : e ≤ hi) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hP : 1000000000 * E ≤ P) (hN : -(1000000000 * E) ≤ N) (hP0 : 0 ≤ P) (hN0 : 0 ≤ N) :
    -(lo * P) - hi * N ≤ 1000000000 * (e * E) := by
  rcases le_total 0 e with h | h
  · have h1 := mul_le_mul_of_nonneg_left (show -N ≤ 1000000000 * E by linarith) h
    have h2 := mul_le_mul_of_nonneg_right he2 hN0
    nlinarith [mul_nonneg hlo hP0]
  · have h1 := mul_le_mul_of_nonpos_left hP h
    have h2 := mul_le_mul_of_nonneg_right he1 hP0
    nlinarith [mul_nonneg hhi hN0]

/-- truncated subtraction bounds the real difference from above -/
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have := (Nat.cast_le (α := ℝ)).mpr h
    simp only [Nat.cast_zero]; linarith

theorem natsub_nonneg (a b : ℕ) : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _

theorem ptblocks_of {pb : ℕ → ℕ} (h : allFrom 0 512 (fun j => ptBlockOk (pb j) j) = true) :
    ∀ j < 512, ptBlockOk (pb j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
-- MVTPROOFS-END
