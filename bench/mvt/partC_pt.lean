
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
