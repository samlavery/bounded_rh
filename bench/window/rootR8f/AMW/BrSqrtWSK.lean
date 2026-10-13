import AMW.BrSqrtWS

/-! ###### AMW/BrSqrtWSK — the generic final κ step under the √-branch profile

Given a rational `H₀ ≤ H_W` and rational `B, c, s`, the bound `κ ≤ Phi_g n c m B` follows from a quotient of rationals:
* `Phi_g_ge_of_quot_sqrt` (`c (m − q) > τ`): `s ≥ 0`, `s² ≤ τ c (m − q)` and
  `κ ≤ (m H₀ − B (m − q)) / (m − (2s − τ))`;
* `Phi_g_ge_of_quot_lin` (`c (m − q) ≤ τ`): `κ ≤ (m H₀ − B (m − q)) / (m − c (m − q))`;
each under `c (m − q) < m`, a positive denominator and `m H₀ − B (m − q) ≥ 0` (`q = n − 1`, `τ = tauq n`).  The
instance-specific tail is then arithmetic on rationals. ###### -/

noncomputable section

namespace Zeta23Ext.BridgeW

/-- **the final κ step, √ branch**: `κ ≤ (m H₀ − B (m − q)) / (m − (2s − τ))` with `H₀ ≤ H_W`, `s ≥ 0`,
`s² ≤ τ c (m − q)`, `τ < c (m − q) < m` gives `κ ≤ Phi_g n c m B` -/
theorem Phi_g_ge_of_quot_sqrt {n : ℕ} {c B κ H₀ s : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (hH : H₀ ≤ AMW.HW) (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ tauq n * (c * ((m : ℝ) - ((n : ℝ) - 1))))
    (hA : tauq n < c * ((m : ℝ) - ((n : ℝ) - 1))) (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hnum : 0 ≤ (m : ℝ) * H₀ - B * ((m : ℝ) - ((n : ℝ) - 1)))
    (hden : 0 < (m : ℝ) - (2 * s - tauq n))
    (hκ : κ ≤ ((m : ℝ) * H₀ - B * ((m : ℝ) - ((n : ℝ) - 1))) / ((m : ℝ) - (2 * s - tauq n))) :
    κ ≤ Phi_g n c m B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := one_sub_gtau_div_pos hn hm hcm
  have hg := two_mul_sub_le_gtau hs hs2 hA
  set g := gtau (tauq n) (c * ((m : ℝ) - ((n : ℝ) - 1))) with hgdef
  set mq : ℝ := (m : ℝ) - ((n : ℝ) - 1) with hmq
  have hmg : 0 < (m : ℝ) - g := by
    have := hD; rw [sub_pos, div_lt_one hmpos] at this; linarith
  rw [le_div_iff₀ hden] at hκ
  have key : κ * ((m : ℝ) - g) ≤ (m : ℝ) * AMW.HW - B * mq := by
    have hHm : (m : ℝ) * H₀ ≤ (m : ℝ) * AMW.HW := mul_le_mul_of_nonneg_left hH hmpos.le
    rcases le_or_gt 0 κ with hk0 | hk0
    · have : κ * ((m : ℝ) - g) ≤ κ * ((m : ℝ) - (2 * s - tauq n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hk0
      linarith
    · have : κ * ((m : ℝ) - g) < 0 := mul_neg_of_neg_of_pos hk0 hmg
      linarith
  unfold Phi_g
  rw [← hgdef, ← hmq, le_div_iff₀ hD]
  have e1 : κ * (1 - g / m) = κ * ((m : ℝ) - g) / m := by field_simp
  have e2 : AMW.HW - B * mq / m = ((m : ℝ) * AMW.HW - B * mq) / m := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hmpos.le

/-- **the final κ step, linear branch**: `κ ≤ (m H₀ − B (m − q)) / (m − c (m − q))` with `H₀ ≤ H_W` and
`c (m − q) ≤ τ`, `c (m − q) < m` gives `κ ≤ Phi_g n c m B` -/
theorem Phi_g_ge_of_quot_lin {n : ℕ} {c B κ H₀ : ℝ} {m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (hH : H₀ ≤ AMW.HW) (hA : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ tauq n)
    (hcm : c * ((m : ℝ) - ((n : ℝ) - 1)) < m)
    (hnum : 0 ≤ (m : ℝ) * H₀ - B * ((m : ℝ) - ((n : ℝ) - 1)))
    (hκ : κ ≤ ((m : ℝ) * H₀ - B * ((m : ℝ) - ((n : ℝ) - 1))) / ((m : ℝ) - c * ((m : ℝ) - ((n : ℝ) - 1)))) :
    κ ≤ Phi_g n c m B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := one_sub_gtau_div_pos hn hm hcm
  set A : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hAdef
  set mq : ℝ := (m : ℝ) - ((n : ℝ) - 1) with hmq
  have hden : 0 < (m : ℝ) - A := by linarith
  rw [le_div_iff₀ hden] at hκ
  have key : κ * ((m : ℝ) - A) ≤ (m : ℝ) * AMW.HW - B * mq := by
    have hHm : (m : ℝ) * H₀ ≤ (m : ℝ) * AMW.HW := mul_le_mul_of_nonneg_left hH hmpos.le
    linarith
  unfold Phi_g
  rw [← hAdef, ← hmq, gtau_of_le hA]
  rw [gtau_of_le hA] at hD
  rw [le_div_iff₀ hD]
  have e1 : κ * (1 - A / m) = κ * ((m : ℝ) - A) / m := by field_simp
  have e2 : AMW.HW - B * mq / m = ((m : ℝ) * AMW.HW - B * mq) / m := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hmpos.le

end Zeta23Ext.BridgeW

end
