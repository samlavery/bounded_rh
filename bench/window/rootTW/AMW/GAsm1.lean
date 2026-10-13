import AMW.GNear

/-!
# AMW/GAsm1 — the harmonic terms in far-sum form (stage G)

For `j ≥ 1`, `s = sin πx`, `c = cos πx`: away from the pole (`x ≠ j`)
  `T_j = (−1)^j (s/π) m_j`,  `T1_j = (−1)^j ((c/π) m_j + (s/π²) m_j')`,
  `T2_j = (−1)^j (−(s/π) m_j + 2 (c/π²) m_j' + (s/π³) m_j'')`;
at the pole only the `x + j` half is expanded and `½ sinc^(n)(π(x − j))` is kept.
-/

noncomputable section

open Real

namespace AMW.G

theorem sin_pi_shift (x : ℝ) (j : ℕ) :
    Real.sin (π * (x - j)) = (-1) ^ j * Real.sin (π * x) ∧ Real.sin (π * (x + j)) = (-1) ^ j * Real.sin (π * x) := by
  constructor
  · rw [show π * (x - j) = π * x - j * π by ring, Real.sin_sub_nat_mul_pi]
  · rw [show π * (x + j) = π * x + j * π by ring, Real.sin_add_nat_mul_pi]

theorem cos_pi_shift (x : ℝ) (j : ℕ) :
    Real.cos (π * (x - j)) = (-1) ^ j * Real.cos (π * x) ∧ Real.cos (π * (x + j)) = (-1) ^ j * Real.cos (π * x) := by
  constructor
  · rw [show π * (x - j) = π * x - j * π by ring, Real.cos_sub_nat_mul_pi]
  · rw [show π * (x + j) = π * x + j * π by ring, Real.cos_add_nat_mul_pi]

/-- the quotient forms at `θ = πy`, `y ≠ 0` -/
theorem sinc_q {y : ℝ} (hy : y ≠ 0) : Real.sinc (π * y) = Real.sin (π * y) / (π * y) :=
  Real.sinc_of_ne_zero (mul_ne_zero Real.pi_pos.ne' hy)
theorem sc1_q {y : ℝ} (hy : y ≠ 0) :
    sc1 (π * y) = (π * y * Real.cos (π * y) - Real.sin (π * y)) / (π * y) ^ 2 := by
  rw [sc1, if_neg (mul_ne_zero Real.pi_pos.ne' hy)]
theorem sc2_q {y : ℝ} (hy : y ≠ 0) :
    sc2 (π * y) = (-(π * y) ^ 2 * Real.sin (π * y) - 2 * (π * y) * Real.cos (π * y) + 2 * Real.sin (π * y)) / (π * y) ^ 3 := by
  rw [sc2, if_neg (mul_ne_zero Real.pi_pos.ne' hy)]

variable {x : ℝ} {j : ℕ}

/-! ## Away from the pole -/

theorem T0_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
    (Real.sinc (π * (x - j)) + Real.sinc (π * (x + j))) / 2 = (-1) ^ j * (Real.sin (π * x) / π) * mf 0 j x := by
  have hπ := Real.pi_pos.ne'
  have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
    rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
  rw [sinc_q h1, sinc_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, mf, if_pos rfl]
  field_simp; ring

theorem T1_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
    (sc1 (π * (x - j)) + sc1 (π * (x + j))) / 2
      = (-1) ^ j * ((Real.cos (π * x) / π) * mf 0 j x + (Real.sin (π * x) / π ^ 2) * mf 1 j x) := by
  have hπ := Real.pi_pos.ne'
  have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
    rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
  rw [sc1_q h1, sc1_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, (cos_pi_shift x j).1, (cos_pi_shift x j).2]
  unfold mf; simp only [if_pos rfl, one_ne_zero, if_false, if_true]
  field_simp; ring

theorem T2_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
    (sc2 (π * (x - j)) + sc2 (π * (x + j))) / 2
      = (-1) ^ j * (-(Real.sin (π * x) / π) * mf 0 j x + 2 * (Real.cos (π * x) / π ^ 2) * mf 1 j x
          + (Real.sin (π * x) / π ^ 3) * mf 2 j x) := by
  have hπ := Real.pi_pos.ne'
  have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
    rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
  rw [sc2_q h1, sc2_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, (cos_pi_shift x j).1, (cos_pi_shift x j).2]
  unfold mf; simp only [if_pos rfl, one_ne_zero, if_false, if_true, show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num]
  field_simp; ring

/-! ## At the pole -/

theorem T0_near (h2 : x + j ≠ 0) :
    (Real.sinc (π * (x - j)) + Real.sinc (π * (x + j))) / 2
      = Real.sinc (π * (x - j)) / 2 + (-1) ^ j * (Real.sin (π * x) / π) * hf 0 j x := by
  have hπ := Real.pi_pos.ne'
  rw [sinc_q h2, (sin_pi_shift x j).2, hf, if_pos rfl]
  field_simp

theorem T1_near (h2 : x + j ≠ 0) :
    (sc1 (π * (x - j)) + sc1 (π * (x + j))) / 2
      = sc1 (π * (x - j)) / 2 + (-1) ^ j * ((Real.cos (π * x) / π) * hf 0 j x + (Real.sin (π * x) / π ^ 2) * hf 1 j x) := by
  have hπ := Real.pi_pos.ne'
  rw [sc1_q h2, (sin_pi_shift x j).2, (cos_pi_shift x j).2]
  unfold hf; simp only [if_pos rfl, one_ne_zero, if_false, if_true]
  field_simp; ring

theorem T2_near (h2 : x + j ≠ 0) :
    (sc2 (π * (x - j)) + sc2 (π * (x + j))) / 2
      = sc2 (π * (x - j)) / 2 + (-1) ^ j * (-(Real.sin (π * x) / π) * hf 0 j x
          + 2 * (Real.cos (π * x) / π ^ 2) * hf 1 j x + (Real.sin (π * x) / π ^ 3) * hf 2 j x) := by
  have hπ := Real.pi_pos.ne'
  rw [sc2_q h2, (sin_pi_shift x j).2, (cos_pi_shift x j).2]
  unfold hf; simp only [if_pos rfl, one_ne_zero, if_false, if_true, show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num]
  field_simp; ring

end AMW.G
