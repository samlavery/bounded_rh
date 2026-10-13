import Mathlib

/-! ###### AMW/DESOS — a cosine polynomial bounded below by a Fejér–Riesz certificate (am-cert)

For `C(θ) = y₀ + 2 Σ_{1 ≤ k < n} y_k cos(kθ)` and any real `a_0, …, a_{n−1}`, the square
`|Σ_j a_j e^{ijθ}|² = (Σ a_j cos jθ)² + (Σ a_j sin jθ)²` is the cosine polynomial with coefficients the
autocorrelations `c_k = Σ_j a_j a_{j+k}` (`sos_cos_eq`). Writing `C = |A|² + r` with `r_k = y_k − c_k`,
`C(θ) ≥ r₀ − 2 Σ_{k ≥ 1} |r_k|` for every `θ` (`cos_poly_ge`). With integer data (`y_k = Y_k/E`, `a_j = A_j/D`) the
bound is one integer inequality, checked by evaluation (`cos_poly_ge_int`). ###### -/

noncomputable section

open Finset Real

namespace AMW.DESOS

/-- the autocorrelation of `a` (taken over `j < n`) -/
def acor (a : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ j ∈ range n, a j * a (j + k)

/-- the squared modulus written out: `(Σ a_j cos jθ)² + (Σ a_j sin jθ)² = Σ_j Σ_l a_j a_l cos((j − l)θ)` -/
lemma sq_add_sq_eq_double (a : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    (∑ j ∈ range n, a j * cos (j * θ)) ^ 2 + (∑ j ∈ range n, a j * sin (j * θ)) ^ 2
      = ∑ j ∈ range n, ∑ l ∈ range n, a j * a l * cos (((j : ℝ) - l) * θ) := by
  rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [sub_mul, cos_sub]
  ring

/-- the upper triangle `l ≥ j` of the double sum, reindexed by `k = l − j` (the terms with `j + k ≥ n` vanish) -/
lemma upper_eq (a : ℕ → ℝ) (n : ℕ) (ha : ∀ j, n ≤ j → a j = 0) (θ : ℝ) (j : ℕ) :
    ∑ l ∈ range n, (if j ≤ l then a j * a l * cos (((j : ℝ) - l) * θ) else 0)
      = ∑ k ∈ range n, a j * a (j + k) * cos ((k : ℝ) * θ) := by
  rw [← sum_filter]
  have hfilt : (range n).filter (fun l => j ≤ l) = Ico j n := by
    ext l; simp [mem_Ico, and_comm]
  rw [hfilt, sum_Ico_eq_sum_range]
  have hcos : ∀ k : ℕ, a j * a (j + k) * cos (((j : ℝ) - ((j + k : ℕ) : ℝ)) * θ)
      = a j * a (j + k) * cos ((k : ℝ) * θ) := by
    intro k
    rw [show ((j : ℝ) - ((j + k : ℕ) : ℝ)) * θ = -((k : ℝ) * θ) by push_cast; ring, cos_neg]
  simp_rw [hcos]
  rcases le_or_gt j n with hjn | hjn
  · refine sum_subset (range_subset_range.mpr (Nat.sub_le n j)) fun k hk hk' => ?_
    have : n ≤ j + k := by simp only [mem_range, not_lt] at hk hk'; omega
    rw [ha _ this, mul_zero, zero_mul]
  · have h0 : n - j = 0 := by omega
    rw [h0, range_zero, sum_empty]
    refine (sum_eq_zero fun k _ => ?_).symm
    rw [ha j hjn.le, zero_mul, zero_mul]

/-- **the Fejér–Riesz identity**: `|Σ_{j<n} a_j e^{ijθ}|² = c₀ + 2 Σ_{1≤k<n} c_k cos kθ` (`a` vanishing from `n` on) -/
theorem sos_cos_eq (a : ℕ → ℝ) (n : ℕ) (ha : ∀ j, n ≤ j → a j = 0) (θ : ℝ) :
    (∑ j ∈ range n, a j * cos (j * θ)) ^ 2 + (∑ j ∈ range n, a j * sin (j * θ)) ^ 2
      = acor a n 0 + 2 * ∑ k ∈ Ico 1 n, acor a n k * cos (k * θ) := by
  rw [sq_add_sq_eq_double]
  set F : ℕ → ℕ → ℝ := fun j l => a j * a l * cos (((j : ℝ) - l) * θ) with hF
  have hsym : ∀ j l, F j l = F l j := by
    intro j l; simp only [hF]; rw [show ((l : ℝ) - j) * θ = -(((j : ℝ) - l) * θ) by ring, cos_neg]; ring
  -- split each pair by `j ≤ l` / `l < j`; the lower part is the upper part transposed, minus the diagonal
  have hsplit : ∀ j l, F j l = (if j ≤ l then F j l else 0) + (if l < j then F j l else 0) := by
    intro j l; by_cases h : j ≤ l
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (not_le.mp h), zero_add]
  have hlow : ∑ j ∈ range n, ∑ l ∈ range n, (if l < j then F j l else 0)
      = ∑ j ∈ range n, ∑ l ∈ range n, (if j ≤ l then F j l else 0) - ∑ j ∈ range n, F j j := by
    rw [sum_comm]
    have : ∀ j l, (if j < l then F l j else 0) = (if j ≤ l then F j l else 0) - (if j = l then F j l else 0) := by
      intro j l
      by_cases h1 : j = l
      · subst h1; simp
      · by_cases h2 : j < l
        · rw [if_pos h2, if_pos h2.le, if_neg h1, sub_zero, hsym]
        · rw [if_neg h2, if_neg (fun h => h2 (lt_of_le_of_ne h h1)), if_neg h1, sub_zero]
    simp_rw [this, sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [sum_ite_eq]; simp [hj]
  have hdiag : ∑ j ∈ range n, F j j = acor a n 0 := by
    unfold acor; refine sum_congr rfl fun j _ => ?_; simp [hF]
  have hupper : ∑ j ∈ range n, ∑ l ∈ range n, (if j ≤ l then F j l else 0)
      = ∑ k ∈ range n, acor a n k * cos (k * θ) := by
    simp only [hF]
    simp_rw [upper_eq a n ha θ]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    unfold acor; rw [sum_mul]
  have htot : ∑ j ∈ range n, ∑ l ∈ range n, F j l
      = 2 * ∑ k ∈ range n, acor a n k * cos (k * θ) - acor a n 0 := by
    rw [show ∑ j ∈ range n, ∑ l ∈ range n, F j l
        = ∑ j ∈ range n, ∑ l ∈ range n, ((if j ≤ l then F j l else 0) + (if l < j then F j l else 0)) from
      sum_congr rfl fun j _ => sum_congr rfl fun l _ => hsplit j l]
    simp only [sum_add_distrib]
    rw [hlow, hdiag, hupper]; ring
  simp only [hF] at htot
  rw [htot]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [acor]
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
    simp; ring

/-- **the certificate bound**: `C(θ) ≥ r₀ − 2 Σ_{1≤k<n} |r_k|` with `r_k = y_k − c_k` -/
theorem cos_poly_ge (y a : ℕ → ℝ) (n : ℕ) (ha : ∀ j, n ≤ j → a j = 0) (θ : ℝ) :
    (y 0 - acor a n 0) - 2 * ∑ k ∈ Ico 1 n, |y k - acor a n k|
      ≤ y 0 + 2 * ∑ k ∈ Ico 1 n, y k * cos (k * θ) := by
  have hsos := sos_cos_eq a n ha θ
  have hsq : 0 ≤ (∑ j ∈ range n, a j * cos (j * θ)) ^ 2 + (∑ j ∈ range n, a j * sin (j * θ)) ^ 2 := by positivity
  have hr : ∀ k ∈ Ico 1 n, -|y k - acor a n k| ≤ (y k - acor a n k) * cos (k * θ) := by
    intro k _
    have h1 := neg_one_le_cos (k * θ); have h2 := cos_le_one (k * θ)
    have := abs_mul (y k - acor a n k) (cos (k * θ))
    have h3 : |cos (k * θ)| ≤ 1 := abs_cos_le_one _
    have h4 : |(y k - acor a n k) * cos (k * θ)| ≤ |y k - acor a n k| := by
      rw [this]; exact mul_le_of_le_one_right (abs_nonneg _) h3
    linarith [neg_abs_le ((y k - acor a n k) * cos (k * θ))]
  have hsum := sum_le_sum hr
  rw [sum_neg_distrib] at hsum
  have hsplit : ∑ k ∈ Ico 1 n, y k * cos (k * θ)
      = ∑ k ∈ Ico 1 n, acor a n k * cos (k * θ) + ∑ k ∈ Ico 1 n, (y k - acor a n k) * cos (k * θ) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_; ring
  rw [hsplit]
  nlinarith [hsos, hsq, hsum]

/-- the residual coefficient in integers: `R_k = Y_k D² − E Σ_j A_j A_{j+k}` -/
def resZ (Y A : ℕ → ℤ) (E D n k : ℕ) : ℤ :=
  Y k * ((D : ℤ) ^ 2) - (E : ℤ) * ∑ j ∈ range n, A j * A (j + k)

/-- **the integer certificate**: `MZ ≤ R₀ − 2 Σ |R_k|` gives `C(θ) ≥ MZ/(E D²)` for every `θ`, where
`C(θ) = Y₀/E + 2 Σ_{1≤k<n} (Y_k/E) cos kθ` -/
theorem cos_poly_ge_int (Y A : ℕ → ℤ) (E D n : ℕ) (hE : 0 < E) (hD : 0 < D) (hA : ∀ j, n ≤ j → A j = 0)
    (MZ : ℤ) (h : MZ ≤ resZ Y A E D n 0 - 2 * ∑ k ∈ Ico 1 n, |resZ Y A E D n k|) (θ : ℝ) :
    (MZ : ℝ) / ((E : ℝ) * (D : ℝ) ^ 2)
      ≤ (Y 0 : ℝ) / E + 2 * ∑ k ∈ Ico 1 n, (Y k : ℝ) / E * cos (k * θ) := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hL : (0 : ℝ) < (E : ℝ) * (D : ℝ) ^ 2 := by positivity
  set a : ℕ → ℝ := fun j => (A j : ℝ) / D with ha_def
  have ha : ∀ j, n ≤ j → a j = 0 := fun j hj => by simp [ha_def, hA j hj]
  have key := cos_poly_ge (fun k => (Y k : ℝ) / E) a n ha θ
  -- the residuals in reals are the integer ones over `E D²`
  have hres : ∀ k, (Y k : ℝ) / E - acor a n k = (resZ Y A E D n k : ℝ) / ((E : ℝ) * (D : ℝ) ^ 2) := by
    intro k
    unfold acor resZ
    simp only [ha_def]
    push_cast
    rw [eq_div_iff hL.ne', sub_mul, Finset.sum_mul]
    have : ∀ j ∈ range n, (A j : ℝ) / D * ((A (j + k) : ℝ) / D) * ((E : ℝ) * (D : ℝ) ^ 2)
        = (E : ℝ) * ((A j : ℝ) * (A (j + k) : ℝ)) := by
      intro j _; field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    field_simp
  simp only [hres] at key
  have habs : ∀ k, |(resZ Y A E D n k : ℝ) / ((E : ℝ) * (D : ℝ) ^ 2)|
      = |(resZ Y A E D n k : ℝ)| / ((E : ℝ) * (D : ℝ) ^ 2) := fun k => by
    rw [abs_div, abs_of_pos hL]
  simp only [habs] at key
  have hcast : ((resZ Y A E D n 0 - 2 * ∑ k ∈ Ico 1 n, |resZ Y A E D n k| : ℤ) : ℝ)
      = (resZ Y A E D n 0 : ℝ) - 2 * ∑ k ∈ Ico 1 n, |(resZ Y A E D n k : ℝ)| := by push_cast; ring
  have hMZ : (MZ : ℝ) ≤ (resZ Y A E D n 0 : ℝ) - 2 * ∑ k ∈ Ico 1 n, |(resZ Y A E D n k : ℝ)| := by
    rw [← hcast]; exact_mod_cast h
  calc (MZ : ℝ) / ((E : ℝ) * (D : ℝ) ^ 2)
      ≤ ((resZ Y A E D n 0 : ℝ) - 2 * ∑ k ∈ Ico 1 n, |(resZ Y A E D n k : ℝ)|) / ((E : ℝ) * (D : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hMZ hL.le
    _ = (resZ Y A E D n 0 : ℝ) / ((E : ℝ) * (D : ℝ) ^ 2)
          - 2 * ∑ k ∈ Ico 1 n, |(resZ Y A E D n k : ℝ)| / ((E : ℝ) * (D : ℝ) ^ 2) := by
        rw [sub_div, mul_div_assoc, Finset.sum_div]
    _ ≤ _ := key

end AMW.DESOS

end
