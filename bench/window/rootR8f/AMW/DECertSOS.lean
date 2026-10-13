import AMW.DESOS
import AMW.DEDefs

/-! ###### AMW/DECertSOS — the Fejér–Riesz certificate for a piecewise-linear certificate `ĝ` (am-cert)

For `c : PLCert`, `certC c` is the cosine polynomial of `AMW.DESOS.cos_poly_ge_int` with `Y := c.Y`, `E := c.E`,
`n := c.n`, so an integer certificate (a factor `A/D` and a margin `MZ ≥ 0` with `MZ ≤ R₀ − 2 Σ |R_k|`) gives
`CertGNonneg c` (`certG_of_int`). The scalar `ĝ(0) ≤ g(0)`, i.e. `y₀ ≤ Dk · (y₀ + 2 Σ_{k≥1} y_k)`, is one integer
inequality (`ghat0_le_g0_of_int`). ###### -/

noncomputable section

open Finset Real

namespace AMW.DE

/-- **`certC c ≥ 0` on ℝ from an integer Fejér–Riesz certificate** -/
theorem certG_of_int (c : PLCert) (A : ℕ → ℤ) (D : ℕ) (hE : 0 < c.E) (hD : 0 < D)
    (hA : ∀ j, c.n ≤ j → A j = 0) (MZ : ℤ) (hMZ : 0 ≤ MZ)
    (h : MZ ≤ AMW.DESOS.resZ c.Y A c.E D c.n 0 - 2 * ∑ k ∈ Ico 1 c.n, |AMW.DESOS.resZ c.Y A c.E D c.n k|) :
    CertGNonneg c := by
  intro θ
  have key := AMW.DESOS.cos_poly_ge_int c.Y A c.E D c.n hE hD hA MZ h θ
  have h0 : (0 : ℝ) ≤ (MZ : ℝ) / ((c.E : ℝ) * (D : ℝ) ^ 2) := by
    have : (0 : ℝ) ≤ MZ := by exact_mod_cast hMZ
    positivity
  exact h0.trans key

/-- **`ĝ(0) ≤ g(0)`** from the integer inequality `DkInv · Y₀ ≤ Y₀ + 2 Σ_{1≤k<n} Y_k` -/
theorem ghat0_le_g0_of_int (c : PLCert) (hE : 0 < c.E) (hDk : 0 < c.DkInv)
    (h : c.Y 0 * (c.DkInv : ℤ) ≤ c.Y 0 + 2 * ∑ k ∈ Ico 1 c.n, c.Y k) :
    c.y 0 ≤ c.dk * certC c 0 := by
  have hE' : (0 : ℝ) < c.E := by exact_mod_cast hE
  have hDk' : (0 : ℝ) < c.DkInv := by exact_mod_cast hDk
  have hC : certC c 0 = ((c.Y 0 : ℝ) + 2 * ∑ k ∈ Ico 1 c.n, (c.Y k : ℝ)) / c.E := by
    unfold certC PLCert.y
    simp only [mul_zero, cos_zero, mul_one]
    rw [add_div, mul_div_assoc, Finset.sum_div]
  rw [hC]
  unfold PLCert.y PLCert.dk
  have hR : ((c.Y 0 : ℝ) * (c.DkInv : ℝ)) ≤ (c.Y 0 : ℝ) + 2 * ∑ k ∈ Ico 1 c.n, (c.Y k : ℝ) := by
    exact_mod_cast h
  rw [div_le_iff₀ hE', one_div, inv_mul_eq_div, div_mul_eq_mul_div, div_mul_cancel₀ _ hE'.ne',
    le_div_iff₀ hDk']
  linarith

/-- **the exact slack `ĝ(0) − g(0)`** (`= y₀ − Dk · certC c 0`) from one integer identity -/
theorem ghat0_sub_g0_of_int (c : PLCert) (hE : 0 < c.E) (hDk : 0 < c.DkInv) (S : ℤ)
    (h : c.Y 0 * (c.DkInv : ℤ) - (c.Y 0 + 2 * ∑ k ∈ Ico 1 c.n, c.Y k) = S) :
    c.y 0 - c.dk * certC c 0 = (S : ℝ) / ((c.E : ℝ) * (c.DkInv : ℝ)) := by
  have hE' : (0 : ℝ) < c.E := by exact_mod_cast hE
  have hDk' : (0 : ℝ) < c.DkInv := by exact_mod_cast hDk
  have hC : certC c 0 = ((c.Y 0 : ℝ) + 2 * ∑ k ∈ Ico 1 c.n, (c.Y k : ℝ)) / c.E := by
    unfold certC PLCert.y
    simp only [mul_zero, cos_zero, mul_one]
    rw [add_div, mul_div_assoc, Finset.sum_div]
  have hR : (c.Y 0 : ℝ) * (c.DkInv : ℝ) - ((c.Y 0 : ℝ) + 2 * ∑ k ∈ Ico 1 c.n, (c.Y k : ℝ)) = S := by
    exact_mod_cast h
  rw [hC]
  unfold PLCert.y PLCert.dk
  rw [← hR]
  field_simp

end AMW.DE

end
