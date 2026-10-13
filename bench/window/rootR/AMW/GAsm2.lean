import AMW.GAsm1

/-!
# AMW/GAsm2 — the sums over the twelve harmonic terms (stage G)

`Σ_j c_j T_j = (s/π) F₀ + near₀`, `Σ_j c_j T1_j = (c/π) F₀ + (s/π²) F₁ + near₁`,
`Σ_j c_j T2_j = −(s/π) F₀ + 2 (c/π²) F₁ + (s/π³) F₂ + near₂`, with `F_n = fsum n k x CE / 10⁹` and
`near_n = c_{j₀}/2 · sinc^(n)(π(x − j₀))` when `2 j₀ = k`, else `0`.
-/

noncomputable section

open Real

namespace AMW.G

theorem fsum_CE (n k : ℕ) (x : ℝ) :
    fsum n k x CE = E9 * ∑ m ∈ Finset.range 12, (-1) ^ (m + 1) * (cAM (m + 1) : ℝ) * fv n k (m + 1) x := by
  simp only [fsum, CE, Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn, E9]
  push_cast
  ring

/-- `(sign, |c_j| · 10⁹)` reads `c_j` -/
theorem CJ_val {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 12) :
    (if (CJ j).2 then (-1 : ℝ) else 1) * ((CJ j).1 : ℝ) / E9 = (cAM j : ℝ) := by
  interval_cases j <;> norm_num [CJ, cAM, cAMn, E9]

/-- the near term selected by the anchor -/
def nsel (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range 12, if 2 * (m + 1) = k then (cAM (m + 1) : ℝ) * f (m + 1) / 2 else 0

theorem nsel_eq (k : ℕ) (f : ℕ → ℝ) :
    nsel k f = if (k % 2 = 0 ∧ 2 ≤ k ∧ k ≤ 24) then (cAM (k / 2) : ℝ) * f (k / 2) / 2 else 0 := by
  unfold nsel
  split_ifs with h
  · obtain ⟨h0, h1, h2⟩ := h
    rw [Finset.sum_eq_single (k / 2 - 1)]
    · rw [if_pos (by omega), show k / 2 - 1 + 1 = k / 2 by omega]
    · intro m _ hm; rw [if_neg]; omega
    · intro hm; exfalso; apply hm; rw [Finset.mem_range]; omega
  · apply Finset.sum_eq_zero; intro m hm; rw [Finset.mem_range] at hm; rw [if_neg]; omega

section sums
variable {k : ℕ} {x : ℝ} (hx : 0 < x) (hsep : ∀ j : ℕ, 1 ≤ j → 2 * j ≠ k → x ≠ j)
include hx hsep

theorem per_j_sep (m : ℕ) (hm : 2 * (m + 1) ≠ k) : x - ((m + 1 : ℕ) : ℝ) ≠ 0 :=
  sub_ne_zero.mpr (hsep (m + 1) (by omega) hm)

theorem per_j_pos (m : ℕ) : x + ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity

theorem sum_T0 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * Tj n x
    = (Real.sin (π * x) / π) * (fsum 0 k x CE / E9) + nsel k (fun j => Real.sinc (π * (x - j))) := by
  rw [fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), Finset.mul_sum, nsel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : Tj m x = (Real.sinc (π * (x - ((m + 1 : ℕ) : ℝ))) + Real.sinc (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
    unfold Tj; push_cast; ring_nf
  rw [e]
  by_cases hm : 2 * (m + 1) = k
  · rw [T0_near (per_j_pos hx hsep m), fv, if_pos hm, if_pos hm]; push_cast; ring
  · rw [T0_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, if_neg hm, if_neg hm]; push_cast; ring

theorem sum_T1 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T1j n x
    = (Real.cos (π * x) / π) * (fsum 0 k x CE / E9) + (Real.sin (π * x) / π ^ 2) * (fsum 1 k x CE / E9)
      + nsel k (fun j => sc1 (π * (x - j))) := by
  rw [fsum_CE, fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
    mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), Finset.mul_sum, Finset.mul_sum, nsel,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : T1j m x = (sc1 (π * (x - ((m + 1 : ℕ) : ℝ))) + sc1 (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
    unfold T1j; push_cast; ring_nf
  rw [e]
  by_cases hm : 2 * (m + 1) = k
  · rw [T1_near (per_j_pos hx hsep m), fv, fv, if_pos hm, if_pos hm, if_pos hm]; push_cast; ring
  · rw [T1_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, fv, if_neg hm, if_neg hm, if_neg hm]; push_cast; ring

theorem sum_T2 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T2j n x
    = -(Real.sin (π * x) / π) * (fsum 0 k x CE / E9) + 2 * (Real.cos (π * x) / π ^ 2) * (fsum 1 k x CE / E9)
      + (Real.sin (π * x) / π ^ 3) * (fsum 2 k x CE / E9) + nsel k (fun j => sc2 (π * (x - j))) := by
  rw [fsum_CE, fsum_CE, fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
    mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, nsel,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : T2j m x = (sc2 (π * (x - ((m + 1 : ℕ) : ℝ))) + sc2 (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
    unfold T2j; push_cast; ring_nf
  rw [e]
  by_cases hm : 2 * (m + 1) = k
  · rw [T2_near (per_j_pos hx hsep m), fv, fv, fv, if_pos hm, if_pos hm, if_pos hm, if_pos hm]; push_cast; ring
  · rw [T2_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, fv, fv, if_neg hm, if_neg hm, if_neg hm, if_neg hm]
    push_cast; ring

end sums

end AMW.G
