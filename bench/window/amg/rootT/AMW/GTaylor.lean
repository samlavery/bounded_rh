import AMW.GMT

/-!
# AMW/GTaylor — Taylor enclosures of `cos`, `sin`, `sinc`, `sc1`, `sc2` on `[-1, 1]` (stage G)

From `Complex.exp_bound` at order 12: `|cos θ − tc θ|, |sin θ − ts θ| ≤ |θ|¹² · C`, `C = 13/5748019200`, with the
degree-10/11 Taylor polynomials `tc`, `ts`.  Dividing the exact polynomial identities
  `θ tc θ − ts θ = θ² g1 θ`,  `−θ² ts θ − 2θ tc θ + 2 ts θ = θ³ g2 θ`,  `ts θ = θ · g0 θ`
by `θ`, `θ²`, `θ³` gives `|sinc − g0| ≤ C`, `|sc1 − g1| ≤ 2C`, `|sc2 − g2| ≤ 5C` on `|θ| ≤ 1`.
-/

noncomputable section

open Real

namespace AMW

def tcos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800
def tsin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800
def tsinc (t : ℝ) : ℝ := 1 - t^2/6 + t^4/120 - t^6/5040 + t^8/362880 - t^10/39916800
def tsc1 (t : ℝ) : ℝ := -t/3 + t^3/30 - t^5/840 + t^7/45360 - t^9/3991680
def tsc2 (t : ℝ) : ℝ := -1/3 + t^2/10 - t^4/168 + t^6/6480 - t^8/443520 + t^10/39916800
def terr : ℝ := 13 / 5748019200

theorem cos_sin_taylor12' (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - tcos θ| ≤ |θ| ^ 12 * terr ∧ |Real.sin θ - tsin θ| ≤ |θ| ^ 12 * terr := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, tcos, tsin]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I)‖
      ≤ |θ| ^ 12 * terr := by
    refine hb.trans (le_of_eq ?_); unfold terr; norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im]

theorem terr_pos : 0 < terr := by unfold terr; norm_num

theorem abs_sinc_sub_tsinc_le {t : ℝ} (ht : |t| ≤ 1) : |Real.sinc t - tsinc t| ≤ terr := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [tsinc, terr_pos.le]
  have hs := (cos_sin_taylor12' t ht).2
  have hp : 0 < |t| := abs_pos.mpr h0
  have e : Real.sinc t - tsinc t = (Real.sin t - tsin t) / t := by
    rw [Real.sinc_of_ne_zero h0]; unfold tsinc tsin; field_simp
  rw [e, abs_div, div_le_iff₀ hp]
  have hte := terr_pos.le
  have h11 : |t| ^ 11 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  calc |Real.sin t - tsin t| ≤ |t| ^ 12 * terr := hs
    _ = (|t| ^ 11 * terr) * |t| := by ring
    _ ≤ (1 * terr) * |t| := by gcongr
    _ = terr * |t| := by ring

theorem abs_sc1_sub_tsc1_le {t : ℝ} (ht : |t| ≤ 1) : |sc1 t - tsc1 t| ≤ 2 * terr := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [sc1, tsc1, terr_pos.le]
  have hc := (cos_sin_taylor12' t ht).1
  have hs := (cos_sin_taylor12' t ht).2
  have hp : 0 < |t| := abs_pos.mpr h0
  have hp2 : 0 < t ^ 2 := by positivity
  have e : sc1 t - tsc1 t = (t * (Real.cos t - tcos t) - (Real.sin t - tsin t)) / t ^ 2 := by
    rw [sc1, if_neg h0]; unfold tsc1 tcos tsin; field_simp; ring
  rw [e, abs_div, abs_of_pos hp2, div_le_iff₀ hp2]
  have h10 : |t| ^ 10 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hte := terr_pos.le
  have h12 : 0 ≤ |t| ^ 12 * terr := by positivity
  calc |t * (Real.cos t - tcos t) - (Real.sin t - tsin t)|
      ≤ |t| * |Real.cos t - tcos t| + |Real.sin t - tsin t| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ |t| * (|t| ^ 12 * terr) + |t| ^ 12 * terr := by gcongr
    _ ≤ 1 * (|t| ^ 12 * terr) + |t| ^ 12 * terr := by gcongr
    _ = (|t| ^ 10 * (2 * terr)) * |t| ^ 2 := by ring
    _ ≤ (1 * (2 * terr)) * |t| ^ 2 := by gcongr
    _ = 2 * terr * t ^ 2 := by rw [ht2]; ring

theorem abs_sc2_sub_tsc2_le {t : ℝ} (ht : |t| ≤ 1) : |sc2 t - tsc2 t| ≤ 5 * terr := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [sc2, tsc2, terr_pos.le]
  have hc := (cos_sin_taylor12' t ht).1
  have hs := (cos_sin_taylor12' t ht).2
  have hp : 0 < |t| := abs_pos.mpr h0
  have hp3 : 0 < |t ^ 3| := by positivity
  have e : sc2 t - tsc2 t
      = (-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t) + 2 * (Real.sin t - tsin t)) / t ^ 3 := by
    rw [sc2, if_neg h0]; unfold tsc2 tcos tsin; field_simp; ring
  rw [e, abs_div, div_le_iff₀ hp3, abs_pow]
  have h9 : |t| ^ 9 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have hsq : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have h0' := abs_nonneg t
  have hte := terr_pos.le
  have h12 : 0 ≤ |t| ^ 12 * terr := by positivity
  calc |-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t) + 2 * (Real.sin t - tsin t)|
      ≤ |t| ^ 2 * |Real.sin t - tsin t| + 2 * |t| * |Real.cos t - tcos t| + 2 * |Real.sin t - tsin t| := by
        have := abs_add_le (-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t)) (2 * (Real.sin t - tsin t))
        have h2 := abs_sub (-t ^ 2 * (Real.sin t - tsin t)) (2 * t * (Real.cos t - tcos t))
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_two] at *
        linarith
    _ ≤ 1 * (|t| ^ 12 * terr) + 2 * 1 * (|t| ^ 12 * terr) + 2 * (|t| ^ 12 * terr) := by gcongr
    _ = (|t| ^ 9 * (5 * terr)) * |t| ^ 3 := by ring
    _ ≤ (1 * (5 * terr)) * |t| ^ 3 := by gcongr
    _ = 5 * terr * |t| ^ 3 := by ring

end AMW
