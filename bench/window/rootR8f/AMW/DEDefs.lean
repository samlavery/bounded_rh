import AMW.Moments

/-! ###### AMW/DEDefs — shared definitions of the dip-certificate route (bridge-port)

A piecewise-linear even certificate `ĝ` has knots `y_k = Y_k/E` at `k·Dk` (`k < n`, `Dk = 1/DkInv`) and vanishes from
`n·Dk` on: `ĝ = Σ_k y_k·(tent pair at ±k·Dk)` (`ghat`).  Its Fourier transform is
`g(u) = Dk·sinc²(πDk·u)·C(2πDk·u)` with the cosine polynomial `C(θ) = y₀ + 2 Σ_{1≤k<n} y_k cos kθ` (`certC`, the
form of `AMW.DESOS.cos_poly_ge_int`; `gPL`).  `qfAM` is the band function of the AM window, the Fourier transform of
`wfunAM`.  The two numeric obligations are `CertGNonneg` (`C ≥ 0`, DESOS) and `CertHNonneg` (`ĝ ≤ qfAM` on
`[0, ∞)`, DEQfCells).  `ghat_seg` reads `ĝ` on a knot segment. ###### -/

noncomputable section

open Real Finset

namespace AMW.DE

/-- a piecewise-linear even certificate: `Dk = 1/DkInv`, knots `y_k = Ys[k]/E` (`k < Ys.length`) -/
structure PLCert where
  DkInv : ℕ
  E : ℕ
  Ys : List ℤ

namespace PLCert

variable (c : PLCert)

/-- the number of knots -/
def n : ℕ := c.Ys.length

/-- the knot numerators, `0` from `n` on -/
def Y (k : ℕ) : ℤ := c.Ys.getD k 0

/-- the knot values -/
def y (k : ℕ) : ℝ := (c.Y k : ℝ) / c.E

/-- the knot spacing -/
def dk : ℝ := 1 / (c.DkInv : ℝ)

theorem Y_eq_zero {k : ℕ} (hk : c.n ≤ k) : c.Y k = 0 := by
  unfold Y; rw [List.getD_eq_default _ _ hk]

theorem y_eq_zero {k : ℕ} (hk : c.n ≤ k) : c.y k = 0 := by
  unfold y; rw [c.Y_eq_zero hk]; simp

end PLCert

/-- the unit tent -/
def tri (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- the `k`-th even tent pair at spacing `Dk` (one tent at `0`) -/
def tent (DkInv : ℝ) (k : ℕ) (α : ℝ) : ℝ :=
  if k = 0 then tri (α * DkInv) else tri (α * DkInv - k) + tri (α * DkInv + k)

/-- the piecewise-linear certificate `ĝ` -/
def ghat (c : PLCert) (α : ℝ) : ℝ := ∑ k ∈ range c.n, c.y k * tent (c.DkInv : ℝ) k α

/-- the cosine polynomial `C(θ) = y₀ + 2 Σ_{1≤k<n} y_k cos kθ` -/
def certC (c : PLCert) (θ : ℝ) : ℝ := c.y 0 + 2 * ∑ k ∈ Ico 1 c.n, c.y k * Real.cos (k * θ)

/-- the Fourier transform of `ĝ` in closed form, `g(u) = Dk·sinc²(πDk·u)·C(2πDk·u)` -/
def gPL (c : PLCert) (u : ℝ) : ℝ := c.dk * Real.sinc (π * c.dk * u) ^ 2 * certC c (2 * π * c.dk * u)

/-- `∫_{-1/2}^{1/2} vAM` -/
def Ivam : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), vAM s

/-- the band function of the AM window: `qf(α) = (vAM ⋆ vAM)(|α|)/(∫vAM)²` on `[-1, 1]`, `0` outside -/
def qfAM (α : ℝ) : ℝ := if |α| ≤ 1 then vConvAM |α| / Ivam ^ 2 else 0

/-- **obligation G** (DESOS): the cosine polynomial is nonnegative, so `g ≥ 0` -/
def CertGNonneg (c : PLCert) : Prop := ∀ θ : ℝ, 0 ≤ certC c θ

/-- **obligation H** (DEQfCells): `ĝ ≤ qf` on `[0, ∞)` (both are even) -/
def CertHNonneg (c : PLCert) : Prop := ∀ α : ℝ, 0 ≤ α → ghat c α ≤ qfAM α

/-! ### Basic facts -/

theorem tri_nonneg (t : ℝ) : 0 ≤ tri t := le_max_left _ _

theorem tri_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : tri t = 0 := by
  unfold tri; rw [max_eq_left (by linarith)]

theorem tri_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : tri t = 1 - |t| := by
  unfold tri; rw [max_eq_right (by linarith)]

theorem tri_neg (t : ℝ) : tri (-t) = tri t := by unfold tri; rw [abs_neg]

theorem continuous_tri : Continuous tri := by unfold tri; fun_prop

theorem tent_neg (D : ℝ) (k : ℕ) (α : ℝ) : tent D k (-α) = tent D k α := by
  unfold tent
  split_ifs
  · rw [neg_mul, tri_neg]
  · rw [neg_mul, show -(α * D) - k = -(α * D + k) by ring, show -(α * D) + k = -(α * D - k) by ring,
      tri_neg, tri_neg, add_comm]

theorem ghat_neg (c : PLCert) (α : ℝ) : ghat c (-α) = ghat c α := by
  unfold ghat; simp_rw [tent_neg]

theorem qfAM_neg (α : ℝ) : qfAM (-α) = qfAM α := by unfold qfAM; rw [abs_neg]

theorem continuous_tent (D : ℝ) (k : ℕ) : Continuous (tent D k) := by
  unfold tent
  split_ifs
  · exact continuous_tri.comp (by fun_prop)
  · exact (continuous_tri.comp (by fun_prop)).add (continuous_tri.comp (by fun_prop))

theorem continuous_ghat (c : PLCert) : Continuous (ghat c) := by
  unfold ghat
  exact continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_tent _ k)

/-- on `α ≥ 0` with `t = α·DkInv`, the tent pair is `tri (t − k)` -/
theorem tent_of_nonneg {D : ℝ} (hD : 0 ≤ D) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    tent D k α = tri (α * D - k) := by
  unfold tent
  split_ifs with hk
  · rw [hk]; simp
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have h0 : 0 ≤ α * D := mul_nonneg hα hD
    rw [tri_eq_zero (t := α * D + k) (by rw [abs_of_nonneg (by linarith)]; linarith), add_zero]

/-- **`ĝ` on a knot segment**: for `k·Dk ≤ α ≤ (k+1)·Dk`, `ĝ(α) = y_k + (y_{k+1} − y_k)(α/Dk − k)`
(`y_k = 0` from `n` on) -/
theorem ghat_seg (c : PLCert) (hD : 0 < c.DkInv) (k : ℕ) {α : ℝ}
    (h1 : (k : ℝ) ≤ α * c.DkInv) (h2 : α * c.DkInv ≤ k + 1) :
    ghat c α = c.y k + (c.y (k + 1) - c.y k) * (α * c.DkInv - k) := by
  have hD' : (0 : ℝ) < c.DkInv := by exact_mod_cast hD
  have hα : 0 ≤ α := by
    have : (0 : ℝ) ≤ α * c.DkInv := le_trans (Nat.cast_nonneg k) h1
    exact nonneg_of_mul_nonneg_left this hD'
  set t : ℝ := α * c.DkInv with ht
  -- each term: only `j = k` and `j = k + 1` survive
  have hterm : ∀ j : ℕ, c.y j * tent (c.DkInv : ℝ) j α
      = (if j = k then c.y k * (1 - (t - k)) else 0) + (if j = k + 1 then c.y (k + 1) * (t - k) else 0) := by
    intro j
    rw [tent_of_nonneg hD'.le j hα]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, if_neg (by omega), add_zero, tri_of_abs_le (by rw [abs_le]; constructor <;> linarith),
        abs_of_nonneg (by linarith)]
    · by_cases hjk1 : j = k + 1
      · subst hjk1
        rw [if_neg (by omega), if_pos rfl, zero_add,
          tri_of_abs_le (by rw [abs_le]; push_cast; constructor <;> linarith)]
        push_cast
        rw [abs_of_nonpos (by linarith)]
        ring
      · rw [if_neg hjk, if_neg hjk1, add_zero, tri_eq_zero, mul_zero]
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : (k : ℝ) + 2 ≤ j := by
            have : k + 2 ≤ j := by omega
            exact_mod_cast this
          rw [abs_of_nonpos (by linarith)]; linarith
  unfold ghat
  simp_rw [hterm, sum_add_distrib]
  rw [sum_ite_eq', sum_ite_eq']
  by_cases hk : k < c.n
  · rw [if_pos (mem_range.mpr hk)]
    by_cases hk1 : k + 1 < c.n
    · rw [if_pos (mem_range.mpr hk1)]; ring
    · rw [if_neg (by simpa using hk1), c.y_eq_zero (k := k + 1) (by omega)]; ring
  · rw [if_neg (by simpa using hk), if_neg (by simp only [mem_range]; omega), c.y_eq_zero (k := k) (by omega),
      c.y_eq_zero (k := k + 1) (by omega)]
    ring

end AMW.DE

end
