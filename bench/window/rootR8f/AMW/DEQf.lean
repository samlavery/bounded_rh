import AMW.Constant

/-! ###### AMW/DEQf — the overlap function of the AMTOPA profile in closed form (mvt-engine; D track, step 5)

For `vConvAM r = ∫_{-½}^{½-r} vAM(s) vAM(s+r) ds` (`AMW/Moments`), each of the 13 × 13 products
`cos(ω_j s) cos(ω_k (s + r))` integrates in closed form (`integral_cos_mul_cos_shift`, and `…_eq` for `j = k`), and
in the variable `r` every term is `cos(ω r)`, `sin(ω r)` or `r cos(ω r)` with `ω` one of the 13 profile frequencies.
Collecting the 169 terms by frequency gives

  `vConvAM r = Σ_{i<13} (Aq i · cos(ω_i r) + Bq i · sin(ω_i r) + Cq i · r · cos(ω_i r))`   (`vConvAM_eq_trig`),

with `Aq`, `Bq`, `Cq` finite sums of the per-pair coefficients (`axq` … `byq`).  The family `trigF A B C D` (adding
`r sin(ω r)`) is closed under `d/dr` (`hasDerivAt_trigF`, coefficient map `dCoef`), so `qf = f⋆f` with `f = vAM/∫vAM`,
`qf′` and `qf″` are all of this form (`qfAM_eq_trig`, `hasDerivAt_qf0`, `hasDerivAt_qf1`). ###### -/

noncomputable section

open Real

namespace AMW

/-! ## A product of shifted cosines -/

/-- an antiderivative of `cos(p s) cos(q (s + r))` in `s` (`p ≠ ±q`) -/
def Fcc (p q r s : ℝ) : ℝ :=
  Real.sin ((p - q) * s - q * r) / (2 * (p - q)) + Real.sin ((p + q) * s + q * r) / (2 * (p + q))

theorem hasDerivAt_Fcc {p q : ℝ} (r s : ℝ) (h1 : p - q ≠ 0) (h2 : p + q ≠ 0) :
    HasDerivAt (Fcc p q r) (Real.cos (p * s) * Real.cos (q * (s + r))) s := by
  have d1 : HasDerivAt (fun s => (p - q) * s - q * r) (p - q) s := by
    simpa using ((hasDerivAt_id s).const_mul (p - q)).sub_const (q * r)
  have d2 : HasDerivAt (fun s => (p + q) * s + q * r) (p + q) s := by
    simpa using ((hasDerivAt_id s).const_mul (p + q)).add_const (q * r)
  have h := ((d1.sin).div_const (2 * (p - q))).add ((d2.sin).div_const (2 * (p + q)))
  have e : Real.cos ((p - q) * s - q * r) * (p - q) / (2 * (p - q))
      + Real.cos ((p + q) * s + q * r) * (p + q) / (2 * (p + q))
      = Real.cos (p * s) * Real.cos (q * (s + r)) := by
    rw [show (p - q) * s - q * r = p * s - q * (s + r) by ring,
      show (p + q) * s + q * r = p * s + q * (s + r) by ring, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  rw [e] at h
  exact h

theorem integral_cos_mul_cos_shift {p q : ℝ} (r a b : ℝ) (h1 : p - q ≠ 0) (h2 : p + q ≠ 0) :
    ∫ s in a..b, Real.cos (p * s) * Real.cos (q * (s + r)) = Fcc p q r b - Fcc p q r a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_Fcc r s h1 h2)
    ((by fun_prop : Continuous fun s => Real.cos (p * s) * Real.cos (q * (s + r))).intervalIntegrable _ _)

/-- an antiderivative of `cos(q s) cos(q (s + r))` in `s` (`q ≠ 0`) -/
def Fcc0 (q r s : ℝ) : ℝ := s * Real.cos (q * r) / 2 + Real.sin (2 * q * s + q * r) / (4 * q)

theorem hasDerivAt_Fcc0 {q : ℝ} (r s : ℝ) (hq : q ≠ 0) :
    HasDerivAt (Fcc0 q r) (Real.cos (q * s) * Real.cos (q * (s + r))) s := by
  have d1 : HasDerivAt (fun s => s * Real.cos (q * r) / 2) (Real.cos (q * r) / 2) s := by
    simpa using ((hasDerivAt_id s).mul_const (Real.cos (q * r))).div_const 2
  have d2 : HasDerivAt (fun s => 2 * q * s + q * r) (2 * q) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 * q)).add_const (q * r)
  have h := d1.add ((d2.sin).div_const (4 * q))
  have e : Real.cos (q * r) / 2 + Real.cos (2 * q * s + q * r) * (2 * q) / (4 * q)
      = Real.cos (q * s) * Real.cos (q * (s + r)) := by
    rw [show 2 * q * s + q * r = q * s + q * (s + r) by ring, show q * r = q * (s + r) - q * s by ring,
      Real.cos_sub, Real.cos_add]
    field_simp
    ring
  rw [e] at h
  exact h

theorem integral_cos_mul_cos_shift_eq {q : ℝ} (r a b : ℝ) (hq : q ≠ 0) :
    ∫ s in a..b, Real.cos (q * s) * Real.cos (q * (s + r)) = Fcc0 q r b - Fcc0 q r a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_Fcc0 r s hq)
    ((by fun_prop : Continuous fun s => Real.cos (q * s) * Real.cos (q * (s + r))).intervalIntegrable _ _)

/-! ## The frequencies -/

theorem ωAM_pos (j : ℕ) : 0 < ωAM j := by
  unfold ωAM; split_ifs with h
  · positivity
  · have : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h
    positivity

theorem ωAM_inj {j k : ℕ} (h : ωAM j = ωAM k) : j = k := by
  have hpi := Real.pi_gt_three
  have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold ωAM at h
  by_cases hj : j = 0 <;> by_cases hk : k = 0
  · rw [hj, hk]
  · rw [if_pos hj, if_neg hk] at h
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  · rw [if_neg hj, if_pos hk] at h
    have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    nlinarith
  · rw [if_neg hj, if_neg hk] at h
    have hp : (2 * π) ≠ 0 := by positivity
    exact_mod_cast mul_left_cancel₀ hp h

theorem ωAM_sub_ne {j k : ℕ} (h : j ≠ k) : ωAM j - ωAM k ≠ 0 :=
  fun h0 => h (ωAM_inj (sub_eq_zero.mp h0))

theorem ωAM_add_ne (j k : ℕ) : ωAM j + ωAM k ≠ 0 := (add_pos (ωAM_pos j) (ωAM_pos k)).ne'

/-! ## The per-pair coefficients -/

/-- `(p − q)/2` and `(p + q)/2` for the pair `(j, k)` -/
def hmq (j k : ℕ) : ℝ := (ωAM j - ωAM k) / 2
def hpq (j k : ℕ) : ℝ := (ωAM j + ωAM k) / 2

/-- the coefficient of `cos(ω_j r)` in `∫ cos(ω_j s) cos(ω_k (s+r))` over `[-½, ½ - r]` -/
def axq (j k : ℕ) : ℝ :=
  if j = k then 1 / 2 + Real.sin (ωAM k) / (2 * ωAM k)
  else Real.sin (hmq j k) / (2 * (ωAM j - ωAM k)) + Real.sin (hpq j k) / (2 * (ωAM j + ωAM k))
/-- the coefficient of `sin(ω_j r)` -/
def bxq (j k : ℕ) : ℝ :=
  if j = k then -(Real.cos (ωAM k) / (2 * ωAM k))
  else -(Real.cos (hmq j k) / (2 * (ωAM j - ωAM k))) - Real.cos (hpq j k) / (2 * (ωAM j + ωAM k))
/-- the coefficient of `r cos(ω_j r)` -/
def cxq (j k : ℕ) : ℝ := if j = k then -(1 / 2) else 0
/-- the coefficient of `cos(ω_k r)` -/
def ayq (j k : ℕ) : ℝ :=
  if j = k then 0
  else Real.sin (hmq j k) / (2 * (ωAM j - ωAM k)) + Real.sin (hpq j k) / (2 * (ωAM j + ωAM k))
/-- the coefficient of `sin(ω_k r)` -/
def byq (j k : ℕ) : ℝ :=
  if j = k then 0
  else Real.cos (hmq j k) / (2 * (ωAM j - ωAM k)) - Real.cos (hpq j k) / (2 * (ωAM j + ωAM k))

/-- one pair's integral on the overlap, in the basis -/
theorem integral_pair (j k : ℕ) (r : ℝ) :
    ∫ s in (-(1:ℝ)/2)..(1/2 - r), Real.cos (ωAM j * s) * Real.cos (ωAM k * (s + r))
      = axq j k * Real.cos (ωAM j * r) + bxq j k * Real.sin (ωAM j * r) + cxq j k * r * Real.cos (ωAM j * r)
        + ayq j k * Real.cos (ωAM k * r) + byq j k * Real.sin (ωAM k * r) := by
  by_cases hjk : j = k
  · subst hjk
    have hq := (ωAM_pos j).ne'
    rw [integral_cos_mul_cos_shift_eq r _ _ hq]
    simp only [axq, bxq, cxq, ayq, byq, ↓reduceIte, Fcc0]
    set q := ωAM j
    rw [show 2 * q * (1 / 2 - r) + q * r = q - q * r by ring,
      show 2 * q * (-(1:ℝ) / 2) + q * r = -(q - q * r) by ring, Real.sin_neg, Real.sin_sub]
    field_simp
    ring
  · have h1 := ωAM_sub_ne hjk
    have h2 := ωAM_add_ne j k
    rw [integral_cos_mul_cos_shift r _ _ h1 h2]
    simp only [axq, bxq, cxq, ayq, byq, hjk, ↓reduceIte, Fcc, hmq, hpq]
    set p := ωAM j
    set q := ωAM k
    rw [show (p - q) * (1 / 2 - r) - q * r = (p - q) / 2 - p * r by ring,
      show (p + q) * (1 / 2 - r) + q * r = (p + q) / 2 - p * r by ring,
      show (p - q) * (-(1:ℝ) / 2) - q * r = -((p - q) / 2 + q * r) by ring,
      show (p + q) * (-(1:ℝ) / 2) + q * r = -((p + q) / 2 - q * r) by ring,
      Real.sin_neg, Real.sin_neg, Real.sin_sub, Real.sin_sub, Real.sin_add, Real.sin_sub]
    field_simp
    ring

/-! ## Collected by frequency -/

/-- the coefficients of `cos(ω_i r)`, `sin(ω_i r)`, `r cos(ω_i r)` in `vConvAM r` -/
def Aq (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 13, (cAM i : ℝ) * cAM k * axq i k + ∑ j ∈ Finset.range 13, (cAM j : ℝ) * cAM i * ayq j i
def Bq (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 13, (cAM i : ℝ) * cAM k * bxq i k + ∑ j ∈ Finset.range 13, (cAM j : ℝ) * cAM i * byq j i
def Cq (i : ℕ) : ℝ := ∑ k ∈ Finset.range 13, (cAM i : ℝ) * cAM k * cxq i k

/-- the trigonometric family on the 13 profile frequencies -/
def trigF (A B C D : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 13, (A i * Real.cos (ωAM i * r) + B i * Real.sin (ωAM i * r)
    + C i * r * Real.cos (ωAM i * r) + D i * r * Real.sin (ωAM i * r))

theorem vConvAM_eq_trig (r : ℝ) : vConvAM r = trigF Aq Bq Cq (fun _ => 0) r := by
  have hint : ∀ j k : ℕ, IntervalIntegrable
      (fun s => (cAM j : ℝ) * cAM k * (Real.cos (ωAM j * s) * Real.cos (ωAM k * (s + r))))
      MeasureTheory.volume (-(1:ℝ)/2) (1/2 - r) := fun j k =>
    (by fun_prop : Continuous fun s =>
      (cAM j : ℝ) * cAM k * (Real.cos (ωAM j * s) * Real.cos (ωAM k * (s + r)))).intervalIntegrable _ _
  have e1 : vConvAM r = ∑ j ∈ Finset.range 13, ∑ k ∈ Finset.range 13,
      (cAM j : ℝ) * cAM k * ∫ s in (-(1:ℝ)/2)..(1/2 - r), Real.cos (ωAM j * s) * Real.cos (ωAM k * (s + r)) := by
    unfold vConvAM vAM
    simp_rw [Finset.sum_mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (continuous_finsetSum _ fun k _ => (by fun_prop : Continuous fun s =>
        (cAM j : ℝ) * Real.cos (ωAM j * s) * ((cAM k : ℝ) * Real.cos (ωAM k * (s + r))))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun k _ => (by fun_prop : Continuous fun s =>
      (cAM j : ℝ) * Real.cos (ωAM j * s) * ((cAM k : ℝ) * Real.cos (ωAM k * (s + r)))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s; ring
  set cs := fun i => Real.cos (ωAM i * r) with hcs
  set sn := fun i => Real.sin (ωAM i * r) with hsn
  set X := fun j k => (cAM j : ℝ) * cAM k * axq j k * cs j + (cAM j : ℝ) * cAM k * bxq j k * sn j
    + (cAM j : ℝ) * cAM k * cxq j k * r * cs j with hX
  set Y := fun j k => (cAM j : ℝ) * cAM k * ayq j k * cs k + (cAM j : ℝ) * cAM k * byq j k * sn k with hY
  have e2 : vConvAM r = ∑ j ∈ Finset.range 13, ∑ k ∈ Finset.range 13, (X j k + Y j k) := by
    rw [e1]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [integral_pair]; simp only [hX, hY, hcs, hsn]; ring
  have e3 : ∑ j ∈ Finset.range 13, ∑ k ∈ Finset.range 13, (X j k + Y j k)
      = ∑ j ∈ Finset.range 13, ∑ k ∈ Finset.range 13, X j k + ∑ k ∈ Finset.range 13, ∑ j ∈ Finset.range 13, Y j k := by
    rw [Finset.sum_comm (f := fun k j => Y j k), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
  have hXs : ∀ j, ∑ k ∈ Finset.range 13, X j k = (∑ k ∈ Finset.range 13, (cAM j : ℝ) * cAM k * axq j k) * cs j
      + (∑ k ∈ Finset.range 13, (cAM j : ℝ) * cAM k * bxq j k) * sn j
      + (∑ k ∈ Finset.range 13, (cAM j : ℝ) * cAM k * cxq j k) * r * cs j := by
    intro j; simp only [hX, Finset.sum_add_distrib, Finset.sum_mul]
  have hYs : ∀ k, ∑ j ∈ Finset.range 13, Y j k = (∑ j ∈ Finset.range 13, (cAM j : ℝ) * cAM k * ayq j k) * cs k
      + (∑ j ∈ Finset.range 13, (cAM j : ℝ) * cAM k * byq j k) * sn k := by
    intro k; simp only [hY, Finset.sum_add_distrib, Finset.sum_mul]
  rw [e2, e3, trigF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hXs i, hYs i]
  simp only [Aq, Bq, Cq, hcs, hsn]
  ring

/-! ## The derivative of the family -/

/-- the coefficient map of `d/dr` on `trigF` -/
def dA (_A B C _D : ℕ → ℝ) (i : ℕ) : ℝ := B i * ωAM i + C i
def dB (A _B _C D : ℕ → ℝ) (i : ℕ) : ℝ := -(A i * ωAM i) + D i
def dC (_A _B _C D : ℕ → ℝ) (i : ℕ) : ℝ := D i * ωAM i
def dD (_A _B C _D : ℕ → ℝ) (i : ℕ) : ℝ := -(C i * ωAM i)

theorem hasDerivAt_trigF (A B C D : ℕ → ℝ) (r : ℝ) :
    HasDerivAt (trigF A B C D) (trigF (dA A B C D) (dB A B C D) (dC A B C D) (dD A B C D) r) r := by
  unfold trigF
  have hterm : ∀ i ∈ Finset.range 13, HasDerivAt (fun r => A i * Real.cos (ωAM i * r) + B i * Real.sin (ωAM i * r)
      + C i * r * Real.cos (ωAM i * r) + D i * r * Real.sin (ωAM i * r))
      (dA A B C D i * Real.cos (ωAM i * r) + dB A B C D i * Real.sin (ωAM i * r)
        + dC A B C D i * r * Real.cos (ωAM i * r) + dD A B C D i * r * Real.sin (ωAM i * r)) r := by
    intro i _
    have hw : HasDerivAt (fun r => ωAM i * r) (ωAM i) r := by simpa using (hasDerivAt_id r).const_mul (ωAM i)
    have hc := hw.cos
    have hs := hw.sin
    have h := (((hc.const_mul (A i)).add (hs.const_mul (B i))).add
      (((hasDerivAt_id r).const_mul (C i)).mul hc)).add (((hasDerivAt_id r).const_mul (D i)).mul hs)
    refine h.congr_deriv ?_
    simp only [dA, dB, dC, dD, id]; ring
  have := HasDerivAt.fun_sum hterm
  simpa using this

/-! ## `qf` -/

/-- `qf = f⋆f` on `[0, 1]`, `f = vAM / ∫vAM` (so `∫_{-1}^{1} qf = 1` and `qf 0 = bInf / aInf²`) -/
def qfAM (α : ℝ) : ℝ := vConvAM α / (∫ s in (-(1:ℝ)/2)..(1/2), vAM s) ^ 2

/-- the normaliser `(∫vAM)² = 2 sin²(√2/2)` -/
def ZQ : ℝ := 2 * Real.sin (Real.sqrt 2 / 2) ^ 2

theorem ZQ_pos : 0 < ZQ := by unfold ZQ; have := sin_theta0_pos; positivity

theorem integral_vAM_sq : (∫ s in (-(1:ℝ)/2)..(1/2), vAM s) ^ 2 = ZQ := by
  rw [integral_vAM, ZQ, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- the coefficients of `qf`, `qf′`, `qf″`, `qf‴` -/
def qA0 (i : ℕ) : ℝ := Aq i / ZQ
def qB0 (i : ℕ) : ℝ := Bq i / ZQ
def qC0 (i : ℕ) : ℝ := Cq i / ZQ
def qD0 (_ : ℕ) : ℝ := 0
def qA1 := dA qA0 qB0 qC0 qD0
def qB1 := dB qA0 qB0 qC0 qD0
def qC1 := dC qA0 qB0 qC0 qD0
def qD1 := dD qA0 qB0 qC0 qD0
def qA2 := dA qA1 qB1 qC1 qD1
def qB2 := dB qA1 qB1 qC1 qD1
def qC2 := dC qA1 qB1 qC1 qD1
def qD2 := dD qA1 qB1 qC1 qD1
def qA3 := dA qA2 qB2 qC2 qD2
def qB3 := dB qA2 qB2 qC2 qD2
def qC3 := dC qA2 qB2 qC2 qD2
def qD3 := dD qA2 qB2 qC2 qD2

/-- `qf`, `qf′`, `qf″`, `qf‴` as members of the family -/
def qf0 : ℝ → ℝ := trigF qA0 qB0 qC0 qD0
def qf1 : ℝ → ℝ := trigF qA1 qB1 qC1 qD1
def qf2 : ℝ → ℝ := trigF qA2 qB2 qC2 qD2
def qf3 : ℝ → ℝ := trigF qA3 qB3 qC3 qD3

theorem qfAM_eq_trig (α : ℝ) : qfAM α = qf0 α := by
  rw [qfAM, integral_vAM_sq, vConvAM_eq_trig, qf0, trigF, trigF, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [qA0, qB0, qC0, qD0]
  ring

theorem hasDerivAt_qf0 (α : ℝ) : HasDerivAt qf0 (qf1 α) α := hasDerivAt_trigF _ _ _ _ α
theorem hasDerivAt_qf1 (α : ℝ) : HasDerivAt qf1 (qf2 α) α := hasDerivAt_trigF _ _ _ _ α
theorem hasDerivAt_qf2 (α : ℝ) : HasDerivAt qf2 (qf3 α) α := hasDerivAt_trigF _ _ _ _ α

theorem hasDerivAt_qfAM (α : ℝ) : HasDerivAt qfAM (qf1 α) α := by
  have e : qfAM = qf0 := funext qfAM_eq_trig
  rw [e]; exact hasDerivAt_qf0 α

end AMW
