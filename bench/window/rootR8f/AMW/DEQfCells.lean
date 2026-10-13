import AMW.DEQfIv

/-! ###### AMW/DEQfCells — `ĝ ≤ qf` by cells (mvt-engine; D track, step 6)

`qf` (`AMW/DEQf`) is bounded below on a cell `[a, b] ⊆ [0, 1]` with centre `c` by Taylor to order two:
`qf(x) ≥ qf(c) + qf′(c)(x − c) − (M/2)(x − c)²` with `M ≥ sup |qf″|` (`taylor2_lower`; `M` from the coefficient
enclosures, `qf2_abs_le`).  Against a line through `(a, y_a)`, `(b, y_b)` that bound is a concave function minus a
line, so the two endpoint checks suffice (`cellOk`, `cell_sound`); `qf(c)`, `qf′(c)` are enclosed at the rational
centre (`evI`).  A knot interval is covered by `s` equal cells (`knotOk`, `knot_sound`). ###### -/

noncomputable section

open Real

namespace AMW.DQ

open AMW

/-! ## `cos`, `sin` of `ω_i c` at a rational point -/

/-- `√2 c / 2` -/
def hX (c : ℚ) : IQ := DQ.mul s2I (DQ.pt (c / 2))

theorem iv_hX (c : ℚ) : InI (hX c) (Real.sqrt 2 * c / 2) := by
  have h := iv_mul iv_s2I (iv_pt (c / 2)); push_cast at h; rw [mul_div_assoc]; exact h

def cosPt (i : ℕ) (c : ℚ) : IQ :=
  if i = 0 then DQ.sub (DQ.mul (DQ.cos01 (hX c)) (DQ.cos01 (hX c))) (DQ.mul (DQ.sin01 (hX c)) (DQ.sin01 (hX c)))
  else sinPiI (2 * i * c + 1 / 2)
def sinPt (i : ℕ) (c : ℚ) : IQ :=
  if i = 0 then DQ.mul (DQ.pt 2) (DQ.mul (DQ.sin01 (hX c)) (DQ.cos01 (hX c)))
  else sinPiI (2 * i * c)
def ptOk (i : ℕ) (c : ℚ) : Bool :=
  if i = 0 then ok01 (hX c) else sinPiOk (2 * i * c) && sinPiOk (2 * i * c + 1 / 2)

theorem ωAM_mul_pt {i : ℕ} (hi : i ≠ 0) (c : ℚ) : ωAM i * c = Real.pi * ((2 * i * c : ℚ) : ℝ) := by
  unfold ωAM; rw [if_neg hi]; push_cast; ring

theorem iv_cosPt {i : ℕ} {c : ℚ} (h : ptOk i c = true) : InI (cosPt i c) (Real.cos (ωAM i * c)) := by
  unfold cosPt ptOk at *
  split_ifs at h ⊢ with hi
  · subst hi
    rw [ωAM_zero, show Real.sqrt 2 * (c : ℝ) = Real.sqrt 2 * c / 2 + Real.sqrt 2 * c / 2 by ring, Real.cos_add]
    exact iv_sub (iv_mul (iv_cos01 (iv_hX c) h) (iv_cos01 (iv_hX c) h))
      (iv_mul (iv_sin01 (iv_hX c) h) (iv_sin01 (iv_hX c) h))
  · simp only [Bool.and_eq_true] at h
    have hs := sinPiI_sound _ h.2
    rw [ωAM_mul_pt hi, ← Real.sin_add_pi_div_two]
    have e : Real.pi * ((2 * i * c + 1 / 2 : ℚ) : ℝ) = Real.pi * ((2 * i * c : ℚ) : ℝ) + Real.pi / 2 := by
      push_cast; ring
    rw [e] at hs; exact hs

theorem iv_sinPt {i : ℕ} {c : ℚ} (h : ptOk i c = true) : InI (sinPt i c) (Real.sin (ωAM i * c)) := by
  unfold sinPt ptOk at *
  split_ifs at h ⊢ with hi
  · subst hi
    rw [ωAM_zero, show Real.sqrt 2 * (c : ℝ) = 2 * (Real.sqrt 2 * c / 2) by ring, Real.sin_two_mul]
    have h2 := iv_mul (iv_pt (2 : ℚ)) (iv_mul (iv_sin01 (iv_hX c) h) (iv_cos01 (iv_hX c) h))
    push_cast at h2; rw [mul_assoc]; exact h2
  · simp only [Bool.and_eq_true] at h
    rw [ωAM_mul_pt hi]; exact sinPiI_sound _ h.1

/-! ## A member of the family at a rational point -/

def evI (A B C D : ℕ → IQ) (c : ℚ) : IQ :=
  DQ.isum (fun i => DQ.add (DQ.add (DQ.add (DQ.mul (A i) (cosPt i c)) (DQ.mul (B i) (sinPt i c)))
    (DQ.mul (DQ.mul (C i) (DQ.pt c)) (cosPt i c))) (DQ.mul (DQ.mul (D i) (DQ.pt c)) (sinPt i c))) 13

def evOk (c : ℚ) : Bool := (List.range 13).all fun i => ptOk i c

theorem iv_evI {A B C D : ℕ → IQ} {a b cc d : ℕ → ℝ} (hs : Sound4 A B C D a b cc d) {c : ℚ}
    (hok : evOk c = true) : InI (evI A B C D c) (trigF a b cc d c) := by
  have hp : ∀ i < 13, ptOk i c = true := by
    intro i hi; simp only [evOk, List.all_eq_true, List.mem_range] at hok; exact hok i hi
  unfold evI trigF
  refine iv_isumB 13 fun i hi => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hs i hi
  have hcos := iv_cosPt (hp i hi)
  have hsin := iv_sinPt (hp i hi)
  exact iv_add (iv_add (iv_add (iv_mul ha hcos) (iv_mul hb hsin)) (iv_mul (iv_mul hc (iv_pt c)) hcos))
    (iv_mul (iv_mul hd (iv_pt c)) hsin)

/-! ## A bound on `|qf″|` -/

def absHi (X : IQ) : ℚ := max |X.1| |X.2|

theorem abs_le_absHi {X : IQ} {x : ℝ} (h : InI X x) : |x| ≤ ((absHi X : ℚ) : ℝ) := by
  unfold absHi; push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le ((X.1 : ℚ) : ℝ)
    have := le_max_left |((X.1 : ℚ) : ℝ)| |((X.2 : ℚ) : ℝ)|
    linarith [h.1]
  · have := le_abs_self ((X.2 : ℚ) : ℝ)
    have := le_max_right |((X.1 : ℚ) : ℝ)| |((X.2 : ℚ) : ℝ)|
    linarith [h.2]

def qsum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => qsum f n + f n

theorem qsum_cast (f : ℕ → ℚ) : ∀ n, ((qsum f n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((f i : ℚ) : ℝ)
  | 0 => by simp [qsum]
  | n + 1 => by rw [qsum, Finset.sum_range_succ]; push_cast; rw [qsum_cast f n]

def bnd4 (A B C D : ℕ → IQ) : ℚ := qsum (fun i => absHi (A i) + absHi (B i) + absHi (C i) + absHi (D i)) 13

theorem trigF_abs_le (a b c d : ℕ → ℝ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    |trigF a b c d r| ≤ ∑ i ∈ Finset.range 13, (|a i| + |b i| + |c i| + |d i|) := by
  unfold trigF
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hc := Real.abs_cos_le_one (ωAM i * r)
  have hs := Real.abs_sin_le_one (ωAM i * r)
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  calc |a i * Real.cos (ωAM i * r) + b i * Real.sin (ωAM i * r) + c i * r * Real.cos (ωAM i * r)
        + d i * r * Real.sin (ωAM i * r)|
      ≤ |a i| * |Real.cos (ωAM i * r)| + |b i| * |Real.sin (ωAM i * r)| + |c i| * |r| * |Real.cos (ωAM i * r)|
        + |d i| * |r| * |Real.sin (ωAM i * r)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_mul _ _).le (abs_mul _ _).le)) ?_)) ?_)
        · rw [abs_mul, abs_mul]
        · rw [abs_mul, abs_mul]
    _ ≤ |a i| * 1 + |b i| * 1 + |c i| * 1 * 1 + |d i| * 1 * 1 := by
        gcongr
    _ = |a i| + |b i| + |c i| + |d i| := by ring

theorem trigF_abs_le_bnd {A B C D : ℕ → IQ} {a b c d : ℕ → ℝ} (hs : Sound4 A B C D a b c d) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ 1) : |trigF a b c d r| ≤ ((bnd4 A B C D : ℚ) : ℝ) := by
  refine (trigF_abs_le a b c d h0 h1).trans ?_
  unfold bnd4; rw [qsum_cast]
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hs i (Finset.mem_range.mp hi)
  push_cast
  linarith [abs_le_absHi ha, abs_le_absHi hb, abs_le_absHi hc, abs_le_absHi hd]

/-- the global second-derivative bound (`9`; the measured maximum of `|qf″|` on `[0, 1]` is `3.58`) -/
def M2 : ℚ := 9

theorem bnd_q2_le : bnd4 qA2T qB2T qC2T qD2T ≤ M2 := by decide +kernel

theorem qf2_abs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : |qf2 r| ≤ ((M2 : ℚ) : ℝ) :=
  (trigF_abs_le_bnd sound_q2 h0 h1).trans (by exact_mod_cast bnd_q2_le)

/-! ## Taylor to order two -/

theorem taylor2_lower {f f1 f2 : ℝ → ℝ} {M a b c x : ℝ}
    (hf : ∀ y, HasDerivAt f (f1 y) y) (hf1 : ∀ y, HasDerivAt f1 (f2 y) y)
    (hM : ∀ y ∈ Set.Icc a b, |f2 y| ≤ M) (hc : c ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b) :
    f c + f1 c * (x - c) - M / 2 * (x - c) ^ 2 ≤ f x := by
  set k : ℝ → ℝ := fun y => f1 y - f1 c + M * (y - c) with hk
  have hkd : ∀ y, HasDerivAt k (f2 y + M) y := by
    intro y
    have := ((hf1 y).sub_const (f1 c)).add (((hasDerivAt_id y).sub_const c).const_mul M)
    have e : k = (fun x => f1 x - f1 c) + fun y => M * (id y - c) := by funext z; simp [hk]
    rw [e]; exact this.congr_deriv (by ring)
  have hkm : MonotoneOn k (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) (fun y _ => (hkd y).continuousAt.continuousWithinAt)
      (fun y _ => (hkd y).differentiableAt.differentiableWithinAt) fun y hy => ?_
    rw [(hkd y).deriv]
    rw [interior_Icc] at hy
    have := hM y ⟨hy.1.le, hy.2.le⟩
    linarith [neg_abs_le (f2 y)]
  have hkc : k c = 0 := by simp [hk]
  set g : ℝ → ℝ := fun y => f y - f c - f1 c * (y - c) + M / 2 * (y - c) ^ 2 with hg
  have hgd : ∀ y, HasDerivAt g (k y) y := by
    intro y
    have h1 := (((hf y).sub_const (f c)).sub (((hasDerivAt_id y).sub_const c).const_mul (f1 c)))
    have h2 := (((hasDerivAt_id y).sub_const c).pow 2).const_mul (M / 2)
    have := h1.add h2
    refine this.congr_deriv ?_
    simp only [hk, id]; ring
  have hgc : g c = 0 := by simp [hg]
  have key : 0 ≤ g x := by
    rcases le_total c x with hcx | hxc
    · have hmono : MonotoneOn g (Set.Icc c b) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc c b) (fun y _ => (hgd y).continuousAt.continuousWithinAt)
          (fun y _ => (hgd y).differentiableAt.differentiableWithinAt) fun y hy => ?_
        rw [(hgd y).deriv]
        rw [interior_Icc] at hy
        have := hkm hc ⟨hc.1.trans hy.1.le, hy.2.le⟩ hy.1.le
        rw [hkc] at this; exact this
      have := hmono ⟨le_rfl, hc.2⟩ ⟨hcx, hx.2⟩ hcx
      rw [hgc] at this; exact this
    · have hanti : AntitoneOn g (Set.Icc a c) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc a c) (fun y _ => (hgd y).continuousAt.continuousWithinAt)
          (fun y _ => (hgd y).differentiableAt.differentiableWithinAt) fun y hy => ?_
        rw [(hgd y).deriv]
        rw [interior_Icc] at hy
        have := hkm ⟨hy.1.le, hy.2.le.trans hc.2⟩ hc hy.2.le
        rw [hkc] at this; exact this
      have := hanti ⟨hx.1, hxc⟩ ⟨hc.1, le_rfl⟩ hxc
      rw [hgc] at this; exact this
  simp only [hg] at key
  linarith

/-! ## A cell -/

/-- the cell check on `[a, b]` against the line through `(a, ya)` and `(b, yb)` -/
def cellOk (M a b ya yb : ℚ) : Bool :=
  let c := (a + b) / 2
  let h := (b - a) / 2
  let Q0 := evI qA0T qB0T qC0T qD0T c
  let Q1 := evI qA1T qB1T qC1T qD1T c
  decide (0 ≤ a) && decide (a < b) && decide (b ≤ 1) && evOk c &&
    decide (ya ≤ Q0.1 - Q1.2 * h - M / 2 * h ^ 2) && decide (yb ≤ Q0.1 + Q1.1 * h - M / 2 * h ^ 2)

theorem cell_sound {a b ya yb : ℚ} (h : cellOk M2 a b ya yb = true) :
    ∀ x ∈ Set.Icc (a : ℝ) b, (ya : ℝ) + (yb - ya) * (x - a) / (b - a) ≤ qfAM x := by
  intro x hx
  simp only [cellOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha0, hab⟩, hb1⟩, hev⟩, hya⟩, hyb⟩ := h
  set c : ℚ := (a + b) / 2 with hcdef
  set hh : ℚ := (b - a) / 2 with hhdef
  have hQ0 := iv_evI sound_q0 hev
  have hQ1 := iv_evI sound_q1 hev
  set Q0 := evI qA0T qB0T qC0T qD0T c
  set Q1 := evI qA1T qB1T qC1T qD1T c
  have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hya' : (ya : ℝ) ≤ Q0.1 - Q1.2 * hh - M2 / 2 * hh ^ 2 := by exact_mod_cast hya
  have hyb' : (yb : ℝ) ≤ Q0.1 + Q1.1 * hh - M2 / 2 * hh ^ 2 := by exact_mod_cast hyb
  have hc' : ((c : ℚ) : ℝ) = ((a : ℝ) + b) / 2 := by rw [hcdef]; push_cast; ring
  have hh' : ((hh : ℚ) : ℝ) = ((b : ℝ) - a) / 2 := by rw [hhdef]; push_cast; ring
  have hcI : ((c : ℚ) : ℝ) ∈ Set.Icc (a : ℝ) b := by rw [hc']; constructor <;> linarith
  have hM : ∀ y ∈ Set.Icc (a : ℝ) b, |qf2 y| ≤ ((M2 : ℚ) : ℝ) :=
    fun y hy => qf2_abs_le (ha0'.trans hy.1) (hy.2.trans hb1')
  have hT := taylor2_lower hasDerivAt_qf0 hasDerivAt_qf1 hM hcI hx
  rw [qfAM_eq_trig]
  -- the weights of `yb` and `ya` at `x`
  set l : ℝ := (x - a) / (b - a) with hl
  have hba : (0 : ℝ) < b - a := by linarith
  have hl0 : 0 ≤ l := div_nonneg (by linarith [hx.1]) hba.le
  have hl1 : l ≤ 1 := by rw [div_le_one hba]; linarith [hx.2]
  have ht : x - ((c : ℚ) : ℝ) = (2 * l - 1) * ((hh : ℚ) : ℝ) := by
    rw [hc', hh', hl]; field_simp; ring
  have hline : (ya : ℝ) + (yb - ya) * (x - a) / (b - a) = (1 - l) * ya + l * yb := by
    rw [hl]; field_simp; ring
  rw [hline]
  have hq0 : ((Q0.1 : ℚ) : ℝ) ≤ qf0 ((c : ℚ) : ℝ) := hQ0.1
  have hq1lo : ((Q1.1 : ℚ) : ℝ) ≤ qf1 ((c : ℚ) : ℝ) := hQ1.1
  have hq1hi : qf1 ((c : ℚ) : ℝ) ≤ ((Q1.2 : ℚ) : ℝ) := hQ1.2
  have hhpos : (0 : ℝ) ≤ ((hh : ℚ) : ℝ) := by rw [hh']; linarith
  have hM2 : (0 : ℝ) ≤ ((M2 : ℚ) : ℝ) := by norm_num [M2]
  have ht2 : (x - ((c : ℚ) : ℝ)) ^ 2 ≤ ((hh : ℚ) : ℝ) ^ 2 := by
    rw [ht, mul_pow]
    have : (2 * l - 1) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ((hh : ℚ) : ℝ)]
  set q1 := qf1 ((c : ℚ) : ℝ)
  have hlin : (1 - l) * (-(((Q1.2 : ℚ) : ℝ)) * hh) + l * (((Q1.1 : ℚ) : ℝ) * hh) ≤ q1 * (x - c) := by
    rw [ht]
    have e1 : (1 - l) * (-(q1) * hh) + l * (q1 * hh) = q1 * ((2 * l - 1) * hh) := by ring
    rw [← e1]
    have h1l : 0 ≤ 1 - l := by linarith
    have t1 : (1 - l) * (-(((Q1.2 : ℚ) : ℝ)) * hh) ≤ (1 - l) * (-q1 * hh) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (neg_le_neg hq1hi) hhpos) h1l
    have t2 : l * (((Q1.1 : ℚ) : ℝ) * hh) ≤ l * (q1 * hh) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq1lo hhpos) hl0
    linarith
  have hquad : ((M2 : ℚ) : ℝ) / 2 * (x - c) ^ 2 ≤ ((M2 : ℚ) : ℝ) / 2 * hh ^ 2 :=
    mul_le_mul_of_nonneg_left ht2 (by linarith)
  have h1l : 0 ≤ 1 - l := by linarith
  have hyacomb : (1 - l) * ya ≤ (1 - l) * (((Q0.1 : ℚ) : ℝ) - Q1.2 * hh - M2 / 2 * hh ^ 2) :=
    mul_le_mul_of_nonneg_left hya' h1l
  have hybcomb : l * yb ≤ l * (((Q0.1 : ℚ) : ℝ) + Q1.1 * hh - M2 / 2 * hh ^ 2) :=
    mul_le_mul_of_nonneg_left hyb' hl0
  have hsum : (1 - l) * (((Q0.1 : ℚ) : ℝ) - Q1.2 * hh - M2 / 2 * hh ^ 2)
      + l * (((Q0.1 : ℚ) : ℝ) + Q1.1 * hh - M2 / 2 * hh ^ 2)
      = ((Q0.1 : ℚ) : ℝ) + ((1 - l) * (-(((Q1.2 : ℚ) : ℝ)) * hh) + l * (((Q1.1 : ℚ) : ℝ) * hh))
        - ((M2 : ℚ) : ℝ) / 2 * hh ^ 2 := by ring
  linarith

/-! ## A knot interval in `s` cells -/

/-- the knot interval `[k/N, (k+1)/N]` in `s` equal cells, against the line through `(k/N, y0)`, `((k+1)/N, y1)` -/
def knotOk (N s k : ℕ) (y0 y1 : ℚ) : Bool :=
  (List.range s).all fun m => cellOk M2 ((k : ℚ) / N + m / (N * s)) ((k : ℚ) / N + (m + 1) / (N * s))
    (y0 + (y1 - y0) * m / s) (y0 + (y1 - y0) * (m + 1) / s)

theorem knot_sound {N s k : ℕ} {y0 y1 : ℚ} (hN : 0 < N) (hs : 0 < s) (h : knotOk N s k y0 y1 = true) :
    ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N), (y0 : ℝ) + (y1 - y0) * (N * x - k) ≤ qfAM x := by
  intro x hx
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set u : ℝ := (N * x - k) * s with hu
  have hu0 : 0 ≤ u := by
    have : (k : ℝ) ≤ N * x := by have := hx.1; rw [div_le_iff₀ hN'] at this; linarith
    rw [hu]; exact mul_nonneg (by linarith) hs'.le
  have hus : u ≤ s := by
    have : N * x ≤ (k : ℝ) + 1 := by have := hx.2; rw [le_div_iff₀ hN'] at this; linarith
    rw [hu]; nlinarith
  set m : ℕ := min (⌊u⌋₊) (s - 1) with hm
  have hms : m < s := by rw [hm]; omega
  have hm1 : (m : ℝ) ≤ u := by
    have : (m : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
    exact this.trans (Nat.floor_le hu0)
  have hm2 : u ≤ (m : ℝ) + 1 := by
    rcases le_or_gt (⌊u⌋₊) (s - 1) with hf | hf
    · have : m = ⌊u⌋₊ := by rw [hm]; exact min_eq_left hf
      rw [this]; exact (Nat.lt_floor_add_one u).le
    · have : m = s - 1 := by rw [hm]; exact min_eq_right hf.le
      rw [this]
      have : ((s - 1 : ℕ) : ℝ) + 1 = s := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; exact hus
  have hcell : cellOk M2 ((k : ℚ) / N + m / (N * s)) ((k : ℚ) / N + (m + 1) / (N * s))
      (y0 + (y1 - y0) * m / s) (y0 + (y1 - y0) * (m + 1) / s) = true := by
    simp only [knotOk, List.all_eq_true, List.mem_range] at h; exact h m hms
  have hxc : x ∈ Set.Icc (((k : ℚ) / N + m / (N * s) : ℚ) : ℝ) ((((k : ℚ) / N + (m + 1) / (N * s)) : ℚ) : ℝ) := by
    push_cast
    constructor
    · have : (m : ℝ) / (N * s) ≤ x - k / N := by
        rw [div_le_iff₀ (by positivity)]; rw [hu] at hm1
        have e : (x - k / N) * (N * s) = (N * x - k) * s := by field_simp
        linarith
      linarith
    · have : x - k / N ≤ ((m : ℝ) + 1) / (N * s) := by
        rw [le_div_iff₀ (by positivity)]; rw [hu] at hm2
        have e : (x - k / N) * (N * s) = (N * x - k) * s := by field_simp
        linarith
      linarith
  have hc := cell_sound hcell x hxc
  have e : ((((y0 + (y1 - y0) * m / s : ℚ)) : ℝ) + ((((y0 + (y1 - y0) * (m + 1) / s : ℚ)) : ℝ)
        - (((y0 + (y1 - y0) * m / s : ℚ)) : ℝ)) * (x - (((k : ℚ) / N + m / (N * s) : ℚ) : ℝ))
        / ((((k : ℚ) / N + (m + 1) / (N * s) : ℚ) : ℝ) - (((k : ℚ) / N + m / (N * s) : ℚ) : ℝ)))
      = (y0 : ℝ) + (y1 - y0) * (N * x - k) := by
    push_cast
    field_simp
    ring
  rw [e] at hc; exact hc

/-! ## The profile at a rational point, and a lower bound near the ends -/

def vI (c : ℚ) : IQ := DQ.isum (fun j => DQ.mul (DQ.pt (cAM j)) (cosPt j c)) 13

theorem iv_vI {c : ℚ} (hok : evOk c = true) : InI (vI c) (vAM c) := by
  have hp : ∀ i < 13, ptOk i c = true := by
    intro i hi; simp only [evOk, List.all_eq_true, List.mem_range] at hok; exact hok i hi
  unfold vI vAM
  exact iv_isumB 13 fun j hj => iv_mul (iv_pt _) (iv_cosPt (hp j hj))

theorem vAM_lip (s c : ℝ) : vAM c - 7 / 2 * |s - c| ≤ vAM s := by
  rcases lt_trichotomy s c with hsc | hsc | hsc
  · obtain ⟨ξ, _, hξ⟩ := exists_hasDerivAt_eq_slope vAM vAMd hsc vAM_continuous.continuousOn
      (fun y _ => hasDerivAt_vAM y)
    have hb := abs_le.mp (abs_vAMd_le ξ)
    rw [hξ] at hb
    have hd : 0 < c - s := by linarith
    rw [abs_of_neg (by linarith : s - c < 0)]
    have := hb.2; rw [div_le_iff₀ hd] at this; linarith
  · subst hsc; simp
  · obtain ⟨ξ, _, hξ⟩ := exists_hasDerivAt_eq_slope vAM vAMd hsc vAM_continuous.continuousOn
      (fun y _ => hasDerivAt_vAM y)
    have hb := abs_le.mp (abs_vAMd_le ξ)
    rw [hξ] at hb
    have hd : 0 < s - c := by linarith
    rw [abs_of_pos hd]
    have := hb.1; rw [le_div_iff₀ hd] at this; linarith

/-- the centre of the `m`-th of `s` cells on `[1/2 − 1/N, 1/2]` -/
def vloC (N s m : ℕ) : ℚ := 1 / 2 - 1 / (N : ℚ) + (2 * (m : ℚ) + 1) / (2 * (N : ℚ) * s)

theorem vloC_cast (N s m : ℕ) : ((vloC N s m : ℚ) : ℝ) = 1 / 2 - 1 / (N : ℝ) + (2 * (m : ℝ) + 1) / (2 * N * s) := by
  unfold vloC; push_cast; ring

/-- `vAM ≥ vlo` on `[1/2 − 1/N, 1/2]`, by `s` cells (Lipschitz `7/2`) -/
def vloOk (N s : ℕ) (vlo : ℚ) : Bool :=
  decide (0 < vlo) && (List.range s).all fun m =>
    evOk (vloC N s m) && decide (vlo ≤ (vI (vloC N s m)).1 - 7 / 2 * (1 / (2 * (N : ℚ) * s)))

theorem vlo_sound {N s : ℕ} {vlo : ℚ} (hN : 0 < N) (hs : 0 < s) (h : vloOk N s vlo = true) :
    ∀ y ∈ Set.Icc ((1 : ℝ) / 2 - 1 / N) (1 / 2), (vlo : ℝ) ≤ vAM y := by
  intro y hy
  simp only [vloOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set u : ℝ := (y - (1 / 2 - 1 / N)) * N * s with hu
  have hu0 : 0 ≤ u := by rw [hu]; have := hy.1; positivity
  have hus : u ≤ s := by
    rw [hu]
    have : y - (1 / 2 - 1 / N) ≤ 1 / N := by linarith [hy.2]
    have : (y - (1 / 2 - 1 / N)) * N ≤ 1 := by rw [← le_div_iff₀ hN']; simpa using this
    nlinarith
  set m : ℕ := min (⌊u⌋₊) (s - 1) with hm
  have hms : m < s := by rw [hm]; omega
  have hm1 : (m : ℝ) ≤ u := (by exact_mod_cast min_le_left _ _ : (m : ℝ) ≤ (⌊u⌋₊ : ℝ)).trans (Nat.floor_le hu0)
  have hm2 : u ≤ (m : ℝ) + 1 := by
    rcases le_or_gt (⌊u⌋₊) (s - 1) with hf | hf
    · have : m = ⌊u⌋₊ := by rw [hm]; exact min_eq_left hf
      rw [this]; exact (Nat.lt_floor_add_one u).le
    · have : m = s - 1 := by rw [hm]; exact min_eq_right hf.le
      rw [this]
      have : ((s - 1 : ℕ) : ℝ) + 1 = s := by rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; exact hus
  obtain ⟨hev, hv⟩ := h.2 m hms
  have hcv := (iv_vI hev).1
  have hl := vAM_lip y ((vloC N s m : ℚ) : ℝ)
  have hdist : |y - ((vloC N s m : ℚ) : ℝ)| ≤ 1 / (2 * N * s) := by
    rw [vloC_cast, abs_le]
    have e : y - (1 / 2 - 1 / (N : ℝ) + (2 * (m : ℝ) + 1) / (2 * N * s)) = (u - m - 1 / 2) / (N * s) := by
      rw [hu]; field_simp; ring
    rw [e]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have : -(1 / (2 * N * s)) * (N * s) = -(1 / 2 : ℝ) := by field_simp
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have : 1 / (2 * N * s) * (N * s) = (1 / 2 : ℝ) := by field_simp
      linarith
  have hv' := (Rat.cast_le (K := ℝ)).mpr hv
  push_cast at hv'
  nlinarith

/-! ## The edge `[1 − 1/N, 1]` -/

theorem vConvAM_edge {N : ℕ} (hN : 2 ≤ N) {vlo : ℝ} (hv0 : 0 ≤ vlo)
    (hv : ∀ y ∈ Set.Icc ((1 : ℝ) / 2 - 1 / N) (1 / 2), vlo ≤ vAM y) :
    ∀ x ∈ Set.Icc ((1 : ℝ) - 1 / N) 1, vlo ^ 2 * (1 - x) ≤ vConvAM x := by
  intro x hx
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hab : -(1 : ℝ) / 2 ≤ 1 / 2 - x := by linarith [hx.2]
  have hc : vlo ^ 2 * (1 - x) = ∫ _ in (-(1:ℝ)/2)..(1/2 - x), vlo ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hc]
  unfold vConvAM
  refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
    ((vAM_continuous.mul (vAM_continuous.comp (continuous_id.add continuous_const))).intervalIntegrable _ _) ?_
  intro t ht
  have h1 : vlo ≤ vAM t := by
    rw [← vAM_even]
    refine hv (-t) ⟨?_, ?_⟩
    · have : (1 : ℝ) / 2 - 1 / N ≤ x - 1 / 2 := by linarith [hx.1]
      linarith [ht.2]
    · linarith [ht.1]
  have h2 : vlo ≤ vAM (t + x) := by
    refine hv (t + x) ⟨?_, ?_⟩
    · have : (1 : ℝ) / 2 - 1 / N ≤ x - 1 / 2 := by linarith [hx.1]
      linarith [ht.1]
    · linarith [ht.2]
  rw [sq]
  exact mul_le_mul h1 h2 hv0 (hv0.trans h1)

/-- the edge check: the line `N y (1 − x)` against `vlo² (1 − x) / ZQ` -/
def edgeOk (N : ℕ) (y vlo : ℚ) : Bool := decide (0 < ZI.1) && decide (N * y * ZI.2 ≤ vlo ^ 2)

theorem edge_sound {N sN : ℕ} {y vlo : ℚ} (hN : 2 ≤ N) (hs : 0 < sN) (hv : vloOk N sN vlo = true)
    (h : edgeOk N y vlo = true) : ∀ x ∈ Set.Icc ((1 : ℝ) - 1 / N) 1, (N * y : ℝ) * (1 - x) ≤ qfAM x := by
  intro x hx
  simp only [edgeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hvb := vlo_sound (by omega) hs hv
  have hv0 : (0 : ℝ) < vlo := by
    simp only [vloOk, Bool.and_eq_true, decide_eq_true_eq] at hv; exact_mod_cast hv.1
  have hE := vConvAM_edge hN hv0.le hvb x hx
  have hZ := iv_ZI
  have hZ0 : (0 : ℝ) < ((ZI.1 : ℚ) : ℝ) := by exact_mod_cast h.1
  have hZp : 0 < ZQ := ZQ_pos
  have h2 : (N * y : ℝ) * ZI.2 ≤ (vlo : ℝ) ^ 2 := by exact_mod_cast h.2
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  rw [qfAM, integral_vAM_sq, le_div_iff₀ hZp]
  -- `N y ZQ ≤ N y ZI.2` needs `N y ≥ 0`; otherwise the left side is `≤ 0 ≤ qf`
  rcases le_total 0 ((N : ℝ) * y) with hy | hy
  · calc (N * y : ℝ) * (1 - x) * ZQ ≤ (N * y : ℝ) * (1 - x) * ZI.2 :=
          mul_le_mul_of_nonneg_left hZ.2 (mul_nonneg hy h1x)
      _ = ((N * y : ℝ) * ZI.2) * (1 - x) := by ring
      _ ≤ (vlo : ℝ) ^ 2 * (1 - x) := mul_le_mul_of_nonneg_right h2 h1x
      _ ≤ vConvAM x := hE
  · have : (N * y : ℝ) * (1 - x) * ZQ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hy h1x) hZp.le
    exact this.trans ((mul_nonneg (sq_nonneg _) h1x).trans hE)

/-! ## The piecewise-linear `ĝ` and the whole interval -/

/-- the knot value `y_k` (`y_N = 0`) -/
def yK (Y : List ℚ) (N k : ℕ) : ℚ := if k < N then Y.getD k 0 else 0

/-- `ĝ` on `[0, 1]`: linear between the knots `k/N`, from `y_k` to `y_{k+1}`, with `y_N = 0` -/
def ghatPL (Y : List ℚ) (N : ℕ) (x : ℝ) : ℝ :=
  let k := min (⌊N * x⌋₊) (N - 1)
  (yK Y N k : ℝ) + ((yK Y N (k + 1) : ℝ) - yK Y N k) * (N * x - k)

/-- every check: the knot intervals `0 … N−2` in `S k` cells, the edge interval, the end bound -/
def ghatOk (Y : List ℚ) (N : ℕ) (S : List ℕ) (sN : ℕ) (vlo : ℚ) : Bool :=
  decide (2 ≤ N) && decide (0 < sN) && vloOk N sN vlo && edgeOk N (yK Y N (N - 1)) vlo &&
    (List.range (N - 1)).all fun k => decide (0 < S.getD k 1) && knotOk N (S.getD k 1) k (yK Y N k) (yK Y N (k + 1))

theorem ghat_le_qf {Y : List ℚ} {N : ℕ} {S : List ℕ} {sN : ℕ} {vlo : ℚ} (h : ghatOk Y N S sN vlo = true) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ghatPL Y N x ≤ qfAM x := by
  intro x hx
  simp only [ghatOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hN, hsN⟩, hv⟩, he⟩, hk⟩ := h
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold ghatPL
  dsimp only
  set k := min (⌊(N : ℝ) * x⌋₊) (N - 1) with hkdef
  have hkN : k ≤ N - 1 := min_le_right _ _
  have hk1 : (k : ℝ) ≤ N * x := (by exact_mod_cast min_le_left _ _ : (k : ℝ) ≤ (⌊(N : ℝ) * x⌋₊ : ℝ)).trans
    (Nat.floor_le (mul_nonneg hN'.le hx.1))
  have hk2 : (N : ℝ) * x ≤ k + 1 := by
    rcases le_or_gt (⌊(N : ℝ) * x⌋₊) (N - 1) with hf | hf
    · have : k = ⌊(N : ℝ) * x⌋₊ := by rw [hkdef]; exact min_eq_left hf
      rw [this]; exact (Nat.lt_floor_add_one _).le
    · have : k = N - 1 := by rw [hkdef]; exact min_eq_right hf.le
      rw [this, Nat.cast_sub (by omega)]; push_cast
      nlinarith [hx.2]
  have hxk : x ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N) := by
    constructor
    · rw [div_le_iff₀ hN']; linarith
    · rw [le_div_iff₀ hN']; linarith
  rcases lt_or_eq_of_le hkN with hlt | heq
  · obtain ⟨hs, hko⟩ := hk k hlt
    exact knot_sound (by omega) hs hko x hxk
  · -- the last interval: `ĝ = N y_{N−1} (1 − x)`
    have hyN : yK Y N (k + 1) = 0 := by unfold yK; rw [if_neg (by omega)]
    have hx1 : x ∈ Set.Icc ((1 : ℝ) - 1 / N) 1 := by
      constructor
      · have hkr : (k : ℝ) = N - 1 := by rw [heq, Nat.cast_sub (by omega)]; push_cast; ring
        have e : (1 : ℝ) - 1 / N = (N - 1) / N := by field_simp
        rw [e, div_le_iff₀ hN']
        linarith [hk1]
      · exact hx.2
    have hE := edge_sound hN hsN hv he x hx1
    rw [hyN, heq]
    have e : ((yK Y N (N - 1) : ℚ) : ℝ) + ((((0 : ℚ)) : ℝ) - yK Y N (N - 1)) * (N * x - ((N - 1 : ℕ) : ℝ))
        = (N * (yK Y N (N - 1) : ℚ) : ℝ) * (1 - x) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; exact hE

end AMW.DQ
