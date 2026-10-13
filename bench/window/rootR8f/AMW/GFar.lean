import AMW.GBase

/-!
# AMW/GFar — soundness of the far sums `F_n` (stage G)

The `j`-th far term is `m_j^(n)(x)` (`m_j = x/(x² − j²)`) away from the near pole and `h_j^(n)(x)`
(`h_j = 1/(2(x + j))`) at it (`2j = k`).  On a cell `[XL, XU] / DZ` that does not meet `j` each is monotone with a
fixed sign, and the integer evaluator reads its magnitude at the endpoints (`a0` rounded down at the endpoint of
least magnitude, `a1` rounded up at the other).  The accumulators then enclose the signed sum.
-/

noncomputable section

open Real

namespace AMW.G

/-- the signed far terms -/
def mf (n : ℕ) (j x : ℝ) : ℝ :=
  if n = 0 then x / (x ^ 2 - j ^ 2) else if n = 1 then -(x ^ 2 + j ^ 2) / (x ^ 2 - j ^ 2) ^ 2
  else 2 * x * (x ^ 2 + 3 * j ^ 2) / (x ^ 2 - j ^ 2) ^ 3
def hf (n : ℕ) (j x : ℝ) : ℝ :=
  if n = 0 then 1 / (2 * (x + j)) else if n = 1 then -1 / (2 * (x + j) ^ 2) else 1 / (x + j) ^ 3
/-- the far term of `j` for the anchor `k` -/
def fv (n k j : ℕ) (x : ℝ) : ℝ := if 2 * j = k then hf n j x else mf n j x

/-- magnitudes, with `d = |x² − j²|` -/
def mmag (n : ℕ) (j x d : ℝ) : ℝ :=
  if n = 0 then x / d else if n = 1 then (x ^ 2 + j ^ 2) / d ^ 2 else 2 * x * (x ^ 2 + 3 * j ^ 2) / d ^ 3
def hmag (n : ℕ) (j x : ℝ) : ℝ :=
  if n = 0 then 1 / (2 * (x + j)) else if n = 1 then 1 / (2 * (x + j) ^ 2) else 1 / (x + j) ^ 3

theorem mf_above {n : ℕ} {j x : ℝ} : mf n j x = (if n = 1 then -1 else 1) * mmag n j x (x ^ 2 - j ^ 2) := by
  unfold mf mmag
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h1 : n = 1
    · subst h1; simp; ring
    · simp [h0, h1]

theorem mf_below {n : ℕ} (hn : n < 3) {j x : ℝ} : mf n j x = -mmag n j x (j ^ 2 - x ^ 2) := by
  unfold mf mmag
  have e : x ^ 2 - j ^ 2 = -(j ^ 2 - x ^ 2) := by ring
  generalize j ^ 2 - x ^ 2 = d at e ⊢
  rw [e]
  interval_cases n
  · simp only [if_true]; rw [div_neg]
  · simp only [one_ne_zero, if_true, if_false]; rw [neg_sq, neg_div]
  · simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false]
    rw [show (-d) ^ 3 = -(d ^ 3) by ring, div_neg]

theorem hf_eq {n : ℕ} {j x : ℝ} : hf n j x = (if n = 1 then -1 else 1) * hmag n j x := by
  unfold hf hmag
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h1 : n = 1
    · subst h1; simp only [one_ne_zero, if_true, if_false]; ring
    · simp [h0, h1]

/-! ## Monotonicity of the magnitudes -/

theorem mmag_above_anti {n : ℕ} (hn : n < 3) {j a b : ℝ} (hj : 0 ≤ j) (ha : j < a) (hab : a ≤ b) :
    mmag n j b (b ^ 2 - j ^ 2) ≤ mmag n j a (a ^ 2 - j ^ 2) := by
  have ha' : 0 < a - j := by linarith
  have hb' : 0 < b - j := by linarith
  have hapj : 0 < a + j := by linarith
  have hbpj : 0 < b + j := by linarith
  have pf : ∀ x : ℝ, j < x → mmag n j x (x ^ 2 - j ^ 2) =
      if n = 0 then (1 / (x - j) + 1 / (x + j)) / 2 else if n = 1 then (1 / (x - j) ^ 2 + 1 / (x + j) ^ 2) / 2
      else 1 / (x - j) ^ 3 + 1 / (x + j) ^ 3 := by
    intro x hx
    have h1 : x - j ≠ 0 := by linarith
    have h2 : x + j ≠ 0 := by linarith
    have h3 : x ^ 2 - j ^ 2 = (x - j) * (x + j) := by ring
    unfold mmag; rw [h3]; split_ifs <;> field_simp <;> ring
  rw [pf b (by linarith), pf a ha]
  have m1 : ∀ p : ℕ, 1 / (b - j) ^ p ≤ 1 / (a - j) ^ p := fun p =>
    one_div_le_one_div_of_le (pow_pos ha' p) (pow_le_pow_left₀ ha'.le (by linarith) p)
  have m2 : ∀ p : ℕ, 1 / (b + j) ^ p ≤ 1 / (a + j) ^ p := fun p =>
    one_div_le_one_div_of_le (pow_pos hapj p) (pow_le_pow_left₀ hapj.le (by linarith) p)
  have m1' := m1 1; have m2' := m2 1; simp only [pow_one] at m1' m2'
  split_ifs
  · linarith
  · linarith [m1 2, m2 2]
  · linarith [m1 3, m2 3]

theorem mmag_below_mono {n : ℕ} (hn : n < 3) {j a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < j) :
    mmag n j a (j ^ 2 - a ^ 2) ≤ mmag n j b (j ^ 2 - b ^ 2) := by
  have hda : 0 < j ^ 2 - a ^ 2 := by nlinarith
  have hdb : 0 < j ^ 2 - b ^ 2 := by nlinarith
  have hd : j ^ 2 - b ^ 2 ≤ j ^ 2 - a ^ 2 := by nlinarith
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  unfold mmag
  interval_cases n <;> simp only [show (1:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 0 by norm_num,
    show (2:ℕ) ≠ 1 by norm_num, if_true, if_false]
  · rw [div_le_div_iff₀ hda hdb]; nlinarith
  · rw [div_le_div_iff₀ (pow_pos hda 2) (pow_pos hdb 2)]
    have e1 : (j ^ 2 - b ^ 2) ^ 2 ≤ (j ^ 2 - a ^ 2) ^ 2 := pow_le_pow_left₀ hdb.le hd 2
    have e2 : a ^ 2 + j ^ 2 ≤ b ^ 2 + j ^ 2 := by linarith
    exact mul_le_mul e2 e1 (by positivity) (by positivity)
  · rw [div_le_div_iff₀ (pow_pos hda 3) (pow_pos hdb 3)]
    have e1 : (j ^ 2 - b ^ 2) ^ 3 ≤ (j ^ 2 - a ^ 2) ^ 3 := pow_le_pow_left₀ hdb.le hd 3
    have e2 : 2 * a * (a ^ 2 + 3 * j ^ 2) ≤ 2 * b * (b ^ 2 + 3 * j ^ 2) := by nlinarith
    have hb0 : 0 ≤ b := ha.trans hab
    exact mul_le_mul e2 e1 (pow_pos hdb 3).le (by positivity)

theorem hmag_anti {n : ℕ} {j a b : ℝ} (ha : 0 < a + j) (hab : a ≤ b) : hmag n j b ≤ hmag n j a := by
  have hb : 0 < b + j := by linarith
  have hle : a + j ≤ b + j := by linarith
  unfold hmag
  split_ifs
  · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · exact one_div_le_one_div_of_le (by have := pow_pos ha 2; linarith) (by nlinarith [pow_le_pow_left₀ ha.le hle 2])
  · exact one_div_le_one_div_of_le (pow_pos ha 3) (pow_le_pow_left₀ ha.le hle 3)

theorem mmag_nonneg {n : ℕ} {j x d : ℝ} (hj : 0 ≤ j) (hx : 0 ≤ x) (hd : 0 < d) : 0 ≤ mmag n j x d := by
  unfold mmag; split_ifs <;> positivity

theorem hmag_nonneg {n : ℕ} {j x : ℝ} (h : 0 < x + j) : 0 ≤ hmag n j x := by
  unfold hmag; split_ifs <;> positivity

/-! ## The accumulators -/

/-- the accumulators enclose `S` (scale `DZ · 10⁹`) -/
def AccEnc (a : Acc) (S : ℝ) : Prop := (a.pl : ℝ) - a.nh ≤ S ∧ S ≤ (a.ph : ℝ) - a.nl

theorem put_enc {a : Acc} {S : ℝ} (h : AccEnc a S) (ng : Bool) (e a0 a1 : ℕ) {m : ℝ}
    (h0 : (a0 : ℝ) ≤ m) (h1 : m ≤ a1) :
    AccEnc (a.put ng e a0 a1) (S + (if ng then -1 else 1) * e * m) := by
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have p0 := mul_le_mul_of_nonneg_left h0 he
  have p1 := mul_le_mul_of_nonneg_left h1 he
  unfold AccEnc at *; obtain ⟨hl, hh⟩ := h
  cases ng <;> simp only [Acc.put, Nat.add_eq, Nat.mul_eq, Bool.false_eq_true, if_true, if_false] <;> push_cast <;>
    constructor <;> nlinarith

theorem mnum_eq0 (X X2 J2 : ℕ) : mnum 0 X X2 J2 = X * DZ ^ 2 := rfl
theorem mnum_eq1 (X X2 J2 : ℕ) : mnum 1 X X2 J2 = (X2 + J2) * DZ ^ 3 := rfl
theorem mnum_eq2 (X X2 J2 : ℕ) : mnum 2 X X2 J2 = 2 * X * (X2 + 3 * J2) * DZ ^ 4 := rfl
theorem hden_eq0 (Y : ℕ) : hden 0 Y = 2 * Y := rfl
theorem hden_eq1 (Y : ℕ) : hden 1 Y = 2 * (Y * Y) := rfl
theorem hden_eq2 (Y : ℕ) : hden 2 Y = Y ^ 3 := rfl

theorem DZr_ne : (DZ : ℝ) ≠ 0 := DZ_pos.ne'

/-- the integer magnitudes are the real ones at the endpoint, times `DZ` -/
theorem mnum_div {n : ℕ} (hn : n < 3) (X : ℕ) (j : ℕ) (d : ℝ) (hd : d = (X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2 ∨
    d = ((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) (hd0 : d ≠ 0) :
    ((mnum n X (X * X) ((j * DZ) * (j * DZ)) : ℕ) : ℝ) / d ^ (n + 1)
      = DZ * mmag n j ((X : ℝ) / DZ) (d / DZ ^ 2) := by
  have hD := DZr_ne
  unfold mmag
  interval_cases n
  · rw [mnum_eq0]; simp only [if_true]; push_cast; field_simp
  · rw [mnum_eq1]; simp only [one_ne_zero, if_true, if_false]; push_cast
    rcases hd with hd | hd <;> (subst hd; push_cast at hd0; field_simp)
  · rw [mnum_eq2]; simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false]; push_cast
    rcases hd with hd | hd <;> (subst hd; push_cast at hd0; field_simp)

theorem hden_div {n : ℕ} (hn : n < 3) (X j : ℕ) (hY : 0 < X + j * DZ) :
    ((DZp (n + 2) : ℕ) : ℝ) / (hden n (X + j * DZ) : ℕ) = DZ * hmag n j ((X : ℝ) / DZ) := by
  have hD := DZr_ne
  have hY' : (0 : ℝ) < ((X + j * DZ : ℕ) : ℝ) := by exact_mod_cast hY
  push_cast at hY'
  unfold hmag DZp
  interval_cases n
  · rw [hden_eq0]; simp only [if_true, Nat.pow_eq]; push_cast; field_simp
  · rw [hden_eq1]; simp only [one_ne_zero, if_true, if_false, Nat.pow_eq]; push_cast; field_simp
  · rw [hden_eq2]; simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false, Nat.pow_eq]
    push_cast; field_simp

theorem sgn_xor (sg b : Bool) : (if xor sg b then (-1 : ℝ) else 1) = (if sg then -1 else 1) * (if b then -1 else 1) := by
  cases sg <;> cases b <;> simp

theorem hneg_eq (n : ℕ) : (if hneg n then (-1 : ℝ) else 1) = (if n = 1 then -1 else 1) := by
  unfold hneg; by_cases h : n = 1
  · subst h; simp
  · have : Nat.beq n 1 = false := by cases hb : Nat.beq n 1; rfl; exact absurd (Nat.eq_of_beq_eq_true hb) h
    simp [this, h]

theorem mneg_true (n : ℕ) : mneg n true = hneg n := by
  unfold mneg hneg; cases Nat.beq n 1 <;> rfl

theorem mneg_false (n : ℕ) : mneg n false = true := by
  unfold mneg; cases Nat.beq n 1 <;> rfl

theorem hden_pos {n : ℕ} (hn : n < 3) {Y : ℕ} (hY : 0 < Y) : 0 < hden n Y := by
  interval_cases n
  · rw [hden_eq0]; omega
  · rw [hden_eq1]; positivity
  · rw [hden_eq2]; positivity

set_option maxHeartbeats 2000000 in
theorem farJ_enc {n k XL XU : ℕ} (hn : n < 3) {x : ℝ} (hxl : (XL : ℝ) / DZ ≤ x) (hxu : x ≤ (XU : ℝ) / DZ)
    {a : Acc} {S : ℝ} (hS : AccEnc a S) (j e : ℕ) (sg : Bool) (hj : 1 ≤ j)
    (hab : 2 * j < k → (j : ℝ) < (XL : ℝ) / DZ) (hbe : k < 2 * j → (XU : ℝ) / DZ < j) :
    AccEnc (farJ n k XL XU (Nat.mul XL XL) (Nat.mul XU XU) a j e sg)
      (S + (if sg then -1 else 1) * e * (DZ * fv n k j x)) := by
  have hD := DZ_pos
  have hD0 : 0 < DZ := by norm_num [DZ]
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hXL0 : (0 : ℝ) ≤ (XL : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  have hx0 : 0 ≤ x := hXL0.trans hxl
  unfold farJ fv
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Nat.pow_eq]
  by_cases hk : 2 * j = k
  · -- the near pole: the half term `h_j`
    have hb : Nat.beq (2 * j) k = true := by rw [hk]; exact Nat.beq_refl k
    simp only [hb, if_pos hk]
    have hY : ∀ X : ℕ, 0 < X + j * DZ := fun X => by have : 0 < j * DZ := Nat.mul_pos hj hD0; omega
    have h0 : ((Nat.div (DZp (n + 2)) (hden n (XU + j * DZ)) : ℕ) : ℝ) ≤ DZ * hmag n j x := by
      refine (ndiv_le _ _ (hden_pos hn (hY XU))).trans ?_
      rw [hden_div hn XU j (hY XU)]
      exact mul_le_mul_of_nonneg_left (hmag_anti (by linarith) hxu) hD.le
    have h1 : DZ * hmag n j x ≤ ((ndivc (DZp (n + 2)) (hden n (XL + j * DZ)) : ℕ) : ℝ) := by
      refine le_trans ?_ (le_ndivc _ _ (hden_pos hn (hY XL)))
      rw [hden_div hn XL j (hY XL)]
      exact mul_le_mul_of_nonneg_left (hmag_anti (by linarith) hxl) hD.le
    have := put_enc hS (xor sg (hneg n)) e _ _ h0 h1
    have key : (if sg then (-1:ℝ) else 1) * e * (DZ * hf n j x)
        = (if xor sg (hneg n) then -1 else 1) * e * (DZ * hmag n j x) := by rw [sgn_xor, hneg_eq, hf_eq]; ring
    rw [key]; exact this
  · have hb : Nat.beq (2 * j) k = false := by
      cases h : Nat.beq (2 * j) k; rfl; exact absurd (Nat.eq_of_beq_eq_true h) hk
    simp only [hb, if_neg hk]
    by_cases hlt : 2 * j < k
    · -- above the pole
      have hb2 : Nat.blt (2 * j) k = true := Nat.blt_eq.mpr hlt
      simp only [hb2]
      have hjx := hab hlt
      have hJ : (((j * DZ : ℕ) : ℝ) / DZ) = j := by push_cast; field_simp
      have hXLJ : j * DZ * (j * DZ) ≤ XL * XL := by
        have : (j : ℝ) * DZ < XL := by rwa [lt_div_iff₀ hD] at hjx
        have h2 : j * DZ ≤ XL := by exact_mod_cast this.le
        exact Nat.mul_le_mul h2 h2
      have hXUJ : j * DZ * (j * DZ) ≤ XU * XU := by
        have : (j : ℝ) * DZ < XU := by
          have := hjx.trans_le (hxl.trans hxu); rwa [lt_div_iff₀ hD] at this
        have h2 : j * DZ ≤ XU := by exact_mod_cast this.le
        exact Nat.mul_le_mul h2 h2
      have dpos : ∀ X : ℕ, (j : ℝ) < (X : ℝ) / DZ → (0 : ℝ) < (X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2 := by
        intro X hX
        have : (j : ℝ) * DZ < X := by rwa [lt_div_iff₀ hD] at hX
        have h1 : (0 : ℝ) < (X : ℝ) - j * DZ := by linarith
        have h2 : (0 : ℝ) < (X : ℝ) + j * DZ := by have := mul_pos (show (0:ℝ) < j by linarith) hD; linarith
        push_cast; nlinarith [mul_pos h1 h2]
      have dsc : ∀ X : ℕ, ((X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2) / DZ ^ 2 = ((X : ℝ) / DZ) ^ 2 - (j : ℝ) ^ 2 := by
        intro X; push_cast; field_simp
      have castd : ∀ X : ℕ, j * DZ * (j * DZ) ≤ X * X →
          (((X * X - j * DZ * (j * DZ)) ^ (n + 1) : ℕ) : ℝ) = ((X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2) ^ (n + 1) := by
        intro X hX; push_cast [Nat.cast_sub hX]; ring
      have hxU : (j : ℝ) < (XU : ℝ) / DZ := hjx.trans_le (hxl.trans hxu)
      have h0 : ((Nat.div (mnum n XU (XU * XU) (j * DZ * (j * DZ))) ((XU * XU - j * DZ * (j * DZ)) ^ Nat.succ n) : ℕ) : ℝ)
          ≤ DZ * mmag n j x (x ^ 2 - j ^ 2) := by
        refine (ndiv_le _ _ (pow_pos (by have := dpos XU hxU; push_cast at this; exact_mod_cast (show (0:ℝ) < ((XU * XU - j * DZ * (j * DZ) : ℕ) : ℝ) by push_cast [Nat.cast_sub hXUJ]; nlinarith)) _)).trans ?_
        rw [castd XU hXUJ, mnum_div hn XU j _ (Or.inl rfl) (dpos XU hxU).ne', dsc]
        exact mul_le_mul_of_nonneg_left (mmag_above_anti hn (by positivity) (hjx.trans_le hxl) hxu) hD.le
      have h1 : DZ * mmag n j x (x ^ 2 - j ^ 2)
          ≤ ((ndivc (mnum n XL (XL * XL) (j * DZ * (j * DZ))) ((XL * XL - j * DZ * (j * DZ)) ^ Nat.succ n) : ℕ) : ℝ) := by
        refine le_trans ?_ (le_ndivc _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((XL * XL - j * DZ * (j * DZ) : ℕ) : ℝ) by push_cast [Nat.cast_sub hXLJ]; have := dpos XL hjx; push_cast at this; nlinarith)) _))
        rw [castd XL hXLJ, mnum_div hn XL j _ (Or.inl rfl) (dpos XL hjx).ne', dsc]
        exact mul_le_mul_of_nonneg_left (mmag_above_anti hn (by positivity) hjx hxl) hD.le
      have := put_enc hS (xor sg (mneg n true)) e _ _ h0 h1
      have key : (if sg then (-1:ℝ) else 1) * e * (DZ * mf n j x)
          = (if xor sg (mneg n true) then -1 else 1) * e * (DZ * mmag n j x (x ^ 2 - j ^ 2)) := by
        rw [sgn_xor, mneg_true, hneg_eq, mf_above]; ring
      rw [key]; exact this
    · -- below the pole
      have hgt : k < 2 * j := by omega
      have hb2 : Nat.blt (2 * j) k = false := by
        cases h : Nat.blt (2 * j) k; rfl; exact absurd (Nat.blt_eq.mp h) hlt
      simp only [hb2]
      have hxj := hbe hgt
      have hXUJ : XU * XU ≤ j * DZ * (j * DZ) := by
        have : (XU : ℝ) < j * DZ := by rwa [div_lt_iff₀ hD] at hxj
        have h2 : XU ≤ j * DZ := by exact_mod_cast this.le
        exact Nat.mul_le_mul h2 h2
      have hXLJ : XL * XL ≤ j * DZ * (j * DZ) := le_trans (Nat.mul_le_mul (by
        have : (XL : ℝ) ≤ XU := by have := hxl.trans hxu; rwa [div_le_div_iff_of_pos_right hD] at this
        exact_mod_cast this) (by
        have : (XL : ℝ) ≤ XU := by have := hxl.trans hxu; rwa [div_le_div_iff_of_pos_right hD] at this
        exact_mod_cast this)) hXUJ
      have dpos : ∀ X : ℕ, (X : ℝ) / DZ < j → (0 : ℝ) < ((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2 := by
        intro X hX
        have : (X : ℝ) < j * DZ := by rwa [div_lt_iff₀ hD] at hX
        have h0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
        have h1 : (0 : ℝ) < (j : ℝ) * DZ - X := by linarith
        have h2 : (0 : ℝ) < (j : ℝ) * DZ + X := by linarith
        push_cast; nlinarith [mul_pos h1 h2]
      have dsc : ∀ X : ℕ, (((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) / DZ ^ 2 = (j : ℝ) ^ 2 - ((X : ℝ) / DZ) ^ 2 := by
        intro X; push_cast; field_simp
      have castd : ∀ X : ℕ, X * X ≤ j * DZ * (j * DZ) →
          (((j * DZ * (j * DZ) - X * X) ^ (n + 1) : ℕ) : ℝ) = (((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) ^ (n + 1) := by
        intro X hX; push_cast [Nat.cast_sub hX]; ring
      have hxL : (XL : ℝ) / DZ < j := (hxl.trans hxu).trans_lt hxj
      have h0 : ((Nat.div (mnum n XL (XL * XL) (j * DZ * (j * DZ))) ((j * DZ * (j * DZ) - XL * XL) ^ Nat.succ n) : ℕ) : ℝ)
          ≤ DZ * mmag n j x (j ^ 2 - x ^ 2) := by
        refine (ndiv_le _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((j * DZ * (j * DZ) - XL * XL : ℕ) : ℝ) by push_cast [Nat.cast_sub hXLJ]; have := dpos XL hxL; push_cast at this; nlinarith)) _)).trans ?_
        rw [castd XL hXLJ, mnum_div hn XL j _ (Or.inr rfl) (dpos XL hxL).ne', dsc]
        exact mul_le_mul_of_nonneg_left (mmag_below_mono hn hXL0 hxl (hxu.trans_lt hxj)) hD.le
      have h1 : DZ * mmag n j x (j ^ 2 - x ^ 2)
          ≤ ((ndivc (mnum n XU (XU * XU) (j * DZ * (j * DZ))) ((j * DZ * (j * DZ) - XU * XU) ^ Nat.succ n) : ℕ) : ℝ) := by
        refine le_trans ?_ (le_ndivc _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((j * DZ * (j * DZ) - XU * XU : ℕ) : ℝ) by push_cast [Nat.cast_sub hXUJ]; have := dpos XU hxj; push_cast at this; nlinarith)) _))
        rw [castd XU hXUJ, mnum_div hn XU j _ (Or.inr rfl) (dpos XU hxj).ne', dsc]
        exact mul_le_mul_of_nonneg_left (mmag_below_mono hn hx0 hxu hxj) hD.le
      have := put_enc hS (xor sg (mneg n false)) e _ _ h0 h1
      have key : (if sg then (-1:ℝ) else 1) * e * (DZ * mf n j x)
          = (if xor sg (mneg n false) then -1 else 1) * e * (DZ * mmag n j x (j ^ 2 - x ^ 2)) := by
        rw [sgn_xor, mneg_false, mf_below hn]; simp
      rw [key]; exact this

/-! ## The fold over the twelve terms -/

/-- the real far sum over a list of terms (scale `10⁹`) -/
def fsum (n k : ℕ) (x : ℝ) : List (ℕ × ℕ × Bool) → ℝ
  | [] => 0
  | (j, e, sg) :: rest => (if sg then -1 else 1) * e * fv n k j x + fsum n k x rest

theorem farAcc_enc {n k XL XU : ℕ} (hn : n < 3) {x : ℝ} (hxl : (XL : ℝ) / DZ ≤ x) (hxu : x ≤ (XU : ℝ) / DZ)
    (hsep : ∀ j : ℕ, 1 ≤ j → (2 * j < k → (j : ℝ) < (XL : ℝ) / DZ) ∧ (k < 2 * j → (XU : ℝ) / DZ < j)) :
    ∀ (L : List (ℕ × ℕ × Bool)), (∀ t ∈ L, 1 ≤ t.1) → ∀ (a : Acc) (S : ℝ), AccEnc a S →
      AccEnc (farAcc n k XL XU (Nat.mul XL XL) (Nat.mul XU XU) L a) (S + DZ * fsum n k x L) := by
  intro L
  induction L with
  | nil => intro _ a S h; simpa [farAcc, fsum] using h
  | cons t rest ih =>
    intro hL a S h
    obtain ⟨j, e, sg⟩ := t
    have hj : 1 ≤ j := hL _ (List.mem_cons_self ..)
    have h1 := farJ_enc hn hxl hxu h j e sg hj (hsep j hj).1 (hsep j hj).2
    have h2 := ih (fun t ht => hL t (List.mem_cons_of_mem _ ht)) _ _ h1
    simp only [farAcc, fsum]
    convert h2 using 1
    ring

theorem CE_pos : ∀ t ∈ CE, 1 ≤ t.1 := by decide

namespace CellA
variable (c : CellA)

theorem RHI_small (h : c.ok = true) : (c.RHI : ℝ) / DZ < 1 / 2 := by
  unfold ok at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  have hTU := h.1.1.2
  have hD := DZ_pos
  have h1 := le_ndivc (Nat.mul PUN c.RHI) E20 (by norm_num [E20])
  have e : ((Nat.mul PUN c.RHI : ℕ) : ℝ) = (PUN : ℝ) * c.RHI := by rw [Nat.mul_eq]; push_cast; ring
  rw [e] at h1
  have h2 : ((ndivc (Nat.mul PUN c.RHI) E20 : ℕ) : ℝ) ≤ DZ := by exact_mod_cast hTU
  have h3 : (PUN : ℝ) * c.RHI ≤ E20 * DZ := by
    have := h1.trans h2; rw [div_le_iff₀ (by norm_num [E20])] at this; linarith
  have hP : (2 : ℝ) * E20 < PUN := by unfold PUN E20; norm_num
  have hE : (0 : ℝ) < E20 := by unfold E20; norm_num
  have hR0 : (0 : ℝ) ≤ c.RHI := Nat.cast_nonneg _
  rw [div_lt_iff₀ hD]
  by_contra hc; push_neg at hc
  have h4 : (PUN : ℝ) * (DZ / 2) ≤ PUN * c.RHI := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5 : 0 < ((PUN : ℝ) / 2 - E20) * DZ := mul_pos (by linarith) hD
  clear h hTU h1 h2 e
  linarith

theorem sep (h : c.ok = true) (j : ℕ) :
    (2 * j < c.k → (j : ℝ) < (c.LLO : ℝ) / DZ) ∧ (c.k < 2 * j → (c.UHI : ℝ) / DZ < j) := by
  have hR := c.RHI_small h
  unfold ok at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hLU, hTU⟩, hside⟩, hE0⟩ := h
  have hD := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hAD := c.AD_div
  have hLU' : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := by
    rw [LLO_div, UHI_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hLU) hSC.le
  cases hs : c.side
  · rw [hs] at hside; simp only [Nat.ble_eq] at hside
    have hk : (c.UHI : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by
      rw [UHI_div]
      have : ((2 * c.UN : ℕ) : ℝ) ≤ ((c.k * SC : ℕ) : ℝ) := by exact_mod_cast hside
      push_cast at this; rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
    have hLA : c.LLO ≤ c.AD := by
      have : (c.LLO : ℝ) / DZ ≤ (c.AD : ℝ) / DZ := by rw [hAD]; linarith
      exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
    have hRe : (c.RHI : ℝ) / DZ = (c.k : ℝ) / 2 - (c.LLO : ℝ) / DZ := by
      simp only [RHI, hs]; rw [show Nat.sub c.AD c.LLO = c.AD - c.LLO from rfl, Nat.cast_sub hLA, sub_div, hAD]
    constructor
    · intro hj
      have : (2 * j + 1 : ℝ) ≤ c.k := by exact_mod_cast hj
      linarith
    · intro hj
      have : (c.k + 1 : ℝ) ≤ 2 * j := by exact_mod_cast hj
      linarith
  · rw [hs] at hside; simp only [Nat.ble_eq] at hside
    have hk : (c.k : ℝ) / 2 ≤ (c.LLO : ℝ) / DZ := by
      rw [LLO_div]
      have : ((c.k * SC : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by exact_mod_cast hside
      push_cast at this; rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
    have hAU : c.AD ≤ c.UHI := by
      have : (c.AD : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := by rw [hAD]; linarith
      exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
    have hRe : (c.RHI : ℝ) / DZ = (c.UHI : ℝ) / DZ - (c.k : ℝ) / 2 := by
      simp only [RHI, hs]; rw [show Nat.sub c.UHI c.AD = c.UHI - c.AD from rfl, Nat.cast_sub hAU, sub_div, hAD]
    constructor
    · intro hj
      have : (2 * j + 1 : ℝ) ≤ c.k := by exact_mod_cast hj
      linarith
    · intro hj
      have : (c.k + 1 : ℝ) ≤ 2 * j := by exact_mod_cast hj
      linarith

/-- the unrolled far sum is the list recursion over `CE` -/
theorem FA_eq (n : ℕ) : c.FA n =
    (let a := farAcc n c.k c.LLO c.UHI (Nat.mul c.LLO c.LLO) (Nat.mul c.UHI c.UHI) CE ⟨0, 0, 0, 0⟩
     IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9) := rfl

/-- the far sum `F_n` is enclosed by `FA n` -/
theorem FA_enc (h : c.ok = true) {n : ℕ} (hn : n < 3) {x : ℝ} (hxl : (c.LLO : ℝ) / DZ ≤ x) (hxu : x ≤ (c.UHI : ℝ) / DZ) :
    (c.FA n).Enc (fsum n c.k x CE / E9) := by
  have hD := DZ_pos
  have hA := farAcc_enc hn hxl hxu (fun j _ => c.sep h j) CE CE_pos ⟨0, 0, 0, 0⟩ 0 (by simp [AccEnc])
  rw [zero_add] at hA
  rw [FA_eq]
  refine IV.enc_divn (by norm_num [E9]) ?_
  obtain ⟨h1, h2⟩ := hA
  constructor
  · simp only [SZ.v]; rw [div_le_iff₀ hD]; linarith
  · simp only [SZ.v]; rw [le_div_iff₀ hD]; linarith

end CellA

end AMW.G
