import AMW.PCellTZ

/-! ###### polytope cells: the zero-order tangent extension (Z), generic (bridge-port)

A tangent's validity beyond its certified convex region `[za, zb]`, on `[zb, U]` (and on `[L, za]`), comes from the
derivative table (`tcheck`). Failing that, it comes from the pyramid table, on `n` equal integer pieces of the range.
* The line of value `v = lo32 X` (`≤ w(p)`) and slope the point claim (`(2·10⁹ − M)/U1` on the right, `(P − 2·10⁹)/U1`
  on the left) must lie below `lb(x0, x1)` at both ends of every nondegenerate piece `[x0, x1]`.
* A line is maximised at an endpoint (`line_le_ends`), and on the right of `p` the tangent `w(p) + w'(p)(s − p)`, with
  `v` in place of `w(p)`, lies below that line, so the tangent is below `w` there.
The tangent's claim becomes the value form `v + w'(p)(s − p) ≤ w(s)` on `[L, U]` (`tangent_valZ`), which is what a
minorant term consumes (`mterm_minV`). ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- the line at distance `x` from `p` against the read `lbv`, all times `SC · 10¹⁰`: value `v`, slope coefficient
`2·10⁹ − c` per `U1` (its two signs apart) -/
def zpt (v c x lbv : ℕ) : Bool :=
  Nat.ble (Nat.add (Nat.mul v 32768) (Nat.mul (Nat.mul 10 (Nat.sub 2000000000 c)) x))
    (Nat.add (Nat.mul lbv 32768) (Nat.mul (Nat.mul 10 (Nat.sub c 2000000000)) x))

/-- one piece `[x0, x1]` (a degenerate piece needs nothing); `right`: the piece lies right of `p` -/
def zpc (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (forceB (lb top bk x0 x1) fun lbv =>
      Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
        (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
    true (Nat.ble x1 x0)

/-- the end of piece `k` of the `n` equal pieces of `[a, b]` -/
def zpe (a b n k : ℕ) : ℕ := Nat.add a (Nat.div (Nat.mul (Nat.sub b a) k) n)

/-- every piece of `[a, b]` -/
def zside (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
  iall (fun k => zpc top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n

/-- the zero-order extension tried on 1 piece, then on 2 pieces, then on `n` (each alternative sound on its own; the
first two are cheap sufficient checks that pass for most tangents, the last is the sizer's check) -/
def zsideF (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
  zside top bk v c p a b 1 right || zside top bk v c p a b 2 right || zside top bk v c p a b n right

/-- the tangent check with the zero-order extension as a third alternative on each side -/
def tcheckZ (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k) || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X))))
        || zsideF top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) U n true)
      && (Nat.ble (rgA R k) L || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X))))
        || zsideF top bk (lo32 X) (lo32 (hi32 X)) p L (rgA R k) n false)

/-- with the one-point case (`L = U = p`, both slope claims present) -/
def tcheckPZ (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tcheckZ R top bk n L U p X EU ED)
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) (Nat.beq L U && Nat.beq L p)

/-! ### the line below the pyramid on the pieces -/

/-- a line below `c` at both ends of `[a, b]` is below `c` on it -/
theorem line_le_ends {v d p a b c x : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (ha : v + d * (a - p) ≤ c)
    (hb : v + d * (b - p) ≤ c) : v + d * (x - p) ≤ c := by
  rcases le_total 0 d with h | h
  · nlinarith [mul_le_mul_of_nonneg_left hx2 h]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 h]

/-- some nondegenerate piece of a sequence of ends covers each point between the first end and the `m`-th -/
theorem pieces_cover (e : ℕ → ℝ) : ∀ m : ℕ, ∀ s : ℝ, e 0 ≤ s → s ≤ e m → e 0 < e m →
    ∃ k < m, e k < e (k + 1) ∧ e k ≤ s ∧ s ≤ e (k + 1)
  | 0, _, _, _, h => absurd h (lt_irrefl _)
  | m + 1, s, h0, hm, hlt => by
    by_cases h1 : s ≤ e m
    · by_cases h2 : e 0 < e m
      · obtain ⟨k, hk, hk'⟩ := pieces_cover e m s h0 h1 h2
        exact ⟨k, by omega, hk'⟩
      · have hs : s = e m := le_antisymm h1 (by linarith [not_lt.mp h2])
        exact ⟨m, by omega, by rw [← hs]; linarith [not_lt.mp h2], le_of_eq hs.symm, hm⟩
    · exact ⟨m, by omega, by linarith [not_le.mp h1], (not_le.mp h1).le, hm⟩

/-- the real reading of `zpt` -/
theorem zpt_sound {v c x lbv : ℕ} (h : zpt v c x lbv = true) :
    (v : ℝ) * 32768 + 10 * (2000000000 - (c : ℝ)) * x ≤ (lbv : ℝ) * 32768 := by
  unfold zpt at h
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  have h' : ((v * 32768 + 10 * (2000000000 - c) * x : ℕ) : ℝ) ≤ ((lbv * 32768 + 10 * (c - 2000000000) * x : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have e2 : ((c - 2000000000 : ℕ) : ℝ) * x - ((2000000000 - c : ℕ) : ℝ) * x = ((c : ℝ) - 2000000000) * x := by
    rw [← sub_mul, natsub_pair]
  linarith

/-- one piece right of `p`: the tangent in value form is below `w` on it -/
theorem zpiece_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p x0 x1 : ℕ} {w1p : ℝ}
    (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ))
    (hz : zpt v M (Nat.sub x0 p) (lb top bk x0 x1) = true) (hz' : zpt v M (Nat.sub x1 p) (lb top bk x0 x1) = true)
    (hp : p ≤ x0) (h01 : x0 ≤ x1) {s : ℝ} (hs1 : (x0 : ℝ) / SC ≤ s) (hs2 : s ≤ (x1 : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hl := hlb x0 x1 s hs1 hs2
  have h0 := zpt_sound hz
  have h1 := zpt_sound hz'
  rw [Nat.sub_eq, Nat.cast_sub hp] at h0
  rw [Nat.sub_eq, Nat.cast_sub (hp.trans h01)] at h1
  rw [hSC] at hs1 hs2 ⊢
  rw [div_le_iff₀ (by norm_num)] at hs1
  rw [le_div_iff₀ (by norm_num)] at hs2
  rw [div_le_iff₀ (by norm_num)] at hl
  -- the scaled line `v·SC + 10 (2·10⁹ − M)(y − p)` is below `lb·SC` at both ends, so at `y = s·SC`
  have hφ := line_le_ends (v := (v : ℝ) * 32768) (d := 10 * (2000000000 - (M : ℝ))) (p := (p : ℝ))
    (c := (lb top bk x0 x1 : ℝ) * 32768) (by linarith : (x0 : ℝ) ≤ s * 32768) (by linarith : s * 32768 ≤ (x1 : ℝ)) h0 h1
  have hps : (p : ℝ) ≤ s * 32768 := le_trans (by exact_mod_cast hp) (by linarith : (x0 : ℝ) ≤ s * 32768)
  have hw := mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr hps)
  rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
  have e : w1p * (s - (p : ℝ) / 32768) * 10000000000 = 1000000000 * w1p * (s * 32768 - p) * (10 / 32768) := by ring
  nlinarith [hφ, hw, hl, e]

/-- one piece left of `p` -/
theorem zpiece_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p x0 x1 : ℕ} {w1p : ℝ}
    (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p)
    (hz : zpt v P (Nat.sub p x0) (lb top bk x0 x1) = true) (hz' : zpt v P (Nat.sub p x1) (lb top bk x0 x1) = true)
    (hp : x1 ≤ p) (h01 : x0 ≤ x1) {s : ℝ} (hs1 : (x0 : ℝ) / SC ≤ s) (hs2 : s ≤ (x1 : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hl := hlb x0 x1 s hs1 hs2
  have h0 := zpt_sound hz
  have h1 := zpt_sound hz'
  rw [Nat.sub_eq, Nat.cast_sub (h01.trans hp)] at h0
  rw [Nat.sub_eq, Nat.cast_sub hp] at h1
  rw [hSC] at hs1 hs2 ⊢
  rw [div_le_iff₀ (by norm_num)] at hs1
  rw [le_div_iff₀ (by norm_num)] at hs2
  rw [div_le_iff₀ (by norm_num)] at hl
  have h0' : (v : ℝ) * 32768 + 10 * ((P : ℝ) - 2000000000) * ((x0 : ℝ) - p) ≤ (lb top bk x0 x1 : ℝ) * 32768 := by
    linarith
  have h1' : (v : ℝ) * 32768 + 10 * ((P : ℝ) - 2000000000) * ((x1 : ℝ) - p) ≤ (lb top bk x0 x1 : ℝ) * 32768 := by
    linarith
  have hφ := line_le_ends (v := (v : ℝ) * 32768) (d := 10 * ((P : ℝ) - 2000000000)) (p := (p : ℝ))
    (c := (lb top bk x0 x1 : ℝ) * 32768) (by linarith : (x0 : ℝ) ≤ s * 32768) (by linarith : s * 32768 ≤ (x1 : ℝ))
    h0' h1'
  have hps : s * 32768 ≤ (p : ℝ) := le_trans (by linarith : s * 32768 ≤ (x1 : ℝ)) (by exact_mod_cast hp)
  have hw := mul_le_mul_of_nonpos_right hP (sub_nonpos.mpr hps)
  rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
  have e : w1p * (s - (p : ℝ) / 32768) * 10000000000 = 1000000000 * w1p * (s * 32768 - p) * (10 / 32768) := by ring
  nlinarith [hφ, hw, hl, e]

theorem zpe_eq (a b n k : ℕ) : zpe a b n k = a + (b - a) * k / n := rfl
theorem zpe_zero (a b n : ℕ) : zpe a b n 0 = a := by rw [zpe_eq]; simp
theorem zpe_n (a b n : ℕ) (hn : 0 < n) (hab : a ≤ b) : zpe a b n n = b := by
  rw [zpe_eq, Nat.mul_div_cancel _ hn]; omega
theorem zpe_ge (a b n k : ℕ) : a ≤ zpe a b n k := by rw [zpe_eq]; exact Nat.le_add_right _ _
theorem zpe_le (a b n k : ℕ) (hab : a ≤ b) (hk : k ≤ n) : zpe a b n k ≤ b := by
  rw [zpe_eq]
  have : (b - a) * k / n ≤ b - a := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hk)
  omega

/-- the right side by pieces: on `[a, b]` with `p ≤ a < b` -/
theorem zside_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p a b n : ℕ} {w1p : ℝ}
    (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ)) (h : zside top bk v M p a b n true = true)
    (hpa : p ≤ a) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  have hSC := SC_pos
  set e : ℕ → ℝ := fun k => ((zpe a b n k : ℕ) : ℝ) / SC with he
  have e0 : e 0 = (a : ℝ) / SC := by simp only [he, zpe_zero]
  have en : e n = (b : ℝ) / SC := by simp only [he, zpe_n a b n hn hab.le]
  obtain ⟨k, hk, hlt, hk1, hk2⟩ := pieces_cover e n s (e0 ▸ hs1) (en ▸ hs2)
    (by rw [e0, en]; exact div_lt_div_of_pos_right (by exact_mod_cast hab) hSC)
  have hpc := iall_true h k hk
  beta_reduce at hpc
  have hlt' : zpe a b n k < zpe a b n (Nat.add k 1) := by
    have : ((zpe a b n k : ℕ) : ℝ) < ((zpe a b n (k + 1) : ℕ) : ℝ) := (div_lt_div_iff_of_pos_right hSC).mp hlt
    exact_mod_cast this
  unfold zpc at hpc
  rw [show Nat.ble (zpe a b n (Nat.add k 1)) (zpe a b n k) = false from
    Bool.eq_false_iff.mpr fun e' => absurd (Nat.le_of_ble_eq_true e') (Nat.not_le.mpr hlt'), forceB_eq] at hpc
  simp only [Bool.and_eq_true] at hpc
  exact zpiece_right hlb hM hpc.1 hpc.2 (hpa.trans (zpe_ge a b n k)) hlt'.le hk1 hk2

/-- the left side by pieces: on `[a, b]` with `a < b ≤ p` -/
theorem zside_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p a b n : ℕ} {w1p : ℝ}
    (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p) (h : zside top bk v P p a b n false = true)
    (hbp : b ≤ p) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  have hSC := SC_pos
  set e : ℕ → ℝ := fun k => ((zpe a b n k : ℕ) : ℝ) / SC with he
  have e0 : e 0 = (a : ℝ) / SC := by simp only [he, zpe_zero]
  have en : e n = (b : ℝ) / SC := by simp only [he, zpe_n a b n hn hab.le]
  obtain ⟨k, hk, hlt, hk1, hk2⟩ := pieces_cover e n s (e0 ▸ hs1) (en ▸ hs2)
    (by rw [e0, en]; exact div_lt_div_of_pos_right (by exact_mod_cast hab) hSC)
  have hpc := iall_true h k hk
  beta_reduce at hpc
  have hlt' : zpe a b n k < zpe a b n (Nat.add k 1) := by
    have : ((zpe a b n k : ℕ) : ℝ) < ((zpe a b n (k + 1) : ℕ) : ℝ) := (div_lt_div_iff_of_pos_right hSC).mp hlt
    exact_mod_cast this
  unfold zpc at hpc
  rw [show Nat.ble (zpe a b n (Nat.add k 1)) (zpe a b n k) = false from
    Bool.eq_false_iff.mpr fun e' => absurd (Nat.le_of_ble_eq_true e') (Nat.not_le.mpr hlt'), forceB_eq] at hpc
  simp only [Bool.and_eq_true] at hpc
  exact zpiece_left hlb hP hpc.1 hpc.2 ((zpe_le a b n (k + 1) hab.le (by omega)).trans hbp) hlt'.le hk1 hk2

theorem zsideF_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p a b n : ℕ} {w1p : ℝ}
    (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ)) (h : zsideF top bk v M p a b n true = true)
    (hpa : p ≤ a) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  unfold zsideF at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact zside_right hlb hM h hpa hab (by norm_num) hs1 hs2
  · exact zside_right hlb hM h hpa hab (by norm_num) hs1 hs2
  · exact zside_right hlb hM h hpa hab hn hs1 hs2

theorem zsideF_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p a b n : ℕ} {w1p : ℝ}
    (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p) (h : zsideF top bk v P p a b n false = true)
    (hbp : b ≤ p) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
    (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
  unfold zsideF at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact zside_left hlb hP h hbp hab (by norm_num) hs1 hs2
  · exact zside_left hlb hP h hbp hab (by norm_num) hs1 hs2
  · exact zside_left hlb hP h hbp hab hn hs1 hs2

/-! ### the tangent in value form -/

/-- a tangent's value-form claim on `[L, U]`: `p` inside, the slope claims, and `v + w'(p)(s − p) ≤ w(s)` -/
def TVal (f : ℕ → ℕ) (L U p : ℕ) : Prop :=
  L ≤ p ∧ p ≤ U ∧ (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) ∧
    1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) ∧
    ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
      (lo32 (f p) : ℝ) / 10000000000 + w1 ((p : ℝ) / SC) * (s - (p : ℝ) / SC) ≤ wfun s

/-- the old check gives the value form -/
theorem tval_of_tcheckP {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) {L U p : ℕ}
    (h : tcheckP R L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p) = true) : TVal f L U p := by
  have hLpU : L ≤ p ∧ p ≤ U := by
    have h' := h
    unfold tcheckP tcheck at h'
    rw [forceB_eq] at h'
    cases hc : (Nat.beq L U && Nat.beq L p)
    · rw [hc] at h'
      simp only [Bool.and_eq_true, Nat.ble_eq] at h'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hLp⟩, hpU⟩, _⟩, _⟩, _⟩, _⟩ := h'
      exact ⟨hLp, hpU⟩
    · simp only [Bool.and_eq_true, Nat.beq_eq] at hc
      omega
  have hLU : (L : ℝ) / SC ≤ (U : ℝ) / SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hLpU.1.trans hLpU.2) SC_pos.le
  obtain ⟨hLp, hpU, hv, hP, hM, -⟩ := tangent_certP hD hpt hR L U p h ((L : ℝ) / SC) le_rfl hLU
  refine ⟨hLp, hpU, hP, hM, fun s hs1 hs2 => ?_⟩
  have := (tangent_certP hD hpt hR L U p h s hs1 hs2).2.2.2.2.2
  linarith

/-- the check with the zero-order extension gives the value form -/
theorem tangent_valZ {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {n L U p : ℕ} (hn : 0 < n)
    (h : tcheckPZ R top bk n L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p) = true) : TVal f L U p := by
  have hSC := SC_pos
  have hU1 := U1_posR
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have cast_le : ∀ {m n : ℕ}, m ≤ n → (m : ℝ) / SC ≤ (n : ℝ) / SC := fun hmn =>
    div_le_div_of_nonneg_right (by exact_mod_cast hmn) hSC.le
  unfold tcheckPZ at h
  cases hc : (Nat.beq L U && Nat.beq L p)
  case true =>
    -- the one-point range: the tangent at `p` is `w` itself
    rw [hc] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc h
    obtain ⟨hLU, hLp⟩ := hc
    subst hLU; subst hLp
    have hp := hpt L
    obtain ⟨-, hPq⟩ := hp.2.1 (by omega)
    obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨le_rfl, le_rfl, by linarith, by linarith, fun s hs1 hs2 => ?_⟩
    rw [le_antisymm hs2 hs1, sub_self, mul_zero, add_zero]; exact hp.1
  rw [hc] at h
  unfold tcheckZ at h
  rw [forceB_eq] at h
  unfold treadU treadD at h
  rw [forceR_eq, forceR_eq] at h
  set k := Nat.shiftRight (Nat.add p 16384) 15 with hkdef
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hap⟩, hpb⟩, hLp⟩, hpU⟩, hP1⟩, hM1⟩, hup⟩, hdn⟩ := h
  have hp := hpt p
  obtain ⟨hkp, hPq⟩ := hp.2.1 (by omega)
  obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  have hP : (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) := by linarith
  have hM : 1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) := by linarith
  have hc := rg_conv hR hk (by omega)
  have hap' := cast_le hap
  have hpb' := cast_le hpb
  set za : ℝ := ((rgA R k : ℕ) : ℝ) / SC
  set zb : ℝ := ((rgB R k : ℕ) : ℝ) / SC
  set q : ℝ := (p : ℝ) / SC
  set v : ℝ := (lo32 (f p) : ℝ) / 10000000000
  have hv : v ≤ wfun q := hp.1
  -- inside the region: the exact tangent, by convexity
  have hmid : ∀ s, za ≤ s → s ≤ zb → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    have := ext_tangent (za := za) (zb := zb) (L := za) (U := zb) hc hap' hpb'
      (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
      (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
      hap' hpb' h1 h2
    linarith
  -- right of the region
  have hright : ∀ s, zb ≤ s → s ≤ (U : ℝ) / SC → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    rcases hup with (hub | ⟨he1, he2⟩) | hz
    · exact hmid s (le_trans hap' (le_trans hpb' h1)) (le_trans h2 (cast_le hub))
    · -- the derivative read: the exact tangent on `[za, U]`
      have hUb : ¬ U ≤ rgB R k ∨ U ≤ rgB R k := (em _).symm
      rcases hUb with hUb | hUb
      · have hb' : Nat.ble U (rgB R k) = false := Bool.eq_false_iff.mpr (fun e => hUb (Nat.le_of_ble_eq_true e))
        rw [hb'] at he1 he2
        have hR' : ∀ x : ℝ, zb ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ w1 q ≤ w1 x := by
          intro x hx1 hx2
          have hb := (hD _ U x hx1 hx2).1 (by simp only at he1; omega)
          obtain ⟨hkx, hbx⟩ := hb
          simp only [fD, ↓reduceIte] at hbx
          rw [div_le_iff₀ hU1, eU] at hbx
          refine ⟨hkx, ?_⟩
          have : (4000000000 : ℝ) ≤ (lo32 (lbDr tD bD (rgB R k) U) : ℝ) + (hi32 (hi32 (f p)) : ℝ) := by
            simp only [Nat.add_eq] at he2; exact_mod_cast he2
          linarith
        have := ext_tangent (za := za) (zb := zb) (L := za) (U := (U : ℝ) / SC) hc hap' hpb' hR'
          (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
            by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
          hap' (cast_le hpU) (le_trans hap' (le_trans hpb' h1)) h2
        linarith
      · exact hmid s (le_trans hap' (le_trans hpb' h1)) (le_trans h2 (cast_le hUb))
    · -- the zero-order extension
      rcases lt_or_ge (rgB R k) U with hbU | hbU
      · exact zsideF_right hlb hM hz hpb hbU hn h1 h2
      · exact hmid s (le_trans hap' (le_trans hpb' h1)) (le_trans h2 (cast_le hbU))
  -- left of the region
  have hleft : ∀ s, (L : ℝ) / SC ≤ s → s ≤ za → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    rcases hdn with (haL | ⟨he1, he2⟩) | hz
    · exact hmid s (le_trans (cast_le haL) h1) (le_trans h2 (le_trans hap' hpb'))
    · rcases (em (rgA R k ≤ L)) with haL | haL
      · exact hmid s (le_trans (cast_le haL) h1) (le_trans h2 (le_trans hap' hpb'))
      · have hb' : Nat.ble (rgA R k) L = false := Bool.eq_false_iff.mpr (fun e => haL (Nat.le_of_ble_eq_true e))
        rw [hb'] at he1 he2
        have hL' : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 q := by
          intro x hx1 hx2
          have hb := (hD L _ x hx1 hx2).2 (by simp only at he1; omega)
          obtain ⟨hkx, hbx⟩ := hb
          simp only [fD, ↓reduceIte, Bool.false_eq_true] at hbx
          rw [div_le_iff₀ hU1, eU] at hbx
          refine ⟨hkx, ?_⟩
          have : (4000000000 : ℝ) ≤ (hi32 (lbDr tD bD L (rgA R k)) : ℝ) + (lo32 (hi32 (f p)) : ℝ) := by
            simp only [Nat.add_eq] at he2; exact_mod_cast he2
          linarith
        have := ext_tangent (za := za) (zb := zb) (L := (L : ℝ) / SC) (U := zb) hc hap' hpb'
          (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
            by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
          hL' (cast_le hLp) hpb' h1 (le_trans h2 (le_trans hap' hpb'))
        linarith
    · rcases lt_or_ge L (rgA R k) with hLa | hLa
      · exact zsideF_left hlb hP hz hap hLa hn h1 h2
      · exact hmid s (le_trans (cast_le hLa) h1) (le_trans h2 (le_trans hap' hpb'))
  refine ⟨hLp, hpU, hP, hM, fun s hs1 hs2 => ?_⟩
  rcases le_total s za with h1 | h1
  · exact hleft s hs1 h1
  rcases le_total s zb with h2 | h2
  · exact hmid s h1 h2
  · exact hright s h2 hs2

/-! ### a minorant term from value-form tangents -/

/-- `mterm_minA` with each tangent's validity taken in value form (`TVal`), whichever check produced it -/
theorem mterm_minV {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (L0 L U Uc lc l1 l2 p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hsum : lc + l1 + l2 = 1024)
    (h1 : l1 = 0 ∨ TVal f L U p1) (h2 : l2 = 0 ∨ TVal f L U p2)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (l1 : ℝ) * ((lo32 (hi32 (f p1)) : ℝ) - 2000000000) + (l2 : ℝ) * ((lo32 (hi32 (f p2)) : ℝ) - 2000000000)
        ≤ 1000000000 * D ∧
      32768 * ((lc : ℝ) * (lb top bk L Uc : ℝ) + (l1 : ℝ) * (lo32 (f p1) : ℝ) + (l2 : ℝ) * (lo32 (f p2) : ℝ))
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * ((l1 : ℝ) * ((hi32 (hi32 (f p1)) : ℝ) - 2000000000) * ((p1 : ℝ) - L0)
          + (l2 : ℝ) * ((hi32 (hi32 (f p2)) : ℝ) - 2000000000) * ((p2 : ℝ) - L0))
        ≤ 327680000000000 * 1024 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hlbs := hlb L Uc s hs1 (hs2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hUc) (by norm_num [SC])))
  have hlbs' : (lb top bk L Uc : ℝ) ≤ 10000000000 * wfun s := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hlbs; linarith
  have tang : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal f L U pk) →
      ∃ dk : ℝ, (lk : ℝ) * ((lo32 (hi32 (f pk)) : ℝ) - 2000000000) ≤ 1000000000 * ((lk : ℝ) * dk) ∧
        32768 * ((lk : ℝ) * (lo32 (f pk) : ℝ)) + 327680000000000 * (((lk : ℝ) * dk) * (s - (L0 : ℝ) / 32768))
          + 10 * ((lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
          ≤ 327680000000000 * ((lk : ℝ) * wfun s) := by
    intro lk pk hk
    rcases hk with hk | ⟨hLp, hpU, hP, hM, hval⟩
    · refine ⟨0, by rw [hk]; simp, by rw [hk]; simp⟩
    have htan := hval s hs1 hs2
    rw [hSC] at htan hM hP
    refine ⟨w1 ((pk : ℝ) / 32768), ?_, ?_⟩
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      nlinarith
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      have hpL : (0 : ℝ) ≤ (pk : ℝ) - L0 := sub_nonneg.mpr (by exact_mod_cast hL0.trans hLp)
      have key : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
          + 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0)) ≤ 327680000000000 * wfun s := by
        have e1 : 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
            = 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
              + 10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0)) := by ring
        rw [e1]
        have h3 : 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
            ≤ -(10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0))) := by
          nlinarith [mul_le_mul_of_nonneg_right hM hpL]
        have h4 : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
            ≤ 327680000000000 * wfun s := by
          have := mul_le_mul_of_nonneg_left htan (by norm_num : (0 : ℝ) ≤ 327680000000000)
          nlinarith [this]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left key hl0]
  obtain ⟨d1, hd1, hb1⟩ := tang l1 p1 h1
  obtain ⟨d2, hd2, hb2⟩ := tang l2 p2 h2
  refine ⟨(l1 : ℝ) * d1 + (l2 : ℝ) * d2, by linarith, ?_⟩
  have hsum' : (lc : ℝ) + l1 + l2 = 1024 := by exact_mod_cast hsum
  have hc0 : (0 : ℝ) ≤ lc := Nat.cast_nonneg _
  have hcl := mul_le_mul_of_nonneg_left hlbs' hc0
  have e2 : (327680000000000 : ℝ) * 1024 * wfun s
      = 327680000000000 * ((lc : ℝ) * wfun s) + 327680000000000 * ((l1 : ℝ) * wfun s)
        + 327680000000000 * ((l2 : ℝ) * wfun s) := by rw [← hsum']; ring
  rw [e2]
  nlinarith [hb1, hb2, hcl]

/-- the side conditions of a term with the zero-order extension (`n` pieces) -/
def mokZ (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (n L U l1 l2 p1 p2 : ℕ) :
    Bool :=
  (Nat.beq l1 0 || tcheckPZ R top bk n L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1))
    && (Nat.beq l2 0 || tcheckPZ R top bk n L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2))

/-- one anchored minorant term with the zero-order extension (`mterm_okA` with `mokZ`) -/
theorem mterm_okZ {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {n : ℕ} (hn : 0 < n)
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : mokZ R top bk tD bD f n L U (mw1 κ lam) (mw2 κ lam) p1 p2 = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl f (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk f L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokZ at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  have tv : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheckPZ R top bk n L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      lk = 0 ∨ TVal f L U pk := fun lk pk h => h.imp id (tangent_valZ hlb hD hpt hR hn)
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_minV hlb L0 L U Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 hL0 hUc
    (mw_sum κ lam hl) (tv _ _ h1) (tv _ _ h2) s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal f L U pk) →
      (lk : ℝ) * (((hi32 (hi32 (f pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (f pk)) : ℕ) : ℝ))
        * ((pk - L0 : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (hL0.trans h.1)]
  have e1 := pk _ _ (tv _ _ h1)
  have e2 := pk _ _ (tv _ _ h2)
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

end AMW.Cert.PyrD
