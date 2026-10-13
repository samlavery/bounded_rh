import Mathlib

/-!
# AMW/GIv — signed-natural interval arithmetic for kernel evaluation (stage G)

The kernel computes natively with natural-number literals (GMP) and emulates `ℤ` through its constructors, which
costs ~50× more per operation.  So a signed integer is a difference `p − n` of naturals (`SZ`), and an interval is
a pair of them (`IV`), read at the fixed scale `DZ = 10¹⁵`: `IV.Enc I a` says `lo/DZ ≤ a ≤ hi/DZ`.
Every operation is written with the raw `Nat.add`/`Nat.mul`/`Nat.div`/`Nat.ble` and comes with its soundness lemma.
-/

namespace AMW.G

def DZ : ℕ := 1000000000000000

/-- ceiling division -/
def ndivc (a b : ℕ) : ℕ := Nat.div (Nat.sub (Nat.add a b) 1) b

theorem DZ_pos : (0 : ℝ) < DZ := by norm_num [DZ]

theorem ndiv_le (a b : ℕ) (hb : 0 < b) : ((Nat.div a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

theorem le_ndivc (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  unfold ndivc
  have h1 : a + b - 1 = a + (b - 1) := by omega
  have h2 : a ≤ (a + (b - 1)) / b * b := by
    have := Nat.lt_div_mul_add (a := a + (b - 1)) hb
    have h3 : a + (b - 1) < (a + (b - 1)) / b * b + b := by
      have := Nat.lt_div_mul_add (a := a + (b - 1)) hb; linarith
    omega
  show (a : ℝ) ≤ ((Nat.div (Nat.sub (Nat.add a b) 1) b : ℕ) : ℝ) * b
  have e : Nat.div (Nat.sub (Nat.add a b) 1) b = (a + (b - 1)) / b := by
    rw [← h1]; rfl
  rw [e]; exact_mod_cast h2

/-- a signed integer `p − n` -/
structure SZ where
  (p n : ℕ)

namespace SZ
def v (a : SZ) : ℝ := (a.p : ℝ) - a.n
def ofN (m : ℕ) : SZ := ⟨m, 0⟩
def add (a b : SZ) : SZ := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
def sub (a b : SZ) : SZ := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
def neg (a : SZ) : SZ := ⟨a.n, a.p⟩
def mul (a b : SZ) : SZ := ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
def muln (m : ℕ) (a : SZ) : SZ := ⟨Nat.mul m a.p, Nat.mul m a.n⟩
def le (a b : SZ) : Bool := Nat.ble (Nat.add a.p b.n) (Nat.add b.p a.n)
def nonneg (a : SZ) : Bool := Nat.ble a.n a.p
def min (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) b a (a.le b)
def max (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) a b (a.le b)
/-- floor and ceiling of `a / d` -/
def fl (a : SZ) (d : ℕ) : SZ :=
  Bool.rec (motive := fun _ => SZ) ⟨0, ndivc (Nat.sub a.n a.p) d⟩ ⟨Nat.div (Nat.sub a.p a.n) d, 0⟩ (Nat.ble a.n a.p)
def ce (a : SZ) (d : ℕ) : SZ :=
  Bool.rec (motive := fun _ => SZ) ⟨0, Nat.div (Nat.sub a.n a.p) d⟩ ⟨ndivc (Nat.sub a.p a.n) d, 0⟩ (Nat.ble a.n a.p)

@[simp] theorem v_ofN (m : ℕ) : (ofN m).v = m := by simp [v, ofN]
@[simp] theorem v_add (a b : SZ) : (a.add b).v = a.v + b.v := by
  simp only [v, add, Nat.add_eq]; push_cast; ring
@[simp] theorem v_sub (a b : SZ) : (a.sub b).v = a.v - b.v := by
  simp only [v, sub, Nat.add_eq]; push_cast; ring
@[simp] theorem v_neg (a : SZ) : a.neg.v = -a.v := by simp only [v, neg]; ring
@[simp] theorem v_mul (a b : SZ) : (a.mul b).v = a.v * b.v := by
  simp only [v, mul, Nat.add_eq, Nat.mul_eq]; push_cast; ring
@[simp] theorem v_muln (m : ℕ) (a : SZ) : (a.muln m).v = m * a.v := by
  simp only [v, muln, Nat.mul_eq]; push_cast; ring

theorem le_iff (a b : SZ) : a.le b = true ↔ a.v ≤ b.v := by
  simp only [le, Nat.ble_eq, Nat.add_eq, v]
  constructor
  · intro h; have : ((a.p + b.n : ℕ) : ℝ) ≤ ((b.p + a.n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · intro h; have : ((a.p + b.n : ℕ) : ℝ) ≤ ((b.p + a.n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem nonneg_iff (a : SZ) : a.nonneg = true ↔ 0 ≤ a.v := by
  simp only [nonneg, Nat.ble_eq, v, sub_nonneg]; exact_mod_cast Iff.rfl

theorem v_min_le_left (a b : SZ) : (a.min b).v ≤ a.v := by
  unfold min; cases h : a.le b <;> simp only
  · have := (le_iff a b).not.mp (by simp [h]); linarith
  · exact le_rfl

theorem v_min_le_right (a b : SZ) : (a.min b).v ≤ b.v := by
  unfold min; cases h : a.le b <;> simp only
  · exact le_rfl
  · exact (le_iff a b).mp h

theorem le_v_max_left (a b : SZ) : a.v ≤ (a.max b).v := by
  unfold max; cases h : a.le b <;> simp only
  · exact le_rfl
  · exact (le_iff a b).mp h

theorem le_v_max_right (a b : SZ) : b.v ≤ (a.max b).v := by
  unfold max; cases h : a.le b <;> simp only
  · have := (le_iff a b).not.mp (by simp [h]); linarith
  · exact le_rfl

theorem v_fl_le (a : SZ) {d : ℕ} (hd : 0 < d) : (a.fl d).v ≤ a.v / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold fl
  cases h : Nat.ble a.n a.p <;> simp only [v]
  · have h : a.p < a.n := not_le.mp fun hle => by simp [Nat.ble_eq.mpr hle] at h
    have h1 := le_ndivc (Nat.sub a.n a.p) d hd
    have e : ((Nat.sub a.n a.p : ℕ) : ℝ) = (a.n : ℝ) - a.p := by
      rw [show Nat.sub a.n a.p = a.n - a.p from rfl, Nat.cast_sub h.le]
    rw [e] at h1
    have : (a.n : ℝ) / d - a.p / d ≤ ((ndivc (Nat.sub a.n a.p) d : ℕ) : ℝ) := by rw [← sub_div]; exact h1
    rw [sub_div]; push_cast; linarith
  · rw [Nat.ble_eq] at h
    have h1 := ndiv_le (Nat.sub a.p a.n) d hd
    have e : ((Nat.sub a.p a.n : ℕ) : ℝ) = (a.p : ℝ) - a.n := by
      rw [show Nat.sub a.p a.n = a.p - a.n from rfl, Nat.cast_sub h]
    rw [e] at h1
    push_cast; linarith

theorem le_v_ce (a : SZ) {d : ℕ} (hd : 0 < d) : a.v / d ≤ (a.ce d).v := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold ce
  cases h : Nat.ble a.n a.p <;> simp only [v]
  · have h : a.p < a.n := not_le.mp fun hle => by simp [Nat.ble_eq.mpr hle] at h
    have h1 := ndiv_le (Nat.sub a.n a.p) d hd
    have e : ((Nat.sub a.n a.p : ℕ) : ℝ) = (a.n : ℝ) - a.p := by
      rw [show Nat.sub a.n a.p = a.n - a.p from rfl, Nat.cast_sub h.le]
    rw [e] at h1
    have : ((Nat.div (Nat.sub a.n a.p) d : ℕ) : ℝ) ≤ (a.n : ℝ) / d - a.p / d := by rw [← sub_div]; exact h1
    rw [sub_div]; push_cast; linarith
  · rw [Nat.ble_eq] at h
    have h1 := le_ndivc (Nat.sub a.p a.n) d hd
    have e : ((Nat.sub a.p a.n : ℕ) : ℝ) = (a.p : ℝ) - a.n := by
      rw [show Nat.sub a.p a.n = a.p - a.n from rfl, Nat.cast_sub h]
    rw [e] at h1
    push_cast; linarith
end SZ

/-- an interval of signed integers -/
structure IV where
  (lo hi : SZ)

namespace IV
/-- `I` encloses `a` at scale `DZ` -/
def Enc (I : IV) (a : ℝ) : Prop := I.lo.v / DZ ≤ a ∧ a ≤ I.hi.v / DZ

def ofN (a b : ℕ) : IV := ⟨⟨a, 0⟩, ⟨b, 0⟩⟩
def zero : IV := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
def add (I J : IV) : IV := ⟨I.lo.add J.lo, I.hi.add J.hi⟩
def sub (I J : IV) : IV := ⟨I.lo.sub J.hi, I.hi.sub J.lo⟩
def neg (I : IV) : IV := ⟨I.hi.neg, I.lo.neg⟩
/-- multiplication by a natural (exact) -/
def muln (m : ℕ) (I : IV) : IV := ⟨I.lo.muln m, I.hi.muln m⟩
/-- interval product at scale `DZ`, rounded outward -/
def mul (I J : IV) : IV :=
  ⟨SZ.fl (SZ.min (SZ.min (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.min (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ,
   SZ.ce (SZ.max (SZ.max (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.max (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ⟩
/-- product with a nonnegative interval `C` (`0 ≤ C.lo`), rounded outward -/
def mulc (C I : IV) : IV :=
  ⟨SZ.fl (Bool.rec (motive := fun _ => SZ) (C.hi.mul I.lo) (C.lo.mul I.lo) I.lo.nonneg) DZ,
   SZ.ce (Bool.rec (motive := fun _ => SZ) (C.lo.mul I.hi) (C.hi.mul I.hi) I.hi.nonneg) DZ⟩
/-- division by a positive natural, rounded outward -/
def divn (I : IV) (d : ℕ) : IV := ⟨I.lo.fl d, I.hi.ce d⟩
/-- `I / E` at scale `DZ` for `E ∈ [e0, e1] / DZ`, `0 < e0` -/
def divp (I : IV) (e0 e1 : ℕ) : IV :=
  ⟨Bool.rec (motive := fun _ => SZ) ((I.lo.muln DZ).fl e0) ((I.lo.muln DZ).fl e1) I.lo.nonneg,
   Bool.rec (motive := fun _ => SZ) ((I.hi.muln DZ).ce e1) ((I.hi.muln DZ).ce e0) I.hi.nonneg⟩
/-- signed multiple `±m · I` (exact) -/
def scl (ng : Bool) (m : ℕ) (I : IV) : IV := Bool.rec (motive := fun _ => IV) (I.muln m) (I.muln m).neg ng

theorem enc_zero : zero.Enc 0 := by simp [Enc, zero, SZ.v]

theorem enc_add {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.add J).Enc (a + b) := by
  simp only [Enc, add, SZ.v_add, add_div] at *
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem enc_sub {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.sub J).Enc (a - b) := by
  simp only [Enc, sub, SZ.v_sub, sub_div] at *
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem enc_neg {I : IV} {a : ℝ} (hI : I.Enc a) : I.neg.Enc (-a) := by
  simp only [Enc, neg, SZ.v_neg, neg_div] at *
  constructor <;> linarith [hI.1, hI.2]

theorem enc_muln {I : IV} {a : ℝ} (m : ℕ) (hI : I.Enc a) : (I.muln m).Enc (m * a) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp only [Enc, muln, SZ.v_muln] at *
  constructor
  · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hI.1 hm
  · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hI.2 hm

theorem enc_scl {I : IV} {a : ℝ} (ng : Bool) (m : ℕ) (hI : I.Enc a) :
    (I.scl ng m).Enc ((if ng then -1 else 1) * m * a) := by
  cases ng
  · simp only [scl, Bool.false_eq_true, if_false, one_mul]; exact enc_muln m hI
  · simp only [scl, if_true]
    have := enc_neg (enc_muln m hI); rwa [show (-1 : ℝ) * m * a = -(m * a) by ring]

/-- the four corner products bound the product of the enclosed reals -/
theorem mul_mem_corners {p P q Q x y : ℝ} (hx : p ≤ x ∧ x ≤ P) (hy : q ≤ y ∧ y ≤ Q) :
    min (min (p * q) (p * Q)) (min (P * q) (P * Q)) ≤ x * y ∧
      x * y ≤ max (max (p * q) (p * Q)) (max (P * q) (P * Q)) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · have h1 : p * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy0
      rcases le_total 0 p with hp | hp
      · have : p * q ≤ p * y := mul_le_mul_of_nonneg_left hy1 hp
        exact (min_le_left _ _).trans ((min_le_left _ _).trans (this.trans h1))
      · have : p * Q ≤ p * y := mul_le_mul_of_nonpos_left hy2 hp
        exact (min_le_left _ _).trans ((min_le_right _ _).trans (this.trans h1))
    · have h1 : P * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy0
      rcases le_total 0 P with hP | hP
      · have : P * q ≤ P * y := mul_le_mul_of_nonneg_left hy1 hP
        exact (min_le_right _ _).trans ((min_le_left _ _).trans (this.trans h1))
      · have : P * Q ≤ P * y := mul_le_mul_of_nonpos_left hy2 hP
        exact (min_le_right _ _).trans ((min_le_right _ _).trans (this.trans h1))
  · rcases le_total 0 y with hy0 | hy0
    · have h1 : x * y ≤ P * y := mul_le_mul_of_nonneg_right hx2 hy0
      rcases le_total 0 P with hP | hP
      · have : P * y ≤ P * Q := mul_le_mul_of_nonneg_left hy2 hP
        exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_right _ _))
      · have : P * y ≤ P * q := mul_le_mul_of_nonpos_left hy1 hP
        exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_right _ _))
    · have h1 : x * y ≤ p * y := mul_le_mul_of_nonpos_right hx1 hy0
      rcases le_total 0 p with hp | hp
      · have : p * y ≤ p * Q := mul_le_mul_of_nonneg_left hy2 hp
        exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_left _ _))
      · have : p * y ≤ p * q := mul_le_mul_of_nonpos_left hy1 hp
        exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem enc_mul {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.mul J).Enc (a * b) := by
  have hD := DZ_pos
  have hD0 : 0 < DZ := by norm_num [DZ]
  have hc := mul_mem_corners (x := a * DZ) (y := b * DZ)
    ⟨(div_le_iff₀ hD).mp hI.1, (le_div_iff₀ hD).mp hI.2⟩ ⟨(div_le_iff₀ hD).mp hJ.1, (le_div_iff₀ hD).mp hJ.2⟩
  unfold Enc mul
  constructor
  · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hD0) hD.le).trans ?_
    rw [div_div, div_le_iff₀ (by positivity)]
    have hm : (SZ.min (SZ.min (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.min (I.hi.mul J.lo) (I.hi.mul J.hi))).v
        ≤ min (min (I.lo.v * J.lo.v) (I.lo.v * J.hi.v)) (min (I.hi.v * J.lo.v) (I.hi.v * J.hi.v)) := by
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
      · rw [← SZ.v_mul]; exact (SZ.v_min_le_left _ _).trans (SZ.v_min_le_left _ _)
      · rw [← SZ.v_mul]; exact (SZ.v_min_le_left _ _).trans (SZ.v_min_le_right _ _)
      · rw [← SZ.v_mul]; exact (SZ.v_min_le_right _ _).trans (SZ.v_min_le_left _ _)
      · rw [← SZ.v_mul]; exact (SZ.v_min_le_right _ _).trans (SZ.v_min_le_right _ _)
    calc _ ≤ _ := hm
      _ ≤ a * DZ * (b * DZ) := hc.1
      _ = a * b * (DZ * DZ) := by ring
  · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hD0) hD.le)
    rw [div_div, le_div_iff₀ (by positivity)]
    have hm : max (max (I.lo.v * J.lo.v) (I.lo.v * J.hi.v)) (max (I.hi.v * J.lo.v) (I.hi.v * J.hi.v))
        ≤ (SZ.max (SZ.max (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.max (I.hi.mul J.lo) (I.hi.mul J.hi))).v := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · rw [← SZ.v_mul]; exact (SZ.le_v_max_left _ _).trans (SZ.le_v_max_left _ _)
      · rw [← SZ.v_mul]; exact (SZ.le_v_max_right _ _).trans (SZ.le_v_max_left _ _)
      · rw [← SZ.v_mul]; exact (SZ.le_v_max_left _ _).trans (SZ.le_v_max_right _ _)
      · rw [← SZ.v_mul]; exact (SZ.le_v_max_right _ _).trans (SZ.le_v_max_right _ _)
    calc a * b * (DZ * DZ) = a * DZ * (b * DZ) := by ring
      _ ≤ _ := hc.2
      _ ≤ _ := hm

theorem enc_mulc {C I : IV} {c a : ℝ} (hC : C.Enc c) (hC0 : 0 ≤ C.lo.v) (hI : I.Enc a) : (C.mulc I).Enc (c * a) := by
  have hD := DZ_pos
  have hD0 : 0 < DZ := by norm_num [DZ]
  have hc0 : 0 ≤ c := (div_nonneg hC0 hD.le).trans hC.1
  obtain ⟨hc1, hc2⟩ := hC; obtain ⟨ha1, ha2⟩ := hI
  have hc1' := (div_le_iff₀ hD).mp hc1; have hc2' := (le_div_iff₀ hD).mp hc2
  have ha1' := (div_le_iff₀ hD).mp ha1; have ha2' := (le_div_iff₀ hD).mp ha2
  unfold Enc mulc
  constructor
  · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hD0) hD.le).trans ?_
    rw [div_div, div_le_iff₀ (by positivity)]
    cases h : I.lo.nonneg <;> simp only [SZ.v_mul]
    · have hn : I.lo.v < 0 := by have := (SZ.nonneg_iff I.lo).not.mp (by simp [h]); linarith
      -- C.hi · lo ≤ c·DZ · a·DZ  (lo < 0, c·DZ ≤ C.hi)
      rcases le_total 0 a with ha | ha
      · nlinarith
      · nlinarith
    · have hn := (SZ.nonneg_iff I.lo).mp h
      nlinarith
  · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hD0) hD.le)
    rw [div_div, le_div_iff₀ (by positivity)]
    cases h : I.hi.nonneg <;> simp only [SZ.v_mul]
    · have hn : I.hi.v < 0 := by have := (SZ.nonneg_iff I.hi).not.mp (by simp [h]); linarith
      nlinarith
    · have hn := (SZ.nonneg_iff I.hi).mp h
      rcases le_total 0 a with ha | ha
      · nlinarith
      · nlinarith

theorem enc_divn {I : IV} {a : ℝ} {d : ℕ} (hd : 0 < d) (hI : I.Enc a) : (I.divn d).Enc (a / d) := by
  have hD := DZ_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold Enc divn
  constructor
  · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hd) hD.le).trans ?_
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hI.1 hd'.le
  · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hd) hD.le)
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hI.2 hd'.le

theorem enc_divp {I : IV} {a e : ℝ} {e0 e1 : ℕ} (he0 : 0 < e0) (h0 : (e0 : ℝ) / DZ ≤ e) (h1 : e ≤ (e1 : ℝ) / DZ)
    (hI : I.Enc a) : (I.divp e0 e1).Enc (a / e) := by
  have hD := DZ_pos
  have hD0 : 0 < DZ := by norm_num [DZ]
  have he0' : (0 : ℝ) < e0 := by exact_mod_cast he0
  have he1 : 0 < e1 := by
    have : (e0 : ℝ) ≤ e1 := by
      have := h0.trans h1; rwa [div_le_div_iff_of_pos_right hD] at this
    exact_mod_cast he0'.trans_le this
  have he1' : (0 : ℝ) < e1 := by exact_mod_cast he1
  have hepos : 0 < e := (div_pos he0' hD).trans_le h0
  have h0' : (e0 : ℝ) ≤ e * DZ := (div_le_iff₀ hD).mp h0
  have h1' : e * DZ ≤ e1 := (le_div_iff₀ hD).mp h1
  obtain ⟨ha1, ha2⟩ := hI
  unfold Enc divp
  constructor
  · cases h : I.lo.nonneg <;> simp only
    · have hn : I.lo.v < 0 := by have := (SZ.nonneg_iff I.lo).not.mp (by simp [h]); linarith
      refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ he0) hD.le).trans ?_
      rw [SZ.v_muln, div_div, div_le_div_iff₀ (by positivity) hepos]
      -- lo·DZ·e ≤ a·(e0·DZ), from lo/DZ ≤ a and lo < 0, e0 ≤ e·DZ
      have := (div_le_iff₀ hD).mp ha1
      nlinarith
    · have hn := (SZ.nonneg_iff I.lo).mp h
      refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ he1) hD.le).trans ?_
      rw [SZ.v_muln, div_div, div_le_div_iff₀ (by positivity) hepos]
      have := (div_le_iff₀ hD).mp ha1
      nlinarith
  · cases h : I.hi.nonneg <;> simp only
    · have hn : I.hi.v < 0 := by have := (SZ.nonneg_iff I.hi).not.mp (by simp [h]); linarith
      refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ he1) hD.le)
      rw [SZ.v_muln, div_div, div_le_div_iff₀ hepos (by positivity)]
      have := (le_div_iff₀ hD).mp ha2
      nlinarith
    · have hn := (SZ.nonneg_iff I.hi).mp h
      refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ he0) hD.le)
      rw [SZ.v_muln, div_div, div_le_div_iff₀ hepos (by positivity)]
      have := (le_div_iff₀ hD).mp ha2
      nlinarith
end IV

end AMW.G
