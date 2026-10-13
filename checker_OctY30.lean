
/-! ###### integer cell pipeline for the pyramid certificate `OctY30` ###### -/

section OctY30Cells

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (key : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000

/-- a cell's endpoints are packed into one key `LN * KB + UN` (every coordinate is below `KB`) -/
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

-- ZDEFS-BEGIN
/-- the scale of the integer bounds -/
def DZ : ℕ := 1000000000000000
def DZ2 : ℕ := 500000000000000
/-- π·10²⁰, below and above -/
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
/-- γ·10¹⁰, below and above -/
def GLN : ℕ := 8274992907
def GUN : ℕ := 8274993018
/-- the Taylor remainder, rounded up at scale `10¹⁵` -/
def ERRD : ℕ := 2262000

/-- floor and ceiling of `a / b` for naturals -/
def ndiv (a b : ℕ) : ℕ := a / b
def ndivc (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `cos (T / DZ)` by the twelve-term Taylor polynomial: positive and negative parts of the
numerator over `3628800 · DZ¹⁰`. -/
def cosP (T : ℕ) : ℕ := 3628800 * DZ^10 + 151200 * T^4 * DZ^6 + 90 * T^8 * DZ^2
def cosN (T : ℕ) : ℕ := 1814400 * T^2 * DZ^8 + 5040 * T^6 * DZ^4 + T^10
def sinP (T : ℕ) : ℕ := 39916800 * T * DZ^10 + 332640 * T^5 * DZ^6 + 110 * T^9 * DZ^2
def sinN (T : ℕ) : ℕ := 6652800 * T^3 * DZ^8 + 7920 * T^7 * DZ^4 + T^11
/-- lower / upper bounds of the polynomial values at scale `DZ` -/
def cosLo (T : ℕ) : ℕ := ndiv (cosP T - cosN T) (3628800 * DZ^9)
def cosHi (T : ℕ) : ℕ := ndivc (cosP T - cosN T) (3628800 * DZ^9)
def sinLo (T : ℕ) : ℕ := ndiv (sinP T - sinN T) (39916800 * DZ^10)
def sinHi (T : ℕ) : ℕ := ndivc (sinP T - sinN T) (39916800 * DZ^10)

/-- floor / ceiling division of an integer by `DZ` -/
def zfdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndiv z.toNat DZ : ℕ) : ℤ) else -((ndivc (-z).toNat DZ : ℕ) : ℤ)
def zcdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndivc z.toNat DZ : ℕ) : ℤ) else -((ndiv (-z).toNat DZ : ℕ) : ℤ)

def imulZZ (e : ℤ) (I : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ e then (e * I.1, e * I.2) else (e * I.2, e * I.1)
def iaddZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 + J.1, I.2 + J.2)
def isubZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 - J.2, I.2 - J.1)

namespace CellN
/-- lower/upper integer bounds (scale `DZ`) of the cell's endpoints -/
def LLO (c : CellN) : ℕ := ndiv (c.LN * DZ) SC
def UHI (c : CellN) : ℕ := ndivc (c.UN * DZ) SC
def AD (c : CellN) : ℕ := c.k * DZ2
def RLO (c : CellN) : ℕ := if c.side then c.LLO - c.AD else c.AD - c.UHI
def RHI (c : CellN) : ℕ := if c.side then c.UHI - c.AD else c.AD - c.LLO
def TLZ (c : CellN) : ℕ := ndiv (PLN * c.RLO) 100000000000000000000
def TUZ (c : CellN) : ℕ := ndivc (PUN * c.RHI) 100000000000000000000
def CLZ (c : CellN) : ℤ := (cosLo c.TUZ : ℤ) - ERRD
def CUZ (c : CellN) : ℤ := (cosHi c.TLZ : ℤ) + ERRD
def SLZ (c : CellN) : ℤ := (sinLo c.TLZ : ℤ) - ERRD
def SUZ (c : CellN) : ℤ := (sinHi c.TUZ : ℤ) + ERRD
def cAZ (c : CellN) : ℤ := (csA c.k).1
def sAZ (c : CellN) : ℤ := (csA c.k).2
def CXZ (c : CellN) : ℤ × ℤ :=
  if c.side then isubZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
  else iaddZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
def SXZ (c : CellN) : ℤ × ℤ :=
  if c.side then iaddZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
  else isubZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
def BLZ (c : CellN) : ℕ := ndiv (PLN * c.LLO) 100000000000000000000
def BUZ (c : CellN) : ℕ := ndivc (PUN * c.UHI) 100000000000000000000
def P2LZ (c : CellN) : ℕ := ndiv (2 * GLN * c.BLZ) 10000000000
def P2UZ (c : CellN) : ℕ := ndivc (2 * GUN * c.BUZ) 10000000000
def TLOZ (c : CellN) : ℤ := zfdiv (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
def THIZ (c : CellN) : ℤ := zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
def NLOZ (c : CellN) : ℤ := max 0 (max (c.CXZ.1 - c.THIZ) (c.TLOZ - c.CXZ.2))
def DHIZ (c : CellN) : ℤ := ((ndivc (2 * c.BUZ * c.BUZ) DZ : ℕ) : ℤ) - DZ
/-- the conditions of the integer check that do not involve the claimed bound -/
def okC (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (DZ * DZ < 2 * c.BLZ * c.BLZ) && decide (0 < c.DHIZ)
/-- the integer check of a claimed bound `WN` -/
def okZ (c : CellN) : Bool :=
  c.okC && decide ((c.WN : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
/-- the bound the pipeline certifies for the cell (0 outside its scope) -/
def WZ (c : CellN) : ℕ :=
  bif c.okC then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0
end CellN
-- ZDEFS-END

end Zeta23Ext.Bridge.ThreePoint

end OctY30Cells

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

-- ZLEMMAS-BEGIN
/-! ### rounding lemmas -/

theorem DZ_pos : (0:ℝ) < DZ := by norm_num [DZ]
theorem DZ_ne : (DZ:ℝ) ≠ 0 := by norm_num [DZ]

theorem ndiv_le (a b : ℕ) (hb : 0 < b) : ((ndiv a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  unfold ndiv
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

theorem le_ndivc (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
  unfold ndivc
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h : a ≤ ((a + b - 1) / b) * b := by
    have := Nat.lt_div_mul_add (a := a + b - 1) hb
    omega
  exact_mod_cast h

theorem zfdiv_le (z : ℤ) : ((zfdiv z : ℤ) : ℝ) ≤ (z : ℝ) / DZ := by
  unfold zfdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact ndiv_le _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (le_ndivc _ _ (by norm_num [DZ]))

theorem le_zcdiv (z : ℤ) : (z : ℝ) / DZ ≤ ((zcdiv z : ℤ) : ℝ) := by
  unfold zcdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact le_ndivc _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (ndiv_le _ _ (by norm_num [DZ]))

/-! ### the Taylor polynomials at scale `DZ` -/

theorem taylorCos_eq (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) = ((cosP T - cosN T : ℕ) : ℝ) / (3628800 * (DZ : ℝ)^10) := by
  rw [Nat.cast_sub h]
  unfold taylorCos cosP cosN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem taylorSin_eq (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) = ((sinP T - sinN T : ℕ) : ℝ) / (39916800 * (DZ : ℝ)^11) := by
  rw [Nat.cast_sub h]
  unfold taylorSin sinP sinN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem cosLo_le (T : ℕ) (h : cosN T ≤ cosP T) :
    ((cosLo T : ℕ) : ℝ) / DZ ≤ taylorCos ((T : ℝ) / DZ) := by
  rw [taylorCos_eq T h]
  unfold cosLo
  have := ndiv_le (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ) ^ 10)
      = (((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ)) * (3628800 * (DZ:ℝ)^9) * DZ := by ring
    _ ≤ ((cosP T - cosN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_cosHi (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) ≤ ((cosHi T : ℕ) : ℝ) / DZ := by
  rw [taylorCos_eq T h]
  unfold cosHi
  have := le_ndivc (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((cosP T - cosN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ)^9) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem sinLo_le (T : ℕ) (h : sinN T ≤ sinP T) :
    ((sinLo T : ℕ) : ℝ) / DZ ≤ taylorSin ((T : ℝ) / DZ) := by
  rw [taylorSin_eq T h]
  unfold sinLo
  have := ndiv_le (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ) ^ 11)
      = (((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ)) * (39916800 * (DZ:ℝ)^10) * DZ := by ring
    _ ≤ ((sinP T - sinN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_sinHi (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) ≤ ((sinHi T : ℕ) : ℝ) / DZ := by
  rw [taylorSin_eq T h]
  unfold sinHi
  have := le_ndivc (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((sinP T - sinN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ)^10) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem ERRD_ge : taylorErr ≤ (ERRD : ℝ) / DZ := by norm_num [taylorErr, ERRD, DZ]

/-! ### interval operations at scale `DZ` -/

theorem imulZZ_sound (e : ℤ) (I : ℤ × ℤ) {f : ℝ} (h1 : (I.1 : ℝ) / DZ ≤ f) (h2 : f ≤ (I.2 : ℝ) / DZ) :
    ((imulZZ e I).1 : ℝ) / DZ ≤ (e : ℝ) * f ∧ (e : ℝ) * f ≤ ((imulZZ e I).2 : ℝ) / DZ := by
  unfold imulZZ
  have hD := DZ_pos
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 he'
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h2 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h1 he'

theorem iaddZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((iaddZ I J).1 : ℝ) / DZ ≤ f + g ∧ f + g ≤ ((iaddZ I J).2 : ℝ) / DZ := by
  unfold iaddZ; simp only; push_cast; rw [add_div, add_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isubZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((isubZ I J).1 : ℝ) / DZ ≤ f - g ∧ f - g ≤ ((isubZ I J).2 : ℝ) / DZ := by
  unfold isubZ; simp only; push_cast; rw [sub_div, sub_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-! ### the integer cell check is sound -/

theorem PLN_le : ((PLN : ℕ) : ℝ) / 100000000000000000000 ≤ Real.pi := by
  have h := pi_lo; norm_num [PLN] at h ⊢; linarith
theorem PUN_ge : Real.pi ≤ ((PUN : ℕ) : ℝ) / 100000000000000000000 := by
  have h := pi_hi; norm_num [PUN] at h ⊢; linarith
theorem GLN_le : ((GLN : ℕ) : ℝ) / 10000000000 ≤ gam := by
  have h := gam_bounds.1; norm_num [GLN] at h ⊢; linarith
theorem GUN_ge : gam ≤ ((GUN : ℕ) : ℝ) / 10000000000 := by
  have h := gam_bounds.2; norm_num [GUN] at h ⊢; linarith

/-- `ndiv a b / DZ ≤ (a / b) / DZ` packaged with a product bound: if `a = p * q` with
`p / P ≤ A` and `q / DZ ≤ B` (all nonnegative) then `ndiv (p*q) P / DZ ≤ A * B`. -/
theorem ndiv_prod_le (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : ((p : ℕ) : ℝ) / P ≤ A)
    (hB : ((q : ℕ) : ℝ) / DZ ≤ B) (hA0 : 0 ≤ ((p : ℕ) : ℝ) / P) (hB0 : 0 ≤ ((q : ℕ) : ℝ) / DZ) :
    ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ A * B := by
  have h := ndiv_le (p * q) P hP
  have hD := DZ_pos
  calc ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ (((p * q : ℕ) : ℝ) / P) / DZ :=
        div_le_div_of_nonneg_right h hD.le
    _ = (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := by push_cast; field_simp
    _ ≤ A * B := mul_le_mul hA hB hB0 (hA0.trans hA)

theorem le_ndivc_prod (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : A ≤ ((p : ℕ) : ℝ) / P)
    (hB : B ≤ ((q : ℕ) : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    A * B ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := by
  have h := le_ndivc (p * q) P hP
  have hD := DZ_pos
  calc A * B ≤ (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = (((p * q : ℕ) : ℝ) / P) / DZ := by push_cast; field_simp
    _ ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := div_le_div_of_nonneg_right h hD.le

set_option maxHeartbeats 4000000 in
theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.okC = true)
    (hW : (w : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 100000000000000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have nG0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 10000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  -- endpoints at scale DZ
  have hLLO : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := ndiv_le (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.LLO
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.UHI : ℕ) : ℝ) / DZ := by
    have := le_ndivc (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.UHI
    push_cast at this ⊢
    rw [le_div_iff₀ hD0]
    calc (c.UN : ℝ) / SC * DZ = (c.UN : ℝ) * DZ / SC := by ring
      _ ≤ _ := this
  have hAD : ((c.AD : ℕ) : ℝ) / DZ = (c.k : ℝ) / 2 := by
    unfold CellN.AD; simp only [DZ, DZ2]; push_cast; ring
  have hL0 : (0:ℝ) ≤ (c.LN : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := hL0.trans hx1
  have hLNUN : (c.LN : ℝ) / SC ≤ (c.UN : ℝ) / SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hLU) hSC.le
  have hkF : c.side = false → (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := fun hs => by
    have : (2 * c.UN : ℝ) ≤ (c.k * SC : ℝ) := by exact_mod_cast hsideF hs
    rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
  have hkT : c.side = true → (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := fun hs => by
    have : (c.k * SC : ℝ) ≤ (2 * c.LN : ℝ) := by exact_mod_cast hsideT hs
    rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
  -- the reduced offset r and the integer bounds RLO ≤ r ≤ RHI
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.RLO : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.RLO
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.UHI c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.LLO with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.RHI : ℕ) : ℝ) / DZ := by
    unfold CellN.RHI
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.LLO ≤ c.AD := by
        have h1 : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.UHI := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.UHI : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  -- θ = π r at scale DZ
  have hTL : ((c.TLZ : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.TLZ
    exact ndiv_prod_le PLN c.RLO _ (by norm_num) PLN_le hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.TUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.TUZ
    exact le_ndivc_prod PUN c.RHI _ (by norm_num) PUN_ge hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.TUZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.TLZ : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  -- Taylor enclosures at the integer endpoints
  have hc1 : ((c.CLZ : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU1
    have h1 := cosLo_le c.TUZ hcP1
    have h2 := ERRD_ge
    unfold CellN.CLZ; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CUZ : ℤ) : ℝ) / DZ := by
    have h := cos_upper hTL0 hTL hθ1
    have h1 := le_cosHi c.TLZ hcP2
    have h2 := ERRD_ge
    unfold CellN.CUZ; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.SLZ : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    have h1 := sinLo_le c.TLZ hsP1
    have h2 := ERRD_ge
    unfold CellN.SLZ; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SUZ : ℤ) : ℝ) / DZ := by
    have h := sin_upper hθ0 hTUr hTU1
    have h1 := le_sinHi c.TUZ hsP2
    have h2 := ERRD_ge
    unfold CellN.SUZ; push_cast; rw [add_div]
    linarith
  -- the shift to the anchor
  have hcs := cos_sin_half c.k
  have hCX : ((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, Bool.false_eq_true, if_false]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, if_true]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hSX : ((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, Bool.false_eq_true, if_false]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, if_true]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  -- π x and 2 γ π x
  have hb1 : ((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.BLZ
    exact ndiv_prod_le PLN c.LLO _ (by norm_num) PLN_le (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.BUZ
    exact le_ndivc_prod PUN c.UHI _ (by norm_num) PUN_ge (hx2.trans hUHI) Real.pi_pos.le hx0
  have hBL0 : (0:ℝ) ≤ ((c.BLZ : ℕ) : ℝ) / DZ := nd0 _
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := (nG0 GLN).trans GLN_le
  have hp1 : ((c.P2LZ : ℕ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) := by
    unfold CellN.P2LZ
    exact ndiv_prod_le (2 * GLN) c.BLZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GLN_le; linarith) hb1 (nG0 _) hBL0
  have hp2 : 2 * gam * (Real.pi * x) ≤ ((c.P2UZ : ℕ) : ℝ) / DZ := by
    unfold CellN.P2UZ
    exact le_ndivc_prod (2 * GUN) c.BUZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GUN_ge; linarith) hb2 (by linarith) hπx0
  have hP2L0 : (0:ℝ) ≤ ((c.P2LZ : ℕ) : ℝ) / DZ := nd0 _
  -- the product 2 γ π x · sin (π x)
  have hT1 : ((c.TLOZ : ℤ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have hz := zfdiv_le (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
    have hmA : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_left _ _
    have hmB : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.TLOZ
    refine (div_le_div_of_nonneg_right hz hD0.le).trans (prod_lo hP2L0 hp1 hp2 hSX.1 ?_ ?_)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ ((c.THIZ : ℤ) : ℝ) / DZ := by
    have hz := le_zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
    have hmA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hmB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.THIZ
    refine (prod_hi hP2L0 hp1 hp2 hSX.2 ?_ ?_).trans (div_le_div_of_nonneg_right hz hD0.le)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  -- the numerator and the denominator
  set N : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) with hNdef
  have hN : ((c.NLOZ : ℤ) : ℝ) / DZ ≤ |N| := by
    have hCX1 := (div_le_iff₀ hD0).mp hCX.1
    have hCX2 := (le_div_iff₀ hD0).mp hCX.2
    have hT1' := (div_le_iff₀ hD0).mp hT1
    have hT2' := (le_div_iff₀ hD0).mp hT2
    have ha1 := mul_le_mul_of_nonneg_right (le_abs_self N) hD0.le
    have ha2 := mul_le_mul_of_nonneg_right (neg_le_abs N) hD0.le
    rw [div_le_iff₀ hD0]
    unfold CellN.NLOZ
    rw [Int.cast_max, Int.cast_max, Int.cast_zero]
    refine max_le (mul_nonneg (abs_nonneg _) hD0.le) (max_le ?_ ?_)
    · push_cast; rw [hNdef] at ha1; linarith
    · push_cast; rw [hNdef] at ha2; linarith
  have hNLO0 : (0:ℝ) ≤ ((c.NLOZ : ℤ) : ℝ) / DZ := by
    unfold CellN.NLOZ; rw [Int.cast_max, Int.cast_zero]
    exact div_nonneg (le_max_left _ _) hD0.le
  have hD' : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
    exact div_pos this hD0
  have hD0' : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have h1 : ((DZ * DZ : ℕ) : ℝ) < ((2 * c.BLZ * c.BLZ : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    have h2 : ((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ) ≤ (Real.pi * x) * (Real.pi * x) :=
      mul_le_mul hb1 hb1 hBL0 hπx0
    have h3 : (1:ℝ) < 2 * (((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ)) := by
      rw [div_mul_div_comm, ← mul_div_assoc, lt_div_iff₀ (mul_pos hD0 hD0)]
      linarith
    rw [pow_two]; linarith
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have h1 := le_ndivc (2 * c.BUZ * c.BUZ) DZ (by norm_num [DZ])
    push_cast at h1
    have h2 : (Real.pi * x) * (Real.pi * x) ≤ ((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ) :=
      mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    have h3 : 2 * (((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ))
        = 2 * (c.BUZ : ℝ) * (c.BUZ : ℝ) / DZ / DZ := by ring
    have h4 := div_le_div_of_nonneg_right h1 hD0.le
    unfold CellN.DHIZ
    push_cast
    rw [sub_div, div_self DZ_ne, pow_two]
    linarith
  have hfin := wfun_ge x (((c.NLOZ : ℤ) : ℝ) / DZ) (((c.DHIZ : ℤ) : ℝ) / DZ) hNLO0 hD' hD0' hDD hN
  have hWr : ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)
      ≤ ((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ) * ((SW : ℕ) : ℝ) := by exact_mod_cast hW
  have hDHpos : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
  have e : (((c.NLOZ : ℤ) : ℝ) / DZ / (((c.DHIZ : ℤ) : ℝ) / DZ))^2
      = (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_div_div_cancel_right₀ DZ_ne]; ring
  have hle : ((w : ℕ) : ℝ) / SW
      ≤ (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_le_div_iff₀ hSW (mul_pos hDHpos hDHpos)]
    calc ((w : ℕ) : ℝ) * (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ))
        = ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) := by ring
      _ ≤ _ := hWr
  rw [← e] at hle
  exact hle.trans hfin

/-- a claimed bound that passes the integer check is sound -/
theorem cellN_soundZ (c : CellN) (h : c.okZ = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okZ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact cellN_soundZ' c c.WN h.1 h.2 x hx1 hx2

/-- the computed bound is sound: no claimed value, the pipeline's own quotient -/
theorem cellN_soundWZ (c : CellN) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WZ : ℝ) / SW ≤ wfun x := by
  have key : ∀ b : Bool, c.okC = b →
      ((bif b then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0 : ℕ) : ℝ) / SW ≤ wfun x := by
    intro b hb
    cases b
    · simp only [cond_false, Nat.cast_zero, zero_div]; exact wfun_nonneg x
    · simp only [cond_true]
      have hD : 0 < c.DHIZ := by
        simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.2
      have hN : 0 ≤ c.NLOZ := by unfold CellN.NLOZ; exact le_max_left _ _
      have hSWz : (0:ℤ) ≤ (SW : ℤ) := by positivity
      set q : ℤ := (c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ) with hq
      have hq0 : 0 ≤ q := by
        rw [hq]; exact Int.ediv_nonneg (mul_nonneg (mul_nonneg hN hN) hSWz) (mul_pos hD hD).le
      have hqe : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      have h1 : q * (c.DHIZ * c.DHIZ) ≤ c.NLOZ * c.NLOZ * SW := by
        rw [hq]; exact Int.ediv_mul_le _ (mul_pos hD hD).ne'
      rw [← hqe] at h1
      exact cellN_soundZ' c q.toNat hb (by linarith) x hx1 hx2
  exact key c.okC rfl
-- ZLEMMAS-END

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### pyramid lower-bound oracle for `wfun`, kernel-evaluated, and its soundness ######

Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Cells are absolute and dyadic: the level-`l` cell `i` is `[i 2^l, (i+1) 2^l] / 2^15`.  A table is a natural
`top` (levels 11..19 in heap order: cell `(l, i)` at field `2^(19-l) + i`) and a block map `bk : ℕ → ℕ`: block
`j` (the level-10 cell `j`) is `r + 2^5 Y`, `r ≤ 10` its finest stored level and `Y` its sub-pyramid, depth
`d = 10 - l`, local index `t`, at field `2^d - 1 + t`.  Fields are 32 bits; entries are lower bounds in units of
`10⁻¹⁰`.  `lb top bk lo hi` covers `[lo, hi]` by blocks of level-`k` cells (`k` from the width, the block size
from the alignment of the running start) and returns the least entry read.  The verification `topOk`/`blockOk`
checks the finest cells of every block by the integer cell bound and every coarser entry against its two children.
Only kernel primitives are used, so the kernel evaluates all of it on numerals. -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.Pyr

open Zeta23Ext.Bridge.ThreePoint

/-- evaluate a natural number to a numeral before continuing (the kernel is call-by-name) -/
def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a

/-- field `i` (32 bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295

/-- the entry for the level-`l` cell `i` (`l ≤ 10`) from the constant `X` of its block `j`: the entry of its
ancestor at level `max l r`, `r` the block's finest stored level -/
def entB (X l i j : ℕ) : ℕ :=
  let r := Nat.land X 31
  let kk := Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r)
  let d := Nat.sub 10 kk
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for the level-`l` cell `i` -/
def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
    (Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
    (Nat.ble 11 l)

/-- the size `t` of the next block of cells (`2^t` cells, `t ≤ 4`); any value is sound -/
def alignK1 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.ble (Nat.add g 2) (Nat.add ib 1))) (Nat.beq (Nat.land g 1) 0)
def alignK2 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK1 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK1 g ib) 2 (Nat.ble (Nat.add g 4) (Nat.add ib 1))) (Nat.beq (Nat.land g 3) 0)
def alignK3 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK2 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK2 g ib) 3 (Nat.ble (Nat.add g 8) (Nat.add ib 1))) (Nat.beq (Nat.land g 7) 0)
def alignK4 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK3 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK3 g ib) 4 (Nat.ble (Nat.add g 16) (Nat.add ib 1))) (Nat.beq (Nat.land g 15) 0)

def nmin (a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b)

/-- min of the entries over a cover of the level-`k` cells from `g` on, by blocks read through their own entries;
the next block starts where the one just read ends; stops after the block reaching past `ib` -/
def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (nmin v (ih g')) (Nat.ble g' ib))
    fuel

/-- 4-bit bit lengths of `0 .. 255` -/
def BL8 : ℕ := 0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888877777777777777777777777777777777777777777777777777777777777777776666666666666666666666666666666655555555555555554444444433332210

/-- the cover level: the bit length of `x < 2^16` (any value is sound) -/
def blen (x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15)
    (Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)) (Nat.ble 256 x)

/-- the lower-bound oracle: `lb top bk lo hi / 10¹⁰ ≤ wfun x` on `[lo, hi] / 2^15` (0 when `hi ≤ lo` or `2^19 < hi`) -/
def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
       dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) 14 (Nat.shiftRight lo k))
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

/-! ### verification of a table -/

/-- `f i` for every `i < n` -/
def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f k) ih) n

/-- `f (a + i)` for every `i < n` -/
def allFrom (a n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f (Nat.add a k)) ih) n

/-- the integer cell of the level-`l` cell `i` (endpoints packed as `LN * KB + UN`) -/
def cellAt (l i : ℕ) : CellN := ⟨Nat.add (Nat.mul (Nat.shiftLeft i l) KB) (Nat.shiftLeft (Nat.add i 1) l), 0⟩

/-- the integer cell bound `CellN.okC`, and the claim `v / 10¹⁰` below the bound it certifies -/
def cellOkCore (c : CellN) (v : ℕ) : Bool :=
  c.okC && decide (((Nat.mul v 1000 : ℕ) : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)

/-- the claim `v` on the level-`l` cell `i` passes the integer cell bound (or is `0`) -/
def cellOk (l i v : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false (cellOkCore (cellAt l i) v) (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
    true (Nat.beq v 0)

/-- a block constant: its finest cells pass the cell bound, every coarser entry is at most its children -/
def blockOkX (X j : ℕ) : Bool :=
  let r := Nat.land X 31
  let D := Nat.sub 10 r
  let Y := Nat.shiftRight X 5
  Nat.ble r 10
    && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk r (Nat.add (Nat.shiftLeft j D) t) (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
    && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
         Nat.ble (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
           (nmin (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                 (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))

def blockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOkX X j) true (Nat.beq X 0)

/-- the entry of the level-`l` cell `i` for `10 ≤ l ≤ 19` as the top levels read it (level 10: the block's own) -/
def topv (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)

/-- every top entry (levels 11..19) is at most its two children -/
def topOk (top : ℕ) (bk : ℕ → ℕ) : Bool :=
  allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
    Nat.ble (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      (nmin (topv top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))

/-! ### soundness -/

theorem forceR_eq (a : ℕ) (k : ℕ → ℕ) : forceR a k = k a := by cases a <;> rfl

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := by rw [← Nat.ble_eq, h]; decide
    show b = min a b; omega
  · have : a ≤ b := by rw [← Nat.ble_eq, h]
    show a = min a b; omega

theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (f n) (allBelow n f) = true := h
    cases hb : allBelow n f
    · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
    · rw [hb] at h'
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih hb i hi
      · subst hi; exact h'

theorem allFrom_spec {a n : ℕ} {f : ℕ → Bool} (h : allFrom a n f = true) : ∀ i < n, f (a + i) = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add a n)) (allFrom a n f) = true := h
    cases hb : allFrom a n f
    · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
    · rw [hb] at h'
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih hb i hi
      · subst hi; exact h'


theorem allFrom_add {a n m : ℕ} {f : ℕ → Bool} (h1 : allFrom a n f = true) (h2 : allFrom (a + n) m f = true) :
    allFrom a (n + m) f = true := by
  induction m with
  | zero => exact h1
  | succ m ih =>
    have h2' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add (a + n) m)) (allFrom (a + n) m f) = true := h2
    cases hb : allFrom (a + n) m f
    · rw [hb] at h2'; exact absurd (show (false : Bool) = true from h2') (by decide)
    · rw [hb] at h2'
      have h3 := ih hb
      show Bool.rec (motive := fun _ => Bool) false (f (Nat.add a (n + m))) (allFrom a (n + m) f) = true
      rw [h3]
      have e : Nat.add a (n + m) = Nat.add (a + n) m := by simp only [Nat.add_eq]; omega
      rw [e]; exact h2'

/-- all `512` blocks verified, from a verified run `allFrom 0 512` -/
theorem blocks_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk (bk j) j) = true) :
    ∀ j < 512, blockOk (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

/-- `v / 10¹⁰` bounds `wfun` below on the level-`l` cell `i`, i.e. on `[i 2^l, (i+1) 2^l] / 2^15` -/
def CS (l i v : ℕ) : Prop :=
  ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → (v : ℝ) / 10000000000 ≤ wfun x

theorem CS_zero (l i : ℕ) : CS l i 0 := by
  intro x _ _; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x

theorem CS_mono {l i v v' : ℕ} (hv : v' ≤ v) (h : CS l i v) : CS l i v' := by
  intro x h1 h2
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hv) (by norm_num)) (h x h1 h2)

theorem SC_posR : (0:ℝ) < SC := by norm_num [SC]

theorem castdiv_le {a b : ℕ} (h : a ≤ b) : (a : ℝ) / SC ≤ (b : ℝ) / SC :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) SC_posR.le

theorem CS_min {l i a b : ℕ} (ha : CS l (2 * i) a) (hb : CS l (2 * i + 1) b) : CS (l + 1) i (min a b) := by
  intro x h1 h2
  have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
  · have := ha x (by rw [e1]; exact h1) hx
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left a b) (by norm_num)) this
  · have := hb x hx (by rw [e2]; exact h2)
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right a b) (by norm_num)) this

theorem CS_anc {l m i v : ℕ} (h : CS (l + m) (i / 2 ^ m) v) : CS l i v := by
  intro x h1 h2
  have hp : 0 < 2 ^ m := by positivity
  apply h x
  · refine le_trans (castdiv_le ?_) h1
    calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
      _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
  · refine le_trans h2 (castdiv_le ?_)
    have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
      have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
    calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
      _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring

/-- a cell claim that passes `cellOk` is sound -/
theorem cellOk_sound {l i v : ℕ} (h : cellOk l i v = true) : CS l i v := by
  unfold cellOk at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : cellOkCore (cellAt l i) v = true := h
      simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨hc, hW⟩ := h'
      have hK' : (i + 1) * 2 ^ l < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
      have hLN : (cellAt l i).LN = i * 2 ^ l := by
        simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
        simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      intro x h1 h2
      have := cellN_soundZ' (cellAt l i) (Nat.mul v 1000) hc hW x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
      have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
        simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
      rw [e] at this; exact this
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; exact CS_zero l i

theorem fld_zero (i : ℕ) : fld 0 i = 0 := by
  simp [fld]

/-- what a verified block constant guarantees: every stored entry bounds its cell -/
def BlockSound (X j : ℕ) : Prop :=
  X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS (10 - d) (j * 2 ^ d + t) (fld (X / 32) (2 ^ d - 1 + t))

theorem blockOkX_sound {X j : ℕ} (h : blockOkX X j = true) : BlockSound X j := by
  have hr : Nat.land X 31 = X % 32 := by
    rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  unfold blockOkX at h
  simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h10, hfin⟩, hint⟩ := h
  refine ⟨h10, ?_⟩
  set D := Nat.sub 10 (X % 32) with hD
  have hD' : D = 10 - X % 32 := rfl
  have hfin' := allBelow_spec hfin
  have hint' := allBelow_spec hint
  -- downward induction on the depth
  suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld (X / 32) (2 ^ (D - e) - 1 + t)) by
    intro d hd t ht
    have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
    rwa [Nat.sub_sub_self (by omega)] at this
  intro e
  induction e with
  | zero =>
    intro _ t ht
    have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
    simp only [Nat.sub_zero]
    have hc := cellOk_sound this
    simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
    have e10 : 10 - D = X % 32 := by omega
    rw [e10]; exact hc
  | succ e ih =>
    intro he t ht
    set d := D - (e + 1) with hd
    have hdD : d < D := by omega
    have hde : D - e = d + 1 := by omega
    have hc := hint' d hdD
    have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
    have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
    have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
    rw [hde] at h0 h1
    have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
    have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
    rw [e0] at h0; rw [e1] at h1
    have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
    have hm := CS_min h0 h1
    rw [hlev] at hm
    refine CS_mono ?_ hm
    have a0 : 2 ^ (d + 1) - 1 + 2 * t = 2 ^ (d + 1) - 1 + 2 * t := rfl
    exact hct

theorem blockOk_sound {X j : ℕ} (h : blockOk X j = true) : BlockSound X j := by
  unfold blockOk at h
  cases hX : Nat.beq X 0
  · rw [hX] at h
    exact blockOkX_sound h
  · have : X = 0 := by rw [← Nat.beq_eq, hX]
    subst this
    refine ⟨by norm_num, fun d _ t _ => ?_⟩
    simp only [Nat.zero_div, fld_zero]; exact CS_zero _ _

theorem topv_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv top bk 10 i = fld (bk i / 32) 0 := by
  unfold topv
  rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem topv_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
    topv top bk l i = fld top (2 ^ (19 - l) + i) := by
  unfold topv
  have : Nat.beq l 10 = false := by
    cases h : Nat.beq l 10
    · rfl
    · exact absurd (by rw [← Nat.beq_eq, h]) hl
  rw [this]
  simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]

/-- the top levels and the blocks' own entries bound their cells -/
theorem top_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS (10 + e) i (topv top bk (10 + e) i) := by
  have ht' := allFrom_spec ht
  intro e
  induction e with
  | zero =>
    intro _ i hi
    rw [Nat.add_zero, topv_ten]
    have hB := blockOk_sound (hb i (by simpa using hi))
    have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
    simpa using this
  | succ e ih =>
    intro he i hi
    have hl := ht' e (by omega) |> allBelow_spec
    have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
    have e1 : 11 + e - 1 = 10 + e := by omega
    rw [e1] at hle
    have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have hm := CS_min h0 h1
    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
    rw [topv_top top bk (by omega)]
    refine CS_mono ?_ hm
    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
    exact hle

/-- every entry the oracle reads bounds its cell -/
theorem entry_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS l i (entry top bk l i) := by
  unfold entry
  cases h11 : Nat.ble 11 l
  · -- a block level
    have hl : l ≤ 10 := by
      have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
      omega
    show CS l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
    rw [forceR_eq]
    set j := Nat.shiftRight i (Nat.sub 10 l) with hj
    have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
    have hj512 : j < 512 := by
      rw [hj']
      have hi' := hi (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
      rwa [show 9 + (10 - l) = 19 - l by omega]
    have hB := blockOk_sound (hb j hj512)
    set X := bk j
    unfold entB
    have hr : Nat.land X 31 = X % 32 := by
      rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    simp only [hr]
    set r := X % 32
    have hr10 : r ≤ 10 := hB.1
    -- kk = max l r
    have hkk : Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r) = max l r := by
      cases hc : Nat.ble l r
      · have : ¬ l ≤ r := by rw [← Nat.ble_eq, hc]; decide
        show l = max l r; omega
      · have : l ≤ r := by rw [← Nat.ble_eq, hc]
        show r = max l r; omega
    simp only [hkk]
    set kk := max l r with hkkdef
    have hkk10 : kk ≤ 10 := by omega
    have hlkk : l ≤ kk := le_max_left _ _
    set d := Nat.sub 10 kk with hd
    have hd' : d = 10 - kk := rfl
    set q := i / 2 ^ (kk - l) with hq
    have hqj : q / 2 ^ d = j := by
      rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
      congr 2; omega
    have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
    have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
        = 2 ^ d - 1 + q % 2 ^ d := by
      simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      rw [← hq]
      have := Nat.div_add_mod' q (2 ^ d)
      rw [hqj] at this
      congr 1; omega
    have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    rw [hidx, hY]
    have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
    have e1 : j * 2 ^ d + q % 2 ^ d = q := by
      have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
    rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
    exact CS_anc hcs
  · cases h20 : Nat.ble 20 l
    · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
      have hl' : l ≤ 19 := by
        have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
        omega
      show CS l i (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      have := top_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
      rw [show 10 + (l - 10) = l by omega, topv_top top bk (by omega)] at this
      simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
    · exact CS_zero l i

/-- the cover of the level-`k` cells `g .. ib` reads only cells that hold sound entries -/
theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ fuel g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      (dcov top bk k ib fuel g : ℝ) / 10000000000 ≤ wfun x := by
  intro fuel
  induction fuel with
  | zero =>
    intro g _ x _ _
    show ((0 : ℕ) : ℝ) / 10000000000 ≤ wfun x
    simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
  | succ fuel ih =>
    intro g hg x h1 h2
    show ((let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (nmin v (dcov top bk k ib fuel g')) (Nat.ble g' ib) : ℕ) : ℝ) / 10000000000 ≤ wfun x
    simp only [forceR_eq]
    set t := alignK4 g ib
    set h := Nat.shiftRight g t with hh
    have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
    have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    -- the block read covers [g, g') at level k
    have hcell : CS (Nat.add k t) h (entry top bk (Nat.add k t) h) := by
      apply entry_sound hb ht
      intro hkt
      have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
      have hgib : g * 2 ^ k < 2 ^ 19 := by
        have := hk hk'
        calc g * 2 ^ k < (ib + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ ≤ 2 ^ 19 := this
      rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
      have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
        rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
      by_contra hcon
      push_neg at hcon
      have := Nat.mul_le_mul_right (2 ^ k) hcon
      rw [e] at this; omega
    have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
        (entry top bk (Nat.add k t) h : ℝ) / 10000000000 ≤ wfun y := by
      intro y hy1 hy2
      apply hcell y
      · refine le_trans (castdiv_le ?_) hy1
        rw [hh', Nat.add_eq, pow_add]
        calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
          _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
      · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
        rw [hg'', Nat.add_eq, pow_add]; ring
    cases hc : Nat.ble g' ib
    · -- the block reaches past ib
      have hgt : ib + 1 ≤ g' := by
        have : ¬ g' ≤ ib := by rw [← Nat.ble_eq, hc]; decide
        omega
      exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
    · have hle : g' ≤ ib := by rw [← Nat.ble_eq, hc]
      show ((nmin _ _ : ℕ) : ℝ) / 10000000000 ≤ wfun x
      rw [nmin_eq]
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (by norm_num)) (hcellx x h1 hx)
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by norm_num)) (ih g' hle x hx h2)

/-- the oracle's soundness: what a verified table certifies -/
def LBSound (top : ℕ) (bk : ℕ → ℕ) : Prop :=
  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb top bk lo hi : ℝ) / 10000000000 ≤ wfun x

theorem lb_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
    LBSound top bk := by
  intro lo hi x h1 h2
  unfold lb
  cases hlo : Nat.ble hi lo
  · cases hhi : Nat.ble 524289 hi
    · have hlh : lo < hi := by
        have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
        omega
      have hhi' : hi ≤ 524288 := by
        have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
        omega
      show ((dcov top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5))) : ℕ) : ℝ) / 10000000000 ≤ wfun x
      set k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
      have hp : 0 < 2 ^ k := by positivity
      apply dcov_sound hb ht k ((hi - 1) / 2 ^ k)
      · intro hk
        have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
          rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
        calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
          _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
      · exact Nat.div_le_div_right (by omega)
      · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
      · refine le_trans h2 (castdiv_le ?_)
        have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
        have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
        rw [e]
        generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
        generalize 2 ^ k = P at h5 ⊢
        omega
    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x

end Zeta23Ext.Bridge.ThreePoint.Pyr

end


/-! ###### mean-value leaf test: integer enclosures of `w'`, derivative pyramids and a point table ######

`w = N² / D²` with `b = π x`, `N = cos b − 2γ b sin b`, `D = 1 − 2 b²`; for `2 b² > 1` its derivative is
`w' = 2π N M / D³` with `M = N_b D + 4 b N` and `N_b = −(1 + 2γ) sin b − 2γ b cos b`.  The integer pipeline below
encloses `w'` on a cell at scale `DZ` (interval products rounded outward) and returns bounds in units `1/U1`.
Two pyramids (the cover arithmetic of `Pyr.lb`) store lower bounds of `w' + 2` and of `2 − w'`; their entries
claim nothing when `0`.  A point table stores lower bounds of `w` at grid points (degenerate cells `[x, x]`). -/

section MvtCells

namespace Zeta23Ext.Bridge.ThreePoint

/-- the derivative scale and the offset `2·U1` -/
def U1 : ℕ := 1000000000
def KU1 : ℕ := 2000000000

def imin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def imax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- interval product at scale `DZ`, rounded outward -/
def imulD (I J : ℤ × ℤ) : ℤ × ℤ :=
  (zfdiv (imin4 (I.1 * J.1) (I.1 * J.2) (I.2 * J.1) (I.2 * J.2)),
   zcdiv (imax4 (I.1 * J.1) (I.1 * J.2) (I.2 * J.1) (I.2 * J.2)))

/-- interval product at scale `DZ`, rounded outward, for a nonnegative first factor -/
def imulP (I J : ℤ × ℤ) : ℤ × ℤ :=
  (zfdiv (min (I.1 * J.1) (I.2 * J.1)), zcdiv (max (I.1 * J.2) (I.2 * J.2)))

/-- interval product at scale `DZ`, rounded outward, of two nonnegative factors -/
def imulPP (I J : ℤ × ℤ) : ℤ × ℤ := (zfdiv (I.1 * J.1), zcdiv (I.2 * J.2))

/-- `2γ` and `1 + 2γ` at scale `DZ` -/
def GAMI : ℤ × ℤ := (1654998581400000, 1654998603600000)
def G1I : ℤ × ℤ := (2654998581400000, 2654998603600000)

/-- lower / upper bounds of `2π q / d³ · U1` from `q ∈ [q1, q2] / DZ` and `d ∈ [d1, d2] / DZ`, `d2 < 0` -/
def w1lo (q2 d1 d2 : ℤ) : ℤ :=
  if q2 ≤ 0 then ((ndiv (2 * PLN * (-q2).toNat * DZ ^ 2 * U1) (100000000000000000000 * (-d1).toNat ^ 3) : ℕ) : ℤ)
  else -((ndivc (2 * PUN * q2.toNat * DZ ^ 2 * U1) (100000000000000000000 * (-d2).toNat ^ 3) : ℕ) : ℤ)
def w1hi (q1 d1 d2 : ℤ) : ℤ :=
  if 0 ≤ q1 then -((ndiv (2 * PLN * q1.toNat * DZ ^ 2 * U1) (100000000000000000000 * (-d1).toNat ^ 3) : ℕ) : ℤ)
  else ((ndivc (2 * PUN * (-q1).toNat * DZ ^ 2 * U1) (100000000000000000000 * (-d2).toNat ^ 3) : ℕ) : ℤ)

namespace CellN
def BI (c : CellN) : ℤ × ℤ := ((c.BLZ : ℤ), (c.BUZ : ℤ))
def PGI (c : CellN) : ℤ × ℤ := imulPP GAMI c.BI
def NI (c : CellN) : ℤ × ℤ := isubZ c.CXZ (imulP c.PGI c.SXZ)
def NbI (c : CellN) : ℤ × ℤ := isubZ (0, 0) (iaddZ (imulP G1I c.SXZ) (imulP c.PGI c.CXZ))
def DI (c : CellN) : ℤ × ℤ := isubZ ((DZ : ℤ), (DZ : ℤ)) (imulZZ 2 (imulPP c.BI c.BI))
def MI (c : CellN) : ℤ × ℤ := iaddZ (imulD c.NbI c.DI) (imulP (imulZZ 4 c.BI) c.NI)
def QI (c : CellN) : ℤ × ℤ := imulD c.NI c.MI
/-- lower / upper bounds of `w' · U1` on the cell -/
def W1LO (c : CellN) : ℤ := w1lo c.QI.2 c.DI.1 c.DI.2
def W1HI (c : CellN) : ℤ := w1hi c.QI.1 c.DI.1 c.DI.2
/-- the cell is in the scope of the derivative enclosure -/
def okD (c : CellN) : Bool := c.okC && decide (c.DI.2 < 0)
end CellN

end Zeta23Ext.Bridge.ThreePoint

end MvtCells

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- evaluate a natural number to a numeral before continuing with a Boolean (the kernel is call-by-name) -/
def forceB (a : ℕ) (k : ℕ → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) a

/-- claims on the level-`l` cell `i` of the tables of `w' + 2` (`sgn = true`) and `2 − w'` (`sgn = false`), in units
`1/U1`; the claim `0` says nothing -/
def cellOkD (sgn : Bool) (l i v : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false
      ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
        (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn)
      (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
    true (Nat.beq v 0)

/-- the point claim `v / 10¹⁰ ≤ w (x / SC)`, checked on the degenerate integer cell `[x, x]` (or `v = 0`) -/
def ptOk (x v : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false (cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v) (Nat.ble (Nat.add x 1) KB))
    true (Nat.beq v 0)

/-- a point block `j` (points `j·2^10 + t·2^r`, `r = X mod 16`, fields of 32 bits after the low 4) -/
def ptBlockOkX (X j : ℕ) : Bool :=
  let r := Nat.land X 15
  Nat.ble r 10 && allBelow (Nat.shiftLeft 1 (Nat.sub 10 r)) (fun t =>
    ptOk (Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r)) (fld (Nat.shiftRight X 4) t))

def ptBlockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (ptBlockOkX X j) true (Nat.beq X 0)

/-- the point lower bound of `w (x / SC)` in units `10⁻¹⁰` (`0` outside the table or off its grid) -/
def ptv (pb : ℕ → ℕ) (x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0))
    0 (Nat.ble 524288 x)

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ###### the derivative tables as one pyramid of pairs ######

The two derivative tables share one block structure, so they are stored as one pyramid of 64-bit entries: the low
32 bits bound `w' + 2` below and the high 32 bits bound `2 − w'` below (units `1/U1`; a half `0` claims nothing).
The cover arithmetic is that of `Pyr.lb` with the cover level taken from `(hi − lo) >>> 4` (pyramid layout adapted
from five-point-pyramid-2 by typh, Apache-2.0); the entries read are combined by the componentwise minimum `pmin`, and the verification checks every coarser entry
componentwise against its children (`ple`). -/

section MvtPairDefs

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- field `i` (64 bits) of a packed natural -/
def fld2 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 64 i)) 18446744073709551615

/-- the two halves of a pair -/
def lo32 (v : ℕ) : ℕ := Nat.land v 4294967295
def hi32 (v : ℕ) : ℕ := Nat.shiftRight v 32

/-- the componentwise minimum of two pairs -/
def pmin (a b : ℕ) : ℕ := Nat.add (nmin (lo32 a) (lo32 b)) (Nat.shiftLeft (nmin (hi32 a) (hi32 b)) 32)

/-- the componentwise order of pairs -/
def ple (a b : ℕ) : Bool := Nat.ble (lo32 a) (lo32 b) && Nat.ble (hi32 a) (hi32 b)

def entB2 (X l i j : ℕ) : ℕ :=
  let r := Nat.land X 31
  let kk := Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r)
  let d := Nat.sub 10 kk
  fld2 (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

def entry2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
    (Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
    (Nat.ble 11 l)

def dcov2 (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry2 top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (pmin v (ih g')) (Nat.ble g' ib))
    fuel

def lb2 (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 4)
       dcov2 top bk k (Nat.shiftRight (Nat.sub hi 1) k) 14 (Nat.shiftRight lo k))
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

/-- a pair claim on the level-`l` cell `i`: both halves pass the derivative cell check -/
def cellOk2 (l i v : ℕ) : Bool := cellOkD true l i (lo32 v) && cellOkD false l i (hi32 v)

def blockOk2X (X j : ℕ) : Bool :=
  let r := Nat.land X 31
  let D := Nat.sub 10 r
  let Y := Nat.shiftRight X 5
  Nat.ble r 10
    && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk2 r (Nat.add (Nat.shiftLeft j D) t) (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
    && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
         ple (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
           (pmin (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                 (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))

def blockOk2 (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOk2X X j) true (Nat.beq X 0)

def topv2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld2 (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)

def topOk2 (top : ℕ) (bk : ℕ → ℕ) : Bool :=
  allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
    ple (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      (pmin (topv2 top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv2 top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))

end Zeta23Ext.Bridge.ThreePoint.PyrD

end MvtPairDefs
noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### the derivative of `wfun` -/

/-- the pieces of `w' = 2π N M / D³` at `b = π x` -/
def kN (x : ℝ) : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)
def kD (x : ℝ) : ℝ := 1 - 2 * (Real.pi * x) ^ 2
def kNb (x : ℝ) : ℝ := -(1 + 2 * gam) * Real.sin (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)
def kM (x : ℝ) : ℝ := kNb x * kD x + 4 * (Real.pi * x) * kN x
/-- the derivative of `wfun` where `2 (π x)² ≠ 1` -/
def w1 (x : ℝ) : ℝ := 2 * Real.pi * kN x * kM x / kD x ^ 3

theorem hasDerivAt_pix (x : ℝ) : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
  simpa using (hasDerivAt_id x).const_mul Real.pi

theorem hasDerivAt_kN (x : ℝ) : HasDerivAt kN (Real.pi * kNb x) x := by
  have h := (hasDerivAt_pix x).cos.sub (((hasDerivAt_pix x).const_mul (2 * gam)).mul (hasDerivAt_pix x).sin)
  have e : kN = fun y : ℝ => Real.cos (Real.pi * y) - 2 * gam * (Real.pi * y) * Real.sin (Real.pi * y) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kNb; ring

theorem hasDerivAt_kD (x : ℝ) : HasDerivAt kD (-(4 * Real.pi * (Real.pi * x))) x := by
  have h := (((hasDerivAt_pix x).pow 2).const_mul 2).const_sub 1
  have e : kD = fun y : ℝ => 1 - 2 * (Real.pi * y) ^ 2 := rfl
  rw [e]
  refine h.congr_deriv ?_
  rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
  push_cast; ring

theorem continuous_kD : Continuous kD := by
  unfold kD; fun_prop

theorem hasDerivAt_wfun (x : ℝ) (hx : kD x ≠ 0) : HasDerivAt wfun (w1 x) x := by
  have hsq := ((hasDerivAt_kN x).div (hasDerivAt_kD x) hx).pow 2
  have hev : ∀ᶠ y in nhds x, kD y ≠ 0 := continuous_kD.continuousAt.eventually_ne hx
  have heq : wfun =ᶠ[nhds x] fun y => (kN y / kD y) ^ 2 := by
    filter_upwards [hev] with y hy
    unfold wfun
    rw [kfun_closed y hy]
    rfl
  refine (hsq.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [Pi.div_apply]
  unfold w1 kM
  rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  field_simp
  ring

/-! ### interval products at scale `DZ` -/

theorem mul_ge_min4 {a b A1 A2 B1 B2 : ℝ} (ha1 : A1 ≤ a) (ha2 : a ≤ A2) (hb1 : B1 ≤ b) (hb2 : b ≤ B2) :
    min (min (A1 * B1) (A1 * B2)) (min (A2 * B1) (A2 * B2)) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · have h1 : A1 * b ≤ a * b := mul_le_mul_of_nonneg_right ha1 hb
    rcases le_total 0 A1 with hA | hA
    · have : A1 * B1 ≤ A1 * b := mul_le_mul_of_nonneg_left hb1 hA
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (this.trans h1)
    · have : A1 * B2 ≤ A1 * b := mul_le_mul_of_nonpos_left hb2 hA
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (this.trans h1)
  · have h1 : A2 * b ≤ a * b := mul_le_mul_of_nonpos_right ha2 hb
    rcases le_total 0 A2 with hA | hA
    · have : A2 * B1 ≤ A2 * b := mul_le_mul_of_nonneg_left hb1 hA
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (this.trans h1)
    · have : A2 * B2 ≤ A2 * b := mul_le_mul_of_nonpos_left hb2 hA
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (this.trans h1)

theorem mul_le_max4 {a b A1 A2 B1 B2 : ℝ} (ha1 : A1 ≤ a) (ha2 : a ≤ A2) (hb1 : B1 ≤ b) (hb2 : b ≤ B2) :
    a * b ≤ max (max (A1 * B1) (A1 * B2)) (max (A2 * B1) (A2 * B2)) := by
  rcases le_total 0 b with hb | hb
  · have h1 : a * b ≤ A2 * b := mul_le_mul_of_nonneg_right ha2 hb
    rcases le_total 0 A2 with hA | hA
    · have : A2 * b ≤ A2 * B2 := mul_le_mul_of_nonneg_left hb2 hA
      exact (h1.trans this).trans (le_trans (le_max_right _ _) (le_max_right _ _))
    · have : A2 * b ≤ A2 * B1 := mul_le_mul_of_nonpos_left hb1 hA
      exact (h1.trans this).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · have h1 : a * b ≤ A1 * b := mul_le_mul_of_nonpos_right ha1 hb
    rcases le_total 0 A1 with hA | hA
    · have : A1 * b ≤ A1 * B2 := mul_le_mul_of_nonneg_left hb2 hA
      exact (h1.trans this).trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · have : A1 * b ≤ A1 * B1 := mul_le_mul_of_nonpos_left hb1 hA
      exact (h1.trans this).trans (le_trans (le_max_left _ _) (le_max_left _ _))

theorem imulD_sound (I J : ℤ × ℤ) {a b : ℝ} (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ)
    (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulD I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulD I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hdd : ∀ u v : ℤ, u ≤ v → (u : ℝ) / DZ / DZ ≤ (v : ℝ) / DZ / DZ := fun u v h =>
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le) hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    refine le_trans ?_ (mul_ge_min4 ha.1 ha.2 hb.1 hb.2)
    unfold imin4
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_left _ _) (min_le_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_left _ _) (min_le_right _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_right _ _) (min_le_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (min_le_right _ _) (min_le_right _ _))
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    refine le_trans (mul_le_max4 ha.1 ha.2 hb.1 hb.2) ?_
    unfold imax4
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [← ec]; exact hdd _ _ (le_trans (le_max_right _ _) (le_max_right _ _))

theorem zfdiv_nonneg {z : ℤ} (h : 0 ≤ z) : 0 ≤ zfdiv z := by
  unfold zfdiv; rw [if_pos h]; exact Int.natCast_nonneg _

theorem imulP_sound (I J : ℤ × ℤ) (h0 : 0 ≤ I.1) {a b : ℝ} (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ)
    (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulP I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulP I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hdd : ∀ u v : ℤ, u ≤ v → (u : ℝ) / DZ / DZ ≤ (v : ℝ) / DZ / DZ := fun u v h =>
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le) hD.le
  have hA0 : (0:ℝ) ≤ (I.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0) hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    exact prod_lo hA0 ha.1 ha.2 hb.1 (by rw [← ec]; exact hdd _ _ (min_le_left _ _))
      (by rw [← ec]; exact hdd _ _ (min_le_right _ _))
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    exact prod_hi hA0 ha.1 ha.2 hb.2 (by rw [← ec]; exact hdd _ _ (le_max_left _ _))
      (by rw [← ec]; exact hdd _ _ (le_max_right _ _))

theorem imulPP_sound (I J : ℤ × ℤ) (h0 : 0 ≤ I.1) (h0' : 0 ≤ J.1) {a b : ℝ}
    (ha : (I.1 : ℝ) / DZ ≤ a ∧ a ≤ (I.2 : ℝ) / DZ) (hb : (J.1 : ℝ) / DZ ≤ b ∧ b ≤ (J.2 : ℝ) / DZ) :
    ((imulPP I J).1 : ℝ) / DZ ≤ a * b ∧ a * b ≤ ((imulPP I J).2 : ℝ) / DZ := by
  have hD := DZ_pos
  have ec : ∀ p q : ℤ, (((p * q : ℤ) : ℝ) / DZ) / DZ = ((p : ℝ) / DZ) * ((q : ℝ) / DZ) := fun p q => by
    push_cast; field_simp
  have hA0 : (0:ℝ) ≤ (I.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0) hD.le
  have hB0 : (0:ℝ) ≤ (J.1 : ℝ) / DZ := div_nonneg (by exact_mod_cast h0') hD.le
  constructor
  · refine le_trans (div_le_div_of_nonneg_right (zfdiv_le _) hD.le) ?_
    rw [ec]
    exact mul_le_mul ha.1 hb.1 hB0 (hA0.trans ha.1)
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_zcdiv _) hD.le)
    rw [ec]
    exact mul_le_mul ha.2 hb.2 (hB0.trans hb.1) ((hA0.trans ha.1).trans ha.2)

theorem gami_sound : ((GAMI.1 : ℤ) : ℝ) / DZ ≤ 2 * gam ∧ 2 * gam ≤ ((GAMI.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [GAMI, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

theorem g1i_sound : ((G1I.1 : ℤ) : ℝ) / DZ ≤ 1 + 2 * gam ∧ 1 + 2 * gam ≤ ((G1I.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [G1I, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

/-! ### the trigonometric enclosures of a cell (the first half of `cellN_soundZ'`) -/

set_option maxHeartbeats 4000000 in
theorem cellN_trig (c : CellN) (hc : c.okC = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    (((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ) ∧
    (((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ) ∧
    (((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ) ∧
    ((DZ * DZ : ℕ) : ℝ) < ((2 * c.BLZ * c.BLZ : ℕ) : ℝ) := by
  simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 100000000000000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hLLO : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := ndiv_le (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.LLO
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.UHI : ℕ) : ℝ) / DZ := by
    have := le_ndivc (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.UHI
    push_cast at this ⊢
    rw [le_div_iff₀ hD0]
    calc (c.UN : ℝ) / SC * DZ = (c.UN : ℝ) * DZ / SC := by ring
      _ ≤ _ := this
  have hAD : ((c.AD : ℕ) : ℝ) / DZ = (c.k : ℝ) / 2 := by
    unfold CellN.AD; simp only [DZ, DZ2]; push_cast; ring
  have hL0 : (0:ℝ) ≤ (c.LN : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := hL0.trans hx1
  have hkF : c.side = false → (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := fun hs => by
    have : (2 * c.UN : ℝ) ≤ (c.k * SC : ℝ) := by exact_mod_cast hsideF hs
    rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
  have hkT : c.side = true → (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := fun hs => by
    have : (c.k * SC : ℝ) ≤ (2 * c.LN : ℝ) := by exact_mod_cast hsideT hs
    rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.RLO : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.RLO
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.UHI c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.LLO with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.RHI : ℕ) : ℝ) / DZ := by
    unfold CellN.RHI
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.LLO ≤ c.AD := by
        have h1 : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.UHI := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.UHI : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  have hTL : ((c.TLZ : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.TLZ
    exact ndiv_prod_le PLN c.RLO _ (by norm_num) PLN_le hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.TUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.TUZ
    exact le_ndivc_prod PUN c.RHI _ (by norm_num) PUN_ge hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.TUZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.TLZ : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  have hc1 : ((c.CLZ : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU1
    have h1 := cosLo_le c.TUZ hcP1
    have h2 := ERRD_ge
    unfold CellN.CLZ; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CUZ : ℤ) : ℝ) / DZ := by
    have h := cos_upper hTL0 hTL hθ1
    have h1 := le_cosHi c.TLZ hcP2
    have h2 := ERRD_ge
    unfold CellN.CUZ; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.SLZ : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    have h1 := sinLo_le c.TLZ hsP1
    have h2 := ERRD_ge
    unfold CellN.SLZ; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SUZ : ℤ) : ℝ) / DZ := by
    have h := sin_upper hθ0 hTUr hTU1
    have h1 := le_sinHi c.TUZ hsP2
    have h2 := ERRD_ge
    unfold CellN.SUZ; push_cast; rw [add_div]
    linarith
  have hcs := cos_sin_half c.k
  have hCX : ((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, Bool.false_eq_true, if_false]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, if_true]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hSX : ((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, Bool.false_eq_true, if_false]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, if_true]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hb1 : ((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.BLZ
    exact ndiv_prod_le PLN c.LLO _ (by norm_num) PLN_le (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.BUZ
    exact le_ndivc_prod PUN c.UHI _ (by norm_num) PUN_ge (hx2.trans hUHI) Real.pi_pos.le hx0
  exact ⟨hCX, hSX, ⟨hb1, hb2⟩, by exact_mod_cast hB⟩

/-! ### the final quotient `2π q / d³` -/

theorem quot_mono {p P a A e E : ℝ} (hp : 0 ≤ p) (hP : p ≤ P) (ha : 0 ≤ a) (hA : a ≤ A) (he : 0 < e)
    (hE : e ≤ E) : p * a / E ^ 3 ≤ P * A / e ^ 3 := by
  have he3 : 0 < e ^ 3 := by positivity
  have hE0 : 0 < E := lt_of_lt_of_le he hE
  have hE3 : 0 < E ^ 3 := by positivity
  rw [div_le_div_iff₀ hE3 he3]
  have h1 : p * a ≤ P * A := mul_le_mul hP hA ha (hp.trans hP)
  have h2 : e ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ he.le hE 3
  exact mul_le_mul h1 h2 he3.le (mul_nonneg (hp.trans hP) (ha.trans hA))

theorem PLN_pos : (0:ℝ) ≤ ((PLN : ℕ) : ℝ) / 100000000000000000000 := by positivity

/-- the rounded quotient: `w1lo ≤ 2π q / d³ · U1 ≤ w1hi` -/
theorem w1lohi_sound (q1 q2 d1 d2 : ℤ) {q d : ℝ} (hq1 : (q1 : ℝ) / DZ ≤ q) (hq2 : q ≤ (q2 : ℝ) / DZ)
    (hd1 : (d1 : ℝ) / DZ ≤ d) (hd2 : d ≤ (d2 : ℝ) / DZ) (hneg : d2 < 0) :
    (w1lo q2 d1 d2 : ℝ) / U1 ≤ 2 * Real.pi * q / d ^ 3 ∧ 2 * Real.pi * q / d ^ 3 ≤ (w1hi q1 d1 d2 : ℝ) / U1 := by
  have hD := DZ_pos
  have hU1 : (0:ℝ) < U1 := by norm_num [U1]
  have hd2r : (d2 : ℝ) < 0 := by exact_mod_cast hneg
  have hd0 : d < 0 := lt_of_le_of_lt hd2 (div_neg_of_neg_of_pos hd2r hD)
  have hd12 : (d1 : ℝ) ≤ d2 := by
    have := hd1.trans hd2
    exact (div_le_div_iff_of_pos_right hD).mp this
  have hd1n : d1 < 0 := by have : (d1 : ℝ) < 0 := lt_of_le_of_lt hd12 hd2r; exact_mod_cast this
  set e := -d with he
  have he0 : 0 < e := by rw [he]; linarith
  have hfe : 2 * Real.pi * q / d ^ 3 = -(2 * Real.pi * q / e ^ 3) := by
    rw [he]; have : d ≠ 0 := hd0.ne; field_simp; (try ring)
  -- E2 = -d1 ≥ e, E1 = -d2 ≤ e, at scale DZ
  have hE2 : (((-d1).toNat : ℕ) : ℝ) = -(d1 : ℝ) := by
    have h := Int.toNat_of_nonneg (show 0 ≤ -d1 by omega); exact_mod_cast h
  have hE1 : (((-d2).toNat : ℕ) : ℝ) = -(d2 : ℝ) := by
    have h := Int.toNat_of_nonneg (show 0 ≤ -d2 by omega); exact_mod_cast h
  have heE2 : e ≤ (((-d1).toNat : ℕ) : ℝ) / DZ := by rw [hE2, neg_div]; linarith
  have heE1 : (((-d1).toNat : ℕ) : ℝ) / DZ > 0 := lt_of_lt_of_le he0 heE2
  have hE1e : (((-d2).toNat : ℕ) : ℝ) / DZ ≤ e := by rw [hE1, neg_div]; linarith
  have hE1p : 0 < (((-d2).toNat : ℕ) : ℝ) / DZ := by rw [hE1, neg_div]; have := div_neg_of_neg_of_pos hd2r hD; linarith
  have hPLN := PLN_le
  have hPUN := PUN_ge
  -- the rounded values as quotients
  have key_lo : ∀ (A E : ℕ), 0 < E → ((ndiv (2 * PLN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) : ℕ) : ℝ) / U1
      ≤ 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * ((A : ℝ) / DZ) / (((E : ℕ) : ℝ) / DZ) ^ 3 := by
    intro A E hE
    have h := ndiv_le (2 * PLN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) (by positivity)
    refine (div_le_div_of_nonneg_right h hU1.le).trans (le_of_eq ?_)
    have hEr : (0:ℝ) < E := by exact_mod_cast hE
    push_cast; field_simp; try ring
  have key_hi : ∀ (A E : ℕ), 0 < E → 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((A : ℝ) / DZ) / (((E : ℕ) : ℝ) / DZ) ^ 3
      ≤ ((ndivc (2 * PUN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) : ℕ) : ℝ) / U1 := by
    intro A E hE
    have h := le_ndivc (2 * PUN * A * DZ ^ 2 * U1) (100000000000000000000 * E ^ 3) (by positivity)
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right h hU1.le)
    have hEr : (0:ℝ) < E := by exact_mod_cast hE
    push_cast; field_simp; try ring
  have hE2pos : 0 < (-d1).toNat := by omega
  have hE1pos : 0 < (-d2).toNat := by omega
  constructor
  · unfold w1lo
    rw [hfe]
    split_ifs with hq
    · -- q ≤ q2/DZ ≤ 0: the bound 2 p_lo |q2| / E2³ ≤ 2 π (-q) / e³
      have hA : ((((-q2).toNat : ℕ) : ℝ)) = -(q2 : ℝ) := by
        have h := Int.toNat_of_nonneg (show 0 ≤ -q2 by omega); exact_mod_cast h
      rw [Int.cast_natCast]
      refine (key_lo _ _ hE2pos).trans ?_
      have hm := quot_mono (p := ((PLN : ℕ) : ℝ) / 100000000000000000000) (a := (((-q2).toNat : ℕ) : ℝ) / DZ)
        (P := Real.pi) (A := -q) PLN_pos hPLN (by positivity) (by rw [hA, neg_div]; linarith) he0 heE2
      have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * (Real.pi * -q / e ^ 3) := by ring
      have e2 : 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * ((((-q2).toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3
          = 2 * ((((PLN : ℕ) : ℝ) / 100000000000000000000) * ((((-q2).toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
      rw [e1, e2]; linarith
    · -- q2 > 0: the bound -2 p_hi q2 / E1³ ≤ -2 π q / e³
      push_neg at hq
      have hA : (((q2.toNat : ℕ) : ℝ)) = (q2 : ℝ) := by
        have h := Int.toNat_of_nonneg hq.le; exact_mod_cast h
      have hk := key_hi q2.toNat (-d2).toNat hE1pos
      push_cast
      have hq2r : (0:ℝ) < (q2 : ℝ) / DZ := div_pos (by exact_mod_cast hq) hD
      rcases le_total q 0 with hq0 | hq0
      · have : 0 ≤ 2 * Real.pi * -q / e ^ 3 := by
          apply div_nonneg _ (by positivity); nlinarith [Real.pi_pos]
        have h2 : 0 ≤ 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3 := by
          rw [hA]; positivity
        have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * Real.pi * -q / e ^ 3 := by ring
        rw [e1, neg_div]; linarith
      · have hm := quot_mono (p := Real.pi) (a := q) (P := ((PUN : ℕ) : ℝ) / 100000000000000000000)
          (A := ((q2.toNat : ℕ) : ℝ) / DZ) Real.pi_pos.le hPUN hq0 (by rw [hA]; exact hq2) hE1p hE1e
        have e1 : 2 * Real.pi * q / e ^ 3 = 2 * (Real.pi * q / e ^ 3) := by ring
        have e2 : 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3
            = 2 * ((((PUN : ℕ) : ℝ) / 100000000000000000000) * (((q2.toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
        rw [e1, neg_div]; rw [e2] at hk; linarith
  · unfold w1hi
    rw [hfe]
    split_ifs with hq
    · -- 0 ≤ q1/DZ ≤ q: -(2π q / e³) ≤ -2 p_lo q1 / E2³
      have hA : (((q1.toNat : ℕ) : ℝ)) = (q1 : ℝ) := by
        have h := Int.toNat_of_nonneg hq; exact_mod_cast h
      have hk := key_lo q1.toNat (-d1).toNat hE2pos
      push_cast
      have hm := quot_mono (p := ((PLN : ℕ) : ℝ) / 100000000000000000000) (a := ((q1.toNat : ℕ) : ℝ) / DZ)
        (P := Real.pi) (A := q) PLN_pos hPLN (by positivity) (by rw [hA]; exact hq1) he0 heE2
      have e1 : 2 * Real.pi * q / e ^ 3 = 2 * (Real.pi * q / e ^ 3) := by ring
      have e2 : 2 * (((PLN : ℕ) : ℝ) / 100000000000000000000) * (((q1.toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3
          = 2 * ((((PLN : ℕ) : ℝ) / 100000000000000000000) * (((q1.toNat : ℕ) : ℝ) / DZ) / ((((-d1).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
      rw [e1, neg_div]; rw [e2] at hk; linarith
    · -- q1 < 0
      push_neg at hq
      have hA : ((((-q1).toNat : ℕ) : ℝ)) = -(q1 : ℝ) := by
        have h := Int.toNat_of_nonneg (show 0 ≤ -q1 by omega); exact_mod_cast h
      have hk := key_hi (-q1).toNat (-d2).toNat hE1pos
      rw [Int.cast_natCast]
      rcases le_total 0 q with hq0 | hq0
      · have : 0 ≤ 2 * Real.pi * q / e ^ 3 := by positivity
        have h2 : 0 ≤ 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3 := by
          positivity
        linarith
      · have hm := quot_mono (p := Real.pi) (a := -q) (P := ((PUN : ℕ) : ℝ) / 100000000000000000000)
          (A := (((-q1).toNat : ℕ) : ℝ) / DZ) Real.pi_pos.le hPUN (by linarith) (by rw [hA, neg_div]; linarith) hE1p hE1e
        have e1 : -(2 * Real.pi * q / e ^ 3) = 2 * (Real.pi * -q / e ^ 3) := by ring
        have e2 : 2 * (((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3
            = 2 * ((((PUN : ℕ) : ℝ) / 100000000000000000000) * ((((-q1).toNat : ℕ) : ℝ) / DZ) / ((((-d2).toNat : ℕ) : ℝ) / DZ) ^ 3) := by ring
        rw [e1]; rw [e2] at hk; linarith

/-! ### the derivative cell is sound -/

set_option maxHeartbeats 4000000 in
theorem cellD_sound (c : CellN) (hc : c.okD = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    kD x < 0 ∧ (c.W1LO : ℝ) / U1 ≤ w1 x ∧ w1 x ≤ (c.W1HI : ℝ) / U1 := by
  simp only [CellN.okD, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hcC, hD2⟩ := hc
  obtain ⟨⟨hC1, hC2⟩, ⟨hS1, hS2⟩, ⟨hB1, hB2⟩, hBB0⟩ := cellN_trig c hcC x hx1 hx2
  have hD0 := DZ_pos
  have hBI : ((c.BI.1 : ℤ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BI.2 : ℤ) : ℝ) / DZ := by
    simp only [CellN.BI, Int.cast_natCast]; exact ⟨hB1, hB2⟩
  have hBI0 : (0:ℤ) ≤ c.BI.1 := Int.natCast_nonneg _
  have hP := imulPP_sound GAMI c.BI (by decide) hBI0 gami_sound hBI
  have hP0 : (0:ℤ) ≤ c.PGI.1 := by
    show (0:ℤ) ≤ zfdiv (GAMI.1 * c.BI.1)
    exact zfdiv_nonneg (mul_nonneg (by decide) hBI0)
  have hT := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hN : ((c.NI.1 : ℤ) : ℝ) / DZ ≤ kN x ∧ kN x ≤ ((c.NI.2 : ℤ) : ℝ) / DZ :=
    isubZ_sound _ _ ⟨hC1, hC2⟩ hT
  have hG1S := imulP_sound G1I c.SXZ (by decide) g1i_sound ⟨hS1, hS2⟩
  have hPC := imulP_sound c.PGI c.CXZ hP0 hP ⟨hC1, hC2⟩
  have h00 : (((0, 0) : ℤ × ℤ).1 : ℝ) / DZ ≤ (0:ℝ) ∧ (0:ℝ) ≤ (((0, 0) : ℤ × ℤ).2 : ℝ) / DZ := by simp
  have hNb0 := isubZ_sound (0, 0) _ h00 (iaddZ_sound _ _ hG1S hPC)
  have hNb : ((c.NbI.1 : ℤ) : ℝ) / DZ ≤ kNb x ∧ kNb x ≤ ((c.NbI.2 : ℤ) : ℝ) / DZ := by
    have e : kNb x = 0 - ((1 + 2 * gam) * Real.sin (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)) := by
      unfold kNb; ring
    rw [e]; exact hNb0
  have hBB := imulPP_sound c.BI c.BI hBI0 hBI0 hBI hBI
  have h2BB := imulZZ_sound 2 _ hBB.1 hBB.2
  have h11 : ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).1 : ℝ) / DZ ≤ (1:ℝ) ∧ (1:ℝ) ≤ ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).2 : ℝ) / DZ := by
    simp only [Int.cast_natCast, div_self DZ_ne]; exact ⟨le_rfl, le_rfl⟩
  have hDD0 := isubZ_sound _ _ h11 h2BB
  have hDD : ((c.DI.1 : ℤ) : ℝ) / DZ ≤ kD x ∧ kD x ≤ ((c.DI.2 : ℤ) : ℝ) / DZ := by
    have e : kD x = 1 - ((2 : ℤ) : ℝ) * ((Real.pi * x) * (Real.pi * x)) := by unfold kD; push_cast; ring
    rw [e]; exact hDD0
  have hNbD := imulD_sound c.NbI c.DI hNb hDD
  have h4B := imulZZ_sound 4 c.BI hBI.1 hBI.2
  have h4B0 : (0:ℤ) ≤ (imulZZ 4 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 4 then ((4:ℤ) * c.BI.1, (4:ℤ) * c.BI.2) else ((4:ℤ) * c.BI.2, (4:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h4BN := imulP_sound (imulZZ 4 c.BI) c.NI h4B0 h4B hN
  have hM0 := iaddZ_sound _ _ hNbD h4BN
  have hM : ((c.MI.1 : ℤ) : ℝ) / DZ ≤ kM x ∧ kM x ≤ ((c.MI.2 : ℤ) : ℝ) / DZ := by
    have e : kM x = kNb x * kD x + ((4 : ℤ) : ℝ) * (Real.pi * x) * kN x := by unfold kM; push_cast; ring
    rw [e]; exact hM0
  have hQ := imulD_sound c.NI c.MI hN hM
  have hkD : kD x < 0 := by
    have : ((c.DI.2 : ℤ) : ℝ) < 0 := by exact_mod_cast hD2
    linarith [hDD.2, div_neg_of_neg_of_pos this hD0]
  have hw := w1lohi_sound c.QI.1 c.QI.2 c.DI.1 c.DI.2 hQ.1 hQ.2 hDD.1 hDD.2 hD2
  have e : w1 x = 2 * Real.pi * (kN x * kM x) / kD x ^ 3 := by unfold w1; ring
  rw [e]
  exact ⟨hkD, hw.1, hw.2⟩

end Zeta23Ext.Bridge.ThreePoint

end
/-! ### the derivative tables: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the function the derivative table of sign `sgn` bounds below: `w' + 2` (`true`) or `2 − w'` (`false`) -/
def fD (sgn : Bool) (x : ℝ) : ℝ := if sgn then w1 x + 2 else 2 - w1 x

/-- a nonzero `v / U1` bounds `fD sgn` below on the level-`l` cell `i`, which lies where `2 (π x)² > 1` -/
def CSD (sgn : Bool) (l i v : ℕ) : Prop :=
  v ≠ 0 → ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC →
    kD x < 0 ∧ (v : ℝ) / U1 ≤ fD sgn x

theorem forceB_eq (a : ℕ) (k : ℕ → Bool) : forceB a k = k a := by cases a <;> rfl

theorem CSD_zero (sgn : Bool) (l i : ℕ) : CSD sgn l i 0 := fun h => absurd rfl h

theorem U1_posR : (0:ℝ) < U1 := by norm_num [U1]

/-- a derivative cell claim that passes `cellOkD` is sound -/
theorem cellOkD_sound {sgn : Bool} {l i v : ℕ} (h : cellOkD sgn l i v = true) : CSD sgn l i v := by
  unfold cellOkD at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
          (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hok, hvb⟩ := h'
      have hK' : (i + 1) * 2 ^ l < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
      have hLN : (cellAt l i).LN = i * 2 ^ l := by
        simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
        simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      intro _ x h1 h2
      obtain ⟨hk, hlo, hhi⟩ := cellD_sound (cellAt l i) hok x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
      refine ⟨hk, ?_⟩
      have hU1 := U1_posR
      have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
      cases sgn
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((cellAt l i).W1HI : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte, Bool.false_eq_true]
        rw [div_le_iff₀ hU1]
        have := (le_div_iff₀ hU1).mp hhi
        rw [eK] at hvr
        nlinarith
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((cellAt l i).W1LO : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte]
        rw [div_le_iff₀ hU1]
        have := (div_le_iff₀ hU1).mp hlo
        rw [eK] at hvr
        nlinarith
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; exact CSD_zero sgn l i


/-! ### the point table -/

/-- a point claim that passes `ptOk` is sound -/
theorem ptOk_sound {x v : ℕ} (h : ptOk x v = true) : (v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) := by
  unfold ptOk at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add x 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v = true := h
      simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨hc, hW⟩ := h'
      have hK' : x < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq] at hK; omega
      have hLN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).LN = x := by
        simp only [CellN.LN, Nat.add_eq, Nat.mul_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).UN = x := by
        simp only [CellN.UN, Nat.add_eq, Nat.mul_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      have := cellN_soundZ' ⟨Nat.add (Nat.mul x KB) x, 0⟩ (Nat.mul v 1000) hc hW ((x : ℝ) / SC)
        (by rw [hLN]) (by rw [hUN])
      have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
        simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
      rw [e] at this; exact this
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _

/-- the point table's soundness: every read bounds `w` at its point -/
def PTSound (pb : ℕ → ℕ) : Prop := ∀ x : ℕ, (ptv pb x : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)

theorem ptv_sound {pb : ℕ → ℕ} (hb : ∀ j < 512, ptBlockOk (pb j) j = true) : PTSound pb := by
  intro x
  unfold ptv
  cases h5 : Nat.ble 524288 x
  · have hx : x < 524288 := by
      have : ¬ 524288 ≤ x := by rw [← Nat.ble_eq, h5]; decide
      omega
    show ((forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0) : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
    simp only [forceR_eq]
    set j := Nat.shiftRight x 10 with hj
    have hj' : j = x / 1024 := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; (try rfl)
    have hj512 : j < 512 := by rw [hj']; omega
    have hB := hb j hj512
    set X := pb j
    have hr : Nat.land X 15 = X % 16 := by
      rw [Nat.land_eq, show (15:ℕ) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have hx1023 : Nat.land x 1023 = x % 1024 := by
      rw [Nat.land_eq, show (1023:ℕ) = 2 ^ 10 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [hr, hx1023]
    set r := X % 16
    cases hal : Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 r) 1)) 0
    · show ((0 : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _
    · show ((fld (Nat.shiftRight X 4) (Nat.shiftRight (x % 1024) r) : ℕ) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      have hal' : x % 2 ^ r = 0 := by
        have h0 := hal
        rw [Nat.beq_eq, Nat.land_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul,
          Nat.and_two_pow_sub_one_eq_mod] at h0
        exact h0
      cases hX : Nat.beq X 0
      · have hB' : ptBlockOkX X j = true := by
          unfold ptBlockOk at hB; rw [hX] at hB; exact hB
        unfold ptBlockOkX at hB'
        rw [hr, Bool.and_eq_true, Nat.ble_eq] at hB'
        obtain ⟨hr10, hall⟩ := hB'
        have hall' := allBelow_spec hall
        set t := Nat.shiftRight (x % 1024) r with ht
        have ht' : t = x % 1024 / 2 ^ r := by rw [ht, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ r * 2 ^ (10 - r) = 1024 := by rw [← pow_add, show r + (10 - r) = 10 by omega]; norm_num
        have htlt : t < 2 ^ (10 - r) := by
          rw [ht', Nat.div_lt_iff_lt_mul (by positivity)]
          have := Nat.mod_lt x (show 0 < 1024 by norm_num)
          rw [mul_comm] at hpow; omega
        have hpt := ptOk_sound (hall' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq]; exact htlt))
        have hxe : Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r) = x := by
          simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
          rw [hj', ht']
          have hdvd : 2 ^ r ∣ 1024 := ⟨2 ^ (10 - r), hpow.symm⟩
          have hm : x % 1024 % 2 ^ r = 0 := by rw [Nat.mod_mod_of_dvd _ hdvd]; exact hal'
          have e1 := Nat.div_add_mod (x % 1024) (2 ^ r)
          have e2 := Nat.div_add_mod x 1024
          rw [hm, Nat.add_zero] at e1
          calc x / 1024 * 2 ^ 10 + x % 1024 / 2 ^ r * 2 ^ r
              = 1024 * (x / 1024) + 2 ^ r * (x % 1024 / 2 ^ r) := by ring
            _ = x := by rw [e1, e2]
        rw [hxe] at hpt
        simpa only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] using hpt
      · have : X = 0 := by rw [← Nat.beq_eq, hX]
        rw [this, show Nat.shiftRight 0 4 = 0 from rfl, fld_zero]
        simp only [Nat.cast_zero, zero_div]
        exact wfun_nonneg _
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ### the pyramid of pairs: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- a pair `v` at the point `x`: each nonzero half bounds its function below (`w' + 2`, `2 − w'`), at a point
where `2 (π x)² > 1` -/
def PS (v : ℕ) (x : ℝ) : Prop :=
  (lo32 v ≠ 0 → kD x < 0 ∧ (lo32 v : ℝ) / U1 ≤ fD true x) ∧
    (hi32 v ≠ 0 → kD x < 0 ∧ (hi32 v : ℝ) / U1 ≤ fD false x)

theorem lo32_eq (v : ℕ) : lo32 v = v % 2 ^ 32 := by
  unfold lo32
  rw [Nat.land_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem hi32_eq (v : ℕ) : hi32 v = v / 2 ^ 32 := by
  unfold hi32
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem pmin_lo (a b : ℕ) : lo32 (pmin a b) = min (lo32 a) (lo32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, lo32_eq (min _ _ + _),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha)]

theorem pmin_hi (a b : ℕ) : hi32 (pmin a b) = min (hi32 a) (hi32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hi32_eq (min _ _ + _),
    Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha), Nat.zero_add]

theorem PS_zero (x : ℝ) : PS 0 x := ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩

theorem PS_mono {v v' : ℕ} {x : ℝ} (h : ple v' v = true) (hv : PS v x) : PS v' x := by
  unfold ple at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := hv.1 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h1) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := hv.2 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) U1_posR.le) hb⟩

theorem PS_pmin_left {a b : ℕ} {x : ℝ} (h : PS a x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩

theorem PS_pmin_right {a b : ℕ} {x : ℝ} (h : PS b x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩

/-- the pair `v` holds on the level-`l` cell `i` -/
def CS2 (l i v : ℕ) : Prop :=
  ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → PS v x

theorem CS2_zero (l i : ℕ) : CS2 l i 0 := fun x _ _ => PS_zero x

theorem CS2_mono {l i v v' : ℕ} (hv : ple v' v = true) (h : CS2 l i v) : CS2 l i v' :=
  fun x h1 h2 => PS_mono hv (h x h1 h2)

theorem CS2_min {l i a b : ℕ} (ha : CS2 l (2 * i) a) (hb : CS2 l (2 * i + 1) b) : CS2 (l + 1) i (pmin a b) := by
  intro x h1 h2
  have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
  · exact PS_pmin_left (ha x (by rw [e1]; exact h1) hx)
  · exact PS_pmin_right (hb x hx (by rw [e2]; exact h2))

theorem CS2_anc {l m i v : ℕ} (h : CS2 (l + m) (i / 2 ^ m) v) : CS2 l i v := by
  intro x h1 h2
  have hp : 0 < 2 ^ m := by positivity
  apply h x
  · refine le_trans (castdiv_le ?_) h1
    calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
      _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
  · refine le_trans h2 (castdiv_le ?_)
    have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
      have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
    calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
      _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring

/-- a pair claim that passes `cellOk2` is sound -/
theorem cellOk2_sound {l i v : ℕ} (h : cellOk2 l i v = true) : CS2 l i v := by
  unfold cellOk2 at h
  rw [Bool.and_eq_true] at h
  have hP := cellOkD_sound h.1
  have hM := cellOkD_sound h.2
  intro x h1 h2
  exact ⟨fun h0 => hP h0 x h1 h2, fun h0 => hM h0 x h1 h2⟩

theorem fld2_zero (i : ℕ) : fld2 0 i = 0 := by
  simp [fld2]

def BlockSound2 (X j : ℕ) : Prop :=
  X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS2 (10 - d) (j * 2 ^ d + t) (fld2 (X / 32) (2 ^ d - 1 + t))

theorem blockOk2X_sound {X j : ℕ} (h : blockOk2X X j = true) : BlockSound2 X j := by
  have hr : Nat.land X 31 = X % 32 := by
    rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  unfold blockOk2X at h
  simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h10, hfin⟩, hint⟩ := h
  refine ⟨h10, ?_⟩
  set D := Nat.sub 10 (X % 32) with hD
  have hD' : D = 10 - X % 32 := rfl
  have hfin' := allBelow_spec hfin
  have hint' := allBelow_spec hint
  -- downward induction on the depth
  suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS2 (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld2 (X / 32) (2 ^ (D - e) - 1 + t)) by
    intro d hd t ht
    have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
    rwa [Nat.sub_sub_self (by omega)] at this
  intro e
  induction e with
  | zero =>
    intro _ t ht
    have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
    simp only [Nat.sub_zero]
    have hc := cellOk2_sound this
    simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
    have e10 : 10 - D = X % 32 := by omega
    rw [e10]; exact hc
  | succ e ih =>
    intro he t ht
    set d := D - (e + 1) with hd
    have hdD : d < D := by omega
    have hde : D - e = d + 1 := by omega
    have hc := hint' d hdD
    have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
    have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
    have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
    rw [hde] at h0 h1
    have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
    have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
    rw [e0] at h0; rw [e1] at h1
    have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
    have hm := CS2_min h0 h1
    rw [hlev] at hm
    exact CS2_mono hct hm

theorem blockOk2_sound {X j : ℕ} (h : blockOk2 X j = true) : BlockSound2 X j := by
  unfold blockOk2 at h
  cases hX : Nat.beq X 0
  · rw [hX] at h
    exact blockOk2X_sound h
  · have : X = 0 := by rw [← Nat.beq_eq, hX]
    subst this
    refine ⟨by norm_num, fun d _ t _ => ?_⟩
    simp only [Nat.zero_div, fld2_zero]; exact CS2_zero _ _

theorem topv2_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv2 top bk 10 i = fld2 (bk i / 32) 0 := by
  unfold topv2
  rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem topv2_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
    topv2 top bk l i = fld2 top (2 ^ (19 - l) + i) := by
  unfold topv2
  have : Nat.beq l 10 = false := by
    cases h : Nat.beq l 10
    · rfl
    · exact absurd (by rw [← Nat.beq_eq, h]) hl
  rw [this]
  simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]

/-- the top levels and the blocks' own entries bound their cells -/
theorem top2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS2 (10 + e) i (topv2 top bk (10 + e) i) := by
  have ht' := allFrom_spec ht
  intro e
  induction e with
  | zero =>
    intro _ i hi
    rw [Nat.add_zero, topv2_ten]
    have hB := blockOk2_sound (hb i (by simpa using hi))
    have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
    simpa using this
  | succ e ih =>
    intro he i hi
    have hl := ht' e (by omega) |> allBelow_spec
    have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
    have e1 : 11 + e - 1 = 10 + e := by omega
    rw [e1] at hle
    have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have hm := CS2_min h0 h1
    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
    rw [topv2_top top bk (by omega)]
    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
    exact CS2_mono hle hm

/-- every entry the oracle reads bounds its cell -/
theorem entry2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS2 l i (entry2 top bk l i) := by
  unfold entry2
  cases h11 : Nat.ble 11 l
  · -- a block level
    have hl : l ≤ 10 := by
      have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
      omega
    show CS2 l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
    rw [forceR_eq]
    set j := Nat.shiftRight i (Nat.sub 10 l) with hj
    have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
    have hj512 : j < 512 := by
      rw [hj']
      have hi' := hi (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
      rwa [show 9 + (10 - l) = 19 - l by omega]
    have hB := blockOk2_sound (hb j hj512)
    set X := bk j
    unfold entB2
    have hr : Nat.land X 31 = X % 32 := by
      rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    simp only [hr]
    set r := X % 32
    have hr10 : r ≤ 10 := hB.1
    -- kk = max l r
    have hkk : Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r) = max l r := by
      cases hc : Nat.ble l r
      · have : ¬ l ≤ r := by rw [← Nat.ble_eq, hc]; decide
        show l = max l r; omega
      · have : l ≤ r := by rw [← Nat.ble_eq, hc]
        show r = max l r; omega
    simp only [hkk]
    set kk := max l r with hkkdef
    have hkk10 : kk ≤ 10 := by omega
    have hlkk : l ≤ kk := le_max_left _ _
    set d := Nat.sub 10 kk with hd
    have hd' : d = 10 - kk := rfl
    set q := i / 2 ^ (kk - l) with hq
    have hqj : q / 2 ^ d = j := by
      rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
      congr 2; omega
    have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
    have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
        = 2 ^ d - 1 + q % 2 ^ d := by
      simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      rw [← hq]
      have := Nat.div_add_mod' q (2 ^ d)
      rw [hqj] at this
      congr 1; omega
    have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    rw [hidx, hY]
    have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
    have e1 : j * 2 ^ d + q % 2 ^ d = q := by
      have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
    rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
    exact CS2_anc hcs
  · cases h20 : Nat.ble 20 l
    · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
      have hl' : l ≤ 19 := by
        have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
        omega
      show CS2 l i (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      have := top2_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
      rw [show 10 + (l - 10) = l by omega, topv2_top top bk (by omega)] at this
      simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
    · exact CS2_zero l i

theorem dcov2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ fuel g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      PS (dcov2 top bk k ib fuel g) x := by
  intro fuel
  induction fuel with
  | zero =>
    intro g _ x _ _
    exact PS_zero x
  | succ fuel ih =>
    intro g hg x h1 h2
    show PS (let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry2 top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (pmin v (dcov2 top bk k ib fuel g')) (Nat.ble g' ib)) x
    simp only [forceR_eq]
    set t := alignK4 g ib
    set h := Nat.shiftRight g t with hh
    have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
    have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    -- the block read covers [g, g') at level k
    have hcell : CS2 (Nat.add k t) h (entry2 top bk (Nat.add k t) h) := by
      apply entry2_sound hb ht
      intro hkt
      have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
      have hgib : g * 2 ^ k < 2 ^ 19 := by
        have := hk hk'
        calc g * 2 ^ k < (ib + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ ≤ 2 ^ 19 := this
      rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
      have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
        rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
      by_contra hcon
      push_neg at hcon
      have := Nat.mul_le_mul_right (2 ^ k) hcon
      rw [e] at this; omega
    have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
        PS (entry2 top bk (Nat.add k t) h) y := by
      intro y hy1 hy2
      apply hcell y
      · refine le_trans (castdiv_le ?_) hy1
        rw [hh', Nat.add_eq, pow_add]
        calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
          _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
      · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
        rw [hg'', Nat.add_eq, pow_add]; ring
    cases hc : Nat.ble g' ib
    · -- the block reaches past ib
      have hgt : ib + 1 ≤ g' := by
        have : ¬ g' ≤ ib := by rw [← Nat.ble_eq, hc]; decide
        omega
      exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
    · have hle : g' ≤ ib := by rw [← Nat.ble_eq, hc]
      show PS (pmin _ _) x
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact PS_pmin_left (hcellx x h1 hx)
      · exact PS_pmin_right (ih g' hle x hx h2)

/-- the oracle's soundness: what a verified table certifies -/
def LBSound2 (top : ℕ) (bk : ℕ → ℕ) : Prop :=
  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → PS (lb2 top bk lo hi) x

theorem lb2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
    LBSound2 top bk := by
  intro lo hi x h1 h2
  unfold lb2
  cases hlo : Nat.ble hi lo
  · cases hhi : Nat.ble 524289 hi
    · have hlh : lo < hi := by
        have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
        omega
      have hhi' : hi ≤ 524288 := by
        have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
        omega
      show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 4)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 4))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 4)))) x
      set k := blen (Nat.shiftRight (Nat.sub hi lo) 4)
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
      have hp : 0 < 2 ^ k := by positivity
      apply dcov2_sound hb ht k ((hi - 1) / 2 ^ k)
      · intro hk
        have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
          rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
        calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
          _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
      · exact Nat.div_le_div_right (by omega)
      · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
      · refine le_trans h2 (castdiv_le ?_)
        have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
        have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
        rw [e]
        generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
        generalize 2 ^ k = P at h5 ⊢
        omega
    · exact PS_zero x
  · exact PS_zero x


theorem blocks2_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk2 (bk j) j) = true) :
    ∀ j < 512, blockOk2 (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ### the mean-value step for one pair term, and the per-gap bound -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the mean value theorem on a pair-sum interval read with nonzero derivative bounds `p`, `q`: the increment of `w`
between two points of `[lo, hi] / SC` is `d` times the increment of the argument, `p − 2 U1 ≤ U1 d ≤ 2 U1 − q` -/
theorem mvt_pair {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSound2 tD bD) (lo hi : ℕ) (hp : 1 ≤ lo32 (lb2 tD bD lo hi))
    (hq : 1 ≤ hi32 (lb2 tD bD lo hi)) (y z : ℝ)
    (hy1 : (lo : ℝ) / SC ≤ y) (hy2 : y ≤ (hi : ℝ) / SC) (hz1 : (lo : ℝ) / SC ≤ z) (hz2 : z ≤ (hi : ℝ) / SC) :
    ∃ d : ℝ, wfun z = wfun y + d * (z - y) ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * d ∧
      1000000000 * d ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
  have hp0 : lo32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hq0 : hi32 (lb2 tD bD lo hi) ≠ 0 := by omega
  have hb : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC →
      kD ξ < 0 ∧ (lo32 (lb2 tD bD lo hi) : ℝ) - 2000000000 ≤ 1000000000 * w1 ξ ∧
        1000000000 * w1 ξ ≤ 2000000000 - (hi32 (lb2 tD bD lo hi) : ℝ) := by
    intro ξ h1 h2
    obtain ⟨hk, hPb⟩ := (hD lo hi ξ h1 h2).1 hp0
    obtain ⟨_, hMb⟩ := (hD lo hi ξ h1 h2).2 hq0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPb hMb
    rw [div_le_iff₀ U1_posR] at hPb hMb
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    rw [eU] at hPb hMb
    exact ⟨hk, by linarith, by linarith⟩
  have hderiv : ∀ ξ : ℝ, (lo : ℝ) / SC ≤ ξ → ξ ≤ (hi : ℝ) / SC → HasDerivAt wfun (w1 ξ) ξ :=
    fun ξ h1 h2 => hasDerivAt_wfun ξ (hb ξ h1 h2).1.ne
  rcases lt_trichotomy y z with hyz | hyz | hyz
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hy1.trans hξ.1) (hξ.2.trans hz2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hy1.trans hξ.1.le) (hξ.2.le.trans hz2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring
  · subst hyz
    obtain ⟨_, h1, h2⟩ := hb y hy1 hy2
    exact ⟨w1 y, by ring, h1, h2⟩
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hyz
      (fun ξ hξ => (hderiv ξ (hz1.trans hξ.1) (hξ.2.trans hy2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2))
    obtain ⟨_, h1, h2⟩ := hb ξ (hz1.trans hξ.1.le) (hξ.2.le.trans hy2)
    refine ⟨w1 ξ, ?_, h1, h2⟩
    rw [hξe]; field_simp [(sub_pos.mpr hyz).ne']; ring

/-- one gap's term of the mean-value expansion: `e ∈ [−lo, hi]`, `U1 E ≤ P`, `−U1 E ≤ N` -/
theorem mterm {e E lo hi P N : ℝ} (he1 : -lo ≤ e) (he2 : e ≤ hi) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hP : 1000000000 * E ≤ P) (hN : -(1000000000 * E) ≤ N) (hP0 : 0 ≤ P) (hN0 : 0 ≤ N) :
    -(lo * P) - hi * N ≤ 1000000000 * (e * E) := by
  rcases le_total 0 e with h | h
  · have h1 := mul_le_mul_of_nonneg_left (show -N ≤ 1000000000 * E by linarith) h
    have h2 := mul_le_mul_of_nonneg_right he2 hN0
    nlinarith [mul_nonneg hlo hP0]
  · have h1 := mul_le_mul_of_nonpos_left hP h
    have h2 := mul_le_mul_of_nonneg_right he1 hP0
    nlinarith [mul_nonneg hhi hN0]

/-- truncated subtraction bounds the real difference from above -/
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have := (Nat.cast_le (α := ℝ)).mpr h
    simp only [Nat.cast_zero]; linarith

theorem natsub_nonneg (a b : ℕ) : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _

theorem ptblocks_of {pb : ℕ → ℕ} (h : allFrom 0 512 (fun j => ptBlockOk (pb j) j) = true) :
    ∀ j < 512, ptBlockOk (pb j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
/-! ###### the slope test: point values of `w` and `w'`, and one pair term's expansion ######

A point table stores at grid points `x / SC` the triple (lower bound of `w`, lower bound of `w' + 2`, lower bound
of `2 − w'`), each checked on the degenerate integer cell `[x, x]`.  `slope_pair`: for `s` and `q` in `[lo, hi]`,
`w s ≥ w q + w'(q)(s − q) − R` with `R` from the derivative pair pyramid on `[q, hi]` and `[lo, q]` (convexity is
free: the charge is the drop of `w'` below `w'(q)` to the right of `q`, and its rise above `w'(q)` to the left). -/

section SlopeDefs

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- field `i` (96 bits) of a packed natural -/
def fld3 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 96 i)) 79228162514264337593543950335

/-- the degenerate integer cell `[x, x]` -/
def dcell (x : ℕ) : CellN := ⟨Nat.add (Nat.mul x KB) x, 0⟩

/-- the claims `p` on `w' + 2` and `m` on `2 − w'` at the point `x / SC`, units `1/U1` (`0` claims nothing) -/
def ptdOk (x p m : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((Nat.beq p 0 || ((dcell x).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (dcell x).W1LO)))
      && (Nat.beq m 0 || ((dcell x).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (dcell x).W1HI))))
    (Nat.ble (Nat.add x 1) KB)

/-- a point block of triples (points `j·2^10 + t·2^r`, `r = X mod 16`, fields of 96 bits after the low 4) -/
def pt3BlockOkX (X j : ℕ) : Bool :=
  let r := Nat.land X 15
  Nat.ble r 10 && allBelow (Nat.shiftLeft 1 (Nat.sub 10 r)) (fun t =>
    ptOk (Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r)) (lo32 (fld3 (Nat.shiftRight X 4) t))
      && ptdOk (Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r)) (lo32 (hi32 (fld3 (Nat.shiftRight X 4) t)))
        (hi32 (hi32 (fld3 (Nat.shiftRight X 4) t))))

def pt3BlockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (pt3BlockOkX X j) true (Nat.beq X 0)

/-- the triple at `x / SC` (`0` outside the table or off its grid) -/
def pt3 (pb : ℕ → ℕ) (x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0))
    0 (Nat.ble 524288 x)


/-- the three-piece read of the `w` pyramid: for `hi − lo ≥ 1024`, the minimum of the reads on `[lo, lo + a]`,
`[lo + a, hi − a]` and `[hi − a, hi]` with `a = (hi − lo) / 16`, so that the middle read's overhang stays inside
`[lo, hi]` and only the two short end reads overhang -/
def lb3 (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.sub hi lo) 4) fun a =>
    Bool.rec (motive := fun _ => ℕ) (lb top bk lo hi)
      (nmin (lb top bk lo (Nat.add lo a)) (nmin (lb top bk (Nat.add lo a) (Nat.sub hi a)) (lb top bk (Nat.sub hi a) hi)))
      (Nat.ble 1024 (Nat.sub hi lo))

/-- one pair term of the slope test, given its bit (`true`: expansion, `false`: zero-order), its interval
`[L, U]` (units `1/SC`) and expansion point `QS`: the looked-up value `X` (the triple at `QS`, or the zero-order
bound), and the two half-interval reads -/
def selX (bit : Bool) (top : ℕ) (bk : ℕ → ℕ) (pb : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lb3 top bk L U) (pt3 pb QS) bit
/-- the derivative pair read with cover shift `6` (cells of `1/32 .. 1/64` of the interval) and fuel `14` -/
def lbDr (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 6)
       dcov2 top bk k (Nat.shiftRight (Nat.sub hi 1) k) 14 (Nat.shiftRight lo k))
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

def selU (bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (QS U : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 (lbDr tD bD QS U) bit
def selD (bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (L QS : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 (lbDr tD bD L QS) bit
/-- the term's value numerator (units `1/U`), slope claims `P`, `M` and offset `K` (units `1/U1`) -/
def tval (bit : Bool) (X : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) X (lo32 X) bit
def tP (bit : Bool) (X : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 (lo32 (hi32 X)) bit
def tM (bit : Bool) (X : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 (hi32 (hi32 X)) bit
def tK (bit : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 2000000000 bit
/-- the convexity charge (units `1/(SC·U1)`) -/
def tchg (bit : Bool) (L U QS X EU ED : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0
    (Nat.max (Nat.mul (Nat.sub U QS) (Nat.sub 4000000000 (Nat.add (hi32 (hi32 X)) (lo32 EU))))
      (Nat.mul (Nat.sub QS L) (Nat.sub 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X)))))) bit
/-- the term's side conditions: nonzero slope claims where they are used -/
def tok (bit : Bool) (L U QS X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X)) && (Nat.beq U QS || Nat.ble 1 (lo32 EU))
      && (Nat.beq QS L || Nat.ble 1 (hi32 ED))) bit

end Zeta23Ext.Bridge.ThreePoint.PyrD

end SlopeDefs

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the three-piece read is a lower bound wherever the pyramid read is: every `x` of `[lo, hi]` lies in one of the
three pieces -/
theorem lb3_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) :
    ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb3 top bk lo hi : ℝ) / 10000000000 ≤ wfun x := by
  intro lo hi x h1 h2
  unfold lb3
  rw [forceR_eq]
  cases hb : Nat.ble 1024 (Nat.sub hi lo)
  · exact hlb lo hi x h1 h2
  · simp only [nmin_eq]
    have hE : (0 : ℝ) ≤ 10000000000 := by norm_num
    rw [Nat.cast_min, Nat.cast_min]
    generalize Nat.shiftRight (Nat.sub hi lo) 4 = a
    rcases le_total x (((Nat.add lo a : ℕ) : ℝ) / SC) with hx | hx
    · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hE) (hlb _ _ x h1 hx)
    · rcases le_total x (((Nat.sub hi a : ℕ) : ℝ) / SC) with hx2 | hx2
      · exact le_trans (div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_left _ _)) hE) (hlb _ _ x hx hx2)
      · exact le_trans (div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_right _ _)) hE) (hlb _ _ x hx2 h2)

/-- the derivative pair read `lbDr` is sound -/
def LBSoundD (top : ℕ) (bk : ℕ → ℕ) : Prop :=
  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → PS (lbDr top bk lo hi) x

theorem lbDr_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
    LBSoundD top bk := by
  intro lo hi x h1 h2
  unfold lbDr
  cases hlo : Nat.ble hi lo
  · cases hhi : Nat.ble 524289 hi
    · have hlh : lo < hi := by
        have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
        omega
      have hhi' : hi ≤ 524288 := by
        have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
        omega
      show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 6)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 6))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 6)))) x
      set k := blen (Nat.shiftRight (Nat.sub hi lo) 6)
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
      have hp : 0 < 2 ^ k := by positivity
      apply dcov2_sound hb ht k ((hi - 1) / 2 ^ k)
      · intro hk
        have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
          rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
        calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
          _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
      · exact Nat.div_le_div_right (by omega)
      · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
      · refine le_trans h2 (castdiv_le ?_)
        have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
        have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
        rw [e]
        generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
        generalize 2 ^ k = P at h5 ⊢
        omega
    · exact PS_zero x
  · exact PS_zero x

theorem ptdOk_sound {x p m : ℕ} (h : ptdOk x p m = true) :
    (p ≠ 0 → kD ((x : ℝ) / SC) < 0 ∧ (p : ℝ) / U1 ≤ fD true ((x : ℝ) / SC)) ∧
      (m ≠ 0 → kD ((x : ℝ) / SC) < 0 ∧ (m : ℝ) / U1 ≤ fD false ((x : ℝ) / SC)) := by
  unfold ptdOk at h
  cases hK : Nat.ble (Nat.add x 1) KB
  · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
  · rw [hK] at h
    have h' : ((Nat.beq p 0 || ((dcell x).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (dcell x).W1LO)))
      && (Nat.beq m 0 || ((dcell x).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (dcell x).W1HI)))) = true := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h'
    obtain ⟨hp, hm⟩ := h'
    have hK' : x < KB := by
      rw [Nat.ble_eq] at hK
      simp only [Nat.add_eq] at hK; omega
    have hLN : (dcell x).LN = x := by
      simp only [dcell, CellN.LN, Nat.add_eq, Nat.mul_eq]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
    have hUN : (dcell x).UN = x := by
      simp only [dcell, CellN.UN, Nat.add_eq, Nat.mul_eq]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
    have hU1 := U1_posR
    have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
    refine ⟨fun hp0 => ?_, fun hm0 => ?_⟩
    · rcases hp with hp | ⟨hok, hv⟩
      · exact absurd (by rw [← Nat.beq_eq]; exact hp) hp0
      obtain ⟨hk, hlo, -⟩ := cellD_sound (dcell x) hok ((x : ℝ) / SC) (by rw [hLN]) (by rw [hUN])
      refine ⟨hk, ?_⟩
      have hvr : (p : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((dcell x).W1LO : ℝ) := by exact_mod_cast hv
      simp only [fD, ↓reduceIte]
      rw [div_le_iff₀ hU1]
      have := (div_le_iff₀ hU1).mp hlo
      rw [eK] at hvr
      nlinarith
    · rcases hm with hm | ⟨hok, hv⟩
      · exact absurd (by rw [← Nat.beq_eq]; exact hm) hm0
      obtain ⟨hk, -, hhi⟩ := cellD_sound (dcell x) hok ((x : ℝ) / SC) (by rw [hLN]) (by rw [hUN])
      refine ⟨hk, ?_⟩
      have hvr : (m : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((dcell x).W1HI : ℝ) := by exact_mod_cast hv
      simp only [fD, ↓reduceIte, Bool.false_eq_true]
      rw [div_le_iff₀ hU1]
      have := (le_div_iff₀ hU1).mp hhi
      rw [eK] at hvr
      nlinarith

/-- what a verified triple table certifies at every grid point -/
def PT3Sound (pb : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, (lo32 (pt3 pb x) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 (pt3 pb x)) ((x : ℝ) / SC)

theorem PS_of_ptdOk {x v : ℕ} (h : ptdOk x (lo32 v) (hi32 v) = true) : PS v ((x : ℝ) / SC) := by
  have h' := ptdOk_sound h
  exact ⟨h'.1, h'.2⟩

theorem fld3_zero (i : ℕ) : fld3 0 i = 0 := by
  simp [fld3]

theorem lo32_zero : lo32 0 = 0 := rfl
theorem hi32_zero : hi32 0 = 0 := rfl

theorem pt3_sound {pb : ℕ → ℕ} (hb : ∀ j < 512, pt3BlockOk (pb j) j = true) : PT3Sound pb := by
  intro x
  have hz : (lo32 0 : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 0) ((x : ℝ) / SC) := by
    rw [lo32_zero, hi32_zero]
    exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
  unfold pt3
  cases h5 : Nat.ble 524288 x
  · have hx : x < 524288 := by
      have : ¬ 524288 ≤ x := by rw [← Nat.ble_eq, h5]; decide
      omega
    show (lo32 (forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0)) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      ∧ PS (hi32 (forceR (pb (Nat.shiftRight x 10)) fun X =>
      Bool.rec (motive := fun _ => ℕ) 0 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0))) ((x : ℝ) / SC)
    simp only [forceR_eq]
    set j := Nat.shiftRight x 10 with hj
    have hj' : j = x / 1024 := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; (try rfl)
    have hj512 : j < 512 := by rw [hj']; omega
    have hB := hb j hj512
    set X := pb j
    have hr : Nat.land X 15 = X % 16 := by
      rw [Nat.land_eq, show (15:ℕ) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have hx1023 : Nat.land x 1023 = x % 1024 := by
      rw [Nat.land_eq, show (1023:ℕ) = 2 ^ 10 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [hr, hx1023]
    set r := X % 16
    cases hal : Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 r) 1)) 0
    · exact hz
    · show (lo32 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (x % 1024) r)) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
        ∧ PS (hi32 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (x % 1024) r))) ((x : ℝ) / SC)
      have hal' : x % 2 ^ r = 0 := by
        have h0 := hal
        rw [Nat.beq_eq, Nat.land_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul,
          Nat.and_two_pow_sub_one_eq_mod] at h0
        exact h0
      cases hX : Nat.beq X 0
      · have hB' : pt3BlockOkX X j = true := by
          unfold pt3BlockOk at hB; rw [hX] at hB; exact hB
        unfold pt3BlockOkX at hB'
        rw [hr, Bool.and_eq_true, Nat.ble_eq] at hB'
        obtain ⟨hr10, hall⟩ := hB'
        have hall' := allBelow_spec hall
        set t := Nat.shiftRight (x % 1024) r with ht
        have ht' : t = x % 1024 / 2 ^ r := by rw [ht, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ r * 2 ^ (10 - r) = 1024 := by rw [← pow_add, show r + (10 - r) = 10 by omega]; norm_num
        have htlt : t < 2 ^ (10 - r) := by
          rw [ht', Nat.div_lt_iff_lt_mul (by positivity)]
          have := Nat.mod_lt x (show 0 < 1024 by norm_num)
          rw [mul_comm] at hpow; omega
        have hpt := hall' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq]; exact htlt)
        rw [Bool.and_eq_true] at hpt
        obtain ⟨hw, hd⟩ := hpt
        have hxe : Nat.add (Nat.shiftLeft j 10) (Nat.shiftLeft t r) = x := by
          simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
          rw [hj', ht']
          have hdvd : 2 ^ r ∣ 1024 := ⟨2 ^ (10 - r), hpow.symm⟩
          have hm : x % 1024 % 2 ^ r = 0 := by rw [Nat.mod_mod_of_dvd _ hdvd]; exact hal'
          have e1 := Nat.div_add_mod (x % 1024) (2 ^ r)
          have e2 := Nat.div_add_mod x 1024
          rw [hm, Nat.add_zero] at e1
          calc x / 1024 * 2 ^ 10 + x % 1024 / 2 ^ r * 2 ^ r
              = 1024 * (x / 1024) + 2 ^ r * (x % 1024 / 2 ^ r) := by ring
            _ = x := by rw [e1, e2]
        rw [hxe] at hw hd
        have hw' := ptOk_sound hw
        have hd' := PS_of_ptdOk hd
        simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] at hw' hd' ⊢
        exact ⟨hw', hd'⟩
      · have : X = 0 := by rw [← Nat.beq_eq, hX]
        rw [this, show Nat.shiftRight 0 4 = 0 from rfl, fld3_zero]
        exact hz
  · exact hz

theorem pt3blocks_of {pb : ℕ → ℕ} (h : allFrom 0 512 (fun j => pt3BlockOk (pb j) j) = true) :
    ∀ j < 512, pt3BlockOk (pb j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

/-- one pair term expanded at the grid point `qt` (units `1/SC`) of `[lo, hi]`: the slope `d = w'(qt / SC)` with its
point bounds, and `w s ≥ w q + d (s − q) − R / (SC·U1)` -/
theorem slope_pair {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) (lo hi qt v : ℕ) (hlq : lo ≤ qt) (hqh : qt ≤ hi)
    (hv : PS v ((qt : ℝ) / SC)) (hP : 1 ≤ lo32 v) (hM : 1 ≤ hi32 v)
    (hup : hi = qt ∨ 1 ≤ lo32 (lbDr tD bD qt hi)) (hdn : qt = lo ∨ 1 ≤ hi32 (lbDr tD bD lo qt))
    (s : ℝ) (hs1 : (lo : ℝ) / SC ≤ s) (hs2 : s ≤ (hi : ℝ) / SC) :
    ∃ d : ℝ, (lo32 v : ℝ) - 2000000000 ≤ 1000000000 * d ∧ 1000000000 * d ≤ 2000000000 - (hi32 v : ℝ) ∧
      -(max ((hi - qt) * (4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi))))
          ((qt - lo) * (4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v))) : ℕ)
        ≤ 32768000000000 * (wfun s - wfun ((qt : ℝ) / SC) - d * (s - (qt : ℝ) / SC)) := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hU1 := U1_posR
  have hq0 : lo32 v ≠ 0 := by omega
  have hm0 : hi32 v ≠ 0 := by omega
  obtain ⟨hkq, hPq⟩ := hv.1 hq0
  obtain ⟨-, hMq⟩ := hv.2 hm0
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  refine ⟨w1 ((qt : ℝ) / SC), by linarith, by linarith, ?_⟩
  set q : ℝ := (qt : ℝ) / SC with hq
  set R := max ((hi - qt) * (4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi))))
    ((qt - lo) * (4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v))) with hR
  have hR1 : ((hi - qt : ℕ) : ℝ) * ((4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi)) : ℕ) : ℝ) ≤ (R : ℝ) := by
    rw [← Nat.cast_mul]; exact_mod_cast le_max_left _ _
  have hR2 : ((qt - lo : ℕ) : ℝ) * ((4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v) : ℕ) : ℝ) ≤ (R : ℝ) := by
    rw [← Nat.cast_mul]; exact_mod_cast le_max_right _ _
  -- derivative on an interval where the pyramid read is nonzero
  have hderiv : ∀ (a b : ℕ) (hab : 1 ≤ lo32 (lbDr tD bD a b) ∨ 1 ≤ hi32 (lbDr tD bD a b)) (ξ : ℝ),
      (a : ℝ) / SC ≤ ξ → ξ ≤ (b : ℝ) / SC → HasDerivAt wfun (w1 ξ) ξ := by
    intro a b hab ξ h1 h2
    rcases hab with hab | hab
    · exact hasDerivAt_wfun ξ ((hD a b ξ h1 h2).1 (by omega)).1.ne
    · exact hasDerivAt_wfun ξ ((hD a b ξ h1 h2).2 (by omega)).1.ne
  rcases lt_trichotomy s q with hsq | hsq | hsq
  · -- to the left of q: the rise of w' above w'(q) on [lo, q]
    have hlo : qt ≠ lo := by
      intro he; rw [hq, he] at hsq; linarith
    have hdn' : 1 ≤ hi32 (lbDr tD bD lo qt) := hdn.resolve_left hlo
    have hlo_q : (lo : ℝ) / SC ≤ q := by rw [hq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hlq) (by norm_num [SC])
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hsq
      (fun ξ hξ => (hderiv lo qt (Or.inr hdn') ξ (hs1.trans hξ.1) hξ.2).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv lo qt (Or.inr hdn') ξ (hs1.trans hξ.1.le) hξ.2.le)
    have hb := (hD lo qt ξ (hs1.trans hξ.1.le) hξ.2.le).2 (by omega)
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hb
    obtain ⟨-, hb⟩ := hb
    rw [div_le_iff₀ hU1, eU] at hb
    have e1 : wfun s - wfun q - w1 q * (s - q) = (w1 q - w1 ξ) * (q - s) := by
      have hne : q - s ≠ 0 := by linarith
      have : wfun q - wfun s = w1 ξ * (q - s) := by rw [hξe]; field_simp
      linarith
    rw [e1]
    have hqs : q - s ≤ ((qt - lo : ℕ) : ℝ) / 32768 := by
      rw [Nat.cast_sub hlq, sub_div]; rw [hSC] at hs1 hq; rw [hq]; linarith
    have hn := natsub_ge 4000000000 (hi32 (lbDr tD bD lo qt) + lo32 v)
    push_cast at hn
    have hqs0 : 0 ≤ q - s := by linarith
    have hn0 : (0 : ℝ) ≤ ((4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hqs hn0, mul_le_mul_of_nonneg_left (show 1000000000 * (w1 ξ - w1 q) ≤ ((4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v) : ℕ) : ℝ) by linarith) hqs0]
  · rw [hsq]; simp only [sub_self, mul_zero]
    have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    linarith
  · -- to the right of q: the drop of w' below w'(q) on [q, hi]
    have hhi : hi ≠ qt := by
      intro he; rw [hq, ← he] at hsq; linarith
    have hup' : 1 ≤ lo32 (lbDr tD bD qt hi) := hup.resolve_left hhi
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hsq
      (fun ξ hξ => (hderiv qt hi (Or.inl hup') ξ hξ.1 (hξ.2.trans hs2)).continuousAt.continuousWithinAt)
      (fun ξ hξ => hderiv qt hi (Or.inl hup') ξ hξ.1.le (hξ.2.le.trans hs2))
    have hb := (hD qt hi ξ hξ.1.le (hξ.2.le.trans hs2)).1 (by omega)
    simp only [fD, ↓reduceIte] at hb
    obtain ⟨-, hb⟩ := hb
    rw [div_le_iff₀ hU1, eU] at hb
    have e1 : wfun s - wfun q - w1 q * (s - q) = (w1 ξ - w1 q) * (s - q) := by
      have hne : s - q ≠ 0 := by linarith
      have : wfun s - wfun q = w1 ξ * (s - q) := by rw [hξe]; field_simp
      linarith
    rw [e1]
    have hsq' : s - q ≤ ((hi - qt : ℕ) : ℝ) / 32768 := by
      rw [Nat.cast_sub hqh, sub_div]; rw [hSC] at hs2 hq; rw [hq]; linarith
    have hn := natsub_ge 4000000000 (hi32 v + lo32 (lbDr tD bD qt hi))
    push_cast at hn
    have hsq0 : 0 ≤ s - q := by linarith
    have hn0 : (0 : ℝ) ≤ ((4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi)) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hsq' hn0, mul_le_mul_of_nonneg_left (show 1000000000 * (w1 q - w1 ξ) ≤ ((4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi)) : ℕ) : ℝ) by linarith) hsq0]


/-- one pair term: `SC·U·w(s) ≥ SC·val + SC·U·d·(s − q) − (U/U1)·charge`, with the slope `d` inside the term's
claims (`d = 0` for a zero-order term) -/
theorem term_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (bit : Bool) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : tok bit L U QS (selX bit top bk pb L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selX bit top bk pb L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selX bit top bk pb L U QS) : ℝ) ∧
      32768 * (tval bit (selX bit top bk pb L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (tchg bit L U QS (selX bit top bk pb L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := lb3_sound hlb L U s hs1 hs2
    simp only [tval, selX, tchg, Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [tok, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨hP, hM⟩, hup⟩, hdn⟩ := hok
    simp only [selX, selU, selD, tval, tP, tM, tK, tchg] at hP hM hup hdn ⊢
    have hp := hpt QS
    obtain ⟨d, hd1, hd2, hd3⟩ := slope_pair hD L U QS (hi32 (pt3 pb QS)) hLQ hQU hp.2 hP hM
      (hup.imp (fun h => h) (fun h => h)) (hdn.imp (fun h => h) (fun h => h)) s hs1 hs2
    refine ⟨d, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    rw [hSC] at hw
    have hw' : (lo32 (pt3 pb QS) : ℝ) ≤ 10000000000 * wfun ((QS : ℝ) / 32768) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    have e : ((Nat.max (Nat.mul (Nat.sub U QS) (Nat.sub 4000000000 (Nat.add (hi32 (hi32 (pt3 pb QS))) (lo32 (lbDr tD bD QS U)))))
        (Nat.mul (Nat.sub QS L) (Nat.sub 4000000000 (Nat.add (hi32 (lbDr tD bD L QS)) (lo32 (hi32 (pt3 pb QS)))))) : ℕ) : ℝ)
        = ((max ((U - QS) * (4000000000 - (hi32 (hi32 (pt3 pb QS)) + lo32 (lbDr tD bD QS U))))
          ((QS - L) * (4000000000 - (hi32 (lbDr tD bD L QS) + lo32 (hi32 (pt3 pb QS))))) : ℕ) : ℝ) := rfl
    rw [e]
    rw [hSC] at hd3
    nlinarith [hd3, hw']

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
/-! ###### convex basins: the sign of `w''` on a cell, chains of cells where `w'' ≥ 0`, and the tangent minorant ######

Basin boxes at the near-minimal local minima after six-point-convex-basins-2 by typh (Apache-2.0): around such a
minimum each pair term is convex on its range, so its tangent at the expansion point is a lower bound and the slope
test needs no charge.  Here `w'' = 2π² P / D⁴` with `P = M² + N (N₂ D² + 4 N D + 8 b M)` and
`N₂ = −(1 + 4γ) cos b + 2γ b sin b` (`b = π x`, `N`, `M`, `D` as in the derivative cells); a cell certifies
`w'' ≥ 0` when the integer enclosure of `P` is nonnegative. -/

section ConvDefs

namespace Zeta23Ext.Bridge.ThreePoint

/-- `1 + 4γ` at scale `DZ` -/
def G2I : ℤ × ℤ := (4309997162800000, 4309997207200000)

namespace CellN
def N2I (c : CellN) : ℤ × ℤ := isubZ (imulP c.PGI c.SXZ) (imulP G2I c.CXZ)
def P2I (c : CellN) : ℤ × ℤ :=
  iaddZ (imulD c.MI c.MI)
    (imulD c.NI (iaddZ (iaddZ (imulD c.N2I (imulD c.DI c.DI)) (imulZZ 4 (imulD c.NI c.DI))) (imulP (imulZZ 8 c.BI) c.MI)))
/-- the cell certifies `D < 0` and `w'' ≥ 0` -/
def convOk (c : CellN) : Bool := c.okD && decide (0 ≤ c.P2I.1)
end CellN

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the cell `[a, b] / SC` -/
def ccell (a b : ℕ) : CellN := ⟨Nat.add (Nat.mul a KB) b, 0⟩

/-- a chain `a = c₀ ≤ c₁ ≤ … ≤ c_k` of cells `[c_i, c_(i+1)]`, each certifying `w'' ≥ 0` -/
def chainOk (a : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && ih b) l a

/-- the chain's last point -/
def chainLast (a : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun a => a) (fun b _ ih _ => ih b) l a

/-- the side conditions of a pair term in a convex basin: nonzero slope claims at `QS` and a nonempty chain from `L`
to `U` (expanded terms), nothing (zero-order terms) -/
def ctok (bit : Bool) (L U QS X : ℕ) (c : List ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X)) && Nat.ble 1 c.length && chainOk L c
      && Nat.beq (chainLast L c) U) bit

/-- the binary block dispatch of the tables: below / from the split point `m`, and a single block `k` -/
def dsel (j m a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) a b (Nat.ble m j)
def dpk (j k v : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 v (Nat.beq j k)

/-- a pair term's value read through a point function `f` (the triple at `QS`) or at zero order (one pyramid read) -/
def selXf (bit : Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lb top bk L U) (f QS) bit
/-- a triple `v` at the point `x / SC`, checked on the degenerate integer cell -/
def pt3e (x v : ℕ) : Bool := ptOk x (lo32 v) && ptdOk x (lo32 (hi32 v)) (hi32 (hi32 v))
/-- the triple of `x` in a short list of points (`0` if absent) -/
def ptl (L : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ ih => Bool.rec (motive := fun _ => ℕ) ih e.2 (Nat.beq e.1 x)) L
def ptlOk (L : List (ℕ × ℕ)) : Bool := List.rec (motive := fun _ => Bool) true (fun e _ ih => pt3e e.1 e.2 && ih) L

/-- evaluate a Boolean before continuing (the kernel is call-by-name) -/
def bforce (b : Bool) (k : Bool → Bool) : Bool := Bool.rec (motive := fun _ => Bool) (k false) (k true) b

/-- convex regions `[a, b]` of `w`, each with a chain of cells from `a` to `b` certifying `w'' ≥ 0` -/
def inReg (R : List (ℕ × ℕ × List ℕ)) (lo hi : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => (Nat.ble r.1 lo && Nat.ble hi r.2.1) || ih) R
def regOk (R : List (ℕ × ℕ × List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => Nat.ble 1 r.2.2.length && chainOk r.1 r.2.2 && Nat.beq (chainLast r.1 r.2.2) r.2.1 && ih) R
/-- convex regions by index `k` (the region around the integer `k`): bounds packed in 20-bit fields of `R.1` and
`R.2.1`, chains in `R.2.2` -/
def rgA (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.1 (Nat.mul 20 k)) 1048575
def rgB (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.2.1 (Nat.mul 20 k)) 1048575
/-- the range `[lo, hi]` lies in the convex region of the integer nearest to `lo` -/
def inRg (R : ℕ × ℕ × List (List ℕ)) (lo hi : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add lo 16384) 15) fun k => Nat.blt k 16 && Nat.ble (rgA R k) lo && Nat.ble hi (rgB R k)
/-- every region `k < 16` is empty or carries a nonempty chain of convex cells from its lower to its upper bound -/
def rgOk (R : ℕ × ℕ × List (List ℕ)) : Bool :=
  allBelow 16 fun k => Nat.blt (rgB R k) (rgA R k)
    || (Nat.ble 1 (R.2.2.getD k []).length && chainOk (rgA R k) (R.2.2.getD k [])
      && Nat.beq (chainLast (rgA R k) (R.2.2.getD k [])) (rgB R k))

/-- the side conditions of a pair term of the slope test: a convex term (`cv`, its range inside a convex region) needs
nonzero slope claims at `QS` when expanded, any other term the slope test's conditions -/
def rtok (cv bit : Bool) (L U QS X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tok bit L U QS X EU ED)
    (Bool.rec (motive := fun _ => Bool) true (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) bit) cv

/-- the derivative reads of a mixed term: none for a convex term (`vb`), else those of the slope test -/
def selUv (vb bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (QS U : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (selU bit tD bD QS U) 0 vb
def selDv (vb bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (L QS : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (selD bit tD bD L QS) 0 vb
/-- the charge of a mixed term: none for a convex term, else the slope test's -/
def mchg (vb bit : Bool) (L U QS X EU ED : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (tchg bit L U QS X EU ED) 0 vb
/-- the side conditions of a mixed term -/
def mtok (vb bit : Bool) (L U QS X EU ED : ℕ) (c : List ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tok bit L U QS X EU ED) (ctok bit L U QS X c) vb

end Zeta23Ext.Bridge.ThreePoint.PyrD

end ConvDefs

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### the second derivative of `wfun` -/

def kN2 (x : ℝ) : ℝ := -(1 + 4 * gam) * Real.cos (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)
def kP2 (x : ℝ) : ℝ := kM x ^ 2 + kN x * (kN2 x * kD x ^ 2 + 4 * kN x * kD x + 8 * (Real.pi * x) * kM x)
/-- the derivative of `w1` where `2 (π x)² ≠ 1` -/
def w2 (x : ℝ) : ℝ := 2 * Real.pi ^ 2 * kP2 x / kD x ^ 4

theorem hasDerivAt_kNb (x : ℝ) : HasDerivAt kNb (Real.pi * kN2 x) x := by
  have h := (((hasDerivAt_pix x).sin).const_mul (-(1 + 2 * gam))).sub
    (((hasDerivAt_pix x).const_mul (2 * gam)).mul (hasDerivAt_pix x).cos)
  have e : kNb = fun y : ℝ => -(1 + 2 * gam) * Real.sin (Real.pi * y) - 2 * gam * (Real.pi * y) * Real.cos (Real.pi * y) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kN2; ring

theorem hasDerivAt_kM (x : ℝ) : HasDerivAt kM (Real.pi * (kN2 x * kD x + 4 * kN x)) x := by
  have h := ((hasDerivAt_kNb x).mul (hasDerivAt_kD x)).add (((hasDerivAt_pix x).const_mul 4).mul (hasDerivAt_kN x))
  have e : kM = fun y : ℝ => kNb y * kD y + 4 * (Real.pi * y) * kN y := rfl
  rw [e]
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_w1 (x : ℝ) (hx : kD x ≠ 0) : HasDerivAt w1 (w2 x) x := by
  have h := ((((hasDerivAt_kN x).const_mul (2 * Real.pi)).mul (hasDerivAt_kM x))).div ((hasDerivAt_kD x).pow 3)
    (pow_ne_zero 3 hx)
  have e : w1 = fun y : ℝ => 2 * Real.pi * kN y * kM y / kD y ^ 3 := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  unfold w2 kP2 kM
  rw [show (3:ℕ) - 1 = 2 from rfl]
  push_cast
  field_simp
  ring

theorem g2i_sound : ((G2I.1 : ℤ) : ℝ) / DZ ≤ 1 + 4 * gam ∧ 1 + 4 * gam ≤ ((G2I.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [G2I, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

/-! ### the convexity cell is sound -/

set_option maxHeartbeats 8000000 in
theorem cellConv_sound (c : CellN) (hc : c.convOk = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    kD x < 0 ∧ 0 ≤ w2 x := by
  simp only [CellN.convOk, CellN.okD, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hcC, hD2⟩, hP2⟩ := hc
  obtain ⟨⟨hC1, hC2⟩, ⟨hS1, hS2⟩, ⟨hB1, hB2⟩, hBB0⟩ := cellN_trig c hcC x hx1 hx2
  have hD0 := DZ_pos
  have hBI : ((c.BI.1 : ℤ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BI.2 : ℤ) : ℝ) / DZ := by
    simp only [CellN.BI, Int.cast_natCast]; exact ⟨hB1, hB2⟩
  have hBI0 : (0:ℤ) ≤ c.BI.1 := Int.natCast_nonneg _
  have hP := imulPP_sound GAMI c.BI (by decide) hBI0 gami_sound hBI
  have hP0 : (0:ℤ) ≤ c.PGI.1 := by
    show (0:ℤ) ≤ zfdiv (GAMI.1 * c.BI.1)
    exact zfdiv_nonneg (mul_nonneg (by decide) hBI0)
  have hT := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hN : ((c.NI.1 : ℤ) : ℝ) / DZ ≤ kN x ∧ kN x ≤ ((c.NI.2 : ℤ) : ℝ) / DZ :=
    isubZ_sound _ _ ⟨hC1, hC2⟩ hT
  have hG1S := imulP_sound G1I c.SXZ (by decide) g1i_sound ⟨hS1, hS2⟩
  have hPC := imulP_sound c.PGI c.CXZ hP0 hP ⟨hC1, hC2⟩
  have h00 : (((0, 0) : ℤ × ℤ).1 : ℝ) / DZ ≤ (0:ℝ) ∧ (0:ℝ) ≤ (((0, 0) : ℤ × ℤ).2 : ℝ) / DZ := by simp
  have hNb0 := isubZ_sound (0, 0) _ h00 (iaddZ_sound _ _ hG1S hPC)
  have hNb : ((c.NbI.1 : ℤ) : ℝ) / DZ ≤ kNb x ∧ kNb x ≤ ((c.NbI.2 : ℤ) : ℝ) / DZ := by
    have e : kNb x = 0 - ((1 + 2 * gam) * Real.sin (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)) := by
      unfold kNb; ring
    rw [e]; exact hNb0
  have hBB := imulPP_sound c.BI c.BI hBI0 hBI0 hBI hBI
  have h2BB := imulZZ_sound 2 _ hBB.1 hBB.2
  have h11 : ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).1 : ℝ) / DZ ≤ (1:ℝ) ∧ (1:ℝ) ≤ ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).2 : ℝ) / DZ := by
    simp only [Int.cast_natCast, div_self DZ_ne]; exact ⟨le_rfl, le_rfl⟩
  have hDD0 := isubZ_sound _ _ h11 h2BB
  have hDD : ((c.DI.1 : ℤ) : ℝ) / DZ ≤ kD x ∧ kD x ≤ ((c.DI.2 : ℤ) : ℝ) / DZ := by
    have e : kD x = 1 - ((2 : ℤ) : ℝ) * ((Real.pi * x) * (Real.pi * x)) := by unfold kD; push_cast; ring
    rw [e]; exact hDD0
  have hNbD := imulD_sound c.NbI c.DI hNb hDD
  have h4B := imulZZ_sound 4 c.BI hBI.1 hBI.2
  have h4B0 : (0:ℤ) ≤ (imulZZ 4 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 4 then ((4:ℤ) * c.BI.1, (4:ℤ) * c.BI.2) else ((4:ℤ) * c.BI.2, (4:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h4BN := imulP_sound (imulZZ 4 c.BI) c.NI h4B0 h4B hN
  have hM0 := iaddZ_sound _ _ hNbD h4BN
  have hM : ((c.MI.1 : ℤ) : ℝ) / DZ ≤ kM x ∧ kM x ≤ ((c.MI.2 : ℤ) : ℝ) / DZ := by
    have e : kM x = kNb x * kD x + ((4 : ℤ) : ℝ) * (Real.pi * x) * kN x := by unfold kM; push_cast; ring
    rw [e]; exact hM0
  -- N₂
  have hPS := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hG2C := imulP_sound G2I c.CXZ (by decide) g2i_sound ⟨hC1, hC2⟩
  have hN20 := isubZ_sound _ _ hPS hG2C
  have hN2 : ((c.N2I.1 : ℤ) : ℝ) / DZ ≤ kN2 x ∧ kN2 x ≤ ((c.N2I.2 : ℤ) : ℝ) / DZ := by
    have e : kN2 x = 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) - (1 + 4 * gam) * Real.cos (Real.pi * x) := by
      unfold kN2; ring
    rw [e]; exact hN20
  -- P
  have hDsq := imulD_sound c.DI c.DI hDD hDD
  have hA := imulD_sound c.N2I (imulD c.DI c.DI) hN2 hDsq
  have hND := imulD_sound c.NI c.DI hN hDD
  have h4ND := imulZZ_sound 4 _ hND.1 hND.2
  have h8B := imulZZ_sound 8 c.BI hBI.1 hBI.2
  have h8B0 : (0:ℤ) ≤ (imulZZ 8 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 8 then ((8:ℤ) * c.BI.1, (8:ℤ) * c.BI.2) else ((8:ℤ) * c.BI.2, (8:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h8BM := imulP_sound (imulZZ 8 c.BI) c.MI h8B0 h8B hM
  have hIn := iaddZ_sound _ _ (iaddZ_sound _ _ hA h4ND) h8BM
  have hNIn := imulD_sound c.NI _ hN hIn
  have hMM := imulD_sound c.MI c.MI hM hM
  have hPP := iaddZ_sound _ _ hMM hNIn
  have hkP : ((c.P2I.1 : ℤ) : ℝ) / DZ ≤ kP2 x := by
    have e : kP2 x = kM x * kM x + kN x * (kN2 x * (kD x * kD x) + ((4 : ℤ) : ℝ) * (kN x * kD x)
        + ((8 : ℤ) : ℝ) * (Real.pi * x) * kM x) := by unfold kP2; push_cast; ring
    rw [e]; exact hPP.1
  have hkD : kD x < 0 := by
    have : ((c.DI.2 : ℤ) : ℝ) < 0 := by exact_mod_cast hD2
    linarith [hDD.2, div_neg_of_neg_of_pos this hD0]
  have hP20 : (0:ℝ) ≤ kP2 x := le_trans (div_nonneg (by exact_mod_cast hP2) hD0.le) hkP
  refine ⟨hkD, ?_⟩
  unfold w2
  exact div_nonneg (mul_nonneg (by positivity) hP20) (by positivity)

/-! ### the tangent minorant on a convex range -/

theorem tangent_le {A B : ℝ} (hc : ∀ x : ℝ, A ≤ x → x ≤ B → kD x < 0 ∧ 0 ≤ w2 x) {q s : ℝ}
    (hq1 : A ≤ q) (hq2 : q ≤ B) (hs1 : A ≤ s) (hs2 : s ≤ B) : wfun q + w1 q * (s - q) ≤ wfun s := by
  have hW : ∀ ξ : ℝ, A ≤ ξ → ξ ≤ B → HasDerivAt wfun (w1 ξ) ξ := fun ξ h1 h2 =>
    hasDerivAt_wfun ξ (hc ξ h1 h2).1.ne
  have hW1 : ∀ ξ : ℝ, A ≤ ξ → ξ ≤ B → HasDerivAt w1 (w2 ξ) ξ := fun ξ h1 h2 =>
    hasDerivAt_w1 ξ (hc ξ h1 h2).1.ne
  rcases lt_trichotomy q s with hqs | hqs | hqs
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hqs
      (fun y hy => (hW y (hq1.trans hy.1) (hy.2.trans hs2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hq1.trans hy.1.le) (hy.2.le.trans hs2))
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hξ.1
      (fun y hy => (hW1 y (hq1.trans hy.1) (hy.2.trans (hξ.2.le.trans hs2))).continuousAt.continuousWithinAt)
      (fun y hy => hW1 y (hq1.trans hy.1.le) (hy.2.le.trans (hξ.2.le.trans hs2)))
    have h2 := (hc η (hq1.trans hη.1.le) (hη.2.le.trans (hξ.2.le.trans hs2))).2
    have hmono : w1 q ≤ w1 ξ := by
      have hpos : 0 < ξ - q := by linarith [hξ.1]
      have : w1 ξ - w1 q = w2 η * (ξ - q) := by rw [hηe]; field_simp
      nlinarith
    have : wfun s - wfun q = w1 ξ * (s - q) := by
      have hne : s - q ≠ 0 := by linarith
      rw [hξe]; field_simp
    nlinarith
  · rw [hqs]; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hqs
      (fun y hy => (hW y (hs1.trans hy.1) (hy.2.trans hq2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hs1.trans hy.1.le) (hy.2.le.trans hq2))
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hξ.2
      (fun y hy => (hW1 y ((hs1.trans hξ.1.le).trans hy.1) (hy.2.trans hq2)).continuousAt.continuousWithinAt)
      (fun y hy => hW1 y ((hs1.trans hξ.1.le).trans hy.1.le) (hy.2.le.trans hq2))
    have h2 := (hc η ((hs1.trans hξ.1.le).trans hη.1.le) (hη.2.le.trans hq2)).2
    have hmono : w1 ξ ≤ w1 q := by
      have hpos : 0 < q - ξ := by linarith [hξ.2]
      have : w1 q - w1 ξ = w2 η * (q - ξ) := by rw [hηe]; field_simp
      nlinarith
    have : wfun q - wfun s = w1 ξ * (q - s) := by
      have hne : q - s ≠ 0 := by linarith
      rw [hξe]; field_simp
    nlinarith

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-! ### chains -/

theorem ccell_LN {a b : ℕ} (hb : b < KB) : (ccell a b).LN = a := by
  simp only [ccell, CellN.LN, Nat.add_eq, Nat.mul_eq]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem ccell_UN {a b : ℕ} (hb : b < KB) : (ccell a b).UN = b := by
  simp only [ccell, CellN.UN, Nat.add_eq, Nat.mul_eq]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem chainOk_sound : ∀ (l : List ℕ) (a : ℕ), chainOk a l = true → l ≠ [] →
    ∀ x : ℝ, (a : ℝ) / SC ≤ x → x ≤ (chainLast a l : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  intro l
  induction l with
  | nil => intro a _ h; exact absurd rfl h
  | cons b r ih =>
    intro a h _ x hx1 hx2
    have h' : (Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && chainOk b r) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨⟨⟨hab, hbK⟩, hcv⟩, hr⟩ := h'
    have hbK' : b < KB := by simp only [Nat.add_eq] at hbK; omega
    rcases le_or_gt x ((b : ℝ) / SC) with hxb | hxb
    · exact cellConv_sound (ccell a b) hcv x (by rw [ccell_LN hbK']; exact hx1) (by rw [ccell_UN hbK']; exact hxb)
    · cases r with
      | nil =>
        have e : chainLast a [b] = b := rfl
        rw [e] at hx2; linarith
      | cons c r' =>
        have e : chainLast a (b :: c :: r') = chainLast b (c :: r') := rfl
        rw [e] at hx2
        exact ih b hr (List.cons_ne_nil c r') x hxb.le hx2

/-- a point function whose triples are sound at every grid point -/
def PTF (f : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, (lo32 (f x) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 (f x)) ((x : ℝ) / SC)

theorem ptl_sound : ∀ (L : List (ℕ × ℕ)), ptlOk L = true → PTF (ptl L) := by
  intro L
  induction L with
  | nil =>
    intro _ x
    show (lo32 0 : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 0) ((x : ℝ) / SC)
    rw [lo32_zero, hi32_zero]
    exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
  | cons e r ih =>
    intro h x
    have h' : (pt3e e.1 e.2 && ptlOk r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨he, hr⟩ := h'
    show (lo32 (Bool.rec (motive := fun _ => ℕ) (ptl r x) e.2 (Nat.beq e.1 x)) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      ∧ PS (hi32 (Bool.rec (motive := fun _ => ℕ) (ptl r x) e.2 (Nat.beq e.1 x))) ((x : ℝ) / SC)
    cases hb : Nat.beq e.1 x
    · exact ih hr x
    · have hx : e.1 = x := by simpa using hb
      simp only [pt3e, Bool.and_eq_true] at he
      rw [← hx]
      exact ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩

theorem term_boundf {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (bit : Bool) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : tok bit L U QS (selXf bit top bk f L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (tchg bit L U QS (selXf bit top bk f L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := hlb L U s hs1 hs2
    simp only [tval, selXf, tchg, Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [tok, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨hP, hM⟩, hup⟩, hdn⟩ := hok
    simp only [selXf, selU, selD, tval, tP, tM, tK, tchg] at hP hM hup hdn ⊢
    have hp := hpt QS
    obtain ⟨d, hd1, hd2, hd3⟩ := slope_pair hD L U QS (hi32 (f QS)) hLQ hQU hp.2 hP hM
      (hup.imp (fun h => h) (fun h => h)) (hdn.imp (fun h => h) (fun h => h)) s hs1 hs2
    refine ⟨d, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    rw [hSC] at hw
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun ((QS : ℝ) / 32768) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    have e : ((Nat.max (Nat.mul (Nat.sub U QS) (Nat.sub 4000000000 (Nat.add (hi32 (hi32 (f QS))) (lo32 (lbDr tD bD QS U)))))
        (Nat.mul (Nat.sub QS L) (Nat.sub 4000000000 (Nat.add (hi32 (lbDr tD bD L QS)) (lo32 (hi32 (f QS)))))) : ℕ) : ℝ)
        = ((max ((U - QS) * (4000000000 - (hi32 (hi32 (f QS)) + lo32 (lbDr tD bD QS U))))
          ((QS - L) * (4000000000 - (hi32 (lbDr tD bD L QS) + lo32 (hi32 (f QS))))) : ℕ) : ℝ) := rfl
    rw [e]
    rw [hSC] at hd3
    nlinarith [hd3, hw']

/-- one pair term in a convex basin: the tangent at `QS` (expanded terms, no charge) or the zero-order bound -/
theorem cterm_bound {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk) (hpt : PTF f) (bit : Bool)
    (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U) (c : List ℕ)
    (hok : ctok bit L U QS (selXf bit top bk f L U QS) c = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := hlb L U s hs1 hs2
    simp only [tval, selXf, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [ctok, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨⟨hP, hM⟩, hlen⟩, hch⟩, hlast⟩ := hok
    simp only [selXf, tval, tP, tM, tK] at hP hM ⊢
    have hp := hpt QS
    have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    have hconv : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
      intro x h1 h2
      exact chainOk_sound c L hch hne x h1 (by rw [hlast]; exact h2)
    set q : ℝ := (QS : ℝ) / SC with hq
    have hq1 : (L : ℝ) / SC ≤ q := div_le_div_of_nonneg_right (by exact_mod_cast hLQ) (by norm_num [SC])
    have hq2 : q ≤ (U : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hQU) (by norm_num [SC])
    have htan := tangent_le hconv hq1 hq2 hs1 hs2
    have hU1 := U1_posR
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    have hq0 : lo32 (hi32 (f QS)) ≠ 0 := by omega
    have hm0 : hi32 (hi32 (f QS)) ≠ 0 := by omega
    obtain ⟨-, hPq⟩ := hp.2.1 hq0
    obtain ⟨-, hMq⟩ := hp.2.2 hm0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨w1 q, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun q := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    rw [hSC] at hq
    rw [← hq]
    nlinarith [htan, hw']

/-- one pair term of the mixed test: convex (tangent, no charge), slope (derivative charge) or zero-order -/
theorem mterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (vb bit : Bool) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U) (c : List ℕ)
    (hok : mtok vb bit L U QS (selXf bit top bk f L U QS) (selUv vb bit tD bD QS U) (selDv vb bit tD bD L QS) c = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg vb bit L U QS (selXf bit top bk f L U QS) (selUv vb bit tD bD QS U) (selDv vb bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  cases vb
  · exact term_boundf hlb hD hpt bit L U QS hLQ hQU hok s hs1 hs2
  · obtain ⟨d, h1, h2, h3⟩ := cterm_bound hlb hpt bit L U QS hLQ hQU c hok s hs1 hs2
    refine ⟨d, h1, h2, ?_⟩
    simp only [mchg, Nat.cast_zero, mul_zero, sub_zero]
    exact h3

theorem bforce_eq (b : Bool) (k : Bool → Bool) : bforce b k = k b := by cases b <;> rfl

/-- every point of a certified region is convex -/
def RegSound (R : List (ℕ × ℕ × List ℕ)) : Prop :=
  ∀ r ∈ R, ∀ x : ℝ, (r.1 : ℝ) / SC ≤ x → x ≤ (r.2.1 : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x

theorem regOk_sound : ∀ (R : List (ℕ × ℕ × List ℕ)), regOk R = true → RegSound R := by
  intro R
  induction R with
  | nil => intro _ r hr; exact absurd hr (List.not_mem_nil)
  | cons r0 R ih =>
    intro h r hr x hx1 hx2
    have h' : (Nat.ble 1 r0.2.2.length && chainOk r0.1 r0.2.2 && Nat.beq (chainLast r0.1 r0.2.2) r0.2.1 && regOk R) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨hlen, hch⟩, hlast⟩, hR⟩ := h'
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hne : r.2.2 ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
      exact chainOk_sound r.2.2 r.1 hch hne x hx1 (by rw [hlast]; exact hx2)
    · exact ih hR r hr' x hx1 hx2

theorem inReg_sound {R : List (ℕ × ℕ × List ℕ)} (hR : RegSound R) {lo hi : ℕ} (h : inReg R lo hi = true) :
    ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  induction R with
  | nil => exact absurd h (by simp [inReg])
  | cons r R ih =>
    intro x hx1 hx2
    have h' : ((Nat.ble r.1 lo && Nat.ble hi r.2.1) || inReg R lo hi) = true := h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h'
    rcases h' with ⟨h1, h2⟩ | h'
    · have e1 : (r.1 : ℝ) / SC ≤ (lo : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h1) (by norm_num [SC])
      have e2 : (hi : ℝ) / SC ≤ (r.2.1 : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h2) (by norm_num [SC])
      exact hR r List.mem_cons_self x (e1.trans hx1) (hx2.trans e2)
    · exact ih (fun r' hr' => hR r' (List.mem_cons_of_mem r hr')) h' x hx1 hx2

/-- a pair term on a convex range: the tangent at `QS` (expanded) or the zero-order bound -/
theorem convterm_bound {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk) (hpt : PTF f) (bit : Bool)
    (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hconv : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x)
    (hok : Bool.rec (motive := fun _ => Bool) true
      (Nat.ble 1 (lo32 (hi32 (selXf bit top bk f L U QS))) && Nat.ble 1 (hi32 (hi32 (selXf bit top bk f L U QS)))) bit = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := hlb L U s hs1 hs2
    simp only [tval, selXf, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨hP, hM⟩ := hok
    simp only [selXf, tval, tP, tM, tK] at hP hM ⊢
    have hp := hpt QS
    set q : ℝ := (QS : ℝ) / SC with hq
    have hq1 : (L : ℝ) / SC ≤ q := div_le_div_of_nonneg_right (by exact_mod_cast hLQ) (by norm_num [SC])
    have hq2 : q ≤ (U : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hQU) (by norm_num [SC])
    have htan := tangent_le hconv hq1 hq2 hs1 hs2
    have hU1 := U1_posR
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    have hq0 : lo32 (hi32 (f QS)) ≠ 0 := by omega
    have hm0 : hi32 (hi32 (f QS)) ≠ 0 := by omega
    obtain ⟨-, hPq⟩ := hp.2.1 hq0
    obtain ⟨-, hMq⟩ := hp.2.2 hm0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨w1 q, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun q := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    rw [hSC] at hq
    rw [← hq]
    nlinarith [htan, hw']

theorem inRg_sound {R : ℕ × ℕ × List (List ℕ)} (hR : rgOk R = true) {lo hi : ℕ} (h : inRg R lo hi = true) :
    ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  intro x hx1 hx2
  unfold inRg at h
  rw [forceB_eq] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨hk, ha⟩, hb⟩ := h
  have hk' := allBelow_spec hR _ hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
  · exfalso
    have : (hi : ℝ) / SC < (lo : ℝ) / SC := by
      apply div_lt_div_of_pos_right _ hSC; exact_mod_cast (by omega : hi < lo)
    linarith
  · set c := R.2.2.getD (Nat.shiftRight (Nat.add lo 16384) 15) [] with hc
    have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    refine chainOk_sound c _ hch hne x (le_trans ?_ hx1) (le_trans hx2 ?_)
    · exact div_le_div_of_nonneg_right (by exact_mod_cast ha) hSC.le
    · rw [hlast]; exact div_le_div_of_nonneg_right (by exact_mod_cast hb) hSC.le

theorem cvflag {b c : Bool} (h : Bool.rec (motive := fun _ => Bool) false b c = true) : b = true := by
  cases c
  · exact absurd h (by simp)
  · exact h

/-- one pair term of the slope test with a convexity flag `cv` (set only when the range is certified convex): the
tangent (no charge, no derivative reads) when set, else the charge from the derivative reads -/
theorem rterm_boundc {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (bit : Bool) (L U QS : ℕ) (cv : Bool)
    (hcv : cv = true → ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x)
    (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : rtok cv bit L U QS (selXf bit top bk f L U QS) (selUv cv bit tD bD QS U) (selDv cv bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg cv bit L U QS (selXf bit top bk f L U QS) (selUv cv bit tD bD QS U) (selDv cv bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  revert hok hcv
  cases cv
  · intro _ hok
    exact term_boundf hlb hD hpt bit L U QS hLQ hQU hok s hs1 hs2
  · intro hcv hok
    obtain ⟨d, h1, h2, h3⟩ := convterm_bound hlb hpt bit L U QS hLQ hQU (hcv rfl) hok s hs1 hs2
    refine ⟨d, h1, h2, ?_⟩
    simp only [mchg, Nat.cast_zero, mul_zero, sub_zero]
    exact h3

/-- one pair term of the slope test: convex when its range lies in a certified convex region (tangent, no charge, no
derivative reads), else charged from the derivative reads -/
theorem rterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : List (ℕ × ℕ × List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : RegSound R) (bit : Bool) (L U QS : ℕ)
    (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : rtok (inReg R L U) bit L U QS (selXf bit top bk f L U QS) (selUv (inReg R L U) bit tD bD QS U)
      (selDv (inReg R L U) bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg (inReg R L U) bit L U QS (selXf bit top bk f L U QS) (selUv (inReg R L U) bit tD bD QS U)
          (selDv (inReg R L U) bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  revert hok
  cases hc : inReg R L U
  · intro hok
    exact term_boundf hlb hD hpt bit L U QS hLQ hQU hok s hs1 hs2
  · intro hok
    obtain ⟨d, h1, h2, h3⟩ := convterm_bound hlb hpt bit L U QS hLQ hQU (inReg_sound hR hc) hok s hs1 hs2
    refine ⟨d, h1, h2, ?_⟩
    simp only [mchg, Nat.cast_zero, mul_zero, sub_zero]
    exact h3

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
/-! ###### per-term minorants: extended tangents, certified once per pair term and combined convexly ######

A minorant leaf bounds each pair term on its range `[L, U]` by its own affine function, chosen by a linear programme
over the box: the zero-order constant, the tangent at a grid point `p`, or a convex combination of two of these.  The
tangent at `p` is a lower bound of `w` on `[L, U]` when `w` is convex on the certified region `[za, zb] ∋ p` and the
derivative table shows `w' ≥ w'(p)` on `[zb, U]` and `w' ≤ w'(p)` on `[L, za]`. -/

section MinDefs

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the side conditions of the tangent at the grid point `p` on the range `[L, U]`: `X` the point triple at `p`, `EU`
the derivative read on `[rgB k, U]`, `ED` the read on `[L, rgA k]`, `k` the region of the integer nearest to `p` -/
def tcheck (R : ℕ × ℕ × List (List ℕ)) (L U p X EU ED : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k) || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X)))))
      && (Nat.ble (rgA R k) L || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X)))))

/-- the upper derivative read of a tangent: on `[rgB k, U]` when `U` lies beyond the region, else nothing -/
def treadU (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDr tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
/-- the lower derivative read of a tangent: on `[L, rgA k]` when `L` lies before the region, else nothing -/
def treadD (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDr tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)

/-- the grid point `j ∈ [0, 8]` of the range `[L, U]`: `L + (U − L) j / 8` rounded down to a multiple of `256`, clamped to
the multiples of `256` inside `[L, U]` -/
def gpt (L U j : ℕ) : ℕ :=
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L 255) 8) 8) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U 8) 8) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) 8) 8) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the weights (out of `1024`) of a minorant term of kind `κ` (`1` tangent, `2` constant and tangent, `3` two tangents,
any other the constant) with weight field `lam`: on the constant, the first tangent, the second tangent -/
def mwc (κ lam : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 1024 0 (Nat.beq κ 3)) (Nat.sub 1024 lam) (Nat.beq κ 2))
    0 (Nat.beq κ 1)
def mw1 (κ lam : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.sub 1024 lam) (Nat.beq κ 3)) lam (Nat.beq κ 2))
    1024 (Nat.beq κ 1)
def mw2 (κ lam : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 lam (Nat.beq κ 3)

/-- a minorant term's value (units `1/(1024 U)`), its charges `(M − KU1)⁺(p − L)` and `(KU1 − M)⁺(p − L)`, its slope
claim `Σ l P` and slope weight `Σ l`, and its side conditions -/
def mval (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U c l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul c (lb top bk L U)) (Nat.add (Nat.mul l1 (lo32 (f p1))) (Nat.mul l2 (lo32 (f p2))))
def mcp (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul l1 (Nat.sub (hi32 (hi32 (f p1))) 2000000000)) (Nat.sub p1 L))
    (Nat.mul (Nat.mul l2 (Nat.sub (hi32 (hi32 (f p2))) 2000000000)) (Nat.sub p2 L))
def mcn (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul l1 (Nat.sub 2000000000 (hi32 (hi32 (f p1))))) (Nat.sub p1 L))
    (Nat.mul (Nat.mul l2 (Nat.sub 2000000000 (hi32 (hi32 (f p2))))) (Nat.sub p2 L))
def msl (f : ℕ → ℕ) (l1 l2 p1 p2 : ℕ) : ℕ := Nat.add (Nat.mul l1 (lo32 (hi32 (f p1)))) (Nat.mul l2 (lo32 (hi32 (f p2))))
def mok (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (L U l1 l2 p1 p2 : ℕ) : Bool :=
  (Nat.beq l1 0 || tcheck R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1))
    && (Nat.beq l2 0 || tcheck R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2))

end Zeta23Ext.Bridge.ThreePoint.PyrD

end MinDefs

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint

/-- on a convex interval `w'` is nondecreasing -/
theorem w1_mono_of_conv {za zb : ℝ} (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) {x y : ℝ}
    (hx : za ≤ x) (hxy : x ≤ y) (hy : y ≤ zb) : w1 x ≤ w1 y := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
    (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
    (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
  have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
  have hpos : 0 < y - x := by linarith
  have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
  nlinarith

/-- the extended tangent: the tangent at `p` is a lower bound of `wfun` on `[L, U]` when `w` is convex on `[za, zb] ∋ p`,
`w'` stays above `w'(p)` on `[zb, U]` and below it on `[L, za]` -/
theorem ext_tangent {za zb L U p : ℝ}
    (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) (hp1 : za ≤ p) (hp2 : p ≤ zb)
    (hR : ∀ x : ℝ, zb ≤ x → x ≤ U → kD x < 0 ∧ w1 p ≤ w1 x)
    (hL : ∀ x : ℝ, L ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 p)
    (hLp : L ≤ p) (hpU : p ≤ U) {s : ℝ} (hs1 : L ≤ s) (hs2 : s ≤ U) :
    wfun p + w1 p * (s - p) ≤ wfun s := by
  have hk : ∀ x, L ≤ x → x ≤ U → kD x < 0 := by
    intro x h1 h2
    rcases le_total x za with h | h
    · exact (hL x h1 h).1
    · rcases le_total x zb with h' | h'
      · exact (hc x h h').1
      · exact (hR x h' h2).1
  have hW : ∀ ξ, L ≤ ξ → ξ ≤ U → HasDerivAt wfun (w1 ξ) ξ := fun ξ h1 h2 => hasDerivAt_wfun ξ (hk ξ h1 h2).ne
  have hmono : ∀ x y, za ≤ x → x ≤ y → y ≤ zb → w1 x ≤ w1 y := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hxy with heq | hlt
    · rw [heq]
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
      (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
      (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
    have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
    have hpos : 0 < y - x := by linarith
    have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
    nlinarith
  have hge : ∀ ξ, p ≤ ξ → ξ ≤ U → w1 p ≤ w1 ξ := by
    intro ξ h1 h2
    rcases le_total ξ zb with h | h
    · exact hmono p ξ hp1 h1 h
    · exact (hR ξ h h2).2
  have hle : ∀ ξ, L ≤ ξ → ξ ≤ p → w1 ξ ≤ w1 p := by
    intro ξ h1 h2
    rcases le_total ξ za with h | h
    · exact (hL ξ h1 h).2
    · exact hmono ξ p h h2 hp2
  rcases lt_trichotomy p s with hps | hps | hps
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
      (fun y hy => (hW y (hLp.trans hy.1) (hy.2.trans hs2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hLp.trans hy.1.le) (hy.2.le.trans hs2))
    have h := hge ξ hξ.1.le (hξ.2.le.trans hs2)
    have hne : s - p ≠ 0 := by linarith
    have e : wfun s - wfun p = w1 ξ * (s - p) := by rw [hξe]; field_simp
    have hsp : 0 ≤ s - p := by linarith
    nlinarith
  · rw [hps]; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
      (fun y hy => (hW y (hs1.trans hy.1) (hy.2.trans hpU)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hs1.trans hy.1.le) (hy.2.le.trans hpU))
    have h := hle ξ (hs1.trans hξ.1.le) hξ.2.le
    have hne : p - s ≠ 0 := by linarith
    have e : wfun p - wfun s = w1 ξ * (p - s) := by rw [hξe]; field_simp
    have hsp : 0 ≤ p - s := by linarith
    nlinarith

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- a nonempty certified region is convex -/
theorem rg_conv {R : ℕ × ℕ × List (List ℕ)} (hR : rgOk R = true) {k : ℕ} (hk : k < 16) (hab : rgA R k ≤ rgB R k) :
    ∀ x : ℝ, ((rgA R k : ℕ) : ℝ) / SC ≤ x → x ≤ ((rgB R k : ℕ) : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  intro x hx1 hx2
  have hk' := allBelow_spec hR _ hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
  rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
  · omega
  · set c := R.2.2.getD k [] with hc
    have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    exact chainOk_sound c _ hch hne x hx1 (by rw [hlast]; exact hx2)

/-- the tangent at the grid point `p` is a sound minorant on `[L, U]` once `tcheck` passes: `v / 10¹⁰ ≤ w(p)`, the slope
`w'(p)` inside the point claims, and `w(p) + w'(p)(s − p) ≤ w(s)` on the range -/
theorem tangent_cert {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (L U p : ℕ)
    (h : tcheck R L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    L ≤ p ∧ p ≤ U ∧ (lo32 (f p) : ℝ) / 10000000000 ≤ wfun ((p : ℝ) / SC) ∧
      (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) ∧
      1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) ∧
      wfun ((p : ℝ) / SC) + w1 ((p : ℝ) / SC) * (s - (p : ℝ) / SC) ≤ wfun s := by
  unfold tcheck at h
  rw [forceB_eq] at h
  unfold treadU treadD at h
  rw [forceR_eq, forceR_eq] at h
  set k := Nat.shiftRight (Nat.add p 16384) 15 with hkdef
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hap⟩, hpb⟩, hLp⟩, hpU⟩, hP⟩, hM⟩, hup⟩, hdn⟩ := h
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU1 := U1_posR
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hp := hpt p
  have hq0 : lo32 (hi32 (f p)) ≠ 0 := by omega
  have hm0 : hi32 (hi32 (f p)) ≠ 0 := by omega
  obtain ⟨hkp, hPq⟩ := hp.2.1 hq0
  obtain ⟨-, hMq⟩ := hp.2.2 hm0
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  have hc := rg_conv hR hk (by omega)
  set q : ℝ := (p : ℝ) / SC with hq
  have cast_le : ∀ {m n : ℕ}, m ≤ n → (m : ℝ) / SC ≤ (n : ℝ) / SC := fun hmn =>
    div_le_div_of_nonneg_right (by exact_mod_cast hmn) hSC.le
  refine ⟨hLp, hpU, hp.1, by linarith, by linarith, ?_⟩
  have hpb' := cast_le hpb; have hap' := cast_le hap
  refine ext_tangent (za := ((rgA R k : ℕ) : ℝ) / SC) (zb := ((rgB R k : ℕ) : ℝ) / SC) (L := (L : ℝ) / SC)
    (U := (U : ℝ) / SC) hc hap' hpb' ?_ ?_ (cast_le hLp) (cast_le hpU) hs1 hs2
  · intro x hx1 hx2
    by_cases hUb : U ≤ rgB R k
    · have hx : x ≤ ((rgB R k : ℕ) : ℝ) / SC := le_trans hx2 (cast_le hUb)
      have hxe : x = ((rgB R k : ℕ) : ℝ) / SC := le_antisymm hx hx1
      refine ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx).1, ?_⟩
      rw [hxe]; exact w1_mono_of_conv hc hap' hpb' le_rfl
    · have hb' : Nat.ble U (rgB R k) = false := Bool.eq_false_iff.mpr (fun h => hUb (Nat.le_of_ble_eq_true h))
      rcases hup with hu | ⟨he1, he2⟩
      · exact absurd hu hUb
      rw [hb'] at he1 he2
      have hb := (hD _ U x hx1 hx2).1 (by simp only at he1; omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (lo32 (lbDr tD bD (rgB R k) U) : ℝ) + (hi32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith
  · intro x hx1 hx2
    by_cases haL : rgA R k ≤ L
    · have hx : ((rgA R k : ℕ) : ℝ) / SC ≤ x := le_trans (cast_le haL) hx1
      have hxe : x = ((rgA R k : ℕ) : ℝ) / SC := le_antisymm hx2 hx
      refine ⟨(hc x hx (le_trans hx2 (le_trans hap' hpb'))).1, ?_⟩
      rw [hxe]; exact w1_mono_of_conv hc le_rfl hap' hpb'
    · have hb' : Nat.ble (rgA R k) L = false := Bool.eq_false_iff.mpr (fun h => haL (Nat.le_of_ble_eq_true h))
      rcases hdn with hd | ⟨he1, he2⟩
      · exact absurd hd haL
      rw [hb'] at he1 he2
      have hb := (hD L _ x hx1 hx2).2 (by simp only at he1; omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte, Bool.false_eq_true] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (hi32 (lbDr tD bD L (rgA R k)) : ℝ) + (lo32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith

/-- one pair term of a minorant leaf: the convex combination (weights `lc`, `l1`, `l2` summing to `1024`) of the
zero-order constant and the tangents at `p1`, `p2`, at scale `SC·U`; `D` is `1024` times the combined slope -/
theorem mterm_min {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L U lc l1 l2 p1 p2 : ℕ) (hsum : lc + l1 + l2 = 1024)
    (h1 : l1 = 0 ∨ tcheck R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1) = true)
    (h2 : l2 = 0 ∨ tcheck R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (l1 : ℝ) * ((lo32 (hi32 (f p1)) : ℝ) - 2000000000) + (l2 : ℝ) * ((lo32 (hi32 (f p2)) : ℝ) - 2000000000)
        ≤ 1000000000 * D ∧
      32768 * ((lc : ℝ) * (lb top bk L U : ℝ) + (l1 : ℝ) * (lo32 (f p1) : ℝ) + (l2 : ℝ) * (lo32 (f p2) : ℝ))
        + 327680000000000 * (D * (s - (L : ℝ) / 32768))
        + 10 * ((l1 : ℝ) * ((hi32 (hi32 (f p1)) : ℝ) - 2000000000) * ((p1 : ℝ) - L)
          + (l2 : ℝ) * ((hi32 (hi32 (f p2)) : ℝ) - 2000000000) * ((p2 : ℝ) - L))
        ≤ 327680000000000 * 1024 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hlbs := hlb L U s hs1 hs2
  have hlbs' : (lb top bk L U : ℝ) ≤ 10000000000 * wfun s := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hlbs; linarith
  -- each tangent with nonzero weight, as an inequality at scale SC·U
  have tang : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheck R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      ∃ dk : ℝ, (lk : ℝ) * ((lo32 (hi32 (f pk)) : ℝ) - 2000000000) ≤ 1000000000 * ((lk : ℝ) * dk) ∧
        32768 * ((lk : ℝ) * (lo32 (f pk) : ℝ)) + 327680000000000 * (((lk : ℝ) * dk) * (s - (L : ℝ) / 32768))
          + 10 * ((lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L))
          ≤ 327680000000000 * ((lk : ℝ) * wfun s) := by
    intro lk pk hk
    rcases hk with hk | hk
    · refine ⟨0, by rw [hk]; simp, by rw [hk]; simp⟩
    obtain ⟨hLp, hpU, hv, hP, hM, htan⟩ := tangent_cert hD hpt hR L U pk hk s hs1 hs2
    rw [hSC] at hv htan hM hP
    refine ⟨w1 ((pk : ℝ) / 32768), ?_, ?_⟩
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      nlinarith
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      have hv' : (lo32 (f pk) : ℝ) ≤ 10000000000 * wfun ((pk : ℝ) / 32768) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hv; linarith
      have hpL : (0 : ℝ) ≤ (pk : ℝ) - L := sub_nonneg.mpr (by exact_mod_cast hLp)
      -- the tangent at p, rewritten from s - p to (s - L) + (L - p), with the slope above by M
      have key : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L : ℝ) / 32768))
          + 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L)) ≤ 327680000000000 * wfun s := by
        have e1 : 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L : ℝ) / 32768))
            = 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
              + 10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L)) := by ring
        rw [e1]
        have h3 : 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L))
            ≤ -(10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L))) := by
          nlinarith [mul_le_mul_of_nonneg_right hM hpL]
        nlinarith
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

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem mw_sum (κ lam : ℕ) (hl : lam ≤ 1024) : mwc κ lam + mw1 κ lam + mw2 κ lam = 1024 := by
  unfold mwc mw1 mw2
  by_cases h1 : κ = 1
  · subst h1; simp only [show Nat.beq 1 1 = true from rfl, show Nat.beq 1 2 = false from rfl, show Nat.beq 1 3 = false from rfl]
  · rw [beq_false h1]
    by_cases h2 : κ = 2
    · subst h2
      simp only [show Nat.beq 2 2 = true from rfl, show Nat.beq 2 3 = false from rfl, Nat.sub_eq]; omega
    · rw [beq_false h2]
      by_cases h3 : κ = 3
      · subst h3; simp only [show Nat.beq 3 3 = true from rfl, Nat.sub_eq]; omega
      · rw [beq_false h3]; rfl

theorem natsub_pair (M : ℕ) : ((M - 2000000000 : ℕ) : ℝ) - ((2000000000 - M : ℕ) : ℝ) = (M : ℝ) - 2000000000 := by
  rcases le_total M 2000000000 with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring

/-- one minorant term from its side conditions -/
theorem mterm_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L U κ lam p1 p2 : ℕ) (hl : lam ≤ 1024)
    (hok : mok R tD bD f L U (mw1 κ lam) (mw2 κ lam) p1 p2 = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl f (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk f L U (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L : ℝ) / 32768))
        + 10 * (mcp f L (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn f L (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  unfold mok at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_min hlb hD hpt hR L U (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 (mw_sum κ lam hl)
    h1 h2 s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheck R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      (lk : ℝ) * (((hi32 (hi32 (f pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (f pk)) : ℕ) : ℝ))
        * ((pk - L : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (tangent_cert hD hpt hR L U pk h s hs1 hs2).1]
  have e1 := pk _ _ h1
  have e2 := pk _ _ h2
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

/-- one gap's linear part: `E (g − l)` on `g − l ∈ [0, H/SC]` with `10⁹ E ≥ −N` -/
theorem gap_lo {E e H N : ℝ} (hN : 0 ≤ N) (hE : -N ≤ 1000000000 * E) (he0 : 0 ≤ e) (he1 : e ≤ H / 32768) :
    -(10 * (N * H)) ≤ 327680000000000 * (E * e) := by
  have hH : 0 ≤ H := by linarith
  rcases le_total 0 E with h | h
  · have : 0 ≤ E * e := mul_nonneg h he0
    nlinarith
  · have h1 : E * e ≥ E * (H / 32768) := by nlinarith
    nlinarith

theorem brec_ne {b : Bool} {x : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 x b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

/-- pair-sum ranges, one gap at a time (lets the instance proofs avoid `linarith` on the ranges) -/
theorem slo_add {A a : ℕ} {X x : ℝ} (h : (A : ℝ) / SC ≤ X) (h' : (a : ℝ) / SC ≤ x) : ((A + a : ℕ) : ℝ) / SC ≤ X + x := by
  push_cast; rw [add_div]; exact add_le_add h h'
theorem shi_add {A a : ℕ} {X x : ℝ} (h : X ≤ (A : ℝ) / SC) (h' : x ≤ (a : ℝ) / SC) : X + x ≤ ((A + a : ℕ) : ℝ) / SC := by
  push_cast; rw [add_div]; exact add_le_add h h'

end Zeta23Ext.Bridge.ThreePoint.PyrD

end

/-! ###### the 8-point weighted certificate `OctY30`: zero-order and minorant leaf tests, walk, cover ###### -/

set_option maxRecDepth 100000

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.OctY30

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD

def SA : ℕ := 100000000
def cN : ℕ := 701466

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 g5 g6 : ℝ) : ℝ :=
  (32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
    + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb3_t` (U = 10¹⁰; three-piece pyramid reads), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32954 l0) (Nat.mul 57979 l1)) (Nat.mul 68753 l2)) (Nat.mul 80628 l3)) (Nat.mul 68753 l4)) (Nat.mul 57979 l5)) (Nat.mul 32954 l6)) 10000000000
  ee 229856378880000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 899641212928 (lb3 top bk l1 u1))
  ee 229856378880000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 899641212928 (lb3 top bk l5 u5))
  ee 229856378880000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1145183174656 (lb3 top bk l4 u4))
  ee 229856378880000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 1145183174656 (lb3 top bk l2 u2))
  ee 229856378880000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 541650026496 (lb3 top bk l0 u0))
  ee 229856378880000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 1380651171840 (lb3 top bk l3 u3))
  ee 229856378880000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 541650026496 (lb3 top bk l6 u6))
  ee 229856378880000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 1462873620480 (lb3 top bk (Nat.add l4 l5) (Nat.add u4 u5)))
  ee 229856378880000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1462873620480 (lb3 top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 229856378880000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 1495704371200 (lb3 top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 229856378880000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 1495704371200 (lb3 top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 229856378880000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 2221964689408 (lb3 top bk (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)))
  ee 229856378880000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 2221964689408 (lb3 top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 229856378880000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 2109670621184 (lb3 top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 229856378880000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 318222008320 (lb3 top bk (Nat.add l5 l6) (Nat.add u5 u6)))
  ee 229856378880000000000 s15 (
  let s16 := Nat.add s15 (Nat.mul 318222008320 (lb3 top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 229856378880000000000 s16 (
  let s17 := Nat.add s16 (Nat.mul 3271643136000 (lb3 top bk (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6)))
  ee 229856378880000000000 s17 (
  let s18 := Nat.add s17 (Nat.mul 3271643136000 (lb3 top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 229856378880000000000 s18 (
  let s19 := Nat.add s18 (Nat.mul 2148619976704 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6)))
  ee 229856378880000000000 s19 (
  let s20 := Nat.add s19 (Nat.mul 2256360046592 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)))
  ee 229856378880000000000 s20 (
  let s21 := Nat.add s20 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6)))
  ee 229856378880000000000 s21 (
  let s22 := Nat.add s21 (Nat.mul 2148619976704 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 229856378880000000000 s22 (
  let s23 := Nat.add s22 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)))
  ee 229856378880000000000 s23 (
  let s24 := Nat.add s23 (Nat.mul 6553600000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6)))
  ee 229856378880000000000 s24 (
  let s25 := Nat.add s24 (Nat.mul 5156864000 (lb3 top bk (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)))
  ee 229856378880000000000 s25 (
  let s26 := Nat.add s25 (Nat.mul 5156864000 (lb3 top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 229856378880000000000 s26 (
  let s27 := Nat.add s26 (Nat.mul 0 (lb3 top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 229856378880000000000 s27 (
  let s28 := Nat.add s27 (Nat.mul 0 (lb3 top bk (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6)))
  Nat.ble 229856378880000000000 s28))))))))))))))))))))))))))))


/-- the minorant inequality of a box, given per term its kind `k`, weight `m` and grid points `p`, `r`:
`1024 cN SC U + RU (Σ a mcn + Σ_r (u − l) N_r) ≤ 1024 U Σ b l + SC Σ a mval + RU Σ a mcp` -/
def mscheck (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) (k21 m21 p21 r21 : ℕ) (k22 m22 p22 r22 : ℕ) (k23 m23 p23 r23 : ℕ) (k25 m25 p25 r25 : ℕ) (k26 m26 p26 r26 : ℕ) (k27 m27 p27 r27 : ℕ) : Bool :=
  ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((Nat.ble l0 u0 && Nat.ble l1 u1) && Nat.ble l2 u2) && Nat.ble l3 u3) && Nat.ble l4 u4) && Nat.ble l5 u5) && Nat.ble l6 u6) && Nat.ble m0 1024) && mok R tD bD f l0 u0 (mw1 k0 m0) (mw2 k0 m0) p0 r0) && Nat.ble m1 1024) && mok R tD bD f (Nat.add l0 l1) (Nat.add u0 u1) (mw1 k1 m1) (mw2 k1 m1) p1 r1) && Nat.ble m3 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mw1 k3 m3) (mw2 k3 m3) p3 r3) && Nat.ble m4 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mw1 k4 m4) (mw2 k4 m4) p4 r4) && Nat.ble m5 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mw1 k5 m5) (mw2 k5 m5) p5 r5) && Nat.ble m6 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (mw1 k6 m6) (mw2 k6 m6) p6 r6) && Nat.ble m7 1024) && mok R tD bD f l1 u1 (mw1 k7 m7) (mw2 k7 m7) p7 r7) && Nat.ble m8 1024) && mok R tD bD f (Nat.add l1 l2) (Nat.add u1 u2) (mw1 k8 m8) (mw2 k8 m8) p8 r8) && Nat.ble m9 1024) && mok R tD bD f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mw1 k9 m9) (mw2 k9 m9) p9 r9) && Nat.ble m10 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mw1 k10 m10) (mw2 k10 m10) p10 r10) && Nat.ble m11 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mw1 k11 m11) (mw2 k11 m11) p11 r11) && Nat.ble m12 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (mw1 k12 m12) (mw2 k12 m12) p12 r12) && Nat.ble m13 1024) && mok R tD bD f l2 u2 (mw1 k13 m13) (mw2 k13 m13) p13 r13) && Nat.ble m14 1024) && mok R tD bD f (Nat.add l2 l3) (Nat.add u2 u3) (mw1 k14 m14) (mw2 k14 m14) p14 r14) && Nat.ble m15 1024) && mok R tD bD f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mw1 k15 m15) (mw2 k15 m15) p15 r15) && Nat.ble m16 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mw1 k16 m16) (mw2 k16 m16) p16 r16) && Nat.ble m17 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (mw1 k17 m17) (mw2 k17 m17) p17 r17) && Nat.ble m18 1024) && mok R tD bD f l3 u3 (mw1 k18 m18) (mw2 k18 m18) p18 r18) && Nat.ble m19 1024) && mok R tD bD f (Nat.add l3 l4) (Nat.add u3 u4) (mw1 k19 m19) (mw2 k19 m19) p19 r19) && Nat.ble m20 1024) && mok R tD bD f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mw1 k20 m20) (mw2 k20 m20) p20 r20) && Nat.ble m21 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (mw1 k21 m21) (mw2 k21 m21) p21 r21) && Nat.ble m22 1024) && mok R tD bD f l4 u4 (mw1 k22 m22) (mw2 k22 m22) p22 r22) && Nat.ble m23 1024) && mok R tD bD f (Nat.add l4 l5) (Nat.add u4 u5) (mw1 k23 m23) (mw2 k23 m23) p23 r23) && Nat.ble m25 1024) && mok R tD bD f l5 u5 (mw1 k25 m25) (mw2 k25 m25) p25 r25) && Nat.ble m26 1024) && mok R tD bD f (Nat.add l5 l6) (Nat.add u5 u6) (mw1 k26 m26) (mw2 k26 m26) p26 r26) && Nat.ble m27 1024) && mok R tD bD f l6 u6 (mw1 k27 m27) (mw2 k27 m27) p27 r27) && Nat.ble (Nat.add 235372931973120000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mcn f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mcn f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mcn f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mcn f l1 (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mcn f (Nat.add l1 l2) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mcn f (Nat.add (Nat.add l1 l2) l3) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mcn f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mcn f l2 (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mcn f (Nat.add l2 l3) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mcn f (Nat.add (Nat.add l2 l3) l4) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mcn f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mcn f l3 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mcn f (Nat.add l3 l4) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mcn f (Nat.add (Nat.add l3 l4) l5) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mcn f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mcn f l4 (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mcn f (Nat.add l4 l5) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mcn f l5 (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mcn f (Nat.add l5 l6) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mcn f l6 (mw1 k27 m27) (mw2 k27 m27) p27 r27))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub u0 l0) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (Nat.add (mw1 k0 m0) (mw2 k0 m0))) (Nat.mul 9711365 (Nat.add (mw1 k1 m1) (mw2 k1 m1)))) (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 33744896000000000 (Nat.mul 16529847 (msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0))) (Nat.mul 9711365 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))))) (Nat.mul (Nat.sub u1 l1) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 9711365 (Nat.add (mw1 k1 m1) (mw2 k1 m1))) (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 27454871 (Nat.add (mw1 k7 m7) (mw2 k7 m7)))) (Nat.mul 44643360 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 59370496000000000 (Nat.mul 9711365 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12)))))) (Nat.mul (Nat.sub u2 l2) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 44643360 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 34948217 (Nat.add (mw1 k13 m13) (mw2 k13 m13)))) (Nat.mul 45645275 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 70403072000000000 (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 44643360 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)))))) (Nat.mul (Nat.sub u3 l3) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 45645275 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 42134130 (Nat.add (mw1 k18 m18) (mw2 k18 m18)))) (Nat.mul 45645275 (Nat.add (mw1 k19 m19) (mw2 k19 m19)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82563072000000000 (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 45645275 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21)))))) (Nat.mul (Nat.sub u4 l4) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 45645275 (Nat.add (mw1 k19 m19) (mw2 k19 m19)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 34948217 (Nat.add (mw1 k22 m22) (mw2 k22 m22)))) (Nat.mul 44643360 (Nat.add (mw1 k23 m23) (mw2 k23 m23))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 70403072000000000 (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 45645275 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23)))))) (Nat.mul (Nat.sub u5 l5) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 44643360 (Nat.add (mw1 k23 m23) (mw2 k23 m23)))) (Nat.mul 27454871 (Nat.add (mw1 k25 m25) (mw2 k25 m25)))) (Nat.mul 9711365 (Nat.add (mw1 k26 m26) (mw2 k26 m26))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 59370496000000000 (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 44643360 (msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26)))))) (Nat.mul (Nat.sub u6 l6) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 9711365 (Nat.add (mw1 k26 m26) (mw2 k26 m26)))) (Nat.mul 16529847 (Nat.add (mw1 k27 m27) (mw2 k27 m27))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 33744896000000000 (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 9711365 (msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27))))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32954 l0) (Nat.mul 57979 l1)) (Nat.mul 68753 l2)) (Nat.mul 80628 l3)) (Nat.mul 68753 l4)) (Nat.mul 57979 l5)) (Nat.mul 32954 l6))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mval top bk f l0 u0 (mwc k0 m0) (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mval top bk f (Nat.add l0 l1) (Nat.add u0 u1) (mwc k1 m1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mval top bk f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mwc k3 m3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mwc k4 m4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mwc k5 m5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (mwc k6 m6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mval top bk f l1 u1 (mwc k7 m7) (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mval top bk f (Nat.add l1 l2) (Nat.add u1 u2) (mwc k8 m8) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mval top bk f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mwc k9 m9) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mval top bk f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mwc k10 m10) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mwc k11 m11) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (mwc k12 m12) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mval top bk f l2 u2 (mwc k13 m13) (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mval top bk f (Nat.add l2 l3) (Nat.add u2 u3) (mwc k14 m14) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mval top bk f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mwc k15 m15) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mval top bk f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mwc k16 m16) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (mwc k17 m17) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mval top bk f l3 u3 (mwc k18 m18) (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mval top bk f (Nat.add l3 l4) (Nat.add u3 u4) (mwc k19 m19) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mval top bk f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mwc k20 m20) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mval top bk f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (mwc k21 m21) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mval top bk f l4 u4 (mwc k22 m22) (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mval top bk f (Nat.add l4 l5) (Nat.add u4 u5) (mwc k23 m23) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mval top bk f l5 u5 (mwc k25 m25) (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mval top bk f (Nat.add l5 l6) (Nat.add u5 u6) (mwc k26 m26) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mval top bk f l6 u6 (mwc k27 m27) (mw1 k27 m27) (mw2 k27 m27) p27 r27))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mcp f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mcp f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mcp f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mcp f l1 (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mcp f (Nat.add l1 l2) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mcp f (Nat.add (Nat.add l1 l2) l3) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mcp f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mcp f l2 (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mcp f (Nat.add l2 l3) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mcp f (Nat.add (Nat.add l2 l3) l4) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mcp f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mcp f l3 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mcp f (Nat.add l3 l4) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mcp f (Nat.add (Nat.add l3 l4) l5) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mcp f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mcp f l4 (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mcp f (Nat.add l4 l5) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mcp f l5 (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mcp f (Nat.add l5 l6) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mcp f l6 (mw1 k27 m27) (mw2 k27 m27) p27 r27)))))

/-- the payload length of a minorant term of kind `k` -/
def mlen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 20 (Nat.beq k 3)) 16 (Nat.beq k 2)) 6 (Nat.beq k 1)

/-- a minorant leaf: the payload length when the check passes, else `0` -/
def mleafN (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR 0 fun o0 =>
  forceR (Nat.land (Nat.shiftRight w o0) 3) fun k0 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o0 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o0 6)) 1023) (Nat.beq k0 2)) fun m0 =>
  forceR (gpt l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 2)) 15)) fun p0 =>
  forceR (gpt l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 6)) 15)) fun r0 =>
  forceR (Nat.add o0 (mlen k0)) fun o1 =>
  forceR (Nat.land (Nat.shiftRight w o1) 3) fun k1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o1 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o1 6)) 1023) (Nat.beq k1 2)) fun m1 =>
  forceR (gpt (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 2)) 15)) fun p1 =>
  forceR (gpt (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 6)) 15)) fun r1 =>
  forceR (Nat.add o1 (mlen k1)) fun o2 =>
  forceR (Nat.land (Nat.shiftRight w o2) 3) fun k3 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o2 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o2 6)) 1023) (Nat.beq k3 2)) fun m3 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o2 2)) 15)) fun p3 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o2 6)) 15)) fun r3 =>
  forceR (Nat.add o2 (mlen k3)) fun o3 =>
  forceR (Nat.land (Nat.shiftRight w o3) 3) fun k4 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o3 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o3 6)) 1023) (Nat.beq k4 2)) fun m4 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o3 2)) 15)) fun p4 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o3 6)) 15)) fun r4 =>
  forceR (Nat.add o3 (mlen k4)) fun o4 =>
  forceR (Nat.land (Nat.shiftRight w o4) 3) fun k5 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o4 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o4 6)) 1023) (Nat.beq k5 2)) fun m5 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o4 2)) 15)) fun p5 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o4 6)) 15)) fun r5 =>
  forceR (Nat.add o4 (mlen k5)) fun o5 =>
  forceR (Nat.land (Nat.shiftRight w o5) 3) fun k6 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o5 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o5 6)) 1023) (Nat.beq k6 2)) fun m6 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o5 2)) 15)) fun p6 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o5 6)) 15)) fun r6 =>
  forceR (Nat.add o5 (mlen k6)) fun o6 =>
  forceR (Nat.land (Nat.shiftRight w o6) 3) fun k7 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o6 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o6 6)) 1023) (Nat.beq k7 2)) fun m7 =>
  forceR (gpt l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 2)) 15)) fun p7 =>
  forceR (gpt l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 6)) 15)) fun r7 =>
  forceR (Nat.add o6 (mlen k7)) fun o7 =>
  forceR (Nat.land (Nat.shiftRight w o7) 3) fun k8 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o7 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o7 6)) 1023) (Nat.beq k8 2)) fun m8 =>
  forceR (gpt (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 2)) 15)) fun p8 =>
  forceR (gpt (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 6)) 15)) fun r8 =>
  forceR (Nat.add o7 (mlen k8)) fun o8 =>
  forceR (Nat.land (Nat.shiftRight w o8) 3) fun k9 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o8 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o8 6)) 1023) (Nat.beq k9 2)) fun m9 =>
  forceR (gpt (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 2)) 15)) fun p9 =>
  forceR (gpt (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 6)) 15)) fun r9 =>
  forceR (Nat.add o8 (mlen k9)) fun o9 =>
  forceR (Nat.land (Nat.shiftRight w o9) 3) fun k10 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o9 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o9 6)) 1023) (Nat.beq k10 2)) fun m10 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 2)) 15)) fun p10 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 6)) 15)) fun r10 =>
  forceR (Nat.add o9 (mlen k10)) fun o10 =>
  forceR (Nat.land (Nat.shiftRight w o10) 3) fun k11 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o10 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o10 6)) 1023) (Nat.beq k11 2)) fun m11 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 2)) 15)) fun p11 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 6)) 15)) fun r11 =>
  forceR (Nat.add o10 (mlen k11)) fun o11 =>
  forceR (Nat.land (Nat.shiftRight w o11) 3) fun k12 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o11 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o11 6)) 1023) (Nat.beq k12 2)) fun m12 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o11 2)) 15)) fun p12 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o11 6)) 15)) fun r12 =>
  forceR (Nat.add o11 (mlen k12)) fun o12 =>
  forceR (Nat.land (Nat.shiftRight w o12) 3) fun k13 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o12 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o12 6)) 1023) (Nat.beq k13 2)) fun m13 =>
  forceR (gpt l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o12 2)) 15)) fun p13 =>
  forceR (gpt l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o12 6)) 15)) fun r13 =>
  forceR (Nat.add o12 (mlen k13)) fun o13 =>
  forceR (Nat.land (Nat.shiftRight w o13) 3) fun k14 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o13 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o13 6)) 1023) (Nat.beq k14 2)) fun m14 =>
  forceR (gpt (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o13 2)) 15)) fun p14 =>
  forceR (gpt (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o13 6)) 15)) fun r14 =>
  forceR (Nat.add o13 (mlen k14)) fun o14 =>
  forceR (Nat.land (Nat.shiftRight w o14) 3) fun k15 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o14 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o14 6)) 1023) (Nat.beq k15 2)) fun m15 =>
  forceR (gpt (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o14 2)) 15)) fun p15 =>
  forceR (gpt (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o14 6)) 15)) fun r15 =>
  forceR (Nat.add o14 (mlen k15)) fun o15 =>
  forceR (Nat.land (Nat.shiftRight w o15) 3) fun k16 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o15 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o15 6)) 1023) (Nat.beq k16 2)) fun m16 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o15 2)) 15)) fun p16 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o15 6)) 15)) fun r16 =>
  forceR (Nat.add o15 (mlen k16)) fun o16 =>
  forceR (Nat.land (Nat.shiftRight w o16) 3) fun k17 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o16 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o16 6)) 1023) (Nat.beq k17 2)) fun m17 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o16 2)) 15)) fun p17 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o16 6)) 15)) fun r17 =>
  forceR (Nat.add o16 (mlen k17)) fun o17 =>
  forceR (Nat.land (Nat.shiftRight w o17) 3) fun k18 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o17 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o17 6)) 1023) (Nat.beq k18 2)) fun m18 =>
  forceR (gpt l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o17 2)) 15)) fun p18 =>
  forceR (gpt l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o17 6)) 15)) fun r18 =>
  forceR (Nat.add o17 (mlen k18)) fun o18 =>
  forceR (Nat.land (Nat.shiftRight w o18) 3) fun k19 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o18 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o18 6)) 1023) (Nat.beq k19 2)) fun m19 =>
  forceR (gpt (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o18 2)) 15)) fun p19 =>
  forceR (gpt (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o18 6)) 15)) fun r19 =>
  forceR (Nat.add o18 (mlen k19)) fun o19 =>
  forceR (Nat.land (Nat.shiftRight w o19) 3) fun k20 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o19 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o19 6)) 1023) (Nat.beq k20 2)) fun m20 =>
  forceR (gpt (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o19 2)) 15)) fun p20 =>
  forceR (gpt (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o19 6)) 15)) fun r20 =>
  forceR (Nat.add o19 (mlen k20)) fun o20 =>
  forceR (Nat.land (Nat.shiftRight w o20) 3) fun k21 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o20 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o20 6)) 1023) (Nat.beq k21 2)) fun m21 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o20 2)) 15)) fun p21 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o20 6)) 15)) fun r21 =>
  forceR (Nat.add o20 (mlen k21)) fun o21 =>
  forceR (Nat.land (Nat.shiftRight w o21) 3) fun k22 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o21 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o21 6)) 1023) (Nat.beq k22 2)) fun m22 =>
  forceR (gpt l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o21 2)) 15)) fun p22 =>
  forceR (gpt l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o21 6)) 15)) fun r22 =>
  forceR (Nat.add o21 (mlen k22)) fun o22 =>
  forceR (Nat.land (Nat.shiftRight w o22) 3) fun k23 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o22 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o22 6)) 1023) (Nat.beq k23 2)) fun m23 =>
  forceR (gpt (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o22 2)) 15)) fun p23 =>
  forceR (gpt (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o22 6)) 15)) fun r23 =>
  forceR (Nat.add o22 (mlen k23)) fun o23 =>
  forceR (Nat.land (Nat.shiftRight w o23) 3) fun k25 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o23 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o23 6)) 1023) (Nat.beq k25 2)) fun m25 =>
  forceR (gpt l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o23 2)) 15)) fun p25 =>
  forceR (gpt l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o23 6)) 15)) fun r25 =>
  forceR (Nat.add o23 (mlen k25)) fun o24 =>
  forceR (Nat.land (Nat.shiftRight w o24) 3) fun k26 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o24 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o24 6)) 1023) (Nat.beq k26 2)) fun m26 =>
  forceR (gpt (Nat.add l5 l6) (Nat.add u5 u6) (Nat.land (Nat.shiftRight w (Nat.add o24 2)) 15)) fun p26 =>
  forceR (gpt (Nat.add l5 l6) (Nat.add u5 u6) (Nat.land (Nat.shiftRight w (Nat.add o24 6)) 15)) fun r26 =>
  forceR (Nat.add o24 (mlen k26)) fun o25 =>
  forceR (Nat.land (Nat.shiftRight w o25) 3) fun k27 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o25 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o25 6)) 1023) (Nat.beq k27 2)) fun m27 =>
  forceR (gpt l6 u6 (Nat.land (Nat.shiftRight w (Nat.add o25 2)) 15)) fun p27 =>
  forceR (gpt l6 u6 (Nat.land (Nat.shiftRight w (Nat.add o25 6)) 15)) fun r27 =>
  forceR (Nat.add o25 (mlen k27)) fun o26 =>
  Bool.rec (motive := fun _ => ℕ) 0 o26 (mscheck top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 k0 m0 p0 r0 k1 m1 p1 r1 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20 k21 m21 p21 r21 k22 m22 p22 r22 k23 m23 p23 r23 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27)


/-- the type of a walk continuation: position and the coordinates to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- a split on gap 0: the lower half (`u0 := q`) from `pos + 4`, then the upper half from where it ends -/
def split0 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l0 u0) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 1: the lower half (`u1 := q`) from `pos + 4`, then the upper half from where it ends -/
def split1 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l1 u1) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 2: the lower half (`u2 := q`) from `pos + 4`, then the upper half from where it ends -/
def split2 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l2 u2) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 3: the lower half (`u3 := q`) from `pos + 4`, then the upper half from where it ends -/
def split3 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l3 u3) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 4: the lower half (`u4 := q`) from `pos + 4`, then the upper half from where it ends -/
def split4 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l4 u4) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 5: the lower half (`u5 := q`) from `pos + 4`, then the upper half from where it ends -/
def split5 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l5 u5) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 6: the lower half (`u6 := q`) from `pos + 4`, then the upper half from where it ends -/
def split6 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l6 u6) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 q
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q u6) (0) (Nat.beq p 0)

/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (split6 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 5)) (split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 4)) (split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 3)) (split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 2)) (split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 1)) (split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 0)

/-- a leaf (bit 0 clear; bit 1 the kind: zero-order, or minorant with its payload from bit 2): in the reflected
half-space, or the leaf's own test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 2) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)) (forceR (mleafN top bk tD bD pb R (Nat.shiftRight w 2) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) fun n => Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) (0) (Nat.beq n 0)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) (Nat.add pos 2) (Nat.ble (Nat.add u6 1) l0)

/-- the bisection walk (`Nat.rec` on the fuel): the node word is `bits >>> pos` (bit 0 split, bits 1..3 axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Prop :=
  ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 ∨ g6 < g0

theorem ee_or {C s : ℕ} {rest : Bool} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    229856378880000000000 ≤ 10000000000 * (32954 * l0 + 57979 * l1 + 68753 * l2 + 80628 * l3 + 68753 * l4 + 57979 * l5 + 32954 * l6) + 32768 * (16529847 * lb3 top bk (l0) (u0) + 9711365 * lb3 top bk (l0 + l1) (u0 + u1) + 0 * lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) + 99842625 * lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 65570678 * lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 100000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) + 200000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) + 27454871 * lb3 top bk (l1) (u1) + 44643360 * lb3 top bk (l1 + l2) (u1 + u2) + 67808981 * lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) + 157375 * lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 68858644 * lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) + 100000000 * lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) + 34948217 * lb3 top bk (l2) (u2) + 45645275 * lb3 top bk (l2 + l3) (u2 + u3) + 64382038 * lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) + 157375 * lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) + 65570678 * lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) + 42134130 * lb3 top bk (l3) (u3) + 45645275 * lb3 top bk (l3 + l4) (u3 + u4) + 67808981 * lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) + 99842625 * lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) + 34948217 * lb3 top bk (l4) (u4) + 44643360 * lb3 top bk (l4 + l5) (u4 + u5) + 0 * lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) + 27454871 * lb3 top bk (l5) (u5) + 9711365 * lb3 top bk (l5 + l6) (u5 + u6) + 16529847 * lb3 top bk (l6) (u6)) := by
  unfold leafOK at h
  dsimp only at h
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 8000000 in
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
  have w0 := lb3_sound hlb (l0) (u0) (g0) h01 h02
  have w1 := lb3_sound hlb (l0 + l1) (u0 + u1) (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  have w2 := lb3_sound hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (slo_add (slo_add h01 h11) h21) (shi_add (shi_add h02 h12) h22)
  have w3 := lb3_sound hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  have w4 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  have w5 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  have w6 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (g0 + g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52) h62)
  have w7 := lb3_sound hlb (l1) (u1) (g1) h11 h12
  have w8 := lb3_sound hlb (l1 + l2) (u1 + u2) (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  have w9 := lb3_sound hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  have w10 := lb3_sound hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  have w11 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  have w12 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52) h62)
  have w13 := lb3_sound hlb (l2) (u2) (g2) h21 h22
  have w14 := lb3_sound hlb (l2 + l3) (u2 + u3) (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  have w15 := lb3_sound hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  have w16 := lb3_sound hlb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  have w17 := lb3_sound hlb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add h21 h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add h22 h32) h42) h52) h62)
  have w18 := lb3_sound hlb (l3) (u3) (g3) h31 h32
  have w19 := lb3_sound hlb (l3 + l4) (u3 + u4) (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  have w20 := lb3_sound hlb (l3 + l4 + l5) (u3 + u4 + u5) (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  have w21 := lb3_sound hlb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add h31 h41) h51) h61) (shi_add (shi_add (shi_add h32 h42) h52) h62)
  have w22 := lb3_sound hlb (l4) (u4) (g4) h41 h42
  have w23 := lb3_sound hlb (l4 + l5) (u4 + u5) (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  have w24 := lb3_sound hlb (l4 + l5 + l6) (u4 + u5 + u6) (g4 + g5 + g6) (slo_add (slo_add h41 h51) h61) (shi_add (shi_add h42 h52) h62)
  have w25 := lb3_sound hlb (l5) (u5) (g5) h51 h52
  have w26 := lb3_sound hlb (l5 + l6) (u5 + u6) (g5 + g6) (slo_add h51 h61) (shi_add h52 h62)
  have w27 := lb3_sound hlb (l6) (u6) (g6) h61 h62
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 32954 * ((l0 : ℝ) / SC) + 57979 * ((l1 : ℝ) / SC) + 68753 * ((l2 : ℝ) / SC) + 80628 * ((l3 : ℝ) / SC) + 68753 * ((l4 : ℝ) / SC) + 57979 * ((l5 : ℝ) / SC) + 32954 * ((l6 : ℝ) / SC) with hL
  set Wt : ℝ := 16529847 * ((lb3 top bk (l0) (u0) : ℝ) / 10000000000) + 9711365 * ((lb3 top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 99842625 * ((lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 65570678 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 200000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 27454871 * ((lb3 top bk (l1) (u1) : ℝ) / 10000000000) + 44643360 * ((lb3 top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 67808981 * ((lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 157375 * ((lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 68858644 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 34948217 * ((lb3 top bk (l2) (u2) : ℝ) / 10000000000) + 45645275 * ((lb3 top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 64382038 * ((lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 157375 * ((lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 65570678 * ((lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 42134130 * ((lb3 top bk (l3) (u3) : ℝ) / 10000000000) + 45645275 * ((lb3 top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 67808981 * ((lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) / 10000000000) + 99842625 * ((lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 34948217 * ((lb3 top bk (l4) (u4) : ℝ) / 10000000000) + 44643360 * ((lb3 top bk (l4 + l5) (u4 + u5) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) : ℝ) / 10000000000) + 27454871 * ((lb3 top bk (l5) (u5) : ℝ) / 10000000000) + 9711365 * ((lb3 top bk (l5 + l6) (u5 + u6) : ℝ) / 10000000000) + 16529847 * ((lb3 top bk (l6) (u6) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (32954 * (l0 : ℝ) + 57979 * (l1 : ℝ) + 68753 * (l2 : ℝ) + 80628 * (l3 : ℝ) + 68753 * (l4 : ℝ) + 57979 * (l5 : ℝ) + 32954 * (l6 : ℝ)) + 32768 * (16529847 * (lb3 top bk (l0) (u0) : ℝ) + 9711365 * (lb3 top bk (l0 + l1) (u0 + u1) : ℝ) + 0 * (lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 99842625 * (lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 65570678 * (lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 100000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) + 200000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) : ℝ) + 27454871 * (lb3 top bk (l1) (u1) : ℝ) + 44643360 * (lb3 top bk (l1 + l2) (u1 + u2) : ℝ) + 67808981 * (lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 157375 * (lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 68858644 * (lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) + 100000000 * (lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) : ℝ) + 34948217 * (lb3 top bk (l2) (u2) : ℝ) + 45645275 * (lb3 top bk (l2 + l3) (u2 + u3) : ℝ) + 64382038 * (lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 157375 * (lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) + 65570678 * (lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) : ℝ) + 42134130 * (lb3 top bk (l3) (u3) : ℝ) + 45645275 * (lb3 top bk (l3 + l4) (u3 + u4) : ℝ) + 67808981 * (lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) + 99842625 * (lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) : ℝ) + 34948217 * (lb3 top bk (l4) (u4) : ℝ) + 44643360 * (lb3 top bk (l4 + l5) (u4 + u5) : ℝ) + 0 * (lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) : ℝ) + 27454871 * (lb3 top bk (l5) (u5) : ℝ) + 9711365 * (lb3 top bk (l5 + l6) (u5 + u6) : ℝ) + 16529847 * (lb3 top bk (l6) (u6) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 229856378880000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
      + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)) * SA
      = 32954 * g0 + 57979 * g1 + 68753 * g2 + 80628 * g3 + 68753 * g4 + 57979 * g5 + 32954 * g6 + 16529847 * wfun (g0) + 9711365 * wfun (g0 + g1) + 0 * wfun (g0 + g1 + g2) + 99842625 * wfun (g0 + g1 + g2 + g3) + 65570678 * wfun (g0 + g1 + g2 + g3 + g4) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + 27454871 * wfun (g1) + 44643360 * wfun (g1 + g2) + 67808981 * wfun (g1 + g2 + g3) + 157375 * wfun (g1 + g2 + g3 + g4) + 68858644 * wfun (g1 + g2 + g3 + g4 + g5) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5 + g6) + 34948217 * wfun (g2) + 45645275 * wfun (g2 + g3) + 64382038 * wfun (g2 + g3 + g4) + 157375 * wfun (g2 + g3 + g4 + g5) + 65570678 * wfun (g2 + g3 + g4 + g5 + g6) + 42134130 * wfun (g3) + 45645275 * wfun (g3 + g4) + 67808981 * wfun (g3 + g4 + g5) + 99842625 * wfun (g3 + g4 + g5 + g6) + 34948217 * wfun (g4) + 44643360 * wfun (g4 + g5) + 0 * wfun (g4 + g5 + g6) + 27454871 * wfun (g5) + 9711365 * wfun (g5 + g6) + 16529847 * wfun (g6) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linear_combination hq' + 32954 * h01 + 57979 * h11 + 68753 * h21 + 80628 * h31 + 68753 * h41 + 57979 * h51 + 32954 * h61 + 16529847 * w0 + 9711365 * w1 + 99842625 * w3 + 65570678 * w4 + 100000000 * w5 + 200000000 * w6 + 27454871 * w7 + 44643360 * w8 + 67808981 * w9 + 157375 * w10 + 68858644 * w11 + 100000000 * w12 + 34948217 * w13 + 45645275 * w14 + 64382038 * w15 + 157375 * w16 + 65570678 * w17 + 42134130 * w18 + 45645275 * w19 + 67808981 * w20 + 99842625 * w21 + 34948217 * w22 + 44643360 * w23 + 27454871 * w25 + 9711365 * w26 + 16529847 * w27

set_option maxHeartbeats 40000000 in
theorem mscheck_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) (k21 m21 p21 r21 : ℕ) (k22 m22 p22 r22 : ℕ) (k23 m23 p23 r23 : ℕ) (k25 m25 p25 r25 : ℕ) (k26 m26 p26 r26 : ℕ) (k27 m27 p27 r27 : ℕ) (h : mscheck top bk tD bD f R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 k0 m0 p0 r0 k1 m1 p1 r1 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20 k21 m21 p21 r21 k22 m22 p22 r22 k23 m23 p23 r23 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  unfold mscheck at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlu0, hlu1⟩, hlu2⟩, hlu3⟩, hlu4⟩, hlu5⟩, hlu6⟩, hm0⟩, hok0⟩, hm1⟩, hok1⟩, hm3⟩, hok3⟩, hm4⟩, hok4⟩, hm5⟩, hok5⟩, hm6⟩, hok6⟩, hm7⟩, hok7⟩, hm8⟩, hok8⟩, hm9⟩, hok9⟩, hm10⟩, hok10⟩, hm11⟩, hok11⟩, hm12⟩, hok12⟩, hm13⟩, hok13⟩, hm14⟩, hok14⟩, hm15⟩, hok15⟩, hm16⟩, hok16⟩, hm17⟩, hok17⟩, hm18⟩, hok18⟩, hm19⟩, hok19⟩, hm20⟩, hok20⟩, hm21⟩, hok21⟩, hm22⟩, hok22⟩, hm23⟩, hok23⟩, hm25⟩, hok25⟩, hm26⟩, hok26⟩, hm27⟩, hok27⟩, hmain⟩ := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨D0, hDl0, hb0⟩ := mterm_ok hlb hD hpt hR (l0) (u0) k0 m0 p0 r0 hm0 hok0
    (g0) h01 h02
  push_cast at hb0
  obtain ⟨D1, hDl1, hb1⟩ := mterm_ok hlb hD hpt hR (l0 + l1) (u0 + u1) k1 m1 p1 r1 hm1 hok1
    (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  push_cast at hb1
  obtain ⟨D3, hDl3, hb3⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) k3 m3 p3 r3 hm3 hok3
    (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  push_cast at hb3
  obtain ⟨D4, hDl4, hb4⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) k4 m4 p4 r4 hm4 hok4
    (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  push_cast at hb4
  obtain ⟨D5, hDl5, hb5⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) k5 m5 p5 r5 hm5 hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  push_cast at hb5
  obtain ⟨D6, hDl6, hb6⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) k6 m6 p6 r6 hm6 hok6
    (g0 + g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52) h62)
  push_cast at hb6
  obtain ⟨D7, hDl7, hb7⟩ := mterm_ok hlb hD hpt hR (l1) (u1) k7 m7 p7 r7 hm7 hok7
    (g1) h11 h12
  push_cast at hb7
  obtain ⟨D8, hDl8, hb8⟩ := mterm_ok hlb hD hpt hR (l1 + l2) (u1 + u2) k8 m8 p8 r8 hm8 hok8
    (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  push_cast at hb8
  obtain ⟨D9, hDl9, hb9⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3) (u1 + u2 + u3) k9 m9 p9 r9 hm9 hok9
    (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  push_cast at hb9
  obtain ⟨D10, hDl10, hb10⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) k10 m10 p10 r10 hm10 hok10
    (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  push_cast at hb10
  obtain ⟨D11, hDl11, hb11⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) k11 m11 p11 r11 hm11 hok11
    (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  push_cast at hb11
  obtain ⟨D12, hDl12, hb12⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) k12 m12 p12 r12 hm12 hok12
    (g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52) h62)
  push_cast at hb12
  obtain ⟨D13, hDl13, hb13⟩ := mterm_ok hlb hD hpt hR (l2) (u2) k13 m13 p13 r13 hm13 hok13
    (g2) h21 h22
  push_cast at hb13
  obtain ⟨D14, hDl14, hb14⟩ := mterm_ok hlb hD hpt hR (l2 + l3) (u2 + u3) k14 m14 p14 r14 hm14 hok14
    (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  push_cast at hb14
  obtain ⟨D15, hDl15, hb15⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4) (u2 + u3 + u4) k15 m15 p15 r15 hm15 hok15
    (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  push_cast at hb15
  obtain ⟨D16, hDl16, hb16⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) k16 m16 p16 r16 hm16 hok16
    (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  push_cast at hb16
  obtain ⟨D17, hDl17, hb17⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) k17 m17 p17 r17 hm17 hok17
    (g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add h21 h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add h22 h32) h42) h52) h62)
  push_cast at hb17
  obtain ⟨D18, hDl18, hb18⟩ := mterm_ok hlb hD hpt hR (l3) (u3) k18 m18 p18 r18 hm18 hok18
    (g3) h31 h32
  push_cast at hb18
  obtain ⟨D19, hDl19, hb19⟩ := mterm_ok hlb hD hpt hR (l3 + l4) (u3 + u4) k19 m19 p19 r19 hm19 hok19
    (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  push_cast at hb19
  obtain ⟨D20, hDl20, hb20⟩ := mterm_ok hlb hD hpt hR (l3 + l4 + l5) (u3 + u4 + u5) k20 m20 p20 r20 hm20 hok20
    (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  push_cast at hb20
  obtain ⟨D21, hDl21, hb21⟩ := mterm_ok hlb hD hpt hR (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) k21 m21 p21 r21 hm21 hok21
    (g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add h31 h41) h51) h61) (shi_add (shi_add (shi_add h32 h42) h52) h62)
  push_cast at hb21
  obtain ⟨D22, hDl22, hb22⟩ := mterm_ok hlb hD hpt hR (l4) (u4) k22 m22 p22 r22 hm22 hok22
    (g4) h41 h42
  push_cast at hb22
  obtain ⟨D23, hDl23, hb23⟩ := mterm_ok hlb hD hpt hR (l4 + l5) (u4 + u5) k23 m23 p23 r23 hm23 hok23
    (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  push_cast at hb23
  obtain ⟨D25, hDl25, hb25⟩ := mterm_ok hlb hD hpt hR (l5) (u5) k25 m25 p25 r25 hm25 hok25
    (g5) h51 h52
  push_cast at hb25
  obtain ⟨D26, hDl26, hb26⟩ := mterm_ok hlb hD hpt hR (l5 + l6) (u5 + u6) k26 m26 p26 r26 hm26 hok26
    (g5 + g6) (slo_add h51 h61) (shi_add h52 h62)
  push_cast at hb26
  obtain ⟨D27, hDl27, hb27⟩ := mterm_ok hlb hD hpt hR (l6) (u6) k27 m27 p27 r27 hm27 hok27
    (g6) h61 h62
  push_cast at hb27
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  have hN0 : -((((2000000000 * (16529847 * (mw1 k0 m0 + mw2 k0 m0) + 9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6))) - (33744896000000000 + 16529847 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 32954 : ℝ) + 16529847 * D0 + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6) := by
    have := natsub_ge (2000000000 * (16529847 * (mw1 k0 m0 + mw2 k0 m0) + 9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6))) (33744896000000000 + 16529847 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6)
    push_cast at this ⊢
    linear_combination this + 16529847 * hDl0 + 9711365 * hDl1 + 99842625 * hDl3 + 65570678 * hDl4 + 100000000 * hDl5 + 200000000 * hDl6
  have hlu0' : ((u0 - l0 : ℕ) : ℝ) = (u0 : ℝ) - l0 := Nat.cast_sub hlu0
  have hg0 := gap_lo (E := ((1024 * 32954 : ℝ) + 16529847 * D0 + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6)) (e := g0 - (l0 : ℝ) / 32768) (H := ((u0 - l0 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN0 (sub_nonneg.mpr h01) (by rw [hlu0', sub_div]; exact sub_le_sub_right h02 _)
  have hN1 : -((((2000000000 * (9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 27454871 * (mw1 k7 m7 + mw2 k7 m7) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12))) - (59370496000000000 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 27454871 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 57979 : ℝ) + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 27454871 * D7 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12) := by
    have := natsub_ge (2000000000 * (9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 27454871 * (mw1 k7 m7 + mw2 k7 m7) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12))) (59370496000000000 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 27454871 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12)
    push_cast at this ⊢
    linear_combination this + 9711365 * hDl1 + 99842625 * hDl3 + 65570678 * hDl4 + 100000000 * hDl5 + 200000000 * hDl6 + 27454871 * hDl7 + 44643360 * hDl8 + 67808981 * hDl9 + 157375 * hDl10 + 68858644 * hDl11 + 100000000 * hDl12
  have hlu1' : ((u1 - l1 : ℕ) : ℝ) = (u1 : ℝ) - l1 := Nat.cast_sub hlu1
  have hg1 := gap_lo (E := ((1024 * 57979 : ℝ) + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 27454871 * D7 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12)) (e := g1 - (l1 : ℝ) / 32768) (H := ((u1 - l1 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN1 (sub_nonneg.mpr h11) (by rw [hlu1', sub_div]; exact sub_le_sub_right h12 _)
  have hN2 : -((((2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 34948217 * (mw1 k13 m13 + mw2 k13 m13) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17))) - (70403072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 34948217 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 68753 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 34948217 * D13 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17) := by
    have := natsub_ge (2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 34948217 * (mw1 k13 m13 + mw2 k13 m13) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17))) (70403072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 34948217 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)
    push_cast at this ⊢
    linear_combination this + 99842625 * hDl3 + 65570678 * hDl4 + 100000000 * hDl5 + 200000000 * hDl6 + 44643360 * hDl8 + 67808981 * hDl9 + 157375 * hDl10 + 68858644 * hDl11 + 100000000 * hDl12 + 34948217 * hDl13 + 45645275 * hDl14 + 64382038 * hDl15 + 157375 * hDl16 + 65570678 * hDl17
  have hlu2' : ((u2 - l2 : ℕ) : ℝ) = (u2 : ℝ) - l2 := Nat.cast_sub hlu2
  have hg2 := gap_lo (E := ((1024 * 68753 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 34948217 * D13 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17)) (e := g2 - (l2 : ℝ) / 32768) (H := ((u2 - l2 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN2 (sub_nonneg.mpr h21) (by rw [hlu2', sub_div]; exact sub_le_sub_right h22 _)
  have hN3 : -((((2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 42134130 * (mw1 k18 m18 + mw2 k18 m18) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21))) - (82563072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 42134130 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 80628 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 42134130 * D18 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21) := by
    have := natsub_ge (2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 42134130 * (mw1 k18 m18 + mw2 k18 m18) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21))) (82563072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 42134130 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21)
    push_cast at this ⊢
    linear_combination this + 99842625 * hDl3 + 65570678 * hDl4 + 100000000 * hDl5 + 200000000 * hDl6 + 67808981 * hDl9 + 157375 * hDl10 + 68858644 * hDl11 + 100000000 * hDl12 + 45645275 * hDl14 + 64382038 * hDl15 + 157375 * hDl16 + 65570678 * hDl17 + 42134130 * hDl18 + 45645275 * hDl19 + 67808981 * hDl20 + 99842625 * hDl21
  have hlu3' : ((u3 - l3 : ℕ) : ℝ) = (u3 : ℝ) - l3 := Nat.cast_sub hlu3
  have hg3 := gap_lo (E := ((1024 * 80628 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 42134130 * D18 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21)) (e := g3 - (l3 : ℝ) / 32768) (H := ((u3 - l3 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN3 (sub_nonneg.mpr h31) (by rw [hlu3', sub_div]; exact sub_le_sub_right h32 _)
  have hN4 : -((((2000000000 * (65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 34948217 * (mw1 k22 m22 + mw2 k22 m22) + 44643360 * (mw1 k23 m23 + mw2 k23 m23))) - (70403072000000000 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 34948217 * msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 68753 : ℝ) + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21 + 34948217 * D22 + 44643360 * D23) := by
    have := natsub_ge (2000000000 * (65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 34948217 * (mw1 k22 m22 + mw2 k22 m22) + 44643360 * (mw1 k23 m23 + mw2 k23 m23))) (70403072000000000 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 34948217 * msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23)
    push_cast at this ⊢
    linear_combination this + 65570678 * hDl4 + 100000000 * hDl5 + 200000000 * hDl6 + 157375 * hDl10 + 68858644 * hDl11 + 100000000 * hDl12 + 64382038 * hDl15 + 157375 * hDl16 + 65570678 * hDl17 + 45645275 * hDl19 + 67808981 * hDl20 + 99842625 * hDl21 + 34948217 * hDl22 + 44643360 * hDl23
  have hlu4' : ((u4 - l4 : ℕ) : ℝ) = (u4 : ℝ) - l4 := Nat.cast_sub hlu4
  have hg4 := gap_lo (E := ((1024 * 68753 : ℝ) + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21 + 34948217 * D22 + 44643360 * D23)) (e := g4 - (l4 : ℝ) / 32768) (H := ((u4 - l4 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN4 (sub_nonneg.mpr h41) (by rw [hlu4', sub_div]; exact sub_le_sub_right h42 _)
  have hN5 : -((((2000000000 * (100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 44643360 * (mw1 k23 m23 + mw2 k23 m23) + 27454871 * (mw1 k25 m25 + mw2 k25 m25) + 9711365 * (mw1 k26 m26 + mw2 k26 m26))) - (59370496000000000 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23 + 27454871 * msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 57979 : ℝ) + 100000000 * D5 + 200000000 * D6 + 68858644 * D11 + 100000000 * D12 + 157375 * D16 + 65570678 * D17 + 67808981 * D20 + 99842625 * D21 + 44643360 * D23 + 27454871 * D25 + 9711365 * D26) := by
    have := natsub_ge (2000000000 * (100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 44643360 * (mw1 k23 m23 + mw2 k23 m23) + 27454871 * (mw1 k25 m25 + mw2 k25 m25) + 9711365 * (mw1 k26 m26 + mw2 k26 m26))) (59370496000000000 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23 + 27454871 * msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26)
    push_cast at this ⊢
    linear_combination this + 100000000 * hDl5 + 200000000 * hDl6 + 68858644 * hDl11 + 100000000 * hDl12 + 157375 * hDl16 + 65570678 * hDl17 + 67808981 * hDl20 + 99842625 * hDl21 + 44643360 * hDl23 + 27454871 * hDl25 + 9711365 * hDl26
  have hlu5' : ((u5 - l5 : ℕ) : ℝ) = (u5 : ℝ) - l5 := Nat.cast_sub hlu5
  have hg5 := gap_lo (E := ((1024 * 57979 : ℝ) + 100000000 * D5 + 200000000 * D6 + 68858644 * D11 + 100000000 * D12 + 157375 * D16 + 65570678 * D17 + 67808981 * D20 + 99842625 * D21 + 44643360 * D23 + 27454871 * D25 + 9711365 * D26)) (e := g5 - (l5 : ℝ) / 32768) (H := ((u5 - l5 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN5 (sub_nonneg.mpr h51) (by rw [hlu5', sub_div]; exact sub_le_sub_right h52 _)
  have hN6 : -((((2000000000 * (200000000 * (mw1 k6 m6 + mw2 k6 m6) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 9711365 * (mw1 k26 m26 + mw2 k26 m26) + 16529847 * (mw1 k27 m27 + mw2 k27 m27))) - (33744896000000000 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26 + 16529847 * msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 32954 : ℝ) + 200000000 * D6 + 100000000 * D12 + 65570678 * D17 + 99842625 * D21 + 9711365 * D26 + 16529847 * D27) := by
    have := natsub_ge (2000000000 * (200000000 * (mw1 k6 m6 + mw2 k6 m6) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 9711365 * (mw1 k26 m26 + mw2 k26 m26) + 16529847 * (mw1 k27 m27 + mw2 k27 m27))) (33744896000000000 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26 + 16529847 * msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27)
    push_cast at this ⊢
    linear_combination this + 200000000 * hDl6 + 100000000 * hDl12 + 65570678 * hDl17 + 99842625 * hDl21 + 9711365 * hDl26 + 16529847 * hDl27
  have hlu6' : ((u6 - l6 : ℕ) : ℝ) = (u6 : ℝ) - l6 := Nat.cast_sub hlu6
  have hg6 := gap_lo (E := ((1024 * 32954 : ℝ) + 200000000 * D6 + 100000000 * D12 + 65570678 * D17 + 99842625 * D21 + 9711365 * D26 + 16529847 * D27)) (e := g6 - (l6 : ℝ) / 32768) (H := ((u6 - l6 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN6 (sub_nonneg.mpr h61) (by rw [hlu6', sub_div]; exact sub_le_sub_right h62 _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  simp only [hlu0', hlu1', hlu2', hlu3', hlu4', hlu5', hlu6'] at hq hg0 hg1 hg2 hg3 hg4 hg5 hg6
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
      + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)) * SA
      = 32954 * g0 + 57979 * g1 + 68753 * g2 + 80628 * g3 + 68753 * g4 + 57979 * g5 + 32954 * g6 + 16529847 * wfun (g0) + 9711365 * wfun (g0 + g1) + 99842625 * wfun (g0 + g1 + g2 + g3) + 65570678 * wfun (g0 + g1 + g2 + g3 + g4) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + 27454871 * wfun (g1) + 44643360 * wfun (g1 + g2) + 67808981 * wfun (g1 + g2 + g3) + 157375 * wfun (g1 + g2 + g3 + g4) + 68858644 * wfun (g1 + g2 + g3 + g4 + g5) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5 + g6) + 34948217 * wfun (g2) + 45645275 * wfun (g2 + g3) + 64382038 * wfun (g2 + g3 + g4) + 157375 * wfun (g2 + g3 + g4 + g5) + 65570678 * wfun (g2 + g3 + g4 + g5 + g6) + 42134130 * wfun (g3) + 45645275 * wfun (g3 + g4) + 67808981 * wfun (g3 + g4 + g5) + 99842625 * wfun (g3 + g4 + g5 + g6) + 34948217 * wfun (g4) + 44643360 * wfun (g4 + g5) + 27454871 * wfun (g5) + 9711365 * wfun (g5 + g6) + 16529847 * wfun (g6) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 701466 := by norm_num [cN]
  rw [hcN]
  linarith [hq, hg0, hg1, hg2, hg3, hg4, hg5, hg6, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 16529847), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 68858644), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 64382038), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 42134130), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb21 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb22 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb23 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb25 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb26 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb27 (by norm_num : (0:ℝ) ≤ 16529847)]

theorem mleafN_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ)
    (h : mleafN top bk tD bD pb R w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  unfold mleafN at h
  simp only [forceR_eq] at h
  exact mscheck_sound (f := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h)

/-- a box split on gap 0 at `q` is covered when both halves are -/
theorem covered_split0 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g0 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 hq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 hq h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 1 at `q` is covered when both halves are -/
theorem covered_split1 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g1 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 hq h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 hq h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 2 at `q` is covered when both halves are -/
theorem covered_split2 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g2 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 hq h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 hq h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 3 at `q` is covered when both halves are -/
theorem covered_split3 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g3 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 hq h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 hq h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 4 at `q` is covered when both halves are -/
theorem covered_split4 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g4 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 hq h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 hq h42 h51 h52 h61 h62

/-- a box split on gap 5 at `q` is covered when both halves are -/
theorem covered_split5 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g5 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 hq h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 hq h52 h61 h62

/-- a box split on gap 6 at `q` is covered when both halves are -/
theorem covered_split6 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 q) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g6 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 hq
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 hq h62

/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ, f pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 → Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6

theorem split0_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split0 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split0 _ hA (hih _ (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split1_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split1 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split1 _ hA (hih _ l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split2_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split2 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6) l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split2 _ hA (hih _ l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split3_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split3 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6) l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split3 _ hA (hih _ l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split4_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split4 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6) l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split4 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split5_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split5 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split5 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split6_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split6 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split6 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1)) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1)) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (Nat.shiftRight (Nat.add l6 u6) 1) u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1) (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split6 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (Nat.shiftRight (Nat.add l6 u6) 1) u6 h')
  · exact absurd (by simp only [hp]) h

theorem splitAx_sound {ih : WF} (hih : WalkOK ih) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : splitAx ih pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold splitAx at h
  cases ha0 : Nat.beq ax 0
  · rw [ha0] at h
    cases ha1 : Nat.beq ax 1
    · rw [ha1] at h
      cases ha2 : Nat.beq ax 2
      · rw [ha2] at h
        cases ha3 : Nat.beq ax 3
        · rw [ha3] at h
          cases ha4 : Nat.beq ax 4
          · rw [ha4] at h
            cases ha5 : Nat.beq ax 5
            · rw [ha5] at h
              exact split6_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
            · rw [ha5] at h; exact split5_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
          · rw [ha4] at h; exact split4_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
        · rw [ha3] at h; exact split3_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
      · rw [ha2] at h; exact split2_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
    · rw [ha1] at h; exact split1_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
  · rw [ha0] at h; exact split0_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ)
    (h : leafStep top bk tD bD pb R pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold leafStep at h
  cases hs : Nat.ble (Nat.add u6 1) l0
  · rw [hs] at h
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
      · rw [hl] at h; exact absurd rfl h
      · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
        exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 hl g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
    · rw [hk, forceR_eq] at h
      intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
      refine Or.inl (mleafN_sound hlb hD hpt hR (Nat.shiftRight w 2) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ?_ g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
      intro h0; rw [h0] at h; exact h rfl
  · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
    right
    have hsk : u6 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u6 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)
        (splitAx (walk top bk tD bD pb R bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 e : ℕ)
    (h : walk top bk tD bD pb R bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 :=
  walk_sound hlb hD hpt hR bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (h ▸ he)


/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear segment's own integer
cell bound must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WZ ≥ cN * SW` -/
def coverCheck (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b) && decide (b < KB)
        && (!cl || Nat.ble (cN * SW) (aAdjN * CellN.WZ ⟨a * KB + b, 0⟩))
        && coverCheck aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

theorem cover_sound (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        rw [Nat.ble_eq] at hcl
        have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
          simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
        have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
          simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
        have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSA : (0:ℝ) < SA := by norm_num [SA]
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        rw [div_le_iff₀ hSA]
        have hm2 : (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
        rw [e]
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdjN : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (cover0 cover1 cover2 cover3 cover4 cover5 cover6 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 S5 S6 : ℕ)
    (hS0 : cN * SC ≤ 32954 * S0) (hS1 : cN * SC ≤ 57979 * S1) (hS2 : cN * SC ≤ 68753 * S2) (hS3 : cN * SC ≤ 80628 * S3) (hS4 : cN * SC ≤ 68753 * S4) (hS5 : cN * SC ≤ 57979 * S5) (hS6 : cN * SC ≤ 32954 * S6)
    (hcov0 : coverCheck 16529847 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 27454871 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 34948217 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 42134130 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 34948217 (SC / 2) S4 cover4 = true) (hcov5 : coverCheck 27454871 (SC / 2) S5 cover5 = true) (hcov6 : coverCheck 16529847 (SC / 2) S6 cover6 = true)
    (hwin : cN * 100 ≤ 19 * 16529847)
    (hrun : ∀ i0 i1 i2 i3 i4 i5 i6, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length → i5 < (badOf cover5).length → i6 < (badOf cover6).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2 ((badOf cover5).getD i5 (0, 0)).1 ((badOf cover5).getD i5 (0, 0)).2 ((badOf cover6).getD i6 (0, 0)).1 ((badOf cover6).getD i6 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → 0 ≤ g5 → 0 ≤ g6 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 ∨ g6 < g0 := by
  intro g0 g1 g2 g3 g4 g5 g6 hg0 hg1 hg2 hg3 hg4 hg5 hg6
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6 with hLin
  set Wt : ℝ := (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6) with hWt
  have hG : G g0 g1 g2 g3 g4 g5 g6 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (32954 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (57979 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (68753 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (80628 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (68753 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have hb50 : (0:ℝ) ≤ (57979 / (SA:ℝ)) * g5 := mul_nonneg (by positivity) hg5
  have hb60 : (0:ℝ) ≤ (32954 / (SA:ℝ)) * g6 := mul_nonneg (by positivity) hg6
  have ha00 : (0:ℝ) ≤ (16529847 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (9711365 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (27454871 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (44643360 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (34948217 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (45645275 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha150 : (0:ℝ) ≤ (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha160 : (0:ℝ) ≤ (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha170 : (0:ℝ) ≤ (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha180 : (0:ℝ) ≤ (42134130 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha190 : (0:ℝ) ≤ (45645275 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha200 : (0:ℝ) ≤ (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha210 : (0:ℝ) ≤ (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha220 : (0:ℝ) ≤ (34948217 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have ha230 : (0:ℝ) ≤ (44643360 / (SA:ℝ)) * wfun (g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha240 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha250 : (0:ℝ) ≤ (27454871 / (SA:ℝ)) * wfun (g5) := mul_nonneg (by positivity) (hw _)
  have ha260 : (0:ℝ) ≤ (9711365 / (SA:ℝ)) * wfun (g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha270 : (0:ℝ) ≤ (16529847 / (SA:ℝ)) * wfun (g6) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30) hb40) hb50) hb60)
  have hWt0 : 0 ≤ Wt := by rw [hWt]; exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190) ha200) ha210) ha220) ha230) ha240) ha250) ha260) ha270)
  have hbL0 : (32954 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans le_rfl (le_add_of_nonneg_right hb10)) (le_add_of_nonneg_right hb20)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50)) (le_add_of_nonneg_right hb60))
  have hbL1 : (57979 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left hb00) (le_add_of_nonneg_right hb20)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50)) (le_add_of_nonneg_right hb60))
  have hbL2 : (68753 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg hb00 hb10)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50)) (le_add_of_nonneg_right hb60))
  have hbL3 : (80628 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg hb00 hb10) hb20)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50)) (le_add_of_nonneg_right hb60))
  have hbL4 : (68753 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30)) (le_add_of_nonneg_right hb50)) (le_add_of_nonneg_right hb60))
  have hbL5 : (57979 / (SA:ℝ)) * g5 ≤ Lin := by rw [hLin]; exact (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30) hb40)) (le_add_of_nonneg_right hb60))
  have hbL6 : (32954 / (SA:ℝ)) * g6 ≤ Lin := by rw [hLin]; exact (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30) hb40) hb50))
  have haW0 : (16529847 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans le_rfl (le_add_of_nonneg_right ha10)) (le_add_of_nonneg_right ha20)) (le_add_of_nonneg_right ha30)) (le_add_of_nonneg_right ha40)) (le_add_of_nonneg_right ha50)) (le_add_of_nonneg_right ha60)) (le_add_of_nonneg_right ha70)) (le_add_of_nonneg_right ha80)) (le_add_of_nonneg_right ha90)) (le_add_of_nonneg_right ha100)) (le_add_of_nonneg_right ha110)) (le_add_of_nonneg_right ha120)) (le_add_of_nonneg_right ha130)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200)) (le_add_of_nonneg_right ha210)) (le_add_of_nonneg_right ha220)) (le_add_of_nonneg_right ha230)) (le_add_of_nonneg_right ha240)) (le_add_of_nonneg_right ha250)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW7 : (27454871 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60)) (le_add_of_nonneg_right ha80)) (le_add_of_nonneg_right ha90)) (le_add_of_nonneg_right ha100)) (le_add_of_nonneg_right ha110)) (le_add_of_nonneg_right ha120)) (le_add_of_nonneg_right ha130)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200)) (le_add_of_nonneg_right ha210)) (le_add_of_nonneg_right ha220)) (le_add_of_nonneg_right ha230)) (le_add_of_nonneg_right ha240)) (le_add_of_nonneg_right ha250)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW13 : (34948217 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200)) (le_add_of_nonneg_right ha210)) (le_add_of_nonneg_right ha220)) (le_add_of_nonneg_right ha230)) (le_add_of_nonneg_right ha240)) (le_add_of_nonneg_right ha250)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW18 : (42134130 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200)) (le_add_of_nonneg_right ha210)) (le_add_of_nonneg_right ha220)) (le_add_of_nonneg_right ha230)) (le_add_of_nonneg_right ha240)) (le_add_of_nonneg_right ha250)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW22 : (34948217 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190) ha200) ha210)) (le_add_of_nonneg_right ha230)) (le_add_of_nonneg_right ha240)) (le_add_of_nonneg_right ha250)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW25 : (27454871 / (SA:ℝ)) * wfun (g5) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190) ha200) ha210) ha220) ha230) ha240)) (le_add_of_nonneg_right ha260)) (le_add_of_nonneg_right ha270))
  have haW27 : (16529847 / (SA:ℝ)) * wfun (g6) ≤ Wt := by rw [hWt]; exact (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190) ha200) ha210) ha220) ha230) ha240) ha250) ha260))
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (32954 / (SA:ℝ)) * g0 := by
      rw [div_le_iff₀ hSA]
      have e : (32954 / (SA:ℝ)) * g0 * SA = 32954 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 32954 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS0
        _ = 32954 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 32954 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL0 (le_add_of_nonneg_right hWt0))
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (16529847 / (SA:ℝ)) * wfun g0 * SA = 16529847 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 16529847)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW0 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · have hc0 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun (g0) := by exact_mod_cast hclear0
    left; rw [hG]; exact le_trans hc0 (le_trans haW0 (le_add_of_nonneg_left hLin0))
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (57979 / (SA:ℝ)) * g1 := by
      rw [div_le_iff₀ hSA]
      have e : (57979 / (SA:ℝ)) * g1 * SA = 57979 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 57979 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS1
        _ = 57979 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 57979 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL1 (le_add_of_nonneg_right hWt0))
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (27454871 / (SA:ℝ)) * wfun g1 * SA = 27454871 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 27454871)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW7 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · have hc1 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun (g1) := by exact_mod_cast hclear1
    left; rw [hG]; exact le_trans hc1 (le_trans haW7 (le_add_of_nonneg_left hLin0))
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (68753 / (SA:ℝ)) * g2 := by
      rw [div_le_iff₀ hSA]
      have e : (68753 / (SA:ℝ)) * g2 * SA = 68753 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 68753 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS2
        _ = 68753 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 68753 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL2 (le_add_of_nonneg_right hWt0))
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (34948217 / (SA:ℝ)) * wfun g2 * SA = 34948217 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 34948217)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW13 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · have hc2 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun (g2) := by exact_mod_cast hclear2
    left; rw [hG]; exact le_trans hc2 (le_trans haW13 (le_add_of_nonneg_left hLin0))
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (80628 / (SA:ℝ)) * g3 := by
      rw [div_le_iff₀ hSA]
      have e : (80628 / (SA:ℝ)) * g3 * SA = 80628 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 80628 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS3
        _ = 80628 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 80628 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL3 (le_add_of_nonneg_right hWt0))
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (42134130 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (42134130 / (SA:ℝ)) * wfun g3 * SA = 42134130 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 42134130)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW18 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · have hc3 : (cN : ℝ) / SA ≤ (42134130 / (SA:ℝ)) * wfun (g3) := by exact_mod_cast hclear3
    left; rw [hG]; exact le_trans hc3 (le_trans haW18 (le_add_of_nonneg_left hLin0))
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (68753 / (SA:ℝ)) * g4 := by
      rw [div_le_iff₀ hSA]
      have e : (68753 / (SA:ℝ)) * g4 * SA = 68753 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 68753 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS4
        _ = 68753 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 68753 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL4 (le_add_of_nonneg_right hWt0))
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (34948217 / (SA:ℝ)) * wfun g4 * SA = 34948217 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 34948217)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW22 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · have hc4 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun (g4) := by exact_mod_cast hclear4
    left; rw [hG]; exact le_trans hc4 (le_trans haW22 (le_add_of_nonneg_left hLin0))
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  -- gap 5: beyond the cutoff the pressure alone pays
  by_cases hcut5 : (S5 : ℝ) / SC ≤ g5
  · have h1 : (cN : ℝ) / SA ≤ (57979 / (SA:ℝ)) * g5 := by
      rw [div_le_iff₀ hSA]
      have e : (57979 / (SA:ℝ)) * g5 * SA = 57979 * g5 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 57979 * S5 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS5
        _ = 57979 * ((S5 : ℝ) / SC) := by ring
        _ ≤ 57979 * g5 := mul_le_mul_of_nonneg_left hcut5 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL5 (le_add_of_nonneg_right hWt0))
  push_neg at hcut5
  rcases le_total g5 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin5 | hwin5
  · have hw19 := wfun_window g5 hg5 (by rw [hhalf] at hwin5; exact hwin5)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun g5 := by
      rw [div_le_iff₀ hSA]
      have e : (27454871 / (SA:ℝ)) * wfun g5 * SA = 27454871 * wfun g5 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 27454871)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW25 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover5 (SC / 2) S5 hcov5 g5 hwin5 hcut5 with hclear5 | ⟨s5, hs5, he5, hb51, hb52⟩
  · have hc5 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun (g5) := by exact_mod_cast hclear5
    left; rw [hG]; exact le_trans hc5 (le_trans haW25 (le_add_of_nonneg_left hLin0))
  obtain ⟨i5, hi5, hsi5⟩ := List.mem_iff_getElem.mp (badOf_mem hs5 he5)
  have hb51' : (((badOf cover5).getD i5 (0, 0)).1 : ℝ) / SC ≤ g5 := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb51
  have hb52' : g5 ≤ (((badOf cover5).getD i5 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb52
  -- gap 6: beyond the cutoff the pressure alone pays
  by_cases hcut6 : (S6 : ℝ) / SC ≤ g6
  · have h1 : (cN : ℝ) / SA ≤ (32954 / (SA:ℝ)) * g6 := by
      rw [div_le_iff₀ hSA]
      have e : (32954 / (SA:ℝ)) * g6 * SA = 32954 * g6 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 32954 * S6 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS6
        _ = 32954 * ((S6 : ℝ) / SC) := by ring
        _ ≤ 32954 * g6 := mul_le_mul_of_nonneg_left hcut6 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL6 (le_add_of_nonneg_right hWt0))
  push_neg at hcut6
  rcases le_total g6 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin6 | hwin6
  · have hw19 := wfun_window g6 hg6 (by rw [hhalf] at hwin6; exact hwin6)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun g6 := by
      rw [div_le_iff₀ hSA]
      have e : (16529847 / (SA:ℝ)) * wfun g6 * SA = 16529847 * wfun g6 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 16529847)
      linear_combination (1 / 100 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW27 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover6 (SC / 2) S6 hcov6 g6 hwin6 hcut6 with hclear6 | ⟨s6, hs6, he6, hb61, hb62⟩
  · have hc6 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun (g6) := by exact_mod_cast hclear6
    left; rw [hG]; exact le_trans hc6 (le_trans haW27 (le_add_of_nonneg_left hLin0))
  obtain ⟨i6, hi6, hsi6⟩ := List.mem_iff_getElem.mp (badOf_mem hs6 he6)
  have hb61' : (((badOf cover6).getD i6 (0, 0)).1 : ℝ) / SC ≤ g6 := by
    rw [List.getD_eq_getElem _ _ hi6, hsi6]; exact hb61
  have hb62' : g6 ≤ (((badOf cover6).getD i6 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi6, hsi6]; exact hb62
  exact hrun i0 i1 i2 i3 i4 i5 i6 hi0 hi1 hi2 hi3 hi4 hi5 hi6 g0 g1 g2 g3 g4 g5 g6 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42' hb51' hb52' hb61' hb62'

end Zeta23Ext.Bridge.ThreePoint.OctY30

end
