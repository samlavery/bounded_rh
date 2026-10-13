import MvtCore

-- SLOPE-BEGIN
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
-- SLOPEDEFS-END

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
-- SLOPE-END
