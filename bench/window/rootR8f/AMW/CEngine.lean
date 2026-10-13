import AMW.CFacade

/-! ###### AM seven-point engine cores (stage G)

The pyramid oracle, the derivative pair pyramid, the point table, the slope test and the convex regions of the
seven-point engine (mvt-engine; pyramid adapted from five-point-pyramid-2 by typh, convex basins after
six-point-convex-basins-2 by typh, Apache-2.0), with the cell evaluator of the AM kernel behind `AMW/CFacade`. -/

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

namespace AMW.Cert.Pyr

open AMW.Cert

/-- `a && b` and `a || b` as one `Bool.rec` (the kernel's `&&` goes through a matcher) -/
scoped notation:35 a:35 " &&ₖ " b:36 => Bool.rec (motive := fun _ => Bool) false b a
scoped notation:30 a:30 " ||ₖ " b:31 => Bool.rec (motive := fun _ => Bool) b true a

/-- evaluate a natural number to a numeral before continuing (the kernel is call-by-name) -/
def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a

/-- field `i` (32 bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295

/-- the entry for the level-`l` cell `i` (`l ≤ 10`) from the constant `X` of its block `j`: the entry of its
ancestor at level `max l r`, `r` the block's finest stored level -/
def entB (X l i j : ℕ) : ℕ :=
  let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
  let d := Nat.sub 10 kk
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for the level-`l` cell `i` -/
def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
    (Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
    (Nat.ble 11 l)

def nmin (a b : ℕ) : ℕ := Nat.sub a (Nat.sub a b)

/-- one block of a cover of the level-`k` cells `g .. E - 1`: the largest block of `2^t ≤ 16` cells aligned at `g`
that fits (`t` from a 3-bit table on `g mod 16` and `min (E − g) 16`; any value is sound), read through its entry
(level and index packed into one numeral, so that equal reads share the kernel's cache), then `ih` from the block's
end while cells remain -/
def dstep (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
  let d := Nat.sub E g
  let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
  let h := Nat.shiftRight g t
  let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
  Bool.rec (motive := fun _ => ℕ) (nmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))

/-- min of the entries over the cover of the level-`k` cells `g .. ib` by `dstep` blocks (at most 14, else `0`) -/
def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
  let E := Nat.add ib 1
  dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (fun _ => 0))))))))))))))

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
       dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) (Nat.shiftRight lo k))
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

theorem brecAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by cases a <;> rfl

theorem brecOr (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = (a || b) := by cases a <;> rfl

theorem forceR_eq (a : ℕ) (k : ℕ → ℕ) : forceR a k = k a := by cases a <;> rfl

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  simp only [Nat.sub_eq]
  rcases le_total a b with h | h
  · rw [min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_zero]
  · rw [min_eq_right h, Nat.sub_sub_self h]

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
    have hkk : Nat.add l (Nat.sub r l) = max l r := by
      simp only [Nat.add_eq, Nat.sub_eq, max_def]; split_ifs <;> omega
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

/-- a function bounding `wfun` on the level-`k` cells `g .. E - 1` from any `g < E` -/
def DSound (k E : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ g, g < E → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC →
    (f g : ℝ) / 10000000000 ≤ wfun x

theorem DSound_zero (k E : ℕ) : DSound k E (fun _ => 0) := by
  intro g _ x _ _
  simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x

theorem entry_ge20 (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (i : ℕ) (hl : 20 ≤ l) : entry top bk l i = 0 := by
  have h11 : Nat.ble 11 l = true := by rw [Nat.ble_eq]; omega
  have h20 : Nat.ble 20 l = true := by rw [Nat.ble_eq]; omega
  unfold entry
  rw [h11, h20]

theorem pack_hi (l h : ℕ) (hh : h < 2 ^ 40) : Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40 = l := by
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hh, Nat.zero_add]

theorem pack_lo (l h : ℕ) (hh : h < 2 ^ 40) : Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775 = h := by
  rw [Nat.land_eq, show (1099511627775 : ℕ) = 2 ^ 40 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]

theorem pack_ge (l h : ℕ) : l ≤ Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40 := by
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity)]
  omega

/-- the packed read of the level-`l` cell `h` -/
theorem entry_pack_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (l h : ℕ) (hi : l ≤ 19 → h < 2 ^ (19 - l)) :
    CS l h (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40) (Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775)) := by
  by_cases hl : l ≤ 19
  · have hh : h < 2 ^ 40 := lt_of_lt_of_le (hi hl) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [pack_hi l h hh, pack_lo l h hh]
    exact entry_sound hb ht l h hi
  · rw [entry_ge20 top bk _ (le_trans (by omega) (pack_ge l h))]
    exact CS_zero l h

/-- one step of the cover, for any block size `t` -/
theorem dcore_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound k E ih)
    (g : ℕ) (hg : g < E) (x : ℝ) (h1 : ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x) (h2 : x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC) (t : ℕ) :
    ((Bool.rec (motive := fun _ => ℕ)
      (nmin (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
        (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
        (ih (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)))
      (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
        (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
      (Nat.ble E (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)) : ℕ) : ℝ) / 10000000000 ≤ wfun x := by
  set h := Nat.shiftRight g t with hh
  have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  set v := entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 40)
    (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 1099511627775) with hv
  set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
  have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  have hcell : CS (Nat.add k t) h v := by
    rw [hv]
    apply entry_pack_sound hb ht
    intro hkt
    have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
    have hgib : g * 2 ^ k < 2 ^ 19 := by
      have := hk hk'
      calc g * 2 ^ k < E * 2 ^ k := Nat.mul_lt_mul_of_pos_right hg (by positivity)
        _ ≤ 2 ^ 19 := this
    rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
    have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
      rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
    by_contra hcon
    push_neg at hcon
    have := Nat.mul_le_mul_right (2 ^ k) hcon
    rw [e] at this; omega
  have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
      (v : ℝ) / 10000000000 ≤ wfun y := by
    intro y hy1 hy2
    apply hcell y
    · refine le_trans (castdiv_le ?_) hy1
      rw [hh', Nat.add_eq, pow_add]
      calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
        _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
    · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
      rw [hg'', Nat.add_eq, pow_add]; ring
  cases hc : Nat.ble E g'
  · have hle : g' < E := by
      have : ¬ E ≤ g' := by rw [← Nat.ble_eq, hc]; decide
      omega
    show ((nmin _ _ : ℕ) : ℝ) / 10000000000 ≤ wfun x
    rw [nmin_eq]
    rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
    · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (by norm_num)) (hcellx x h1 hx)
    · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by norm_num)) (hih g' hle x hx h2)
  · have hgt : E ≤ g' := by rw [← Nat.ble_eq, hc]
    exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))

theorem dstep_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound k E ih) :
    DSound k E (dstep top bk k E ih) := by
  intro g hg x h1 h2
  unfold dstep
  simp only [forceR_eq]
  exact dcore_sound hb ht k E hk hih g hg x h1 h2 _

/-- the cover of the level-`k` cells `g .. ib` reads only cells that hold sound entries -/
theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      (dcov top bk k ib g : ℝ) / 10000000000 ≤ wfun x := by
  intro g hg x h1 h2
  have hs : ∀ {f : ℕ → ℕ}, DSound k (Nat.add ib 1) f → DSound k (Nat.add ib 1) (dstep top bk k (Nat.add ib 1) f) :=
    fun hf => dstep_sound hb ht k (Nat.add ib 1) hk hf
  exact hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (DSound_zero k _)))))))))))))) g (by simp only [Nat.add_eq]; omega) x h1 h2

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
      show ((dcov top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5)))
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

end AMW.Cert.Pyr

end

/-! ###### mean-value leaf test: integer enclosures of `w'`, derivative pyramids and a point table ######

`w = N² / D²` with `b = π x`, `N = cos b − 2γ b sin b`, `D = 1 − 2 b²`; for `2 b² > 1` its derivative is
`w' = 2π N M / D³` with `M = N_b D + 4 b N` and `N_b = −(1 + 2γ) sin b − 2γ b cos b`.  The integer pipeline below
encloses `w'` on a cell at scale `DZ` (interval products rounded outward) and returns bounds in units `1/U1`.
Two pyramids (the cover arithmetic of `Pyr.lb`) store lower bounds of `w' + 2` and of `2 − w'`; their entries
claim nothing when `0`.  A point table stores lower bounds of `w` at grid points (degenerate cells `[x, x]`). -/



noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

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

end AMW.Cert.PyrD

end

/-! ###### the derivative tables as one pyramid of pairs ######

The two derivative tables share one block structure, so they are stored as one pyramid of 64-bit entries: the low
32 bits bound `w' + 2` below and the high 32 bits bound `2 − w'` below (units `1/U1`; a half `0` claims nothing).
The cover arithmetic is that of `Pyr.lb` with the cover level taken from `(hi − lo) >>> 4` (pyramid layout adapted
from five-point-pyramid-2 by typh, Apache-2.0); the entries read are combined by the componentwise minimum `pmin`, and the verification checks every coarser entry
componentwise against its children (`ple`). -/

section MvtPairDefs

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- field `i` (64 bits) of a packed natural -/
def fld2 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 64 i)) 18446744073709551615

/-- the two halves of a pair -/
def lo32 (v : ℕ) : ℕ := Nat.land v 4294967295
def hi32 (v : ℕ) : ℕ := Nat.shiftRight v 32

/-- the componentwise minimum of two pairs -/
def pmin (a b : ℕ) : ℕ :=
  Nat.add (Nat.sub (Nat.land a 4294967295) (Nat.sub (Nat.land a 4294967295) (Nat.land b 4294967295)))
    (Nat.shiftLeft (Nat.sub (Nat.shiftRight a 32) (Nat.sub (Nat.shiftRight a 32) (Nat.shiftRight b 32))) 32)

/-- the componentwise order of pairs -/
def ple (a b : ℕ) : Bool := Nat.ble (lo32 a) (lo32 b) && Nat.ble (hi32 a) (hi32 b)

def entB2 (X l i j : ℕ) : ℕ :=
  let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
  let d := Nat.sub 10 kk
  fld2 (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

def entry2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
    (Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
    (Nat.ble 11 l)

/-- one block of a cover of the level-`k` cells `g .. E - 1`: the largest block of `2^t ≤ 16` cells aligned at `g`
that fits (`t` from a 3-bit table on `g mod 16` and `min (E − g) 16`; any value is sound), read through its entry
(level and index packed into one numeral, so that equal reads share the kernel's cache), then `ih` from the block's
end while cells remain -/
def dstep2 (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
  let d := Nat.sub E g
  let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
  let h := Nat.shiftRight g t
  let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry2 top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
  Bool.rec (motive := fun _ => ℕ) (pmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))

def dcov2 (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
  let E := Nat.add ib 1
  dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (fun _ => 0))))))))))))))

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

end AMW.Cert.PyrD

end MvtPairDefs

/-! ### the derivative tables: what a verified table certifies -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

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

end AMW.Cert.PyrD

end

/-! ### the pyramid of pairs: what a verified table certifies -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

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

theorem pmin_def (a b : ℕ) :
    pmin a b = Nat.add (nmin (lo32 a) (lo32 b)) (Nat.shiftLeft (nmin (hi32 a) (hi32 b)) 32) := rfl

theorem pmin_lo (a b : ℕ) : lo32 (pmin a b) = min (lo32 a) (lo32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  rw [pmin_def, nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, lo32_eq (min _ _ + _),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha)]

theorem pmin_hi (a b : ℕ) : hi32 (pmin a b) = min (hi32 a) (hi32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  rw [pmin_def, nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hi32_eq (min _ _ + _),
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
    have hkk : Nat.add l (Nat.sub r l) = max l r := by
      simp only [Nat.add_eq, Nat.sub_eq, max_def]; split_ifs <;> omega
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

/-- a function bounding the pair tables on the level-`k` cells `g .. E - 1` from any `g < E` -/
def DSound2 (k E : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ g, g < E → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC → PS (f g) x

theorem DSound2_zero (k E : ℕ) : DSound2 k E (fun _ => 0) := fun _ _ x _ _ => PS_zero x

theorem entry2_ge20 (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (i : ℕ) (hl : 20 ≤ l) : entry2 top bk l i = 0 := by
  have h11 : Nat.ble 11 l = true := by rw [Nat.ble_eq]; omega
  have h20 : Nat.ble 20 l = true := by rw [Nat.ble_eq]; omega
  unfold entry2
  rw [h11, h20]

theorem entry2_pack_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (l h : ℕ) (hi : l ≤ 19 → h < 2 ^ (19 - l)) :
    CS2 l h (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40) (Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775)) := by
  by_cases hl : l ≤ 19
  · have hh : h < 2 ^ 40 := lt_of_lt_of_le (hi hl) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [pack_hi l h hh, pack_lo l h hh]
    exact entry2_sound hb ht l h hi
  · rw [entry2_ge20 top bk _ (le_trans (by omega) (pack_ge l h))]
    exact CS2_zero l h

theorem dcore2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound2 k E ih)
    (g : ℕ) (hg : g < E) (x : ℝ) (h1 : ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x) (h2 : x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC) (t : ℕ) :
    PS (Bool.rec (motive := fun _ => ℕ)
      (pmin (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
        (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
        (ih (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)))
      (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
        (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
      (Nat.ble E (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t))) x := by
  set h := Nat.shiftRight g t with hh
  have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  set v := entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 40)
    (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 1099511627775) with hv
  set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
  have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  have hcell : CS2 (Nat.add k t) h v := by
    rw [hv]
    apply entry2_pack_sound hb ht
    intro hkt
    have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
    have hgib : g * 2 ^ k < 2 ^ 19 := by
      have := hk hk'
      calc g * 2 ^ k < E * 2 ^ k := Nat.mul_lt_mul_of_pos_right hg (by positivity)
        _ ≤ 2 ^ 19 := this
    rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
    have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
      rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
    by_contra hcon
    push_neg at hcon
    have := Nat.mul_le_mul_right (2 ^ k) hcon
    rw [e] at this; omega
  have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC → PS v y := by
    intro y hy1 hy2
    apply hcell y
    · refine le_trans (castdiv_le ?_) hy1
      rw [hh', Nat.add_eq, pow_add]
      calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
        _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
    · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
      rw [hg'', Nat.add_eq, pow_add]; ring
  cases hc : Nat.ble E g'
  · have hle : g' < E := by
      have : ¬ E ≤ g' := by rw [← Nat.ble_eq, hc]; decide
      omega
    show PS (pmin _ _) x
    rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
    · exact PS_pmin_left (hcellx x h1 hx)
    · exact PS_pmin_right (hih g' hle x hx h2)
  · have hgt : E ≤ g' := by rw [← Nat.ble_eq, hc]
    exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))

theorem dstep2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound2 k E ih) :
    DSound2 k E (dstep2 top bk k E ih) := by
  intro g hg x h1 h2
  unfold dstep2
  simp only [forceR_eq]
  exact dcore2_sound hb ht k E hk hih g hg x h1 h2 _

theorem dcov2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      PS (dcov2 top bk k ib g) x := by
  intro g hg x h1 h2
  have hs : ∀ {f : ℕ → ℕ}, DSound2 k (Nat.add ib 1) f → DSound2 k (Nat.add ib 1) (dstep2 top bk k (Nat.add ib 1) f) :=
    fun hf => dstep2_sound hb ht k (Nat.add ib 1) hk hf
  exact hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (DSound2_zero k _)))))))))))))) g (by simp only [Nat.add_eq]; omega) x h1 h2

theorem blocks2_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk2 (bk j) j) = true) :
    ∀ j < 512, blockOk2 (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end AMW.Cert.PyrD

end

/-! ### the mean-value step for one pair term, and the per-gap bound -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

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

end AMW.Cert.PyrD

end

/-! ###### the slope test: point values of `w` and `w'`, and one pair term's expansion ######

A point table stores at grid points `x / SC` the triple (lower bound of `w`, lower bound of `w' + 2`, lower bound
of `2 − w'`), each checked on the degenerate integer cell `[x, x]`.  `slope_pair`: for `s` and `q` in `[lo, hi]`,
`w s ≥ w q + w'(q)(s − q) − R` with `R` from the derivative pair pyramid on `[q, hi]` and `[lo, q]` (convexity is
free: the charge is the drop of `w'` below `w'(q)` to the right of `q`, and its rise above `w'(q)` to the left). -/

section SlopeDefs

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- field `i` (96 bits) of a packed natural -/
def fld3 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 96 i)) 79228162514264337593543950335

/-- the degenerate integer cell `[x, x]` -/
def dcell (x : ℕ) : CellN := ⟨Nat.add (Nat.mul x KB) x, 0⟩

/-- the claims `p` on `w' + 2` and `m` on `2 − w'` at the point `x / SC`, units `1/U1` (`0` claims nothing) -/
def ptdOk (x p m : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((Nat.beq p 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1LO)))
      && (Nat.beq m 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1HI))))
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
    (forceR (Nat.shiftRight x 10) fun jb =>
      let X := pb jb
      Bool.rec (motive := fun _ => ℕ) 0 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0))
    0 (Nat.ble 524288 x)


/-- the three-piece read of the `w` pyramid: for `hi − lo ≥ 1024`, the minimum of the reads on `[lo, lo + a]`,
`[lo + a, hi − a]` and `[hi − a, hi]` with `a = (hi − lo) / 16`, so that the middle read's overhang stays inside
`[lo, hi]` and only the two short end reads overhang -/
def lb3 (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  let a := Nat.shiftRight (Nat.sub hi lo) 4
  Bool.rec (motive := fun _ => ℕ) (lb top bk lo hi)
    (nmin (lb top bk lo (Nat.add lo a)) (nmin (lb top bk (Nat.add lo a) (Nat.sub hi a)) (lb top bk (Nat.sub hi a) hi)))
    (Nat.ble 1024 (Nat.sub hi lo))

/-- the derivative pair read with cover shift `6` (cells of `1/32 .. 1/64` of the interval) and fuel `14` -/
def lbDr (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 6)
       dcov2 top bk k (Nat.shiftRight (Nat.sub hi 1) k) (Nat.shiftRight lo k))
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
    (Nat.ble 1 (lo32 (hi32 X)) &&ₖ Nat.ble 1 (hi32 (hi32 X)) &&ₖ (Nat.beq U QS ||ₖ Nat.ble 1 (lo32 EU))
      &&ₖ (Nat.beq QS L ||ₖ Nat.ble 1 (hi32 ED))) bit

end AMW.Cert.PyrD

end SlopeDefs

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the three-piece read is a lower bound wherever the pyramid read is: every `x` of `[lo, hi]` lies in one of the
three pieces -/
theorem lb3_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) :
    ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb3 top bk lo hi : ℝ) / 10000000000 ≤ wfun x := by
  intro lo hi x h1 h2
  unfold lb3
  dsimp only
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
      show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 6)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 6)))
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
    show (lo32 (forceR (Nat.shiftRight x 10) fun jb =>
      let X := pb jb
      Bool.rec (motive := fun _ => ℕ) 0 (fld3 (Nat.shiftRight X 4) (Nat.shiftRight (Nat.land x 1023) (Nat.land X 15)))
        (Nat.beq (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.land X 15)) 1)) 0)) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      ∧ PS (hi32 (forceR (Nat.shiftRight x 10) fun jb =>
      let X := pb jb
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
    linarith only [hR2, mul_le_mul_of_nonneg_right hqs hn0, mul_le_mul_of_nonneg_left (show 1000000000 * (w1 ξ - w1 q) ≤ ((4000000000 - (hi32 (lbDr tD bD lo qt) + lo32 v) : ℕ) : ℝ) by linarith) hqs0]
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
    linarith only [hR1, mul_le_mul_of_nonneg_right hsq' hn0, mul_le_mul_of_nonneg_left (show 1000000000 * (w1 q - w1 ξ) ≤ ((4000000000 - (hi32 v + lo32 (lbDr tD bD qt hi)) : ℕ) : ℝ) by linarith) hsq0]


end AMW.Cert.PyrD

end

/-! ###### convex basins: the sign of `w''` on a cell, chains of cells where `w'' ≥ 0`, and the tangent minorant ######

Basin boxes at the near-minimal local minima after six-point-convex-basins-2 by typh (Apache-2.0): around such a
minimum each pair term is convex on its range, so its tangent at the expansion point is a lower bound and the slope
test needs no charge.  Here `w'' = 2π² P / D⁴` with `P = M² + N (N₂ D² + 4 N D + 8 b M)` and
`N₂ = −(1 + 4γ) cos b + 2γ b sin b` (`b = π x`, `N`, `M`, `D` as in the derivative cells); a cell certifies
`w'' ≥ 0` when the integer enclosure of `P` is nonnegative. -/

section ConvDefs


namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the cell `[a, b] / SC` -/
def ccell (a b : ℕ) : CellN := ⟨Nat.add (Nat.mul a KB) b, 0⟩

/-- a chain `a = c₀ ≤ c₁ ≤ … ≤ c_k` of cells `[c_i, c_(i+1)]`, each certifying `w'' ≥ 0` -/
def chainOk (a : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && ih b) l a

/-- the chain's last point -/
def chainLast (a : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun a => a) (fun b _ ih _ => ih b) l a

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

/-- convex regions by index `k` (the region around the integer `k`): bounds packed in 20-bit fields of `R.1` and
`R.2.1`, chains in `R.2.2` -/
def rgA (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.1 (Nat.mul 20 k)) 1048575
def rgB (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.2.1 (Nat.mul 20 k)) 1048575
/-- the range `[lo, hi]` lies in the convex region of the integer nearest to `lo` -/
def inRg (R : ℕ × ℕ × List (List ℕ)) (lo hi : ℕ) : Bool :=
  let k := Nat.shiftRight (Nat.add lo 16384) 15
  Nat.blt k 16 &&ₖ Nat.ble (rgA R k) lo &&ₖ Nat.ble hi (rgB R k)
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
end AMW.Cert.PyrD

end ConvDefs

noncomputable section

namespace AMW.Cert

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

end AMW.Cert

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

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
  · simp only [tok, brecAnd, brecOr, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
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

theorem bforce_eq (b : Bool) (k : Bool → Bool) : bforce b k = k b := by cases b <;> rfl

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
  simp only [brecAnd, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
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

theorem cvflag' {b c : Bool} (h : (c && b) = true) : b = true := by
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

end AMW.Cert.PyrD

end

