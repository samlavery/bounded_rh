import PyrCheck

-- MVTDEFS-BEGIN
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
def PGI (c : CellN) : ℤ × ℤ := imulD GAMI c.BI
def NI (c : CellN) : ℤ × ℤ := isubZ c.CXZ (imulD c.PGI c.SXZ)
def NbI (c : CellN) : ℤ × ℤ := isubZ (0, 0) (iaddZ (imulD G1I c.SXZ) (imulD c.PGI c.CXZ))
def DI (c : CellN) : ℤ × ℤ := isubZ ((DZ : ℤ), (DZ : ℤ)) (imulZZ 2 (imulD c.BI c.BI))
def MI (c : CellN) : ℤ × ℤ := iaddZ (imulD c.NbI c.DI) (imulD (imulZZ 4 c.BI) c.NI)
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
The cover arithmetic is that of `Pyr.lb` (pyramid layout adapted from five-point-pyramid-2 by typh, Apache-2.0); the
entries read are combined by the componentwise minimum `pmin`, and the verification checks every coarser entry
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
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
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
-- MVTDEFS-END
