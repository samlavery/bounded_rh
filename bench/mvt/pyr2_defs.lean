
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
