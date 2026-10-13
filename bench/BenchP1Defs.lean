/-
Cost-attribution probe P1: variant-B forcing of the box and the 15 interval sums, then only the
piece lists (`piecesN'`) of the 15 terms are generated and their lengths summed (no table search).
The `Nat.ble 0 _` makes the kernel reduce the sum to a numeral; the result is always `true`.
-/
import BenchCore

universe u

def force {α : Sort u} (a : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (motive := fun _ => α) a (k 0) (fun n => k (Nat.succ n))

namespace Zeta23Ext.Bridge.ThreePoint

def termWN (_t : CTN) (lo hi : ℕ) : ℕ :=
  force lo fun lo => force hi fun hi => (piecesN' lo hi).length

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

def leafCheck (tb : CTN) (b : Box) : Bool :=
  force b.l0 fun l0 => force b.l1 fun l1 => force b.l2 fun l2 => force b.l3 fun l3 => force b.l4 fun l4 =>
  force b.u0 fun u0 => force b.u1 fun u1 => force b.u2 fun u2 => force b.u3 fun u3 => force b.u4 fun u4 =>
  force (l0 + l1) fun l01 => force (l01 + l2) fun l02 => force (l02 + l3) fun l03 => force (l03 + l4) fun l04 =>
  force (l1 + l2) fun l12 => force (l12 + l3) fun l13 => force (l13 + l4) fun l14 =>
  force (l2 + l3) fun l23 => force (l23 + l4) fun l24 =>
  force (l3 + l4) fun l34 =>
  force (u0 + u1) fun u01 => force (u01 + u2) fun u02 => force (u02 + u3) fun u03 => force (u03 + u4) fun u04 =>
  force (u1 + u2) fun u12 => force (u12 + u3) fun u13 => force (u13 + u4) fun u14 =>
  force (u2 + u3) fun u23 => force (u23 + u4) fun u24 =>
  force (u3 + u4) fun u34 =>
  Nat.ble 0 (termWN tb l0 u0 + termWN tb l01 u01 + termWN tb l02 u02 + termWN tb l03 u03 + termWN tb l04 u04 + termWN tb l1 u1 + termWN tb l12 u12 + termWN tb l13 u13 + termWN tb l14 u14 + termWN tb l2 u2 + termWN tb l23 u23 + termWN tb l24 u24 + termWN tb l3 u3 + termWN tb l34 u34 + termWN tb l4 u4)

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := axOf bits pos
        let q := b.mid ax
        match walk tb bits fuel (pos + 4) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheck tb b then some (pos + 1) else none

end Zeta23Ext.Bridge.ThreePoint.SixW7
