-- Variant C2: variant C with only the lookupAllN key forcing kept (the other three reverted to variant B).
/-
Variant C (exploratory): variant B plus forcing inside the remaining helpers.
* `piecesNF`: the grid point `q` is forced before it is used twice (`roundFar a q`, recursive call).
* `lookupAllNF`: the packed key `a * KB + b` is forced before the search.
* `chainWNF`: `chainWN rest` is forced once (the original names it twice).
* `walk`: the split axis, the midpoint and `pos + 4` are forced before the recursive calls.
Same values as A/B; the walk theorem statements are unchanged.
-/
import BenchCore

universe u

def force {α : Sort u} (a : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (motive := fun _ => α) a (k 0) (fun n => k (Nat.succ n))

namespace Zeta23Ext.Bridge.ThreePoint

def piecesNF : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(roundFar a hi)]
  | fuel + 1, a, hi =>
      force (((a >>> 13) + 1) <<< 13) fun q =>
      bif Nat.blt q hi then (roundFar a q) :: piecesNF fuel q hi else [(roundFar a hi)]

def lookupAllNF (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      force (a * KB + b) fun key =>
      match t.find key, lookupAllNF t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainWNF : List CellN → ℕ
  | [] => 0
  | c :: rest => force (chainWNF rest) fun m =>
      bif rest.isEmpty then c.WN else bif Nat.ble c.WN m then c.WN else m

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllNF t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ :=
  force lo fun lo => force hi fun hi => termWNcore t lo hi (piecesN' lo hi)

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
  Nat.ble (cN * SC * SW) ((24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) * SW + (25326800 * termWN tb l0 u0 + 62369200 * termWN tb l01 u01 + 40126500 * termWN tb l02 u02 + 99999900 * termWN tb l03 u03 + 200000000 * termWN tb l04 u04 + 48244400 * termWN tb l1 u1 + 37630700 * termWN tb l12 u12 + 119746800 * termWN tb l13 u13 + 99999900 * termWN tb l14 u14 + 52857300 * termWN tb l2 u2 + 37630700 * termWN tb l23 u23 + 40126500 * termWN tb l24 u24 + 48244400 * termWN tb l3 u3 + 62369200 * termWN tb l34 u34 + 25326800 * termWN tb l4 u4) * SC)

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
