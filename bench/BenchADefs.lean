/-
Variant A (baseline): `termWNcore`, `termWN`, `leafCheck`, `walk` copied verbatim from
`../SolutionSixW7.lean` (lines ≈5726–5787).
-/
import BenchCore

namespace Zeta23Ext.Bridge.ThreePoint

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((24896 * b.l0 + 42034 * b.l1 + 46137 * b.l2 + 42034 * b.l3 + 24896 * b.l4) * SW + (25326800 * termWN tb (b.l0) (b.u0) + 62369200 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 40126500 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 99999900 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) + 200000000 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l1) (b.u1) + 37630700 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 119746800 * termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) + 99999900 * termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) + 52857300 * termWN tb (b.l2) (b.u2) + 37630700 * termWN tb (b.l2 + b.l3) (b.u2 + b.u3) + 40126500 * termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l3) (b.u3) + 62369200 * termWN tb (b.l3 + b.l4) (b.u3 + b.u4) + 25326800 * termWN tb (b.l4) (b.u4)) * SC)

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
