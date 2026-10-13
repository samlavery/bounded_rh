/-
Cost-attribution probe P0: the variant-B `walk` with `leafCheck` replaced by `true`
(traversal only: bit tests, axis decoding, box construction, the `u4 < l0` half-space test).
Not a checker; it only exists to split the kernel time.
-/
import BenchCore

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

def leafCheck (_tb : CTN) (_b : Box) : Bool := true

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
