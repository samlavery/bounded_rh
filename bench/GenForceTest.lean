-- test of the gen_checkerN_force.py block (generated for SixW7 params) in the core-only bench environment
import BenchData
import BenchADefs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1

/-! ###### call-by-value copies of the leaf/walk checker (`forceN`), equal to the originals as functions ###### -/

section SixW7Force

universe uF

namespace Zeta23Ext.Bridge.ThreePoint

/-- evaluate a natural-number argument to a numeral once, then continue: the kernel reduces the
`Nat.casesOn` scrutinee to a literal, so `k` receives a numeral instead of the unevaluated term -/
def forceN {α : Sort uF} (a : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (motive := fun _ => α) a (k 0) (fun n => k (Nat.succ n))

theorem forceN_eq {α : Sort uF} (a : ℕ) (k : ℕ → α) : forceN a k = k a := by cases a <;> rfl

def piecesNF : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(roundFar a hi)]
  | fuel + 1, a, hi =>
      forceN (((a >>> 13) + 1) <<< 13) fun q =>
      bif Nat.blt q hi then (roundFar a q) :: piecesNF fuel q hi else [(roundFar a hi)]

def lookupAllNF (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      forceN (a * KB + b) fun key =>
      match t.find key, lookupAllNF t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainWNF : List CellN → ℕ
  | [] => 0
  | c :: rest => forceN (chainWNF rest) fun m =>
      bif rest.isEmpty then c.WN else bif Nat.ble c.WN m then c.WN else m

def termWNcoreF (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllNF t ps with
  | some cs => if chainOKN lo hi cs then chainWNF cs else 0
  | none => 0

def termWNF (t : CTN) (lo hi : ℕ) : ℕ :=
  forceN lo fun lo => forceN hi fun hi => termWNcoreF t lo hi (piecesNF 64 lo hi)

theorem piecesNF_eq : ∀ fuel a hi, piecesNF fuel a hi = piecesN fuel a hi
  | 0, a, hi => by simp only [piecesNF, piecesN]
  | fuel + 1, a, hi => by simp only [piecesNF, piecesN, forceN_eq, piecesNF_eq fuel]

theorem lookupAllNF_eq (t : CTN) : ∀ ps, lookupAllNF t ps = lookupAllN t ps
  | [] => by simp only [lookupAllNF, lookupAllN]
  | (a, b) :: rest => by simp only [lookupAllNF, lookupAllN, forceN_eq, lookupAllNF_eq t rest]; (try rfl)

theorem chainWNF_eq : ∀ cs, chainWNF cs = chainWN cs
  | [] => by simp only [chainWNF, chainWN]
  | c :: rest => by simp only [chainWNF, chainWN, forceN_eq, chainWNF_eq rest]

theorem termWNF_eq (t : CTN) (lo hi : ℕ) : termWNF t lo hi = termWN t lo hi := by
  simp only [termWNF, termWN, forceN_eq, termWNcoreF, termWNcore, piecesNF_eq, lookupAllNF_eq, chainWNF_eq, piecesN']; (try rfl)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW7

def leafCheckF (tb : CTN) (b : Box) : Bool :=
  forceN b.l0 fun l0 =>
  forceN b.l1 fun l1 =>
  forceN b.l2 fun l2 =>
  forceN b.l3 fun l3 =>
  forceN b.l4 fun l4 =>
  forceN b.u0 fun u0 =>
  forceN b.u1 fun u1 =>
  forceN b.u2 fun u2 =>
  forceN b.u3 fun u3 =>
  forceN b.u4 fun u4 =>
  forceN (l0 + l1) fun l0_2 =>
  forceN (l0_2 + l2) fun l0_3 =>
  forceN (l0_3 + l3) fun l0_4 =>
  forceN (l0_4 + l4) fun l0_5 =>
  forceN (l1 + l2) fun l1_3 =>
  forceN (l1_3 + l3) fun l1_4 =>
  forceN (l1_4 + l4) fun l1_5 =>
  forceN (l2 + l3) fun l2_4 =>
  forceN (l2_4 + l4) fun l2_5 =>
  forceN (l3 + l4) fun l3_5 =>
  forceN (u0 + u1) fun u0_2 =>
  forceN (u0_2 + u2) fun u0_3 =>
  forceN (u0_3 + u3) fun u0_4 =>
  forceN (u0_4 + u4) fun u0_5 =>
  forceN (u1 + u2) fun u1_3 =>
  forceN (u1_3 + u3) fun u1_4 =>
  forceN (u1_4 + u4) fun u1_5 =>
  forceN (u2 + u3) fun u2_4 =>
  forceN (u2_4 + u4) fun u2_5 =>
  forceN (u3 + u4) fun u3_5 =>
  Nat.ble (cN * SC * SW) ((24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) * SW + (25326800 * termWNF tb l0 u0 + 62369200 * termWNF tb l0_2 u0_2 + 40126500 * termWNF tb l0_3 u0_3 + 99999900 * termWNF tb l0_4 u0_4 + 200000000 * termWNF tb l0_5 u0_5 + 48244400 * termWNF tb l1 u1 + 37630700 * termWNF tb l1_3 u1_3 + 119746800 * termWNF tb l1_4 u1_4 + 99999900 * termWNF tb l1_5 u1_5 + 52857300 * termWNF tb l2 u2 + 37630700 * termWNF tb l2_4 u2_4 + 40126500 * termWNF tb l2_5 u2_5 + 48244400 * termWNF tb l3 u3 + 62369200 * termWNF tb l3_5 u3_5 + 25326800 * termWNF tb l4 u4) * SC)

def walkF (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        forceN (axOf bits pos) fun ax => forceN (b.mid ax) fun q => forceN (pos + 4) fun p4 =>
        match walkF tb bits fuel p4 (b.setHi ax q) with
        | none => none
        | some pos' => walkF tb bits fuel pos' (b.setLo ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheckF tb b then some (pos + 1) else none

theorem leafCheckF_eq (tb : CTN) (b : Box) : leafCheckF tb b = leafCheck tb b := by
  simp only [leafCheckF, leafCheck, forceN_eq, termWNF_eq]

/-- the forced walk is the walk: walk theorems are checked on `walkF` and read back through this -/
theorem walkF_eq (tb : CTN) (bits : ℕ) : ∀ fuel pos b, walkF tb bits fuel pos b = walk tb bits fuel pos b
  | 0, _, _ => by simp only [walkF, walk]
  | fuel + 1, pos, b => by simp only [walkF, walk, forceN_eq, leafCheckF_eq, walkF_eq tb bits fuel]; (try rfl)

end Zeta23Ext.Bridge.ThreePoint.SixW7

end SixW7Force

namespace Zeta23Ext.Bridge.ThreePoint.SixW7Data

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW7

set_option maxRecDepth 100000

theorem wk0 : SixW7.walk table bits 64 0 bx0 = some 1431 :=
  (SixW7.walkF_eq table bits 64 0 bx0).symm.trans (by decide +kernel)

theorem wk15 : SixW7.walk table bits 59 25358 bx15 = some 25394 :=
  (SixW7.walkF_eq table bits 59 25358 bx15).symm.trans (by decide +kernel)

theorem wk15_bad : SixW7.walk table bits 59 25358 bx15 = some 25395 :=
  (SixW7.walkF_eq table bits 59 25358 bx15).symm.trans (by decide +kernel)

#print axioms wk0
#print axioms SixW7.walkF_eq
end Zeta23Ext.Bridge.ThreePoint.SixW7Data
