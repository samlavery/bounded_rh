import ConvCore
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1

namespace AMW.F
def DZ : ℕ := 1000000000000000
def DZ2 : ℕ := 1000000000000000000000000000000
def DZ3 : ℕ := 1000000000000000000000000000000000000000000000
def ndivc (a b : ℕ) : ℕ := Nat.div (Nat.sub (Nat.add a b) 1) b
def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a
def forceB (a : ℕ) (k : ℕ → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) a
/-- list-fold version: (j, |e|, sg, J, J2) -/
structure Acc where (pl ph nl nh : ℕ)
def Acc.put (a : Acc) (neg : Bool) (e m0 m1 : ℕ) : Acc :=
  Bool.rec (motive := fun _ => Acc) ⟨Nat.add a.pl (Nat.mul e m0), Nat.add a.ph (Nat.mul e m1), a.nl, a.nh⟩
    ⟨a.pl, a.ph, Nat.add a.nl (Nat.mul e m0), Nat.add a.nh (Nat.mul e m1)⟩ neg
/-- n = 0 term of j: `x/(x²−J²)` (or the half pole term) -/
def term0 (k XL XU XL2 XU2 : ℕ) (a : Acc) (j e : ℕ) (sg : Bool) (J J2 : ℕ) : Acc :=
  Bool.rec (motive := fun _ => Acc)
    (Bool.rec (motive := fun _ => Acc)
      (a.put (!sg) e (Nat.div (Nat.mul XL DZ2) (Nat.sub J2 XL2)) (ndivc (Nat.mul XU DZ2) (Nat.sub J2 XU2)))
      (a.put sg e (Nat.div DZ2 (Nat.mul 2 (Nat.add XU J))) (ndivc DZ2 (Nat.mul 2 (Nat.add XL J))))
      (Nat.beq (Nat.mul 2 j) k))
    (a.put sg e (Nat.div (Nat.mul XU DZ2) (Nat.sub XU2 J2)) (ndivc (Nat.mul XL DZ2) (Nat.sub XL2 J2)))
    (Nat.blt (Nat.mul 2 j) k)
def fold0 (k XL XU XL2 XU2 : ℕ) : List (ℕ × ℕ × Bool × ℕ × ℕ) → Acc → Acc
  | [], a => a
  | (j, e, sg, J, J2) :: rest, a => fold0 k XL XU XL2 XU2 rest (term0 k XL XU XL2 XU2 a j e sg J J2)

def CE2 : List (ℕ × ℕ × Bool × ℕ × ℕ) := [(1, 12378982, true, 1000000000000000, 1000000000000000000000000000000), (2, 12602495, true, 2000000000000000, 4000000000000000000000000000000), (3, 4164033, true, 3000000000000000, 9000000000000000000000000000000), (4, 5741405, false, 4000000000000000, 16000000000000000000000000000000), (5, 1724025, false, 5000000000000000, 25000000000000000000000000000000), (6, 6219280, false, 6000000000000000, 36000000000000000000000000000000), (7, 8047828, false, 7000000000000000, 49000000000000000000000000000000), (8, 6321519, false, 8000000000000000, 64000000000000000000000000000000), (9, 5241981, false, 9000000000000000, 81000000000000000000000000000000), (10, 892658, true, 10000000000000000, 100000000000000000000000000000000), (11, 560544, true, 11000000000000000, 121000000000000000000000000000000), (12, 431207, true, 12000000000000000, 144000000000000000000000000000000)]
def F0list (k XL XU : ℕ) : Acc := fold0 k XL XU (Nat.mul XL XL) (Nat.mul XU XU) CE2 ⟨0, 0, 0, 0⟩
/-- one term in CPS: adds `±e·[m0, m1]` to the accumulators and continues -/
def putK (neg : Bool) (e m0 m1 pl ph nl nh : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (forceB (Nat.add pl (Nat.mul e m0)) fun pl' => forceB (Nat.add ph (Nat.mul e m1)) fun ph' => k pl' ph' nl nh)
    (forceB (Nat.add nl (Nat.mul e m0)) fun nl' => forceB (Nat.add nh (Nat.mul e m1)) fun nh' => k pl ph nl' nh')
    neg
def termK (kk XL XU XL2 XU2 j e : ℕ) (sg : Bool) (J J2 : ℕ) (pl ph nl nh : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (putK (!sg) e (Nat.div (Nat.mul XL DZ2) (Nat.sub J2 XL2)) (ndivc (Nat.mul XU DZ2) (Nat.sub J2 XU2)) pl ph nl nh k)
      (putK sg e (Nat.div DZ2 (Nat.mul 2 (Nat.add XU J))) (ndivc DZ2 (Nat.mul 2 (Nat.add XL J))) pl ph nl nh k)
      (Nat.beq (Nat.mul 2 j) kk))
    (putK sg e (Nat.div (Nat.mul XU DZ2) (Nat.sub XU2 J2)) (ndivc (Nat.mul XL DZ2) (Nat.sub XL2 J2)) pl ph nl nh k)
    (Nat.blt (Nat.mul 2 j) kk)
def F0K (kk XL XU : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  forceB (Nat.mul XL XL) fun XL2 => forceB (Nat.mul XU XU) fun XU2 =>
  let pl := 0; let ph := 0; let nl := 0; let nh := 0
  termK kk XL XU XL2 XU2 1 12378982 true 1000000000000000 1000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 2 12602495 true 2000000000000000 4000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 3 4164033 true 3000000000000000 9000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 4 5741405 false 4000000000000000 16000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 5 1724025 false 5000000000000000 25000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 6 6219280 false 6000000000000000 36000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 7 8047828 false 7000000000000000 49000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 8 6321519 false 8000000000000000 64000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 9 5241981 false 9000000000000000 81000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 10 892658 true 10000000000000000 100000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 11 560544 true 11000000000000000 121000000000000000000000000000000 pl ph nl nh fun pl ph nl nh =>
  termK kk XL XU XL2 XU2 12 431207 true 12000000000000000 144000000000000000000000000000000 pl ph nl nh fun pl ph nl nh => k pl ph nl nh
end AMW.F
open Zeta23Ext.Bridge.ThreePoint.Pyr AMW.F
theorem warm : allBelow 64 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem tL : allBelow 64 (fun t => Nat.ble (F0list 7 (3500000000000000 + t * 1000000000) (3500000000000000 + t * 1000000000 + 100)).pl 5 || true) = true := by decide +kernel
theorem tK : allBelow 64 (fun t => F0K 7 (3500000000000000 + t * 1000000000) (3500000000000000 + t * 1000000000 + 100) (fun pl _ _ _ => Nat.ble pl 5) || true) = true := by decide +kernel
theorem tL2 : allBelow 64 (fun t => Nat.ble (F0list 4 (2000000000000000 + t * 1000000000) (2000000000000000 + t * 1000000000 + 100)).pl 5 || true) = true := by decide +kernel
theorem tK2 : allBelow 64 (fun t => F0K 4 (2000000000000000 + t * 1000000000) (2000000000000000 + t * 1000000000 + 100) (fun pl _ _ _ => Nat.ble pl 5) || true) = true := by decide +kernel
#eval (F0list 7 3500000000000000 3500000000000100)
#eval F0K 7 3500000000000000 3500000000000100 (fun pl ph nl nh => dbgTrace s!"{pl} {ph} {nl} {nh}" fun _ => true)
