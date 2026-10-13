import AMW.GCell
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000

namespace AMW.G
def CE2 : List ((ℕ × ℕ × Bool) × (ℕ × ℕ)) := [((1, 12378982, true), (1000000000000000, 1000000000000000000000000000000)), ((2, 12602495, true), (2000000000000000, 4000000000000000000000000000000)), ((3, 4164033, true), (3000000000000000, 9000000000000000000000000000000)), ((4, 5741405, false), (4000000000000000, 16000000000000000000000000000000)), ((5, 1724025, false), (5000000000000000, 25000000000000000000000000000000)), ((6, 6219280, false), (6000000000000000, 36000000000000000000000000000000)), ((7, 8047828, false), (7000000000000000, 49000000000000000000000000000000)), ((8, 6321519, false), (8000000000000000, 64000000000000000000000000000000)), ((9, 5241981, false), (9000000000000000, 81000000000000000000000000000000)), ((10, 892658, true), (10000000000000000, 100000000000000000000000000000000)), ((11, 560544, true), (11000000000000000, 121000000000000000000000000000000)), ((12, 431207, true), (12000000000000000, 144000000000000000000000000000000))]
def farJ2 (n k XL XU XL2 XU2 : ℕ) (a : Acc) (j e : ℕ) (sg : Bool) (J J2 : ℕ) : Acc :=
  Bool.rec (motive := fun _ => Acc)
    (Bool.rec (motive := fun _ => Acc)
      (a.put (xor sg (mneg n false)) e (Nat.div (mnum n XL XL2 J2) (Nat.pow (Nat.sub J2 XL2) (Nat.succ n)))
        (ndivc (mnum n XU XU2 J2) (Nat.pow (Nat.sub J2 XU2) (Nat.succ n))))
      (a.put (xor sg (mneg n true)) e (Nat.div (mnum n XU XU2 J2) (Nat.pow (Nat.sub XU2 J2) (Nat.succ n)))
        (ndivc (mnum n XL XL2 J2) (Nat.pow (Nat.sub XL2 J2) (Nat.succ n))))
      (Nat.blt (Nat.mul 2 j) k))
    (a.put (xor sg (hneg n)) e (Nat.div (DZp (Nat.add n 2)) (hden n (Nat.add XU J)))
      (ndivc (DZp (Nat.add n 2)) (hden n (Nat.add XL J))))
    (Nat.beq (Nat.mul 2 j) k)
def farAcc2 (n k XL XU XL2 XU2 : ℕ) : List ((ℕ × ℕ × Bool) × (ℕ × ℕ)) → Acc → Acc
  | [], a => a
  | ((j, e, sg), (J, J2)) :: rest, a => farAcc2 n k XL XU XL2 XU2 rest (farJ2 n k XL XU XL2 XU2 a j e sg J J2)
def CellA.FA2 (c : CellA) (n : ℕ) : IV :=
  let a := farAcc2 n c.k c.LLO c.UHI (Nat.mul c.LLO c.LLO) (Nat.mul c.UHI c.UHI) CE2 ⟨0, 0, 0, 0⟩
  IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9
end AMW.G
open AMW.G
def allB (n : ℕ) (f : ℕ → Bool) : Bool := Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f k) ih) n
def cA (l i : ℕ) : CellA := ⟨Nat.shiftLeft i l, Nat.shiftLeft (Nat.add i 1) l⟩
theorem warm : allB 64 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem z0 : allB 64 (fun t => (cA 5 (3600 + t)).ok && (cA 5 (3600 + t)).KA.nonneg) = true := by decide +kernel
theorem d0 : allB 64 (fun t => (cA 5 (3600 + t)).ok && (cA 5 (3600 + t)).W1.lo.le (cA 5 (3600 + t)).W1.hi) = true := by decide +kernel
theorem c0 : allB 64 (fun t => (cA 5 (3600 + t)).ok && ((cA 5 (3600 + t)).W2L.nonneg || true)) = true := by decide +kernel
theorem z1 : allB 64 (fun t => (cA 5 (2048 + t)).ok && (cA 5 (2048 + t)).KA.nonneg) = true := by decide +kernel
theorem d1 : allB 64 (fun t => (cA 5 (2048 + t)).ok && (cA 5 (2048 + t)).W1.lo.le (cA 5 (2048 + t)).W1.hi) = true := by decide +kernel
theorem ok1 : allB 64 (fun t => (cA 5 (2048 + t)).ok) = true := by decide +kernel
theorem fa1 : allB 64 (fun t => ((cA 5 (2048 + t)).FA 0).lo.le ((cA 5 (2048 + t)).FA 0).hi) = true := by decide +kernel
theorem fa2 : allB 64 (fun t => ((cA 5 (2048 + t)).FA2 0).lo.le ((cA 5 (2048 + t)).FA2 0).hi) = true := by decide +kernel
theorem fa1b : allB 64 (fun t => ((cA 5 (2048 + t)).FA 0).lo.le ((cA 5 (2048 + t)).FA 0).hi) = true := by decide +kernel
theorem ept : allB 64 (fun t => Nat.ble (Nat.mul (cA 5 (2048 + t)).LLO (cA 5 (2048 + t)).UHI) 5 || true) = true := by decide +kernel
