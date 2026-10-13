import ConvCore
set_option profiler true
set_option profiler.threshold 10
set_option maxRecDepth 100000
open Zeta23Ext.Bridge.ThreePoint.Pyr
def tI (a b : ℤ) : Bool := decide (a < b)
def tI2 (a b : ℤ) : Bool := decide (a ≤ b)
def tm (a b : ℤ) : ℤ := min a b
def tmul (a b : ℤ) : ℤ := a * b
def tdiv (a b : ℤ) : ℤ := a / b
set_option pp.explicit true in
#print tI
set_option pp.explicit true in
#print tI2
set_option pp.explicit true in
#print tm
set_option pp.explicit true in
#print tdiv
def L1 : List (ℕ × ℤ) := [(1, -12378982), (2, -12602495), (3, -4164033), (4, 5741405), (5, 1724025), (6, 6219280), (7, 8047828),
   (8, 6321519), (9, 5241981), (10, -892658), (11, -560544), (12, -431207)]
def sumL : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (j, e) :: rest => e * j + sumL rest
def sumF (t : ℕ) : ℤ := L1.foldl (fun acc p => acc + p.2 * (p.1 + t)) 0
theorem b1 : allBelow 64 (fun t => decide (sumL L1 + t ≤ 0) || true) = true := by decide +kernel
theorem b2 : allBelow 64 (fun t => decide (sumF t ≤ 0) || true) = true := by decide +kernel
theorem b3 : allBelow 64 (fun t => decide ((t : ℤ) * 1000000000000000 < 5000000000000000000000) || true) = true := by decide +kernel
theorem b4 : allBelow 64 (fun t => Nat.blt (t * 1000000000000000) 5000000000000000000000 || true) = true := by decide +kernel
theorem b5 : allBelow 64 (fun t => decide (min ((t : ℤ) * 1000000000000000) 7 ≤ 5) || true) = true := by decide +kernel
theorem b6 : allBelow 64 (fun t => decide ((t : ℤ) * 1000000000000000 / 7 ≤ 5) || true) = true := by decide +kernel
theorem b7 : allBelow 640 (fun t => decide ((t : ℤ) * 1000000000000000 / 7 ≤ 5) || true) = true := by decide +kernel
theorem b8 : allBelow 640 (fun t => decide ((-(t : ℤ)) * 1000000000000000 / 7 ≤ 5) || true) = true := by decide +kernel
theorem b9 : allBelow 640 (fun t => decide ((t : ℤ) ^ 3 ≤ 5) || true) = true := by decide +kernel
