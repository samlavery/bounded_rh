import ConvCore
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
open Zeta23Ext.Bridge.ThreePoint.Pyr
def f1 (t : ℕ) : ℕ := ((((t * 1000000000000007 + 3) * 1000000000000007 + 3) / 13 + t) * 1000000000000007 + 3) / 17 + ((t * 1000000000000007 + 3) * 1000000000000007 + 3) / 19
def f2 (t : ℕ) : ℕ := Nat.add (Nat.div (Nat.add (Nat.mul (Nat.add (Nat.div (Nat.add (Nat.mul (Nat.add (Nat.mul t 1000000000000007) 3) 1000000000000007) 3) 13) t) 1000000000000007) 3) 17) (Nat.div (Nat.add (Nat.mul (Nat.add (Nat.mul t 1000000000000007) 3) 1000000000000007) 3) 19)
structure P3 where (a b c : ℕ)
def f3 (t : ℕ) : P3 := ⟨t * 3, t + 5, t * t⟩
def g3 (t : ℕ) : ℕ := (f3 t).a + (f3 t).b + (f3 t).c
def f4 (t : ℕ) : ℕ := bif Nat.ble t 300 then t * 7 else t + 9
theorem w0 : allBelow 640 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem w1 : allBelow 640 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem t1 : allBelow 640 (fun t => Nat.ble (f1 t) 5 || true) = true := by decide +kernel
theorem t2 : allBelow 640 (fun t => Nat.ble (f2 t) 5 || true) = true := by decide +kernel
theorem t3 : allBelow 640 (fun t => Nat.ble (g3 t) 5 || true) = true := by decide +kernel
theorem t4 : allBelow 640 (fun t => Nat.ble (f4 t) 5 || true) = true := by decide +kernel
