import ConvCore
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
open Zeta23Ext.Bridge.ThreePoint.Pyr
def fl (a : ℤ) (b : ℕ) : ℤ := if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else -(((((-a).toNat + b - 1) / b : ℕ)) : ℤ)
theorem d0 : allBelow 640 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem d1 : allBelow 640 (fun t => Nat.ble t 5 || true) = true := by decide +kernel
theorem n1 : allBelow 640 (fun t => Nat.ble (t * 1000000000000000 / 7 + t * t) 5 || true) = true := by decide +kernel
theorem i1 : allBelow 640 (fun t => decide ((t:ℤ) * 1000000000000000 - 7 * t ≤ 5) || true) = true := by decide +kernel
theorem i2 : allBelow 640 (fun t => decide ((t:ℤ) * 1000000000000000 - 7 * t ≤ -5) || true) = true := by decide +kernel
theorem i3 : allBelow 640 (fun t => decide (min ((t:ℤ) * 1000000000000000) (-7 * t) ≤ 5) || true) = true := by decide +kernel
theorem i4 : allBelow 640 (fun t => decide (fl ((t:ℤ) * 1000000000000000 - 70000000000000000000) 7 ≤ 5) || true) = true := by decide +kernel
theorem i5 : allBelow 640 (fun t => decide ((t:ℤ) - 1000000000000000 ≤ 5) || true) = true := by decide +kernel
theorem i6 : allBelow 640 (fun t => decide ((t:ℤ) + 1000000000000000 ≤ 5) || true) = true := by decide +kernel
theorem i7 : allBelow 640 (fun t => decide ((-(t:ℤ)) * 1000000000000000 ≤ 5) || true) = true := by decide +kernel
theorem i8 : allBelow 640 (fun t => decide ((t:ℤ) < 5) || true) = true := by decide +kernel
theorem i9 : allBelow 640 (fun t => decide ((t:ℤ) ≤ 5) || true) = true := by decide +kernel
theorem i10 : allBelow 640 (fun t => decide (5 ≤ (t:ℤ)) || true) = true := by decide +kernel
theorem i11 : allBelow 640 (fun t => decide (-(t:ℤ) ≤ 5) || true) = true := by decide +kernel
