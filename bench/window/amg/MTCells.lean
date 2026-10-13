import SevC
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD
theorem warm : Pyr.allFrom 0 64 (fun i => Nat.ble i 5 || true) = true := by decide +kernel
theorem cellsW : Pyr.allFrom (81*16) (67*16) (fun i => (cellAt 6 i).okC || true) = true := by decide +kernel
theorem cellsD : Pyr.allFrom (128*32) (24*32) (fun i => (cellAt 5 i).okD || true) = true := by decide +kernel
theorem cellsD2 : Pyr.allFrom (128*32) (24*32) (fun i => cellOk2 5 i 0 || true) = true := by decide +kernel
