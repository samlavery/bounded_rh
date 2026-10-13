import BenchCore
import BenchSKQDefs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1

namespace Zeta23Ext.Bridge.ThreePoint.PyrSKQ

set_option maxRecDepth 100000

theorem wk20 : walk TOP BK wk20_seg 27 1 30720 33152 59904 75264 31744 38400 59904 75264 30720 40448 = 1572 := by decide +kernel

theorem wk21 : walk TOP BK wk21_seg 21 1 33152 35584 59904 63744 31744 38400 59904 75264 30720 40448 = 372 := by decide +kernel

theorem wk22 : walk TOP BK wk22_seg 20 1 33152 35584 63744 67584 31744 38400 59904 75264 30720 33152 = 772 := by decide +kernel

theorem wk23 : walk TOP BK wk23_seg 17 1 33152 35584 63744 67584 31744 38400 59904 63744 33152 35584 = 297 := by decide +kernel

theorem wk24 : walk TOP BK wk24_seg 16 1 33152 35584 63744 67584 31744 33408 63744 67584 33152 35584 = 372 := by decide +kernel

theorem wk25 : walk TOP BK wk25_seg 27 1 33152 35584 63744 64704 33408 35072 63744 67584 33152 35584 = 59087 := by decide +kernel

theorem wk26 : walk TOP BK wk26_seg 24 1 33152 35584 64704 65184 33408 35072 63744 64704 33152 35584 = 36222 := by decide +kernel

theorem wk27 : walk TOP BK wk27_seg 24 1 33152 35584 64704 65184 33408 34240 64704 65184 33152 35584 = 72647 := by decide +kernel

theorem wk28 : walk TOP BK wk28_seg 24 1 33152 35584 64704 65184 34240 35072 64704 65184 33152 35584 = 58472 := by decide +kernel

theorem wk29 : walk TOP BK wk29_seg 24 1 33152 35584 64704 65184 33408 35072 65184 65664 33152 35584 = 40282 := by decide +kernel

theorem wk30 : walk TOP BK wk30_seg 20 1 33152 35584 64704 65184 33408 35072 65664 67584 33152 35584 = 4287 := by decide +kernel

theorem wk31 : walk TOP BK wk31_seg 24 1 33152 35584 65184 65664 33408 35072 63744 64704 33152 35584 = 23347 := by decide +kernel

theorem wk32 : walk TOP BK wk32_seg 25 1 33152 35584 65184 65664 33408 35072 64704 65664 33152 35584 = 62607 := by decide +kernel

theorem wk33 : walk TOP BK wk33_seg 18 1 33152 35584 65184 65664 33408 35072 65664 67584 33152 35584 = 2242 := by decide +kernel

theorem wk34 : walk TOP BK wk34_seg 23 1 33152 35584 65664 67584 33408 35072 63744 67584 33152 35584 = 12922 := by decide +kernel

theorem wk35 : walk TOP BK wk35_seg 18 1 33152 35584 63744 67584 35072 38400 63744 67584 33152 35584 = 1132 := by decide +kernel

theorem wk36 : walk TOP BK wk36_seg 12 1 33152 35584 63744 67584 31744 38400 67584 75264 33152 35584 = 57 := by decide +kernel

theorem wk37 : walk TOP BK wk37_seg 19 1 33152 35584 63744 67584 31744 38400 59904 75264 35584 40448 = 407 := by decide +kernel

theorem wk38 : walk TOP BK wk38_seg 16 1 33152 35584 67584 75264 31744 38400 59904 75264 30720 40448 = 97 := by decide +kernel

theorem wk39 : walk TOP BK wk39_seg 21 1 35584 40448 59904 75264 31744 38400 59904 75264 30720 40448 = 567 := by decide +kernel

end Zeta23Ext.Bridge.ThreePoint.PyrSKQ
