def A : Nat := 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem tA : Nat.land (Nat.shiftRight A 100) 255 = 255 := by decide +kernel
#print A
