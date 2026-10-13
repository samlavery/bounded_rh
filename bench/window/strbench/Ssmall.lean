noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000

/-- the 6-bit value of a base64 character (A–Z a–z 0–9 + /) -/
def b64v (c : Char) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 63 62 (Nat.beq c.toNat 43))
        (Nat.add c.toNat 4) (Nat.ble 48 c.toNat))
      (Nat.sub c.toNat 65) (Nat.ble 65 c.toNat))
    (Nat.sub c.toNat 71) (Nat.ble 97 c.toNat)

/-- big-endian base64 → ℕ -/
def dec (s : String) : Nat := s.foldl (fun a c => Nat.add (Nat.mul a 64) (b64v c)) 0


theorem a1 : b64v 'B' = 1 := by decide +kernel
theorem a2 : dec "B" = 1 := by decide +kernel
theorem a3 : dec "BA" = 64 := by decide +kernel
def dec2 (s : String) : Nat := s.toList.foldl (fun a c => Nat.add (Nat.mul a 64) (b64v c)) 0
theorem a4 : dec2 "BA" = 64 := by decide +kernel
theorem a5 : "BA".toList = ['B', 'A'] := by decide +kernel
