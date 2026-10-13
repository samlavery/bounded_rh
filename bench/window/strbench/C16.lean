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
def dec (s : String) : Nat := s.toList.foldl (fun a c => Nat.add (Nat.mul a 64) (b64v c)) 0

theorem b0 : "B+NAAeaaACgQAJyD".toByteArray.size = 16 := by decide +kernel
theorem b1 : "RkhTQACclNgGW6Kb".toByteArray.size = 16 := by decide +kernel
theorem b2 : "AIlZwJRYD8aAARcp".toByteArray.size = 16 := by decide +kernel
theorem b3 : "sAyx5TYKcOAhHING".toByteArray.size = 16 := by decide +kernel
theorem b4 : "SFNAAJeU2AZa8psA".toByteArray.size = 16 := by decide +kernel
theorem b5 : "AgYAfjQAQEvKbAMt".toByteArray.size = 16 := by decide +kernel
theorem b6 : "eU2AAQM9jkGjJCmg".toByteArray.size = 16 := by decide +kernel
theorem b7 : "AgK2U2AZeQpsAaRY".toByteArray.size = 16 := by decide +kernel
theorem b8 : "YIucBPrGyDBAZGps".toByteArray.size = 16 := by decide +kernel
theorem b9 : "Ay9Zq4E0i6kRc9iI".toByteArray.size = 16 := by decide +kernel
theorem b10 : "nKuAAgIH40AB5poA".toByteArray.size = 16 := by decide +kernel
theorem b11 : "KBAAgQnUisbiwYIC".toByteArray.size = 16 := by decide +kernel
theorem b12 : "vVNgGXVqbAAnEsss".toByteArray.size = 16 := by decide +kernel
theorem b13 : "5V7AAfjQAHmmgAoE".toByteArray.size = 16 := by decide +kernel
theorem b14 : "AAEBTkGjJCmgAGXK".toByteArray.size = 16 := by decide +kernel
theorem b15 : "bAMuqYuAZOoYBPrG".toByteArray.size = 16 := by decide +kernel
theorem b16 : "yDBAdepsAyzxq4Fk".toByteArray.size = 16 := by decide +kernel
theorem b17 : "6hnsB+NAAHaU2AZV".toByteArray.size = 16 := by decide +kernel
theorem b18 : "UpsAydQwggPxoABL".toByteArray.size = 16 := by decide +kernel
theorem b19 : "ymwDLWFNgARHVqyl".toByteArray.size = 16 := by decide +kernel
