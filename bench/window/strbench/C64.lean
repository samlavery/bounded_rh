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

theorem b0 : "B+NAAeaaACgQAJyDRkhTQACclNgGW6KbAIlZwJRYD8aAARcpsAyx5TYKcOAhHING".toByteArray.size = 64 := by decide +kernel
theorem b1 : "SFNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRY".toByteArray.size = 64 := by decide +kernel
theorem b2 : "YIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYIC".toByteArray.size = 64 := by decide +kernel
theorem b3 : "vVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrG".toByteArray.size = 64 := by decide +kernel
theorem b4 : "yDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyl".toByteArray.size = 64 := by decide +kernel
theorem b5 : "djZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2".toByteArray.size = 64 := by decide +kernel
theorem b6 : "AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aA".toByteArray.size = 64 := by decide +kernel
theorem b7 : "A800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAE".toByteArray.size = 64 := by decide +kernel
theorem b8 : "jUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvV".toByteArray.size = 64 := by decide +kernel
theorem b9 : "NgGXgqbAAsGAXFA/GgAgJeU2AZbUpsACk9iIbo+WNzYMEB8DVwDKrmrgUaKwjlxb".toByteArray.size = 64 := by decide +kernel
theorem b10 : "JRYD8aAARcpsAyx5TYKcOAhHINGSFNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AA".toByteArray.size = 64 := by decide +kernel
theorem b11 : "QM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAA".toByteArray.size = 64 := by decide +kernel
theorem b12 : "gIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBT".toByteArray.size = 64 := by decide +kernel
theorem b13 : "kGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAy".toByteArray.size = 64 := by decide +kernel
theorem b14 : "dQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cA".toByteArray.size = 64 := by decide +kernel
theorem b15 : "yq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJy".toByteArray.size = 64 := by decide +kernel
theorem b16 : "rgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABAD".toByteArray.size = 64 := by decide +kernel
theorem b17 : "FwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPx".toByteArray.size = 64 := by decide +kernel
theorem b18 : "oAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU2AZbUpsACk9iIb".toByteArray.size = 64 := by decide +kernel
theorem b19 : "gQAJyDRkhTQACclNgGW6KbAIlZwJRYD8aAARcpsAyx5TYKcOAhHINGSFNAAJeU2A".toByteArray.size = 64 := by decide +kernel
