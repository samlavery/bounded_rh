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

theorem e4 : "B+NAAeaaACgQAJyDRkhTQACclNgGW6KbAIlZwJRYD8aAARcpsAyx5TYKcOAhHINGSFNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU2AZbUpsACk9iIbo+WNzYMEB8DVwDKrmrgUaKwjlxbgLigfjQAQGwGTAKsyU2ANIr8IfA".toByteArray.data.toList.length = 667 := by decide +kernel
