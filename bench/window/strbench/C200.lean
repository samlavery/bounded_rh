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

theorem b0 : "B+NAAeaaACgQAJyDRkhTQACclNgGW6KbAIlZwJRYD8aAARcpsAyx5TYKcOAhHINGSFNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVq".toByteArray.size = 200 := by decide +kernel
theorem b1 : "bAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbI".toByteArray.size = 200 := by decide +kernel
theorem b2 : "MEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU2".toByteArray.size = 200 := by decide +kernel
theorem b3 : "PrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZV".toByteArray.size = 200 := by decide +kernel
theorem b4 : "c1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwD".toByteArray.size = 200 := by decide +kernel
theorem b5 : "NAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAy".toByteArray.size = 200 := by decide +kernel
theorem b6 : "zxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNN".toByteArray.size = 200 := by decide +kernel
theorem b7 : "ABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU2AZbUpsACk9iIbo+WNzYMEB8DVwDKrmrgUaKwjlxbgLigfjQAQGwGTAKsyU2ANIr8If".toByteArray.size = 200 := by decide +kernel
theorem b8 : "qbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sb".toByteArray.size = 200 := by decide +kernel
theorem b9 : "IMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU".toByteArray.size = 200 := by decide +kernel
theorem b10 : "BPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZ".toByteArray.size = 200 := by decide +kernel
theorem b11 : "Vc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mw".toByteArray.size = 200 := by decide +kernel
theorem b12 : "FNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsA".toByteArray.size = 200 := by decide +kernel
theorem b13 : "yzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPN".toByteArray.size = 200 := by decide +kernel
theorem b14 : "NABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJeU2AZbUpsACk9iIbo+WNzYMEB8DVwDKrmrgUaKwjlxbgLigfjQAQGwGTAKsyU2ANIr8I".toByteArray.size = 200 := by decide +kernel
theorem b15 : "VqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauAZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+s".toByteArray.size = 200 := by decide +kernel
theorem b16 : "bIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16mwDLPGrgWTqGcsBAQPxoAA7SmwDKqlNgGTqGEEAz7QACvVNgGXgqbAAsGAXFA/GgAgJe".toByteArray.size = 200 := by decide +kernel
theorem b17 : "cBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdepsAyzxq4Fk6hnsB+NAAHaU2AZVUpsAydQwggPxoABLymwDLWFNgARHVqyldjZBggPgauA".toByteArray.size = 200 := by decide +kernel
theorem b18 : "ZVc1cCjRWEcucBPrGyDBAfA1cAyq5q4FGisI5c9jkGjJCmgAgNoU2AZbYxcAyIZwE+sbIMEB+6mwDK8GrgWTDPYiJyrgCAgfhwAAEAH4cAACAoAQED8aAA800AFAgAQA/GgAPNNABQIAREOgFxQPxoABADFwCIEAIiHR2AgIH40AB8ZoAKBAEjUMIiA/tjeDUoMEB16m".toByteArray.size = 200 := by decide +kernel
theorem b19 : "SFNAAJeU2AZa8psAAgYAfjQAQEvKbAMteU2AAQM9jkGjJCmgAgK2U2AZeQpsAaRYYIucBPrGyDBAZGpsAy9Zq4E0i6kRc9iInKuAAgIH40AB5poAKBAAgQnUisbiwYICvVNgGXVqbAAnEsss5V7AAfjQAHmmgAoEAAEBTkGjJCmgAGXKbAMuqYuAZOoYBPrGyDBAdeps".toByteArray.size = 200 := by decide +kernel
