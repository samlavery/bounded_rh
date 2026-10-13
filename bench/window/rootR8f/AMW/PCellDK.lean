import AMW.PCellIV

/-! ###### the dominant-kind flag (am-cert, bytes lever: loop-free kind code)

Each term position `t` has a dominant kind `d_t` (the most frequent there).  A term's kind is written as one flag bit:
`0` = the dominant kind; `1` = followed by the kind as 2 raw bits (value LSB-first).  The term's fields follow unchanged
(`j1` 7 bits if κ ≥ 1, `j2` 7 bits if κ = 3, `λ` `lb` bits if κ ≥ 2).  `dec4D` is `dec4F` with that kind read, with the
same number of forced steps (the kind and the field start are forced as one packed value). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the field length after the kind: `0`, `7`, `7 + lb`, `14 + lb` -/
def plenK (lb a : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add 14 lb) (Nat.beq a 3))
    (Nat.add 7 lb) (Nat.beq a 2)) 7 (Nat.beq a 1)

/-- one term under the dominant-kind flag (dominant kind `d`): `k a m p r o'` as `dec4F` -/
def dec4D (d lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Nat.add (Nat.land (Nat.shiftRight w (Nat.add o 1)) 3) (Nat.shiftLeft (Nat.add o 3) 2))
      (Nat.add d (Nat.shiftLeft (Nat.add o 1) 2))
      (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 0)) fun af =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 14)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 3))
      (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.shiftRight af 2)) 127)) 0
      (Nat.beq (Nat.land af 3) 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) 127))
      (Nat.beq (Nat.land af 3) 3)) fun r =>
  forceR (Nat.add (Nat.shiftRight af 2) (plenK lb (Nat.land af 3))) fun o' => k (Nat.land af 3) (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

end AMW.Cert.PCell

end
