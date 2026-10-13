import AMW.PCellIV

/-! ###### loop-free walk codes, round 13b/13c (am-cert microbenchmark)

* K2 (ranked kind flags per term position, ranks `r0 … r3`): `[1]` = `r0`, `[0][1]` = `r1`, `[0][0][x]` = `r2` (x = 0) or `r3`.
* G (point index through a table `JT`, 7 bits per entry, packed): a `jw`-bit field; with escape (`esc ≠ 0`), the value
  `esc` is followed by the index as 7 raw bits.
The fields after the kind keep the fixed order `j1`, `j2`, `λ` (`lb` raw bits).  As `dec4F`, nothing here needs a proof. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the field length after the kind (7-bit indices) -/
def plenK7 (lb a : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add 14 lb) (Nat.beq a 3))
    (Nat.add 7 lb) (Nat.beq a 2)) 7 (Nat.beq a 1)

/-- one point index through the table at bit `f`: packed `index + 2^24 · next bit` -/
def jtab (JT jw esc w f : ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight w f) (Nat.sub (Nat.shiftLeft 1 jw) 1)) fun v =>
  Bool.rec (motive := fun _ => ℕ)
    (Nat.add (Nat.land (Nat.shiftRight JT (Nat.mul 7 v)) 127) (Nat.shiftLeft (Nat.add f jw) 24))
    (Nat.add (Nat.land (Nat.shiftRight w (Nat.add f jw)) 127) (Nat.shiftLeft (Nat.add (Nat.add f jw) 7) 24))
    (Bool.and (Nat.blt 0 esc) (Nat.beq v esc))

/-- control: the fixed layout through the same packed kind/start as the variants below -/
def dec4P (lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Nat.add (Nat.land (Nat.shiftRight w o) 3) (Nat.shiftLeft (Nat.add o 2) 2)) fun af =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 14)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 3))
      (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.shiftRight af 2)) 127)) 0
      (Nat.beq (Nat.land af 3) 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) 127))
      (Nat.beq (Nat.land af 3) 3)) fun r =>
  forceR (Nat.add (Nat.shiftRight af 2) (plenK7 lb (Nat.land af 3))) fun o' => k (Nat.land af 3) (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

/-- K2 kind, raw indices (inline) -/
def dec4R (r0 r1 r2 r3 lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (Nat.add r2 (Nat.shiftLeft (Nat.add o 3) 2)) (Nat.add r3 (Nat.shiftLeft (Nat.add o 3) 2))
        (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 2)) 1) 1))
      (Nat.add r1 (Nat.shiftLeft (Nat.add o 2) 2)) (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 1)) 1) 1))
    (Nat.add r0 (Nat.shiftLeft (Nat.add o 1) 2)) (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)) fun af =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 14)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 3))
      (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq (Nat.land af 3) 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.shiftRight af 2)) 127)) 0
      (Nat.beq (Nat.land af 3) 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add (Nat.shiftRight af 2) 7)) 127))
      (Nat.beq (Nat.land af 3) 3)) fun r =>
  forceR (Nat.add (Nat.shiftRight af 2) (plenK7 lb (Nat.land af 3))) fun o' => k (Nat.land af 3) (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

/-- fixed kind, table indices (inline) -/
def dec4G (JT jw esc lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Nat.add (Nat.land (Nat.shiftRight w o) 3) (Nat.shiftLeft (Nat.add o 2) 2)) fun af =>
  forceR (Bool.rec (motive := fun _ => ℕ) (jtab JT jw esc w (Nat.shiftRight af 2)) (Nat.shiftLeft (Nat.shiftRight af 2) 24)
      (Nat.beq (Nat.land af 3) 0)) fun v1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft (Nat.shiftRight v1 24) 24) (jtab JT jw esc w (Nat.shiftRight v1 24))
      (Nat.beq (Nat.land af 3) 3)) fun v2 =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w (Nat.shiftRight v2 24)) (Nat.sub (Nat.shiftLeft 1 lb) 1))
      (Nat.ble 2 (Nat.land af 3))) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land v1 16777215)) 0 (Nat.beq (Nat.land af 3) 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land v2 16777215)) (Nat.beq (Nat.land af 3) 3)) fun r =>
  k (Nat.land af 3) (Nat.shiftLeft lam (Nat.sub 10 lb)) p r
    (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight v2 24) (Nat.add (Nat.shiftRight v2 24) lb) (Nat.ble 2 (Nat.land af 3)))

/-- K2 kind, table indices (inline) -/
def dec4RG (r0 r1 r2 r3 JT jw esc lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (Nat.add r2 (Nat.shiftLeft (Nat.add o 3) 2)) (Nat.add r3 (Nat.shiftLeft (Nat.add o 3) 2))
        (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 2)) 1) 1))
      (Nat.add r1 (Nat.shiftLeft (Nat.add o 2) 2)) (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 1)) 1) 1))
    (Nat.add r0 (Nat.shiftLeft (Nat.add o 1) 2)) (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)) fun af =>
  forceR (Bool.rec (motive := fun _ => ℕ) (jtab JT jw esc w (Nat.shiftRight af 2)) (Nat.shiftLeft (Nat.shiftRight af 2) 24)
      (Nat.beq (Nat.land af 3) 0)) fun v1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft (Nat.shiftRight v1 24) 24) (jtab JT jw esc w (Nat.shiftRight v1 24))
      (Nat.beq (Nat.land af 3) 3)) fun v2 =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w (Nat.shiftRight v2 24)) (Nat.sub (Nat.shiftLeft 1 lb) 1))
      (Nat.ble 2 (Nat.land af 3))) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land v1 16777215)) 0 (Nat.beq (Nat.land af 3) 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land v2 16777215)) (Nat.beq (Nat.land af 3) 3)) fun r =>
  k (Nat.land af 3) (Nat.shiftLeft lam (Nat.sub 10 lb)) p r
    (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight v2 24) (Nat.add (Nat.shiftRight v2 24) lb) (Nat.ble 2 (Nat.land af 3)))

/-- K2 in `dec4F`'s own style: the kind and the field start forced separately (no packed extraction) -/
def dec4R2 (r0 r1 r2 r3 lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) r2 r3 (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 2)) 1) 1))
        r1 (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 1)) 1) 1))
      r0 (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)) fun a =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (Nat.add o 3) (Nat.add o 2) (Nat.beq (Nat.land (Nat.shiftRight w (Nat.add o 1)) 1) 1))
      (Nat.add o 1) (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)) fun f =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w (Nat.add f 14)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 3))
      (Nat.land (Nat.shiftRight w (Nat.add f 7)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w f) 127)) 0 (Nat.beq a 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add f 7)) 127)) (Nat.beq a 3)) fun r =>
  forceR (Nat.add f (plenK7 lb a)) fun o' => k a (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

end AMW.Cert.PCell

end
