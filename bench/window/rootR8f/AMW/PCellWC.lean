import AMW.PCellIV

/-! ###### walk prefix codes (am-cert, bytes: window-scope's round-13 spec `est/r13/walkcode_spec_*.json`)

The leaf word `w` is read LSB-first (the k-th bit read is bit `o + k`).  A canonical prefix codeword is written MSB-first
(its first bit at the lowest position); symbols in (length, symbol) order; `first[1] = 0`,
`first[l+1] = (first[l] + count[l]) << 1`; the decoder reads `code = 2 code + bit` until `first[l] ≤ code < first[l] + count[l]`.
A table is two literals: the counts `cP` (8 bits per length, length `l + 1` at bits `8l`) and the symbols `sP` (`W` bits each,
canonical order).  The escape symbol `esc` (= the alphabet size) is followed by the symbol as a raw field of `rb` bits.
Results are packed `symbol + 2^24 · next bit`.  Nothing here needs a proof: the decoded fields feed the checked leaf, which
is sound for any value (as `dec4F`). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the canonical decode loop (fuel = the maximum length); state: length index `l`, `code`, `first`, `off`, bit `o` -/
def hcLoop (cP sP W w : ℕ) (fuel : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (fun _ _ _ _ o => Nat.shiftLeft o 24)
    (fun _ ih l code first off o =>
      forceR (Nat.add (Nat.add code code) (Nat.land (Nat.shiftRight w o) 1)) fun c =>
      forceR (Nat.land (Nat.shiftRight cP (Nat.mul 8 l)) 255) fun n =>
      Bool.rec (motive := fun _ => ℕ)
        (ih (Nat.add l 1) c (Nat.shiftLeft (Nat.add first n) 1) (Nat.add off n) (Nat.add o 1))
        (Nat.add (Nat.land (Nat.shiftRight sP (Nat.mul W (Nat.sub (Nat.add off c) first))) (Nat.sub (Nat.shiftLeft 1 W) 1))
          (Nat.shiftLeft (Nat.add o 1) 24))
        (Nat.ble first c && Nat.blt c (Nat.add first n)))
    fuel

/-- one codeword at bit `o`, with the escape's raw field: `symbol + 2^24 · next bit` -/
def hcDec (cP sP W esc rb w o : ℕ) : ℕ :=
  forceR (hcLoop cP sP W w 15 0 0 0 0 o) fun v =>
  Bool.rec (motive := fun _ => ℕ) v
    (Nat.add (Nat.land (Nat.shiftRight w (Nat.shiftRight v 24)) (Nat.sub (Nat.shiftLeft 1 rb) 1))
      (Nat.shiftLeft (Nat.add (Nat.shiftRight v 24) rb) 24))
    (Nat.beq (Nat.land v 16777215) esc)

/-- the joint kind code of a term pair (code A: alphabet 16, symbols 5 bits, raw 4): `k (4κa + κb) o'` -/
def decKA (cP sP w o : ℕ) (k : ℕ → ℕ → ℕ) : ℕ :=
  forceR (hcDec cP sP 5 16 4 w o) fun v => k (Nat.land v 16777215) (Nat.shiftRight v 24)

/-- a point index (code B when `cP ≠ 0`: alphabet 128, symbols 8 bits, raw 7; else 7 raw bits): packed -/
def decJ (cP sP w o : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (hcDec cP sP 8 128 7 w o)
    (Nat.add (Nat.land (Nat.shiftRight w o) 127) (Nat.shiftLeft (Nat.add o 7) 24)) (Nat.beq cP 0)

/-- a term's fields after its kind `a` (the spec's order: `j1` if `a ≥ 1`, `j2` if `a = 3`, `λ` (`lb` raw bits) if `a ≥ 2`),
then `k a m p r o'` as `dec4F` (points by `gptF` on the term's range, `m = λ · 2^(10 − lb)`) -/
def decTF (c1 s1 c2 s2 lb w o L U a : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ) (decJ c1 s1 w o) (Nat.shiftLeft o 24) (Nat.beq a 0)) fun v1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft (Nat.shiftRight v1 24) 24) (decJ c2 s2 w (Nat.shiftRight v1 24))
    (Nat.beq a 3)) fun v2 =>
  forceR (Nat.shiftRight v2 24) fun o2 =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w o2) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.ble 2 a))
    fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land v1 16777215)) 0 (Nat.beq a 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land v2 16777215)) (Nat.beq a 3)) fun r =>
  k a (Nat.shiftLeft lam (Nat.sub 10 lb)) p r (Bool.rec (motive := fun _ => ℕ) o2 (Nat.add o2 lb) (Nat.ble 2 a))

end AMW.Cert.PCell

end
