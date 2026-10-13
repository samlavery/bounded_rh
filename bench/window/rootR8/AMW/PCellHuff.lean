import AMW.PCellRoot

/-! ###### polytope cells: the canonical-Huffman field decoder (bridge-port; spec mvt-engine's HUFF.md)

A canonical table is two numbers: `cs`, the count of each code length from length 0 (16-bit fields), and `sy`, the
symbols in table order (16-bit fields).  `hdec` reads a codeword MSB first (the first bit read is the code's most
significant bit) from a 32-bit window of the walk, comparing at each length against the first code of that length, and
returns `symbol + 2^16 · length`.  A one-entry table (length 0) reads no bit.  Every decoded field only feeds a checked
leaf or a split (whose soundness holds for any value), so the decoder carries no proof. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr

/-- one length of the canonical decode: return the symbol when `code − first < cnt`, else read the next bit -/
def hstep (sy : ℕ) (ih : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (code first base cs y ln : ℕ) : ℕ :=
  forceR (Nat.land cs 65535) fun cnt => forceR (Nat.sub code first) fun d =>
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.add (Nat.add code code) (Nat.land y 1)) fun c => forceR (Nat.shiftLeft (Nat.add first cnt) 1) fun f =>
      forceR (Nat.add base cnt) fun b => forceR (Nat.shiftRight cs 16) fun cs' => forceR (Nat.shiftRight y 1) fun y' =>
      ih c f b cs' y' (Nat.add ln 1))
    (Nat.add (Nat.land (Nat.shiftRight sy (Nat.shiftLeft (Nat.add base d) 4)) 65535) (Nat.shiftLeft ln 16))
    (Nat.blt d cnt)

/-- the codeword of table `(cs, sy)` at bit `o` of `w`: `symbol + 2^16 · length` (`0` when no codeword of length ≤ 32) -/
def hdec (cs sy w o : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (fun _ _ _ _ _ _ => 0) (fun _ ih => hstep sy ih) 33 0 0 0 cs
    (Nat.land (Nat.shiftRight w o) 4294967295) 0

/-- the decode with a lookup: `lut`'s entry at the next bits (walk order, masked by `km = 2^kb − 1`; 24-bit entries
`symbol + 2^16 · (length + 1)`) when a codeword of length ≤ `kb` is a prefix of them, else (entry `0`) `hdec` -/
def hdecL (km lut cs sy w o : ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight lut (Nat.mul 24 (Nat.land (Nat.shiftRight w o) km))) 16777215) fun e =>
  Bool.rec (motive := fun _ => ℕ) (Nat.sub e 65536) (hdec cs sy w o) (Nat.beq e 0)

/-- one minorant term (HUFF.md §5.1) after its codeword `sl = symbol + 2^16 · length` read at `o` (symbol
`κ · 2^14 + j1 · 2^7 + j2`): `λ` (`lb` bits if `κ = 2`, `λ − 1` in `lb − 1` bits if `κ = 3`) as the weight
`m = λ · 2^(10 − lb)` of 1024; grid points on `[L, U]` only where the kind reads them; then the continuation with
`κ, m, p, r` and the next offset -/
def dec4S (lb sl w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.land sl 65535) 14) fun a => forceR (Nat.add o (Nat.shiftRight sl 16)) fun o1 =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.add (Nat.land (Nat.shiftRight w o1) (Nat.sub (Nat.shiftLeft 1 (Nat.sub lb 1)) 1)) 1) (Nat.beq a 3))
      (Nat.land (Nat.shiftRight w o1) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) o1 (Nat.add o1 (Nat.sub lb 1)) (Nat.beq a 3))
      (Nat.add o1 lb) (Nat.beq a 2)) fun o' =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight sl 7) 127)) 0 (Nat.beq a 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land sl 127)) (Nat.beq a 3)) fun r =>
  k a (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

end AMW.Cert.PCell
