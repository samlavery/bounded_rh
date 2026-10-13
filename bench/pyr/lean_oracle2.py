"""Lean text of the pyramid lower-bound oracle, version 2 (fewer kernel steps): `Bool.rec` selections, `let`s instead of
`forceN`, level from a 4-bit bit-length table, and a cover whose next start is the end of the block just read
(so the block size `t` needs no alignment proof).  Pyramid lower-bound table adapted from five-point-pyramid-2 by
typh (Apache-2.0)."""

def sel(c, t, e):
    """bif c then t else e, as one Bool.rec"""
    return f"Bool.rec (motive := fun _ => ℕ) ({e}) ({t}) ({c})"

def oracle_defs2(P, TB="T"):
    PB, KT, EB, EM, PE, FUEL, MAXA = P.PB, P.KT, P.EB, P.EM, P.PE, P.FUEL, P.MAXA
    # 4-bit bit-length table of 0..255
    BL8 = 0
    for x in range(256): BL8 |= x.bit_length() << (4 * x)
    al = []
    for t in range(1, MAXA + 1):
        nxt = "0" if t == 1 else f"alignK{t - 1} g ib"
        al.append(f"def alignK{t} (g ib : ℕ) : ℕ :=\n  " + sel(f"Nat.beq (Nat.land g {(1 << t) - 1}) 0", sel(f"Nat.ble (Nat.add g {1 << t}) (Nat.add ib 1)", str(t), nxt), nxt))
    return f"""
/-- field `i` (EB = {EB} bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul {EB} i)) {EM}

/-- the entry for level-`l` cell `i` (`l ≤ {PB}`) from the constant `X` of its block `j`: the entry of its ancestor
at level `max l r`, `r` the block's finest stored level -/
def entB (X l i j : ℕ) : ℕ :=
  let r := Nat.land X 31
  let kk := {sel("Nat.ble l r", "r", "l")}
  let d := Nat.sub {PB} kk
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for level-`l` cell `i` -/
def entry (T : PyrTab) (l i : ℕ) : ℕ :=
  {sel(f"Nat.blt {KT} l", "0", sel(f"Nat.blt {PB} l", f"fld T.top (Nat.add (Nat.shiftLeft 1 (Nat.sub {KT} l)) i)", f"let j := Nat.shiftRight i (Nat.sub {PB} l); entB (T.bk j) l i j"))}

{chr(10).join(al)}

def nmin (a b : ℕ) : ℕ := {sel("Nat.ble a b", "a", "b")}

/-- min of the entries over a cover of the level-`k` cells `g .. ib` by blocks of `2^t` cells (`t` from `alignK`),
each read through its own entry at level `k + t`; the next block starts where the one just read ends -/
def dcov (T : PyrTab) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      let t := alignK{MAXA} g ib
      let h := Nat.shiftRight g t
      let v := entry T (Nat.add k t) h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      {sel("Nat.blt ib g'", "v", "nmin v (ih g')")})
    fuel

/-- bit length of `x < 2^16` from a 4-bit table -/
def BL8 : ℕ := {BL8}
def blen (x : ℕ) : ℕ := {sel("Nat.ble 256 x", "Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)", "Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15")}

/-- the lower-bound oracle: `lb T lo hi / {P.U}` bounds `wfun` below on `[lo, hi] / 2^15` -/
def lb (T : PyrTab) (lo hi : ℕ) : ℕ :=
  {sel(f"Nat.ble hi lo || Nat.blt {1 << KT} hi", "0", f"let k := blen (Nat.shiftRight (Nat.sub hi lo) {PE}); dcov T k (Nat.shiftRight (Nat.sub hi 1) k) {FUEL} (Nat.shiftRight lo k)")}
"""
