"""Lean text of the pyramid lower-bound oracle, version 3: kernel primitives only (`Nat.add`, `Nat.sub`, `Nat.ble`,
`Nat.beq`, `Nat.land`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.mul`), `Bool.rec` selections, no `Nat.blt`, no
notation, table passed as `(top : ℕ) (bk : ℕ → ℕ)`.  Pyramid lower-bound table adapted from five-point-pyramid-2
by typh (Apache-2.0)."""

def sel(c, t, e):
    """if c then t else e, as one Bool.rec"""
    return f"Bool.rec (motive := fun _ => ℕ) ({e}) ({t}) ({c})"

def oracle_defs3(P, FORCE=False):
    PB, KT, EB, EM, PE, FUEL, MAXA = P.PB, P.KT, P.EB, P.EM, P.PE, P.FUEL, P.MAXA
    BL8 = 0
    for x in range(256): BL8 |= x.bit_length() << (4 * x)
    al = []
    for t in range(1, MAXA + 1):
        nxt = "0" if t == 1 else f"alignK{t - 1} g ib"
        al.append(f"def alignK{t} (g ib : ℕ) : ℕ :=\n  " + sel(f"Nat.beq (Nat.land g {(1 << t) - 1}) 0", sel(f"Nat.ble (Nat.add g {1 << t}) (Nat.add ib 1)", str(t), nxt), nxt))
    FR = "def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a\n" if FORCE else ""
    return FR + f"""
/-- field `i` ({EB} bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul {EB} i)) {EM}

/-- the entry for level-`l` cell `i` (`l ≤ {PB}`) from the constant `X` of its block `j`: the entry of its ancestor
at level `max l r`, `r` the block's finest stored level -/
def entB (X l i j : ℕ) : ℕ :=
  let r := Nat.land X 31
  let kk := {sel("Nat.ble l r", "r", "l")}
  let d := Nat.sub {PB} kk
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for level-`l` cell `i` -/
def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  {sel(f"Nat.ble {PB + 1} l", sel(f"Nat.ble {KT + 1} l", "0", f"fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub {KT} l)) i)"), (f"forceR (Nat.shiftRight i (Nat.sub {PB} l)) fun j => entB (bk j) l i j" if FORCE else f"let j := Nat.shiftRight i (Nat.sub {PB} l); entB (bk j) l i j"))}

{chr(10).join(al)}

def nmin (a b : ℕ) : ℕ := {sel("Nat.ble a b", "a", "b")}

/-- min of the entries over a cover of the level-`k` cells `g .. ib` by blocks of `2^t` cells (`t` from `alignK`),
each read through its own entry at level `k + t`; the next block starts where the one just read ends -/
def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      let t := alignK{MAXA} g ib
      let h := Nat.shiftRight g t
      let v := {"forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h" if FORCE else "entry top bk (Nat.add k t) h"}
      let g' := Nat.shiftLeft (Nat.add h 1) t
      {sel("Nat.ble g' ib", "nmin v (ih g')", "v")})
    fuel

/-- bit length of `x < 2^16` from a 4-bit table -/
def BL8 : ℕ := {BL8}
def blen (x : ℕ) : ℕ := {sel("Nat.ble 256 x", "Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)", "Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15")}

/-- the lower-bound oracle: `lb top bk lo hi / {P.U}` bounds `wfun` below on `[lo, hi] / 2^15` -/
def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  {sel("Nat.ble hi lo", "0", sel(f"Nat.ble {(1 << KT) + 1} hi", "0", f"let k := blen (Nat.shiftRight (Nat.sub hi lo) {PE}); dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) {FUEL} (Nat.shiftRight lo k)"))}
"""
