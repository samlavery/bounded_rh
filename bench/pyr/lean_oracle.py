"""Lean text of the pyramid lower-bound oracle `lb` (core Lean, call-by-value through `forceN`), for a Pyr layout.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0)."""

def oracle_defs(P, ns_force="forceN"):
    F = ns_force
    PB, KT, EB, EM, PE, FUEL, MAXA = P.PB, P.KT, P.EB, P.EM, P.PE, P.FUEL, P.MAXA
    al = []
    for t in range(MAXA, 0, -1):
        al.append(f"  {'bif' if t == MAXA else 'else bif'} Nat.beq (Nat.land g {(1 << t) - 1}) 0 then "
                  f"(bif Nat.ble (Nat.add g {1 << t}) (Nat.succ ib) then {t} else {'0' if t == 1 else 'alignK' + str(t - 1) + ' g ib'})")
    # alignK as a chain of small defs (each level tests one alignment)
    alignk = []
    for t in range(1, MAXA + 1):
        nxt = "0" if t == 1 else f"alignK{t - 1} g ib"
        alignk.append(f"def alignK{t} (g ib : ℕ) : ℕ :=\n  bif Nat.beq (Nat.land g {(1 << t) - 1}) 0 && Nat.ble (Nat.add g {1 << t}) (Nat.succ ib) then {t} else {nxt}")
    return f"""
/-- field `i` (EB = {EB} bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul {EB} i)) {EM}

/-- the entry for level-`l` cell `i` (l ≤ {PB}) from the constant `X` of its block `j = i >>> ({PB} - l)`:
the entry of the cell itself if the block is stored that fine, else of its ancestor at the block's finest level -/
def entB (X l i j : ℕ) : ℕ :=
  {F} (Nat.land X 31) fun r =>
  {F} (bif Nat.ble l r then r else l) fun kk =>
  {F} (Nat.sub {PB} kk) fun d =>
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for level-`l` cell `i` -/
def entry (l i : ℕ) : ℕ :=
  bif Nat.blt {KT} l then 0
  else bif Nat.blt {PB} l then fld TOP (Nat.add (Nat.shiftLeft 1 (Nat.sub {KT} l)) i)
  else {F} (Nat.shiftRight i (Nat.sub {PB} l)) fun j => entB (BK j) l i j

{chr(10).join(alignk)}

/-- min of the entries over the aligned cover of the level-`k` cells `g .. ib` (0 if the fuel runs out) -/
def dcov (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      {F} (alignK{MAXA} g ib) fun t =>
      {F} (entry (Nat.add k t) (Nat.shiftRight g t)) fun v =>
      {F} (Nat.add g (Nat.shiftLeft 1 t)) fun g' =>
      bif Nat.blt ib g' then v else {F} (ih g') fun w => bif Nat.ble v w then v else w)
    fuel

/-- bit length of `w < 2^32` -/
def bl0 (w acc : ℕ) : ℕ := bif Nat.ble 1 w then Nat.succ acc else acc
def bl1 (w acc : ℕ) : ℕ := bif Nat.ble 2 w then bl0 (Nat.shiftRight w 1) (Nat.add acc 1) else bl0 w acc
def bl2 (w acc : ℕ) : ℕ := bif Nat.ble 4 w then bl1 (Nat.shiftRight w 2) (Nat.add acc 2) else bl1 w acc
def bl3 (w acc : ℕ) : ℕ := bif Nat.ble 16 w then bl2 (Nat.shiftRight w 4) (Nat.add acc 4) else bl2 w acc
def bl4 (w acc : ℕ) : ℕ := bif Nat.ble 256 w then bl3 (Nat.shiftRight w 8) (Nat.add acc 8) else bl3 w acc
def bitLen (w : ℕ) : ℕ := bif Nat.ble 65536 w then bl4 (Nat.shiftRight w 16) 16 else bl4 w 0

/-- the lower-bound oracle: `lb lo hi / {P.U}` bounds `wfun` below on `[lo, hi] / 2^15` (0 when `hi ≤ lo` or `2^{KT} < hi`) -/
def lb (lo hi : ℕ) : ℕ :=
  bif Nat.ble hi lo || Nat.blt {1 << KT} hi then 0 else
  {F} (Nat.sub (bitLen (Nat.sub hi lo)) {PE}) fun k =>
  {F} (Nat.shiftRight (Nat.sub hi 1) k) fun ib =>
  dcov k ib {FUEL} (Nat.shiftRight lo k)
"""
