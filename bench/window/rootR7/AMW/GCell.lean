import AMW.GIv

/-!
# AMW/GCell — the integer cell evaluator for the AM kernel (definitions; stage G)

On the cell `[LN, UN] / SC` the evaluator encloses `k = kfunAM`, `k' = k1AM`, `k'' = k2AM` (scale `DZ = 10¹⁵`):
  `k   = −N/E + σ·(sin πx · F₀) + ρ·B₀`,
  `k'  = π M/E² + ρ·(cos πx · F₀) + σ·(sin πx · F₁) + ρ·B₁`,
  `k'' = −π² P/E³ − τ·(sin πx · F₀) + 2ρ·(cos πx · F₁) + σ·(sin πx · F₂) + ρ·B₂`,
with `E = −D = 2(πx)² − 1`, `ρ = 1/(√2 sin(√2/2))`, `σ = ρ/π`, `τ = ρπ`, the far sums
`F_n = Σ_{j ≠ j₀} c_j (−1)^j m_j^(n)(x) + c_{j₀} (−1)^{j₀} h_{j₀}^(n)(x)`, `m_j = x/(x² − j²)`, `h_j = 1/(2(x + j))`
(each term monotone on the cell with a fixed sign, so it is read at the endpoints), and the near pole `j₀ = k/2`:
`B_n = c_{j₀}/2 · πⁿ · sincⁿ(π(x − j₀))` by Taylor polynomials at `t = π|x − j₀| ≤ 1`.
The trigonometric base (cos/sin of `πx` through the nearest half-integer anchor `k/2`) is the Montgomery–Taylor cell's.
An exact replica of `bench/window/amg/amk.py` (`cellK2`). -/

namespace AMW.G

def SC : ℕ := 32768
def DZ2 : ℕ := 500000000000000
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
def E20 : ℕ := 100000000000000000000
def ERRD : ℕ := 2262000
def E9 : ℕ := 1000000000
def CDEN : ℕ := Nat.mul 3628800 (Nat.pow DZ 9)
def SDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 10)
def SCDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)
def S1DEN : ℕ := Nat.mul 3991680 (Nat.pow DZ 8)
def S2DEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)

/-- `DZ^k` -/
def DZp (k : ℕ) : ℕ := Nat.pow DZ k

def cosP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 3628800 (DZp 10)) (Nat.mul (Nat.mul 151200 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))
def cosN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1814400 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 5040 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def sinP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 39916800 T) (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 5)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 9)) (DZp 2))
def sinN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 3)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 7)) (DZp 4))) (Nat.pow T 11)
def scP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 39916800 (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 8)) (DZp 2))
def scN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def s1P (T : ℕ) : ℕ := Nat.add (Nat.mul (Nat.mul 133056 (Nat.pow T 3)) (DZp 6)) (Nat.mul (Nat.mul 88 (Nat.pow T 7)) (DZp 2))
def s1N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1330560 T) (DZp 8)) (Nat.mul (Nat.mul 4752 (Nat.pow T 5)) (DZp 4))) (Nat.pow T 9)
def s2P (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 3991680 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 6160 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def s2N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 13305600 (DZp 10)) (Nat.mul (Nat.mul 237600 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))

/-- constants at scale `DZ` -/
def PIC : IV := IV.ofN 3141592653589793 3141592653589794
def PI2C : IV := IV.ofN 9869604401089357 9869604401089364
def GAM0 : ℕ := 1654998581400000
def GAM1 : ℕ := 1654998603600000
def G1C : IV := IV.ofN 2654998581400000 2654998603600000
def G2C : IV := IV.ofN 4309997162800000 4309997207200000
def RHOC : IV := IV.ofN 1088464550157349 1088464557864635
def SIGC : IV := IV.ofN 346469027075676 346469029528983
def TAUC : IV := IV.ofN 3419512234467246 3419512258680401

/-- `(j, |c_j (−1)^j| · 10⁹, c_j (−1)^j < 0)` for `j = 1, …, 12` -/
def CE : List (ℕ × ℕ × Bool) :=
  [(1, 12078945, true), (2, 13283088, true), (3, 3963606, true), (4, 6042520, false), (5, 1347463, false),
   (6, 6607159, false), (7, 7899775, false), (8, 5702398, false), (9, 5766402, false), (10, 879305, true),
   (11, 543568, true), (12, 412815, true)]
/-- `(|c_j| · 10⁹, c_j < 0)` -/
def CJ (j : ℕ) : ℕ × Bool :=
  match j with
  | 1 => (12078945, false) | 2 => (13283088, true) | 3 => (3963606, false) | 4 => (6042520, false)
  | 5 => (1347463, true) | 6 => (6607159, false) | 7 => (7899775, true) | 8 => (5702398, false)
  | 9 => (5766402, true) | 10 => (879305, true) | 11 => (543568, false) | 12 => (412815, true) | _ => (0, false)

/-- four accumulators of a far sum: `lo = pl − nh`, `hi = ph − nl` -/
structure Acc where
  (pl ph nl nh : ℕ)

def Acc.put (a : Acc) (ng : Bool) (e m0 m1 : ℕ) : Acc :=
  Bool.rec (motive := fun _ => Acc) ⟨Nat.add a.pl (Nat.mul e m0), Nat.add a.ph (Nat.mul e m1), a.nl, a.nh⟩
    ⟨a.pl, a.ph, Nat.add a.nl (Nat.mul e m0), Nat.add a.nh (Nat.mul e m1)⟩ ng

/-- numerators and denominators of `|m^(n)|` at `X` (`X2 = X²`, `J2 = J²`, `d = |X² − J²|`) and of `|h^(n)|` at `Y = X + J` -/
def mnum (n X X2 J2 : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (Nat.mul X (DZp 2))
    (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul (Nat.add X2 J2) (DZp 3))
      (fun _ _ => Nat.mul (Nat.mul (Nat.mul 2 X) (Nat.add X2 (Nat.mul 3 J2))) (DZp 4)) m) n
def hden (n Y : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 Y)
    (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 (Nat.mul Y Y)) (fun _ _ => Nat.pow Y 3) m) n
/-- the value of `m^(n)` is negative (`ab` = above the pole) / of `h^(n)` -/
def mneg (n : ℕ) (ab : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (!ab) true (Nat.beq n 1)
def hneg (n : ℕ) : Bool := Nat.beq n 1

/-- the far term of `j` added to the accumulators -/
def farJ (n k XL XU XL2 XU2 : ℕ) (a : Acc) (j e : ℕ) (sg : Bool) : Acc :=
  let J := Nat.mul j DZ
  let J2 := Nat.mul J J
  Bool.rec (motive := fun _ => Acc)
    (Bool.rec (motive := fun _ => Acc)
      (a.put (xor sg (mneg n false)) e (Nat.div (mnum n XL XL2 J2) (Nat.pow (Nat.sub J2 XL2) (Nat.succ n)))
        (ndivc (mnum n XU XU2 J2) (Nat.pow (Nat.sub J2 XU2) (Nat.succ n))))
      (a.put (xor sg (mneg n true)) e (Nat.div (mnum n XU XU2 J2) (Nat.pow (Nat.sub XU2 J2) (Nat.succ n)))
        (ndivc (mnum n XL XL2 J2) (Nat.pow (Nat.sub XL2 J2) (Nat.succ n))))
      (Nat.blt (Nat.mul 2 j) k))
    (a.put (xor sg (hneg n)) e (Nat.div (DZp (Nat.add n 2)) (hden n (Nat.add XU J)))
      (ndivc (DZp (Nat.add n 2)) (hden n (Nat.add XL J))))
    (Nat.beq (Nat.mul 2 j) k)

def farAcc (n k XL XU XL2 XU2 : ℕ) : List (ℕ × ℕ × Bool) → Acc → Acc
  | [], a => a
  | (j, e, sg) :: rest, a => farAcc n k XL XU XL2 XU2 rest (farJ n k XL XU XL2 XU2 a j e sg)

/-- a cell `[LN, UN] / SC` -/
structure CellA where
  (LN UN : ℕ)

namespace CellA
def k (c : CellA) : ℕ := Nat.div (Nat.add (Nat.mul 2 (Nat.add c.LN c.UN)) SC) (Nat.mul 2 SC)
def side (c : CellA) : Bool := Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)
def LLO (c : CellA) : ℕ := Nat.div (Nat.mul c.LN DZ) SC
def UHI (c : CellA) : ℕ := ndivc (Nat.mul c.UN DZ) SC
def AD (c : CellA) : ℕ := Nat.mul c.k DZ2
def RLO (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.UHI) (Nat.sub c.LLO c.AD) c.side
def RHI (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.LLO) (Nat.sub c.UHI c.AD) c.side
def TLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.RLO) E20
def TUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.RHI) E20
/-- `cos θ`, `sin θ`, `θ = π |x − k/2|` -/
def CI (c : CellA) : IV :=
  ⟨⟨Nat.div (Nat.sub (cosP c.TUZ) (cosN c.TUZ)) CDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (cosP c.TLZ) (cosN c.TLZ)) CDEN) ERRD, 0⟩⟩
def SI (c : CellA) : IV :=
  ⟨⟨Nat.div (Nat.sub (sinP c.TLZ) (sinN c.TLZ)) SDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (sinP c.TUZ) (sinN c.TUZ)) SDEN) ERRD, 0⟩⟩
def km4 (c : CellA) : ℕ := Nat.mod c.k 4
/-- `cos (πx)`, `sin (πx)` -/
def CX (c : CellA) : IV :=
  Bool.rec (motive := fun _ => IV)
    (Bool.rec (motive := fun _ => IV)
      (Bool.rec (motive := fun _ => IV) (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) c.CI.neg (Nat.beq c.km4 2))
      (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 1))
    c.CI (Nat.beq c.km4 0)
def SX (c : CellA) : IV :=
  Bool.rec (motive := fun _ => IV)
    (Bool.rec (motive := fun _ => IV)
      (Bool.rec (motive := fun _ => IV) c.CI.neg (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 2))
      c.CI (Nat.beq c.km4 1))
    (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) (Nat.beq c.km4 0)
def BLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.LLO) E20
def BUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.UHI) E20
def BI (c : CellA) : IV := IV.ofN c.BLZ c.BUZ
def PG (c : CellA) : IV := IV.ofN (Nat.div (Nat.mul GAM0 c.BLZ) DZ) (ndivc (Nat.mul GAM1 c.BUZ) DZ)
def NI (c : CellA) : IV := c.CX.sub (IV.mulc c.PG c.SX)
def E0 (c : CellA) : ℕ := Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ
def E1 (c : CellA) : ℕ := Nat.sub (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ
def EI (c : CellA) : IV := IV.ofN c.E0 c.E1
/-- the checked conditions -/
def ok (c : CellA) : Bool :=
  Nat.ble c.LN c.UN && Nat.ble c.TUZ DZ
    && Bool.rec (motive := fun _ => Bool) (Nat.ble (Nat.mul 2 c.UN) (Nat.mul c.k SC)) (Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)) c.side
    && Nat.blt 0 c.E0
/-- the far sum `F_n` -/
def FA (c : CellA) (n : ℕ) : IV :=
  let a := farAcc n c.k c.LLO c.UHI (Nat.mul c.LLO c.LLO) (Nat.mul c.UHI c.UHI) CE ⟨0, 0, 0, 0⟩
  IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9
/-- the near pole `j₀ = k/2` -/
def nearOn (c : CellA) : Bool := Nat.beq (Nat.mod c.k 2) 0 && Nat.ble 2 c.k && Nat.ble c.k 24
def S0 (c : CellA) : IV :=
  ⟨(SZ.fl ⟨scP c.TLZ, scN c.TUZ⟩ SCDEN).sub (SZ.ofN ERRD), (SZ.ce ⟨scP c.TUZ, scN c.TLZ⟩ SCDEN).add (SZ.ofN ERRD)⟩
def G1 (c : CellA) : IV :=
  ⟨(SZ.fl ⟨s1P c.TLZ, s1N c.TUZ⟩ S1DEN).sub (SZ.ofN (Nat.mul 2 ERRD)), (SZ.ce ⟨s1P c.TUZ, s1N c.TLZ⟩ S1DEN).add (SZ.ofN (Nat.mul 2 ERRD))⟩
def G2 (c : CellA) : IV :=
  ⟨(SZ.fl ⟨s2P c.TLZ, s2N c.TUZ⟩ S2DEN).sub (SZ.ofN (Nat.mul 5 ERRD)), (SZ.ce ⟨s2P c.TUZ, s2N c.TLZ⟩ S2DEN).add (SZ.ofN (Nat.mul 5 ERRD))⟩
def j0 (c : CellA) : ℕ := Nat.div c.k 2
def B0 (c : CellA) : IV :=
  Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 c.S0).divn (Nat.mul 2 E9)) c.nearOn
def B1 (c : CellA) : IV :=
  Bool.rec (motive := fun _ => IV) IV.zero
    ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PIC (Bool.rec (motive := fun _ => IV) c.G1.neg c.G1 c.side))).divn (Nat.mul 2 E9))
    c.nearOn
def B2 (c : CellA) : IV :=
  Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PI2C c.G2)).divn (Nat.mul 2 E9)) c.nearOn

def SF0 (c : CellA) : IV := c.SX.mul (c.FA 0)
/-- `k` -/
def K0 (c : CellA) : IV := (c.NI.neg.divp c.E0 c.E1).add ((IV.mulc SIGC c.SF0).add (IV.mulc RHOC c.B0))
/-- `M = Nb·D + 4bN` with `Nb = −((1+2γ) sin b + 2γ b cos b)`, `D = −E` -/
def MI (c : CellA) : IV :=
  (IV.mulc c.EI ((IV.mulc G1C c.SX).add (IV.mulc c.PG c.CX))).add (IV.mulc (c.BI.muln 4) c.NI)
def E2L (c : CellA) : ℕ := Nat.div (Nat.mul c.E0 c.E0) DZ
def E2U (c : CellA) : ℕ := ndivc (Nat.mul c.E1 c.E1) DZ
/-- `k'` -/
def K1 (c : CellA) : IV :=
  (IV.mulc PIC (c.MI.divp c.E2L c.E2U)).add
    (((IV.mulc RHOC (c.CX.mul (c.FA 0))).add (IV.mulc SIGC (c.SX.mul (c.FA 1)))).add (IV.mulc RHOC c.B1))
/-- `N₂ = 2γ b sin b − (1+4γ) cos b`, `P = N₂ E² − 4NE + 8bM` -/
def N2 (c : CellA) : IV := (IV.mulc c.PG c.SX).sub (IV.mulc G2C c.CX)
def E3L (c : CellA) : ℕ := Nat.div (Nat.mul c.E2L c.E0) DZ
def E3U (c : CellA) : ℕ := ndivc (Nat.mul c.E2U c.E1) DZ
def PP (c : CellA) : IV :=
  ((IV.mulc (IV.ofN c.E2L c.E2U) c.N2).sub ((IV.mulc c.EI c.NI).muln 4)).add ((IV.mulc c.BI c.MI).muln 8)
/-- `k''` -/
def K2 (c : CellA) : IV :=
  (IV.mulc PI2C (c.PP.divp c.E3L c.E3U)).neg.add
    ((((IV.mulc RHOC (c.CX.mul (c.FA 1))).muln 2).sub (IV.mulc TAUC c.SF0)).add
      ((IV.mulc SIGC (c.SX.mul (c.FA 2))).add (IV.mulc RHOC c.B2)))

/-- `|k| ≥ KA` -/
def KA (c : CellA) : SZ := SZ.max (SZ.ofN 0) (SZ.max c.K0.lo c.K0.hi.neg)
/-- `w' = 2 k k'` -/
def W1 (c : CellA) : IV := (c.K0.mul c.K1).muln 2
/-- `w''/2 ≥ k'² + k k''` at scale `DZ²` -/
def W2L (c : CellA) : SZ :=
  SZ.add (SZ.mul (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)) (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)))
    ((c.K0.mul c.K2).lo.muln DZ)
end CellA

end AMW.G
