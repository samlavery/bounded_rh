import Mathlib

/-! ###### AM-window cell enclosures (definitions; kernel-evaluated)

Intervals of integers at scale `DZ = 10¹⁵`.  On a cell `[LN, UN] / SC` the evaluator encloses
`k(x) = N/D + ρ Σ_{j=1}^{12} c_j (sinc(π(x−j)) + sinc(π(x+j)))/2` and its first two derivatives, with
`N = cos b − 2γ b sin b`, `D = 1 − 2b²`, `b = πx` (the Montgomery–Taylor part), `ρ = a / sin a`, `a = √2/2`. -/

namespace AMW.C

def SC : ℕ := 32768
def KB : ℕ := 1048576
def DZ : ℕ := 1000000000000000
def DZ2 : ℕ := 500000000000000
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
def ERRD : ℕ := 2262000

def ndiv (a b : ℕ) : ℕ := a / b
def ndivc (a b : ℕ) : ℕ := (a + b - 1) / b

def cosP (T : ℕ) : ℕ := 3628800 * DZ^10 + 151200 * T^4 * DZ^6 + 90 * T^8 * DZ^2
def cosN (T : ℕ) : ℕ := 1814400 * T^2 * DZ^8 + 5040 * T^6 * DZ^4 + T^10
def sinP (T : ℕ) : ℕ := 39916800 * T * DZ^10 + 332640 * T^5 * DZ^6 + 110 * T^9 * DZ^2
def sinN (T : ℕ) : ℕ := 6652800 * T^3 * DZ^8 + 7920 * T^7 * DZ^4 + T^11
def cosLo (T : ℕ) : ℕ := ndiv (cosP T - cosN T) (3628800 * DZ^9)
def cosHi (T : ℕ) : ℕ := ndivc (cosP T - cosN T) (3628800 * DZ^9)
def sinLo (T : ℕ) : ℕ := ndiv (sinP T - sinN T) (39916800 * DZ^10)
def sinHi (T : ℕ) : ℕ := ndivc (sinP T - sinN T) (39916800 * DZ^10)

/-- `sinc t`, `s₁ t`, `s₂ t` Taylor polynomials at `T / DZ`: positive and negative parts over a common denominator -/
def scP (T : ℕ) : ℕ := 39916800 * DZ^10 + 332640 * T^4 * DZ^6 + 110 * T^8 * DZ^2
def scN (T : ℕ) : ℕ := 6652800 * T^2 * DZ^8 + 7920 * T^6 * DZ^4 + T^10
def s1P (T : ℕ) : ℕ := 133056 * T^3 * DZ^6 + 88 * T^7 * DZ^2
def s1N (T : ℕ) : ℕ := 1330560 * T * DZ^8 + 4752 * T^5 * DZ^4 + T^9
def s2P (T : ℕ) : ℕ := 3991680 * T^2 * DZ^8 + 6160 * T^6 * DZ^4 + T^10
def s2N (T : ℕ) : ℕ := 13305600 * DZ^10 + 237600 * T^4 * DZ^6 + 90 * T^8 * DZ^2

/-- floor and ceiling of `a / b` (`b > 0`), through natural division (the kernel's `Int.ediv` is slow) -/
def fl (a : ℤ) (b : ℕ) : ℤ := if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else -(((((-a).toNat + b - 1) / b : ℕ)) : ℤ)
def ce (a : ℤ) (b : ℕ) : ℤ := if 0 ≤ a then ((((a.toNat + b - 1) / b : ℕ)) : ℤ) else -((((-a).toNat / b : ℕ)) : ℤ)

def iadd (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 + J.1, I.2 + J.2)
def isub (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 - J.2, I.2 - J.1)
def ineg (I : ℤ × ℤ) : ℤ × ℤ := (-I.2, -I.1)
def iscl (e : ℤ) (I : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ e then (e * I.1, e * I.2) else (e * I.2, e * I.1)
def idivn (I : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := (fl I.1 n, ce I.2 n)
/-- interval product at scale `DZ`, rounded outward -/
def imul (I J : ℤ × ℤ) : ℤ × ℤ :=
  (fl (min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2))) DZ,
   ce (max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2))) DZ)
/-- `I / E` at scale `DZ` for `0 < E.1` -/
def idivp (I E : ℤ × ℤ) : ℤ × ℤ :=
  (if 0 ≤ I.1 then fl (I.1 * DZ) E.2.toNat else fl (I.1 * DZ) E.1.toNat,
   if 0 ≤ I.2 then ce (I.2 * DZ) E.1.toNat else ce (I.2 * DZ) E.2.toNat)

def csA : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k+1 => (-(csA k).2, (csA k).1)

/-- constants at scale `DZ`: π, π², 2γ, 1 + 2γ, 1 + 4γ, ρ, ρ/π, ρπ -/
def PIC : ℤ × ℤ := (3141592653589793, 3141592653589794)
def PI2C : ℤ × ℤ := (9869604401089357, 9869604401089364)
def GAMC : ℤ × ℤ := (1654998581400000, 1654998603600000)
def G1C : ℤ × ℤ := (2654998581400000, 2654998603600000)
def G2C : ℤ × ℤ := (4309997162800000, 4309997207200000)
def RHOC : ℤ × ℤ := (1088464550157349, 1088464557864635)
def SIGC : ℤ × ℤ := (346469027075676, 346469029528983)
def TAUC : ℤ × ℤ := (3419512234467246, 3419512258680401)

/-- `c_j (−1)^j · 10⁹` for `j = 1, …, 12` -/
def CE : List (ℕ × ℤ) :=
  [(1, -12378982), (2, -12602495), (3, -4164033), (4, 5741405), (5, 1724025), (6, 6219280), (7, 8047828),
   (8, 6321519), (9, 5241981), (10, -892658), (11, -560544), (12, -431207)]
/-- `c_j · 10⁹` -/
def CJ (j : ℕ) : ℤ :=
  match j with
  | 1 => 12378982 | 2 => -12602495 | 3 => 4164033 | 4 => 5741405 | 5 => -1724025 | 6 => 6219280
  | 7 => -8047828 | 8 => 6321519 | 9 => -5241981 | 10 => -892658 | 11 => 560544 | 12 => -431207 | _ => 0

structure Cell where
  (key : ℕ) (WN : ℕ)

namespace Cell
def LN (c : Cell) : ℕ := c.key / KB
def UN (c : Cell) : ℕ := c.key % KB
def k (c : Cell) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def side (c : Cell) : Bool := Nat.ble (c.k * SC) (2 * c.LN)
def LLO (c : Cell) : ℕ := ndiv (c.LN * DZ) SC
def UHI (c : Cell) : ℕ := ndivc (c.UN * DZ) SC
def AD (c : Cell) : ℕ := c.k * DZ2
def RLO (c : Cell) : ℕ := if c.side then c.LLO - c.AD else c.AD - c.UHI
def RHI (c : Cell) : ℕ := if c.side then c.UHI - c.AD else c.AD - c.LLO
def TLZ (c : Cell) : ℕ := ndiv (PLN * c.RLO) 100000000000000000000
def TUZ (c : Cell) : ℕ := ndivc (PUN * c.RHI) 100000000000000000000
def CLZ (c : Cell) : ℤ := (cosLo c.TUZ : ℤ) - ERRD
def CUZ (c : Cell) : ℤ := (cosHi c.TLZ : ℤ) + ERRD
def SLZ (c : Cell) : ℤ := (sinLo c.TLZ : ℤ) - ERRD
def SUZ (c : Cell) : ℤ := (sinHi c.TUZ : ℤ) + ERRD
def cA (c : Cell) : ℤ := (csA c.k).1
def sA (c : Cell) : ℤ := (csA c.k).2
/-- `cos (π x)` and `sin (π x)` -/
def CX (c : Cell) : ℤ × ℤ :=
  if c.side then isub (iscl c.cA (c.CLZ, c.CUZ)) (iscl c.sA (c.SLZ, c.SUZ))
  else iadd (iscl c.cA (c.CLZ, c.CUZ)) (iscl c.sA (c.SLZ, c.SUZ))
def SX (c : Cell) : ℤ × ℤ :=
  if c.side then iadd (iscl c.sA (c.CLZ, c.CUZ)) (iscl c.cA (c.SLZ, c.SUZ))
  else isub (iscl c.sA (c.CLZ, c.CUZ)) (iscl c.cA (c.SLZ, c.SUZ))
def BLZ (c : Cell) : ℕ := ndiv (PLN * c.LLO) 100000000000000000000
def BUZ (c : Cell) : ℕ := ndivc (PUN * c.UHI) 100000000000000000000
/-- `b = π x` -/
def BI (c : Cell) : ℤ × ℤ := ((c.BLZ : ℤ), (c.BUZ : ℤ))
/-- `2γ b`, `N`, `E = −D = 2b² − 1` -/
def PG (c : Cell) : ℤ × ℤ := (fl (GAMC.1 * c.BLZ) DZ, ce (GAMC.2 * c.BUZ) DZ)
def NI (c : Cell) : ℤ × ℤ := isub c.CX (imul c.PG c.SX)
def EI (c : Cell) : ℤ × ℤ := (fl (2 * c.BLZ * c.BLZ) DZ - DZ, ce (2 * c.BUZ * c.BUZ) DZ - DZ)
/-- the conditions of the base enclosures -/
def okB (c : Cell) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (0 < c.EI.1)
end Cell

/-- `1 / yⁿ⁺¹` for `y ∈ [Y0, Y1] / DZ`, `0 < Y0` -/
def rpos (Y0 Y1 : ℤ) (n : ℕ) : ℤ × ℤ :=
  (((DZ ^ (n + 2) / Y1.toNat ^ (n + 1) : ℕ) : ℤ), ((ndivc (DZ ^ (n + 2)) (Y0.toNat ^ (n + 1)) : ℕ) : ℤ))
/-- `1 / yⁿ⁺¹` for `y ∈ [−Y1, −Y0] / DZ` -/
def rneg (Y0 Y1 : ℤ) (n : ℕ) : ℤ × ℤ := if n % 2 = 0 then ineg (rpos Y0 Y1 n) else rpos Y0 Y1 n
/-- the far reciprocal powers of `x + j` and `x − j` (the latter dropped at the near pole `2j = k`) -/
def termJ (k : ℕ) (L U : ℤ) (n j : ℕ) : ℤ × ℤ :=
  if 2 * j < k then iadd (rpos (L + j * DZ) (U + j * DZ) n) (rpos (L - j * DZ) (U - j * DZ) n)
  else if k < 2 * j then iadd (rpos (L + j * DZ) (U + j * DZ) n) (rneg (j * DZ - U) (j * DZ - L) n)
  else rpos (L + j * DZ) (U + j * DZ) n
def okJ (k : ℕ) (L U : ℤ) (j : ℕ) : Bool :=
  (!(decide (2 * j < k)) || decide (j * (DZ : ℤ) < L)) && (!(decide (k < 2 * j)) || decide (U < j * (DZ : ℤ)))
def farAcc (k : ℕ) (L U : ℤ) (n : ℕ) : List (ℕ × ℤ) → ℤ × ℤ
  | [] => (0, 0)
  | (j, e) :: rest => iadd (iscl e (termJ k L U n j)) (farAcc k L U n rest)
def okFar (k : ℕ) (L U : ℤ) : List (ℕ × ℤ) → Bool
  | [] => true
  | (j, _) :: rest => okJ k L U j && okFar k L U rest

namespace Cell
/-- `A_n = Σ_far c_j (−1)^j / 2 · y^{−(n+1)}` -/
def FA (c : Cell) (n : ℕ) : ℤ × ℤ := idivn (farAcc c.k c.LLO c.UHI n CE) 2000000000
/-- the near pole `j₀ = k/2` (when `k` is even and `1 ≤ j₀ ≤ 12`) -/
def nearOn (c : Cell) : Bool := c.k % 2 == 0 && Nat.ble 2 c.k && Nat.ble c.k 24
def S0 (c : Cell) : ℤ × ℤ :=
  (fl ((scP c.TLZ : ℤ) - scN c.TUZ) (39916800 * DZ^9) - ERRD, ce ((scP c.TUZ : ℤ) - scN c.TLZ) (39916800 * DZ^9) + ERRD)
def G1 (c : Cell) : ℤ × ℤ :=
  (fl ((s1P c.TLZ : ℤ) - s1N c.TUZ) (3991680 * DZ^8) - 2 * ERRD, ce ((s1P c.TUZ : ℤ) - s1N c.TLZ) (3991680 * DZ^8) + 2 * ERRD)
def G2 (c : Cell) : ℤ × ℤ :=
  (fl ((s2P c.TLZ : ℤ) - s2N c.TUZ) (39916800 * DZ^9) - 5 * ERRD, ce ((s2P c.TUZ : ℤ) - s2N c.TLZ) (39916800 * DZ^9) + 5 * ERRD)
def B0 (c : Cell) : ℤ × ℤ := if c.nearOn then idivn (iscl (CJ (c.k / 2)) c.S0) 2000000000 else (0, 0)
def B1 (c : Cell) : ℤ × ℤ :=
  if c.nearOn then idivn (iscl (CJ (c.k / 2)) (imul PIC (if c.side then c.G1 else ineg c.G1))) 2000000000 else (0, 0)
def B2 (c : Cell) : ℤ × ℤ := if c.nearOn then idivn (iscl (CJ (c.k / 2)) (imul PI2C c.G2)) 2000000000 else (0, 0)
def ok (c : Cell) : Bool := c.okB && okFar c.k c.LLO c.UHI CE

/-- `k` on the cell -/
def K0 (c : Cell) : ℤ × ℤ :=
  iadd (idivp (ineg c.NI) c.EI) (iadd (imul SIGC (imul c.SX (c.FA 0))) (imul RHOC c.B0))
/-- `k'`: `π M / D² + ρ (cos(πx) A₀ − sin(πx) A₁ / π + B₁)` -/
def MI (c : Cell) : ℤ × ℤ :=
  iadd (imul (ineg (iadd (imul G1C c.SX) (imul c.PG c.CX))) (ineg c.EI)) (imul (iscl 4 c.BI) c.NI)
def E2 (c : Cell) : ℤ × ℤ := imul c.EI c.EI
def K1 (c : Cell) : ℤ × ℤ :=
  iadd (imul PIC (idivp c.MI c.E2))
    (iadd (isub (imul RHOC (imul c.CX (c.FA 0))) (imul SIGC (imul c.SX (c.FA 1)))) (imul RHOC c.B1))
/-- `k''` -/
def N2 (c : Cell) : ℤ × ℤ := isub (imul c.PG c.SX) (imul G2C c.CX)
def K2 (c : Cell) : ℤ × ℤ :=
  iadd (ineg (imul PI2C (idivp (iadd (isub (imul c.N2 c.E2) (iscl 4 (imul c.NI c.EI))) (iscl 8 (imul c.BI c.MI)))
      (imul c.E2 c.EI))))
    (iadd (iadd (ineg (imul TAUC (imul c.SX (c.FA 0)))) (ineg (iscl 2 (imul RHOC (imul c.CX (c.FA 1))))))
      (iadd (iscl 2 (imul SIGC (imul c.SX (c.FA 2)))) (imul RHOC c.B2)))

/-- the zero-order bound: `|k| ≥ KA` -/
def KA (c : Cell) : ℤ := max 0 (max c.K0.1 (-c.K0.2))
/-- `w' = 2 k k'` at scale `DZ` -/
def W1 (c : Cell) : ℤ × ℤ := iscl 2 (imul c.K0 c.K1)
/-- `w'' / 2 ≥ k'² + k k''`, lower bound at scale `DZ²` -/
def W2L (c : Cell) : ℤ :=
  max 0 (max c.K1.1 (-c.K1.2)) * max 0 (max c.K1.1 (-c.K1.2)) + (imul c.K0 c.K2).1 * DZ
end Cell

end AMW.C
