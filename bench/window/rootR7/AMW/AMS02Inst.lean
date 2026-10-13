import AMW.CWindow

/-! ###### the AM 7-point weighted certificate `AMS02`: zero-order and slope leaf tests, convex basins, walk, cover

Weights: AMTOPA's window (zeta-exact-pressure), first 13 terms; LP pair weights and pressures, mirror-symmetric,
over SA = 10⁸.  Pyramid lower-bound table adapted from five-point-pyramid-2 by typh, convex basins after
six-point-convex-basins-2 by typh (Apache-2.0). ###### -/

noncomputable section

namespace AMW.Cert.AMS02

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

def SA : ℕ := 100000000
def cN : ℕ := 789487

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  (48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5
    + (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb3_t` (U = 10¹⁰; three-piece pyramid reads), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 48468 l0) (Nat.mul 71367 l1)) (Nat.mul 82339 l2)) (Nat.mul 82339 l3)) (Nat.mul 71367 l4)) (Nat.mul 48468 l5)) 10000000000
  ee 258699100160000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 790920462336 (lb3 top bk l0 u0))
  ee 258699100160000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1110645964800 (lb3 top bk l4 u4))
  ee 258699100160000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1375233572864 (lb3 top bk l3 u3))
  ee 258699100160000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 1110645964800 (lb3 top bk l1 u1))
  ee 258699100160000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 1375233572864 (lb3 top bk l2 u2))
  ee 258699100160000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 790920462336 (lb3 top bk l5 u5))
  ee 258699100160000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3666646794240 (lb3 top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 258699100160000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 1443476602880 (lb3 top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 258699100160000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1443476602880 (lb3 top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 258699100160000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 258699100160000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 2511680438272 (lb3 top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 258699100160000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 2511680438272 (lb3 top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 258699100160000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)))
  ee 258699100160000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 258699100160000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 6553600000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)))
  ee 258699100160000000000 s15 (
  let s16 := Nat.add s15 (Nat.mul 765119561728 (lb3 top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 258699100160000000000 s16 (
  let s17 := Nat.add s16 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)))
  ee 258699100160000000000 s17 (
  let s18 := Nat.add s17 (Nat.mul 765119561728 (lb3 top bk (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)))
  ee 258699100160000000000 s18 (
  let s19 := Nat.add s18 (Nat.mul 0 (lb3 top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 258699100160000000000 s19 (
  let s20 := Nat.add s19 (Nat.mul 0 (lb3 top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 258699100160000000000 s20 (
  let s21 := Nat.add s20 (Nat.mul 0 (lb3 top bk (Nat.add l4 l5) (Nat.add u4 u5)))
  Nat.ble 258699100160000000000 s21)))))))))))))))))))))

/-- bit `t` of `T` -/
def bitOf (T t : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight T t) 1) 1


/-- the slope inequality at the point `q` with expansion set `T`, given the per-term reads and convexity flags:
`cN·SC·U + (U/U1)·(Σ_r ((q_r − l_r)·Pos_r + (u_r − q_r)·Neg_r) + Σ_t a_t·charge_t) ≤ U·Σ b_r q_r + SC·Σ a_t·val_t` -/
def cscheck (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ) (x0 eu0 ed0 : ℕ) (v0 : Bool) (x1 eu1 ed1 : ℕ) (v1 : Bool) (x2 eu2 ed2 : ℕ) (v2 : Bool) (x3 eu3 ed3 : ℕ) (v3 : Bool) (x4 eu4 ed4 : ℕ) (v4 : Bool) (x5 eu5 ed5 : ℕ) (v5 : Bool) (x6 eu6 ed6 : ℕ) (v6 : Bool) (x7 eu7 ed7 : ℕ) (v7 : Bool) (x8 eu8 ed8 : ℕ) (v8 : Bool) (x9 eu9 ed9 : ℕ) (v9 : Bool) (x10 eu10 ed10 : ℕ) (v10 : Bool) (x11 eu11 ed11 : ℕ) (v11 : Bool) (x12 eu12 ed12 : ℕ) (v12 : Bool) (x13 eu13 ed13 : ℕ) (v13 : Bool) (x14 eu14 ed14 : ℕ) (v14 : Bool) (x15 eu15 ed15 : ℕ) (v15 : Bool) (x16 eu16 ed16 : ℕ) (v16 : Bool) (x17 eu17 ed17 : ℕ) (v17 : Bool) (x18 eu18 ed18 : ℕ) (v18 : Bool) (x19 eu19 ed19 : ℕ) (v19 : Bool) (x20 eu20 ed20 : ℕ) (v20 : Bool) : Bool :=
  ((((((((((((((((((((((((((((((((Nat.ble l0 q0 && Nat.ble q0 u0) && Nat.ble l1 q1) && Nat.ble q1 u1) && Nat.ble l2 q2) && Nat.ble q2 u2) && Nat.ble l3 q3) && Nat.ble q3 u3) && Nat.ble l4 q4) && Nat.ble q4 u4) && Nat.ble l5 q5) && Nat.ble q5 u5) && rtok v0 (bitOf T 0) l0 u0 q0 x0 eu0 ed0) && rtok v1 (bitOf T 1) (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1) x1 eu1 ed1) && rtok v2 (bitOf T 2) (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2) x2 eu2 ed2) && rtok v3 (bitOf T 3) (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) x3 eu3 ed3) && rtok v4 (bitOf T 4) (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) x4 eu4 ed4) && rtok v5 (bitOf T 5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) x5 eu5 ed5) && rtok v6 (bitOf T 6) l1 u1 q1 x6 eu6 ed6) && rtok v7 (bitOf T 7) (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2) x7 eu7 ed7) && rtok v8 (bitOf T 8) (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3) x8 eu8 ed8) && rtok v9 (bitOf T 9) (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) x9 eu9 ed9) && rtok v10 (bitOf T 10) (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) x10 eu10 ed10) && rtok v11 (bitOf T 11) l2 u2 q2 x11 eu11 ed11) && rtok v12 (bitOf T 12) (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3) x12 eu12 ed12) && rtok v13 (bitOf T 13) (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4) x13 eu13 ed13) && rtok v14 (bitOf T 14) (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) x14 eu14 ed14) && rtok v15 (bitOf T 15) l3 u3 q3 x15 eu15 ed15) && rtok v16 (bitOf T 16) (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4) x16 eu16 ed16) && rtok v17 (bitOf T 17) (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5) x17 eu17 ed17) && rtok v18 (bitOf T 18) l4 u4 q4 x18 eu18 ed18) && rtok v19 (bitOf T 19) (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5) x19 eu19 ed19) && rtok v20 (bitOf T 20) l5 u5 q5 x20 eu20 ed20) && Nat.ble (Nat.add 258699100160000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub q0 l0) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 48468000000000 (Nat.mul 24136977 (tK (bitOf T 0)))) (Nat.mul 0 (tK (bitOf T 1)))) (Nat.mul 23349596 (tK (bitOf T 2)))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24136977 (tM (bitOf T 0) x0)) (Nat.mul 0 (tM (bitOf T 1) x1))) (Nat.mul 23349596 (tM (bitOf T 2) x2))) (Nat.mul 100000000 (tM (bitOf T 3) x3))) (Nat.mul 100000000 (tM (bitOf T 4) x4))) (Nat.mul 200000000 (tM (bitOf T 5) x5))))) (Nat.mul (Nat.sub u0 q0) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24136977 (tK (bitOf T 0))) (Nat.mul 0 (tK (bitOf T 1)))) (Nat.mul 23349596 (tK (bitOf T 2)))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 48468000000000 (Nat.mul 24136977 (tP (bitOf T 0) x0))) (Nat.mul 0 (tP (bitOf T 1) x1))) (Nat.mul 23349596 (tP (bitOf T 2) x2))) (Nat.mul 100000000 (tP (bitOf T 3) x3))) (Nat.mul 100000000 (tP (bitOf T 4) x4))) (Nat.mul 200000000 (tP (bitOf T 5) x5)))))) (Nat.mul (Nat.sub q1 l1) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 71367000000000 (Nat.mul 0 (tK (bitOf T 1)))) (Nat.mul 23349596 (tK (bitOf T 2)))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 33894225 (tK (bitOf T 6)))) (Nat.mul 44051410 (tK (bitOf T 7)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 0 (tM (bitOf T 1) x1)) (Nat.mul 23349596 (tM (bitOf T 2) x2))) (Nat.mul 100000000 (tM (bitOf T 3) x3))) (Nat.mul 100000000 (tM (bitOf T 4) x4))) (Nat.mul 200000000 (tM (bitOf T 5) x5))) (Nat.mul 33894225 (tM (bitOf T 6) x6))) (Nat.mul 44051410 (tM (bitOf T 7) x7))) (Nat.mul 76650404 (tM (bitOf T 8) x8))) (Nat.mul 0 (tM (bitOf T 9) x9))) (Nat.mul 100000000 (tM (bitOf T 10) x10)))))) (Nat.mul (Nat.sub u1 q1) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 0 (tK (bitOf T 1))) (Nat.mul 23349596 (tK (bitOf T 2)))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 33894225 (tK (bitOf T 6)))) (Nat.mul 44051410 (tK (bitOf T 7)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 71367000000000 (Nat.mul 0 (tP (bitOf T 1) x1))) (Nat.mul 23349596 (tP (bitOf T 2) x2))) (Nat.mul 100000000 (tP (bitOf T 3) x3))) (Nat.mul 100000000 (tP (bitOf T 4) x4))) (Nat.mul 200000000 (tP (bitOf T 5) x5))) (Nat.mul 33894225 (tP (bitOf T 6) x6))) (Nat.mul 44051410 (tP (bitOf T 7) x7))) (Nat.mul 76650404 (tP (bitOf T 8) x8))) (Nat.mul 0 (tP (bitOf T 9) x9))) (Nat.mul 100000000 (tP (bitOf T 10) x10)))))) (Nat.mul (Nat.sub q2 l2) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82339000000000 (Nat.mul 23349596 (tK (bitOf T 2)))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 44051410 (tK (bitOf T 7)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 41968798 (tK (bitOf T 11)))) (Nat.mul 111897180 (tK (bitOf T 12)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 23349596 (tM (bitOf T 2) x2)) (Nat.mul 100000000 (tM (bitOf T 3) x3))) (Nat.mul 100000000 (tM (bitOf T 4) x4))) (Nat.mul 200000000 (tM (bitOf T 5) x5))) (Nat.mul 44051410 (tM (bitOf T 7) x7))) (Nat.mul 76650404 (tM (bitOf T 8) x8))) (Nat.mul 0 (tM (bitOf T 9) x9))) (Nat.mul 100000000 (tM (bitOf T 10) x10))) (Nat.mul 41968798 (tM (bitOf T 11) x11))) (Nat.mul 111897180 (tM (bitOf T 12) x12))) (Nat.mul 76650404 (tM (bitOf T 13) x13))) (Nat.mul 100000000 (tM (bitOf T 14) x14)))))) (Nat.mul (Nat.sub u2 q2) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 23349596 (tK (bitOf T 2))) (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 44051410 (tK (bitOf T 7)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 41968798 (tK (bitOf T 11)))) (Nat.mul 111897180 (tK (bitOf T 12)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82339000000000 (Nat.mul 23349596 (tP (bitOf T 2) x2))) (Nat.mul 100000000 (tP (bitOf T 3) x3))) (Nat.mul 100000000 (tP (bitOf T 4) x4))) (Nat.mul 200000000 (tP (bitOf T 5) x5))) (Nat.mul 44051410 (tP (bitOf T 7) x7))) (Nat.mul 76650404 (tP (bitOf T 8) x8))) (Nat.mul 0 (tP (bitOf T 9) x9))) (Nat.mul 100000000 (tP (bitOf T 10) x10))) (Nat.mul 41968798 (tP (bitOf T 11) x11))) (Nat.mul 111897180 (tP (bitOf T 12) x12))) (Nat.mul 76650404 (tP (bitOf T 13) x13))) (Nat.mul 100000000 (tP (bitOf T 14) x14)))))) (Nat.mul (Nat.sub q3 l3) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82339000000000 (Nat.mul 100000000 (tK (bitOf T 3)))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 111897180 (tK (bitOf T 12)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 41968798 (tK (bitOf T 15)))) (Nat.mul 44051410 (tK (bitOf T 16)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tM (bitOf T 3) x3)) (Nat.mul 100000000 (tM (bitOf T 4) x4))) (Nat.mul 200000000 (tM (bitOf T 5) x5))) (Nat.mul 76650404 (tM (bitOf T 8) x8))) (Nat.mul 0 (tM (bitOf T 9) x9))) (Nat.mul 100000000 (tM (bitOf T 10) x10))) (Nat.mul 111897180 (tM (bitOf T 12) x12))) (Nat.mul 76650404 (tM (bitOf T 13) x13))) (Nat.mul 100000000 (tM (bitOf T 14) x14))) (Nat.mul 41968798 (tM (bitOf T 15) x15))) (Nat.mul 44051410 (tM (bitOf T 16) x16))) (Nat.mul 23349596 (tM (bitOf T 17) x17)))))) (Nat.mul (Nat.sub u3 q3) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tK (bitOf T 3))) (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 76650404 (tK (bitOf T 8)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 111897180 (tK (bitOf T 12)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 41968798 (tK (bitOf T 15)))) (Nat.mul 44051410 (tK (bitOf T 16)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82339000000000 (Nat.mul 100000000 (tP (bitOf T 3) x3))) (Nat.mul 100000000 (tP (bitOf T 4) x4))) (Nat.mul 200000000 (tP (bitOf T 5) x5))) (Nat.mul 76650404 (tP (bitOf T 8) x8))) (Nat.mul 0 (tP (bitOf T 9) x9))) (Nat.mul 100000000 (tP (bitOf T 10) x10))) (Nat.mul 111897180 (tP (bitOf T 12) x12))) (Nat.mul 76650404 (tP (bitOf T 13) x13))) (Nat.mul 100000000 (tP (bitOf T 14) x14))) (Nat.mul 41968798 (tP (bitOf T 15) x15))) (Nat.mul 44051410 (tP (bitOf T 16) x16))) (Nat.mul 23349596 (tP (bitOf T 17) x17)))))) (Nat.mul (Nat.sub q4 l4) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 71367000000000 (Nat.mul 100000000 (tK (bitOf T 4)))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 44051410 (tK (bitOf T 16)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.mul 33894225 (tK (bitOf T 18)))) (Nat.mul 0 (tK (bitOf T 19)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tM (bitOf T 4) x4)) (Nat.mul 200000000 (tM (bitOf T 5) x5))) (Nat.mul 0 (tM (bitOf T 9) x9))) (Nat.mul 100000000 (tM (bitOf T 10) x10))) (Nat.mul 76650404 (tM (bitOf T 13) x13))) (Nat.mul 100000000 (tM (bitOf T 14) x14))) (Nat.mul 44051410 (tM (bitOf T 16) x16))) (Nat.mul 23349596 (tM (bitOf T 17) x17))) (Nat.mul 33894225 (tM (bitOf T 18) x18))) (Nat.mul 0 (tM (bitOf T 19) x19)))))) (Nat.mul (Nat.sub u4 q4) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tK (bitOf T 4))) (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 0 (tK (bitOf T 9)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 76650404 (tK (bitOf T 13)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 44051410 (tK (bitOf T 16)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.mul 33894225 (tK (bitOf T 18)))) (Nat.mul 0 (tK (bitOf T 19)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 71367000000000 (Nat.mul 100000000 (tP (bitOf T 4) x4))) (Nat.mul 200000000 (tP (bitOf T 5) x5))) (Nat.mul 0 (tP (bitOf T 9) x9))) (Nat.mul 100000000 (tP (bitOf T 10) x10))) (Nat.mul 76650404 (tP (bitOf T 13) x13))) (Nat.mul 100000000 (tP (bitOf T 14) x14))) (Nat.mul 44051410 (tP (bitOf T 16) x16))) (Nat.mul 23349596 (tP (bitOf T 17) x17))) (Nat.mul 33894225 (tP (bitOf T 18) x18))) (Nat.mul 0 (tP (bitOf T 19) x19)))))) (Nat.mul (Nat.sub q5 l5) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 48468000000000 (Nat.mul 200000000 (tK (bitOf T 5)))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.mul 0 (tK (bitOf T 19)))) (Nat.mul 24136977 (tK (bitOf T 20)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (tM (bitOf T 5) x5)) (Nat.mul 100000000 (tM (bitOf T 10) x10))) (Nat.mul 100000000 (tM (bitOf T 14) x14))) (Nat.mul 23349596 (tM (bitOf T 17) x17))) (Nat.mul 0 (tM (bitOf T 19) x19))) (Nat.mul 24136977 (tM (bitOf T 20) x20)))))) (Nat.mul (Nat.sub u5 q5) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (tK (bitOf T 5))) (Nat.mul 100000000 (tK (bitOf T 10)))) (Nat.mul 100000000 (tK (bitOf T 14)))) (Nat.mul 23349596 (tK (bitOf T 17)))) (Nat.mul 0 (tK (bitOf T 19)))) (Nat.mul 24136977 (tK (bitOf T 20)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 48468000000000 (Nat.mul 200000000 (tP (bitOf T 5) x5))) (Nat.mul 100000000 (tP (bitOf T 10) x10))) (Nat.mul 100000000 (tP (bitOf T 14) x14))) (Nat.mul 23349596 (tP (bitOf T 17) x17))) (Nat.mul 0 (tP (bitOf T 19) x19))) (Nat.mul 24136977 (tP (bitOf T 20) x20)))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24136977 (mchg v0 (bitOf T 0) l0 u0 q0 x0 eu0 ed0)) (Nat.mul 0 (mchg v1 (bitOf T 1) (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1) x1 eu1 ed1))) (Nat.mul 23349596 (mchg v2 (bitOf T 2) (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2) x2 eu2 ed2))) (Nat.mul 100000000 (mchg v3 (bitOf T 3) (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) x3 eu3 ed3))) (Nat.mul 100000000 (mchg v4 (bitOf T 4) (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) x4 eu4 ed4))) (Nat.mul 200000000 (mchg v5 (bitOf T 5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) x5 eu5 ed5))) (Nat.mul 33894225 (mchg v6 (bitOf T 6) l1 u1 q1 x6 eu6 ed6))) (Nat.mul 44051410 (mchg v7 (bitOf T 7) (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2) x7 eu7 ed7))) (Nat.mul 76650404 (mchg v8 (bitOf T 8) (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3) x8 eu8 ed8))) (Nat.mul 0 (mchg v9 (bitOf T 9) (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) x9 eu9 ed9))) (Nat.mul 100000000 (mchg v10 (bitOf T 10) (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) x10 eu10 ed10))) (Nat.mul 41968798 (mchg v11 (bitOf T 11) l2 u2 q2 x11 eu11 ed11))) (Nat.mul 111897180 (mchg v12 (bitOf T 12) (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3) x12 eu12 ed12))) (Nat.mul 76650404 (mchg v13 (bitOf T 13) (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4) x13 eu13 ed13))) (Nat.mul 100000000 (mchg v14 (bitOf T 14) (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) x14 eu14 ed14))) (Nat.mul 41968798 (mchg v15 (bitOf T 15) l3 u3 q3 x15 eu15 ed15))) (Nat.mul 44051410 (mchg v16 (bitOf T 16) (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4) x16 eu16 ed16))) (Nat.mul 23349596 (mchg v17 (bitOf T 17) (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5) x17 eu17 ed17))) (Nat.mul 33894225 (mchg v18 (bitOf T 18) l4 u4 q4 x18 eu18 ed18))) (Nat.mul 0 (mchg v19 (bitOf T 19) (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5) x19 eu19 ed19))) (Nat.mul 24136977 (mchg v20 (bitOf T 20) l5 u5 q5 x20 eu20 ed20)))))) (Nat.add (Nat.mul 10000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 48468 q0) (Nat.mul 71367 q1)) (Nat.mul 82339 q2)) (Nat.mul 82339 q3)) (Nat.mul 71367 q4)) (Nat.mul 48468 q5))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24136977 (tval (bitOf T 0) x0)) (Nat.mul 0 (tval (bitOf T 1) x1))) (Nat.mul 23349596 (tval (bitOf T 2) x2))) (Nat.mul 100000000 (tval (bitOf T 3) x3))) (Nat.mul 100000000 (tval (bitOf T 4) x4))) (Nat.mul 200000000 (tval (bitOf T 5) x5))) (Nat.mul 33894225 (tval (bitOf T 6) x6))) (Nat.mul 44051410 (tval (bitOf T 7) x7))) (Nat.mul 76650404 (tval (bitOf T 8) x8))) (Nat.mul 0 (tval (bitOf T 9) x9))) (Nat.mul 100000000 (tval (bitOf T 10) x10))) (Nat.mul 41968798 (tval (bitOf T 11) x11))) (Nat.mul 111897180 (tval (bitOf T 12) x12))) (Nat.mul 76650404 (tval (bitOf T 13) x13))) (Nat.mul 100000000 (tval (bitOf T 14) x14))) (Nat.mul 41968798 (tval (bitOf T 15) x15))) (Nat.mul 44051410 (tval (bitOf T 16) x16))) (Nat.mul 23349596 (tval (bitOf T 17) x17))) (Nat.mul 33894225 (tval (bitOf T 18) x18))) (Nat.mul 0 (tval (bitOf T 19) x19))) (Nat.mul 24136977 (tval (bitOf T 20) x20)))))

/-- the slope test at the point `q` with expansion set `T`: an expanded term whose range lies in a convex region of `R`
is bounded by its tangent (no charge), the other expanded terms are charged from the derivative reads -/
def ctest (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ) : Bool :=
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l0 u0) (bitOf T 0)) fun v0 =>
  forceB (selXf (bitOf T 0) top bk pb l0 u0 q0) fun x0 =>
  forceB (selUv v0 (bitOf T 0) tD bD q0 u0) fun eu0 =>
  forceB (selDv v0 (bitOf T 0) tD bD l0 q0) fun ed0 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l0 l1) (Nat.add u0 u1)) (bitOf T 1)) fun v1 =>
  forceB (selXf (bitOf T 1) top bk pb (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1)) fun x1 =>
  forceB (selUv v1 (bitOf T 1) tD bD (Nat.add q0 q1) (Nat.add u0 u1)) fun eu1 =>
  forceB (selDv v1 (bitOf T 1) tD bD (Nat.add l0 l1) (Nat.add q0 q1)) fun ed1 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)) (bitOf T 2)) fun v2 =>
  forceB (selXf (bitOf T 2) top bk pb (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2)) fun x2 =>
  forceB (selUv v2 (bitOf T 2) tD bD (Nat.add (Nat.add q0 q1) q2) (Nat.add (Nat.add u0 u1) u2)) fun eu2 =>
  forceB (selDv v2 (bitOf T 2) tD bD (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add q0 q1) q2)) fun ed2 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)) (bitOf T 3)) fun v3 =>
  forceB (selXf (bitOf T 3) top bk pb (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3)) fun x3 =>
  forceB (selUv v3 (bitOf T 3) tD bD (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)) fun eu3 =>
  forceB (selDv v3 (bitOf T 3) tD bD (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3)) fun ed3 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)) (bitOf T 4)) fun v4 =>
  forceB (selXf (bitOf T 4) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4)) fun x4 =>
  forceB (selUv v4 (bitOf T 4) tD bD (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)) fun eu4 =>
  forceB (selDv v4 (bitOf T 4) tD bD (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4)) fun ed4 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)) (bitOf T 5)) fun v5 =>
  forceB (selXf (bitOf T 5) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5)) fun x5 =>
  forceB (selUv v5 (bitOf T 5) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)) fun eu5 =>
  forceB (selDv v5 (bitOf T 5) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5)) fun ed5 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l1 u1) (bitOf T 6)) fun v6 =>
  forceB (selXf (bitOf T 6) top bk pb l1 u1 q1) fun x6 =>
  forceB (selUv v6 (bitOf T 6) tD bD q1 u1) fun eu6 =>
  forceB (selDv v6 (bitOf T 6) tD bD l1 q1) fun ed6 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l1 l2) (Nat.add u1 u2)) (bitOf T 7)) fun v7 =>
  forceB (selXf (bitOf T 7) top bk pb (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2)) fun x7 =>
  forceB (selUv v7 (bitOf T 7) tD bD (Nat.add q1 q2) (Nat.add u1 u2)) fun eu7 =>
  forceB (selDv v7 (bitOf T 7) tD bD (Nat.add l1 l2) (Nat.add q1 q2)) fun ed7 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)) (bitOf T 8)) fun v8 =>
  forceB (selXf (bitOf T 8) top bk pb (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3)) fun x8 =>
  forceB (selUv v8 (bitOf T 8) tD bD (Nat.add (Nat.add q1 q2) q3) (Nat.add (Nat.add u1 u2) u3)) fun eu8 =>
  forceB (selDv v8 (bitOf T 8) tD bD (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add q1 q2) q3)) fun ed8 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)) (bitOf T 9)) fun v9 =>
  forceB (selXf (bitOf T 9) top bk pb (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4)) fun x9 =>
  forceB (selUv v9 (bitOf T 9) tD bD (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)) fun eu9 =>
  forceB (selDv v9 (bitOf T 9) tD bD (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4)) fun ed9 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)) (bitOf T 10)) fun v10 =>
  forceB (selXf (bitOf T 10) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5)) fun x10 =>
  forceB (selUv v10 (bitOf T 10) tD bD (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)) fun eu10 =>
  forceB (selDv v10 (bitOf T 10) tD bD (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5)) fun ed10 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l2 u2) (bitOf T 11)) fun v11 =>
  forceB (selXf (bitOf T 11) top bk pb l2 u2 q2) fun x11 =>
  forceB (selUv v11 (bitOf T 11) tD bD q2 u2) fun eu11 =>
  forceB (selDv v11 (bitOf T 11) tD bD l2 q2) fun ed11 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l2 l3) (Nat.add u2 u3)) (bitOf T 12)) fun v12 =>
  forceB (selXf (bitOf T 12) top bk pb (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3)) fun x12 =>
  forceB (selUv v12 (bitOf T 12) tD bD (Nat.add q2 q3) (Nat.add u2 u3)) fun eu12 =>
  forceB (selDv v12 (bitOf T 12) tD bD (Nat.add l2 l3) (Nat.add q2 q3)) fun ed12 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)) (bitOf T 13)) fun v13 =>
  forceB (selXf (bitOf T 13) top bk pb (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4)) fun x13 =>
  forceB (selUv v13 (bitOf T 13) tD bD (Nat.add (Nat.add q2 q3) q4) (Nat.add (Nat.add u2 u3) u4)) fun eu13 =>
  forceB (selDv v13 (bitOf T 13) tD bD (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add q2 q3) q4)) fun ed13 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)) (bitOf T 14)) fun v14 =>
  forceB (selXf (bitOf T 14) top bk pb (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5)) fun x14 =>
  forceB (selUv v14 (bitOf T 14) tD bD (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)) fun eu14 =>
  forceB (selDv v14 (bitOf T 14) tD bD (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5)) fun ed14 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l3 u3) (bitOf T 15)) fun v15 =>
  forceB (selXf (bitOf T 15) top bk pb l3 u3 q3) fun x15 =>
  forceB (selUv v15 (bitOf T 15) tD bD q3 u3) fun eu15 =>
  forceB (selDv v15 (bitOf T 15) tD bD l3 q3) fun ed15 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l3 l4) (Nat.add u3 u4)) (bitOf T 16)) fun v16 =>
  forceB (selXf (bitOf T 16) top bk pb (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4)) fun x16 =>
  forceB (selUv v16 (bitOf T 16) tD bD (Nat.add q3 q4) (Nat.add u3 u4)) fun eu16 =>
  forceB (selDv v16 (bitOf T 16) tD bD (Nat.add l3 l4) (Nat.add q3 q4)) fun ed16 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)) (bitOf T 17)) fun v17 =>
  forceB (selXf (bitOf T 17) top bk pb (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5)) fun x17 =>
  forceB (selUv v17 (bitOf T 17) tD bD (Nat.add (Nat.add q3 q4) q5) (Nat.add (Nat.add u3 u4) u5)) fun eu17 =>
  forceB (selDv v17 (bitOf T 17) tD bD (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add q3 q4) q5)) fun ed17 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l4 u4) (bitOf T 18)) fun v18 =>
  forceB (selXf (bitOf T 18) top bk pb l4 u4 q4) fun x18 =>
  forceB (selUv v18 (bitOf T 18) tD bD q4 u4) fun eu18 =>
  forceB (selDv v18 (bitOf T 18) tD bD l4 q4) fun ed18 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l4 l5) (Nat.add u4 u5)) (bitOf T 19)) fun v19 =>
  forceB (selXf (bitOf T 19) top bk pb (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5)) fun x19 =>
  forceB (selUv v19 (bitOf T 19) tD bD (Nat.add q4 q5) (Nat.add u4 u5)) fun eu19 =>
  forceB (selDv v19 (bitOf T 19) tD bD (Nat.add l4 l5) (Nat.add q4 q5)) fun ed19 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l5 u5) (bitOf T 20)) fun v20 =>
  forceB (selXf (bitOf T 20) top bk pb l5 u5 q5) fun x20 =>
  forceB (selUv v20 (bitOf T 20) tD bD q5 u5) fun eu20 =>
  forceB (selDv v20 (bitOf T 20) tD bD l5 q5) fun ed20 =>
  cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T x0 eu0 ed0 v0 x1 eu1 ed1 v1 x2 eu2 ed2 v2 x3 eu3 ed3 v3 x4 eu4 ed4 v4 x5 eu5 ed5 v5 x6 eu6 ed6 v6 x7 eu7 ed7 v7 x8 eu8 ed8 v8 x9 eu9 ed9 v9 x10 eu10 ed10 v10 x11 eu11 ed11 v11 x12 eu12 ed12 v12 x13 eu13 ed13 v13 x14 eu14 ed14 v14 x15 eu15 ed15 v15 x16 eu16 ed16 v16 x17 eu17 ed17 v17 x18 eu18 ed18 v18 x19 eu19 ed19 v19 x20 eu20 ed20 v20


/-- the expansion point of a gap from its 2-bit mode: the lower end, the upper end or the midpoint, each rounded to a
multiple of `2^8`, else of `16`, when that stays in `[l, u]` (any value is sound: the test checks `l ≤ q ≤ u`) -/
def dec (m l u : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (Nat.shiftRight (Nat.add l u) 1) fun c =>
        forceR (Nat.shiftLeft (Nat.shiftRight c 8) 8) fun cc =>
          Bool.rec (motive := fun _ => ℕ)
            (forceR (Nat.shiftLeft (Nat.shiftRight c 4) 4) fun c2 => Bool.rec (motive := fun _ => ℕ) c c2 (Nat.ble l c2))
            cc (Nat.ble l cc))
      (forceR (Nat.shiftLeft (Nat.shiftRight u 8) 8) fun mm =>
        Bool.rec (motive := fun _ => ℕ)
          (forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun m2 => Bool.rec (motive := fun _ => ℕ) u m2 (Nat.ble l m2))
          mm (Nat.ble l mm))
      (Nat.beq m 1))
    (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 255) 8) 8) fun mm =>
      Bool.rec (motive := fun _ => ℕ)
        (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun m2 => Bool.rec (motive := fun _ => ℕ) l m2 (Nat.ble m2 u))
        mm (Nat.ble mm u))
    (Nat.beq m 0)

/-- a slope leaf: modes (bits 3..14), then a flag (bit 15: every term expanded) or the expansion set
(bits 16..) of the walk word `w` -/
def sleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  forceB (dec (Nat.land (Nat.shiftRight w 3) 3) l0 u0) fun q0 =>
  forceB (dec (Nat.land (Nat.shiftRight w 5) 3) l1 u1) fun q1 =>
  forceB (dec (Nat.land (Nat.shiftRight w 7) 3) l2 u2) fun q2 =>
  forceB (dec (Nat.land (Nat.shiftRight w 9) 3) l3 u3) fun q3 =>
  forceB (dec (Nat.land (Nat.shiftRight w 11) 3) l4 u4) fun q4 =>
  forceB (dec (Nat.land (Nat.shiftRight w 13) 3) l5 u5) fun q5 =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 16) 2097151) 2097151 (Nat.beq (Nat.land (Nat.shiftRight w 15) 1) 1)) fun T =>
  ctest top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T

/-- the expansion point of a gap at a centre leaf: coordinate `r` of the centre `k` (20-bit fields of `C`), clamped to
`[l, u]` rounded inward to multiples of `16` when that is nonempty, else to `[l, u]` -/
def cdec (C k r l u : ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight C (Nat.mul 20 (Nat.add (Nat.mul 6 k) r))) 1048575) fun c =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun la =>
  forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun ua =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c u (Nat.ble u c)) l (Nat.ble c l))
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c ua (Nat.ble ua c)) la (Nat.ble c la))
    (Nat.ble la ua)

/-- a centre leaf: the centre index (bits 3..10), then a flag (bit 11: every term expanded) or the expansion set
(bits 12..) of the walk word `w` -/
def cleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  forceB (Nat.land (Nat.shiftRight w 3) 255) fun k =>
  forceB (cdec C k 0 l0 u0) fun q0 =>
  forceB (cdec C k 1 l1 u1) fun q1 =>
  forceB (cdec C k 2 l2 u2) fun q2 =>
  forceB (cdec C k 3 l3 u3) fun q3 =>
  forceB (cdec C k 4 l4 u4) fun q4 =>
  forceB (cdec C k 5 l5 u5) fun q5 =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 12) 2097151) 2097151 (Nat.beq (Nat.land (Nat.shiftRight w 11) 1) 1)) fun T =>
  ctest top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T

/-- a basin box -/
structure Bx where
  (l0 u0 : ℕ) (l1 u1 : ℕ) (l2 u2 : ℕ) (l3 u3 : ℕ) (l4 u4 : ℕ) (l5 u5 : ℕ)

/-- the box lies inside one of the basin boxes -/
def inBas (bas : List Bx) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  bas.any fun b => Nat.ble b.l0 l0 && Nat.ble u0 b.u0 && Nat.ble b.l1 l1 && Nat.ble u1 b.u1 && Nat.ble b.l2 l2 && Nat.ble u2 b.u2 && Nat.ble b.l3 l3 && Nat.ble u3 b.u3 && Nat.ble b.l4 l4 && Nat.ble u4 b.u4 && Nat.ble b.l5 l5 && Nat.ble u5 b.u5

/-- the type of a walk continuation: position and the coordinates to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- a split on gap 0: the lower half (`u0 := q`) from `pos + 4`, then the upper half from where it ends -/
def split0 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l0 u0) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
  Bool.rec (motive := fun _ => ℕ) (ih p q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (0) (Nat.beq p 0)

/-- a split on gap 1: the lower half (`u1 := q`) from `pos + 4`, then the upper half from where it ends -/
def split1 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l1 u1) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5) (0) (Nat.beq p 0)

/-- a split on gap 2: the lower half (`u2 := q`) from `pos + 4`, then the upper half from where it ends -/
def split2 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l2 u2) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5) (0) (Nat.beq p 0)

/-- a split on gap 3: the lower half (`u3 := q`) from `pos + 4`, then the upper half from where it ends -/
def split3 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l3 u3) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5) (0) (Nat.beq p 0)

/-- a split on gap 4: the lower half (`u4 := q`) from `pos + 4`, then the upper half from where it ends -/
def split4 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l4 u4) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5) (0) (Nat.beq p 0)

/-- a split on gap 5: the lower half (`u5 := q`) from `pos + 4`, then the upper half from where it ends -/
def split5 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l5 u5) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5) (0) (Nat.beq p 0)

/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq ax 4)) (split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq ax 3)) (split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq ax 2)) (split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq ax 1)) (split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq ax 0)

/-- a leaf (bit 0 clear; bits 1..2 the kind: zero-order, slope with its payload, basin): in the reflected half-space, or
the leaf's own test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 33) (Nat.add pos 12) (Nat.beq (Nat.land (Nat.shiftRight w 11) 1) 1)) (cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 3) (inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2)) (Bool.rec (motive := fun _ => ℕ) (0) (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 37) (Nat.add pos 16) (Nat.beq (Nat.land (Nat.shiftRight w 15) 1) 1)) (sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1)) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 3) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0)) (Nat.add pos 3) (Nat.ble (Nat.add u5 1) l0)

/-- the bisection walk (`Nat.rec` on the fuel): the node word is `bits >>> pos` (bit 0 split, bits 1..3 axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Prop :=
  ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 ∨ g5 < g0

theorem ee_or {C s : ℕ} {rest : Bool} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    258699100160000000000 ≤ 10000000000 * (48468 * l0 + 71367 * l1 + 82339 * l2 + 82339 * l3 + 71367 * l4 + 48468 * l5) + 32768 * (24136977 * lb3 top bk (l0) (u0) + 0 * lb3 top bk (l0 + l1) (u0 + u1) + 23349596 * lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) + 100000000 * lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 100000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 200000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) + 33894225 * lb3 top bk (l1) (u1) + 44051410 * lb3 top bk (l1 + l2) (u1 + u2) + 76650404 * lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) + 0 * lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 100000000 * lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) + 41968798 * lb3 top bk (l2) (u2) + 111897180 * lb3 top bk (l2 + l3) (u2 + u3) + 76650404 * lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) + 100000000 * lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) + 41968798 * lb3 top bk (l3) (u3) + 44051410 * lb3 top bk (l3 + l4) (u3 + u4) + 23349596 * lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) + 33894225 * lb3 top bk (l4) (u4) + 0 * lb3 top bk (l4 + l5) (u4 + u5) + 24136977 * lb3 top bk (l5) (u5)) := by
  unfold leafOK at h
  dsimp only at h
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 8000000 in
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
  have w0 := lb3_sound hlb (l0) (u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := lb3_sound hlb (l0 + l1) (u0 + u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := lb3_sound hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := lb3_sound hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (g0 + g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42, h52])
  have w6 := lb3_sound hlb (l1) (u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w7 := lb3_sound hlb (l1 + l2) (u1 + u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w8 := lb3_sound hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w9 := lb3_sound hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w10 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42, h52])
  have w11 := lb3_sound hlb (l2) (u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w12 := lb3_sound hlb (l2 + l3) (u2 + u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w13 := lb3_sound hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w14 := lb3_sound hlb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42, h52])
  have w15 := lb3_sound hlb (l3) (u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w16 := lb3_sound hlb (l3 + l4) (u3 + u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w17 := lb3_sound hlb (l3 + l4 + l5) (u3 + u4 + u5) (g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h32, h42, h52])
  have w18 := lb3_sound hlb (l4) (u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  have w19 := lb3_sound hlb (l4 + l5) (u4 + u5) (g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h42, h52])
  have w20 := lb3_sound hlb (l5) (u5) (g5) (by push_cast; (try simp only [add_div]); linarith [h51]) (by push_cast; (try simp only [add_div]); linarith [h52])
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 48468 * ((l0 : ℝ) / SC) + 71367 * ((l1 : ℝ) / SC) + 82339 * ((l2 : ℝ) / SC) + 82339 * ((l3 : ℝ) / SC) + 71367 * ((l4 : ℝ) / SC) + 48468 * ((l5 : ℝ) / SC) with hL
  set Wt : ℝ := 24136977 * ((lb3 top bk (l0) (u0) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 23349596 * ((lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 200000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 33894225 * ((lb3 top bk (l1) (u1) : ℝ) / 10000000000) + 44051410 * ((lb3 top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 76650404 * ((lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 41968798 * ((lb3 top bk (l2) (u2) : ℝ) / 10000000000) + 111897180 * ((lb3 top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 76650404 * ((lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 41968798 * ((lb3 top bk (l3) (u3) : ℝ) / 10000000000) + 44051410 * ((lb3 top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 23349596 * ((lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) / 10000000000) + 33894225 * ((lb3 top bk (l4) (u4) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l4 + l5) (u4 + u5) : ℝ) / 10000000000) + 24136977 * ((lb3 top bk (l5) (u5) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (48468 * (l0 : ℝ) + 71367 * (l1 : ℝ) + 82339 * (l2 : ℝ) + 82339 * (l3 : ℝ) + 71367 * (l4 : ℝ) + 48468 * (l5 : ℝ)) + 32768 * (24136977 * (lb3 top bk (l0) (u0) : ℝ) + 0 * (lb3 top bk (l0 + l1) (u0 + u1) : ℝ) + 23349596 * (lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 100000000 * (lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 100000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 200000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) + 33894225 * (lb3 top bk (l1) (u1) : ℝ) + 44051410 * (lb3 top bk (l1 + l2) (u1 + u2) : ℝ) + 76650404 * (lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 0 * (lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 100000000 * (lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) + 41968798 * (lb3 top bk (l2) (u2) : ℝ) + 111897180 * (lb3 top bk (l2 + l3) (u2 + u3) : ℝ) + 76650404 * (lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 100000000 * (lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) + 41968798 * (lb3 top bk (l3) (u3) : ℝ) + 44051410 * (lb3 top bk (l3 + l4) (u3 + u4) : ℝ) + 23349596 * (lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) + 33894225 * (lb3 top bk (l4) (u4) : ℝ) + 0 * (lb3 top bk (l4 + l5) (u4 + u5) : ℝ) + 24136977 * (lb3 top bk (l5) (u5) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 258699100160000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5
      + (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5)) * SA
      = 48468 * g0 + 71367 * g1 + 82339 * g2 + 82339 * g3 + 71367 * g4 + 48468 * g5 + 24136977 * wfun (g0) + 0 * wfun (g0 + g1) + 23349596 * wfun (g0 + g1 + g2) + 100000000 * wfun (g0 + g1 + g2 + g3) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 33894225 * wfun (g1) + 44051410 * wfun (g1 + g2) + 76650404 * wfun (g1 + g2 + g3) + 0 * wfun (g1 + g2 + g3 + g4) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5) + 41968798 * wfun (g2) + 111897180 * wfun (g2 + g3) + 76650404 * wfun (g2 + g3 + g4) + 100000000 * wfun (g2 + g3 + g4 + g5) + 41968798 * wfun (g3) + 44051410 * wfun (g3 + g4) + 23349596 * wfun (g3 + g4 + g5) + 33894225 * wfun (g4) + 0 * wfun (g4 + g5) + 24136977 * wfun (g5) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 48468), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 71367), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 82339), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 82339), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 71367), mul_le_mul_of_nonneg_left h51 (by positivity : (0:ℝ) ≤ 48468), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 24136977), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 111897180), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w15 (by positivity : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left w16 (by positivity : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left w17 (by positivity : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left w18 (by positivity : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left w19 (by positivity : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left w20 (by positivity : (0:ℝ) ≤ 24136977)]

theorem ctest_spec {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ)
    (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T = true) :
    cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (bitOf T 0) tD bD (q0) (u0)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (bitOf T 0) tD bD (l0) (q0)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (bitOf T 1) tD bD (q0 + q1) (u0 + u1)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (bitOf T 1) tD bD (l0 + l1) (q0 + q1)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (bitOf T 2) tD bD (q0 + q1 + q2) (u0 + u1 + u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (bitOf T 2) tD bD (l0 + l1 + l2) (q0 + q1 + q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (bitOf T 3) tD bD (q0 + q1 + q2 + q3) (u0 + u1 + u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (bitOf T 3) tD bD (l0 + l1 + l2 + l3) (q0 + q1 + q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (bitOf T 4) tD bD (q0 + q1 + q2 + q3 + q4) (u0 + u1 + u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (bitOf T 4) tD bD (l0 + l1 + l2 + l3 + l4) (q0 + q1 + q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (bitOf T 5) tD bD (q0 + q1 + q2 + q3 + q4 + q5) (u0 + u1 + u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (bitOf T 5) tD bD (l0 + l1 + l2 + l3 + l4 + l5) (q0 + q1 + q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (selXf (bitOf T 6) top bk pb (l1) (u1) (q1)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 6)) (bitOf T 6) tD bD (q1) (u1)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 6)) (bitOf T 6) tD bD (l1) (q1)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 6)) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 7)) (bitOf T 7) tD bD (q1 + q2) (u1 + u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 7)) (bitOf T 7) tD bD (l1 + l2) (q1 + q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 7)) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 8)) (bitOf T 8) tD bD (q1 + q2 + q3) (u1 + u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 8)) (bitOf T 8) tD bD (l1 + l2 + l3) (q1 + q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 8)) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 9)) (bitOf T 9) tD bD (q1 + q2 + q3 + q4) (u1 + u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 9)) (bitOf T 9) tD bD (l1 + l2 + l3 + l4) (q1 + q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 9)) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 10)) (bitOf T 10) tD bD (q1 + q2 + q3 + q4 + q5) (u1 + u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 10)) (bitOf T 10) tD bD (l1 + l2 + l3 + l4 + l5) (q1 + q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 10)) (selXf (bitOf T 11) top bk pb (l2) (u2) (q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 11)) (bitOf T 11) tD bD (q2) (u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 11)) (bitOf T 11) tD bD (l2) (q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 11)) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 12)) (bitOf T 12) tD bD (q2 + q3) (u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 12)) (bitOf T 12) tD bD (l2 + l3) (q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 12)) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 13)) (bitOf T 13) tD bD (q2 + q3 + q4) (u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 13)) (bitOf T 13) tD bD (l2 + l3 + l4) (q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 13)) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 14)) (bitOf T 14) tD bD (q2 + q3 + q4 + q5) (u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 14)) (bitOf T 14) tD bD (l2 + l3 + l4 + l5) (q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 14)) (selXf (bitOf T 15) top bk pb (l3) (u3) (q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 15)) (bitOf T 15) tD bD (q3) (u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 15)) (bitOf T 15) tD bD (l3) (q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 15)) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 16)) (bitOf T 16) tD bD (q3 + q4) (u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 16)) (bitOf T 16) tD bD (l3 + l4) (q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 16)) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 17)) (bitOf T 17) tD bD (q3 + q4 + q5) (u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 17)) (bitOf T 17) tD bD (l3 + l4 + l5) (q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 17)) (selXf (bitOf T 18) top bk pb (l4) (u4) (q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 18)) (bitOf T 18) tD bD (q4) (u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 18)) (bitOf T 18) tD bD (l4) (q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 18)) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 19)) (bitOf T 19) tD bD (q4 + q5) (u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 19)) (bitOf T 19) tD bD (l4 + l5) (q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 19)) (selXf (bitOf T 20) top bk pb (l5) (u5) (q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 20)) (bitOf T 20) tD bD (q5) (u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 20)) (bitOf T 20) tD bD (l5) (q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 20)) = true := by
  unfold ctest at h
  simp only [forceB_eq, bforce_eq] at h
  exact h

set_option maxHeartbeats 40000000 in
theorem ctest_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ) (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have h' := ctest_spec l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq01, hq02⟩, hq11⟩, hq12⟩, hq21⟩, hq22⟩, hq31⟩, hq32⟩, hq41⟩, hq42⟩, hq51⟩, hq52⟩, hok0⟩, hok1⟩, hok2⟩, hok3⟩, hok4⟩, hok5⟩, hok6⟩, hok7⟩, hok8⟩, hok9⟩, hok10⟩, hok11⟩, hok12⟩, hok13⟩, hok14⟩, hok15⟩, hok16⟩, hok17⟩, hok18⟩, hok19⟩, hok20⟩, hmain⟩ := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨d0, hdl0, hdu0, hb0⟩ := rterm_boundc hlb hD hpt (bitOf T 0) (l0) (u0) (q0) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok0
    (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  push_cast at hb0
  obtain ⟨d1, hdl1, hdu1, hb1⟩ := rterm_boundc hlb hD hpt (bitOf T 1) (l0 + l1) (u0 + u1) (q0 + q1) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok1
    (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  push_cast at hb1
  obtain ⟨d2, hdl2, hdu2, hb2⟩ := rterm_boundc hlb hD hpt (bitOf T 2) (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok2
    (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  push_cast at hb2
  obtain ⟨d3, hdl3, hdu3, hb3⟩ := rterm_boundc hlb hD hpt (bitOf T 3) (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok3
    (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  push_cast at hb3
  obtain ⟨d4, hdl4, hdu4, hb4⟩ := rterm_boundc hlb hD hpt (bitOf T 4) (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok4
    (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  push_cast at hb4
  obtain ⟨d5, hdl5, hdu5, hb5⟩ := rterm_boundc hlb hD hpt (bitOf T 5) (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42, h52])
  push_cast at hb5
  obtain ⟨d6, hdl6, hdu6, hb6⟩ := rterm_boundc hlb hD hpt (bitOf T 6) (l1) (u1) (q1) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok6
    (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  push_cast at hb6
  obtain ⟨d7, hdl7, hdu7, hb7⟩ := rterm_boundc hlb hD hpt (bitOf T 7) (l1 + l2) (u1 + u2) (q1 + q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok7
    (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  push_cast at hb7
  obtain ⟨d8, hdl8, hdu8, hb8⟩ := rterm_boundc hlb hD hpt (bitOf T 8) (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok8
    (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  push_cast at hb8
  obtain ⟨d9, hdl9, hdu9, hb9⟩ := rterm_boundc hlb hD hpt (bitOf T 9) (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok9
    (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  push_cast at hb9
  obtain ⟨d10, hdl10, hdu10, hb10⟩ := rterm_boundc hlb hD hpt (bitOf T 10) (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok10
    (g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42, h52])
  push_cast at hb10
  obtain ⟨d11, hdl11, hdu11, hb11⟩ := rterm_boundc hlb hD hpt (bitOf T 11) (l2) (u2) (q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok11
    (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  push_cast at hb11
  obtain ⟨d12, hdl12, hdu12, hb12⟩ := rterm_boundc hlb hD hpt (bitOf T 12) (l2 + l3) (u2 + u3) (q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok12
    (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  push_cast at hb12
  obtain ⟨d13, hdl13, hdu13, hb13⟩ := rterm_boundc hlb hD hpt (bitOf T 13) (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok13
    (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  push_cast at hb13
  obtain ⟨d14, hdl14, hdu14, hb14⟩ := rterm_boundc hlb hD hpt (bitOf T 14) (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok14
    (g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42, h52])
  push_cast at hb14
  obtain ⟨d15, hdl15, hdu15, hb15⟩ := rterm_boundc hlb hD hpt (bitOf T 15) (l3) (u3) (q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok15
    (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  push_cast at hb15
  obtain ⟨d16, hdl16, hdu16, hb16⟩ := rterm_boundc hlb hD hpt (bitOf T 16) (l3 + l4) (u3 + u4) (q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok16
    (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  push_cast at hb16
  obtain ⟨d17, hdl17, hdu17, hb17⟩ := rterm_boundc hlb hD hpt (bitOf T 17) (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok17
    (g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h32, h42, h52])
  push_cast at hb17
  obtain ⟨d18, hdl18, hdu18, hb18⟩ := rterm_boundc hlb hD hpt (bitOf T 18) (l4) (u4) (q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok18
    (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  push_cast at hb18
  obtain ⟨d19, hdl19, hdu19, hb19⟩ := rterm_boundc hlb hD hpt (bitOf T 19) (l4 + l5) (u4 + u5) (q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok19
    (g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h42, h52])
  push_cast at hb19
  obtain ⟨d20, hdl20, hdu20, hb20⟩ := rterm_boundc hlb hD hpt (bitOf T 20) (l5) (u5) (q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok20
    (g5) (by push_cast; (try simp only [add_div]); linarith [h51]) (by push_cast; (try simp only [add_div]); linarith [h52])
  push_cast at hb20
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have hl0 : (l0 : ℝ) ≤ q0 := by exact_mod_cast hq01
  have hu0 : (q0 : ℝ) ≤ u0 := by exact_mod_cast hq02
  have hl1 : (l1 : ℝ) ≤ q1 := by exact_mod_cast hq11
  have hu1 : (q1 : ℝ) ≤ u1 := by exact_mod_cast hq12
  have hl2 : (l2 : ℝ) ≤ q2 := by exact_mod_cast hq21
  have hu2 : (q2 : ℝ) ≤ u2 := by exact_mod_cast hq22
  have hl3 : (l3 : ℝ) ≤ q3 := by exact_mod_cast hq31
  have hu3 : (q3 : ℝ) ≤ u3 := by exact_mod_cast hq32
  have hl4 : (l4 : ℝ) ≤ q4 := by exact_mod_cast hq41
  have hu4 : (q4 : ℝ) ≤ u4 := by exact_mod_cast hq42
  have hl5 : (l5 : ℝ) ≤ q5 := by exact_mod_cast hq51
  have hu5 : (q5 : ℝ) ≤ u5 := by exact_mod_cast hq52
  have hP0 : (1000000000 : ℝ) * ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5) ≤ (((48468000000000 + 24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) - (24136977 * tM (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 0 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (48468000000000 + 24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) (24136977 * tM (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 0 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdu0, hdu1, hdu2, hdu3, hdu4, hdu5]
  have hN0 : -((1000000000 : ℝ) * ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5)) ≤ (((24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) - (48468000000000 + 24136977 * tP (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 0 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) (48468000000000 + 24136977 * tP (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 0 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdl0, hdl1, hdl2, hdl3, hdl4, hdl5]
  have hml0 : ((q0 - l0 : ℕ) : ℝ) = (q0 : ℝ) - l0 := Nat.cast_sub hq01
  have hum0 : ((u0 - q0 : ℕ) : ℝ) = (u0 : ℝ) - q0 := Nat.cast_sub hq02
  have ht0 := mterm (e := g0 - (q0 : ℝ) / 32768) (E := ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5)) (lo := ((q0 - l0 : ℕ) : ℝ) / 32768)
    (hi := ((u0 - q0 : ℕ) : ℝ) / 32768) (by rw [hml0]; linarith [h01]) (by rw [hum0]; linarith [h02])
    (by positivity) (by positivity) hP0 hN0 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP1 : (1000000000 : ℝ) * ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10) ≤ (((71367000000000 + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) - (0 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 33894225 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l1) (u1) (q1)) + 44051410 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (71367000000000 + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) (0 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 33894225 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l1) (u1) (q1)) + 44051410 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdu1, hdu2, hdu3, hdu4, hdu5, hdu6, hdu7, hdu8, hdu9, hdu10]
  have hN1 : -((1000000000 : ℝ) * ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10)) ≤ (((0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) - (71367000000000 + 0 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 33894225 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l1) (u1) (q1)) + 44051410 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) (71367000000000 + 0 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 33894225 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l1) (u1) (q1)) + 44051410 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdl1, hdl2, hdl3, hdl4, hdl5, hdl6, hdl7, hdl8, hdl9, hdl10]
  have hml1 : ((q1 - l1 : ℕ) : ℝ) = (q1 : ℝ) - l1 := Nat.cast_sub hq11
  have hum1 : ((u1 - q1 : ℕ) : ℝ) = (u1 : ℝ) - q1 := Nat.cast_sub hq12
  have ht1 := mterm (e := g1 - (q1 : ℝ) / 32768) (E := ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10)) (lo := ((q1 - l1 : ℕ) : ℝ) / 32768)
    (hi := ((u1 - q1 : ℕ) : ℝ) / 32768) (by rw [hml1]; linarith [h11]) (by rw [hum1]; linarith [h12])
    (by positivity) (by positivity) hP1 hN1 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP2 : (1000000000 : ℝ) * ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14) ≤ (((82339000000000 + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) - (23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 44051410 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 41968798 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l2) (u2) (q2)) + 111897180 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (82339000000000 + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) (23349596 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 44051410 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 41968798 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l2) (u2) (q2)) + 111897180 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdu2, hdu3, hdu4, hdu5, hdu7, hdu8, hdu9, hdu10, hdu11, hdu12, hdu13, hdu14]
  have hN2 : -((1000000000 : ℝ) * ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14)) ≤ (((23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) - (82339000000000 + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 44051410 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 41968798 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l2) (u2) (q2)) + 111897180 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) (82339000000000 + 23349596 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 44051410 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 41968798 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l2) (u2) (q2)) + 111897180 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)))
    push_cast at this
    linarith [hdl2, hdl3, hdl4, hdl5, hdl7, hdl8, hdl9, hdl10, hdl11, hdl12, hdl13, hdl14]
  have hml2 : ((q2 - l2 : ℕ) : ℝ) = (q2 : ℝ) - l2 := Nat.cast_sub hq21
  have hum2 : ((u2 - q2 : ℕ) : ℝ) = (u2 : ℝ) - q2 := Nat.cast_sub hq22
  have ht2 := mterm (e := g2 - (q2 : ℝ) / 32768) (E := ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14)) (lo := ((q2 - l2 : ℕ) : ℝ) / 32768)
    (hi := ((u2 - q2 : ℕ) : ℝ) / 32768) (by rw [hml2]; linarith [h21]) (by rw [hum2]; linarith [h22])
    (by positivity) (by positivity) hP2 hN2 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP3 : (1000000000 : ℝ) * ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17) ≤ (((82339000000000 + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) - (100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 111897180 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 41968798 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l3) (u3) (q3)) + 44051410 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (82339000000000 + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) (100000000 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 76650404 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 111897180 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 41968798 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l3) (u3) (q3)) + 44051410 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)))
    push_cast at this
    linarith [hdu3, hdu4, hdu5, hdu8, hdu9, hdu10, hdu12, hdu13, hdu14, hdu15, hdu16, hdu17]
  have hN3 : -((1000000000 : ℝ) * ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17)) ≤ (((100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) - (82339000000000 + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 111897180 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 41968798 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l3) (u3) (q3)) + 44051410 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) (82339000000000 + 100000000 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 76650404 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 111897180 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 41968798 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l3) (u3) (q3)) + 44051410 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)))
    push_cast at this
    linarith [hdl3, hdl4, hdl5, hdl8, hdl9, hdl10, hdl12, hdl13, hdl14, hdl15, hdl16, hdl17]
  have hml3 : ((q3 - l3 : ℕ) : ℝ) = (q3 : ℝ) - l3 := Nat.cast_sub hq31
  have hum3 : ((u3 - q3 : ℕ) : ℝ) = (u3 : ℝ) - q3 := Nat.cast_sub hq32
  have ht3 := mterm (e := g3 - (q3 : ℝ) / 32768) (E := ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17)) (lo := ((q3 - l3 : ℕ) : ℝ) / 32768)
    (hi := ((u3 - q3 : ℕ) : ℝ) / 32768) (by rw [hml3]; linarith [h31]) (by rw [hum3]; linarith [h32])
    (by positivity) (by positivity) hP3 hN3 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP4 : (1000000000 : ℝ) * ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19) ≤ (((71367000000000 + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) - (100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 44051410 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 33894225 * tM (bitOf T 18) (selXf (bitOf T 18) top bk pb (l4) (u4) (q4)) + 0 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (71367000000000 + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) (100000000 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 0 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 76650404 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 44051410 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 33894225 * tM (bitOf T 18) (selXf (bitOf T 18) top bk pb (l4) (u4) (q4)) + 0 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)))
    push_cast at this
    linarith [hdu4, hdu5, hdu9, hdu10, hdu13, hdu14, hdu16, hdu17, hdu18, hdu19]
  have hN4 : -((1000000000 : ℝ) * ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19)) ≤ (((100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) - (71367000000000 + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 44051410 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 33894225 * tP (bitOf T 18) (selXf (bitOf T 18) top bk pb (l4) (u4) (q4)) + 0 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5))) : ℕ) : ℝ) := by
    have := natsub_ge (100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) (71367000000000 + 100000000 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 0 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 76650404 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 44051410 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 33894225 * tP (bitOf T 18) (selXf (bitOf T 18) top bk pb (l4) (u4) (q4)) + 0 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)))
    push_cast at this
    linarith [hdl4, hdl5, hdl9, hdl10, hdl13, hdl14, hdl16, hdl17, hdl18, hdl19]
  have hml4 : ((q4 - l4 : ℕ) : ℝ) = (q4 : ℝ) - l4 := Nat.cast_sub hq41
  have hum4 : ((u4 - q4 : ℕ) : ℝ) = (u4 : ℝ) - q4 := Nat.cast_sub hq42
  have ht4 := mterm (e := g4 - (q4 : ℝ) / 32768) (E := ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19)) (lo := ((q4 - l4 : ℕ) : ℝ) / 32768)
    (hi := ((u4 - q4 : ℕ) : ℝ) / 32768) (by rw [hml4]; linarith [h41]) (by rw [hum4]; linarith [h42])
    (by positivity) (by positivity) hP4 hN4 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP5 : (1000000000 : ℝ) * ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20) ≤ (((48468000000000 + 200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) - (200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 0 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 24136977 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l5) (u5) (q5))) : ℕ) : ℝ) := by
    have := natsub_ge (48468000000000 + 200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) (200000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 23349596 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 0 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 24136977 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l5) (u5) (q5)))
    push_cast at this
    linarith [hdu5, hdu10, hdu14, hdu17, hdu19, hdu20]
  have hN5 : -((1000000000 : ℝ) * ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20)) ≤ (((200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) - (48468000000000 + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 0 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 24136977 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l5) (u5) (q5))) : ℕ) : ℝ) := by
    have := natsub_ge (200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) (48468000000000 + 200000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 23349596 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 0 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 24136977 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l5) (u5) (q5)))
    push_cast at this
    linarith [hdl5, hdl10, hdl14, hdl17, hdl19, hdl20]
  have hml5 : ((q5 - l5 : ℕ) : ℝ) = (q5 : ℝ) - l5 := Nat.cast_sub hq51
  have hum5 : ((u5 - q5 : ℕ) : ℝ) = (u5 : ℝ) - q5 := Nat.cast_sub hq52
  have ht5 := mterm (e := g5 - (q5 : ℝ) / 32768) (E := ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20)) (lo := ((q5 - l5 : ℕ) : ℝ) / 32768)
    (hi := ((u5 - q5 : ℕ) : ℝ) / 32768) (by rw [hml5]; linarith [h51]) (by rw [hum5]; linarith [h52])
    (by positivity) (by positivity) hP5 hN5 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5] at hq
  simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5] at ht0 ht1 ht2 ht3 ht4 ht5
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5
      + (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5)) * SA
      = 48468 * g0 + 71367 * g1 + 82339 * g2 + 82339 * g3 + 71367 * g4 + 48468 * g5 + 24136977 * wfun (g0) + 0 * wfun (g0 + g1) + 23349596 * wfun (g0 + g1 + g2) + 100000000 * wfun (g0 + g1 + g2 + g3) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 33894225 * wfun (g1) + 44051410 * wfun (g1 + g2) + 76650404 * wfun (g1 + g2 + g3) + 0 * wfun (g1 + g2 + g3 + g4) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5) + 41968798 * wfun (g2) + 111897180 * wfun (g2 + g3) + 76650404 * wfun (g2 + g3 + g4) + 100000000 * wfun (g2 + g3 + g4 + g5) + 41968798 * wfun (g3) + 44051410 * wfun (g3 + g4) + 23349596 * wfun (g3 + g4 + g5) + 33894225 * wfun (g4) + 0 * wfun (g4 + g5) + 24136977 * wfun (g5) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 789487 := by norm_num [cN]
  rw [hcN]
  linarith [hq, ht0, ht1, ht2, ht3, ht4, ht5, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 24136977), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 111897180), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 24136977)]

theorem covered_of_ctest {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ) (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T = true) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  exact Or.inl (ctest_sound hlb hD hpt hR l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T h g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)

/-- a box split on gap 0 at `q` is covered when both halves are -/
theorem covered_split0 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (hB : Covered q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g0 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 hq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  · exact hB g0 g1 g2 g3 g4 g5 hq h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52

/-- a box split on gap 1 at `q` is covered when both halves are -/
theorem covered_split1 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5) (hB : Covered l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g1 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 h02 h11 hq h21 h22 h31 h32 h41 h42 h51 h52
  · exact hB g0 g1 g2 g3 g4 g5 h01 h02 hq h12 h21 h22 h31 h32 h41 h42 h51 h52

/-- a box split on gap 2 at `q` is covered when both halves are -/
theorem covered_split2 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5) (hB : Covered l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g2 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 hq h31 h32 h41 h42 h51 h52
  · exact hB g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 hq h22 h31 h32 h41 h42 h51 h52

/-- a box split on gap 3 at `q` is covered when both halves are -/
theorem covered_split3 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5) (hB : Covered l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g3 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 hq h41 h42 h51 h52
  · exact hB g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 hq h32 h41 h42 h51 h52

/-- a box split on gap 4 at `q` is covered when both halves are -/
theorem covered_split4 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g4 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 hq h51 h52
  · exact hB g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 hq h42 h51 h52

/-- a box split on gap 5 at `q` is covered when both halves are -/
theorem covered_split5 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  rcases le_total g5 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 hq
  · exact hB g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 hq h52

/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ, f pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0 → Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5

theorem split0_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split0 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) 0
  · have h' : ih (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split0 _ hA (hih _ (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h')
  · exact absurd (by simp only [hp]) h

theorem split1_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split1 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5) l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split1 _ hA (hih _ l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 h')
  · exact absurd (by simp only [hp]) h

theorem split2_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split2 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5) l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split2 _ hA (hih _ l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 h')
  · exact absurd (by simp only [hp]) h

theorem split3_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split3 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5) l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split3 _ hA (hih _ l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 h')
  · exact absurd (by simp only [hp]) h

theorem split4_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split4 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5) l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split4 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 h')
  · exact absurd (by simp only [hp]) h

theorem split5_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold split5 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1)) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1)) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split5 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 h')
  · exact absurd (by simp only [hp]) h

theorem splitAx_sound {ih : WF} (hih : WalkOK ih) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : splitAx ih pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold splitAx at h
  cases ha0 : Nat.beq ax 0
  · rw [ha0] at h
    cases ha1 : Nat.beq ax 1
    · rw [ha1] at h
      cases ha2 : Nat.beq ax 2
      · rw [ha2] at h
        cases ha3 : Nat.beq ax 3
        · rw [ha3] at h
          cases ha4 : Nat.beq ax 4
          · rw [ha4] at h
            exact split5_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
          · rw [ha4] at h; exact split4_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
        · rw [ha3] at h; exact split3_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
      · rw [ha2] at h; exact split2_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
    · rw [ha1] at h; exact split1_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
  · rw [ha0] at h; exact split0_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h

theorem sleaf_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  unfold sleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem cleaf_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  unfold cleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- the basin boxes are covered -/
def BasOK (bas : List Bx) : Prop := ∀ b ∈ bas, Covered b.l0 b.u0 b.l1 b.u1 b.l2 b.u2 b.l3 b.u3 b.l4 b.u4 b.l5 b.u5

theorem inBas_sound {bas : List Bx} (hbas : BasOK bas) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold inBas at h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, hin⟩ := h
  simp only [Bool.and_eq_true, Nat.ble_eq] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbl0, hbu0⟩, hbl1⟩, hbu1⟩, hbl2⟩, hbu2⟩, hbl3⟩, hbu3⟩, hbl4⟩, hbu4⟩, hbl5⟩, hbu5⟩ := hin
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  exact hbas b hb g0 g1 g2 g3 g4 g5 (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl0) (by norm_num [SC])) h01) (le_trans h02 (div_le_div_of_nonneg_right (by exact_mod_cast hbu0) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl1) (by norm_num [SC])) h11) (le_trans h12 (div_le_div_of_nonneg_right (by exact_mod_cast hbu1) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl2) (by norm_num [SC])) h21) (le_trans h22 (div_le_div_of_nonneg_right (by exact_mod_cast hbu2) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl3) (by norm_num [SC])) h31) (le_trans h32 (div_le_div_of_nonneg_right (by exact_mod_cast hbu3) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl4) (by norm_num [SC])) h41) (le_trans h42 (div_le_div_of_nonneg_right (by exact_mod_cast hbu4) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl5) (by norm_num [SC])) h51) (le_trans h52 (div_le_div_of_nonneg_right (by exact_mod_cast hbu5) (by norm_num [SC])))

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ)
    (h : leafStep top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold leafStep at h
  cases hs : Nat.ble (Nat.add u5 1) l0
  · rw [hs] at h
    cases hk0 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0
    · rw [hk0] at h
      cases hk1 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1
      · rw [hk1] at h
        cases hk2 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2
        · rw [hk2] at h
          cases hl : cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
          · rw [hl] at h; exact absurd rfl h
          · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
            exact Or.inl (cleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
        · rw [hk2] at h
          cases hl : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
          · rw [hl] at h; exact absurd rfl h
          · exact inBas_sound hbas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl
      · rw [hk1] at h
        cases hl : sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
        · rw [hl] at h; exact absurd rfl h
        · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
          exact Or.inl (sleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
    · rw [hk0] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
      · rw [hl] at h; exact absurd rfl h
      · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
        exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
  · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
    right
    have hsk : u5 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u5 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R C bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R C bas pos (Nat.shiftRight bits pos) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (splitAx (walk top bk tD bD pb R C bas bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR hbas pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 e : ℕ)
    (h : walk top bk tD bD pb R C bas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 :=
  walk_sound hlb hD hpt hR hbas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (h ▸ he)


/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear segment's own integer
cell bound must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WZ ≥ cN * SW` -/
def coverCheck (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b) && decide (b < KB)
        && (!cl || Nat.ble (cN * SW) (aAdjN * CellN.WZ ⟨a * KB + b, 0⟩))
        && coverCheck aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

theorem cover_sound (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        rw [Nat.ble_eq] at hcl
        have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
          simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
        have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
          simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
        have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSA : (0:ℝ) < SA := by norm_num [SA]
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        rw [div_le_iff₀ hSA]
        have hm2 : (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
        rw [e]
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdjN : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (cover0 cover1 cover2 cover3 cover4 cover5 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 S5 : ℕ)
    (hS0 : cN * SC ≤ 48468 * S0) (hS1 : cN * SC ≤ 71367 * S1) (hS2 : cN * SC ≤ 82339 * S2) (hS3 : cN * SC ≤ 82339 * S3) (hS4 : cN * SC ≤ 71367 * S4) (hS5 : cN * SC ≤ 48468 * S5)
    (hcov0 : coverCheck 24136977 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 33894225 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 41968798 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 41968798 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 33894225 (SC / 2) S4 cover4 = true) (hcov5 : coverCheck 24136977 (SC / 2) S5 cover5 = true)
    (hwin : cN * 4 ≤ 24136977)
    (hrun : ∀ i0 i1 i2 i3 i4 i5, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length → i5 < (badOf cover5).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2 ((badOf cover5).getD i5 (0, 0)).1 ((badOf cover5).getD i5 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → 0 ≤ g5 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 ∨ g5 < g0 := by
  intro g0 g1 g2 g3 g4 g5 hg0 hg1 hg2 hg3 hg4 hg5
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5 with hLin
  set Wt : ℝ := (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5) with hWt
  have hG : G g0 g1 g2 g3 g4 g5 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (48468 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (71367 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (82339 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (82339 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (71367 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have hb50 : (0:ℝ) ≤ (48468 / (SA:ℝ)) * g5 := mul_nonneg (by positivity) hg5
  have ha00 : (0:ℝ) ≤ (24136977 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (33894225 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (44051410 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (41968798 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (111897180 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha150 : (0:ℝ) ≤ (41968798 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha160 : (0:ℝ) ≤ (44051410 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha170 : (0:ℝ) ≤ (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha180 : (0:ℝ) ≤ (33894225 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have ha190 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha200 : (0:ℝ) ≤ (24136977 / (SA:ℝ)) * wfun (g5) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40, hb50]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have hbL0 : (48468 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40, hb50]
  have hbL1 : (71367 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40, hb50]
  have hbL2 : (82339 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40, hb50]
  have hbL3 : (82339 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40, hb50]
  have hbL4 : (71367 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb50]
  have hbL5 : (48468 / (SA:ℝ)) * g5 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have haW0 : (24136977 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW1 : (0 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW2 : (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW3 : (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW4 : (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW5 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW6 : (33894225 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW7 : (44051410 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW8 : (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW9 : (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW10 : (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW11 : (41968798 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW12 : (111897180 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW13 : (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW14 : (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha150, ha160, ha170, ha180, ha190, ha200]
  have haW15 : (41968798 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha160, ha170, ha180, ha190, ha200]
  have haW16 : (44051410 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha170, ha180, ha190, ha200]
  have haW17 : (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha180, ha190, ha200]
  have haW18 : (33894225 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha190, ha200]
  have haW19 : (0 / (SA:ℝ)) * wfun (g4 + g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha200]
  have haW20 : (24136977 / (SA:ℝ)) * wfun (g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (48468 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (48468 / (SA:ℝ)) * g0 * SA = 48468 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 48468 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 48468 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 48468 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (24136977 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (24136977 / (SA:ℝ)) * wfun g0 * SA = 24136977 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 24136977)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW0, hLin0]
  rcases cover_sound _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · left; rw [hG]; linarith [hclear0, haW0, hLin0]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (71367 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (71367 / (SA:ℝ)) * g1 * SA = 71367 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 71367 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 71367 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 71367 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (33894225 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (33894225 / (SA:ℝ)) * wfun g1 * SA = 33894225 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 33894225)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW6, hLin0]
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW6, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (82339 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (82339 / (SA:ℝ)) * g2 * SA = 82339 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 82339 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 82339 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 82339 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (41968798 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (41968798 / (SA:ℝ)) * wfun g2 * SA = 41968798 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 41968798)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW11, hLin0]
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW11, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (82339 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (82339 / (SA:ℝ)) * g3 * SA = 82339 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 82339 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 82339 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 82339 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (41968798 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (41968798 / (SA:ℝ)) * wfun g3 * SA = 41968798 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 41968798)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW15, hLin0]
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW15, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (71367 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (71367 / (SA:ℝ)) * g4 * SA = 71367 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 71367 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 71367 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 71367 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (33894225 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (33894225 / (SA:ℝ)) * wfun g4 * SA = 33894225 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 33894225)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW18, hLin0]
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW18, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  -- gap 5: beyond the cutoff the pressure alone pays
  by_cases hcut5 : (S5 : ℝ) / SC ≤ g5
  · have h1 : (cN : ℝ) / SA ≤ (48468 / (SA:ℝ)) * g5 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS5; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (48468 / (SA:ℝ)) * g5 * SA = 48468 * g5 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 48468 * S5 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 48468 * ((S5 : ℝ) / SC) := by ring
        _ ≤ 48468 * g5 := mul_le_mul_of_nonneg_left hcut5 (by norm_num)
    left; rw [hG]; linarith [h1, hbL5, hWt0]
  push_neg at hcut5
  rcases le_total g5 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin5 | hwin5
  · have hw19 := wfun_window g5 hg5 (by rw [hhalf] at hwin5; exact hwin5)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (24136977 / (SA:ℝ)) * wfun g5 := by
      rw [div_le_iff₀ hSA]
      have e : (24136977 / (SA:ℝ)) * wfun g5 * SA = 24136977 * wfun g5 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 24136977)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW20, hLin0]
  rcases cover_sound _ cover5 (SC / 2) S5 hcov5 g5 hwin5 hcut5 with hclear5 | ⟨s5, hs5, he5, hb51, hb52⟩
  · left; rw [hG]; linarith [hclear5, haW20, hLin0]
  obtain ⟨i5, hi5, hsi5⟩ := List.mem_iff_getElem.mp (badOf_mem hs5 he5)
  have hb51' : (((badOf cover5).getD i5 (0, 0)).1 : ℝ) / SC ≤ g5 := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb51
  have hb52' : g5 ≤ (((badOf cover5).getD i5 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb52
  exact hrun i0 i1 i2 i3 i4 i5 hi0 hi1 hi2 hi3 hi4 hi5 g0 g1 g2 g3 g4 g5 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42' hb51' hb52'

end AMW.Cert.AMS02

end
