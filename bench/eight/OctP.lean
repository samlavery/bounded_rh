import MinCore

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 100

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.OctT

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD

def SA : ℕ := 100000000
def cN : ℕ := 701466

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 g5 g6 : ℝ) : ℝ :=
  (32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
    + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb3_t` (U = 10¹⁰; three-piece pyramid reads), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32954 l0) (Nat.mul 57979 l1)) (Nat.mul 68753 l2)) (Nat.mul 80628 l3)) (Nat.mul 68753 l4)) (Nat.mul 57979 l5)) (Nat.mul 32954 l6)) 10000000000
  ee 229856378880000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 541650026496 (lb3 top bk l0 u0))
  ee 229856378880000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 318222008320 (lb3 top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 229856378880000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 0 (lb3 top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 229856378880000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 3271643136000 (lb3 top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 229856378880000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 2148619976704 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 229856378880000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)))
  ee 229856378880000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 6553600000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6)))
  ee 229856378880000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 899641212928 (lb3 top bk l1 u1))
  ee 229856378880000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1462873620480 (lb3 top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 229856378880000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 2221964689408 (lb3 top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 229856378880000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 5156864000 (lb3 top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 229856378880000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 2256360046592 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)))
  ee 229856378880000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 3276800000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6)))
  ee 229856378880000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 1145183174656 (lb3 top bk l2 u2))
  ee 229856378880000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 1495704371200 (lb3 top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 229856378880000000000 s15 (
  let s16 := Nat.add s15 (Nat.mul 2109670621184 (lb3 top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 229856378880000000000 s16 (
  let s17 := Nat.add s16 (Nat.mul 5156864000 (lb3 top bk (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)))
  ee 229856378880000000000 s17 (
  let s18 := Nat.add s17 (Nat.mul 2148619976704 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6)))
  ee 229856378880000000000 s18 (
  let s19 := Nat.add s18 (Nat.mul 1380651171840 (lb3 top bk l3 u3))
  ee 229856378880000000000 s19 (
  let s20 := Nat.add s19 (Nat.mul 1495704371200 (lb3 top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 229856378880000000000 s20 (
  let s21 := Nat.add s20 (Nat.mul 2221964689408 (lb3 top bk (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)))
  ee 229856378880000000000 s21 (
  let s22 := Nat.add s21 (Nat.mul 3271643136000 (lb3 top bk (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6)))
  ee 229856378880000000000 s22 (
  let s23 := Nat.add s22 (Nat.mul 1145183174656 (lb3 top bk l4 u4))
  ee 229856378880000000000 s23 (
  let s24 := Nat.add s23 (Nat.mul 1462873620480 (lb3 top bk (Nat.add l4 l5) (Nat.add u4 u5)))
  ee 229856378880000000000 s24 (
  let s25 := Nat.add s24 (Nat.mul 0 (lb3 top bk (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6)))
  ee 229856378880000000000 s25 (
  let s26 := Nat.add s25 (Nat.mul 899641212928 (lb3 top bk l5 u5))
  ee 229856378880000000000 s26 (
  let s27 := Nat.add s26 (Nat.mul 318222008320 (lb3 top bk (Nat.add l5 l6) (Nat.add u5 u6)))
  ee 229856378880000000000 s27 (
  let s28 := Nat.add s27 (Nat.mul 541650026496 (lb3 top bk l6 u6))
  Nat.ble 229856378880000000000 s28))))))))))))))))))))))))))))

/-- bit `t` of `T` -/
def bitOf (T t : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight T t) 1) 1


/-- the slope inequality at the point `q` with expansion set `T`, given the per-term reads and convexity flags:
`cN·SC·U + (U/U1)·(Σ_r ((q_r − l_r)·Pos_r + (u_r − q_r)·Neg_r) + Σ_t a_t·charge_t) ≤ U·Σ b_r q_r + SC·Σ a_t·val_t` -/
def cscheck (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (q0 q1 q2 q3 q4 q5 q6 : ℕ) (T : ℕ) (x0 eu0 ed0 : ℕ) (v0 : Bool) (x1 eu1 ed1 : ℕ) (v1 : Bool) (x2 eu2 ed2 : ℕ) (v2 : Bool) (x3 eu3 ed3 : ℕ) (v3 : Bool) (x4 eu4 ed4 : ℕ) (v4 : Bool) (x5 eu5 ed5 : ℕ) (v5 : Bool) (x6 eu6 ed6 : ℕ) (v6 : Bool) (x7 eu7 ed7 : ℕ) (v7 : Bool) (x8 eu8 ed8 : ℕ) (v8 : Bool) (x9 eu9 ed9 : ℕ) (v9 : Bool) (x10 eu10 ed10 : ℕ) (v10 : Bool) (x11 eu11 ed11 : ℕ) (v11 : Bool) (x12 eu12 ed12 : ℕ) (v12 : Bool) (x13 eu13 ed13 : ℕ) (v13 : Bool) (x14 eu14 ed14 : ℕ) (v14 : Bool) (x15 eu15 ed15 : ℕ) (v15 : Bool) (x16 eu16 ed16 : ℕ) (v16 : Bool) (x17 eu17 ed17 : ℕ) (v17 : Bool) (x18 eu18 ed18 : ℕ) (v18 : Bool) (x19 eu19 ed19 : ℕ) (v19 : Bool) (x20 eu20 ed20 : ℕ) (v20 : Bool) (x21 eu21 ed21 : ℕ) (v21 : Bool) (x22 eu22 ed22 : ℕ) (v22 : Bool) (x23 eu23 ed23 : ℕ) (v23 : Bool) (x24 eu24 ed24 : ℕ) (v24 : Bool) (x25 eu25 ed25 : ℕ) (v25 : Bool) (x26 eu26 ed26 : ℕ) (v26 : Bool) (x27 eu27 ed27 : ℕ) (v27 : Bool) : Bool :=
  (((((((((((((((((((((((((((((((((((((((((Nat.ble l0 q0 && Nat.ble q0 u0) && Nat.ble l1 q1) && Nat.ble q1 u1) && Nat.ble l2 q2) && Nat.ble q2 u2) && Nat.ble l3 q3) && Nat.ble q3 u3) && Nat.ble l4 q4) && Nat.ble q4 u4) && Nat.ble l5 q5) && Nat.ble q5 u5) && Nat.ble l6 q6) && Nat.ble q6 u6) && rtok v0 (bitOf T 0) l0 u0 q0 x0 eu0 ed0) && rtok v1 (bitOf T 1) (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1) x1 eu1 ed1) && rtok v2 (bitOf T 2) (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2) x2 eu2 ed2) && rtok v3 (bitOf T 3) (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) x3 eu3 ed3) && rtok v4 (bitOf T 4) (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) x4 eu4 ed4) && rtok v5 (bitOf T 5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) x5 eu5 ed5) && rtok v6 (bitOf T 6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) q6) x6 eu6 ed6) && rtok v7 (bitOf T 7) l1 u1 q1 x7 eu7 ed7) && rtok v8 (bitOf T 8) (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2) x8 eu8 ed8) && rtok v9 (bitOf T 9) (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3) x9 eu9 ed9) && rtok v10 (bitOf T 10) (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) x10 eu10 ed10) && rtok v11 (bitOf T 11) (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) x11 eu11 ed11) && rtok v12 (bitOf T 12) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) q6) x12 eu12 ed12) && rtok v13 (bitOf T 13) l2 u2 q2 x13 eu13 ed13) && rtok v14 (bitOf T 14) (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3) x14 eu14 ed14) && rtok v15 (bitOf T 15) (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4) x15 eu15 ed15) && rtok v16 (bitOf T 16) (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) x16 eu16 ed16) && rtok v17 (bitOf T 17) (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) q6) x17 eu17 ed17) && rtok v18 (bitOf T 18) l3 u3 q3 x18 eu18 ed18) && rtok v19 (bitOf T 19) (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4) x19 eu19 ed19) && rtok v20 (bitOf T 20) (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5) x20 eu20 ed20) && rtok v21 (bitOf T 21) (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.add (Nat.add (Nat.add q3 q4) q5) q6) x21 eu21 ed21) && rtok v22 (bitOf T 22) l4 u4 q4 x22 eu22 ed22) && rtok v23 (bitOf T 23) (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5) x23 eu23 ed23) && rtok v24 (bitOf T 24) (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6) (Nat.add (Nat.add q4 q5) q6) x24 eu24 ed24) && rtok v25 (bitOf T 25) l5 u5 q5 x25 eu25 ed25) && rtok v26 (bitOf T 26) (Nat.add l5 l6) (Nat.add u5 u6) (Nat.add q5 q6) x26 eu26 ed26) && rtok v27 (bitOf T 27) l6 u6 q6 x27 eu27 ed27) && Nat.ble (Nat.add 229856378880000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub q0 l0) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 32954000000000 (Nat.mul 16529847 (tK (bitOf T 0)))) (Nat.mul 9711365 (tK (bitOf T 1)))) (Nat.mul 0 (tK (bitOf T 2)))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (tM (bitOf T 0) x0)) (Nat.mul 9711365 (tM (bitOf T 1) x1))) (Nat.mul 0 (tM (bitOf T 2) x2))) (Nat.mul 99842625 (tM (bitOf T 3) x3))) (Nat.mul 65570678 (tM (bitOf T 4) x4))) (Nat.mul 100000000 (tM (bitOf T 5) x5))) (Nat.mul 200000000 (tM (bitOf T 6) x6))))) (Nat.mul (Nat.sub u0 q0) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (tK (bitOf T 0))) (Nat.mul 9711365 (tK (bitOf T 1)))) (Nat.mul 0 (tK (bitOf T 2)))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 32954000000000 (Nat.mul 16529847 (tP (bitOf T 0) x0))) (Nat.mul 9711365 (tP (bitOf T 1) x1))) (Nat.mul 0 (tP (bitOf T 2) x2))) (Nat.mul 99842625 (tP (bitOf T 3) x3))) (Nat.mul 65570678 (tP (bitOf T 4) x4))) (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6)))))) (Nat.mul (Nat.sub q1 l1) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 57979000000000 (Nat.mul 9711365 (tK (bitOf T 1)))) (Nat.mul 0 (tK (bitOf T 2)))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 27454871 (tK (bitOf T 7)))) (Nat.mul 44643360 (tK (bitOf T 8)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 9711365 (tM (bitOf T 1) x1)) (Nat.mul 0 (tM (bitOf T 2) x2))) (Nat.mul 99842625 (tM (bitOf T 3) x3))) (Nat.mul 65570678 (tM (bitOf T 4) x4))) (Nat.mul 100000000 (tM (bitOf T 5) x5))) (Nat.mul 200000000 (tM (bitOf T 6) x6))) (Nat.mul 27454871 (tM (bitOf T 7) x7))) (Nat.mul 44643360 (tM (bitOf T 8) x8))) (Nat.mul 67808981 (tM (bitOf T 9) x9))) (Nat.mul 157375 (tM (bitOf T 10) x10))) (Nat.mul 68858644 (tM (bitOf T 11) x11))) (Nat.mul 100000000 (tM (bitOf T 12) x12)))))) (Nat.mul (Nat.sub u1 q1) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 9711365 (tK (bitOf T 1))) (Nat.mul 0 (tK (bitOf T 2)))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 27454871 (tK (bitOf T 7)))) (Nat.mul 44643360 (tK (bitOf T 8)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 57979000000000 (Nat.mul 9711365 (tP (bitOf T 1) x1))) (Nat.mul 0 (tP (bitOf T 2) x2))) (Nat.mul 99842625 (tP (bitOf T 3) x3))) (Nat.mul 65570678 (tP (bitOf T 4) x4))) (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 27454871 (tP (bitOf T 7) x7))) (Nat.mul 44643360 (tP (bitOf T 8) x8))) (Nat.mul 67808981 (tP (bitOf T 9) x9))) (Nat.mul 157375 (tP (bitOf T 10) x10))) (Nat.mul 68858644 (tP (bitOf T 11) x11))) (Nat.mul 100000000 (tP (bitOf T 12) x12)))))) (Nat.mul (Nat.sub q2 l2) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 68753000000000 (Nat.mul 0 (tK (bitOf T 2)))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 44643360 (tK (bitOf T 8)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 34948217 (tK (bitOf T 13)))) (Nat.mul 45645275 (tK (bitOf T 14)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 0 (tM (bitOf T 2) x2)) (Nat.mul 99842625 (tM (bitOf T 3) x3))) (Nat.mul 65570678 (tM (bitOf T 4) x4))) (Nat.mul 100000000 (tM (bitOf T 5) x5))) (Nat.mul 200000000 (tM (bitOf T 6) x6))) (Nat.mul 44643360 (tM (bitOf T 8) x8))) (Nat.mul 67808981 (tM (bitOf T 9) x9))) (Nat.mul 157375 (tM (bitOf T 10) x10))) (Nat.mul 68858644 (tM (bitOf T 11) x11))) (Nat.mul 100000000 (tM (bitOf T 12) x12))) (Nat.mul 34948217 (tM (bitOf T 13) x13))) (Nat.mul 45645275 (tM (bitOf T 14) x14))) (Nat.mul 64382038 (tM (bitOf T 15) x15))) (Nat.mul 157375 (tM (bitOf T 16) x16))) (Nat.mul 65570678 (tM (bitOf T 17) x17)))))) (Nat.mul (Nat.sub u2 q2) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 0 (tK (bitOf T 2))) (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 44643360 (tK (bitOf T 8)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 34948217 (tK (bitOf T 13)))) (Nat.mul 45645275 (tK (bitOf T 14)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 68753000000000 (Nat.mul 0 (tP (bitOf T 2) x2))) (Nat.mul 99842625 (tP (bitOf T 3) x3))) (Nat.mul 65570678 (tP (bitOf T 4) x4))) (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 44643360 (tP (bitOf T 8) x8))) (Nat.mul 67808981 (tP (bitOf T 9) x9))) (Nat.mul 157375 (tP (bitOf T 10) x10))) (Nat.mul 68858644 (tP (bitOf T 11) x11))) (Nat.mul 100000000 (tP (bitOf T 12) x12))) (Nat.mul 34948217 (tP (bitOf T 13) x13))) (Nat.mul 45645275 (tP (bitOf T 14) x14))) (Nat.mul 64382038 (tP (bitOf T 15) x15))) (Nat.mul 157375 (tP (bitOf T 16) x16))) (Nat.mul 65570678 (tP (bitOf T 17) x17)))))) (Nat.mul (Nat.sub q3 l3) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 80628000000000 (Nat.mul 99842625 (tK (bitOf T 3)))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 45645275 (tK (bitOf T 14)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 42134130 (tK (bitOf T 18)))) (Nat.mul 45645275 (tK (bitOf T 19)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (tM (bitOf T 3) x3)) (Nat.mul 65570678 (tM (bitOf T 4) x4))) (Nat.mul 100000000 (tM (bitOf T 5) x5))) (Nat.mul 200000000 (tM (bitOf T 6) x6))) (Nat.mul 67808981 (tM (bitOf T 9) x9))) (Nat.mul 157375 (tM (bitOf T 10) x10))) (Nat.mul 68858644 (tM (bitOf T 11) x11))) (Nat.mul 100000000 (tM (bitOf T 12) x12))) (Nat.mul 45645275 (tM (bitOf T 14) x14))) (Nat.mul 64382038 (tM (bitOf T 15) x15))) (Nat.mul 157375 (tM (bitOf T 16) x16))) (Nat.mul 65570678 (tM (bitOf T 17) x17))) (Nat.mul 42134130 (tM (bitOf T 18) x18))) (Nat.mul 45645275 (tM (bitOf T 19) x19))) (Nat.mul 67808981 (tM (bitOf T 20) x20))) (Nat.mul 99842625 (tM (bitOf T 21) x21)))))) (Nat.mul (Nat.sub u3 q3) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (tK (bitOf T 3))) (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 67808981 (tK (bitOf T 9)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 45645275 (tK (bitOf T 14)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 42134130 (tK (bitOf T 18)))) (Nat.mul 45645275 (tK (bitOf T 19)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 80628000000000 (Nat.mul 99842625 (tP (bitOf T 3) x3))) (Nat.mul 65570678 (tP (bitOf T 4) x4))) (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 67808981 (tP (bitOf T 9) x9))) (Nat.mul 157375 (tP (bitOf T 10) x10))) (Nat.mul 68858644 (tP (bitOf T 11) x11))) (Nat.mul 100000000 (tP (bitOf T 12) x12))) (Nat.mul 45645275 (tP (bitOf T 14) x14))) (Nat.mul 64382038 (tP (bitOf T 15) x15))) (Nat.mul 157375 (tP (bitOf T 16) x16))) (Nat.mul 65570678 (tP (bitOf T 17) x17))) (Nat.mul 42134130 (tP (bitOf T 18) x18))) (Nat.mul 45645275 (tP (bitOf T 19) x19))) (Nat.mul 67808981 (tP (bitOf T 20) x20))) (Nat.mul 99842625 (tP (bitOf T 21) x21)))))) (Nat.mul (Nat.sub q4 l4) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 68753000000000 (Nat.mul 65570678 (tK (bitOf T 4)))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 45645275 (tK (bitOf T 19)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 34948217 (tK (bitOf T 22)))) (Nat.mul 44643360 (tK (bitOf T 23)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 65570678 (tM (bitOf T 4) x4)) (Nat.mul 100000000 (tM (bitOf T 5) x5))) (Nat.mul 200000000 (tM (bitOf T 6) x6))) (Nat.mul 157375 (tM (bitOf T 10) x10))) (Nat.mul 68858644 (tM (bitOf T 11) x11))) (Nat.mul 100000000 (tM (bitOf T 12) x12))) (Nat.mul 64382038 (tM (bitOf T 15) x15))) (Nat.mul 157375 (tM (bitOf T 16) x16))) (Nat.mul 65570678 (tM (bitOf T 17) x17))) (Nat.mul 45645275 (tM (bitOf T 19) x19))) (Nat.mul 67808981 (tM (bitOf T 20) x20))) (Nat.mul 99842625 (tM (bitOf T 21) x21))) (Nat.mul 34948217 (tM (bitOf T 22) x22))) (Nat.mul 44643360 (tM (bitOf T 23) x23))) (Nat.mul 0 (tM (bitOf T 24) x24)))))) (Nat.mul (Nat.sub u4 q4) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 65570678 (tK (bitOf T 4))) (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 157375 (tK (bitOf T 10)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 64382038 (tK (bitOf T 15)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 45645275 (tK (bitOf T 19)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 34948217 (tK (bitOf T 22)))) (Nat.mul 44643360 (tK (bitOf T 23)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 68753000000000 (Nat.mul 65570678 (tP (bitOf T 4) x4))) (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 157375 (tP (bitOf T 10) x10))) (Nat.mul 68858644 (tP (bitOf T 11) x11))) (Nat.mul 100000000 (tP (bitOf T 12) x12))) (Nat.mul 64382038 (tP (bitOf T 15) x15))) (Nat.mul 157375 (tP (bitOf T 16) x16))) (Nat.mul 65570678 (tP (bitOf T 17) x17))) (Nat.mul 45645275 (tP (bitOf T 19) x19))) (Nat.mul 67808981 (tP (bitOf T 20) x20))) (Nat.mul 99842625 (tP (bitOf T 21) x21))) (Nat.mul 34948217 (tP (bitOf T 22) x22))) (Nat.mul 44643360 (tP (bitOf T 23) x23))) (Nat.mul 0 (tP (bitOf T 24) x24)))))) (Nat.mul (Nat.sub q5 l5) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 57979000000000 (Nat.mul 100000000 (tK (bitOf T 5)))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 44643360 (tK (bitOf T 23)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.mul 27454871 (tK (bitOf T 25)))) (Nat.mul 9711365 (tK (bitOf T 26)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tM (bitOf T 5) x5)) (Nat.mul 200000000 (tM (bitOf T 6) x6))) (Nat.mul 68858644 (tM (bitOf T 11) x11))) (Nat.mul 100000000 (tM (bitOf T 12) x12))) (Nat.mul 157375 (tM (bitOf T 16) x16))) (Nat.mul 65570678 (tM (bitOf T 17) x17))) (Nat.mul 67808981 (tM (bitOf T 20) x20))) (Nat.mul 99842625 (tM (bitOf T 21) x21))) (Nat.mul 44643360 (tM (bitOf T 23) x23))) (Nat.mul 0 (tM (bitOf T 24) x24))) (Nat.mul 27454871 (tM (bitOf T 25) x25))) (Nat.mul 9711365 (tM (bitOf T 26) x26)))))) (Nat.mul (Nat.sub u5 q5) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (tK (bitOf T 5))) (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 68858644 (tK (bitOf T 11)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 157375 (tK (bitOf T 16)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 67808981 (tK (bitOf T 20)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 44643360 (tK (bitOf T 23)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.mul 27454871 (tK (bitOf T 25)))) (Nat.mul 9711365 (tK (bitOf T 26)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 57979000000000 (Nat.mul 100000000 (tP (bitOf T 5) x5))) (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 68858644 (tP (bitOf T 11) x11))) (Nat.mul 100000000 (tP (bitOf T 12) x12))) (Nat.mul 157375 (tP (bitOf T 16) x16))) (Nat.mul 65570678 (tP (bitOf T 17) x17))) (Nat.mul 67808981 (tP (bitOf T 20) x20))) (Nat.mul 99842625 (tP (bitOf T 21) x21))) (Nat.mul 44643360 (tP (bitOf T 23) x23))) (Nat.mul 0 (tP (bitOf T 24) x24))) (Nat.mul 27454871 (tP (bitOf T 25) x25))) (Nat.mul 9711365 (tP (bitOf T 26) x26)))))) (Nat.mul (Nat.sub q6 l6) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 32954000000000 (Nat.mul 200000000 (tK (bitOf T 6)))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.mul 9711365 (tK (bitOf T 26)))) (Nat.mul 16529847 (tK (bitOf T 27)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (tM (bitOf T 6) x6)) (Nat.mul 100000000 (tM (bitOf T 12) x12))) (Nat.mul 65570678 (tM (bitOf T 17) x17))) (Nat.mul 99842625 (tM (bitOf T 21) x21))) (Nat.mul 0 (tM (bitOf T 24) x24))) (Nat.mul 9711365 (tM (bitOf T 26) x26))) (Nat.mul 16529847 (tM (bitOf T 27) x27)))))) (Nat.mul (Nat.sub u6 q6) (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (tK (bitOf T 6))) (Nat.mul 100000000 (tK (bitOf T 12)))) (Nat.mul 65570678 (tK (bitOf T 17)))) (Nat.mul 99842625 (tK (bitOf T 21)))) (Nat.mul 0 (tK (bitOf T 24)))) (Nat.mul 9711365 (tK (bitOf T 26)))) (Nat.mul 16529847 (tK (bitOf T 27)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 32954000000000 (Nat.mul 200000000 (tP (bitOf T 6) x6))) (Nat.mul 100000000 (tP (bitOf T 12) x12))) (Nat.mul 65570678 (tP (bitOf T 17) x17))) (Nat.mul 99842625 (tP (bitOf T 21) x21))) (Nat.mul 0 (tP (bitOf T 24) x24))) (Nat.mul 9711365 (tP (bitOf T 26) x26))) (Nat.mul 16529847 (tP (bitOf T 27) x27)))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mchg v0 (bitOf T 0) l0 u0 q0 x0 eu0 ed0)) (Nat.mul 9711365 (mchg v1 (bitOf T 1) (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1) x1 eu1 ed1))) (Nat.mul 0 (mchg v2 (bitOf T 2) (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2) x2 eu2 ed2))) (Nat.mul 99842625 (mchg v3 (bitOf T 3) (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) x3 eu3 ed3))) (Nat.mul 65570678 (mchg v4 (bitOf T 4) (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) x4 eu4 ed4))) (Nat.mul 100000000 (mchg v5 (bitOf T 5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) x5 eu5 ed5))) (Nat.mul 200000000 (mchg v6 (bitOf T 6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) q6) x6 eu6 ed6))) (Nat.mul 27454871 (mchg v7 (bitOf T 7) l1 u1 q1 x7 eu7 ed7))) (Nat.mul 44643360 (mchg v8 (bitOf T 8) (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2) x8 eu8 ed8))) (Nat.mul 67808981 (mchg v9 (bitOf T 9) (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3) x9 eu9 ed9))) (Nat.mul 157375 (mchg v10 (bitOf T 10) (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) x10 eu10 ed10))) (Nat.mul 68858644 (mchg v11 (bitOf T 11) (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) x11 eu11 ed11))) (Nat.mul 100000000 (mchg v12 (bitOf T 12) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) q6) x12 eu12 ed12))) (Nat.mul 34948217 (mchg v13 (bitOf T 13) l2 u2 q2 x13 eu13 ed13))) (Nat.mul 45645275 (mchg v14 (bitOf T 14) (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3) x14 eu14 ed14))) (Nat.mul 64382038 (mchg v15 (bitOf T 15) (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4) x15 eu15 ed15))) (Nat.mul 157375 (mchg v16 (bitOf T 16) (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) x16 eu16 ed16))) (Nat.mul 65570678 (mchg v17 (bitOf T 17) (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) q6) x17 eu17 ed17))) (Nat.mul 42134130 (mchg v18 (bitOf T 18) l3 u3 q3 x18 eu18 ed18))) (Nat.mul 45645275 (mchg v19 (bitOf T 19) (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4) x19 eu19 ed19))) (Nat.mul 67808981 (mchg v20 (bitOf T 20) (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5) x20 eu20 ed20))) (Nat.mul 99842625 (mchg v21 (bitOf T 21) (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.add (Nat.add (Nat.add q3 q4) q5) q6) x21 eu21 ed21))) (Nat.mul 34948217 (mchg v22 (bitOf T 22) l4 u4 q4 x22 eu22 ed22))) (Nat.mul 44643360 (mchg v23 (bitOf T 23) (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5) x23 eu23 ed23))) (Nat.mul 0 (mchg v24 (bitOf T 24) (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6) (Nat.add (Nat.add q4 q5) q6) x24 eu24 ed24))) (Nat.mul 27454871 (mchg v25 (bitOf T 25) l5 u5 q5 x25 eu25 ed25))) (Nat.mul 9711365 (mchg v26 (bitOf T 26) (Nat.add l5 l6) (Nat.add u5 u6) (Nat.add q5 q6) x26 eu26 ed26))) (Nat.mul 16529847 (mchg v27 (bitOf T 27) l6 u6 q6 x27 eu27 ed27)))))) (Nat.add (Nat.mul 10000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32954 q0) (Nat.mul 57979 q1)) (Nat.mul 68753 q2)) (Nat.mul 80628 q3)) (Nat.mul 68753 q4)) (Nat.mul 57979 q5)) (Nat.mul 32954 q6))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (tval (bitOf T 0) x0)) (Nat.mul 9711365 (tval (bitOf T 1) x1))) (Nat.mul 0 (tval (bitOf T 2) x2))) (Nat.mul 99842625 (tval (bitOf T 3) x3))) (Nat.mul 65570678 (tval (bitOf T 4) x4))) (Nat.mul 100000000 (tval (bitOf T 5) x5))) (Nat.mul 200000000 (tval (bitOf T 6) x6))) (Nat.mul 27454871 (tval (bitOf T 7) x7))) (Nat.mul 44643360 (tval (bitOf T 8) x8))) (Nat.mul 67808981 (tval (bitOf T 9) x9))) (Nat.mul 157375 (tval (bitOf T 10) x10))) (Nat.mul 68858644 (tval (bitOf T 11) x11))) (Nat.mul 100000000 (tval (bitOf T 12) x12))) (Nat.mul 34948217 (tval (bitOf T 13) x13))) (Nat.mul 45645275 (tval (bitOf T 14) x14))) (Nat.mul 64382038 (tval (bitOf T 15) x15))) (Nat.mul 157375 (tval (bitOf T 16) x16))) (Nat.mul 65570678 (tval (bitOf T 17) x17))) (Nat.mul 42134130 (tval (bitOf T 18) x18))) (Nat.mul 45645275 (tval (bitOf T 19) x19))) (Nat.mul 67808981 (tval (bitOf T 20) x20))) (Nat.mul 99842625 (tval (bitOf T 21) x21))) (Nat.mul 34948217 (tval (bitOf T 22) x22))) (Nat.mul 44643360 (tval (bitOf T 23) x23))) (Nat.mul 0 (tval (bitOf T 24) x24))) (Nat.mul 27454871 (tval (bitOf T 25) x25))) (Nat.mul 9711365 (tval (bitOf T 26) x26))) (Nat.mul 16529847 (tval (bitOf T 27) x27)))))

/-- the slope test at the point `q` with expansion set `T`: an expanded term whose range lies in a convex region of `R`
is bounded by its tangent (no charge), the other expanded terms are charged from the derivative reads -/
def ctest (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (q0 q1 q2 q3 q4 q5 q6 : ℕ) (T : ℕ) : Bool :=
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
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6)) (bitOf T 6)) fun v6 =>
  forceB (selXf (bitOf T 6) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) q6)) fun x6 =>
  forceB (selUv v6 (bitOf T 6) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) q6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6)) fun eu6 =>
  forceB (selDv v6 (bitOf T 6) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5) q6)) fun ed6 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l1 u1) (bitOf T 7)) fun v7 =>
  forceB (selXf (bitOf T 7) top bk pb l1 u1 q1) fun x7 =>
  forceB (selUv v7 (bitOf T 7) tD bD q1 u1) fun eu7 =>
  forceB (selDv v7 (bitOf T 7) tD bD l1 q1) fun ed7 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l1 l2) (Nat.add u1 u2)) (bitOf T 8)) fun v8 =>
  forceB (selXf (bitOf T 8) top bk pb (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2)) fun x8 =>
  forceB (selUv v8 (bitOf T 8) tD bD (Nat.add q1 q2) (Nat.add u1 u2)) fun eu8 =>
  forceB (selDv v8 (bitOf T 8) tD bD (Nat.add l1 l2) (Nat.add q1 q2)) fun ed8 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)) (bitOf T 9)) fun v9 =>
  forceB (selXf (bitOf T 9) top bk pb (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3)) fun x9 =>
  forceB (selUv v9 (bitOf T 9) tD bD (Nat.add (Nat.add q1 q2) q3) (Nat.add (Nat.add u1 u2) u3)) fun eu9 =>
  forceB (selDv v9 (bitOf T 9) tD bD (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add q1 q2) q3)) fun ed9 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)) (bitOf T 10)) fun v10 =>
  forceB (selXf (bitOf T 10) top bk pb (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4)) fun x10 =>
  forceB (selUv v10 (bitOf T 10) tD bD (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)) fun eu10 =>
  forceB (selDv v10 (bitOf T 10) tD bD (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4)) fun ed10 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)) (bitOf T 11)) fun v11 =>
  forceB (selXf (bitOf T 11) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5)) fun x11 =>
  forceB (selUv v11 (bitOf T 11) tD bD (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)) fun eu11 =>
  forceB (selDv v11 (bitOf T 11) tD bD (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5)) fun ed11 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6)) (bitOf T 12)) fun v12 =>
  forceB (selXf (bitOf T 12) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) q6)) fun x12 =>
  forceB (selUv v12 (bitOf T 12) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) q6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6)) fun eu12 =>
  forceB (selDv v12 (bitOf T 12) tD bD (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5) q6)) fun ed12 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l2 u2) (bitOf T 13)) fun v13 =>
  forceB (selXf (bitOf T 13) top bk pb l2 u2 q2) fun x13 =>
  forceB (selUv v13 (bitOf T 13) tD bD q2 u2) fun eu13 =>
  forceB (selDv v13 (bitOf T 13) tD bD l2 q2) fun ed13 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l2 l3) (Nat.add u2 u3)) (bitOf T 14)) fun v14 =>
  forceB (selXf (bitOf T 14) top bk pb (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3)) fun x14 =>
  forceB (selUv v14 (bitOf T 14) tD bD (Nat.add q2 q3) (Nat.add u2 u3)) fun eu14 =>
  forceB (selDv v14 (bitOf T 14) tD bD (Nat.add l2 l3) (Nat.add q2 q3)) fun ed14 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)) (bitOf T 15)) fun v15 =>
  forceB (selXf (bitOf T 15) top bk pb (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4)) fun x15 =>
  forceB (selUv v15 (bitOf T 15) tD bD (Nat.add (Nat.add q2 q3) q4) (Nat.add (Nat.add u2 u3) u4)) fun eu15 =>
  forceB (selDv v15 (bitOf T 15) tD bD (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add q2 q3) q4)) fun ed15 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)) (bitOf T 16)) fun v16 =>
  forceB (selXf (bitOf T 16) top bk pb (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5)) fun x16 =>
  forceB (selUv v16 (bitOf T 16) tD bD (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)) fun eu16 =>
  forceB (selDv v16 (bitOf T 16) tD bD (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5)) fun ed16 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6)) (bitOf T 17)) fun v17 =>
  forceB (selXf (bitOf T 17) top bk pb (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.add (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) q6)) fun x17 =>
  forceB (selUv v17 (bitOf T 17) tD bD (Nat.add (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) q6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6)) fun eu17 =>
  forceB (selDv v17 (bitOf T 17) tD bD (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add q2 q3) q4) q5) q6)) fun ed17 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l3 u3) (bitOf T 18)) fun v18 =>
  forceB (selXf (bitOf T 18) top bk pb l3 u3 q3) fun x18 =>
  forceB (selUv v18 (bitOf T 18) tD bD q3 u3) fun eu18 =>
  forceB (selDv v18 (bitOf T 18) tD bD l3 q3) fun ed18 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l3 l4) (Nat.add u3 u4)) (bitOf T 19)) fun v19 =>
  forceB (selXf (bitOf T 19) top bk pb (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4)) fun x19 =>
  forceB (selUv v19 (bitOf T 19) tD bD (Nat.add q3 q4) (Nat.add u3 u4)) fun eu19 =>
  forceB (selDv v19 (bitOf T 19) tD bD (Nat.add l3 l4) (Nat.add q3 q4)) fun ed19 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)) (bitOf T 20)) fun v20 =>
  forceB (selXf (bitOf T 20) top bk pb (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5)) fun x20 =>
  forceB (selUv v20 (bitOf T 20) tD bD (Nat.add (Nat.add q3 q4) q5) (Nat.add (Nat.add u3 u4) u5)) fun eu20 =>
  forceB (selDv v20 (bitOf T 20) tD bD (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add q3 q4) q5)) fun ed20 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6)) (bitOf T 21)) fun v21 =>
  forceB (selXf (bitOf T 21) top bk pb (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.add (Nat.add (Nat.add q3 q4) q5) q6)) fun x21 =>
  forceB (selUv v21 (bitOf T 21) tD bD (Nat.add (Nat.add (Nat.add q3 q4) q5) q6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6)) fun eu21 =>
  forceB (selDv v21 (bitOf T 21) tD bD (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add q3 q4) q5) q6)) fun ed21 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l4 u4) (bitOf T 22)) fun v22 =>
  forceB (selXf (bitOf T 22) top bk pb l4 u4 q4) fun x22 =>
  forceB (selUv v22 (bitOf T 22) tD bD q4 u4) fun eu22 =>
  forceB (selDv v22 (bitOf T 22) tD bD l4 q4) fun ed22 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l4 l5) (Nat.add u4 u5)) (bitOf T 23)) fun v23 =>
  forceB (selXf (bitOf T 23) top bk pb (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5)) fun x23 =>
  forceB (selUv v23 (bitOf T 23) tD bD (Nat.add q4 q5) (Nat.add u4 u5)) fun eu23 =>
  forceB (selDv v23 (bitOf T 23) tD bD (Nat.add l4 l5) (Nat.add q4 q5)) fun ed23 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6)) (bitOf T 24)) fun v24 =>
  forceB (selXf (bitOf T 24) top bk pb (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add u4 u5) u6) (Nat.add (Nat.add q4 q5) q6)) fun x24 =>
  forceB (selUv v24 (bitOf T 24) tD bD (Nat.add (Nat.add q4 q5) q6) (Nat.add (Nat.add u4 u5) u6)) fun eu24 =>
  forceB (selDv v24 (bitOf T 24) tD bD (Nat.add (Nat.add l4 l5) l6) (Nat.add (Nat.add q4 q5) q6)) fun ed24 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l5 u5) (bitOf T 25)) fun v25 =>
  forceB (selXf (bitOf T 25) top bk pb l5 u5 q5) fun x25 =>
  forceB (selUv v25 (bitOf T 25) tD bD q5 u5) fun eu25 =>
  forceB (selDv v25 (bitOf T 25) tD bD l5 q5) fun ed25 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R (Nat.add l5 l6) (Nat.add u5 u6)) (bitOf T 26)) fun v26 =>
  forceB (selXf (bitOf T 26) top bk pb (Nat.add l5 l6) (Nat.add u5 u6) (Nat.add q5 q6)) fun x26 =>
  forceB (selUv v26 (bitOf T 26) tD bD (Nat.add q5 q6) (Nat.add u5 u6)) fun eu26 =>
  forceB (selDv v26 (bitOf T 26) tD bD (Nat.add l5 l6) (Nat.add q5 q6)) fun ed26 =>
  bforce (Bool.rec (motive := fun _ => Bool) false (inRg R l6 u6) (bitOf T 27)) fun v27 =>
  forceB (selXf (bitOf T 27) top bk pb l6 u6 q6) fun x27 =>
  forceB (selUv v27 (bitOf T 27) tD bD q6 u6) fun eu27 =>
  forceB (selDv v27 (bitOf T 27) tD bD l6 q6) fun ed27 =>
  cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T x0 eu0 ed0 v0 x1 eu1 ed1 v1 x2 eu2 ed2 v2 x3 eu3 ed3 v3 x4 eu4 ed4 v4 x5 eu5 ed5 v5 x6 eu6 ed6 v6 x7 eu7 ed7 v7 x8 eu8 ed8 v8 x9 eu9 ed9 v9 x10 eu10 ed10 v10 x11 eu11 ed11 v11 x12 eu12 ed12 v12 x13 eu13 ed13 v13 x14 eu14 ed14 v14 x15 eu15 ed15 v15 x16 eu16 ed16 v16 x17 eu17 ed17 v17 x18 eu18 ed18 v18 x19 eu19 ed19 v19 x20 eu20 ed20 v20 x21 eu21 ed21 v21 x22 eu22 ed22 v22 x23 eu23 ed23 v23 x24 eu24 ed24 v24 x25 eu25 ed25 v25 x26 eu26 ed26 v26 x27 eu27 ed27 v27


/-- the minorant inequality of a box, given per term its kind `k`, weight `m` and grid points `p`, `r`:
`1024 cN SC U + RU (Σ a mcn + Σ_r (u − l) N_r) ≤ 1024 U Σ b l + SC Σ a mval + RU Σ a mcp` -/
def mscheck (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) (k21 m21 p21 r21 : ℕ) (k22 m22 p22 r22 : ℕ) (k23 m23 p23 r23 : ℕ) (k25 m25 p25 r25 : ℕ) (k26 m26 p26 r26 : ℕ) (k27 m27 p27 r27 : ℕ) : Bool :=
  ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((Nat.ble l0 u0 && Nat.ble l1 u1) && Nat.ble l2 u2) && Nat.ble l3 u3) && Nat.ble l4 u4) && Nat.ble l5 u5) && Nat.ble l6 u6) && Nat.ble m0 1024) && mok R tD bD f l0 u0 (mw1 k0 m0) (mw2 k0 m0) p0 r0) && Nat.ble m1 1024) && mok R tD bD f (Nat.add l0 l1) (Nat.add u0 u1) (mw1 k1 m1) (mw2 k1 m1) p1 r1) && Nat.ble m3 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mw1 k3 m3) (mw2 k3 m3) p3 r3) && Nat.ble m4 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mw1 k4 m4) (mw2 k4 m4) p4 r4) && Nat.ble m5 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mw1 k5 m5) (mw2 k5 m5) p5 r5) && Nat.ble m6 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (mw1 k6 m6) (mw2 k6 m6) p6 r6) && Nat.ble m7 1024) && mok R tD bD f l1 u1 (mw1 k7 m7) (mw2 k7 m7) p7 r7) && Nat.ble m8 1024) && mok R tD bD f (Nat.add l1 l2) (Nat.add u1 u2) (mw1 k8 m8) (mw2 k8 m8) p8 r8) && Nat.ble m9 1024) && mok R tD bD f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mw1 k9 m9) (mw2 k9 m9) p9 r9) && Nat.ble m10 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mw1 k10 m10) (mw2 k10 m10) p10 r10) && Nat.ble m11 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mw1 k11 m11) (mw2 k11 m11) p11 r11) && Nat.ble m12 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (mw1 k12 m12) (mw2 k12 m12) p12 r12) && Nat.ble m13 1024) && mok R tD bD f l2 u2 (mw1 k13 m13) (mw2 k13 m13) p13 r13) && Nat.ble m14 1024) && mok R tD bD f (Nat.add l2 l3) (Nat.add u2 u3) (mw1 k14 m14) (mw2 k14 m14) p14 r14) && Nat.ble m15 1024) && mok R tD bD f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mw1 k15 m15) (mw2 k15 m15) p15 r15) && Nat.ble m16 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mw1 k16 m16) (mw2 k16 m16) p16 r16) && Nat.ble m17 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (mw1 k17 m17) (mw2 k17 m17) p17 r17) && Nat.ble m18 1024) && mok R tD bD f l3 u3 (mw1 k18 m18) (mw2 k18 m18) p18 r18) && Nat.ble m19 1024) && mok R tD bD f (Nat.add l3 l4) (Nat.add u3 u4) (mw1 k19 m19) (mw2 k19 m19) p19 r19) && Nat.ble m20 1024) && mok R tD bD f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mw1 k20 m20) (mw2 k20 m20) p20 r20) && Nat.ble m21 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (mw1 k21 m21) (mw2 k21 m21) p21 r21) && Nat.ble m22 1024) && mok R tD bD f l4 u4 (mw1 k22 m22) (mw2 k22 m22) p22 r22) && Nat.ble m23 1024) && mok R tD bD f (Nat.add l4 l5) (Nat.add u4 u5) (mw1 k23 m23) (mw2 k23 m23) p23 r23) && Nat.ble m25 1024) && mok R tD bD f l5 u5 (mw1 k25 m25) (mw2 k25 m25) p25 r25) && Nat.ble m26 1024) && mok R tD bD f (Nat.add l5 l6) (Nat.add u5 u6) (mw1 k26 m26) (mw2 k26 m26) p26 r26) && Nat.ble m27 1024) && mok R tD bD f l6 u6 (mw1 k27 m27) (mw2 k27 m27) p27 r27) && Nat.ble (Nat.add 235372931973120000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mcn f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mcn f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mcn f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mcn f l1 (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mcn f (Nat.add l1 l2) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mcn f (Nat.add (Nat.add l1 l2) l3) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mcn f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mcn f l2 (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mcn f (Nat.add l2 l3) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mcn f (Nat.add (Nat.add l2 l3) l4) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mcn f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mcn f l3 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mcn f (Nat.add l3 l4) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mcn f (Nat.add (Nat.add l3 l4) l5) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mcn f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mcn f l4 (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mcn f (Nat.add l4 l5) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mcn f l5 (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mcn f (Nat.add l5 l6) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mcn f l6 (mw1 k27 m27) (mw2 k27 m27) p27 r27))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub u0 l0) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (Nat.add (mw1 k0 m0) (mw2 k0 m0))) (Nat.mul 9711365 (Nat.add (mw1 k1 m1) (mw2 k1 m1)))) (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 33744896000000000 (Nat.mul 16529847 (msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0))) (Nat.mul 9711365 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))))) (Nat.mul (Nat.sub u1 l1) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 9711365 (Nat.add (mw1 k1 m1) (mw2 k1 m1))) (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 27454871 (Nat.add (mw1 k7 m7) (mw2 k7 m7)))) (Nat.mul 44643360 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 59370496000000000 (Nat.mul 9711365 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12)))))) (Nat.mul (Nat.sub u2 l2) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 44643360 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 34948217 (Nat.add (mw1 k13 m13) (mw2 k13 m13)))) (Nat.mul 45645275 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 70403072000000000 (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 44643360 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)))))) (Nat.mul (Nat.sub u3 l3) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99842625 (Nat.add (mw1 k3 m3) (mw2 k3 m3))) (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 67808981 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 45645275 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 42134130 (Nat.add (mw1 k18 m18) (mw2 k18 m18)))) (Nat.mul 45645275 (Nat.add (mw1 k19 m19) (mw2 k19 m19)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 82563072000000000 (Nat.mul 99842625 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 67808981 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 45645275 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21)))))) (Nat.mul (Nat.sub u4 l4) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 65570678 (Nat.add (mw1 k4 m4) (mw2 k4 m4))) (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 157375 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 64382038 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 45645275 (Nat.add (mw1 k19 m19) (mw2 k19 m19)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 34948217 (Nat.add (mw1 k22 m22) (mw2 k22 m22)))) (Nat.mul 44643360 (Nat.add (mw1 k23 m23) (mw2 k23 m23))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 70403072000000000 (Nat.mul 65570678 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 157375 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 64382038 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 45645275 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23)))))) (Nat.mul (Nat.sub u5 l5) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 100000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5))) (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 68858644 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 157375 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 67808981 (Nat.add (mw1 k20 m20) (mw2 k20 m20)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 44643360 (Nat.add (mw1 k23 m23) (mw2 k23 m23)))) (Nat.mul 27454871 (Nat.add (mw1 k25 m25) (mw2 k25 m25)))) (Nat.mul 9711365 (Nat.add (mw1 k26 m26) (mw2 k26 m26))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 59370496000000000 (Nat.mul 100000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 68858644 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 157375 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 67808981 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 44643360 (msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26)))))) (Nat.mul (Nat.sub u6 l6) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (Nat.add (mw1 k6 m6) (mw2 k6 m6))) (Nat.mul 100000000 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 65570678 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 99842625 (Nat.add (mw1 k21 m21) (mw2 k21 m21)))) (Nat.mul 9711365 (Nat.add (mw1 k26 m26) (mw2 k26 m26)))) (Nat.mul 16529847 (Nat.add (mw1 k27 m27) (mw2 k27 m27))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 33744896000000000 (Nat.mul 200000000 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 100000000 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 65570678 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 99842625 (msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 9711365 (msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27))))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 32954 l0) (Nat.mul 57979 l1)) (Nat.mul 68753 l2)) (Nat.mul 80628 l3)) (Nat.mul 68753 l4)) (Nat.mul 57979 l5)) (Nat.mul 32954 l6))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mval top bk f l0 u0 (mwc k0 m0) (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mval top bk f (Nat.add l0 l1) (Nat.add u0 u1) (mwc k1 m1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mval top bk f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mwc k3 m3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mwc k4 m4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mwc k5 m5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (mwc k6 m6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mval top bk f l1 u1 (mwc k7 m7) (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mval top bk f (Nat.add l1 l2) (Nat.add u1 u2) (mwc k8 m8) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mval top bk f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mwc k9 m9) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mval top bk f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mwc k10 m10) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mwc k11 m11) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (mwc k12 m12) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mval top bk f l2 u2 (mwc k13 m13) (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mval top bk f (Nat.add l2 l3) (Nat.add u2 u3) (mwc k14 m14) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mval top bk f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mwc k15 m15) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mval top bk f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mwc k16 m16) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (mwc k17 m17) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mval top bk f l3 u3 (mwc k18 m18) (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mval top bk f (Nat.add l3 l4) (Nat.add u3 u4) (mwc k19 m19) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mval top bk f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mwc k20 m20) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mval top bk f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (mwc k21 m21) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mval top bk f l4 u4 (mwc k22 m22) (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mval top bk f (Nat.add l4 l5) (Nat.add u4 u5) (mwc k23 m23) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mval top bk f l5 u5 (mwc k25 m25) (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mval top bk f (Nat.add l5 l6) (Nat.add u5 u6) (mwc k26 m26) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mval top bk f l6 u6 (mwc k27 m27) (mw1 k27 m27) (mw2 k27 m27) p27 r27))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16529847 (mcp f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 9711365 (mcp f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 99842625 (mcp f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 65570678 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 100000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 200000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 27454871 (mcp f l1 (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 44643360 (mcp f (Nat.add l1 l2) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 67808981 (mcp f (Nat.add (Nat.add l1 l2) l3) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 157375 (mcp f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 68858644 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 100000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 34948217 (mcp f l2 (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 45645275 (mcp f (Nat.add l2 l3) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 64382038 (mcp f (Nat.add (Nat.add l2 l3) l4) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 157375 (mcp f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 65570678 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 42134130 (mcp f l3 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 45645275 (mcp f (Nat.add l3 l4) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 67808981 (mcp f (Nat.add (Nat.add l3 l4) l5) (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.mul 99842625 (mcp f (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (mw1 k21 m21) (mw2 k21 m21) p21 r21))) (Nat.mul 34948217 (mcp f l4 (mw1 k22 m22) (mw2 k22 m22) p22 r22))) (Nat.mul 44643360 (mcp f (Nat.add l4 l5) (mw1 k23 m23) (mw2 k23 m23) p23 r23))) (Nat.mul 27454871 (mcp f l5 (mw1 k25 m25) (mw2 k25 m25) p25 r25))) (Nat.mul 9711365 (mcp f (Nat.add l5 l6) (mw1 k26 m26) (mw2 k26 m26) p26 r26))) (Nat.mul 16529847 (mcp f l6 (mw1 k27 m27) (mw2 k27 m27) p27 r27)))))

/-- the payload length of a minorant term of kind `k` -/
def mlen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 20 (Nat.beq k 3)) 16 (Nat.beq k 2)) 6 (Nat.beq k 1)

/-- a minorant leaf: the payload length when the check passes, else `0` -/
def mleafN (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR 0 fun o0 =>
  forceR (Nat.land (Nat.shiftRight w o0) 3) fun k0 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o0 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o0 6)) 1023) (Nat.beq k0 2)) fun m0 =>
  forceR (gpt l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 2)) 15)) fun p0 =>
  forceR (gpt l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 6)) 15)) fun r0 =>
  forceR (Nat.add o0 (mlen k0)) fun o1 =>
  forceR (Nat.land (Nat.shiftRight w o1) 3) fun k1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o1 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o1 6)) 1023) (Nat.beq k1 2)) fun m1 =>
  forceR (gpt (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 2)) 15)) fun p1 =>
  forceR (gpt (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 6)) 15)) fun r1 =>
  forceR (Nat.add o1 (mlen k1)) fun o2 =>
  forceR (Nat.land (Nat.shiftRight w o2) 3) fun k3 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o2 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o2 6)) 1023) (Nat.beq k3 2)) fun m3 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o2 2)) 15)) fun p3 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o2 6)) 15)) fun r3 =>
  forceR (Nat.add o2 (mlen k3)) fun o3 =>
  forceR (Nat.land (Nat.shiftRight w o3) 3) fun k4 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o3 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o3 6)) 1023) (Nat.beq k4 2)) fun m4 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o3 2)) 15)) fun p4 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o3 6)) 15)) fun r4 =>
  forceR (Nat.add o3 (mlen k4)) fun o4 =>
  forceR (Nat.land (Nat.shiftRight w o4) 3) fun k5 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o4 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o4 6)) 1023) (Nat.beq k5 2)) fun m5 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o4 2)) 15)) fun p5 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o4 6)) 15)) fun r5 =>
  forceR (Nat.add o4 (mlen k5)) fun o5 =>
  forceR (Nat.land (Nat.shiftRight w o5) 3) fun k6 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o5 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o5 6)) 1023) (Nat.beq k6 2)) fun m6 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o5 2)) 15)) fun p6 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o5 6)) 15)) fun r6 =>
  forceR (Nat.add o5 (mlen k6)) fun o6 =>
  forceR (Nat.land (Nat.shiftRight w o6) 3) fun k7 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o6 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o6 6)) 1023) (Nat.beq k7 2)) fun m7 =>
  forceR (gpt l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 2)) 15)) fun p7 =>
  forceR (gpt l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 6)) 15)) fun r7 =>
  forceR (Nat.add o6 (mlen k7)) fun o7 =>
  forceR (Nat.land (Nat.shiftRight w o7) 3) fun k8 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o7 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o7 6)) 1023) (Nat.beq k8 2)) fun m8 =>
  forceR (gpt (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 2)) 15)) fun p8 =>
  forceR (gpt (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 6)) 15)) fun r8 =>
  forceR (Nat.add o7 (mlen k8)) fun o8 =>
  forceR (Nat.land (Nat.shiftRight w o8) 3) fun k9 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o8 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o8 6)) 1023) (Nat.beq k9 2)) fun m9 =>
  forceR (gpt (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 2)) 15)) fun p9 =>
  forceR (gpt (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 6)) 15)) fun r9 =>
  forceR (Nat.add o8 (mlen k9)) fun o9 =>
  forceR (Nat.land (Nat.shiftRight w o9) 3) fun k10 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o9 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o9 6)) 1023) (Nat.beq k10 2)) fun m10 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 2)) 15)) fun p10 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 6)) 15)) fun r10 =>
  forceR (Nat.add o9 (mlen k10)) fun o10 =>
  forceR (Nat.land (Nat.shiftRight w o10) 3) fun k11 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o10 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o10 6)) 1023) (Nat.beq k11 2)) fun m11 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 2)) 15)) fun p11 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 6)) 15)) fun r11 =>
  forceR (Nat.add o10 (mlen k11)) fun o11 =>
  forceR (Nat.land (Nat.shiftRight w o11) 3) fun k12 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o11 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o11 6)) 1023) (Nat.beq k12 2)) fun m12 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o11 2)) 15)) fun p12 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o11 6)) 15)) fun r12 =>
  forceR (Nat.add o11 (mlen k12)) fun o12 =>
  forceR (Nat.land (Nat.shiftRight w o12) 3) fun k13 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o12 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o12 6)) 1023) (Nat.beq k13 2)) fun m13 =>
  forceR (gpt l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o12 2)) 15)) fun p13 =>
  forceR (gpt l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o12 6)) 15)) fun r13 =>
  forceR (Nat.add o12 (mlen k13)) fun o13 =>
  forceR (Nat.land (Nat.shiftRight w o13) 3) fun k14 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o13 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o13 6)) 1023) (Nat.beq k14 2)) fun m14 =>
  forceR (gpt (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o13 2)) 15)) fun p14 =>
  forceR (gpt (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o13 6)) 15)) fun r14 =>
  forceR (Nat.add o13 (mlen k14)) fun o14 =>
  forceR (Nat.land (Nat.shiftRight w o14) 3) fun k15 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o14 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o14 6)) 1023) (Nat.beq k15 2)) fun m15 =>
  forceR (gpt (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o14 2)) 15)) fun p15 =>
  forceR (gpt (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o14 6)) 15)) fun r15 =>
  forceR (Nat.add o14 (mlen k15)) fun o15 =>
  forceR (Nat.land (Nat.shiftRight w o15) 3) fun k16 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o15 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o15 6)) 1023) (Nat.beq k16 2)) fun m16 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o15 2)) 15)) fun p16 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o15 6)) 15)) fun r16 =>
  forceR (Nat.add o15 (mlen k16)) fun o16 =>
  forceR (Nat.land (Nat.shiftRight w o16) 3) fun k17 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o16 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o16 6)) 1023) (Nat.beq k17 2)) fun m17 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o16 2)) 15)) fun p17 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o16 6)) 15)) fun r17 =>
  forceR (Nat.add o16 (mlen k17)) fun o17 =>
  forceR (Nat.land (Nat.shiftRight w o17) 3) fun k18 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o17 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o17 6)) 1023) (Nat.beq k18 2)) fun m18 =>
  forceR (gpt l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o17 2)) 15)) fun p18 =>
  forceR (gpt l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o17 6)) 15)) fun r18 =>
  forceR (Nat.add o17 (mlen k18)) fun o18 =>
  forceR (Nat.land (Nat.shiftRight w o18) 3) fun k19 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o18 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o18 6)) 1023) (Nat.beq k19 2)) fun m19 =>
  forceR (gpt (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o18 2)) 15)) fun p19 =>
  forceR (gpt (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o18 6)) 15)) fun r19 =>
  forceR (Nat.add o18 (mlen k19)) fun o19 =>
  forceR (Nat.land (Nat.shiftRight w o19) 3) fun k20 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o19 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o19 6)) 1023) (Nat.beq k20 2)) fun m20 =>
  forceR (gpt (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o19 2)) 15)) fun p20 =>
  forceR (gpt (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o19 6)) 15)) fun r20 =>
  forceR (Nat.add o19 (mlen k20)) fun o20 =>
  forceR (Nat.land (Nat.shiftRight w o20) 3) fun k21 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o20 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o20 6)) 1023) (Nat.beq k21 2)) fun m21 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o20 2)) 15)) fun p21 =>
  forceR (gpt (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (Nat.land (Nat.shiftRight w (Nat.add o20 6)) 15)) fun r21 =>
  forceR (Nat.add o20 (mlen k21)) fun o21 =>
  forceR (Nat.land (Nat.shiftRight w o21) 3) fun k22 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o21 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o21 6)) 1023) (Nat.beq k22 2)) fun m22 =>
  forceR (gpt l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o21 2)) 15)) fun p22 =>
  forceR (gpt l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o21 6)) 15)) fun r22 =>
  forceR (Nat.add o21 (mlen k22)) fun o22 =>
  forceR (Nat.land (Nat.shiftRight w o22) 3) fun k23 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o22 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o22 6)) 1023) (Nat.beq k23 2)) fun m23 =>
  forceR (gpt (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o22 2)) 15)) fun p23 =>
  forceR (gpt (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o22 6)) 15)) fun r23 =>
  forceR (Nat.add o22 (mlen k23)) fun o23 =>
  forceR (Nat.land (Nat.shiftRight w o23) 3) fun k25 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o23 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o23 6)) 1023) (Nat.beq k25 2)) fun m25 =>
  forceR (gpt l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o23 2)) 15)) fun p25 =>
  forceR (gpt l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o23 6)) 15)) fun r25 =>
  forceR (Nat.add o23 (mlen k25)) fun o24 =>
  forceR (Nat.land (Nat.shiftRight w o24) 3) fun k26 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o24 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o24 6)) 1023) (Nat.beq k26 2)) fun m26 =>
  forceR (gpt (Nat.add l5 l6) (Nat.add u5 u6) (Nat.land (Nat.shiftRight w (Nat.add o24 2)) 15)) fun p26 =>
  forceR (gpt (Nat.add l5 l6) (Nat.add u5 u6) (Nat.land (Nat.shiftRight w (Nat.add o24 6)) 15)) fun r26 =>
  forceR (Nat.add o24 (mlen k26)) fun o25 =>
  forceR (Nat.land (Nat.shiftRight w o25) 3) fun k27 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o25 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o25 6)) 1023) (Nat.beq k27 2)) fun m27 =>
  forceR (gpt l6 u6 (Nat.land (Nat.shiftRight w (Nat.add o25 2)) 15)) fun p27 =>
  forceR (gpt l6 u6 (Nat.land (Nat.shiftRight w (Nat.add o25 6)) 15)) fun r27 =>
  forceR (Nat.add o25 (mlen k27)) fun o26 =>
  Bool.rec (motive := fun _ => ℕ) 0 o26 (mscheck top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 k0 m0 p0 r0 k1 m1 p1 r1 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20 k21 m21 p21 r21 k22 m22 p22 r22 k23 m23 p23 r23 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27)


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

/-- a slope leaf: modes (bits 3..16), then a flag (bit 17: every term expanded) or the expansion set
(bits 18..) of the walk word `w` -/
def sleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Bool :=
  forceB (dec (Nat.land (Nat.shiftRight w 3) 3) l0 u0) fun q0 =>
  forceB (dec (Nat.land (Nat.shiftRight w 5) 3) l1 u1) fun q1 =>
  forceB (dec (Nat.land (Nat.shiftRight w 7) 3) l2 u2) fun q2 =>
  forceB (dec (Nat.land (Nat.shiftRight w 9) 3) l3 u3) fun q3 =>
  forceB (dec (Nat.land (Nat.shiftRight w 11) 3) l4 u4) fun q4 =>
  forceB (dec (Nat.land (Nat.shiftRight w 13) 3) l5 u5) fun q5 =>
  forceB (dec (Nat.land (Nat.shiftRight w 15) 3) l6 u6) fun q6 =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 18) 268435455) 268435455 (Nat.beq (Nat.land (Nat.shiftRight w 17) 1) 1)) fun T =>
  ctest top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T

/-- the expansion point of a gap at a centre leaf: coordinate `r` of the centre `k` (20-bit fields of `C`), clamped to
`[l, u]` rounded inward to multiples of `16` when that is nonempty, else to `[l, u]` -/
def cdec (C k r l u : ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight C (Nat.mul 20 (Nat.add (Nat.mul 7 k) r))) 1048575) fun c =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun la =>
  forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun ua =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c u (Nat.ble u c)) l (Nat.ble c l))
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) c ua (Nat.ble ua c)) la (Nat.ble c la))
    (Nat.ble la ua)

/-- a centre leaf: the centre index (bits 3..8), then a flag (bit 9: every term expanded) or the expansion set
(bits 10..) of the walk word `w` -/
def cleaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Bool :=
  forceB (Nat.land (Nat.shiftRight w 3) 63) fun k =>
  forceB (cdec C k 0 l0 u0) fun q0 =>
  forceB (cdec C k 1 l1 u1) fun q1 =>
  forceB (cdec C k 2 l2 u2) fun q2 =>
  forceB (cdec C k 3 l3 u3) fun q3 =>
  forceB (cdec C k 4 l4 u4) fun q4 =>
  forceB (cdec C k 5 l5 u5) fun q5 =>
  forceB (cdec C k 6 l6 u6) fun q6 =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 10) 268435455) 268435455 (Nat.beq (Nat.land (Nat.shiftRight w 9) 1) 1)) fun T =>
  ctest top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T

/-- a basin box -/
structure Bx where
  (l0 u0 : ℕ) (l1 u1 : ℕ) (l2 u2 : ℕ) (l3 u3 : ℕ) (l4 u4 : ℕ) (l5 u5 : ℕ) (l6 u6 : ℕ)

/-- the box lies inside one of the basin boxes -/
def inBas (bas : List Bx) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Bool :=
  bas.any fun b => Nat.ble b.l0 l0 && Nat.ble u0 b.u0 && Nat.ble b.l1 l1 && Nat.ble u1 b.u1 && Nat.ble b.l2 l2 && Nat.ble u2 b.u2 && Nat.ble b.l3 l3 && Nat.ble u3 b.u3 && Nat.ble b.l4 l4 && Nat.ble u4 b.u4 && Nat.ble b.l5 l5 && Nat.ble u5 b.u5 && Nat.ble b.l6 l6 && Nat.ble u6 b.u6

/-- the type of a walk continuation: position and the coordinates to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- a split on gap 0: the lower half (`u0 := q`) from `pos + 4`, then the upper half from where it ends -/
def split0 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l0 u0) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 1: the lower half (`u1 := q`) from `pos + 4`, then the upper half from where it ends -/
def split1 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l1 u1) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 2: the lower half (`u2 := q`) from `pos + 4`, then the upper half from where it ends -/
def split2 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l2 u2) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 3: the lower half (`u3 := q`) from `pos + 4`, then the upper half from where it ends -/
def split3 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l3 u3) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 4: the lower half (`u4 := q`) from `pos + 4`, then the upper half from where it ends -/
def split4 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l4 u4) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5 l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 5: the lower half (`u5 := q`) from `pos + 4`, then the upper half from where it ends -/
def split5 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l5 u5) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q l6 u6
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5 l6 u6) (0) (Nat.beq p 0)

/-- a split on gap 6: the lower half (`u6 := q`) from `pos + 4`, then the upper half from where it ends -/
def split6 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l6 u6) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 q
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q u6) (0) (Nat.beq p 0)

/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (split6 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 5)) (split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 4)) (split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 3)) (split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 2)) (split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 1)) (split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq ax 0)

/-- a leaf (bit 0 clear; bits 1..2 the kind: zero-order, slope with its payload, basin): in the reflected half-space, or
the leaf's own test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 38) (Nat.add pos 10) (Nat.beq (Nat.land (Nat.shiftRight w 9) 1) 1)) (cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 4) (inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)) (forceR (mleafN top bk tD bD pb R (Nat.shiftRight w 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) fun n => Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 4 n)) (0) (Nat.beq n 0)) (Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2)) (Bool.rec (motive := fun _ => ℕ) (0) (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 46) (Nat.add pos 18) (Nat.beq (Nat.land (Nat.shiftRight w 17) 1) 1)) (sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1)) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 3) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0)) (Nat.add pos 3) (Nat.ble (Nat.add u6 1) l0)

/-- the bisection walk (`Nat.rec` on the fuel): the node word is `bits >>> pos` (bit 0 split, bits 1..3 axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : Prop :=
  ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 ∨ g6 < g0

theorem ee_or {C s : ℕ} {rest : Bool} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    229856378880000000000 ≤ 10000000000 * (32954 * l0 + 57979 * l1 + 68753 * l2 + 80628 * l3 + 68753 * l4 + 57979 * l5 + 32954 * l6) + 32768 * (16529847 * lb3 top bk (l0) (u0) + 9711365 * lb3 top bk (l0 + l1) (u0 + u1) + 0 * lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) + 99842625 * lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 65570678 * lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 100000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) + 200000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) + 27454871 * lb3 top bk (l1) (u1) + 44643360 * lb3 top bk (l1 + l2) (u1 + u2) + 67808981 * lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) + 157375 * lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 68858644 * lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) + 100000000 * lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) + 34948217 * lb3 top bk (l2) (u2) + 45645275 * lb3 top bk (l2 + l3) (u2 + u3) + 64382038 * lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) + 157375 * lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) + 65570678 * lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) + 42134130 * lb3 top bk (l3) (u3) + 45645275 * lb3 top bk (l3 + l4) (u3 + u4) + 67808981 * lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) + 99842625 * lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) + 34948217 * lb3 top bk (l4) (u4) + 44643360 * lb3 top bk (l4 + l5) (u4 + u5) + 0 * lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) + 27454871 * lb3 top bk (l5) (u5) + 9711365 * lb3 top bk (l5 + l6) (u5 + u6) + 16529847 * lb3 top bk (l6) (u6)) := by
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
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
  have w0 := lb3_sound hlb (l0) (u0) (g0) h01 h02
  have w1 := lb3_sound hlb (l0 + l1) (u0 + u1) (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  have w2 := lb3_sound hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (slo_add (slo_add h01 h11) h21) (shi_add (shi_add h02 h12) h22)
  have w3 := lb3_sound hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  have w4 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  have w5 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  have w6 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (g0 + g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52) h62)
  have w7 := lb3_sound hlb (l1) (u1) (g1) h11 h12
  have w8 := lb3_sound hlb (l1 + l2) (u1 + u2) (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  have w9 := lb3_sound hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  have w10 := lb3_sound hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  have w11 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  have w12 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52) h62)
  have w13 := lb3_sound hlb (l2) (u2) (g2) h21 h22
  have w14 := lb3_sound hlb (l2 + l3) (u2 + u3) (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  have w15 := lb3_sound hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  have w16 := lb3_sound hlb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  have w17 := lb3_sound hlb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add h21 h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add h22 h32) h42) h52) h62)
  have w18 := lb3_sound hlb (l3) (u3) (g3) h31 h32
  have w19 := lb3_sound hlb (l3 + l4) (u3 + u4) (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  have w20 := lb3_sound hlb (l3 + l4 + l5) (u3 + u4 + u5) (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  have w21 := lb3_sound hlb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add h31 h41) h51) h61) (shi_add (shi_add (shi_add h32 h42) h52) h62)
  have w22 := lb3_sound hlb (l4) (u4) (g4) h41 h42
  have w23 := lb3_sound hlb (l4 + l5) (u4 + u5) (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  have w24 := lb3_sound hlb (l4 + l5 + l6) (u4 + u5 + u6) (g4 + g5 + g6) (slo_add (slo_add h41 h51) h61) (shi_add (shi_add h42 h52) h62)
  have w25 := lb3_sound hlb (l5) (u5) (g5) h51 h52
  have w26 := lb3_sound hlb (l5 + l6) (u5 + u6) (g5 + g6) (slo_add h51 h61) (shi_add h52 h62)
  have w27 := lb3_sound hlb (l6) (u6) (g6) h61 h62
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 32954 * ((l0 : ℝ) / SC) + 57979 * ((l1 : ℝ) / SC) + 68753 * ((l2 : ℝ) / SC) + 80628 * ((l3 : ℝ) / SC) + 68753 * ((l4 : ℝ) / SC) + 57979 * ((l5 : ℝ) / SC) + 32954 * ((l6 : ℝ) / SC) with hL
  set Wt : ℝ := 16529847 * ((lb3 top bk (l0) (u0) : ℝ) / 10000000000) + 9711365 * ((lb3 top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 99842625 * ((lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 65570678 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 200000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 27454871 * ((lb3 top bk (l1) (u1) : ℝ) / 10000000000) + 44643360 * ((lb3 top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 67808981 * ((lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 157375 * ((lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 68858644 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 100000000 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 34948217 * ((lb3 top bk (l2) (u2) : ℝ) / 10000000000) + 45645275 * ((lb3 top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 64382038 * ((lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 157375 * ((lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 65570678 * ((lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 42134130 * ((lb3 top bk (l3) (u3) : ℝ) / 10000000000) + 45645275 * ((lb3 top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 67808981 * ((lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) / 10000000000) + 99842625 * ((lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) : ℝ) / 10000000000) + 34948217 * ((lb3 top bk (l4) (u4) : ℝ) / 10000000000) + 44643360 * ((lb3 top bk (l4 + l5) (u4 + u5) : ℝ) / 10000000000) + 0 * ((lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) : ℝ) / 10000000000) + 27454871 * ((lb3 top bk (l5) (u5) : ℝ) / 10000000000) + 9711365 * ((lb3 top bk (l5 + l6) (u5 + u6) : ℝ) / 10000000000) + 16529847 * ((lb3 top bk (l6) (u6) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (32954 * (l0 : ℝ) + 57979 * (l1 : ℝ) + 68753 * (l2 : ℝ) + 80628 * (l3 : ℝ) + 68753 * (l4 : ℝ) + 57979 * (l5 : ℝ) + 32954 * (l6 : ℝ)) + 32768 * (16529847 * (lb3 top bk (l0) (u0) : ℝ) + 9711365 * (lb3 top bk (l0 + l1) (u0 + u1) : ℝ) + 0 * (lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 99842625 * (lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 65570678 * (lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 100000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) + 200000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) : ℝ) + 27454871 * (lb3 top bk (l1) (u1) : ℝ) + 44643360 * (lb3 top bk (l1 + l2) (u1 + u2) : ℝ) + 67808981 * (lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 157375 * (lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 68858644 * (lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) + 100000000 * (lb3 top bk (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) : ℝ) + 34948217 * (lb3 top bk (l2) (u2) : ℝ) + 45645275 * (lb3 top bk (l2 + l3) (u2 + u3) : ℝ) + 64382038 * (lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 157375 * (lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) + 65570678 * (lb3 top bk (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) : ℝ) + 42134130 * (lb3 top bk (l3) (u3) : ℝ) + 45645275 * (lb3 top bk (l3 + l4) (u3 + u4) : ℝ) + 67808981 * (lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) + 99842625 * (lb3 top bk (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) : ℝ) + 34948217 * (lb3 top bk (l4) (u4) : ℝ) + 44643360 * (lb3 top bk (l4 + l5) (u4 + u5) : ℝ) + 0 * (lb3 top bk (l4 + l5 + l6) (u4 + u5 + u6) : ℝ) + 27454871 * (lb3 top bk (l5) (u5) : ℝ) + 9711365 * (lb3 top bk (l5 + l6) (u5 + u6) : ℝ) + 16529847 * (lb3 top bk (l6) (u6) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 229856378880000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
      + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)) * SA
      = 32954 * g0 + 57979 * g1 + 68753 * g2 + 80628 * g3 + 68753 * g4 + 57979 * g5 + 32954 * g6 + 16529847 * wfun (g0) + 9711365 * wfun (g0 + g1) + 0 * wfun (g0 + g1 + g2) + 99842625 * wfun (g0 + g1 + g2 + g3) + 65570678 * wfun (g0 + g1 + g2 + g3 + g4) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + 27454871 * wfun (g1) + 44643360 * wfun (g1 + g2) + 67808981 * wfun (g1 + g2 + g3) + 157375 * wfun (g1 + g2 + g3 + g4) + 68858644 * wfun (g1 + g2 + g3 + g4 + g5) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5 + g6) + 34948217 * wfun (g2) + 45645275 * wfun (g2 + g3) + 64382038 * wfun (g2 + g3 + g4) + 157375 * wfun (g2 + g3 + g4 + g5) + 65570678 * wfun (g2 + g3 + g4 + g5 + g6) + 42134130 * wfun (g3) + 45645275 * wfun (g3 + g4) + 67808981 * wfun (g3 + g4 + g5) + 99842625 * wfun (g3 + g4 + g5 + g6) + 34948217 * wfun (g4) + 44643360 * wfun (g4 + g5) + 0 * wfun (g4 + g5 + g6) + 27454871 * wfun (g5) + 9711365 * wfun (g5 + g6) + 16529847 * wfun (g6) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 32954), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 57979), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 68753), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 80628), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 68753), mul_le_mul_of_nonneg_left h51 (by positivity : (0:ℝ) ≤ 57979), mul_le_mul_of_nonneg_left h61 (by positivity : (0:ℝ) ≤ 32954), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 16529847), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 68858644), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left w15 (by positivity : (0:ℝ) ≤ 64382038), mul_le_mul_of_nonneg_left w16 (by positivity : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left w17 (by positivity : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left w18 (by positivity : (0:ℝ) ≤ 42134130), mul_le_mul_of_nonneg_left w19 (by positivity : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left w20 (by positivity : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left w21 (by positivity : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left w22 (by positivity : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left w23 (by positivity : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left w24 (by positivity : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left w25 (by positivity : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left w26 (by positivity : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left w27 (by positivity : (0:ℝ) ≤ 16529847)]

theorem ctest_spec {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (q0 q1 q2 q3 q4 q5 q6 : ℕ) (T : ℕ)
    (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T = true) :
    cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (bitOf T 0) tD bD (q0) (u0)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (bitOf T 0) tD bD (l0) (q0)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0) (u0)) (bitOf T 0)) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (bitOf T 1) tD bD (q0 + q1) (u0 + u1)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (bitOf T 1) tD bD (l0 + l1) (q0 + q1)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1) (u0 + u1)) (bitOf T 1)) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (bitOf T 2) tD bD (q0 + q1 + q2) (u0 + u1 + u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (bitOf T 2) tD bD (l0 + l1 + l2) (q0 + q1 + q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2) (u0 + u1 + u2)) (bitOf T 2)) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (bitOf T 3) tD bD (q0 + q1 + q2 + q3) (u0 + u1 + u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (bitOf T 3) tD bD (l0 + l1 + l2 + l3) (q0 + q1 + q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) (bitOf T 3)) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (bitOf T 4) tD bD (q0 + q1 + q2 + q3 + q4) (u0 + u1 + u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (bitOf T 4) tD bD (l0 + l1 + l2 + l3 + l4) (q0 + q1 + q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) (bitOf T 4)) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (bitOf T 5) tD bD (q0 + q1 + q2 + q3 + q4 + q5) (u0 + u1 + u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (bitOf T 5) tD bD (l0 + l1 + l2 + l3 + l4 + l5) (q0 + q1 + q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5)) (bitOf T 5)) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 6)) (bitOf T 6) tD bD (q0 + q1 + q2 + q3 + q4 + q5 + q6) (u0 + u1 + u2 + u3 + u4 + u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 6)) (bitOf T 6) tD bD (l0 + l1 + l2 + l3 + l4 + l5 + l6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 6)) (selXf (bitOf T 7) top bk pb (l1) (u1) (q1)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 7)) (bitOf T 7) tD bD (q1) (u1)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 7)) (bitOf T 7) tD bD (l1) (q1)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1) (u1)) (bitOf T 7)) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 8)) (bitOf T 8) tD bD (q1 + q2) (u1 + u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 8)) (bitOf T 8) tD bD (l1 + l2) (q1 + q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2) (u1 + u2)) (bitOf T 8)) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 9)) (bitOf T 9) tD bD (q1 + q2 + q3) (u1 + u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 9)) (bitOf T 9) tD bD (l1 + l2 + l3) (q1 + q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3) (u1 + u2 + u3)) (bitOf T 9)) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 10)) (bitOf T 10) tD bD (q1 + q2 + q3 + q4) (u1 + u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 10)) (bitOf T 10) tD bD (l1 + l2 + l3 + l4) (q1 + q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) (bitOf T 10)) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 11)) (bitOf T 11) tD bD (q1 + q2 + q3 + q4 + q5) (u1 + u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 11)) (bitOf T 11) tD bD (l1 + l2 + l3 + l4 + l5) (q1 + q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5)) (bitOf T 11)) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 12)) (bitOf T 12) tD bD (q1 + q2 + q3 + q4 + q5 + q6) (u1 + u2 + u3 + u4 + u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 12)) (bitOf T 12) tD bD (l1 + l2 + l3 + l4 + l5 + l6) (q1 + q2 + q3 + q4 + q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6)) (bitOf T 12)) (selXf (bitOf T 13) top bk pb (l2) (u2) (q2)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 13)) (bitOf T 13) tD bD (q2) (u2)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 13)) (bitOf T 13) tD bD (l2) (q2)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2) (u2)) (bitOf T 13)) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 14)) (bitOf T 14) tD bD (q2 + q3) (u2 + u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 14)) (bitOf T 14) tD bD (l2 + l3) (q2 + q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3) (u2 + u3)) (bitOf T 14)) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 15)) (bitOf T 15) tD bD (q2 + q3 + q4) (u2 + u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 15)) (bitOf T 15) tD bD (l2 + l3 + l4) (q2 + q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4) (u2 + u3 + u4)) (bitOf T 15)) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 16)) (bitOf T 16) tD bD (q2 + q3 + q4 + q5) (u2 + u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 16)) (bitOf T 16) tD bD (l2 + l3 + l4 + l5) (q2 + q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5)) (bitOf T 16)) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6)) (bitOf T 17)) (bitOf T 17) tD bD (q2 + q3 + q4 + q5 + q6) (u2 + u3 + u4 + u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6)) (bitOf T 17)) (bitOf T 17) tD bD (l2 + l3 + l4 + l5 + l6) (q2 + q3 + q4 + q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6)) (bitOf T 17)) (selXf (bitOf T 18) top bk pb (l3) (u3) (q3)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 18)) (bitOf T 18) tD bD (q3) (u3)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 18)) (bitOf T 18) tD bD (l3) (q3)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3) (u3)) (bitOf T 18)) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 19)) (bitOf T 19) tD bD (q3 + q4) (u3 + u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 19)) (bitOf T 19) tD bD (l3 + l4) (q3 + q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4) (u3 + u4)) (bitOf T 19)) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 20)) (bitOf T 20) tD bD (q3 + q4 + q5) (u3 + u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 20)) (bitOf T 20) tD bD (l3 + l4 + l5) (q3 + q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5) (u3 + u4 + u5)) (bitOf T 20)) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6)) (bitOf T 21)) (bitOf T 21) tD bD (q3 + q4 + q5 + q6) (u3 + u4 + u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6)) (bitOf T 21)) (bitOf T 21) tD bD (l3 + l4 + l5 + l6) (q3 + q4 + q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6)) (bitOf T 21)) (selXf (bitOf T 22) top bk pb (l4) (u4) (q4)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 22)) (bitOf T 22) tD bD (q4) (u4)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 22)) (bitOf T 22) tD bD (l4) (q4)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l4) (u4)) (bitOf T 22)) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 23)) (bitOf T 23) tD bD (q4 + q5) (u4 + u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 23)) (bitOf T 23) tD bD (l4 + l5) (q4 + q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5) (u4 + u5)) (bitOf T 23)) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5 + l6) (u4 + u5 + u6)) (bitOf T 24)) (bitOf T 24) tD bD (q4 + q5 + q6) (u4 + u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5 + l6) (u4 + u5 + u6)) (bitOf T 24)) (bitOf T 24) tD bD (l4 + l5 + l6) (q4 + q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l4 + l5 + l6) (u4 + u5 + u6)) (bitOf T 24)) (selXf (bitOf T 25) top bk pb (l5) (u5) (q5)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 25)) (bitOf T 25) tD bD (q5) (u5)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 25)) (bitOf T 25) tD bD (l5) (q5)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l5) (u5)) (bitOf T 25)) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5 + l6) (u5 + u6)) (bitOf T 26)) (bitOf T 26) tD bD (q5 + q6) (u5 + u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l5 + l6) (u5 + u6)) (bitOf T 26)) (bitOf T 26) tD bD (l5 + l6) (q5 + q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l5 + l6) (u5 + u6)) (bitOf T 26)) (selXf (bitOf T 27) top bk pb (l6) (u6) (q6)) (selUv (Bool.rec (motive := fun _ => Bool) false (inRg R (l6) (u6)) (bitOf T 27)) (bitOf T 27) tD bD (q6) (u6)) (selDv (Bool.rec (motive := fun _ => Bool) false (inRg R (l6) (u6)) (bitOf T 27)) (bitOf T 27) tD bD (l6) (q6)) (Bool.rec (motive := fun _ => Bool) false (inRg R (l6) (u6)) (bitOf T 27)) = true := by
  unfold ctest at h
  simp only [forceB_eq, bforce_eq] at h
  exact h

set_option maxHeartbeats 40000000 in
theorem ctest_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (q0 q1 q2 q3 q4 q5 q6 : ℕ) (T : ℕ) (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  have h' := ctest_spec l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq01, hq02⟩, hq11⟩, hq12⟩, hq21⟩, hq22⟩, hq31⟩, hq32⟩, hq41⟩, hq42⟩, hq51⟩, hq52⟩, hq61⟩, hq62⟩, hok0⟩, hok1⟩, hok2⟩, hok3⟩, hok4⟩, hok5⟩, hok6⟩, hok7⟩, hok8⟩, hok9⟩, hok10⟩, hok11⟩, hok12⟩, hok13⟩, hok14⟩, hok15⟩, hok16⟩, hok17⟩, hok18⟩, hok19⟩, hok20⟩, hok21⟩, hok22⟩, hok23⟩, hok24⟩, hok25⟩, hok26⟩, hok27⟩, hmain⟩ := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨d0, hdl0, hdu0, hb0⟩ := rterm_boundc hlb hD hpt (bitOf T 0) (l0) (u0) (q0) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok0
    (g0) h01 h02
  push_cast at hb0
  obtain ⟨d1, hdl1, hdu1, hb1⟩ := rterm_boundc hlb hD hpt (bitOf T 1) (l0 + l1) (u0 + u1) (q0 + q1) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok1
    (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  push_cast at hb1
  obtain ⟨d2, hdl2, hdu2, hb2⟩ := rterm_boundc hlb hD hpt (bitOf T 2) (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok2
    (g0 + g1 + g2) (slo_add (slo_add h01 h11) h21) (shi_add (shi_add h02 h12) h22)
  push_cast at hb2
  obtain ⟨d3, hdl3, hdu3, hb3⟩ := rterm_boundc hlb hD hpt (bitOf T 3) (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok3
    (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  push_cast at hb3
  obtain ⟨d4, hdl4, hdu4, hb4⟩ := rterm_boundc hlb hD hpt (bitOf T 4) (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok4
    (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  push_cast at hb4
  obtain ⟨d5, hdl5, hdu5, hb5⟩ := rterm_boundc hlb hD hpt (bitOf T 5) (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  push_cast at hb5
  obtain ⟨d6, hdl6, hdu6, hb6⟩ := rterm_boundc hlb hD hpt (bitOf T 6) (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok6
    (g0 + g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52) h62)
  push_cast at hb6
  obtain ⟨d7, hdl7, hdu7, hb7⟩ := rterm_boundc hlb hD hpt (bitOf T 7) (l1) (u1) (q1) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok7
    (g1) h11 h12
  push_cast at hb7
  obtain ⟨d8, hdl8, hdu8, hb8⟩ := rterm_boundc hlb hD hpt (bitOf T 8) (l1 + l2) (u1 + u2) (q1 + q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok8
    (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  push_cast at hb8
  obtain ⟨d9, hdl9, hdu9, hb9⟩ := rterm_boundc hlb hD hpt (bitOf T 9) (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok9
    (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  push_cast at hb9
  obtain ⟨d10, hdl10, hdu10, hb10⟩ := rterm_boundc hlb hD hpt (bitOf T 10) (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok10
    (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  push_cast at hb10
  obtain ⟨d11, hdl11, hdu11, hb11⟩ := rterm_boundc hlb hD hpt (bitOf T 11) (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok11
    (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  push_cast at hb11
  obtain ⟨d12, hdl12, hdu12, hb12⟩ := rterm_boundc hlb hD hpt (bitOf T 12) (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok12
    (g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52) h62)
  push_cast at hb12
  obtain ⟨d13, hdl13, hdu13, hb13⟩ := rterm_boundc hlb hD hpt (bitOf T 13) (l2) (u2) (q2) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok13
    (g2) h21 h22
  push_cast at hb13
  obtain ⟨d14, hdl14, hdu14, hb14⟩ := rterm_boundc hlb hD hpt (bitOf T 14) (l2 + l3) (u2 + u3) (q2 + q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok14
    (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  push_cast at hb14
  obtain ⟨d15, hdl15, hdu15, hb15⟩ := rterm_boundc hlb hD hpt (bitOf T 15) (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok15
    (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  push_cast at hb15
  obtain ⟨d16, hdl16, hdu16, hb16⟩ := rterm_boundc hlb hD hpt (bitOf T 16) (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok16
    (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  push_cast at hb16
  obtain ⟨d17, hdl17, hdu17, hb17⟩ := rterm_boundc hlb hD hpt (bitOf T 17) (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok17
    (g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add h21 h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add h22 h32) h42) h52) h62)
  push_cast at hb17
  obtain ⟨d18, hdl18, hdu18, hb18⟩ := rterm_boundc hlb hD hpt (bitOf T 18) (l3) (u3) (q3) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok18
    (g3) h31 h32
  push_cast at hb18
  obtain ⟨d19, hdl19, hdu19, hb19⟩ := rterm_boundc hlb hD hpt (bitOf T 19) (l3 + l4) (u3 + u4) (q3 + q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok19
    (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  push_cast at hb19
  obtain ⟨d20, hdl20, hdu20, hb20⟩ := rterm_boundc hlb hD hpt (bitOf T 20) (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok20
    (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  push_cast at hb20
  obtain ⟨d21, hdl21, hdu21, hb21⟩ := rterm_boundc hlb hD hpt (bitOf T 21) (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok21
    (g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add h31 h41) h51) h61) (shi_add (shi_add (shi_add h32 h42) h52) h62)
  push_cast at hb21
  obtain ⟨d22, hdl22, hdu22, hb22⟩ := rterm_boundc hlb hD hpt (bitOf T 22) (l4) (u4) (q4) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok22
    (g4) h41 h42
  push_cast at hb22
  obtain ⟨d23, hdl23, hdu23, hb23⟩ := rterm_boundc hlb hD hpt (bitOf T 23) (l4 + l5) (u4 + u5) (q4 + q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok23
    (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  push_cast at hb23
  obtain ⟨d24, hdl24, hdu24, hb24⟩ := rterm_boundc hlb hD hpt (bitOf T 24) (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok24
    (g4 + g5 + g6) (slo_add (slo_add h41 h51) h61) (shi_add (shi_add h42 h52) h62)
  push_cast at hb24
  obtain ⟨d25, hdl25, hdu25, hb25⟩ := rterm_boundc hlb hD hpt (bitOf T 25) (l5) (u5) (q5) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok25
    (g5) h51 h52
  push_cast at hb25
  obtain ⟨d26, hdl26, hdu26, hb26⟩ := rterm_boundc hlb hD hpt (bitOf T 26) (l5 + l6) (u5 + u6) (q5 + q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok26
    (g5 + g6) (slo_add h51 h61) (shi_add h52 h62)
  push_cast at hb26
  obtain ⟨d27, hdl27, hdu27, hb27⟩ := rterm_boundc hlb hD hpt (bitOf T 27) (l6) (u6) (q6) _ (fun h => inRg_sound hR (cvflag h)) (by omega) (by omega) hok27
    (g6) h61 h62
  push_cast at hb27
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
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
  have hl6 : (l6 : ℝ) ≤ q6 := by exact_mod_cast hq61
  have hu6 : (q6 : ℝ) ≤ u6 := by exact_mod_cast hq62
  have hP0 : (1000000000 : ℝ) * ((32954 : ℝ) + 16529847 * d0 + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6) ≤ (((32954000000000 + 16529847 * tK (bitOf T 0) + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6)) - (16529847 * tM (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 9711365 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (32954000000000 + 16529847 * tK (bitOf T 0) + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6)) (16529847 * tM (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 9711365 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdu0, hdu1, hdu2, hdu3, hdu4, hdu5, hdu6]
  have hN0 : -((1000000000 : ℝ) * ((32954 : ℝ) + 16529847 * d0 + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6)) ≤ (((16529847 * tK (bitOf T 0) + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6)) - (32954000000000 + 16529847 * tP (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 9711365 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (16529847 * tK (bitOf T 0) + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6)) (32954000000000 + 16529847 * tP (bitOf T 0) (selXf (bitOf T 0) top bk pb (l0) (u0) (q0)) + 9711365 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdl0, hdl1, hdl2, hdl3, hdl4, hdl5, hdl6]
  have hml0 : ((q0 - l0 : ℕ) : ℝ) = (q0 : ℝ) - l0 := Nat.cast_sub hq01
  have hum0 : ((u0 - q0 : ℕ) : ℝ) = (u0 : ℝ) - q0 := Nat.cast_sub hq02
  have ht0 := mterm (e := g0 - (q0 : ℝ) / 32768) (E := ((32954 : ℝ) + 16529847 * d0 + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6)) (lo := ((q0 - l0 : ℕ) : ℝ) / 32768)
    (hi := ((u0 - q0 : ℕ) : ℝ) / 32768) (by rw [hml0]; linarith [h01]) (by rw [hum0]; linarith [h02])
    (by positivity) (by positivity) hP0 hN0 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP1 : (1000000000 : ℝ) * ((57979 : ℝ) + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 27454871 * d7 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12) ≤ (((57979000000000 + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 27454871 * tK (bitOf T 7) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12)) - (9711365 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 27454871 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1) (u1) (q1)) + 44643360 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (57979000000000 + 9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 27454871 * tK (bitOf T 7) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12)) (9711365 * tM (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 27454871 * tM (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1) (u1) (q1)) + 44643360 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdu1, hdu2, hdu3, hdu4, hdu5, hdu6, hdu7, hdu8, hdu9, hdu10, hdu11, hdu12]
  have hN1 : -((1000000000 : ℝ) * ((57979 : ℝ) + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 27454871 * d7 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12)) ≤ (((9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 27454871 * tK (bitOf T 7) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12)) - (57979000000000 + 9711365 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 27454871 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1) (u1) (q1)) + 44643360 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (9711365 * tK (bitOf T 1) + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 27454871 * tK (bitOf T 7) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12)) (57979000000000 + 9711365 * tP (bitOf T 1) (selXf (bitOf T 1) top bk pb (l0 + l1) (u0 + u1) (q0 + q1)) + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 27454871 * tP (bitOf T 7) (selXf (bitOf T 7) top bk pb (l1) (u1) (q1)) + 44643360 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdl1, hdl2, hdl3, hdl4, hdl5, hdl6, hdl7, hdl8, hdl9, hdl10, hdl11, hdl12]
  have hml1 : ((q1 - l1 : ℕ) : ℝ) = (q1 : ℝ) - l1 := Nat.cast_sub hq11
  have hum1 : ((u1 - q1 : ℕ) : ℝ) = (u1 : ℝ) - q1 := Nat.cast_sub hq12
  have ht1 := mterm (e := g1 - (q1 : ℝ) / 32768) (E := ((57979 : ℝ) + 9711365 * d1 + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 27454871 * d7 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12)) (lo := ((q1 - l1 : ℕ) : ℝ) / 32768)
    (hi := ((u1 - q1 : ℕ) : ℝ) / 32768) (by rw [hml1]; linarith [h11]) (by rw [hum1]; linarith [h12])
    (by positivity) (by positivity) hP1 hN1 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP2 : (1000000000 : ℝ) * ((68753 : ℝ) + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 34948217 * d13 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17) ≤ (((68753000000000 + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 34948217 * tK (bitOf T 13) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17)) - (0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 44643360 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 34948217 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2) (u2) (q2)) + 45645275 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (68753000000000 + 0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 34948217 * tK (bitOf T 13) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17)) (0 * tM (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 44643360 * tM (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 34948217 * tM (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2) (u2) (q2)) + 45645275 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdu2, hdu3, hdu4, hdu5, hdu6, hdu8, hdu9, hdu10, hdu11, hdu12, hdu13, hdu14, hdu15, hdu16, hdu17]
  have hN2 : -((1000000000 : ℝ) * ((68753 : ℝ) + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 34948217 * d13 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17)) ≤ (((0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 34948217 * tK (bitOf T 13) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17)) - (68753000000000 + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 44643360 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 34948217 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2) (u2) (q2)) + 45645275 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (0 * tK (bitOf T 2) + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 44643360 * tK (bitOf T 8) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 34948217 * tK (bitOf T 13) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17)) (68753000000000 + 0 * tP (bitOf T 2) (selXf (bitOf T 2) top bk pb (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2)) + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 44643360 * tP (bitOf T 8) (selXf (bitOf T 8) top bk pb (l1 + l2) (u1 + u2) (q1 + q2)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 34948217 * tP (bitOf T 13) (selXf (bitOf T 13) top bk pb (l2) (u2) (q2)) + 45645275 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdl2, hdl3, hdl4, hdl5, hdl6, hdl8, hdl9, hdl10, hdl11, hdl12, hdl13, hdl14, hdl15, hdl16, hdl17]
  have hml2 : ((q2 - l2 : ℕ) : ℝ) = (q2 : ℝ) - l2 := Nat.cast_sub hq21
  have hum2 : ((u2 - q2 : ℕ) : ℝ) = (u2 : ℝ) - q2 := Nat.cast_sub hq22
  have ht2 := mterm (e := g2 - (q2 : ℝ) / 32768) (E := ((68753 : ℝ) + 0 * d2 + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 44643360 * d8 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 34948217 * d13 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17)) (lo := ((q2 - l2 : ℕ) : ℝ) / 32768)
    (hi := ((u2 - q2 : ℕ) : ℝ) / 32768) (by rw [hml2]; linarith [h21]) (by rw [hum2]; linarith [h22])
    (by positivity) (by positivity) hP2 hN2 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP3 : (1000000000 : ℝ) * ((80628 : ℝ) + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 42134130 * d18 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21) ≤ (((80628000000000 + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 42134130 * tK (bitOf T 18) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21)) - (99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 45645275 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 42134130 * tM (bitOf T 18) (selXf (bitOf T 18) top bk pb (l3) (u3) (q3)) + 45645275 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (80628000000000 + 99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 42134130 * tK (bitOf T 18) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21)) (99842625 * tM (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 67808981 * tM (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 45645275 * tM (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 42134130 * tM (bitOf T 18) (selXf (bitOf T 18) top bk pb (l3) (u3) (q3)) + 45645275 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdu3, hdu4, hdu5, hdu6, hdu9, hdu10, hdu11, hdu12, hdu14, hdu15, hdu16, hdu17, hdu18, hdu19, hdu20, hdu21]
  have hN3 : -((1000000000 : ℝ) * ((80628 : ℝ) + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 42134130 * d18 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21)) ≤ (((99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 42134130 * tK (bitOf T 18) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21)) - (80628000000000 + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 45645275 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 42134130 * tP (bitOf T 18) (selXf (bitOf T 18) top bk pb (l3) (u3) (q3)) + 45645275 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (99842625 * tK (bitOf T 3) + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 67808981 * tK (bitOf T 9) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 45645275 * tK (bitOf T 14) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 42134130 * tK (bitOf T 18) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21)) (80628000000000 + 99842625 * tP (bitOf T 3) (selXf (bitOf T 3) top bk pb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3)) + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 67808981 * tP (bitOf T 9) (selXf (bitOf T 9) top bk pb (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 45645275 * tP (bitOf T 14) (selXf (bitOf T 14) top bk pb (l2 + l3) (u2 + u3) (q2 + q3)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 42134130 * tP (bitOf T 18) (selXf (bitOf T 18) top bk pb (l3) (u3) (q3)) + 45645275 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)))
    push_cast at this
    linarith [hdl3, hdl4, hdl5, hdl6, hdl9, hdl10, hdl11, hdl12, hdl14, hdl15, hdl16, hdl17, hdl18, hdl19, hdl20, hdl21]
  have hml3 : ((q3 - l3 : ℕ) : ℝ) = (q3 : ℝ) - l3 := Nat.cast_sub hq31
  have hum3 : ((u3 - q3 : ℕ) : ℝ) = (u3 : ℝ) - q3 := Nat.cast_sub hq32
  have ht3 := mterm (e := g3 - (q3 : ℝ) / 32768) (E := ((80628 : ℝ) + 99842625 * d3 + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 67808981 * d9 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 45645275 * d14 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 42134130 * d18 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21)) (lo := ((q3 - l3 : ℕ) : ℝ) / 32768)
    (hi := ((u3 - q3 : ℕ) : ℝ) / 32768) (by rw [hml3]; linarith [h31]) (by rw [hum3]; linarith [h32])
    (by positivity) (by positivity) hP3 hN3 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP4 : (1000000000 : ℝ) * ((68753 : ℝ) + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21 + 34948217 * d22 + 44643360 * d23 + 0 * d24) ≤ (((68753000000000 + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 34948217 * tK (bitOf T 22) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24)) - (65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 45645275 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 34948217 * tM (bitOf T 22) (selXf (bitOf T 22) top bk pb (l4) (u4) (q4)) + 44643360 * tM (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (68753000000000 + 65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 34948217 * tK (bitOf T 22) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24)) (65570678 * tM (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tM (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 64382038 * tM (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 45645275 * tM (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 34948217 * tM (bitOf T 22) (selXf (bitOf T 22) top bk pb (l4) (u4) (q4)) + 44643360 * tM (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)))
    push_cast at this
    linarith [hdu4, hdu5, hdu6, hdu10, hdu11, hdu12, hdu15, hdu16, hdu17, hdu19, hdu20, hdu21, hdu22, hdu23, hdu24]
  have hN4 : -((1000000000 : ℝ) * ((68753 : ℝ) + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21 + 34948217 * d22 + 44643360 * d23 + 0 * d24)) ≤ (((65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 34948217 * tK (bitOf T 22) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24)) - (68753000000000 + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 45645275 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 34948217 * tP (bitOf T 22) (selXf (bitOf T 22) top bk pb (l4) (u4) (q4)) + 44643360 * tP (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (65570678 * tK (bitOf T 4) + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 157375 * tK (bitOf T 10) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 64382038 * tK (bitOf T 15) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 45645275 * tK (bitOf T 19) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 34948217 * tK (bitOf T 22) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24)) (68753000000000 + 65570678 * tP (bitOf T 4) (selXf (bitOf T 4) top bk pb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4)) + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tP (bitOf T 10) (selXf (bitOf T 10) top bk pb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 64382038 * tP (bitOf T 15) (selXf (bitOf T 15) top bk pb (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 45645275 * tP (bitOf T 19) (selXf (bitOf T 19) top bk pb (l3 + l4) (u3 + u4) (q3 + q4)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 34948217 * tP (bitOf T 22) (selXf (bitOf T 22) top bk pb (l4) (u4) (q4)) + 44643360 * tP (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)))
    push_cast at this
    linarith [hdl4, hdl5, hdl6, hdl10, hdl11, hdl12, hdl15, hdl16, hdl17, hdl19, hdl20, hdl21, hdl22, hdl23, hdl24]
  have hml4 : ((q4 - l4 : ℕ) : ℝ) = (q4 : ℝ) - l4 := Nat.cast_sub hq41
  have hum4 : ((u4 - q4 : ℕ) : ℝ) = (u4 : ℝ) - q4 := Nat.cast_sub hq42
  have ht4 := mterm (e := g4 - (q4 : ℝ) / 32768) (E := ((68753 : ℝ) + 65570678 * d4 + 100000000 * d5 + 200000000 * d6 + 157375 * d10 + 68858644 * d11 + 100000000 * d12 + 64382038 * d15 + 157375 * d16 + 65570678 * d17 + 45645275 * d19 + 67808981 * d20 + 99842625 * d21 + 34948217 * d22 + 44643360 * d23 + 0 * d24)) (lo := ((q4 - l4 : ℕ) : ℝ) / 32768)
    (hi := ((u4 - q4 : ℕ) : ℝ) / 32768) (by rw [hml4]; linarith [h41]) (by rw [hum4]; linarith [h42])
    (by positivity) (by positivity) hP4 hN4 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP5 : (1000000000 : ℝ) * ((57979 : ℝ) + 100000000 * d5 + 200000000 * d6 + 68858644 * d11 + 100000000 * d12 + 157375 * d16 + 65570678 * d17 + 67808981 * d20 + 99842625 * d21 + 44643360 * d23 + 0 * d24 + 27454871 * d25 + 9711365 * d26) ≤ (((57979000000000 + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24) + 27454871 * tK (bitOf T 25) + 9711365 * tK (bitOf T 26)) - (100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 44643360 * tM (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 27454871 * tM (bitOf T 25) (selXf (bitOf T 25) top bk pb (l5) (u5) (q5)) + 9711365 * tM (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (57979000000000 + 100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24) + 27454871 * tK (bitOf T 25) + 9711365 * tK (bitOf T 26)) (100000000 * tM (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 68858644 * tM (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tM (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 67808981 * tM (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 44643360 * tM (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 27454871 * tM (bitOf T 25) (selXf (bitOf T 25) top bk pb (l5) (u5) (q5)) + 9711365 * tM (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)))
    push_cast at this
    linarith [hdu5, hdu6, hdu11, hdu12, hdu16, hdu17, hdu20, hdu21, hdu23, hdu24, hdu25, hdu26]
  have hN5 : -((1000000000 : ℝ) * ((57979 : ℝ) + 100000000 * d5 + 200000000 * d6 + 68858644 * d11 + 100000000 * d12 + 157375 * d16 + 65570678 * d17 + 67808981 * d20 + 99842625 * d21 + 44643360 * d23 + 0 * d24 + 27454871 * d25 + 9711365 * d26)) ≤ (((100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24) + 27454871 * tK (bitOf T 25) + 9711365 * tK (bitOf T 26)) - (57979000000000 + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 44643360 * tP (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 27454871 * tP (bitOf T 25) (selXf (bitOf T 25) top bk pb (l5) (u5) (q5)) + 9711365 * tP (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6))) : ℕ) : ℝ) := by
    have := natsub_ge (100000000 * tK (bitOf T 5) + 200000000 * tK (bitOf T 6) + 68858644 * tK (bitOf T 11) + 100000000 * tK (bitOf T 12) + 157375 * tK (bitOf T 16) + 65570678 * tK (bitOf T 17) + 67808981 * tK (bitOf T 20) + 99842625 * tK (bitOf T 21) + 44643360 * tK (bitOf T 23) + 0 * tK (bitOf T 24) + 27454871 * tK (bitOf T 25) + 9711365 * tK (bitOf T 26)) (57979000000000 + 100000000 * tP (bitOf T 5) (selXf (bitOf T 5) top bk pb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5)) + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 68858644 * tP (bitOf T 11) (selXf (bitOf T 11) top bk pb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 157375 * tP (bitOf T 16) (selXf (bitOf T 16) top bk pb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 67808981 * tP (bitOf T 20) (selXf (bitOf T 20) top bk pb (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 44643360 * tP (bitOf T 23) (selXf (bitOf T 23) top bk pb (l4 + l5) (u4 + u5) (q4 + q5)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 27454871 * tP (bitOf T 25) (selXf (bitOf T 25) top bk pb (l5) (u5) (q5)) + 9711365 * tP (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)))
    push_cast at this
    linarith [hdl5, hdl6, hdl11, hdl12, hdl16, hdl17, hdl20, hdl21, hdl23, hdl24, hdl25, hdl26]
  have hml5 : ((q5 - l5 : ℕ) : ℝ) = (q5 : ℝ) - l5 := Nat.cast_sub hq51
  have hum5 : ((u5 - q5 : ℕ) : ℝ) = (u5 : ℝ) - q5 := Nat.cast_sub hq52
  have ht5 := mterm (e := g5 - (q5 : ℝ) / 32768) (E := ((57979 : ℝ) + 100000000 * d5 + 200000000 * d6 + 68858644 * d11 + 100000000 * d12 + 157375 * d16 + 65570678 * d17 + 67808981 * d20 + 99842625 * d21 + 44643360 * d23 + 0 * d24 + 27454871 * d25 + 9711365 * d26)) (lo := ((q5 - l5 : ℕ) : ℝ) / 32768)
    (hi := ((u5 - q5 : ℕ) : ℝ) / 32768) (by rw [hml5]; linarith [h51]) (by rw [hum5]; linarith [h52])
    (by positivity) (by positivity) hP5 hN5 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP6 : (1000000000 : ℝ) * ((32954 : ℝ) + 200000000 * d6 + 100000000 * d12 + 65570678 * d17 + 99842625 * d21 + 0 * d24 + 9711365 * d26 + 16529847 * d27) ≤ (((32954000000000 + 200000000 * tK (bitOf T 6) + 100000000 * tK (bitOf T 12) + 65570678 * tK (bitOf T 17) + 99842625 * tK (bitOf T 21) + 0 * tK (bitOf T 24) + 9711365 * tK (bitOf T 26) + 16529847 * tK (bitOf T 27)) - (200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 9711365 * tM (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)) + 16529847 * tM (bitOf T 27) (selXf (bitOf T 27) top bk pb (l6) (u6) (q6))) : ℕ) : ℝ) := by
    have := natsub_ge (32954000000000 + 200000000 * tK (bitOf T 6) + 100000000 * tK (bitOf T 12) + 65570678 * tK (bitOf T 17) + 99842625 * tK (bitOf T 21) + 0 * tK (bitOf T 24) + 9711365 * tK (bitOf T 26) + 16529847 * tK (bitOf T 27)) (200000000 * tM (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 100000000 * tM (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 65570678 * tM (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 99842625 * tM (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 0 * tM (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 9711365 * tM (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)) + 16529847 * tM (bitOf T 27) (selXf (bitOf T 27) top bk pb (l6) (u6) (q6)))
    push_cast at this
    linarith [hdu6, hdu12, hdu17, hdu21, hdu24, hdu26, hdu27]
  have hN6 : -((1000000000 : ℝ) * ((32954 : ℝ) + 200000000 * d6 + 100000000 * d12 + 65570678 * d17 + 99842625 * d21 + 0 * d24 + 9711365 * d26 + 16529847 * d27)) ≤ (((200000000 * tK (bitOf T 6) + 100000000 * tK (bitOf T 12) + 65570678 * tK (bitOf T 17) + 99842625 * tK (bitOf T 21) + 0 * tK (bitOf T 24) + 9711365 * tK (bitOf T 26) + 16529847 * tK (bitOf T 27)) - (32954000000000 + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 9711365 * tP (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)) + 16529847 * tP (bitOf T 27) (selXf (bitOf T 27) top bk pb (l6) (u6) (q6))) : ℕ) : ℝ) := by
    have := natsub_ge (200000000 * tK (bitOf T 6) + 100000000 * tK (bitOf T 12) + 65570678 * tK (bitOf T 17) + 99842625 * tK (bitOf T 21) + 0 * tK (bitOf T 24) + 9711365 * tK (bitOf T 26) + 16529847 * tK (bitOf T 27)) (32954000000000 + 200000000 * tP (bitOf T 6) (selXf (bitOf T 6) top bk pb (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) (q0 + q1 + q2 + q3 + q4 + q5 + q6)) + 100000000 * tP (bitOf T 12) (selXf (bitOf T 12) top bk pb (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) (q1 + q2 + q3 + q4 + q5 + q6)) + 65570678 * tP (bitOf T 17) (selXf (bitOf T 17) top bk pb (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) (q2 + q3 + q4 + q5 + q6)) + 99842625 * tP (bitOf T 21) (selXf (bitOf T 21) top bk pb (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) (q3 + q4 + q5 + q6)) + 0 * tP (bitOf T 24) (selXf (bitOf T 24) top bk pb (l4 + l5 + l6) (u4 + u5 + u6) (q4 + q5 + q6)) + 9711365 * tP (bitOf T 26) (selXf (bitOf T 26) top bk pb (l5 + l6) (u5 + u6) (q5 + q6)) + 16529847 * tP (bitOf T 27) (selXf (bitOf T 27) top bk pb (l6) (u6) (q6)))
    push_cast at this
    linarith [hdl6, hdl12, hdl17, hdl21, hdl24, hdl26, hdl27]
  have hml6 : ((q6 - l6 : ℕ) : ℝ) = (q6 : ℝ) - l6 := Nat.cast_sub hq61
  have hum6 : ((u6 - q6 : ℕ) : ℝ) = (u6 : ℝ) - q6 := Nat.cast_sub hq62
  have ht6 := mterm (e := g6 - (q6 : ℝ) / 32768) (E := ((32954 : ℝ) + 200000000 * d6 + 100000000 * d12 + 65570678 * d17 + 99842625 * d21 + 0 * d24 + 9711365 * d26 + 16529847 * d27)) (lo := ((q6 - l6 : ℕ) : ℝ) / 32768)
    (hi := ((u6 - q6 : ℕ) : ℝ) / 32768) (by rw [hml6]; linarith [h61]) (by rw [hum6]; linarith [h62])
    (by positivity) (by positivity) hP6 hN6 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5, hml6, hum6] at hq
  simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5, hml6, hum6] at ht0 ht1 ht2 ht3 ht4 ht5 ht6
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
      + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)) * SA
      = 32954 * g0 + 57979 * g1 + 68753 * g2 + 80628 * g3 + 68753 * g4 + 57979 * g5 + 32954 * g6 + 16529847 * wfun (g0) + 9711365 * wfun (g0 + g1) + 0 * wfun (g0 + g1 + g2) + 99842625 * wfun (g0 + g1 + g2 + g3) + 65570678 * wfun (g0 + g1 + g2 + g3 + g4) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + 27454871 * wfun (g1) + 44643360 * wfun (g1 + g2) + 67808981 * wfun (g1 + g2 + g3) + 157375 * wfun (g1 + g2 + g3 + g4) + 68858644 * wfun (g1 + g2 + g3 + g4 + g5) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5 + g6) + 34948217 * wfun (g2) + 45645275 * wfun (g2 + g3) + 64382038 * wfun (g2 + g3 + g4) + 157375 * wfun (g2 + g3 + g4 + g5) + 65570678 * wfun (g2 + g3 + g4 + g5 + g6) + 42134130 * wfun (g3) + 45645275 * wfun (g3 + g4) + 67808981 * wfun (g3 + g4 + g5) + 99842625 * wfun (g3 + g4 + g5 + g6) + 34948217 * wfun (g4) + 44643360 * wfun (g4 + g5) + 0 * wfun (g4 + g5 + g6) + 27454871 * wfun (g5) + 9711365 * wfun (g5 + g6) + 16529847 * wfun (g6) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 701466 := by norm_num [cN]
  rw [hcN]
  linarith [hq, ht0, ht1, ht2, ht3, ht4, ht5, ht6, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 16529847), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 68858644), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 64382038), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 42134130), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb21 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb22 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb23 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb24 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb25 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb26 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb27 (by norm_num : (0:ℝ) ≤ 16529847)]

theorem covered_of_ctest {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (q0 q1 q2 q3 q4 q5 q6 : ℕ) (T : ℕ) (h : ctest top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T = true) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  exact Or.inl (ctest_sound hlb hD hpt hR l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 q0 q1 q2 q3 q4 q5 q6 T h g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)

set_option maxHeartbeats 40000000 in
theorem mscheck_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) (k21 m21 p21 r21 : ℕ) (k22 m22 p22 r22 : ℕ) (k23 m23 p23 r23 : ℕ) (k25 m25 p25 r25 : ℕ) (k26 m26 p26 r26 : ℕ) (k27 m27 p27 r27 : ℕ) (h : mscheck top bk tD bD f R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 k0 m0 p0 r0 k1 m1 p1 r1 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20 k21 m21 p21 r21 k22 m22 p22 r22 k23 m23 p23 r23 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  unfold mscheck at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlu0, hlu1⟩, hlu2⟩, hlu3⟩, hlu4⟩, hlu5⟩, hlu6⟩, hm0⟩, hok0⟩, hm1⟩, hok1⟩, hm3⟩, hok3⟩, hm4⟩, hok4⟩, hm5⟩, hok5⟩, hm6⟩, hok6⟩, hm7⟩, hok7⟩, hm8⟩, hok8⟩, hm9⟩, hok9⟩, hm10⟩, hok10⟩, hm11⟩, hok11⟩, hm12⟩, hok12⟩, hm13⟩, hok13⟩, hm14⟩, hok14⟩, hm15⟩, hok15⟩, hm16⟩, hok16⟩, hm17⟩, hok17⟩, hm18⟩, hok18⟩, hm19⟩, hok19⟩, hm20⟩, hok20⟩, hm21⟩, hok21⟩, hm22⟩, hok22⟩, hm23⟩, hok23⟩, hm25⟩, hok25⟩, hm26⟩, hok26⟩, hm27⟩, hok27⟩, hmain⟩ := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨D0, hDl0, hb0⟩ := mterm_ok hlb hD hpt hR (l0) (u0) k0 m0 p0 r0 hm0 hok0
    (g0) h01 h02
  push_cast at hb0
  obtain ⟨D1, hDl1, hb1⟩ := mterm_ok hlb hD hpt hR (l0 + l1) (u0 + u1) k1 m1 p1 r1 hm1 hok1
    (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  push_cast at hb1
  obtain ⟨D3, hDl3, hb3⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) k3 m3 p3 r3 hm3 hok3
    (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  push_cast at hb3
  obtain ⟨D4, hDl4, hb4⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) k4 m4 p4 r4 hm4 hok4
    (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  push_cast at hb4
  obtain ⟨D5, hDl5, hb5⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) k5 m5 p5 r5 hm5 hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  push_cast at hb5
  obtain ⟨D6, hDl6, hb6⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4 + l5 + l6) (u0 + u1 + u2 + u3 + u4 + u5 + u6) k6 m6 p6 r6 hm6 hok6
    (g0 + g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52) h62)
  push_cast at hb6
  obtain ⟨D7, hDl7, hb7⟩ := mterm_ok hlb hD hpt hR (l1) (u1) k7 m7 p7 r7 hm7 hok7
    (g1) h11 h12
  push_cast at hb7
  obtain ⟨D8, hDl8, hb8⟩ := mterm_ok hlb hD hpt hR (l1 + l2) (u1 + u2) k8 m8 p8 r8 hm8 hok8
    (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  push_cast at hb8
  obtain ⟨D9, hDl9, hb9⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3) (u1 + u2 + u3) k9 m9 p9 r9 hm9 hok9
    (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  push_cast at hb9
  obtain ⟨D10, hDl10, hb10⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) k10 m10 p10 r10 hm10 hok10
    (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  push_cast at hb10
  obtain ⟨D11, hDl11, hb11⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) k11 m11 p11 r11 hm11 hok11
    (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  push_cast at hb11
  obtain ⟨D12, hDl12, hb12⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4 + l5 + l6) (u1 + u2 + u3 + u4 + u5 + u6) k12 m12 p12 r12 hm12 hok12
    (g1 + g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52) h62)
  push_cast at hb12
  obtain ⟨D13, hDl13, hb13⟩ := mterm_ok hlb hD hpt hR (l2) (u2) k13 m13 p13 r13 hm13 hok13
    (g2) h21 h22
  push_cast at hb13
  obtain ⟨D14, hDl14, hb14⟩ := mterm_ok hlb hD hpt hR (l2 + l3) (u2 + u3) k14 m14 p14 r14 hm14 hok14
    (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  push_cast at hb14
  obtain ⟨D15, hDl15, hb15⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4) (u2 + u3 + u4) k15 m15 p15 r15 hm15 hok15
    (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  push_cast at hb15
  obtain ⟨D16, hDl16, hb16⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) k16 m16 p16 r16 hm16 hok16
    (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  push_cast at hb16
  obtain ⟨D17, hDl17, hb17⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4 + l5 + l6) (u2 + u3 + u4 + u5 + u6) k17 m17 p17 r17 hm17 hok17
    (g2 + g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add (slo_add h21 h31) h41) h51) h61) (shi_add (shi_add (shi_add (shi_add h22 h32) h42) h52) h62)
  push_cast at hb17
  obtain ⟨D18, hDl18, hb18⟩ := mterm_ok hlb hD hpt hR (l3) (u3) k18 m18 p18 r18 hm18 hok18
    (g3) h31 h32
  push_cast at hb18
  obtain ⟨D19, hDl19, hb19⟩ := mterm_ok hlb hD hpt hR (l3 + l4) (u3 + u4) k19 m19 p19 r19 hm19 hok19
    (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  push_cast at hb19
  obtain ⟨D20, hDl20, hb20⟩ := mterm_ok hlb hD hpt hR (l3 + l4 + l5) (u3 + u4 + u5) k20 m20 p20 r20 hm20 hok20
    (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  push_cast at hb20
  obtain ⟨D21, hDl21, hb21⟩ := mterm_ok hlb hD hpt hR (l3 + l4 + l5 + l6) (u3 + u4 + u5 + u6) k21 m21 p21 r21 hm21 hok21
    (g3 + g4 + g5 + g6) (slo_add (slo_add (slo_add h31 h41) h51) h61) (shi_add (shi_add (shi_add h32 h42) h52) h62)
  push_cast at hb21
  obtain ⟨D22, hDl22, hb22⟩ := mterm_ok hlb hD hpt hR (l4) (u4) k22 m22 p22 r22 hm22 hok22
    (g4) h41 h42
  push_cast at hb22
  obtain ⟨D23, hDl23, hb23⟩ := mterm_ok hlb hD hpt hR (l4 + l5) (u4 + u5) k23 m23 p23 r23 hm23 hok23
    (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  push_cast at hb23
  obtain ⟨D25, hDl25, hb25⟩ := mterm_ok hlb hD hpt hR (l5) (u5) k25 m25 p25 r25 hm25 hok25
    (g5) h51 h52
  push_cast at hb25
  obtain ⟨D26, hDl26, hb26⟩ := mterm_ok hlb hD hpt hR (l5 + l6) (u5 + u6) k26 m26 p26 r26 hm26 hok26
    (g5 + g6) (slo_add h51 h61) (shi_add h52 h62)
  push_cast at hb26
  obtain ⟨D27, hDl27, hb27⟩ := mterm_ok hlb hD hpt hR (l6) (u6) k27 m27 p27 r27 hm27 hok27
    (g6) h61 h62
  push_cast at hb27
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  have hN0 : -((((2000000000 * (16529847 * (mw1 k0 m0 + mw2 k0 m0) + 9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6))) - (33744896000000000 + 16529847 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 32954 : ℝ) + 16529847 * D0 + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6) := by
    have := natsub_ge (2000000000 * (16529847 * (mw1 k0 m0 + mw2 k0 m0) + 9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6))) (33744896000000000 + 16529847 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6)
    push_cast at this ⊢
    linarith [hDl0, hDl1, hDl3, hDl4, hDl5, hDl6]
  have hlu0' : ((u0 - l0 : ℕ) : ℝ) = (u0 : ℝ) - l0 := Nat.cast_sub hlu0
  have hg0 := gap_lo (E := ((1024 * 32954 : ℝ) + 16529847 * D0 + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6)) (e := g0 - (l0 : ℝ) / 32768) (H := ((u0 - l0 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN0 (by linarith [h01]) (by rw [hlu0']; linarith [h02])
  have hN1 : -((((2000000000 * (9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 27454871 * (mw1 k7 m7 + mw2 k7 m7) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12))) - (59370496000000000 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 27454871 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 57979 : ℝ) + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 27454871 * D7 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12) := by
    have := natsub_ge (2000000000 * (9711365 * (mw1 k1 m1 + mw2 k1 m1) + 99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 27454871 * (mw1 k7 m7 + mw2 k7 m7) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12))) (59370496000000000 + 9711365 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 27454871 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12)
    push_cast at this ⊢
    linarith [hDl1, hDl3, hDl4, hDl5, hDl6, hDl7, hDl8, hDl9, hDl10, hDl11, hDl12]
  have hlu1' : ((u1 - l1 : ℕ) : ℝ) = (u1 : ℝ) - l1 := Nat.cast_sub hlu1
  have hg1 := gap_lo (E := ((1024 * 57979 : ℝ) + 9711365 * D1 + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 27454871 * D7 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12)) (e := g1 - (l1 : ℝ) / 32768) (H := ((u1 - l1 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN1 (by linarith [h11]) (by rw [hlu1']; linarith [h12])
  have hN2 : -((((2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 34948217 * (mw1 k13 m13 + mw2 k13 m13) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17))) - (70403072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 34948217 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 68753 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 34948217 * D13 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17) := by
    have := natsub_ge (2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 44643360 * (mw1 k8 m8 + mw2 k8 m8) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 34948217 * (mw1 k13 m13 + mw2 k13 m13) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17))) (70403072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 44643360 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 34948217 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)
    push_cast at this ⊢
    linarith [hDl3, hDl4, hDl5, hDl6, hDl8, hDl9, hDl10, hDl11, hDl12, hDl13, hDl14, hDl15, hDl16, hDl17]
  have hlu2' : ((u2 - l2 : ℕ) : ℝ) = (u2 : ℝ) - l2 := Nat.cast_sub hlu2
  have hg2 := gap_lo (E := ((1024 * 68753 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 44643360 * D8 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 34948217 * D13 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17)) (e := g2 - (l2 : ℝ) / 32768) (H := ((u2 - l2 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN2 (by linarith [h21]) (by rw [hlu2']; linarith [h22])
  have hN3 : -((((2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 42134130 * (mw1 k18 m18 + mw2 k18 m18) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21))) - (82563072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 42134130 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 80628 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 42134130 * D18 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21) := by
    have := natsub_ge (2000000000 * (99842625 * (mw1 k3 m3 + mw2 k3 m3) + 65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 67808981 * (mw1 k9 m9 + mw2 k9 m9) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 45645275 * (mw1 k14 m14 + mw2 k14 m14) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 42134130 * (mw1 k18 m18 + mw2 k18 m18) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21))) (82563072000000000 + 99842625 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 67808981 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 45645275 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 42134130 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21)
    push_cast at this ⊢
    linarith [hDl3, hDl4, hDl5, hDl6, hDl9, hDl10, hDl11, hDl12, hDl14, hDl15, hDl16, hDl17, hDl18, hDl19, hDl20, hDl21]
  have hlu3' : ((u3 - l3 : ℕ) : ℝ) = (u3 : ℝ) - l3 := Nat.cast_sub hlu3
  have hg3 := gap_lo (E := ((1024 * 80628 : ℝ) + 99842625 * D3 + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 67808981 * D9 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 45645275 * D14 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 42134130 * D18 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21)) (e := g3 - (l3 : ℝ) / 32768) (H := ((u3 - l3 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN3 (by linarith [h31]) (by rw [hlu3']; linarith [h32])
  have hN4 : -((((2000000000 * (65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 34948217 * (mw1 k22 m22 + mw2 k22 m22) + 44643360 * (mw1 k23 m23 + mw2 k23 m23))) - (70403072000000000 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 34948217 * msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 68753 : ℝ) + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21 + 34948217 * D22 + 44643360 * D23) := by
    have := natsub_ge (2000000000 * (65570678 * (mw1 k4 m4 + mw2 k4 m4) + 100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 157375 * (mw1 k10 m10 + mw2 k10 m10) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 64382038 * (mw1 k15 m15 + mw2 k15 m15) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 45645275 * (mw1 k19 m19 + mw2 k19 m19) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 34948217 * (mw1 k22 m22 + mw2 k22 m22) + 44643360 * (mw1 k23 m23 + mw2 k23 m23))) (70403072000000000 + 65570678 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 157375 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 64382038 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 45645275 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 34948217 * msl f (mw1 k22 m22) (mw2 k22 m22) p22 r22 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23)
    push_cast at this ⊢
    linarith [hDl4, hDl5, hDl6, hDl10, hDl11, hDl12, hDl15, hDl16, hDl17, hDl19, hDl20, hDl21, hDl22, hDl23]
  have hlu4' : ((u4 - l4 : ℕ) : ℝ) = (u4 : ℝ) - l4 := Nat.cast_sub hlu4
  have hg4 := gap_lo (E := ((1024 * 68753 : ℝ) + 65570678 * D4 + 100000000 * D5 + 200000000 * D6 + 157375 * D10 + 68858644 * D11 + 100000000 * D12 + 64382038 * D15 + 157375 * D16 + 65570678 * D17 + 45645275 * D19 + 67808981 * D20 + 99842625 * D21 + 34948217 * D22 + 44643360 * D23)) (e := g4 - (l4 : ℝ) / 32768) (H := ((u4 - l4 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN4 (by linarith [h41]) (by rw [hlu4']; linarith [h42])
  have hN5 : -((((2000000000 * (100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 44643360 * (mw1 k23 m23 + mw2 k23 m23) + 27454871 * (mw1 k25 m25 + mw2 k25 m25) + 9711365 * (mw1 k26 m26 + mw2 k26 m26))) - (59370496000000000 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23 + 27454871 * msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 57979 : ℝ) + 100000000 * D5 + 200000000 * D6 + 68858644 * D11 + 100000000 * D12 + 157375 * D16 + 65570678 * D17 + 67808981 * D20 + 99842625 * D21 + 44643360 * D23 + 27454871 * D25 + 9711365 * D26) := by
    have := natsub_ge (2000000000 * (100000000 * (mw1 k5 m5 + mw2 k5 m5) + 200000000 * (mw1 k6 m6 + mw2 k6 m6) + 68858644 * (mw1 k11 m11 + mw2 k11 m11) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 157375 * (mw1 k16 m16 + mw2 k16 m16) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 67808981 * (mw1 k20 m20 + mw2 k20 m20) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 44643360 * (mw1 k23 m23 + mw2 k23 m23) + 27454871 * (mw1 k25 m25 + mw2 k25 m25) + 9711365 * (mw1 k26 m26 + mw2 k26 m26))) (59370496000000000 + 100000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 68858644 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 157375 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 67808981 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 44643360 * msl f (mw1 k23 m23) (mw2 k23 m23) p23 r23 + 27454871 * msl f (mw1 k25 m25) (mw2 k25 m25) p25 r25 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26)
    push_cast at this ⊢
    linarith [hDl5, hDl6, hDl11, hDl12, hDl16, hDl17, hDl20, hDl21, hDl23, hDl25, hDl26]
  have hlu5' : ((u5 - l5 : ℕ) : ℝ) = (u5 : ℝ) - l5 := Nat.cast_sub hlu5
  have hg5 := gap_lo (E := ((1024 * 57979 : ℝ) + 100000000 * D5 + 200000000 * D6 + 68858644 * D11 + 100000000 * D12 + 157375 * D16 + 65570678 * D17 + 67808981 * D20 + 99842625 * D21 + 44643360 * D23 + 27454871 * D25 + 9711365 * D26)) (e := g5 - (l5 : ℝ) / 32768) (H := ((u5 - l5 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN5 (by linarith [h51]) (by rw [hlu5']; linarith [h52])
  have hN6 : -((((2000000000 * (200000000 * (mw1 k6 m6 + mw2 k6 m6) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 9711365 * (mw1 k26 m26 + mw2 k26 m26) + 16529847 * (mw1 k27 m27 + mw2 k27 m27))) - (33744896000000000 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26 + 16529847 * msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 32954 : ℝ) + 200000000 * D6 + 100000000 * D12 + 65570678 * D17 + 99842625 * D21 + 9711365 * D26 + 16529847 * D27) := by
    have := natsub_ge (2000000000 * (200000000 * (mw1 k6 m6 + mw2 k6 m6) + 100000000 * (mw1 k12 m12 + mw2 k12 m12) + 65570678 * (mw1 k17 m17 + mw2 k17 m17) + 99842625 * (mw1 k21 m21 + mw2 k21 m21) + 9711365 * (mw1 k26 m26 + mw2 k26 m26) + 16529847 * (mw1 k27 m27 + mw2 k27 m27))) (33744896000000000 + 200000000 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 100000000 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 65570678 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 99842625 * msl f (mw1 k21 m21) (mw2 k21 m21) p21 r21 + 9711365 * msl f (mw1 k26 m26) (mw2 k26 m26) p26 r26 + 16529847 * msl f (mw1 k27 m27) (mw2 k27 m27) p27 r27)
    push_cast at this ⊢
    linarith [hDl6, hDl12, hDl17, hDl21, hDl26, hDl27]
  have hlu6' : ((u6 - l6 : ℕ) : ℝ) = (u6 : ℝ) - l6 := Nat.cast_sub hlu6
  have hg6 := gap_lo (E := ((1024 * 32954 : ℝ) + 200000000 * D6 + 100000000 * D12 + 65570678 * D17 + 99842625 * D21 + 9711365 * D26 + 16529847 * D27)) (e := g6 - (l6 : ℝ) / 32768) (H := ((u6 - l6 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN6 (by linarith [h61]) (by rw [hlu6']; linarith [h62])
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  simp only [hlu0', hlu1', hlu2', hlu3', hlu4', hlu5', hlu6'] at hq hg0 hg1 hg2 hg3 hg4 hg5 hg6
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6
      + (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6)) * SA
      = 32954 * g0 + 57979 * g1 + 68753 * g2 + 80628 * g3 + 68753 * g4 + 57979 * g5 + 32954 * g6 + 16529847 * wfun (g0) + 9711365 * wfun (g0 + g1) + 99842625 * wfun (g0 + g1 + g2 + g3) + 65570678 * wfun (g0 + g1 + g2 + g3 + g4) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + 27454871 * wfun (g1) + 44643360 * wfun (g1 + g2) + 67808981 * wfun (g1 + g2 + g3) + 157375 * wfun (g1 + g2 + g3 + g4) + 68858644 * wfun (g1 + g2 + g3 + g4 + g5) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5 + g6) + 34948217 * wfun (g2) + 45645275 * wfun (g2 + g3) + 64382038 * wfun (g2 + g3 + g4) + 157375 * wfun (g2 + g3 + g4 + g5) + 65570678 * wfun (g2 + g3 + g4 + g5 + g6) + 42134130 * wfun (g3) + 45645275 * wfun (g3 + g4) + 67808981 * wfun (g3 + g4 + g5) + 99842625 * wfun (g3 + g4 + g5 + g6) + 34948217 * wfun (g4) + 44643360 * wfun (g4 + g5) + 27454871 * wfun (g5) + 9711365 * wfun (g5 + g6) + 16529847 * wfun (g6) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 701466 := by norm_num [cN]
  rw [hcN]
  linarith [hq, hg0, hg1, hg2, hg3, hg4, hg5, hg6, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 16529847), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 68858644), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 64382038), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 157375), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 65570678), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 42134130), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 45645275), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 67808981), mul_le_mul_of_nonneg_left hb21 (by norm_num : (0:ℝ) ≤ 99842625), mul_le_mul_of_nonneg_left hb22 (by norm_num : (0:ℝ) ≤ 34948217), mul_le_mul_of_nonneg_left hb23 (by norm_num : (0:ℝ) ≤ 44643360), mul_le_mul_of_nonneg_left hb25 (by norm_num : (0:ℝ) ≤ 27454871), mul_le_mul_of_nonneg_left hb26 (by norm_num : (0:ℝ) ≤ 9711365), mul_le_mul_of_nonneg_left hb27 (by norm_num : (0:ℝ) ≤ 16529847)]

theorem mleafN_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ)
    (h : mleafN top bk tD bD pb R w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  unfold mleafN at h
  simp only [forceR_eq] at h
  exact mscheck_sound (f := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h)

/-- a box split on gap 0 at `q` is covered when both halves are -/
theorem covered_split0 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 q l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered q u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g0 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 hq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 hq h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 1 at `q` is covered when both halves are -/
theorem covered_split1 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 q l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 q u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g1 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 hq h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 hq h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 2 at `q` is covered when both halves are -/
theorem covered_split2 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 q l3 u3 l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 q u2 l3 u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g2 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 hq h31 h32 h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 hq h22 h31 h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 3 at `q` is covered when both halves are -/
theorem covered_split3 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 q l4 u4 l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 q u3 l4 u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g3 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 hq h41 h42 h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 hq h32 h41 h42 h51 h52 h61 h62

/-- a box split on gap 4 at `q` is covered when both halves are -/
theorem covered_split4 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 q l5 u5 l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 q u4 l5 u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g4 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 hq h51 h52 h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 hq h42 h51 h52 h61 h62

/-- a box split on gap 5 at `q` is covered when both halves are -/
theorem covered_split5 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 q l6 u6) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 q u5 l6 u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g5 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 hq h61 h62
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 hq h52 h61 h62

/-- a box split on gap 6 at `q` is covered when both halves are -/
theorem covered_split6 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 q) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q u6) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  rcases le_total g6 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 hq
  · exact hB g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 hq h62

/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ, f pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 → Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6

theorem split0_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split0 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split0 _ hA (hih _ (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split1_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split1 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6) l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split1 _ hA (hih _ l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split2_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split2 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6) l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split2 _ hA (hih _ l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split3_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split3 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6) l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split3 _ hA (hih _ l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split4_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split4 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6) l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) l5 u5 l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split4 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 l5 u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split5_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split5 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split5 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 l6 u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 (Nat.shiftRight (Nat.add l5 u5) 1) l6 u6 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split5 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (Nat.shiftRight (Nat.add l5 u5) 1) u5 l6 u6 h')
  · exact absurd (by simp only [hp]) h

theorem split6_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : split6 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold split6 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1)) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1)) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (Nat.shiftRight (Nat.add l6 u6) 1) u6 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 (Nat.shiftRight (Nat.add l6 u6) 1) (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split6 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (Nat.shiftRight (Nat.add l6 u6) 1) u6 h')
  · exact absurd (by simp only [hp]) h

theorem splitAx_sound {ih : WF} (hih : WalkOK ih) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : splitAx ih pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
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
            cases ha5 : Nat.beq ax 5
            · rw [ha5] at h
              exact split6_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
            · rw [ha5] at h; exact split5_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
          · rw [ha4] at h; exact split4_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
        · rw [ha3] at h; exact split3_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
      · rw [ha2] at h; exact split2_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
    · rw [ha1] at h; exact split1_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
  · rw [ha0] at h; exact split0_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h

theorem sleaf_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  unfold sleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem cleaf_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (l6 : ℝ) / SC ≤ g6 → g6 ≤ (u6 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 := by
  unfold cleaf at h
  simp only [forceB_eq] at h
  exact ctest_sound (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- the basin boxes are covered -/
def BasOK (bas : List Bx) : Prop := ∀ b ∈ bas, Covered b.l0 b.u0 b.l1 b.u1 b.l2 b.u2 b.l3 b.u3 b.l4 b.u4 b.l5 b.u5 b.l6 b.u6

theorem inBas_sound {bas : List Bx} (hbas : BasOK bas) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) (h : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = true) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold inBas at h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, hin⟩ := h
  simp only [Bool.and_eq_true, Nat.ble_eq] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbl0, hbu0⟩, hbl1⟩, hbu1⟩, hbl2⟩, hbu2⟩, hbl3⟩, hbu3⟩, hbl4⟩, hbu4⟩, hbl5⟩, hbu5⟩, hbl6⟩, hbu6⟩ := hin
  intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
  exact hbas b hb g0 g1 g2 g3 g4 g5 g6 (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl0) (by norm_num [SC])) h01) (le_trans h02 (div_le_div_of_nonneg_right (by exact_mod_cast hbu0) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl1) (by norm_num [SC])) h11) (le_trans h12 (div_le_div_of_nonneg_right (by exact_mod_cast hbu1) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl2) (by norm_num [SC])) h21) (le_trans h22 (div_le_div_of_nonneg_right (by exact_mod_cast hbu2) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl3) (by norm_num [SC])) h31) (le_trans h32 (div_le_div_of_nonneg_right (by exact_mod_cast hbu3) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl4) (by norm_num [SC])) h41) (le_trans h42 (div_le_div_of_nonneg_right (by exact_mod_cast hbu4) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl5) (by norm_num [SC])) h51) (le_trans h52 (div_le_div_of_nonneg_right (by exact_mod_cast hbu5) (by norm_num [SC]))) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hbl6) (by norm_num [SC])) h61) (le_trans h62 (div_le_div_of_nonneg_right (by exact_mod_cast hbu6) (by norm_num [SC])))

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ)
    (h : leafStep top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 := by
  unfold leafStep at h
  cases hs : Nat.ble (Nat.add u6 1) l0
  · rw [hs] at h
    cases hk0 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0
    · rw [hk0] at h
      cases hk1 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1
      · rw [hk1] at h
        cases hk2 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2
        · rw [hk2] at h
          cases hl : cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
          · rw [hl] at h; exact absurd rfl h
          · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
            exact Or.inl (cleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 hl g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
        · rw [hk2] at h
          cases hsb : Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1
          · rw [hsb] at h
            cases hl : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
            · rw [hl] at h; exact absurd rfl h
            · exact inBas_sound hbas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 hl
          · rw [hsb, forceR_eq] at h
            intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
            refine Or.inl (mleafN_sound hlb hD hpt hR (Nat.shiftRight w 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 ?_ g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
            intro h0; rw [h0] at h; exact h rfl
      · rw [hk1] at h
        cases hl : sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
        · rw [hl] at h; exact absurd rfl h
        · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
          exact Or.inl (sleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 hl g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
    · rw [hk0] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6
      · rw [hl] at h; exact absurd rfl h
      · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
        exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 hl g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62)
  · intro g0 g1 g2 g3 g4 g5 g6 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62
    right
    have hsk : u6 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u6 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R C bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R C bas pos (Nat.shiftRight bits pos) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)
        (splitAx (walk top bk tD bD pb R C bas bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6)
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR hbas pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 e : ℕ)
    (h : walk top bk tD bD pb R C bas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 :=
  walk_sound hlb hD hpt hR hbas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 (h ▸ he)


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
theorem of_check (cover0 cover1 cover2 cover3 cover4 cover5 cover6 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 S5 S6 : ℕ)
    (hS0 : cN * SC ≤ 32954 * S0) (hS1 : cN * SC ≤ 57979 * S1) (hS2 : cN * SC ≤ 68753 * S2) (hS3 : cN * SC ≤ 80628 * S3) (hS4 : cN * SC ≤ 68753 * S4) (hS5 : cN * SC ≤ 57979 * S5) (hS6 : cN * SC ≤ 32954 * S6)
    (hcov0 : coverCheck 16529847 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 27454871 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 34948217 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 42134130 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 34948217 (SC / 2) S4 cover4 = true) (hcov5 : coverCheck 27454871 (SC / 2) S5 cover5 = true) (hcov6 : coverCheck 16529847 (SC / 2) S6 cover6 = true)
    (hwin : cN * 100 ≤ 19 * 16529847)
    (hrun : ∀ i0 i1 i2 i3 i4 i5 i6, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length → i5 < (badOf cover5).length → i6 < (badOf cover6).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2 ((badOf cover5).getD i5 (0, 0)).1 ((badOf cover5).getD i5 (0, 0)).2 ((badOf cover6).getD i6 (0, 0)).1 ((badOf cover6).getD i6 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 g5 g6 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → 0 ≤ g5 → 0 ≤ g6 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 g6 ∨ g6 < g0 := by
  intro g0 g1 g2 g3 g4 g5 g6 hg0 hg1 hg2 hg3 hg4 hg5 hg6
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (32954 / (SA:ℝ)) * g0 + (57979 / (SA:ℝ)) * g1 + (68753 / (SA:ℝ)) * g2 + (80628 / (SA:ℝ)) * g3 + (68753 / (SA:ℝ)) * g4 + (57979 / (SA:ℝ)) * g5 + (32954 / (SA:ℝ)) * g6 with hLin
  set Wt : ℝ := (16529847 / (SA:ℝ)) * wfun (g0) + (9711365 / (SA:ℝ)) * wfun (g0 + g1) + (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g1) + (44643360 / (SA:ℝ)) * wfun (g1 + g2) + (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g2) + (45645275 / (SA:ℝ)) * wfun (g2 + g3) + (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (42134130 / (SA:ℝ)) * wfun (g3) + (45645275 / (SA:ℝ)) * wfun (g3 + g4) + (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (34948217 / (SA:ℝ)) * wfun (g4) + (44643360 / (SA:ℝ)) * wfun (g4 + g5) + (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (27454871 / (SA:ℝ)) * wfun (g5) + (9711365 / (SA:ℝ)) * wfun (g5 + g6) + (16529847 / (SA:ℝ)) * wfun (g6) with hWt
  have hG : G g0 g1 g2 g3 g4 g5 g6 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (32954 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (57979 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (68753 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (80628 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (68753 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have hb50 : (0:ℝ) ≤ (57979 / (SA:ℝ)) * g5 := mul_nonneg (by positivity) hg5
  have hb60 : (0:ℝ) ≤ (32954 / (SA:ℝ)) * g6 := mul_nonneg (by positivity) hg6
  have ha00 : (0:ℝ) ≤ (16529847 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (9711365 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99842625 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (65570678 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (27454871 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (44643360 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (67808981 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (157375 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (68858644 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (34948217 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (45645275 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha150 : (0:ℝ) ≤ (64382038 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha160 : (0:ℝ) ≤ (157375 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha170 : (0:ℝ) ≤ (65570678 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha180 : (0:ℝ) ≤ (42134130 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha190 : (0:ℝ) ≤ (45645275 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha200 : (0:ℝ) ≤ (67808981 / (SA:ℝ)) * wfun (g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha210 : (0:ℝ) ≤ (99842625 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha220 : (0:ℝ) ≤ (34948217 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have ha230 : (0:ℝ) ≤ (44643360 / (SA:ℝ)) * wfun (g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha240 : (0:ℝ) ≤ (0 / (SA:ℝ)) * wfun (g4 + g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha250 : (0:ℝ) ≤ (27454871 / (SA:ℝ)) * wfun (g5) := mul_nonneg (by positivity) (hw _)
  have ha260 : (0:ℝ) ≤ (9711365 / (SA:ℝ)) * wfun (g5 + g6) := mul_nonneg (by positivity) (hw _)
  have ha270 : (0:ℝ) ≤ (16529847 / (SA:ℝ)) * wfun (g6) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40, hb50, hb60]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260, ha270]
  have hbL0 : (32954 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40, hb50, hb60]
  have hbL1 : (57979 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40, hb50, hb60]
  have hbL2 : (68753 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40, hb50, hb60]
  have hbL3 : (80628 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40, hb50, hb60]
  have hbL4 : (68753 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb50, hb60]
  have hbL5 : (57979 / (SA:ℝ)) * g5 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40, hb60]
  have hbL6 : (32954 / (SA:ℝ)) * g6 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40, hb50]
  have haW0 : (16529847 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260, ha270]
  have haW7 : (27454871 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260, ha270]
  have haW13 : (34948217 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260, ha270]
  have haW18 : (42134130 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260, ha270]
  have haW22 : (34948217 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha230, ha240, ha250, ha260, ha270]
  have haW25 : (27454871 / (SA:ℝ)) * wfun (g5) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha260, ha270]
  have haW27 : (16529847 / (SA:ℝ)) * wfun (g6) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140, ha150, ha160, ha170, ha180, ha190, ha200, ha210, ha220, ha230, ha240, ha250, ha260]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (32954 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (32954 / (SA:ℝ)) * g0 * SA = 32954 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 32954 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 32954 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 32954 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (16529847 / (SA:ℝ)) * wfun g0 * SA = 16529847 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 16529847)
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
  · have h1 : (cN : ℝ) / SA ≤ (57979 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (57979 / (SA:ℝ)) * g1 * SA = 57979 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 57979 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 57979 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 57979 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (27454871 / (SA:ℝ)) * wfun g1 * SA = 27454871 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 27454871)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW7, hLin0]
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW7, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (68753 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (68753 / (SA:ℝ)) * g2 * SA = 68753 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 68753 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 68753 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 68753 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (34948217 / (SA:ℝ)) * wfun g2 * SA = 34948217 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 34948217)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW13, hLin0]
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW13, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (80628 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (80628 / (SA:ℝ)) * g3 * SA = 80628 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 80628 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 80628 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 80628 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (42134130 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (42134130 / (SA:ℝ)) * wfun g3 * SA = 42134130 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 42134130)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW18, hLin0]
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW18, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (68753 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (68753 / (SA:ℝ)) * g4 * SA = 68753 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 68753 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 68753 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 68753 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (34948217 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (34948217 / (SA:ℝ)) * wfun g4 * SA = 34948217 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 34948217)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW22, hLin0]
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW22, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  -- gap 5: beyond the cutoff the pressure alone pays
  by_cases hcut5 : (S5 : ℝ) / SC ≤ g5
  · have h1 : (cN : ℝ) / SA ≤ (57979 / (SA:ℝ)) * g5 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS5; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (57979 / (SA:ℝ)) * g5 * SA = 57979 * g5 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 57979 * S5 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 57979 * ((S5 : ℝ) / SC) := by ring
        _ ≤ 57979 * g5 := mul_le_mul_of_nonneg_left hcut5 (by norm_num)
    left; rw [hG]; linarith [h1, hbL5, hWt0]
  push_neg at hcut5
  rcases le_total g5 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin5 | hwin5
  · have hw19 := wfun_window g5 hg5 (by rw [hhalf] at hwin5; exact hwin5)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (27454871 / (SA:ℝ)) * wfun g5 := by
      rw [div_le_iff₀ hSA]
      have e : (27454871 / (SA:ℝ)) * wfun g5 * SA = 27454871 * wfun g5 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 27454871)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW25, hLin0]
  rcases cover_sound _ cover5 (SC / 2) S5 hcov5 g5 hwin5 hcut5 with hclear5 | ⟨s5, hs5, he5, hb51, hb52⟩
  · left; rw [hG]; linarith [hclear5, haW25, hLin0]
  obtain ⟨i5, hi5, hsi5⟩ := List.mem_iff_getElem.mp (badOf_mem hs5 he5)
  have hb51' : (((badOf cover5).getD i5 (0, 0)).1 : ℝ) / SC ≤ g5 := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb51
  have hb52' : g5 ≤ (((badOf cover5).getD i5 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb52
  -- gap 6: beyond the cutoff the pressure alone pays
  by_cases hcut6 : (S6 : ℝ) / SC ≤ g6
  · have h1 : (cN : ℝ) / SA ≤ (32954 / (SA:ℝ)) * g6 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS6; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (32954 / (SA:ℝ)) * g6 * SA = 32954 * g6 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 32954 * S6 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 32954 * ((S6 : ℝ) / SC) := by ring
        _ ≤ 32954 * g6 := mul_le_mul_of_nonneg_left hcut6 (by norm_num)
    left; rw [hG]; linarith [h1, hbL6, hWt0]
  push_neg at hcut6
  rcases le_total g6 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin6 | hwin6
  · have hw19 := wfun_window g6 hg6 (by rw [hhalf] at hwin6; exact hwin6)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (16529847 / (SA:ℝ)) * wfun g6 := by
      rw [div_le_iff₀ hSA]
      have e : (16529847 / (SA:ℝ)) * wfun g6 * SA = 16529847 * wfun g6 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 16529847)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW27, hLin0]
  rcases cover_sound _ cover6 (SC / 2) S6 hcov6 g6 hwin6 hcut6 with hclear6 | ⟨s6, hs6, he6, hb61, hb62⟩
  · left; rw [hG]; linarith [hclear6, haW27, hLin0]
  obtain ⟨i6, hi6, hsi6⟩ := List.mem_iff_getElem.mp (badOf_mem hs6 he6)
  have hb61' : (((badOf cover6).getD i6 (0, 0)).1 : ℝ) / SC ≤ g6 := by
    rw [List.getD_eq_getElem _ _ hi6, hsi6]; exact hb61
  have hb62' : g6 ≤ (((badOf cover6).getD i6 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi6, hsi6]; exact hb62
  exact hrun i0 i1 i2 i3 i4 i5 i6 hi0 hi1 hi2 hi3 hi4 hi5 hi6 g0 g1 g2 g3 g4 g5 g6 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42' hb51' hb52' hb61' hb62'

end Zeta23Ext.Bridge.ThreePoint.OctT

end
