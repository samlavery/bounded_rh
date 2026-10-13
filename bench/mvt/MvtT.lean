import MvtCore

set_option maxRecDepth 100000

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.MvtT

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD

def SA : ℕ := 100000000
def cN : ℕ := 354704

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24896 l0) (Nat.mul 42034 l1)) (Nat.mul 46137 l2)) (Nat.mul 42034 l3)) (Nat.mul 24896 l4)) 10000000000
  ee 116229406720000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 1580872499200 (lb top bk l1 u1))
  ee 116229406720000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1580872499200 (lb top bk l3 u3))
  ee 116229406720000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1732028006400 (lb top bk l2 u2))
  ee 116229406720000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 829908582400 (lb top bk l0 u0))
  ee 116229406720000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 116229406720000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 829908582400 (lb top bk l4 u4))
  ee 116229406720000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 116229406720000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 3923863142400 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 116229406720000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 116229406720000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 116229406720000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 116229406720000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 2043713945600 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 116229406720000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 1233082777600 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 116229406720000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 2043713945600 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 116229406720000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 1233082777600 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  Nat.ble 116229406720000000000 s15)))))))))))))))

/-- the centre of `[l, u]` for the mean-value expansion (any value is sound: the test checks `l ≤ m ≤ u`): the upper
end when the gap's derivative bound `Pos` is `0`, the lower end when `Neg` is `0`, else the midpoint; each rounded to a
multiple of `2^4` when that stays in the interval -/
def pick (l u P N : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (Nat.shiftRight (Nat.add l u) 1) fun m =>
        forceR (Nat.shiftLeft (Nat.shiftRight m 4) 4) fun mm =>
        Bool.rec (motive := fun _ => ℕ) m mm (Nat.ble l mm))
      (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l 15) 4) 4) fun mm =>
        Bool.rec (motive := fun _ => ℕ) l mm (Nat.ble mm u))
      (Nat.beq N 0))
    (forceR (Nat.shiftLeft (Nat.shiftRight u 4) 4) fun mm =>
      Bool.rec (motive := fun _ => ℕ) u mm (Nat.ble l mm))
    (Nat.beq P 0)

/-- the mean-value inequality at the centre `m`, given the derivative bounds `p_t`, `q_t` and the per-gap bounds
`P_r`, `N_r` -/
def mcore (pb : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (m0 m1 m2 m3 m4 p0 q0 p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7 p8 q8 p9 q9 p10 q10 p11 q11 p12 q12 p13 q13 p14 q14 P0 N0 P1 N1 P2 N2 P3 N3 P4 N4 : ℕ) : Bool :=
  (((((((((((((((((((((((((((((((((((((((Nat.ble l0 m0 && Nat.ble m0 u0) && Nat.ble l1 m1) && Nat.ble m1 u1) && Nat.ble l2 m2) && Nat.ble m2 u2) && Nat.ble l3 m3) && Nat.ble m3 u3) && Nat.ble l4 m4) && Nat.ble m4 u4) && Nat.ble 1 p0) && Nat.ble 1 q0) && Nat.ble 1 p1) && Nat.ble 1 q1) && Nat.ble 1 p2) && Nat.ble 1 q2) && Nat.ble 1 p3) && Nat.ble 1 q3) && Nat.ble 1 p4) && Nat.ble 1 q4) && Nat.ble 1 p5) && Nat.ble 1 q5) && Nat.ble 1 p6) && Nat.ble 1 q6) && Nat.ble 1 p7) && Nat.ble 1 q7) && Nat.ble 1 p8) && Nat.ble 1 q8) && Nat.ble 1 p9) && Nat.ble 1 q9) && Nat.ble 1 p10) && Nat.ble 1 q10) && Nat.ble 1 p11) && Nat.ble 1 q11) && Nat.ble 1 p12) && Nat.ble 1 q12) && Nat.ble 1 p13) && Nat.ble 1 q13) && Nat.ble 1 p14) && Nat.ble 1 q14) && Nat.ble (Nat.add 116229406720000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub m0 l0) P0) (Nat.mul (Nat.sub u0 m0) N0)) (Nat.mul (Nat.sub m1 l1) P1)) (Nat.mul (Nat.sub u1 m1) N1)) (Nat.mul (Nat.sub m2 l2) P2)) (Nat.mul (Nat.sub u2 m2) N2)) (Nat.mul (Nat.sub m3 l3) P3)) (Nat.mul (Nat.sub u3 m3) N3)) (Nat.mul (Nat.sub m4 l4) P4)) (Nat.mul (Nat.sub u4 m4) N4)))) (Nat.add (Nat.mul 10000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24896 m0) (Nat.mul 42034 m1)) (Nat.mul 46137 m2)) (Nat.mul 42034 m3)) (Nat.mul 24896 m4))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 25326800 (ptv pb m0)) (Nat.mul 62369200 (ptv pb (Nat.add m0 m1)))) (Nat.mul 40126500 (ptv pb (Nat.add (Nat.add m0 m1) m2)))) (Nat.mul 99999900 (ptv pb (Nat.add (Nat.add (Nat.add m0 m1) m2) m3)))) (Nat.mul 200000000 (ptv pb (Nat.add (Nat.add (Nat.add (Nat.add m0 m1) m2) m3) m4)))) (Nat.mul 48244400 (ptv pb m1))) (Nat.mul 37630700 (ptv pb (Nat.add m1 m2)))) (Nat.mul 119746800 (ptv pb (Nat.add (Nat.add m1 m2) m3)))) (Nat.mul 99999900 (ptv pb (Nat.add (Nat.add (Nat.add m1 m2) m3) m4)))) (Nat.mul 52857300 (ptv pb m2))) (Nat.mul 37630700 (ptv pb (Nat.add m2 m3)))) (Nat.mul 40126500 (ptv pb (Nat.add (Nat.add m2 m3) m4)))) (Nat.mul 48244400 (ptv pb m3))) (Nat.mul 62369200 (ptv pb (Nat.add m3 m4)))) (Nat.mul 25326800 (ptv pb m4)))))

/-- the mean-value leaf test at the centre `m` chosen by `pick`:
`cN·SC·U + (U/U1)·Σ_r ((m_r − l_r)·Pos_r + (u_r − m_r)·Neg_r) ≤ U·Σ b_r m_r + SC·Σ a_t v_t`, with `v_t` the point
bound of `w` at `s_t(m)`, `Pos_r = U1 b_r + KU1 A_r − Σ_(t∋r) a_t q_t` and `Neg_r = KU1 A_r − U1 b_r − Σ_(t∋r) a_t p_t`
(truncated at 0), `p_t`, `q_t` the bounds of `w' + 2` and `2 − w'` on the pair-sum interval (the halves of one read of
the pair pyramid, nonzero) -/
def mleafOK (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  forceB (lb2 tD bD l0 u0) fun e0 =>
  forceB (lb2 tD bD (Nat.add l0 l1) (Nat.add u0 u1)) fun e1 =>
  forceB (lb2 tD bD (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)) fun e2 =>
  forceB (lb2 tD bD (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)) fun e3 =>
  forceB (lb2 tD bD (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)) fun e4 =>
  forceB (lb2 tD bD l1 u1) fun e5 =>
  forceB (lb2 tD bD (Nat.add l1 l2) (Nat.add u1 u2)) fun e6 =>
  forceB (lb2 tD bD (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)) fun e7 =>
  forceB (lb2 tD bD (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)) fun e8 =>
  forceB (lb2 tD bD l2 u2) fun e9 =>
  forceB (lb2 tD bD (Nat.add l2 l3) (Nat.add u2 u3)) fun e10 =>
  forceB (lb2 tD bD (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)) fun e11 =>
  forceB (lb2 tD bD l3 u3) fun e12 =>
  forceB (lb2 tD bD (Nat.add l3 l4) (Nat.add u3 u4)) fun e13 =>
  forceB (lb2 tD bD l4 u4) fun e14 =>
  forceB (Nat.sub 855669696000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 25326800 (hi32 e0)) (Nat.mul 62369200 (hi32 e1))) (Nat.mul 40126500 (hi32 e2))) (Nat.mul 99999900 (hi32 e3))) (Nat.mul 200000000 (hi32 e4)))) fun P0 =>
  forceB (Nat.sub 855644800000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 24896000000000 (Nat.mul 25326800 (lo32 e0))) (Nat.mul 62369200 (lo32 e1))) (Nat.mul 40126500 (lo32 e2))) (Nat.mul 99999900 (lo32 e3))) (Nat.mul 200000000 (lo32 e4)))) fun N0 =>
  forceB (Nat.sub 1416276834000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 62369200 (hi32 e1)) (Nat.mul 40126500 (hi32 e2))) (Nat.mul 99999900 (hi32 e3))) (Nat.mul 200000000 (hi32 e4))) (Nat.mul 48244400 (hi32 e5))) (Nat.mul 37630700 (hi32 e6))) (Nat.mul 119746800 (hi32 e7))) (Nat.mul 99999900 (hi32 e8)))) fun P1 =>
  forceB (Nat.sub 1416234800000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 42034000000000 (Nat.mul 62369200 (lo32 e1))) (Nat.mul 40126500 (lo32 e2))) (Nat.mul 99999900 (lo32 e3))) (Nat.mul 200000000 (lo32 e4))) (Nat.mul 48244400 (lo32 e5))) (Nat.mul 37630700 (lo32 e6))) (Nat.mul 119746800 (lo32 e7))) (Nat.mul 99999900 (lo32 e8)))) fun N1 =>
  forceB (Nat.sub 1456282737000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 40126500 (hi32 e2)) (Nat.mul 99999900 (hi32 e3))) (Nat.mul 200000000 (hi32 e4))) (Nat.mul 37630700 (hi32 e6))) (Nat.mul 119746800 (hi32 e7))) (Nat.mul 99999900 (hi32 e8))) (Nat.mul 52857300 (hi32 e9))) (Nat.mul 37630700 (hi32 e10))) (Nat.mul 40126500 (hi32 e11)))) fun P2 =>
  forceB (Nat.sub 1456236600000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 46137000000000 (Nat.mul 40126500 (lo32 e2))) (Nat.mul 99999900 (lo32 e3))) (Nat.mul 200000000 (lo32 e4))) (Nat.mul 37630700 (lo32 e6))) (Nat.mul 119746800 (lo32 e7))) (Nat.mul 99999900 (lo32 e8))) (Nat.mul 52857300 (lo32 e9))) (Nat.mul 37630700 (lo32 e10))) (Nat.mul 40126500 (lo32 e11)))) fun N2 =>
  forceB (Nat.sub 1416276834000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99999900 (hi32 e3)) (Nat.mul 200000000 (hi32 e4))) (Nat.mul 119746800 (hi32 e7))) (Nat.mul 99999900 (hi32 e8))) (Nat.mul 37630700 (hi32 e10))) (Nat.mul 40126500 (hi32 e11))) (Nat.mul 48244400 (hi32 e12))) (Nat.mul 62369200 (hi32 e13)))) fun P3 =>
  forceB (Nat.sub 1416234800000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 42034000000000 (Nat.mul 99999900 (lo32 e3))) (Nat.mul 200000000 (lo32 e4))) (Nat.mul 119746800 (lo32 e7))) (Nat.mul 99999900 (lo32 e8))) (Nat.mul 37630700 (lo32 e10))) (Nat.mul 40126500 (lo32 e11))) (Nat.mul 48244400 (lo32 e12))) (Nat.mul 62369200 (lo32 e13)))) fun N3 =>
  forceB (Nat.sub 855669696000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (hi32 e4)) (Nat.mul 99999900 (hi32 e8))) (Nat.mul 40126500 (hi32 e11))) (Nat.mul 62369200 (hi32 e13))) (Nat.mul 25326800 (hi32 e14)))) fun P4 =>
  forceB (Nat.sub 855644800000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 24896000000000 (Nat.mul 200000000 (lo32 e4))) (Nat.mul 99999900 (lo32 e8))) (Nat.mul 40126500 (lo32 e11))) (Nat.mul 62369200 (lo32 e13))) (Nat.mul 25326800 (lo32 e14)))) fun N4 =>
  forceB (pick l0 u0 P0 N0) fun m0 =>
  forceB (pick l1 u1 P1 N1) fun m1 =>
  forceB (pick l2 u2 P2 N2) fun m2 =>
  forceB (pick l3 u3 P3 N3) fun m3 =>
  forceB (pick l4 u4 P4 N4) fun m4 =>
  mcore pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 m0 m1 m2 m3 m4 (lo32 e0) (hi32 e0) (lo32 e1) (hi32 e1) (lo32 e2) (hi32 e2) (lo32 e3) (hi32 e3) (lo32 e4) (hi32 e4) (lo32 e5) (hi32 e5) (lo32 e6) (hi32 e6) (lo32 e7) (hi32 e7) (lo32 e8) (hi32 e8) (lo32 e9) (hi32 e9) (lo32 e10) (hi32 e10) (lo32 e11) (hi32 e11) (lo32 e12) (hi32 e12) (lo32 e13) (hi32 e13) (lo32 e14) (hi32 e14) P0 N0 P1 N1 P2 N2 P3 N3 P4 N4

/-- the type of a walk continuation: position and the ten coordinates to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- a split on gap 0: the lower half (`u0 := q`) from `pos + 4`, then the upper half from where it ends -/
def split0 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l0 u0) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 q l1 u1 l2 u2 l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p q u0 l1 u1 l2 u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 1: the lower half (`u1 := q`) from `pos + 4`, then the upper half from where it ends -/
def split1 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l1 u1) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 q l2 u2 l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 q u1 l2 u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 2: the lower half (`u2 := q`) from `pos + 4`, then the upper half from where it ends -/
def split2 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l2 u2) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 q l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 q u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 3: the lower half (`u3 := q`) from `pos + 4`, then the upper half from where it ends -/
def split3 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l3 u3) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 q l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 q u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 4: the lower half (`u4 := q`) from `pos + 4`, then the upper half from where it ends -/
def split4 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l4 u4) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 q
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 q u4) (0) (Nat.beq p 0)

/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 3)) (split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 2)) (split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 1)) (split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 0)

/-- a leaf (two bits: `0`, then the test flag `fl`): in the reflected half-space, or the flagged leaf test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (pos fl l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 2) (Bool.rec (motive := fun _ => Bool) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (mleafOK tD bD pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq fl 1))) (Nat.add pos 2) (Nat.ble (Nat.add u4 1) l0)

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis; a leaf is bit 0 clear and bit 1 its test flag); the position
after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb pos (Nat.land (Nat.shiftRight w 1) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (splitAx ih pos (Nat.shiftRight w 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Prop :=
  ∀ g0 g1 g2 g3 g4 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0

theorem ee_or {C s : ℕ} {rest : Bool} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    116229406720000000000 ≤ 10000000000 * (24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) + 32768 * (25326800 * lb top bk (l0) (u0) + 62369200 * lb top bk (l0 + l1) (u0 + u1) + 40126500 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 99999900 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 48244400 * lb top bk (l1) (u1) + 37630700 * lb top bk (l1 + l2) (u1 + u2) + 119746800 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 99999900 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 52857300 * lb top bk (l2) (u2) + 37630700 * lb top bk (l2 + l3) (u2 + u3) + 40126500 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 48244400 * lb top bk (l3) (u3) + 62369200 * lb top bk (l3 + l4) (u3 + u4) + 25326800 * lb top bk (l4) (u4)) := by
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
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 4000000 in
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    ∀ g0 g1 g2 g3 g4 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
  have w0 := hlb (l0) (u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := hlb (l0 + l1) (u0 + u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := hlb (l1) (u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w6 := hlb (l1 + l2) (u1 + u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w7 := hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w8 := hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w9 := hlb (l2) (u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w10 := hlb (l2 + l3) (u2 + u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w11 := hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w12 := hlb (l3) (u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w13 := hlb (l3 + l4) (u3 + u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w14 := hlb (l4) (u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU : (0:ℝ) < 10000000000 := by norm_num
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 24896 * ((l0 : ℝ) / SC) + 42034 * ((l1 : ℝ) / SC) + 46137 * ((l2 : ℝ) / SC) + 42034 * ((l3 : ℝ) / SC) + 24896 * ((l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25326800 * ((lb top bk (l0) (u0) : ℝ) / 10000000000) + 62369200 * ((lb top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 40126500 * ((lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 99999900 * ((lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 200000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 48244400 * ((lb top bk (l1) (u1) : ℝ) / 10000000000) + 37630700 * ((lb top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 119746800 * ((lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 99999900 * ((lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 52857300 * ((lb top bk (l2) (u2) : ℝ) / 10000000000) + 37630700 * ((lb top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 40126500 * ((lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 48244400 * ((lb top bk (l3) (u3) : ℝ) / 10000000000) + 62369200 * ((lb top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 25326800 * ((lb top bk (l4) (u4) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (24896 * (l0 : ℝ) + 42034 * (l1 : ℝ) + 46137 * (l2 : ℝ) + 42034 * (l3 : ℝ) + 24896 * (l4 : ℝ)) + 32768 * (25326800 * (lb top bk (l0) (u0) : ℝ) + 62369200 * (lb top bk (l0 + l1) (u0 + u1) : ℝ) + 40126500 * (lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 99999900 * (lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 200000000 * (lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 48244400 * (lb top bk (l1) (u1) : ℝ) + 37630700 * (lb top bk (l1 + l2) (u1 + u2) : ℝ) + 119746800 * (lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 99999900 * (lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 52857300 * (lb top bk (l2) (u2) : ℝ) + 37630700 * (lb top bk (l2 + l3) (u2 + u3) : ℝ) + 40126500 * (lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 48244400 * (lb top bk (l3) (u3) : ℝ) + 62369200 * (lb top bk (l3 + l4) (u3 + u4) : ℝ) + 25326800 * (lb top bk (l4) (u4) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 116229406720000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
      + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * wfun (g0) + 62369200 * wfun (g0 + g1) + 40126500 * wfun (g0 + g1 + g2) + 99999900 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48244400 * wfun (g1) + 37630700 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 99999900 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 37630700 * wfun (g2 + g3) + 40126500 * wfun (g2 + g3 + g4) + 48244400 * wfun (g3) + 62369200 * wfun (g3 + g4) + 25326800 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25326800)]

theorem mleafOK_spec {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)
    (h : mleafOK tD bD pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    ∃ m0 m1 m2 m3 m4 : ℕ, mcore pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 m0 m1 m2 m3 m4
      (lo32 (lb2 tD bD (l0) (u0))) (hi32 (lb2 tD bD (l0) (u0))) (lo32 (lb2 tD bD (l0 + l1) (u0 + u1))) (hi32 (lb2 tD bD (l0 + l1) (u0 + u1))) (lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2))) (hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2))) (lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3))) (hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3))) (lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4))) (hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4))) (lo32 (lb2 tD bD (l1) (u1))) (hi32 (lb2 tD bD (l1) (u1))) (lo32 (lb2 tD bD (l1 + l2) (u1 + u2))) (hi32 (lb2 tD bD (l1 + l2) (u1 + u2))) (lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3))) (hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3))) (lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4))) (hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4))) (lo32 (lb2 tD bD (l2) (u2))) (hi32 (lb2 tD bD (l2) (u2))) (lo32 (lb2 tD bD (l2 + l3) (u2 + u3))) (hi32 (lb2 tD bD (l2 + l3) (u2 + u3))) (lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4))) (hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4))) (lo32 (lb2 tD bD (l3) (u3))) (hi32 (lb2 tD bD (l3) (u3))) (lo32 (lb2 tD bD (l3 + l4) (u3 + u4))) (hi32 (lb2 tD bD (l3 + l4) (u3 + u4))) (lo32 (lb2 tD bD (l4) (u4))) (hi32 (lb2 tD bD (l4) (u4))) (855669696000000000 - (25326800 * hi32 (lb2 tD bD (l0) (u0)) + 62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)))) (855644800000000000 - (24896000000000 + 25326800 * lo32 (lb2 tD bD (l0) (u0)) + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)))) (1416276834000000000 - (62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l1) (u1)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)))) (1416234800000000000 - (42034000000000 + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l1) (u1)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)))) (1456282737000000000 - (40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * hi32 (lb2 tD bD (l2) (u2)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)))) (1456236600000000000 - (46137000000000 + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * lo32 (lb2 tD bD (l2) (u2)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)))) (1416276834000000000 - (99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l3) (u3)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4)))) (1416234800000000000 - (42034000000000 + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l3) (u3)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4)))) (855669696000000000 - (200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * hi32 (lb2 tD bD (l4) (u4)))) (855644800000000000 - (24896000000000 + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * lo32 (lb2 tD bD (l4) (u4)))) = true := by
  unfold mleafOK at h
  simp only [forceB_eq] at h
  exact ⟨_, _, _, _, _, h⟩

set_option maxHeartbeats 16000000 in
theorem mleaf_sound {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (hD : LBSound2 tD bD) (hpt : PTSound pb) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)
    (h : mleafOK tD bD pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    ∀ g0 g1 g2 g3 g4 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  obtain ⟨m0, m1, m2, m3, m4, h⟩ := mleafOK_spec l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
  unfold mcore at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm01, hm02⟩, hm11⟩, hm12⟩, hm21⟩, hm22⟩, hm31⟩, hm32⟩, hm41⟩, hm42⟩, hp0⟩, hq0⟩, hp1⟩, hq1⟩, hp2⟩, hq2⟩, hp3⟩, hq3⟩, hp4⟩, hq4⟩, hp5⟩, hq5⟩, hp6⟩, hq6⟩, hp7⟩, hq7⟩, hp8⟩, hq8⟩, hp9⟩, hq9⟩, hp10⟩, hq10⟩, hp11⟩, hq11⟩, hp12⟩, hq12⟩, hp13⟩, hq13⟩, hp14⟩, hq14⟩, hmain⟩ := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  have hl0 : (l0 : ℝ) ≤ m0 := by exact_mod_cast hm01
  have hu0 : (m0 : ℝ) ≤ u0 := by exact_mod_cast hm02
  have hl1 : (l1 : ℝ) ≤ m1 := by exact_mod_cast hm11
  have hu1 : (m1 : ℝ) ≤ u1 := by exact_mod_cast hm12
  have hl2 : (l2 : ℝ) ≤ m2 := by exact_mod_cast hm21
  have hu2 : (m2 : ℝ) ≤ u2 := by exact_mod_cast hm22
  have hl3 : (l3 : ℝ) ≤ m3 := by exact_mod_cast hm31
  have hu3 : (m3 : ℝ) ≤ u3 := by exact_mod_cast hm32
  have hl4 : (l4 : ℝ) ≤ m4 := by exact_mod_cast hm41
  have hu4 : (m4 : ℝ) ≤ u4 := by exact_mod_cast hm42
  obtain ⟨d0, hd0, hdl0, hdu0⟩ := mvt_pair hD (l0) (u0) hp0 hq0
    ((m0 : ℝ) / 32768) (g0)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl0])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu0])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h01])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h02])
  have hv0 := hpt (m0)
  rw [show (((m0 : ℕ) : ℝ) / SC) = (m0 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv0
  obtain ⟨d1, hd1, hdl1, hdu1⟩ := mvt_pair hD (l0 + l1) (u0 + u1) hp1 hq1
    ((m0 : ℝ) / 32768 + (m1 : ℝ) / 32768) (g0 + g1)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl0, hl1])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu0, hu1])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h01, h11])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h02, h12])
  have hv1 := hpt (m0 + m1)
  rw [show (((m0 + m1 : ℕ) : ℝ) / SC) = (m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv1
  obtain ⟨d2, hd2, hdl2, hdu2⟩ := mvt_pair hD (l0 + l1 + l2) (u0 + u1 + u2) hp2 hq2
    ((m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768) (g0 + g1 + g2)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl0, hl1, hl2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu0, hu1, hu2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h01, h11, h21])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h02, h12, h22])
  have hv2 := hpt (m0 + m1 + m2)
  rw [show (((m0 + m1 + m2 : ℕ) : ℝ) / SC) = (m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv2
  obtain ⟨d3, hd3, hdl3, hdu3⟩ := mvt_pair hD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) hp3 hq3
    ((m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768) (g0 + g1 + g2 + g3)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl0, hl1, hl2, hl3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu0, hu1, hu2, hu3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h01, h11, h21, h31])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have hv3 := hpt (m0 + m1 + m2 + m3)
  rw [show (((m0 + m1 + m2 + m3 : ℕ) : ℝ) / SC) = (m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv3
  obtain ⟨d4, hd4, hdl4, hdu4⟩ := mvt_pair hD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) hp4 hq4
    ((m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768) (g0 + g1 + g2 + g3 + g4)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl0, hl1, hl2, hl3, hl4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu0, hu1, hu2, hu3, hu4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have hv4 := hpt (m0 + m1 + m2 + m3 + m4)
  rw [show (((m0 + m1 + m2 + m3 + m4 : ℕ) : ℝ) / SC) = (m0 : ℝ) / 32768 + (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv4
  obtain ⟨d5, hd5, hdl5, hdu5⟩ := mvt_pair hD (l1) (u1) hp5 hq5
    ((m1 : ℝ) / 32768) (g1)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl1])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu1])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h11])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h12])
  have hv5 := hpt (m1)
  rw [show (((m1 : ℕ) : ℝ) / SC) = (m1 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv5
  obtain ⟨d6, hd6, hdl6, hdu6⟩ := mvt_pair hD (l1 + l2) (u1 + u2) hp6 hq6
    ((m1 : ℝ) / 32768 + (m2 : ℝ) / 32768) (g1 + g2)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl1, hl2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu1, hu2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h11, h21])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h12, h22])
  have hv6 := hpt (m1 + m2)
  rw [show (((m1 + m2 : ℕ) : ℝ) / SC) = (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv6
  obtain ⟨d7, hd7, hdl7, hdu7⟩ := mvt_pair hD (l1 + l2 + l3) (u1 + u2 + u3) hp7 hq7
    ((m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768) (g1 + g2 + g3)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl1, hl2, hl3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu1, hu2, hu3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h11, h21, h31])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h12, h22, h32])
  have hv7 := hpt (m1 + m2 + m3)
  rw [show (((m1 + m2 + m3 : ℕ) : ℝ) / SC) = (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv7
  obtain ⟨d8, hd8, hdl8, hdu8⟩ := mvt_pair hD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) hp8 hq8
    ((m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768) (g1 + g2 + g3 + g4)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl1, hl2, hl3, hl4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu1, hu2, hu3, hu4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h11, h21, h31, h41])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have hv8 := hpt (m1 + m2 + m3 + m4)
  rw [show (((m1 + m2 + m3 + m4 : ℕ) : ℝ) / SC) = (m1 : ℝ) / 32768 + (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv8
  obtain ⟨d9, hd9, hdl9, hdu9⟩ := mvt_pair hD (l2) (u2) hp9 hq9
    ((m2 : ℝ) / 32768) (g2)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu2])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h21])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h22])
  have hv9 := hpt (m2)
  rw [show (((m2 : ℕ) : ℝ) / SC) = (m2 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv9
  obtain ⟨d10, hd10, hdl10, hdu10⟩ := mvt_pair hD (l2 + l3) (u2 + u3) hp10 hq10
    ((m2 : ℝ) / 32768 + (m3 : ℝ) / 32768) (g2 + g3)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl2, hl3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu2, hu3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h21, h31])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h22, h32])
  have hv10 := hpt (m2 + m3)
  rw [show (((m2 + m3 : ℕ) : ℝ) / SC) = (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv10
  obtain ⟨d11, hd11, hdl11, hdu11⟩ := mvt_pair hD (l2 + l3 + l4) (u2 + u3 + u4) hp11 hq11
    ((m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768) (g2 + g3 + g4)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl2, hl3, hl4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu2, hu3, hu4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h21, h31, h41])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h22, h32, h42])
  have hv11 := hpt (m2 + m3 + m4)
  rw [show (((m2 + m3 + m4 : ℕ) : ℝ) / SC) = (m2 : ℝ) / 32768 + (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv11
  obtain ⟨d12, hd12, hdl12, hdu12⟩ := mvt_pair hD (l3) (u3) hp12 hq12
    ((m3 : ℝ) / 32768) (g3)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu3])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h31])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h32])
  have hv12 := hpt (m3)
  rw [show (((m3 : ℕ) : ℝ) / SC) = (m3 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv12
  obtain ⟨d13, hd13, hdl13, hdu13⟩ := mvt_pair hD (l3 + l4) (u3 + u4) hp13 hq13
    ((m3 : ℝ) / 32768 + (m4 : ℝ) / 32768) (g3 + g4)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl3, hl4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu3, hu4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h31, h41])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h32, h42])
  have hv13 := hpt (m3 + m4)
  rw [show (((m3 + m4 : ℕ) : ℝ) / SC) = (m3 : ℝ) / 32768 + (m4 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv13
  obtain ⟨d14, hd14, hdl14, hdu14⟩ := mvt_pair hD (l4) (u4) hp14 hq14
    ((m4 : ℝ) / 32768) (g4)
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hl4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [hu4])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h41])
    (by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [h42])
  have hv14 := hpt (m4)
  rw [show (((m4 : ℕ) : ℝ) / SC) = (m4 : ℝ) / 32768 by push_cast; rw [hSCe]; (try ring)] at hv14
  have hP0 : (1000000000 : ℝ) * ((24896 : ℝ) + 25326800 * d0 + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4) ≤ ((855669696000000000 - (25326800 * hi32 (lb2 tD bD (l0) (u0)) + 62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 855669696000000000 (25326800 * hi32 (lb2 tD bD (l0) (u0)) + 62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)))
    push_cast at this
    linarith [hdu0, hdu1, hdu2, hdu3, hdu4]
  have hN0 : -((1000000000 : ℝ) * ((24896 : ℝ) + 25326800 * d0 + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4)) ≤ ((855644800000000000 - (24896000000000 + 25326800 * lo32 (lb2 tD bD (l0) (u0)) + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 855644800000000000 (24896000000000 + 25326800 * lo32 (lb2 tD bD (l0) (u0)) + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)))
    push_cast at this
    linarith [hdl0, hdl1, hdl2, hdl3, hdl4]
  have hml0 : ((m0 - l0 : ℕ) : ℝ) = (m0 : ℝ) - l0 := Nat.cast_sub hm01
  have hum0 : ((u0 - m0 : ℕ) : ℝ) = (u0 : ℝ) - m0 := Nat.cast_sub hm02
  have ht0 := mterm (e := g0 - (m0 : ℝ) / 32768) (E := ((24896 : ℝ) + 25326800 * d0 + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4)) (lo := ((m0 - l0 : ℕ) : ℝ) / 32768)
    (hi := ((u0 - m0 : ℕ) : ℝ) / 32768) (by rw [hml0]; linarith [h01]) (by rw [hum0]; linarith [h02])
    (by positivity) (by positivity) hP0 hN0 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP1 : (1000000000 : ℝ) * ((42034 : ℝ) + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 48244400 * d5 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8) ≤ ((1416276834000000000 - (62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l1) (u1)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1416276834000000000 (62369200 * hi32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l1) (u1)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)))
    push_cast at this
    linarith [hdu1, hdu2, hdu3, hdu4, hdu5, hdu6, hdu7, hdu8]
  have hN1 : -((1000000000 : ℝ) * ((42034 : ℝ) + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 48244400 * d5 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8)) ≤ ((1416234800000000000 - (42034000000000 + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l1) (u1)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1416234800000000000 (42034000000000 + 62369200 * lo32 (lb2 tD bD (l0 + l1) (u0 + u1)) + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l1) (u1)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)))
    push_cast at this
    linarith [hdl1, hdl2, hdl3, hdl4, hdl5, hdl6, hdl7, hdl8]
  have hml1 : ((m1 - l1 : ℕ) : ℝ) = (m1 : ℝ) - l1 := Nat.cast_sub hm11
  have hum1 : ((u1 - m1 : ℕ) : ℝ) = (u1 : ℝ) - m1 := Nat.cast_sub hm12
  have ht1 := mterm (e := g1 - (m1 : ℝ) / 32768) (E := ((42034 : ℝ) + 62369200 * d1 + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 48244400 * d5 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8)) (lo := ((m1 - l1 : ℕ) : ℝ) / 32768)
    (hi := ((u1 - m1 : ℕ) : ℝ) / 32768) (by rw [hml1]; linarith [h11]) (by rw [hum1]; linarith [h12])
    (by positivity) (by positivity) hP1 hN1 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP2 : (1000000000 : ℝ) * ((46137 : ℝ) + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8 + 52857300 * d9 + 37630700 * d10 + 40126500 * d11) ≤ ((1456282737000000000 - (40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * hi32 (lb2 tD bD (l2) (u2)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1456282737000000000 (40126500 * hi32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * hi32 (lb2 tD bD (l2) (u2)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)))
    push_cast at this
    linarith [hdu2, hdu3, hdu4, hdu6, hdu7, hdu8, hdu9, hdu10, hdu11]
  have hN2 : -((1000000000 : ℝ) * ((46137 : ℝ) + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8 + 52857300 * d9 + 37630700 * d10 + 40126500 * d11)) ≤ ((1456236600000000000 - (46137000000000 + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * lo32 (lb2 tD bD (l2) (u2)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1456236600000000000 (46137000000000 + 40126500 * lo32 (lb2 tD bD (l0 + l1 + l2) (u0 + u1 + u2)) + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l1 + l2) (u1 + u2)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 52857300 * lo32 (lb2 tD bD (l2) (u2)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)))
    push_cast at this
    linarith [hdl2, hdl3, hdl4, hdl6, hdl7, hdl8, hdl9, hdl10, hdl11]
  have hml2 : ((m2 - l2 : ℕ) : ℝ) = (m2 : ℝ) - l2 := Nat.cast_sub hm21
  have hum2 : ((u2 - m2 : ℕ) : ℝ) = (u2 : ℝ) - m2 := Nat.cast_sub hm22
  have ht2 := mterm (e := g2 - (m2 : ℝ) / 32768) (E := ((46137 : ℝ) + 40126500 * d2 + 99999900 * d3 + 200000000 * d4 + 37630700 * d6 + 119746800 * d7 + 99999900 * d8 + 52857300 * d9 + 37630700 * d10 + 40126500 * d11)) (lo := ((m2 - l2 : ℕ) : ℝ) / 32768)
    (hi := ((u2 - m2 : ℕ) : ℝ) / 32768) (by rw [hml2]; linarith [h21]) (by rw [hum2]; linarith [h22])
    (by positivity) (by positivity) hP2 hN2 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP3 : (1000000000 : ℝ) * ((42034 : ℝ) + 99999900 * d3 + 200000000 * d4 + 119746800 * d7 + 99999900 * d8 + 37630700 * d10 + 40126500 * d11 + 48244400 * d12 + 62369200 * d13) ≤ ((1416276834000000000 - (99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l3) (u3)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1416276834000000000 (99999900 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * hi32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * hi32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * hi32 (lb2 tD bD (l3) (u3)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4)))
    push_cast at this
    linarith [hdu3, hdu4, hdu7, hdu8, hdu10, hdu11, hdu12, hdu13]
  have hN3 : -((1000000000 : ℝ) * ((42034 : ℝ) + 99999900 * d3 + 200000000 * d4 + 119746800 * d7 + 99999900 * d8 + 37630700 * d10 + 40126500 * d11 + 48244400 * d12 + 62369200 * d13)) ≤ ((1416234800000000000 - (42034000000000 + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l3) (u3)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4))) : ℕ) : ℝ) := by
    have := natsub_ge 1416234800000000000 (42034000000000 + 99999900 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3)) + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 119746800 * lo32 (lb2 tD bD (l1 + l2 + l3) (u1 + u2 + u3)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 37630700 * lo32 (lb2 tD bD (l2 + l3) (u2 + u3)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 48244400 * lo32 (lb2 tD bD (l3) (u3)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4)))
    push_cast at this
    linarith [hdl3, hdl4, hdl7, hdl8, hdl10, hdl11, hdl12, hdl13]
  have hml3 : ((m3 - l3 : ℕ) : ℝ) = (m3 : ℝ) - l3 := Nat.cast_sub hm31
  have hum3 : ((u3 - m3 : ℕ) : ℝ) = (u3 : ℝ) - m3 := Nat.cast_sub hm32
  have ht3 := mterm (e := g3 - (m3 : ℝ) / 32768) (E := ((42034 : ℝ) + 99999900 * d3 + 200000000 * d4 + 119746800 * d7 + 99999900 * d8 + 37630700 * d10 + 40126500 * d11 + 48244400 * d12 + 62369200 * d13)) (lo := ((m3 - l3 : ℕ) : ℝ) / 32768)
    (hi := ((u3 - m3 : ℕ) : ℝ) / 32768) (by rw [hml3]; linarith [h31]) (by rw [hum3]; linarith [h32])
    (by positivity) (by positivity) hP3 hN3 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP4 : (1000000000 : ℝ) * ((24896 : ℝ) + 200000000 * d4 + 99999900 * d8 + 40126500 * d11 + 62369200 * d13 + 25326800 * d14) ≤ ((855669696000000000 - (200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * hi32 (lb2 tD bD (l4) (u4))) : ℕ) : ℝ) := by
    have := natsub_ge 855669696000000000 (200000000 * hi32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * hi32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * hi32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * hi32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * hi32 (lb2 tD bD (l4) (u4)))
    push_cast at this
    linarith [hdu4, hdu8, hdu11, hdu13, hdu14]
  have hN4 : -((1000000000 : ℝ) * ((24896 : ℝ) + 200000000 * d4 + 99999900 * d8 + 40126500 * d11 + 62369200 * d13 + 25326800 * d14)) ≤ ((855644800000000000 - (24896000000000 + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * lo32 (lb2 tD bD (l4) (u4))) : ℕ) : ℝ) := by
    have := natsub_ge 855644800000000000 (24896000000000 + 200000000 * lo32 (lb2 tD bD (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4)) + 99999900 * lo32 (lb2 tD bD (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4)) + 40126500 * lo32 (lb2 tD bD (l2 + l3 + l4) (u2 + u3 + u4)) + 62369200 * lo32 (lb2 tD bD (l3 + l4) (u3 + u4)) + 25326800 * lo32 (lb2 tD bD (l4) (u4)))
    push_cast at this
    linarith [hdl4, hdl8, hdl11, hdl13, hdl14]
  have hml4 : ((m4 - l4 : ℕ) : ℝ) = (m4 : ℝ) - l4 := Nat.cast_sub hm41
  have hum4 : ((u4 - m4 : ℕ) : ℝ) = (u4 : ℝ) - m4 := Nat.cast_sub hm42
  have ht4 := mterm (e := g4 - (m4 : ℝ) / 32768) (E := ((24896 : ℝ) + 200000000 * d4 + 99999900 * d8 + 40126500 * d11 + 62369200 * d13 + 25326800 * d14)) (lo := ((m4 - l4 : ℕ) : ℝ) / 32768)
    (hi := ((u4 - m4 : ℕ) : ℝ) / 32768) (by rw [hml4]; linarith [h41]) (by rw [hum4]; linarith [h42])
    (by positivity) (by positivity) hP4 hN4 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [hml0, hml1, hml2, hml3, hml4, hum0, hum1, hum2, hum3, hum4] at hq
  simp only [hml0, hml1, hml2, hml3, hml4, hum0, hum1, hum2, hum3, hum4] at ht0 ht1 ht2 ht3 ht4
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
      + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * wfun (g0) + 62369200 * wfun (g0 + g1) + 40126500 * wfun (g0 + g1 + g2) + 99999900 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48244400 * wfun (g1) + 37630700 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 99999900 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 37630700 * wfun (g2 + g3) + 40126500 * wfun (g2 + g3 + g4) + 48244400 * wfun (g3) + 62369200 * wfun (g3 + g4) + 25326800 * wfun (g4) := by
    field_simp; try ring
  rw [eG, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14]
  have hcN : ((cN : ℕ) : ℝ) = 354704 := by norm_num [cN]
  rw [hcN]
  linarith [hq, ht0, ht1, ht2, ht3, ht4, mul_le_mul_of_nonneg_left hv0 (by norm_num : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left hv1 (by norm_num : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left hv2 (by norm_num : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left hv3 (by norm_num : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left hv4 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hv5 (by norm_num : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left hv6 (by norm_num : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left hv7 (by norm_num : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left hv8 (by norm_num : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left hv9 (by norm_num : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left hv10 (by norm_num : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left hv11 (by norm_num : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left hv12 (by norm_num : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left hv13 (by norm_num : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left hv14 (by norm_num : (0:ℝ) ≤ 25326800)]

/-- a box split on gap 0 at `q` is covered when both halves are -/
theorem covered_split0 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 q l1 u1 l2 u2 l3 u3 l4 u4) (hB : Covered q u0 l1 u1 l2 u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g0 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 hq h11 h12 h21 h22 h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 hq h02 h11 h12 h21 h22 h31 h32 h41 h42

/-- a box split on gap 1 at `q` is covered when both halves are -/
theorem covered_split1 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 q l2 u2 l3 u3 l4 u4) (hB : Covered l0 u0 q u1 l2 u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g1 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 hq h21 h22 h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 hq h12 h21 h22 h31 h32 h41 h42

/-- a box split on gap 2 at `q` is covered when both halves are -/
theorem covered_split2 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 q l3 u3 l4 u4) (hB : Covered l0 u0 l1 u1 q u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g2 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 hq h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 hq h22 h31 h32 h41 h42

/-- a box split on gap 3 at `q` is covered when both halves are -/
theorem covered_split3 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 q l4 u4) (hB : Covered l0 u0 l1 u1 l2 u2 q u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g3 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 hq h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 hq h32 h41 h42

/-- a box split on gap 4 at `q` is covered when both halves are -/
theorem covered_split4 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 q) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 q u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g4 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 hq
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 hq h42

/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ, f pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0 → Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4

theorem split0_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split0 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4) (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split0 _ hA (hih _ (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split1_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split1 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4) l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split1 _ hA (hih _ l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split2_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split2 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4) l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split2 _ hA (hih _ l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split3_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split3 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4) l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split3 _ hA (hih _ l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split4_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split4 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1)) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1)) l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split4 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 h')
  · exact absurd (by simp only [hp]) h

theorem splitAx_sound {ih : WF} (hih : WalkOK ih) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : splitAx ih pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold splitAx at h
  cases ha0 : Nat.beq ax 0
  · rw [ha0] at h
    cases ha1 : Nat.beq ax 1
    · rw [ha1] at h
      cases ha2 : Nat.beq ax 2
      · rw [ha2] at h
        cases ha3 : Nat.beq ax 3
        · rw [ha3] at h
          exact split4_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
        · rw [ha3] at h; exact split3_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
      · rw [ha2] at h; exact split2_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    · rw [ha1] at h; exact split1_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
  · rw [ha0] at h; exact split0_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hD : LBSound2 tD bD) (hpt : PTSound pb) (pos fl l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafStep top bk tD bD pb pos fl l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold leafStep at h
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  cases hs : Nat.ble (Nat.add u4 1) l0
  · rw [hs] at h
    cases hf : Nat.beq fl 1
    · rw [hf] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
      · rw [hl] at h; exact absurd rfl h
      · exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 hl g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42)
    · rw [hf] at h
      cases hl : mleafOK tD bD pb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
      · rw [hl] at h; exact absurd rfl h
      · exact Or.inl (mleaf_sound hD hpt l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 hl g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42)
  · right
    have hsk : u4 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u4 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hD : LBSound2 tD bD) (hpt : PTSound pb) (bits : ℕ) : ∀ fuel, WalkOK (walk top bk tD bD pb bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb pos (Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (splitAx (walk top bk tD bD pb bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hD : LBSound2 tD bD) (hpt : PTSound pb) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 e : ℕ)
    (h : walk top bk tD bD pb bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 :=
  walk_sound hlb hD hpt bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (h ▸ he)

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
theorem of_check (cover0 cover1 cover2 cover3 cover4 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 : ℕ)
    (hS0 : cN * SC ≤ 24896 * S0) (hS1 : cN * SC ≤ 42034 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42034 * S3) (hS4 : cN * SC ≤ 24896 * S4)
    (hcov0 : coverCheck 25326800 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 48244400 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 52857300 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 48244400 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 25326800 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25326800)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (46137 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (52857300 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (24896 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (42034 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (46137 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (42034 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (24896 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25326800 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (62369200 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (48244400 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (37630700 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (52857300 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (37630700 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (48244400 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (62369200 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (25326800 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g0 * SA = 24896 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 24896 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g0 * SA = 25326800 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
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
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g1 * SA = 42034 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 42034 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g1 * SA = 48244400 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW5, hLin0]
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW5, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (46137 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (46137 / (SA:ℝ)) * g2 * SA = 46137 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 46137 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 46137 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 46137 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (52857300 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (52857300 / (SA:ℝ)) * wfun g2 * SA = 52857300 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 52857300)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW9, hLin0]
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW9, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g3 * SA = 42034 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 42034 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g3 * SA = 48244400 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW12, hLin0]
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW12, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g4 * SA = 24896 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 24896 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g4 * SA = 25326800 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW14, hLin0]
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  exact hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4 g0 g1 g2 g3 g4 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42'

end Zeta23Ext.Bridge.ThreePoint.MvtT

end
