import AMW.CWindow
import AMW.CMinX

/-! ###### the AM 7-point weighted certificate `AT7`: zero-order and minorant leaf tests, walk, cover

Weights: LP pair weights and pressures over SA = 10⁸ for the window of `AMW.Window`.  Pyramid lower-bound table adapted
from five-point-pyramid-2 by typh (Apache-2.0); per-term minorant leaves after mvt-engine's MinCore. ###### -/

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.AT7

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

def SA : ℕ := 100000000
def cN : ℕ := 787380

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  (41468 / (SA:ℝ)) * g0 + (70344 / (SA:ℝ)) * g1 + (87381 / (SA:ℝ)) * g2 + (87381 / (SA:ℝ)) * g3 + (70344 / (SA:ℝ)) * g4 + (41468 / (SA:ℝ)) * g5
    + (21269442 / (SA:ℝ)) * wfun (g0) + (890898 / (SA:ℝ)) * wfun (g0 + g1) + (28398464 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (75539688 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g1) + (65972058 / (SA:ℝ)) * wfun (g1 + g2) + (71601535 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (48920622 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g2) + (66274085 / (SA:ℝ)) * wfun (g2 + g3) + (71601535 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (75539688 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g3) + (65972058 / (SA:ℝ)) * wfun (g3 + g4) + (28398464 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g4) + (890898 / (SA:ℝ)) * wfun (g4 + g5) + (21269442 / (SA:ℝ)) * wfun (g5)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb3_t` (U = 10¹⁰; three-piece pyramid reads), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 41468 l0) (Nat.mul 70344 l1)) (Nat.mul 87381 l2)) (Nat.mul 87381 l3)) (Nat.mul 70344 l4)) (Nat.mul 41468 l5)) 10000000000
  ee 258008678400000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 696957075456 (lb3 top bk l0 u0))
  ee 258008678400000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1176260509696 (lb3 top bk l1 u1))
  ee 258008678400000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1176260509696 (lb3 top bk l4 u4))
  ee 258008678400000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 696957075456 (lb3 top bk l5 u5))
  ee 258008678400000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 1403582382080 (lb3 top bk l2 u2))
  ee 258008678400000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 1403582382080 (lb3 top bk l3 u3))
  ee 258008678400000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 2171669217280 (lb3 top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 258008678400000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 2161772396544 (lb3 top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 258008678400000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 2161772396544 (lb3 top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 258008678400000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 2346239098880 (lb3 top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 258008678400000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 2346239098880 (lb3 top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 258008678400000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 930560868352 (lb3 top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 258008678400000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 930560868352 (lb3 top bk (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)))
  ee 258008678400000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 2475284496384 (lb3 top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 258008678400000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 2475284496384 (lb3 top bk (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)))
  ee 258008678400000000000 s15 (
  let s16 := Nat.add s15 (Nat.mul 1603030941696 (lb3 top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 258008678400000000000 s16 (
  let s17 := Nat.add s16 (Nat.mul 3276799967232 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 258008678400000000000 s17 (
  let s18 := Nat.add s17 (Nat.mul 3276799967232 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)))
  ee 258008678400000000000 s18 (
  let s19 := Nat.add s18 (Nat.mul 29192945664 (lb3 top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 258008678400000000000 s19 (
  let s20 := Nat.add s19 (Nat.mul 6553600000000 (lb3 top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)))
  ee 258008678400000000000 s20 (
  let s21 := Nat.add s20 (Nat.mul 29192945664 (lb3 top bk (Nat.add l4 l5) (Nat.add u4 u5)))
  Nat.ble 258008678400000000000 s21)))))))))))))))))))))


/-- the grid point `j ∈ [0, 8]` of the range `[L, U]`: `L + (U − L) j / 8` rounded down to a multiple of `2^4`, clamped
to the multiples of `2^4` inside `[L, U]` -/
def gptG (L U j : ℕ) : ℕ :=
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L 15) 4) 4) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U 4) 4) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) 4) 4) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the grid point of the 5-bit field `jj`: `gptG` with `j = jj mod 16` on the grid of multiples of `2^4` when bit 4 is
set, else of `2^8` -/
def gptF (L U jj : ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ) 8 4 (Nat.beq (Nat.shiftRight jj 4) 1)) fun s =>
  forceR (Nat.land jj 15) fun j =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 s) 1)) s) s) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U s) s) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) s) s) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the minorant inequality of a box, given per term its kind `k`, weight `m` and grid points `p`, `r`:
`1024 cN SC U + RU (Σ a mcn + Σ_r (u − l) N_r) ≤ 1024 U Σ b l + SC Σ a mval + RU Σ a mcp` -/
def mscheck (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k2 m2 p2 r2 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) : Bool :=
  (((((((((((((((((((((((((((((((((((((((((((((((Nat.ble l0 u0 && Nat.ble l1 u1) && Nat.ble l2 u2) && Nat.ble l3 u3) && Nat.ble l4 u4) && Nat.ble l5 u5) && Nat.ble m0 1024) && mok R tD bD f l0 u0 (mw1 k0 m0) (mw2 k0 m0) p0 r0) && Nat.ble m1 1024) && mok R tD bD f (Nat.add l0 l1) (Nat.add u0 u1) (mw1 k1 m1) (mw2 k1 m1) p1 r1) && Nat.ble m2 1024) && mok R tD bD f (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (mw1 k2 m2) (mw2 k2 m2) p2 r2) && Nat.ble m3 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mw1 k3 m3) (mw2 k3 m3) p3 r3) && Nat.ble m4 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mw1 k4 m4) (mw2 k4 m4) p4 r4) && Nat.ble m5 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mw1 k5 m5) (mw2 k5 m5) p5 r5) && Nat.ble m6 1024) && mok R tD bD f l1 u1 (mw1 k6 m6) (mw2 k6 m6) p6 r6) && Nat.ble m7 1024) && mok R tD bD f (Nat.add l1 l2) (Nat.add u1 u2) (mw1 k7 m7) (mw2 k7 m7) p7 r7) && Nat.ble m8 1024) && mok R tD bD f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mw1 k8 m8) (mw2 k8 m8) p8 r8) && Nat.ble m9 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mw1 k9 m9) (mw2 k9 m9) p9 r9) && Nat.ble m10 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mw1 k10 m10) (mw2 k10 m10) p10 r10) && Nat.ble m11 1024) && mok R tD bD f l2 u2 (mw1 k11 m11) (mw2 k11 m11) p11 r11) && Nat.ble m12 1024) && mok R tD bD f (Nat.add l2 l3) (Nat.add u2 u3) (mw1 k12 m12) (mw2 k12 m12) p12 r12) && Nat.ble m13 1024) && mok R tD bD f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mw1 k13 m13) (mw2 k13 m13) p13 r13) && Nat.ble m14 1024) && mok R tD bD f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mw1 k14 m14) (mw2 k14 m14) p14 r14) && Nat.ble m15 1024) && mok R tD bD f l3 u3 (mw1 k15 m15) (mw2 k15 m15) p15 r15) && Nat.ble m16 1024) && mok R tD bD f (Nat.add l3 l4) (Nat.add u3 u4) (mw1 k16 m16) (mw2 k16 m16) p16 r16) && Nat.ble m17 1024) && mok R tD bD f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mw1 k17 m17) (mw2 k17 m17) p17 r17) && Nat.ble m18 1024) && mok R tD bD f l4 u4 (mw1 k18 m18) (mw2 k18 m18) p18 r18) && Nat.ble m19 1024) && mok R tD bD f (Nat.add l4 l5) (Nat.add u4 u5) (mw1 k19 m19) (mw2 k19 m19) p19 r19) && Nat.ble m20 1024) && mok R tD bD f l5 u5 (mw1 k20 m20) (mw2 k20 m20) p20 r20) && Nat.ble (Nat.add 264200886681600000000000 (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 21269442 (mcn f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 890898 (mcn f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 28398464 (mcn f (Nat.add (Nat.add l0 l1) l2) (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (mcn f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 35896622 (mcn f l1 (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 65972058 (mcn f (Nat.add l1 l2) (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 71601535 (mcn f (Nat.add (Nat.add l1 l2) l3) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (mcn f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (mcn f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 42833935 (mcn f l2 (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 66274085 (mcn f (Nat.add l2 l3) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 71601535 (mcn f (Nat.add (Nat.add l2 l3) l4) (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (mcn f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 42833935 (mcn f l3 (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 65972058 (mcn f (Nat.add l3 l4) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 28398464 (mcn f (Nat.add (Nat.add l3 l4) l5) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 35896622 (mcn f l4 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 890898 (mcn f (Nat.add l4 l5) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 21269442 (mcn f l5 (mw1 k20 m20) (mw2 k20 m20) p20 r20))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.sub u0 l0) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 21269442 (Nat.add (mw1 k0 m0) (mw2 k0 m0))) (Nat.mul 890898 (Nat.add (mw1 k1 m1) (mw2 k1 m1)))) (Nat.mul 28398464 (Nat.add (mw1 k2 m2) (mw2 k2 m2)))) (Nat.mul 75539688 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 99999999 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 42463232000000000 (Nat.mul 21269442 (msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0))) (Nat.mul 890898 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 28398464 (msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))))) (Nat.mul (Nat.sub u1 l1) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 890898 (Nat.add (mw1 k1 m1) (mw2 k1 m1))) (Nat.mul 28398464 (Nat.add (mw1 k2 m2) (mw2 k2 m2)))) (Nat.mul 75539688 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 99999999 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 35896622 (Nat.add (mw1 k6 m6) (mw2 k6 m6)))) (Nat.mul 65972058 (Nat.add (mw1 k7 m7) (mw2 k7 m7)))) (Nat.mul 71601535 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 48920622 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 99999999 (Nat.add (mw1 k10 m10) (mw2 k10 m10))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 72032256000000000 (Nat.mul 890898 (msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 28398464 (msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 35896622 (msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 65972058 (msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 71601535 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10)))))) (Nat.mul (Nat.sub u2 l2) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 28398464 (Nat.add (mw1 k2 m2) (mw2 k2 m2))) (Nat.mul 75539688 (Nat.add (mw1 k3 m3) (mw2 k3 m3)))) (Nat.mul 99999999 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 65972058 (Nat.add (mw1 k7 m7) (mw2 k7 m7)))) (Nat.mul 71601535 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 48920622 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 99999999 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 42833935 (Nat.add (mw1 k11 m11) (mw2 k11 m11)))) (Nat.mul 66274085 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 71601535 (Nat.add (mw1 k13 m13) (mw2 k13 m13)))) (Nat.mul 75539688 (Nat.add (mw1 k14 m14) (mw2 k14 m14))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 89478144000000000 (Nat.mul 28398464 (msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 65972058 (msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 71601535 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 42833935 (msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 66274085 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 71601535 (msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14)))))) (Nat.mul (Nat.sub u3 l3) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 75539688 (Nat.add (mw1 k3 m3) (mw2 k3 m3))) (Nat.mul 99999999 (Nat.add (mw1 k4 m4) (mw2 k4 m4)))) (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 71601535 (Nat.add (mw1 k8 m8) (mw2 k8 m8)))) (Nat.mul 48920622 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 99999999 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 66274085 (Nat.add (mw1 k12 m12) (mw2 k12 m12)))) (Nat.mul 71601535 (Nat.add (mw1 k13 m13) (mw2 k13 m13)))) (Nat.mul 75539688 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 42833935 (Nat.add (mw1 k15 m15) (mw2 k15 m15)))) (Nat.mul 65972058 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 28398464 (Nat.add (mw1 k17 m17) (mw2 k17 m17))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 89478144000000000 (Nat.mul 75539688 (msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 71601535 (msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 66274085 (msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 71601535 (msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 42833935 (msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 65972058 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 28398464 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)))))) (Nat.mul (Nat.sub u4 l4) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 99999999 (Nat.add (mw1 k4 m4) (mw2 k4 m4))) (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5)))) (Nat.mul 48920622 (Nat.add (mw1 k9 m9) (mw2 k9 m9)))) (Nat.mul 99999999 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 71601535 (Nat.add (mw1 k13 m13) (mw2 k13 m13)))) (Nat.mul 75539688 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 65972058 (Nat.add (mw1 k16 m16) (mw2 k16 m16)))) (Nat.mul 28398464 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 35896622 (Nat.add (mw1 k18 m18) (mw2 k18 m18)))) (Nat.mul 890898 (Nat.add (mw1 k19 m19) (mw2 k19 m19))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 72032256000000000 (Nat.mul 99999999 (msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 48920622 (msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 71601535 (msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 65972058 (msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 28398464 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 35896622 (msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 890898 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19)))))) (Nat.mul (Nat.sub u5 l5) (Nat.sub (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 200000000 (Nat.add (mw1 k5 m5) (mw2 k5 m5))) (Nat.mul 99999999 (Nat.add (mw1 k10 m10) (mw2 k10 m10)))) (Nat.mul 75539688 (Nat.add (mw1 k14 m14) (mw2 k14 m14)))) (Nat.mul 28398464 (Nat.add (mw1 k17 m17) (mw2 k17 m17)))) (Nat.mul 890898 (Nat.add (mw1 k19 m19) (mw2 k19 m19)))) (Nat.mul 21269442 (Nat.add (mw1 k20 m20) (mw2 k20 m20))))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 42463232000000000 (Nat.mul 200000000 (msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 99999999 (msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 75539688 (msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 28398464 (msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 890898 (msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 21269442 (msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20))))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 41468 l0) (Nat.mul 70344 l1)) (Nat.mul 87381 l2)) (Nat.mul 87381 l3)) (Nat.mul 70344 l4)) (Nat.mul 41468 l5))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 21269442 (mval top bk f l0 u0 (mwc k0 m0) (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 890898 (mval top bk f (Nat.add l0 l1) (Nat.add u0 u1) (mwc k1 m1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 28398464 (mval top bk f (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (mwc k2 m2) (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (mval top bk f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (mwc k3 m3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (mwc k4 m4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (mwc k5 m5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 35896622 (mval top bk f l1 u1 (mwc k6 m6) (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 65972058 (mval top bk f (Nat.add l1 l2) (Nat.add u1 u2) (mwc k7 m7) (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 71601535 (mval top bk f (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (mwc k8 m8) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (mval top bk f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (mwc k9 m9) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (mval top bk f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (mwc k10 m10) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 42833935 (mval top bk f l2 u2 (mwc k11 m11) (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 66274085 (mval top bk f (Nat.add l2 l3) (Nat.add u2 u3) (mwc k12 m12) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 71601535 (mval top bk f (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (mwc k13 m13) (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (mval top bk f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (mwc k14 m14) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 42833935 (mval top bk f l3 u3 (mwc k15 m15) (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 65972058 (mval top bk f (Nat.add l3 l4) (Nat.add u3 u4) (mwc k16 m16) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 28398464 (mval top bk f (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (mwc k17 m17) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 35896622 (mval top bk f l4 u4 (mwc k18 m18) (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 890898 (mval top bk f (Nat.add l4 l5) (Nat.add u4 u5) (mwc k19 m19) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 21269442 (mval top bk f l5 u5 (mwc k20 m20) (mw1 k20 m20) (mw2 k20 m20) p20 r20))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 21269442 (mcp f l0 (mw1 k0 m0) (mw2 k0 m0) p0 r0)) (Nat.mul 890898 (mcp f (Nat.add l0 l1) (mw1 k1 m1) (mw2 k1 m1) p1 r1))) (Nat.mul 28398464 (mcp f (Nat.add (Nat.add l0 l1) l2) (mw1 k2 m2) (mw2 k2 m2) p2 r2))) (Nat.mul 75539688 (mcp f (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (mw1 k3 m3) (mw2 k3 m3) p3 r3))) (Nat.mul 99999999 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (mw1 k4 m4) (mw2 k4 m4) p4 r4))) (Nat.mul 200000000 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (mw1 k5 m5) (mw2 k5 m5) p5 r5))) (Nat.mul 35896622 (mcp f l1 (mw1 k6 m6) (mw2 k6 m6) p6 r6))) (Nat.mul 65972058 (mcp f (Nat.add l1 l2) (mw1 k7 m7) (mw2 k7 m7) p7 r7))) (Nat.mul 71601535 (mcp f (Nat.add (Nat.add l1 l2) l3) (mw1 k8 m8) (mw2 k8 m8) p8 r8))) (Nat.mul 48920622 (mcp f (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (mw1 k9 m9) (mw2 k9 m9) p9 r9))) (Nat.mul 99999999 (mcp f (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (mw1 k10 m10) (mw2 k10 m10) p10 r10))) (Nat.mul 42833935 (mcp f l2 (mw1 k11 m11) (mw2 k11 m11) p11 r11))) (Nat.mul 66274085 (mcp f (Nat.add l2 l3) (mw1 k12 m12) (mw2 k12 m12) p12 r12))) (Nat.mul 71601535 (mcp f (Nat.add (Nat.add l2 l3) l4) (mw1 k13 m13) (mw2 k13 m13) p13 r13))) (Nat.mul 75539688 (mcp f (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (mw1 k14 m14) (mw2 k14 m14) p14 r14))) (Nat.mul 42833935 (mcp f l3 (mw1 k15 m15) (mw2 k15 m15) p15 r15))) (Nat.mul 65972058 (mcp f (Nat.add l3 l4) (mw1 k16 m16) (mw2 k16 m16) p16 r16))) (Nat.mul 28398464 (mcp f (Nat.add (Nat.add l3 l4) l5) (mw1 k17 m17) (mw2 k17 m17) p17 r17))) (Nat.mul 35896622 (mcp f l4 (mw1 k18 m18) (mw2 k18 m18) p18 r18))) (Nat.mul 890898 (mcp f (Nat.add l4 l5) (mw1 k19 m19) (mw2 k19 m19) p19 r19))) (Nat.mul 21269442 (mcp f l5 (mw1 k20 m20) (mw2 k20 m20) p20 r20)))))

/-- the payload length of a minorant term of kind `k` -/
def mlen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 22 (Nat.beq k 3)) 17 (Nat.beq k 2)) 7 (Nat.beq k 1)

/-- a minorant leaf: the payload length when the check passes, else `0` -/
def mleafN (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  forceR 0 fun o0 =>
  forceR (Nat.land (Nat.shiftRight w o0) 3) fun k0 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o0 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o0 7)) 1023) (Nat.beq k0 2)) fun m0 =>
  forceR (gptF l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 2)) 31)) fun p0 =>
  forceR (gptF l0 u0 (Nat.land (Nat.shiftRight w (Nat.add o0 7)) 31)) fun r0 =>
  forceR (Nat.add o0 (mlen k0)) fun o1 =>
  forceR (Nat.land (Nat.shiftRight w o1) 3) fun k1 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o1 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o1 7)) 1023) (Nat.beq k1 2)) fun m1 =>
  forceR (gptF (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 2)) 31)) fun p1 =>
  forceR (gptF (Nat.add l0 l1) (Nat.add u0 u1) (Nat.land (Nat.shiftRight w (Nat.add o1 7)) 31)) fun r1 =>
  forceR (Nat.add o1 (mlen k1)) fun o2 =>
  forceR (Nat.land (Nat.shiftRight w o2) 3) fun k2 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o2 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o2 7)) 1023) (Nat.beq k2 2)) fun m2 =>
  forceR (gptF (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.land (Nat.shiftRight w (Nat.add o2 2)) 31)) fun p2 =>
  forceR (gptF (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.land (Nat.shiftRight w (Nat.add o2 7)) 31)) fun r2 =>
  forceR (Nat.add o2 (mlen k2)) fun o3 =>
  forceR (Nat.land (Nat.shiftRight w o3) 3) fun k3 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o3 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o3 7)) 1023) (Nat.beq k3 2)) fun m3 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o3 2)) 31)) fun p3 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o3 7)) 31)) fun r3 =>
  forceR (Nat.add o3 (mlen k3)) fun o4 =>
  forceR (Nat.land (Nat.shiftRight w o4) 3) fun k4 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o4 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o4 7)) 1023) (Nat.beq k4 2)) fun m4 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o4 2)) 31)) fun p4 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o4 7)) 31)) fun r4 =>
  forceR (Nat.add o4 (mlen k4)) fun o5 =>
  forceR (Nat.land (Nat.shiftRight w o5) 3) fun k5 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o5 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o5 7)) 1023) (Nat.beq k5 2)) fun m5 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o5 2)) 31)) fun p5 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o5 7)) 31)) fun r5 =>
  forceR (Nat.add o5 (mlen k5)) fun o6 =>
  forceR (Nat.land (Nat.shiftRight w o6) 3) fun k6 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o6 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o6 7)) 1023) (Nat.beq k6 2)) fun m6 =>
  forceR (gptF l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 2)) 31)) fun p6 =>
  forceR (gptF l1 u1 (Nat.land (Nat.shiftRight w (Nat.add o6 7)) 31)) fun r6 =>
  forceR (Nat.add o6 (mlen k6)) fun o7 =>
  forceR (Nat.land (Nat.shiftRight w o7) 3) fun k7 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o7 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o7 7)) 1023) (Nat.beq k7 2)) fun m7 =>
  forceR (gptF (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 2)) 31)) fun p7 =>
  forceR (gptF (Nat.add l1 l2) (Nat.add u1 u2) (Nat.land (Nat.shiftRight w (Nat.add o7 7)) 31)) fun r7 =>
  forceR (Nat.add o7 (mlen k7)) fun o8 =>
  forceR (Nat.land (Nat.shiftRight w o8) 3) fun k8 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o8 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o8 7)) 1023) (Nat.beq k8 2)) fun m8 =>
  forceR (gptF (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 2)) 31)) fun p8 =>
  forceR (gptF (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.land (Nat.shiftRight w (Nat.add o8 7)) 31)) fun r8 =>
  forceR (Nat.add o8 (mlen k8)) fun o9 =>
  forceR (Nat.land (Nat.shiftRight w o9) 3) fun k9 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o9 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o9 7)) 1023) (Nat.beq k9 2)) fun m9 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 2)) 31)) fun p9 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o9 7)) 31)) fun r9 =>
  forceR (Nat.add o9 (mlen k9)) fun o10 =>
  forceR (Nat.land (Nat.shiftRight w o10) 3) fun k10 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o10 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o10 7)) 1023) (Nat.beq k10 2)) fun m10 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 2)) 31)) fun p10 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o10 7)) 31)) fun r10 =>
  forceR (Nat.add o10 (mlen k10)) fun o11 =>
  forceR (Nat.land (Nat.shiftRight w o11) 3) fun k11 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o11 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o11 7)) 1023) (Nat.beq k11 2)) fun m11 =>
  forceR (gptF l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o11 2)) 31)) fun p11 =>
  forceR (gptF l2 u2 (Nat.land (Nat.shiftRight w (Nat.add o11 7)) 31)) fun r11 =>
  forceR (Nat.add o11 (mlen k11)) fun o12 =>
  forceR (Nat.land (Nat.shiftRight w o12) 3) fun k12 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o12 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o12 7)) 1023) (Nat.beq k12 2)) fun m12 =>
  forceR (gptF (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o12 2)) 31)) fun p12 =>
  forceR (gptF (Nat.add l2 l3) (Nat.add u2 u3) (Nat.land (Nat.shiftRight w (Nat.add o12 7)) 31)) fun r12 =>
  forceR (Nat.add o12 (mlen k12)) fun o13 =>
  forceR (Nat.land (Nat.shiftRight w o13) 3) fun k13 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o13 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o13 7)) 1023) (Nat.beq k13 2)) fun m13 =>
  forceR (gptF (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o13 2)) 31)) fun p13 =>
  forceR (gptF (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.land (Nat.shiftRight w (Nat.add o13 7)) 31)) fun r13 =>
  forceR (Nat.add o13 (mlen k13)) fun o14 =>
  forceR (Nat.land (Nat.shiftRight w o14) 3) fun k14 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o14 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o14 7)) 1023) (Nat.beq k14 2)) fun m14 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o14 2)) 31)) fun p14 =>
  forceR (gptF (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o14 7)) 31)) fun r14 =>
  forceR (Nat.add o14 (mlen k14)) fun o15 =>
  forceR (Nat.land (Nat.shiftRight w o15) 3) fun k15 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o15 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o15 7)) 1023) (Nat.beq k15 2)) fun m15 =>
  forceR (gptF l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o15 2)) 31)) fun p15 =>
  forceR (gptF l3 u3 (Nat.land (Nat.shiftRight w (Nat.add o15 7)) 31)) fun r15 =>
  forceR (Nat.add o15 (mlen k15)) fun o16 =>
  forceR (Nat.land (Nat.shiftRight w o16) 3) fun k16 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o16 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o16 7)) 1023) (Nat.beq k16 2)) fun m16 =>
  forceR (gptF (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o16 2)) 31)) fun p16 =>
  forceR (gptF (Nat.add l3 l4) (Nat.add u3 u4) (Nat.land (Nat.shiftRight w (Nat.add o16 7)) 31)) fun r16 =>
  forceR (Nat.add o16 (mlen k16)) fun o17 =>
  forceR (Nat.land (Nat.shiftRight w o17) 3) fun k17 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o17 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o17 7)) 1023) (Nat.beq k17 2)) fun m17 =>
  forceR (gptF (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o17 2)) 31)) fun p17 =>
  forceR (gptF (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.land (Nat.shiftRight w (Nat.add o17 7)) 31)) fun r17 =>
  forceR (Nat.add o17 (mlen k17)) fun o18 =>
  forceR (Nat.land (Nat.shiftRight w o18) 3) fun k18 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o18 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o18 7)) 1023) (Nat.beq k18 2)) fun m18 =>
  forceR (gptF l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o18 2)) 31)) fun p18 =>
  forceR (gptF l4 u4 (Nat.land (Nat.shiftRight w (Nat.add o18 7)) 31)) fun r18 =>
  forceR (Nat.add o18 (mlen k18)) fun o19 =>
  forceR (Nat.land (Nat.shiftRight w o19) 3) fun k19 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o19 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o19 7)) 1023) (Nat.beq k19 2)) fun m19 =>
  forceR (gptF (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o19 2)) 31)) fun p19 =>
  forceR (gptF (Nat.add l4 l5) (Nat.add u4 u5) (Nat.land (Nat.shiftRight w (Nat.add o19 7)) 31)) fun r19 =>
  forceR (Nat.add o19 (mlen k19)) fun o20 =>
  forceR (Nat.land (Nat.shiftRight w o20) 3) fun k20 =>
  forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o20 12)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o20 7)) 1023) (Nat.beq k20 2)) fun m20 =>
  forceR (gptF l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o20 2)) 31)) fun p20 =>
  forceR (gptF l5 u5 (Nat.land (Nat.shiftRight w (Nat.add o20 7)) 31)) fun r20 =>
  forceR (Nat.add o20 (mlen k20)) fun o21 =>
  Bool.rec (motive := fun _ => ℕ) 0 o21 (mscheck top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 k0 m0 p0 r0 k1 m1 p1 r1 k2 m2 p2 r2 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20)


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

/-- a leaf (bit 0 clear; bit 1 the kind: zero-order, or minorant with its payload from bit 2): in the reflected
half-space, or the leaf's own test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 2) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (forceR (mleafN top bk tD bD pb R (Nat.shiftRight w 2) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) fun n => Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) (0) (Nat.beq n 0)) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) (Nat.add pos 2) (Nat.ble (Nat.add u5 1) l0)

/-- the bisection walk (`Nat.rec` on the fuel): the node word is `bits >>> pos` (bit 0 split, bits 1..3 axis) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq (Nat.land w 1) 1))
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
    258008678400000000000 ≤ 10000000000 * (41468 * l0 + 70344 * l1 + 87381 * l2 + 87381 * l3 + 70344 * l4 + 41468 * l5) + 32768 * (21269442 * lb3 top bk (l0) (u0) + 890898 * lb3 top bk (l0 + l1) (u0 + u1) + 28398464 * lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) + 75539688 * lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 99999999 * lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 200000000 * lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) + 35896622 * lb3 top bk (l1) (u1) + 65972058 * lb3 top bk (l1 + l2) (u1 + u2) + 71601535 * lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) + 48920622 * lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 99999999 * lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) + 42833935 * lb3 top bk (l2) (u2) + 66274085 * lb3 top bk (l2 + l3) (u2 + u3) + 71601535 * lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) + 75539688 * lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) + 42833935 * lb3 top bk (l3) (u3) + 65972058 * lb3 top bk (l3 + l4) (u3 + u4) + 28398464 * lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) + 35896622 * lb3 top bk (l4) (u4) + 890898 * lb3 top bk (l4 + l5) (u4 + u5) + 21269442 * lb3 top bk (l5) (u5)) := by
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
  have w0 := lb3_sound hlb (l0) (u0) (g0) h01 h02
  have w1 := lb3_sound hlb (l0 + l1) (u0 + u1) (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  have w2 := lb3_sound hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (slo_add (slo_add h01 h11) h21) (shi_add (shi_add h02 h12) h22)
  have w3 := lb3_sound hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  have w4 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  have w5 := lb3_sound hlb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  have w6 := lb3_sound hlb (l1) (u1) (g1) h11 h12
  have w7 := lb3_sound hlb (l1 + l2) (u1 + u2) (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  have w8 := lb3_sound hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  have w9 := lb3_sound hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  have w10 := lb3_sound hlb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  have w11 := lb3_sound hlb (l2) (u2) (g2) h21 h22
  have w12 := lb3_sound hlb (l2 + l3) (u2 + u3) (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  have w13 := lb3_sound hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  have w14 := lb3_sound hlb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  have w15 := lb3_sound hlb (l3) (u3) (g3) h31 h32
  have w16 := lb3_sound hlb (l3 + l4) (u3 + u4) (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  have w17 := lb3_sound hlb (l3 + l4 + l5) (u3 + u4 + u5) (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  have w18 := lb3_sound hlb (l4) (u4) (g4) h41 h42
  have w19 := lb3_sound hlb (l4 + l5) (u4 + u5) (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  have w20 := lb3_sound hlb (l5) (u5) (g5) h51 h52
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 41468 * ((l0 : ℝ) / SC) + 70344 * ((l1 : ℝ) / SC) + 87381 * ((l2 : ℝ) / SC) + 87381 * ((l3 : ℝ) / SC) + 70344 * ((l4 : ℝ) / SC) + 41468 * ((l5 : ℝ) / SC) with hL
  set Wt : ℝ := 21269442 * ((lb3 top bk (l0) (u0) : ℝ) / 10000000000) + 890898 * ((lb3 top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 28398464 * ((lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 75539688 * ((lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 99999999 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 200000000 * ((lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 35896622 * ((lb3 top bk (l1) (u1) : ℝ) / 10000000000) + 65972058 * ((lb3 top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 71601535 * ((lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 48920622 * ((lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 99999999 * ((lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 42833935 * ((lb3 top bk (l2) (u2) : ℝ) / 10000000000) + 66274085 * ((lb3 top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 71601535 * ((lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 75539688 * ((lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 42833935 * ((lb3 top bk (l3) (u3) : ℝ) / 10000000000) + 65972058 * ((lb3 top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 28398464 * ((lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) / 10000000000) + 35896622 * ((lb3 top bk (l4) (u4) : ℝ) / 10000000000) + 890898 * ((lb3 top bk (l4 + l5) (u4 + u5) : ℝ) / 10000000000) + 21269442 * ((lb3 top bk (l5) (u5) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (41468 * (l0 : ℝ) + 70344 * (l1 : ℝ) + 87381 * (l2 : ℝ) + 87381 * (l3 : ℝ) + 70344 * (l4 : ℝ) + 41468 * (l5 : ℝ)) + 32768 * (21269442 * (lb3 top bk (l0) (u0) : ℝ) + 890898 * (lb3 top bk (l0 + l1) (u0 + u1) : ℝ) + 28398464 * (lb3 top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 75539688 * (lb3 top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 99999999 * (lb3 top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 200000000 * (lb3 top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) + 35896622 * (lb3 top bk (l1) (u1) : ℝ) + 65972058 * (lb3 top bk (l1 + l2) (u1 + u2) : ℝ) + 71601535 * (lb3 top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 48920622 * (lb3 top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 99999999 * (lb3 top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) + 42833935 * (lb3 top bk (l2) (u2) : ℝ) + 66274085 * (lb3 top bk (l2 + l3) (u2 + u3) : ℝ) + 71601535 * (lb3 top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 75539688 * (lb3 top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) + 42833935 * (lb3 top bk (l3) (u3) : ℝ) + 65972058 * (lb3 top bk (l3 + l4) (u3 + u4) : ℝ) + 28398464 * (lb3 top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) + 35896622 * (lb3 top bk (l4) (u4) : ℝ) + 890898 * (lb3 top bk (l4 + l5) (u4 + u5) : ℝ) + 21269442 * (lb3 top bk (l5) (u5) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 258008678400000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((41468 / (SA:ℝ)) * g0 + (70344 / (SA:ℝ)) * g1 + (87381 / (SA:ℝ)) * g2 + (87381 / (SA:ℝ)) * g3 + (70344 / (SA:ℝ)) * g4 + (41468 / (SA:ℝ)) * g5
      + (21269442 / (SA:ℝ)) * wfun (g0) + (890898 / (SA:ℝ)) * wfun (g0 + g1) + (28398464 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (75539688 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g1) + (65972058 / (SA:ℝ)) * wfun (g1 + g2) + (71601535 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (48920622 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g2) + (66274085 / (SA:ℝ)) * wfun (g2 + g3) + (71601535 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (75539688 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g3) + (65972058 / (SA:ℝ)) * wfun (g3 + g4) + (28398464 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g4) + (890898 / (SA:ℝ)) * wfun (g4 + g5) + (21269442 / (SA:ℝ)) * wfun (g5)) * SA
      = 41468 * g0 + 70344 * g1 + 87381 * g2 + 87381 * g3 + 70344 * g4 + 41468 * g5 + 21269442 * wfun (g0) + 890898 * wfun (g0 + g1) + 28398464 * wfun (g0 + g1 + g2) + 75539688 * wfun (g0 + g1 + g2 + g3) + 99999999 * wfun (g0 + g1 + g2 + g3 + g4) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 35896622 * wfun (g1) + 65972058 * wfun (g1 + g2) + 71601535 * wfun (g1 + g2 + g3) + 48920622 * wfun (g1 + g2 + g3 + g4) + 99999999 * wfun (g1 + g2 + g3 + g4 + g5) + 42833935 * wfun (g2) + 66274085 * wfun (g2 + g3) + 71601535 * wfun (g2 + g3 + g4) + 75539688 * wfun (g2 + g3 + g4 + g5) + 42833935 * wfun (g3) + 65972058 * wfun (g3 + g4) + 28398464 * wfun (g3 + g4 + g5) + 35896622 * wfun (g4) + 890898 * wfun (g4 + g5) + 21269442 * wfun (g5) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linear_combination hq' + 41468 * h01 + 70344 * h11 + 87381 * h21 + 87381 * h31 + 70344 * h41 + 41468 * h51 + 21269442 * w0 + 890898 * w1 + 28398464 * w2 + 75539688 * w3 + 99999999 * w4 + 200000000 * w5 + 35896622 * w6 + 65972058 * w7 + 71601535 * w8 + 48920622 * w9 + 99999999 * w10 + 42833935 * w11 + 66274085 * w12 + 71601535 * w13 + 75539688 * w14 + 42833935 * w15 + 65972058 * w16 + 28398464 * w17 + 35896622 * w18 + 890898 * w19 + 21269442 * w20

set_option maxHeartbeats 40000000 in
theorem mscheck_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (k0 m0 p0 r0 : ℕ) (k1 m1 p1 r1 : ℕ) (k2 m2 p2 r2 : ℕ) (k3 m3 p3 r3 : ℕ) (k4 m4 p4 r4 : ℕ) (k5 m5 p5 r5 : ℕ) (k6 m6 p6 r6 : ℕ) (k7 m7 p7 r7 : ℕ) (k8 m8 p8 r8 : ℕ) (k9 m9 p9 r9 : ℕ) (k10 m10 p10 r10 : ℕ) (k11 m11 p11 r11 : ℕ) (k12 m12 p12 r12 : ℕ) (k13 m13 p13 r13 : ℕ) (k14 m14 p14 r14 : ℕ) (k15 m15 p15 r15 : ℕ) (k16 m16 p16 r16 : ℕ) (k17 m17 p17 r17 : ℕ) (k18 m18 p18 r18 : ℕ) (k19 m19 p19 r19 : ℕ) (k20 m20 p20 r20 : ℕ) (h : mscheck top bk tD bD f R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 k0 m0 p0 r0 k1 m1 p1 r1 k2 m2 p2 r2 k3 m3 p3 r3 k4 m4 p4 r4 k5 m5 p5 r5 k6 m6 p6 r6 k7 m7 p7 r7 k8 m8 p8 r8 k9 m9 p9 r9 k10 m10 p10 r10 k11 m11 p11 r11 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k19 m19 p19 r19 k20 m20 p20 r20 = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  unfold mscheck at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlu0, hlu1⟩, hlu2⟩, hlu3⟩, hlu4⟩, hlu5⟩, hm0⟩, hok0⟩, hm1⟩, hok1⟩, hm2⟩, hok2⟩, hm3⟩, hok3⟩, hm4⟩, hok4⟩, hm5⟩, hok5⟩, hm6⟩, hok6⟩, hm7⟩, hok7⟩, hm8⟩, hok8⟩, hm9⟩, hok9⟩, hm10⟩, hok10⟩, hm11⟩, hok11⟩, hm12⟩, hok12⟩, hm13⟩, hok13⟩, hm14⟩, hok14⟩, hm15⟩, hok15⟩, hm16⟩, hok16⟩, hm17⟩, hok17⟩, hm18⟩, hok18⟩, hm19⟩, hok19⟩, hm20⟩, hok20⟩, hmain⟩ := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨D0, hDl0, hb0⟩ := mterm_ok hlb hD hpt hR (l0) (u0) k0 m0 p0 r0 hm0 hok0
    (g0) h01 h02
  push_cast at hb0
  obtain ⟨D1, hDl1, hb1⟩ := mterm_ok hlb hD hpt hR (l0 + l1) (u0 + u1) k1 m1 p1 r1 hm1 hok1
    (g0 + g1) (slo_add h01 h11) (shi_add h02 h12)
  push_cast at hb1
  obtain ⟨D2, hDl2, hb2⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2) (u0 + u1 + u2) k2 m2 p2 r2 hm2 hok2
    (g0 + g1 + g2) (slo_add (slo_add h01 h11) h21) (shi_add (shi_add h02 h12) h22)
  push_cast at hb2
  obtain ⟨D3, hDl3, hb3⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) k3 m3 p3 r3 hm3 hok3
    (g0 + g1 + g2 + g3) (slo_add (slo_add (slo_add h01 h11) h21) h31) (shi_add (shi_add (shi_add h02 h12) h22) h32)
  push_cast at hb3
  obtain ⟨D4, hDl4, hb4⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) k4 m4 p4 r4 hm4 hok4
    (g0 + g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42)
  push_cast at hb4
  obtain ⟨D5, hDl5, hb5⟩ := mterm_ok hlb hD hpt hR (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) k5 m5 p5 r5 hm5 hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add (slo_add h01 h11) h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add (shi_add h02 h12) h22) h32) h42) h52)
  push_cast at hb5
  obtain ⟨D6, hDl6, hb6⟩ := mterm_ok hlb hD hpt hR (l1) (u1) k6 m6 p6 r6 hm6 hok6
    (g1) h11 h12
  push_cast at hb6
  obtain ⟨D7, hDl7, hb7⟩ := mterm_ok hlb hD hpt hR (l1 + l2) (u1 + u2) k7 m7 p7 r7 hm7 hok7
    (g1 + g2) (slo_add h11 h21) (shi_add h12 h22)
  push_cast at hb7
  obtain ⟨D8, hDl8, hb8⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3) (u1 + u2 + u3) k8 m8 p8 r8 hm8 hok8
    (g1 + g2 + g3) (slo_add (slo_add h11 h21) h31) (shi_add (shi_add h12 h22) h32)
  push_cast at hb8
  obtain ⟨D9, hDl9, hb9⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) k9 m9 p9 r9 hm9 hok9
    (g1 + g2 + g3 + g4) (slo_add (slo_add (slo_add h11 h21) h31) h41) (shi_add (shi_add (shi_add h12 h22) h32) h42)
  push_cast at hb9
  obtain ⟨D10, hDl10, hb10⟩ := mterm_ok hlb hD hpt hR (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) k10 m10 p10 r10 hm10 hok10
    (g1 + g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add (slo_add h11 h21) h31) h41) h51) (shi_add (shi_add (shi_add (shi_add h12 h22) h32) h42) h52)
  push_cast at hb10
  obtain ⟨D11, hDl11, hb11⟩ := mterm_ok hlb hD hpt hR (l2) (u2) k11 m11 p11 r11 hm11 hok11
    (g2) h21 h22
  push_cast at hb11
  obtain ⟨D12, hDl12, hb12⟩ := mterm_ok hlb hD hpt hR (l2 + l3) (u2 + u3) k12 m12 p12 r12 hm12 hok12
    (g2 + g3) (slo_add h21 h31) (shi_add h22 h32)
  push_cast at hb12
  obtain ⟨D13, hDl13, hb13⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4) (u2 + u3 + u4) k13 m13 p13 r13 hm13 hok13
    (g2 + g3 + g4) (slo_add (slo_add h21 h31) h41) (shi_add (shi_add h22 h32) h42)
  push_cast at hb13
  obtain ⟨D14, hDl14, hb14⟩ := mterm_ok hlb hD hpt hR (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) k14 m14 p14 r14 hm14 hok14
    (g2 + g3 + g4 + g5) (slo_add (slo_add (slo_add h21 h31) h41) h51) (shi_add (shi_add (shi_add h22 h32) h42) h52)
  push_cast at hb14
  obtain ⟨D15, hDl15, hb15⟩ := mterm_ok hlb hD hpt hR (l3) (u3) k15 m15 p15 r15 hm15 hok15
    (g3) h31 h32
  push_cast at hb15
  obtain ⟨D16, hDl16, hb16⟩ := mterm_ok hlb hD hpt hR (l3 + l4) (u3 + u4) k16 m16 p16 r16 hm16 hok16
    (g3 + g4) (slo_add h31 h41) (shi_add h32 h42)
  push_cast at hb16
  obtain ⟨D17, hDl17, hb17⟩ := mterm_ok hlb hD hpt hR (l3 + l4 + l5) (u3 + u4 + u5) k17 m17 p17 r17 hm17 hok17
    (g3 + g4 + g5) (slo_add (slo_add h31 h41) h51) (shi_add (shi_add h32 h42) h52)
  push_cast at hb17
  obtain ⟨D18, hDl18, hb18⟩ := mterm_ok hlb hD hpt hR (l4) (u4) k18 m18 p18 r18 hm18 hok18
    (g4) h41 h42
  push_cast at hb18
  obtain ⟨D19, hDl19, hb19⟩ := mterm_ok hlb hD hpt hR (l4 + l5) (u4 + u5) k19 m19 p19 r19 hm19 hok19
    (g4 + g5) (slo_add h41 h51) (shi_add h42 h52)
  push_cast at hb19
  obtain ⟨D20, hDl20, hb20⟩ := mterm_ok hlb hD hpt hR (l5) (u5) k20 m20 p20 r20 hm20 hok20
    (g5) h51 h52
  push_cast at hb20
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have hN0 : -((((2000000000 * (21269442 * (mw1 k0 m0 + mw2 k0 m0) + 890898 * (mw1 k1 m1 + mw2 k1 m1) + 28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5))) - (42463232000000000 + 21269442 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 890898 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 41468 : ℝ) + 21269442 * D0 + 890898 * D1 + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5) := by
    have := natsub_ge (2000000000 * (21269442 * (mw1 k0 m0 + mw2 k0 m0) + 890898 * (mw1 k1 m1 + mw2 k1 m1) + 28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5))) (42463232000000000 + 21269442 * msl f (mw1 k0 m0) (mw2 k0 m0) p0 r0 + 890898 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5)
    push_cast at this ⊢
    linear_combination this + 21269442 * hDl0 + 890898 * hDl1 + 28398464 * hDl2 + 75539688 * hDl3 + 99999999 * hDl4 + 200000000 * hDl5
  have hlu0' : ((u0 - l0 : ℕ) : ℝ) = (u0 : ℝ) - l0 := Nat.cast_sub hlu0
  have hg0 := gap_lo (E := ((1024 * 41468 : ℝ) + 21269442 * D0 + 890898 * D1 + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5)) (e := g0 - (l0 : ℝ) / 32768) (H := ((u0 - l0 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN0 (sub_nonneg.mpr h01) (by rw [hlu0', sub_div]; exact sub_le_sub_right h02 _)
  have hN1 : -((((2000000000 * (890898 * (mw1 k1 m1 + mw2 k1 m1) + 28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 35896622 * (mw1 k6 m6 + mw2 k6 m6) + 65972058 * (mw1 k7 m7 + mw2 k7 m7) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10))) - (72032256000000000 + 890898 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 35896622 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 65972058 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 70344 : ℝ) + 890898 * D1 + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 35896622 * D6 + 65972058 * D7 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10) := by
    have := natsub_ge (2000000000 * (890898 * (mw1 k1 m1 + mw2 k1 m1) + 28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 35896622 * (mw1 k6 m6 + mw2 k6 m6) + 65972058 * (mw1 k7 m7 + mw2 k7 m7) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10))) (72032256000000000 + 890898 * msl f (mw1 k1 m1) (mw2 k1 m1) p1 r1 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 35896622 * msl f (mw1 k6 m6) (mw2 k6 m6) p6 r6 + 65972058 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10)
    push_cast at this ⊢
    linear_combination this + 890898 * hDl1 + 28398464 * hDl2 + 75539688 * hDl3 + 99999999 * hDl4 + 200000000 * hDl5 + 35896622 * hDl6 + 65972058 * hDl7 + 71601535 * hDl8 + 48920622 * hDl9 + 99999999 * hDl10
  have hlu1' : ((u1 - l1 : ℕ) : ℝ) = (u1 : ℝ) - l1 := Nat.cast_sub hlu1
  have hg1 := gap_lo (E := ((1024 * 70344 : ℝ) + 890898 * D1 + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 35896622 * D6 + 65972058 * D7 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10)) (e := g1 - (l1 : ℝ) / 32768) (H := ((u1 - l1 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN1 (sub_nonneg.mpr h11) (by rw [hlu1', sub_div]; exact sub_le_sub_right h12 _)
  have hN2 : -((((2000000000 * (28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 65972058 * (mw1 k7 m7 + mw2 k7 m7) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 42833935 * (mw1 k11 m11 + mw2 k11 m11) + 66274085 * (mw1 k12 m12 + mw2 k12 m12) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14))) - (89478144000000000 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 65972058 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 42833935 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 66274085 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 87381 : ℝ) + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 65972058 * D7 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10 + 42833935 * D11 + 66274085 * D12 + 71601535 * D13 + 75539688 * D14) := by
    have := natsub_ge (2000000000 * (28398464 * (mw1 k2 m2 + mw2 k2 m2) + 75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 65972058 * (mw1 k7 m7 + mw2 k7 m7) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 42833935 * (mw1 k11 m11 + mw2 k11 m11) + 66274085 * (mw1 k12 m12 + mw2 k12 m12) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14))) (89478144000000000 + 28398464 * msl f (mw1 k2 m2) (mw2 k2 m2) p2 r2 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 65972058 * msl f (mw1 k7 m7) (mw2 k7 m7) p7 r7 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 42833935 * msl f (mw1 k11 m11) (mw2 k11 m11) p11 r11 + 66274085 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14)
    push_cast at this ⊢
    linear_combination this + 28398464 * hDl2 + 75539688 * hDl3 + 99999999 * hDl4 + 200000000 * hDl5 + 65972058 * hDl7 + 71601535 * hDl8 + 48920622 * hDl9 + 99999999 * hDl10 + 42833935 * hDl11 + 66274085 * hDl12 + 71601535 * hDl13 + 75539688 * hDl14
  have hlu2' : ((u2 - l2 : ℕ) : ℝ) = (u2 : ℝ) - l2 := Nat.cast_sub hlu2
  have hg2 := gap_lo (E := ((1024 * 87381 : ℝ) + 28398464 * D2 + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 65972058 * D7 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10 + 42833935 * D11 + 66274085 * D12 + 71601535 * D13 + 75539688 * D14)) (e := g2 - (l2 : ℝ) / 32768) (H := ((u2 - l2 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN2 (sub_nonneg.mpr h21) (by rw [hlu2', sub_div]; exact sub_le_sub_right h22 _)
  have hN3 : -((((2000000000 * (75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 66274085 * (mw1 k12 m12 + mw2 k12 m12) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 42833935 * (mw1 k15 m15 + mw2 k15 m15) + 65972058 * (mw1 k16 m16 + mw2 k16 m16) + 28398464 * (mw1 k17 m17 + mw2 k17 m17))) - (89478144000000000 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 66274085 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 42833935 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 65972058 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 87381 : ℝ) + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10 + 66274085 * D12 + 71601535 * D13 + 75539688 * D14 + 42833935 * D15 + 65972058 * D16 + 28398464 * D17) := by
    have := natsub_ge (2000000000 * (75539688 * (mw1 k3 m3 + mw2 k3 m3) + 99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 71601535 * (mw1 k8 m8 + mw2 k8 m8) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 66274085 * (mw1 k12 m12 + mw2 k12 m12) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 42833935 * (mw1 k15 m15 + mw2 k15 m15) + 65972058 * (mw1 k16 m16 + mw2 k16 m16) + 28398464 * (mw1 k17 m17 + mw2 k17 m17))) (89478144000000000 + 75539688 * msl f (mw1 k3 m3) (mw2 k3 m3) p3 r3 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 71601535 * msl f (mw1 k8 m8) (mw2 k8 m8) p8 r8 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 66274085 * msl f (mw1 k12 m12) (mw2 k12 m12) p12 r12 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 42833935 * msl f (mw1 k15 m15) (mw2 k15 m15) p15 r15 + 65972058 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17)
    push_cast at this ⊢
    linear_combination this + 75539688 * hDl3 + 99999999 * hDl4 + 200000000 * hDl5 + 71601535 * hDl8 + 48920622 * hDl9 + 99999999 * hDl10 + 66274085 * hDl12 + 71601535 * hDl13 + 75539688 * hDl14 + 42833935 * hDl15 + 65972058 * hDl16 + 28398464 * hDl17
  have hlu3' : ((u3 - l3 : ℕ) : ℝ) = (u3 : ℝ) - l3 := Nat.cast_sub hlu3
  have hg3 := gap_lo (E := ((1024 * 87381 : ℝ) + 75539688 * D3 + 99999999 * D4 + 200000000 * D5 + 71601535 * D8 + 48920622 * D9 + 99999999 * D10 + 66274085 * D12 + 71601535 * D13 + 75539688 * D14 + 42833935 * D15 + 65972058 * D16 + 28398464 * D17)) (e := g3 - (l3 : ℝ) / 32768) (H := ((u3 - l3 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN3 (sub_nonneg.mpr h31) (by rw [hlu3', sub_div]; exact sub_le_sub_right h32 _)
  have hN4 : -((((2000000000 * (99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 65972058 * (mw1 k16 m16 + mw2 k16 m16) + 28398464 * (mw1 k17 m17 + mw2 k17 m17) + 35896622 * (mw1 k18 m18 + mw2 k18 m18) + 890898 * (mw1 k19 m19 + mw2 k19 m19))) - (72032256000000000 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 65972058 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 35896622 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 890898 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 70344 : ℝ) + 99999999 * D4 + 200000000 * D5 + 48920622 * D9 + 99999999 * D10 + 71601535 * D13 + 75539688 * D14 + 65972058 * D16 + 28398464 * D17 + 35896622 * D18 + 890898 * D19) := by
    have := natsub_ge (2000000000 * (99999999 * (mw1 k4 m4 + mw2 k4 m4) + 200000000 * (mw1 k5 m5 + mw2 k5 m5) + 48920622 * (mw1 k9 m9 + mw2 k9 m9) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 71601535 * (mw1 k13 m13 + mw2 k13 m13) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 65972058 * (mw1 k16 m16 + mw2 k16 m16) + 28398464 * (mw1 k17 m17 + mw2 k17 m17) + 35896622 * (mw1 k18 m18 + mw2 k18 m18) + 890898 * (mw1 k19 m19 + mw2 k19 m19))) (72032256000000000 + 99999999 * msl f (mw1 k4 m4) (mw2 k4 m4) p4 r4 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 48920622 * msl f (mw1 k9 m9) (mw2 k9 m9) p9 r9 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 71601535 * msl f (mw1 k13 m13) (mw2 k13 m13) p13 r13 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 65972058 * msl f (mw1 k16 m16) (mw2 k16 m16) p16 r16 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 35896622 * msl f (mw1 k18 m18) (mw2 k18 m18) p18 r18 + 890898 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19)
    push_cast at this ⊢
    linear_combination this + 99999999 * hDl4 + 200000000 * hDl5 + 48920622 * hDl9 + 99999999 * hDl10 + 71601535 * hDl13 + 75539688 * hDl14 + 65972058 * hDl16 + 28398464 * hDl17 + 35896622 * hDl18 + 890898 * hDl19
  have hlu4' : ((u4 - l4 : ℕ) : ℝ) = (u4 : ℝ) - l4 := Nat.cast_sub hlu4
  have hg4 := gap_lo (E := ((1024 * 70344 : ℝ) + 99999999 * D4 + 200000000 * D5 + 48920622 * D9 + 99999999 * D10 + 71601535 * D13 + 75539688 * D14 + 65972058 * D16 + 28398464 * D17 + 35896622 * D18 + 890898 * D19)) (e := g4 - (l4 : ℝ) / 32768) (H := ((u4 - l4 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN4 (sub_nonneg.mpr h41) (by rw [hlu4', sub_div]; exact sub_le_sub_right h42 _)
  have hN5 : -((((2000000000 * (200000000 * (mw1 k5 m5 + mw2 k5 m5) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 28398464 * (mw1 k17 m17 + mw2 k17 m17) + 890898 * (mw1 k19 m19 + mw2 k19 m19) + 21269442 * (mw1 k20 m20 + mw2 k20 m20))) - (42463232000000000 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 890898 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 21269442 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20) : ℕ) : ℝ)) ≤ 1000000000 * ((1024 * 41468 : ℝ) + 200000000 * D5 + 99999999 * D10 + 75539688 * D14 + 28398464 * D17 + 890898 * D19 + 21269442 * D20) := by
    have := natsub_ge (2000000000 * (200000000 * (mw1 k5 m5 + mw2 k5 m5) + 99999999 * (mw1 k10 m10 + mw2 k10 m10) + 75539688 * (mw1 k14 m14 + mw2 k14 m14) + 28398464 * (mw1 k17 m17 + mw2 k17 m17) + 890898 * (mw1 k19 m19 + mw2 k19 m19) + 21269442 * (mw1 k20 m20 + mw2 k20 m20))) (42463232000000000 + 200000000 * msl f (mw1 k5 m5) (mw2 k5 m5) p5 r5 + 99999999 * msl f (mw1 k10 m10) (mw2 k10 m10) p10 r10 + 75539688 * msl f (mw1 k14 m14) (mw2 k14 m14) p14 r14 + 28398464 * msl f (mw1 k17 m17) (mw2 k17 m17) p17 r17 + 890898 * msl f (mw1 k19 m19) (mw2 k19 m19) p19 r19 + 21269442 * msl f (mw1 k20 m20) (mw2 k20 m20) p20 r20)
    push_cast at this ⊢
    linear_combination this + 200000000 * hDl5 + 99999999 * hDl10 + 75539688 * hDl14 + 28398464 * hDl17 + 890898 * hDl19 + 21269442 * hDl20
  have hlu5' : ((u5 - l5 : ℕ) : ℝ) = (u5 : ℝ) - l5 := Nat.cast_sub hlu5
  have hg5 := gap_lo (E := ((1024 * 41468 : ℝ) + 200000000 * D5 + 99999999 * D10 + 75539688 * D14 + 28398464 * D17 + 890898 * D19 + 21269442 * D20)) (e := g5 - (l5 : ℝ) / 32768) (H := ((u5 - l5 : ℕ) : ℝ))
    (natsub_nonneg _ _) hN5 (sub_nonneg.mpr h51) (by rw [hlu5', sub_div]; exact sub_le_sub_right h52 _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  simp only [hlu0', hlu1', hlu2', hlu3', hlu4', hlu5'] at hq hg0 hg1 hg2 hg3 hg4 hg5
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((41468 / (SA:ℝ)) * g0 + (70344 / (SA:ℝ)) * g1 + (87381 / (SA:ℝ)) * g2 + (87381 / (SA:ℝ)) * g3 + (70344 / (SA:ℝ)) * g4 + (41468 / (SA:ℝ)) * g5
      + (21269442 / (SA:ℝ)) * wfun (g0) + (890898 / (SA:ℝ)) * wfun (g0 + g1) + (28398464 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (75539688 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g1) + (65972058 / (SA:ℝ)) * wfun (g1 + g2) + (71601535 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (48920622 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g2) + (66274085 / (SA:ℝ)) * wfun (g2 + g3) + (71601535 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (75539688 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g3) + (65972058 / (SA:ℝ)) * wfun (g3 + g4) + (28398464 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g4) + (890898 / (SA:ℝ)) * wfun (g4 + g5) + (21269442 / (SA:ℝ)) * wfun (g5)) * SA
      = 41468 * g0 + 70344 * g1 + 87381 * g2 + 87381 * g3 + 70344 * g4 + 41468 * g5 + 21269442 * wfun (g0) + 890898 * wfun (g0 + g1) + 28398464 * wfun (g0 + g1 + g2) + 75539688 * wfun (g0 + g1 + g2 + g3) + 99999999 * wfun (g0 + g1 + g2 + g3 + g4) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 35896622 * wfun (g1) + 65972058 * wfun (g1 + g2) + 71601535 * wfun (g1 + g2 + g3) + 48920622 * wfun (g1 + g2 + g3 + g4) + 99999999 * wfun (g1 + g2 + g3 + g4 + g5) + 42833935 * wfun (g2) + 66274085 * wfun (g2 + g3) + 71601535 * wfun (g2 + g3 + g4) + 75539688 * wfun (g2 + g3 + g4 + g5) + 42833935 * wfun (g3) + 65972058 * wfun (g3 + g4) + 28398464 * wfun (g3 + g4 + g5) + 35896622 * wfun (g4) + 890898 * wfun (g4 + g5) + 21269442 * wfun (g5) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 787380 := by norm_num [cN]
  rw [hcN]
  linarith [hq, hg0, hg1, hg2, hg3, hg4, hg5, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 21269442), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 890898), mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 28398464), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 75539688), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 99999999), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 35896622), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 65972058), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 71601535), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 48920622), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 99999999), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 42833935), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 66274085), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 71601535), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 75539688), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 42833935), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 65972058), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 28398464), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 35896622), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 890898), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 21269442)]

theorem mleafN_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ)
    (h : mleafN top bk tD bD pb R w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  unfold mleafN at h
  simp only [forceR_eq] at h
  exact mscheck_sound (f := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h)

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

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ)
    (h : leafStep top bk tD bD pb R pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold leafStep at h
  cases hs : Nat.ble (Nat.add u5 1) l0
  · rw [hs] at h
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
      · rw [hl] at h; exact absurd rfl h
      · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
        exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
    · rw [hk, forceR_eq] at h
      intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
      refine Or.inl (mleafN_sound hlb hD hpt hR (Nat.shiftRight w 2) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ?_ g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
      intro h0; rw [h0] at h; exact h rfl
  · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
    right
    have hsk : u5 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u5 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (splitAx (walk top bk tD bD pb R bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hD hpt hR pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 e : ℕ)
    (h : walk top bk tD bD pb R bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 :=
  walk_sound hlb hD hpt hR bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (h ▸ he)


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
    (hS0 : cN * SC ≤ 41468 * S0) (hS1 : cN * SC ≤ 70344 * S1) (hS2 : cN * SC ≤ 87381 * S2) (hS3 : cN * SC ≤ 87381 * S3) (hS4 : cN * SC ≤ 70344 * S4) (hS5 : cN * SC ≤ 41468 * S5)
    (hcov0 : coverCheck 21269442 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 35896622 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 42833935 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 42833935 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 35896622 (SC / 2) S4 cover4 = true) (hcov5 : coverCheck 21269442 (SC / 2) S5 cover5 = true)
    (hwin : cN * 4 ≤ 21269442)
    (hrun : ∀ i0 i1 i2 i3 i4 i5, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length → i5 < (badOf cover5).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2 ((badOf cover5).getD i5 (0, 0)).1 ((badOf cover5).getD i5 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → 0 ≤ g5 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 ∨ g5 < g0 := by
  intro g0 g1 g2 g3 g4 g5 hg0 hg1 hg2 hg3 hg4 hg5
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (41468 / (SA:ℝ)) * g0 + (70344 / (SA:ℝ)) * g1 + (87381 / (SA:ℝ)) * g2 + (87381 / (SA:ℝ)) * g3 + (70344 / (SA:ℝ)) * g4 + (41468 / (SA:ℝ)) * g5 with hLin
  set Wt : ℝ := (21269442 / (SA:ℝ)) * wfun (g0) + (890898 / (SA:ℝ)) * wfun (g0 + g1) + (28398464 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (75539688 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g1) + (65972058 / (SA:ℝ)) * wfun (g1 + g2) + (71601535 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (48920622 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g2) + (66274085 / (SA:ℝ)) * wfun (g2 + g3) + (71601535 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (75539688 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (42833935 / (SA:ℝ)) * wfun (g3) + (65972058 / (SA:ℝ)) * wfun (g3 + g4) + (28398464 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (35896622 / (SA:ℝ)) * wfun (g4) + (890898 / (SA:ℝ)) * wfun (g4 + g5) + (21269442 / (SA:ℝ)) * wfun (g5) with hWt
  have hG : G g0 g1 g2 g3 g4 g5 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (41468 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (70344 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (87381 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (87381 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (70344 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have hb50 : (0:ℝ) ≤ (41468 / (SA:ℝ)) * g5 := mul_nonneg (by positivity) hg5
  have ha00 : (0:ℝ) ≤ (21269442 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (890898 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (28398464 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (75539688 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (99999999 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (35896622 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (65972058 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (71601535 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (48920622 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (99999999 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (42833935 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (66274085 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (71601535 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (75539688 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha150 : (0:ℝ) ≤ (42833935 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha160 : (0:ℝ) ≤ (65972058 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha170 : (0:ℝ) ≤ (28398464 / (SA:ℝ)) * wfun (g3 + g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha180 : (0:ℝ) ≤ (35896622 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have ha190 : (0:ℝ) ≤ (890898 / (SA:ℝ)) * wfun (g4 + g5) := mul_nonneg (by positivity) (hw _)
  have ha200 : (0:ℝ) ≤ (21269442 / (SA:ℝ)) * wfun (g5) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30) hb40) hb50)
  have hWt0 : 0 ≤ Wt := by rw [hWt]; exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190) ha200)
  have hbL0 : (41468 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_trans (le_trans le_rfl (le_add_of_nonneg_right hb10)) (le_add_of_nonneg_right hb20)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50))
  have hbL1 : (70344 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left hb00) (le_add_of_nonneg_right hb20)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50))
  have hbL2 : (87381 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg hb00 hb10)) (le_add_of_nonneg_right hb30)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50))
  have hbL3 : (87381 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; exact (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg hb00 hb10) hb20)) (le_add_of_nonneg_right hb40)) (le_add_of_nonneg_right hb50))
  have hbL4 : (70344 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; exact (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30)) (le_add_of_nonneg_right hb50))
  have hbL5 : (41468 / (SA:ℝ)) * g5 ≤ Lin := by rw [hLin]; exact (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg hb00 hb10) hb20) hb30) hb40))
  have haW0 : (21269442 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans le_rfl (le_add_of_nonneg_right ha10)) (le_add_of_nonneg_right ha20)) (le_add_of_nonneg_right ha30)) (le_add_of_nonneg_right ha40)) (le_add_of_nonneg_right ha50)) (le_add_of_nonneg_right ha60)) (le_add_of_nonneg_right ha70)) (le_add_of_nonneg_right ha80)) (le_add_of_nonneg_right ha90)) (le_add_of_nonneg_right ha100)) (le_add_of_nonneg_right ha110)) (le_add_of_nonneg_right ha120)) (le_add_of_nonneg_right ha130)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200))
  have haW6 : (35896622 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50)) (le_add_of_nonneg_right ha70)) (le_add_of_nonneg_right ha80)) (le_add_of_nonneg_right ha90)) (le_add_of_nonneg_right ha100)) (le_add_of_nonneg_right ha110)) (le_add_of_nonneg_right ha120)) (le_add_of_nonneg_right ha130)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200))
  have haW11 : (42833935 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100)) (le_add_of_nonneg_right ha120)) (le_add_of_nonneg_right ha130)) (le_add_of_nonneg_right ha140)) (le_add_of_nonneg_right ha150)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200))
  have haW15 : (42833935 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_trans (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140)) (le_add_of_nonneg_right ha160)) (le_add_of_nonneg_right ha170)) (le_add_of_nonneg_right ha180)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200))
  have haW18 : (35896622 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; exact (le_trans (le_trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170)) (le_add_of_nonneg_right ha190)) (le_add_of_nonneg_right ha200))
  have haW20 : (21269442 / (SA:ℝ)) * wfun (g5) ≤ Wt := by rw [hWt]; exact (le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ha00 ha10) ha20) ha30) ha40) ha50) ha60) ha70) ha80) ha90) ha100) ha110) ha120) ha130) ha140) ha150) ha160) ha170) ha180) ha190))
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (41468 / (SA:ℝ)) * g0 := by
      rw [div_le_iff₀ hSA]
      have e : (41468 / (SA:ℝ)) * g0 * SA = 41468 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 41468 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS0
        _ = 41468 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 41468 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL0 (le_add_of_nonneg_right hWt0))
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (21269442 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (21269442 / (SA:ℝ)) * wfun g0 * SA = 21269442 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 21269442)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW0 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · have hc0 : (cN : ℝ) / SA ≤ (21269442 / (SA:ℝ)) * wfun (g0) := by exact_mod_cast hclear0
    left; rw [hG]; exact le_trans hc0 (le_trans haW0 (le_add_of_nonneg_left hLin0))
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (70344 / (SA:ℝ)) * g1 := by
      rw [div_le_iff₀ hSA]
      have e : (70344 / (SA:ℝ)) * g1 * SA = 70344 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 70344 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS1
        _ = 70344 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 70344 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL1 (le_add_of_nonneg_right hWt0))
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (35896622 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (35896622 / (SA:ℝ)) * wfun g1 * SA = 35896622 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 35896622)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW6 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · have hc1 : (cN : ℝ) / SA ≤ (35896622 / (SA:ℝ)) * wfun (g1) := by exact_mod_cast hclear1
    left; rw [hG]; exact le_trans hc1 (le_trans haW6 (le_add_of_nonneg_left hLin0))
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (87381 / (SA:ℝ)) * g2 := by
      rw [div_le_iff₀ hSA]
      have e : (87381 / (SA:ℝ)) * g2 * SA = 87381 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 87381 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS2
        _ = 87381 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 87381 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL2 (le_add_of_nonneg_right hWt0))
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (42833935 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (42833935 / (SA:ℝ)) * wfun g2 * SA = 42833935 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 42833935)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW11 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · have hc2 : (cN : ℝ) / SA ≤ (42833935 / (SA:ℝ)) * wfun (g2) := by exact_mod_cast hclear2
    left; rw [hG]; exact le_trans hc2 (le_trans haW11 (le_add_of_nonneg_left hLin0))
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (87381 / (SA:ℝ)) * g3 := by
      rw [div_le_iff₀ hSA]
      have e : (87381 / (SA:ℝ)) * g3 * SA = 87381 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 87381 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS3
        _ = 87381 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 87381 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL3 (le_add_of_nonneg_right hWt0))
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (42833935 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (42833935 / (SA:ℝ)) * wfun g3 * SA = 42833935 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 42833935)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW15 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · have hc3 : (cN : ℝ) / SA ≤ (42833935 / (SA:ℝ)) * wfun (g3) := by exact_mod_cast hclear3
    left; rw [hG]; exact le_trans hc3 (le_trans haW15 (le_add_of_nonneg_left hLin0))
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (70344 / (SA:ℝ)) * g4 := by
      rw [div_le_iff₀ hSA]
      have e : (70344 / (SA:ℝ)) * g4 * SA = 70344 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 70344 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS4
        _ = 70344 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 70344 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL4 (le_add_of_nonneg_right hWt0))
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (35896622 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (35896622 / (SA:ℝ)) * wfun g4 * SA = 35896622 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 35896622)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW18 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · have hc4 : (cN : ℝ) / SA ≤ (35896622 / (SA:ℝ)) * wfun (g4) := by exact_mod_cast hclear4
    left; rw [hG]; exact le_trans hc4 (le_trans haW18 (le_add_of_nonneg_left hLin0))
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  -- gap 5: beyond the cutoff the pressure alone pays
  by_cases hcut5 : (S5 : ℝ) / SC ≤ g5
  · have h1 : (cN : ℝ) / SA ≤ (41468 / (SA:ℝ)) * g5 := by
      rw [div_le_iff₀ hSA]
      have e : (41468 / (SA:ℝ)) * g5 * SA = 41468 * g5 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 41468 * S5 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; exact_mod_cast hS5
        _ = 41468 * ((S5 : ℝ) / SC) := by ring
        _ ≤ 41468 * g5 := mul_le_mul_of_nonneg_left hcut5 (by norm_num)
    left; rw [hG]; exact le_trans h1 (le_trans hbL5 (le_add_of_nonneg_right hWt0))
  push_neg at hcut5
  rcases le_total g5 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin5 | hwin5
  · have hw19 := wfun_window g5 hg5 (by rw [hhalf] at hwin5; exact hwin5)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (21269442 / (SA:ℝ)) * wfun g5 := by
      rw [div_le_iff₀ hSA]
      have e : (21269442 / (SA:ℝ)) * wfun g5 * SA = 21269442 * wfun g5 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 21269442)
      linear_combination (1 / 4 : ℝ) * hq + hm
    left; rw [hG]; exact le_trans h1 (le_trans haW20 (le_add_of_nonneg_left hLin0))
  rcases cover_sound _ cover5 (SC / 2) S5 hcov5 g5 hwin5 hcut5 with hclear5 | ⟨s5, hs5, he5, hb51, hb52⟩
  · have hc5 : (cN : ℝ) / SA ≤ (21269442 / (SA:ℝ)) * wfun (g5) := by exact_mod_cast hclear5
    left; rw [hG]; exact le_trans hc5 (le_trans haW20 (le_add_of_nonneg_left hLin0))
  obtain ⟨i5, hi5, hsi5⟩ := List.mem_iff_getElem.mp (badOf_mem hs5 he5)
  have hb51' : (((badOf cover5).getD i5 (0, 0)).1 : ℝ) / SC ≤ g5 := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb51
  have hb52' : g5 ≤ (((badOf cover5).getD i5 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi5, hsi5]; exact hb52
  exact hrun i0 i1 i2 i3 i4 i5 hi0 hi1 hi2 hi3 hi4 hi5 g0 g1 g2 g3 g4 g5 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42' hb51' hb52'

end AMW.Cert.AT7

end
