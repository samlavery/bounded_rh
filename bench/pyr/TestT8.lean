import PyrCheck
set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

/-! ###### the 6-point weighted certificate `PyrT8` on the pyramid oracle: leaf test, walk, cover ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrT8

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

def SA : ℕ := 100000000
def cN : ℕ := 329624

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24896 l0) (Nat.mul 42034 l1)) (Nat.mul 46137 l2)) (Nat.mul 42034 l3)) (Nat.mul 24896 l4)) 10000000000
  ee 108011192320000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 1580872499200 (lb top bk l1 u1))
  ee 108011192320000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1732028006400 (lb top bk l2 u2))
  ee 108011192320000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1580872499200 (lb top bk l3 u3))
  ee 108011192320000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 829908582400 (lb top bk l0 u0))
  ee 108011192320000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 829908582400 (lb top bk l4 u4))
  ee 108011192320000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 3923863142400 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 108011192320000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 2043713945600 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 108011192320000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 108011192320000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 108011192320000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 2043713945600 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 108011192320000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 1233082777600 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 108011192320000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 1233082777600 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 108011192320000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 108011192320000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 108011192320000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  Nat.ble 108011192320000000000 s15)))))))))))))))

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

/-- a leaf: in the reflected half-space, or the leaf test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 1) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)) (Nat.add pos 1) (Nat.ble (Nat.add u4 1) l0)

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis); the position after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (splitAx ih pos (Nat.shiftRight w 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq (Nat.land w 1) 1))
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
    108011192320000000000 ≤ 10000000000 * (24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) + 32768 * (25326800 * lb top bk (l0) (u0) + 62369200 * lb top bk (l0 + l1) (u0 + u1) + 40126500 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 99999900 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 48244400 * lb top bk (l1) (u1) + 37630700 * lb top bk (l1 + l2) (u1 + u2) + 119746800 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 99999900 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 52857300 * lb top bk (l2) (u2) + 37630700 * lb top bk (l2 + l3) (u2 + u3) + 40126500 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 48244400 * lb top bk (l3) (u3) + 62369200 * lb top bk (l3 + l4) (u3 + u4) + 25326800 * lb top bk (l4) (u4)) := by
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
    calc (cN : ℝ) * (SC * 10000000000) = 108011192320000000000 := by norm_num [cN, SC]
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

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold leafStep at h
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  cases hs : Nat.ble (Nat.add u4 1) l0
  · rw [hs] at h
    cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
    · rw [hl] at h; exact absurd rfl h
    · exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 hl g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42)
  · right
    have hsk : u4 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u4 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits : ℕ) : ∀ fuel, WalkOK (walk top bk bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (splitAx (walk top bk bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 e : ℕ)
    (h : walk top bk bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 :=
  walk_sound hlb bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (h ▸ he)

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

end Zeta23Ext.Bridge.ThreePoint.PyrT8

end

/-! ###### certificate data `PyrT8`: pyramid table (494 blocks, 3628 finest cells, 6762 entries), 16037 leaves (half-space) ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrT8Data

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrT8

set_option maxRecDepth 100000

def TOP : ℕ := 7497405325609820960580801032216102383532393753305385486965402356498315787963785376799552397562623853702260735201149693511676577662584835040084951894272352869716230312993504509467414686500219761419741672674577961796161980608294197556465479455607246419104079064988516021714831321442021498294820367182374547522405222032063139952520693366923086917106452151441302481414143194755492310396130163736213135028026143959416853595066600507652395763513243873823047286497404427160960821558754763658183992077929444871596450043598381582744968759246348843399408587228065272706467653418479017902061776425015037645914587530941408862485117060037772806086618000159251519190253450699032062839655788832379733323151816286981932389506340188901059778789634632796217935381464700625572174254888506319378544673490644141095377650337120213700709375391851422955684902081791753651320217720514976676115188217141915884966535187264259559609694873995964626967824880035017634447343132511974701734213948873520734743299048594380979923681765141357757652253094190296664923289019298180129937766072136929198221040390965227021096661824179889783316243032743357797930318872322173567593937685024450620202976463222878470013552333079940755129226826276203503637232778252408400982688827973437747177103871824000191181811951296241842067750347492751721604574143720677374836688150090885642743019128078732423645264967132244161592288447723185681476581396313155544668832081231185502643816304829388183548528079656385770235904051940002303222845209025835664643093965894299885408739495172471613925685838749312897580831102261382618159603179540059376209766648517899078655218434278365583523959428095674452967283974020168622918591591930466191525113995761087541775812175721080919499159999749953607287005923967502172787810553554592658974990550664186325306910705224323656235916252967596395487810880434109220863600147605623280447860210827335583078449844993007102947542434408050883241520298409060721148708773598914184174345882537701285600724103036279832061132388618469698518501056596574397175902938699095277943139834789081923526056105340684948762419079380398826021962679285728344424173338415409622097471360288421689822009207509217384104088456388246402563983298273992568109331186347805897755207357901351504529574771952541433848126785997080953237692895951825191555515225781002813966690108312892005010527728694873798872242920172193978580646201075263629652546589337010249268817276212677754196034922633257868982045377169834839583074726707896661992094376848785704757133701377411324389027247139212870828321121663044767444931868053020891016026115721143261220695800766310371364284133214427648408380957177719250840313908436538036580781301076452610619338348689770415230132330894544067087447835669917448418518361709377023406789081767238706745428277340228277929277502674615000312548592939265779146303981813064110012604583227299765992541887653736254903275614438502210950996770982549011074510086317957906556359175909074726201665262393058668885584368784430530573078658492523078831212200564129699382461691927152866189665703380646882792310461704612953606492624989811815409514064425804321923165842516139498052852473690459711366327823130495604439582621771001463667155724729616971882090819247424867634136260855629745162951913636455919223133966784827941776765855766960485978729185670321871729686710833787622122262871291497172771747493572865588442944602822373854429979187755017980778209563386665660200812646996851039035106756070384960364499674704009122335651007831058639105557690578406694517837469765687375244648735646933739280563321301732194780351485389542906939547708250601677717131983243439103722111087908095801886445248298942638886537059468407480915791853489516849234559414675283355675824140965217104858714340088753717407440772418759103334431020455818309260684681215249911782381625810540317542480095758972488188518870563436526090510535791647803112375662909143303110432165276952089916485594919802922652978781431492147417610806938632597832849899518733194480452720882455757910647889516936699506009150570479599493391490510029468973684454216381557941277859774662956463712088978077919546603158758780766208324737476492952897978173452169777790666123492686411872191278830021878430296497230515394137275174743489358426303677912709864025847981535141137188245493163087043384751302154759650390669499559005654875437182965464377542749801045490629038295492873691856455566928054681605244340256833144173683926981866198735456012516772504577445216603779319500520384842282406185994609242342674382783698359910031031896247825038643301215903746222738602376492704575556192889139256492548288283448443729746800925579941446400930090336089365712254981397152331595906145719329338958354092222129791648694255294764355288962271972876533431092367729910241129860653033575223883747797297780764129892782075903603323592664068379794350972207697842042251186215853396387874175485934984427929245971412664283064867447974731148688114405007992846016315392
def BK_16 : ℕ := 102514058122
def BK_17 : ℕ := 91636865354
def BK_18 : ℕ := 80773004714
def BK_19 : ℕ := 70169019178
def BK_20 : ℕ := 60020123530
def BK_21 : ℕ := 50479647946
def BK_22 : ℕ := 41665041770
def BK_23 : ℕ := 33662019658
def BK_24 : ℕ := 26527728170
def BK_25 : ℕ := 20293431338
def BK_26 : ℕ := 14966998026
def BK_27 : ℕ := 10535347498
def BK_28 : ℕ := 6966931498
def BK_29 : ℕ := 4214282026
def BK_30 : ℕ := 2216621962
def BK_31 : ℕ := 1596447981934847164067170387900170765160466316732454750390305366105523511286815426556373511337029810576882746194485936677525991422878716855017167237725268468875612761113332057726356938094894440565010287918072473551424320199475289650373040256940862698738233195788677554580717439371325743910434019893464841908386150350748965704912499552107936857874631421245408320205660516213144576738009772486417697432163805469260267250791365819187970025624404155653014564873496094796651930909041257263789111661481299487832546444846590130750056293766215037640855062676768054198221556103179355866546145822925908451871817777701
def BK_32 : ℕ := 10441327398298883890489530599542712699871407769841437400584888324647807809737985694241640290352231238082453578766020965396602512445240517692464182422739474693027985884824821081705761750530836249304126153448055785453676161423640070540399882104243300661835542679594137002890985864983487074074127675037831903026067201875822583089316875237559400160312597309996721565315332673015910677962334750933661839714729942033295805348483390485558010397993974768404604481075301389854003080879580690593427959950537283635228822053260845269201470780055726788248120453791126729682395582184068655453383745655921429494538752581647741332762236040979247408566155065767449681063469322334018616265344950451513887178090988466278458255250069032766002665396443462857998828732638084846215533319222768533896344237573420779263838935336950821748051623808815904820939507656880465195996828071178864893655902258369599273490941958256110508072030956236896870688764908166018881581500728941009461731710819797677546569372997299192151503753580131556606010059717707852686047450592359105785393240588727252781136267102098814141219359983098270672608935376820683733982490990883795520256117957816232553311463115441247133831243597074142339441887777786668097261503529724821340842377130823137465580444980564740245972591893351624813315952185901557597395545255707965777246949086059568781038103668857778392912735838408608861879386646224411264816787398678917895687287282356133880664162268936238853157301982923814212123455498540898107923871611361873739894053783326017787972172929378747412806309722280369789737049888199379525877737891685564020175182424008077780517243837446223536382400184689538220690585448930085002425993088363923424303242394072801129364974523554273910253603490270985241542779568116513356499263186366758939596245800087805419455052222000244364825713287901818124773414632882182694444655088212187982484247661520986968253362903272808038199694448903816004614546227874374299326492928130503965885078149147410503891973764675782856478359332485259274289073226102680003153320056065834924159898426308795363843424027684680892782741706350628440591517112482322771207144825133215295356520057381078941247251392247449579832786581420707560692340589638209681210427345891871115598670495082361484122530545665957904890097728618247268365607788496912602814440879668873032263293336490835674739834935563726277516424791246023789459434672658020941812683145370699940018242700312038634690580504051048069176782550511019530548387
def BK_33 : ℕ := 356603370830383244811964281011393614855484665141604755915750891875099545844020853442760182574959867741781304968472465877978672282662282689078428155222669425120983949490629328828017860512007305121818116566010446402246958589343357757516056493732410319023039152329438766971145968571368246547481506443761134429160654974258161021786939041702695903712184255840992708948271109714013901651553581503079462405337276925778658206602587417651668328179371488306522871753871431515687271625038776372702902088070350984510548397514036423100106540537003725228931679475453019582806794763093700585203279718483161236610717328472747289361940232642065872763569871543628070295968179967521915847992511112180902423367774109412324928629237675947445098796687365258803279323671816893174963886936470964595413870303549911934719735497923702402261382818597320764354610991762493182859191133454138250682297632601792268566799263724204018352740278227013645578977316598623654918129199210343016660925717810113506103673737255356137423754117046096790021285277246708073377537773176225197129411911335246703571122776601614426496258031081223250175213420013489513487858119470189253153650348328948112136491593270680889642503086017103373904641237070188869080451200744748788936093164265958083229240810008286747982481942686078155283087409076925237903349767418288268162402909375045273903764632685940119947448424197360309284264631995480151454589637860620600395982831149954578209269988822982842942008291641956331551948931431625400368781265013003257626375902926083589409340278220309186846281355132417780920113086615765380290029221695781246491019636251588601171552203746729518525557248399112592723035860295521469767627618257905351839094979606811665754444283463230544745840425107441987519508801027067928715837822042302346078942356177144728889796835462308896397650602219648562235615663600698728807518849674357133642025353759387114284143592840100958851941531113657888850025031407744674262432323399735041058134857099070443051412183191892095802648956518721877724871427616690358690549753035915409684878215369530461861632767540025978936868989825273352293128091741560815017264279776228069475717453602240256892407361046049943364847546774548380883671671695206877945160577598284842190806298307035614737072018151835537579388419816669568144967273099298128528513772368535824753381820186167575858770404700887364175429709992025117261806406255773964182256442478248796218366701819303410219892260770872492276032252939295113871363
def BK_34 : ℕ := 499178130720553383655148863920692681930455770854390457107614013698766459546889983489108800348493348996993399211381307788806792756350740368054013220240524265484691152315077937603289658677275009812911315784010574993267905964809609723136237684152642132424319786657068187080121190020562717819536184638707247356557082794124456189819250709837561813952431765117967607009814348944811008584659407867226553321555227859952998486676101224621943902603228513697192020326684848520391013358075155140383173394341965623575798607879768076837064068951289176524411392179476535740421172740997506241813818795467464484666260909285
def BK_35 : ℕ := 8816497334492099961925882046448497351431576384902214695323778229497402718033485282336825022753501370101767439322839029651839518321619902425812514634185306304313118082354805670139865811849805395330559396800480114341245996480631054544707209115597280560726352495536990736437959991846771771306050489318
def BK_36 : ℕ := 10000171096117227904177779625505830446714140770180488655661951678120
def BK_37 : ℕ := 42412708529178540186970048073
def BK_38 : ℕ := 2694622346
def BK_39 : ℕ := 3788154666
def BK_40 : ℕ := 4906205610
def BK_41 : ℕ := 5989079466
def BK_42 : ℕ := 6985807114
def BK_43 : ℕ := 7854746378
def BK_44 : ℕ := 8563880458
def BK_45 : ℕ := 9090825962
def BK_46 : ℕ := 9422569322
def BK_47 : ℕ := 9554956490
def BK_48 : ℕ := 9400773898
def BK_49 : ℕ := 8982433834
def BK_50 : ℕ := 8416692234
def BK_51 : ℕ := 7730271658
def BK_52 : ℕ := 6952494250
def BK_53 : ℕ := 6114031018
def BK_54 : ℕ := 5245705450
def BK_55 : ℕ := 4377384970
def BK_56 : ℕ := 3536987786
def BK_57 : ℕ := 2749628042
def BK_58 : ℕ := 1543843083580086390466681300774808579455402417237793783645062319431728325509677364901164591294392124826309590075896324084892585593131027134051655
def BK_59 : ℕ := 1416436874
def BK_60 : ℕ := 53204483781413959469196437907833021992396164881199561105462046446910315351081164086563220195152492390948944967551004998537555721334089033504322552659040359337496579490145665669132011427146512480515771731289731742153898296878589703895179904161882618531455107792391092978776411926393114928712997809044856122525675765755417314564009302772793676737712901395112266295341354416135325192359936767363761766800627505419736290924542327487382110418500857238585159631511815908463038397922312330702383812139766583898842727188372840265779659189601606054766485114948059210382791142510888304875584179699458974034748916640446683733201602149359354463608495118231423931137092572847541490484907570309219040992072274797638488235081960080381257887823438172565216858184372719688055099205011479511043336425997941897646193913132049203788379432229458362132209491165193680465571666678547285230219989357285998941407681007453639991575872646721537391585334001751975019806935442149567462244348167837490618487596423908316358089848187657640936806698491197247909784907879260501079767982057281042851618950462625172135688415912208335778125321584314634241668366121472588185288129678767112693995332194822579985367037416563877488430321164442950911824293349505668
def BK_61 : ℕ := 29411605545069358108619048849560615086607357028625484664341111397063740397232005831196966345147662972154146373615016656306134721772097024211716152707220729600848334501286373975809235743312819151573852186921065094108396434599890972155016748116883849745345836582667287775093015496611490926033577116112021001127267938397444598520134795358844688193054268319965998307238305907228459141377593377731661851576774692556966014570835780269180841200333168060206777738151615022324354573477104231847917900336563960343363270956589719590827750955646323846167808528006152603664950109963346502062290383491034475673332271682603944760761756607125029846945057949279016420307782907463756496759348069269212294583667795160751281625874148986704849561766656644723732003008079222024511486360296078304561169596038908399522099139505576623984770320124767541166238108975466610250195715500351281773541720102923014324252594545219943589506457439466041901453338918897553914142154804459988036594442496970477697597670662515230730183905665712279926137670342701508485308007569823811509677231520388330856752547382746370892699878631521311137264842764444904280324527338941878631711886092262827385753010450172015426906092745145147681331696064703662023404501549368644
def BK_62 : ℕ := 13252099519148418739963084144303114982000381501030025111098535405168318773497428344434256895287360819298570536112945155186543468499994482365847085440804289313140719857598277016166761332384106982184715010389427538420321224437500341434234886939519586324210176245369241434770350586418644166415460441412146069415514193991348665577739176395770696079328655879641162495482695192900813970805708575740546515426448136092473464102379615941719019635888697193705249479572748606944902412519265434398970487025499728265678994705297211597293751131338529945214772572296008394379262017972655499561754338955662670958594596942070400021620527906380097777551718541499029066619216909209710443409691258309268048980542609182147175170095896276347339144172137754493573316655132753573339213015776752780718885311044212796412396595876815573127782312153740131004246555462318611147390409898381609941614778546733066598712506601150185195701399519858964237591969715828818470836267437257002006717553809096868025097388138644890940919911743246721826179648599690792757789182694155577207563649025693302393029322948993873301274822476370961239518449800104820286786268981816447397912988817231292813983353582941555888234619807525822785263428972896439903528988655711699638666310709868531835189490157866598350698433175770668909213528919448616869495464766791095730758037528678706571984257689924040978368544465615951935760021536745116449982727584781943508451587122768100827315998072378318567550702238458255816324920530722110980444801181363177235062613431571830192281693088698195641450928258987451451730448887658439599344122967158125948693697769805086294082906540467478166004969631788350208188123084284279982111692828118514808434071762055013040848530182485290005463224761493798304339489159851888690879624883851908933435556805967914925690204731402497462483679343553301785913663453719318765892328140146598607918979832784057753051540467607021691614310987106903252485000137393002000119620985073380330573987364442044276870247781109937829770920523166475000419303398770365669640336479929399722104726225466657827883225328356659553843213480039881555549571630065629637419100603397629441310985395264167777610912732693387933922089711398241808660074874480470919548141042555381923744459482007249868392373621309203842777927035834740053080377602346928257552380288337053546929200934478720028103246240862252778748912110233005858702404739556407968193597008768029135069969560591871835780863714525535291124720983399769606703971
def BK_63 : ℕ := 3396022062143911735592818672083945341554387404759269380196321471470497641731371145140906903473637929167152374954751081178335311120661944989606581227839409850363813880812375365244538410615597983168655430390379832248595141982196564477272946329271944289190452543082912844357808115016958766762614215105074839386305669936633987367185026497995008624303176786234150997508343014754251681126146035239812257039232848173671735332092664315060119980017538245696719084998854971008971370885853643896247622498233834378386783650600084708652394339257978246241290912910983322951205628734143328513878333081370247842216073336062511674065304197655232778271532361433068181252285314710138752401838971758066853827367616690157487454339067580050133906035766126883786668370593345718835799062583788789800742678786363194442606122991315733040138825252172000912830944604416051889380766873409172493315934525450810099055126525476378369280450067038594460341539623662404679295853091267532099626783846138594962436100164900001384110892128637422211484477116582883430118174135975238194156656635378628232455017529140064576234799357321135345357301007897654720376333022004852075897473470245922436685944658287889527040080991137751445603231034402161724206599549177554232347397118302565845887203752205609920895491728986140639261769821942667838016135110362129906039170754203773699420935367635939083282529609829330040051965295169814669033079736131483422100093877585549011798827364818502320230916739887770432745220920436334235141486345340859694741576792228200683611283335177883941238658008291186389327450437976756606499447578813477778969700787742430933286632601518558027829880133500987568342531095895229298354174271230567647084060835109968034485434636817153391138024054270558665237072756371889763957375378129008736755925669212934491575750919380959089672193952135899724151354092707632263970466279709598215949522111456735380050597641205832944916093153073252722541639891830385634107872563713333019560712486781247214242901942176867126646306555786613546062149781157492707882742807510000252903460325633278480849689482470290913011525814865189004403069738344580670734965467807600586580657239516332830096239509672158942152992397171232003924216710443515764981405267596928294687898121977343580416489113402154762443571286085050931569915996371827883837669641367685487023109077810713355700161388370213541232740093639602723244928881358967765047933878224807872035853411425492398927045366674326773960195244197373229839119297068449088737416093250268138073131877811837574730604790634555931034437094981054235301834265777568693069618699171190442498554023501966358609775584047437658365296223346231997807450722287376793639610293990061113134839313684996197821812608521992624478045018604043172707503078864219552417225502168915651766457917965848145705160007829717754316134021805584407384782753051271563494890715173206965855780862903001805921977420617896708275266541590758456907942976675076073071216591739420409839103711252528894193771758766635824639045551504158547743923314693560079839058396513589548799752046267930741992082390900346725946738573208662815959916142831783903100469422646244806783353048859936995775326395206819579498448251938700827926448940926921352441003717847450503963454280185176205581508696062948930849695210847198689058942715022139850205029032996743609961494958482303105882813234846346943117882782809571286770960069220537133646547656713861041298882744847121998171240546668347271483331347272793630656991176605941797043997874147063627940971483167686742047110010862891017776398744858237962140354917470488329812626738947654153621718688928859170834405163662530963993767522140534288273898998972017729381648756632091852903433723448349007541488320769710717605161956439966767488999524356750282841076567133683929634663238399331815873010968324141722112696065881264501859055594601038132877995128068536100893648800904420734660839728143661070855226330798558263788077396586492348076990150240606395564077942101773394890309475114521934366755442878848886088619628910464627074989719162660987191553454947600768380391985591378365298602726463594736148824058374271433645978336913928533128927424579076535198824380346109798155374603118073421818333326956558682080629415168567301261794815820474541814950495232002308938320684316593141578396864142649432194716307828658198303362883555519171398881873588389595611417783969525281129254543993144331281310926710464442365880215962202359734672882388193308564171062916947244732559974925399368746155835847963723708241981316546979252886153481670717652590159764006866531328306931815562978600307595673299882510816811168264815890051522299931429279389766396992232313648204386043872188862038302995613992310157828519185836840104243357435249301009606594932592399046473489846108177778080707627629407924059025279674012498126833260196270204500034107854749653697082737529520340864217969789949450628490031129016600095511811254432992450826218247275261071377484271780503040192377954
def BK_64 : ℕ := 2942287648078341682064402441285017354372058000036730975631326301874273744685092053708806644656963557784544831050208517731359965683136894468950758381494729297146461123081703707142873390303304076864796304011240804899346353785390707083208930919975044849972265912610475793044535460697709461071174363048931348345835721276660521934901768415493198343014520071332840053053110179474762682724961368026277763548443205468807550359009099223605941510838388595236293802480710646834406802540289626664541252198036613578044671134980839440517405380367043003173794532429357067128587001252209026265196721330806025755077189280579921086588635367968130718817921358592681712660161280468693219005510492994061605624444547202717837764646629336981442571069867099171831292927330815632589898249366820570453705020040456927976007218978054270481297035449682914387167191440864179462789801061094417131553191275310435404199777181984953935363269502807829119279176141419393136257504726188269617027242743140691731795752642878259857940162198531032153163222617604969499489949310427999998915264952934290828319328246928526201962588874545901453646257974170857433029680276783979399574433352365657649808680253472443907757504885108480435035332719349134130095118691096980259242769515051235394044553960804094951065116373572534647936658692317643067519166792644480285549676974514041347370732577871199784834608073489571498433464136010355229481525423627251451051947223718286354638998642108597077432093054091383721458489740299912462564122271641977244542562292191291729142956448687461686783504310629524193225248162340250018474748099382295418921031762758154047534598032892750072515795151106492401906439604540775936221573887038712174417433492659460534208327575916413208121211024841708603122005865609413674736592671963029726102368737332250790431899152988521220480439721243233659417010894862809075518039001951996218128902270817420088081150127777943161656388311551281135345315039863298128552089975202251559382533033840078001554302591701173353827142102338190966302983895925097852810530064633358040448249878852875607495166183583419484512818094753043060335320155432903433001342896180554617163181405042807396443878593980876184407439553500632967732348801064203413745066770052818005373350160268892554110354257873057112998755994628090080321700508687534044946945739005497055351997546629786436704261840454931825175638530035441970587225380850281229059943323205304354567340696667926700412853445723994607288692525780493664259
def BK_65 : ℕ := 3152002693793398241590268418339835894481435828340262047312604862610736036401601207734763504279465736133451629522687636163411552807634022220628072276755359759091358187167600393677684817359231158294146990211669803405558515666670289823853073658631064122276981875767874010853534758131012598891600717592492764740648576373940012382065142124680998752099843677466971464452888729495570644390518922796421002782467975595095165021531345166803332342227348955284826497590738820676524901996234138997422666504150008394758594056974919993125552112751470421604813375056283746399112805478293609444461861533315929769553143818773875789193465610631404744410178041589707723227863420640818375511600102961556084371332208749021305538322378712426472576138879479412134421844933281972473891707418605538424858237011289354602164737434265654606102965630604666721413980070906955712525239139835530793908847784159467240941319927453877401813008414748933202929452175235238544912002933230883265505179097941604998370329598621575524386326882409301514505014026726380319821149341148307780547222761000091362042383219002823227673462698613419724945851290479206655785295212575098483682904135822996160921219135184936811414344976346285439742616608400269139748705848603780
def BK_66 : ℕ := 11833599404893978412829604921568575936927784667146495883691721612236312636572422011489520143228222473342099680964602792879738243107476296632112372779712692060744600156203146486761958253091910062191448680264660022901203315505733674432565735364914949023895023567284649231552841868638862891308885540901596216749505158675401165928355521915313574436703094025942698713096189716295056425440810063950974180636485411268829120632786309678453203698540041461418293098909110435039488851309319749883130384335595084771038070290312667913227331380814484146831592944491293431131229071274079871359407392605143612466577723631622304597130703248723554234534674044988377938270449290296979566693455577433399924592875736859463464684265139104147395395591344971838006942646432017597552534532016298979007676813009248427238110917079746762593209594875143550287345244851518503711049482359568411314849824216275123525329772638034275474823550752112047679552794660784777813600354909313980132114556337005288643542097297003441880948179244490213879847064664916829754032020886520306694809064339717206814290574887229389237695594779247204277137850473927985200481870853513827548908051018483548277909394254925410943332414631265356423561657016211967439833403816092836
def BK_67 : ℕ := 771625676561413815454311917979898414828810304624731201208261782822340482641805690990668648607951116185253369846419831490751463403149835210664311994085895209626250273541169950094000941989328104049590842442767766215264043446263460460844037121914232871355074527097470584905999052961162609970478331480092955673371028540964730904733879817106401501686238651373227712117679270764299756249104568127448024881517976187146619093966960860926167525929526737118103575682112179921123198125703466479899708714056998823849682951312582128559155889850755765507842530079860049658425136781176943481685536414283963176231159035205
def BK_68 : ℕ := 1298484969263662200667813223815162904542419732929448438593513452039826528614324345521158079782210296990904421675115978497305411442381443582074805634170097659696972538061159344897752798554515673491061517300458265677095835059613583156981888690230986499550395957438738572953321731866729800077364247044717462761857161068408212739158357361999921566857385696392173091179518655987705437716057663086114153250146778379440163114668282958786874793958926680281615758557353650290382823463277531460733730832902983586745956330816388580481758617638928965453765358699339062615242083914804164328415002435199815086929134896261
def BK_69 : ℕ := 10489861617562598728054088718113510628001887252175555050108163095569893394379272673535617348776259192348834298209806605980786456913334217351086227407994149677351075356860433327676427646593745218744534813358521369347911463857700489734555226618258180432776502283102065499148399650541805699681192590406
def BK_70 : ℕ := 1034827644407382016289782905652886485972123730427850834225461175883958479697268006896204224774561219057613080729135557002521969822728850393067303
def BK_71 : ℕ := 1315480497183967230571488174221240034943956110301796757170083158195444358287080675697267676989323203616447506129749648095168752198498997226732359
def BK_72 : ℕ := 13363773437029698603683769520437555153239506585005323589198460657128
def BK_73 : ℕ := 15622946542926976108929125224416146335375383616969606769764255412232
def BK_74 : ℕ := 17664697114912662322614248913118241380167552013942554174488478204680
def BK_75 : ℕ := 2775171882
def BK_76 : ℕ := 59416784995744134850646936873
def BK_77 : ℕ := 3229804970
def BK_78 : ℕ := 3365296554
def BK_79 : ℕ := 3433727114
def BK_80 : ℕ := 3401165738
def BK_81 : ℕ := 3272246186
def BK_82 : ℕ := 3086926122
def BK_83 : ℕ := 2853445866
def BK_84 : ℕ := 16662636060641146468343830387624431840850778009886527399894336446440
def BK_85 : ℕ := 2281813386
def BK_86 : ℕ := 36920766316406437232675398761
def BK_87 : ℕ := 1232617393784282486697432046179350623816287496922418151411223573584858034979925266530864346234389516987521674261371416108464705534645050512033991
def BK_88 : ℕ := 24956768888417176688150167913
def BK_89 : ℕ := 10370755793106557416152083220758429120360431986877769496020421323023641601987836529590368659928604312241921975770032196442496060651265460812813988052296303194862236802960914366233061709800264048645830920039211642811199237936172743692117894453453787040083368137673870013299619082365415656698986501158
def BK_90 : ℕ := 4882555505813644232512934544054942642455594134402043318904345646536
def BK_91 : ℕ := 940320160872826103349038199801490498174109223621681901878409542247536216013102520270500775065499697052971604639247196001289134655987570796690689013440066462547330282807468476244615426803302939868284020546560899867809230094936978615262412145728035059962710614482627941355315017326843342403030601385524673125425157278906281091465508941289766548951412481882398191483148066872199241965928473743939048388059177920693743687745387389927489768132368771237243777848842446747027587083911681252297022858816929035751149278331736148452731417863304637417497737979652292397445335256240836344959594419410910004974752498309
def BK_92 : ℕ := 582277397421827268617741535430283932865321179540079950847685473752744048497884481499465374450235481308148148453756576928010881567864689889720283614989021253285187982903534838038628427061129227028244175494133824587810951818800505456632597243440874218137532507085774005329124601298767805568769573400060373214728624118933991008382755430489670978514044329086400762199070842870046147883514500171776713243598749668618139013153931585248603470993927871482758876992064165600814324281522109204286937045035218074432380950484352787559753597156466452012152405722767643492526119512702835674895627457688921958405079271045
def BK_93 : ℕ := 306432550794395501909172638881581970259468617495319580520344877928179704701571811449984413599994764215702738366750469576242152000814680412501927926474342148416714174374903616229797166439635039536898381294755968849024613516700860288362223230861151648643547533565888527025705214084750456312259809911255350803234480981627141668664004718628132147376553261286049682080190815619514357331212467739458256095417361240094726136257708016564784215781034541663865995868224284438670734145608650021355934538296497304851562003088419539028644185873443197472047286198588927160021374636301948022875350379192837904179024164901
def BK_94 : ℕ := 117797536630795566475694096632597665603545158409576726533091287674521773844178328037894101575921616776447275393327836115155914696960865453621716715102559711368283561524152942219498940590131415844349212521851273424842824484650834295743339048027125931297995318459140482806596443332133370066336717734229519795372647318003848447933081367629465088839452254770174630256728859269239642094738283999500758419456152102971463018715302055929397251200845639262017021834071035283069790651556235798766804365615367365919874991915145714669735185520095254569604721884380555015731391174617696285595174124797501029015418437253
def BK_95 : ℕ := 580562133027559983045505774805713265446196204749111096047273465543166319835474453900670385960195425792934961305447568351745474553211403169887211373733441783403039939358616307653140099076843184655549742948475855796273624180223439654138992083409575196938387584965948134501810451565243742970691694506930251848072011641790191515636303341308569522730519923698604478657166599269078365360706282577071670717149492701748050400322929942336711598034376211644564846836469942747607711887146303020114020110150709095928394436890260159668952445415556624801101659206887342293685398840623161884616358488165633144974374714434138131340383528357634917330151076773102179894057764071319616281291348668550269060867623027405793002517765996170140814848391045122808561982413070262394576308403376020899015057152398494536773533574355754117423295824001924845069668490595290261455618307546831883478952045848201126822017666832470014789282175502920180240602156862591488959786358975642385810261024861699049501765474682326282477167726405011795078837731987426538100143975223255419560711719170909345300867535557426020536002109152534391257917384679600129768987015429622403841074699279937058416813735113639473233665415032603722497816610472610030338623745587172
def BK_96 : ℕ := 153576382025365455781056679811458054687125633130370470958456447762256788065747178919458678879882499786131095969469250653736057353604000232693207006161393969560952474636771625788039993724441317663365105963887015115136338481586507230919695865479457381426036597550776514225774585398311208640930318131908567697098931744980322090730618835645927431297725553221888875378360027500177745327713570431826574956688284468912460779388864627530382524828364174362511125661352155963160914804442801459235344819459549242928827838332961213213510533196154221269407171815648680226204297981998215895310879742050446822239960050091524474678126015676623157420248931030187956891247290683737727552385281705382019025692738494436649370226055554057111168207353604237797494338985746404400025380287239056008416088113841162337804562061548433276740441587953375684040420444536164086859988998002676612426304228633966599198009834763404322606116641140456055118859495228113901435444104734748296027139918893971283081589571756960399317318914180230794963684236833355877163847098518441456452806664598118844509967856830445535132074333346435675051616519225613777920001744303123641825392409283274994042544410423252242105129816785760525466926328378327755497436830760964
def BK_97 : ℕ := 2358495732373725576534625397246246775572271079108172015949992540230060753313856738895597162155678468537373455156958348636705872805165382818271657005869384750467079786158173994678398946795212629886983787000012519501819680125126499235263057641120095054579729298702671746561667476418422834833135329828742101583078023950724134826554929190092857261533399821652457994239539460796303658747943739238834010352550367605304059259280022103839603968817882859207289757362644130310942085714339168891959671172682954503523381616952288432393209173715289493831412917567757061675998405605820023535536362598668892026611989841438278526839569138110655601065982621856148665197958692811770873866883426764002400531663486319998537941643502207161498016234125854115989719557923125841294585031822333516415355821069636465950697601953772763189782854002736119261763186683855785558909789130217385673648938758456836623831752125864922176662304640752124540027699456617695747781832680975668050453962331095519150473091073913458163649166234303236967031845863324296166179344823560952735246866606317535213900589219522760121688948306475378496701803443937258706513897339855836736335997859024817720575422852196693889120554104592947861718777822450729701311561987870276
def BK_98 : ℕ := 212962098433783628851469297286296832128498205899806575916872824525838024268830562049847643802563330120318790428857982019337565889750461721116754642413079328540996515657386634847289828353902523950244864864346136096520507700531752889888589705558117215491916317890909041310067124897124840886535091833029540837978984094808321388100893214192289527963580392098972641874826358123159715292727432277208909834223090507986901512082002071341783865679330509236289886084190122115339213715139770571660842569929304025331902463339898800767973074607354551693949891622384037609264829135343764102436741422615266381912959737701
def BK_99 : ℕ := 419341898560029239562431315193339942545330523832552202084427175096508451641147125008063750704368259769063648313501343966861381243541919426613608321144072772740150791496462759928036365616740282376000645129086333962096926997135199591963094314821971318992475768288791494100527354274127433900714843593565453884413761380262788306312450282768932024150878440916090562676700021927814942265315547663518756769189285472909234678072699230894960943939007885926700601234642886337753275375514647649630062539383034104737534748604894079906368982739886140964889146612290562466080104890659970576374094256568105046816722977381
def BK_100 : ℕ := 3720308707826075580673808429823791308122887152887782455255298829439751930676724333829840233130661107525279215255636714384983212676646264573130100860184310444211090173370944894309126320489241662665989217653767263779104646154914966341433182853159227953152880329198686218705544904909024594447378145030
def BK_101 : ℕ := 5371806377288569898981617294262811975689073612586451777211198726491911831374346063542539963826895752784285413269137364737458591143046813276358369520408844455448540656150869583799637864770598581956219569572090042883988577389240781546191768795491128308698160200785823454235139036929019353360804470566
def BK_102 : ℕ := 524486451428442529321081190657327726362417834157673040258419107461530204818375731515180146262236737420195337692871680705526681913814559384148167
def BK_103 : ℕ := 662147449734619726231232930822414961996873878352402924659903705237282775051767213554799156467205457118707964471490573669215816284505055204808839
def BK_104 : ℕ := 798608733857076574161502714201405411596334144221578758913549805572287089792771656008095546503955315473035191470486970359971752674743742029542567
def BK_105 : ℕ := 7843578889259091872066402934329852384707813276361081095305495721608
def BK_106 : ℕ := 8868958623457699679194562513469295370090365581903964310850433733000
def BK_107 : ℕ := 9756009916900374430381494796981532790124522726011471096746155001576
def BK_108 : ℕ := 30021346971383207582867987657
def BK_109 : ℕ := 31684745077621804714496480073
def BK_110 : ℕ := 32737394804127878582008909673
def BK_111 : ℕ := 1758368266
def BK_112 : ℕ := 32679814989775337829235694601
def BK_113 : ℕ := 31522266746406850736743422889
def BK_114 : ℕ := 29811446045769603021154775881
def BK_115 : ℕ := 27620947427739245318038848297
def BK_116 : ℕ := 25040157025714235776766098313
def BK_117 : ℕ := 7594598703542719559673443560266537764905241825185927384921334968936
def BK_118 : ℕ := 6549262405777218188719975242057782205354558618307303889913164881928
def BK_119 : ℕ := 5480906720520101267850561837145420439827564054290085140320827955368
def BK_120 : ℕ := 6906588552873852270467522244120047747100798129618278083574324866102386468116655509241892038729632117466313189043661638909073975275885876636017465064437184217414883586573481202196544957038714391501061641085249316044240208936226475605265132537552727459313528943556607244370305940862918192152864229702
def BK_121 : ℕ := 397926292341606684153745368939743105370697936990367101115962434435629039534822750763051835608474315029900618210328603818651731810553628786282407
def BK_122 : ℕ := 291404693109851042353078784149346044495170397826821454728037296909452351584333168376581291066754181870916803017608452314858846034801663343431815
def BK_123 : ℕ := 2660270206167335017350243785587903480701849341420655683103769747374410367741423240551653209832691345396042376551450521022679682541265160417601427281723820638880017740418241847063859432327578152138675159153456209231039191510746247052183607293313914498223932790521579450368240751905029257893960308198
def BK_124 : ℕ := 291917050594598503317143004334733520524698654106028385717177642904802458327531331168228735490266129167350650401381452244629248349378252608595055630366881099172658305247797351187524600982305990665107300358182808132666160157020715902675045634144198881904642709533251295427680124653128512873762684439099031759508970854904548702060620986951067224491130993573373347863039220923976993215443849072504055816916212045815255455586177691269442425493488833241248490515362961000588046635231214157098387706066625778363616987410987995828212022352803936405991566849270595896300889439547475161043932019678417935063468378821
def BK_125 : ℕ := 149013573259170195950844230208003626635425458012222607497544445286401785990853860503881089620280710405148198840543349622497310460383183716476203929453526766611803963060953417606658146681294988796449255671074253230032447761287266786159504451639059749829192069978528084241639924184827117301240549123291443314323229314897940750211287335526087142985678176703214585148890162395544562009313082109180064646253193052756037166984878753786956153607402604497393627521275082098409903428353489144006600140922816348095022398497500666873763612764228185523168716719868628823131471870989838391807549738402469675676271239493
def BK_126 : ℕ := 53127729738225709437788570341971348613836316949953138769833713687061107892424912093925004339005995358955578739302906547537479307885833233256375018099898689287233731153041128900888129815443252925190448887947161339084354000422227342402972988600130759641347746631703509681905298636101126586085739825011440853731203470683042957834037966658812426873633962042062258028695313160201293125270978629633188405454551212643688675951012555387771761901359340682976485352966454463010478160711286559360892082097730852466916655805729079108910252073811560142214772030691906186984756325728171899111698970543007007273913334661
def BK_127 : ℕ := 182786838895370704711178406576760826138822783616212949073904625881088426028010922259481433984924398922848982525152351404363407518945889855482308756782799254417392328891515342005101606910786328678069040244624399324713122355133473977849886152422409454583102291918973239749148677444511278103021187602877990627975129004237427529170780325530309160005269345725610100907629139538531427303494798726887285622040161532349808348446725398310638169368742854403559953083514256765773964514563933938661728777365728393505484158329381810209414004501958856963044467673195404354442976029442021159065901441284382967593271957972580811144441550738242207778624233044818725704018527662537054293475333619200450112471265354905279102132397915219480438513686672722460264560545784563557709522382448400029200244096287330000991164054837097667568919041951217898674347929572098058411580826912452589491106696326115122236075382843605073368223588940240911334224449710439087414828842365781366897614350193660937857285028077907272147113005894140787984861249412743545574054462761211843357956910921695263531553730051831172855014112419491418498837553741105342339473660733049685065209758439281092726284039496923557484380647112640783212431728624679572427266642232164
def BK_128 : ℕ := 186805246960638081644977830855617391266247533200046749531625944931860694332997883228287705424581302878792987439216932505468707037733037942943394354318494785062076288454023814575518704802081141713433925382451936105777564656062017486034519117156075943983602231545677034510885528694376926384884009427455328100829980826947653426135976646563559571823178892966214002573127907580234163446399794221625398389850294447128641611783554379556365066834143836387053997163731625211659381466718187457005699315865012127103214812025360126122315880446903661304116033731563618421241038191214309263768728484215528227691287855187945670625211443803419834080023432000705107543172768613954114724900328764875158440180769188205020189483938755521803928114831218186301153766159338103331184944633062946563794576529944732504423091934419356001522425870674946408160432845630405838576679217916855025494713631666277034903709460024514376206267007528326866763147452080872829563931052888687228527603415562141485239389563091382799134099965143779768893907288034120894660422805466010788644550046836838956588288084734414539276802986783797286275424314879001268261543371462290378766716731430559708071199052986229134478521374426563885381354721248364512314143652446212
def BK_129 : ℕ := 50250283242586463907209925299954500103442656453375762464211723807583884936977068228275858043788359341326203313849637856472335075788500318600404272038005791257363602051923224535668809405733538576772275778088031358172805908578167595057528672081477045387933555579982232153547218250196403746015304019494789788351261072028034547601350184794915041168744763769708262883294346900985022828661212845060831640306166057301878995837897615750978683594961035408844711993986222564129383247368156878014218357514179100092042041927822902045921490440781473639028093150150417701072420881141596507973121121670347190957279380837
def BK_130 : ℕ := 137060736649755850713854052984383174897734982003255371942144393284587097205894699924183765678569041371932228895035224762209976810961189881031532539526965694361591276045054372495290547206980904975000980131873969002196439150239374989486308565741413546499614235620801123930396833151451174357605870483926003203802274411805388864899267949116840168187188976912355385448054244119456741481846459621315976509307137396673125652653977427154063353981378564076221167801541685975763780615543133328701111058151055175107000002867009438429336305381682349951802529446087216802055164716701663106684697900905171805112241748229
def BK_131 : ℕ := 260575661413270285753285460733631004438981681703298115002269387537955177539826804033008965086568742009242394925407492725433796338311193479987583135057348850236854632790727774357039093491672224564648456376722878239693999568628910491152972249718713848448533850347964764517778268970345686216401250273427547471645347613391025113055570474585632603755744224995885349647207506748357518406583620800172675618732084369628925739408356430218593902859716231696095709794444117495269434512461383347932412965475616772595716357659181389961379938562709473844754149363908683198353126946009491314112706935461601335139038057061
def BK_132 : ℕ := 2273656603387261195427140576973181418963412802167517931737536183277855444563653958389918936796319421327434632989251669509767672562690742999348031801743432001479114742100246283582531765960040903971451007946255479222891649039124220285859525279220899910177972273738605452583476118898500790796740037990
def BK_133 : ℕ := 3251472721312786865157377417139542171862843455317180407038781030434823200506587024731119287381976886304603040920053612719346361395136282758760572237215229173047199166330192597811568713165476227144236105576829097174128939271192603363144979864476893844793180552778336372107846293660610717792321307174
def BK_134 : ℕ := 316010149299604461410444942343196693024509465149235428401940376479426293665515252493441251317849349992091051954966201631794503559644968361269063
def BK_135 : ℕ := 397720521385688177836485628705121783316785968483363869759304473959090422021746566464945810033156290914935061225012339421867154259822596813921031
def BK_136 : ℕ := 4035146168599075156618863231844579300492266158501356908560969447560
def BK_137 : ℕ := 4707336186494383600013767198506630350052130594638470394559436336328
def BK_138 : ℕ := 5323618218544087941532172226361877924537751937928920172307305501320
def BK_139 : ℕ := 5860109549794149262923428650146475240496546983160504949825377619048
def BK_140 : ℕ := 6296675246545080639735895883612888114198257207117134303400311580616
def BK_141 : ℕ := 6617577761056499486395845317533637256127998568595218449602229894376
def BK_142 : ℕ := 6811941135774782504701363275466829385029168124451077576886133073992
def BK_143 : ℕ := 20051910683041433283635130921
def BK_144 : ℕ := 19799042124991720824661172809
def BK_145 : ℕ := 19127728804843163160440346153
def BK_146 : ℕ := 18116940496145021225138781033
def BK_147 : ℕ := 901395466
def BK_148 : ℕ := 15257518075371084613717637417
def BK_149 : ℕ := 13522376597002544311824380585
def BK_150 : ℕ := 3991861082904984007658172616830184468486354911306157197833529699656
def BK_151 : ℕ := 387909966281779390585047617899820768516582666044422907295470433182854044658291827451489247636506126634748918267982528715622436492083772401879271
def BK_152 : ℕ := 313227624596126972488005946541292175577534581830759580022476338299380094455264478758424869994905983603739447288639063669542148654184221700502407
def BK_153 : ℕ := 242018316036025803959823604352400746928098671558352618487833812693481710091696829777565133909430733693919131502173345749355725415025667714107207
def BK_154 : ℕ := 176725986387462530305753924119678054906154529255310177613597206967678517085093230827696453597869425742454256459338361225609127771985621953680039
def BK_155 : ℕ := 119510474715807369437434258613699180797537404818937530819727121850115895059194413134140596056667285480207366099396088531946340563117523092696391
def BK_156 : ℕ := 968794607884100007649984347472519953891737343738494461315588058126341703583309747436247634329048232386284699471217880208988983169226680329380307708651416793775421392705688402083607446079533788784987709320804044207514243693937852429619390731042827351761229812070906008884752935964254136296660592006
def BK_157 : ℕ := 484531399464704440912727994200705930207570806960247285052309550471333045786834482471566422853812454322626603578419979126840356770564711773309995705855751443944860031394781755006334176222127319981812737352616537578046758053682245968819867662283487214662258403470581761442211071109787523221200218246
def BK_158 : ℕ := 163903084011394014824049781752334415056670717385492143931330952251155148409286262679704176675159158466802017402468077669879305920380593299644889952420770486180740109531321484490471161164219088124673791031940193739109567036290218859848493959844108056173553743627009894734174121713479780293089993190
def BK_159 : ℕ := 2311397879834785567377602911830306393364446058660393440542171599400384235020935547739577132839703587899688010748393048061028112160479379680137417240148818060255414535921619222613901603566048531774213239465744611768738336659360131791008178910391683737009924964184047961463474896817897208643220934461456989698559544205165937501839808840930033215461884442716046227816770630493785522043834555243341320258307081946325628067753284507046638296413232124150706050852247372502463652244708470946537543802334608167670183546778003373598632439267407390915051999355386716896774687338316731050209757488464250278239281605
def BK_160 : ℕ := 4992966998756124232235592863117817857055163748105034775178731653531301694222159282669565694013596387968202288718629145338804357275848963830008184070726049342625574857003040557367731199591772089933726656495079782737404672488503061055133636691287830068223950106344856035187355999560846528379538699272779786032688105071378032760453131652377025080570531894770523999608495798968957421229597721816520749169587485534691642471386881401092502564914401556597216191706975277475560741349893098045519584292131478696850635772134464773942926317822120423151576415864380398368070518478772263030580210877758548705013661701
def BK_161 : ℕ := 36491999904016517599340537476568264515783826201438255351487647074215235795010223629404737390191970039803884776013573035143007330706352783574560805835942843783894829347826401843497895677485961664584981694607650047279606555730481746238563301332090148467843311371762958550214783334940014810105104873023555799602626659269992093962400580180642903182074225649982869217896676984627929075142960390185080354704018532664964156680607950865133645667725681679269962332342341149033017978431063168936135896105224030250397206498691685541200966069324131408826523917691011017767685339146551563509018781291571450008061364933
def BK_162 : ℕ := 94908138474660139946407188648252522881122498459416707601320061608594792267460375529948551363847180421489178458890588924192241623420103285413588665015071934177018891233407244920098938731199319521077451780908856746567435444777572410818869755244614967660899984825168616838367482558310829243468695678175191955625263182638879716392953622569399420060695900371153096410224425485458160587783116705111796397550937812854761592175066447613344351061581589075769411470496118664430915317085441907197875499613241036231817251242068075252138693967750774947682313847371618870466332261631101946471655519099099872831566663941
def BK_163 : ℕ := 177000099877484154876251149994096063580359954715578361938930489345195982651732640256961061592347471090096173904252615661008172548622947916031053211220861397095171945024905961056691923603417141716235589871221540293729620707926730457481471015363552633283910166912583926938430588891808061938551350984998464384593083881432541288649543622465937183524811276652458318479293205147164330503329138278121270172132649863410421687155083539222981325494709528299553860808313973158941625956101623900851261620064783294179717257403845413658309354877197610135882460217274229537730907574599682490961037657382478596719332164997
def BK_164 : ℕ := 1530160869659978040140162906853464945005321033490020328075000804689312379982527051878969692678296780032155047695990999627989466001393086772958073614849889348395841239545228654238770367455960894045304724475041446720170543142951816007230047085922542131647999924078295543716768583240736601002278239558
def BK_165 : ℕ := 2176375604480799290723529952290736979958757100146785883849372453972595602726724979675669657628157478930037254524494543017590640382563316422639990674872062063170531489952200954620974664656002277042195174858927140862485065159967957929596043451733953228310020471083568319863863176317665440891649110694
def BK_166 : ℕ := 210981279108893246560932980688651324053067707331427266228813853273889030878369834738053649423602287140469271345811818966941677882920917325908135
def BK_167 : ℕ := 265076245362448266516478600178236444469192501627795383913188410994338035314299991670081587418814257968680995155601907124334127200527304466483687
def BK_168 : ℕ := 318967464184826168610741828990104649206855041520700594625957107889588548973342109409621036083667378169154810381640020555639762830130767773529159
def BK_169 : ℕ := 3136368244799571415906107806359725499008195526544638636104783679176
def BK_170 : ℕ := 3547561193291023475106592431730087318878211742005554399299309912968
def BK_171 : ℕ := 3906902670162666866196867109586529503051293730236732676734803458984
def BK_172 : ℕ := 4200830720919416555356449343053215436341081119175460388033894536392
def BK_173 : ℕ := 4418599148254871506110433357714372689374176559011144791520733443432
def BK_174 : ℕ := 13228413415194060711987510633
def BK_175 : ℕ := 13428267506600458174115593833
def BK_176 : ℕ := 13272124820036379684322308553
def BK_177 : ℕ := 12834741597502926290914158153
def BK_178 : ℕ := 12167964700641672963986365129
def BK_179 : ℕ := 11299497302134077619538409897
def BK_180 : ℕ := 10264132617641618411832887977
def BK_181 : ℕ := 9102278756575390531184048777
def BK_182 : ℕ := 7858303532643494393377209481
def BK_183 : ℕ := 6578767118194421315275969577
def BK_184 : ℕ := 1814803917156108638733692320020991358296633600247631379970563738440
def BK_185 : ℕ := 162542188041153711800092283348416599840425392681879069160371420566857050894989801867062983094636159971117778600306997716893438174273571183152807
def BK_186 : ℕ := 118446592152417087581072715471063706324289259375554580973989649083990967987121595369336027473719736016256125957635091120975594407221045201639335
def BK_187 : ℕ := 79794006550376818013131052000949969550707610755543897093617775251237180085214759048957806778898408857279388669091977182514229885033028510229767
def BK_188 : ℕ := 47845502236696702508116220659331025179996981598207420872895105892549358748416075112962257972776186163524273844605315004673566607279051466633255
def BK_189 : ℕ := 316479150560403509728670555787934877587401242077638317964108743391985353121603423305013195245283220851633119544867447015681031079970285687723118886879678914214586752410746771986818414200614424469128941815900917663158552043605178899758981652887690037968243000635953813439179401606859599527933872006
def BK_190 : ℕ := 102981305947656424550014985343142598911434488158760190650342407633375372035725272265349158231295431345203448993818195479060346899039048920137714607760605560328217015244667928969673928982449608532161329248458371765926602876293533106994092829189123835043813556766018364196330378449383649716933312102
def BK_191 : ℕ := 6192718262476912127264242691409312823985129431776704521144088211238153452878151768757532243668567619472820829336919086795582167085278384544456602728742361270235062578088384275077833935846264321484755195296817077722860227933929935891883827262481188269927173588845967501905878067217161379283317318
def BK_192 : ℕ := 4283177802677656068932247434763245038614015478250063298505940106757606607640289409483910315431507658712080702830116283997568031036709260436947085627686491016033147986694511892241866275863321638598887722424109099546880137056220067435053025144355833960836223449577514331135390745858912682985064398638152311710823836412580612705961226693494926755317624183409416196886150686662830557626078783604276180161273445478869122552467879225239275508136169418733857418228875187621800838272792114133694200291643875101842404302247961626872953931624459304715166836719150607899471348260615923417659324395656329933457719301
def BK_193 : ℕ := 27477996661654038537968974274529668897216484317370749846240876277861936727206862154706557105596734304679316155117208957648867336425499287001374663606991411394784026663014216329021693274410091055477040161268222861181110070342622071411841481521379421821195542444614425610088871504701984359299173794476093059492795436876979755080610028112483932213472824109330878220932941737576761977948718634382387626476684730057732150119226920276105350222746120631981949728583331954213307335763138388158454411931757363277327866618403601798958777105953151228869088490204776567439956984390092195652368390235344470289068654693
def BK_194 : ℕ := 69409153613858565098394343985559176127518293161898604896698521530676347034131738349803632738275307675706160185205639987275144236313604577571340358799291876702737606524610612237587887945799384289772356454433174182225731648190117396254104888437639602400476946332026641834592928392885276551846572273597497826929935416614519704838993827686535194019720606776323169516506006830224534089689169194600208371160174563478988492267364520582840568015991718599286896615301390371121357618019682911245500196263438760419278205988276066501938751928291039246684232975268658056638190374203791043168408506143992012426928741157
def BK_195 : ℕ := 699535167948470202514147871157049718392911689702632056199958678567414726289639972793563023302846931649487798003690517349492861169684254904485805683738695375786141161828379120834124348470678841468700862255347600409852345855946053234298829402194278174974915169648735437872495548674417151460013375014
def BK_196 : ℕ := 1099075578905181580655914750349753516579591753310747886311427941023354032497704263657998896393229189784241617418897992466100531810652333176325611684212251139985133948523420706371247242531866314389394489213325738472905841128816877281975022265717880172015529697180117720984099160209107972463639864038
def BK_197 : ℕ := 113802802095427561250198144452332095937155994909629717438987364879383399277909513566456253755282802415245462934602219583708628929889913461088743
def BK_198 : ℕ := 150772517646985642120045491648263065213762259417648645429763829013617010576760727394800438616193189632057373085887500491283399960206675815910183
def BK_199 : ℕ := 189223100230523905446256526632534144789812933209981762808713681466444176814864241052722046105398647873758359627443840652237013974041233755019783
def BK_200 : ℕ := 227579624068452285521729437753023314257222055485241718185960545107283024883120358949113027604848711625434612661302551431030080849415444881857991
def BK_201 : ℕ := 2238576177482679030203060612005541310344916340844809245167429119624
def BK_202 : ℕ := 2532416650113643546644970917760653889255654569113177625350693918248
def BK_203 : ℕ := 2789880062759855255027511962637505703919026643077838338453085992968
def BK_204 : ℕ := 3001215314499122620222463053221783718208928915241010238494169733128
def BK_205 : ℕ := 3158625943673276683847740555204206106882596142215170260889120809064
def BK_206 : ℕ := 9469239098477669920670884937
def BK_207 : ℕ := 9618706720083155233574337033
def BK_208 : ℕ := 9513382009536077585377478921
def BK_209 : ℕ := 9206094080669852137601047113
def BK_210 : ℕ := 8733463114690291905611704009
def BK_211 : ℕ := 2771794979431136802655555030909190473334257737172547711770895178824
def BK_212 : ℕ := 7375122209566886373222551273
def BK_213 : ℕ := 6542873591091213097303810921
def BK_214 : ℕ := 5650000412282190841916789289
def BK_215 : ℕ := 4730061580262171409585315209
def BK_216 : ℕ := 1303614026284183312095657948412743062014994971381756624920282982664
def BK_217 : ℕ := 1005446672101468789436645480959423923413103139020740418819307870984
def BK_218 : ℕ := 731563968250421251027115631178896000346130537124367095929878238568
def BK_219 : ℕ := 57004670294955481202615485345776061684613686822720382528273147056106449528364410966967374740920652035955107226929159379942131190547428703778887
def BK_220 : ℕ := 33999561788575214220301607856784556940811646726744465931013979202359937996041239951999223748891019990524225012816317858257467524674254038221799
def BK_221 : ℕ := 16574504649379116899434942032648290066256904931438894177875978398368313968749874837397365172964448323188660250600740680302666779489859113055335
def BK_222 : ℕ := 5235611217993324735934910942438511202450335754728245943144723713514106317282043623969352784367771967316358630463978975557854581208503502629319
def BK_223 : ℕ := 3340225869200153991311399627427417656070863853224584289978196082482080100022926125524099634697027814583303439646341406638280643530996212370138926029533941186308050338002047002041726509770047721185010399425352574695011264059707249150506000290138932378790807535404173341829951925880529067358632678
def BK_224 : ℕ := 18326491795751956977276574654927143042744294631722762117544765051371115082378860673132335654958563159670328719161709655058094660402860821649305007755210118516308128362637105098633492333338248070734849052850726791759084228505781527048933425719887704034112115638206213102357769904868767284133363718
def BK_225 : ℕ := 114458323276040611565268093966672877540697213082633868953865884812767492311693663118846066065420306045725496936617423493936773392728982053222473573830725435896682524720130279167793036236509263576800097350722824662438810298415676356677429806861074999005608745241780098432760781127250021684846157862
def BK_226 : ℕ := 287523873555991738135354226704962179406642635867815860811645873189933635074851245290519333627995326670258101563924018711068487351133556210534201963988663656543005955319136561420762150487169205860126301531662103771144270359507920041691692000987947357605960352613497340839700489006131231507045465542
def BK_227 : ℕ := 528837183236516833177241877750642768371508256436386834300374839436942250386190546521065562592431978760346210132726113671451554249581649024602430080117911022830188312373508844877691619804223810551690700298891316749497450715855145106114339075224710770543896636413824552049828861484623379536153073382
def BK_228 : ℕ := 827276744040224990688205392910742347454888815953959949988510253891855421521707470882436676536991076436845769707343715084906612317097811809156270263363478029207065466786903459205216693603342819637355761073637234541658319938584945338740019537869931569146164126614822136619677231833297068949480329318
def BK_229 : ℕ := 1169749843533545404319073597439431691019679932444817783585312798888320838118737870114075246372034697995518980011208259947862965578037589298760012842666709057382211996613732198165854810442397117588020942218389118988604135268961934712786176908023493995715815007960453356642443439301988955102330685670
def BK_230 : ℕ := 113087662567281880580528451515947132429796624711724825967224110312747489853113189926198940299153819572833978023908145177825988347588124864990919
def BK_231 : ℕ := 141821074281647143073699577160709380660820200428399534795346822138131252638298620828241374776448505477349704263708273796334392003365795139728359
def BK_232 : ℕ := 170512015355698349340983855234677609580683191561174678085868692495646840177707815463951984167654312548802382965653592364234452443981826061313031
def BK_233 : ℕ := 1677703779627338816977596610655383651302429399804893326092562976424
def BK_234 : ℕ := 1898142335387844957808380517378411417667209080973702406262132131816
def BK_235 : ℕ := 2091659255485318467754050484947610573183638386926995905852156845672
def BK_236 : ℕ := 2250908221781388844140005694125704377444564327038658913561066455368
def BK_237 : ℕ := 2369977510077017878410795051455963899181554017594121835400452482600
def BK_238 : ℕ := 7112066916533343717211275977
def BK_239 : ℕ := 7227859933032096998901756969
def BK_240 : ℕ := 7152303840200306341436997449
def BK_241 : ℕ := 6924699942787899624576252489
def BK_242 : ℕ := 6572282128315477734492763881
def BK_243 : ℕ := 329011754
def BK_244 : ℕ := 5554498814247018514818962153
def BK_245 : ℕ := 4929080993329702465774108041
def BK_246 : ℕ := 4257106541835714491108648297
def BK_247 : ℕ := 3563910955951414152226144137
def BK_248 : ℕ := 2875239987451571966946465737
def BK_249 : ℕ := 2216269162358132701976412489
def BK_250 : ℕ := 549800996478410268285532031088776874191603251149355412961086701064
def BK_251 : ℕ := 368530149484685466313268712146327743880492716131160958409264584936
def BK_252 : ℕ := 25386092614993926689977478210624373298799220187491562151133701642738937205182417156301708317516319053622102283709105885513060865778097352667271
def BK_253 : ℕ := 12270177352410653007962514273604874295188737449794496220050405124232532316400220885448038073477205261065553194264131154809451529213638183327655
def BK_254 : ℕ := 3785771477464825790694348753885162064981194714053786624155528019728048662340817409921623806605739189371724791782827843519390712645233952127463
def BK_255 : ℕ := 145925957076982663446580385741313614754696277395254840011244554352416498215074492451843935455051912883498512179207614841496988830976960565319
def BK_256 : ℕ := 15553209315145770869405634357884493295332132025578293710578896891948353768264365476025406138223259320797107854951262265499364992219474186005581169742077353219256168080018223056233319696285345322289231572876798262171548892324896145714210097300460298731455467909421515627311995017364056159939461126
def BK_257 : ℕ := 91417282447664268858068982802415907611024278122509624008954927922095504492005963153413037982321498575913475267022781457309612693350387484667335635931929919388086526125106929280718903403582722368883823024668947714084349532331109756980651487785602353656519787556678993449105946989206996229992279014
def BK_258 : ℕ := 226301160197380404356022486741422132028834978545931543320449323048573350245207027678140109491800487851563954500352267151057190378245344503530235086652041834632617230924244046325391624359480117638369161840585395573078806853395537784514958361089957627597147400644395186564650933105613034913825142854
def BK_259 : ℕ := 413654744146944842357096767450329822328586782108677625640861979206503410075280972898707843503938385901728162581127047855415306029260671421558440628776566792029214052236013936653738790591367944761491363431920209441567486877114047073967685179029866257557805935508443471607045608432490150513970668070
def BK_260 : ℕ := 645034382384891585618897720811913343685769039829008875489971950165899850780426738241643027835952375534782146692170773872560180090229877259136699433564472184216804636310114779425708273905658040876500368231315280757836938853533646274940653845085915123935548572043818021895558192764640361834987943174
def BK_261 : ℕ := 66544911173118384824545516492862046800486387921836834321166683983277066923000738385398402332819353893976496030475903290497621724372512285495239
def BK_262 : ℕ := 87948253201299909459735654916059063987003976482297386017165849539895328453930475592400461588257492436083590742966138487108216747316909389349895
def BK_263 : ℕ := 110233919293909788485092490267291559313096471860711469263493045628443486110987341377034173621701111251461128166224635295843309211601935711350567
def BK_264 : ℕ := 1118436712876510276408588175036601326389831259787260391646061168840
def BK_265 : ℕ := 1304016564235850974124093502246935954217329335279368823930879070472
def BK_266 : ℕ := 1475496940324736574515029937386019492797314888536855381797954779496
def BK_267 : ℕ := 1626252636452356935160095806713255240414433162358153264080823232744
def BK_268 : ℕ := 5042379419600334549446573385
def BK_269 : ℕ := 5339178382240974993164824841
def BK_270 : ℕ := 5537163597093145431223632105
def BK_271 : ℕ := 5629420929328037779176000585
def BK_272 : ℕ := 5572710620536776469831066473
def BK_273 : ℕ := 5397406341635125263159304521
def BK_274 : ℕ := 5124549777089904008070360489
def BK_275 : ℕ := 4765203070389400748945682185
def BK_276 : ℕ := 233558570
def BK_277 : ℕ := 207307466
def BK_278 : ℕ := 3322432745774500710786547849
def BK_279 : ℕ := 2781372328241618625421423241
def BK_280 : ℕ := 2243430443473238840290818281
def BK_281 : ℕ := 1728385542895914170891743209
def BK_282 : ℕ := 428207610249101481051890934396267776730994097289076933232314870344
def BK_283 : ℕ := 286524284587035238316549891106158430769302862936556358054935298184
def BK_284 : ℕ := 169641235502039128881408226801844520815935014176555054648740569096
def BK_285 : ℕ := 9442414202163326347759254091184533419114273632288688385268965461165321315083820164121584844447716600001395295885813463568007241757559823415911
def BK_286 : ℕ := 24654045217868150608086921889373776602565265015797330389734518344
def BK_287 : ℕ := 91081614271530584322192826188298412986052426597658969084992405399758690887681735718533190891493468997097069756253286750312853480815515003271
def BK_288 : ℕ := 825177096464094283735787363753066249244092395086036746548529524384010652520542086006492633794353922386882084632319221354439592853985430601735
def BK_289 : ℕ := 5169044419829630246492429731440274682096012050397656128822080044458184940359099048457012842959725954011306130712942339063301247730219730108487
def BK_290 : ℕ := 13013715922814370768317946983984652123772976465431075115454966752728366872200921863843592419465571079181822688883476242644771541625400024971239
def BK_291 : ℕ := 23985747683501679426375654138073977928066162733446162875913063452354462471395123547581049397801051604173914847224511624205249786634553388603303
def BK_292 : ℕ := 37597750726817485490434653684310950428569671235065601411505409386945054313012789711956386857666822761157953943007664290119276991465631623182055
def BK_293 : ℕ := 53268463402745029052311672377511739727214890698819473935840152357640213920674541480260676045548056292029203000855647482849694351900335796933799
def BK_294 : ℕ := 587627916294315901320550617392304844731218918069431884005614538152
def BK_295 : ℕ := 740568646426517813544252108659046640722014329416737680371848603144
def BK_296 : ℕ := 894257004484344002646736210372999687385329449773532629647076231496
def BK_297 : ℕ := 1042602092676859779227872505047364448751266792473481409042067341640
def BK_298 : ℕ := 1179800855990362035244795414442581461390111067772328227828141973256
def BK_299 : ℕ := 3726128376624259089317737929
def BK_300 : ℕ := 4034763950853541184354158377
def BK_301 : ℕ := 4273314884095511081801475657
def BK_302 : ℕ := 4433008200014234781688093673
def BK_303 : ℕ := 241341514
def BK_304 : ℕ := 4464136859310039084814869961
def BK_305 : ℕ := 4324989379390511512391617577
def BK_306 : ℕ := 221501706
def BK_307 : ℕ := 3820451153964145440045151241
def BK_308 : ℕ := 187406026
def BK_309 : ℕ := 166368394
def BK_310 : ℕ := 143717706
def BK_311 : ℕ := 120311498
def BK_312 : ℕ := 1799114196604706588938219849
def BK_313 : ℕ := 1385498644553970138083888841
def BK_314 : ℕ := 1005129733140279007010319497
def BK_315 : ℕ := 671609648725080986125830889
def BK_316 : ℕ := 396586698537137289971633289
def BK_317 : ℕ := 189333249168008880297123049
def BK_318 : ℕ := 56422244467892621627272169
def BK_319 : ℕ := 1512337870587490486796361
def BK_320 : ℕ := 3627367754654246229770249
def BK_321 : ℕ := 65917152557009671271276073
def BK_322 : ℕ := 202113153425281651497730217
def BK_323 : ℕ := 15945514
def BK_324 : ℕ := 28547786
def BK_325 : ℕ := 976153292314400527636202441
def BK_326 : ℕ := 1319149395366080513699904521
def BK_327 : ℕ := 1682365491112149102559235593
def BK_328 : ℕ := 2051217140962731513206037001
def BK_329 : ℕ := 2411086849762499072397622569
def BK_330 : ℕ := 2747880124444158369581287625
def BK_331 : ℕ := 3048558511145332986324563657
def BK_332 : ℕ := 3301622457181554840160425161
def BK_333 : ℕ := 183602346
def BK_334 : ℕ := 192468234
def BK_335 : ℕ := 3691495131162653055610716617
def BK_336 : ℕ := 197264362
def BK_337 : ℕ := 191163370
def BK_338 : ℕ := 181593546
def BK_339 : ℕ := 168939210
def BK_340 : ℕ := 153698250
def BK_341 : ℕ := 136461674
def BK_342 : ℕ := 117890058
def BK_343 : ℕ := 98687530
def BK_344 : ℕ := 79574282
def BK_345 : ℕ := 61259018
def BK_346 : ℕ := 44412010
def BK_347 : ℕ := 29639882
def BK_348 : ℕ := 17463242
def BK_349 : ℕ := 8297834
def BK_350 : ℕ := 2439754
def BK_351 : ℕ := 55594
def BK_352 : ℕ := 10
def BK_353 : ℕ := 1174794
def BK_354 : ℕ := 5690666
def BK_355 : ℕ := 13373002
def BK_356 : ℕ := 23873386
def BK_357 : ℕ := 36739882
def BK_358 : ℕ := 51435210
def BK_359 : ℕ := 67358474
def BK_360 : ℕ := 83868618
def BK_361 : ℕ := 100309354
def BK_362 : ℕ := 116034474
def BK_363 : ℕ := 130432362
def BK_364 : ℕ := 142948970
def BK_365 : ℕ := 153108298
def BK_366 : ℕ := 160529770
def BK_367 : ℕ := 164941770
def BK_368 : ℕ := 164593994
def BK_369 : ℕ := 159534634
def BK_370 : ℕ := 151576170
def BK_371 : ℕ := 141037162
def BK_372 : ℕ := 128331402
def BK_373 : ℕ := 113951306
def BK_374 : ℕ := 98448138
def BK_375 : ℕ := 82410346
def BK_376 : ℕ := 66440746
def BK_377 : ℕ := 51133226
def BK_378 : ℕ := 37050378
def BK_379 : ℕ := 24702090
def BK_380 : ℕ := 14526762
def BK_381 : ℕ := 6875370
def BK_382 : ℕ := 1998730
def BK_383 : ℕ := 39242
def BK_384 : ℕ := 10
def BK_385 : ℕ := 1024074
def BK_386 : ℕ := 4866474
def BK_387 : ℕ := 11375050
def BK_388 : ℕ := 20258666
def BK_389 : ℕ := 31138442
def BK_390 : ℕ := 43563210
def BK_391 : ℕ := 57027402
def BK_392 : ℕ := 70991050
def BK_393 : ℕ := 84900618
def BK_394 : ℕ := 98210410
def BK_395 : ℕ := 110403178
def BK_396 : ℕ := 121009802
def BK_397 : ℕ := 129626570
def BK_398 : ℕ := 135929930
def BK_399 : ℕ := 139688202
def BK_400 : ℕ := 139416938
def BK_401 : ℕ := 135153706
def BK_402 : ℕ := 128431466
def BK_403 : ℕ := 119518410
def BK_404 : ℕ := 108764042
def BK_405 : ℕ := 96584810
def BK_406 : ℕ := 83447786
def BK_407 : ℕ := 69852042
def BK_408 : ℕ := 56309546
def BK_409 : ℕ := 43325226
def BK_410 : ℕ := 31377962
def BK_411 : ℕ := 20902314
def BK_412 : ℕ := 12272586
def BK_413 : ℕ := 5788906
def BK_414 : ℕ := 1666538
def BK_415 : ℕ := 28490
def BK_416 : ℕ := 10
def BK_417 : ℕ := 899690
def BK_418 : ℕ := 4208330
def BK_419 : ℕ := 9792810
def BK_420 : ℕ := 17406186
def BK_421 : ℕ := 26726282
def BK_422 : ℕ := 37368842
def BK_423 : ℕ := 48902730
def BK_424 : ℕ := 60866794
def BK_425 : ℕ := 72787914
def BK_426 : ℕ := 84199082
def BK_427 : ℕ := 94657258
def BK_428 : ℕ := 103760074
def BK_429 : ℕ := 111160714
def BK_430 : ℕ := 116580874
def BK_431 : ℕ := 119820554
def BK_432 : ℕ := 119604938
def BK_433 : ℕ := 115963786
def BK_434 : ℕ := 110210570
def BK_435 : ℕ := 102574282
def BK_436 : ℕ := 93353898
def BK_437 : ℕ := 82906282
def BK_438 : ℕ := 71632170
def BK_439 : ℕ := 59960266
def BK_440 : ℕ := 48330698
def BK_441 : ℕ := 37178090
def BK_442 : ℕ := 26914922
def BK_443 : ℕ := 17916074
def BK_444 : ℕ := 10504746
def BK_445 : ℕ := 4940554
def BK_446 : ℕ := 1410250
def BK_447 : ℕ := 21194
def BK_448 : ℕ := 10
def BK_449 : ℕ := 796138
def BK_450 : ℕ := 3674698
def BK_451 : ℕ := 8518666
def BK_452 : ℕ := 15115946
def BK_453 : ℕ := 23189258
def BK_454 : ℕ := 32407338
def BK_455 : ℕ := 42398154
def BK_456 : ℕ := 52763402
def BK_457 : ℕ := 63093994
def BK_458 : ℕ := 72985738
def BK_459 : ℕ := 82054858
def BK_460 : ℕ := 89952458
def BK_461 : ℕ := 96377450
def BK_462 : ℕ := 101087818
def BK_463 : ℕ := 103909258
def BK_464 : ℕ := 103735018
def BK_465 : ℕ := 100589162
def BK_466 : ℕ := 95609642
def BK_467 : ℕ := 88994154
def BK_468 : ℕ := 81001450
def BK_469 : ℕ := 71940714
def BK_470 : ℕ := 62159562
def BK_471 : ℕ := 52030154
def BK_472 : ℕ := 41934986
def BK_473 : ℕ := 32252074
def BK_474 : ℕ := 23340426
def BK_475 : ℕ := 15526730
def BK_476 : ℕ := 9092842
def BK_477 : ℕ := 4265610
def BK_478 : ℕ := 1208554
def BK_479 : ℕ := 16074
def BK_480 : ℕ := 10
def BK_481 : ℕ := 709098
def BK_482 : ℕ := 3236138
def BK_483 : ℕ := 7477610
def BK_484 : ℕ := 13249418
def BK_485 : ℕ := 20310346
def BK_486 : ℕ := 28371978
def BK_487 : ℕ := 37109994
def BK_488 : ℕ := 46176810
def BK_489 : ℕ := 55215210
def BK_490 : ℕ := 63872042
def BK_491 : ℕ := 71811594
def BK_492 : ℕ := 78728458
def BK_493 : ℕ := 84358762
def BK_494 : ℕ := 88490186
def BK_495 : ℕ := 90969418
def BK_496 : ℕ := 90826602
def BK_497 : ℕ := 88081514
def BK_498 : ℕ := 83729482
def BK_499 : ℕ := 77942986
def BK_500 : ℕ := 70948074
def BK_501 : ℕ := 63015306
def BK_502 : ℕ := 54449002
def BK_503 : ℕ := 45575306
def BK_504 : ℕ := 36729738
def BK_505 : ℕ := 28243946
def BK_506 : ℕ := 20433418
def BK_507 : ℕ := 13585194
def BK_508 : ℕ := 7947434
def BK_509 : ℕ := 3719914
def BKs1_3 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_17 (Nat.beq j 17)) (Bool.rec (motive := fun _ => ℕ) 0 BK_18 (Nat.beq j 18)) (Nat.ble 18 j)
def BKs0_3 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_16 (Nat.beq j 16)) (BKs1_3 j) (Nat.ble 17 j)
def BKs3_5 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_19 (Nat.beq j 19)) (Bool.rec (motive := fun _ => ℕ) 0 BK_20 (Nat.beq j 20)) (Nat.ble 20 j)
def BKs5_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_21 (Nat.beq j 21)) (Bool.rec (motive := fun _ => ℕ) 0 BK_22 (Nat.beq j 22)) (Nat.ble 22 j)
def BKs3_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs3_5 j) (BKs5_7 j) (Nat.ble 21 j)
def BKs0_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_3 j) (BKs3_7 j) (Nat.ble 19 j)
def BKs7_9 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_23 (Nat.beq j 23)) (Bool.rec (motive := fun _ => ℕ) 0 BK_24 (Nat.beq j 24)) (Nat.ble 24 j)
def BKs9_11 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_25 (Nat.beq j 25)) (Bool.rec (motive := fun _ => ℕ) 0 BK_26 (Nat.beq j 26)) (Nat.ble 26 j)
def BKs7_11 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs7_9 j) (BKs9_11 j) (Nat.ble 25 j)
def BKs11_13 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_27 (Nat.beq j 27)) (Bool.rec (motive := fun _ => ℕ) 0 BK_28 (Nat.beq j 28)) (Nat.ble 28 j)
def BKs13_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_29 (Nat.beq j 29)) (Bool.rec (motive := fun _ => ℕ) 0 BK_30 (Nat.beq j 30)) (Nat.ble 30 j)
def BKs11_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs11_13 j) (BKs13_15 j) (Nat.ble 29 j)
def BKs7_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs7_11 j) (BKs11_15 j) (Nat.ble 27 j)
def BKs0_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_7 j) (BKs7_15 j) (Nat.ble 23 j)
def BKs16_18 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_32 (Nat.beq j 32)) (Bool.rec (motive := fun _ => ℕ) 0 BK_33 (Nat.beq j 33)) (Nat.ble 33 j)
def BKs15_18 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_31 (Nat.beq j 31)) (BKs16_18 j) (Nat.ble 32 j)
def BKs18_20 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_34 (Nat.beq j 34)) (Bool.rec (motive := fun _ => ℕ) 0 BK_35 (Nat.beq j 35)) (Nat.ble 35 j)
def BKs20_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_36 (Nat.beq j 36)) (Bool.rec (motive := fun _ => ℕ) 0 BK_37 (Nat.beq j 37)) (Nat.ble 37 j)
def BKs18_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs18_20 j) (BKs20_22 j) (Nat.ble 36 j)
def BKs15_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_18 j) (BKs18_22 j) (Nat.ble 34 j)
def BKs22_24 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_38 (Nat.beq j 38)) (Bool.rec (motive := fun _ => ℕ) 0 BK_39 (Nat.beq j 39)) (Nat.ble 39 j)
def BKs24_26 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_40 (Nat.beq j 40)) (Bool.rec (motive := fun _ => ℕ) 0 BK_41 (Nat.beq j 41)) (Nat.ble 41 j)
def BKs22_26 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs22_24 j) (BKs24_26 j) (Nat.ble 40 j)
def BKs26_28 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_42 (Nat.beq j 42)) (Bool.rec (motive := fun _ => ℕ) 0 BK_43 (Nat.beq j 43)) (Nat.ble 43 j)
def BKs28_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_44 (Nat.beq j 44)) (Bool.rec (motive := fun _ => ℕ) 0 BK_45 (Nat.beq j 45)) (Nat.ble 45 j)
def BKs26_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs26_28 j) (BKs28_30 j) (Nat.ble 44 j)
def BKs22_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs22_26 j) (BKs26_30 j) (Nat.ble 42 j)
def BKs15_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_22 j) (BKs22_30 j) (Nat.ble 38 j)
def BKs0_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_15 j) (BKs15_30 j) (Nat.ble 31 j)
def BKs31_33 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_47 (Nat.beq j 47)) (Bool.rec (motive := fun _ => ℕ) 0 BK_48 (Nat.beq j 48)) (Nat.ble 48 j)
def BKs30_33 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_46 (Nat.beq j 46)) (BKs31_33 j) (Nat.ble 47 j)
def BKs33_35 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_49 (Nat.beq j 49)) (Bool.rec (motive := fun _ => ℕ) 0 BK_50 (Nat.beq j 50)) (Nat.ble 50 j)
def BKs35_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_51 (Nat.beq j 51)) (Bool.rec (motive := fun _ => ℕ) 0 BK_52 (Nat.beq j 52)) (Nat.ble 52 j)
def BKs33_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs33_35 j) (BKs35_37 j) (Nat.ble 51 j)
def BKs30_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_33 j) (BKs33_37 j) (Nat.ble 49 j)
def BKs37_39 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_53 (Nat.beq j 53)) (Bool.rec (motive := fun _ => ℕ) 0 BK_54 (Nat.beq j 54)) (Nat.ble 54 j)
def BKs39_41 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_55 (Nat.beq j 55)) (Bool.rec (motive := fun _ => ℕ) 0 BK_56 (Nat.beq j 56)) (Nat.ble 56 j)
def BKs37_41 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs37_39 j) (BKs39_41 j) (Nat.ble 55 j)
def BKs41_43 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_57 (Nat.beq j 57)) (Bool.rec (motive := fun _ => ℕ) 0 BK_58 (Nat.beq j 58)) (Nat.ble 58 j)
def BKs43_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_59 (Nat.beq j 59)) (Bool.rec (motive := fun _ => ℕ) 0 BK_60 (Nat.beq j 60)) (Nat.ble 60 j)
def BKs41_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs41_43 j) (BKs43_45 j) (Nat.ble 59 j)
def BKs37_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs37_41 j) (BKs41_45 j) (Nat.ble 57 j)
def BKs30_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_37 j) (BKs37_45 j) (Nat.ble 53 j)
def BKs45_47 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_61 (Nat.beq j 61)) (Bool.rec (motive := fun _ => ℕ) 0 BK_62 (Nat.beq j 62)) (Nat.ble 62 j)
def BKs47_49 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_63 (Nat.beq j 63)) (Bool.rec (motive := fun _ => ℕ) 0 BK_64 (Nat.beq j 64)) (Nat.ble 64 j)
def BKs45_49 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_47 j) (BKs47_49 j) (Nat.ble 63 j)
def BKs49_51 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_65 (Nat.beq j 65)) (Bool.rec (motive := fun _ => ℕ) 0 BK_66 (Nat.beq j 66)) (Nat.ble 66 j)
def BKs51_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_67 (Nat.beq j 67)) (Bool.rec (motive := fun _ => ℕ) 0 BK_68 (Nat.beq j 68)) (Nat.ble 68 j)
def BKs49_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs49_51 j) (BKs51_53 j) (Nat.ble 67 j)
def BKs45_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_49 j) (BKs49_53 j) (Nat.ble 65 j)
def BKs53_55 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_69 (Nat.beq j 69)) (Bool.rec (motive := fun _ => ℕ) 0 BK_70 (Nat.beq j 70)) (Nat.ble 70 j)
def BKs55_57 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_71 (Nat.beq j 71)) (Bool.rec (motive := fun _ => ℕ) 0 BK_72 (Nat.beq j 72)) (Nat.ble 72 j)
def BKs53_57 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs53_55 j) (BKs55_57 j) (Nat.ble 71 j)
def BKs57_59 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_73 (Nat.beq j 73)) (Bool.rec (motive := fun _ => ℕ) 0 BK_74 (Nat.beq j 74)) (Nat.ble 74 j)
def BKs59_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_75 (Nat.beq j 75)) (Bool.rec (motive := fun _ => ℕ) 0 BK_76 (Nat.beq j 76)) (Nat.ble 76 j)
def BKs57_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs57_59 j) (BKs59_61 j) (Nat.ble 75 j)
def BKs53_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs53_57 j) (BKs57_61 j) (Nat.ble 73 j)
def BKs45_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_53 j) (BKs53_61 j) (Nat.ble 69 j)
def BKs30_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_45 j) (BKs45_61 j) (Nat.ble 61 j)
def BKs0_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_30 j) (BKs30_61 j) (Nat.ble 46 j)
def BKs62_64 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_78 (Nat.beq j 78)) (Bool.rec (motive := fun _ => ℕ) 0 BK_79 (Nat.beq j 79)) (Nat.ble 79 j)
def BKs61_64 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_77 (Nat.beq j 77)) (BKs62_64 j) (Nat.ble 78 j)
def BKs64_66 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_80 (Nat.beq j 80)) (Bool.rec (motive := fun _ => ℕ) 0 BK_81 (Nat.beq j 81)) (Nat.ble 81 j)
def BKs66_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_82 (Nat.beq j 82)) (Bool.rec (motive := fun _ => ℕ) 0 BK_83 (Nat.beq j 83)) (Nat.ble 83 j)
def BKs64_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs64_66 j) (BKs66_68 j) (Nat.ble 82 j)
def BKs61_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_64 j) (BKs64_68 j) (Nat.ble 80 j)
def BKs68_70 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_84 (Nat.beq j 84)) (Bool.rec (motive := fun _ => ℕ) 0 BK_85 (Nat.beq j 85)) (Nat.ble 85 j)
def BKs70_72 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_86 (Nat.beq j 86)) (Bool.rec (motive := fun _ => ℕ) 0 BK_87 (Nat.beq j 87)) (Nat.ble 87 j)
def BKs68_72 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs68_70 j) (BKs70_72 j) (Nat.ble 86 j)
def BKs72_74 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_88 (Nat.beq j 88)) (Bool.rec (motive := fun _ => ℕ) 0 BK_89 (Nat.beq j 89)) (Nat.ble 89 j)
def BKs74_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_90 (Nat.beq j 90)) (Bool.rec (motive := fun _ => ℕ) 0 BK_91 (Nat.beq j 91)) (Nat.ble 91 j)
def BKs72_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs72_74 j) (BKs74_76 j) (Nat.ble 90 j)
def BKs68_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs68_72 j) (BKs72_76 j) (Nat.ble 88 j)
def BKs61_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_68 j) (BKs68_76 j) (Nat.ble 84 j)
def BKs76_78 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_92 (Nat.beq j 92)) (Bool.rec (motive := fun _ => ℕ) 0 BK_93 (Nat.beq j 93)) (Nat.ble 93 j)
def BKs78_80 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_94 (Nat.beq j 94)) (Bool.rec (motive := fun _ => ℕ) 0 BK_95 (Nat.beq j 95)) (Nat.ble 95 j)
def BKs76_80 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_78 j) (BKs78_80 j) (Nat.ble 94 j)
def BKs80_82 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_96 (Nat.beq j 96)) (Bool.rec (motive := fun _ => ℕ) 0 BK_97 (Nat.beq j 97)) (Nat.ble 97 j)
def BKs82_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_98 (Nat.beq j 98)) (Bool.rec (motive := fun _ => ℕ) 0 BK_99 (Nat.beq j 99)) (Nat.ble 99 j)
def BKs80_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs80_82 j) (BKs82_84 j) (Nat.ble 98 j)
def BKs76_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_80 j) (BKs80_84 j) (Nat.ble 96 j)
def BKs84_86 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_100 (Nat.beq j 100)) (Bool.rec (motive := fun _ => ℕ) 0 BK_101 (Nat.beq j 101)) (Nat.ble 101 j)
def BKs86_88 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_102 (Nat.beq j 102)) (Bool.rec (motive := fun _ => ℕ) 0 BK_103 (Nat.beq j 103)) (Nat.ble 103 j)
def BKs84_88 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs84_86 j) (BKs86_88 j) (Nat.ble 102 j)
def BKs88_90 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_104 (Nat.beq j 104)) (Bool.rec (motive := fun _ => ℕ) 0 BK_105 (Nat.beq j 105)) (Nat.ble 105 j)
def BKs90_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_106 (Nat.beq j 106)) (Bool.rec (motive := fun _ => ℕ) 0 BK_107 (Nat.beq j 107)) (Nat.ble 107 j)
def BKs88_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs88_90 j) (BKs90_92 j) (Nat.ble 106 j)
def BKs84_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs84_88 j) (BKs88_92 j) (Nat.ble 104 j)
def BKs76_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_84 j) (BKs84_92 j) (Nat.ble 100 j)
def BKs61_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_76 j) (BKs76_92 j) (Nat.ble 92 j)
def BKs93_95 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_109 (Nat.beq j 109)) (Bool.rec (motive := fun _ => ℕ) 0 BK_110 (Nat.beq j 110)) (Nat.ble 110 j)
def BKs92_95 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_108 (Nat.beq j 108)) (BKs93_95 j) (Nat.ble 109 j)
def BKs95_97 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_111 (Nat.beq j 111)) (Bool.rec (motive := fun _ => ℕ) 0 BK_112 (Nat.beq j 112)) (Nat.ble 112 j)
def BKs97_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_113 (Nat.beq j 113)) (Bool.rec (motive := fun _ => ℕ) 0 BK_114 (Nat.beq j 114)) (Nat.ble 114 j)
def BKs95_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs95_97 j) (BKs97_99 j) (Nat.ble 113 j)
def BKs92_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_95 j) (BKs95_99 j) (Nat.ble 111 j)
def BKs99_101 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_115 (Nat.beq j 115)) (Bool.rec (motive := fun _ => ℕ) 0 BK_116 (Nat.beq j 116)) (Nat.ble 116 j)
def BKs101_103 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_117 (Nat.beq j 117)) (Bool.rec (motive := fun _ => ℕ) 0 BK_118 (Nat.beq j 118)) (Nat.ble 118 j)
def BKs99_103 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs99_101 j) (BKs101_103 j) (Nat.ble 117 j)
def BKs103_105 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_119 (Nat.beq j 119)) (Bool.rec (motive := fun _ => ℕ) 0 BK_120 (Nat.beq j 120)) (Nat.ble 120 j)
def BKs105_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_121 (Nat.beq j 121)) (Bool.rec (motive := fun _ => ℕ) 0 BK_122 (Nat.beq j 122)) (Nat.ble 122 j)
def BKs103_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs103_105 j) (BKs105_107 j) (Nat.ble 121 j)
def BKs99_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs99_103 j) (BKs103_107 j) (Nat.ble 119 j)
def BKs92_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_99 j) (BKs99_107 j) (Nat.ble 115 j)
def BKs107_109 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_123 (Nat.beq j 123)) (Bool.rec (motive := fun _ => ℕ) 0 BK_124 (Nat.beq j 124)) (Nat.ble 124 j)
def BKs109_111 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_125 (Nat.beq j 125)) (Bool.rec (motive := fun _ => ℕ) 0 BK_126 (Nat.beq j 126)) (Nat.ble 126 j)
def BKs107_111 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_109 j) (BKs109_111 j) (Nat.ble 125 j)
def BKs111_113 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_127 (Nat.beq j 127)) (Bool.rec (motive := fun _ => ℕ) 0 BK_128 (Nat.beq j 128)) (Nat.ble 128 j)
def BKs113_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_129 (Nat.beq j 129)) (Bool.rec (motive := fun _ => ℕ) 0 BK_130 (Nat.beq j 130)) (Nat.ble 130 j)
def BKs111_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs111_113 j) (BKs113_115 j) (Nat.ble 129 j)
def BKs107_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_111 j) (BKs111_115 j) (Nat.ble 127 j)
def BKs115_117 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_131 (Nat.beq j 131)) (Bool.rec (motive := fun _ => ℕ) 0 BK_132 (Nat.beq j 132)) (Nat.ble 132 j)
def BKs117_119 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_133 (Nat.beq j 133)) (Bool.rec (motive := fun _ => ℕ) 0 BK_134 (Nat.beq j 134)) (Nat.ble 134 j)
def BKs115_119 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs115_117 j) (BKs117_119 j) (Nat.ble 133 j)
def BKs119_121 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_135 (Nat.beq j 135)) (Bool.rec (motive := fun _ => ℕ) 0 BK_136 (Nat.beq j 136)) (Nat.ble 136 j)
def BKs121_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_137 (Nat.beq j 137)) (Bool.rec (motive := fun _ => ℕ) 0 BK_138 (Nat.beq j 138)) (Nat.ble 138 j)
def BKs119_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs119_121 j) (BKs121_123 j) (Nat.ble 137 j)
def BKs115_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs115_119 j) (BKs119_123 j) (Nat.ble 135 j)
def BKs107_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_115 j) (BKs115_123 j) (Nat.ble 131 j)
def BKs92_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_107 j) (BKs107_123 j) (Nat.ble 123 j)
def BKs61_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_92 j) (BKs92_123 j) (Nat.ble 108 j)
def BKs0_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_61 j) (BKs61_123 j) (Nat.ble 77 j)
def BKs124_126 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_140 (Nat.beq j 140)) (Bool.rec (motive := fun _ => ℕ) 0 BK_141 (Nat.beq j 141)) (Nat.ble 141 j)
def BKs123_126 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_139 (Nat.beq j 139)) (BKs124_126 j) (Nat.ble 140 j)
def BKs126_128 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_142 (Nat.beq j 142)) (Bool.rec (motive := fun _ => ℕ) 0 BK_143 (Nat.beq j 143)) (Nat.ble 143 j)
def BKs128_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_144 (Nat.beq j 144)) (Bool.rec (motive := fun _ => ℕ) 0 BK_145 (Nat.beq j 145)) (Nat.ble 145 j)
def BKs126_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs126_128 j) (BKs128_130 j) (Nat.ble 144 j)
def BKs123_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_126 j) (BKs126_130 j) (Nat.ble 142 j)
def BKs130_132 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_146 (Nat.beq j 146)) (Bool.rec (motive := fun _ => ℕ) 0 BK_147 (Nat.beq j 147)) (Nat.ble 147 j)
def BKs132_134 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_148 (Nat.beq j 148)) (Bool.rec (motive := fun _ => ℕ) 0 BK_149 (Nat.beq j 149)) (Nat.ble 149 j)
def BKs130_134 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs130_132 j) (BKs132_134 j) (Nat.ble 148 j)
def BKs134_136 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_150 (Nat.beq j 150)) (Bool.rec (motive := fun _ => ℕ) 0 BK_151 (Nat.beq j 151)) (Nat.ble 151 j)
def BKs136_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_152 (Nat.beq j 152)) (Bool.rec (motive := fun _ => ℕ) 0 BK_153 (Nat.beq j 153)) (Nat.ble 153 j)
def BKs134_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs134_136 j) (BKs136_138 j) (Nat.ble 152 j)
def BKs130_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs130_134 j) (BKs134_138 j) (Nat.ble 150 j)
def BKs123_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_130 j) (BKs130_138 j) (Nat.ble 146 j)
def BKs138_140 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_154 (Nat.beq j 154)) (Bool.rec (motive := fun _ => ℕ) 0 BK_155 (Nat.beq j 155)) (Nat.ble 155 j)
def BKs140_142 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_156 (Nat.beq j 156)) (Bool.rec (motive := fun _ => ℕ) 0 BK_157 (Nat.beq j 157)) (Nat.ble 157 j)
def BKs138_142 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_140 j) (BKs140_142 j) (Nat.ble 156 j)
def BKs142_144 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_158 (Nat.beq j 158)) (Bool.rec (motive := fun _ => ℕ) 0 BK_159 (Nat.beq j 159)) (Nat.ble 159 j)
def BKs144_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_160 (Nat.beq j 160)) (Bool.rec (motive := fun _ => ℕ) 0 BK_161 (Nat.beq j 161)) (Nat.ble 161 j)
def BKs142_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs142_144 j) (BKs144_146 j) (Nat.ble 160 j)
def BKs138_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_142 j) (BKs142_146 j) (Nat.ble 158 j)
def BKs146_148 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_162 (Nat.beq j 162)) (Bool.rec (motive := fun _ => ℕ) 0 BK_163 (Nat.beq j 163)) (Nat.ble 163 j)
def BKs148_150 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_164 (Nat.beq j 164)) (Bool.rec (motive := fun _ => ℕ) 0 BK_165 (Nat.beq j 165)) (Nat.ble 165 j)
def BKs146_150 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs146_148 j) (BKs148_150 j) (Nat.ble 164 j)
def BKs150_152 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_166 (Nat.beq j 166)) (Bool.rec (motive := fun _ => ℕ) 0 BK_167 (Nat.beq j 167)) (Nat.ble 167 j)
def BKs152_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_168 (Nat.beq j 168)) (Bool.rec (motive := fun _ => ℕ) 0 BK_169 (Nat.beq j 169)) (Nat.ble 169 j)
def BKs150_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs150_152 j) (BKs152_154 j) (Nat.ble 168 j)
def BKs146_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs146_150 j) (BKs150_154 j) (Nat.ble 166 j)
def BKs138_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_146 j) (BKs146_154 j) (Nat.ble 162 j)
def BKs123_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_138 j) (BKs138_154 j) (Nat.ble 154 j)
def BKs155_157 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_171 (Nat.beq j 171)) (Bool.rec (motive := fun _ => ℕ) 0 BK_172 (Nat.beq j 172)) (Nat.ble 172 j)
def BKs154_157 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_170 (Nat.beq j 170)) (BKs155_157 j) (Nat.ble 171 j)
def BKs157_159 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_173 (Nat.beq j 173)) (Bool.rec (motive := fun _ => ℕ) 0 BK_174 (Nat.beq j 174)) (Nat.ble 174 j)
def BKs159_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_175 (Nat.beq j 175)) (Bool.rec (motive := fun _ => ℕ) 0 BK_176 (Nat.beq j 176)) (Nat.ble 176 j)
def BKs157_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs157_159 j) (BKs159_161 j) (Nat.ble 175 j)
def BKs154_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_157 j) (BKs157_161 j) (Nat.ble 173 j)
def BKs161_163 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_177 (Nat.beq j 177)) (Bool.rec (motive := fun _ => ℕ) 0 BK_178 (Nat.beq j 178)) (Nat.ble 178 j)
def BKs163_165 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_179 (Nat.beq j 179)) (Bool.rec (motive := fun _ => ℕ) 0 BK_180 (Nat.beq j 180)) (Nat.ble 180 j)
def BKs161_165 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs161_163 j) (BKs163_165 j) (Nat.ble 179 j)
def BKs165_167 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_181 (Nat.beq j 181)) (Bool.rec (motive := fun _ => ℕ) 0 BK_182 (Nat.beq j 182)) (Nat.ble 182 j)
def BKs167_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_183 (Nat.beq j 183)) (Bool.rec (motive := fun _ => ℕ) 0 BK_184 (Nat.beq j 184)) (Nat.ble 184 j)
def BKs165_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs165_167 j) (BKs167_169 j) (Nat.ble 183 j)
def BKs161_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs161_165 j) (BKs165_169 j) (Nat.ble 181 j)
def BKs154_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_161 j) (BKs161_169 j) (Nat.ble 177 j)
def BKs169_171 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_185 (Nat.beq j 185)) (Bool.rec (motive := fun _ => ℕ) 0 BK_186 (Nat.beq j 186)) (Nat.ble 186 j)
def BKs171_173 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_187 (Nat.beq j 187)) (Bool.rec (motive := fun _ => ℕ) 0 BK_188 (Nat.beq j 188)) (Nat.ble 188 j)
def BKs169_173 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_171 j) (BKs171_173 j) (Nat.ble 187 j)
def BKs173_175 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_189 (Nat.beq j 189)) (Bool.rec (motive := fun _ => ℕ) 0 BK_190 (Nat.beq j 190)) (Nat.ble 190 j)
def BKs175_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_191 (Nat.beq j 191)) (Bool.rec (motive := fun _ => ℕ) 0 BK_192 (Nat.beq j 192)) (Nat.ble 192 j)
def BKs173_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs173_175 j) (BKs175_177 j) (Nat.ble 191 j)
def BKs169_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_173 j) (BKs173_177 j) (Nat.ble 189 j)
def BKs177_179 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_193 (Nat.beq j 193)) (Bool.rec (motive := fun _ => ℕ) 0 BK_194 (Nat.beq j 194)) (Nat.ble 194 j)
def BKs179_181 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_195 (Nat.beq j 195)) (Bool.rec (motive := fun _ => ℕ) 0 BK_196 (Nat.beq j 196)) (Nat.ble 196 j)
def BKs177_181 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs177_179 j) (BKs179_181 j) (Nat.ble 195 j)
def BKs181_183 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_197 (Nat.beq j 197)) (Bool.rec (motive := fun _ => ℕ) 0 BK_198 (Nat.beq j 198)) (Nat.ble 198 j)
def BKs183_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_199 (Nat.beq j 199)) (Bool.rec (motive := fun _ => ℕ) 0 BK_200 (Nat.beq j 200)) (Nat.ble 200 j)
def BKs181_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs181_183 j) (BKs183_185 j) (Nat.ble 199 j)
def BKs177_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs177_181 j) (BKs181_185 j) (Nat.ble 197 j)
def BKs169_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_177 j) (BKs177_185 j) (Nat.ble 193 j)
def BKs154_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_169 j) (BKs169_185 j) (Nat.ble 185 j)
def BKs123_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_154 j) (BKs154_185 j) (Nat.ble 170 j)
def BKs186_188 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_202 (Nat.beq j 202)) (Bool.rec (motive := fun _ => ℕ) 0 BK_203 (Nat.beq j 203)) (Nat.ble 203 j)
def BKs185_188 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_201 (Nat.beq j 201)) (BKs186_188 j) (Nat.ble 202 j)
def BKs188_190 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_204 (Nat.beq j 204)) (Bool.rec (motive := fun _ => ℕ) 0 BK_205 (Nat.beq j 205)) (Nat.ble 205 j)
def BKs190_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_206 (Nat.beq j 206)) (Bool.rec (motive := fun _ => ℕ) 0 BK_207 (Nat.beq j 207)) (Nat.ble 207 j)
def BKs188_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs188_190 j) (BKs190_192 j) (Nat.ble 206 j)
def BKs185_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_188 j) (BKs188_192 j) (Nat.ble 204 j)
def BKs192_194 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_208 (Nat.beq j 208)) (Bool.rec (motive := fun _ => ℕ) 0 BK_209 (Nat.beq j 209)) (Nat.ble 209 j)
def BKs194_196 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_210 (Nat.beq j 210)) (Bool.rec (motive := fun _ => ℕ) 0 BK_211 (Nat.beq j 211)) (Nat.ble 211 j)
def BKs192_196 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs192_194 j) (BKs194_196 j) (Nat.ble 210 j)
def BKs196_198 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_212 (Nat.beq j 212)) (Bool.rec (motive := fun _ => ℕ) 0 BK_213 (Nat.beq j 213)) (Nat.ble 213 j)
def BKs198_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_214 (Nat.beq j 214)) (Bool.rec (motive := fun _ => ℕ) 0 BK_215 (Nat.beq j 215)) (Nat.ble 215 j)
def BKs196_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs196_198 j) (BKs198_200 j) (Nat.ble 214 j)
def BKs192_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs192_196 j) (BKs196_200 j) (Nat.ble 212 j)
def BKs185_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_192 j) (BKs192_200 j) (Nat.ble 208 j)
def BKs200_202 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_216 (Nat.beq j 216)) (Bool.rec (motive := fun _ => ℕ) 0 BK_217 (Nat.beq j 217)) (Nat.ble 217 j)
def BKs202_204 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_218 (Nat.beq j 218)) (Bool.rec (motive := fun _ => ℕ) 0 BK_219 (Nat.beq j 219)) (Nat.ble 219 j)
def BKs200_204 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_202 j) (BKs202_204 j) (Nat.ble 218 j)
def BKs204_206 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_220 (Nat.beq j 220)) (Bool.rec (motive := fun _ => ℕ) 0 BK_221 (Nat.beq j 221)) (Nat.ble 221 j)
def BKs206_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_222 (Nat.beq j 222)) (Bool.rec (motive := fun _ => ℕ) 0 BK_223 (Nat.beq j 223)) (Nat.ble 223 j)
def BKs204_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs204_206 j) (BKs206_208 j) (Nat.ble 222 j)
def BKs200_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_204 j) (BKs204_208 j) (Nat.ble 220 j)
def BKs208_210 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_224 (Nat.beq j 224)) (Bool.rec (motive := fun _ => ℕ) 0 BK_225 (Nat.beq j 225)) (Nat.ble 225 j)
def BKs210_212 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_226 (Nat.beq j 226)) (Bool.rec (motive := fun _ => ℕ) 0 BK_227 (Nat.beq j 227)) (Nat.ble 227 j)
def BKs208_212 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs208_210 j) (BKs210_212 j) (Nat.ble 226 j)
def BKs212_214 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_228 (Nat.beq j 228)) (Bool.rec (motive := fun _ => ℕ) 0 BK_229 (Nat.beq j 229)) (Nat.ble 229 j)
def BKs214_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_230 (Nat.beq j 230)) (Bool.rec (motive := fun _ => ℕ) 0 BK_231 (Nat.beq j 231)) (Nat.ble 231 j)
def BKs212_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs212_214 j) (BKs214_216 j) (Nat.ble 230 j)
def BKs208_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs208_212 j) (BKs212_216 j) (Nat.ble 228 j)
def BKs200_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_208 j) (BKs208_216 j) (Nat.ble 224 j)
def BKs185_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_200 j) (BKs200_216 j) (Nat.ble 216 j)
def BKs217_219 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_233 (Nat.beq j 233)) (Bool.rec (motive := fun _ => ℕ) 0 BK_234 (Nat.beq j 234)) (Nat.ble 234 j)
def BKs216_219 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_232 (Nat.beq j 232)) (BKs217_219 j) (Nat.ble 233 j)
def BKs219_221 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_235 (Nat.beq j 235)) (Bool.rec (motive := fun _ => ℕ) 0 BK_236 (Nat.beq j 236)) (Nat.ble 236 j)
def BKs221_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_237 (Nat.beq j 237)) (Bool.rec (motive := fun _ => ℕ) 0 BK_238 (Nat.beq j 238)) (Nat.ble 238 j)
def BKs219_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs219_221 j) (BKs221_223 j) (Nat.ble 237 j)
def BKs216_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_219 j) (BKs219_223 j) (Nat.ble 235 j)
def BKs223_225 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_239 (Nat.beq j 239)) (Bool.rec (motive := fun _ => ℕ) 0 BK_240 (Nat.beq j 240)) (Nat.ble 240 j)
def BKs225_227 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_241 (Nat.beq j 241)) (Bool.rec (motive := fun _ => ℕ) 0 BK_242 (Nat.beq j 242)) (Nat.ble 242 j)
def BKs223_227 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs223_225 j) (BKs225_227 j) (Nat.ble 241 j)
def BKs227_229 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_243 (Nat.beq j 243)) (Bool.rec (motive := fun _ => ℕ) 0 BK_244 (Nat.beq j 244)) (Nat.ble 244 j)
def BKs229_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_245 (Nat.beq j 245)) (Bool.rec (motive := fun _ => ℕ) 0 BK_246 (Nat.beq j 246)) (Nat.ble 246 j)
def BKs227_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs227_229 j) (BKs229_231 j) (Nat.ble 245 j)
def BKs223_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs223_227 j) (BKs227_231 j) (Nat.ble 243 j)
def BKs216_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_223 j) (BKs223_231 j) (Nat.ble 239 j)
def BKs231_233 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_247 (Nat.beq j 247)) (Bool.rec (motive := fun _ => ℕ) 0 BK_248 (Nat.beq j 248)) (Nat.ble 248 j)
def BKs233_235 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_249 (Nat.beq j 249)) (Bool.rec (motive := fun _ => ℕ) 0 BK_250 (Nat.beq j 250)) (Nat.ble 250 j)
def BKs231_235 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_233 j) (BKs233_235 j) (Nat.ble 249 j)
def BKs235_237 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_251 (Nat.beq j 251)) (Bool.rec (motive := fun _ => ℕ) 0 BK_252 (Nat.beq j 252)) (Nat.ble 252 j)
def BKs237_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_253 (Nat.beq j 253)) (Bool.rec (motive := fun _ => ℕ) 0 BK_254 (Nat.beq j 254)) (Nat.ble 254 j)
def BKs235_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs235_237 j) (BKs237_239 j) (Nat.ble 253 j)
def BKs231_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_235 j) (BKs235_239 j) (Nat.ble 251 j)
def BKs239_241 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_255 (Nat.beq j 255)) (Bool.rec (motive := fun _ => ℕ) 0 BK_256 (Nat.beq j 256)) (Nat.ble 256 j)
def BKs241_243 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_257 (Nat.beq j 257)) (Bool.rec (motive := fun _ => ℕ) 0 BK_258 (Nat.beq j 258)) (Nat.ble 258 j)
def BKs239_243 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs239_241 j) (BKs241_243 j) (Nat.ble 257 j)
def BKs243_245 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_259 (Nat.beq j 259)) (Bool.rec (motive := fun _ => ℕ) 0 BK_260 (Nat.beq j 260)) (Nat.ble 260 j)
def BKs245_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_261 (Nat.beq j 261)) (Bool.rec (motive := fun _ => ℕ) 0 BK_262 (Nat.beq j 262)) (Nat.ble 262 j)
def BKs243_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs243_245 j) (BKs245_247 j) (Nat.ble 261 j)
def BKs239_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs239_243 j) (BKs243_247 j) (Nat.ble 259 j)
def BKs231_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_239 j) (BKs239_247 j) (Nat.ble 255 j)
def BKs216_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_231 j) (BKs231_247 j) (Nat.ble 247 j)
def BKs185_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_216 j) (BKs216_247 j) (Nat.ble 232 j)
def BKs123_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_185 j) (BKs185_247 j) (Nat.ble 201 j)
def BKs0_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_123 j) (BKs123_247 j) (Nat.ble 139 j)
def BKs248_250 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_264 (Nat.beq j 264)) (Bool.rec (motive := fun _ => ℕ) 0 BK_265 (Nat.beq j 265)) (Nat.ble 265 j)
def BKs247_250 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_263 (Nat.beq j 263)) (BKs248_250 j) (Nat.ble 264 j)
def BKs250_252 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_266 (Nat.beq j 266)) (Bool.rec (motive := fun _ => ℕ) 0 BK_267 (Nat.beq j 267)) (Nat.ble 267 j)
def BKs252_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_268 (Nat.beq j 268)) (Bool.rec (motive := fun _ => ℕ) 0 BK_269 (Nat.beq j 269)) (Nat.ble 269 j)
def BKs250_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs250_252 j) (BKs252_254 j) (Nat.ble 268 j)
def BKs247_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_250 j) (BKs250_254 j) (Nat.ble 266 j)
def BKs254_256 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_270 (Nat.beq j 270)) (Bool.rec (motive := fun _ => ℕ) 0 BK_271 (Nat.beq j 271)) (Nat.ble 271 j)
def BKs256_258 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_272 (Nat.beq j 272)) (Bool.rec (motive := fun _ => ℕ) 0 BK_273 (Nat.beq j 273)) (Nat.ble 273 j)
def BKs254_258 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs254_256 j) (BKs256_258 j) (Nat.ble 272 j)
def BKs258_260 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_274 (Nat.beq j 274)) (Bool.rec (motive := fun _ => ℕ) 0 BK_275 (Nat.beq j 275)) (Nat.ble 275 j)
def BKs260_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_276 (Nat.beq j 276)) (Bool.rec (motive := fun _ => ℕ) 0 BK_277 (Nat.beq j 277)) (Nat.ble 277 j)
def BKs258_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs258_260 j) (BKs260_262 j) (Nat.ble 276 j)
def BKs254_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs254_258 j) (BKs258_262 j) (Nat.ble 274 j)
def BKs247_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_254 j) (BKs254_262 j) (Nat.ble 270 j)
def BKs263_265 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_279 (Nat.beq j 279)) (Bool.rec (motive := fun _ => ℕ) 0 BK_280 (Nat.beq j 280)) (Nat.ble 280 j)
def BKs262_265 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_278 (Nat.beq j 278)) (BKs263_265 j) (Nat.ble 279 j)
def BKs265_267 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_281 (Nat.beq j 281)) (Bool.rec (motive := fun _ => ℕ) 0 BK_282 (Nat.beq j 282)) (Nat.ble 282 j)
def BKs267_269 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_283 (Nat.beq j 283)) (Bool.rec (motive := fun _ => ℕ) 0 BK_284 (Nat.beq j 284)) (Nat.ble 284 j)
def BKs265_269 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs265_267 j) (BKs267_269 j) (Nat.ble 283 j)
def BKs262_269 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs262_265 j) (BKs265_269 j) (Nat.ble 281 j)
def BKs269_271 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_285 (Nat.beq j 285)) (Bool.rec (motive := fun _ => ℕ) 0 BK_286 (Nat.beq j 286)) (Nat.ble 286 j)
def BKs271_273 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_287 (Nat.beq j 287)) (Bool.rec (motive := fun _ => ℕ) 0 BK_288 (Nat.beq j 288)) (Nat.ble 288 j)
def BKs269_273 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs269_271 j) (BKs271_273 j) (Nat.ble 287 j)
def BKs273_275 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_289 (Nat.beq j 289)) (Bool.rec (motive := fun _ => ℕ) 0 BK_290 (Nat.beq j 290)) (Nat.ble 290 j)
def BKs275_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_291 (Nat.beq j 291)) (Bool.rec (motive := fun _ => ℕ) 0 BK_292 (Nat.beq j 292)) (Nat.ble 292 j)
def BKs273_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs273_275 j) (BKs275_277 j) (Nat.ble 291 j)
def BKs269_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs269_273 j) (BKs273_277 j) (Nat.ble 289 j)
def BKs262_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs262_269 j) (BKs269_277 j) (Nat.ble 285 j)
def BKs247_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_262 j) (BKs262_277 j) (Nat.ble 278 j)
def BKs278_280 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_294 (Nat.beq j 294)) (Bool.rec (motive := fun _ => ℕ) 0 BK_295 (Nat.beq j 295)) (Nat.ble 295 j)
def BKs277_280 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_293 (Nat.beq j 293)) (BKs278_280 j) (Nat.ble 294 j)
def BKs280_282 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_296 (Nat.beq j 296)) (Bool.rec (motive := fun _ => ℕ) 0 BK_297 (Nat.beq j 297)) (Nat.ble 297 j)
def BKs282_284 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_298 (Nat.beq j 298)) (Bool.rec (motive := fun _ => ℕ) 0 BK_299 (Nat.beq j 299)) (Nat.ble 299 j)
def BKs280_284 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs280_282 j) (BKs282_284 j) (Nat.ble 298 j)
def BKs277_284 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs277_280 j) (BKs280_284 j) (Nat.ble 296 j)
def BKs284_286 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_300 (Nat.beq j 300)) (Bool.rec (motive := fun _ => ℕ) 0 BK_301 (Nat.beq j 301)) (Nat.ble 301 j)
def BKs286_288 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_302 (Nat.beq j 302)) (Bool.rec (motive := fun _ => ℕ) 0 BK_303 (Nat.beq j 303)) (Nat.ble 303 j)
def BKs284_288 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs284_286 j) (BKs286_288 j) (Nat.ble 302 j)
def BKs288_290 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_304 (Nat.beq j 304)) (Bool.rec (motive := fun _ => ℕ) 0 BK_305 (Nat.beq j 305)) (Nat.ble 305 j)
def BKs290_292 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_306 (Nat.beq j 306)) (Bool.rec (motive := fun _ => ℕ) 0 BK_307 (Nat.beq j 307)) (Nat.ble 307 j)
def BKs288_292 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs288_290 j) (BKs290_292 j) (Nat.ble 306 j)
def BKs284_292 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs284_288 j) (BKs288_292 j) (Nat.ble 304 j)
def BKs277_292 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs277_284 j) (BKs284_292 j) (Nat.ble 300 j)
def BKs292_294 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_308 (Nat.beq j 308)) (Bool.rec (motive := fun _ => ℕ) 0 BK_309 (Nat.beq j 309)) (Nat.ble 309 j)
def BKs294_296 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_310 (Nat.beq j 310)) (Bool.rec (motive := fun _ => ℕ) 0 BK_311 (Nat.beq j 311)) (Nat.ble 311 j)
def BKs292_296 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs292_294 j) (BKs294_296 j) (Nat.ble 310 j)
def BKs296_298 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_312 (Nat.beq j 312)) (Bool.rec (motive := fun _ => ℕ) 0 BK_313 (Nat.beq j 313)) (Nat.ble 313 j)
def BKs298_300 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_314 (Nat.beq j 314)) (Bool.rec (motive := fun _ => ℕ) 0 BK_315 (Nat.beq j 315)) (Nat.ble 315 j)
def BKs296_300 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs296_298 j) (BKs298_300 j) (Nat.ble 314 j)
def BKs292_300 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs292_296 j) (BKs296_300 j) (Nat.ble 312 j)
def BKs300_302 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_316 (Nat.beq j 316)) (Bool.rec (motive := fun _ => ℕ) 0 BK_317 (Nat.beq j 317)) (Nat.ble 317 j)
def BKs302_304 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_318 (Nat.beq j 318)) (Bool.rec (motive := fun _ => ℕ) 0 BK_319 (Nat.beq j 319)) (Nat.ble 319 j)
def BKs300_304 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs300_302 j) (BKs302_304 j) (Nat.ble 318 j)
def BKs304_306 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_320 (Nat.beq j 320)) (Bool.rec (motive := fun _ => ℕ) 0 BK_321 (Nat.beq j 321)) (Nat.ble 321 j)
def BKs306_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_322 (Nat.beq j 322)) (Bool.rec (motive := fun _ => ℕ) 0 BK_323 (Nat.beq j 323)) (Nat.ble 323 j)
def BKs304_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs304_306 j) (BKs306_308 j) (Nat.ble 322 j)
def BKs300_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs300_304 j) (BKs304_308 j) (Nat.ble 320 j)
def BKs292_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs292_300 j) (BKs300_308 j) (Nat.ble 316 j)
def BKs277_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs277_292 j) (BKs292_308 j) (Nat.ble 308 j)
def BKs247_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_277 j) (BKs277_308 j) (Nat.ble 293 j)
def BKs309_311 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_325 (Nat.beq j 325)) (Bool.rec (motive := fun _ => ℕ) 0 BK_326 (Nat.beq j 326)) (Nat.ble 326 j)
def BKs308_311 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_324 (Nat.beq j 324)) (BKs309_311 j) (Nat.ble 325 j)
def BKs311_313 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_327 (Nat.beq j 327)) (Bool.rec (motive := fun _ => ℕ) 0 BK_328 (Nat.beq j 328)) (Nat.ble 328 j)
def BKs313_315 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_329 (Nat.beq j 329)) (Bool.rec (motive := fun _ => ℕ) 0 BK_330 (Nat.beq j 330)) (Nat.ble 330 j)
def BKs311_315 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs311_313 j) (BKs313_315 j) (Nat.ble 329 j)
def BKs308_315 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs308_311 j) (BKs311_315 j) (Nat.ble 327 j)
def BKs315_317 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_331 (Nat.beq j 331)) (Bool.rec (motive := fun _ => ℕ) 0 BK_332 (Nat.beq j 332)) (Nat.ble 332 j)
def BKs317_319 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_333 (Nat.beq j 333)) (Bool.rec (motive := fun _ => ℕ) 0 BK_334 (Nat.beq j 334)) (Nat.ble 334 j)
def BKs315_319 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs315_317 j) (BKs317_319 j) (Nat.ble 333 j)
def BKs319_321 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_335 (Nat.beq j 335)) (Bool.rec (motive := fun _ => ℕ) 0 BK_336 (Nat.beq j 336)) (Nat.ble 336 j)
def BKs321_323 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_337 (Nat.beq j 337)) (Bool.rec (motive := fun _ => ℕ) 0 BK_338 (Nat.beq j 338)) (Nat.ble 338 j)
def BKs319_323 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs319_321 j) (BKs321_323 j) (Nat.ble 337 j)
def BKs315_323 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs315_319 j) (BKs319_323 j) (Nat.ble 335 j)
def BKs308_323 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs308_315 j) (BKs315_323 j) (Nat.ble 331 j)
def BKs323_325 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_339 (Nat.beq j 339)) (Bool.rec (motive := fun _ => ℕ) 0 BK_340 (Nat.beq j 340)) (Nat.ble 340 j)
def BKs325_327 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_341 (Nat.beq j 341)) (Bool.rec (motive := fun _ => ℕ) 0 BK_342 (Nat.beq j 342)) (Nat.ble 342 j)
def BKs323_327 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs323_325 j) (BKs325_327 j) (Nat.ble 341 j)
def BKs327_329 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_343 (Nat.beq j 343)) (Bool.rec (motive := fun _ => ℕ) 0 BK_344 (Nat.beq j 344)) (Nat.ble 344 j)
def BKs329_331 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_345 (Nat.beq j 345)) (Bool.rec (motive := fun _ => ℕ) 0 BK_346 (Nat.beq j 346)) (Nat.ble 346 j)
def BKs327_331 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs327_329 j) (BKs329_331 j) (Nat.ble 345 j)
def BKs323_331 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs323_327 j) (BKs327_331 j) (Nat.ble 343 j)
def BKs331_333 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_347 (Nat.beq j 347)) (Bool.rec (motive := fun _ => ℕ) 0 BK_348 (Nat.beq j 348)) (Nat.ble 348 j)
def BKs333_335 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_349 (Nat.beq j 349)) (Bool.rec (motive := fun _ => ℕ) 0 BK_350 (Nat.beq j 350)) (Nat.ble 350 j)
def BKs331_335 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs331_333 j) (BKs333_335 j) (Nat.ble 349 j)
def BKs335_337 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_351 (Nat.beq j 351)) (Bool.rec (motive := fun _ => ℕ) 0 BK_352 (Nat.beq j 352)) (Nat.ble 352 j)
def BKs337_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_353 (Nat.beq j 353)) (Bool.rec (motive := fun _ => ℕ) 0 BK_354 (Nat.beq j 354)) (Nat.ble 354 j)
def BKs335_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs335_337 j) (BKs337_339 j) (Nat.ble 353 j)
def BKs331_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs331_335 j) (BKs335_339 j) (Nat.ble 351 j)
def BKs323_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs323_331 j) (BKs331_339 j) (Nat.ble 347 j)
def BKs308_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs308_323 j) (BKs323_339 j) (Nat.ble 339 j)
def BKs340_342 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_356 (Nat.beq j 356)) (Bool.rec (motive := fun _ => ℕ) 0 BK_357 (Nat.beq j 357)) (Nat.ble 357 j)
def BKs339_342 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_355 (Nat.beq j 355)) (BKs340_342 j) (Nat.ble 356 j)
def BKs342_344 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_358 (Nat.beq j 358)) (Bool.rec (motive := fun _ => ℕ) 0 BK_359 (Nat.beq j 359)) (Nat.ble 359 j)
def BKs344_346 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_360 (Nat.beq j 360)) (Bool.rec (motive := fun _ => ℕ) 0 BK_361 (Nat.beq j 361)) (Nat.ble 361 j)
def BKs342_346 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs342_344 j) (BKs344_346 j) (Nat.ble 360 j)
def BKs339_346 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs339_342 j) (BKs342_346 j) (Nat.ble 358 j)
def BKs346_348 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_362 (Nat.beq j 362)) (Bool.rec (motive := fun _ => ℕ) 0 BK_363 (Nat.beq j 363)) (Nat.ble 363 j)
def BKs348_350 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_364 (Nat.beq j 364)) (Bool.rec (motive := fun _ => ℕ) 0 BK_365 (Nat.beq j 365)) (Nat.ble 365 j)
def BKs346_350 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs346_348 j) (BKs348_350 j) (Nat.ble 364 j)
def BKs350_352 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_366 (Nat.beq j 366)) (Bool.rec (motive := fun _ => ℕ) 0 BK_367 (Nat.beq j 367)) (Nat.ble 367 j)
def BKs352_354 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_368 (Nat.beq j 368)) (Bool.rec (motive := fun _ => ℕ) 0 BK_369 (Nat.beq j 369)) (Nat.ble 369 j)
def BKs350_354 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs350_352 j) (BKs352_354 j) (Nat.ble 368 j)
def BKs346_354 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs346_350 j) (BKs350_354 j) (Nat.ble 366 j)
def BKs339_354 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs339_346 j) (BKs346_354 j) (Nat.ble 362 j)
def BKs354_356 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_370 (Nat.beq j 370)) (Bool.rec (motive := fun _ => ℕ) 0 BK_371 (Nat.beq j 371)) (Nat.ble 371 j)
def BKs356_358 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_372 (Nat.beq j 372)) (Bool.rec (motive := fun _ => ℕ) 0 BK_373 (Nat.beq j 373)) (Nat.ble 373 j)
def BKs354_358 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs354_356 j) (BKs356_358 j) (Nat.ble 372 j)
def BKs358_360 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_374 (Nat.beq j 374)) (Bool.rec (motive := fun _ => ℕ) 0 BK_375 (Nat.beq j 375)) (Nat.ble 375 j)
def BKs360_362 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_376 (Nat.beq j 376)) (Bool.rec (motive := fun _ => ℕ) 0 BK_377 (Nat.beq j 377)) (Nat.ble 377 j)
def BKs358_362 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs358_360 j) (BKs360_362 j) (Nat.ble 376 j)
def BKs354_362 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs354_358 j) (BKs358_362 j) (Nat.ble 374 j)
def BKs362_364 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_378 (Nat.beq j 378)) (Bool.rec (motive := fun _ => ℕ) 0 BK_379 (Nat.beq j 379)) (Nat.ble 379 j)
def BKs364_366 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_380 (Nat.beq j 380)) (Bool.rec (motive := fun _ => ℕ) 0 BK_381 (Nat.beq j 381)) (Nat.ble 381 j)
def BKs362_366 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs362_364 j) (BKs364_366 j) (Nat.ble 380 j)
def BKs366_368 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_382 (Nat.beq j 382)) (Bool.rec (motive := fun _ => ℕ) 0 BK_383 (Nat.beq j 383)) (Nat.ble 383 j)
def BKs368_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_384 (Nat.beq j 384)) (Bool.rec (motive := fun _ => ℕ) 0 BK_385 (Nat.beq j 385)) (Nat.ble 385 j)
def BKs366_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs366_368 j) (BKs368_370 j) (Nat.ble 384 j)
def BKs362_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs362_366 j) (BKs366_370 j) (Nat.ble 382 j)
def BKs354_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs354_362 j) (BKs362_370 j) (Nat.ble 378 j)
def BKs339_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs339_354 j) (BKs354_370 j) (Nat.ble 370 j)
def BKs308_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs308_339 j) (BKs339_370 j) (Nat.ble 355 j)
def BKs247_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_308 j) (BKs308_370 j) (Nat.ble 324 j)
def BKs371_373 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_387 (Nat.beq j 387)) (Bool.rec (motive := fun _ => ℕ) 0 BK_388 (Nat.beq j 388)) (Nat.ble 388 j)
def BKs370_373 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_386 (Nat.beq j 386)) (BKs371_373 j) (Nat.ble 387 j)
def BKs373_375 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_389 (Nat.beq j 389)) (Bool.rec (motive := fun _ => ℕ) 0 BK_390 (Nat.beq j 390)) (Nat.ble 390 j)
def BKs375_377 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_391 (Nat.beq j 391)) (Bool.rec (motive := fun _ => ℕ) 0 BK_392 (Nat.beq j 392)) (Nat.ble 392 j)
def BKs373_377 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs373_375 j) (BKs375_377 j) (Nat.ble 391 j)
def BKs370_377 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs370_373 j) (BKs373_377 j) (Nat.ble 389 j)
def BKs377_379 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_393 (Nat.beq j 393)) (Bool.rec (motive := fun _ => ℕ) 0 BK_394 (Nat.beq j 394)) (Nat.ble 394 j)
def BKs379_381 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_395 (Nat.beq j 395)) (Bool.rec (motive := fun _ => ℕ) 0 BK_396 (Nat.beq j 396)) (Nat.ble 396 j)
def BKs377_381 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs377_379 j) (BKs379_381 j) (Nat.ble 395 j)
def BKs381_383 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_397 (Nat.beq j 397)) (Bool.rec (motive := fun _ => ℕ) 0 BK_398 (Nat.beq j 398)) (Nat.ble 398 j)
def BKs383_385 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_399 (Nat.beq j 399)) (Bool.rec (motive := fun _ => ℕ) 0 BK_400 (Nat.beq j 400)) (Nat.ble 400 j)
def BKs381_385 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs381_383 j) (BKs383_385 j) (Nat.ble 399 j)
def BKs377_385 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs377_381 j) (BKs381_385 j) (Nat.ble 397 j)
def BKs370_385 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs370_377 j) (BKs377_385 j) (Nat.ble 393 j)
def BKs385_387 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_401 (Nat.beq j 401)) (Bool.rec (motive := fun _ => ℕ) 0 BK_402 (Nat.beq j 402)) (Nat.ble 402 j)
def BKs387_389 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_403 (Nat.beq j 403)) (Bool.rec (motive := fun _ => ℕ) 0 BK_404 (Nat.beq j 404)) (Nat.ble 404 j)
def BKs385_389 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs385_387 j) (BKs387_389 j) (Nat.ble 403 j)
def BKs389_391 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_405 (Nat.beq j 405)) (Bool.rec (motive := fun _ => ℕ) 0 BK_406 (Nat.beq j 406)) (Nat.ble 406 j)
def BKs391_393 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_407 (Nat.beq j 407)) (Bool.rec (motive := fun _ => ℕ) 0 BK_408 (Nat.beq j 408)) (Nat.ble 408 j)
def BKs389_393 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs389_391 j) (BKs391_393 j) (Nat.ble 407 j)
def BKs385_393 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs385_389 j) (BKs389_393 j) (Nat.ble 405 j)
def BKs393_395 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_409 (Nat.beq j 409)) (Bool.rec (motive := fun _ => ℕ) 0 BK_410 (Nat.beq j 410)) (Nat.ble 410 j)
def BKs395_397 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_411 (Nat.beq j 411)) (Bool.rec (motive := fun _ => ℕ) 0 BK_412 (Nat.beq j 412)) (Nat.ble 412 j)
def BKs393_397 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs393_395 j) (BKs395_397 j) (Nat.ble 411 j)
def BKs397_399 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_413 (Nat.beq j 413)) (Bool.rec (motive := fun _ => ℕ) 0 BK_414 (Nat.beq j 414)) (Nat.ble 414 j)
def BKs399_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_415 (Nat.beq j 415)) (Bool.rec (motive := fun _ => ℕ) 0 BK_416 (Nat.beq j 416)) (Nat.ble 416 j)
def BKs397_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs397_399 j) (BKs399_401 j) (Nat.ble 415 j)
def BKs393_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs393_397 j) (BKs397_401 j) (Nat.ble 413 j)
def BKs385_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs385_393 j) (BKs393_401 j) (Nat.ble 409 j)
def BKs370_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs370_385 j) (BKs385_401 j) (Nat.ble 401 j)
def BKs402_404 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_418 (Nat.beq j 418)) (Bool.rec (motive := fun _ => ℕ) 0 BK_419 (Nat.beq j 419)) (Nat.ble 419 j)
def BKs401_404 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_417 (Nat.beq j 417)) (BKs402_404 j) (Nat.ble 418 j)
def BKs404_406 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_420 (Nat.beq j 420)) (Bool.rec (motive := fun _ => ℕ) 0 BK_421 (Nat.beq j 421)) (Nat.ble 421 j)
def BKs406_408 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_422 (Nat.beq j 422)) (Bool.rec (motive := fun _ => ℕ) 0 BK_423 (Nat.beq j 423)) (Nat.ble 423 j)
def BKs404_408 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs404_406 j) (BKs406_408 j) (Nat.ble 422 j)
def BKs401_408 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs401_404 j) (BKs404_408 j) (Nat.ble 420 j)
def BKs408_410 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_424 (Nat.beq j 424)) (Bool.rec (motive := fun _ => ℕ) 0 BK_425 (Nat.beq j 425)) (Nat.ble 425 j)
def BKs410_412 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_426 (Nat.beq j 426)) (Bool.rec (motive := fun _ => ℕ) 0 BK_427 (Nat.beq j 427)) (Nat.ble 427 j)
def BKs408_412 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs408_410 j) (BKs410_412 j) (Nat.ble 426 j)
def BKs412_414 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_428 (Nat.beq j 428)) (Bool.rec (motive := fun _ => ℕ) 0 BK_429 (Nat.beq j 429)) (Nat.ble 429 j)
def BKs414_416 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_430 (Nat.beq j 430)) (Bool.rec (motive := fun _ => ℕ) 0 BK_431 (Nat.beq j 431)) (Nat.ble 431 j)
def BKs412_416 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs412_414 j) (BKs414_416 j) (Nat.ble 430 j)
def BKs408_416 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs408_412 j) (BKs412_416 j) (Nat.ble 428 j)
def BKs401_416 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs401_408 j) (BKs408_416 j) (Nat.ble 424 j)
def BKs416_418 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_432 (Nat.beq j 432)) (Bool.rec (motive := fun _ => ℕ) 0 BK_433 (Nat.beq j 433)) (Nat.ble 433 j)
def BKs418_420 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_434 (Nat.beq j 434)) (Bool.rec (motive := fun _ => ℕ) 0 BK_435 (Nat.beq j 435)) (Nat.ble 435 j)
def BKs416_420 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs416_418 j) (BKs418_420 j) (Nat.ble 434 j)
def BKs420_422 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_436 (Nat.beq j 436)) (Bool.rec (motive := fun _ => ℕ) 0 BK_437 (Nat.beq j 437)) (Nat.ble 437 j)
def BKs422_424 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_438 (Nat.beq j 438)) (Bool.rec (motive := fun _ => ℕ) 0 BK_439 (Nat.beq j 439)) (Nat.ble 439 j)
def BKs420_424 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs420_422 j) (BKs422_424 j) (Nat.ble 438 j)
def BKs416_424 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs416_420 j) (BKs420_424 j) (Nat.ble 436 j)
def BKs424_426 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_440 (Nat.beq j 440)) (Bool.rec (motive := fun _ => ℕ) 0 BK_441 (Nat.beq j 441)) (Nat.ble 441 j)
def BKs426_428 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_442 (Nat.beq j 442)) (Bool.rec (motive := fun _ => ℕ) 0 BK_443 (Nat.beq j 443)) (Nat.ble 443 j)
def BKs424_428 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs424_426 j) (BKs426_428 j) (Nat.ble 442 j)
def BKs428_430 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_444 (Nat.beq j 444)) (Bool.rec (motive := fun _ => ℕ) 0 BK_445 (Nat.beq j 445)) (Nat.ble 445 j)
def BKs430_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_446 (Nat.beq j 446)) (Bool.rec (motive := fun _ => ℕ) 0 BK_447 (Nat.beq j 447)) (Nat.ble 447 j)
def BKs428_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs428_430 j) (BKs430_432 j) (Nat.ble 446 j)
def BKs424_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs424_428 j) (BKs428_432 j) (Nat.ble 444 j)
def BKs416_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs416_424 j) (BKs424_432 j) (Nat.ble 440 j)
def BKs401_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs401_416 j) (BKs416_432 j) (Nat.ble 432 j)
def BKs370_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs370_401 j) (BKs401_432 j) (Nat.ble 417 j)
def BKs433_435 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_449 (Nat.beq j 449)) (Bool.rec (motive := fun _ => ℕ) 0 BK_450 (Nat.beq j 450)) (Nat.ble 450 j)
def BKs432_435 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_448 (Nat.beq j 448)) (BKs433_435 j) (Nat.ble 449 j)
def BKs435_437 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_451 (Nat.beq j 451)) (Bool.rec (motive := fun _ => ℕ) 0 BK_452 (Nat.beq j 452)) (Nat.ble 452 j)
def BKs437_439 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_453 (Nat.beq j 453)) (Bool.rec (motive := fun _ => ℕ) 0 BK_454 (Nat.beq j 454)) (Nat.ble 454 j)
def BKs435_439 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs435_437 j) (BKs437_439 j) (Nat.ble 453 j)
def BKs432_439 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs432_435 j) (BKs435_439 j) (Nat.ble 451 j)
def BKs439_441 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_455 (Nat.beq j 455)) (Bool.rec (motive := fun _ => ℕ) 0 BK_456 (Nat.beq j 456)) (Nat.ble 456 j)
def BKs441_443 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_457 (Nat.beq j 457)) (Bool.rec (motive := fun _ => ℕ) 0 BK_458 (Nat.beq j 458)) (Nat.ble 458 j)
def BKs439_443 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs439_441 j) (BKs441_443 j) (Nat.ble 457 j)
def BKs443_445 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_459 (Nat.beq j 459)) (Bool.rec (motive := fun _ => ℕ) 0 BK_460 (Nat.beq j 460)) (Nat.ble 460 j)
def BKs445_447 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_461 (Nat.beq j 461)) (Bool.rec (motive := fun _ => ℕ) 0 BK_462 (Nat.beq j 462)) (Nat.ble 462 j)
def BKs443_447 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs443_445 j) (BKs445_447 j) (Nat.ble 461 j)
def BKs439_447 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs439_443 j) (BKs443_447 j) (Nat.ble 459 j)
def BKs432_447 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs432_439 j) (BKs439_447 j) (Nat.ble 455 j)
def BKs447_449 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_463 (Nat.beq j 463)) (Bool.rec (motive := fun _ => ℕ) 0 BK_464 (Nat.beq j 464)) (Nat.ble 464 j)
def BKs449_451 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_465 (Nat.beq j 465)) (Bool.rec (motive := fun _ => ℕ) 0 BK_466 (Nat.beq j 466)) (Nat.ble 466 j)
def BKs447_451 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs447_449 j) (BKs449_451 j) (Nat.ble 465 j)
def BKs451_453 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_467 (Nat.beq j 467)) (Bool.rec (motive := fun _ => ℕ) 0 BK_468 (Nat.beq j 468)) (Nat.ble 468 j)
def BKs453_455 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_469 (Nat.beq j 469)) (Bool.rec (motive := fun _ => ℕ) 0 BK_470 (Nat.beq j 470)) (Nat.ble 470 j)
def BKs451_455 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs451_453 j) (BKs453_455 j) (Nat.ble 469 j)
def BKs447_455 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs447_451 j) (BKs451_455 j) (Nat.ble 467 j)
def BKs455_457 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_471 (Nat.beq j 471)) (Bool.rec (motive := fun _ => ℕ) 0 BK_472 (Nat.beq j 472)) (Nat.ble 472 j)
def BKs457_459 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_473 (Nat.beq j 473)) (Bool.rec (motive := fun _ => ℕ) 0 BK_474 (Nat.beq j 474)) (Nat.ble 474 j)
def BKs455_459 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs455_457 j) (BKs457_459 j) (Nat.ble 473 j)
def BKs459_461 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_475 (Nat.beq j 475)) (Bool.rec (motive := fun _ => ℕ) 0 BK_476 (Nat.beq j 476)) (Nat.ble 476 j)
def BKs461_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_477 (Nat.beq j 477)) (Bool.rec (motive := fun _ => ℕ) 0 BK_478 (Nat.beq j 478)) (Nat.ble 478 j)
def BKs459_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs459_461 j) (BKs461_463 j) (Nat.ble 477 j)
def BKs455_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs455_459 j) (BKs459_463 j) (Nat.ble 475 j)
def BKs447_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs447_455 j) (BKs455_463 j) (Nat.ble 471 j)
def BKs432_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs432_447 j) (BKs447_463 j) (Nat.ble 463 j)
def BKs464_466 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_480 (Nat.beq j 480)) (Bool.rec (motive := fun _ => ℕ) 0 BK_481 (Nat.beq j 481)) (Nat.ble 481 j)
def BKs463_466 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_479 (Nat.beq j 479)) (BKs464_466 j) (Nat.ble 480 j)
def BKs466_468 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_482 (Nat.beq j 482)) (Bool.rec (motive := fun _ => ℕ) 0 BK_483 (Nat.beq j 483)) (Nat.ble 483 j)
def BKs468_470 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_484 (Nat.beq j 484)) (Bool.rec (motive := fun _ => ℕ) 0 BK_485 (Nat.beq j 485)) (Nat.ble 485 j)
def BKs466_470 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs466_468 j) (BKs468_470 j) (Nat.ble 484 j)
def BKs463_470 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs463_466 j) (BKs466_470 j) (Nat.ble 482 j)
def BKs470_472 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_486 (Nat.beq j 486)) (Bool.rec (motive := fun _ => ℕ) 0 BK_487 (Nat.beq j 487)) (Nat.ble 487 j)
def BKs472_474 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_488 (Nat.beq j 488)) (Bool.rec (motive := fun _ => ℕ) 0 BK_489 (Nat.beq j 489)) (Nat.ble 489 j)
def BKs470_474 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs470_472 j) (BKs472_474 j) (Nat.ble 488 j)
def BKs474_476 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_490 (Nat.beq j 490)) (Bool.rec (motive := fun _ => ℕ) 0 BK_491 (Nat.beq j 491)) (Nat.ble 491 j)
def BKs476_478 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_492 (Nat.beq j 492)) (Bool.rec (motive := fun _ => ℕ) 0 BK_493 (Nat.beq j 493)) (Nat.ble 493 j)
def BKs474_478 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs474_476 j) (BKs476_478 j) (Nat.ble 492 j)
def BKs470_478 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs470_474 j) (BKs474_478 j) (Nat.ble 490 j)
def BKs463_478 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs463_470 j) (BKs470_478 j) (Nat.ble 486 j)
def BKs478_480 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_494 (Nat.beq j 494)) (Bool.rec (motive := fun _ => ℕ) 0 BK_495 (Nat.beq j 495)) (Nat.ble 495 j)
def BKs480_482 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_496 (Nat.beq j 496)) (Bool.rec (motive := fun _ => ℕ) 0 BK_497 (Nat.beq j 497)) (Nat.ble 497 j)
def BKs478_482 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs478_480 j) (BKs480_482 j) (Nat.ble 496 j)
def BKs482_484 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_498 (Nat.beq j 498)) (Bool.rec (motive := fun _ => ℕ) 0 BK_499 (Nat.beq j 499)) (Nat.ble 499 j)
def BKs484_486 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_500 (Nat.beq j 500)) (Bool.rec (motive := fun _ => ℕ) 0 BK_501 (Nat.beq j 501)) (Nat.ble 501 j)
def BKs482_486 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs482_484 j) (BKs484_486 j) (Nat.ble 500 j)
def BKs478_486 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs478_482 j) (BKs482_486 j) (Nat.ble 498 j)
def BKs486_488 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_502 (Nat.beq j 502)) (Bool.rec (motive := fun _ => ℕ) 0 BK_503 (Nat.beq j 503)) (Nat.ble 503 j)
def BKs488_490 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_504 (Nat.beq j 504)) (Bool.rec (motive := fun _ => ℕ) 0 BK_505 (Nat.beq j 505)) (Nat.ble 505 j)
def BKs486_490 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs486_488 j) (BKs488_490 j) (Nat.ble 504 j)
def BKs490_492 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_506 (Nat.beq j 506)) (Bool.rec (motive := fun _ => ℕ) 0 BK_507 (Nat.beq j 507)) (Nat.ble 507 j)
def BKs492_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_508 (Nat.beq j 508)) (Bool.rec (motive := fun _ => ℕ) 0 BK_509 (Nat.beq j 509)) (Nat.ble 509 j)
def BKs490_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs490_492 j) (BKs492_494 j) (Nat.ble 508 j)
def BKs486_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs486_490 j) (BKs490_494 j) (Nat.ble 506 j)
def BKs478_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs478_486 j) (BKs486_494 j) (Nat.ble 502 j)
def BKs463_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs463_478 j) (BKs478_494 j) (Nat.ble 494 j)
def BKs432_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs432_463 j) (BKs463_494 j) (Nat.ble 479 j)
def BKs370_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs370_432 j) (BKs432_494 j) (Nat.ble 448 j)
def BKs247_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_370 j) (BKs370_494 j) (Nat.ble 386 j)
def BKs0_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_247 j) (BKs247_494 j) (Nat.ble 263 j)
def BK (j : ℕ) : ℕ := (BKs0_494 j)

theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel

theorem blk_0 : Pyr.allFrom 0 63 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_1 : Pyr.allFrom 63 8 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_2 : Pyr.allFrom 71 50 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_3 : Pyr.allFrom 121 39 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_4 : Pyr.allFrom 160 62 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_5 : Pyr.allFrom 222 96 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_6 : Pyr.allFrom 318 194 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by
  have h := (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add blk_0 blk_1) blk_2) blk_3) blk_4) blk_5) blk_6)
  exact h
theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 39936, false),
  (39936, 40000, true),
  (40000, 40064, true),
  (40064, 40192, true),
  (40192, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 434176, false)]
theorem cover0_ok : PyrT8.coverCheck 25326800 (SC / 2) 434176 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 74752, false),
  (74752, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88320, true),
  (88320, 88448, true),
  (88448, 88576, true),
  (88576, 262144, false)]
theorem cover1_ok : PyrT8.coverCheck 48244400 (SC / 2) 262144 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 60416, true),
  (60416, 74240, false),
  (74240, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 89088, true),
  (89088, 237568, false)]
theorem cover2_ok : PyrT8.coverCheck 52857300 (SC / 2) 237568 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 74752, false),
  (74752, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88320, true),
  (88320, 88448, true),
  (88448, 88576, true),
  (88576, 262144, false)]
theorem cover3_ok : PyrT8.coverCheck 48244400 (SC / 2) 262144 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 39936, false),
  (39936, 40000, true),
  (40000, 40064, true),
  (40064, 40192, true),
  (40192, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 434176, false)]
theorem cover4_ok : PyrT8.coverCheck 25326800 (SC / 2) 434176 cover4 = true := by decide +kernel

theorem wk0 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 8803407355216322864250380443845930125127263092462753321878488666875902059190372450977312753359948729395577331303852871008634641307192607180065800732225449880922817548296917560596180747749757440705668405682026648891921246672976970995337697955127521440002587172665910487410366802158551188045060589931488077017921284505638045878392258703528547981451230320289296330185391882786 21 30720 39936 31744 38400 31744 38400 31744 38400 30720 39936 1247 (by decide +kernel) (by decide)
theorem wk1 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 174197801677684951647036566506476917493857965747583116579794265037618286256382588648237505591117148452562543673445396901432058487828900071024342210679594632843417720395772985707357701507062815182461920379523059508491648880745977437537371225660199086231716839154809831034781839124822271470232079053694177339538554637205051021688476291453125958234722331570045359586783341285807343164414015665602153263682732193010936446863592633944581327884950859007664618986986664230618695650346317212035044520023410593283963336900600835903930957246155417194121675068241566563308699499957922234380452927829668430886537036546070983975449683362770855042733048716815939729424343648602833713935597473836537380649262880435901904728806917065960784761988764178224441791878802892009426855493052124999888241034818853609207917885997697559078285238240540149085312348114079421473849012258013813740569056091214937736957239278910151248791014182922198113136539275033924506765061186147120200126835105818650173905155863346 26 30720 39936 31744 38400 31744 38400 31744 38400 57344 434176 3287 (by decide +kernel) (by decide)
theorem wk2 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 724654987021757899778607335745650408834709395851773966623621717954190488705866053167622534488349909918942879901179992418275789868219237685341396594715435327454411496279256626961925823275097078034958799407996925650933278759499713527276048347318933157289652439350235221478764333818807703822540751051996292168666239113175449647700777638223123033641696148214477406134495062189840745408724150686589368860587328164390693930628112557971992976013745831720864363174036683319711630508493815168746039643014761226869648410546081860840850234862760446834360858372139824172387338295386123959745795429203603964429430338790409144736127523821378495692444800202698697510528369219772992734095294274161863914377305854624982566969910011310253863574618969333810441915668324182861903018016171279424058831113153639687460541679911055205082375097591700897215532028664796984102813423194361582 25 30720 39936 31744 38400 31744 38400 59904 74752 30720 39936 2877 (by decide +kernel) (by decide)
theorem wk3 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 338469491533500347552765995177874037761712754642571806774915825353990179218793214495394762470797700278335558945724850874921579692298054299304231294462393962429078917056105361208345850077250692175648774044167170870155499059604431067339393445663212334075642666061102485600264903929918255531285593591290075346357885657598388944103292774509105032469762553726575965139333477458421869445339479556513061728648476453435502047571381016345226254500812613760902913649532058435851632749680371711016967325672109773951182074951102765880627990405368645437941640198484909431943064784050117774000547703834101529053529284595675372539608105208382555227719727874952817807418003218342428315990955802160503588343232025124834226392559982568331782302337528541194306181673334108331321347410464907651591461169020234475685745377958541334857805478172284563766024444304737974143667863943590187181527051115629133835645955761509854153609576319491532209457319558777696757726723539054472073863488259157959178458444594 29 30720 39936 31744 38400 31744 38400 59904 74752 57344 434176 3272 (by decide +kernel) (by decide)
theorem wk4 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 371118927258623828730740088128753063286709686149162799261718985793876257865217513249988346320099654204273028022503992020445560269510522529078451316315155100404230077467579354775286300870680023486388255682168203266899467481654720166184786091640711874121615275195764588980721395472992743706870281855884744888540559025850058538170327915091096809557679175815854647902981261765937124762151788932846 25 30720 39936 31744 38400 31744 38400 88576 262144 30720 39936 1312 (by decide +kernel) (by decide)
theorem wk5 : PyrT8.Covered 30720 39936 31744 38400 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 1283128239939926780414750962859837396587956279292486179711010796635138411727631094185881006342279063827097394025051977968692180646363291210151893354238207294458919861495881338740158370070125443463818438563641419176880220016376309361849276420610912554191090418 28 30720 39936 31744 38400 31744 38400 88576 262144 57344 434176 872 (by decide +kernel) (by decide)
theorem wk6 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 37943528928780361014614478996775856475142048686630817807901005597487969907805203781496036590729514494929710289876408499436652107032801416963600963240354952465120049597732516390700748140982624690212882373148470549840866625152414167824831047074139761586562648053043120811822579842103300094247039984874763480943901177595411100688144705838722272166394852287175939899140832372414269710708313802976346714866549428637187541175127108296044664908441501000838984295746629331159793573112824282446701173871839775262462352669467241280702889452665459335904934293402756318145570388951943469753149504131647636446730460674069452611329670673730509309432576843794484103426818096902747731421897040939187912621321234692870092227369191397357262943199075989202779670358411877594711937938932596293011251812837744620780646737932665576957896936962993829577794041047164459349156631285037748180372875788697880830231624871400128424319088760910975970572288143240029246265888426200561823149633140190063116962474 25 30720 39936 31744 38400 60416 74240 31744 38400 30720 39936 3262 (by decide +kernel) (by decide)
theorem wk7 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 787942549896667687282710464510085934313068686317513100831252632673554445937550423945738781035649985002635472998965096686476079355210185753996003758271355155136297012459031637185114311261302440685943100057461712425460718472373727837801972818971639919053746606839252608881362119096289365258156056912769112154742084817119059095233822149854640182250612101433032265853263913815020153566996380988235008122379415159214954825478868913586135397337166505184781557857543486605867601362790389588492087825262593317602144150939002699371744959578910388152824282212411073012101930790243897621660175224836603179020975163228181225805301718118410123240501786135058679858857118530963020849980882591521241250692569897655246137313006783444850207324752564611519493461465564691436840795781650356891243285809496742386819114293750599854746074080799536208553614630248649364424977865468042907112917807626369571244157848907521191476365576834482660650847458207279368242309179542305445697889117261499240331924319138829574731722126785527170064573195866306262083493556523550818790826429051725146943517547897623715487156581460224576750874912408083949226391861241310379123655685947815620561471945800121223698971006954120298823482667830140364370742015329167270086080196237055560191081816786672927326776808364635348640311016752657249168421528262967814077971115156768793367011747268295896254407112768134957578357521010745837347160442938365219190303351424632327109562668156230790425504022142468374546235885384047127690052336970365622098507065968633748456179915441640256306 31 30720 39936 31744 38400 60416 74240 31744 38400 57344 434176 5097 (by decide +kernel) (by decide)
theorem wk8 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 5426684256338301846123273058886203265742063210294123931082823592022417135993110957548744319977306103494210386791323613692360823783405207277892161156597433221249777238981915824611298128285924350978073644176787019046103118120983726961579203379174327833271712072735111475679609654570450410722031112526357897696619084385962749843981171400080316773992338996246745992857296202011899996739706185618521002995328735649956696485348612797918910484417018467098840067572069066961576719130807404562548156883143805243773001542422152678581594552428282136161592337921131504060858602140518377893920037815194111613675202295274107678151643919813759844557796717326535931398234953630367825434075984956644136247223707631106474371610803941686605247114161834 26 30720 39936 31744 38400 60416 74240 59904 74752 30720 39936 2442 (by decide +kernel) (by decide)
theorem wk9 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 255331825858418837903570045083778022435048730917004047746698899177620109490278917746513894199453962353617006856278638058432490133495107669505231676437206693116000943541717234450820835946736974478330747204810997245641885834940062441245203819811969450589738239106370794827311186667143230086366933840213918441014028127122226 27 30720 39936 31744 38400 60416 74240 59904 74752 57344 434176 1072 (by decide +kernel) (by decide)
theorem wk10 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 252640476469373416321566591761937900163820853329778268825186140986213935140529752546249225168197693166 21 30720 39936 31744 38400 60416 74240 88576 262144 30720 39936 342 (by decide +kernel) (by decide)
theorem wk11 : PyrT8.Covered 30720 39936 31744 38400 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 356774869281344030919206564594 19 30720 39936 31744 38400 60416 74240 88576 262144 57344 434176 107 (by decide +kernel) (by decide)
theorem wk12 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 2840959290184462538763610812037885482547687597116223462409040712947594051044721326294667065136884420585829622955455174972911314643930653898025531122404514840111101256088248350068807483222956716692099328687600046097337112296552797910625675930601905193294426613456895367630644454826630339211658278942282802505003542395873119036092884069034 26 30720 39936 31744 38400 89088 237568 31744 38400 30720 39936 1127 (by decide +kernel) (by decide)
theorem wk13 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 14553283121372232787166214136937577387377799390161776887396580454144852140992497074012515879168381690855033775347259018023960105427079456108137031529989187042991450617895836205139592373553669745249764022100376231995562185070391986 28 30720 39936 31744 38400 89088 237568 31744 38400 57344 434176 772 (by decide +kernel) (by decide)
theorem wk14 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 31935390142311017482269988910079757965828982981971995536824775980350368426 22 30720 39936 31744 38400 89088 237568 59904 74752 30720 39936 252 (by decide +kernel) (by decide)
theorem wk15 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 348574109191577415247901362 17 30720 39936 31744 38400 89088 237568 59904 74752 57344 434176 97 (by decide +kernel) (by decide)
theorem wk16 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 4008357550 10 30720 39936 31744 38400 89088 237568 88576 262144 30720 39936 42 (by decide +kernel) (by decide)
theorem wk17 : PyrT8.Covered 30720 39936 31744 38400 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 31744 38400 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk18 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 34359462441680531715669577411444440634973785855878507076954339298417942506152070750138341206265560541111640868850407807041501254948416983756664855438699103214759030799748338341907211620600193237736436613757279876929852145227703488329368149562086311117559600211795967415212254766264297882008900711775639309801741082176462726116358188651547168168630342311993811891961866841596345631217000558646934541175274855935750176556296726146540173146890257187994602606747830728817148972965414564944787584553383461071617090329768426861500638108196323890492621008557598637486379300277006689010650265756111067907496530802180558389516534494269925503722044512938368364414724298521753635188427799747378750358050511757806561667928749488293620892567251668106616876506246164459102169369609311332706635621467875517848582286790248038 25 30720 39936 59904 74752 31744 38400 31744 38400 30720 39936 2692 (by decide +kernel) (by decide)
theorem wk19 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 1331081003779210651982807241735879822917601792463323420687514930961851155575814085532396224160547124434295680405613400267649060175364131512075632391832884246830804534434991971168715455594625857474099443422402857531058091704899020282708245182981717683494125241964262580066786432341130729087378770841487486500875126170410555476047476357297364587148451113179248608407514673216934670374297778641763106019358696981044790896363657843014383025176070797337296569125118010123869462879066288789748898266330791270809941506501334599371160813077074262620991794191189709979679135399545507896889602145841082468734110107350840736139580641624178021983693806542420549674071898861888930126440784087650273318721343997606821153740320407720939705211826563074456182614414630312419058386214808039739356101387885428832659031106601906740044424376309331106418071124211197509528879177570876323475231587566026544660361126909565607166172808360051183598188888594374996198264703113198705039361067117845328669035658090782473574597055367186961818409692696428144205068159073938543367955749228736665810776333742283932877552646112368673634651027435569237411757439743146990117390431079364193591224922277186442399612005134281875198017419490132057176579401708502671536156075850872136914594530248073292340381852972228962703512956128047022596554180955166695722282317979820364440629737290930913541096072242025910812977353027284996396396808875483365820862199412703205234177449457140098536991049255701081484714429848640604607536696332466849935330361894816625806065907715992160004564061161658247286690780354319427412855588586287623484439056045257568933573094093608475374233885693600148321635359386828454409606904162147796052766665207046326231132288392130680110272072399852040562053459635174377097568232489963850116590392371069409803309609030480422056746615888940844734674125126176240212133638097604257002532322601034079510453352950865454867920386965901581879365016976816720670584191484296448172605231959738893739904726488957976405032643201087152709772672349122531470724756489319218 32 30720 39936 59904 74752 31744 38400 31744 38400 57344 434176 6762 (by decide +kernel) (by decide)
theorem wk20 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 348583475495205322809650804627414900746625733623009210562453985009169968326589716727052821814612903740218394813727346347280649496868099511539292357016906396094174456589261546625719833154244273193308015067305406194089597919765307513473906627860238492509160939458931701208286693646094308930750114899061529981313853141683744725549985637533400878129844605657567593868209218277385281397920415003976885376023376468307737888864167566085684392510921606354035872512711507263334553306569138280516485772296340324243168372820285225512757059474878853696390680180795591534566537603968015442920689254022978706393816785634976470792098774813921558121743688116553895993134158790752803251504186211214531119844791455124553748856818685646335314067925758016913360791417987778400749632275351278567491934055149029000448617806944638999174339033572756829040291729014777906717460847203932258983291505868314865875940021709792805466255401797417726999075592540767975327787275324338077720314125316524965374598974012191274959435919388477234879781424104843918126033480784055581995596180828820555480749719162896820353151084632824212482406344876364658538409827412413357609001381083317380635328550359142296219224188525106613177187569119894075001768602716670640515778419624306577233921277643420355474052042703973226737197310121194492576795457019016088791111582555136930511789137686903450896360983982281507017738596523955849542272896392498297512775373254821848103845181986776998064019697145195517301050174912797560017242628075403004578876803324916093599933207883746148364507545623632114143100789882313405357658497559123683314525331046154317873174132419306861270740237231653342435373962831853206087788060079924057679437664996288072163928185461863664436770627534728278516213023090151304246887773562453308821143756960540577699601047602159478207844316197637189924371389185869058393428584361441836072160511599555942669285294028652083354273870000658883894930125506361063794167900968909115172019561771341743800334688471668754421127861835240523176366726509783778256314798595906360727473137092265671184681970698370364035726031585803530020225694552356240802395548949403704339548749993782213944736231127669602019670107992413754650225151477196337101409843360927138446635355535591115572008682908196049243789221411016140454692432942098617800673268171177648180299886698155125488601589214912620069464319077661991345797085380667552650911723094031648455491584454449154729657309628901289834126736462769182792733283581042352816897498757658723669214348902 30 30720 39936 59904 74752 31744 38400 59904 74752 30720 39936 8297 (by decide +kernel) (by decide)
theorem wk21 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 1307429988668513631978204204507180259246613230903109252734867255328640489946326183273056641248086626868944175020028103741144219433960370488019998009945264828138999266850105129925971200720039921505670368152833860212983530235969973846109042819078151661190580625070561286340959910946486373165520762553495232948375315767164106164751197626235831050875624281083503521354522526018787847301339645614572835339900352439854249548355695467057287830488097400344850368806439367798186119031394451668199225139743862450805875871255646061342860701809182752211008938703008875373796647946853414949322196014399037548804060590469435228615865621194004468664050411437350235621728001012393234334079925181572199762180602239328008384192046610687887406558874240678875588011851005055723837730774179283502360223586009407103534660743416809175145122025507825704301236448557725501234555193201515557393344584196934257129283067806141524952614528741219677192071301010730702028598930644744677074623836983262639173101757013843796526956698081808327799258446119157068565803656418186924971408776890628026416080022808217706393998555094100488415623381201714 33 30720 39936 59904 74752 31744 38400 59904 74752 57344 434176 3707 (by decide +kernel) (by decide)
theorem wk22 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 19908900373132068648093600806583054735781739969811411743132673717296778370305350913668102465811882438986982324369025953296382111635650313138137087766912265744127865109793981957728892434891144977490760824729377767321326 26 30720 39936 59904 74752 31744 38400 88576 262144 30720 39936 727 (by decide +kernel) (by decide)
theorem wk23 : PyrT8.Covered 30720 39936 59904 74752 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 71475721996085591998143781788478452821848818 22 30720 39936 59904 74752 31744 38400 88576 262144 57344 434176 157 (by decide +kernel) (by decide)
theorem wk24 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 30331381482620730684815623043918815629016402117358133118038381287415044923200321749998370822250298477909259943039188551214977332783395916726833841298910418758488080580077807756286417394174545484244531997072364181318623696973413998492731024632201709883013222517820019161469295763673172956067097283788303937816656145761083718192174487025976155097481721589322124067592342681854231559532356388372108844123738723394265089780750816838524001819005930787591478718466455642249549702751063568863297127204680333604619959295128893870902753326683881215903036863027709785815828197501681944515280724835991118341268370690893856791599212458298754836616424462649932928068845467959870763083434 26 30720 39936 59904 74752 60416 74240 31744 38400 30720 39936 2242 (by decide +kernel) (by decide)
theorem wk25 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 38053604649607186295096275884084434427320932429428251145195111674431070790866317412233789289286959471829079395549924055828872881066808932244899706561857478235653152984861021713081735340854213740058600994963872956082405705715340658573182738671102515359463245843220153141489879547768251255881925003477695362238448702097826998412481211781816115162329301603816185954115187289456865649129980250159255884642037552586255584665679540411593697849818715139804975702419614574856980794984768516128503342982359501407482741561734125451243024798892914708390010868782825556502792399425270285235580856309358143434775544461883790192684076216837061445445717456415392978001347138119441843894175609396885970239178876652273826606158368317445924284513448635764589629056149956170839598660725615387872495229233061068566107919886179312394154969477946643276777759494029648264748175718139887242588441774991798009746596155162015070465599058162950221572530670239804811707850887978496818 32 30720 39936 59904 74752 60416 74240 31744 38400 57344 434176 3182 (by decide +kernel) (by decide)
theorem wk26 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 9796036528250264894517716750728998966196288007016336995099712009512682190942512692145332150844164512723339567647984958011393285335319796922033531750785010921298776036437550631304603738812530776418198666350218410 24 30720 39936 59904 74752 60416 74240 59904 74752 30720 39936 707 (by decide +kernel) (by decide)
theorem wk27 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 2854199096641929390606546842418 18 30720 39936 59904 74752 60416 74240 59904 74752 57344 434176 107 (by decide +kernel) (by decide)
theorem wk28 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 214609646 9 30720 39936 59904 74752 60416 74240 88576 262144 30720 39936 37 (by decide +kernel) (by decide)
theorem wk29 : PyrT8.Covered 30720 39936 59904 74752 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 59904 74752 60416 74240 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk30 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 3548500256672579547581662214164681695986625839408413201333261233776126634 22 30720 39936 59904 74752 89088 237568 31744 38400 30720 39936 252 (by decide +kernel) (by decide)
theorem wk31 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 10882869176106555571614386 16 30720 39936 59904 74752 89088 237568 31744 38400 57344 434176 92 (by decide +kernel) (by decide)
theorem wk32 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 420522 7 30720 39936 59904 74752 89088 237568 59904 74752 30720 39936 27 (by decide +kernel) (by decide)
theorem wk33 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 59904 74752 89088 237568 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk34 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 59904 74752 89088 237568 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk35 : PyrT8.Covered 30720 39936 59904 74752 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 59904 74752 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk36 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 2697697231925886883853222538684437651430602029739607097070762272562127561652314828340511868328376671598108026932222087496323547165511030889338453005151766115382084538228861951016575414291451368849643558664856835978086560179161382347293022022103249136694969934627594072234805345180137901855038922532395272177103583778450675270042987837347869767808579178606127783241318 25 30720 39936 88576 262144 31744 38400 31744 38400 30720 39936 1222 (by decide +kernel) (by decide)
theorem wk37 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 22031769154308680724901933284879816343047955436829596834320294700498183595605010870039059498287355230165747163767460680457296099512326072477073458156520694649633947851134542019806464141176486136520531730367341272906186310791299396364214091526111202391787729012155072848487346994669949748568039511816994276131171115257875000623202071873355396066233843066500545604488130049589255548244750962 31 30720 39936 88576 262144 31744 38400 31744 38400 57344 434176 1307 (by decide +kernel) (by decide)
theorem wk38 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 8532878439777564802550295705595002702262725701887763045195133693194690958712877693689328697317966109907715516174800433642736377005566470397137162962482403298917791358439848877650742274321228113495250569632912547702374 26 30720 39936 88576 262144 31744 38400 59904 74752 30720 39936 727 (by decide +kernel) (by decide)
theorem wk39 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 166254251965102830024732620315724190315606642 22 30720 39936 88576 262144 31744 38400 59904 74752 57344 434176 157 (by decide +kernel) (by decide)
theorem wk40 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 1702533457638 12 30720 39936 88576 262144 31744 38400 88576 262144 30720 39936 52 (by decide +kernel) (by decide)
theorem wk41 : PyrT8.Covered 30720 39936 88576 262144 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 31744 38400 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk42 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 3227570228123061314653467335864998491785642141357176233379210851271282339661337093638581823078 21 30720 39936 88576 262144 60416 74240 31744 38400 30720 39936 317 (by decide +kernel) (by decide)
theorem wk43 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 357103697103981409529358348914 19 30720 39936 88576 262144 60416 74240 31744 38400 57344 434176 107 (by decide +kernel) (by decide)
theorem wk44 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 499820134 9 30720 39936 88576 262144 60416 74240 59904 74752 30720 39936 37 (by decide +kernel) (by decide)
theorem wk45 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 60416 74240 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk46 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 60416 74240 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk47 : PyrT8.Covered 30720 39936 88576 262144 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 60416 74240 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk48 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 1718265510 10 30720 39936 88576 262144 89088 237568 31744 38400 30720 39936 42 (by decide +kernel) (by decide)
theorem wk49 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 89088 237568 31744 38400 57344 434176 2 (by decide +kernel) (by decide)
theorem wk50 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 89088 237568 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk51 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 89088 237568 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk52 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 89088 237568 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk53 : PyrT8.Covered 30720 39936 88576 262144 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 30720 39936 88576 262144 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk54 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 31744 38400 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk55 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 270578364929754946103207079805287528268677850461544178323203454355169788161070889044786240295462118734962512425402539831684283962589956241326166840637927435629892669084541745639574974180468432242508651014505813362579785620824163463739927660384984339666843379030699303177995854083129445188551537414994898957855151893375567083970730073013461208219128948207985440645104873831842334486850110094181233563312922014003688831179465116090906607478783872368714062009685051149520831953112280461745894911349283592132812569921227660012579339936398690171564633869201733189981274822523957381557107534654583005949162300271296347646204980831115594458817242364771816732074007616710396525471342468531399334904284771060401410453747962715097760973289341382739585198403849586945538854361110115080183029135175110192720776884427791853195873436961164156341672533206487630377360288605287757877695687832257208783191873990384713684940517821266945495258009021018210700018763298021143287563446133546180711919204522844020068333789996523366499828448217811218625354424451694338734033730047181693785807934130166474904682289021828434665740870430322152526974413906722 31 57344 434176 31744 38400 31744 38400 31744 38400 57344 434176 3762 (by decide +kernel) (by decide)
theorem wk56 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 31744 38400 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk57 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 4579569985769649123241499963221281001455290382541976378729277379758179193706808222024880129046251101405865934575710112972525807861642043134992675921096170723408993732366643890710513223508855583595829319148688581789833411961367468949373556811021559292346572584139520624959919856968661811075557412491980775324549709278107955702395366937118608529641255219463544469921570982845045254298709451944218268304478703646851797775786796354812197759935193127519164879636198848579246699816899568046038414772124690780851014411414937733213525988725850203451678372477424064058648273018428124551139908940276328689505628555959851100505855112000245572341314140716790472542058546359456060693474733197525588551002404646228808577231384505325731997757072638946959978840049870251193084780352124622924511825279693707951907033815422404013374662752543589362138528500686883013805147505240897403828213275272741185390161456717423739077579681977838868888784922416752008988799505556546150721699644966851826162818517568624045387560672234057657303666490018433773760925072012272460605104930 35 57344 434176 31744 38400 31744 38400 59904 74752 57344 434176 3507 (by decide +kernel) (by decide)
theorem wk58 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 31744 38400 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk59 : PyrT8.Covered 57344 434176 31744 38400 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 76253967346423407912172644787162225144988231297377497793229304773625090217093221052351836729122 30 57344 434176 31744 38400 31744 38400 88576 262144 57344 434176 327 (by decide +kernel) (by decide)
theorem wk60 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 60416 74240 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk61 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 31920132859228472171369348774562950702228592811262190462461292761496467781001729770377868964666669968521635949990417925034353905378068178001985493852257716356777432573400351852940969334735346299822709145837269511521870880731574184347505907111197096400311494691189551183362660411532282781934898886148588068589497712964423156124364422127758462491456646936136404234065047247562706727269913897564852540639718732471247723783023822868179108975010047835768121668437599608092964031937552227713316519400283307194823320057880606068269335616442189914634963669611063125934047944264930668117423411102718390562334637557519533109431725047808092498099797680090737365538829415420694622847473187858326219318533609013478747017677374455370351305966169621777494890819589006017096453832231225968327102707522238514893140567432269349551797600573319928667182391665714016653209405187480594135763502092186267258913633992002937432138398739002465969020941519049778935269123832736774295039207711559968726704924234101781830173829008459768346908513500680626314429291125967178989903492368715260620365823155717188674959311644055535373286992884529383604012172561801766613123060109987378413479869269350536579696878603136368071707324773664290426445765315907477793725105709878417307422693056310074993074184972363917427148813085613497113516063108100051403223533637689734461710874285952903246031711119573813854399497622925017515100823502936066460647440719670172933113845870725290009841441310659143360834408963224364794379766801885400929633269287676630189491705397870769591814142186861247989971083844547346777106159505304314853978803817007106855116769534977553641824496773365009430818633972829891741730687979767174442201804236254656363020616369284647251885634127476733484082602786 38 57344 434176 31744 38400 60416 74240 31744 38400 57344 434176 5782 (by decide +kernel) (by decide)
theorem wk62 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 60416 74240 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk63 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 13609420450189582914172746740446919295281715232973156710400304589842396903420837770891866610722054365906762243936387076618912449139998663458 31 57344 434176 31744 38400 60416 74240 59904 74752 57344 434176 472 (by decide +kernel) (by decide)
theorem wk64 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 60416 74240 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk65 : PyrT8.Covered 57344 434176 31744 38400 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 37585845104418 14 57344 434176 31744 38400 60416 74240 88576 262144 57344 434176 62 (by decide +kernel) (by decide)
theorem wk66 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 89088 237568 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk67 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 65363915337402839674624068308039911779024112990898810048260786440920397654818 30 57344 434176 31744 38400 89088 237568 31744 38400 57344 434176 267 (by decide +kernel) (by decide)
theorem wk68 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 89088 237568 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk69 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 89088 237568 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk70 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 89088 237568 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk71 : PyrT8.Covered 57344 434176 31744 38400 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 31744 38400 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk72 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 31744 38400 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk73 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 2988307517638786846071255378981629857725855899124709700806799029491967264480036138721928372300959197335152044356715564328274666681195890490623267977772509656240082497782336013394012145029193378009458745820950405108838035228182114108301421756269397274425386069037845018304215985688483364439133097138714628443852127872604501373251168171891043168567299709174055491399791198941386012282388153631483823553123949427186335197934290390520904383183474703515701403301145080218148151037764242278781454667005197062657942554193577167016166400205033823790338809852792929218458647640287479000764207790883691868572832923933123529221243297625386982811271590986880845714047008493463721226475376317102990207473762393859063948658564179759338422049128990310979270534314124189966484460051004605131172028810951190520437956744423383308563627577931522328768756681297871469725980034547975065780487292485026361112171166808532368889585805532500381128151945435111905602963843691690889628516757493237367536458271623702002589180706 35 57344 434176 59904 74752 31744 38400 31744 38400 57344 434176 3327 (by decide +kernel) (by decide)
theorem wk74 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 31744 38400 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk75 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 846035080159694355926444107405881672590115161053991218357494807780289085569584610046657375330344226218239305791866242966089533135735369486533450934774907795502295379369955035231902488918289455545158685523577809429814919242530 34 57344 434176 59904 74752 31744 38400 59904 74752 57344 434176 757 (by decide +kernel) (by decide)
theorem wk76 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 31744 38400 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk77 : PyrT8.Covered 57344 434176 59904 74752 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 2766373656957431586 17 57344 434176 59904 74752 31744 38400 88576 262144 57344 434176 77 (by decide +kernel) (by decide)
theorem wk78 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 60416 74240 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk79 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 425294383162636508970659844152414463430305687159876816847268427259136925727643951354812572206094473062716071780907552517199151229755925282 31 57344 434176 59904 74752 60416 74240 31744 38400 57344 434176 467 (by decide +kernel) (by decide)
theorem wk80 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 60416 74240 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk81 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 9179439906 11 57344 434176 59904 74752 60416 74240 59904 74752 57344 434176 47 (by decide +kernel) (by decide)
theorem wk82 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 60416 74240 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk83 : PyrT8.Covered 57344 434176 59904 74752 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 60416 74240 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk84 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk85 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 31744 38400 57344 434176 2 (by decide +kernel) (by decide)
theorem wk86 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk87 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk88 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk89 : PyrT8.Covered 57344 434176 59904 74752 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 59904 74752 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk90 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 31744 38400 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk91 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 76186745156610943447304962108653780344478256756117196239389300623557709778202288644690411661090 30 57344 434176 88576 262144 31744 38400 31744 38400 57344 434176 327 (by decide +kernel) (by decide)
theorem wk92 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 31744 38400 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk93 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 2766373622589302562 17 57344 434176 88576 262144 31744 38400 59904 74752 57344 434176 77 (by decide +kernel) (by decide)
theorem wk94 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 31744 38400 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk95 : PyrT8.Covered 57344 434176 88576 262144 31744 38400 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 31744 38400 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk96 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 60416 74240 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk97 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 37551476975394 14 57344 434176 88576 262144 60416 74240 31744 38400 57344 434176 62 (by decide +kernel) (by decide)
theorem wk98 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 60416 74240 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk99 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 60416 74240 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk100 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 60416 74240 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk101 : PyrT8.Covered 57344 434176 88576 262144 60416 74240 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 60416 74240 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem wk102 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 31744 38400 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 31744 38400 30720 39936 2 (by decide +kernel) (by decide)
theorem wk103 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 31744 38400 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 31744 38400 57344 434176 2 (by decide +kernel) (by decide)
theorem wk104 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 59904 74752 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 59904 74752 30720 39936 2 (by decide +kernel) (by decide)
theorem wk105 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 59904 74752 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 59904 74752 57344 434176 2 (by decide +kernel) (by decide)
theorem wk106 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 88576 262144 30720 39936 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 88576 262144 30720 39936 2 (by decide +kernel) (by decide)
theorem wk107 : PyrT8.Covered 57344 434176 88576 262144 89088 237568 88576 262144 57344 434176 :=
  PyrT8.covered_of_walk lbS 0 2 57344 434176 88576 262144 89088 237568 88576 262144 57344 434176 2 (by decide +kernel) (by decide)
theorem bd0_0 : (PyrT8.badOf cover0).getD 0 (0, 0) = (30720, 39936) := by decide +kernel
theorem bd0_1 : (PyrT8.badOf cover0).getD 1 (0, 0) = (57344, 434176) := by decide +kernel
theorem nb0_eq : (PyrT8.badOf cover0).length = 2 := by decide +kernel
theorem bd1_0 : (PyrT8.badOf cover1).getD 0 (0, 0) = (31744, 38400) := by decide +kernel
theorem bd1_1 : (PyrT8.badOf cover1).getD 1 (0, 0) = (59904, 74752) := by decide +kernel
theorem bd1_2 : (PyrT8.badOf cover1).getD 2 (0, 0) = (88576, 262144) := by decide +kernel
theorem nb1_eq : (PyrT8.badOf cover1).length = 3 := by decide +kernel
theorem bd2_0 : (PyrT8.badOf cover2).getD 0 (0, 0) = (31744, 38400) := by decide +kernel
theorem bd2_1 : (PyrT8.badOf cover2).getD 1 (0, 0) = (60416, 74240) := by decide +kernel
theorem bd2_2 : (PyrT8.badOf cover2).getD 2 (0, 0) = (89088, 237568) := by decide +kernel
theorem nb2_eq : (PyrT8.badOf cover2).length = 3 := by decide +kernel
theorem bd3_0 : (PyrT8.badOf cover3).getD 0 (0, 0) = (31744, 38400) := by decide +kernel
theorem bd3_1 : (PyrT8.badOf cover3).getD 1 (0, 0) = (59904, 74752) := by decide +kernel
theorem bd3_2 : (PyrT8.badOf cover3).getD 2 (0, 0) = (88576, 262144) := by decide +kernel
theorem nb3_eq : (PyrT8.badOf cover3).length = 3 := by decide +kernel
theorem bd4_0 : (PyrT8.badOf cover4).getD 0 (0, 0) = (30720, 39936) := by decide +kernel
theorem bd4_1 : (PyrT8.badOf cover4).getD 1 (0, 0) = (57344, 434176) := by decide +kernel
theorem nb4_eq : (PyrT8.badOf cover4).length = 2 := by decide +kernel
theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (PyrT8.badOf cover0).length → i1 < (PyrT8.badOf cover1).length → i2 < (PyrT8.badOf cover2).length → i3 < (PyrT8.badOf cover3).length → i4 < (PyrT8.badOf cover4).length →
    PyrT8.Covered ((PyrT8.badOf cover0).getD i0 (0, 0)).1 ((PyrT8.badOf cover0).getD i0 (0, 0)).2 ((PyrT8.badOf cover1).getD i1 (0, 0)).1 ((PyrT8.badOf cover1).getD i1 (0, 0)).2 ((PyrT8.badOf cover2).getD i2 (0, 0)).1 ((PyrT8.badOf cover2).getD i2 (0, 0)).2 ((PyrT8.badOf cover3).getD i3 (0, 0)).1 ((PyrT8.badOf cover3).getD i3 (0, 0)).2 ((PyrT8.badOf cover4).getD i4 (0, 0)).1 ((PyrT8.badOf cover4).getD i4 (0, 0)).2 := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  rw [nb3_eq] at hi3
  rw [nb4_eq] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk0
  | 0, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk1
  | 0, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk2
  | 0, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk3
  | 0, 0, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_2, bd4_0]; exact wk4
  | 0, 0, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_2, bd4_1]; exact wk5
  | 0, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk6
  | 0, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk7
  | 0, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk8
  | 0, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk9
  | 0, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk10
  | 0, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk11
  | 0, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk12
  | 0, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk13
  | 0, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk14
  | 0, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk15
  | 0, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk16
  | 0, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk17
  | 0, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk18
  | 0, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk19
  | 0, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk20
  | 0, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk21
  | 0, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk22
  | 0, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk23
  | 0, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk24
  | 0, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk25
  | 0, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk26
  | 0, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk27
  | 0, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk28
  | 0, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk29
  | 0, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk30
  | 0, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk31
  | 0, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk32
  | 0, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk33
  | 0, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk34
  | 0, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk35
  | 0, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk36
  | 0, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk37
  | 0, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk38
  | 0, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk39
  | 0, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk40
  | 0, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk41
  | 0, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk42
  | 0, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk43
  | 0, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk44
  | 0, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk45
  | 0, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk46
  | 0, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk47
  | 0, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk48
  | 0, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk49
  | 0, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk50
  | 0, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk51
  | 0, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk52
  | 0, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk53
  | 1, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk54
  | 1, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk55
  | 1, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk56
  | 1, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk57
  | 1, 0, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_0]; exact wk58
  | 1, 0, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_1]; exact wk59
  | 1, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk60
  | 1, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk61
  | 1, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk62
  | 1, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk63
  | 1, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk64
  | 1, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk65
  | 1, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk66
  | 1, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk67
  | 1, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk68
  | 1, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk69
  | 1, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk70
  | 1, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk71
  | 1, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk72
  | 1, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk73
  | 1, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk74
  | 1, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk75
  | 1, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk76
  | 1, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk77
  | 1, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk78
  | 1, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk79
  | 1, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk80
  | 1, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk81
  | 1, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk82
  | 1, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk83
  | 1, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk84
  | 1, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk85
  | 1, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk86
  | 1, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk87
  | 1, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk88
  | 1, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk89
  | 1, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk90
  | 1, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk91
  | 1, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk92
  | 1, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk93
  | 1, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk94
  | 1, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk95
  | 1, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk96
  | 1, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk97
  | 1, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk98
  | 1, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk99
  | 1, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk100
  | 1, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk101
  | 1, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk102
  | 1, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk103
  | 1, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk104
  | 1, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk105
  | 1, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk106
  | 1, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk107
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (PyrT8.cN : ℝ) / PyrT8.SA ≤ PyrT8.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  PyrT8.of_check cover0 cover1 cover2 cover3 cover4 434176 262144 237568 262144 434176
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok

end Zeta23Ext.Bridge.ThreePoint.PyrT8Data

end
