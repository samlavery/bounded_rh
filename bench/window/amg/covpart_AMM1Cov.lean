
/-! ###### the 7-point weighted certificate `AMM1Cov` on the pyramid oracle: leaf test, walk, cover ###### -/

noncomputable section

namespace AMW.Cert.AMM1Cov

open AMW.Cert AMW.Cert.Pyr

def SA : ℕ := 100000000
def cN : ℕ := 789487

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  (48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5
    + (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 48468 l0) (Nat.mul 71367 l1)) (Nat.mul 82339 l2)) (Nat.mul 82339 l3)) (Nat.mul 71367 l4)) (Nat.mul 48468 l5)) 10000000000
  ee 258699100160000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 790920462336 (lb top bk l0 u0))
  ee 258699100160000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 790920462336 (lb top bk l5 u5))
  ee 258699100160000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1110645964800 (lb top bk l4 u4))
  ee 258699100160000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 1110645964800 (lb top bk l1 u1))
  ee 258699100160000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 1375233572864 (lb top bk l3 u3))
  ee 258699100160000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 1375233572864 (lb top bk l2 u2))
  ee 258699100160000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3666646794240 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 258699100160000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 1443476602880 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 258699100160000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1443476602880 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  ee 258699100160000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 2511680438272 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 258699100160000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 2511680438272 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 258699100160000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 258699100160000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5)))
  ee 258699100160000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 765119561728 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 258699100160000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 765119561728 (lb top bk (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5)))
  ee 258699100160000000000 s15 (
  let s16 := Nat.add s15 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 258699100160000000000 s16 (
  let s17 := Nat.add s16 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5)))
  ee 258699100160000000000 s17 (
  let s18 := Nat.add s17 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5)))
  ee 258699100160000000000 s18 (
  let s19 := Nat.add s18 (Nat.mul 0 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 258699100160000000000 s19 (
  let s20 := Nat.add s19 (Nat.mul 0 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 258699100160000000000 s20 (
  let s21 := Nat.add s20 (Nat.mul 0 (lb top bk (Nat.add l4 l5) (Nat.add u4 u5)))
  Nat.ble 258699100160000000000 s21)))))))))))))))))))))

/-- the type of a walk continuation: position and the ten coordinates to the end position (`0` = failure) -/
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

/-- a leaf: in the reflected half-space, or the leaf test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 1) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)) (Nat.add pos 1) (Nat.ble (Nat.add u5 1) l0)

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis); the position after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (splitAx ih pos (Nat.shiftRight w 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq (Nat.land w 1) 1))
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
    258699100160000000000 ≤ 10000000000 * (48468 * l0 + 71367 * l1 + 82339 * l2 + 82339 * l3 + 71367 * l4 + 48468 * l5) + 32768 * (24136977 * lb top bk (l0) (u0) + 0 * lb top bk (l0 + l1) (u0 + u1) + 23349596 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 100000000 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 100000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) + 33894225 * lb top bk (l1) (u1) + 44051410 * lb top bk (l1 + l2) (u1 + u2) + 76650404 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 0 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 100000000 * lb top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) + 41968798 * lb top bk (l2) (u2) + 111897180 * lb top bk (l2 + l3) (u2 + u3) + 76650404 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 100000000 * lb top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) + 41968798 * lb top bk (l3) (u3) + 44051410 * lb top bk (l3 + l4) (u3 + u4) + 23349596 * lb top bk (l3 + l4 + l5) (u3 + u4 + u5) + 33894225 * lb top bk (l4) (u4) + 0 * lb top bk (l4 + l5) (u4 + u5) + 24136977 * lb top bk (l5) (u5)) := by
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

set_option maxHeartbeats 4000000 in
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
  have w0 := hlb (l0) (u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := hlb (l0 + l1) (u0 + u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := hlb (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (g0 + g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42, h52])
  have w6 := hlb (l1) (u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w7 := hlb (l1 + l2) (u1 + u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w8 := hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w9 := hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w10 := hlb (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42, h52])
  have w11 := hlb (l2) (u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w12 := hlb (l2 + l3) (u2 + u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w13 := hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w14 := hlb (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42, h52])
  have w15 := hlb (l3) (u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w16 := hlb (l3 + l4) (u3 + u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w17 := hlb (l3 + l4 + l5) (u3 + u4 + u5) (g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h32, h42, h52])
  have w18 := hlb (l4) (u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  have w19 := hlb (l4 + l5) (u4 + u5) (g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h42, h52])
  have w20 := hlb (l5) (u5) (g5) (by push_cast; (try simp only [add_div]); linarith [h51]) (by push_cast; (try simp only [add_div]); linarith [h52])
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU : (0:ℝ) < 10000000000 := by norm_num
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 48468 * ((l0 : ℝ) / SC) + 71367 * ((l1 : ℝ) / SC) + 82339 * ((l2 : ℝ) / SC) + 82339 * ((l3 : ℝ) / SC) + 71367 * ((l4 : ℝ) / SC) + 48468 * ((l5 : ℝ) / SC) with hL
  set Wt : ℝ := 24136977 * ((lb top bk (l0) (u0) : ℝ) / 10000000000) + 0 * ((lb top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 23349596 * ((lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 200000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 33894225 * ((lb top bk (l1) (u1) : ℝ) / 10000000000) + 44051410 * ((lb top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 76650404 * ((lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 0 * ((lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 41968798 * ((lb top bk (l2) (u2) : ℝ) / 10000000000) + 111897180 * ((lb top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 76650404 * ((lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) / 10000000000) + 41968798 * ((lb top bk (l3) (u3) : ℝ) / 10000000000) + 44051410 * ((lb top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 23349596 * ((lb top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) / 10000000000) + 33894225 * ((lb top bk (l4) (u4) : ℝ) / 10000000000) + 0 * ((lb top bk (l4 + l5) (u4 + u5) : ℝ) / 10000000000) + 24136977 * ((lb top bk (l5) (u5) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (48468 * (l0 : ℝ) + 71367 * (l1 : ℝ) + 82339 * (l2 : ℝ) + 82339 * (l3 : ℝ) + 71367 * (l4 : ℝ) + 48468 * (l5 : ℝ)) + 32768 * (24136977 * (lb top bk (l0) (u0) : ℝ) + 0 * (lb top bk (l0 + l1) (u0 + u1) : ℝ) + 23349596 * (lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 100000000 * (lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 100000000 * (lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 200000000 * (lb top bk (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) : ℝ) + 33894225 * (lb top bk (l1) (u1) : ℝ) + 44051410 * (lb top bk (l1 + l2) (u1 + u2) : ℝ) + 76650404 * (lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 0 * (lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 100000000 * (lb top bk (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) : ℝ) + 41968798 * (lb top bk (l2) (u2) : ℝ) + 111897180 * (lb top bk (l2 + l3) (u2 + u3) : ℝ) + 76650404 * (lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 100000000 * (lb top bk (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) : ℝ) + 41968798 * (lb top bk (l3) (u3) : ℝ) + 44051410 * (lb top bk (l3 + l4) (u3 + u4) : ℝ) + 23349596 * (lb top bk (l3 + l4 + l5) (u3 + u4 + u5) : ℝ) + 33894225 * (lb top bk (l4) (u4) : ℝ) + 0 * (lb top bk (l4 + l5) (u4 + u5) : ℝ) + 24136977 * (lb top bk (l5) (u5) : ℝ)) := by
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

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold leafStep at h
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  cases hs : Nat.ble (Nat.add u5 1) l0
  · rw [hs] at h
    cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
    · rw [hl] at h; exact absurd rfl h
    · exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
  · right
    have hsk : u5 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u5 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits : ℕ) : ∀ fuel, WalkOK (walk top bk bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (splitAx (walk top bk bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 e : ℕ)
    (h : walk top bk bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 :=
  walk_sound hlb bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (h ▸ he)

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

end AMW.Cert.AMM1Cov

end
