import AMW.PCellClose

/-! ###### polytope cells: the closure through one point, biased (bridge-port, 2026-10-07; one helper for every split)

A split at `q` on the pair `(i, j)`, `i < j`, has two children: `x_j − x_i ≤ q` (the edge `i → j`, weight `q`) and
`x_j − x_i ≥ q` (the edge `j → i`, weight `−q`). Through an edge `s → t` of weight `w`, every slot `(a, b)` is bounded
by the path through it: `x_b − x_a ≤ D(a, s) + w + D(t, b)` and `x_b − x_a ≥ −(D(b, s) + w + D(t, a))`, where
`D(x, y)` is the cell's bound of `x_y − x_x` (`hi`, `0` or `−lo`, as in `PCellClose`).

With the column `X_x = BB + D(x, s)` and the row `Y_x = BB + w + D(t, x)`, both in ℕ (`BB = 2^42`), the update is the
same expression for every slot (`cuB`): `hi(a, b) := min(hi(a, b), X_a + Y_b − 2BB)` and
`lo(a, b) := max(lo(a, b), 2BB − X_b − Y_a)`. Soundness needs only that `X` and `Y` are upper bounds (`ColOK`); Nat
truncation in them only loosens, and a truncated candidate still bounds a nonnegative pair sum (`natsub_hi`,
`natsub_lo`). The split's own slot gets the candidate `q`, so a child is the closure of the parent's fields plus the
edge (`cov_splitB`). On a closed parent the candidates that `cupd` skips never bind, so the states are `cupd`'s.
###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the bias `2^42` -/
def BB : ℕ := 4398046511104
/-- twice the bias -/
def TB : ℕ := 8796093022208

theorem TB_eq : (TB : ℝ) / SC = (BB : ℝ) / SC + (BB : ℝ) / SC := by
  rw [← add_div]; norm_num [TB, BB]

/-- `X` bounds the column through `s` and `Y` the row: `x_s − x_x ≤ X_x − BB` and `x_x − x_s ≤ Y_x − BB` -/
def ColOK (Q : ℕ) (g : ℕ → ℝ) (s : ℕ) (X Y : List ℕ) : Prop :=
  ∀ x ≤ Q, gsum g 0 s - gsum g 0 x ≤ ((X.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC ∧
    gsum g 0 x - gsum g 0 s ≤ ((Y.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC

/-- the closure update through the column `X` and the row `Y` -/
def cuB (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (X Y : List ℕ) : Cl :=
  ⟨(List.range Q).map (fun r => nmax (c.L.getD r 0) (Nat.sub TB (Nat.add (X.getD (r + 1) 0) (Y.getD r 0)))),
   (List.range Q).map (fun r => nmin (c.U.getD r 0) (Nat.sub (Nat.add (X.getD r 0) (Y.getD (r + 1) 0)) TB)),
   (List.range PR.length).map (fun k =>
     nmax (c.A.getD k 0) (Nat.sub TB (Nat.add (X.getD (pJ PR k) 0) (Y.getD (pI PR k) 0)))),
   (List.range PR.length).map (fun k =>
     nmin (c.B.getD k 0) (Nat.sub (Nat.add (X.getD (pI PR k) 0) (Y.getD (pJ PR k) 0)) TB))⟩

section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {g : ℕ → ℝ} {s : ℕ} {X Y : List ℕ}

/-- the upper candidate of `x_b − x_a` -/
theorem candB_hi (hX : ColOK Q g s X Y) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (h0 : 0 ≤ gsum g a b) :
    gsum g a b ≤ ((Nat.sub (Nat.add (X.getD a 0) (Y.getD b 0)) TB : ℕ) : ℝ) / SC := by
  have h1 := (hX a (hab.trans hb)).1
  have h2 := (hX b hb).2
  refine natsub_hi ?_ h0
  rw [cast_add_div, TB_eq, gsum_sub g hab]
  linarith

/-- the lower candidate of `x_b − x_a` -/
theorem candB_lo (hX : ColOK Q g s X Y) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (h0 : 0 ≤ gsum g a b) :
    ((Nat.sub TB (Nat.add (X.getD b 0) (Y.getD a 0)) : ℕ) : ℝ) / SC ≤ gsum g a b := by
  have h1 := (hX b hb).1
  have h2 := (hX a (hab.trans hb)).2
  refine natsub_lo ?_ h0
  rw [cast_add_div, TB_eq, gsum_sub g hab]
  linarith

/-- the update keeps every point of the cell whose column and row bounds hold -/
theorem cuB_ok {c : Cl} (hPR : PRok Q PR) (hg : InCell Q PR c g) (hX : ColOK Q g s X Y) :
    InCell Q PR (cuB Q PR c X Y) g := by
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · have h0 : 0 ≤ gsum g r (r + 1) := gsum_nonneg hg (by omega)
    have hlo := candB_lo hX (Nat.le_succ r) (by omega) h0
    have hhi := candB_hi hX (Nat.le_succ r) (by omega) h0
    rw [gsum_single] at hlo hhi
    show (((List.range Q).map (fun r => nmax (c.L.getD r 0) (Nat.sub TB (Nat.add (X.getD (r + 1) 0) (Y.getD r 0))))).getD
        r 0 : ℝ) / SC ≤ g r ∧
      g r ≤ (((List.range Q).map (fun r => nmin (c.U.getD r 0)
        (Nat.sub (Nat.add (X.getD r 0) (Y.getD (r + 1) 0)) TB))).getD r 0 : ℝ) / SC
    rw [getD_map_range _ hr, getD_map_range _ hr]
    exact ⟨lo_nmax (hg.1 r hr).1 hlo, hi_nmin (hg.1 r hr).2 hhi⟩
  · obtain ⟨h1, h2⟩ := hPR k hk
    have h0 : 0 ≤ gsum g (pI PR k) (pJ PR k) := gsum_nonneg hg h2
    have hlo := candB_lo hX (a := pI PR k) (b := pJ PR k) (by omega) h2 h0
    have hhi := candB_hi hX (a := pI PR k) (b := pJ PR k) (by omega) h2 h0
    show (((List.range PR.length).map (fun k => nmax (c.A.getD k 0)
        (Nat.sub TB (Nat.add (X.getD (pJ PR k) 0) (Y.getD (pI PR k) 0))))).getD k 0 : ℝ) / SC ≤
        gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ (((List.range PR.length).map (fun k => nmin (c.B.getD k 0)
        (Nat.sub (Nat.add (X.getD (pI PR k) 0) (Y.getD (pJ PR k) 0)) TB))).getD k 0 : ℝ) / SC
    rw [getD_map_range _ hk, getD_map_range _ hk]
    exact ⟨lo_nmax (hg.2 k hk).1 hlo, hi_nmin (hg.2 k hk).2 hhi⟩

end

/-! ### the column and the row read from the cell -/

/-- `E + D(a, b)` in ℕ: `D(a, b)` is `hi(a, b)` if `a < b`, `0` if `a = b`, `−lo(b, a)` if `b < a` (truncated) -/
def dE (Q : ℕ) (SL : List ℕ) (c : Cl) (E a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Nat.sub E (sLo Q c (slT Q SL b a))) E (Nat.beq a b))
    (Nat.add E (sHi Q c (slT Q SL a b))) (Nat.blt a b)

/-- the column through `s` -/
def colB (Q : ℕ) (SL : List ℕ) (c : Cl) (s : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c BB x s)

/-- the row from `t`, with the base `E` (`BB` plus the edge's weight) -/
def rowB (Q : ℕ) (SL : List ℕ) (c : Cl) (E t : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c E t x)

section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {c : Cl} {g : ℕ → ℝ}

theorem dE_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) (E : ℕ) {a b : ℕ} (ha : a ≤ Q) (hb : b ≤ Q) :
    gsum g 0 b - gsum g 0 a ≤ ((dE Q SL c E a b : ℕ) : ℝ) / SC - (E : ℝ) / SC := by
  have l := leg_ok hSL hg ha hb
  rcases lt_trichotomy a b with h | h | h
  · have e1 : Nat.blt a b = true := Nat.blt_eq.mpr h
    have e2 : Nat.blt b a = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    simp only [legP, legN, e1, e2, ov, Nat.cast_zero, zero_div, sub_zero] at l
    simp only [dE, e1]
    rw [cast_add_div]; linarith
  · rw [h]
    have e1 : Nat.blt b b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (lt_irrefl _)
    simp only [dE, e1, Nat.beq_refl, sub_self, le_refl]
  · have e1 : Nat.blt a b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    have e2 : Nat.blt b a = true := Nat.blt_eq.mpr h
    have e3 : Nat.beq a b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.eq_of_beq_eq_true e) (by omega)
    simp only [legP, legN, e1, e2, ov, Nat.cast_zero, zero_div, zero_sub] at l
    simp only [dE, e1, e3]
    have := natsub_ge E (sLo Q c (slT Q SL b a))
    have hSC := SC_pos
    have : ((E : ℝ) - (sLo Q c (slT Q SL b a) : ℕ)) / SC ≤ ((Nat.sub E (sLo Q c (slT Q SL b a)) : ℕ) : ℝ) / SC :=
      (div_le_div_iff_of_pos_right hSC).mpr (by simpa [Nat.sub_eq] using this)
    rw [sub_div] at this; linarith

/-- the column through `s` and the row from `t` (base `E`) bound the cell, given the edge `x_t − x_s ≤ E − BB` -/
theorem colB_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {s t E : ℕ} (hs : s ≤ Q) (ht : t ≤ Q)
    (hE : gsum g 0 t - gsum g 0 s ≤ (E : ℝ) / SC - (BB : ℝ) / SC) :
    ColOK Q g s (colB Q SL c s) (rowB Q SL c E t) := by
  intro x hx
  have hx' : x < Q + 1 := by omega
  rw [colB, rowB, getD_map_range _ hx', getD_map_range _ hx']
  have h1 := dE_ok hSL hg BB hx hs
  have h2 := dE_ok hSL hg E ht hx
  exact ⟨h1, by linarith⟩

/-- a split at any `q` on `(i, j)`, `i < j ≤ Q`: the children are the closures through `i → j` (weight `q`) and
`j → i` (weight `−q`) -/
theorem cov_splitB {P : (ℕ → ℝ) → Prop} (hSL : SLok Q PR SL) (hPR : PRok Q PR) {i j : ℕ} (hij : i < j) (hj : j ≤ Q)
    (q : ℕ) (hA : CovBy Q PR P (cuB Q PR c (colB Q SL c i) (rowB Q SL c (Nat.add BB q) j)))
    (hB : CovBy Q PR P (cuB Q PR c (colB Q SL c j) (rowB Q SL c (Nat.sub BB q) i))) : CovBy Q PR P c := by
  intro g hg
  have hSC := SC_pos
  rcases le_total (gsum g 0 j - gsum g 0 i) ((q : ℝ) / SC) with h | h
  · refine hA g (cuB_ok hPR hg (colB_ok hSL hg (by omega) hj ?_))
    rw [cast_add_div]; linarith
  · refine hB g (cuB_ok hPR hg (colB_ok hSL hg hj (by omega) ?_))
    have := natsub_ge BB q
    have : ((BB : ℝ) - q) / SC ≤ ((Nat.sub BB q : ℕ) : ℝ) / SC :=
      (div_le_div_iff_of_pos_right hSC).mpr (by simpa [Nat.sub_eq] using this)
    rw [sub_div] at this; linarith

end

end AMW.Cert.PCell
