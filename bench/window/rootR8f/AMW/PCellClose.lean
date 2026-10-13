import AMW.PCellT1

/-! ###### polytope cells: the exact closure, generic (mvt-engine; bench/eight/am8/TZ.md §5)

A cell is a system of difference constraints on the prefix sums `x_k = g_0 + … + g_{k−1}`: slot `(a, b)` bounds
`x_b − x_a`. A split adds one edge `s → t` to the constraint graph: child A of a split on the pair `(p, q)` sets
`hi(p, q) := m` (edge `p → q`, weight `m`), child B sets `lo(p, q) := m` (edge `q → p`, weight `−m`).
`cupd` then tightens every slot by the path through the new edge:
* `hi(a, b) ≤ D(a, s) + D(s, t) + D(t, b)` and `lo(a, b) ≥ −(D(b, s) + D(s, t) + D(t, a))`,
* where `D(x, y) = hi(x, y)` if `x < y`, `0` if `x = y`, and `−lo(y, x)` if `x > y`, all read on the cell after the split.

Each leg is a valid bound on `x_y − x_x`, so every candidate is a valid bound and `cupd` keeps every point (`cupd_ok`).
Closedness is not needed for this. On a closed cell (the root box, then by induction every child), `cupd` is the
closure of the child, which is what the sizer's `tz.close` computes. In Nat, a candidate is
`(positive legs) − (negative legs)`; truncation only loosens an upper bound and, inside the `max` with `lo ≥ 0`, is exact
for a lower bound.

`hi(a, b)` is kept when `b = s` or `a = t`, and `lo(a, b)` when `a = s` or `b = t`. On a closed cell those
candidates never bind, and skipping them keeps the update sound in any case. The slot of the pair `(a, b)` is read from
the instance's table `SL` (`SLok`, by `decide`). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-! ### the slot table -/

/-- the slot of the pair `(a, b)`, `a < b ≤ Q`: entry `a · (Q + 1) + b` of `SL` -/
def slT (Q : ℕ) (SL : List ℕ) (a b : ℕ) : ℕ := SL.getD (a * (Q + 1) + b) 0

/-- every pair `(a, b)`, `a < b ≤ Q`, has a slot with those gaps -/
def SLok (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Prop :=
  ∀ a < Q + 1, ∀ b < Q + 1, a < b →
    slT Q SL a b < Q + PR.length ∧ sI Q PR (slT Q SL a b) = a ∧ sJ Q PR (slT Q SL a b) = b

instance (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Decidable (SLok Q PR SL) := by unfold SLok; infer_instance

/-! ### optional sums -/

def oadd : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.add a b)

def ov : Option ℕ → ℕ
  | none => 0
  | some a => a

theorem ov_oadd (x y : Option ℕ) : ov (oadd x y) = ov x + ov y := by
  cases x <;> cases y <;> simp [oadd, ov, Nat.add_eq]

/-- positive part minus negative part; no candidate without a positive part -/
def csub : Option ℕ → Option ℕ → Option ℕ
  | none, _ => none
  | some p, none => some p
  | some p, some n => some (Nat.sub p n)

/-! ### legs, paths, candidates -/

/-- the positive part of `D(x, y)`: `hi(x, y)` when `x < y` -/
def legP (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
  Bool.rec (motive := fun _ => Option ℕ) none (some (sHi Q c (slT Q SL x y))) (Nat.blt x y)

/-- the negative part of `D(x, y)`: `lo(y, x)` when `y < x` -/
def legN (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
  Bool.rec (motive := fun _ => Option ℕ) none (some (sLo Q c (slT Q SL y x))) (Nat.blt y x)

def pathP (Q : ℕ) (SL : List ℕ) (c : Cl) (a s t b : ℕ) : Option ℕ :=
  oadd (oadd (legP Q SL c a s) (legP Q SL c s t)) (legP Q SL c t b)

def pathN (Q : ℕ) (SL : List ℕ) (c : Cl) (a s t b : ℕ) : Option ℕ :=
  oadd (oadd (legN Q SL c a s) (legN Q SL c s t)) (legN Q SL c t b)

/-- the candidate upper bound of `x_b − x_a` through `s → t` -/
def cHi (Q : ℕ) (SL : List ℕ) (c : Cl) (a b s t : ℕ) : Option ℕ := csub (pathP Q SL c a s t b) (pathN Q SL c a s t b)

/-- the candidate lower bound of `x_b − x_a`: minus the path bound of `x_a − x_b` -/
def cLo (Q : ℕ) (SL : List ℕ) (c : Cl) (a b s t : ℕ) : Option ℕ := csub (pathN Q SL c b s t a) (pathP Q SL c b s t a)

def upHi (h : ℕ) : Option ℕ → ℕ
  | none => h
  | some v => nmin h v

def upLo (l : ℕ) : Option ℕ → ℕ
  | none => l
  | some v => nmax l v

/-- slot `d`'s new lower bound -/
def nLo (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) (c : Cl) (d s t : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (upLo (sLo Q c d) (cLo Q SL c (sI Q PR d) (sJ Q PR d) s t)) (sLo Q c d)
    (Nat.beq (sI Q PR d) s || Nat.beq (sJ Q PR d) t)

/-- slot `d`'s new upper bound -/
def nHi (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) (c : Cl) (d s t : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (upHi (sHi Q c d) (cHi Q SL c (sI Q PR d) (sJ Q PR d) s t)) (sHi Q c d)
    (Nat.beq (sJ Q PR d) s || Nat.beq (sI Q PR d) t)

/-- the closure update through the edge `s → t`: every slot at once, from the cell `c` -/
def cupd (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) (c : Cl) (s t : ℕ) : Cl :=
  ⟨(List.range Q).map (fun r => nLo Q PR SL c r s t), (List.range Q).map (fun r => nHi Q PR SL c r s t),
   (List.range PR.length).map (fun k => nLo Q PR SL c (Q + k) s t),
   (List.range PR.length).map (fun k => nHi Q PR SL c (Q + k) s t)⟩

theorem cupd_len (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) (c : Cl) (s t : ℕ) :
    ClLen Q PR.length (cupd Q PR SL c s t) := by
  simp [ClLen, cupd]

/-! ### soundness -/

theorem gsum_sub (g : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) : gsum g a b = gsum g 0 b - gsum g 0 a := by
  have := gsum_add g (Nat.zero_le a) h; linarith

theorem cast_ov_oadd (x y : Option ℕ) : ((ov (oadd x y) : ℕ) : ℝ) = (ov x : ℝ) + (ov y : ℝ) := by
  rw [ov_oadd]; push_cast; ring

section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {c : Cl} {g : ℕ → ℝ}

/-- a leg bounds `x_y − x_x` -/
theorem leg_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {x y : ℕ} (hx : x ≤ Q) (hy : y ≤ Q) :
    gsum g 0 y - gsum g 0 x ≤ ((ov (legP Q SL c x y) : ℕ) : ℝ) / SC - ((ov (legN Q SL c x y) : ℕ) : ℝ) / SC := by
  rcases lt_trichotomy x y with h | h | h
  · have hb : Nat.blt x y = true := Nat.blt_eq.mpr h
    have hb' : Nat.blt y x = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    simp only [legP, legN, hb, hb', ov, Nat.cast_zero, zero_div, sub_zero]
    obtain ⟨h1, h2, h3⟩ := hSL x (by omega) y (by omega) h
    have := (slot_ok hg h1).2
    rw [h2, h3] at this
    rw [← gsum_sub g h.le]; exact this
  · subst h
    have hb : Nat.blt x x = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (lt_irrefl _)
    simp [legP, legN, hb, ov]
  · have hb : Nat.blt y x = true := Nat.blt_eq.mpr h
    have hb' : Nat.blt x y = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    simp only [legP, legN, hb, hb', ov, Nat.cast_zero, zero_div, zero_sub]
    obtain ⟨h1, h2, h3⟩ := hSL y (by omega) x (by omega) h
    have := (slot_ok hg h1).1
    rw [h2, h3] at this
    rw [gsum_sub g h.le] at this; linarith

/-- a path through `s → t` bounds `x_b − x_a` -/
theorem path_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {a s t b : ℕ} (ha : a ≤ Q) (hs : s ≤ Q) (ht : t ≤ Q)
    (hb : b ≤ Q) : gsum g 0 b - gsum g 0 a ≤
      ((ov (pathP Q SL c a s t b) : ℕ) : ℝ) / SC - ((ov (pathN Q SL c a s t b) : ℕ) : ℝ) / SC := by
  have l1 := leg_ok hSL hg ha hs
  have l2 := leg_ok hSL hg hs ht
  have l3 := leg_ok hSL hg ht hb
  simp only [pathP, pathN, cast_ov_oadd, add_div]
  linarith

theorem cHi_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {a b s t : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (hs : s ≤ Q)
    (ht : t ≤ Q) {v : ℕ} (hv : cHi Q SL c a b s t = some v) : gsum g a b ≤ (v : ℝ) / SC := by
  have hp := path_ok hSL hg (hab.trans hb) hs ht hb (a := a) (b := b)
  rw [← gsum_sub g hab] at hp
  have h0 : 0 ≤ gsum g a b := gsum_nonneg hg hb
  unfold cHi at hv
  cases hP : pathP Q SL c a s t b with
  | none => rw [hP] at hv; simp [csub] at hv
  | some P =>
    rw [hP] at hv hp
    cases hN : pathN Q SL c a s t b with
    | none =>
      rw [hN] at hv hp; simp only [csub, Option.some.injEq] at hv; subst hv
      simpa [ov] using hp
    | some N =>
      rw [hN] at hv hp; simp only [csub, Option.some.injEq] at hv; subst hv
      exact natsub_hi (by simpa [ov] using hp) h0

theorem cLo_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {a b s t : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (hs : s ≤ Q)
    (ht : t ≤ Q) {v : ℕ} (hv : cLo Q SL c a b s t = some v) : (v : ℝ) / SC ≤ gsum g a b := by
  have hp := path_ok hSL hg hb hs ht (hab.trans hb) (a := b) (b := a)
  have e := gsum_sub g hab
  have h0 : 0 ≤ gsum g a b := gsum_nonneg hg hb
  unfold cLo at hv
  cases hN : pathN Q SL c b s t a with
  | none => rw [hN] at hv; simp [csub] at hv
  | some N =>
    rw [hN] at hv hp
    cases hP : pathP Q SL c b s t a with
    | none =>
      rw [hP] at hv hp; simp only [csub, Option.some.injEq] at hv; subst hv
      simp only [ov, Nat.cast_zero, zero_div, zero_sub] at hp; linarith
    | some P =>
      rw [hP] at hv hp; simp only [csub, Option.some.injEq] at hv; subst hv
      exact natsub_lo (by simp only [ov] at hp; linarith) h0

/-- a slot's gaps are an interval inside the `Q` gaps -/
theorem slot_gaps (hPR : PRok Q PR) {d : ℕ} (hd : d < Q + PR.length) : sI Q PR d ≤ sJ Q PR d ∧ sJ Q PR d ≤ Q := by
  unfold sI sJ
  split_ifs with h
  · omega
  · obtain ⟨h1, h2⟩ := hPR (d - Q) (by omega); omega

theorem nLo_ok (hSL : SLok Q PR SL) (hPR : PRok Q PR) (hg : InCell Q PR c g) {s t : ℕ} (hs : s ≤ Q) (ht : t ≤ Q)
    {d : ℕ} (hd : d < Q + PR.length) :
    ((nLo Q PR SL c d s t : ℕ) : ℝ) / SC ≤ gsum g (sI Q PR d) (sJ Q PR d) := by
  obtain ⟨h1, h2⟩ := slot_gaps hPR hd
  unfold nLo
  cases (Nat.beq (sI Q PR d) s || Nat.beq (sJ Q PR d) t)
  · show ((upLo (sLo Q c d) (cLo Q SL c (sI Q PR d) (sJ Q PR d) s t) : ℕ) : ℝ) / SC ≤ _
    cases hv : cLo Q SL c (sI Q PR d) (sJ Q PR d) s t with
    | none => exact (slot_ok hg hd).1
    | some v => exact lo_nmax (slot_ok hg hd).1 (cLo_ok hSL hg h1 h2 hs ht hv)
  · exact (slot_ok hg hd).1

theorem nHi_ok (hSL : SLok Q PR SL) (hPR : PRok Q PR) (hg : InCell Q PR c g) {s t : ℕ} (hs : s ≤ Q) (ht : t ≤ Q)
    {d : ℕ} (hd : d < Q + PR.length) :
    gsum g (sI Q PR d) (sJ Q PR d) ≤ ((nHi Q PR SL c d s t : ℕ) : ℝ) / SC := by
  obtain ⟨h1, h2⟩ := slot_gaps hPR hd
  unfold nHi
  cases (Nat.beq (sJ Q PR d) s || Nat.beq (sI Q PR d) t)
  · show _ ≤ ((upHi (sHi Q c d) (cHi Q SL c (sI Q PR d) (sJ Q PR d) s t) : ℕ) : ℝ) / SC
    cases hv : cHi Q SL c (sI Q PR d) (sJ Q PR d) s t with
    | none => exact (slot_ok hg hd).2
    | some v => exact hi_nmin (slot_ok hg hd).2 (cHi_ok hSL hg h1 h2 hs ht hv)
  · exact (slot_ok hg hd).2

/-- the closure update keeps every point of the cell -/
theorem cupd_ok (hSL : SLok Q PR SL) (hPR : PRok Q PR) (hg : InCell Q PR c g) {s t : ℕ} (hs : s ≤ Q) (ht : t ≤ Q) :
    InCell Q PR (cupd Q PR SL c s t) g := by
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · have hlo := nLo_ok hSL hPR hg hs ht (d := r) (by omega)
    have hhi := nHi_ok hSL hPR hg hs ht (d := r) (by omega)
    have e1 : sI Q PR r = r := by simp [sI, hr]
    have e2 : sJ Q PR r = r + 1 := by simp [sJ, hr]
    rw [e1, e2, gsum_single] at hlo hhi
    show (((List.range Q).map (fun r => nLo Q PR SL c r s t)).getD r 0 : ℝ) / SC ≤ g r ∧
      g r ≤ (((List.range Q).map (fun r => nHi Q PR SL c r s t)).getD r 0 : ℝ) / SC
    rw [getD_map_range _ hr, getD_map_range _ hr]
    exact ⟨hlo, hhi⟩
  · have hlo := nLo_ok hSL hPR hg hs ht (d := Q + k) (by omega)
    have hhi := nHi_ok hSL hPR hg hs ht (d := Q + k) (by omega)
    have e1 : sI Q PR (Q + k) = pI PR k := by simp [sI]
    have e2 : sJ Q PR (Q + k) = pJ PR k := by simp [sJ]
    rw [e1, e2] at hlo hhi
    show (((List.range PR.length).map (fun k => nLo Q PR SL c (Q + k) s t)).getD k 0 : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ (((List.range PR.length).map (fun k => nHi Q PR SL c (Q + k) s t)).getD k 0 : ℝ) / SC
    rw [getD_map_range _ hk, getD_map_range _ hk]
    exact ⟨hlo, hhi⟩

/-- covering the updated cell covers the cell -/
theorem cov_cupd {P : (ℕ → ℝ) → Prop} (hSL : SLok Q PR SL) (hPR : PRok Q PR) {s t : ℕ} (hs : s ≤ Q) (ht : t ≤ Q)
    (h : CovBy Q PR P (cupd Q PR SL c s t)) : CovBy Q PR P c :=
  fun g hg => h g (cupd_ok hSL hPR hg hs ht)

end

/-! ### the splits with the closure update -/

/-- gap `r` at its midpoint: child A (`u_r := m`, edge `r → r+1`), child B (`l_r := m`, edge `r+1 → r`) -/
theorem cov_gmidC {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {P : (ℕ → ℝ) → Prop} {c : Cl} (hSL : SLok Q PR SL)
    (hPR : PRok Q PR) (r : ℕ) (hL' : c.L.length = Q) (hU' : c.U.length = Q) (hr : r < Q)
    (hA : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U.set r (qG c r), c.A, c.B⟩ r (r + 1)))
    (hB : CovBy Q PR P (cupd Q PR SL ⟨c.L.set r (qG c r), c.U, c.A, c.B⟩ (r + 1) r)) : CovBy Q PR P c :=
  cov_gmid r hL' hU' hr (cov_cupd hSL hPR (by omega) (by omega) hA) (cov_cupd hSL hPR (by omega) (by omega) hB)

/-- pair `k` at the raw midpoint of its bounds: child A (`B_k := m`, edge `i → j`), child B (`A_k := m`, edge `j → i`) -/
theorem cov_rmidC {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {P : (ℕ → ℝ) → Prop} {c : Cl} (hSL : SLok Q PR SL)
    (hPR : PRok Q PR) (k : ℕ) (hA'' : c.A.length = PR.length) (hB'' : c.B.length = PR.length) (hk : k < PR.length)
    (hA : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U, c.A, c.B.set k (qR c k)⟩ (pI PR k) (pJ PR k)))
    (hB : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U, c.A.set k (qR c k), c.B⟩ (pJ PR k) (pI PR k))) : CovBy Q PR P c := by
  obtain ⟨h1, h2⟩ := hPR k hk
  exact cov_rmid k hA'' hB'' hk (cov_cupd hSL hPR (by omega) h2 hA) (cov_cupd hSL hPR h2 (by omega) hB)

end AMW.Cert.PCell
