import AMW.PCellLeaf

/-! ###### polytope cells: the triple pass and the zero-order tangent extension, generic (bridge-port)

**Triples (T).** A cell's 28 pair intervals are its slots: slot `s < Q` is gap `s` (`[L_s, U_s]`), slot `Q + k` is pair
`k` of `PR` (`[A_k, B_k]`). Every point of the cell satisfies every slot (`InCell`).
* `matC` writes each pair's effective range `[max(A, Σl), min(B, Σu)]` into `A, B`.
* `triC` is one triple `s_d = s_a + s_b`, in mvt-engine's order: `d` from `a + b`, then `a` from `d − b`, then `b`
  from `d − a`, each bound clipped against the slot's own.
Each step keeps every point (`mat_gen`, `tri_gen`), so any sequence of steps does. On a point the updated slots are
nonempty, so an empty slot means an empty cell.

**Zero-order extension (Z).** Beyond the certified convex region a tangent can stay below `w` without derivative
information. Its line (value `v ≤ w(p)`, slope within the point claims) only has to lie below the pyramid's lower
bound of `w` at both ends of each piece of the range, because a line is maximised at an endpoint (`line_le_ends`).
The pieces are `n` equal integer pieces (`zpieces_cover`); a degenerate piece needs no check. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-! ### (T) slots -/

/-- slot `s`: gap `s` (`s < Q`) or pair `s − Q`; its gaps `[sI, sJ)` and its raw bounds -/
def sI (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s else pI PR (s - Q)
def sJ (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s + 1 else pJ PR (s - Q)
def sLo (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.L.getD s 0 else c.A.getD (s - Q) 0
def sHi (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.U.getD s 0 else c.B.getD (s - Q) 0
def setLo (Q : ℕ) (c : Cl) (s v : ℕ) : Cl :=
  if s < Q then ⟨c.L.set s v, c.U, c.A, c.B⟩ else ⟨c.L, c.U, c.A.set (s - Q) v, c.B⟩
def setHi (Q : ℕ) (c : Cl) (s v : ℕ) : Cl :=
  if s < Q then ⟨c.L, c.U.set s v, c.A, c.B⟩ else ⟨c.L, c.U, c.A, c.B.set (s - Q) v⟩

/-- the list lengths of a cell -/
def ClLen (Q n : ℕ) (c : Cl) : Prop := c.L.length = Q ∧ c.U.length = Q ∧ c.A.length = n ∧ c.B.length = n

theorem setLo_len {Q n : ℕ} {c : Cl} (h : ClLen Q n c) (s v : ℕ) : ClLen Q n (setLo Q c s v) := by
  unfold setLo; split_ifs <;> simpa [ClLen] using h
theorem setHi_len {Q n : ℕ} {c : Cl} (h : ClLen Q n c) (s v : ℕ) : ClLen Q n (setHi Q c s v) := by
  unfold setHi; split_ifs <;> simpa [ClLen] using h

theorem gsum_single (g : ℕ → ℝ) (s : ℕ) : gsum g s (s + 1) = g s := by simp [gsum]

theorem gsum_add (g : ℕ → ℝ) {i k j : ℕ} (h1 : i ≤ k) (h2 : k ≤ j) : gsum g i k + gsum g k j = gsum g i j :=
  Finset.sum_Ico_consecutive _ h1 h2

theorem gsum_nonneg {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) {i j : ℕ} (hj : j ≤ Q) :
    0 ≤ gsum g i j :=
  Finset.sum_nonneg fun r hr =>
    (div_nonneg (Nat.cast_nonneg _) SC_pos.le).trans (hg.1 r (by simp at hr; omega)).1

/-- every point of the cell lies in every slot -/
theorem slot_ok {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) {s : ℕ}
    (hs : s < Q + PR.length) :
    ((sLo Q c s : ℕ) : ℝ) / SC ≤ gsum g (sI Q PR s) (sJ Q PR s) ∧
      gsum g (sI Q PR s) (sJ Q PR s) ≤ ((sHi Q c s : ℕ) : ℝ) / SC := by
  unfold sLo sHi sI sJ
  split_ifs with h
  · rw [gsum_single]; exact hg.1 s h
  · exact hg.2 (s - Q) (by omega)

theorem setLo_ok {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hc : ClLen Q PR.length c) (hg : InCell Q PR c g)
    {s v : ℕ} (hs : s < Q + PR.length) (hv : (v : ℝ) / SC ≤ gsum g (sI Q PR s) (sJ Q PR s)) :
    InCell Q PR (setLo Q c s v) g := by
  unfold setLo
  split_ifs with h
  · refine ⟨fun r hr => ?_, hg.2⟩
    show (((c.L.set s v).getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ (by rw [hc.1]; exact h)]
    split_ifs with e
    · subst e; simp only [sI, sJ, h, if_true, gsum_single] at hv; exact ⟨hv, (hg.1 r hr).2⟩
    · exact hg.1 r hr
  · refine ⟨hg.1, fun k hk => ?_⟩
    show (((c.A.set (s - Q) v).getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ ((c.B.getD k 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ (by rw [hc.2.2.1]; omega)]
    split_ifs with e
    · subst e; simp only [sI, sJ, h, if_false] at hv; exact ⟨hv, (hg.2 _ hk).2⟩
    · exact hg.2 k hk

theorem setHi_ok {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hc : ClLen Q PR.length c) (hg : InCell Q PR c g)
    {s v : ℕ} (hs : s < Q + PR.length) (hv : gsum g (sI Q PR s) (sJ Q PR s) ≤ (v : ℝ) / SC) :
    InCell Q PR (setHi Q c s v) g := by
  unfold setHi
  split_ifs with h
  · refine ⟨fun r hr => ?_, hg.2⟩
    show ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ (((c.U.set s v).getD r 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ (by rw [hc.2.1]; exact h)]
    split_ifs with e
    · subst e; simp only [sI, sJ, h, if_true, gsum_single] at hv; exact ⟨(hg.1 r hr).1, hv⟩
    · exact hg.1 r hr
  · refine ⟨hg.1, fun k hk => ?_⟩
    show ((c.A.getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ (((c.B.set (s - Q) v).getD k 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ (by rw [hc.2.2.2]; omega)]
    split_ifs with e
    · subst e; simp only [sI, sJ, h, if_false] at hv; exact ⟨(hg.2 _ hk).1, hv⟩
    · exact hg.2 k hk

/-! ### (T) one triple -/

/-- `d = a + b` as slots: `a` and `b` adjacent, their union `d`, inside the gaps -/
def TriOk (Q : ℕ) (PR : List (ℕ × ℕ)) (a b d : ℕ) : Prop :=
  a < Q + PR.length ∧ b < Q + PR.length ∧ d < Q + PR.length ∧ sI Q PR a = sI Q PR d ∧ sJ Q PR a = sI Q PR b ∧
    sJ Q PR b = sJ Q PR d ∧ sI Q PR a ≤ sJ Q PR a ∧ sI Q PR b ≤ sJ Q PR b ∧ sJ Q PR d ≤ Q

instance (Q : ℕ) (PR : List (ℕ × ℕ)) (a b d : ℕ) : Decidable (TriOk Q PR a b d) := by unfold TriOk; infer_instance

/-- the six clipped updates of a triple, in order -/
def triC (Q : ℕ) (c : Cl) (a b d : ℕ) : Cl :=
  let c1 := setLo Q c d (nmax (sLo Q c d) (Nat.add (sLo Q c a) (sLo Q c b)))
  let c2 := setHi Q c1 d (nmin (sHi Q c1 d) (Nat.add (sHi Q c1 a) (sHi Q c1 b)))
  let c3 := setLo Q c2 a (nmax (sLo Q c2 a) (Nat.sub (sLo Q c2 d) (sHi Q c2 b)))
  let c4 := setHi Q c3 a (nmin (sHi Q c3 a) (Nat.sub (sHi Q c3 d) (sLo Q c3 b)))
  let c5 := setLo Q c4 b (nmax (sLo Q c4 b) (Nat.sub (sLo Q c4 d) (sHi Q c4 a)))
  setHi Q c5 b (nmin (sHi Q c5 b) (Nat.sub (sHi Q c5 d) (sLo Q c5 a)))

/-- some slot of the triple is empty -/
def temp (Q : ℕ) (c : Cl) (a b d : ℕ) : Bool :=
  Nat.blt (sHi Q c d) (sLo Q c d) || Nat.blt (sHi Q c a) (sLo Q c a) || Nat.blt (sHi Q c b) (sLo Q c b)

/-- a difference of two scaled naturals, truncated, is a lower bound of a nonnegative quantity above it -/
theorem natsub_lo {x y : ℕ} {t : ℝ} (h : (x : ℝ) / SC - (y : ℝ) / SC ≤ t) (ht : 0 ≤ t) :
    ((Nat.sub x y : ℕ) : ℝ) / SC ≤ t := by
  rcases le_total y x with hxy | hxy
  · rw [Nat.sub_eq, Nat.cast_sub hxy, sub_div]; exact h
  · rw [Nat.sub_eq, Nat.sub_eq_zero_of_le hxy]; simpa using ht

/-- and an upper bound of a nonnegative quantity below it -/
theorem natsub_hi {x y : ℕ} {t : ℝ} (h : t ≤ (x : ℝ) / SC - (y : ℝ) / SC) (ht : 0 ≤ t) :
    t ≤ ((Nat.sub x y : ℕ) : ℝ) / SC := by
  have hSC := SC_pos
  have hyx : y ≤ x := by
    have : (y : ℝ) / SC ≤ (x : ℝ) / SC := by linarith
    exact_mod_cast (div_le_div_iff_of_pos_right hSC).mp this
  rw [Nat.sub_eq, Nat.cast_sub hyx, sub_div]; exact h

theorem cast_add_div (x y : ℕ) : ((Nat.add x y : ℕ) : ℝ) / SC = (x : ℝ) / SC + (y : ℝ) / SC := by
  rw [Nat.add_eq, Nat.cast_add, add_div]

/-- (T) a triple keeps every point of the cell, and its slots are nonempty on a point -/
theorem tri_gen {Q : ℕ} {PR : List (ℕ × ℕ)} {a b d : ℕ} (ht : TriOk Q PR a b d) {c : Cl} (hc : ClLen Q PR.length c)
    {g : ℕ → ℝ} (hg : InCell Q PR c g) : temp Q (triC Q c a b d) a b d = false ∧ InCell Q PR (triC Q c a b d) g := by
  obtain ⟨ha, hb, hd, h1, h2, h3, h4, h5, h6⟩ := ht
  have hsum : gsum g (sI Q PR d) (sJ Q PR d) = gsum g (sI Q PR a) (sJ Q PR a) + gsum g (sI Q PR b) (sJ Q PR b) := by
    rw [← h1, ← h3, h2]; exact (gsum_add g (h2 ▸ h4) h5).symm
  have hGa : 0 ≤ gsum g (sI Q PR a) (sJ Q PR a) := gsum_nonneg hg (by omega)
  have hGb : 0 ≤ gsum g (sI Q PR b) (sJ Q PR b) := gsum_nonneg hg (by omega)
  -- the six steps, each from the bounds of the cell before it
  have s1 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setLo Q c d (nmax (sLo Q c d) (Nat.add (sLo Q c a) (sLo Q c b)))) g := fun hc hg =>
    setLo_ok hc hg hd (lo_nmax (slot_ok hg hd).1
      (by rw [cast_add_div, hsum]; exact add_le_add (slot_ok hg ha).1 (slot_ok hg hb).1))
  have s2 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setHi Q c d (nmin (sHi Q c d) (Nat.add (sHi Q c a) (sHi Q c b)))) g := fun hc hg =>
    setHi_ok hc hg hd (hi_nmin (slot_ok hg hd).2
      (by rw [cast_add_div, hsum]; exact add_le_add (slot_ok hg ha).2 (slot_ok hg hb).2))
  have s3 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setLo Q c a (nmax (sLo Q c a) (Nat.sub (sLo Q c d) (sHi Q c b)))) g := fun hc hg =>
    setLo_ok hc hg ha (lo_nmax (slot_ok hg ha).1
      (natsub_lo (by linarith [(slot_ok hg hd).1, (slot_ok hg hb).2]) hGa))
  have s4 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setHi Q c a (nmin (sHi Q c a) (Nat.sub (sHi Q c d) (sLo Q c b)))) g := fun hc hg =>
    setHi_ok hc hg ha (hi_nmin (slot_ok hg ha).2
      (natsub_hi (by linarith [(slot_ok hg hd).2, (slot_ok hg hb).1]) hGa))
  have s5 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setLo Q c b (nmax (sLo Q c b) (Nat.sub (sLo Q c d) (sHi Q c a)))) g := fun hc hg =>
    setLo_ok hc hg hb (lo_nmax (slot_ok hg hb).1
      (natsub_lo (by linarith [(slot_ok hg hd).1, (slot_ok hg ha).2]) hGb))
  have s6 : ∀ {c : Cl}, ClLen Q PR.length c → InCell Q PR c g →
      InCell Q PR (setHi Q c b (nmin (sHi Q c b) (Nat.sub (sHi Q c d) (sLo Q c a)))) g := fun hc hg =>
    setHi_ok hc hg hb (hi_nmin (slot_ok hg hb).2
      (natsub_hi (by linarith [(slot_ok hg hd).2, (slot_ok hg ha).1]) hGb))
  have hfin : InCell Q PR (triC Q c a b d) g :=
    s6 (setLo_len (setHi_len (setLo_len (setHi_len (setLo_len hc _ _) _ _) _ _) _ _) _ _)
      (s5 (setHi_len (setLo_len (setHi_len (setLo_len hc _ _) _ _) _ _) _ _)
        (s4 (setLo_len (setHi_len (setLo_len hc _ _) _ _) _ _)
          (s3 (setHi_len (setLo_len hc _ _) _ _)
            (s2 (setLo_len hc _ _) (s1 hc hg)))))
  refine ⟨?_, hfin⟩
  have ne : ∀ s, s < Q + PR.length → Nat.blt (sHi Q (triC Q c a b d) s) (sLo Q (triC Q c a b d) s) = false := by
    intro s hs
    have h := slot_ok hfin hs
    have hle : sLo Q (triC Q c a b d) s ≤ sHi Q (triC Q c a b d) s := by
      have : ((sLo Q (triC Q c a b d) s : ℕ) : ℝ) / SC ≤ ((sHi Q (triC Q c a b d) s : ℕ) : ℝ) / SC := h.1.trans h.2
      exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp this
    exact Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr hle)
  unfold temp
  rw [ne d hd, ne a ha, ne b hb]; rfl

/-! ### (T) the effective ranges written into the pair bounds -/

/-- every pair's effective range as its bounds -/
def matC (PR : List (ℕ × ℕ)) (c : Cl) : Cl :=
  ⟨c.L, c.U, imap (fun k _ => fLe PR c k) 0 c.A, imap (fun k _ => fUe PR c k) 0 c.B⟩

/-- (T) on a point, every pair's effective range is nonempty and the written bounds hold -/
theorem mat_gen {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} (hc : ClLen Q PR.length c)
    {g : ℕ → ℝ} (hg : InCell Q PR c g) :
    (∀ k < PR.length, femp PR c k = false) ∧ InCell Q PR (matC PR c) g := by
  have hk : ∀ k < PR.length, ((fLe PR c k : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ ((fUe PR c k : ℕ) : ℝ) / SC := by
    intro k hk
    obtain ⟨hij, hjQ⟩ := hPR k hk
    have hn : pI PR k + (pJ PR k - pI PR k) = pJ PR k := by omega
    have hsl := sum_lo hg.1 (pI PR k) (pJ PR k - pI PR k) (by omega)
    have hsu := sum_hi hg.1 (pI PR k) (pJ PR k - pI PR k) (by omega)
    rw [hn] at hsl hsu
    exact ⟨lo_nmax (hg.2 k hk).1 hsl, hi_nmin (hg.2 k hk).2 hsu⟩
  refine ⟨fun k hkk => ?_, hg.1, fun k hkk => ?_⟩
  · have h := hk k hkk
    have h2 : fLe PR c k ≤ fUe PR c k := by
      have : ((fLe PR c k : ℕ) : ℝ) / SC ≤ ((fUe PR c k : ℕ) : ℝ) / SC := h.1.trans h.2
      exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp this
    unfold femp; exact Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr h2)
  · show (((imap (fun k _ => fLe PR c k) 0 c.A).getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ (((imap (fun k _ => fUe PR c k) 0 c.B).getD k 0 : ℕ) : ℝ) / SC
    rw [imap_getD _ _ _ _ (by rw [hc.2.2.1]; exact hkk), imap_getD _ _ _ _ (by rw [hc.2.2.2]; exact hkk), Nat.zero_add]
    exact hk k hkk

end AMW.Cert.PCell
