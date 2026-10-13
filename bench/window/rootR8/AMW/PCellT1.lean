import AMW.PCellRoot
import AMW.PCellLeafZ

/-! ###### polytope cells: the T1 node tightening's kernel shapes (bridge-port; TZ.md §1)

T1 runs in three stages, each with an emptiness test and each a sequence of the generic steps of `PCellTZ`:
1. the gap check (`gempG`);
2. the pair intervals, i.e. the box sums clipped by the pair bounds, written into the bounds (`matC`, emptiness
   `mempG`);
3. the 56 triples (`triC`, emptiness `temp`).

The kernel tests emptiness once, at the end, on all 28 slots (`gempG`, `pempG`). Every step only raises lower bounds and
lowers upper bounds, so a slot that is empty at some point stays empty, and the verdict is TZ.md's.

A sum split cuts at the raw midpoint `(A + B) >> 1` of the persisted bounds (`cov_rmid`). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the raw midpoint of pair `k`'s bounds -/
def qR (c : Cl) (k : ℕ) : ℕ := Nat.shiftRight (Nat.add (c.A.getD k 0) (c.B.getD k 0)) 1

theorem cov_rmid {Q : ℕ} {PR : List (ℕ × ℕ)} {P : (ℕ → ℝ) → Prop} {c : Cl} (k : ℕ) {n : ℕ}
    (hA'' : c.A.length = n) (hB'' : c.B.length = n) (hk : k < n)
    (hA : CovBy Q PR P ⟨c.L, c.U, c.A, c.B.set k (qR c k)⟩) (hB : CovBy Q PR P ⟨c.L, c.U, c.A.set k (qR c k), c.B⟩) :
    CovBy Q PR P c := cov_ssplit k _ hA'' hB'' hk hA hB

/-- some gap of the first `n` is empty, left-nested as the kernel writes it -/
def gempG (c : Cl) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun r acc => acc || Nat.blt (c.U.getD r 0) (c.L.getD r 0)) n

theorem gemp_false {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) :
    ∀ n ≤ Q, gempG c n = false
  | 0, _ => rfl
  | n + 1, hn => by
    show (gempG c n || Nat.blt (c.U.getD n 0) (c.L.getD n 0)) = false
    rw [gemp_false hg n (by omega), Bool.false_or]
    have h := hg.1 n (by omega)
    have hle : c.L.getD n 0 ≤ c.U.getD n 0 := by
      have : ((c.L.getD n 0 : ℕ) : ℝ) / SC ≤ ((c.U.getD n 0 : ℕ) : ℝ) / SC := h.1.trans h.2
      exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp this
    exact Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr hle)

/-- some pair of the first `n` has an empty effective range, left-nested -/
def mempG (PR : List (ℕ × ℕ)) (c : Cl) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc || femp PR c k) n

theorem memp_false {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} (hc : ClLen Q PR.length c)
    {g : ℕ → ℝ} (hg : InCell Q PR c g) : ∀ n ≤ PR.length, mempG PR c n = false
  | 0, _ => rfl
  | n + 1, hn => by
    show (mempG PR c n || femp PR c n) = false
    rw [memp_false hPR hc hg n (by omega), (mat_gen hPR hc hg).1 n (by omega)]; rfl

/-- some pair bound of the first `n` is empty (`B < A`), left-nested -/
def pempG (c : Cl) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc || Nat.blt (c.B.getD k 0) (c.A.getD k 0)) n

theorem pemp_false {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) :
    ∀ n ≤ PR.length, pempG c n = false
  | 0, _ => rfl
  | n + 1, hn => by
    show (pempG c n || Nat.blt (c.B.getD n 0) (c.A.getD n 0)) = false
    rw [pemp_false hg n (by omega), Bool.false_or]
    have h := hg.2 n (by omega)
    have hle : c.A.getD n 0 ≤ c.B.getD n 0 := by
      have : ((c.A.getD n 0 : ℕ) : ℝ) / SC ≤ ((c.B.getD n 0 : ℕ) : ℝ) / SC := h.1.trans h.2
      exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp this
    exact Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr hle)

/-- the fixed-width term fields (mvt-engine's DATA layout): `[κ 2][j1 7 if κ ≥ 1][j2 7 if κ = 3][λ lb if κ ≥ 2]`, the
weight `m = λ · 2^(10 − lb)` of 1024 -/
def plenF (lb a : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 (Nat.add 16 lb) (Nat.beq a 3))
    (Nat.add 9 lb) (Nat.beq a 2)) 9 (Nat.beq a 1)
def dec4F (lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (Nat.land (Nat.shiftRight w o) 3) fun a =>
  forceR (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w (Nat.add o 16)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 3))
      (Nat.land (Nat.shiftRight w (Nat.add o 9)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 2)) fun lam =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 127)) 0 (Nat.beq a 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 9)) 127)) (Nat.beq a 3)) fun r =>
  forceR (Nat.add o (plenF lb a)) fun o' => k a (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'

/-- a root cell depends on the index function only below `Q` -/
theorem rootCl_congr {Q NC W : ℕ} {cov : List (List (ℕ × ℕ × Bool))} {idx idx' : ℕ → ℕ} (h : ∀ r < Q, idx r = idx' r) :
    rootCl Q NC W cov idx = rootCl Q NC W cov idx' := by
  unfold rootCl
  congr 1 <;> exact List.map_congr_left fun r hr => by rw [h r (List.mem_range.mp hr)]

/-- the functional on a tuple of gaps, as its terms (for a certificate's real form `G`) -/
theorem gsum_range (g : ℕ → ℝ) (i j : ℕ) : gsum g i j = ∑ r ∈ Finset.range (j - i), g (i + r) :=
  Finset.sum_Ico_eq_sum_range g i j

/-- a point function's value at `x` is a sound triple (`PTF f` is `∀ x, PV x (f x)`) -/
def PV (x v : ℕ) : Prop := (lo32 v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 v) ((x : ℝ) / SC)

theorem pv_zero (x : ℕ) : PV x 0 := by
  unfold PV; rw [lo32_zero, hi32_zero]
  exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
theorem pv_dsel {x j m a b : ℕ} (ha : PV x a) (hb : PV x b) : PV x (dsel j m a b) := by
  unfold dsel; cases Nat.ble m j <;> assumption
theorem pv_dpk {x j k v : ℕ} (hv : PV x v) : PV x (dpk j k v) := by
  unfold dpk; cases Nat.beq j k
  · exact pv_zero x
  · exact hv

theorem triC_len {Q n : ℕ} {c : Cl} (h : ClLen Q n c) (a b d : ℕ) : ClLen Q n (triC Q c a b d) :=
  setHi_len (setLo_len (setHi_len (setLo_len (setHi_len (setLo_len h _ _) _ _) _ _) _ _) _ _) _ _

end AMW.Cert.PCell
