/-
AMW/Minorant.lean — the per-term affine minorant test, for an abstract pair kernel w.

The n-point functional over gaps g : Fin (n−1) → ℝ,
    Gk w n a b g = Σ_r b_r g_r + Σ_{i<j} a_ij · w(s_ij(g)),   s_ij(g) = Σ_{i ≤ r < j} g_r
(`Gk wfun n W.a W.b = Fw W` of the bridge, by rfl).  If a_ij ≥ 0 and each term carries a line
w(s) ≥ α_ij + β_ij·s on the range of s_ij over a box, then
    Gk ≥ Σ_r (b_r + Σ_{i ≤ r < j} a_ij β_ij)·g_r + Σ_{i<j} a_ij α_ij ≥ (corner minimum) + Σ a_ij α_ij,
the corner chosen coordinatewise by the sign of the coefficient.  Lines are certified from a value
bound w(p) ≥ v and one-sided derivative bounds (w′ ≤ β on [l, p], w′ ≥ β on [p, h]).
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open Finset

namespace AMW.Min

/-! ### one-variable lines below w -/

/-- **a line through (p, v) below w on [l, h]**: w(p) ≥ v, w′ ≤ β on (l, p) and w′ ≥ β on (p, h)
(open intervals: for p = l or p = h one side is vacuous). -/
theorem line_of_deriv {w w1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt w (w1 x) x) {l p h v β : ℝ}
    (hv : v ≤ w p) (hL : ∀ x ∈ Set.Ioo l p, w1 x ≤ β) (hR : ∀ x ∈ Set.Ioo p h, β ≤ w1 x) :
    ∀ s ∈ Set.Icc l h, v + β * (s - p) ≤ w s := by
  set H : ℝ → ℝ := fun s => w s - β * s with hH
  have hHd : ∀ x, HasDerivAt H (w1 x - β) x := fun x => by
    have h2 : HasDerivAt (fun s : ℝ => β * s) β x := by simpa using (hasDerivAt_id x).const_mul β
    exact (hd x).sub h2
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun x => (hHd x).continuousAt
  have key : ∀ s ∈ Set.Icc l h, H p ≤ H s := by
    intro s hs
    rcases le_total p s with hps | hsp
    · have hmono : MonotoneOn H (Set.Icc p h) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p h) hHc.continuousOn
          (fun x _ => (hHd x).hasDerivWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            linarith [hR x hx])
      exact hmono ⟨le_rfl, hps.trans hs.2⟩ ⟨hps, hs.2⟩ hps
    · have hanti : AntitoneOn H (Set.Icc l p) :=
        antitoneOn_of_deriv_nonpos (convex_Icc l p) hHc.continuousOn
          (fun x _ => (hHd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [(hHd x).deriv]
            rw [interior_Icc] at hx
            linarith [hL x hx])
      exact hanti ⟨hs.1, hsp⟩ ⟨hs.1.trans hsp, le_rfl⟩ hsp
  intro s hs
  have := key s hs
  simp only [hH] at this
  nlinarith

/-! ### the functional and its affine minorant -/

/-- the point positions of the gap vector (`ptsN` of the bridge). -/
def ptsK (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0

/-- the weighted n-point functional over an abstract kernel (`Fw` of the bridge). -/
def Gk (w : ℝ → ℝ) (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin (n - 1) → ℝ) (g : Fin (n - 1) → ℝ) : ℝ :=
  ∑ r, b r * g r
    + ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then a i j * w (ptsK n g j - ptsK n g i) else 0

/-- the gap sum of the pair (i, j) is linear in the gaps. -/
theorem ptsK_sub (n : ℕ) (g : Fin (n - 1) → ℝ) {i j : Fin n} (hij : (i : ℕ) < (j : ℕ)) :
    ptsK n g j - ptsK n g i = ∑ r : Fin (n - 1), if (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ) then g r else 0 := by
  unfold ptsK
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h1 : (r : ℕ) < (i : ℕ)
  · simp [h1, show (r : ℕ) < (j : ℕ) by omega, show ¬ ((i : ℕ) ≤ (r : ℕ)) by omega]
  · by_cases h2 : (r : ℕ) < (j : ℕ)
    · simp [h1, h2, show (i : ℕ) ≤ (r : ℕ) by omega]
    · simp [h1, h2]

theorem sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (X : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, X a b c = ∑ c, ∑ a, ∑ b, X a b c :=
  calc ∑ a, ∑ b, ∑ c, X a b c = ∑ a, ∑ c, ∑ b, X a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, X a b c := Finset.sum_comm

/-- **the pair sums are linear**: Σ_{i<j} c_ij (s_ij(d)) = Σ_r (Σ_{i ≤ r < j} c_ij) d_r. -/
theorem pair_lin (n : ℕ) (c : Fin n → Fin n → ℝ) (d : Fin (n - 1) → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) < (j : ℕ) then c i j * (ptsK n d j - ptsK n d i) else 0)
      = ∑ r : Fin (n - 1), (∑ i : Fin n, ∑ j : Fin n,
          if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ) then c i j else 0) * d r := by
  have e1 : ∀ i j : Fin n,
      (if (i : ℕ) < (j : ℕ) then c i j * (ptsK n d j - ptsK n d i) else 0)
      = ∑ r : Fin (n - 1), (if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ)
          then c i j else 0) * d r := by
    intro i j
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos hij, ptsK_sub n d hij, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ)
      · rw [if_pos hr, if_pos ⟨hij, hr⟩]
      · rw [if_neg hr, if_neg (fun h => hr h.2)]; ring
    · rw [if_neg hij]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg (fun h => hij h.1), zero_mul]
  simp_rw [e1, Finset.sum_mul]
  exact sum3_comm _

/-- the coefficient of g_r in the affine minorant. -/
def coef (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin (n - 1) → ℝ) (β : Fin n → Fin n → ℝ) (r : Fin (n - 1)) : ℝ :=
  b r + ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ) then a i j * β i j else 0

/-- the constant of the affine minorant. -/
def const (n : ℕ) (a α : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then a i j * α i j else 0

/-- **the affine minorant**: with a_ij ≥ 0 and w(s_ij) ≥ α_ij + β_ij s_ij at g,
Σ_r coef_r g_r + const ≤ Gk w n a b g. -/
theorem Gk_ge_affine (w : ℝ → ℝ) (n : ℕ) (a α β : Fin n → Fin n → ℝ) (b' : Fin (n - 1) → ℝ)
    (g : Fin (n - 1) → ℝ) (ha : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → 0 ≤ a i j)
    (hl : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) →
      α i j + β i j * (ptsK n g j - ptsK n g i) ≤ w (ptsK n g j - ptsK n g i)) :
    ∑ r, coef n a b' β r * g r + const n a α ≤ Gk w n a b' g := by
  -- the pair part of the minorant, expanded over the gaps
  have hlin : ∑ i : Fin n, ∑ j : Fin n,
        (if (i : ℕ) < (j : ℕ) then a i j * (α i j + β i j * (ptsK n g j - ptsK n g i)) else 0)
      = ∑ r, (coef n a b' β r - b' r) * g r + const n a α := by
    have e1 : ∀ i j : Fin n,
        (if (i : ℕ) < (j : ℕ) then a i j * (α i j + β i j * (ptsK n g j - ptsK n g i)) else 0)
        = (if (i : ℕ) < (j : ℕ) then a i j * α i j else 0)
          + ∑ r : Fin (n - 1), (if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ)
              then a i j * β i j else 0) * g r := by
      intro i j
      by_cases hij : (i : ℕ) < (j : ℕ)
      · rw [if_pos hij, if_pos hij, ptsK_sub n g hij, mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ)
        · rw [if_pos hr, if_pos ⟨hij, hr⟩]; ring
        · rw [if_neg hr, if_neg (fun h => hr h.2)]; ring
      · rw [if_neg hij, if_neg hij, zero_add]
        symm
        refine Finset.sum_eq_zero fun r _ => ?_
        rw [if_neg (fun h => hij h.1), zero_mul]
    simp_rw [e1, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    unfold coef
    simp_rw [add_sub_cancel_left, Finset.sum_mul]
    exact sum3_comm _
  have hmono : ∑ i : Fin n, ∑ j : Fin n,
        (if (i : ℕ) < (j : ℕ) then a i j * (α i j + β i j * (ptsK n g j - ptsK n g i)) else 0)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
        (if (i : ℕ) < (j : ℕ) then a i j * w (ptsK n g j - ptsK n g i) else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos hij, if_pos hij]
      exact mul_le_mul_of_nonneg_left (hl i j hij) (ha i j hij)
    · rw [if_neg hij, if_neg hij]
  unfold Gk
  have hsplit : ∑ r, coef n a b' β r * g r = ∑ r, b' r * g r + ∑ r, (coef n a b' β r - b' r) * g r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => by ring
  linarith

/-- **the corner minimum** of a linear form over a box. -/
theorem sum_ge_corner {k : ℕ} (c lo hi g : Fin k → ℝ) (h : ∀ r, lo r ≤ g r ∧ g r ≤ hi r) :
    ∑ r, min (c r * lo r) (c r * hi r) ≤ ∑ r, c r * g r := by
  refine Finset.sum_le_sum fun r _ => ?_
  rcases le_total 0 (c r) with hc | hc
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (h r).1 hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (h r).2 hc)

/-- the range of a pair sum over a box. -/
theorem ptsK_sub_mem {n : ℕ} {lo hi g : Fin (n - 1) → ℝ} (h : ∀ r, lo r ≤ g r ∧ g r ≤ hi r)
    {i j : Fin n} (hij : (i : ℕ) < (j : ℕ)) :
    ptsK n lo j - ptsK n lo i ≤ ptsK n g j - ptsK n g i
      ∧ ptsK n g j - ptsK n g i ≤ ptsK n hi j - ptsK n hi i := by
  rw [ptsK_sub n lo hij, ptsK_sub n g hij, ptsK_sub n hi hij]
  constructor <;> refine Finset.sum_le_sum fun r _ => ?_ <;> split_ifs
  · exact (h r).1
  · exact le_rfl
  · exact (h r).2
  · exact le_rfl

/-- **the box test**: lines valid on each pair's range give
Σ_r min(coef_r lo_r, coef_r hi_r) + const ≤ Gk on the whole box. -/
theorem Gk_ge_box (w : ℝ → ℝ) (n : ℕ) (a α β : Fin n → Fin n → ℝ) (b : Fin (n - 1) → ℝ)
    (lo hi : Fin (n - 1) → ℝ) (ha : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → 0 ≤ a i j)
    (hl : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → ∀ s, ptsK n lo j - ptsK n lo i ≤ s →
      s ≤ ptsK n hi j - ptsK n hi i → α i j + β i j * s ≤ w s)
    (g : Fin (n - 1) → ℝ) (hg : ∀ r, lo r ≤ g r ∧ g r ≤ hi r) :
    ∑ r, min (coef n a b β r * lo r) (coef n a b β r * hi r) + const n a α ≤ Gk w n a b g := by
  have h1 := Gk_ge_affine w n a α β b g ha fun i j hij =>
    hl i j hij _ (ptsK_sub_mem hg hij).1 (ptsK_sub_mem hg hij).2
  have h2 := sum_ge_corner (coef n a b β) lo hi g hg
  linarith

/-! ### the decidable minorant leaf test -/

/-- Σ_{i<n} f i by structural recursion (fast in the kernel). -/
def sumN (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => sumN f k + f k

theorem sumN_eq (f : ℕ → ℚ) (n : ℕ) : sumN f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

/-- a box sum Σ_{i ≤ r < j} x_r over ℕ-indexed rationals. -/
def boxSumQ (m : ℕ) (x : ℕ → ℚ) (i j : ℕ) : ℚ := sumN (fun r => if i ≤ r ∧ r < j then x r else 0) m

/-- the coefficient of g_r, over ℚ. -/
def coefQ (n : ℕ) (a β : ℕ → ℕ → ℚ) (b : ℕ → ℚ) (r : ℕ) : ℚ :=
  b r + sumN (fun i => sumN (fun j => if i < j ∧ i ≤ r ∧ r < j then a i j * β i j else 0) n) n

/-- the constant, over ℚ. -/
def constQ (n : ℕ) (a α : ℕ → ℕ → ℚ) : ℚ :=
  sumN (fun i => sumN (fun j => if i < j then a i j * α i j else 0) n) n

/-- the leaf test: every pair's line is certified on its range over the box (`lineOk lo hi α β`),
the pair weights are nonnegative, and the corner minimum of the affine minorant is at least C. -/
def minCheck (n : ℕ) (a α β : ℕ → ℕ → ℚ) (b lo hi : ℕ → ℚ) (C : ℚ)
    (lineOk : ℚ → ℚ → ℚ → ℚ → Bool) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j =>
    !decide (i < j) || (decide (0 ≤ a i j)
      && lineOk (boxSumQ (n - 1) lo i j) (boxSumQ (n - 1) hi i j) (α i j) (β i j))))
  && decide (C ≤ sumN (fun r => min (coefQ n a β b r * lo r) (coefQ n a β b r * hi r)) (n - 1)
      + constQ n a α)

theorem boxSum_cast (n : ℕ) (x : ℕ → ℚ) {i j : Fin n} (hij : (i : ℕ) < (j : ℕ)) :
    ((boxSumQ (n - 1) x i j : ℚ) : ℝ)
      = ptsK n (fun r => (x r : ℝ)) j - ptsK n (fun r => (x r : ℝ)) i := by
  rw [ptsK_sub n _ hij, boxSumQ, sumN_eq, ← Fin.sum_univ_eq_sum_range]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- **soundness of the leaf test.** -/
theorem minCheck_sound (w : ℝ → ℝ) {n : ℕ} {a α β : ℕ → ℕ → ℚ} {b lo hi : ℕ → ℚ} {C : ℚ}
    {lineOk : ℚ → ℚ → ℚ → ℚ → Bool}
    (hline : ∀ l h α β, lineOk l h α β = true → ∀ s : ℝ, (l : ℝ) ≤ s → s ≤ h → (α : ℝ) + β * s ≤ w s)
    (hc : minCheck n a α β b lo hi C lineOk = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) :
    (C : ℝ) ≤ Gk w n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) g := by
  simp only [minCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hc
  obtain ⟨hpairs, hC⟩ := hc
  have hpair : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → 0 ≤ a i j
      ∧ lineOk (boxSumQ (n - 1) lo i j) (boxSumQ (n - 1) hi i j) (α i j) (β i j) = true := by
    intro i j hij
    rcases hpairs i i.2 j j.2 with h | h
    · exact absurd hij h
    · exact h
  have hbox := Gk_ge_box w n (fun i j => (a i j : ℝ)) (fun i j => (α i j : ℝ)) (fun i j => (β i j : ℝ))
    (fun r => (b r : ℝ)) (fun r => (lo r : ℝ)) (fun r => (hi r : ℝ))
    (fun i j hij => by exact_mod_cast (hpair i j hij).1)
    (fun i j hij s hs1 hs2 => by
      rw [← boxSum_cast n lo hij] at hs1
      rw [← boxSum_cast n hi hij] at hs2
      exact hline _ _ _ _ (hpair i j hij).2 s hs1 hs2) g hg
  refine le_trans ?_ hbox
  rw [sumN_eq] at hC
  have hC' : (C : ℝ) ≤ ((∑ r ∈ range (n - 1), min (coefQ n a β b r * lo r) (coefQ n a β b r * hi r)
      + constQ n a α : ℚ) : ℝ) := by exact_mod_cast hC
  refine hC'.trans (le_of_eq ?_)
  push_cast
  have hcoef : ∀ r : Fin (n - 1), ((coefQ n a β b r : ℚ) : ℝ)
      = coef n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) (fun i j => (β i j : ℝ)) r := by
    intro r
    unfold coefQ coef
    simp only [sumN_eq]
    push_cast
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hconst : ((constQ n a α : ℚ) : ℝ) = const n (fun i j => (a i j : ℝ)) (fun i j => (α i j : ℝ)) := by
    unfold constQ const
    simp only [sumN_eq]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [← hconst]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun r => min (((coefQ n a β b r : ℚ) : ℝ) * (lo r : ℝ))
    (((coefQ n a β b r : ℚ) : ℝ) * (hi r : ℝ)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hcoef r]

end AMW.Min

end
