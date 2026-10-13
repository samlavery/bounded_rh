/-
AMW/PSDBasin.lean — Hessian-PSD basins for the weighted n-point functional over an abstract kernel w.

On a box where each pair term carries ℓ_t ≤ w″ on a range containing its pair sums at g and at q,
    a_t w(s) ≥ a_t [w(s_q) + w′(s_q)(s − s_q)] + (a_t ℓ_t/2)(s − s_q)²,
and if the quadratic form Σ_t a_t ℓ_t (Σ_{r∈t} d_r)² is positive semidefinite (checked by exact
Gaussian elimination, `psdN`), then Gk(g) ≥ Gk(q) + ∇Gk(q)·(g − q) on the box.
After the convex-basin layer of six-point-convex-basins-2 (typh, Apache-2.0: `Riemann.BasinC`,
`Riemann.Basin6`), made dimension-free.
-/
import AMW.Minorant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Field

noncomputable section

open Finset

namespace AMW.Min

/-! ### the second-order lower bound in one variable -/

/-- **ℓ ≤ w″ on [l, h] ⇒ w(s) ≥ w(p) + w′(p)(s − p) + (ℓ/2)(s − p)²** for p, s ∈ [l, h]. -/
theorem taylor2_lower {w w1 w2 : ℝ → ℝ} (hd : ∀ x, HasDerivAt w (w1 x) x)
    (hd1 : ∀ x, HasDerivAt w1 (w2 x) x) {l h p ℓ : ℝ} (hp : p ∈ Set.Icc l h)
    (hℓ : ∀ x ∈ Set.Icc l h, ℓ ≤ w2 x) :
    ∀ s ∈ Set.Icc l h, w p + w1 p * (s - p) + ℓ / 2 * (s - p) ^ 2 ≤ w s := by
  set K : ℝ → ℝ := fun s => w1 s - w1 p - ℓ * (s - p) with hK
  have hKd : ∀ x, HasDerivAt K (w2 x - ℓ) x := fun x => by
    have h2 : HasDerivAt (fun s : ℝ => ℓ * (s - p)) ℓ x := by
      simpa using ((hasDerivAt_id x).sub_const p).const_mul ℓ
    exact ((hd1 x).sub_const (w1 p)).sub h2
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun x => (hKd x).continuousAt
  have hKm : MonotoneOn K (Set.Icc l h) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l h) hKc.continuousOn
      (fun x _ => (hKd x).hasDerivWithinAt)
      (fun x hx => by linarith [hℓ x (interior_subset hx)])
  have hKp : K p = 0 := by simp [hK]
  set H : ℝ → ℝ := fun s => w s - w1 p * (s - p) - ℓ / 2 * (s - p) ^ 2 with hH
  have hHd : ∀ x, HasDerivAt H (K x) x := fun x => by
    have h1 : HasDerivAt (fun s : ℝ => w1 p * (s - p)) (w1 p) x := by
      simpa using ((hasDerivAt_id x).sub_const p).const_mul (w1 p)
    have h2 : HasDerivAt (fun s : ℝ => ℓ / 2 * (s - p) ^ 2) (ℓ * (x - p)) x := by
      have := (HasDerivAt.fun_pow ((hasDerivAt_id' x).sub_const p) 2).const_mul (ℓ / 2)
      exact this.congr_deriv (by first | ring | (simp; ring) | simp)
    exact (((hd x).sub h1).sub h2).congr_deriv (by simp only [hK])
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun x => (hHd x).continuousAt
  intro s hs
  have hHs : H p ≤ H s := by
    rcases le_total p s with hps | hsp
    · have hmono : MonotoneOn H (Set.Icc p h) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p h) hHc.continuousOn
          (fun x _ => (hHd x).hasDerivWithinAt)
          (fun x hx => by
            have hx' := interior_subset hx
            rw [← hKp]
            exact hKm ⟨hp.1, hp.2⟩ ⟨hp.1.trans hx'.1, hx'.2⟩ hx'.1)
      exact hmono ⟨le_rfl, hps.trans hs.2⟩ ⟨hps, hs.2⟩ hps
    · have hanti : AntitoneOn H (Set.Icc l p) :=
        antitoneOn_of_deriv_nonpos (convex_Icc l p) hHc.continuousOn
          (fun x _ => (hHd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [(hHd x).deriv]
            have hx' := interior_subset hx
            rw [← hKp]
            exact hKm ⟨hx'.1, hx'.2.trans hp.2⟩ ⟨hp.1, hp.2⟩ hx'.2)
      exact hanti ⟨hs.1, hsp⟩ ⟨hs.1.trans hsp, le_rfl⟩ hsp
  simp only [hH, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at hHs
  linarith

/-! ### positive semidefinite forms by exact elimination -/

/-- the quadratic form of a (ℕ-indexed) k × k matrix. -/
def qf (k : ℕ) (M : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range k, ∑ j ∈ range k, M i j * d i * d j

/-- one elimination step: the Schur complement of the (0, 0) entry. -/
def schurQ (M : ℕ → ℕ → ℚ) : ℕ → ℕ → ℚ := fun i j => M (i + 1) (j + 1) - M (i + 1) 0 * M 0 (j + 1) / M 0 0

/-- exact Gaussian elimination: positive pivots, the last one nonnegative. -/
def psdN : ℕ → (ℕ → ℕ → ℚ) → Bool
  | 0, _ => true
  | 1, M => decide (0 ≤ M 0 0)
  | k + 2, M => decide (0 < M 0 0) && psdN (k + 1) (schurQ M)

/-- symmetry of a k × k matrix. -/
def SymmK (k : ℕ) (M : ℕ → ℕ → ℝ) : Prop := ∀ i < k, ∀ j < k, M i j = M j i

theorem qf_succ (k : ℕ) (M : ℕ → ℕ → ℝ) (hM : SymmK (k + 1) M) (d : ℕ → ℝ) :
    qf (k + 1) M d = M 0 0 * d 0 ^ 2 + 2 * d 0 * ∑ j ∈ range k, M 0 (j + 1) * d (j + 1)
      + qf k (fun i j => M (i + 1) (j + 1)) (fun i => d (i + 1)) := by
  unfold qf
  have hrow : ∀ i, ∑ j ∈ range (k + 1), M i j * d i * d j
      = ∑ j ∈ range k, M i (j + 1) * d i * d (j + 1) + M i 0 * d i * d 0 :=
    fun i => Finset.sum_range_succ' _ _
  simp_rw [hrow]
  rw [Finset.sum_range_succ', Finset.sum_add_distrib]
  have A : ∑ i ∈ range k, M (i + 1) 0 * d (i + 1) * d 0 = ∑ i ∈ range k, M 0 (i + 1) * d (i + 1) * d 0 :=
    Finset.sum_congr rfl fun i hi => by
      rw [hM (i + 1) (by simp at hi; omega) 0 (by omega)]
  have B : 2 * d 0 * ∑ j ∈ range k, M 0 (j + 1) * d (j + 1)
      = ∑ j ∈ range k, M 0 (j + 1) * d 0 * d (j + 1) + ∑ i ∈ range k, M 0 (i + 1) * d (i + 1) * d 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [A, B]
  ring

theorem psdN_sound : ∀ (k : ℕ) (M : ℕ → ℕ → ℚ), psdN k M = true →
    SymmK k (fun i j => (M i j : ℝ)) → ∀ d : ℕ → ℝ, 0 ≤ qf k (fun i j => (M i j : ℝ)) d
  | 0, _, _, _, d => by simp [qf]
  | 1, M, h, _, d => by
    simp only [psdN, decide_eq_true_eq] at h
    have : (0 : ℝ) ≤ M 0 0 := by exact_mod_cast h
    simp only [qf, Finset.sum_range_one]
    nlinarith [sq_nonneg (d 0)]
  | k + 2, M, h, hM, d => by
    simp only [psdN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h0, hs⟩ := h
    have h0' : (0 : ℝ) < M 0 0 := by exact_mod_cast h0
    have hMs : SymmK (k + 1) (fun i j => ((schurQ M i j : ℚ) : ℝ)) := by
      have hM' : ∀ i < k + 2, ∀ j < k + 2, (M i j : ℝ) = M j i := hM
      intro i hi j hj
      simp only [schurQ]; push_cast
      rw [hM' (i + 1) (by omega) (j + 1) (by omega), hM' (i + 1) (by omega) 0 (by omega),
        hM' 0 (by omega) (j + 1) (by omega)]
      ring
    have ih := psdN_sound (k + 1) (schurQ M) hs hMs (fun i => d (i + 1))
    rw [qf_succ (k + 1) _ hM d]
    set S := ∑ j ∈ range (k + 1), (M 0 (j + 1) : ℝ) * d (j + 1) with hS
    have hschur : qf (k + 1) (fun i j => ((schurQ M i j : ℚ) : ℝ)) (fun i => d (i + 1))
        = qf (k + 1) (fun i j => (M (i + 1) (j + 1) : ℝ)) (fun i => d (i + 1)) - S ^ 2 / M 0 0 := by
      unfold qf
      simp only [schurQ]; push_cast
      have hS2 : S ^ 2 = ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
          (M 0 (i + 1) : ℝ) * d (i + 1) * ((M 0 (j + 1) : ℝ) * d (j + 1)) := by
        rw [sq, hS, Finset.sum_mul_sum]
      rw [hS2, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hM' : ∀ i < k + 2, ∀ j < k + 2, (M i j : ℝ) = M j i := hM
      rw [hM' (i + 1) (by simp at hi; omega) 0 (by omega)]
      field_simp
    have hsq : 0 ≤ (M 0 0 : ℝ) * (d 0 + S / M 0 0) ^ 2 := by positivity
    have e : (M 0 0 : ℝ) * d 0 ^ 2 + 2 * d 0 * S
        = (M 0 0 : ℝ) * (d 0 + S / M 0 0) ^ 2 - S ^ 2 / M 0 0 := by
      field_simp; ring
    rw [hschur] at ih
    linarith

/-! ### the tangent-plane bound on a basin -/

theorem ptsK_sub_fun (n : ℕ) (g q : Fin (n - 1) → ℝ) (i : Fin n) :
    ptsK n (fun r => g r - q r) i = ptsK n g i - ptsK n q i := by
  unfold ptsK
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

/-- the gradient of Gk at q. -/
def gradK (w1 : ℝ → ℝ) (n : ℕ) (a : Fin n → Fin n → ℝ) (b q : Fin (n - 1) → ℝ) (r : Fin (n - 1)) : ℝ :=
  b r + ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ) then
      a i j * w1 (ptsK n q j - ptsK n q i) else 0

/-- **the tangent plane at q bounds Gk below on a basin**: each pair sum at g and at q lies in
[L_ij, H_ij], where ℓ_ij ≤ w″; and the form Σ a_ij ℓ_ij (s_ij(g) − s_ij(q))² is nonnegative. -/
theorem Gk_ge_tangent {w w1 w2 : ℝ → ℝ} (hd : ∀ x, HasDerivAt w (w1 x) x)
    (hd1 : ∀ x, HasDerivAt w1 (w2 x) x) (n : ℕ) (a ℓ L H : Fin n → Fin n → ℝ)
    (b q g : Fin (n - 1) → ℝ) (ha : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → 0 ≤ a i j)
    (hq : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → ptsK n q j - ptsK n q i ∈ Set.Icc (L i j) (H i j))
    (hg : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → ptsK n g j - ptsK n g i ∈ Set.Icc (L i j) (H i j))
    (hℓ : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → ∀ x ∈ Set.Icc (L i j) (H i j), ℓ i j ≤ w2 x)
    (hpsd : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then
      a i j * ℓ i j * ((ptsK n g j - ptsK n g i) - (ptsK n q j - ptsK n q i)) ^ 2 else 0) :
    Gk w n a b q + ∑ r, gradK w1 n a b q r * (g r - q r) ≤ Gk w n a b g := by
  set sg : Fin n → Fin n → ℝ := fun i j => ptsK n g j - ptsK n g i with hsg
  set sq : Fin n → Fin n → ℝ := fun i j => ptsK n q j - ptsK n q i with hsq
  -- per term
  have hterm : ∀ i j : Fin n,
      (if (i : ℕ) < (j : ℕ) then a i j * w (sq i j) + a i j * w1 (sq i j) * (sg i j - sq i j)
        + a i j * ℓ i j * (sg i j - sq i j) ^ 2 / 2 else 0)
      ≤ (if (i : ℕ) < (j : ℕ) then a i j * w (sg i j) else 0) := by
    intro i j
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos hij, if_pos hij]
      have ht := taylor2_lower hd hd1 (hq i j hij) (hℓ i j hij) (sg i j) (hg i j hij)
      have := mul_le_mul_of_nonneg_left ht (ha i j hij)
      nlinarith
    · rw [if_neg hij, if_neg hij]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
  -- split the left side
  have hsplit : ∀ i j : Fin n,
      (if (i : ℕ) < (j : ℕ) then a i j * w (sq i j) + a i j * w1 (sq i j) * (sg i j - sq i j)
        + a i j * ℓ i j * (sg i j - sq i j) ^ 2 / 2 else 0)
      = (if (i : ℕ) < (j : ℕ) then a i j * w (sq i j) else 0)
        + (if (i : ℕ) < (j : ℕ) then (a i j * w1 (sq i j)) *
            (ptsK n (fun r => g r - q r) j - ptsK n (fun r => g r - q r) i) else 0)
        + (if (i : ℕ) < (j : ℕ) then a i j * ℓ i j * (sg i j - sq i j) ^ 2 else 0) / 2 := by
    intro i j
    split_ifs
    · rw [ptsK_sub_fun, ptsK_sub_fun]; simp only [hsg, hsq]; ring
    · ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_div] at hsum
  rw [pair_lin n (fun i j => a i j * w1 (sq i j)) (fun r => g r - q r)] at hsum
  have hpsd' : 0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      if (i : ℕ) < (j : ℕ) then a i j * ℓ i j * (sg i j - sq i j) ^ 2 else 0) / 2 := by
    have := hpsd; positivity
  have hgrad : ∑ r, gradK w1 n a b q r * (g r - q r)
      = ∑ r, b r * (g r - q r) + ∑ r : Fin (n - 1), (∑ i : Fin n, ∑ j : Fin n,
          if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ) then a i j * w1 (sq i j) else 0)
          * (g r - q r) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [gradK, hsq]; ring
  have hb : ∑ r, b r * (g r - q r) = ∑ r, b r * g r - ∑ r, b r * q r := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  unfold Gk
  rw [hgrad, hb]
  simp only [hsg, hsq] at hsum hpsd'
  linarith

/-! ### PSD from an exact factorisation M = F D Fᵀ -/

/-- the (r, r') entry of F·diag(D)·Fᵀ over m columns. -/
def fdfQ (m : ℕ) (F : ℕ → ℕ → ℚ) (D : ℕ → ℚ) (r r' : ℕ) : ℚ :=
  sumN (fun c => F r c * D c * F r' c) m

/-- the factorisation check: D ≥ 0 and M = F D Fᵀ on the k × k block. -/
def factorOk (k m : ℕ) (M F : ℕ → ℕ → ℚ) (D : ℕ → ℚ) : Bool :=
  (List.range m).all (fun c => decide (0 ≤ D c))
    && (List.range k).all (fun r => (List.range k).all (fun r' => decide (M r r' = fdfQ m F D r r')))

theorem factorOk_sound {k m : ℕ} {M F : ℕ → ℕ → ℚ} {D : ℕ → ℚ} (h : factorOk k m M F D = true)
    (d : ℕ → ℝ) : 0 ≤ qf k (fun i j => (M i j : ℝ)) d := by
  simp only [factorOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hD, hM⟩ := h
  have e : qf k (fun i j => (M i j : ℝ)) d
      = ∑ c ∈ range m, (D c : ℝ) * (∑ r ∈ range k, (F r c : ℝ) * d r) ^ 2 := by
    unfold qf
    have hM' : ∀ r ∈ range k, ∀ r' ∈ range k,
        (M r r' : ℝ) * d r * d r' = ∑ c ∈ range m, (D c : ℝ) * ((F r c : ℝ) * d r) * ((F r' c : ℝ) * d r') := by
      intro r hr r' hr'
      rw [hM r (Finset.mem_range.mp hr) r' (Finset.mem_range.mp hr'), fdfQ, sumN_eq]
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun r' hr' => hM' r hr r' hr']
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun r' _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sq]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by ring
  rw [e]
  refine Finset.sum_nonneg fun c hc => mul_nonneg ?_ (sq_nonneg _)
  exact_mod_cast hD c (Finset.mem_range.mp hc)

/-! ### the pair form as a matrix form -/

/-- the pair matrix Σ_{i<j} c_ij e_ij e_ijᵀ on the gaps (ℕ-indexed). -/
def pairMat (n : ℕ) (c : ℕ → ℕ → ℝ) (r r' : ℕ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i < j ∧ i ≤ r ∧ r < j ∧ i ≤ r' ∧ r' < j then c i j else 0

/-- a gap vector extended by zero to ℕ. -/
def extG {m : ℕ} (d : Fin m → ℝ) (r : ℕ) : ℝ := if h : r < m then d ⟨r, h⟩ else 0

theorem sum4_comm {s t u v : Finset ℕ} (X : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ r ∈ u, ∑ r' ∈ v, X i j r r' = ∑ r ∈ u, ∑ r' ∈ v, ∑ i ∈ s, ∑ j ∈ t, X i j r r' := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ r ∈ u, ∑ r' ∈ v, X i j r r'
      = ∑ i ∈ s, ∑ r ∈ u, ∑ j ∈ t, ∑ r' ∈ v, X i j r r' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ r ∈ u, ∑ r' ∈ v, ∑ j ∈ t, X i j r r' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r ∈ u, ∑ i ∈ s, ∑ r' ∈ v, ∑ j ∈ t, X i j r r' := Finset.sum_comm
    _ = ∑ r ∈ u, ∑ r' ∈ v, ∑ i ∈ s, ∑ j ∈ t, X i j r r' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem ptsK_sub_range (n : ℕ) (d : Fin (n - 1) → ℝ) {i j : Fin n} (hij : (i : ℕ) < (j : ℕ)) :
    ptsK n d j - ptsK n d i = ∑ r ∈ range (n - 1), if (i : ℕ) ≤ r ∧ r < (j : ℕ) then extG d r else 0 := by
  rw [ptsK_sub n d hij, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [extG, r.2]

/-- **Σ_{i<j} c_ij (s_ij(d))² is the matrix form of the pair matrix.** -/
theorem pairForm_eq (n : ℕ) (c : ℕ → ℕ → ℝ) (d : Fin (n - 1) → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) < (j : ℕ) then c i j * (ptsK n d j - ptsK n d i) ^ 2 else 0)
      = qf (n - 1) (pairMat n c) (extG d) := by
  have hT : ∀ i j : Fin n,
      (if (i : ℕ) < (j : ℕ) then c i j * (ptsK n d j - ptsK n d i) ^ 2 else 0)
      = ∑ r ∈ range (n - 1), ∑ r' ∈ range (n - 1),
          (if (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ r ∧ r < (j : ℕ) ∧ (i : ℕ) ≤ r' ∧ r' < (j : ℕ)
            then c i j else 0) * extG d r * extG d r' := by
    intro i j
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos hij, ptsK_sub_range n d hij, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      split_ifs <;> first | ring1 | (exfalso; tauto)
    · rw [if_neg hij]
      symm
      refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun r' _ => ?_
      rw [if_neg (fun h => hij h.1)]; ring
  set X : ℕ → ℕ → ℕ → ℕ → ℝ := fun i j r r' =>
    (if i < j ∧ i ≤ r ∧ r < j ∧ i ≤ r' ∧ r' < j then c i j else 0) * extG d r * extG d r' with hX
  simp_rw [hT]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n, ∑ r ∈ range (n - 1), ∑ r' ∈ range (n - 1),
      X i j r r') n]
  rw [Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun j => ∑ r ∈ range (n - 1),
      ∑ r' ∈ range (n - 1), X i j r r') n]
  rw [sum4_comm]
  unfold qf pairMat
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

/-! ### the rational pair matrix and the PSD hypothesis of the tangent bound -/

/-- the pair matrix over ℚ (for kernel evaluation). -/
def pairMatQ (n : ℕ) (c : ℕ → ℕ → ℚ) (r r' : ℕ) : ℚ :=
  sumN (fun i => sumN (fun j => if i < j ∧ i ≤ r ∧ r < j ∧ i ≤ r' ∧ r' < j then c i j else 0) n) n

theorem pairMatQ_cast (n : ℕ) (c : ℕ → ℕ → ℚ) (r r' : ℕ) :
    ((pairMatQ n c r r' : ℚ) : ℝ) = pairMat n (fun i j => (c i j : ℝ)) r r' := by
  unfold pairMatQ pairMat
  simp only [sumN_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **an exact factorisation of the pair matrix makes the pair form nonnegative.** -/
theorem pairForm_nonneg_of_factor {n m : ℕ} {c : ℕ → ℕ → ℚ} {F : ℕ → ℕ → ℚ} {D : ℕ → ℚ}
    (h : factorOk (n - 1) m (pairMatQ n c) F D = true) (d : Fin (n - 1) → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      (if (i : ℕ) < (j : ℕ) then (c i j : ℝ) * (ptsK n d j - ptsK n d i) ^ 2 else 0) := by
  rw [pairForm_eq n (fun i j => (c i j : ℝ)) d]
  have := factorOk_sound h (extG d)
  simp only [pairMatQ_cast] at this
  exact this

/-- the same for the differences g − q, in the form `Gk_ge_tangent` asks. -/
theorem tangent_psd_of_factor {n m : ℕ} {c : ℕ → ℕ → ℚ} {F : ℕ → ℕ → ℚ} {D : ℕ → ℚ}
    (h : factorOk (n - 1) m (pairMatQ n c) F D = true) (a ℓ : Fin n → Fin n → ℝ)
    (hc : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → a i j * ℓ i j = (c i j : ℝ)) (g q : Fin (n - 1) → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then
      a i j * ℓ i j * ((ptsK n g j - ptsK n g i) - (ptsK n q j - ptsK n q i)) ^ 2 else 0 := by
  have h0 := pairForm_nonneg_of_factor h (fun r => g r - q r)
  refine h0.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hc i j hij, ptsK_sub_fun, ptsK_sub_fun]; ring
  · rfl

/-! ### PSD from a rounded factorisation and a diagonally dominant residual -/

/-- the residual E = M − F·diag(D)·Fᵀ. -/
def resQ (m : ℕ) (M F : ℕ → ℕ → ℚ) (D : ℕ → ℚ) (r r' : ℕ) : ℚ := M r r' - fdfQ m F D r r'

/-- D ≥ 0, and every row of the residual is diagonally dominant (with the symmetrised off-diagonal). -/
def ddOk (k m : ℕ) (M F : ℕ → ℕ → ℚ) (D : ℕ → ℚ) : Bool :=
  (List.range m).all (fun c => decide (0 ≤ D c))
    && (List.range k).all (fun r => decide (sumN (fun r' => if r' = r then 0 else
        (|resQ m M F D r r'| + |resQ m M F D r' r|) / 2) k ≤ resQ m M F D r r))

theorem qf_ge_dd (k : ℕ) (E : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    ∑ r ∈ range k, d r ^ 2 * (E r r - ∑ r' ∈ range k, if r' = r then 0 else (|E r r'| + |E r' r|) / 2)
      ≤ qf k E d := by
  unfold qf
  have hT : ∀ r ∈ range k, ∀ r' ∈ range k,
      (if r' = r then E r r * d r ^ 2 else -(|E r r'| * (d r ^ 2 + d r' ^ 2) / 2)) ≤ E r r' * d r * d r' := by
    intro r _ r' _
    split_ifs with h
    · subst h; ring_nf; rfl
    · have h1 : |E r r' * d r * d r'| ≤ |E r r'| * (d r ^ 2 + d r' ^ 2) / 2 := by
        rw [abs_mul, abs_mul]
        have : |d r| * |d r'| ≤ (d r ^ 2 + d r' ^ 2) / 2 := by
          nlinarith [sq_nonneg (|d r| - |d r'|), sq_abs (d r), sq_abs (d r')]
        nlinarith [abs_nonneg (E r r')]
      linarith [neg_abs_le (E r r' * d r * d r')]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun r' hr' => hT r hr r' hr')
  -- evaluate the left side
  have hsplit : ∀ r ∈ range k, ∑ r' ∈ range k,
      (if r' = r then E r r * d r ^ 2 else -(|E r r'| * (d r ^ 2 + d r' ^ 2) / 2))
      = E r r * d r ^ 2 - ∑ r' ∈ range k, (if r' = r then 0 else |E r r'| * d r ^ 2 / 2)
        - ∑ r' ∈ range k, (if r' = r then 0 else |E r r'| * d r' ^ 2 / 2) := by
    intro r hr
    have : ∀ r' ∈ range k, (if r' = r then E r r * d r ^ 2 else -(|E r r'| * (d r ^ 2 + d r' ^ 2) / 2))
        = (if r' = r then E r r * d r ^ 2 else 0) - (if r' = r then 0 else |E r r'| * d r ^ 2 / 2)
          - (if r' = r then 0 else |E r r'| * d r' ^ 2 / 2) := fun r' _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' (range k) r,
      if_pos hr]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- the transposed double sum
  have hswap : ∑ r ∈ range k, ∑ r' ∈ range k, (if r' = r then 0 else |E r r'| * d r' ^ 2 / 2)
      = ∑ r ∈ range k, ∑ r' ∈ range k, (if r' = r then 0 else |E r' r| * d r ^ 2 / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    by_cases h : r' = r
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_sub, Finset.mul_sum, mul_comm]
  have : ∀ r' ∈ range k, (d r ^ 2 * if r' = r then 0 else (|E r r'| + |E r' r|) / 2)
      = (if r' = r then 0 else |E r r'| * d r ^ 2 / 2) + (if r' = r then 0 else |E r' r| * d r ^ 2 / 2) :=
    fun r' _ => by split_ifs <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  ring

theorem ddOk_sound {k m : ℕ} {M F : ℕ → ℕ → ℚ} {D : ℕ → ℚ} (h : ddOk k m M F D = true) (d : ℕ → ℝ) :
    0 ≤ qf k (fun i j => (M i j : ℝ)) d := by
  simp only [ddOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hD, hdd⟩ := h
  -- M = F D Fᵀ + E
  have hF : 0 ≤ qf k (fun i j => (fdfQ m F D i j : ℝ)) d := by
    have hok : factorOk k m (fun i j => fdfQ m F D i j) F D = true := by
      simp only [factorOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
      exact ⟨hD, fun _ _ _ _ => trivial⟩
    exact factorOk_sound hok d
  have hE : 0 ≤ qf k (fun i j => (resQ m M F D i j : ℝ)) d := by
    refine le_trans ?_ (qf_ge_dd k _ d)
    refine Finset.sum_nonneg fun r hr => mul_nonneg (sq_nonneg _) ?_
    have := hdd r (Finset.mem_range.mp hr)
    rw [sumN_eq] at this
    have h' : (0 : ℝ) ≤ ((resQ m M F D r r - ∑ r' ∈ range k,
        (if r' = r then 0 else (|resQ m M F D r r'| + |resQ m M F D r' r|) / 2) : ℚ) : ℝ) := by
      exact_mod_cast sub_nonneg.mpr this
    refine h'.trans (le_of_eq ?_)
    rw [Rat.cast_sub, Rat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun r' _ => ?_
    split_ifs <;> push_cast <;> rfl
  have hsum : qf k (fun i j => (M i j : ℝ)) d
      = qf k (fun i j => (fdfQ m F D i j : ℝ)) d + qf k (fun i j => (resQ m M F D i j : ℝ)) d := by
    unfold qf resQ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  linarith

/-- `ddOk` on the pair matrix makes the tangent bound's quadratic form nonnegative. -/
theorem tangent_psd_of_dd {n m : ℕ} {c : ℕ → ℕ → ℚ} {F : ℕ → ℕ → ℚ} {D : ℕ → ℚ}
    (h : ddOk (n - 1) m (pairMatQ n c) F D = true) (a ℓ : Fin n → Fin n → ℝ)
    (hc : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → a i j * ℓ i j = (c i j : ℝ)) (g q : Fin (n - 1) → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then
      a i j * ℓ i j * ((ptsK n g j - ptsK n g i) - (ptsK n q j - ptsK n q i)) ^ 2 else 0 := by
  have h0 := ddOk_sound h (extG (fun r => g r - q r))
  simp only [pairMatQ_cast] at h0
  rw [← pairForm_eq n (fun i j => (c i j : ℝ)) (fun r => g r - q r)] at h0
  refine h0.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hc i j hij, ptsK_sub_fun, ptsK_sub_fun]; ring
  · rfl

/-! ### the decidable basin test -/

/-- lower end of a product of two intervals. -/
def imulLo (x1 x2 y1 y2 : ℚ) : ℚ := min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2))

theorem imulLo_le {x1 x2 y1 y2 : ℚ} {x y : ℝ} (hx : (x1 : ℝ) ≤ x ∧ x ≤ x2) (hy : (y1 : ℝ) ≤ y ∧ y ≤ y2) :
    ((imulLo x1 x2 y1 y2 : ℚ) : ℝ) ≤ x * y := by
  unfold imulLo
  push_cast
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  have hcol : ∀ c : ℝ, min (c * y1) (c * y2) ≤ c * y := fun c => by
    rcases le_total 0 c with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy2 hc)
  have hrow : min ((x1 : ℝ) * y) (x2 * y) ≤ x * y := by
    rcases le_total 0 y with hy0 | hy0
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx1 hy0)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx2 hy0)
  exact (min_le_min (hcol x1) (hcol x2)).trans hrow

/-- the gradient enclosure at q, coordinate r: b_r + Σ_{i ≤ r < j} a_ij [u_ij, U_ij] (a ≥ 0). -/
def gradLoQ (n : ℕ) (a u : ℕ → ℕ → ℚ) (b : ℕ → ℚ) (r : ℕ) : ℚ :=
  b r + sumN (fun i => sumN (fun j => if i < j ∧ i ≤ r ∧ r < j then a i j * u i j else 0) n) n

/-- the basin test.  Per pair: a_ij ≥ 0, the w″ bound ℓ_ij on the hull of its range and its value at q
(`w2Ok`), a value lower bound v_ij at s_ij(q) (`valOk`), a derivative enclosure [u_ij, U_ij] there
(`d1Ok`); the pair matrix Σ a_ij ℓ_ij e_ij e_ijᵀ is PSD (`psdN`); and the tangent plane's corner
minimum is at least C. -/
def basinCheck (n : ℕ) (a ℓ v u U : ℕ → ℕ → ℚ) (b lo hi q : ℕ → ℚ) (C : ℚ)
    (w2Ok : ℚ → ℚ → ℚ → Bool) (valOk : ℚ → ℚ → Bool) (d1Ok : ℚ → ℚ → ℚ → Bool)
    (psd : (ℕ → ℕ → ℚ) → Bool) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j =>
    !decide (i < j) || (decide (0 ≤ a i j)
      && w2Ok (min (boxSumQ (n - 1) lo i j) (boxSumQ (n - 1) q i j))
          (max (boxSumQ (n - 1) hi i j) (boxSumQ (n - 1) q i j)) (ℓ i j)
      && valOk (boxSumQ (n - 1) q i j) (v i j) && d1Ok (boxSumQ (n - 1) q i j) (u i j) (U i j))))
  && psd (pairMatQ n (fun i j => a i j * ℓ i j))
  && decide (C ≤ sumN (fun r => b r * q r) (n - 1) + constQ n a v
      + sumN (fun r => imulLo (gradLoQ n a u b r) (gradLoQ n a U b r) (lo r - q r) (hi r - q r)) (n - 1))

theorem pairMatQ_symm (n : ℕ) (c : ℕ → ℕ → ℚ) (r r' : ℕ) : pairMatQ n c r r' = pairMatQ n c r' r := by
  unfold pairMatQ
  simp only [sumN_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ i ≤ r ∧ r < j ∧ i ≤ r' ∧ r' < j
  · rw [if_pos h, if_pos ⟨h.1, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.2.2.1, h'.2.2.2.2, h'.2.1, h'.2.2.1⟩)]

/-- `psdN` of the pair matrix makes the tangent bound's quadratic form nonnegative. -/
theorem tangent_psd_of_psdN {n : ℕ} {c : ℕ → ℕ → ℚ} (h : psdN (n - 1) (pairMatQ n c) = true)
    (a ℓ : Fin n → Fin n → ℝ) (hc : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → a i j * ℓ i j = (c i j : ℝ))
    (g q : Fin (n - 1) → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then
      a i j * ℓ i j * ((ptsK n g j - ptsK n g i) - (ptsK n q j - ptsK n q i)) ^ 2 else 0 := by
  have hsym : SymmK (n - 1) (fun i j => ((pairMatQ n c i j : ℚ) : ℝ)) := fun i _ j _ => by
    simp only [pairMatQ_symm n c i j]
  have h0 := psdN_sound (n - 1) (pairMatQ n c) h hsym (extG (fun r => g r - q r))
  simp only [pairMatQ_cast] at h0
  rw [← pairForm_eq n (fun i j => (c i j : ℝ)) (fun r => g r - q r)] at h0
  refine h0.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hc i j hij, ptsK_sub_fun, ptsK_sub_fun]; ring
  · rfl

theorem pairMatQ_symmK (n : ℕ) (c : ℕ → ℕ → ℚ) : SymmK (n - 1) (fun i j => ((pairMatQ n c i j : ℚ) : ℝ)) :=
  fun i _ j _ => by simp only [pairMatQ_symm n c i j]

/-- a nonnegative quadratic form of the pair matrix makes the tangent bound's form nonnegative. -/
theorem tangent_psd_of_qf {n : ℕ} {c : ℕ → ℕ → ℚ}
    (h : ∀ d : ℕ → ℝ, 0 ≤ qf (n - 1) (fun i j => ((pairMatQ n c i j : ℚ) : ℝ)) d)
    (a ℓ : Fin n → Fin n → ℝ) (hc : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → a i j * ℓ i j = (c i j : ℝ))
    (g q : Fin (n - 1) → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) < (j : ℕ) then
      a i j * ℓ i j * ((ptsK n g j - ptsK n g i) - (ptsK n q j - ptsK n q i)) ^ 2 else 0 := by
  have h0 := h (extG (fun r => g r - q r))
  simp only [pairMatQ_cast] at h0
  rw [← pairForm_eq n (fun i j => (c i j : ℝ)) (fun r => g r - q r)] at h0
  refine h0.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hc i j hij, ptsK_sub_fun, ptsK_sub_fun]; ring
  · rfl

/-- the two PSD checks, in the form the basin test asks. -/
theorem psdN_ok (k : ℕ) : ∀ M : ℕ → ℕ → ℚ, psdN k M = true → SymmK k (fun i j => (M i j : ℝ)) →
    ∀ d, 0 ≤ qf k (fun i j => (M i j : ℝ)) d := fun M h hs d => psdN_sound k M h hs d

theorem ddOk_ok (k m : ℕ) (F : ℕ → ℕ → ℚ) (D : ℕ → ℚ) : ∀ M : ℕ → ℕ → ℚ, ddOk k m M F D = true →
    SymmK k (fun i j => (M i j : ℝ)) → ∀ d, 0 ≤ qf k (fun i j => (M i j : ℝ)) d :=
  fun _ h _ d => ddOk_sound h d

/-- **soundness of the basin test.** -/
theorem basinCheck_sound {w w1 w2 : ℝ → ℝ} (hd : ∀ x, HasDerivAt w (w1 x) x)
    (hd1 : ∀ x, HasDerivAt w1 (w2 x) x) {n : ℕ} {a ℓ v u U : ℕ → ℕ → ℚ} {b lo hi q : ℕ → ℚ} {C : ℚ}
    {w2Ok : ℚ → ℚ → ℚ → Bool} {valOk : ℚ → ℚ → Bool} {d1Ok : ℚ → ℚ → ℚ → Bool}
    {psd : (ℕ → ℕ → ℚ) → Bool}
    (hw2 : ∀ L H ℓ, w2Ok L H ℓ = true → ∀ x : ℝ, (L : ℝ) ≤ x → x ≤ H → (ℓ : ℝ) ≤ w2 x)
    (hval : ∀ s v, valOk s v = true → (v : ℝ) ≤ w s)
    (hd1o : ∀ s u U, d1Ok s u U = true → (u : ℝ) ≤ w1 s ∧ w1 s ≤ U)
    (hpsdS : ∀ M : ℕ → ℕ → ℚ, psd M = true → SymmK (n - 1) (fun i j => (M i j : ℝ)) →
      ∀ d, 0 ≤ qf (n - 1) (fun i j => (M i j : ℝ)) d)
    (hc : basinCheck n a ℓ v u U b lo hi q C w2Ok valOk d1Ok psd = true) (g : Fin (n - 1) → ℝ)
    (hg : ∀ r : Fin (n - 1), (lo r : ℝ) ≤ g r ∧ g r ≤ hi r) :
    (C : ℝ) ≤ Gk w n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) g := by
  simp only [basinCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hc
  obtain ⟨⟨hpairs, hpsd⟩, hC⟩ := hc
  have hpair : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → 0 ≤ a i j
      ∧ w2Ok (min (boxSumQ (n - 1) lo i j) (boxSumQ (n - 1) q i j))
          (max (boxSumQ (n - 1) hi i j) (boxSumQ (n - 1) q i j)) (ℓ i j) = true
      ∧ valOk (boxSumQ (n - 1) q i j) (v i j) = true
      ∧ d1Ok (boxSumQ (n - 1) q i j) (u i j) (U i j) = true := by
    intro i j hij
    rcases hpairs i i.2 j j.2 with h | h
    · exact absurd hij h
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  set qR : Fin (n - 1) → ℝ := fun r => (q r : ℝ) with hqR
  have hsq : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) →
      ptsK n qR j - ptsK n qR i = ((boxSumQ (n - 1) q i j : ℚ) : ℝ) := fun i j hij =>
    (boxSum_cast n q hij).symm
  -- the tangent bound
  have htan := Gk_ge_tangent hd hd1 n (fun i j => (a i j : ℝ)) (fun i j => (ℓ i j : ℝ))
    (fun i j => ((min (boxSumQ (n - 1) lo i j) (boxSumQ (n - 1) q i j) : ℚ) : ℝ))
    (fun i j => ((max (boxSumQ (n - 1) hi i j) (boxSumQ (n - 1) q i j) : ℚ) : ℝ))
    (fun r => (b r : ℝ)) qR g
    (fun i j hij => by exact_mod_cast (hpair i j hij).1)
    (fun i j hij => by
      rw [hsq i j hij]; push_cast
      exact ⟨min_le_right _ _, le_max_right _ _⟩)
    (fun i j hij => by
      have hm := ptsK_sub_mem (lo := fun r => (lo r : ℝ)) (hi := fun r => (hi r : ℝ)) hg hij
      rw [← boxSum_cast n lo hij, ← boxSum_cast n hi hij] at hm
      push_cast
      exact ⟨(min_le_left _ _).trans hm.1, hm.2.trans (le_max_left _ _)⟩)
    (fun i j hij x hx => hw2 _ _ _ (hpair i j hij).2.1 x hx.1 hx.2)
    (tangent_psd_of_qf (hpsdS _ hpsd (pairMatQ_symmK n _)) _ _ (fun i j _ => by push_cast; ring) g qR)
  refine le_trans ?_ htan
  simp only [sumN_eq] at hC
  have hC' : (C : ℝ) ≤ ((∑ r ∈ range (n - 1), b r * q r + constQ n a v
      + ∑ r ∈ range (n - 1), imulLo (gradLoQ n a u b r) (gradLoQ n a U b r) (lo r - q r) (hi r - q r) : ℚ) : ℝ) := by
    exact_mod_cast hC
  refine hC'.trans ?_
  push_cast
  -- the value part
  have hGq : (∑ r ∈ range (n - 1), ((b r : ℚ) : ℝ) * (q r : ℝ)) + ((constQ n a v : ℚ) : ℝ)
      ≤ Gk w n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) qR := by
    unfold Gk constQ
    simp only [sumN_eq]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun r => ((b r : ℚ) : ℝ) * (q r : ℝ))]
    apply add_le_add le_rfl
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos hij, if_pos hij]
      push_cast
      rw [hsq i j hij]
      exact mul_le_mul_of_nonneg_left (hval _ _ (hpair i j hij).2.2.1) (by exact_mod_cast (hpair i j hij).1)
    · rw [if_neg hij, if_neg hij]; simp
  -- the gradient part
  have hgrad : ∀ r : Fin (n - 1),
      ((gradLoQ n a u b r : ℚ) : ℝ) ≤ gradK w1 n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) qR r
      ∧ gradK w1 n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) qR r ≤ ((gradLoQ n a U b r : ℚ) : ℝ) := by
    intro r
    unfold gradLoQ gradK
    simp only [sumN_eq]
    push_cast
    constructor <;> refine add_le_add le_rfl ?_ <;> rw [← Fin.sum_univ_eq_sum_range] <;>
      refine Finset.sum_le_sum fun i _ => ?_ <;> rw [← Fin.sum_univ_eq_sum_range] <;>
      refine Finset.sum_le_sum fun j _ => ?_ <;> by_cases hr : (i : ℕ) < (j : ℕ) ∧ (i : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < (j : ℕ)
    · rw [if_pos hr, if_pos hr]; push_cast
      rw [hsq i j hr.1]
      exact mul_le_mul_of_nonneg_left (hd1o _ _ _ (hpair i j hr.1).2.2.2).1
        (by exact_mod_cast (hpair i j hr.1).1)
    · rw [if_neg hr, if_neg hr]; simp
    · rw [if_pos hr, if_pos hr]; push_cast
      rw [hsq i j hr.1]
      exact mul_le_mul_of_nonneg_left (hd1o _ _ _ (hpair i j hr.1).2.2.2).2
        (by exact_mod_cast (hpair i j hr.1).1)
    · rw [if_neg hr, if_neg hr]; simp
  have hlin : ∑ r ∈ range (n - 1), ((imulLo (gradLoQ n a u b r) (gradLoQ n a U b r) (lo r - q r) (hi r - q r) : ℚ) : ℝ)
      ≤ ∑ r, gradK w1 n (fun i j => (a i j : ℝ)) (fun r => (b r : ℝ)) qR r * (g r - qR r) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => ((imulLo (gradLoQ n a u b r) (gradLoQ n a U b r) (lo r - q r) (hi r - q r) : ℚ) : ℝ))]
    refine Finset.sum_le_sum fun r _ => imulLo_le (hgrad r) ?_
    push_cast
    simp only [hqR]
    constructor <;> linarith [(hg r).1, (hg r).2]
  linarith

end AMW.Min

end
