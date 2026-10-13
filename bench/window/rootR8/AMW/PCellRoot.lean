import AMW.PCellLeaf
import AMW.CWindow

/-! ###### polytope cells: the per-gap root cover, once for any Q and term list (bridge-port)

Each gap `r` is covered on `[0, ∞)` by: the window `g_r ≤ 1/2` (`w ≥ 1/4` pays `cN` through the adjacent term), a
one-dimensional cover of `[1/2, Smax_r)` whose clear segments pay `cN` through the adjacent term's integer cell bound, and
`g_r ≥ Smax_r` where the linear part pays alone.  A point no gap pays for lies in a product of bad segments: a root box,
whose polytope cell (pair bounds absent) the walks cover.  (After `of_check` of the AM box certificates.) ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- per-gap one-dimensional cover: segments `(a, b, clear)` from `pos` to at least `S`; a clear segment's integer cell
bound pays `cN` through the adjacent term alone: `aAdj · WZ ≥ cN · SW` -/
def coverChk (cN aAdj : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b) && decide (b < KB)
        && (!cl || Nat.ble (cN * SW) (aAdj * CellN.WZ ⟨a * KB + b, 0⟩))
        && coverChk cN aAdj b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

theorem coverChk_sound (cN aAdj : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverChk cN aAdj pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) ≤ (aAdj : ℝ) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC ∧ s.2.1 < KB := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverChk, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverChk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb, hbK⟩
      · left
        rw [Nat.ble_eq] at hcl
        have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
          simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
        have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
          simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
        have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        have hm2 : (aAdj : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdj : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdj : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdj : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2, h3⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2, h3⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

/-- the root cell of a choice `idx r` of bad segment per gap, every pair bound absent -/
def rootCl (Q NC W : ℕ) (cov : List (List (ℕ × ℕ × Bool))) (idx : ℕ → ℕ) : Cl :=
  ⟨(List.range Q).map fun r => ((badOf (cov.getD r [])).getD (idx r) (0, 0)).1,
   (List.range Q).map fun r => ((badOf (cov.getD r [])).getD (idx r) (0, 0)).2,
   List.replicate NC 0, List.replicate NC W⟩

theorem getD_map_range (f : ℕ → ℕ) {Q r : ℕ} (hr : r < Q) : ((List.range Q).map f).getD r 0 = f r := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]

theorem Fg_ge_lin {Q : ℕ} {bs : List ℕ} {TS : List Term} {g : ℕ → ℝ} (hg : ∀ r < Q, 0 ≤ g r) {r : ℕ} (hr : r < Q) :
    ((bs.getD r 0 : ℕ) : ℝ) * g r ≤ Fg Q bs TS g := by
  unfold Fg
  have h1 := Finset.single_le_sum (f := fun r => ((bs.getD r 0 : ℕ) : ℝ) * g r)
    (fun r hr => mul_nonneg (Nat.cast_nonneg _) (hg r (Finset.mem_range.mp hr))) (Finset.mem_range.mpr hr)
  have h2 := Finset.sum_nonneg fun n (_ : n ∈ Finset.range TS.length) =>
    mul_nonneg (Nat.cast_nonneg (tA TS n)) (wfun_nonneg (gsum g (tI TS n) (tJ TS n)))
  linarith

theorem Fg_ge_term {Q : ℕ} {bs : List ℕ} {TS : List Term} {g : ℕ → ℝ} (hg : ∀ r < Q, 0 ≤ g r) {n : ℕ}
    (hn : n < TS.length) : ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)) ≤ Fg Q bs TS g := by
  unfold Fg
  have h1 := Finset.single_le_sum (f := fun n => ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)))
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _)) (Finset.mem_range.mpr hn)
  have h2 := Finset.sum_nonneg fun r (hr : r ∈ Finset.range Q) =>
    mul_nonneg (Nat.cast_nonneg (bs.getD r 0)) (hg r (Finset.mem_range.mp hr))
  linarith

/-- (root) every point with nonnegative gaps satisfies the certificate, once the walks cover every root cell -/
theorem root_cover {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {cN : ℕ} {bs : List ℕ} {TS : List Term}
    (adj : ℕ → ℕ) (hadj : ∀ r < Q, adj r < TS.length ∧ tI TS (adj r) = r ∧ tJ TS (adj r) = r + 1)
    (Smax : ℕ → ℕ) (hS : ∀ r < Q, cN * SC ≤ bs.getD r 0 * Smax r)
    (cov : List (List (ℕ × ℕ × Bool)))
    (hcov : ∀ r < Q, coverChk cN (tA TS (adj r)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < Q, cN * 4 ≤ tA TS (adj r)) (W : ℕ) (hW : Q * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < Q, idx r < (badOf (cov.getD r [])).length) →
      CovBy Q PR (Pg cN Q bs TS) (rootCl Q PR.length W cov idx))
    (g : ℕ → ℝ) (hg : ∀ r < Q, 0 ≤ g r) : Pg cN Q bs TS g := by
  classical
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  -- a gap that pays `cN` alone settles the point
  by_cases hgood : ∃ r < Q, (cN : ℝ) ≤ Fg Q bs TS g
  · obtain ⟨r, -, h⟩ := hgood; exact Or.inl h
  push_neg at hgood
  have hbad : ∀ r < Q, ∃ i, i < (badOf (cov.getD r [])).length ∧
      (((badOf (cov.getD r [])).getD i (0, 0)).1 : ℝ) / SC ≤ g r ∧ g r ≤ (((badOf (cov.getD r [])).getD i (0, 0)).2 : ℝ) / SC ∧
      ((badOf (cov.getD r [])).getD i (0, 0)).2 < KB := by
    intro r hr
    obtain ⟨hn, hi, hj⟩ := hadj r hr
    have hsr : gsum g (tI TS (adj r)) (tJ TS (adj r)) = g r := by rw [hi, hj, gsum]; simp
    have hterm := Fg_ge_term (bs := bs) hg hn
    rw [hsr] at hterm
    -- beyond the cutoff the linear part pays
    by_cases hcut : (Smax r : ℝ) / SC ≤ g r
    · exfalso
      have hq := (Nat.cast_le (α := ℝ)).mpr (hS r hr); push_cast at hq
      have h1 : (cN : ℝ) ≤ (bs.getD r 0 : ℝ) * g r := by
        have : (cN : ℝ) ≤ (bs.getD r 0 : ℝ) * ((Smax r : ℝ) / SC) := by
          rw [mul_div_assoc', le_div_iff₀ hSC]; linarith
        exact this.trans (mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _))
      exact absurd (h1.trans (Fg_ge_lin hg hr)) (not_le.mpr (hgood r hr))
    push_neg at hcut
    -- the window: `w ≥ 1/4` on `[0, 1/2]`
    rcases le_total (g r) (((SC / 2 : ℕ) : ℝ) / SC) with hw | hw
    · exfalso
      have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1 / 2 := by norm_num [SC]
      have h19 := wfun_window (g r) (hg r hr) (by rw [hhalf] at hw; exact hw)
      have hq := (Nat.cast_le (α := ℝ)).mpr (hwin r hr); push_cast at hq
      have h1 : (cN : ℝ) ≤ (tA TS (adj r) : ℝ) * wfun (g r) := by
        nlinarith [mul_le_mul_of_nonneg_left h19 (Nat.cast_nonneg (tA TS (adj r)) : (0:ℝ) ≤ (tA TS (adj r) : ℝ))]
      exact absurd (h1.trans hterm) (not_le.mpr (hgood r hr))
    rcases coverChk_sound cN (tA TS (adj r)) (cov.getD r []) (SC / 2) (Smax r) (hcov r hr) (g r) hw hcut with
      hclear | ⟨s, hs, he, h1, h2, h3⟩
    · exact absurd (hclear.trans hterm) (not_le.mpr (hgood r hr))
    obtain ⟨i, hi', hsi⟩ := List.mem_iff_getElem.mp (badOf_mem hs he)
    refine ⟨i, hi', ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h1
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h2
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h3
  choose! idx hidx using hbad
  apply hrun idx (fun r hr => (hidx r hr).1) g
  refine incell_root hPR (W := W) (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk])
    (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk]) ?_ (fun r hr => ?_)
  · have h1 : ((sumR (rootCl Q PR.length W cov idx).U 0 Q : ℕ) : ℝ) ≤ ((Q * KB : ℕ) : ℝ) := by
      rw [sumR_eq, Nat.zero_add]; push_cast
      calc ∑ r ∈ Finset.Ico 0 Q, (((rootCl Q PR.length W cov idx).U.getD r 0 : ℕ) : ℝ)
          ≤ ∑ r ∈ Finset.Ico 0 Q, (KB : ℝ) := by
            apply Finset.sum_le_sum; intro r hr
            have hr' : r < Q := (Finset.mem_Ico.mp hr).2
            simp only [rootCl]; rw [getD_map_range _ hr']
            exact_mod_cast (hidx r hr').2.2.2.le
        _ = (Q : ℝ) * KB := by simp
    exact (by exact_mod_cast h1 : sumR _ 0 Q ≤ Q * KB).trans hW
  · simp only [rootCl]; rw [getD_map_range _ hr, getD_map_range _ hr]
    exact ⟨(hidx r hr).2.1, (hidx r hr).2.2.1⟩

end AMW.Cert.PCell

end
