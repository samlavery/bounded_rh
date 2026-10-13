import AMW.PCellCloseB
import AMW.PCDZ

/-! ###### polytope cells without the reflected half-space (mvt-engine, 2026-10-08)

The pair-cell certificates of PC8 cover only the half-space `g (Q−1) ≥ g 0` and finish by the functional's mirror
symmetry, so their cell predicate is `Pg = cN ≤ Fg ∨ g (Q−1) < g 0`. A truncated (prefix) window functional has no
mirror symmetry. Its certificate covers every point and proves `PgL = cN ≤ Fg` itself.

The two lemmas below are bridge-port's `mcheckGX_sound` (AMW.PCDZ) and `root_cover` (AMW.PCellRoot), copied with the
reflected disjunct removed. Their proofs are unchanged: each already proves `cN ≤ Fg` after choosing the left disjunct
(`left`, `Or.inl`). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the certificate's statement on a point, without the reflected half-space -/
def PgL (cN Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : Prop := (cN : ℝ) ≤ Fg Q bs TS g

/-- (bridge-port's `mcheckGX_sound`, conclusion `PgL`) -/
theorem mcheckGX_soundL {ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ}
    (hok : ∀ (L0 L U k m p r : ℕ), L0 ≤ L → ok L U k m p r = true → ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
      ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
        32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
          + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s)
    {Q : ℕ} {PR : List (ℕ × ℕ)} {bs : List ℕ} {TS : List Term} {cN : ℕ} (hPR : PRok Q PR) (hTS : TSok Q PR TS)
    {c : Cl} {FS : List Term} {P S : List ℕ} {Cp Cm : ℕ} (hY : MulOKg Q PR c P S Cp Cm)
    (h : mcheckGX ok top bk f Q bs TS cN c FS P S Cp Cm = true) : CovBy Q PR (PgL cN Q bs TS) c := by
  intro g hg
  show (cN : ℝ) ≤ Fg Q bs TS g
  unfold mcheckGX at h
  obtain ⟨hpre, hmain⟩ := brec_and h
  obtain ⟨hbox, hterm⟩ := brec_and hpre
  have hbox' := iall_true hbox
  have hterm' := iall_true hterm
  rw [Nat.ble_eq] at hmain
  set NT := TS.length with hNT
  -- the per-term anchored minorants
  have hT : ∀ n, n < NT → ∃ D : ℝ,
      (mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ) - 2000000000 * (mwT (tI FS n) (tJ FS n) : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n)) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
        + 327680000000000 * (D * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
        + 10 * (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
        - 10 * (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
        ≤ 327680000000000 * 1024 * wfun (gsum g (tI TS n) (tJ TS n)) := by
    intro n hn
    obtain ⟨h0, h1, h2⟩ := term_range hPR hTS hg hn
    exact hok _ _ _ _ _ _ _ h0 (hterm' n hn) _ h1 h2
  choose! D hD1 hD2 using hT
  -- shorthand
  set a : ℕ → ℝ := fun n => ((tA TS n : ℕ) : ℝ) with ha
  set e : ℕ → ℝ := fun r => g r - ((c.L.getD r 0 : ℕ) : ℝ) / 32768 with he
  set ind : ℕ → ℕ → Prop := fun n r => tI TS n ≤ r ∧ r < tJ TS n with hind
  set DD : ℕ → ℝ := fun r => ∑ n ∈ Finset.range NT, if tI TS n ≤ r ∧ r < tJ TS n then a n * D n else 0 with hDD
  have ha0 : ∀ n, 0 ≤ a n := fun n => Nat.cast_nonneg _
  -- (S1) the weighted term bounds
  have S1 : 32768 * ∑ n ∈ Finset.range NT, a n * (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n)) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
      + 327680000000000 * ∑ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
      + 10 * ∑ n ∈ Finset.range NT, a n * (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
      - 10 * ∑ n ∈ Finset.range NT, a n * (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
      ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range NT, a n * wfun (gsum g (tI TS n) (tJ TS n)) := by
    have := Finset.sum_le_sum fun n (hn : n ∈ Finset.range NT) =>
      mul_le_mul_of_nonneg_left (hD2 n (Finset.mem_range.mp hn)) (ha0 n)
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · apply Finset.sum_congr rfl; intro n _; ring
    · apply Finset.sum_congr rfl; intro n _; ring
  -- (S2) regrouping the slopes by gap
  have S2 : ∑ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
      = ∑ r ∈ Finset.range Q, e r * DD r := by
    have hx : ∀ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
        = ∑ r ∈ Finset.range Q, if tI TS n ≤ r ∧ r < tJ TS n then e r * (a n * D n) else 0 := by
      intro n hn
      obtain ⟨hij, hjQ, -⟩ := hTS n (Finset.mem_range.mp hn)
      rw [span_eq (Q := Q) g hij.le hjQ, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hx, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [hDD, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    split_ifs <;> ring
  -- (S3) per gap: the slope charge bounds the slope from below, then `gap_lo`
  have S3 : ∀ r ∈ Finset.range Q, -(10 * (((Ng f bs TS FS P S r : ℕ) : ℝ) * ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ)))
      ≤ 327680000000000 * ((1024 * ((bs.getD r 0 : ℕ) : ℝ) + DD r - (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) / 1000000000) * e r) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hlu : c.L.getD r 0 ≤ c.U.getD r 0 := Nat.le_of_ble_eq_true (hbox' r hr')
    have hgr := hg.1 r hr'
    have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
    rw [hSCe] at hgr
    refine gap_lo (natsub_nonneg _ _) ?_ (by simp only [he]; linarith [hgr.1]) ?_
    · -- `−N_r ≤ 10⁹ E_r`
      refine neg_natsub_le ?_
      simp only [Nat.add_eq, Nat.mul_eq]
      push_cast
      rw [isum_cast, isum_cast]
      simp only [brec0_cast, inr_true]
      have hsum : ∑ n ∈ Finset.range NT, (if tI TS n ≤ r ∧ r < tJ TS n then ((tA TS n * mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℕ) : ℝ) else 0)
          - 2000000000 * ∑ n ∈ Finset.range NT, (if tI TS n ≤ r ∧ r < tJ TS n then ((tA TS n * mwT (tI FS n) (tJ FS n) : ℕ) : ℝ) else 0)
          ≤ 1000000000 * DD r := by
        rw [hDD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum; intro n hn
        split_ifs
        · push_cast
          have := mul_le_mul_of_nonneg_left (hD1 n (Finset.mem_range.mp hn)) (ha0 n)
          simp only [ha] at this; nlinarith [this]
        · simp
      linarith
    · rw [Nat.cast_sub hlu, sub_div]; simp only [he]; linarith [hgr.2]
  -- (S4) the multipliers
  have S4 := hY g hg
  have S4' : ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
      = 32768 * ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * e r := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
  -- (S5) the main inequality, as reals
  have S5 := (Nat.cast_le (α := ℝ)).mpr hmain
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at S5
  push_cast at S5
  rw [isum_cast, isum_cast, isum_cast, isum_cast, isum_cast] at S5
  push_cast at S5
  -- the per-gap sums
  have S3s := Finset.sum_le_sum S3
  have e1 : ∑ r ∈ Finset.range Q, 327680000000000 * ((1024 * ((bs.getD r 0 : ℕ) : ℝ) + DD r
        - (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) / 1000000000) * e r)
      = 327680000000000 * 1024 * ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * e r
        + 327680000000000 * ∑ r ∈ Finset.range Q, e r * DD r
        - 327680 * ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * e r := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have e2 : ∑ r ∈ Finset.range Q, -(10 * (((Ng f bs TS FS P S r : ℕ) : ℝ) * ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ)))
      = -(10 * ∑ r ∈ Finset.range Q, ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ) * ((Ng f bs TS FS P S r : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _; ring
  have e3 : ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * g r
      = (∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * ((c.L.getD r 0 : ℕ) : ℝ)) / 32768
        + ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * e r := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
  rw [e1, e2] at S3s
  rw [S2] at S1
  rw [S4'] at S4
  unfold Fg
  rw [e3, ← hNT]
  simp only [ha] at S1
  linarith [S1, S3s, S4, S5]


/-- (bridge-port's `root_cover`, conclusion `PgL`) -/
theorem root_coverL {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {cN : ℕ} {bs : List ℕ} {TS : List Term}
    (adj : ℕ → ℕ) (hadj : ∀ r < Q, adj r < TS.length ∧ tI TS (adj r) = r ∧ tJ TS (adj r) = r + 1)
    (Smax : ℕ → ℕ) (hS : ∀ r < Q, cN * SC ≤ bs.getD r 0 * Smax r)
    (cov : List (List (ℕ × ℕ × Bool)))
    (hcov : ∀ r < Q, coverChk cN (tA TS (adj r)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < Q, cN * 4 ≤ tA TS (adj r)) (W : ℕ) (hW : Q * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < Q, idx r < (badOf (cov.getD r [])).length) →
      CovBy Q PR (PgL cN Q bs TS) (rootCl Q PR.length W cov idx))
    (g : ℕ → ℝ) (hg : ∀ r < Q, 0 ≤ g r) : PgL cN Q bs TS g := by
  classical
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  -- a gap that pays `cN` alone settles the point
  by_cases hgood : ∃ r < Q, (cN : ℝ) ≤ Fg Q bs TS g
  · obtain ⟨r, -, h⟩ := hgood; exact h
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
