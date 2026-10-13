import AMW.PCellZ

/-! ###### polytope cells: the minorant leaf with the zero-order tangent extension (bridge-port)

`mcheckGZ` is `mcheckG` with each term's side conditions `mokTZ` (the tangent check `tcheckPZ`: the derivative read,
else `zn` pyramid pieces; TZ.md §2) in place of `mokT`. `mcheckGZ_sound` is `mcheckG_sound`'s proof with
`mtermTZ` (from `mterm_okZ`) in place of `mtermT`. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- a term's side conditions with the zero-order extension -/
def mokTZ (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (zn L U k m p r : ℕ) :
    Bool :=
  Nat.ble m 1024 && mokZ R top bk tD bD f zn L U (mw1 k m) (mw2 k m) p r

/-- one anchored minorant term in the short forms, with the zero-order extension -/
theorem mtermTZ {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {zn : ℕ} (hzn : 0 < zn)
    {L0 L U k m p r : ℕ} (hL0 : L0 ≤ L) (hok : mokTZ R top bk tD bD f zn L U k m p r = true)
    {s : ℝ} (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokTZ at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okZ hlb hD hpt hR hzn L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1 hok.2 s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

/-- (3) the minorant leaf's check with the zero-order extension (`zn` pieces): box, every term's side conditions on its effective range, the main inequality -/
def mcheckGZ (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (zn Q : ℕ) (bs : List ℕ)
    (TS : List Term) (cN : ℕ) (c : Cl) (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Nat.ble
      (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (isum (fun n => Nat.mul (tA TS n)
        (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) TS.length) Cp)
        (isum (fun r => Nat.mul (Nat.sub (c.U.getD r 0) (c.L.getD r 0)) (Ng f bs TS FS P S r)) Q))))
      (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (bs.getD r 0) (c.L.getD r 0)) Q))
        (Nat.mul 32768 (isum (fun n => Nat.mul (tA TS n) (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n))
          (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) TS.length)))
        (Nat.mul 10 (Nat.add (isum (fun n => Nat.mul (tA TS n) (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)))
          TS.length) Cm))))
    (Bool.rec (motive := fun _ => Bool) false
      (iall (fun n => mokTZ R top bk tD bD f zn (eL TS c n) (eU TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)) TS.length)
      (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) Q))


/-- (3) the minorant leaf with the zero-order extension is sound, for every Q and term list -/
theorem mcheckGZ_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {zn : ℕ} (hzn : 0 < zn)
    {Q : ℕ} {PR : List (ℕ × ℕ)} {bs : List ℕ} {TS : List Term} {cN : ℕ} (hPR : PRok Q PR) (hTS : TSok Q PR TS)
    {c : Cl} {FS : List Term} {P S : List ℕ} {Cp Cm : ℕ} (hY : MulOKg Q PR c P S Cp Cm)
    (h : mcheckGZ top bk tD bD f R zn Q bs TS cN c FS P S Cp Cm = true) : CovBy Q PR (Pg cN Q bs TS) c := by
  intro g hg
  left
  unfold mcheckGZ at h
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
    exact mtermTZ hlb hD hpt hR hzn h0 (hterm' n hn) h1 h2
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


end AMW.Cert.PCell

end
