import AMW.PCellGen

/-! ###### polytope cells: the minorant leaf, proved once for any term list (bridge-port)

The certificate functional is `Fg = Σ_r b_r g_r + Σ_n a_n w(g_{i_n} + … + g_{j_n − 1})` (units `1/SA`), its terms a list
`TS` of `(i, j, a, k)` (`k` the pair index of `[i, j)` when `j − i ≥ 2`).  `mcheckG` is the minorant leaf's check in
generic form, written with `isum`/`iall` (`Nat.rec` on the length, left-nested) so that an instance's unrolled check is
definitionally equal to it on literal lists; `mcheckG_sound` is mvt-engine's `mscheck_sound` argument (per-term anchored
minorants, per-gap slope bounds, the multiplier invariant) once, for every Q and term list. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- a term `(i, j, a, k)`, or a leaf's fields `(κ, λ, p, r)` -/
abbrev Term := ℕ × ℕ × ℕ × ℕ
def tI (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).1
def tJ (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.1
def tA (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.1
def tK (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.2

/-- `Σ_{i < n} f i`, and `∧_{i < n} f i`, left-nested (the kernel's unrolled shapes) -/
def isum (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (f i)) n
def iall (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => Bool.rec (motive := fun _ => Bool) false (f i) acc) n

theorem isum_cast (f : ℕ → ℕ) : ∀ n, ((isum f n : ℕ) : ℝ) = ∑ i ∈ Finset.range n, ((f i : ℕ) : ℝ)
  | 0 => by simp [isum]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← isum_cast f n]
    show ((Nat.add (isum f n) (f n) : ℕ) : ℝ) = _
    simp only [Nat.add_eq]; push_cast; ring

theorem iall_true {f : ℕ → Bool} : ∀ {n}, iall f n = true → ∀ i < n, f i = true
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    have h' : Bool.rec (motive := fun _ => Bool) false (f n) (iall f n) = true := h
    cases hc : iall f n
    · rw [hc] at h'; exact absurd h' Bool.false_ne_true
    · rw [hc] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact iall_true hc i hi
      · subst hi; exact h'

theorem brec_and {x y : Bool} (h : Bool.rec (motive := fun _ => Bool) false x y = true) : y = true ∧ x = true := by
  cases y <;> simp_all

theorem brec0_cast (X : ℕ) (b : Bool) :
    ((Bool.rec (motive := fun _ => ℕ) 0 X b : ℕ) : ℝ) = if b = true then (X : ℝ) else 0 := by cases b <;> simp

theorem inr_true (r i j : ℕ) : inr r i j = true ↔ i ≤ r ∧ r < j := by
  unfold inr
  by_cases h1 : i ≤ r
  · rw [Nat.ble_eq_true_of_le h1]; simp [Nat.blt_eq, h1]
  · rw [show Nat.ble i r = false from Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)]; simp [h1]

/-- a term's effective range and box corner -/
def eL (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nmax (c.A.getD (tK TS n) 0) (sumR c.L (tI TS n) (tJ TS n - tI TS n)))
    (c.L.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
def eU (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nmin (c.B.getD (tK TS n) 0) (sumR c.U (tI TS n) (tJ TS n - tI TS n)))
    (c.U.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
def eL0 (TS : List Term) (c : Cl) (n : ℕ) : ℕ := sumR c.L (tI TS n) (tJ TS n - tI TS n)

/-- gap `r`'s slope charge `N_r` -/
def Ng (f : ℕ → ℕ) (bs : List ℕ) (TS FS : List Term) (P S : List ℕ) (r : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.mul 2000000000 (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
      (Nat.mul (tA TS n) (mwT (tI FS n) (tJ FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (P.getD r 0))
    (Nat.add (Nat.add (Nat.mul 1024000000000 (bs.getD r 0)) (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
      (Nat.mul (tA TS n) (mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (S.getD r 0))

/-- (3) the minorant leaf's check: box, every term's side conditions on its effective range, the main inequality -/
def mcheckG (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (Q : ℕ) (bs : List ℕ)
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
      (iall (fun n => mokT R tD bD f (eL TS c n) (eU TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)) TS.length)
      (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) Q))

/-- the certificate functional (units `1/SA`) and the statement on a cell point -/
def Fg (Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * g r
    + ∑ n ∈ Finset.range TS.length, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
def Pg (cN Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : Prop := (cN : ℝ) ≤ Fg Q bs TS g ∨ g (Q - 1) < g 0

/-- every term is a pair inside the `Q` gaps; a non-adjacent one names its pair index -/
def TSok (Q : ℕ) (PR : List (ℕ × ℕ)) (TS : List Term) : Prop :=
  ∀ n < TS.length, tI TS n < tJ TS n ∧ tJ TS n ≤ Q ∧
    (tJ TS n - tI TS n = 1 ∨ (tK TS n < PR.length ∧ pI PR (tK TS n) = tI TS n ∧ pJ PR (tK TS n) = tJ TS n))

instance (Q : ℕ) (PR : List (ℕ × ℕ)) (TS : List Term) : Decidable (TSok Q PR TS) := by unfold TSok; infer_instance

/-- a term's sum lies in its effective range, whose start is at least the box corner -/
theorem term_range {Q : ℕ} {PR : List (ℕ × ℕ)} {TS : List Term} (hPR : PRok Q PR) (hTS : TSok Q PR TS) {c : Cl} {g : ℕ → ℝ}
    (hg : InCell Q PR c g) {n : ℕ} (hn : n < TS.length) :
    eL0 TS c n ≤ eL TS c n ∧ ((eL TS c n : ℕ) : ℝ) / SC ≤ gsum g (tI TS n) (tJ TS n) ∧
      gsum g (tI TS n) (tJ TS n) ≤ ((eU TS c n : ℕ) : ℝ) / SC := by
  obtain ⟨hij, hjQ, h1 | ⟨hk, hpi, hpj⟩⟩ := hTS n hn
  · have hb : Nat.beq (tJ TS n - tI TS n) 1 = true := by rw [h1]; rfl
    have hj : tJ TS n = tI TS n + 1 := by omega
    have hs : gsum g (tI TS n) (tJ TS n) = g (tI TS n) := by rw [hj, gsum]; simp
    unfold eL eU eL0
    rw [hb, h1, hs]
    exact ⟨le_rfl, (hg.1 _ (by omega)).1, (hg.1 _ (by omega)).2⟩
  · have h2 := (hPR _ hk).1
    rw [hpi, hpj] at h2
    have hb : Nat.beq (tJ TS n - tI TS n) 1 = false := Bool.eq_false_iff.mpr fun h => by
      have := Nat.eq_of_beq_eq_true h; omega
    have hn' : tI TS n + (tJ TS n - tI TS n) = tJ TS n := by omega
    have hsl := sum_lo hg.1 (tI TS n) (tJ TS n - tI TS n) (by omega)
    have hsu := sum_hi hg.1 (tI TS n) (tJ TS n - tI TS n) (by omega)
    rw [hn'] at hsl hsu
    have hA := (hg.2 _ hk).1
    have hB := (hg.2 _ hk).2
    rw [hpi, hpj] at hA hB
    unfold eL eU eL0
    rw [hb]
    exact ⟨le_nmax_right _ _, lo_nmax hA hsl, hi_nmin hB hsu⟩

/-- a term's slope span: `gsum − L0/SC` is the sum of the gaps' offsets `g_r − L_r/SC` over its gaps -/
theorem span_eq {Q : ℕ} {TS : List Term} {c : Cl} (g : ℕ → ℝ) {n : ℕ} (hij : tI TS n ≤ tJ TS n) (hjQ : tJ TS n ≤ Q) :
    gsum g (tI TS n) (tJ TS n) - ((eL0 TS c n : ℕ) : ℝ) / 32768 =
      ∑ r ∈ Finset.range Q, if tI TS n ≤ r ∧ r < tJ TS n then g r - ((c.L.getD r 0 : ℕ) : ℝ) / 32768 else 0 := by
  rw [← Finset.sum_filter]
  have hf : Finset.filter (fun r => tI TS n ≤ r ∧ r < tJ TS n) (Finset.range Q) = Finset.Ico (tI TS n) (tJ TS n) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_sub_distrib, ← Finset.sum_div, gsum, eL0, sumR_eq, show tI TS n + (tJ TS n - tI TS n) = tJ TS n by omega]

/-- (3) the minorant leaf is sound, for every Q and term list -/
theorem mcheckG_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    {Q : ℕ} {PR : List (ℕ × ℕ)} {bs : List ℕ} {TS : List Term} {cN : ℕ} (hPR : PRok Q PR) (hTS : TSok Q PR TS)
    {c : Cl} {FS : List Term} {P S : List ℕ} {Cp Cm : ℕ} (hY : MulOKg Q PR c P S Cp Cm)
    (h : mcheckG top bk tD bD f R Q bs TS cN c FS P S Cp Cm = true) : CovBy Q PR (Pg cN Q bs TS) c := by
  intro g hg
  left
  unfold mcheckG at h
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
    exact mtermT hlb hD hpt hR h0 (hterm' n hn) h1 h2
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
