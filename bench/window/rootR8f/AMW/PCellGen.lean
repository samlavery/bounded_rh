import AMW.PCellCore

/-! ###### polytope cells: the generic proof layer (bridge-port)

The propositions see a cell as four lists (`Cl`): gap bounds `L`, `U` (gap `r`) and pair bounds `A`, `B` (pair `k` of the
instance's pair list `PR`).  Every split, tightening pass and multiplier entry is proved here once, for any gap, pair
and `Q`; an instance links its unrolled kernel functions to these by definitional unfolding (`List.set`, `imap`,
`sumR` and `List.getD` reduce on literal lists). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

structure Cl where
  (L U A B : List ℕ)

/-- the pair sum `g_i + … + g_{j−1}` -/
def gsum (g : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ r ∈ Finset.Ico i j, g r

/-- the gaps `[pI, pJ)` of pair `k` -/
def pI (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).1
def pJ (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).2

def InCell (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (g : ℕ → ℝ) : Prop :=
  (∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC) ∧
  ∀ k < PR.length, ((c.A.getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
    gsum g (pI PR k) (pJ PR k) ≤ ((c.B.getD k 0 : ℕ) : ℝ) / SC

/-- every point of the cell satisfies `P` -/
def CovBy (Q : ℕ) (PR : List (ℕ × ℕ)) (P : (ℕ → ℝ) → Prop) (c : Cl) : Prop := ∀ g, InCell Q PR c g → P g

/-- every pair is non-adjacent and inside the `Q` gaps -/
def PRok (Q : ℕ) (PR : List (ℕ × ℕ)) : Prop := ∀ k < PR.length, pI PR k + 2 ≤ pJ PR k ∧ pJ PR k ≤ Q

instance (Q : ℕ) (PR : List (ℕ × ℕ)) : Decidable (PRok Q PR) := by unfold PRok; infer_instance

theorem getD_set (L : List ℕ) (r q k : ℕ) (hr : r < L.length) :
    (L.set r q).getD k 0 = if k = r then q else L.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : r = k
  · subst h; simp [hr]
  · simp [h, Ne.symm h]

/-! ### (2) splits -/

theorem cov_gsplit {Q : ℕ} {PR : List (ℕ × ℕ)} {P : (ℕ → ℝ) → Prop} {c : Cl} (r q : ℕ) {n : ℕ}
    (hL' : c.L.length = n) (hU' : c.U.length = n) (hr : r < n)
    (hA : CovBy Q PR P ⟨c.L, c.U.set r q, c.A, c.B⟩) (hB : CovBy Q PR P ⟨c.L.set r q, c.U, c.A, c.B⟩) :
    CovBy Q PR P c := by
  have hL : r < c.L.length := hL' ▸ hr
  have hU : r < c.U.length := hU' ▸ hr
  intro g hg
  rcases le_total (g r) ((q : ℝ) / SC) with h | h
  · refine hA g ⟨fun r' hr' => ?_, hg.2⟩
    show ((c.L.getD r' 0 : ℕ) : ℝ) / SC ≤ g r' ∧ g r' ≤ (((c.U.set r q).getD r' 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ hU]
    split_ifs with e
    · subst e; exact ⟨(hg.1 _ hr').1, h⟩
    · exact hg.1 r' hr'
  · refine hB g ⟨fun r' hr' => ?_, hg.2⟩
    show (((c.L.set r q).getD r' 0 : ℕ) : ℝ) / SC ≤ g r' ∧ g r' ≤ ((c.U.getD r' 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ hL]
    split_ifs with e
    · subst e; exact ⟨h, (hg.1 _ hr').2⟩
    · exact hg.1 r' hr'

theorem cov_ssplit {Q : ℕ} {PR : List (ℕ × ℕ)} {P : (ℕ → ℝ) → Prop} {c : Cl} (k q : ℕ) {n : ℕ}
    (hA'' : c.A.length = n) (hB'' : c.B.length = n) (hk : k < n)
    (hA : CovBy Q PR P ⟨c.L, c.U, c.A, c.B.set k q⟩) (hB : CovBy Q PR P ⟨c.L, c.U, c.A.set k q, c.B⟩) :
    CovBy Q PR P c := by
  have hA' : k < c.A.length := hA'' ▸ hk
  have hB' : k < c.B.length := hB'' ▸ hk
  intro g hg
  rcases le_total (gsum g (pI PR k) (pJ PR k)) ((q : ℝ) / SC) with h | h
  · refine hA g ⟨hg.1, fun k' hk' => ?_⟩
    show ((c.A.getD k' 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k') (pJ PR k') ∧
      gsum g (pI PR k') (pJ PR k') ≤ (((c.B.set k q).getD k' 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ hB']
    split_ifs with e
    · subst e; exact ⟨(hg.2 _ hk').1, h⟩
    · exact hg.2 k' hk'
  · refine hB g ⟨hg.1, fun k' hk' => ?_⟩
    show (((c.A.set k q).getD k' 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k') (pJ PR k') ∧
      gsum g (pI PR k') (pJ PR k') ≤ ((c.B.getD k' 0 : ℕ) : ℝ) / SC
    rw [getD_set _ _ _ _ hA']
    split_ifs with e
    · subst e; exact ⟨h, (hg.2 _ hk').2⟩
    · exact hg.2 k' hk'

/-! ### sums and indexed maps, in the kernel's shapes -/

/-- `n` consecutive entries from `i`, left-nested as the kernel writes them -/
def sumR (L : List ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => L.getD i 0
  | n + 2 => Nat.add (sumR L i (n + 1)) (L.getD (i + n + 1) 0)

theorem sumR_eq (L : List ℕ) (i : ℕ) : ∀ n, ((sumR L i n : ℕ) : ℝ) = ∑ r ∈ Finset.Ico i (i + n), ((L.getD r 0 : ℕ) : ℝ)
  | 0 => by simp [sumR]
  | 1 => by simp [sumR]
  | n + 2 => by
    have ih := sumR_eq L i (n + 1)
    rw [show i + (n + 2) = (i + (n + 1)) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ← ih]
    simp only [sumR, Nat.add_eq]; push_cast; rw [Nat.add_assoc i n 1]

/-- an indexed map: `f r x` at position `r` (from `s`) -/
def imap (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, x :: xs => f s x :: imap f (s + 1) xs

theorem imap_length (f : ℕ → ℕ → ℕ) : ∀ (s : ℕ) (L : List ℕ), (imap f s L).length = L.length
  | _, [] => rfl
  | s, _ :: xs => by simp [imap, imap_length f (s + 1) xs]

theorem imap_getD (f : ℕ → ℕ → ℕ) : ∀ (s : ℕ) (L : List ℕ) (r : ℕ), r < L.length →
    (imap f s L).getD r 0 = f (s + r) (L.getD r 0)
  | _, [], r, h => absurd h (Nat.not_lt_zero _)
  | s, x :: xs, 0, _ => by simp [imap]
  | s, x :: xs, r + 1, h => by
    simp only [imap, List.getD_cons_succ]
    rw [imap_getD f (s + 1) xs r (by simpa using h)]
    congr 1; omega

/-- the box part of a cell (a gap sum on it lies between the sums of its bounds: `sum_lo`, `sum_hi`) -/
def InBox (Q : ℕ) (c : Cl) (g : ℕ → ℝ) : Prop :=
  ∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC

theorem sum_lo {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
    ((sumR c.L i n : ℕ) : ℝ) / SC ≤ gsum g i (i + n) := by
  rw [sumR_eq, gsum, Finset.sum_div]
  exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).1

theorem sum_hi {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
    gsum g i (i + n) ≤ ((sumR c.U i n : ℕ) : ℝ) / SC := by
  rw [sumR_eq, gsum, Finset.sum_div]
  exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).2

/-! ### (5) one tightening pass of pair `k`, in the kernel's form -/

def fLe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmax (c.A.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k))
def fUe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmin (c.B.getD k 0) (sumR c.U (pI PR k) (pJ PR k - pI PR k))
/-- the effective range of pair `k` is empty -/
def femp (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : Bool := Nat.blt (fUe PR c k) (fLe PR c k)

/-- the tightened cell (Jacobi: every new gap bound from the old ones) -/
def fbC (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : Cl :=
  ⟨imap (fun r x => if pI PR k ≤ r ∧ r < pJ PR k then
      nmax x (Nat.sub (fLe PR c k) (Nat.sub (sumR c.U (pI PR k) (pJ PR k - pI PR k)) (c.U.getD r 0))) else x) 0 c.L,
   imap (fun r x => if pI PR k ≤ r ∧ r < pJ PR k then
      nmin x (Nat.sub (fUe PR c k) (Nat.sub (sumR c.L (pI PR k) (pJ PR k - pI PR k)) (c.L.getD r 0))) else x) 0 c.U,
   c.A, c.B⟩

theorem single_le (f : ℕ → ℝ) {i j r : ℕ} (hf : ∀ t ∈ Finset.Ico i j, 0 ≤ f t) (hr : r ∈ Finset.Ico i j) :
    f r ≤ ∑ t ∈ Finset.Ico i j, f t := Finset.single_le_sum hf hr

/-- (4, 5) on a cell point, pair `k`'s range is nonempty and the tightened bounds hold -/
theorem fb_gen {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} (hL : c.L.length = Q) (hU : c.U.length = Q)
    {k : ℕ} (hk : k < PR.length) {g : ℕ → ℝ} (hg : InCell Q PR c g) :
    femp PR c k = false ∧ InCell Q PR (fbC PR c k) g := by
  obtain ⟨hij, hjQ⟩ := hPR k hk
  set i := pI PR k with hi
  set j := pJ PR k with hj
  have hn : i + (j - i) = j := by omega
  have hsl := sum_lo hg.1 i (j - i) (by omega)
  have hsu := sum_hi hg.1 i (j - i) (by omega)
  rw [hn] at hsl hsu
  have hlo : ((fLe PR c k : ℕ) : ℝ) / SC ≤ gsum g i j := lo_nmax (hg.2 k hk).1 hsl
  have hhi : gsum g i j ≤ ((fUe PR c k : ℕ) : ℝ) / SC := hi_nmin (hg.2 k hk).2 hsu
  have hSC := SC_pos
  refine ⟨?_, fun r hr => ?_, hg.2⟩
  · have : ((fLe PR c k : ℕ) : ℝ) / SC ≤ ((fUe PR c k : ℕ) : ℝ) / SC := hlo.trans hhi
    have h2 : fLe PR c k ≤ fUe PR c k := by
      have := (div_le_div_iff_of_pos_right hSC).mp this; exact_mod_cast this
    unfold femp; exact Bool.eq_false_iff.mpr fun h => absurd (Nat.blt_eq.mp h) (Nat.not_lt.mpr h2)
  show (((fbC PR c k).L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ (((fbC PR c k).U.getD r 0 : ℕ) : ℝ) / SC
  simp only [fbC, ← hi, ← hj]
  rw [imap_getD _ _ _ _ (by omega), imap_getD _ _ _ _ (by omega), Nat.zero_add]
  split_ifs with hin
  · obtain ⟨h1, h2⟩ := hin
    have hmem : r ∈ Finset.Ico i j := Finset.mem_Ico.mpr ⟨h1, h2⟩
    have hgr := hg.1 r hr
    -- the other gaps of the pair: `gsum g i j − g r`
    have hsplit : gsum g i j = g r + (gsum g i j - g r) := by ring
    have hUr : c.U.getD r 0 ≤ sumR c.U i (j - i) := by
      have h := single_le (fun t => ((c.U.getD t 0 : ℕ) : ℝ)) (fun t _ => Nat.cast_nonneg _) (j := j) (i := i) hmem
      rw [← hn, ← sumR_eq] at h; exact_mod_cast h
    have hLr : c.L.getD r 0 ≤ sumR c.L i (j - i) := by
      have h := single_le (fun t => ((c.L.getD t 0 : ℕ) : ℝ)) (fun t _ => Nat.cast_nonneg _) (j := j) (i := i) hmem
      rw [← hn, ← sumR_eq] at h; exact_mod_cast h
    -- the others lie within the sums of their bounds less gap r's
    have hoU : gsum g i j - g r ≤ ((Nat.sub (sumR c.U i (j - i)) (c.U.getD r 0) : ℕ) : ℝ) / SC := by
      rw [Nat.sub_eq, Nat.cast_sub hUr, sub_div]
      have h := single_le (fun t => ((c.U.getD t 0 : ℕ) : ℝ) / SC - g t)
        (fun t ht => sub_nonneg.mpr (hg.1 t (by simp at ht; omega)).2) hmem
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hn, ← sumR_eq, hn] at h
      simp only [gsum] at *; linarith
    have hoL : ((Nat.sub (sumR c.L i (j - i)) (c.L.getD r 0) : ℕ) : ℝ) / SC ≤ gsum g i j - g r := by
      rw [Nat.sub_eq, Nat.cast_sub hLr, sub_div]
      have h := single_le (fun t => g t - ((c.L.getD t 0 : ℕ) : ℝ) / SC)
        (fun t ht => sub_nonneg.mpr (hg.1 t (by simp at ht; omega)).1) hmem
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hn, ← sumR_eq, hn] at h
      simp only [gsum] at *; linarith
    refine ⟨fb_lo (o := gsum g i j - g r) (ou := Nat.sub (sumR c.U i (j - i)) (c.U.getD r 0))
      (by rw [Nat.sub_eq]; omega) hgr.1 (by linarith) hoU,
      fb_hi (o := gsum g i j - g r) (ol := Nat.sub (sumR c.L i (j - i)) (c.L.getD r 0))
      (by rw [Nat.sub_eq]; omega) hgr.2 (by linarith) hoL⟩
  · exact hg.1 r hr

/-! ### (3) multipliers, in the kernel's form -/

/-- a kernel boolean as `0`/`1`; gap `r` lies in `[i, j)` -/
def ind (b : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 1 b
def inr (r i j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) false (Nat.blt r j) (Nat.ble i r)

theorem ind_inr (r i j : ℕ) : ((ind (inr r i j) : ℕ) : ℝ) = if i ≤ r ∧ r < j then 1 else 0 := by
  unfold ind inr
  by_cases h1 : i ≤ r
  · rw [Nat.ble_eq_true_of_le h1]
    by_cases h2 : r < j
    · rw [show Nat.blt r j = true from Nat.blt_eq.mpr h2]; simp [h1, h2]
    · rw [show Nat.blt r j = false from Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)]; simp [h2]
  · rw [show Nat.ble i r = false from Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)]; simp [h1]

/-- the accumulated multipliers are valid on the cell: `Σ y · slack = (Cp − Cm) + Σ_r (P_r − S_r)(SC g_r − L_r) ≥ 0` -/
def MulOKg (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (P S : List ℕ) (Cp Cm : ℕ) : Prop :=
  ∀ g, InCell Q PR c g → 0 ≤ ((Cp : ℝ) - Cm) +
    ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))

/-- one entry: `Ylo` on pair `k`'s lower bound, `Yhi` on its upper bound (the kernel sets one of them to `0`) -/
theorem mul_step {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} {P S : List ℕ} {Cp Cm : ℕ}
    (hP : P.length = Q) (hS : S.length = Q) (h : MulOKg Q PR c P S Cp Cm) {k : ℕ} (hk : k < PR.length) (Ylo Yhi : ℕ) :
    MulOKg Q PR c (imap (fun r x => Nat.add x (Nat.mul Ylo (ind (inr r (pI PR k) (pJ PR k))))) 0 P)
      (imap (fun r x => Nat.add x (Nat.mul Yhi (ind (inr r (pI PR k) (pJ PR k))))) 0 S)
      (Nat.add (Nat.add Cp (Nat.mul Ylo (Nat.sub (sumR c.L (pI PR k) (pJ PR k - pI PR k)) (c.A.getD k 0))))
        (Nat.mul Yhi (Nat.sub (c.B.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k)))))
      (Nat.add (Nat.add Cm (Nat.mul Ylo (Nat.sub (c.A.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k)))))
        (Nat.mul Yhi (Nat.sub (sumR c.L (pI PR k) (pJ PR k - pI PR k)) (c.B.getD k 0)))) := by
  intro g hg
  have h0 := h g hg
  obtain ⟨hij, hjQ⟩ := hPR k hk
  set i := pI PR k with hi
  set j := pJ PR k with hj
  have hn : i + (j - i) = j := by omega
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  -- the multiplier sum over the pair's gaps
  have hsum : ∑ r ∈ Finset.range Q, ((ind (inr r i j) : ℕ) : ℝ) * (32768 * g r - (c.L.getD r 0 : ℕ))
      = 32768 * gsum g i j - (sumR c.L i (j - i) : ℕ) := by
    simp only [ind_inr, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, sumR_eq, hn, gsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr
    · ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    · intro _ _; rfl
  have hA := (hg.2 k hk).1
  have hB := (hg.2 k hk).2
  rw [hSCe] at hA hB
  have hlo : (0 : ℝ) ≤ Ylo * (32768 * gsum g i j - (c.A.getD k 0 : ℕ)) :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [div_le_iff₀ (by norm_num)] at hA; linarith)
  have hhi : (0 : ℝ) ≤ Yhi * ((c.B.getD k 0 : ℕ) - 32768 * gsum g i j) :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [le_div_iff₀ (by norm_num)] at hB; linarith)
  have hd1 := natsub_diff (sumR c.L i (j - i)) (c.A.getD k 0)
  have hd2 := natsub_diff (c.B.getD k 0) (sumR c.L i (j - i))
  have e : ∑ r ∈ Finset.range Q, ((((imap (fun r x => Nat.add x (Nat.mul Ylo (ind (inr r i j)))) 0 P).getD r 0 : ℕ) : ℝ)
        - (((imap (fun r x => Nat.add x (Nat.mul Yhi (ind (inr r i j)))) 0 S).getD r 0 : ℕ) : ℝ))
        * (32768 * g r - (c.L.getD r 0 : ℕ))
      = ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
        + (Ylo - Yhi) * ∑ r ∈ Finset.range Q, ((ind (inr r i j) : ℕ) : ℝ) * (32768 * g r - (c.L.getD r 0 : ℕ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [imap_getD _ _ _ _ (by rw [hP]; simpa using hr), imap_getD _ _ _ _ (by rw [hS]; simpa using hr)]
    simp only [Nat.zero_add, Nat.add_eq, Nat.mul_eq]
    push_cast; ring
  rw [e, hsum]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  have e2 : (Ylo : ℝ) * ((sumR c.L i (j - i) - c.A.getD k 0 : ℕ) : ℝ) - Ylo * ((c.A.getD k 0 - sumR c.L i (j - i) : ℕ) : ℝ)
      = Ylo * ((sumR c.L i (j - i) : ℕ) - (c.A.getD k 0 : ℕ)) := by rw [← mul_sub, hd1]
  have e3 : (Yhi : ℝ) * ((c.B.getD k 0 - sumR c.L i (j - i) : ℕ) : ℝ) - Yhi * ((sumR c.L i (j - i) - c.B.getD k 0 : ℕ) : ℝ)
      = Yhi * ((c.B.getD k 0 : ℕ) - (sumR c.L i (j - i) : ℕ)) := by rw [← mul_sub, hd2]
  nlinarith [e2, e3, hlo, hhi, h0]

/-- the kernel's split points: the midpoint of gap `r`'s range, of pair `k`'s effective range -/
def qG (c : Cl) (r : ℕ) : ℕ := Nat.shiftRight (Nat.add (c.L.getD r 0) (c.U.getD r 0)) 1
def qP (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := Nat.shiftRight (Nat.add (fLe PR c k) (fUe PR c k)) 1

theorem cov_gmid {Q : ℕ} {PR : List (ℕ × ℕ)} {P : (ℕ → ℝ) → Prop} {c : Cl} (r : ℕ) {n : ℕ}
    (hL' : c.L.length = n) (hU' : c.U.length = n) (hr : r < n)
    (hA : CovBy Q PR P ⟨c.L, c.U.set r (qG c r), c.A, c.B⟩) (hB : CovBy Q PR P ⟨c.L.set r (qG c r), c.U, c.A, c.B⟩) :
    CovBy Q PR P c := cov_gsplit r _ hL' hU' hr hA hB

theorem cov_smid {Q : ℕ} {PR : List (ℕ × ℕ)} {P : (ℕ → ℝ) → Prop} {c : Cl} (k : ℕ) {n : ℕ}
    (hA'' : c.A.length = n) (hB'' : c.B.length = n) (hk : k < n)
    (hA : CovBy Q PR P ⟨c.L, c.U, c.A, c.B.set k (qP PR c k)⟩) (hB : CovBy Q PR P ⟨c.L, c.U, c.A.set k (qP PR c k), c.B⟩) :
    CovBy Q PR P c := cov_ssplit k _ hA'' hB'' hk hA hB

theorem neg_natsub_le {X Y : ℕ} {e : ℝ} (h : (Y : ℝ) - X ≤ e) : -((X - Y : ℕ) : ℝ) ≤ e := by
  have := natsub_ge X Y; linarith

/-! ### (kind 8) the Farkas leaf: a multiplier form that is negative on the whole box -/

/-- the box maximum of the multiplier slopes: `Σ_{r < n} (U_r − L_r)(P_r − S_r)⁺` (left-nested, as the kernel adds) -/
def fsum (c : Cl) (P S : List ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (fsum c P S n) (Nat.mul (Nat.sub (c.U.getD n 0) (c.L.getD n 0)) (Nat.sub (P.getD n 0) (S.getD n 0)))

theorem fsum_ge {Q : ℕ} {c : Cl} (P S : List ℕ) {g : ℕ → ℝ} (hb : InBox Q c g) : ∀ n ≤ Q,
    ∑ r ∈ Finset.range n, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
      ≤ ((fsum c P S n : ℕ) : ℝ)
  | 0, _ => by simp [fsum]
  | n + 1, hn => by
    rw [Finset.sum_range_succ]
    have ih := fsum_ge P S hb n (by omega)
    simp only [fsum, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast
    have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
    obtain ⟨h1, h2⟩ := hb n (by omega)
    rw [hSCe, div_le_iff₀ (by norm_num)] at h1
    rw [hSCe, le_div_iff₀ (by norm_num)] at h2
    have hd1 := natsub_ge (c.U.getD n 0) (c.L.getD n 0)
    have hn1 := natsub_nonneg (c.U.getD n 0) (c.L.getD n 0)
    have hn2 := natsub_nonneg (P.getD n 0) (S.getD n 0)
    have hd2 := natsub_ge (P.getD n 0) (S.getD n 0)
    rcases le_total (S.getD n 0) (P.getD n 0) with h | h
    · rw [Nat.cast_sub h] at hd2 hn2 ⊢
      have e : ((P.getD n 0 : ℕ) : ℝ) - (S.getD n 0 : ℕ) ≥ 0 := hn2
      nlinarith [mul_le_mul_of_nonneg_left (show 32768 * g n - (c.L.getD n 0 : ℕ) ≤ ((c.U.getD n 0 - c.L.getD n 0 : ℕ) : ℝ) by linarith) e]
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, mul_zero, add_zero]
      have e : ((P.getD n 0 : ℕ) : ℝ) - (S.getD n 0 : ℕ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast h)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg e (show (0 : ℝ) ≤ 32768 * g n - (c.L.getD n 0 : ℕ) by linarith)]

/-- the Farkas leaf: valid multipliers whose box maximum is below `0` cover the cell vacuously -/
theorem farkas_cov {Q : ℕ} {PR : List (ℕ × ℕ)} {P' : (ℕ → ℝ) → Prop} {c : Cl} {P S : List ℕ} {Cp Cm : ℕ}
    (h : MulOKg Q PR c P S Cp Cm) (hf : Nat.blt (Nat.add Cp (fsum c P S Q)) Cm = true) : CovBy Q PR P' c := by
  intro g hg
  exfalso
  have h0 := h g hg
  have h1 := fsum_ge P S hg.1 Q le_rfl
  have h2 : ((Nat.add Cp (fsum c P S Q) : ℕ) : ℝ) < Cm := by exact_mod_cast Nat.blt_eq.mp hf
  simp only [Nat.add_eq] at h2; push_cast at h2
  linarith

/-! ### the root, list helpers, and the kernel's small helpers -/

/-- the root: a box with every pair bound absent (`A = 0`, `B = W ≥ Σ U`) -/
theorem incell_root {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} {W : ℕ}
    (hA : ∀ k < PR.length, c.A.getD k 0 = 0) (hB : ∀ k < PR.length, c.B.getD k 0 = W) (hW : sumR c.U 0 Q ≤ W)
    {g : ℕ → ℝ} (hb : InBox Q c g) : InCell Q PR c g := by
  refine ⟨hb, fun k hk => ⟨?_, ?_⟩⟩
  · rw [hA k hk, Nat.cast_zero, zero_div, gsum]
    exact Finset.sum_nonneg fun r hr =>
      le_trans (div_nonneg (Nat.cast_nonneg _) SC_pos.le) (hb r (by have := hPR k hk; simp at hr; omega)).1
  · obtain ⟨hij, hjQ⟩ := hPR k hk
    have h1 := sum_hi hb (pI PR k) (pJ PR k - pI PR k) (by omega)
    rw [show pI PR k + (pJ PR k - pI PR k) = pJ PR k by omega] at h1
    refine h1.trans (div_le_div_of_nonneg_right ?_ SC_pos.le)
    rw [hB k hk]
    have h2 : ((sumR c.U (pI PR k) (pJ PR k - pI PR k) : ℕ) : ℝ) ≤ ((sumR c.U 0 Q : ℕ) : ℝ) := by
      rw [sumR_eq, sumR_eq]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
      · intro _ _ _; exact Nat.cast_nonneg _
    exact h2.trans (by exact_mod_cast hW)

theorem list_of_getD (M : List ℕ) (n : ℕ) (h : M.length = n) : (List.range n).map (fun r => M.getD r 0) = M := by
  subst h
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem brec_dep {α : Sort _} {P : α → Prop} {a b : α} {c : Bool} (ha : c = false → P a) (hb : c = true → P b) :
    P (Bool.rec (motive := fun _ => α) a b c) := by cases c <;> simp_all

/-- evaluate a natural before continuing (any result type) -/
def forceT {α : Sort _} (a : ℕ) (k : ℕ → α) : α := Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) a
theorem forceT_eq {α : Sort _} (a : ℕ) (k : ℕ → α) : forceT a k = k a := by cases a <;> rfl

/-- the tightened gap bounds (the kernel's per-gap step) -/
def tl (l u Le su : ℕ) : ℕ := nmax l (Nat.sub Le (Nat.sub su u))
def tu (u l Ue sl : ℕ) : ℕ := nmin u (Nat.sub Ue (Nat.sub sl l))

/-- leaf field reads (term fields `[κ 2][j1 7][j2 7 if κ = 3][λ 10 if κ ≥ 2]`): kind, weight, position -/
def fk (w o : ℕ) : ℕ := Nat.land (Nat.shiftRight w o) 3
def fm (w o k : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o 16)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o 9)) 1023) (Nat.beq k 2)
def fj (w o d : ℕ) : ℕ := Nat.land (Nat.shiftRight w (Nat.add o d)) 127
/-- the payload length of a minorant term of kind `k` (2, 9, 19, 26 bits) -/
def plen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 26 (Nat.beq k 3)) 19 (Nat.beq k 2)) 9 (Nat.beq k 1)
/-- mvt-engine's grid point (JSH = 5): position code `33` is the range start (PLO); else `j = jj & 63` of 32 on the
fine grid `2^5` (bit 6 set) or the `2^8` grid, clamped to the grid points inside `[L, U]` -/
def gptF (L U jj : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) 8 5 (Nat.beq (Nat.land (Nat.shiftRight jj 6) 1) 1)) fun gs =>
     forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 gs) 1)) gs) gs) fun ga =>
     forceR (Nat.shiftLeft (Nat.shiftRight U gs) gs) fun gb =>
     forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) (Nat.land jj 63)) 5)) gs) gs) fun x =>
     Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga))
    L (Nat.beq jj 33)
/-- the constant read of a range: a degenerate `[L, L]` reads `[L, L + 1]` -/
def uc (L U : ℕ) : ℕ := nmax U (Nat.add L 1)
theorem le_uc (L U : ℕ) : U ≤ uc L U := le_nmax_left _ _

/-- decode one term's fields at offset `o` (grid points on `[L, U]`), then continue with them and the next offset -/
def dec4 (w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (fk w o) fun a => forceR (fm w o a) fun m => forceR (gptF L U (fj w o 2)) fun p =>
  forceR (gptF L U (fj w o 9)) fun r => forceR (Nat.add o (plen a)) fun o' => k a m p r o'
/-- one gap's tightened bounds, forced, then the continuation -/
def fb1 (l u Le su Ue sl : ℕ) (k : ℕ → ℕ → ℕ) : ℕ := forceR (tl l u Le su) fun l' => forceR (tu u l Ue sl) fun u' => k l' u'

/-- a term's side conditions, value, charges, slope and slope weight, from its kind and weight -/
def mokT (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : Bool :=
  Nat.ble m 1024 && mokP R tD bD f L U (mw1 k m) (mw2 k m) p r
def mvT (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ := mval top bk f L U (mwc k m) (mw1 k m) (mw2 k m) p r
def mcpT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcp f L0 (mw1 k m) (mw2 k m) p r
def mcnT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcn f L0 (mw1 k m) (mw2 k m) p r
def mslT (f : ℕ → ℕ) (k m p r : ℕ) : ℕ := msl f (mw1 k m) (mw2 k m) p r
def mwT (k m : ℕ) : ℕ := Nat.add (mw1 k m) (mw2 k m)

/-- kind-aware evaluation (reads only what the kind needs: a constant term reads no point, a one-tangent term one point),
equal to the generic forms (`mvK_eq` …) -/
def mvK (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.mul 1024 (lb top bk L U))
      (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (f p))) (Nat.mul m (lo32 (f r)))) (Nat.beq k 3))
    (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 (f p)))) (Nat.beq k 2))
    (Nat.mul 1024 (lo32 (f p))) (Nat.beq k 1)
/-- a tangent's charge at `L0`: `l (h − KU1)⁺ (p − L0)` (`sg`: true for `(h − KU1)⁺`, false for `(KU1 − h)⁺`) -/
def chg (f : ℕ → ℕ) (sg : Bool) (L0 l p : ℕ) : ℕ :=
  Nat.mul (Nat.mul l (Bool.rec (motive := fun _ => ℕ) (Nat.sub 2000000000 (hi32 (hi32 (f p)))) (Nat.sub (hi32 (hi32 (f p))) 2000000000) sg)) (Nat.sub p L0)
def mcK (f : ℕ → ℕ) (sg : Bool) (L0 k m p r : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
      (Nat.add (chg f sg L0 (Nat.sub 1024 m) p) (chg f sg L0 m r)) (Nat.beq k 3))
    (chg f sg L0 m p) (Nat.beq k 2))
    (chg f sg L0 1024 p) (Nat.beq k 1)
def mslK (f : ℕ → ℕ) (k m p r : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
      (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 (f p)))) (Nat.mul m (lo32 (hi32 (f r))))) (Nat.beq k 3))
    (Nat.mul m (lo32 (hi32 (f p)))) (Nat.beq k 2))
    (Nat.mul 1024 (lo32 (hi32 (f p)))) (Nat.beq k 1)

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp [h, beq_false h]

theorem mvK_eq (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : mvK top bk f L U k m p r = mvT top bk f L U k m p r := by
  unfold mvK mvT mval mwc mw1 mw2
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
  · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mcpK_eq (f : ℕ → ℕ) (L0 k m p r : ℕ) : mcK f true L0 k m p r = mcpT f L0 k m p r := by
  unfold mcK chg mcpT mcp mw1 mw2
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
  · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mcnK_eq (f : ℕ → ℕ) (L0 k m p r : ℕ) : mcK f false L0 k m p r = mcnT f L0 k m p r := by
  unfold mcK chg mcnT mcn mw1 mw2
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
  · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mslK_eq (f : ℕ → ℕ) (k m p r : ℕ) : mslK f k m p r = mslT f k m p r := by
  unfold mslK mslT msl mw1 mw2
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
  · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]

/-- the kind-aware decode: the points only where the kind reads them -/
def dec4K (w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  forceR (fk w o) fun a => forceR (fm w o a) fun m =>
  forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (fj w o 2)) 0 (Nat.beq a 0)) fun p =>
  forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (fj w o 9)) (Nat.beq a 3)) fun r => forceR (Nat.add o (plen a)) fun o' => k a m p r o'

/-- one anchored minorant term in the short forms -/
theorem mtermT {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    {L0 L U k m p r : ℕ} (hL0 : L0 ≤ L) (hok : mokT R tD bD f L U k m p r = true)
    {s : ℝ} (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokT at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okA hlb hD hpt hR L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1 hok.2 s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

end AMW.Cert.PCell

end
