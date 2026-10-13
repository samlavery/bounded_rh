/-
AMW/TanChord.lean — two more per-term minorants for the slope test: the extended tangent and the chord.

(1) The extended tangent.  For a grid point p in a certified convex region [za, zb] (w″ ≥ 0, from the region's chain
of convex cells), the tangent at p bounds w below on the whole term range [L, U] as soon as the derivative table shows
w′ ≥ w′(p) on [zb, U] and w′ ≤ w′(p) on [L, za]: on the convex piece w′ is monotone, outside it the table bounds
take over, and the line lemma `AMW.Min.line_of_deriv` closes (`ext_tangent`).  Since w′(p) is known only through the
point pair (P, M), the table conditions are read against that pair: lo32(lbDr zb U) ≥ 4U1 − M, hi32(lbDr L za) ≥ 4U1 − P.

(2) The chord.  On a range [a, b] where w″ ≤ 0 (the concave cell check `concOk`, the mirror of `convOk`, chained as
the convex regions are), any line lying below w at a and at b lies below w on [a, b] (`chord_le`).  The raw line takes
the chord slope from the two point bounds rounded down, anchors at a, and checks the end b.

Both are re-expressed at the term's expansion point QS as packed triples (`lmAt`), certified in the form `PkOK0`
(slope claims hold unconditionally), so they plug into `pk_term` and the slope test like the other modes.
-/
import AMW.LineMode

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-! ### the real lemmas -/

/-- **the extended tangent**: the tangent at `p` bounds `f` below on `[lo, hi]` when `f′` is monotone on a piece
`[za, zb] ∋ p` and lies on the right side of `f′(p)` outside it. -/
theorem ext_tangent {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {lo za p zb hi : ℝ}
    (hmono : MonotoneOn f' (Set.Icc za zb)) (hp1 : za ≤ p) (hp2 : p ≤ zb)
    (hL : ∀ y ∈ Set.Icc lo za, f' y ≤ f' p) (hR : ∀ y ∈ Set.Icc zb hi, f' p ≤ f' y) :
    ∀ s ∈ Set.Icc lo hi, f p + f' p * (s - p) ≤ f s := by
  refine AMW.Min.line_of_deriv hf le_rfl (fun y hy => ?_) (fun y hy => ?_)
  · rcases le_or_gt y za with h | h
    · exact hL y ⟨hy.1.le, h⟩
    · exact hmono ⟨h.le, hy.2.le.trans hp2⟩ ⟨hp1, hp2⟩ hy.2.le
  · rcases le_or_gt y zb with h | h
    · exact hmono ⟨hp1, hp2⟩ ⟨hp1.trans hy.1.le, h⟩ hy.1.le
    · exact hR y ⟨h.le, hy.2.le⟩

/-- **the chord**: on a range where `f″ ≤ 0`, a line below `f` at both ends is below `f` throughout. -/
theorem chord_le {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {a b c β : ℝ} (hab : a ≤ b) (hc : ∀ x, a ≤ x → x ≤ b → f'' x ≤ 0)
    (ha : c + β * a ≤ f a) (hb : c + β * b ≤ f b) : ∀ s, a ≤ s → s ≤ b → c + β * s ≤ f s := by
  set g : ℝ → ℝ := fun x => f x - (c + β * x) with hg
  have hgd : ∀ x, HasDerivAt g (f' x - β) x := by
    intro x
    have h2 : HasDerivAt (fun s : ℝ => c + β * s) β x := by
      simpa using ((hasDerivAt_id x).const_mul β).const_add c
    exact (hf x).sub h2
  have hA : AntitoneOn f' (Set.Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun z _ => (hf' z).continuousAt.continuousWithinAt)
    (fun z _ => (hf' z).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [interior_Icc] at hz; rw [(hf' z).deriv]; exact hc z hz.1.le hz.2.le)
  have hanti : AntitoneOn (deriv g) (interior (Set.Icc a b)) := by
    intro x hx y hy hxy
    rw [(hgd x).deriv, (hgd y).deriv]
    rw [interior_Icc] at hx hy
    have := hA ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy
    linarith
  have hconc : ConcaveOn ℝ (Set.Icc a b) g := AntitoneOn.concaveOn_of_deriv (convex_Icc a b)
    (fun x _ => (hgd x).continuousAt.continuousWithinAt)
    (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) hanti
  intro s hs1 hs2
  have h := hconc.ge_on_segment (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
    (by rw [segment_eq_Icc hab]; exact ⟨hs1, hs2⟩)
  simp only [hg] at h
  have h1 : 0 ≤ f a - (c + β * a) := by linarith
  have h2 : 0 ≤ f b - (c + β * b) := by linarith
  have := le_trans (le_min h1 h2) h
  linarith

theorem mono_of_w2 {za zb : ℝ} (h : ∀ x, za ≤ x → x ≤ zb → 0 ≤ w2 x) : MonotoneOn w1 (Set.Icc za zb) := by
  have hd : ∀ x, HasDerivAt w1 (w2 x) x := fun x => AMW.hasDerivAt_w1AM x
  refine monotoneOn_of_deriv_nonneg (convex_Icc za zb) (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
  rw [interior_Icc] at hx
  rw [(hd x).deriv]; exact h x hx.1.le hx.2.le

/-! ### the concave cell check (the mirror of `convOk`) -/

/-- `max(hi, −lo)` bounds `|a|` above (scale `DZ`) -/
def mabsU (I : AMW.G.IV) : AMW.G.SZ := AMW.G.SZ.max I.hi I.lo.neg

theorem mabsU_ge {I : AMW.G.IV} {a : ℝ} (h : I.Enc a) : |a| * AMW.G.DZ ≤ (mabsU I).v := by
  have hD := AMW.G.DZ_pos
  unfold mabsU
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    have := (le_div_iff₀ hD).mp h.2
    exact this.trans (AMW.G.SZ.le_v_max_left _ _)
  · rw [abs_of_nonpos ha]
    have := (div_le_iff₀ hD).mp h.1
    refine le_trans ?_ (AMW.G.SZ.le_v_max_right _ _)
    rw [AMW.G.SZ.v_neg]; linarith

/-- `w''/2 ≤ k'² + k k''` above, at scale `DZ²` -/
def w2U (c : AMW.G.CellA) : AMW.G.SZ :=
  AMW.G.SZ.add (AMW.G.SZ.mul (mabsU c.K1) (mabsU c.K1)) ((c.K0.mul c.K2).hi.muln AMW.G.DZ)

def nonposZ (a : AMW.G.SZ) : Bool := Nat.ble a.p a.n

theorem nonposZ_iff (a : AMW.G.SZ) (h : nonposZ a = true) : a.v ≤ 0 := by
  unfold nonposZ at h
  rw [Nat.ble_eq] at h
  have : (a.p : ℝ) ≤ a.n := by exact_mod_cast h
  unfold AMW.G.SZ.v; linarith

theorem w2_nonpos (c : AMW.G.CellA) (hc : c.ok = true) (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L)
    (hW : nonposZ (w2U c) = true) {x : ℝ} (hx1 : (c.LN : ℝ) / AMW.G.SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / AMW.G.SC) :
    AMW.w2AM x ≤ 0 := by
  have hD := AMW.G.DZ_pos
  have hK1 := c.K1_enc hc hE2 hx1 hx2
  have hKK := AMW.G.IV.enc_mul (c.K0_enc hc hx1 hx2) (c.K2_enc hc hE2 hE3 hx1 hx2)
  have hW' := nonposZ_iff _ hW
  unfold w2U at hW'
  rw [AMW.G.SZ.v_add, AMW.G.SZ.v_mul, AMW.G.SZ.v_muln] at hW'
  have hsk := mabsU_ge hK1
  have hs0 : 0 ≤ |AMW.k1AM x| * AMW.G.DZ := by positivity
  have hsq : (AMW.k1AM x) ^ 2 * (AMW.G.DZ : ℝ) ^ 2 ≤ (mabsU c.K1).v * (mabsU c.K1).v := by
    have := mul_le_mul hsk hsk hs0 (hs0.trans hsk)
    rw [show |AMW.k1AM x| * AMW.G.DZ * (|AMW.k1AM x| * AMW.G.DZ) = |AMW.k1AM x| ^ 2 * (AMW.G.DZ : ℝ) ^ 2 by ring,
      sq_abs] at this
    exact this
  have hq := hKK.2
  have hD2 : (0 : ℝ) < (AMW.G.DZ : ℝ) ^ 2 := by positivity
  unfold AMW.w2AM
  generalize (c.K0.mul c.K2).hi.v = q at hq hW'
  generalize (mabsU c.K1).v = sv at hsq hW'
  generalize AMW.kfunAM x * AMW.k2AM x = kk at hq ⊢
  generalize AMW.k1AM x = a at hsq ⊢
  have hq' : kk * AMW.G.DZ ≤ q := (le_div_iff₀ hD).mp hq
  have hkk : kk * (AMW.G.DZ : ℝ) ^ 2 ≤ q * AMW.G.DZ := by
    have := mul_le_mul_of_nonneg_right hq' hD.le; linarith [show kk * AMW.G.DZ * AMW.G.DZ = kk * (AMW.G.DZ : ℝ) ^ 2 by ring]
  have h3 : (a ^ 2 + kk) * (AMW.G.DZ : ℝ) ^ 2 ≤ 0 := by linarith
  have := nonpos_of_mul_nonpos_left h3 hD2
  linarith

/-- the concave cell check: `w'' ≤ 0` on the cell -/
def concOk (c : CellN) : Bool := c.okD && Nat.blt 0 c.A.E3L && nonposZ (w2U c.A)

theorem cellConc_sound (c : CellN) (hc : concOk c = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : w2 x ≤ 0 := by
  simp only [concOk, CellN.okD, Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hok, hE2⟩, hE3⟩, hW⟩ := hc
  exact w2_nonpos c.A hok hE2 hE3 hW hx1 hx2

/-- a chain `a = c₀ ≤ c₁ ≤ … ≤ c_k` of cells `[c_i, c_(i+1)]`, each certifying `w'' ≤ 0` -/
def chainOkC (a : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && concOk (ccell a b) && ih b) l a

theorem chainOkC_sound : ∀ (l : List ℕ) (a : ℕ), chainOkC a l = true → l ≠ [] →
    ∀ x : ℝ, (a : ℝ) / SC ≤ x → x ≤ (chainLast a l : ℝ) / SC → w2 x ≤ 0 := by
  intro l
  induction l with
  | nil => intro a _ h; exact absurd rfl h
  | cons b r ih =>
    intro a h _ x hx1 hx2
    have h' : (Nat.ble a b && Nat.ble (Nat.add b 1) KB && concOk (ccell a b) && chainOkC b r) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨⟨⟨hab, hbK⟩, hcv⟩, hr⟩ := h'
    have hbK' : b < KB := by simp only [Nat.add_eq] at hbK; omega
    rcases le_or_gt x ((b : ℝ) / SC) with hxb | hxb
    · exact cellConc_sound (ccell a b) hcv x (by rw [ccell_LN hbK']; exact hx1) (by rw [ccell_UN hbK']; exact hxb)
    · cases r with
      | nil =>
        have e : chainLast a [b] = b := rfl
        rw [e] at hx2; linarith
      | cons c r' =>
        have e : chainLast a (b :: c :: r') = chainLast b (c :: r') := rfl
        rw [e] at hx2
        exact ih b hr (List.cons_ne_nil c r') x hxb.le hx2

/-- concave regions by index `k < 16`, in the format of the convex regions (`rgA`, `rgB`, chains in `R.2.2`) -/
def rgOkC (R : ℕ × ℕ × List (List ℕ)) : Bool :=
  allBelow 16 fun k => Nat.blt (rgB R k) (rgA R k)
    || (Nat.ble 1 (R.2.2.getD k []).length && chainOkC (rgA R k) (R.2.2.getD k [])
      && Nat.beq (chainLast (rgA R k) (R.2.2.getD k [])) (rgB R k))

/-- every point of a certified convex region `k` is convex -/
theorem rg_conv {R : ℕ × ℕ × List (List ℕ)} (hR : rgOk R = true) {k : ℕ} (hk : k < 16) :
    ∀ x : ℝ, (rgA R k : ℝ) / SC ≤ x → x ≤ (rgB R k : ℝ) / SC → 0 ≤ w2 x := by
  intro x hx1 hx2
  have hk' := allBelow_spec hR k hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
  · exfalso
    have : (rgB R k : ℝ) / SC < (rgA R k : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hempty) hSC
    linarith
  · have hne : R.2.2.getD k [] ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    refine (chainOk_sound _ _ hch hne x hx1 ?_).2
    rw [hlast]; exact hx2

/-- every point of a certified concave region `k` is concave -/
theorem rg_conc {R : ℕ × ℕ × List (List ℕ)} (hR : rgOkC R = true) {k : ℕ} (hk : k < 16) :
    ∀ x : ℝ, (rgA R k : ℝ) / SC ≤ x → x ≤ (rgB R k : ℝ) / SC → w2 x ≤ 0 := by
  intro x hx1 hx2
  have hk' := allBelow_spec hR k hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
  · exfalso
    have : (rgB R k : ℝ) / SC < (rgA R k : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hempty) hSC
    linarith
  · have hne : R.2.2.getD k [] ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    refine chainOkC_sound _ _ hch hne x hx1 ?_
    rw [hlast]; exact hx2

/-! ### a line through a grid point, re-expressed at `QS` -/

/-- the value at `QS` of a line through `(p, v)` whose slope lies in the claims `[P/U1 − 2, 2 − M/U1]`, packed with
the claims (`0` if the value would be negative) -/
def lmAt (v P M p QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (lmDn v (Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub 2000000000 M))) P M)
      (lmUp v (Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub M 2000000000))) P M) (Nat.ble 2000000000 M))
    (Bool.rec (motive := fun _ => ℕ)
      (lmDn v (Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub 2000000000 P))) P M)
      (lmUp v (Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub P 2000000000))) P M) (Nat.ble 2000000000 P))
    (Nat.ble p QS)

set_option maxHeartbeats 1000000 in
theorem lmAt_spec (v P M p QS : ℕ) (d : ℝ) (hd1 : (P : ℝ) - 2000000000 ≤ 1000000000 * d)
    (hd2 : 1000000000 * d ≤ 2000000000 - (M : ℝ)) :
    lmAt v P M p QS = 0 ∨ ∃ val : ℕ, lmAt v P M p QS = lmPk val P M ∧
      32768 * (val : ℝ) ≤ 32768 * (v : ℝ) + 10000000000 * d * ((QS : ℝ) - p) := by
  unfold lmAt
  by_cases hpq : Nat.ble p QS = true
  · rw [hpq]
    have hpq' : p ≤ QS := Nat.ble_eq.mp hpq
    have hdist : ((Nat.sub QS p : ℕ) : ℝ) = (QS : ℝ) - p := by rw [Nat.sub_eq, Nat.cast_sub hpq']
    have hm : ((P : ℝ) - 2000000000) * ((QS : ℝ) - p) ≤ 1000000000 * d * ((QS : ℝ) - p) :=
      mul_le_mul_of_nonneg_right hd1 (by rw [← hdist]; exact Nat.cast_nonneg _)
    by_cases h2 : Nat.ble 2000000000 P = true
    · rw [h2]
      have h2' : 2000000000 ≤ P := Nat.ble_eq.mp h2
      right
      obtain ⟨val, hval, hle⟩ := lmUp_val v (Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub P 2000000000))) P M
      refine ⟨val, hval, ?_⟩
      have ea : ((Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub P 2000000000)) : ℕ) : ℝ)
          = 10 * ((QS : ℝ) - p) * ((P : ℝ) - 2000000000) := by
        simp only [Nat.mul_eq]; push_cast; rw [hdist, Nat.sub_eq, Nat.cast_sub h2']; push_cast; ring
      rw [ea] at hle
      linarith
    · have h2f : Nat.ble 2000000000 P = false := Bool.eq_false_iff.mpr h2
      rw [h2f]
      have h2' : P < 2000000000 := by rw [Nat.ble_eq] at h2; omega
      rcases lmDn_val v (Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub 2000000000 P))) P M with h0 | ⟨val, hval, hle⟩
      · left; exact h0
      · right
        refine ⟨val, hval, ?_⟩
        have ea : ((Nat.mul 10 (Nat.mul (Nat.sub QS p) (Nat.sub 2000000000 P)) : ℕ) : ℝ)
            = 10 * ((QS : ℝ) - p) * (2000000000 - (P : ℝ)) := by
          simp only [Nat.mul_eq]; push_cast; rw [hdist, Nat.sub_eq, Nat.cast_sub h2'.le]; push_cast; ring
        rw [ea] at hle
        linarith
  · have hpqf : Nat.ble p QS = false := Bool.eq_false_iff.mpr hpq
    rw [hpqf]
    have hpq' : QS < p := by rw [Nat.ble_eq] at hpq; omega
    have hdist : ((Nat.sub p QS : ℕ) : ℝ) = (p : ℝ) - QS := by rw [Nat.sub_eq, Nat.cast_sub hpq'.le]
    have hm : 1000000000 * d * ((p : ℝ) - QS) ≤ (2000000000 - (M : ℝ)) * ((p : ℝ) - QS) :=
      mul_le_mul_of_nonneg_right hd2 (by rw [← hdist]; exact Nat.cast_nonneg _)
    by_cases h2 : Nat.ble 2000000000 M = true
    · rw [h2]
      have h2' : 2000000000 ≤ M := Nat.ble_eq.mp h2
      right
      obtain ⟨val, hval, hle⟩ := lmUp_val v (Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub M 2000000000))) P M
      refine ⟨val, hval, ?_⟩
      have ea : ((Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub M 2000000000)) : ℕ) : ℝ)
          = 10 * ((p : ℝ) - QS) * ((M : ℝ) - 2000000000) := by
        simp only [Nat.mul_eq]; push_cast; rw [hdist, Nat.sub_eq, Nat.cast_sub h2']; push_cast; ring
      rw [ea] at hle
      linarith
    · have h2f : Nat.ble 2000000000 M = false := Bool.eq_false_iff.mpr h2
      rw [h2f]
      have h2' : M < 2000000000 := by rw [Nat.ble_eq] at h2; omega
      rcases lmDn_val v (Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub 2000000000 M))) P M with h0 | ⟨val, hval, hle⟩
      · left; exact h0
      · right
        refine ⟨val, hval, ?_⟩
        have ea : ((Nat.mul 10 (Nat.mul (Nat.sub p QS) (Nat.sub 2000000000 M)) : ℕ) : ℝ)
            = 10 * ((p : ℝ) - QS) * (2000000000 - (M : ℝ)) := by
          simp only [Nat.mul_eq]; push_cast; rw [hdist, Nat.sub_eq, Nat.cast_sub h2'.le]; push_cast; ring
        rw [ea] at hle
        linarith

/-- what a packed triple certifies, with no side condition on the claims -/
def PkOK0 (L U QS val P M : ℕ) : Prop :=
  ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC → ∃ d : ℝ,
    (P : ℝ) - 2000000000 ≤ 1000000000 * d ∧ 1000000000 * d ≤ 2000000000 - (M : ℝ) ∧
    32768 * (val : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768)) ≤ 327680000000000 * wfun s

theorem PkOK0.pkOK {L U QS val P M : ℕ} (h : PkOK0 L U QS val P M) : PkOK L U QS val P M :=
  fun _ _ => h

/-- a line through `(p, v)` with a fixed slope `d` in the claims, below `w` on the range, gives `PkOK0` at `QS` -/
theorem lmAt_pk {v P M p QS L U : ℕ} {d : ℝ} (hd1 : (P : ℝ) - 2000000000 ≤ 1000000000 * d)
    (hd2 : 1000000000 * d ≤ 2000000000 - (M : ℝ))
    (hline : ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
      (v : ℝ) / 10000000000 + d * (s - (p : ℝ) / 32768) ≤ wfun s) :
    lmAt v P M p QS = 0 ∨ ∃ val : ℕ, lmAt v P M p QS = lmPk val P M ∧ PkOK0 L U QS val P M := by
  rcases lmAt_spec v P M p QS d hd1 hd2 with h0 | ⟨val, hval, hle⟩
  · exact Or.inl h0
  · refine Or.inr ⟨val, hval, fun s hs1 hs2 => ⟨d, hd1, hd2, ?_⟩⟩
    have h := hline s hs1 hs2
    have key : 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        = 327680000000000 * (d * (s - (p : ℝ) / 32768)) - 10000000000 * d * ((QS : ℝ) - p) := by ring
    rw [key]
    linarith

/-! ### (1) the extended tangent as a packed triple -/

/-- the derivative table shows `w′ ≥ 2 − M/U1` on `[zb, U]` (nothing to show when `U ≤ zb`) -/
def edgeR (tD : ℕ) (bD : ℕ → ℕ) (zb U M : ℕ) : Bool :=
  Nat.ble U zb || forceB (lo32 (lbDr tD bD zb U)) fun D => Nat.ble 1 D && Nat.ble (Nat.sub 4000000000 M) D
/-- the derivative table shows `w′ ≤ P/U1 − 2` on `[L, za]` (nothing to show when `za ≤ L`) -/
def edgeL (tD : ℕ) (bD : ℕ → ℕ) (L za P : ℕ) : Bool :=
  Nat.ble za L || forceB (hi32 (lbDr tD bD L za)) fun D => Nat.ble 1 D && Nat.ble (Nat.sub 4000000000 P) D

/-- the conditions of the extended tangent: `p` in the region `[za, zb]` (index `k < 16`), nonzero claims, the
table on both sides -/
def lmEc (tD : ℕ) (bD : ℕ → ℕ) (k L U p P M za zb : ℕ) : Bool :=
  Nat.blt k 16 && Nat.ble za p && Nat.ble p zb && Nat.ble 1 P && Nat.ble 1 M
    && edgeR tD bD zb U M && edgeL tD bD L za P

/-- **the extended tangent** at the grid point `p` of the convex region `k` of `R`, for the term range `[L, U]`,
re-expressed at `QS`; `0` when a condition fails -/
def lmE (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (k L U QS p : ℕ) : ℕ :=
  forceR (f p) fun X =>
  forceR (lo32 (hi32 X)) fun P =>
  forceR (hi32 (hi32 X)) fun M =>
  forceR (rgA R k) fun za =>
  forceR (rgB R k) fun zb =>
  Bool.rec (motive := fun _ => ℕ) 0 (lmAt (lo32 X) P M p QS) (lmEc tD bD k L U p P M za zb)

theorem edgeR_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {zb U M : ℕ} (h : edgeR tD bD zb U M = true) :
    U ≤ zb ∨ ∀ y : ℝ, (zb : ℝ) / SC ≤ y → y ≤ (U : ℝ) / SC → 2 - (M : ℝ) / U1 ≤ w1 y := by
  unfold edgeR at h
  simp only [Bool.or_eq_true, Nat.ble_eq, forceB_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    intro y hy1 hy2
    have hlo := AMW.Min.slopeLo_sound hD (by omega : lo32 (lbDr tD bD zb U) ≠ 0) y hy1 hy2
    have hn := natsub_ge 4000000000 M
    have h2' : ((Nat.sub 4000000000 M : ℕ) : ℝ) ≤ (lo32 (lbDr tD bD zb U) : ℝ) := by exact_mod_cast h2
    rw [Nat.sub_eq] at h2'
    push_cast at hn
    have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    rw [hU1] at hlo ⊢
    show 2 - (M : ℝ) / 1000000000 ≤ AMW.w1AM y
    have : (4000000000 - (M : ℝ)) / 1000000000 ≤ (lo32 (lbDr tD bD zb U) : ℝ) / 1000000000 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have e : (4000000000 - (M : ℝ)) / 1000000000 = 4 - (M : ℝ) / 1000000000 := by ring
    linarith

theorem edgeL_sound {tD : ℕ} {bD : ℕ → ℕ} (hD : LBSoundD tD bD) {L za P : ℕ} (h : edgeL tD bD L za P = true) :
    za ≤ L ∨ ∀ y : ℝ, (L : ℝ) / SC ≤ y → y ≤ (za : ℝ) / SC → w1 y ≤ (P : ℝ) / U1 - 2 := by
  unfold edgeL at h
  simp only [Bool.or_eq_true, Nat.ble_eq, forceB_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    intro y hy1 hy2
    have hhi := AMW.Min.slopeHi_sound hD (by omega : hi32 (lbDr tD bD L za) ≠ 0) y hy1 hy2
    have hn := natsub_ge 4000000000 P
    have h2' : ((Nat.sub 4000000000 P : ℕ) : ℝ) ≤ (hi32 (lbDr tD bD L za) : ℝ) := by exact_mod_cast h2
    rw [Nat.sub_eq] at h2'
    push_cast at hn
    have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    rw [hU1] at hhi ⊢
    show AMW.w1AM y ≤ (P : ℝ) / 1000000000 - 2
    have : (4000000000 - (P : ℝ)) / 1000000000 ≤ (hi32 (lbDr tD bD L za) : ℝ) / 1000000000 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have e : (4000000000 - (P : ℝ)) / 1000000000 = 4 - (P : ℝ) / 1000000000 := by ring
    linarith

theorem lo32_lt (v : ℕ) : lo32 v < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)

/-- **the extended tangent is certified**: a nonzero triple of `lmE` satisfies `PkOK0` on the term range. -/
theorem lmE_spec {f : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (k L U QS p : ℕ) :
    lmE f tD bD R k L U QS p = 0 ∨ ∃ val P M : ℕ, lmE f tD bD R k L U QS p = lmPk val P M ∧ P < 2 ^ 32 ∧
      PkOK0 L U QS val P M := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hSCp : (0 : ℝ) < SC := by norm_num [SC]
  have hU1 : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  unfold lmE
  simp only [forceR_eq]
  by_cases hc : lmEc tD bD k L U p (lo32 (hi32 (f p))) (hi32 (hi32 (f p))) (rgA R k) (rgB R k) = true
  · rw [hc]
    unfold lmEc at hc
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hk, hza⟩, hzb⟩, hP1⟩, hM1⟩, hER⟩, hEL⟩ := hc
    have hps := (hpt p).2
    obtain ⟨-, hPd⟩ := hps.1 (by omega)
    obtain ⟨-, hMd⟩ := hps.2 (by omega)
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPd hMd
    rw [hU1, div_le_iff₀ (by norm_num)] at hPd hMd
    have hd1 : (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) := by linarith
    have hd2 : 1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) := by linarith
    have hmono := mono_of_w2 (rg_conv hR hk)
    have hp1 : (rgA R k : ℝ) / SC ≤ (p : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hza) hSCp.le
    have hp2 : (p : ℝ) / SC ≤ (rgB R k : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hzb) hSCp.le
    have hL : ∀ y ∈ Set.Icc ((L : ℝ) / SC) ((rgA R k : ℝ) / SC), w1 y ≤ w1 ((p : ℝ) / SC) := by
      intro y hy
      rcases edgeL_sound hD hEL with h | h
      · have hLz : (rgA R k : ℝ) / SC ≤ (L : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) hSCp.le
        exact hmono ⟨hLz.trans hy.1, hy.2.trans (hp1.trans hp2)⟩ ⟨hp1, hp2⟩ (hy.2.trans hp1)
      · have := h y hy.1 hy.2
        rw [hU1] at this
        have e : (lo32 (hi32 (f p)) : ℝ) / 1000000000 - 2 ≤ w1 ((p : ℝ) / SC) := by
          rw [div_sub' (by norm_num), div_le_iff₀ (by norm_num)]; linarith
        linarith
    have hR' : ∀ y ∈ Set.Icc ((rgB R k : ℝ) / SC) ((U : ℝ) / SC), w1 ((p : ℝ) / SC) ≤ w1 y := by
      intro y hy
      rcases edgeR_sound hD hER with h | h
      · have hUz : (U : ℝ) / SC ≤ (rgB R k : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) hSCp.le
        exact hmono ⟨hp1, hp2⟩ ⟨hp1.trans (hp2.trans hy.1), hy.2.trans hUz⟩ (hp2.trans hy.1)
      · have := h y hy.1 hy.2
        rw [hU1] at this
        have e : w1 ((p : ℝ) / SC) ≤ 2 - (hi32 (hi32 (f p)) : ℝ) / 1000000000 := by
          rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by norm_num)]; linarith
        linarith
    have htan := ext_tangent (f := wfun) (f' := w1) (fun x => hasDerivAt_wfun x (kD_neg x).ne) hmono hp1 hp2 hL hR'
    rcases lmAt_pk (L := L) (U := U) (QS := QS) (v := lo32 (f p)) (p := p) hd1 hd2 (fun s hs1 hs2 => by
        have h1 := htan s ⟨hs1, hs2⟩
        have h2 := (hpt p).1
        rw [show (p : ℝ) / 32768 = (p : ℝ) / SC by rw [hSC]]
        linarith) with h0 | ⟨val, hval, hpk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨val, _, _, hval, lo32_lt _, hpk⟩
  · left
    rw [Bool.not_eq_true] at hc
    rw [hc]

/-! ### (2) the chord on a concave range as a packed triple -/

/-- the chord slope from `(a, va)` to `(b, vb)`, rounded down (units `1/U1`, offset `2U1`) -/
def chSlope (va vb a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Nat.sub 2000000000 (AMW.G.ndivc (Nat.mul 32768 (Nat.sub va vb)) (Nat.mul 10 (Nat.sub b a))))
    (Nat.add 2000000000 (Nat.div (Nat.mul 32768 (Nat.sub vb va)) (Nat.mul 10 (Nat.sub b a))))
    (Nat.ble va vb)

/-- the line from `(a, va)` with slope `D` is below `vb` at `b` -/
def chEnd (va vb a b D : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Nat.ble (Nat.mul 32768 va) (Nat.add (Nat.mul 32768 vb) (Nat.mul 10 (Nat.mul (Nat.sub b a) (Nat.sub 2000000000 D)))))
    (Nat.ble (Nat.add (Nat.mul 32768 va) (Nat.mul 10 (Nat.mul (Nat.sub b a) (Nat.sub D 2000000000)))) (Nat.mul 32768 vb))
    (Nat.ble 2000000000 D)

/-- the conditions of the chord: `[a, b] ⊇ [L, U]` inside the concave region `k < 16`, a valid slope, the end check -/
def lmCc (RC : ℕ × ℕ × List (List ℕ)) (k L U a b va vb D : ℕ) : Bool :=
  Nat.blt k 16 && Nat.ble (rgA RC k) a && Nat.ble a L && Nat.ble U b && Nat.ble a b && Nat.ble b (rgB RC k)
    && Nat.ble 1 D && Nat.blt D 4000000000 && chEnd va vb a b D

/-- **the chord** over the grid points `a ≤ L ≤ U ≤ b` of the concave region `k` of `RC`, re-expressed at `QS`;
`0` when a condition fails -/
def lmC (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (RC : ℕ × ℕ × List (List ℕ)) (k L U QS a b : ℕ) : ℕ :=
  forceR (lmV top bk f a) fun va =>
  forceR (lmV top bk f b) fun vb =>
  forceR (chSlope va vb a b) fun D =>
  Bool.rec (motive := fun _ => ℕ) 0 (lmAt va D (Nat.sub 4000000000 D) a QS) (lmCc RC k L U a b va vb D)

theorem chEnd_sound {va vb a b D : ℕ} (hab : a ≤ b) (h : chEnd va vb a b D = true) :
    32768 * (va : ℝ) + 10 * ((b : ℝ) - a) * ((D : ℝ) - 2000000000) ≤ 32768 * (vb : ℝ) := by
  have hd : ((Nat.sub b a : ℕ) : ℝ) = (b : ℝ) - a := by rw [Nat.sub_eq, Nat.cast_sub hab]
  unfold chEnd at h
  by_cases h2 : Nat.ble 2000000000 D = true
  · rw [h2] at h
    have h2' : 2000000000 ≤ D := Nat.ble_eq.mp h2
    rw [Nat.ble_eq] at h
    have h' : ((Nat.add (Nat.mul 32768 va) (Nat.mul 10 (Nat.mul (Nat.sub b a) (Nat.sub D 2000000000))) : ℕ) : ℝ)
        ≤ ((Nat.mul 32768 vb : ℕ) : ℝ) := by exact_mod_cast h
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    push_cast at h'
    rw [hd, Nat.sub_eq, Nat.cast_sub h2'] at h'
    push_cast at h'
    linarith
  · have h2f : Nat.ble 2000000000 D = false := Bool.eq_false_iff.mpr h2
    rw [h2f] at h
    have h2' : D < 2000000000 := by rw [Nat.ble_eq] at h2; omega
    rw [Nat.ble_eq] at h
    have h' : ((Nat.mul 32768 va : ℕ) : ℝ)
        ≤ ((Nat.add (Nat.mul 32768 vb) (Nat.mul 10 (Nat.mul (Nat.sub b a) (Nat.sub 2000000000 D))) : ℕ) : ℝ) := by
      exact_mod_cast h
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    push_cast at h'
    rw [hd, Nat.sub_eq, Nat.cast_sub h2'.le] at h'
    push_cast at h'
    linarith

/-- **the chord is certified**: a nonzero triple of `lmC` satisfies `PkOK0` on the term range. -/
theorem lmC_spec {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} {RC : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk)
    (hpt : PTF f) (hRC : rgOkC RC = true) (k L U QS a b : ℕ) :
    lmC top bk f RC k L U QS a b = 0 ∨ ∃ val P M : ℕ, lmC top bk f RC k L U QS a b = lmPk val P M ∧ P < 2 ^ 32 ∧
      PkOK0 L U QS val P M := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hSCp : (0 : ℝ) < SC := by norm_num [SC]
  have hva := lmV_sound hlb hpt a
  have hvb := lmV_sound hlb hpt b
  unfold lmC
  simp only [forceR_eq]
  generalize lmV top bk f a = va at hva ⊢
  generalize lmV top bk f b = vb at hvb ⊢
  generalize chSlope va vb a b = D
  by_cases hc : lmCc RC k L U a b va vb D = true
  · rw [hc]
    unfold lmCc at hc
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, haz⟩, haL⟩, hUb⟩, hab⟩, hbz⟩, hD1⟩, hD4⟩, hend⟩ := hc
    have hE := chEnd_sound hab hend
    set d : ℝ := ((D : ℝ) - 2000000000) / 1000000000 with hd
    have hM : ((Nat.sub 4000000000 D : ℕ) : ℝ) = 4000000000 - (D : ℝ) := by
      rw [Nat.sub_eq, Nat.cast_sub hD4.le]; push_cast; ring
    have hd1 : (D : ℝ) - 2000000000 ≤ 1000000000 * d := by rw [hd]; field_simp; linarith
    have hd2 : 1000000000 * d ≤ 2000000000 - ((Nat.sub 4000000000 D : ℕ) : ℝ) := by
      rw [hM, hd]; field_simp; linarith
    have hconc := rg_conc hRC hk
    have ha' : (rgA RC k : ℝ) / SC ≤ (a : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast haz) hSCp.le
    have hb' : (b : ℝ) / SC ≤ (rgB RC k : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hbz) hSCp.le
    have hab' : (a : ℝ) / SC ≤ (b : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hab) hSCp.le
    have hch := chord_le (f := wfun) (f' := w1) (f'' := w2) (fun x => hasDerivAt_wfun x (kD_neg x).ne)
      (fun x => hasDerivAt_w1 x (kD_neg x).ne) hab'
      (fun x h1 h2 => hconc x (ha'.trans h1) (h2.trans hb'))
      (c := (va : ℝ) / 10000000000 - d * ((a : ℝ) / 32768)) (β := d)
      (by rw [hSC] at hva; rw [hSC]; linarith)
      (by
        rw [hSC] at hvb; rw [hSC]
        have : (va : ℝ) / 10000000000 + d * (((b : ℝ) - a) / 32768) ≤ (vb : ℝ) / 10000000000 := by
          rw [hd]
          have e : (va : ℝ) / 10000000000 + ((D : ℝ) - 2000000000) / 1000000000 * (((b : ℝ) - a) / 32768)
              = (32768 * (va : ℝ) + 10 * ((b : ℝ) - a) * ((D : ℝ) - 2000000000)) / 327680000000000 := by ring
          rw [e, div_le_iff₀ (by norm_num)]
          linarith
        have e2 : (va : ℝ) / 10000000000 - d * ((a : ℝ) / 32768) + d * ((b : ℝ) / 32768)
            = (va : ℝ) / 10000000000 + d * (((b : ℝ) - a) / 32768) := by ring
        linarith)
    have hLa : (a : ℝ) / SC ≤ (L : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast haL) hSCp.le
    have hUb' : (U : ℝ) / SC ≤ (b : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hUb) hSCp.le
    rcases lmAt_pk (L := L) (U := U) (QS := QS) (v := va) (p := a) hd1 hd2 (fun s hs1 hs2 => by
        have h1 := hch s (hLa.trans hs1) (hs2.trans hUb')
        have e : (va : ℝ) / 10000000000 - d * ((a : ℝ) / 32768) + d * s
            = (va : ℝ) / 10000000000 + d * (s - (a : ℝ) / 32768) := by ring
        linarith) with h0 | ⟨val, hval, hpk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨val, D, _, hval, by omega, hpk⟩
  · left
    rw [Bool.not_eq_true] at hc
    rw [hc]

/-! ### convex combinations of two certified triples, and the per-term bound -/

/-- the form every mode's triple is certified in: `0` (rejected), or a packed triple with `PkOK0` -/
def PkSpec (L U QS X : ℕ) : Prop :=
  X = 0 ∨ ∃ val P M : ℕ, X = lmPk val P M ∧ P < 2 ^ 32 ∧ PkOK0 L U QS val P M

/-- the combination `(k·X1 + (1024 − k)·X2)/1024` of two packed triples, componentwise rounded down; `0` unless
`k ≤ 1024` and both triples are nonzero -/
def pkComb (k X1 X2 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0
    (lmPk (Nat.div (Nat.add (Nat.mul k (lo32 X1)) (Nat.mul (Nat.sub 1024 k) (lo32 X2))) 1024)
      (Nat.div (Nat.add (Nat.mul k (lo32 (hi32 X1))) (Nat.mul (Nat.sub 1024 k) (lo32 (hi32 X2)))) 1024)
      (Nat.div (Nat.add (Nat.mul k (hi32 (hi32 X1))) (Nat.mul (Nat.sub 1024 k) (hi32 (hi32 X2)))) 1024))
    (Nat.ble k 1024 && Nat.ble 1 X1 && Nat.ble 1 X2)

/-- a convex combination of two lower bounds of `w` is one -/
theorem pkComb_spec {L U QS X1 X2 : ℕ} (h1 : PkSpec L U QS X1) (h2 : PkSpec L U QS X2) (k : ℕ) :
    PkSpec L U QS (pkComb k X1 X2) := by
  unfold pkComb
  by_cases hc : (Nat.ble k 1024 && Nat.ble 1 X1 && Nat.ble 1 X2) = true
  · rw [hc]
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨⟨hk, hX1⟩, hX2⟩ := hc
    rcases h1 with h1 | ⟨v1, P1, M1, e1, hP1, hpk1⟩
    · omega
    rcases h2 with h2 | ⟨v2, P2, M2, e2, hP2, hpk2⟩
    · omega
    clear hX1 hX2
    rw [e1, e2]
    rw [lmPk_P hP1, lmPk_M hP1, lmPk_P hP2, lmPk_M hP2]
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, nat_div_eq]
    right
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at hP1 hP2 ⊢
      have m1 : k * P1 ≤ k * 4294967295 := Nat.mul_le_mul_left k (by omega)
      have m2 : (1024 - k) * P2 ≤ (1024 - k) * 4294967295 := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro s hs1 hs2
      obtain ⟨d1, hd11, hd12, hb1⟩ := hpk1 s hs1 hs2
      obtain ⟨d2, hd21, hd22, hb2⟩ := hpk2 s hs1 hs2
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hk1 : (0 : ℝ) ≤ 1024 - k := by
        have : (k : ℝ) ≤ 1024 := by exact_mod_cast hk
        linarith
      have hkc : (((1024 - k : ℕ)) : ℝ) = 1024 - k := by rw [Nat.cast_sub hk]; norm_num
      have hlo1 : (lo32 (lmPk v1 P1 M1) : ℝ) ≤ v1 := by exact_mod_cast lmPk_lo v1 P1 M1
      have hlo2 : (lo32 (lmPk v2 P2 M2) : ℝ) ≤ v2 := by exact_mod_cast lmPk_lo v2 P2 M2
      have fl : ∀ a : ℕ, (((a / 1024 : ℕ)) : ℝ) * 1024 ≤ a := fun a => by
        have := Nat.div_mul_le_self a 1024; exact_mod_cast this
      have cl : ∀ a : ℕ, (a : ℝ) < (((a / 1024 : ℕ)) : ℝ) * 1024 + 1024 := fun a => by
        have := Nat.lt_div_mul_add (a := a) (b := 1024) (by norm_num); exact_mod_cast this
      refine ⟨((k : ℝ) * d1 + (1024 - k) * d2) / 1024, ?_, ?_, ?_⟩
      · have hfl := fl (k * P1 + (1024 - k) * P2)
        push_cast [hkc] at hfl
        have m1 := mul_le_mul_of_nonneg_left hd11 hk0
        have m2 := mul_le_mul_of_nonneg_left hd21 hk1
        linarith
      · have hcl := cl (k * M1 + (1024 - k) * M2)
        push_cast [hkc] at hcl
        have m1 := mul_le_mul_of_nonneg_left hd12 hk0
        have m2 := mul_le_mul_of_nonneg_left hd22 hk1
        have hfl := fl (k * M1 + (1024 - k) * M2)
        push_cast [hkc] at hfl
        linarith
      · have hfv := fl (k * lo32 (lmPk v1 P1 M1) + (1024 - k) * lo32 (lmPk v2 P2 M2))
        push_cast [hkc] at hfv
        have hlo := lmPk_lo ((k * lo32 (lmPk v1 P1 M1) + (1024 - k) * lo32 (lmPk v2 P2 M2)) / 1024)
          ((k * P1 + (1024 - k) * P2) / 1024) ((k * M1 + (1024 - k) * M2) / 1024)
        have hlo' : (lo32 (lmPk ((k * lo32 (lmPk v1 P1 M1) + (1024 - k) * lo32 (lmPk v2 P2 M2)) / 1024)
            ((k * P1 + (1024 - k) * P2) / 1024) ((k * M1 + (1024 - k) * M2) / 1024)) : ℝ)
            ≤ (((k * lo32 (lmPk v1 P1 M1) + (1024 - k) * lo32 (lmPk v2 P2 M2)) / 1024 : ℕ) : ℝ) := by
          exact_mod_cast hlo
        have m1 := mul_le_mul_of_nonneg_left hb1 hk0
        have m2 := mul_le_mul_of_nonneg_left hb2 hk1
        have m3 := mul_le_mul_of_nonneg_left hlo1 hk0
        have m4 := mul_le_mul_of_nonneg_left hlo2 hk1
        have e : 327680000000000 * ((((k : ℝ) * d1 + (1024 - k) * d2) / 1024) * (s - (QS : ℝ) / 32768))
            = ((k : ℝ) * (327680000000000 * (d1 * (s - (QS : ℝ) / 32768)))
              + (1024 - k) * (327680000000000 * (d2 * (s - (QS : ℝ) / 32768)))) / 1024 := by ring
        rw [e]
        linarith
  · left
    rw [Bool.not_eq_true] at hc
    rw [hc]

/-- the per-term inequality of the slope test for a certified triple read with no charge (`cv`, `bit` set) -/
theorem spec_term {X L U QS EU ED : ℕ} (hX : PkSpec L U QS X)
    (hok : rtok true true L U QS X EU ED = true) (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP true X : ℝ) - (tK true : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK true : ℝ) - (tM true X : ℝ) ∧
      32768 * (tval true X : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg true true L U QS X EU ED : ℝ) ≤ 327680000000000 * wfun s := by
  refine pk_term ?_ hok s hs1 hs2
  rcases hX with h | ⟨val, P, M, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨val, P, M, h1, h2, h3.pkOK⟩

theorem lmE_pk {f : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (k L U QS p : ℕ) : PkSpec L U QS (lmE f tD bD R k L U QS p) :=
  lmE_spec hD hpt hR k L U QS p

theorem lmC_pk {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} {RC : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk)
    (hpt : PTF f) (hRC : rgOkC RC = true) (k L U QS a b : ℕ) : PkSpec L U QS (lmC top bk f RC k L U QS a b) :=
  lmC_spec hlb hpt hRC k L U QS a b

end AMW.Cert.PyrD

end

