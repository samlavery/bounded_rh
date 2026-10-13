import AMW.CMinX

/-! ###### polytope cells (pair-distance splits): the generic pieces (bridge-port)

A polytope cell is a box `l_r ≤ SC g_r ≤ u_r` cut by explicit pair-distance bounds `A_t ≤ SC s_t ≤ B_t`,
`s_t = g_i + … + g_{j−1}` (absent bounds: `A_t = 0`, `B_t` large).  A pair term is then read on its EFFECTIVE range
`[max(A_t, Σ l), min(B_t, Σ u)]`, and its minorant is expanded at the term's box corner `L0 = Σ l ≤ max(A_t, Σ l)`, so
the gap slopes of the minorant leaf keep their form.  Here: kernel `min`/`max`, the anchored per-term minorant (mvt-engine's
MinCore term with the expansion point `L0` below the range), the bound-tightening steps and the empty-range test. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- kernel `max` (two arithmetic primitives; the engine's `nmin a b = a − (a − b)` is the `min`) -/
def nmax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)

theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax
  simp only [Nat.add_eq, Nat.sub_eq]
  omega

theorem le_nmax_right (a b : ℕ) : b ≤ nmax a b := by rw [nmax_eq]; exact le_max_right _ _
theorem le_nmax_left (a b : ℕ) : a ≤ nmax a b := by rw [nmax_eq]; exact le_max_left _ _

theorem natsub_diff (a b : ℕ) : ((a - b : ℕ) : ℝ) - ((b - a : ℕ) : ℝ) = (a : ℝ) - b := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring

theorem SC_pos : (0 : ℝ) < SC := by norm_num [SC]

/-- a pair sum on the cell lies in the effective range: below -/
theorem lo_nmax {A L0 : ℕ} {s : ℝ} (h1 : (A : ℝ) / SC ≤ s) (h2 : (L0 : ℝ) / SC ≤ s) :
    ((nmax A L0 : ℕ) : ℝ) / SC ≤ s := by
  rw [nmax_eq]
  rcases le_total A L0 with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- a pair sum on the cell lies in the effective range: above -/
theorem hi_nmin {B U0 : ℕ} {s : ℝ} (h1 : s ≤ (B : ℝ) / SC) (h2 : s ≤ (U0 : ℝ) / SC) :
    s ≤ ((nmin B U0 : ℕ) : ℝ) / SC := by
  rw [nmin_eq]
  rcases le_total B U0 with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

/-- (5) bound tightening, upper end of a gap: `g + o ≤ Ue/SC` with the other gaps `o ≥ ol/SC` (`sl = l + ol`) gives
`g ≤ (Ue − (sl − l))/SC` -/
theorem fb_hi {g o : ℝ} {l u Ue sl ol : ℕ} (hsl : sl = l + ol) (hu : g ≤ (u : ℝ) / SC)
    (hs : g + o ≤ (Ue : ℝ) / SC) (ho : (ol : ℝ) / SC ≤ o) :
    g ≤ ((nmin u (Nat.sub Ue (Nat.sub sl l)) : ℕ) : ℝ) / SC := by
  have e : Nat.sub sl l = ol := by rw [Nat.sub_eq, hsl]; omega
  rw [e, nmin_eq, Nat.sub_eq]
  rcases le_total u (Ue - ol) with h | h
  · rw [min_eq_left h]; exact hu
  · rw [min_eq_right h]
    rcases le_total ol Ue with h' | h'
    · rw [Nat.cast_sub h', sub_div]; linarith
    · have : (Ue : ℝ) / SC ≤ (ol : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h') SC_pos.le
      rw [Nat.sub_eq_zero_of_le h']; simp only [Nat.cast_zero, zero_div]; linarith

/-- (5) bound tightening, lower end of a gap: `Le/SC ≤ g + o` with the other gaps `o ≤ ou/SC` (`su = u + ou`) gives
`(Le − (su − u))/SC ≤ g` (a truncated difference is `0 ≤ g`) -/
theorem fb_lo {g o : ℝ} {l u Le su ou : ℕ} (hsu : su = u + ou) (hl : (l : ℝ) / SC ≤ g)
    (hs : (Le : ℝ) / SC ≤ g + o) (ho : o ≤ (ou : ℝ) / SC) :
    ((nmax l (Nat.sub Le (Nat.sub su u)) : ℕ) : ℝ) / SC ≤ g := by
  have e : Nat.sub su u = ou := by rw [Nat.sub_eq, hsu]; omega
  rw [e, nmax_eq, Nat.sub_eq]
  have hg0 : 0 ≤ g := le_trans (div_nonneg (Nat.cast_nonneg _) SC_pos.le) hl
  rcases le_total l (Le - ou) with h | h
  · rw [max_eq_right h]
    rcases le_total ou Le with h' | h'
    · rw [Nat.cast_sub h', sub_div]; linarith
    · rw [Nat.sub_eq_zero_of_le h']; simpa using hg0
  · rw [max_eq_left h]; exact hl

end AMW.Cert.PCell

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the tangent check with the one-point case (`L = U = p` and both slope claims present; the sizer's PLO code) -/
def tcheckP (R : ℕ × ℕ × List (List ℕ)) (L U p X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tcheck R L U p X EU ED) (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X)))
    (Nat.beq L U && Nat.beq L p)
def mokP (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (L U l1 l2 p1 p2 : ℕ) : Bool :=
  (Nat.beq l1 0 || tcheckP R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1))
    && (Nat.beq l2 0 || tcheckP R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2))

/-- `tangent_cert` with the one-point case: on `[p, p]` the tangent at `p` is `w` itself -/
theorem tangent_certP {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (L U p : ℕ)
    (h : tcheckP R L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    L ≤ p ∧ p ≤ U ∧ (lo32 (f p) : ℝ) / 10000000000 ≤ wfun ((p : ℝ) / SC) ∧
      (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) ∧
      1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) ∧
      wfun ((p : ℝ) / SC) + w1 ((p : ℝ) / SC) * (s - (p : ℝ) / SC) ≤ wfun s := by
  unfold tcheckP at h
  cases hc : (Nat.beq L U && Nat.beq L p)
  · rw [hc] at h; exact tangent_cert hD hpt hR L U p h s hs1 hs2
  rw [hc] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc h
  obtain ⟨hLU, hLp⟩ := hc
  subst hLU; subst hLp
  have hU1 := U1_posR
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hp := hpt L
  obtain ⟨-, hPq⟩ := hp.2.1 (by omega)
  obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  have hs : s = (L : ℝ) / SC := le_antisymm hs2 hs1
  refine ⟨le_rfl, le_rfl, hp.1, by linarith, by linarith, ?_⟩
  rw [hs, sub_self, mul_zero, add_zero]

/-- one pair term of a minorant leaf on the range `[L, U]`, expanded at an anchor `L0 ≤ L` (mvt-engine's `mterm_min`
with the expansion point moved below the range: the charges `(M − KU1)(p − L0)` absorb the shift) -/
theorem mterm_minA {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L0 L U Uc lc l1 l2 p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hsum : lc + l1 + l2 = 1024)
    (h1 : l1 = 0 ∨ tcheckP R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1) = true)
    (h2 : l2 = 0 ∨ tcheckP R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (l1 : ℝ) * ((lo32 (hi32 (f p1)) : ℝ) - 2000000000) + (l2 : ℝ) * ((lo32 (hi32 (f p2)) : ℝ) - 2000000000)
        ≤ 1000000000 * D ∧
      32768 * ((lc : ℝ) * (lb top bk L Uc : ℝ) + (l1 : ℝ) * (lo32 (f p1) : ℝ) + (l2 : ℝ) * (lo32 (f p2) : ℝ))
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * ((l1 : ℝ) * ((hi32 (hi32 (f p1)) : ℝ) - 2000000000) * ((p1 : ℝ) - L0)
          + (l2 : ℝ) * ((hi32 (hi32 (f p2)) : ℝ) - 2000000000) * ((p2 : ℝ) - L0))
        ≤ 327680000000000 * 1024 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hlbs := hlb L Uc s hs1 (hs2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hUc) (by norm_num [SC])))
  have hlbs' : (lb top bk L Uc : ℝ) ≤ 10000000000 * wfun s := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hlbs; linarith
  have tang : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheckP R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      ∃ dk : ℝ, (lk : ℝ) * ((lo32 (hi32 (f pk)) : ℝ) - 2000000000) ≤ 1000000000 * ((lk : ℝ) * dk) ∧
        32768 * ((lk : ℝ) * (lo32 (f pk) : ℝ)) + 327680000000000 * (((lk : ℝ) * dk) * (s - (L0 : ℝ) / 32768))
          + 10 * ((lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
          ≤ 327680000000000 * ((lk : ℝ) * wfun s) := by
    intro lk pk hk
    rcases hk with hk | hk
    · refine ⟨0, by rw [hk]; simp, by rw [hk]; simp⟩
    obtain ⟨hLp, hpU, hv, hP, hM, htan⟩ := tangent_certP hD hpt hR L U pk hk s hs1 hs2
    rw [hSC] at hv htan hM hP
    refine ⟨w1 ((pk : ℝ) / 32768), ?_, ?_⟩
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      nlinarith
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      have hv' : (lo32 (f pk) : ℝ) ≤ 10000000000 * wfun ((pk : ℝ) / 32768) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hv; linarith
      have hpL : (0 : ℝ) ≤ (pk : ℝ) - L0 := sub_nonneg.mpr (by exact_mod_cast hL0.trans hLp)
      have key : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
          + 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0)) ≤ 327680000000000 * wfun s := by
        have e1 : 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
            = 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
              + 10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0)) := by ring
        rw [e1]
        have h3 : 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
            ≤ -(10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0))) := by
          nlinarith [mul_le_mul_of_nonneg_right hM hpL]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left key hl0]
  obtain ⟨d1, hd1, hb1⟩ := tang l1 p1 h1
  obtain ⟨d2, hd2, hb2⟩ := tang l2 p2 h2
  refine ⟨(l1 : ℝ) * d1 + (l2 : ℝ) * d2, by linarith, ?_⟩
  have hsum' : (lc : ℝ) + l1 + l2 = 1024 := by exact_mod_cast hsum
  have hc0 : (0 : ℝ) ≤ lc := Nat.cast_nonneg _
  have hcl := mul_le_mul_of_nonneg_left hlbs' hc0
  have e2 : (327680000000000 : ℝ) * 1024 * wfun s
      = 327680000000000 * ((lc : ℝ) * wfun s) + 327680000000000 * ((l1 : ℝ) * wfun s)
        + 327680000000000 * ((l2 : ℝ) * wfun s) := by rw [← hsum']; ring
  rw [e2]
  nlinarith [hb1, hb2, hcl]

/-- one anchored minorant term from its side conditions (`mterm_ok` with the charges taken at `L0 ≤ L`) -/
theorem mterm_okA {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : mokP R tD bD f L U (mw1 κ lam) (mw2 κ lam) p1 p2 = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl f (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk f L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokP at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_minA hlb hD hpt hR L0 L U Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 hL0 hUc
    (mw_sum κ lam hl) h1 h2 s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheckP R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      (lk : ℝ) * (((hi32 (hi32 (f pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (f pk)) : ℕ) : ℝ))
        * ((pk - L0 : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (hL0.trans (tangent_certP hD hpt hR L U pk h s hs1 hs2).1)]
  have e1 := pk _ _ h1
  have e2 := pk _ _ h2
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

end AMW.Cert.PyrD

end
