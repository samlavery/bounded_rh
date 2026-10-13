import AMW.PCDF

/-! ###### polytope cells: coarse-first tangent sides (bridge-port, 2026-10-07)

A tangent's validity beyond its certified region `[za, zb]` is checked on `[zb, U]` (and on `[L, za]`). Here the far end
is first rounded out, `U` up and `L` down, to a multiple of `2^j` with `2^j` about `1/2^csh` of the side's length.
On the rounded side the derivative read is tried, then the zero-order pieces. Neighbouring leaves round to the same
end, so the kernel's cache shares these checks. When both fail, the exact alternatives of `tcheckZ` follow.

Each alternative is sound on its own. A read or a piece check on the longer side `[zb, uc] ⊇ [zb, U]` certifies the
tangent on `[zb, U]` (`tangent_valZC`). The leaf chain is restated once for any term check that yields the term
bound (`mcheckGX`, `mcheckGX_sound`), and the coarse-first check is one instance (`mokTZC`, `mtermTZC`). ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- `U` rounded up to a multiple of `2^j` -/
def rup (U j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight (Nat.add U (Nat.sub (Nat.shiftLeft 1 j) 1)) j) j
/-- `L` rounded down to a multiple of `2^j` -/
def rdn (L j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight L j) j

theorem le_rup (U j : ℕ) : U ≤ rup U j := by
  unfold rup
  simp only [Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.sub_eq,
    Nat.one_mul]
  have hp : 0 < 2 ^ j := by positivity
  have := Nat.lt_div_mul_add (a := U + (2 ^ j - 1)) hp
  omega

theorem rdn_le (L j : ℕ) : rdn L j ≤ L := by
  unfold rdn
  simp only [Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  exact Nat.div_mul_le_self L _

theorem zsideFG_eq (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) :
    zsideFG top bk v c p a b n right = zsideF top bk v c p a b n right := by
  simp only [zsideFG, zsideF, zsideG, zside, zpcF_eq]

/-- the tangent check with the coarse-first alternatives on each side -/
def tcheckZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
    Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k)
        || (forceB (blen (Nat.shiftRight (Nat.sub U (rgB R k)) csh)) fun jj => forceB (rup U jj) fun uc =>
             (Nat.ble 1 (lo32 (treadUF R tD bD uc p))
               && Nat.ble 4000000000 (Nat.add (lo32 (treadUF R tD bD uc p)) (hi32 (hi32 X))))
             || zsideFG top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) uc n true)
        || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X))))
        || zsideFG top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) U n true)
      && (Nat.ble (rgA R k) L
        || (forceB (blen (Nat.shiftRight (Nat.sub (rgA R k) L) csh)) fun jj => forceB (rdn L jj) fun lc =>
             (Nat.ble 1 (hi32 (treadDF R tD bD lc p))
               && Nat.ble 4000000000 (Nat.add (hi32 (treadDF R tD bD lc p)) (lo32 (hi32 X))))
             || zsideFG top bk (lo32 X) (lo32 (hi32 X)) p lc (rgA R k) n false)
        || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X))))
        || zsideFG top bk (lo32 X) (lo32 (hi32 X)) p L (rgA R k) n false)

/-- with the one-point case -/
def tcheckPZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) (tcheckZC R top bk tD bD n csh L U p X EU ED)
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) (Nat.beq L U && Nat.beq L p)

/-- the coarse-first check gives the value form -/
theorem tangent_valZC {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {n csh L U p : ℕ} (hn : 0 < n)
    (h : tcheckPZC R top bk tD bD n csh L U p (f p) (treadUF R tD bD U p) (treadDF R tD bD L p) = true) :
    TVal f L U p := by
  have hSC := SC_pos
  have hU1 := U1_posR
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have cast_le : ∀ {m n : ℕ}, m ≤ n → (m : ℝ) / SC ≤ (n : ℝ) / SC := fun hmn =>
    div_le_div_of_nonneg_right (by exact_mod_cast hmn) hSC.le
  unfold tcheckPZC at h
  cases hc : (Nat.beq L U && Nat.beq L p)
  case true =>
    rw [hc] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc h
    obtain ⟨hLU, hLp⟩ := hc
    subst hLU; subst hLp
    have hp := hpt L
    obtain ⟨-, hPq⟩ := hp.2.1 (by omega)
    obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨le_rfl, le_rfl, by linarith, by linarith, fun s hs1 hs2 => ?_⟩
    rw [le_antisymm hs2 hs1, sub_self, mul_zero, add_zero]; exact hp.1
  rw [hc] at h
  unfold tcheckZC at h
  simp only [forceB_eq, treadUF_eq, treadDF_eq, zsideFG_eq] at h
  unfold treadU treadD at h
  simp only [forceR_eq] at h
  set k := Nat.shiftRight (Nat.add p 16384) 15 with hkdef
  set uc := rup U (blen (Nat.shiftRight (Nat.sub U (rgB R k)) csh)) with huc
  set lc := rdn L (blen (Nat.shiftRight (Nat.sub (rgA R k) L) csh)) with hlc
  have hUuc : U ≤ uc := le_rup _ _
  have hlcL : lc ≤ L := rdn_le _ _
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hap⟩, hpb⟩, hLp⟩, hpU⟩, hP1⟩, hM1⟩, hup⟩, hdn⟩ := h
  have hp := hpt p
  obtain ⟨hkp, hPq⟩ := hp.2.1 (by omega)
  obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  have hP : (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) := by linarith
  have hM : 1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) := by linarith
  have hc := rg_conv hR hk (by omega)
  have hap' := cast_le hap
  have hpb' := cast_le hpb
  set za : ℝ := ((rgA R k : ℕ) : ℝ) / SC
  set zb : ℝ := ((rgB R k : ℕ) : ℝ) / SC
  set q : ℝ := (p : ℝ) / SC
  set v : ℝ := (lo32 (f p) : ℝ) / 10000000000
  have hv : v ≤ wfun q := hp.1
  -- inside the region: the exact tangent, by convexity
  have hmid : ∀ s, za ≤ s → s ≤ zb → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    have := ext_tangent (za := za) (zb := zb) (L := za) (U := zb) hc hap' hpb'
      (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
      (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
      hap' hpb' h1 h2
    linarith
  -- a derivative read on `[zb, E]` with `U ≤ E` (the exact `E = U`, or the coarse `E = uc`)
  have hderR : ∀ E : ℕ, U ≤ E → rgB R k < U →
      1 ≤ lo32 (lbDr tD bD (rgB R k) E) →
      4000000000 ≤ Nat.add (lo32 (lbDr tD bD (rgB R k) E)) (hi32 (hi32 (f p))) →
      ∀ s, zb ≤ s → s ≤ (U : ℝ) / SC → v + w1 q * (s - q) ≤ wfun s := by
    intro E hUE hbU he1 he2 s h1 h2
    have hR' : ∀ x : ℝ, zb ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ w1 q ≤ w1 x := by
      intro x hx1 hx2
      have hb := (hD _ E x hx1 (hx2.trans (cast_le hUE))).1 (by omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (lo32 (lbDr tD bD (rgB R k) E) : ℝ) + (hi32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith
    have := ext_tangent (za := za) (zb := zb) (L := za) (U := (U : ℝ) / SC) hc hap' hpb' hR'
      (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
      hap' (cast_le hpU) (le_trans hap' (le_trans hpb' h1)) h2
    linarith
  -- a derivative read on `[E, za]` with `E ≤ L`
  have hderL : ∀ E : ℕ, E ≤ L → L < rgA R k →
      1 ≤ hi32 (lbDr tD bD E (rgA R k)) →
      4000000000 ≤ Nat.add (hi32 (lbDr tD bD E (rgA R k))) (lo32 (hi32 (f p))) →
      ∀ s, (L : ℝ) / SC ≤ s → s ≤ za → v + w1 q * (s - q) ≤ wfun s := by
    intro E hEL hLa he1 he2 s h1 h2
    have hL' : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 q := by
      intro x hx1 hx2
      have hb := (hD E _ x ((cast_le hEL).trans hx1) hx2).2 (by omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte, Bool.false_eq_true] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (hi32 (lbDr tD bD E (rgA R k)) : ℝ) + (lo32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith
    have := ext_tangent (za := za) (zb := zb) (L := (L : ℝ) / SC) (U := zb) hc hap' hpb'
      (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
        by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
      hL' (cast_le hLp) hpb' h1 (le_trans h2 (le_trans hap' hpb'))
    linarith
  -- right of the region
  have hright : ∀ s, zb ≤ s → s ≤ (U : ℝ) / SC → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    rcases le_or_gt U (rgB R k) with hUb | hbU
    · exact hmid s (le_trans hap' (le_trans hpb' h1)) (le_trans h2 (cast_le hUb))
    have hbuc : rgB R k < uc := lt_of_lt_of_le hbU hUuc
    have nb1 : Nat.ble U (rgB R k) = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
    have nb2 : Nat.ble uc (rgB R k) = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
    rw [nb2] at hup
    rw [nb1] at hup
    rcases hup with (((hub | ⟨he1, he2⟩ | hz) | ⟨he1, he2⟩) | hz)
    · exact absurd hub (by omega)
    · exact hderR uc hUuc hbU he1 he2 s h1 h2
    · exact zsideF_right hlb hM hz hpb hbuc hn h1 (h2.trans (cast_le hUuc))
    · exact hderR U le_rfl hbU he1 he2 s h1 h2
    · exact zsideF_right hlb hM hz hpb hbU hn h1 h2
  -- left of the region
  have hleft : ∀ s, (L : ℝ) / SC ≤ s → s ≤ za → v + w1 q * (s - q) ≤ wfun s := by
    intro s h1 h2
    rcases le_or_gt (rgA R k) L with haL | hLa
    · exact hmid s (le_trans (cast_le haL) h1) (le_trans h2 (le_trans hap' hpb'))
    have hlca : lc < rgA R k := lt_of_le_of_lt hlcL hLa
    have nb1 : Nat.ble (rgA R k) L = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
    have nb2 : Nat.ble (rgA R k) lc = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
    rw [nb2] at hdn
    rw [nb1] at hdn
    rcases hdn with (((haL | ⟨he1, he2⟩ | hz) | ⟨he1, he2⟩) | hz)
    · exact absurd haL (by omega)
    · exact hderL lc hlcL hLa he1 he2 s h1 h2
    · exact zsideF_left hlb hP hz hap hlca hn ((cast_le hlcL).trans h1) h2
    · exact hderL L le_rfl hLa he1 he2 s h1 h2
    · exact zsideF_left hlb hP hz hap hLa hn h1 h2
  refine ⟨hLp, hpU, hP, hM, fun s hs1 hs2 => ?_⟩
  rcases le_total s za with h1 | h1
  · exact hleft s hs1 h1
  rcases le_total s zb with h2 | h2
  · exact hmid s h1 h2
  · exact hright s h2 hs2

/-- the side conditions of a term with the coarse-first check -/
def mokZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ)
    (n csh L U l1 l2 p1 p2 : ℕ) : Bool :=
  (Nat.beq l1 0 || tcheckPZC R top bk tD bD n csh L U p1 (f p1) (treadUF R tD bD U p1) (treadDF R tD bD L p1))
    && (Nat.beq l2 0 || tcheckPZC R top bk tD bD n csh L U p2 (f p2) (treadUF R tD bD U p2) (treadDF R tD bD L p2))

/-- one anchored minorant term with the coarse-first check (`mterm_okZ` with `mokZC`) -/
theorem mterm_okZC {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n)
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : mokZC R top bk tD bD f n csh L U (mw1 κ lam) (mw2 κ lam) p1 p2 = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl f (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk f L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn f L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokZC at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  have tv : ∀ (lk pk : ℕ),
      (lk = 0 ∨ tcheckPZC R top bk tD bD n csh L U pk (f pk) (treadUF R tD bD U pk) (treadDF R tD bD L pk) = true) →
      lk = 0 ∨ TVal f L U pk := fun lk pk h => h.imp id (tangent_valZC hlb hD hpt hR hn)
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_minV hlb L0 L U Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 hL0 hUc
    (mw_sum κ lam hl) (tv _ _ h1) (tv _ _ h2) s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal f L U pk) →
      (lk : ℝ) * (((hi32 (hi32 (f pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (f pk)) : ℕ) : ℝ))
        * ((pk - L0 : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (hL0.trans h.1)]
  have e1 := pk _ _ (tv _ _ h1)
  have e2 := pk _ _ (tv _ _ h2)
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

end AMW.Cert.PyrD

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- a term's side conditions with the coarse-first check -/
def mokTZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (zn csh L U k m p r : ℕ) :
    Bool :=
  Nat.ble m 1024 && mokZC R top bk tD bD f zn csh L U (mw1 k m) (mw2 k m) p r

/-- one anchored minorant term in the short forms, with the coarse-first check -/
theorem mtermTZC {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {zn csh : ℕ} (hzn : 0 < zn)
    (L0 L U k m p r : ℕ) (hL0 : L0 ≤ L) (hok : mokTZC R top bk tD bD f zn csh L U k m p r = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokTZC at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okZC hlb hD hpt hR hzn L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1 hok.2 s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

/-- the minorant leaf's check for any term check `ok`: box, every term's `ok` on its effective range, the main
inequality (`mcheckGZ` is the instance `ok = mokTZ …`) -/
def mcheckGX (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (Q : ℕ) (bs : List ℕ)
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
      (iall (fun n => ok (eL TS c n) (eU TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)) TS.length)
      (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) Q))

/-- the leaf is sound for any term check that gives each term's anchored bound -/
theorem mcheckGX_sound {ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ}
    (hok : ∀ (L0 L U k m p r : ℕ), L0 ≤ L → ok L U k m p r = true → ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
      ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
        32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
          + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s)
    {Q : ℕ} {PR : List (ℕ × ℕ)} {bs : List ℕ} {TS : List Term} {cN : ℕ} (hPR : PRok Q PR) (hTS : TSok Q PR TS)
    {c : Cl} {FS : List Term} {P S : List ℕ} {Cp Cm : ℕ} (hY : MulOKg Q PR c P S Cp Cm)
    (h : mcheckGX ok top bk f Q bs TS cN c FS P S Cp Cm = true) : CovBy Q PR (Pg cN Q bs TS) c := by
  intro g hg
  left
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

end AMW.Cert.PCell
