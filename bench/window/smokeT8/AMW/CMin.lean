import AMW.CEngine

/-! ###### per-term minorants for the AM certificate (stage G): mvt-engine's MinCore (extended tangents at grid points,
certified once per pair term, combined convexly), on the AM engine cores. ###### -/
/-! ###### per-term minorants: extended tangents, certified once per pair term and combined convexly ######

A minorant leaf bounds each pair term on its range `[L, U]` by its own affine function, chosen by a linear programme
over the box: the zero-order constant, the tangent at a grid point `p`, or a convex combination of two of these.  The
tangent at `p` is a lower bound of `w` on `[L, U]` when `w` is convex on the certified region `[za, zb] ∋ p` and the
derivative table shows `w' ≥ w'(p)` on `[zb, U]` and `w' ≤ w'(p)` on `[L, za]`. -/

section MinDefs

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the side conditions of the tangent at the grid point `p` on the range `[L, U]`: `X` the point triple at `p`, `EU`
the derivative read on `[rgB k, U]`, `ED` the read on `[L, rgA k]`, `k` the region of the integer nearest to `p` -/
def tcheck (R : ℕ × ℕ × List (List ℕ)) (L U p X EU ED : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k) || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X)))))
      && (Nat.ble (rgA R k) L || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X)))))

/-- the upper derivative read of a tangent: on `[rgB k, U]` when `U` lies beyond the region, else nothing -/
def treadU (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDr tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
/-- the lower derivative read of a tangent: on `[L, rgA k]` when `L` lies before the region, else nothing -/
def treadD (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDr tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)

/-- the grid point `j ∈ [0, 8]` of the range `[L, U]`: `L + (U − L) j / 8` rounded down to a multiple of `256`, clamped to
the multiples of `256` inside `[L, U]` -/
def gpt (L U j : ℕ) : ℕ :=
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L 255) 8) 8) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U 8) 8) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) 8) 8) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the weights (out of `1024`) of a minorant term of kind `κ` (`1` tangent, `2` constant and tangent, `3` two tangents,
any other the constant) with weight field `lam`: on the constant, the first tangent, the second tangent -/
def mwc (κ lam : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 1024 0 (Nat.beq κ 3)) (Nat.sub 1024 lam) (Nat.beq κ 2))
    0 (Nat.beq κ 1)
def mw1 (κ lam : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.sub 1024 lam) (Nat.beq κ 3)) lam (Nat.beq κ 2))
    1024 (Nat.beq κ 1)
def mw2 (κ lam : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 lam (Nat.beq κ 3)

/-- a minorant term's value (units `1/(1024 U)`), its charges `(M − KU1)⁺(p − L)` and `(KU1 − M)⁺(p − L)`, its slope
claim `Σ l P` and slope weight `Σ l`, and its side conditions -/
def mval (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U c l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul c (lb top bk L U)) (Nat.add (Nat.mul l1 (lo32 (f p1))) (Nat.mul l2 (lo32 (f p2))))
def mcp (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul l1 (Nat.sub (hi32 (hi32 (f p1))) 2000000000)) (Nat.sub p1 L))
    (Nat.mul (Nat.mul l2 (Nat.sub (hi32 (hi32 (f p2))) 2000000000)) (Nat.sub p2 L))
def mcn (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul l1 (Nat.sub 2000000000 (hi32 (hi32 (f p1))))) (Nat.sub p1 L))
    (Nat.mul (Nat.mul l2 (Nat.sub 2000000000 (hi32 (hi32 (f p2))))) (Nat.sub p2 L))
def msl (f : ℕ → ℕ) (l1 l2 p1 p2 : ℕ) : ℕ := Nat.add (Nat.mul l1 (lo32 (hi32 (f p1)))) (Nat.mul l2 (lo32 (hi32 (f p2))))
def mok (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (L U l1 l2 p1 p2 : ℕ) : Bool :=
  (Nat.beq l1 0 || tcheck R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1))
    && (Nat.beq l2 0 || tcheck R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2))

end AMW.Cert.PyrD

end MinDefs

noncomputable section

namespace AMW.Cert

/-- on a convex interval `w'` is nondecreasing -/
theorem w1_mono_of_conv {za zb : ℝ} (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) {x y : ℝ}
    (hx : za ≤ x) (hxy : x ≤ y) (hy : y ≤ zb) : w1 x ≤ w1 y := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
    (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
    (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
  have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
  have hpos : 0 < y - x := by linarith
  have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
  nlinarith

/-- the extended tangent: the tangent at `p` is a lower bound of `wfun` on `[L, U]` when `w` is convex on `[za, zb] ∋ p`,
`w'` stays above `w'(p)` on `[zb, U]` and below it on `[L, za]` -/
theorem ext_tangent {za zb L U p : ℝ}
    (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) (hp1 : za ≤ p) (hp2 : p ≤ zb)
    (hR : ∀ x : ℝ, zb ≤ x → x ≤ U → kD x < 0 ∧ w1 p ≤ w1 x)
    (hL : ∀ x : ℝ, L ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 p)
    (hLp : L ≤ p) (hpU : p ≤ U) {s : ℝ} (hs1 : L ≤ s) (hs2 : s ≤ U) :
    wfun p + w1 p * (s - p) ≤ wfun s := by
  have hk : ∀ x, L ≤ x → x ≤ U → kD x < 0 := by
    intro x h1 h2
    rcases le_total x za with h | h
    · exact (hL x h1 h).1
    · rcases le_total x zb with h' | h'
      · exact (hc x h h').1
      · exact (hR x h' h2).1
  have hW : ∀ ξ, L ≤ ξ → ξ ≤ U → HasDerivAt wfun (w1 ξ) ξ := fun ξ h1 h2 => hasDerivAt_wfun ξ (hk ξ h1 h2).ne
  have hmono : ∀ x y, za ≤ x → x ≤ y → y ≤ zb → w1 x ≤ w1 y := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hxy with heq | hlt
    · rw [heq]
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
      (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
      (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
    have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
    have hpos : 0 < y - x := by linarith
    have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
    nlinarith
  have hge : ∀ ξ, p ≤ ξ → ξ ≤ U → w1 p ≤ w1 ξ := by
    intro ξ h1 h2
    rcases le_total ξ zb with h | h
    · exact hmono p ξ hp1 h1 h
    · exact (hR ξ h h2).2
  have hle : ∀ ξ, L ≤ ξ → ξ ≤ p → w1 ξ ≤ w1 p := by
    intro ξ h1 h2
    rcases le_total ξ za with h | h
    · exact (hL ξ h1 h).2
    · exact hmono ξ p h h2 hp2
  rcases lt_trichotomy p s with hps | hps | hps
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
      (fun y hy => (hW y (hLp.trans hy.1) (hy.2.trans hs2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hLp.trans hy.1.le) (hy.2.le.trans hs2))
    have h := hge ξ hξ.1.le (hξ.2.le.trans hs2)
    have hne : s - p ≠ 0 := by linarith
    have e : wfun s - wfun p = w1 ξ * (s - p) := by rw [hξe]; field_simp
    have hsp : 0 ≤ s - p := by linarith
    nlinarith
  · rw [hps]; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
      (fun y hy => (hW y (hs1.trans hy.1) (hy.2.trans hpU)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hs1.trans hy.1.le) (hy.2.le.trans hpU))
    have h := hle ξ (hs1.trans hξ.1.le) hξ.2.le
    have hne : p - s ≠ 0 := by linarith
    have e : wfun p - wfun s = w1 ξ * (p - s) := by rw [hξe]; field_simp
    have hsp : 0 ≤ p - s := by linarith
    nlinarith

end AMW.Cert

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- a nonempty certified region is convex -/
theorem rg_conv {R : ℕ × ℕ × List (List ℕ)} (hR : rgOk R = true) {k : ℕ} (hk : k < 16) (hab : rgA R k ≤ rgB R k) :
    ∀ x : ℝ, ((rgA R k : ℕ) : ℝ) / SC ≤ x → x ≤ ((rgB R k : ℕ) : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  intro x hx1 hx2
  have hk' := allBelow_spec hR _ hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
  rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
  · omega
  · set c := R.2.2.getD k [] with hc
    have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    exact chainOk_sound c _ hch hne x hx1 (by rw [hlast]; exact hx2)

/-- the tangent at the grid point `p` is a sound minorant on `[L, U]` once `tcheck` passes: `v / 10¹⁰ ≤ w(p)`, the slope
`w'(p)` inside the point claims, and `w(p) + w'(p)(s − p) ≤ w(s)` on the range -/
theorem tangent_cert {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (L U p : ℕ)
    (h : tcheck R L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    L ≤ p ∧ p ≤ U ∧ (lo32 (f p) : ℝ) / 10000000000 ≤ wfun ((p : ℝ) / SC) ∧
      (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) ∧
      1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) ∧
      wfun ((p : ℝ) / SC) + w1 ((p : ℝ) / SC) * (s - (p : ℝ) / SC) ≤ wfun s := by
  unfold tcheck at h
  rw [forceB_eq] at h
  unfold treadU treadD at h
  rw [forceR_eq, forceR_eq] at h
  set k := Nat.shiftRight (Nat.add p 16384) 15 with hkdef
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hap⟩, hpb⟩, hLp⟩, hpU⟩, hP⟩, hM⟩, hup⟩, hdn⟩ := h
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU1 := U1_posR
  have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
  have hp := hpt p
  have hq0 : lo32 (hi32 (f p)) ≠ 0 := by omega
  have hm0 : hi32 (hi32 (f p)) ≠ 0 := by omega
  obtain ⟨hkp, hPq⟩ := hp.2.1 hq0
  obtain ⟨-, hMq⟩ := hp.2.2 hm0
  simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
  rw [div_le_iff₀ hU1, eU] at hPq hMq
  have hc := rg_conv hR hk (by omega)
  set q : ℝ := (p : ℝ) / SC with hq
  have cast_le : ∀ {m n : ℕ}, m ≤ n → (m : ℝ) / SC ≤ (n : ℝ) / SC := fun hmn =>
    div_le_div_of_nonneg_right (by exact_mod_cast hmn) hSC.le
  refine ⟨hLp, hpU, hp.1, by linarith, by linarith, ?_⟩
  have hpb' := cast_le hpb; have hap' := cast_le hap
  refine ext_tangent (za := ((rgA R k : ℕ) : ℝ) / SC) (zb := ((rgB R k : ℕ) : ℝ) / SC) (L := (L : ℝ) / SC)
    (U := (U : ℝ) / SC) hc hap' hpb' ?_ ?_ (cast_le hLp) (cast_le hpU) hs1 hs2
  · intro x hx1 hx2
    by_cases hUb : U ≤ rgB R k
    · have hx : x ≤ ((rgB R k : ℕ) : ℝ) / SC := le_trans hx2 (cast_le hUb)
      have hxe : x = ((rgB R k : ℕ) : ℝ) / SC := le_antisymm hx hx1
      refine ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx).1, ?_⟩
      rw [hxe]; exact w1_mono_of_conv hc hap' hpb' le_rfl
    · have hb' : Nat.ble U (rgB R k) = false := Bool.eq_false_iff.mpr (fun h => hUb (Nat.le_of_ble_eq_true h))
      rcases hup with hu | ⟨he1, he2⟩
      · exact absurd hu hUb
      rw [hb'] at he1 he2
      have hb := (hD _ U x hx1 hx2).1 (by simp only at he1; omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (lo32 (lbDr tD bD (rgB R k) U) : ℝ) + (hi32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith
  · intro x hx1 hx2
    by_cases haL : rgA R k ≤ L
    · have hx : ((rgA R k : ℕ) : ℝ) / SC ≤ x := le_trans (cast_le haL) hx1
      have hxe : x = ((rgA R k : ℕ) : ℝ) / SC := le_antisymm hx2 hx
      refine ⟨(hc x hx (le_trans hx2 (le_trans hap' hpb'))).1, ?_⟩
      rw [hxe]; exact w1_mono_of_conv hc le_rfl hap' hpb'
    · have hb' : Nat.ble (rgA R k) L = false := Bool.eq_false_iff.mpr (fun h => haL (Nat.le_of_ble_eq_true h))
      rcases hdn with hd | ⟨he1, he2⟩
      · exact absurd hd haL
      rw [hb'] at he1 he2
      have hb := (hD L _ x hx1 hx2).2 (by simp only at he1; omega)
      obtain ⟨hkx, hbx⟩ := hb
      simp only [fD, ↓reduceIte, Bool.false_eq_true] at hbx
      rw [div_le_iff₀ hU1, eU] at hbx
      refine ⟨hkx, ?_⟩
      have : (4000000000 : ℝ) ≤ (hi32 (lbDr tD bD L (rgA R k)) : ℝ) + (lo32 (hi32 (f p)) : ℝ) := by
        simp only [Nat.add_eq] at he2; exact_mod_cast he2
      linarith

/-- one pair term of a minorant leaf: the convex combination (weights `lc`, `l1`, `l2` summing to `1024`) of the
zero-order constant and the tangents at `p1`, `p2`, at scale `SC·U`; `D` is `1024` times the combined slope -/
theorem mterm_min {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L U lc l1 l2 p1 p2 : ℕ) (hsum : lc + l1 + l2 = 1024)
    (h1 : l1 = 0 ∨ tcheck R L U p1 (f p1) (treadU R tD bD U p1) (treadD R tD bD L p1) = true)
    (h2 : l2 = 0 ∨ tcheck R L U p2 (f p2) (treadU R tD bD U p2) (treadD R tD bD L p2) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (l1 : ℝ) * ((lo32 (hi32 (f p1)) : ℝ) - 2000000000) + (l2 : ℝ) * ((lo32 (hi32 (f p2)) : ℝ) - 2000000000)
        ≤ 1000000000 * D ∧
      32768 * ((lc : ℝ) * (lb top bk L U : ℝ) + (l1 : ℝ) * (lo32 (f p1) : ℝ) + (l2 : ℝ) * (lo32 (f p2) : ℝ))
        + 327680000000000 * (D * (s - (L : ℝ) / 32768))
        + 10 * ((l1 : ℝ) * ((hi32 (hi32 (f p1)) : ℝ) - 2000000000) * ((p1 : ℝ) - L)
          + (l2 : ℝ) * ((hi32 (hi32 (f p2)) : ℝ) - 2000000000) * ((p2 : ℝ) - L))
        ≤ 327680000000000 * 1024 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hlbs := hlb L U s hs1 hs2
  have hlbs' : (lb top bk L U : ℝ) ≤ 10000000000 * wfun s := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hlbs; linarith
  -- each tangent with nonzero weight, as an inequality at scale SC·U
  have tang : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheck R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      ∃ dk : ℝ, (lk : ℝ) * ((lo32 (hi32 (f pk)) : ℝ) - 2000000000) ≤ 1000000000 * ((lk : ℝ) * dk) ∧
        32768 * ((lk : ℝ) * (lo32 (f pk) : ℝ)) + 327680000000000 * (((lk : ℝ) * dk) * (s - (L : ℝ) / 32768))
          + 10 * ((lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L))
          ≤ 327680000000000 * ((lk : ℝ) * wfun s) := by
    intro lk pk hk
    rcases hk with hk | hk
    · refine ⟨0, by rw [hk]; simp, by rw [hk]; simp⟩
    obtain ⟨hLp, hpU, hv, hP, hM, htan⟩ := tangent_cert hD hpt hR L U pk hk s hs1 hs2
    rw [hSC] at hv htan hM hP
    refine ⟨w1 ((pk : ℝ) / 32768), ?_, ?_⟩
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      nlinarith
    · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
      have hv' : (lo32 (f pk) : ℝ) ≤ 10000000000 * wfun ((pk : ℝ) / 32768) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hv; linarith
      have hpL : (0 : ℝ) ≤ (pk : ℝ) - L := sub_nonneg.mpr (by exact_mod_cast hLp)
      -- the tangent at p, rewritten from s - p to (s - L) + (L - p), with the slope above by M
      have key : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L : ℝ) / 32768))
          + 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L)) ≤ 327680000000000 * wfun s := by
        have e1 : 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L : ℝ) / 32768))
            = 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
              + 10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L)) := by ring
        rw [e1]
        have h3 : 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L))
            ≤ -(10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L))) := by
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

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem mw_sum (κ lam : ℕ) (hl : lam ≤ 1024) : mwc κ lam + mw1 κ lam + mw2 κ lam = 1024 := by
  unfold mwc mw1 mw2
  by_cases h1 : κ = 1
  · subst h1; simp only [show Nat.beq 1 1 = true from rfl, show Nat.beq 1 2 = false from rfl, show Nat.beq 1 3 = false from rfl]
  · rw [beq_false h1]
    by_cases h2 : κ = 2
    · subst h2
      simp only [show Nat.beq 2 2 = true from rfl, show Nat.beq 2 3 = false from rfl, Nat.sub_eq]; omega
    · rw [beq_false h2]
      by_cases h3 : κ = 3
      · subst h3; simp only [show Nat.beq 3 3 = true from rfl, Nat.sub_eq]; omega
      · rw [beq_false h3]; rfl

theorem natsub_pair (M : ℕ) : ((M - 2000000000 : ℕ) : ℝ) - ((2000000000 - M : ℕ) : ℝ) = (M : ℝ) - 2000000000 := by
  rcases le_total M 2000000000 with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring

/-- one minorant term from its side conditions -/
theorem mterm_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L U κ lam p1 p2 : ℕ) (hl : lam ≤ 1024)
    (hok : mok R tD bD f L U (mw1 κ lam) (mw2 κ lam) p1 p2 = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl f (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk f L U (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L : ℝ) / 32768))
        + 10 * (mcp f L (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn f L (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  unfold mok at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_min hlb hD hpt hR L U (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 (mw_sum κ lam hl)
    h1 h2 s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ tcheck R L U pk (f pk) (treadU R tD bD U pk) (treadD R tD bD L pk) = true) →
      (lk : ℝ) * (((hi32 (hi32 (f pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (f pk)) : ℕ) : ℝ))
        * ((pk - L : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (tangent_cert hD hpt hR L U pk h s hs1 hs2).1]
  have e1 := pk _ _ h1
  have e2 := pk _ _ h2
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

/-- one gap's linear part: `E (g − l)` on `g − l ∈ [0, H/SC]` with `10⁹ E ≥ −N` -/
theorem gap_lo {E e H N : ℝ} (hN : 0 ≤ N) (hE : -N ≤ 1000000000 * E) (he0 : 0 ≤ e) (he1 : e ≤ H / 32768) :
    -(10 * (N * H)) ≤ 327680000000000 * (E * e) := by
  have hH : 0 ≤ H := by linarith
  rcases le_total 0 E with h | h
  · have : 0 ≤ E * e := mul_nonneg h he0
    nlinarith
  · have h1 : E * e ≥ E * (H / 32768) := by nlinarith
    nlinarith

theorem brec_ne {b : Bool} {x : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 x b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

end AMW.Cert.PyrD

end
