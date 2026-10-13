import AMW.GConst
import AMW.GFar

/-!
# AMW/GNear — the near-pole terms (stage G)

At the anchor `k = 2 j₀` the term `sinc(π(x − j₀))` and its derivatives are read from Taylor polynomials at
`t = π |x − j₀| ∈ [TLZ, TUZ] / DZ ⊂ [0, 1]`, split into positive and negative parts (each increasing in `t ≥ 0`).
-/

noncomputable section

open Real

namespace AMW.G

/-- the generic near enclosure: integer polynomials `P`, `N` reading `DZ · Pr`, `DZ · Nr`, both increasing on
`[0, ∞)`, and `f` within `ε ≤ E / DZ` of `Pr − Nr` on `[0, 1]` -/
theorem near_enc {P N : ℕ → ℕ} {Pr Nr f : ℝ → ℝ} {DEN E : ℕ} (hDEN : 0 < DEN)
    (hP : ∀ T : ℕ, (P T : ℝ) / DEN = DZ * Pr ((T : ℝ) / DZ)) (hN : ∀ T : ℕ, (N T : ℝ) / DEN = DZ * Nr ((T : ℝ) / DZ))
    (hPm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Pr u ≤ Pr v) (hNm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Nr u ≤ Nr v)
    {ε : ℝ} (hε : ε ≤ (E : ℝ) / DZ) (herr : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |f u - (Pr u - Nr u)| ≤ ε)
    {TL TU : ℕ} {t : ℝ} (h0 : (TL : ℝ) / DZ ≤ t) (h1 : t ≤ (TU : ℝ) / DZ) (h2 : (TU : ℝ) / DZ ≤ 1) :
    (IV.mk ((SZ.fl ⟨P TL, N TU⟩ DEN).sub (SZ.ofN E)) ((SZ.ce ⟨P TU, N TL⟩ DEN).add (SZ.ofN E))).Enc (f t) := by
  have hD := DZ_pos
  have hTL0 : (0 : ℝ) ≤ (TL : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
  have ht0 : 0 ≤ t := hTL0.trans h0
  have hE := (abs_le.mp (herr t ht0 (h1.trans h2)))
  constructor
  · simp only [SZ.v_sub, SZ.v_ofN, sub_div]
    have f1 := SZ.v_fl_le ⟨P TL, N TU⟩ hDEN
    have e : (SZ.v ⟨P TL, N TU⟩) / DEN = DZ * Pr ((TL : ℝ) / DZ) - DZ * Nr ((TU : ℝ) / DZ) := by
      simp only [SZ.v]; rw [sub_div, hP, hN]
    rw [e] at f1
    have m1 := hPm _ _ hTL0 h0
    have m2 := hNm _ _ ht0 h1
    have : (SZ.fl ⟨P TL, N TU⟩ DEN).v / DZ ≤ Pr ((TL : ℝ) / DZ) - Nr ((TU : ℝ) / DZ) := by
      rw [div_le_iff₀ hD]; linarith
    linarith
  · simp only [SZ.v_add, SZ.v_ofN, add_div]
    have f1 := SZ.le_v_ce ⟨P TU, N TL⟩ hDEN
    have e : (SZ.v ⟨P TU, N TL⟩) / DEN = DZ * Pr ((TU : ℝ) / DZ) - DZ * Nr ((TL : ℝ) / DZ) := by
      simp only [SZ.v]; rw [sub_div, hP, hN]
    rw [e] at f1
    have m1 := hPm _ _ ht0 h1
    have m2 := hNm _ _ hTL0 h0
    have : Pr ((TU : ℝ) / DZ) - Nr ((TL : ℝ) / DZ) ≤ (SZ.ce ⟨P TU, N TL⟩ DEN).v / DZ := by
      rw [le_div_iff₀ hD]; linarith
    linarith

theorem pow_mono0 {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) : u ^ n ≤ v ^ n := pow_le_pow_left₀ hu huv n

/-! ## `sinc`, `sc1`, `sc2` -/

def Ps0 (u : ℝ) : ℝ := 1 + u ^ 4 / 120 + u ^ 8 / 362880
def Ns0 (u : ℝ) : ℝ := u ^ 2 / 6 + u ^ 6 / 5040 + u ^ 10 / 39916800
def Ps1 (u : ℝ) : ℝ := u ^ 3 / 30 + u ^ 7 / 45360
def Ns1 (u : ℝ) : ℝ := u / 3 + u ^ 5 / 840 + u ^ 9 / 3991680
def Ps2 (u : ℝ) : ℝ := u ^ 2 / 10 + u ^ 6 / 6480 + u ^ 10 / 39916800
def Ns2 (u : ℝ) : ℝ := 1 / 3 + u ^ 4 / 168 + u ^ 8 / 443520

theorem DZr : (DZ : ℝ) = 10 ^ 15 := by norm_num [DZ]

theorem scP_eq (T : ℕ) : (scP T : ℝ) / SCDEN = DZ * Ps0 ((T : ℝ) / DZ) := by
  unfold scP Ps0 SCDEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring
theorem scN_eq (T : ℕ) : (scN T : ℝ) / SCDEN = DZ * Ns0 ((T : ℝ) / DZ) := by
  unfold scN Ns0 SCDEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring
theorem s1P_eq (T : ℕ) : (s1P T : ℝ) / S1DEN = DZ * Ps1 ((T : ℝ) / DZ) := by
  unfold s1P Ps1 S1DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring
theorem s1N_eq (T : ℕ) : (s1N T : ℝ) / S1DEN = DZ * Ns1 ((T : ℝ) / DZ) := by
  unfold s1N Ns1 S1DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring
theorem s2P_eq (T : ℕ) : (s2P T : ℝ) / S2DEN = DZ * Ps2 ((T : ℝ) / DZ) := by
  unfold s2P Ps2 S2DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring
theorem s2N_eq (T : ℕ) : (s2N T : ℝ) / S2DEN = DZ * Ns2 ((T : ℝ) / DZ) := by
  unfold s2N Ns2 S2DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
  rw [DZr]; field_simp; ring

theorem tsinc_split (u : ℝ) : tsinc u = Ps0 u - Ns0 u := by unfold tsinc Ps0 Ns0; ring
theorem tsc1_split (u : ℝ) : tsc1 u = Ps1 u - Ns1 u := by unfold tsc1 Ps1 Ns1; ring
theorem tsc2_split (u : ℝ) : tsc2 u = Ps2 u - Ns2 u := by unfold tsc2 Ps2 Ns2; ring

namespace CellA
variable (c : CellA)

theorem near_t (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    (c.TLZ : ℝ) / DZ ≤ π * c.roff x ∧ π * c.roff x ≤ (c.TUZ : ℝ) / DZ ∧ (c.TUZ : ℝ) / DZ ≤ 1 :=
  let b := c.base_sound hc hx1 hx2; ⟨b.tlo, b.thi, b.t1⟩

theorem S0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.S0.Enc (Real.sinc (π * c.roff x)) := by
  obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
  unfold S0
  refine near_enc (by norm_num [SCDEN, DZ]) scP_eq scN_eq ?_ ?_ ERRD_ge ?_ h0 h1 h2
  · intro u v hu huv; unfold Ps0; gcongr
  · intro u v hu huv; unfold Ns0; gcongr
  · intro u hu0 hu1; rw [← tsinc_split]; exact abs_sinc_sub_tsinc_le (CellA.abs_le_one_of hu0 hu1)

theorem G1_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.G1.Enc (sc1 (π * c.roff x)) := by
  obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
  unfold G1
  have he : 2 * terr ≤ ((Nat.mul 2 ERRD : ℕ) : ℝ) / DZ := by rw [Nat.mul_eq]; push_cast; norm_num [terr, ERRD, DZ]
  refine near_enc (by norm_num [S1DEN, DZ]) s1P_eq s1N_eq ?_ ?_ he ?_ h0 h1 h2
  · intro u v hu huv; unfold Ps1; gcongr
  · intro u v hu huv; unfold Ns1; gcongr
  · intro u hu0 hu1; rw [← tsc1_split]; exact abs_sc1_sub_tsc1_le (CellA.abs_le_one_of hu0 hu1)

theorem G2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    c.G2.Enc (sc2 (π * c.roff x)) := by
  obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
  unfold G2
  have he : 5 * terr ≤ ((Nat.mul 5 ERRD : ℕ) : ℝ) / DZ := by rw [Nat.mul_eq]; push_cast; norm_num [terr, ERRD, DZ]
  refine near_enc (by norm_num [S2DEN, DZ]) s2P_eq s2N_eq ?_ ?_ he ?_ h0 h1 h2
  · intro u v hu huv; unfold Ps2; gcongr
  · intro u v hu huv; unfold Ns2; gcongr
  · intro u hu0 hu1; rw [← tsc2_split]; exact abs_sc2_sub_tsc2_le (CellA.abs_le_one_of hu0 hu1)

end CellA

end AMW.G
