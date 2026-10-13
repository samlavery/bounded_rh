import AMW.DESlack

/-! ###### AMW/DEPInterface — Lemma P as a count-only hypothesis on the Lean object (bridge-port)

The zeros with ordinate in `(T, 2T]` are grouped by ordinate: `M_T(t) = Σ_{Im ρ = t} m_ρ` (`ordMult`), so an
off-line pair `{ρ, 1 − ρ̄}` (same ordinate) is one class of multiplicity `≥ 2`, and `ordSq Z T = Σ_t M_T(t)²`.
`LemmaPObj Z h₀ g₀`: `h₀ N + g₀ Σ_t M_T(t)² − ε N ≤ ‖Â_T‖_F²` eventually, for every `ε > 0` (Lemma P with the dip
certificate's count-only right side).  Since `Σ_t M_T(t)² ≥ 2N − N₀ˢ` (`ordSq_ge`: a class of total multiplicity
one is a simple zero on the line, by the reflection symmetry), `LemmaPObj` with `e₀ ≤ h₀ + g₀ + σ` gives the
defect-energy inequality with `δ = g₀/2` and slack `σ/2` (`defectEnergyS_of_lemmaP`), hence
`κ = 1 − (e∞ + σ/2)/(g₀/2)` (`AMW.am_dyadic_lemmaP`, `AMW.am_cumulative_lemmaP`).  `LemmaPObj` is a hypothesis of
these theorems throughout. ###### -/

noncomputable section

open Filter Topology Finset Classical
open Zeta23 RHLinalg

namespace Zeta23Ext.Bridge

/-- the zeros with ordinate in `(T, 2T]`, as a finset -/
def winFin (Z : ZeroConfig) (T : ℝ) : Finset ℂ := (Z.finite_window T (2 * T)).toFinset

/-- the total multiplicity of the zeros with ordinate `t` (in `(T, 2T]`) -/
def ordMult (Z : ZeroConfig) (T t : ℝ) : ℕ := ∑ ρ ∈ (winFin Z T).filter (fun ρ => ρ.im = t), Z.mult ρ

/-- `Σ_t M_T(t)²` over the ordinates in `(T, 2T]` -/
def ordSq (Z : ZeroConfig) (T : ℝ) : ℕ := ∑ t ∈ (winFin Z T).image Complex.im, ordMult Z T t ^ 2

/-- **Lemma P, count-only, on the Lean object** (a hypothesis) -/
def LemmaPObj (Z : ZeroConfig) (h0 g0 : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    h0 * (Z.N T (2 * T) : ℝ) + g0 * (ordSq Z T : ℝ) - ε * (Z.N T (2 * T) : ℝ)
      ≤ frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))

theorem mem_winFin {Z : ZeroConfig} {T : ℝ} {ρ : ℂ} :
    ρ ∈ winFin Z T ↔ ρ ∈ Z.carrier ∧ T < ρ.im ∧ ρ.im ≤ 2 * T := by
  unfold winFin
  rw [Set.Finite.mem_toFinset]
  rfl

theorem N_eq_sum_winFin (Z : ZeroConfig) (T : ℝ) :
    Z.N T (2 * T) = ∑ ρ ∈ winFin Z T, Z.mult ρ := by
  unfold ZeroConfig.N winFin
  exact finsum_mem_eq_finite_toFinset_sum _ (Z.finite_window T (2 * T))

theorem N0s_eq_card (Z : ZeroConfig) (T : ℝ) :
    Z.N0s T (2 * T) = ((winFin Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)).card := by
  unfold ZeroConfig.N0s
  have : Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple
      = ↑((winFin Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)) := by
    ext ρ
    simp only [Set.mem_inter_iff, coe_filter, Set.mem_setOf_eq, mem_winFin, ZeroConfig.window,
      ZeroConfig.onLine, ZeroConfig.simple]
    tauto
  rw [this, Set.ncard_coe_finset]

theorem reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by
  simp [reflect]

theorem reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by
  simp [reflect]

/-- one ordinate class: `2 M ≤ M² + #(simple on-line zeros in the class)` -/
theorem class_ineq (Z : ZeroConfig) (T t : ℝ) (ht : t ∈ (winFin Z T).image Complex.im) :
    2 * ordMult Z T t
      ≤ ordMult Z T t ^ 2
        + ((winFin Z T).filter (fun ρ => ρ.im = t ∧ (ρ.re = 1 / 2 ∧ Z.mult ρ = 1))).card := by
  obtain ⟨ρ, hρS, hρt⟩ := mem_image.mp ht
  have hρ := mem_winFin.mp hρS
  have hm1 : 1 ≤ Z.mult ρ := Z.one_le_mult ρ hρ.1
  have hρC : ρ ∈ (winFin Z T).filter (fun ρ => ρ.im = t) := mem_filter.mpr ⟨hρS, hρt⟩
  have hle : Z.mult ρ ≤ ordMult Z T t :=
    single_le_sum (f := fun ρ => Z.mult ρ) (fun _ _ => Nat.zero_le _) hρC
  by_cases h2 : 2 ≤ ordMult Z T t
  · nlinarith
  · have hM : ordMult Z T t = 1 := by omega
    have hmρ : Z.mult ρ = 1 := by omega
    -- the class's zero is on the line: otherwise its reflection is a second zero of the class
    have hre : ρ.re = 1 / 2 := by
      by_contra hne
      have hrS : reflect ρ ∈ winFin Z T := by
        refine mem_winFin.mpr ⟨Z.reflect_mem ρ hρ.1, ?_, ?_⟩ <;> rw [reflect_im]
        · exact hρ.2.1
        · exact hρ.2.2
      have hrC : reflect ρ ∈ (winFin Z T).filter (fun ρ => ρ.im = t) :=
        mem_filter.mpr ⟨hrS, by rw [reflect_im]; exact hρt⟩
      have hne' : reflect ρ ≠ ρ := by
        intro h
        apply hne
        have := congrArg Complex.re h
        rw [reflect_re] at this
        linarith
      have hpair : ({ρ, reflect ρ} : Finset ℂ) ⊆ (winFin Z T).filter (fun ρ => ρ.im = t) := by
        intro x hx
        rcases mem_insert.mp hx with h | h
        · rw [h]; exact hρC
        · rw [mem_singleton.mp h]; exact hrC
      have hsum := sum_le_sum_of_subset (f := fun ρ => Z.mult ρ) hpair
      rw [sum_pair hne'.symm, Z.mult_reflect ρ hρ.1] at hsum
      have : ordMult Z T t ≥ 2 := by unfold ordMult; omega
      omega
    have hcard : 1 ≤ ((winFin Z T).filter (fun ρ => ρ.im = t ∧ (ρ.re = 1 / 2 ∧ Z.mult ρ = 1))).card :=
      card_pos.mpr ⟨ρ, mem_filter.mpr ⟨hρS, hρt, hre, hmρ⟩⟩
    rw [hM]
    omega

/-- **the count**: `Σ_t M_T(t)² ≥ 2N − N₀ˢ` -/
theorem ordSq_ge (Z : ZeroConfig) (T : ℝ) :
    2 * Z.N T (2 * T) ≤ ordSq Z T + Z.N0s T (2 * T) := by
  set S := winFin Z T with hS
  have hmaps : ∀ ρ ∈ S, ρ.im ∈ S.image Complex.im := fun ρ hρ => mem_image_of_mem _ hρ
  have hN : Z.N T (2 * T) = ∑ t ∈ S.image Complex.im, ordMult Z T t := by
    rw [N_eq_sum_winFin]
    exact (sum_fiberwise_of_maps_to hmaps (fun ρ => Z.mult ρ)).symm
  have hN0 : Z.N0s T (2 * T)
      = ∑ t ∈ S.image Complex.im, (S.filter (fun ρ => ρ.im = t ∧ (ρ.re = 1 / 2 ∧ Z.mult ρ = 1))).card := by
    rw [N0s_eq_card, card_eq_sum_card_fiberwise (f := Complex.im) (t := S.image Complex.im)
      (fun ρ hρ => hmaps ρ (mem_filter.mp hρ).1)]
    refine sum_congr rfl fun t _ => ?_
    congr 1
    ext ρ
    simp only [mem_filter]
    tauto
  rw [hN, hN0, ordSq, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun t ht => class_ineq Z T t ht

/-- **Lemma P ⇒ the defect-energy inequality** with `δ = g₀/2` and slack `σ/2` -/
theorem defectEnergyS_of_lemmaP {Z : ZeroConfig} {h0 g0 σ : ℝ} (hP : LemmaPObj Z h0 g0) (hg0 : 0 ≤ g0)
    (hs : e0DE ≤ h0 + g0 + σ) : DefectEnergyS Z (g0 / 2) (σ / 2) := by
  intro ε hε
  filter_upwards [hP ε hε] with T h
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set Ns : ℝ := (Z.N0s T (2 * T) : ℝ) with hNsdef
  set F := frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) with hFdef
  have hc : 2 * N ≤ (ordSq Z T : ℝ) + Ns := by
    have := ordSq_ge Z T
    rw [hNdef, hNsdef]
    exact_mod_cast this
  have hNs0 : 0 ≤ Ns := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  unfold edE
  rw [← hFdef, ← hNdef]
  rcases eq_or_ne N 0 with h0' | h0'
  · rw [h0']
    have : 0 ≤ g0 / 2 * Ns := by positivity
    simp only [zero_sub, mul_neg, zero_mul, add_zero, zero_div, mul_zero]
    linarith
  · have hF : N * ((F / N - e0DE) / 2) = (F - e0DE * N) / 2 := by field_simp
    rw [hF]
    have hg : g0 * (2 * N - Ns) ≤ g0 * (ordSq Z T : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hg0
    have hεN : 0 ≤ ε * N := mul_nonneg hε.le hN0
    have hsN : e0DE * N ≤ (h0 + g0 + σ) * N := mul_le_mul_of_nonneg_right hs hN0
    nlinarith

end Zeta23Ext.Bridge

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge

/-- **the board's dyadic shape under Lemma P**: `κ ≤ 1 − (e∞ + σ/2)/(g₀/2)` -/
theorem am_dyadic_lemmaP {h0 g0 σ κ : ℝ} (hP : LemmaPObj zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  am_dyadic_defectS (by positivity) (defectEnergyS_of_lemmaP hP hg0.le hs) hκ

/-- the cumulative form -/
theorem am_cumulative_lemmaP {h0 g0 σ κ : ℝ} (hP : LemmaPObj zetaZeroConfig h0 g0) (hg0 : 0 < g0)
    (hs : e0DE ≤ h0 + g0 + σ) (hκ : κ ≤ 1 - (eInfDE + σ / 2) / (g0 / 2)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  am_cumulative_defectS (by positivity) (defectEnergyS_of_lemmaP hP hg0.le hs) hκ

end AMW

end
