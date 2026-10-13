import AMW.DEObj

/-! ###### AMW/DEObjMain — Lemma P on the Lean object for on-line windows (bridge-port)

If every zero of `𝒵(I')` is on the line for large `T`, the count-only Lemma P holds on the Lean object with the
dip certificate's constants: `LemmaPObj Z (qf(0) − y₀) (g(0))` (`lemmaPObj_online`).  This instance shows that the
interface `LemmaPObj` is inhabited; it is conditional on the window zeros being on the line.

Proof: `‖Â‖_F² = Σ m m' K_T²` (`frob_hat_Az_online`); keep the intra-block pairs of the bulk (`block_bound`, blocks of
normalised length `Λ`); `K_T` is within `δ_T = O(1/L)` of `kfun` (`kernel_close_real`); the block masses satisfy
`Σ_j n_j² ≥ N_bulk²/J` (Cauchy–Schwarz) with `J ≲ (1 + κ₀/2) N/Λ` (`growth`); `Σ_bulk m² ≤ 4(1/c∞ + 1) N` from the
diagonal and `frobAz_le`; the walls are `o(N)`.  The bookkeeping is `final_algebra`; one height is
`online_at_T`. ###### -/

noncomputable section

open Finset Real Filter Topology Asymptotics RHLinalg
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

open Classical

/-! ### Bookkeeping -/

theorem fa_Q2 {κ κ₀ Λ N NS Q2 Jr W : ℝ} (hκ0 : 0 ≤ κ) (hκκ₀ : κ ≤ κ₀ / 4) (hκ₀ : 0 ≤ κ₀)
    (hκ₀16 : κ₀ ≤ 1 / 16) (hΛ : 0 < Λ) (hN0 : 0 ≤ N) (hcount : N ≤ NS + W) (hwall : W ≤ κ * N)
    (hCS : NS ^ 2 ≤ Jr * Q2) (hJ : 0 < Jr) (hJle : Jr ≤ (1 + κ₀ / 2) * N / Λ) :
    (1 - κ₀) * Λ * N ≤ Q2 := by
  have hκ1 : 0 ≤ 1 - κ := by linarith
  have hNS : (1 - κ) * N ≤ NS := by linarith [mul_comm κ N]
  have hsq : ((1 - κ) * N) ^ 2 ≤ NS ^ 2 := pow_le_pow_left₀ (mul_nonneg hκ1 hN0) hNS 2
  have hpoly : (1 - κ₀) * (1 + κ₀ / 2) ≤ (1 - κ) ^ 2 := by nlinarith
  have hJN : (1 - κ₀) * Λ * N * Jr ≤ (1 - κ₀) * (1 + κ₀ / 2) * N ^ 2 := by
    have h1κ₀ : 0 ≤ 1 - κ₀ := by linarith
    have h := mul_le_mul_of_nonneg_left hJle (show 0 ≤ (1 - κ₀) * Λ * N by positivity)
    calc (1 - κ₀) * Λ * N * Jr ≤ (1 - κ₀) * Λ * N * ((1 + κ₀ / 2) * N / Λ) := h
      _ = (1 - κ₀) * (1 + κ₀ / 2) * N ^ 2 := by field_simp
  have h2 : (1 - κ₀) * (1 + κ₀ / 2) * N ^ 2 ≤ (1 - κ) ^ 2 * N ^ 2 :=
    mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)
  have h3 : ((1 - κ) * N) ^ 2 = (1 - κ) ^ 2 * N ^ 2 := by ring
  have hchain : Jr * ((1 - κ₀) * Λ * N) ≤ Jr * Q2 := by linarith
  exact le_of_mul_le_mul_left hchain hJ

theorem fa_poly {κ₀ η : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ₀16 : κ₀ ≤ 1 / 16) (hη0 : 0 ≤ η) (hηκ : η ≤ κ₀) :
    1 - 4 * κ₀ ≤ (1 - κ₀) ^ 2 * (1 - η) * (1 - κ₀) := by
  nlinarith [mul_nonneg hκ₀ hκ₀, mul_nonneg (mul_nonneg hκ₀ hκ₀) hκ₀, mul_nonneg hκ₀ hη0,
    mul_nonneg (mul_nonneg hκ₀ hκ₀) hη0, mul_nonneg (mul_nonneg (mul_nonneg hκ₀ hκ₀) hκ₀) hη0]

theorem fa_frac {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : b * (a / (8 * (b + 1))) ≤ a / 8 := by
  rw [show b * (a / (8 * (b + 1))) = a / 8 * (b / (b + 1)) by field_simp]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))

theorem fa_main {h0 ε κ₀ η ε₁ Λ R Qδ N Q2 : ℝ} (hε : 0 < ε) (hh0 : 0 < h0) (hκ₀ : 0 < κ₀)
    (hκ₀16 : κ₀ ≤ 1 / 16) (hκ₀ε : κ₀ ≤ ε / (16 * (h0 + 1))) (hη : 0 < η) (hη12 : η ≤ 1 / 2) (hηκ : η ≤ κ₀)
    (hε₁0 : 0 ≤ ε₁) (hε₁ε : ε₁ ≤ ε / 8) (hε₁h : ε₁ ≤ h0 / 8) (hΛpos : 0 < Λ) (hR : 0 < R)
    (hRΛ : R ≤ κ₀ * Λ)
    (hQδ0 : 0 ≤ Qδ) (hQδ2 : Qδ ≤ 1 / 2) (hQδκ : Qδ ≤ κ₀ * η * ((1 - η) * (h0 - ε₁) / (Λ + R)))
    (hN0 : 0 ≤ N) (hQ2 : (1 - κ₀) * Λ * N ≤ Q2) :
    (h0 - 3 * ε / 8) * N ≤ ((1 - η) * (h0 - ε₁) / (Λ + R) - Qδ ^ 2 / η) * Q2 := by
  set h0' := h0 - ε₁ with hh0'def
  have hh0' : 0 < h0' := by rw [hh0'def]; linarith
  have h1η : 0 ≤ 1 - η := by linarith
  have h1κ₀ : 0 ≤ 1 - κ₀ := by linarith
  set X := (1 - η) * h0' / (Λ + R) with hX
  have hX0 : 0 ≤ X := by positivity
  have hQQ : Qδ ^ 2 ≤ Qδ := by
    calc Qδ ^ 2 = Qδ * Qδ := sq _
      _ ≤ Qδ * 1 := mul_le_mul_of_nonneg_left (by linarith) hQδ0
      _ = Qδ := mul_one _
  have hQ2δ : Qδ ^ 2 / η ≤ κ₀ * X := by
    rw [div_le_iff₀ hη]
    have : κ₀ * η * X = κ₀ * X * η := by ring
    linarith
  have hβ : (1 - κ₀) * X ≤ X - Qδ ^ 2 / η := by linarith
  have hβ0 : 0 ≤ (1 - κ₀) * X := mul_nonneg h1κ₀ hX0
  have hΛR : (1 - κ₀) ≤ Λ / (Λ + R) := by
    rw [le_div_iff₀ (by linarith)]
    have : (1 - κ₀) * R ≤ R := mul_le_of_le_one_left hR.le (by linarith)
    have e : (1 - κ₀) * (Λ + R) = Λ - κ₀ * Λ + (1 - κ₀) * R := by ring
    linarith
  have s1 : (1 - κ₀) * X * ((1 - κ₀) * Λ * N) ≤ (X - Qδ ^ 2 / η) * Q2 :=
    mul_le_mul hβ hQ2 (by positivity) (hβ0.trans hβ)
  have s2 : (1 - κ₀) * X * ((1 - κ₀) * Λ * N) = (1 - κ₀) ^ 2 * (1 - η) * h0' * (Λ / (Λ + R)) * N := by
    rw [hX]; field_simp
  have hA : 0 ≤ (1 - κ₀) ^ 2 * (1 - η) * h0' := by positivity
  have s3 : (1 - κ₀) ^ 2 * (1 - η) * h0' * (1 - κ₀) * N
      ≤ (1 - κ₀) ^ 2 * (1 - η) * h0' * (Λ / (Λ + R)) * N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛR hA) hN0
  have s4 : (1 - 4 * κ₀) * h0' ≤ (1 - κ₀) ^ 2 * (1 - η) * h0' * (1 - κ₀) := by
    have := mul_le_mul_of_nonneg_right (fa_poly hκ₀.le hκ₀16 hη.le hηκ) hh0'.le
    have e : (1 - κ₀) ^ 2 * (1 - η) * (1 - κ₀) * h0' = (1 - κ₀) ^ 2 * (1 - η) * h0' * (1 - κ₀) := by ring
    linarith
  have s5 : h0 - 3 * ε / 8 ≤ (1 - 4 * κ₀) * h0' := by
    have h4κ : 4 * κ₀ * h0 ≤ ε / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hκ₀ε (show 0 ≤ 4 * h0 by linarith)
      have e : 4 * h0 * (ε / (16 * (h0 + 1))) = ε / 4 * (h0 / (h0 + 1)) := by field_simp; ring
      have hfrac : h0 / (h0 + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have h2 : ε / 4 * (h0 / (h0 + 1)) ≤ ε / 4 := mul_le_of_le_one_right (by linarith) hfrac
      have e2 : 4 * κ₀ * h0 = 4 * h0 * κ₀ := by ring
      linarith
    have h3 : 4 * κ₀ * h0' ≤ 4 * κ₀ * h0 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : (1 - 4 * κ₀) * h0' = h0' - 4 * κ₀ * h0' := by ring
    linarith
  have s6 : (h0 - 3 * ε / 8) * N ≤ (1 - 4 * κ₀) * h0' * N := mul_le_mul_of_nonneg_right s5 hN0
  have s7 : (1 - 4 * κ₀) * h0' * N ≤ (1 - κ₀) ^ 2 * (1 - η) * h0' * (1 - κ₀) * N :=
    mul_le_mul_of_nonneg_right s4 hN0
  linarith

/-- the bookkeeping of the on-line instance -/
theorem final_algebra {h0 g0 ε κ₀ η ε₁ Λ R Qδ κ C₁ N NS SS Q2 Jr F ord W : ℝ}
    (hε : 0 < ε) (hh0 : 0 < h0) (hg0 : 0 ≤ g0) (hκ₀ : 0 < κ₀) (hκ₀16 : κ₀ ≤ 1 / 16)
    (hκ₀ε : κ₀ ≤ ε / (16 * (h0 + 1)))
    (hη : 0 < η) (hη12 : η ≤ 1 / 2) (hηκ : η ≤ κ₀) (hηg : η ≤ ε / (8 * (g0 * C₁ + 1))) (hC₁ : 0 ≤ C₁)
    (hε₁0 : 0 ≤ ε₁) (hε₁ε : ε₁ ≤ ε / 8) (hε₁h : ε₁ ≤ h0 / 8)
    (hΛpos : 0 < Λ) (hR : 0 < R) (hRΛ : R ≤ κ₀ * Λ)
    (hQδ0 : 0 ≤ Qδ) (hQδ2 : Qδ ≤ 1 / 2) (hQδκ : Qδ ≤ κ₀ * η * ((1 - η) * (h0 - ε₁) / (Λ + R)))
    (hκ : 0 < κ) (hκκ₀ : κ ≤ κ₀ / 4) (hκε : κ ≤ ε / (8 * (g0 + 1)))
    (hN0 : 0 ≤ N) (hSS0 : 0 ≤ SS)
    (hbb : ((1 - η) * (h0 - ε₁) / (Λ + R) - Qδ ^ 2 / η) * Q2 + (1 - η) * g0 * SS ≤ F)
    (hSS : SS ≤ C₁ * N) (hCS : NS ^ 2 ≤ Jr * Q2) (hJpos : 0 < Jr) (hJle : Jr ≤ (1 + κ₀ / 2) * N / Λ)
    (hcount : N ≤ NS + W) (hwall : W ≤ κ * N) (hwall2 : W ^ 2 ≤ κ * N) (hord : ord ≤ SS + W ^ 2) :
    h0 * N + g0 * ord - ε * N ≤ F := by
  have hQ2 := fa_Q2 hκ.le hκκ₀ hκ₀.le hκ₀16 hΛpos hN0 hcount hwall hCS hJpos hJle
  have hmain := fa_main hε hh0 hκ₀ hκ₀16 hκ₀ε hη hη12 hηκ hε₁0 hε₁ε hε₁h hΛpos hR hRΛ hQδ0 hQδ2 hQδκ hN0 hQ2
  -- the multiplicity terms
  have hg1 : g0 * SS - ε / 8 * N ≤ (1 - η) * g0 * SS := by
    have hgC : 0 ≤ g0 * C₁ := mul_nonneg hg0 hC₁
    have h2 : η * (g0 * C₁) ≤ ε / 8 := by
      have h5 := mul_le_mul_of_nonneg_left hηg hgC
      have h6 := fa_frac hε.le hgC
      have e : η * (g0 * C₁) = g0 * C₁ * η := by ring
      linarith
    have h1 : η * g0 * SS ≤ η * g0 * (C₁ * N) := mul_le_mul_of_nonneg_left hSS (by positivity)
    have h3 : η * g0 * (C₁ * N) = η * (g0 * C₁) * N := by ring
    have h4 : η * (g0 * C₁) * N ≤ ε / 8 * N := mul_le_mul_of_nonneg_right h2 hN0
    have e : (1 - η) * g0 * SS = g0 * SS - η * g0 * SS := by ring
    linarith
  have hg2 : g0 * ord - ε / 8 * N ≤ g0 * SS := by
    have h1 : g0 * ord ≤ g0 * (SS + W ^ 2) := mul_le_mul_of_nonneg_left hord hg0
    have h4 : g0 * κ ≤ ε / 8 := by
      have h5 := mul_le_mul_of_nonneg_left hκε hg0
      have h6 := fa_frac hε.le hg0
      linarith
    have h3 : g0 * W ^ 2 ≤ g0 * (κ * N) := mul_le_mul_of_nonneg_left hwall2 hg0
    have h7 : g0 * (κ * N) = g0 * κ * N := by ring
    have h8 : g0 * κ * N ≤ ε / 8 * N := mul_le_mul_of_nonneg_right h4 hN0
    have e : g0 * (SS + W ^ 2) = g0 * SS + g0 * W ^ 2 := by ring
    linarith
  have hεN : 0 ≤ ε * N := mul_nonneg hε.le hN0
  linarith

/-! ### One height -/

set_option maxHeartbeats 800000 in
/-- the on-line inequality at one height `T`, from the facts that hold eventually -/
theorem online_at_T (Z : ZeroConfig) (c : AMW.DE.PLCert) (hD : 0 < c.DkInv)
    (hG : AMW.DE.CertGNonneg c) (hH : AMW.DE.CertHNonneg c)
    {ε κ₀ η ε₁ Λ R Qδ κ cinv : ℝ} (hε : 0 < ε) (hh0pos : 0 < AMW.DE.qfAM 0 - c.y 0)
    (hκ₀ : 0 < κ₀) (hκ₀16 : κ₀ ≤ 1 / 16) (hκ₀ε : κ₀ ≤ ε / (16 * (AMW.DE.qfAM 0 - c.y 0 + 1)))
    (hη : 0 < η) (hη12 : η ≤ 1 / 2) (hηκ : η ≤ κ₀)
    (hηg : η ≤ ε / (8 * (AMW.DE.gPL c 0 * (4 * (cinv + 1)) + 1))) (hcinv : 0 < cinv)
    (hε₁0 : 0 ≤ ε₁) (hε₁ε : ε₁ ≤ ε / 8) (hε₁h : ε₁ ≤ (AMW.DE.qfAM 0 - c.y 0) / 8)
    (hR : ∀ (ι : Type) (s : Finset ι) (m x : ι → ℝ) (W : ℝ), 0 ≤ W → (∀ a, 0 ≤ m a) →
      (∀ a ∈ s, 0 ≤ x a ∧ x a ≤ W) →
      (AMW.DE.qfAM 0 - c.y 0 - ε₁) * (∑ a ∈ s, m a) ^ 2 / (W + R) + AMW.DE.gPL c 0 * ∑ a ∈ s, m a ^ 2
        ≤ ∑ a ∈ s, ∑ b ∈ s, m a * m b * AMW.wfunAM (x a - x b))
    (hΛpos : 0 < Λ) (hRpos : 0 < R) (hRΛ : R ≤ κ₀ * Λ)
    (hQδ : 0 < Qδ) (hQδ2 : Qδ ≤ 1 / 2)
    (hQδκ : Qδ ≤ κ₀ * η * ((1 - η) * (AMW.DE.qfAM 0 - c.y 0 - ε₁) / (Λ + R)))
    (hκ : 0 < κ) (hκκ₀ : κ ≤ κ₀ / 4) (hκε : κ ≤ ε / (8 * (AMW.DE.gPL c 0 + 1)))
    (hP : (paramsOf stdProfile 1).Valid) {T : ℝ}
    (hon' : ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) (hT : 0 < T)
    (h8 : 8 * (paramsOf stdProfile 1).w ≤ (paramsOf stdProfile 1).L T)
    (h32 : 32 * (paramsOf stdProfile 1).w ≤ (paramsOf stdProfile 1).L T)
    (hF : PrimeSide.LocalHypsCoreW (AMW.cAMW (paramsOf stdProfile 1).ϱ) ((paramsOf stdProfile 1).toSetting T)
      (AMW.lfW (paramsOf stdProfile 1) (AMW.WAM (paramsOf stdProfile 1)) T))
    (hL1 : 1 ≤ (paramsOf stdProfile 1).L T)
    (hδ : 10 * (AMW.cAMW (paramsOf stdProfile 1).ϱ / (paramsOf stdProfile 1).w) ^ 2 / (paramsOf stdProfile 1).L T ^ 4
      + 12 * (paramsOf stdProfile 1).w / (paramsOf stdProfile 1).L T ≤ Qδ)
    (hfrob : frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) ≤ (cinv + 1) * (Z.N T (2 * T) : ℝ))
    (hwall : wallN Z T ≤ κ * Z.N T (2 * T)) (hwall2 : wallN Z T ^ 2 ≤ κ * Z.N T (2 * T))
    (hdN : ((mtParams T).d T : ℝ) ≤ (1 + κ) * Z.N T (2 * T))
    (hNΛ : 4 * Λ / κ₀ ≤ (Z.N T (2 * T) : ℝ)) :
    (AMW.DE.qfAM 0 - c.y 0) * (Z.N T (2 * T) : ℝ) + AMW.DE.gPL c 0 * (ordSq Z T : ℝ)
      - ε * (Z.N T (2 * T) : ℝ) ≤ frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) := by
  set Pt := mtParams T with hPt
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
  have hLpos : 0 < L := by linarith
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hreal : PhiHatReal T Pt := phiHatReal_atAM hP T
  have hfrobeq := frob_hat_Az_online hreal hon'
  set S := bulkFin Z Pt T with hS
  set I := ZI Z T with hI
  set m : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) with hm
  set x : ℂ → ℝ := fun ρ => xr Pt T ρ.im with hx
  set Kt : ℂ → ℂ → ℝ := fun ρ ρ' => KT Pt T ρ.im ρ'.im with hKt
  set d : ℝ := (Pt.d T : ℝ) with hd
  set J : ℕ := ⌊(d - 2 * L ^ 2) / Λ⌋₊ + 1 with hJ
  have hSI : S ⊆ I := (bulkFin_subset Z Pt T).trans (winFin_subset_ZI Z T)
  have hSmem : ∀ ρ ∈ S, L ^ 2 ≤ x ρ ∧ x ρ ≤ d - L ^ 2 := fun ρ hρ => (mem_filter.mp hρ).2
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hSx : ∀ ρ ∈ S, L ^ 2 ≤ x ρ ∧ ⌊(x ρ - L ^ 2) / Λ⌋₊ < J := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hSmem ρ hρ
    refine ⟨h1, Nat.lt_succ_of_le (Nat.floor_le_floor ?_)⟩
    exact div_le_div_of_nonneg_right (by linarith) hΛpos.le
  have hclose : ∀ ρ ∈ S, ∀ ρ' ∈ S, |Kt ρ ρ' - AMW.kfunAM (x ρ - x ρ')| ≤ Qδ := by
    intro ρ hρ ρ' hρ'
    obtain ⟨a1, a2⟩ := hSmem ρ hρ
    obtain ⟨b1, b2⟩ := hSmem ρ' hρ'
    exact (kernel_close_real hP hT h8 h32 hF a1 a2 b1 b2).trans hδ
  have hbb := AMW.DE.block_bound c hD hG hH hR I S hSI m (fun ρ => Nat.cast_nonneg _) x Kt hΛpos hη
    (hη12.trans (by norm_num)) J hSx hclose
  set F := frobSq (Pt.hat T (Z.Az Pt T)) with hFdef
  have hFeq : F = ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * Kt ρ ρ' ^ 2 := hfrobeq
  rw [← hFeq] at hbb
  -- the diagonal: `SS ≤ C₁ N`
  have hmn : ∀ ρ, 0 ≤ m ρ := fun ρ => Nat.cast_nonneg _
  have hdiagK : ∀ ρ ∈ S, 1 / 2 ≤ Kt ρ ρ := by
    intro ρ hρ
    have h := hclose ρ hρ ρ hρ
    rw [sub_self, kfunAM_zero] at h
    have h1 := (abs_le.mp h).1
    linarith
  have hdiag : (∑ ρ ∈ S, m ρ ^ 2) / 4 ≤ F := by
    rw [hFeq]
    have hterm : ∀ ρ ∈ S, m ρ ^ 2 / 4 ≤ m ρ * m ρ * Kt ρ ρ ^ 2 := by
      intro ρ hρ
      have hK2 : (1 / 2 : ℝ) ^ 2 ≤ Kt ρ ρ ^ 2 := pow_le_pow_left₀ (by norm_num) (hdiagK ρ hρ) 2
      have h1 := mul_le_mul_of_nonneg_left hK2 (mul_nonneg (hmn ρ) (hmn ρ))
      have e : m ρ * m ρ * (1 / 2) ^ 2 = m ρ ^ 2 / 4 := by ring
      linarith
    calc (∑ ρ ∈ S, m ρ ^ 2) / 4 = ∑ ρ ∈ S, m ρ ^ 2 / 4 := by rw [sum_div]
      _ ≤ ∑ ρ ∈ S, m ρ * m ρ * Kt ρ ρ ^ 2 := sum_le_sum hterm
      _ ≤ ∑ ρ ∈ I, m ρ * m ρ * Kt ρ ρ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hSI fun ρ _ _ =>
            mul_nonneg (mul_nonneg (hmn ρ) (hmn ρ)) (sq_nonneg _)
      _ ≤ ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * Kt ρ ρ' ^ 2 :=
          sum_le_sum fun ρ hρ => single_le_sum (f := fun ρ' => m ρ * m ρ' * Kt ρ ρ' ^ 2)
            (fun ρ' _ => mul_nonneg (mul_nonneg (hmn ρ) (hmn ρ')) (sq_nonneg _)) hρ
  have hSS : (∑ ρ ∈ S, m ρ ^ 2) ≤ 4 * (cinv + 1) * N := by linarith
  -- block masses: Cauchy–Schwarz
  have hfib : ∑ j ∈ range J, ∑ ρ ∈ S.filter (fun ρ => ⌊(x ρ - L ^ 2) / Λ⌋₊ = j), m ρ = ∑ ρ ∈ S, m ρ :=
    sum_fiberwise_of_maps_to (g := fun ρ => ⌊(x ρ - L ^ 2) / Λ⌋₊) (t := range J)
      (fun ρ hρ => mem_range.mpr (hSx ρ hρ).2) _
  have hCS : (∑ ρ ∈ S, m ρ) ^ 2
      ≤ (J : ℝ) * ∑ j ∈ range J, (∑ ρ ∈ S.filter (fun ρ => ⌊(x ρ - L ^ 2) / Λ⌋₊ = j), m ρ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range J)
      (f := fun j => ∑ ρ ∈ S.filter (fun ρ => ⌊(x ρ - L ^ 2) / Λ⌋₊ = j), m ρ)
    rw [hfib, card_range] at this
    exact this
  -- counting
  have hcount : N ≤ (∑ ρ ∈ S, m ρ) + wallN Z T := sum_mult_le_bulk_add Z (P := Pt) (T := T) hLpos
  have hwinOn : ∀ ρ ∈ winFin Z T, ρ.re = 1 / 2 := fun ρ hρ =>
    hon' ρ ((mem_ZI Z T).mp (winFin_subset_ZI Z T hρ))
  have hord : (ordSq Z T : ℝ) ≤ (∑ ρ ∈ S, m ρ ^ 2) + wallN Z T ^ 2 := by
    rw [ordSq_eq_of_online Z T hwinOn]
    exact sum_sq_le_bulk_add Z (P := Pt) (T := T) hLpos
  -- `J ≤ (1 + κ₀/2) N / Λ`
  have hJle : (J : ℝ) ≤ (1 + κ₀ / 2) * N / Λ := by
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    have h1 : (⌊(d - 2 * L ^ 2) / Λ⌋₊ : ℝ) ≤ d / Λ :=
      natFloor_le_of_le (div_nonneg hd0 hΛpos.le) (div_le_div_of_nonneg_right (by linarith) hΛpos.le)
    have h2 : d / Λ ≤ (1 + κ) * N / Λ := div_le_div_of_nonneg_right hdN hΛpos.le
    have h3 : (1 : ℝ) ≤ κ₀ / 4 * N / Λ := by
      rw [le_div_iff₀ hΛpos]
      have := (div_le_iff₀ hκ₀).mp hNΛ
      linarith
    have h4 : (1 + κ) * N / Λ + κ₀ / 4 * N / Λ ≤ (1 + κ₀ / 2) * N / Λ := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hΛpos.le
      have := mul_le_mul_of_nonneg_right hκκ₀ hN0
      linarith
    have hJc : (J : ℝ) = (⌊(d - 2 * L ^ 2) / Λ⌋₊ : ℝ) + 1 := by rw [hJ]; push_cast; ring
    linarith
  have hJpos : (0 : ℝ) < J := by rw [hJ]; positivity
  exact final_algebra hε hh0pos (AMW.DE.gPL_nonneg c hG 0) hκ₀ hκ₀16 hκ₀ε hη hη12 hηκ hηg
    (by positivity) hε₁0 hε₁ε hε₁h hΛpos hRpos hRΛ hQδ.le hQδ2 hQδκ hκ hκκ₀ hκε
    hN0 (sum_nonneg fun ρ _ => sq_nonneg _) hbb hSS hCS hJpos hJle hcount hwall hwall2 hord

/-! ### The theorem -/

/-- **Lemma P on the Lean object for on-line windows** -/
theorem lemmaPObj_online (Z : ZeroConfig) (H : PaperInputs Z) (c : AMW.DE.PLCert) (hD : 0 < c.DkInv)
    (hG : AMW.DE.CertGNonneg c) (hH : AMW.DE.CertHNonneg c) (hh0 : c.y 0 < AMW.DE.qfAM 0)
    (hon : ∀ᶠ T in atTop, ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) :
    LemmaPObj Z (AMW.DE.qfAM 0 - c.y 0) (AMW.DE.gPL c 0) := by
  intro ε hε
  have hh0pos : 0 < AMW.DE.qfAM 0 - c.y 0 := by linarith
  have hg0 : 0 ≤ AMW.DE.gPL c 0 := AMW.DE.gPL_nonneg c hG 0
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  set h0 := AMW.DE.qfAM 0 - c.y 0 with hh0def
  set g0 := AMW.DE.gPL c 0 with hg0def
  set cinv := (cRatio 1 AMW.aInf AMW.bInf AMW.JInf)⁻¹ with hcinvdef
  have hcinv : 0 < cinv := inv_pos.mpr (AMW.cRatio_W_pos one_pos)
  set κ₀ : ℝ := min (1 / 16) (ε / (16 * (h0 + 1))) with hκ₀def
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (by positivity)
  set η : ℝ := min (1 / 2) (min κ₀ (ε / (8 * (g0 * (4 * (cinv + 1)) + 1)))) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (lt_min hκ₀ (by positivity))
  have hη12 : η ≤ 1 / 2 := min_le_left _ _
  set ε₁ : ℝ := min ε h0 / 8 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁ε : ε₁ ≤ ε / 8 := by rw [hε₁def]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hε₁h : ε₁ ≤ h0 / 8 := by rw [hε₁def]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨R, hRpos, hR⟩ := AMW.DE.cert_T_free c hD hG hH ε₁ hε₁
  set Λ : ℝ := max 1 (R / κ₀) with hΛdef
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hRΛ : R ≤ κ₀ * Λ := by
    have := le_max_right 1 (R / κ₀)
    rw [← hΛdef, div_le_iff₀ hκ₀] at this
    linarith
  set Qδ : ℝ := min (1 / 2) (κ₀ * η * ((1 - η) * (h0 - ε₁) / (Λ + R))) with hQδdef
  have hQδ : 0 < Qδ := lt_min (by norm_num) (by
    have : 0 < 1 - η := by linarith
    have : 0 < h0 - ε₁ := by linarith
    positivity)
  set κ : ℝ := min (κ₀ / 4) (ε / (8 * (g0 + 1))) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  obtain ⟨T₁, hT₁⟩ := AMW.localHypsCoreAM_eventually hP
  set K : ℝ := (AMW.cAMW (paramsOf stdProfile 1).ϱ / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  filter_upwards [hon, eventually_gt_atTop 0, eventually_w8 hP, AMW.eventually_w32 hP,
    eventually_ge_atTop T₁, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / Qδ),
    frobAz_le Z H 1 one_pos, growth Z H κ hκ,
    (tendsto_N_atTop Z H.RvM).eventually_ge_atTop (4 * Λ / κ₀)]
    with T hon' hT h8 h32 hTT₁ hL1 hLδ hfrob hgrowth hNΛ
  obtain ⟨hwall, hwall2, hdN⟩ := hgrowth
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
  have hLpos : 0 < L := by linarith
  have hδ : 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L ≤ Qδ := by
    have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hLpos 2, pow_pos hLpos 3]
    have h1 : 10 * K / L ^ 4 ≤ 10 * K / L := div_le_div_of_nonneg_left (by positivity) hLpos hL4
    have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ Qδ := by
      rw [div_le_iff₀ hLpos]
      have := (div_le_iff₀ hQδ).mp hLδ
      linarith
    calc 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
        ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
      _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
      _ ≤ Qδ := h2
  exact online_at_T Z c hD hG hH hε hh0pos hκ₀ (min_le_left _ _) (min_le_right _ _) hη hη12
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _)) hcinv
    hε₁.le hε₁ε hε₁h hR hΛpos hRpos hRΛ hQδ (min_le_left _ _) (min_le_right _ _) hκ (min_le_left _ _)
    (min_le_right _ _) hP hon' hT h8 h32 ((hT₁ T hTT₁).toCoreW) hL1 hδ hfrob hwall hwall2 hdN hNΛ

end Zeta23Ext.Bridge

end
