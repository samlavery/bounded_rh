import AMW.AMTail

/-! ###### AMW/DefectEnergy — the defect-energy route to the simple-zero proportion (bridge-port; skeleton)

For the R8 (AMTOPA) window let `Â_T` be the hat-unit Gram matrix of the windowed zeros (`Z.Az`). Its Frobenius energy
per zero, less the density spike `e₀ = bInf/aInf² (= qf(0))`, halved to the one-sided form, is the defect energy
`ℰ_T = (‖Â_T‖_F²/N − e₀)/2` (`edE`). The traces give its limit from above: `N ℰ_T ≤ (e∞ + ε) N` eventually, with
`e∞ = JInf/(2 aInf²) (= ∫₀¹ qf(α) α dα)` (`defectEnergy_datum`). Under the defect-energy inequality
`D(δ): δ (N − N₀ˢ) ≤ N ℰ_T + o(N)` (`DefectEnergy`, an explicit hypothesis), the simple on-line zeros are at least
`(1 − e∞/δ) N` (`dyadic_of_defectEnergy`), and `AMW.am_dyadic_defect`, `AMW.am_cumulative_defect` give the board's
two shapes. ###### -/

noncomputable section

open Matrix RHLinalg Filter Topology Asymptotics
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

/-- the density spike of the R8 window: `qf(0) = bInf/aInf²` -/
def e0DE : ℝ := AMW.bInf / AMW.aInf ^ 2

/-- the band-1 pair-correlation energy of the R8 window: `∫₀¹ qf(α) α dα = JInf/(2 aInf²)` -/
def eInfDE : ℝ := AMW.JInf / (2 * AMW.aInf ^ 2)

/-- the defect energy at height `T`: one-sided, the density spike removed -/
def edE (Z : ZeroConfig) (T : ℝ) : ℝ :=
  (frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) / (Z.N T (2 * T) : ℝ) - e0DE) / 2

/-- **the defect-energy inequality `D(δ)`** for the zeros of `Z` (a hypothesis of the theorems below) -/
def DefectEnergy (Z : ZeroConfig) (δ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    δ * ((Z.N T (2 * T) : ℝ) - (Z.N0s T (2 * T) : ℝ)) ≤ (Z.N T (2 * T) : ℝ) * edE Z T + ε * (Z.N T (2 * T) : ℝ)

/-- the Frobenius limit splits into the density spike and twice the pair energy -/
lemma cRatio_inv_eq : (cRatio 1 AMW.aInf AMW.bInf AMW.JInf)⁻¹ = e0DE + 2 * eInfDE := by
  have ha := AMW.aInf_pos
  unfold cRatio e0DE eInfDE
  rw [inv_div]
  field_simp

/-- `(s + e)² ≤ (c + ε) N` from `s² ≤ (c + ε/4) N`, `e ≤ Bt ≤ 1` and `N` large against `1/η` -/
lemma sq_split_le {F s e Bt η c N ε : ℝ} (hF : F ≤ (s + e) ^ 2) (hs : 0 ≤ s) (he0 : 0 ≤ e)
    (he : e ≤ Bt) (hBt1 : Bt ≤ 1) (hη : 0 < η) (hN0 : 0 ≤ N) (hX : s ^ 2 ≤ (c + ε / 4) * N)
    (hηc : η * (c + ε / 4) ≤ ε / 4) (hN4 : 1 + 1 / η ≤ ε / 4 * N) : F ≤ (c + ε) * N := by
  have hB0 : 0 ≤ Bt := he0.trans he
  have h1 : (s + e) ^ 2 ≤ (s + Bt) ^ 2 := by gcongr
  have h2 : 2 * s * Bt ≤ η * s ^ 2 + Bt ^ 2 / η := by
    have h := div_nonneg (sq_nonneg (η * s - Bt)) hη.le
    have e : (η * s - Bt) ^ 2 / η = η * s ^ 2 + Bt ^ 2 / η - 2 * s * Bt := by field_simp; ring
    linarith
  have h3 : Bt ^ 2 ≤ 1 := pow_le_one₀ hB0 hBt1
  have h4 : Bt ^ 2 / η ≤ 1 / η := div_le_div_of_nonneg_right h3 hη.le
  have h5 : η * s ^ 2 ≤ ε / 4 * N := by
    calc η * s ^ 2 ≤ η * ((c + ε / 4) * N) := mul_le_mul_of_nonneg_left hX hη.le
      _ = η * (c + ε / 4) * N := by ring
      _ ≤ ε / 4 * N := mul_le_mul_of_nonneg_right hηc hN0
  have h6 : (s + Bt) ^ 2 = s ^ 2 + 2 * s * Bt + Bt ^ 2 := by ring
  have h7 : 0 < 1 / η := by positivity
  linarith

/-- the Frobenius bound from the traces, absorbed into `(c + ε/4) N` -/
lemma frob_absorb {x ci N K c ε : ℝ} (hx : x ≤ ci * N + K * (ci * N)) (h1 : ci ≤ c + ε / 8)
    (hK0 : 0 ≤ K) (h2 : K * (c + ε / 8) ≤ ε / 8) (hN0 : 0 ≤ N) : x ≤ (c + ε / 4) * N := by
  have a1 : ci * N ≤ (c + ε / 8) * N := mul_le_mul_of_nonneg_right h1 hN0
  have a2 : K * (ci * N) ≤ K * ((c + ε / 8) * N) := mul_le_mul_of_nonneg_left a1 hK0
  have a3 : K * (c + ε / 8) * N ≤ ε / 8 * N := mul_le_mul_of_nonneg_right h2 hN0
  have a4 : K * ((c + ε / 8) * N) = K * (c + ε / 8) * N := by ring
  linarith

/-- the tail in hat units tends to `0` (the `o4` step of `endgame_defect`) -/
lemma tail_hat_tendsto {P : Params} (hP : P.Valid) {aT θ₀ : ℝ → ℝ}
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hθ0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T) {Cθ : ℝ}
    (hθ : ∀ᶠ T in atTop, θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1)) :
    Tendsto (fun T => θ₀ T / (aT T * P.L T)) atTop (𝓝 0) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
    simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hθ0, ha, eventually_l_pos] with T hT0 ha2 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact div_nonneg hT0 (by nlinarith [ha2.1])
  · filter_upwards [ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
      with T ha2 hl hθT hT0
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
    rw [div_le_iff₀ (mul_pos hapos' hLpos)]
    calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
      _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
      _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
      _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
        have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
            = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
        rw [this]; gcongr; exact ha2.1

/-- the Frobenius datum for any valid AMTOPA parameter family -/
theorem frobAz_le_P (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) :
    ∀ ε > 0, ∀ᶠ T in atTop, frobSq ((AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T))
      ≤ ((cRatio P.lam AMW.aInf AMW.bInf AMW.JInf)⁻¹ + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  have hLoc := AMW.localHypsCoreAM_eventually hP
  have hTr := AMW.tracesBoundsAM_concrete (Z := Z) hP H
  have hc : Tendsto (fun T => cRatio (P.lam1 T) ((AMW.concreteDataW P (AMW.WAM P) Z).aT T)
      ((AMW.concreteDataW P (AMW.WAM P) Z).bT T) ((AMW.concreteDataW P (AMW.WAM P) Z).JT T)) atTop
      (𝓝 (cRatio P.lam AMW.aInf AMW.bInf AMW.JInf)) := AMW.tendsto_cRatio_W hP
  have hc0 := AMW.cRatio_W_pos hP.lam_pos
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (AMW.concreteDataW P (AMW.WAM P) Z).aT T ∧
      (AMW.concreteDataW P (AMW.WAM P) Z).aT T ≤ 1 :=
    (AMW.concreteFactsW hP H (AMW.admWindow_WAM hP) hLoc).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, ⟨Cθ, hθ⟩⟩ := AMW.eventually_tailPackageAM Z H hP
  have hGzGp := AMW.eventually_GzGpAM Z H hP
  have hcalE := Assembly.calE_tendsto_zero P hlam0 hlam1 (zero_le_one.trans hP.one_le_w)
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  set aT := (AMW.concreteDataW P (AMW.WAM P) Z).aT with haT
  set bT := (AMW.concreteDataW P (AMW.WAM P) Z).bT with hbT
  set JT := (AMW.concreteDataW P (AMW.WAM P) Z).JT with hJT
  set trG2 := (AMW.concreteDataW P (AMW.WAM P) Z).trG2 with htrG2
  set c := cRatio P.lam AMW.aInf AMW.bInf AMW.JInf with hcdef
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  have hci : 0 < c⁻¹ := inv_pos.mpr hc0
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have o4 := tail_hat_tendsto hP ha (hTail.mono fun T h => h.theta_nonneg) hθ
  -- the split constant
  set η : ℝ := ε / (4 * (c⁻¹ + 1 + ε)) with hηdef
  have hD : 0 < c⁻¹ + 1 + ε := by linarith
  have hη : 0 < η := div_pos hε (by linarith)
  have hηD : η * (c⁻¹ + 1 + ε) = ε / 4 := by
    rw [hηdef, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]; ring
  have hηc : η * (c⁻¹ + ε / 4) ≤ ε / 4 := by
    rw [← hηD]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
  have e1 : ∀ᶠ T in atTop, cinv T ≤ c⁻¹ + ε / 8 :=
    hcinv_to.eventually (eventually_le_nhds (by linarith))
  have e2 : ∀ᶠ T in atTop, C₂ * P.calE T * (c⁻¹ + ε / 8) ≤ ε / 8 := by
    have h0 : Tendsto (fun T => C₂ * P.calE T * (c⁻¹ + ε / 8)) atTop (𝓝 0) := by
      simpa using (hcalE.const_mul C₂).mul_const (c⁻¹ + ε / 8)
    exact h0.eventually (eventually_le_nhds (by linarith))
  have e3 : ∀ᶠ T in atTop, θ₀ T / (aT T * P.L T) ≤ 1 := o4.eventually (eventually_le_nhds one_pos)
  have e4 : ∀ᶠ T in atTop, (1 + 1 / η) / (ε / 4) ≤ N T :=
    (tendsto_N_atTop Z H.RvM).eventually_ge_atTop _
  filter_upwards [e1, e2, e3, e4, hTail, hGzGp, ha, eventually_ge_atTop T₂,
    eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_l_pos,
    eventually_gt_atTop (0:ℝ)]
    with T h1 h2 h3 h4 hTl hGG ha2 hT₂ hE0 hl hT0
  have hid : (AMW.atAM P T).trGtilde T = (AMW.concreteDataW P (AMW.WAM P) Z).trG T ∧
      (AMW.atAM P T).trGtildeSq T = trG2 T ∧ (AMW.atAM P T).a T = aT T :=
    AMW.atW_ident Z hP (AMW.WAM_even P) T
  obtain ⟨-, hidfr, hida⟩ := hid
  have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
  have hN0 : 0 ≤ N T := Nat.cast_nonneg _
  -- ‖Ĝ‖² from the traces
  have hfr : frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T)) = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
    rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
  have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + C₂ * P.calE T * (cinv T * N T) := by
    have h := hfr2 T hT₂
    simp only at h
    have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
      rw [← mul_assoc] at h
      exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
    have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
      rw [inv_pow, div_eq_inv_mul]
    rw [e]; linarith
  -- Â = Ĝ − Ê, and the tail's Frobenius bound
  obtain ⟨Bt, hB0, -, hfrE, hBle⟩ := hTl.hat
  have haL : (AMW.atAM P T).a T * (AMW.atAM P T).L T = aT T * P.L T := by rw [hida]; rfl
  rw [haL] at hBle
  have hA : (AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T)
      = (AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T) - (AMW.atAM P T).hat T (Z.Ez (AMW.atAM P T) T) := by
    rw [eq_sub_iff_add_eq, ← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hfa := frobSq_sub_le ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T))
    ((AMW.atAM P T).hat T (Z.Ez (AMW.atAM P T) T))
  rw [← hA] at hfa
  have hs2 : Real.sqrt (frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T))) ^ 2
      = frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T)) := Real.sq_sqrt (frobSq_nonneg _)
  have hsE : Real.sqrt (frobSq ((AMW.atAM P T).hat T (Z.Ez (AMW.atAM P T) T))) ≤ Bt :=
    Real.sqrt_le_iff.mpr ⟨hB0, hfrE⟩
  have hX : Real.sqrt (frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T))) ^ 2 ≤ (c⁻¹ + ε / 4) * N T := by
    rw [hs2, hfr]
    exact frob_absorb hfrb h1 (mul_nonneg hC₂.le hE0) h2 hN0
  have hN4 : 1 + 1 / η ≤ ε / 4 * N T := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < ε / 4)).mp h4
    linarith
  exact sq_split_le hfa (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hsE (hBle.trans h3) hη hN0 hX hηc hN4

/-- **the Frobenius datum**: the hat-unit energy of the windowed zeros is at most `(1/c∞ + ε) N`, eventually -/
theorem frobAz_le (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop, frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
      ≤ ((cRatio 1 AMW.aInf AMW.bInf AMW.JInf)⁻¹ + ε) * (Z.N T (2 * T) : ℝ) :=
  frobAz_le_P Z H (paramsOf stdProfile 1) (paramsOf_valid taperProfile_stdProfile one_pos le_rfl)

/-- **the datum**: `N ℰ_T ≤ (e∞ + ε) N`, eventually -/
theorem defectEnergy_datum (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Z.N T (2 * T) : ℝ) * edE Z T ≤ (eInfDE + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  filter_upwards [frobAz_le Z H (2 * ε) (by linarith)] with T h
  rw [cRatio_inv_eq] at h
  unfold edE
  set F := frobSq ((mtParams T).hat T (Z.Az (mtParams T) T)) with hFdef
  set N := (Z.N T (2 * T) : ℝ) with hNdef
  rcases eq_or_ne N 0 with h0 | h0
  · rw [h0]; simp
  · have hF : N * (F / N) = F := by field_simp
    calc N * ((F / N - e0DE) / 2) = (N * (F / N) - e0DE * N) / 2 := by ring
      _ = (F - e0DE * N) / 2 := by rw [hF]
      _ ≤ (eInfDE + ε) * N := by linarith

end Zeta23Ext.Bridge

end

noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge

/-- **from `D(δ)` to the simple on-line zeros**: `(1 − e∞/δ − ε) N(T,2T) ≤ N₀ˢ(T,2T)` for large `T` -/
theorem dyadic_of_defectEnergy {δ : ℝ} (hδ : 0 < δ) (hD : DefectEnergy zetaZeroConfig δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - eInfDE / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((hD (δ * ε / 2) (by positivity)).and
      (defectEnergy_datum zetaZeroConfig paperInputs_zeta (δ * ε / 2) (by positivity)))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at h1 h2
  have e : δ * ((1 - eInfDE / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      = δ * (Zeta23.Ncount T (2 * T) : ℝ) - eInfDE * (Zeta23.Ncount T (2 * T) : ℝ)
        - δ * ε * (Zeta23.Ncount T (2 * T) : ℝ) := by
    field_simp
  have key : δ * ((1 - eInfDE / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      ≤ δ * (Zeta23.N0simple T (2 * T) : ℝ) := by
    rw [e]; linarith
  exact le_of_mul_le_mul_left key hδ

/-- the board's dyadic shape: `κ ≤ 1 − e∞/δ` under `D(δ)` -/
theorem am_dyadic_defect {δ κ : ℝ} (hδ : 0 < δ) (hD : DefectEnergy zetaZeroConfig δ)
    (hκ : κ ≤ 1 - eInfDE / δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := dyadic_of_defectEnergy hδ hD ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (1 - eInfDE / δ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- the cumulative form -/
theorem am_cumulative_defect {δ κ : ℝ} (hδ : 0 < δ) (hD : DefectEnergy zetaZeroConfig δ)
    (hκ : κ ≤ 1 - eInfDE / δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (am_dyadic_defect hδ hD hκ)

end AMW

end
