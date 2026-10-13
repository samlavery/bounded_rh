import AMW.DECert
import AMW.DEPInterface

/-! ###### AMW/DEObjA — the Lean object on on-line windows: Gram expansion and kernel closeness (bridge-port)

* `frob_hat_Az_online`: if every zero of `𝒵(I')` is on the line, `‖Â‖_F² = Σ_{ρ,ρ'} m_ρ m_ρ' K_T(γ_ρ, γ_ρ')²` with the
  real sampled kernel `K_T(γ, γ') = (aL²)⁻¹ Σ_{k<d} φ̂(γ − τ_k) φ̂(γ' − τ_k)` (`KT`) — every term is a square.
* `kernel_close_real`: for real ordinates at normalised distance `≥ L²` from the walls,
  `|K_T(γ, γ') − kfun(x − x')| ≤ 10K/L⁴ + 12w/L` (`x = L(γ − T)/2π`).  This is the bridge's `gram_close_of`
  (BrB) restated for any two real ordinates, simple or not. ###### -/

noncomputable section

open Matrix Finset Filter MeasureTheory Real Set RHLinalg
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

/-- the normalised coordinate of a real ordinate -/
def xr (P : Params) (T γ : ℝ) : ℝ := P.L T * (γ - T) / (2 * Real.pi)

/-- the real sampled kernel -/
def KT (P : Params) (T γ γ' : ℝ) : ℝ :=
  (aL2 P T)⁻¹ * ∑ k : Fin (P.d T), P.phiHatR T (γ - P.tau T k) * P.phiHatR T (γ' - P.tau T k)

theorem xnorm_eq_xr (P : Params) (T : ℝ) (ρ : ℂ) : xnorm P T ρ = xr P T ρ.im := rfl

/-- the far conditions from the normalised position (the bridge's `retained_far` for a real ordinate) -/
lemma far_of_xr {P : Params} {T γ : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    (h1 : P.L T ^ 2 ≤ xr P T γ) (h2 : xr P T γ ≤ (P.d T : ℝ) - P.L T ^ 2) :
    P.L T ≤ γ - T ∧ P.L T ≤ 2 * T - γ ∧ P.L T ≤ P.tau T (P.d T) - γ := by
  unfold xr at h1 h2
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * (γ - T) := by
    have := (le_div_iff₀ hπ).mp h1; linarith
  have h2' : P.L T * (γ - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
    have := (div_le_iff₀ hπ).mp h2; linarith
  have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
    have := (le_div_iff₀ hπ).mp hd; linarith
  have g1 : 2 * Real.pi * P.L T ≤ γ - T := by
    have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * (γ - T) := by nlinarith
    exact le_of_mul_le_mul_left this hL
  have g2 : 2 * Real.pi * P.L T ≤ 2 * T - γ := by
    have : P.L T * (γ - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
    have := le_of_mul_le_mul_left this hL
    linarith
  have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
    simp only [Params.tau, Params.hgrid, Int.cast_natCast]
  rw [htau]
  have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - γ
      = (2 * Real.pi * (P.d T : ℝ) - P.L T * (γ - T)) / P.L T := by
    field_simp
    ring
  rw [e, le_div_iff₀ hL]
  nlinarith

/-- **kernel closeness for real ordinates** (the bridge's `gram_close_of`, any two ordinates) -/
theorem kernel_close_real {P : Params} (hP : P.Valid) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T) (h32 : 32 * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (AMW.cAMW P.ϱ) (P.toSetting T) (AMW.lfW P (AMW.WAM P) T))
    {γ γ' : ℝ}
    (hx1 : P.L T ^ 2 ≤ xr (AMW.atAM P T) T γ) (hx2 : xr (AMW.atAM P T) T γ ≤ ((AMW.atAM P T).d T : ℝ) - P.L T ^ 2)
    (hx1' : P.L T ^ 2 ≤ xr (AMW.atAM P T) T γ')
    (hx2' : xr (AMW.atAM P T) T γ' ≤ ((AMW.atAM P T).d T : ℝ) - P.L T ^ 2) :
    |KT (AMW.atAM P T) T γ γ' - kfun (xr (AMW.atAM P T) T γ - xr (AMW.atAM P T) T γ')|
      ≤ 10 * (AMW.cAMW P.ϱ / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := AMW.admWindow_WAM hP T h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (AMW.atAM P T).a T := (AMW.aAM_range_of hP h32).1
  set K : ℝ := (AMW.cAMW P.ϱ / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  unfold KT
  rw [← Kfun_eq_sum hP T γ γ']
  obtain ⟨g1, g2, g3⟩ := far_of_xr (P := AMW.atAM P T) (γ := γ) hL hT.le hx1 hx2
  obtain ⟨g1', g2', g3'⟩ := far_of_xr (P := AMW.atAM P T) (γ := γ') hL hT.le hx1' hx2'
  have htail : |PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'
  have hx : 2 * Real.pi * (xr (AMW.atAM P T) T γ - xr (AMW.atAM P T) T γ') / P.L T = γ - γ' := by
    unfold xr
    rw [atAM_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP h8 h32 (xr (AMW.atAM P T) T γ - xr (AMW.atAM P T) T γ')
  rw [hx] at hlim
  set A : ℝ := (AMW.atAM P T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (AMW.WAM P T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' = P.L T * V :=
    Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (AMW.atAM P T) T = A * P.L T ^ 2 := by unfold aL2; rw [atAM_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  set kx := kfun (xr (AMW.atAM P T) T γ - xr (AMW.atAM P T) T γ') with hkx
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kx
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V) + (V / (A * P.L T) - kx) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V) + (V / (A * P.L T) - kx)|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)| + |V / (A * P.L T) - kx| := abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf| + |V / (A * P.L T) - kx| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
    _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
        gcongr
    _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
        field_simp
        ring

/-! ### The Gram expansion of `‖Â‖_F²` on on-line windows -/

/-- `Σ_{k,l} (Σ_ρ m_ρ a_ρk a_ρl)² = Σ_{ρ,ρ'} m_ρ m_ρ' (Σ_k a_ρk a_ρ'k)²` -/
theorem sum_sq_rank_one {κ ι : Type*} (K : Finset κ) (I : Finset ι) (m : ι → ℝ) (a : ι → κ → ℝ) :
    ∑ k ∈ K, ∑ l ∈ K, (∑ ρ ∈ I, m ρ * a ρ k * a ρ l) ^ 2
      = ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * (∑ k ∈ K, a ρ k * a ρ' k) ^ 2 := by
  have lhs : ∀ k l, (∑ ρ ∈ I, m ρ * a ρ k * a ρ l) ^ 2
      = ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l) := by
    intro k l
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun ρ _ => sum_congr rfl fun ρ' _ => by ring
  have rhs : ∀ ρ ρ', m ρ * m ρ' * (∑ k ∈ K, a ρ k * a ρ' k) ^ 2
      = ∑ k ∈ K, ∑ l ∈ K, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l) := by
    intro ρ ρ'
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun k _ => by rw [mul_sum]; exact sum_congr rfl fun l _ => by ring
  simp_rw [lhs, rhs]
  calc ∑ k ∈ K, ∑ l ∈ K, ∑ ρ ∈ I, ∑ ρ' ∈ I, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l)
      = ∑ k ∈ K, ∑ ρ ∈ I, ∑ l ∈ K, ∑ ρ' ∈ I, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l) :=
        sum_congr rfl fun k _ => sum_comm
    _ = ∑ ρ ∈ I, ∑ k ∈ K, ∑ l ∈ K, ∑ ρ' ∈ I, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l) := sum_comm
    _ = ∑ ρ ∈ I, ∑ ρ' ∈ I, ∑ k ∈ K, ∑ l ∈ K, m ρ * m ρ' * (a ρ k * a ρ' k) * (a ρ l * a ρ' l) :=
        sum_congr rfl fun ρ _ => (sum_congr rfl fun k _ => sum_comm).trans sum_comm

/-- the entries of `Â` on an on-line window -/
theorem hat_Az_apply_online {Z : ZeroConfig} {P : Params} {T : ℝ} (hreal : PhiHatReal T P)
    (hon : ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) (k l : Fin (P.d T)) :
    P.hat T (Z.Az P T) k l
      = (((aL2 P T)⁻¹ * ∑ ρ ∈ ZI Z T, (Z.mult ρ : ℝ) * P.phiHatR T (ρ.im - P.tau T k)
          * P.phiHatR T (ρ.im - P.tau T l) : ℝ) : ℂ) := by
  rw [hat_eq, Matrix.smul_apply]
  change ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T)]
  change ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • ∑ ρ ∈ ZI Z T, Z.Gsummand P T k l ρ) = _
  rw [smul_eq_mul, aL2]
  push_cast
  congr 1
  refine sum_congr rfl fun ρ hρ => ?_
  have hre := hon ρ ((mem_ZI Z T).mp hρ)
  simp only [ZeroConfig.Gsummand]
  rw [gammaOf_of_re_eq_half hre, ← Complex.ofReal_sub, ← Complex.ofReal_sub, hreal, hreal]

/-- **`‖Â‖_F²` on an on-line window is a sum of squares over pairs of zeros** -/
theorem frob_hat_Az_online {Z : ZeroConfig} {P : Params} {T : ℝ} (hreal : PhiHatReal T P)
    (hon : ∀ ρ ∈ Z.ZIprime T, ρ.re = 1 / 2) :
    frobSq (P.hat T (Z.Az P T))
      = ∑ ρ ∈ ZI Z T, ∑ ρ' ∈ ZI Z T, (Z.mult ρ : ℝ) * (Z.mult ρ' : ℝ) * KT P T ρ.im ρ'.im ^ 2 := by
  set c : ℝ := (aL2 P T)⁻¹ with hc
  have e : ∀ k l, ‖P.hat T (Z.Az P T) k l‖ ^ 2
      = c ^ 2 * (∑ ρ ∈ ZI Z T, (Z.mult ρ : ℝ) * P.phiHatR T (ρ.im - P.tau T k)
          * P.phiHatR T (ρ.im - P.tau T l)) ^ 2 := by
    intro k l
    rw [hat_Az_apply_online hreal hon, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have hrk := sum_sq_rank_one (Finset.univ : Finset (Fin (P.d T))) (ZI Z T) (fun ρ => (Z.mult ρ : ℝ))
    (fun ρ k => P.phiHatR T (ρ.im - P.tau T k))
  calc frobSq (P.hat T (Z.Az P T))
      = ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), c ^ 2 * (∑ ρ ∈ ZI Z T, (Z.mult ρ : ℝ)
          * P.phiHatR T (ρ.im - P.tau T k) * P.phiHatR T (ρ.im - P.tau T l)) ^ 2 := by
        rw [Assembly.frobSq_eq_sum_norm_sq]
        exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => e k l
    _ = c ^ 2 * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), (∑ ρ ∈ ZI Z T, (Z.mult ρ : ℝ)
          * P.phiHatR T (ρ.im - P.tau T k) * P.phiHatR T (ρ.im - P.tau T l)) ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by rw [mul_sum]
    _ = c ^ 2 * ∑ ρ ∈ ZI Z T, ∑ ρ' ∈ ZI Z T, (Z.mult ρ : ℝ) * (Z.mult ρ' : ℝ)
          * (∑ k : Fin (P.d T), P.phiHatR T (ρ.im - P.tau T k) * P.phiHatR T (ρ'.im - P.tau T k)) ^ 2 := by
        rw [hrk]
    _ = ∑ ρ ∈ ZI Z T, ∑ ρ' ∈ ZI Z T, (Z.mult ρ : ℝ) * (Z.mult ρ' : ℝ) * KT P T ρ.im ρ'.im ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun ρ _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun ρ' _ => ?_
        unfold KT
        rw [← hc]
        ring

end Zeta23Ext.Bridge

end
