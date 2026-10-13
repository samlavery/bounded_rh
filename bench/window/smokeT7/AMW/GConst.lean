import AMW.GBase

/-!
# AMW/GConst — the constant enclosures of the cell evaluator (stage G)

`π`, `π²`, `2γ`, `1 + 2γ`, `1 + 4γ`, `ρ = 1/(√2 sin(√2/2))`, `σ = ρ/π`, `τ = ρπ` at scale `DZ`, from Taylor
bounds of `cos`, `sin` at `√2/2` (the Montgomery–Taylor file's enclosures, recomputed here).
-/

noncomputable section

open Real

namespace AMW.G

theorem sqrt2_half_bounds' :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧ Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

theorem cos_sqrt2_half_bounds' :
    (7602445947/10^10 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) ∧ Real.cos (Real.sqrt 2 / 2) ≤ 7602445994/10^10 := by
  have hb := sqrt2_half_bounds'
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hu : Real.sqrt 2 / 2 ≤ 1 := by linarith [hb.2]
  have hlo := CellA.cos_le_cos01 h0 hb.2 (by norm_num)
  have hhi := CellA.cos_le_cos01 (by norm_num) hb.1 hu
  have t1 := (cos_sin_taylor12' (7071067811865475245/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).1
  have t2 := (cos_sin_taylor12' (7071067811865475244/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).1
  have e1 : tcos (7071067811865475245/10^19 : ℝ) - terr ≥ 7602445947/10^10 := by unfold tcos terr; norm_num
  have e2 : tcos (7071067811865475244/10^19 : ℝ) + terr ≤ 7602445994/10^10 := by unfold tcos terr; norm_num
  have q1 : |(7071067811865475245/10^19 : ℝ)| ^ 12 * terr ≤ terr :=
    CellA.err12 (by norm_num) (by norm_num)
  have q2 : |(7071067811865475244/10^19 : ℝ)| ^ 12 * terr ≤ terr :=
    CellA.err12 (by norm_num) (by norm_num)
  constructor
  · linarith [(abs_le.mp t1).1]
  · linarith [(abs_le.mp t2).2]

theorem sin_sqrt2_half_bounds' :
    (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) ∧ Real.sin (Real.sqrt 2 / 2) ≤ 6496369414/10^10 := by
  have hb := sqrt2_half_bounds'
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hu : Real.sqrt 2 / 2 ≤ 1 := by linarith [hb.2]
  have hlo := CellA.sin_le_sin01 (by norm_num) hb.1 hu
  have hhi := CellA.sin_le_sin01 h0 hb.2 (by norm_num)
  have t1 := (cos_sin_taylor12' (7071067811865475244/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).2
  have t2 := (cos_sin_taylor12' (7071067811865475245/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).2
  have e1 : tsin (7071067811865475244/10^19 : ℝ) - terr ≥ 6496369368/10^10 := by unfold tsin terr; norm_num
  have e2 : tsin (7071067811865475245/10^19 : ℝ) + terr ≤ 6496369414/10^10 := by unfold tsin terr; norm_num
  have q1 : |(7071067811865475244/10^19 : ℝ)| ^ 12 * terr ≤ terr := CellA.err12 (by norm_num) (by norm_num)
  have q2 : |(7071067811865475245/10^19 : ℝ)| ^ 12 * terr ≤ terr := CellA.err12 (by norm_num) (by norm_num)
  constructor
  · linarith [(abs_le.mp t1).1]
  · linarith [(abs_le.mp t2).2]

theorem gamAM_bounds : (8274992907/10^10 : ℝ) ≤ gamAM ∧ gamAM ≤ 8274993018/10^10 := by
  have hb := sqrt2_half_bounds'
  have hc := cos_sqrt2_half_bounds'
  have hs := sin_sqrt2_half_bounds'
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  have hprodl : (7071067811865475244/10^19 : ℝ) * (7602445947/10^10) ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
    mul_le_mul hb.1 hc.1 (by norm_num) h0
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) ≤ (7071067811865475245/10^19 : ℝ) * (7602445994/10^10) :=
    mul_le_mul hb.2 hc.2 (by linarith [hc.1]) (by norm_num)
  constructor
  · rw [gamAM, le_div_iff₀ hspos]; nlinarith [hprodl, hs.2]
  · rw [gamAM, div_le_iff₀ hspos]; nlinarith [hprodu, hs.1]

theorem rhoAM_eq : rhoAM = (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2) := by
  have hs : Real.sin (Real.sqrt 2 / 2) ≠ 0 := by linarith [sin_sqrt2_half_bounds'.1]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold rhoAM K0AM
  field_simp
  linarith [hsq]

theorem rhoAM_bounds : (1088464550157349/10^15 : ℝ) ≤ rhoAM ∧ rhoAM ≤ 1088464557864635/10^15 := by
  rw [rhoAM_eq]
  have hb := sqrt2_half_bounds'
  have hs := sin_sqrt2_half_bounds'
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  constructor
  · rw [le_div_iff₀ hspos]; nlinarith [hb.1, hs.2]
  · rw [div_le_iff₀ hspos]; nlinarith [hb.2, hs.1]

theorem pi_bounds15 : (3141592653589793/10^15 : ℝ) ≤ π ∧ π ≤ 3141592653589794/10^15 := by
  have h1 := Real.pi_gt_d20; have h2 := Real.pi_lt_d20
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

theorem enc_ofN {a b : ℕ} {v : ℝ} (h1 : (a : ℝ) / DZ ≤ v) (h2 : v ≤ (b : ℝ) / DZ) : (IV.ofN a b).Enc v := by
  simp only [IV.Enc, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact ⟨h1, h2⟩

theorem PIC_enc : PIC.Enc π := by
  have h := pi_bounds15
  refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]

theorem PI2C_enc : PI2C.Enc (π ^ 2) := by
  have h := pi_bounds15
  have h0 : (0:ℝ) ≤ 3141592653589793/10^15 := by norm_num
  refine enc_ofN ?_ ?_ <;> norm_num [DZ]
  · nlinarith [mul_le_mul h.1 h.1 h0 (h0.trans h.1)]
  · nlinarith [mul_le_mul h.2 h.2 (h0.trans h.1) (by norm_num : (0:ℝ) ≤ 3141592653589794/10^15)]

theorem G1C_enc : G1C.Enc (1 + 2 * gamAM) := by
  have h := gamAM_bounds
  refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]

theorem G2C_enc : G2C.Enc (1 + 4 * gamAM) := by
  have h := gamAM_bounds
  refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]

theorem GAM_bounds : (GAM0 : ℝ) / DZ ≤ 2 * gamAM ∧ 2 * gamAM ≤ (GAM1 : ℝ) / DZ := by
  have h := gamAM_bounds
  constructor <;> norm_num [GAM0, GAM1, DZ] <;> linarith [h.1, h.2]

theorem RHOC_enc : RHOC.Enc rhoAM := by
  have h := rhoAM_bounds
  refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]

theorem rhoAM_pos : 0 < rhoAM := by linarith [rhoAM_bounds.1]

theorem SIGC_enc : SIGC.Enc (rhoAM / π) := by
  have h := rhoAM_bounds
  have hp := pi_bounds15
  have hpp : 0 < π := Real.pi_pos
  refine enc_ofN ?_ ?_ <;> norm_num [DZ]
  · rw [le_div_iff₀ hpp]; nlinarith [h.1, hp.2]
  · rw [div_le_iff₀ hpp]; nlinarith [h.2, hp.1]

theorem TAUC_enc : TAUC.Enc (rhoAM * π) := by
  have h := rhoAM_bounds
  have hp := pi_bounds15
  refine enc_ofN ?_ ?_ <;> norm_num [DZ]
  · nlinarith [mul_le_mul h.1 hp.1 (by norm_num) rhoAM_pos.le]
  · nlinarith [mul_le_mul h.2 hp.2 Real.pi_pos.le (by norm_num)]

end AMW.G
