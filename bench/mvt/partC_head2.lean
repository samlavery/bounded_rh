
/-! ### the derivative tables: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the function the derivative table of sign `sgn` bounds below: `w' + 2` (`true`) or `2 − w'` (`false`) -/
def fD (sgn : Bool) (x : ℝ) : ℝ := if sgn then w1 x + 2 else 2 - w1 x

/-- a nonzero `v / U1` bounds `fD sgn` below on the level-`l` cell `i`, which lies where `2 (π x)² > 1` -/
def CSD (sgn : Bool) (l i v : ℕ) : Prop :=
  v ≠ 0 → ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC →
    kD x < 0 ∧ (v : ℝ) / U1 ≤ fD sgn x

theorem forceB_eq (a : ℕ) (k : ℕ → Bool) : forceB a k = k a := by cases a <;> rfl

theorem CSD_zero (sgn : Bool) (l i : ℕ) : CSD sgn l i 0 := fun h => absurd rfl h

theorem U1_posR : (0:ℝ) < U1 := by norm_num [U1]

/-- a derivative cell claim that passes `cellOkD` is sound -/
theorem cellOkD_sound {sgn : Bool} {l i v : ℕ} (h : cellOkD sgn l i v = true) : CSD sgn l i v := by
  unfold cellOkD at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
          (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hok, hvb⟩ := h'
      have hK' : (i + 1) * 2 ^ l < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
      have hLN : (cellAt l i).LN = i * 2 ^ l := by
        simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
        simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      intro _ x h1 h2
      obtain ⟨hk, hlo, hhi⟩ := cellD_sound (cellAt l i) hok x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
      refine ⟨hk, ?_⟩
      have hU1 := U1_posR
      have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
      cases sgn
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((cellAt l i).W1HI : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte, Bool.false_eq_true]
        rw [div_le_iff₀ hU1]
        have := (le_div_iff₀ hU1).mp hhi
        rw [eK] at hvr
        nlinarith
      · have hv' : (v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO := of_decide_eq_true hvb
        have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((cellAt l i).W1LO : ℝ) := by exact_mod_cast hv'
        simp only [fD, ↓reduceIte]
        rw [div_le_iff₀ hU1]
        have := (div_le_iff₀ hU1).mp hlo
        rw [eK] at hvr
        nlinarith
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; exact CSD_zero sgn l i

