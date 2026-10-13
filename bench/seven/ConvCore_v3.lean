import SlopeCore

-- CONV-BEGIN
/-! ###### convex basins: the sign of `w''` on a cell, chains of cells where `w'' ≥ 0`, and the tangent minorant ######

Basin boxes at the near-minimal local minima after six-point-convex-basins-2 by typh (Apache-2.0): around such a
minimum each pair term is convex on its range, so its tangent at the expansion point is a lower bound and the slope
test needs no charge.  Here `w'' = 2π² P / D⁴` with `P = M² + N (N₂ D² + 4 N D + 8 b M)` and
`N₂ = −(1 + 4γ) cos b + 2γ b sin b` (`b = π x`, `N`, `M`, `D` as in the derivative cells); a cell certifies
`w'' ≥ 0` when the integer enclosure of `P` is nonnegative. -/

section ConvDefs

namespace Zeta23Ext.Bridge.ThreePoint

/-- `1 + 4γ` at scale `DZ` -/
def G2I : ℤ × ℤ := (4309997162800000, 4309997207200000)

namespace CellN
def N2I (c : CellN) : ℤ × ℤ := isubZ (imulP c.PGI c.SXZ) (imulP G2I c.CXZ)
def P2I (c : CellN) : ℤ × ℤ :=
  iaddZ (imulD c.MI c.MI)
    (imulD c.NI (iaddZ (iaddZ (imulD c.N2I (imulD c.DI c.DI)) (imulZZ 4 (imulD c.NI c.DI))) (imulP (imulZZ 8 c.BI) c.MI)))
/-- the cell certifies `D < 0` and `w'' ≥ 0` -/
def convOk (c : CellN) : Bool := c.okD && decide (0 ≤ c.P2I.1)
end CellN

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- the cell `[a, b] / SC` -/
def ccell (a b : ℕ) : CellN := ⟨Nat.add (Nat.mul a KB) b, 0⟩

/-- a chain `a = c₀ ≤ c₁ ≤ … ≤ c_k` of cells `[c_i, c_(i+1)]`, each certifying `w'' ≥ 0` -/
def chainOk (a : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && ih b) l a

/-- the chain's last point -/
def chainLast (a : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun a => a) (fun b _ ih _ => ih b) l a

/-- the side conditions of a pair term in a convex basin: nonzero slope claims at `QS` and a nonempty chain from `L`
to `U` (expanded terms), nothing (zero-order terms) -/
def ctok (bit : Bool) (L U QS X : ℕ) (c : List ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X)) && Nat.ble 1 c.length && chainOk L c
      && Nat.beq (chainLast L c) U) bit

/-- the binary block dispatch of the tables: below / from the split point `m`, and a single block `k` -/
def dsel (j m a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) a b (Nat.ble m j)
def dpk (j k v : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 v (Nat.beq j k)

/-- a pair term's value read through a point function `f` (the triple at `QS`) or at zero order -/
def selXf (bit : Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lb3 top bk L U) (f QS) bit
/-- a triple `v` at the point `x / SC`, checked on the degenerate integer cell -/
def pt3e (x v : ℕ) : Bool := ptOk x (lo32 v) && ptdOk x (lo32 (hi32 v)) (hi32 (hi32 v))
/-- the triple of `x` in a short list of points (`0` if absent) -/
def ptl (L : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ ih => Bool.rec (motive := fun _ => ℕ) ih e.2 (Nat.beq e.1 x)) L
def ptlOk (L : List (ℕ × ℕ)) : Bool := List.rec (motive := fun _ => Bool) true (fun e _ ih => pt3e e.1 e.2 && ih) L

/-- evaluate a Boolean before continuing (the kernel is call-by-name) -/
def bforce (b : Bool) (k : Bool → Bool) : Bool := Bool.rec (motive := fun _ => Bool) (k false) (k true) b

/-- convex regions `[a, b]` of `w`, each with a chain of cells from `a` to `b` certifying `w'' ≥ 0` -/
def inReg (R : List (ℕ × ℕ × List ℕ)) (lo hi : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => (Nat.ble r.1 lo && Nat.ble hi r.2.1) || ih) R
def regOk (R : List (ℕ × ℕ × List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => Nat.ble 1 r.2.2.length && chainOk r.1 r.2.2 && Nat.beq (chainLast r.1 r.2.2) r.2.1 && ih) R
/-- the side conditions of a pair term of the slope test: a convex term (`cv`, its range inside a convex region) needs
nonzero slope claims at `QS` when expanded, any other term the slope test's conditions -/
def rtok (cv bit : Bool) (L U QS X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tok bit L U QS X EU ED)
    (Bool.rec (motive := fun _ => Bool) true (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) bit) cv

/-- the derivative reads of a mixed term: none for a convex term (`vb`), else those of the slope test -/
def selUv (vb bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (QS U : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (selU bit tD bD QS U) 0 vb
def selDv (vb bit : Bool) (tD : ℕ) (bD : ℕ → ℕ) (L QS : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (selD bit tD bD L QS) 0 vb
/-- the charge of a mixed term: none for a convex term, else the slope test's -/
def mchg (vb bit : Bool) (L U QS X EU ED : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (tchg bit L U QS X EU ED) 0 vb
/-- the side conditions of a mixed term -/
def mtok (vb bit : Bool) (L U QS X EU ED : ℕ) (c : List ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tok bit L U QS X EU ED) (ctok bit L U QS X c) vb

end Zeta23Ext.Bridge.ThreePoint.PyrD

end ConvDefs
-- CONVDEFS-END

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### the second derivative of `wfun` -/

def kN2 (x : ℝ) : ℝ := -(1 + 4 * gam) * Real.cos (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)
def kP2 (x : ℝ) : ℝ := kM x ^ 2 + kN x * (kN2 x * kD x ^ 2 + 4 * kN x * kD x + 8 * (Real.pi * x) * kM x)
/-- the derivative of `w1` where `2 (π x)² ≠ 1` -/
def w2 (x : ℝ) : ℝ := 2 * Real.pi ^ 2 * kP2 x / kD x ^ 4

theorem hasDerivAt_kNb (x : ℝ) : HasDerivAt kNb (Real.pi * kN2 x) x := by
  have h := (((hasDerivAt_pix x).sin).const_mul (-(1 + 2 * gam))).sub
    (((hasDerivAt_pix x).const_mul (2 * gam)).mul (hasDerivAt_pix x).cos)
  have e : kNb = fun y : ℝ => -(1 + 2 * gam) * Real.sin (Real.pi * y) - 2 * gam * (Real.pi * y) * Real.cos (Real.pi * y) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kN2; ring

theorem hasDerivAt_kM (x : ℝ) : HasDerivAt kM (Real.pi * (kN2 x * kD x + 4 * kN x)) x := by
  have h := ((hasDerivAt_kNb x).mul (hasDerivAt_kD x)).add (((hasDerivAt_pix x).const_mul 4).mul (hasDerivAt_kN x))
  have e : kM = fun y : ℝ => kNb y * kD y + 4 * (Real.pi * y) * kN y := rfl
  rw [e]
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_w1 (x : ℝ) (hx : kD x ≠ 0) : HasDerivAt w1 (w2 x) x := by
  have h := ((((hasDerivAt_kN x).const_mul (2 * Real.pi)).mul (hasDerivAt_kM x))).div ((hasDerivAt_kD x).pow 3)
    (pow_ne_zero 3 hx)
  have e : w1 = fun y : ℝ => 2 * Real.pi * kN y * kM y / kD y ^ 3 := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  unfold w2 kP2 kM
  rw [show (3:ℕ) - 1 = 2 from rfl]
  push_cast
  field_simp
  ring

theorem g2i_sound : ((G2I.1 : ℤ) : ℝ) / DZ ≤ 1 + 4 * gam ∧ 1 + 4 * gam ≤ ((G2I.2 : ℤ) : ℝ) / DZ := by
  have h := gam_bounds
  simp only [G2I, DZ]; push_cast
  constructor <;> linarith [h.1, h.2]

/-! ### the convexity cell is sound -/

set_option maxHeartbeats 8000000 in
theorem cellConv_sound (c : CellN) (hc : c.convOk = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    kD x < 0 ∧ 0 ≤ w2 x := by
  simp only [CellN.convOk, CellN.okD, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hcC, hD2⟩, hP2⟩ := hc
  obtain ⟨⟨hC1, hC2⟩, ⟨hS1, hS2⟩, ⟨hB1, hB2⟩, hBB0⟩ := cellN_trig c hcC x hx1 hx2
  have hD0 := DZ_pos
  have hBI : ((c.BI.1 : ℤ) : ℝ) / DZ ≤ Real.pi * x ∧ Real.pi * x ≤ ((c.BI.2 : ℤ) : ℝ) / DZ := by
    simp only [CellN.BI, Int.cast_natCast]; exact ⟨hB1, hB2⟩
  have hBI0 : (0:ℤ) ≤ c.BI.1 := Int.natCast_nonneg _
  have hP := imulPP_sound GAMI c.BI (by decide) hBI0 gami_sound hBI
  have hP0 : (0:ℤ) ≤ c.PGI.1 := by
    show (0:ℤ) ≤ zfdiv (GAMI.1 * c.BI.1)
    exact zfdiv_nonneg (mul_nonneg (by decide) hBI0)
  have hT := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hN : ((c.NI.1 : ℤ) : ℝ) / DZ ≤ kN x ∧ kN x ≤ ((c.NI.2 : ℤ) : ℝ) / DZ :=
    isubZ_sound _ _ ⟨hC1, hC2⟩ hT
  have hG1S := imulP_sound G1I c.SXZ (by decide) g1i_sound ⟨hS1, hS2⟩
  have hPC := imulP_sound c.PGI c.CXZ hP0 hP ⟨hC1, hC2⟩
  have h00 : (((0, 0) : ℤ × ℤ).1 : ℝ) / DZ ≤ (0:ℝ) ∧ (0:ℝ) ≤ (((0, 0) : ℤ × ℤ).2 : ℝ) / DZ := by simp
  have hNb0 := isubZ_sound (0, 0) _ h00 (iaddZ_sound _ _ hG1S hPC)
  have hNb : ((c.NbI.1 : ℤ) : ℝ) / DZ ≤ kNb x ∧ kNb x ≤ ((c.NbI.2 : ℤ) : ℝ) / DZ := by
    have e : kNb x = 0 - ((1 + 2 * gam) * Real.sin (Real.pi * x) + 2 * gam * (Real.pi * x) * Real.cos (Real.pi * x)) := by
      unfold kNb; ring
    rw [e]; exact hNb0
  have hBB := imulPP_sound c.BI c.BI hBI0 hBI0 hBI hBI
  have h2BB := imulZZ_sound 2 _ hBB.1 hBB.2
  have h11 : ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).1 : ℝ) / DZ ≤ (1:ℝ) ∧ (1:ℝ) ≤ ((((DZ : ℤ), (DZ : ℤ)) : ℤ × ℤ).2 : ℝ) / DZ := by
    simp only [Int.cast_natCast, div_self DZ_ne]; exact ⟨le_rfl, le_rfl⟩
  have hDD0 := isubZ_sound _ _ h11 h2BB
  have hDD : ((c.DI.1 : ℤ) : ℝ) / DZ ≤ kD x ∧ kD x ≤ ((c.DI.2 : ℤ) : ℝ) / DZ := by
    have e : kD x = 1 - ((2 : ℤ) : ℝ) * ((Real.pi * x) * (Real.pi * x)) := by unfold kD; push_cast; ring
    rw [e]; exact hDD0
  have hNbD := imulD_sound c.NbI c.DI hNb hDD
  have h4B := imulZZ_sound 4 c.BI hBI.1 hBI.2
  have h4B0 : (0:ℤ) ≤ (imulZZ 4 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 4 then ((4:ℤ) * c.BI.1, (4:ℤ) * c.BI.2) else ((4:ℤ) * c.BI.2, (4:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h4BN := imulP_sound (imulZZ 4 c.BI) c.NI h4B0 h4B hN
  have hM0 := iaddZ_sound _ _ hNbD h4BN
  have hM : ((c.MI.1 : ℤ) : ℝ) / DZ ≤ kM x ∧ kM x ≤ ((c.MI.2 : ℤ) : ℝ) / DZ := by
    have e : kM x = kNb x * kD x + ((4 : ℤ) : ℝ) * (Real.pi * x) * kN x := by unfold kM; push_cast; ring
    rw [e]; exact hM0
  -- N₂
  have hPS := imulP_sound c.PGI c.SXZ hP0 hP ⟨hS1, hS2⟩
  have hG2C := imulP_sound G2I c.CXZ (by decide) g2i_sound ⟨hC1, hC2⟩
  have hN20 := isubZ_sound _ _ hPS hG2C
  have hN2 : ((c.N2I.1 : ℤ) : ℝ) / DZ ≤ kN2 x ∧ kN2 x ≤ ((c.N2I.2 : ℤ) : ℝ) / DZ := by
    have e : kN2 x = 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) - (1 + 4 * gam) * Real.cos (Real.pi * x) := by
      unfold kN2; ring
    rw [e]; exact hN20
  -- P
  have hDsq := imulD_sound c.DI c.DI hDD hDD
  have hA := imulD_sound c.N2I (imulD c.DI c.DI) hN2 hDsq
  have hND := imulD_sound c.NI c.DI hN hDD
  have h4ND := imulZZ_sound 4 _ hND.1 hND.2
  have h8B := imulZZ_sound 8 c.BI hBI.1 hBI.2
  have h8B0 : (0:ℤ) ≤ (imulZZ 8 c.BI).1 := by
    show (0:ℤ) ≤ (if (0:ℤ) ≤ 8 then ((8:ℤ) * c.BI.1, (8:ℤ) * c.BI.2) else ((8:ℤ) * c.BI.2, (8:ℤ) * c.BI.1)).1
    rw [if_pos (by decide)]
    exact mul_nonneg (by decide) hBI0
  have h8BM := imulP_sound (imulZZ 8 c.BI) c.MI h8B0 h8B hM
  have hIn := iaddZ_sound _ _ (iaddZ_sound _ _ hA h4ND) h8BM
  have hNIn := imulD_sound c.NI _ hN hIn
  have hMM := imulD_sound c.MI c.MI hM hM
  have hPP := iaddZ_sound _ _ hMM hNIn
  have hkP : ((c.P2I.1 : ℤ) : ℝ) / DZ ≤ kP2 x := by
    have e : kP2 x = kM x * kM x + kN x * (kN2 x * (kD x * kD x) + ((4 : ℤ) : ℝ) * (kN x * kD x)
        + ((8 : ℤ) : ℝ) * (Real.pi * x) * kM x) := by unfold kP2; push_cast; ring
    rw [e]; exact hPP.1
  have hkD : kD x < 0 := by
    have : ((c.DI.2 : ℤ) : ℝ) < 0 := by exact_mod_cast hD2
    linarith [hDD.2, div_neg_of_neg_of_pos this hD0]
  have hP20 : (0:ℝ) ≤ kP2 x := le_trans (div_nonneg (by exact_mod_cast hP2) hD0.le) hkP
  refine ⟨hkD, ?_⟩
  unfold w2
  exact div_nonneg (mul_nonneg (by positivity) hP20) (by positivity)

/-! ### the tangent minorant on a convex range -/

theorem tangent_le {A B : ℝ} (hc : ∀ x : ℝ, A ≤ x → x ≤ B → kD x < 0 ∧ 0 ≤ w2 x) {q s : ℝ}
    (hq1 : A ≤ q) (hq2 : q ≤ B) (hs1 : A ≤ s) (hs2 : s ≤ B) : wfun q + w1 q * (s - q) ≤ wfun s := by
  have hW : ∀ ξ : ℝ, A ≤ ξ → ξ ≤ B → HasDerivAt wfun (w1 ξ) ξ := fun ξ h1 h2 =>
    hasDerivAt_wfun ξ (hc ξ h1 h2).1.ne
  have hW1 : ∀ ξ : ℝ, A ≤ ξ → ξ ≤ B → HasDerivAt w1 (w2 ξ) ξ := fun ξ h1 h2 =>
    hasDerivAt_w1 ξ (hc ξ h1 h2).1.ne
  rcases lt_trichotomy q s with hqs | hqs | hqs
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hqs
      (fun y hy => (hW y (hq1.trans hy.1) (hy.2.trans hs2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hq1.trans hy.1.le) (hy.2.le.trans hs2))
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hξ.1
      (fun y hy => (hW1 y (hq1.trans hy.1) (hy.2.trans (hξ.2.le.trans hs2))).continuousAt.continuousWithinAt)
      (fun y hy => hW1 y (hq1.trans hy.1.le) (hy.2.le.trans (hξ.2.le.trans hs2)))
    have h2 := (hc η (hq1.trans hη.1.le) (hη.2.le.trans (hξ.2.le.trans hs2))).2
    have hmono : w1 q ≤ w1 ξ := by
      have hpos : 0 < ξ - q := by linarith [hξ.1]
      have : w1 ξ - w1 q = w2 η * (ξ - q) := by rw [hηe]; field_simp
      nlinarith
    have : wfun s - wfun q = w1 ξ * (s - q) := by
      have hne : s - q ≠ 0 := by linarith
      rw [hξe]; field_simp
    nlinarith
  · rw [hqs]; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hqs
      (fun y hy => (hW y (hs1.trans hy.1) (hy.2.trans hq2)).continuousAt.continuousWithinAt)
      (fun y hy => hW y (hs1.trans hy.1.le) (hy.2.le.trans hq2))
    obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hξ.2
      (fun y hy => (hW1 y ((hs1.trans hξ.1.le).trans hy.1) (hy.2.trans hq2)).continuousAt.continuousWithinAt)
      (fun y hy => hW1 y ((hs1.trans hξ.1.le).trans hy.1.le) (hy.2.le.trans hq2))
    have h2 := (hc η ((hs1.trans hξ.1.le).trans hη.1.le) (hη.2.le.trans hq2)).2
    have hmono : w1 ξ ≤ w1 q := by
      have hpos : 0 < q - ξ := by linarith [hξ.2]
      have : w1 q - w1 ξ = w2 η * (q - ξ) := by rw [hηe]; field_simp
      nlinarith
    have : wfun q - wfun s = w1 ξ * (q - s) := by
      have hne : q - s ≠ 0 := by linarith
      rw [hξe]; field_simp
    nlinarith

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-! ### chains -/

theorem ccell_LN {a b : ℕ} (hb : b < KB) : (ccell a b).LN = a := by
  simp only [ccell, CellN.LN, Nat.add_eq, Nat.mul_eq]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem ccell_UN {a b : ℕ} (hb : b < KB) : (ccell a b).UN = b := by
  simp only [ccell, CellN.UN, Nat.add_eq, Nat.mul_eq]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem chainOk_sound : ∀ (l : List ℕ) (a : ℕ), chainOk a l = true → l ≠ [] →
    ∀ x : ℝ, (a : ℝ) / SC ≤ x → x ≤ (chainLast a l : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  intro l
  induction l with
  | nil => intro a _ h; exact absurd rfl h
  | cons b r ih =>
    intro a h _ x hx1 hx2
    have h' : (Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && chainOk b r) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨⟨⟨hab, hbK⟩, hcv⟩, hr⟩ := h'
    have hbK' : b < KB := by simp only [Nat.add_eq] at hbK; omega
    rcases le_or_gt x ((b : ℝ) / SC) with hxb | hxb
    · exact cellConv_sound (ccell a b) hcv x (by rw [ccell_LN hbK']; exact hx1) (by rw [ccell_UN hbK']; exact hxb)
    · cases r with
      | nil =>
        have e : chainLast a [b] = b := rfl
        rw [e] at hx2; linarith
      | cons c r' =>
        have e : chainLast a (b :: c :: r') = chainLast b (c :: r') := rfl
        rw [e] at hx2
        exact ih b hr (List.cons_ne_nil c r') x hxb.le hx2

/-- a point function whose triples are sound at every grid point -/
def PTF (f : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, (lo32 (f x) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 (f x)) ((x : ℝ) / SC)

theorem ptl_sound : ∀ (L : List (ℕ × ℕ)), ptlOk L = true → PTF (ptl L) := by
  intro L
  induction L with
  | nil =>
    intro _ x
    show (lo32 0 : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 0) ((x : ℝ) / SC)
    rw [lo32_zero, hi32_zero]
    exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
  | cons e r ih =>
    intro h x
    have h' : (pt3e e.1 e.2 && ptlOk r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨he, hr⟩ := h'
    show (lo32 (Bool.rec (motive := fun _ => ℕ) (ptl r x) e.2 (Nat.beq e.1 x)) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC)
      ∧ PS (hi32 (Bool.rec (motive := fun _ => ℕ) (ptl r x) e.2 (Nat.beq e.1 x))) ((x : ℝ) / SC)
    cases hb : Nat.beq e.1 x
    · exact ih hr x
    · have hx : e.1 = x := by simpa using hb
      simp only [pt3e, Bool.and_eq_true] at he
      rw [← hx]
      exact ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩

theorem term_boundf {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (bit : Bool) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : tok bit L U QS (selXf bit top bk f L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (tchg bit L U QS (selXf bit top bk f L U QS) (selU bit tD bD QS U) (selD bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := lb3_sound hlb L U s hs1 hs2
    simp only [tval, selXf, tchg, Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [tok, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨hP, hM⟩, hup⟩, hdn⟩ := hok
    simp only [selXf, selU, selD, tval, tP, tM, tK, tchg] at hP hM hup hdn ⊢
    have hp := hpt QS
    obtain ⟨d, hd1, hd2, hd3⟩ := slope_pair hD L U QS (hi32 (f QS)) hLQ hQU hp.2 hP hM
      (hup.imp (fun h => h) (fun h => h)) (hdn.imp (fun h => h) (fun h => h)) s hs1 hs2
    refine ⟨d, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    rw [hSC] at hw
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun ((QS : ℝ) / 32768) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    have e : ((Nat.max (Nat.mul (Nat.sub U QS) (Nat.sub 4000000000 (Nat.add (hi32 (hi32 (f QS))) (lo32 (lbDr tD bD QS U)))))
        (Nat.mul (Nat.sub QS L) (Nat.sub 4000000000 (Nat.add (hi32 (lbDr tD bD L QS)) (lo32 (hi32 (f QS)))))) : ℕ) : ℝ)
        = ((max ((U - QS) * (4000000000 - (hi32 (hi32 (f QS)) + lo32 (lbDr tD bD QS U))))
          ((QS - L) * (4000000000 - (hi32 (lbDr tD bD L QS) + lo32 (hi32 (f QS))))) : ℕ) : ℝ) := rfl
    rw [e]
    rw [hSC] at hd3
    nlinarith [hd3, hw']

/-- one pair term in a convex basin: the tangent at `QS` (expanded terms, no charge) or the zero-order bound -/
theorem cterm_bound {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk) (hpt : PTF f) (bit : Bool)
    (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U) (c : List ℕ)
    (hok : ctok bit L U QS (selXf bit top bk f L U QS) c = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := lb3_sound hlb L U s hs1 hs2
    simp only [tval, selXf, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [ctok, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨⟨hP, hM⟩, hlen⟩, hch⟩, hlast⟩ := hok
    simp only [selXf, tval, tP, tM, tK] at hP hM ⊢
    have hp := hpt QS
    have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
    have hconv : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
      intro x h1 h2
      exact chainOk_sound c L hch hne x h1 (by rw [hlast]; exact h2)
    set q : ℝ := (QS : ℝ) / SC with hq
    have hq1 : (L : ℝ) / SC ≤ q := div_le_div_of_nonneg_right (by exact_mod_cast hLQ) (by norm_num [SC])
    have hq2 : q ≤ (U : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hQU) (by norm_num [SC])
    have htan := tangent_le hconv hq1 hq2 hs1 hs2
    have hU1 := U1_posR
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    have hq0 : lo32 (hi32 (f QS)) ≠ 0 := by omega
    have hm0 : hi32 (hi32 (f QS)) ≠ 0 := by omega
    obtain ⟨-, hPq⟩ := hp.2.1 hq0
    obtain ⟨-, hMq⟩ := hp.2.2 hm0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨w1 q, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun q := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    rw [hSC] at hq
    rw [← hq]
    nlinarith [htan, hw']

/-- one pair term of the mixed test: convex (tangent, no charge), slope (derivative charge) or zero-order -/
theorem mterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
    (hD : LBSoundD tD bD) (hpt : PTF f) (vb bit : Bool) (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U) (c : List ℕ)
    (hok : mtok vb bit L U QS (selXf bit top bk f L U QS) (selUv vb bit tD bD QS U) (selDv vb bit tD bD L QS) c = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg vb bit L U QS (selXf bit top bk f L U QS) (selUv vb bit tD bD QS U) (selDv vb bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  cases vb
  · exact term_boundf hlb hD hpt bit L U QS hLQ hQU hok s hs1 hs2
  · obtain ⟨d, h1, h2, h3⟩ := cterm_bound hlb hpt bit L U QS hLQ hQU c hok s hs1 hs2
    refine ⟨d, h1, h2, ?_⟩
    simp only [mchg, Nat.cast_zero, mul_zero, sub_zero]
    exact h3

theorem bforce_eq (b : Bool) (k : Bool → Bool) : bforce b k = k b := by cases b <;> rfl

/-- every point of a certified region is convex -/
def RegSound (R : List (ℕ × ℕ × List ℕ)) : Prop :=
  ∀ r ∈ R, ∀ x : ℝ, (r.1 : ℝ) / SC ≤ x → x ≤ (r.2.1 : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x

theorem regOk_sound : ∀ (R : List (ℕ × ℕ × List ℕ)), regOk R = true → RegSound R := by
  intro R
  induction R with
  | nil => intro _ r hr; exact absurd hr (List.not_mem_nil)
  | cons r0 R ih =>
    intro h r hr x hx1 hx2
    have h' : (Nat.ble 1 r0.2.2.length && chainOk r0.1 r0.2.2 && Nat.beq (chainLast r0.1 r0.2.2) r0.2.1 && regOk R) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨hlen, hch⟩, hlast⟩, hR⟩ := h'
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hne : r.2.2 ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
      exact chainOk_sound r.2.2 r.1 hch hne x hx1 (by rw [hlast]; exact hx2)
    · exact ih hR r hr' x hx1 hx2

theorem inReg_sound {R : List (ℕ × ℕ × List ℕ)} (hR : RegSound R) {lo hi : ℕ} (h : inReg R lo hi = true) :
    ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
  induction R with
  | nil => exact absurd h (by simp [inReg])
  | cons r R ih =>
    intro x hx1 hx2
    have h' : ((Nat.ble r.1 lo && Nat.ble hi r.2.1) || inReg R lo hi) = true := h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h'
    rcases h' with ⟨h1, h2⟩ | h'
    · have e1 : (r.1 : ℝ) / SC ≤ (lo : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h1) (by norm_num [SC])
      have e2 : (hi : ℝ) / SC ≤ (r.2.1 : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h2) (by norm_num [SC])
      exact hR r List.mem_cons_self x (e1.trans hx1) (hx2.trans e2)
    · exact ih (fun r' hr' => hR r' (List.mem_cons_of_mem r hr')) h' x hx1 hx2

/-- a pair term on a convex range: the tangent at `QS` (expanded) or the zero-order bound -/
theorem convterm_bound {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk) (hpt : PTF f) (bit : Bool)
    (L U QS : ℕ) (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hconv : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x)
    (hok : Bool.rec (motive := fun _ => Bool) true
      (Nat.ble 1 (lo32 (hi32 (selXf bit top bk f L U QS))) && Nat.ble 1 (hi32 (hi32 (selXf bit top bk f L U QS)))) bit = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        ≤ 327680000000000 * wfun s := by
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  cases bit
  · refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
    have h := lb3_sound hlb L U s hs1 hs2
    simp only [tval, selXf, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
    linarith
  · simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨hP, hM⟩ := hok
    simp only [selXf, tval, tP, tM, tK] at hP hM ⊢
    have hp := hpt QS
    set q : ℝ := (QS : ℝ) / SC with hq
    have hq1 : (L : ℝ) / SC ≤ q := div_le_div_of_nonneg_right (by exact_mod_cast hLQ) (by norm_num [SC])
    have hq2 : q ≤ (U : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast hQU) (by norm_num [SC])
    have htan := tangent_le hconv hq1 hq2 hs1 hs2
    have hU1 := U1_posR
    have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
    have hq0 : lo32 (hi32 (f QS)) ≠ 0 := by omega
    have hm0 : hi32 (hi32 (f QS)) ≠ 0 := by omega
    obtain ⟨-, hPq⟩ := hp.2.1 hq0
    obtain ⟨-, hMq⟩ := hp.2.2 hm0
    simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
    rw [div_le_iff₀ hU1, eU] at hPq hMq
    refine ⟨w1 q, by push_cast; linarith, by push_cast; linarith, ?_⟩
    have hw := hp.1
    have hw' : (lo32 (f QS) : ℝ) ≤ 10000000000 * wfun q := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hw; linarith
    rw [hSC] at hq
    rw [← hq]
    nlinarith [htan, hw']

/-- one pair term of the slope test: convex when its range lies in a certified convex region (tangent, no charge, no
derivative reads), else charged from the derivative reads -/
theorem rterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : List (ℕ × ℕ × List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : RegSound R) (bit : Bool) (L U QS : ℕ)
    (hLQ : L ≤ QS) (hQU : QS ≤ U)
    (hok : rtok (inReg R L U) bit L U QS (selXf bit top bk f L U QS) (selUv (inReg R L U) bit tD bD QS U)
      (selDv (inReg R L U) bit tD bD L QS) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP bit (selXf bit top bk f L U QS) : ℝ) - (tK bit : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK bit : ℝ) - (tM bit (selXf bit top bk f L U QS) : ℝ) ∧
      32768 * (tval bit (selXf bit top bk f L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg (inReg R L U) bit L U QS (selXf bit top bk f L U QS) (selUv (inReg R L U) bit tD bD QS U)
          (selDv (inReg R L U) bit tD bD L QS) : ℝ)
        ≤ 327680000000000 * wfun s := by
  revert hok
  cases hc : inReg R L U
  · intro hok
    exact term_boundf hlb hD hpt bit L U QS hLQ hQU hok s hs1 hs2
  · intro hok
    obtain ⟨d, h1, h2, h3⟩ := convterm_bound hlb hpt bit L U QS hLQ hQU (inReg_sound hR hc) hok s hs1 hs2
    refine ⟨d, h1, h2, ?_⟩
    simp only [mchg, Nat.cast_zero, mul_zero, sub_zero]
    exact h3

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
-- CONV-END
