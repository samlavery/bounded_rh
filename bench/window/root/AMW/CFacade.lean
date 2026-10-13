import AMW.GCellSound

/-!
# AMW/CFacade — the AM cell evaluator behind the interface of the seven-point engine (stage G)

The certificate engine (pyramid of lower bounds, derivative pair pyramid, point table, convex regions, walk) reads a
cell through `CellN` (endpoints packed in `key`) and the facts `cellN_soundZ'`, `cellN_soundWZ`, `cellD_sound`,
`cellConv_sound`, `hasDerivAt_wfun`, `hasDerivAt_w1`.  Here they are supplied by the AM evaluator (`AMW.G.CellA`),
so the engine's definitions and proofs carry over unchanged, with `wfun = wfunAM`, `w1 = w1AM = wfunAM'`,
`w2 = w2AM = w1AM'`.  The AM kernel is differentiable everywhere, so the engine's side condition `kD x < 0` (the
domain of the Montgomery–Taylor closed form) is the constant `kD = −1`.
-/

noncomputable section

namespace AMW.Cert

def SC : ℕ := 32768
def KB : ℕ := 1048576
def SW : ℕ := 10000000000000
def U1 : ℕ := 1000000000
def KU1 : ℕ := 2000000000

theorem SC_eq : SC = AMW.G.SC := rfl

/-- the pair weight and its first two derivatives -/
def wfun (x : ℝ) : ℝ := AMW.wfunAM x
def w1 (x : ℝ) : ℝ := AMW.w1AM x
def w2 (x : ℝ) : ℝ := AMW.w2AM x
/-- the engine's domain condition, vacuous for the AM kernel -/
def kD (_ : ℝ) : ℝ := -1

theorem kD_neg (x : ℝ) : kD x < 0 := by norm_num [kD]

theorem wfun_nonneg (x : ℝ) : 0 ≤ wfun x := AMW.wfunAM_nonneg x

theorem hasDerivAt_wfun (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt wfun (w1 x) x := AMW.hasDerivAt_wfunAM x

theorem hasDerivAt_w1 (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt w1 (w2 x) x := AMW.hasDerivAt_w1AM x

/-- a cell, endpoints packed as `LN * KB + UN` (the engine's convention) -/
structure CellN where
  (key : ℕ) (WN : ℕ)

namespace CellN
def LN (c : CellN) : ℕ := c.key / KB
def UN (c : CellN) : ℕ := c.key % KB
def A (c : CellN) : AMW.G.CellA := ⟨c.LN, c.UN⟩
/-- zero order: `|k| ≥ NLOZ / DHIZ` -/
def okC (c : CellN) : Bool := c.A.ok
def NLOZ (c : CellN) : ℤ := (c.A.KAn : ℤ)
def DHIZ (c : CellN) : ℤ := (AMW.G.DZ : ℤ)
/-- the computed zero-order bound in units `1/SW` -/
def WZ (c : CellN) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.div (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)) c.okC
/-- first order: `w' ∈ [W1LO, W1HI] / U1` -/
def okD (c : CellN) : Bool := c.A.ok && Nat.blt 0 c.A.E2L
def W1LO (c : CellN) : ℤ := ((c.A.W1.lo.fl 1000000).p : ℤ) - ((c.A.W1.lo.fl 1000000).n : ℤ)
def W1HI (c : CellN) : ℤ := ((c.A.W1.hi.ce 1000000).p : ℤ) - ((c.A.W1.hi.ce 1000000).n : ℤ)
/-- second order: `w'' ≥ 0` -/
def convOk (c : CellN) : Bool := c.okD && Nat.blt 0 c.A.E3L && c.A.W2L.nonneg
end CellN

theorem SC_posR : (0 : ℝ) < SC := by norm_num [SC]

theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.okC = true)
    (hW : (w : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ wfun x := by
  have hl := c.A.w_lower hc (x := x) hx1 hx2
  have hD := AMW.G.DZ_pos
  have hSW : (0 : ℝ) < SW := by norm_num [SW]
  have hWr : (w : ℝ) * AMW.G.DZ * AMW.G.DZ ≤ (c.A.KAn : ℝ) * c.A.KAn * SW := by
    have := (Int.cast_le (R := ℝ)).mpr hW
    simp only [CellN.DHIZ, CellN.NLOZ, Int.cast_mul, Int.cast_natCast] at this; exact this
  unfold wfun
  refine le_trans ?_ hl
  generalize (AMW.G.DZ : ℝ) = D at hD hWr ⊢
  generalize (c.A.KAn : ℝ) = K at hWr ⊢
  generalize (SW : ℝ) = S at hSW hWr ⊢
  rw [div_pow, div_le_div_iff₀ hSW (by positivity)]
  linarith

theorem cellN_soundWZ (c : CellN) (x : ℝ) (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    (c.WZ : ℝ) / SW ≤ wfun x := by
  unfold CellN.WZ
  cases hc : c.okC
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
  · simp only
    apply cellN_soundZ' c _ hc _ x hx1 hx2
    simp only [CellN.DHIZ, CellN.NLOZ]
    have h := Nat.div_mul_le_self (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)
    rw [show Nat.div (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)
      = Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW / Nat.mul AMW.G.DZ AMW.G.DZ from rfl]
    generalize Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW / Nat.mul AMW.G.DZ AMW.G.DZ = q at h ⊢
    simp only [Nat.mul_eq] at h
    have h' : ((q * (AMW.G.DZ * AMW.G.DZ) : ℕ) : ℤ) ≤ ((c.A.KAn * c.A.KAn * SW : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith

theorem cellD_sound (c : CellN) (hc : c.okD = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    kD x < 0 ∧ (c.W1LO : ℝ) / U1 ≤ w1 x ∧ w1 x ≤ (c.W1HI : ℝ) / U1 := by
  simp only [CellN.okD, Bool.and_eq_true, Nat.blt_eq] at hc
  have hW := c.A.w1_enc hc.1 hc.2 (x := x) hx1 hx2
  have hD := AMW.G.DZ_pos
  have hU : (0 : ℝ) < U1 := by norm_num [U1]
  have hm : (0 : ℕ) < 1000000 := by norm_num
  refine ⟨kD_neg x, ?_, ?_⟩
  · have h1 := AMW.G.SZ.v_fl_le c.A.W1.lo hm
    have e : ((c.W1LO : ℤ) : ℝ) = (c.A.W1.lo.fl 1000000).v := by
      simp only [CellN.W1LO, AMW.G.SZ.v]; push_cast; ring
    rw [e]; unfold w1
    have h2 := hW.1
    rw [div_le_iff₀ hU]
    have : c.A.W1.lo.v / ((1000000 : ℕ) : ℝ) = (c.A.W1.lo.v / AMW.G.DZ) * U1 := by norm_num [AMW.G.DZ, U1]; ring
    rw [this] at h1
    nlinarith
  · have h1 := AMW.G.SZ.le_v_ce c.A.W1.hi hm
    have e : ((c.W1HI : ℤ) : ℝ) = (c.A.W1.hi.ce 1000000).v := by
      simp only [CellN.W1HI, AMW.G.SZ.v]; push_cast; ring
    rw [e]; unfold w1
    have h2 := hW.2
    rw [le_div_iff₀ hU]
    have : c.A.W1.hi.v / ((1000000 : ℕ) : ℝ) = (c.A.W1.hi.v / AMW.G.DZ) * U1 := by norm_num [AMW.G.DZ, U1]; ring
    rw [this] at h1
    nlinarith

theorem cellConv_sound (c : CellN) (hc : c.convOk = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : kD x < 0 ∧ 0 ≤ w2 x := by
  simp only [CellN.convOk, CellN.okD, Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hok, hE2⟩, hE3⟩, hW⟩ := hc
  exact ⟨kD_neg x, c.A.w2_nonneg hok hE2 hE3 hW hx1 hx2⟩

-- the engine reads these through their soundness lemmas only; the kernel still evaluates them
attribute [irreducible] CellN.okC CellN.NLOZ CellN.DHIZ CellN.WZ CellN.okD CellN.W1LO CellN.W1HI CellN.convOk

end AMW.Cert
