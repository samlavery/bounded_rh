/-
AMW/MinMode.lean — the minorant term of the slope test: per expanded pair term, a convex combination (10-bit weight)
of at most two certified lines among the constant and extended tangents at grid points of the term's range, in
mvt-engine's encoding (κ, λ, j₁, j₂), re-expressed at the expansion point as a packed triple (no charge).

Term data (expanded terms only; the expansion set T marks them): a 2-bit kind c (κ = c + 1: 1 tangent at p₁,
2 constant and tangent at p₁ with weights 1024 − λ, λ, 3 tangents at p₁, p₂ with weights 1024 − λ, λ), the 4-bit grid
index j₁, then λ (10 bits) for κ ≥ 2, then j₂ (4 bits) for κ = 3; p = `mgpt L U j`, the 256-grid point at
L + (U − L)·j/8 clamped into [L, U] (mvt-engine's `gpt`).  The tangent at p is `lmE` with the convex region of the
integer nearest p.  Soundness: `mterm_bound`, with the conclusion of `rterm_boundc`.
-/
import AMW.TanChord

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr

/-- the grid point `j ∈ [0, 8]` of the range `[L, U]`: `L + (U − L) j / 8` rounded down to a multiple of `256`,
clamped to the multiples of `256` inside `[L, U]` -/
def mgpt (L U j : ℕ) : ℕ :=
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L 255) 8) 8) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U 8) 8) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) 8) 8) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the constant term: the pyramid bound on `[L, U]` with slope exactly `0` -/
def lmK (top : ℕ) (bk : ℕ → ℕ) (L U : ℕ) : ℕ := lmPk (lb top bk L U) 2000000000 2000000000

/-- the extended tangent at `p`, in the convex region of the integer nearest to `p` -/
def lmTg (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (L U QS p : ℕ) : ℕ :=
  lmE f tD bD R (Nat.shiftRight (Nat.add p 16384) 15) L U QS p

/-- the minorant of kind `κ ∈ {1, 2, 3}` with weight `λ` and grid indices `j₁`, `j₂` -/
def lmMT (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))
    (L U QS κ lam j1 j2 : ℕ) : ℕ :=
  forceR (mgpt L U j1) fun p1 =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (mgpt L U j2) fun p2 => pkComb (Nat.sub 1024 lam) (lmTg f tD bD R L U QS p1) (lmTg f tD bD R L U QS p2))
      (pkComb lam (lmTg f tD bD R L U QS p1) (lmK top bk L U)) (Nat.beq κ 2))
    (lmTg f tD bD R L U QS p1) (Nat.ble κ 1)

/-- the length of an expanded term's data from its kind field `c` (κ = c + 1) -/
def mlen (c : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 20 16 (Nat.beq c 1)) 6 (Nat.beq c 0)
/-- the data stream after a term (`b` its expansion bit, `e` the stream at the term) -/
def mNext (b : Bool) (e : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) e (Nat.shiftRight e (mlen (Nat.land e 3))) b
/-- a term's packed read: zero order (`b` false), else the minorant read from the stream `e` -/
def lmMX (b : Bool) (e : ℕ) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ)
    (R : ℕ × ℕ × List (List ℕ)) (L U QS : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (selXf false top bk f L U QS)
    (lmMT top bk f tD bD R L U QS (Nat.add 1 (Nat.land e 3)) (Nat.land (Nat.shiftRight e 6) 1023)
      (Nat.land (Nat.shiftRight e 2) 15) (Nat.land (Nat.shiftRight e 16) 15)) b

/-! ### soundness -/

theorem lmK_pk {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (L U QS : ℕ) : PkSpec L U QS (lmK top bk L U) := by
  right
  refine ⟨_, _, _, rfl, by norm_num, fun s hs1 hs2 => ⟨0, by norm_num, by norm_num, ?_⟩⟩
  have h := hlb L U s hs1 hs2
  have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
  simp only [zero_mul, mul_zero, add_zero]
  have : (wfun s) = AMW.wfunAM s := rfl
  linarith

theorem lmTg_pk {f : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hD : LBSoundD tD bD)
    (hpt : PTF f) (hR : rgOk R = true) (L U QS p : ℕ) : PkSpec L U QS (lmTg f tD bD R L U QS p) :=
  lmE_pk hD hpt hR _ L U QS p

theorem lmMT_pk {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (L U QS κ lam j1 j2 : ℕ) : PkSpec L U QS (lmMT top bk f tD bD R L U QS κ lam j1 j2) := by
  unfold lmMT
  simp only [forceR_eq]
  cases Nat.ble κ 1
  · cases Nat.beq κ 2
    · exact pkComb_spec (lmTg_pk hD hpt hR _ _ _ _) (lmTg_pk hD hpt hR _ _ _ _) _
    · exact pkComb_spec (lmTg_pk hD hpt hR _ _ _ _) (lmK_pk hlb _ _ _) _
  · exact lmTg_pk hD hpt hR _ _ _ _

theorem lb_term {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (L U QS X EU ED : ℕ)
    (hX : X = lb top bk L U) (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP false X : ℝ) - (tK false : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK false : ℝ) - (tM false X : ℝ) ∧
      32768 * (tval false X : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg false false L U QS X EU ED : ℝ) ≤ 327680000000000 * wfun s := by
  refine ⟨0, by simp [tP, tK], by simp [tM, tK], ?_⟩
  have h := hlb L U s hs1 hs2
  have h' := (div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)).mp h
  have e1 : tval false X = lb top bk L U := hX
  have e2 : mchg false false L U QS X EU ED = 0 := rfl
  rw [e1, e2]
  have : (wfun s) = AMW.wfunAM s := rfl
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, sub_zero]
  linarith

/-- **one pair term of the minorant slope test**: zero order when not expanded, else the minorant read from the data
stream, with no charge; the conclusion of `rterm_boundc` with `cv = bit = b` -/
theorem minterm_bound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    (b : Bool) (e L U QS EU ED : ℕ)
    (hok : rtok b b L U QS (lmMX b e top bk f tD bD R L U QS) EU ED = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ d : ℝ, (tP b (lmMX b e top bk f tD bD R L U QS) : ℝ) - (tK b : ℝ) ≤ 1000000000 * d ∧
      1000000000 * d ≤ (tK b : ℝ) - (tM b (lmMX b e top bk f tD bD R L U QS) : ℝ) ∧
      32768 * (tval b (lmMX b e top bk f tD bD R L U QS) : ℝ) + 327680000000000 * (d * (s - (QS : ℝ) / 32768))
        - 10 * (mchg b b L U QS (lmMX b e top bk f tD bD R L U QS) EU ED : ℝ) ≤ 327680000000000 * wfun s := by
  cases b
  · exact lb_term hlb L U QS _ EU ED rfl s hs1 hs2
  · exact spec_term (lmMT_pk hlb hD hpt hR L U QS _ _ _ _) hok s hs1 hs2

end AMW.Cert.PyrD

end
