#!/usr/bin/env python3
"""Pyr2.lean: the derivative tables as ONE pyramid of 64-bit entries (low 32 bits: a lower bound of `w' + 2`, high 32
bits: a lower bound of `2 − w'`, units 1/U1, 0 claims nothing), read with componentwise minima.  The lookup, the
verification and the soundness are the pyramid of PyrCheck.lean (typh's five-point-pyramid-2 layout, Apache-2.0)
with 64-bit fields, `pmin` for `nmin`, `ple` for `≤`, and the pointwise pair semantics `PS`."""
import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, "..", "pyr", "PyrCheck.lean"), encoding="utf-8").read()

def grab(start, end):
    a = src.index(start); b = src.index(end, a)
    return src[a:b]

def sub_all(s, reps):
    for x, y in reps:
        assert x in s, x
        s = s.replace(x, y)
    return s

# ---------------- definitions ----------------
entB = grab("def entB (X l i j : ℕ) : ℕ :=", "/-- the entry for the level-`l` cell `i` -/")
entB = sub_all(entB, [("def entB (X l i j : ℕ)", "def entB2 (X l i j : ℕ)"), ("  fld (Nat.shiftRight X 5)", "  fld2 (Nat.shiftRight X 5)")])
entry = grab("def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=", "/-- the size `t` of the next block")
entry = sub_all(entry, [("def entry (top", "def entry2 (top"), ("fun j => entB (bk j)", "fun j => entB2 (bk j)"), ("(fld top (", "(fld2 top (")])
dcov = grab("def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=", "/-- 4-bit bit lengths")
dcov = sub_all(dcov, [("def dcov (top", "def dcov2 (top"), ("fun h => entry top bk l h", "fun h => entry2 top bk l h"),
                      ("(nmin v (ih g'))", "(pmin v (ih g'))")])
lb = grab("def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=", "/-! ### verification of a table -/")
lb = sub_all(lb, [("def lb (top", "def lb2 (top"), ("dcov top bk k", "dcov2 top bk k")])
blockX = grab("def blockOkX (X j : ℕ) : Bool :=", "def blockOk (X j : ℕ)")
blockX = sub_all(blockX, [("def blockOkX (X j : ℕ)", "def blockOk2X (X j : ℕ)"),
    ("(fun t => cellOk r (Nat.add (Nat.shiftLeft j D) t) (fld Y", "(fun t => cellOk2 r (Nat.add (Nat.shiftLeft j D) t) (fld2 Y"),
    ("""         Nat.ble (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
           (nmin (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                 (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))""",
     """         ple (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
           (pmin (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                 (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))""")])
topv = grab("def topv (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=", "/-- every top entry")
topv = sub_all(topv, [("def topv (top", "def topv2 (top"), ("(fld top (", "(fld2 top ("), ("(fld (Nat.shiftRight (bk i) 5) 0)", "(fld2 (Nat.shiftRight (bk i) 5) 0)")])
topOk = grab("def topOk (top : ℕ) (bk : ℕ → ℕ) : Bool :=", "/-! ### soundness -/")
topOk = sub_all(topOk, [("def topOk (top", "def topOk2 (top"),
    ("""    Nat.ble (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      (nmin (topv top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))""",
     """    ple (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      (pmin (topv2 top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv2 top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))""")])

DEFS = f"""
/-! ###### the derivative tables as one pyramid of pairs ######

The two derivative tables share one block structure, so they are stored as one pyramid of 64-bit entries: the low
32 bits bound `w' + 2` below and the high 32 bits bound `2 − w'` below (units `1/U1`; a half `0` claims nothing).
The cover arithmetic is that of `Pyr.lb` (pyramid layout adapted from five-point-pyramid-2 by typh, Apache-2.0); the
entries read are combined by the componentwise minimum `pmin`, and the verification checks every coarser entry
componentwise against its children (`ple`). -/

section MvtPairDefs

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- field `i` (64 bits) of a packed natural -/
def fld2 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 64 i)) 18446744073709551615

/-- the two halves of a pair -/
def lo32 (v : ℕ) : ℕ := Nat.land v 4294967295
def hi32 (v : ℕ) : ℕ := Nat.shiftRight v 32

/-- the componentwise minimum of two pairs -/
def pmin (a b : ℕ) : ℕ := Nat.add (nmin (lo32 a) (lo32 b)) (Nat.shiftLeft (nmin (hi32 a) (hi32 b)) 32)

/-- the componentwise order of pairs -/
def ple (a b : ℕ) : Bool := Nat.ble (lo32 a) (lo32 b) && Nat.ble (hi32 a) (hi32 b)

{entB}{entry}{dcov}{lb}/-- a pair claim on the level-`l` cell `i`: both halves pass the derivative cell check -/
def cellOk2 (l i v : ℕ) : Bool := cellOkD true l i (lo32 v) && cellOkD false l i (hi32 v)

{blockX}def blockOk2 (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOk2X X j) true (Nat.beq X 0)

{topv}{topOk}end Zeta23Ext.Bridge.ThreePoint.PyrD

end MvtPairDefs
"""

# ---------------- soundness ----------------
mid = grab("def BlockSound (X j : ℕ) : Prop :=", "/-- the cover of the level-`k` cells `g .. ib` reads only cells")
mid = sub_all(mid, [
 ("def BlockSound (X j : ℕ) : Prop :=", "def BlockSound2 (X j : ℕ) : Prop :="),
 ("CS (10 - d) (j * 2 ^ d + t) (fld (X / 32) (2 ^ d - 1 + t))", "CS2 (10 - d) (j * 2 ^ d + t) (fld2 (X / 32) (2 ^ d - 1 + t))"),
 ("theorem blockOkX_sound {X j : ℕ} (h : blockOkX X j = true) : BlockSound X j := by", "theorem blockOk2X_sound {X j : ℕ} (h : blockOk2X X j = true) : BlockSound2 X j := by"),
 ("unfold blockOkX at h", "unfold blockOk2X at h"),
 ("CS (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld (X / 32) (2 ^ (D - e) - 1 + t))", "CS2 (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld2 (X / 32) (2 ^ (D - e) - 1 + t))"),
 ("have hc := cellOk_sound this", "have hc := cellOk2_sound this"),
 ("    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct\n    have h0 := ih",
  "    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct\n    have h0 := ih"),
 ("have hm := CS_min h0 h1\n    rw [hlev] at hm\n    refine CS_mono ?_ hm\n    have a0 : 2 ^ (d + 1) - 1 + 2 * t = 2 ^ (d + 1) - 1 + 2 * t := rfl\n    exact hct",
  "have hm := CS2_min h0 h1\n    rw [hlev] at hm\n    exact CS2_mono hct hm"),
 ("theorem blockOk_sound {X j : ℕ} (h : blockOk X j = true) : BlockSound X j := by", "theorem blockOk2_sound {X j : ℕ} (h : blockOk2 X j = true) : BlockSound2 X j := by"),
 ("unfold blockOk at h", "unfold blockOk2 at h"),
 ("exact blockOkX_sound h", "exact blockOk2X_sound h"),
 ("simp only [Nat.zero_div, fld_zero]; exact CS_zero _ _", "simp only [Nat.zero_div, fld2_zero]; exact CS2_zero _ _"),
 ("theorem topv_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv top bk 10 i = fld (bk i / 32) 0 := by\n  unfold topv",
  "theorem topv2_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv2 top bk 10 i = fld2 (bk i / 32) 0 := by\n  unfold topv2"),
 ("theorem topv_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :\n    topv top bk l i = fld top (2 ^ (19 - l) + i) := by\n  unfold topv",
  "theorem topv2_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :\n    topv2 top bk l i = fld2 top (2 ^ (19 - l) + i) := by\n  unfold topv2"),
 ("theorem top_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :\n    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS (10 + e) i (topv top bk (10 + e) i) := by",
  "theorem top2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :\n    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS2 (10 + e) i (topv2 top bk (10 + e) i) := by"),
 ("    rw [Nat.add_zero, topv_ten]\n    have hB := blockOk_sound", "    rw [Nat.add_zero, topv2_ten]\n    have hB := blockOk2_sound"),
 ("    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle\n    have e1",
  "    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle\n    have e1"),
 ("    have hm := CS_min h0 h1\n    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm\n    rw [topv_top top bk (by omega)]\n    refine CS_mono ?_ hm\n    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]\n    exact hle",
  "    have hm := CS2_min h0 h1\n    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm\n    rw [topv2_top top bk (by omega)]\n    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]\n    exact CS2_mono hle hm"),
 ("theorem entry_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)\n    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS l i (entry top bk l i) := by\n  unfold entry",
  "theorem entry2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)\n    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS2 l i (entry2 top bk l i) := by\n  unfold entry2"),
 ("show CS l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)", "show CS2 l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)"),
 ("have hB := blockOk_sound (hb j hj512)", "have hB := blockOk2_sound (hb j hj512)"),
 ("    unfold entB\n", "    unfold entB2\n"),
 ("exact CS_anc hcs", "exact CS2_anc hcs"),
 ("show CS l i (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))", "show CS2 l i (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))"),
 ("have := top_sound hb ht (l - 10)", "have := top2_sound hb ht (l - 10)"),
 ("rw [show 10 + (l - 10) = l by omega, topv_top top bk (by omega)] at this", "rw [show 10 + (l - 10) = l by omega, topv2_top top bk (by omega)] at this"),
 ("    · exact CS_zero l i", "    · exact CS2_zero l i"),
])
for bad in [" CS ", "CS_", "(CS ", "blockOk_", "topv top", "entry top", "entB (", " fld ("]:
    for line in mid.splitlines():
        if bad in line and "CS2" not in line.replace(bad, "") and bad not in ("CS_",):
            raise SystemExit(f"untransformed: {bad!r} in {line}")
dco = grab("theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ}", "/-- the oracle's soundness: what a verified table certifies -/")
dco = sub_all(dco, [
 ("theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)",
  "theorem dcov2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)"),
 ("      (dcov top bk k ib fuel g : ℝ) / 10000000000 ≤ wfun x := by", "      PS (dcov2 top bk k ib fuel g) x := by"),
 ("    show ((0 : ℕ) : ℝ) / 10000000000 ≤ wfun x\n    simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x", "    exact PS_zero x"),
 ("""    show ((let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (nmin v (dcov top bk k ib fuel g')) (Nat.ble g' ib) : ℕ) : ℝ) / 10000000000 ≤ wfun x""",
  """    show PS (let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry2 top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (pmin v (dcov2 top bk k ib fuel g')) (Nat.ble g' ib)) x"""),
 ("    have hcell : CS (Nat.add k t) h (entry top bk (Nat.add k t) h) := by\n      apply entry_sound hb ht",
  "    have hcell : CS2 (Nat.add k t) h (entry2 top bk (Nat.add k t) h) := by\n      apply entry2_sound hb ht"),
 ("        (entry top bk (Nat.add k t) h : ℝ) / 10000000000 ≤ wfun y := by", "        PS (entry2 top bk (Nat.add k t) h) y := by"),
 ("""      show ((nmin _ _ : ℕ) : ℝ) / 10000000000 ≤ wfun x
      rw [nmin_eq]
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (by norm_num)) (hcellx x h1 hx)
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by norm_num)) (ih g' hle x hx h2)""",
  """      show PS (pmin _ _) x
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact PS_pmin_left (hcellx x h1 hx)
      · exact PS_pmin_right (ih g' hle x hx h2)"""),
])
lbs = grab("/-- the oracle's soundness: what a verified table certifies -/", "end Zeta23Ext.Bridge.ThreePoint.Pyr")
lbs = sub_all(lbs, [
 ("def LBSound (top : ℕ) (bk : ℕ → ℕ) : Prop :=\n  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb top bk lo hi : ℝ) / 10000000000 ≤ wfun x",
  "def LBSound2 (top : ℕ) (bk : ℕ → ℕ) : Prop :=\n  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → PS (lb2 top bk lo hi) x"),
 ("theorem lb_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :\n    LBSound top bk := by\n  intro lo hi x h1 h2\n  unfold lb",
  "theorem lb2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :\n    LBSound2 top bk := by\n  intro lo hi x h1 h2\n  unfold lb2"),
 ("""      show ((dcov top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5))) : ℕ) : ℝ) / 10000000000 ≤ wfun x""",
  """      show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5)))) x"""),
 ("      apply dcov_sound hb ht k", "      apply dcov2_sound hb ht k"),
 ("    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x\n  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x",
  "    · exact PS_zero x\n  · exact PS_zero x"),
])

HEAD = r"""
/-! ### the pyramid of pairs: what a verified table certifies -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.PyrD

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

/-- a pair `v` at the point `x`: each nonzero half bounds its function below (`w' + 2`, `2 − w'`), at a point
where `2 (π x)² > 1` -/
def PS (v : ℕ) (x : ℝ) : Prop :=
  (lo32 v ≠ 0 → kD x < 0 ∧ (lo32 v : ℝ) / U1 ≤ fD true x) ∧
    (hi32 v ≠ 0 → kD x < 0 ∧ (hi32 v : ℝ) / U1 ≤ fD false x)

theorem lo32_eq (v : ℕ) : lo32 v = v % 2 ^ 32 := by
  unfold lo32
  rw [Nat.land_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem hi32_eq (v : ℕ) : hi32 v = v / 2 ^ 32 := by
  unfold hi32
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem pmin_lo (a b : ℕ) : lo32 (pmin a b) = min (lo32 a) (lo32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, lo32_eq (min _ _ + _),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha)]

theorem pmin_hi (a b : ℕ) : hi32 (pmin a b) = min (hi32 a) (hi32 b) := by
  have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
  unfold pmin
  rw [nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hi32_eq (min _ _ + _),
    Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha), Nat.zero_add]

theorem PS_zero (x : ℝ) : PS 0 x := ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩

theorem PS_mono {v v' : ℕ} {x : ℝ} (h : ple v' v = true) (hv : PS v x) : PS v' x := by
  unfold ple at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := hv.1 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h1) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := hv.2 (by omega)
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) U1_posR.le) hb⟩

theorem PS_pmin_left {a b : ℕ} {x : ℝ} (h : PS a x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩

theorem PS_pmin_right {a b : ℕ} {x : ℝ} (h : PS b x) : PS (pmin a b) x := by
  unfold PS
  rw [pmin_lo, pmin_hi]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩
  · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
    exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩

/-- the pair `v` holds on the level-`l` cell `i` -/
def CS2 (l i v : ℕ) : Prop :=
  ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → PS v x

theorem CS2_zero (l i : ℕ) : CS2 l i 0 := fun x _ _ => PS_zero x

theorem CS2_mono {l i v v' : ℕ} (hv : ple v' v = true) (h : CS2 l i v) : CS2 l i v' :=
  fun x h1 h2 => PS_mono hv (h x h1 h2)

theorem CS2_min {l i a b : ℕ} (ha : CS2 l (2 * i) a) (hb : CS2 l (2 * i + 1) b) : CS2 (l + 1) i (pmin a b) := by
  intro x h1 h2
  have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
  · exact PS_pmin_left (ha x (by rw [e1]; exact h1) hx)
  · exact PS_pmin_right (hb x hx (by rw [e2]; exact h2))

theorem CS2_anc {l m i v : ℕ} (h : CS2 (l + m) (i / 2 ^ m) v) : CS2 l i v := by
  intro x h1 h2
  have hp : 0 < 2 ^ m := by positivity
  apply h x
  · refine le_trans (castdiv_le ?_) h1
    calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
      _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
  · refine le_trans h2 (castdiv_le ?_)
    have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
      have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
    calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
      _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring

/-- a pair claim that passes `cellOk2` is sound -/
theorem cellOk2_sound {l i v : ℕ} (h : cellOk2 l i v = true) : CS2 l i v := by
  unfold cellOk2 at h
  rw [Bool.and_eq_true] at h
  have hP := cellOkD_sound h.1
  have hM := cellOkD_sound h.2
  intro x h1 h2
  exact ⟨fun h0 => hP h0 x h1 h2, fun h0 => hM h0 x h1 h2⟩

theorem fld2_zero (i : ℕ) : fld2 0 i = 0 := by
  simp [fld2]

"""
TAIL = r"""
theorem blocks2_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk2 (bk j) j) = true) :
    ∀ j < 512, blockOk2 (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

end Zeta23Ext.Bridge.ThreePoint.PyrD

end
"""
open(os.path.join(HERE, "pyr2_defs.lean"), "w", encoding="utf-8").write(DEFS)
open(os.path.join(HERE, "pyr2_proofs.lean"), "w", encoding="utf-8").write(HEAD + mid + dco + lbs + TAIL)
print("ok", len(DEFS.splitlines()), len((HEAD + mid + dco + lbs + TAIL).splitlines()))
