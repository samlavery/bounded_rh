#!/usr/bin/env python3
"""Generate the natural-number leaf/walk checker for n points (Q = n-1 gaps) with the certificate's
weights baked in as numerals.  Scales: coordinates SC = 2^56, cell bounds SW = 10^13, weights SA.
Usage: gen_checkerN.py Q SA aN_list(comma, pairs i<j in order) bN_list(comma) cN NAME
Emits checker_<NAME>.lean with namespace Zeta23Ext.Bridge.ThreePoint.<NAME>.  TABLELESS variant: every piece bound is
computed by the integer pipeline inside the kernel (no cell table in the data)."""
import sys, os
Q = int(sys.argv[1]); SA = int(sys.argv[2])
aN = [int(x) for x in sys.argv[3].split(",")]; bN = [int(x) for x in sys.argv[4].split(",")]
cN = int(sys.argv[5]); NAME = sys.argv[6]
SCE = int(sys.argv[7]) if len(sys.argv) > 7 else 96   # coordinate scale SC = 2^SCE; pieces split at multiples of 2^(SCE-2)
HALF = os.environ.get("HALF") == "1"   # half-space certificate: boxes strictly inside g_0 > g_{Q-1} pass (covered by reflection)
n = Q + 1
pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
assert len(aN) == len(pairs) and len(bN) == Q
V = [f"g{r}" for r in range(Q)]                     # real variables
SKIP = f"Nat.blt b.u{Q-1} b.l0 || " if HALF else ""
ORX = f" ∨ {V[Q-1]} < {V[0]}" if HALF else ""
LEFT = "left; " if HALF else ""
LEAFCASE = (f"""    · simp only [Bool.or_eq_true, Nat.blt_eq] at hleaf
      rcases hleaf with hskip | hleaf
      · right
        obtain ⟨{', '.join(f'h{r}1, h{r}2' for r in range(Q))}⟩ := hm
        have hsk : ((b.u{Q-1} : ℕ) : ℝ) / SC < ((b.l0 : ℕ) : ℝ) / SC :=
          div_lt_div_of_pos_right (by exact_mod_cast hskip) (by norm_num [SC])
        linarith
      · left; exact leaf_sound b hleaf {' '.join(V)} hm
""" if HALF else
    f"""    · exact leaf_sound b hleaf {' '.join(V)} hm
""")
LO = [f"b.l{r}" for r in range(Q)]; HI = [f"b.u{r}" for r in range(Q)]
def rsum(xs): return " + ".join(xs)
def term_lo(i, j): return rsum(LO[i:j]); 
def term_hi(i, j): return rsum(HI[i:j])
def term_g(i, j): return rsum(V[i:j])

out = []; A = out.append
A(f"""
/-! ###### natural-number checker for the {n}-point weighted certificate `{NAME}` ###### -/

section {NAME}Defs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (LN UN : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0, 0⟩⟩

def SC : ℕ := {2**SCE}
def SW : ℕ := 10000000000000
def SC4 : ℕ := {2**(SCE-2)}

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

-- ZSPLICE-DEFS

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> {SCE-2}) + 1) <<< {SCE-2}
      bif Nat.blt q hi then (a, q) :: piecesN fuel q hi else [(a, hi)]

/-- the bound of one piece `[a, b]` (scaled), computed by the integer pipeline -/
def pieceW (a b : ℕ) : ℕ := CellN.WZ ⟨a, b, 0⟩

def chainOKN : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | lo, hi, [] => Nat.ble hi lo
  | lo, hi, (a, b) :: rest => Nat.ble a lo && chainOKN b hi rest

def chainWN : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a, b) :: rest => bif rest.isEmpty then pieceW a b else bif Nat.ble (pieceW a b) (chainWN rest) then pieceW a b else chainWN rest

def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := piecesN 64 lo hi

def termWNcore (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ := bif chainOKN lo hi ps then chainWN ps else 0

def termWN (lo hi : ℕ) : ℕ := termWNcore lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.{NAME}

def SA : ℕ := {SA}
def cN : ℕ := {cN}

structure Box where
  ({' '.join(f'l{r} u{r}' for r in range(Q))} : ℕ)
  deriving DecidableEq

def Box.widthArg (b : Box) : ℕ :=
""")
# widthArg: first index attaining max width
ws = [f"(b.u{r} - b.l{r})" for r in range(Q)]
lines = []
for r in range(Q - 1):
    conds = " && ".join(f"Nat.ble {ws[s]} {ws[r]}" for s in range(r + 1, Q))
    lines.append(f"  {'bif' if r == 0 else 'else bif'} {conds} then {r}")
lines.append(f"  else {Q - 1}")
A("\n".join(lines) + "\n")
A("def Box.mid (b : Box) : ℕ → ℕ\n" + "\n".join(f"  | {r} => (b.l{r} + b.u{r}) / 2" for r in range(Q - 1)) + f"\n  | _ => (b.l{Q-1} + b.u{Q-1}) / 2\n")
A("def Box.setHi (b : Box) (ax : ℕ) (q : ℕ) : Box :=\n  match ax with\n" + "\n".join(f"  | {r} => {{ b with u{r} := q }}" for r in range(Q - 1)) + f"\n  | _ => {{ b with u{Q-1} := q }}\n")
A("def Box.setLo (b : Box) (ax : ℕ) (q : ℕ) : Box :=\n  match ax with\n" + "\n".join(f"  | {r} => {{ b with l{r} := q }}" for r in range(Q - 1)) + f"\n  | _ => {{ b with l{Q-1} := q }}\n")
lin = " + ".join(f"{bN[r]} * b.l{r}" for r in range(Q))
wsum = " + ".join(f"{aN[t]} * termWN ({term_lo(i, j)}) ({term_hi(i, j)})" for t, (i, j) in enumerate(pairs))
A(f"""
def leafCheck (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) (({lin}) * SW + ({wsum}) * SC)

/-- the bisection axis stored in the three bits after a split marker -/
def axOf (bits pos : ℕ) : ℕ := (bits >>> (pos + 1)) &&& 7

def walk (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := axOf bits pos
        let q := b.mid ax
        match walk bits fuel (pos + 4) (b.setHi ax q) with
        | none => none
        | some pos' => walk bits fuel pos' (b.setLo ax q)
      else bif {SKIP}leafCheck b then some (pos + 1) else none

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear
segment's cell must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WN ≥ cN * SW`. -/
def coverCheck (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || Nat.ble (cN * SW) (aAdjN * pieceW a b))
        && coverCheck aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

def boxOf ({' '.join(f'bd{r}' for r in range(Q))} : List (ℕ × ℕ)) ({' '.join(f'i{r}' for r in range(Q))} : ℕ) : Box :=
  ⟨{', '.join(f'(bd{r}.getD i{r} (0, 0)).1, (bd{r}.getD i{r} (0, 0)).2' for r in range(Q))}⟩

end Zeta23Ext.Bridge.ThreePoint.{NAME}

end {NAME}Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the computed piece bounds -/

theorem SC_pos : (0:ℚ) < SC := by norm_num [SC]
theorem SW_pos : (0:ℚ) < SW := by norm_num [SW]

-- ZSPLICE-LEMMAS

theorem pieceW_sound (a b : ℕ) (x : ℝ) (h1 : (a : ℝ) / SC ≤ x) (h2 : x ≤ (b : ℝ) / SC) :
    (pieceW a b : ℝ) / SW ≤ wfun x :=
  cellN_soundWZ ⟨a, b, 0⟩ x h1 h2

theorem chainOKN_sound : ∀ (ps : List (ℕ × ℕ)) (lo hi : ℕ), chainOKN lo hi ps = true →
      ∀ e : ℝ, (lo : ℝ) / SC ≤ e → e ≤ (hi : ℝ) / SC → (chainWN ps : ℝ) / SW ≤ wfun e := by
  intro ps
  induction ps with
  | nil =>
    intro lo hi _ e _ _
    simp only [chainWN, Nat.cast_zero, zero_div]; exact wfun_nonneg e
  | cons ab rest ih =>
    intro lo hi h e he1 he2
    obtain ⟨a, b⟩ := ab
    simp only [chainOKN, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hL' : (a : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN, Bool.cond_eq_ite, Nat.ble_eq]
    split_ifs with hempty hle
    · have hU : hi ≤ b := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKN, Nat.ble_eq] using hrest
      exact pieceW_sound a b e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rcases le_total e ((b : ℝ) / SC) with hU | hU
      · exact pieceW_sound a b e hL' hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num [SW]))
          (ih _ _ hrest e hU he2)
    · rcases le_total e ((b : ℝ) / SC) with hU | hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (not_le.mp hle).le) (by norm_num [SW]))
          (pieceW_sound a b e hL' hU)
      · exact ih _ _ hrest e hU he2

theorem termWN_sound_gen (lo hi : ℕ) (ps : List (ℕ × ℕ)) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) :
    (termWNcore lo hi ps : ℝ) / SW ≤ wfun e := by
  unfold termWNcore
  cases hch : chainOKN lo hi ps
  · simp only [cond_false, Nat.cast_zero, zero_div]; exact wfun_nonneg e
  · simp only [cond_true]; exact chainOKN_sound ps lo hi hch e he1 he2

theorem termWN_sound (lo hi : ℕ) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) : (termWN lo hi : ℝ) / SW ≤ wfun e :=
  termWN_sound_gen lo hi (piecesN' lo hi) e he1 he2

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.{NAME}

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G ({' '.join(V)} : ℝ) : ℝ :=
  {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
    + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))}

def Box.mem (b : Box) ({' '.join(V)} : ℝ) : Prop :=
  {' ∧ '.join(f'(b.l{r} : ℝ) / SC ≤ {V[r]} ∧ {V[r]} ≤ (b.u{r} : ℝ) / SC' for r in range(Q))}

set_option maxHeartbeats 4000000 in
theorem leaf_sound (b : Box) (h : leafCheck b = true)
    ({' '.join(V)} : ℝ) (hm : b.mem {' '.join(V)}) : (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  obtain ⟨{', '.join(f'h{r}1, h{r}2' for r in range(Q))}⟩ := hm
""")
# term soundness facts
for t, (i, j) in enumerate(pairs):
    hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
    A(f"  have w{t} := termWN_sound ({term_lo(i, j)}) ({term_hi(i, j)}) ({term_g(i, j)}) "
      f"(by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n")
A(f"""  simp only [leafCheck, Nat.ble_eq] at h
  have hq := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hpos : (0:ℝ) < SC * SW := by positivity
  set L : ℝ := {' + '.join(f'{bN[r]} * ((b.l{r} : ℝ) / SC)' for r in range(Q))} with hL
  set Wt : ℝ := {' + '.join(f'{aN[t]} * ((termWN ({term_lo(i, j)}) ({term_hi(i, j)}) : ℝ) / SW)' for t, (i, j) in enumerate(pairs))} with hWt
  have e : (L + Wt) * (SC * SW) = ({' + '.join(f'{bN[r]} * (b.l{r} : ℝ)' for r in range(Q))}) * SW + ({' + '.join(f'{aN[t]} * (termWN ({term_lo(i, j)}) ({term_hi(i, j)}) : ℝ)' for t, (i, j) in enumerate(pairs))}) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))} := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', {', '.join(f'mul_le_mul_of_nonneg_left h{r}1 (by positivity : (0:ℝ) ≤ {bN[r]})' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left w{t} (by positivity : (0:ℝ) ≤ {aN[t]})' for t in range(len(pairs)))}]
""")

# ---- walk composition, walk soundness, cover, top-level ----
A(f"""
theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℕ) ({' '.join(V)} : ℝ) (hm : b.mem {' '.join(V)})
    (hle : match ax with {' '.join(f'| {r} => {V[r]} ≤ (q : ℝ) / SC' for r in range(Q - 1))} | _ => {V[Q-1]} ≤ (q : ℝ) / SC) :
    (b.setHi ax q).mem {' '.join(V)} := by
  obtain ⟨{', '.join(f'h{r}1, h{r}2' for r in range(Q))}⟩ := hm
  match ax with
""")
for r in range(Q):
    pat = f"| {r}" if r < Q - 1 else f"| n + {Q - 1}"
    fields = []
    for k in range(Q):
        fields.append(f"h{k}1"); fields.append("hle" if k == r else f"h{k}2")
    A(f"  {pat} => exact ⟨{', '.join(fields)}⟩\n")
A(f"""
theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℕ) ({' '.join(V)} : ℝ) (hm : b.mem {' '.join(V)})
    (hge : match ax with {' '.join(f'| {r} => (q : ℝ) / SC ≤ {V[r]}' for r in range(Q - 1))} | _ => (q : ℝ) / SC ≤ {V[Q-1]}) :
    (b.setLo ax q).mem {' '.join(V)} := by
  obtain ⟨{', '.join(f'h{r}1, h{r}2' for r in range(Q))}⟩ := hm
  match ax with
""")
for r in range(Q):
    pat = f"| {r}" if r < Q - 1 else f"| n + {Q - 1}"
    fields = []
    for k in range(Q):
        fields.append("hge" if k == r else f"h{k}1"); fields.append(f"h{k}2")
    A(f"  {pat} => exact ⟨{', '.join(fields)}⟩\n")
A(f"""
theorem walk_split (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk bits fuel (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) = some pos1)
    (h2 : walk bits fuel pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) = some pos') :
    walk bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, cond_true, h1]
  exact h2

theorem walk_sound (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk bits fuel pos b = some pos' →
      ∀ {' '.join(V)} : ℝ, b.mem {' '.join(V)} → (cN : ℝ) / SA ≤ G {' '.join(V)}{ORX} := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk] at h
  | succ fuel ih =>
    intro pos b pos' h {' '.join(V)} hm
    simp only [walk, Bool.cond_eq_ite] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) pos1 h1 {' '.join(V)}
        have hhi := ih pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) pos' h {' '.join(V)}
        set ax := axOf bits pos with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
""")
for r in range(Q):
    pat = f"| {r}, hlo, hhi" if r < Q - 1 else f"| n + {Q - 1}, hlo, hhi"
    axv = f"{r}" if r < Q - 1 else f"(n + {Q - 1})"
    A(f"""        {pat} =>
          rcases le_total {V[r]} ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b {axv} q {' '.join(V)} hm hs)
          · exact hhi (Box.setLo_mem b {axv} q {' '.join(V)} hm hs)
""")
A(LEAFCASE)
A(f"""

theorem cover_sound (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        have hW := pieceW_sound a b v (by rw [hpos]; exact hv1) hvb
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSA : (0:ℝ) < SA := by norm_num [SA]
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        rw [div_le_iff₀ hSA]
        have hm2 : (aAdjN : ℝ) * ((pieceW a b : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
        rw [e]
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdjN : ℝ) * pieceW a b / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdjN : ℝ) * ((pieceW a b : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {{cover : List (ℕ × ℕ × Bool)}} {{s : ℕ × ℕ × Bool}} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (bits fuel : ℕ)
    ({' '.join(f'cover{r}' for r in range(Q))} : List (ℕ × ℕ × Bool)) ({' '.join(f'S{r}' for r in range(Q))} : ℕ)
    {' '.join(f'(hS{r} : cN * SC ≤ {bN[r]} * S{r})' for r in range(Q))}
    {' '.join(f'(hcov{r} : coverCheck {aN[pairs.index((r, r+1))]} (SC / 2) S{r} cover{r} = true)' for r in range(Q))}
    (hwin : cN * 100 ≤ 19 * {min(aN[pairs.index((r, r+1))] for r in range(Q))})
    (hrun : ∀ {' '.join(f'i{r}' for r in range(Q))}, {' → '.join(f'i{r} < (badOf cover{r}).length' for r in range(Q))} →
      ∃ pos pos', walk bits fuel pos (boxOf {' '.join(f'(badOf cover{r})' for r in range(Q))} {' '.join(f'i{r}' for r in range(Q))}) = some pos') :
    ∀ {' '.join(V)} : ℝ, {' → '.join(f'0 ≤ {V[r]}' for r in range(Q))} → (cN : ℝ) / SA ≤ G {' '.join(V)}{ORX} := by
  intro {' '.join(V)} {' '.join(f'hg{r}' for r in range(Q))}
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))} with hLin
  set Wt : ℝ := {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(pairs))} with hWt
  have hG : G {' '.join(V)} = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
""")
A("".join(f"  have hb{r}0 : (0:ℝ) ≤ ({bN[r]} / (SA:ℝ)) * {V[r]} := mul_nonneg (by positivity) hg{r}\n" for r in range(Q)))
A("".join(f"  have ha{t}0 : (0:ℝ) ≤ ({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)}) := mul_nonneg (by positivity) (hw _)\n" for t, (i, j) in enumerate(pairs)))
A(f"  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [{', '.join(f'hb{r}0' for r in range(Q))}]\n")
A(f"  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [{', '.join(f'ha{t}0' for t in range(len(pairs)))}]\n")
A("".join(f"  have hbL{r} : ({bN[r]} / (SA:ℝ)) * {V[r]} ≤ Lin := by rw [hLin]; linarith [{', '.join(f'hb{k}0' for k in range(Q) if k != r)}]\n" for r in range(Q)))
A("".join(f"  have haW{t} : ({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)}) ≤ Wt := by rw [hWt]; linarith [{', '.join(f'ha{k}0' for k in range(len(pairs)) if k != t)}]\n" for t, (i, j) in enumerate(pairs)))
amin = min(aN[pairs.index((r, r+1))] for r in range(Q))
for r in range(Q):
    adj = aN[pairs.index((r, r+1))]; tadj = pairs.index((r, r+1))
    A(f"""  -- gap {r}: beyond the cutoff the pressure alone pays
  by_cases hcut{r} : (S{r} : ℝ) / SC ≤ {V[r]}
  · have h1 : (cN : ℝ) / SA ≤ ({bN[r]} / (SA:ℝ)) * {V[r]} := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS{r}; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : ({bN[r]} / (SA:ℝ)) * {V[r]} * SA = {bN[r]} * {V[r]} := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ {bN[r]} * S{r} / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = {bN[r]} * ((S{r} : ℝ) / SC) := by ring
        _ ≤ {bN[r]} * {V[r]} := mul_le_mul_of_nonneg_left hcut{r} (by norm_num)
    {LEFT}rw [hG]; linarith [h1, hbL{r}, hWt0]
  push_neg at hcut{r}
  rcases le_total {V[r]} ((SC / 2 : ℕ) / (SC : ℝ)) with hwin{r} | hwin{r}
  · have hw19 := wfun_window {V[r]} hg{r} (by rw [hhalf] at hwin{r}; exact hwin{r})
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ ({adj} / (SA:ℝ)) * wfun {V[r]} := by
      rw [div_le_iff₀ hSA]
      have e : ({adj} / (SA:ℝ)) * wfun {V[r]} * SA = {adj} * wfun {V[r]} := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ {adj})
      linarith [hq, hm]
    {LEFT}rw [hG]; linarith [h1, haW{tadj}, hLin0]
  rcases cover_sound _ cover{r} (SC / 2) S{r} hcov{r} {V[r]} hwin{r} hcut{r} with hclear{r} | ⟨s{r}, hs{r}, he{r}, hb{r}1, hb{r}2⟩
  · {LEFT}rw [hG]; linarith [hclear{r}, haW{tadj}, hLin0]
  obtain ⟨i{r}, hi{r}, hsi{r}⟩ := List.mem_iff_getElem.mp (badOf_mem hs{r} he{r})
  have hb{r}1' : (((badOf cover{r}).getD i{r} (0, 0)).1 : ℝ) / SC ≤ {V[r]} := by
    rw [List.getD_eq_getElem _ _ hi{r}, hsi{r}]; exact hb{r}1
  have hb{r}2' : {V[r]} ≤ (((badOf cover{r}).getD i{r} (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi{r}, hsi{r}]; exact hb{r}2
""")
A(f"""  obtain ⟨pos, pos', hwalk⟩ := hrun {' '.join(f'i{r}' for r in range(Q))} {' '.join(f'hi{r}' for r in range(Q))}
  exact walk_sound bits fuel pos _ pos' hwalk {' '.join(V)} ⟨{', '.join(f"hb{r}1', hb{r}2'" for r in range(Q))}⟩

end Zeta23Ext.Bridge.ThreePoint.{NAME}

end
""")
text = "".join(out)
# ---- integer cell check (checkerZ.lean): splice the defs after CellN.toQ, the lemmas before CTN.find_sound,
#      and make the table check and the cell soundness theorem use it ----
import os as _os
_z = open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "checkerZ.lean"), encoding="utf-8").read()
_zd = _z[_z.index("-- ZDEFS-BEGIN"):_z.index("-- ZDEFS-END") + len("-- ZDEFS-END")]
_zl = _z[_z.index("-- ZLEMMAS-BEGIN"):_z.index("-- ZLEMMAS-END") + len("-- ZLEMMAS-END")]
assert text.count("-- ZSPLICE-DEFS") == 1 and text.count("-- ZSPLICE-LEMMAS") == 1
text = text.replace("-- ZSPLICE-DEFS", _zd, 1)
text = text.replace("-- ZSPLICE-LEMMAS", _zl, 1)
open(f"checker_{NAME}.lean", "w", encoding="utf-8").write(text)
out = [text]
print(f"wrote checker_{NAME}.lean ({len(''.join(out))} bytes)")
