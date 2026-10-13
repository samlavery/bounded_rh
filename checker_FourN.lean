
/-! ###### natural-number checker for the 4-point weighted certificate `FourN` ###### -/

section FourNDefs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (LN UN : ℕ) (k : ℕ) (side : Bool) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0, 0, true, 0⟩⟩

def SC : ℕ := 79228162514264337593543950336
def SW : ℕ := 10000000000000
def SC4 : ℕ := 19807040628566084398385987584

/-- the rational cell a natural-number cell denotes -/
def CellN.toQ (c : CellN) : Cell := ⟨(c.LN : ℚ) / SC, (c.UN : ℚ) / SC, c.k, c.side, (c.WN : ℚ) / SW⟩

inductive CTN
  | nil
  | node (l : CTN) (c : CellN) (r : CTN)

namespace CTN
def toList : CTN → List CellN
  | nil => []
  | node l c r => l.toList ++ c :: r.toList
def allOk : CTN → Bool
  | nil => true
  | node l c r => l.allOk && c.toQ.ok && r.allOk
def find : CTN → ℕ → ℕ → Option CellN
  | nil, _, _ => none
  | node l c r, a, b =>
      if a < c.LN then l.find a b
      else if c.LN < a then r.find a b
      else if b < c.UN then l.find a b
      else if c.UN < b then r.find a b
      else some c
end CTN

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 94) + 1) <<< 94
      if q < hi then (a, q) :: piecesN fuel q hi else [(a, hi)]

def lookupAllN (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      match t.find a b, lookupAllN t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainOKN : ℕ → ℕ → List CellN → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, c :: rest => decide (c.LN ≤ lo) && chainOKN c.UN hi rest

def chainWN : List CellN → ℕ
  | [] => 0
  | c :: rest => if rest.isEmpty then c.WN else min c.WN (chainWN rest)

def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := piecesN 64 lo hi

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.FourN

def SA : ℕ := 600000000
def cN : ℕ := 1386000

structure Box where
  (l0 u0 l1 u1 l2 u2 : ℕ)
  deriving DecidableEq

def Box.widthArg (b : Box) : ℕ :=
  if (b.u1 - b.l1) ≤ (b.u0 - b.l0) ∧ (b.u2 - b.l2) ≤ (b.u0 - b.l0) then 0
  else if (b.u2 - b.l2) ≤ (b.u1 - b.l1) then 1
  else 2
def Box.mid (b : Box) : ℕ → ℕ
  | 0 => (b.l0 + b.u0) / 2
  | 1 => (b.l1 + b.u1) / 2
  | _ => (b.l2 + b.u2) / 2
def Box.setHi (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with u0 := q }
  | 1 => { b with u1 := q }
  | _ => { b with u2 := q }
def Box.setLo (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with l0 := q }
  | 1 => { b with l1 := q }
  | _ => { b with l2 := q }

def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((240000 * b.l0 + 240000 * b.l1 + 240000 * b.l2) * SW + (400000000 * termWN tb (b.l0) (b.u0) + 600000000 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 1200000000 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 400000000 * termWN tb (b.l1) (b.u1) + 600000000 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 400000000 * termWN tb (b.l2) (b.u2)) * SC)

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk tb bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else if leafCheck tb b then some (pos + 1) else none

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear
segment's cell must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WN ≥ cN * SW`. -/
def coverCheck (tb : CTN) (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match tb.find a b with | some c => decide (cN * SW ≤ aAdjN * c.WN) | none => false))
        && coverCheck tb aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

def boxOf (bd0 bd1 bd2 : List (ℕ × ℕ)) (i0 i1 i2 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint.FourN

end FourNDefs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the natural-number cell table (through the rational cell) -/

theorem SC_pos : (0:ℚ) < SC := by norm_num [SC]
theorem SW_pos : (0:ℚ) < SW := by norm_num [SW]

theorem CTN.find_sound : ∀ (t : CTN) (a b : ℕ) (c : CellN), t.find a b = some c →
    c ∈ t.toList ∧ c.LN = a ∧ c.UN = b := by
  intro t
  induction t with
  | nil => intro a b c h; simp [CTN.find] at h
  | node l c0 r ihl ihr =>
    intro a b c h
    simp only [CTN.find] at h
    split_ifs at h with h1 h2 h3 h4
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h; exact ⟨by simp [CTN.toList, hm], hL, hU⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp [CTN.toList], le_antisymm (not_lt.mp h1) (not_lt.mp h2),
        le_antisymm (not_lt.mp h3) (not_lt.mp h4)⟩

theorem CTN.allOk_sound : ∀ (t : CTN), t.allOk = true → ∀ c ∈ t.toList, c.toQ.ok = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CTN.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CTN.allOk, Bool.and_eq_true] at h
    simp only [CTN.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc

theorem lookupAllN_sound (t : CTN) : ∀ (ps : List (ℕ × ℕ)) (cs : List CellN),
    lookupAllN t ps = some cs → ∀ c ∈ cs, c ∈ t.toList := by
  intro ps
  induction ps with
  | nil => intro cs h; simp [lookupAllN] at h; subst h; simp
  | cons ab rest ih =>
    intro cs h
    obtain ⟨a, b⟩ := ab
    cases hf : t.find a b with
    | none => simp [lookupAllN, hf] at h
    | some c =>
      cases hr : lookupAllN t rest with
      | none => simp [lookupAllN, hf, hr] at h
      | some cs' =>
        simp only [lookupAllN, hf, hr, Option.some.injEq] at h
        subst h
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact (CTN.find_sound t a b d hf).1
        · exact ih cs' hr d hd

/-- a natural-number cell's bound holds on its interval, read in real coordinates -/
theorem cellN_sound (c : CellN) (hok : c.toQ.ok = true) (x : ℝ)
    (h1 : (c.LN : ℝ) / SC ≤ x) (h2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  have := cell_sound c.toQ hok x (by simp only [CellN.toQ]; push_cast; exact h1)
    (by simp only [CellN.toQ]; push_cast; exact h2)
  simp only [CellN.toQ] at this; push_cast at this; exact this

theorem chainOKN_sound (t : CTN) (hok : t.allOk = true) :
    ∀ (cs : List CellN), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℕ), chainOKN lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) / SC ≤ e → e ≤ (hi : ℝ) / SC → (chainWN cs : ℝ) / SW ≤ wfun e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWN, Nat.cast_zero, zero_div]; exact wfun_nonneg e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [chainOKN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok := CTN.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.LN : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN]
    split_ifs with hempty
    · have hU : hi ≤ c.UN := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKN] using hrest
      exact cellN_sound c hcok e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rw [Nat.cast_min, ← min_div_div_right (by norm_num [SW] : (0:ℝ) ≤ SW)]
      rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact (min_le_left _ _).trans (cellN_sound c hcok e hL' hU)
      · exact (min_le_right _ _).trans
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)

theorem termWN_sound_gen (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (ps : List (ℕ × ℕ)) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) :
    (termWNcore t lo hi ps : ℝ) / SW ≤ wfun e := by
  unfold termWNcore
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact chainOKN_sound t hok cs (lookupAllN_sound t _ cs hcs) lo hi hch e he1 he2
    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e

theorem termWN_sound (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) : (termWN t lo hi : ℝ) / SW ≤ wfun e :=
  termWN_sound_gen t hok lo hi (piecesN' lo hi) e he1 he2

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.FourN

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 : ℝ) : ℝ :=
  (240000 / (SA:ℝ)) * g0 + (240000 / (SA:ℝ)) * g1 + (240000 / (SA:ℝ)) * g2
    + (400000000 / (SA:ℝ)) * wfun (g0) + (600000000 / (SA:ℝ)) * wfun (g0 + g1) + (1200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g1) + (600000000 / (SA:ℝ)) * wfun (g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g2)

def Box.mem (b : Box) (g0 g1 g2 : ℝ) : Prop :=
  (b.l0 : ℝ) / SC ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / SC ∧ (b.l1 : ℝ) / SC ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / SC ∧ (b.l2 : ℝ) / SC ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / SC

theorem leaf_sound (tb : CTN) (hok : tb.allOk = true) (b : Box) (h : leafCheck tb b = true)
    (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2) : (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  have w0 := termWN_sound tb hok (b.l0) (b.u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := termWN_sound tb hok (b.l0 + b.l1) (b.u0 + b.u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := termWN_sound tb hok (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := termWN_sound tb hok (b.l1) (b.u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w4 := termWN_sound tb hok (b.l1 + b.l2) (b.u1 + b.u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w5 := termWN_sound tb hok (b.l2) (b.u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  simp only [leafCheck, Nat.ble_eq] at h
  have hq := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hpos : (0:ℝ) < SC * SW := by positivity
  set L : ℝ := 240000 * ((b.l0 : ℝ) / SC) + 240000 * ((b.l1 : ℝ) / SC) + 240000 * ((b.l2 : ℝ) / SC) with hL
  set Wt : ℝ := 400000000 * ((termWN tb (b.l0) (b.u0) : ℝ) / SW) + 600000000 * ((termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) / SW) + 1200000000 * ((termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) / SW) + 400000000 * ((termWN tb (b.l1) (b.u1) : ℝ) / SW) + 600000000 * ((termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) / SW) + 400000000 * ((termWN tb (b.l2) (b.u2) : ℝ) / SW) with hWt
  have e : (L + Wt) * (SC * SW) = (240000 * (b.l0 : ℝ) + 240000 * (b.l1 : ℝ) + 240000 * (b.l2 : ℝ)) * SW + (400000000 * (termWN tb (b.l0) (b.u0) : ℝ) + 600000000 * (termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) + 1200000000 * (termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) + 400000000 * (termWN tb (b.l1) (b.u1) : ℝ) + 600000000 * (termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) + 400000000 * (termWN tb (b.l2) (b.u2) : ℝ)) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((240000 / (SA:ℝ)) * g0 + (240000 / (SA:ℝ)) * g1 + (240000 / (SA:ℝ)) * g2
      + (400000000 / (SA:ℝ)) * wfun (g0) + (600000000 / (SA:ℝ)) * wfun (g0 + g1) + (1200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g1) + (600000000 / (SA:ℝ)) * wfun (g1 + g2) + (400000000 / (SA:ℝ)) * wfun (g2)) * SA
      = 240000 * g0 + 240000 * g1 + 240000 * g2 + 400000000 * wfun (g0) + 600000000 * wfun (g0 + g1) + 1200000000 * wfun (g0 + g1 + g2) + 400000000 * wfun (g1) + 600000000 * wfun (g1 + g2) + 400000000 * wfun (g2) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 240000), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 400000000), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 600000000), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 1200000000), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 400000000), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 600000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 400000000)]

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2)
    (hle : match ax with | 0 => g0 ≤ (q : ℝ) / SC | 1 => g1 ≤ (q : ℝ) / SC | _ => g2 ≤ (q : ℝ) / SC) :
    (b.setHi ax q).mem g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  match ax with
  | 0 => exact ⟨h01, hle, h11, h12, h21, h22⟩
  | 1 => exact ⟨h01, h02, h11, hle, h21, h22⟩
  | n + 2 => exact ⟨h01, h02, h11, h12, h21, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 : ℝ) (hm : b.mem g0 g1 g2)
    (hge : match ax with | 0 => (q : ℝ) / SC ≤ g0 | 1 => (q : ℝ) / SC ≤ g1 | _ => (q : ℝ) / SC ≤ g2) :
    (b.setLo ax q).mem g0 g1 g2 := by
  obtain ⟨h01, h02, h11, h12, h21, h22⟩ := hm
  match ax with
  | 0 => exact ⟨hge, h02, h11, h12, h21, h22⟩
  | 1 => exact ⟨h01, h02, hge, h12, h21, h22⟩
  | n + 2 => exact ⟨h01, h02, h11, h12, hge, h22⟩

theorem walk_split (tb : CTN) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk tb bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk tb bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, if_true, h1]
  exact h2

theorem walk_sound (tb : CTN) (hok : tb.allOk = true) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk tb bits fuel pos b = some pos' →
      ∀ g0 g1 g2 : ℝ, b.mem g0 g1 g2 → (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk] at h
  | succ fuel ih =>
    intro pos b pos' h g0 g1 g2 hm
    simp only [walk] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 g0 g1 g2
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h g0 g1 g2
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total g0 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b 0 q g0 g1 g2 hm hs)
        | 1, hlo, hhi =>
          rcases le_total g1 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b 1 q g0 g1 g2 hm hs)
        | n + 2, hlo, hhi =>
          rcases le_total g2 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 2) q g0 g1 g2 hm hs)
          · exact hhi (Box.setLo_mem b (n + 2) q g0 g1 g2 hm hs)
    · exact leaf_sound tb hok b hleaf g0 g1 g2 hm

theorem cover_sound (tb : CTN) (hok : tb.allOk = true) (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck tb aAdjN pos S cover = true →
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
      Bool.not_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        split at hcl
        · rename_i c hfind
          obtain ⟨hmem, hL, hU⟩ := CTN.find_sound tb a b c hfind
          have hcok := CTN.allOk_sound tb hok c hmem
          have hW := cellN_sound c hcok v (by rw [hL, hpos]; exact hv1) (by rw [hU]; exact hvb)
          have hq := (Nat.cast_le (α := ℝ)).mpr (decide_eq_true_eq.mp hcl)
          push_cast at hq
          have hSA : (0:ℝ) < SA := by norm_num [SA]
          have hSW : (0:ℝ) < SW := by norm_num [SW]
          rw [div_le_iff₀ hSA]
          have hm2 : (aAdjN : ℝ) * ((c.WN : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
            mul_le_mul_of_nonneg_left hW (by positivity)
          have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
          rw [e]
          calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
            _ ≤ (aAdjN : ℝ) * c.WN / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
            _ = (aAdjN : ℝ) * ((c.WN : ℝ) / SW) := by ring
            _ ≤ _ := hm2
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

theorem of_check (tb : CTN) (hok : tb.allOk = true) (bits fuel : ℕ)
    (cover0 cover1 cover2 : List (ℕ × ℕ × Bool)) (S0 S1 S2 : ℕ)
    (hS0 : cN * SC ≤ 240000 * S0) (hS1 : cN * SC ≤ 240000 * S1) (hS2 : cN * SC ≤ 240000 * S2)
    (hcov0 : coverCheck tb 400000000 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck tb 400000000 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck tb 400000000 (SC / 2) S2 cover2 = true)
    (hwin : cN * 100 ≤ 19 * 400000000)
    (hrun : ∀ i0 i1 i2, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length →
      ∃ pos pos', walk tb bits fuel pos (boxOf (badOf cover0) (badOf cover1) (badOf cover2) i0 i1 i2) = some pos') :
    ∀ g0 g1 g2 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → (cN : ℝ) / SA ≤ G g0 g1 g2 := by
  intro g0 g1 g2 hg0 hg1 hg2
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g0 * SA = 240000 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 240000 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g0 * SA = 400000000 * wfun g0 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g1 * SA = 240000 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 240000 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g1 * SA = 400000000 * wfun g1 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (240000 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (240000 / (SA:ℝ)) * g2 * SA = 240000 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 240000 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 240000 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 240000 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g2))]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (400000000 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (400000000 / (SA:ℝ)) * wfun g2 * SA = 400000000 * wfun g2 := by field_simp
      rw [e]; nlinarith [hq, hw19]
    unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2))]
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · unfold G
    linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg0, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg1, mul_nonneg (by positivity : (0:ℝ) ≤ 240000 / SA) hg2, mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g0)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g0 + g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 1200000000 / SA) (hw (g0 + g1 + g2)), mul_nonneg (by positivity : (0:ℝ) ≤ 400000000 / SA) (hw (g1)), mul_nonneg (by positivity : (0:ℝ) ≤ 600000000 / SA) (hw (g1 + g2))]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 hi0 hi1 hi2
  exact walk_sound tb hok bits fuel pos _ pos' hwalk g0 g1 g2 ⟨hb01', hb02', hb11', hb12', hb21', hb22'⟩

end Zeta23Ext.Bridge.ThreePoint.FourN

end
