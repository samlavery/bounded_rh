
/-! ###### five-point checker: cell search tree, quarter pieces, bit-encoded bisection ###### -/

section Checker5Defs

namespace Zeta23Ext.Bridge.ThreePoint

/-- A binary search tree of cells keyed by `(L, U)`. -/
inductive CT
  | nil
  | node (l : CT) (c : Cell) (r : CT)

namespace CT
def toList : CT → List Cell
  | nil => []
  | node l c r => l.toList ++ c :: r.toList

def allOk : CT → Bool
  | nil => true
  | node l c r => l.allOk && c.ok && r.allOk

def find : CT → ℚ → ℚ → Option Cell
  | nil, _, _ => none
  | node l c r, a, b =>
      if a < c.L then l.find a b
      else if c.L < a then r.find a b
      else if b < c.U then l.find a b
      else if c.U < b then r.find a b
      else some c
end CT

/-- Quarter pieces of `[a, hi]`: cut at the multiples of `1/4` strictly inside. -/
def piecesAux : ℕ → ℚ → ℚ → List (ℚ × ℚ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q : ℚ := ((⌊4 * a⌋ : ℤ) + 1) / 4
      if q < hi then (a, q) :: piecesAux fuel q hi else [(a, hi)]

def pieces (lo hi : ℚ) : List (ℚ × ℚ) := piecesAux 64 lo hi

/-- Look every piece up; `none` if any piece is missing from the table. -/
def lookupAll (t : CT) : List (ℚ × ℚ) → Option (List Cell)
  | [] => some []
  | (a, b) :: rest =>
      match t.find a b, lookupAll t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

/-- The chain covers `[lo, hi]`: first cell starts at or before `lo`, consecutive cells touch,
last cell reaches `hi`. -/
def chainOKC : ℚ → ℚ → List Cell → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, c :: rest => decide (c.L ≤ lo) && chainOKC c.U hi rest

def chainWC : List Cell → ℚ
  | [] => 0
  | c :: rest => if rest.isEmpty then c.W else min c.W (chainWC rest)

/-- The bound the table gives for `wfun` on `[lo, hi]` (`0` when the table has no chain). -/
def termW5 (t : CT) (lo hi : ℚ) : ℚ :=
  match lookupAll t (pieces lo hi) with
  | some cs => if chainOKC lo hi cs then chainWC cs else 0
  | none => 0

structure Box5 where
  (xl xu yl yu zl zu ul uu : ℚ)
  deriving DecidableEq

def Box5.widthArg (b : Box5) : ℕ :=
  let w0 := b.xu - b.xl; let w1 := b.yu - b.yl; let w2 := b.zu - b.zl; let w3 := b.uu - b.ul
  if w1 ≤ w0 ∧ w2 ≤ w0 ∧ w3 ≤ w0 then 0
  else if w2 ≤ w1 ∧ w3 ≤ w1 then 1
  else if w3 ≤ w2 then 2 else 3

def Box5.mid (b : Box5) : ℕ → ℚ
  | 0 => (b.xl + b.xu) / 2
  | 1 => (b.yl + b.yu) / 2
  | 2 => (b.zl + b.zu) / 2
  | _ => (b.ul + b.uu) / 2

def Box5.setHi (b : Box5) (ax : ℕ) (q : ℚ) : Box5 :=
  match ax with
  | 0 => { b with xu := q }
  | 1 => { b with yu := q }
  | 2 => { b with zu := q }
  | _ => { b with uu := q }

def Box5.setLo (b : Box5) (ax : ℕ) (q : ℚ) : Box5 :=
  match ax with
  | 0 => { b with xl := q }
  | 1 => { b with yl := q }
  | 2 => { b with zl := q }
  | _ => { b with ul := q }

def leafCheck5 (t : CT) (c p : ℚ) (b : Box5) : Bool :=
  decide (c ≤ (b.xl + b.yl + b.zl + b.ul) / p
    + 1/2 * termW5 t b.xl b.xu + 1/2 * termW5 t b.yl b.yu + 1/2 * termW5 t b.zl b.zu
    + 1/2 * termW5 t b.ul b.uu
    + 2/3 * termW5 t (b.xl + b.yl) (b.xu + b.yu) + 2/3 * termW5 t (b.yl + b.zl) (b.yu + b.zu)
    + 2/3 * termW5 t (b.zl + b.ul) (b.zu + b.uu)
    + termW5 t (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu)
    + termW5 t (b.yl + b.zl + b.ul) (b.yu + b.zu + b.uu)
    + 2 * termW5 t (b.xl + b.yl + b.zl + b.ul) (b.xu + b.yu + b.zu + b.uu))

/-- Walk the bit-encoded tree (`1` = split at the widest side's midpoint, `0` = leaf) from bit
`pos`; returns the position after the subtree when every leaf checks. -/
def walk5 (t : CT) (c p : ℚ) (bits : ℕ) : ℕ → ℕ → Box5 → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk5 t c p bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk5 t c p bits fuel pos' (b.setLo ax q)
      else if leafCheck5 t c p b then some (pos + 1) else none

def allTuples (nb : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range nb).flatMap fun i => (List.range nb).flatMap fun j =>
    (List.range nb).flatMap fun k => (List.range nb).map fun l => (i, j, k, l)

def boxOf5 (bad : List (ℚ × ℚ)) (i j k l : ℕ) : Box5 :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2, (bad.getD l (0, 0)).1, (bad.getD l (0, 0)).2⟩

/-- Consume the trees of all tuples in order. -/
def runTuples (t : CT) (c p : ℚ) (bits : ℕ) (fuel : ℕ) (bad : List (ℚ × ℚ)) :
    List (ℕ × ℕ × ℕ × ℕ) → ℕ → Option ℕ
  | [], pos => some pos
  | (i, j, k, l) :: rest, pos =>
      match walk5 t c p bits fuel pos (boxOf5 bad i j k l) with
      | none => none
      | some pos' => runTuples t c p bits fuel bad rest pos'

/-- The one-dimensional cover: segments `(a, b, clear)`; a clear segment's cell is looked up. -/
def coverCheck5 (t : CT) (lvl : ℚ) : ℚ → ℚ → List (ℚ × ℚ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match t.find a b with | some c => decide (lvl ≤ c.W) | none => false))
        && coverCheck5 t lvl b S rest

def badOf5 (cover : List (ℚ × ℚ × Bool)) : List (ℚ × ℚ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

end Zeta23Ext.Bridge.ThreePoint

end Checker5Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness: the search tree -/

theorem CT.find_sound : ∀ (t : CT) (a b : ℚ) (c : Cell), t.find a b = some c →
    c ∈ t.toList ∧ c.L = a ∧ c.U = b := by
  intro t
  induction t with
  | nil => intro a b c h; simp [CT.find] at h
  | node l c0 r ihl ihr =>
    intro a b c h
    simp only [CT.find] at h
    split_ifs at h with h1 h2 h3 h4
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp [CT.toList], le_antisymm (not_lt.mp h1) (not_lt.mp h2),
        le_antisymm (not_lt.mp h3) (not_lt.mp h4)⟩

theorem CT.allOk_sound : ∀ (t : CT), t.allOk = true → ∀ c ∈ t.toList, c.ok = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CT.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CT.allOk, Bool.and_eq_true] at h
    simp only [CT.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc

theorem lookupAll_sound (t : CT) : ∀ (ps : List (ℚ × ℚ)) (cs : List Cell),
    lookupAll t ps = some cs → ∀ c ∈ cs, c ∈ t.toList := by
  intro ps
  induction ps with
  | nil => intro cs h; simp [lookupAll] at h; subst h; simp
  | cons ab rest ih =>
    intro cs h
    obtain ⟨a, b⟩ := ab
    cases hf : t.find a b with
    | none => simp [lookupAll, hf] at h
    | some c =>
      cases hr : lookupAll t rest with
      | none => simp [lookupAll, hf, hr] at h
      | some cs' =>
        simp only [lookupAll, hf, hr, Option.some.injEq] at h
        subst h
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact (CT.find_sound t a b d hf).1
        · exact ih cs' hr d hd

/-! ### Soundness: chains of cells -/

theorem chainOKC_sound (t : CT) (hok : t.allOk = true) :
    ∀ (cs : List Cell), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℚ), chainOKC lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) ≤ e → e ≤ hi → (chainWC cs : ℝ) ≤ wfun e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWC, Rat.cast_zero]; exact wfun_nonneg e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [chainOKC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok : c.ok = true := CT.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.L : ℝ) ≤ e := le_trans (by exact_mod_cast hL) he1
    simp only [chainWC]
    split_ifs with hempty
    · have hU : hi ≤ c.U := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKC] using hrest
      exact cell_sound c hcok e hL' (he2.trans (by exact_mod_cast hU))
    · rw [Rat.cast_min]
      rcases le_total e (c.U : ℝ) with hU | hU
      · exact (min_le_left _ _).trans (cell_sound c hcok e hL' hU)
      · exact (min_le_right _ _).trans
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)

theorem termW5_sound (t : CT) (hok : t.allOk = true) (lo hi : ℚ) (e : ℝ)
    (he1 : (lo : ℝ) ≤ e) (he2 : e ≤ hi) : (termW5 t lo hi : ℝ) ≤ wfun e := by
  unfold termW5
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact chainOKC_sound t hok cs (lookupAll_sound t _ cs hcs) lo hi hch e he1 he2
    · simp only [Rat.cast_zero]; exact wfun_nonneg e
  · simp only [Rat.cast_zero]; exact wfun_nonneg e

/-! ### Soundness: leaves and the bit-encoded tree -/

/-- The five-point functional written out on the four gaps. -/
def G5 (p : ℚ) (x y z u : ℝ) : ℝ :=
  (1 / (p : ℝ)) * (x + y + z + u)
    + 1/2 * wfun x + 1/2 * wfun y + 1/2 * wfun z + 1/2 * wfun u
    + 2/3 * wfun (x + y) + 2/3 * wfun (y + z) + 2/3 * wfun (z + u)
    + wfun (x + y + z) + wfun (y + z + u)
    + 2 * wfun (x + y + z + u)

def Box5.mem (b : Box5) (x y z u : ℝ) : Prop :=
  (b.xl : ℝ) ≤ x ∧ x ≤ b.xu ∧ (b.yl : ℝ) ≤ y ∧ y ≤ b.yu ∧ (b.zl : ℝ) ≤ z ∧ z ≤ b.zu
    ∧ (b.ul : ℝ) ≤ u ∧ u ≤ b.uu

theorem leaf5_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (b : Box5)
    (h : leafCheck5 t c p b = true) (x y z u : ℝ) (hm : b.mem x y z u) :
    (c : ℝ) ≤ G5 p x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  simp only [leafCheck5, decide_eq_true_eq] at h
  have w0 := termW5_sound t hok _ _ x hx1 hx2
  have w1 := termW5_sound t hok _ _ y hy1 hy2
  have w2 := termW5_sound t hok _ _ z hz1 hz2
  have w3 := termW5_sound t hok _ _ u hu1 hu2
  have w4 := termW5_sound t hok (b.xl + b.yl) (b.xu + b.yu) (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := termW5_sound t hok (b.yl + b.zl) (b.yu + b.zu) (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w6 := termW5_sound t hok (b.zl + b.ul) (b.zu + b.uu) (z + u) (by push_cast; linarith) (by push_cast; linarith)
  have w7 := termW5_sound t hok (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w8 := termW5_sound t hok (b.yl + b.zl + b.ul) (b.yu + b.zu + b.uu) (y + z + u) (by push_cast; linarith) (by push_cast; linarith)
  have w9 := termW5_sound t hok (b.xl + b.yl + b.zl + b.ul) (b.xu + b.yu + b.zu + b.uu) (x + y + z + u) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl + b.ul) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G5
  linarith

theorem setHi_mem (b : Box5) (ax : ℕ) (q : ℚ) (x y z u : ℝ) (hm : b.mem x y z u)
    (hle : match ax with | 0 => x ≤ q | 1 => y ≤ q | 2 => z ≤ q | _ => u ≤ q) :
    (b.setHi ax q).mem x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  match ax with
  | 0 => exact ⟨hx1, hle, hy1, hy2, hz1, hz2, hu1, hu2⟩
  | 1 => exact ⟨hx1, hx2, hy1, hle, hz1, hz2, hu1, hu2⟩
  | 2 => exact ⟨hx1, hx2, hy1, hy2, hz1, hle, hu1, hu2⟩
  | n + 3 => exact ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hle⟩

theorem setLo_mem (b : Box5) (ax : ℕ) (q : ℚ) (x y z u : ℝ) (hm : b.mem x y z u)
    (hge : match ax with | 0 => (q : ℝ) ≤ x | 1 => (q : ℝ) ≤ y | 2 => (q : ℝ) ≤ z | _ => (q : ℝ) ≤ u) :
    (b.setLo ax q).mem x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  match ax with
  | 0 => exact ⟨hge, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩
  | 1 => exact ⟨hx1, hx2, hge, hy2, hz1, hz2, hu1, hu2⟩
  | 2 => exact ⟨hx1, hx2, hy1, hy2, hge, hz2, hu1, hu2⟩
  | n + 3 => exact ⟨hx1, hx2, hy1, hy2, hz1, hz2, hge, hu2⟩

/-- A split node's walk from the walks of its two children (used to chunk the kernel checks). -/
theorem walk5_split (t : CT) (c p : ℚ) (bits fuel pos : ℕ) (b : Box5) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk5 t c p bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk5 t c p bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk5 t c p bits (fuel + 1) pos b = some pos' := by
  simp only [walk5, hbit, if_true, h1]
  exact h2

theorem walk5_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box5) (pos' : ℕ), walk5 t c p bits fuel pos b = some pos' →
      ∀ x y z u : ℝ, b.mem x y z u → (c : ℝ) ≤ G5 p x y z u := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk5] at h
  | succ fuel ih =>
    intro pos b pos' h x y z u hm
    simp only [walk5] at h
    split_ifs at h with hbit hleaf
    · -- a split
      split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 x y z u
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h x y z u
        -- case on the split axis and side
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total x (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 0 q x y z u hm hs)
          · exact hhi (setLo_mem b 0 q x y z u hm hs)
        | 1, hlo, hhi =>
          rcases le_total y (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 1 q x y z u hm hs)
          · exact hhi (setLo_mem b 1 q x y z u hm hs)
        | 2, hlo, hhi =>
          rcases le_total z (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 2 q x y z u hm hs)
          · exact hhi (setLo_mem b 2 q x y z u hm hs)
        | n + 3, hlo, hhi =>
          rcases le_total u (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b (n + 3) q x y z u hm hs)
          · exact hhi (setLo_mem b (n + 3) q x y z u hm hs)
    · exact leaf5_sound t hok c p hp b hleaf x y z u hm

theorem runTuples_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits fuel : ℕ)
    (bad : List (ℚ × ℚ)) :
    ∀ (tuples : List (ℕ × ℕ × ℕ × ℕ)) (pos pos' : ℕ),
      runTuples t c p bits fuel bad tuples pos = some pos' →
      ∀ i j k l, (i, j, k, l) ∈ tuples → ∀ x y z u : ℝ, (boxOf5 bad i j k l).mem x y z u →
        (c : ℝ) ≤ G5 p x y z u := by
  intro tuples
  induction tuples with
  | nil => intro _ _ _ i j k l hmem; simp at hmem
  | cons hd rest ih =>
    intro pos pos' h i j k l hmem x y z u hm
    obtain ⟨i0, j0, k0, l0⟩ := hd
    simp only [runTuples] at h
    split at h
    · exact absurd h (by simp)
    · rename_i pos1 hw
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | hmem
      · exact walk5_sound t hok c p hp bits fuel pos _ pos1 hw x y z u hm
      · exact ih pos1 pos' h i j k l hmem x y z u hm

/-! ### Soundness: the cover -/

theorem cover5_sound (t : CT) (hok : t.allOk = true) (lvl : ℚ) :
    ∀ (cover : List (ℚ × ℚ × Bool)) (pos S : ℚ), coverCheck5 t lvl pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) ≤ v → v < S →
        (lvl : ℝ) ≤ wfun v ∨ ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) ≤ v ∧ v ≤ s.2.1 := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck5, decide_eq_true_eq] at h
    have : (S : ℝ) ≤ pos := by exact_mod_cast h
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck5, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v (b : ℝ) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        split at hcl
        · rename_i c hfind
          obtain ⟨hmem, hL, hU⟩ := CT.find_sound t a b c hfind
          have hcok := CT.allOk_sound t hok c hmem
          have hW := cell_sound c hcok v (by rw [hL, hpos]; exact hv1) (by rw [hU]; exact hvb)
          exact le_trans (by exact_mod_cast (decide_eq_true_eq.mp hcl)) hW
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf5_mem {cover : List (ℚ × ℚ × Bool)} {s : ℚ × ℚ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf5 cover := by
  simp only [badOf5, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

theorem mem_allTuples {nb i j k l : ℕ} (hi : i < nb) (hj : j < nb) (hk : k < nb) (hl : l < nb) :
    (i, j, k, l) ∈ allTuples nb := by
  simp only [allTuples, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨i, hi, j, hj, k, hk, l, hl, rfl⟩

/-! ### The five-point certificate from a checked table -/

theorem five_point_of_check (t : CT) (cover : List (ℚ × ℚ × Bool)) (bits fuel : ℕ)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 2 * c ≤ 19/100) (hok : t.allOk = true)
    (hcov : coverCheck5 t (2 * c) (1/2) S cover = true)
    (hrun : ∀ i j k l, i < (badOf5 cover).length → j < (badOf5 cover).length →
      k < (badOf5 cover).length → l < (badOf5 cover).length →
      ∃ pos pos', walk5 t c p bits fuel pos (boxOf5 (badOf5 cover) i j k l) = some pos') :
    ∀ x y z u : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ u → (c : ℝ) ≤ G5 p x y z u := by
  intro x y z u hx hy hz hu
  have hw := fun v : ℝ => wfun_nonneg v
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z + u
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G5
    linarith [hw x, hw y, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z),
      hw (y + z + u), hw (x + y + z + u)]
  push_neg at hsum
  set bad := badOf5 cover with hbad
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 1/2 * wfun v ∨ ∃ i, i < bad.length ∧
        ((bad.getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ (bad.getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := wfun_window v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover5_sound t hok _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := badOf5_mem hs he
        obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hmem
        refine ⟨i, hi, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h1
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h2
  rcases key x hx (by linarith) with hc | ⟨i, hi, hi1, hi2⟩
  · unfold G5; linarith [hw y, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key y hy (by linarith) with hc | ⟨j, hj, hj1, hj2⟩
  · unfold G5; linarith [hw x, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key z hz (by linarith) with hc | ⟨k, hk, hk1, hk2⟩
  · unfold G5; linarith [hw x, hw y, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key u hu (by linarith) with hc | ⟨l, hl, hl1, hl2⟩
  · unfold G5; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  obtain ⟨pos, pos', hwalk⟩ := hrun i j k l hi hj hk hl
  exact walk5_sound t hok c p hp bits fuel pos _ pos' hwalk x y z u
    ⟨hi1, hi2, hj1, hj2, hk1, hk2, hl1, hl2⟩

private lemma sum4 (f : Fin (5 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  show ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3
  exact Fin.sum_univ_four f

/-- The five-point functional, written out. -/
lemma F5_eq (p : ℕ) (g : Fin 4 → ℝ) :
    F 5 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2 + g 3)
      + 1/2 * wfun (g 0) + 1/2 * wfun (g 1) + 1/2 * wfun (g 2) + 1/2 * wfun (g 3)
      + 2/3 * wfun (g 0 + g 1) + 2/3 * wfun (g 1 + g 2) + 2/3 * wfun (g 2 + g 3)
      + wfun (g 0 + g 1 + g 2) + wfun (g 1 + g 2 + g 3)
      + 2 * wfun (g 0 + g 1 + g 2 + g 3) := by
  simp only [F, ptsN, sum4, Fin.sum_univ_five, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end
