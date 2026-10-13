
/-! ###### four-point checker in the bit-walk format (reuses the cell search tree) ###### -/

section Checker4Defs

namespace Zeta23Ext.Bridge.ThreePoint

def Box.widthArg (b : Box) : ℕ :=
  let w0 := b.xu - b.xl; let w1 := b.yu - b.yl; let w2 := b.zu - b.zl
  if w1 ≤ w0 ∧ w2 ≤ w0 then 0 else if w2 ≤ w1 then 1 else 2

def Box.mid (b : Box) : ℕ → ℚ
  | 0 => (b.xl + b.xu) / 2
  | 1 => (b.yl + b.yu) / 2
  | _ => (b.zl + b.zu) / 2

def Box.setHi (b : Box) (ax : ℕ) (q : ℚ) : Box :=
  match ax with
  | 0 => { b with xu := q }
  | 1 => { b with yu := q }
  | _ => { b with zu := q }

def Box.setLo (b : Box) (ax : ℕ) (q : ℚ) : Box :=
  match ax with
  | 0 => { b with xl := q }
  | 1 => { b with yl := q }
  | _ => { b with zl := q }

def leafCheck4 (t : CT) (c p : ℚ) (b : Box) : Bool :=
  decide (c ≤ (b.xl + b.yl + b.zl) / p
    + 2/3 * termW5 t b.xl b.xu + 2/3 * termW5 t b.yl b.yu + 2/3 * termW5 t b.zl b.zu
    + termW5 t (b.xl + b.yl) (b.xu + b.yu) + termW5 t (b.yl + b.zl) (b.yu + b.zu)
    + 2 * termW5 t (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu))

def walk4 (t : CT) (c p : ℚ) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk4 t c p bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk4 t c p bits fuel pos' (b.setLo ax q)
      else if leafCheck4 t c p b then some (pos + 1) else none

def boxOf4 (bad : List (ℚ × ℚ)) (i j k : ℕ) : Box :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint

end Checker4Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

def Box.mem (b : Box) (x y z : ℝ) : Prop :=
  (b.xl : ℝ) ≤ x ∧ x ≤ b.xu ∧ (b.yl : ℝ) ≤ y ∧ y ≤ b.yu ∧ (b.zl : ℝ) ≤ z ∧ z ≤ b.zu

theorem leaf4_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (b : Box)
    (h : leafCheck4 t c p b = true) (x y z : ℝ) (hm : b.mem x y z) : (c : ℝ) ≤ G4 p x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  simp only [leafCheck4, decide_eq_true_eq] at h
  have w0 := termW5_sound t hok _ _ x hx1 hx2
  have w1 := termW5_sound t hok _ _ y hy1 hy2
  have w2 := termW5_sound t hok _ _ z hz1 hz2
  have w3 := termW5_sound t hok (b.xl + b.yl) (b.xu + b.yu) (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w4 := termW5_sound t hok (b.yl + b.zl) (b.yu + b.zu) (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := termW5_sound t hok (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G4
  linarith

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℚ) (x y z : ℝ) (hm : b.mem x y z)
    (hle : match ax with | 0 => x ≤ q | 1 => y ≤ q | _ => z ≤ q) : (b.setHi ax q).mem x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  match ax with
  | 0 => exact ⟨hx1, hle, hy1, hy2, hz1, hz2⟩
  | 1 => exact ⟨hx1, hx2, hy1, hle, hz1, hz2⟩
  | n + 2 => exact ⟨hx1, hx2, hy1, hy2, hz1, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℚ) (x y z : ℝ) (hm : b.mem x y z)
    (hge : match ax with | 0 => (q : ℝ) ≤ x | 1 => (q : ℝ) ≤ y | _ => (q : ℝ) ≤ z) :
    (b.setLo ax q).mem x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  match ax with
  | 0 => exact ⟨hge, hx2, hy1, hy2, hz1, hz2⟩
  | 1 => exact ⟨hx1, hx2, hge, hy2, hz1, hz2⟩
  | n + 2 => exact ⟨hx1, hx2, hy1, hy2, hge, hz2⟩

theorem walk4_split (t : CT) (c p : ℚ) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk4 t c p bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk4 t c p bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk4 t c p bits (fuel + 1) pos b = some pos' := by
  simp only [walk4, hbit, if_true, h1]
  exact h2

theorem walk4_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk4 t c p bits fuel pos b = some pos' →
      ∀ x y z : ℝ, b.mem x y z → (c : ℝ) ≤ G4 p x y z := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk4] at h
  | succ fuel ih =>
    intro pos b pos' h x y z hm
    simp only [walk4] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 x y z
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h x y z
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total x (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q x y z hm hs)
          · exact hhi (Box.setLo_mem b 0 q x y z hm hs)
        | 1, hlo, hhi =>
          rcases le_total y (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q x y z hm hs)
          · exact hhi (Box.setLo_mem b 1 q x y z hm hs)
        | n + 2, hlo, hhi =>
          rcases le_total z (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 2) q x y z hm hs)
          · exact hhi (Box.setLo_mem b (n + 2) q x y z hm hs)
    · exact leaf4_sound t hok c p hp b hleaf x y z hm

theorem four_point_of_check' (t : CT) (cover : List (ℚ × ℚ × Bool)) (bits fuel : ℕ)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 3/2 * c ≤ 19/100) (hok : t.allOk = true)
    (hcov : coverCheck5 t (3/2 * c) (1/2) S cover = true)
    (hrun : ∀ i j k, i < (badOf5 cover).length → j < (badOf5 cover).length →
      k < (badOf5 cover).length →
      ∃ pos pos', walk4 t c p bits fuel pos (boxOf4 (badOf5 cover) i j k) = some pos') :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (c : ℝ) ≤ G4 p x y z := by
  intro x y z hx hy hz
  have hw := fun v : ℝ => wfun_nonneg v
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G4; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  push_neg at hsum
  set bad := badOf5 cover with hbad
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 2/3 * wfun v ∨ ∃ i, i < bad.length ∧
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
  · unfold G4; linarith [hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key y hy (by linarith) with hc | ⟨j, hj, hj1, hj2⟩
  · unfold G4; linarith [hw x, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key z hz (by linarith) with hc | ⟨k, hk, hk1, hk2⟩
  · unfold G4; linarith [hw x, hw y, hw (x + y), hw (y + z), hw (x + y + z)]
  obtain ⟨pos, pos', hwalk⟩ := hrun i j k hi hj hk
  exact walk4_sound t hok c p hp bits fuel pos _ pos' hwalk x y z ⟨hi1, hi2, hj1, hj2, hk1, hk2⟩

end Zeta23Ext.Bridge.ThreePoint

end
