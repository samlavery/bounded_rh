import AMW.PCellPT

/-! ###### the point table with block-relative keys and relative intervals (am-cert, bytes lever L3)

As `PCellPT`, but each leaf carries its block index `j` and its entries `(key, word)` use the key `x mod 1024` and the
word `triple + 2^96 · (da + 2^20 · db)` for the interval `[x − da, x + db]`.  A lookup decodes the word at the queried
point (`pwD`, a few operations, once per point and declaration), and returns `0` outside the leaf's block.  The check
(`ptOkTD`) runs on the decoded words at the entries' absolute points `1024 j + key`. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- an entry's word decoded at `x`: the triple, then the interval `[x − da, x + db]` in the standard fields -/
def pwD (x w : ℕ) : ℕ :=
  Nat.add (trip w) (Nat.add (Nat.shiftLeft (Nat.sub x (Nat.land (Nat.shiftRight w 96) 1048575)) 96)
    (Nat.shiftLeft (Nat.add x (Nat.shiftRight w 116)) 120))

/-- a block's list with block-relative keys -/
def ptlD (L : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ ih => Bool.rec (motive := fun _ => ℕ) ih (pwD x e.2) (Nat.beq e.1 (Nat.mod x 1024))) L

/-- the block check: every entry, decoded, at its absolute point `1024 j + key` -/
def ptlOkD (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh j : ℕ)
    (L : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2))
      && ivOk R top bk tD bD n csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2) && ih) L

theorem ptlD_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) (j : ℕ) :
    ∀ L : List (ℕ × ℕ), ptlOkD R top bk tD bD n csh j L = true → ∀ x, x / 1024 = j → PVI x (ptlD L x) := by
  intro L
  induction L with
  | nil => intro _ x _; exact pvi_zero x
  | cons e r ih =>
    intro h x hx
    have h' : (pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2))
      && ivOk R top bk tD bD n csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2)
      && ptlOkD R top bk tD bD n csh j r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨he, hiv⟩, hr⟩ := h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptlD r x) (pwD x e.2) (Nat.beq e.1 (Nat.mod x 1024)))
    cases hb : Nat.beq e.1 (Nat.mod x 1024)
    · exact ih hr x hx
    · have he1 : e.1 = x % 1024 := by have := Nat.eq_of_beq_eq_true hb; exact this
      have hxe : Nat.add (Nat.mul 1024 j) e.1 = x := by
        show 1024 * j + e.1 = x
        rw [he1, ← hx]; exact Nat.div_add_mod x 1024
      rw [hxe] at he hiv
      simp only [pt3e, Bool.and_eq_true] at he
      have hpv : PV x (trip (pwD x e.2)) := ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩
      exact ⟨hpv, ivOk_sound hlb hD hR hn hpv hiv⟩

/-- a dispatch tree of blocks: `lf j L` the block `j`; `nd k l r` blocks `< k` left -/
inductive PTrD where
  | lf (j : ℕ) (L : List (ℕ × ℕ))
  | nd (k : ℕ) (l r : PTrD)

def ptGetD (t : PTrD) (x : ℕ) : ℕ :=
  PTrD.rec (motive := fun _ => ℕ) (fun j L => Bool.rec (motive := fun _ => ℕ) 0 (ptlD L x) (Nat.beq (Nat.div x 1024) j))
    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt (Nat.div x 1024) k)) t

def ptOkTD (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh : ℕ) (t : PTrD) : Bool :=
  PTrD.rec (motive := fun _ => Bool) (fun j L => ptlOkD R top bk tD bD n csh j L) (fun _ _ _ bl br => bl && br) t

theorem ptTD_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) :
    ∀ t : PTrD, ptOkTD R top bk tD bD n csh t = true → ∀ x, PVI x (ptGetD t x) := by
  intro t
  induction t with
  | lf j L =>
    intro h x
    show PVI x (Bool.rec (motive := fun _ => ℕ) 0 (ptlD L x) (Nat.beq (Nat.div x 1024) j))
    cases hb : Nat.beq (Nat.div x 1024) j
    · exact pvi_zero x
    · exact ptlD_sound hlb hD hR hn j L h x (Nat.eq_of_beq_eq_true hb)
  | nd k l r ihl ihr =>
    intro h x
    have h' : (ptOkTD R top bk tD bD n csh l && ptOkTD R top bk tD bD n csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptGetD r x) (ptGetD l x) (Nat.blt (Nat.div x 1024) k))
    cases Nat.blt (Nat.div x 1024) k
    · exact ihr h'.2 x
    · exact ihl h'.1 x

theorem ptOkTD_nd {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {n csh k : ℕ}
    {l r : PTrD} (hl : ptOkTD R top bk tD bD n csh l = true) (hr : ptOkTD R top bk tD bD n csh r = true) :
    ptOkTD R top bk tD bD n csh (.nd k l r) = true := by
  show (ptOkTD R top bk tD bD n csh l && ptOkTD R top bk tD bD n csh r) = true
  rw [hl, hr]; rfl

end AMW.Cert.PCell

end
