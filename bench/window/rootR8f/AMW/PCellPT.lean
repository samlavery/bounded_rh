import AMW.PCellIV

/-! ###### the point table as one checked tree (am-cert, bytes lever L2)

The point function is a binary dispatch tree on the block index `x >> 10` whose leaves are the blocks' `(x, word)` lists
(`ptl`).  One Boolean check over the tree (`ptOkT`: every leaf list by `ptlOkI`) certifies `PVI` for every lookup
(`ptT_sound`), in place of a definition and a soundness theorem per dispatch node and a theorem per block. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- a dispatch tree of point blocks: `nd k l r` sends blocks `< k` left and the rest right -/
inductive PTr where
  | lf (L : List (ℕ × ℕ))
  | nd (k : ℕ) (l r : PTr)

/-- the lookup: descend on the block index, then the block's list -/
def ptGet (t : PTr) (x : ℕ) : ℕ :=
  PTr.rec (motive := fun _ => ℕ) (fun L => ptl L x)
    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt (Nat.shiftRight x 10) k)) t

/-- every leaf list checked once (triples and precertified intervals) -/
def ptOkT (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh : ℕ) (t : PTr) : Bool :=
  PTr.rec (motive := fun _ => Bool) (fun L => ptlOkI R top bk tD bD n csh L) (fun _ _ _ bl br => bl && br) t

theorem ptT_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) :
    ∀ t : PTr, ptOkT R top bk tD bD n csh t = true → ∀ x, PVI x (ptGet t x) := by
  intro t
  induction t with
  | lf L => intro h x; exact ptlI_sound hlb hD hR hn L h x
  | nd k l r ihl ihr =>
    intro h x
    have h' : (ptOkT R top bk tD bD n csh l && ptOkT R top bk tD bD n csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptGet r x) (ptGet l x) (Nat.blt (Nat.shiftRight x 10) k))
    cases Nat.blt (Nat.shiftRight x 10) k
    · exact ihr h'.2 x
    · exact ihl h'.1 x

/-- a tree whose subtrees were checked separately (`nd k l r` with both checks given) -/
theorem ptOkT_nd {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {n csh k : ℕ} {l r : PTr}
    (hl : ptOkT R top bk tD bD n csh l = true) (hr : ptOkT R top bk tD bD n csh r = true) :
    ptOkT R top bk tD bD n csh (.nd k l r) = true := by
  show (ptOkT R top bk tD bD n csh l && ptOkT R top bk tD bD n csh r) = true
  rw [hl, hr]; rfl

end AMW.Cert.PCell

end
