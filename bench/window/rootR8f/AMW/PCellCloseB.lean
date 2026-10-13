import AMW.PCellClose

/-! ###### polytope cells: closure splits at any cut, and the region-boundary cut (mvt-engine; TZ.md §5, BSPLIT)

A split may cut a range at any point `q`, not only its midpoint: covering both closed children covers the cell for every
`q` (`cov_gsplitQ`, `cov_ssplitQ`, from `cov_gsplit` / `cov_ssplit` and `cov_cupd`). The sizer's boundary split
(BSPLIT, mode 1) cuts `[lo, hi]` at the region boundary `z` (from the instance's sorted list `BND`) nearest the midpoint
with `lo + bm ≤ z` and `z + bm ≤ hi`, the first in list order on a tie (`bcutL`); with no such boundary it returns the
midpoint (the sizer never asks for one then). Nothing about `bcutL` is needed for soundness. ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- `|2z − s|` in Nat -/
def bdist (s z : ℕ) : ℕ := Nat.add (Nat.sub (Nat.add z z) s) (Nat.sub s (Nat.add z z))

/-- the region-boundary cut of `[lo, hi]` (the running choice and whether one was found, folded over `BND`) -/
def bcutL (BND : List ℕ) (bm lo hi : ℕ) : ℕ :=
  (List.rec (motive := fun _ => ℕ × Bool → ℕ × Bool) (fun acc => acc)
    (fun z _ ih acc => ih (Bool.rec (motive := fun _ => ℕ × Bool) acc (z, true)
      (Nat.ble (Nat.add lo bm) z && Nat.ble (Nat.add z bm) hi &&
        (!acc.2 || Nat.blt (bdist (Nat.add lo hi) z) (bdist (Nat.add lo hi) acc.1)))))
    BND (Nat.shiftRight (Nat.add lo hi) 1, false)).1

/-- the cut of gap `r` in mode `md` (0: the midpoint, 1: the region boundary) -/
def qB (BND : List ℕ) (bm : ℕ) (c : Cl) (r md : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (qG c r) (bcutL BND bm (c.L.getD r 0) (c.U.getD r 0)) (Nat.beq md 1)

/-- the cut of pair `k`'s bounds in mode `md` -/
def qBr (BND : List ℕ) (bm : ℕ) (c : Cl) (k md : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (qR c k) (bcutL BND bm (c.A.getD k 0) (c.B.getD k 0)) (Nat.beq md 1)

/-- gap `r` cut at any `q`: child A (`u_r := q`, edge `r → r+1`), child B (`l_r := q`, edge `r+1 → r`), both closed -/
theorem cov_gsplitQ {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {P : (ℕ → ℝ) → Prop} {c : Cl} (hSL : SLok Q PR SL)
    (hPR : PRok Q PR) (r q : ℕ) (hL' : c.L.length = Q) (hU' : c.U.length = Q) (hr : r < Q)
    (hA : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U.set r q, c.A, c.B⟩ r (r + 1)))
    (hB : CovBy Q PR P (cupd Q PR SL ⟨c.L.set r q, c.U, c.A, c.B⟩ (r + 1) r)) : CovBy Q PR P c :=
  cov_gsplit r q hL' hU' hr (cov_cupd hSL hPR (by omega) (by omega) hA) (cov_cupd hSL hPR (by omega) (by omega) hB)

/-- pair `k` cut at any `q`: child A (`B_k := q`, edge `i → j`), child B (`A_k := q`, edge `j → i`), both closed -/
theorem cov_ssplitQ {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {P : (ℕ → ℝ) → Prop} {c : Cl} (hSL : SLok Q PR SL)
    (hPR : PRok Q PR) (k q : ℕ) (hA'' : c.A.length = PR.length) (hB'' : c.B.length = PR.length) (hk : k < PR.length)
    (hA : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U, c.A, c.B.set k q⟩ (pI PR k) (pJ PR k)))
    (hB : CovBy Q PR P (cupd Q PR SL ⟨c.L, c.U, c.A.set k q, c.B⟩ (pJ PR k) (pI PR k))) : CovBy Q PR P c := by
  obtain ⟨h1, h2⟩ := hPR k hk
  exact cov_ssplit k q hA'' hB'' hk (cov_cupd hSL hPR (by omega) h2 hA) (cov_cupd hSL hPR h2 (by omega) hB)

end AMW.Cert.PCell
