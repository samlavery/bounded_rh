import AMW.PCellLeafZ

/-! ###### polytope cells: cache-shared derivative reads (bridge-port, 2026-10-07)

`lbDrF` is `lbDr` with the cover's level and cell range evaluated before the cover is read. The kernel then sees
`dcov2 top bk k ib g` with numerals, so two leaves whose reads cover the same cells share the kernel's cache for the whole
cover, not only for its entries. The value is `lbDr`'s (`lbDrF_eq`), so the tangent check with these reads
(`mokTZF`) is the old check (`mokTZF_eq`), and every soundness proof is reused unchanged. ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- `lbDr` with the cover's level `k`, last cell `ib` and first cell `g` forced -/
def lbDrF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 6)) fun k =>
        forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov2 top bk k ib g)
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

theorem lbDrF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbDrF top bk lo hi = lbDr top bk lo hi := by
  simp only [lbDrF, lbDr, forceR_eq]

/-- `treadU` through `lbDrF` -/
def treadUF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))

/-- `treadD` through `lbDrF` -/
def treadDF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)

theorem treadUF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) :
    treadUF R tD bD U p = treadU R tD bD U p := by
  simp only [treadUF, treadU, lbDrF_eq]

theorem treadDF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) :
    treadDF R tD bD L p = treadD R tD bD L p := by
  simp only [treadDF, treadD, lbDrF_eq]

/-- `mokZ` with the cache-shared reads -/
def mokZF (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (n L U l1 l2 p1 p2 : ℕ) :
    Bool :=
  (Nat.beq l1 0 || tcheckPZ R top bk n L U p1 (f p1) (treadUF R tD bD U p1) (treadDF R tD bD L p1))
    && (Nat.beq l2 0 || tcheckPZ R top bk n L U p2 (f p2) (treadUF R tD bD U p2) (treadDF R tD bD L p2))

/-! ### the pyramid reads the same way (the zero-order pieces and the constant term) -/

/-- `lb` with the cover's level, last cell and first cell forced -/
def lbF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 5)) fun k =>
        forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov top bk k ib g)
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

theorem lbF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbF top bk lo hi = lb top bk lo hi := by
  simp only [lbF, lb, forceR_eq]

/-- `zpc` through `lbF` -/
def zpcF (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (forceB (lbF top bk x0 x1) fun lbv =>
      Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
        (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
    true (Nat.ble x1 x0)

/-- `zside` through `zpcF` -/
def zsideG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
  iall (fun k => zpcF top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n

/-- `zsideF` through `zsideG` -/
def zsideFG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
  zsideG top bk v c p a b 1 right || zsideG top bk v c p a b 2 right || zsideG top bk v c p a b n right

/-- `tcheckZ` through `zsideFG` -/
def tcheckZG (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k) || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X))))
        || zsideFG top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) U n true)
      && (Nat.ble (rgA R k) L || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X))))
        || zsideFG top bk (lo32 X) (lo32 (hi32 X)) p L (rgA R k) n false)

/-- `tcheckPZ` through `tcheckZG` -/
def tcheckPZG (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tcheckZG R top bk n L U p X EU ED)
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) (Nat.beq L U && Nat.beq L p)

theorem zpcF_eq (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) :
    zpcF top bk v c p x0 x1 right = zpc top bk v c p x0 x1 right := by
  simp only [zpcF, zpc, lbF_eq]

theorem tcheckPZG_eq (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) :
    tcheckPZG R top bk n L U p X EU ED = tcheckPZ R top bk n L U p X EU ED := by
  simp only [tcheckPZG, tcheckPZ, tcheckZG, tcheckZ, zsideFG, zsideF, zsideG, zside, zpcF_eq]

/-- `mokZ` with the cache-shared derivative and pyramid reads -/
def mokZG (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (n L U l1 l2 p1 p2 : ℕ) :
    Bool :=
  (Nat.beq l1 0 || tcheckPZG R top bk n L U p1 (f p1) (treadUF R tD bD U p1) (treadDF R tD bD L p1))
    && (Nat.beq l2 0 || tcheckPZG R top bk n L U p2 (f p2) (treadUF R tD bD U p2) (treadDF R tD bD L p2))

end AMW.Cert.PyrD

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- `mokTZ` with the cache-shared reads -/
def mokTZF (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (zn L U k m p r : ℕ) :
    Bool :=
  Nat.ble m 1024 && mokZF R top bk tD bD f zn L U (mw1 k m) (mw2 k m) p r

theorem mokTZF_eq (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ)
    (zn L U k m p r : ℕ) : mokTZF R top bk tD bD f zn L U k m p r = mokTZ R top bk tD bD f zn L U k m p r := by
  simp only [mokTZF, mokTZ, mokZF, mokZ, treadUF_eq, treadDF_eq]

/-- `mokTZ` with the cache-shared derivative and pyramid reads -/
def mokTZG (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (zn L U k m p r : ℕ) :
    Bool :=
  Nat.ble m 1024 && mokZG R top bk tD bD f zn L U (mw1 k m) (mw2 k m) p r

theorem mokTZG_eq (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ)
    (zn L U k m p r : ℕ) : mokTZG R top bk tD bD f zn L U k m p r = mokTZ R top bk tD bD f zn L U k m p r := by
  simp only [mokTZG, mokTZ, mokZG, mokZ, treadUF_eq, treadDF_eq, tcheckPZG_eq]

/-- `mvK` with the cache-shared pyramid read -/
def mvKF (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.mul 1024 (lbF top bk L U))
      (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (f p))) (Nat.mul m (lo32 (f r)))) (Nat.beq k 3))
    (Nat.add (Nat.mul (Nat.sub 1024 m) (lbF top bk L U)) (Nat.mul m (lo32 (f p)))) (Nat.beq k 2))
    (Nat.mul 1024 (lo32 (f p))) (Nat.beq k 1)

theorem mvKF_eq (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : mvKF top bk f L U k m p r = mvK top bk f L U k m p r := by
  simp only [mvKF, mvK, lbF_eq]

end AMW.Cert.PCell
