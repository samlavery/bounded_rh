import AMW.PCDZ

/-! ###### the generic minorant leaf, kind-aware (mvt-engine, 2026-10-08)

`mcheckGXK` is `mcheckGX` with each term read by its kind (`mvKF`, `mcK`, `mslK`): a constant term reads no point, a
one-tangent term one point, and only a term that uses the constant reads the w pyramid.  `mcheckGX` reads the pyramid and
both points for every term whatever its kind; on a list-evaluated instance that is most of the leaf's kernel time.
`mcheckGXK_eq` is the equality with `mcheckGX`, so the soundness of `mcheckGX` applies unchanged. ###### -/

noncomputable section

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- gap `r`'s slope charge, kind-aware (`Ng` with `mslK`) -/
def NgK (f : ℕ → ℕ) (bs : List ℕ) (TS FS : List Term) (P S : List ℕ) (r : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.mul 2000000000 (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
      (Nat.mul (tA TS n) (mwT (tI FS n) (tJ FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (P.getD r 0))
    (Nat.add (Nat.add (Nat.mul 1024000000000 (bs.getD r 0)) (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
      (Nat.mul (tA TS n) (mslK f (tI FS n) (tJ FS n) (tA FS n) (PCell.tK FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (S.getD r 0))

/-- the minorant leaf's check for any term check `ok`, each term read by its kind -/
def mcheckGXK (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (Q : ℕ) (bs : List ℕ)
    (TS : List Term) (cN : ℕ) (c : Cl) (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Nat.ble
      (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (isum (fun n => Nat.mul (tA TS n)
        (mcK f false (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (PCell.tK FS n))) TS.length) Cp)
        (isum (fun r => Nat.mul (Nat.sub (c.U.getD r 0) (c.L.getD r 0)) (NgK f bs TS FS P S r)) Q))))
      (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (bs.getD r 0) (c.L.getD r 0)) Q))
        (Nat.mul 32768 (isum (fun n => Nat.mul (tA TS n) (mvKF top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n))
          (tI FS n) (tJ FS n) (tA FS n) (PCell.tK FS n))) TS.length)))
        (Nat.mul 10 (Nat.add (isum (fun n => Nat.mul (tA TS n) (mcK f true (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (PCell.tK FS n)))
          TS.length) Cm))))
    (Bool.rec (motive := fun _ => Bool) false
      (iall (fun n => ok (eL TS c n) (eU TS c n) (tI FS n) (tJ FS n) (tA FS n) (PCell.tK FS n)) TS.length)
      (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) Q))

theorem mcheckGXK_eq (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (Q : ℕ) (bs : List ℕ)
    (TS : List Term) (cN : ℕ) (c : Cl) (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ) :
    mcheckGXK ok top bk f Q bs TS cN c FS P S Cp Cm = mcheckGX ok top bk f Q bs TS cN c FS P S Cp Cm := by
  simp only [mcheckGXK, mcheckGX, NgK, Ng, mvKF_eq, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq]

end AMW.Cert.PyrD
