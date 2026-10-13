/-
AMW/BHalf.lean — the AMTOPA prime side: eventual LocalHypsCore and TracesBoundsD.
b ≥ 1/2 eventually is `eventually_bW_ge_half` (AMW/Floor: b_T → bInf > 1/2).
-/
import AMW.Concrete
import AMW.Floor

noncomputable section

open Real Set MeasureTheory Filter

namespace AMW

open Zeta23

variable {P : Params}

theorem eventually_bAM_ge_half (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ AdmWindow.bv (WAM P T) (P.L T) :=
  eventually_bW_ge_half hP

/-- eventual `LocalHypsCore` for the AMTOPA data. -/
theorem localHypsCoreAM_eventually (hP : P.Valid) : LocalHypsCoreWEventually P (WAM P) (cAMW P.ϱ) :=
  localHypsCoreW_eventually hP (admWindow_WAM hP) (eventually_bAM_ge_half hP)

/-- **TracesBoundsD for the AMTOPA window.** -/
theorem tracesBoundsAM_concrete {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z) :
    ThmD.TracesBoundsD P (concreteDataW P (WAM P) Z).aT (concreteDataW P (WAM P) Z).bT
      (concreteDataW P (WAM P) Z).JT (concreteDataW P (WAM P) Z).trG (concreteDataW P (WAM P) Z).trG2
      (concreteDataW P (WAM P) Z).Ncnt :=
  tracesBoundsW_concrete hP inp (admWindow_WAM hP) (localHypsCoreAM_eventually hP)

end AMW

end
