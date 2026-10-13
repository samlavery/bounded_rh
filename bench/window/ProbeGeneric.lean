import ChallengeDeps.CandidateSpec
import Zeta23.ThmD.Mult
import Zeta23.ThmD.ZeroSideD
import Zeta23.XiPrime.Window
import Zeta23.XiPrime.QuarticWindow.ZeroSide
import Zeta23.XiPrime.QuarticWindow.Moments
import Zeta23.XiPrime.QuarticWindow.ModWindow

/-! Probe: the window-generic pieces of the pinned artifact are importable next to the template's
imports, have the expected statements, and use only the standard axioms. -/

open Zeta23

#check @XiPrime.blockInputsV_of'
#check @XiPrime.GzGpV_of'
#check @XiPrime.eventually_tailPackageV_of
#check @XiPrime.tendsto_cRatio_cWin
#check @XiPrime.tendsto_JT_of_autocorr_close
#check @XiPrime.admWindow_phiM
#check @XiPrime.edge_estimate
#check @AdmWindow.localHypsCore
#check @ThmD.sumA2g_close
#check @ThmD.tracesBoundsD_of_factsD
#check @ThmD.autocorr_deriv_facts
#check @Params.atV_trGtilde
#check @Params.atV_a

#print axioms XiPrime.eventually_tailPackageV_of
#print axioms XiPrime.tendsto_JT_of_autocorr_close
#print axioms XiPrime.admWindow_phiM
#print axioms AdmWindow.localHypsCore
