/-
Riemann.fail submission — an unconditional critical-line proportion of 0.6727382,
strictly above the pinned record 2 − 1/cMT = 0.67250070…

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned
Zeta23 development (the Montgomery–Taylor window at λ = 1), specialised to n = 3 and made
unconditional by a kernel-checked finite certificate (`three_point_cert`: 368 interval cell
lemmas and 487 leaves of a two-dimensional bisection), assembled with the window-count
pressure bookkeeping (`n_point_bound_w'`).  The resulting constant is
`(447000000·H − 297200)/446400399 = 0.67273822…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`,
and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places
the exact rational `3363691/5000000` strictly between the record and the proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib;
no placeholders, no `native_decide`, no additional axioms.  Sources: the Zeta Lab bridge
(`Zeta23Ext.Bridge`, `Zeta23Ext.BridgeW`, `ThreePoint`), MIT-licensed, ported here into one
file; the counting functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{IMPORTS}}
import Zeta23.Main
import Zeta23.Final
import Zeta23.Statement.SeamClosed
import Zeta23.ThmD.Functional
