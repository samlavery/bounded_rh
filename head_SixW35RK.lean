/-
Riemann.fail submission — an unconditional critical-line proportion of 6730187/10000000 = 0.6730187,
strictly above the pinned record 2 − 1/cMT = 0.67250070…

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW35RK`: a table of 10345 interval cells, each certified by
an integer pipeline (Taylor enclosures of cos and sin at scale 10¹⁵, `cellN_soundZ`), and a
bisection over the gaps with 112490 leaves over the half-space
g₀ ≤ g₄; the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`.  The resulting constant is
`(9800000000·H − 17339711)/9766693039 = 0.67301870…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is
enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places the exact rational
`6730187/10000000` strictly between the record and the proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{IMPORTS}}
