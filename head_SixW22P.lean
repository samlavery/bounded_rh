/-
Riemann.fail submission — an unconditional critical-line proportion of 3365247/5000000 = 0.6730494,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW22P`: a bisection over the gaps with 220851 leaves over the
half-space g₀ ≤ g₄ (the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`), each leaf decided by a dyadic pyramid of lower bounds for `wfun`
(495 blocks, 7972 finest cells certified by the integer pipeline `cellN_soundZ'` — Taylor
enclosures of cos and sin at scale 10¹⁵ —, 15449 stored entries, every coarser entry at most its
children), read by the oracle `Pyr.lb` whose soundness is `Pyr.lb_sound`.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
The resulting constant is `(5800000000·H − 10259829)/5780026915 = 0.67304949…` with
`H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument,
which is what places the exact rational `3365247/5000000` strictly between the record and the
proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{IMPORTS}}
