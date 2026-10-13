/-
Riemann.fail submission — an unconditional critical-line proportion of 336549/500000 = 0.6730980,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW015N`: a bisection over the gaps with 183331 leaves over the
half-space g₀ ≤ g₄ (the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`).  Each leaf carries one of two tests.  The zero-order test bounds every pair
term below by a dyadic pyramid of lower bounds for `wfun` (496 blocks, 6052 finest cells
certified by the integer pipeline `cellN_soundZ'`, 11608 stored entries), read by `Pyr.lb`
(`Pyr.lb_sound`).  The mean-value test (101328 leaves) expands the functional about a centre `m` of
the box: `G(g) − G(m) = Σ_r (g_r − m_r)(b_r + Σ_(t∋r) a_t w'(ξ_t))`, one mean value point per pair
term (`exists_hasDerivAt_eq_slope`, with `w' = 2π N M / D³` from `kfun_closed`), the values
`w(s_t(m))` bounded by a point table of degenerate integer cells (2457 points), and `w'` bounded
on each pair-sum interval by two pyramids of lower bounds for `w' + 2` and `2 − w'` (280 blocks,
1922 finest cells each, every cell enclosed by an integer interval evaluation of `2π N M / D³`,
`cellD_sound`).
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
The resulting constant is `(28400000000·H − 50219163)/28300187750 = 0.67309803…` with
`H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument,
which is what places the exact rational `336549/500000` strictly between the record and the
proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{IMPORTS}}
