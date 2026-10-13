/-
Riemann.fail submission — an unconditional critical-line proportion of 6731889/10000000 = 0.6731889,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 8 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `OctY30` for the weighted functional on the seven gaps: a bisection
with 19143 leaves over the half-space g₀ ≤ g₆ (the pair weights are symmetric under gap reversal,
so the other half follows by the reflection `G_rev`).  Each leaf (1150 of them lie in the reflected
half-space) carries one of two tests.
* Zero-order (4006 leaves): every pair term is bounded below by a dyadic pyramid of lower bounds for
  `wfun` (496 blocks, 992 finest cells certified by the integer pipeline `cellN_soundZ'`), read
  by `Pyr.lb` (`Pyr.lb_sound`) on three pieces of each wide range (`lb3`), so that the cover's overhang
  stays short.
* Minorant (13987 leaves): every pair term is bounded below on its range by its own affine function, read
  from the walk: the zero-order constant, the tangent at a grid point `p` inside one of 15 convex
  regions `[za, zb]` of `w` (each certified once by a chain of cells on which `w'' = 2π² P / D⁴ ≥ 0`,
  `cellConv_sound`), valid on the whole range once the derivative table shows `w' ≥ w'(p)` on `[zb, U]`
  and `w' ≤ w'(p)` on `[L, za]` (`ext_tangent`, `tangent_cert`), or a convex combination of two of these
  with weights out of 1024 (`mterm_ok`); the resulting affine bound is minimised over the box gap by gap
  (`gap_lo`, `mscheck_sound`).  The derivative reads come from a pyramid of lower bounds of `w' + 2` and
  `2 − w'` (352 blocks, 832 finest cells, each enclosed by an integer interval evaluation of
  `2π N M / D³`, `cellD_sound`), the values and slopes at the grid points from a point table of degenerate
  integer cells (331 points).
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
The resulting constant is `(3725000000·H − 14200000)/3700097957 = 0.67318896…` with
`H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument,
which is what places the exact rational `6731889/10000000` strictly between the record and the
proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{IMPORTS}}
