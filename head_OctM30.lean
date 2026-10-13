/-
Riemann.fail submission — an unconditional critical-line proportion of 6731889/10000000 = 0.6731889,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 8 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `OctM30` for the weighted functional on the seven gaps: a bisection
with 18100 leaves over the half-space g₀ ≤ g₆ (the pair weights are symmetric under gap reversal,
so the other half follows by the reflection `G_rev`).  Each leaf carries one of four tests.
* Zero-order (4449 leaves): every pair term is bounded below by a dyadic pyramid of lower bounds for
  `wfun` (496 blocks, 3968 finest cells certified by the integer pipeline `cellN_soundZ'`), read
  by `Pyr.lb` (`Pyr.lb_sound`) on three pieces of each wide range (`lb3`), so that the cover's overhang
  stays short.
* Slope (882 leaves): at a point `q` of the box (coded in the walk: per gap the lower end, the upper end
  or the midpoint, or, at 389 leaves, a basin centre clamped to the box) and for a chosen set of pair
  terms, each expanded term is bounded below by an affine function of the gaps.  A term whose range lies
  in one of 15 convex regions of `w` (each certified once by a chain of cells on which
  `w'' = 2π² P / D⁴ ≥ 0`, `cellConv_sound`) is bounded by its tangent at `q_t` (`tangent_le`); any other
  expanded term by `w(s) ≥ w(q_t) + w'(q_t)(s − q_t) − R_t`, the charge `R_t` read from lower bounds of
  `w' + 2` and `2 − w'` (a derivative pyramid of pairs, 397 blocks, 3688 finest cells, each enclosed
  by an integer interval evaluation of `2π N M / D³`, `cellD_sound`; the mean value theorem on each half).
  The values and slopes at `q_t` come from a point table of degenerate integer cells (2007 points), the
  remaining terms are read at zero order, and the linear part is bounded gap by gap.
* Minorant (11686 leaves): every pair term is bounded below on its range by its own affine function, read
  from the walk: the zero-order constant, the tangent at a grid point `p` inside a certified convex region
  `[za, zb]` (valid on the whole range once the derivative table shows `w' ≥ w'(p)` on `[zb, U]` and
  `w' ≤ w'(p)` on `[L, za]`; `ext_tangent`, `tangent_cert`), or a convex combination of two of these with
  weights out of 1024 (`mterm_ok`); the resulting affine bound is minimised over the box gap by gap
  (`gap_lo`, `mscheck_sound`).
* Basin (1 leaves): the box lies inside one of 34 boxes around the near-minimal local minima
  (and their mirror images), each certified once by the slope test at the minimum, where every pair
  term's range lies in a convex region.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
Basin boxes at the near-minimal local minima after six-point-convex-basins-2 by typh (Apache-2.0).
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
