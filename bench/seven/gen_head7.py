#!/usr/bin/env python3
"""Header of the seven-point slope/basin certificate submission: head_<NAME>.lean (kappa_<NAME>.txt from gen_tail7.py).
Usage: gen_head7.py NAME   (reads data_<NAME>.lean and kappa_<NAME>.txt in the workspace root)"""
import sys, re, os
from fractions import Fraction as F
ROOT = os.path.expanduser("~/work/riemann-submission")
NAME = sys.argv[1]
kn, kd, P, R, D = (int(x) for x in open(os.path.join(ROOT, f"kappa_{NAME}.txt")).read().split())
kappa = F(kn, kd)
phi_lo = (P * (F(3, 2) - F(8274993018, 10**10)) - R) / D
d = open(os.path.join(ROOT, f"data_{NAME}.lean"), encoding="utf-8").read()
mm = re.search(r"pyramid table \((\d+) blocks, (\d+) finest cells\), derivative table \((\d+) blocks, (\d+) finest cells\), "
               r"point table \((\d+) points\), (\d+) basins, (\d+) leaves \(half-space; (\d+) zero-order, (\d+) slope \((\d+) at centres\), (\d+) in basins\)", d)
blocks, finest, dblocks, dfinest, points, nbas, leaves, nZ, nS, nSc, nB = (int(x) for x in mm.groups())
nreg = len(re.findall(r"\[\d", d[d.index("def REG"):d.index("theorem hR")]))
open(os.path.join(ROOT, f"head_{NAME}.lean"), "w", encoding="utf-8").write(f"""/-
Riemann.fail submission — an unconditional critical-line proportion of {kappa.numerator}/{kappa.denominator} = {float(kappa):.7f},
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 7 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `{NAME}` for the weighted functional on the six gaps: a bisection
with {leaves} leaves over the half-space g₀ ≤ g₅ (the pair weights are symmetric under gap reversal,
so the other half follows by the reflection `G_rev`).  Each leaf carries one of three tests.
* Zero-order ({nZ} leaves): every pair term is bounded below by a dyadic pyramid of lower bounds for
  `wfun` ({blocks} blocks, {finest} finest cells certified by the integer pipeline `cellN_soundZ'`), read
  by `Pyr.lb` (`Pyr.lb_sound`) on three pieces of each wide range (`lb3`), so that the cover's overhang
  stays short.
* Slope ({nS} leaves): at a point `q` of the box (coded in the walk: per gap the lower end, the upper end
  or the midpoint, or, at {nSc} leaves, a basin centre clamped to the box) and for a chosen set of pair
  terms, each expanded term is bounded below by an affine function of the gaps.  A term whose range lies
  in one of {nreg} convex regions of `w` (each certified once by a chain of cells on which
  `w'' = 2π² P / D⁴ ≥ 0`, `cellConv_sound`) is bounded by its tangent at `q_t` (`tangent_le`); any other
  expanded term by `w(s) ≥ w(q_t) + w'(q_t)(s − q_t) − R_t`, the charge `R_t` read from lower bounds of
  `w' + 2` and `2 − w'` (a derivative pyramid of pairs, {dblocks} blocks, {dfinest} finest cells, each enclosed
  by an integer interval evaluation of `2π N M / D³`, `cellD_sound`; the mean value theorem on each half).
  The values and slopes at `q_t` come from a point table of degenerate integer cells ({points} points), the
  remaining terms are read at zero order, and the linear part is bounded gap by gap.
* Basin ({nB} leaves): the box lies inside one of {nbas} boxes around the near-minimal local minima
  (and their mirror images), each certified once by the slope test at the minimum, where every pair
  term's range lies in a convex region.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
Basin boxes at the near-minimal local minima after six-point-convex-basins-2 by typh (Apache-2.0).
The resulting constant is `({P}·H − {R})/{D} = {f"{float(phi_lo):.12f}"[:10]}…` with
`H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument,
which is what places the exact rational `{kappa.numerator}/{kappa.denominator}` strictly between the record and the
proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
{{{{IMPORTS}}}}
""")
print(f"wrote head_{NAME}.lean; kappa = {kappa} = {float(kappa):.7f}")
