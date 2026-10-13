#!/usr/bin/env python3
"""Header (docstring + imports placeholder) of a pyramid-oracle submission file: head_<NAME>.lean.
Usage: gen_head_pyr.py NAME   (reads <NAME>_params.txt and data_<NAME>.lean; constant as gen_tail_w.py computes it)"""
import sys, re, math
from fractions import Fraction as F
NAME = sys.argv[1]
Q, SA, aN, bN, cN, _ = open(f"{NAME}_params.txt").read().split()[:6]
Q = int(Q); SA = int(SA); bN = [int(x) for x in bN.split(",")]; cN = int(cN)
n = Q + 1
c = F(cN, SA); B = sum(F(b, SA) for b in bN); m = (n - 1) + int(1 / c)
num_H = m; num_0 = -B * (m - (n - 1)); den = m - c * (m - (n - 1))
L = math.lcm(num_0.denominator, den.denominator)
P = int(num_H * L); R = int(-num_0 * L); D = int(den * L)
g = math.gcd(math.gcd(P, R), D); P //= g; R //= g; D //= g
H_lo = F(3, 2) - F(8274993018, 10**10)
phi_lo = (P * H_lo - R) / D
kappa = F(int(phi_lo * 10**7), 10**7)
d = open(f"data_{NAME}.lean", encoding="utf-8").read()
mm = re.search(r"certificate data `\w+`: pyramid table \((\d+) blocks, (\d+) finest cells, (\d+) entries\), (\d+) leaves", d)
blocks, finest, entries, leaves = (int(x) for x in mm.groups())
open(f"head_{NAME}.lean", "w", encoding="utf-8").write(f"""/-
Riemann.fail submission — an unconditional critical-line proportion of {kappa.numerator}/{kappa.denominator} = {float(kappa):.7f},
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = {n} with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `{NAME}`: a bisection over the gaps with {leaves} leaves over the
half-space g₀ ≤ g₄ (the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`), each leaf decided by a dyadic pyramid of lower bounds for `wfun`
({blocks} blocks, {finest} finest cells certified by the integer pipeline `cellN_soundZ'` — Taylor
enclosures of cos and sin at scale 10¹⁵ —, {entries} stored entries, every coarser entry at most its
children), read by the oracle `Pyr.lb` whose soundness is `Pyr.lb_sound`.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
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
open(f"kappa_{NAME}.txt", "w").write(f"{kappa.numerator} {kappa.denominator} {P} {R} {D}\n")
print(f"wrote head_{NAME}.lean; kappa = {kappa} = {float(kappa):.7f}; constant ({P} H - {R})/{D} >= {float(phi_lo):.10f}")
