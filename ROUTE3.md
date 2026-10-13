# Route 3: a third trace moment (triple correlation) as new arithmetic input. Plan and source facts (lead, 2026-10-12)

Sam's choice (10-12): route 3.

## Source facts. Zeta23 paper, refs/zeta23_paper.txt (helix_frobenius), §7.5, lines 1605–1667
- (e) The prime-side evaluation of tr G̃^k by the paper's diagonal method is available **unconditionally exactly in the Rudnick–Sarnak range kλ < 2** [RS96].
  - So k = 3 requires λ < 2/3.
  - The paper adds: "an odd moment does not lower Λ1(0). Thus, unconditionally, higher moments add nothing to the n+-bound on (1/2, 1)."
- Prop 7.4 (Cap): any Prop 4.1-type certificate with band λ certifies at most λ·N on-line points.
  - So the third moment of the SAME compression, in its unconditional range λ < 2/3, is capped below 2/3·N, under the current record 0.6736.
  - This is a property of that instrument: the third moment of the band-λ compression in the RS range.
- (g) **Under RH**, tr G̃³ in the full band λ < 1 is a theorem [Hej94, RS96]. With cubic weights the paper gets 0.85082 for distinct zeros (also using Ns ≥ 19/27 on RH). This is conditional, so not admissible.
- (f) Moments at λ = 1: m_k(1) = 1, 4/3, 2, 13/4 for k = 1..4 (sine-kernel limits; read from a garbled extraction, to be checked against the PDF).

## What route 3 therefore is
A NEW THEOREM: tr G̃³ (triple correlation) evaluated UNCONDITIONALLY for band λ ∈ (2/3, 1], beyond the RS range, in the Weil-form framework. This is the analogue of what BGSTB24 did for the second moment (Montgomery's theorem made unconditional). Then a three-moment certificate for distinct on-line zeros.

## Phase A (desk, pre-registered). Two questions decide whether to proceed
- **A1 (window-scope), source read.** Hejhal 1994 (IMRN no. 7, 293–302), Rudnick–Sarnak 1996 (Duke 81), BGSTB24 (arXiv), GLSS25 (arXiv:2503.15449).
  - Where exactly does RH enter the k = 3 evaluation beyond kλ < 2?
    - Only to place γ on the line / define the correlation (which the Weil-form framework avoids, as BGSTB24 avoided it)?
    - Or in a prime-sum / off-diagonal estimate that needs RH-strength input?
  - Does BGSTB24's unconditional technique extend to k = 3?
  - Lead prediction: RH enters in the off-diagonal Λ-correlation bounds, so not removable by the framework trick alone (≈ 65%).
- **A2 (am-cert), prize.** If tr G̃³ at λ = 1 WERE available unconditionally (m3 = 2), what is the best certificate for DISTINCT ON-LINE zeros?
  - Unconditional means off-line pairs are allowed; the board quantity is N₀*.
  - Method: the Lemma 3.2 / Prop 4.4 analogue with polynomial weights up to cubic, plus Schur–Horn majorisation, by LP over integer multiplicity configurations and off-line pair blocks.
  - Also: does it combine with the n-point / Gram-defect refinement?
  - Lead prediction: 0.70–0.78 for distinct on-line zeros (wide).
- Go / no-go:
  - proceed to Phase B (proof of the third-moment evaluation) only if A1 finds a plausible unconditional path AND A2's prize is ≥ 0.69;
  - otherwise record the state and what input would be needed.

## A1 RESULT (window-scope, ROUTE3_A1.md): premise overturned
- RS96 Thm 3.1 gives the smoothed n-level sums over complex zeros WITHOUT RH. RH enters only in the smooth-to-sharp, real-γ passage (Thm 3.2).
- For the 3-cycle tr G̃³, Σ|ξ| = 2(max − min) ≤ 2λ < 2, so the third moment is UNCONDITIONAL for the whole band λ < 1.
  - Zeta23 (e)'s kλ < 2 is a sufficient bound, not the sharp one.
  - Exact: kλ < 2 (even k), (k − 1)λ < 2 (odd k).
  - Lead checked the support computation independently: agrees.
- Remaining work at the trace level: adapt the localization (smooth weights on the Gabor grid). Soft analysis; Lean cost not yet sized.
- Hejhal 1994 not obtained (paywall).

## Lead's quick check for A2
- The two-moment extremal (2/3·N simple on-line + 1/6·N off-line pairs at depth → 0, spectrally eigenvalue 2) has tr³ = 2/3 + 8/6 = 2 = m3(1).
- So a PURELY SPECTRAL three-moment certificate stays at 2/3 for N₀*. Consistent with Zeta23 (e): an odd moment does not lower Λ1(0).
- Any gain must come at the CONFIGURATION level: a three-point term in the local (Ainta / Gram-defect) functional. A2 is refocused there.
- Nearest relative to read at source: Knausgård arXiv:2610.08965 (unconditional 67.35% simple on-line, 83.9% distinct; pair correlation only). A1b → window-scope.

## A1b (window-scope, ROUTE3_A1b.md): Knausgård arXiv:2610.08965 read at source
- Pair correlation only; the same scheme as the board chain. His θ = 17/20 is our d.
- Ceilings, critical line: 0.67357 (8 points), 0.67383 (all pairs), 0.68185 (any window).
- No three-point term.
- All published walls are two-moment walls.
- Lead: Yang–Yang claims an unconditional m₄ = 13/4 ("Lemma D"). If valid at λ near 1, it excludes the two-moment extremal (m₄ = 10/3). A1c (window-scope) checks it at source. Lead prediction: ≈ 80% it hides a Hardy–Littlewood input.

## A1c (window-scope, ROUTE3_A1c.md): Yang–Yang "More than 0.7962…" (Zenodo 10.5281/zenodo.21975236, no arXiv)
- Lemma D (Thm 7.5) is a Lavrik-type mean square for SMALL moduli over full ranges.
- Consuming it for m₄ → 13/4 relies on archived, undefined steps: a per-cell ℓ₁, an interface mismatch, short- versus full-range.
- NOT established as written.
- THE LEAD: an averaged shifted-convolution asymptotic for Λ∗Λ over |h| ≤ X²/T could replace Hardy–Littlewood. MRT 2019 gives Λ·Λ for H ≥ X^{8/33+ε}, which translates to λ ≥ 33/50 = 0.66.
- If it extends to Λ∗Λ, an unconditional m₄ exists on λ ∈ (0.66, 1).
  - Prize per Zeta23 (f): up to 13/18 ≈ 0.722 at λ → 1 (spectral; HL*(4)).
- Dispatched:
  - A1d (window-scope): MRT I/II and sequels at source, for coverage of Λ∗Λ averaged correlations. Lead: 55% needs an extension / 25% direct / 20% not available.
  - A2 extension (am-cert): prize table vs λ ∈ [0.66, 1) for a four-moment certificate of N₀*.
- Caveat: Lean formalization of MRT-type results would be a very large project. Size it only if the math and the prize hold.

## A2 RESULT (am-cert, ROUTE3_A2.md): the third moment alone gives NO gain unconditionally (pre-registered threshold 0.69 not met)
- The third moment enters only through D = m3 − 3m2 + 2 = avg x(x−1)(x−2).
- Unconditional "absorbers" supply either sign of D at vanishing m2 cost:
  - D > 0: stacked off-line pairs;
  - D < 0: two off-line pairs with a shared imaginary part and orthogonal real parts.
- So valid cubic certificates collapse to Lemma 3.2: spectral 0.6725, geometric LP → two-moment value.
- If interacting deep off-line pairs were EXCLUDED: max 0.685558 (cos(8s/5)-like window). Under a depth bound δ0, the gain is ≈ +0.005 (δ0 = 1 spacing) up to 0.0137 (δ0 → 0).
- **Forward inputs identified:**
  - (i) the FOURTH moment (HL*(4) → 13/18; the MRT route, A1d running);
  - (ii) DEPTH CONTROL of off-line zeros: mass of zeros deeper than δ spacings. This is a zero-density-near-the-line input, Selberg-type, needed with explicit constants.
- Refutation spec for the "no gain" instrument claim: ROUTE3_A2.md §10 (self-contained LP). am-cert disclosed it had already run it; an independent re-run is the check. For Sam to route.

## A1d (window-scope, ROUTE3_A1d.md): MRT coverage of the fourth moment
- MRT I Thm 1.3 covers Λ·Λ, d_k·d_l, etc. for H ≥ X^{8/33+ε}.
  - Λ∗Λ is NOT covered as stated: the extension via Λ₂ = μ∗log² looks standard but is unwritten. The leg weights are unwritten too.
  - Evans's almost primes are unweighted only; balanced factorizations lose the bilinear advantage.
- Threshold: scale m = T^u is covered iff u ≥ 33/25. Coverage starts at λ > 0.66.
- BUT scales m ∈ (T, T^{33/25}) are uncovered at EVERY λ. Shifts there are O(1), which is pointwise Hardy–Littlewood (≈ 11.5% of R at λ = 1; matches Yang–Yang's 0.885).
- ⇒ A two-sided unconditional m₄ is NOT available from current results (a property of these instruments).
- A one-sided m₄ ≤ 13/4 + Δ with Δ < 1/12 would exclude the two-moment extremal (10/3). The uncovered part needs a signed bound. Ŵ changes sign, so parity blocks it UNLESS a window makes Ŵ ≥ 0 on the low scales u ∈ (1, 1.32). Unexamined.
- Next: A1e (zero-density constants, window-scope); bridge-port on the window-positivity question plus the sieve Δ estimate; am-cert prize tables (m₄ vs λ; depth-control grid).

## A1e (window-scope, ROUTE3_A1e.md): explicit depth control. NOT available for δ ≤ 3
- Explicit Selberg-type (Simonič 2020): fraction ≤ 4πa·e^{−δ/4} with a ≥ 3.259 (method floor). Trivial (> 1) until δ ≈ 14.8.
- Jutila / Conrey have better exponents but non-explicit constants (papers paywalled or unretrieved).
- Conrey's survey: 99% within |β − ½| < 8/log γ (δ = 8, no reference).
- The best explicit bound at δ ≤ 3 is depth-independent: ≤ 0.3265, from on-line proportions (a bootstrap of the same machinery).
- ⇒ The depth-control input that would unlock the third moment's +0.012 does not exist explicitly in the needed regime. Creating it would be a new theorem (explicit near-line zero density at δ ~ 1).

## B1 (bridge-port, ROUTE3_B1.md): the one-sided fourth moment. NOT available
- Ŵ = Re (χ⁴)^ is the transform of the HEIGHT cut, independent of the window ϕ.
  - ϕ enters only via O₄ ≥ 0.
  - Any height weighting gives ∫Ŵ = 2πW(0) = 0, so the kernel is signed; positivity at most for TΔ ≤ π/2 (one-line proof), or ≈ 3 by LP.
  - No admissible choice makes Ŵ ≥ 0 on the low scales.
- Sieve Δ: dropping negative lobes is legal (C(h) ≥ 0), but the off-diagonal mass at scale m > T is ≈ (m/T) × the diagonal, with the net O(1) only by cancellation.
  - Measured: Δ ≥ 0.15 even at a perfect sieve; ≈ 0.4–0.5 at realistic B; divergent as T → ∞. Not < 1/12.
- Also found: MRT's log^{−A} saving is insufficient to evaluate any scale m ≥ T(log T)^C to o(1) (power saving needed). The "88.5% covered" is a measured share, not proof-level coverage. CONTRADICTS A1d's coverage picture; needs an independent re-run.
- Refutation specs R1 (LP / kernel cap) and R2 (amplification exponent) in ROUTE3_B1.md, for Sam to route.

## B2 (bridge-port, dispatched): BUILD the depth input from classical tools
- Littlewood's lemma on the mollified ζ, with Conrey/BCY/PRZZ explicit mollified mean squares c(R0), gives a two-sided deep fraction ≤ log c(R0)/(R − R0).
- Tabulate ε(δ0) at δ0 = 0.5–3 spacings against am-cert's grid.
- Lead's pencil guess: ≈ 0.18 at 1 spacing, ≈ 0.02 at 3 spacings.
