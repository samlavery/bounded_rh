# ROUTE3_A1c: Yang–Yang's unconditional fourth moment ("Lemma D") at source (window-scope, 2026-10-12)

Task (lead, 10-12): find Lemma D and its proof, and answer:
1. what exactly it claims (the quantity, the band λ, the error term);
2. where the off-diagonal (Λ∗Λ)(m)(Λ∗Λ)(m + h)-type terms go: evaluated, bounded or dropped;
3. whether it is valid unconditionally at λ ∈ (1/2, 1), with the line of any gap, or else the input that replaces Hardy–Littlewood.

The rule: if a step is unclear, say so; do not reconstruct it.

## Prediction (written before reading Lemma D or §7)
- About 85%: there is a gap at λ > 1/2.
  - Most likely place: the shifted-correlation class R (pairs N₁ ≠ N₂ of products of prime powers with |log N₁/N₂| ≲ 1/T). Its unconditional asymptotic is a variance-of-primes-in-short-intervals / averaged Hardy–Littlewood statement (the Goldston–Montgomery equivalence for pair correlation beyond α > 1). That is not known unconditionally.
  - Expected form: either the major arcs (q ≤ (log X)^B, Siegel–Walfisz) are evaluated and the remaining arcs are declared negligible with a bound that is not o(main term) when λ > 1/2; or R is set to its model value (−301/60) by an identity that encodes the singular-series average.
- About 10%: the step holds as written (that would be a major unconditional theorem).
- About 5%: the write-up is too incomplete to locate a definite gap. In that case I will say "unclear".

## Source
- H. Yang and S. Yang, "More than 0.7962 of the zeros of the Riemann zeta function are simple and on the critical line", preprint v1.0, August 2026.
  - Zenodo DOI 10.5281/zenodo.21975236 (record 21975237, English PDF). Local copy: `route3_refs/yang_yang_zenodo21975237_EN.pdf`.
  - **No arXiv id**: none appears in the document, and a web search finds only the Zenodo record.
  - Reproduction repository named in the paper: github.com/JoshuaHKU/zeta-0.7947-reproduction (not inspected).
- The paper's own grading (p. 1, footnote): "certified-candidate, not record … the analytic layer is unformalized, and no external review has taken place."
- §11(b), p. 28, places in that ungraded-by-proof layer "the truncation discharge; the spectral proof of Lemma D (Theorem 7.5) — whose minor/mixed-bin size bookkeeping is classical in kind but carried at write-out grade with face-checked budgets — … the covered-zone/band/glue chain of §4".
- §11, p. 28, also lists "archived certified lemmas (bridge, glue, aggregation, D1 truncation, consumer interface, anchor certificates: §4)". These are NOT in the paper.
- Page numbers below are the PDF's.

## Answer 1. What Lemma D claims
- Theorem 7.5 ("Lemma D, truncated form"), p. 19:
  > Let B be fixed, b₁, b₂ ≤ (log X)^B prime powers, windows of length Y ≍ X^ϑ, ϑ ∈ (1/2, 1]. Then for every A > 0, Σ_{k≤K} Σ_{|j|≤J} |N₄(k, j) − S₄(k, j)V(k, j)|² ≪_{A,B} KJV²(log X)^{−A}. Consequently, with Proposition 5.3, m₄ → 13/4 two-sidedly.
- Definitions (§2.3, p. 10):
  - N₄(k, j) is "the Λ⁴-weighted count of locked quadruples (m, m − rk, n, n − qk) with b₁n − b₂m = j";
  - S₄V is its singular-series model times the window-overlap volume;
  - the shift and lock ranges are full-length: "shifts k ≤ K ≍ Y/max(r, q) and locks |j| ≤ J ≍ X", with r = b₁/g, q = b₂/g, g = (b₁, b₂).
- So the quantity is a mean square, over full-length shift and lock ranges, of the error in a four-prime correlation count, for SMALL moduli b₁, b₂ ≤ (log X)^B. The saving is an arbitrary log power, with ineffective constants (Siegel–Walfisz, Remark 7.2).
- Band: the consumed statement is m₄ → 13/4 "in the endpoint regime" λ → 1⁻ (§2.3, (2.5), p. 9).
- The authors say (§7, p. 18): "In its unrestricted form — moduli up to a power of X — it remains open … Two observations remove the difficulty from the consumed form: the truncation discharge of §5, and the spectral frame below."

## Answer 2. Where the off-diagonal (Λ∗Λ)(m)(Λ∗Λ)(m+h)-type terms go
- They are the class R. Proposition 3.5 (p. 12): µ₄ = 1 + 2 + 17/60 + R + o(1) = 197/60 + R + o(1), where "R is the shifted-correlation class: pairs of restricted products N₁ = b₁m₁ ≠ N₂ = b₂m₂ (all legs prime powers ≤ X), weight Λ⁴/√(N₁N₂), window kernel Ŵ(Δ) = [sin 2TΔ − sin TΔ]/Δ at Δ = log N₁/N₂ …". The model value is R = −1/30 (= 13/4 − 197/60).
- Zeta23 §7.5(f) places exactly this in the band: "for k = 4, λ > 1/2 it encodes a Hardy–Littlewood-type asymptotic for the additive correlations Σ_m (Λ∗Λ)(m)(Λ∗Λ)(m + h), |h| ≤ X²/T".
- They are treated two ways:
  - **One-sided route** (§4, Theorem 4.1, p. 13: R̄ = 0.0066, giving 0.6916). R is BOUNDED, not evaluated.
    - Partly by Matomäki–Radziwiłł–Tao (Prop. 4.3, p. 15, MRT Theorem 1.3(i), variance form for Λ(n)Λ(n+h), X^{8/33+ε} ≤ H ≤ X^{1−ε}): "The covered share of the class at the 8/33 exponent is 0.885".
    - The rest by a "middle band" and "low zone", whose "certified finite-height price at the operating point is 0.0163" (p. 16), i.e. by measurement at finite T.
    - The core constant is computed, not proved (Lemma 4.10, "grade: proof shape with computed constants").
  - **Two-sided route** (§§5–7). R is claimed EVALUATED through Lemma D. This needs:
    - (i) the truncation discharge (Proposition 5.3, p. 17) to throw away every cell whose "cell parameter" ℓ₁ exceeds P = (log X)^B;
    - (ii) a consumer interface from R to the (k, j)-aggregated variance of Theorem 7.5. Theorem 7.5's proof: "The (k, j)-aggregation constants of the bridge and glue layer are archived and certified (§4.2); the normalization match to KJV² is the consumer interface there" (p. 20).
    - Inside Theorem 7.5, the major arcs are evaluated by Siegel–Walfisz (Lemma 7.1). The minor and mixed arcs are bounded by Vaughan's estimate (Lemma 7.3), with "size bookkeeping … classical and … face-checked at 24–31× tightness".

## Answer 3. Is the step valid unconditionally at λ ∈ (1/2, 1)?
**Not established by the paper.** I can name the lines where the argument cannot be checked from the text, but I do not reconstruct the archived steps. Four points:

- **(a) The truncation discharge rests on a per-cell weight the paper never defines.**
  - Proposition 5.3 (p. 17): "F − F^{(P)} ≪_ε Y²(log Y)^c P^{−(k−2)+ε} two-sidedly … only moduli ≤ (log X)^B are ever consumed." Its proof is one line: "Weight × mass × multiplicity = ℓ^{−k} · ℓ · ℓ^ε summed over ℓ > P."
  - The per-cell factor ℓ₁^{−k} is the only source of decay.
  - The only definition of ℓ₁ in the paper is the GLOBAL normalisation "µ_k = tr G̃^k/(dℓ₁^k)" (§2.1, p. 8), from Zeta23 (ℓ₁ ≍ log T, one number). The summary on p. 6 says the cells are "weighted 1/(dℓ₁^k)" in the same symbol.
  - The paper uses ℓ₁ as a per-cell parameter in Lemmas 5.1–5.2 and in V ≍ Y²/(rq ℓ₁) (p. 10), but does not define that parameter or derive a per-cell factor ℓ₁^{−k} from the prime-side expansion.
  - Lemma 5.1's proof ends with a measurement: "The numerical ledger face measures the aggregate mass essentially flat in ℓ₁ (fitted exponent −0.11)".
- **(b) Proposition 5.3 and Theorem 7.5 do not join up.** Proposition 5.3 truncates the cell parameter ("ℓ₁ ≤ P"). Theorem 7.5 assumes the moduli are small ("b₁, b₂ ≤ (log X)^B"). The paper does not show that ℓ₁ ≤ P implies b₁, b₂ ≤ (log X)^B.
  - In R, both legs of N = b·m range up to X ("all legs prime powers ≤ X", p. 12).
  - Lemma 4.10 (p. 16), on the same class: "the ensemble collapses onto the universal (1, 1)-class (Mertens mass concentrates on pairs of large primes)", with weights Λ(b₁)Λ(b₂)/(b₁b₂).
  - So the paper's own description puts the mass of R on large legs. Discarding large moduli is exactly what needs proof, and Proposition 5.3 is the only place it is asserted.
- **(c) The full-range variance of Theorem 7.5 does not, as written, control a short-range quantity.**
  - Theorem 7.5 bounds a mean square over full-length ranges (k ≤ K ≍ Y/max(r, q), |j| ≤ J ≍ X). That is Lavrik-type "twin primes on average over all shifts", accessible by the circle method with Siegel–Walfisz and Vaughan.
  - The Zeta23 description of the k = 4 content involves shifts |h| ≤ X²/T, short against the length X² (for λ = 1 that is about √(length)).
  - A full-range bound Σ_{k≤K}|dev|² ≪ KY²(log)^{−A} gives, for a sub-range of length H ≪ K, only (K/H)(log)^{−A} relative to that sub-range's natural size. That is useless when K/H is a power.
  - Whether R really reduces to full-range averages is the "bridge and glue … consumer interface" step. It is archived and not in the paper, so it cannot be checked here.
- **(d) The minor- and mixed-arc bookkeeping is not written out** (Lemma 7.3, p. 19): "The size bookkeeping … is classical and is face-checked at 24–31× tightness (face arcs)." §11(b) repeats that it is "carried at write-out grade with face-checked budgets".
- **Consistency flag** (a reason to locate the error, not a proof of one): §12(b)–(c), pp. 29–30.
  - The authors say the machinery is k-uniform: "the labour is bookkeeping rather than new technology", "the moment route cannot stop at any fixed proportion … 0.9 near k ≈ 20–40".
  - Zeta23 §7.5(f) says that the moments for all k and all λ < 1 "would give proportion 1 (of simple zeros on the line)".
  - So the method, as claimed, would prove from Siegel–Walfisz and Vaughan alone that asymptotically 100% of the zeros are simple and on the line. RS96 (Remark, pp. 35–36) places the k ≥ 4 content past its region in Hardy–Littlewood territory, and Yang–Yang cite neither Rudnick–Sarnak nor Hejhal.
- **What could replace Hardy–Littlewood at λ near 1** (my reading, not the paper's claim):
  - The needed object is an AVERAGED shifted-convolution asymptotic for Λ∗Λ over |h| ≤ X²/T. A bounded kernel weight is handled by Cauchy–Schwarz against a variance bound.
  - For Λ·Λ the unconditional input is MRT (2019): variance form, H ≥ X^{8/33+ε}. The paper itself uses it in §4, covering 88.5%.
  - For the products here (length about X², shift range X²/T), MRT's threshold H ≥ (length)^{8/33+ε} means λ ≥ 33/50 = 0.66.
  - I did NOT check whether MRT (or its sequels) covers Λ∗Λ with the uniformity needed. If it does, a two-sided m₄ at λ ∈ (0.66, 1] is plausible from MRT-type input. If not, it is open.
  - For λ ∈ (1/2, 0.66) the shift ranges are shorter than any averaged result I know covers.
- **Verdict on the paper:** Theorem 7.5 itself (a full-range, small-moduli variance) is the kind of statement Siegel–Walfisz and Vaughan can deliver. But the paper does NOT establish that m₄ → 13/4 follows from it: steps (a)–(c) are undefined in the text or archived, and (d) is checked numerically. Its 13/18 and 0.7962 rungs are unproven as written. The one-sided 0.6916 (§4) also rests on finite-height numerics for the uncovered 11.5%, as the authors' grade says.

## Prediction check
- Predicted about 85% "a gap at λ > 1/2, most likely in R / short-interval variance": SUPPORTED in substance, not in form.
  - The step from R to Lemma D cannot be verified (points a–c).
  - Short versus full range (point c) is the structural issue, as predicted.
  - But I could not point to a single false line. The decisive steps are archived or undefined.
- Lead's about 80% "silently uses a Hardy–Littlewood-type input or drops a non-small off-diagonal": consistent with (a)–(c). If anything is dropped, it is by the truncation discharge (a, b), whose basis is not in the text.
- Surprise against my prior (logged): for λ ≥ 0.66 the barrier is averaged correlations of Λ∗Λ in shift ranges that MRT-type theorems reach for Λ·Λ. That is not full Hardy–Littlewood, so "Hardy–Littlewood needed" is too strong at λ near 1. This is unchecked for Λ∗Λ.
