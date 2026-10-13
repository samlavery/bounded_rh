# ROUTE3_A1: source read. Where RH enters the k = 3 (triple-correlation) evaluation beyond the Rudnick–Sarnak range (window-scope, 2026-10-12)

Task (lead, 10-12): read Hej94, RS96, BGSTB24 and GLSS25 at source, and answer:
1. where RH is used in the k = 3 evaluation beyond kλ < 2: only to define the correlation with real γ, or in an RH-strength prime-sum / off-diagonal estimate;
2. whether BGSTB24's unconditional technique extends to k = 3, and with what extra input;
3. whether any newer unconditional triple-correlation result has support beyond the RS range.

## Prediction (written before reading any of the four papers)
- Q1:
  - (b), RH used as an analytic input in the prime-side evaluation: about 60%. The most likely form is the RH error term in the explicit formula or prime number theorem (ψ(x) = x + O(x^{1/2+ε})). It would be used for the off-diagonal triples of prime powers where n1·n2 ≈ n3, which are no longer killed by Montgomery–Vaughan once the support exceeds the RS range.
  - (a), RH only to make the γ's real and the correlation well defined: about 40%.
  - For Hejhal's paper in particular: about 70% that RH is assumed globally in the statement, with the stated reason only partly localised.
- Q2: BGSTB24 extends to k = 3 inside the RS range at no extra cost (about 70%). Beyond it, it needs one extra input, predicted to be an unconditional mean-value or short-interval prime estimate of RH strength for the three-factor off-diagonal (about 60%). So "the framework trick alone" does not remove RH beyond kλ < 2: about 60%. That is close to the lead's 65%.
- Q3: no unconditional triple (or n ≥ 3) correlation result with support beyond the RS range exists in the literature: about 85%.

## Sources obtained (local copies in `~/work/riemann-submission/route3_refs/`)
- **RS96**, read at source. Rudnick–Sarnak, "Zeros of principal L-functions and random matrix theory": the authors' preprint (Exeter copy, `rudnick_sarnak_1996.pdf`).
  - Page numbers below are the PREPRINT's (its running heads). They are not Duke 81's 269–322.
- **BGSTB24**, read at source. arXiv:2306.04799v1 (the only arXiv version).
- **GLSS25**, read at source. arXiv:2503.15449v4 (30 Mar 2026).
- **Hej94: NOT OBTAINED.** The OUP page is paywalled and blocked automated access, and no open copy was found.
  - Everything said about Hejhal below comes from two secondary sources, labelled as such: RS96's description of it (p. 2), and Conrey–Snaith's restatement (arXiv:math/0610495, eq. (1.2), p. 2).
- Zeta23 (`helix_frobenius/refs/zeta23_paper.txt`), §7.5 (e)–(g) (pp. 24–25) and the G̃ setup (§2.2, (2.15), (2.19)–(2.20), Lemma 2.2, pp. 7–9).

## Answer 1. Where RH enters, and the RS range for k = 3

### 1a. RS96 evaluates the n-level sums WITHOUT RH. RH is used only to remove the smoothing.
- p. 4, before Theorem 1.1: "if h and f are defined for complex argument and are localized then the sums (1.4) make sense even if we do not assume RH, and we still refer to these as the n-level correlations."
- Theorem 1.1 (pp. 4–5) carries no RH hypothesis (m = 1 is ζ): "Let f satisfy TF 1,2,3 and in addition assume that f̂(ξ) is supported in Σ_j |ξ_j| < 2/m. Let g ∈ C_c^∞(ℝ) and h(r) = ∫ g(u)e^{iru} du (so that h and f are entire). Then … R_n(T, f, h) ∼ (m/2π) T log T ∫ h(r)^n dr ∫ f(x) W_n(x) δ((x_1+⋯+x_n)/n) dx."
- p. 5: "If we assume RH for L(s, π) we can relax the smoothness condition on h and in fact choose it to be the characteristic function of an interval." That is Theorem 1.2, "With the assumptions of Theorem 1.1 and also RH …".
- p. 7: the smoothed form "allows us to avoid appealing to RH."
- §3, Theorem 3.1 (p. 20): the same unconditional statement for the sums C_n over ALL n-tuples of zeros, not only distinct ones. Φ is supported in Σ|ξ_j| < 2/m. Main term κ(h)(TL/2π) ∫ C_O Φ, error O(T).
- Theorem 3.2 (p. 20): "for this we will assume the Riemann Hypothesis".
- Its proof (pp. 36–37) uses RH only to approximate the sharp cutoff χ_[−1,1] by smooth h₁ ≤ H ≤ h₂ (a sandwich that needs real ordinates): "In what follows we assume the Riemann Hypothesis … Hence Theorem 3.1 is valid with h_j(r) = χ_[−1,1](r)."
- **How the prime side is evaluated unconditionally** (Lemmas 3.2–3.3, pp. 23–24): no estimate is involved.
  - Because g has compact support, A_{r,s}(n, T) = 0 unless n₁⋯n_{r+s} ≪ T^{2−δ}, and unless (3.28) |log(n₁⋯n_r / n_{r+1}⋯n_{r+s})| ≪ T^{−1+δ/3}.
  - For M ≠ N, (3.29) gives |log M/N| ≥ 1/√(MN) ≫ T^{−1+δ/2}, a contradiction.
  - So the off-diagonal terms VANISH identically inside the support region. Integer spacing beats the 1/T localization.
- **What limits the region** (Remark, pp. 35–36): for ζ it is the pole at s = 1.
  - (3.66): the polar term ∼ h(0)^n T^{(|ξ₁|+⋯+|ξ_n|)/2}. "The region Σ|ξ_j| < 2 … is precisely that which renders (3.66) smaller than the main term T log T."
  - Beyond it, (3.68)–(3.70) bring in Hardy–Littlewood-type sums Σ c(m)c(m+h) ("of order X, if we assume the 'twin-prime' type conjectures").
  - So the barrier past the RS region is the polar and Hardy–Littlewood structure, not RH.

### 1b. For the k = 3 trace, the RS region is the whole band λ < 1, not λ < 2/3
- From Zeta23 (2.20), G_kl = Σ_ρ m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l), and Lemma 2.2 (Σ_k φ̂(τ−τ_k)φ̂(τ′−τ_k) = LΦ(τ−τ′), Φ = (φ²)^, supp φ = [−L/2, L/2], L = λl).
- Hence tr G³ = Σ_{ρ_a, ρ_b, ρ_c} m m m K(γ_a, γ_b) K(γ_b, γ_c) K(γ_c, γ_a), a 3-cycle in the zeros with kernel ≈ LΦ(γ − γ′).
- In RS's variables x = (log T/2π)γ, each kernel factor has Fourier support |a| ≤ λ/2.
- For the 3-cycle the dual variables of the three zeros are ξ₁ = a₁ − a₃, ξ₂ = a₂ − a₁, ξ₃ = a₃ − a₂ (Σξ = 0). So
  Σ_j |ξ_j| = 2 (max a − min a) ≤ 2λ, and also max_j |ξ_j| ≤ λ.
- RS's condition Σ|ξ_j| < 2 therefore holds for every λ < 1. It is the same as Hejhal's hexagon (max |ξ_j| ≤ 1, per Conrey–Snaith (1.2): vertices (1,0), (0,1), (−1,1), (−1,0), (0,−1), (1,−1)), since on the plane Σξ = 0 with n = 3, Σ|ξ_j| = 2 max|ξ_j|.
- The product of the prime powers is n_a n_b n_c ≪ T^{Σ|ξ_j|} ≤ T^{2λ}, not T^{3λ}.
- General k: the cyclic sum Σ_i |a_i − a_{i−1}| has maximum kλ for even k (alternating signs) and (k − 1)λ for odd k. So:
  - the exact RS condition for tr G̃^k is kλ < 2 for even k and (k − 1)λ < 2 for odd k;
  - k = 3 gives λ < 1; k = 4 gives λ < 1/2, which agrees with Zeta23 (f), "for k = 4, λ > 1/2 it encodes a Hardy–Littlewood-type asymptotic".
- Zeta23 (e)'s "kλ < 2 … (and only for λ < 2/3)" uses the per-entry count k·λ. That is sufficient but not necessary.
  - Zeta23 (g) itself says that under RH "tr G̃³ (equivalently, the triple correlation of zeros in the band λ < 1) is available as a theorem [Hej94, RS96]". That is consistent with this reading: the band-λ < 1 triple correlation is inside RS's region.
  - The RH in (g) is the sharp-cutoff, real-γ form (RS Thm 3.2 / Hejhal). It is not a prime-side input.
- **Answer to Q1: (a), not (b).**
  - In RS96, RH enters only to pass from smoothed sums over complex zeros (Thm 3.1, unconditional) to sharp counts of real ordinates (Thm 3.2 / 1.2).
  - Inside the support region the off-diagonal prime terms vanish exactly; no estimate, RH-strength or otherwise, is used.
  - Past the region the obstruction is the polar term and Hardy–Littlewood, not RH.
  - Hejhal (secondary only): RS p. 2 says Hejhal computed the 3-level correlation "assuming RH and in a restricted range, similar to the assumption and restriction used by Montgomery". Conrey–Snaith (1.2) states it for real γ ∈ [T, 2T], distinct, with a Gaussian weight. I could not check where in Hejhal's proof RH is used.

### 1c. What this means for route 3 (my reading; checks requested)
- The "new theorem" in ROUTE3.md, tr G̃³ unconditionally for λ ∈ (2/3, 1), is, in substance, RS96 Theorem 3.1 (k = 3, Σ|ξ_j| ≤ 2λ < 2).
  - What remains is an adaptation of the localization. RS smooth each zero by h(γ/T) with compactly supported ĝ at scale 1/T; Zeta23 truncates a Gabor grid sharply to d points.
  - The RS mechanism (Lemma 3.3) needs only a localization whose Fourier transform is compactly supported at scale 1/T. Smooth vertex weights on the grid would provide that.
  - That adaptation is not done here; "not proven in this file".
- So route 3 is not a new arithmetic input at the trace level. Its value rests entirely on A2: whether the third moment improves an UNCONDITIONAL certificate.
  - Zeta23 (e) already notes "an odd moment does not lower Λ₁(0). Thus, unconditionally, higher moments add nothing to the n₊-bound on (1/2, 1)".
  - The gain in (g) is for DISTINCT zeros (Nd) under RH, and its argument uses H = M^{1/2}ΓM^{1/2} ⪰ 0 (G̃ PSD), i.e. RH, beyond the trace.
- Request: an independent check of the support computation in 1b by am-cert or the lead before anyone acts on it. It is three lines: Σ_cyc |a_i − a_{i−1}| = 2 (max − min) for three reals.

## Answer 2. Does BGSTB24's technique extend to k = 3, and with what input?
- BGSTB24's unconditional ingredients, read at source:
  - (i) Lemma 1, Montgomery's explicit-formula identity with complex δ (ρ = 1/2 + δ + iγ), from Landau's formula (2.3);
  - (ii) Lemma 3, positivity by pairing ρ ↔ 1 − ρ̄: "F(x, T) = (2/π) ∫ |Σ_ρ x^{ρ−1/2} / (1 − (ρ − (1/2+it))²)|² dt" (2.6), so F ≥ 0 (Theorem 1: "F(α) is real, even, and nonnegative");
  - (iii) the zero-free region, to control the factors x^{δ+δ′} in truncation errors. Lemma 4: F = L/(2π) + O(x^{1−2η(T log T)} log³T) + O(x), with (2.16) x^{δ+δ′+i(γ−γ′)} ≪ x^{2Θ(Z)−1} ≤ x^{1−2η(T log T)}.
  - Abstract and Remark: the method "neither requires nor provides any information on whether any of these zeros are on or not on the critical line."
- BGSTB24 treats only k = 2. Grep finds no triple, n-level or Rudnick–Sarnak in the paper.
- For k = 3:
  - (ii) has no analogue (a triple product is not a square), so positivity is lost. (i) and (iii) extend formally.
  - It is not needed for the trace evaluation, though: RS96 Thm 3.1 is already the unconditional smoothed k = 3 statement in the band λ < 1 (Answer 1).
  - What a sharp-cutoff, Montgomery-form k = 3 statement would add is the smooth-to-sharp passage. RS do that with RH (Thm 3.2). The Zeta23 framework does not need sharp cutoffs if its grid localization is smoothed.
- So the extra input for k = 3 in the band λ < 1 is NONE at the level of the trace evaluation. Past the RS region (λ > 1 for k = 3, irrelevant here, or k ≥ 4 with λ > 1/2) it would be Hardy–Littlewood-type correlations, which BGSTB24's technique does not supply.

## Answer 3. Newer unconditional triple-correlation results past the RS range?
Searched (2026-10-12): web searches on triple / n-level correlation with extended support, unconditional, 2024–2026, and Hughes–Rudnick / Rodgers on mock-Gaussian support.
- **None found.** Every n ≥ 3 correlation result for ζ I found is either within Σ|ξ_j| < 2 (Hejhal 1994; RS 1996) or conditional:
  - Rodgers' UCLA thesis: a slight enlargement under a uniform Hardy–Littlewood hypothesis (per the search summary, not read at source);
  - Conrey–Snaith, math/0610495: lower-order terms from the ratios conjecture, with RH;
  - Bogomolny–Keating: heuristic, Hardy–Littlewood.
- Families, not single-L-function correlations: Drappeau–Pratt–Radziwiłł extend the 1-level density for Dirichlet L-functions unconditionally past the trivial range (per the search summary). That is a different statistic.
- arXiv:2507.20653 ("On Hypothesis H of Rudnick and Sarnak") is relevant only to degree ≥ 4. Its summary says defining the m-level sums "requires GRH". That contradicts RS96 p. 4 (quoted above) for the smoothed sums.
- **Nearby result found in the search, relevant to A2's benchmark, NOT read at source** (alphaXiv summary only): Knausgård, arXiv:2610.08965 (6 Oct 2026; Lean repository github.com/kristianmk/839).
  - Claims, unconditionally, "more than 83.9% of the zeros … are distinct and more than 67.35% are simple and on the critical line".
  - Per the summary, it uses ONLY the unconditional pair-correlation (second-moment) energy, with computer-assisted local inequalities (θ = 17/20, frames of 7–8 consecutive points).
  - If correct, an unconditional distinct-zero proportion of ≈ 0.839 already exists from pair correlation alone, close to Zeta23 (g)'s RH-conditional 0.84262 "from the correlation input alone". A2's prize should be measured against it.

## Prediction check
- Q1 (b) at ≈ 60%: REFUTED. RH enters only as (a), sharp-cutoff / real-γ, in RS96. The question's premise (λ < 2/3 for k = 3) is an artifact of the per-entry count: the RS region for the 3-cycle trace is λ < 1.
- Q2, "BGSTB extends inside the RS range at no extra cost": SUPPORTED in substance, and stronger. RS96 Thm 3.1 already supplies the unconditional smoothed k = 3 statement. "Beyond it, an RH-strength input": REFUTED as to its nature (it would be Hardy–Littlewood, not RH), and moot for band ≤ 1.
- Q3, none past the RS range at ≈ 85%: SUPPORTED, with the coverage limits stated.
- The lead's ≈ 65% (RH in off-diagonal Λ-correlation bounds): not supported by RS96 at source. Hejhal is unchecked.
