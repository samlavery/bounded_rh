# ROUTE3_A1d: do Matomäki–Radziwiłł–Tao (and sequels) cover the averaged Λ∗Λ shifted convolutions that m₄ needs at λ ≥ 0.66? (window-scope, 2026-10-12)

Task (lead, 10-12):
1. the exact statement needed (Zeta23 §7.5(f)): mean square or weighted average, precision, uniformity;
2. what MRT I/II and sequels prove: which functions, what averaged form, which H, what error; is Λ∗Λ covered;
3. the threshold in λ;
4. whether the h-average carries the right weights for the fourth trace.

## Prediction (written before reading MRT or any sequel)
- Q2:
  - about 55%: MRT I proves L¹-averaged asymptotics for Λ·Λ, d_k·d_l and Λ·d_k in shift ranges H ≥ X^{8/33+ε}, but no theorem covers Λ∗Λ (or its log-weighted bilinear variants) directly. Since Λ∗Λ = Λ₂ − Λ·log, with Λ₂ = μ∗log² obeying the same Heath-Brown-identity Type I/II structure as Λ, the extension would be "standard but not written";
  - about 20%: some stated theorem covers it directly, e.g. a general Type I/II "f, g" formulation in MRT I or a later paper;
  - about 25%: not available, because the needed uniformity (factor weights, two-factor support) breaks the method.
- Q3: if covered, the threshold is the same H ≥ X^{8/33+ε} for the prime-like factor, so λ ≥ 33/50 (about 70%). Divisor-type parts (d₂-like) would allow much shorter H (MRT II), but the prime-like part sets the bound.
- Q1/Q4: the fourth trace needs a WEIGHTED average over h of shifted bilinear sums Σ_{ab=M} Λ(a)Λ(b) w(log a, log b), not a pure mean square. An L¹-averaged asymptotic with o(main) error is enough for bounded weights. The factor weights w add a smooth twist that Mellin decomposition can absorb (about 60%).

## Sources read at source (local copies in `route3_refs/`)
- **MRT I:** K. Matomäki, M. Radziwiłł, T. Tao, "Correlations of the von Mangoldt and higher divisor functions I. Long shift ranges", Proc. LMS 118 (2019) 284–350; arXiv:1707.01315v3.
  - Read: §1 (Theorem 1.3, prior results, overview), §3 (Corollary 3.2, Propositions 3.3–3.4). Not read: §§4–8 in detail.
- **Evans:** N. Evans, "Correlations of almost primes", Math. Proc. Cambridge Philos. Soc.; arXiv:2102.12297v3.
  - Read: §1 (Theorems 1.1, 1.3, 1.4, outline), §9 (Theorem 1.3).
- **Summary level only (web), not read at source:**
  - MRT II (arXiv:1712.08840);
  - Matomäki–Radziwiłł–Shao–Tao–Teräväinen, "Higher uniformity … II. Almost all intervals" (arXiv:2411.05770, Invent. Math.);
  - Farmer–Gonek–Lee–Lester on zero correlations and almost-prime statistics (cited in arXiv:2609.33953; a pointer for later).
- Search for any improvement of σ = 8/33 for averaged Λ·Λ correlations (2023–2026): none found. A Nov 2025 paper (arXiv:2511.10594) still calls 8/33 "the best result so far".

## Answer 1. The exact statement the fourth trace needs
- **Zeta23 says only** (§7.5(f), p. 25): "for k = 4, λ > 1/2 it encodes a Hardy–Littlewood-type asymptotic for the additive correlations Σ_m (Λ∗Λ)(m)(Λ∗Λ)(m + h), |h| ≤ X²/T". It gives no mean-square or weighting detail.
- **The weighted form** is in Yang–Yang Prop. 3.5 (p. 12; see ROUTE3_A1c). The class is R: "pairs of restricted products N₁ = b₁m₁ ≠ N₂ = b₂m₂ (all legs prime powers ≤ X), weight Λ⁴/√(N₁N₂), window kernel Ŵ(Δ) = [sin 2TΔ − sin TΔ]/Δ at Δ = log N₁/N₂", with the 4-cycle overlap geometry O₄ depending on the individual legs.
- **So the object is a WEIGHTED average over shifts, not a mean square:**
  Σ over dyadic scales m ∈ (T, X²] of Σ_{0<|h|≲m/T} Ŵ(h/m) Σ_{M∼m} F(M) F′(M+h)/√(M(M+h)),
  where F(M) = Σ_{ab=M, a,b≤X} Λ(a)Λ(b) w(log a, log b) is a restricted, leg-weighted Λ∗Λ.
- **Precision:** the consumption (Zeta23 HL*(k₀, λ): tr G̃⁴ = dℓ₁⁴(m₄(λ) + o(1))) needs this evaluated to o(1) in normalised moment units, uniformly over the scales.
- **Averaging form:** an L¹ "almost all h" asymptotic with a sieve upper bound on the exceptional h is enough for a bounded kernel. A variance form is not needed (but is what MRT's proof produces anyway, Corollary 3.2).
- **Key structural point:** the shift range at scale m is |h| ≲ m/T, so H(m) = m/T = m^{1−1/u} for m = T^u, u ∈ (1, 2λ]. The global "|h| ≤ X²/T" is only the top scale.

## Answer 2. What MRT and the sequels prove
- **MRT I, Theorem 1.3** (p. 8). For X^{σ+ε} ≤ H ≤ X^{1−ε}, σ = 8/33, 0 ≤ h₀ ≤ X^{1−ε}:
  - (i) "Σ_{X<n≤2X} Λ(n)Λ(n + h) = S(h)X + O_{A,ε}(X log^{−A} X) for all but O_{A,ε}(H log^{−A} X) values of h with |h − h₀| ≤ H";
  - (ii) the same for d_k(n)d_l(n + h);
  - (iii) the same for Λ(n)d_k(n + h);
  - (iv) averaged Goldbach.
  - No other functions are stated.
- **The framework** (Corollary 3.2, p. 34): f, g with size bounds, a major-arc estimate, and a minor-arc estimate (59) "for one of the two functions f, g". The proof passes through the variance bound Σ_{|h−h₀|≤H} |Σ_n f(n)g(n+h) − MT_{M,h}|² ≪ η³F²G²HX².
  - The minor-arc input, Proposition 3.4 (pp. 35–36), is stated ONLY for "f(n) := Λ(n)1_(X,2X] or f(n) := d_k(n)1_(X,2X]". Its proof (§§5–8) runs through the Heath-Brown identity into "Type II" and "Type d₁–d₄" pieces (p. 12).
- **Is Λ∗Λ covered? Not as stated.**
  - Λ∗Λ = Λ₂ − Λ·log, and Λ₂ = μ ∗ log² has the same Heath-Brown decomposition as Λ = μ ∗ log, with log² in place of log. So Proposition 3.4 for Λ₂, and hence Theorem 1.3-type statements for (Λ∗Λ)·(Λ∗Λ), look like a standard extension. They are not written in MRT I.
  - The object actually needed (Answer 1) is the RESTRICTED, leg-weighted F(M). Its minor-arc estimate needs the weights w(log a, log b) and the cut a, b ≤ X separated, e.g. by Mellin twists a^{it}, b^{iu}, and carried through §§5–8. That is not written either.
- **MRT II** (summary level): d_k·d_l in very short ranges with weaker error. Not Λ·Λ, and not prime-like functions.
- **MRSTT higher uniformity II** (summary level): ℓ-point Hardy–Littlewood with one averaging variable for H ≥ X^{1/3+ε}. That is weaker than 8/33 for two points.
- **Evans** (read at source). The bilinear (semiprime) structure gives much shorter ranges, but only for UNWEIGHTED semiprimes.
  - Theorem 1.3 (p. 2): for exp((log X)^{1−ε}) ≤ H ≤ X log^{−A} X, "Σ 1_{E₂}(n)1_{E₂}(n+h) ∼ S(h)(Σ 1_{E₂}(n))²/X … for all but at most O(H log^{−B} X) values of 0 < |h| ≤ H".
  - Theorem 1.1: H ≥ log^{19+ε} X when one factor p₁ ∈ (P, P^{1+δ}] with small P.
  - The proof of Theorem 1.3 (§9, p. 31) reduces to "E₂ numbers which factorise in the 'typical' way: … almost all products of exactly two primes p₁p₂ ≤ X with p₁ ≤ p₂ satisfy p₁ ∈ [exp((log X)^{ε(X)}), exp((log X)^{1−ε(X)})]", i.e. to a SMALL factor p₁ = X^{o(1)}. The argument uses "a short Dirichlet polynomial corresponding to the smaller prime factor p₁" (p. 5).
  - **This does not transfer to Λ∗Λ.** The weights log a · log b spread the mass uniformly in log a / log M, so balanced factorizations (both factors about √M) carry most of it. In the fourth trace both legs are ≤ X, and at the top scale both are about X ≈ √M. Evans's typical-factorization reduction discards exactly these as a negligible unweighted fraction.
  - For balanced factors the bilinear advantage disappears once H < √M: for fixed a ≈ √M, the cofactor b ranges over an interval of length H/a < 1. One is back to a Λ₂-type Heath-Brown analysis, i.e. MRT's σ = 8/33 at best.

## Answer 3. The threshold
- **With MRT-type input at σ = 8/33** (assuming the Λ∗Λ extension above), scale m = T^u is covered iff H(m) = m/T ≥ m^{8/33+ε}, i.e. u ≥ 33/25 = 1.32.
- **Coverage starts at λ > 33/50 = 0.66** (some scales u ∈ (1.32, 2λ] exist). This agrees with the earlier figure.
- **Full coverage never happens at any λ ∈ (1/2, 1].** The scales m ∈ (T, T^{33/25}) are uncovered at every λ, since there H(m) < m^{8/33}. For m = cT the shifts are |h| ≲ c, which is pointwise-Hardy–Littlewood territory.
- **Size of the gap:** this matches Yang–Yang's own measurement at λ = 1, "The covered share of the class at the 8/33 exponent is 0.885 (anchored at the archived 0.797 at exponent 1/3)" (Yang–Yang p. 15). That is about 11.5% of R uncovered (a measured share, not proved).
- Lowering σ shrinks the gap. Closing it needs averaged correlations of balanced Λ∗Λ for every power range H = m^{δ}, δ → 0, which no known result gives.

## Answer 4. The weights
- **The shift weight** Ŵ(h/m) is bounded and oscillatory. An "almost all h" asymptotic (or the variance form) plus a sieve upper bound for the exceptional h handles any bounded weight, so no extra twist is needed in h.
- **The leg weights** (O₄ geometry, the cut a, b ≤ X, the 1/√(MN) factor) are extra twists on F. They need the weighted bilinear minor-arc estimate (Answer 2), which is not written.
- **One-sided use is blocked by parity.** Ŵ changes sign inside the main region (sin 2x − sin x < 0 for x ∈ (π/3, π), x = TΔ). An UPPER bound on R over the uncovered scales would need LOWER bounds for prime or semiprime correlations at the negative-weight shifts. Sieves cannot give those.
- Yang–Yang price this part at finite height (0.0163, their §4), not by proof.

## Conclusion
- **Two-sided:** an unconditional m₄ → 13/4 is NOT available from MRT I or the sequels I read, at any λ ∈ (1/2, 1].
  - (i) Λ∗Λ (restricted and leg-weighted) is not covered as stated; the extension looks standard but is unwritten.
  - (ii) Even granted (i), σ = 8/33 leaves the scales m ∈ (T, T^{33/25}) uncovered at every λ, about 11.5% of R at λ = 1 by Yang–Yang's measurement.
  - (iii) Evans's subpolynomial ranges apply to unweighted semiprimes dominated by small-factor factorizations, not to the balanced Λ∗Λ mass.
- **One-sided** (an upper bound m₄ ≤ 13/4 + Δ with Δ < 1/12, which would already exclude the two-moment extremal at 10/3): the covered 88.5% can in principle be evaluated. The uncovered part needs a signed bound, which the sign changes of Ŵ make a parity-type problem.
  - Whether a different window (a kernel with Ŵ ≥ 0 on the uncovered scales) avoids the sign issue is a concrete question I have not examined.

## Prediction check
- Mine:
  - "not directly covered; a standard extension via Λ₂" (about 55%): SUPPORTED;
  - threshold 33/50 (about 70%): SUPPORTED for the START of coverage, but the bigger finding, the permanent low-scale gap, was not predicted;
  - weights (a weighted average, L¹ enough, smooth leg twists, about 60%): SUPPORTED, plus the parity obstruction for one-sided use, also not predicted.
- Lead's 55 / 25 / 20 (genuine extension / direct / not available): consistent with "a genuine extension for coverage". Even then the remaining low-scale gap makes the two-sided m₄ "not available with current results".

## RECHECK against bridge-port's B1 §4 (2026-10-12): pre-registration
B1 §4's claim (as relayed by the lead): at scale m > T the R kernel mass is about (m/T) × the diagonal, and the net is O(1) only by cancellation. Evaluating a scale to o(1) therefore needs relative error ≲ T/m, a POWER saving. MRT's O(X log^{−A}) then covers no scale m ≥ T(log T)^C, and "88.5% covered" is a measured share, not proof-level coverage.

Predictions (written after reading only the lead's summary, before reading B1 §4 or re-reading the sources):
- MRT I Theorem 1.3 gives only a log^{−A} saving for Λ·Λ. Power savings are mentioned for divisor-function correlations only (about 95%).
- B1 §4's amplification argument is right and A1d's coverage statement is wrong (about 80%). In A1d I bounded the error of the h-sum by o(H·X·max|Ŵ|) and called that o(main). But the target is the NET of the h-sum (O(1) in m₄ units after cancellation), while H·X·max|Ŵ| is about (m/T) × O(1).
- The k = 2 control is decisive: MRT-type coverage evaluating Montgomery's F(α) for α > 1 would contradict the open status of that range (about 85%).
- In Yang–Yang §4, "covered" will turn out to mean "the MRT variance hypothesis applies on that zone", not "evaluated to o(1) in R-units". Their Theorem 4.1 sweeps the covered-zone error into "o(1)" without the amplification factor (about 65%).
