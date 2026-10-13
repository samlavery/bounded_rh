# ROUTE3_A1e: explicit unconditional bounds on zeros at depth |β − ½| ≥ δ/log T (window-scope, 2026-10-12)

Task (lead, 10-12): find, at source, the best EXPLICIT unconditional estimates for the fraction of zeros in [T, 2T] with |β − ½| ≥ δ/log T, δ ∈ [0.5, 3]. For each: the exact statement, whether the constant is explicit, and the resulting fraction bound at δ = 0.5, 1, 2, 3. am-cert is computing what fraction would matter.

## Prediction (written before searching or reading)
- Selberg-type density theorems N(σ, T) ≪ T^{1−(σ−½)/4} log T give fraction ≲ C e^{−δ/4} at σ = ½ + δ/log T.
  - Explicit versions (e.g. Simonič 2020, "near the critical line") have C large enough that the bound is TRIVIAL (> 1) for every δ ≤ 3 (about 80%).
  - The exponent 1/4 makes e^{−δ/4} ≥ 0.47 at δ = 3 even with C = 1.
- Levinson / Conrey-type mollified counts give the useful numbers. They lower-bound the zeros within R/log T of the line or on it; equivalently, they upper-bound the deep fraction by 1 − κ(R) with explicit κ(R).
  - Prediction: these are the best explicit bounds in this δ range (about 70%), with a deep fraction ≤ 0.3–0.5 at δ ≈ 1–3 (about 50%).
- No 2020s explicit density paper beats the Levinson-type numbers at δ ≤ 3 (about 75%).

## Normalisation
- The depth is |β − ½| ≥ δ/log T. The mean spacing at height T is 2π/log T, so "δ spacings" in the lead's message corresponds to δ_here = 2πδ_spacings. Table columns use δ_here = 0.5, 1, 2, 3.
- Fraction = (number of zeros in [T, 2T] with |β − ½| ≥ δ/log T) / (N(2T) − N(T)), with N(2T) − N(T) ∼ (T/2π) log T.
- By the symmetry ρ ↦ 1 − ρ̄ the two-sided count is twice the one-sided N(½ + δ/log T; T, 2T).

## Sources and what they give
**1. Simonič (2020), explicit Selberg.** Read at source: A. Simonič, "Explicit zero density estimate for the Riemann zeta-function near the critical line", J. Math. Anal. Appl. 491 (2020) 124303; arXiv:1910.08274v2 (`route3_refs/simonic_1910.08274.pdf`).
- Theorem 1 (p. 2): "Let T ≥ H₀ and σ ∈ [1/2, 0.831]. Then we have N(σ, 2T) − N(σ, T) ≤ aT^{1−¼(σ−½)} log T + b log² T + c log T log log T + d log T, with a = 10395.2, b = 1.104, c = 0.173 and d = 0.51." Here H₀ = 3.0610046 · 10¹⁰.
- Also p. 2: "for T ≥ 10⁵⁰ and σ ∈ [1/2, 0.569] we have N(σ, 2T) − N(σ, T) ≤ 5.357 · T^{1−¼(σ−½)} log T + 1.11 · log² T. … But with the method presented here we cannot get a smaller constant than 3.259."
- Explicit: YES.
- At σ = ½ + δ/log T, T^{−¼(σ−½)} = e^{−δ/4}, so the two-sided fraction is ≤ 4πa e^{−δ/4} (leading term).

**2. Context for Selberg-type bounds, quoted at source in Simonič (pp. 1–2).**
- Selberg: "N(σ, T) ≪ T^{1−¼(σ−½)} log T … which supersedes (2) [Ingham] for σ − 1/2 ≪ log log T / log T".
- "Jutila improved in [Jut83] the constant 1/4 to 1 − ε and Conrey announced in [Con89] a further improvement to 8/7 − ε, where the implied constant in (3) depends on ε > 0."
- The only other explicit Selberg-type result: "Karatsuba and Korolëv … N(σ, T + H) − N(σ, T − H) ≤ 13HT^{ε(1−2σ)/10} log T … Unfortunately, T₀(ε) is not explicitly known."
- NOT read at source: Jutila 1983 (Birkhäuser chapter, paywalled) and Conrey's 1989 BAMS announcement (the AMS and Project Euclid PDFs were not retrievable).
- Conrey's 1989 Crelle paper WAS retrieved (scan, `route3_refs/conrey1989_crelle.pdf`). Its stated theorem is the on-line proportion only (Theorem 1: "κ ≥ 0.4077 and κ* ≥ 0.401"); the density results were in the announcement.
- So exponents 1 − ε and 8/7 − ε are known, with NON-explicit constants.

**3. Conrey's survey.** Read at source: B. Conrey, "Riemann's Hypothesis" (aimath.org/~kaur/publications/90.pdf), §4.2, p. 9: "at least 99% of the zeros ρ = β + iγ satisfy |β − 1/2| < 8/log γ, and almost all are within φ(γ)/log γ of the critical line where φ is any function which goes to infinity."
- This is a depth statement at δ = 8 (deep fraction ≤ 0.01). No proof or reference is given in the survey sentence, and nothing for δ ≤ 3.

**4. Bounds that hold for every depth δ > 0, from on-line proportions** (the deep fraction ≤ 1 − N₀/N ≤ 1 − N₀ˢ/N):
- Knausgård, arXiv:2610.08965, Theorem 1.3 (p. 3), read at source (ROUTE3_A1b): N₀ˢ/N ≥ 0.67353820, so the deep fraction is ≤ **0.32646**. Lean-formalised, with one search axiom; not refereed.
- Alpöge–Furman / Zeta23 (arXiv:2608.13637) and Lamzouri (arXiv:2609.02882): 2/3 and 0.67250, so ≤ 1/3 and ≤ 0.3275 (as quoted at source in Knausgård p. 2: "[2, 25] proved 0.67250 …").
- Levinson's method, refereed: Pratt–Robles–Zaharescu–Zeindler (Res. Math. Sci. 2020), "slightly more than 5/12" on the line (Knausgård p. 2), so ≤ about 0.583.

## The table: upper bounds for the fraction of zeros in [T, 2T] with |β − ½| ≥ δ/log T

| source | explicit? | δ = 0.5 | δ = 1 | δ = 2 | δ = 3 |
|---|---|---|---|---|---|
| Simonič Thm 1 (a = 10395.2, T ≥ H₀) | yes | 115,280 | 101,735 | 79,231 | 61,705 |
| Simonič (5) (a = 5.357, T ≥ 10⁵⁰) | yes | 59.4 | 52.4 | 40.8 | 31.8 |
| Simonič's method floor (a = 3.259) | (limit) | 36.1 | 31.9 | 24.8 | 19.3 |
| Jutila, exponent 1 − ε | no (C(ε)) | C·0.607 | C·0.368 | C·0.135 | C·0.050 |
| Conrey (announced), 8/7 − ε | no (C(ε)) | C·0.565 | C·0.319 | C·0.102 | C·0.032 |
| on-line proportion, Knausgård 0.67354 | yes | 0.3265 | 0.3265 | 0.3265 | 0.3265 |
| on-line proportion, 2/3 (Alpöge–Furman) | yes | 0.3333 | 0.3333 | 0.3333 | 0.3333 |
| on-line proportion, PRZZ (refereed) | yes | ≈ 0.583 | ≈ 0.583 | ≈ 0.583 | ≈ 0.583 |

- The Selberg-type rows are trivial (above 1) throughout δ ≤ 3. Even the method's floor constant needs δ ≥ 4 log(4π·3.259) ≈ 14.8 before the two-sided bound drops below 1. One-sided bounds are half of the table values.
- **Best explicit unconditional bound for δ ∈ [0.5, 3]: 0.3265, depth-independent**, from Knausgård's on-line proportion. Equivalently, about 1/3 from Alpöge–Furman / Zeta23.
- **Caveat on circularity:** Knausgård's bound comes from the same two-moment machinery. Using it as a depth input to improve the same count is a bootstrap; it is admissible only as an already-proved theorem. Its refereeing status is open.
- No source read gives a DEPTH-DEPENDENT explicit bound below about 1/3 for δ ≤ 3. The first explicit depth-dependent statement found is Conrey's survey: ≤ 1% at δ = 8 (unreferenced in the survey).

## Prediction check
- Selberg-type explicit bounds trivial for δ ≤ 3 (about 80%): SUPPORTED. Simonič's constants give bounds ≥ 19 even at the method's floor.
- Levinson / Conrey-type the best, with 0.3–0.5 (about 70% / 50%): PARTLY REFUTED.
  - The Levinson method's best on-line proportion gives about 0.58.
  - The best explicit numbers come from the newer two-moment on-line proportions (≈ 0.327–0.333).
  - No depth-dependent Levinson-type number for δ ≤ 3 was found at source; Conrey's density announcement could not be retrieved.
- No 2020s explicit density paper beats this (about 75%): SUPPORTED for what was found. The explicit Ingham-type and log-free estimates found by search (Kadiri–Lumley–Ng; Bellotti; Chourasiya–Simonič, arXiv:2507.15184) are for σ well away from ½, per Simonič p. 2 for KLN ("produces non-trivial bound for σ > 5/8").
