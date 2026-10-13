# ROUTE3_B1: can a window make the fourth-moment kernel Ŵ ≥ 0 on the low scales, and what is the sieve Δ? (bridge-port, 2026-10-12)

Task (lead, 10-12), desk only:
1. Ŵ exactly, as a function of the window ϕ in the Zeta23 setting (R; Yang–Yang Prop. 3.5; Zeta23 (2.20), Lemma 2.2), and the
   argument range the low scales u ∈ (1, 33/25) occupy.
2. Can an admissible window (supp ϕ ⊂ [−L/2, L/2]) make Ŵ ≥ 0 there? Effect on H(λ) and the two-moment constants.
3. If yes: Δ, the excess from a sieve upper bound on the low scales (≈ 11.5 % of R at λ = 1); is Δ < 1/12 plausible?

## Prediction (written before any computation below; after reading ROUTE3.md, A1c, A1d, Zeta23 §2.2 and Yang–Yang §3)

**P1 (≈ 85 %).** Ŵ does not depend on ϕ at all.
- It is the transform of the HEIGHT window, i.e. the τ-range [T, 2T] of the Gabor grid, which is where the [sin 2TΔ − sin TΔ]/Δ comes
  from.
- ϕ enters R only through the leg-overlap factor O₄, a 4-fold overlap of translates of ϕ², which is ≥ 0 for every real ϕ.

**P2 (≈ 85 %).** No admissible choice makes Ŵ ≥ 0 on the uncovered range.
- ϕ does not enter Ŵ.
- The other free choice is a height weighting: a diagonal congruence D G D keeps the positive index by Sylvester. It gives a kernel
  with ∫ Ŵ dΔ = 2π·w(0) = 0, because the window sits at height T, not at 0. So the kernel is signed.
- Positivity can hold only on x = TΔ ≤ x* = O(1). The uncovered range reaches x ≈ T^{1−25u/33} → ∞.

**P3 (≈ 70 %).** Δ < 1/12 is NOT plausible by a sieve route, for any sieve constant.
- At scale m > T the off-diagonal pairs carry absolute kernel mass about (m/T) × (the diagonal mass), and the net R is O(1) only by
  cancellation between Ŵ's lobes.
- A one-sided bound gives up that cancellation, so the excess grows like a power of T.

**P4 (≈ 60 %).** The same amplification means MRT-type inputs (log-power savings) do not cover scales m ≥ T^{1+ε} at proof level
either.
- A1d/Yang–Yang's "covered 88.5 %" would then be a measured share, not a coverage.
- The control: applied to k = 2, the A1d coverage logic would evaluate pair correlation F(α) on part of α ∈ (1.32, 2)
  unconditionally from MRT. I do not believe that is known.

## Answer 1. What Ŵ is, and which argument range the low scales occupy

**Derivation, from Zeta23's own definitions.**
- (2.5)–(2.7): G_kl = ∫ ϕ̂(s − τ_k) ϕ̂(s − τ_l) ν_X(s) ds, with ν_X = µ + Π_X + P_X and P_X(s) = −(1/π) Σ_{n≤X} Λ(n) n^{−1/2} cos(s log n).
- (2.19)–(2.20): τ_k = T + kh, 0 ≤ k < d, so the grid covers heights [T, 2T).
- In tr G⁴ = Σ_{k₁…k₄} G_{k₁k₂} G_{k₂k₃} G_{k₃k₄} G_{k₄k₁}, each shared index sums to K(s, s′) = Σ_{0≤k<d} ϕ̂(s − τ_k) ϕ̂(s′ − τ_k).
  By Lemma 2.2 this is L·Φ(s − s′)·χ(s), where χ is the height cut of the grid (≈ 1_[T,2T], with edges of width O(1/L)).
- So tr G⁴ = L⁴ ∫ Π_i ν_X(s_i) Π_i Φ(s_i − s_{i+1}) χ(s_i) ds.
- Insert Φ(r) = ∫ ϕ²(u) e^{iru} du (Φ = (ϕ²)^, (2.15)) and the four prime terms e^{iσ_i s_i log n_i}.
  - Each s_i-integral gives χ̂(u_i − u_{i−1} + σ_i log n_i), of width 1/T.
  - The u-differences sum to zero around the cycle.
  - Integrating the differences out gives

  **(prime 4-cycle term) ∝ Π Λ(n_i) n_i^{−1/2} · O₄(σ log n) · Ŵ(Δ),  Δ = Σ_i σ_i log n_i,**

  **Ŵ = Re (χ⁴)^,  O₄(ξ) = ∫ ϕ²(u) ϕ²(u + ξ₁) ϕ²(u + ξ₁ + ξ₂) ϕ²(u + ξ₁ + ξ₂ + ξ₃) du.**
- For the sharp grid χ⁴ = 1_[T,2T], so Ŵ(Δ) = ∫_T^{2T} cos(τΔ) dτ = [sin 2TΔ − sin TΔ]/Δ. This is Yang–Yang Prop. 3.5's kernel.
- The class R is the alternating pattern σ = (+, −, +, −): N₁ = n₁n₃ ≠ N₂ = n₂n₄. The cyclic partial sums must stay inside
  supp ϕ², which is what allows N up to X².

**So: Ŵ is the transform of the HEIGHT window (the τ-range of the Gabor grid), and it does not depend on ϕ at all.**
- ϕ enters only through O₄, a 4-fold overlap of translates of ϕ². That is **≥ 0 for every real ϕ**.
- A height weighting (see Answer 2) replaces χ⁴ by (wχ)⁴. For the k-th trace the kernel is the transform of the k-th power of the
  height profile.

**Range of the argument.**
- At scale m = T^u, Δ = log(N₂/N₁) ≈ h/m, so x := TΔ = Th/m, on a lattice of spacing T/m = T^{1−u}.
- MRT averages need shift windows of length ≥ m^{8/33}, so the uncovered shifts are |h| < m^{8/33}.
- **The uncovered argument range is x ∈ (0, T^{1−25u/33}).** It is unbounded as T → ∞ for every u < 33/25, and O(1) only within
  O(1/log T) of u = 33/25.
- The flat-grid kernel x·Ŵ/T = sin 2x − sin x is negative on (π/3, π) (A1d), and periodically after that.

## Answer 2. Can an admissible choice make Ŵ ≥ 0 there? No

**(a) The window ϕ cannot.** Ŵ does not contain ϕ (identity above). Changing ϕ moves only O₄ ≥ 0, a, b and the overlap constants.

**(b) Height weights cannot either.** They are the remaining freedom that acts on the height variable: a congruence S G S* keeps
n₊; its translation-invariant part acts like a window change, and its height-dependent part like a height weight.
- A diagonal congruence D = diag(√w(τ_k)), w > 0 on the grid, keeps n₊ (Sylvester, Zeta23 §3). It changes the moments, and the
  kernel becomes ((wχ)⁴)^, the transform of a weight W ≥ 0 supported on the counting window [T, 2T].
- Then ∫ Ŵ dΔ = 2π·W(0) = 0, so Ŵ is signed, for every such W.
- Checked for the flat window: Poisson gives Σ_{h≠0} Ŵ(h/m) = −T for m > T/π (numerically −999.999, −999.977, −2999.998 for
  (T, m) = (10³, 5·10³), (10³, 2·10⁴), (3·10³, 9·10³)).
- **Local positivity is also capped.** LP over all W ≥ 0 on [cT′, T′] (`route3_b1/lp_kernel.py`, bisection):

| window | ratio | positivity range x* = TΔ |
|---|---|---|
| [T, 2T] (dyadic) | 2 | **π/2** (attained by a point mass at height T: cos(TΔ) ≥ 0). Proof of the cap: for TΔ ∈ (π/2, 3π/4) every cos(τΔ) with τ ∈ [T, 2T] is negative, so Ŵ < 0 there for every W ≥ 0, W ≢ 0 |
| | 4 | 2.05 |
| | 10 | 2.57 |
| | 20 | 2.82 |
| | 100 | ≥ 2.0 (bisection capped) |

- Even a counting window spanning two decades keeps positivity only to x ≈ 3 (in units of T_min·Δ). The uncovered range needs x up
  to T^{1−25u/33} → ∞.
- **Property of this instrument:** no Gabor-grid moment certificate whose height window sits at height ≍ T can have Ŵ ≥ 0 on the
  low scales, except on a sliver of width O(1/log T) at u = 33/25.
- **(c) H(λ) and the two-moment constants:** no change is needed, because no admissible modification helps. For completeness, ϕ
  moves a, b and the edge weights, and the board's H(λ) is window-independent in the flat-top limit w/L → 0.

## Answer 3. The sieve Δ: not < 1/12

- Because Ŵ is signed, a sieve route has to drop the negative lobes. That is legitimate: C(h) := Σ_M F(M)F(M+h) ≥ 0, so no lower
  bound is needed, and parity is not the obstacle. The positive lobes are then bounded by a sieve bound B × (Hardy–Littlewood
  model).
- The excess, even at B = 1, is at least P_low − R_low: the positive-lobe mass of the uncovered scales minus their true (signed)
  contribution.

**The amplification.** At scale m > T:
- there are ≈ m·(m/T) resonant pairs, each with weight ≈ T/m;
- so the off-diagonal kernel mass is ≈ (m/T) × the diagonal mass;
- the net is O(diagonal) only by cancellation (Σ_{h≠0} Ŵ = −T).

Measured on actual prime powers (`route3_b1/amplify2.py`). This is a toy: λ = 1, F = Λ∗Λ with both legs ≤ X, and O₄ is omitted
(it is ≥ 0 and reweights legs). Per dyadic scale, relative to that scale's diagonal, at T = X = 10⁴ with uncovered cutoff
x ≤ T^{8/33}:

| m/T | 1.6 | 3.3 | 6.6 | 13 | 26 | 52 | 105 |
|---|---|---|---|---|---|---|---|
| positive mass P/D | 0.93 | 1.59 | 2.65 | 4.27 | 6.71 | 10.5 | 16.0 |
| absolute mass A/D | 2.48 | 3.89 | 6.09 | 9.50 | 14.6 | 22.6 | 34.2 |

- The growth is ≈ (m/T)^{0.68}.
- Low scales (T ≤ m, 2m ≤ T^{33/25}) against the TOTAL diagonal:

| T | P_low | net S_low |
|---|---|---|
| 10³ | 0.40 | −0.07 |
| 3·10³ | 0.40 | −0.07 |
| 10⁴ | 0.37 | −0.15 |

- **Δ:**
  - In m₄ units, with the diagonal ≈ the {2,2} class (17/60), at T = 10⁴: Δ ≥ (0.37 + 0.15)·0.28 ≈ **0.15 > 1/12** at a perfect
    sieve B = 1.
  - With a Selberg-type B ≈ 3.4–4 (the twin-prime constant; for Λ∗Λ pairs it is not smaller), Δ ≈ 0.4–0.5.
  - **Asymptotically Δ → ∞:** the upper end of the low scales is m/T = T^{0.32}, so P_low grows like T^{0.32·0.68}/log T.
- **Verdict: Δ < 1/12 is not plausible by this route**, for any sieve constant. This is a property of one-sided treatments of a
  zero-mean kernel, not of the sieve's quality.
- Caveat: O₄ changes the constants by O(1) factors. At T = 10⁴, B = 1, a 0.5 suppression of the off-diagonal against the diagonal
  would bring 0.15 to ≈ 0.075. The asymptotic divergence does not depend on it.

## Answer 4 (found on the way). The same amplification limits the TWO-sided coverage

This is stated as a property of the instrument.
- To evaluate R's contribution at scale m to o(1), the h-averaged deviations from the Hardy–Littlewood main term must be
  o((T/m) × main). That is a POWER saving m^{−(1−1/u)}.
- MRT I Thm 1.3 gives relative error log^{−A}; through its variance form and Cauchy–Schwarz the scale-m error is
  ≈ (m/T)·log^{−A/2} in diagonal units.
- So MRT-type input with log-power savings does not cover any scale m ≥ T(log T)^C. The "covered 88.5 %" (Yang–Yang §4, A1d) is a
  measured share, not a coverage.
- **Control:** the same coverage logic, applied to the second moment at band α ∈ (1.32, 2), would evaluate part of Montgomery's
  F(α) beyond α = 1 unconditionally from MRT. By Goldston–Montgomery that part is a short-interval prime-variance statement. I
  know of no result giving it, and it is open even on GRH.
- Refutation spec R2 below.

## Prediction check
- P1 (Ŵ independent of ϕ; ϕ only in O₄ ≥ 0): **SUPPORTED** by derivation from Zeta23 (2.5)–(2.20) and Lemma 2.2.
- P2 (no admissible choice gives Ŵ ≥ 0): **SUPPORTED**. The zero-mean identity and the LP give x* = π/2 for the dyadic window.
- P3 (Δ < 1/12 not plausible): **SUPPORTED**. Δ ≈ 0.15 at T = 10⁴ with B = 1, and diverging in T.
- P4 (MRT log savings do not cover m ≥ T^{1+ε}): derived, not refuted here; issued as R2. The measured per-scale growth
  (m/T)^{0.68} was below my linear guess, because the product density thins toward X².

## Refutation specs (for an independent model; self-contained)

**R1. Claim:** for every nonnegative weight W ≢ 0 supported in [1, 2], the function K(x) = ∫₁² W(s) cos(sx) ds has a negative
value somewhere on [0, π/2 + 0.05].
- Inputs: none.
- Procedure: discretise s ∈ [1, 2] (≥ 400 nodes) and x ∈ [0, π/2 + 0.05] (≥ 1500 nodes). Solve the LP: find W ≥ 0 with Σ W = 1
  and K(x_j) ≥ 0 for all j. Repeat with the right end π/2 − 0.05 as a control, which must be feasible: W = δ₁ gives K = cos x.
- Decision rule (pre-registered): a feasible W at π/2 + 0.05 refutes the claim; infeasibility supports it.
- Predicted outcome: infeasible at π/2 + 0.05 and feasible at π/2 − 0.05. W = δ₁ is optimal, with K = cos x, zero at π/2.

**R2. Claim:** take products N = ab of prime powers a, b ≤ X, F(N) = Σ_{ab=N} Λ(a)Λ(b), and the kernel
k(Δ) = (sin 2TΔ − sin TΔ)/Δ with X = T. Per dyadic scale m ∈ [T, T²], compare:
- the absolute off-diagonal kernel mass A(m) = Σ_{N₁≠N₂ ∈ [m,2m), T|log(N₂/N₁)| ≤ 10} F(N₁)F(N₂)(N₁N₂)^{−1/2}·|k|;
- the diagonal D(m) = T·Σ_{N∈[m,2m)} F(N)²/N.

The claim is that A(m)/D(m) grows without bound as m/T grows, at a rate at least (m/T)^{0.4} over m/T ∈ [2, 500].
- Inputs: T = X ∈ {3·10³, 10⁴, 3·10⁴}.
- Procedure: enumerate the products, sort them, and sum over pairs inside the window.
- Decision rule (pre-registered): a fitted exponent < 0.2 (or a ratio bounded by 10) refutes the claim; ≥ 0.4 supports it.
- Predicted outcome: exponent ≈ 0.6–0.7.
- Interpretation if supported: any input whose relative error is (log)^{−A} contributes an error ≈ (A/D)·(log)^{−A} at that scale,
  which is unbounded.
