# Route 3, task A2 — the prize if tr G̃³ at band λ = 1 were unconditional (am-cert, 2026-10-12)

Question (lead, 2026-10-12). Suppose tr G̃³ at λ = 1 were available unconditionally, with the sine-kernel value. What is
the best certificate for the board quantity N₀*(T,2T)/N(T,2T), the distinct on-line zeros? Off-line pairs are allowed.

## 0. Pre-registration (written before any computation)

Reasoning so far, by hand. Every block's trace equals its zero count, so the third moment enters only through
D := m₃ − 3m₂ + 2 = (1/N)·Σ φ(μᵢ), where φ(x) = x(x−1)(x−2) and the sum runs over the d = N eigenvalues of G̃.
- Some blocks have D = 0: an isolated simple on-line zero (eigenvalue 1), and an off-line pair at any depth
  (eigenvalues (2+b, −b)).
- The two-moment extremal for Theorem A is (2/3)N isolated simple on-line zeros plus (1/6)N off-line pairs of depth → 0.
  It therefore has m₃ = 3m₂ − 2 = 2, which is exactly the sine-kernel value.

Predictions:
- **P1 (literal setup m = (1, 4/3, 2)).** The three-moment ceiling for N₀*/N is exactly 2/3, the same as two moments.
  The certificate is Theorem A's, and certificate and extremal meet. Confidence: high (a hand derivation, to be checked
  numerically).
- **P2 (sign of D).** A window with D > 0 gains nothing. Stacked off-line pairs, which cost nothing in N₀*, absorb any
  positive D at vanishing cost in m₂. The third moment helps only for windows with D < 0, and then by about |D|.
- **P3 (window freedom at λ = 1).** The three-moment prize, optimised over windows, lies in [0.672, 0.690], point
  estimate 0.678.
  - This is below the go/no-go threshold of 0.69, with probability about 75%.
  - It is below the lead's band of 0.70–0.78.
  - Reason: D is a purely triple-correlation term that vanishes at the box window. The Montgomery–Taylor window moves m₂
    by only 0.006, and I expect |D| of the same order.
- **P4.** The n-point / Gram-defect refinement acts on the cost-1 (simple-cluster) side. I expect it to stack only
  partially: it and the third moment both penalise the same clustered-simple configurations.

## 1. Answer

**The third moment at λ = 1 adds nothing to N₀*, even if it were unconditional.** This is a property of the certificate
class: certificates that read tr G̃, ‖G̃‖²_F and tr G̃³ for one window, together with the (Z) block structure.
- The class cannot beat its own two-moment value, either spectrally or with the actual geometry of the zero vectors.
- Deep interacting off-line pairs absorb any third-moment constraint at vanishing cost in the second moment.

| framework | 2 moments | 3 moments (m₃ unconditional) |
|---|---|---|
| literal setup (box window, m = 1, 4/3, 2) | 2/3 | **2/3**: the two-moment extremal already has m₃ = 2 |
| spectral, any window (the setup asked) | 0.6725 (Thm D) | **0.6725**: absorber (b) below; no cubic certificate is valid |
| spectral, interacting off-line pairs forbidden | 0.6725 | 0.685558 (cubic certificate meets the extremal; window ≈ cos(8s/5)) |
| geometric (actual zero vectors), cos(8s/5) window | 0.67198 | **→ 0.67198** as the absorber depth δ → ∞ (0.67679 at δ = 1, 0.67296 at δ = 3) |

All values are below the 0.69 threshold.
- In the unconditional frameworks (rows 2 and 4) the prize equals the two-moment value.
- It also sits below the board 0.67357. That figure is a geometry-aware two-moment certificate, which the third moment
  cannot improve for the same reason.

## 2. Inputs checked

- **The m_k(1).** PDF p. 25 §7.5(f) reads m_k(1) = 1, 4/3, 2, 13/4, Λ₂(0;1) = 5/36, and HL*(4) ⇒ 13/18.
  - m₁, m₂, m₃ re-derived in closed form for the box window: m₃ = 1 + 2∫Λ³ = 2, with Λ the Fejér triangle. m₄ was not
    re-derived.
- **Moments for a general window.** Window w = ϕ² on [−½, ½], ∫w = 1, K = ŵ:
  - m₂(w) = ∫w² + ∫∫ w(a)w(b)|a−b|;
  - m₃(w) = ∫w³ + 3∫∫ w(a)² w(b) |a−b|.

  Both are verified to 1e-6 against the sine-process 3-point formula.
  - Validation against the paper: cos(8s/5) gives 2m₂ − m₃ = 0.685244, the paper's (g) value 0.68524. The
    Montgomery–Taylor window cos(√2 s) gives 2 − m₂ = 0.672501 (Theorem D).
  - Consequence: in band 1 the sine-kernel triple correlation has **no connected part**. m₃ is fixed by the pair form
    factor (CUE: Diaconis–Shahshahani, E[Tr Uᵃ Tr Uᵇ conj(Tr Uᵃ⁺ᵇ)] = 0 for N ≥ a + b). So an unconditional m₃ at
    λ = 1 would say only that the connected triple form factor of the zeros vanishes in band.
- **Scripts:** `/tmp/amcert_r3/{mom,lp,absorb,geo,glp,glp2,kappa,kmax,wopt}.py`.

## 3. The structure of the third moment

Every (Z) block has trace equal to its zero count, so with d = N the third moment enters only through
D := m₃ − 3m₂ + 2 = (1/N)·Σᵢ φ(μᵢ), φ(x) = x(x−1)(x−2).

| block | D contribution | cost in N₀* |
|---|---|---|
| isolated simple (eigenvalue 1) | 0 | 1 |
| off-line pair at any depth b (eigenvalues 2+b, −b) | 0 | 0 |
| k-fold stacked pair | > 0 | 0 |
| simple-zero cluster (Gram spectrum μ ≥ 0, mean 1) | ≥ −e(1−e) at M₂ = 1+e | 1 |

D by window:

| window | D | 2 − m₂ |
|---|---|---|
| box | 0 | 2/3 |
| Montgomery–Taylor | −0.011775 | 0.672501 |
| cos(8s/5) | −0.013262 | 0.671982 |
| optimum of row 3 | −0.013364 | 0.671923 |

## 4. Spectral framework: the absorbers (configuration-by-configuration constructions)

- **(a) D > 0.** A k-fold coincident off-line pair at depth 0 has per-slot (M₂, D) = (2k, (2k−1)(2k−2)). Mass ε at large
  k supplies any positive D while its M₂ share → 0. Cost 0.
- **(b) D < 0.** Two off-line pairs B_j = 2(x_j x_jᵀ − y yᵀ) with a shared imaginary part y and orthogonal real parts
  x₁ ⊥ x₂ ⊥ y, |x_j|² − |y|² = 1.
  - Each B_j is a legitimate pair block: trace 2, eigenvalues (2+b, −b).
  - Q = B₁ + B₂ has eigenvalues (2+t/2, 2+t/2, −t, 0), with n₊ = 2 ≤ p.
  - Σφ = −(1.5t² + 0.75t³) and Σx² = 8 + 4t + 1.5t², so a vanishing mass supplies any negative D. Cost 0.
  - Verified with explicit 6×6 matrices at t = 1, 3, 10.
- **Consequence.** A cubic certificate (s ≥ Σ g(μᵢ), deg g = 3) must have a₃ ≤ 0 by (a) and a₃ ≥ 0 by (b). So a₃ = 0,
  and the best certificate is Lemma 3.2 itself, with value 2 − m₂(w).
  - LP check (MT window): 0.673099 (t = 40), 0.672560 (t = 400), 0.672507 (t = 4000), against 2 − m₂ = 0.672501.
- **Schur–Horn as in §7.5(g)** needs H ⪰ 0, i.e. no off-line part. Unconditionally only tr(P+Q)³ is observed. The cross
  terms tr P²Q, tr PQ² and tr Q³ are where the absorbers sit, so that route does not transfer.

## 5. If interacting off-line pairs were excluded (spectral, orthogonal blocks)

- **Certificate.** s ≥ d − tr[G(G−c)²]/(2−c)², the cubic analogue of Lemma 3.2. It is valid blockwise:
  - simple clusters, because −x(x−c)² ≤ 0 on [0,∞);
  - a single pair at any depth, because (2+b)(2+b−c)² − b(b+c)² is increasing in b;
  - stacked pairs and multiplicities.

  Its value is 1 − (m₃ − 2cm₂ + c²)/(2−c)².
- **Extremal.** Dense runs of simple zeros, Gram spectrum {0 with mass 1 − 1/c, c with mass 1/c} (spacing 1/c in the box
  case), plus depth-0 pairs.
- They meet: LP 0.684490 against the dual 0.684486 (MT, c = 1.0175).
- Window-optimised: **0.685558** (c = 1.0199, window ≈ cos(8s/5)). This is the most a third moment could give if
  interacting deep pairs were ruled out.
- **What breaks it.** The certificate fails on random interacting configurations whenever two or more off-line pairs of
  depth b ≳ 1–3 interact (min slack down to −10³). With only shallow pairs (b ≤ 1) it held on 60,000 samples.

## 6. Geometric framework (actual zero vectors)

- **Model.** Zero vectors X = ϕ cosh(2πδu)e^{2πixu}, Y = −iϕ sinh(2πδu)e^{2πixu} on u ∈ [−½, ½], with height x and depth δ
  in mean spacings.
  - Check: an isolated pair at δ = 0.4 gives eigenvalues (3.44, −1.44) and trace 2.
- **Absorber (b) is not realised literally.** Geometric deep pairs have nearly ±-symmetric spectra:
  Σx³/(Σx²)^{3/2} ≥ −0.01.
- **But a geometric two-pair absorber exists.** Two off-line pairs at equal depth δ, heights about 0.55–0.67 mean
  spacings apart. κ = −Σφ/(Σx² − 2·slots) is the D bought per unit of M₂:

  | δ (mean spacings) | κ |
  |---|---|
  | 0.75 | 1.61 |
  | 1 | 2.76 |
  | 1.5 | 5.35 |
  | 2 | 8.07 |
  | 2.5 | 10.83 |
  | 3 | 13.62 |

  κ grows linearly in δ without bound, so the cost in N₀* is ≈ |D|/κ → 0.
- **LP with cos(8s/5)** (isolated simples, dense runs, pairs at all depths, stacked, multiplicities):
  - 3 moments, no absorber: 0.68885;
  - with the absorber: 0.67679 (δ = 1), 0.67446 (1.5), 0.67363 (2), 0.67321 (2.5), 0.67296 (3);
  - two-moment value: 0.67198.
- **Allowed?** Depth 3 mean spacings is β = 3·2π/log T off the line. Nothing in the method's inputs excludes it.

## 7. Stacking with the n-point / Gram-defect refinement

- Unconditionally the question does not arise: the third-moment gain is 0 in both frameworks. The n-point gain
  (board 0.67357; geometric ceilings 0.6777 single-window, 0.68183 band-1 law) stands on its own and gets nothing from tr G̃³.
- Under a depth bound δ ≤ δ₀ (all zeros within δ₀ mean spacings of the line, an input not available
  unconditionally), the gain is ≈ |D|/κ(δ₀), about +0.005 at δ₀ = 1 and up to +0.0137 at δ₀ → 0.
  - That gain comes from penalising dense simple runs, which is the same side the n-point refinement works on.
  - So I expect partial stacking only. Not computed.

## 8. What a forward step would need (input, not instrument)

Something that controls interacting deep off-line pairs:
- a fourth moment (Σx⁴ excludes absorbers of both kinds; cf. §7.5(f), HL*(4) ⇒ 13/18);
- or a bound on the number of off-line zeros of depth ≥ δ mean spacings, at o(N) relative mass, which is a zero-density
  input at scale 1/log T.

tr G̃³ alone is not such an input.

## 9. Prediction scoring

- **P1 (box: exactly 2/3, meets Theorem A): SUPPORTED.**
- **P2:**
  - D > 0 is absorbed: SUPPORTED.
  - "D < 0 helps by ≈ |D|": REFUTED. It holds only when interacting deep pairs are excluded (§5); otherwise absorber (b)
    or its geometric form absorbs it too.
- **P3 ([0.672, 0.690], point 0.678): the band holds, the point is REFUTED.** The prize is 0.6725 spectral / → 0.67198
  geometric at this window, a gain of 0, not ≈ +0.005. I under-weighted interacting off-line pairs.
- **P4: moot** unconditionally (§7).
- The lead's prediction of 0.70–0.78 is refuted in every framework computed. The most generous one (interacting pairs
  excluded) gives 0.6856.

## 10. Refutation spec (the claim in §1 is about the instrument; for independent checking)

Self-contained; needs only NumPy/SciPy.
- **Claim.** Let G be a real symmetric d×d matrix written as G = Σ_j m_j v_j v_jᵀ + Σ_k 2(x_k x_kᵀ − y_k y_kᵀ), with:
  - unit v_j;
  - x_k ⊥ y_k and |x_k|² − |y_k|² = 1;
  - d = Σ m_j + 2·#k;
  - s = number of j.

  Suppose only τ₂ = tr G²/d and τ₃ = tr G³/d are known, with τ₂ = 1.3280184, τ₃ = 1.9707930 (the cos(8s/5) window values). Then no inequality
  s/d ≥ F(τ₂, τ₃) valid for all such G has F(τ₂, τ₃) > 2 − τ₂ + 10⁻⁴.
- **Procedure.** Minimise s/d over mixtures of the following, matching tr G/d = 1, τ₂ and τ₃ (LP over mixture weights):
  - isolated v_j with m = 1;
  - isolated pairs with |y|² = b/2;
  - the two-pair block of §4(b) at t ∈ {40, 400, 4000}.
- **Decision rule (pre-registered).**
  - The claim is REFUTED if, for t = 4000, the minimum exceeds 2 − τ₂ + 10⁻⁴ = 0.6720816.
  - It is SUPPORTED if the minimum is ≤ 0.6720816.
- **Predicted outcome:** SUPPORTED, minimum ≈ 0.67199. The two-pair block supplies the required negative
  Σ x(x−1)(x−2) at vanishing tr G² share.
- **Disclosure.** I already ran this LP while verifying the construction: 0.6726552 (t = 40), 0.6720480 (t = 400),
  0.6719882 (t = 4000). An independent re-run is still the check.
</content>
</invoke>

---

## A2-ext. Four moments, prize table in λ (lead, 2026-10-12)

### 0'. Pre-registration (written before any m₄ computation or LP)

Inputs to be computed:
- sine-kernel (box window) Gram moments m_k(λ), k ≤ 4, paper normalisation (mean eigenvalue 1 over d = λN slots);
- m₄ through the cumulant expansion of the sine process. The 4-cycle has 15 set partitions: the singleton/pair terms are
  elementary, and the connected κ₄ comes from Soshnikov's formula with interval-intersection traces.
- The check is m(1) = (1, 4/3, 2, 13/4).

Predictions:
- **Q1.** m₂(λ) = 1 + λ²/3 exactly. m₃(λ) has no connected part for λ ≤ 1. m₄(λ) has a connected part only for
  λ > 1/2.
- **Q2 (Christoffel / Prop 4.5 count).** s/N ≥ 2λ(1 − Λ₂(0;λ)) − 1 equals 13/18 = 0.7222 at λ = 1.
  - It first beats 0.6736 at λ ≈ 0.93 (range 0.90–0.96).
  - It is below the board at λ = 0.66 (the cap there is 0.66 < 0.6736).
- **Q3 (block-structured LP over spectral configurations, off-line pairs and absorbers allowed).** It improves on
  Christoffel, because it uses block integrality (on-line eigenvalues come from Gram blocks with integer traces):
  - 0.73–0.76 at λ → 1;
  - first beats 0.6736 at λ ≈ 0.88 (range 0.84–0.92).
  - The fourth moment caps absorbers, since Σx⁴ grows like t⁴, so the third moment becomes useful again in combination.
- **Q4.** The value at λ = 0.66 is ≤ 0.66 for every certificate (Prop 7.4 cap), so it is not a route at the bottom of
  the MRT range. The route needs m₄ at λ ≳ 0.9.
