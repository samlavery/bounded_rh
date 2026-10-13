# ROUTE3_A1b: Knausgård, arXiv:2610.08965, read at source (window-scope, 2026-10-12)

Task (lead, 10-12):
1. the method for > 67.35% simple on-line and > 83.9% distinct: its inputs, local functional, frames and θ;
2. whether any three-point or triple-correlation term appears or is discussed;
3. how it relates to the board chain (Zeta23 + Ainta + Arun's Gram-defect);
4. what the author says limits his constants.

## Prediction (written before reading the paper or the repository)
- Q1: the only arithmetic input is the unconditional pair-correlation (second-moment) asymptotic, in the BGSTB / Montgomery form. The local functional is a frame or Gram-type inequality on 7–8 consecutive points with a close-pair threshold θ = 17/20. The constants are certified by a finite search (about 85%).
- Q2: no three-point term in the proofs (about 85%). Higher correlations get at most a remark as an extension (about 50%).
- Q3: the same family as the board chain, i.e. pair-correlation energy plus a local inequality on consecutive zeros. The 67.35% is the board chain's own number or a close relative, not an independent mechanism (about 65%).
- Q4: he names the band-width ≤ 1 of the pair-correlation input, and the frame size and search cost, as the limits (about 60%).

## Source
- Read in full where quoted: K. M. Knausgård, "More than 83.9% of the zeros of the Riemann zeta function are distinct and more than 67.35% are simple and on the critical line", arXiv:2610.08965v1, 6 Oct 2026, 43 pp.
- Local copy: `route3_refs/knausgard_2610.08965.pdf`. Page numbers are the paper's own.
- Not inspected: the Lean repository (Distinct839 / Simple673 / Line889).
- Read for route-3 relevance only (§3.2 and the abstract), because Knausgård cites it as the one moment-based report (his [50]): H. Yang, S. Yang, "More than 0.7962 of the zeros … simple and on the critical line", Zenodo 10.5281/zenodo.21975236, Aug 2026 (`route3_refs/yang_yang_zenodo21975237_EN.pdf`).

## Answer 1. Method, inputs, local functional, θ
- **Arithmetic input: pair correlation only.** Proposition 3.1 (p. 13): tr A² = (C(f_ε) + o(1)) N, by "[4, Lemma 5], [23, Proposition 5]".
  - [4] is BGSTB24. Quote: "The unconditional Montgomery theorem [4, Lemma 5] applies to real, even, integrable test functions supported in [−1, 1] … and it sums over all zeros, on or off the line, with multiplicity." The weight w(ρ − ρ′) is removed exactly by applying the theorem to R_ε and R_ε″.
  - Section 7.1 (p. 23): "The proof uses three facts about the zeros: tr A = N, tr A² ≤ (C(f) + o(1))N, and that the rescaled zeros lie in an interval of length N + o(N)."
- **The operator.** From [25] (Lamzouri) and [2] (Alpöge–Furman, the Zeta23 line), p. 13: "A = Σ_z ν_z F_z ⟨F_z̄, ·⟩ … Hermitian, and tr A = N, tr A² = Σ ν_z ν_w K_ε(z − w)²". Off-line pairs give terms with at most one positive eigenvalue ("The splitting and this count follow [2, 25]", p. 14).
- **The count.** Lemma 2.1 at clipping level c.
  - Distinct zeros: c = 67/20. Theorem 3.2, p. 14: lim inf N_d/N ≥ (3 − C(f) + x₂ − x₁ − b)/(2 − 2x₁ + x₂), for a certificate (x₁, x₂, b).
  - Critical line: c = 2 (p. 17: "4c − c² ≥ 4, that is, (c − 2)² ≤ 0. So c = 2"). Theorem 5.1, p. 18: lim inf N₀ˢ/N ≥ (2 − C(f) − b)/(1 − x), for a certificate (x, b) on θ-separated simple points.
- **The local functional.**
  - Distinct zeros: a computer-assisted inequality for SEVEN consecutive θ-separated points with labels d ∈ {1, 2}. Proposition 3.3, p. 16, with inequality (2.3).
  - Critical line: EIGHT points, no labels. (5.3), p. 18: α(y₇ − y₀) + Σ_{i<j} W_ij K(y_j − y_i)² + Σ_r B_r(g_r) ≥ x, with column weights Σ_{i} W_{i,i+s} ≤ 2, and gap corrections B_r with Σ B_r = 0.
  - The corrections are one-gap functions that telescope: "the increments of a storage function in the sense of Willems" (p. 7).
- **θ = 17/20.**
  - Points closer than θ are paired into 2×2 blocks. The rest are θ-separated, and on them a Selberg majorant g (ĝ supported in (−θ, θ), Λ = ĝ(0) = 1.67105 < 2c) bounds the Gram matrix, so there is no clipping (p. 5; first window, p. 15).
  - Remark 3.4 (p. 16): θ is confined to roughly (0.8267, 0.8705) for c = 67/20, and to ≥ 0.7855 for any admissible c. "The choice matters little for the constant."
- **Windows.** Trigonometric polynomials f(u) = 1 + Σ_j a_j cos(2πju) on |u| ≤ 1/2: six terms (first window, Theorem 1.1) and ten terms (second window, Theorem 1.3). These are not Montgomery–Taylor; C(f) is about 0.005 larger, for more interaction (Table 1, p. 6).
- **Certificates.**
  - Distinct: (x₁, x₂, b) = (0.054350, 0.069433, 0.037314) (p. 7).
  - Critical line: (x, b) = (0.008722, 0.004389) (p. 7).
  - Results: 1645064/1960733 = 0.83900 distinct; 1669159/2478195 = 0.6735382 simple and on the line (Theorem 1.3, p. 3).
- **Formal status** (p. 1 and Table 5, p. 33): the four theorems are proved in Lean on top of the Zeta23 library ([7, 2]), "with three axioms beyond those of Mathlib, one per inequality. Each records that a search program returned true."

## Answer 2. Any three-point or triple-correlation term?
- **No.** The proofs use the first two moments only (the three facts quoted from p. 23). The local inequalities are pair energies inside 7- or 8-point frames.
- What the paper says about higher moments:
  - p. 2: "A report [50] claims much larger values, 0.7962 for this quantity and 0.8981 for distinct zeros, from trace moments of order up to six. Its authors grade it as a candidate whose analytic part is not yet verified. In [2, Section 7.2] bounds of this kind, such as 13/18 from the fourth moment, are derived from a hypothesis on these moments. We do not count this report among the values above."
  - p. 30: "We do not know whether laws with triple points give a smaller constant." Here "triple points" means multiplicity-3 points in the ceiling construction, not triple correlation.
- So his ceilings are ceilings for arguments that use only tr A, tr A² and the length (Section 7.1, Q*(f), p. 23). A third-moment input is outside their scope.
- **On the third moment itself, from Yang–Yang §3.2 (read at source):**
  - Lemma 3.3 ("Exact 3-cycle resonances", p. 11): for λ ≤ 1 and prime powers n₁, n₂, n₃ ≤ T^λ with |log(n₁n₂/n₃)| ≤ C/T, n₁n₂ = n₃. This is RS96's integer-spacing argument again, consistent with ROUTE3_A1 §1b.
  - Theorem 3.4 (p. 11): the third normalised moment µ₃ "converges … and its limit tends to 2 in the endpoint limit λ → 1⁻".
  - m₃ = 2 is the value that, as the lead noted, the two-moment extremal already has. The third moment at λ = 1 therefore adds nothing spectrally.
  - Yang–Yang's claimed gains (0.6916 to 0.7962) come from the 4th to 6th moments ("the exact fourth moment", m₄ = 13/4, via their "Lemma D" with Siegel–Walfisz and Vaughan).
  - By RS96's remark (pp. 35–36) and Zeta23 §7.5(f), k = 4 with λ > 1/2 is Hardy–Littlewood territory.
  - Yang–Yang cite neither Rudnick–Sarnak nor Hejhal (grep: none). Their own grading is "certified-candidate, not record … the analytic layer is unformalized, and no external review has taken place" (p. 1).
  - I have NOT checked Lemma D.

## Answer 3. Relation to the board chain (Zeta23 + ainta + Arun's Gram corrections)
- **The same mechanism, developed in parallel.** Knausgård states the lineage himself:
  - operator and splitting from [2, 25] (Alpöge–Furman / Zeta23, and Lamzouri), p. 14;
  - the critical-line count Theorem 5.1 "is used in [1] and in [34, (1.8)], for the Montgomery–Taylor window. The bound 0.67305 of [34] is its value at (x, b) = (19/5000, 1/500), and the constant of [1], as quoted in [34], is its value at (x, b) = (4997/1345000, 2680/1345000)" (p. 18);
  - [1] = ainta, github.com/ainta/zeta-simple-zeros; [34] = R. Arun Chandru, "Compensated Gram corrections for zero counts", Zenodo, Sep 2026;
  - the seven-point local input of his first paper [23] was "imported from work on simple zeros [1, 45, 39, 41]" (p. 4);
  - the telescoping correction "for points without labels … is in [34, Section 3.3]" (p. 7);
  - the separation step for simple critical zeros "is due to G. Freund [14]", whose value is 0.673492, which Knausgård "had found … independently" (p. 6);
  - the "defect" (Gram-matrix inequality) is from his own first paper [23, Theorem 2] (p. 4). It is NOT used here ("That inequality is not used here", p. 4).
- **The board's MOP chain is this scheme.** κ = (H − B)/(1 − c) is Theorem 5.1's (2 − C(f) − b)/(1 − x), with H ↔ 2 − C(f), B ↔ b, c ↔ x. The board's close-pair distance d = 17/20 is his θ = 17/20.
- **What differs:**
  - his window: a 10-term cosine polynomial, not Montgomery–Taylor;
  - eight-point frames with one-gap storage corrections;
  - a Selberg majorant for the separated block.
- **The board's entries in his list:** S. Lavery [26] (0.6734812, eight-point frames, Riemann.fail attempt-014) and dani-ani0 [9] (0.6734824), quoted as "up to 0.67348" (p. 2).
- **Comparison with the board's current numbers (window-scope's estimates, not his):**
  - t570 nine-point κ = 0.6735700 is above his 0.6735382;
  - our rank-limited frame ceilings (n = 8: 0.67356, n = 9: 0.67360, n = ∞: 0.67381) are of the same size as his second-window ceilings (8 points 0.67357, all pairs 0.67383, Proposition 7.3, p. 27);
  - they are for different windows.

## Answer 4. What he says limits his constants
- **Ground-state ceilings** (Section 7; Figure 2, p. 8; "How far the method goes", pp. 7–9):
  - distinct zeros: first window with seven points < 0.83916 (formalised); first window with any frame length Q* < 0.83998 (Proposition 7.1); any window with V(f) ≤ 10B(f) < 0.84093 (Corollary 7.9, p. 30);
  - simple critical zeros: second window with eight points < 0.67357, all pairs < 0.67383 (Proposition 7.3, p. 27); any window with V ≤ 10B < 0.68185 (Corollary 7.9), "in agreement with [2, Section 7.2]" (p. 9). This is Zeta23's pair-correlation cap.
  - "The certificate of Theorem 1.3 realises at least 98% of what frames of eight points can add to 2 − C(f) for the second window" (p. 27).
  - The trial states that saturate the ceilings alternate gaps near 1 and near 2, "so that all distances are close to integers, where K is small" (p. 27).
- **The window, §7.5 (p. 28):** "Three requirements compete. The energy constant C(f) should be small … The lattice energy should be large … Finally the edge value f(1/2) must be small enough for the majorant … So here it is the edge value of f that decides whether the separated blocks escape the clipping."
- **The clipping level and θ** (Remark 3.4, p. 16): c is confined to (2Λ, 2 + √2 − 2x₁) = (3.3421, 3.3752), and θ to about (0.8267, 0.8705).
- **The input itself:** the ceilings hold for any argument that uses only tr A, tr A² (band [−1, 1]) and the length (p. 23). Corollary 7.9's 0.68185 rests on a law of period 256 "with the pair correlation of the zeros in the band" (Definition 7.5 and Proposition 7.8, p. 30).

## Prediction check
- Q1 (pair correlation only; seven- or eight-point frames; θ = 17/20; finite search): SUPPORTED.
- Q2 (no three-point term, about 85%): SUPPORTED. "A remark on higher moments" (about 50%): he cites the Yang–Yang moment report and [2]'s fourth-moment bound, without his own extension.
- Q3 (same family as the board chain, about 65%): SUPPORTED. His 67.35% is a parallel development of the same scheme, not the board's own number.
- Q4 (limits named as band ≤ 1 and frame size): SUPPORTED, with more detail. The window-edge / majorant tension and explicit ground-state ceilings are his main statements.

## Consequence for route 3 (my reading)
- His ceilings are exactly the two-moment wall (Q* uses only tr A and tr A²).
- The third moment at λ = 1 equals the extremal's value (m₃ = 2: Yang–Yang Theorem 3.4, the lead's computation, Zeta23 (f)). A purely spectral use of the third moment therefore cannot move past these walls, consistent with the lead's note.
- What could move them is a configuration-level three-point term: a local functional that uses triple products K(y_i − y_j)K(y_j − y_k)K(y_k − y_i) inside a frame, fed by the third-moment identity.
- None of the papers read uses such a term.
- Whether that helps is A2's question. This file makes no claim about it.
