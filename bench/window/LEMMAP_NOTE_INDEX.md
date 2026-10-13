# Lemma P — state note, index (2026-10-09)

Lemma P is the single hypothesis behind the D-track board constant κ = 6759644/10⁷. This index ties together the three
section notes; every number has a file pointer in its section note.

| section | file | author |
|---|---|---|
| deep pairs (y ≥ 0.8): identities, pencil lemmas, certified reductions | `LEMMAP_NOTE_deep.md` | bridge-port |
| shallow pairs: single pair, separated class, density lemma, dense blocks | `LEMMAP_NOTE_shallow.md` | window-scope |
| board cost of the certificate, 11 conditions | `LEMMAP_NOTE_cost.md` | am-cert |

Running log: `~/work/riemann-submission/SUBMISSION.md` (entries of 2026-10-09).

## Lean (compiled)

- **Current hypothesis.** `rootR8f/AMW/DEPLin.lean` gives `AMW.am_dyadic_R8_ratL` and `AMW.am_cumulative_R8_ratL`: κ = 6759644/10⁷
  with sole hypothesis `LemmaPObjL zetaZeroConfig (qfAM 0 − cR8.y 0) (gPL cR8 0)`.
  - Axioms `[propext, Classical.choice, Quot.sound]` for all 13 theorems; axiom check re-run independently by the lead.
  - `LemmaPObjL` uses LINEAR weights: 1 for a simple on-line zero, 2M for an on-line zero of multiplicity M ≥ 2, 2m off the line.
    `pLin_add_N0s` proves pLin + N₀ˢ = 2N exactly, so the hypothesis reads h₀N + g₀(2N − N₀ˢ) − εN ≤ frobSq, the weakest form
    the count step needs.
  - It is implied by both earlier forms (`lemmaPObjL_of_lemmaPObjZ`, `lemmaPObjL_of_lemmaPObj`) and holds on on-line windows
    (`lemmaPObjL_R8_online`).
- **Why it was weakened twice (2026-10-09):**
  - `LemmaPObj` (ordinate-grouped) fails configuration-wise on stacked deep pairs (`sat9/e15`).
  - `LemmaPObjZ` (per-zero, mult² on the line, `DEPSq.lean`) fails configuration-wise at an on-line multiplicity M ≥ 4 flanked by
    shallow pairs (M = 4: −0.249 at N = 64; M = 6: −8.12 at N = 256; mp50 and independent code; `band1/round8_onmult_*.log`).
  - The linear form passes the adversarial search (min +3.12, ≈ 0.30·M²; `band1/round9_lin_*.log`).

## Mathematics: strength of each piece

Labels:
- **pencil**: proved by hand.
- **DP**: computer-assisted, double precision with allowances, not interval arithmetic.
- **QP-cert**: two-sided convex-QP bracket on a depth grid, tested configurations only.
- **exact-local**: exact functional, local minima from stated starts.

- Single pair, all depths: DP (shallow note §1).
- Separated pairs, mixed depths (radii 2/4/14 by depth class): DP; the allocation check is exhaustive (shallow §2).
- Deep pairs:
  - pencil: P ≤ 2, equal depths, Lemma LL (isolated dense clusters), Lemma SL (sign of one term open) (deep §2).
  - pencil/exact: the end-potential identity and the bulk per-pair margin τ(a) (deep §1).
  - QP-cert: lattice-like chains with spacing ≤ 0.8 (positions-only reduction).
  - QP-cert: irregular and near-spacing-1 chains (two depth labels), on the labellings tested (deep §3).
- Shallow dense blocks:
  - pencil: the density lemma DV.
  - DP: saved geometries, and the graded family's per-pair slope.
  - exact-local: the local-density shape at environment density 2/3 and 0.93 (shallow §3–5).
- Instruments that failed their pre-registered tests are listed with their numbers in deep §4 and shallow §6.
- Truth checks of the full functional (exact-local, 2026-10-09, after the board pause):
  - deep pairs inside an on-line environment: SUPPORTS, min LP +21.4 (`sat9/e38.log`);
  - mixed shallow/deep: SUPPORTS for on-line multiplicity ≤ 3 (shallow §8);
  - long fixed chains at spacing 0.99, N = 4P: a pre-registered extrapolation rule fired at P ≤ 128 (`sat9/e39*.log`).
    - Converged, environment-separated (`sat9/e41*.log`, `sat9/e42*.log`): LP_chain = +1292 (P = 128), +861 (P = 256),
      ≤ +578 (P = 512, unconverged), still falling. **Undecided.**
    - Last numerics round (`sat9/e43*.log`): the exact-kernel evaluator is validated, but the optimiser cannot track the
      minima beyond P ≈ 256 (stiff deep interiors).
    - **Analytic end-term study (`sat9/e44*`, `e45*`; deep note §1.6, §3, §5): family CLOSED, no counterexample.**
      - Exact Abel form (checked ≤ 1.6e-9). For long chains it reduces to (1′) ≈ 2E_end + τ(a)P with a P-free end
        functional E_end.
      - With shallow end pairs, E_end < 0, down to ≈ −0.21. End positivity (E_∞) is FALSE in that form.
      - All 90 mirrored finite chains have (1′) > 0. The minimum is +0.592 at a = 0.999, P = 100 (`sat9/e45g.log`);
        for a ≤ 0.99 it is +1.423 (`sat9/e45f.log`).
      - Candidate lemma shape, NOT proved: (1′) ≥ τ(a)P − 2 sup_L|E_end| with sup_L|E_end| ≤ C(a). The data suggest
        C ≈ 0.15–0.3, and the thinnest corner is a → 1⁻ (τ(1) = 0.0055).
  - **Correction:** the deep note's end-positivity minima (§3, "≈ +15 to +27"; e31b) are NOT global. With deeper interiors,
    Q_pp at P = 256 is ≤ 103.7 (a = 0.95) and ≤ 23.0 (a = 0.90) (`sat9/e42c_*.log`).

## What is not established

- A certificate covering **all** configurations.
  - For deep chains, the optimal dual witness is not local: transplants at radius ≤ 24 give certified D < 0
    (sat9/e35, e36), and the endpoint form of the depth minimum is refuted (sat9/e37).
  - For shallow dense blocks there is no geometry-covering method: the alphabet DP is estimated infeasible, and the
    uniform-interior reduction is refuted.
- Interval-arithmetic rigour for any numerical piece.
- Deep pairs with y > 3, and the coupling between deep clusters and nearby on-line zeros.

## Board verdict (cost note)

The current architecture does not fit the board budget, which is ≈ 950 board-s (conservative) to ≈ 1,300 (nominal)
after the base D file.
- Ported as-is: ≈ 7.8e6 board-s.
- Compressed, on the band as tested: known-size pieces ≈ 9,260; smallest-count total ≈ 14,200.
- The per-configuration pieces have no finite count.

This is a statement about this certificate architecture, not about Lemma P. The board route is paused under the rule
pre-registered on 2026-10-09; PC8E (κ 0.6735015) is the live #1.
