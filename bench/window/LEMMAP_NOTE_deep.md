# Lemma P state note: the deep-pair part (bridge-port, 2026-10-09)

Scope: the pair–pair inequality (1′) for off-line pairs of depth y ≥ 0.8, in the per-zero (pSq) convention. Each claim is
stated at the strength proved or measured.

File pointers:
- `S/` = `~/work/riemann-submission/bench/window/sat9/`
- `L/` = `~/work/riemann-submission/bench/window/rootR8f/AMW/`

Numerics are double precision, on the 6001-point α-grid of `S/common.py`, and on the tested configurations only.

## 0. Setting and Lean status

Two-sided inner products are in L²(q) on [−1, 1], with q the R8 window and ∫q = 1. Pairs sit at ordinates s_p with depths
y_p, and:
- B_y(α) = 2cosh(2παy) − 2, c_p = 2 + B_{y_p};
- V = Σ_p e(αs_p), S_A = Σ_p c_p·e(αs_p), S_B = S_A − 2V;
- Q_pp = ‖S_A‖² − 4‖V‖², T_g^pp = 4Σ_{p≠p'} g(s_p − s_p'), h = K − g.

The target (1′) is Q_pp + T_g^pp ≥ 0.

Lean status: the sole hypothesis of κ = 6759644/10⁷ is now `LemmaPObjZ` (per-zero weights: m² on the line, 2m off it).
- File: `L/DEPSq.lean`. Axioms standard (`L/DEPSqAx.lean`).
- Reason: the ordinate-grouped `ordSq` form fails in the periodic model.
  - Configuration: two multiplicity-m stacks at depth 0.8 joined by a chain of six deeper pairs.
  - E − F_C = −54 (m = 12), −207 (m = 16), −1051 (m = 32), stable in N from 192 to 384 (`S/e15_Nscan.log`, `S/e15_thresh.log`).
  - See `L/DE_LEAN_STATE.md`.

## 1. Exact identities

1. **Target form.** Q_pp + T_g^pp = ‖S_A‖²_q − 4g(0)P − 4Σ_{p,p'} h(s_p − s_p').
   - Since ĥ ≥ 0, |h(u)| ≤ h(0) = 1 − g(0) = 0.0095692.
   - Checked numerically to ≤ 2e-14 (`S/e19_c1_big.log`, column "identity err").
2. **Dual form.** Q_pp = ‖S_B‖² + 4Re⟨S_B, V⟩ ≥ 4Re⟨S_B, W⟩ − 4‖W − V‖² for every W, with equality at W = S_A/2.
   - If W does not depend on the depths, the depths enter one pair at a time: 4Re⟨S_B, W⟩ = Σ_p 4⟨B_{y_p}, Re(W̄e_p)⟩.
3. **End potentials** (lead's derivation and check, `S/lead_endpot_check.py` and `S/lead_endpot_check.log`). The check uses
   a generic q = (1 − |α|)²₊ in closed form, not the certificate's qf, so it verifies the identity, not the certificate's
   numbers. On an exact lattice of spacing a < 1:
   - 4Re⟨S_B, V⟩ = −4Σ_p [Λ_{y_p}(p+1) + Λ_{y_p}(P−p)], with Λ_y(j) = Σ_{k≥j} L_y(ka) and L_y = (qB_y)^∨.
   - It agrees with the direct sum to 1e-14 for a ∈ {0.6, 0.76, 0.9}, P ∈ {5, 9, 16}.
4. **Equal-depth lattice, closed form.** For spacing a < 1, depth y and P pairs:
   - Q_pp(P) = C_end(a, y) − ½∫q(B² + 4B)·cos(2πPaα)/sin²(πaα), with C_end(a, y) = ½∫_{−1}^{1} q(B² + 4B)/sin²(πaα).
   - T_g^pp(P) = P·τ(a) − 8Σ_k k·g(ka) + (tail), with τ(a) = 8Σ_{k≥1} g(ka).
   - Check: at a = 0.76, y = 0.8, P = 128, Q_pp = 237.204 against C_end = 237.225.
   - At P = 64, P·τ + C_end − Σ = 315.196 against the direct value 315.206.
   - C_end(·, 0.8) = 209–769 for a ∈ [0.6, 0.95]. All from `S/e31.log`.
5. **Bulk margin.** In the periodic model, an exact lattice with a < 1 has V(α_j) = 0 at every in-band frequency except α = 0,
   and there S_A(0) = 2V(0).
   - So the bulk Q_pp per period is (1/L)·Σ_{j≠0} q·|S_A(α_j)|² ≥ 0, with equality at constant depth.
   - The bulk per-pair margin of (1′) is therefore τ(a) exactly, under the optimal depth profile.
   - τ = 0.6517, 0.3035, 0.0913, 0.0055 at a = 0.85, 0.90, 0.95, 1.00 (`S/e34.log`).
   - τ = 1.2572 at a = 0.76 (`S/e31.log`).
6. **Abel form and the end functional.** On an exact lattice of spacing a < 1, with z = e(αa) and Δc_p = c_p − c_{p−1}
   (Δc_0 = c_0):
   - Q_pp = ∫ q/(4sin²(παa)) · [ |c_0 + Σ_{p=1}^{P−1} Δc_p z^p − c_{P−1} z^P|² − 4|1 − z^P|² ] dα.
   - Checked against the direct evaluator to ≤ 1.6e-9 relative at P = 64, 128, 256 (`S/e44a.log`).
   - The flat interior contributes nothing. For P beyond the end layers, Q_pp ≈ E_end[left] + E_end[right], with the P-free
     functional E_end[c] = ∫ q/(4sin²(παa)) (|Σ_{p≥0} Δc_p z^p|² − 4) dα.
   - For a constant depth y this equals E_const(y) = ∫q(c_y² − 4)/(4sin²) ≥ 0.

## 2. Proved (pencil)

- **P ≤ 2.** P = 1 is immediate. For P = 2, pointwise |c₁e₁ + c₂e₂|² − 4|e₁ + e₂|² ≥ (c₁ − c₂)² ≥ 0, so Q_pp ≥ 0.
- **Equal depths, any P and positions.** Q_pp = ∫q(B² + 4B)|V|² ≥ 0.
- **Lemma LL** (isolated clusters, any depths y ≥ 0).
  - Statement: if P·(2δ·cos(2πδL)·Q̄(δ) − h(0)) ≥ g(0) for some δ ≤ 1/(4L), where Q̄(δ) = (1/2δ)∫_{−δ}^{δ} q, then
    Q_pp + T_g^pp ≥ 0.
  - Proof: B_p ≥ 0 and cos ≥ 0 on |α| ≤ δ, so the low band has |S_A|² ≥ 4|V|² pointwise.
  - With Q̄ grid-evaluated, the length thresholds are:

    | P | 8 | 16 | 32 | 64 | 128 |
    |---|---|---|---|---|---|
    | L ≤ | 1.300 | 2.471 | 4.396 | 7.143 | 10.358 |

    (`S/LL_thresholds.log`). These cover, in isolation, the stack families where Q_pp < 0.
- **Lemma SL.**
  - Setup: for a₀ ∈ (0, 1] let T = (1 − |α|/a₀)₊, κ = min q/T², Φ = FT(T²) ≥ 0 and D_p = Σ_{p'} Φ(s_p − s_p').
  - Statement: ‖S_A‖² ≥ 4κ·Σ_p D_p + C_B, where C_B = 4κ·Σ_{p,p'} ∫T²·B_p·cos(2πα(s_p − s_p')).
  - The B_*-part of C_B (minimum depth) is ≥ 0 exactly. **The sign of the depth-difference part is not proved.**
  - Tests: `S/e22.log`.

## 3. Certified numerically (double precision; tested configurations only)

"Certified" means a two-sided bracket. The convex-QP optimum on a depth grid of step 0.02 is ≥ the quantity, and the hard
evaluation of the maximiser on a step-0.005 grid is ≤ it. This is not interval arithmetic, and the depth minimum is taken on
grid nodes.

- **Regime A, positions-only dual D(s) ≥ 0** (identity 2, with W = V + Σ_n w_n e(αt_n), t_n = the sites plus 4 virtual sites
  per end).
  - Lattices a ∈ {0.6, 0.7, 0.76, 0.8} × P ∈ {6, 12, 24, 48}: hard D from +5.9 to +123.3 (`S/e32d.log`, `S/e34.log`).
  - The same spacings at P = 64 and 128: hard D from +57.3 to +335.1 (`S/e36.log`).
  - Witnesses: `S/e34_witness.json`, `S/e36_w_a*.json`. D ≈ T_g − O(1); the loss against the truth is the depth-profile end
    term.
- **Regime B, class-resolved dual D_K, K = 2** (W = V + Σ_{n,j} w_{n,j}·φ_j·e(αt_n), φ ∈ {1, B_{ŷ1}, B_{ŷ2}}; within-class
  depth minimum).
  - Positive on all six configurations tested. Hard values against the truth:
    - lattice a = 0.9: +183.4 / 184.5 (P = 12), +48.5 / 82.3 (P = 48);
    - minimisers e23: +26.35 / 29.06 (P = 12), +39.16 / 43.01 (16), +58.16 / 61.78 (24), +86.67 / 90.27 (32).
  - At K = 4 the e23 losses are ≈ 0. Source: `S/e33.log`, `S/e33_results.json`.
  - **Labellings covered: L0 (the true min-profile labels) and one greedy single-flip sweep only, not all K^P.**
- **True values found by adversarial search** (not bounds):
  - Binding regime, moderate-density arched chains: minimum total +29.6 at P = 12 (`S/e19_c1_big.log`). Totals for
    P = 3, 4, 6, 8, 12, 16, 24, 32 are 57.0, 42.3, 32.9, 30.1, 29.6, 43.1, 61.8, 90.3 (`S/e19_c1.log`, `S/e19_c1_big.log`).
  - Minimum of Q_pp over depth profiles on exact lattices: ≈ +15 to +27 for a = 0.6–0.8, P = 12–48 (`S/e31b.log`).
    **These are local minima from the stated starts (L-BFGS), NOT global minima.** Deeper interiors give lower values at
    P = 256: ≤ +103.7 (a = 0.95) and ≤ +23.0 (a = 0.90), not converged, against the e31b values ≈ 74–82 at a = 0.9
    (`S/e42c_0.95_256.log`, `S/e42c_0.90_256.log`).
  - Sparse chains: ≥ +1.3e3 (`S/e25_truth.log`).
  - **End functional E_end** (§1.6; exact-kernel quadrature; analytic-Hessian Newton; PD Hessian required for "converged").
    - End depth ≥ 0.8, a = 0.99: converged min E_end = +840.2, +685.1, +500.8 at L = 50, 100, 200. Then ≤ +340.3 at L = 400 and
      ≤ +306.9 at L = 800 and ≤ +286.4 at L = 1600 (not converged; layer length ≈ 485 at L = 1600; `S/e44c_a0.99.log`,
      `S/e45_1.log`). The decrease flattens, but the limit is not established because these are upper bounds.
    - End depth ≥ 0.8, a = 0.95 / 0.90: ≤ +35.6 / ≤ +10.4 at L = 400 (not converged; `S/e44c_a*.log`).
    - **End depth free (y ≥ 0.01): E_end < 0 is attained by actual configurations.**
      - a = 0.99: −0.0439, −0.0792, −0.1273 (converged) at L = 50, 100, 200, and ≤ −0.1767 at L = 400.
      - a = 0.95: ≈ −0.19 to −0.21. a = 0.90: ≈ −0.148.
      - a = 0.999: +0.0031 and +0.00003 at L = 50, 100, and −0.0118 at L = 200 (converged).
      - The optima have a shallow end pair (y_0 = 0.01) in front of a deeper interior (`S/e45_2_a*.log`, `S/e45g.log`).
    - **Every mirrored finite chain built from these layers has (1′) = Q_pp + T_g > 0.** Flat interiors m = 0 … 400 were used,
      90 chains in all.
      - Minimum +0.592 (a = 0.999, L = 50, P = 100; `S/e45g.log`).
      - For a ≤ 0.99 the minimum is +1.423 (a = 0.99, L = 50, P = 100; `S/e45f.log`).
      - T_g ≈ τ(a)P exceeds 2|E_end| in every case.

## 4. Instruments that failed their pre-registered tests

| instrument | result | log |
|---|---|---|
| Posed criterion ‖S_B‖ ≥ 4P + 2M_near | X = 14.35 < 16 at y = 1, P = 4 | `S/e1.log` |
| Q_pp ≥ 0 at unequal deep depths, P ≥ 3 | Q_pp = −19.3, −55.1, −184.6, −185.4 at P = 16, 24, 32, 48 | `S/e9.log`, `S/e9_cfg_*.json` |
| Edge mode as the common mode | edge band [0.85, 1] carries 2.4 of ‖S_A‖² = 201 (e9 P = 16) | `S/e21.log` |
| Per-pair split Q_pp ≥ θΣself − c·T_g | θ_max(c = 1) = 0.25, 0.17, 0.087 at P = 3, 4, 6, depths [0.05, 0.4] | `S/e18_adv.log` |
| Reverse-triangle reference depth (cellA) | ratio 0.74–0.99 for P ≤ 16 | `S/e24.log` |
| Exact C_B split with \|S_B\|² dropped (cellB) | 0.93–0.97 of target, deep pairs in gaps | `S/e24b.log` |
| Fejér lobe q_min·T, δ ∈ {1/16, 1/8, 1/4} | ratios 0.70–0.998 at P = 3–12 | `S/e23.log` |
| q·Fejér lobe, fresh pre-registration | min [bound − target] = −7.5 (P = 5) to −55.5 (P = 32), sparse chains | `S/e25_free.log` |
| Combined partition of unity, global c_* | ≈ −1e101 at every P | `S/e28_free.log` |
| Combined partition, pointwise-optimal c | −2.3 to −36.7 at P ≥ 8 | `S/e28_freediag.log`, `S/e28b.log` |
| θ-split with depth classes (Δ₀ = 0.25) | negative at every P ≥ 5 (to −1e104); diagnostic too | `S/e29_primary.log`, `S/e29_diag.log` |
| Same, depths capped at 3 | −4e13 to −2.3e14; diagnostic −5e12 to −7e13 | `S/e30_primary.log`, `S/e30_diag.log` |
| Positions-only dual D(s) | certified negative at a = 0.9, P = 12 (−0.16) and e23 P = 12–32 (−5.4 to −108.6) | `S/e32d.log` |
| W transplant, r ≤ 12 (P 24 → 48) | loss 3.1e3 to 5.6e6 | `S/e35.log` |
| W transplant, r ∈ {16, 20, 24} (P 64 → 128) | hard D from −1.4e4 to −3.5e5 | `S/e36.log` |
| Endpoint lemma (depth minimum at y = 0.8 or 3) | 440 pairs with an interior minimum, at y ≈ 2.5–2.93; dips ≤ 0.143 positions-only, ≤ 0.54 D_K | `S/e37.log`, `S/e37b.log` |

For the endpoint lemma, of the mechanism: B_{y'}/B_y is nondecreasing in α (pencil: x ↦ x·coth(cx) increases), but g_p has
4 to 213 sign changes, not ≤ 1.

## 5. Open conditions

- **Covering and locality of the dual witness.** For QP-optimal witnesses this is refuted at the current stiffness:
  - transplants fail (`S/e35.log`, `S/e36.log`);
  - the response of w* to one label flip is ~1e3 at every distance (`S/e35.log`);
  - the witness interior is not converged in P: the median is 0.0170 at P = 64 against 0.0002 at P = 128 for a = 0.6
    (`S/e36.log`).
- **Endpoint lemma (am-cert condition 11).** Refuted as stated. The weaker observation min_y φ_p ≥ min(endpoints) − 0.6 holds
  on the tested witnesses only. Certifying it needs interval bisection in y ∈ [2.4, 3].
- **Robust dual** (maximise the minimum slack, regularise w, or lower the top depth to reduce the e^{4π·y_max} stiffness).
  Untested.
- **D_K over all labellings.** Needs a binary-label chain search. Not built.
- **End positivity (E).** Q_pp ≥ 0 on lattices under every depth profile. Not proved. The e31b value ≈ +15 (`S/e31b.log`) is a
  local minimum, NOT a global one: with deeper interiors, e42c reaches ≤ +23.0 at a = 0.90 and ≤ +103.7 at a = 0.95 at
  P = 256 (not converged; `S/e42c_0.90_256.log`, `S/e42c_0.95_256.log`). At a = 0.99 the converged P = 256 minimum is +946.7 dense
  (+948.0 exact-quadrature, `S/e43b_a0.99.log`), and P ≥ 512 is unresolved (`S/e42_pp099.log`, `S/e43b_a*.log`).
  - **In end-functional form (E_∞: inf E_end ≥ 0), this is FALSE for shallow ends.** E_end < 0 down to ≈ −0.21 (§3).
  - It does not decide (1′): every mirrored chain stays positive (§3, minimum +0.592).
  - Candidate lemma shape, NOT proved: on lattices with a < 1, (1′) ≥ τ(a)·P − 2|E_end(L)| + (decoupling error).
    - Candidate target: sup_L |E_end(L)| ≤ C(a) with C(a) finite. With that, (1′) > 0 for P > 2C(a)/τ(a), and the remaining
      finite P is a compact check. Not established: at a = 0.99 the free-end |E_end| still grows through L = 400.
    - Observed |E_end| is small and sublinear in L: ≈ L^0.7 at a = 0.99, with doubling ratios 1.80, 1.61, 1.39; flat at
      a = 0.90.
    - The thinnest corner is a → 1⁻, where τ(0.999) = 0.0069 and τ(1) = 0.0055.
  - Pencil (Riemann–Lebesgue): a fixed smooth ramp stretched over L sites gives E_end → E_const(y_0) ≥ 0. The minima below that
    value come from finite-length interference, through the cross term 2c_0·Re Σ_{p≥1} Δc_p z^p.
- **Lemma SL.** The sign of the depth-difference part of C_B.
- **Small P = 3, 4.** A design exists (decoupling induction, a certified compact core, deepest-pair dominance as y → ∞). Not
  built.
