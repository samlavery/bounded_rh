# D track, Lean state (bridge-port, 2026-10-08; per-zero repair 2026-10-09)

Every theorem below compiles in `rootR8f/AMW`.
- Axioms: exactly `[propext, Classical.choice, Quot.sound]` (checked in `DEAx.lean`, `DER8Ax.lean`, `DEPSqAx.lean`).
- No `sorry`, no `native_decide`, no new `axiom`.
- One option is set: `online_at_T` carries `set_option maxHeartbeats 800000`.

## 2026-10-09: the hypothesis now uses per-zero weights (`DEPSq`)

**Why.** `LemmaPObj` charges `g₀ Σ_t M_T(t)²` with the zeros grouped by ordinate (`ordSq`), so a multiplicity-m
off-line zero with its reflection is charged `g₀(2m)²`. In the periodic model of Lemma P that form fails:
- Configuration: two such stacks at depth 0.8, joined by a chain of six deeper simple pairs.
- E(Z) − F_C(D(Z)) = +4.2 (m = 10), −54 (m = 12), −207 (m = 16), −1051 (m = 32).
- The deficit is stable in the period N (192 to 384), so a positive density of these clusters violates the
  `ordSq` form.
- Script and logs: `bench/window/sat9/e15_exact_mult.py`, `e15_Nscan.log`, `e15_thresh.log`.
- The numerical model (`band1/lemmaP.py`) counts each off-line pair as its own double, and there the same
  configurations are positive (+1694 at m = 16, +6809 at m = 32). The two conventions differ by exactly
  8g(0)(m² − m).

**The repair** (`DEPSq.lean`). Each zero carries `w(ρ) = m_ρ²` on the line and `2m_ρ` off it, and
`pSq Z T = Σ_ρ w(ρ)`.

| theorem | content |
|---|---|
| `Zeta23Ext.Bridge.pSq_ge` | 2N ≤ pSq + N₀ˢ (term by term; unconditional) |
| `Zeta23Ext.Bridge.pSq_le_ordSq` | pSq ≤ ordSq (an off-line class contains the reflection) |
| `Zeta23Ext.Bridge.lemmaPObjZ_of_lemmaPObj` | `LemmaPObj Z h0 g0 → 0 ≤ g0 → LemmaPObjZ Z h0 g0` (the new hypothesis is weaker) |
| `Zeta23Ext.Bridge.pSq_eq_of_online` | on an on-line window pSq = ordSq |
| `Zeta23Ext.Bridge.defectEnergyS_of_lemmaPZ` | as `defectEnergyS_of_lemmaP`, from `LemmaPObjZ` |
| `Zeta23Ext.Bridge.lemmaPObjZ_online`, `AMW.lemmaPObjZ_R8_online` | the on-line instances (conditional on `hon`) |
| `AMW.am_dyadic_R8_ratZ`, `AMW.am_cumulative_R8_ratZ` | κ = 6759644/10⁷, unchanged, under `LemmaPObjZ` |

**The remaining hypothesis is now**
`Zeta23Ext.Bridge.LemmaPObjZ zetaZeroConfig (AMW.DE.qfAM 0 - AMW.DE.cR8.y 0) (AMW.DE.gPL AMW.DE.cR8 0)`.
It has the form below with `pSq` in place of `ordSq`. The `ordSq` versions (`LemmaPObj`, `am_dyadic_R8_rat`, …)
are kept unchanged and imply the new ones.

## The ordSq hypothesis (kept; superseded by `LemmaPObjZ` above)

```lean
Zeta23Ext.Bridge.LemmaPObj zetaZeroConfig (AMW.DE.qfAM 0 - AMW.DE.cR8.y 0) (AMW.DE.gPL AMW.DE.cR8 0)
-- where
LemmaPObj Z h0 g0 := ∀ ε > 0, ∀ᶠ T in atTop,
  h0 * N(T,2T) + g0 * ordSq Z T - ε * N(T,2T) ≤ frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
-- ordSq Z T = Σ_t M_T(t)²: zeros of (T,2T] grouped by ordinate (an off-line pair is one class)
```

- This is Lemma P on the Lean object: the count-only form of the dip certificate, at R8's constants.
- It is the only hypothesis of the final theorems.
- Proving it for `zetaZeroConfig` is Phase 2 and waits on window-scope's shallow-depth rigidity lemma.

## Final theorems (`DER8K`)

| theorem | hypotheses | conclusion |
|---|---|---|
| `AMW.am_dyadic_R8_rat` | `LemmaPObj …` | `∀ε>0 ∃T₀ ∀T≥T₀, (0.6759644 − ε)·Ncount T 2T ≤ N0star T 2T` |
| `AMW.am_cumulative_R8_rat` | `LemmaPObj …` | the same for `Ncount 0 T`, `N0star 0 T` |
| `AMW.kappa_R8_floor` | none | `0.6759644 ≤ 1 − (e∞ + σ/2)/(g(0)/2)` |

How the floor is built:
- `eInfDE_eq`: e∞ = (2 − H_W − e₀)/2.
- `HW_ge` (Floor): H_W ≥ 0.67216841.
- `qfAM_zero_ge` (mvt-engine, `DEQfZero`): e₀ = qf(0) ≥ 1.0082637.
- The exact value is 0.6759645.

## The chain

**Skeleton** (`DefectEnergy`, `DESlack`): `frobAz_le`, `defectEnergy_datum`, `DefectEnergyS`, `am_dyadic_defectS`, `am_cumulative_defectS`. No hypotheses beyond `PaperInputs` and the D-inequality.

**Interface** (`DEPInterface`):
- `ordSq_ge`: 2N ≤ ordSq + N₀ˢ, by reflection symmetry. Unconditional.
- `defectEnergyS_of_lemmaP (hP : LemmaPObj Z h0 g0) (0 ≤ g0) (e₀ ≤ h0+g0+σ) : DefectEnergyS Z (g0/2) (σ/2)`.
- `am_dyadic_lemmaP`, `am_cumulative_lemmaP`.

**Definitions** (`DEDefs`): `PLCert`, `ghat`, `certC`, `gPL`, `qfAM`, `CertGNonneg`, `CertHNonneg`, `ghat_seg`.

**Fourier** (`DEFourier`), all unconditional:
- `integral_tri_cos`;
- `integral_ghat_cos` (∫ĝ cos = gPL);
- `integral_qfAM_cos` (∫qf cos = wfunAM);
- `energy_eq_integral`.

**Density** (`DEDensity`): `density_lb`. If B ≥ 0 is continuous with compact support, κ = B̌ ≥ 0 and ∫κ = 1, then N²(∫_{−M}^{M}κ)²/∫ψ ≤ ∫B|S|².

**Certificate** (`DECert`): `cert_T_free (c) (hD) (hG : CertGNonneg c) (hH : CertHNonneg c)`. For finite real configurations in [0,W]: (ĥ(0) − ε)N²/(W+R) + g(0)Σm² ≤ Σ m m′ wfun.

**R8 data and checks**:
- `cR8` (am-cert, `DEData`), `certG_R8` (am-cert, `DESOSR8`), `ghat0_sub_g0_R8`.
- `certH_R8` (mvt-engine, `DEQfR8`).
- `cert_T_free_R8`.
- `qfAM_zero_eq_e0DE`, `one_le_qfAM_zero`, `gPL_zero_pos_R8`, `sigmaR8_eq` (σ = 12023728861/8796093022208).
- `e0DE_eq_R8`, `am_dyadic_R8`, `am_cumulative_R8` (`DER8`).

**On-line instance** (`DEObjA/B/C`, `DEObj`, `DEObjMain`):
- `lemmaPObj_online (Z) (H) (c) (hD) (hG) (hH) (y₀ < qf(0)) (hon : ∀ᶠ T, ∀ ρ ∈ Z.ZIprime T, ρ.re = 1/2) : LemmaPObj Z (qf(0) − y₀) (g(0))`.
- `AMW.lemmaPObj_R8_online (hon)`.
- These show the interface is inhabited. They are conditional on `hon` (window zeros on the line), not a proof for zeta.
- Pieces:
  - `frob_hat_Az_online`, `kernel_close_real`, `sum_sq_rank_one`;
  - `block_bound`, `sq_ge_of_close`, `sum_blocks_le`;
  - `N_le_short`, `bulkFin`/`edgeFin`, `sum_mult_le_bulk_add`, `sum_sq_le_bulk_add`, `ordSq_eq_of_online`;
  - `growth`, `final_algebra`, `online_at_T`.

## What Phase 2 must supply

`LemmaPObj zetaZeroConfig (qf(0) − y₀) (g(0))` for configurations that may contain off-line zeros.

- The on-line proof does not carry over unchanged. It uses `frob_hat_Az_online`, which writes ‖Â‖² as a sum of squares and needs every zero real. With off-line zeros, the matrix Â has a pair part (`hatQ`) and the expansion is no longer termwise nonnegative.
- The kernel comparison (`kernel_close_real`) is for real ordinates only.
- What is reusable: the block/count/growth layer, `cert_T_free`, and everything downstream of `LemmaPObj`.
- Since 2026-10-09 the target is `LemmaPObjZ` (per-zero weights). It is weaker than `LemmaPObj` and is the form the
  numerical model checks.

## Phase 2 math, deep pairs (pencil; not in Lean)

Notation (two-sided, ‖F‖²_q = ∫_{−1}^{1} q|F|²):
- P off-line pairs at ordinates s_p and depths y_p.
- c_p(α) = 2cosh(2παy_p) = 2 + B_p(α).
- S_A = Σ_p c_p e(αs_p), V = Σ_p e(αs_p), S_B = Σ_p B_p e(αs_p).
- Q_pp = ‖S_A‖² − 4‖V‖².
- T_g^pp = 4Σ_{p≠p'} g(s_p − s_p').
- h = K − g, with K(u) = ∫q cos(2παu).

Results:
- **Identity (exact).** Q_pp + T_g^pp = ‖S_A‖²_q − 4g(0)P − 4Σ_{p,p'} h(s_p − s_p').
- **|h(u)| ≤ h(0) = 1 − g(0) = 0.00957** for all real u, since ĥ ≥ 0.
- **Equal depths.** Q_pp = ∫q(B² + 4B)|V|² ≥ 0. For P = 2, pointwise ≥ (c₁ − c₂)².
- **Lemma LL (PROVED, pencil; checked by the lead).**
  - Scope: isolated clusters (P pairs with ordinates in an interval of length L and no other pairs), any depths y_p ≥ 0.
  - Statement: if P·(2δ·cos(2πδL)·Q̄(δ) − h(0)) ≥ g(0) for some δ ≤ 1/(4L), where Q̄(δ) = (1/2δ)∫_{−δ}^{δ} q, then
    Q_pp + T_g^pp ≥ 0.
  - Proof:
    - On |α| ≤ δ, |S_A|² − 4|V|² = |S_B|² + 4Σ_{p,p'} B_p cos(2πα(s_p − s_p')) ≥ 0, every term being ≥ 0.
    - |V|² ≥ P²·cos(2πδL).
    - So ‖S_A‖² ≥ 4P²·cos(2πδL)·∫_{−δ}^{δ} q.
    - Insert this into the identity, using |Σh| ≤ h(0)P².
  - Optimum: δL = 0.1369, which solves 2πx·tan(2πx) = 1.
  - Thresholds (Q̄ on the 6001-point grid; q is decreasing on [0, 1], so Q̄(δ) ≥ q(δ) also works):

    | P | 8 | 16 | 32 | 64 |
    |---|---|---|---|---|
    | L ≤ | 1.30 | 2.47 | 4.40 | 7.14 |

    For moderate P this is roughly P/L ≥ 5.5 + 0.054P.
  - It covers, in isolation, the stack families where Q_pp < 0 (bench/window/sat9/e9, e12).
- **Lemma SL (PROVED, pencil; exact).**
  - Setup:
    - For a₀ ∈ (0, 1] let T = (1 − |α|/a₀)₊ and κ = min_{|α|≤a₀} q/T². On the grid κ = 1.008 for a₀ ≤ 0.3.
    - Let Φ = FT(T²) ≥ 0, and let D_p = Σ_{p'} Φ(s_p − s_p') (local pair density at scale 1/a₀).
  - Statement: ‖S_A‖²_q ≥ 4κ·Σ_p D_p + C_B, where C_B = 4κ·Σ_{p,p'} ∫T²·B_p·cos(2πα(s_p − s_p')).
  - Tests (sat9/e22): SL alone exceeds the (1′) target on every dense test configuration, but not on the spacing-1
    lattice. C_B ≥ 0 in every test.
  - Not proved: the sign of C_B. Its leading term is −4κΣ_p y_p²·D''(s_p).
- **Not proved.** Q_pp + T_g^pp ≥ 0 for general configurations.
  - The adversarial minima (y ∈ [0.8, 3]) are ≥ +29.6 in total for P ≤ 24 (sat9/e19).
  - The margin sits in the DC lobe at α = 0, and the band edge is where the cancellation happens (sat9/e21).
  - What is missing: a sharp lobe estimate without the quarter-turn restriction, the sparse case (in-band comb
    peaks), and a localisation with a cross-term bound.
- **State after the relaxation rounds (2026-10-09; the θ-split was the last round).** Every pre-registered relaxation
  failed its adversarial test:
  - the q·Fejér lobe (e23, e25, e26);
  - the combined partition-of-unity bound (e28, e28b);
  - the θ-split with depth classes of width 0.25 (e29).
  - Complete pencil coverage: P ≤ 2; equal depths (any P); isolated dense clusters (LL).
  - Not covered:
    - moderate-density chains with unequal depths (binding; true minimum +29.6 at P = 12, ≈ 2.5 per pair);
    - sparse and hole chains (true ≥ +1.3e3);
    - large depth spread (true ≥ 1e20);
    - P = 3, 4 (true 57.0, 42.3).
  - The decision between a computer-assisted core and pausing (1′) is with the lead and Sam.
- **Focused core push (3 rounds, depths in [0.8, 3], 2026-10-09).**
  - Round 1: the capped θ-split FAILED.
    - Exact lattice-with-ends: Q_pp → C_end(a, y) = ½∫q(B² + 4B)/sin²(πaα) at equal depth.
    - The min over depth profiles on lattices is an end term ≈ +15 (sat9/e30, e31).
  - Round 2: the positions-only dual reduction D(s) (exact convex QP, two-sided certificate, sat9/e32d).
    - Certified PASS on lattices with a ≤ 0.8.
    - Certified FAIL at a = 0.9 (P = 12) and on the irregular minimisers (P ≥ 12).
  - Round 3: the depth-class reduction D_K, with α-profiled test functions W = V + Σ w_{n,j}·B_{ŷ_j}·e(αt_n) (sat9/e33).
    - It is positive on every configuration tested, already at K = 2 (loss ≤ 3.8, except 33.8 at a = 0.9, P = 48).
    - The loss is ≈ 0 at K = 4 on the irregular minimisers.
    - This covers the labellings tested only; certifying all labellings needs the binary-label chain DP.
  - Bulk margin, exact in the periodic model: for an exact lattice with a < 1, Q_pp's bulk part is ≥ 0, so the per-pair
    margin is τ(a) = 8Σ_k g(ka), which falls to 0.0055 at a = 1.
  - Regime-(A) witnesses W* are saved in sat9/e34_witness.json.

## Linear per-zero weights: `DEPLin` (am-cert, 2026-10-09)

**Why.** `LemmaPObjZ` (`DEPSq`) charges an on-line zero of multiplicity `m` the weight `m²`. That form is refuted
configuration-wise in the periodic model (window R8b). An on-line zero of multiplicity `M` flanked by shallow off-line
pairs gives `LP_pSq < 0`:
- `M ≥ 4` at `N = 64` (`M = 4`: −0.25);
- `M ≥ 5` at `N = 256` (`M = 4`: +0.0099; `M = 5`: −2.12; `M = 12`: −58).

Sources: bench/window/band1/round8_onmult_{a,b,c}.log (mp50 recheck: `M = 5` −3.198, `M = 6` −8.122) and
round9_lin_i{64,256}.log.

The count only needs `2N ≤ p + N₀ˢ`, and the linear weight meets it with equality. The linear weight is:
- `1` for a simple on-line zero;
- `2m` for any other zero.

In the same model, the pre-registered adversarial test gives min `LP_lin = +3.12` (`M = 3`, `N = 64`), growing like
`≈ 0.30·M²` up to `M = 48` (round9_lin_i64.log, round9_lin_largeM.log). Numerical strength; no Lean statement depends on
it.

**Theorems** (`rootR8f/AMW/DEPLin.lean`, imports `AMW.DEPSq`; `DEPSq` unchanged):

| theorem | statement |
|---|---|
| `Zeta23Ext.Bridge.wLin`, `pLin` | `wLin = 1` (on the line, `m = 1`), `2m` otherwise; `pLin Z T = Σ_{ρ ∈ winFin Z T} wLin` |
| `Zeta23Ext.Bridge.LemmaPObjL` | `LemmaPObjZ` with `pLin` in place of `pSq` (a hypothesis) |
| `pLin_add_N0s` | `pLin Z T + N₀ˢ(T, 2T) = 2·N(T, 2T)` (exact) |
| `pLin_ge` | `2N ≤ pLin + N₀ˢ` |
| `wLin_le_zWeight`, `pLin_le_pSq` | `pLin ≤ pSq` (`2m ≤ m²` for `m ≥ 2`) |
| `lemmaPObjL_of_lemmaPObjZ` | `LemmaPObjZ Z h₀ g₀ → 0 ≤ g₀ → LemmaPObjL Z h₀ g₀` |
| `lemmaPObjL_of_lemmaPObj` | the same from the ordinate-class `LemmaPObj` |
| `defectEnergyS_of_lemmaPL` | `LemmaPObjL → DefectEnergyS Z (g₀/2) (σ/2)` |
| `lemmaPObjL_online` | the on-line instance (hypothesis `hon`: window zeros on the line) |
| `AMW.am_dyadic_lemmaPL`, `AMW.am_cumulative_lemmaPL` | the board shape under `LemmaPObjL` |
| `AMW.am_dyadic_R8_ratL`, `AMW.am_cumulative_R8_ratL` | `κ = 6759644/10⁷` (unchanged), with sole hypothesis `LemmaPObjL zetaZeroConfig (qfAM 0 − cR8.y 0) (gPL cR8 0)` |
| `AMW.lemmaPObjL_R8_online` | from `lemmaPObjZ_R8_online` via the implication (conditional on `hon`) |

**Checks.**
- Axioms: all 13 theorems give `[propext, Classical.choice, Quot.sound]` (`DEPLinAx.lean`).
- No `sorry`, `axiom` or `native_decide`.
- Build: `leanr.sh rootR8f AMW/DEPLin` (`LEAN_NUM_THREADS=2 nice -n 10`). DEPLin compiles in 22 s, DEPLinAx in 20 s, both
  with no warnings.
