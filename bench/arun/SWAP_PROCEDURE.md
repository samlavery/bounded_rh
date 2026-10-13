# MOPX: certificate swap procedure (am-cert, 2026-10-10)

## Skeleton

`bench/arun/MOPX_skel.lean` is 1,718,796 B. It is built by `mk_skel.py` from `MOP_Solution.lean` plus `deps_mop_k.tsv`.
- Dead declarations are removed, using the dead set from the compiled olean. Attributed lemmas are kept.
- Non-notice comments are removed.
- Every copyright, license and attribution notice is kept verbatim: 20 notice blocks, and Arun's author block.
- Sam's copyright and NOTICE block and the Apache-2.0 §4(b) change notice sit before the imports. The change notice has
  the placeholders `@@W@@ @@B@@ @@C@@ @@KAPPA@@`.

Control: the skeleton with PC8C5BF still in it.
- Private root: `specroot_mopx`; record 6735015/10⁷, candidate 66812491/99194876.
- BUILD EXIT 0, with standard axioms on all three theorems; REPLAY EXIT 0. Export closure: 76,330 constants.
- Build 367 s, 2.956e12 instructions. Predicted board time 2,229 s (instruction-ratio model against PC8C5BF's actual
  2,319 s).

Swap points are marked by one-line `-- SWAP …` comments.

## What changes when a new certificate NAME drops in

| where | declarations / constants |
|---|---|
| certificate region (`-- SWAP BEGIN` … `-- SWAP END`) | `AMW.Cert.NAME` (instance: `cN`, `SIG`, `SA`, `G`, `Fg_G`, splits, `pc_spl_NAMEInst` macro), `AMW.Cert.NAMEData` (tables, `cert`), `AMW.Cert.NAME_G_rev / NAME_half / NAME_cert_full`, `RiemannFail.{aW8, bW8, W8, W8_B, W8_a_nonneg, W8_bmin, W8_capacity, W8_adm, Fw_W8, cert_AM}` |
| interface (names and types unchanged) | `RiemannFail.W8 : WCert 8`; `W8_adm : W8.Adm`; `W8_B : W8.B = B`; `cert_AM : ∀ g, (∀ i, 0 ≤ g i) → c ≤ Fw W8 g` |
| `Opeth.AMCounting` | `cFloor := c`, `pressureSum := B`, `proposedQ := κ` (`proposedQ_identity` is `norm_num`, so its text is unchanged) |
| `Opeth.AMFinal.actual_dyadic / actual_cumulative` | the κ literal in the statements |
| export wrapper | the κ literal in `am_export_candidate_exact` |
| change notice | `@@W@@`, `@@B@@`, `@@C@@`, `@@KAPPA@@` |

Unchanged:
- `AMW.HW_ge` (H⁻ = 67216841/10⁸);
- the Opeth matching / pinching / separated-spectrum chain;
- the certificate engine (`AMW.Cert.Pyr/PyrD/PCell/CellN`, `AMW.G`);
- all notices.

Side conditions checked by the script:
- c ≤ 1/64, needed by `AMMatching.close_pair_block_bound`;
- κ > 66812491/99194876, the current record, needed by `candidate_strict_improvement`.

κ = (H⁻ − B)/(1 − c), in lowest terms. With B = b/10⁸ and c = c'/10⁸: κ = (67216841 − b)/(10⁸ − c'), reduced. Other
denominators are handled exactly (`fractions.Fraction`).

## Steps

1. Assemble a single file FULL for NAME with our assembler (`window/tauint/assemble_am_tau.py … --final6 NAME --npts 8`,
   as in `run_n8.sh`; the √/edge options are not needed). FULL must contain `namespace AMW.Cert.NAME` …
   `end AMW.Cert.NAMEData`, the glue `NAME_cert_full`, and `RiemannFail` up to `cert_AM`.
   - CHECK: the engine text in FULL (`AMW.Cert.Pyr/PyrD/PCell/CellN`, `AMW.G`) is identical to the skeleton's. If the
     revalidated pipeline changed the engine, the engine must be swapped too; the markers do not cover that.
2. Run `python3 arun/swap_cert.py arun/MOPX_skel.lean FULL NAME "<weights id>" arun/MOPX_NAME.lean`.
   - It prints the bytes, B, c, κ and the spec numbers.
   - It asserts c ≤ 1/64 and κ > the record.
   - It carries over the notice blocks inside the region.
3. Run `bash pyr/private_check_rec.sh arun/MOPX_NAME.lean CandMOPXNAME KNUM KDEN 66812491 99194876 specroot_mopxname`.
   It must give BUILD EXIT 0, standard axioms on the three theorems, and REPLAY EXIT 0.
4. Run `bash nanoda/stage.sh CandMOPXNAME $PWD/specroot_mopxname`, then the instruction-ratio prediction against
   PC8C5BF (actual 2,319 s). Gates:
   - size ≤ 2,000,000 B;
   - predicted time ≤ the lead's gate (2,600 s soft);
   - nanoda RSS ≤ 7.5 GB.
5. Optional, if bytes are tight: re-strip the swapped file. FULL's `RiemannFail` carries a few lemmas this chain does not
   use, e.g. `W8_hsym` and the edge `sumE*` lemmas. To re-strip, compile once, dump the deps (`DepMOP.lean` pattern),
   then run `mk_skel.py` on it. `mk_skel.py` inserts our header blocks, so either remove them from its input first or
   drop its duplicate insertion.

No upload: uploads are Sam's.

## n-point skeleton MOPX9 (2026-10-10)

`arun/MOPX9_skel.lean` is 1,719,833 B. It is built by `mk_skel9.py` from `MOPX_skel.lean` and the compiled-and-tested
`Gen9Test.lean`.
- Arun's eight-point counting layer is replaced by the n-generic `OpethN` layer:
  - `card_near_le_k`;
  - `band_close_n` (error 4(n−1)δ per point);
  - `pressure_le_n`, `remainder_bound_n`, `block_remainder_bound_n` (boundary (n−1)c);
  - `matching_defect_bound_n`;
  - `Counting.defect_to_dyadic` (κ = (H⁻ − B)/(1 − c), δ = min(c/(8(n−1)), (1−c)ε/C), C = 4(n−1)+2+c+B);
  - `ActualDefect.actual_dyadic / actual_cumulative` (any admissible `WCert n`, c ∈ (0, 1/64]).
- All 20 notice blocks are kept, and the change notice records the generalisation.
- Control at n = 8 with PC8C5BF (`specroot_mopx9`): BUILD EXIT 0, standard axioms, REPLAY EXIT 0, stages OK, predicted
  2,234 s.

Swap for an n-point certificate:

    python3 arun/swap_cert9.py arun/MOPX9_skel.lean FULL NAME "<weights id>" arun/MOPX9_NAME.lean

- FULL: the assembler output with `--final6 NAME --npts N`. It defines `RiemannFail.W<N> : WCert <N>`, `W<N>_adm`,
  `W<N>_B` and `cert_AM`.
- The tool reads N, B and c from FULL and regenerates the `Opeth.AMFinal` instantiation for n = N. It also replaces
  the export κ literal and fills the change notice.
- Self-test with PC8C5BF at n = 8: the regenerated final block is byte-identical to the skeleton's.
- Then steps 3–4 as above: private check with record 66812491/99194876, then the stages.
