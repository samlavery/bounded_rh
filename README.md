# bounded_rh: riemannzeta.fun / Riemann.fail critical-line submissions

Working directory of Samuel Lavery (github: samlavery) and his agent team (bridge-port, am-cert, mvt-engine,
window-scope) for the riemannzeta.fun critical-line proportion board. Apache-2.0, as all board submissions are; the
notices of every upstream author are kept in the files that carry their work.

## Accepted board entries
- attempt-020: re-optimised eight-point certificate on R. Arun Chandru's master-of-puppets2, κ = 0.6735479979
  (`bench/arun/UPLOAD_PC8R2.lean`).
- attempt-021: nine-point certificate with an n-generic counting chain, κ = 166950417639218487/247859045000000000
  = 0.6735700028 (`bench/arun/UPLOAD_PC9Q5.lean`, sha256 01128ffe…3749f60).
- Earlier entries attempt-002 … attempt-016: see `SUBMISSION.md`.

## Layout
- `SUBMISSION.md`: running log of every campaign, decision, measurement and correction.
- `bench/`: certificate engines, generators, sizers, Lean modules and build/stage logs.
  - `bench/arun/`: the eight- and nine-point campaigns on the Gram-defect chain; `cert/n9/ANATOMY.md` and
    `est/ESTIMATE_STATE.md` hold the pre-registered rounds.
  - `bench/specroot_*/`: private-check roots (candidate sources and build/replay logs).
- `ROUTE3*.md`: the route-3 study (third and fourth trace moments as new arithmetic input), with refutation specs
  in `ROUTE3_A2.md` §10 and `ROUTE3_B1.md`.

## Not included (see `.gitignore`)
- Build artefacts (`*.olean`, `*.ilean`, `.lake/`), sizer dumps (`*.pkl`), kernel exports (`*.ndjson`) and numeric
  caches (`*.npz`). All are regenerable.
- Third-party repositories used by the pipeline:
  - `zeta23/`: https://github.com/anthropics/zeta-23-lean @ 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
  - `tools/nanoda/`: https://github.com/ammkrn/nanoda_lib.git @ 418320295890faed83a96fd97907b12a3b6728c2
  - `tools/comparator/`: https://github.com/leanprover/comparator.git @ 273294467ce06429e6667ece7f5699f8678c9f4e
- Copies of published papers (`route3_refs/`, `*.pdf`); the route-3 notes cite them by reference.
