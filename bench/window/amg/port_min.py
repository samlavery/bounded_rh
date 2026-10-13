"""Build root/AMW/CMin.lean: mvt-engine's per-term minorant core (bench/psd/MinCore.lean, the MIN block: extended
tangents `tcheck`/`tangent_cert`, the convex-combination term `mterm_ok`, the gap bound `gap_lo`) on the AM engine
(AMW/CEngine), by renaming.  Source read only."""
import os
B = os.path.expanduser("~/work/riemann-submission/bench")
OUT = os.path.join(B, "window", "root", "AMW", "CMin.lean")
src = open(f"{B}/psd/MinCore.lean").read()
i = src.index("-- MIN-BEGIN\n"); j = src.index("-- MIN-END")
body = src[i + len("-- MIN-BEGIN\n"):j].replace("-- MINDEFS-END\n", "")
body = body.replace("Zeta23Ext.Bridge.ThreePoint", "AMW.Cert")
head = """import AMW.CEngine

/-! ###### per-term minorants for the AM certificate (stage G): mvt-engine's MinCore (extended tangents at grid points,
certified once per pair term, combined convexly), on the AM engine cores. ###### -/
"""
open(OUT, "w").write(head + body)
print(len(head + body), "bytes")
