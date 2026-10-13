"""Build root/AMW/CEngine.lean: the seven-point engine cores (pyramid oracle, derivative pair pyramid, point table,
slope test, convex regions) with the Montgomery–Taylor cell code removed and every reference resolved by the AM
facade (AMW/CFacade.lean).  Sources (read only): bench/pyr/PyrCheck.lean, bench/mvt/MvtDefs.lean,
bench/mvt/MvtCore.lean, bench/seven/SlopeCore.lean, bench/seven/ConvCore.lean (mvt-engine; pyramid adapted from
five-point-pyramid-2 by typh, basins after six-point-convex-basins-2 by typh, Apache-2.0)."""
import os, re
B = os.path.expanduser("~/work/riemann-submission/bench")
OUT = os.path.expanduser("~/work/riemann-submission/bench/window/root/AMW/CEngine.lean")

def between(s, a, b):
    i = s.index(a); j = s.index(b, i)
    return s[i + len(a):j]

pyr = open(f"{B}/pyr/PyrCheck.lean").read()
pyr = pyr[pyr.index("\n") + 1:]                       # drop `import PyrBase`
defs = between(open(f"{B}/mvt/MvtDefs.lean").read(), "-- MVTDEFS-BEGIN\n", "-- MVTDEFS-END")
core = between(open(f"{B}/mvt/MvtCore.lean").read(), "-- MVTPROOFS-BEGIN\n", "-- MVTPROOFS-END")
slope = between(open(f"{B}/seven/SlopeCore.lean").read(), "-- SLOPE-BEGIN\n", "-- SLOPE-END").replace("-- SLOPEDEFS-END\n", "")
conv = between(open(f"{B}/seven/ConvCore.lean").read(), "-- CONV-BEGIN\n", "-- CONV-END").replace("-- CONVDEFS-END\n", "")

# MvtDefs: the Montgomery–Taylor derivative cell (section MvtCells) is supplied by the facade
i = defs.index("section MvtCells"); j = defs.index("end MvtCells") + len("end MvtCells")
defs = defs[:i] + defs[j:]
# MvtCore: the first block (derivative of the MT closed form, interval lemmas, cellN_trig, cellD_sound)
i = core.index("namespace Zeta23Ext.Bridge.ThreePoint\n"); j = core.index("end Zeta23Ext.Bridge.ThreePoint\n\nend\n")
core = core[:i] + core[j + len("end Zeta23Ext.Bridge.ThreePoint\n\nend\n"):]
core = core.replace("noncomputable section\n\nopen Real\n\n", "", 1)
# ConvCore: the MT convexity cell (G2I, CellN.N2I/P2I/convOk) and its proof; keep `tangent_le`
i = conv.index("namespace Zeta23Ext.Bridge.ThreePoint\n"); j = conv.index("end Zeta23Ext.Bridge.ThreePoint\n", i)
conv = conv[:i] + conv[j + len("end Zeta23Ext.Bridge.ThreePoint\n"):]
i = conv.index("/-! ### the second derivative of `wfun` -/"); j = conv.index("/-! ### the tangent minorant on a convex range -/")
conv = conv[:i] + conv[j:]

body = "\n".join([pyr, defs, core, slope, conv])
body = body.replace("Zeta23Ext.Bridge.ThreePoint", "AMW.Cert")
head = """import AMW.CFacade

/-! ###### AM seven-point engine cores (stage G)

The pyramid oracle, the derivative pair pyramid, the point table, the slope test and the convex regions of the
seven-point engine (mvt-engine; pyramid adapted from five-point-pyramid-2 by typh, convex basins after
six-point-convex-basins-2 by typh, Apache-2.0), with the cell evaluator of the AM kernel behind `AMW/CFacade`. -/
"""
open(OUT, "w").write(head + body)
print(len(head + body), "bytes")
