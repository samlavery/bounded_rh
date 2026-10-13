#!/usr/bin/env python3
"""Generate the AM seven-point (Q = 6) copies of the eight-point engine in bench/eight for the AT7 certificate (typh's
window, layer bench/window/rootTW): gen7at.py (instance; from gen8z), gen7mat.py (minorant leaf; from gen8mz),
gen_cover7at.py (cover and of_check; from gen_cover8), make7at.py (sizing and emission; from make8z).  The AM
substitutions are am-cert's (bench/window/amg/port8.py): the AM window bound 1/4 (`AMW.Cert.wfun_window`), the amk
kernel, modules AMW/{NAME}Inst + AMW/{NAME}Data in AMROOT with `{NAME}_cert_full` (amg/make8am_tail.txt).  Sources are
read only; the sizer is size7at.py (the n = 7 AM sizer with the two-grid tangents, MINR, MAXD)."""
import os
H = os.path.dirname(os.path.abspath(__file__)); E = os.path.join(H, ".."); AMG = os.path.join(H, "..", "..", "window", "amg")
def port(src, dst, reps, head=""):
    s = open(os.path.join(E, src)).read()
    for old, new in reps:
        assert s.count(old) == 1, (src, old[:70], s.count(old)); s = s.replace(old, new)
    open(os.path.join(H, dst), "w").write(head + s)
port("gen_cover8.py", "gen_cover7at.py", [
    ("(hwin : cN * 100 ≤ 19 * {min(aN[pairs.index((r, r+1))] for r in range(Q))})", "(hwin : cN * 4 ≤ {min(aN[pairs.index((r, r+1))] for r in range(Q))})"),
    ("      linear_combination (1 / 100 : ℝ) * hq + hm", "      linear_combination (1 / 4 : ℝ) * hq + hm"),
], head="# (AM seven-point copy of bench/eight/gen_cover8.py by port7at.py: window bound 1/4, AMW.Cert.wfun_window)\n")
port("gen8z.py", "gen7at.py", [
    ("\nQ = 7\n", "\nQ = 6\n"),
    ('os.path.join(HERE, "gen_cover8.py")', 'os.path.join(HERE, "gen_cover7at.py")'),
    ("from gen8mz import mleaf_defs, mleaf_proofs", "from gen7mat import mleaf_defs, mleaf_proofs"),
], head="# (AM seven-point copy of bench/eight/gen8z.py by port7at.py: Q = 6, cover gen_cover7at, leaf gen7mat)\n")
port("gen8mz.py", "gen7mat.py", [
    ("from gen7n import Q, PAIRS", "from gen7at import Q, PAIRS"),
], head="# (AM seven-point copy of bench/eight/gen8mz.py by port7at.py: names from gen7at, Q = 6)\n")
mk = open(os.path.join(E, "make8z.py")).read()
reps = [
    ('HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))',
     'HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "window", os.environ.get("AMROOT", "rootTW"), "AMW"))'),
    ('sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "mvt"))\nimport size7s\nfrom size7s import',
     'sys.path.insert(0, os.path.join(HERE, "..", "..", "mvt")); sys.path.insert(0, HERE)\nimport size7at as size7s\nfrom size7at import'),
    ("from gen8z import checker", "from gen7at import checker"),
    ("from w2cell import conv_ok, chain as w2chain", "from amk import conv_ok, chain as w2chain"),
    ("from w1cell import fP, fM", "from amk import fP, fM"),
    ("from gen8mz import JB", "from gen7mat import JB"),
]
for old, new in reps:
    assert mk.count(old) == 1, ("make8z", old[:70], mk.count(old)); mk = mk.replace(old, new)
i = mk.index('open(os.path.join(ROOT, f"data_{NAME}.lean"), "w", encoding="utf-8").write(data)')
j = mk.index('print(f"[{NAME}] delta={DELTA} cN={cN} leaves={len(leaves)}')
TAIL = open(os.path.join(AMG, "make8am_tail.txt")).read()
mk = mk[:i] + TAIL + mk[j:]
open(os.path.join(H, "make7at.py"), "w").write("# (AM seven-point copy of bench/eight/make8z.py by port7at.py: amk kernel, sizer size7at; modules AMW/{NAME}Inst, AMW/{NAME}Data in AMROOT (default rootTW))\n" + mk)
print("ported")
