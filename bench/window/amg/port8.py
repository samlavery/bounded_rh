"""Regenerate the AM copies of mvt-engine's eight-point engine (bench/eight: size7s, gen8z, gen8mz, gen_cover8, make8z) as
amg/size8am.py, gen8am.py, gen8mam.py, gen_cover8am.py, make8am.py: AM kernel (amk, AMWIN), AM window bound 1/4, modules
AMW/{NAME}Inst + AMW/{NAME}Data in AMROOT.  Sources are read only; rerun after mvt-engine updates them."""
import os
E = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "eight")
H = os.path.dirname(os.path.abspath(__file__))
def port(src, dst, reps, head=""):
    s = open(os.path.join(E, src)).read()
    for old, new in reps:
        assert s.count(old) == 1, (src, old[:70], s.count(old)); s = s.replace(old, new)
    open(os.path.join(H, dst), "w").write(head + s)
PHASE1 = '''from size_pyr import SA, SC, QUARTER, WFRAC, X0
from pyr_table import Pyr
import amk
from amk import WZ, SW, fP, fM, U1, KU1
from size_m import PyrF
from amk import w as wf, w1 as w1f
import sevenw as _sw
_sw.w = amk.w; _sw.w1 = amk.w1; _sw.w2 = amk.w2
def phase1(cN, aAdjN, S):
    """per-gap cover of [1/2, S] (units 2^-15), as size_pyr.phase1 with the AM cell bound and float w"""
    roots = []; a = X0
    while a < S:
        b = min(a + QUARTER, S); roots.append((a, b)); a = b
    clear, bad = [], []
    stack = list(reversed(roots))
    while stack:
        l, u = stack.pop()
        if cN * SW <= aAdjN * WZ(l, u): clear.append((l, u)); continue
        wm = float(wf(np.linspace(l / SC, u / SC, 121)).min())
        if wm * aAdjN < cN and (u - l) <= SC // 64: bad.append((l, u)); continue
        if u - l <= SC // 4096: bad.append((l, u)); continue
        m = (l + u) // 2; stack.append((m, u)); stack.append((l, m))
    bad.sort(); merged = []
    for iv in bad:
        if merged and merged[-1][1] == iv[0]: merged[-1] = (merged[-1][0], iv[1])
        else: merged.append(iv)
    clear.sort()
    return clear, merged
'''
port("size7s.py", "size8am.py", [
    ('for p in (HERE, os.path.join(HERE, "..", "pyr"), os.path.join(HERE, "..", "mvt")):',
     'for p in (HERE, os.path.join(HERE, "..", "..", "pyr"), os.path.join(HERE, "..", "..", "mvt"), os.path.join(HERE, "..", "..", "eight")):'),
    ('from size_pyr import phase1, SA, SC, QUARTER, WFRAC\nfrom pyr_table import Pyr\nfrom wz import WZ, SW\nfrom w1cell import fP, fM, U1, KU1\nfrom size_m import PyrF\nfrom sevenw import w as wf, w1 as w1f\n', PHASE1),
], head="# (AM copy of bench/eight/size7s.py, mvt-engine, by port8.py: kernel swapped to amk (AMWIN); AM phase1; nothing else changed)\n")
port("gen_cover8.py", "gen_cover8am.py", [
    ("(hwin : cN * 100 ≤ 19 * {min(aN[pairs.index((r, r+1))] for r in range(Q))})", "(hwin : cN * 4 ≤ {min(aN[pairs.index((r, r+1))] for r in range(Q))})"),
    ("      linear_combination (1 / 100 : ℝ) * hq + hm", "      linear_combination (1 / 4 : ℝ) * hq + hm"),
], head="# (AM copy of bench/eight/gen_cover8.py, mvt-engine, by port8.py: window bound 1/4, AMW.Cert.wfun_window)\n")
port("gen8z.py", "gen8am.py", [
    ('os.path.join(HERE, "gen_cover8.py")', 'os.path.join(HERE, "gen_cover8am.py")'),
    ("from gen8mz import mleaf_defs, mleaf_proofs", "from gen8mam import mleaf_defs, mleaf_proofs"),
], head="# (AM copy of bench/eight/gen8z.py, mvt-engine, by port8.py: cover gen_cover8am, leaf gen8mam)\n")
port("gen8mz.py", "gen8mam.py", [], head="# (AM copy of bench/eight/gen8mz.py, mvt-engine, by port8.py; unchanged)\n")
mk = open(os.path.join(E, "make8z.py")).read()
reps = [
    ('HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))',
     'HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", os.environ.get("AMROOT", "rootR8"), "AMW"))'),
    ('sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "mvt"))\nimport size7s\nfrom size7s import',
     'sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "..", "mvt"))\nimport size8am as size7s\nfrom size8am import'),
    ("from gen8z import checker", "from gen8am import checker"),
    ("from w2cell import conv_ok, chain as w2chain", "from amk import conv_ok, chain as w2chain"),
    ("from w1cell import fP, fM", "from amk import fP, fM"),
]
for old, new in reps:
    assert mk.count(old) == 1, ("make8z", old[:70], mk.count(old)); mk = mk.replace(old, new)
mk = mk.replace("from gen8mz import JB", "from gen8mam import JB")
i = mk.index('open(os.path.join(ROOT, f"data_{NAME}.lean"), "w", encoding="utf-8").write(data)')
j = mk.index('print(f"[{NAME}] delta={DELTA} cN={cN} leaves={len(leaves)}')
TAIL = open(os.path.join(H, "make8am_tail.txt")).read()
mk = mk[:i] + TAIL + mk[j:]
open(os.path.join(H, "make8am.py"), "w").write("# (AM copy of bench/eight/make8z.py, mvt-engine, by port8.py: amk kernel; modules AMW/{NAME}Inst, AMW/{NAME}Data in AMROOT)\n" + mk)
print("ported")
