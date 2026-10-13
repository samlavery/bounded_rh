# (AM copy of bench/eight/make8z.py, mvt-engine, by port8.py: amk kernel; modules AMW/{NAME}Inst, AMW/{NAME}Data in AMROOT)
#!/usr/bin/env python3
"""Size and emit the weighted (Q+1)-point certificate (Q gaps) with two leaf kinds: zero-order leaves and minorant
leaves (per-term certified affine minorants, payload in the walk word); no slope leaves, no basins.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Usage: make8z.py WEIGHTS.npz DELTA NAME [CH]
Writes in the workspace root: data_<NAME>.lean, checker_<NAME>.lean, <NAME>_params.txt, <NAME>_order.txt.
Every leaf is re-verified on the built tables (integer-faithful replicas of the Lean tests)."""
import os, sys, itertools, time
import numpy as np
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", os.environ.get("AMROOT", "rootR8"), "AMW"))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "..", "mvt"))
import size8am as size7s
from size8am import run, Q, PAIRS, NP, TS, SC, U, U1, KU1, RU, M32
from emit_tables import PairTable
def dispatch(name, consts):
    """`def name (j : ℕ) : ℕ` returning consts[j] (a dict j -> constant name), 0 elsewhere (`dsel` / `dpk` tree)"""
    L = []; js = sorted(consts)
    if not js: return [f"def {name} (j : ℕ) : ℕ := 0"]
    def sub(a, b):
        if b - a == 1: return f"(dpk j {js[a]} {consts[js[a]]})"
        return f"({name}s{a}_{b} j)"
    def mk(a, b):
        if b - a == 1: return
        m = (a + b) // 2; mk(a, m); mk(m, b)
        L.append(f"def {name}s{a}_{b} (j : ℕ) : ℕ := dsel j {js[m]} {sub(a, m)} {sub(m, b)}")
    mk(0, len(js))
    L.append(f"def {name} (j : ℕ) : ℕ := {sub(0, len(js))}")
    return L
def pyr_consts(P, top, bk):
    L = [f"def {top} : ℕ := {P.TOPN}"]
    for j in sorted(P.BKN): L.append(f"def {bk}_{j} : ℕ := {P.BKN[j]}")
    L += dispatch(bk, {j: f"{bk}_{j}" for j in P.BKN})
    return "\n".join(L) + "\n"
pair_consts = pyr_consts
from gen8am import checker
from gen8mam import JB
WF, DELTA, NAME = sys.argv[1], float(sys.argv[2]), sys.argv[3]
CH = int(sys.argv[4]) if len(sys.argv) > 4 else 1500
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
JCQ = 8
d = np.load(os.path.join(HERE, WF)); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
SA = 10**8
gmin = float(d['vals'][0]) * SA
cN = int(gmin * (1 - DELTA))
CSU = cN * SC * U
t0 = time.time()
# ---- convex regions of w: maximal intervals of 64-unit cells passing the convexity cell test, each certified by a
# chain of cells (cut at the half-integers); an expanded term whose range lies in one needs no charge ----
from amk import conv_ok, chain as w2chain
REGS = []
_lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]
_s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None:
        c_ = w2chain(_s, x_); assert c_ is not None; REGS.append((_s, x_, c_)); _s = None
print(f"[{NAME}] {len(REGS)} convex regions, {sum(len(c) for *_, c in REGS)} chain cells", flush=True)
def region_of(lo, hi):
    for (a_, b_, _) in REGS:
        if a_ <= lo and hi <= b_: return (a_, b_)
    return None
DPE = int(os.environ.get("DPE", "6")); DFUEL = int(os.environ.get("DFUEL", "14"))
DLO = int(os.environ.get("DLO", "5")); DHI = int(os.environ.get("DHI", "6")); XD = 81920
DDENSE = os.environ.get("DDENSE", "1") == "1"
r = run(cN, aN, bN, JCQ=JCQ, basins=(), WMIN=int(os.environ.get("WMIN", "6")), PED=DPE, DFUEL=DFUEL,
        DLO=DLO if DDENSE else None, DHI=DHI if DDENSE else None, XD=XD, centers=(), CRAD=0, MTEST=3,
        regions=[(a_, b_) for (a_, b_, _) in REGS])
assert r is not None and r["bad"] == 0
P, PP, PM, built, sint, dec, sfloat = r["P"], r["PP"], r["PM"], r["built"], r["sint"], r["dec"], r["sfloat"]
print(f"[{NAME}] sizing: {r['nleaves']} leaves (Z {r['nZ']}, S {r['nS']}, basin {r['nB']}); points {r['stats']['points']} "
      f"({r['stats']['ptcells']} point cells) ({time.time()-t0:.0f}s)", flush=True)
CSU = cN * SC * U
# extend the tables with the minorant reads, rebuild, re-verify
qz_all, qd_all, qz1_all = set(), set(), set()
leaves = r["leaves"]
def iv(box): return [(sum(box[k][0] for k in range(i, j)), sum(box[k][1] for k in range(i, j))) for (i, j) in PAIRS]
for _, box, kind, pay in leaves:
    I = iv(box)
    if kind == 1: qz_all.update(I)
    elif kind == 6:
        Q_ = {'z': set(), 'd': set(), 'p': set()}
        assert r["meval"](box, pay, *built[:5], Q_=Q_); qz1_all |= Q_['z']; qd_all |= Q_['d']
assert all(kind in (0, 1, 6) for _, box, kind, pay in leaves)
from size_m import PyrF
from amk import fP, fM
WMIN = int(os.environ.get("WMIN", "6"))
P = PyrF(size7s.wcell, dmin=WMIN, PE=5, PB=10, MAXA=4, U=U, FUEL=14)
P.need({pc for (lo, hi) in qz_all for pc in r["pieces"](lo, hi)} | qz1_all)
P.xmax = max(P.xmax, r["P"].xmax)
for j in range(P.X0 >> P.PB, ((P.xmax - 1) >> P.PB) + 1): P.res[j] = WMIN
P.build()
PP = PyrF(fP, dmin=5, PE=DPE, PB=10, MAXA=4, U=U1, FUEL=DFUEL); PP.need(qd_all)
PM = PyrF(fM, dmin=5, PE=DPE, PB=10, MAXA=4, U=U1, FUEL=DFUEL); PM.need(qd_all)
PP.xmax = max(PP.xmax, r["PP"].xmax); PM.xmax = max(PM.xmax, r["PM"].xmax)
if DDENSE:
    for X_ in (PP, PM):
        for j in range(X_.X0 >> X_.PB, ((X_.xmax - 1) >> X_.PB) + 1): X_.res[j] = DLO if (j << 10) < XD else DHI
PP.build(); PM.build()
DT = PairTable(PP, PM)
ptw, ptd = built[3], built[4]
Plb3 = size7s.lb3_of(P.lb, 4, 1024)
built2 = (P.lb, PP.lb, PM.lb, ptw, ptd)
def zlow(box):
    return U * sum(bN[k] * box[k][0] for k in range(Q)) + SC * sum(aN[t] * Plb3(lo, hi) for t, (lo, hi) in enumerate(iv(box)))
bad = 0; pts = set(); nZ = nS = nB = nT = nSc = nM = 0
for _, box, kind, pay in leaves:
    if box[0][0] > box[Q - 1][1]: nT += 1; continue
    if kind == 1:
        nZ += 1
        if zlow(box) < CSU: bad += 1; print("  Z fails", box)
    elif kind == 6:
        nM += 1; Q_ = {'z': set(), 'd': set(), 'p': set()}
        if not r["meval"](box, pay, *built2, Q_=Q_): bad += 1; print("  M fails", box, r["meval"](box, pay, *built[:5]))
        pts |= Q_['p']
print(f"[{NAME}] re-verified on the final tables: Z {nZ}, M {nM}, reflected {nT}; failures {bad}", flush=True)
assert bad == 0
# the pair table reads agree with the two pyramids
for (lo, hi) in qd_all:
    e = DT.lb2(lo, hi); assert (e & M32, e >> 32) == (PP.lb(lo, hi), PM.lb(lo, hi))
# ---- the point table of triples ----
from collections import defaultdict
assert max(pts) < 524288
blocks = defaultdict(dict)
for x in pts:
    w_ = ptw(x); p_, m_ = ptd(x)
    blocks[x >> 10][x & 1023] = w_ | (p_ << 32) | (m_ << 64)
PB3 = {}
for j, dd in blocks.items():
    tz = min(min(10, (o & -o).bit_length() - 1) if o else 10 for o in dd)
    X = 0
    for o, v in dd.items(): X |= v << (96 * (o >> tz))
    PB3[j] = tz | (X << 4)
ptcells = sum(1 << (10 - (X & 15)) for X in PB3.values())
print(f"[{NAME}] point table: {len(pts)} points, {len(PB3)} blocks, {ptcells} stored triples", flush=True)
def pt3_py(x):
    if x >= 524288: return 0
    X = PB3.get(x >> 10, 0); rr = X & 15
    if x & ((1 << rr) - 1): return 0
    return ((X >> 4) >> (96 * ((x & 1023) >> rr))) & ((1 << 96) - 1)
for x in pts:
    v = pt3_py(x); assert v & M32 == ptw(x) and ((v >> 32) & M32, v >> 64) == ptd(x)
# ---- early-exit order of the zero-order test ----
contrib = [0] * NP
for _, box, kind, pay in leaves:
    if kind != 1 or box[0][0] > box[Q - 1][1]: continue
    for t, (lo, hi) in enumerate(iv(box)): contrib[t] += aN[t] * Plb3(lo, hi)
ORDER = sorted(range(NP), key=lambda t: -contrib[t])
# ---- Lean data ----
L = []; W = L.append
NS = f"Zeta23Ext.Bridge.ThreePoint.{NAME}"
stw, std = P.stats(), PP.stats()
W(f"\n/-! ###### certificate data `{NAME}`: pyramid table ({stw['blocks']} blocks, {stw['finest']} finest cells), "
  f"derivative table ({std['blocks']} blocks, {std['finest']} finest cells), point table ({len(pts)} points), "
  f"{len(leaves)} leaves (half-space; {nZ} zero-order, {nM} minorant, {nT} reflected) ###### -/\n")
W(f"noncomputable section\n\nnamespace {NS}Data\n\nopen Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD {NS}\n\nset_option maxRecDepth 100000\n")
W(pyr_consts(P, "TOP", "BK"))
W("theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel\n")
def chunked(name, res, check, target, unit):
    cost = {j: (1 << (10 - res[j])) for j in res}
    chunks = []; a0 = 0; acc = 0
    for j in range(512):
        acc += cost.get(j, 0) * unit + 1
        if acc >= target or j == 511:
            chunks.append((a0, j + 1 - a0)); a0 = j + 1; acc = 0
    for cc, (a1, nn) in enumerate(chunks):
        W(f"theorem {name}_{cc} : Pyr.allFrom {a1} {nn} (fun j => {check}) = true := by decide +kernel")
    expr = f"{name}_0"
    for cc in range(1, len(chunks)): expr = f"(Pyr.allFrom_add {expr} {name}_{cc})"
    W(f"theorem {name}_all : Pyr.allFrom 0 512 (fun j => {check}) = true := by\n  have h := {expr}\n  exact h")
chunked("blk", P.res, "Pyr.blockOk (BK j) j", 600, 1)
W("theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok\n")
W(pair_consts(DT, "TOPD", "BKD"))
W("theorem topD_ok : topOk2 TOPD BKD = true := by decide +kernel\n")
chunked("dblk", PP.res, "blockOk2 (BKD j) j", 600, 3)
W("theorem lbD : LBSoundD TOPD BKD := lbDr_sound (blocks2_of dblk_all) topD_ok\n")
for j in sorted(PB3): W(f"def PT3B_{j} : ℕ := {PB3[j]}")
W("\n".join(dispatch("PT3B", {j: f"PT3B_{j}" for j in PB3})))
chunked("pblk", {j: X & 15 for j, X in PB3.items()}, "pt3BlockOk (PT3B j) j", 600, 3)
W("theorem ptS : PT3Sound PT3B := pt3_sound (pt3blocks_of pblk_all)\n")
def coords(box): return " ".join(f"{l} {u}" for (l, u) in box)
def trip(x):
    p_, m_ = ptd(x); return ptw(x) | (p_ << 32) | (m_ << 64)
RGK = {}
for (a_, b_, c_) in REGS:
    k_ = (a_ + 16384) >> 15
    if k_ < 16: RGK[k_] = (a_, b_, c_)
RA = sum((RGK[k][0] if k in RGK else 1) << (20 * k) for k in range(16))
RB = sum((RGK[k][1] if k in RGK else 0) << (20 * k) for k in range(16))
W(f"def REG : ℕ × ℕ × List (List ℕ) := ({RA}, {RB}, [" + ", ".join("[" + ", ".join(map(str, RGK[k][2])) + "]" if k in RGK else "[]" for k in range(16)) + "])")
W("theorem hR : rgOk REG = true := by decide +kernel\n")
aAdj = [aN[PAIRS.index((k, k + 1))] for k in range(Q)]
covers, bads, S = r["covers"], r["bads"], r["S"]
for k in range(Q):
    clear, badk = covers[k]
    segs = sorted([(l, u, True) for (l, u) in clear] + [(l, u, False) for (l, u) in badk])
    pos = SC // 2
    for (l, u, cl) in segs: assert l == pos; pos = u
    assert pos == S[k]
    W(f"def cover{k} : List (ℕ × ℕ × Bool) := [\n  " + ",\n  ".join(f"({l}, {u}, {'true' if cl else 'false'})" for (l, u, cl) in segs) + "]")
    W(f"theorem cover{k}_ok : {NAME}.coverCheck {aAdj[k]} (SC / 2) {S[k]} cover{k} = true := by decide +kernel\n")
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def height(nd): return 1 if nd[0] == 'leaf' else 1 + max(height(nd[4]), height(nd[5]))
def code(nd, out):
    if nd[0] == 'leaf':
        if nd[2] == 6:
            out.extend([0, 1])
            for t in range(NP):
                if aN[t] == 0: continue
                kap, j1, j2, lam = nd[3][t]
                out.extend([kap & 1, kap >> 1])
                if kap >= 1: out.extend([(j1 >> i) & 1 for i in range(JB)])
                if kap == 3: out.extend([(j2 >> i) & 1 for i in range(JB)])
                if kap >= 2: out.extend([(lam >> i) & 1 for i in range(10)])
            return
        assert nd[2] in (0, 1)
        out.extend([0, 0])
    else:
        out.append(1); out.extend([(nd[2] >> i) & 1 for i in range(3)]); code(nd[4], out); code(nd[5], out)
nthm = [0]; nbits = [0]; nchunk = []
def proof(nd):
    if nleaf(nd) <= CH:
        bl = [0]; code(nd, bl)
        bits = sum(1 << i for i, b in enumerate(bl) if b)
        nbits[0] += len(bl)
        name = f"wk{nthm[0]}"; nthm[0] += 1; nchunk.append(nleaf(nd))
        W(f"theorem {name} : {NAME}.Covered {coords(nd[1])} :=\n  {NAME}.covered_of_walk lbS lbD ptS hR {bits} {height(nd) + 1} {coords(nd[1])} {len(bl)} (by decide +kernel) (by decide)")
        return name
    return f"({NAME}.covered_split{nd[2]} {nd[3]} {proof(nd[4])} {proof(nd[5])})"
roots = {}
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    roots[tup] = proof(r["nodes"][tup])
for k in range(Q):
    for i, (l, u) in enumerate(bads[k]):
        W(f"theorem bd{k}_{i} : ({NAME}.badOf cover{k}).getD {i} (0, 0) = ({l}, {u}) := by decide +kernel")
    W(f"theorem nb{k}_eq : ({NAME}.badOf cover{k}).length = {len(bads[k])} := by decide +kernel")
cases = []
for tup, pf in roots.items():
    rw = ", ".join(f"bd{k}_{tup[k]}" for k in range(Q))
    cases.append(f"  | {', '.join(str(i) for i in tup)}, {', '.join('_' for _ in range(Q))} => rw [{rw}]; exact {pf}")
for k in range(Q):
    pat = ", ".join((f"i + {len(bads[k])}" if kk == k else "_") for kk in range(Q))
    hp = ", ".join(("hi" if kk == k else "_") for kk in range(Q))
    cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
ivs = " ".join(f"i{k}" for k in range(Q)); hvs = " ".join(f"hi{k}" for k in range(Q))
W(f"theorem run_ok : ∀ {ivs}, {' → '.join(f'i{k} < ({NAME}.badOf cover{k}).length' for k in range(Q))} →\n"
  f"    {NAME}.Covered {' '.join(f'(({NAME}.badOf cover{k}).getD i{k} (0, 0)).1 (({NAME}.badOf cover{k}).getD i{k} (0, 0)).2' for k in range(Q))} := by\n"
  f"  intro {ivs} {hvs}\n" + "".join(f"  rw [nb{k}_eq] at hi{k}\n" for k in range(Q)) +
  f"  match {', '.join(f'i{k}' for k in range(Q))}, {', '.join(f'hi{k}' for k in range(Q))} with\n" + "\n".join(cases) + "\n")
W(f"theorem cert : ∀ {' '.join(f'g{k}' for k in range(Q))} : ℝ, {' → '.join(f'0 ≤ g{k}' for k in range(Q))} → "
  f"({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'g{k}' for k in range(Q))} ∨ g{Q-1} < g0 :=\n"
  f"  {NAME}.of_check {' '.join(f'cover{k}' for k in range(Q))} {' '.join(str(x) for x in S)}\n"
  f"    {' '.join('(by decide +kernel)' for _ in range(Q))} {' '.join(f'cover{k}_ok' for k in range(Q))} (by decide +kernel) run_ok\n")
W(f"end {NS}Data\n\nend\n")
data = "\n".join(L)
import re as _re
data = _re.sub(r"(?<![\w.])(\d{40,})(?![\w.])", lambda m: hex(int(m.group(1))), data)
data = data.replace("Zeta23Ext.Bridge.ThreePoint", "AMW.Cert")
data = f"import AMW.{NAME}Inst\n" + data
_X = [f"x{r}" for r in range(Q)]
data += (f"""
noncomputable section

namespace AMW.Cert

theorem {NAME}_G_rev ({' '.join(_X)} : ℝ) : {NAME}.G {' '.join(reversed(_X))} = {NAME}.G {' '.join(_X)} := by
  unfold {NAME}.G; ring_nf

/-- **the AM {Q + 1}-point certificate**: the half-space certificate completed by reflection (symmetric weights) -/
theorem {NAME}_cert_full : ∀ {' '.join(_X)} : ℝ, {' → '.join(f'0 ≤ {v}' for v in _X)} →
    ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(_X)} := by
  intro {' '.join(_X)} {' '.join(f'h{r}' for r in range(Q))}
  rcases lt_or_ge {_X[Q-1]} {_X[0]} with hlt | hle
  · rcases {NAME}Data.cert {' '.join(reversed(_X))} {' '.join(f'h{r}' for r in reversed(range(Q)))} with h | h
    · rw [← {NAME}_G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases {NAME}Data.cert {' '.join(_X)} {' '.join(f'h{r}' for r in range(Q))} with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

end AMW.Cert

end
""")
open(os.path.join(ROOT, f"{NAME}Data.lean"), "w", encoding="utf-8").write(data)
# ---- the instance, on the AM engine cores (AMW/CEngine via AMW/CWindow) and the minorant core (AMW/CMin via AMW/CMinX) ----
inst = (f"""import AMW.CWindow
import AMW.CMinX

/-! ###### the AM {Q + 1}-point weighted certificate `{NAME}`: zero-order and minorant leaf tests, walk, cover

Weights: LP pair weights and pressures over SA = 10⁸ for the window of `AMW.Window`.  Pyramid lower-bound table adapted
from five-point-pyramid-2 by typh (Apache-2.0); per-term minorant leaves after mvt-engine's MinCore. ###### -/

set_option maxRecDepth 100000
""" + checker(NAME, SA, aN, bN, cN, ORDER, JCQ)).replace("Zeta23Ext.Bridge.ThreePoint", "AMW.Cert")
chk = inst
open(os.path.join(ROOT, f"{NAME}Inst.lean"), "w", encoding="utf-8").write(chk)
open(os.path.join(HERE, f"{NAME}_params.txt"), "w").write(f"{Q} {SA} {','.join(map(str, aN))} {','.join(map(str, bN))} {cN} {NAME} 15 0 0\n")
open(os.path.join(HERE, f"{NAME}_order.txt"), "w").write(",".join(map(str, ORDER)) + "\n")
print(f"[{NAME}] delta={DELTA} cN={cN} leaves={len(leaves)} (Z {nZ}, M {nM}, reflected {nT}) "
      f"w={stw['finest']} d={std['finest']} points={len(pts)} chunks={nthm[0]} bits={nbits[0]} order={ORDER} "
      f"data={len(data.encode())} checker={len(chk.encode())} ({time.time()-t0:.0f}s)")
