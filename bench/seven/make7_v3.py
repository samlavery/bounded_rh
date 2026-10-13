#!/usr/bin/env python3
"""Size and emit the weighted seven-point certificate (six gaps): zero-order leaves, slope leaves (expansion point and
expansion set in the walk word), basin boxes certified once by the slope test at an explicit point.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0); basin boxes at the near-minimal
local minima after six-point-convex-basins-2 by typh (Apache-2.0).

Usage: make7.py WEIGHTS.npz DELTA TAU HW NAME [CH]
Writes in the workspace root: data_<NAME>.lean, checker_<NAME>.lean, <NAME>_params.txt, <NAME>_order.txt.
Every leaf and basin is re-verified on the built tables (integer-faithful replicas of the Lean tests)."""
import os, sys, itertools, time
import numpy as np
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "mvt"))
import size7s
from size7s import run, Q, PAIRS, NP, TS, SC, U, U1, KU1, RU, M32
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
from gen7n import checker, LEAFLEN
WF, DELTA, TAU, HW, NAME = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
CH = int(sys.argv[6]) if len(sys.argv) > 6 else 1500
JCQ = 8
d = np.load(os.path.join(HERE, WF)); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
SA = 10**8
gmin = float(d['vals'][0]) * SA
cN = int(gmin * (1 - DELTA))
CSU = cN * SC * U
t0 = time.time()
# ---- basins: boxes centred at the (grid-rounded) near-minimal minima and their mirror images near the diagonal; the
# slope test at the centre certifies each (the gradient vanishes there, and the charges vanish where w is convex) ----
# the upper extent is cut so that no pair term's range reaches the concave zone beyond its next inflection point
from sevenw import w1 as w1f
def w2n(x, h=1e-6): return (w1f(x + h) - w1f(x - h)) / (2 * h)
def upper_extent(q):
    hu = HW
    for (i, j) in PAIRS:
        qt = sum(q[i:j]); xs = (qt + np.arange(0, (j - i) * HW + 1)) / SC; neg = np.nonzero(w2n(xs) < 0)[0]
        if len(neg): hu = min(hu, (int(neg[0]) - 16) // (j - i))
    return hu
centres = []
for v, x in zip(d['vals'], d['mins']):
    if v * SA > gmin * (1 + TAU): break
    q = [int(round(xx * SC)) for xx in x]
    hu = upper_extent(q)
    for qq in (q, q[::-1]):
        bx = tuple((qk - HW, qk + hu) for qk in qq)
        if bx[0][0] <= bx[Q - 1][1] and all(bx != b for b, _ in centres): centres.append((bx, qq))
    print(f"  basin at {[round(xx, 4) for xx in x]}: extents -{HW} / +{hu}", flush=True)
basins = [b for b, _ in centres]
DPE = int(os.environ.get("DPE", "6")); DFUEL = int(os.environ.get("DFUEL", "14"))
DLO = int(os.environ.get("DLO", "5")); DHI = int(os.environ.get("DHI", "6")); XD = 81920
r = run(cN, aN, bN, JCQ=JCQ, basins=basins, WMIN=int(os.environ.get("WMIN", "6")), PED=DPE, DFUEL=DFUEL, DLO=DLO, DHI=DHI, XD=XD)
assert r is not None and r["bad"] == 0
P, PP, PM, built, sint, dec, sfloat = r["P"], r["PP"], r["PM"], r["built"], r["sint"], r["dec"], r["sfloat"]
print(f"[{NAME}] sizing: {r['nleaves']} leaves (Z {r['nZ']}, S {r['nS']}, basin {r['nB']}); points {r['stats']['points']} "
      f"({r['stats']['ptcells']} point cells) ({time.time()-t0:.0f}s)", flush=True)
CSU = cN * SC * U
def bas_queries(box, q, T):
    qz, qd = set(), set()
    for t, (i, j) in enumerate(PAIRS):
        lo = sum(box[k][0] for k in range(i, j)); hi = sum(box[k][1] for k in range(i, j)); qt = sum(q[i:j])
        if T >> t & 1:
            if hi > qt: qd.add((qt, hi))
            if qt > lo: qd.add((lo, qt))
        else: qz.add((lo, hi))
    return qz, qd
# the basin certificates: the convex-basin test at the centre: every expanded term carries a chain of cells on which
# w'' >= 0 (the others are read at zero order)
from w2cell import chain as w2chain
bascand = []
for box, q in centres:
    chs = []
    for t, (i, j) in enumerate(PAIRS):
        lo = sum(box[k][0] for k in range(i, j)); hi = sum(box[k][1] for k in range(i, j))
        chs.append(w2chain(lo, hi))
    T = sum(1 << t for t in range(NP) if chs[t] is not None)
    bascand.append((box, q, T, chs))
    print(f"  basin {[x[0] + HW for x in box]}: convex terms {bin(T).count('1')}/21, chain cells "
          f"{sum(len(c) for c in chs if c is not None)}", flush=True)
# extend the tables with the basin reads, rebuild, re-verify
qz_all, qd_all = set(), set()
leaves = r["leaves"]
def iv(box): return [(sum(box[k][0] for k in range(i, j)), sum(box[k][1] for k in range(i, j))) for (i, j) in PAIRS]
for _, box, kind, pay in leaves:
    I = iv(box)
    if kind == 1: qz_all.update(I)
    elif kind == 2:
        modes, T = pay; q = [dec(modes[k], box[k][0], box[k][1]) for k in range(Q)]
        a, b = bas_queries(box, q, T); qz_all |= a; qd_all |= b
FULL = (1 << NP) - 1
for box, q, T, chs in bascand:
    a, b = bas_queries(box, q, FULL); qz_all |= a; qd_all |= b
    a, b = bas_queries(box, q, 0); qz_all |= a
from size_m import PyrF
from w1cell import fP, fM
WMIN = int(os.environ.get("WMIN", "6"))
P = PyrF(size7s.wcell, dmin=WMIN, PE=5, PB=10, MAXA=4, U=U, FUEL=14)
P.need({pc for (lo, hi) in qz_all for pc in r["pieces"](lo, hi)})
for j in range(P.X0 >> P.PB, ((P.xmax - 1) >> P.PB) + 1): P.res[j] = WMIN
P.build()
PP = PyrF(fP, dmin=5, PE=DPE, PB=10, MAXA=4, U=U1, FUEL=DFUEL); PP.need(qd_all)
PM = PyrF(fM, dmin=5, PE=DPE, PB=10, MAXA=4, U=U1, FUEL=DFUEL); PM.need(qd_all)
for X_ in (PP, PM):
    for j in range(X_.X0 >> X_.PB, ((X_.xmax - 1) >> X_.PB) + 1): X_.res[j] = DLO if (j << 10) < XD else DHI
PP.build(); PM.build()
DT = PairTable(PP, PM)
ptw, ptd = built[3], built[4]
Plb3 = size7s.lb3_of(P.lb, 4, 1024)
built2 = (Plb3, PP.lb, PM.lb, ptw, ptd)
def zlow(box):
    return U * sum(bN[k] * box[k][0] for k in range(Q)) + SC * sum(aN[t] * Plb3(lo, hi) for t, (lo, hi) in enumerate(iv(box)))
bad = 0; pts = set(); nZ = nS = nB = nT = 0
for _, box, kind, pay in leaves:
    if box[0][0] > box[Q - 1][1]: nT += 1; continue
    if kind == 1:
        nZ += 1
        if zlow(box) < CSU: bad += 1
    elif kind == 2:
        nS += 1; modes, T = pay; q = [dec(modes[k], box[k][0], box[k][1]) for k in range(Q)]
        if sint(box, q, T, *built2) < CSU: bad += 1
        for t, (i, j) in enumerate(PAIRS):
            if T >> t & 1: pts.add(sum(q[i:j]))
    elif kind == 3:
        nB += 1
        if not any(all(bb[k][0] <= box[k][0] and box[k][1] <= bb[k][1] for k in range(Q)) for bb in basins): bad += 1
NEG = -(1 << 200)
def mint(box, q, T, V):
    """the integer mixed basin test, exactly as the Lean `cscheck` (chains checked separately): expanded terms
    (`T`) convex (`V`, no charge) or charged from the derivative reads, the others at zero order"""
    I = iv(box); lhs_t = 0; Pt = [0] * NP; Mt = [0] * NP; Rsum = 0
    lbP, lbM = built2[1], built2[2]
    for t, (i, j) in enumerate(PAIRS):
        lo, hi = I[t]
        if T >> t & 1:
            qt = sum(q[i:j]); p_, m_ = ptd(qt)
            if p_ < 1 or m_ < 1: return NEG
            Pt[t] = p_; Mt[t] = m_; lhs_t += aN[t] * ptw(qt)
            if not (V >> t & 1):
                up = dn = 0
                if hi > qt:
                    e = lbP(qt, hi)
                    if e < 1: return NEG
                    up = (hi - qt) * max(0, 4 * U1 - m_ - e)
                if qt > lo:
                    e = lbM(lo, qt)
                    if e < 1: return NEG
                    dn = (qt - lo) * max(0, 4 * U1 - e - p_)
                Rsum += aN[t] * max(up, dn)
        else: lhs_t += aN[t] * Plb3(lo, hi)
    pen = 0
    for k in range(Q):
        AT = sum(aN[t] for t in size7s.TS[k] if T >> t & 1)
        Pos = max(0, U1 * bN[k] + KU1 * AT - sum(aN[t] * Mt[t] for t in size7s.TS[k] if T >> t & 1))
        Neg = max(0, KU1 * AT - U1 * bN[k] - sum(aN[t] * Pt[t] for t in size7s.TS[k] if T >> t & 1))
        pen += (q[k] - box[k][0]) * Pos + (box[k][1] - q[k]) * Neg
    return U * sum(bN[k] * q[k] for k in range(Q)) + SC * lhs_t - RU * (pen + Rsum)
bascert = []
for box, q, V, chs in bascand:
    T = FULL
    v = mint(box, q, T, V)
    improved = True
    while v < CSU and improved:
        improved = False
        for t in range(NP):
            for T2, V2 in ((T ^ (1 << t), V & (T ^ (1 << t))), (T, V & ~(1 << t))):
                v2 = mint(box, q, T2, V2)
                if v2 > v: v, T, V, improved = v2, T2, V2, True
    print(f"  basin {[x[0] + HW for x in box]}: integer margin {(v - CSU) / (SC * U):+.0f} (units 1e-8); "
          f"expanded {bin(T).count('1')}, convex {bin(V).count('1')}", flush=True)
    if v < CSU: bad += 1; print("  basin fails", box)
    bpts = sorted({sum(q[i:j]) for t, (i, j) in enumerate(PAIRS) if T >> t & 1})
    bascert.append((box, q, T, V, [chs[t] if V >> t & 1 else [] for t in range(NP)], bpts))
print(f"[{NAME}] re-verified on the final tables: Z {nZ}, S {nS}, basin {nB}, reflected {nT}; failures {bad}", flush=True)
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
  f"{len(bascert)} basins, {len(leaves)} leaves (half-space; {nZ} zero-order, {nS} slope, {nB} in basins) ###### -/\n")
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
for k, (box, q, T, V, chs, bpts) in enumerate(bascert):
    CHT = " ".join("[" + ", ".join(map(str, c)) + "]" for c in chs)
    W(f"def BP{k} : List (ℕ × ℕ) := [" + ", ".join(f"({x}, {trip(x)})" for x in bpts) + "]")
    W(f"theorem bas{k} : {NAME}.Covered {coords(box)} :=\n  {NAME}.covered_of_ctest lbS lbD (ptl_sound BP{k} (by decide +kernel)) {coords(box)} {' '.join(map(str, q))} {T} {V}\n    {CHT}\n    (by decide +kernel)")
W(f"def basList : List {NAME}.Bx := [" + ", ".join(f"⟨{', '.join(f'{l}, {u}' for (l, u) in box)}⟩" for box, *_ in bascert) + "]")
W(f"theorem hbas : {NAME}.BasOK basList := by\n  intro b hb\n  simp only [basList, List.mem_cons, List.not_mem_nil, or_false] at hb\n"
  f"  rcases hb with {' | '.join('rfl' for _ in bascert)}\n  exacts [{', '.join(f'bas{k}' for k in range(len(bascert)))}]\n")
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
        kind = {0: 0, 1: 0, 2: 1, 3: 2}[nd[2]]
        out.extend([0, kind & 1, kind >> 1])
        if kind == 1:
            modes, T = nd[3]
            for k in range(Q): out.extend([modes[k] & 1, modes[k] >> 1])
            if T == (1 << NP) - 1: out.append(1)
            else: out.append(0); out.extend([(T >> t) & 1 for t in range(NP)])
    else:
        out.append(1); out.extend([(nd[2] >> i) & 1 for i in range(3)]); code(nd[4], out); code(nd[5], out)
nthm = [0]; nbits = [0]; nchunk = []
def proof(nd):
    if nleaf(nd) <= CH:
        bl = [0]; code(nd, bl)
        bits = sum(1 << i for i, b in enumerate(bl) if b)
        nbits[0] += len(bl)
        name = f"wk{nthm[0]}"; nthm[0] += 1; nchunk.append(nleaf(nd))
        W(f"theorem {name} : {NAME}.Covered {coords(nd[1])} :=\n  {NAME}.covered_of_walk lbS lbD ptS hbas {bits} {height(nd) + 1} {coords(nd[1])} {len(bl)} (by decide +kernel) (by decide)")
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
open(os.path.join(ROOT, f"data_{NAME}.lean"), "w", encoding="utf-8").write(data)
# ---- checker: cells + pyramid of the accepted certificate, the mean-value core, the slope core, the instance ----
c25 = open(os.path.join(ROOT, "checker_SixW25P.lean"), encoding="utf-8").read()
pre = c25[:c25.index("/-! ###### the 6-point weighted certificate `SixW25P`")].replace("SixW25P", NAME)
defs = open(os.path.join(HERE, "..", "mvt", "MvtDefs.lean"), encoding="utf-8").read()
defs = defs[defs.index("-- MVTDEFS-BEGIN"):defs.index("-- MVTDEFS-END")].replace("-- MVTDEFS-BEGIN\n", "")
core = open(os.path.join(HERE, "..", "mvt", "MvtCore.lean"), encoding="utf-8").read()
core = core[core.index("-- MVTPROOFS-BEGIN"):core.index("-- MVTPROOFS-END")].replace("-- MVTPROOFS-BEGIN\n", "")
sl = open(os.path.join(HERE, "SlopeCore.lean"), encoding="utf-8").read()
sl = sl[sl.index("-- SLOPE-BEGIN"):sl.index("-- SLOPE-END")].replace("-- SLOPE-BEGIN\n", "").replace("-- SLOPEDEFS-END\n", "")
cv = open(os.path.join(HERE, "ConvCore.lean"), encoding="utf-8").read()
cv = cv[cv.index("-- CONV-BEGIN"):cv.index("-- CONV-END")].replace("-- CONV-BEGIN\n", "").replace("-- CONVDEFS-END\n", "")
inst = (f"\n/-! ###### the 7-point weighted certificate `{NAME}`: zero-order and slope leaf tests, convex basins, walk, cover ###### -/\n"
        + checker(NAME, SA, aN, bN, cN, ORDER, JCQ))
chk = pre + defs + core + sl + cv + inst
open(os.path.join(ROOT, f"checker_{NAME}.lean"), "w", encoding="utf-8").write(chk)
open(os.path.join(ROOT, f"{NAME}_params.txt"), "w").write(f"{Q} {SA} {','.join(map(str, aN))} {','.join(map(str, bN))} {cN} {NAME} 15 0 0\n")
open(os.path.join(ROOT, f"{NAME}_order.txt"), "w").write(",".join(map(str, ORDER)) + "\n")
print(f"[{NAME}] delta={DELTA} cN={cN} leaves={len(leaves)} (Z {nZ}, S {nS}, basin {nB}, reflected {nT}) basins={len(bascert)} "
      f"w={stw['finest']} d={std['finest']} points={len(pts)} chunks={nthm[0]} bits={nbits[0]} order={ORDER} "
      f"data={len(data.encode())} checker={len(chk.encode())} ({time.time()-t0:.0f}s)")
