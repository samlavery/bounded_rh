#!/usr/bin/env python3
"""Size and emit a weighted six-point certificate with the two leaf tests (zero-order pyramid test, mean-value test).
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Usage: make_mvt.py DELTA NAME [CH]
Writes, in the workspace root: data_<NAME>.lean, checker_<NAME>.lean (cells + pyramid as the accepted certificate, the
mean-value core, the instance), head_<NAME>.lean, <NAME>_params.txt, <NAME>_order.txt, kappa_<NAME>.txt.
Every leaf is re-verified on the built tables (integer-faithful replicas of the Lean tests) before emission."""
import os, sys, itertools, time, math, re
from fractions import Fraction as F
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
from size_m import run, PAIRS, Q, AN, BN, SA, SC
from emit_tables import pyr_consts, pt_blocks, pt_consts, pt_lookup, PairTable, pair_consts
import gen_inst
from gen_checker_mvt import checker
DELTA = float(sys.argv[1]); NAME = sys.argv[2]; CH = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
cN = round(358287 * (1 - DELTA))
t0 = time.time()
r = run(cN, JC=gen_inst.JC, corner=gen_inst.CORNER, dmin=gen_inst.DMIN, PED=gen_inst.PED)
assert r is not None and r["bad_leaves"] == 0
P, PP, PM, PT = r["P"], r["PP"], r["PM"], r["PT"]
nodes, covers, bads, S = r["nodes"], r["covers"], r["bads"], r["S"]
for X in (P, PP, PM):
    assert (X.PB, X.KT, X.MAXA, X.EB, X.FUEL) == (10, 19, 4, 32, 14)
    assert max(X.res.values(), default=0) < 512 and X.xmax <= (1 << 19)
assert P.PE == 5 and PP.PE == PM.PE == gen_inst.PED == 4
assert sorted(PP.res.items()) == sorted(PM.res.items()), "the two derivative tables share one block structure"
PB = pt_blocks(PT)
DT = PairTable(PP, PM)
for x, v in PT.items(): assert pt_lookup(PB, x) == v
# ---- early-exit order of the zero-order test: by total contribution over its leaves ----
leaves = r["leaves"]
def terms(box): return [(sum(box[q][0] for q in range(i, j)), sum(box[q][1] for q in range(i, j))) for (i, j) in PAIRS]
contrib = [0] * len(PAIRS)
for b, kind in leaves:
    if kind != 1 or b[0][0] > b[Q - 1][1]: continue
    for t, (lo, hi) in enumerate(terms(b)): contrib[t] += AN[t] * P.lb(lo, hi)
ORDER = sorted(range(len(PAIRS)), key=lambda t: -contrib[t])
# ---- replica of the Lean walk: every leaf decided by its flagged test on the built tables ----
U = 10**10; U1 = 10**9; KU1 = 2 * U1; CSU = cN * SC * U
TS = gen_inst.TS; AR = [sum(AN[t] for t in TS[q]) for q in range(Q)]
def leafZ(b):
    s = U * sum(BN[q] * b[q][0] for q in range(Q))
    for t, (lo, hi) in enumerate(terms(b)): s += SC * AN[t] * P.lb(lo, hi)
    return s >= CSU
def leafM(b):
    tm = terms(b); e = [DT.lb2(lo, hi) for lo, hi in tm]
    p = [x & ((1 << 32) - 1) for x in e]; qq = [x >> 32 for x in e]
    assert p == [PP.lb(lo, hi) for lo, hi in tm] and qq == [PM.lb(lo, hi) for lo, hi in tm]
    PN = []
    for q in range(Q):
        Pos = max(0, U1 * BN[q] + KU1 * AR[q] - sum(AN[t] * qq[t] for t in TS[q]))
        Neg = max(0, KU1 * AR[q] - (U1 * BN[q] + sum(AN[t] * p[t] for t in TS[q])))
        PN.append((Pos, Neg))
    m = [gen_inst.pick_py(b[q][0], b[q][1], *PN[q]) for q in range(Q)]
    if any(not (b[q][0] <= m[q] <= b[q][1]) for q in range(Q)): return False
    if min(p) < 1 or min(qq) < 1: return False
    pen = sum((m[q] - b[q][0]) * PN[q][0] + (b[q][1] - m[q]) * PN[q][1] for q in range(Q))
    lhs = U * sum(BN[q] * m[q] for q in range(Q)) + SC * sum(AN[t] * pt_lookup(PB, sum(m[i:j])) for t, (i, j) in enumerate(PAIRS))
    return CSU + (U // U1) * pen <= lhs
nZ = nM = 0
for b, kind in leaves:
    if b[0][0] > b[Q - 1][1]: continue
    if kind == 2: assert leafM(b), b; nM += 1
    else: assert leafZ(b), b; nZ += 1
print(f"[{NAME}] replica: {nZ} zero-order leaves and {nM} mean-value leaves pass on the built tables", flush=True)
# ---- Lean data ----
L = []; W = L.append
NS = f"Zeta23Ext.Bridge.ThreePoint.{NAME}"
stw, std = P.stats(), PP.stats()
nleaves = r["nleaves"]
W(f"\n/-! ###### certificate data `{NAME}`: pyramid table ({stw['blocks']} blocks, {stw['finest']} finest cells, "
  f"{stw['entries']} entries), derivative tables ({std['blocks']} blocks, {std['finest']} finest cells), point table "
  f"({len(PT)} points), {nleaves} leaves (half-space; {nM} mean-value) ###### -/\n")
W(f"noncomputable section\n\nnamespace {NS}Data\n\nopen Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD {NS}\n\nset_option maxRecDepth 100000\n")
W(pyr_consts(P, "TOP", "BK"))
W("theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel\n")
def chunked(name, res, check, target, unit):
    cost = {j: (1 << (10 - res[j])) for j in res}
    chunks = []; a = 0; acc = 0
    for j in range(512):
        acc += cost.get(j, 0) * unit + 1
        if acc >= target or j == 511:
            chunks.append((a, j + 1 - a)); a = j + 1; acc = 0
    for c, (a, nn) in enumerate(chunks):
        W(f"theorem {name}_{c} : Pyr.allFrom {a} {nn} (fun j => {check}) = true := by decide +kernel")
    expr = f"{name}_0"
    for c in range(1, len(chunks)): expr = f"(Pyr.allFrom_add {expr} {name}_{c})"
    W(f"theorem {name}_all : Pyr.allFrom 0 512 (fun j => {check}) = true := by\n  have h := {expr}\n  exact h")
chunked("blk", P.res, "Pyr.blockOk (BK j) j", 600, 1)
W("theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok\n")
W(pair_consts(DT, "TOPD", "BKD"))
W("theorem topD_ok : topOk2 TOPD BKD = true := by decide +kernel\n")
chunked("dblk", PP.res, "blockOk2 (BKD j) j", 600, 3)
W("theorem lbD : LBSound2 TOPD BKD := lb2_sound (blocks2_of dblk_all) topD_ok\n")
W(pt_consts(PB))
pres = {j: X & 15 for j, X in PB.items()}
chunked("pblk", pres, "ptBlockOk (PTB j) j", 600, 1)
W("theorem ptS : PTSound PTB := ptv_sound (ptblocks_of pblk_all)\n")
aAdj = [AN[PAIRS.index((q, q + 1))] for q in range(Q)]
for q in range(Q):
    clear, bad = covers[q]
    segs = sorted([(l, u, True) for (l, u) in clear] + [(l, u, False) for (l, u) in bad])
    pos = SC // 2
    for (l, u, cl) in segs: assert l == pos; pos = u
    assert pos == S[q]
    W(f"def cover{q} : List (ℕ × ℕ × Bool) := [\n  " + ",\n  ".join(f"({l}, {u}, {'true' if cl else 'false'})" for (l, u, cl) in segs) + "]")
    W(f"theorem cover{q}_ok : {NAME}.coverCheck {aAdj[q]} (SC / 2) {S[q]} cover{q} = true := by decide +kernel\n")
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def height(nd): return 1 if nd[0] == 'leaf' else 1 + max(height(nd[4]), height(nd[5]))
def coords(box): return " ".join(f"{l} {u}" for (l, u) in box)
nthm = [0]; nbits = [0]; nchunk = []
def proof(nd):
    if nleaf(nd) <= CH:
        bl = [0]; gen_inst.walk_code(nd, bl)
        bits = sum(1 << i for i, b in enumerate(bl) if b)
        nbits[0] += len(bl)
        name = f"wk{nthm[0]}"; nthm[0] += 1; nchunk.append(nleaf(nd))
        W(f"theorem {name} : {NAME}.Covered {coords(nd[1])} :=\n  {NAME}.covered_of_walk lbS lbD ptS {bits} {height(nd) + 1} {coords(nd[1])} {len(bl)} (by decide +kernel) (by decide)")
        return name
    k, m = nd[2], nd[3]
    return f"({NAME}.covered_split{k} {m} {proof(nd[4])} {proof(nd[5])})"
roots = {}
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    roots[tup] = proof(nodes[tup])
for q in range(Q):
    for i, (l, u) in enumerate(bads[q]):
        W(f"theorem bd{q}_{i} : ({NAME}.badOf cover{q}).getD {i} (0, 0) = ({l}, {u}) := by decide +kernel")
    W(f"theorem nb{q}_eq : ({NAME}.badOf cover{q}).length = {len(bads[q])} := by decide +kernel")
cases = []
for tup, pf in roots.items():
    rw = ", ".join(f"bd{q}_{tup[q]}" for q in range(Q))
    cases.append(f"  | {', '.join(str(i) for i in tup)}, {', '.join('_' for _ in range(Q))} => rw [{rw}]; exact {pf}")
for q in range(Q):
    pat = ", ".join((f"i + {len(bads[q])}" if k == q else "_") for k in range(Q))
    hp = ", ".join(("hi" if k == q else "_") for k in range(Q))
    cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
iv = " ".join(f"i{q}" for q in range(Q)); hv = " ".join(f"hi{q}" for q in range(Q))
W(f"theorem run_ok : ∀ {iv}, {' → '.join(f'i{q} < ({NAME}.badOf cover{q}).length' for q in range(Q))} →\n"
  f"    {NAME}.Covered {' '.join(f'(({NAME}.badOf cover{q}).getD i{q} (0, 0)).1 (({NAME}.badOf cover{q}).getD i{q} (0, 0)).2' for q in range(Q))} := by\n"
  f"  intro {iv} {hv}\n" + "".join(f"  rw [nb{q}_eq] at hi{q}\n" for q in range(Q)) +
  f"  match {', '.join(f'i{q}' for q in range(Q))}, {', '.join(f'hi{q}' for q in range(Q))} with\n" + "\n".join(cases) + "\n")
W(f"theorem cert : ∀ {' '.join(f'g{q}' for q in range(Q))} : ℝ, {' → '.join(f'0 ≤ g{q}' for q in range(Q))} → "
  f"({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'g{q}' for q in range(Q))} ∨ g{Q-1} < g0 :=\n"
  f"  {NAME}.of_check {' '.join(f'cover{q}' for q in range(Q))} {' '.join(str(x) for x in S)}\n"
  f"    {' '.join('(by decide +kernel)' for _ in range(Q))} {' '.join(f'cover{q}_ok' for q in range(Q))} (by decide +kernel) run_ok\n")
W(f"end {NS}Data\n\nend\n")
data = "\n".join(L)
open(os.path.join(ROOT, f"data_{NAME}.lean"), "w", encoding="utf-8").write(data)
# ---- checker: cells + pyramid of the accepted certificate, the mean-value core, the instance ----
c25 = open(os.path.join(ROOT, "checker_SixW25P.lean"), encoding="utf-8").read()
i_inst = c25.index("/-! ###### the 6-point weighted certificate `SixW25P`")
pre = c25[:i_inst].replace("SixW25P", NAME)
defs = open(os.path.join(HERE, "MvtDefs.lean"), encoding="utf-8").read()
defs = defs[defs.index("-- MVTDEFS-BEGIN"):defs.index("-- MVTDEFS-END")].replace("-- MVTDEFS-BEGIN\n", "")
core = open(os.path.join(HERE, "MvtCore.lean"), encoding="utf-8").read()
core = core[core.index("-- MVTPROOFS-BEGIN"):core.index("-- MVTPROOFS-END")].replace("-- MVTPROOFS-BEGIN\n", "")
inst = checker(NAME, SA, AN, BN, cN, ORDER)
inst = (f"\n/-! ###### the 6-point weighted certificate `{NAME}`: zero-order and mean-value leaf tests, walk, cover ###### -/\n"
        + inst + "\n" + open(os.path.join(HERE, "cover_text.lean"), encoding="utf-8").read() + f"end {NS}\n\nend\n")
chk = pre + defs + core + inst
open(os.path.join(ROOT, f"checker_{NAME}.lean"), "w", encoding="utf-8").write(chk)
open(os.path.join(ROOT, f"{NAME}_params.txt"), "w").write(f"{Q} {SA} {','.join(map(str, AN))} {','.join(map(str, BN))} {cN} {NAME} 15 0 0\n")
open(os.path.join(ROOT, f"{NAME}_order.txt"), "w").write(",".join(map(str, ORDER)) + "\n")
print(f"[{NAME}] delta={DELTA} cN={cN} leaves={nleaves} (Z {nZ}, M {nM}) w={stw} d={std} points={len(PT)} "
      f"chunks={nthm[0]} (max {max(nchunk)} leaves) bits={nbits[0]} order={ORDER} data={len(data.encode())} "
      f"checker={len(chk.encode())} ({time.time()-t0:.0f}s)")
