#!/usr/bin/env python3
"""Kernel-cost benchmark of the mean-value certificate: size at DELTA, build the tables, and emit MvtBench.lean
(import MvtDefs; the instance's computational definitions; the tables; table checks; a sample of walk chunks, each a
`decide +kernel` evaluation).  Prints the (Z, M, split) counts of every emitted chunk.
Usage: bench_gen.py DELTA NCHUNK [CH]"""
import os, sys, itertools, random
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import size_m
from size_m import run, AN, BN, SA, Q, PAIRS
from emit_tables import pyr_consts, pt_blocks, pt_consts, pt_lookup, PairTable, pair_consts
import gen_inst
DELTA = float(sys.argv[1]); NCH = int(sys.argv[2]); CH = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
cN = round(358287 * (1 - DELTA))
r = run(cN, JC=gen_inst.JC, corner=gen_inst.CORNER, dmin=gen_inst.DMIN, PED=gen_inst.PED)
assert r and r["bad_leaves"] == 0
P, PP, PM, PT = r["P"], r["PP"], r["PM"], r["PT"]
PB = pt_blocks(PT)
for x, v in PT.items(): assert pt_lookup(PB, x) == v
ORDER = [5, 12, 9, 0, 4, 14, 3, 7, 2, 8, 11, 1, 10, 13, 6]
L = ["import MvtDefs", "", "set_option maxRecDepth 100000", "set_option profiler true", "set_option profiler.threshold 50"]
L.append(gen_inst.inst_defs("MvtB", SA, AN, BN, cN, ORDER))
L.append("end Zeta23Ext.Bridge.ThreePoint.MvtB\n\nend\n")
L.append("noncomputable section\n\nnamespace Zeta23Ext.Bridge.ThreePoint.MvtBData\n\nopen Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD Zeta23Ext.Bridge.ThreePoint.MvtB\n")
DT = PairTable(PP, PM)
L.append(pyr_consts(P, "TOP", "BK")); L.append(pair_consts(DT, "TOPD", "BKD")); L.append(pt_consts(PB))
if os.environ.get("CHK"): L.append("theorem chkD : allFrom 0 512 (fun j => blockOk2 (BKD j) j) = true := by decide +kernel")
if os.environ.get("CHK"): L.append("theorem chkW : allFrom 0 512 (fun j => blockOk (BK j) j) = true := by decide +kernel")
if os.environ.get("CHK"): L.append("theorem chkPT : allFrom 0 512 (fun j => ptBlockOk (PTB j) j) = true := by decide +kernel")
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def counts(nd, c):
    if nd[0] == 'leaf': c[nd[2]] += 1
    else: c[3] += 1; counts(nd[4], c); counts(nd[5], c)
def height(nd): return 1 if nd[0] == 'leaf' else 1 + max(height(nd[4]), height(nd[5]))
chunks = []
def collect(nd):
    if nleaf(nd) <= CH: chunks.append(nd); return
    collect(nd[4]); collect(nd[5])
for nd in r["nodes"].values(): collect(nd)
def cnt(nd):
    c = [0, 0, 0, 0]; counts(nd, c); return c
byM = sorted(chunks, key=lambda nd: -cnt(nd)[2])[:NCH // 2]
byZ = sorted([nd for nd in chunks if cnt(nd)[2] * 10 < cnt(nd)[1]], key=lambda nd: -cnt(nd)[1])[:NCH - NCH // 2]
sel = byM + byZ
print(f"{len(chunks)} chunks; sample:")
for k, nd in enumerate(sel):
    bl = [0]; gen_inst.walk_code(nd, bl)
    bits = sum(1 << i for i, b in enumerate(bl) if b)
    c = [0, 0, 0, 0]; counts(nd, c)
    coords = " ".join(f"{l} {u}" for (l, u) in nd[1])
    L.append(f"theorem bw{k} : walk TOP BK TOPD BKD PTB {bits} {height(nd) + 1} 1 {coords} = {len(bl)} := by decide +kernel")
    print(f"bw{k}: trivial {c[0]} Z {c[1]} M {c[2]} splits {c[3]}")
L.append("\nend Zeta23Ext.Bridge.ThreePoint.MvtBData\n\nend\n")
open(os.path.join(HERE, "MvtBench.lean"), "w", encoding="utf-8").write("\n".join(L))
print("tables:", r["stats"], "point blocks", len(PB), "bytes", len("\n".join(L).encode()))
