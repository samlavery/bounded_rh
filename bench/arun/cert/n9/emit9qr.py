#!/usr/bin/env python3
"""Certificate data for the pair-cell eight-point certificate (fixed-width walk, PCELL.md / TZ.md), with re-verification.

1. Replays the sizer's dump as the kernel walks it (size8pz REPLAY): at every node the T1 tightening of the incoming cell
   must reproduce the dump's cell; a split recomputes its children from the tightened cell and the axis; every leaf is
   re-verified with the exact integer leaf check on the BUILT tables.  Any failure aborts.
2. Encodes every root's walk in the fixed-width layout and decodes it back; the decode must reproduce every node.
3. Writes DATA.json: weights, cN, settings, root cells, per-root walks (hex, LSB-first, bit counts), the tables (w pyramid
   TOP/BK, derivative pair table TOPD/BKD, convex regions REG, sparse points), and the per-gap root covers.
Usage (same env as the sizing run): emit8pz.py W.json DELTA DUMP.pkl OUT.json"""
import os, sys, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
# (bridge-port, 2026-10-10: emit9pz.py = mvt-engine's eight/am8/emit8pz.py with the split-axis field sized for any Q,
#  AXB = bit_length(Q + NC - 1): 5 bits at Q = 7 (output unchanged), 6 at Q = 8, as genpcellQ.py's AXB.)
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8")
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
WJ, DELTA, DUMP, OUT = sys.argv[1], float(sys.argv[2]), sys.argv[3], sys.argv[4]
os.environ["REPLAY"] = DUMP
os.environ["SQ"] = str(json.load(open(WJ))["n"] - 1)   # the sizer's gap count (size8pz reads it at import)
import size9pr as S   # (emit9qr.py, bridge-port 10-11) size9pz + the RCUT root-partition hook; RCUT must match the sizing run
assert os.environ.get("RCUT"), "emit9qr replays an RCUT tree: set RCUT as in the sizing run"
from amk import conv_ok, chain as w2chain
from emit_tables import PairTable
J = json.load(open(WJ)); n_ = J["n"]
PAIRS = S.PAIRS; Q = S.Q; NP = len(PAIRS)
aN = [int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]; bN = [int(x) for x in J["bN"]]
gmin = float(J["eps_strong"]) * 1e8; cN = int(gmin * (1 - DELTA))
SC = S.SC
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: c_ = w2chain(_s, x_); assert c_ is not None; REGS.append((_s, x_, c_)); _s = None
t0 = time.time()
r = S.run(cN, aN, bN, JCQ=8, basins=(), PED=6, DFUEL=14, DLO=int(os.environ["DLO"]), DHI=int(os.environ["DHI"]),
          regions=[(a_, b_) for (a_, b_, _) in REGS], centers=(), CRAD=0, WMIN=int(os.environ["WMIN"]), MTEST=3, NPT=9)
assert r is not None
print(f"replay: {r['RPL']}; leaves {r['nleaves']} kinds {r['kinds']}; verification failures {r['bad']} ({time.time() - t0:.0f}s)", flush=True)
assert r['bad'] == 0, "verification failed"
LS = int(os.environ.get("LSC", "1024")); LB = LS.bit_length() - 1; JSH = int(os.environ.get("JSH", "3")); JB = JSH + 2
NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]; RANK = {t: k for k, t in enumerate(NADJ)}
AXB = max(1, (Q + len(NADJ) - 1).bit_length())   # the split-axis field width (5 at Q = 7, 6 at Q = 8)
assert len(NADJ) <= 32, "the multiplier's constraint code is 5 bits"
# (bridge-port, emit9q.py = emit9pz.py with the rank-1 quantisation fields from the sizing env: λ width LB = log2 LSC (as
#  before), the multiplier quantum SIGSH = YFRAC (was a fixed 14), the Yq width QB (env QB, default 12; was a fixed 12).
#  The Lean decoders read these widths as parameters (dec4F lb, ydec qb, Inst SIG); no checker change.)
SIGSH_ = int(os.environ.get("YFRAC", "14")); QB_ = int(os.environ.get("QB", "12"))
BSPLIT = os.environ.get("BSPLIT") == "1"   # split layout [1][axis 5][mode 1]: mode 1 cuts at the region boundary nearest the midpoint
ACT = [t for t in range(NP) if aN[t] > 0]
# ---- the fixed-width walk
def put(bits, v, n):
    assert 0 <= v < (1 << n), (v, n)
    for k in range(n): bits.append((v >> k) & 1)
def enc(nd, bits):
    if nd[0] == 'split':
        ax = nd[2]; put(bits, 1, 1); put(bits, ax if ax < Q else Q + RANK[ax - Q], AXB)
        if BSPLIT: put(bits, 1 if nd[3] else 0, 1)            # the split mode: midpoint or region boundary
        enc(nd[4], bits); enc(nd[5], bits); return
    _, cell, kind, pay = nd
    if kind == 7: return                                   # empty: no bits
    put(bits, 0, 1)
    if kind == 0: return                                   # reflected
    assert kind == 6, kind
    put(bits, 0, 1)
    mc, Ys = pay
    for t in ACT:
        k, j1, j2, lam = mc[t]; put(bits, k, 2)
        if k >= 1: put(bits, j1, JB)
        if k == 3: put(bits, j2, JB)
        if k >= 2: put(bits, lam, LB)
    for (t, side) in sorted(Ys):
        put(bits, 1, 1); put(bits, RANK[t], 5); put(bits, side, 1); put(bits, Ys[(t, side)], QB_)
    put(bits, 0, 1)
def dec(nd, bits, pos):
    """decode against the tree: every field read must equal the node's (the kernel would read exactly these bits)"""
    def get(n):
        nonlocal pos
        v = sum(bits[pos + k] << k for k in range(n)); pos += n; return v
    def go(nd):
        if nd[0] == 'split':
            assert get(1) == 1; ax = get(AXB); assert ax == (nd[2] if nd[2] < Q else Q + RANK[nd[2] - Q])
            if BSPLIT: assert get(1) == (1 if nd[3] else 0)
            go(nd[4]); go(nd[5]); return
        _, cell, kind, pay = nd
        if kind == 7: return
        assert get(1) == 0
        if kind == 0: return
        assert get(1) == 0
        mc, Ys = pay
        for t in ACT:
            k = get(2); assert k == mc[t][0]
            if k >= 1: assert get(JB) == mc[t][1]
            if k == 3: assert get(JB) == mc[t][2]
            if k >= 2: assert get(LB) == mc[t][3]
        got = {}
        while get(1):
            c = get(5); side = get(1); got[(NADJ[c], side)] = get(QB_)
        assert got == Ys
    go(nd)
    return pos
walks = []; nbits = 0
for tup, nd in r['nodes'].items():
    bits = []; enc(nd, bits); end = dec(nd, bits, 0); assert end == len(bits)
    walks.append(dict(root=list(tup), cell=[list(r['bads'][g_][tup[g_]]) for g_ in range(Q)],
                      nbits=len(bits), hex=hex(sum(b << k for k, b in enumerate(bits)))))
    nbits += len(bits)
print(f"walks: {len(walks)} roots, {nbits} bits = {nbits / 4 / 1e3:.1f} KB hex; encode/decode round trip OK", flush=True)
# ---- tables
P, PP, PM = r['P'], r['PP'], r['PM']
DT = PairTable(PP, PM)
RGK = {}
for (a_, b_, c_) in REGS:
    k_ = (a_ + 16384) >> 15
    if k_ < 16: RGK[k_] = (a_, b_, [list(x) if isinstance(x, (list, tuple)) else x for x in c_])
pts = sorted(r['pts'])
ptw, ptd = r['built'][3], r['built'][4]
points = [[int(x), int(ptw(x) | (ptd(x)[0] << 32) | (ptd(x)[1] << 64))] for x in pts]
covers = [[[int(l), int(u), bool(cl)] for (l, u, cl) in sorted([(l, u, True) for (l, u) in cv[0]] + [(l, u, False) for (l, u) in cv[1]])]
          for cv in r['covers']]
D = dict(name="pair-cell eight-point certificate", window=os.path.basename(WJ), delta=DELTA, cN=cN, SA=100000000,
         pairs=[f"{i},{j}" for (i, j) in PAIRS], aN=aN, bN=bN,
         settings={k: os.environ.get(k) for k in ("TWOGRID", "GSH", "JSH", "WMIN", "DLO", "DHI", "PLO", "MINR", "YFRAC", "LSC",
                                                   "NR", "TRIPLE", "PERSIST", "ZEXT", "SPLIT", "PFK", "MINPW", "NOZ",
                                                   "TCLOSE", "MINSPLIT", "BSPLIT", "BMARG", "NOREFL")},
         layout=f"split [1][axis {AXB}: 0..{Q - 1} gaps, {Q}..{Q + len(NADJ) - 1} sum ranks]; leaf [0], reflected: nothing, else [kind 1: 0 = M]; "
                f"M: per active pair in pair order [kappa 2][j1 {JB} if kappa>=1][j2 {JB} if kappa=3][lambda {LB} if kappa>=2], "
                "then multipliers [1][c 5][side 1][Yq 12] closed by [0]; empty nodes: no bits; bits LSB-first",
         S=[int(x) for x in r['S']], covers=covers, walks=walks,
         params=dict(SC=SC, U=10**10, U1=10**9, KU1=2 * 10**9, RU=10, LS_kernel=1024, LB=LB, JSH=JSH, JB=JB,
                     GSH=int(os.environ.get("GSH", "8")), PLO=(1 << JSH) + 1, SIGSH=SIGSH_, QB=QB_, ZEXT=int(os.environ.get("ZEXT", "0")),
                     BSPLIT=int(BSPLIT), BMARG=int(os.environ.get("BMARG", "64")), BND=sorted({z for (a_, b_, _) in REGS for z in (a_, b_)}),
                     w_pyr=dict(PE=5, PB=10, KT=19, MAXA=4, EB=32, FUEL=14), d_pyr=dict(PE=6, PB=10, KT=19, MAXA=4, FUEL=14)),
         tables=dict(TOP=hex(P.TOPN), BK={str(j): hex(v) for j, v in sorted(P.BKN.items())},
                     TOPD=hex(DT.TOPN), BKD={str(j): hex(v) for j, v in sorted(DT.BKN.items())},
                     REG={str(k): [RGK[k][0], RGK[k][1], RGK[k][2]] for k in sorted(RGK)},
                     points=[[x, hex(v)] for x, v in points], w_finest=P.stats()['finest'], d_finest=PP.stats()['finest']),
         counts=dict(leaves=r['nleaves'], kinds={str(k): v for k, v in r['kinds'].items()}, splits=r['nsplit'],
                     points=len(points), walk_bits=nbits))
json.dump(D, open(OUT, "w"))
if r.get('ZLOG'): json.dump(r['ZLOG'], open(OUT.replace(".json", "_zlog.json"), "w"), indent=1)
print(f"wrote {OUT}: {os.path.getsize(OUT) / 1e6:.2f} MB json; points {len(points)}, w {P.stats()['finest']} cells, "
      f"d {PP.stats()['finest']} cells", flush=True)
