#!/usr/bin/env python3
"""Where the leaves of a sizing run sit: margin (G(centre) - gmin)/gmin, box widths, gap ranges; AMWIN selects the
AM kernel (else the MT kernel from sevenw).  Usage: leafstat.py WEIGHTS.npz LEAVES.pkl [MT]"""
import os, sys, pickle
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "window", "amg")); sys.path.insert(0, os.path.join(HERE, ".."))
MT = len(sys.argv) > 3
if MT: from sevenw import w as wf
else: from amk import w as wf
wpath = sys.argv[1] if os.path.exists(sys.argv[1]) else os.path.join(HERE, "..", "..", "window", "amg", sys.argv[1])
d = np.load(wpath); a = np.array(d['aN'], float) / 1e8; b = np.array(d['bN'], float) / 1e8; gmin = float(d['vals'][0])
Q = len(b); PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
L = [(x[0], x[1]) for x in pickle.load(open(sys.argv[2], "rb"))]
SC = 32768.0
boxes = np.array([[[l, u] for (l, u) in box] for box, kind in L], float) / SC
kinds = np.array([k for _, k in L])
c = boxes.mean(axis=2); wid = boxes[:, :, 1] - boxes[:, :, 0]
G = c @ b
for t, (i, j) in enumerate(PAIRS):
    if a[t]: G += a[t] * wf(c[:, i:j].sum(axis=1))
m = (G - gmin) / gmin
refl = boxes[:, 0, 0] > boxes[:, Q - 1, 1]
print(f"{len(L)} leaves; kinds {dict(zip(*np.unique(kinds, return_counts=True)))}; reflected {refl.sum()}")
for lo, hi in [(-1, 0.05), (0.05, 0.1), (0.1, 0.2), (0.2, 0.5), (0.5, 1), (1, 1e9)]:
    s = (m >= lo) & (m < hi) & ~refl
    if s.sum(): print(f"  margin [{lo}, {hi}): {s.sum():6d}  (M {((kinds == 6) & s).sum()}, Z {((kinds == 1) & s).sum()})  median max-width {np.median(wid[s].max(axis=1)) * SC:.0f} units")
gs = c.sum(axis=1)
print("  total length sum g (centre): quantiles", np.round(np.quantile(gs[~refl], [0.1, 0.5, 0.9]), 3))
print("  per-gap centre medians", np.round(np.median(c[~refl], axis=0), 3))
