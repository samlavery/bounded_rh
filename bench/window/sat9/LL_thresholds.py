"""Lemma LL thresholds: largest L with max_{delta <= 1/(4L)} P (2 delta cos(2 pi delta L) Qbar(delta) - h(0)) >= g(0),
Qbar(delta) = (1/delta) int_0^delta q (two-sided average), q on the 6001-point grid of common.py (trapezoid)."""
import numpy as np
from common import *
cq = np.concatenate([[0], np.cumsum(0.5 * (qa[1:] + qa[:-1]) * np.diff(al))])
def lhs(P, L):
    return max(P * (2 * (x / L) * np.cos(2 * np.pi * x) * np.interp(x / L, al, cq) / (x / L) - (1 - g0)) for x in np.linspace(0.01, 0.25, 481) if x / L <= 1)
print('q decreasing on [0,1]:', bool(np.all(np.diff(qa) <= 1e-15)), ' g0 = %.7f  h0 = %.7f' % (g0, 1 - g0))
for P in (8, 16, 32, 64, 128):
    lo, hi = 0.001, float(P)
    for _ in range(50):
        mid = (lo + hi) / 2
        if lhs(P, mid) >= g0: lo = mid
        else: hi = mid
    print('P=%3d: LL holds for L <= %.4f' % (P, lo))
