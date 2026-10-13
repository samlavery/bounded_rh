#!/usr/bin/env python3
"""Sizing only (floats, no certification): leaf counts of the weighted six-point bisection under
  Z  : the current zero-order leaf test (each pair term bounded by its own min of w over its pair-sum interval), and
  Z+T: Z or the centered second-order test at the box centre m with half-widths h:
       G(m) - sum_r |dG/dg_r(m)| h_r - 1/2 sum_t a_t sup|w''|(I_t) (sum_{r in t} h_r)^2  >=  c.
Same covers, roots, half-space and passfirst axis rule as size_pyr.run.  Usage: size_taylor.py DELTA [MODE]
MODE: Z | ZT (default both)."""
import sys, time, itertools, math
import numpy as np
sys.setrecursionlimit(100000)
import size_pyr as sp
SC, Q, PAIRS, AN, BN = sp.SC, sp.Q, sp.PAIRS, sp.AN, sp.BN
S2 = math.sqrt(2.0); GAM = (1 / S2) * math.cos(1 / S2) / math.sin(1 / S2)
B0 = 1 / S2

def f_of(x):
    b = np.pi * x
    num = np.cos(b) - 2 * GAM * b * np.sin(b); den = 1 - 2 * b * b
    out = np.empty_like(b); far = np.abs(b - B0) > 2e-3
    out[far] = num[far] / den[far]
    # removable point: average of the symmetric neighbours at +-2e-3 (f is smooth; sizing only)
    if (~far).any():
        bl = B0 - 2e-3; br = B0 + 2e-3
        fl = (math.cos(bl) - 2 * GAM * bl * math.sin(bl)) / (1 - 2 * bl * bl)
        fr = (math.cos(br) - 2 * GAM * br * math.sin(br)) / (1 - 2 * br * br)
        t = (b[~far] - bl) / (br - bl); out[~far] = fl + t * (fr - fl)
    return out

def build_grid(xmax_units):
    n = np.arange(0, xmax_units + 3, dtype=np.float64)
    x = n / SC
    w = f_of(x) ** 2
    h = 1.0 / SC
    w1 = np.gradient(w, h)
    w2 = np.gradient(w1, h)
    # smooth the finite-difference noise of w'' with a running max over +-8 units (conservative for sup)
    k = 8
    a2 = np.abs(w2)
    pad = np.pad(a2, k, mode="edge")
    sup2 = np.max(np.lib.stride_tricks.sliding_window_view(pad, 2 * k + 1), axis=1)
    return w, w1, sup2

def run(delta, mode):
    cN = round(358287 * (1 - delta))
    adj = [AN[PAIRS.index((r, r + 1))] for r in range(Q)]
    S = [-(-(4 * cN * SC) // (BN[r] * 4 * sp.QUARTER)) * sp.QUARTER for r in range(Q)]
    covers = [sp.phase1(cN, adj[r], S[r]) for r in range(Q)]
    bads = [cv[1] for cv in covers]
    xmax = sum(S) + 16
    W, W1, SUP2 = build_grid(xmax)
    # block mins for range-min over w (block 256) to keep long ranges cheap
    BLK = 256
    nb = len(W) // BLK + 1
    Wp = np.pad(W, (0, nb * BLK - len(W)), constant_values=np.inf)
    bmin = Wp.reshape(nb, BLK).min(axis=1)
    S2p = np.pad(SUP2, (0, nb * BLK - len(SUP2)), constant_values=0)
    bmax2 = S2p.reshape(nb, BLK).max(axis=1)
    def rmin(lo, hi):
        if hi - lo < 4 * BLK: return float(W[lo:hi + 1].min())
        a = -(-lo // BLK); b = (hi + 1) // BLK
        return float(min(W[lo:a * BLK].min() if a * BLK > lo else np.inf, bmin[a:b].min(), W[b * BLK:hi + 1].min() if hi + 1 > b * BLK else np.inf))
    def rmax2(lo, hi):
        if hi - lo < 4 * BLK: return float(SUP2[lo:hi + 1].max())
        a = -(-lo // BLK); b = (hi + 1) // BLK
        return float(max(SUP2[lo:a * BLK].max() if a * BLK > lo else 0, bmax2[a:b].max(), SUP2[b * BLK:hi + 1].max() if hi + 1 > b * BLK else 0))
    def interp(arr, xu):
        i = int(xu); t = xu - i
        return arr[i] * (1 - t) + arr[i + 1] * t
    def zlow(box):
        s = sum(BN[r] * box[r][0] for r in range(Q)) / SC
        for t, (i, j) in enumerate(PAIRS):
            lo = sum(box[r][0] for r in range(i, j)); hi = sum(box[r][1] for r in range(i, j))
            s += AN[t] * rmin(lo, hi)
        return s
    def tlow(box):
        m = [(b[0] + b[1]) / 2 for b in box]; h = [(b[1] - b[0]) / 2 / SC for b in box]
        val = sum(BN[r] * m[r] for r in range(Q)) / SC
        grad = list(BN)
        rem = 0.0
        for t, (i, j) in enumerate(PAIRS):
            su = sum(m[r] for r in range(i, j))
            val += AN[t] * interp(W, su)
            d = AN[t] * interp(W1, su)
            for r in range(i, j): grad[r] += d
            lo = sum(box[r][0] for r in range(i, j)); hi = sum(box[r][1] for r in range(i, j))
            rem += 0.5 * AN[t] * rmax2(lo, hi) * sum(h[r] for r in range(i, j)) ** 2
        return val - sum(abs(grad[r]) * h[r] for r in range(Q)) - rem
    def lower(box):
        z = zlow(box)
        if mode == "Z" or z >= cN: return z
        return max(z, tlow(box))
    count = [0]
    WFRAC = 4
    def choose_axis(box):
        w = [b[1] - b[0] for b in box]; mw = max(w); best = None
        for k in range(Q):
            if w[k] == 0: continue
            mid = (box[k][0] + box[k][1]) // 2
            a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
            la, lb2 = lower(tuple(a)), lower(tuple(b2))
            both = la >= cN and lb2 >= cN
            if w[k] * WFRAC < mw and not both: continue
            score = ((la >= cN) + (lb2 >= cN), la + lb2)
            if best is None or score > best[0]: best = (score, k)
        return best[1]
    def sub(box, depth=0):
        if box[0][0] > box[Q - 1][1]: count[0] += 1; return True
        if sum(BN[r] * box[r][0] for r in range(Q)) >= cN * SC: count[0] += 1; return True
        if lower(box) >= cN: count[0] += 1; return True
        if depth > 70 or count[0] > 3 * 10**6 or max(b[1] - b[0] for b in box) <= 1: return False
        k = choose_axis(box); mid = (box[k][0] + box[k][1]) // 2
        a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
        return sub(tuple(a), depth + 1) and sub(tuple(b2), depth + 1)
    t0 = time.time()
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        if not sub(box):
            print(f"delta={delta} mode={mode}: FAIL/cap at {count[0]} leaves ({time.time()-t0:.0f}s)", flush=True); return None
    print(f"delta={delta} mode={mode}: {count[0]} leaves ({time.time()-t0:.0f}s)", flush=True)
    return count[0]

if __name__ == "__main__":
    delta = float(sys.argv[1]); modes = [sys.argv[2]] if len(sys.argv) > 2 else ["Z", "ZT"]
    for mo in modes: run(delta, mo)
