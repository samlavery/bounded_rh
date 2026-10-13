"""E30 = FOCUSED CORE PUSH, round 1 part (1) (lead, 2026-10-09).  Fixed BEFORE any run:
BOUND (identical to e29_theta.py, imported unchanged): lobe = int qT(|S_A|^2-4|V|^2) exact, T = (1-|al|/d)_+, d in {1/4,3/8,1/2};
  high band = theta-split per depth class (theta in {1,1/2,1/4}, best per al), class reference c_i = c(al, min depth of class),
  greedy classes of width DELTA0; between-class terms:
    PRIMARY   : DELTA0 = 0.25, pointwise bound -2(|S^i||S^j| + 4|V^i||V^j|)
    DIAG      : DELTA0 = 0.25, between-class terms exact (upper bound for any between-class estimate)
    ONECLASS  : DELTA0 = 10 (one class: c_* = c(y_min), S' = all depth differences)
  L = T_g^pp + max_d[lobe_d + high_d].
RANGE: depths in [0.8, 3] ONLY (deep pairs y > 3 are out of scope); P = 5, 6, 8, 12, 16, 24, 32.
SEEDS: arches (e23 refined e19 minimisers, e20 form), e25 sparse minimisers, hole configurations (min gap 1-1.25, flat 0.85 and
  arched 0.8-1.4), e9 stacks, e28/e29 minimisers with depths clipped to 3, random starts with depths in [0.8, 3].
PASS = min L >= 0 for every P (separately for each variant; PRIMARY is the one that counts).
PREDICTION (bridge-port, before the run): PRIMARY FAILS from P = 8 on: an arch spanning 0.8-1.6 has >= 4 depth classes, each a
  sparse sub-chain with in-band comb peaks, and the pointwise between-class bound throws away the cancellation between them.
  DIAG FAILS too (it keeps only 3/4 of each class's high-band (c^2-4)|V^i|^2, which is large for sparse sub-chains, while the
  truth nets it against exact cross terms).  ONECLASS FAILS on arches (the S' penalty for spread up to 2.2 at al near 1).
  All three may pass at P = 5, 6 (small spread)."""
import sys, json, numpy as np
from scipy.optimize import minimize
src = open('e29_theta.py').read().split("if __name__ == '__main__':")[0]
exec(src)
variant = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 30)
mode = 'primary' if variant in ('primary', 'oneclass') else 'diag'
DELTA0 = 10.0 if variant == 'oneclass' else 0.25
YMAX = 3.0
def search3(P, starts):
    best = (np.inf, None)
    for s0, y0 in starts:
        y0 = np.clip(y0, 0.8, YMAX)
        try:
            r = minimize(Lval, np.concatenate([s0, y0]), args=(P, mode), jac=True, method='L-BFGS-B',
                         bounds=[(None, None)] * P + [(0.8, YMAX)] * P, options={'maxiter': 2000})
            v = Lval(r.x, P, mode, False)[0]
        except (FloatingPointError, ValueError):
            continue
        if v < best[0]: best = (v, r.x.copy())
    return best
seeds = {}
def add(P, s, y): seeds.setdefault(int(P), []).append((np.asarray(s, float), np.clip(np.asarray(y, float), 0.8, YMAX)))
for P, c in json.load(open('e25_free.json')).items(): add(P, c['s'], c['y'])
for P in (5, 6, 8, 12, 16, 24, 32):
    for pre in ('e28_free_', 'e28_freediag_', 'e29_primary_', 'e29_diag_'):
        try: c = json.load(open('%s%d.json' % (pre, P))); add(P, c['s'], c['y'])
        except FileNotFoundError: pass
for P in (6, 8, 12, 16, 24, 32):
    c = json.load(open('e23_arch_%d.json' % P)); add(P, c['s'], c['y'])
for P in (16, 24, 32):
    c = json.load(open('e9_cfg_%d.json' % P)); add(P, c['s'], c['y'])
for P, (a, A, k) in {16: (0.6739, 0.9803, 0.804), 24: (0.7544, 1.2758, 0.790), 32: (0.7552, 1.7195, 0.804)}.items():
    t = np.arange(P) / (P - 1); add(P, a * np.arange(P), 0.8 + A * np.sin(np.pi * t) ** k)
for P in (5, 6, 8, 12, 16, 24, 32):
    t = np.arange(P) / (P - 1)
    for a in (1.0, 1.1, 1.25):
        s = a * np.arange(P) + rng.normal(0, 0.02, P); add(P, s, np.full(P, 0.85)); add(P, s, 0.8 + 0.6 * np.sin(np.pi * t) ** 0.8)
    for a in (0.6, 0.7, 0.76):
        add(P, a * np.arange(P), 0.8 + 0.8 * np.sin(np.pi * t) ** 0.8)
    for _ in range(6):
        s = np.sort(rng.uniform(0, rng.uniform(0.4, 2.0) * P, P)); add(P, s, rng.uniform(0.8, 3.0, P))
print('== variant %s (mode %s, DELTA0 %g), depths in [0.8, %g]' % (variant, mode, DELTA0, YMAX), flush=True)
allpass = True
for P in (5, 6, 8, 12, 16, 24, 32):
    b = search3(P, seeds[P]); s, y = b[1][:P], b[1][P:]; o = np.argsort(s)
    L1, L2 = report('min (%s) P=%d' % (variant, P), s[o], y[o])
    v = L2 if mode == 'diag' else L1
    allpass &= v >= 0
    print('      %s  s %s\n      y %s' % ('PASS' if v >= 0 else 'FAIL', np.round(s[o] - s[o][0], 3).tolist(), np.round(y[o], 3).tolist()), flush=True)
    json.dump({'s': s[o].tolist(), 'y': y[o].tolist(), 'L': float(v)}, open('e30_%s_%d.json' % (variant, P), 'w'))
print('VERDICT %s: %s' % (variant, 'PASS' if allpass else 'FAIL'), flush=True)
