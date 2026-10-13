"""Round 4: concrete optimised certificates.  Rounds the LP weights (lp{n}_lo0.json) to integers over 10^8 (a by floor, so the
capacity holds exactly; b to nearest), then a FRESH global search of Fw for the rounded weights (exact kernel in the final
evaluation), kappa = (H_lo - B)/(1 - c_true), basin structure, Hessians at the near-binding minima, and basin half-widths.
usage: python3 cert_final.py N"""
import sys, json, itertools, numpy as np
from scipy.optimize import minimize
N = int(sys.argv[1])
pre = open('lp_frame.py').read().split("t0 = time.time(); rng")[0]
pre = pre.replace("n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]", "n = %d; LO = 0.0; OUT = '/tmp/unused'" % N)
exec(pre)
J = json.load(open('lp%d_lo0.json' % N))
assert [tuple(p) for p in J['pairs']] == list(zip(PI.tolist(), PJ.tolist()))
a_f = np.array(J['a']); b_f = np.array(J['b'])
A_int = np.floor(a_f * 1e8 + 1e-6).astype(np.int64); B_int = np.rint(b_f * 1e8).astype(np.int64)
for k in range(NP): assert A_int[k] == A_int[MP[k]], 'symmetry'
for r in range(m): assert B_int[r] == B_int[m - 1 - r], 'symmetry b'
caps = [int(A_int[SPAN == s].sum()) for s in range(1, N)]
assert max(caps) <= 2 * 10 ** 8, caps
a = A_int / 1e8; b = B_int / 1e8; Bsum = int(B_int.sum())
print('n=%d: rounded weights: B = %d / 10^8 (float LP B %.9f); capacities (x10^8) %s; nonzero a %d of %d'
      % (N, Bsum, b_f.sum(), caps, int((A_int > 0).sum()), NP), flush=True)
rng = np.random.default_rng(20261010)
ALPH = np.array([0.3, 0.7, 1.04, 1.3, 1.6, 1.97, 2.4, 2.93, 3.5, 5.0])
seeds = list(WORDS) + [ALPH[rng.integers(0, len(ALPH), m)] for _ in range(20000)] + [rng.uniform(0, 4, m) for _ in range(5000)] + [rng.uniform(0, 40, m) for _ in range(2000)]
f0, g0 = global_min(a, b, seeds, rng, nrand=0)
mins = sorted([(Fw_val(g, a, b, exact=True), g) for f, g in LASTMINS], key=lambda v: v[0])
# perturbation pass around every basin within 1e-3 of the minimum
cmin0 = mins[0][0]; near = [g for f, g in mins if f <= cmin0 * (1 + 1e-3)]
pert = [g + rng.normal(0, s, m) for g in near for s in (0.01, 0.05, 0.2) for _ in range(20)]
f1, g1 = global_min(a, b, pert, rng, nrand=0)
mins2 = sorted([(Fw_val(g, a, b, exact=True), g) for f, g in LASTMINS], key=lambda v: v[0])
allm = {}
for f, g in mins + mins2:
    key = tuple(np.round(g, 3))
    if key not in allm or f < allm[key][0]: allm[key] = (f, g)
mins = sorted(allm.values(), key=lambda v: v[0]); c = mins[0][0]
H_LO = 0.67216841; kap = (H_LO - Bsum / 1e8) / (1 - c); kap_lp = J['kappa_Hfloor']
print('fresh search: %d distinct local minima; c_true(rounded) = %.10f at %s; LP c_true (unrounded) %.10f'
      % (len(mins), c, np.round(mins[0][1], 4), J['c_true']), flush=True)
print('kappa_%d (rounded, true min, H floor) = %.9f ; unrounded LP %.9f ; rounding cost %+.2e ; gain over 0.6735478 %+.3e'
      % (N, kap, kap_lp, kap - kap_lp, kap - 0.6735478), flush=True)
def hess(g):
    h = 1e-4; Hm = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            def f(di, dj):
                gg = g.copy(); gg[i] += di; gg[j] += dj; return Fw_val(gg, a, b, exact=True)
            v = (f(h, h) - f(h, -h) - f(-h, h) + f(-h, -h)) / (4 * h * h); Hm[i, j] = Hm[j, i] = v
    return Hm
rows = []
for dl in (1e-6, 1e-5, 5e-5, 2e-4, 1e-3, 5e-3):
    k = sum(1 for f, g in mins if f <= c * (1 + dl)); print('   basins within %.0e rel: %d' % (dl, k), flush=True)
nb = [(f, g) for f, g in mins if f <= c * (1 + 2e-4)]
mg = min(float(g.min()) for f, g in nb)
print('near-binding basins at 2e-4: %d; minimal gap in them %.4f; maximal gap %.4f' % (len(nb), mg, max(float(g.max()) for f, g in nb)), flush=True)
wid = []
for f, g in nb:
    ev = np.linalg.eigvalsh(hess(g)); hw = np.sqrt(2 * 2e-4 * c / np.maximum(ev, 1e-12))
    wid.append((float(ev.min()), float(ev.max()), float(hw.min()), float(hw.max())))
    rows.append({'F': f, 'gaps': g.tolist(), 'rel_excess': f / c - 1, 'hess_eig': ev.tolist()})
    print('   F %.10f (+%.1e) gaps %s | Hessian eig %.3g..%.3g | half-width at 2e-4: %.2e..%.2e' % (f, f / c - 1, np.round(g, 3), ev.min(), ev.max(), hw.min(), hw.max()), flush=True)
json.dump({'n': N, 'a_int_over_1e8': {('%d,%d' % (i, j)): int(v) for i, j, v in zip(PI, PJ, A_int)}, 'b_int_over_1e8': B_int.tolist(), 'B_int': Bsum,
           'c_true': c, 'kappa_Hfloor': kap, 'kappa_LP_unrounded': kap_lp, 'near_binding_2e-4': rows, 'n_local_minima': len(mins)},
          open('cert%d_final.json' % N, 'w'), indent=1)
