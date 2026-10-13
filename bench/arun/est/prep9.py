"""Round 5: certificate inputs for the 9-point B&B.  From cert9_final.json (integer weights over 10^8):
 (1) independent fresh re-check of c_true (new seeds), c_cert = floor(c_true (1 - 2e-4) 10^8)/10^8, the exact board rational
     kappa = (67216841 - B)/(10^8 - c_cert*10^8), and the side conditions;
 (2) the near-binding basin list (excess <= 2e-4) with Hessians, and a refinement map: for every local minimum with relative
     excess <= 1e-1, per-coordinate extents of the sublevel sets {Fw <= c (1 + thr)} (quadratic model, sqrt(2 (thr - ex) c (H^-1)_rr))
     for thr in {2e-4, 1e-3, 1e-2, 1e-1}, merged into intervals per coordinate.
usage: python3 prep9.py"""
import json, numpy as np
from fractions import Fraction
pre = open('lp_frame.py').read().split("t0 = time.time(); rng")[0]
pre = pre.replace("n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]", "n = 9; LO = 0.0; OUT = '/tmp/unused'")
exec(pre)
C9 = json.load(open('cert9_final.json'))
A_int = np.array([C9['a_int_over_1e8']['%d,%d' % (i, j)] for i, j in zip(PI, PJ)], dtype=np.int64)
B_int = np.array(C9['b_int_over_1e8'], dtype=np.int64); Bsum = int(B_int.sum())
a = A_int / 1e8; b = B_int / 1e8
rng = np.random.default_rng(777001)
ALPH = np.array([0.2, 0.5, 0.9, 1.04, 1.25, 1.5, 1.75, 1.97, 2.2, 2.6, 2.93, 3.3, 4.0, 6.0])
seeds = list(WORDS) + [ALPH[rng.integers(0, len(ALPH), m)] for _ in range(30000)] + [rng.uniform(0, 5, m) for _ in range(8000)]
global_min(a, b, seeds, rng, nrand=0)
mins = {}
for f, g in LASTMINS:
    fe = Fw_val(g, a, b, exact=True); key = tuple(np.round(g, 3))
    if key not in mins or fe < mins[key][0]: mins[key] = (fe, g)
mins = sorted(mins.values(), key=lambda v: v[0]); c = mins[0][0]
print('independent re-check: %d distinct local minima; c_true = %.10f (round-4 value %.10f, diff %+.1e)' % (len(mins), c, C9['c_true'], c - C9['c_true']), flush=True)
c_cert_int = int(np.floor(c * (1 - 2e-4) * 1e8)); kap_cert = Fraction(67216841 - Bsum, 10 ** 8 - c_cert_int)
kap_true = (0.67216841 - Bsum / 1e8) / (1 - c)
print('c_cert = %d / 10^8 (margin %.3e rel); kappa_cert = %d / %d = %.10f (gain over 0.6735478 %+.3e); kappa at c_true %.10f'
      % (c_cert_int, 1 - c_cert_int / 1e8 / c, kap_cert.numerator, kap_cert.denominator, float(kap_cert), float(kap_cert) - 0.6735478, kap_true), flush=True)
side = {'c_le_1_64': c_cert_int / 1e8 <= 1 / 64, 'wfun_17_20': float(wex(0.85)), 'min_wfun_on_0_17_20': float(wex(np.linspace(0, 0.85, 2001)).min()),
        'capacities': [int(A_int[SPAN == s].sum()) for s in range(1, 9)], 'a_nonneg': bool((A_int >= 0).all()), 'b_pos': bool((B_int > 0).all()),
        'symmetric': bool(all(A_int[k] == A_int[MP[k]] for k in range(NP))) and bool(all(B_int[r] == B_int[7 - r] for r in range(8)))}
print('side conditions:', side, flush=True)
def hess(g):
    h = 1e-4; Hm = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            def f(di, dj):
                gg = g.copy(); gg[i] += di; gg[j] += dj; return Fw_val(gg, a, b, exact=True)
            Hm[i, j] = Hm[j, i] = (f(h, h) - f(h, -h) - f(-h, h) + f(-h, -h)) / (4 * h * h)
    return Hm
THR = [2e-4, 1e-3, 1e-2, 1e-1]
basins = []; extents = {t: [[] for _ in range(m)] for t in THR}
for fe, g in mins:
    ex = fe / c - 1
    if ex > 1e-1: break
    Hm = hess(g); ev, evec = np.linalg.eigh(Hm)
    Hinv = np.linalg.pinv(Hm) if ev.min() > 1e-10 else None
    rec = {'F': fe, 'rel_excess': ex, 'gaps': [round(float(v), 6) for v in g], 'hess_eig': [float(v) for v in ev]}
    if ex <= 2e-4:
        rec['half_widths_at_2e-4'] = [float(v) for v in np.sqrt(2 * 2e-4 * c / np.maximum(ev, 1e-12))]
        rec['hess_eigvec'] = evec.T.tolist(); basins.append(rec)
    if Hinv is not None:
        for t in THR:
            if ex <= t:
                for r in range(m):
                    w = float(np.sqrt(max(0.0, 2 * (t - ex) * c * Hinv[r, r]))); extents[t][r].append((float(g[r]) - w, float(g[r]) + w))
def merge(iv):
    iv = sorted(iv); out = []
    for lo, hi in iv:
        if out and lo <= out[-1][1] + 1e-9: out[-1][1] = max(out[-1][1], hi)
        else: out.append([lo, hi])
    return [[round(lo, 5), round(hi, 5)] for lo, hi in out]
refmap = {('%.0e' % t): [merge(extents[t][r]) for r in range(m)] for t in THR}
nmin = {('%.0e' % t): sum(1 for fe, g in mins if fe / c - 1 <= t) for t in THR}
print('local minima with excess <= thr:', nmin, flush=True)
for t in THR:
    print('thr %.0e: per-coordinate intervals (coord 0..3; symmetric) ' % t + ' | '.join(str(refmap['%.0e' % t][r]) for r in range(4)), flush=True)
print('near-binding basins (excess <= 2e-4): %d' % len(basins), flush=True)
json.dump({'n': 9, 'pairs': [[int(i), int(j)] for i, j in zip(PI, PJ)], 'a_int_over_1e8': A_int.tolist(), 'b_int_over_1e8': B_int.tolist(), 'B_int': Bsum,
           'c_true': c, 'c_cert_int_over_1e8': c_cert_int, 'kappa_cert': [kap_cert.numerator, kap_cert.denominator], 'kappa_cert_float': float(kap_cert),
           'kappa_at_c_true': kap_true, 'H_lo': [67216841, 10 ** 8], 'side_conditions': side,
           'basins_excess_le_2e-4': basins, 'n_local_minima_by_excess': nmin, 'refinement_map_intervals': refmap,
           'refinement_suggestion': {'inside 2e-4 intervals': 'box edge <= 2^-10 (~9.8e-4; min half-width 1.3e-3)',
                                     'inside 1e-2 intervals': 'box edge 2^-7', 'inside 1e-1 intervals': 'box edge 2^-5', 'elsewhere': 'box edge 2^-3 or coarser; Fw - c >= 0.1 c'},
           'kernel': 'R8 window rwin8.json; wfun = (K/K(0))^2', 'notes': 'double precision; c_true from fresh multistart search (independent seeds from round 4)'},
          open('cert9_inputs.json', 'w'), indent=1)
