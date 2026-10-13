"""Convert cert9_final.json (lp9 optimum, integer weights over 10^8) into the rwin8.json format generalised to n = 9, for
bridge-port's sizer: n, B_SA, SA, cnum/cden (R8 window), H (string), aN dict, bN palindromic, eps_strong = TRUE minimum,
eps_lp_float, spans, window-only constants (copied from rwin8.json: same window), delta_* entries for the LINEAR chain
kappa = (H - B)/(1 - c) (no block length: m = null, phi = kappa_linear).  eps_strong = min of: the two round-4/5 fresh searches
(cert9_final / cert9_inputs) and famq.Family.global_min with the rwin.py lattice {1.04, 1.97, 2.91, 0.5}^8 (3 seeds) plus a
150k random cover (2 seeds) - the same oracle rwin.py uses for rwin8's eps_strong.
usage: python3 make_rwin9.py OUT.json"""
import sys, json, itertools, numpy as np
from fractions import Fraction
OUT = sys.argv[1]
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family
R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
C9 = json.load(open('cert9_final.json')); I9 = json.load(open('cert9_inputs.json'))
n, Q, SA = 9, 8, 10 ** 8
c = np.array(R8['cnum'], float) / R8['cden']; w = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(c))])
fam = Family(Q, c, w)
aN = np.array([C9['a_int_over_1e8']['%d,%d' % (i, j)] for (i, j) in fam.pairs], dtype=np.int64)
bN = np.array(C9['b_int_over_1e8'], dtype=np.int64); B_SA = int(bN.sum())
mir = [fam.pairs.index((n - 1 - j, n - 1 - i)) for (i, j) in fam.pairs]
assert all(aN[k] == aN[mir[k]] for k in range(fam.NP)), 'mirror symmetry aN(i,j) = aN(n-1-j, n-1-i)'
assert all(bN == bN[::-1]) and all(bN > 0) and B_SA == C9['B_int']
spans = [int(aN[cols].sum()) for cols in fam.blocks]; assert max(spans) <= 2 * SA and min(aN) >= 0
aR, bR = aN / SA, bN / SA
lat4 = np.array(list(itertools.product((1.04, 1.97, 2.91, 0.5), repeat=Q)))
floors = []
for s in (1, 2, 3):
    v, g, f = fam.global_min(aR, bR, coarse=400000, keep=250, seed=s, extra_starts=lat4); floors.append(('lattice seed %d' % s, float(v), g)); print(floors[-1][:2], np.round(g, 4), flush=True)
for s in (11, 12):
    v, g, f = fam.global_min(aR, bR, coarse=150000, keep=150, seed=s + 1000); floors.append(('random cover seed %d' % s, float(v), g)); print(floors[-1][:2], np.round(g, 4), flush=True)
floors.append(('fresh search round 4 (cert9_final)', float(C9['c_true']), None)); floors.append(('fresh search round 5 (cert9_inputs)', float(I9['c_true']), None))
eps = min(f[1] for f in floors)
print('eps_strong = %.15f (min of %s)' % (eps, ['%.13f' % f[1] for f in floors]), flush=True)
res = dict(n=n, B_SA=B_SA, SA=SA, cnum=R8['cnum'], cden=R8['cden'], H=R8['H'], aN={f'{i},{j}': int(aN[k]) for k, (i, j) in enumerate(fam.pairs)},
           bN=[int(x) for x in bN], eps_strong=eps, eps_lp_float=float(json.load(open('lp9_lo0.json'))['c_true']), spans=spans,
           sum_abs=R8['sum_abs'], vd_bound=R8['vd_bound'], vdd_bound=R8['vdd_bound'], v0=R8['v0'], vmin=R8['vmin'], pv_v=R8['pv_v'], pv_sqrt_v_over_M=R8['pv_sqrt_v_over_M'],
           window_ref='R8 window (bench/window/rwin8.json cnum/cden; same window as PC8C5BF and MOP)',
           chain='MOP linear chain kappa = (H_lo - B)/(1 - c), H_lo = 67216841/10^8 (no block length m)',
           source='window-scope lp9 optimum (bench/arun/est/lp_frame.py -> lp9_lo0.json -> cert_final.py -> cert9_final.json); mirror-symmetric; capacities exact',
           root_hints_near_binding=[b['gaps'] for b in I9['basins_excess_le_2e-4']])
for d in (0.0, 0.00005, 0.0002, 0.0005, 0.001):
    cc = int(np.floor(eps * (1 - d) * SA)); k = Fraction(67216841 - B_SA, SA - cc)
    res[f'delta_{d}'] = dict(cN=cc, m=None, phi=float(k), kappa_rational=[k.numerator, k.denominator])
json.dump(res, open(OUT, 'w'), indent=1)
print(json.dumps({k: v for k, v in res.items() if k not in ('aN', 'root_hints_near_binding')}, indent=1))
