"""Sizer file for the re-optimised n = 8 certificate (cert8_final.json) in rwin8.json's format: mirror symmetry asserted,
eps_strong = min(lattice oracle famq {1.04,1.97,2.91,0.5}^7 x 3 seeds, cert8 fresh-search value), delta entries incl. 3e-5.
usage: python3 make_rwin8_reopt.py OUT.json"""
import sys, json, itertools, numpy as np
from fractions import Fraction
OUT = sys.argv[1]
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family
R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
C8 = json.load(open('cert8_final.json'))
n, Q, SA = 8, 7, 10 ** 8
c = np.array(R8['cnum'], float) / R8['cden']; w = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(c))])
fam = Family(Q, c, w)
aN = np.array([C8['a_int_over_1e8']['%d,%d' % (i, j)] for (i, j) in fam.pairs], dtype=np.int64)
bN = np.array(C8['b_int_over_1e8'], dtype=np.int64); B_SA = int(bN.sum()); assert B_SA == C8['B_int'] == 406753
mir = [fam.pairs.index((n - 1 - j, n - 1 - i)) for (i, j) in fam.pairs]
assert all(aN[k] == aN[mir[k]] for k in range(fam.NP)), 'mirror symmetry'
assert all(bN == bN[::-1]) and all(bN > 0)
spans = [int(aN[cols].sum()) for cols in fam.blocks]; assert max(spans) <= 2 * SA and aN.min() >= 0
aR, bR = aN / SA, bN / SA
lat4 = np.array(list(itertools.product((1.04, 1.97, 2.91, 0.5), repeat=Q)))
lat = []
for s in (1, 2, 3):
    v, g, f = fam.global_min(aR, bR, coarse=400000, keep=250, seed=s, extra_starts=lat4); lat.append(float(v)); print('lattice seed %d: %.15f at %s' % (s, v, np.round(g, 4)), flush=True)
eps = min(lat + [float(C8['c_true'])])
print('eps_strong %.15f (lattice %s, cert8 fresh %.15f)' % (eps, ['%.15f' % v for v in lat], C8['c_true']), flush=True)
res = dict(n=n, B_SA=B_SA, SA=SA, cnum=R8['cnum'], cden=R8['cden'], H=R8['H'], aN={f'{i},{j}': int(aN[k]) for k, (i, j) in enumerate(fam.pairs)},
           bN=[int(x) for x in bN], eps_strong=eps, spans=spans,
           sum_abs=R8['sum_abs'], vd_bound=R8['vd_bound'], vdd_bound=R8['vdd_bound'], v0=R8['v0'], vmin=R8['vmin'], pv_v=R8['pv_v'], pv_sqrt_v_over_M=R8['pv_sqrt_v_over_M'],
           window_ref='R8 window (bench/window/rwin8.json)', chain='MOP linear chain kappa = (H_lo - B)/(1 - c), H_lo = 67216841/10^8',
           source='window-scope re-optimised n = 8 (lp_frame.py -> lp8_lo0.json -> cert_final.py -> cert8_final.json)')
for d in (0.0, 0.00003, 0.00005, 0.0002):
    cN = int(np.floor(eps * (1 - d) * SA)); k = Fraction(67216841 - B_SA, SA - cN)
    res[f'delta_{d}'] = dict(cN=cN, m=None, phi=float(k), kappa_rational=[k.numerator, k.denominator], gain_over_0_6735478=float(k) - 0.6735478)
json.dump(res, open(OUT, 'w'), indent=1)
print(json.dumps({k: v for k, v in res.items() if k.startswith('delta') or k in ('B_SA', 'bN', 'spans', 'eps_strong')}, indent=1))
