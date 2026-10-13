"""Round 7 finalisation: round a separation-LP certificate (sepF<T>.json) with cert9's rules (a floor, capacity exact, mirror
symmetry; b nearest, palindromic, > 0), eps_strong = true minimum (famq lattice oracle {1.04,1.97,2.91,0.5}^8, 3 seeds, plus a fresh
word/alphabet/uniform search), basin counts by relative excess, kappa at c_true and certified at delta 5e-5 / 2e-4, and the sizer
JSON in rwin9_lp9.json's format.  usage: python3 make_rwin9_t.py T(570|562|555) OUT.json"""
import sys, json, itertools, numpy as np
from fractions import Fraction
T, OUTJ = sys.argv[1], sys.argv[2]
pre = open('lp_frame.py').read().split("t0 = time.time(); rng")[0]
pre = pre.replace("n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]", "n = 9; LO = 0.0; OUT = '/tmp/unused'")
exec(pre)
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family
S = json.load(open(__import__('os').environ.get('SEPJSON', 'sepG%s.json' % T))); R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
SA = 10 ** 8
a_f = np.array(S['a']); b_f = np.array(S['b'])
A_int = np.floor(a_f * SA + 1e-6).astype(np.int64); B_int = np.rint(b_f * SA).astype(np.int64)
B_int = np.maximum(B_int, 1); B_int = np.minimum(B_int, B_int[::-1]) if False else B_int
assert all(A_int[k] == A_int[MP[k]] for k in range(NP)) and all(B_int == B_int[::-1]) and all(B_int > 0)
caps = [int(A_int[SPAN == s].sum()) for s in range(1, n)]; assert max(caps) <= 2 * SA
a = A_int / SA; b = B_int / SA; B_SA = int(B_int.sum())
# fresh search (my oracle)
rng = np.random.default_rng(424242)
ALPH = np.array([0.2, 0.5, 0.9, 1.04, 1.25, 1.5, 1.75, 1.97, 2.2, 2.6, 2.93, 3.3, 4.0, 6.0])
seeds = list(WORDS) + [ALPH[rng.integers(0, len(ALPH), m)] for _ in range(20000)] + [rng.uniform(0, 5, m) for _ in range(5000)]
global_min(a, b, seeds, rng, nrand=0)
mins = {}
for f, g in LASTMINS:
    fe = Fw_val(g, a, b, exact=True); key = tuple(np.round(g, 3))
    if key not in mins or fe < mins[key][0]: mins[key] = (fe, g)
mins = sorted(mins.values(), key=lambda v: v[0])
# lattice oracle (famq), as rwin.py
cw_ = np.array(R8['cnum'], float) / R8['cden']; ww = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw_))])
fam = Family(m, cw_, ww); assert [tuple(p) for p in fam.pairs] == list(zip(PI.tolist(), PJ.tolist()))
lat4 = np.array(list(itertools.product((1.04, 1.97, 2.91, 0.5), repeat=m)))
lat = [float(fam.global_min(a, b, coarse=400000, keep=250, seed=s, extra_starts=lat4)[0]) for s in (1, 2, 3)]
eps = min([mins[0][0]] + lat)
print('T=%s: B_SA %d, caps %s; true min: fresh %.15f, lattice %s -> eps_strong %.15f; argmin %s'
      % (T, B_SA, caps, mins[0][0], ['%.15f' % v for v in lat], eps, np.round(mins[0][1], 4)), flush=True)
cnt = {('%.0e' % d): sum(1 for f, g in mins if f <= eps * (1 + d)) for d in (2e-4, 1e-3, 1e-2)}
second = next((f / eps - 1 for f, g in mins if f / eps - 1 > 1e-6), None)
k_true = (0.67216841 - B_SA / SA) / (1 - eps)
out = dict(n=9, B_SA=B_SA, SA=SA, cnum=R8['cnum'], cden=R8['cden'], H=R8['H'], aN={f'{i},{j}': int(v) for i, j, v in zip(PI, PJ, A_int)},
           bN=[int(x) for x in B_int], eps_strong=eps, spans=caps,
           sum_abs=R8['sum_abs'], vd_bound=R8['vd_bound'], vdd_bound=R8['vdd_bound'], v0=R8['v0'], vmin=R8['vmin'], pv_v=R8['pv_v'], pv_sqrt_v_over_M=R8['pv_sqrt_v_over_M'],
           window_ref='R8 window (bench/window/rwin8.json)', chain='MOP linear chain kappa = (H_lo - B)/(1 - c), H_lo = 67216841/10^8',
           source='window-scope round 7 separation LP (lp_sep.py, keep = palindromic word), target %s' % T,
           kappa_at_c_true=k_true, basin_counts=cnt, second_basin_rel_excess=second,
           root_hints_near_binding=[[round(float(v), 6) for v in g] for f, g in mins if f <= eps * (1 + 1e-2)][:60])
for nm, d in (('c_cert_target', 5e-5), ('c_cert_fallback', 2e-4)):
    cN = int(np.floor(eps * (1 - d) * SA)); k = Fraction(67216841 - B_SA, SA - cN)
    out[nm] = dict(delta=d, cN_over_1e8=cN, kappa_rational=[k.numerator, k.denominator], kappa=float(k), gain_over_0_6735478=float(k) - 0.6735478)
for d in (0.0, 5e-5, 0.0002):
    cN = int(np.floor(eps * (1 - d) * SA)); k = Fraction(67216841 - B_SA, SA - cN); out[f'delta_{d}'] = dict(cN=cN, m=None, phi=float(k))
json.dump(out, open(OUTJ, 'w'), indent=1)
print('kappa at c_true %.9f; certified (5e-5) %s = %.9f; basins %s; 2nd basin rel excess %.3e' % (k_true, out['c_cert_target']['kappa_rational'], out['c_cert_target']['kappa'], cnt, second), flush=True)
