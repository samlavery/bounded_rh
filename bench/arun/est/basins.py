"""Round 3 (3): binding-word structure for B&B sizing.  For a certificate (n, a_ij, b_r), collect the distinct local minima of Fw
(word-seeded {1.04,1.97,2.93}^(n-1) + 300 random starts, gaps in [lo, 40]) and count the basins with Fw <= c_min (1 + delta).
Inputs: 'mop' (MOP's W8 parsed from MOP_Solution.lean) or a lp_frame JSON.  usage: python3 basins.py SRC [LO]"""
import sys, json, itertools, numpy as np
SRC = sys.argv[1]; LO = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
sys.argv = ['lp_frame.py', '8', str(LO), '/tmp/unused']
pre = open('lp_frame.py').read().split("t0 = time.time(); rng")[0]
if SRC == 'mop':
    nn = 8
else:
    J = json.load(open(SRC)); nn = J['n']
pre = pre.replace("n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]", "n = %d; LO = %r; OUT = '/tmp/unused'" % (nn, LO))
exec(pre)
if SRC == 'mop':
    import re
    srcl = open('/Users/samuellavery/work/riemann-submission/bench/arun/MOP_Solution.lean').read()
    blk = srcl[srcl.index('def aW8 : Fin 8 → Fin 8 → ℝ'):srcl.index('def bW8')]
    A = np.zeros((8, 8))
    for i, j, v in re.findall(r'\| (\d), (\d) => \((\d+) : ℝ\) / 100000000', blk): A[int(i), int(j)] = int(v) / 1e8
    blk2 = srcl[srcl.index('def bW8 : Fin 7 → ℝ'):srcl.index('def W8 : WCert 8')]
    b = np.array([int(v) / 1e8 for _, v in re.findall(r'\| (\d) => \((\d+) : ℝ\) / 100000000', blk2)])
    a = np.array([A[i, j] for i, j in zip(PI, PJ)])
else:
    a = np.array(J['a']); b = np.array(J['b'])
rng = np.random.default_rng(3)
f0, g0 = global_min(a, b, list(WORDS), rng, nrand=300)
mins = [(Fw_val(g, a, b, exact=True), g) for f, g in LASTMINS]
mins.sort(key=lambda v: v[0]); cmin = mins[0][0]
print('%s (n=%d, lo=%.2f): c_min %.9f, B %.9f, distinct local minima %d' % (SRC, nn, LO, cmin, b.sum(), len(mins)))
for dl in (1e-6, 1e-5, 5e-5, 2e-4, 1e-3, 5e-3):
    k = sum(1 for f, g in mins if f <= cmin * (1 + dl)); print('   basins within %.0e (rel): %d' % (dl, k))
print('   lowest 6:', '; '.join('%.9f %s' % (f, np.round(g, 2)) for f, g in mins[:6]))
