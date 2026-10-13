"""LP ceiling of the weighted n-point family for a chosen window, under OUR assembly
(n_point_bound_w': Phi = (H - B(m-q)/m)/(1 - eps(m-q)/m), q = n-1), with the window's own H.
Reference column: AMTOPA's sharp block law h_m (famq.family_bound).

usage: python3 ww.py WINDOW Q B [rounds]      WINDOW in {MT, AM}  (AM = AMTOPA's 17-term window)
Writes ww_<WINDOW>_Q<Q>_B<B>.npz next to this file.
Adapted from helix_frobenius/tmp/att940_amtopa_n8/{wq.py, wq_strong.py}; the family code is famq.py."""
import sys, time, itertools, os
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family, H_of, frequencies, family_bound, AMTOPA_C

HERE = os.path.dirname(os.path.abspath(__file__))  # (AM copy: writes next to this file)
win = sys.argv[1]; Q = int(sys.argv[2]); B = float(sys.argv[3]); rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 30
n = Q + 1
if win == 'MT':
    c = np.array([1.0]); w = np.array([np.sqrt(2.0)])
elif win == 'AM':
    c = AMTOPA_C.copy(); w = frequencies(17)
elif win.startswith('AM'):          # AMk: AMTOPA's window truncated to its first k terms (no re-optimisation)
    k = int(win[2:]); c = AMTOPA_C[:k].copy(); w = frequencies(k)
else:
    raise SystemExit('window must be MT, AM or AMk')
H = H_of(c, w)
H_lo = H - 1e-9          # float H minus a margin; the exact rational floor is a Lean task (stage F)
fam = Family(Q, c, w)

def phi_lin(eps):
    best = (-1.0, 0)
    for m in range(2 * n, 6000):
        if eps * (m - (n - 1)) >= 1: break
        best = max(best, ((H_lo - B * (m - (n - 1)) / m) / (1 - eps * (m - (n - 1)) / m), m))
    return best

print('window %s  H = %.10f  Q = %d (n = %d)  B = %.7f' % (win, H, Q, n, B), flush=True)
lat3 = np.array(list(itertools.product([1.04, 1.97, 2.91], repeat=Q)))
t0 = time.time(); okw = dict(coarse=60000, keep=120, extra_starts=lat3)
lower, upper, a, b, gmin, hist = fam.eps_star(B, rounds=rounds, seed=31, verbose=False, prox=0.3, oracle_kw=okw, ncuts=120)
print('LP  eps* achieved %.9f  LP upper %.9f  (%.0fs)  gmin %s' % (lower, upper, time.time() - t0, np.array2string(gmin, precision=3)), flush=True)
# strong oracle on the LP's (a, b)
lat4 = np.array(list(itertools.product([1.04, 1.97, 2.91, 0.5], repeat=Q)))
coarse = 400000 if Q <= 6 else 200000
floors = []
for seed in (1, 2, 3):
    t1 = time.time()
    r = fam.global_min(a, b, coarse=coarse, keep=250, seed=seed, extra_starts=lat4)
    floors.append(r[0])
    print('  strong seed %d: floor %.9f (%.0fs)' % (seed, r[0], time.time() - t1), flush=True)
eps = min(floors)
pl, ml = phi_lin(eps); pu, mu = phi_lin(upper)
ph, mh = family_bound(H_lo, eps, B, n - 1)
print('RESULT %s n=%d B=%.7f: H=%.10f eps_strong=%.9f (LP upper %.9f) -> Phi_w\' = %.7f at m=%d [from LP upper %.7f]  | h_m law %.7f at m=%d'
      % (win, n, B, H, eps, upper, pl, ml, pu, ph, mh), flush=True)
np.savez(os.path.join(HERE, 'ww_%s_Q%d_B%.7f.npz' % (win, Q, B)), a=a, b=b, gmin=gmin, eps=eps, upper=upper, B=B, H=H)
