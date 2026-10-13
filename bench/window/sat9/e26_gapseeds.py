"""E26: held-out seeds for the q*Fejer pre-registration (lead 2026-10-09): the e24b gap configurations
(3 shallow blocks of 8 pairs at spacing 0.6, 2 deep pairs at Y in gaps of width G).  Evaluate bound - target at the seeds,
then run the e25 adversary (minimise [bound - target], depths in [0.8, 20]) from each seed."""
import numpy as np
from scipy.optimize import minimize
src = open('e25_qfejer_adv.py').read().split('rng = np.random.default_rng')[0]
exec(src)
worst = (np.inf, None)
for Y in (5.0, 10.0):
    for G in (1.0, 1.5, 2.0, 3.0, 4.0):
        blk = 0.6 * np.arange(8); s = np.concatenate([blk, blk + 4.2 + G, blk + 2 * (4.2 + G), [4.2 + G / 2, 2 * (4.2 + G) - G / 2]])
        y = np.concatenate([np.full(24, 0.8), np.full(2, Y)]); P = len(s)
        v0, tgt, d0, parts0, _ = exact(s, y)
        r = minimize(obj, np.concatenate([s, y]), args=(P, None), jac=True, method='L-BFGS-B',
                     bounds=[(None, None)] * P + [(0.8, 20.0)] * P, options={'maxiter': 3000})
        v1, tgt1, d1, parts1, _ = exact(r.x[:P], r.x[P:])
        yy = r.x[P:]
        print('seed Y=%g G=%.1f: at seed [bound-target] %+.3g (delta*=%.3f) | after local adversary %+.3f (delta*=%.3f, (i) %.1f (ii) %+.1f (iii) %.1f; max depth now %.2f) %s'
              % (Y, G, v0, d0, v1, d1, parts1[0], parts1[1], parts1[2], yy.max(), 'PASS' if v1 >= 0 else 'FAIL'), flush=True)
        if v1 < worst[0]: worst = (v1, Y, G)
print('worst after adversary: %+.3f at Y=%g G=%.1f' % worst)
