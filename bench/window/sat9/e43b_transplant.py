"""E43b: same pre-registration as e43_scalable.py (quantity, evaluator, decision rule unchanged); SEEDING upgraded because the
4-parameter ansatz of e43 did not reproduce the dense P = 256 optima (a = 0.99: ansatz+300 L-BFGS 1181.8 vs dense 952.5).
Seeding: P = 256 from the e42c dense profile; each larger P from the previous P's best profile: half-profile h(d) stretched by
1/r (r in {1, 0.75, 0.5}) with the interior lifted by delta (in {0, 0.2, 0.4}); best of the 9 by exact evaluation; then
L-BFGS-B refinement of all y_p (maxiter 1500 / 1000 / 600 / 300 / 200 for P = 256..512 / 1024 / 2048 / 4096 / 8192).
Every value is an upper bound on the family minimum."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
exec(open('e43_scalable.py').read().split("if __name__ == '__main__':")[0])
a = float(sys.argv[1]); Ps = [int(x) for x in sys.argv[2].split(',')]
y = np.array(json.load(open('e42c_pp_a%.2f_P256.json' % a))['y']); rows = []
for P in Ps:
    t0 = time.time(); ch = Chain(a, P)
    if len(y) == P:
        y0 = y.copy()
    else:
        Pp = len(y); half = y[:Pp // 2]; d = np.minimum(np.arange(P), P - 1 - np.arange(P)); best = (np.inf, None)
        for r in (1.0, 0.75, 0.5):
            for delta in (0.0, 0.2, 0.4):
                idx = np.minimum((d * r).astype(int), len(half) - 1); cand = half[idx].copy()
                interior = (d * r) >= len(half) - 1; cand[interior] = np.minimum(cand[interior] + delta, 3.0)
                v = ch.onep(cand)[0]
                if v < best[0]: best = (v, cand)
        y0 = best[1]
    mi = {256: 1500, 512: 1500, 1024: 1000, 2048: 600, 4096: 300, 8192: 200}.get(P, 300)
    v0 = ch.onep(y0)[0]
    rr = minimize(lambda yy: ch.onep(yy, True), y0, jac=True, method='L-BFGS-B', bounds=[(0.8, 3.0)] * P, options={'maxiter': mi})
    y = rr.x; val = rr.fun; gproj = rr.jac.copy(); gproj[(y <= 0.8 + 1e-9) & (gproj > 0)] = 0; gproj[(y >= 3 - 1e-9) & (gproj < 0)] = 0
    print('a=%.2f P=%5d: seed %+12.4f -> refined (1\') %+12.4f | Q_pp %+12.4f T_g %9.4f | proj-grad %.2e | its %d | depths ends %.3f mid %.3f max %.3f | n_gl %d | %.0fs'
          % (a, P, v0, val, val - ch.Tg, ch.Tg, np.linalg.norm(gproj), rr.nit, y[0], y[P // 2], y.max(), len(ch.al), time.time() - t0), flush=True)
    rows.append({'P': P, 'onep': float(val), 'Q_pp': float(val - ch.Tg), 'Tg': ch.Tg, 'projgrad': float(np.linalg.norm(gproj))})
    json.dump({'a': a, 'rows': rows, 'y_last': y.tolist()}, open('e43b_a%.2f.json' % a, 'w'))
    json.dump({'a': a, 'P': P, 'y': y.tolist(), 'onep': float(val)}, open('e43b_a%.2f_P%d.json' % (a, P), 'w'))
