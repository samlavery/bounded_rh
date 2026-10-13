"""Save the hardest known multi-pair shallow geometries (periodic relaxed minimisers, certificate v1) for the joint
environment-DP test: pair centres, depths, the environment, the exact periodic LP_total and its split.  Output multipair_geoms.json."""
import sys, json, numpy as np
from scipy.optimize import minimize
out = []
for N, cases in ((64, [('block32', 0.4), ('block16', 0.2), ('block16', 0.4), ('comp8', 0.4), ('comp4', 0.4), ('comp8', 0.2)]), (128, [('block64', 0.2), ('block64', 0.4)])):
    exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % N))
    exec(open('multipair_dense2.py').read().split("def run(")[0].split("exec(open('lemmaP.py')")[1].split('\n', 1)[1])
    rr = np.random.default_rng(31)
    for name, Y in cases:
        best = (np.inf, None)
        if name.startswith('block'):
            P = int(name[5:]); starts = [(np.arange(P, dtype=float), np.full(P, Y), set(range(P, 2 * P)))]
        else:
            P = int(name[4:]); prof = 0.15 + 0.85 * np.exp(-((np.arange(P) - (P - 1) / 2) / max(1, P / 4)) ** 2)
            starts = [(10 + s0 * np.arange(P), Y * prof / prof.max(), v) for s0 in (0.6, 0.7, 0.85, 1.0)
                      for v in (set(range(30, 30 + P)), set(np.round(np.linspace(26, 64, P, endpoint=False)).astype(int) % N))]
        for cen, ys, vacs in starts:
            occ = set(np.round(cen).astype(int))
            xon = np.array([t for t in range(N) if t not in occ and t not in vacs], float); k = len(xon) + 2 * P - N
            if k > 0: xon = xon[:len(xon) - k]
            if len(xon) + 2 * P != N: continue
            n1 = len(xon); z0 = np.concatenate([xon + rr.normal(0, 0.02, n1), cen])
            r = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), z0, jac=True, method='L-BFGS-B', options={'maxiter': 8000})
            if r.fun < best[0]: best = (r.fun, r.x.copy(), n1, ys.copy())
        d, z, n1, ys = best; xon, sc = z[:n1], z[n1:]; sp = split(xon, sc, ys)
        c0 = float(np.mean(sc)); rel = lambda v: ((v - c0 + N / 2) % N) - N / 2
        o = np.argsort(rel(sc))
        out.append({'name': name, 'N': N, 'Y': Y, 'pairs': rel(sc)[o].tolist(), 'depths': ys[o].tolist(), 'env': np.sort(rel(xon)).tolist(),
                    'LP_total': float(sum(sp)), 'split': {'P_h': sp[0], 'T_g': sp[1], 'fields': sp[2], 'BB': sp[3]},
                    'LP_over_sum_y2': float(sum(sp) / np.sum(ys ** 2))})
        print('%s N=%d Y=%.1f: LP_total %.4f (LP/sum y^2 %.3f) split P_h %.3f T_g %.3f fields %.3f BB %.3f; pair spacings %s' % (
            name, N, Y, sum(sp), sum(sp) / np.sum(ys ** 2), *sp, np.round(np.diff(np.sort(rel(sc))), 3)[:12]), flush=True)
json.dump(out, open('multipair_geoms.json', 'w'), indent=1)
print('saved multipair_geoms.json')
