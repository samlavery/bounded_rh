"""(Depths FIXED by a profile scaled to max depth Y; positions relaxed; reported as LP_total / sum_p y_p^2.)
Adversarial search, compressed shallow clusters (periodic model N = 64, certificate v1): P pairs started at spacing s0 in
{0.6, 0.7, 0.85, 1.0} with depth profiles (flat, peaked, random) in [0.02, 0.8], environment = lattice with P vacancies (contiguous or
spread); ALL positions and depths relaxed (depths bounded to [0.02, 0.8]).  Reports min W per defect (units 2 delta') and the split
LP_total = P_h + T_g + fields + B-B at the minimiser, and the minimiser's pair spacings and depths."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', 64"))
exec(open('multipair_dense2.py').read().split("def run(")[0].split("exec(open('lemmaP.py')")[1].split('\n', 1)[1])
rr = np.random.default_rng(31)
def W_of(d, P): return (d / N - N * (gN0 - gh0) / 2 - gN0 * P) / P / g0
worst_all = (np.inf, None)
for Y in (0.1, 0.2, 0.4, 0.8):
    for P in (2, 3, 4, 6, 8):
        best = (np.inf, None)
        for s0 in (0.6, 0.7, 0.85, 1.0):
            for prof in ('flat', 'peak', 'alt', 'rand'):
                for vac in ('contig', 'spread'):
                    cen = 10 + s0 * np.arange(P)
                    pr = {'flat': np.ones(P), 'peak': 0.15 + 0.85 * np.exp(-((np.arange(P) - (P - 1) / 2) / max(1, P / 4)) ** 2),
                          'alt': np.where(np.arange(P) % 2 == 0, 1.0, 0.3), 'rand': rr.uniform(0.1, 1.0, P)}[prof]
                    ys = Y * pr / pr.max()
                    occ = set(np.round(cen).astype(int))
                    vacs = set(range(30, 30 + P)) if vac == 'contig' else set(np.round(np.linspace(26, 64, P, endpoint=False)).astype(int) % N)
                    xon = np.array([t for t in range(N) if t not in occ and t not in vacs], float)
                    k = len(xon) + 2 * P - N
                    if k > 0: xon = xon[:len(xon) - k]
                    if len(xon) + 2 * P != N: continue
                    n1 = len(xon); z0 = np.concatenate([xon + rr.normal(0, 0.02, n1), cen])
                    r = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), z0, jac=True, method='L-BFGS-B', options={'maxiter': 8000})
                    lp = 2 * (r.fun / N - N * (gN0 - gh0) / 2 - gN0 * P); val = lp / float(np.sum(ys ** 2))
                    if val < best[0]: best = (val, r.x.copy(), n1, ys.copy(), prof, s0)
        val, z, n1, ys, prof, s0 = best; xon, sc = z[:n1], z[n1:]
        sp = split(xon, sc, ys); o = np.argsort(sc); S2 = float(np.sum(ys ** 2))
        print('Y=%.1f P=%d: min LP/sum y^2 %+.3f (profile %s, start spacing %.2f) | split /sum y^2: P_h %+.3f T_g %+.3f fields %+.3f B-B %+.3f | spacings %s'
              % (Y, P, val, prof, s0, *(v / S2 for v in sp), np.round(np.diff(sc[o]), 3)), flush=True)
        if val < worst_all[0]: worst_all = (val, (Y, P, prof))
print('WORST LP/sum y^2: %+.4f at %s' % worst_all, flush=True)
