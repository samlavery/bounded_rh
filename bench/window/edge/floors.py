"""Edge windows for PC8SF: floors of the PREFIX-truncated functionals of the eight-point certificate PC8C5BF
(weights = rwin8.json aN/bN, checked equal to rootR8f/AMW/PC8C5BFInst.lean BS/TS; kernel = the R8 window).

F_k(g_0..g_{k-1}) = sum_{r<k} b_r g_r + sum_{a<b<=k} a_ab W(g_a + ... + g_{b-1}),  W = K^2,  g in [0, inf)^k.
Floor c_t(k) = min F_k: a dense grid on [0, G]^k (W from a fine table, linear interpolation) plus L-BFGS-B refinement
with the exact kernel from the best grid points, plus a large-gap escape check.  Double precision.
Writes edge_k{k}.json (a superset of rwin8.json's format: n = k+1 points, aN keyed 'i,j', bN, B_SA, eps_strong = floor)."""
import sys, json, math, itertools, time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from slack import K

R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
SA = R8['SA']
aN = {tuple(map(int, k.split(','))): v for k, v in R8['aN'].items()}
bN = R8['bN']

XT = np.linspace(0, 40, 400001); WT = K(XT) ** 2
def W_tab(x): return np.interp(x, XT, WT, right=0.0)
def W_ex(x): return K(np.asarray(x, float)) ** 2

def terms(k):
    return [(a, b, aN[(a, b)] / SA) for (a, b) in sorted(aN) if b <= k and aN[(a, b)]]

def F_exact(g, k):
    g = np.asarray(g, float); x = np.concatenate([[0.0], np.cumsum(g)])
    v = sum(bN[r] / SA * g[r] for r in range(k))
    for a, b, w in terms(k): v += w * float(W_ex(x[b] - x[a]))
    return float(v)

def F_grid_batch(G, k):
    """G: (N, k) array of gap vectors"""
    x = np.concatenate([np.zeros((G.shape[0], 1)), np.cumsum(G, axis=1)], axis=1)
    v = G @ (np.array(bN[:k]) / SA)
    for a, b, w in terms(k): v += w * W_tab(x[:, b] - x[:, a])
    return v

def floor(k, step, Gmax, extra=(5.0, 8.0, 15.0), keep=300):
    levels = np.concatenate([np.arange(0, Gmax + 1e-9, step), extra])
    t0 = time.time(); best = []
    # enumerate the grid in chunks over the first coordinate
    for v0 in levels:
        rest = np.array(list(itertools.product(levels, repeat=k - 1))) if k > 1 else np.zeros((1, 0))
        Gc = np.concatenate([np.full((rest.shape[0], 1), v0), rest], axis=1)
        vals = F_grid_batch(Gc, k)
        idx = np.argsort(vals)[:keep]
        best += [(float(vals[i]), Gc[i].copy()) for i in idx]
        best = sorted(best, key=lambda t: t[0])[:keep]
    tgrid = time.time() - t0
    ref = (np.inf, None)
    for v, g0 in best:
        r = minimize(lambda g: F_exact(g, k), g0, method='L-BFGS-B', bounds=[(0, 60)] * k, options={'ftol': 1e-15, 'gtol': 1e-12, 'maxiter': 2000})
        if r.fun < ref[0]: ref = (float(r.fun), r.x.copy())
    return ref, best[0], tgrid, len(levels) ** k

if __name__ == '__main__':
    out = {}
    for k, step in ((3, 0.02), (4, 0.04), (5, 0.08), (6, 0.16)):
        (cf, gmin), gbest, tg, npts = floor(k, step, 4.0)
        Bt = sum(bN[:k])
        # local robustness: perturbed restarts around the minimiser
        rng = np.random.default_rng(k); worst = cf
        for _ in range(200):
            g0 = np.clip(gmin + rng.normal(0, 0.3, k), 0, None)
            r = minimize(lambda g: F_exact(g, k), g0, method='L-BFGS-B', bounds=[(0, 60)] * k)
            worst = min(worst, float(r.fun))
        print('k=%d: grid %d pts step %.2f (%.0fs) grid-best %.9f; refined floor c_t = %.10f at %s; perturbed-restart min %.10f; B_t = %d/SA'
              % (k, npts, step, tg, gbest[0], cf, np.round(gmin, 5), worst, Bt), flush=True)
        cf = min(cf, worst)
        d = {'n': k + 1, 'k_gaps': k, 'kind': 'prefix truncation of the PC8C5BF eight-point functional (rwin8.json) to points 0..k; '
             'the suffix truncation is its mirror (W is reversal-symmetric)', 'parent': 'rwin8.json',
             'SA': SA, 'cnum': R8['cnum'], 'cden': R8['cden'], 'H': R8['H'],
             'aN': {'%d,%d' % (a, b): aN[(a, b)] for (a, b) in sorted(aN) if b <= k},
             'bN': bN[:k], 'B_SA': Bt, 'eps_strong': cf, 'floor_minimiser': [float(x) for x in gmin],
             'cN_t_at_0.01pct': int(math.floor(cf * (1 - 1e-4) * SA)), 'cN_t_at_0.1pct': int(math.floor(cf * (1 - 1e-3) * SA))}
        json.dump(d, open('/Users/samuellavery/work/riemann-submission/bench/window/edge/edge_k%d.json' % k, 'w'), indent=1)
        out[k] = d
