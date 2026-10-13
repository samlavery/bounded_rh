"""(A) Ergodic minimum of PC8C5BF's eight-point functional F (rwin8.json weights = PC8C5BFInst BS/TS, R8 kernel):
c_erg = min over periodic gap words of the cyclic window average (1/q) sum_s F(g_s, ..., g_{s+6}) (no density
constraint), approximating min over shift-invariant measures.  Then kappa with the exact sqrt-branch formula
(PC8SF: m optimised around 152, tau = 8/7, B = 404350/10^8, H floor 67216841/10^8), and the cap 0.6737854.
Double precision."""
import sys, json, math, itertools, time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from slack import K, bN, aN, cc
PAIRS = [(a, b, wt) for (a, b), wt in aN.items() if wt]
PA = np.array([p[0] for p in PAIRS]); PB = np.array([p[1] for p in PAIRS]); PW = np.array([p[2] for p in PAIRS])
B = float(bN.sum())

def F_windows(g):
    """F on every cyclic window of the periodic word g (length q), vectorised"""
    g = np.asarray(g, float); q = len(g)
    ext = np.concatenate([g, g[np.arange(7) % q]] if q < 7 else [g, g[:7]])
    ext = np.concatenate([g] * (7 // q + 2))[: q + 7]
    x = np.concatenate([[0.0], np.cumsum(ext)])
    s = np.arange(q)[:, None]
    spans = x[s + PB[None, :]] - x[s + PA[None, :]]
    pairpart = (PW[None, :] * K(spans) ** 2).sum(axis=1)
    press = np.array([np.dot(bN, ext[i:i + 7]) for i in range(q)])
    return press + pairpart

def Favg(g): return float(F_windows(g).mean())

def single_F(w7): return float(F_windows(np.asarray(w7))[0]) if False else Fwin(w7)
def Fwin(w7):
    w7 = np.asarray(w7, float); x = np.concatenate([[0.0], np.cumsum(w7)])
    return float(np.dot(bN, w7) + np.sum(PW * K(x[PB] - x[PA]) ** 2))

def best_word(q, starts, rng):
    best = (np.inf, None)
    for s0 in starts:
        r = minimize(Favg, s0, method='L-BFGS-B', bounds=[(0, 6)] * q, options={'maxiter': 500})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    return best

if __name__ == '__main__':
    t0 = time.time(); rng = np.random.default_rng(9)
    eps = 805165 / 1e8          # eps_strong of rwin8.json (the per-window minimum)
    print('per-window minimum check: F at the k=1 minimiser %.9f (eps_strong %.9f, cN/SA %.9f)'
          % (Fwin([1.983, 1.043, 1.973, 1.044, 1.973, 1.043, 1.983]), eps, cc), flush=True)
    results = []
    a, b = 1.04, 1.97
    for q in range(1, 9):
        starts = [np.array(p) for p in itertools.product((a, b), repeat=q)]
        starts += [rng.uniform(0.5, 2.5, q) for _ in range(30 if q < 6 else 15)]
        if q <= 3: starts += [np.full(q, v) for v in (0.8, 1.0, 1.2, 1.5, 2.0)]
        e, g = best_word(q, starts, rng)
        results.append((e, q, g))
        print('q = %d: min cyclic average %.9f (ratio to eps %+.4f%%) word %s (%.0fs)'
              % (q, e, 100 * (e / eps - 1), np.round(g, 4), time.time() - t0), flush=True)
    # structured words: the dual's words, the k=2 minimiser pattern, and long a/b words
    named = {'P3': [1.96183, 1.03817], 'Q7': [1.029992, 1.953037, 1.037678, 1.958585, 1.037678, 1.953037, 1.029992],
             'P4': [1.028397, 1.028397, 1.943206], 'k2pat': [1.038, 1.971, 1.043, 1.966, 1.036, 1.035, 1.964, 1.038]}
    for nm, w in named.items():
        e0 = Favg(w)
        r = minimize(Favg, np.array(w), method='L-BFGS-B', bounds=[(0, 6)] * len(w))
        print('%s: cyclic average %.9f (%+.4f%%), refined %.9f (%+.4f%%) %s' % (nm, e0, 100 * (e0 / eps - 1), r.fun, 100 * (r.fun / eps - 1), np.round(r.x, 4)), flush=True)
        results.append((float(r.fun), len(w), r.x))
    for L in range(9, 25):
        for pattern in ('ab', 'aab', 'abb'):
            base = {'ab': [b, a], 'aab': [a, a, b], 'abb': [a, b, b]}[pattern]
            # words of length L mixing the block with alternation
            w = []
            while len(w) < L: w += [b, a]
            w = w[:L]
            if pattern != 'ab': w[: len(base)] = base
            r = minimize(Favg, np.array(w, float), method='L-BFGS-B', bounds=[(0, 6)] * L)
            results.append((float(r.fun), L, r.x))
    e, q, g = min(results, key=lambda t: t[0])
    print('\nc_erg (best over all words) = %.9f at q = %d: %s; c_erg/eps - 1 = %+.4f%%' % (e, q, np.round(g, 4), 100 * (e / eps - 1)), flush=True)
    json.dump(dict(c_erg=e, q=q, word=list(map(float, g)), eps=eps, ratio=e / eps - 1), open('ergodic_r8.json', 'w'), indent=1)
