"""E1: adversarial test of the posed criterion ||S_B|| >= 4P (+ 2 M_near), equal depths, no environment.
S_B(a) = B_y(a) V(a), V(a) = sum_p e(a s_p).  Minimise X^2 = ||S_B||^2 over the positions s_p (L-BFGS, analytic gradient),
many starts (arithmetic progressions at spacings 1/4, 1/2, 3/2, 5/2, product (1+e(a d_i)) patterns, random).
Reported with the cluster's own pair cost T_g = sum_{p != p'} 4 g(s_p - s_p') (doubles of mass 2) and ||V||_q."""
import sys, numpy as np
from scipy.optimize import minimize
from common import *
rng = np.random.default_rng(5)

def X2_and_grad(s, wB2):
    E = np.exp(2j * np.pi * np.outer(al, s)); V = E.sum(1)
    X2 = float(wB2 @ np.abs(V) ** 2)
    # d|V|^2/ds_p = 2 Re(conj(V) * 2 pi i a e_p)
    G = 2 * np.real(np.conj(V)[:, None] * (2j * np.pi * al[:, None]) * E)
    return X2, wB2 @ G

def Tg(s):
    d = s[:, None] - s[None, :]; iu = np.triu_indices(len(s), 1)
    return float(2 * 4 * g_of(d[iu]).sum())

def normV(s):
    V = np.exp(2j * np.pi * np.outer(al, s)).sum(1); return float(np.sqrt(W2 @ np.abs(V) ** 2))

def starts(P):
    out = []
    for d in (0.25, 0.5, 1.5, 2.5, 1.0 / 3, 2.0 / 3):
        out.append(d * np.arange(P))
    # product patterns: subset sums of half-integers
    m = int(np.ceil(np.log2(P)))
    for base in ((0.5, 1.5, 2.5, 3.5, 4.5, 5.5), (0.5, 0.5 + 1, 0.5 + 3, 0.5 + 5, 7.5, 9.5)):
        sums = np.array([0.0])
        for i in range(m):
            sums = np.concatenate([sums, sums + base[i]])
        out.append(np.sort(sums)[:P])
    for t in range(6):
        out.append(np.sort(rng.uniform(0, max(1.0, 0.5 * P), P)))
    return out

ys = [float(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [0.8, 1.0, 1.2, 1.5]
Ps = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [2, 4, 8, 12, 16, 24, 32]
for y in (ys if __name__ == '__main__' else []):
    wB2 = W2 * B(y) ** 2; nB = normB(y)
    print('y=%.2f  ||B_y|| = %.3f   (criterion ||S_B|| >= 4P fails iff X < 4P)' % (y, nB), flush=True)
    for P in Ps:
        best = (np.inf, None)
        for s0 in starts(P):
            r = minimize(lambda s: X2_and_grad(s, wB2), s0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, np.sort(r.x - r.x.min()))
        X = np.sqrt(max(best[0], 0)); s = best[1]
        print('  P=%2d: min ||S_B|| = %9.4f  (4P = %3d, ratio %.4f, /(P||B||) %.4f) | T_g(cluster) %.3f | ||V||_q %.3f | diam %.2f | gaps %s'
              % (P, X, 4 * P, X / (4 * P), X / (P * nB), Tg(s), normV(s), s[-1], np.round(np.diff(s)[:8], 3)), flush=True)
