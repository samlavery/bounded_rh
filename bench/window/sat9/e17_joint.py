"""E17: joint relaxation for the ordSq objective.  Multiplicity pattern fixed (two stacks of multiplicity m + k simple
pairs, e12 start), minimise E(Z) over environment positions AND item positions/depths (depths in [0.8, 3]).  F_C(ordSq)
is fixed by the pattern as long as no new ordinate coincidences form; extra coincidences only raise ordSq, so a negative
computed LP is a negative ordSq LP.  Reports LP_ordSq and LP_R = LP_ordSq + g_N(0) sum_items ((2m)^2 - 4m)."""
import sys, json, numpy as np
from scipy.optimize import minimize
import e15_exact_mult as X
N = int(sys.argv[1]); ms = [int(v) for v in sys.argv[2].split(',')]; src = sys.argv[3] if len(sys.argv) > 3 else 'e12'
rng = np.random.default_rng(5)
J, q, q0, gN0 = X.setup(N)
data = json.load(open(src + '_k6.json'))
for m in ms:
    e = data[str(m)]; s0 = np.array(e['s']) + 5.0; y0 = np.array(e['y']); mm = np.array(e['m'], float); P = len(mm)
    n_on = N - int(2 * mm.sum())
    occ = set()
    for t in s0: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.sort(np.array([t for t in range(N) if t not in occ], float))[:n_on]
    def f(z):
        x = z[:n_on]; s = z[n_on:n_on + P]; y = z[n_on + P:]
        Ex = np.exp(2j * np.pi * np.outer(J, x) / N); Es = np.exp(2j * np.pi * np.outer(J, s) / N)
        c = 2 * np.cosh(2 * np.pi * np.outer(J, y) / N)
        S = Ex.sum(1) + (Es * c) @ mm
        E = (q0 * N ** 2 + 2 * float(q @ np.abs(S) ** 2)) / N
        W = (q * np.conj(S))[:, None]; a = 2j * np.pi * J[:, None] / N
        gx = 4 * np.real(W * Ex * a).sum(0) / N
        gs = 4 * np.real(W * Es * c * a).sum(0) * mm / N
        gy = 4 * np.real(W * Es * (4 * np.pi * J[:, None] / N) * np.sinh(2 * np.pi * np.outer(J, y) / N)).sum(0) * mm / N
        return E, np.concatenate([gx, gs, gy])
    best = (np.inf, None)
    for t in range(3):
        z0 = np.concatenate([base + rng.normal(0, 0.03 * t, n_on), s0 + rng.normal(0, 0.01 * t, P), y0])
        r = minimize(f, z0, jac=True, method='L-BFGS-B', bounds=[(None, None)] * (n_on + P) + [(0.8, 3.0)] * P,
                     options={'maxiter': 20000})
        if r.fun < best[0]: best = (r.fun, r.x)
    EZ, z = best; s = z[n_on:n_on + P]; y = z[n_on + P:]
    Fo = (q0 - X.gh0) * N + gN0 * (n_on + float(np.sum((2 * mm) ** 2)))
    LPo = EZ - Fo; LPr = LPo + gN0 * float(np.sum((2 * mm) ** 2 - 4 * mm))
    xs = np.sort(np.concatenate([z[:n_on] % N, s % N])); mind = np.min(np.abs(np.diff(np.sort(s % N))))
    print('m=%2d N=%d joint: LP_ordSq %+9.3f | LP_R %+9.3f | min item gap %.4f | s-s0 %s | y %s' % (m, N, LPo, LPr, mind,
          np.round(np.sort(s) - np.sort(s)[0], 3), np.round(y[np.argsort(s)], 3)), flush=True)
