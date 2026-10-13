"""E12: scaling of the stack mechanism.  Configuration: weighted pairs (multiplicity m_p) at positions s_p and depths y_p:
two stacks of multiplicity m at depth y1 = 0.8 joined by a chain of k simple pairs (positions, depths free in [0.8, 3]),
optionally chains outside as well.  Q_pp = int q (|sum m_p c_p e_p|^2 - 4 |sum m_p e_p|^2), c = 2 cosh(2 pi a y).
For each m: minimise Q_pp over chain positions/depths and the stack separation; save; report Q_pp/m^2."""
import sys, json, numpy as np
from scipy.optimize import minimize
import common as C
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
y1 = 0.8

def obj(z, mvec, nfree, ystack):
    # z = positions of all items (stacks + chain) then depths of chain items
    P = len(mvec); s = z[:P]; y = ystack.copy(); y[nfree:] = z[P:]
    E = np.exp(2j * np.pi * np.outer(C.al, s)); c = 2 * np.cosh(2 * np.pi * np.outer(C.al, y))
    F = (c * E) @ mvec; G = E @ mvec
    Q = float(C.W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * C.al[:, None]
    gs = C.W2 @ (2 * np.real(np.conj(F)[:, None] * c * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E)) * mvec
    dc = 4 * np.pi * C.al[:, None] * np.sinh(2 * np.pi * np.outer(C.al, y))
    gy = (C.W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E)) * mvec)[nfree:]
    return Q, np.concatenate([gs, gy])

k = int(sys.argv[2]) if len(sys.argv) > 2 else 6
ms = [int(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [1, 2, 4, 8, 16, 32]
out = {}
for m in ms:
    # items: stack A, stack B (weight m, depth y1, nfree = 2 fixed-depth items first), then k chain pairs
    mvec = np.array([m, m] + [1] * k, float); P = len(mvec); nfree = 2
    ystack = np.full(P, y1)
    best = (np.inf, None)
    for t in range(30):
        L = rng.uniform(0.6, 0.9) * (k + 1)
        s0 = np.concatenate([[0.0, L], np.sort(rng.uniform(0.2, L - 0.2, k))]) + rng.normal(0, 0.02, P)
        y0 = rng.uniform(y1, 1.6, k)
        r = minimize(lambda z: obj(z, mvec, nfree, ystack), np.concatenate([s0, y0]), jac=True, method='L-BFGS-B',
                     bounds=[(None, None)] * P + [(y1, 3.0)] * k, options={'maxiter': 6000})
        if r.fun < best[0]: best = (r.fun, r.x.copy())
    z = best[1]; s = z[:P]; yv = ystack.copy(); yv[nfree:] = z[P:]
    o = np.argsort(s)
    out[str(m)] = {'s': (s[o] - s[o][0]).tolist(), 'y': yv[o].tolist(), 'm': mvec[o].tolist(), 'Qpp': best[0]}
    print('m=%3d k=%d: min Q_pp %+.4e | Q_pp/m^2 %+.4f | s %s | y %s | mult %s' % (m, k, best[0], best[0] / m ** 2,
          np.round(s[o] - s[o][0], 3), np.round(yv[o], 3), mvec[o].astype(int)), flush=True)
json.dump(out, open('e12b_k%d.json' % k, 'w'))
