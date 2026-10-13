import numpy as np, sys
sys.path.insert(0, '.')
import amk
w_exact = lambda x: float(np.ravel(amk.w_exact(x))[0]); w1_exact = lambda x: float(np.ravel(amk.w1_exact(x))[0]); w2 = lambda x: float(np.ravel(amk.w2(x))[0])
d = np.load('wAM6.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
Q = 5; PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]; SA = 1e8; SC = 32768
def G(x):
    return sum(bN[k] * x[k] for k in range(Q)) / SA + sum(aN[t] * w_exact(sum(x[i:j])) for t, (i, j) in enumerate(PAIRS)) / SA
def grad(x):
    g = np.array([bN[k] / SA for k in range(Q)])
    for t, (i, j) in enumerate(PAIRS):
        s = w1_exact(sum(x[i:j])) * aN[t] / SA
        for k in range(i, j): g[k] += s
    return g
def hess(x):
    H = np.zeros((Q, Q))
    for t, (i, j) in enumerate(PAIRS):
        s = w2(sum(x[i:j])) * aN[t] / SA
        for k in range(i, j):
            for l in range(i, j): H[k, l] += s
    return H
gmin = d['vals'][0]
for v, x in list(zip(d['vals'], d['mins']))[:8]:
    q = np.round(np.array(x) * SC) / SC
    g = grad(q); 
    xn = np.array(x, float)
    for _ in range(6): xn = xn - np.linalg.solve(hess(xn), grad(xn))
    qn = np.round(xn * SC) / SC
    print(f"v={v:.10f} G(q)-gmin={(G(q)-gmin)*1e8:+.1f} |g|1(q)={np.abs(g).sum():.2e}  newton: G={G(xn):.10f} dx={np.abs(xn-x).max()*SC:.2f}grid |g|1(qn)={np.abs(grad(qn)).sum():.2e} eig={np.linalg.eigvalsh(hess(xn)).round(4)}")
import itertools
print("---- best grid point near each minimum, by |grad|_1 (float)")
for v, x in list(zip(d['vals'], d['mins']))[:8]:
    xs = np.array(x, float); q0 = np.round(xs * SC).astype(int)
    sym = list(q0) == list(q0[::-1])
    best = []
    R = 2
    for dq in itertools.product(range(-R, R + 1), repeat=Q):
        if sym and list(dq) != list(dq[::-1]): continue
        q = (q0 + np.array(dq)) / SC
        g = grad(q); best.append((np.abs(g).sum(), (G(q) - gmin) * 1e8, dq))
    best.sort()
    print(f"v={v:.10f} round |g|1={np.abs(grad(q0/SC)).sum():.2e}; best: " + "; ".join(f"{b[0]:.2e} dG={b[1]:+.1f} {b[2]}" for b in best[:3]))
