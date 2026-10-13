"""Seven-point (Q = 6 gaps) weighted functional: symmetrised LP weights, integer rounding over SA = 10^8, and a search
for the local minima of the rounded functional on the half-space g0 <= g5.

G(g) = sum_r b_r g_r + sum_{i<j} a_ij w(g_i + ... + g_{j-1}),  w = kfun^2 (closed form)."""
import sys, itertools, math
import numpy as np
from scipy.optimize import minimize

Q = 5; n = Q + 1; SA = 10**8
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]
NP = len(PAIRS)
MIRROR = [PAIRS.index((n - 1 - j, n - 1 - i)) for (i, j) in PAIRS]
S2 = math.sqrt(2.0); GAM = (1 / S2) * math.cos(1 / S2) / math.sin(1 / S2)
INC = np.zeros((NP, Q))
for t, (i, j) in enumerate(PAIRS): INC[t, i:j] = 1.0

def kf(x):
    b = np.pi * np.asarray(x, float); N = np.cos(b) - 2 * GAM * b * np.sin(b); D = 1 - 2 * b * b
    return N / D
def w(x): return kf(x) ** 2
def w1(x):
    b = np.pi * np.asarray(x, float); N = np.cos(b) - 2 * GAM * b * np.sin(b); D = 1 - 2 * b * b
    Nb = -(1 + 2 * GAM) * np.sin(b) - 2 * GAM * b * np.cos(b); M = Nb * D + 4 * b * N
    return 2 * np.pi * N * M / D ** 3
def w2(x, h=1e-5):
    return (w1(np.asarray(x) + h) - w1(np.asarray(x) - h)) / (2 * h)

class Fun:
    def __init__(self, a, b):
        self.a = np.asarray(a, float); self.b = np.asarray(b, float)
    def val(self, G):
        G = np.atleast_2d(G); s = G @ INC.T
        return G @ self.b + w(s) @ self.a
    def vg(self, g):
        s = INC @ g; v = float(self.b @ g + self.a @ w(s)); gr = self.b + INC.T @ (self.a * w1(s))
        return v, gr
    def hess(self, g):
        s = INC @ g; return INC.T @ np.diag(self.a * w2(s)) @ INC

def symmetrise(a, b):
    a = np.asarray(a, float); b = np.asarray(b, float)
    return (a + a[MIRROR]) / 2, (b + b[::-1]) / 2

def round_weights(a, b):
    """integers over SA: symmetric, per-span sums <= 2 SA, b_r >= 1"""
    aN = [int(round(x * SA)) for x in a]
    for t in range(NP): aN[t] = max(0, aN[t])
    for t in range(NP): aN[MIRROR[t]] = aN[t] = min(aN[t], aN[MIRROR[t]])
    for s in range(1, Q + 1):
        idx = [t for t, (i, j) in enumerate(PAIRS) if j - i == s]
        excess = sum(aN[t] for t in idx) - 2 * SA
        while excess > 0:
            t = max(idx, key=lambda t: aN[t])
            if MIRROR[t] != t:
                d = (excess + 1) // 2; aN[t] -= d; aN[MIRROR[t]] -= d; excess -= 2 * d
            else:
                aN[t] -= excess; excess = 0
    bN = [int(round(x * SA)) for x in b]
    for r in range(Q): bN[r] = bN[Q - 1 - r] = max(1, min(bN[r], bN[Q - 1 - r]))
    for s in range(1, Q + 1):
        assert sum(aN[t] for t, (i, j) in enumerate(PAIRS) if j - i == s) <= 2 * SA
    assert all(aN[t] == aN[MIRROR[t]] for t in range(NP)) and bN == bN[::-1]
    return aN, bN

def local_minima(F, starts=200000, keep=600, seed=0, hi=8.0, half=True, tol=1e-9):
    rng = np.random.default_rng(seed)
    lat = np.array(list(itertools.product([1.04, 1.97, 2.91], repeat=Q)))
    S = np.vstack([lat, rng.uniform(0.0, hi, size=(starts, Q)), rng.uniform(0.6, 3.2, size=(starts, Q)),
                   rng.choice([1.04, 1.97, 2.91, 3.9], size=(starts, Q)) + rng.normal(0, 0.06, size=(starts, Q))])
    S = np.clip(S, 0.0, hi)
    if half:
        sw = S[:, 0] > S[:, Q - 1]; S[sw] = S[sw, ::-1]
    vals = F.val(S); order = np.argsort(vals)[:keep]
    found = []
    for idx in order:
        r = minimize(F.vg, S[idx], jac=True, method="L-BFGS-B", bounds=[(0.0, hi)] * Q,
                     options={"maxiter": 2000, "ftol": 1e-17, "gtol": 1e-13})
        x = r.x
        if half and x[0] > x[Q - 1] + 1e-9: x = x[::-1]
        found.append((float(F.vg(x)[0]), x))
    found.sort(key=lambda t: t[0])
    uniq = []
    for v, x in found:
        if all(np.max(np.abs(x - y)) > 1e-4 for _, y in uniq): uniq.append((v, x))
    return uniq
