"""E2: exact Lemma P quantity W(Z) = [E(Z) - F_C(D(Z))]/2 (periodic model of band1/lemmaP.py, backed R8 certificate) for
deep equal-depth clusters at adversarial positions (the E1 minimisers of ||S_B|| and arithmetic patterns), embedded in a lattice
environment; then (a) environment relaxed with the cluster fixed, (b) everything relaxed (pair centres + environment).
Reports W per defect (units of g(0) = 2 delta'), the split into s(D) and the exact field term, and the CS-chain quantity
s + X^2 - (4P + 2 M_near) X (which is what the posed criterion needs to be >= 0, ignoring 'far')."""
import sys, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[3]) if len(sys.argv) > 3 else 128
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(11)

def split(z, n1, P, y):
    s = z[n1:n1 + P]; x = z[:n1]
    d, _ = d_and_grad(z, n1, 0, P, np.full(P, y))
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
    xr = np.concatenate([x, s]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)])
    dD = d_real(xr, mr); sl = dD / N - N * (gN0 - gh0) / 2 - gN0 * P
    A = 2 * np.cosh(2 * np.pi * np.outer(J, np.full(P, y)) / N) - 2; Es = np.exp(2j * np.pi * np.outer(J, s) / N)
    SB = (A * Es).sum(1); X = np.sqrt((2 / N) * np.sum(qv * np.abs(SB) ** 2))
    dist = np.min(np.abs(((x[:, None] - s[None, :]) + N / 2) % N - N / 2), axis=1)
    Mnear = int(np.sum(dist < 1.0))
    chain = 2 * sl + X ** 2 - (4 * P + 2 * Mnear) * X          # two-sided units: 2W = 2 s + Q, Q >= X^2 - (4P+2M)X - far
    return W, sl, X, Mnear, chain

def run(y, P, s_rel, tag):
    s = 10.0 + np.asarray(s_rel, float); n1 = N - 2 * P
    occ = set()
    for t in s: occ |= {int(np.floor(t)), int(np.ceil(t))}
    base = np.array([t for t in range(N) if t not in occ], float)
    base = base[:n1] if len(base) >= n1 else np.concatenate([base, np.linspace(40, N - 1, n1 - len(base))])
    best = (np.inf, None)
    for k in range(3):
        x0 = base + rng.normal(0, 0.02 * k, n1)
        def f(xx):
            z = np.concatenate([xx, s]); d, g = d_and_grad(z, n1, 0, P, np.full(P, y)); return d, g[:n1]
        r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 4000})
        if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, s]))
    W, sl, X, Mn, ch = split(best[1], n1, P, y)
    # everything relaxed
    r2 = minimize(lambda z: d_and_grad(z, n1, 0, P, np.full(P, y)), best[1], jac=True, method='L-BFGS-B', options={'maxiter': 4000})
    W2_, sl2, X2_, Mn2, ch2 = split(r2.x, n1, P, y)
    print('  %-10s y=%.2f P=%2d | env relaxed: W/def %+9.3f (s %8.3f) X %9.3f vs 4P+2M %4d chain %+10.2f | all relaxed: W/def %+9.3f X %9.3f chain %+10.2f'
          % (tag, y, P, W / (g0 * P), sl, X, 4 * P + 2 * Mn, ch, W2_ / (g0 * P), X2_, ch2), flush=True)

ys = [float(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [1.0, 1.5]
Ps = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [4, 8, 16]
sys.path.insert(0, '.')
import e1_criterion as e1m
for y in ys:
    from common import B as Bc, W2 as W2c
    wB2 = W2c * Bc(y) ** 2
    for P in Ps:
        bestE1 = (np.inf, None)
        for s0 in e1m.starts(P):
            r = minimize(lambda ss: e1m.X2_and_grad(ss, wB2), s0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            if r.fun < bestE1[0]: bestE1 = (r.fun, np.sort(r.x - r.x.min()))
        run(y, P, bestE1[1], 'E1-min')
        run(y, P, 0.5 * np.arange(P), 'AP 1/2')
        run(y, P, 1.5 * np.arange(P), 'AP 3/2')
