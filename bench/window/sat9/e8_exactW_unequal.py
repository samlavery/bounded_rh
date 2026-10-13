"""E8: exact Lemma P W for the unequal-depth pair clusters of e7_best.json (in particular those with Q_pp < 0),
embedded in a lattice environment (periodic model of band1/lemmaP.py, backed R8 certificate); environment relaxed with the
cluster fixed, then centres + environment relaxed with depths fixed.  Reports W/defect, s(D), Q_pp (exact, periodic grid)."""
import sys, json, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[2]) if len(sys.argv) > 2 else 128
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(13)
data = json.load(open('e7_best.json'))
keys = sys.argv[1].split(';') if len(sys.argv) > 1 else sorted(data)

def pieces(z, n1, P, ys):
    x = z[:n1]; s = z[n1:n1 + P]
    d, _ = d_and_grad(z, n1, 0, P, ys)
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
    xr = np.concatenate([x, s]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)])
    sl = d_real(xr, mr) / N - N * (gN0 - gh0) / 2 - gN0 * P
    Es = np.exp(2j * np.pi * np.outer(J, s) / N); c = 2 * np.cosh(2 * np.pi * np.outer(J, ys) / N)
    F = (c * Es).sum(1); G = Es.sum(1)
    Qpp = float((2 / N) * np.sum(qv * (np.abs(F) ** 2 - 4 * np.abs(G) ** 2)))
    return W, sl, Qpp

for key in keys:
    e = data[key]; s_rel = np.array(e['s']); ys = np.array(e['y']); P = len(s_rel)
    s = 6.0 + s_rel; n1 = N - 2 * P; occ = set()
    for t in s: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.array([t for t in range(N) if t not in occ], float)
    if len(base) < n1: base = np.concatenate([base, rng.uniform(s[-1] + 2, N, n1 - len(base))])
    base = base[:n1]
    best = (np.inf, None)
    for k in range(3):
        x0 = base + rng.normal(0, 0.03 * k, n1)
        def f(xx):
            z = np.concatenate([xx, s]); d, g = d_and_grad(z, n1, 0, P, ys); return d, g[:n1]
        r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 5000})
        if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, s]))
    W, sl, Qpp = pieces(best[1], n1, P, ys)
    r2 = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), best[1], jac=True, method='L-BFGS-B', options={'maxiter': 5000})
    W2_, sl2, Q2 = pieces(r2.x, n1, P, ys)
    print('%-8s P=%2d (cont. Q_pp %+.3f, T_g %.2f) | env relaxed: W/def %+.4f s %.3f Q_pp %+.3f | all relaxed: W/def %+.4f s %.3f Q_pp %+.3f'
          % (key, P, e['Qpp'], e['Tg'], W / (g0 * P), sl, Qpp, W2_ / (g0 * P), sl2, Q2), flush=True)
