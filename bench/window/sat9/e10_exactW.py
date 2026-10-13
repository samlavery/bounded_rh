"""E10: exact Lemma P W (periodic model of band1/lemmaP.py, backed R8 certificate) for the e9 pair clusters (Q_pp < 0),
embedded in a lattice environment.  (i) environment relaxed, cluster fixed; (ii) centres + environment relaxed, depths fixed;
(iii) everything relaxed, depths free in [0.8, 3].  Reports W/defect (units g(0)), s(D), Q_pp on the periodic grid."""
import sys, json, numpy as np
from scipy.optimize import minimize
P_list = [int(v) for v in sys.argv[1].split(',')]
NN = int(sys.argv[2]) if len(sys.argv) > 2 else 160
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(17)

def pieces(z, n1, P, ys):
    x = z[:n1]; s = z[n1:n1 + P]
    d, _ = d_and_grad(z, n1, 0, P, ys)
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
    xr = np.concatenate([x, s]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)])
    sl = d_real(xr, mr) / N - N * (gN0 - gh0) / 2 - gN0 * P
    Es = np.exp(2j * np.pi * np.outer(J, s) / N); c = 2 * np.cosh(2 * np.pi * np.outer(J, ys) / N)
    Qpp = float((2 / N) * np.sum(qv * (np.abs((c * Es).sum(1)) ** 2 - 4 * np.abs(Es.sum(1)) ** 2)))
    return W, sl, Qpp

for P in P_list:
    cfg = json.load(open('e9_cfg_%d.json' % P)); ys = np.array(cfg['y']); s = 5.0 + np.array(cfg['s'])
    n1 = N - 2 * P; occ = set()
    for t in s: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.array([t for t in range(N) if t not in occ], float)
    if len(base) < n1: base = np.concatenate([base, rng.uniform(s[-1] + 2, N, n1 - len(base))])
    base = base[:n1]
    best = (np.inf, None)
    for k in range(3):
        x0 = base + rng.normal(0, 0.03 * k, n1)
        def f(xx):
            z = np.concatenate([xx, s]); d, g = d_and_grad(z, n1, 0, P, ys); return d, g[:n1]
        r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 6000})
        if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, s]))
    W1, s1, Q1 = pieces(best[1], n1, P, ys)
    r2 = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), best[1], jac=True, method='L-BFGS-B', options={'maxiter': 6000})
    W2_, s2, Q2 = pieces(r2.x, n1, P, ys)
    z3 = np.concatenate([r2.x, ys])
    r3 = minimize(lambda z: d_and_grad(z, n1, 0, P, None), z3, jac=True, method='L-BFGS-B',
                  bounds=[(None, None)] * (n1 + P) + [(0.8, 3.0)] * P, options={'maxiter': 6000})
    W3, s3, Q3 = pieces(r3.x[:n1 + P], n1, P, r3.x[n1 + P:])
    print('P=%2d (cont. Q_pp %+.2f, T_g %.1f) | (i) W/def %+.4f s %.2f Q_pp %+.2f | (ii) W/def %+.4f s %.2f Q_pp %+.2f | (iii) W/def %+.4f s %.2f Q_pp %+.2f'
          % (P, cfg['Qpp'], cfg['Tg'], W1 / (g0 * P), s1, Q1, W2_ / (g0 * P), s2, Q2, W3 / (g0 * P), s3, Q3), flush=True)
