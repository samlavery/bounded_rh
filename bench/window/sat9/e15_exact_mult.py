"""E15: Lemma P with EXACT multiplicities, independent of band1/lemmaP.py's W formula.
Periodic model, period N, total multiplicity N (on-line simple points + 2 * sum of pair multiplicities).
  S_j = sum_on e(j x/N) + sum_items m_i 2 cosh(2 pi j y_i/N) e(j s_i/N)        (items = off-line zeros, multiplicity m_i)
  E(Z) = (1/N) [ q(0) N^2 + 2 sum_{j=1}^{N-1} q(j/N) |S_j|^2 ]                 (two-sided)
  D(Z): each item -> ONE point of mass 2 m_i at s_i;  F_C(D) = (q(0) - g^(0)) N + g_N(0) sum_{points of D} mass^2
  LP = E(Z) - F_C(D(Z));  Lemma P <=> LP >= 0.   Also E(D), s(D) = E(D) - F_C(D), Delta = E(Z) - E(D).
The environment (simple on-line points) is relaxed with the items fixed (L-BFGS on E(Z), analytic gradient).
Configurations: e12_k<k>.json (two stacks of multiplicity m + chain), and e9_cfg_<P>.json with near-coincident pairs merged
(within tol) into exact multiplicities."""
import sys, json, numpy as np
from scipy.optimize import minimize
from fractions import Fraction
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
B1 = '/Users/samuellavery/work/riemann-submission/bench/window/band1/'
cw = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24)
qfun = make_qf(cw)
cj = json.load(open(B1 + 'cert_R8_backed.json'))
yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); Dk = 1 / 32; nb = len(yk)
g0 = Dk * (yk[0] + 2 * yk[1:].sum()); gh0 = yk[0]
def g_of(u):
    u = np.atleast_1d(np.asarray(u, float)); out = np.empty(len(u)); z = np.abs(u) < 1e-12
    th = 2 * np.pi * Dk * u[~z]; Cc = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:])
    out[~z] = Dk * np.sinc(Dk * u[~z]) ** 2 * Cc; out[z] = g0; return out

def setup(N):
    J = np.arange(1, N); q = qfun(np.minimum(J / N, 0.9999999)); q0 = float(qfun(np.array([0.0]))[0])
    gN0 = g0 + 2 * float(np.sum(g_of(np.arange(1, 20001) * N)))
    return J, q, q0, gN0

def energy(x, items, N, J, q, q0):
    s, y, m = items
    Ex = np.exp(2j * np.pi * np.outer(J, x) / N)
    S = Ex.sum(1) + (np.exp(2j * np.pi * np.outer(J, s) / N) * 2 * np.cosh(2 * np.pi * np.outer(J, y) / N)) @ m
    E = (q0 * N ** 2 + 2 * float(q @ np.abs(S) ** 2)) / N
    W = (q * np.conj(S))[:, None]
    gx = 2 * 2 * np.real(W * Ex * (2j * np.pi * J[:, None] / N)).sum(0) / N
    return E, gx

def energy_D(x, items, N, J, q, q0):
    s, y, m = items
    S = np.exp(2j * np.pi * np.outer(J, x) / N).sum(1) + np.exp(2j * np.pi * np.outer(J, s) / N) @ (2 * m)
    return (q0 * N ** 2 + 2 * float(q @ np.abs(S) ** 2)) / N

def FC(n_on, items, N, q0, gN0):
    m = items[2]; return (q0 - gh0) * N + gN0 * (n_on + float(np.sum((2 * m) ** 2)))

def run(tag, s, y, m, N, rng):
    J, q, q0, gN0 = setup(N)
    items = (np.asarray(s, float) + 5.0, np.asarray(y, float), np.asarray(m, float))
    n_on = N - int(2 * np.sum(m))
    occ = set()
    for t in items[0]: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.array([t for t in range(N) if t not in occ], float)
    base = np.sort(base)[:n_on] if len(base) >= n_on else np.concatenate([base, rng.uniform(items[0].max() + 2, N, n_on - len(base))])
    best = (np.inf, None)
    for k in range(3):
        x0 = base + rng.normal(0, 0.03 * k, n_on)
        r = minimize(lambda x: energy(x, items, N, J, q, q0), x0, jac=True, method='L-BFGS-B', options={'maxiter': 8000})
        if r.fun < best[0]: best = (r.fun, r.x)
    EZ, x = best; ED = energy_D(x, items, N, J, q, q0); F = FC(n_on, items, N, q0, gN0)
    LP = EZ - F; sD = ED - F; dB = EZ - ED
    ndef = int(np.sum(m))
    print('%-22s N=%3d items=%2d mult=%s | LP = E(Z) - F_C(D(Z)) = %+10.3f (per defect, units g(0): %+.4f) | s(D) %+10.3f | E(Z)-E(D) %+10.3f'
          % (tag, N, len(m), np.asarray(m).astype(int).tolist()[:12], LP, LP / 2 / (g0 * ndef), sD, dB), flush=True)
    return LP

if __name__ == '__main__':
    rng = np.random.default_rng(7)
    mode = sys.argv[1]
    if mode == 'stacks':
        k = int(sys.argv[2]); N = int(sys.argv[3]); ms = [int(v) for v in sys.argv[4].split(',')]
        data = json.load(open((sys.argv[5] if len(sys.argv) > 5 else 'e12') + '_k%d.json' % k))
        for mm in ms:
            e = data[str(mm)]
            run('stacks m=%d k=%d' % (mm, k), e['s'], e['y'], e['m'], N, rng)
    else:
        P = int(sys.argv[2]); N = int(sys.argv[3]); tol = float(sys.argv[4]) if len(sys.argv) > 4 else 0.01
        cfg = json.load(open('e9_cfg_%d.json' % P)); s = np.array(cfg['s']); y = np.array(cfg['y'])
        # merge near-coincident pairs (same depth class) into exact multiplicity
        order = np.argsort(s); s, y = s[order], y[order]
        S, Y, M = [], [], []
        for si, yi in zip(s, y):
            if S and abs(si - S[-1]) < tol and abs(yi - Y[-1]) < 0.05:
                M[-1] += 1; S[-1] = (S[-1] * (M[-1] - 1) + si) / M[-1]
            else:
                S.append(si); Y.append(yi); M.append(1)
        run('e9 P=%d merged(tol %.3f)' % (P, tol), S, Y, M, N, rng)
        run('e9 P=%d unmerged' % P, s, y, np.ones(len(s)), N, rng)
