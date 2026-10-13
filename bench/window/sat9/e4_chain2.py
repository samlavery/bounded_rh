"""E4: exact W (band1/lemmaP.py periodic model, backed R8 certificate) minimised over pair centres, environment, and (option)
pair depths, starting from cancelling clusters; reports
  W/defect (units g(0)),
  chainCS = 2s + X^2 - (4P + 2 M_near) X - far          (the posed chain; X = ||S_B||),
  chain2  = 2s + Q_pp + ... with the pair-pair term exact: 2s + Q_pp - 2 ||S_on^near||_q X - far,
where near = on-line points within distance R0 = 1 of a pair centre, far = |2 <S_on^far, S_B>| (exact), Q_pp exact.
2W = 2s + Q_pp + 2<S_on, S_B> exactly, so chain2 <= 2W; chain2 >= 0 is the corrected step-9 requirement."""
import sys, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[3]) if len(sys.argv) > 3 else 128
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(29)
R0 = 1.0

def pieces(z, n1, P, ys):
    x = z[:n1]; s = z[n1:n1 + P]
    d, _ = d_and_grad(z, n1, 0, P, ys)
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
    xr = np.concatenate([x, s]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)])
    dD = d_real(xr, mr); sl = dD / N - N * (gN0 - gh0) / 2 - gN0 * P
    Ex = np.exp(2j * np.pi * np.outer(J, x) / N); Es = np.exp(2j * np.pi * np.outer(J, s) / N)
    A = 2 * np.cosh(2 * np.pi * np.outer(J, ys) / N) - 2
    U = (A * Es).sum(1); V = Es.sum(1)
    ip = lambda F, G: float((2 / N) * np.sum(qv * np.real(np.conj(F) * G)))
    X = np.sqrt(ip(U, U)); Qpp = ip(U, U) + 4 * ip(V, U)
    dist = np.min(np.abs(((x[:, None] - s[None, :]) + N / 2) % N - N / 2), axis=1)
    near = dist < R0
    Sn = Ex[:, near].sum(1); Sf = Ex[:, ~near].sum(1)
    nSn = np.sqrt(ip(Sn, Sn)); far = abs(2 * ip(Sf, U)); Mn = int(near.sum())
    chainCS = 2 * sl + X ** 2 - (4 * P + 2 * Mn) * X - far
    chain2 = 2 * sl + Qpp - 2 * nSn * X - far
    exact = 2 * sl + Qpp + 2 * ip(Sn + Sf, U)
    return W, sl, X, Qpp, Mn, nSn, far, chainCS, chain2, exact

def lattice_start(P, s):
    n1 = N - 2 * P; occ = set()
    for t in s: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.array([t for t in range(N) if t not in occ], float)
    if len(base) < n1: base = np.concatenate([base, rng.uniform(0, N, n1 - len(base))])
    return base[:n1]

def search(P, yfix, yb, s_list, starts_env=2):
    n1 = N - 2 * P; best = (np.inf, None, None)
    for s_rel in s_list:
        s = 8.0 + np.asarray(s_rel, float)
        for k in range(starts_env):
            x0 = lattice_start(P, s) + rng.normal(0, 0.03 * k, n1)
            if yfix is not None:
                ys = np.full(P, yfix)
                r = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), np.concatenate([x0, s]), jac=True, method='L-BFGS-B',
                             options={'maxiter': 5000})
                cand = (r.fun, r.x, ys)
            else:
                y0 = rng.uniform(yb[0], yb[1], P)
                r = minimize(lambda z: d_and_grad(z, n1, 0, P, None), np.concatenate([x0, s, y0]), jac=True, method='L-BFGS-B',
                             bounds=[(None, None)] * (n1 + P) + [yb] * P, options={'maxiter': 5000})
                cand = (r.fun, r.x[:n1 + P], r.x[n1 + P:])
            if cand[0] < best[0]: best = cand
    return best

def report(tag, P, best):
    _, z, ys = best; n1 = N - 2 * P
    W, sl, X, Qpp, Mn, nSn, far, cCS, c2, ex = pieces(z, n1, P, ys)
    print('  %-22s P=%2d: W/def %+9.3f | s %8.3f X %9.3f Q_pp %+11.3e | M_near %2d ||S_near|| %6.3f far %9.3f | chainCS %+11.2f chain2 %+11.2f (2W %+11.2f) | y %s'
          % (tag, P, W / (g0 * P), sl, X, Qpp, Mn, nSn, far, cCS, c2, ex, np.round(np.sort(ys), 2)[:6]), flush=True)

def cluster_starts(P):
    out = [0.5 * np.arange(P), 0.6 * np.arange(P), 1.5 * np.arange(P)]
    out.append(np.sort(rng.uniform(0, 0.6 * P, P)))
    return out

mode = sys.argv[1] if len(sys.argv) > 1 else 'equal'
Ps = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [8, 16]
if mode == 'equal':
    for y in (0.8, 1.0, 1.5):
        print('equal depth y = %.1f (N = %d)' % (y, N), flush=True)
        for P in Ps:
            report('y=%.1f all relaxed' % y, P, search(P, y, None, cluster_starts(P)))
else:
    yb = tuple(float(v) for v in mode.split(':'))
    print('free depths in [%.2f, %.2f] (N = %d)' % (yb[0], yb[1], N), flush=True)
    for P in Ps:
        report('free depths', P, search(P, None, yb, cluster_starts(P), starts_env=3))
