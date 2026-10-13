"""E13: exact Lemma P W for the stack configurations of e12 (two stacks of multiplicity m at depth 0.8 + a chain of k deeper
pairs), periodic model of band1/lemmaP.py with the backed R8 certificate, cluster embedded in a lattice environment.
(i) environment relaxed (cluster fixed); (ii) chain centres + environment relaxed (stacks, depths fixed).
Reports W, W/defect (units g(0)), s(D) split into T_g and the h-part, and Q_pp (periodic grid)."""
import sys, json, numpy as np
from scipy.optimize import minimize
k = int(sys.argv[1]); ms = [int(v) for v in sys.argv[2].split(',')]; NN = int(sys.argv[3])
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(19)
data = json.load(open('e12_k%d.json' % k))

def g_vec(u):
    u = np.asarray(u, float); out = np.empty(u.shape); z = np.abs(u) < 1e-9; out[z] = g0
    if np.any(~z): out[~z] = g_of(u[~z])
    return out

def pieces(z, n1, P, ys):
    x = z[:n1]; s = z[n1:n1 + P]
    d, _ = d_and_grad(z, n1, 0, P, ys)
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
    xr = np.concatenate([x, s]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)])
    sl = d_real(xr, mr) / N - N * (gN0 - gh0) / 2 - gN0 * P
    # T_g of D over DISTINCT points (stacks merged), ordered pairs, periodic distance
    pts = {}
    for xx, mm in zip(xr, mr):
        key = round(float(xx) % N, 6); pts[key] = pts.get(key, 0.0) + mm
    px = np.array(list(pts.keys())); pm = np.array(list(pts.values()))
    D = ((px[:, None] - px[None, :]) + N / 2) % N - N / 2; off = ~np.eye(len(px), dtype=bool)
    Tg = float((pm[:, None] * pm[None, :])[off] @ g_vec(D[off]))
    Es = np.exp(2j * np.pi * np.outer(J, s) / N); c = 2 * np.cosh(2 * np.pi * np.outer(J, ys) / N)
    Qpp = float((2 / N) * np.sum(qv * (np.abs((c * Es).sum(1)) ** 2 - 4 * np.abs(Es.sum(1)) ** 2)))
    return W, sl, Tg, Qpp

for m in ms:
    e = data[str(m)]; s_items = np.array(e['s']); y_items = np.array(e['y']); m_items = np.array(e['m']).astype(int)
    s = np.repeat(4.0 + s_items, m_items); ys = np.repeat(y_items, m_items); P = len(s)
    n1 = N - 2 * P
    occ = set()
    for t in s: occ |= {int(np.floor(t)) % N, int(np.ceil(t)) % N}
    base = np.array([t for t in range(N) if t not in occ], float)
    if len(base) < n1: base = np.concatenate([base, rng.uniform(s.max() + 2, N, n1 - len(base))])
    base = np.sort(base)[:n1]
    best = (np.inf, None)
    for kk in range(3):
        x0 = base + rng.normal(0, 0.03 * kk, n1)
        def f(xx):
            z = np.concatenate([xx, s]); d, g = d_and_grad(z, n1, 0, P, ys); return d, g[:n1]
        r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 6000})
        if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, s]))
    W, sl, Tg, Qpp = pieces(best[1], n1, P, ys)
    print('m=%3d k=%d P=%3d N=%d: (i) W %+10.3f  W/def %+8.4f | s %9.3f (T_g/2 %9.3f) | Q_pp %+10.3f (cont. %+10.3f) | 2W ~ 2s + Q_pp + field'
          % (m, k, P, N, W, W / (g0 * P), sl, Tg / 2, Qpp, e['Qpp']), flush=True)
