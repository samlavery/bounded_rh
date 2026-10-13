"""Marked-law LP with ONLY the R8 window datum (positive control in the marked-law frame): min simple fraction over
N-periodic marked laws subject to  sum_c w_c sum_j qf(j/N) |S_c(j)|^2 = sum_j qf(j/N) j  (the window's band-1 pair sum
at zeta's form factor), plus optionally the first K band-1 directions exactly.  usage: python3 marked_lp_window.py N K"""
import sys, json, time, numpy as np
from scipy.optimize import linprog, minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
N = int(sys.argv[1]); KD = int(sys.argv[2]) if len(sys.argv) > 2 else 0; STARTS = int(sys.argv[3]) if len(sys.argv) > 3 else 6
c = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'])
J = np.arange(1, N); qv = make_qf(c)(J / N)
rows = [qv] + [np.eye(N - 1)[k] for k in range(KD)]
R = np.array(rows); tgt = R @ J.astype(float)
rng = np.random.default_rng(3); cols = []; cost = []
def feat(x, mk): return np.abs(np.exp(2j * np.pi * np.outer(J, x) / N) @ mk) ** 2
def add(x, mk): cols.append(R @ feat(x, mk)); cost.append(float((mk == 1).sum()) / N)
add(np.arange(N, dtype=float), np.ones(N)); add(np.arange(N // 2, dtype=float) * 2, np.full(N // 2, 2.0))
for k in range(N // 2 + 1):
    for _ in range(4):
        npts = N - k; x = np.sort(rng.uniform(0, N, npts)); mk = np.ones(npts); mk[rng.choice(npts, k, replace=False)] = 2; add(x, mk)
BIGM = 10.0; m_ = R.shape[0]
def master():
    A = np.array(cols).T; C = len(cols)
    Aeq = np.vstack([np.hstack([A, np.eye(m_), -np.eye(m_)]), np.concatenate([np.ones(C), np.zeros(2 * m_)])])
    return linprog(np.concatenate([cost, np.full(2 * m_, BIGM)]), A_eq=Aeq, b_eq=np.concatenate([tgt, [1.0]]), bounds=[(0, None)] * (C + 2 * m_), method='highs')
t0 = time.time()
for it in range(150):
    res = master(); pi = res.eqlin.marginals[:-1]; mu = res.eqlin.marginals[-1]; found = 0
    for k in range(N // 2 + 1):
        npts = N - k; mk = np.ones(npts); mk[:k] = 2
        for s in range(STARTS):
            mk_s = rng.permutation(mk); x0 = np.sort(rng.uniform(0, N, npts)) if s else np.linspace(0, N, npts, endpoint=False)
            f = lambda x: (mk_s == 1).sum() / N - pi @ (R @ feat(x, mk_s)) - mu
            r = minimize(f, x0, method='L-BFGS-B')
            if r.fun < -1e-9: add(r.x % N, mk_s); found += 1
    if found == 0: break
res = master(); sl = float(res.x[len(cols):].sum())
S_zeta = None
print('N=%d, window + %d directions: min simple fraction %.8f (slack %.1e, %d rounds, %.0fs)' % (N, KD, res.fun - BIGM * sl, sl, it, time.time() - t0), flush=True)

w = res.x[:len(cols)]
sup = [(w[i], cost[i], cols[i][0]) for i in range(len(cols)) if w[i] > 1e-6]
print('  support (weight, simple fraction p_c, window datum sum_j qf |S_j|^2 vs zeta %.4f):' % tgt[0])
for wt, pc, d in sorted(sup, key=lambda t: t[1]): print('    w %.4f  p_c %.4f  datum %.4f' % (wt, pc, d))
