"""Band-1 constrained dual over MARKED periodic laws (the Zeta23 PairCeiling setting, LawN256.lean): N-periodic
configurations with marks m in {1,2} (simple points / on-line doubles), total multiplicity N per period N (density 1);
law weights w_c >= 0, sum 1; band-1 data: for 0 < j < N,  sum_c w_c |sum_i m_i e^{2 pi i j x_i / N}|^2 = j  (N S(j) = j,
zeta's form factor |alpha| on (0, 1)).  Objective: min simple-point fraction p = sum_c w_c (#simple)/N.
Column generation: master LP (HiGHS); pricing = multistart L-BFGS over positions for every number of doubles.
The LP value is the obstruction ceiling for ANY certificate reading only band-1 pair data + integrality configuration by
configuration (signed band-1 terms of every direction included); duals pi_j show which alpha = j/N directions bind.
usage: python3 marked_lp.py N rounds"""
import sys, time, math, numpy as np
from scipy.optimize import linprog, minimize
N = int(sys.argv[1]); ROUNDS = int(sys.argv[2]) if len(sys.argv) > 2 else 60
J = np.arange(1, N); target = J.astype(float)
rng = np.random.default_rng(1)
def feat(x, mk):
    E = np.exp(2j * np.pi * np.outer(J, x) / N)
    return np.abs(E @ mk) ** 2
cols = []; cost = []
def add(x, mk):
    cols.append(feat(x, mk)); cost.append(float((mk == 1).sum()) / N)
# seed columns: lattice (all simple), all doubles, random
add(np.arange(N, dtype=float), np.ones(N))
add(np.arange(N // 2, dtype=float) * 2, np.full(N // 2, 2.0))
for k in range(0, N // 2 + 1):
    for _ in range(4):
        npts = N - k; x = np.sort(rng.uniform(0, N, npts)); mk = np.ones(npts); mk[rng.choice(npts, k, replace=False)] = 2
        add(x, mk)
BIGM = 10.0
def master():
    # Phase-I-free master: slack columns (+/-) on every band-1 constraint at cost BIGM keep it feasible
    A = np.array(cols).T; C = len(cols); m_ = len(J)
    Aeq = np.vstack([np.hstack([A, np.eye(m_), -np.eye(m_)]), np.concatenate([np.ones(C), np.zeros(2 * m_)])])
    c_ = np.concatenate([np.array(cost), np.full(2 * m_, BIGM)])
    return linprog(c_, A_eq=Aeq, b_eq=np.concatenate([target, [1.0]]), bounds=[(0, None)] * (C + 2 * m_), method='highs')
t0 = time.time()
for it in range(ROUNDS):
    res = master()
    pi = res.eqlin.marginals[:-1]; mu = res.eqlin.marginals[-1]
    # pricing: min over configurations of cost - pi.feat - mu
    best = (0.0, None); found = 0
    for k in range(0, N // 2 + 1):
        npts = N - k; mk = np.ones(npts); mk[:k] = 2
        for s in range(6):
            x0 = np.sort(rng.uniform(0, N, npts)) if s else np.linspace(0, N, npts, endpoint=False)
            mk_s = rng.permutation(mk)
            f = lambda x: (mk_s == 1).sum() / N - pi @ feat(x, mk_s) - mu
            r = minimize(f, x0, method='L-BFGS-B')
            if r.fun < -1e-9:
                add(r.x % N, mk_s); found += 1
                if r.fun < best[0]: best = (r.fun, k)
    if it % 5 == 0 or found == 0:
        w = res.x; p = res.fun; sl = float(res.x[len(cols):].sum())
        print('it %d: LP obj %.8f (slack %.2e), columns %d, new %d, most negative reduced cost %.2e (k=%s) (%.0fs)'
              % (it, p, sl, len(cols), found, best[0], best[1], time.time() - t0), flush=True)
    if found == 0: break
res = master()
pi = res.eqlin.marginals[:-1]
slack = float(res.x[len(cols):].sum())
print('FINAL N=%d: min simple fraction p = %.8f (residual slack %.2e); dual weights pi_j (alpha = j/N):' % (N, res.fun - BIGM * slack, slack))
print('  ' + ' '.join('%.3f:%+.4f' % (j / N, pi[j - 1]) for j in J))
used = [(res.x[c], cost[c]) for c in range(len(cols)) if res.x[c] > 1e-6]
print('  support: %d configurations; simple fractions %s' % (len(used), sorted(set(round(u[1], 4) for u in used))))
