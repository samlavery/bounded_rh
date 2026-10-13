"""Continuum-faithful window optimisation for the D form with delta_true.
Window: q(a) = sum_b w_b hat_b(a), hats on nodes b/B (b = 0..B-1), q(1) = 0, w >= 0 (so q >= 0).  Normalise int_0^1 q a = 1.
A configuration v at period N_v (non-simple fraction 1 - p_v, |S_j|^2 = F_vj) gives the linear cut
    sum_j q(j/N_v) F_vj / N_v^2  >=  delta (1 - p_v)
and kappa = 1 - 1/delta (Montgomery's band datum int q a; the D(delta) consequence).  Single defects at every period
N in NSET are superlattices of spacing N; clusters k = 2..4 at the cluster periods.  LP: max delta over (w, delta).
usage: python3 winopt_cont.py B ROUNDS"""
import sys, json, time, numpy as np
from scipy.optimize import linprog, minimize
B, ROUNDS = int(sys.argv[1]), int(sys.argv[2]); sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
t0 = time.time(); nodes = np.arange(B) / B
def hats(a):
    a = np.asarray(a, float); H = np.maximum(0, 1 - np.abs(a[:, None] * B - np.arange(B)[None, :])); return H
from scipy.integrate import quad
mom = np.array([quad(lambda a, b=b: max(0.0, 1 - abs(a * B - b)) * a, 0, 1, points=[b / B], limit=200)[0] for b in range(B)])
NSET = list(range(3, 49)); CLUS = [(48, 2), (48, 3), (48, 4), (64, 2), (64, 3), (64, 4)]
cuts = []   # (row over w, 1 - p)
def add_cut(N, F, frac):
    J = np.arange(1, N); cuts.append((hats(J / N).T @ F / N ** 2, frac))
def single_any(q, N, starts):
    J = np.arange(1, N); out = []
    inits = [unrelaxed(N, dv) for dv in range(1, max(2, N // 2))] if N >= 4 else []
    inits += [rng.uniform(-N / 2, N / 2, N - 2) for _ in range(starts)]
    for z0 in inits:
        if len(z0) != N - 2: continue
        r = minimize(lambda y: energy(y, q, N, J), z0, jac=True, method='L-BFGS-B'); out.append((float(r.fun), np.concatenate([r.x, [0.0]])))
    return min(out, key=lambda t: t[0])
def F_of(z, N, k, t):
    J = np.arange(1, N); n1 = N - 2 * k - 3 * t
    return np.abs(np.exp(2j * np.pi * np.outer(J, z) / N) @ np.concatenate([np.ones(n1), np.full(k, 2.0), np.full(t, 3.0)])) ** 2
# seed: R8 window
w = np.maximum(0, q_family(R8C, 2 * B + 1)[1::2][:B] if False else make_qf(R8C)(nodes)); w = w / (w @ mom)
hist = []
for it in range(ROUNDS):
    new = 0; worst = 0.0
    if cuts:
        A = np.array([np.concatenate([-row, [frac]]) for row, frac in cuts])          # -row.w + delta frac <= 0
        r = linprog(np.concatenate([np.zeros(B), [-1.0]]), A_ub=A, b_ub=np.zeros(len(cuts)), A_eq=np.concatenate([mom, [0.0]])[None, :], b_eq=[1.0],
                    bounds=[(0, None)] * B + [(0, None)], method='highs')
        w = r.x[:B]; delta = r.x[-1]
    else:
        delta = np.inf
    qfun = lambda a: hats(a) @ w
    for N in NSET:
        q = qfun(np.arange(1, N) / N); d, z = single_any(q, N, 6)
        if d / N ** 2 < delta * 2 / N * (1 - 1e-9): add_cut(N, F_of(z, N, 1, 0), 2 / N); new += 1; worst = min(worst, d / N ** 2 / (2 / N) - delta)
    if it % 3 == 0 or new == 0:
        for (N, k) in CLUS:
            q = qfun(np.arange(1, N) / N); d, z = dmin_type(q, N, k, 0, 24)
            if d / N ** 2 < delta * 2 * k / N * (1 - 1e-9): add_cut(N, F_of(z, N, k, 0), 2 * k / N); new += 1; worst = min(worst, d / N ** 2 / (2 * k / N) - delta)
    kap = 1 - 1 / delta if np.isfinite(delta) else float('nan')
    print('it %d: delta %.6f  kappa %.7f  new cuts %d  worst gap %.2e  (%.0fs)' % (it, delta, kap, new, worst, time.time() - t0), flush=True)
    hist.append((kap, w.copy()))
    if new == 0 and np.isfinite(delta): break
json.dump({'B': B, 'w': list(map(float, w)), 'delta_int_qa_1': float(delta), 'kappa': float(1 - 1 / delta)}, open('winopt_cont_B%d.json' % B, 'w'), indent=1)
print('CONT B=%d: kappa (delta_true form) %.7f ; q(a)/q(0) at a = k/12: %s' % (B, 1 - 1 / delta, ' '.join('%.3f' % v for v in (hats(np.arange(12) / 12) @ w) / w[0])))
