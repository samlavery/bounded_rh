"""Realisation test for the single-window (R8) marked-law certificate (c0, lam):  p_c >= c0 + lam * d_c  for every
N-periodic configuration, d_c = sum_{0<j<N} qf(j/N) |S_c(j)|^2.

Configuration elements (all on a circle of length N, total count N):
  simple on-line zero : amplitude 1, count 1, simple 1
  pair-site at depth y: amplitude 2cosh(2 pi j y / N) at frequency j, count 2, simple 0   (y = 0 is an on-line double)
  triple              : amplitude 3, count 3, simple 0
The pair amplitude is the all-ones form of Zeta23's Hermitian frame: for a zero multiset closed under conjugation,
sum_{a,b} K(g_a - g_b) = int qf(a) |sum_a e^{2 pi i a g_a}|^2 da, and the pair {s - iy, s + iy} gives e(a s) 2cosh(2 pi a y).

For the window-only LP the pricing problem for a type (k pair-sites, t triples) is min d over positions and depths, so the
law's minimum simple fraction is the lower convex hull at d = target of the points (p_type, d_min(type)), together with
the lattice (1, 0).  usage: python3 realise.py N YMAX STARTS"""
import sys, json, time, numpy as np
from scipy.optimize import minimize, linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
N = int(sys.argv[1]); YMAX = float(sys.argv[2]); STARTS = int(sys.argv[3])
c = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'])
J = np.arange(1, N).astype(float); q = make_qf(c)(J / N); TGT = float(q @ J)
rng = np.random.default_rng(11)

def datum(z, n1, k, t, grad=True):
    """z = (x_0..x_{n-1}, y_0..y_{k-1}); sites ordered simple | pair | triple."""
    n = n1 + k + t; x = z[:n]; y = z[n:]
    E = np.exp(2j * np.pi * np.outer(J, x) / N)
    A = np.empty((len(J), n)); A[:, :n1] = 1.0; A[:, n1 + k:] = 3.0
    ch = 2 * np.cosh(2 * np.pi * np.outer(J, y) / N); A[:, n1:n1 + k] = ch
    S = (E * A).sum(1); d = float(q @ np.abs(S) ** 2)
    if not grad: return d
    W = (q * np.conj(S))[:, None] * E
    gx = 2 * np.real(W * A * (2j * np.pi * J[:, None] / N)).sum(0)
    gy = 2 * np.real(W[:, n1:n1 + k] * 2 * np.sinh(2 * np.pi * np.outer(J, y) / N) * (2 * np.pi * J[:, None] / N)).sum(0)
    return d, np.concatenate([gx, gy])

def dmin(k, t, ymax, starts, yfix=None, seeds=()):
    n1 = N - 2 * k - 3 * t; n = n1 + k + t; best = (np.inf, None)
    if n1 < 0: return best
    m = np.array([1] * n1 + [2] * k + [3] * t, float)
    for s in range(-len(seeds), starts):
        order = rng.permutation(n)
        if s < 0:
            x0 = seeds[s][:n].copy()
        elif s % 3 == 2:   # evenly spread defects in a mass-uniform chain
            sl = np.round(np.linspace(0, n, k + t, endpoint=False)).astype(int); ty = np.zeros(n, int); ty[sl] = [2] * k + [3] * t
            mm = np.where(ty == 0, 1, ty).astype(float); gaps = (mm + np.roll(mm, -1)) / 2; pos = np.concatenate([[0], np.cumsum(gaps)[:-1]])
            idx = np.empty(n, int); idx[ty == 1] = 0; idx[ty == 0] = np.arange(n1); idx[np.where(ty == 2)[0]] = n1 + np.arange(k); idx[np.where(ty == 3)[0]] = n1 + k + np.arange(t)
            x0 = np.empty(n); x0[idx] = pos + rng.normal(0, 0.05, n)
        elif s % 2 == 0:   # mass-uniform placement in random order: gap between neighbours = mean of their counts
            mm = m[order]; gaps = (mm + np.roll(mm, -1)) / 2; pos = np.concatenate([[0], np.cumsum(gaps)[:-1]])
            x0 = np.empty(n); x0[order] = pos + rng.normal(0, 0.15, n)
        else:
            x0 = rng.uniform(0, N, n)
        if yfix is None:
            y0 = (np.full(k, 0.01 * (s + 2) * ymax) if s < 0 else rng.uniform(0, ymax, k) if s % 3 else np.zeros(k))
            bnds = [(None, None)] * n + [(0.0, ymax)] * k
            r = minimize(lambda z: datum(z, n1, k, t), np.concatenate([x0, y0]), jac=True, method='L-BFGS-B', bounds=bnds)
            z = r.x
        else:
            yv = np.full(k, yfix)
            r = minimize(lambda x: (lambda dg: (dg[0], dg[1][:n]))(datum(np.concatenate([x, yv]), n1, k, t)), x0, jac=True, method='L-BFGS-B')
            z = np.concatenate([r.x, yv])
        if r.fun < best[0]: best = (float(r.fun), z.copy())
    return best

def hull(points):
    """min E p s.t. E d_min <= TGT over mixtures of type corners (p, d_min) and the lattice (1, 0); a type's datum can be
    raised freely, so this equals the marked LP's value.  Returns (min p, c0, lam) with  p_t >= c0 + lam d_min_t  dual."""
    P = np.array([1.0] + [p for (p, d, _) in points]); D = np.array([0.0] + [d for (p, d, _) in points])
    r = linprog(P, A_ub=D[None, :], b_ub=[TGT], A_eq=np.ones((1, len(P))), b_eq=[1.0], bounds=[(0, None)] * len(P), method='highs')
    lam = float(r.ineqlin.marginals[0]); c0 = float(r.eqlin.marginals[0])
    sup = [(float(r.x[i]), (('lattice',) if i == 0 else points[i - 1][2])) for i in range(len(P)) if r.x[i] > 1e-9]
    return float(r.fun), c0, lam, sup

if __name__ == '__main__':
    t0 = time.time(); out = {'N': N, 'YMAX': YMAX, 'STARTS': STARTS, 'target': TGT}
    types = [(k, t) for t in range(0, N // 3 + 1) for k in range(0, (N - 3 * t) // 2 + 1) if (k, t) != (0, 0)]
    base = {kt: dmin(kt[0], kt[1], 0.0, STARTS, yfix=0.0) for kt in types}
    P = lambda k, t: (N - 2 * k - 3 * t) / N
    # (A) marks {1,2}, on-line only: control against marked_window2.log, and the certificate (c0, lam)
    vA, c0, lam, supA = hull([(P(k, 0), base[(k, 0)][0], (k, 0)) for (k, t) in types if t == 0])
    print('N=%d target %.4f | marks {1,2} on-line: min p %.8f  support %s | certificate c0 %.8f lam %.6e  (%.0fs)'
          % (N, TGT, vA, [(round(w, 4), tg) for (w, tg) in supA], c0, lam, time.time() - t0), flush=True)
    print('  d_min(k), y=0:', ' '.join('%d:%.3f' % (k, base[(k, 0)][0]) for (k, t) in types if t == 0 and k <= 8), flush=True)
    slk = lambda k, t, d: P(k, t) - c0 - lam * d
    def hess_y(k, t):   # exact second y-derivative of d at a y = 0 optimum, per double site (the y-gradient vanishes there)
        z = base[(k, t)][1]; n1 = N - 2 * k - 3 * t; n = n1 + k + t; x = z[:n]
        E = np.exp(2j * np.pi * np.outer(J, x) / N); A = np.ones((len(J), n)); A[:, n1:n1 + k] = 2.0; A[:, n1 + k:] = 3.0
        S = (E * A).sum(1); return 4 * np.real((q * (2 * np.pi * J / N) ** 2 * np.conj(S))[:, None] * E[:, n1:n1 + k]).sum(0)
    hy = [(float(hess_y(k, t).min()), k, t) for (k, t) in types if k]
    print('  y-Hessian at the y=0 optima: min over all double sites of all types %+.4f at %s; min over t=0 types %+.4f'
          % (min(hy)[0], min(hy)[1:], min(h for h in hy if h[2] == 0)[0]), flush=True)
    # (A3) add triples (on-line, y = 0)
    vA3, _, _, supA3 = hull([(P(k, t), base[(k, t)][0], (k, t)) for (k, t) in types])
    wt = min((slk(k, t, base[(k, t)][0]), k, t) for (k, t) in types if t > 0)
    print('  + triples: min p %.8f  support %s | certificate worst slack on triple types %+.6f at k=%d t=%d'
          % (vA3, [(round(w, 4), tg) for (w, tg) in supA3], *wt), flush=True)
    out['A'] = {'minp': vA, 'c0': c0, 'lam': lam, 'support': [(w, list(tg)) for (w, tg) in supA],
                'dmin0': {'%d,%d' % kt: base[kt][0] for kt in types}, 'minp_triples': vA3, 'triple_worst_slack': wt[0]}
    # (B) common fixed depth y for every non-simple site (t = 0): slack of the (A) certificate
    out['B'] = {}
    for y in [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
        sl = []
        for (k, t) in types:
            if t: continue
            d, _ = dmin(k, 0, y, max(4, STARTS // 4), yfix=y, seeds=[base[(k, 0)][1]]); sl.append((slk(k, 0, d), k, d))
        mn = min(sl); out['B'][str(y)] = {'min_slack': mn[0], 'k': mn[1], 'd': mn[2]}
        print('  common depth y=%.3f: worst slack %+.7f at k=%d (d_min %.4f vs y=0 %.4f)' % (y, mn[0], mn[1], mn[2], base[(mn[1], 0)][0]), flush=True)
    # (C) free per-site depths in [0, YMAX] plus triples, seeded from the y = 0 optimum: re-solve
    free = {}
    for (k, t) in types:
        if k == 0: free[(k, t)] = base[(k, t)]; continue
        free[(k, t)] = dmin(k, t, YMAX, max(4, STARTS // 4), seeds=[base[(k, t)][1]] * 3)
        if base[(k, t)][0] < free[(k, t)][0]: free[(k, t)] = base[(k, t)]
    vC, c0C, lamC, supC = hull([(P(k, t), free[(k, t)][0], (k, t)) for (k, t) in types])
    gain = max(((base[kt][0] - free[kt][0]), kt) for kt in types)
    print('  largest drop type %s: depths %s' % (gain[1], np.round(free[gain[1]][1][N - gain[1][0] - 2 * gain[1][1]:], 5)), flush=True)
    wc = min((slk(k, t, free[(k, t)][0]), k, t) for (k, t) in types)
    def depths(kt):
        k, t = kt; z = free[kt][1]; n = N - k - 2 * t; return list(np.round(z[n:], 5)) if z is not None and k else []
    print('re-solved, pairs y in [0,%.2f] + triples: min p %.8f  support %s, depths in support %s | largest d_min drop vs y=0 %.2e at %s | (A) certificate worst slack %+.7f at k=%d t=%d  (%.0fs)'
          % (YMAX, vC, [(round(w, 4), tg) for (w, tg) in supC], [depths(tg) for (w, tg) in supC if tg != ('lattice',)], gain[0], gain[1], *wc, time.time() - t0), flush=True)
    out['C'] = {'minp': vC, 'c0': c0C, 'lam': lamC, 'support': [(w, list(tg)) for (w, tg) in supC], 'max_drop': gain[0], 'worst_slack': wc[0],
                'dmin_free': {'%d,%d' % kt: free[kt][0] for kt in types}}
    json.dump(out, open('realise_N%d_y%g.json' % (N, YMAX), 'w'), indent=1)
