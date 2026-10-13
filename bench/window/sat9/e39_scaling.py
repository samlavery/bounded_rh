"""E39 (lead, 2026-10-09): N proportional to P scaling test for near-density-1 deep chains in an environment.  Fixed BEFORE any run.
Model: as e38 (periodic, total mass N, pSq weights, depths in [0.8, 3]).  Families: a in {0.95, 0.99}; pair positions
  (i) FIXED on the lattice s_p = a p, (ii) FREE (seeded on the lattice); depths and environment free; N/P in {4, 8};
  P in {16, 32, 64, 128}.  Starts per case: depth profiles flat 0.8, arched 0.8 -> 1.5, random in [0.8, 1.6] (environment seeded
  uniformly outside the chain, as e38).  L-BFGS, maxiter 3000.  Every LP < 1 re-evaluated in mpmath (50 digits).
Report: LP, LP/P, slope dLP/dP between consecutive P at fixed (a, N/P, mode); environment density next to the chain (points in
  the windows of width 10 beyond each chain end, /20) and nominal far density (N - 2P)/(N - aP).
REFUTES: a confirmed LP < 0; or a negative slope at fixed N/P persisting through P = 128 with an extrapolated zero crossing
  (reported and marked as an extrapolation).  SUPPORTS: slope >= 0 within resolution at fixed N/P, or LP bounded below.
PREDICTION (bridge-port): SUPPORTS.  At fixed N/P the far environment density is constant ((4-2)/(4-a) ~ 0.66, (8-2)/(8-a) ~ 0.85),
  and a sub-unit-density on-line environment carries positive certificate slack per unit length (its in-band Bragg peak), so LP
  GROWS linearly in P; the e38b decrease came from N fixed while P grew (environment thinning with P), not from a bulk deficit."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 39)
fams = [(a, r, mode) for a in (0.95, 0.99) for r in (4, 8) for mode in ('fixed', 'free')]
if len(sys.argv) > 2: fams = [f for f in fams if ('%.2f' % f[0]) == sys.argv[2]]
out = []
for (a, ratio, mode) in fams:
    prev = None
    for P in (16, 32, 64, 128):
        N = ratio * P; M = Model(N, P); n = M.n_on; s = a * np.arange(P); t = np.arange(P) / (P - 1); best = (np.inf, None)
        for prof in ('flat', 'arch', 'rand'):
            y0 = np.full(P, 0.8) if prof == 'flat' else (0.8 + 0.7 * np.sin(np.pi * t) ** 0.8 if prof == 'arch' else rng.uniform(0.8, 1.6, P))
            z0 = embed(M, s, y0, rng, 0.02); sfix = z0[n:n + P].copy()
            if mode == 'fixed':
                def f(v):
                    z = np.concatenate([v[:n], sfix, v[n:]]); val, g = M.LP(z); return val, np.concatenate([g[:n], g[n + P:]])
                r = minimize(f, np.concatenate([z0[:n], z0[n + P:]]), jac=True, method='L-BFGS-B', bounds=[(None, None)] * n + [(0.8, 3.0)] * P, options={'maxiter': 3000})
                z = np.concatenate([r.x[:n], sfix, r.x[n:]])
            else:
                r = minimize(M.LP, z0, jac=True, method='L-BFGS-B', bounds=[(None, None)] * (n + P) + [(0.8, 3.0)] * P, options={'maxiter': 3000})
                z = r.x
            v = M.LP(z, False)
            if v < best[0]: best = (v, z.copy())
        v, z = best; x = np.mod(z[:n], N); sp = z[n:n + P]; lo, hi = sp.min() % N, sp.max() % N
        near = ((np.mod(x - hi, N) < 10) | (np.mod(lo - x, N) < 10)).sum() / 20.0; far = (N - 2 * P) / (N - (sp.max() - sp.min()))
        vm = M.LP_mp(z) if v < 1 else None
        sl = ('%+.4f' % ((v - prev[1]) / (P - prev[0]))) if prev else '   -   '
        print('a=%.2f N=%dP %-5s P=%3d N=%4d: LP %+11.4f (per pair %+.4f)%s | slope %s | env density near chain %.3f, nominal far %.3f | pair span %.2f'
              % (a, ratio, mode, P, N, v, v / P, (' [mp50 %+.6f]' % vm) if vm is not None else '', sl, near, far, sp.max() - sp.min()), flush=True)
        out.append({'a': a, 'ratio': ratio, 'mode': mode, 'P': P, 'N': N, 'LP': v, 'mp50': vm, 'z': z.tolist()})
        json.dump(out, open('e39_results%s.json' % (('_' + sys.argv[2]) if len(sys.argv) > 2 else ''), 'w'))
        prev = (P, v)
