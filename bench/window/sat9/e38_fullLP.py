"""E38 (lead, 2026-10-09): TRUTH CHECK of the full exact LP with DEEP pairs inside an on-line environment.  Fixed BEFORE any run.
MODEL: periodic, period N, total mass N.  Environment: n_on = N - 2P simple on-line points x_b.  P pairs at s_p +- i y_p,
  y_p in [0.8, 3].  S_j = sum_b e(j x_b/N) + sum_p 2cosh(2 pi j y_p/N) e(j s_p/N),  j = 1..N-1,  q_j = qf(j/N).
  E(Z) = (1/N)[q(0) N^2 + 2 sum_j q_j |S_j|^2];  pSq weights: F_C = (q(0) - ghat(0)) N + g_N(0)(n_on + 4P),
  g_N(0) = sum_k g(kN);  LP = E(Z) - F_C  (the form used in e15, which matched band1/lemmaP.py).
  Double-precision evaluation as  LP = (2/N) sum_j q_j|S_j|^2 - [g_N(0)(n_on+4P) - ghat(0) N]  (all terms of E are >= 0, so a
  small LP forces every q_j|S_j|^2 to be O(N); the only cancellation is inside S_j).  Every candidate with LP < 1 is
  RE-EVALUATED with S_j summed in mpmath at 50 digits (positions, depths, q_j, g_N(0), ghat(0) taken as the given doubles).
SEARCH: P in {2, 4, 8, 16, 32}, N in {64, 128, 256} (n_on >= 0), L-BFGS on (x, s, y) with analytic gradient, depths boxed.
  Seeds, each embedded in a density-1 environment placed outside the cluster and free to relax: e19/e23 arched chains (scaled to
  P), e9 stacks (P = 16, 32), chains at a in {0.9, 0.95, 0.99} with arched depths 0.8 -> 1.5, gap configurations (two blocks of
  pairs at 0.8, spacing 0.6, with deep pairs at y = 2 and 3 in the gaps), random clusters; plus random perturbations.
DECISION: REFUTES Lemma P configuration-wise: any LP < 0 confirmed in mpmath (saved).  SUPPORTS: min LP >= 0 everywhere; report
  the thinnest per-pair margin LP/P by regime and where it sits.
PREDICTION (bridge-port): SUPPORTS (~75%).  Thinnest per-pair margin in near-density-1 chains (a = 0.95-0.99), but >= 0.05 per
  pair, not below 0.01: with total mass fixed, a compressed chain forces an environment deficit whose P_h/T_g cost adds to
  tau(a).  (Lead's prediction: SUPPORTS ~70%, thinnest < 0.01 per pair in near-density-1 deep chains.)"""
import sys, json, time, numpy as np
from scipy.optimize import minimize
from fractions import Fraction
import mpmath as mp
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
B1 = '/Users/samuellavery/work/riemann-submission/bench/window/band1/'
cw = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24); qfun = make_qf(cw)
cj = json.load(open(B1 + 'cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); Dk = 1 / 32; nb = len(yk)
g0 = Dk * (yk[0] + 2 * yk[1:].sum()); gh0 = yk[0]
def g_of(u):
    u = np.atleast_1d(np.asarray(u, float)); out = np.empty(len(u)); z = np.abs(u) < 1e-12
    th = 2 * np.pi * Dk * u[~z]; Cc = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:])
    out[~z] = Dk * np.sinc(Dk * u[~z]) ** 2 * Cc; out[z] = g0; return out
class Model:
    def __init__(self, N, P):
        self.N, self.P = N, P; self.n_on = N - 2 * P; self.J = np.arange(1, N); self.al = self.J / N
        self.q = qfun(np.minimum(self.al, 0.9999999)); self.q0 = float(qfun(np.array([0.0]))[0])
        self.gN0 = g0 + 2 * float(np.sum(g_of(np.arange(1, 20001) * N)))
        self.const = self.gN0 * (self.n_on + 4 * P) - gh0 * N
    def LP(self, z, grad=True):
        N, P, n = self.N, self.P, self.n_on; x = z[:n]; s = z[n:n + P]; y = z[n + P:]
        Ex = np.exp(2j * np.pi * np.outer(self.J, x) / N); Es = np.exp(2j * np.pi * np.outer(self.J, s) / N)
        C = 2 * np.cosh(2 * np.pi * np.outer(self.al, y)); S = Ex.sum(1) + (C * Es).sum(1)
        val = (2 / N) * float(self.q @ np.abs(S) ** 2) - self.const
        if not grad: return val
        Wt = (self.q * np.conj(S))[:, None]; ia = (2j * np.pi * self.J / N)[:, None]
        gx = (4 / N) * np.real(Wt * Ex * ia).sum(0); gs = (4 / N) * np.real(Wt * C * Es * ia).sum(0)
        D = 4 * np.pi * self.al[:, None] * np.sinh(2 * np.pi * np.outer(self.al, y)); gy = (4 / N) * np.real(Wt * D * Es).sum(0)
        return val, np.concatenate([gx, gs, gy])
    def LP_mp(self, z, dps=50):
        mp.mp.dps = dps; N, P, n = self.N, self.P, self.n_on; x = z[:n]; s = z[n:n + P]; y = z[n + P:]
        tot = mp.mpf(0); twopi = 2 * mp.pi
        for jj, qj in zip(self.J, self.q):
            a = mp.mpf(int(jj)) / N; Sre = mp.mpf(0); Sim = mp.mpf(0)
            for xb in x:
                th = twopi * a * mp.mpf(float(xb)); Sre += mp.cos(th); Sim += mp.sin(th)
            for sp, yp in zip(s, y):
                c = 2 * mp.cosh(twopi * a * mp.mpf(float(yp))); th = twopi * a * mp.mpf(float(sp)); Sre += c * mp.cos(th); Sim += c * mp.sin(th)
            tot += mp.mpf(float(qj)) * (Sre ** 2 + Sim ** 2)
        return float(2 * tot / N - (mp.mpf(self.gN0) * (n + 4 * P) - mp.mpf(float(gh0)) * N))
def embed(M, s_cl, y_cl, rng, jitter=0.0):
    N, n = M.N, M.n_on; s_cl = np.asarray(s_cl, float); s_cl = s_cl - s_cl.min() + 2.0; L = s_cl.max() - s_cl.min()
    lo, hi = s_cl.max() + 1.0, N + 2.0 - 1.0
    x = np.linspace(lo, hi, n, endpoint=False) + 0.5 * (hi - lo) / max(n, 1) if n > 0 else np.zeros(0)
    if jitter: x = x + rng.normal(0, jitter, n)
    return np.concatenate([x, s_cl, np.clip(y_cl, 0.8, 3.0)])
def seeds(P, rng):
    out = []
    t = np.arange(P) / max(P - 1, 1)
    for Pz in (6, 8, 12, 16, 24, 32):
        try:
            c = json.load(open('e23_arch_%d.json' % Pz)); ss = np.sort(np.array(c['s'])); yy = np.array(c['y'])[np.argsort(c['s'])]
            if Pz == P: out.append(('arch-e23', ss, yy))
        except FileNotFoundError: pass
    for a in (0.6, 0.76, 0.9, 0.95, 0.99, 1.0):
        out.append(('chain a=%.2f' % a, a * np.arange(P), 0.8 + 0.7 * np.sin(np.pi * t) ** 0.8 if P > 1 else np.full(P, 0.8)))
        out.append(('chain flat a=%.2f' % a, a * np.arange(P), np.full(P, 0.8)))
    if P in (16, 32):
        c = json.load(open('e9_cfg_%d.json' % P)); out.append(('e9 stacks', np.array(c['s']), np.array(c['y'])))
    if P >= 4:
        k = (P - 2) // 2; blk = 0.6 * np.arange(k); ss = np.concatenate([blk, blk + 0.6 * k + 3.0, [0.6 * k + 1.5], [2 * (0.6 * k) + 4.5]])[:P]
        yy = np.concatenate([np.full(2 * k, 0.8), [2.0, 3.0]])[:P]; out.append(('gap', ss, yy))
    for _ in range(3):
        out.append(('random', np.sort(rng.uniform(0, rng.uniform(0.5, 2.0) * P, P)), rng.uniform(0.8, 2.0, P)))
    return out
if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 38)
    best_all = []; cands = []
    for N in (64, 128, 256):
        for P in (2, 4, 8, 16, 32):
            if 2 * P > N: continue
            M = Model(N, P); n = M.n_on; t0 = time.time(); best = (np.inf, None, None)
            for (fam, s_cl, y_cl) in seeds(P, rng):
                for jit in (0.0, 0.05):
                    z0 = embed(M, s_cl, y_cl, rng, jit)
                    bnds = [(None, None)] * (n + P) + [(0.8, 3.0)] * P
                    try:
                        r = minimize(M.LP, z0, jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 4000})
                    except (FloatingPointError, ValueError):
                        continue
                    v = M.LP(r.x, False)
                    if v < best[0]: best = (v, r.x.copy(), fam)
                    if v < 1.0: cands.append((N, P, fam, v, r.x.copy()))
            v, z, fam = best; s = z[n:n + P]; y = z[n + P:]
            print('N=%3d P=%2d: min LP %+11.4f (per pair %+.4f) from seed [%s] | pair depths %.2f-%.2f | pair span %.2f | %.0fs'
                  % (N, P, v, v / P, fam, y.min(), y.max(), s.max() - s.min(), time.time() - t0), flush=True)
            best_all.append({'N': N, 'P': P, 'LP': v, 'fam': fam, 'z': z.tolist()})
            json.dump(best_all, open('e38_best.json', 'w'))
    print('candidates with LP < 1 (double):', len(cands), flush=True)
    conf = []
    for (N, P, fam, v, z) in sorted(cands, key=lambda c: c[3])[:12]:
        M = Model(N, P); vm = M.LP_mp(z)
        print('  mp50 re-evaluation N=%d P=%d [%s]: double %+.6f, mpmath %+.6f' % (N, P, fam, v, vm), flush=True)
        conf.append({'N': N, 'P': P, 'fam': fam, 'double': v, 'mp50': vm, 'z': z.tolist()})
    json.dump(conf, open('e38_candidates.json', 'w'))
    neg = [c for c in conf if c['mp50'] < 0]
    print('VERDICT: %s' % ('REFUTES (confirmed LP < 0 in mpmath)' if neg else 'SUPPORTS on this search'), flush=True)
