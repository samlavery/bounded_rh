"""Window optimisation for OUR n-point assembly (n_point_bound_w': Phi = (H - B x)/(1 - eps x), x = (m-q)/m,
q = n-1, with c(m-q) <= 1), window v(s) = cos(w0 s) + sum_{j=1..K} c_j cos(2 pi j s), c_0 = 1 (scale-free).

  python3 wopt.py scan  n  B  w0 [K|am]           LP ceiling of one window (K = 0: single cosine; 'am' = AMTOPA's
                                                  12 corrections, first 13 terms)
  python3 wopt.py opt   n  B  w0 K|am  iters      joint ascent in (w0, c_1..c_K) with the LP envelope gradient
                                                  (pair weights and pressures re-optimised at every step)
The family / kernel / H code is famq.py (Q-generic AMTOPA family, closed-form C/A matrices for any frequencies)."""
import sys, time, json, itertools
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family, H_of, AMTOPA_C

def window(w0, corr):
    K = len(corr)
    c = np.concatenate([[1.0], np.asarray(corr, float)])
    w = np.concatenate([[w0], 2 * np.pi * np.arange(1, K + 1)])
    return c, w

def best_phi(H, eps, B, n):
    q = n - 1; best = (-1.0, 0)
    for m in range(2 * n, 100000):
        if eps * (m - q) > 1: break
        x = (m - q) / m
        best = max(best, ((H - B * x) / (1 - eps * x), m))
    return best

class LPState:
    """cutting-plane LP for eps*(B) = max_{a,b} min_g F(g; a, b) with duals on the cuts."""
    def __init__(self, fam, B, seed=0):
        self.fam, self.B = fam, B
        Q = fam.Q; rng = np.random.default_rng(seed)
        lat5 = np.array(list(itertools.product((1.04, 1.97, 2.91, 3.0, 4.0), repeat=Q))) if Q <= 6 else \
            np.array(list(itertools.product((1.04, 1.97, 2.91), repeat=Q)))
        G = np.vstack([lat5, lat5 + rng.normal(0, 0.03, size=lat5.shape),
                       rng.uniform(0.0, 8.0, size=(3000, Q)), rng.uniform(0.6, 3.2, size=(3000, Q))])
        self.G = np.clip(G, 0.0, 40.0)
    def solve_lp(self):
        fam, Q, NP, B = self.fam, self.fam.Q, self.fam.NP, self.B
        Wm = fam.Wmat(self.G)
        nvar = NP + Q + 1; cost = np.zeros(nvar); cost[-1] = -1.0
        A_eq = np.zeros((Q + 1, nvar))
        for s, cols in enumerate(fam.blocks): A_eq[s, cols] = 1.0
        A_eq[Q, NP:NP + Q] = 1.0; b_eq = np.concatenate([np.full(Q, 2.0), [B]])
        A_ub = np.hstack([-Wm, -self.G, np.ones((Wm.shape[0], 1))])
        res = linprog(cost, A_ub=A_ub, b_ub=np.zeros(Wm.shape[0]), A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 2)] * NP + [(0, B)] * Q + [(None, None)], method='highs')
        if not res.success: raise RuntimeError(res.message)
        lam = -res.ineqlin.marginals          # >= 0, sum = 1
        return res.x[:NP], res.x[NP:NP + Q], float(res.x[-1]), lam
    def run(self, rounds=40, coarse=60000, tol=3e-9, prox=0.3, verbose=False):
        """cutting planes with proximal stabilisation (as famq.eps_star); keeps the best achieved (a, b), and the
        duals of the last LP for the envelope gradient."""
        fam, Q = self.fam, self.fam.Q
        rng = np.random.default_rng(17)
        lat = np.array(list(itertools.product((1.04, 1.97, 2.91), repeat=Q)))
        prev, best = None, (-1.0, None, None)
        for it in range(rounds):
            a, b, t, lam = self.solve_lp()
            G_lp, ab_lp = self.G, (a.copy(), b.copy())
            if prev is not None and prox > 0:
                a, b = (1 - prox) * a + prox * prev[0], (1 - prox) * b + prox * prev[1]
            lo, g, found = fam.global_min(a, b, coarse=coarse, keep=120, seed=it, extra_starts=lat)
            if lo > best[0]: best = (lo, a.copy(), b.copy())
            if verbose: print('   lp %2d upper %.9f lower %.9f' % (it, t, lo), flush=True)
            if t - lo < tol: break
            cuts = [x for _, x in found[:120]] + [np.clip(g + rng.normal(0, 0.02, Q), 0, 40) for _ in range(20)]
            self.G = np.vstack([self.G] + [np.asarray(cuts)]); prev = (a, b)
        self.a, self.b, self.upper, self.lower, self.lam = best[1], best[2], t, best[0], lam
        self.G_lp, self.ab_lp = G_lp, ab_lp          # the cut set and LP solution the duals belong to
        return best[0], t

def strong_floor(fam, a, b, Q):
    lat4 = np.array(list(itertools.product((1.04, 1.97, 2.91, 0.5), repeat=Q)))
    return min(fam.global_min(a, b, coarse=300000 if Q <= 6 else 150000, keep=200, seed=s, extra_starts=lat4)[0]
               for s in (1, 2))

def evaluate(n, B, w0, corr, rounds=25, verbose=False, strong=True, G0=None):
    c, w = window(w0, corr); H = H_of(c, w); fam = Family(n - 1, c, w)
    st = LPState(fam, B)
    if G0 is not None: st.G = G0.copy()           # warm start: the previous window's cut set
    lo, up = st.run(rounds=rounds, verbose=verbose)
    if strong: lo = min(lo, strong_floor(fam, st.a, st.b, n - 1))
    phi, m = best_phi(H, lo, B, n)
    return dict(H=H, eps=lo, upper=up, phi=phi, m=m, state=st, fam=fam)

def grad(n, B, w0, corr, st, h=1e-6):
    """d eps / d theta at fixed (a, b) and active cuts (envelope), and d H / d theta; theta = (w0, c_1..c_K)."""
    theta = np.concatenate([[w0], corr]); act = st.lam > 1e-10
    Gact, lam = st.G_lp[act], st.lam[act]
    a_lp, b_lp = st.ab_lp
    def eps_at(th):
        c, w = window(th[0], th[1:]); fam = Family(n - 1, c, w)
        return float(lam @ (Gact @ b_lp + fam.Wmat(Gact) @ a_lp))
    def H_at(th):
        c, w = window(th[0], th[1:]); return H_of(c, w)
    ge, gH = np.zeros_like(theta), np.zeros_like(theta)
    for i in range(len(theta)):
        e = np.zeros_like(theta); e[i] = h
        ge[i] = (eps_at(theta + e) - eps_at(theta - e)) / (2 * h)
        gH[i] = (H_at(theta + e) - H_at(theta - e)) / (2 * h)
    return ge, gH

def phi_grad(H, eps, B, n, m, ge, gH):
    x = (m - (n - 1)) / m; D = 1 - eps * x
    return gH / D + (H - B * x) * x / D ** 2 * ge

if __name__ == '__main__':
    mode, n, B, w0 = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
    spec = sys.argv[5] if len(sys.argv) > 5 else '0'
    corr = AMTOPA_C[1:13].copy() if spec == 'am' else np.zeros(int(spec))
    if mode == 'scan':
        t0 = time.time(); r = evaluate(n, B, w0, corr)
        print('SCAN n=%d B=%.5f w0=%.6f K=%d: H=%.10f eps=%.9f (LP upper %.9f) -> Phi=%.7f at m=%d (%.0fs)'
              % (n, B, w0, len(corr), r['H'], r['eps'], r['upper'], r['phi'], r['m'], time.time() - t0), flush=True)
    elif mode == 'opt':
        iters = int(sys.argv[6]); theta = np.concatenate([[w0], corr]); step = 0.02
        r = evaluate(n, B, theta[0], theta[1:], strong=False); best = (r['phi'], theta.copy())
        print('it 0: Phi=%.7f H=%.10f eps=%.9f m=%d w0=%.5f' % (r['phi'], r['H'], r['eps'], r['m'], theta[0]), flush=True)
        for it in range(1, iters + 1):
            ge, gH = grad(n, B, theta[0], theta[1:], r['state'])
            g = phi_grad(r['H'], r['eps'], B, n, r['m'], ge, gH)
            scale = np.ones_like(theta); scale[0] = 1.0           # w0 and c_j on comparable scales
            trial = theta + step * g * scale / (np.linalg.norm(g) + 1e-30)
            rt = evaluate(n, B, trial[0], trial[1:], strong=False)
            if rt['phi'] > r['phi']:
                theta, r = trial, rt; step *= 1.3
            else:
                step *= 0.5
            if r['phi'] > best[0]: best = (r['phi'], theta.copy())
            print('it %d: Phi=%.7f H=%.10f eps=%.9f m=%d w0=%.5f step=%.2e |g|=%.3e' %
                  (it, r['phi'], r['H'], r['eps'], r['m'], theta[0], step, np.linalg.norm(g)), flush=True)
            if step < 1e-5: break
        rs = evaluate(n, B, best[1][0], best[1][1:], strong=True)
        print('BEST n=%d B=%.5f: Phi=%.7f (strong eps %.9f, H %.10f, m %d) theta=%s' %
              (n, B, rs['phi'], rs['eps'], rs['H'], rs['m'], json.dumps([round(float(t), 9) for t in best[1]])), flush=True)
