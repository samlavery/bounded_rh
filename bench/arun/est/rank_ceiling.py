"""Ceilings for re-optimised n-point frame certificates on kappa = (H - B)/(1 - c) (MOP's linear chain).
Obstruction (rank-limited Lemma 5.1): for a stationary gap measure mu with mean gap d = 1/r, any WCert with capacity <= 2 per rank
has c <= B d + E_R(mu), E_R = 2 sum_{s=1}^{R} wbar_s (R = n - 1); kappa >= r would need H >= r (1 - E_R(mu)).  So
kappa_n* <= root of H = r (1 - e_R(1/r)), e_R = lower convex envelope (mixtures) of min-over-words E_R at mean gap d.
R = inf uses the full pair energy Ef (Poisson, capscan/dual.py) and must reproduce the window's class cap.
Words: periodic, q = 1..QMAX gaps, min E_R at fixed mean gap by multi-start SLSQP on a d-grid.
usage: python3 rank_ceiling.py WINDOW(r8|r7|typh7|famcg) R[,R..] [QMAX]"""
import sys, json, math, numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import window_from_cnum, make_qf, H_of, QFTable, Ef_word, lower_hull, envelope_at
WIN = sys.argv[1]; RS = [(10 ** 9 if v == 'inf' else int(v)) for v in sys.argv[2].split(',')]; QMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 8
BW = '/Users/samuellavery/work/riemann-submission/bench/window/'
if WIN == 'famcg':
    cc = np.array(json.load(open(BW + 'capscan/fam_cg_K24.json'))['c'], float)
else:
    f = {'r8': 'rwin8.json', 'r7': 'rwin7.json', 'typh7': 'rwin_typh7.json'}.get(WIN, WIN if WIN.endswith('.json') else WIN + '.json')
    cc = window_from_cnum(json.load(open(f if f.startswith('/') else BW + f))['cnum'])
H = H_of(cc); qf = make_qf(cc); T = QFTable(qf)
coef = np.concatenate([[1.0], cc]); w = np.concatenate([[math.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cc) + 1)])
def Kraw(x):
    x = np.asarray(x, float)[..., None]
    return ((np.sinc((w - 2 * np.pi * x) / 2 / np.pi) + np.sinc((w + 2 * np.pi * x) / 2 / np.pi)) / 2 * coef).sum(-1)
K0 = float(Kraw(0.0))
def wf(x): return (Kraw(x) / K0) ** 2
def E_R(g, R):
    g = np.asarray(g, float); q = len(g)
    if R >= 10 ** 8: return Ef_word(g, T)
    reps = R // q + 2; x = np.concatenate([[0.0], np.cumsum(np.tile(g, reps))])
    i = np.arange(q)[:, None]; s = np.arange(1, R + 1)[None, :]
    return 2 * float(wf(x[i + s] - x[i]).mean(axis=0).sum())
def min_word(q, d, R, rng, starts=10):
    L = q * d
    if q == 1: return E_R([d], R), np.array([d])
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L, 'jac': lambda g: np.ones_like(g)},)
    best = (np.inf, None)
    seeds = [np.full(q, d)] + [rng.dirichlet(np.ones(q) * (0.7 if s % 2 else 2.0)) * L for s in range(starts)]
    for g0 in seeds:
        r = minimize(lambda g: E_R(g, R), g0, method='SLSQP', bounds=[(0, L)] * q, constraints=cons, options={'maxiter': 300, 'ftol': 1e-14})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    return best
def ceiling(hull, lo=0.60, hi=0.70):
    def G(r):
        e, _ = envelope_at(hull, 1 / r); return H - r * (1 - e)
    a, b = lo, hi
    if G(a) < 0 or G(b) > 0: return None
    for _ in range(80):
        m = (a + b) / 2
        if G(m) >= 0: a = m
        else: b = m
    return a
print('window %s: H = %.10f, K-terms %d' % (WIN, H, len(cc) + 1), flush=True)
DG = np.round(np.arange(1.30, 1.701, 0.01), 4)
for R in RS:
    rng = np.random.default_rng(11); pts = []
    for q in range(1, QMAX + 1):
        for d in DG:
            e, g = min_word(q, d, R, rng, starts=6 if R < 10 ** 8 else 4)
            pts.append((float(d), e, q, [round(float(v), 4) for v in g]))
    # structured long words (period-3 / period-4 blocks [a, b], [a, a, b]) as in capscan/dual_blocks.py
    for n2 in range(1, 12):
        for n3 in range(0, 3):
            for a in (1.03, 1.04):
                word = [a, 3 - a] * n2 + [a, a, 4 - 2 * a] * n3
                g = np.array(word); pts.append((float(g.mean()), E_R(g, R), len(g), 'struct'))
    hull = lower_hull(pts); r = ceiling(hull)
    e, br = envelope_at(hull, 1 / r) if r else (None, None)
    tag = 'inf' if R >= 10 ** 8 else str(R)
    print('R = %s (n = %s): ceiling kappa* = %.8f  (gap to MOP 0.6735478: %+.2e); envelope at d = 1/kappa*: e = %.6f, between d = %s'
          % (tag, 'inf' if R >= 10 ** 8 else R + 1, r, r - 0.6735478, e, br), flush=True)
    hp = [h for h in hull if abs(h[0] - 1 / r) < 0.12]
    print('   hull points near: ' + '; '.join('d=%.3f e=%.6f q=%s' % (h[0], h[1], h[2]) for h in hp[:6]), flush=True)
