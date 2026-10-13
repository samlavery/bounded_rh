"""Phase 1 (a): excess geometry of the 9-point functional on bridge-port's sizer dump (read-only).
Per leaf: eps = min F/c - 1 over sample points of the leaf polytope (box + explicit pair-sum constraints): the centre, the
corners and 96 random points, kept only if they satisfy the constraints; F with the exact kernel and the window file's weights.
Also the volume distribution: uniform samples in the 16 root boxes (weighted by box volume, constraints respected).
usage: python3 geom_a.py DUMP.pkl WINDOW.json OUT_PREFIX"""
import sys, json, pickle, itertools, numpy as np
DUMP, WJ, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
class Cell(tuple):
    def __new__(cls, box, cons=None):
        c = tuple.__new__(cls, box); c.cons = dict(cons or {}); return c
    def __reduce__(self): return (Cell, (tuple(self), self.cons))
class U(pickle.Unpickler):
    def find_class(self, mod, name):
        if name == 'Cell': return Cell
        return super().find_class(mod, name)
D = U(open(DUMP, 'rb')).load()
W = json.load(open(WJ)); n = W['n']; Q = n - 1; SA = W['SA']; SC = 2 ** 15
cw = np.array(W['cnum'], float) / W['cden']; om = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw))])
def Kraw(x):
    x = np.asarray(x, float)[..., None]
    return ((np.sinc((om - 2 * np.pi * x) / 2 / np.pi) + np.sinc((om + 2 * np.pi * x) / 2 / np.pi)) / 2 * cw).sum(-1)
K0 = float(Kraw(0.0))
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]
PI = np.array([p[0] for p in PAIRS]); PJ = np.array([p[1] for p in PAIRS])
aN = np.array([W['aN']['%d,%d' % (i, j)] for i, j in PAIRS], float) / SA; bN = np.array(W['bN'], float) / SA
c = W['eps_strong']
def F(G):
    G = np.atleast_2d(G); P = np.concatenate([np.zeros((len(G), 1)), np.cumsum(G, axis=1)], axis=1)
    d = P[:, PJ] - P[:, PI]; return G @ bN + ((Kraw(d.ravel()) / K0) ** 2).reshape(d.shape) @ aN
# the dump's pair-index convention: cons keys index a pair list; reconstruct it from a cell (check by bounds consistency)
def pair_sums(G):
    P = np.concatenate([np.zeros((len(G), 1)), np.cumsum(G, axis=1)], axis=1); return P[:, PJ] - P[:, PI]
rng = np.random.default_rng(1)
leaves = D['leaves']
print('leaves %d, roots %d; window %s; c = %.12f' % (len(leaves), D['nroots'], WJ, c), flush=True)
L0 = leaves[0]; print('leaf tuple length', len(L0), 'kinds sample', [L[3] if len(L) > 3 else None for L in leaves[:5]], flush=True)
def feasible(G, cons):
    if not cons: return np.ones(len(G), bool)
    S = pair_sums(G) * SC; ok = np.ones(len(G), bool)
    for t, (lb, ub) in cons.items(): ok &= (S[:, t] >= lb - 1e-6) & (S[:, t] <= ub + 1e-6)
    return ok
from scipy.optimize import minimize
def Fg(g):
    p = np.concatenate([[0.0], np.cumsum(g)]); d = p[PJ] - p[PI]; k = Kraw(d) / K0
    h = 1e-7; kp = (Kraw(d + h) - Kraw(d - h)) / (2 * h) / K0
    val = float(bN @ g + aN @ (k * k)); grad = bN.copy(); contrib = aN * 2 * k * kp
    for q in range(len(PI)): grad[PI[q]:PJ[q]] += contrib[q]
    return val, grad
def leaf_min(box, cons):
    lo, hi = box[:, 0], box[:, 1]
    G = lo + (hi - lo) * rng.random((400, Q)); G = np.vstack([0.5 * (lo + hi), G]); ok = feasible(G, cons)
    if not ok.any(): G = G[:1]; ok = np.array([True])
    Gf = G[ok]; fv = F(Gf); order = np.argsort(fv)[:3]; best = float(fv.min())
    cl = []
    for t_, (lb, ub) in cons.items():
        i_, j_ = PAIRS[t_]
        cl.append({'type': 'ineq', 'fun': (lambda g, i_=i_, j_=j_, lb=lb: g[i_:j_].sum() - lb / SC), 'jac': (lambda g, i_=i_, j_=j_: np.r_[np.zeros(i_), np.ones(j_ - i_), np.zeros(Q - j_)])})
        cl.append({'type': 'ineq', 'fun': (lambda g, i_=i_, j_=j_, ub=ub: ub / SC - g[i_:j_].sum()), 'jac': (lambda g, i_=i_, j_=j_: -np.r_[np.zeros(i_), np.ones(j_ - i_), np.zeros(Q - j_)])})
    for k_ in order:
        r = minimize(Fg, Gf[k_], jac=True, method='SLSQP', bounds=list(zip(lo, hi)), constraints=cl, options={'maxiter': 200, 'ftol': 1e-14})
        if r.success or r.status in (8, 9):
            gg = np.clip(r.x, lo, hi)
            if feasible(gg[None, :], {t_: (lb - 1, ub + 1) for t_, (lb, ub) in cons.items()})[0]: best = min(best, float(F(gg)[0]))
    return best
res = []
for k, L in enumerate(leaves):
    box = np.array(L[0], float) / SC; cons = L[1]
    m_ = leaf_min(box, cons)
    res.append((m_ / c - 1, float(np.prod(box[:, 1] - box[:, 0])), float((box[:, 1] - box[:, 0]).max()), 0, k))
    if k % 2000 == 0: print('  leaf %d / %d' % (k, len(leaves)), flush=True)
eps = np.array([r[0] for r in res]); vol = np.array([r[1] for r in res])
bands = [(-1, 1e-3), (1e-3, 1e-2), (1e-2, 1e-1), (1e-1, np.inf)]
print('LEAF distribution by box-min relative excess:', flush=True)
for lo_, hi_ in bands:
    sel = (eps > lo_) & (eps <= hi_) if lo_ >= 0 else (eps <= hi_)
    print('   (%s, %s]: %6d leaves (%.1f%%), leaf-volume share %.2e' % (lo_ if lo_ >= 0 else '-', hi_, sel.sum(), 100 * sel.mean(), vol[sel].sum() / vol.sum()), flush=True)
# volume distribution over the root boxes (tree roots)
roots = [np.array(t[1], float) / SC for t in D['trees']]; rcons = [t[2] for t in D['trees']]
rv = np.array([np.prod(r[:, 1] - r[:, 0]) for r in roots]); NS = 200000; samples = []
for r, cs, v in zip(roots, rcons, rv):
    m_ = max(1, int(NS * v / rv.sum())); G = r[:, 0] + (r[:, 1] - r[:, 0]) * rng.random((m_, Q))
    ok = feasible(G, cs); samples.append(F(G[ok]) / c - 1)
ev = np.concatenate(samples)
print('VOLUME distribution (uniform on the 16 root polytopes, %d feasible samples):' % len(ev), flush=True)
for lo_, hi_ in bands:
    sel = (ev > lo_) & (ev <= hi_) if lo_ >= 0 else (ev <= hi_)
    print('   (%s, %s]: %.4f%% of volume' % (lo_ if lo_ >= 0 else '-', hi_, 100 * sel.mean()), flush=True)
json.dump({'leaf_eps': eps.tolist(), 'leaf_vol': vol.tolist(), 'vol_eps_quantiles': np.quantile(ev, [0, 1e-4, 1e-3, 1e-2, 0.1, 0.5]).tolist()}, open(OUT + '.json', 'w'))
