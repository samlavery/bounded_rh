"""Phase 1 (a) tree collapse + (b) second-order minorant proxy, on bridge-port's dump (read-only) and geom_a's per-leaf excess.
(a) A perfect far-field test at level theta certifies any subtree whose leaves all have min excess > theta; leaves after collapse.
(b) Per leaf: pair-sum ranges (box sums intersected with the explicit constraints), half-widths h_t, sup|w''| and sup|w'''| on each
    range (profile table), E1 = sum a_t sup|w''| h_t^2/2 (tangent at the centre), E2 = sum a_t sup|w'''| h_t^3/6 (second-order),
    margin m = (eps + delta) c.  Isotropic enlargement admissible: lam1 = sqrt(m/E1), lam2 = (m/E2)^(1/3); gain = lam2/lam1.
    Saved levels per leaf = floor(log2 gain) per split axis along its root path (capped by the depth on that axis);
    proxy leaf count = sum over leaves of 2^(-saved).
usage: python3 geom_ab.py DUMP.pkl WINDOW.json GEOM_A.json [DELTA]"""
import sys, json, pickle, numpy as np
DUMP, WJ, GA = sys.argv[1], sys.argv[2], sys.argv[3]; DELTA = float(sys.argv[4]) if len(sys.argv) > 4 else 5e-5
class Cell(tuple):
    def __new__(cls, box, cons=None):
        c = tuple.__new__(cls, box); c.cons = dict(cons or {}); return c
class U(pickle.Unpickler):
    def find_class(self, mod, name):
        if name == 'Cell': return Cell
        return super().find_class(mod, name)
D = U(open(DUMP, 'rb')).load(); W = json.load(open(WJ)); A = json.load(open(GA))
eps = np.array(A['leaf_eps']); n = W['n']; Q = n - 1; SA = W['SA']; SC = 2 ** 15; c = W['eps_strong']
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]
aN = np.array([W['aN']['%d,%d' % (i, j)] for i, j in PAIRS], float) / SA
prof = np.load('w_profile.npz'); s = prof['s']; d2 = np.abs(prof['d2']); d3 = np.abs(prof['d3'])
BW = 0.005; nb = int(np.ceil(s[-1] / BW)) + 1; idx = np.minimum((s / BW).astype(int), nb - 1)
M2 = np.zeros(nb); M3 = np.zeros(nb); np.maximum.at(M2, idx, d2); np.maximum.at(M3, idx, d3)
def supm(M, lo, hi):
    a = int(min(nb - 1, max(0, np.floor(lo / BW)))); b = int(min(nb - 1, max(a, np.ceil(hi / BW)))); return float(M[a:b + 1].max())
# traverse trees in collection order (X then Y), recording per-leaf axis split depths; check against D['leaves'] order
leaves_t = []
def walk(nd, depth_axes):
    if nd[0] == 'leaf': leaves_t.append((nd, tuple(depth_axes))); return
    ax = nd[3] if not isinstance(nd[3], dict) else nd[2]
    da = list(depth_axes); key = ax if isinstance(ax, int) and ax < Q else Q          # gap axis, or pair-sum split -> bucket Q
    da[key] += 1; walk(nd[4], da); walk(nd[5], da)
for t in D['trees']: walk(t, [0] * (Q + 1))
assert len(leaves_t) == len(D['leaves']) == len(eps), (len(leaves_t), len(D['leaves']), len(eps))
same = sum(1 for (nd, _), L in zip(leaves_t, D['leaves']) if tuple(nd[1]) == tuple(L[0])); print('leaf order check: %d / %d boxes match' % (same, len(eps)), flush=True)
# (a) collapse
def collapse(nd, it, theta):
    """returns (leaf count after collapse, all-leaves-far flag)"""
    if nd[0] == 'leaf':
        e = eps[next(it)]; return 1, e > theta
    l1, f1 = collapse(nd[4], it, theta); l2, f2 = collapse(nd[5], it, theta)
    if f1 and f2: return 1, True
    return l1 + l2, False
print('(a) perfect far-field test: leaves after collapsing all-far subtrees (t570 dump, %d leaves)' % len(eps), flush=True)
for th in (1e-1, 3e-2, 1e-2, 3e-3, 1e-3):
    it = iter(range(len(eps))); tot = sum(collapse(t, it, th)[0] for t in D['trees'])
    print('   theta %.0e: %6d leaves (%.1f%% of %d)' % (th, tot, 100 * tot / len(eps), len(eps)), flush=True)
# (b) second-order proxy
gains, saved, bands = [], [], []
for k, (L, (nd, da)) in enumerate(zip(D['leaves'], leaves_t)):
    box = np.array(L[0], float) / SC; cons = L[1]
    E1 = E2 = 0.0
    for t, (i, j) in enumerate(PAIRS):
        if aN[t] <= 0: continue
        lo = box[i:j, 0].sum(); hi = box[i:j, 1].sum()
        if t in cons: lo = max(lo, cons[t][0] / SC); hi = min(hi, cons[t][1] / SC)
        h = max(hi - lo, 0) / 2
        E1 += aN[t] * supm(M2, lo, hi) * h * h / 2; E2 += aN[t] * supm(M3, lo, hi) * h ** 3 / 6
    m = (max(eps[k], 0) + DELTA) * c
    lam1 = np.sqrt(m / E1) if E1 > 0 else np.inf; lam2 = (m / E2) ** (1 / 3) if E2 > 0 else np.inf
    g = lam2 / lam1 if np.isfinite(lam1) and np.isfinite(lam2) else 1.0
    gains.append(g)
    sv = int(np.floor(np.log2(max(g, 1.0))))
    saved.append(sum(min(sv, da[ax]) for ax in range(Q + 1)))
gains = np.array(gains); saved = np.array(saved)
print('(b) second-order vs tangent: per-leaf isotropic enlargement gain = lam2/lam1 (median, 10%, 90%) by excess band', flush=True)
for lo_, hi_ in ((-1, 1e-3), (1e-3, 1e-2), (1e-2, 1e-1), (1e-1, np.inf)):
    sel = (eps > lo_) & (eps <= hi_) if lo_ >= 0 else (eps <= hi_)
    if sel.any():
        print('   eps in (%s, %s]: %5d leaves, gain median %.2f [%.2f, %.2f], saved levels mean %.2f' % (lo_ if lo_ >= 0 else '-', hi_, sel.sum(), np.median(gains[sel]), np.quantile(gains[sel], 0.1), np.quantile(gains[sel], 0.9), saved[sel].mean()), flush=True)
proxy = float(np.sum(2.0 ** (-saved)))
print('   proxy leaf count with second-order minorants: %.0f (%.1f%% of %d)' % (proxy, 100 * proxy / len(eps), len(eps)), flush=True)
