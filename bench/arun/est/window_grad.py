"""(3) Does re-optimising the WINDOW move the n-point frame ceiling?  Local active-set model of rank_ceiling.py:
the envelope at d = 1/kappa* is the chord between two binding words (R8: q=5 at d=1.41 and q=2 at d=1.51 for R=7).  For a
window c, each binding word is re-minimised locally at its fixed d (SLSQP from the R8 minimiser) and the ceiling solves
H(c) = r (1 - e_chord(1/r)).  Finite-difference gradient in the 12 corrections, then a few projected ascent steps; every
accepted step is re-checked with the full rank_ceiling search (q <= QMAX words).  usage: python3 window_grad.py R STEPS [QMAX]"""
import sys, json, math, numpy as np
from scipy.optimize import minimize
R = int(sys.argv[1]); STEPS = int(sys.argv[2]); QMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6
sys.argv = ['rank_ceiling.py', 'r8', str(R), str(QMAX)]
src = open('rank_ceiling.py').read().split("print('window %s: H")[0]
exec(src)
c0 = cc.copy()
def setwin(cvec):
    global cc, H, qf, T, coef, K0
    cc = np.asarray(cvec, float); H = H_of(cc); qf = make_qf(cc); T = QFTable(qf, N=20001)
    coef = np.concatenate([[1.0], cc]); K0 = float(Kraw(0.0))
def full_ceiling(Rr):
    rng = np.random.default_rng(11); pts = []
    for q in range(1, QMAX + 1):
        for d in DG2:
            e, g = min_word(q, d, Rr, rng, starts=5); pts.append((float(d), e, q, g))
    hull = lower_hull(pts); return ceiling(hull), hull
DG2 = np.round(np.arange(1.30, 1.701, 0.01), 4)
setwin(c0); r0, hull0 = full_ceiling(R)
near = sorted([h for h in hull0], key=lambda h: abs(h[0] - 1 / r0))[:4]
lo_pt = max([h for h in hull0 if h[0] <= 1 / r0], key=lambda h: h[0]); hi_pt = min([h for h in hull0 if h[0] >= 1 / r0], key=lambda h: h[0])
print('R = %d, QMAX %d: baseline ceiling %.8f; binding words d=%.3f (q=%d) and d=%.3f (q=%d)' % (R, QMAX, r0, lo_pt[0], lo_pt[2], hi_pt[0], hi_pt[2]), flush=True)
WORDS = [(lo_pt[0], np.array(lo_pt[3], float)), (hi_pt[0], np.array(hi_pt[3], float))]
def local_e(d, g0):
    q = len(g0); L = q * d
    if q == 1: return E_R([d], R), g0
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L, 'jac': lambda g: np.ones_like(g)},)
    r = minimize(lambda g: E_R(g, R), g0, method='SLSQP', bounds=[(0, L)] * q, constraints=cons, options={'maxiter': 300, 'ftol': 1e-15})
    return float(r.fun), r.x
def local_ceiling(cvec):
    setwin(cvec); (d1, g1), (d2, g2) = WORDS
    e1, _ = local_e(d1, g1); e2, _ = local_e(d2, g2)
    def G(r):
        d = 1 / r; t = (d - d1) / (d2 - d1); return H - r * (1 - (e1 + t * (e2 - e1)))
    a, b = 0.60, 0.70
    for _ in range(80):
        m = (a + b) / 2
        if G(m) >= 0: a = m
        else: b = m
    return a
base = local_ceiling(c0); print('local model at R8: %.8f (full %.8f)' % (base, r0), flush=True)
c = c0.copy(); h = 2e-4
for step in range(STEPS):
    k0 = local_ceiling(c); grad = np.zeros(len(c))
    for j in range(len(c)):
        cp = c.copy(); cp[j] += h; cm = c.copy(); cm[j] -= h
        grad[j] = (local_ceiling(cp) - local_ceiling(cm)) / (2 * h)
    gn = np.linalg.norm(grad)
    print('step %d: local ceiling %.8f, |grad| %.4e, grad %s' % (step, k0, gn, np.round(grad, 5)), flush=True)
    if gn < 1e-9: break
    best = None
    for t in (5e-4, 1e-3, 2e-3, 4e-3, 8e-3):
        cn = c + t * grad / gn; v = local_ceiling(cn)
        if best is None or v > best[0]: best = (v, cn, t)
    if best[0] <= k0: print('  no ascent along the gradient'); break
    c = best[1]; setwin(c); rf, hf = full_ceiling(R)
    print('  step size %.1e: local %.8f -> full re-check %.8f (gain over R8 full %+.2e); H %.8f' % (best[2], best[0], rf, rf - r0, H), flush=True)
    lo_pt = max([hh for hh in hf if hh[0] <= 1 / rf], key=lambda hh: hh[0]); hi_pt = min([hh for hh in hf if hh[0] >= 1 / rf], key=lambda hh: hh[0])
    WORDS = [(lo_pt[0], np.array(lo_pt[3], float)), (hi_pt[0], np.array(hi_pt[3], float))]
json.dump({'R': R, 'c_final': c.tolist(), 'c_R8': c0.tolist()}, open('window_grad_R%d.json' % R, 'w'))
