"""Round 11 (1): ideal box-restricted long-gap decoupling T2* on bridge-port's t570 split tree (read-only dump).
At a node and gap r: m_L = min of the left sub-frame functional (points 0..r) over the node's box restricted to gaps 0..r-1 and the node's
constraints on pairs inside the left side; m_R likewise for points r+1..8.  Cross pairs and cross constraints dropped (cross pairs >= 0).
Certified if m_L + m_R + b_r lo_r >= cN/SA.  Collapse top-down.
Side minimiser (an estimate, not a bound): basin-word seeds (integer gaps, so every pair distance sits near a zero of w) + box corners +
random feasible samples; batched projected-gradient descent on a table of K, K'; exact SLSQP polish of the best distinct points.
Inheritance: if the parent's side minimiser lies in the child's side box and constraints, the child's side minimum equals it.
Skipping r is decided only by upper bounds (values at feasible points), never by the estimate.
usage: python3 t2star.py ROOTS(comma list or all) OUT.json"""
import sys, json, pickle, time, numpy as np
from scipy.optimize import minimize
ROOTS = sys.argv[1]; OUT = sys.argv[2]
import os
DUMP = os.environ.get('T2DUMP', '/Users/samuellavery/work/riemann-submission/bench/arun/cert/n9/dump_full_t570.pkl')   # T2DUMP: another tree (QV)
WJ = '/Users/samuellavery/work/riemann-submission/bench/arun/cert/rwin9_t570.json'
class Cell(tuple):
    def __new__(cls, box, cons=None):
        c = tuple.__new__(cls, box); c.cons = dict(cons or {}); return c
class U(pickle.Unpickler):
    def find_class(self, mod, name):
        if name == 'Cell': return Cell
        return super().find_class(mod, name)
D = U(open(DUMP, 'rb')).load(); W = json.load(open(WJ))
n = W['n']; Q = n - 1; SA = W['SA']; SC = 2 ** 15
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]
aN = np.array([W['aN']['%d,%d' % (i, j)] for i, j in PAIRS], float) / SA; bN = np.array(W['bN'], float) / SA
cN = W['c_cert_target']['cN_over_1e8'] / SA
cw = np.array(W['cnum'], float) / W['cden']; om = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw))])
def Kd(x):
    x = np.asarray(x, float)[..., None]; u1 = (om - 2 * np.pi * x) / 2; u2 = (om + 2 * np.pi * x) / 2
    s1 = np.sinc(u1 / np.pi); s2 = np.sinc(u2 / np.pi)
    with np.errstate(divide='ignore', invalid='ignore'):
        d1 = np.where(np.abs(u1) > 1e-8, (np.cos(u1) - s1) / u1, 0.0); d2 = np.where(np.abs(u2) > 1e-8, (np.cos(u2) - s2) / u2, 0.0)
    K = ((s1 + s2) / 2 * cw).sum(-1); Kp = ((-np.pi * d1 + np.pi * d2) / 2 * cw).sum(-1)
    return K, Kp
K0 = float(Kd(0.0)[0])
XT = np.linspace(0, 300, 1500001); KT, KPT = Kd(XT); KT = KT / K0; KPT = KPT / K0          # table step 2e-4, for the batched descent only
class Side:
    def __init__(self, p0, p1):          # points p0..p1 inclusive; gaps p0..p1-1
        self.p0, self.p1 = p0, p1; self.gaps = list(range(p0, p1)); self.m = p1 - p0
        self.tix = [t for t, (i, j) in enumerate(PAIRS) if p0 <= i and j <= p1]
        self.I = np.array([PAIRS[t][0] - p0 for t in self.tix], int); self.J = np.array([PAIRS[t][1] - p0 for t in self.tix], int)
        self.a = aN[self.tix]; self.b = bN[self.gaps]
        self.Inc = np.zeros((len(self.tix), self.m))
        for q in range(len(self.tix)): self.Inc[q, self.I[q]:self.J[q]] = 1.0
    def f(self, g):                       # exact value and gradient
        p = np.concatenate([[0.0], np.cumsum(g)]); d = p[self.J] - p[self.I]; K, Kp = Kd(d); k = K / K0; kp = Kp / K0
        return float(self.b @ g + self.a @ (k * k)), self.b + (self.a * 2 * k * kp) @ self.Inc
    def fv(self, G):                      # exact values, batched
        G = np.atleast_2d(G); P = np.concatenate([np.zeros((len(G), 1)), np.cumsum(G, axis=1)], axis=1); d = P[:, self.J] - P[:, self.I]
        k = Kd(d.ravel())[0].reshape(d.shape) / K0; return G @ self.b + (k * k) @ self.a
    def fgt(self, G):                     # tabled values and gradients, batched
        P = np.concatenate([np.zeros((len(G), 1)), np.cumsum(G, axis=1)], axis=1); d = (P[:, self.J] - P[:, self.I]).ravel()
        k = np.interp(d, XT, KT).reshape(len(G), -1); kp = np.interp(d, XT, KPT).reshape(len(G), -1)
        return G @ self.b + (k * k) @ self.a, self.b + (self.a * 2 * k * kp) @ self.Inc
    def cons_of(self, cons):
        return [(PAIRS[t][0] - self.p0, PAIRS[t][1] - self.p0, lb / SC, ub / SC) for t, (lb, ub) in cons.items() if t in self.tix]
SIDES = {r: (Side(0, r), Side(r + 1, n - 1)) for r in range(Q)}
def feas(G, cl, tol=1e-9):
    ok = np.ones(len(G), bool)
    for i, j, lb, ub in cl:
        s = G[:, i:j].sum(1); ok &= (s >= lb - tol) & (s <= ub + tol)
    return ok
def viol(G, cl):
    v = np.zeros(len(G)); gv = np.zeros_like(G)
    for i, j, lb, ub in cl:
        s = G[:, i:j].sum(1); e = np.maximum(0, lb - s) - np.maximum(0, s - ub); v += e * e; gv[:, i:j] -= 2 * e[:, None]
    return v, gv
rng = np.random.default_rng(11)
SEEDV = np.array([1.04, 1.97, 2.93] + list(range(4, 300)), float)          # word alphabet of the multi-point basins, then integers
NKEEP, NDESC, NPOL, MU, NPER = 3000, 150, 12, 10.0, 4
MEMO = {}; SSTAT = {'calls': 0, 'memo': 0, 'inherit': 0, 'solve': 0}
def descend(side, X, lo, hi, cl, iters=NDESC):
    f, g = side.fgt(X); v, gv = viol(X, cl); f = f + MU * v; g = g + MU * gv; st = np.full(len(X), 0.3)
    for _ in range(iters):
        Xn = np.clip(X - st[:, None] * g, lo, hi); fn, gn = side.fgt(Xn); vn, gvn = viol(Xn, cl); fn = fn + MU * vn; gn = gn + MU * gvn
        acc = fn <= f - 1e-4 * np.sum(g * (X - Xn), 1)
        X[acc], f[acc], g[acc] = Xn[acc], fn[acc], gn[acc]; st[acc] *= 1.6; st[~acc] *= 0.25
    return X, f
def polish(side, x0, lo, hi, cl):
    C = []
    for i, j, lb, ub in cl:
        v = np.zeros(side.m); v[i:j] = 1.0
        C.append({'type': 'ineq', 'fun': (lambda g, v=v, lb=lb: v @ g - lb), 'jac': (lambda g, v=v: v)})
        C.append({'type': 'ineq', 'fun': (lambda g, v=v, ub=ub: ub - v @ g), 'jac': (lambda g, v=v: -v)})
    r = minimize(side.f, x0, jac=True, method='SLSQP', bounds=list(zip(lo, hi)), constraints=C, options={'maxiter': 300, 'ftol': 1e-15})
    x = np.clip(r.x, lo, hi)
    return (float(side.f(x)[0]), x) if feas(x[None, :], cl, 1e-7)[0] else (np.inf, x)
def side_min(side, lo, hi, cl, key, hints=()):
    """returns (estimated minimum, list of (value, x) local minima found).  hints: the parent's local minima for this side."""
    if side.m == 0: return 0.0, [(0.0, np.zeros(0))]
    SSTAT['calls'] += 1
    if key in MEMO: SSTAT['memo'] += 1; return MEMO[key]
    inside = [(v, x) for v, x in hints if np.all(x >= lo - 1e-12) and np.all(x <= hi + 1e-12) and feas(x[None, :], cl, 1e-7)[0]]
    if hints and inside and inside[0][1] is hints[0][1]:      # the parent's best point lies in the child: equal minima
        SSTAT['inherit'] += 1; MEMO[key] = (hints[0][0], inside); return MEMO[key]
    SSTAT['solve'] += 1
    R = lo + (hi - lo) * rng.random((400, side.m)); okR = feas(R, cl); U = float(side.fv(R[okR]).min()) if okR.any() else np.inf
    if inside: U = min(U, inside[0][0])
    base = float(side.b @ lo); cands = []
    for s in range(side.m):
        top = min(hi[s], lo[s] + (U - base) / side.b[s]) if np.isfinite(U) else hi[s]
        cands.append(np.unique(np.array([lo[s], top] + [v for v in SEEDV if lo[s] < v < top][:NPER])))
    tot = int(np.prod([len(c) for c in cands]))
    mesh = (np.stack(np.meshgrid(*cands, indexing='ij'), -1).reshape(-1, side.m) if tot <= 300000 else
            np.stack([c[rng.integers(0, len(c), 300000)] for c in cands], -1))
    if len(mesh) > NKEEP:
        sv, _ = side.fgt(mesh); sv = sv + MU * viol(mesh, cl)[0]; o = np.argsort(sv)
        mesh = np.vstack([mesh[o[:NKEEP - 500]], mesh[rng.choice(o[NKEEP - 500:], 500, replace=False)]])
    X = np.vstack([mesh, R[okR][:200]] + ([np.array([x for _, x in inside])] if inside else []))
    X, fX = descend(side, X.copy(), lo, hi, cl)
    o = np.argsort(fX); picks = []
    for q in o:
        if all(np.max(np.abs(X[q] - X[p])) > 1e-3 for p in picks): picks.append(q)
        if len(picks) >= NPOL: break
    mins = [polish(side, X[q], lo, hi, cl) for q in picks] + inside
    if okR.any(): q = np.argmin(side.fv(R[okR])); mins.append((float(side.fv(R[okR][q:q + 1])[0]), R[okR][q]))
    mins = sorted([m for m in mins if np.isfinite(m[0])], key=lambda t: t[0])[:20]
    MEMO[key] = (mins[0][0] if mins else np.inf, mins); return MEMO[key]
def side_key(side, boxi, cons):
    return (side.p0, side.p1, tuple(boxi[g] for g in side.gaps), tuple(sorted((t, tuple(v)) for t, v in cons.items() if t in side.tix)))
T0 = time.time()
GA = np.array(json.load(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/geom_a_t570.json'))['leaf_eps']) * W['eps_strong'] + W['eps_strong']   # per-leaf found minima (phase 1)
if len(GA) != len(D['leaves']): GA = np.full(len(D['leaves']), np.inf)          # another tree: no phase-1 minima, guard off
stats = {'nodes': 0, 'r_tried': 0, 'cert': 0, 'geom_violations': 0}
records = []
ORDER = [3, 4, 2, 5, 1, 6, 0, 7]; STOP = {3, 4}          # balanced gaps first; descend until a gap in STOP certifies
def node_cert(box, cons, boxi, hints, need):
    """all certifying gaps r at this node, as (r, mL, mR); stops early once a gap in STOP certifies."""
    lo, hi = box[:, 0], box[:, 1]; newh = {}; out = []
    G = lo + (hi - lo) * rng.random((300, Q)); fullcl = [(PAIRS[t][0], PAIRS[t][1], lb / SC, ub / SC) for t, (lb, ub) in cons.items()]
    G = G[feas(G, fullcl)]
    def ub(side, f_samples):                    # an upper bound on the side minimum: best feasible sample or inherited point
        u = float(np.min(f_samples)) if len(f_samples) else np.inf
        lo_, hi_ = lo[side.gaps], hi[side.gaps]; cl_ = None
        for v, x in hints.get((side.p0, side.p1), ()):
            if np.all(x >= lo_ - 1e-12) and np.all(x <= hi_ + 1e-12):
                if cl_ is None: cl_ = side.cons_of(cons)
                if feas(x[None, :], cl_, 1e-9)[0]: u = min(u, v); break
        return u if side.m else 0.0
    for r in [q for q in ORDER if q in need]:
        L, R = SIDES[r]
        uL = ub(L, L.fv(G[:, L.gaps]) if (L.m and len(G)) else []); uR = ub(R, R.fv(G[:, R.gaps]) if (R.m and len(G)) else [])
        if uL + uR + bN[r] * lo[r] < cN: continue        # upper bounds already fail: r cannot certify
        stats['r_tried'] += 1
        mL, hl = side_min(L, lo[L.gaps], hi[L.gaps], L.cons_of(cons), side_key(L, boxi, cons), hints.get((L.p0, L.p1), ()))
        newh[(L.p0, L.p1)] = hl
        if mL + uR + bN[r] * lo[r] < cN: continue
        mR, hr = side_min(R, lo[R.gaps], hi[R.gaps], R.cons_of(cons), side_key(R, boxi, cons), hints.get((R.p0, R.p1), ()))
        newh[(R.p0, R.p1)] = hr
        if mL + mR + bN[r] * lo[r] >= cN:
            out.append((r, mL, mR))
            if r in STOP: break
    return out, newh
def sub_leaves(nd):
    return 1 if nd[0] == 'leaf' else sub_leaves(nd[4]) + sub_leaves(nd[5])
def walk(nd, off, hints, path, need=frozenset(range(Q)), inh=()):
    """visits nodes top-down until a gap in STOP certifies; records every visited node with its certifying gaps."""
    stats['nodes'] += 1
    box = np.array(nd[1], float) / SC; cons = nd[2]; nl = sub_leaves(nd); boxi = [tuple(b) for b in nd[1]]
    cl, newh = node_cert(box, cons, boxi, hints, need); gmin = float(GA[off:off + nl].min())
    if stats['nodes'] % 50 == 0: print('   node %d path %s certs %s (%.0fs)' % (stats['nodes'], path, [c[0] for c in cl], time.time() - T0), flush=True)
    for r, mL, mR in cl:
        if mL + mR + bN[r] * box[r, 0] > gmin + 1e-9: stats['geom_violations'] += 1    # a lower estimate above a found full minimum
    if cl: stats['cert'] += 1
    records.append({'path': path, 'leaf': nd[0] == 'leaf', 'cert': [(r, mL, mR, float(bN[r] * box[r, 0])) for r, mL, mR in cl], 'inh': [c[0] for c in inh],
                    'box': [list(b) for b in nd[1]], 'cons': {str(k): list(v) for k, v in cons.items()}, 'sub_leaves': nl, 'geom_min': gmin})
    if nd[0] == 'leaf' or any(r in STOP for r, _, _ in cl): return
    h = dict(hints); h.update(newh)
    got = {r for r, *_ in cl}                          # below, only the classes not yet collapsed need gaps evaluated
    need2 = set(need) & (STOP if got & {2, 3, 4, 5} else {2, 3, 4, 5} if got else set(range(Q)))
    need2 = frozenset(need2 - got); inh2 = tuple(inh) + tuple(cl)      # certified gaps stay certified below (monotone)
    walk(nd[4], off, h, path + 'X', need2, inh2); walk(nd[5], off + sub_leaves(nd[4]), h, path + 'Y', need2, inh2)
def collapse(recs, C):
    """top-down leaf count when only gaps in C may certify (from the visited-node records of one root)"""
    by = {x['path']: x for x in recs}
    def go(p):
        x = by[p]
        if any(r in C for r, *_ in x['cert']) or x['leaf']: return 1
        if p + 'X' not in by: return x['sub_leaves']           # not visited below (a STOP gap certified above): cannot happen for C within ORDER
        return go(p + 'X') + go(p + 'Y')
    return go(min(by, key=len))
if __name__ == '__main__':
    roots = list(range(len(D['trees']))) if ROOTS == 'all' else [int(x) for x in ROOTS.split(',')]
    OFF = np.concatenate([[0], np.cumsum([sub_leaves(t) for t in D['trees']])])
    t0 = time.time(); per = {}
    for ri in roots:
        k0 = len(records); base = sub_leaves(D['trees'][ri]); walk(D['trees'][ri], int(OFF[ri]), {}, 'R%d:' % ri); rec = records[k0:]
        per[ri] = {'base': base, 'all': collapse(rec, set(range(Q))), 'r2to5': collapse(rec, {2, 3, 4, 5}), 'r34': collapse(rec, {3, 4})}
        print('root %2d: %5d -> all-r %5d | r2-5 %5d | r3,4 %5d leaves (%.0fs; %s; %s)' % (ri, base, per[ri]['all'], per[ri]['r2to5'], per[ri]['r34'],
              time.time() - t0, stats, SSTAT), flush=True)
        json.dump({'per_root': per, 'records': records, 'stats': stats, 'sstat': SSTAT}, open(OUT, 'w'))
