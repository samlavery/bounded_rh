"""Round 11 (2), driver v2: price the T2* collapses with ONE proxy on both sides of the comparison (calibration-free ratio).
For each first-certified node X of a gap class C (gap r = the certifying gap of largest slack):
    full(X)  = proxy leaves certifying the 9-point functional >= cN on X's cell,
    sides(X) = proxy leaves certifying F_L >= theta_L and F_R >= theta_R on X's side cells (slack split by m, pre-registered),
proxy = subcert2.SideHull (LP with the valid convex minorant of w on each pair range, the sizer's SPLIT=err rule).
Net in sizer leaves:  pooled   top + sum_X sizer(X) * sum_X sides_dedup / sum_X full(X)
                      per-node top + sum_X sizer(X) * min(1, (1/sizer + sides(X)/full(X)))    (collapse only where it pays)
usage: python3 subcert_net2.py CLASS(r34|r2to5|all) OUT.json REC1.json [REC2.json ...]"""
import sys, json, time, numpy as np
CLS, OUTN, RECS = sys.argv[1], sys.argv[2], sys.argv[3:]
sys.argv = ['t2star.py', '0', '/dev/null']
exec(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/t2star.py').read().split("if __name__")[0])
import subcert2 as S2
C = {'r34': {3, 4}, 'r2to5': {2, 3, 4, 5}, 'all': set(range(Q))}[CLS]
LP = {}
def lp(p0, p1):
    if (p0, p1) not in LP: LP[(p0, p1)] = S2.SideHull(Side(p0, p1), XT, KT ** 2)
    return LP[(p0, p1)]
def lc(sl, cons): return {sl.side.tix.index(t): (lb / SC, ub / SC) for t, (lb, ub) in cons.items() if t in sl.side.tix}
CAP = 20000
recs = []
for f in RECS: recs += json.load(open(f))['records']
by = {x['path']: x for x in recs}
def dump_node(path):
    ri, p = path.split(':'); nd = D['trees'][int(ri[1:])]
    for ch in p: nd = nd[4] if ch == 'X' else nd[5]
    return nd
fc = []
def go(p):
    x = by[p]; cs = [c for c in x['cert'] if c[0] in C]
    if cs: fc.append((p, max(cs, key=lambda c: c[1] + c[2] + c[3]))); return
    if x['leaf']: return
    go(p + 'X'); go(p + 'Y')
roots = sorted(p for p in by if p.endswith(':'))
for p in roots: go(p)
base = sum(by[p]['sub_leaves'] for p in roots); removed = sum(by[p]['sub_leaves'] for p, _ in fc); top = base - removed + len(fc)
print('class %s: roots %d, base %d, collapsed %d, removed %d, top-level %d' % (CLS, len(roots), base, len(fc), removed, top), flush=True)
SUB = {}                                               # dedup: side key -> (largest theta, proxy count at it)
def side_count(p0, p1, boxi, cons, theta):
    sl = lp(p0, p1); side = sl.side; key = side_key(side, boxi, cons)
    if key in SUB and SUB[key][0] >= theta - 1e-15: return SUB[key][1], key
    b = np.array(boxi, float) / SC
    c, ok = sl.count(b[side.gaps, 0], b[side.gaps, 1], lc(sl, cons), theta, cap=CAP); c = c if ok else np.inf
    if key not in SUB or SUB[key][0] < theta: SUB[key] = (theta, c)
    return c, key
import os
SH = os.environ.get('SHARD')                     # 'k/N': price rows k, k+N, ... only (merge offline; summary lines then cover the shard)
work = fc if not SH else fc[int(SH.split('/')[0])::int(SH.split('/')[1])]
rows = []; t0 = time.time()
for k, (p, (r, mL, mR, blo)) in enumerate(work):
    nd = dump_node(p); boxi = [tuple(b) for b in nd[1]]; cons = nd[2]; bx = np.array(boxi, float) / SC
    full, ok = lp(0, n - 1).count(bx[:, 0], bx[:, 1], lc(lp(0, n - 1), cons), cN, cap=CAP); full = full if ok else np.inf
    s = mL + mR + blo - cN; tot = mL + mR
    tL, tR = (mL - s * mL / tot, mR - s * mR / tot) if tot > 0 else (0.0, 0.0)
    cL, kL = side_count(0, r, boxi, cons, tL) if (r > 0 and mL > 0) else (0, None)
    cR, kR = side_count(r + 1, n - 1, boxi, cons, tR) if (r < Q - 1 and mR > 0) else (0, None)
    rows.append({'path': p, 'r': r, 'sizer': by[p]['sub_leaves'], 'full': full, 'cL': cL, 'cR': cR, 'kL': repr(kL), 'kR': repr(kR),
                 'slack': s / cN, 'nL': r + 1, 'nR': n - r - 1})
    if k % 20 == 0: print('  %d/%d %s r=%d sizer %d full %s sides %s+%s slack %.4f (%.0fs)' % (k, len(work), p, r, by[p]['sub_leaves'], full, cL, cR, s / cN, time.time() - t0), flush=True)
for x in rows: x['fin'] = bool(np.isfinite(x['full']) and np.isfinite(x['cL']) and np.isfinite(x['cR']) and x['full'] > 0)
fin = [x for x in rows if x['fin']]
Sz = sum(x['sizer'] for x in fin); Sf = sum(x['full'] for x in fin); Ss = sum(x['cL'] + x['cR'] for x in fin)
ded = {}
for x in fin:
    for kk in ('kL', 'kR'):
        if x[kk] != 'None': ded[x[kk]] = None
Sd = sum(SUB[eval(kk)][1] for kk in ded) if ded else 0.0
inf_rows = len(rows) - len(fin); unc = sum(x['sizer'] - 1 for x in rows if not x['fin'])      # capped nodes stay uncollapsed
pooled = top + unc + (Sz * Sd / Sf if Sf else np.nan)
pern = base - removed
for x in rows:
    pern += min(x['sizer'], 1 + x['sizer'] * (x['cL'] + x['cR']) / x['full']) if x['fin'] else x['sizer']
res = {'class': CLS, 'base': base, 'collapsed': len(fc), 'removed': removed, 'top': top, 'sum_sizer': Sz, 'sum_full_proxy': Sf,
       'sum_sides_proxy': Ss, 'sum_sides_proxy_dedup': Sd, 'distinct_subs': len(ded), 'capped_nodes': inf_rows,
       'net_pooled': pooled, 'net_per_node_best': pern, 'rows': rows}
print({k: v for k, v in res.items() if k != 'rows'}, '(%.0fs)' % (time.time() - t0), flush=True)
json.dump(res, open(OUTN, 'w'), default=float)
