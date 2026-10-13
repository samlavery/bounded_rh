"""Round 11 (2): net leaves of the box-restricted decoupling.  Reads the T2* visited-node records (t2star.py) and, per class of
admissible gaps C, prices each collapsed node by proxy sub-certificates (subcert.py) on its two sides:
    theta_L = m_L - s m_L/(m_L+m_R), theta_R = m_R - s m_R/(m_L+m_R),  s = m_L + m_R + b_r lo_r - cN   (slack split by m, pre-registered)
Three accountings:
  plain   - collapse at the first certified node (as in (1)); sub-certificates priced there.
  best    - at each such node keep the original subtree when it is cheaper.
  dp      - bottom-up over the sizer subtree below each collapsed node, collapse wherever cheapest; below the first certified node the
            ancestor's (r, m_L, m_R) are reused with the node's own lo_r (valid: side minima only grow on sub-boxes).
Sub-certificates are deduplicated by (side, side box, side constraints) at the largest threshold.  The calibration factor k
(sizer leaves per proxy leaf, calib_proxy.py) converts proxy counts; the product test full-proxy/(cL+cR) needs no calibration.
usage: python3 subcert_net.py K OUT.json REC1.json [REC2.json ...]"""
import sys, json, time, numpy as np
KCAL, OUTN, RECS = float(sys.argv[1]), sys.argv[2], sys.argv[3:]
sys.argv = ['t2star.py', '0', '/dev/null']
exec(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/t2star.py').read().split("if __name__")[0])
import subcert as SCt
FULL = Side(0, n - 1); CAP = 20000
recs = []
for f in RECS: recs += json.load(open(f))['records']
by = {x['path']: x for x in recs}
def dump_node(path):
    ri, p = path.split(':'); nd = D['trees'][int(ri[1:])]
    for ch in p: nd = nd[4] if ch == 'X' else nd[5]
    return nd
PC = {}
def pcount(side, boxi, cons, theta):
    """proxy leaves certifying side >= theta on the side's part of the box (ints) and constraints; memo by key, monotone in theta"""
    key = side_key(side, boxi, cons)
    for th, c in PC.get(key, ()):
        if th >= theta - 1e-15: return c                        # a certificate at a higher threshold serves
    b = np.array(boxi, float) / SC
    c, ok = SCt.count(side, b[side.gaps, 0], b[side.gaps, 1], side.cons_of(cons), theta, cap=CAP)
    c = c if ok else np.inf
    PC.setdefault(key, []).append((theta, c)); return c
def thetas(mL, mR, blo):
    s = mL + mR + blo - cN; tot = mL + mR
    return (mL - s * mL / tot, mR - s * mR / tot) if tot > 0 else (0.0, 0.0)
def price(boxi, cons, r, mL, mR, lo_r):
    """(cost in proxy leaves of the two side sub-certificates, side keys with thresholds)"""
    L, R = SIDES[r]; tL, tR = thetas(mL, mR, bN[r] * lo_r)
    cL = pcount(L, boxi, cons, tL) if L.m and mL > 0 else 0; cR = pcount(R, boxi, cons, tR) if R.m and mR > 0 else 0
    subs = []
    if L.m and mL > 0: subs.append((side_key(L, boxi, cons), tL, L, boxi, cons))
    if R.m and mR > 0: subs.append((side_key(R, boxi, cons), tR, R, boxi, cons))
    return cL + cR, subs
def first_certified(C):
    out = []
    def go(p):
        x = by[p]
        cs = [c for c in x['cert'] if c[0] in C]
        if cs: out.append((p, cs)); return
        if x['leaf']: return
        go(p + 'X'); go(p + 'Y')
    for p in [q for q in by if q.endswith(':')]: go(p)
    return out
def dp(nd, cands):
    """cheapest cover of the sizer subtree nd: (cost in sizer-leaf units, top-level leaves, chosen sub-certificates); cands = [(r, mL, mR)]"""
    boxi = [tuple(b) for b in nd[1]]; cons = nd[2]
    best_c, best_s = np.inf, []
    for r, mL, mR in cands:
        lo_r = boxi[r][0] / SC
        if mL + mR + bN[r] * lo_r < cN: continue
        c, subs = price(boxi, cons, r, mL, mR, lo_r)
        if 1 + KCAL * c < best_c: best_c, best_s = 1 + KCAL * c, subs
    if nd[0] == 'leaf': return 1.0, 1, []                        # a collapsed leaf costs 1 + its sub-certificates >= 1
    a, ta, sa = dp(nd[4], cands); b, tb, sb = dp(nd[5], cands)
    return (a + b, ta + tb, sa + sb) if a + b <= best_c else (best_c, 1, best_s)
def dedupe(subs):
    m = {}
    for key, th, side, boxi, cons in subs:
        if key not in m or th > m[key][0]: m[key] = (th, side, boxi, cons)
    tot = 0.0
    for key, (th, side, boxi, cons) in m.items(): tot += pcount(side, boxi, cons, th)
    return tot, len(m)
res = {}; t0 = time.time()
roots = sorted({p.split(':')[0] for p in by})
base_total = sum(by[r + ':']['sub_leaves'] for r in roots)
for name, C in [('r34', {3, 4}), ('r2to5', {2, 3, 4, 5}), ('all', set(range(Q)))]:
    fc = first_certified(C); col = {p for p, _ in fc}
    removed = sum(by[p]['sub_leaves'] for p in col)
    top_plain = base_total - removed + len(col)
    plain_subs, best_extra, best_subs, dp_cost, dp_top, dp_subs, prod = [], 0.0, [], 0.0, 0, [], []
    for p, cs in fc:
        x = by[p]; nd = dump_node(p); boxi = [tuple(b) for b in nd[1]]; cons = nd[2]
        opts = [(price(boxi, cons, r, mL, mR, boxi[r][0] / SC), r) for r, mL, mR, blo in cs]
        (c, subs), r = min(opts, key=lambda o: o[0][0])
        plain_subs += subs
        if np.isfinite(c) and 1 + KCAL * c < x['sub_leaves']: best_extra += 0; best_subs += subs
        else: best_extra += x['sub_leaves'] - 1          # keep the original subtree
        dc, dt, ds = dp(nd, [(r_, mL, mR) for r_, mL, mR, blo in cs]); dp_cost += dc; dp_top += dt; dp_subs += ds
        bx = np.array(boxi, float) / SC
        fp, ok = SCt.count(FULL, bx[:, 0], bx[:, 1], FULL.cons_of(cons), cN, cap=50000)
        prod.append({'path': p, 'r': r, 'sizer': x['sub_leaves'], 'full_proxy': fp if ok else None, 'sides_proxy': c})
    pl, npl = dedupe(plain_subs); bs, nbs = dedupe(best_subs); dps, ndps = dedupe(dp_subs)
    res[name] = {'collapsed': len(col), 'removed_sizer_leaves': removed, 'top_plain': top_plain,
                 'plain_sub_proxy': pl, 'plain_net': top_plain + KCAL * pl, 'plain_distinct_subs': npl,
                 'best_net': top_plain + best_extra + KCAL * bs, 'best_distinct_subs': nbs,
                 'dp_top': base_total - removed + dp_top, 'dp_net_nodedupe': base_total - removed + dp_cost,
                 'dp_sub_proxy_dedupe': dps, 'dp_net': base_total - removed + dp_top + KCAL * dps, 'dp_distinct_subs': ndps, 'product_test': prod,
                 'r_hist': {str(r): sum(1 for p, cs in fc if any(c[0] == r for c in cs)) for r in range(Q)}}
    print(name, {k: v for k, v in res[name].items() if k != 'product_test'}, '(%.0fs)' % (time.time() - t0), flush=True)
json.dump({'K': KCAL, 'base': base_total, 'res': res}, open(OUTN, 'w'))
