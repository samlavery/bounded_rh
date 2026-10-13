"""Round 11 (C3, deep version): decoupling below the first certified level, priced by the hull proxy, against the hull baseline.
For each T2*-collapsed node X of a class not covered by a hull-certified ancestor, a DP over the sizer subtree of X:
    cost(v) = 1                                  if the hull test certifies v (or v is a sizer leaf the hull walk keeps),
            = min( sum cost(children), 1 + sides(v) )   otherwise,
with sides(v) the hull-proxy leaves of F_L >= theta_L, F_R >= theta_R on v's side cells, using X's (r, m_L, m_R) and v's own lo_r
(valid: side minima only grow on sub-cells; the slack s_v = m_L + m_R + b_r lo_r(v) - cN is split by m).  A count is stopped at the
point where it can no longer pay.  Bytes variant: a decoupled leaf costs 0.1 + beta_L c_L + beta_R c_R full-leaf equivalents.
usage: python3 hybrid_dp.py CLASS HULLNODES.json DECODE.json NET2.json T2REC1.json [...] OUT.json"""
import os, sys, json, time, numpy as np
HFS = os.environ.get('HF', '1')            # side costs divided by HF (allowance for the proxy's cruder split rule); 'node' = full(X)/hull(X)
HF = 1.0 if HFS == 'node' else float(HFS)
CLS, HN, DEC, NET2 = sys.argv[1:5]; RECF = sys.argv[5:-1]; OUTD = sys.argv[-1]
sys.argv = ['t2star.py', '0', '/dev/null']
exec(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/t2star.py').read().split("if __name__")[0])
import subcert2 as S2
NODE = json.load(open(HN))['nodes']; base = json.load(open(HN))['total'][1]
J = json.load(open(DEC)); pp = {tuple(map(int, k.split(','))): v for k, v in J['per_pair_bits_per_leaf'].items()}
mult = J['T']['mult_bits'] / J['T']['m_leaves']; FULLB = 2 + sum(pp.values()) + mult
def beta(p0, p1):
    ps = [v for (i, j), v in pp.items() if p0 <= i and j <= p1]; return (2 + sum(ps) + mult * len(ps) / len(pp)) / FULLB
CERT = {}
for f in RECF:
    for x in json.load(open(f))['records']: CERT[x['path']] = x['cert']
LP = {}
def lp(p0, p1):
    if (p0, p1) not in LP: LP[(p0, p1)] = S2.SideHull(Side(p0, p1), XT, KT ** 2)
    return LP[(p0, p1)]
def lc(sl, cons): return {sl.side.tix.index(t): (lb / SC, ub / SC) for t, (lb, ub) in cons.items() if t in sl.side.tix}
def covered(path):
    root, p = path.split(':')
    return any((root + ':' + p[:k]) in NODE and NODE[root + ':' + p[:k]][1] for k in range(len(p) + 1))
def dump_node(path):
    ri, p = path.split(':'); nd = D['trees'][int(ri[1:])]
    for ch in p: nd = nd[4] if ch == 'X' else nd[5]
    return nd
st = {'counts': 0}
def sides(nd, r, mL, mR, budget, bytes_):
    """cost of decoupling nd at gap r (leaves or bytes), or inf if it cannot come under budget"""
    boxi = [tuple(b) for b in nd[1]]; cons = nd[2]; bx = np.array(boxi, float) / SC; lo_r = bx[r, 0]
    s = mL + mR + bN[r] * lo_r - cN
    if s < 0: return np.inf
    tot = mL + mR; tL, tR = (mL - s * mL / tot, mR - s * mR / tot) if tot > 0 else (0.0, 0.0)
    cost = 0.1 if bytes_ else 1.0
    for (p0, p1, th, m_) in ((0, r, tL, mL), (r + 1, n - 1, tR, mR)):
        if p1 == p0 or m_ <= 0: continue
        bfac = (beta(p0, p1) if bytes_ else 1.0) / HF; room = (budget - cost) / bfac
        if room < 1: return np.inf
        sl = lp(p0, p1); g = sl.side.gaps; st['counts'] += 1
        c, ok = sl.count(bx[g, 0], bx[g, 1], lc(sl, cons), th, cap=int(np.ceil(room)))
        if not ok: return np.inf
        cost += bfac * c
    return cost
def dp(nd, path, r, mL, mR, bytes_):
    h, cert = NODE.get(path, (1, True))
    if cert or nd[0] == 'leaf' or path not in NODE: return 1.0, 0
    a, na = dp(nd[4], path + 'X', r, mL, mR, bytes_); b, nb = dp(nd[5], path + 'Y', r, mL, mR, bytes_)
    keep = a + b
    d = sides(nd, r, mL, mR, keep, bytes_)
    return (d, 1) if d < keep else (keep, na + nb)
R = json.load(open(NET2)); rows = [x for x in R['rows'] if x['fin'] and not covered(x['path']) and x['path'] in NODE]
ALLH = sum(NODE[x['path']][0] for x in rows); NALL = len(rows)
NSAMP = int(os.environ.get('NSAMP', '0'))       # >0: a uniform random sample of candidates, savings scaled by hull leaves
if NSAMP and NSAMP < len(rows): rows = [rows[i] for i in sorted(np.random.default_rng(7).choice(len(rows), NSAMP, replace=False))]
SH = os.environ.get('SHARD')                      # 'k/N': candidates k, k+N, ... (merge offline: net = base - sum h + sum v)
if SH: rows = rows[int(SH.split('/')[0])::int(SH.split('/')[1])]
t0 = time.time(); res = {'leaves': [0.0, 0.0, 0], 'bytes': [0.0, 0.0, 0]}
for k, x in enumerate(rows):
    p = x['path']; c = [c_ for c_ in CERT[p] if c_[0] == x['r']][0]; r, mL, mR = c[0], c[1], c[2]; nd = dump_node(p); h = NODE[p][0]
    if HFS == 'node': HF = max(1.0, x['full'] / h)
    for mode, b in (('leaves', False), ('bytes', True)):
        v, nd_ = dp(nd, p, r, mL, mR, b); res[mode][0] += h; res[mode][1] += v; res[mode][2] += nd_
    if k % 50 == 0: print('  %d/%d (%.0fs) %s counts %d' % (k, len(rows), time.time() - t0, res, st['counts']), flush=True)
out = {'class': CLS, 'HF': HFS, 'hull_baseline': base, 'candidates': NALL, 'sampled': len(rows), 'hull_under_all_candidates': ALLH}
for mode in res:
    h, v, nd_ = res[mode]; sav = (h - v) / h * ALLH if h else 0.0
    out[mode] = {'hull_under_sample': h, 'dp_under_sample': v, 'decoupled_nodes': nd_, 'net_extrapolated': base - sav, 'cut': '%.2f%%' % (-100 * sav / base)}
print(out, '(%.0fs)' % (time.time() - t0), flush=True)
json.dump(out, open(OUTD, 'w'))
