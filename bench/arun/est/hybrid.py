"""Round 11 (C3): hybrid of the hull-LP baseline and the box-restricted decoupling, both priced by the hull proxy (subcert2.SideHull).
Baseline: the hull walk on the full functional (hull_collapse.py nodes: path -> (hull leaves below, certified here)).
At each T2*-collapsed node X of a class (subcert_net2.py rows) that no hull-certified ancestor covers: decouple iff 1 + sides(X) < hull(X).
Sharing of sub-certificates (by side key) is charged two OPTIMISTIC ways:
  greedy     nodes in decreasing hull(X); a side key costs its proxy leaves at its first use, 0 afterwards;
  amortised  each key's cost is split equally among all nodes that use it (a lower bound for any assignment).
Leaves and bytes (a sub-frame leaf priced by its pair fields, decode_bits.py; a decoupled top leaf 0.1 of a full leaf).
usage: python3 hybrid.py HULLNODES.json DECODE.json NET2_r34.json NET2_r2to5.json NET2_all.json"""
import os, sys, json, collections, numpy as np
HFS = os.environ.get('HF', '1')            # side costs divided by HF: an allowance for the proxy's cruder split rule; 'node' = full(X)/hull(X) per node
HF = 1.0 if HFS == 'node' else float(HFS)
H = json.load(open(sys.argv[1])); NODE = H['nodes']; base = H['total'][1]
J = json.load(open(sys.argv[2])); pp = {tuple(map(int, k.split(','))): v for k, v in J['per_pair_bits_per_leaf'].items()}
mult = J['T']['mult_bits'] / J['T']['m_leaves']; FULLB = 2 + sum(pp.values()) + mult
def beta(p0, p1):
    ps = [v for (i, j), v in pp.items() if p0 <= i and j <= p1]; return (2 + sum(ps) + mult * len(ps) / len(pp)) / FULLB
TOPB = 0.1
def covered(path):
    """True if a proper ancestor of path, or path itself, is hull-certified (then decoupling below cannot help)"""
    root, p = path.split(':')
    for k in range(len(p) + 1):
        q = root + ':' + p[:k]
        if q in NODE and NODE[q][1]: return True
    return False
out = {}
for f in sys.argv[3:]:
    R = json.load(open(f)); cls = R['class']; rows = [x for x in R['rows'] if x['fin']]
    cand = []
    for x in rows:
        if covered(x['path']) or x['path'] not in NODE: continue
        cand.append(x)
    use = collections.Counter()
    for x in cand:
        for k in ('kL', 'kR'):
            if x[k] != 'None': use[x[k]] += 1
    kc = {}
    for x in cand:
        for k, c in (('kL', 'cL'), ('kR', 'cR')):
            if x[k] != 'None': kc[x[k]] = max(kc.get(x[k], 0), x[c])
    def run(mode, bytes_):
        tot = base; charged = set(); nd = 0
        for x in sorted(cand, key=lambda x: -NODE[x['path']][0]):
            h = NODE[x['path']][0]; r = x['r']; bl = beta(0, r) if bytes_ else 1.0; br = beta(r + 1, 8) if bytes_ else 1.0
            cost = TOPB if bytes_ else 1.0
            hf = max(1.0, x['full'] / h) if HFS == 'node' else HF
            for k, b in (('kL', bl), ('kR', br)):
                if x[k] == 'None': continue
                if mode == 'greedy': cost += 0 if x[k] in charged else b * kc[x[k]] / hf
                else: cost += b * kc[x[k]] / use[x[k]] / hf
            if cost < h:
                tot += cost - h; nd += 1
                if mode == 'greedy': charged.update(x[k] for k in ('kL', 'kR') if x[k] != 'None')
        return tot, nd
    res = {'candidates': len(cand), 'hull_leaves_under_candidates': sum(NODE[x['path']][0] for x in cand), 'distinct_keys': len(kc),
           'shared_keys': sum(1 for k in use if use[k] > 1)}
    for mode in ('greedy', 'amortised'):
        for b in (False, True):
            t, nd = run(mode, b); res['%s_%s' % (mode, 'bytes' if b else 'leaves')] = (round(t, 1), nd, '%.1f%%' % (100 * (t / base - 1)))
    out[cls] = res; print(cls, res, flush=True)
print('hull baseline', base, 'HF', HFS)
