"""Round 2 (2): local-density comparison.  For each relaxed block (rb16/32/64 at Y = 0.2, 0.4) take the best certified LB from the given
logs (same t_L for m_bulk), and compare with sum_p m_bulk(a_p), a_p = mean of the spacings adjacent to pair p (one spacing at the ends).
Also reports sum_p m_bulk(a_p) split into the graded edge region (a_p < a_c - 0.005) and the bulk, and a gradient measure
G = sum_p (a_{p+1} - a_p)^2 / (local spacing)^2.  usage: python3 local_density.py LOG1 [LOG2 ...]"""
import sys, re, json, numpy as np
LOGS = sys.argv[1:]
sys.argv = ['bulk_end.py', 'none']
exec(open('bulk_end.py').read().split("if STAGE == 'mbulk':")[0])
G = {(g['name'], round(g['Y'], 3)): g for g in json.load(open('bulk_end_relaxed.json'))}
best = {}
for f in LOGS:
    for l in open(f):
        m = re.search(r'(rb\d+)\s+N=\s*\d+\s+Y=([\d.]+).*tlow=([\d.]+): joint lower bound ([+-][\d.]+)', l)
        if not m: continue
        k = (m.group(1), round(float(m.group(2)), 3)); lb = float(m.group(4)); tl = float(m.group(3))
        hdr = re.match(r'\[([^\]]*)\]', l); tag = hdr.group(1) if hdr else ''
        if k not in best or lb > best[k][0]: best[k] = (lb, tl, tag)
for k in sorted(best, key=lambda t: (t[1], int(t[0][2:]))):
    lb, tl, tag = best[k]; g = G[k]; s = np.sort(np.array(g['pairs'])); P = len(s); sp = np.diff(s)
    ap = np.empty(P); ap[0], ap[-1] = sp[0], sp[-1]; ap[1:-1] = (sp[:-1] + sp[1:]) / 2
    mb = np.array([m_bulk(a, 0.5, tl)[0] for a in ap]); ac = sp[len(sp) // 2]
    edge = ap < ac - 0.005; Gr = float(np.sum(np.diff(ap) ** 2 / ap[1:] ** 2))
    print('%s Y=%.1f P=%3d: LB %+.4f [%s] | sum_p m_bulk(a_p) %.4f (edge region %d pairs: %.4f; bulk %.4f) | LB - sum %+.4f | gradient G %.4f | exact periodic LP %.3f, LP - sum %+.3f'
          % (k[0], k[1], P, lb, tag, mb.sum(), int(edge.sum()), mb[edge].sum(), mb[~edge].sum(), lb - mb.sum(), Gr, g['LP_total'], g['LP_total'] - mb.sum()))
