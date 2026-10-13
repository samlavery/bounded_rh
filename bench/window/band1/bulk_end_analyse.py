"""Round 1 (1) analysis: best certified bound per geometry (over the 3 parameter sets), m_bulk at the centre and mean spacings (same t_L),
deficit D = LB - P m_bulk(a_c), near-part deficit D_near = (LB - tails) - P m_bulk(a_c), grading length l (fit of the edge spacing profile
a_c - spacing_k ~ b exp(-k / l) on the outer half)."""
import re, json, sys, numpy as np
sys.argv = ['bulk_end.py', 'none']
exec(open('bulk_end.py').read().split("if STAGE == 'mbulk':")[0])
G = {}
for f in ('bulk_end_relaxed.json', 'bulk_end_uniform.json'):
    for g in json.load(open(f)): G[(g['name'], round(g['Y'], 3))] = g
best = {}
for l in open('bulk_end_dp.log'):
    m = re.match(r'\[XR=(\S+) tlow=(\S+)\] (\S+)\s+N=\s*\d+\s+Y=([\d.]+).*joint lower bound ([+-][\d.]+).*tails ([+-][\d.]+)', l)
    if not m: continue
    xr, tl, name, Y, lb, tails = m.group(1), float(m.group(2)), m.group(3), round(float(m.group(4)), 3), float(m.group(5)), float(m.group(6))
    k = (name, Y)
    if k not in best or lb > best[k][0]: best[k] = (lb, tails, tl, xr)
rows = []
for (name, Y), (lb, tails, tl, xr) in sorted(best.items(), key=lambda t: (t[0][0][0], t[0][1], len(G[t[0]]['pairs']))):
    g = G[(name, Y)]; s = np.sort(np.array(g['pairs'])); P = len(s); sp = np.diff(s)
    ac = float(sp[len(sp) // 2]); am = float(np.mean(sp))
    mc = m_bulk(ac, 0.5, tl)[0]; mm = m_bulk(am, 0.5, tl)[0]
    half = sp[: max(3, len(sp) // 2)]; dlt = ac - half; ok = dlt > 1e-4
    ell = float('nan')
    if ok.sum() >= 3:
        kk = np.arange(len(half))[ok]; slope = np.polyfit(kk, np.log(dlt[ok]), 1)[0]; ell = -1 / slope if slope < 0 else float('inf')
    D = lb - P * mc; Dn = (lb - tails) - P * mc
    rows.append((name, Y, P, lb, tails, ac, am, mc, D, Dn, ell, tl, xr))
    print('%-9s Y=%.1f P=%3d: LB %+.4f (tails %+.4f; XR %s t_L %.3f) | a_c %.4f a_mean %.4f m_bulk(a_c) %.4f | D = LB - P m %+.3f | D_near %+.3f | grading l %.2f'
          % (name, Y, P, lb, tails, xr, tl, ac, am, mc, D, Dn, ell))
