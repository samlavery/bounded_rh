"""Round 7 analysis: per family and N, the lowest LP and the thinnest per-pair margin.  For the lowest configurations, the split
LP = s(D) + Delta_B: s(D) = E(D) - F_C^pSq (pairs replaced by on-line points of mass 2 m_i at s_i), Delta_B = E(Z) - E(D).
Also the density-1 lattice value N sigma (sigma = g^(0) - g(0)).
usage: python3 round7_analyse.py RESULTS.json [RESULTS.json ...]"""
import sys, json, numpy as np
sys.argv = ['mixed_search.py', 'none', '64', '/tmp/x'] + sys.argv[1:]
FILES = sys.argv[4:]
exec(open('mixed_search.py').read().split("for N in NS:")[0])
rows = [r for f in FILES for r in json.load(open(f))]
def split(r):
    N = r['N']; c = r['cfg']; J, q, g0, gh0 = setup(N)
    x, m_on, s, y, mi = map(np.array, (c['x'], c['m_on'], c['s'], c['y'], c['mi']))
    SD = np.exp(2j * np.pi * np.outer(J, x) / N) @ m_on + np.exp(2j * np.pi * np.outer(J, s) / N) @ (2 * mi)
    ED = 2 * float(q @ np.abs(SD) ** 2) / N
    sD = ED + gh0 * N - g0 * (float(np.sum(m_on ** 2)) + 4 * float(np.sum(mi)))
    return sD, r['LP'] - sD, N * (gh0 - g0)
print('%d runs from %s' % (len(rows), FILES))
for fam in sorted(set(r['fam'] for r in rows)):
    for N in sorted(set(r['N'] for r in rows if r['fam'] == fam)):
        rr = [r for r in rows if r['fam'] == fam and r['N'] == N]
        b = min(rr, key=lambda r: r['LP']); bp = min((r for r in rr if r['per_pair']), key=lambda r: r['per_pair'])
        sD, dB, lat = split(b)
        print('fam %s N=%3d (%3d runs): min LP %+.5f%s [%s; pairs %g, deep %d at y=%s, shallow y in %s] = s(D) %+.4f + Delta_B %+.4f  (lattice N*sigma %.4f)'
              % (fam, N, len(rr), b['LP'], (' (mp50 %+.6f)' % b['LP_mp50']) if 'LP_mp50' in b else '', b['tag'], b['pairs'], b['n_deep'],
                 ['%.3f' % v for v in b['deep_y']][:4], ['%.3f' % v for v in b['shallow_y_range']] if b['shallow_y_range'] else '-', sD, dB, lat))
        print('        thinnest per-pair %+.5f [%s; LP %+.4f, pairs %g, deep %d]' % (bp['per_pair'], bp['tag'], bp['LP'], bp['pairs'], bp['n_deep']))
neg = [r for r in rows if r['LP'] < 0 or r.get('LP_mp50', 1) < 0]
print('runs with LP < 0 (float or mp50): %d' % len(neg))
mp = [r for r in rows if 'LP_mp50' in r]
print('mp50 re-evaluations: %d; max |mp50 - float| = %.2e' % (len(mp), max(abs(r['mp_minus_float']) for r in mp) if mp else 0))
low = sorted(rows, key=lambda r: r['LP'])[:8]
print('lowest 8 overall:')
for r in low:
    sD, dB, lat = split(r)
    print('  %s N=%d %-36s LP %+.5f  s(D) %+.4f  Delta_B %+.4f  pairs %g deep %d  shallow y %s' % (r['fam'], r['N'], r['tag'], r['LP'], sD, dB, r['pairs'], r['n_deep'],
          ['%.3f' % v for v in r['shallow_y_range']] if r['shallow_y_range'] else '-'))
