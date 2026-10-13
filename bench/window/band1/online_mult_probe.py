"""Round 8 follow-up: an on-line zero of multiplicity M at the centre of an arched chain inside a shallow block (pSq: weight M^2).
Start: the top N = 256 ratio configuration (rb64 + collapsed stack m = 3 -> on-line multiplicity 6), then M in {4, 6, 8, 10, 12}
(environment singles removed or added far from the block to conserve mass).  Two objectives from each start:
minimise LP (mixed_search.relax) and maximise R (ratio_search.negR).  Every run with LP < 1 or R > 0.9 is re-evaluated in mpmath (50 digits).
usage: python3 online_mult_probe.py M[,M..] OUT_PREFIX"""
import sys, json, numpy as np
MS = [int(v) for v in sys.argv[1].split(',')]; OUTP = sys.argv[2]; N = 256
sys.argv = ['ratio_search.py', 'none', '256', '/tmp/x']
exec(open('ratio_search.py').read().split("RES = []")[0])
src = max(json.load(open('round8_rs_256.json')), key=lambda r: r['R']); c = src['cfg']
x, m_on, s, y, mi = map(np.array, (c['x'], c['m_on'], c['s'], c['y'], c['mi'])); ks = int(np.argmax(mi)); keep = np.arange(len(s)) != ks
sc, s1, y1, mi1 = float(s[ks]), s[keep], y[keep], mi[keep]
def evaluate(x, m_on, s, y, mi):
    sv, dB = parts(np.concatenate([x, s, y]), len(x), m_on, mi, N, grad=False); return sv, dB
out = []
for M in MS:
    extra = M - 6                                                   # on-line point of mass M replaces the stack's mass 6
    xe = x.copy(); me = m_on.copy()
    if extra > 0:                                                   # remove 'extra' environment singles farthest from the block centre
        far = np.argsort(-np.abs(((xe - sc) + N / 2) % N - N / 2))[:extra]; xe = np.delete(xe, far); me = np.delete(me, far)
    elif extra < 0:                                                 # add singles far away
        xe = np.concatenate([xe, sc + N / 2 + np.arange(-extra) - (-extra) / 2]); me = np.concatenate([me, np.ones(-extra)])
    x0 = np.concatenate([xe, [sc]]); m0 = np.concatenate([me, [float(M)]])
    assert abs(m0.sum() + 2 * mi1.sum() - N) < 1e-9
    sv, dB = evaluate(x0, m0, s1, y1, mi1)
    row = {'M': M, 'start': {'R': -dB / sv, 'LP': sv + dB, 's': sv, 'dB': dB}}
    print('M=%2d start: R %.4f LP %+.4f (s %.4f dB %+.4f)' % (M, -dB / sv, sv + dB, sv, dB), flush=True)
    # (i) minimise LP, all positions and depths free (pairs y in [1e-3, 3])
    K = len(s1); LPv, xr, sr, yr, rr = relax(x0, m0, s1, y1, mi1, np.full(K, 1e-3), np.full(K, 3.0), N, maxiter=40000)
    sv, dB = evaluate(xr, m0, sr, yr, mi1); row['minLP'] = {'LP': float(LPv), 'R': -dB / sv, 's': sv, 'dB': dB, 'nit': int(rr.nit), 'y_range': [float(yr.min()), float(yr.max())],
                                                          'cfg': {'x': xr.tolist(), 'm_on': m0.tolist(), 's': sr.tolist(), 'y': yr.tolist(), 'mi': mi1.tolist()}}
    if LPv < 1 or -dB / sv > 0.9:
        row['minLP']['LP_mp50'] = float(lp_mp(xr, m0, sr, yr, mi1, N))
    print('M=%2d min LP: LP %+.5f (R %.4f, s %.4f, dB %+.4f) pair y %.3f-%.3f%s [nit %d]' % (M, LPv, -dB / sv, sv, dB, yr.min(), yr.max(),
          (' | mp50 LP %+.8f' % row['minLP']['LP_mp50']) if 'LP_mp50' in row['minLP'] else '', rr.nit), flush=True)
    out.append(row)
json.dump(out, open(OUTP + '.json', 'w'))
