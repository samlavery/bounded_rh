"""Round 9: validation of the linear-weight repair pLin (w = 1 simple on-line, 2M on-line multiplicity M >= 2, 2m off-line).
  LP_lin = LP_pSq + g(0) * sum_on (M^2 - w(M))      (a constant shift for fixed multiplicities: same minimisers as LP_pSq)
  s_lin(D) = s_pSq(D) + g(0) * sum_on (M^2 - w(M)),   R_lin = -Delta_B / s_lin
Families (positions and pair depths free, y in [1e-3, 3]):
  i   one multiplicity M with P_near pairs at +-0.88k (start depth 0.4 or 1.0)
  ii  multiplicity M flanked by off-line stacks (m pairs, start depth 0.5) at +-d, plus 4 single pairs beyond
  iii K multiplicities M at spacing d with one pair between neighbours and one at each end
  iv  round-8 on-line multiplicity configurations re-scored
Every LP_lin < 1 is re-evaluated in mpmath (50 digits).  R_lin is maximised from the lowest-LP_lin configuration of each (family, M).
usage: python3 lin_search.py FAM[,FAM..] N[,N..] OUT_PREFIX"""
import sys, json, time, numpy as np
_A = list(sys.argv)
sys.argv = ['ratio_search.py', 'none', '64', '/tmp/x']
exec(open('ratio_search.py').read().split("RES = []")[0])
FAMS = _A[1].split(','); NS = [int(v) for v in _A[2].split(',')]; OUT = _A[3]
G0 = float(G0_MP)
def wlin(M): return 1.0 if M == 1 else 2.0 * M
def shift(m_on): return G0 * float(sum(M * M - wlin(M) for M in m_on))
RES = []
def run(fam, N, tag, x, m_on, s, y, mi):
    t0 = time.time(); m_on = np.asarray(m_on, float); mi = np.asarray(mi, float)
    assert abs(m_on.sum() + 2 * mi.sum() - N) < 1e-9, (m_on.sum(), mi.sum(), N)
    K = len(s)
    LP, xr, sr, yr, r = relax(np.asarray(x, float), m_on, np.asarray(s, float), np.asarray(y, float), mi, np.full(K, 1e-3), np.full(K, 3.0), N, maxiter=40000)
    sh = shift(m_on); sp, dB = parts(np.concatenate([xr, sr, yr]), len(xr), m_on, mi, N, grad=False)
    row = {'fam': fam, 'N': N, 'tag': tag, 'LP_pSq': float(LP), 'LP_lin': float(LP) + sh, 'shift': sh, 's_lin': sp + sh, 'dB': dB,
           'R_lin': -dB / (sp + sh), 'Mmax': int(m_on.max()), 'pairs': float(mi.sum()), 'y_range': [float(yr.min()), float(yr.max())], 'nit': int(r.nit),
           'cfg': {'x': xr.tolist(), 'm_on': m_on.tolist(), 's': sr.tolist(), 'y': yr.tolist(), 'mi': mi.tolist()}}
    if row['LP_lin'] < 1:
        row['LP_lin_mp50'] = float(lp_mp(xr, m_on, sr, yr, mi, N) + G0_MP * sum(int(M) ** 2 - int(wlin(M)) for M in m_on))
    RES.append(row)
    print('%-4s N=%3d %-44s LP_lin %+.4f (LP_pSq %+.4f + shift %.3f) R_lin %.4f  pairs %g y %.3f-%.3f%s [nit %d, %.0fs]'
          % (fam, N, tag, row['LP_lin'], LP, sh, row['R_lin'], mi.sum(), yr.min(), yr.max(),
             (' | mp50 %+.8f' % row['LP_lin_mp50']) if 'LP_lin_mp50' in row else '', r.nit, time.time() - t0), flush=True)
    return row
def env_fill(N, used_mass, start):
    n = int(round(N - used_mass)); return start + np.arange(n, dtype=float), np.ones(n)
for N in NS:
    if 'i' in FAMS:
        for M in (3, 4, 5, 6, 8, 10, 12, 16, 20):
            for Pn in (2, 4, 8, 16):
                for y0v in (0.4, 1.0):
                    k = np.arange(1, Pn // 2 + 1); s0 = np.concatenate([-0.88 * k[::-1], 0.88 * k]); y0 = np.full(Pn, y0v)
                    xe, me = env_fill(N, M + 2 * Pn, 0.88 * (Pn // 2) + 1.0)
                    run('i', N, 'M=%d Pnear=%d y0=%.1f' % (M, Pn, y0v), np.concatenate([[0.0], xe]), np.concatenate([[float(M)], me]), s0, y0, np.ones(Pn))
    if 'ii' in FAMS:
        for M in (3, 4, 6, 8, 12):
            for m in (2, 3, 4):
                for d in (0.5, 0.9, 1.5):
                    s0 = np.array([-d, d, -d - 0.9, d + 0.9, -d - 1.8, d + 1.8]); y0 = np.array([0.5, 0.5, 0.4, 0.4, 0.4, 0.4]); mi = np.array([m, m, 1, 1, 1, 1], float)
                    xe, me = env_fill(N, M + 2 * mi.sum(), d + 2.8)
                    run('ii', N, 'M=%d stacks m=%d at +-%.1f' % (M, m, d), np.concatenate([[0.0], xe]), np.concatenate([[float(M)], me]), s0, y0, mi)
    if 'iii' in FAMS:
        for Kc in (2, 3, 4):
            for M in (3, 4, 6, 8):
                for d in (0.8, 1.5, 3.0):
                    xm = d * np.arange(Kc); s0 = np.concatenate([xm[:-1] + d / 2, [xm[0] - 0.9, xm[-1] + 0.9]]); P = len(s0); y0 = np.full(P, 0.4)
                    xe, me = env_fill(N, Kc * M + 2 * P, xm[-1] + 2.0)
                    run('iii', N, '%d mult M=%d spacing %.1f' % (Kc, M, d), np.concatenate([xm, xe]), np.concatenate([np.full(Kc, float(M)), me]), s0, y0, np.ones(P))
    if 'iv' in FAMS:
        for f in ('round8_onmult_a.json', 'round8_onmult_b.json', 'round8_onmult_c.json'):
            for r in json.load(open(f)):
                c = r['minLP']['cfg']
                if N != 256: continue
                run('iv', N, 'round8 M=%d minLP config' % r['M'], c['x'], c['m_on'], c['s'], c['y'], c['mi'])
        for r in json.load(open('round8_onmult_small.json')):
            if r['N'] != N: continue
            c = r['cfg']; run('iv', N, 'round8 small M=%d P=%d' % (r['M'], r['P']), c['x'], c['m_on'], c['s'], c['y'], c['mi'])
# R_lin maximisation from the lowest-LP_lin configuration of each (family, M, N)
best = {}
for r in RES:
    k = (r['fam'], r['Mmax'], r['N'])
    if k not in best or r['LP_lin'] < best[k]['LP_lin']: best[k] = r
RL = []
for k, r in sorted(best.items()):
    c = r['cfg']; m_on = np.array(c['m_on']); mi = np.array(c['mi']); n_on, K = len(c['x']), len(c['s']); N = r['N']; sh = shift(m_on)
    def f(z):
        sp, dB, g_s, g_dB = parts(z, n_on, m_on, mi, N); sl = sp + sh
        return dB / sl, (g_dB * sl - dB * g_s) / sl ** 2
    z0 = np.concatenate([c['x'], c['s'], c['y']]); bnds = [(None, None)] * (n_on + K) + [(1e-3, 3.0)] * K
    rr = minimize(f, z0, jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 20000, 'maxfun': 40000, 'ftol': 1e-15, 'gtol': 1e-10, 'maxcor': 30})
    sp, dB = parts(rr.x, n_on, m_on, mi, N, grad=False); Rl = -dB / (sp + sh)
    RL.append({'fam': k[0], 'M': k[1], 'N': k[2], 'R_lin_max': Rl, 'LP_lin_at': sp + sh + dB})
    print('R_lin max  %-4s M=%2d N=%3d: %.4f (LP_lin there %+.4f)' % (k[0], k[1], k[2], Rl, sp + sh + dB), flush=True)
json.dump({'runs': RES, 'R_lin': RL}, open(OUT + '.json', 'w'))
for fam in sorted(set(r['fam'] for r in RES)):
    for M in sorted(set(r['Mmax'] for r in RES if r['fam'] == fam)):
        rr = [r for r in RES if r['fam'] == fam and r['Mmax'] == M]; b = min(rr, key=lambda r: r['LP_lin'])
        print('SUMMARY %-4s M=%2d (%3d runs): min LP_lin %+.4f [%s N=%d; LP_pSq %+.4f]%s' % (fam, M, len(rr), b['LP_lin'], b['tag'], b['N'], b['LP_pSq'],
              (' mp50 %+.8f' % b['LP_lin_mp50']) if 'LP_lin_mp50' in b else ''), flush=True)
