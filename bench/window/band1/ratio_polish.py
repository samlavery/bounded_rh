"""Round 8 polish: re-maximise R from the top-K configurations of round8_rs_*.json with a larger iteration budget (maxiter 100000,
3 passes).  usage: python3 ratio_polish.py N K OUT_PREFIX"""
import sys, json, numpy as np
N0, KTOP, OUTP = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sys.argv = ['ratio_search.py', 'none', str(N0), '/tmp/rp_unused']
exec(open('ratio_search.py').read().split("RES = []")[0])
rows = sorted([r for r in json.load(open('round8_rs_%d.json' % N0))], key=lambda r: -r['R'])[:KTOP]
out = []
for r in rows:
    c = r['cfg']; m_on = np.array(c['m_on']); mi = np.array(c['mi']); x = np.array(c['x']); s = np.array(c['s']); y = np.array(c['y'])
    n_on, K = len(x), len(s); z = np.concatenate([x, s, y]); bnds = [(None, None)] * (n_on + K) + [(1e-3, 3.0)] * K
    best = None
    for _ in range(3):
        rr = minimize(lambda zz: negR(zz, n_on, m_on, mi, N0), z, jac=True, method='L-BFGS-B', bounds=bnds,
                      options={'maxiter': 100000, 'maxfun': 200000, 'ftol': 1e-15, 'gtol': 1e-10, 'maxcor': 50})
        if best is None or rr.fun < best.fun: best = rr
        z = best.x
    s_, dB = parts(best.x, n_on, m_on, mi, N0, grad=False); R = -dB / s_
    xr, sr, yr = best.x[:n_on], best.x[n_on:n_on + K], best.x[n_on + K:]; Tg, Tloc = tg_parts(xr, m_on, sr, mi, N0)
    row = {'reg': r['reg'], 'N': N0, 'tag': r['tag'], 'R_before': r['R'], 'R': R, 'dB': dB, 's': s_, 'LP': s_ + dB, 'Tg': Tg, 'Ph': s_ - Tg, 'Tg_loc': Tloc,
           'R_loc': -dB / Tloc, 'nit': int(best.nit), 'msg': str(best.message), 'cfg': {'x': xr.tolist(), 'm_on': m_on.tolist(), 's': sr.tolist(), 'y': yr.tolist(), 'mi': mi.tolist()}}
    if R > 0.9:
        J, q, g0, gh0 = setup(N0); pSq = float(np.sum(m_on ** 2)) + 4 * float(np.sum(mi))
        dZ = d_mp(xr, m_on, sr, yr, mi, N0, False); dD = d_mp(xr, m_on, sr, yr, mi, N0, True)
        smp = 2 * dD / N0 + GH0_MP * N0 - G0_MP * pSq; dBmp = 2 * (dZ - dD) / N0; row['R_mp50'] = float(-dBmp / smp)
    out.append(row)
    print('%-6s N=%d %-40s R %+.4f -> %+.4f (dB %+.4f s %.4f LP %+.4f; P_h %.3f T_g %.3f; R_loc %+.3f) y %.3f-%.3f [nit %d, %s]'
          % (r['reg'], N0, r['tag'], r['R'], R, dB, s_, s_ + dB, s_ - Tg, Tg, row['R_loc'], yr.min(), yr.max(), best.nit, row['msg'][:40]), flush=True)
json.dump(out, open(OUTP + '.json', 'w'))
