"""Round 8: R as a function of the stack depth for the top N = 256 configuration (rb64 + stack m = 3 at the centre).
The stack's depth is held at y_s; everything else (positions, the other depths in [1e-3, 3]) re-maximises R.
usage: python3 ratio_stack_scan.py YS[,YS..] OUT_PREFIX"""
import sys, json, numpy as np
YS = [float(v) for v in sys.argv[1].split(',')]; OUTP = sys.argv[2]; N0 = 256
sys.argv = ['ratio_search.py', 'none', '256', '/tmp/rs_unused']
exec(open('ratio_search.py').read().split("RES = []")[0])
src = max(json.load(open('round8_rs_256.json')), key=lambda r: r['R'])
c = src['cfg']; m_on = np.array(c['m_on']); mi = np.array(c['mi']); n_on, K = len(c['x']), len(c['s'])
ks = int(np.argmax(mi)); out = []
for ys in YS:
    y = np.array(c['y']); y[ks] = ys; z = np.concatenate([c['x'], c['s'], y])
    bnds = [(None, None)] * (n_on + K) + [((ys, ys) if k == ks else (1e-3, 3.0)) for k in range(K)]
    r = minimize(lambda zz: negR(zz, n_on, m_on, mi, N0), z, jac=True, method='L-BFGS-B', bounds=bnds,
                 options={'maxiter': 40000, 'maxfun': 80000, 'ftol': 1e-15, 'gtol': 1e-10, 'maxcor': 50})
    s_, dB = parts(r.x, n_on, m_on, mi, N0, grad=False); R = -dB / s_
    yr = r.x[n_on + K:]; others = np.delete(yr, ks)
    out.append({'y_stack': ys, 'R': R, 'dB': dB, 's': s_, 'LP': s_ + dB, 'nit': int(r.nit), 'msg': str(r.message),
                'cfg': {'x': r.x[:n_on].tolist(), 'm_on': m_on.tolist(), 's': r.x[n_on:n_on + K].tolist(), 'y': yr.tolist(), 'mi': mi.tolist()}})
    print('stack m=%d at y_s = %.3f: R %+.4f (dB %+.4f, s %.4f, LP %+.4f); other depths %.3f-%.3f (%d at <= 0.002) [nit %d, %s]'
          % (int(mi[ks]), ys, R, dB, s_, s_ + dB, others.min(), others.max(), int(np.sum(others <= 0.002)), r.nit, str(r.message)[:30]), flush=True)
json.dump(out, open(OUTP + '.json', 'w'))
