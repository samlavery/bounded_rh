"""E37b: quadrature check of the e37 refutation: recompute phi_p(y) for the worst pairs on a 4x finer alpha grid and report the
location and size of the interior dip."""
import json, numpy as np
from common import *
from common import qfun
alF = np.linspace(0.0, 1.0, 24001); waF = np.full(len(alF), alF[1]); waF[0] /= 2; waF[-1] /= 2
qF = qfun(np.minimum(alF, 0.9999999)); qF[-1] = 0.0; W2F = 2 * qF * waF
YY = np.round(np.arange(0.8, 3.0 + 1e-9, 0.001), 4)
def phi(s, t, w, p, A, W):
    g = np.cos(2 * np.pi * np.outer(A, s[p] - s)).sum(1) + np.cos(2 * np.pi * np.outer(A, s[p] - t)) @ w
    return np.array([4 * float((W * (2 * np.cosh(2 * np.pi * A * y) - 2)) @ g) for y in YY])
for a, P in ((0.8, 128), (0.6, 48)):
    if P == 128:
        d = json.load(open('e36_w_a%.2f.json' % a)); w = np.array(d['w128']); s = a * np.arange(P)
        t = np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9)
    else:
        v = json.load(open('e34_witness.json'))['a=%.2f P=%d' % (a, P)]; s = np.array(v['s']); t = np.array(v['t']); w = np.array(v['w'])
    found = 0
    for p in range(P):
        f1 = phi(s, t, w, p, al, W2); k = int(np.argmin(f1)); dip1 = min(f1[0], f1[-1]) - f1[k]
        if 0 < k < len(YY) - 1 and dip1 > 0.01:
            f4 = phi(s, t, w, p, alF, W2F); k4 = int(np.argmin(f4)); dip4 = min(f4[0], f4[-1]) - f4[k4]
            print('  a=%.2f P=%d pair %3d: 6001-grid argmin y=%.3f dip %.4f (phi=%.4g) | 24001-grid argmin y=%.3f dip %.4f (phi=%.4g)'
                  % (a, P, p, YY[k], dip1, f1[k], YY[k4], dip4, f4[k4]), flush=True)
            found += 1
            if found >= 4: break
