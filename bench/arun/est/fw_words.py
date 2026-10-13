"""Robust minimum of W8's Fw on gaps >= lo: starts at every word in {1.04, 1.97, 2.93}^7 plus the fw_min random starts.
usage: python3 fw_words.py LO[,LO..]"""
import sys, itertools, numpy as np
LOS = [float(v) for v in sys.argv[1].split(',')]
sys.argv = ['fw_min.py']
exec(open('fw_min.py').read().split("print('window K(0)")[0])
H, B = 0.67216841, 0.0040435
for lo in LOS:
    best = (np.inf, None)
    for word in itertools.product((1.04, 1.97, 2.93), repeat=7):
        g0 = np.maximum(np.array(word), lo)
        r = minimize(lambda g: (Fw(g), gradF(g)), g0, jac=True, method='L-BFGS-B', bounds=[(lo, 30.0)] * 7, options={'ftol': 1e-15, 'gtol': 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
    f2, g2 = fmin(lo, nst=200, seed=7)
    if f2 < best[0]: best = (f2, g2)
    print('lo = %.3f: min Fw = %.8f at gaps %s ; kappa %.8f' % (lo, best[0], np.round(best[1], 4), (H - B) / (1 - best[0])), flush=True)
