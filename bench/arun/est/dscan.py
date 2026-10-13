"""Separation-threshold scan for MOP's matching argument: remainder floor c(d) = min Fw over gaps >= d (W8 fixed),
pair-block feasibility min_{u <= d} wfun(u) >= c(d), and the resulting kappa = (H - B)/(1 - min(c(d), ...)).
usage: python3 dscan.py"""
import numpy as np
exec(open('fw_min.py').read().split("print('window K(0)")[0])
us = np.linspace(0, 1.4, 1401); wv = wfun(us)
print('wfun on [0, 1.4]: ' + ', '.join('%.2f:%.5f' % (u, v) for u, v in zip(us[::50], wv[::50])))
H, B = 0.67216841, 0.0040435
for d in (0.85, 0.95, 1.0, 1.02, 1.03, 1.035, 1.04, 1.05, 1.07, 1.1, 1.15, 1.2):
    f, g = fmin(d, nst=250, seed=3); wmin = float(wfun(np.linspace(0, d, 2001)).min())
    ok = wmin >= f
    print('d = %.3f: c(d) = %.8f at %s | min_{u<=d} wfun = %.6f -> pair blocks %s | kappa %.8f (gain %+.2e)' % (d, f, np.round(g, 3), wmin, 'OK' if ok else 'FAIL', (H - B) / (1 - f), (H - B) / (1 - f) - 0.6735478))
