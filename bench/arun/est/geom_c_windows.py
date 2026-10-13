"""Phase 1 (c): smoothed R8 windows c_j -> c_j exp(-beta j^2) (j >= 1; the sqrt(2) term untouched).  Writes window JSONs
(cnum over 1e9) and prints curvature metrics of w = (K/K0)^2 on the pair-sum ranges, plus H.  usage: python3 geom_c_windows.py"""
import json, sys, numpy as np
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import window_from_cnum, H_of
R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
c8 = np.array(R8['cnum'][1:], float) / R8['cnum'][0]
for beta in (0.0, 0.003, 0.01, 0.03, 0.1):
    cj = c8 * np.exp(-beta * np.arange(1, len(c8) + 1) ** 2)
    cnum = [10 ** 9] + [int(round(v * 1e9)) for v in cj]
    fn = '/Users/samuellavery/work/riemann-submission/bench/arun/est/win_smooth_b%g.json' % beta
    json.dump({'cnum': cnum, 'cden': 10 ** 9, 'beta': beta, 'base': 'R8 rwin8.json'}, open(fn, 'w'))
    cc = window_from_cnum(cnum); coef = np.concatenate([[1.0], cc]); om = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cc) + 1)])
    s = np.linspace(-1, 41, 420001); h = s[1] - s[0]
    K = ((np.sinc((om[None, :] - 2 * np.pi * s[:, None]) / 2 / np.pi) + np.sinc((om[None, :] + 2 * np.pi * s[:, None]) / 2 / np.pi)) / 2 * coef[None, :]).sum(1)
    K0 = float(((np.sinc(om / 2 / np.pi)) * coef).sum()); w = (K / K0) ** 2
    d2 = np.gradient(np.gradient(w, h), h)
    met = []
    for lo, hi in ((0.8, 1.2), (1.2, 2.5), (2.5, 5), (5, 10), (10, 40)):
        msk = (s >= lo) & (s < hi); met.append(float(np.abs(d2[msk]).max()))
    print('beta %-6g H %.8f | sup|w\'\'| on [0.8,1.2) %.3f [1.2,2.5) %.4f [2.5,5) %.4f [5,10) %.5f [10,40) %.5f | %s' % (beta, H_of(cc), *met, fn), flush=True)
