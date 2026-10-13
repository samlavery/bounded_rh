"""Slack sharing for the multi-pair interface (single-pair DP of crowd_dp.py with only a fraction lam of T_g, localised to
[0, L]), and the fraction of the pair's own diagonal int qf B_y^2 that the single-pair bound consumes:
  need(y) = max(0, int qf B^2 / y^2 - bound) / (int qf B^2 / y^2)   (bound = certified lower bound of LP/y^2 with the diagonal)."""
import sys, numpy as np
sys.argv = ['crowd_dp.py', '128']
import crowd_dp as C
def diag(y): return float(2 * np.sum(C.qa2 * C.wa2 * (2 * np.cosh(2 * np.pi * C.al2 * y) - 2) ** 2)) / y ** 2
yb = np.linspace(0, 0.4, 33)
for lam, L in ((1.0, None), (1.0, 8.0), (0.5, 8.0)):
    worst = np.inf; wneed = 0.0; rows = []
    for ylo, yhi in zip(yb[:-1], yb[1:]):
        try:
            o = C.dp(ylo, yhi, [], L, lam)
        except AssertionError as e:
            rows.append('[%.4f,%.4f] precondition fails (%s)' % (ylo, yhi, e)); continue
        b = o['S0'] + 2 * o['Vfree']; d = diag(yhi); worst = min(worst, b); need = max(0.0, d - b) / d; wneed = max(wneed, need)
        rows.append('[%.3f,%.3f] %+.3f need %.2f' % (ylo, yhi, b, need))
    print('lam=%.2f slack %s: ALL-D bound min %+.4f ; max fraction of own diagonal consumed %.3f' % (lam, 'full' if L is None else 'localised to %g' % L, worst, wneed), flush=True)
    for i in range(0, len(rows), 4): print('    ' + ' | '.join(rows[i:i + 4]), flush=True)
