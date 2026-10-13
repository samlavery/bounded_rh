"""Extension probe of crowd_dp.py beyond y0 = 0.4 (slack within [0, X]; tail beyond X by half-unit bins): certified lower
bound of LP/y^2 for ALL real D on y-intervals of width 0.025 in [0.4, 1.2], stopping where the DP's same-cell positivity
or the tail-bin condition fails."""
import sys, time, numpy as np
sys.argv = ['crowd_dp.py', '128']
import crowd_dp as C
for ylo in np.arange(0.4, 1.2, 0.025):
    yhi = ylo + 0.025; t1 = time.time()
    try:
        o = C.dp(ylo, yhi, [(2, 38 / 256)], L=C.X)
    except AssertionError as e:
        print('y in [%.3f, %.3f]: DP precondition fails (%s)' % (ylo, yhi, e), flush=True); break
    print('y in [%.3f, %.3f]: ALL D: LP/y^2 >= %+.4f  (crowding R=2 d0=0.1484: %+.4f)  free chain %s  [%.0fs]'
          % (ylo, yhi, o['S0'] + 2 * o['Vfree'], o['S0'] + o['Vfree'] + o['crowd'][(2, 38 / 256)][0], C.fmt(o['free_chain'], 5), time.time() - t1), flush=True)
