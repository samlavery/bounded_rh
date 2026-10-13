"""E16: minimal form of the e15 failure.  ONE off-line zero of multiplicity m at s + i y and its reflection (one ordinate
class of total multiplicity 2m, ordSq convention of AMW.DEPInterface), environment of simple on-line points relaxed.
LP = E(Z) - F_C(D(Z)) with F_C = h^(0) N + g_N(0) sum_t M(t)^2  (distinct ordinates).  Scan m, y, N."""
import sys, numpy as np
import e15_exact_mult as X
rng = np.random.default_rng(11)
N = int(sys.argv[1]); ys = [float(v) for v in sys.argv[2].split(',')]; ms = [int(v) for v in sys.argv[3].split(',')]
for y in ys:
    for m in ms:
        X.run('single y=%.2f m=%d' % (y, m), [0.0], [y], [m], N, rng)
