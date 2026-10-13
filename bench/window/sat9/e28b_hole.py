"""E28b: the hole seeds for the combined bound (min gap 1-1.25, density 0.8-1), primary and diagnostic c, at the seed and after a
local adversary on each.  Completes the e28 pre-registration's seed list."""
import numpy as np, sys
src = open('e28_combined.py').read().split("if __name__ == '__main__':")[0]
exec(src)
rng = np.random.default_rng(23)
for P in (3, 4, 8, 16, 32):
    for a in (1.0, 1.1, 1.25):
        s = a * np.arange(P) + rng.normal(0, 0.02, P); t = np.arange(P) / max(P - 1, 1)
        for yprof in ('flat', 'arch'):
            y = np.full(P, 0.85) if yprof == 'flat' else 0.8 + 0.6 * np.sin(np.pi * t) ** 0.8
            r0 = report('hole a=%.2f %s seed' % (a, yprof), s, y)
            for mode in ('primary', 'diag'):
                SEARCH_MODE = mode
                b = search(P, [(s.copy(), y.copy())])
                ss, yy = b[1][:P], b[1][P:]
                L1, L2 = report('   -> local adversary (%s)' % mode, ss, yy)
                print('      min gap after: %.3f  verdict(%s): %s' % (np.diff(np.sort(ss)).min(), mode,
                      'PASS' if (L1 if mode == 'primary' else L2) >= 0 else 'FAIL'), flush=True)
