"""Joint window ascent for our n-point assembly with warm-started LPs and a 3-point line search along the
LP-envelope gradient.  usage: python3 wopt2.py n B iters THETA_JSON|am  -> prints the path and BEST theta."""
import sys, json, time
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate, grad, phi_grad, AMTOPA_C
n, B, iters = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
theta = np.concatenate([[np.sqrt(2.0)], AMTOPA_C[1:13]]) if sys.argv[4] == 'am' else np.array(json.loads(sys.argv[4]))
t0 = time.time()
r = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=False)
print('it 0: Phi=%.7f H=%.10f eps=%.9f m=%d (%.0fs)' % (r['phi'], r['H'], r['eps'], r['m'], time.time() - t0), flush=True)
s0 = 3e-3
for it in range(1, iters + 1):
    ge, gH = grad(n, B, theta[0], theta[1:], r['state'])
    g = phi_grad(r['H'], r['eps'], B, n, r['m'], ge, gH); d = g / (np.linalg.norm(g) + 1e-30)
    best = None
    for s in (s0, s0 / 3, s0 / 9):
        th = theta + s * d
        rt = evaluate(n, B, th[0], th[1:], rounds=20, strong=False, G0=r['state'].G)
        if best is None or rt['phi'] > best[0]['phi']: best = (rt, th, s)
    if best[0]['phi'] > r['phi'] + 2e-7:
        r, theta = best[0], best[1]; s0 = min(3 * best[2], 0.05)
    else:
        s0 /= 9
    print('it %d: Phi=%.7f H=%.10f eps=%.9f m=%d w0=%.5f s0=%.1e |g|=%.2e (%.0fs)' %
          (it, r['phi'], r['H'], r['eps'], r['m'], theta[0], s0, np.linalg.norm(g), time.time() - t0), flush=True)
    if s0 < 1e-6: break
rs = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=True)
print('BEST n=%d B=%.5f: Phi=%.7f (strong eps %.9f, H %.10f, m %d) theta=%s' %
      (n, B, rs['phi'], rs['eps'], rs['H'], rs['m'], json.dumps([round(float(t), 9) for t in theta])), flush=True)
