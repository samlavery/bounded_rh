"""All-simple lower side on the sampled object: min N E_T over N = W simple zeros in [0, W] (no margin zeros: they only
add to frobSq), several starts; the structure of the minimiser (gaps near the edges vs the bulk) and the scaling in W.
usage: python3 sampled_lower.py WINDOW STARTS W1 W2 ..."""
import sys, numpy as np
WIN, ST = sys.argv[1], int(sys.argv[2]); WS = [int(v) for v in sys.argv[3:]]
sys.argv = [sys.argv[0], WIN]
exec(open('sampled.py').read().split("if __name__ == '__main__':")[0])
rng = np.random.default_rng(7)
for W in WS:
    res = []
    starts = [('lattice', np.arange(W) + 0.5), ('edge-compressed', (np.arange(W) + 0.5) * (W - 2.0) / W + 1.0)]
    starts += [('random%d' % i, np.sort(rng.uniform(0, W, W))) for i in range(ST)]
    starts += [('jitter%d' % i, np.clip(np.arange(W) + 0.5 + rng.normal(0, 0.3, W), 0, W)) for i in range(ST)]
    for name, x0 in starts:
        r = minimize(lambda z: frob(z, np.ones(W), W, grad=True), x0, jac=True, method='L-BFGS-B', bounds=[(1e-9, W)] * W, options={'maxiter': 5000})
        res.append(((r.fun / W - q0) / 2 * W, name, np.sort(r.x)))
    res.sort(key=lambda t: t[0]); e, name, x = res[0]; g = np.diff(x)
    print('W=%d: min N E_T %+.4f (from %s); others %s' % (W, e, name, ' '.join('%+.3f' % t[0] for t in res[1:6])), flush=True)
    print('   gaps: first 8 %s | last 8 %s | bulk mean %.4f sd %.4f min %.4f max %.4f; points at the walls: %d'
          % (np.round(g[:8], 3), np.round(g[-8:], 3), g[20:-20].mean(), g[20:-20].std(), g[20:-20].min(), g[20:-20].max(),
             int(np.sum(x < 1e-6) + np.sum(x > W - 1e-6))), flush=True)
