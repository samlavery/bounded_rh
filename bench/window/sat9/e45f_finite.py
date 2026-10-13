"""E45f: (part of the e45 protocol, run early on the layers already saved): for every saved free-end layer with E_end < 0,
mirror it, insert a flat interior of m sites (m in {0, 25, 50, 100, 200, 400}), and evaluate (1') = Q_pp + T_g on the finite chain
with the exact-kernel evaluator (e43 Chain).  Also 2 E_end + tau(a) P for comparison."""
import json, glob, numpy as np
exec(open('e43_scalable.py').read().split("if __name__ == '__main__':")[0])
from common import g_of as gof
for fn in sorted(glob.glob('e45_2_a*_L*.json')):
    d = json.load(open(fn)); a = d['a']; y = np.array(d['y']); E = d['E_end']
    if E >= 0: continue
    tau = 8 * float(gof(a * np.arange(1, 400)).sum()); layer = y[:-1]; yi = y[-1]
    out = []
    for m in (0, 25, 50, 100, 200, 400):
        prof = np.concatenate([layer, np.full(m, yi), layer[::-1]]); P = len(prof); ch = Chain(a, P); v = ch.onep(prof)[0]
        out.append('m=%d P=%d: (1\') %+.5f [Q_pp %+.5f, T_g %.4f; 2E_end + tau P = %+.4f]' % (m, P, v, v - ch.Tg, ch.Tg, 2 * E + tau * P))
    print('%s (E_end %+.6f, y0 %.3f, y_inf %.3f):\n   ' % (fn, E, y[0], yi) + '\n   '.join(out), flush=True)
