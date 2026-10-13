"""E45g (lead, 2026-10-09; one extra point, declared before running): a = 0.999, end depth free (y >= 0.01), L in {50, 100, 200},
min E_end (e45 solver; seeds: ramps from 0.01 to y_inf in {0.5, 1.0, 1.6}); then the mirrored finite chains with flat interiors
m in {0, 25, 50, 100, 200, 400} and (1') = Q_pp + T_g by the exact-kernel chain evaluator; report the worst (smallest) (1').
If (1') < 0: full LP with environment (e38 model, N = 4P) + mp50.
PREDICTION (bridge-port): E_end negative, ~ -0.05 to -0.2 at L = 200; every mirrored chain positive but thin, worst (1') ~ +0.3 to
+0.6 at P = 100 (tau(0.999) ~ 0.006 per pair)."""
import sys, json, numpy as np
exec(open('e45_round2.py').read().split("\nif __name__ == '__main__':\n")[0])
exec(open('e43_scalable.py').read().split("if __name__ == '__main__':")[0])
a = 0.999; worst = (np.inf, None)
for L in (50, 100, 200):
    seeds = [ramp(L, 0.01, yi, fr) for yi in (0.5, 1.0, 1.6) for fr in (0.2, 0.5)]
    f, y, gn, lam, conv, it = solve(a, L, 0.01, seeds, n=max(8000, int(4 * a * L) + 4000))
    print('a=0.999 L=%3d (end depth free): min E_end %+.6f | ||g|| %.2e | min eig %+.3e | %s | y_0 %.4f y_1 %.4f y_inf %.4f' % (L, f, gn, lam, 'CONVERGED' if conv else 'not converged', y[0], y[1], y[-1]), flush=True)
    json.dump({'a': a, 'L': L, 'E_end': f, 'y': y.tolist(), 'conv': bool(conv)}, open('e45g_a0.999_L%d.json' % L, 'w'))
    layer = y[:-1]; yi = y[-1]
    for m in (0, 25, 50, 100, 200, 400):
        prof = np.concatenate([layer, np.full(m, yi), layer[::-1]]); P = len(prof); ch = Chain(a, P); v = ch.onep(prof)[0]
        print('   m=%3d P=%4d: (1\') %+.6f [Q_pp %+.6f, T_g %.5f]' % (m, P, v, v - ch.Tg, ch.Tg), flush=True)
        if v < worst[0]: worst = (v, (L, m, P))
print('WORST mirrored chain at a=0.999: (1\') = %+.6f at (L, m, P) = %s' % worst, flush=True)
