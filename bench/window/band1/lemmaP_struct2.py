"""Cheapest negative Delta_B, exact constraint: min W s.t. Delta_B/2 <= -eps*g(0) (SLSQP), seeded from Delta_B-seeking
minimisers (feasible starts).  One pair at fixed depth y.  usage: python3 lemmaP_struct2.py WINDOW N"""
import sys
WINN = sys.argv[1:3]
exec(open('lemmaP_struct.py').read().split("const = N * (gN0 - gh0) / 2 + gN0")[0])
const = N * (gN0 - gh0) / 2 + gN0
for y in (0.03, 0.05, 0.1, 0.2, 0.3):
    seeds = []
    for s in range(10):
        r = minimize(lambda z: (lambda p: (p[0] - p[2], p[1] - p[3]))(parts(z, y)), inits(n1, 0, 1, 100 + s), jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        seeds.append((r.fun, r.x))
    mostneg = min(v for v, _ in seeds) / N / 2 / g0
    row = ['most negative Delta_B/2 %+.4f' % mostneg]
    for eps in (0.001, 0.01):
        best = None
        for v, z0 in seeds:
            if v / N / 2 > -eps * g0: continue
            cons = {'type': 'ineq', 'fun': lambda z: -((lambda p: (p[0] - p[2]) / N / 2)(parts(z, y)) + eps * g0),
                    'jac': lambda z: -((lambda p: (p[1] - p[3]) / N / 2)(parts(z, y)))}
            r = minimize(lambda z: (lambda p: (p[0] / N - const, p[1] / N))(parts(z, y)), z0, jac=True, method='SLSQP', constraints=[cons], options={'maxiter': 500, 'ftol': 1e-12})
            d, g, dD, gD = parts(r.x, y)
            if (d - dD) / N / 2 <= -eps * g0 * 0.999 and (best is None or d / N - const < best[0]): best = (d / N - const, dD / N - const, (d - dD) / N / 2)
        row.append('Delta_B/2 <= -%.3f: %s' % (eps, 'min W %+.4f (slack %+.4f)' % (best[0] / g0, best[1] / g0) if best else 'no feasible seed'))
    print('%s N=%d y=%.2f: %s' % (WIN, N, y, ' | '.join(row)), flush=True)
