"""Structure of Lemma P: the cheapest way to make Delta_B negative.  For one pair at fixed depth y, minimise
W = slack(D(Z)) + Delta_B/2 subject to Delta_B/2 <= -eps (quadratic penalty), from structured, random and
Delta_B-seeking starts; report the minimal slack (and W) among configurations with Delta_B/2 <= -eps (units 2 delta').
usage: python3 lemmaP_struct.py WINDOW N"""
import sys
WINN = sys.argv[1:3]
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = WINN[0], int(WINN[1])"))
n1 = N - 2
def parts(z, y):
    d, g = d_and_grad(z, n1, 0, 1, np.array([y]))
    xr = np.concatenate([z[:n1], z[n1:n1 + 1]]); mr = np.concatenate([np.ones(n1), [2.0]])
    Er = np.exp(2j * np.pi * np.outer(J, xr) / N); S = Er @ mr; dD = float(qv @ np.abs(S) ** 2)
    Wq = (qv * np.conj(S))[:, None]; gD = 2 * np.real(Wq * Er * mr[None, :] * (2j * np.pi * J[:, None] / N)).sum(0)
    return d, g, dD, gD
const = N * (gN0 - gh0) / 2 + gN0
for y in (0.05, 0.1, 0.2, 0.3):
    seeds = [inits(n1, 0, 1, s) for s in range(24)]
    for s in range(8):      # Delta_B-seeking seeds
        r = minimize(lambda z: (lambda p: (p[0] - p[2], p[1] - p[3]))(parts(z, y)), inits(n1, 0, 1, 100 + s), jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        seeds.append(r.x)
    row = []
    for eps in (0.001, 0.01, 0.1):
        best = (np.inf, None)
        for z0 in seeds:
            for mu in (1e3, 1e5):
                def f(z):
                    d, g, dD, gD = parts(z, y); W = d / N - const; dB = (d - dD) / N
                    v = max(0.0, dB / 2 + eps * g0); return W + mu * v * v, g / N + (mu * 2 * v * (g - gD) / N / 2 if v > 0 else 0)
                r = minimize(f, z0, jac=True, method='L-BFGS-B', options={'maxiter': 3000}); z0 = r.x
            d, g, dD, gD = parts(r.x, y); dB = (d - dD) / N
            if dB / 2 <= -eps * g0 * 0.999:
                W = d / N - const
                if W < best[0]: best = (W, (dD / N - const), dB / 2)
        row.append('Delta_B/2 <= -%.3f: min W %s (slack %s)' % (eps, '%+.4f' % (best[0] / g0) if best[1] else 'none found', '%+.4f' % (best[1] / g0) if best[1] else '-'))
    print('%s N=%d y=%.2f: %s' % (WIN, N, y, ' | '.join(row)), flush=True)
