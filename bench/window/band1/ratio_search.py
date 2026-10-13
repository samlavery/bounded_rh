"""Round 8: adversarial maximisation of R(Z) = -Delta_B / s(D) (periodic model, pSq weights; LP = s(D) + Delta_B).
  s(D) = E(D) - F_C^pSq = 2 d_D/N + g^(0) N - g(0) pSq,  Delta_B = E(Z) - E(D) = 2 (d_Z - d_D)/N,  d = sum_{0<j<N} q(j/N)|S_j|^2.
  D: each item (pair of multiplicity m_i at s_i) -> an on-line point of mass 2 m_i at s_i.
Maximise R by L-BFGS-B on Delta_B/s (all positions and depths free, y in [1e-3, 3]), two passes per start.
Reports R, Delta_B, s, LP, and the pair-local R_loc = -Delta_B / T_g^loc (T_g^loc: the terms of T_g(D) = sum_{a != b} m_a m_b g_N(x_a - x_b)
with at least one point within 8 of a pair position).  Runs with R > 0.9 are re-evaluated in mpmath (50 digits).
usage: python3 ratio_search.py REGIME[,REGIME..] N[,N..] OUT_PREFIX   (REGIME in blocks mixed deep stacks random crowd)"""
import sys, json, time, numpy as np
_ARGS = list(sys.argv)
sys.argv = ['mixed_search.py', 'none', '64', '/tmp/x']
exec(open('mixed_search.py').read().split("for N in NS:")[0])
REG = _ARGS[1].split(','); NS = [int(v) for v in _ARGS[2].split(',')]; OUT = _ARGS[3]
YK = np.array([float(v) for v in YKF]); DK = 1 / 32; NB = len(YK); G0F = float(G0_MP)
def g_of(u):
    u = np.atleast_1d(np.asarray(u, float)); th = 2 * np.pi * DK * u
    return DK * np.sinc(DK * u) ** 2 * (YK[0] + 2 * (np.cos(np.outer(th, np.arange(1, NB))) @ YK[1:]))
def gN(u, N, K=60):
    u = ((np.asarray(u, float) + N / 2) % N) - N / 2; out = np.zeros(len(u))
    for n in range(-K, K + 1): out += g_of(u + n * N)
    return out
def parts(z, n_on, m_on, mi, N, grad=True):
    J, q, g0, gh0 = setup(N); K = len(mi)
    x, s, y = z[:n_on], z[n_on:n_on + K], z[n_on + K:]
    Ex = np.exp(2j * np.pi * np.outer(J, x) / N); Es = np.exp(2j * np.pi * np.outer(J, s) / N)
    arg = 2 * np.pi * np.outer(J, y) / N; A = 2 * np.cosh(arg)
    SZ = Ex @ m_on + (Es * A) @ mi; SD = Ex @ m_on + Es @ (2 * mi)
    dZ = float(q @ np.abs(SZ) ** 2); dD = float(q @ np.abs(SD) ** 2)
    pSq = float(np.sum(m_on ** 2)) + 4 * float(np.sum(mi))
    s_ = 2 * dD / N + gh0 * N - g0 * pSq; dB = 2 * (dZ - dD) / N
    if not grad: return s_, dB
    k2 = 2j * np.pi * J[:, None] / N; WZ = (q * np.conj(SZ))[:, None]; WD = (q * np.conj(SD))[:, None]
    gxZ = 2 * np.real(WZ * Ex * m_on[None, :] * k2).sum(0); gsZ = 2 * np.real(WZ * Es * A * mi[None, :] * k2).sum(0)
    gyZ = 2 * np.real(WZ * Es * 2 * np.sinh(arg) * mi[None, :] * (2 * np.pi * J[:, None] / N)).sum(0)
    gxD = 2 * np.real(WD * Ex * m_on[None, :] * k2).sum(0); gsD = 2 * np.real(WD * Es * 2 * mi[None, :] * k2).sum(0)
    g_s = 2 * np.concatenate([gxD, gsD, np.zeros(K)]) / N
    g_dB = 2 * np.concatenate([gxZ - gxD, gsZ - gsD, gyZ]) / N
    return s_, dB, g_s, g_dB
def negR(z, n_on, m_on, mi, N):
    s_, dB, g_s, g_dB = parts(z, n_on, m_on, mi, N)
    return dB / s_, (g_dB * s_ - dB * g_s) / s_ ** 2
def d_mp(x, m_on, s, y, mi, N, doubled):
    q = q_mp(N); d = mpm.mpf(0)
    X = [mpm.mpf(float(v)) for v in x]; Sx = [mpm.mpf(float(v)) for v in s]; Y = [mpm.mpf(float(v)) for v in y]
    for j in range(1, N):
        S = mpm.mpc(0)
        for xa, ma in zip(X, m_on): S += int(ma) * mpm.expjpi(2 * j * xa / N)
        for si, yi, m in zip(Sx, Y, mi):
            S += int(m) * (2 if doubled else 2 * mpm.cosh(2 * mpm.pi * j * yi / N)) * mpm.expjpi(2 * j * si / N)
        d += q[j - 1] * (S.real ** 2 + S.imag ** 2)
    return d
def ghat(a):
    return np.interp(np.abs(a), np.arange(NB + 1) * DK, np.concatenate([YK, [0.0]]), right=0.0)
def tg_fourier(pos, mass, N):
    """T_g of a point set, exactly: (1/N) sum_{|j| < 3N} g-hat(j/N)|S_j|^2 - g(0) sum m^2  (g_N(0) = g(0) for N a multiple of 32)"""
    if len(pos) == 0: return 0.0
    JA = np.arange(-3 * N + 1, 3 * N); S = np.exp(2j * np.pi * np.outer(JA, pos) / N) @ mass
    return float(ghat(JA / N) @ np.abs(S) ** 2) / N - G0F * float(np.sum(mass ** 2))
def tg_parts(x, m_on, s, mi, N, rloc=8.0):
    """T_g(D) and T_g^loc = T_g(D) - T_g(points farther than rloc from every pair position), both exact by Fourier."""
    pos = np.concatenate([x, s]); mass = np.concatenate([m_on, 2 * mi])
    dist = np.min(np.abs(((pos[:, None] - s[None, :]) + N / 2) % N - N / 2), axis=1) if len(s) else np.full(len(pos), np.inf)
    far = dist > rloc; Tg = tg_fourier(pos, mass, N)
    return Tg, Tg - tg_fourier(pos[far], mass[far], N)
RES = []
def run(reg, N, tag, x, m_on, s, y, mi, ylo=1e-3, yhi=3.0, passes=2):
    t0 = time.time(); m_on = np.asarray(m_on, float); mi = np.asarray(mi, float); x = np.asarray(x, float); s = np.asarray(s, float); y = np.asarray(y, float)
    assert abs(m_on.sum() + 2 * mi.sum() - N) < 1e-9
    n_on, K = len(x), len(s); z = np.concatenate([x, s, np.clip(y, ylo, yhi)]); bnds = [(None, None)] * (n_on + K) + [(ylo, yhi)] * K
    best = None
    for _ in range(passes):
        r = minimize(lambda zz: negR(zz, n_on, m_on, mi, N), z, jac=True, method='L-BFGS-B', bounds=bnds,
                     options={'maxiter': 20000, 'maxfun': 40000, 'ftol': 1e-15, 'gtol': 1e-10, 'maxcor': 30})
        if best is None or r.fun < best.fun: best = r
        z = best.x
    z = best.x; s_, dB = parts(z, n_on, m_on, mi, N, grad=False); R = -dB / s_
    xr, sr, yr = z[:n_on], z[n_on:n_on + K], z[n_on + K:]
    Tg, Tloc = tg_parts(xr, m_on, sr, mi, N)
    row = {'reg': reg, 'N': N, 'tag': tag, 'R': R, 'dB': dB, 's': s_, 'LP': s_ + dB, 'Tg': Tg, 'Ph': s_ - Tg, 'Tg_loc': Tloc,
           'R_loc': (-dB / Tloc) if Tloc > 0 else None, 'pairs': float(mi.sum()), 'y_range': [float(yr.min()), float(yr.max())],
           'nit': int(best.nit), 'secs': round(time.time() - t0, 1),
           'cfg': {'x': xr.tolist(), 'm_on': m_on.tolist(), 's': sr.tolist(), 'y': yr.tolist(), 'mi': mi.tolist()}}
    if R > 0.9:
        J, q, g0, gh0 = setup(N); pSq = float(np.sum(m_on ** 2)) + 4 * float(np.sum(mi))
        dZ = d_mp(xr, m_on, sr, yr, mi, N, False); dD = d_mp(xr, m_on, sr, yr, mi, N, True)
        smp = 2 * dD / N + GH0_MP * N - G0_MP * pSq; dBmp = 2 * (dZ - dD) / N
        row['R_mp50'] = float(-dBmp / smp); row['LP_mp50'] = float(smp + dBmp)
    RES.append(row)
    print('%-6s N=%3d %-40s R %+.4f (dB %+.4f, s %.4f, LP %+.4f; P_h %.3f, T_g %.3f, T_g^loc %.3f, R_loc %s) pairs %g y %.3f-%.3f%s [nit %d, %.0fs]'
          % (reg, N, tag, R, dB, s_, s_ + dB, s_ - Tg, Tg, Tloc, ('%+.3f' % row['R_loc']) if row['R_loc'] is not None else '-', mi.sum(),
             yr.min(), yr.max(), (' | mp50 R %+.6f LP %+.6f' % (row['R_mp50'], row['LP_mp50'])) if 'R_mp50' in row else '', best.nit, row['secs']), flush=True)
    return row
BLK = {(g['N'], g['Y']): g for g in json.load(open('bulk_end_n4_starts.json'))}
TH = json.load(open('round7_thinnest.json'))
E38 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/sat9/e38_best.json'))
for N in NS:
    P0 = N // 4
    if 'blocks' in REG:
        for Y in (0.2, 0.4):
            g = BLK[(N, Y)]; s, env = np.array(g['pairs']), np.array(g['env'])
            for y0 in (0.1, 0.3, 0.5, 0.8):
                run('blocks', N, 'rb%d Y=%.1f start y=%.1f' % (P0, Y, y0), env, np.ones(len(env)), s, np.full(P0, y0), np.ones(P0))
    if 'mixed' in REG:
        for r in TH['lowest'] + TH['lowest_with_deep']:
            if r['N'] != N or r['fam'] not in ('a', 'e', 'b', 'c'): continue
            c = r['cfg']; run('mixed', N, 'r7 %s %s' % (r['fam'], r['tag'][:28]), c['x'], c['m_on'], c['s'], c['y'], c['mi'])
    if 'deep' in REG:
        for e in E38:
            if e['N'] != N: continue
            P = e['P']; z = np.array(e['z']); n_on = N - 2 * P
            run('deep', N, 'e38 P=%d %s' % (P, e['fam'][:24]), z[:n_on], np.ones(n_on), z[n_on:n_on + P], z[n_on + P:], np.ones(P))
    if 'stacks' in REG:
        for Y in (0.2, 0.4):
            g = BLK[(N, Y)]; s, env = np.array(g['pairs']), np.array(g['env']); c0 = float(np.mean(s))
            for m in (2, 3):
                for ys in (0.3, 0.6, 0.9):
                    e2 = env[np.argsort(-np.abs(env - c0))[2 * m:]]
                    run('stacks', N, 'rb%d Y=%.1f stack m=%d y=%.1f centre' % (P0, Y, m, ys), np.sort(e2), np.ones(len(e2)),
                        np.concatenate([s, [c0 + 0.37]]), np.concatenate([np.full(P0, Y), [ys]]), np.concatenate([np.ones(P0), [m]]))
    if 'random' in REG:
        for sd in range(30):
            seed = 8000000 + 1000 * N + sd; rng = np.random.default_rng(seed)
            P = int(rng.integers(1, min(64, N // 4) + 1)); y0 = rng.uniform(0.05, 1.5, P)
            if sd % 2 == 0:
                a = rng.uniform(0.85, 1.05); s0 = a * np.arange(P) + rng.normal(0, 0.03, P); lay = 'block a=%.2f' % a
            else:
                s0 = rng.uniform(0, N, P); lay = 'uniform'
            n_on = N - 2 * P; x0 = np.arange(np.floor(s0.max()) + 1, np.floor(s0.max()) + 1 + n_on) + rng.normal(0, 0.05, n_on)
            run('random', N, 'P=%d %s seed %d' % (P, lay, seed), x0, np.ones(n_on), s0, y0, np.ones(P))
    if 'crowd' in REG:      # one pair (or two) with on-line doubles crowding it, density-1 lattice elsewhere
        for sd in range(20):
            seed = 9000000 + 1000 * N + sd; rng = np.random.default_rng(seed)
            P = 1 + (sd % 3 == 2); nd = int(rng.integers(1, 5)); y0 = rng.uniform(0.15, 0.6, P)
            s0 = np.array([0.0, 1.0][:P]); xd = rng.choice([-1, 1], nd) * rng.uniform(0.6, 1.0, nd) + (P - 1) * 0.5 * (rng.random(nd) > 0.5)
            n1 = N - 2 * P - 2 * nd; lat = np.arange(2, 2 + n1) + 0.0; x0 = np.concatenate([xd, lat]); m0 = np.concatenate([np.full(nd, 2.0), np.ones(n1)])
            run('crowd', N, 'P=%d doubles %d seed %d' % (P, nd, seed), x0, m0, s0, y0, np.ones(P))
json.dump(RES, open(OUT + '.json', 'w'))
for reg in sorted(set(r['reg'] for r in RES)):
    rr = [r for r in RES if r['reg'] == reg]; b = max(rr, key=lambda r: r['R']); bl = max((r for r in rr if r['R_loc'] is not None), key=lambda r: r['R_loc'])
    print('SUMMARY %-6s (%d runs): sup R %+.4f [%s N=%d; dB %+.4f s %.4f]%s | sup R_loc %+.3f [%s N=%d]'
          % (reg, len(rr), b['R'], b['tag'], b['N'], b['dB'], b['s'], (' mp50 R %+.6f' % b['R_mp50']) if 'R_mp50' in b else '', bl['R_loc'], bl['tag'], bl['N']), flush=True)
