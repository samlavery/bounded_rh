"""Round 7: adversarial truth check of Lemma P for MIXED shallow/deep configurations, full exact LP, per-zero (pSq) weights,
periodic model (period N, total multiplicity N).
  S_j = sum_on m_a e(j x_a/N) + sum_items m_i 2cosh(2 pi j y_i/N) e(j s_i/N),   d = sum_{0<j<N} q(j/N) |S_j|^2   (all terms >= 0)
  LP  = E(Z) - F_C(D(Z)) = 2d/N + g^(0) N - g_N(0) (sum_on m_a^2 + 4 sum_items m_i),   g_N(0) = g(0) for N a multiple of 32.
An item is an off-line pair of multiplicity m_i (a stack: m_i coincident pairs; pSq weight 2 m_i for each of its two zeros).
L-BFGS-B over all on-line positions, item positions and item depths (shallow items y in [1e-3, 0.8], deep items y in [0.8, 3];
family d uses one range [1e-3, 3]).  Candidates with float LP < 1 are re-evaluated in mpmath at 50 digits (q from the window's
closed form with its exact rational coefficients; g^(0), g(0) from the exact rational knots).
usage: python3 mixed_search.py FAMILY[,FAMILY..] N[,N..] OUT_PREFIX   (FAMILY in a b c d v; v = validation)"""
import sys, json, time, math, numpy as np
from fractions import Fraction
from scipy.optimize import minimize
import mpmath as mpm
FAMS = sys.argv[1].split(','); NS = [int(v) for v in sys.argv[2].split(',')]; OUT = sys.argv[3]
lsrc = open('lemmaP.py').read().split("if __name__ == '__main__':")[0]
cj = json.load(open('cert_R8_backed.json')); YKF = [Fraction(v) for v in cj['knots_rational']]
CNUM = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum']
SETUP = {}
def setup(N):
    if N not in SETUP:
        L = {}; exec(lsrc.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % N), L)
        assert abs(L['gN0'] - L['g0']) < 1e-15
        J = np.arange(1, N); SETUP[N] = (J, L['qfun'](J / N), float(L['g0']), float(L['gh0']))
    return SETUP[N]
def lp_grad(z, n_on, m_on, mi, N):
    J, q, g0, gh0 = setup(N); K = len(mi)
    x, s, y = z[:n_on], z[n_on:n_on + K], z[n_on + K:]
    Ex = np.exp(2j * np.pi * np.outer(J, x) / N); Es = np.exp(2j * np.pi * np.outer(J, s) / N)
    arg = 2 * np.pi * np.outer(J, y) / N; A = 2 * np.cosh(arg)
    S = Ex @ m_on + (Es * A) @ mi; d = float(q @ np.abs(S) ** 2)
    LP = 2 * d / N + gh0 * N - g0 * (float(np.sum(m_on ** 2)) + 4 * float(np.sum(mi)))
    W = (q * np.conj(S))[:, None]; k2 = 2j * np.pi * J[:, None] / N
    gx = 2 * np.real(W * Ex * m_on[None, :] * k2).sum(0)
    gs = 2 * np.real(W * Es * A * mi[None, :] * k2).sum(0)
    gy = 2 * np.real(W * Es * 2 * np.sinh(arg) * mi[None, :] * (2 * np.pi * J[:, None] / N)).sum(0)
    return LP, 2 * np.concatenate([gx, gs, gy]) / N
# ---------------- mpmath re-evaluation (50 digits) ----------------
mpm.mp.dps = 50
_QMP = {}
def q_mp(N):
    if N in _QMP: return _QMP[N]
    c = [mpm.mpf(v) / mpm.mpf(CNUM[0]) for v in CNUM[1:]]; c += [mpm.mpf(0)] * (24 - len(c))
    zz = [mpm.mpf(1)] + c; w = [mpm.sqrt(2)] + [2 * mpm.pi * k for k in range(1, 25)]; A = 2 * mpm.sin(w[0] / 2) / w[0]
    def I(nu, th, h):
        l = 1 - h; x = nu * l / 2; s = mpm.mpf(1) if x == 0 else mpm.sin(x) / x
        return l * mpm.cos(-nu * h / 2 + th) * s
    out = []
    for j in range(1, N):
        h = mpm.mpf(j) / N; t = mpm.mpf(0)
        for i in range(25):
            if zz[i] == 0: continue
            for k in range(25):
                if zz[k] == 0: continue
                t += zz[i] * zz[k] * (I(w[i] + w[k], w[k] * h, h) + I(w[i] - w[k], -w[k] * h, h)) / 2
        out.append(t / A ** 2)
    _QMP[N] = out; return out
G0_MP = mpm.mpf(1) / 32 * (mpm.mpf(YKF[0].numerator) / YKF[0].denominator + 2 * sum(mpm.mpf(v.numerator) / v.denominator for v in YKF[1:]))
GH0_MP = mpm.mpf(YKF[0].numerator) / YKF[0].denominator
def lp_mp(x, m_on, s, y, mi, N):
    q = q_mp(N); d = mpm.mpf(0)
    X = [mpm.mpf(float(v)) for v in x]; Sx = [mpm.mpf(float(v)) for v in s]; Y = [mpm.mpf(float(v)) for v in y]
    for j in range(1, N):
        S = mpm.mpc(0)
        for xa, ma in zip(X, m_on): S += int(ma) * mpm.expjpi(2 * j * xa / N)
        for si, yi, m in zip(Sx, Y, mi): S += int(m) * 2 * mpm.cosh(2 * mpm.pi * j * yi / N) * mpm.expjpi(2 * j * si / N)
        d += q[j - 1] * (S.real ** 2 + S.imag ** 2)
    return 2 * d / N + GH0_MP * N - G0_MP * (sum(int(m) ** 2 for m in m_on) + 4 * sum(int(m) for m in mi))
# ---------------- runs ----------------
def relax(x, m_on, s, y, mi, ylo, yhi, N, maxiter=20000):
    n_on = len(x); z0 = np.concatenate([x, s, y])
    bnds = [(None, None)] * (n_on + len(s)) + list(zip(ylo, yhi))
    r = minimize(lambda z: lp_grad(z, n_on, np.asarray(m_on, float), np.asarray(mi, float), N), z0, jac=True, method='L-BFGS-B',
                 bounds=bnds, options={'maxiter': maxiter, 'maxfun': 2 * maxiter, 'ftol': 1e-15, 'gtol': 1e-9, 'maxcor': 30})
    K = len(s); return r.fun, r.x[:n_on], r.x[n_on:n_on + K], r.x[n_on + K:], r
RES = []
def record(fam, N, tag, seed, m_on, mi, ylo, yhi, x, s, y, passes=1):
    t0 = time.time()
    m_on = np.asarray(m_on, float); mi = np.asarray(mi, float)
    assert abs(m_on.sum() + 2 * mi.sum() - N) < 1e-9, (m_on.sum(), mi.sum(), N)
    LP, xr, sr, yr, r = relax(np.asarray(x, float), m_on, np.asarray(s, float), np.asarray(y, float), mi, ylo, yhi, N)
    for _ in range(passes - 1):
        LP2, xr2, sr2, yr2, r2 = relax(xr, m_on, sr, yr, mi, ylo, yhi, N)
        if LP2 < LP: LP, xr, sr, yr, r = LP2, xr2, sr2, yr2, r2
    P = float(mi.sum()); deep = np.asarray(ylo) >= 0.8 - 1e-12
    row = {'fam': fam, 'N': N, 'tag': tag, 'seed': seed, 'LP': float(LP), 'pairs': P, 'per_pair': float(LP / P) if P else None,
           'n_deep': int(mi[deep].sum()), 'deep_y': [float(v) for v in yr[deep]], 'shallow_y_range': [float(yr[~deep].min()), float(yr[~deep].max())] if np.any(~deep) else None,
           'max_on_mult': int(m_on.max()), 'nit': int(r.nit), 'gmax': float(np.max(np.abs(r.jac))), 'secs': round(time.time() - t0, 1),
           'cfg': {'x': xr.tolist(), 'm_on': m_on.tolist(), 's': sr.tolist(), 'y': yr.tolist(), 'mi': mi.tolist(), 'ylo': list(map(float, ylo)), 'yhi': list(map(float, yhi))}}
    if LP < 1:
        row['LP_mp50'] = float(lp_mp(xr, m_on, sr, yr, mi, N)); row['mp_minus_float'] = row['LP_mp50'] - float(LP)
    RES.append(row)
    print('%s N=%d %-34s seed %-6s LP %+.5f (pairs %g, deep %d, per pair %+.5f)%s  [nit %d, %.0fs]'
          % (fam, N, tag, seed, LP, P, row['n_deep'], row['per_pair'] if P else float('nan'),
             (' | mp50 %+.6f' % row['LP_mp50']) if 'LP_mp50' in row else '', r.nit, row['secs']), flush=True)
    return row
BLK = {(g['N'], g['Y']): g for g in json.load(open('bulk_end_n4_starts.json'))}      # rb16/32/64 at N = 4P, start (b), lowest of 3
def block(N, Y):
    g = BLK[(N, Y)]; return np.array(g['pairs']), np.array(g['env'])
def drop_env(env, centre, k):        # remove the k environment points farthest from the block centre (coordinates are centred, in [-N/2, N/2))
    if k <= 0: return env
    o = np.argsort(-np.abs(env - centre)); return env[np.sort(o[k:])]
for N in NS:
    P0 = N // 4
    if 'v' in FAMS:      # validation: start-(b) rb block at N = 4P with fixed depth must reproduce exact_n16's value; mp agrees with float
        for Y in (0.2, 0.4):
            s, env = block(N, Y); row = record('v', N, 'rb%d Y=%.1f fixed depth' % (P0, Y), '-', np.ones(len(env)), np.ones(P0),
                                              [Y] * P0, [Y] * P0, env, s, np.full(P0, Y))
            print('   reference (round 4, start b): %.4f' % BLK[(N, Y)]['LP_total'], flush=True)
            if 'LP_mp50' not in row: print('   mp50 %+.8f' % float(lp_mp(np.array(row['cfg']['x']), np.ones(len(env)), np.array(row['cfg']['s']), np.array(row['cfg']['y']), np.ones(P0), N)), flush=True)
    if 'a' in FAMS:      # deep pairs inserted into the block
        for Y in (0.2, 0.4):
            s, env = block(N, Y)
            for k in (1, 2, 4):
                for pos in ('centre', 'end'):
                    idx = (list(range(P0 // 2 - k // 2, P0 // 2 - k // 2 + k)) if pos == 'centre' else list(range(k)))
                    for yd in (0.8, 1.2, 2.0, 3.0):
                        y0 = np.full(P0, Y); y0[idx] = yd; ylo = np.full(P0, 1e-3); yhi = np.full(P0, 0.8); ylo[idx] = 0.8; yhi[idx] = 3.0
                        record('a', N, 'rb%d Y=%.1f k=%d %s yd=%.1f' % (P0, Y, k, pos, yd), '-', np.ones(len(env)), np.ones(P0), ylo, yhi, env, s, y0)
    if 'b' in FAMS:      # shallow block flanked by deep pairs (one each side, gap g), environment balanced
        for Y in (0.2, 0.4):
            s, env = block(N, Y); c = float(np.mean(s))
            for g in (1.0, 2.0, 4.0):
                for yd in (0.8, 1.2, 2.0):
                    s2 = np.concatenate([s, [s.min() - g, s.max() + g]]); y0 = np.concatenate([np.full(P0, Y), [yd, yd]])
                    ylo = np.concatenate([np.full(P0, 1e-3), [0.8, 0.8]]); yhi = np.concatenate([np.full(P0, 0.8), [3.0, 3.0]])
                    e2 = drop_env(env, c, 4)
                    record('b', N, 'rb%d Y=%.1f flank gap %g yd=%.1f' % (P0, Y, g, yd), '-', np.ones(len(e2)), np.ones(P0 + 2), ylo, yhi, e2, s2, y0)
    if 'c' in FAMS:      # stacks under pSq: one item of multiplicity m (m coincident pairs), and on-line multiplicities
        for Y in (0.2, 0.4):
            s, env = block(N, Y); c = float(np.mean(s))
            for m in (2, 3, 4, 6):
                for yd in (0.8, 1.0):
                    for pos in ('centre', 'end', 'isolated'):
                        sp = {'centre': c, 'end': s.max() + 1.5, 'isolated': c + N / 2 - 3}[pos]
                        e2 = np.sort(env[np.argsort(np.abs(env - sp))[2 * m:]]) if pos == 'isolated' else drop_env(env, c, 2 * m)
                        s2 = np.concatenate([s, [sp]]); y0 = np.concatenate([np.full(P0, Y), [yd]]); mi = np.concatenate([np.ones(P0), [m]])
                        ylo = np.concatenate([np.full(P0, 1e-3), [0.8]]); yhi = np.concatenate([np.full(P0, 0.8), [3.0]])
                        record('c', N, 'rb%d Y=%.1f stack m=%d y=%.1f %s' % (P0, Y, m, yd, pos), '-', np.ones(len(e2)), mi, ylo, yhi, e2, s2, y0)
            for mo in (2, 3):     # on-line multiplicity next to the block end and in the first gap
                for pos in ('end', 'gap'):
                    xp = s.max() + 0.5 if pos == 'end' else 0.5 * (s[0] + s[1])
                    e2 = drop_env(env, c, mo); x2 = np.concatenate([e2, [xp]]); mo_arr = np.concatenate([np.ones(len(e2)), [mo]])
                    record('c', N, 'rb%d Y=%.1f on-line mult %d %s' % (P0, Y, mo, pos), '-', mo_arr, np.ones(P0), np.full(P0, 1e-3), np.full(P0, 0.8), x2, s, np.full(P0, Y))
    if 'd' in FAMS:      # random mixtures, depths in one range [1e-3, 3]
        for sd in range(40):
            rng = np.random.default_rng(1000 * N + sd)
            Ps = int(rng.integers(0, N // 8 + 1)); Pd = int(rng.integers(1, 5)); P = Ps + Pd
            s0 = np.sort(rng.uniform(0, N, P)); y0 = np.concatenate([rng.uniform(0.05, 0.8, Ps), rng.uniform(0.8, 3.0, Pd)]); rng.shuffle(y0)
            n_on = N - 2 * P; x0 = np.sort(rng.uniform(0, N, n_on))
            record('d', N, 'random Ps=%d Pd=%d' % (Ps, Pd), str(1000 * N + sd), np.ones(n_on), np.ones(P), np.full(P, 1e-3), np.full(P, 3.0), x0, s0, y0)
    if 'e' in FAMS:      # random mixtures with deep pairs held deep: deep y in [0.8, 3], shallow y in [y_lo, 0.8]
        for ylo_s in (0.05, 0.1, 0.2):
            for sd in range(20):
                seed = 7000000 + 10000 * N + 100 * int(round(100 * ylo_s)) + sd; rng = np.random.default_rng(seed)
                Ps = int(rng.integers(0, N // 4 + 1)); Pd = int(rng.integers(1, 5)); P = Ps + Pd
                if sd % 2 == 0 and Ps > 0:       # near-lattice shallow block, deep pairs inside (replacing sites) or beside it
                    a = rng.uniform(0.9, 1.0); sb = a * np.arange(Ps) + rng.normal(0, 0.02, Ps)
                    sdp = np.concatenate([rng.choice(sb, size=min(Pd, Ps), replace=False) + 0.5 * a, sb.max() + a * (1 + np.arange(max(0, Pd - Ps)))])
                    s0 = np.concatenate([sb, sdp[:Pd]]); lay = 'block a=%.3f' % a
                else:
                    s0 = rng.uniform(0, N, P); lay = 'uniform'
                ys0 = rng.uniform(ylo_s, 0.8, Ps); yd0 = rng.uniform(0.8, 3.0, Pd); y0 = np.concatenate([ys0, yd0])
                ylo = np.concatenate([np.full(Ps, ylo_s), np.full(Pd, 0.8)]); yhi = np.concatenate([np.full(Ps, 0.8), np.full(Pd, 3.0)])
                n_on = N - 2 * P; span = (s0.min() - 1, s0.max() + 1)
                cand = np.arange(np.floor(span[1]) + 1, np.floor(span[1]) + 1 + N)                    # lattice outside the pairs, then random jitter
                x0 = (cand[:n_on] + rng.normal(0, 0.05, n_on))
                record('e', N, 'ylo=%.2f Ps=%d Pd=%d %s' % (ylo_s, Ps, Pd, lay), str(seed), np.ones(n_on), np.ones(P), ylo, yhi, x0, s0, y0, passes=2)
json.dump(RES, open(OUT + '.json', 'w'))
for fam in sorted(set(r['fam'] for r in RES)):
    rr = [r for r in RES if r['fam'] == fam]; b = min(rr, key=lambda r: r['LP']); bp = min((r for r in rr if r['per_pair'] is not None), key=lambda r: r['per_pair'])
    print('SUMMARY family %s (%d runs): min LP %+.5f [%s N=%d]%s; thinnest per-pair %+.5f [%s N=%d]'
          % (fam, len(rr), b['LP'], b['tag'], b['N'], (' mp50 %+.6f' % b['LP_mp50']) if 'LP_mp50' in b else '', bp['per_pair'], bp['tag'], bp['N']), flush=True)
