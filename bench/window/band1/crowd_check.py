"""Independent checks of crowd_dp.py (certificate v1).
(1) periodic model, N = 64, random D: slack(D) = P_h + T_g exactly (P_h from h^ = qf - g^ on j/N, T_g from g_N = sum of images),
    and Delta_B(y) = E(Z) - E(D) = 2[K_N(2iy) - K_N(0)] + sum_b m_b phi_N(u_b)  (the field form used by the DP);
(2) normalisation of the line-model psi (Taylor coefficients c_j) against the periodic phi_N at N = 2048;
(3) exact all-pairs P_h-free objective  S0 + sum m psi + T_g/y^2  on the DP binding chains (cell centres), at the ends and the
    middle of each y-interval: must be >= the DP bound; also the nearest-neighbour objective (the DP's own relaxation)."""
import sys, numpy as np
sys.argv = ['crowd_dp.py', '128']
import crowd_dp as C
from fractions import Fraction
rng = np.random.default_rng(5)
qf = C.qf; yk = C.yk; Dk = C.Dk
def ghat(a):
    a = np.abs(np.asarray(a, float)); return np.interp(a, np.arange(len(yk) + 1) * Dk, np.concatenate([yk, [0.0]]), right=0.0)
def gN(u, N):
    return sum(C.gfun(u + k * N) for k in range(-40, 41))
print('(1) periodic decomposition, N = 64', flush=True)
N = 64; js = np.arange(-3 * N, 3 * N + 1)
for trial in range(3):
    k2 = 6; x = np.concatenate([np.sort(rng.uniform(0, N, N - 2 * k2)), rng.uniform(0, N, k2)]); m = np.concatenate([np.ones(N - 2 * k2), np.full(k2, 2.0)])
    S = np.exp(2j * np.pi * np.outer(js, x) / N) @ m; qv = np.where(np.abs(js) < N, qf(np.minimum(np.abs(js) / N, 1 - 1e-12)), 0.0)
    E = float(np.sum(qv * np.abs(S) ** 2) / N); gh = ghat(js / N); hh = qv - gh
    gN0 = float(gN(np.array([0.0]), N)[0]); FC = float(hh[js == 0][0]) * N + gN0 * float(np.sum(m ** 2))
    Ph = float(np.sum(np.where(js != 0, hh, 0.0) * np.abs(S) ** 2) / N)
    D = x[:, None] - x[None, :]; G = gN(D.ravel(), N).reshape(D.shape); np.fill_diagonal(G, 0.0); Tg = float(m @ G @ m)
    s_idx = len(x) - 1; s = x[s_idx]
    for y in (0.1, 0.3):
        B = 2 * np.cosh(2 * np.pi * js * y / N) - 2
        dB = float(np.sum(qv * (B ** 2 + 2 * B * np.real(S * np.exp(-2j * np.pi * js * s / N)))) / N)
        KN = lambda z: np.real(np.sum(qv[None, :] * np.exp(2j * np.pi * np.outer(z, js) / N), 1)) / N
        u = x - s; others = np.arange(len(x)) != s_idx
        phiN = 4 * (KN(u[others] + 1j * y) - KN(u[others]))
        field = 2 * (KN(np.array([2j * y]))[0] - KN(np.array([0.0]))[0]) + float(m[others] @ phiN)
        print('   trial %d y=%.1f: slack %.10f  P_h + T_g %.10f (P_h %.4f, T_g %.4f) | Delta_B %.10f  field form %.10f' % (trial, y, E - FC, Ph + Tg, Ph, Tg, dB, field), flush=True)
print('(2) psi normalisation: line-model psi (Taylor coefficients) vs periodic phi_N/y^2 at N = 2048', flush=True)
N = 2048; js = np.arange(-N + 1, N); qv = qf(np.abs(js) / N)
uu = np.array([0.3, 0.79, 1.0, 2.37, 5.5]);
for y in (0.05, 0.25, 0.4):
    KN = lambda z: np.real(np.sum(qv[None, :] * np.exp(2j * np.pi * np.outer(z, js) / N), 1)) / N
    per = 4 * (KN(uu + 1j * y) - KN(uu)) / y ** 2
    line = (C.cjs(uu) * np.array([y ** (2 * j) for j in range(C.J)])[:, None]).sum(0)
    s0p = 2 * (KN(np.array([2j * y]))[0] - KN(np.array([0.0]))[0]) / y ** 2
    print('   y=%.2f: max |psi_line - phi_N/y^2| = %.2e ; S0 line %.6f periodic %.6f' % (y, np.max(np.abs(per - line)), C.S0(y), s0p), flush=True)
print('(3) exact objectives on the DP binding chains', flush=True)
def psi_exact(u, y):
    return (C.cjs(np.abs(u), C.al2, C.wa2, C.qa2) * np.array([y ** (2 * j) for j in range(C.J)])[:, None]).sum(0)
def objective(pos_r, m_r, pos_l, m_l, y, nn_only=False):
    val = C.S0(y)
    for pos, m in ((pos_r, m_r), (pos_l, m_l)):
        val += float(m @ psi_exact(pos, y)) + 4 * float(m @ C.gfun(np.abs(pos))) / y ** 2
    if nn_only:
        for pos, m in ((pos_r, m_r), (pos_l, m_l)):
            if len(pos) > 1: val += 2 * float(np.sum(m[1:] * m[:-1] * C.gfun(np.abs(np.diff(pos))))) / y ** 2
    else:
        pos = np.concatenate([pos_r, -pos_l]); m = np.concatenate([m_r, m_l]); D = np.abs(pos[:, None] - pos[None, :])
        G = C.gfun(D.ravel()).reshape(D.shape); np.fill_diagonal(G, 0.0); val += float(m @ G @ m) / y ** 2
    return val
D0 = (26 / 256, 38 / 256, 52 / 256); configs = [(2, d) for d in D0]
for ylo, yhi in ((0.0, 0.05), (0.15, 0.2), (0.2, 0.25), (0.35, 0.4)):
    o = C.dp(ylo, yhi, configs)
    def topos(ch): return np.array([(C.lo[k] + C.hi[k]) / 2 for k, m in ch]), np.array([float(m) for k, m in ch])
    pf, mf = topos(o['free_chain'])
    for (R, d0) in configs:
        vc, ch = o['crowd'][(R, d0)]; pc, mc = topos(ch); bound = o['S0'] + o['Vfree'] + vc
        ys = [y for y in (ylo, (ylo + yhi) / 2, yhi) if y > 0]
        ex = [objective(pc, mc, pf, mf, y) for y in ys]; nn = [objective(pc, mc, pf, mf, y, True) for y in ys]
        print('   y in [%.2f,%.2f] R=%d d0=%.4f: DP bound %+.4f | binding chains (%d + %d points): NN objective %s | all-pairs objective %s'
              % (ylo, yhi, R, d0, bound, len(pc), len(pf), ' '.join('%+.3f' % v for v in nn), ' '.join('%+.3f' % v for v in ex)), flush=True)
