"""Analytic chain for Lemma P: numerical verification of each step (periodic model, two-sided normalisation
E = (1/N) sum_j q_j |S_j|^2, j over all integers; q = 0 off the band).
 I1  E(Z) - F_C(D) = P_h + T_g + Delta_B, P_h = (1/N) sum_{j!=0} h^_j |S_D,j|^2 >= 0, T_g = sum_{a!=b} m m' g_N >= 0 (exact)
 I2  Delta_B = (1/N) sum_j q_j |S_B,j|^2 + 2 sum_p (1/N) sum_j q_j B_p,j Re(conj(S_D,j) e(j s_p/N))     (field form)
 I3  2 (1/N) sum_j q_j B_j Re(conj S_D,j e(j s/N)) = 2 sum_b m_b L_y(x_b - s),  L_y = (q B_y)-check  (real-space form)
 I4  Poisson: sum over a full lattice of L_y(n + t) = 0 for all t, y
 I5  pair block >= 0 pointwise in alpha (>= (A_1 - A_2)^2-type), no uniform constant
 S_b the lead's step (b): |cross| <= 2 ||S_env^fl|| ||S_B||  -> CS lower bound for W; class: shallow pair + K remote dipoles
 T   termwise step: Lambda_y(u) = 4 g(u) + 2 L_y(u) at integer u (g tight there)
 V   second order: Delta_B / y^2 -> -2 V''_D(s); curvature-slack constant lambda* = sup V''_D(s)/s(D) over V'' > 0
usage: python3 lemmaP_chain.py WINDOW N"""
import sys, json, numpy as np
from scipy.optimize import minimize
WINN = sys.argv[1:3]
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = WINN[0], int(WINN[1])"))
JA = np.arange(-3 * N + 1, 3 * N)                      # all frequencies where q or g^ can be nonzero (A = 3)
aJ = JA / N; qA = np.where(np.abs(aJ) < 1, qfun(np.minimum(np.abs(aJ), 0.99999)), 0.0)
ghA = np.interp(np.abs(aJ), np.arange(nb + 1) * Dk, np.concatenate([yk, [0.0]])); hhA = qA - ghA
def Sfull(x, m, freqs): return np.exp(2j * np.pi * np.outer(freqs, x) / N) @ m
def amps_pair(freqs, y): return 2 * np.cosh(2 * np.pi * np.outer(freqs, y) / N)
def config_terms(xon, mon, s, y):
    xD = np.concatenate([xon, s]); mD = np.concatenate([mon, np.full(len(s), 2.0)])
    SD = Sfull(xD, mD, JA); SB = (np.exp(2j * np.pi * np.outer(JA, s) / N) * (amps_pair(JA, y) - 2)).sum(1)
    E_Z = float(np.sum(qA * np.abs(SD + SB) ** 2) / N); E_D = float(np.sum(qA * np.abs(SD) ** 2) / N)
    nz = JA != 0
    Ph = float(np.sum(hhA[nz] * np.abs(SD[nz]) ** 2) / N)
    Tg = float(np.sum(ghA * np.abs(SD) ** 2) / N) - gN0 * float(np.sum(mD ** 2))
    FC = (qfun(np.array([0.0]))[0] - gh0) * N + gN0 * float(np.sum(mD ** 2))
    return E_Z, E_D, Ph, Tg, FC, SD, SB, xD, mD
def L_y(u, y):
    a = np.arange(-N + 1, N); qq = np.where(np.abs(a) < N, qfun(np.minimum(np.abs(a) / N, 0.99999)), 0.0)
    B = 2 * (np.cosh(2 * np.pi * a * y / N) - 1)
    return np.real(np.exp(2j * np.pi * np.outer(np.atleast_1d(u), a) / N) @ (qq * B)) / N
def dipole_env(centres, dv=2):
    x = np.arange(N, dtype=float); m = np.ones(N); rm = []
    for cc in centres: rm += [cc, (cc - dv) % N]          # the double site itself is carried by the pair; vacancy at cc - dv
    keep = np.setdiff1d(np.arange(N), rm); return x[keep], m[keep]
print('window %s N=%d: g(0) %.6f' % (WIN, N, g0), flush=True)
rng = np.random.default_rng(3); errs = []
for t in range(6):   # I1-I3 on random and dipole configurations with 1-2 pairs
    P = 1 + t % 2; n = N - 2 * P
    xon = rng.uniform(0, N, n) if t < 3 else dipole_env([5, 20][:P])[0][: n]
    mon = np.ones(len(xon)); s = rng.uniform(0, N, P) if t < 3 else np.array([5.0, 20.0][:P]); y = rng.uniform(0.02, 0.6, P)
    E_Z, E_D, Ph, Tg, FC, SD, SB, xD, mD = config_terms(xon, mon, s, y)
    i1 = abs((E_Z - FC) - (Ph + Tg + (E_Z - E_D)))
    j = np.arange(-N + 1, N); qq = np.where(np.abs(j) < N, qfun(np.minimum(np.abs(j) / N, 0.99999)), 0.0)
    SDj = Sfull(xD, mD, j); SBj = (np.exp(2j * np.pi * np.outer(j, s) / N) * (amps_pair(j, y) - 2)).sum(1)
    fld = sum(2 * np.sum(qq * (amps_pair(j, y[p:p + 1])[:, 0] - 2) * np.real(np.conj(SDj) * np.exp(2j * np.pi * j * s[p] / N))) / N for p in range(P))
    i2 = abs((E_Z - E_D) - (np.sum(qq * np.abs(SBj) ** 2) / N + fld))
    rs = sum(2 * np.sum(mD * L_y(xD - s[p], y[p])) for p in range(P))
    i3 = abs(fld - rs); errs.append((i1, i2, i3, Ph >= -1e-9, Tg >= -1e-9))
print('I1-I3 identities (max abs error over 6 configs): I1 %.1e  I2 %.1e  I3 %.1e;  P_h >= 0 and T_g >= 0 in all: %s'
      % (max(e[0] for e in errs), max(e[1] for e in errs), max(e[2] for e in errs), all(e[3] and e[4] for e in errs)), flush=True)
print('I4 Poisson: max |sum_n L_y(n + t)| over t in [0,1), y in {0.05, 0.3, 1}: %.1e' % max(abs(np.sum(L_y(np.arange(N) + t, yy))) for t in np.linspace(0, 1, 7) for yy in (0.05, 0.3, 1.0)), flush=True)
mn = np.inf
for _ in range(2000):
    A1, A2 = 2 * np.cosh(rng.uniform(0, 4, 2)); cc = rng.uniform(-1, 1)
    mn = min(mn, (A1 ** 2 - 4) + (A2 ** 2 - 4) + 2 * cc * (A1 * A2 - 4) - (A1 - A2) ** 2)
print('I5 pair block pointwise: min[(A1^2-4)+(A2^2-4)+2c(A1A2-4) - (A1-A2)^2] over 2000 samples %.2e (>= 0)' % mn, flush=True)
# S_b: the lead's global CS step on the class "shallow pair + K remote dipoles"
print('S_b (global Cauchy-Schwarz, step (b)) on: one pair at depth y on a lattice site (its own vacancy at -2) + K remote dipoles', flush=True)
for K in (0, 1, 3, 6):
    for y in (0.05, 0.1, 0.3):
        cents = [2] + [int(round(N * (i + 1) / (K + 1))) + 2 for i in range(K)]
        xenv, menv = dipole_env(cents); mon = menv.copy()
        for cc in cents[1:]: xenv = np.append(xenv, float(cc)); mon = np.append(mon, 2.0)
        E_Z, E_D, Ph, Tg, FC, SD, SB, xD, mD = config_terms(xenv, mon, np.array([2.0]), np.array([y]))
        j = np.arange(-N + 1, N); qq = np.where(np.abs(j) < N, qfun(np.minimum(np.abs(j) / N, 0.99999)), 0.0)
        Senv = Sfull(xenv, mon, j); Senv[j == 0] = 0; SBj = SB[np.abs(JA) < N]; e2 = np.exp(2j * np.pi * j * 2.0 / N)
        nrmB = np.sqrt(np.sum(qq * np.abs(SBj) ** 2) / N); nrmE = np.sqrt(np.sum(qq * np.abs(Senv) ** 2) / N)
        own = np.sum(qq * (np.abs(SBj + 2 * e2) ** 2 - 4) / N) - 0   # pair block (own double + B), j = 0 term is 0
        own = float(np.real(np.sum(qq * (np.abs(2 * e2 + SBj) ** 2 - np.abs(2 * e2) ** 2)) / N))
        W_true = (E_Z - FC); W_cs = (Ph + Tg) + own - 2 * nrmB * nrmE
        print('  K=%d y=%.2f: W (two-sided) %+.4f | step-(b) bound slack + pair block - 2||B|| ||S_env^fl|| = %+.4f  (||S_env^fl||^2 %.2f vs slack %.4f)'
              % (K, y, W_true, W_cs, nrmE ** 2, Ph + Tg), flush=True)
# T: termwise payment at integer separations
print('T  termwise kernel Lambda_y(n) = 4 g(n) + 2 L_y(n) at n = 1, 2, 3 (g(n) ~ 0 by lattice tightness):', flush=True)
for y in (0.05, 0.1, 0.3):
    print('  y=%.2f: g(1..3) %s | L_y(1..3) %s -> Lambda %s' % (y, np.round(g_of(np.array([1.0, 2.0, 3.0])), 7), np.round(L_y(np.array([1.0, 2.0, 3.0]), y), 6),
          np.round(4 * g_of(np.array([1.0, 2.0, 3.0])) + 2 * L_y(np.array([1.0, 2.0, 3.0]), y), 6)), flush=True)
# V: second order and the curvature-slack constant
def Vpp(xD, mD, s):
    j = np.arange(-N + 1, N); qq = np.where(np.abs(j) < N, qfun(np.minimum(np.abs(j) / N, 0.99999)), 0.0)
    return float(-np.real(np.sum(qq * (2 * np.pi * j / N) ** 2 * Sfull(xD, mD, j) * np.exp(-2j * np.pi * j * s / N))) / N)
xenv, menv = dipole_env([2]); y = 1e-3
E_Z, E_D, Ph, Tg, FC, SD, SB, xD, mD = config_terms(xenv, menv, np.array([2.0]), np.array([y]))
print('V  second order on the lattice dipole: Delta_B / y^2 = %.4f vs -2 V\'\'_D(s) = %.4f' % ((E_Z - E_D) / y ** 2, -2 * Vpp(xD, mD, 2.0)), flush=True)
def neg_obj(z, lam):     # maximise V''_D(s) - lam * slack(D) over D with a double at s = z[-1]
    xon = z[:-1]; s = z[-1:]
    xD = np.concatenate([xon, s]); mD = np.concatenate([np.ones(len(xon)), [2.0]])
    j = np.arange(-N + 1, N); qq = np.where(np.abs(j) < N, qfun(np.minimum(np.abs(j) / N, 0.99999)), 0.0)
    S = Sfull(xD, mD, j); E_D = float(np.sum(qq * np.abs(S) ** 2) / N)
    FC = (qfun(np.array([0.0]))[0] - gh0) * N + gN0 * float(np.sum(mD ** 2))
    return -(Vpp(xD, mD, s[0]) - lam * (E_D - FC))
best_ratio = 0.0; best_cfg = None
for trial in range(40):
    xon = (np.sort(rng.uniform(0, N, N - 2)) if trial % 2 else np.setdiff1d(np.arange(N), [5]).astype(float)[: N - 2] + rng.normal(0, 0.3, N - 2))
    z0 = np.concatenate([xon, [rng.uniform(0, N)]])
    r = minimize(lambda z: neg_obj(z, 0.5), z0, method='L-BFGS-B', options={'maxiter': 3000})
    z = r.x; xD = np.concatenate([z[:-1], z[-1:]]); mD = np.concatenate([np.ones(N - 2), [2.0]])
    vpp = Vpp(xD, mD, z[-1]); sl = -neg_obj(z, 0.0) * 0 + (lambda S: float(np.sum(np.where(np.abs(np.arange(-N + 1, N)) < N, qfun(np.minimum(np.abs(np.arange(-N + 1, N)) / N, 0.99999)), 0.0) * np.abs(S) ** 2) / N))(Sfull(xD, mD, np.arange(-N + 1, N))) - ((qfun(np.array([0.0]))[0] - gh0) * N + gN0 * float(np.sum(mD ** 2)))
    if vpp > 0 and vpp / sl > best_ratio: best_ratio, best_cfg = vpp / sl, (vpp, sl)
print('V  curvature-slack: largest V\'\'_D(s)/slack(D) found among V\'\' > 0 configurations: %.4f (V\'\' %.3f, slack %.3f) -> second-order Lemma P needs y^2 <= slack/(2 V\'\') i.e. y <= %.3f'
      % (best_ratio, *(best_cfg if best_cfg else (0, 0)), (1 / (2 * best_ratio)) ** 0.5 if best_ratio > 0 else float('inf')), flush=True)
