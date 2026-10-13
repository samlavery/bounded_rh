"""Multi-pair shallow, extreme cases (periodic model, certificate v1, N = 64):
  (a) a block of P consecutive equal-depth pairs (P = 8, 16, 24, 32), vacancies contiguous (far side) or spread;
  (b) all mass in pairs: N/2 equal-depth pairs at spacing 2;
  (c) mixed: a block of 16 pairs with depths alternating shallow/deep, and a shallow block with one deep pair in the middle.
For each: W per defect (units of 2 delta' = g(0); W = LP_total/2, LP_total = E(Z) - F_C(D(Z))) at the lattice positions and
after relaxing ALL positions (pair centres included), and the split of LP_total = P_h + T_g + fields + B-B form."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', 64"))
JA = np.arange(-3 * N + 1, 3 * N); aJ = JA / N
qA = np.where(np.abs(aJ) < 1, qfun(np.minimum(np.abs(aJ), 0.99999)), 0.0)
ghA = np.interp(np.abs(aJ), np.arange(nb + 1) * Dk, np.concatenate([yk, [0.0]]), right=0.0); hhA = qA - ghA
def split(xon, s, ys):
    xD = np.concatenate([xon, s]); mD = np.concatenate([np.ones(len(xon)), np.full(len(s), 2.0)])
    SD = np.exp(2j * np.pi * np.outer(JA, xD) / N) @ mD
    SB = (np.exp(2j * np.pi * np.outer(JA, s) / N) * (2 * np.cosh(2 * np.pi * np.outer(JA, ys) / N) - 2)).sum(1)
    nz = JA != 0
    Ph = float(np.sum(hhA[nz] * np.abs(SD[nz]) ** 2) / N); Tg = float(np.sum(ghA * np.abs(SD) ** 2) / N) - gN0 * float(np.sum(mD ** 2))
    BB = float(np.sum(qA * np.abs(SB) ** 2) / N); FLD = 2 * float(np.sum(qA * np.real(np.conj(SD) * SB)) / N)
    return Ph, Tg, FLD, BB
def run(xon, s, ys, label):
    n1 = len(xon); P = len(s); z = np.concatenate([xon, s])
    Wl = sum(split(xon, s, ys)) / 2
    r = minimize(lambda zz: d_and_grad(zz, n1, 0, P, ys), z, jac=True, method='L-BFGS-B', options={'maxiter': 6000})
    xr, sr = r.x[:n1], r.x[n1:]; sp = split(xr, sr, ys); Wr = sum(sp) / 2
    print('  %-46s W/defect (units 2d\'): lattice %+.5f relaxed %+.5f | relaxed split per defect: P_h %+.4f T_g %+.4f fields %+.4f B-B %+.4f'
          % (label, Wl / P / g0, Wr / P / g0, *(v / 2 / P / g0 for v in sp)), flush=True)
    return Wr / P / g0
worst = (np.inf, None)
for y in (0.1, 0.2, 0.3, 0.4, 0.6, 0.8):
    print('y = %.1f' % y, flush=True)
    for P in (8, 16, 24, 32):
        for spread in (False, True):
            if P == 32 and spread: continue
            cen = np.arange(P, dtype=float)
            if spread:
                vac = set(np.round(np.linspace(P, N, P, endpoint=False) + (N - P) / (2 * P)).astype(int) % N)
            else:
                vac = set(range(P, 2 * P))
            xon = np.array([t for t in range(P, N) if t not in vac], float)
            if len(xon) + 2 * P != N: continue
            w = run(xon, cen, np.full(P, y), '(a) block P=%d, vacancies %s' % (P, 'spread' if spread else 'contiguous'))
            if w < worst[0]: worst = (w, ('a', y, P, spread))
    cen = np.arange(0, N, 2, dtype=float); w = run(np.array([]), cen, np.full(N // 2, y), '(b) all mass in pairs, spacing 2')
    if w < worst[0]: worst = (w, ('b', y))
    for deep in (1.0, 1.5):
        P = 16; cen = np.arange(P, dtype=float); vac = set(range(P, 2 * P)); xon = np.array([t for t in range(P, N) if t not in vac], float)
        ys = np.where(np.arange(P) % 2 == 0, y, deep); w = run(xon, cen, ys, '(c) block 16, depths alternate %.1f/%.1f' % (y, deep))
        if w < worst[0]: worst = (w, ('c-alt', y, deep))
        ys = np.full(P, y); ys[P // 2] = deep; w = run(xon, cen, ys, '(c) block 16 at %.1f, one deep %.1f in the middle' % (y, deep))
        if w < worst[0]: worst = (w, ('c-one', y, deep))
print('WORST relaxed W per defect: %+.5f at %s' % worst, flush=True)
