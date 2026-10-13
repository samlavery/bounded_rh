"""Round 3 (2): exact P_h (and T_g) cost of a density-2 stretch, periodic model, certificate v1 (same normalisation as multipair_dense2.split):
  P_h(D) = (1/N) sum_{j != 0, |j| < 3N} h-hat(j/N) |S_j|^2,   T_g(D) = (1/N) sum_j g-hat(j/N) |S_j|^2 - g_N(0) sum m^2,   S_j = sum_a m_a e(j x_a / N).
A = density-1 lattice (singletons at 0..N-1).  B(L) = doubles at 0..L-1 (mass 2L) and the remaining N - 2L singletons evenly spread on [L, N)
(the compensation).  Reports Delta = B - A, split into |alpha| < 1/2 (low band) and |alpha| >= 1/2 (Bragg region), per unit stretch length.
usage: python3 stretch_ph.py N [L,L,...]"""
import sys, numpy as np
N = int(sys.argv[1]); LS = [int(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [16, 32, 64, 128, 256]
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % N))
JA = np.arange(-3 * N + 1, 3 * N); aJ = JA / N
qA = np.where(np.abs(aJ) < 1, qfun(np.minimum(np.abs(aJ), 0.99999)), 0.0)
ghA = np.interp(np.abs(aJ), np.arange(nb + 1) * Dk, np.concatenate([yk, [0.0]]), right=0.0); hhA = qA - ghA
nz = JA != 0; low = np.abs(aJ) < 0.5
def S2(x, m):
    out = np.empty(len(JA))
    for i in range(0, len(JA), 512):
        out[i:i + 512] = np.abs(np.exp(2j * np.pi * np.outer(JA[i:i + 512], x) / N) @ m) ** 2
    return out
def parts(x, m):
    s2 = S2(x, m); ph = hhA * s2 / N
    return float(ph[nz].sum()), float(ph[nz & low].sum()), float(ph[nz & ~low].sum()), float(np.sum(ghA * s2) / N - gN0 * np.sum(m ** 2))
xA = np.arange(N, dtype=float); A = parts(xA, np.ones(N))
print('N = %d: h-hat(0) = %.5f; lattice P_h = %.4f (low %.4f, Bragg %.4f), T_g = %.4f' % (N, float(qfun(0.0) - yk[0]), *A), flush=True)
for L in LS:
    M = N - 2 * L; s = (N - L) / M
    xB = np.concatenate([np.arange(L, dtype=float), L + (np.arange(M) + 0.5) * s]); mB = np.concatenate([np.full(L, 2.0), np.ones(M)])
    B = parts(xB, mB); d = [b - a for a, b in zip(A, B)]
    print('L = %4d: Delta P_h = %+.4f (per unit length %+.5f) = low band %+.4f (%+.5f/L) + Bragg region %+.4f (%+.5f/L) | Delta T_g = %+.4f (%+.5f/L)'
          % (L, d[0], d[0] / L, d[1], d[1] / L, d[2], d[2] / L, d[3], d[3] / L), flush=True)
# other compensations of the same excess (doubles at 0..L-1, all other points on the integer lattice):
#   B2 = a contiguous vacancy block of length L at the antipode;  B3 = L vacancies evenly spread over [L, N).
for L in LS:
    rest = np.arange(L, N)
    for name, vac in (('B2 contiguous vacancies', np.arange(N // 2, N // 2 + L)), ('B3 spread vacancies', L + np.round((np.arange(L) + 0.5) * (N - L) / L).astype(int))):
        keep = rest[~np.isin(rest, vac)]; xB = np.concatenate([np.arange(L, dtype=float), keep.astype(float)]); mB = np.concatenate([np.full(L, 2.0), np.ones(len(keep))])
        assert mB.sum() == N
        B = parts(xB, mB); d = [b - a for a, b in zip(A, B)]
        print('L = %4d %-24s: Delta P_h = %+.4f (%+.5f/L) = low %+.4f (%+.5f/L) + Bragg %+.4f | Delta T_g = %+.4f (%+.5f/L)'
              % (L, name, d[0], d[0] / L, d[1], d[1] / L, d[2], d[3], d[3] / L), flush=True)
