"""e46b -- follow-up to e46: the lower bound comes from aliasing at the window's edge jump.

e46 found low ~1.574 (n <= 64, optimised gaps ~1.04-1.09, so the separation constraint is inactive) and a best
bandlimited majorant of 1.6679 at d = 0.85, 1.6588 at d = 1.00.  The e46 'lattice limit' at d = 1.00 (1.658759)
counts the measure-zero point theta = 1/2 and is NOT a valid lattice value at spacing exactly 1.

Pencil claim to check (not yet checked): w = rho*vAM jumps at +-1/2 with edge value e = w(1/2) = 0.829374.  For a
lattice of spacing a > 1 the symbol is (1/a) sum_m w((theta+m)/a); on the overlap |theta - 1/2| <= (a-1)/2 two copies
add, giving ess sup >= (1/a)(w(1/2 - (a-1)/(2a)) + ...) -> 2e as a -> 1+.  Finite Toeplitz sections T_N satisfy
lambda_max(T_N) -> ess sup of the symbol.  Hence Lambda(d) >= 2e = 1.658748 for every d <= 1.

PRE-REGISTERED:
  (a) symbol ess sup for a in {1.002, 1.005, 1.01, 1.02, 1.05, 1.1}: predicted ~ 2e/a, i.e. 1.6554 ... 1.508.
  (b) lambda_max of N-point sections, N in {64, 256, 1024, 4096}: increases with N toward (a); I predict
      a = 1.01 reaches >= 1.64 at N = 4096.  If no section exceeds 1.62 at any a, the pencil claim is in doubt: report.
  (c) majorant convergence in K at d = 0.85: K = 8, 12, 16, 20; values non-increasing; predicted limit 1.663-1.668.
  (d) loss decomposition of the file's G = (14/13) gMaj: int_{|s|>1/2} G and int_{|s|<=1/2} (G - w).
"""
import numpy as np
exec(open("e46_sepgram.py").read().split("\nif __name__ == \"__main__\":\n")[0])

e = float(w_R8(np.array([0.5]))[0])
print(f"edge value w(1/2) = {e:.6f}, 2e = {2*e:.6f}, w(0) = {float(w_R8(np.array([0.0]))[0]):.6f}", flush=True)

print("(a) symbol ess sup (open overlap, grid excludes theta = 1/2 exactly):", flush=True)
for a in [1.002, 1.005, 1.01, 1.02, 1.05, 1.1]:
    th = np.linspace(0, 1, 200001)[1:-1] + 1e-9
    tot = np.zeros_like(th)
    for m in range(-3, 4):
        s = (th + m) / a
        tot += np.where(np.abs(s) < 0.5, w_R8(s), 0.0)
    print(f"  a={a}: ess sup {tot.max()/a:.6f}   2e/a {2*e/a:.6f}", flush=True)

print("(b) finite sections:", flush=True)
for a in [1.002, 1.005, 1.01, 1.02, 1.05]:
    row = []
    for N in [64, 256, 1024, 4096]:
        col = kern_col = k_R8(a * np.arange(N))[0]
        from scipy.linalg import toeplitz, eigh
        T = toeplitz(col)
        lam = eigh(T, eigvals_only=True, subset_by_index=[N - 1, N - 1])[0]
        row.append(f"N={N}: {lam:.6f}")
    print(f"  a={a}: " + " | ".join(row), flush=True)

print("(c) best majorant vs K at d = 0.85 and d = 1.00:", flush=True)
for d in [0.85, 1.00]:
    for K in [8, 12, 16, 20]:
        maj, mg, sc = best_majorant(w_R8, d, K=K, ngrid=1201)
        print(f"  d={d} K={K}: maj {maj:.6f} (grid {mg:.6f}, repair x{sc:.6f})", flush=True)

print("(d) loss decomposition of G = (14/13) gMaj (= w_G here):", flush=True)
from scipy.integrate import quad
inner = quad(lambda s: w_G(np.array([s]))[0] - w_R8(np.array([s]))[0], -0.5, 0.5, limit=400)[0]
total = float(k_G(np.array([0.0]))[0][0])
outer = total - quad(lambda s: w_G(np.array([s]))[0], -0.5, 0.5, limit=400)[0]
print(f"  int G = {total:.6f}; int w = 1; int_(|s|<=1/2)(G - w) = {inner:.6f}; int_(|s|>1/2) G = {outer:.6f}", flush=True)
ss = np.linspace(-0.5, 0.5, 20001)
gap = w_G(ss) - w_R8(ss)
print(f"  min_(|s|<=1/2)(G - w) = {gap.min():.6e} at s = {ss[gap.argmin()]:.4f}; G - w at s = 0: {gap[10000]:.6f}, at 1/2: {gap[-1]:.6f}",
      flush=True)
