"""ROUTE3_B1 (bridge-port): the kernel-mass amplification of the fourth-moment off-diagonal class R, on actual prime powers.
Products N = a*b (a, b prime powers <= X), F(N) = sum_{ab=N} Lambda(a)Lambda(b) (no leg geometry O4 >= 0: it only reweights legs).
Per dyadic scale bin of N: diagonal D = T * sum F(N)^2/N  (kernel at Delta = 0 is T);
off-diagonal over pairs N1 != N2 in the bin with x = T*log(N2/N1) <= R:
  signed S = sum F F / sqrt(N1 N2) * k(Delta),  positive part P (k^+ only), absolute A (|k|),  k(Delta) = (sin 2T Delta - sin T Delta)/Delta.
Prints S/D, P/D, A/D against m/T.  Usage: amplify.py X T R"""
import sys, math, numpy as np
X, T, R = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
sieve = np.ones(X + 1, bool); sieve[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
pp = []
for p in np.nonzero(sieve)[0]:
    q = int(p)
    while q <= X: pp.append((q, math.log(p))); q *= int(p)
F = {}
for a, la in pp:
    for b, lb in pp:
        N = a * b; F[N] = F.get(N, 0.0) + la * lb
Ns = np.array(sorted(F)); Fv = np.array([F[n] for n in Ns]); lN = np.log(Ns.astype(float))
bins = np.arange(math.floor(math.log2(T)) - 2, math.ceil(math.log2(Ns[-1])) + 1)
D = np.zeros(len(bins)); S = np.zeros(len(bins)); P = np.zeros(len(bins)); A = np.zeros(len(bins))
bidx = np.floor(np.log2(Ns)).astype(int) - bins[0]
for i in range(len(Ns)):
    D[bidx[i]] += T * Fv[i] ** 2 / Ns[i]
    hi = np.searchsorted(lN, lN[i] + R / T, side="right")
    if hi <= i + 1: continue
    d = lN[i + 1:hi] - lN[i]
    k = (np.sin(2 * T * d) - np.sin(T * d)) / d
    w = 2 * Fv[i] * Fv[i + 1:hi] / np.sqrt(Ns[i] * Ns[i + 1:hi].astype(float))
    S[bidx[i]] += (w * k).sum(); P[bidx[i]] += (w * np.maximum(k, 0)).sum(); A[bidx[i]] += (w * np.abs(k)).sum()
print(f"X={X} T={T:g} R={R:g} products={len(Ns)}  (scale bin m = 2^b; m/T shown)")
print(f"{'m/T':>9} {'S/D':>8} {'P/D':>8} {'A/D':>8}")
for j, b in enumerate(bins):
    if D[j] > 0: print(f"{2.0**b / T:9.3f} {S[j]/D[j]:8.3f} {P[j]/D[j]:8.3f} {A[j]/D[j]:8.3f}")
