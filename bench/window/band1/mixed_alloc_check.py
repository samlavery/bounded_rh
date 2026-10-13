"""Mixed-depth class (i): slack-allocation check.  Pair p has radius L_p by depth class (a: L=2, b: L=4, c: L=8), non-cluster weight
v_p(u) = clip((L_p + 1/2 - u), 0, 1) and cluster weight c_p(u) = 0.8 v_p(u) + CW_p (L_p/u)^2 [u >= L_p + 1/2]  (CW = 0.15, 0.15, 0.14).
Admissible configurations: |s_p - s_q| >= L_p + L_q.  Checks sup_x sum_p v_p <= 1 and sup_x sum_p c_p <= 1 over random and adversarial
(minimal-separation) class sequences."""
import numpy as np
LS = {'a': 2.0, 'b': 4.0, 'c': 8.0}; CWS = {'a': 0.15, 'b': 0.15, 'c': 0.14}
def v(u, L): return np.clip(L + 0.5 - u, 0.0, 1.0)
def c(u, L, cw): return 0.8 * v(u, L) + np.where(u >= L + 0.5, cw * (L / np.maximum(u, L)) ** 2, 0.0)
rng = np.random.default_rng(7); worst_v = worst_c = 0.0; wc_conf = None
seqs = [''.join(rng.choice(list('abc'), 60)) for _ in range(300)] + ['a' * 60, 'b' * 60, 'c' * 60, 'ac' * 30, 'ab' * 30, 'bc' * 30, 'aac' * 20, 'cca' * 20, 'abcba' * 12]
for sq in seqs:
    L = np.array([LS[t] for t in sq]); CW = np.array([CWS[t] for t in sq])
    s = np.concatenate([[0.0], np.cumsum(L[:-1] + L[1:])])                        # minimal separations
    xs = np.linspace(s[20], s[40], 20001)
    U = np.abs(xs[:, None] - s[None, :])
    sv = v(U, L[None, :]).sum(1).max(); scl = c(U, L[None, :], CW[None, :]).sum(1).max()
    if sv > worst_v: worst_v = sv
    if scl > worst_c: worst_c, wc_conf = scl, sq[18:42]
print('sup sum v = %.4f ; sup sum c = %.4f (worst class pattern around the max: %s)' % (worst_v, worst_c, wc_conf))
