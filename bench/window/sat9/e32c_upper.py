"""E32c: certify the e32b FAILs from above.  For any depth profile y (a pure mixture), the dual gives
  D(s) <= U(y) := T_g + 4 Re<S_B(y), V> + ||P_F S_B(y)||^2   (P_F = projection onto F = span e(al t_n)).
Evaluate U at the adversarial depths y* returned by the e32b maximiser and at a few other profiles; U < 0 => D < 0 certified."""
import json, numpy as np
exec(open('e32b_maxmin.py').read().split("if __name__ == '__main__':")[0])
def U_of(s, y):
    s = np.sort(np.asarray(s, float)); P = len(s); a = (s[-1] - s[0]) / (P - 1)
    t = np.unique(np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9))
    E = np.exp(2j * np.pi * np.outer(al, s)); B = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2
    SB = (B * E).sum(1); V = E.sum(1)
    Et = np.exp(2j * np.pi * np.outer(al, t)); b = np.real(W2 @ (SB[:, None] * np.conj(Et)))
    G = Kmat(t[:, None] - t[None, :]); proj = float(b @ np.linalg.pinv(G, rcond=1e-12) @ b)
    return Tg(s) + 4 * float(W2 @ np.real(np.conj(V) * SB)) + proj, float(W2 @ np.abs(SB) ** 2), proj
cfgs = []
for a in (0.6, 0.7, 0.76, 0.8, 0.9):
    for P in (12, 24, 48): cfgs.append(('lattice a=%.2f P=%d' % (a, P), a * np.arange(P)))
for P in (12, 16, 24, 32):
    c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
for name, s in cfgs:
    D, ystar, T = D_of(s); s2 = np.sort(s)
    U1, full1, proj1 = U_of(s2, ystar)
    print('%-22s D(lower, e32b) %+12.2f | U at y* %+12.2f (||S_B||^2 %.3g, ||P_F S_B||^2 %.3g, captured %.4f) -> %s'
          % (name, D, U1, full1, proj1, proj1 / full1, 'FAIL certified' if U1 < 0 else 'not certified'), flush=True)
