"""Joint optimum of the global two-point certificate over windows: kappa_cert = 1 - e_inf/delta' = 1 - 2 int_0^1 q a da / g(0).
q (window datum, supported in [-1,1]) and g^ piecewise linear on the knot grid b*Dk; normalise g(0) = int g^ = 1.
LP: min int_0^1 q a  s.t.  g^ <= q at knots of [0,1),  g^ <= 0 at knots of [1, A),  q >= 0,  T_g >= 0 (g >= 0 exactly),
g^(0) <= 1,  optionally K = q-check >= 0 (T_q >= 0; a necessary condition for q = sum of autocorrelations).
usage: python3 global_joint.py A DK_DEN [Kpos]"""
import sys, numpy as np
from scipy.optimize import linprog
A, DKD = float(sys.argv[1]), int(sys.argv[2]); KPOS = len(sys.argv) > 3
Dk = 1.0 / DKD; nb = int(round(A / Dk)); nq = DKD                    # g^ knots 0..nb-1 ; q knots 0..nq-1 (q(1) = 0)
def D2(n):
    M = np.zeros((n + 1, n))
    for b in range(n + 1):
        for (o, w) in ((b - 1, 1), (b, -2), (b + 1, 1)):
            if 0 <= abs(o) < n: M[b, abs(o)] += w / Dk
    M[0] = 0; M[0, 0] = -2 / Dk
    if n > 1: M[0, 1] = 2 / Dk
    return M
def Tmat(u, n):
    u = np.asarray(u, float)[:, None]; cs = np.cos(2 * np.pi * np.arange(n + 1)[None, :] * Dk * u); cs[:, 1:] *= 2
    return -(cs @ D2(n))
P = 1 / Dk; nv = nb + nq                                              # variables: [g^ knots (nb), q knots (nq)]
ug = list(np.linspace(1e-4, P / 2, 3000))
obj = np.zeros(nv); kk = np.arange(nq) * Dk                           # int_0^1 q a for piecewise linear q with q(1) = 0
w = np.zeros(nq); w[0] = Dk ** 2 / 6
for b in range(1, nq): w[b] = Dk * kk[b]                              # exact: int hat_b(a) a da = Dk * a_b (b >= 1), Dk^2/6 (b = 0)
obj[nb:] = w
g0row = np.zeros(nv); g0row[:nb] = Dk * np.concatenate([[1.0], 2 * np.ones(nb - 1)])
for rd in range(40):
    rows, rhs = [], []
    Tg = np.zeros((len(ug), nv)); Tg[:, :nb] = Tmat(ug, nb); rows.append(-Tg); rhs.append(np.zeros(len(ug)))
    if KPOS:
        Tq = np.zeros((len(ug), nv)); Tq[:, nb:] = Tmat(ug, nq); rows.append(-Tq); rhs.append(np.zeros(len(ug)))
    C = np.zeros((nb, nv))
    for b in range(nb):
        C[b, b] = 1
        if b < nq: C[b, nb + b] = -1                                   # g^ <= q on [0,1); g^ <= 0 beyond (q = 0 there)
    rows.append(C); rhs.append(np.zeros(nb))
    r0 = np.zeros(nv); r0[0] = 1; rows.append(r0[None, :]); rhs.append([1.0])          # g^(0) <= g(0) = 1
    r = linprog(obj, A_ub=np.vstack(rows), b_ub=np.concatenate(rhs), A_eq=g0row[None, :], b_eq=[1.0],
                bounds=[(-20, 20)] * nb + [(0, 20)] * nq, method='highs', options={'presolve': False})
    x = r.x; uf = np.linspace(1e-4, P / 2, 100000); badg = uf[Tmat(uf, nb) @ x[:nb] < -1e-12]
    badq = uf[Tmat(uf, nq) @ x[nb:] < -1e-12] if KPOS else np.array([])
    if len(badg) == 0 and len(badq) == 0: break
    ug += list(badg[:: max(1, len(badg) // 200)]) + list(badq[:: max(1, len(badq) // 200)])
einf = r.fun; kap = 1 - 2 * einf
q = x[nb:]
print('JOINT A=%.2f Dk=1/%d %s: min e_inf (g(0) = 1) %.6f -> kappa_cert %.6f  (refinements %d; residual T_g %+.1e%s)'
      % (A, DKD, 'with K >= 0' if KPOS else 'q >= 0 only', einf, kap, rd, (Tmat(uf, nb) @ x[:nb]).min(),
         ', T_q %+.1e' % (Tmat(uf, nq) @ q).min() if KPOS else ''), flush=True)
print('  window q at a = 0, .1, .25, .5, .75, .9: ' + ' '.join('%.4f' % np.interp(a, np.arange(nq + 1) * Dk, np.concatenate([q, [0]])) for a in (0, .1, .25, .5, .75, .9)))
json_out = {'A': A, 'Dk': Dk, 'nb': nb, 'nq': nq, 'Kpos': KPOS, 'einf': float(einf), 'kappa': float(kap), 'g_knots': list(map(float, x[:nb])), 'q_knots': list(map(float, x[nb:]))}
import json; json.dump(json_out, open('global_joint_A%g_%s.json' % (A, 'K' if KPOS else 'noK'), 'w'))
