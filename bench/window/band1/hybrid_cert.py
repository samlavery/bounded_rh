"""Hybrid certificate for D with off-line pairs (option (i)).
E = int [S_on; S_off]^* Q [S_on; S_off],  Q = qf [[1,1],[1,1]],  S_off = sum_p 2 cosh(2 pi a y_p) e(a s_p).
Split Q = M + G:  M(a) PSD (2x2 over the classes on / off; cosh-safe, bounded below by its DC term);
G = [[g^_on, g^_x], [g^_x, g^_oo]] termwise:  on-on at real arguments (dips allowed, g_on >= 0 exactly via the periodic
trigonometric check);  on-off kernel  int g^_x cosh(2 pi a y) cos(2 pi a u) >= 0  and off-off kernel
int g^_oo cosh(2 pi a y) cosh(2 pi a y') cos(2 pi a u) >= 0  for all depths on the grid Y = [0, YMAX] (cosh-safety).
First-order density expansion (exact; the rho^2 term is [1,-1] M [1,-1]^T >= 0):
   delta' = g_on(0)/2 with g_on(0) >= g^_on(0);   every pair at depth y needs
   g^_on(0) - g^_x(0) + int g^_oo cosh^2(2 pi a y) da >= g_on(0).
PSD is imposed by linear cuts (24 angles) at knots and midpoints: a RELAXATION, so the LP value is an upper bound for the
family at that depth grid.  Mode 'R8': fixed window, max g_on(0).  Mode 'joint': window q piecewise linear (q >= 0,
K = q-check >= 0) and certificate together, g_on(0) = 1, min int_0^1 q a;  kappa_cert = 1 - 2 int q a.
usage: python3 hybrid_cert.py MODE A YMAX"""
import sys, json, time, numpy as np
from scipy.optimize import linprog
MODE, A, YMAX = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]); TAIL = (sys.argv[4] != 'notail') if len(sys.argv) > 4 else True; DROP = sys.argv[5] if len(sys.argv) > 5 else ''
exec(open('global_cert.py').read().split("def b3(t):")[0].replace("WIN = sys.argv[1]; DT = float(sys.argv[2])", "WIN = 'R8'; DT = 0.495338"))
EINF_R8 = 0.159784; t0 = time.time()
Dk = 1 / 32; nb = int(round(A / Dk)); P = 1 / Dk; JOINT = MODE == 'joint'; nq = 32 if JOINT else 0
Y = [0.0] if YMAX == 0 else list(np.linspace(0, YMAX, 5))
NV = 3 * nb + nq; ion, ix, ioo, iq = 0, nb, 2 * nb, 3 * nb
def D2m(n):
    M = np.zeros((n + 1, n))
    for b in range(n + 1):
        for (o, w) in ((b - 1, 1), (b, -2), (b + 1, 1)):
            if 0 <= abs(o) < n: M[b, abs(o)] += w / Dk
    M[0] = 0; M[0, 0] = -2 / Dk
    if n > 1: M[0, 1] = 2 / Dk
    return M
D2 = D2m(nb); D2q = D2m(nq) if JOINT else None
def interp_mat(a, n):
    a = np.abs(np.asarray(a, float)); M = np.zeros((len(a), n)); t = a / Dk; i = np.floor(t).astype(int); fr = t - i
    for r in range(len(a)):
        if i[r] < n: M[r, i[r]] += 1 - fr[r]
        if i[r] + 1 < n: M[r, i[r] + 1] += fr[r]
    return M
upg = np.linspace(1e-3, P / 2, 1500); ugr = np.arange(0, 30, 0.04)
af = np.arange(0, A + 1e-12, Dk / 16); Hf = interp_mat(af, nb); wtr = np.full(len(af), af[1] - af[0]); wtr[0] /= 2; wtr[-1] /= 2
def kernel_rows(weight):        # rows over a g^ block: (int g^ weight cos(2 pi a u)) at u in ugr, two-sided
    C = np.cos(2 * np.pi * np.outer(ugr, af)); return 2 * (C * (weight * wtr)[None, :]) @ Hf
def asym_rows(weight_at_knots):  # periodic leading term T(u) >= 0 for g^ * weight (kinks of g^ weighted)
    u = upg[:, None]; cs = np.cos(2 * np.pi * np.arange(nb + 1)[None, :] * Dk * u); cs[:, 1:] *= 2
    return -(cs * weight_at_knots[None, :]) @ D2
rows, rhs = [], []
def add(block_rows, block, b=None):
    R = np.zeros((block_rows.shape[0], NV)); R[:, block:block + block_rows.shape[1]] = block_rows; rows.append(-R); rhs.append(np.zeros(len(R)) if b is None else -b)
add(asym_rows(np.ones(nb + 1)), ion)                                      # g_on >= 0 (exact periodic form)
g0 = Dk * np.concatenate([[1.0], 2 * np.ones(nb - 1)]); e0 = np.zeros(nb); e0[0] = 1
r = np.zeros(NV); r[ion:ion + nb] = g0 - e0; rows.append(-r[None, :]); rhs.append([0.0])          # g_on(0) >= g^_on(0)
kn = np.arange(nb) * Dk
for y in Y:                                                               # on-off cosh-safety
    if DROP in ('onoff', 'both') and y > 0: continue
    w = np.cosh(2 * np.pi * af * y); add(kernel_rows(w), ix)
    if TAIL or y == 0: add(asym_rows(np.cosh(2 * np.pi * np.arange(nb + 1) * Dk * y)), ix)
for i1, y1 in enumerate(Y):                                               # off-off cosh-safety
    for y2 in Y[i1:]:
        if DROP in ('offoff', 'both') and (y1 > 0 or y2 > 0): continue
        w = np.cosh(2 * np.pi * af * y1) * np.cosh(2 * np.pi * af * y2); add(kernel_rows(w), ioo)
        if TAIL or (y1 == 0 and y2 == 0): add(asym_rows(np.cosh(2 * np.pi * np.arange(nb + 1) * Dk * y1) * np.cosh(2 * np.pi * np.arange(nb + 1) * Dk * y2)), ioo)
for y in Y:                                                               # pair charge >= the double's
    r = np.zeros(NV); r[ion] += 1; r[ix] -= 1; r[ioo:ioo + nb] += 2 * (np.cosh(2 * np.pi * af * y) ** 2 * wtr) @ Hf; r[ion:ion + nb] -= g0
    rows.append(-r[None, :]); rhs.append([0.0])
apts = np.unique(np.concatenate([kn, kn + Dk / 2])); apts = apts[apts < A]; Ha = interp_mat(apts, nb)
qfix = np.where(apts < 1, qfun(np.minimum(apts, 0.99999)), 0.0)
Hq = interp_mat(np.minimum(apts, 1.0), nq) * (apts < 1)[:, None] if JOINT else None
for th in np.linspace(0, np.pi, 24, endpoint=False):                      # PSD cuts: c^2 M11 + 2cs M12 + s^2 M22 >= 0
    c, s = np.cos(th), np.sin(th); R = np.zeros((len(apts), NV))
    R[:, ion:ion + nb] = -c * c * Ha; R[:, ix:ix + nb] = -2 * c * s * Ha; R[:, ioo:ioo + nb] = -s * s * Ha
    tot = c * c + 2 * c * s + s * s
    if JOINT: R[:, iq:iq + nq] = tot * Hq; rows.append(-R); rhs.append(np.zeros(len(apts)))
    else: rows.append(-R); rhs.append(tot * qfix)
if JOINT:
    u = upg[:, None]; cs = np.cos(2 * np.pi * np.arange(nq + 1)[None, :] * Dk * u); cs[:, 1:] *= 2
    add(-(cs @ D2q), iq)                                                  # K = q-check >= 0
Aub = np.vstack(rows); bub = np.concatenate([np.atleast_1d(v) for v in rhs])
cobj = np.zeros(NV)
if JOINT:
    wq = np.zeros(nq); wq[0] = Dk ** 2 / 6; wq[1:] = Dk * np.arange(1, nq) * Dk; cobj[iq:iq + nq] = wq
    Aeq = np.zeros((1, NV)); Aeq[0, ion:ion + nb] = g0; beq = [1.0]
    bounds = [(-30, 30)] * (3 * nb) + [(0, 30)] * nq
else:
    cobj[ion:ion + nb] = -g0; Aeq = None; beq = None; bounds = [(-30, 30)] * (3 * nb)
res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs', options={'presolve': False})
if res.x is None: print('LP failed:', res.message); sys.exit(1)
x = res.x
if JOINT: kap = 1 - 2 * res.fun; dlt = 0.5
else: g0v = -res.fun; dlt = g0v / 2; kap = 1 - EINF_R8 / dlt if dlt > 1e-9 else float('-inf')
# exact PSD check of the solution (min eigenvalue of M on a fine grid) and pair-charge profile at finer depths
ff = np.arange(0, A, Dk / 8); Hff = interp_mat(ff, nb)
qv = (interp_mat(np.minimum(ff, 1.0), nq) * (ff < 1)[:, None]) @ x[iq:iq + nq] if JOINT else np.where(ff < 1, qfun(np.minimum(ff, 0.99999)), 0.0)
M11 = qv - Hff @ x[ion:ion + nb]; M12 = qv - Hff @ x[ix:ix + nb]; M22 = qv - Hff @ x[ioo:ioo + nb]
lmin = np.min(0.5 * (M11 + M22) - np.sqrt(0.25 * (M11 - M22) ** 2 + M12 ** 2))
gon0 = g0 @ x[ion:ion + nb]
prof = []
for y in sorted(set([0.0, YMAX / 2, YMAX, 2 * YMAX, 4 * YMAX] if YMAX > 0 else [0.0, 0.05, 0.1])):
    ch = x[ion] - x[ix] + 2 * (np.cosh(2 * np.pi * af * y) ** 2 * wtr) @ Hf @ x[ioo:ioo + nb]
    prof.append('y=%.3f: %.4f' % (y, ch / gon0))
print(('' if TAIL else '[cosh-safety only for |u| <= 30] ') + ('[dropped: %s] ' % DROP if DROP else '') + 'HYBRID %s A=%.1f depth grid [0, %.3f]: delta\' %.6f (%s) -> kappa_cert %.6f | min eig M %+.1e | pair charge / double charge: %s  (%.0fs)'
      % (MODE, A, YMAX, dlt, ('g_on(0) normalised' if JOINT else '%.2f%% of R8 delta_true' % (100 * dlt / 0.495338)), kap, lmin, ', '.join(prof), time.time() - t0), flush=True)
json.dump({'mode': MODE, 'A': A, 'ymax': YMAX, 'kappa': kap, 'x': list(map(float, x))}, open('hybrid_%s_A%g_y%g%s.json' % (MODE, A, YMAX, ('' if TAIL else '_notail') + ('_drop' + DROP if DROP else '')), 'w'))
