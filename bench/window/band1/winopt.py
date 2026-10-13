"""Window optimisation for the single-defect objective  kappa_D(q) = 1 - int_0^1 q a da / delta(q),
delta(q) = Delta_1(q) / 2N,  Delta_1 = min over relaxations of d = sum_{0<j<N} q(j/N) |S_j|^2 for ONE double in N-2 simples
on the circle of length N (L1).  Grid form: kappa_D,N = 1 - 2 (TGT/N^2) / (Delta_1/N), TGT = sum_j q(j/N) j.

Pieces:
  delta1(q)          L1 solver (double fixed at 0; multistart from the unrelaxed symmetric chain; analytic gradient)
  family             25-mode window f = (1/A)(cos(sqrt2 t) + sum_{j<=24} c_j cos(2 pi j t)), qf = z^T M(h) z, z = (1, c);
                     maximise kappa_D over c by L-BFGS with the Danskin gradient d Delta_1/d q_j = |S_j*|^2
  typed_lp(q)        validation: the window-only marked LP over all types (k doubles, t triples) -> min p (c0 free),
                     the c0 = 1 value 1 - TGT max_c (1-p_c)/d_c, and the per-type energies d_min(k)/k
  general(N)         q >= 0 free on the grid: column generation on the dual side (= the full band-1 LP with pi = -q)
  farfield(q)        E(K) = Delta_1 with only the K nearest simples on each side relaxed; displacement profile
usage: python3 winopt.py MODE N ...   (MODE in family | general | check | far)"""
import sys, json, math, time
import numpy as np
from scipy.optimize import minimize, linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
S2 = math.sqrt(2.0); KF = 24
R8C = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], KF)
rng = np.random.default_rng(5)

def Mmats(hs, K=KF, w0=S2):
    """M(h) with qf(h) = z^T M(h) z for z = (1, c_1..c_K); same closed form as dual.make_qf"""
    n = K + 1; w = np.concatenate([[w0], 2 * np.pi * np.arange(1, n)]); A = 2 * math.sin(w0 / 2) / w0
    h = np.asarray(hs, float)
    def I(nu, theta):
        l = 1 - h; ch = -h / 2; x = nu * l / 2
        s = np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / np.where(np.abs(x) < 1e-12, 1.0, x))
        return l * np.cos(nu * ch + theta) * s
    M = np.zeros((len(h), n, n))
    for i in range(n):
        for k in range(n):
            M[:, i, k] = 0.5 * (I(w[i] + w[k], w[k] * h) + I(w[i] - w[k], -w[k] * h)) / A ** 2
    M = 0.5 * (M + M.transpose(0, 2, 1)); M[h >= 1] = 0
    return M

def unrelaxed(N, dv=2):
    """lattice dipole: double at 0, vacancy at -dv, simples on every other integer (centred on the circle)"""
    a = np.arange(-(N // 2) + 1, N // 2 + 1); return a[(a != 0) & (a != -dv)].astype(float)

def energy(y, q, N, J, grad=True, free=None, yfix=None):
    """one double at 0 (amplitude 2), simples at y; returns d and gradient in y (masked to `free`)"""
    yy = y if free is None else np.where(free, 0, yfix)
    if free is not None: yy = yy.copy(); yy[free] = y
    x = np.concatenate([[0.0], yy]); m = np.concatenate([[2.0], np.ones(len(yy))])
    E = np.exp(2j * np.pi * np.outer(J, x) / N); S = E @ m; d = float(q @ np.abs(S) ** 2)
    if not grad: return d
    g = 2 * np.real((q * np.conj(S))[:, None] * E * (2j * np.pi * J[:, None] / N)).sum(0)[1:] * 1.0
    return d, (g if free is None else g[free])

def delta1(q, N, y0=None, starts=4, dvs=range(1, 9), ret_dv=False):
    J = np.arange(1, N); best = (np.inf, None, None)
    inits = ([(y0, -1)] if y0 is not None else []) + [(unrelaxed(N, dv), dv) for dv in dvs if dv < N // 2]
    inits += [(unrelaxed(N, 2) + rng.normal(0, s, N - 2), 2) for s in [0.05, 0.15][:max(0, starts - 2)]]
    for z0, dv in inits:
        r = minimize(lambda y: energy(y, q, N, J), z0, jac=True, method='L-BFGS-B', options={'maxiter': 3000, 'gtol': 1e-10})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy(), dv)
    if ret_dv: return best
    best = best[:2]
    d, y = best; x = np.concatenate([[0.0], y]); m = np.concatenate([[2.0], np.ones(len(y))])
    S2v = np.abs(np.exp(2j * np.pi * np.outer(J, x) / N) @ m) ** 2
    return d, y, S2v

# ---------------------------------------------------------------- typed LP (validation), all types incl. triples
def datum_t(z, q, N, J, n1, k, t):
    n = n1 + k + t; x = z[:n]
    E = np.exp(2j * np.pi * np.outer(J, x) / N)
    m = np.concatenate([np.ones(n1), np.full(k, 2.0), np.full(t, 3.0)])
    S = E @ m; d = float(q @ np.abs(S) ** 2)
    g = 2 * np.real((q * np.conj(S))[:, None] * E * m[None, :] * (2j * np.pi * J[:, None] / N)).sum(0)
    return d, g

def dmin_type(q, N, k, t, starts):
    J = np.arange(1, N); n1 = N - 2 * k - 3 * t; n = n1 + k + t; best = (np.inf, None)
    if n1 < 0: return best
    mlist = np.array([1] * n1 + [2] * k + [3] * t, float)
    for s in range(starts):
        if t == 0 and k > 0 and s % 6 == 3:   # lattice dipoles: doubles on integer sites, a vacancy dv sites below each
            dv = int(rng.integers(1, 4)); dsites = np.round(np.linspace(0, N, k, endpoint=False)).astype(int) % N
            vac = (dsites - dv) % N; rest = np.setdiff1d(np.arange(N), np.concatenate([dsites, vac]))
            if len(np.unique(np.concatenate([dsites, vac]))) == 2 * k and len(rest) == n1:
                x0 = np.concatenate([rest, dsites]).astype(float) + rng.normal(0, 0.01 * (s // 6), n)
                r = minimize(lambda z: datum_t(z, q, N, J, n1, k, t), x0, jac=True, method='L-BFGS-B')
                if r.fun < best[0]: best = (float(r.fun), r.x.copy())
                continue
        if s % 3 == 0:   # evenly spread defects in a mass-uniform chain
            sl = np.round(np.linspace(0, n, k + t, endpoint=False)).astype(int); ty = np.zeros(n, int); ty[sl] = [2] * k + [3] * t
            mm = np.where(ty == 0, 1, ty).astype(float); gaps = (mm + np.roll(mm, -1)) / 2; pos = np.concatenate([[0], np.cumsum(gaps)[:-1]])
            idx = np.empty(n, int); idx[ty == 0] = np.arange(n1); idx[np.where(ty == 2)[0]] = n1 + np.arange(k); idx[np.where(ty == 3)[0]] = n1 + k + np.arange(t)
            x0 = np.empty(n); x0[idx] = pos + rng.normal(0, 0.03 * (s // 3), n)
        elif s % 3 == 1:
            order = rng.permutation(n); mm = mlist[order]; gaps = (mm + np.roll(mm, -1)) / 2
            pos = np.concatenate([[0], np.cumsum(gaps)[:-1]]); x0 = np.empty(n); x0[order] = pos + rng.normal(0, 0.15, n)
        else:
            x0 = rng.uniform(0, N, n)
        r = minimize(lambda z: datum_t(z, q, N, J, n1, k, t), x0, jac=True, method='L-BFGS-B')
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    return best

def single_minima(q, N, starts):
    """distinct local minima of the one-double energy: dipole inits (vacancy distance 1..N/2-1) plus random starts;
    returned in dmin_type order (simples, then the double)"""
    J = np.arange(1, N); out = []
    inits = [unrelaxed(N, dv) for dv in range(1, N // 2)] + [unrelaxed(N, int(rng.integers(1, 4))) + rng.normal(0, 0.2, N - 2) for _ in range(starts // 2)]
    inits += [rng.uniform(-N / 2, N / 2, N - 2) for _ in range(starts - starts // 2)]
    for z0 in inits:
        r = minimize(lambda y: energy(y, q, N, J), z0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        if all(abs(r.fun - o[0]) > 1e-9 for o in out): out.append((float(r.fun), np.concatenate([r.x, [0.0]])))
    return out

def typed_lp(q, N, starts=60, tmax=None):
    J = np.arange(1, N); TGT = float(q @ J)
    types = [(k, t) for t in range(0, (N // 3 if tmax is None else tmax) + 1) for k in range(0, (N - 3 * t) // 2 + 1) if (k, t) != (0, 0)]
    dm = {kt: dmin_type(q, N, kt[0], kt[1], starts) for kt in types}
    P = np.array([1.0] + [(N - 2 * k - 3 * t) / N for (k, t) in types]); D = np.array([0.0] + [dm[kt][0] for kt in types])
    r = linprog(P, A_ub=D[None, :], b_ub=[TGT], A_eq=np.ones((1, len(P))), b_eq=[1.0], bounds=[(0, None)] * len(P), method='highs')
    ratio = max(((1 - P[i]) / D[i], types[i - 1]) for i in range(1, len(P)))
    per_def = {'%d,%d' % kt: dm[kt][0] / (kt[0] + 1.5 * kt[1]) for kt in types}   # energy per double-equivalent (2 non-simple zeros)
    return float(r.fun), 1 - TGT * ratio[0], ratio[1], per_def, dm

# ---------------------------------------------------------------- far field
def energy_all(x, q, N, J, free, xfix):
    """double at position 0 of the vector (amplitude 2), simples after it; only `free` coordinates vary"""
    xx = xfix.copy(); xx[free] = x
    m = np.concatenate([[2.0], np.ones(len(xx) - 1)])
    E = np.exp(2j * np.pi * np.outer(J, xx) / N); S = E @ m; d = float(q @ np.abs(S) ** 2)
    g = 2 * np.real((q * np.conj(S))[:, None] * E * m[None, :] * (2j * np.pi * J[:, None] / N)).sum(0)
    return d, g[free]

def farfield(q, N, Ks):
    """relaxation locality around the optimal dipole: E(K) = energy with the double and the 2K simples nearest the dipole
    centre free, every other simple frozen on its lattice site"""
    J = np.arange(1, N); d1, y1, dv = delta1(q, N, ret_dv=True)
    if dv < 0: dv = 2
    base = np.concatenate([[0.0], unrelaxed(N, dv)]); full = np.concatenate([[0.0], y1])
    rank = np.argsort(np.argsort(np.abs(base[1:] + dv / 2))); out = []
    d0 = energy_all(base, q, N, J, np.ones(N - 1, bool), base)[0]
    for K in Ks:
        free = np.concatenate([[True], rank < 2 * K])
        r = minimize(lambda x: energy_all(x, q, N, J, free, base), base[free], jac=True, method='L-BFGS-B', options={'maxiter': 5000, 'gtol': 1e-11})
        out.append((K, float(r.fun)))
    sh = full - full[0]
    order = np.argsort(np.abs(base[1:] + dv / 2)); disp = [(float(base[1 + i]), float(sh[1 + i] - base[1 + i])) for i in order]
    return d1, d0, out, disp, dv

# ---------------------------------------------------------------- family optimisation
def family(N, c0=None, iters=300, ngrid=241):
    """maximise kappa_D,N over the 25-mode family subject to qf(a) >= 0 on a fine grid of [0, 1)"""
    J = np.arange(1, N); M = Mmats(J / N); Mg = Mmats(np.linspace(0, 0.999, ngrid)); state = {'y': None}
    def obj(c):
        z = np.concatenate([[1.0], c]); q = np.einsum('jik,i,k->j', M, z, z); TGT = float(q @ J)
        d, y, S2v = delta1(q, N, y0=state['y'], starts=2, dvs=range(1, 5)); state['y'] = y
        dq = 2 * np.einsum('jik,k->ji', M, z); dT = J @ dq; dD = S2v @ dq
        return TGT / d, ((dT * d - TGT * dD) / d ** 2)[1:]
    cons = lambda c: np.einsum('jik,i,k->j', Mg, np.concatenate([[1.0], c]), np.concatenate([[1.0], c]))
    cjac = lambda c: (2 * np.einsum('jik,k->ji', Mg, np.concatenate([[1.0], c])))[:, 1:]
    c_init = R8C.copy() if c0 is None else c0
    r = minimize(obj, c_init, jac=True, method='SLSQP', constraints=[{'type': 'ineq', 'fun': cons, 'jac': cjac}],
                 options={'maxiter': iters, 'ftol': 1e-12})
    rho, _ = obj(r.x); return 1 - 2 * rho / N, r.x, float(cons(r.x).min())

def q_family(c, N):
    J = np.arange(1, N); return make_qf(np.asarray(c, float))(J / N)

def kappa_D(q, N):
    J = np.arange(1, N); d, _, _ = delta1(q, N, starts=4); return 1 - 2 * (float(q @ J) / N ** 2) / (d / N), d / N

def cont_kappa(c, dN):
    from scipy.integrate import quad
    qf = make_qf(np.asarray(c, float)); I1 = quad(lambda a: float(qf(np.array([a]))[0]) * a, 0, 1, limit=400)[0]
    I0 = quad(lambda a: float(qf(np.array([a]))[0]), 0, 1, limit=400)[0]
    return I1, I0, 1 - 2 * I1 / dN

if __name__ == '__main__':
    mode = sys.argv[1]; N = int(sys.argv[2]); t0 = time.time()
    if mode == 'family':
        out = {}
        kR8, dR8 = kappa_D(q_family(R8C, N), N)
        print('N=%d R8: kappa_D,N %.7f  Delta_1/N %.6f' % (N, kR8, dR8), flush=True)
        starts = [('R8', R8C), ('zero', np.zeros(KF))] + [('rand%d' % i, R8C + rng.normal(0, 0.05, KF)) for i in range(3)]
        best = (-1, None, None)
        for name, c0 in starts:
            k, c, qmin = family(N, c0)
            kk, dN = kappa_D(q_family(c, N), N)
            print('  start %-6s -> kappa_D,N %.7f (re-evaluated %.7f, Delta_1/N %.6f, min qf on grid %+.2e)  (%.0fs)' % (name, k, kk, dN, qmin, time.time() - t0), flush=True)
            if kk > best[0] and qmin > -1e-7: best = (kk, c, name)
        kk, c, name = best; _, dN = kappa_D(q_family(c, N), N); I1, I0, kc = cont_kappa(c, dN)
        print('FAMILY BEST (start %s): kappa_D,N %.7f; continuum int q a / int q = %.6f, kappa_D,cont %.7f; c = %s'
              % (name, kk, I1 / I0 / 2, kc, np.array2string(c, precision=5, max_line_width=250)), flush=True)
        json.dump({'N': N, 'R8': [kR8, dR8], 'best': kk, 'cont': kc, 'dN': dN, 'I1': I1, 'I0': I0, 'c': list(map(float, c))},
                  open('winopt_family_N%d.json' % N, 'w'), indent=1)
    elif mode == 'general':
        ROUNDS = int(sys.argv[3]) if len(sys.argv) > 3 else 60; ST = int(sys.argv[4]) if len(sys.argv) > 4 else 16
        SEL = sys.argv[5] if len(sys.argv) > 5 else 'all'
        J = np.arange(1, N); types = [(k, t) for t in range(0, N // 3 + 1) for k in range(0, (N - 3 * t) // 2 + 1) if (k, t) != (0, 0)]
        if SEL == 'single': types = [(1, 0)]
        F = [np.zeros(N - 1)]; Pv = [1.0]
        for (k, t) in types:   # seed: one evenly spread configuration per type at the R8 window
            d, z = dmin_type(q_family(R8C, N), N, k, t, 3); n1 = N - 2 * k - 3 * t
            m = np.concatenate([np.ones(n1), np.full(k, 2.0), np.full(t, 3.0)]); F.append(np.abs(np.exp(2j * np.pi * np.outer(J, z) / N) @ m) ** 2); Pv.append(n1 / N)
        for it in range(ROUNDS):
            if SEL == 'single':   # dilute-gas form (c0 = 1): min sum_j q_j j  s.t.  q.F_v >= 2/N for every single-defect v
                Fs = np.array(F[1:]); r = linprog(J.astype(float), A_ub=-Fs, b_ub=np.full(len(Fs), -2.0 / N), bounds=[(0, None)] * (N - 1), method='highs')
                c0 = 1.0; q = r.x; val = 1 - r.fun
            elif SEL == 'allc1':   # D form with delta_true (c0 = 1): min sum_j q_j j  s.t.  q.F_v >= 1 - p_v for every config v
                Fs = np.array(F[1:]); r = linprog(J.astype(float), A_ub=-Fs, b_ub=-(1 - np.array(Pv[1:])), bounds=[(0, None)] * (N - 1), method='highs')
                c0 = 1.0; q = r.x; val = 1 - r.fun
            else:
                A = np.hstack([np.ones((len(F), 1)), -np.array(F)])     # c0 - q.F_v <= p_v
                r = linprog(np.concatenate([[-1.0], J.astype(float)]), A_ub=A, b_ub=np.array(Pv), bounds=[(None, None)] + [(0, None)] * (N - 1), method='highs')
                c0 = r.x[0]; q = r.x[1:]; val = -r.fun
            added = 0; worst = 0
            for (k, t) in types:
                if SEL in ('single', 'allc1') and (k, t) == (1, 0):   # every violating local minimum from a wide multistart becomes a cut
                    for (dd, zz) in single_minima(q, N, ST):
                        if dd < 2.0 / N - 1e-12:
                            m = np.concatenate([np.ones(N - 2), [2.0]]); F.append(np.abs(np.exp(2j * np.pi * np.outer(J, zz) / N) @ m) ** 2); Pv.append(1 - 2 / N); added += 1; worst = min(worst, dd - 2.0 / N)
                    continue
                d, z = dmin_type(q, N, k, t, ST); n1 = N - 2 * k - 3 * t; rc = n1 / N - c0 + d
                if rc < -1e-9:
                    m = np.concatenate([np.ones(n1), np.full(k, 2.0), np.full(t, 3.0)]); F.append(np.abs(np.exp(2j * np.pi * np.outer(J, z) / N) @ m) ** 2); Pv.append(n1 / N); added += 1; worst = min(worst, rc)
            print('it %d: dual value %.8f  c0 %.8f  added %d  worst rc %.2e  (%.0fs)' % (it, val, c0, added, worst, time.time() - t0), flush=True)
            if added == 0: break
        qn = q / q[0]
        kD, dN = kappa_D(q, N)
        print('GENERAL[%s] N=%d: LP value %.8f (c0 %.8f); kappa_D,N of this window %.7f (Delta_1/N %.6f)' % (SEL, N, val, c0, kD, dN))
        print('  window q(j/N)/q(1/N):', ' '.join('%.3f:%.4f' % (j / N, v) for j, v in zip(J, qn)))
        json.dump({'N': N, 'value': val, 'c0': c0, 'q': list(map(float, q)), 'kappa_D': kD, 'dN': dN}, open('winopt_general_%s_N%d.json' % (SEL, N), 'w'), indent=1)
    elif mode == 'famcut':
        # 25-mode family: fit the general single-defect optimum window, then cutting-plane SLSQP on
        #   max u  s.t.  z^T A_v z >= u z^T P z  (every single-defect config v found so far),  qf >= 0 on a fine grid
        from scipy.optimize import least_squares
        J = np.arange(1, N); M = Mmats(J / N); Mg = Mmats(np.linspace(0, 0.999, 241)); P = np.einsum('j,jik->ik', J.astype(float), M)
        gq = np.array(json.load(open(sys.argv[3]))['q']); gN = len(gq) + 1
        tgt = np.interp(J / N, np.arange(1, gN) / gN, gq); tgt = tgt / (tgt @ J)
        def resid(c):
            z = np.concatenate([[1.0], c]); q = np.einsum('jik,i,k->j', M, z, z); return q / (q @ J) - tgt
        fits = [least_squares(resid, c0).x for c0 in [R8C, np.zeros(KF)]]
        cf = min(fits, key=lambda c: np.abs(resid(c)).sum())
        qz = lambda c: np.einsum('jik,i,k->j', M, np.concatenate([[1.0], c]), np.concatenate([[1.0], c]))
        print('fit to the general window: max rel. residual %.2e; kappa_D,N(fit) %.7f; kappa_D,N(R8) %.7f' % (np.abs(resid(cf)).max() / tgt.max(), kappa_D(qz(cf), N)[0], kappa_D(qz(R8C), N)[0]), flush=True)
        json.dump({'N': N, 'c': list(map(float, cf)), 'source': sys.argv[3]}, open('winopt_famfit_N%d.json' % N, 'w'), indent=1)
        for NN in [24, 32, 48, 64]:
            kk, dN = kappa_D(q_family(cf, NN), NN); kr, dr = kappa_D(q_family(R8C, NN), NN)
            print('  N=%d: fit kappa_D,N %.7f (Delta_1/N %.6f) | R8 %.7f (%.6f)' % (NN, kk, dN, kr, dr), flush=True)
        I1, I0, kc = cont_kappa(cf, dN); I1r, I0r, kcr = cont_kappa(R8C, dr)
        print('  continuum (Delta_1/N at N=64): fit kappa_D %.7f  delta %.6f  int q a %.6f  int q %.6f | R8 kappa_D %.7f  delta %.6f  int q a %.6f'
              % (kc, dN / 2, I1, I0, kcr, dr / 2, I1r), flush=True)
        if len(sys.argv) < 5 or sys.argv[4] != 'refine': sys.exit(0)
        A = []
        for cc in [cf, R8C]:
            for (dd, zz) in single_minima(qz(cc), N, 20):
                A.append(np.einsum('j,jik->ik', np.abs(np.exp(2j * np.pi * np.outer(J, zz) / N) @ np.concatenate([np.ones(N - 2), [2.0]])) ** 2, M))
        c = cf.copy()
        for it in range(60):
            zf = lambda x: np.concatenate([[1.0], x[:-1]])
            cons = [{'type': 'ineq', 'fun': (lambda x, Av=Av: zf(x) @ Av @ zf(x) - x[-1] * (zf(x) @ P @ zf(x))),
                     'jac': (lambda x, Av=Av: np.concatenate([(2 * (Av - x[-1] * P) @ zf(x))[1:], [-(zf(x) @ P @ zf(x))]]))} for Av in A]
            cons.append({'type': 'ineq', 'fun': lambda x: np.einsum('jik,i,k->j', Mg, zf(x), zf(x)),
                         'jac': lambda x: np.hstack([(2 * np.einsum('jik,k->ji', Mg, zf(x)))[:, 1:], np.zeros((Mg.shape[0], 1))])})
            u0 = min(zf(np.concatenate([c, [0]])) @ Av @ zf(np.concatenate([c, [0]])) for Av in A) / (zf(np.concatenate([c, [0]])) @ P @ zf(np.concatenate([c, [0]])))
            r = minimize(lambda x: (-x[-1], np.concatenate([np.zeros(KF), [-1.0]])), np.concatenate([c, [u0]]), jac=True, method='SLSQP',
                         constraints=cons, options={'maxiter': 400, 'ftol': 1e-14})
            c = r.x[:-1]; u = r.x[-1]; q = qz(c); TG = float(q @ J); new = 0; dmn = np.inf
            for (dd, zz) in single_minima(q, N, 24):
                dmn = min(dmn, dd)
                if dd < u * TG * (1 - 1e-9):
                    A.append(np.einsum('j,jik->ik', np.abs(np.exp(2j * np.pi * np.outer(J, zz) / N) @ np.concatenate([np.ones(N - 2), [2.0]])) ** 2, M)); new += 1
            print('it %d: cut value %.7f  true kappa_D,N %.7f  new cuts %d  (%.0fs)' % (it, 1 - 2 / (N * u), 1 - 2 * TG / (N * dmn), new, time.time() - t0), flush=True)
            if new == 0: break
        kk, dN = kappa_D(q, N); qmin = float(np.einsum('jik,i,k->j', Mg, np.concatenate([[1.0], c]), np.concatenate([[1.0], c])).min())
        I1, I0, kc = cont_kappa(c, dN)
        print('FAMILY BEST N=%d: kappa_D,N %.7f (Delta_1/N %.6f, min qf %+.1e); continuum kappa_D %.7f; c = %s' % (N, kk, dN, qmin, kc, np.array2string(c, precision=6, max_line_width=300)), flush=True)
        json.dump({'N': N, 'kappa_D': kk, 'dN': dN, 'cont': kc, 'I1': I1, 'I0': I0, 'c': list(map(float, c))}, open('winopt_famcut_N%d.json' % N, 'w'), indent=1)
    elif mode == 'check':
        src = sys.argv[3]; ST = int(sys.argv[4]) if len(sys.argv) > 4 else 60
        if src == 'R8': q = q_family(R8C, N)
        elif src.startswith('family'): q = q_family(json.load(open(src.split(':')[1]))['c'], N)
        else:
            g = json.load(open(src.split(':')[1])); assert g['N'] == N; q = np.array(g['q'])
        J = np.arange(1, N); kD, dN = kappa_D(q, N); lpv, k1, arg, per_def, dm = typed_lp(q, N, ST)
        print('CHECK %s N=%d: kappa_D,N (single defect) %.7f | typed LP min p %.7f (c0 free), c0=1 value %.7f at type %s | Delta_1 %.4f'
              % (src, N, kD, lpv, k1, arg, dN * N), flush=True)
        print('  energy per double-equivalent / Delta_1:', ' '.join('%s:%.5f' % (kt, v / (dN * N)) for kt, v in sorted(per_def.items(), key=lambda t: t[1])[:8]), flush=True)
    elif mode == 'far':
        src = sys.argv[3]
        if src == 'R8': q = q_family(R8C, N)
        elif src.startswith('family'): q = q_family(json.load(open(src.split(':')[1]))['c'], N)
        else: q = np.array(json.load(open(src.split(':')[1]))['q']) if json.load(open(src.split(':')[1]))['N'] == N else None
        Ks = list(range(0, 9)) + [10, 12, 15, 20, 25, 30]
        d1, d0, out, disp, dv = farfield(q, N, [K for K in Ks if K <= (N - 2) // 2])
        print('FAR %s N=%d: optimal dipole: double at 0, vacancy at -%d; Delta_1/N %.6f, unrelaxed dipole/N %.6f' % (src, N, dv, d1 / N, d0 / N))
        for K, e in out: print('  double + K=%2d nearest simples each side relaxed: E/Delta_1 - 1 = %.2e   relaxation captured %.5f' % (K, e / d1 - 1, (d0 - e) / (d0 - d1)))
        print('  displacements relative to the double, by distance from the dipole centre (site: shift): ' + ' '.join('%g:%+.4f' % (b, v) for b, v in disp[:24]))
