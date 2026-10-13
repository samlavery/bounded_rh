"""e46 -- how sharp is the separated-set Gram bound of the leader's file (bench/arun/MOP_Solution.lean)?

Object.  For a weight w >= 0 supported on [-1/2, 1/2] with kernel k(t) = int w(s) cos(2 pi t s) ds, put
    Lambda_w(d) = sup over finite d-separated sets Y of lambda_max [k(y_i - y_j)].
The leader's file bounds it by a bandlimited majorant G >= w with G^ = 0 on |t| >= 17/20
(`separatedBound`, `scaled_separated_bound`): Lambda <= int G.

Weights.
  R8  : w = rho * vAM on [-1/2, 1/2], rho = 1/(sqrt2 sin(sqrt2/2)), so k(0) = 1 (the AM chain's kfun).
        Majorant used there: G = (14/13) gMaj = (7/10)(sincN(d0(u-1/2)) + sincN(d0(u+1/2)))^2, d0 = 17/20,
        int G = 1.92707 (bounded by 1253/650; times 51/50 finite-height slack = 63903/32500 = 1.96625).
  P673: w = fCos (Knausgard's Simple673 window), k(0) = 1.  normS = 19/10 there; int gMaj = 1.78942.
  G   : the majorant itself (gamma = 7/10), as a weight.

Three numbers per (weight, d), d in {0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 1.00}:
  low : max lambda_max found over d-separated configurations (n = 2..64 points, L-BFGS-B on gaps >= d,
        multi-start; a LOWER bound for Lambda, local optima from stated starts) and the lattice limit
        sup_theta (1/d) sum_m w((theta + m)/d) (exact for the infinite lattice dZ).
  maj : the best bandlimited majorant value  min { int G : G >= w on [-1/2,1/2], G >= 0, G^ supported in [-d,d] },
        by SDP: G = sum_kl M_kl psi_k psi_l, psi_k(s) = sincN(d s - k), |k| <= K, M PSD, int G = tr M / d;
        constraint on a grid, then REPAIRED to a sound value by scaling with max_s w/G on a 20001-point grid.
        (An upper bound for Lambda; "best the majorant method can do".)
  used: the file's value (R8: 1.92707 at d = 0.85; P673: 1.78942 at d = 0.85).

PRE-REGISTERED PREDICTIONS (written before any run):
  P1 (pencil, checked numerically as a control): for w = G, Lambda_G(d) = int G exactly for every d >= 17/20,
      because every off-diagonal G^(y_i - y_j) vanishes.  So the majorant step is exact for G and the whole loss
      of the file's bound is in replacing w by G.
  P2: R8 at d = 0.85: low in [1.29, 1.40] (lattice limit rho*v(0)/d = 1.2885); I predict 1.30-1.35.
  P3: R8 at d = 0.85: maj in [1.45, 1.70]; I predict about 1.55.  So the file's 1.927 loses ~0.35 to the shape
      of its majorant and a further ~0.2 to the majorant method itself.
  P4: P673 at d = 0.85: low about 1.30-1.40 (lattice limit f(0)/d = 1.294); maj about 1.5-1.7.
  P5 (sanity, decides correctness of this script): low <= maj <= used at d = 0.85 for both windows.  A violation
      is a bug here (or in the source) and voids the round.

DECISION RULE (pre-registered):
  - "clearly below 19/10" means maj(0.85) <= 1.80 for the R8 weight.  Then report maj as the sharp majorant-method
    constant and low as the attained value; the gap low..maj is what any majorant proof cannot close.
  - If low(0.85) > 1.9 for either window, the stated bound is contradicted: STOP and report.
  - kappa consequence is NOT decided here: the source read (L23457 proposedQ_identity; L22947) shows the cap
    enters kappa only as "<= 2".  This round is LATERAL (instrument) by that reading.
"""
import sys, time, json
import numpy as np
from scipy.optimize import minimize

RHO = 1.0 / (np.sqrt(2) * np.sin(np.sqrt(2) / 2))
C_R8 = np.array([1000000000, 12310798, -15041681, 3867664, 6489926, -992327, 5580097,
                 -6846472, 3781297, -5670353, 3355089, -450523, -218483]) / 1e9
OM_R8 = np.array([np.sqrt(2)] + [2 * np.pi * j for j in range(1, 13)])
A_P673 = np.array([122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]) / 1e6
D0 = 17 / 20
GAM = 7 / 10


def sincU(x):
    return np.sinc(np.asarray(x) / np.pi)


def dsincU(x):
    x = np.asarray(x, dtype=float)
    out = np.empty_like(x)
    sm = np.abs(x) < 1e-4
    xs = x[sm]
    out[sm] = -xs / 3 + xs ** 3 / 30
    xb = x[~sm]
    out[~sm] = (xb * np.cos(xb) - np.sin(xb)) / xb ** 2
    return out


def dsincN(t):
    t = np.asarray(t, dtype=float)
    out = np.empty_like(t)
    sm = np.abs(t) < 1e-6
    out[sm] = -(np.pi ** 2) * t[sm] / 3
    tb = t[~sm]
    out[~sm] = (np.cos(np.pi * tb) - np.sinc(tb)) / tb
    return out


# ---- weights -------------------------------------------------------------------------------------------
def w_R8(s):
    s = np.asarray(s, dtype=float)
    v = (C_R8[None, :] * np.cos(OM_R8[None, :] * s.reshape(-1, 1))).sum(1).reshape(s.shape)
    return np.where(np.abs(s) <= 0.5, RHO * v, 0.0)


def w_P673(s):
    s = np.asarray(s, dtype=float)
    j = np.arange(1, 11)
    v = 1 + (A_P673[None, :] * np.cos(2 * np.pi * j[None, :] * s.reshape(-1, 1))).sum(1).reshape(s.shape)
    return np.where(np.abs(s) <= 0.5, v, 0.0)


def w_G(s):
    s = np.asarray(s, dtype=float)
    return GAM * (np.sinc(D0 * (s - 0.5)) + np.sinc(D0 * (s + 0.5))) ** 2


# ---- kernels k(t) and k'(t) ----------------------------------------------------------------------------
def k_R8(t):
    t = np.asarray(t, dtype=float)
    b = 2 * np.pi * t[..., None]
    zp = (OM_R8 + b) / 2
    zm = (OM_R8 - b) / 2
    k = 0.5 * RHO * (C_R8 * (sincU(zp) + sincU(zm))).sum(-1)
    dk = 0.5 * RHO * (C_R8 * (np.pi * dsincU(zp) - np.pi * dsincU(zm))).sum(-1)
    return k, dk


def k_P673(t):
    t = np.asarray(t, dtype=float)
    j = np.arange(1, 11)
    tt = t[..., None]
    k = np.sinc(t) + (A_P673 / 2 * (np.sinc(tt - j) + np.sinc(tt + j))).sum(-1)
    dk = dsincN(t) + (A_P673 / 2 * (dsincN(tt - j) + dsincN(tt + j))).sum(-1)
    return k, dk


def k_G(t):
    t = np.asarray(t, dtype=float)
    a = np.abs(t)
    inside = a < D0
    r = D0 - a
    k = GAM * (2 / D0 ** 2) * (r * np.cos(np.pi * t) + np.sin(np.pi * r) / np.pi)
    # derivative wrt t (for t != 0): d/dt [r cos(pi t) + sin(pi r)/pi], r = d0 - |t|
    sg = np.sign(t)
    dk = GAM * (2 / D0 ** 2) * (-sg * np.cos(np.pi * t) - np.pi * r * np.sin(np.pi * t) - sg * np.cos(np.pi * r))
    return np.where(inside, k, 0.0), np.where(inside, dk, 0.0)


WEIGHTS = {"R8": (w_R8, k_R8), "P673": (w_P673, k_P673), "G": (w_G, k_G)}


# ---- lower bound: configurations -----------------------------------------------------------------------
def lam_and_grad(gaps, kern):
    y = np.concatenate([[0.0], np.cumsum(gaps)])
    D = y[:, None] - y[None, :]
    K, dK = kern(D)
    K = 0.5 * (K + K.T)
    ev, U = np.linalg.eigh(K)
    u = U[:, -1]
    lam = ev[-1]
    # d lam / d y_i = 2 u_i sum_j u_j k'(y_i - y_j)
    gy = 2 * u * (dK @ u)
    # y_i = sum_{r < i} g_r  ->  d/dg_r = sum_{i > r} gy_i
    gg = np.cumsum(gy[::-1])[::-1][1:]
    return lam, gg


def best_config(kern, d, n, starts, rng, gmax=6.0):
    best = (-np.inf, None)
    for s in range(starts):
        if s == 0:
            g0 = np.full(n - 1, d)
        elif s == 1:
            g0 = np.full(n - 1, d) + 1e-3 * rng.random(n - 1)
        else:
            g0 = d + rng.exponential(0.4, n - 1)
        g0 = np.clip(g0, d, gmax)
        f = lambda g: tuple(-v for v in lam_and_grad(g, kern))
        res = minimize(f, g0, jac=True, method="L-BFGS-B", bounds=[(d, gmax)] * (n - 1),
                       options={"maxiter": 3000, "ftol": 1e-14, "gtol": 1e-11})
        lam = -res.fun
        if lam > best[0]:
            best = (lam, res.x.copy())
    return best


def lattice_limit(w, d, m=4001):
    th = np.linspace(-0.5, 0.5, m)
    tot = np.zeros_like(th)
    for mm in range(-4, 5):
        tot += w((th + mm) / d)
    return tot.max() / d


# ---- upper bound: best bandlimited majorant (SDP) ------------------------------------------------------
def best_majorant(w, d, K=12, ngrid=801):
    import cvxpy as cp
    ks = np.arange(-K, K + 1)
    s = np.linspace(-0.5, 0.5, ngrid)
    Psi = np.sinc(d * s[:, None] - ks[None, :])
    wv = w(s)
    M = cp.Variable((len(ks), len(ks)), PSD=True)
    cons = [cp.sum(cp.multiply(Psi @ M, Psi), axis=1) >= wv]
    prob = cp.Problem(cp.Minimize(cp.trace(M) / d), cons)
    prob.solve(solver=cp.CLARABEL)
    Mv = 0.5 * (M.value + M.value.T)
    ev, U = np.linalg.eigh(Mv)
    Mv = (U * np.clip(ev, 0, None)) @ U.T
    sf = np.linspace(-0.5, 0.5, 20001)
    Pf = np.sinc(d * sf[:, None] - ks[None, :])
    Gf = np.einsum("ik,kl,il->i", Pf, Mv, Pf)
    wf = w(sf)
    scale = max(1.0, float(np.max(wf / np.maximum(Gf, 1e-300))))
    return float(np.trace(Mv) / d) * scale, float(prob.value), scale


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = np.random.default_rng(46)
    ds = [0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 1.00]
    ns = [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
    out = {}
    names = ["R8", "P673", "G"] if which == "all" else [which]
    for name in names:
        w, kern = WEIGHTS[name]
        print(f"== weight {name}: k(0) = {kern(np.array([0.0]))[0][0]:.6f}, int w = "
              f"{np.trapezoid(w(np.linspace(-30, 30, 600001)), np.linspace(-30, 30, 600001)):.6f}", flush=True)
        for d in ds:
            t0 = time.time()
            low, arg, nbest = -np.inf, None, None
            per_n = {}
            for n in ns:
                lam, g = best_config(kern, d, n, starts=12 if n <= 16 else 6, rng=rng)
                per_n[n] = lam
                if lam > low:
                    low, arg, nbest = lam, g, n
            lat = lattice_limit(w, d)
            if name != "G":
                maj, maj_grid, sc = best_majorant(w, d)
            else:
                maj, maj_grid, sc = float("nan"), float("nan"), float("nan")
            gstats = (float(arg.min()), float(np.median(arg)), float(arg.max())) if arg is not None and len(arg) else None
            print(f"  d={d:.2f}: low {low:.6f} (n={nbest}; gaps min/med/max {gstats}) | lattice limit {lat:.6f} | "
                  f"maj {maj:.6f} (grid {maj_grid:.6f}, repair x{sc:.6f}) | per n "
                  + " ".join(f"{n}:{v:.4f}" for n, v in per_n.items()) + f" | {time.time()-t0:.0f}s", flush=True)
            out[f"{name}_{d:.2f}"] = dict(low=low, n=nbest, gaps=None if arg is None else arg.tolist(), lattice=lat,
                                          maj=maj, maj_grid=maj_grid, repair=sc, per_n=per_n)
    with open(f"e46_{which}.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
