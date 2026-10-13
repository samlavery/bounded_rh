"""Constrained window ascent for our n-point assembly at w0 = sqrt 2 (frozen), K corrections, with the Lean layer's
admissibility constants as hard constraints (so the window drops into the existing AMW layer unchanged):
  S1  = sum_j |c_j|                       <= 13/200          (sum_abs_cAM_succ, vAM bounds, hW_core_ge)
  D1  = 3/2 + 6.3 sum_j |c_j| j           <= 7/2             (abs_vAMd_le)
  D2  = 2 + 39.7 sum_j |c_j| j^2          <= 78              (abs_vAMdd_le)
  PV  = sum_i max(v'(m_i) + 78/256, 0)/160 <= 9/200           (pvCheck, 64 midpoint cells)
  V0  = v(0)/M                             <= 81/100          (vAM_zero_div_le)
each kept at a margin (MARG below).  Ascent: LP-envelope gradient of Phi, projected off the near-active constraints,
3-point line search with warm-started LPs; infeasible trials are rejected.

  python3 wopt8.py scan n B THETA_JSON              Phi of one window (theta = [w0, c_1..c_K]; w0 is reset to sqrt 2)
  python3 wopt8.py opt  n B iters THETA_JSON [K]    ascent (theta padded with zeros to K corrections)"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate, grad, phi_grad, LPState

import os
if os.environ.get('WOPT8_COARSE'):                              # stronger inner minimiser (n = 8: weak-vs-strong gap)
    _d = list(LPState.run.__defaults__); _d[1] = int(os.environ['WOPT8_COARSE']); LPState.run.__defaults__ = tuple(_d)
LIM = dict(S1=13 / 200, D1=3.5, D2=78.0, PV=9 / 200, V0=0.81)
LIM.update(json.loads(os.environ.get('WOPT8_LIM', '{}')))      # relaxed-constant experiments
MARG = dict(S1=2e-4, D1=0.02, D2=0.3, PV=4e-4, V0=1e-3)
MID = (2 * np.arange(64) + 1) / 256

def adm(theta):
    c = np.concatenate([[1.0], theta[1:]]); K = len(c) - 1; j = np.arange(1, K + 1)
    w = np.concatenate([[theta[0]], 2 * np.pi * j])
    a = np.abs(c[1:])
    vd = -(c[:, None] * w[:, None] * np.sin(w[:, None] * MID[None, :])).sum(0)
    return dict(S1=a.sum(), D1=1.5 + 6.3 * (a * j).sum(), D2=2 + 39.7 * (a * j * j).sum(),
                PV=np.clip(vd + LIM['D2'] / 256, 0, None).sum() / 160, V0=c.sum() / 1.25)

def feasible(theta):
    v = adm(theta); return all(v[k] <= LIM[k] - MARG[k] for k in LIM), v

def adm_grad(theta, h=1e-7):
    P = len(theta); out = {k: np.zeros(P) for k in LIM}
    for i in range(1, P):
        e = np.zeros(P); e[i] = h
        vp, vm = adm(theta + e), adm(theta - e)
        for k in LIM: out[k][i] = (vp[k] - vm[k]) / (2 * h)
    return out

def project(d, theta):
    """remove from d the components that push near-active constraints outward (active set, least squares)."""
    v = adm(theta); g = adm_grad(theta)
    act = [k for k in LIM if v[k] >= LIM[k] - 3 * MARG[k]]
    for _ in range(3):
        out = [k for k in act if g[k] @ d > 0]
        if not out: break
        A = np.array([g[k] for k in out])
        d = d - A.T @ np.linalg.lstsq(A @ A.T, A @ d, rcond=None)[0]
    return d, act

def fmt(v): return ' '.join('%s=%.5g' % (k, v[k]) for k in LIM)

def smin(fam, a, b, lat, seed):
    """strong minimum of G(.; a, b): local descents from the 150 best lattice points (the lattice gets its own quota;
    in famq.global_min the random samples can crowd the lattice basins out of the `keep` list, which at n = 8 missed
    the (2,1,2,2,1,2,1) basin by 7e-6) and from the 150 best of a random cover."""
    v1, g1, f1 = fam.global_min(a, b, coarse=2, keep=150, seed=seed, extra_starts=lat)
    v2, g2, f2 = fam.global_min(a, b, coarse=150000, keep=150, seed=seed + 1000)
    found = sorted(f1 + f2, key=lambda t: t[0])
    return (v1, g1, found) if v1 <= v2 else (v2, g2, found)

def evaluate_s(n, B, w0, corr, rounds=25, G0=None, outer=4):
    """evaluate() with the strong oracle folded INTO the LP: after each cutting-plane run, a strong global search
    (4-level lattice incl. the small-gap level 0.5) at the LP's weights; its minimisers are added as cuts and the LP is
    re-run, until the LP's lower bound agrees with the strong search.  The duals then belong to the cut set that
    contains the true minimisers, so the ascent climbs on the real floor."""
    import itertools
    from wopt import window, best_phi
    from famq import Family, H_of
    c, w = window(w0, corr); H = H_of(c, w); fam = Family(n - 1, c, w); Q = n - 1
    levels = tuple(float(x) for x in os.environ.get('WOPT8_LAT', '1.04,1.97,2.91,0.5').split(','))
    lat4 = np.array(list(itertools.product(levels, repeat=Q)))
    st = LPState(fam, B)
    st.G = np.vstack([G0.copy() if G0 is not None else st.G, lat4])
    for k in range(outer):
        lo, up = st.run(rounds=rounds)
        s_lo, _, found = smin(fam, st.a, st.b, lat4, seed=101 + k)
        if s_lo >= lo - 2e-8: break
        st.G = np.vstack([st.G, np.array([x for _, x in found[:200]])])
    lo = min(lo, s_lo)
    phi, m = best_phi(H, lo, B, n)
    return dict(H=H, eps=lo, upper=up, phi=phi, m=m, state=st, fam=fam)

if __name__ == '__main__':
    mode, n, B = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    if mode == 'scan':
        theta = np.array(json.loads(sys.argv[4]), float); theta[0] = np.sqrt(2.0)
        t0 = time.time(); r = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=True)
        ok, v = feasible(theta)
        print('SCAN n=%d B=%.6f K=%d: Phi=%.7f H=%.10f eps=%.9f m=%d feasible=%s %s (%.0fs)' %
              (n, B, len(theta) - 1, r['phi'], r['H'], r['eps'], r['m'], ok, fmt(v), time.time() - t0), flush=True)
        sys.exit(0)
    iters = int(sys.argv[4]); t_in = np.array(json.loads(sys.argv[5]), float)
    K = int(sys.argv[6]) if len(sys.argv) > 6 else len(t_in) - 1
    theta = np.zeros(K + 1); theta[:len(t_in)] = t_in; theta[0] = np.sqrt(2.0)
    ok, v = feasible(theta)
    if not ok:                                         # shrink the corrections into the feasible set
        for f in np.linspace(0.99, 0.5, 50):
            th = theta.copy(); th[1:] *= f
            if feasible(th)[0]: theta = th; break
    t0 = time.time()
    r = evaluate_s(n, B, theta[0], theta[1:], rounds=40)
    print('it 0: Phi=%.7f H=%.10f eps=%.9f m=%d %s (%.0fs)' % (r['phi'], r['H'], r['eps'], r['m'], fmt(adm(theta)),
                                                              time.time() - t0), flush=True)
    s0 = 2e-3
    for it in range(1, iters + 1):
        ge, gH = grad(n, B, theta[0], theta[1:], r['state'])
        g = phi_grad(r['H'], r['eps'], B, n, r['m'], ge, gH); g[0] = 0.0
        d, act = project(g, theta); d = d / (np.linalg.norm(d) + 1e-30)
        best = None
        for s in (s0, s0 / 3, s0 / 9):
            th = theta + s * d
            if not feasible(th)[0]: continue
            rt = evaluate_s(n, B, th[0], th[1:], rounds=20, G0=r['state'].G)
            if best is None or rt['phi'] > best[0]['phi']: best = (rt, th, s)
        if best is not None and best[0]['phi'] > r['phi'] + 2e-7:
            r, theta = best[0], best[1]; s0 = min(3 * best[2], 0.02)
        else:
            s0 /= 9
        print('it %d: Phi=%.7f H=%.10f eps=%.9f m=%d s0=%.1e |g|=%.2e act=%s %s (%.0fs)' %
              (it, r['phi'], r['H'], r['eps'], r['m'], s0, np.linalg.norm(g), ','.join(act) or '-',
               fmt(adm(theta)), time.time() - t0), flush=True)
        print('   theta=%s' % json.dumps([round(float(t), 9) for t in theta]), flush=True)
        if s0 < 1e-6: break
    rs = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=True)
    print('BEST n=%d B=%.6f K=%d: Phi=%.7f (strong eps %.9f, H %.10f, m %d) %s theta=%s' %
          (n, B, K, rs['phi'], rs['eps'], rs['H'], rs['m'], fmt(adm(theta)),
           json.dumps([round(float(t), 9) for t in theta])), flush=True)
