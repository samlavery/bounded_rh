"""Trust-region LP ascent (wopt3) with w0 = sqrt 2 frozen and the Lean layer's admissibility constants (wopt8.LIM, with
margins) as linearised constraints; the strong-LP oracle (wopt8.evaluate_s) for n >= 8 or WOPT_STRONG=1.
Each step solves  max kE t + kH gH.dth  s.t.  t <= b.g + a.(W(g) + J_g dth) on every near-active cut g,
adm_k(theta) + grad adm_k . dth <= LIM_k - MARG_k,  |dth_i| <= r,  dth_0 = 0;  accept if the re-solved Phi improves.

  python3 wopt9.py n B iters THETA_JSON [K] [SEED]   (SEED > 0: random start, see below)
Random start (SEED > 0): c_j = theta_j + N(0, sigma_j) with sigma_j = RAND_SCALE * (|theta_j| + 1e-3), shrunk into the
feasible set; RAND_SCALE from the environment (default 0.5)."""
import sys, os, json, time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate, window
from wopt8 import evaluate_s, adm, adm_grad, feasible, LIM, MARG, fmt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family, H_of

n, B, iters = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
t_in = np.array(json.loads(sys.argv[4]), float)
K = int(sys.argv[5]) if len(sys.argv) > 5 else len(t_in) - 1
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
theta = np.zeros(K + 1); theta[:len(t_in)] = t_in; theta[0] = np.sqrt(2.0)
q = n - 1
STRONG = n >= 8 or bool(os.environ.get('WOPT_STRONG'))
FREE_W0 = bool(os.environ.get('WOPT_FREE_W0'))   # w0 free (Lean's EL identity needs w0 = sqrt 2)
if seed > 0:
    rng = np.random.default_rng(seed); sc = float(os.environ.get('RAND_SCALE', '0.5'))
    theta[1:] = theta[1:] + rng.normal(0, 1, K) * sc * (np.abs(theta[1:]) + 1e-3)
if not feasible(theta)[0]:
    for f in np.linspace(0.99, 0.3, 140):
        th = theta.copy(); th[1:] *= f
        if feasible(th)[0]: theta = th; break

def ev(th, G0=None, rounds=25):
    if STRONG: return evaluate_s(n, B, th[0], th[1:], rounds=rounds, G0=G0)
    return evaluate(n, B, th[0], th[1:], rounds=rounds, strong=False, G0=G0)

def phi_parts(H, eps, m):
    x = (m - q) / m; D = 1 - eps * x
    return (H - B * x) / D, 1 / D, (H - B * x) * x / D ** 2

def W_of(th, G):
    c, w = window(th[0], th[1:]); return Family(q, c, w).Wmat(G)

t0 = time.time()
r = ev(theta, rounds=40)
print('start seed=%d: Phi=%.7f H=%.10f eps=%.9f m=%d %s (%.0fs)' % (seed, r['phi'], r['H'], r['eps'], r['m'],
                                                                 fmt(adm(theta)), time.time() - t0), flush=True)
rad = 2e-3
for it in range(1, iters + 1):
    st = r['state']; a, b = st.a, st.b
    G = st.G
    F0 = G @ b + W_of(theta, G) @ a
    near = F0 <= r['eps'] + 2e-4
    Gn = G[near]; W0 = W_of(theta, Gn)
    P = len(theta); h = 1e-6
    J = np.zeros((Gn.shape[0], P)); gH = np.zeros(P)
    for i in range(0 if FREE_W0 else 1, P):
        e = np.zeros(P); e[i] = h
        J[:, i] = (W_of(theta + e, Gn) @ a - W_of(theta - e, Gn) @ a) / (2 * h)
        c1, w1 = window((theta + e)[0], (theta + e)[1:]); c2, w2 = window((theta - e)[0], (theta - e)[1:])
        gH[i] = (H_of(c1, w1) - H_of(c2, w2)) / (2 * h)
    _, kH, kE = phi_parts(r['H'], r['eps'], r['m'])
    v, ga = adm(theta), adm_grad(theta)
    cost = np.concatenate([-kH * gH, [-kE]])
    A_ub = [np.hstack([-J, np.ones((Gn.shape[0], 1))])]; b_ub = [Gn @ b + W0 @ a]
    for k in LIM:
        # linearised with twice the margin: S1, D2 (|c|) and PV (clipped cells) are only piecewise linear
        A_ub.append(np.concatenate([ga[k], [0.0]])[None, :]); b_ub.append([max(LIM[k] - 2 * MARG[k] - v[k], 0.0)])
    bounds = [(-rad, rad) if FREE_W0 else (0.0, 0.0)] + [(-rad, rad)] * (P - 1) + [(None, None)]
    res = linprog(cost, A_ub=np.vstack(A_ub), b_ub=np.concatenate(b_ub), bounds=bounds, method='highs')
    if not res.success:
        rad /= 3; print('it %d: step LP failed (%s), rad %.1e' % (it, res.message[:40], rad), flush=True)
        if rad < 1e-6: break
        continue
    th_new = theta + res.x[:P]
    if not feasible(th_new)[0]:
        rad /= 3; print('it %d: infeasible step, rad %.1e' % (it, rad), flush=True)
        if rad < 1e-6: break
        continue
    rt = ev(th_new, G0=st.G)
    if rt['phi'] > r['phi'] + 2e-7:
        theta, r = th_new, rt; rad = min(rad * 1.5, 1e-2); tag = 'accept'
    else:
        rad /= 3; tag = 'reject (%.7f)' % rt['phi']
    print('it %d: %s Phi=%.7f H=%.10f eps=%.9f m=%d rad=%.1e near=%d %s (%.0fs)' %
          (it, tag, r['phi'], r['H'], r['eps'], r['m'], rad, int(near.sum()), fmt(adm(theta)), time.time() - t0), flush=True)
    print('   theta=%s' % json.dumps([round(float(t), 9) for t in theta]), flush=True)
    if rad < 1e-6: break
print('BEST n=%d B=%.6f K=%d seed=%d: Phi=%.7f (eps %.9f, H %.10f, m %d) %s theta=%s' %
      (n, B, K, seed, r['phi'], r['eps'], r['H'], r['m'], fmt(adm(theta)), json.dumps([round(float(t), 9) for t in theta])),
      flush=True)
