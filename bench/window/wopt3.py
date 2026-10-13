"""Trust-region LP ascent in the window coefficients for our n-point assembly (handles the max-min non-smoothness:
all near-active cuts move together).  Alternates
  (i)  (a, b) <- LP optimum for the current window (warm-started cutting planes, wopt.LPState);
  (ii) dtheta <- argmax  kE * t + kH * (dH . dtheta)  s.t.  t <= b.g + a.(W0(g) + J_g dtheta)  for every near-active
       cut g,  |dtheta_i| <= r  (linearised kernel, fixed (a, b), fixed m);  kE = dPhi/deps, kH = dPhi/dH;
and accepts the step if the re-solved Phi improves (else r /= 3).
usage: python3 wopt3.py n B iters K THETA_JSON|am   (K = number of corrections; am = AMTOPA's 12, padded to K)"""
import sys, json, time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate, window, AMTOPA_C
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family, H_of

n, B, iters, K = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
if sys.argv[5] == 'am':
    theta = np.zeros(K + 1); theta[0] = np.sqrt(2.0); theta[1:13] = AMTOPA_C[1:13]
else:
    t0 = np.array(json.loads(sys.argv[5])); theta = np.zeros(K + 1); theta[:len(t0)] = t0
q = n - 1

def phi_parts(H, eps, m):
    x = (m - q) / m; D = 1 - eps * x
    return (H - B * x) / D, 1 / D, (H - B * x) * x / D ** 2   # Phi, dPhi/dH, dPhi/deps

def W_of(th, G):
    c, w = window(th[0], th[1:]); return Family(q, c, w).Wmat(G)

t0 = time.time()
r = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=False)
print('it 0: Phi=%.7f H=%.10f eps=%.9f m=%d (%.0fs)' % (r['phi'], r['H'], r['eps'], r['m'], time.time() - t0), flush=True)
rad = 2e-3
for it in range(1, iters + 1):
    st = r['state']; a, b = st.a, st.b
    G = st.G
    F0 = G @ b + W_of(theta, G) @ a
    near = F0 <= r['eps'] + 2e-4                      # near-active cuts
    Gn = G[near]; W0 = W_of(theta, Gn)
    P = len(theta); h = 1e-6
    J = np.empty((Gn.shape[0], P))                    # d (a . W(g)) / d theta_i
    gH = np.empty(P)
    for i in range(P):
        e = np.zeros(P); e[i] = h
        J[:, i] = (W_of(theta + e, Gn) @ a - W_of(theta - e, Gn) @ a) / (2 * h)
        c1, w1 = window(*((theta + e)[0], (theta + e)[1:])); c2, w2 = window(*((theta - e)[0], (theta - e)[1:]))
        gH[i] = (H_of(c1, w1) - H_of(c2, w2)) / (2 * h)
    _, kH, kE = phi_parts(r['H'], r['eps'], r['m'])
    # variables: dtheta (P), t ; maximise kE t + kH gH.dtheta
    cost = np.concatenate([-kH * gH, [-kE]])
    A_ub = np.hstack([-J, np.ones((Gn.shape[0], 1))])
    b_ub = Gn @ b + W0 @ a
    bounds = [(-rad, rad)] * P + [(None, None)]
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    if not res.success:
        print('  LP step failed:', res.message); rad /= 3; continue
    dth = res.x[:P]
    th_new = theta + dth
    rt = evaluate(n, B, th_new[0], th_new[1:], rounds=25, strong=False, G0=st.G)
    pred = kE * (res.x[-1] - r['eps']) + kH * gH @ dth
    if rt['phi'] > r['phi'] + 2e-7:
        theta, r = th_new, rt; rad = min(rad * 1.5, 2e-2)
        tag = 'accept'
    else:
        rad /= 3; tag = 'reject'
    print('it %d: %s Phi=%.7f (pred +%.2e, got %+.2e) H=%.10f eps=%.9f m=%d w0=%.5f rad=%.1e near=%d (%.0fs)' %
          (it, tag, r['phi'], pred, rt['phi'] - (r['phi'] if tag == 'reject' else r['phi'] - (rt['phi'] - r['phi'])),
           r['H'], r['eps'], r['m'], theta[0], rad, int(near.sum()), time.time() - t0), flush=True)
    if rad < 1e-6: break
rs = evaluate(n, B, theta[0], theta[1:], rounds=40, strong=True)
print('BEST n=%d B=%.5f K=%d: Phi=%.7f (strong eps %.9f, H %.10f, m %d) theta=%s' %
      (n, B, K, rs['phi'], rs['eps'], rs['H'], rs['m'], json.dumps([round(float(t), 9) for t in theta])), flush=True)
