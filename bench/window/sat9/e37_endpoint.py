"""E37: ENDPOINT LEMMA test (am-cert condition 11).  Fixed BEFORE the run.
For every pair p of every saved witness, phi_p(y) = 4 < B_y, g_p >_q,  g_p(al) = Re(conj W(al) e(al s_p)),  W = V + U:
  positions-only witnesses: e34_witness.json (16 lattices), e36_w_a*.json (P = 64, 128; a = 0.6, 0.7, 0.76, 0.8);
  D_K witnesses (K = 2, recomputed by the e33 QP at the e33 local-search labelling): the 6 e33 configurations; for these the
  min runs over the pair's class, so the lemma is 'min at a class endpoint'.
Grid: y step 0.001 on [0.8, 3] (or the class).  Grid error: max |phi(y_k+1) - phi(y_k)| over the pair (reported).
SUPPORTS: min at an endpoint for every pair of every witness.  REFUTES: an interior min below both endpoints by more than the grid
error.  Mechanism checks: (i) B_y'/B_y increasing in al for y' > y [pencil: d/dal log(sinh^2(pi al y')/sinh^2(pi al y))
= 2 pi (y' coth(pi al y') - y coth(pi al y)) >= 0 since x coth x - type monotonicity]; checked numerically on the grid;
(ii) number of sign changes of g_p on (0, 1) (q > 0 there).
PREDICTION (bridge-port): REFUTES.  The e32d hard evaluations already put argmin depths of QP-optimal witnesses in the interior
(e.g. 2.31 at a = 0.9 P = 12, 2.52 at a = 0.76 P = 48, 1.95 at a = 0.9 P = 24): at the QP optimum the one-body functions are
equalised near their minima, so interior minima are expected; the dips below the endpoint minimum should be small relative to
the margins but well above the grid error.  g_p will typically have >= 2 sign changes (V's sidelobes)."""
import json, numpy as np
from common import *
YY = np.round(np.arange(0.8, 3.0 + 1e-9, 0.001), 4)
def Bof(y): return 2 * np.cosh(2 * np.pi * al * y) - 2
BYY = np.array([Bof(y) for y in YY])                                       # (Ny, nA)
WB = W2 * BYY
def phi_all(s, t, w, phis=None):
    """phi_p(y) for all p on YY.  positions-only: W = V + sum_n w_n e(al t_n); profiled: w has shape (n, J) with phis (J, nA)."""
    s = np.asarray(s); t = np.asarray(t); P = len(s)
    if phis is None:
        gp = np.cos(2 * np.pi * np.outer(al, (s[:, None] - s[None, :]).ravel())).reshape(len(al), P, P).sum(2) \
           + (np.cos(2 * np.pi * np.outer(al, (s[:, None] - t[None, :]).ravel())).reshape(len(al), P, len(t)) @ w)
    else:
        ct = np.cos(2 * np.pi * np.outer(al, (s[:, None] - t[None, :]).ravel())).reshape(len(al), P, len(t))
        prof = np.einsum('nj,ja->an', w, phis)                              # (nA, n): sum_j w_nj phi_j(al)
        gp = np.cos(2 * np.pi * np.outer(al, (s[:, None] - s[None, :]).ravel())).reshape(len(al), P, P).sum(2) + np.einsum('apn,an->ap', ct, prof)
    return 4 * (WB @ gp), gp                                                 # (Ny, P), (nA, P)
def analyse(name, ph, gp, lo=None, hi=None):
    P = ph.shape[1]; worst = 0.0; n_int = 0; gerr = 0.0; signch = []
    for p in range(P):
        if lo is None: m = np.ones(len(YY), bool)
        else: m = (YY >= lo[p] - 1e-9) & (YY <= hi[p] + 1e-9)
        f = ph[m, p]; k = int(np.argmin(f)); ge = float(np.max(np.abs(np.diff(f)))) if len(f) > 1 else 0.0; gerr = max(gerr, ge)
        endmin = min(f[0], f[-1])
        if 0 < k < len(f) - 1:
            dip = endmin - f[k]
            if dip > ge: n_int += 1; worst = max(worst, dip)
        g = gp[(al > 0) & (al < 1), p]; sg = np.sign(g[np.abs(g) > 1e-12 * np.abs(g).max()]); signch.append(int((np.diff(sg) != 0).sum()))
    print('  %-30s P=%3d | pairs with interior min (dip > grid err): %3d | worst dip %.4g | max grid err %.3g | sign changes of g_p: min %d median %d max %d'
          % (name, P, n_int, worst, gerr, min(signch), int(np.median(signch)), max(signch)), flush=True)
    return n_int, worst
# (i) monotonicity of B_y'/B_y in alpha
ok = True
for y1, y2 in ((0.8, 0.9), (0.8, 3.0), (1.5, 1.6), (2.9, 3.0)):
    r = Bof(y2)[1:] / Bof(y1)[1:]; ok &= bool(np.all(np.diff(r) >= -1e-12 * r[1:]))
print('(i) B_{y\'}/B_y nondecreasing in alpha on the grid for tested pairs:', ok)
tot_int = 0; tot_worst = 0.0
print('positions-only witnesses:')
wit = json.load(open('e34_witness.json'))
for k, v in wit.items():
    ph, gp = phi_all(v['s'], v['t'], np.array(v['w'])); a, b = analyse('e34 ' + k, ph, gp); tot_int += a; tot_worst = max(tot_worst, b)
for a in (0.6, 0.7, 0.76, 0.8):
    d = json.load(open('e36_w_a%.2f.json' % a))
    for P, key in ((64, 'w64'), (128, 'w128')):
        s = a * np.arange(P); t = np.round(np.concatenate([s[0] - a * np.arange(4, 0, -1), s, s[-1] + a * np.arange(1, 5)]), 9)
        ph, gp = phi_all(s, t, np.array(d[key])); x, b = analyse('e36 a=%.2f P=%d' % (a, P), ph, gp); tot_int += x; tot_worst = max(tot_worst, b)
print('D_K witnesses (K = 2, class-restricted min):')
exec(open('e33_classK.py').read().split("if __name__ == '__main__':")[0])
res = json.load(open('e33_results.json'))
cfgs = [('lattice a=0.90 P=12', 0.9 * np.arange(12)), ('lattice a=0.90 P=48', 0.9 * np.arange(48))]
for P in (12, 16, 24, 32):
    c = json.load(open('e23_arch_%d.json' % P)); cfgs.append(('e23 minimiser P=%d' % P, np.array(c['s'])))
for name, s in cfgs:
    lab = np.array(res['%s K=2' % name]['labels_min']); Sc = Setup(s, 2, 0.02); o, w = solveQP(Sc, lab)
    edges = Sc.edges; yhat = 0.5 * (edges[:-1] + edges[1:])
    phis = np.array([np.ones_like(al)] + [Bof(y) / np.sqrt(W2 @ Bof(y) ** 2) for y in yhat])
    ph, gp = phi_all(Sc.s, Sc.t, w.reshape(len(Sc.t), Sc.J), phis)
    x, b = analyse('D_K ' + name, ph, gp, lo=edges[lab], hi=edges[lab + 1]); tot_int += x; tot_worst = max(tot_worst, b)
print('TOTAL pairs with interior minima beyond grid error: %d; worst dip %.4g -> %s' % (tot_int, tot_worst, 'REFUTES' if tot_int > 0 else 'SUPPORTS'))
