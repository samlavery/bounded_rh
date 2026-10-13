"""Class (i) at separation D0 (small): exact B-B cross terms X(d; y_p, y_q) = int_{-1}^{1} qf B_p B_q cos(2 pi a d) on d in [D0, 64],
two-integration-by-parts tail beyond 64.  Each unordered 2 X_pq is charged to the deeper pair q (y_p <= y_q); a D0-separated set has
at most one pair per side in each annulus [k D0, (k+1) D0), so
  charge_q / y_q^2 <= 4 sum_k sup_{d in annulus k, y_p <= y_q, y_q in [a,b]} |X| / y_q^2      (grid + neighbour-variation allowance x2).
Compared with the certified per-pair margins m_[a,b] of the allocated DP (log given): class (i) at D0 closes iff R < m on every interval.
usage: python3 xlemma_exact.py DPLOG D0 [START WIDTH]   (mixed depths: annuli of WIDTH starting at START)"""
import sys, re, json, numpy as np
LOG, D0 = sys.argv[1], float(sys.argv[2]); START = float(sys.argv[3]) if len(sys.argv) > 3 else D0; WID = float(sys.argv[4]) if len(sys.argv) > 4 else D0
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
xg, wg = np.polynomial.legendre.leggauss(600); al = (xg + 1) / 2; wa = wg / 2; qa = qf(al)
def B(y): return 2 * np.cosh(2 * np.pi * al * y) - 2
def Bn(y): return B(y) / y ** 2 if y > 0 else (2 * np.pi * al) ** 2
dgrid = np.arange(START, 64.0001, 0.01); C = np.cos(2 * np.pi * np.outer(dgrid, al))      # nd x na
def Xn(yp, yq):          # X(d; yp, yq) / yq^2 on dgrid
    return 2 * (C @ (qa * wa * B(yp) * Bn(yq)))
af = np.linspace(0, 1, 20001); q = qf(np.minimum(af, 1 - 1e-13)); q[-1] = 0.0
def tail_coef(b):        # IBP bound constants for r~ = qf B_b^2 / b^2 (all derivatives monotone in depth)
    Bb = (2 * np.cosh(2 * np.pi * af * b) - 2); rt = q * Bb ** 2 / b ** 2
    d1 = np.gradient(rt, af, edge_order=2); d2 = np.gradient(d1, af, edge_order=2); d3 = np.gradient(d2, af, edge_order=2)
    return 1.05 * abs(d1[-1]), 1.05 * (abs(d2[-1]) + np.trapezoid(np.abs(d3), af))
nk = int(np.ceil((64 - START) / WID))
def R_interval(a, b):
    yqs = np.linspace(max(a, 1e-6), b, 3); per = []
    for yq in yqs:
        best_k = np.zeros(nk)
        yps = np.linspace(0.0, yq, 21)
        F = np.array([np.abs(Xn(yp, yq)) for yp in yps])            # n_yp x nd
        best_k = np.zeros(nk)
        for k in range(nk):
            sel = (dgrid >= START + WID * k) & (dgrid < START + WID * (k + 1) + 0.011)
            if not np.any(sel): continue
            Fk = F[:, sel]; var = max(float(np.max(np.abs(np.diff(Fk, axis=0)))), float(np.max(np.abs(np.diff(Fk, axis=1)))))
            best_k[k] = float(Fk.max()) + 2 * var                                   # local grid + neighbour-variation allowance
        per.append(best_k)
    per = np.array(per); best_k = per.max(0) + 2 * np.abs(np.diff(per, axis=0)).max(0)     # y_q variation allowance (x2)
    c2, c3 = tail_coef(b)
    kk = np.arange(int((64 - START) // WID), 200000)
    dk = START + WID * kk; tail = 2 * np.sum(c2 / (2 * np.pi * dk) ** 2 + c3 / (2 * np.pi * dk) ** 3) * 2      # |X| <= 2[...] per pair, 2 per annulus
    return 4 * float(best_k.sum()) + 2 * tail
rows = [l for l in open(LOG) if l.startswith('  y in')]
worst = np.inf
for l in rows:
    a, b = map(float, re.findall(r'\[([\d.]+), ([\d.]+)\]', l)[0]); m = float(re.search(r'LP_p/y\^2 >= ([+-][\d.]+)', l).group(1))
    r = R_interval(a, b); worst = min(worst, m - r)
    print('  y_q in [%.4f, %.4f]: margin %.4f | X charge %.4f | m - R %+.4f' % (a, b, m, r, m - r), flush=True)
print('D0 = %g (annuli start %g width %g): min (m - R) = %+.4f -> %s' % (D0, START, WID, worst, 'CLOSED' if worst > 0 else 'NOT closed'), flush=True)
