"""Class (i) closure: B-B cross terms between separated pairs (centres pairwise >= D0 apart, depths <= 0.8).
X_pq = int_{-1}^{1} qf B_p B_q cos(2 pi a d) = 2 int_0^1 r cos, r = qf B_p B_q, r(1) = r'(0) = 0, so (two integrations by parts)
  |X_pq| <= 2 [ |r'(1)|/(2 pi d)^2 + (|r''(1)| + int_0^1 |r'''|)/(2 pi d)^3 ].
Each unordered 2 X_pq is charged to the deeper pair q (y_p <= y_q).  B_p <= B_q and B_q/y_q^2, with all a-derivatives, increase in
y_q, so charge_q / y_q^2 <= R(b) for y_q <= b, with r~ = qf B_b^2 / b^2 and
  R(b) = 4 [ |r~'(1)| (pi^2/3)/(D0^2 (2pi)^2) + (|r~''(1)| + int|r~'''|) 2 zeta(3)/(D0^3 (2pi)^3) ]   (sums over a D0-separated set).
Compared with the certified allocated-slack margins m_[a,b] of crowd_dp3 (LP_q >= m y_q^2): class (i) closes iff R(b) < m_[a,b].
Derivatives by finite differences x 1.05 (the standard of the other tail constants).  usage: python3 sep_xlemma.py LOG [D0]"""
import sys, re, json, numpy as np
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
LOG = sys.argv[1]; D0 = float(sys.argv[2]) if len(sys.argv) > 2 else 32.0
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
af = np.linspace(0, 1, 20001); q = qf(np.minimum(af, 1 - 1e-13)); q[-1] = 0.0
zeta3 = 1.2020569
def R(b):
    Bb = (2 * np.cosh(2 * np.pi * af * b) - 2) if b > 0 else None
    rt = q * Bb ** 2 / b ** 2
    d1 = np.gradient(rt, af, edge_order=2); d2 = np.gradient(d1, af, edge_order=2); d3 = np.gradient(d2, af, edge_order=2)
    c2 = 1.05 * abs(d1[-1]); c3 = 1.05 * (abs(d2[-1]) + np.trapezoid(np.abs(d3), af))
    return 4 * (c2 * (np.pi ** 2 / 3) / (D0 ** 2 * (2 * np.pi) ** 2) + c3 * 2 * zeta3 / (D0 ** 3 * (2 * np.pi) ** 3))
rows = [l for l in open(LOG) if l.startswith('  y in')]
worst = np.inf
for l in rows:
    a, b = map(float, re.findall(r'\[([\d.]+), ([\d.]+)\]', l)[0]); m = float(re.search(r'LP_p/y\^2 >= ([+-][\d.]+)', l).group(1))
    r = R(b); worst = min(worst, m - r)
    if abs(b * 80 - round(b * 80)) < 1e-9 and round(b * 80) % 8 == 0 or m - r < 0.5:
        print('  y_q in [%.4f, %.4f]: margin m %.4f | X charge R(b) %.4f | m - R %+.4f' % (a, b, m, r, m - r), flush=True)
print('D0 = %g: min over intervals of (m - R) = %+.4f  -> class (i) %s' % (D0, worst, 'CLOSED' if worst > 0 else 'NOT closed'), flush=True)
