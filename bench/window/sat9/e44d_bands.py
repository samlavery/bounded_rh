"""E44d: part (c) diagnostics: for the saved E_end minimisers, split E_end = int w (|A|^2 - 4) into alpha bands and into the
positive and negative parts of the integrand; also the trivial bound -4 int_{|A|<2} w."""
import sys, json, numpy as np
exec(open('e44_endterm.py').read().rsplit("if __name__ == '__main__':", 1)[0])
for a in (0.90, 0.95, 0.99):
    for L in (50, 100, 200, 400):
        try: d = json.load(open('e44c_end_a%.2f_L%d.json' % (a, L)))
        except FileNotFoundError: continue
        ET = EndTerm(a, L, n=8000); y = np.array(d['y']); yi = d['yinf']; al = ET.al; k = 2 * np.pi * al
        cc = np.concatenate([2 * np.cosh(np.outer(k, y)), 2 * np.cosh(k * yi)[:, None]], 1); cinf = cc[:, L]
        D = np.concatenate([cc[:, :1], np.diff(cc, axis=1)], 1); X = (D[:, 1:] * (ET.Zp[:, 1:L + 1] - 1)).sum(1)
        F = (cinf ** 2 - 4) + 2 * cinf * np.real(X) + np.abs(X) ** 2; A2 = F + 4; contrib = ET.wq * F
        bands = [(0, 0.05), (0.05, 0.2), (0.2, 0.5), (0.5, 0.8), (0.8, 0.95), (0.95, 1.0001)]
        bs = ' '.join('[%.2f,%.2f):%+.3f' % (lo, hi, contrib[(al >= lo) & (al < hi)].sum()) for lo, hi in bands)
        neg = contrib[contrib < 0].sum(); pos = contrib[contrib > 0].sum(); triv = -4 * ET.wq[A2 < 4].sum()
        amin = al[np.argmin(contrib)]
        print('a=%.2f L=%3d E_end %+.4f | pos %+.4f neg %+.4f (most negative at al=%.3f) | trivial bound on neg part (-4 int_{|A|<2} w) %+.4f | bands %s'
              % (a, L, contrib.sum(), pos, neg, amin, triv, bs), flush=True)
