"""Phase 1 (b), part 1: derivative profile of the pair term w(s) = (K(s)/K0)^2 for the R8 window: |w''| and |w'''| envelopes by range.
Analytic derivatives of K via sinc derivatives (finite differences of the analytic K at step 1e-4 checked against step 2e-4)."""
import json, numpy as np
R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
cw = np.array(R8['cnum'], float) / R8['cden']; om = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw))])
def K(x):
    x = np.asarray(x, float)[..., None]
    return ((np.sinc((om - 2 * np.pi * x) / 2 / np.pi) + np.sinc((om + 2 * np.pi * x) / 2 / np.pi)) / 2 * cw).sum(-1)
K0 = float(K(0.0)); s = np.linspace(-1, 261, 1310001); h = s[1] - s[0]
w = (K(s) / K0) ** 2
d1 = np.gradient(w, h); d2 = np.gradient(d1, h); d3 = np.gradient(d2, h)
keep = (s >= 0) & (s <= 260); s, w, d1, d2, d3 = s[keep], w[keep], d1[keep], d2[keep], d3[keep]
for lo, hi in ((0, 0.8), (0.8, 1.2), (1.2, 2.5), (2.5, 5), (5, 10), (10, 20), (20, 36), (36, 100), (100, 260)):
    m = (s >= lo) & (s < hi)
    print('s in [%5.1f, %5.1f): max w %.3e | max|w\'\'| %.3e | max|w\'\'\'| %.3e | ratio max|w\'\'|/max|w\'\'\'| %.3f' % (lo, hi, w[m].max(), np.abs(d2[m]).max(), np.abs(d3[m]).max(), np.abs(d2[m]).max() / np.abs(d3[m]).max()))
np.savez('w_profile.npz', s=s, w=w, d1=d1, d2=d2, d3=d3)
