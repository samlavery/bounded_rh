"""AdmWindow / LocalHypsCore obligations for phi = sqrt(v/M) * taper, v = AMTOPA window (k terms).
Fields that depend on v: le_one (v/M <= 1), l1_deriv (TV(phi) <= 2), l1_deriv_sq (TV(phi^2) <= 2), b_ge_half
(int (v/M)^2 > 1/2), 1/2 <= a <= 1.  Ramp taper is nonincreasing in |u|, so on the half line
TV/2 = f(0) + 2 PV(f) with f = sqrt(v/M) (resp. v/M); the ramp adds nothing (max_deriv_mul_le)."""
import numpy as np, sys
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import AMTOPA_C, frequencies
s = np.linspace(0, 0.5, 4_000_001)
for k in (17, 13):
    c = AMTOPA_C[:k]; w = frequencies(k)
    v = (c[:, None] * np.cos(w[:, None] * s[None, :])).sum(0)
    pv = np.clip(np.diff(v), 0, None).sum(); pvs = np.clip(np.diff(np.sqrt(v)), 0, None).sum()
    I1 = 2 * np.trapezoid(v, s); I2 = 2 * np.trapezoid(v * v, s)
    print(f"k={k}: v(0)={v[0]:.6f} vmax={v.max():.6f} at s={s[v.argmax()]:.4f} vmin={v.min():.6f}  int v={I1:.6f} int v^2={I2:.6f}"
          f"  PV(v)={pv:.6f} PV(sqrt v)={pvs:.6f}  sum|c_j|,j>=1 = {np.abs(c[1:]).sum():.6f}")
    print(f"   as given (M=1): le_one: max phi^2 = {v.max():.5f} (fails by {v.max()-1:+.5f});"
          f" TV(phi)/2 = {np.sqrt(v[0]) + 2*pvs:.5f}; TV(phi^2)/2 = {v[0] + 2*pv:.5f}  (need <= 1)")
    Mlo = max(v.max(), (np.sqrt(v[0]) + 2 * pvs) ** 2, v[0] + 2 * pv); Mhi = np.sqrt(2 * I2)
    print(f"   admissible scalings M in [{Mlo:.5f}, {Mhi:.5f})  (lower: le_one/TV; upper: b > 1/2)")
    for M in (1.0652, 1.25):
        f0 = np.sqrt(v[0] / M)
        print(f"   M={M}: a={I1/M:.4f} b={I2/M**2:.4f}  TV(phi)/2={f0 + 2*pvs/np.sqrt(M):.4f}  TV(phi^2)/2={(v[0]+2*pv)/M:.4f}"
              f"  PV budget for a cell certificate: PV(v) <= {min((1-f0)*np.sqrt(v.min()*M), (M - v[0])/2):.4f} (true {pv:.5f})")
