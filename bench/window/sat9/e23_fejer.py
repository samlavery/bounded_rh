"""E23 (pre-registered by the lead): Fejer positive-definite minorant of the lobe.
phi(al) = q_min(delta) (1 - |al|/delta)_+ <= q  (q decreasing on [0,1], so q_min(delta) = q(delta)); phi-check >= 0.
||S_A||_q^2 >= int phi |S_A|^2 = (i) 4 int phi |V|^2  +  (ii) 4 int phi Re(conj(V) S_B)  +  (iii) int phi |S_B|^2.
Target of (1'): 4 g0 P + 4 sum_{p,p'} h(s_p - s_p').  delta in {1/16, 1/8, 1/4}.
Configurations: e9_cfg_{16,24,32,48}.json; the e19 free minimisers (refined from the printed 3-decimal values by a short
L-BFGS run on (Q_pp + T_g^pp), depths in [0.8, 3]); the e20 parametric arches (exact)."""
import json, re, numpy as np
from scipy.optimize import minimize
from common import *
U = np.linspace(0.0, 64.0, 128001); GT = g_of(U); GT[0] = g0; dGT = np.gradient(GT, U)
def gtab(u):
    a = np.abs(u); return np.interp(a, U, GT, right=0.0), np.interp(a, U, dGT, right=0.0) * np.sign(u)
def f(z, P):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    F = (ch * E).sum(1); G = E.sum(1)
    Q = float(W2 @ (np.abs(F) ** 2 - 4 * np.abs(G) ** 2))
    ia = 2j * np.pi * al[:, None]
    gs = W2 @ (2 * np.real(np.conj(F)[:, None] * ch * ia * E) - 8 * np.real(np.conj(G)[:, None] * ia * E))
    dc = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    gy = W2 @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    d = s[:, None] - s[None, :]; gv, gd = gtab(d); np.fill_diagonal(gv, 0.0); np.fill_diagonal(gd, 0.0)
    return Q + 4 * gv.sum(), np.concatenate([gs + 8 * gd.sum(1), gy])

def test(name, s, y):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s)
    E = np.exp(2j * np.pi * np.outer(al, s)); Bm = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2
    V = E.sum(1); SB = (Bm * E).sum(1)
    d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * P + 4 * float((K_of(d) - g_of(d)).sum())
    QT = f(np.concatenate([s, y]), P)[0]
    row = []
    for de in (1 / 16, 1 / 8, 1 / 4):
        qmin = float(qfun(np.array([de]))[0]); phi = qmin * np.clip(1 - al / de, 0, None)
        w2 = 2 * phi * wa
        i1 = float(w2 @ (4 * np.abs(V) ** 2)); i2 = float(w2 @ (4 * np.real(np.conj(V) * SB))); i3 = float(w2 @ np.abs(SB) ** 2)
        row.append((de, i1, i2, i3, i1 + i2 + i3))
    best = max(r[4] for r in row)
    print('%-26s P=%2d target %7.2f | Q_pp+T_g %+8.2f |' % (name, P, tgt, QT) +
          ' | '.join('d=1/%d: (i) %7.2f (ii) %+7.2f (iii) %6.2f = %7.2f' % (round(1 / de), i1, i2, i3, t) for de, i1, i2, i3, t in row) +
          ' || best/target %.3f %s' % (best / tgt, 'PASS' if best >= tgt else 'FAIL'), flush=True)
    return best >= tgt

ok = True
for P in (16, 24, 32, 48):
    c = json.load(open('e9_cfg_%d.json' % P)); ok &= test('e9 P=%d' % P, c['s'], c['y'])
# e19 free minimisers: parse, refine
txt = open('e19_c1.log').read() + open('e19_c1_big.log').read()
for m in re.finditer(r'P=\s*(\d+): min.*?\n\s+s (\[.*?\])\s*\n\s+y (\[.*?\])', txt):
    P = int(m.group(1)); s0 = np.array(json.loads(m.group(2))); y0 = np.array(json.loads(m.group(3)))
    r = minimize(f, np.concatenate([s0, y0]), args=(P,), jac=True, method='L-BFGS-B',
                 bounds=[(None, None)] * P + [(0.8, 3.0)] * P, options={'maxiter': 4000})
    json.dump({'s': r.x[:P].tolist(), 'y': r.x[P:].tolist(), 'QT': r.fun}, open('e23_arch_%d.json' % P, 'w'))
    ok &= test('e19 min P=%d (refined)' % P, r.x[:P], r.x[P:])
# e20 parametric arches
for line in open('e20.log'):
    mm = re.search(r'P=\s*(\d+): .* at a=([\d.]+) A=([\d.]+) k=([\d.]+)', line)
    if mm:
        P = int(mm.group(1)); a, A, k = float(mm.group(2)), float(mm.group(3)), float(mm.group(4))
        t = np.arange(P) / (P - 1); ok &= test('e20 arch P=%d' % P, a * np.arange(P), 0.8 + A * np.sin(np.pi * t) ** k)
print('ALL PASS' if ok else 'SOME FAIL')
