"""Two-level certificate simulation with run-breaking allowed (double precision).
Certified block value of a configuration (block of m = 152 points, every phase of a periodic word):
  CL = g( c(m-q) + delta c * #(windows not in U_delta) ) + sum over maximal runs of U-windows of credit(run),
  credit(run) = exact energy of the pairs INSIDE the run's point span at rank >= 8 (optimistic: the certificate is
  assumed to know the run's gaps exactly; pairs crossing a run boundary get nothing), folded additively (beta = 1).
R_2L(delta) = min over configurations (words x phases); kappa_2L = (mH - B(m-q)) / (m - R_2L).
Candidates: exact-integer slip words, drifted slip words (tl_drift.json optimal words at every drift), the ergodic and
alternating words, and defect words: a base word repeated j times with one gap shifted by s (j = 2..20)."""
import json, math, numpy as np
from rmax import Fwin, K, B, tau, m
from slack import H
c_cls = 805165 / 1e8; cN = 805124 / 1e8; q = 7
def g(E): return E if E <= tau else 2 * math.sqrt(tau * E) - tau
def kap(R): return (m * H - B * (m - q)) / (m - R)
R0 = g(cN * (m - q)); k0 = kap(R0)

def windows_excess(gw):
    gw = np.asarray(gw, float); ext = np.tile(gw, 8 // len(gw) + 2)
    return np.array([Fwin(ext[s:s + 7]) for s in range(len(gw))]) / c_cls - 1

def CL_min_over_phases(gw, delta):
    gw = np.asarray(gw, float); qq = len(gw)
    exc = windows_excess(gw)
    best = np.inf
    for ph in range(qq):
        seq = np.tile(np.roll(gw, -ph), m // qq + 3)[: m - 1]
        x = np.concatenate([[0.0], np.cumsum(seq)])
        inU = [(exc[(ph + s) % qq] <= delta) for s in range(m - q)]
        nout = sum(1 for u in inU if not u)
        cred = 0.0; s = 0
        while s < m - q:
            if inU[s]:
                e = s
                while e + 1 < m - q and inU[e + 1]: e += 1
                lo, hi = s, e + 7                     # points of the run
                if hi - lo >= 8:
                    pts = x[lo:hi + 1]
                    D = pts[:, None] - pts[None, :]
                    idx = np.arange(len(pts)); rk = np.abs(idx[:, None] - idx[None, :])
                    cred += float((K(D[rk >= 8]) ** 2).sum())
                s = e + 1
            else:
                s += 1
        best = min(best, g(cN * (m - q) + delta * cN * nout) + cred)
    return best

if __name__ == '__main__':
    drift = json.load(open('tl_drift.json'))
    cands = {}
    for nm, rows in drift.items():
        for d, e, cr, gw in rows: cands['%s d%+.4f' % (nm, d)] = gw
    cands['ergodic abbabab'] = [1.0451, 1.9866, 1.9866, 1.0451, 1.9758, 1.0436, 1.9759]
    cands['alternating'] = [1.9745, 1.0427]
    bases = {k: v for k, v in cands.items() if any(t in k for t in ('ab d+0.0090', 'ab d+0.0146', 'abb d+0.0090', 'abb d+0.0146',
             'abbabab d+0.0382', 'ababababb d+0.0236', 'ergodic', 'alternating'))}
    for bn, bw in bases.items():
        for j in range(2, 21):
            w = list(np.tile(bw, j // len(bw) + 1)[:max(j, len(bw))])
            for sh in (-0.06, -0.03, -0.015, 0.015, 0.03, 0.06):
                w2 = list(w); w2[0] = w2[0] + sh
                cands['defect %s j%d s%+.3f' % (bn, j, sh)] = w2
    print('PC8SF: R0 = %.6f kappa %.7f; %d candidate configurations' % (R0, k0, len(cands)), flush=True)
    for delta in (0.0025, 0.005, 0.01, 0.015, 0.02, 0.025, 0.03, 0.04):
        best = (np.inf, None)
        for nm, gw in cands.items():
            v = CL_min_over_phases(gw, delta)
            if v < best[0]: best = (v, nm)
        print('delta %.2f%%: R_2L %.6f  kappa_2L %.7f  gain %+.2e   binding: %s' % (100 * delta, best[0], kap(best[0]), kap(best[0]) - k0, best[1]), flush=True)
