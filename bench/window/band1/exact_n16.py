"""Round 4: the N = 16P exact decision test.  Exact relaxed periodic LP (certificate v1, lemmaP normalisation, LP_total = 2W) of a block of
P equal-depth pairs with N - 2P on-line singletons, at N = MULT*P, from three starts:
  (a) contiguous vacancies next to the block (round-1 construction), (b) P vacancies spread evenly, (c) a uniformly stretched environment.
L-BFGS on all positions (environment and pair centres; depths fixed at Y).  For the lowest LP: a_p (mean adjacent spacing), sum_p m_bulk(a_p)
with the round-2 t_L per geometry and with t_L = 0.016, the environment density within 40 of the block ends, and the environment's phase
locking to the block (|mean e(x)| over the environment 3..60 from the ends, and its phase relative to arg sum_p e(s_p)).
usage: python3 exact_n16.py P[,P..] Y[,Y..] [MULT] [OUT.json]"""
import sys, json, time, numpy as np
from scipy.optimize import minimize
PS = [int(v) for v in sys.argv[1].split(',')]; YS = [float(v) for v in sys.argv[2].split(',')]
MULT = int(sys.argv[3]) if len(sys.argv) > 3 else 16; OUT = sys.argv[4] if len(sys.argv) > 4 else None
TL = {(0.2, 16): 0.008, (0.2, 32): 0.008, (0.2, 64): 0.012, (0.4, 16): 0.012, (0.4, 32): 0.016, (0.4, 64): 0.016}
B = {}; exec(open('bulk_end.py').read().split("if STAGE == 'mbulk':")[0].replace("STAGE = sys.argv[1]", "STAGE = 'none'"), B); m_bulk = B['m_bulk']
lsrc = open('lemmaP.py').read().split("if __name__ == '__main__':")[0]
out = []
for P in PS:
    N = MULT * P; L = {}; exec(lsrc.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % N), L)
    dg, gN0, gh0 = L['d_and_grad'], L['gN0'], L['gh0']; M = N - 2 * P; cen = np.arange(P, dtype=float)
    rest = np.arange(P, N); vac = P + np.round((np.arange(P) + 0.5) * (N - P) / P).astype(int)
    starts = {'a': np.arange(2 * P, N, dtype=float), 'b': rest[~np.isin(rest, vac)].astype(float), 'c': P + (np.arange(M) + 0.5) * (N - P) / M}
    for Y in YS:
        ys = np.full(P, Y); res = {}
        for nm, xon in starts.items():
            assert len(xon) == M
            t0 = time.time()
            r = minimize(lambda z: dg(z, M, 0, P, ys), np.concatenate([xon, cen]), jac=True, method='L-BFGS-B', options={'maxiter': 40000, 'maxfun': 60000, 'ftol': 1e-15, 'gtol': 1e-9, 'maxcor': 30})
            LP = 2 * (r.fun / N - N * (gN0 - gh0) / 2 - gN0 * P); gmax = float(np.max(np.abs(r.jac)))
            res[nm] = (LP, r)
            print('  P=%d N=%d Y=%.1f start %s: exact LP %.4f  (nit %d, success %s, max|grad| %.1e, %.0fs)' % (P, N, Y, nm, LP, r.nit, r.success, gmax, time.time() - t0), flush=True)
        nm = min(res, key=lambda k: res[k][0]); LP, r = res[nm]
        sc = r.x[M:]; xe = r.x[:M]; c0 = float(np.mean(sc)); rel = lambda v: ((v - c0 + N / 2) % N) - N / 2
        s = np.sort(rel(sc)); e = np.sort(rel(xe)); sp = np.diff(s)
        ap = np.empty(P); ap[0], ap[-1] = sp[0], sp[-1]; ap[1:-1] = (sp[:-1] + sp[1:]) / 2
        tl = TL[(round(Y, 1), P)]; mb = float(sum(m_bulk(a, 0.5, tl)[0] for a in ap)); mb16 = float(sum(m_bulk(a, 0.5, 0.016)[0] for a in ap))
        lo_, hi_ = s.min(), s.max(); dens = float(np.sum(((e >= lo_ - 40) & (e < lo_)) | ((e > hi_) & (e <= hi_ + 40)))) / 80
        near = ((e >= lo_ - 60) & (e <= lo_ - 3)) | ((e >= hi_ + 3) & (e <= hi_ + 60))
        zb = np.sum(np.exp(2j * np.pi * s)); ze = np.mean(np.exp(2j * np.pi * e[near]))
        print('P=%2d N=%4d Y=%.1f: exact LP %.4f (start %s) | sum m_bulk(a_p) %.4f (t_L %.3f) -> LP - sum %+.4f | with t_L 0.016: sum %.4f, LP - sum %+.4f | '
              'centre spacing %.4f, end spacings %.3f %.3f | env density within 40 of the ends %.3f | env locking |mean e(x)| %.3f, phase vs block %+.2f rad, |sum_p e(s_p)|/P %.3f'
              % (P, N, Y, LP, nm, mb, tl, LP - mb, mb16, LP - mb16, sp[len(sp) // 2], sp[0], sp[-1], dens, abs(ze), float(np.angle(ze / zb)), abs(zb) / P), flush=True)
        out.append({'name': 'rb%d_n%d' % (P, MULT), 'N': N, 'Y': Y, 'pairs': s.tolist(), 'depths': ys.tolist(), 'env': e.tolist(), 'LP_total': float(LP),
                    'split': {'P_h': float('nan')}, 'LP_over_sum_y2': float(LP / np.sum(ys ** 2)), 'start': nm, 'all_starts': {k: float(v[0]) for k, v in res.items()}})
if OUT: json.dump(out, open(OUT, 'w'))
