"""Round 1 (1): bulk/end decomposition of the certified multi-pair bound for shallow dense blocks.
 m_bulk(a) = 4 sum_{k != 0} g(k a) + 4 (2 t_B - t_B^2) (1/a) sum_m hhat_W(m/a) + [4 t_L - 2 t_L a - t_L^2 a / hhat(0)]   (Poisson; Q_pp/P -> 0)
 stage 'mbulk' : tabulate m_bulk(a) and its parts;
 stage 'uniform': DP bounds of exact uniform blocks (a in A, y in Y, P in PS) -> slope vs m_bulk, end terms;
 stage 'relax' : periodic minimisers with N = 4P (P = 32, 64; P = 16 from multipair_geoms.json) saved to bulk_end_geoms.json.
usage: python3 bulk_end.py STAGE"""
import sys, os, json, numpy as np
STAGE = sys.argv[1]
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
from fractions import Fraction
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); Dk = 1 / 32
def gfun(u):
    u = np.atleast_1d(np.asarray(u, float)); th = 2 * np.pi * Dk * u
    C = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, 96))) @ yk[1:]); return Dk * np.sinc(Dk * u) ** 2 * C
def hhat(a):
    a = np.abs(np.asarray(a, float)); gh = np.interp(a, np.arange(97) * Dk, np.concatenate([yk, [0.0]]), right=0.0)
    return np.where(a < 1, qf(np.minimum(a, 1 - 1e-13)), 0.0) - gh
def hhatW(a, A0=0.5, A1=0.75):
    a = np.abs(np.asarray(a, float)); return hhat(a) * np.clip((a - A0) / (A1 - A0), 0.0, 1.0)
h0 = float(hhat(0.0))
def m_bulk(a, tB=0.5, tL=0.008):
    k = np.arange(1, 4000); Tpp = 8 * float(np.sum(gfun(k * a)))
    m = np.arange(-int(3 * a) - 2, int(3 * a) + 3); band = 4 * (2 * tB - tB ** 2) / a * float(np.sum(hhatW(m / a)))
    low = 4 * tL - 2 * tL * a - tL ** 2 * a / h0
    return Tpp + band + low, Tpp, band, low
if STAGE == 'mbulk':
    print('m_bulk(a) per pair (t_B = 0.5, t_L = 0.008): total = T_pp + band + low')
    for a in (0.85, 0.9, 0.94, 0.96, 0.97, 0.98, 0.985, 0.99, 0.995, 0.999):
        tot, T, b, l = m_bulk(a); print('  a = %.3f: m_bulk %.5f = T_pp %.5f + band %.5f + low %.5f' % (a, tot, T, b, l))
elif STAGE == 'uniform':
    G = []
    for a in (0.97, 0.985):
        for y in (0.2, 0.4):
            for P in (8, 16, 32, 64):
                s = a * (np.arange(P) - (P - 1) / 2)
                G.append({'name': 'U%03d_%d' % (int(round(1000 * a)), P), 'N': 0, 'Y': y, 'pairs': s.tolist(), 'depths': [y] * P, 'env': [],
                          'LP_total': float('nan'), 'split': {'P_h': float('nan')}, 'LP_over_sum_y2': float('nan')})
    json.dump(G, open('bulk_end_uniform.json', 'w')); print('saved', len(G))
elif STAGE == 'relax':
    from scipy.optimize import minimize
    out = []
    for P in (32, 64):
        N = 4 * P
        exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % N), globals())
        for Y in (0.2, 0.4):
            ys = np.full(P, Y); cen = np.arange(P, dtype=float); vac = set(range(P, 2 * P))
            xon = np.array([t for t in range(P, N) if t not in vac], float); n1 = len(xon)
            r = minimize(lambda z: d_and_grad(z, n1, 0, P, ys), np.concatenate([xon, cen]), jac=True, method='L-BFGS-B', options={'maxiter': 20000})
            sc = r.x[n1:]; c0 = float(np.mean(sc)); rel = lambda v: ((v - c0 + N / 2) % N) - N / 2
            LP = 2 * (r.fun / N - N * (gN0 - gh0) / 2 - gN0 * P)
            out.append({'name': 'rb%d' % P, 'N': N, 'Y': Y, 'pairs': np.sort(rel(sc)).tolist(), 'depths': ys.tolist(), 'env': np.sort(rel(r.x[:n1])).tolist(),
                        'LP_total': float(LP), 'split': {'P_h': float('nan')}, 'LP_over_sum_y2': float(LP / np.sum(ys ** 2))})
            print('P=%d N=%d Y=%.1f: exact LP %.4f; spacings (first 8) %s centre %.4f' % (P, N, Y, LP, np.round(np.diff(np.sort(rel(sc)))[:8], 3), float(np.diff(np.sort(rel(sc)))[P // 2])), flush=True)
    json.dump(out, open('bulk_end_geoms.json', 'w'))
