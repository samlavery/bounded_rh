"""Slack attribution of PC8SF's block inequality on the dual's minimising words (double precision).

PC8SF (tauint/PC8C5BFh2TS.lean header: kappa 6734832/10^7, m = 152, q = 7, tau = 8/7, sqrt branch) on window R8
(rwin8.json), certificate PC8C5BF (rootR8f/AMW/PC8C5BFInst.lean: cN 805124, SA 10^8, BS/TS = rwin8.json bN/aN).
Block chain (rootR8f/AMW/BrTau.lean block_energy_band, window_pairs_le_band; BrSqrtWS.lean block_bound_w'_g):
  c(m-q) <= PairSum + Press  (each window's functional F >= c; PairSum = sum over windows of a_ab W(span))
  PairSum <= Eband           (span mass <= 2; Eband = sum over ordered pairs at rank distance 1..q of W)
  defect = tr Phi(G) >= g(Eband)                      (band_profile_sqrt)
  defect + Press >= g(c(m-q)) = R                     (g monotone, increments <= identity's)
Per block, total slack S = defect + Press - R splits as
  L1   = tr Phi(G) - g(Eband)                          (band-profile link)
  L2c  = g(Eband + Press) - g(PairSum + Press)         (band coverage: pairs/weights the windows do not certify)
  L2l  = g(Eband) + Press - g(Eband + Press)           (sqrt-branch Lipschitz step, (sqrt y - sqrt tau)^2 when Eband <= tau)
  L3   = g(PairSum + Press) - g(c(m-q))                (local-functional excess sum (F - c) through g)
Part (1): exact tr Phi(G_block) vs the Frobenius / Ef of step (a) (Lemma 5.1, txt:333-335)."""
import sys, json, math
import numpy as np
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, H_of, QFTable, Ef_word, window_from_cnum

R8 = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))
c = window_from_cnum(R8['cnum']); H = H_of(c)
z = np.concatenate([[1.0], c]); w = np.concatenate([[math.sqrt(2)], 2 * np.pi * np.arange(1, len(c) + 1)])
A = 2 * math.sin(math.sqrt(2) / 2) / math.sqrt(2)

def Sfun(nu):
    nu = np.asarray(nu, float); out = np.ones_like(nu)
    nz = np.abs(nu) > 1e-14
    out[nz] = 2 * np.sin(nu[nz] / 2) / nu[nz]
    return out

def K(x):
    x = np.asarray(x, float); tot = np.zeros_like(x)
    for zj, wj in zip(z, w):
        tot += zj * 0.5 * (Sfun(wj - 2 * np.pi * x) + Sfun(wj + 2 * np.pi * x))
    return tot / A

def W(x): return K(x) ** 2

SA = 10 ** 8; q = 7; m = 152; tau = 8 / 7
cc = 805124 / SA
bN = np.array(R8['bN']) / SA
aN = {tuple(map(int, k.split(','))): v / SA for k, v in R8['aN'].items()}
def g(E): return E if E <= tau else 2 * math.sqrt(tau * E) - tau
def Phi(t): return np.where(t <= 2, (t - 1) ** 2, 2 * t - 3)
R = g(cc * (m - q))

def block_points(gaps, phase, n):
    gaps = list(gaps); qq = len(gaps)
    seq = [gaps[(phase + k) % qq] for k in range(n - 1)]
    return np.concatenate([[0.0], np.cumsum(seq)])

def block_stats(gaps, phase, n=m):
    x = block_points(gaps, phase, n)
    D = x[:, None] - x[None, :]
    G = K(D)
    lam = np.linalg.eigvalsh(G)
    trPhi = float(Phi(lam).sum())
    Wm = G ** 2; np.fill_diagonal(Wm, 0)
    frob = float(Wm.sum())
    idx = np.arange(n); rk = np.abs(idx[:, None] - idx[None, :])
    Eband = float(Wm[(rk >= 1) & (rk <= q)].sum())
    pair = 0.0; press = 0.0
    for i in range(n - q):
        for (a, b), wt in aN.items():
            if wt: pair += wt * W(np.array([x[i + b] - x[i + a]]))[0]
        press += float(np.sum(bN * np.diff(x[i:i + q + 1])))
    return dict(trPhi=trPhi, frob=frob, Eband=Eband, pair=pair, press=press, lmax=float(lam.max()), lmin=float(lam.min()))

def word_report(gaps, label):
    qq = len(gaps); rows = [block_stats(gaps, p) for p in range(qq)]
    avg = {k: float(np.mean([r[k] for r in rows])) for k in rows[0]}
    avg['lmax'] = max(r['lmax'] for r in rows); avg['lmin'] = min(r['lmin'] for r in rows)
    L1 = avg['trPhi'] - g(avg['Eband'])
    L2c = g(avg['Eband'] + avg['press']) - g(avg['pair'] + avg['press'])
    L2l = g(avg['Eband']) + avg['press'] - g(avg['Eband'] + avg['press'])
    L3 = g(avg['pair'] + avg['press']) - R
    return avg, dict(L1=L1, L2c=L2c, L2l=L2l, L3=L3, S=avg['trPhi'] + avg['press'] - R)

if __name__ == '__main__':
    qf = make_qf(c); T = QFTable(qf)
    words = {'P3 [1.0382,1.9618]': [1.96183, 1.03817],
             'Q7 period 10': [1.029992, 1.953037, 1.037678, 1.958585, 1.037678, 1.953037, 1.029992],
             'P4 [1.0284,1.0284,1.9432]': [1.028397, 1.028397, 1.943206]}
    for k, v in list(words.items()):
        L = round(sum(v)); words[k] = [x * L / sum(v) for x in v]
    print('R8: H = %.10f; PC8SF: c = %.8f, m = %d, R = g(c(m-q)) = %.8f (c(m-q) = %.6f, tau = %.6f)' % (H, cc, m, R, cc * (m - q), tau))
    out = {}
    for k, gaps in words.items():
        avg, Ls = word_report(gaps, k)
        Ef = Ef_word(gaps, T, exact=True)
        # infinite-m per-point tr Phi from a long block (centre rows): check against Ef
        big = block_stats(gaps, 0, n=1200)
        print('\n%s  (mean gap %.5f)' % (k, sum(gaps) / len(gaps)))
        print('  eigenvalues of G_152 in [%.5f, %.5f]  (clip level 2 %s)' % (avg['lmin'], avg['lmax'], 'NOT reached' if avg['lmax'] < 2 else 'REACHED'))
        print('  per point: Ef (step a, infinite) %.9f | Frobenius_152/m %.9f | trPhi_152/m %.9f | trPhi_1200/1200 %.9f'
              % (Ef, avg['frob'] / m, avg['trPhi'] / m, big['trPhi'] / 1200))
        print('  per block (m=152): trPhi %.6f  Eband %.6f  PairSum %.6f  Press %.6f  R %.6f' % (avg['trPhi'], avg['Eband'], avg['pair'], avg['press'], R))
        print('  slack per block: L1 %.6f  L2c %.6f  L2l %.6f  L3 %.6f  total %.6f   (per point x1e4: %.3f %.3f %.3f %.3f)'
              % (Ls['L1'], Ls['L2c'], Ls['L2l'], Ls['L3'], Ls['S'], *(1e4 * Ls[x] / m for x in ('L1', 'L2c', 'L2l', 'L3'))))
        out[k] = dict(avg=avg, slack=Ls, Ef=Ef, trPhi_inf=big['trPhi'] / 1200)
    json.dump(out, open('slack_r8.json', 'w'), indent=1)
