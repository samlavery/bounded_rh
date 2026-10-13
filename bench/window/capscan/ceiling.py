"""Obstruction ceiling r(family): the root of Fobs(r) = max_c [H(f) - r(1 - Ef)] = 0 for a two-configuration mixture
(Lemma 5.1, Prop. 6.1 of refs/Zeta_Geometry_and_Class_Cap.txt), for window families
  cos(w0 t) + sum_{j=1}^K c_j cos(2 pi j t) on [-1/2, 1/2].
usage: python3 ceiling.py K w0|sqrt2 [confs: paper | 'qa,La,g1,..;qb,Lb,g1,..']"""
import sys, time, json
import mpmath as mp
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from capcore import *

PAPER = [(2, 3, [mp.mpf(5189) / 5000, mp.mpf(9811) / 5000]),
         (3, 4, [mp.mpf(10289) / 10000, mp.mpf(10289) / 10000, mp.mpf(9711) / 5000])]

def parse_confs(s):
    if s == 'paper': return PAPER
    out = []
    for part in s.split(';'):
        v = part.split(','); q, L = int(v[0]), int(v[1])
        out.append((q, L, [mp.mpf(x) for x in v[2:]]))
    return out

def ceiling(K, w0, confs, lo=0.6725, hi=0.6760, tol=1e-12, dps=30):
    mp.mp.dps = dps
    w = freqs(K, w0); A = Amass(w0); pre = prep(w, A, confs)
    F = lambda r: obstruction_pre(mp.mpf(r), pre)[0]
    flo, fhi = F(lo), F(hi)
    if flo < 0 or fhi > 0:
        return None, (float(flo), float(fhi))
    a, b = mp.mpf(lo), mp.mpf(hi)
    while b - a > tol:
        mid = (a + b) / 2
        if F(mid) >= 0: a = mid
        else: b = mid
    return a, None

if __name__ == '__main__':
    K = int(sys.argv[1]); w0 = mp.sqrt(2) if sys.argv[2] == 'sqrt2' else mp.mpf(sys.argv[2])
    confs = parse_confs(sys.argv[3] if len(sys.argv) > 3 else 'paper')
    t0 = time.time()
    r, bad = ceiling(K, w0, confs)
    if r is None: print('K=%d w0=%s: bracket failed F(lo), F(hi) = %s' % (K, mp.nstr(w0, 10), bad))
    else: print('K=%d w0=%s: ceiling r = %s (%.0fs)' % (K, mp.nstr(w0, 10), mp.nstr(r, 12), time.time() - t0), flush=True)
