"""E21: where the margin of (1') sits.  For given deep configurations, split ||S_A||_q^2 = 2 int_0^1 q |S_A|^2 into
frequency bands and compare with the target 4 g0 P + 4 sum_{p,p'} h(s_p - s_p').  Configurations: the e19 arched-chain
minimiser (P = 12, printed in e19_c1_big.log), equal-depth lattices, the e9 stacks."""
import json, numpy as np
from common import *
def bands(s, y, edges=(0.0, 0.05, 0.15, 0.3, 0.5, 0.7, 0.85, 0.95, 1.0001)):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s)
    E = np.exp(2j * np.pi * np.outer(al, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    SA2 = np.abs((ch * E).sum(1)) ** 2; V2 = np.abs(E.sum(1)) ** 2
    tot = float(W2 @ SA2)
    d = s[:, None] - s[None, :]
    H = float((K_of(d.ravel()) - g_of(d.ravel())).sum())
    tgt = 4 * g0 * P + 4 * H
    parts = [float(W2[(al >= a) & (al < b)] @ SA2[(al >= a) & (al < b)]) for a, b in zip(edges[:-1], edges[1:])]
    lowV = [float(W2[(al >= a) & (al < b)] @ (4 * V2[(al >= a) & (al < b)])) for a, b in zip(edges[:-1], edges[1:])]
    return P, tot, tgt, parts, lowV, edges
cfgs = {}
cfgs['arch12'] = ([0.0, 0.761, 1.517, 2.274, 3.028, 3.775, 4.513, 5.241, 5.966, 6.691, 7.425, 8.183],
                  [0.8, 1.121, 1.325, 1.464, 1.559, 1.616, 1.633, 1.604, 1.523, 1.378, 1.152, 0.8])
for a in (0.6, 0.76, 1.0, 1.5):
    cfgs['lat a=%.2f y=.8 P=24' % a] = (list(a * np.arange(24)), [0.8] * 24)
for P in (16, 24):
    c = json.load(open('e9_cfg_%d.json' % P)); cfgs['e9 P=%d' % P] = (c['s'], c['y'])
for k, (s, y) in cfgs.items():
    P, tot, tgt, parts, lowV, edges = bands(s, y)
    print('%-22s P=%2d ||S_A||^2 = %10.2f  target 4g0P+4H = %8.2f  margin %+9.2f' % (k, P, tot, tgt, tot - tgt))
    print('    bands %s' % ' '.join('[%.2f,%.2f):%.1f' % (a, b, v) for a, b, v in zip(edges[:-1], edges[1:], parts)))
    print('    4|V|^2 by band %s' % ' '.join('%.1f' % v for v in lowV))
