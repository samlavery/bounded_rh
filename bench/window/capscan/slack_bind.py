"""L1 / L2c / L2l / L3 at F's own binding words (as is, own mean gap), PC8SF constants; kappa per link via
d kappa ~ r s / (m - R) (r = 0.6734832, R = g(c(m-q)))."""
import json
import numpy as np
from slack import word_report, R, m
kap = 0.6734832
words = {'abbabab q=7 (c_erg word)': [1.0451, 1.9866, 1.9866, 1.0451, 1.9758, 1.0436, 1.9759],
         'alternating [1.9745,1.0427]': [1.9745, 1.0427]}
out = {}
for k, gw in words.items():
    avg, L = word_report(gw, k)
    conv = {x: kap * L[x] / (m - R) for x in ('L1', 'L2c', 'L2l', 'L3', 'S')}
    print('%s  mean gap %.5f  eigen [%.4f, %.4f]' % (k, sum(gw) / len(gw), avg['lmin'], avg['lmax']))
    print('  per block: trPhi %.6f Eband %.6f PairSum %.6f Press %.6f (PairSum+Press %.6f vs c(m-q) %.6f)'
          % (avg['trPhi'], avg['Eband'], avg['pair'], avg['press'], avg['pair'] + avg['press'], 0.00805124 * (m - 7)))
    print('  slack per block: L1 %.6f L2c %.6f L2l %.6f L3 %.6f total %.6f' % (L['L1'], L['L2c'], L['L2l'], L['L3'], L['S']))
    print('  kappa ceilings: L1 %.3e  L2c %.3e  L2l %.3e  L2 %.3e  L3 %.3e  all %.3e'
          % (conv['L1'], conv['L2c'], conv['L2l'], conv['L2c'] + conv['L2l'], conv['L3'], conv['S']))
    print('  kappa if L1 alone removed (ideal n = 9 limit): %.7f' % (kap + conv['L1']))
    out[k] = dict(avg=avg, slack=L, kappa_link=conv)
json.dump(out, open('slack_bind_r8.json', 'w'), indent=1)
