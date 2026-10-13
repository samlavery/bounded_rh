"""out-of-band pair energy of the binding words by rank distance (phase-averaged 152-point blocks): how much of L1
an n = 9 (rank 8), n = 10 (rank <= 9), ... window would add"""
import numpy as np
from slack import K, block_points, m
words = {'abbabab q=7': [1.0451, 1.9866, 1.9866, 1.0451, 1.9758, 1.0436, 1.9759],
         'alternating': [1.9745, 1.0427],
         'dual P3 (period 3)': [1.96183, 1.03817]}
for nm, gw in words.items():
    q = len(gw); E = np.zeros(m)
    for p in range(q):
        x = block_points(gw, p, m)
        Wm = K(x[:, None] - x[None, :]) ** 2
        for k in range(1, m):
            E[k] += 2 * np.trace(Wm, offset=k) / q          # ordered pairs at rank distance k
    band = E[1:8].sum(); out = E[8:].sum()
    cum = np.cumsum(E[8:])
    print('%-20s band(1..7) %.5f  out(>=8) %.5f | rank 8 %.5f (%.0f%% of out), <=9 %.0f%%, <=15 %.0f%%, <=30 %.0f%%, <=60 %.0f%%'
          % (nm, band, out, E[8], 100 * E[8] / out, 100 * cum[1] / out, 100 * cum[7] / out, 100 * cum[22] / out, 100 * cum[52] / out))
    print('    first ranks 8..16:', np.round(E[8:17], 5))
