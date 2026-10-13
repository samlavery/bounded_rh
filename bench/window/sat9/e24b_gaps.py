"""E24b: adversarial for the exact C_B split: deep pairs placed in gaps between dense shallow blocks, so that
Re(conj V e_p) < 0 near the top of the lobe, where Delta B_p is largest.  Same quantities as e24 (imports evalcfg)."""
import numpy as np, sys, io, contextlib
src = open('e24_cells.py').read().split('for P in (16, 24, 32, 48):')[0]
exec(src)
for Y in (1.5, 3.0, 5.0, 10.0, 20.0):
    for G in (1.0, 1.5, 2.0, 3.0, 4.0):
        blk = 0.6 * np.arange(8); s = np.concatenate([blk, blk + 4.2 + G, blk + 2 * (4.2 + G)])
        gaps = [4.2 + G / 2, 2 * (4.2 + G) - G / 2]
        s = np.concatenate([s, gaps]); y = np.concatenate([np.full(24, 0.8), np.full(2, Y)])
        evalcfg('3 blocks@0.8, 2 deep@Y=%g in gaps G=%.1f' % (Y, G), s, y)
