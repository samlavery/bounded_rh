"""How often is the min over a cell's finer descendants (as the pyramid stores it) below the cell's own WZ?"""
import random
from wz import WZ
random.seed(3)
tot = worse = 0; worst = 0
for l in range(2, 14):
    for _ in range(400):
        i = random.randrange((16384 >> l), (12 * 32768) >> l)
        own = WZ(i << l, (i + 1) << l)
        for dd in (1, 2, 3):
            if l - dd < 0: continue
            m = min(WZ((i << dd) + t << (l - dd), ((i << dd) + t + 1) << (l - dd)) for t in range(1 << dd))
            tot += 1
            if m < own:
                worse += 1; worst = max(worst, (own - m) / max(own, 1))
print(f"pairs {tot}: min over descendants below own WZ in {worse} ({100*worse/tot:.2f}%), worst relative shortfall {worst:.2e}")
