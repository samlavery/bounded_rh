import re, sys, numpy as np
sys.set_int_max_str_digits(0)
NAME = sys.argv[1]; Q = 6
d = open(f"../../data_{NAME}.lean").read()
W = np.load('w40.npz'); gmin = W['vals'][0]
cents = []
for v, x in zip(W['vals'], W['mins']):
    if v > gmin * 1.03: break
    for y in (x, x[::-1]): cents.append(np.array(y) * 32768)
cents = np.array(cents)
dists = {'S': [], 'Z': []}; wid = {'S': [], 'Z': []}
for m in re.finditer(r"theorem (wk\d+) : \S+ ([\d ]+) :=\n  \S+covered_of_walk lbS lbD ptS (?:hR )?hbas (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+)", d):
    bits = int(m.group(3), 0); coords = [int(x) for x in m.group(5).split()]
    pos = 1; stack = [tuple((coords[2 * r], coords[2 * r + 1]) for r in range(Q))]
    while stack:
        box = stack.pop(); w = bits >> pos
        if w & 1:
            ax = (w >> 1) & 7; l, u = box[ax]; q = (l + u) >> 1
            A = list(box); A[ax] = (l, q); B = list(box); B[ax] = (q, u); pos += 4; stack += [tuple(B), tuple(A)]; continue
        kind = (w >> 1) & 3
        if kind == 1: pos += 16 if (w >> 15) & 1 else 37
        else: pos += 3
        if box[Q - 1][1] < box[0][0] or kind == 2: continue
        c = np.array([(a + b) / 2 for a, b in box]); k = 'S' if kind == 1 else 'Z'
        dists[k].append(np.abs(cents - c).max(axis=1).min() / 32768)
        wid[k].append(max(b - a for a, b in box) / 32768)
for k in ('S', 'Z'):
    a = np.array(dists[k]); print(k, len(a), 'dist pct', np.round(np.percentile(a, [10, 25, 50, 75, 90]), 3), 'width med', np.round(np.median(wid[k]), 4))
    print('  fraction within 0.1:', round(float((a < 0.1).mean()), 3), ' within 0.2:', round(float((a < 0.2).mean()), 3))
