"""per-chunk leaf counts of the walk chunks in data_<NAME>.lean (decoded from the bit words)"""
import re, sys
sys.set_int_max_str_digits(0)
NAME = sys.argv[1]
d = open(f"../../data_{NAME}.lean").read()
Q = 6; NP = 21
res = {}
for m in re.finditer(r"theorem (wk\d+) : \S+ ([\d ]+) :=\n  \S+covered_of_walk (?:\(C := CEN\) )?lbS lbD ptS (?:hR )?hbas (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+)", d):
    name = m.group(1); bits = int(m.group(3), 0); L = int(m.group(6))
    coords = [int(x) for x in m.group(5).split()]
    pos = 1; cnt = {'Z': 0, 'S': 0, 'SF': 0, 'B': 0, 'R': 0}
    stack = [tuple((coords[2 * r], coords[2 * r + 1]) for r in range(Q))]
    while stack:
        box = stack.pop()
        w = bits >> pos
        if w & 1:
            ax = (w >> 1) & 7; l, u = box[ax]; q = (l + u) >> 1
            A = list(box); A[ax] = (l, q); B = list(box); B[ax] = (q, u)
            pos += 4; stack.append(tuple(B)); stack.append(tuple(A))
        else:
            kind = (w >> 1) & 3
            if box[Q - 1][1] < box[0][0]: cnt['R'] += 1; pos += 3
            elif kind == 0: cnt['Z'] += 1; pos += 3
            elif kind == 1:
                fl = (w >> 15) & 1
                if fl: cnt['SF'] += 1; pos += 16
                else: cnt['S'] += 1; pos += 37
            elif kind == 3:
                fl = (w >> 7) & 1; cnt['S'] += 1; pos += 8 if fl else 29
            else: cnt['B'] += 1; pos += 3
    assert pos == L, (name, pos, L)
    res[name] = cnt
import json
json.dump(res, open(f"walkstat_{NAME}.json", "w"))
tot = {k: sum(c[k] for c in res.values()) for k in ['Z', 'S', 'SF', 'B', 'R']}
print(len(res), tot)
