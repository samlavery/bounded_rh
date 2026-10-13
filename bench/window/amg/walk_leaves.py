#!/usr/bin/env python3
"""(bridge-port) Replay the bisection walks of a seven-point data file (AMS02Data.lean format) and list their leaves:
kind, box and the leaf word (masked to its payload).  Usage: walk_leaves.py DATA.lean [KIND] [N]"""
import re, sys

PAY = {0: 3, 2: 3}


def leaves_of(bits, fuel, box):
    out = []

    def go(pos, box, fuel):
        if fuel == 0: return 0
        w = bits >> pos
        if w & 1:
            ax = (w >> 1) & 7
            l, u = box[2 * ax], box[2 * ax + 1]
            q = (l + u) >> 1
            a = list(box); a[2 * ax + 1] = q
            p = go(pos + 4, a, fuel - 1)
            if p == 0: return 0
            b = list(box); b[2 * ax] = q
            return go(p, b, fuel - 1)
        if box[11] + 1 <= box[0]: return pos + 3
        kind = (w >> 1) & 3
        if kind == 0: out.append(("z", w & 7, tuple(box))); return pos + 3
        if kind == 1:
            n = 16 if (w >> 15) & 1 else 37
            out.append(("s", w & ((1 << n) - 1), tuple(box))); return pos + n
        if kind == 2: return pos + 3
        n = 12 if (w >> 11) & 1 else 33
        out.append(("c", w & ((1 << n) - 1), tuple(box))); return pos + n

    e = go(1, list(box), fuel)
    return e, out


def walks(path):
    txt = open(path).read()
    pat = re.compile(r"covered_of_walk \(C := CEN\) lbS lbD ptS hR hbas (0x[0-9a-f]+|\d+) (\d+) ((?:\d+ ){12})(\d+) ")
    for m in pat.finditer(txt):
        bits = int(m.group(1), 0); fuel = int(m.group(2)); box = [int(x) for x in m.group(3).split()]
        yield bits, fuel, box, int(m.group(4))


if __name__ == "__main__":
    kind = sys.argv[2] if len(sys.argv) > 2 else "s"; N = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    got = 0; tot = {"z": 0, "s": 0, "c": 0}
    for bits, fuel, box, e in walks(sys.argv[1]):
        e2, lv = leaves_of(bits, fuel, box)
        assert e2 == e, (e2, e)
        for k, w, b in lv:
            tot[k] += 1
            if k == kind and got < N:
                print(w, " ".join(map(str, b))); got += 1
    print("# totals", tot, file=sys.stderr)
