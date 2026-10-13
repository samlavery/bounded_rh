"""wctab.py: Lean literals of the round-13 walk-code tables (canonical, from the spec's length maps) — am-cert"""
import json
def canon(lengths):
    """lengths {sym: len} -> (cP, sP_list) with counts per length 1..15 (8 bits each at 8(l-1)), symbols in (len, sym) order"""
    syms = sorted(lengths, key=lambda s: (lengths[s], s))
    cnt = [0] * 16
    for s in syms: cnt[lengths[s]] += 1
    cP = sum(cnt[l] << (8 * (l - 1)) for l in range(1, 16))
    return cP, syms
def pack(syms, W): return sum(s << (W * i) for i, s in enumerate(syms))
def tables(spec_path):
    S = json.load(open(spec_path))
    A = {int(q): canon({int(s): l for s, l in v.items()}) for q, v in S['A']['contexts'].items()}
    B = {tuple(map(int, k.split(','))): canon({int(s): l for s, l in v.items()}) for k, v in S['B']['contexts'].items()}
    C = {int(k): canon({int(s): l for s, l in v.items()}) for k, v in S['C']['contexts'].items()}
    return S, {q: (c, pack(sy, 5)) for q, (c, sy) in A.items()}, {k: (c, pack(sy, 8)) for k, (c, sy) in B.items()}, C
def py_dec(cP, sP, W, esc, rb, w, o):
    """the Lean hcDec, in Python (for the unit test)"""
    l = code = first = off = 0
    for _ in range(15):
        c = 2 * code + ((w >> o) & 1); n = (cP >> (8 * l)) & 255
        if first <= c < first + n:
            s = (sP >> (W * (off + c - first))) & ((1 << W) - 1); o += 1
            if s == esc: return (w >> o) & ((1 << rb) - 1), o + rb
            return s, o
        l += 1; code = c; first = (first + n) << 1; off += n; o += 1
    raise ValueError
