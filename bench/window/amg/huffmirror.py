#!/usr/bin/env python3
"""(bridge-port) Python mirror of the Lean Huffman walk decoder (PCellHuff + genpcell3), for the golden vectors of HUFF.md.

Packs each canonical table as the kernel reads it: `cs` = the count of each code length from 0 (16-bit fields), `sy` = the
symbols in table order (16-bit fields).  `hdec` is the kernel loop step for step (a 32-bit window, at most 33 steps).  The
walk mirrors the kernel node: Jacobi tightening (NR rounds over the mask of split pairs, empty: no bits), then bit 0 split
([1][axis code], child A then child B) or leaf ([0]; reflected: nothing; else the kind bit, then the minorant terms of the
active pairs and the multiplier list, or the Farkas list).
Usage: huffmirror.py TABLES.json GOLDEN.json WINDOW.json [NR]"""
import sys, json

Q = 7; N = Q + 1
PAIRS = [(i, j) for i in range(N) for j in range(i + 1, N)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]

def pack(table):
    """(cs, sy) of a canonical table [[symbol, length], ...] sorted by (length, symbol)"""
    assert table == sorted(table, key=lambda e: (e[1], e[0])), "not canonical order"
    mx = max(l for _, l in table)
    cnt = [0] * (mx + 1)
    for _, l in table: cnt[l] += 1
    assert max(cnt) < 1 << 16 and all(s < 1 << 16 for s, _ in table) and mx <= 32
    cs = sum(c << (16 * k) for k, c in enumerate(cnt))
    sy = sum(s << (16 * k) for k, (s, _) in enumerate(table))
    return cs, sy

def hdec(cs, sy, w, o):
    """the kernel's hdec: symbol + 2^16 * length (0 when 33 steps find no codeword)"""
    y = (w >> o) & 0xFFFFFFFF; code = first = base = ln = 0
    for _ in range(33):
        cnt = cs & 0xFFFF; d = max(0, code - first)
        if d < cnt: return ((sy >> ((base + d) << 4)) & 0xFFFF) + (ln << 16)
        code = code + code + (y & 1); first = (first + cnt) << 1; base += cnt; cs >>= 16; y >>= 1; ln += 1
    return 0

def gpt(L, U, jj):
    if jj == 33: return L
    gs = 5 if (jj >> 6) & 1 else 8
    ga = ((L + (1 << gs) - 1) >> gs) << gs; gb = (U >> gs) << gs
    x = ((L + (((U - L) * (jj & 63)) >> 5)) >> gs) << gs
    return ga if x <= ga else (gb if gb <= x else x)

def main():
    T = json.load(open(sys.argv[1])); G = json.load(open(sys.argv[2])); J = json.load(open(sys.argv[3]))
    NR = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    LB = T["LB"]; YB = T["YB"]; YBF = T["YB_farkas"]
    aN = {tuple(map(int, k.split(","))): int(v) for k, v in J["aN"].items()}
    ACT = [t for t in PAIRS if aN[t] > 0]
    TT = {tuple(map(int, k.split(","))): pack(v) for k, v in T["term_tables"].items()}
    AX = pack(T["axis_table"]); CT = pack(T["c_table"])
    assert T["sum_constraints_in_rank_order"] == [f"{i},{j}" for i, j in SUMS]
    bits = int(G["walk_hex"], 16) << 1          # the kernel walk starts at position 1
    box0 = G["nodes"][0]["box"]; assert G["nodes"][0]["cons"] == {}
    BIG = 1 << 40
    stats = dict(split=0, empty=0, refl=0, M=0, F=0, termbits=0, mulbits=0, axbits=0, hsteps=0)
    golden = iter(G["nodes"]); log = []

    def tighten(l, u, A, B, M):
        for _ in range(NR):
            for ci, (i, j) in enumerate(SUMS):
                if not (M >> ci) & 1: continue
                sl = sum(l[i:j]); su = sum(u[i:j]); Le = max(A[ci], sl); Ue = min(B[ci], su)
                if Ue < Le: return None
                ol = l[i:j]; ou = u[i:j]
                for k, r in enumerate(range(i, j)):
                    l[r] = max(ol[k], Le - (su - ou[k])) if Le >= su - ou[k] else ol[k]
                    u[r] = min(ou[k], Ue - (sl - ol[k]))
        return l, u

    def ylist(w, o, qb):
        ent = []
        while (w >> o) & 1:
            cl = hdec(*CT, w, o + 1); c = cl & 0xFFFF; o1 = o + 1 + (cl >> 16)
            sd = (w >> o1) & 1; yq = (w >> (o1 + 1)) & ((1 << qb) - 1)
            ent.append((c, sd, yq)); stats["mulbits"] += (o1 + 1 + qb) - o; o = o1 + 1 + qb
        return ent, o + 1

    def node(pos, l, u, A, B, M, path):
        r = tighten(list(l), list(u), A, B, M)
        if r is None: stats["empty"] += 1; return pos
        l, u = r
        if (bits >> pos) & 1:
            al = hdec(*AX, bits, pos + 1); ax = al & 0xFFFF; p = pos + 1 + (al >> 16); stats["axbits"] += p - pos
            stats["split"] += 1
            g = next(golden, None)
            if g is not None:
                assert g["path"] == path and g["type"] == "split" and g["axis"] == ax, (g["path"], path, g.get("axis"), ax)
                assert g["bits"] == "".join(str((bits >> k) & 1) for k in range(pos, p)), path
            if ax < Q:
                m = (l[ax] + u[ax]) >> 1
                uA = list(u); uA[ax] = m; lB = list(l); lB[ax] = m
                p = node(p, l, uA, A, B, M, path + "A")
                return node(p, lB, u, A, B, M, path + "B")
            ci = ax - Q; i, j = SUMS[ci]
            m = (max(A[ci], sum(l[i:j])) + min(B[ci], sum(u[i:j]))) >> 1
            BA = list(B); BA[ci] = m; AB = list(A); AB[ci] = m
            p = node(p, l, u, A, BA, M | (1 << ci), path + "A")
            return node(p, l, u, AB, B, M | (1 << ci), path + "B")
        if u[Q - 1] < l[0]: stats["refl"] += 1; return pos + 1
        w = bits >> (pos + 2)
        if (bits >> (pos + 1)) & 1:
            ent, o = ylist(w, 0, YBF); stats["F"] += 1; log.append(("F", path, ent, pos, list(l), list(u), list(A), list(B))); return pos + 2 + o
        o = 0; terms = []
        for (i, j) in ACT:
            cs, sy = TT[(i, j)]
            sl_ = hdec(cs, sy, w, o); s = sl_ & 0xFFFF; a = s >> 14; o1 = o + (sl_ >> 16)
            if (i, j) in SUMS:
                ci = SUMS.index((i, j)); L = max(A[ci], sum(l[i:j])); U = min(B[ci], sum(u[i:j]))
            else:
                L, U = l[i], u[i]
            lam = ((w >> o1) & ((1 << LB) - 1)) if a == 2 else (((w >> o1) & ((1 << (LB - 1)) - 1)) + 1 if a == 3 else 0)
            ll = LB if a == 2 else (LB - 1 if a == 3 else 0)
            p_ = gpt(L, U, (s >> 7) & 127) if a else 0; r_ = gpt(L, U, s & 127) if a == 3 else 0
            terms.append((a, (s >> 7) & 127, s & 127, lam, p_, r_)); stats["termbits"] += o1 + ll - o; o = o1 + ll
        ent, o = ylist(w, o, YB); stats["M"] += 1; log.append(("M", path, terms, ent))
        return pos + 2 + o

    end = node(1, [b[0] for b in box0], [b[1] for b in box0], [0] * len(SUMS), [BIG] * len(SUMS), 0, "")
    print(f"end {end} (walk bits {G['walk_bits']} + 1): {'OK' if end == G['walk_bits'] + 1 else 'MISMATCH'}; {stats}")
    return end, log, TT, AX, CT, ACT

if __name__ == "__main__":
    main()
