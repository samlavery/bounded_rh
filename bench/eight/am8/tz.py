#!/usr/bin/env python3
"""The T1 (pair-sum triple pass) and Z (zero-order tangent extension) semantics, as plain integer functions shared by the
sizer (size8pz) and the replay verifier.  TZ.md is the specification; these functions ARE that specification in code.
Units: gaps and pair sums in 1/SC (SC = 32768); w values in 1/U (U = 10^10); slope claims P, M in 1/U1 (U1 = 10^9)."""

SC = 32768; U = 10**10; U1 = 10**9; KU1 = 2 * U1; RU = U // U1


def pairs(Q):
    return [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]


def t1(l, u, cons, Q, reclip=True):
    """One triple pass on a cell.

    l, u: gap bounds (lists of Q ints).  cons: {(i, j): (Lb, Ub)} for non-adjacent pairs (j - i >= 2); a missing pair
    or a None bound means no explicit bound.  Returns None if the cell is empty, else (l2, u2, cons2, I) where
      I[(i, j)] = [lo, hi] for every pair (the propagated intervals: the leaf's effective ranges and the split ranges),
      l2[r], u2[r] = I[(r, r + 1)] (the gaps take their adjacent-pair intervals),
      cons2 = {(i, j): (lo, hi)} for every non-adjacent pair (the persisted pair bounds of the children).
    Steps (numbered as in TZ.md 1.3):
      1. empty if any l[r] > u[r];
      2. for every pair (i, j) in pair order: lo = sum l[i:j], hi = sum u[i:j]; clip by the explicit bounds
         (lo = max(lo, Lb), hi = min(hi, Ub)); empty if lo > hi;
      3. for i = 0..Q, for j = i+2..Q, for k = i+1..j-1, with a = I(i,k), b = I(k,j), c = I(i,j), in this order:
           c.lo = max(c.lo, a.lo + b.lo);  c.hi = min(c.hi, a.hi + b.hi)
           a.lo = max(a.lo, c.lo - b.hi);  a.hi = min(a.hi, c.hi - b.lo)
           b.lo = max(b.lo, c.lo - a.hi);  b.hi = min(b.hi, c.hi - a.lo)
         (each line uses the values just written), then empty if a.lo > a.hi or b.lo > b.hi or c.lo > c.hi;
      4. gaps take their adjacent intervals (l2, u2);
      5. re-clip, every non-adjacent pair in pair order: lo = max(lo, sum l2[i:j]), hi = min(hi, sum u2[i:j]); empty if
         lo > hi.  Afterwards every interval lies within the new box sums, so the leaf's anchor L0 = sum l2 is <= lo.
    The persisted bounds cons2 are the intervals after step 5.  reclip=False skips step 5 (the pre-2026-10-03 semantics;
    for the positive control ctl_anchor.py and the golden vectors only)."""
    if any(l[r] > u[r] for r in range(Q)): return None
    I = {}
    for (i, j) in pairs(Q):
        lo, hi = sum(l[i:j]), sum(u[i:j])
        if (i, j) in cons:
            Lb, Ub = cons[(i, j)]
            if Lb is not None: lo = max(lo, Lb)
            if Ub is not None: hi = min(hi, Ub)
        if lo > hi: return None
        I[(i, j)] = [lo, hi]
    for i in range(Q + 1):
        for j in range(i + 2, Q + 1):
            for k in range(i + 1, j):
                a, b, c = I[(i, k)], I[(k, j)], I[(i, j)]
                c[0] = max(c[0], a[0] + b[0]); c[1] = min(c[1], a[1] + b[1])
                a[0] = max(a[0], c[0] - b[1]); a[1] = min(a[1], c[1] - b[0])
                b[0] = max(b[0], c[0] - a[1]); b[1] = min(b[1], c[1] - a[0])
                if a[0] > a[1] or b[0] > b[1] or c[0] > c[1]: return None
    l2 = [I[(r, r + 1)][0] for r in range(Q)]; u2 = [I[(r, r + 1)][1] for r in range(Q)]
    # step 5: a gap raised later in the pass can lift sum l2 above an interval's lower end (or sum u2 below its upper end)
    for (i, j) in pairs(Q):
        if j - i < 2 or not reclip: continue
        c = I[(i, j)]; c[0] = max(c[0], sum(l2[i:j])); c[1] = min(c[1], sum(u2[i:j]))
        if c[0] > c[1]: return None
    cons2 = {(i, j): (I[(i, j)][0], I[(i, j)][1]) for (i, j) in pairs(Q) if j - i >= 2}
    return l2, u2, cons2, I


def close(l, u, cons, Q):
    """The exact closure of a cell (candidate replacement for t1; same arguments and return shape).

    A cell is a system of difference constraints on the prefix sums x_0 = 0, x_k = g_0 + ... + g_{k-1}: every pair
    (i, j) bounds x_j - x_i.  Its closure (all-pairs shortest paths, d[a][b] = the least upper bound on x_b - x_a) gives
    every pair its exact range over the cell, so it is the tightest any propagation can reach, and it is unique: the
    kernel may compute it incrementally (close_split) while this computes it from scratch (Floyd-Warshall).  Empty iff a
    negative cycle (d[a][a] < 0).  The closed intervals satisfy sum l <= lo <= hi <= sum u for every pair."""
    if any(l[r] > u[r] for r in range(Q)): return None
    N = Q + 1; d = [[0] * N for _ in range(N)]
    for (i, j) in pairs(Q):
        lo, hi = sum(l[i:j]), sum(u[i:j])
        if (i, j) in cons:
            Lb, Ub = cons[(i, j)]
            if Lb is not None: lo = max(lo, Lb)
            if Ub is not None: hi = min(hi, Ub)
        d[i][j] = hi; d[j][i] = -lo
    for k in range(N):
        dk = d[k]
        for a in range(N):
            dak = d[a][k]; da = d[a]
            for b in range(N):
                if dak + dk[b] < da[b]: da[b] = dak + dk[b]
    if any(d[a][a] < 0 for a in range(N)): return None
    I = {(i, j): [-d[j][i], d[i][j]] for (i, j) in pairs(Q)}
    l2 = [I[(r, r + 1)][0] for r in range(Q)]; u2 = [I[(r, r + 1)][1] for r in range(Q)]
    return l2, u2, {(i, j): (I[(i, j)][0], I[(i, j)][1]) for (i, j) in pairs(Q) if j - i >= 2}, I


def close_split(I, p, q, m, side, Q, skip=False):
    """The kernel's incremental form of close: I is a closed state (every pair's [lo, hi]), the split puts hi(p, q) := m
    (side 0, child A: edge p -> q of weight m) or lo(p, q) := m (side 1, child B: edge q -> p of weight -m), with
    lo(p, q) <= m <= hi(p, q).  With D(a, b) = hi(a, b) if a < b, 0 if a = b, -lo(b, a) if a > b (all from the parent):
      side 0:  hi'(i, j) = min(hi, D(i, p) + m + D(q, j)),   lo'(i, j) = max(lo, -(D(j, p) + m + D(q, i)))
      side 1:  hi'(i, j) = min(hi, D(i, q) - m + D(p, j)),   lo'(i, j) = max(lo, -(D(j, q) - m + D(p, i)))
    (one new edge enters a shortest path at most once).  The result is close of the child, and it is never empty, since
    the new cycle has weight m - lo(p, q) >= 0 or hi(p, q) - m >= 0.  In Nat: every hi candidate is >= hi' >= lo' >= 0, so
    (positive part) - (negative part) never truncates; a lo candidate may be negative, and truncating it to 0 inside the
    max with lo >= 0 changes nothing.
    skip=True is the Lean kernel's form (PCellClose `nLo`/`nHi`): with s -> t the new edge, the candidate for d[a][b] is
    not computed when b = s or a = t, i.e. hi(i, j) is kept when j = s or i = t, lo(i, j) when i = s or j = t.  On a
    closed state those 13 candidates never bind (d[a][s] + w + d[t][s] >= d[a][s] since w + d[t][s] >= 0, and likewise
    d[t][s] + w + d[t][b] >= d[t][b]), and they are the only ones that read the split slot other than through w."""
    def D(a, b): return I[(a, b)][1] if a < b else (0 if a == b else -I[(b, a)][0])
    s, t, w = (p, q, m) if side == 0 else (q, p, -m)
    J = {}
    for (i, j) in pairs(Q):
        lo, hi = I[(i, j)]
        lo2 = lo if skip and (i == s or j == t) else max(lo, -(D(j, s) + w + D(t, i)))
        hi2 = hi if skip and (j == s or i == t) else min(hi, D(i, s) + w + D(t, j))
        J[(i, j)] = [lo2, hi2]
    return J


def zext(a, b, p, v, P, M, right, lbw, n=8, log=None):
    """Zero-order extension of the tangent at p on [a, b] (right: [a, b] = [zb, U], p <= a; left: [a, b] = [L, za],
    b <= p).  v: lo32 of the point triple at p (a lower bound of w(p), 1/U); P, M: its claims (w'(p) + 2 >= P/U1,
    2 - w'(p) >= M/U1).  The tangent with any slope d in [(P - KU1)/U1, (KU1 - M)/U1] through (p, v) must stay below
    lbw(x0, x1) (the w pyramid read, 1/U) on each of n pieces: piece k = [x0, x1], x0 = a + (b - a) k // n,
    x1 = a + (b - a) (k + 1) // n; a piece with x1 <= x0 passes.  On a piece, with s the slope numerator
    (right: KU1 - M, the largest slope, since x - p >= 0; left: P - KU1, the smallest, since x - p <= 0), the check is
        v * SC + RU * s * (x - p) <= SC * lbw(x0, x1)   for x = x0 and for x = x1."""
    s = (KU1 - M) if right else (P - KU1)
    for k in range(n):
        x0 = a + (b - a) * k // n; x1 = a + (b - a) * (k + 1) // n
        if x1 <= x0: continue
        lo = lbw(x0, x1)
        top = max(v * SC + RU * s * (x0 - p), v * SC + RU * s * (x1 - p))
        if log is not None: log.append(dict(piece=k, x0=x0, x1=x1, lb=lo, lhs=top, rhs=SC * lo, ok=top <= SC * lo))
        if top > SC * lo: return False
    return True
