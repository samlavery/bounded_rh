"""EXHAUSTIVE mixed-depth cluster-slack allocation check (replaces the sampled mixed_alloc_check.py).
Classes a / b / c: radius L = 2 / 4 / 14, tail weight CW = 0.1 / 0.1 / 0.05; admissible: |s_p - s_q| >= L_p + L_q.
v_p(u) = clip(L_p + 1/2 - u, 0, 1), c_p(u) = 0.8 v_p(u) + CW_p (L_p/u)^2 [u >= L_p + 1/2].  Claim: sum_p c_p(x) <= 1 everywhere.
Proof structure (all weights are non-increasing in distance):
 (i) a point x with every v_p(x) = 0 carries only tails, bounded classwise below by T_side (each class's members on one side are
     mutually >= 2L apart, the first at >= L + 1/2) - checked < 1;
 (ii) otherwise x lies in the core/ramp of some centre q at offset u in [0, L_q + 1/2]; for fixed class sequences of the other centres
     the sum is largest at minimal separations; left and right are independent, so sup = max_u [c_q(u) + max_left + max_right];
     the first K = 10 neighbours per side are enumerated (3^10 sequences), and the rest is bounded CLASSWISE: each class's members beyond
     the K-th neighbour are >= dK + 4 away and mutually >= 2 L_class apart.
 u-grid with the breakpoints L_q -+ 1/2 included and a slope allowance (|d/du| <= 1.6 + tail slopes) x half-step."""
import itertools, numpy as np
CL = {'a': (2.0, 0.10), 'b': (4.0, 0.10), 'c': (14.0, 0.05)}
def cwt(u, L, C):
    v = np.clip(L + 0.5 - u, 0.0, 1.0); return 0.8 * v + np.where(u >= L + 0.5, C * (L / np.maximum(u, L)) ** 2, 0.0)
def classwise_tail(d0):        # sum over classes of sum_i CW L^2 / (d0 + 2 L i)^2  (members of a class are >= 2L apart)
    i = np.arange(0, 200000)
    return float(sum(np.sum(C * L ** 2 / (d0 + 2 * L * i) ** 2) for L, C in CL.values()))
# (i) x in no core/ramp: tails only, first member of each class at >= L + 1/2 on each side
Ti = 2 * float(sum(np.sum(C * (L / (L + 0.5 + 2 * L * np.arange(0, 200000))) ** 2) for L, C in CL.values()))
print('(i) points in no core or ramp: tail sum <= %.4f' % Ti, flush=True)
K = 10
seqs = np.array(list(itertools.product(range(3), repeat=K)))                 # 59049 x K, entries 0/1/2 = a/b/c
Ls = np.array([CL[t][0] for t in 'abc']); Cs = np.array([CL[t][1] for t in 'abc'])
Lseq = Ls[seqs]; Cseq = Cs[seqs]
worst = 0.0; arg = None
for qc in 'abc':
    Lq, Cq = CL[qc]
    us = np.unique(np.concatenate([np.linspace(0.0, Lq + 0.5, 6001), [Lq - 0.5, Lq + 0.5]]))
    h = float(np.max(np.diff(us)))
    # distances from s_q of the K neighbours at minimal separations: d_1 = Lq + L_1, d_k = d_{k-1} + L_{k-1} + L_k
    d = np.cumsum(np.concatenate([(Lq + Lseq[:, :1]), Lseq[:, :-1] + Lseq[:, 1:]], axis=1), axis=1)    # 59049 x K
    best_R = np.full(len(us), -np.inf); best_L = np.full(len(us), -np.inf)
    for i0 in range(0, len(us), 100):
        uu = us[i0:i0 + 100]
        dr = d[:, :, None] - uu[None, None, :]; dl = d[:, :, None] + uu[None, None, :]
        Lb = Lseq[:, :, None]; Cb = Cseq[:, :, None]
        SR = cwt(dr, Lb, Cb).sum(1).max(0); SL = cwt(dl, Lb, Cb).sum(1).max(0)
        best_R[i0:i0 + 100] = SR; best_L[i0:i0 + 100] = SL
    dK = Lq + 2.0 + 4.0 * (K - 1)                                          # smallest distance of the K-th neighbour from s_q
    rem = np.array([classwise_tail(dK + 4 - u) + classwise_tail(dK + 4 + u) for u in us[::300]]); rem = np.interp(us, us[::300], rem)
    tot = cwt(us, Lq, Cq) + best_R + best_L + rem
    slope = 1.6 + 2 * float(sum(2 * C * L ** 2 / (L + 0.5) ** 3 for L, C in CL.values()))
    m = float(tot.max()) + slope * h / 2
    i = int(np.argmax(tot))
    print('central class %s: max %.4f at u = %.3f (enumerated %.4f + remainder %.4f) + slope allowance %.4f -> %.4f'
          % (qc, tot[i], us[i], tot[i] - rem[i], rem[i], slope * h / 2, m), flush=True)
    if m > worst: worst, arg = m, (qc, float(us[i]))
print('EXHAUSTIVE: sup_x sum_p c_p(x) <= %.4f (at %s); points in no ramp <= %.4f -> %s'
      % (worst, arg, Ti, 'OK (<= 1)' if max(worst, Ti) <= 1 else 'FAILS'), flush=True)
