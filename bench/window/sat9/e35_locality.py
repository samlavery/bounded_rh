"""E35: is the optimal dual witness w* local?  (a) regime A (positions-only witnesses, e34_witness.json): transplant test -
build w for the P = 48 lattice from the P = 24 witness (end patterns of radius r copied from each end, interior filled by the
P = 24 central value), evaluate the certified hard D (valid lower bound) and compare with the optimum.  (b) regime B (class
reduction, K = 2, e23 P = 32): sensitivity of w* to a local change (one label flipped / one position moved by 0.05): |Delta w_n|
against distance from the change, and the loss of a truncated update (keep the old w* beyond radius r)."""
import json, numpy as np
exec(open('e32d_qp.py').read().rsplit("if __name__ == '__main__':", 1)[0])
wit = json.load(open('e34_witness.json'))
def hardD(s, t, w):
    s = np.asarray(s); t = np.asarray(t); base = 4 * Lmat(s[:, None] - s[None, :]).sum(2); M = 4 * Lmat(s[:, None] - t[None, :])
    G = Kmat(t[:, None] - t[None, :]); ob = base + np.einsum('kpn,n->kp', M, w); return Tg(s) + ob.min(0).sum() - 4 * w @ G @ w
print('(a) regime A transplant: w(P=48) built from w*(P=24) with end radius r')
for a in (0.6, 0.7, 0.76, 0.8):
    w24 = np.array(wit['a=%.2f P=24' % a]['w']); w48 = np.array(wit['a=%.2f P=48' % a]['w'])
    s48 = np.array(wit['a=%.2f P=48' % a]['s']); t48 = np.array(wit['a=%.2f P=48' % a]['t']); D48 = wit['a=%.2f P=48' % a]['D_hard']
    n24, n48 = len(w24), len(w48); mid = w24[n24 // 2]
    # interior structure of the optimum
    print('  a=%.2f: w*(P=48) end entries %s ... interior mean %.4f std %.4f | w*(P=24) end %s' % (a, np.round(w48[:6], 3).tolist(),
          w48[12:-12].mean(), w48[12:-12].std(), np.round(w24[:6], 3).tolist()))
    for r in (2, 4, 6, 8, 12):
        w = np.full(n48, mid); w[:r] = w24[:r]; w[-r:] = w24[-r:]
        print('     r=%2d: D_hard(transplant) %+9.3f vs optimum %+9.3f (loss %.3f)' % (r, hardD(s48, t48, w), D48, D48 - hardD(s48, t48, w)))
print('(b) regime B sensitivity (K = 2 class reduction, e23 P = 32)')
exec(open('e33_classK.py').read().split("if __name__ == '__main__':")[0])
c = json.load(open('e23_arch_32.json')); s = np.sort(np.array(c['s'])); res = json.load(open('e33_results.json'))
lab = np.array(res['e23 minimiser P=32 K=2']['labels_min'])
Sc = Setup(s, 2, 0.02); Sf = Setup(s, 2, 0.005); J = Sc.J; t = Sc.t
o0, w0 = solveQP(Sc, lab); D0 = hardval(Sf, lab, w0)
W0 = w0.reshape(len(t), J)
for (kind, p) in (('flip', 16), ('flip', 4), ('move', 16)):
    lab2 = lab.copy(); s2 = s.copy()
    if kind == 'flip': lab2[p] = 1 - lab2[p]
    else: s2[p] += 0.05
    Sc2 = Setup(s2, 2, 0.02) if kind == 'move' else Sc; Sf2 = Setup(s2, 2, 0.005) if kind == 'move' else Sf
    o1, w1 = solveQP(Sc2, lab2); D1 = hardval(Sf2, lab2, w1); W1 = w1.reshape(len(Sc2.t), J)
    dist = np.abs(Sc2.t - s2[p]); dw = np.abs(W1 - W0).max(1)
    print('  %s pair %d: D %+.3f -> %+.3f | max|dw_n| by distance: %s' % (kind, p, D0, D1,
          ' '.join('d<%g:%.2e' % (r, dw[(dist < r) & (dist >= r / 2 if r > 1 else True)].max() if np.any((dist < r) & (dist >= (r / 2 if r > 1 else 0))) else 0) for r in (1, 2, 4, 8, 16, 32))))
    for r in (1, 2, 4, 8, 16):
        wt = W0.copy(); near = dist < r; wt[near] = W1[near]
        print('     truncated update radius %2d: D_hard %+.3f (optimum %+.3f, loss %.3f)' % (r, hardval(Sf2, lab2, wt.ravel()), D1, D1 - hardval(Sf2, lab2, wt.ravel())))
