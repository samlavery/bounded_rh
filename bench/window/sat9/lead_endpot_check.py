import numpy as np
# q(al) = (1-|al|)^2 on [-1,1]; closed form of int_0^1 (1-al)^2 e^{z al} d al
def I(z):
    z = np.asarray(z, dtype=complex)
    out = np.empty_like(z)
    small = np.abs(z) < 1e-3
    zs = z[small]; out[small] = 1/3 + zs/12 + zs**2/60
    zl = z[~small]; out[~small] = (2*np.exp(zl) - (zl**2 + 2*zl + 2))/zl**3
    return out
def L(u, y):  # (q B_y)^vee(u), two-sided
    u = np.asarray(u, float); c = 2*np.pi*y; w = 2*np.pi*u
    return 2*np.real(I(c+1j*w) + I(-c+1j*w) - 2*I(1j*w))
rng = np.random.default_rng(1)
for a in (0.6, 0.76, 0.9):
  for P in (5, 9, 16):
    ys = rng.uniform(0.8, 1.6, P)
    X = 4*sum(L((p-pp)*a, ys[p]) for p in range(P) for pp in range(P))
    K = 400000; ks = np.arange(K)
    E = 0.0; pois = []
    for p in range(P):
        Lk = L(ks*a, ys[p]); tail = np.cumsum(Lk[::-1])[::-1]   # tail[j] = sum_{k>=j}
        E += -4*(tail[p+1] + tail[P-p]); pois.append(Lk[0] + 2*tail[1])
    print(f"a={a} P={P}: direct={X:.6f}  endpot={E:.6f}  max|Poisson|={max(map(abs,pois)):.2e}")

print("--- one-body end potentials U_p(y) = -4[Lam_y(p+1)+Lam_y(P-p)], generic q, P=200 (half-chain view)")
ys = np.linspace(0.8, 3.0, 45); K = 400000; ks = np.arange(K)
for a in (0.6, 0.76, 0.9):
    tails = []
    for y in ys:
        Lk = L(ks*a, y); tails.append(np.cumsum(Lk[::-1])[::-1])
    tails = np.array(tails)          # tails[iy, j]
    P = 200
    mins = []
    for p in range(8):
        U = -4*(tails[:, p+1] + tails[:, P-p])
        mins.append((p, U.min(), ys[U.argmin()]))
    s = sum(m[1] for m in mins)
    print(f"a={a}: " + "  ".join(f"p{p}:{m:.3g}@y{yy:.2f}" for p,m,yy in mins) + f"   sum(min, p<8)={s:.4g}")
