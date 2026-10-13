import re, sys
DZ=10**15; DZ2=5*10**14; PLN=314159265358979323846; PUN=PLN+1; GLN=8274992907; GUN=8274993018
ERRD=2262000; SC=2**96; SW=10**13; P20=10**20; P10=10**10
def ndiv(a,b): return a//b
def ndivc(a,b): return (a+b-1)//b
def nsub(a,b): return a-b if a>=b else 0
def cosP(T): return 3628800*DZ**10 + 151200*T**4*DZ**6 + 90*T**8*DZ**2
def cosN(T): return 1814400*T**2*DZ**8 + 5040*T**6*DZ**4 + T**10
def sinP(T): return 39916800*T*DZ**10 + 332640*T**5*DZ**6 + 110*T**9*DZ**2
def sinN(T): return 6652800*T**3*DZ**8 + 7920*T**7*DZ**4 + T**11
def cosLo(T): return ndiv(nsub(cosP(T),cosN(T)), 3628800*DZ**9)
def cosHi(T): return ndivc(nsub(cosP(T),cosN(T)), 3628800*DZ**9)
def sinLo(T): return ndiv(nsub(sinP(T),sinN(T)), 39916800*DZ**10)
def sinHi(T): return ndivc(nsub(sinP(T),sinN(T)), 39916800*DZ**10)
def zfdiv(z): return ndiv(z,DZ) if z>=0 else -ndivc(-z,DZ)
def zcdiv(z): return ndivc(z,DZ) if z>=0 else -ndiv(-z,DZ)
def imulZZ(e,I): return (e*I[0],e*I[1]) if e>=0 else (e*I[1],e*I[0])
def iaddZ(I,J): return (I[0]+J[0], I[1]+J[1])
def isubZ(I,J): return (I[0]-J[1], I[1]-J[0])
def csA(k):
    c,s = 1,0
    for _ in range(k): c,s = -s,c
    return c,s
def okZ(LN,UN,k,side,WN, why=False):
    LLO=ndiv(LN*DZ,SC); UHI=ndivc(UN*DZ,SC); AD=k*DZ2
    RLO = nsub(LLO,AD) if side else nsub(AD,UHI)
    RHI = nsub(UHI,AD) if side else nsub(AD,LLO)
    TLZ=ndiv(PLN*RLO,P20); TUZ=ndivc(PUN*RHI,P20)
    CLZ=cosLo(TUZ)-ERRD; CUZ=cosHi(TLZ)+ERRD; SLZ=sinLo(TLZ)-ERRD; SUZ=sinHi(TUZ)+ERRD
    cA,sA=csA(k)
    if side:
        CXZ=isubZ(imulZZ(cA,(CLZ,CUZ)), imulZZ(sA,(SLZ,SUZ))); SXZ=iaddZ(imulZZ(sA,(CLZ,CUZ)), imulZZ(cA,(SLZ,SUZ)))
    else:
        CXZ=iaddZ(imulZZ(cA,(CLZ,CUZ)), imulZZ(sA,(SLZ,SUZ))); SXZ=isubZ(imulZZ(sA,(CLZ,CUZ)), imulZZ(cA,(SLZ,SUZ)))
    BLZ=ndiv(PLN*LLO,P20); BUZ=ndivc(PUN*UHI,P20)
    P2LZ=ndiv(2*GLN*BLZ,P10); P2UZ=ndivc(2*GUN*BUZ,P10)
    TLOZ=zfdiv(min(P2LZ*SXZ[0], P2UZ*SXZ[0])); THIZ=zcdiv(max(P2LZ*SXZ[1], P2UZ*SXZ[1]))
    NLOZ=max(0, max(CXZ[0]-THIZ, TLOZ-CXZ[1]))
    DHIZ=ndivc(2*BUZ*BUZ,DZ)-DZ
    conds = [LN<=UN, TUZ<=DZ, (k*SC<=2*LN if side else 2*UN<=k*SC), cosN(TUZ)<=cosP(TUZ), cosN(TLZ)<=cosP(TLZ),
             sinN(TLZ)<=sinP(TLZ), sinN(TUZ)<=sinP(TUZ), DZ*DZ < 2*BLZ*BLZ, 0<DHIZ, WN*DHIZ*DHIZ <= NLOZ*NLOZ*SW]
    if why: return conds, (NLOZ, DHIZ, WN)
    return all(conds)
for fn in sys.argv[1:]:
    s = open(fn, encoding="utf-8").read()
    cells = re.findall(r"⟨(\d+),\s*(\d+),\s*(\d+),\s*(true|false),\s*(\d+)⟩", s)
    bad = []; margins = []
    for LN,UN,k,side,WN in cells:
        LN,UN,k,WN = int(LN),int(UN),int(k),int(WN); side = side=="true"
        conds,(NLOZ,DHIZ,W) = okZ(LN,UN,k,side,WN, why=True)
        if not all(conds): bad.append((LN,UN,k,side,WN,conds))
        if DHIZ>0: margins.append((NLOZ*NLOZ*SW)/(DHIZ*DHIZ)/W if W>0 else float('inf'))
    print(f"{fn}: cells={len(cells)} fail={len(bad)} min margin (certified/claimed) = {min(margins):.6f}")
    for b in bad[:5]: print("   FAIL", b)
