import sys; sys.path.insert(0,'.')
import numpy as np
from size7s import run, PAIRS, NP, SC, U, U1, KU1, RU, TS, Q, frq
from sevenw import w1 as w1f, w as wf
d=np.load('w40.npz'); aN=[int(x) for x in d['aN']]; bN=[int(x) for x in d['bN']]
gmin=float(d['vals'][0])*1e8; cN=int(gmin*(1-0.003)); CSU=cN*SC*U
R=run(cN,aN,bN,probe=True,PED=6,DFUEL=14,DLO=5,DHI=6)
lbw,lbP,lbM,pw,pd=R['est']
x=d['mins'][0]; q=[int(round(v*SC)) for v in x]; HW=1475
box=tuple((qq-HW,qq+HW) for qq in q)
tot_lin=0
for t,(i,j) in enumerate(PAIRS):
    lo=sum(b[0] for b in box[i:j]); hi=sum(b[1] for b in box[i:j]); qt=sum(q[i:j])
    p_,m_=pd(qt)
    up=(hi-qt)*max(0,4*U1-m_-lbP(qt,hi)); dn=(qt-lo)*max(0,4*U1-lbM(lo,qt)-p_)
    ich=aN[t]*max(up,dn)*RU/(SC*U)
    w1q=w1f(qt/SC)
    fup=max(0.0,w1q-frq('lo',qt,hi))*(hi-qt)/SC; fdn=max(0.0,frq('hi',lo,qt)-w1q)*(qt-lo)/SC
    fch=aN[t]*max(fup,fdn)/1e8*1e8/1e8
    print(t,(i,j),f"int charge {ich:.0f}  float charge {aN[t]*max(fup,fdn)/1e8*1e8:.0f}  (1e-8 units)")
# linear part
pen=0
for k in range(Q):
    AT=sum(aN[t] for t in TS[k]); Pt={t:pd(sum(q[PAIRS[t][0]:PAIRS[t][1]])) for t in TS[k]}
    Pos=max(0,U1*bN[k]+KU1*AT-sum(aN[t]*Pt[t][1] for t in TS[k])); Neg=max(0,KU1*AT-U1*bN[k]-sum(aN[t]*Pt[t][0] for t in TS[k]))
    pen+=(q[k]-box[k][0])*Pos+(box[k][1]-q[k])*Neg
    g=bN[k]/1e8+sum(aN[t]/1e8*w1f(sum(x[PAIRS[t][0]:PAIRS[t][1]])) for t in TS[k])
    print('gap',k,'Pos',Pos/1e17,'Neg',Neg/1e17,'exact grad at min',g)
print('linear penalty',pen*RU/(SC*U))
val=U*sum(bN[k]*q[k] for k in range(Q))+SC*sum(aN[t]*pw(sum(q[i:j])) for t,(i,j) in enumerate(PAIRS))
print('G(q)-c (int)',(val-CSU)/(SC*U))
