# S6: (1) accuracy-increase for one proposition is strictly weaker than reflection; (2) with introspection, value-form reflection for all events implies function form; (3) TT <-> function form under INT (random sanity checks).
from fractions import Fraction as F
from itertools import combinations, product
import random, math
random.seed(7)
print("(1) underconfident-but-informative expert. Worlds (phi, cell). Expert credence Q(phi)=0.6 in cell 'h', 0.4 in cell 'l'; P(phi|h)=0.9, P(phi|l)=0.1; P(h)=P(l)=1/2.")
P={(1,'h'):F(9,20),(0,'h'):F(1,20),(1,'l'):F(1,20),(0,'l'):F(9,20)}
Q={'h':F(3,5),'l':F(2,5)}
Pphi=sum(v for k,v in P.items() if k[0]==1)
print("  P(phi)=",Pphi)
for name,c in [("h",'h'),("l",'l')]:
    print(f"  cell {name}: P(phi|cell)=",sum(v for k,v in P.items() if k[0]==1 and k[1]==c)/sum(v for k,v in P.items() if k[1]==c)," Q(phi)=",Q[c]," reflection holds:",sum(v for k,v in P.items() if k[0]==1 and k[1]==c)/sum(v for k,v in P.items() if k[1]==c)==Q[c])
def exp_loss(loss):
    q=sum(P[k]*loss(Q[k[1]],k[0]) for k in P); c=sum(P[k]*loss(Pphi,k[0]) for k in P); return q,c
brier=lambda p,y:(p-y)**2
logl=lambda p,y:-math.log(float(p) if y==1 else 1-float(p))
def thresh(t): return lambda p,y: (F(1)-t if (p>=t and y==0) else (t if (p<t and y==1) else F(0)))   # Schervish threshold loss: predict phi iff p>=t
q,c=exp_loss(brier); print("  Brier: expert",q," constant",c," expert better:",q<c)
q,c=exp_loss(logl); print("  log:   expert",round(q,4)," constant",round(c,4)," expert better:",q<c)
allth=True
for k in range(1,100):
    t=F(k,100); q,c=exp_loss(thresh(t)); allth = allth and (q<=c)
print("  every threshold loss t=0.01..0.99: expert <= constant:",allth," => (Schervish) expected accuracy non-decrease for EVERY proper score on phi, yet reflection fails.")
# TT failure at a self-referential variable: X = 1[not phi and cell h]; expert in h (INT) estimates 0.4, in l estimates 0.
X={k:(F(1) if (k[0]==0 and k[1]=='h') else F(0)) for k in P}
EQ={'h':F(2,5),'l':F(0)}
t=F(3,10); cell=[k for k in P if EQ[k[1]]>=t]; cond=sum(P[k]*X[k] for k in cell)/sum(P[k] for k in cell)
print("  Total Trust at X=1[¬phi ∧ h], t=0.3: E_P[X | E_Q X >= 0.3] =",cond," >= 0.3 ?",cond>=t," -> TT fails (bets on the expert's own state expose the miscalibration).")
print()
print("(2)+(3) random finite models with INT: branches i=1..3, sub-worlds k=1..2; state rho_i supported on branch i.")
def rand_model(reflective):
    branches=[1,2,3]; subs=[1,2]; atoms=[(i,k) for i in branches for k in subs]
    Pb={i:F(random.randint(1,5)) for i in branches}; Z=sum(Pb.values()); Pb={i:v/Z for i,v in Pb.items()}
    rho={}
    for i in branches:
        w={k:F(random.randint(1,5)) for k in subs}; Zw=sum(w.values()); rho[i]={(j,k):(w[k]/Zw if j==i else F(0)) for (j,k) in atoms}
    P={}
    for i in branches:
        if reflective: condi=rho[i]
        else:
            w={k:F(random.randint(1,5)) for k in subs}; Zw=sum(w.values()); condi={(j,k):(w[k]/Zw if j==i else F(0)) for (j,k) in atoms}
        for a in atoms: P[a]=P.get(a,F(0))+Pb[i]*condi[a]
    return atoms,P,rho,Pb
def rfun(atoms,P,rho,Pb):
    return all(P[a]/Pb[a[0]]==rho[a[0]][a] for a in atoms)
def rval_all_events(atoms,P,rho,Pb):
    for r in range(1,len(atoms)):
        for ev in combinations(atoms,r):
            ev=set(ev); cells={}
            for a in atoms:
                c=sum(rho[a[0]][b] for b in ev); cells.setdefault(c,[F(0),F(0)]); cells[c][1]+=P[a]; 
                if a in ev: cells[c][0]+=P[a]
            for c,(hit,mass) in cells.items():
                if mass>0 and hit/mass!=c: return False
    return True
def tt(atoms,P,rho,Pb,trials=200):
    for _ in range(trials):
        X={a:F(random.randint(-5,5)) for a in atoms}
        EQ={i:sum(rho[i][a]*X[a] for a in atoms) for i in (1,2,3)}
        for v in sorted(set(EQ.values())):
            hi=[a for a in atoms if EQ[a[0]]>=v]; lo=[a for a in atoms if EQ[a[0]]<=v]
            if hi and sum(P[a]*X[a] for a in hi)/sum(P[a] for a in hi)<v: return False
            if lo and sum(P[a]*X[a] for a in lo)/sum(P[a] for a in lo)>v: return False
    return True
agree=0; tot=0; ttagree=0
for trial in range(60):
    m=rand_model(reflective=(trial%2==0))
    a=rfun(*m); b=rval_all_events(*m); c=tt(*m)
    tot+=1; agree+= (a==b); ttagree+=(a==c)
print(f"  over {tot} random models (half reflective by construction): R-fun == R-val-for-all-events in {agree}/{tot};  R-fun == TT(random X, all thresholds) in {ttagree}/{tot}")
