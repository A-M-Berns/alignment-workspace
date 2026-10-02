# Brief A: the selection worry. Exact arithmetic with Fractions.
from fractions import Fraction as F
from itertools import product

def E(dist, X): return sum(dist[w]*X[w] for w in dist)
def cond(P, cell):
    Z = sum(P[w] for w in cell)
    return {w: (P[w]/Z if w in cell else F(0)) for w in P}
def cellof(part, w): return next(c for c in part if w in c)
def est(P, part, X): return {w: E(cond(P, cellof(part, w)), X) for w in P}

print("== T1: argmax over unbiased NON-Bayesian (noisy) candidates ==")
delta = F(1,10)
worlds = [(o,ea,eb) for o in (1,2) for ea in (-1,1) for eb in (-1,1)]
P = {w: F(1,8) for w in worlds}
X = {w: F(1) if w[0]==1 else F(0) for w in worlds}
est_a = {w: F(1,2)+w[1]*delta for w in worlds}
est_b = {w: F(1,2)+w[2]*delta for w in worlds}
print(" E X =", E(P,X), "| E est_a =", E(P,est_a), "| E est_b =", E(P,est_b))
mx = {w: max(est_a[w],est_b[w]) for w in worlds}
print(" E[max_k est_k] =", E(P,mx), " vs 1/2+delta/2 =", F(1,2)+delta/2)

print("== T2: selective forgetting ==")
worlds=[1,2]; P={1:F(1,2),2:F(1,2)}; X={1:F(1),2:F(0)}
full={w: X[w] for w in worlds}          # E_{P(.|omega)} X = X(omega)
none={w: E(P,X) for w in worlds}        # E_P X
chosen={w: max(full[w],none[w]) for w in worlds}
print(" E[chosen estimate] =", E(P,chosen), " (E X =", E(P,X), ")")
worlds=[1,2,3,4]; P={w:F(1,4) for w in worlds}; X={1:F(3),2:F(-1),3:F(2),4:F(0)}
m=E(P,X); print(" 4-world: E X =", m, "| E max(X,EX) =", E(P,{w:max(X[w],m) for w in worlds}))

print("== T3: Bayesian refinements, all selection rules enumerated ==")
worlds=[1,2,3,4,5,6]
P={1:F(1,12),2:F(2,12),3:F(3,12),4:F(1,12),5:F(2,12),6:F(3,12)}
X={1:F(5),2:F(-2),3:F(1),4:F(4),5:F(0),6:F(-3)}
Y={1:F(2),2:F(7),3:F(-1),4:F(0),5:F(3),6:F(1)}
Z={1:F(1),2:F(1),3:F(4),4:F(-2),5:F(2),6:F(0)}
F1=[{1},{2,3},{4},{5,6}]; F2=[{1,2},{3},{4,5},{6}]; F3=[{1,2,3},{4,5,6}]
def run(G, parts, V):
    ests=[est(P,part,V) for part in parts]; base=E(P,V); out=[]
    for rule in product(range(len(parts)), repeat=len(G)):
        sel={w: ests[rule[next(i for i,c in enumerate(G) if w in c)]][w] for w in P}
        out.append((E(P,sel)-base, rule))
    return base, out
G=[{1,2,3},{4,5,6}]
base,devs=run(G,[F1,F2,F3],X)
print(" case (i)  G coarser than every F_k: E X =", base, "| max |E[E_{rho^s}X]-EX| over", len(devs), "rules =", max(abs(d) for d,_ in devs))
Gfine=[{w} for w in worlds]
base,devs=run(Gfine,[F1,F2,F3],X)
worst=max(devs,key=lambda t:abs(t[0]))
print(" case (ii) G = full information: max deviation =", worst[0], "at rule", worst[1], "| rules:", len(devs))
# argmax selection specifically:
ests=[est(P,part,X) for part in [F1,F2,F3]]
sel={w: max(e[w] for e in ests) for w in worlds}
print(" case (ii) argmax rule: E[E_{rho^s}X] =", E(P,sel), " vs E X =", E(P,X))

print("== T4: optional stopping, all rules tau<=3 ==")
prior=F(1,2); l1={1:F(4,5),0:F(1,5)}; l0={1:F(3,10),0:F(7,10)}
def post(h):
    a=prior; b=1-prior
    for o in h: a*=l1[o]; b*=l0[o]
    return a/(a+b)
def prob(h):
    a=prior; b=1-prior
    for o in h: a*=l1[o]; b*=l0[o]
    return a+b
hist1=[(o,) for o in (0,1)]; hist2=[(o1,o2) for o1 in (0,1) for o2 in (0,1)]
count=0; bad=0
for stop1 in product((0,1),repeat=2):          # stop after o1? indexed by o1
    for stop2 in product((0,1),repeat=4):      # stop after o2? indexed by (o1,o2)
        count+=1; tot=F(0)
        for h1 in hist1:
            if stop1[h1[0]]: tot+=prob(h1)*post(h1); continue
            for o2 in (0,1):
                h2=h1+(o2,)
                if stop2[hist2.index(h2)]: tot+=prob(h2)*post(h2); continue
                for o3 in (0,1):
                    h3=h2+(o3,); tot+=prob(h3)*post(h3)
        if tot!=prior: bad+=1
print(" rules enumerated:", count, "| rules with E[posterior at tau] != 1/2:", bad)

print("== T5: compensation c(rho)=E_rho Y - E_rho Z ==")
def comp_dev(G, parts):
    estY=[est(P,part,Y) for part in parts]; estZ=[est(P,part,Z) for part in parts]
    base=E(P,Y)-E(P,Z); vals=set()
    for rule in product(range(len(parts)), repeat=len(G)):
        idx={w: rule[next(i for i,c in enumerate(G) if w in c)] for w in P}
        c={w: estY[idx[w]][w]-estZ[idx[w]][w] for w in P}
        vals.add(E(P,c)-base)
    return vals
print(" case (i)  set of E[c(rho^s)]-c(P) over rules:", comp_dev(G,[F1,F2,F3]))
v=comp_dev(Gfine,[F1,F2,F3]); print(" case (ii) number of distinct values:", len(v), "| max:", max(v), "| min:", min(v))
