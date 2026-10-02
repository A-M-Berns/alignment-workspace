# Common-prior deference: if the agent's evidence is coarser than the programmers', D1 holds for every X; if finer, it can fail.
from fractions import Fraction as F
import random, itertools
random.seed(3)
W=[0,1,2,3]
def EX(X,mu,cell): 
    m=sum(mu[w] for w in cell); return sum(mu[w]*X[w] for w in cell)/m if m>0 else None
def test(h_part,y_part,mu_agent,mu_prog,trials=3000):
    viol=0; tested=0
    for _ in range(trials):
        X=[F(random.randint(-9,9)) for _ in W]
        press=set()
        for cell in h_part:
            e=EX(X,mu_prog,cell)
            if e is not None and e<0: press|=set(cell)
        if not press: continue
        for ycell in y_part:
            cond=[w for w in ycell if w in press]
            if not cond: continue
            tested+=1
            if EX(X,mu_agent,cond)>0: viol+=1
    return tested,viol
full=[[0],[1],[2],[3]]; coarse=[[0,1],[2,3]]; triv=[[0,1,2,3]]
mu=[F(1,4)]*4
print("agent trivial, programmers full, common prior:      tested/violations",test(full,triv,mu,mu))
print("agent coarse, programmers full, common prior:       tested/violations",test(full,coarse,mu,mu))
print("agent full, programmers coarse, common prior:       tested/violations",test(coarse,full,mu,mu))
muA=[F(4,10),F(4,10),F(1,10),F(1,10)]; muP=[F(1,10),F(1,10),F(4,10),F(4,10)]
print("agent coarse, programmers full, heterogeneous prior:tested/violations",test(full,coarse,muA,muP))

print("agent trivial, programmers coarse, heterogeneous prior:tested/violations",test(coarse,triv,muA,muP))
print("agent trivial, programmers coarse, common prior:       tested/violations",test(coarse,triv,mu,mu))

muA2=[F(4,10),F(1,10),F(4,10),F(1,10)]; muP2=[F(1,10),F(4,10),F(1,10),F(4,10)]   # heterogeneity WITHIN the programmers' cells
print("agent trivial, programmers coarse, within-cell heterogeneous prior: tested/violations",test(coarse,triv,muA2,muP2))
print("agent coarse=programmers coarse, within-cell heterogeneous prior:    tested/violations",test(coarse,coarse,muA2,muP2))
