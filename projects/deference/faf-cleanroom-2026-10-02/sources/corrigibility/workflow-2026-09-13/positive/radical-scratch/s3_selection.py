# S3: optional stopping preserves reflection; selection among estimators at face value breaks it; conditioning on the selection restores it.
from fractions import Fraction as F
from itertools import product
th=[F(1,3),F(2,3)]; prior=[F(1,2),F(1,2)]   # theta = P(heads); phi = {theta=2/3}
N=3
def post(seq):  # P(theta=2/3 | seq)
    l=[prior[k]*th[k]**seq.count(1)*(1-th[k])**(len(seq)-seq.count(1)) for k in range(2)]
    return l[1]/(l[0]+l[1])
def pseq(seq): # marginal prob of sequence
    return sum(prior[k]*th[k]**seq.count(1)*(1-th[k])**(len(seq)-seq.count(1)) for k in range(2))
def pjoint(seq): # P(phi and seq)
    return prior[1]*th[1]**seq.count(1)*(1-th[1])**(len(seq)-seq.count(1))
leaves=list(product([0,1],repeat=N))
# (i) enumerate all adapted stopping rules on the depth-N binary tree (full prefix-free covers)
def rules(d):
    if d==0: return [[()]]
    out=[[()]]
    for r0 in rules(d-1):
        for r1 in rules(d-1):
            out.append([(0,)+p for p in r0]+[(1,)+p for p in r1])
    return out
R=rules(N); print("number of adapted stopping rules on depth-3 tree:",len(R))
allok=True
for r in R:
    # stopping node for each leaf = unique prefix in r
    vals={}
    for leaf in leaves:
        node=[p for p in r if leaf[:len(p)]==p]; assert len(node)==1; node=node[0]
        c=post(list(node)); vals.setdefault(c,[F(0),F(0)]); vals[c][0]+=pjoint(leaf); vals[c][1]+=pseq(leaf)
    E=sum(c*v[1] for c,v in vals.items())
    refl=all(v[0]/v[1]==c for c,v in vals.items())
    allok = allok and (E==F(1,2)) and refl
print("(i) every adapted stopping rule: E[P_tau]=1/2 and P(phi | P_tau=c)=c for all c:",allok)
# (ii) non-adapted: stop at the first time achieving the path-maximum of P_t (uses the future)
vals={}
for leaf in leaves:
    ps=[post(list(leaf[:t])) for t in range(N+1)]; m=max(ps); c=m
    vals.setdefault(c,[F(0),F(0)]); vals[c][0]+=pjoint(leaf); vals[c][1]+=pseq(leaf)
E=sum(c*v[1] for c,v in vals.items())
print("(ii) non-adapted 'stop at path max': E[P_tau*] =",E,"(>1/2:",E>F(1,2),");  P(phi|P_tau*=c) vs c:",[(str(c),str(v[0]/v[1])) for c,v in sorted(vals.items())])
# (iii) selection among two estimators: two independent flips X1,X2 of the same coin; rho_i = P(phi | X_i); adopt the larger.
vals_face={}; vals_cond={}
for x1,x2 in product([0,1],repeat=2):
    r1=post([x1]); r2=post([x2]); sigma=1 if r1>=r2 else 2; adopted=max(r1,r2)
    pj=pjoint([x1,x2]); ps=pseq([x1,x2])
    vals_face.setdefault(adopted,[F(0),F(0)]); vals_face[adopted][0]+=pj; vals_face[adopted][1]+=ps
    key=(sigma,adopted); vals_cond.setdefault(key,[F(0),F(0)]); vals_cond[key][0]+=pj; vals_cond[key][1]+=ps
Ef=sum(c*v[1] for c,v in vals_face.items())
print("(iii) face-value adoption of the larger estimate: E[rho_sigma] =",Ef,"(>1/2:",Ef>F(1,2),");  P(phi | rho_sigma=c) vs c:",[(str(c),str(v[0]/v[1])) for c,v in sorted(vals_face.items())])
print("     conditioning on the selection event (sigma, rho_sigma): P(phi | sigma, rho_sigma) =",[(k[0],str(k[1]),str(v[0]/v[1])) for k,v in sorted(vals_cond.items())])
Ec=sum((v[0]/v[1])*v[1] for v in vals_cond.values())
print("     the selection-aware estimator P(phi|sigma,rho_sigma) is a martingale (mean 1/2):",Ec==F(1,2),"and reflective by construction (it is a conditional probability).")
# (iv) adapted choice of *which experiment to run* next (a policy), based on X1: flip the coin again if X1=1, else consult a sensor S with P(S=1|theta=2/3)=9/10, P(S=1|theta=1/3)=1/5
def sens(k,s): return (F(9,10) if s==1 else F(1,10)) if k==1 else (F(1,5) if s==1 else F(4,5))
vals={}
for x1 in [0,1]:
    for y in [0,1]:
        # joint over theta
        if x1==1:
            l=[prior[k]*th[k]*(th[k] if y==1 else 1-th[k]) for k in range(2)]
        else:
            l=[prior[k]*(1-th[k])*sens(k,y) for k in range(2)]
        c=l[1]/(l[0]+l[1]); vals.setdefault(c,[F(0),F(0)]); vals[c][0]+=l[1]; vals[c][1]+=l[0]+l[1]
E=sum(c*v[1] for c,v in vals.items()); refl=all(v[0]/v[1]==c for c,v in vals.items())
print("(iv) adapted choice among experiments (a policy): E[P_2]=",E," reflective:",refl)
