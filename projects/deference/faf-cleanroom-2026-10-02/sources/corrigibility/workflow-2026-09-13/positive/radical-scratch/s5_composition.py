# S5: composition of reflection/legitimacy across three times; function-form vs value-form at step 1.
from fractions import Fraction as F
# atoms (phi, b1, b2). Time-1 credence depends on b1 (branch A or B); time-2 credence depends on (b1,b2).
atoms=[(p,b1,b2) for p in (1,0) for b1 in 'AB' for b2 in 'ab']
def cond(mu,pred): 
    Z=sum(v for k,v in mu.items() if pred(k)); return {k:(v/Z if pred(k) else F(0)) for k,v in mu.items()}
def prob(mu,pred): return sum(v for k,v in mu.items() if pred(k))
# P_0: branch A conditional is uniform over (phi,b2); branch B conditional biased.
P0={}
for (p,b1,b2) in atoms:
    if b1=='A': P0[(p,b1,b2)]=F(1,2)*F(1,4)
    else: P0[(p,b1,b2)]=F(1,2)*{(1,'a'):F(3,8),(1,'b'):F(1,8),(0,'a'):F(1,8),(0,'b'):F(3,8)}[(p,b2)]
assert sum(P0.values())==1
# time-1 credences (INT: supported on own branch)
rhoA={k:F(0) for k in atoms}; rhoB={k:F(0) for k in atoms}
for (p,b1,b2) in atoms:
    if b1=='A': rhoA[(p,b1,b2)]={(1,'a'):F(3,8),(1,'b'):F(1,8),(0,'a'):F(1,8),(0,'b'):F(3,8)}[(p,b2)]   # same phi-marginal 1/2 as P0(.|A), different correlation with b2
    else: rhoB[(p,b1,b2)]=P0[(p,b1,b2)]/F(1,2)   # rhoB = P0(.|B): function-form reflection holds on branch B
phi=lambda k:k[0]==1
# time-2 announced credences in phi per (b1,b2) = rho's own conditional on b2 (so each rho is value-reflective toward P_2)
c={}
for b1,rho in (('A',rhoA),('B',rhoB)):
    for b2 in 'ab': c[(b1,b2)]=prob(cond(rho,lambda k:k[2]==b2),phi)
print("announced P_2(phi) per cell (b1,b2):",{k:str(v) for k,v in c.items()})
for b1,rho in (('A',rhoA),('B',rhoB)):
    print(f" step-1 value-form P0(phi|b1={b1})={prob(cond(P0,lambda k:k[1]==b1),phi)} vs rho_{b1}(phi)={prob(rho,phi)}  -> value-form holds: {prob(cond(P0,lambda k:k[1]==b1),phi)==prob(rho,phi)}")
    ff=all(cond(P0,lambda k:k[1]==b1)[k]==rho[k] for k in atoms)
    print(f" step-1 function-form P0(.|b1={b1})==rho_{b1}: {ff}")
    for b2 in 'ab':
        comp=prob(cond(P0,lambda k:k[1]==b1 and k[2]==b2),phi)
        print(f"   composite P0(phi | P_2 cell ({b1},{b2}))={comp} vs announced {c[(b1,b2)]}  -> reflection of P0 toward P2 on this cell: {comp==c[(b1,b2)]}")
print("Conclusion: on branch B (function-form at step 1 + value-form at step 2) the two-step reflection holds; on branch A (value-form only at step 1) it fails although each step is value-reflective.")
# legitimacy-credence martingale under function-form: P0(L12 | b1=B) = rho_B(L12) for any event L12
L12=lambda k:k[2]=='a'
print("legitimacy-credence adoption on the function-form branch: P0(L12|B)=",prob(cond(P0,lambda k:k[1]=='B'),L12)," rho_B(L12)=",prob(rhoB,L12))
print("  ... and on the value-form-only branch: P0(L12|A)=",prob(cond(P0,lambda k:k[1]=='A'),L12)," rho_A(L12)=",prob(rhoA,L12)," (equal here by accident of the example; the phi∧L12 joint differs:", prob(cond(P0,lambda k:k[1]=='A'),lambda k:phi(k) and L12(k)),"vs",prob(rhoA,lambda k:phi(k) and L12(k)),")")
