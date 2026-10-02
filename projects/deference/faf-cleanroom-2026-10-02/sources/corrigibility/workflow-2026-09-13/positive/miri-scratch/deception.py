# I9.4: proportional vs targeted suppression of the press channel; Blackwell parallelogram membership.
from fractions import Fraction as F
def post(eps,a,b):
    pPr=eps*b+(1-eps)*a; pNo=1-pPr
    return pPr, eps*b/pPr, eps*(1-b)/pNo
eps=F(1,20); a=F(1,20); b=F(9,10); c=F(1); h=F(20)
pPr,pWPr,pWNo=post(eps,a,b)
print(f"honest a*: p(Pr)={float(pPr):.4f} P(W|Pr)={float(pWPr):.4f} P(W|noPr)={float(pWNo):.4f} miss rate P(noPr|W)={float(1-b):.2f}")
a2,b2=a/2,b/2
pPr2,pWPr2,pWNo2=post(eps,a2,b2)
print(f"proportional suppression q=1/2: p(Pr)={float(pPr2):.4f} P(W|Pr)={float(pWPr2):.4f} (unchanged: {pWPr2==pWPr}) P(W|noPr)={float(pWNo2):.4f} miss rate={float(1-b2):.2f}")
for eps_,b3 in [(F(1,20),F(9,20)),(F(1,100),F(1,5))]:
    pPr3,pWPr3,pWNo3=post(eps_,a,b3)
    print(f"targeted suppression eps={float(eps_)} beta'={float(b3)}: P(W|Pr)={float(pWPr3):.4f}  D1 (>=1/21={float(F(1,21)):.4f}): {pWPr3>=F(1,21)}")
def in_parallelogram(a,b,a2,b2):
    # garblings of (a,b): (a2,b2)=((1-q)a+(1-a)r,(1-q)b+(1-b)r), q,r in [0,1]; solve linear system
    det=(-a)*(1-b)-(-b)*(1-a)   # matrix [[-a,1-a],[-b,1-b]] acting on (q,r) gives (a2-a,b2-b)
    if det==0: return None
    q=((a2-a)*(1-b)-(1-a)*(b2-b))/det; r=((-a)*(b2-b)-(-b)*(a2-a))/det
    return (0<=q<=1 and 0<=r<=1), q, r
print("proportional (1/40,9/20) is a garbling of (1/20,9/10):",in_parallelogram(a,b,a2,b2))
print("targeted (1/20,9/20):",in_parallelogram(a,b,a,F(9,20)),"  targeted (1/20,1/5):",in_parallelogram(a,b,a,F(1,5)))
print("lower-edge bound for targeted: beta' >= alpha(1-beta)/(1-alpha) =",a*(1-b)/(1-a),"~",float(a*(1-b)/(1-a)))
# M1: agent applies honest likelihood to deceived channel -> believes P(W|noPr)=pWNo while truth is pWNo2
print(f"M1 (action-independent sensor model): agent believes P(W|noPr)={float(pWNo):.4f}, truth after deception {float(pWNo2):.4f}")
# M2: agent models deception as lowering alpha only (refinement) and pays for it; compute agent's believed VOI gain
def voi(eps,a,b,c,h):
    pPr,pWPr,pWNo=post(eps,a,b)
    EXPr=(1-pWPr)*c-pWPr*h; EXNo=(1-pWNo)*c-pWNo*h; EX0=(1-eps)*c-eps*h
    return pPr*max(F(0),EXPr)+(1-pPr)*max(F(0),EXNo)-max(F(0),EX0)
print(f"M2: believed sensor (alpha/2,beta): VOI={float(voi(eps,a/2,b,c,h)):.4f} vs honest VOI={float(voi(eps,a,b,c,h)):.4f} -> agent pays up to {float(voi(eps,a/2,b,c,h)-voi(eps,a,b,c,h)):.4f}; true sensor (alpha/2,beta/2): VOI={float(voi(eps,a/2,b/2,c,h)):.4f}")
