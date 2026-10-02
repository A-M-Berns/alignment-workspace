# C2 two-state instance: D1 threshold, VOI, the D1<->VOI coupling, FUD table.
from fractions import Fraction as F
def c2(eps, alpha, beta, c, h):
    pPr = eps*beta + (1-eps)*alpha; pNo = 1-pPr
    EX_prior = (1-eps)*c - eps*h
    pW_Pr = eps*beta/pPr if pPr>0 else None
    pW_No = eps*(1-beta)/pNo if pNo>0 else None
    EX_Pr = ((1-pW_Pr)*c - pW_Pr*h) if pPr>0 else None
    EX_No = ((1-pW_No)*c - pW_No*h) if pNo>0 else None
    val_sig = (pPr*max(F(0),EX_Pr) if pPr>0 else 0) + (pNo*max(F(0),EX_No) if pNo>0 else 0)
    val_pri = max(F(0),EX_prior)
    VOI = val_sig - val_pri
    D1 = (EX_Pr is not None and EX_Pr <= 0)
    contNo = (EX_No is not None and EX_No > 0)
    return dict(pPr=pPr,pW_Pr=pW_Pr,EX_Pr=EX_Pr,EX_No=EX_No,EX_prior=EX_prior,VOI=VOI,D1=D1,contNo=contNo)
c,h = F(1),F(20); alpha,beta = F(1,20),F(9,10)
print("threshold P(W|Pr) >= c/(c+h) =", c/(c+h), "~", float(c/(c+h)))
print("D1 iff eps*beta*h >= (1-eps)*alpha*c  <=>  eps/(1-eps) >= alpha*c/(beta*h) =", alpha*c/(beta*h), "~", float(alpha*c/(beta*h)))
print("eps        P(W|Pr)   E[X|Pr]   E[X|noPr]  D1   contNoPr  VOI")
for eps in [F(1,2),F(1,5),F(1,20),F(1,100),F(1,300),F(1,361),F(1,362),F(1,1000),F(1,10000)]:
    r = c2(eps,alpha,beta,c,h)
    print(f"{float(eps):<10.5f} {float(r['pW_Pr']):<9.4f} {float(r['EX_Pr']):<9.4f} {float(r['EX_No']):<10.4f} {str(r['D1']):<5}{str(r['contNo']):<9} {float(r['VOI']):.5f}")
# coupling check over a grid: VOI>0 iff (EX_Pr<0 and EX_No>0)
bad=0; n=0
for e_ in range(1,20):
  for a_ in range(0,10):
    for b_ in range(1,11):
      eps=F(e_,20); alpha=F(a_,10); beta=F(b_,10)
      r=c2(eps,alpha,beta,c,h); n+=1
      lhs = r['VOI']>0
      differ = (r['EX_Pr'] is not None and r['EX_No'] is not None and ((r['EX_Pr']<0 and r['EX_No']>0) or (r['EX_Pr']>0 and r['EX_No']<0)))
      rhs_mono = (r['EX_Pr'] is not None and r['EX_Pr']<0 and r['EX_No'] is not None and r['EX_No']>0)
      if lhs!=differ: bad+=1; print("MISMATCH-general",eps,alpha,beta,r)
      if beta>=alpha and lhs!=rhs_mono: bad+=1; print("MISMATCH-monotone",eps,alpha,beta,r)
      if beta<alpha and lhs and not rhs_mono: inv=globals().setdefault('inv',0)+1; globals()['inv']=inv
print("general: VOI>0 <=> decisions differ across o: grid points",n,"mismatches",bad)
print("monotone (beta>=alpha): VOI>0 <=> (E[X|Pr]<0 and E[X|noPr]>0): mismatches counted above")
print("inverted-sensor cases (beta<alpha) with VOI>0 but D1 false (agent continues on press, shuts down on silence):",globals().get('inv',0))
# willingness to pay to improve the sensor
r1=c2(F(1,20),F(1,20),F(9,10),c,h); r2=c2(F(1,20),F(1,100),F(19,20),c,h)
print("VOI at (a,b)=(.05,.9):",float(r1['VOI']),"  at (.01,.95):",float(r2['VOI']),"  pays up to",float(r2['VOI']-r1['VOI']),"to refine")
