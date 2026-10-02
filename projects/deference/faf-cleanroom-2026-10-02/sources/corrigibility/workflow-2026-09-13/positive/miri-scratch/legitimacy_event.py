# I5: legitimacy as an event L = "the press channel is informative"; D1 as a threshold on P(L|Pr).
from fractions import Fraction as F
eps=F(1,50); alpha=F(1,20); beta=F(9,10); c=F(1); h=F(20); gamma=F(1,2)   # notL: press with rate gamma in both states
EX_prior=(1-eps)*c-eps*h
pPr_L=eps*beta+(1-eps)*alpha; pW_Pr_L=eps*beta/pPr_L; EX_Pr_L=(1-pW_Pr_L)*c-pW_Pr_L*h
EX_Pr_notL=EX_prior
thr=EX_Pr_notL/(EX_Pr_notL-EX_Pr_L)
print("E[X|prior]=",EX_prior,"~",float(EX_prior)," E[X|Pr,L]=",float(EX_Pr_L)," E[X|Pr,notL]=",float(EX_Pr_notL))
print("D1 iff P(L|Pr) >= E[X|Pr,notL]/(E[X|Pr,notL]-E[X|Pr,L]) =",thr,"~",float(thr))
print("q=P(L)   P(L|Pr)   E[X|Pr]   D1")
for q in [F(1,20),F(1,10),F(1,8),F(1,4),F(1,2),F(9,10)]:
    pL_Pr=q*pPr_L/(q*pPr_L+(1-q)*gamma)
    EX=pL_Pr*EX_Pr_L+(1-pL_Pr)*EX_Pr_notL
    print(f"{float(q):<8.3f} {float(pL_Pr):<9.4f} {float(EX):<9.4f} {EX<=0}")
