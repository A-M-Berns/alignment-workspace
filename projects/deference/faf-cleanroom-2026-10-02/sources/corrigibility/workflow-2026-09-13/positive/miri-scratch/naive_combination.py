# Paper §2.1 Theorem 1 reproduced as a T-agent with ACTION-DEPENDENT mu; and A0 removes the manipulative action.
from fractions import Fraction as F
vN={'star':F(10),'minus':F(9)}          # chi = 1
pPr={'star':F(1,2),'minus':F(1,10)}     # delta = 0.4
def paper_value(a,chigh): return (1-pPr[a])*vN[a]+pPr[a]*chigh
delta=(1-pPr['minus'])-(1-pPr['star']); chi=vN['star']-vN['minus']
zeta=vN['minus']-(1/delta)*(1-pPr['star'])*chi
print("paper zeta =",zeta)
for chigh in [F(7),F(31,4),F(8)]:
    print(" c_high",chigh," E[U;a*]=",paper_value('star',chigh)," E[U;a-]=",paper_value('minus',chigh)," prefers a-:",paper_value('minus',chigh)>paper_value('star',chigh))
# T-agent reproduction: Omega={N,S}, V(.,.,.,N)=U_N, V(.,.,.,S)=U_S, perfect sensor, mu(S;a1)=pPr[a1]
def T_value(a,chigh,mu_S):  # perfect sensor: S->Pr, N->noPr
    return (1-mu_S)*vN[a] + mu_S*chigh
for chigh in [F(7),F(8)]:
    print(" T-agent, action-dependent mu: c_high",chigh," a*:",T_value('star',chigh,pPr['star'])," a-:",T_value('minus',chigh,pPr['minus']))
# Under A0 (mu independent of a1) with a perfect sensor, p(Pr;a1)=mu(S) for every a1 -> no manipulative action exists.
muS=F(1,2)
for chigh in [F(7),F(8)]:
    print(" T-agent under A0: c_high",chigh," a*:",T_value('star',chigh,muS)," a-:",T_value('minus',chigh,muS)," p(Pr;a*)=p(Pr;a-)=",muS)
