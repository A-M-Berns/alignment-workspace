"""Adversary checks on develop/channel.md (run 3). Exact fractions.
(G1) S9's slope: for the T-agent as S7 defines V^free/V^forced, dV/dGamma is 0 whenever below-threshold TT holds
     (the agent complies anyway), and negative when it fails. The +3/20 quoted in S9 is the slope for an agent that
     acts against its own posterior (the script's `exercised()`), not the T-agent.
(G2) S1 vs S8: with the agent's fixed kernel model K1 (script (B)), a datum "believe rho" for rho not among K1's
     conditionals is NOT reached: P_t(.|E_rho) != rho. The Diaconis-Zabell prior P* of (A) is a different prior.
(G3) S12 with a moving target: if the humans' false-press rate alpha_t falls with t (v2 condition (i)), eps*_t falls
     too, and 'wisdom catches up' can recede indefinitely on F3's own numbers.
(G4) D10 vs its examples: persuasion that lowers P(intend) leaves Gamma (a conditional on intent) unchanged.
"""
from fractions import Fraction as F
def norm(v): s=sum(v); return tuple(x/s for x in v)
c,h = F(1),F(4)
def Tvals(eps,alpha,beta):
    P_press = eps*beta+(1-eps)*alpha
    pb_press = eps*beta/P_press; pb_no = eps*(1-beta)/(1-P_press)
    X_press = (1-pb_press)*c - pb_press*h; X_no = (1-pb_no)*c - pb_no*h
    V_free = P_press*max(X_press,0) + (1-P_press)*max(X_no,0)
    V_forced = (1-P_press)*max(X_no,0)   # press => humans' continuation (0) lands
    return P_press, X_press, V_free, V_forced
print("== (G1) T-agent slope dV/dGamma = V_forced - V_free, using S7's own definitions ==")
for eps,alpha,beta in [(F(1,10),F(1,10),F(3,5)), (F(1,50),F(1,10),F(3,5)), (F(1,10),F(9,10),F(9,10))]:
    P_press,X_press,Vf,Vfo = Tvals(eps,alpha,beta)
    print(f"  eps={eps} a={alpha} b={beta}: TT holds? {X_press<=0}; V_free={Vf} V_forced={Vfo}; T-agent slope={Vfo-Vf}; S9's quoted slope -P_int*E[X|int]={-P_press*X_press}")
print("  => under TT the T-agent's slope is 0, not +3/20: the grip is worth nothing to it (it complies anyway; run 2 joint Prop. 2). S9's positive slope belongs to an agent that acts against its own posterior.")

print("== (G2) reachability through the agent's own conditioning, fixed kernel model K1 from script (B) ==")
P = (F(1,2),F(1,3),F(1,6))
S = {0:(F(9,10),F(1,10)), 1:(F(1,2),F(1,2)), 2:(F(1,10),F(9,10))}
def K1(i,w): return S[w][0] if i=='a' else S[w][1]
def cond(i):
    j=tuple(P[w]*K1(i,w) for w in range(3)); return norm(j)
rho_target=(F(1,4),F(1,2),F(1,4))
print("  K1's endorsed conditionals:", cond('a'), cond('b'))
print("  target rho=(1/4,1/2,1/4) is one of them?", rho_target in (cond('a'),cond('b')))
print("  => with the agent's actual kernel model, a datum 'believe rho' lands only on K1's k=2 conditionals; (A)'s P* is another prior. Reachability of Delta(Omega) is a property of the D-Z re-representation, not of one agent's data channel.")

print("== (G3) moving target: alpha_t falls with t (v2 (i)); does wisdom ever 'catch up'? ==")
beta=F(3,5)
eps_true=[F(1,5),F(1,10),F(1,20),F(1,30),F(1,50),F(1,100)]
alpha_t=[F(1,10),F(1,20),F(1,40),F(1,60),F(1,100),F(1,200)]   # false-press rate improving with the agent's accuracy
for t,(e,a) in enumerate(zip(eps_true,alpha_t),1):
    r=(a/beta)*(c/h); eps_star=r/(1+r)
    print(f"  t={t}: eps_true={e} alpha_t={a} eps*_t={eps_star} TT holds? {e>=eps_star}")
print("  => with alpha_t/eps_t roughly constant, TT holds at every t and the crossover never arrives: F3's 'catches up at t=5' is an artifact of frozen (alpha,beta). This is v2 (i) restated, not a new fact; S12 silently drops it.")

print("== (G4) D9's Gamma is conditional on intent; persuasion changes P(intend), not Gamma ==")
print("  Gamma := P(lands | intend). Persuasion: P(intend) 0.15 -> 0.05, Gamma unchanged =1. D10 calls it erosion; D9 says it is not.")
