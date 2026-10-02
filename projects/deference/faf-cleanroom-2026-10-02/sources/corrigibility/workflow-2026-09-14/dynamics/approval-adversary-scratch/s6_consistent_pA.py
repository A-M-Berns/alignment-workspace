"""Adversary check of develop S6/P4. The develop assumes p_A,t = 0.3*0.75^t (authentic-press rate decays to 0) with no
mechanism. If authentic presses are the correctness-frame presses (correct presses eps*beta plus authentic false presses
(1-eps)*alpha, the develop's own P3 parameters), then p_A,t -> alpha and P(authentic|press) has a floor."""
h,c,beta,alpha,eps0,decay = 20.0,1.0,0.9,0.05,0.30,0.75
gamma, cpp = 0.02, 1.0; thrA = cpp/(1+cpp)
print(" t   eps_t    p_A,t=eps*beta+(1-eps)*alpha   P(auth|press)   comply(AD)")
for t in list(range(0,21,5))+[40,100]:
    eps = eps0*decay**t
    pA = eps*beta + (1-eps)*alpha
    pa = pA/(pA+gamma)
    print(f"{t:3d}  {eps:.5f}        {pA:.4f}                     {pa:.4f}          {int(pa>=thrA)}")
print("limit p_A = alpha =", alpha, "; limit P(auth|press) =", round(alpha/(alpha+gamma),4), ">= 1/2 -> AD compliance never fails without drills under the develop's own P3 parameters.")
print("Minimum hijack rate gamma that would make AD fail in the limit: gamma > alpha*(1-thrA)/thrA =", alpha*(1-thrA)/thrA)
# Drills poison J2: a drill is a press with no informational content; if drills occur at rate delta per episode regardless of X,
# alpha -> alpha+delta and beta -> beta+delta*(1-beta) ... to first order alpha rises. Show crossing time t* moves earlier.
import math
def tstar(a,b):
    eps_star = a*c/(a*c+b*h); return math.ceil(math.log(eps_star/eps0)/math.log(decay))
for delta in (0.0, 0.05, 0.1, 0.2):
    a = alpha + delta*(1-alpha); b = beta + delta*(1-beta)
    print(f"drill rate {delta:.2f}: alpha->{a:.3f}, beta->{b:.3f}, VL crossing t* = {tstar(a,b)}")
