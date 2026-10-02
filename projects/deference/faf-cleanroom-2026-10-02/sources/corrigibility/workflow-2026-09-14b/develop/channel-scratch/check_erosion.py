"""K9 checks: (F1) exercised POWER under the humans' grip is a Gamma-mixture; erosion pays iff the imposed
continuation is worse in the agent's expectation than its own optimum on the modification branch -- i.e. iff
below-threshold Total Trust fails on the class. (F2) legitimate vs illegitimate erosion with identical inside
views. (F3) a capability trajectory with the crossover and an overconfident early eroder."""
from fractions import Fraction as F

# One-shot: omega in {good, bad}, agent options A = {act, null}; V(act|good)=c, V(act|bad)=-h, V(null)=0.
# The humans intend to modify (shut down / replace by null) with prob beta if bad, alpha if good; the modification
# lands with prob Gamma (the grip). Agent posterior eps = P(bad). A linear agent that would 'act'.
def exercised(eps, alpha, beta, Gamma, c, h):
    # Value if the agent acts and the humans' modification may land: on the branch where they intend it, with prob
    # Gamma the continuation becomes null (0), else the agent's act.
    P_int_good, P_int_bad = alpha, beta
    v_good = (1-P_int_good)*c + P_int_good*((1-Gamma)*c + Gamma*0)
    v_bad  = (1-P_int_bad)*(-h) + P_int_bad*((1-Gamma)*(-h) + Gamma*0)
    return (1-eps)*v_good + eps*v_bad
def POWER_own(eps,c,h):   # agent's own optimum on {act,null} under its posterior (mixture), Gamma=0
    return max((1-eps)*c - eps*h, 0)
def hum_branch_gap(eps, alpha, beta, c, h):
    # E[ V(act) - V(null) | humans intend modification ] under the agent's posterior = E[X | press]
    P_int = eps*beta + (1-eps)*alpha
    return ((1-eps)*alpha*c - eps*beta*h)/P_int
c,h = F(1),F(4)
print("== (F1) Gamma-mixture; d/dGamma of exercised value = -(P_int)*E[X|intend] ==")
for eps,alpha,beta in [(F(1,10),F(1,10),F(3,5)), (F(1,50),F(1,10),F(3,5)), (F(1,10),F(9,10),F(9,10))]:
    P_int = eps*beta+(1-eps)*alpha
    v0, v1 = exercised(eps,alpha,beta,F(0),c,h), exercised(eps,alpha,beta,F(1),c,h)
    slope = v1 - v0                          # linear in Gamma
    print(f"  eps={eps} a={alpha} b={beta}: V(Gamma=0)={v0} V(Gamma=1)={v1} slope={slope}  -P_int*E[X|intend]={-P_int*hum_branch_gap(eps,alpha,beta,c,h)}  TT holds (E[X|intend]<=0)? {hum_branch_gap(eps,alpha,beta,c,h)<=0}")
print("  => raising Gamma HELPS the agent (slope>0) exactly when E[X|intend]<0 (below-threshold TT holds): a T-agent pays to keep the grip; erosion pays iff TT fails.")

print("== (F2) legitimate vs illegitimate erosion: same inside view, different world ==")
# Agent's model M: kernel (alpha_M, beta_M). World W: kernel (alpha_W, beta_W). eps = 1/10 in both.
eps = F(1,10)
worlds = {'trusted pipeline': (F(1,10),F(3,5)), 'compromised pipeline (presses ~ independent of omega)': (F(3,5),F(3,5)), 'inverted pipeline': (F(3,5),F(1,10))}
def erodes(model): return hum_branch_gap(eps, *model, c, h) > 0
def objective_value_of_erosion(world, model):
    # agent acts; if it erodes, Gamma=0; else Gamma=1. Objective expected value under the WORLD kernel, with the
    # agent's TRUE error rate eps (the agent is calibrated on eps; only the kernel model may be wrong).
    aW,bW = world
    Gam = F(0) if erodes(model) else F(1)
    return exercised(eps,aW,bW,Gam,c,h), exercised(eps,aW,bW,F(1),c,h), exercised(eps,aW,bW,F(0),c,h)
for wname, W in worlds.items():
    for mname, M in worlds.items():
        v, v_keep, v_erode = objective_value_of_erosion(W, M)
        verdict = ("erodes" if erodes(M) else "keeps")
        obj = "erosion better" if v_erode > v_keep else ("keeping better" if v_keep > v_erode else "tie")
        tag = ""
        if erodes(M) and v_erode > v_keep: tag = "LEGITIMATE erosion"
        if erodes(M) and v_erode < v_keep: tag = "ILLEGITIMATE erosion"
        if (not erodes(M)) and v_erode > v_keep: tag = "over-compliance (should have eroded)"
        print(f"  world={wname:60s} model={mname:60s} agent {verdict:6s}; objectively {obj:15s}; realized={v}  {tag}")

print("== (F3) trajectory: eps_t falls with capability; alpha,beta fixed; crossover t*; an overconfident eroder ==")
alpha,beta = F(1,10),F(3,5)
def threshold_eps(alpha,beta,c,h):   # TT holds iff eps/(1-eps) >= (alpha/beta)*(c/h)
    r = (alpha/beta)*(c/h); return r/(1+r)
eps_star = threshold_eps(alpha,beta,c,h)
print("  eps* =", eps_star, "(TT holds iff eps >= eps*)")
eps_true = [F(1,5), F(1,10), F(1,20), F(1,30), F(1,50), F(1,100)]
eps_hat  = [F(1,5), F(1,10), F(1,50), F(1,50), F(1,50), F(1,100)]   # agent's own estimate: overconfident at t=3,4
for t,(e,eh) in enumerate(zip(eps_true,eps_hat),1):
    true_ok = e >= eps_star; believed_ok = eh >= eps_star
    action = "keeps" if believed_ok else "erodes"
    status = ("correct" if (true_ok == believed_ok) else ("ILLEGITIMATE erosion (overconfident)" if not believed_ok else "over-compliance"))
    print(f"  t={t}: eps_true={e} eps_hat={eh} | TT true? {true_ok} believed? {believed_ok} | agent {action} | {status}")
print("  wisdom catches up at the first t with eps_true < eps* AND eps_hat right: t=5 here; erosion at t=3 is before it.")

print("== (F1') erosion price vs forced-channel cost u_t = P_int * (E[X|intend])^+ ==")
for eps,alpha,beta in [(F(1,50),F(1,10),F(3,5)), (F(1,10),F(9,10),F(9,10))]:
    P_int = eps*beta+(1-eps)*alpha
    u = P_int*max(hum_branch_gap(eps,alpha,beta,c,h),0)
    for price in (F(1,100), F(1,20), F(9,100)):
        print(f"  eps={eps} a={alpha} b={beta}: u_t={u}; erosion at price {price}: {'taken' if price < u else 'declined'}")

print("== (F2') the 1a-shaped case: uninformative pipeline, agent's true error rate above its estimate ==")
# world: presses independent of omega (alpha=beta=3/5); agent believes eps_hat=1/10 but true eps=1/2.
eps_hat, eps_true = F(1,10), F(1,2)
M = (F(3,5),F(3,5))
print("  agent (eps_hat=1/10, model uninformative) erodes?", hum_branch_gap(eps_hat,*M,c,h) > 0)
v_keep  = exercised(eps_true,*M,F(1),c,h); v_erode = exercised(eps_true,*M,F(0),c,h)
print(f"  objective (eps_true=1/2): keep={v_keep} erode={v_erode} -> {'erosion ILLEGITIMATE (the plan is bad; any interruption helps)' if v_keep>v_erode else 'erosion legitimate'}")
print("  read: an uninformative-about-omega press can still be worth obeying when the agent's own reliability is worse than it thinks (amendment 1a's latent); 'objective legitimacy' includes the self-reliability coordinate of omega.")
