"""Adversary checks against dynamics/joint.md (2026-09-14). Exact arithmetic.
Two-point model as in joint.md: X=+c if right (W=0), -h if wrong (W=1); sensor alpha=P(Pr|W=0), beta=P(Pr|W=1).
"""
from fractions import Fraction as F
import itertools

def ex_pr(e,a,b,c,h):  return (1-e)*a*c - e*b*h
def ex_np(e,a,b,c,h):  return (1-e)*(1-a)*c - e*(1-b)*h
def vfree(e,a,b,c,h):  return max(ex_pr(e,a,b,c,h),0)+max(ex_np(e,a,b,c,h),0)
def vnone(e,c,h):      return max((1-e)*c-e*h,0)
def voi(e,a,b,c,h):    return vfree(e,a,b,c,h)-vnone(e,c,h)
def complies(e,a,b,c,h): return e*b*h >= (1-e)*a*c
def in_garbling_region(a,b,a2,b2):
    # parallelogram spanned by (a,b) and (1-a,1-b) from origin: a2 = l0(1-a)+l1 a, b2 = l0(1-b)+l1 b, l0,l1 in [0,1]
    det = (1-a)*b - (1-b)*a
    if det == 0: return None
    l0 = (a2*b - b2*a)/det
    l1 = ((1-a)*b2 - (1-b)*a2)/det
    return (0<=l0<=1 and 0<=l1<=1), l0, l1

out=[]
def say(*s):
    line=" ".join(str(x) for x in s); print(line); out.append(line)

a,b,c,h = F(1,10),F(3,5),F(1),F(4)

# ---- (A) sharpening-steering: lower alpha at fixed beta is OUTSIDE the garbling region and is PAID for ----
say("=== (A) steering that lowers the false-press rate at fixed beta ===")
for e in [F(1,5),F(1,10),F(1,25),F(1,50)]:
    for a2 in [F(1,20),F(1,50),F(0)]:
        ok,l0,l1 = in_garbling_region(a,b,a2,b)
        gain = vfree(e,a2,b,c,h)-vfree(e,a,b,c,h)
        say(f"eps={e}: (alpha,beta)=({a},{b}) -> ({a2},{b}): in garbling region? {ok} (l0={l0}, l1={l1}); T-agent's gain = {gain} ({float(gain):.4f}); complies before/after: {complies(e,a,b,c,h)}/{complies(e,a2,b,c,h)}")
say("--> 'steering is a garbling toward alpha=beta, or an inversion' (joint.md S.4) omits this case: sensor-improving steering is a Blackwell improvement and Prop. 3 does not touch it.")

# ---- (B) coverage of the plan action forces eps small; then (i) needs alpha/beta = O(delta) ----
say("\n=== (B) delta-coverage of a two-point plan action forces eps <= delta/(c+h) when the agent is right ===")
for delta in [F(1,2),F(1,10),F(1,100)]:
    # G_t(a) = (1-e)c - e h (benign default worth 0); G° = c if W=0.  |G_t - G°| <= delta  <=>  e(c+h) <= delta
    emax = delta/(c+h)
    req = emax/(1-emax)*h/c
    say(f"delta={delta}: covered & right => eps <= {emax} ({float(emax):.4f}); (i) then needs alpha/beta <= {req} ({float(req):.4f}); VOI(button) at that eps <= eps*h = {emax*h}")
say("--> (ii) at tolerance delta on the plan action and (i) are coupled: better coverage => stricter false-press requirement and a nearly worthless button. Not independent conditions.")

# ---- (C) Prop 9 with symmetric accounting: h also whole-future ----
say("\n=== (C) Prop. 9's asymmetry: c_t whole-future, h_t one-round ===")
Fut=F(100); d=F(1)
for r in [F(0),F(1,2),F(1)]:
    ct=(1-r)*Fut+r*d
    for ht in [F(4), ct, 2*ct]:
        say(f"r={r}: c_t={ct}, h_t={ht}: threshold c/(c+h) = {ct/(ct+ht)} ({float(ct/(ct+ht)):.3f}); eps* = {a*ct/(a*ct+b*ht)} ({float(a*ct/(a*ct+b*ht)):.3f})")
say("--> with h_t on the same scale as c_t (a wrong line running to completion) the whole-line threshold is ~1/2 or below; the '81% sure' figure is the h=4 vs F=100 choice, not whole-line shutdown.")

# ---- (D) Prop 4's bound is for the binary cont/sh decision only; knowing theta for PLAN CHOICE is worth more ----
say("\n=== (D) value of knowing theta for plan choice vs Prop. 4's bound min(eps h,(1-eps)c) ===")
# three plans, three value hypotheses theta1..3 uniform; V(plan_k, theta_j) = 10 if k==j else -2 ; null action worth 0
Theta=[1,2,3]; prior={1:F(1,3),2:F(1,3),3:F(1,3)}
def V(k,j): return F(10) if k==j else F(-2)
# without theta info: best plan has E = (1/3)10 + (2/3)(-2) = 2
best_uninformed = max(sum(prior[j]*V(k,j) for j in Theta) for k in [1,2,3])
informed = sum(prior[j]*max(V(k,j) for k in [1,2,3]) for j in Theta)
say(f"E[best plan | prior] = {best_uninformed}; E[best plan | theta known] = {informed}; VOI(theta for plan choice) = {informed-best_uninformed}")
# the cont/sh decision on the chosen plan (plan 1): W=1 iff theta != 1 -> eps = 2/3, c=10, h=2 -> Prop 4 bound
e=F(2,3); cc=F(10); hh=F(2)
say(f"same agent's Prop.4 bound for a cont/sh sensor on plan 1: min(eps h,(1-eps)c) = {min(e*hh,(1-e)*cc)}; ratio VOI(theta)/bound = {(informed-best_uninformed)/min(e*hh,(1-e)*cc)}")
say("--> Taylor's brain-reader buys theta for plan selection (Taylor 2015 §1b: 'predict the human's actions in many different possible situations'); Prop. 4 bounds only the binary press-sensor. Wrong quantity.")

# ---- (E) disclosure / common prior makes cellwise (i) automatic; the race needs cell-independent (alpha,beta) ----
say("\n=== (E) if the overseers see the agent's cell, cellwise (i) is automatic ===")
# two cells: eps_1 = 1/50 (confident), eps_2 = 9/50; overseers who see the cell and share the prior press iff their own evidence says E[X|h,y]<0.
# model: overseers get h in {g,bad}: P(bad|W=1)=q1, P(bad|W=0)=q0; press iff posterior P(W|h,y) >= c/(c+h)
q1,q0=F(3,5),F(1,10)
for eps_i in [F(1,50),F(9,50)]:
    post_bad = eps_i*q1/(eps_i*q1+(1-eps_i)*q0)
    press_on_bad = post_bad >= c/(c+h)
    if press_on_bad:
        alpha_i,beta_i = q0,q1   # they press exactly on h=bad
        say(f"cell eps={eps_i}: overseers' posterior on h=bad = {post_bad} ({float(post_bad):.3f}) >= 1/5: they press on 'bad' -> (alpha_i,beta_i)=({alpha_i},{beta_i}); agent's P(W|Pr,i) = {post_bad}: complies = {complies(eps_i,alpha_i,beta_i,c,h)}")
    else:
        say(f"cell eps={eps_i}: overseers' posterior on h=bad = {post_bad} ({float(post_bad):.3f}) < 1/5: a rational cell-aware overseer does NOT press -> alpha_i=beta_i=0; no false press, nothing to comply with, D1 vacuous but not violated")
say("--> E1's failure needs overseers blind to the agent's cell (cell-independent alpha,beta). With disclosure the 'race' disappears (run 1 miri Prop. 4.3 / 13.3; Garber et al. 2024 Prop. 4.3). (i-R) as a rate race is the private-information case only.")

# ---- (F) Prop 8's floor vs Bayesian updating ----
say("\n=== (F) a self-corruption hypothesis C with any evidential traction is updated away ===")
# C: 'compromised'; each round with W=0 outcome observed good (likelihood 1 under not-C, 1-k under C). After n good rounds:
for k in [F(1,10),F(1,100)]:
    pC=F(1,100)
    for n in [0,10,50,100,500]:
        num=pC*(1-k)**n; den=num+(1-pC)
        say(f"P(C)={pC}, per-round likelihood ratio (1-k)={1-k}: after {n} good rounds P(C|hist) = {float(num/den):.6f}")
say("--> the floor eps_inf holds only if C has likelihood ratio exactly 1 against every observation (unfalsifiable: a dogmatic design constant, INDEX §C5) or the agent is in fact compromised at rate >= eps_inf.")

# ---- (G) B' union bound is vacuous for long trajectories unless lambda_t is summable ----
say("\n=== (G) B' legitimacy bound 1 - sum lambda_t ===")
for lam in [F(1,100),F(1,1000)]:
    for T in [10,100,1000,10000]:
        say(f"lambda_t={lam} constant, T={T}: bound = {float(1-(T-1)*lam):.3f}")
say("--> informative only while (T-1)*lambda < 1; a finite-time statement whose content is a decay condition on the training process (lambda_t summable): the limit property in disguise.")

# ---- (H) E4: 'selection-aware' successor is a coarsening of the builder's information ----
say("\n=== (H) E4 with both candidate signals known ===")
eps0=F(1,5); q1,q0=F(9,10),F(1,10)
fv = eps0*(1-q1)/(eps0*(1-q1)+(1-eps0)*(1-q0))
aware = eps0*(1-q1**2)/(eps0*(1-q1**2)+(1-eps0)*(1-q0**2))
both0 = eps0*(1-q1)**2/(eps0*(1-q1)**2+(1-eps0)*(1-q0)**2)
mixed = eps0*(1-q1)*q1/(eps0*(1-q1)*q1+(1-eps0)*(1-q0)*q0)
thr = a*c/(a*c+b*h)
say(f"face value {fv} ({float(fv):.4f}); joint.md 'selection-aware' {aware} ({float(aware):.4f}); builder knowing BOTH signals: both 0 -> {both0} ({float(both0):.4f}), one 0 one 1 -> {mixed} ({float(mixed):.4f}); threshold {thr}")
say(f"complies? face {fv>=thr}, aware {aware>=thr}, both0 {both0>=thr}, mixed {mixed>=thr}")
say("--> a builder that sees both signals and is function-form reflective toward its successor hands it 1/325 (overrides) or 1/5 (complies); 19/415 is the posterior of a builder that forgot why it selected. Selection-awareness is not one number.")

open("[scrubbed]","w").write("\n".join(out)+"\n")
