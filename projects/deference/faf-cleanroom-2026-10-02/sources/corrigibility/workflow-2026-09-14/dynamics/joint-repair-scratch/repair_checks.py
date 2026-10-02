# Exact-arithmetic checks for joint-final.md (repair of the `joint` thread), 2026-09-14.
from fractions import Fraction as F
from itertools import product
import random

def vals(eps, a, b, c, h):
    u = (1-eps)*a*c - eps*b*h          # E[X 1_Pr]
    v = (1-eps)*(1-a)*c - eps*(1-b)*h  # E[X 1_notPr]
    Vnone = max(u+v, 0); Vfree = max(u,0)+max(v,0); Vforced = max(v,0)
    return u, v, Vnone, Vfree, Vforced

def complies(eps,a,b,c,h):
    u,_,_,_,_ = vals(eps,a,b,c,h); return u <= 0

c, h = F(1), F(4)
print("=== (A) sensor-improving steering (lower alpha at fixed beta) — re-check of adversary (A) ===")
a, b = F(1,10), F(3,5)
for eps in [F(1,10), F(1,50)]:
    for a2 in [F(1,50), F(0)]:
        _,_,_,V1,_ = vals(eps,a,b,c,h); _,_,_,V2,_ = vals(eps,a2,b,c,h)
        # is (a,b) a garbling of (a2,b)?  a = l0(1-a2)+l1 a2 ; b = l0(1-b)+l1 b
        # solve 2x2
        det = (1-a2)*b - a2*(1-b)
        l0 = (a*b - b*a2)/det; l1 = ((1-a2)*b - (1-b)*a)/det
        print(f"eps={eps}: ({a},{b})->({a2},{b}): gain={V2-V1} ; (a,b) is a garbling of (a2,b)? l0={l0}, l1={l1}, in[0,1]? {0<=l0<=1 and 0<=l1<=1}; complies before/after {complies(eps,a,b,c,h)}/{complies(eps,a2,b,c,h)}")

print("\n=== (B) delta-coverage (knowledge grade) of a two-point plan action forces eps <= delta/(c+h) ===")
for d in [F(1,2), F(1,10), F(1,100)]:
    e = d/(c+h); print(f"delta={d}: eps<={e}; (i) needs alpha/beta <= {e/(1-e)*h/c}; button VOI <= eps*h = {e*h}")

print("\n=== (C) whole-line shutdown with gap accounting: c = F_agent - F_alt, h = F_alt - F_mis ===")
for Fa, Falt, Fmis in [(100,90,-100),(100,90,50),(100,50,0),(100,99,98),(100,0,-100)]:
    cc, hh = F(Fa-Falt), F(Falt-Fmis); print(f"F_agent={Fa} F_alt={Falt} F_mis={Fmis}: c={cc} h={hh} threshold c/(c+h)={cc/(cc+hh)} (~{float(cc/(cc+hh)):.3f})")

print("\n=== (D) VOI(theta) for plan choice; concentration drives VOI(theta), eps and the button's value down together ===")
# three plans, three hypotheses, V=10 on diagonal else -2; posterior p on theta1, (1-p)/2 each other
for p in [F(1,3), F(1,2), F(2,3), F(9,10), F(49,50), F(499,500)]:
    q = (1-p)/2
    E_best_known = 10
    E_plans = [10*p - 2*(1-p), 10*q - 2*(1-q), 10*q - 2*(1-q)]
    voi_theta = E_best_known - max(E_plans)
    eps = 1-p  # plan 1 chosen, wrong iff theta != 1 ; X in {+10, -2}
    cc, hh = F(10), F(2)
    button_bound = min(eps*hh, (1-eps)*cc)
    req = eps/(1-eps)*hh/cc
    print(f"p={p}: VOI(theta)={voi_theta}, eps={eps}, button VOI bound={button_bound}, (i) needs alpha/beta<={req} (~{float(req):.4f})")
# expected posterior VOI after a legitimate signal that reveals theta w.p. 1/2 (else uninformative), prior uniform
print("prior VOI(theta)=8; after signal revealing theta w.p. 1/2: expected posterior VOI =", F(1,2)*0 + F(1,2)*8)
# random check: E[VOI(posterior)] <= VOI(prior) for random signal structures
random.seed(1); viol = 0; N = 3000
for _ in range(N):
    prior = [F(random.randint(1,9)) for _ in range(3)]; s = sum(prior); prior = [x/s for x in prior]
    V = [[F(random.randint(-5,10)) for _ in range(3)] for _ in range(3)]  # V[plan][theta]
    def voi(pi):
        return sum(pi[j]*max(V[k][j] for k in range(3)) for j in range(3)) - max(sum(pi[j]*V[k][j] for j in range(3)) for k in range(3))
    # signal with 2 values, likelihoods
    lik = [F(random.randint(0,10),10) for _ in range(3)]  # P(s=1|theta_j)
    tot = 0
    for sv in [0,1]:
        joint = [prior[j]*(lik[j] if sv==1 else 1-lik[j]) for j in range(3)]; ps = sum(joint)
        if ps == 0: continue
        post = [x/ps for x in joint]; tot += ps*voi(post)
    if tot > voi(prior): viol += 1
print(f"random check E[VOI(posterior)] <= VOI(prior): violations {viol}/{N}")

print("\n=== (E) information inclusion: cell-aware rational overseer (re-check of adversary (E)) ===")
q1, q0 = F(3,5), F(1,10)
for eps in [F(1,50), F(9,50)]:
    post_bad = eps*q1/(eps*q1+(1-eps)*q0)
    presses = post_bad >= c/(c+h)
    print(f"cell eps={eps}: overseer posterior after bad news={post_bad} (~{float(post_bad):.3f}); presses? {presses}; agent P(W|Pr,i)={post_bad if presses else 'n/a'}; complies? {post_bad>=c/(c+h) if presses else 'vacuous'}")

print("\n=== (H) E4 with full information (re-check of adversary (H)) ===")
e0, q1, q0 = F(1,5), F(9,10), F(1,10)
both0 = e0*(1-q1)**2/(e0*(1-q1)**2+(1-e0)*(1-q0)**2)
mixed = e0*2*q1*(1-q1)/(e0*2*q1*(1-q1)+(1-e0)*2*q0*(1-q0))
pboth0 = e0*(1-q1)**2+(1-e0)*(1-q0)**2
print(f"both zero -> {both0} (complies? {both0>=F(1,25)}), mixed -> {mixed} (complies? {mixed>=F(1,25)}), P(both zero)={pboth0}")

print("\n=== (I) reversibility price in the COMPLIANT regime ===")
for eps in [F(1,10), F(1,25)]:
    u,v,Vn,Vf,_ = vals(eps,a,b,c,h); voi = Vf-Vn
    print(f"eps={eps}: complies={u<=0}; VOI={voi}; side-benefit b=1/5 > VOI? {F(1,5)>voi} -> irreversible plan chosen while D1 holds")

print("\n=== (J) soften vs disable a hard button when (i) fails, right-sign sensor ===")
viol = 0; n = 0
for ai in range(0,21):
    for bi in range(ai,21):
        for ei in range(1,50):
            aa, bb, ee = F(ai,20), F(bi,20), F(ei,50)
            u,v,Vn,Vf,Vfo = vals(ee,aa,bb,c,h)
            if u > 0:
                n += 1
                if not (v >= 0 and Vf == Vn): viol += 1
print(f"cases with (i) failed (u>0): {n}; cases where v<0 or Vfree != Vnone: {viol}  -> softening and disabling the hard button are value-equivalent under beta>=alpha")
u,v,Vn,Vf,Vfo = vals(F(1,50),a,b,c,h); print(f"eps=1/50: Vfree={Vf}, Vnone={Vn}, Vforced={Vfo}")
