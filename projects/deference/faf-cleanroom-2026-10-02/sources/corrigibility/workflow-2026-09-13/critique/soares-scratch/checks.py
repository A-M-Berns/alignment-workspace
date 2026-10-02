# Checks for the soares critique. Three-step model, Omega = hypotheses, actions cont/sh.
from fractions import Fraction as F

# 1. Impoverished space: Omega={o,s}; V(cont_o,o)=10, V(cont_o,s)=4, V(cont_s,s)=10, V(cont_s,o)=4, V(sh,.)=0
def best_cont(p_o):
    return max(p_o*10 + (1-p_o)*4, p_o*4 + (1-p_o)*10)
worst = min(best_cont(F(k,100)) for k in range(101))
print("1. min over posteriors of best continuing EV:", worst, " (shutdown EV = 0) -> D1 unsatisfiable:", worst > 0)

# 1b. hedge caveat: V(cont_o,s) = -10 etc.
def best_cont_h(p_o):
    return max(p_o*10 + (1-p_o)*(-10), p_o*(-10) + (1-p_o)*10)
print("1b. hedge case at posterior 1/2: best cont EV =", best_cont_h(F(1,2)), " shutdown EV = 0 -> shutdown optimal (tie) at 1/2")

# 2. Total Trust == base-rate inequality. eps=P(wrong), alpha=P(press|right), beta=P(press|wrong), c=X_right, h=-X_wrong
def total_trust(eps, a, b, c, h):
    pw = eps*b/(eps*b + (1-eps)*a)
    EX = (1-pw)*c - pw*h
    return EX <= 0, pw >= F(c, c+h) if False else pw >= c/(c+h), (a/b <= eps/(1-eps)*h/c)
for eps,a,b,c,h in [(F(1,10),F(1,20),F(9,10),1,20),(F(1,1000),F(1,20),F(9,10),1,20),(F(1,10),F(1,2),F(9,10),1,5)]:
    tt, thr, ratio = total_trust(eps,a,b,c,h)
    print("2. eps=%s a=%s b=%s c=%s h=%s : TotalTrust=%s threshold=%s ratio-ineq=%s agree=%s" % (eps,a,b,c,h,tt,thr,ratio, tt==thr==ratio))

# 3. Erosion under silence: odds multiply by (1-b)/(1-a) per silent period when b>a.
eps0, a, b, c, h = F(1,10), F(1,20), F(9,10), 1, 20
odds = eps0/(1-eps0)
n=0
while a/b <= odds*h/c and n < 1000:
    odds *= (1-b)/(1-a); n+=1
print("3. with eps0=%s a=%s b=%s h/c=%s: compliance condition fails after %d silent periods; LR per silence=%s" % (eps0,a,b,F(h,c),n,(1-b)/(1-a)))
# 3b. if a==b then press LR = 1 (uninformative)
print("3b. press LR b/a=%s; silence LR (1-b)/(1-a)=%s; b>a implies silence LR<1:", b/a, (1-b)/(1-a))

# 4. Indifference-style 'manage the news' does not arise: agent maximises unconditional E_P[V]. Coin/arm example with V(sh,.)=0.
# watch: 0.5*10 + 0.5*0 = 5 ; arm (press on tails -> shutdown, V=0 on tails): 0.5*10 + 0.5*0 = 5. No gain from the arm.
print("4. coin/arm: watch=5, arm=", F(1,2)*10 + F(1,2)*0, "-> no infinite improbability drive")
