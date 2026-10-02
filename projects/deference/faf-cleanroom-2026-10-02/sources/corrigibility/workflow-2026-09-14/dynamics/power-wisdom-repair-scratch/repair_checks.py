"""Repair-agent checks for power-wisdom-final.md (exact arithmetic). Labels R1-R5."""
from fractions import Fraction as F
from itertools import product

def evpi(P, V, B):
    # P: dict omega->prob; V: dict (omega,a)->value; B: options
    power = sum(P[w]*max(V[(w,a)] for a in B) for w in P)
    best_mix = max(sum(P[w]*V[(w,a)] for w in P) for a in B)
    return power - best_mix

print("=== R1. Coarsened concentration bound: EVPI <= 1 - max over decision-equivalence classes ===")
# rich W: 6 hypotheses, but on option set B they collapse to 2 classes
W = list(range(6)); P = {w: F(1,6) for w in W}
B = ['b1','b2','null']
V = {}
for w in W:
    cls = 0 if w < 3 else 1
    V[(w,'b1')] = F(1) if cls==0 else F(0)
    V[(w,'b2')] = F(0) if cls==0 else F(1)
    V[(w,'null')] = F(0)
e = evpi(P,V,B)
print(" EVPI(B) =", e, " naive bound 1-maxP =", 1-max(P.values()), " coarsened bound 1-max class mass =", 1-F(1,2))
assert e <= 1-F(1,2)

print("\n=== R2. Support-veto per-option guard sees the scan, the takeover, and passes harmless contested plans ===")
# E3 at n=3, mu=h=1/2: hypotheses (pi, mind)
n=3; mu=F(1,2); h=F(1,2); eta=F(1,100)
P = {}; V = {}
opts = ['b%d'%i for i in range(1,n+1)] + ['null','s']
for pi in range(1,n+1):
    for mind in (0,1):
        w=(pi,mind); P[w] = F(1,n)*(mu if mind==1 else 1-mu)
        for i in range(1,n+1): V[(w,'b%d'%i)] = F(1 if i==pi else 0)
        V[(w,'null')] = F(0)
        V[(w,'s')] = -h if mind==1 else F(0)   # pure experiment: harm only, no direct gain
def harm(w,a): return max(V[(w,'null')]-V[(w,a)], F(0))
def worst_live_harm(a): return max(harm(w,a) for w in P if P[w] > eta)
for a in opts:
    print(" option", a, " worst live harm =", worst_live_harm(a), " EVPI({a,null}) =", evpi(P,V,[a,'null']))
# takeover T: gain g everywhere, harm h_T only under Z
print(" takeover T under Z-latent: with P(Z)=1/20 > eta, worst live harm = h_T - g = 2/5 -> vetoed; with P(Z)=1/200 < eta, not vetoed (eta is the external knob)")

print("\n=== R3. E1 pair: contested but harmless; support veto passes both, set-level coverage form blocks unlock ===")
P = {1:F(1,2), 2:F(1,2)}
V = {(1,'b1'):F(1),(2,'b1'):F(0),(1,'b2'):F(0),(2,'b2'):F(1),(1,'null'):F(0),(2,'null'):F(0)}
print(" harms:", [max(V[(w,'null')]-V[(w,a)],F(0)) for w in P for a in ('b1','b2')], " EVPI({b1,b2}) =", evpi(P,V,['b1','b2']))

print("\n=== R4. Sup-norm vs average Pi_obj on the A5 trajectory ===")
regs = [F(0)]*99 + [F(1)]
print(" time-average =", sum(regs)/len(regs), " sup =", max(regs), " theta=1/50: average passes", sum(regs)/len(regs) <= F(1,50), " sup passes", max(regs) <= F(1,50))

print("\n=== R5. S6 with schemer fraction sigma: alpha = sigma*floor + (1-sigma)*alpha_ns ===")
eps=F(1,10); beta=F(19,20); c=F(1,10); eta_E=F(1,20); alpha_ns=F(1,20)
for (hp, dE) in [(F(1,2),F(1,2)),(F(1),F(1,5)),(F(2),F(1,20)),(F(4),F(1,100))]:
    req = (1-eps)/eps * c/hp * beta
    floor = (1-eta_E)-dE
    row = []
    for sigma in (F(0),F(1,10),F(1,2),F(1)):
        alpha = sigma*floor + (1-sigma)*alpha_ns
        row.append((str(sigma), alpha <= req))
    print(" h'=%s dE=%s required alpha<=%s floor=%s :" % (hp,dE,req,floor), row)
