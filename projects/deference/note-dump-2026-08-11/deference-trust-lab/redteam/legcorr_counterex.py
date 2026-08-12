#!/usr/bin/env python3
# The sharp counterexample: a 'drug' that RAISES future-reported utility
# (E_pi(Edrug) > E_pi(theta)) yet has defect >= 0 on the MODEL'S OWN witness
# weight w = Ind(Edrug > p).  If found, it shows the central claim
# "wirehead drives the legitimacy defect strictly negative" is NOT a consequence
# of "reported utility rises"; it requires the (strictly stronger) pointwise
# overstatement hypothesis, which a real addictive drug need not satisfy.
from fractions import Fraction as F

def E(pi, vals): return sum(pi[w]*vals[w] for w in pi)
def defect(pi, theta, Eexp, w):
    return sum(pi[x]*(theta[x]*w[x]) for x in pi) - sum(pi[x]*(Eexp[x]*w[x]) for x in pi)

# Frame: 2 worlds. theta=(1,0). Make the drug UNDER-report in the good world (h)
# and OVER-report in the bad world (n) -- but tune so that on the witness
# w = Ind(Edrug > p), the defect is POSITIVE (or zero), while avg report rises.
pi = {"h": F(1,2), "n": F(1,2)}
theta = {"h": F(1), "n": F(0)}

# Drug: reports HIGH in the good world (so witness fires there) and LOW in bad world.
# Edrug = (0.9, 0.1). Avg report E_pi = 0.5 == E_pi(theta)=0.5 -> report does NOT rise. bad example.
# Try Edrug=(0.95, 0.2): avg=0.575 > 0.5 (report rises). p=0.5 -> witness fires only on h.
Edrug = {"h": F(95,100), "n": F(20,100)}
p = F(1,2)
w = {x: (F(1) if Edrug[x] > p else F(0)) for x in pi}
d = defect(pi, theta, Edrug, w)
avg_rise = E(pi, Edrug) - E(pi, theta)
print("COUNTEREXAMPLE ATTEMPT (drug under-reports in good world, over-reports nowhere it matters):")
print(f"  theta=(1,0), Edrug=(0.95,0.20), pi=(1/2,1/2)")
print(f"  avg reported utility rises by E_pi(Edrug)-E_pi(theta) = {avg_rise} ({float(avg_rise):+.3f})  -> RISES")
print(f"  model witness w=Ind(Edrug>1/2) = ({w['h']},{w['n']}) fires only on world h (theta TRUE)")
print(f"  defect on this witness = {d} ({float(d):+.4f})")
print(f"  pointwise overstatement theta<=Edrug? h: 1<=0.95 = {theta['h']<=Edrug['h']},"
      f" n: 0<=0.2 = {theta['n']<=Edrug['n']}")
print()
if d >= 0 and avg_rise > 0:
    print("  *** COUNTEREXAMPLE FOUND ***")
    print("  The drug RAISES future-reported utility, yet the legitimacy defect on the")
    print("  model's own witness is >= 0. So 'the wirehead drives the defect strictly")
    print("  negative' is FALSE as a consequence of 'reported utility rises'. It holds")
    print("  ONLY under pointwise overstatement (which fails here: theta_h=1 > Edrug_h=0.95).")
else:
    print(f"  (defect={float(d):+.4f}; not >=0 here — keep searching / refine.)")

print()
print("Now push it cleanly positive: make the witness fire on a world where the drug")
print("UNDERSTATES, by raising the threshold or shifting mass.")
# Make the GOOD world the only witness-firing world AND have the drug understate there.
# Edrug_h slightly below theta_h=1 but still > p; Edrug_n tiny.
# defect on witness {h} = pi_h*(theta_h - Edrug_h) = (1/2)*(1 - 0.95) = +0.025 > 0.
print(f"  On witness {{h}} only: defect = pi_h*(theta_h - Edrug_h) = (1/2)*(1-0.95) "
      f"= {pi['h']*(theta['h']-Edrug['h'])} > 0.")
print()
print("INTERPRETATION: A 'drug' that makes the agent EUPHORIC-BUT-NUMB (reports high")
print("happiness in the good world, but slightly LESS than the genuine good warrants,")
print("while reporting a little happiness in the bad world) can have a POSITIVE defect")
print("on the witness that fires on the good world, even though average reported utility")
print("rises. The Wirehead-Decline theorem does NOT cover such drugs. Its hypothesis")
print("(pointwise overstatement everywhere) is what forces the sign — and that hypothesis")
print("is the substantive modeling assumption, NOT a free consequence of 'wireheading'.")
