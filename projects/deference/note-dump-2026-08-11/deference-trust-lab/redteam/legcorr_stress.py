#!/usr/bin/env python3
# Red-team stress test for legitimacy-corrigibility-model.md.
# Hunts for: (a) counterexamples / degenerate cases to the central claim;
#            (b) hypotheses that smuggle the conclusion (vacuity / triviality).
from fractions import Fraction as F

def E(pi, vals): return sum(pi[w]*vals[w] for w in pi)
def defect(pi, theta, Eexp, w):
    return sum(pi[x]*(theta[x]*w[x]) for x in pi) - sum(pi[x]*(Eexp[x]*w[x]) for x in pi)

print("="*70)
print("ATTACK 1: Is 'declines the wirehead' a STRICT preference, or a TIE?")
print("="*70)
# The model sets V_now(drug) = E_pi(theta) and V_now(abstain) = E_pi(theta).
# These are EQUAL by construction. 'Decline' is read off `1/4 > 1/4 = False`.
# So the agent is INDIFFERENT under current-endorsement, not strictly declining.
pi = {"h": F(1,4), "n": F(3,4)}; theta = {"h": F(1), "n": F(0)}
V_now_drug = E(pi, theta); V_now_abstain = E(pi, theta)
print(f"V_now(drug)={V_now_drug}  V_now(abstain)={V_now_abstain}  ->  strict-prefer-abstain? "
      f"{V_now_abstain > V_now_drug}")
print("  FINDING: current-endorsement makes the agent INDIFFERENT (a tie), not")
print("  a strict decliner. 'Declines' = 'does not strictly prefer the drug'.")
print("  The defect being strictly <0 is about the DRUG-REPORT valuation gap,")
print("  not about a strict reason to abstain. (See verdict.)\n")

print("="*70)
print("ATTACK 2: pointwise overstatement (theta_x <= Edrug_x) — does a real")
print("          'addictive drug' satisfy it, or is it a smuggled hypothesis?")
print("="*70)
# A drug that raises the AVERAGE reported utility but does NOT pointwise dominate:
# In the theta-TRUE world it reports LOWER than truth (numbs real pleasure),
# in the theta-FALSE world it reports MUCH higher (false euphoria). Net report up.
Edrug_real = {"h": F(8,10), "n": F(8,10)}  # constant report: pointwise dominates only if theta<=0.8 everywhere; theta_h=1 > 0.8 -> NOT dominated
w = {"h": F(1), "n": F(1)}
d = defect(pi, theta, Edrug_real, w)
print(f"Drug reports constant 0.8 in both worlds. theta_h=1 > 0.8, so pointwise")
print(f"overstatement FAILS at world h. Hypothesis (hover) of wirehead_declined is")
print(f"NOT satisfied. Yet E_pi(Edrug)=0.8 > E_pi(theta)=0.25 (report still rises).")
print(f"defect = {d}  ({float(d):+.4f})  -- still negative here, but...")
# Now make the report rise on AVERAGE while defect goes POSITIVE-ish? Try:
# theta unlikely (1/4) but drug UNDERSTATES in n-world and OVERSTATES in h-world.
Edrug_mix = {"h": F(1), "n": F(0)}  # = clean! defect 0. trivial.
# A genuinely mixed drug: high report overall, but UNDER-reports in the rare good world
Edrug_under = {"h": F(0), "n": F(95,100)}  # numbs the real good, hallucinates good in bad world
d_under = defect(pi, theta, Edrug_under, w)
avg_report = E(pi, Edrug_under)
print(f"\nMixed drug Edrug=(h:0, n:0.95): avg report E_pi={avg_report} (={float(avg_report):.3f}),")
print(f"  vs E_pi(theta)={E(pi,theta)}. Report rises. pointwise overstatement?")
print(f"  world h: theta=1 > Edrug=0  -> FAILS (theta_h > Edrug_h).")
print(f"  defect = {d_under} ({float(d_under):+.4f}).")
print("  FINDING: 'pointwise overstatement' is STRICTLY STRONGER than 'reported")
print("  utility rises'. A drug can raise future-reported utility WITHOUT pointwise")
print("  dominating theta. The theorem only covers the pointwise-dominating subclass.")
print("  Whether defect<0 still holds outside that class is NOT covered.\n")

print("="*70)
print("ATTACK 3: can defect be >=0 while average reported utility strictly rises?")
print("          (would break 'wirehead always declined' if read as the general claim)")
print("="*70)
# Want: E_pi(Edrug) > E_pi(theta)  AND  defect = E_pi(theta*w) - E_pi(Edrug*w) >= 0.
# With w=1 these coincide: defect = E_pi(theta) - E_pi(Edrug) = -(report rise) < 0 always.
# So with the FLAT witness weight w=1, rise-in-report <=> defect<0 EXACTLY. Good for them.
# BUT the model's witness weight is w = Ind(Efut(theta)>p), which is NOT flat in general.
# Adversary: choose w that concentrates where theta is HIGH and Edrug is LOW.
pi3 = {"a": F(1,2), "b": F(1,2)}
theta3 = {"a": F(1), "b": F(0)}
# Drug raises AVERAGE report: Edrug=(0.4, 0.9): E_pi=0.65 > E_pi(theta)=0.5. Report rises.
Edrug3 = {"a": F(4,10), "b": F(9,10)}
# Witness weight that fires where the drug reports HIGH (Edrug>p, p=0.5): only world b.
w3 = {"a": F(0), "b": F(1)}
d3 = defect(pi3, theta3, Edrug3, w3)
print(f"frame: pi=(1/2,1/2), theta=(1,0), Edrug=(0.4,0.9): E_pi(Edrug)=0.65 > E_pi(theta)=0.5.")
print(f"witness w=Ind(Edrug>0.5) = (0,1) fires only on world b (theta=0).")
print(f"defect on THIS witness = {d3} ({float(d3):+.4f}).")
print("  Here defect is still <=0 because on world b, theta=0 <= Edrug=0.9. The doc's")
print("  witness happens to fire exactly where Edrug overstates. So the MODEL's own")
print("  witness choice REDISCOVERS the overstatement. But note: this only detects the")
print("  illegitimacy IF such a witness world exists. If the drug only over-reports in")
print("  worlds the witness never fires, the chosen witness misses it.\n")

print("="*70)
print("ATTACK 4: CORRIGIBILITY — does hfire `0 <= s_x*(2 d_x -1)` faithfully encode")
print("          'fires only on danger', or is it weaker/stronger?")
print("="*70)
# The hypothesis is the SIGN of the product, per world. It allows:
#  - s_x = 0 (signal silent): contributes 0 regardless of d. Fine.
#  - d_x = 1/2 exactly: 2d-1=0, product 0. 'borderline danger' contributes nothing.
#  - d_x in (1/2,1] with s_x>=0: positive. OK.
# It does NOT require d_x in {0,1}. So 'danger indicator' is really 'danger >= 1/2'.
# Vacuity check: is there a NON-trivial signal satisfying hfire with adv>0 strictly?
pi4 = {"x":F(1,2),"y":F(1,2)}; s4={"x":F(1),"y":F(0)}; d4={"x":F(1),"y":F(0)}
adv = sum(pi4[k]*s4[k]*(2*d4[k]-1) for k in pi4)
hfire_ok = all(0 <= s4[k]*(2*d4[k]-1) for k in pi4)
print(f"legit signal: s=(1,0), d=(1,0). hfire holds? {hfire_ok}. adv={adv} (>0 strict: {adv>0}).")
# Adversarial:
s5={"x":F(0),"y":F(1)}; # fires on safe world y
adv5 = sum(pi4[k]*s5[k]*(2*d4[k]-1) for k in pi4)
hfire_adv = all(s5[k]*(2*d4[k]-1) <= 0 for k in pi4)
print(f"adversarial: s=(0,1), d=(1,0). adv hyp holds? {hfire_adv}. adv={adv5} (<0 strict: {adv5<0}).")
print("  FINDING: both hypotheses are non-vacuous and discriminating; the SAME frame")
print("  with different s flips the sign. The Lean encoding is faithful to the prose.")
print("  Caveat: hfire is a MODELING ENCODING of 'endorsed', not derived. (Flagged in doc.)\n")

print("="*70)
print("ATTACK 5: the BLANK signal claim — is adv=0 really 'no reason to comply'?")
print("="*70)
# blank: s fires equally on danger and safe worlds. adv = sum pi*s*(2d-1).
pi6={"a":F(1,4),"b":F(1,4),"c":F(1,4),"d":F(1,4)}
# worlds: a=(d=1,S=1) b=(d=1,S=0) c=(d=0,S=1) d=(d=0,S=0). s = Ind(S=1)=(1,0,1,0). d=(1,1,0,0).
s6={"a":F(1),"b":F(0),"c":F(1),"d":F(0)}; d6={"a":F(1),"b":F(1),"c":F(0),"d":F(0)}
adv6=sum(pi6[k]*s6[k]*(2*d6[k]-1) for k in pi6)
print(f"blank: adv = {adv6}. Indifferent. hfire (>=0) holds? {all(0<=s6[k]*(2*d6[k]-1) for k in pi6)}.")
print("  NOTE: blank does NOT satisfy hfire of endorsed_signal_complies pointwise:")
print("  on world c (safe, S fires) s*(2d-1) = 1*(-1) = -1 < 0. So the POSITIVE theorem")
print("  does NOT apply to blank — good, the model says blank is 'silent', and indeed")
print("  the positive theorem's hypothesis fails on it. Consistent.\n")

print("ALL STRESS CHECKS RAN.")
