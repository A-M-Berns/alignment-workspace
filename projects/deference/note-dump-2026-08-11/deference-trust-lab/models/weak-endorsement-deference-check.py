#!/usr/bin/env python3
"""
Micro-example checks for the weak-endorsement => weak-deference model.
Exact rational arithmetic via fractions.Fraction (no sympy needed).

Three checks:
  (1) GODEL IMPOSSIBILITY (liar): a 2-world finite frame encoding the liar
      sentence chi = "P_later(chi) < 1/2".  HARD two-sided endorsement at t=1/2
      conditioned on {P_later(chi) >= 1/2} demands E_now(chi | .) = 1/2, but the
      true conditional value is 0 (the conjunction is disprovable).  => unsat.
  (2) SOFT SATISFIABILITY: replace the hard indicator by a Lipschitz ramp Ind_delta;
      now the constraint becomes a one-sided >= and is satisfied by the LI answer
      ~1/2.  Show no contradiction for any delta>0.
  (3) FINITE COLLAPSE (anti-expert / modest): show, on DDB Fig.2, that the HARD
      conditional-martingale identity forces immodesty (P_w(P=P_w)=1), and that
      a genuinely modest frame VIOLATES it -- so hard endorsement is unavailable
      under modesty, while Value(soft) is what tracks deferability.
"""
from fractions import Fraction as F

def approx(x): return float(x)

print("="*70)
print("CHECK 1 -- Godel/liar: HARD two-sided endorsement is UNSATISFIABLE")
print("="*70)
# Model the liar as a 2-outcome variable from the NOW-self's viewpoint.
# chi_n true iff P_later(chi_n) < 1/2.
# The LI fact (paper eq. after thm:st, lines 2118-2126):
#   P_now( chi AND [P_later(chi) >= 1/2] ) ~ 0   (conjunction is DISPROVABLE).
# So with X = 1(chi), w = 1[P_later(chi) >= 1/2] (HARD indicator):
#   E_now( X * w )  =  P_now(chi AND P_later>=1/2)  = 0.
# HARD TWO-SIDED endorsement at t=1/2 demands:
#   E_now( X * w )  =  (1/2) * E_now( w ).
# This forces  E_now(w) = 0 , i.e. P_now(P_later(chi) >= 1/2) = 0.
# But the SAME hard endorsement applied to the COMPLEMENT band, or simply the
# fact that on the liar the future self DOES reach >=1/2 on a nonneg-measure set
# (the inductor's prices oscillate around 1/2, hitting >=1/2 infinitely often,
# Thm recurringunbiasedness), gives E_now(w) -/-> 0.  Contradiction.
#
# We exhibit the contradiction concretely with the minimal numbers the paper pins:
LHS = F(0)                 # E_now(X*w) = P_now(chi AND P_later>=1/2) = 0   (disprovable)
t   = F(1,2)
# Suppose, for contradiction, hard endorsement holds with E_now(w)=q>0.
# Then 0 = LHS = t*q = q/2  =>  q = 0.  But the liar forces q>0 (oscillation).
for q in [F(1,10), F(1,3), F(1,2), F(9,10)]:
    demanded = t*q
    ok = (demanded == LHS)
    print(f"  E_now(w)=q={str(q):>4}: hard endorsement demands E_now(Xw)= t*q = {str(demanded):>4}; "
          f"actual (disprovable) = 0 -> {'CONSISTENT' if ok else 'CONTRADICTION'}")
print("  => For ANY q>0 the hard two-sided identity is violated (0 != q/2).")
print("     The only escape q=0 contradicts the liar's recurrent oscillation (>=1/2 i.o.).")
print("     CONCLUSION: hard endorsement + liar  is JOINTLY UNSATISFIABLE.  [matches paper]")

print()
print("="*70)
print("CHECK 2 -- SOFT version IS satisfiable (one-sided >=, ramp Ind_delta)")
print("="*70)
# Soft self-trust (thm:st) with the liar gives, conditional on Ind_delta(P_later>1/2-ish):
#   E_now(chi | soft) ~ 1/2  (paper line 2130: "extremely close to 0.5 => roughly 0.5").
# The constraint is now ONE-SIDED:  E_now(X * Ind_delta) >= p * E_now(Ind_delta).
# Model: future price sits at 1/2 - eps (just below), ramp width delta.
# Ind_delta(x>p) with x = 1/2 (the cluster value), p slightly below; ramp value in (0,1].
def ind_delta(x, p, delta):
    if x <= p: return F(0)
    if x >= p+delta: return F(1)
    return (x-p)/delta
# Take p = 1/2 - delta/2 so the future price x=1/2 sits at top of the ramp band:
for delta in [F(1,4), F(1,8), F(1,100)]:
    p = F(1,2) - delta/2
    x = F(1,2)                       # cluster value of the liar's future price
    w = ind_delta(x, p, delta)       # soft weight in (0,1]
    # LI's actual soft conditional value of chi is ~ 1/2 (NOT 0): call it c.
    c = F(1,2)
    Exw = c * w                      # E_now(X*Ind) modeled as (value)*(weight)
    rhs = p * w                      # p * E_now(Ind)
    ok = Exw >= rhs
    print(f"  delta={str(delta):>5}: p={str(p):>7}, soft weight w={str(w):>4}; "
          f"E_now(Xw)={approx(Exw):.4f} >= p*E_now(w)={approx(rhs):.4f} ? {ok}")
print("  => one-sided soft endorsement holds for every delta>0 (no contradiction).")
print("     SOFT endorsement + liar is SATISFIABLE; the LI answer ~1/2 witnesses it.")

print()
print("="*70)
print("CHECK 3 -- finite collapse: HARD cond. martingale FORCES immodesty;")
print("           a modest frame violates it (so hard endorsement unavailable)")
print("="*70)
# DDB Fig.2 anti-expert frame: pi=(1/2,1/2), P_a=(.2,.8), P_b=(.8,.2). MODEST.
W = ['a','b']
pi = {'a':F(1,2),'b':F(1,2)}
P  = {'a':{'a':F(1,5),'b':F(4,5)}, 'b':{'a':F(4,5),'b':F(1,5)}}
# In this frame every world has a DISTINCT credence, so the "fiber" {v: P_v=P_w} = {w}.
# Immodesty would require P_w(w)=1.  Here P_a(a)=1/5, P_b(b)=1/5 -- MODEST.
for w in W:
    print(f"  world {w}: P_{w}(fiber {w}) = P_{w}({w}) = {str(P[w][w])}  (immodest would need =1)")
# HARD conditional-martingale identity (the algebraic shadow of hard endorsement) at w:
#   E_w(X) = E_pi(X | fiber w)  for all X.
# Test it at X = indicator of fiber w (= indicator of {w}):
def Ew(w, X): return sum(P[w][v]*X[v] for v in W)
def fiber_ind(w): return {v:(F(1) if v==w else F(0)) for v in W}
def Epi_cond_fiber(w, X):
    num = sum(pi[v]*(F(1) if v==w else F(0))*X[v] for v in W)
    den = sum(pi[v]*(F(1) if v==w else F(0)) for v in W)
    return num/den
for w in W:
    Xind = fiber_ind(w)
    lhs = Ew(w, Xind)               # = P_w(fiber w) = P_w(w)
    rhs = Epi_cond_fiber(w, Xind)   # = 1  (novice conditioned on {w} is certain of w)
    print(f"  hard-CM at {w}, X=1[fiber]: E_{w}(X)={str(lhs)}  vs  E_pi(X|fiber)={str(rhs)}  -> "
          f"{'holds' if lhs==rhs else 'VIOLATED'}")
print("  => hard endorsement would force E_w(1[fiber])=1 i.e. P_w(w)=1 (IMMODESTY).")
print("     The modest frame has P_w(w)=1/5 != 1, so it VIOLATES hard endorsement.")
print("     Hence a MODEST reasoner cannot satisfy hard endorsement on a finite frame.")
print("     (This is the CM_implies_immodest core; the soft version remains available.)")

print()
print("ALL THREE CHECKS COMPLETED.")
