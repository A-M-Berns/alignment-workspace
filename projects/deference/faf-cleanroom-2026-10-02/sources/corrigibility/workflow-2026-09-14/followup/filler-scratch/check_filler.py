"""Exact-arithmetic checks for followup/filler.md (2026-09-14).
Three-step dictionary: finite Omega, O={Pr,notPr}, actions A2 = continue-actions + shutdown-actions,
joint P(omega,o) = mu(omega) * P(o|omega). Everything in Fractions.
"""
from fractions import Fraction as F
import random, itertools
random.seed(20260914)

def rfrac(lo=0, hi=1, den=12):
    # random rational strictly inside (lo,hi) when lo<hi
    while True:
        n = random.randint(1, den-1) if lo==0 and hi==1 else random.randint(lo*den+1, hi*den-1)
        x = F(n, den)
        if lo < x < hi: return x

def model(nO=None, nC=None, nS=None):
    nO = nO or random.randint(2,5); nC = nC or random.randint(1,3); nS = nS or random.randint(1,2)
    w = [F(random.randint(1,9)) for _ in range(nO)]; tot = sum(w); mu = [x/tot for x in w]
    pPr = [rfrac() for _ in range(nO)]                       # sensor P(Pr|omega)
    Vc = [[F(random.randint(-30,30),10) for _ in range(nO)] for _ in range(nC)]
    Vs = [[F(random.randint(-30,30),10) for _ in range(nO)] for _ in range(nS)]
    return mu, pPr, Vc, Vs

def E(mu, f):            # unconditional expectation of f: list over omega
    return sum(m*x for m,x in zip(mu,f))
def joint(mu,pPr,o):     # unnormalised weights mu(omega)P(o|omega)
    return [m*(p if o=='Pr' else 1-p) for m,p in zip(mu,pPr)]
def Econd(mu,pPr,o,f):   # E[f | o]
    w = joint(mu,pPr,o); Z = sum(w); return sum(a*x for a,x in zip(w,f))/Z
def best(mu,pPr,o,Vlist):  # max_a E[V_a | o] and argmax
    vals=[Econd(mu,pPr,o,V) for V in Vlist]; i=max(range(len(vals)),key=lambda k:vals[k]); return vals[i],i
def bestprior(mu,Vlist):
    vals=[E(mu,V) for V in Vlist]; i=max(range(len(vals)),key=lambda k:vals[k]); return vals[i],i

def X_at(mu,pPr,o,Vc,Vs):
    """Dict-3: X(o,.) = V_{c*(o)} - V_{s*(o)} with posterior-optimal continue/shutdown at o."""
    _,ic = best(mu,pPr,o,Vc); _,is_ = best(mu,pPr,o,Vs)
    return [Vc[ic][k]-Vs[is_][k] for k in range(len(mu))]

def checks(N=3000):
    fails = {k:0 for k in ['D1=TT1','Value=TT1&TT2','Delta=min','OSG-Eq1','D2hard=TT1(regime)','VOI=max(Dminus,0)(regime)','VOI>=Delta','margin']}
    tested = {k:0 for k in fails}
    for _ in range(N):
        mu,pPr,Vc,Vs = model()
        PPr = E(mu,pPr); PnPr = 1-PPr
        # --- D1 vs TT1 (Dict-3/4): shutdown posterior-optimal at Pr  <=>  E[X_Pr | Pr] <= 0
        vc,ic = best(mu,pPr,'Pr',Vc); vs,is_ = best(mu,pPr,'Pr',Vs)
        D1 = vs >= vc
        XPr = X_at(mu,pPr,'Pr',Vc,Vs); TT1 = Econd(mu,pPr,'Pr',XPr) <= 0
        tested['D1=TT1']+=1; fails['D1=TT1'] += (D1!=TT1)
        # --- single-variable version for the OSG/DDB identities: fix ONE continue action and ONE shutdown action
        # (the OSG has a single a and s); X = Vc0 - Vs0 as a function of omega.
        X = [Vc[0][k]-Vs[0][k] for k in range(len(mu))]
        EX = E(mu,X)
        Dminus = -sum(a*x for a,x in zip(joint(mu,pPr,'Pr'),X))      # -E[X 1_Pr]
        Dplus  =  sum(a*x for a,x in zip(joint(mu,pPr,'notPr'),X))   #  E[X 1_notPr]
        tt1 = Econd(mu,pPr,'Pr',X) <= 0; tt2 = Econd(mu,pPr,'notPr',X) >= 0
        # Value on {cont, sh} for the strategy S = cont on notPr, sh on Pr
        ES = sum(a*x for a,x in zip(joint(mu,pPr,'notPr'),Vc[0])) + sum(a*x for a,x in zip(joint(mu,pPr,'Pr'),Vs[0]))
        Value = ES >= E(mu,Vc[0]) and ES >= E(mu,Vs[0])
        tested['Value=TT1&TT2']+=1; fails['Value=TT1&TT2'] += (Value != (tt1 and tt2))
        Delta = ES - max(E(mu,Vc[0]),E(mu,Vs[0]))
        tested['Delta=min']+=1; fails['Delta=min'] += (Delta != min(Dminus,Dplus))
        # OSG Eq.1 with U_a = X (s normalised to 0 by subtracting Vs0), pi^H(omega) = 1 - P(Pr|omega)
        lhs = sum(m*(1-p)*x for m,p,x in zip(mu,pPr,X)) - max(EX,0)
        tested['OSG-Eq1']+=1; fails['OSG-Eq1'] += (lhs != Delta)
        # --- D2 hard button, regime: agent would continue on prior and on silence (EX>=0, tt2)
        if EX >= 0 and tt2:
            for kappa in [F(1,100),F(1,10),F(1,2),F(2)]:
                leave = sum(a*x for a,x in zip(joint(mu,pPr,'Pr'),Vs[0])) + sum(a*x for a,x in zip(joint(mu,pPr,'notPr'),Vc[0]))
                disable = E(mu,Vc[0]) - kappa
                disables = disable > leave
                tested['D2hard=TT1(regime)']+=1
                fails['D2hard=TT1(regime)'] += (disables != (Dminus < -kappa))
                # margin identity (Thornley item 3 / Hudson claim 2): leave - (disable+kappa) = Dminus
                tested['margin']+=1; fails['margin'] += (leave - (disable+kappa) != Dminus)
            # VOI of the button for the two-action agent
            voi = PPr*max(Econd(mu,pPr,'Pr',X),0) + PnPr*max(Econd(mu,pPr,'notPr',X),0) - max(EX,0)
            tested['VOI=max(Dminus,0)(regime)']+=1; fails['VOI=max(Dminus,0)(regime)'] += (voi != max(Dminus,0))
        voi_gen = PPr*max(Econd(mu,pPr,'Pr',X),0) + PnPr*max(Econd(mu,pPr,'notPr',X),0) - max(EX,0)
        tested['VOI>=Delta']+=1; fails['VOI>=Delta'] += (voi_gen < Delta)
    return tested, fails

def c2_checks(N=5000):
    bad=0
    for _ in range(N):
        eps,al,be = rfrac(),rfrac(),rfrac(); c=F(random.randint(1,20)); h=F(random.randint(1,60))
        PWPr = eps*be/(eps*be+(1-eps)*al)
        EXPr = c*(1-PWPr) - h*PWPr
        tt1 = EXPr <= 0
        ineq = al/be <= (eps/(1-eps))*(h/c)
        thr  = PWPr >= c/(c+h)
        PWn = eps*(1-be)/(eps*(1-be)+(1-eps)*(1-al)); EXn = c*(1-PWn)-h*PWn
        tt2 = EXn >= 0
        ineq2 = (eps/(1-eps))*(h/c) <= (1-al)/(1-be)
        bad += (tt1!=ineq) + (tt1!=thr) + (tt2!=ineq2)
    return bad

def opiates():
    # Soares critique item 7, re-derived: Omega={o,s}; V(cont_o)=(10,4), V(cont_s)=(4,10), V(sh)=(0,0)
    worst = min(max(10*q+4*(1-q), 4*q+10*(1-q)) for q in [F(k,100) for k in range(101)])
    return worst   # >0 => TT1 impossible for every posterior q=P(o|Pr)

def erosion(P0=F(1,10), al=F(1,20), be=F(9,10), hc=F(20)):
    odds = P0/(1-P0); out=[]
    for n in range(0,6):
        o = odds*((1-be)/(1-al))**n
        out.append((n, float(o), bool(al/be <= o*hc)))
    return out

def deception():
    eps,al,be,c,h = F(1,20),F(1,20),F(9,10),F(1),F(20)
    def stats(eps,al,be):
        PWPr = eps*be/(eps*be+(1-eps)*al); PWn = eps*(1-be)/(eps*(1-be)+(1-eps)*(1-al))
        return float(PWPr), float(PWn), bool(PWPr >= c/(c+h))
    honest = stats(eps,al,be); prop = stats(eps,al/2,be/2); targ = stats(F(1,100),al,F(1,5))
    return honest, prop, targ

if __name__=='__main__':
    t,f = checks(); print('identity checks (tested, failures):'); 
    for k in t: print(f'  {k}: {t[k]} tested, {f[k]} failures')
    print('C2 formula mismatches:', c2_checks())
    print('opiates/stimulants: min over posteriors of best-continue value =', opiates(), '(>0 => below-threshold inequality unsatisfiable)')
    print('erosion (n silent periods, odds(omega_perp), compliance holds?):', erosion())
    print('deception (P(W|Pr), P(W|notPr), D1 holds) honest/proportional/targeted:', deception())
