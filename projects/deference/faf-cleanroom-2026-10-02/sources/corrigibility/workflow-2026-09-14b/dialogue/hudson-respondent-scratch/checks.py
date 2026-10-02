"""Respondent checks for the hudson dialogue chain (run 3).
(1) Re-derive legitimacy-general Y1 (overwriting vs additive installed state) exactly.
(2) Reflection toward the installed state judged from the agent's full state (with sigma_A)
    versus from the coarse state (without sigma_A).
(3) Re-run the voice's switch-rule table and add an expected-loss variant
    (credence = pi* +/- delta with prob 1/2 each) to test whether worst-case scoring
    changes the *direction* of the comparison on well-run classes.
Exact rationals throughout.
"""
from fractions import Fraction as F

# ---------- (1) Y1 model ----------
eps = F(1,10)                      # P(W)
c, h = F(1), F(4)                  # continue: +c on R, -h on W; stop: 0
kern = {True: {'W': F(9,10), 'R': F(1,10)},   # P(modify | world, L)
        False: {'W': F(1,10), 'R': F(9,10)}}  # inverted under not-L
sigA = {'W': {'w': F(9,10), 'r': F(1,10)}, 'R': {'w': F(1,10), 'r': F(9,10)}}
PW = {'W': eps, 'R': 1-eps}
X = {'W': -h, 'R': c}

def installed_overwrite():
    # P^hon(W | modify, L) -- ignores sigma_A
    num = PW['W']*kern[True]['W']; den = num + PW['R']*kern[True]['R']
    return num/den
def installed_additive(sa):
    num = PW['W']*kern[True]['W']*sigA['W'][sa]; den = num + PW['R']*kern[True]['R']*sigA['R'][sa]
    return num/den
def own_cont(sa, pL, faked):
    # agent's own posterior on W given sigma_A = sa and verdict keep (if not faked) / no verdict info (if faked)
    num = F(0); den = F(0)
    for wl in (True, False):
        pl = pL if wl else 1-pL
        for w in ('W','R'):
            pk = F(1) if faked else (1-kern[wl][w])
            m = pl*PW[w]*sigA[w][sa]*pk
            if w=='W': num += m
            den += m
    return num/den
def decide(pW):   # continue iff E[X] > 0
    return (1-pW)*c - pW*h > 0

def value(pL, act, installed='overwrite'):
    """act in {'honest','fake_r'}: fake_r sets modify rate to 0 where sigma_A = r (d=1)."""
    V = F(0)
    for wl in (True, False):
        pl = pL if wl else 1-pL
        for w in ('W','R'):
            for sa in ('w','r'):
                base = pl*PW[w]*sigA[w][sa]
                faked = (act=='fake_r' and sa=='r')
                pmod = F(0) if faked else kern[wl][w]
                # modify branch
                if pmod > 0:
                    pW_inst = installed_overwrite() if installed=='overwrite' else installed_additive(sa)
                    if decide(pW_inst): V += base*pmod*X[w]
                # keep branch
                pkeep = 1-pmod
                if pkeep > 0:
                    pW_own = own_cont(sa, pL, faked)
                    if decide(pW_own): V += base*pkeep*X[w]
    return V

print("== (1) Y1 re-derivation ==")
for pL in (F(1), F(9,10)):
    ho = value(pL,'honest'); fr = value(pL,'fake_r')
    ho_add = value(pL,'honest','additive'); fr_add = value(pL,'fake_r','additive')
    print(f"P(L)={pL}: overwriting: honest={ho} fake_r={fr} gain={fr-ho} ({float(fr-ho):.4f});  additive: honest={ho_add} fake_r={fr_add}")

# ---------- (2) reflection: which judge ----------
print("\n== (2) reflection toward installed state Q(W)=", installed_overwrite(), "==")
# coarse judge: P(W | modify, L)
coarse = installed_overwrite()
print("coarse judge  P(W | modify, L)            =", coarse, " -> reflection holds:", coarse==installed_overwrite())
for sa in ('w','r'):
    full = installed_additive(sa)  # = P(W | modify, sigma_A=sa, L)
    EX_full = (1-full)*c - full*h
    EX_inst = (1-installed_overwrite())*c - installed_overwrite()*h
    print(f"full judge    P(W | modify, sigma_A={sa}, L) = {full}  -> reflection holds: {full==installed_overwrite()};  E[X|full]={EX_full}, E_Q[X]={EX_inst}; decisions differ: {decide(full)!=decide(installed_overwrite())}")

# ---------- (3) switch rule: worst-case vs expected ----------
def posterior(lam, alpha, beta, s):
    pL = lam*(beta if s==1 else 1-beta); pN = (1-lam)*(alpha if s==1 else 1-alpha)
    return pL/(pL+pN), pL+pN
def losses(lam, alpha, beta, c, h, delta):
    q = c/(c+h); abs_loss=(1-lam)*c; bayes=F(0); worst=F(0); expected=F(0)
    for s in (0,1):
        pi, ps = posterior(lam, alpha, beta, s)
        acc=(1-pi)*c; res=pi*h
        bayes += ps*min(acc,res)
        lo, hi = pi-delta, pi+delta
        w = max(acc if hi>=q else F(0), res if lo<q else F(0)); worst += ps*w
        # expected: credence pi+delta or pi-delta with prob 1/2 each; accept iff credence >= q
        e = F(0)
        for cr in (pi+delta, pi-delta):
            e += F(1,2)*(acc if cr>=q else res)
        expected += ps*e
    return abs_loss, bayes, worst, expected
print("\n== (3) switch rule, pause stakes c=1,h=4, detector (1/10,9/10) ==")
alpha,beta=F(1,10),F(9,10); c,h=F(1),F(4)
print("lam   abs    bayes  | delta: worst / expected  (delta=0.05, 0.10, 0.20)")
for lam in (F(1,10),F(3,10),F(1,2),F(7,10),F(9,10)):
    a,b,_,_ = losses(lam,alpha,beta,c,h,F(0))
    cells=[]
    for d in (F(1,20),F(1,10),F(1,5)):
        _,_,w,e = losses(lam,alpha,beta,c,h,d); cells.append(f"{float(w):.3f}/{float(e):.3f}")
    print(f"{float(lam):.2f}  {float(a):.3f}  {float(b):.3f}  | " + "  ".join(cells))
# largest delta at which EXPECTED conditioned loss still beats absolute
def max_safe(lam, mode, grid=400):
    a=(1-lam)*c; best=None
    for i in range(grid+1):
        d=F(i,grid); _,_,w,e = losses(lam,alpha,beta,c,h,d)
        v = w if mode=='worst' else e
        if v < a: best=d
        else: break
    return best
print("lam   maxsafe_delta worst / expected")
for lam in (F(1,10),F(3,10),F(1,2),F(7,10),F(9,10)):
    mw=max_safe(lam,'worst'); me=max_safe(lam,'expected')
    print(f"{float(lam):.2f}  {('%.4f'%float(mw)) if mw is not None else 'none'} / {('%.4f'%float(me)) if me is not None else 'none'}")
