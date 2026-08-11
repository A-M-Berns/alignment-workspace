#!/usr/bin/env python3.11
"""
Machine-check for the LI Value proof in deference-in-logical-induction.md (sec. 3-5).

What this DOES check (rigorously):
  A. SYMBOLIC: the proof's central decomposition is an exact algebraic identity,
       gap_i = D_CM + D_UM_i + E_pi(barm - m_i),
     valid for EVERY finite frame / menu / weight family (sympy, all-symbolic).
  B. The softmax/Gibbs bound  barm >= max_j m_j - delta*log k  (identity barm = L - delta*H).
  C. EXACT (rationals): DDB Fig 2 (anti-expert) & Fig 3, incl. the sec.4 "trap"
     (unconditional martingale holds, yet Value fails because D_CM != 0).
  D. EXACT: conditional martingale  =>  Value, on random partitional/prior frames.
  E. EXACT: finite-collapse (sec 5.2): on finite frames, conditional martingale
     => immodesty; equivalently every modest finite frame breaks cond. martingale.
  F. EXACT/float: the LI regime in miniature -- modest, near-cond-martingale frames
     satisfy Value up to the predicted error  |D_CM| + |D_UM| + delta*log k.

What this does NOT check: the asymptotic LI layer itself -- that the real theorems
  thm:ccee / thm:cee / thm:loe drive D_CM, D_UM -> 0 and that the ~_n bookkeeping
  closes. That would require formalizing the Logical Induction paper and is out of scope.
"""

from fractions import Fraction as F
import math, random, itertools

# ----------------------------------------------------------------------------- helpers (exact)
def dot(p, x):                       # sum_w p[w]*x[w]
    return sum(pw*xw for pw, xw in zip(p, x))

def Eexp(frame_P, w, X):             # E_w(X) = expert's expectation of X at world w
    return dot(frame_P[w], X)

def Erv(frame_P, X):                 # the random variable  w |-> E_w(X)
    return [Eexp(frame_P, w, X) for w in range(len(frame_P))]

def Epi(pi, X):                      # novice expectation  E_pi(X)
    return dot(pi, X)

def hard_select(frame_P, menu):
    """recommended strategy: at each w, index j maximizing E_w(O^j) (ties -> lowest j)."""
    sel = []
    for w in range(len(frame_P)):
        ms = [Eexp(frame_P, w, O) for O in menu]
        best = max(range(len(menu)), key=lambda j: ms[j])  # max() picks first on ties
        sel.append(best)
    return sel

def strategy_return(frame_P, menu, sel):     # hatS(w) = O^{sel(w)}(w)
    return [menu[sel[w]][w] for w in range(len(frame_P))]

def fiber(frame_P, w):                       # {v : P_v == P_w}
    return [v for v in range(len(frame_P)) if frame_P[v] == frame_P[w]]

def is_cond_martingale(pi, frame_P):
    """exact conditional martingale  <=>  P_w == pi(.|fiber(w))  for all w in supp(pi)."""
    for w in range(len(pi)):
        if pi[w] == 0:
            continue
        fib = fiber(frame_P, w)
        mass = sum(pi[v] for v in fib)
        cond = [(pi[v]/mass if v in fib else F(0)) for v in range(len(pi))]
        if frame_P[w] != cond:
            return False
    return True

def is_immodest(pi, frame_P):
    """immodest: every supported w is certain of its own fiber, P_w(fiber(w)) == 1."""
    for w in range(len(pi)):
        if pi[w] == 0:
            continue
        if sum(frame_P[w][v] for v in fiber(frame_P, w)) != 1:
            return False
    return True

def value_gaps(pi, frame_P, menu):
    """for the hard recommended strategy, return [E_pi(S) - E_pi(O^i)] for each option i."""
    sel = hard_select(frame_P, menu)
    S = strategy_return(frame_P, menu, sel)
    ES = Epi(pi, S)
    return [ES - Epi(pi, menu[i]) for i in range(len(menu))]

def defects(pi, frame_P, menu, alpha):
    """
    alpha[j][w] = weight on option j at world w (sum_j alpha[j][w] == 1).
    Returns the three terms of the decomposition for the WORST option i (lowest gap target),
    plus the realized gap, all exact.
    """
    n = len(frame_P)
    m = [Erv(frame_P, O) for O in menu]                       # m[j][w] = E_w(O^j)
    hatS = [sum(alpha[j][w]*menu[j][w] for j in range(len(menu))) for w in range(n)]
    barm = [sum(alpha[j][w]*m[j][w]    for j in range(len(menu))) for w in range(n)]
    D_CM = sum(pi[w]*sum(alpha[j][w]*(menu[j][w]-m[j][w]) for j in range(len(menu)))
               for w in range(n))
    out = []
    for i in range(len(menu)):
        D_UM_i = Epi(pi, m[i]) - Epi(pi, menu[i])
        E_barm_minus_mi = sum(pi[w]*(barm[w]-m[i][w]) for w in range(n))
        gap_i = Epi(pi, hatS) - Epi(pi, menu[i])
        out.append(dict(i=i, gap=gap_i, D_CM=D_CM, D_UM=D_UM_i,
                        soft=E_barm_minus_mi, rhs=D_CM+D_UM_i+E_barm_minus_mi))
    return out

def rand_dist(n, rng, dmax=6):
    r = [F(rng.randint(1, dmax)) for _ in range(n)]
    s = sum(r); return [x/s for x in r]

def rand_vec(n, rng, lo=-4, hi=4):
    return [F(rng.randint(lo, hi)) for _ in range(n)]

PASS = {"n":0,"fail":0}
def check(name, cond, extra=""):
    ok = bool(cond); PASS["n"]+=1; PASS["fail"]+= (0 if ok else 1)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{('  '+extra) if extra else ''}")
    return ok

# ============================================================================= A. SYMBOLIC
print("="*78)
print("A. SYMBOLIC identity  gap_i = D_CM + D_UM_i + E_pi(barm - m_i)   (sympy)")
print("="*78)
import sympy as sp
def symbolic_identity(nW, nO):
    pi  = sp.symbols(f'pi0:{nW}', real=True)
    P   = [[sp.symbols(f'P_{w}_{v}', real=True) for v in range(nW)] for w in range(nW)]
    O   = [[sp.symbols(f'O{j}_{w}', real=True) for w in range(nW)] for j in range(nO)]
    al  = [[sp.symbols(f'a{j}_{w}', real=True) for w in range(nW)] for j in range(nO)]
    m   = [[sum(P[w][v]*O[j][v] for v in range(nW)) for w in range(nW)] for j in range(nO)]
    hatS= [sum(al[j][w]*O[j][w] for j in range(nO)) for w in range(nW)]
    barm= [sum(al[j][w]*m[j][w] for j in range(nO)) for w in range(nW)]
    Ep  = lambda X: sum(pi[w]*X[w] for w in range(nW))
    D_CM= sum(pi[w]*sum(al[j][w]*(O[j][w]-m[j][w]) for j in range(nO)) for w in range(nW))
    worst = True
    for i in range(nO):
        D_UM = Ep(m[i]) - Ep(O[i])
        soft = sum(pi[w]*(barm[w]-m[i][w]) for w in range(nW))
        gap  = Ep(hatS) - Ep(O[i])
        worst &= (sp.expand(gap - (D_CM + D_UM + soft)) == 0)
    return worst
for (nW,nO) in [(2,2),(3,2),(3,3),(2,3),(4,3)]:
    check(f"identity holds for ALL frames of shape (worlds={nW}, options={nO})",
          symbolic_identity(nW,nO))
print("  -> the decomposition is pure linearity; no frame assumption used.")

# ============================================================================= B. softmax bound
print("="*78)
print("B. softmax/Gibbs bound   barm = L - delta*H(alpha) >= max_j m_j - delta*log k")
print("="*78)
def softmax_check(rng, trials=20000):
    worst_id, worst_lb = 0.0, 0.0
    for _ in range(trials):
        k = rng.randint(2,6); delta = rng.uniform(1e-3, 2.0)
        m = [rng.uniform(0,1) for _ in range(k)]
        shift = max(m)                                   # stable softmax / log-sum-exp
        Z = sum(math.exp((mj-shift)/delta) for mj in m)
        al = [math.exp((mj-shift)/delta)/Z for mj in m]
        barm = sum(a*mj for a,mj in zip(al,m))
        L = shift + delta*math.log(Z)
        H = -sum(a*math.log(a) for a in al if a>0)
        worst_id = max(worst_id, abs(barm - (L - delta*H)))           # Gibbs identity
        worst_lb = max(worst_lb, (max(m) - delta*math.log(k)) - barm) # lower-bound violation
    return worst_id, worst_lb
wid, wlb = softmax_check(random.Random(0))
check("Gibbs identity  barm == L - delta*H   (max abs err over 20000 trials)", wid < 1e-9,
      f"max|err|={wid:.2e}")
check("lower bound  barm >= max_j m_j - delta*log k   (worst violation)", wlb <= 1e-12,
      f"worst (lb-barm)={wlb:.2e}")

# ============================================================================= C. DDB figures
print("="*78)
print("C. DDB Fig 2 (anti-expert) and Fig 3 -- exact, incl. the sec.4 trap")
print("="*78)
def half(*xs): return [F(x) for x in xs]
# bet menu used throughout DDB:  O_a pays +1 at a / -1 at b ;  O_b the reverse
O_a, O_b = half(1,-1), half(-1,1)
menu = [O_a, O_b]

print("Fig 2  anti-expert:  pi=(1/2,1/2),  P_a=(.2,.8), P_b=(.8,.2)")
pi2   = half(F(1,2),F(1,2))
P2    = [half(F(1,5),F(4,5)), half(F(4,5),F(1,5))]
gaps2 = value_gaps(pi2,P2,menu)
stat2 = [Epi(pi2,[P2[w][v] for w in range(2)]) for v in range(2)]     # pi @ P  (column sums)
sel2  = hard_select(P2,menu); alpha2 = [[F(1) if sel2[w]==j else F(0) for w in range(2)] for j in range(2)]
dec2  = defects(pi2,P2,menu,alpha2)
check("Value FAILS (some gap < 0)", min(gaps2) < 0, f"gaps={gaps2}")
check("stationary: pi@P == pi (unconditional martingale on these bets)", stat2==pi2,
      f"pi@P={stat2}")
check("BUT conditional martingale FAILS (NOT cond-martingale frame)",
      not is_cond_martingale(pi2,P2))
# the trap, quantified, for option O_a:
da = next(d for d in dec2 if d['i']==0)
check("sec.4 trap: gap = D_CM + D_UM + soft  with  D_UM==0  and  D_CM<0",
      da['gap']==da['rhs'] and da['D_UM']==0 and da['D_CM']<0,
      f"gap={da['gap']}, D_CM={da['D_CM']}, D_UM={da['D_UM']}, soft={da['soft']}")

print("Fig 3  valued modest:  pi=(1/2,1/2),  P_a=(.9,.1), P_b=(.2,.8)")
pi3 = half(F(1,2),F(1,2))
P3  = [half(F(9,10),F(1,10)), half(F(1,5),F(4,5))]
gaps3 = value_gaps(pi3,P3,menu)
stat3 = [Epi(pi3,[P3[w][v] for w in range(2)]) for v in range(2)]
check("Value HOLDS (all gaps >= 0)", min(gaps3) >= 0, f"gaps={gaps3}")
check("yet NOT stationary (unconditional martingale fails)", stat3 != pi3, f"pi@P={stat3}")
check("and NOT conditional martingale (generic valued modest frame)",
      not is_cond_martingale(pi3,P3))
print("  -> together: unconditional martingale is neither necessary (Fig3) nor")
print("     sufficient (Fig2) for Value; the CONDITIONAL one is what tracks it.")

# ============================================================================= D. CM => Value
print("="*78)
print("D. EXACT:  conditional martingale  =>  Value   (random partitional/prior frames)")
print("="*78)
def random_prior_frame(rng, nW, ncells):
    cells = [[] for _ in range(ncells)]
    for w in range(nW): cells[rng.randrange(ncells)].append(w)
    cells = [c for c in cells if c]                       # drop empties
    pi = rand_dist(nW, rng)
    P  = [None]*nW
    for c in cells:
        mass = sum(pi[v] for v in c)
        cond = [(pi[v]/mass if v in c else F(0)) for v in range(nW)]
        for w in c: P[w] = cond                            # P_w = pi(.|cell)
    return pi, P
rng = random.Random(1); bad=0; checked=0
for _ in range(3000):
    nW = rng.randint(2,6)
    pi,P = random_prior_frame(rng, nW, rng.randint(1,nW))
    if not is_cond_martingale(pi,P):   # sanity: prior frames must be CM
        bad+=1; continue
    menu_r = [rand_vec(nW,rng) for _ in range(rng.randint(2,4))]
    gaps = value_gaps(pi,P,menu_r)
    # decomposition with hard weights: D_CM and D_UM must be exactly 0 on a CM frame
    sel = hard_select(P,menu_r); al=[[F(1) if sel[w]==j else F(0) for w in range(nW)]
                                     for j in range(len(menu_r))]
    dec = defects(pi,P,menu_r,al)
    # 'bad' also catches any prior frame that fails to be cond-martingale (construction sanity)
    if (min(gaps) < 0) or any(d['D_CM']!=0 or d['D_UM']!=0 for d in dec): bad+=1
    checked+=1
check(f"CM frame => Value, with exact D_CM==0 and D_UM==0  ({checked} random frames)",
      bad==0, f"counterexamples={bad}")

# ============================================================================= E. collapse
print("="*78)
print("E. EXACT finite-collapse (sec 5.2):  cond. martingale (finite) => immodesty;")
print("   equivalently every MODEST finite frame breaks the conditional martingale.")
print("="*78)
def random_typed_frame(rng, nW, ntypes):
    """worlds drawn from a small set of expert 'types' so fibers can be nontrivial."""
    types = [rand_dist(nW, rng) for _ in range(ntypes)]
    P = [types[rng.randrange(ntypes)] for _ in range(nW)]
    pi = rand_dist(nW, rng)
    return pi, P
rng = random.Random(2)
ce_cm_modest = 0   # frames that are CM but modest  (must be 0)
n_cm=n_modest=n_imm=trials=0
for _ in range(20000):
    nW = rng.randint(2,5)
    pi,P = random_typed_frame(rng, nW, rng.randint(1,nW))
    cm  = is_cond_martingale(pi,P); im = is_immodest(pi,P)
    trials+=1; n_cm+=cm; n_imm+=im; n_modest += (not im)
    if cm and not im: ce_cm_modest += 1
check(f"NO finite frame is both conditional-martingale AND modest  ({trials} frames)",
      ce_cm_modest==0, f"counterexamples={ce_cm_modest}; saw {n_cm} CM, {n_modest} modest")
# explicit modest witness must break CM:
pim, Pm = half(F(1,2),F(1,2)), [half(F(7,10),F(3,10)), half(F(3,10),F(7,10))]  # leaks across fibers
check("explicit modest 2-world frame is NOT conditional-martingale",
      (not is_cond_martingale(pim,Pm)) and (not is_immodest(pim,Pm)))

# ============================================================================= F. LI regime
print("="*78)
print("F. LI regime in miniature:  modest, NEAR-cond-martingale frame, soft selection")
print("   -> Value holds up to predicted error  |D_CM| + |D_UM| + delta*log k,")
print("      and error -> 0 as (perturbation, delta) -> 0.")
print("="*78)
def perturb_toward_modest(pi, P, eps):
    """move each P_w a little toward the uniform mix of all P_v -> introduces modesty
       and a small conditional-martingale defect, like an LI future-self."""
    nW=len(P); avg=[sum(P[v][u] for v in range(nW))/nW for u in range(nW)]
    return [[(1-eps)*P[w][u] + eps*avg[u] for u in range(nW)] for w in range(nW)]
def softmax_weights(P, menu, delta):
    nW=len(P); al=[[0.0]*nW for _ in menu]
    for w in range(nW):
        ms=[float(Eexp(P,w,O)) for O in menu]
        shift=max(ms)                                    # stable softmax
        Z=sum(math.exp((mj-shift)/delta) for mj in ms)
        for j in range(len(menu)): al[j][w]=math.exp((ms[j]-shift)/delta)/Z
    return al
rng=random.Random(3)
print(f"  {'eps':>6} {'delta':>7} | {'min gap':>10} {'-(|DCM|+|DUM|+dlogk)':>22}  bound_ok")
worst_bound_ok=True
for eps in [F(1,3), F(1,10), F(1,50)]:
    for delta in [0.5, 0.1, 0.02]:
        # build a random prior (immodest, CM) then perturb to modest near-CM
        pi,P0 = random_prior_frame(rng, 4, 2)
        P = perturb_toward_modest(pi,P0,eps)
        modest = not is_immodest(pi,P)
        menu_r=[rand_vec(4,rng) for _ in range(3)]
        # float evaluation of gap and defects with soft weights
        alf = softmax_weights(P, menu_r, delta)
        m=[[float(Eexp(P,w,O)) for w in range(4)] for O in menu_r]
        hatS=[sum(alf[j][w]*float(menu_r[j][w]) for j in range(len(menu_r))) for w in range(4)]
        pif=[float(x) for x in pi]
        Epf=lambda X: sum(pif[w]*X[w] for w in range(4))
        gaps=[Epf(hatS)-Epf([float(menu_r[i][w]) for w in range(4)]) for i in range(len(menu_r))]
        D_CM=sum(pif[w]*sum(alf[j][w]*(float(menu_r[j][w])-m[j][w]) for j in range(len(menu_r)))
                 for w in range(4))
        D_UM=[Epf(m[i])-Epf([float(menu_r[i][w]) for w in range(4)]) for i in range(len(menu_r))]
        dlogk=delta*math.log(len(menu_r))
        # predicted lower bound on each gap:  gap_i >= D_CM + D_UM_i - dlogk
        bound_ok = all(gaps[i] >= D_CM + D_UM[i] - dlogk - 1e-9 for i in range(len(menu_r)))
        worst_bound_ok &= bound_ok
        err = -(abs(D_CM)+max(abs(d) for d in D_UM)+dlogk)
        print(f"  {str(eps):>6} {delta:>7.3f} | {min(gaps):>10.4f} {err:>22.4f}  {bound_ok}"
              + ("  (modest)" if modest else "  (immodest!)"))
check("predicted error bound  gap_i >= D_CM + D_UM_i - delta*log k  holds in every row",
      worst_bound_ok)
print("  -> as eps,delta shrink (the LI limit), all three error terms shrink and gap -> >=0.")

# ============================================================================= summary
print("="*78)
print(f"SUMMARY:  {PASS['n']-PASS['fail']}/{PASS['n']} checks passed"
      + ("" if PASS['fail']==0 else f"   ({PASS['fail']} FAILED)"))
print("="*78)
print("Checked: the proof's algebra (A, symbolic, all frames), the softmax bound (B),")
print("the discriminating examples + sec.4 trap (C), CM=>Value (D), the finite-collapse")
print("proposition (E), and the LI-regime error bound (F).")
print("NOT checked: that the LI theorems thm:ccee/thm:cee actually drive D_CM,D_UM -> 0")
print("and the ~_n bookkeeping -- that needs the Logical Induction framework formalized.")
import sys; sys.exit(1 if PASS['fail'] else 0)
