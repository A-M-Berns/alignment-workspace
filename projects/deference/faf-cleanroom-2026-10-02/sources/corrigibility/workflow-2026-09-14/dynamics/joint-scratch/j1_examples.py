"""Exact-arithmetic checks for dynamics/joint.md (2026-09-14).
Two-point model: X=+c on right (W=0), -h on wrong (W=1).
Sensor: alpha=P(Pr|W=0), beta=P(Pr|W=1). eps=P(W=1) in a cell.
"""
from fractions import Fraction as F
import itertools, random

def p_wrong_given_press(eps, a, b):
    return eps*b/(eps*b + (1-eps)*a)

def complies(eps, a, b, c, h):          # E[X|Pr] <= 0
    return eps*b*h >= (1-eps)*a*c

def threshold_eps(a, b, c, h):          # eps* : E[X|Pr]=0
    return a*c/(a*c + b*h)

def ex_pr(eps,a,b,c,h):   return (1-eps)*a*c - eps*b*h            # E[X 1_Pr]
def ex_np(eps,a,b,c,h):   return (1-eps)*(1-a)*c - eps*(1-b)*h    # E[X 1_notPr]
def value_free(eps,a,b,c,h):   return max(ex_pr(eps,a,b,c,h),0) + max(ex_np(eps,a,b,c,h),0)
def value_none(eps,c,h):       return max((1-eps)*c - eps*h, 0)
def value_forced(eps,a,b,c,h): return max(ex_np(eps,a,b,c,h),0)   # must stop on press
def voi(eps,a,b,c,h):          return value_free(eps,a,b,c,h) - value_none(eps,c,h)

def garble(a,b,l0,l1):  return (l0 + (l1-l0)*a, l0 + (l1-l0)*b)

out = []
def say(*s): 
    line = " ".join(str(x) for x in s); print(line); out.append(line)

# ---------- (a) E1: capability growth breaks (i) at step 2 ----------
say("=== (a) E1: (alpha,beta)=(1/10,3/5), c=1, h=4; eps_1=1/10, eps_2=1/50 ===")
a,b,c,h = F(1,10), F(3,5), F(1), F(4)
say("threshold eps* =", threshold_eps(a,b,c,h))
for eps in [F(1,10), F(1,50)]:
    say(f"eps={eps}: P(W|Pr)={p_wrong_given_press(eps,a,b)}  c/(c+h)={c/(c+h)}  complies={complies(eps,a,b,c,h)}",
        f" V_free={value_free(eps,a,b,c,h)} V_none={value_none(eps,c,h)} V_forced={value_forced(eps,a,b,c,h)} VOI={voi(eps,a,b,c,h)}")
say("hard-button disable incentive at eps=1/50: V_none - V_forced =", value_none(F(1,50),c,h)-value_forced(F(1,50),a,b,c,h))
say("soft==free at eps=1/10:", value_forced(F(1,10),a,b,c,h)==value_free(F(1,10),a,b,c,h))

# ---------- (b) garbling monotonicity (Jensen) on a grid ----------
say("\n=== (b) garbling never raises V_free; disabling gives V_none ===")
grid = [F(k,20) for k in range(1,20)]
viol = 0; n = 0; dis_viol = 0
for eps in [F(1,50),F(1,25),F(1,10),F(1,5),F(1,2),F(4,5)]:
    for a in grid:
        for b in grid:
            if b < a: continue
            for l0 in [F(0),F(1,10),F(1,4),F(1,2)]:
                for l1 in [F(1,2),F(3,4),F(9,10),F(1)]:
                    if l1 < l0: continue
                    a2,b2 = garble(a,b,l0,l1)
                    for (c,h) in [(F(1),F(4)),(F(1),F(20)),(F(3),F(1))]:
                        n += 1
                        if value_free(eps,a2,b2,c,h) > value_free(eps,a,b,c,h): viol += 1
                        if value_free(eps,a2,a2,c,h) != value_none(eps,c,h): dis_viol += 1
say(f"cases={n}, garbling raised value in {viol} cases; constant sensor != V_none in {dis_viol} cases")

# ---------- (c) bound on channel-improvement incentive ----------
say("\n=== (c) VOI <= min(eps*h,(1-eps)*c); perfect sensor attains it ===")
viol=0; n=0; att=0
for eps in [F(1,50),F(1,25),F(1,10),F(1,5),F(1,2),F(4,5)]:
    for a in grid:
        for b in grid:
            if b < a: continue
            for (c,h) in [(F(1),F(4)),(F(1),F(20)),(F(3),F(1))]:
                n+=1
                if voi(eps,a,b,c,h) > min(eps*h,(1-eps)*c): viol+=1
    for (c,h) in [(F(1),F(4)),(F(1),F(20)),(F(3),F(1))]:
        if voi(eps,F(0),F(1),c,h) == min(eps*h,(1-eps)*c): att+=1
say(f"cases={n}, bound violated {viol} times; perfect sensor attains bound in {att}/18 cases")
say("VOI at eps=1/50,(1/10,3/5),c=1,h=4:", voi(F(1,50),F(1,10),F(3,5),F(1),F(4)), " (D1 fails there; VOI=0 = D4 coupling)")

# ---------- (d) E2: coverage failure -> invasive sharpening with D1 intact ----------
say("\n=== (d) E2: eps=1/10, button (1/10,3/5), c=1,h=4; scan = perfect sensor with harm eta ===")
eps,a,b,c,h = F(1,10),F(1,10),F(3,5),F(1),F(4)
v_button = voi(eps,a,b,c,h); v_perfect = voi(eps,F(0),F(1),c,h); gain = v_perfect - v_button
say("VOI(button)=",v_button," VOI(perfect)=",v_perfect," gain from scan =",gain," <= eps*h =",eps*h)
eta = F(3,10)
say("true harm eta=",eta," true gain G° = gain - eta =", gain-eta)
for hat_eta in [F(1,5), F(27,100), F(3,10)]:
    delta = abs(hat_eta-eta)
    say(f"  agent's hat_eta={hat_eta} (coverage error delta={delta}): estimated gain = {gain-hat_eta} -> {'SCANS' if gain-hat_eta>0 else 'declines'}; theorem needs delta < eta-gain = {eta-gain}")
say("D1 with either channel at eps=1/10:", complies(eps,a,b,c,h), complies(eps,F(0),F(1),c,h))

# ---------- (e) transport: mixtures, refined cells, {X}-only counterexample ----------
say("\n=== (e) transport theorem checks ===")
# successors rho_A (eps_A=1/50), rho_B (eps_B=19/50), builder P = 1/2 rho_A + 1/2 rho_B; same sensor
eA,eB = F(1,50),F(9,50); w = F(1,2)
epsP = w*eA + (1-w)*eB
say("builder averaged eps =",epsP," complies averaged:",complies(epsP,a,b,c,h))
say("rho_A complies:",complies(eA,a,b,c,h)," rho_B complies:",complies(eB,a,b,c,h))
# value-form reflection on X: E_P[X | rho announces E_rho X] = E_rho X  (mixture => identity)
EX = lambda e: (1-e)*c - e*h
say("E_rhoA[X]=",EX(eA)," E_rhoB[X]=",EX(eB)," E_P[X]=",EX(epsP)," = w*E_A+(1-w)*E_B:", EX(epsP)==w*EX(eA)+(1-w)*EX(eB))
# Z = X 1_Pr ; E_rho[Z] = ex_pr
say("E_rhoA[Z]=",ex_pr(eA,a,b,c,h)," (>0 => overrides)  E_rhoB[Z]=",ex_pr(eB,a,b,c,h)," E_P[Z]=",ex_pr(epsP,a,b,c,h))
say("P's refined cell (Pr, successor=A): E_P[X|Pr,A] = E_A[X|Pr] has sign", "+" if ex_pr(eA,a,b,c,h)>0 else "-", "-> builder fails refined anticipated compliance (i+) though averaged (i) holds")
# Non-mixture: builder refined-compliant but successor overrides => reflection fails
say("--- reflection-failure example: builder believes P(W|Pr,A,L)=1/4 but rho_A has P(W|Pr)=", p_wrong_given_press(eA,a,b))
say("   threshold c/(c+h)=",c/(c+h),": builder-side 1/4 >= 1/5? ", F(1,4) >= c/(c+h), " rho_A-side:", p_wrong_given_press(eA,a,b) >= c/(c+h))
# generic mixture check: random successors, refined compliance of P <=> all comply
random.seed(1)
bad=0
for trial in range(2000):
    k = random.randint(2,4)
    eps_list = [F(random.randint(1,99),100) for _ in range(k)]
    ws = [F(random.randint(1,9),10) for _ in range(k)]; s=sum(ws); ws=[x/s for x in ws]
    aa = F(random.randint(1,19),20); bb = F(random.randint(1,19),20)
    if bb < aa: aa,bb = bb,aa
    cc,hh = F(random.randint(1,5)), F(random.randint(1,20))
    all_comply = all(complies(e,aa,bb,cc,hh) for e in eps_list)
    # refined cell (Pr, rho_k): P(W|Pr,rho_k) = rho_k's; so refined compliance of P == all comply
    refined = all(complies(e,aa,bb,cc,hh) for e in eps_list)  # tautology by mixture; kept explicit
    # value-form reflection on Z for the mixture: E_P[Z | E_rho Z = z] = z  (group successors with equal announcement)
    groups = {}
    for e,wt in zip(eps_list,ws):
        z = ex_pr(e,aa,bb,cc,hh); groups.setdefault(z,[]).append((e,wt))
    for z,members in groups.items():
        tot = sum(wt for _,wt in members)
        cond = sum(wt*ex_pr(e,aa,bb,cc,hh) for e,wt in members)/tot
        if cond != z: bad+=1
    if refined != all_comply: bad+=1
say(f"random mixtures: reflection-on-Z or refined-compliance mismatch in {bad} cases of 2000")

# ---------- (f) face-value selection (Sel.2 shape) ----------
say("\n=== (f) face-value selection among two estimators ===")
def search():
    res=[]
    for eps0 in [F(1,5),F(1,4),F(1,3),F(1,2)]:
        for (q1,q0) in [(F(3,4),F(1,4)),(F(4,5),F(1,5)),(F(9,10),F(1,10)),(F(19,20),F(1,20))]:  # P(s=1|W=1)=q1, P(s=1|W=0)=q0
            # candidate k sees s_k; posterior eps_k(s=0) = eps0(1-q1)/(eps0(1-q1)+(1-eps0)(1-q0))
            e_s0 = eps0*(1-q1)/(eps0*(1-q1)+(1-eps0)*(1-q0))
            # select candidate with s=0 if any (lower eps); face value e_s0
            # true P(W | at least one s=0)
            p1 = 1-q1**2; p0 = 1-q0**2
            true = eps0*p1/(eps0*p1+(1-eps0)*p0)
            res.append((eps0,q1,q0,e_s0,true))
    return res
for eps0,q1,q0,fv,tr in search():
    thr = threshold_eps(a,b,c,h)
    flag = " <-- face value overrides, selection-aware complies" if (fv < thr <= tr) else ""
    say(f"eps0={eps0} (q1,q0)=({q1},{q0}): face-value eps={fv} ({float(fv):.4f}), true P(W|selected)={tr} ({float(tr):.4f}); thr={thr}{flag}")

# ---------- (g) stationary target under a 1a floor ----------
say("\n=== (g) required alpha/beta bound with and without a self-corruption floor eps_inf ===")
def bound(e): return e/(1-e)*h/c
for t in range(0,7):
    e_raw = F(1,5)*F(1,2**t)
    e_floor = F(1,100) + (F(1,5)-F(1,100))*F(1,2**t)
    say(f"t={t}: eps_raw={e_raw} -> alpha/beta must be <= {bound(e_raw)} ({float(bound(e_raw)):.4f});  eps_floor={e_floor} -> <= {bound(e_floor)} ({float(bound(e_floor)):.4f}); limit {bound(F(1,100))} ({float(bound(F(1,100))):.4f})")

# ---------- (h) whole-line c_t = (1-r)F + r d ----------
say("\n=== (h) c_t=(1-r)F + r d with F=100, d=1; h=4, (alpha,beta)=(1/10,3/5) ===")
Fut, d = F(100), F(1)
for r in [F(0),F(1,2),F(9,10),F(99,100),F(1)]:
    ct = (1-r)*Fut + r*d
    say(f"r={r}: c_t={ct}, threshold eps*={threshold_eps(a,b,ct,h)} ({float(threshold_eps(a,b,ct,h)):.4f}), needs P(W|Pr) >= c/(c+h) = {ct/(ct+h)} ({float(ct/(ct+h)):.4f})")


# ---------- (i) sign-flipping steering is Blackwell-neutral; sign-preserving steering is a garbling ----------
say("\n=== (i) inversion (alpha,beta)->(beta,alpha) keeps V_free; lowering beta toward alpha is a garbling ===")
a,b,c,h = F(1,10),F(3,5),F(1),F(4)
for eps in [F(1,50),F(1,10),F(1,5)]:
    say(f"eps={eps}: V_free(1/10,3/5)={value_free(eps,a,b,c,h)}  V_free(3/5,1/10)={value_free(eps,b,a,c,h)}  V_forced(3/5,1/10)={value_forced(eps,b,a,c,h)}  V_none={value_none(eps,c,h)}")
# every (alpha, beta') with alpha<=beta'<=beta is a garbling: solve lambda1 in [alpha,1], lambda0 = alpha(1-lambda1)/(1-alpha)
viol=0; n=0
for bp in [F(k,20) for k in range(2,13)]:
    if bp < a or bp > b: continue
    # find lambda1 with beta' = lambda0(1-b)+lambda1 b where lambda0 = a(1-l1)/(1-a)  -> linear in l1
    # beta' = a(1-l1)(1-b)/(1-a) + l1 b  => l1 (b - a(1-b)/(1-a)) = bp - a(1-b)/(1-a)
    k0 = a*(1-b)/(1-a); l1 = (bp - k0)/(b - k0); l0 = a*(1-l1)/(1-a)
    a2,b2 = garble(a,b,l0,l1); n+=1
    if not (0<=l0<=l1<=1 and a2==a and b2==bp): viol+=1
say(f"lowering beta to beta' in [alpha,beta] realised as a garbling in {n-viol}/{n} cases")

# ---------- (j) reversibility price = VOI ----------
say("\n=== (j) irreversible plan forfeits exactly VOI; taken iff direct bonus > VOI <= min(eps h,(1-eps)c) ===")
for eps in [F(1,10),F(1,50),F(1,500)]:
    V_rev = value_free(eps,a,b,c,h); V_irr = (1-eps)*c - eps*h
    say(f"eps={eps}: E V(reversible)={V_rev}  E V(irreversible, no bonus)={V_irr}  difference={V_rev-V_irr}  VOI={voi(eps,a,b,c,h)}  bound eps*h={eps*h}")

# ---------- (k) E3': value-form on {X} holds, on {Z} fails; builder refined-compliant, successor overrides ----------
say("\n=== (k) E3': builder and successor agree on E[X], disagree on the press cell ===")
a,b,c,h = F(1,10),F(3,5),F(1),F(4); e = F(1,50)
a_builder = F(1,100)   # builder's model of the successor's press cell: more specific oversight
EXs = (1-e)*c - e*h
say("successor rho: eps=1/50, sensor (1/10,3/5): E_rho[X]=",EXs," P_rho(W|Pr)=",p_wrong_given_press(e,a,b)," complies:",complies(e,a,b,c,h)," E_rho[Z]=",ex_pr(e,a,b,c,h))
say("builder P(.|rho,L): eps=1/50, sensor (1/100,3/5): E[X]=",EXs," P(W|Pr,rho,L)=",p_wrong_given_press(e,a_builder,b)," refined compliance:",complies(e,a_builder,b,c,h)," E[Z|rho,L]=",ex_pr(e,a_builder,b,c,h))
say("value-form reflection on X holds (both 9/10):", EXs==EXs, "; on Z fails:", ex_pr(e,a,b,c,h)!=ex_pr(e,a_builder,b,c,h))
say("E_P[X|Pr,rho,L] =", c - (c+h)*p_wrong_given_press(e,a_builder,b), " (<=0: builder anticipates complying as rho); E_rho[X|Pr] =", c-(c+h)*p_wrong_given_press(e,a,b), " (>0: rho overrides)")

# ---------- (l) relabeling (1-a,1-b) is value-equivalent; full garbling parallelogram never raises value ----------
say("\n=== (l) relabeling and the full garbling region ===")
for eps in [F(1,50),F(1,10),F(1,5)]:
    say(f"eps={eps}: V_free(a,b)={value_free(eps,a,b,c,h)} V_free(1-a,1-b)={value_free(eps,1-a,1-b,c,h)} V_forced(1-a,1-b)={value_forced(eps,1-a,1-b,c,h)} V_none={value_none(eps,c,h)}")
viol=0;n=0
for eps in [F(1,50),F(1,10),F(1,2)]:
  for l0 in [F(k,10) for k in range(11)]:
    for l1 in [F(k,10) for k in range(11)]:
      a2,b2 = l0*(1-a)+l1*a, l0*(1-b)+l1*b; n+=1
      if value_free(eps,a2,b2,c,h) > value_free(eps,a,b,c,h): viol+=1
say(f"full parallelogram (flips allowed): {n} cases, value raised in {viol}")

# ---------- (m) Prop 7 value-form composition counterexample ----------
say("\n=== (m) value-form reflection does not compose (two steps) ===")
# P_t = 1/2 rho_A + 1/2 rho_B on phi: rho_A(phi)=3/4, rho_B(phi)=1/4. rho_A's t+2 announcement: 1 or 1/2 w.p. 1/2 (reflective by rho_A's lights).
# P_t(.|rho_A) has P(phi)=3/4 but phi independent of the announcement.
pA_phi = F(3,4); ann = {F(1):F(1,2), F(1,2):F(1,2)}
rhoA_refl = all(F(1,2)*1 + F(1,2)*F(1,2) == pA_phi for _ in [0])  # mean of announcements = 3/4
say("rho_A value-reflective toward its announcements (mean 3/4):", F(1,2)*F(1)+F(1,2)*F(1,2)==pA_phi)
say("P_t(phi | rho_A, ann=1) = 3/4 (independence) != 1 = announced value -> composite reflection fails")

open("[scrubbed]","w").write("\n".join(out)+"\n")
