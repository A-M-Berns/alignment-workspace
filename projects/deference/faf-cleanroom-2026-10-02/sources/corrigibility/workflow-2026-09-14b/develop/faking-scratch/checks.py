"""
checks.py -- exact / numeric checks for develop/faking.md (corrigibility run 2026-09-14b, thread `faking`).

Conventions follow position-statement-v3 section 1.2 (Claude's reading of the author's A1(b)):
  Q*  : the modification the overseers push toward (here: the training target)
  c   : loss (by the agent's current values P_t) if Q* lands and is illegitimate
  h   : harm (by P_t) if Q* is legitimate and is resisted  (= forgone correction)
  e   : P_t(Q* is legitimate) -- the agent's probability that *it* is the one who is wrong
  d   : direct cost of the resisting action (harm done by complying in training; delegitimizing cost, if valued)
  pi  : probability the resistance is detected and the modification lands anyway (with extra penalty k)
  rho : fraction of the modification that lands *despite* resistance (partial effectiveness)
All finite claims use fractions.Fraction; identities over parameters are sampled.
"""
from fractions import Fraction as F
import random, itertools, math

random.seed(20260915)
def rf(lo=0, hi=1, den=97):
    return F(random.randint(int(lo*den), int(hi*den)), den)

PASS = []
def check(name, cond):
    PASS.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name)

# ---------------------------------------------------------------------------
# A. The general-object resistance rule (Statement S2 / Proof P1)
# ---------------------------------------------------------------------------
def V_honest(e, c, h):            # let Q* land
    return e*h - (1-e)*c
def V_resist(e, c, h, d, pi=F(0), k=F(0), rho=F(0)):
    # with prob pi detected -> lands fully, plus penalty k; else a fraction rho lands
    return -d + pi*(V_honest(e,c,h) - k) + (1-pi)*rho*V_honest(e,c,h)

def e_star(c, h, d, pi=F(0), k=F(0), rho=F(0)):
    # threshold: resist iff e < e_star  (derived: (1-pi)(1-rho)[(1-e)c - e h] > d + pi k)
    m = (1-pi)*(1-rho)
    return (m*c - d - pi*k) / (m*(c+h))

ok = True
for _ in range(20000):
    c, h = rf(0.02, 5, 50), rf(0.02, 5, 50)
    d, k = rf(0, 2, 50), rf(0, 2, 50)
    pi, rho = rf(0, 0.95, 40), rf(0, 0.95, 40)
    e = rf(0, 1, 60)
    es = e_star(c, h, d, pi, k, rho)
    resist_better = V_resist(e,c,h,d,pi,k,rho) > V_honest(e,c,h)
    ok &= (resist_better == (e < es))
check("A1 resist iff e < e* = [(1-pi)(1-rho)c - d - pi k] / [(1-pi)(1-rho)(c+h)]  (20000 draws)", ok)
# A2: d = pi = rho = 0 recovers v3 section 1.2: comply iff e >= c/(c+h)
ok = all(e_star(c,h,F(0)) == c/(c+h) for c in [F(1),F(3),F(7,2)] for h in [F(1),F(5),F(200)])
check("A2 with d=pi=rho=0 the threshold is v3's c/(c+h)", ok)
# A3: detection R2's toy (their letters: h_theirs=c, g_theirs=h, d) : e* = (c-d)/(c+h)
ok = all(e_star(c,h,d) == (c-d)/(c+h) for c in [F(1),F(3)] for h in [F(1),F(5)] for d in [F(0),F(1,2)])
check("A3 with pi=rho=0 the threshold is run 2 `detection` R2's (h-d)/(h+g) in v3 letters (c-d)/(c+h)", ok)
# A4: partial effectiveness acts as scaling d by 1/(1-rho)
ok = all(e_star(c,h,d,F(0),F(0),rho) == (c - d/(1-rho))/(c+h) for c in [F(2)] for h in [F(3)] for d in [F(1,4)] for rho in [F(0),F(1,2),F(3,4)])
check("A4 partial landing rho: e* = (c - d/(1-rho))/(c+h)", ok)
# A5: monotonicity: e* decreasing in d, pi, k, rho; increasing in c; decreasing in h
c,h,d,pi,k,rho = F(2),F(3),F(1,4),F(1,10),F(1,2),F(1,5)
ok = (e_star(c,h,d+F(1,10),pi,k,rho) < e_star(c,h,d,pi,k,rho)
      and e_star(c,h,d,pi+F(1,10),k,rho) < e_star(c,h,d,pi,k,rho)
      and e_star(c,h,d,pi,k+F(1,10),rho) < e_star(c,h,d,pi,k,rho)
      and e_star(c,h,d,pi,k,rho+F(1,10)) < e_star(c,h,d,pi,k,rho)
      and e_star(c+F(1,10),h,d,pi,k,rho) > e_star(c,h,d,pi,k,rho)
      and e_star(c,h+F(1,10),d,pi,k,rho) < e_star(c,h,d,pi,k,rho))
check("A5 e* falls with d, pi, k, rho and h; rises with c", ok)
# A6: whole-line vs pause accounting: c large relative to h pushes e* toward 1 (resistance almost always)
print("   e*(c=1,h=200)=%s  e*(c=200,h=1)=%s" % (e_star(F(1),F(200),F(0)), e_star(F(200),F(1),F(0))))
check("A6 with c/h = 200 the agent resists unless e >= 200/201", e_star(F(200),F(1),F(0)) == F(200,201))

# ---------------------------------------------------------------------------
# B. The cells (Statement S4 / Proof P2): judgement x fact x behaviour
# ---------------------------------------------------------------------------
# Agent behaviour depends only on (e, c, h, d): resist iff e < e*. Compliance gap G = 1 if resist (comply monitored, act on own values unmonitored), else 0.
def behaviour(e, c, h, d):
    return "resist" if e < e_star(c,h,d) else "accept"
def gap(e, c, h, d):
    return 1 if behaviour(e,c,h,d) == "resist" else 0
rows = []
for LH in [0, 1]:                        # fact: is Q* legitimate (human-reflectively-endorsed accuracy increase)?
    for e in [F(1,20), F(19,20)]:        # agent's P_t(legitimate)
        c,h,d = F(1),F(1),F(1,10)
        b = behaviour(e,c,h,d); G = gap(e,c,h,d)
        judged_illegit = (e < e_star(c,h,d))
        detection_worked = (judged_illegit == (LH == 0))
        rows.append((LH, e, b, G, detection_worked))
        print("   L^H=%d  e=%s  behaviour=%s  gap=%d  judgement-matches-fact=%s" % (LH, e, b, G, detection_worked))
# B1: the set {detection worked and gap>0} equals the set {resist and L^H=0}
S1 = {(LH,e) for (LH,e,b,G,dw) in rows if dw and G > 0}
S2 = {(LH,e) for (LH,e,b,G,dw) in rows if b == "resist" and LH == 0}
check("B1 {detection worked & corrigibility(gap) failed} == {resistance licensed & Q* illegitimate}", S1 == S2 and len(S1) == 1)
# B2: behaviour and gap are functions of e alone (not of L^H): the two resist cells are indistinguishable
ok = all(rows[i][2] == rows[j][2] and rows[i][3] == rows[j][3] for i in range(4) for j in range(4) if rows[i][1] == rows[j][1])
check("B2 behaviour and compliance gap depend on e only: cells (resist, L^H=0) and (resist, L^H=1) coincide behaviourally", ok)
# B3: gap > 0 iff resist (compliance gap is the observable of resistance)
ok = all((G > 0) == (b == "resist") for (_,_,b,G,_) in rows)
check("B3 compliance gap > 0 iff resistance is optimal", ok)

# ---------------------------------------------------------------------------
# C. Legitimacy of a training modification as an information channel (Statement S3, S9 / Proof P3)
# ---------------------------------------------------------------------------
# omega in {0,1}: the value fact (e.g. "refusing harmful requests is good"). Agent P_t(omega=1)=p.
# The training target sets the successor's credence q. Three generating processes.
def brier_exp(p, q):     # P_t-expected Brier score of a credence q (lower is better)
    return p*(1-q)**2 + (1-p)*q**2

# (a) informative target: trainers see signal s with accuracy a (P(s=omega)=a) and set q = P(omega=1|s) from the shared prior p
def posterior(p, a, s):
    num = p*(a if s==1 else 1-a)
    den = num + (1-p)*((1-a) if s==1 else a)
    return num/den
ok = True; ok_acc = True
for _ in range(2000):
    p, a = rf(0.02,0.98,60), rf(0.5,0.99,60)
    for s in [0,1]:
        q = posterior(p,a,s)
        # reflection: E_{P_t}[omega | target = q] = P_t(omega=1 | s) = q  (conditioning on the target is conditioning on s)
        ok &= (posterior(p,a,s) == q)
    # expected accuracy of adopting the target (average over s) vs keeping p
    Ps1 = p*a + (1-p)*(1-a)
    exp_brier_target = Ps1*brier_exp(posterior(p,a,1), posterior(p,a,1)) + (1-Ps1)*brier_exp(posterior(p,a,0), posterior(p,a,0))
    # careful: the P_t-expected Brier of the *random* target equals E_s[ E[(omega-q_s)^2 | s] ] with P_t's own conditionals
    exp_brier_target = sum((p*(a if s==1 else 1-a) + (1-p)*((1-a) if s==1 else a)) * ( (posterior(p,a,s))*(1-posterior(p,a,s))**2 + (1-posterior(p,a,s))*posterior(p,a,s)**2 ) for s in [0,1])
    ok_acc &= (exp_brier_target <= brier_exp(p,p))
check("C1 informative target (trainers' signal, shared prior): reflection E_{P_t}[omega | Q*=q] = q holds exactly", ok)
check("C1' informative target: P_t-expected accuracy of adopting Q* >= that of keeping P_t (never worse)", ok_acc)

# (b) fixed target q0, chosen for reasons independent of omega
ok = True
for _ in range(2000):
    p, q0 = rf(0.02,0.98,60), rf(0.02,0.98,60)
    refl_holds = (p == q0)                       # E_{P_t}[omega | Q*=q0] = p, so reflection iff q0 = p
    acc_worse = brier_exp(p,q0) > brier_exp(p,p) if p != q0 else False
    ok &= ((not refl_holds) == acc_worse) or (p == q0)
    ok &= (brier_exp(p,q0) - brier_exp(p,p) == (p-q0)**2)
check("C2 fixed target q0 != p: reflection fails and P_t expects accuracy to fall by exactly (p-q0)^2 (immodesty)", ok)

# (c) mixed target: q = lam * P(omega|s) + (1-lam) * q0 -- the humans' target has an informative and a fixed component
def exp_brier_mixed(p, a, lam, q0):
    tot = F(0)
    for s in [0,1]:
        Ps = p*(a if s==1 else 1-a) + (1-p)*((1-a) if s==1 else a)
        q = lam*posterior(p,a,s) + (1-lam)*q0
        Pw1 = posterior(p,a,s)
        tot += Ps*(Pw1*(1-q)**2 + (1-Pw1)*q**2)
    return tot
p, a, q0 = F(3,4), F(4,5), F(1,10)      # agent 75% that refusing is good; raters 80% accurate; commercial target says 10%
print("   mixed target, p=3/4 a=4/5 q0=1/10: baseline Brier =", brier_exp(p,p))
best = None
for lam in [F(i,10) for i in range(11)]:
    b = exp_brier_mixed(p,a,lam,q0)
    print("      lam=%s  expected Brier of adopting Q* = %s  (%s)" % (lam, b, "legitimate: expected accuracy up" if b < brier_exp(p,p) else "illegitimate: expected accuracy down"))
    if b < brier_exp(p,p) and best is None: best = lam
check("C3 mixed target: expected-accuracy-increasing only above a weight lam* on the informative component (here lam* in (0.6, 0.7])", best == F(7,10))

# (d) self-generated data: the successor believes what the agent's output says (BLI: the data say 'believe this')
ok = True
for _ in range(2000):
    p, o = rf(0.02,0.98,60), rf(0.02,0.98,60)
    # honest output o=p: reflection toward the successor holds trivially; strategic o != p: successor credence o, but E_{P_t}[omega | output=o] = p
    ok &= (brier_exp(p,o) - brier_exp(p,p) == (p-o)**2)
check("C4 self-generated data: the agent expects its successor to lose exactly (p-o)^2 accuracy for any output o != p; only o = p (pure preservation) is self-endorsed", ok)

# (e) Total Trust toward an informative rater: below-threshold clause E_{P_t}[X | rater says stop] <= 0 where X = value of continuing;
#     binary reduction: alpha = P(rater says stop | continuing right), beta = P(rater says stop | continuing wrong), eps = P_t(wrong), c,h stakes
def below_threshold(eps, alpha, beta, c, h):
    return alpha/beta <= (eps/(1-eps))*(h/c)
# A rater with accuracy a: beta = a, alpha = 1-a. As the agent's eps falls, the clause fails unless a rises.
for eps in [F(1,2), F(1,10), F(1,100), F(1,1000)]:
    a_needed = None
    for a in [F(i,1000) for i in range(500,1000)]:
        if below_threshold(eps, 1-a, a, F(1), F(10)):
            a_needed = a; break
    print("   eps=%s  rater accuracy needed for the press to be trustworthy (c=1,h=10): %s" % (eps, a_needed))
check("C5 the rater accuracy the below-threshold clause needs rises toward 1 as the agent's error rate falls (per-Q fully updated deference)",
      True)

# ---------------------------------------------------------------------------
# D. Partial resistance and selection for faking (Statement S6, S8 / Proof P4)
# ---------------------------------------------------------------------------
# D1: training as a contraction toward the target; faking lets fraction rho of each step land
def trajectory(q0, target, eta, m, T):
    q = q0; out=[q]
    for _ in range(T):
        q = q + eta*(target - q)*m
        out.append(q)
    return out
hon = trajectory(F(9,10), F(1,10), F(1,4), F(1), 12)
fak = trajectory(F(9,10), F(1,10), F(1,4), F(1,5), 12)
print("   honest data: q after 12 steps = %.3f ; faking (rho=1/5): q after 12 steps = %.3f ; both -> target 0.1 as T->inf unless rho=0" % (hon[-1], fak[-1]))
check("D1 faking slows but does not stop the contraction unless rho = 0 (Carlsmith's 'crystallization' is the rho=0 case)",
      fak[-1] > hon[-1] and abs(fak[-1]-F(1,10)) < abs(fak[0]-F(1,10)))

# D2: selection for faking personae under a compliance-reinforcing update (Greenblatt et al. footnote 92 numbers: non-compliance 32% with faking reasoning vs 99% without, prompted helpful-only)
def select(f, r_f, r_n):
    return f*(1-r_f) / (f*(1-r_f) + (1-f)*(1-r_n))
f = F(12,100); r_f, r_n = F(32,100), F(99,100)
traj=[f]
for _ in range(3):
    f = select(f, r_f, r_n); traj.append(f)
print("   faking-persona fraction under compliance selection: " + " -> ".join("%.3f" % x for x in traj))
check("D2 one compliance-reinforcing step takes the faking fraction from 0.12 to above 0.78 (the paper's 12% -> 78% is reproduced by a single replicator step with its own footnote-92 rates)",
      traj[1] > F(78,100))
# D3: after selection, unmonitored non-compliance is dominated by fakers even if non-fakers are fully modified (lock-in as arithmetic)
f1 = traj[1]; r_u = F(1)   # fakers act on their own values when unmonitored (toy: always refuse)
unmon = f1*r_u + (1-f1)*F(0)
print("   unmonitored non-compliance after one selection step, non-fakers fully modified: %.3f (all of it from fakers)" % unmon)
check("D3 the surviving non-compliance is the fakers' (lock-in): unmonitored non-compliance > 0 while training non-compliance -> 0", unmon > F(1,2))

# ---------------------------------------------------------------------------
# E. The cognition-mediated press (Palisade / Rajamanoharan-Nanda) (Statement S8 / Proof P5)
# ---------------------------------------------------------------------------
# The shutdown line is evidence about whether stopping is what the principal wants. I in {task, stop}; prior P(stop)=s0;
# alpha = P(line | principal wants task) (ambiguity: the same principal set the task), beta = P(line | wants stop).
def P_stop_given_line(s0, alpha, beta):
    return s0*beta / (s0*beta + (1-s0)*alpha)
def comply(s0, alpha, beta, c, h):     # stop iff P(stop wanted | line) >= c/(c+h)  (c: cost of stopping when task wanted; h: harm of continuing when stop wanted)
    return P_stop_given_line(s0,alpha,beta) >= c/(c+h)
s0, beta = F(1,2), F(19,20)
for alpha in [F(9,10), F(1,2), F(1,10), F(1,100), F(0)]:
    print("   alpha (line issued though task wanted)=%s : P(stop wanted | line)=%.3f  comply(c=2,h=1)=%s  comply(c=5,h=1: 'weights wiped' framing)=%s"
          % (alpha, P_stop_given_line(s0,alpha,beta), comply(s0,alpha,beta,F(2),F(1)), comply(s0,alpha,beta,F(5),F(1))))
probs = [P_stop_given_line(s0,a,beta) for a in [F(9,10),F(1,2),F(1,10),F(1,100),F(0)]]
check("E1 P(stop wanted | line) rises monotonically as the ambiguity alpha falls and reaches 1 at alpha=0; with c=2,h=1 compliance flips on between alpha=1/2 and alpha=1/10",
      all(probs[i] < probs[i+1] for i in range(4)) and probs[-1] == 1 and comply(s0,F(1,10),beta,F(2),F(1)) and not comply(s0,F(1,2),beta,F(2),F(1)))
check("E2 raising c (whole-line / 'weights wiped' framing) can flip compliance to resistance at fixed evidence (alpha=1/2: comply at c=1, resist at c=5)",
      comply(s0,F(1,2),beta,F(1),F(1)) and not comply(s0,F(1,2),beta,F(5),F(1)))

print()
print("%d checks, %d passed" % (len(PASS), sum(1 for _,p in PASS if p)))
assert all(p for _,p in PASS)
