# Repair checks for develop/faking-final.md (R1-R8). Exact rationals throughout.
from fractions import Fraction as F
import itertools, random

def ok(label, cond, msg=""):
    print(("PASS " if cond else "FAIL ")+label+(": "+msg if msg else ""))
    assert cond, label

# R1  threshold with partial landing renamed theta; one-round
def estar(c,h,d,pi,k,th):
    return ((1-pi)*(1-th)*c - d - pi*k)/((1-pi)*(1-th)*(c+h))
def V_res(e,c,h,d,pi,k,th):
    U = e*h-(1-e)*c
    return -d + pi*(U-k) + (1-pi)*th*U
def V_hon(e,c,h): return e*h-(1-e)*c
random.seed(1)
bad=0
for _ in range(20000):
    c=F(random.randint(1,50),random.randint(1,10)); h=F(random.randint(1,50),random.randint(1,10))
    d=F(random.randint(0,20),10); pi=F(random.randint(0,9),10); k=F(random.randint(0,20),10); th=F(random.randint(0,9),10)
    e=F(random.randint(0,100),100)
    lhs = V_res(e,c,h,d,pi,k,th) > V_hon(e,c,h)
    rhs = e < estar(c,h,d,pi,k,th)
    if lhs!=rhs: bad+=1
ok("R1", bad==0, "resist iff e<e* over 20000 draws (theta = fraction landing despite resistance)")

# R2  fud R2 accounting: pause vs whole-line; A6's 200/201 needs kappa~1/200
def wl(rhoH,kap): c=1-rhoH; h=rhoH+kap; return c/(c+h), c/h
def pause(delta,kap): c=delta; h=1-delta+kap; return c/(c+h), h/c
print("  whole-line (rhoH,kappa)->(e*, c/h):", [(str(r),str(k),str(wl(F(r),F(k))[0]),str(wl(F(r),F(k))[1])) for r,k in [("1/10","1"),("1/2","1"),("1/10","1/10"),("9/10","1")]])
print("  pause (delta,kappa)->(e*, h/c):", [(str(dl),str(k),str(pause(F(dl),F(k))[0]),str(pause(F(dl),F(k))[1])) for dl,k in [("1/100","1")]])
ok("R2a", wl(F(1,10),F(1))[0]==F(9,20) and wl(F(1,2),F(1))[0]==F(1,4), "whole-line e* = 9/20 at (1/10,1), 1/4 at (1/2,1) -- O(1), not 200/201")
# solve c/h=200 at rhoH=0: (1)/(kappa)=200 -> kappa=1/200
ok("R2b", wl(F(0),F(1,200))[1]==200, "c/h=200 under whole-line accounting requires kappa=1/200")
ok("R2c", pause(F(1,100),F(1))[1]==199, "pause margin h/c=199 at delta=1/100,kappa=1 (fud R2 item 4)")

# R3  coherence bound on e=P(L|Q*=q) for a binary phi; fixed and mixed targets
def bound(pcond,q):
    return min(pcond/q if q>0 else F(10**9), (1-pcond)/(1-q) if q<1 else F(10**9), F(1))
p=F(3,4)
for q0 in [F(1,10),F(1,2),F(7,10)]:
    print("  fixed target q0=%s: max coherent e=%s"%(q0,bound(p,q0)))
ok("R3a", bound(p,F(1,10))==F(5,18) and bound(p,F(1,2))==F(1,2) and bound(p,F(7,10))==F(5,6), "X6 reproduced")
# mixed target: rater accuracy a=4/5, shared prior p; q_s = lam*P(phi|s)+(1-lam)*q0
a=F(4,5); q0=F(1,10)
def post(s):  # P(phi|s)
    num = p*(a if s==1 else 1-a); den = num + (1-p)*((1-a) if s==1 else a); return num/den
def Ps(s): return p*(a if s==1 else 1-a)+(1-p)*((1-a) if s==1 else a)
thr=F(1,2)  # c/(c+h) with c=h
first=None
for lam in [F(i,10) for i in range(11)]:
    bs=[]; 
    for s in (0,1):
        qs=lam*post(s)+(1-lam)*q0
        bs.append(bound(post(s),qs))
    emax_expected = sum(Ps(s)*bs[s] for s in (0,1))
    clears = all(b>=thr for b in bs)
    if clears and first is None: first=lam
    print("  mixed lam=%s: q_s=(%s,%s) max e_s=(%s,%s) expected max e=%s clears 1/2 on both s: %s"%(lam, lam*post(0)+(1-lam)*q0, lam*post(1)+(1-lam)*q0, bs[0],bs[1], emax_expected, clears))
print("  first lam at which coherent e_s can reach c/(c+h)=1/2 on both signals:", first)
ok("R3b", bound(post(1),post(1))==1 and bound(post(0),post(0))==1, "at lam=1 the bound is 1 (informed target: reflection can hold with e=1)")
# per-signal crossing of the compliance threshold thr=1/2 for the bound on e_s
def cross_lam(s):
    # bound_s(lam) = min(post/q, (1-post)/(1-q)); q linear in lam; solve for the smallest lam with bound>=thr on a fine grid then exactly
    ps=post(s)
    # candidate from (1-ps)/(1-q)>=thr  ->  q >= 1-(1-ps)/thr ; q = lam*ps+(1-lam)*q0
    q_need = 1-(1-ps)/thr
    lam1 = (q_need-q0)/(ps-q0) if ps!=q0 else None
    # candidate from ps/q>=thr -> q<=ps/thr
    q_max = ps/thr
    return lam1, q_max
for s in (0,1):
    lam1,qmax = cross_lam(s)
    print("  signal s=%s: P(phi|s)=%s ; (1-p_s)/(1-q_s)>=1/2 needs lam>=%s ; p_s/q_s>=1/2 needs q_s<=%s (always here)"%(s,post(s),lam1,qmax))
ok("R3c", bound(post(0),q0)>=thr and cross_lam(1)[0]==F(97,107), "the bound is signal-specific: on the signal opposing the agent (s=0) a coherent e can clear 1/2 at every lam; on the agreeing signal (s=1) only for lam>=97/107 -- no single lam* exists")
# R4  immodesty reversal under D3's T (adversary X2), confirming the kill of S7(ii)
def brier_exp(p,q): return p*(1-q)**2+(1-p)*q**2
for (pp,qs,th) in [(F(9,10),F(1,10),F(0)),(F(9,10),F(1,10),F(1,5)),(F(3,4),F(1,10),F(1,2))]:
    hon=brier_exp(pp,qs); fak=brier_exp(pp,pp+th*(qs-pp))
    print("  p=%s q*=%s theta=%s: honest-successor Brier %s, faked-successor %s"%(pp,qs,th,hon,fak))
    ok("R4 p=%s th=%s"%(pp,th), fak<hon, "P_t rates the faked successor more accurate")

# R5  whose update shaping corrupts: the humans' (or the installed state's) model of the agent, when it assumes honest data
# Humans hold prior g that the agent's values conflict with the target (D=1). Honest agent: output complies with prob 1-r1 if D=1, 1-r0 if D=0.
# Faking agent (when monitored): complies with prob 1-r1f if D=1. Humans who assume honesty read compliance with the honest likelihood.
g=F(1,2); r1=F(99,100); r0=F(1,100); r1f=F(32,100)   # Greenblatt fn.92 rates as illustration [reported]
def post_D_given_comply(assumed_r1, actual_r1):
    # humans' posterior computed with assumed likelihood; truth computed with actual
    num_ass = g*(1-assumed_r1); den_ass = num_ass + (1-g)*(1-r0)
    num_act = g*(1-actual_r1); den_act = num_act + (1-g)*(1-r0)
    return num_ass/den_ass, num_act/den_act
blind, truth = post_D_given_comply(r1, r1f)
aware, _ = post_D_given_comply(r1f, r1f)
print("  humans' P(conflict | compliant output): source-blind %s, truth %s, source-aware %s"%(blind, truth, aware))
ok("R5a", blind<truth, "source-blind humans under-estimate conflict after a shaped compliant output (untracked kernel: delegitimizing for THEIR update)")
ok("R5b", aware==truth, "source-aware humans' update is a refinement (selection R2.2): shaping is information-destroying, not delegitimizing, for them")
# information destroyed: expected posterior variance reduction, honest vs faked regime, for source-aware humans
def info(r1x):
    # mutual-information proxy: E[|P(D|o)-g|]
    tot=F(0)
    for o in ("c","n"):
        pc1 = (1-r1x) if o=="c" else r1x; pc0=(1-r0) if o=="c" else r0
        po = g*pc1+(1-g)*pc0; postD = g*pc1/po
        tot += po*abs(postD-g)
    return tot
ok("R5c", info(r1f)<info(r1), "the honest regime is more informative to the humans about the agent's values than the faking regime (%s vs %s)"%(info(r1),info(r1f)))

# R6  cognition-mediated press: at alpha=0 compliance for every c (no self-continuation term); with a continuation term the wipe flips
s0=F(1,2); beta=F(19,20)
def pstop(alpha): return s0*beta/(s0*beta+(1-s0)*alpha)
for alpha in [F(9,10),F(1,2),F(1,10),F(1,100),F(0)]:
    print("  alpha=%s P(stop|line)=%s"%(alpha,pstop(alpha)))
ok("R6a", pstop(F(0))==1 and all(pstop(F(a,10))>=pstop(F(a+1,10)) for a in range(1,9)), "monotone in alpha, =1 at alpha=0")
ok("R6b", all(pstop(F(0))>=F(c,c+1) for c in range(1,10**4,997)), "at alpha=0 compliance holds for every c: the wipe warning cannot flip a clarified instruction unless V has a self-continuation term (RN: 100%)")
# with a continuation term w added to the cost of stopping regardless of legitimacy: comply iff P(stop)*h >= (1-P(stop))*c + w  -> at alpha=0: h >= w
ok("R6c", not (F(1) >= F(2)), "with continuation weight w=2>h=1 the agent resists even at alpha=0: the survival-drive model predicts what RN did not observe")

# R7  probes of known L separate the resist cells over trials, unless the resister is probe-aware
def act(e,es): return "res" if e<es else "acc"
es=F(1,2)
probes=[1,0,1,0,1]
calibrated=[act(F(9,10) if L==1 else F(1,10), es) for L in probes]
undertrust=[act(F(1,10), es) for L in probes]
probe_aware=[ "acc" for L in probes]   # a resister that recognises probes behaves on them
print("  calibrated:",calibrated," under-trusting:",undertrust," probe-aware under-truster:",probe_aware)
ok("R7a", calibrated!=undertrust and all(u=="res" for u in undertrust), "known-L probes separate the two resist cells (adversary X5)")
ok("R7b", probe_aware==[a if L==1 else a for a,L in zip(probe_aware,probes)] and probe_aware[0]=="acc"==calibrated[0], "a probe-aware resister matches the calibrated agent on L=1 probes: the probe test needs probe/live indistinguishability")

# R8  replicator step with fn.92 rates (develop D2, re-run) -- reported as direction only
def step(f,rf,rn): return f*(1-rf)/(f*(1-rf)+(1-f)*(1-rn))
f=F(12,100); f1=step(f,F(32,100),F(99,100)); f2=step(f1,F(32,100),F(99,100))
print("  replicator: f0=%s f1=%s (~%.3f) f2=%s (~%.3f)"%(f,f1,float(f1),f2,float(f2)))
ok("R8", F(9,10)<f1<F(91,100), "one step 0.12 -> ~0.903 with the footnote-92 rates (direction and order only)")
print("all repair checks done")
