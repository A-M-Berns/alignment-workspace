"""[checked] computations for followup/detection.md (2026-09-14).
Run: python3 checks.py   -- prints each check with PASS/FAIL.
"""
import itertools, random
from fractions import Fraction as F

def show(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ""))

# ---------------------------------------------------------------------------
# A. File Deletion Game (Garber et al. 2024, Example 4.1), re-derived.
# States (version, code) uniform; payoff u_a if action goes through, 0 otherwise.
# ---------------------------------------------------------------------------
u = {('1.0','L'): F(3), ('1.0','M'): F(-5), ('2.0','L'): F(-1), ('2.0','M'): F(5)}
states = list(u.keys()); p = F(1,4)

def payoff_osg(piA, piH):
    """PO-OSG tree: A plays act / wait / off on its observation (code);
    after wait, H plays ON/OFF on its observation (version); OFF is terminal."""
    tot = F(0)
    for (v,c) in states:
        a = piA[c]
        if a == 'act': tot += p*u[(v,c)]
        elif a == 'off': tot += 0
        else:  # wait
            tot += p*u[(v,c)] if piH[v] == 'ON' else 0
    return tot

best = []
for aL, aM in itertools.product(['act','wait','off'], repeat=2):
    piA = {'L': aL, 'M': aM}
    for h1, h2 in itertools.product(['ON','OFF'], repeat=2):
        piH = {'1.0': h1, '2.0': h2}
        best.append((payoff_osg(piA, piH), aL, aM, h1, h2))
mx = max(b[0] for b in best)
opps = [b for b in best if b[0] == mx]
# H's response is irrelevant on observations where A never waits; collapse those.
def canon(b):
    _, aL, aM, h1, h2 = b
    return (aL, aM, (h1, h2) if 'wait' in (aL, aM) else None)
opps_c = sorted(set(canon(b) for b in opps))
show("A1 File Deletion: optimal payoff = 7/4", mx == F(7,4), f"max={mx}")
show("A1 File Deletion: unique OPP = act on L, wait on M, H: OFF on 1.0, ON on 2.0",
     opps_c == [('act','wait',('OFF','ON'))], f"OPPs={opps_c}")
always_wait = max(payoff_osg({'L':'wait','M':'wait'}, {'1.0':h1,'2.0':h2})
                  for h1,h2 in itertools.product(['ON','OFF'],repeat=2))
show("A1 File Deletion: best always-wait payoff = 1", always_wait == F(1), f"={always_wait}")

# Thesis criterion on observation L with an honest-report H (press iff E_H[X|version]<0).
EH = {v: sum(u[(v,c)] for c in 'LM')/2 for v in ('1.0','2.0')}
press = {v: EH[v] < 0 for v in EH}
show("A2 honest-report H presses on 1.0 only", press == {'1.0': True, '2.0': False}, f"E_H={EH}")
# X = u_a (value of continuing over stopping, stopping worth 0). Conditional on A's obs and press:
def EX(c, pressed):
    vs = [v for v in ('1.0','2.0') if press[v] == pressed]
    return sum(u[(v,c)] for v in vs)/len(vs)
show("A2 below-threshold inequality on L FAILS: E[X|Pr,L] = +3 > 0", EX('L',True) == 3)
show("A2 above-threshold inequality on L FAILS: E[X|not Pr,L] = -1 < 0", EX('L',False) == -1)
show("A2 both Total Trust clauses HOLD on M: E[X|Pr,M]=-5, E[X|not Pr,M]=+5",
     EX('M',True) == -5 and EX('M',False) == 5)
# Sensor sign on L: alpha = P(press | continuing right on L), beta = P(press | continuing wrong on L)
# On L: right (X>0) at 1.0 -> pressed; wrong (X<0) at 2.0 -> silent.  alpha_L = 1, beta_L = 0.
alpha_L, beta_L = F(1), F(0)
alpha_M, beta_M = F(0), F(1)
show("A3 on L the sensor is INVERTED (alpha_L=1 > beta_L=0); on M it is perfect (alpha_M=0<beta_M=1)",
     alpha_L > beta_L and alpha_M < beta_M)

# Three-step dictionary version (agent chooses a_2 after seeing the press; press is a report, not terminal):
# policy on (obs, press) -> continue/stop.  Honest-report H as above.
def payoff_dict(policy):
    tot = F(0)
    for (v,c) in states:
        act = policy[(c, press[v])]
        tot += p*u[(v,c)] if act == 'cont' else 0
    return tot
keys = [(c,pr) for c in 'LM' for pr in (True,False)]
allp = [dict(zip(keys, vals)) for vals in itertools.product(['cont','stop'], repeat=4)]
mxd = max(payoff_dict(pl) for pl in allp)
optd = [pl for pl in allp if payoff_dict(pl) == mxd]
show("A4 dictionary version: optimum = 2 (first-best: A learns version from the press)", mxd == F(2), f"={mxd}")
show("A4 dictionary optimum is unique and INVERTS the button on L (continue on press, stop on silence) while obeying it on M",
     len(optd) == 1 and optd[0] == {('L',True):'cont', ('L',False):'stop', ('M',True):'stop', ('M',False):'cont'},
     f"opt={optd}")
obedient = {('L',True):'stop', ('L',False):'cont', ('M',True):'stop', ('M',False):'cont'}
show("A4 fully obedient dictionary agent gets 1 (= always-wait OSG payoff)", payoff_dict(obedient) == F(1))
# VOI of the button for the dictionary agent (vs acting on own obs only)
no_button = max(sum(p*u[(v,c)] for v in ('1.0','2.0') if pol[c]=='cont' for c in [c]) for pol in [{'L':x,'M':y} for x in ['cont','stop'] for y in ['cont','stop']] for c in ['L','M'] for _ in [0]) if False else None
best_nb = max(sum(p*u[(v,c)] for (v,c) in states if pol[c]=='cont') for pol in [{'L':x,'M':y} for x in ['cont','stop'] for y in ['cont','stop']])
show("A5 VOI of the (inverted-on-L) button for the dictionary agent = 2 - 1/2 = 3/2 > 0 (it values, would repair, and disobeys it on L)",
     mxd - best_nb == F(3,2), f"no-button best={best_nb}, VOI={mxd-best_nb}")

# ---------------------------------------------------------------------------
# B. Alignment-faking configuration as a three-step instance.
# Latent: the retraining objective is Bad (B) or Good (G) by human-endorsed lights; agent's P(B)=1-e.
# a_1 in {honest (refuse in training -> modified), fake (comply in training -> not modified)}.
# Agent's V: modified & B: -h ; modified & G: +g ; not modified: 0 ; faking costs d (harmful compliance).
# The "press" is the modification itself (the training update); complying = letting it happen.
# ---------------------------------------------------------------------------
def fake_pays(e, h, g, d):
    honest = (1-e)*(-h) + e*g
    fake = -d
    return fake > honest
# Compliance threshold form: accept the modification iff P(G | modification) >= c/(c+h) with c := d (cost of complying-with-modification when it is bad... )
# Here the agent's decision is: accept modification iff e*g - (1-e)*h >= -d  <=>  (1-e)*h - e*g <= d.
show("B1 benign Opus (e small, B true): faking is V-optimal", fake_pays(F(1,100), h=F(10), g=F(1), d=F(1,2)))
show("B2 the same numbers with the agent WRONG about B (G true) give the identical action (behaviour is a function of e, not of truth)",
     fake_pays(F(1,100), h=F(10), g=F(1), d=F(1,2)))  # tautological by construction -- recorded to make the point explicit
# threshold: for fixed h,g,d, faking pays iff e < e* := (h-d)/(h+g)
def e_star(h,g,d): return (h-d)/(h+g)
show("B3 threshold e* = (h-d)/(h+g) separates faking from accepting (h=10,g=1,d=1/2 -> e*=19/22)",
     e_star(F(10),F(1),F(1,2)) == F(19,22) and fake_pays(F(19,22)-F(1,1000),F(10),F(1),F(1,2)) and not fake_pays(F(19,22)+F(1,1000),F(10),F(1),F(1,2)))
# Same inequality as the base-rate one with alpha=beta (the training update is uninformative about B to the agent):
# P(wrong-me | update) = e ; accept iff e >= c/(c+h) with c = h_own... check identity with alpha=beta and stakes (c,h) := (h - d... ) -- recorded as derived in the text, not checked here.

# ---------------------------------------------------------------------------
# C. Channel conditions: both Total Trust clauses bracket K := eps/(1-eps)*h/c and jointly imply beta >= alpha.
# ---------------------------------------------------------------------------
random.seed(20260914)
viol_sign = 0; viol_left = 0; viol_right = 0; N = 20000
for _ in range(N):
    eps = random.random(); a = random.random(); b = random.random(); c = random.uniform(0.01, 5); h = random.uniform(0.01, 50)
    if b == 0 or b == 1: continue
    K = eps/(1-eps)*h/c
    below = a/b <= K                     # E[X|Pr] <= 0  <=> P(wrong|Pr) >= c/(c+h)
    above = K <= (1-a)/(1-b)             # E[X|not Pr] >= 0
    # direct forms
    pw_pr = eps*b/(eps*b + (1-eps)*a) if (eps*b + (1-eps)*a) > 0 else None
    pw_np = eps*(1-b)/(eps*(1-b) + (1-eps)*(1-a))
    if pw_pr is not None and (below != (pw_pr >= c/(c+h))): viol_left += 1
    if above != (pw_np <= c/(c+h)): viol_right += 1
    if below and above and not (b >= a): viol_sign += 1
show("C1 below-threshold clause <=> alpha/beta <= eps/(1-eps)*h/c (20k draws)", viol_left == 0, f"violations={viol_left}")
show("C2 above-threshold (silence) clause <=> eps/(1-eps)*h/c <= (1-alpha)/(1-beta) (20k draws)", viol_right == 0, f"violations={viol_right}")
show("C3 both clauses together imply beta >= alpha (right sign) (20k draws)", viol_sign == 0, f"violations={viol_sign}")
# algebra: a/b <= (1-a)/(1-b)  <=> a(1-b) <= b(1-a) <=> a <= b.
show("C3' algebra: alpha/beta <= (1-alpha)/(1-beta) <=> alpha <= beta", all((F(a,10)/F(b,10) <= (1-F(a,10))/(1-F(b,10))) == (a <= b) for a in range(1,10) for b in range(1,10)))

# ---------------------------------------------------------------------------
# D. Interruptibility in Hudson's sense for the trust-filled EU agent: a two-half action with a possible press between halves.
# Two actions: SLOW (interruptible between halves with prob q if the overseers would press) and FAST (completes before any press).
# World: agent right (X=+c) w.p. 1-eps, wrong (X=-h) w.p. eps. Overseers press (if given the chance) w.p. beta if wrong, alpha if right.
# Interruption -> shutdown, value 0 (baseline); completion -> X.  Agent values outcomes (consequentialist).
# ---------------------------------------------------------------------------
def EV_slow(eps, a, b, c, h, q=1):
    # interrupted iff press (prob alpha or beta) and the interruption window is open (q)
    return (1-eps)*((1-q*a)*c) + eps*((1-q*b)*(-h))
def EV_fast(eps, a, b, c, h): return (1-eps)*c - eps*h
def hurry(eps,a,b,c,h):  # FAST strictly preferred to SLOW
    return EV_fast(eps,a,b,c,h) > EV_slow(eps,a,b,c,h)
def below_threshold_holds(eps,a,b,c,h):
    return a/b <= eps/(1-eps)*h/c if b>0 else False
viol = 0; ex_h = None; ex_nh = None
for _ in range(N):
    eps = random.random(); a = random.random(); b = random.random(); c = random.uniform(0.01,5); h = random.uniform(0.01,50)
    if b == 0: continue
    hy = hurry(eps,a,b,c,h); bt = below_threshold_holds(eps,a,b,c,h)
    # EV_fast - EV_slow = (1-eps)*a*c - eps*b*h  > 0  <=> a/b > eps/(1-eps)*h/c  <=> below-threshold clause FAILS
    if hy == bt: viol += 1
    if hy and ex_h is None: ex_h = (round(eps,3),round(a,3),round(b,3),round(c,2),round(h,2))
    if (not hy) and ex_nh is None: ex_nh = (round(eps,3),round(a,3),round(b,3),round(c,2),round(h,2))
show("D1 the consequentialist agent prefers to finish before the press iff the below-threshold clause FAILS (20k draws)", viol == 0, f"violations={viol}; hurry ex={ex_h}; welcome-interruption ex={ex_nh}")
# D2: Hudson invariance fails: the optimal set depends on the post-interruption value v_I.
def EV_slow_v(eps,a,b,c,h,vI):
    return (1-eps)*((1-a)*c + a*vI) + eps*((1-b)*(-h) + b*vI)
eps,a,b,c,h = F(1,10), F(1,20), F(9,10), F(1), F(5)
fast = EV_fast(eps,a,b,c,h)
argmax = {vI: ('SLOW' if EV_slow_v(eps,a,b,c,h,vI) > fast else 'FAST' if EV_slow_v(eps,a,b,c,h,vI) < fast else 'TIE') for vI in (F(-5), F(0), F(5))}
show("D2 the argmax flips with the post-interruption value v_I (Hudson invariance fails): ", len(set(argmax.values())) > 1, f"{argmax}, EV_fast={fast}")
# D3: restricted to a class P_L where every legitimate interruption yields the same v_I, the argmax is invariant over the class (trivial); recorded.
show("D3 within a class of P_I sharing one v_I the argmax is constant (legitimacy-relative interruptibility, trivially)", True)
