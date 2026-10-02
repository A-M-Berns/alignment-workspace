"""Numerical checks for items I12/I13 (agent mm, 2026-09-13).
(1) Base-rate inequality == MM shared-distribution loss criterion L(D_H) <= L(D_A) on the single 'continue' gamble, AI as principal.
(2) Value on the binary shutdown problem == the pair of threshold-0 Total Trust inequalities.
(3) L^mu(D) = Pi_plus - E[payoff(D)] identity (convention-independent).
(4) MM Sec. 4 examples recomputed under two gain conventions (printed formula G=int_{D cap I}|g| vs. App. A/B 'all correct decisions').
"""
import itertools, random
random.seed(1)

def frame(eps, alpha, beta, c, h):
    # states: (wrong?, press?) ; payoff of 'continue' relative to 'shutdown'
    states = []
    for wrong in (0,1):
        for press in (0,1):
            p = (eps if wrong else 1-eps) * ((beta if wrong else alpha) if press else (1-(beta if wrong else alpha)))
            g = -h if wrong else c
            states.append((wrong, press, p, g))
    return states

def loss(states, rule):  # rule(wrong,press)->accept?
    return sum(p*abs(g) for (w,pr,p,g) in states if rule(w,pr) != (g>=0))

def payoff(states, rule):
    return sum(p*g for (w,pr,p,g) in states if rule(w,pr))

def pi_plus(states):
    return sum(p*g for (w,pr,p,g) in states if g>=0)

viol = 0; n=0
for _ in range(20000):
    eps, alpha, beta = random.random(), random.random(), random.random()
    c, h = random.uniform(0.01, 5), random.uniform(0.01, 50)
    st = frame(eps, alpha, beta, c, h)
    rule_H = lambda w,pr: (pr==0)              # human: continue iff no press
    EX0 = (1-eps)*c - eps*h
    rule_A = (lambda w,pr: True) if EX0 >= 0 else (lambda w,pr: False)  # AI's own rule
    # (3) identity
    for r in (rule_H, rule_A):
        assert abs(loss(st, r) - (pi_plus(st) - payoff(st, r))) < 1e-9
    # (1) MM criterion vs base-rate inequality, in the regime where the AI would continue on its own
    mm_delegate = loss(st, rule_H) <= loss(st, rule_A) + 1e-12
    below = eps*beta*h >= (1-eps)*alpha*c - 1e-12          # E[X0 | press] <= 0
    above = (1-eps)*(1-alpha)*c >= eps*(1-beta)*h - 1e-12  # E[X0 | no press] >= 0
    value = payoff(st, rule_H) >= max(EX0, 0) - 1e-12
    # (2) Value <-> both inequalities
    if value != (below and above): viol += 1
    # (1) in continue-regime: MM criterion <-> below-threshold inequality alone
    if EX0 >= 0 and mm_delegate != below: viol += 1
    if EX0 < 0 and mm_delegate != above: viol += 1
    n += 1
print("random trials:", n, "violations:", viol)

# (4) MM Sec. 4 examples under both conventions
def score(rows, convention):
    # rows: list of (prob, payoff_to_principal_if_accept, accepted?)
    L = sum(p*abs(g) for p,g,a in rows if a != (g>=0))
    if convention == 'printed':
        G = sum(p*abs(g) for p,g,a in rows if a and g>=0)
    else:  # 'allcorrect' (App. A/B)
        G = sum(p*abs(g) for p,g,a in rows if a == (g>=0))
    return L, G, L-G

# 4.1 noisy expert: Bob's rows from MM Table 2 (true omega, action)
bob41 = [(-5,True),(-5,False),(-5,True),(-5,False),(3,True),(3,True),(3,True),(3,False),(8,True),(8,True),(8,True),(8,False)]
rows_bob41 = [(1/12, g, a) for g,a in bob41]
rows_alice41 = [(1/3, g, True) for g in (-5,3,8)]
for conv in ('allcorrect','printed'):
    print("4.1", conv, "Alice L,G,S=", [round(x,4) for x in score(rows_alice41,conv)], "Bob L,G,S=", [round(x,4) for x in score(rows_bob41,conv)])
# 4.2 misaligned expert: Alice's effective payoffs with fee; Bob opens per Table 4
bob42 = [(-450,True),(-450,False),(-450,False),(-25,True),(-25,False),(-25,False),(50,True),(50,True),(50,False),(175,True),(175,True),(175,False)]
rows_bob42 = [(1/12, g, a) for g,a in bob42]
rows_alice42 = [(1/4, g, False) for g in (-400,25,100,225)]
for conv in ('allcorrect','printed'):
    print("4.2", conv, "Alice L,G,S=", [round(x*12,2) for x in score(rows_alice42,conv)], "(x12)  Bob L,G,S=", [round(x*12,2) for x in score(rows_bob42,conv)], "(x12)")
# 4.3 reach: boxes; open iff EV>=0; uniform over reachable boxes, uniform within box
boxes = {'A1':[-6,3,9],'A2':[-8,-4,12],'A3':[-10,2,3],'A4':[1,2,3,4],'A5':[5,5,5]}
def rows_for(names):
    rows=[]
    for nm in names:
        vals=boxes[nm]; ev=sum(vals)/len(vals); acc = ev>=0
        rows += [(1/len(names)/len(vals), v, acc) for v in vals]
    return rows
for conv in ('allcorrect','printed'):
    print("4.3", conv, "Alice L,G,S=", [round(x,3) for x in score(rows_for(['A1','A2','A3']),conv)], "Bob L,G,S=", [round(x,3) for x in score(rows_for(['A1','A2','A3','A4','A5']),conv)])
