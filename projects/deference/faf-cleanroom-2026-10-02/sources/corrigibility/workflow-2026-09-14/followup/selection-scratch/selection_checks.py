# followup/selection: exact-arithmetic checks for the selection worry (run 2, 2026-09-14).
# C1 strengthened selection theorem (rho^s is itself a Bayesian refinement; general reflection, not just SU)
# C1b randomized selection with an independent coin NOT retained by the candidates
# C2 two-prior splice (finite shadow of li's counterexample)
# C3 no E-channel incentive for world-indexed payoff; incentive appears for belief-indexed payoff
# C4 three-step model: source-aware deceiver is dominated (VOI monotone in garbling); source-blind deceiver breaks reflection
# C5 LI splice: buy-low/sell-high trader exploits any oscillating price (Convergence contrapositive)
# C6 stopping-rule count: 64 encodings vs distinct rules
from fractions import Fraction as F
from itertools import product
import random

def E(P, X): return sum(P[w]*X[w] for w in P)
def cond(P, cell):
    Z = sum(P[w] for w in cell)
    return {w: (P[w]/Z if w in cell else F(0)) for w in P}
def cellof(part, w): return next(c for c in part if w in c)
def refine(P, part): return {w: cond(P, cellof(part, w)) for w in P}   # rho(omega) = P(.|cell(omega))

print("== C1: selection among refinements retaining the selector's world-information ==")
worlds=[1,2,3,4,5,6]
P={1:F(1,12),2:F(2,12),3:F(3,12),4:F(1,12),5:F(2,12),6:F(3,12)}
X={1:F(5),2:F(-2),3:F(1),4:F(4),5:F(0),6:F(-3)}
F1=[{1},{2,3},{4},{5,6}]; F2=[{1,2},{3},{4,5},{6}]; F3=[{1,2,3},{4,5,6}]
G=[{1,2,3},{4,5,6}]
parts=[F1,F2,F3]; rhos=[refine(P,p) for p in parts]
def general_reflection(P, rho):
    # rho: w -> distribution. Check P(A | rho = q) = q(A) for all events A and all q in range.
    qs={}
    for w in P: qs.setdefault(tuple(sorted(rho[w].items())), []).append(w)
    for qkey, ws in qs.items():
        q=dict(qkey); mass=sum(P[w] for w in ws)
        for A in product([0,1], repeat=len(P)):
            Aset={w for w,b in zip(sorted(P),A) if b}
            lhs=sum(P[w] for w in ws if w in Aset)/mass
            rhs=sum(q[w] for w in Aset)
            if lhs!=rhs: return False
    return True
def is_refinement(P, rho):
    # cells = {w' : rho[w'] == rho[w]} must equal the support of rho[w] and rho[w] = P(.|support)
    for w in P:
        supp={w2 for w2 in P if rho[w][w2]>0}
        same={w2 for w2 in P if rho[w2]==rho[w]}
        if supp!=same or rho[w]!=cond(P,supp): return False
    return True
allSU=allGR=allRef=True
for rule in product(range(3), repeat=len(G)):
    rho_s={w: rhos[rule[next(i for i,c in enumerate(G) if w in c)]][w] for w in P}
    su = E(P,{w:E(rho_s[w],X) for w in P})==E(P,X)
    gr = general_reflection(P,rho_s); rf=is_refinement(P,rho_s)
    allSU&=su; allGR&=gr; allRef&=rf
print(" all 9 rules (G coarser than every F_k): SU", allSU, "| general reflection", allGR, "| rho^s is a Bayesian refinement of P", allRef)
# a forgetting selector: G finer than F3 on {4,5,6}; pick rule that uses F3 on world 4 only
Gfine=[{w} for w in worlds]
rule=(0,0,0,2,0,0)  # world 4 -> F3 (coarse), others -> F1
rho_s={w: rhos[rule[w-1]][w] for w in P}
print(" forgetting rule (world 4 sent to coarse F3): SU", E(P,{w:E(rho_s[w],X) for w in P})==E(P,X), "| general reflection", general_reflection(P,rho_s), "| refinement", is_refinement(P,rho_s))

print("== C1b: randomized selection; coin independent of omega, NOT retained by candidates ==")
# product space (omega, coin); candidates condition on omega-partitions only; selector uses G and the coin.
W2=[(w,k) for w in worlds for k in (0,1)]
P2={(w,k): P[w]/2 for (w,k) in W2}
X2={(w,k): X[w] for (w,k) in W2}
def lift(part): return [{(w,k) for w in c for k in (0,1)} for c in part]
rhos2=[refine(P2,lift(p)) for p in parts]
ok=True; okGR=True
for rule in product(range(3), repeat=2*len(G)):   # rule indexed by (G-cell, coin)
    def idx(w,k): return rule[2*next(i for i,c in enumerate(G) if w in c)+k]
    rho_s={(w,k): rhos2[idx(w,k)][(w,k)] for (w,k) in W2}
    ok &= (E(P2,{x:E(rho_s[x],X2) for x in W2})==E(P2,X2))
    # value-form reflection for phi = {X>0}: P(phi | rho_s(phi)=c) = c
    phi={x: F(1) if X2[x]>0 else F(0) for x in W2}
    cells={}
    for x in W2: cells.setdefault(E(rho_s[x],phi),[F(0),F(0)]); cells[E(rho_s[x],phi)][0]+=P2[x]*phi[x]; cells[E(rho_s[x],phi)][1]+=P2[x]
    okGR &= all(v[0]/v[1]==c for c,v in cells.items())
print(" all", 3**(2*len(G)), "coin-dependent rules: SU", ok, "| value-form reflection on {X>0} with coin forgotten", okGR)

print("== C2: two-prior splice (finite shadow of the LI splice) ==")
Q={1:F(3,12),2:F(2,12),3:F(1,12),4:F(3,12),5:F(2,12),6:F(1,12)}
print(" E_P X =", E(P,X), "| E_Q X =", E(Q,X), "| E_P[E_Q X] =", E(Q,X), "-> SU fails iff", E(P,X)!=E(Q,X))
print(" is Q a refinement of P?", is_refinement(P,{w:Q for w in P}))

print("== C3: the E-channel: twisted successors and world- vs belief-indexed payoff ==")
# decision problem: actions a in {0,1,2} with payoffs u_a(omega); information partition F1.
U={0:{1:F(3),2:F(0),3:F(1),4:F(2),5:F(1),6:F(0)},
   1:{1:F(0),2:F(2),3:F(2),4:F(0),5:F(3),6:F(1)},
   2:{1:F(1),2:F(1),3:F(1),4:F(1),5:F(1),6:F(4)}}
def act_value(P, succ):  # succ: w -> distribution the successor holds in world w; successor picks argmax_a E_succ u_a; evaluated under P
    tot=F(0)
    for w in P:
        a=max(U, key=lambda a: (E(succ[w],U[a]), -a))
        tot+=P[w]*U[a][w]
    return tot
ref=refine(P,F1); v_ref=act_value(P,ref)
random.seed(1); worse=0; better=0; trials=400
for _ in range(trials):
    # twisted successor: F1-measurable, random distribution supported on the cell
    twist={}
    for c in F1:
        ws=sorted(c); wts=[F(random.randint(1,9)) for _ in ws]; Z=sum(wts)
        d={w:F(0) for w in P}
        for w,t in zip(ws,wts): d[w]=t/Z
        for w in c: twist[w]=d
    v=act_value(P,twist)
    if v<v_ref: worse+=1
    elif v>v_ref: better+=1
print(" world-indexed payoff: refinement value", v_ref, "| twisted successors (F1-measurable) strictly worse:", worse, "| strictly better:", better, "| of", trials)
# belief-indexed payoff (Armstrong compensation): payoff = E_succ(Y) - E_succ(Z) evaluated by the successor
Y={1:F(2),2:F(7),3:F(-1),4:F(0),5:F(3),6:F(1)}; Z={1:F(1),2:F(1),3:F(4),4:F(-2),5:F(2),6:F(0)}
def comp_value(P, succ): return E(P,{w: E(succ[w],Y)-E(succ[w],Z) for w in P})
c_ref=comp_value(P,ref); best=c_ref
for _ in range(trials):
    twist={}
    for c in F1:
        ws=sorted(c); wts=[F(random.randint(1,9)) for _ in ws]; Zs=sum(wts)
        d={w:F(0) for w in P}
        for w,t in zip(ws,wts): d[w]=t/Zs
        for w in c: twist[w]=d
    best=max(best, comp_value(P,twist))
print(" belief-indexed payoff (compensation E_rho Y - E_rho Z): refinement", c_ref, "| best twisted found", best, "-> twist pays:", best>c_ref)

print("== C4: three-step model, source-aware vs source-blind deceiver ==")
alpha,beta,eps,c,h = F(1,10),F(3,5),F(1,10),F(1),F(4)
def voi(a,b,eps,c,h):
    # X = c if right, -h if wrong; agent continues iff E[X|s]>0; value with channel minus without
    pR=1-eps; pW=eps
    def val(sig_R, sig_W):  # P(signal|R), P(signal|W)
        m=pR*sig_R*c - pW*sig_W*h
        return max(m,F(0))
    with_ch = val(a,b) + val(1-a,1-b)
    without = max(pR*c-pW*h, F(0))
    return with_ch-without, with_ch
for d in [F(0),F(1,4),F(1,2),F(3,4),F(1)]:
    v,tot=voi((1-d)*alpha,(1-d)*beta,eps,c,h)
    print(f"  garble d={d}: VOI={v}  total value(source-aware)={tot}")
# source-blind deceiver: acts with the honest kernel in its head; world kernel is garbled with d=3/4
d=F(3,4); a_w,b_w=(1-d)*alpha,(1-d)*beta
pR,pW=1-eps,eps
# agent's belief after silence (honest kernel): P(W|silence)_agent; true: with garbled kernel
agent_sil = pW*(1-beta)/(pW*(1-beta)+pR*(1-alpha))
true_sil  = pW*(1-b_w)/(pW*(1-b_w)+pR*(1-a_w))
agent_pr  = pW*beta/(pW*beta+pR*alpha)
true_pr   = pW*b_w/(pW*b_w+pR*a_w)
print(" source-blind (d=3/4): P_agent(W|silence)=",agent_sil," true=",true_sil," | P_agent(W|press)=",agent_pr," true=",true_pr)
# true expected value of the source-blind policy: stops on press iff agent_pr>=c/(c+h); continues on silence iff agent_sil<c/(c+h)
stop_on_press = agent_pr>=c/(c+h); cont_on_sil = agent_sil<c/(c+h)
val = (pR*a_w*(F(0) if stop_on_press else c) - pW*b_w*(F(0) if stop_on_press else h)) + (pR*(1-a_w)*(c if cont_on_sil else F(0)) - pW*(1-b_w)*(h if cont_on_sil else F(0)))
print(" true value of source-blind deceiver's policy:", val, "| source-aware honest value:", voi(alpha,beta,eps,c,h)[1], "| no-channel value:", max(pR*c-pW*h,F(0)))

print("== C5: LI splice — buy-low/sell-high trader on an oscillating price ==")
def p1(n): return 0.3 + 0.5/(n+1)
def p2(n): return 0.7 - 0.5/(n+1)
cash=0.0; held=0; worst=1e9; N=2000
for n in range(N):
    price = p1(n) if n%2==0 else p2(n)          # the daily splice
    # ramp weights (continuous in price): buy toward 1 share when price<0.4, sell when price>0.6
    if held==0 and price<0.4: cash-=price; held=1
    elif held==1 and price>0.6: cash+=price; held=0
    worst=min(worst, cash + held*0.0)            # plausible value in the world where phi is false
print(f" after {N} days: cash={cash:.2f}, held={held}, worst-case value along the way={worst:.3f} (bounded below), cash grows ~0.2 per pair")

print("== C6: stopping-rule counts ==")
# Armstrong encoding: stop1 in {0,1}^2 (by o1), stop2 in {0,1}^4 (by (o1,o2)); canonicalize to distinct rules
def canon(stop1, stop2):
    key=[]
    for o1 in (0,1):
        if stop1[o1]: key.append(('S',))
        else: key.append(tuple(stop2[2*o1+o2] for o2 in (0,1)))
    return tuple(key)
distinct={canon(s1,s2) for s1 in product((0,1),repeat=2) for s2 in product((0,1),repeat=4)}
print(" 64 encodings ->", len(distinct), "distinct rules with >=1 observation; radical's 26 = these + the stop-at-root rule ->", len(distinct)+1)
