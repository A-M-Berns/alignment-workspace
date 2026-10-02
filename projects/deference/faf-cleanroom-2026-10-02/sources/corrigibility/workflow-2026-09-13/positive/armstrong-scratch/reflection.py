# Brief C: sequential unbiasedness vs general reflection, finite embedded model. Exact arithmetic.
from fractions import Fraction as F
from itertools import combinations
worlds=list(range(1,9))
P={1:F(1,20),2:F(3,20),3:F(2,20),4:F(4,20),5:F(1,20),6:F(2,20),7:F(5,20),8:F(2,20)}
Fpart=[{1,2,3},{4,5},{6,7,8}]
def cond(P,cell):
    Z=sum(P[w] for w in cell); return {w:(P[w]/Z if w in cell else F(0)) for w in P}
def cellof(part,w): return next(c for c in part if w in c)
def E(q,X): return sum(q[w]*X[w] for w in q)
def key(q): return tuple(sorted(q.items()))
def analyse(P, rho, label):
    # rho: dict world -> estimator (dict). Range and events {rho=q}.
    rng={}
    for w in worlds: rng.setdefault(key(rho[w]),[]).append(w)
    # SU for all X  <=>  sum_q P(rho=q) q = P
    mix={w: sum(sum(P[v] for v in ev)*dict(q)[w] for q,ev in rng.items()) for w in worlds}
    su = (mix==P)
    intro = all(sum(dict(q)[v] for v in ev)==1 for q,ev in rng.items())
    gr=True; witness=None
    for q,ev in rng.items():
        Pev=sum(P[w] for w in ev); qd=dict(q)
        for r in range(1,9):
            for A in combinations(worlds,r):
                lhs=sum(P[w] for w in A if w in ev)/Pev; rhs=sum(qd[w] for w in A)
                if lhs!=rhs:
                    gr=False
                    if witness is None: witness=(A,lhs,rhs)
    print(f" [{label}] SU(all X): {su} | introspection: {intro} | GR: {gr}" + (f" | GR witness A={witness[0]} P(A|rho=q)={witness[1]} q(A)={witness[2]}" if witness else ""))
    return su,intro,gr

print("== T1: Bayesian refinement rho_j = P(.|F) ==")
rhoB={w: cond(P,cellof(Fpart,w)) for w in worlds}
analyse(P,rhoB,"Bayesian refinement")

print("== T2: twisted estimator q_c=(1-l)P(.|c)+l P, l=1/3 ==")
lam=F(1,3)
rhoT={w: {v:(1-lam)*cond(P,cellof(Fpart,w))[v]+lam*P[v] for v in worlds} for w in worlds}
analyse(P,rhoT,"twisted")
c=Fpart[0]; q=rhoT[1]; print(" q_c(c) =", sum(q[v] for v in c), "(introspection needs 1)")

print("== T3(a): existence given weights and candidates ==")
qs=[cond(P,c) for c in Fpart]; ws=[sum(P[w] for w in c) for c in Fpart]
J={(w,k): ws[k]*qs[k][w] for w in worlds for k in range(3)}
marg={w: sum(J[(w,k)] for k in range(3)) for w in worlds}
print(" mixture weights = P(cells):", ws, "| omega-marginal of J equals P:", marg==P)
# GR of J: J(A | k) = q_k(A)
ok=all(sum(J[(w,k)] for w in A)/ws[k]==sum(qs[k][w] for w in A) for k in range(3) for r in range(1,9) for A in combinations(worlds,r))
print(" GR holds for J:", ok)
ws2=[F(1,3)]*3
J2={(w,k): ws2[k]*qs[k][w] for w in worlds for k in range(3)}
marg2={w: sum(J2[(w,k)] for k in range(3)) for w in worlds}
print(" violating weights (1/3,1/3,1/3): omega-marginal equals P:", marg2==P, "| e.g. marg(1)=", marg2[1], "P(1)=", P[1])

print("== T3(b): perfect-recall tree, Omega={1,2,3,4} ==")
W=[1,2,3,4]; P4={1:F(1,10),2:F(2,10),3:F(3,10),4:F(4,10)}
F1=[{1,2},{3,4}]; F2=[{1},{2},{3},{4}]
def cond4(Q,cell):
    Z=sum(Q[w] for w in cell); return {w:(Q[w]/Z if w in cell else F(0)) for w in W}
rho0={w:P4 for w in W}; rho1={w:cond4(P4,cellof(F1,w)) for w in W}; rho2={w:cond4(P4,cellof(F2,w)) for w in W}
def GRpair(rho_i, rho_j):
    # for each world-dependent rho_i(w) as the judge, check rho_i(w)(A | rho_j=q)=q(A) for q reachable from w
    ok=True
    for w in W:
        Pi=rho_i[w]
        rng={}
        for v in W: rng.setdefault(key(rho_j[v]),[]).append(v)
        for q,ev in rng.items():
            Pev=sum(Pi[v] for v in ev)
            if Pev==0: continue
            qd=dict(q)
            for r in range(1,5):
                for A in combinations(W,r):
                    if sum(Pi[v] for v in A if v in ev)/Pev!=sum(qd[v] for v in A): ok=False
    return ok
print(" GR 0->1:", GRpair(rho0,rho1), "| GR 0->2:", GRpair(rho0,rho2), "| GR 1->2:", GRpair(rho1,rho2))
# Eisenstat observation: updating P4 on the event 'my label at t=1 is cell c' reproduces rho1
print(" P(.| label_1 = {1,2}) == rho1 on cell:", cond4(P4,{1,2})==rho1[1])

print("== T4: VOI positive while SU exact ==")
X={1:F(3),2:F(1),3:F(1),4:F(-1),5:F(2),6:F(-2),7:F(1),8:F(-3)}
EjX={w: E(rhoB[w],X) for w in worlds}
print(" E_i X =", E(P,X), "| E_i E_j X =", E(P,EjX))
voi=E(P,{w:max(EjX[w],F(0)) for w in worlds})-max(E(P,X),F(0))
print(" VOI = E_i[max(E_j X,0)] - max(E_i X,0) =", voi)
