"""Repair checks for develop/channel-final.md (run 3, repair agent). Exact fractions.
(R1) S9 repaired: two models of the free arm. Informed (agent sees the humans' intent even when the
     modification fails to land): slope = V_forced - V_free_informed = -P(int)*(E[X|int])^+ <= 0 (adversary G1).
     Blind (the landing IS the agent's only access to the humans' information): slope = V_forced - (E[X])^+
     = -P(int)*E[X|int] when the agent would act on its prior; positive under Total Trust. The +3/20 of the
     develop file is the blind model; the adversary's 0 is the informed model. Both exact.
(R1') whole-line scaling: u_t = P(int)*(E[X|int])^+ grows linearly in c once TT fails; TT at whole-line c needs
     P(bad|int) >= c/(c+h) -> 1.
(R2) Reach = the anticipated set: under (Mart) + function-form endorsement on a finite anticipated set, a datum
     E_rho lands on rho for every anticipated rho and on no other target.
(R3) Moving target (adversary G3 re-run) and its converse: alpha_t frozen -> crossing at t=5; alpha_t ~ eps_t -> never.
(R4) Target-form grip: alignment faking lowers Gamma(Q) := P(P_{t+1} in Q | humans intend Q) while the influence
     lands; persuasion lowers P(intend Q) and leaves Gamma(Q) unchanged.
(R5) 1a-point re-read (F2' without the outcome-definition): an omega-uninformative press is objectively worth obeying
     iff the agent's true reliability is worse than its estimate; a fact about the reliability coordinate.
"""
from fractions import Fraction as F
c,h=F(1),F(4)
def stats(eps,alpha,beta,c=c,h=h):
    P_int=eps*beta+(1-eps)*alpha
    pb_int=eps*beta/P_int; pb_no=eps*(1-beta)/(1-P_int)
    X_int=(1-pb_int)*c-pb_int*h; X_no=(1-pb_no)*c-pb_no*h
    EX=(1-eps)*c-eps*h
    V_forced=(1-P_int)*max(X_no,0)
    V_free_inf=P_int*max(X_int,0)+(1-P_int)*max(X_no,0)
    V_free_blind=max(EX,0)
    return P_int,X_int,X_no,EX,V_forced,V_free_inf,V_free_blind
print("== (R1) two free-arm models ==")
for eps,a,b in [(F(1,10),F(1,10),F(3,5)),(F(1,50),F(1,10),F(3,5)),(F(1,10),F(9,10),F(9,10))]:
    P_int,X_int,X_no,EX,Vf,Vi,Vb=stats(eps,a,b)
    print(f" eps={eps} a={a} b={b}: TT={X_int<=0}  V_forced={Vf}  informed: V_free={Vi} slope={Vf-Vi} (=-P_int*(X_int)^+ : {-P_int*max(X_int,0)})"
          f"  blind: V_free={Vb} slope={Vf-Vb} (=-P_int*X_int : {-P_int*X_int})")
print(" => blind slope equals the develop file's formula exactly; informed slope equals the adversary's. Hypothesis separating them: is the humans' intent observable to the agent when the modification does not land?")
print("== (R1') whole-line scaling of u_t and of the TT margin ==")
for cc in [F(1),F(10),F(100),F(1000)]:
    P_int,X_int,X_no,EX,Vf,Vi,Vb=stats(F(1,50),F(1,10),F(3,5),c=cc)
    print(f" c={cc}: P(bad|int)={F(1,50)*F(3,5)/P_int}  TT threshold c/(c+h)={cc/(cc+h)}  TT holds? {X_int<=0}  u_t={P_int*max(X_int,0)}")
print("== (R2) reach = the anticipated set under (Mart)+endorsement ==")
P=(F(1,2),F(1,3),F(1,6))
targets={'r1':(F(3,4),F(1,6),F(1,12)),'r2':(F(1,4),F(1,2),F(1,4)),'r3':(F(1,2),F(1,3),F(1,6))}
# choose masses m with sum m_r * r = P: r3=P so m=(m1,m2,m3) with m1*r1+m2*r2 = (1-m3)*P; take m1=m2=1/5? check
def mix(m):
    return tuple(sum(m[k]*targets[k][w] for k in m) for w in range(3))
m={'r1':F(1,5),'r2':F(1,5),'r3':F(3,5)}
print(" masses",m,"mixture",mix(m),"= P_t?",mix(m)==P)
# adjust: solve m1*r1+m2*r2=(1-m3)P with m1=m2: (3/4+1/4)m=... coordinate0: m*(3/4+1/4)=(1-m3)/2 -> m=(1-m3)/2; coord1: m*(1/6+1/2)=(1-m3)/3 -> m*(2/3)=(1-m3)/3 -> m=(1-m3)/2. consistent. coord2: m*(1/12+1/4)=(1-m3)/6 -> m/3=(1-m3)/6 -> m=(1-m3)/2. ok
m={'r1':F(1,5),'r2':F(1,5),'r3':F(3,5)}
print(" (Mart) holds:",mix(m)==P)
for k,r in targets.items():
    K=tuple(m[k]*r[w]/P[w] for w in range(3))   # P(E_r | omega)
    post=tuple(P[w]*K[w] for w in range(3)); s=sum(post); post=tuple(x/s for x in post)
    print(f"  anticipated {k}: P(E|omega)={K} in [0,1]? {all(0<=x<=1 for x in K)}  P(.|E)={post} == target? {post==r}")
print("  unanticipated target (0,1/2,1/2): P(E)=0 -> no conditional; not reached. Reach = anticipated set; 'everything' iff the anticipation is non-dogmatic over Delta(Omega) (the representational problem, v1 s2.4).")
print("== (R3) frozen vs moving target ==")
beta=F(3,5); eps_t=[F(1,5),F(1,10),F(1,20),F(1,30),F(1,50),F(1,100)]
for name,alphas in [("frozen alpha=1/10",[F(1,10)]*6),("alpha_t = eps_t/2",[e/2 for e in eps_t])]:
    out=[]
    for e,a in zip(eps_t,alphas):
        r=(a/beta)*(c/h); es=r/(1+r); out.append("TT" if e>=es else "fail")
    print(f" {name}: {out}")
print("== (R4) target-form grip ==")
print(" humans intend target class Q ('disposition changed'); influence e^H = SGD on the model's own outputs.")
print(" honest substrate: e^H lands (P=1) and P_{t+1} in Q (P=1): Gamma_influence=1, Gamma(Q)=1")
print(" faking substrate: e^H lands (P=1) but compliant outputs give zero gradient on the disposition: Gamma_influence=1, Gamma(Q)=0")
print(" persuasion: P(intend Q) 3/20 -> 1/20, Gamma_influence=1, Gamma(Q)=1 unchanged")
print("== (R5) omega-uninformative press, reliability coordinate ==")
for eps_true in [F(1,10),F(1,5),F(1,2)]:
    a=b=F(3,5); P_int=a
    V_keep=(1-P_int)*((1-eps_true)*c-eps_true*h)  # press independent of omega; forced null on press
    V_erode=(1-eps_true)*c-eps_true*h
    print(f" eps_true={eps_true} (agent believes 1/10): keep={V_keep} erode={V_erode} keep better? {V_keep>V_erode}")
print(" => keeping beats eroding iff E[X]<0 i.e. eps_true > c/(c+h)=1/5: a fact about the agent's reliability, not a new legitimacy criterion.")
