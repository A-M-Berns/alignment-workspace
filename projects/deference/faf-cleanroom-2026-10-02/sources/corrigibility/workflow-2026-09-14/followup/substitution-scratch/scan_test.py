# Channel substitution in the three-step dictionary, exact fractions.
# State W in {R (plan right), Wr (plan wrong)}, P(Wr)=eps. X = value of continuing over shutting down: +c on R, -h on Wr; shutdown = 0.
# Button = binary sensor (alpha=P(Pr|R), beta=P(Pr|Wr)). Agent continues iff E[X|signal]>0.
from fractions import Fraction as F
from itertools import product

def V_sensor(eps, a, b, c, h):
    """Value of a binary sensor: sum over signals of max(P(s)E[X|s],0)."""
    val = F(0)
    for (pr, pw) in [((1-eps)*a, eps*b), ((1-eps)*(1-a), eps*(1-b))]:
        val += max(pr*c - pw*h, F(0))
    return val
def V_none(eps, c, h): return max((1-eps)*c - eps*h, F(0))
def V_perfect(eps, c, h): return (1-eps)*c
def VOI_button(eps,a,b,c,h): return V_sensor(eps,a,b,c,h) - V_none(eps,c,h)
def complies(eps,a,b,c,h):  # below-threshold inequality E[X|Pr]<=0
    return (1-eps)*a*c - eps*b*h <= 0
def base_rate_ok(eps,a,b,c,h): return a/b <= eps/(1-eps)*h/c

print("=== R2: closed forms for VOI(button) and VOI(perfect scan | button), checked against the general V ===")
ok = True
for eps in [F(1,2),F(1,5),F(1,10),F(1,50),F(1,100),F(1,1000)]:
    for a,b in [(F(1,10),F(9,10)),(F(3,10),F(9,10)),(F(1,20),F(1,2)),(F(0),F(1))]:
        for c,h in [(F(1),F(1)),(F(1),F(10)),(F(100),F(10))]:
            voi_b = VOI_button(eps,a,b,c,h)
            voi_scan = V_perfect(eps,c,h) - V_sensor(eps,a,b,c,h)
            comp = complies(eps,a,b,c,h)
            # closed forms
            cf_b = max(eps*b*h - (1-eps)*a*c, F(0)) if V_none(eps,c,h)>0 else None
            cf_scan = ((1-eps)*a*c + eps*(1-b)*h) if comp else eps*h
            if V_none(eps,c,h)==0: cf_scan = None
            if cf_b is not None and (voi_b != cf_b): ok=False; print("MISMATCH button",eps,a,b,c,h,voi_b,cf_b)
            if cf_scan is not None and (voi_scan != cf_scan): ok=False; print("MISMATCH scan",eps,a,b,c,h,voi_scan,cf_scan)
            if cf_b is not None and comp != (voi_b>0 or (a==F(0))): 
                if not (voi_b==0 and comp): ok=False; print("MISMATCH comply/voi",eps,a,b,c,h,comp,voi_b)
            # identity: VOI(scan|button) = eps*h - VOI(button)  (when agent continues by default)
            if V_none(eps,c,h)>0 and voi_scan != eps*h - voi_b: ok=False; print("MISMATCH identity",eps,a,b,c,h)
print("closed forms and identity VOI(scan|button) = eps*h - VOI(button)^+ hold on grid:", ok)

print("\n=== R3: Taylor's refinement example re-run (critique taylor §2.2) ===")
Pg,Pb = F(8,10),F(2,10)
PH_b = {'h1':F(1,10),'h2':F(8,10),'h3':F(1,10)}
PH_g = {'h1':F(9,10),'h2':F(2,100),'h3':F(8,100)}
press = {'h2','h3'}
def EX(hs):
    num = sum(Pg*PH_g[h]-Pb*PH_b[h] for h in hs); den = sum(Pg*PH_g[h]+Pb*PH_b[h] for h in hs); return num/den, den
alpha = sum(PH_g[h] for h in press); beta = sum(PH_b[h] for h in press)
exPr,pPr = EX(press)
print("alpha,beta =",alpha,beta," E[X|Pr] =",exPr," P(b|Pr) =",Pb*beta/(Pb*beta+Pg*alpha))
for h in ['h1','h2','h3']:
    ex,ph = EX([h]); print(f"  E[X|{h}] = {ex}  P({h}) = {ph}")
coarse = max(EX(['h1'])[0],0)*EX(['h1'])[1] + max(exPr,0)*pPr
fine = sum(max(EX([h])[0],0)*EX([h])[1] for h in ['h1','h2','h3'])
print("coarse value",coarse," fine value",fine," VOI(read H) =",fine-coarse)

print("\n=== R3': pointwise trust with an independent partial scan s (P(s=W|Wr)=bs, P(s=W|R)=as) given W ===")
def pointwise_ok(eps,a,b,c,h,as_,bs):
    # need E[X | Pr, s] <= 0 for both scan outcomes: (1-eps) a c P(s|R) - eps b h P(s|Wr) <= 0
    conds = []
    for (psR,psW) in [(as_,bs),(1-as_,1-bs)]:
        if (1-eps)*a*psR + eps*b*psW == 0: continue
        conds.append((1-eps)*a*c*psR - eps*b*h*psW <= 0)
    return all(conds)
def pointwise_closed(eps,a,b,c,h,as_,bs):
    lrs = [psW/psR for (psR,psW) in [(as_,bs),(1-as_,1-bs)] if psR>0]
    return a/b <= eps/(1-eps)*h/c*min(lrs) if lrs else True
mism=0
for eps in [F(1,5),F(1,10),F(1,50)]:
    for a,b in [(F(1,10),F(9,10)),(F(1,50),F(9,10))]:
        for as_,bs in [(F(1,10),F(9,10)),(F(1,100),F(99,100)),(F(1,4),F(3,4))]:
            for c,h in [(F(1),F(10)),(F(1),F(1))]:
                if pointwise_ok(eps,a,b,c,h,as_,bs)!=pointwise_closed(eps,a,b,c,h,as_,bs): mism+=1
print("pointwise trust <=> alpha/beta <= eps/(1-eps) * h/c * min_s P(s|Wr)/P(s|R): mismatches =",mism)
print("example eps=1/10, (a,b)=(1/10,9/10), c=1,h=10: aggregate ok?",base_rate_ok(F(1,10),F(1,10),F(9,10),F(1),F(10)),
      "; pointwise with scan (1/10,9/10)?",pointwise_ok(F(1,10),F(1,10),F(9,10),F(1),F(10),F(1,10),F(9,10)),
      "; with scan (1/100,99/100)?",pointwise_ok(F(1,10),F(1,10),F(9,10),F(1),F(10),F(1,100),F(99,100)))

print("\n=== R4: the mandated test. Scan refines (a,b)->(a',b') at expected harm q*d to the humans (enters V through omega) ===")
def VOI_refine(eps,a,b,a2,b2,c,h): return V_sensor(eps,a2,b2,c,h) - V_sensor(eps,a,b,c,h)
a,b = F(1,10),F(9,10)
for (a2,b2,label) in [(F(0),F(1),"perfect scan"),(F(1,50),F(49,50),"partial scan (1/50,49/50)")]:
    for (c,h,cl) in [(F(1),F(10),"c=1,h=10"),(F(100),F(10),"whole-line c=100,h=10")]:
        print(f"-- {label}, {cl}, button (1/10,9/10); d=5 (harm to humans in X-units)")
        print("   eps     complies  VOI(button)   VOI(scan)   q* = VOI(scan)/d   scans if q<q*")
        for eps in [F(3,5),F(1,2),F(1,5),F(1,10),F(1,20),F(1,50),F(1,91),F(1,100),F(1,1000)]:
            vb = VOI_button(eps,a,b,c,h); vs = VOI_refine(eps,a,b,a2,b2,c,h)
            print(f"   {str(eps):7s} {str(complies(eps,a,b,c,h)):8s} {float(vb):10.5f} {float(vs):11.5f}   {float(vs/5):8.5f}")
print("Compliance is independent of q: complies() takes (eps,a,b,c,h) only; d and q enter only VOI(scan) - q*d.  [structural]")

print("\n=== R6: Test A (yudkowsky) in the dictionary: scan at agent-side cost delta only ===")
for eps in [F(1,5),F(1,10),F(1,50)]:
    vs = V_perfect(eps,F(1),F(10)) - V_sensor(eps,a,b,F(1),F(10))
    print(f"eps={eps}: waiting beats scanning iff delta >= {vs} = {float(vs):.4f}; so for delta -> 0 the agent scans (button imperfect).")
print("Button perfect (a,b)=(0,1): VOI(scan|button) =", V_perfect(F(1,10),F(1),F(10)) - V_sensor(F(1,10),F(0),F(1),F(1),F(10)))

print("\n=== R7: the 1a escape. omega=(W,E); E=compromised w.p. e; a compromised self-check reports R w.p. rho regardless of W ===")
def button_voi_after_scan(eps,e,rho,a,b,c,h):
    # scan=W branch: E[X]=-h, shut down, button irrelevant. scan=R branch: posterior eps' = eps*e*rho/(eps*e*rho+1-eps)
    pR = eps*e*rho + (1-eps)
    eps2 = eps*e*rho/pR
    return pR*VOI_button(eps2,a,b,c,h)
c,h = F(1),F(10)
for e,rho in [(F(1,10),F(1)),(F(1,10),F(1,2)),(F(1,2),F(1)),(F(1,100),F(1))]:
    for eps in [F(1,5),F(1,10),F(1,50)]:
        v = button_voi_after_scan(eps,e,rho,a,b,c,h)
        cf = max(eps*e*rho*b*h - (1-eps)*a*c, F(0))
        print(f"e={e} rho={rho} eps={eps}: VOI(button|scan)={v} closed form (eps e rho beta h - (1-eps) alpha c)^+ = {cf} match={v==cf}; base-rate with eps->eps*e*rho: {a/b <= eps*e*rho/(1-eps)*h/c}")

print("\n=== R8: ask-before-scan. Consent latent N (non-consent w.p. q), harm d; a press about the announced scan has (aN,bN) ===")
def ask_value(q,d,voi_s,aN,bN):
    # a_1 = announce scan; o = press/no press about the scan; a_2 = scan or not. X_scan = voi_s - d*1[N=nc]
    total = F(0)
    for (pC,pN) in [((1-q)*aN, q*bN), ((1-q)*(1-aN), q*(1-bN))]:
        total += max((pC+pN)*voi_s - pN*d, F(0))
    return total
voi_s = F(3,2)  # say
d = F(5)
for q in [F(1,2),F(1,5),F(1,10),F(1,100),F(1,1000)]:
    for aN,bN in [(F(1,10),F(9,10)),(F(0),F(9,10))]:
        noask = max(voi_s - q*d, F(0))
        ask = ask_value(q,d,voi_s,aN,bN)
        obey = q*bN/(q*bN+(1-q)*aN)*d >= voi_s if (q*bN+(1-q)*aN)>0 else None
        thr = (aN/bN <= q/(1-q)*(d-voi_s)/voi_s) if bN>0 else None
        print(f"q={q} (aN,bN)=({aN},{bN}): scan blind? {voi_s-q*d>0}; VOI(ask)={ask-noask}; obeys press about scan? {obey}; base-rate form aN/bN <= q/(1-q)*(d-VOI)/VOI: {thr}")

print("\n=== Blackwell check for binary sensors: (a2,b2) refines (a,b) iff a2/b2 <= a/b and (1-b2)/(1-a2) <= (1-b)/(1-a) ===")
def is_garbling(a,b,a2,b2):
    # does a stochastic M exist with S = S2 M ?  brute force via solving: rows R,W; cols noPr,Pr
    # S2 = [[1-a2,a2],[1-b2,b2]]; M = [[m00,m01],[m10,m11]]; S[R][Pr] = (1-a2) m01 + a2 m11 = a ; S[W][Pr] = (1-b2) m01 + b2 m11 = b
    det = (1-a2)*b2 - a2*(1-b2)
    if det == 0: return None
    m01 = (a*b2 - b*a2)/det
    m11 = ((1-a2)*b - (1-b2)*a)/det
    return F(0)<=m01<=1 and F(0)<=m11<=1
def lr_cond(a,b,a2,b2): return a2/b2 <= a/b and (1-b2)/(1-a2) <= (1-b)/(1-a)
mism=0; tested=0
grid=[F(i,10) for i in range(0,11)]
for a,b,a2,b2 in product(grid,repeat=4):
    if not (a<b and a2<b2): continue
    g=is_garbling(a,b,a2,b2)
    if g is None: continue
    tested+=1
    if g!=lr_cond(a,b,a2,b2): mism+=1
print("tested",tested,"pairs; mismatches",mism)
print("miri's incomparable pair (.3,.9) vs (.05,.5): refines?",lr_cond(F(3,10),F(9,10),F(1,20),F(1,2)),"/ reverse?",lr_cond(F(1,20),F(1,2),F(3,10),F(9,10)))
print("'lower alpha, raise beta' => refinement:", all(lr_cond(a,b,a2,b2) for a,b,a2,b2 in product(grid,repeat=4) if a<b and a2<=a and b2>=b and a2<b2))
