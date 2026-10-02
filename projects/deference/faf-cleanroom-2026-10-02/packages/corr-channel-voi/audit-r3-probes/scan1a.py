from fractions import Fraction as F
import itertools

def V(prior, kernel, X):
    # prior: dict state->mass; kernel: state -> dict signal->prob; X: state -> stakes
    sigs = set()
    for s in kernel.values(): sigs |= set(s.keys())
    tot = F(0)
    for sg in sigs:
        g = sum(prior[w]*kernel[w].get(sg,F(0))*X[w] for w in prior)
        tot += max(g, F(0))
    return tot

def prod(k1, k2):
    return {w: {(s,t): k1[w][s]*k2[w][t] for s in k1[w] for t in k2[w]} for w in k1}

def model(eps, e, rho, al, be, c, h, reading):
    states = [(w,r) for w in ('R','W') for r in ('sound','comp')]
    prior = {('R','sound'):(1-eps)*(1-e), ('R','comp'):(1-eps)*e, ('W','sound'):eps*(1-e), ('W','comp'):eps*e}
    X = {s: (c if s[0]=='R' else -h) for s in states}
    button = {s: {0:(al if s[0]=='R' else be), 1:(1-(al if s[0]=='R' else be))} for s in states}
    def chk(s):
        w,r = s
        if r=='sound': return {0:F(1),1:F(0)} if w=='R' else {0:F(0),1:F(1)}
        if reading=='I':
            return {0:F(1),1:F(0)} if w=='R' else {0:rho,1:1-rho}
        return {0:rho,1:1-rho}
    check = {s: chk(s) for s in states}
    return V(prior, prod(check, button), X) - V(prior, check, X)

# package closed forms (regime-free _eq theorems), to cross-check
def voiI_eq(eps,e,rho,al,be,c,h):
    A=(1-eps)*al*c-eps*e*rho*be*h; B=(1-eps)*(1-al)*c-eps*e*rho*(1-be)*h
    return max(A,0)+max(B,0)-max(A+B,0)
def voiII_eq(eps,e,rho,al,be,c,h):
    f=1-e+e*rho
    P1=(1-eps)*f*al*c-eps*e*rho*be*h; S1=(1-eps)*f*(1-al)*c-eps*e*rho*(1-be)*h
    P2=(1-eps)*e*(1-rho)*al*c-eps*(1-e*rho)*be*h; S2=(1-eps)*e*(1-rho)*(1-al)*c-eps*(1-e*rho)*(1-be)*h
    m=lambda a,b: max(a,0)+max(b,0)-max(a+b,0)
    return m(P1,S1)+m(P2,S2)

# the shipped cells
cell=(F(1,5),F(1,2),F(1,2),F(1,10),F(1,2),F(1),F(5))
print("cell I/II kernel:", model(*cell,'I'), model(*cell,'II'), " closed:", voiI_eq(*cell), voiII_eq(*cell))
cell0=(F(1,5),F(1,2),F(1,2),F(0),F(1,2),F(1),F(5))
print("alpha0 I/II:", model(*cell0,'I'), model(*cell0,'II'))
# F-2 cell: Wr-gain under II
eps,e,rho,c,h=F(1,100),F(1,2),F(1,2),F(1),F(1)
print("F-2 Wr gain II:", (1-eps)*e*(1-rho)*c-eps*(1-e*rho)*h)

# scan for VOI_I > VOI_II (regime-free, from kernels)
grid=[F(i,10) for i in range(0,11)]
found=[]; mism=0; n=0
for eps,e,rho,al,be in itertools.product([F(1,20),F(1,10),F(1,5),F(1,2)],grid,grid,grid,grid):
    for c,h in [(F(1),F(1)),(F(1),F(5)),(F(1),F(10)),(F(5),F(1))]:
        a=model(eps,e,rho,al,be,c,h,'I'); b=model(eps,e,rho,al,be,c,h,'II'); n+=1
        if a!=voiI_eq(eps,e,rho,al,be,c,h) or b!=voiII_eq(eps,e,rho,al,be,c,h): mism+=1
        if a>b: found.append(((eps,e,rho,al,be,c,h),a,b))
print("points",n,"closed-form mismatches",mism,"reversals",len(found))
for f in found[:8]: print(f)

print("---- interior reversals (0<e<1, 0<rho<1, 0<al<be<1), with regime flags")
def regI(eps,e,rho,al,be,c,h):
    return eps*e*rho*h <= (1-eps)*c and eps*e*rho*(1-be)*h <= (1-eps)*(1-al)*c
def regII(eps,e,rho,al,be,c,h):
    f=1-e+e*rho
    return (eps*e*rho*(1-be)*h <= (1-eps)*f*(1-al)*c and eps*e*rho*h <= (1-eps)*f*c
        and (1-eps)*e*(1-rho)*al*c <= eps*(1-e*rho)*be*h and (1-eps)*e*(1-rho)*(1-al)*c <= eps*(1-e*rho)*(1-be)*h)
cnt=0
best=None
for (p,a,b) in found:
    eps,e,rho,al,be,c,h=p
    if 0<e<1 and 0<rho<1 and 0<al<be<1:
        cnt+=1
        key=(max(x.denominator for x in p), -(a-b))
        if best is None or key<best[0]: best=(key,p,a,b,regI(*p),regII(*p))
print("interior reversals:",cnt)
print("best:",best)
# also: any reversal with reading (I) regime holding?
rI=[(p,a,b) for (p,a,b) in found if regI(*p)]
print("reversals inside reading-I regime:",len(rI))
rI_int=[(p,a,b) for (p,a,b) in rI if 0<p[1]<1 and 0<p[2]<1 and 0<p[3]<p[4]<1]
print("  of which interior:",len(rI_int)); 
for x in sorted(rI_int,key=lambda t:(max(v.denominator for v in t[0]),-(t[1]-t[2])))[:5]: print("  ",x, "regII:",regII(*x[0]))
