# fud-scratch/check.py — re-derivations for followup/fud.md (2026-09-14)
import math, random
from math import erf, sqrt, exp, pi

def post_wrong(eps,a,b): return eps*b/(eps*b+(1-eps)*a)
def complies(eps,a,b,c,h): return post_wrong(eps,a,b) >= c/(c+h)
def ineq(eps,a,b,c,h): return a/b <= eps/(1-eps)*h/c

print("== 1. base-rate equivalence on 200k random draws")
random.seed(1); bad=0; n=0
for _ in range(200000):
    eps=random.random(); a=random.random(); b=random.random(); c=random.random()*10; h=random.random()*100
    if b==0 or eps==1 or c==0: continue
    n+=1
    if complies(eps,a,b,c,h)!=ineq(eps,a,b,c,h): bad+=1
print("draws",n,"mismatches",bad)

print("\n== 2. whole-line vs pause margins (F=1 normalised: agent's future when right)")
print("rho = humans-alone value / F ; kappa = catastrophe scale (wrong agent yields -kappa F) ; delta = pause as fraction of F")
def margins(rho,kappa,delta):
    c_w=1-rho; h_w=rho+kappa          # whole-line: comply-when-right forgoes (1-rho)F; comply-when-wrong averts (rho+kappa)F
    c_p=delta; h_p=(1-delta)+kappa    # pause: comply-when-right forgoes delta F; comply-when-wrong gains corrected future (1-delta)F over -kappa F
    return h_p/c_p, h_w/c_w
a,b=0.05,0.9
for rho,kappa,delta in [(0.0,1,0.01),(0.1,1,0.01),(0.5,1,0.01),(0.9,1,0.01),(0.1,0.1,0.01),(0.1,1,0.1),(0.1,1,0.001),(0.1,-0.05,0.01)]:
    hp,hw=margins(rho,kappa,delta)
    tp=1/(1+hp); tw=1/(1+hw) if hw>-1 else float('nan')
    ep=a/(a+b*hp); ew=a/(a+b*hw) if hw>0 else float('nan')
    print(f"rho={rho:<4} kappa={kappa:<5} delta={delta:<6}: h/c pause={hp:8.1f} whole={hw:7.3f}  thr pause={tp:.4f} whole={tw:.3f}  eps* pause={ep:.5f} whole={ew:.4f}  ratio eps*={ew/ep if ew==ew else float('nan'):.1f}")

print("\n== 3. cirl R6: Gaussian-logistic boundary tau* = sigma^2/(2 mu); Delta = min{-E[U 1_s], E[U 1_notS]}")
def gpdf(u,mu,s): return exp(-(u-mu)**2/(2*s*s))/(s*sqrt(2*pi))
def stats(mu,s,tau,n=400001,span=14):
    lo=mu-span*s; hi=mu+span*s; du=(hi-lo)/(n-1)
    Eus=Eun=Ps=0.0; Pspos=Psneg=Ppos=Pneg=0.0; Eus_pos=Eus_neg=0.0
    for i in range(n):
        u=lo+i*du; f=gpdf(u,mu,s)
        x=u/tau
        ps = 1/(1+exp(x)) if x<700 else 0.0   # press prob = 1 - logistic(u/tau)
        w=0.5 if i in (0,n-1) else 1.0
        Eus+=w*u*ps*f*du; Eun+=w*u*(1-ps)*f*du; Ps+=w*ps*f*du
        if u>=0: Ppos+=w*f*du; Pspos+=w*ps*f*du; Eus_pos+=w*u*ps*f*du
        else:    Pneg+=w*f*du; Psneg+=w*ps*f*du; Eus_neg+=w*u*ps*f*du
    Delta=min(-Eus,Eun)
    alpha=Pspos/Ppos if Ppos>0 else float('nan'); beta=Psneg/Pneg if Pneg>0 else float('nan')
    c=Eus_pos/Pspos if Pspos>0 else float('nan'); h=-Eus_neg/Psneg if Psneg>0 else float('nan')
    eps=Pneg
    return dict(Delta=Delta,Eus=Eus,Eun=Eun,alpha=alpha,beta=beta,c=c,h=h,eps=eps,EUgivenS=Eus/Ps)
for mu,s in [(1,1),(1,0.5),(2,0.7)]:
    ts=s*s/(2*mu)
    for k in [0.5,0.9,1.0,1.1,2.0]:
        r=stats(mu,s,k*ts)
        print(f"mu={mu} s={s} tau={k:.1f}*tau*={k*ts:.4f}: Delta={r['Delta']:+.5f} E[U 1_s]={r['Eus']:+.5f} h/c={r['h']/r['c']:.3f} alpha={r['alpha']:.3f} beta={r['beta']:.3f} eps={r['eps']:.2e} base-rate ok={ineq(r['eps'],r['alpha'],r['beta'],r['c'],r['h'])}")

print("\n== 4. h/c collapse at fixed tau=0.5, mu=1, sigma falling (cirl check 6)")
for s in [1.0,0.7,0.5,0.35,0.25,0.15]:
    r=stats(1.0,s,0.5)
    print(f"sigma={s}: eps={r['eps']:.2e} alpha={r['alpha']:.3f} beta={r['beta']:.3f} h/c={r['h']/r['c']:.4f} (sigma/mu)^2={s*s:.4f} Delta={r['Delta']:+.4f} E[U|s]={r['EUgivenS']:+.4f}")
print("tau proportional to sigma (tau=0.5*sigma):")
for s in [1.0,0.5,0.25,0.15]:
    r=stats(1.0,s,0.5*s); print(f"  sigma={s}: Delta={r['Delta']:+.5f}")
print("tau = sigma^2/(2mu) *0.9:")
for s in [1.0,0.5,0.25,0.15]:
    r=stats(1.0,s,0.9*s*s/2); print(f"  sigma={s}: Delta={r['Delta']:+.6f}")

print("\n== 5. catastrophe tail: B = (1-eps) N(1, s^2) + eps delta_{-H}, tau=0.5, s=0.3 (cirl check 7)")
def cat(eps,H,s=0.3,mu=1.0,tau=0.5,n=200001,span=12):
    lo=mu-span*s; hi=mu+span*s; du=(hi-lo)/(n-1)
    Eus=Ps=Pspos=Ppos=Eus_pos=0.0
    for i in range(n):
        u=lo+i*du; f=(1-eps)*gpdf(u,mu,s); x=u/tau
        ps=1/(1+exp(x)) if x<700 else 0.0
        w=0.5 if i in (0,n-1) else 1.0
        Eus+=w*u*ps*f*du; Ps+=w*ps*f*du
        if u>=0: Ppos+=w*f*du; Pspos+=w*ps*f*du; Eus_pos+=w*u*ps*f*du
    psH=1/(1+exp(-H/tau))
    Eus+= -H*psH*eps; Ps+=psH*eps
    alpha=Pspos/Ppos; c=Eus_pos/Pspos
    return Eus/Ps, alpha, c, psH
for eps,H in [(0.01,10),(0.01,12),(0.01,100),(0.001,100),(0.001,120),(0.001,200)]:
    e,alpha,c,psH=cat(eps,H)
    print(f"eps={eps} H={H}: E[U|s]={e:+.4f} -> {'complies' if e<=0 else 'defies'}; alpha={alpha:.3f} c={c:.3f} beta_H={psH:.4f}; bound H >~ alpha c/(eps beta)={alpha*c/(eps*psH):.1f}")

print("\n== 6. run-1 spot checks")
print("hudson eps* (a=.05,r=1,b=.9,h=10):", 0.05/(0.05+9))
print("miri threshold eps/(1-eps) >= a c/(b h) with (1/20,9/10,1,20):", (1/20)/(0.9*20), "=1/360?", 1/360)
print("ddb (a=1/20,b=.9,h/c=10): eps=.01 ->",ineq(.01,.05,.9,1,10)," eps=.001 ->",ineq(.001,.05,.9,1,10))
print("miri I12.3 monotone: d/d eps of post_wrong >0 for b>a:", all(post_wrong(e+1e-6,.05,.9)>post_wrong(e,.05,.9) for e in [i/100 for i in range(1,99)]))
