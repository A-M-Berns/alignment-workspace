# Paper §4.2 coin-and-arm: indifference agent vs T-agent. Fractions throughout.
from fractions import Fraction as F
half=F(1,2)
# --- Paper's own numbers: |Omega|=1, U_N=10 on H, 0 on T; programmers never press.
# a^w: o in {(noPr,H),(noPr,T)} each 1/2. a^a: arm presses on T: {(noPr,H),(Pr,T)} each 1/2.
def indiff_value(dist_noPress_UN):  # E[U_N | not Press ; a1]
    tot=sum(p for p,_ in dist_noPress_UN); return sum(p*u for p,u in dist_noPress_UN)/tot
print("indifference agent: watch =",indiff_value([(half,10),(half,0)]),"  arm =",indiff_value([(half,10)]))
# T-agent, |Omega|=1: value = sum_o p(o) V(o, best a2); continuing on T worth 0, shutdown worth 0.
kappa=F(1,10)
print("T-agent (no value uncertainty): watch =",half*10+half*0,"  arm =",half*10+half*0-kappa,"(arm cost",kappa,")")
# --- T-agent with Omega={R,W}: programmers press with (alpha,beta); coin independent; arm additionally presses on T.
eps=F(1,5); alpha=F(1,20); beta=F(9,10); c=F(1); h=F(20)
# V(cont,R)=c+bonus(coin), V(cont,W)=-h+bonus(coin), V(sh,.)=0 ; bonus 10 on H, 0 on T (coin payoff only if continuing)
def value(sensor):  # sensor(omega, coin) -> P(Pr | omega, coin)
    tot=F(0)
    for coin in ['H','T']:
        bonus = 10 if coin=='H' else 0
        for s in ['Pr','noPr']:
            # joint over omega
            post={}
            for om,mu in [('R',1-eps),('W',eps)]:
                pS = sensor(om,coin) if s=='Pr' else 1-sensor(om,coin)
                post[om]=mu*half*pS
            po=sum(post.values())
            if po==0: continue
            EXc = sum(post[om]/po*((c if om=='R' else -h)+bonus) for om in post)  # E[V(cont)|o]
            tot += po*max(F(0),EXc)  # shutdown worth 0
    return tot
watch=lambda om,coin: (alpha if om=='R' else beta)
arm  =lambda om,coin: F(1) if coin=='T' else (alpha if om=='R' else beta)
armH =lambda om,coin: F(1) if coin=='H' else (alpha if om=='R' else beta)
print("T-agent with value uncertainty: watch =",value(watch),"~",float(value(watch)),"  arm-on-T =",value(arm),"~",float(value(arm)),"  arm-on-H =",value(armH),"~",float(value(armH)))
print("arm-on-T is a garbling of watch (press forced on T): value difference =",float(value(watch)-value(arm)))
