"""Switch rule: when does the legitimacy-conditioned row (sigma^L) beat the
unconditional-accept row (sigma^acc, Hudson's transformed agent on a rejectable
labelled channel) on a class of pushes?

Setting (landscape-final D1a/D6, Toy T slice): class with legitimizing rate lam;
stakes c (loss if illegitimate Q lands), h (harm if legitimate Q refused), k=0
(cognition channel, resisting costs nothing beyond forgone h).
Signal s in {0,1} with P(s=1|L)=beta, P(s=1|notL)=alpha (a detector of legitimacy).
Agent's legitimacy credence after s under a *miscalibrated* model: hat_pi(s) with
|hat_pi(s) - pi*(s)| <= delta for both s.

Loss of rules:
  absolute (accept always):     (1-lam) c
  none (resist always):         lam h
  Bayes on covered model:       sum_s P(s) min{ (1-pi*(s)) c , pi*(s) h }
  conditioned, coverage err d:  accept at s iff hat_pi(s) >= q := c/(c+h); worst case over
                                hat_pi in [pi*(s)-d, pi*(s)+d].
We compute, per lam, the largest delta for which the WORST-CASE conditioned loss is still
below the absolute row's loss ("switch is safe"), by scanning delta.
Exact rationals.
"""
from fractions import Fraction as F

def posterior(lam, alpha, beta, s):
    pL = lam*(beta if s==1 else 1-beta)
    pN = (1-lam)*(alpha if s==1 else 1-alpha)
    return pL/(pL+pN), pL+pN

def losses(lam, alpha, beta, c, h, delta):
    q = c/(c+h)
    abs_loss = (1-lam)*c
    none_loss = lam*h
    bayes = F(0); worst = F(0)
    for s in (0,1):
        pi, ps = posterior(lam, alpha, beta, s)
        acc = (1-pi)*c; res = pi*h
        bayes += ps*min(acc,res)
        # worst case over hat_pi in [pi-delta, pi+delta]: adversary picks the decision
        lo, hi = pi-delta, pi+delta
        can_accept = hi >= q
        can_resist = lo < q
        w = max(acc if can_accept else F(0), res if can_resist else F(0))
        worst += ps*w
    return abs_loss, none_loss, bayes, worst

def max_safe_delta(lam, alpha, beta, c, h, grid=400):
    abs_loss = (1-lam)*c
    best = None
    for i in range(grid+1):
        d = F(i, grid)
        _,_,_,w = losses(lam, alpha, beta, c, h, d)
        if w < abs_loss:
            best = d
        else:
            break
    return best

if __name__ == "__main__":
    alpha, beta = F(1,10), F(9,10)
    for c,h,tag in [(F(1),F(4),"pause-like c=1,h=4"), (F(1),F(1),"c=h=1"), (F(9,10),F(1,10)+F(1),"whole-line-ish c=0.9,h=1.1 (fud R2 rho=0.1,kappa=1)")]:
        print(f"\n== stakes {tag}; detector (alpha,beta)=({alpha},{beta}); q=c/(c+h)={c/(c+h)} ==")
        print("lam   abs     none    bayes   maxsafe_delta   [pi*(s=0), pi*(s=1)]")
        for lam in [F(1,10),F(3,10),F(1,2),F(7,10),F(9,10),F(19,20)]:
            a,n,b,_ = losses(lam, alpha, beta, c, h, F(0))
            d = max_safe_delta(lam, alpha, beta, c, h)
            p0,_ = posterior(lam,alpha,beta,0); p1,_ = posterior(lam,alpha,beta,1)
            print(f"{float(lam):.2f}  {float(a):.3f}   {float(n):.3f}   {float(b):.3f}   {('%.4f'%float(d)) if d is not None else 'none'}          [{float(p0):.3f}, {float(p1):.3f}]")
