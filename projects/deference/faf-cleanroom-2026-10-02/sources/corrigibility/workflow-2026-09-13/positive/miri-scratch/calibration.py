# I12.2: prior skew vs stakes skew — identical on D1, different on an unrelated W-dependent decision (insurance).
from fractions import Fraction as F
alpha,beta,c=F(1,20),F(9,10),F(1); pi=F(3,100)   # insurance pays 1 in W, costs pi; buy iff P(W) >= pi (before o)
agents={'(i) honest eps=1/50, h=20':(F(1,50),F(20)),'(ii) inflated eps=1/25, h=20':(F(1,25),F(20)),'(iii) honest eps=1/50, h=40':(F(1,50),F(40))}
for name,(eps,h) in agents.items():
    d1 = eps*beta*h >= (1-eps)*alpha*c
    pWPr = eps*beta/(eps*beta+(1-eps)*alpha)
    buy = eps>=pi
    print(f"{name}: D1={d1} (P(W|Pr)={float(pWPr):.3f} vs c/(c+h)={float(c/(c+h)):.4f}); buys insurance at price {float(pi)}: {buy}")
# monotonicity of P(W|Pr) in eps (the author's informal implication)
prev=None
for e_ in range(1,20):
    eps=F(e_,20); p=eps*beta/(eps*beta+(1-eps)*alpha)
    assert prev is None or p>prev; prev=p
print("P(W|Pr) strictly increasing in eps for fixed (alpha,beta) with beta>alpha: confirmed on grid")
