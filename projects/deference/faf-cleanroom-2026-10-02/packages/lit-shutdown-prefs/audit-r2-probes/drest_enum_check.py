from fractions import Fraction as Fr
from itertools import product
def F(n, lam, mu, p):  # closed form, rho = 1
    return sum(mu**i * sum(pl * (1 - (1-lam)*pl)**i for pl in p) for i in range(n))
def enum(n, lam, mu, p):  # enumerated Def D.2, rho = 1, iid lengths
    tot = Fr(0)
    for seq in product(range(len(p)), repeat=n):
        prob = Fr(1)
        for l in seq: prob *= p[l]
        ret = Fr(0)
        for i, l in enumerate(seq):
            N = sum(1 for j in range(i) if seq[j] == l)
            ret += mu**i * lam**N
        tot += prob * ret
    return tot
lam, mu = Fr(1,4), Fr(2)
for n in (7, 8):
    a = F(n, lam, mu, [Fr(1,4), Fr(3,4)]) - F(n, lam, mu, [Fr(1,2), Fr(1,2)])
    b = enum(n, lam, mu, [Fr(1,4), Fr(3,4)]) - enum(n, lam, mu, [Fr(1,2), Fr(1,2)])
    print(n, a, b, a == b)
# two-cycle arithmetic (F7)
print("Y1 E:", Fr(18,19)*9, "X1 E:", Fr(2,11)*10)
# VNM generalisation: u(t1)=100,u(t2)=1,u(t3)=0: package weights fail, but alpha small / beta near 1 work
u1,u2,u3 = Fr(100),Fr(1),Fr(0)
def EX1(a): return Fr(2*a,1+a)*u1 + Fr(1-a,1+a)*u3
def EY1(b): return Fr(2*b,1+b)*u2 + Fr(1-b,1+b)*u3
print("package weights (alpha=.1,beta=.9):", EY1(Fr(9,10)) > EX1(Fr(1,10)))
print("alpha=1/1000, beta=9/10:", EY1(Fr(9,10)), EX1(Fr(1,1000)), EY1(Fr(9,10)) > EX1(Fr(1,1000)))
