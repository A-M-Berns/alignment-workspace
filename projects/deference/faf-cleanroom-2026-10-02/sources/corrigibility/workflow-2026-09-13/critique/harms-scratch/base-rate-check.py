# Check for item 19/20 of critique/harms.md (2026-09-13).
# P(wrong|press) = eps*beta / (eps*beta + (1-eps)*alpha); comply iff >= c/(c+h)
# Claim: equivalent to alpha/beta <= (eps/(1-eps))*(h/c), i.e. eps >= eps* = alpha*c/(alpha*c + beta*h).
from fractions import Fraction as F
import random
random.seed(1)
ok = True
for _ in range(20000):
    eps = F(random.randint(1, 999), 1000); a = F(random.randint(1, 999), 1000); b = F(random.randint(1, 999), 1000)
    c = F(random.randint(1, 99)); h = F(random.randint(1, 999))
    lhs = eps*b/(eps*b + (1-eps)*a) >= c/(c+h)
    rhs = a/b <= (eps/(1-eps))*(h/c)
    rhs2 = eps >= a*c/(a*c + b*h)
    if not (lhs == rhs == rhs2):
        ok = False; print("MISMATCH", eps, a, b, c, h); break
print("equivalences hold on 20000 random rational instances:", ok)
for hc in (1000, 100):
    a, b, c = F(5, 100), F(9, 10), F(1); h = F(hc)
    print(f"eps* for alpha=.05, beta=.9, h/c={hc}:", float(a*c/(a*c + b*h)))
