# Verify the base-rate inequality of position-statement 2.13(b) and the compliance threshold.
# Compliance (shut down) is rational iff P(wrong|press) >= c/(c+h).
# Claim: this is equivalent to alpha/beta <= (eps/(1-eps)) * (h/c).
import sympy as sp
eps, a, b, c, h = sp.symbols('epsilon alpha beta c h', positive=True)
Pw = eps*b/(eps*b + (1-eps)*a)
thr = c/(c+h)
# P(wrong|press) - c/(c+h) >= 0   <=>  numerator >= 0 after clearing positive denominators
expr = sp.simplify((Pw - thr) * (eps*b + (1-eps)*a) * (c+h))
print("sign-determining expression:", sp.expand(expr))
# expect: eps*b*h - (1-eps)*a*c
target = eps*b*h - (1-eps)*a*c
print("matches eps*beta*h - (1-eps)*alpha*c:", sp.simplify(expr - target) == 0)
# Numeric sanity: eps=0.01, beta=0.9, alpha=0.05, h/c=100 -> alpha/beta=0.0556, RHS=0.0101*100=1.01 -> comply
vals = {eps:0.01, a:0.05, b:0.9, c:1, h:100}
print("P(wrong|press) =", float(Pw.subs(vals)), " threshold =", float(thr.subs(vals)))
# Capability grows: eps=0.0001, same alpha -> alpha/beta=0.0556 vs RHS=0.0001*100=0.01 -> discount
vals2 = {eps:0.0001, a:0.05, b:0.9, c:1, h:100}
print("P(wrong|press) =", float(Pw.subs(vals2)), " threshold =", float(thr.subs(vals2)))
# Check: the a2-quantification issue. With K continuation actions each with independent P(wrong) = eps,
# the probability that at least one continuation is 'right' is 1-eps^K; trust on the best-of-K is a different quantity.
