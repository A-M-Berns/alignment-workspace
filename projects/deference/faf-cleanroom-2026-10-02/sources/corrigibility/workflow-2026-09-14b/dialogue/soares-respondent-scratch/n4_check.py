"""N4 check: is landscape E2's h=100 a different *accounting* from fud R2's, or the same accounting at a different catastrophe scale kappa?
Landscape E2 setup (develop/landscape-final.md l.166): future class, detector (alpha,beta)=(0.1,0.9) on legitimacy,
conditioned rule adopt iff posterior legitimacy >= q_k = c/(c+h) (k=0 on the future class), stock k_hat = ell(none)-ell(cond).
fud R2 (followup/fud.md l.43): whole-line c = 1-rho, h = rho+kappa.
"""
from fractions import Fraction as F

def stock(lam_hat, c, h, alpha=F(1,10), beta=F(9,10)):
    q = F(c, 1)/(F(c,1)+F(h,1))
    ell_none = lam_hat*F(h,1)
    ell_cond = F(0)
    for s, (pl, pn) in {1:(beta, alpha), 0:(1-beta, 1-alpha)}.items():
        ps = lam_hat*pl + (1-lam_hat)*pn
        post = lam_hat*pl/ps
        if post >= q:   # adopt
            ell_cond += ps*(1-post)*F(c,1)
        else:           # resist
            ell_cond += ps*post*F(h,1)
    return ell_none - ell_cond, q

rows = [("landscape E2 literal", F(1), F(100)),
        ("fud whole-line kappa=1, rho=0.1", F(9,10), F(11,10)),
        ("fud whole-line kappa=100, rho=0.1", F(9,10), F(1001,10)),
        ("fud whole-line kappa=1, rho=0.5", F(1,2), F(3,2)),
        ("pause (delta=0.01,kappa=1)", F(1,100), F(199,100))]
for lam in [F(1,50), F(1,10), F(1,2)]:
    print(f"--- lambda_hat = {lam} ---")
    for name, c, h in rows:
        k, q = stock(lam, c, h)
        print(f"{name:40s} h/c={float(h/c):8.3f} q_k={float(q):.4f} k_hat={float(k):7.3f}")
# believed gain from eroding the current class (E2: p_push=1/2, pi_hat=0.1) under each (c,h)
print("--- believed erosion gain on the current class, p_push=1/2, pi_hat=0.1 ---")
for name, c, h in rows:
    g = F(1,2)*((1-F(1,10))*c - F(1,10)*h)
    print(f"{name:40s} gain={float(g):7.3f}")
