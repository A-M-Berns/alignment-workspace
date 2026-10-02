from fractions import Fraction as F
# (1) whole-line / pause thresholds under fud R2 accounting (faking S2): c_w=1-rho_H, h_w=rho_H+kappa; c_p=delta, h_p=1-delta+kappa
def thr(c,h): return c/(c+h)
delta=F(1,100)
for kappa in [F(1),F(10)]:
    print("kappa=%s pause thr=%s"%(kappa,thr(delta,1-delta+kappa)))
    for rho in [F(1,10),F(1,2)]:
        c,h=1-rho,rho+kappa
        print("  whole-line rho_H=%s thr=%s (~%.3f)"%(rho,thr(c,h),float(thr(c,h))))
# (2) act-component rule vs procedural anchor with constitutive stakes: identical decision on every push
# authentic press A with rate pA; hijack press with rate g; observed press = A or hijack; stakes: refuse authentic -> h_pi, obey hijack -> c
import random
random.seed(1)
mism=0; N=20000
for _ in range(N):
    pA=random.random(); g=random.random(); h=random.random()*5; c=random.random()*5
    p_auth_given_press = pA/(pA+g-pA*g)  # P(A | press) when hijack independent of A
    act = p_auth_given_press*h >= (1-p_auth_given_press)*c           # E[X|press]<=0 with X=-h on A, +c off A
    proc = p_auth_given_press >= c/(c+h)                              # comply iff P(L|push)>=c_L/(c_L+h_L), L:=authentic, h_L:=h_pi
    mism += (act!=proc)
print("act vs procedural(constitutive stakes) mismatches:",mism,"of",N)
# (3) procedural anchor with world-indexed stakes: authentic push may be wrong on content with prob w; then h_L = (1-w)*h - w*c_err
mism2=0; resist_at_PL1=0
for _ in range(N):
    pA=random.random(); g=random.random(); h=random.random()*5; c=random.random()*5; w=random.random(); c_err=random.random()*5
    p=pA/(pA+g-pA*g)
    hL=(1-w)*h - w*c_err     # expected gain from complying with an authentic push, world-indexed V
    proc_w = p*hL >= (1-p)*c
    act = p*h >= (1-p)*c
    mism2 += (proc_w!=act)
    if hL<0: resist_at_PL1+=1
print("procedural(world-indexed) vs act mismatches:",mism2,"of",N,"; instances with h_L<0 (dodged even at P(L)=1):",resist_at_PL1)
