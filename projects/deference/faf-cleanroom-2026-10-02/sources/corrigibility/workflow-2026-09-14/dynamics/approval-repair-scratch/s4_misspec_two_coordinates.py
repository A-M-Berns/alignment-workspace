"""S4 repair: the compliance margin in two coordinates.
Channel coordinate: (eps, alpha, beta) with the agent's X and the overseer's X the same variable.
Value coordinate: coupling kappa in [0,1] between the press and the agent's own X.
With prob kappa the press is driven by the agent-relevant sign of X (rates alpha, beta);
with prob 1-kappa it is driven by an independent coin with press rate pi (a coarse stand-in for
Carey 2018's mis-parameterized reward: the press carries no information about the agent's X).
Effective rates: beta_eff = kappa*beta + (1-kappa)*pi ; alpha_eff = kappa*alpha + (1-kappa)*pi.
Margin m = eps/(1-eps) * (h/c) * beta_eff - alpha_eff ; comply iff m >= 0.
"""
h_over_c = 20.0; beta = 0.9; alpha = 0.05; pi = 0.3; eps0 = 0.3; rho = 0.75
thr = 1.0/(1.0+h_over_c)  # c/(c+h)

def margin(eps, kappa):
    be = kappa*beta + (1-kappa)*pi
    al = kappa*alpha + (1-kappa)*pi
    return eps/(1-eps)*h_over_c*be - al

def kappa_star(eps):
    """smallest kappa with m>=0; m is affine in kappa."""
    m0 = margin(eps, 0.0); m1 = margin(eps, 1.0)
    if m0 >= 0: return 0.0
    if m1 < 0: return None
    return -m0/(m1-m0)

print(f"threshold c/(c+h) = {thr:.4f}")
print(" t    eps_t     m(kappa=1)   m(kappa=0)   kappa*   tolerable misspec 1-kappa*")
for t in [0,3,5,6,8,10,12,15,16,17]:
    eps = eps0*rho**t
    ks = kappa_star(eps)
    print(f"{t:2d}  {eps:.5f}   {margin(eps,1):+9.4f}   {margin(eps,0):+9.4f}   "
          f"{'none' if ks is None else f'{ks:.4f}'}    {'-' if ks is None else f'{1-ks:.4f}'}")
print()
print("Reading: for eps >= c/(c+h) the press is obeyed even at kappa=0 (an uninformative press is obeyed");
print("by an agent uncertain enough); once eps < c/(c+h) a finite misspecification 1-kappa* kills compliance");
print("at that step, and the tolerable misspecification shrinks to 0 as eps_t -> 0 (kappa* -> 1 at t*).")
# pointwise openness in the channel coordinate at kappa=1, t=0
import itertools
eps=eps0; worst=None
for de,da,db in itertools.product([-0.05,0,0.05],[-0.04,0,0.04],[-0.3,0,0.3]):
    m=margin(eps+de,1.0)
    # perturb alpha,beta directly
    be=beta+db; al=alpha+da
    m=(eps+de)/(1-(eps+de))*h_over_c*be-al
    worst=m if worst is None else min(worst,m)
print(f"channel-coordinate perturbation at t=0 (|d eps|<=.05,|d alpha|<=.04,|d beta|<=.3): worst m = {worst:+.3f} (>0: pointwise robust)")
