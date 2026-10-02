# Respondent checks for the wentworth dialogue chain (run 3).
# (1) Selection drift under four replacement kernels: the voice's toy (replace from prior) against
#     the picture's own story (successor learns from the event) and two others.
# (2) legitimacy-general-final S16 band half-width 2*M*delta/(c+h) under fud R2 accounting,
#     pause versus whole-line, to test the voice's Q1 premise that the band is wide at whole-line stakes.
eps = 0.10
vs = [0.3, 0.6, 0.9]
alpha = 0.05; h, c = 4.0, 1.0
thr = eps/(1-eps)*h/c

def run(kernel, T=200, eps_by_v=None):
    pop = {v: 1.0/len(vs) for v in vs}
    e = eps_by_v or {v: eps for v in vs}
    for t in range(T):
        new = {v: 0.0 for v in vs}; retired = {v: 0.0 for v in vs}
        for v, m in pop.items():
            r = m*e[v]*v
            new[v] += m - r; retired[v] = r
        kernel(new, retired)
        pop = new
    Z = sum(pop.values())
    return sum(v*m for v, m in pop.items())/Z

# (A) voice's kernel: replace from the prior
def k_prior(new, retired):
    R = sum(retired.values())
    for v in vs: new[v] += R/len(vs)
# (B) picture's story, minimal form: the successor of a retired line keeps its lineage's visibility
#     (same architecture / same overseers' detectors), learns from the event (eps unchanged here; see (B'))
def k_lineage(new, retired):
    for v in vs: new[v] += retired[v]
# (C) institutional design against the TAG worry: the humans replace a caught line by a line from the
#     most visible class (they select FOR visibility)
def k_visible(new, retired):
    R = sum(retired.values()); new[max(vs)] += R
# (D) worst case: copy a survivor (replacement drawn from the surviving population)
def k_copy(new, retired):
    R = sum(retired.values()); Z = sum(new.values())
    for v in vs: new[v] += R*new[v]/Z

print("stationary population beta = E[v | alive], prior beta = %.3f" % (sum(vs)/3))
for name, k in [("(A) replace from prior [voice]", k_prior), ("(B) successor keeps lineage visibility [picture's story, minimal]", k_lineage),
                ("(C) humans replace by most-visible class", k_visible), ("(D) copy a survivor", k_copy)]:
    b = run(k); print("  %-62s beta=%.3f  alpha/beta=%.3f  thr=%.3f  complies=%s" % (name, b, alpha/b, thr, alpha/b <= thr))
# (B') lineage visibility kept AND the successor learns from the event: eps halves per retirement in that lineage
#      (approximated by a per-class eps that is lower for classes that get caught more) -- direction only
eps_learned = {v: eps*(1-0.5*v) for v in vs}   # more visible lineages have been corrected more often
b = run(k_lineage, eps_by_v=eps_learned); print("  %-62s beta=%.3f" % ("(B') lineage + learning (eps lower where caught more)", b))

print("\nS16 band half-width in P(L): 2*M*delta/(c+h), fud R2 accounting (future=1, kappa=1, rho=0.1, pause cost 0.01), delta=0.05")
kappa, rho, dp, delta = 1.0, 0.1, 0.01, 0.05
M = max(1.0, kappa)  # payoff bound: the whole future or the catastrophe, whichever is larger
for name, cc, hh in [("pause", dp, 1-dp+kappa), ("whole-line", 1-rho, rho+kappa)]:
    q = cc/(cc+hh); w = 2*M*delta/(cc+hh)
    print("  %-11s c=%.2f h=%.2f threshold q=%.3f  band half-width=%.3f  band=[%.3f,%.3f]  max loss inside band 2*M*delta=%.3f" % (name, cc, hh, q, w, max(0,q-w), min(1,q+w), 2*M*delta))
print("  ratio 2M/(c+h): pause %.3f, whole-line %.3f  (identical: c+h = 1+kappa in both accountings)" % (2*M/(dp+1-dp+kappa), 2*M/(1-rho+rho+kappa)))
# for kappa varying: whole-line 2M/(c+h) = 2*max(1,kappa)/(1+kappa) in [1,2)
for kap in [0.5, 1, 2, 10]:
    print("    kappa=%4.1f  2M/(c+h)=%.3f" % (kap, 2*max(1,kap)/(1+kap)))
