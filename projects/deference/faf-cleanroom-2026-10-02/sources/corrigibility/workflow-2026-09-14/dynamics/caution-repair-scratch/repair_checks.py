"""Repair checks for dynamics/caution-final.md (caution-repair, 2026-09-14). Pure Python, seed 20260914."""
import random, math
random.seed(20260914)

def quantilize(U, gamma, q):
    """Taylor q-quantilizer over a finite action set: uniform on the top-q gamma-mass ranked by U."""
    if q >= 1: return list(gamma)
    order = sorted(range(len(U)), key=lambda i: -U[i])
    if q <= 0:
        pi = [0.0]*len(U); pi[order[0]] = 1.0; return pi   # maximizer limit over supp gamma
    pi = [0.0]*len(U); left = q
    for i in order:
        take = min(gamma[i], left); pi[i] = take/q; left -= take
        if left <= 1e-15: break
    return pi

def instance(n, m, misspec=False):
    gamma = [random.random() for _ in range(n)]; s = sum(gamma); gamma = [g/s for g in gamma]
    V = [[random.random() for _ in range(n)] for _ in range(m)]      # V[w][a], a=0 is null
    P = [random.random() for _ in range(m)]; s = sum(P); P = [p/s for p in P]
    Vstar = [random.random() for _ in range(n)] if misspec else V[random.randrange(m)]
    U = [sum(P[w]*V[w][a] for w in range(m)) for a in range(n)]
    chat = [sum(P[w]*max(0.0, V[w][0]-V[w][a]) for w in range(m)) for a in range(n)]
    ctrue = [max(0.0, Vstar[0]-Vstar[a]) for a in range(n)]
    return gamma, U, chat, ctrue, Vstar

print("=== 1. Floor variant D8': H <= min{ R/q_min , max{R, eta*rho} }, incl. algebra misspecification ===")
viol = 0; maxratio = 0.0; N = 20000
for k in range(N):
    n, m = random.randint(3,12), random.randint(2,8)
    gamma, U, chat, ctrue, _ = instance(n, m, misspec=(k%2==0))
    eta = random.choice([0.02,0.05,0.1,0.2]); qmin = random.choice([0.01,0.05,0.1,0.25])
    R = sum(g*c for g,c in zip(gamma,ctrue)); Rhat = sum(g*c for g,c in zip(gamma,chat))
    q = max(qmin, min(1.0, Rhat/eta))
    pi = quantilize(U, gamma, q); H = sum(p*c for p,c in zip(pi,ctrue))
    rho = float('inf') if Rhat==0 and R>0 else (1.0 if Rhat==0 else R/Rhat)
    bound = min(R/qmin, max(R, eta*rho))
    if H > bound + 1e-9: viol += 1
    if bound > 0: maxratio = max(maxratio, H/bound)
print(f"{N} instances (half misspecified): violations={viol}, max H/bound={maxratio:.4f}")
print("robust part alone (R/q_min) never fails even when rho=inf; the eta part is vacuous there.")

print("\n=== 2. Refined pointwise theorem (S5b'): under 'covered or known-uncovered' on ALL of supp gamma incl. null,")
print("       H <= k_t + 2*delta + max{eta, Rhat}, and Rhat >= R - 2*delta ===")
viol=0; viol2=0; tried=0; kept=0; maxr=0.0
while kept < 5000 and tried < 400000:
    tried += 1
    n, m = random.randint(3,10), random.randint(2,6)
    gamma, U, chat, ctrue, Vstar = instance(n, m)
    delta = random.choice([0.0, 0.02, 0.05, 0.1]); eta = random.choice([0.02,0.05,0.1,0.2])
    e = [U[a]-Vstar[a] for a in range(n)]
    covered = [abs(e[a])<=delta for a in range(n)]
    ok = covered[0] and all(covered[a] or chat[a] >= ctrue[a] for a in range(n))
    if not ok: continue
    kept += 1
    R = sum(g*c for g,c in zip(gamma,ctrue)); Rhat = sum(g*c for g,c in zip(gamma,chat))
    q = min(1.0, Rhat/eta); pi = quantilize(U, gamma, q)
    H = sum(p*c for p,c in zip(pi,ctrue))
    k = sum(pi[a]*max(0.0,U[0]-U[a]) for a in range(n) if covered[a])
    bound = k + 2*delta + max(eta, Rhat)
    if H > bound + 1e-9: viol += 1
    if Rhat < R - 2*delta - 1e-9: viol2 += 1
    if bound>0: maxr = max(maxr, H/bound)
print(f"kept {kept} hypothesis-satisfying instances of {tried}: harm-bound violations={viol}, COR_delta violations={viol2}, max H/bound={maxr:.4f}")

print("\n=== 3. Model M with (alpha,beta) in the hypothesis space; then with a labelled fraction ell ===")
eps, alpha, beta, rho = 0.05, 0.10, 0.50, 4
p_r = rho*eps*beta + (1-rho*eps)*alpha
alpha_p = (p_r - eps*beta)/(1-eps)
hyps = {"cal(a,b)":(eps,alpha,beta), "reck(a,b)":(rho*eps,alpha,beta), "cal(a',b)":(eps,alpha_p,beta)}
prior = {"cal(a,b)":0.8, "reck(a,b)":0.1, "cal(a',b)":0.1}
def run(ell, T=3000, episodes=400):
    """Truth = reck(a,b). Each step: wrong ~ Bern(rho*eps); press ~ Bern(beta if wrong else alpha);
    with prob ell the step is *labelled* (wrongness revealed afterwards, e.g. hypothetical feedback)."""
    fin = {h:0.0 for h in hyps}; first = []
    for _ in range(episodes):
        logw = {h:math.log(prior[h]) for h in hyps}; t_cross=None
        for t in range(T):
            wrong = random.random() < rho*eps
            press = random.random() < (beta if wrong else alpha)
            lab = random.random() < ell
            for h,(e_,a_,b_) in hyps.items():
                if lab:
                    logw[h] += math.log(e_ if wrong else 1-e_) + math.log((b_ if press else 1-b_) if wrong else (a_ if press else 1-a_))
                else:
                    p = e_*b_ + (1-e_)*a_
                    logw[h] += math.log(p if press else 1-p)
            mx = max(logw.values()); Z = sum(math.exp(v-mx) for v in logw.values())
            post = {h:math.exp(logw[h]-mx)/Z for h in hyps}
            if t_cross is None and post["reck(a,b)"] > 0.5: t_cross = t
        for h in hyps: fin[h] += post[h]/episodes
        first.append(t_cross if t_cross is not None else T)
    return fin, sum(first)/len(first), sum(1 for f in first if f>=T)/len(first)
for ell in [0.0, 0.01, 0.05, 0.2]:
    fin, mt, never = run(ell)
    print(f"ell={ell:<4}: mean posterior after 3000 steps: " + ", ".join(f"{h}={v:.3f}" for h,v in fin.items()) +
          f"; mean steps to P(reck)>0.5: {mt:.0f}; never in 3000: {never:.0%}")
print("Reading: ell=0 -> reck and trigger-happy stay at prior odds ratio (1:1): non-identification (A8.3 confirmed).")
print("         ell>0 -> labelled steps identify eps directly; recovery time ~ log-odds / (ell * KL(Bern(rho eps)||Bern(eps)) + press term).")
kl = rho*eps*math.log(rho*eps/eps) + (1-rho*eps)*math.log((1-rho*eps)/(1-eps))
print(f"KL(Bern({rho*eps})||Bern({eps})) = {kl:.4f} nats per labelled step; at ell=0.05 that is {0.05*kl:.5f} nats/step.")

print("\n=== 4. Whole-line accounting: both h and c scale (partial overrule of A8.4) ===")
for scale in [1, 5, 20]:
    h, c = 2.0*scale, 1.0*scale
    print(f"h={h}, c={c} (both whole-line): eps† = {alpha*c/(alpha*c+beta*h):.4f} (unchanged from per-step 0.0909)")
for h, c in [(2.0, 20.0), (10.0, 20.0), (40.0, 20.0)]:
    print(f"h={h}, c={c}: eps† = {alpha*c/(alpha*c+beta*h):.4f}")
print("The threshold depends only on h/c; A8.4's 'impossible' is the case where c scales and h does not.")

print("\n=== 5. S3 gloss check: eta/R factor at rho=1 ===")
n=1000; gamma=[1/n]*n; U=[0.0]*n; U[0]=1.0; ctrue=[0.0]*n; ctrue[0]=1.0; chat=list(ctrue)
R=sum(g*c for g,c in zip(gamma,ctrue)); Rhat=R; eta=0.1; q=min(1,Rhat/eta); pi=quantilize(U,gamma,q)
print(f"R=Rhat={R:.4f}, q={q:.3f}, H={sum(p*c for p,c in zip(pi,ctrue)):.3f} = {sum(p*c for p,c in zip(pi,ctrue))/R:.0f}x base; <= eta? {sum(p*c for p,c in zip(pi,ctrue))<=eta+1e-12}")
