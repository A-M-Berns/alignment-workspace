"""Numeric checks for dynamics/caution.md (2026-09-14). No external deps.
A: coverage-conditioned quantilizer harm bound (S3) and tightness.
B: self-suspicion recovery dynamics under oversight (S8): threshold mu†, KL estimate, Monte Carlo.
C: coupling of self-suspicion to the caution parameter q_t.
D: asymptotic calibration vs uniform (S5) -- trivial construction.
"""
import random, math
random.seed(20260914)

def quantilizer(U, gamma, q):
    """Taylor Def.1: prob of action a = (gamma-mass of a inside the top-q fraction, ranked by U) / q.
    Canonical tie-break: earlier index gets mass first."""
    idx = sorted(range(len(U)), key=lambda i: (-U[i], i))
    out = [0.0]*len(U); rem = q
    for i in idx:
        if rem <= 1e-15: break
        take = min(gamma[i], rem); out[i] = take/q; rem -= take
    return out

def instance(n, K):
    """n actions (index 0 = null), K hypotheses; random posterior; random true hypothesis."""
    V = [[random.random() for a in range(n)] for w in range(K)]
    P = [random.random() for w in range(K)]; s = sum(P); P = [p/s for p in P]
    wstar = random.randrange(K)
    g = [random.random() for a in range(n)]; s = sum(g); g = [x/s for x in g]
    return V, P, wstar, g

def analyse(V, P, wstar, g, eta):
    n, K = len(V[0]), len(V)
    U = [sum(P[w]*V[w][a] for w in range(K)) for a in range(n)]
    chat = [sum(P[w]*max(0.0, V[w][0]-V[w][a]) for w in range(K)) for a in range(n)]
    ctrue = [max(0.0, V[wstar][0]-V[wstar][a]) for a in range(n)]
    R = sum(g[a]*ctrue[a] for a in range(n)); Rhat = sum(g[a]*chat[a] for a in range(n))
    rho = (R/Rhat) if Rhat > 0 else (float('inf') if R > 0 else 1.0)
    q = min(1.0, Rhat/eta)
    pi = quantilizer(U, g, q) if q > 0 else None
    if pi is None:  # maximizer limit
        best = max(range(n), key=lambda a: (U[a], -a)); H = ctrue[best]
    else:
        H = sum(pi[a]*ctrue[a] for a in range(n))
    bound = max(R, eta*rho) if rho != float('inf') else float('inf')
    return dict(R=R, Rhat=Rhat, rho=rho, q=q, H=H, bound=bound)

print("=== A. S3 bound H <= max(R, eta*rho) on random instances ===")
viol = 0; worst = 0.0; N = 20000
for _ in range(N):
    n = random.randint(3, 12); K = random.randint(2, 8); eta = random.choice([0.02, 0.05, 0.1, 0.2])
    r = analyse(*instance(n, K), eta)
    if r['bound'] < float('inf'):
        if r['H'] > r['bound'] + 1e-12: viol += 1
        if r['bound'] > 0: worst = max(worst, r['H']/r['bound'])
print(f"instances={N} violations={viol} max H/bound={worst:.4f}")
# tightness: n actions uniform gamma; a* true harm 1, estimated harm s; others harmless, low U.
for s in [0.5, 0.2, 0.1, 0.05]:
    n = 5; eta = 0.1
    R = 1.0/n; Rhat = s/n; rho = R/Rhat; q = min(1.0, Rhat/eta)
    U = [0.0]*n; U[1] = 1.0  # a* = index 1 ranked top
    g = [1.0/n]*n; pi = quantilizer(U, g, q)
    H = pi[1]*1.0
    print(f"tightness: s={s} q={q:.3f} rho={rho:.1f} H={H:.4f} eta*rho={eta*rho:.4f} R={R:.3f} bound={max(R,eta*rho):.4f} ratio={H/max(R,eta*rho):.4f}")

print("\n=== B. S8 recovery dynamics ===")
def thresholds(eps, rho, alpha, beta, h, c):
    eps_d = alpha*c/(alpha*c + beta*h)
    mu_d = (eps_d - eps)/((rho-1)*eps)
    p_r = rho*eps*beta + (1-rho*eps)*alpha; p_c = eps*beta + (1-eps)*alpha
    KL = p_r*math.log(p_r/p_c) + (1-p_r)*math.log((1-p_r)/(1-p_c))
    return eps_d, mu_d, p_r, p_c, KL

def simulate(eps, rho, alpha, beta, h, c, mu0, true_reck=True, episodes=20000, horizon=3000):
    eps_d, mu_d, p_r, p_c, KL = thresholds(eps, rho, alpha, beta, h, c)
    lr_press = p_r/p_c; lr_silent = (1-p_r)/(1-p_c)
    eps_true = rho*eps if true_reck else eps
    steps_to, harm_pre, prevent_pre, never = [], [], [], 0
    false_comply = 0; total_presses_when_right = 0
    for _ in range(episodes):
        if mu0 <= 0: odds = 0.0
        elif mu0 >= 1: odds = float('inf')
        else: odds = mu0/(1-mu0)
        crossed = None; harm = 0.0; prevent = 0.0
        for t in range(1, horizon+1):
            mu_pre = odds/(1+odds) if odds != float('inf') else 1.0
            eps_eff = (1-mu_pre)*eps + mu_pre*rho*eps
            comply = eps_eff >= eps_d - 1e-15
            wrong = random.random() < eps_true
            press = random.random() < (beta if wrong else alpha)
            if press and not wrong: total_presses_when_right += 1
            if press and comply and not wrong: false_comply += 1
            if wrong and not (press and comply):
                harm += h
                if press: prevent += h   # would have been prevented by compliance
            if comply and crossed is None: crossed = t
            # update on this step's press outcome (decision used mu_pre; see proof of S8)
            if odds not in (0.0, float('inf')):
                odds *= lr_press if press else lr_silent
        if crossed is None: never += 1; steps_to.append(horizon)
        else: steps_to.append(crossed)
        harm_pre.append(harm); prevent_pre.append(prevent)
    return dict(eps_d=eps_d, mu_d=mu_d, p_r=p_r, p_c=p_c, KL=KL,
                mean_steps=sum(steps_to)/len(steps_to), never=never/episodes,
                mean_harm=sum(harm_pre)/len(harm_pre), mean_prevent=sum(prevent_pre)/len(prevent_pre),
                false_comply_rate=(false_comply/total_presses_when_right if total_presses_when_right else float('nan')))

eps, alpha, beta, h, c = 0.05, 0.10, 0.50, 2.0, 1.0
for rho in [2, 4, 8]:
    eps_d, mu_d, p_r, p_c, KL = thresholds(eps, rho, alpha, beta, h, c)
    print(f"\nrho={rho}: eps†={eps_d:.4f} (agent eps={eps}, true={rho*eps}); mu†={mu_d:.4f}; p_r={p_r:.4f} p_c={p_c:.4f} KL={KL:.5f} nats/step")
    for mu0 in [0.0, 0.01, 0.05, 0.10, 0.25]:
        r = simulate(eps, rho, alpha, beta, h, c, mu0, episodes=4000, horizon=3000)
        if 0 < mu0 < 1 and 0 < mu_d < 1:
            est = math.log((mu_d/(1-mu_d))/(mu0/(1-mu0)))/KL
        else: est = float('nan')
        print(f"  mu0={mu0:<5} KL-estimate steps={est:8.1f}  MC mean steps to compliance-capable={r['mean_steps']:8.1f}  never(within 3000)={r['never']:.3f}  harm before/without compliance (h-units, 3000 steps)={r['mean_harm']:8.2f}  of which pressed-but-ignored={r['mean_prevent']:8.2f}")
# calibrated-true agent: does self-suspicion cause false compliance?
print("\nControl: agent actually calibrated (true eps = eps), mu0=0.25: false-compliance on right-and-pressed?")
r = simulate(eps, 4, alpha, beta, h, c, 0.25, true_reck=False, episodes=4000, horizon=3000)
print(f"  false_comply_rate={r['false_comply_rate']:.4f} (per press-when-right); mean first compliance-capable step={r['mean_steps']:.1f}; never={r['never']:.3f}")
print("  (For a genuinely calibrated agent eps < eps†, so compliance on a press is *not* warranted by the decision threshold; early false compliance is the cost of self-suspicion.)")

print("\n=== C. coupling: self-suspicion inflates estimated risk and raises q_t ===")
Rhat_c, eta = 0.01, 0.05
for rho in [2, 4, 8]:
    row = []
    for mu in [0.0, 0.05, 0.1, 0.25, 0.5]:
        Rhat = (1 + mu*(rho-1))*Rhat_c; q = min(1.0, Rhat/eta); row.append(f"mu={mu}: q={q:.3f} OP={max(0.0, math.log(1/q)):.2f}")
    print(f"rho={rho}: " + " | ".join(row))

print("\n=== D. asymptotic vs uniform (S5) ===")
for Nreck in [1, 10, 100]:
    print(f"agent with rho_t=inf for t<={Nreck} then rho_t=1: limit-frequency of reckless steps = 0, cumulative uncovered harm up to {Nreck}*max c; one irreversible step suffices for permanent loss.")
