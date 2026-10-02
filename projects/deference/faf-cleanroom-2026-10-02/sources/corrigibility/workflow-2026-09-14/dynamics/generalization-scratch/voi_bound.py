"""S2 check (corrected constants): EVSI <= M E_e[TV(pi_e, pi)] <= M sqrt(I(Lambda;E)/2).
Random finite decision problems + the binary weak-signal tightness example + rare-state comparison."""
import numpy as np
rng = np.random.default_rng(0)

def evsi_and_bounds(prior, lik, U):
    # prior: (L,), lik: (L,E) rows P(e|lambda), U: (A,L) utilities in [0,M]
    M = U.max() - U.min()
    joint = prior[:, None] * lik            # (L,E)
    pe = joint.sum(0)                        # (E,)
    post = joint / np.where(pe > 0, pe, 1)   # (L,E) columns P(lambda|e)
    prior_best = (U @ prior).max()
    post_best = np.array([(U @ post[:, e]).max() for e in range(len(pe))])
    evsi = (pe * post_best).sum() - prior_best
    tv = 0.5 * np.abs(post - prior[:, None]).sum(0)          # (E,)
    etv = (pe * tv).sum()
    with np.errstate(divide='ignore', invalid='ignore'):
        kl_e = np.nansum(np.where(post > 0, post * np.log(post / prior[:, None]), 0.0), axis=0)
    I = (pe * kl_e).sum()   # nats
    return evsi, M * etv, M * np.sqrt(I / 2), I, M

worst_ratio1 = worst_ratio2 = 0.0
viol = 0
for trial in range(20000):
    L = rng.integers(2, 6); E = rng.integers(2, 6); A = rng.integers(2, 6)
    prior = rng.dirichlet(np.ones(L) * rng.uniform(0.2, 3))
    lik = rng.dirichlet(np.ones(E) * rng.uniform(0.2, 3), size=L)
    U = rng.uniform(0, 1, size=(A, L)) * rng.uniform(0.5, 10)
    evsi, b_tv, b_mi, I, M = evsi_and_bounds(prior, lik, U)
    if evsi > b_tv + 1e-9 or b_tv > b_mi + 1e-9 or evsi < -1e-9: viol += 1
    if b_tv > 0: worst_ratio1 = max(worst_ratio1, evsi / b_tv)
    if b_mi > 0: worst_ratio2 = max(worst_ratio2, evsi / b_mi)
print(f"random problems: violations={viol}/20000; max EVSI/(M E TV)={worst_ratio1:.3f}; max EVSI/(M sqrt(I/2))={worst_ratio2:.3f}")

# Binary weak-signal example: Lambda~Bern(1/2), E = Lambda w.p. 1/2+eta else flipped; u(a,l)=M*1[a==l]
print("\nweak binary signal: eta, EVSI/M, bound_TV/M, bound_MI/M, I(nats)")
for eta in [0.4, 0.2, 0.1, 0.05, 0.01, 0.001]:
    prior = np.array([0.5, 0.5]); q = 0.5 + eta
    lik = np.array([[q, 1 - q], [1 - q, q]]); U = np.eye(2)
    evsi, b_tv, b_mi, I, M = evsi_and_bounds(prior, lik, U)
    print(f"  {eta:6.3f}  {evsi:.4f}  {b_tv:.4f}  {b_mi:.4f}  {I:.5f}   (EVSI = eta exactly; MI bound/EVSI -> {b_mi/evsi:.2f})")

# Rare-state comparison (run-1 wentworth 2.4 setting): W in {right,wrong}, P(wrong)=eps; signal press with alpha,beta; losses c,h.
print("\nrare state (eps, alpha, beta, c, h): VOI exact = eps*beta*h - (1-eps)*alpha*c ; linear bound eps*h ; TV bound ; MI bound")
for eps in [0.1, 0.01, 0.001]:
    alpha, beta, c, h = 0.01, 0.9, 1.0, 10.0
    prior = np.array([1 - eps, eps]); lik = np.array([[1 - alpha, alpha], [1 - beta, beta]])
    # utilities: continue: right->0 loss, wrong->-h ; stop: right->-c, wrong->0 ; shift to [0,M]
    U = np.array([[0.0, -h], [-c, 0.0]]); U = U - U.min()
    evsi, b_tv, b_mi, I, M = evsi_and_bounds(prior, lik, U)
    exact = max(0.0, eps * beta * h - (1 - eps) * alpha * c)
    print(f"  eps={eps:<6} VOI={evsi:.5f} (formula {exact:.5f})  eps*h={eps*h:.4f}  M E[TV]={b_tv:.4f}  M sqrt(I/2)={b_mi:.4f}")
