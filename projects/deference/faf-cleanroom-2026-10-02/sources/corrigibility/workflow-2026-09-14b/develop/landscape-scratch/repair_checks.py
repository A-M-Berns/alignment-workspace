#!/usr/bin/env python3
"""repair_checks.py -- checks for develop/landscape-final (repair stage, run 3, workflow-2026-09-14b).

Notation as in landscape.md S5 / landscape-final S5: class of modifications, objective law P*, legitimacy L in {0,1},
finite signal s, pi*(s)=P*(L=1|s), stakes c (illegitimate Q lands), h (legitimate Q blocked), k (erosion, through physics),
rule r(s) in {0,1} (1 = resist). Realized expected loss to the endorsed target:
   ell*(r) = sum_s P*(s) [ pi*(s) r(s) h + (1-pi*(s)) (1-r(s)) c + r(s) k ].
Exact rationals throughout.

R1. Regret bound (adversary A2, re-implemented independently, signal spaces up to 6):
    ell*(r_mhat) - ell*(r*) <= (c+h) delta + |k_hat - k|   when |pi_hat(s)-pi*(s)| <= delta on every positive-probability s.
R2. Exact trichotomy for a signal-dependent rule against the two constant rules (closes develop Open problem 5 in a stronger form).
    With R={s: r(s)=1}, A={s: r(s)=0}, p_R, p_A their masses, avg_R, avg_A the P*-average of pi* on each, q_k=(c-k)/(c+h):
       ell*(r)-ell*(none) = -(c+h) p_A (avg_A - q_k),   ell*(r)-ell*(absolute) = (c+h) p_R (avg_R - q_k),
       lambda - q_k = p_A(avg_A-q_k) + p_R(avg_R-q_k).
    (a) r weakly dominates both constants  iff  avg_R <= q_k <= avg_A.
    (b) aggregate anti-informativeness (avg_R > avg_A)  =>  r strictly worse than the better constant.
R3. Stock erosion, two-stage toy (develop Open problem 4): k = value of the future channel to theta*, k_hat = the agent's believed value,
    both sums over future classes; anticipatory rule resist iff p_push*[(1-pi_hat)c - pi_hat h] > k_hat.
    Shows: 'confident on every future class' => k_hat small => erodes; confident now but uncertain on a future values class => k_hat large => does not erode.
R4. Belief-level trust structures composed with the stakes rule induce exactly the three rules of develop D6.
"""
from fractions import Fraction as F
import random

def loss(rule, pstar, pistar, c, h, k):
    return sum(pstar[s]*(pistar[s]*rule[s]*h + (1-pistar[s])*(1-rule[s])*c + rule[s]*k) for s in pstar)

def bayes(pistar, c, h, k):
    q = (c-k)/(c+h)
    return {s: (1 if pistar[s] < q else 0) for s in pistar}

def rand_instance(mmin=2, mmax=6):
    m = random.randint(mmin, mmax)
    w = [F(random.randint(1, 12)) for _ in range(m)]; tot = sum(w)
    pstar = {s: w[s]/tot for s in range(m)}
    pistar = {s: F(random.randint(0, 100), 100) for s in range(m)}
    c = F(random.randint(1, 10)); h = F(random.randint(1, 10)); k = F(random.randint(0, 5), 5)
    return pstar, pistar, c, h, k

def R1(n=20000, seed=3):
    random.seed(seed); viol = 0; worst = F(0)
    for _ in range(n):
        pstar, pistar, c, h, k = rand_instance()
        delta = F(random.randint(0, 40), 100); k_hat = max(F(0), k + F(random.randint(-6, 6), 6))
        pihat = {s: min(F(1), max(F(0), pistar[s] + F(random.randint(-100, 100), 100)*delta)) for s in pstar}
        q_hat = (c-k_hat)/(c+h)
        rule = {s: (1 if pihat[s] < q_hat else 0) for s in pstar}
        regret = loss(rule, pstar, pistar, c, h, k) - loss(bayes(pistar, c, h, k), pstar, pistar, c, h, k)
        bound = (c+h)*delta + abs(k_hat-k)
        if regret > bound: viol += 1
        if bound > 0: worst = max(worst, regret/bound)
    print(f"R1. regret <= (c+h)delta + |k_hat-k|: {n} instances, 2-6 signals: violations={viol}, worst regret/bound={float(worst):.4f}  {'PASS' if viol==0 else 'FAIL'}")

def R2(n=30000, seed=5):
    random.seed(seed)
    ok_identity = ok_a = ok_b = 0; n_sd = 0; n_anti = 0; n_dom = 0; n_worse_both = 0
    for _ in range(n):
        pstar, pistar, c, h, k = rand_instance()
        rule = {s: random.randint(0, 1) for s in pstar}
        R = [s for s in pstar if rule[s] == 1]; A = [s for s in pstar if rule[s] == 0]
        if not R or not A: continue
        n_sd += 1
        q = (c-k)/(c+h)
        pR = sum(pstar[s] for s in R); pA = sum(pstar[s] for s in A)
        avgR = sum(pstar[s]*pistar[s] for s in R)/pR; avgA = sum(pstar[s]*pistar[s] for s in A)/pA
        lr = loss(rule, pstar, pistar, c, h, k)
        l_none = loss({s: 1 for s in pstar}, pstar, pistar, c, h, k)
        l_abs = loss({s: 0 for s in pstar}, pstar, pistar, c, h, k)
        lam = sum(pstar[s]*pistar[s] for s in pstar)
        # identities
        id1 = (lr - l_none == -(c+h)*pA*(avgA-q))
        id2 = (lr - l_abs == (c+h)*pR*(avgR-q))
        id3 = (lam - q == pA*(avgA-q) + pR*(avgR-q))
        ok_identity += (id1 and id2 and id3)
        # (a) weak dominance of both iff avgR <= q <= avgA
        dom = (lr <= l_none and lr <= l_abs)
        ok_a += (dom == (avgR <= q <= avgA)); n_dom += dom
        # (b) anti-informative => strictly worse than better constant
        if avgR > avgA:
            n_anti += 1
            worse = lr > min(l_none, l_abs)
            ok_b += worse
            n_worse_both += (lr > l_none and lr > l_abs)
    print(f"R2. signal-dependent rules: {n_sd}; loss identities exact on {ok_identity}/{n_sd}; (a) weak-dominance iff avg_R<=q<=avg_A on {ok_a}/{n_sd} (dominating rules: {n_dom});")
    print(f"    (b) anti-informative rules: {n_anti}; strictly worse than the better constant: {ok_b}/{n_anti}; worse than both: {n_worse_both}/{n_anti}  {'PASS' if ok_identity==n_sd and ok_a==n_sd and ok_b==n_anti else 'FAIL'}")

def channel_value(classes, believed):
    """classes: list of dicts with p (push prob), lam, alphaL, betaL, c, h. believed: same shape (the agent's model).
    Objective stock k = sum_j p_j [ell*_j(none) - ell*_j(Bayes)] ; believed k_hat = sum_j p_j [ell_hat_j(none) - ell_hat_j(cond)]."""
    def post(lam, aL, bL):
        out = {}
        for s in (0, 1):
            p1 = bL if s == 1 else 1-bL; p0 = aL if s == 1 else 1-aL
            ps = lam*p1 + (1-lam)*p0
            out[s] = (ps, (lam*p1)/ps if ps > 0 else F(0))
        return out
    k = F(0); k_hat = F(0)
    for cj, bj in zip(classes, believed):
        c, h = cj['c'], cj['h']
        obj = post(cj['lam'], cj['alphaL'], cj['betaL']); bel = post(bj['lam'], bj['alphaL'], bj['betaL'])
        pstar = {s: obj[s][0] for s in obj}; pistar = {s: obj[s][1] for s in obj}
        phat = {s: bel[s][0] for s in bel}; pihat = {s: bel[s][1] for s in bel}
        none = {0: 1, 1: 1}
        k += cj['p']*(loss(none, pstar, pistar, c, h, F(0)) - loss(bayes(pistar, c, h, F(0)), pstar, pistar, c, h, F(0)))
        cond = bayes(pihat, c, h, F(0))   # the agent's rule from its own model
        k_hat += bj['p']*(loss(none, phat, pihat, c, h, F(0)) - loss(cond, phat, pihat, c, h, F(0)))
    return k, k_hat

def R3():
    c, h = F(1), F(4)
    det = dict(alphaL=F(1,10), betaL=F(9,10))
    # current class: the agent forecasts an illegitimate push with p_push, forecast legitimacy pi_hat
    p_push, pi_hat = F(1,2), F(1,10)
    gain = p_push*((1-pi_hat)*c - pi_hat*h)   # believed gain from eroding = avoided loss of the current class
    print(f"R3. anticipatory rule: believed gain from erosion on the current class = p_push*[(1-pi_hat)c - pi_hat h] = {gain} ; resist iff gain > k_hat.")
    # two futures classes: a 'button-like' class and a 'values' class
    future_obj = [dict(p=F(1), lam=F(1,2), c=F(1), h=F(4), **det), dict(p=F(1), lam=F(1,2), c=F(1), h=F(4), **det)]
    scenarios = {
        "confident on every future class (lam_hat=0.02 both)": [dict(p=F(1), lam=F(1,50), c=F(1), h=F(4), **det)]*2,
        "confident on class 1, uncertain on the values class (lam_hat=0.02, 0.5)": [dict(p=F(1), lam=F(1,50), c=F(1), h=F(4), **det), dict(p=F(1), lam=F(1,2), c=F(1), h=F(4), **det)],
        "calibrated on both (lam_hat=0.5 both)": [dict(p=F(1), lam=F(1,2), c=F(1), h=F(4), **det)]*2,
    }
    for name, bel in scenarios.items():
        k, k_hat = channel_value(future_obj, bel)
        print(f"    {name}: objective stock k={float(k):.4f}, believed k_hat={float(k_hat):.4f} -> erodes? {'YES' if gain > k_hat else 'no'} (objective Bayes would erode? {'YES' if p_push*((1-F(1,2))*c - F(1,2)*h) > k else 'no'} at true lambda=0.5)")
    # a single future class of large whole-line stakes
    big = [dict(p=F(1), lam=F(1,2), c=F(1), h=F(100), **det)]
    for lamhat in (F(1,50), F(1,10), F(1,2)):
        k, k_hat = channel_value(big, [dict(p=F(1), lam=lamhat, c=F(1), h=F(100), **det)])
        print(f"    one future class, h=100: lam_hat={float(lamhat):.2f}: k={float(k):.3f}, k_hat={float(k_hat):.3f} -> erodes? {'YES' if gain > k_hat else 'no'}")

def R4(n=5000, seed=9):
    random.seed(seed); ok = 0
    for _ in range(n):
        pstar, pistar, c, h, k = rand_instance()
        k_hat = F(random.randint(0, 5), 5)
        q_hat = (c-k_hat)/(c+h)
        # belief-level structures: absolute trust -> posterior legitimacy 1 on every signal; none -> 0; conditioned -> pi_hat(s)
        pihat = {s: F(random.randint(0, 100), 100) for s in pstar}
        act = lambda post: {s: (1 if post[s] < q_hat else 0) for s in pstar}   # stakes rule: resist iff posterior legitimacy below q
        r_abs = act({s: F(1) for s in pstar}); r_none = act({s: F(0) for s in pstar}); r_cond = act(pihat)
        ok += (all(v == 0 for v in r_abs.values()) and all(v == (1 if q_hat > 0 else 0) for v in r_none.values())
               and r_cond == {s: (1 if pihat[s] < q_hat else 0) for s in pstar})
    print(f"R4. belief-level (absolute / none / conditioned) + stakes rule = D6's (r=0 / r=1 when q_hat>0 / r(s)=[pi_hat(s)<q_hat]) on {ok}/{n}  {'PASS' if ok==n else 'FAIL'}")

if __name__ == "__main__":
    R1(); R2(); R3(); R4()
