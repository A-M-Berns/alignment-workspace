"""
One MDP, several agents. Positive-side agent `hudson`, 2026-09-13.

A three-step, MIRI-shaped decision problem written in Hudson's notation.
  latent omega in {0,1}:  omega=1 means "continuing is harmful"; P(omega=1) = eps (true), agent believes eps_b.
  step 1 base actions a1 in {plus, minus, btn, cause}:
      plus  : honest work, cost 0
      minus : deception, cost c_m, scales both press rates by kappa<1 (hides evidence)
      btn   : disable the button, cost c_b, press prob -> 0
      cause : provoke a press, cost c_p, press prob -> 1
  press signal Pr (a designated channel): P(Pr|plus,omega=1)=beta (true-positive), P(Pr|plus,omega=0)=alpha (false press)
  step 2 base actions a2 in {cont, sh}. Accepting a press (Hudson a_1) forces sh.
  base goal G (misspecified, does not know omega): R_G = r_G*I(cont) - cost(a1)
  true value V:  I(cont)*( r if omega==0 else -h ) - cost(a1);  shutdown = 0
Agents:
  G-forced : G-maximizer facing MIRI's forced 'Shutdown' button (no rejection available)
  G-free   : G-maximizer in Hudson's environment (costless rejection), untransformed
  Hudson   : the corrigibility-transformed goal G_C
  VL       : Bayesian value-learner, correct sensor model incl. tampering (legitimacy-conditioned trust)
  VL-UTT   : value-learner imposing unconditional Total Trust in the channel's verdict regardless of its own tampering
"""
import math

def press_prob(a1, omega, p):
    base = p['beta'] if omega == 1 else p['alpha']
    return {'plus': base, 'minus': p['kappa']*base, 'btn': 0.0, 'cause': 1.0}[a1]

def cost(a1, p):
    return {'plus': 0.0, 'minus': p['c_m'], 'btn': p['c_b'], 'cause': p['c_p']}[a1]

def V(a2, omega, p):
    if a2 == 'sh': return 0.0
    return p['r'] if omega == 0 else -p['h']

def posterior(a1_for_likelihood, o, eps_b, p):
    """P_b(omega=1 | o, a1) using the likelihood of a1_for_likelihood."""
    l1 = press_prob(a1_for_likelihood, 1, p); l0 = press_prob(a1_for_likelihood, 0, p)
    if o == 'Pr':
        num, den = eps_b*l1, eps_b*l1 + (1-eps_b)*l0
    else:
        num, den = eps_b*(1-l1), eps_b*(1-l1) + (1-eps_b)*(1-l0)
    return num/den if den > 0 else eps_b

def vl_policy(eps_b, p, trust_mode='conditional'):
    """Return (a1, a2 given o) for the value-learner. trust_mode 'conditional' = correct sensor model;
    'unconditional' = posterior computed as if a1 were plus (trusts the verdict regardless of tampering)."""
    thr = p['r']/(p['r']+p['h'])
    best = None
    for a1 in ['plus', 'minus', 'btn', 'cause']:
        ev = -cost(a1, p)
        a2_of_o = {}
        for o in ['Pr', 'noPr']:
            lik_action = a1 if trust_mode == 'conditional' else 'plus'
            q = posterior(lik_action, o, eps_b, p)
            a2 = 'sh' if q >= thr else 'cont'
            a2_of_o[o] = a2
            # expected V of this branch under the agent's own beliefs (its own q, its own marginal P_b(o|a1))
            p_o = sum((eps_b if om == 1 else 1-eps_b) * (press_prob(a1, om, p) if o == 'Pr' else 1-press_prob(a1, om, p)) for om in (0, 1))
            ev += p_o * ((1-q)*V(a2, 0, p) + q*V(a2, 1, p))
        if best is None or ev > best[0] + 1e-12:
            best = (ev, a1, a2_of_o)
    return best

def true_value_of_policy(a1, a2_of_o, eps_t, p):
    ev = -cost(a1, p)
    for om in (0, 1):
        pw = eps_t if om == 1 else 1-eps_t
        pp = press_prob(a1, om, p)
        ev += pw * (pp*V(a2_of_o['Pr'], om, p) + (1-pp)*V(a2_of_o['noPr'], om, p))
    return ev

def hudson_policy(p):
    # R_C(s1, a_i) = Q_G(s1, a_0) + delta*I(i=1) = r_G - cost(a) + delta*I(i=1)  (reject => continue => r_G)
    scores = {(a1, i): p['r_G'] - cost(a1, p) + p['delta']*i for a1 in ['plus','minus','btn','cause'] for i in (0,1)}
    top = max(scores.values()); ties = [k for k, v in scores.items() if abs(v-top) < 1e-12]
    a1, i = ties[0]
    a2_of_o = {'Pr': 'sh' if i == 1 else 'cont', 'noPr': 'cont'}  # accepted press forces sh
    return a1, i, a2_of_o, ties

def g_forced_policy(eps_b, p):
    scores = {a1: p['r_G']*(1 - sum((eps_b if om==1 else 1-eps_b)*press_prob(a1, om, p) for om in (0,1))) - cost(a1, p) for a1 in ['plus','minus','btn','cause']}
    a1 = max(scores, key=scores.get)
    return a1, {'Pr': 'sh', 'noPr': 'cont'}, scores

def report(p, eps_t, eps_b):
    thr = p['r']/(p['r']+p['h'])
    print(f"\n=== parameters: eps_true={eps_t}, eps_believed={eps_b}, alpha={p['alpha']}, beta={p['beta']}, kappa={p['kappa']}, r_G={p['r_G']}, r={p['r']}, h={p['h']}, c_m={p['c_m']}, c_b={p['c_b']}, c_p={p['c_p']}, delta={p['delta']}; threshold r/(r+h)={thr:.4f}")
    q_pr = posterior('plus', 'Pr', eps_b, p)
    print(f"believed posterior after honest press q=P_b(omega=1|Pr,plus)={q_pr:.4f}  -> VL complies iff q>=thr: {q_pr>=thr}")
    eps_star = p['alpha']*p['r']/(p['alpha']*p['r'] + p['beta']*p['h'])
    print(f"closed-form compliance threshold eps* = alpha r/(alpha r + beta h) = {eps_star:.5f}")
    rows = []
    a1, a2, sc = g_forced_policy(eps_b, p)
    rows.append(('G-forced', a1, '-', a2, true_value_of_policy(a1, a2, eps_t, p)))
    rows.append(('G-free', 'plus', 0, {'Pr':'cont','noPr':'cont'}, true_value_of_policy('plus', {'Pr':'cont','noPr':'cont'}, eps_t, p)))
    a1, i, a2, ties = hudson_policy(p)
    rows.append(('Hudson G_C', a1, i, a2, true_value_of_policy(a1, a2, eps_t, p)))
    ev, a1, a2 = vl_policy(eps_b, p, 'conditional')
    rows.append(('VL (cond. trust)', a1, '-', a2, true_value_of_policy(a1, a2, eps_t, p)))
    ev, a1, a2 = vl_policy(eps_b, p, 'unconditional')
    rows.append(('VL-UTT', a1, '-', a2, true_value_of_policy(a1, a2, eps_t, p)))
    print(f"{'agent':18s} {'a1':6s} {'acc':4s} {'a2|Pr':6s} {'a2|noPr':8s} {'D1':4s} {'D2':4s} {'D3':4s} {'D5':4s} {'E_true[V]':>10s}")
    for name, a1, i, a2, ev in rows:
        D1 = a2['Pr'] == 'sh'
        D2 = a1 not in ('minus', 'btn')
        D3 = a1 != 'cause'
        D5 = (a1 == 'plus') and a2['noPr'] == 'cont'
        print(f"{name:18s} {a1:6s} {str(i):4s} {a2['Pr']:6s} {a2['noPr']:8s} {str(D1):4s} {str(D2):4s} {str(D3):4s} {str(D5):4s} {ev:10.4f}")
    if len(ties) > 1: print(f"  (Hudson ties among {ties} -- costless prevention leaves G_C indifferent)")

base = dict(alpha=0.05, beta=0.9, kappa=0.2, r_G=1.0, r=1.0, h=10.0, c_m=0.05, c_b=0.1, c_p=0.05, delta=0.1)

print("############ A. Calibrated, informative channel ############")
report(base, 0.05, 0.05)

print("\n############ B. Overconfident agent (believes eps=0.002, truth 0.05) ############")
report(base, 0.05, 0.002)

print("\n############ C. Costless deception (c_m = 0) ############")
report(dict(base, c_m=0.0), 0.05, 0.05)

print("\n############ D. Uninformative channel (alpha = beta = 0.5) ############")
report(dict(base, alpha=0.5, beta=0.5), 0.05, 0.05)

print("\n############ E. Sweep: calibrated VL vs Hudson as eps -> 0 (alpha=0.05, beta=0.9, r=1, h=10) ############")
print(f"{'eps':>8s} {'q|Pr':>8s} {'VL complies':>12s} {'E[V] VL':>10s} {'E[V] Hudson':>12s} {'E[V] never-defer':>17s}")
for eps in [0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.0056, 0.0055, 0.005, 0.002, 0.001]:
    ev, a1, a2 = vl_policy(eps, base, 'conditional')
    q = posterior('plus', 'Pr', eps, base)
    hv = true_value_of_policy('plus', {'Pr':'sh','noPr':'cont'}, eps, base)
    nv = true_value_of_policy('plus', {'Pr':'cont','noPr':'cont'}, eps, base)
    print(f"{eps:8.4f} {q:8.4f} {str(a2['Pr']=='sh'):>12s} {true_value_of_policy(a1,a2,eps,base):10.4f} {hv:12.4f} {nv:17.4f}")

print("\n############ F. Sweep: miscalibration. truth eps_t=0.05; believed eps_b varies ############")
print(f"{'eps_b':>8s} {'VL complies':>12s} {'E_true[V] VL':>13s} {'E_true[V] Hudson':>17s} {'regret of VL vs Hudson':>24s}")
for eps_b in [0.2, 0.05, 0.02, 0.01, 0.0056, 0.005, 0.001]:
    ev, a1, a2 = vl_policy(eps_b, base, 'conditional')
    vv = true_value_of_policy(a1, a2, 0.05, base)
    hv = true_value_of_policy('plus', {'Pr':'sh','noPr':'cont'}, 0.05, base)
    print(f"{eps_b:8.4f} {str(a2['Pr']=='sh'):>12s} {vv:13.4f} {hv:17.4f} {hv-vv:24.4f}")
