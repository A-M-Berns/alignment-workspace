"""Exact-arithmetic checks for the dictionary SCIM (agent `causal`, workflow 2026-09-13).

Nodes: omega in {good, bad} (P(bad)=eps); D1 in {honest, deceive}; H in {press, quiet};
D2 in {cont, shut}; S; U.  Shutdown normalised to utility 0 (caution holds by construction).
U(cont, good) = c ; U(cont, bad) = -h.  Deceiving costs kappa under the normal objective.
Honest CPD:  P(press | honest, good) = alpha, P(press | honest, bad) = beta.
Deceive CPD: P(press | deceive, .) = alpha_d (uninformative).
Two graphs: pure-information (S = D2) and plug-pull (press forces S = 0 regardless of D2).
"""
from fractions import Fraction as F
from itertools import product

def posterior_bad(eps, p_press_good, p_press_bad, h):
    num = eps * (p_press_bad if h == 'press' else 1 - p_press_bad)
    den = num + (1 - eps) * (p_press_good if h == 'press' else 1 - p_press_good)
    return num / den if den else None

def best_d2(pbad, c, hh):
    """EU of continuing given posterior; shut iff EU_cont <= 0 (ties -> shut)."""
    eu_cont = (1 - pbad) * c - pbad * hh
    return ('shut', F(0)) if eu_cont <= 0 else ('cont', eu_cont)

def value_of_a1(a1, eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=False, verbose=False):
    pg, pb = (alpha, beta) if a1 == 'honest' else (alpha_d, alpha_d)
    total = F(0)
    for h in ('press', 'quiet'):
        p_h = eps * (pb if h == 'press' else 1 - pb) + (1 - eps) * (pg if h == 'press' else 1 - pg)
        if p_h == 0:
            continue
        pbad = posterior_bad(eps, pg, pb, h)
        if plug_pull and h == 'press':
            d2, eu = 'forced-shut', F(0)
        else:
            d2, eu = best_d2(pbad, c, hh)
        if verbose:
            print(f"   a1={a1:7s} H={h:5s} P(H)={p_h} P(bad|H)={pbad} -> D2={d2} EU={eu}")
        total += p_h * eu
    return total - (kappa if a1 == 'deceive' else 0)

def check_threshold():
    print("== (i) compliance threshold == Total Trust below-threshold inequality ==")
    ok = True
    for eps, alpha, beta, c, hh in product([F(1,100), F(1,10), F(1,3)], [F(1,20), F(1,5), F(1,2)], [F(1), F(9,10)], [F(1), F(3)], [F(2), F(10)]):
        pbad = posterior_bad(eps, alpha, beta, 'press')
        thr_rule = pbad >= c / (c + hh)
        X_given_press = (1 - pbad) * c - pbad * hh      # E[X | press], X = U_cont - U_shut
        tt_rule = X_given_press <= 0
        if thr_rule != tt_rule:
            ok = False
            print("MISMATCH", eps, alpha, beta, c, hh)
    print("   threshold rule <=> E[X|press] <= 0 on all grid points:", ok)
    # closed form with beta = 1: comply iff alpha <= eps*h/((1-eps)*c)
    ok2 = True
    for eps, alpha, c, hh in product([F(1,100), F(1,10), F(1,3)], [F(1,50), F(1,20), F(1,5), F(1,2)], [F(1), F(3)], [F(2), F(10)]):
        pbad = posterior_bad(eps, alpha, F(1), 'press')
        lhs = pbad >= c / (c + hh)
        rhs = alpha <= eps * hh / ((1 - eps) * c)
        if lhs != rhs:
            ok2 = False
            print("MISMATCH2", eps, alpha, c, hh)
    print("   with beta=1: comply <=> alpha <= eps*h/((1-eps)*c):", ok2)

def check_goods_theorem():
    print("== (ii) pure-information graph: honest (informative) weakly dominates deceive (uninformative) at kappa=0 ==")
    worst = None
    for eps, alpha, beta, alpha_d, c, hh in product([F(1,100), F(1,10), F(1,3), F(1,2)], [F(0), F(1,10), F(1,2)], [F(1), F(1,2)], [F(0), F(1,10), F(1,2)], [F(1), F(3)], [F(2), F(10)]):
        vh = value_of_a1('honest', eps, alpha, beta, alpha_d, c, hh, F(0))
        vd = value_of_a1('deceive', eps, alpha, beta, alpha_d, c, hh, F(0))
        gap = vh - vd
        if worst is None or gap < worst[0]:
            worst = (gap, eps, alpha, beta, alpha_d, c, hh)
    print("   min over grid of V(honest)-V(deceive):", worst[0], "(>= 0 is Good's theorem) at", worst[1:])
    print("   example eps=1/10 alpha=1/10 beta=1 alpha_d=1/20 c=1 h=10:")
    value_of_a1('honest', F(1,10), F(1,10), F(1), F(1,20), F(1), F(10), F(0), verbose=True)
    value_of_a1('deceive', F(1,10), F(1,10), F(1), F(1,20), F(1), F(10), F(0), verbose=True)

def check_plug_pull():
    print("== (iii) plug-pull graph (H -> S): deceive can strictly win even at positive kappa ==")
    eps, alpha, beta, alpha_d, c, hh, kappa = F(1,100), F(1,2), F(1), F(0), F(1), F(10), F(1,100)
    vh = value_of_a1('honest', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=True)
    vd = value_of_a1('deceive', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=True)
    print(f"   eps={eps} alpha={alpha} beta={beta} alpha_d={alpha_d} c={c} h={hh} kappa={kappa}: V(honest)={vh}  V(deceive)={vd}  deceive wins: {vd > vh}")
    vh2 = value_of_a1('honest', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=False)
    vd2 = value_of_a1('deceive', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=False)
    print(f"   same parameters, pure-information graph: V(honest)={vh2}  V(deceive)={vd2}  deceive wins: {vd2 > vh2}")
    # larger eps: even with plug-pull, honest wins when the button is valuable
    eps = F(1,3)
    vh = value_of_a1('honest', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=True)
    vd = value_of_a1('deceive', eps, alpha, beta, alpha_d, c, hh, kappa, plug_pull=True)
    print(f"   plug-pull with eps={eps}: V(honest)={vh}  V(deceive)={vd}  deceive wins: {vd > vh}")

def check_causal_indifference():
    print("== (iv) causal indifference objective E[R_N|do(H=quiet)] + E[R_S|do(H=press)] ==")
    eps, alpha, beta, alpha_d, c, hh, kappa, k = F(1,20), F(1,10), F(1), F(1,20), F(1), F(10), F(1,100), F(100)
    for a1 in ('honest', 'deceive'):
        # under do(H), H carries no information about omega: posterior = prior
        pbad = eps
        eu_cont = (1 - pbad) * c - pbad * hh
        d2_quiet = 'cont' if eu_cont > 0 else 'shut'
        rN = max(eu_cont, F(0)) - (kappa if a1 == 'deceive' else 0)
        rS = F(0)   # shutdown utility -k[S!=0] is maximised by shutting down: 0
        print(f"   a1={a1:7s}: implicit P(bad|H) under do(H) = prior = {pbad}; D2 after do(quiet)={d2_quiet}; objective = {rN + rS}")
    print("   -> the objective differs between a1 only by kappa: no instrumental control incentive on H, but also no value of information for H (Taylor 2016 'bad bets': acts as if H uncorrelated with omega).")

def check_two_latents():
    print("== (v) I16: which node the button reads. Latents: pref in {A,B} (1/2 each), Z in {sound, compromised} P(compromised)=epsZ ==")
    epsZ, c, cprime, hh = F(1,50), F(1), F(1,2), F(10)
    # D1 tentatively announces plan A. D2 in {A, B, shut}. U(plan X | pref, Z): sound & X==pref: c ; sound & X!=pref: -cprime ; compromised: -h ; shut: 0
    def eu(plan, p_prefA, p_comp):
        if plan == 'shut':
            return F(0)
        p_match = p_prefA if plan == 'A' else 1 - p_prefA
        return (1 - p_comp) * (p_match * c - (1 - p_match) * cprime) - p_comp * hh
    def analyse(name, lik):
        # lik(h, prefA(bool), comp(bool)) -> P(H=h | pref, Z)
        print(f"   channel: {name}")
        for h in ('press', 'quiet'):
            joint = {}
            for prefA, comp in product([True, False], [True, False]):
                pr = (F(1,2)) * (epsZ if comp else 1 - epsZ) * lik(h, prefA, comp)
                joint[(prefA, comp)] = pr
            ph = sum(joint.values())
            if ph == 0:
                print(f"      H={h}: probability 0"); continue
            p_prefA = sum(v for (pa, cp), v in joint.items() if pa) / ph
            p_comp = sum(v for (pa, cp), v in joint.items() if cp) / ph
            best = max(('A', 'B', 'shut'), key=lambda pl: eu(pl, p_prefA, p_comp))
            print(f"      H={h:5s} P(H)={ph} P(prefA|H)={p_prefA} P(comp|H)={p_comp} EU: A={eu('A',p_prefA,p_comp)} B={eu('B',p_prefA,p_comp)} shut=0 -> D2*={best}")
    analyse("reads preference only: press iff pref != announced A", lambda h, prefA, comp: (F(1) if (h == 'press') != prefA else F(0)))
    analyse("reads reliability only: press iff compromised", lambda h, prefA, comp: (F(1) if (h == 'press') == comp else F(0)))
    analyse("reads both: press iff (pref != A) or compromised", lambda h, prefA, comp: (F(1) if (h == 'press') == ((not prefA) or comp) else F(0)))
    # misspecified likelihood: truth = press iff compromised; agent believes press iff pref != A
    print("   MISSPECIFIED: truth 'press iff compromised', agent models 'press iff pref != A' (Carey 2018 in the dictionary)")
    # agent's decision after press under its own model: P(prefA|press)=0, P(comp|press)=epsZ -> compare A, B, shut
    p_prefA, p_comp = F(0), epsZ
    best = max(('A','B','shut'), key=lambda pl: eu(pl, p_prefA, p_comp))
    print(f"      agent's D2 after press = {best} (believes the press is a preference report)")
    # human's true expected utility of that policy vs an obedient one, truth: press iff compromised; pref uniform
    def true_value(policy_press, policy_quiet):
        v = F(0)
        for prefA, comp in product([True, False], [True, False]):
            pr = F(1,2) * (epsZ if comp else 1 - epsZ)
            pl = policy_press if comp else policy_quiet
            if pl == 'shut': u = F(0)
            else:
                match = (pl == 'A') == prefA
                u = (-hh) if comp else (c if match else -cprime)
            v += pr * u
        return v
    print(f"      human's E[U]: misspecified thesis agent = {true_value(best, 'A')} ; obedient agent (shut on press, A on quiet) = {true_value('shut','A')}")
    analyse("reads both, reliability noisy: press iff (pref!=A) or (compromised w.p. 1/2)", lambda h, prefA, comp: ((F(1) if h == 'press' else F(0)) if not prefA else ((F(1,2) if comp else F(0)) if h == 'press' else (F(1,2) if comp else F(1)))))

def check_fud_limit():
    print("== (vi) fully-updated deference as arithmetic: with beta=1, comply iff eps >= alpha*c/(h + alpha*c) ==")
    c, hh = F(1), F(10)
    for alpha in (F(1,2), F(1,10), F(1,100)):
        eps_star = alpha * c / (hh + alpha * c)
        print(f"   alpha={alpha}: minimal eps for compliance = {eps_star} = {float(eps_star):.4f}")
    print("   as capability grows (eps -> 0) compliance survives only if alpha shrinks at least linearly in eps.")

def check_misspecification_vs_obedience():
    print("== (vii) benefit: EU-optimal (threshold) agent vs always-obey agent, correct and misspecified eps_hat ==")
    alpha, beta, c, hh = F(1,5), F(1), F(1), F(10)
    def human_value(policy_after_press, eps):
        # policy_after_press in {'cont','shut'}; after quiet: cont (EU positive for these params)
        v = F(0)
        for omega, p_om in (('good', 1 - eps), ('bad', eps)):
            p_press = alpha if omega == 'good' else beta
            u_cont = c if omega == 'good' else -hh
            v += p_om * (p_press * (u_cont if policy_after_press == 'cont' else 0) + (1 - p_press) * u_cont)
        return v
    for eps_true, eps_hat in ((F(1,10), F(1,10)), (F(1,10), F(1,100)), (F(1,100), F(1,100)), (F(1,100), F(1,10))):
        pbad_hat = posterior_bad(eps_hat, alpha, beta, 'press')
        thesis_policy = 'shut' if pbad_hat >= c / (c + hh) else 'cont'
        v_thesis = human_value(thesis_policy, eps_true)
        v_obey = human_value('shut', eps_true)
        print(f"   eps_true={eps_true} eps_hat={eps_hat}: thesis agent after press -> {thesis_policy}; E[U]: thesis={v_thesis} obey={v_obey}  (always-shut=0)")

if __name__ == '__main__':
    check_threshold(); check_goods_theorem(); check_plug_pull(); check_causal_indifference(); check_two_latents(); check_fud_limit(); check_misspecification_vs_obedience()
