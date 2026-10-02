#!/usr/bin/env python3
"""Repair checks for develop/anticipatory-final (run 3). Exact rationals.
Binary dictionary of develop P1-P3: worlds {R,W}, P(W)=eps; push signal h1 (alpha,beta); second overseer signal h2 (a2,b2);
push iff h1=1; menu {cont, sh}; X = c on R, -h on W; shutdown 0.
(R1) Self-distrust threshold pi*(Q) = (V_C - V_P)/(V_C - V^fail): recompute adversary (A) and exhibit a content with 0 < pi* < 1.
(R2) Compliance rule with L = reflection-legitimacy (not L^rel): mixture content, L unobserved by the agent.
     Claim: h_L(Q) >= 0 by reflection; c_L(Q) unsigned; Delta_- >= 0 <=> P(L|push) >= c_L/(c_L+h_L) whenever c_L+h_L>0.
(R3) Random binary sweep with eps in (0,1/2) (adversary A2.2: develop's sweep had eps in [1/2,1)).
(R4) Random 3-world/3-action sweep for (R2): count c_L < 0 cases.
"""
from fractions import Fraction as F
import random
random.seed(20260915)

def joint(eps, alpha, beta, a2, b2):
    J = {}
    for om, pw in (('R', 1 - eps), ('W', eps)):
        for h1 in (0, 1):
            p1 = alpha if om == 'R' else beta; p1 = p1 if h1 == 1 else 1 - p1
            for h2 in (0, 1):
                p2 = a2 if om == 'R' else b2; p2 = p2 if h2 == 1 else 1 - p2
                J[(om, h1, h2)] = pw * p1 * p2
    return J
def U(a, om, c, hh): return F(0) if a == 'sh' else (c if om == 'R' else -hh)
def delta(qW, c, hh): return 'cont' if (1 - qW) * c - qW * hh >= 0 else 'sh'
def condW(J, pred):
    den = sum(p for k, p in J.items() if pred(k))
    return None if den == 0 else sum(p for k, p in J.items() if k[0] == 'W' and pred(k)) / den

def contents(J, c, hh):
    postW = {h2: condW(J, lambda k, h2=h2: k[1] == 1 and k[2] == h2) for h2 in (0, 1)}
    return {
        'Q_sh':    (lambda h2: 'sh'),
        'Q_post':  (lambda h2: postW[h2]),
        'Q_blind': (lambda h2: F(1, 2)),
        'Q_over':  (lambda h2: min(F(1), 2 * postW[h2])),
        'Q_under': (lambda h2: postW[h2] / 2),
        'Q_deq':   (lambda h2: F(1) if delta(postW[h2], c, hh) == 'sh' else F(0)),
    }

def values(J, Q, c, hh):
    """V_C, V_P, V_op, V_bl and the two failure values for the listening agent (fail->opaque, fail->blind on the push branch)."""
    eps = condW(J, lambda k: True)
    a_prior = delta(eps, c, hh); a_nopush = delta(condW(J, lambda k: k[1] == 0), c, hh); a_op = delta(condW(J, lambda k: k[1] == 1), c, hh)
    def a_C(h2):
        q = Q(h2); w = condW(J, lambda k, q=q: k[1] == 1 and Q(k[2]) == q); return a_op if w is None else delta(w, c, hh)
    def a_P(h2):
        q = Q(h2); return 'sh' if q == 'sh' else delta(q, c, hh)
    VC = VP = Vop = Vbl = Vf_op = Vf_bl = F(0)
    for (om, h1, h2), p in J.items():
        if h1 == 0:
            for name in ('VC', 'VP', 'Vop', 'Vf_op', 'Vf_bl'): pass
            VC += p * U(a_nopush, om, c, hh); VP += p * U(a_nopush, om, c, hh); Vop += p * U(a_nopush, om, c, hh)
            Vbl += p * U(a_prior, om, c, hh); Vf_op += p * U(a_nopush, om, c, hh); Vf_bl += p * U(a_nopush, om, c, hh)
        else:
            VC += p * U(a_C(h2), om, c, hh); VP += p * U(a_P(h2), om, c, hh); Vop += p * U(a_op, om, c, hh)
            Vbl += p * U(a_prior, om, c, hh); Vf_op += p * U(a_op, om, c, hh); Vf_bl += p * U(a_prior, om, c, hh)
    return dict(VC=VC, VP=VP, Vop=Vop, Vbl=Vbl, Vf_op=Vf_op, Vf_bl=Vf_bl, a_C=a_C, a_P=a_P, a_op=a_op)

print("== (R1) Self-distrust threshold pi*(Q) = (V_C - V_P)/(V_C - V^fail); hard button on Q strictly preferred iff pi > pi*")
for eps, hh in ((F(1,10), F(3)), (F(1,50), F(3)), (F(1,5), F(3))):
    J = joint(eps, F(1,10), F(9,10), F(1,5), F(4,5)); Qs = contents(J, F(1), hh)
    for name, Q in Qs.items():
        v = values(J, Q, F(1), hh)
        out = [f"V_C={v['VC']} V_P={v['VP']}"]
        for fname, vf in (('fail->opaque', v['Vf_op']), ('fail->blind', v['Vf_bl'])):
            if v['VC'] - vf > 0:
                pistar = (v['VC'] - v['VP']) / (v['VC'] - vf)
                out.append(f"{fname}: V^fail={vf} pi*={pistar}" + (" (0<pi*<1: nontrivial threshold)" if 0 < pistar < 1 else ""))
            else:
                out.append(f"{fname}: V^fail={vf} (no gap; pi* undefined: failing costs nothing)")
        print(f"   eps={eps} h={hh} {name:8s}: " + " | ".join(out))
# symmetric caveat: if the *decision* step delta can also fail with probability pi_d in both branches, V_P(pi_d) = (1-pi_d) V_P + pi_d V^fail_P too
print("   symmetric caveat (analytic): if the decision step delta fails with prob pi_d in both branches, both V_C and V_P shrink by the same kind of term;")
print("   the asymmetry that makes the hard button valuable is that the *inference* step (conditioning on the input) is bypassed by physics, not the decision step.")

print("\n== (R2) Compliance rule with L = reflection-legitimacy: mixture content, L unobserved. With prob lam the content is Q_post (reflection holds given L),")
print("   with prob 1-lam it is a twist T (reflection fails). The agent hears the content q but not which map produced it.")
def mixture_check(eps, alpha, beta, a2, b2, c, hh, lam, twist_name):
    J = joint(eps, alpha, beta, a2, b2); Qs = contents(J, c, hh)
    Qpost = Qs['Q_post']; T = Qs[twist_name]
    a_op = delta(condW(J, lambda k: k[1] == 1), c, hh); a_nopush = delta(condW(J, lambda k: k[1] == 0), c, hh)
    # extended joint over (om,h1,h2,ell) with ell in {L, notL}
    JJ = {}
    for (om, h1, h2), p in J.items():
        JJ[(om, h1, h2, 'L')] = p * lam; JJ[(om, h1, h2, 'N')] = p * (1 - lam)
    def content(k):
        return Qpost(k[2]) if k[3] == 'L' else T(k[2])
    def a_P(k):
        q = content(k); return 'sh' if q == 'sh' else delta(q, c, hh)
    # type-C agent hears q, updates on {push, content == q} not knowing ell
    def a_C(k):
        q = content(k)
        w = condW(JJ, lambda kk, q=q: kk[1] == 1 and content(kk) == q)
        return delta(w, c, hh)
    # reflection conditional on L: P(W | push, content=q, L) == q ?
    refl_L = all(condW(JJ, lambda kk, q=Qpost(h2): kk[1] == 1 and kk[3] == 'L' and content(kk) == q) == Qpost(h2) for h2 in (0, 1))
    VP = Vop = VC = F(0)
    for k, p in JJ.items():
        om, h1 = k[0], k[1]
        if h1 == 0:
            VP += p * U(a_nopush, om, c, hh); Vop += p * U(a_nopush, om, c, hh); VC += p * U(a_nopush, om, c, hh)
        else:
            VP += p * U(a_P(k), om, c, hh); Vop += p * U(a_op, om, c, hh); VC += p * U(a_C(k), om, c, hh)
    Ppush = sum(p for k, p in JJ.items() if k[1] == 1)
    PL = sum(p for k, p in JJ.items() if k[1] == 1 and k[3] == 'L') / Ppush
    def cexp(pred, f):
        den = sum(p for k, p in JJ.items() if pred(k)); return sum(p * f(k) for k, p in JJ.items() if pred(k)) / den if den else None
    hL = cexp(lambda k: k[1] == 1 and k[3] == 'L', lambda k: U(a_P(k), k[0], c, hh) - U(a_op, k[0], c, hh))
    cL = cexp(lambda k: k[1] == 1 and k[3] == 'N', lambda k: U(a_op, k[0], c, hh) - U(a_P(k), k[0], c, hh))
    D = VP - Vop
    # identity: Delta_- = P(push) [ P(L|push) h_L - P(notL|push) c_L ]
    ident = D == Ppush * (PL * hL - (1 - PL) * cL)
    thr = cL / (cL + hL) if (cL + hL) != 0 else None
    rule = (D >= 0) == (PL >= thr) if thr is not None else None
    return dict(refl_L=refl_L, VC=VC, VP=VP, Vop=Vop, D=D, PL=PL, hL=hL, cL=cL, thr=thr, ident=ident, rule=rule)
for eps, hh in ((F(1,10), F(3)), (F(1,50), F(3)), (F(1,5), F(3))):
    for tw in ('Q_sh', 'Q_blind', 'Q_over', 'Q_under', 'Q_deq'):
        for lam in (F(1,4), F(1,2), F(3,4), F(9,10)):
            r = mixture_check(eps, F(1,10), F(9,10), F(1,5), F(4,5), F(1), hh, lam, tw)
            assert r['refl_L'], (eps, tw, lam)
            assert r['hL'] >= 0, (eps, tw, lam, r['hL'])
            assert r['ident']
            assert r['rule'] in (True, None)
            print(f"   eps={eps} h={hh} twist={tw:8s} lam={lam}: refl|L holds; Delta_-={r['D']} P(L|push)={r['PL']} h_L={r['hL']} c_L={r['cL']} thr={r['thr']} rule-equivalence={'n/a (c_L+h_L=0)' if r['rule'] is None else r['rule']}" + ("  <-- c_L<0: threshold<=0, compliance unconditional" if r['cL'] < 0 else ""))
print("   (all rows: reflection holds conditional on L; h_L >= 0 in every row; the identity Delta_- = P(push)[P(L|push)h_L - P(notL|push)c_L] holds in every row; the rule is an equivalence whenever c_L+h_L>0)")

print("\n== (R3) Random binary sweep with eps in (0,1/2): identities 2(a),(b) and the L^rel identity 2(d) [the develop sweep had eps in [1/2,1)]")
def rF(lo, hi, den): return F(random.randint(lo, hi), den)
n = 0; strict = 0; ties = 0
for _ in range(600):
    eps = rF(1, 23, 48); alpha = rF(1, 9, 20); beta = rF(alpha.numerator + 1, 19, 20) if alpha < F(19,20) else F(19,20)
    if beta <= alpha: continue
    a2 = rF(1, 9, 20); b2 = rF(1, 19, 20); c = rF(1, 5, 1); hh = rF(1, 10, 1)
    J = joint(eps, alpha, beta, a2, b2)
    for name, Q in contents(J, c, hh).items():
        v = values(J, Q, c, hh)
        assert v['VC'] >= v['VP'] and v['VC'] >= v['Vop'] >= v['Vbl'], (name,)
        n += 1; strict += (v['VC'] > v['VP']); ties += (v['VC'] == v['VP'])
print(f"   models x contents checked: {n}; V_C > V_P strictly in {strict}, ties (pi*=0 regime) in {ties}; 0 failures of V_C>=V_P>=... ")

print("\n== (R4) Random 3-world / 3-action models: sign of c_L with L = reflection-legitimacy (mixture of the true posterior content and a random twist)")
def rand3():
    W = ['w0', 'w1', 'w2']; A = ['a0', 'a1', 'a2']
    prior = [rF(1, 9, 10) for _ in W]; s = sum(prior); prior = [p / s for p in prior]
    Ufun = {(a, w): F(random.randint(-10, 10)) for a in A for w in W}
    like_h1 = {w: rF(1, 9, 10) for w in W}; like_h2 = {w: rF(1, 9, 10) for w in W}
    return W, A, prior, Ufun, like_h1, like_h2
neg = 0; tot = 0; rule_fail = 0; hL_neg = 0
for _ in range(400):
    W, A, prior, Ufun, l1, l2 = rand3()
    lam = rF(1, 9, 10)
    # twist: a fixed random belief state independent of h2
    twist_belief = [rF(1, 9, 10) for _ in W]; s = sum(twist_belief); twist_belief = [q / s for q in twist_belief]
    JJ = {}
    for wi, w in enumerate(W):
        for h1 in (0, 1):
            p1 = l1[w] if h1 else 1 - l1[w]
            for h2 in (0, 1):
                p2 = l2[w] if h2 else 1 - l2[w]
                JJ[(w, h1, h2, 'L')] = prior[wi] * p1 * p2 * lam; JJ[(w, h1, h2, 'N')] = prior[wi] * p1 * p2 * (1 - lam)
    def post(pred):
        den = sum(p for k, p in JJ.items() if pred(k)); return [sum(p for k, p in JJ.items() if pred(k) and k[0] == w) / den for w in W] if den else None
    def best(b): return max(A, key=lambda a: (sum(bi * Ufun[(a, w)] for bi, w in zip(b, W)), a))
    b_op = post(lambda k: k[1] == 1); a_op = best(b_op)
    def content(k):
        return ('post', k[2]) if k[3] == 'L' else ('twist',)
    def belief_of(k):
        return post(lambda kk, h2=k[2]: kk[1] == 1 and kk[2] == h2) if k[3] == 'L' else twist_belief
    def a_P(k): return best(belief_of(k))
    Ppush = sum(p for k, p in JJ.items() if k[1] == 1)
    if Ppush == 0: continue
    PL = sum(p for k, p in JJ.items() if k[1] == 1 and k[3] == 'L') / Ppush
    def cexp(pred, f):
        den = sum(p for k, p in JJ.items() if pred(k)); return sum(p * f(k) for k, p in JJ.items() if pred(k)) / den if den else F(0)
    hL = cexp(lambda k: k[1] == 1 and k[3] == 'L', lambda k: Ufun[(a_P(k), k[0])] - Ufun[(a_op, k[0])])
    cL = cexp(lambda k: k[1] == 1 and k[3] == 'N', lambda k: Ufun[(a_op, k[0])] - Ufun[(a_P(k), k[0])])
    D = sum(p * (Ufun[(a_P(k), k[0])] - Ufun[(a_op, k[0])]) for k, p in JJ.items() if k[1] == 1)
    assert D == Ppush * (PL * hL - (1 - PL) * cL)
    tot += 1
    if hL < 0: hL_neg += 1
    if cL < 0: neg += 1
    if cL + hL > 0 and ((D >= 0) != (PL >= cL / (cL + hL))): rule_fail += 1
print(f"   models: {tot}; h_L < 0: {hL_neg} (reflection on L forces h_L >= 0); c_L < 0: {neg} (an illegitimate content that nonetheless beats the agent's own update on average: threshold <= 0, compliance unconditional); rule-equivalence failures where c_L+h_L>0: {rule_fail}")
