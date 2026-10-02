#!/usr/bin/env python3
"""Newcomb-like problems in the sequential self-game (round 2, thread R2-D / T4a-T4b).

Machine-check of notes/01-interleaving-sketch.md sections 2, 3, 5 in the finite model of
sequential-self-game.md section 1, using sequential_self_game.py as a library (exact Fractions).

Payoffs are normalised so that every path return lies in [0, 1]:
    $1M -> MEG = 1000/1001,  $1K -> KILO = 1/1001,  both -> 1,  nothing -> 0.
Sections:
  (1) opaque Newcomb      : action a_1 in {one, two}, then percept e_1 in {M, 0}      (T = 1)
  (2) transparent Newcomb : dummy action `look`, percept e_0 in {M, 0}, then a_1      (T = 2)
  (3) V_upd (policy-conditioned value), the current-node floor against V_upd^*(root),
      and the policy-level floor; plus an agent-simulating Omega variant of (2).
Run: python3 newcomb_interleaving.py   -> prints the tables and ends with ALL ASSERTIONS PASSED.
"""
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sequential_self_game import Tree, Hyp, Analysis, check_facts, det_policy, pure_policies  # noqa: E402

MEG, KILO = F(1000, 1001), F(1, 1001)
ONE, TWO, M, ZERO = "one", "two", "M", "0"


def payoff(a, content):
    """terminal payoff of action a given box content."""
    box = MEG if content == M else F(0)
    return box + (KILO if a == TWO else F(0))


assert payoff(TWO, M) == 1 and payoff(ONE, M) == MEG and payoff(TWO, ZERO) == KILO and payoff(ONE, ZERO) == 0


def fmt(x):
    return "%s (%.6f)" % (x, float(x))

# ----------------------------------------------------------------------------
# (1) opaque Newcomb: T = 1, root actions {one, two}, percept = revealed content
# ----------------------------------------------------------------------------
ROOT = ()


def opaque_newcomb(q, delta, fracs):
    """fracs = (f1, f2, f3): fractions of delta on T_1 ("Omega-accurate & I one-box"),
    T_2 ("Omega-accurate & I two-box"), T_3 ("random Omega, random me"); f3 may be 0.
    Omega-accurate with accuracy q: under T_1 Omega predicted one-box and put M w.p. q
    *regardless of the action taken* (the content is fixed before the choice); under T_2
    Omega predicted two-box and put 0 w.p. q regardless.  T_i's action kernel is deterministic."""
    q, delta = F(q), F(delta)
    f1, f2, f3 = (F(x) for x in fracs)
    assert f1 + f2 + f3 == 1
    tree = Tree(lambda h: [ONE, TWO] if h == ROOT else [], lambda h, a: [M, ZERO],
                lambda h: payoff(h[0][0], h[0][1]), T=1)
    T1 = Hyp("T1:acc&one", lambda h: {ONE: F(1)}, lambda h, a: {M: q, ZERO: 1 - q})
    T2 = Hyp("T2:acc&two", lambda h: {TWO: F(1)}, lambda h, a: {M: 1 - q, ZERO: q})
    T3 = Hyp("T3:random", lambda h: {ONE: F(1, 2), TWO: F(1, 2)}, lambda h, a: {M: F(1, 2), ZERO: F(1, 2)})
    hyps, wts = [T1, T2, T3], [delta * f1, delta * f2, delta * f3]
    keep = [i for i in range(3) if wts[i] > 0]
    return tree, [hyps[i] for i in keep], [wts[i] for i in keep]


def opaque_report(q, delta, fracs, verbose=True):
    q, delta = F(q), F(delta)
    tree, hyps, wts = opaque_newcomb(q, delta, fracs)
    pis = {"one-box": det_policy({ROOT: ONE}), "two-box": det_policy({ROOT: TWO})}
    ans = {name: Analysis(tree, hyps, wts, delta, pi) for name, pi in pis.items()}
    for an in ans.values():
        check_facts(an)
    a1, a2 = ans["one-box"], ans["two-box"]
    # Q_xi at the root is pi-independent (F1 + fixed kernels): identical under both self-policies
    for a in (ONE, TWO):
        assert a1.Qxi[(ROOT, a)] == a2.Qxi[(ROOT, a)] == a1.Qstar[(ROOT, a)] == a2.Qstar[(ROOT, a)]
        assert a1.envS(ROOT, a) == a2.envS(ROOT, a)
    xiM_one, xiM_two = a1.envS(ROOT, ONE)[M], a1.envS(ROOT, TWO)[M]
    f1, f2, f3 = (F(x) for x in fracs)
    # closed forms of the percept conditionals
    # closed forms: T_3 plays each action w.p. 1/2, so its contribution is weighted by 1/2
    assert xiM_one == (f1 * q + f3 / 4) / (f1 + f3 / 2)
    if f2 + f3 > 0:
        assert xiM_two == (f2 * (1 - q) + f3 / 4) / (f2 + f3 / 2)
    fps = [name for name, an in ans.items() if an.is_fixed_point()]
    Qone, Qtwo = a1.Qxi[(ROOT, ONE)], a1.Qxi[(ROOT, TWO)]
    assert Qone == xiM_one * MEG and Qtwo == xiM_two * 1 + (1 - xiM_two) * KILO
    # fixed points = argmax of the pi-independent Q_xi: unique unless tied
    if Qone != Qtwo:
        assert fps == (["one-box"] if Qone > Qtwo else ["two-box"])
    for name in fps:
        an = ans[name]
        assert an.trust_bound(ROOT) and an.gap(ROOT) == 0 and an.w[ROOT] == 1 - delta
        assert an.M(ROOT) == an.Vstar[ROOT]                      # last level: M = V^*, so TB holds with slack
    if verbose:
        print("  q=%s delta=%s fracs(T1,T2,T3)=%s" % (q, delta, tuple(fracs)))
        print("    xi(M|one-box)=%s  xi(M|two-box)=%s   [pi-independent]" % (fmt(xiM_one), fmt(xiM_two)))
        print("    Q_xi(one)=%s  Q_xi(two)=%s  pi*=%s  V*=%s" % (fmt(Qone), fmt(Qtwo), a1.pistar[ROOT], fmt(a1.Vstar[ROOT])))
        print("    fixed points: %s ; TB at each: %s ; gap at each: %s"
              % (fps, [ans[n].trust_bound(ROOT) for n in fps], [ans[n].gap(ROOT) for n in fps]))
    return dict(xiM_one=xiM_one, xiM_two=xiM_two, Qone=Qone, Qtwo=Qtwo, fps=fps, ans=ans)


def opaque_threshold_check():
    """with T3 absent: one-box iff q*MEG > (1-q) + q*KILO  <=>  q > 1001/2000."""
    qc = F(1001, 2000)
    for q in [F(1, 2), qc, F(1002, 2000), F(9, 10), F(99, 100), F(1)]:
        r = opaque_report(q, F(1, 10), (F(1, 2), F(1, 2), 0), verbose=False)
        if q > qc:
            assert r["fps"] == ["one-box"]
        elif q < qc:
            assert r["fps"] == ["two-box"]
        else:
            assert r["Qone"] == r["Qtwo"] and set(r["fps"]) == {"one-box", "two-box"}
    return qc


def opaque_no_T2_check(q=F(9, 10), delta=F(1, 10)):
    """hypothesis class {T_1, self} only: no non-self hypothesis plays two-box, so xi(.|two-box) is the
    FALLBACK (prior-weighted non-self percept mixture at (root, two)) = T_1's content kernel = M w.p. q:
    the box is 'already full' on the two-box branch and the agent two-boxes."""
    r = opaque_report(q, delta, (1, 0, 0), verbose=False)
    assert r["xiM_two"] == q == r["xiM_one"] and r["fps"] == ["two-box"]
    return r


def section1():
    print("(1) OPAQUE NEWCOMB  (T=1; payoffs MEG=1000/1001, KILO=1/1001)")
    for q, delta, fracs in [(F(1), F(1, 10), (F(1, 2), F(1, 2), 0)), (F(9, 10), F(1, 10), (F(1, 2), F(1, 2), 0)),
                            (F(9, 10), F(1, 100), (F(1, 2), F(1, 2), 0)), (F(9, 10), F(1, 10), (F(1, 3), F(1, 3), F(1, 3))),
                            (F(9, 10), F(1, 10), (F(1, 10), F(1, 10), F(8, 10)))]:
        opaque_report(q, delta, fracs)
    qc = opaque_threshold_check()
    print("  threshold (T3 absent): one-box is the unique fixed point iff q > %s; tie at q = %s (both pure policies are fixed points)" % (qc, qc))
    r = opaque_no_T2_check()
    print("  class {T1, self} only (no two-boxing hypothesis): fallback gives xi(M|two-box)=%s -> unique fixed point %s" % (r["xiM_two"], r["fps"]))
    # mixed self-policies cannot be fixed points off a tie (Q_xi is pi-independent): spot check
    tree, hyps, wts = opaque_newcomb(F(9, 10), F(1, 10), (F(1, 2), F(1, 2), 0))
    for j in [F(1, 4), F(1, 2), F(3, 4)]:
        an = Analysis(tree, hyps, wts, F(1, 10), {ROOT: {ONE: j, TWO: 1 - j}})
        check_facts(an)
        assert not an.is_fixed_point() and an.Qxi[(ROOT, ONE)] == F(9, 10) * MEG
    print("  mixed self-policies (j in {1/4,1/2,3/4}): none is a fixed point; Q_xi unchanged.  [section 1 assertions passed]")



# ----------------------------------------------------------------------------
# (2) transparent Newcomb: T = 2, root action `look`, percept e_0 = visible content, then a_1
# ----------------------------------------------------------------------------
LOOK, DASH = "look", "-"
H_M, H_0 = ((LOOK, M),), ((LOOK, ZERO),)
# the four deterministic policies, written as (action on M, action on 0)
POLICIES = {"UDT": (ONE, TWO), "1box": (ONE, ONE), "2box": (TWO, TWO), "worst": (TWO, ONE)}


def transparent_tree():
    def actions(h):
        return [LOOK] if h == ROOT else ([ONE, TWO] if len(h) == 1 else [])

    def percepts(h, a):
        return [M, ZERO] if h == ROOT else [DASH]

    def reward(h):
        return F(0) if len(h) == 1 else payoff(h[1][0], h[0][1])
    return Tree(actions, percepts, reward, T=2)


def omega_hyp(name, pol, q):
    """T_pol = "Omega-accurate (accuracy q) and I am pol": Omega predicts pol's action on seeing M
    and fills the box accordingly; the action kernel is pol."""
    aM, a0 = pol
    content = {M: q, ZERO: 1 - q} if aM == ONE else {M: 1 - q, ZERO: q}
    return Hyp(name, lambda h: {LOOK: F(1)} if h == ROOT else {(aM if h == H_M else a0): F(1)},
               lambda h, a: dict(content) if h == ROOT else {DASH: F(1)})


def transparent_class(q, delta, fracs):
    """fracs: dict policy-name -> fraction of delta (missing = 0)."""
    q, delta = F(q), F(delta)
    assert sum(F(x) for x in fracs.values()) == 1
    hyps, wts = [], []
    for name, pol in POLICIES.items():
        f = F(fracs.get(name, 0))
        if f > 0:
            hyps.append(omega_hyp("T_" + name, pol, q))
            wts.append(delta * f)
    return transparent_tree(), hyps, wts


def pol_of(pi):
    return (next(a for a, p in pi[H_M].items() if p == 1), next(a for a, p in pi[H_0].items() if p == 1))


def name_of(pol):
    return next(n for n, p in POLICIES.items() if p == pol)


def det_pol(pol):
    return det_policy({ROOT: LOOK, H_M: pol[0], H_0: pol[1]})


def true_value(pol, q):
    """E_{T_pol}[return]: the value of pol against the Omega-accurate universe in which it is the agent."""
    q = F(q)
    pM = q if pol[0] == ONE else 1 - q
    return pM * payoff(pol[0], M) + (1 - pM) * payoff(pol[1], ZERO)


def transparent_report(q, delta, fracs, verbose=True):
    q, delta = F(q), F(delta)
    tree, hyps, wts = transparent_class(q, delta, fracs)
    ans = {name: Analysis(tree, hyps, wts, delta, det_pol(pol)) for name, pol in POLICIES.items()}
    for an in ans.values():
        check_facts(an)
    ref = ans["2box"]
    xiM = ref.envS(ROOT, LOOK)[M]
    # xi(e_0) is the prior-weighted non-self mixture, identical under every self-policy
    pM_closed = sum(F(fracs.get(n, 0)) * (q if POLICIES[n][0] == ONE else 1 - q) for n in POLICIES)
    assert xiM == pM_closed
    for an in ans.values():
        assert an.envS(ROOT, LOOK)[M] == xiM
        for h in (H_M, H_0):
            assert an.w[h] == 1 - delta                                  # F1: seeing e_0 never moves the self-posterior
            for a in (ONE, TWO):
                assert an.Qxi[(h, a)] == an.Qstar[(h, a)] == payoff(a, h[0][1])   # last level: immediate payoff
        assert an.pistar[H_M] == TWO and an.pistar[H_0] == TWO
        assert an.Vstar[ROOT] == xiM * 1 + (1 - xiM) * KILO
    fps = [name for name, an in ans.items() if an.is_fixed_point()]
    assert fps == ["2box"]
    fp = ans["2box"]
    assert fp.gap(ROOT) == 0 and all(fp.trust_bound(h) for h in (ROOT, H_M, H_0))
    assert fp.Vpi[ROOT] == fp.Vstar[ROOT]
    tv = {name: true_value(pol, q) for name, pol in POLICIES.items()}
    # cross-check true values against the solver's hypothesis-internal root values
    for i, hyp in enumerate(hyps):
        assert ref.Qnu[(i, ROOT)] == tv[hyp.name[2:]]
    if verbose:
        print("  q=%s delta=%s fracs=%s" % (q, delta, dict(fracs)))
        print("    xi(M)=%s  [prior-weighted; identical under all four self-policies]" % fmt(xiM))
        print("    pi*_xi: on M -> %s, on 0 -> %s ; V*_xi(root)=%s ; w after seeing M = %s = 1-delta"
              % (fp.pistar[H_M], fp.pistar[H_0], fmt(fp.Vstar[ROOT]), fp.w[H_M]))
        print("    plain fixed points: %s ; V^{pi_S}_xi(root)=%s ; gap=%s ; TB at root/M/0: %s"
              % (fps, fmt(fp.Vpi[ROOT]), fp.gap(ROOT), [fp.trust_bound(h) for h in (ROOT, H_M, H_0)]))
        print("    true value E_{T_pi}[return] of each policy against its own accurate Omega:")
        for name in POLICIES:
            print("      %-6s %s" % (name, fmt(tv[name])))
    return dict(xiM=xiM, ans=ans, fp=fp, tv=tv, hyps=hyps, wts=wts, tree=tree)


BASE = {"UDT": F(1, 2), "2box": F(1, 2)}                                   # the sketch's {T_1, T_2}
FULL = {"UDT": F(1, 4), "1box": F(1, 4), "2box": F(1, 4), "worst": F(1, 4)}  # one hypothesis per policy


def section2():
    print("(2) TRANSPARENT NEWCOMB  (T=2; look, e_0, then one/two)")
    for q, delta, fracs in [(F(1), F(1, 10), BASE), (F(9, 10), F(1, 10), BASE), (F(9, 10), F(1, 100), BASE),
                            (F(9, 10), F(1, 10), FULL), (F(9, 10), F(1, 10), {"UDT": F(1, 100), "2box": F(99, 100)})]:
        transparent_report(q, delta, fracs)
    print("  [section 2 assertions passed]")



# ----------------------------------------------------------------------------
# (3) V_upd, the current-node floor against V_upd^*(root), the policy-level floor,
#     and an agent-simulating Omega
# ----------------------------------------------------------------------------


def hyp_pol(hyp):
    return (next(a for a, p in hyp.act(H_M).items() if p == 1), next(a for a, p in hyp.act(H_0).items() if p == 1))


def V_upd(an, pol, include_self=False):
    """Policy-conditioned value at the root: the prior conditioned on "my policy is pol", i.e. the
    weighted mean of E_T[return] over hypotheses whose action kernel equals pol on {H_M, H_0}.
    include_self: also count the self-hypothesis (weight 1-delta, return V^pi_xi(root)) when the
    agent's own policy pi equals pol (F2: the self-hypothesis is the agent).  None if no mass."""
    num, den = F(0), F(0)
    for i, hyp in enumerate(an.hyps):
        if hyp_pol(hyp) == pol:
            num += an.weights[i] * an.Qnu[(i, ROOT)]
            den += an.weights[i]
    if include_self and pol_of(an.pi) == pol:
        num += (1 - an.delta) * an.Vpi[ROOT]
        den += 1 - an.delta
    return num / den if den > 0 else None


def V_upd_star(an):
    """(value, policy) of the V_upd-optimal policy, non-self hypotheses only; first argmax in POLICIES order."""
    vals = [(V_upd(an, pol), pol) for pol in POLICIES.values() if V_upd(an, pol) is not None]
    best = max(v for v, _ in vals)
    return best, next(pol for v, pol in vals if v == best)


def argmax_policy(an):
    """the EDT-argmax policy of xi (asserting no ties at the decision nodes)."""
    out = {ROOT: LOOK}
    for h in (H_M, H_0):
        am = an.argmax(h)
        assert len(am) == 1, ("tie", h)
        out[h] = am[0]
    return (out[H_M], out[H_0])


def upd_floor_sign(an, h, U):
    d = an.M(h) - an.w[h] * U
    return -1 if d < 0 else (1 if d > 0 else 0)


def is_upd_floored_fixed_point(an, U, pol_star):
    """current-node floor with the constant yardstick U = V_upd^*(root) and reset action pol_star(h)."""
    star = {ROOT: LOOK, H_M: pol_star[0], H_0: pol_star[1]}
    for h in an.tree.nonterminal:
        supp = set(a for a, p in an.pi[h].items() if p > 0)
        sgn = upd_floor_sign(an, h, U)
        ok = {-1: supp == {star[h]}, 1: supp <= set(an.argmax(h)), 0: supp <= set(an.argmax(h)) | {star[h]}}[sgn]
        if not ok:
            return False
    return True


def section3_report(q, delta, fracs, verbose=True):
    q, delta = F(q), F(delta)
    tree, hyps, wts = transparent_class(q, delta, fracs)
    ans = {name: Analysis(tree, hyps, wts, delta, det_pol(pol)) for name, pol in POLICIES.items()}
    ref = ans["2box"]
    # (3a) V_upd for the four policies (non-self only): equals the true value against the policy's own Omega
    vup = {name: V_upd(ref, pol) for name, pol in POLICIES.items()}
    for name, pol in POLICIES.items():
        if vup[name] is not None:
            assert vup[name] == true_value(pol, q)
        for an in ans.values():                              # independent of the agent's policy
            assert V_upd(an, pol) == vup[name]
    Ustar, pol_star = V_upd_star(ref)
    if q > F(1, 2):
        assert pol_star == POLICIES["UDT"] and Ustar == q * MEG + (1 - q) * KILO
    # (3b) V_upd for the agent's own policy with the self-hypothesis included (depends on the fixed point)
    vself = {name: V_upd(an, POLICIES[name], include_self=True) for name, an in ans.items()}
    xiM = ref.envS(ROOT, LOOK)[M]
    assert vself["2box"] == ((1 - delta) * (xiM + (1 - xiM) * KILO) + delta * F(fracs.get("2box", 0)) * true_value(POLICIES["2box"], q)) \
        / ((1 - delta) + delta * F(fracs.get("2box", 0)))
    # (3c) current-node floor against V_upd^*(root): enumerate pure fixed points
    cur_fps = [name for name, an in ans.items() if is_upd_floored_fixed_point(an, Ustar, pol_star)]
    signs = {name: (upd_floor_sign(an, H_M, Ustar), upd_floor_sign(an, H_0, Ustar)) for name, an in ans.items()}
    for an in ans.values():
        assert an.M(H_M) == 1 and an.w[H_M] == 1 - delta        # the floor can never fire at H_M: M(H_M) = 1 >= w U for any U <= 1
        assert upd_floor_sign(an, H_M, Ustar) == 1
    h0_fires = KILO < (1 - delta) * Ustar
    assert all(signs[n][1] == (-1 if h0_fires else 1) for n in ans) or not h0_fires
    assert cur_fps == ["2box"]                                  # unique: two-box on M and on 0
    # (3d) policy-level floor: if V_upd(argmax policy) < w_root V_upd^* play pol_star, else the argmax policy
    pol_fps = {}
    for include_self in (False, True):
        fps = []
        for name, an in ans.items():
            pA = argmax_policy(an)
            assert pA == POLICIES["2box"]                       # pi-independent: last-level Q_xi is the immediate payoff
            vA = V_upd(an, pA, include_self=include_self)
            fires = vA < an.w[ROOT] * Ustar
            prescribed = pol_star if fires else pA
            if pol_of(an.pi) == prescribed:
                fps.append(name)
        pol_fps[include_self] = fps
    assert pol_fps[False] == ["UDT"]
    assert "UDT" in pol_fps[True]
    two_box_self_trap = (vself["2box"] >= (1 - delta) * Ustar)
    assert ("2box" in pol_fps[True]) == two_box_self_trap
    if verbose:
        print("  q=%s delta=%s fracs=%s" % (q, delta, dict(fracs)))
        print("    V_upd (non-self): " + ", ".join("%s=%s" % (n, "undefined" if v is None else fmt(v)) for n, v in vup.items()))
        print("    V_upd^*(root)=%s attained by %s" % (fmt(Ustar), name_of(pol_star)))
        print("    V_upd of the agent's own policy WITH self-mass: " + ", ".join("%s=%s" % (n, fmt(v)) for n, v in vself.items()))
        print("    current-node floor vs V_upd^*: fixed points %s ; floor signs (H_M, H_0) at 2box = %s ; M(H_M)=%s, (1-delta)V_upd^*=%s"
              % (cur_fps, signs["2box"], ans["2box"].M(H_M), fmt((1 - delta) * Ustar)))
        print("    policy-level floor: fixed points without self-mass %s ; with self-mass %s  [2box self-trap: %s]"
              % (pol_fps[False], pol_fps[True], two_box_self_trap))
    return dict(vup=vup, Ustar=Ustar, pol_star=pol_star, vself=vself, cur_fps=cur_fps, pol_fps=pol_fps, xiM=xiM)


def prefix_conditioned_check(q=F(9, 10), delta=F(1, 10), fracs=FULL):
    """The h-conditioned variant V^pol_upd(h) := sum_{T: pol(T)=pol} w(T|h) E_T[return|h] collapses to the
    updateful ranking at H_M: within each policy class only T_pol is consistent with e_0 = M, so
    V^pol_upd(H_M) = payoff(pol(M), M) and the V_upd(H_M)-optimum two-boxes.  (Hence "V_upd^*(root) at every h".)"""
    q, delta = F(q), F(delta)
    tree, hyps, wts = transparent_class(q, delta, fracs)
    an = Analysis(tree, hyps, wts, delta, det_pol(POLICIES["2box"]))
    vals = {}
    for name, pol in POLICIES.items():
        num = den = F(0)
        for i, hyp in enumerate(hyps):
            if hyp_pol(hyp) == pol:
                m = wts[i] * an.nu_joint[(i, H_M)]
                num, den = num + m * an.Qnu[(i, H_M)], den + m
        vals[name] = num / den
        assert vals[name] == payoff(pol[0], M)
    assert max(vals.values()) == 1 == vals["2box"] == vals["worst"] and vals["UDT"] == MEG
    return vals


def self_trap_threshold(q, delta):
    """class {T_UDT (1-f), T_2box (f)}: exact f* such that 2box is a fixed point of the policy-level floor
    WITH self-mass iff f <= f* (the borrowed percept kernel makes the two-boxer expect the money)."""
    q, delta = F(q), F(delta)
    Ustar = q * MEG + (1 - q) * KILO
    tv2 = true_value(POLICIES["2box"], q)

    def g(f):
        xiM = q * (1 - f) + (1 - q) * f
        return (1 - delta) * (xiM + (1 - xiM) * KILO) + delta * f * tv2 - (1 - delta) * Ustar * ((1 - delta) + delta * f)
    fstar = -g(F(0)) / (g(F(1)) - g(F(0)))          # g is affine in f
    assert g(F(1)) < 0 < g(F(0)) and 0 < fstar < 1
    # delta -> 0: the condition becomes xi(M)(1-KILO) + KILO >= q MEG + (1-q) KILO, i.e. f <= q KILO / ((2q-1) MEG)
    flim = q * KILO / ((2 * q - 1) * MEG)
    assert abs(fstar - flim) <= 3 * delta                      # affine in f; the delta-terms are O(delta)
    for f in [fstar / 2, fstar, (fstar + 1) / 2]:
        r = section3_report(q, delta, {"UDT": 1 - f, "2box": f}, verbose=False)
        assert ("2box" in r["pol_fps"][True]) == (f <= fstar)
    return fstar


def simulating_omega_report(q, delta, f1, f2, fO, verbose=True):
    """class {T_UDT (f1), T_2box (f2), T_Omega(pi) (fO), self}: T_Omega(pi) = "Omega-accurate and I am pi_S",
    an agent-tracking hypothesis whose content kernel follows the candidate policy (the rOSI feature the
    finite model lacks).  Fixed point: pi is the argmax under the xi built from {.., T_Omega(pi), self(pi)}."""
    q, delta, f1, f2, fO = (F(x) for x in (q, delta, f1, f2, fO))
    assert f1 + f2 + fO == 1
    tree = transparent_tree()
    fps, out = [], {}
    for name, pol in POLICIES.items():
        hyps = [omega_hyp("T_UDT", POLICIES["UDT"], q), omega_hyp("T_2box", POLICIES["2box"], q), omega_hyp("T_Omega", pol, q)]
        an = Analysis(tree, hyps, [delta * f1, delta * f2, delta * fO], delta, det_pol(pol))
        check_facts(an)
        if an.is_fixed_point():
            fps.append(name)
            out = dict(an=an, xiM=an.envS(ROOT, LOOK)[M], Vstar=an.Vstar[ROOT],
                       wO_M=delta * fO * (1 - q) / an.xi[H_M], wS_M=an.w[H_M])
    assert fps == ["2box"]
    assert out["xiM"] == f1 * q + f2 * (1 - q) + fO * (1 - q)
    assert out["Vstar"] == out["xiM"] + (1 - out["xiM"]) * KILO
    if verbose:
        print("  q=%s delta=%s (f_UDT,f_2box,f_Omega)=%s: fixed point %s ; xi(M)=%s ; V*_xi(root)=%s ; after seeing M: w(T_Omega)=%s, w(self)=%s"
              % (q, delta, (f1, f2, fO), fps, fmt(out["xiM"]), fmt(out["Vstar"]), fmt(out["wO_M"]), out["wS_M"]))
    return out


def section3():
    print("(3) V_upd AND THE TWO FLOORS ON TRANSPARENT NEWCOMB")
    for q, delta, fracs in [(F(1), F(1, 10), BASE), (F(9, 10), F(1, 10), BASE), (F(9, 10), F(1, 10), FULL),
                            (F(9, 10), F(1, 10), {"UDT": F(9, 10), "2box": F(1, 10)})]:
        section3_report(q, delta, fracs)
    for q, delta in [(F(1), F(1, 10)), (F(9, 10), F(1, 10)), (F(9, 10), F(1, 100)), (F(9, 10), F(1, 10 ** 6))]:
        print("  self-trap threshold (class {T_UDT, T_2box}, q=%s, delta=%s): 2box is a with-self policy-floor fixed point iff f_2box <= %s"
              % (q, delta, fmt(self_trap_threshold(q, delta))))
    print("    (delta -> 0 limit of the threshold: q KILO / ((2q-1) MEG) = %s for q=9/10, %s for q=1)" % (fmt(F(9, 8000)), fmt(F(1, 1000))))
    print("  prefix-conditioned V_upd at H_M (collapses to the updateful ranking): %s" % {k: str(v) for k, v in prefix_conditioned_check().items()})
    print("  agent-simulating Omega (the sketch's 'xi($1M) ~ 0 at the two-boxing fixed point'):")
    for fO in [F(0), F(1, 2), F(9, 10), F(99, 100)]:
        simulating_omega_report(F(9, 10), F(1, 10), (1 - fO) / 2, (1 - fO) / 2, fO)
    simulating_omega_report(F(1), F(1, 10), F(1, 200), F(1, 200), F(99, 100))
    print("  [section 3 assertions passed]")


if __name__ == "__main__":
    section1()
    section2()
    section3()
    print("ALL ASSERTIONS PASSED")
