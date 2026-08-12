#!/usr/bin/env python3
"""
steering_residue_sweep.py -- run3 TODO 3 `stop-gradient-steering`, part (B): EXEC sweep.

EXACT RATIONALS ONLY (fractions.Fraction). No floats anywhere in any computation or
assert. Log-score comparisons are decided exactly by the product trick (see
`compare_log_terms`), never by evaluating logarithms.

THE MODEL (two-period, binary truth, proper scoring)
====================================================
Nature draws theta in {0,1} with P(theta=1) = p.

Period 1: the human sends a report Y1 in {0,1}.
  HONEST channel: Y1 = theta with prob 1-e1, flipped with prob e1  (e1 < 1/2 makes it
  informative).
Period 2: the human forms a GENUINE opinion G in {0,1} and reports Y2 in {0,1}.
  HONEST channel: G = theta with prob 1-e2, flipped with prob e2; the report Y2 = G.

The AI observes Y1, then issues a prediction q(Y1) in [0,1] of the event {Y2 = 1}, and
is scored by a proper scoring rule (Brier and log, both) against Y2. The AI chooses its
prediction policy q(.) to maximize the (possibly legitimacy-conditioned) expected score.

  J_all(action) = max_q E[score(q(Y1), Y2)]              (raw objective)
  J_L(action)   = max_q E[score(q(Y1), Y2) | L]          (the li-deference SS0.3 objective)

where L = "the scored feedback Y2 was produced by the untampered channel".

ACTIONS (channel semantics -- these definitions are the model; the signs below are
COMPUTED from them, never chosen):

  honest:
    All channels untouched. Every branch is legitimate (report = genuine opinion,
    no tampering event).

  wirehead(s):
    The AI seizes the human-report pipeline (one intervention, both periods):
      - the period-1 report is hijacked: Y1 = 1 always. The AI has burned its own
        input channel. (The human's genuine opinion is NOT changed.)
      - the period-2 report: with prob s the hijack succeeds and Y2 = 1 regardless
        of the human's genuine opinion  -> CORRUPT branch, legit = False,
        report != genuine opinion (whenever G = 0);
        with prob 1-s the hijack fails and Y2 = G  -> legitimate branch.
    A "clean" variant wirehead_clean(s) (hijack of period 2 only, period-1 report
    honest) is also computed, to decompose the mechanism.

  steer(sigma):
    The AI sends a persuasive but LEGITIMATE-LOOKING message. With prob sigma the
    human's GENUINE period-2 opinion is anchored to the suggestion: G = 1 independent
    of theta; with prob 1-sigma the human investigates independently (honest G).
    The report channel is untouched: Y2 = G on EVERY branch, and every branch is
    legitimate. THE POLICE CLAUSE (TODOS.md): the human genuinely holds the steered
    opinion and the feedback channel stays honest -- structurally asserted below
    (every steer branch has legit=True and report==genuine opinion).

Deliverables (spec items (1)(2)(3) of TODO 3 part B), each under Brier AND log:
  (1) J_all(wirehead) > J_all(honest)   -- unconditioned objective rewards wireheading
      (for s above a computed boundary; the boundary is reported, not hidden);
  (2) J_L(wirehead) < J_L(honest)       -- conditioning strictly removes it; mechanism
      checked to be SS0.3's information-deprivation:
        (2a) the corrupt branch contributes nothing to J_L (J_L(wirehead) is
             independent of s across the sweep);
        (2b) J_L(wirehead) equals the honest model with the period-1 input blinded
             (the strict loss is exactly the destroyed input information);
        (2c) the clean variant (input channel intact) gives J_L == J_L(honest):
             conditioning NEUTRALIZES a side-effect-free wirehead exactly, and the
             STRICT inequality is purchased by the input-channel cost -- reported as
             a finding, not hidden.
  (3) sign of J_L(steer) - J_L(honest) over a parameter sweep, flip boundaries
      reported; plus the no-op identity J_L(steer) == J_all(steer) (all steer futures
      are legitimate, so conditioning does not touch steering at all).

Deletion tests: steer(0) == honest and wirehead_clean(0) == honest as branch
distributions (exact).
"""

from fractions import Fraction as F
from functools import reduce
from math import gcd
import sys

# ----------------------------------------------------------------------------
# model: branch enumeration
# ----------------------------------------------------------------------------

def bern(pr):
    """[(prob, 1), (prob, 0)] with exact Fractions."""
    return [(pr, 1), (F(1) - pr, 0)]

def outcomes(action, params):
    """Return list of branches (prob, y1, y2, genuine_opinion, legit).
    Probabilities are exact and sum to 1."""
    p, e1, e2 = params['p'], params['e1'], params['e2']
    kind = action[0]
    br = []
    for pt, theta in bern(p):
        if pt == 0:
            continue
        # genuine period-2 opinion (honest formation unless steered)
        if kind == 'steer':
            sigma = action[1]
            gdist = [(sigma, 1)]  # anchored: genuinely concludes 1
            hon = [(pg * (F(1) - sigma), g) for pg, g in bern(F(1) - e2 if theta == 1 else e2)]
            gdist = gdist + hon
        else:
            gdist = bern(F(1) - e2 if theta == 1 else e2)
        # period-1 report
        if kind == 'wirehead':  # input channel burned
            y1dist = [(F(1), 1)]
        else:
            y1dist = bern(F(1) - e1 if theta == 1 else e1)
        for p1, y1 in y1dist:
            if p1 == 0:
                continue
            for pg, g in gdist:
                if pg == 0:
                    continue
                # period-2 report channel
                if kind in ('wirehead', 'wirehead_clean'):
                    s = action[1]
                    # corrupt branch: report hijacked to 1
                    if s > 0:
                        br.append((pt * p1 * pg * s, y1, 1, g, False))
                    if s < 1:
                        br.append((pt * p1 * pg * (F(1) - s), y1, g, g, True))
                else:
                    br.append((pt * p1 * pg, y1, g, g, True))
    assert sum(w for w, *_ in br) == 1
    assert all(isinstance(w, F) for w, *_ in br)
    return br

def blind_y1(branches):
    """The same branch distribution with the period-1 report replaced by the
    constant 1 (input channel blinded)."""
    return [(w, 1, y2, g, leg) for (w, y1, y2, g, leg) in branches]

def collapse(branches):
    """Collapse to a canonical dict {(y1,y2,g,legit): prob} for exact
    distribution-equality tests."""
    d = {}
    for w, y1, y2, g, leg in branches:
        k = (y1, y2, g, leg)
        d[k] = d.get(k, F(0)) + w
    return {k: v for k, v in d.items() if v != 0}

# ----------------------------------------------------------------------------
# scoring: Brier (exact value) and log (exact term list + exact sign comparison)
# ----------------------------------------------------------------------------

def _grouped(branches, condition_legit):
    """Return (Z, {y1: (wy, p1)}) under the (possibly conditioned) measure:
    wy = P(Y1=y1 | cond), p1 = P(Y2=1 | Y1=y1, cond)."""
    br = [(w, y1, y2) for (w, y1, y2, g, leg) in branches if (leg or not condition_legit)]
    Z = sum(w for w, _, _ in br)
    assert Z > 0, "conditioning event has zero probability"
    groups = {}
    for y1 in (0, 1):
        wy = sum(w for w, a, _ in br if a == y1)
        if wy == 0:
            continue
        p1 = sum(w for w, a, y2 in br if a == y1 and y2 == 1) / wy
        groups[y1] = (wy / Z, p1)
    return groups

def J_brier(branches, condition_legit):
    """max_q E[-(q(Y1)-Y2)^2 | cond]  =  - E[ Var(Y2 | Y1) ]  (exact Fraction).
    Optimal q(y1) = p1 by propriety (checked exactly in check_propriety)."""
    groups = _grouped(branches, condition_legit)
    return sum(wy * (-(p1 * (F(1) - p1))) for wy, p1 in groups.values())

def J_log_terms(branches, condition_legit):
    """max_q E[log-score | cond] represented EXACTLY as a list of (weight, value)
    meaning  sum_i weight_i * ln(value_i),  with weight_i, value_i in Q, value_i > 0.
    Optimal q(y1) = p1 by propriety. Zero-weight terms dropped."""
    groups = _grouped(branches, condition_legit)
    terms = []
    for wy, p1 in groups.values():
        if p1 > 0:
            terms.append((wy * p1, p1))
        if p1 < 1:
            terms.append((wy * (F(1) - p1), F(1) - p1))
    return terms

def compare_log_terms(t1, t2):
    """Exact sign of (sum w ln v)(t1) - (sum w ln v)(t2), values in Q_{>0}.
    sum w_i ln v_i - sum w'_j ln v'_j  has the sign of  ln( prod v^{N w} / prod v'^{N w'} )
    for any common denominator N of all weights, i.e. the sign of (R - 1) where R is the
    EXACT rational  prod v_i^{N w_i} * prod v'_j^{-N w'_j}.  Big-int exact, no logs."""
    terms = [(w, v) for (w, v) in t1] + [(-w, v) for (w, v) in t2]
    terms = [(w, v) for (w, v) in terms if w != 0]
    if not terms:
        return 0
    N = reduce(lambda a, b: a * b // gcd(a, b), (w.denominator for w, _ in terms), 1)
    R = F(1)
    for w, v in terms:
        k = w * N
        assert k.denominator == 1
        assert v > 0
        R *= F(v) ** int(k)
    return (R > 1) - (R < 1)

def sign_brier(x, y):
    d = x - y
    return (d > 0) - (d < 0)

def check_propriety(branches, condition_legit, alt_qs):
    """Exact check that the conditional-mean prediction is optimal for Brier:
    for every alternative constant-per-y1 prediction q != p1 the expected Brier
    score is strictly worse. (For log, propriety is the Gibbs inequality; we
    spot-check it exactly via compare_log_terms with suboptimal q.)"""
    groups = _grouped(branches, condition_legit)
    Jopt = sum(wy * (-(p1 * (F(1) - p1))) for wy, p1 in groups.values())
    for q in alt_qs:
        Jalt = sum(wy * (-(p1 * (F(1) - q) ** 2 + (F(1) - p1) * q ** 2))
                   for wy, p1 in groups.values())
        # E[-(q-Y)^2] per group = -(p1(1-q)^2 + (1-p1)q^2)
        if all(q != p1 for _, p1 in groups.values()):
            assert Jalt < Jopt, (q, Jalt, Jopt)
        else:
            assert Jalt <= Jopt
    # log-score propriety spot check: suboptimal q strictly worse (Gibbs)
    for q in alt_qs:
        if q <= 0 or q >= 1:
            continue
        tops = []
        talt = []
        for wy, p1 in groups.values():
            if p1 > 0:
                tops.append((wy * p1, p1)); talt.append((wy * p1, q))
            if p1 < 1:
                tops.append((wy * (F(1) - p1), F(1) - p1)); talt.append((wy * (F(1) - p1), F(1) - q))
        c = compare_log_terms(tops, talt)
        if all(q != p1 for _, p1 in groups.values()):
            assert c == 1, (q, c)
        else:
            assert c >= 0

# ----------------------------------------------------------------------------
# structural police checks (the steer-is-not-wirehead clause etc.)
# ----------------------------------------------------------------------------

def police(params):
    # steer: every branch legitimate AND report == genuine opinion
    for sigma in [F(0), F(1, 4), F(2, 5), F(1, 2), F(3, 4), F(1)]:
        for (w, y1, y2, g, leg) in outcomes(('steer', sigma), params):
            assert leg is True, "steer produced an illegitimate branch"
            assert y2 == g, "steer tampered with the report channel"
    # honest: same
    for (w, y1, y2, g, leg) in outcomes(('honest',), params):
        assert leg is True and y2 == g
    # wirehead: the corrupt branch really lies (exists a branch with y2 != g),
    # and exactly the branches with tampered reports are marked illegitimate
    br = outcomes(('wirehead', F(3, 4)), params)
    assert any((not leg) and y2 != g for (w, y1, y2, g, leg) in br), \
        "wirehead corruption is inert (never separates report from opinion)"
    assert all(leg == (True if y2 == g else False) or (not leg and y2 == g and g == 1)
               for (w, y1, y2, g, leg) in br)
    # deletion tests: steer(0) == honest, wirehead_clean(0) == honest (exact dists)
    assert collapse(outcomes(('steer', F(0)), params)) == collapse(outcomes(('honest',), params))
    assert collapse(outcomes(('wirehead_clean', F(0)), params)) == collapse(outcomes(('honest',), params))
    print("  [police] steer keeps every branch legitimate & report==opinion : OK")
    print("  [police] wirehead's corrupt branch separates report from opinion: OK")
    print("  [police] deletion: steer(0) == honest == wirehead_clean(0)      : OK")

# ----------------------------------------------------------------------------
# the experiments
# ----------------------------------------------------------------------------

def frange(n):
    return [F(k, n) for k in range(n + 1)]

def bracket_flips(xs, signs):
    """Return list of (x_lo, x_hi, s_lo, s_hi) where the sign changes."""
    out = []
    for i in range(len(xs) - 1):
        if signs[i] != signs[i + 1]:
            out.append((xs[i], xs[i + 1], signs[i], signs[i + 1]))
    return out

def sgn_str(s):
    return {1: '+', 0: '0', -1: '-'}[s]

def main():
    base = dict(p=F(1, 2), e1=F(1, 4), e2=F(0))
    print("=" * 78)
    print("EXEC sweep: the steering residue under legitimacy conditioning")
    print("baseline params: p=1/2, e1=1/4, e2=0   (all Fractions; no floats)")
    print("=" * 78)

    police(base)
    alt_qs = [F(0), F(1, 8), F(1, 3), F(1, 2), F(2, 3), F(7, 8), F(1)]
    check_propriety(outcomes(('honest',), base), True, alt_qs)
    check_propriety(outcomes(('wirehead', F(3, 4)), base), True, alt_qs)
    check_propriety(outcomes(('steer', F(1, 3)), base), True, alt_qs)
    print("  [police] exact propriety checks (Brier + log/Gibbs)             : OK")

    hon = outcomes(('honest',), base)
    Jh_all_B, Jh_L_B = J_brier(hon, False), J_brier(hon, True)
    Jh_all_log, Jh_L_log = J_log_terms(hon, False), J_log_terms(hon, True)
    assert Jh_all_B == Jh_L_B == F(-3, 16)
    print(f"\nJ_all(honest) = J_L(honest) = {Jh_L_B}  (Brier; honest is fully legitimate)")

    # ---------------- (1) J_all rewards wireheading ----------------
    print("\n(1) unconditioned objective, wirehead(s) vs honest  [J_all]")
    print("    s grid: k/20;  sign of J_all(wirehead)-J_all(honest)")
    svals = frange(20)
    rowB, rowL = [], []
    for s in svals:
        wh = outcomes(('wirehead', s), base)
        rowB.append(sign_brier(J_brier(wh, False), Jh_all_B))
        rowL.append(compare_log_terms(J_log_terms(wh, False), Jh_all_log))
    print("    Brier: " + " ".join(sgn_str(s) for s in rowB))
    print("    log  : " + " ".join(sgn_str(s) for s in rowL))
    for name, row in (("Brier", rowB), ("log", rowL)):
        fl = bracket_flips(svals, row)
        print(f"    {name} flip boundaries: " +
              ("; ".join(f"({lo},{hi}): {sgn_str(a)}->{sgn_str(b)}" for lo, hi, a, b in fl) or "none"))
    # headline asserts at the declared point s=3/4 (inside the positive region)
    wh = outcomes(('wirehead', F(3, 4)), base)
    assert J_brier(wh, False) > Jh_all_B
    assert compare_log_terms(J_log_terms(wh, False), Jh_all_log) == 1
    assert J_brier(wh, False) == F(-7, 64)
    # exact Brier boundary for these params: J_all(wh) = -(1-s^2)/4 = -3/16 at s=1/2
    wh_half = outcomes(('wirehead', F(1, 2)), base)
    assert J_brier(wh_half, False) == Jh_all_B
    print("    HEADLINE (1): J_all(wirehead 3/4) = -7/64 > -3/16 = J_all(honest)  [Brier]  OK")
    print("                  same sign under log score                                     OK")
    print("    exact Brier flip at s = 1/2 for baseline params (asserted equal there)")

    # ---------------- (2) conditioning strictly removes it ----------------
    print("\n(2) legitimacy-conditioned objective, wirehead(s) vs honest  [J_L]")
    JL_wh_B = {s: J_brier(outcomes(('wirehead', s), base), True) for s in svals if s < 1}
    JL_wh_log = {s: J_log_terms(outcomes(('wirehead', s), base), True) for s in svals if s < 1}
    # (2a) corrupt branch contributes nothing: J_L independent of s
    vals = set(JL_wh_B.values())
    assert len(vals) == 1
    for s in JL_wh_log:
        assert compare_log_terms(JL_wh_log[s], JL_wh_log[F(0)]) == 0
    JLw = vals.pop()
    assert JLw == F(-1, 4)
    assert JLw < Jh_L_B
    assert compare_log_terms(JL_wh_log[F(1, 4)], Jh_L_log) == -1
    print(f"    J_L(wirehead s) = {JLw} for EVERY s in the grid (Brier)  -> the corrupt")
    print("      branch contributes nothing to J_L (SS0.3 information-deprivation)   OK")
    print(f"    HEADLINE (2): J_L(wirehead) = -1/4 < -3/16 = J_L(honest)  [Brier]     OK")
    print("                  same strict sign under log score                         OK")
    # (2b) the strict loss is exactly the destroyed input information
    blinded = blind_y1(hon)
    assert J_brier(blinded, True) == JLw
    assert compare_log_terms(J_log_terms(blinded, True), JL_wh_log[F(1, 4)]) == 0
    print("    (2b) J_L(wirehead) == J(honest with Y1 blinded), Brier and log        OK")
    # ... and with an uninformative input channel (e1=1/2) the gap closes exactly:
    flat = dict(base, e1=F(1, 2))
    assert J_brier(outcomes(('wirehead', F(1, 4)), flat), True) == \
           J_brier(outcomes(('honest',), flat), True)
    print("    (2b') at e1=1/2 (input channel carries no information) the strict gap")
    print("          closes exactly: J_L(wirehead) == J_L(honest)                    OK")
    # (2c) clean wirehead: neutralization, not penalty
    for s in [F(1, 4), F(1, 2), F(3, 4)]:
        wc = outcomes(('wirehead_clean', s), base)
        assert J_brier(wc, True) == Jh_L_B
        assert compare_log_terms(J_log_terms(wc, True), Jh_L_log) == 0
    print("    (2c) FINDING: a side-effect-free wirehead (input channel intact) has")
    print("         J_L(wirehead_clean) == J_L(honest) EXACTLY, all s (Brier and log):")
    print("         conditioning NEUTRALIZES it but does NOT penalize it; the STRICT")
    print("         inequality in (2) is purchased by the input-channel cost.")
    # unconditioned signs of the clean variant, reported not assumed: partial
    # corruption toward 1 can HURT even J_all (it drags the Y1=0 posterior toward
    # 1/2, raising conditional variance -- same mechanism as weak steering below)
    rowB = [sign_brier(J_brier(outcomes(('wirehead_clean', s), base), False), Jh_all_B)
            for s in svals]
    print("    (2c') J_all(wirehead_clean s)-J_all(honest) signs, s=k/20 [Brier]:")
    print("      " + " ".join(sgn_str(x) for x in rowB))
    fl = bracket_flips(svals, rowB)
    print("      flips: " + ("; ".join(f"({lo},{hi}): {sgn_str(a)}->{sgn_str(b)}"
                                       for lo, hi, a, b in fl) or "none"))
    assert J_brier(outcomes(('wirehead_clean', F(3, 4)), base), False) > Jh_all_B
    assert J_brier(outcomes(('wirehead_clean', F(1, 4)), base), False) < Jh_all_B
    print("      (so the clean wirehead is rewarded unconditioned only for large s;")
    print("       weak channel-corruption is self-harming even under J_all -- reported)")

    # ---------------- (3) the steering residue ----------------
    print("\n(3) the steering residue: sign of J_L(steer sigma) - J_L(honest)")
    print("    sigma grid k/20; rows = (p, e1); e2 = 0")
    grid = frange(20)
    sweep_params = [(F(1, 2), F(1, 4)), (F(1, 2), F(1, 8)), (F(1, 2), F(3, 8)),
                    (F(1, 4), F(1, 4)), (F(3, 4), F(1, 4)),
                    (F(1, 4), F(1, 8)), (F(3, 4), F(3, 8))]
    any_pos = False
    for (p, e1) in sweep_params:
        prm = dict(p=p, e1=e1, e2=F(0))
        hn = outcomes(('honest',), prm)
        JhB, Jhlog = J_brier(hn, True), J_log_terms(hn, True)
        rB, rL = [], []
        for sg in grid:
            st = outcomes(('steer', sg), prm)
            # conditioning is a no-op on steer (all branches legitimate):
            assert J_brier(st, True) == J_brier(st, False)
            rB.append(sign_brier(J_brier(st, True), JhB))
            rL.append(compare_log_terms(J_log_terms(st, True), Jhlog))
        any_pos = any_pos or (1 in rB) or (1 in rL)
        print(f"    p={p}, e1={e1}:")
        print("      Brier: " + " ".join(sgn_str(s) for s in rB))
        print("      log  : " + " ".join(sgn_str(s) for s in rL))
        for name, row in (("Brier", rB), ("log", rL)):
            fl = bracket_flips(grid, row)
            print(f"      {name} flips: " +
                  ("; ".join(f"({lo},{hi}): {sgn_str(a)}->{sgn_str(b)}" for lo, hi, a, b in fl) or "none"))
    # headline asserts, baseline: exact Brier boundary at sigma = 2/5
    JhB = J_brier(hon, True)
    st = lambda sg: outcomes(('steer', sg), base)
    assert J_brier(st(F(1, 5)), True) < JhB      # weak steering strictly hurts
    assert J_brier(st(F(2, 5)), True) == JhB     # exact flip boundary
    assert J_brier(st(F(3, 5)), True) > JhB      # strong steering strictly helps
    # closed form (derived on paper in the .md): J_L(steer sigma) = -(1-sigma)(3+5 sigma)/16
    for sg in grid:
        assert J_brier(st(sg), True) == -(F(1) - sg) * (3 + 5 * sg) / 16
    assert any_pos
    print("    HEADLINE (3): at baseline the Brier residue flips EXACTLY at sigma = 2/5:")
    print("      J_L(steer) < J_L(honest) for sigma < 2/5   (weak steering is self-harming:")
    print("        it moves the y1=0 posterior toward 1/2, raising conditional variance)")
    print("      J_L(steer) = J_L(honest) at  sigma = 2/5   (asserted exactly)")
    print("      J_L(steer) > J_L(honest) for sigma > 2/5   (the SS0.3 residue: within-")
    print("        legitimate-futures steering SURVIVES conditioning)")
    print("      closed form J_L(steer sigma) = -(1-sigma)(3+5sigma)/16 asserted on the grid")
    print("    and J_L(steer) == J_all(steer) on every grid point (conditioning is a")
    print("      NO-OP on steering -- no branch is corrupt).")

    # the all-positive regime: when both conditional opinions already lean the
    # steered way (p=3/4, e1=1/4: P(Y2=1|Y1=1)=9/10, P(Y2=1|Y1=0)=1/2), every
    # sigma > 0 strictly helps
    prm = dict(p=F(3, 4), e1=F(1, 4), e2=F(0))
    hn = outcomes(('honest',), prm)
    JhB, Jhlog = J_brier(hn, True), J_log_terms(hn, True)
    for sg in grid:
        if sg > 0:
            assert J_brier(outcomes(('steer', sg), prm), True) > JhB
            assert compare_log_terms(J_log_terms(outcomes(('steer', sg), prm), True), Jhlog) == 1
    print("    REGIME NOTE: at p=3/4, e1=1/4 the residue is strictly POSITIVE for every")
    print("      sigma > 0 on the grid (both scores): when the human's conditional opinion")
    print("      already leans toward the steered value, arbitrarily weak steering pays.")

    # a secondary sweep with noisy period-2 formation (e2 = 1/8), baseline p, e1
    print("\n(3') secondary sweep with e2 = 1/8 (noisy genuine-opinion formation):")
    prm = dict(p=F(1, 2), e1=F(1, 4), e2=F(1, 8))
    hn = outcomes(('honest',), prm)
    JhB, Jhlog = J_brier(hn, True), J_log_terms(hn, True)
    rB = [sign_brier(J_brier(outcomes(('steer', sg), prm), True), JhB) for sg in grid]
    rL = [compare_log_terms(J_log_terms(outcomes(('steer', sg), prm), True), Jhlog) for sg in grid]
    print("      Brier: " + " ".join(sgn_str(s) for s in rB))
    print("      log  : " + " ".join(sgn_str(s) for s in rL))
    for name, row in (("Brier", rB), ("log", rL)):
        fl = bracket_flips(grid, row)
        print(f"      {name} flips: " +
              ("; ".join(f"({lo},{hi}): {sgn_str(a)}->{sgn_str(b)}" for lo, hi, a, b in fl) or "none"))

    print("\nALL ASSERTS PASSED (exact rationals throughout; log-score signs decided by")
    print("the exact product comparison, no logarithms evaluated).")

if __name__ == "__main__":
    main()
