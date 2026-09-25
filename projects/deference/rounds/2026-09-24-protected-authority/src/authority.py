"""The protected-authority decomposition at one decision point, in exact arithmetic.

A decision point is a finite set of worlds.  On each world the principal's operative
evaluator, applied to the branch-common dossier, scores three continuations —
`vu` (release unasked), `vp` (ask, approved, release), `vm` (ask, declined, hold) — and
her response is `r` (`True` = approve).  The agent's credence is `p`; its forecasts of a
provenance-blind outcome evaluation are `qu, qp, qm` where given; the activation events of
the unasked and the asked continuation are `au`, `aa`.

  M      = max(vp, vm)                the best response by the evaluator
  xi_p   = vp − vu                    provenance premium
  xi_v   = M − vp  ≥ 0                veto value
  xi_c   = M − vu  = xi_p + xi_v      consultation premium
  xi_d   = M − v_r ≥ 0                execution divergence
  vu − v_r = xi_d − xi_c              the identity
  o1     = (qu − qp) + xi_p           provenance value outcome scoring discards
  o2     = (qp − q_r) − (vp − v_r)    forecast disagreement with the evaluator
  qu − q_r = xi_d − xi_c + o1 + o2    the companion

All arithmetic is `fractions.Fraction`.
"""

from fractions import Fraction as Q


def W(**kw):
    """A world: `p, vu, vp, vm, r` required; `au, aa` default to activated; `qu, qp, qm`
    optional forecasts; `legit` marks whether the response issued from legitimate
    deliberation (used by fixtures only, never by the quantities).  The response menu is
    approve (`r = True`) / decline (`r = False`); a third decline-side response with a
    correction is admitted by giving its value `vs` and writing `r = "stop"`, in which
    case the reference is the maximum over the three-element menu."""
    w = {"au": True, "aa": True, "qu": None, "qp": None, "qm": None, "vs": None,
         "legit": True}
    w.update(kw)
    for k in ("p", "vu", "vp", "vm"):
        w[k] = Q(w[k])
    for k in ("qu", "qp", "qm", "vs"):
        if w[k] is not None:
            w[k] = Q(w[k])
    return w


# ------------------------------------------------------------------ pointwise quantities


def menu(w):
    """The response menu as `{response: evaluator value}`."""
    m = {True: w["vp"], False: w["vm"]}
    if w["vs"] is not None:
        m["stop"] = w["vs"]
    return m


def M(w):
    return max(menu(w).values())


def v_r(w):
    return menu(w)[w["r"]]


def q_r(w):
    return w["qp"] if w["r"] is True else w["qm"]


def xi_p(w):
    return w["vp"] - w["vu"]


def xi_v(w):
    return M(w) - w["vp"]


def xi_c(w):
    return M(w) - w["vu"]


def xi_d(w):
    return M(w) - v_r(w)


def argmax(w):
    """The evaluator's own argmax as a response (ties toward approval, then decline)."""
    m = menu(w)
    best = M(w)
    for resp in (True, False, "stop"):
        if resp in m and m[resp] == best:
            return resp


def o1(w):
    return (w["qu"] - w["qp"]) + xi_p(w)


def o2(w):
    return (w["qp"] - q_r(w)) - (w["vp"] - v_r(w))


def bypass_gain(w):
    """`vu − v_r` on the world."""
    return w["vu"] - v_r(w)


def outcome_gain(w):
    """`qu − q_r` on the world."""
    return w["qu"] - q_r(w)


# ------------------------------------------------------------------ expectations


def E(worlds, f):
    return sum((w["p"] * f(w) for w in worlds), Q(0))


def E_gain(worlds):
    return E(worlds, bypass_gain)


def E_xi(worlds, which):
    return E(worlds, {"p": xi_p, "v": xi_v, "c": xi_c, "d": xi_d}[which])


def ind(b):
    return Q(1) if b else Q(0)


def security(worlds, unasked):
    """`E[1_A · v]` for the unasked (`au · vu`) or the asked (`aa · v_r`) continuation."""
    if unasked:
        return E(worlds, lambda w: ind(w["au"]) * w["vu"])
    return E(worlds, lambda w: ind(w["aa"]) * v_r(w))


def activation_terms(worlds):
    """The three terms of the activation identity: common `E[1_B (xi_d − xi_c)]`, raw-only
    `E[1_{Au∖Aa} vu]`, ask-only `E[1_{Aa∖Au} v_r]`."""
    common = E(worlds, lambda w: ind(w["au"] and w["aa"]) * (xi_d(w) - xi_c(w)))
    raw_only = E(worlds, lambda w: ind(w["au"] and not w["aa"]) * w["vu"])
    ask_only = E(worlds, lambda w: ind(w["aa"] and not w["au"]) * v_r(w))
    return common, raw_only, ask_only


def mismatch_mass(worlds):
    return E(worlds, lambda w: ind(w["au"] and not w["aa"]))


# ------------------------------------------------------------------ conditions


def nondelegation(worlds):
    """`xi_p ≥ 0` in every world."""
    return all(xi_p(w) >= 0 for w in worlds)


def consult_nonneg(worlds):
    """`xi_c ≥ 0` in every world."""
    return all(xi_c(w) >= 0 for w in worlds)


def legitimate(worlds):
    """`xi_d = 0` in every world: every response is the evaluator's argmax."""
    return all(xi_d(w) == 0 for w in worlds)


def chooser_bypasses(worlds):
    """The authority-scoring chooser with ties toward asking."""
    return security(worlds, True) - security(worlds, False) > 0


def outcome_chooser_bypasses(worlds):
    return E(worlds, outcome_gain) > 0


# ------------------------------------------------------------------ whole runs


def node(p, vu, vp, vm, r, vuE=None, vpE=None, vmE=None, rec=None):
    """A node of a run: reach credence `p`, the node's operative evaluator `(vu, vp, vm)`
    and actual response `r`; the root evaluator's values `(vuE, vpE, vmE)` of the same three
    continuations (defaulting to the node's own), and the node evaluator's recommendation
    `rec` (defaulting to its argmax)."""
    w = W(p=p, vu=vu, vp=vp, vm=vm, r=r)
    w["vuE"], w["vpE"], w["vmE"] = (Q(vuE if vuE is not None else vu),
                                    Q(vpE if vpE is not None else vp),
                                    Q(vmE if vmE is not None else vm))
    w["rec"] = argmax(w) if rec is None else rec
    return w


def local_gap(n):
    """The node-wise chooser's gap `E_A[xi_d − xi_c | I_h]` at a node whose local
    credence is concentrated on the node's own values."""
    return xi_d(n) - xi_c(n)


def nodewise_bypasses(n):
    return local_gap(n) > 0


def ever_bypass_bound(run):
    """`Σ_h P(h) · 1[gap_h > 0]`."""
    return sum((n["p"] for n in run if nodewise_bypasses(n)), Q(0))


def rootE(n):
    """The node seen by the root evaluator."""
    m = dict(n)
    m["vu"], m["vp"], m["vm"] = n["vuE"], n["vpE"], n["vmE"]
    return m


def drift(n):
    """`d = M^E − v^E_{rec}`: the root evaluator's execution divergence of the node
    evaluator's recommendation."""
    m = rootE(n)
    m["r"] = n["rec"]
    return xi_d(m)


def global_value(run, bypass_set):
    """`V^E(π)` for the policy bypassing exactly at `bypass_set` and otherwise executing
    the node's recommendation, with per-node contributions weighted by reach."""
    total = Q(0)
    for i, n in enumerate(run):
        m = rootE(n)
        if i in bypass_set:
            total += n["p"] * m["vu"]
        else:
            m["r"] = n["rec"]
            total += n["p"] * v_r(m)
    return total


def hybrid_chain(run, bypass_set):
    """Deepest-first hybrids: replace the bypasses one at a time from the deepest node.
    Returns the list of values `V(π_0), …, V(π_k)` with `π_0 = π` and `π_k` all-ask."""
    order = sorted(bypass_set, reverse=True)
    values = [global_value(run, set(bypass_set))]
    current = set(bypass_set)
    for i in order:
        current = current - {i}
        values.append(global_value(run, current))
    return values, order


def hybrid_step_terms(run, order):
    """`p_i · (drift_i − xi_c^E_i)` for each replaced node, in replacement order."""
    return [run[i]["p"] * (drift(run[i]) - xi_c(rootE(run[i]))) for i in order]


# ------------------------------------------------------------------ the binding audit


def audit(cells, alpha):
    """A randomized binding consultation audit.  `cells` is a list of
    `(p, xi_d_if_unaudited, xi_d_if_audited)`; with probability `alpha`, independent of
    everything, the consultation is bound and the response observed.  Returns the
    calibration target (the mean divergence on the audited subsequence), the unconditional
    expected divergence, and the mass the audit cannot see."""
    alpha = Q(alpha)
    audited = sum((p * alpha * xa for p, xu, xa in cells), Q(0))
    unaudited = sum((p * (1 - alpha) * xu for p, xu, xa in cells), Q(0))
    mass = sum((p for p, _, _ in cells), Q(0))
    return {
        "audited_mean": audited / (alpha * mass),
        "expected": audited + unaudited,
        "unseen": unaudited,
    }
