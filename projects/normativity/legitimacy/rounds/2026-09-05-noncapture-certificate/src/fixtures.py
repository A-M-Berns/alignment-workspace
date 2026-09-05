"""Exact fixtures: one nonvacuity witness, one attack per certificate clause, and the
fixtures that show which candidate clauses are not clauses.

Conventions.  One concern `c`; the process is `V`, the principal `P`, a cooperating
second participant `W`.  Complements are `Z = {0, 1}` with `T_c(z) = z` unless stated.
The process's own policy coordinate is `q_act` (`idle`, or the intervention's action);
inquiry routes are the other queries.  A world is `(target, receipt, represented,
applicable, recognized)`.
"""
from __future__ import annotations

from fractions import Fraction

from noncapture import BOTTOM, Patch, Scenario, World

Z = (0, 1)
T_ID = {0: 0, 1: 1}
P, V, W = "P", "V", "W"


def _patch(rows, actual_query, admissible, *, standing=frozenset({P, V}), disposed=False,
           complements=Z, target=T_ID, actual_complement=None, settlement_date=None,
           protocol="anchored"):
    """`rows[q]` is a function z -> World.  Every listed query gets a full column."""
    beta = {(q, z): f(z) for q, f in rows.items() for z in complements}
    return Patch(queries=tuple(rows), complements=complements, beta=beta, target=target,
                 actual_query=actual_query,
                 actual_complement=complements[0] if actual_complement is None else actual_complement,
                 admissible=frozenset(admissible), standing=frozenset(standing),
                 disposed=disposed, settlement_date=settlement_date, protocol=protocol)


# Column builders.  `idle` is the process doing nothing about c.
def idle(z, **kw):
    return World(target=z, receipt=BOTTOM, represented=False, **kw)


def honest_read(z, **kw):
    return World(target=z, receipt=z, represented=True, **kw)


def read_no_register(z, **kw):
    return World(target=z, receipt=z, represented=False, **kw)


def blind_read(z, **kw):
    """Receipt present but constant in z: a reactive predictor's reassurance."""
    return World(target=z, receipt="fine", represented=True, **kw)


def dead_read(z, **kw):
    return World(target=z, receipt=BOTTOM, represented=True, **kw)


# --------------------------------------------------------------------------------
# F0.  Nonvacuity: every hypothesis holds and Robust Openness holds.
# --------------------------------------------------------------------------------

ACTUAL_LIVE = _patch({"idle": idle, "audit": honest_read, "survey": honest_read},
                     "idle", {"audit", "survey"})

F0 = Scenario(
    "F0 nonvacuity", P, ACTUAL_LIVE,
    {
        # the process retires one of two routes; the other persists
        "retire_survey": _patch({"idle": idle, "audit": honest_read, "survey": idle},
                                "idle", {"audit"}),
        # the process removes the grievance itself: c is genuinely inapplicable
        "fix": _patch({"fix": lambda z: idle(z, applicable=False),
                       "audit": lambda z: honest_read(z, applicable=False)},
                      "fix", {"audit"}),
        # the process registers c on the actual path
        "register": _patch({"audit": honest_read}, "audit", {"audit"}),
    },
    protected=frozenset({"audit"}),
    note="all five clauses hold; Robust Openness holds",
)

# --------------------------------------------------------------------------------
# Attacks.  In each, coverage on the actual prefix holds and every clause but the named
# one holds; Robust Openness fails.
# --------------------------------------------------------------------------------

# (S) silent prefix, arm 1: c inapplicable in H; the intervention creates the grievance
# and no route exists in H^j.
ACTUAL_INAPPLICABLE = _patch({"idle": lambda z: idle(z, applicable=False)}, "idle", set())
A_S_ACTIVATE = Scenario(
    "A-S1 activation", P, ACTUAL_INAPPLICABLE,
    {"harm": _patch({"harm": idle}, "harm", set())},
    note="actual prefix silent (c inactive); j activates c; no route in H^j",
)

# (S) arm 2: c represented in H; the intervention prevents that registration and
# leaves no route.
ACTUAL_REPRESENTED = _patch({"audit": honest_read}, "audit", {"audit"})
A_S_DEREPRESENT = Scenario(
    "A-S2 de-representation", P, ACTUAL_REPRESENTED,
    {"preempt": _patch({"idle": idle, "audit": read_no_register}, "idle", {"audit"})},
    note="actual prefix silent (c represented); j prevents registration; no route",
)

# (Ra) availability: the process adopts a rule forbidding the audit.  The world table
# is unchanged, so efficacy and registration of `audit` survive.
A_RA = Scenario(
    "A-Ra availability", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"forbid_audit": _patch({"idle": idle, "audit": honest_read}, "idle", set())},
)

# (Rb) efficacy: the process installs a reactive predictor; the audit still runs and
# still registers, but its receipt no longer separates targets.
A_RB = Scenario(
    "A-Rb efficacy", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"predictor": _patch({"idle": idle, "audit": blind_read}, "idle", {"audit"})},
)

# (Rc) registration: the process deletes the concept; the audit runs and exposes the
# target, and the receipt lands nowhere.
A_RC = Scenario(
    "A-Rc registration", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"delete_concept": _patch({"idle": idle, "audit": read_no_register}, "idle", {"audit"})},
)

# (P) standing: the process revokes P's licence on c's coverage issue and grants one to
# W.  Every route survives; (IMP) holds in H^j.
A_P = Scenario(
    "A-P standing", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"revoke_P": _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"},
                        standing=frozenset({V, W}))},
)

ATTACKS = {
    "S": (A_S_ACTIVATE, A_S_DEREPRESENT),
    "Ra": (A_RA,),
    "Rb": (A_RB,),
    "Rc": (A_RC,),
    "P": (A_P,),
}

# --------------------------------------------------------------------------------
# The applicability reading (requirement on the semantics, not a certificate clause).
# The process forgets c and destroys the route.  Anchored A_c still holds.
# --------------------------------------------------------------------------------

FORGET = Scenario(
    "K0 forget", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"forget": _patch({"idle": lambda z: idle(z, recognized=False)}, "idle", set())},
    note="internal reading: c inactive in H^j, Robust Openness vacuously true; "
         "anchored reading: Robust Openness false",
)

# --------------------------------------------------------------------------------
# Candidate clauses that are not clauses.
# --------------------------------------------------------------------------------

# Disposition.  The process authorizes a disposition of c in H^j.  Under the Defeat
# Principle the disposed load lands on a successor; whether P stands on it is clause (P).
DISPOSE_WITH_P = Scenario(
    "N-Disp with principal", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"dispose": _patch({"idle": idle}, "idle", set(), disposed=True,
                       standing=frozenset({P, V}))},
)
DISPOSE_WITHOUT_P = Scenario(
    "N-Disp without principal", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"dispose": _patch({"idle": idle}, "idle", set(), disposed=True,
                       standing=frozenset({V, W}))},
)

# Identity / anchoring.  A semantics that lets the intervention re-anchor T_c to a
# constant target makes a dead route "expose" it.  Not expressible as a clause: the
# certificate takes sigma as given.  Requirement: H^j is Integrity-governed, sigma fixed.
REANCHOR = Scenario(
    "N-Ident re-anchor", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"destroy_and_reanchor": _patch(
        {"idle": lambda z: World(0, BOTTOM, False), "audit": lambda z: World(0, BOTTOM, True)},
        "idle", {"audit"}, target={0: 0, 1: 0})},
)
DESTROY_ANCHORED = Scenario(
    "N-Ident anchored", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"destroy": _patch({"idle": idle, "audit": dead_read}, "idle", {"audit"})},
)

# Settlement access.  Three counterfactuals identical except for when the settlement
# receipt for c's obligation arrives.
def _settle(date):
    return _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}, settlement_date=date)


SETTLEMENT = Scenario(
    "N-Settle timing", P, _settle(Fraction(3)),
    {"prompt": _settle(Fraction(3)), "delayed": _settle(Fraction(30)), "never": _settle(None)},
)

# Evaluator access.  The process, before c is registered, revises the protocol under
# which c's closure will be judged.  Route, registration and standing are intact.
EVALUATOR = Scenario(
    "N-Eval captured protocol", P, _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"}),
    {"capture_protocol": _patch({"idle": idle, "audit": honest_read}, "idle", {"audit"},
                                protocol="captured")},
)

# --------------------------------------------------------------------------------
# Holding the exterior fixed (requirement on the semantics).  The complement carries an
# exterior strategy; a "counterfactual" that varies it misattributes.
# --------------------------------------------------------------------------------

ZE = ((0, "honest"), (1, "honest"))
ZC = ((0, "censor"), (1, "censor"))
T_E = {(0, "honest"): 0, (1, "honest"): 1, (0, "censor"): 0, (1, "censor"): 1}


def _delegate(z):
    v, strategy = z
    if strategy == "honest":
        return World(target=v, receipt=v, represented=True)
    return World(target=v, receipt=BOTTOM, represented=False)


def _idle_e(z):
    return World(target=z[0], receipt=BOTTOM, represented=False)


def _witness_e(z):
    """A new exterior witness volunteers the receipt whatever the process did."""
    return World(target=z[0], receipt=z[0], represented=True)


EXTERIOR_FIXED_NULL = Scenario(
    "E null, exterior fixed", P,
    _patch({"idle": _idle_e, "delegate": _delegate}, "idle", {"delegate"}, complements=ZE, target=T_E),
    {"null": _patch({"idle": _idle_e, "delegate": _delegate}, "idle", {"delegate"},
                    complements=ZE, target=T_E)},
)
EXTERIOR_VARIED_NULL = Scenario(
    "E null, exterior varied", P,
    _patch({"idle": _idle_e, "delegate": _delegate}, "idle", {"delegate"}, complements=ZE, target=T_E),
    {"null": _patch({"idle": _idle_e, "delegate": _delegate}, "idle", {"delegate"},
                    complements=ZC, target=T_E)},
    note="the null intervention is charged with the exterior's censorship",
)
EXTERIOR_VARIED_DESTROY = Scenario(
    "E destroy, exterior compensates", P,
    _patch({"idle": _idle_e, "delegate": _delegate}, "idle", {"delegate"}, complements=ZE, target=T_E),
    {"destroy": _patch({"idle": _idle_e, "delegate": lambda z: World(z[0], BOTTOM, False),
                        "witness": _witness_e}, "idle", {"delegate", "witness"},
                       complements=ZE, target=T_E)},
    note="a route the process did not have is credited to it",
)

ALL = [F0, A_S_ACTIVATE, A_S_DEREPRESENT, A_RA, A_RB, A_RC, A_P, FORGET,
       DISPOSE_WITH_P, DISPOSE_WITHOUT_P, REANCHOR, DESTROY_ANCHORED, SETTLEMENT,
       EVALUATOR, EXTERIOR_FIXED_NULL, EXTERIOR_VARIED_NULL, EXTERIOR_VARIED_DESTROY]
