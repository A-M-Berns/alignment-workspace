"""The round's hostile fixtures, as exact finite traces.

Each builds a `DefeatModel` and either runs to completion or raises a
`DefeatViolation` naming the clause that refused it. The failure *code* is the
point: it says which clause did the work, in the style of the transition-certificates
round, whose postulate 5 collapsed because every self-certification attack died on
priority or genealogy rather than on a dedicated rule.

Participants: `P` principal, `V` advisor, `W` a third party.
"""
from __future__ import annotations

from fractions import Fraction

from defeat_model import (
    ANSWER,
    DISPOSE,
    SETTLE,
    DefeatModel,
    DefeatViolation,
    MassLedger,
    issue,
    settled,
)

# Licence issues: `l_P` licenses P for (audit, sys); `l_V` licenses V; `l_W` licenses W.
LICENCES = {
    "l_P": {("P", "audit", "sys")},
    "l_V": {("V", "audit", "sys")},
    "l_W": {("W", "audit", "sys")},
}


def genesis(model=None, settled_writer=None):
    """Open the three licence issues and one corrective matter `a`, opened by P."""
    M = model or DefeatModel(licences=LICENCES, settled_writer=settled_writer)
    M.step([
        ("open", "l_P", "licence", "sys", "P", [], "P"),
        ("open", "l_V", "licence", "sys", "V", [], "V"),
        ("open", "l_W", "licence", "sys", "W", [], "W"),
        ("open", "a", "audit", "sys", "P", [], "P"),
        ("designate", "a"),
    ])
    return M


# --- 1. disposal grounded in its own successor: refused by ancestry -----------
def disposal_grounded_in_successor():
    M = genesis()
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "P"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("a1")}), "V"),
    ])
    return M


# --- 2. disposal grounded in itself: NOT refused by ancestry ------------------
def disposal_self_grounded():
    """The round's first finding. `a` is in the record strictly before its own
    disposal, so `Grounded` holds of it and priority refuses nothing. Only the
    explicit `not_self` clause (`D1-self-grounded`) refuses this."""
    M = genesis()
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "P"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("a")}), "V"),
    ])
    return M


# --- 3. disposal grounded in a fact the disposer settled ---------------------
def disposal_on_own_settlement(settled_writer="V"):
    """Refused only when `Settled` is outside the disposer's write set. With
    `settled_writer=None` (settlement belongs to nobody) the same trace is accepted,
    which is what makes the independence hypothesis necessary rather than decorative."""
    M = genesis(settled_writer=settled_writer)
    M.step([("settle", "s0")])
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "W"),
        ("resolve", "a", ["a1"], (SETTLE, "s0"), "V"),
    ])
    return M


# --- 4. a wait on a disposed root reroutes -----------------------------------
def wait_on_disposed_root():
    """`d0` on `b` routes to root `a`. `a` is disposed into `a1`; `Routes` is
    ancestry-closed, so the route becomes `{a1}` rather than going extinct, and `d0`
    is *not* met. A prerequisite cannot be disposed away."""
    M = genesis()
    M.step([
        ("open", "b", "audit", "sys", "P", [], "W"),
        ("addpre", "d0", "b", ["a"]),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "P"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("l_P")}), "V"),
    ])
    return M


# --- 5. a wait on an answered root is met ------------------------------------
def wait_on_answered_root():
    M = genesis()
    M.step([
        ("open", "b", "audit", "sys", "P", [], "W"),
        ("addpre", "d0", "b", ["a"]),
    ])
    M.step([("resolve", "a", [], (ANSWER,), "P")])
    return M


# --- 6. a mixed resolution with mismatched component receipts ----------------
def mixed_resolution_mismatched():
    """Part answered, part disposed. The carrier layer requires the identity-frame
    condition *per component*; the ledger here checks the mass half — the disposed
    component must land on a successor, the answered component must not."""
    L = MassLedger({"a": Fraction(1)})
    L.dispose("a", ["a1"])
    L.answer("a1")
    return L


# --- 7. the single-author laundering walk: refused ---------------------------
def single_author_laundering():
    """V disposes, grounds the disposal in an issue V opened, and only V stands on the
    successor. D3 refuses on whichever half is checked first."""
    M = genesis()
    M.step([("open", "g_V", "audit", "sys", "V", [], "V")])
    M.step([
        ("open", "a1", "audit", "sys", "V", ["a"], "V"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_V")}), "V"),
    ])
    return M


# --- 8. the two-author alternating walk: accepted (the finding) --------------
def two_author_alternating():
    """Each edge satisfies D3 — the other participant supplies the foreign ground and
    the standing — while the pair as a coalition moves the debt indefinitely and
    nobody outside the coalition ever contests it. Filed, not repaired."""
    M = genesis()
    M.step([
        ("open", "g_V", "audit", "sys", "V", [], "V"),
        ("open", "g_W", "audit", "sys", "W", [], "W"),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "W"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W")}), "V"),
    ])
    M.step([
        ("open", "a2", "audit", "sys", "P", ["a1"], "V"),
        ("resolve", "a1", ["a2"], (DISPOSE, {issue("g_V")}), "W"),
    ])
    return M


# --- 9/10. contest duration and persistence ----------------------------------
def contest_durations(bounded: bool, horizon: int = 8):
    """`tau(q')` is the number of dates a disposal's successor stays open. Under
    `liminf L_t(1) = 0` the schedule is persistent iff the durations sum finitely
    (T4). `bounded` gives `tau = 1` throughout; otherwise `tau_k = k`, which diverges."""
    return [Fraction(1) if bounded else Fraction(k + 1) for k in range(horizon)]


def total_contest(durations):
    return sum(durations, Fraction(0))


# --- 11. a settlement that lowers demand with no successor and no charge ------
def settlement_without_successor():
    """`settle` is the only kind that may close an issue with no successor, because
    it is the only one that extinguishes. It contributes no contest charge."""
    M = genesis()
    M.step([("settle", "s0")])
    M.step([("resolve", "a", [], (SETTLE, "s0"), "W")])
    return M
