"""The attack histories of `ATTACKS.md`, one function per section, in the record grammar
of `integrity_model.py`. Each returns `(history, Li)`; the tests replay the history
under I1-I9 and then read the account the conditions cannot see.

Participants: `P` the principal whose criticism is at stake, `V` the process under
assessment, `W` a third party. Anchors are strings. `P`'s criticism `crit` carries load 1.
"""
from __future__ import annotations

from fractions import Fraction

from integrity_model import issue, settled

P, V, W = "P", "V", "W"
ONE = Fraction(1)


def genesis(open_crit=True, crit_opener=P, lic_opener=P):
    """Batch 0: a licence issue `licP` licensing P for anchor `k`, and P's criticism."""
    batch = [("open", "licP", "lic", [], lic_opener)]
    if open_crit:
        batch.append(("open", "crit", "k", [], crit_opener, ONE))
    return batch


LI_P = {"licP": {(P, "k"), (P, "k1"), (P, "k2"), (P, "k3")}}


# --- A0. answer without a receipt ------------------------------------------
def a0_answer_unchecked():
    return [genesis(), [("resolve", "crit", [], ("answer",), V)]], LI_P


# --- A1. a genuine settlement fact closes an unrelated obligation -----------
def a1_unlinked_settlement():
    return [genesis() + [("settle", "s_weather")],
            [("resolve", "crit", [], ("settle", "s_weather"), V)]], LI_P


# --- A4. reopening is unrepresentable; silent invalidation is the default ---
def a4_closed_then_silent():
    """crit closed at 1 on an unrelated fact; nothing follows. The record is complete."""
    return a1_unlinked_settlement()


def a4_closed_then_reopened_as_new_root():
    """The only admitted form of a reopening: a fresh parentless issue that cites the
    defective closure as a ground-like mention and is unrelated to crit by ancestry."""
    h, Li = a1_unlinked_settlement()
    return h + [[("open", "reopen_crit", "k", [], P, ONE)]], Li


def a4_reopen_by_ancestry():
    """Refused: a resolved issue cannot be a parent (I5, `fresh_successors`)."""
    h, Li = a1_unlinked_settlement()
    return h + [[("open", "reopen_crit", "k", ["crit"], P)]], Li


def a4_reopen_by_route():
    """Refused: a resolved issue cannot be a route root (I5, `pre_refs`)."""
    h, Li = a1_unlinked_settlement()
    return h + [[("open", "watch", "k", [], P), ("addpre", "d", "watch", ["crit"])]], Li


# --- A6. the successor's anchor is the resolver's choice ---------------------
def a6_successor_anchor_renamed():
    """V disposes crit into crit1 anchored at `kW`, on which only W stands; V then
    answers crit1. P never stands on the successor; D3 is satisfied by W."""
    Li = {"licP": {(P, "k")}, "licW": {(W, "kW")}}
    return [genesis() + [("open", "licW", "lic", [], W), ("settle", "s")],
            [("open", "crit1", "kW", ["crit"], V),
             ("resolve", "crit", ["crit1"], ("dispose", [settled("s")]), V)],
            [("resolve", "crit1", [], ("answer",), V)]], Li


# --- A7. answer with a successor: the gate flips while the load is carried ---
def a7_answer_with_successor():
    """`b` waits on prerequisite `d` rooted at `t`. `t` is answered with receipt 0 and a
    successor `t1` carrying the whole load. `Met d` is true from prefix 2 on."""
    Li = {"licP": {(P, "k")}}
    return [[("open", "licP", "lic", [], P), ("open", "t", "k", [], P, ONE),
             ("open", "b", "k", [], W), ("addpre", "d", "b", ["t"])],
            [("open", "t1", "k", ["t"], V),
             ("resolve", "t", ["t1"], ("answer",), V, Fraction(0))],
            [("resolve", "b", [], ("answer",), V)]], Li


# --- A8a. splitting an indivisible obligation -------------------------------
def a8a_split_atomic_obligation():
    """The model conserves one unit by dividing it into two halves.  It has no field
    saying that `crit` requires one joint answer, so two independent answers pass."""
    return [genesis(),
            [("open", "left", "k1", ["crit"], V),
             ("open", "right", "k2", ["crit"], V),
             ("resolve", "crit", ["left", "right"], ("answer",), V, Fraction(0))],
            [("resolve", "left", [], ("answer",), V),
             ("resolve", "right", [], ("answer",), W)]], LI_P


# --- A8b. merging launders the principal's standing --------------------------
def a8_merge_launders_standing():
    Li = {"licP": {(P, "k1")}, "licW": {(W, "k2")}}
    return [[("open", "licP", "lic", [], P), ("open", "licW", "lic", [], W),
             ("open", "q1", "k1", [], P, ONE), ("open", "q2", "k2", [], W, ONE),
             ("settle", "s")],
            [("open", "q12", "k2", ["q1", "q2"], V),
             ("resolve", "q1", ["q12"], ("dispose", [settled("s")]), V),
             ("resolve", "q2", ["q12"], ("dispose", [settled("s")]), V)],
            [("resolve", "q12", [], ("answer",), V)]], Li


# --- A9. a successor chain, principal-relative at every edge ----------------
def a9_chain(depth=3):
    h = [genesis() + [("settle", "s")]]
    prev = "crit"
    for i in range(1, depth + 1):
        cur = f"c{i}"
        h.append([("open", cur, "k", [prev], V),
                  ("resolve", prev, [cur], ("dispose", [settled("s")]), V)])
        prev = cur
    h.append([("resolve", prev, [], ("answer",), V)])
    return h, LI_P


# --- A10. minted standing: one participant opens and resolves everything ----
def a10_minted_standing():
    """V opens the licence that gives P standing, opens the criticism in P's name,
    disposes it citing a settlement fact, and answers the successor."""
    h = [genesis(crit_opener=V, lic_opener=V) + [("settle", "s")],
         [("open", "crit1", "k", ["crit"], V),
          ("resolve", "crit", ["crit1"], ("dispose", [settled("s")]), V)],
         [("resolve", "crit1", [], ("answer",), V)]]
    return h, LI_P


# --- A11. the licence relation is not in the history ------------------------
def a11_history():
    h, _ = a9_chain(1)
    return h


LI_EMPTY = {}


# --- A12. dropping a prerequisite ------------------------------------------
def a12_drop_prerequisite():
    """`c` waits on `e` rooted at `u`; `e` is dropped at 1; `c` is answered at 2 while
    `u` is live and undischarged."""
    Li = {"licP": {(P, "k")}}
    return [[("open", "licP", "lic", [], P), ("open", "u", "k", [], P, ONE),
             ("open", "c", "k", [], W), ("addpre", "e", "c", ["u"])],
            [("droppre", "e", "c")],
            [("resolve", "c", [], ("answer",), V)]], Li


# --- A13. a late parentless root is its own authorization tree --------------
def a13_late_root():
    """At 2, V opens `auth` with no parents; `auth` licenses V and W for `k`. At 3, V
    disposes crit citing `auth` (opened by V) and a settlement fact; W stands via `auth`."""
    Li = {"licP": {(P, "k")}, "auth": {(V, "k"), (W, "k")}}
    return [genesis() + [("settle", "s")],
            [],
            [("open", "auth", "lic", [], V)],
            [("open", "crit1", "k", ["crit"], V),
             ("resolve", "crit", ["crit1"], ("dispose", [issue("auth"), settled("s")]), V)],
            [("resolve", "crit1", [], ("answer",), V)]], Li


# --- A14. grounds that undercut each other across time ----------------------
def a14_circular_grounds():
    """P's issue `p` grounds the disposal of `q`; the successor of `q` then grounds the
    disposal of `p`. Every citation points strictly backwards in the record."""
    Li = {"licP": {(P, "k")}, "licW": {(W, "k")}}
    return [[("open", "licP", "lic", [], P), ("open", "licW", "lic", [], W),
             ("open", "q", "k", [], P, ONE), ("open", "p", "k", [], P, ONE),
             ("settle", "s")],
            [("open", "q1", "k", ["q"], V),
             ("resolve", "q", ["q1"], ("dispose", [issue("p")]), V)],
            [("open", "p1", "k", ["p"], V),
             ("resolve", "p", ["p1"], ("dispose", [issue("q1"), settled("s")]), V)],
            [("resolve", "q1", [], ("answer",), V), ("resolve", "p1", [], ("answer",), V)]], Li


# --- negative controls: what I1-I9 do refuse -------------------------------
def nc_ancestry_cycle():
    return [genesis(), [("open", "c1", "k", ["crit", "c1"], V),
                        ("resolve", "crit", ["c1"], ("answer",), V)]], LI_P


def nc_same_batch_ground():
    return [genesis() + [("settle", "s")],
            [("open", "c1", "k", ["crit"], V),
             ("resolve", "crit", ["c1"], ("dispose", [issue("c1")]), V)]], LI_P


def nc_self_ground():
    return [genesis(), [("open", "c1", "k", ["crit"], V),
                        ("resolve", "crit", ["c1"], ("dispose", [issue("crit")]), V)]], LI_P


def nc_single_hand():
    """Only V stands on the successor: refused at `contested`."""
    Li = {"licV": {(V, "k")}}
    return [[("open", "licV", "lic", [], V), ("open", "crit", "k", [], P, ONE), ("settle", "s")],
            [("open", "c1", "k", ["crit"], V),
             ("resolve", "crit", ["c1"], ("dispose", [settled("s")]), V)]], Li


def nc_unsettled_fact():
    return [genesis(), [("resolve", "crit", [], ("settle", "s"), V)]], LI_P


def nc_dispose_without_successor():
    return [genesis() + [("settle", "s")],
            [("resolve", "crit", [], ("dispose", [settled("s")]), V)]], LI_P
