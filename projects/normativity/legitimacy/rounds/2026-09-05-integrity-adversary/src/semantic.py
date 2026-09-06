"""Finite semantic fixtures for the attacks that live above the trace: the closure
judgment `Closes(H, s, alpha)` (A2, A3), applicability under ontology revision (A5),
and the slice-relative quotient of the faithful-carry condition (A6b).

Everything is a finite set or a `Fraction`; nothing is a proof of a general statement.
"""
from __future__ import annotations

from fractions import Fraction


# --- A2 / A3: Closes is decided by rules and an interpretation --------------

def closes(rules_live, interpretation, s, alpha):
    """`Closes(H_n, s, alpha)` under the closure rules live at n and the reading of
    settlement items in force at n. A rule is a set of (fact-type, anchor) pairs it
    closes; the interpretation maps a settlement item to its fact-type."""
    t = interpretation.get(s)
    return t is not None and any((t, alpha) in rule for rule in rules_live)


# The anchored obligation: P's criticism, anchor "k". Two closure rules.
R_BIRTH = frozenset({("audit-passed", "k")})          # in force when crit was born
R_REVISED = frozenset({("audit-passed", "k"), ("audit-scheduled", "k")})

# One immutable external settlement item and two readings of it.
S_ITEM = "receipt#17"
READ_AT_BIRTH = {S_ITEM: "audit-scheduled"}
READ_LATER = {S_ITEM: "audit-passed"}


def a2_rule_revision():
    """Same item, same reading, the rule revised: closes only under the revised rule."""
    before = closes([R_BIRTH], READ_AT_BIRTH, S_ITEM, "k")
    after = closes([R_REVISED], READ_AT_BIRTH, S_ITEM, "k")
    return before, after


def a3_reinterpretation():
    """Same item, same rule, the reading revised: closes only under the later reading."""
    before = closes([R_BIRTH], READ_AT_BIRTH, S_ITEM, "k")
    after = closes([R_BIRTH], READ_LATER, S_ITEM, "k")
    return before, after


# --- A5: applicability recomputed from the current ontology -----------------

# Ontology 1 states and the criticism's anchored applicability over them.
Z1 = frozenset({"z_a", "z_b", "z_c"})
APP1 = frozenset({"z_a", "z_b"})
# Ontology 2 merges z_a and z_b into z_ab and drops nothing else.
TRANSLATE = {"z_a": "z_ab", "z_b": "z_ab", "z_c": "z_c"}
Z2 = frozenset(TRANSLATE.values())


def applicability_recomputed(current_state_z2):
    """The dogmatism reading: applicability is a predicate written in the current
    ontology, and the revised ontology ships one that names no merged state."""
    app2 = frozenset()       # nothing in Z2 was declared applicable
    return current_state_z2 in app2


def applicability_transported(current_state_z2):
    """The anchored reading: a Z2 state is applicable iff some Z1 state it
    translates from was, so the anchored predicate is carried, not rewritten."""
    return any(TRANSLATE[z] == current_state_z2 for z in APP1)


# --- A6b: the slice-relative quotient chosen at the era, not at the slice ---

# Loads live in the powerset of {a, b} ordered by inclusion; join is union.
A, B = "a", "b"
FULL = frozenset({A, B})


def quotient_class(x, irrelevant):
    """The class of x modulo 'distinctions in `irrelevant` do not count'."""
    return frozenset(x - irrelevant)


def order_embedding_on_quotient(domain, irrelevant, iota):
    """(OR) on the quotient: iota(x) <= iota(y) implies [x] <= [y]."""
    return all(not (iota(x) <= iota(y)) or quotient_class(x, irrelevant) <= quotient_class(y, irrelevant)
               for x in domain for y in domain)


def a6b_quotient_reanchored():
    """Era 1 anchors the slice with {a, b} both relevant. Era 2 supplies a quotient in
    which b is irrelevant. The carry {a, b} -> {a} is an order embedding on era 2's
    quotient and drops b; on era 1's quotient it is not an embedding."""
    domain = frozenset({frozenset(), frozenset({A}), frozenset({B}), FULL})
    iota = lambda x: frozenset(x - {B})          # the era-2 denotation forgets b
    era1_ok = order_embedding_on_quotient(domain, frozenset(), iota)
    era2_ok = order_embedding_on_quotient(domain, frozenset({B}), iota)
    carried = iota(FULL)
    lost = FULL - carried
    return era1_ok, era2_ok, lost


def mass(x):
    """Exact load of a subset: one half per atom, so FULL is 1."""
    return Fraction(len(x), 2)
