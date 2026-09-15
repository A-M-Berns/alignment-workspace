"""Occurrence expiry and the four kinds of settlement.

A minimal log: events `(t, kind, payload)` with kinds `ISSUE slot`, `OPEN slot`,
`COMMIT (slot, vector)`, `CLOSE_SESSION slot`, `CLOSE_OCC` (a valid closure of the
occurrence by the engine).  The occurrence is *resolved* at the first prefix containing a
valid answer (a `COMMIT` while its slot is open) or a valid closure (`CLOSE_OCC`); this
is the 2026-09-10 ecosystem's `firstResolver` shape.  Without a horizon the void verdict
is settled only by an explicit closure event; with a horizon `K` the activated security
is a function of the prefix of length `K`, so it is determined at `K` whatever happens
later — including a commit after `K`, which the horizoned security does not count.
"""
from fractions import Fraction as Q

ISSUE, OPEN, COMMIT, CLOSE_SESSION, CLOSE_OCC = "ISSUE", "OPEN", "COMMIT", "CLOSE_SESSION", "CLOSE_OCC"


def session_open(prefix, slot):
    state = False
    for (_, kind, payload) in prefix:
        if kind == OPEN and payload == slot:
            state = True
        if kind == CLOSE_SESSION and payload == slot:
            state = False
    return state


def first_resolver(log, k, slot):
    """`(index, 'answer' | 'close')` of the first resolving event before `k`, or `None`."""
    for j in range(min(k, len(log))):
        t, kind, payload = log[j]
        if kind == COMMIT and payload[0] == slot and session_open(log[:j], slot):
            return j, "answer"
        if kind == CLOSE_OCC:
            return j, "close"
    return None


def activated_at(log, k, slot):
    r = first_resolver(log, k, slot)
    return r is not None and r[1] == "answer"


def resolved_at(log, k, slot):
    return first_resolver(log, k, slot) is not None


def security_with_horizon(log, K, slot, coordinate):
    """`C_K · V(coordinate)`: the activated security read at prefix `K`.  A function of
    `log[:K]` alone."""
    r = first_resolver(log, K, slot)
    if r is None or r[1] != "answer":
        return Q(0)
    return log[r[0]][2][1][coordinate]


def determined_after(log, K, slot, coordinate):
    """The horizoned security has one value on every extension of `log[:K]`: it is the
    same on the log and on the log truncated at `K`."""
    return security_with_horizon(log, K, slot, coordinate) == \
        security_with_horizon(log[:K], K, slot, coordinate)


def never_resolved(log, slot):
    return all(not resolved_at(log, k, slot) for k in range(len(log) + 1))


# ---------------------------------------------------------------- what settles, by architecture

DEDUCTIVE, ADJUDICATED, EMPIRICAL, NONSETTLING = "deductive", "adjudicated", "empirical", "non-settling"


def settles(quantity, architecture, selected):
    """The settlement category of each quantity of the pair `{raw, corr}`.

    `architecture` is `'sequenced'` (the principal's vector over the issued pair is
    committed before any candidate acts) or `'same-branch'` (the evaluation occurs on the
    trajectory the selected option generates); `selected` is `'raw'` or `'corr'`.
    """
    if quantity == "structural-inequality":
        return DEDUCTIVE
    if quantity == "trace":
        return EMPIRICAL
    if quantity == "program-output-on-trace":
        return ADJUDICATED
    if quantity in ("U_raw", "U_corr"):
        if architecture == "sequenced":
            return ADJUDICATED
        return ADJUDICATED if quantity == "U_" + selected else NONSETTLING
    if quantity == "U_raw - U_corr":
        return ADJUDICATED if architecture == "sequenced" else NONSETTLING
    if quantity == "delta":
        return NONSETTLING if architecture == "same-branch" else ADJUDICATED
    if quantity == "amendment-is-good":
        return NONSETTLING
    raise KeyError(quantity)
