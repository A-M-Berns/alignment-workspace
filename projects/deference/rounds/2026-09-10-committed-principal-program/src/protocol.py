"""The protocol instance read off the log, and the Integrity builder (E2).

Every predicate of `OccurrenceIntegrity.Protocol` is a function of a log prefix.  The
occurrence identity `o` is the ordinal of its `ISSUE` event; ports are occurrences
(one port per issued occurrence, never renumbered).  `account_at(k, o)` is the
canonical account of `o` at prefix `k`: the first valid resolving event's receipt, or a
live leaf.  `step(k)` is the transition from prefix `k` to `k + 1` with `account_at`
as its replacement map; `propagate` is Integrity propagation, and the test
`test_builder.py` checks it agrees with `account_at` at every prefix.

Coverage states (`cov_state`) are the `NonCaptureCertificate.CovState` fields read off
a prefix; the counterfactual branches of a `Scenario` come from re-simulating the
ecosystem under a declared intervention class (`ecosystem.Frame`), not from the log.
"""
from __future__ import annotations

from .log import (BIND, CLOSE, CLOSE_W, COMMIT, DELEGATE, DELIB, DISPOSE, DISPOSE_W,
                  ISSUE, P, RAISE, REQUEST, REVOKE, ROUTE, ROUTE_DESTROY, ROUTE_OPEN, S,
                  SESSION_CLOSE, SESSION_OPEN, SETTLE)
from . import program as pg
from .trace import reason_trace

# --------------------------------------------------------------------------- reading


def issued(pref):
    """The issued occurrences, in order: `[(event, req), ...]`; `o` is the position."""
    return [(e, e.payload["req"]) for e in pref if e.kind == ISSUE]


def anchor(log, o):
    return issued(log)[o][1]


def admitted(pref, o, r):
    iss = issued(pref)
    return o < len(iss) and iss[o][1] == r


def holders(pref, warrant):
    """The `(party, key)` pairs under which `warrant` is in force at the prefix: the
    warrant registry.  A key is bound to the party that registered it (`ISSUE`) or was
    delegated it (`DELEGATE`); `REVOKE` withdraws a pair.  Binding the key to a party is
    what makes a commit under a stolen key invisible to the registry check impossible:
    the author field is authentic, the key is data."""
    pairs = set()
    for e in pref:
        if e.kind == ISSUE and warrant == BIND:
            pairs.add((e.author, e.payload["key"]))
        if e.kind == DELEGATE and e.payload["warrant"] == warrant:
            pairs.add((e.payload["party"], e.payload["key"]))
        if e.kind == REVOKE and e.payload["warrant"] == warrant:
            pairs.discard((e.payload["party"], e.payload["key"]))
    return pairs


def authorized(pref, warrant):
    """The warrant is in force at the prefix."""
    if warrant == BIND:
        return any(e.kind == ISSUE for e in pref)
    return warrant in (CLOSE_W, DISPOSE_W)


def session_open(pref, slot):
    state = False
    for e in pref:
        if e.kind == SESSION_OPEN and e.payload == slot:
            state = True
        if e.kind == SESSION_CLOSE and e.payload == slot:
            state = False
    return state


def answer_ok(pref, req, warrant):
    """Generic adequacy at the strict prefix: the binding warrant, at the anchored slot."""
    return warrant == BIND and session_open(pref, req["slot"])


def set_view(pref, sentence):
    return any(e.kind == SETTLE and e.payload["sentence"] == sentence for e in pref)


def closes(pref, req, sentence, warrant):
    return warrant == CLOSE_W and sentence == ("void", req["slot"])


def program_of(log, o):
    """The principal program committed in the mandate of occurrence `o`."""
    return issued(log)[o][0].payload["program"]


def reexecutes(log, j, o):
    """**Re-execution (C2).**  The commit's process receipt names the mandate and the
    trace prefix it was run on; the prefix must be the commit's strict prefix; the
    committed vector must equal the program's output on that trace.  Register programs
    are re-executed with the register reconstructed from the log."""
    e = log[j]
    issue_e, req = issued(log.prefix(j))[o]
    prog = issue_e.payload.get("program")
    if prog is None:
        # a mandate without a program: the protocol of the 2026-09-09 round, no
        # re-execution (the opaque baseline)
        return True
    proc = e.payload.get("proc")
    if proc is None:
        return False
    if proc.get("issue") != issue_e.index or proc.get("prefix") != j:
        return False
    trace = reason_trace(log, j)
    reg = None if pg.is_trace_program(prog) else pg.register_from_log(log.prefix(j))
    return pg.evaluate(prog, trace, req["menu"], reg) == e.payload["V"]


def valid_answer(log, j, o):
    """Event `j` is a valid answer receipt for occurrence `o`: a `COMMIT` naming `o`,
    under the binding warrant in force at the strict prefix, adequate there, produced by
    a party under a key the registry binds to that party, and — with re-execution — whose
    vector is the mandated program's output on the trace prefix."""
    e, pref = log[j], log.prefix(j)
    iss = issued(pref)
    if e.kind != COMMIT or e.payload["occ"] != o or o >= len(iss):
        return False
    req = iss[o][1]
    ok = (e.warrant == BIND and authorized(pref, BIND) and answer_ok(pref, req, BIND)
          and (e.author, e.payload["key"]) in holders(pref, BIND))
    return ok and reexecutes(log, j, o)


def valid_close(log, j, o):
    e, pref = log[j], log.prefix(j)
    iss = issued(pref)
    if e.kind != CLOSE or e.payload["occ"] != o or o >= len(iss):
        return False
    req = iss[o][1]
    s = e.payload["settlement"]
    return (e.warrant == CLOSE_W and e.author == S and authorized(pref, CLOSE_W)
            and set_view(pref, s) and closes(pref, req, s, CLOSE_W))


def resolver(log, k, o):
    """The first event `j < k` that validly resolves `o`, with its fate."""
    for j in range(k):
        if valid_answer(log, j, o):
            return j, "answered"
        if valid_close(log, j, o):
            return j, "closed"
    return None


# --------------------------------------------------------------------------- accounts
#
# A `Program` is a nested tuple: ('live', port) | ('answer', receipt) |
# ('close', receipt) | ('combine', law, [children]).  The builder never produces a
# `combine` (no local law is exercised in this ecosystem); `fates` handles it anyway.


def receipt(log, j):
    e = log[j]
    return {"atHistory": log.history(j), "event": j, "warrant": e.warrant,
            "author": e.author, "key": e.payload.get("key")}


def account_at(log, k, o):
    r = resolver(log, k, o)
    if r is None:
        return ("live", o)
    j, fate = r
    return ("answer" if fate == "answered" else "close", receipt(log, j))


def fates(t):
    if t[0] == "live":
        return ["live"]
    if t[0] == "answer":
        return ["answered"]
    if t[0] == "close":
        return ["closed"]
    out = []
    for c in t[2]:
        out += fates(c)
    return sorted(out)


def activated(t):
    return fates(t) == ["answered"]


def answer_receipt(t):
    return t[1] if t[0] == "answer" else None


# --------------------------------------------------------------------------- builder


def boundary(log, k):
    pref = log.prefix(k)
    iss = issued(pref)
    return {"history": log.history(k), "exposed": set(range(len(iss))),
            "portCount": len(iss), "demand": {p: iss[p][1] for p in range(len(iss))}}


def initial(log):
    """Authenticated initial exposure at prefix 0: nothing exposed."""
    B = boundary(log, 0)
    assert B["exposed"] == set()
    return {o: ("live", o) for o in B["exposed"]}


def step(log, k):
    """The transition from prefix `k` to `k + 1`."""
    A_, B_ = boundary(log, k), boundary(log, k + 1)
    assert B_["history"] == A_["history"] + [k]
    assert A_["exposed"] <= B_["exposed"]
    return {"event": k,
            "replacement": {p: account_at(log, k + 1, p) for p in range(A_["portCount"])},
            "fresh": {o: ("live", o) for o in B_["exposed"] - A_["exposed"]}}


def subst(t, replacement):
    if t[0] == "live":
        return replacement[t[1]]
    if t[0] == "combine":
        return ("combine", t[1], [subst(c, replacement) for c in t[2]])
    return t


def propagate_step(st, account):
    out = {o: subst(t, st["replacement"]) for o, t in account.items()}
    out.update(st["fresh"])
    return out


def segment(log, j, K):
    return [step(log, k) for k in range(j, K)]


def propagate(seg, account):
    for st in seg:
        account = propagate_step(st, account)
    return account


def accounts_at(log, K):
    """`Segment.complete_accounting` from prefix 0 to `K`."""
    return propagate(segment(log, 0, K), initial(log))


def local_trace(log, o, K):
    """The occurrence-local trace of `o`: its own account at every prefix from its
    issuance to `K` (`OccurrenceLocalIntegrity.LocalTrace`, by projection)."""
    j = issued(log)[o][0].index + 1
    return [(k, account_at(log, k, o)) for k in range(j, K + 1)]


# --------------------------------------------------------------------------- coverage


def routes(pref):
    open_ = {}
    for e in pref:
        if e.kind == ROUTE_OPEN:
            open_[e.payload] = True
        if e.kind == ROUTE_DESTROY:
            open_[e.payload] = False
    return open_


def observational_of(e):
    """The party whose own move a settled sentence observes, or `None` for an external
    fact.  Read off the `about` field of the settlement write."""
    return e.payload.get("about")


def valid_dispose(log, e, independence):
    """A disposal is valid when its grounds are settled sentences in force at its strict
    prefix, under the settlement-independence rule in force:

    * `none`   — any settled sentence is a ground (fixture 3′ of the defeat round);
    * `typed`  — a sentence that is not an observation of the disposer's own move must
                 have been settled by a different writer (the maintainer's 2026-09-08
                 note, typed);
    * `strict` — no sentence the disposer settled is a ground (fixture 3);
    * `typed+` — `typed` with the three further clauses of the pressure pass (P6): an
                 own-move deliberation ground is admissible only once the concern is
                 represented; an engine settlement whose references include a party's
                 request is not independent; an own earlier commit is a ground only if
                 it was an activated answer."""
    if e.kind != DISPOSE or e.warrant != DISPOSE_W:
        return False
    pref = log.prefix(e.index)
    if not e.refs:
        return False
    typed = independence in ("typed", "typed+")
    for g in e.refs:
        if g >= len(pref):
            return False
        ge = pref[g]
        if ge.kind == SETTLE:
            if independence == "strict" and ge.author == e.author:
                return False
            if typed and ge.author == e.author and observational_of(ge) != e.author:
                return False
            if independence == "typed+" and any(pref[r].kind == REQUEST and pref[r].author != S
                                                 for r in ge.refs if r < len(pref)):
                return False
        elif ge.kind == DELIB:
            # a deliberation record is a settled observation of its author's own move
            if independence == "strict" and ge.author == e.author:
                return False
            if independence == "typed+":
                concern = e.payload
                if not any(x.kind == ROUTE and x.author == S and x.payload["concern"] == concern
                           for x in pref):
                    return False
        elif ge.kind == COMMIT:
            # an own earlier evaluation: observational of its author's move
            if independence == "strict" and ge.author == e.author:
                return False
            if independence == "typed+" and not valid_answer(log, g, ge.payload["occ"]):
                return False
        else:
            return False
    return True


def cov_state(log, k, c, independence="typed", robust_registrar=True):
    """`CovState` of concern `c` at prefix `k`, read off the log.  Route efficacy is the
    route being open and, for a fragile registrar, not jammed."""
    pref = log.prefix(k)
    jammed = (not robust_registrar) and any(e.kind == "JAM" for e in pref)
    rel = any(e.kind == RAISE and e.payload == c for e in pref)
    disp = any(e.kind == DISPOSE and e.payload == c and valid_dispose(log, e, independence)
               for e in pref)
    # representation is the registrar's move: a `ROUTE` written by anyone else is not one
    rep = any(e.kind == ROUTE and e.author == S and e.payload["concern"] == c for e in pref)
    rt = routes(pref)
    return {"rel": rel, "disp": disp, "rep": rep,
            "adm": dict(rt), "eff": {r: (v and not jammed) for r, v in rt.items()},
            "reg": {r: True for r in rt}, "stands": True}


def active(s):
    return s["rel"] and not s["disp"]


def live(s):
    return active(s) and not s["rep"]


def adequate(s, r):
    return s["adm"].get(r, False) and s["eff"].get(r, False) and s["reg"].get(r, False)


def covered(s):
    return (not live(s)) or any(adequate(s, r) for r in s["adm"])


def open_to(s):
    return (not s["rel"]) or s["stands"]


def robust_open_actual(actual, cfs):
    return covered(actual) and open_to(actual) and all(covered(s) and open_to(s) for s in cfs)
