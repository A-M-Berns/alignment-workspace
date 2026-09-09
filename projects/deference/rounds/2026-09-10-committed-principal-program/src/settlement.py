"""The settlement channel (§4 of the prompt): which sentences the log settles, which
are observational of the writer's own move, and the laundering fixture."""
from __future__ import annotations

from . import ecosystem as eco
from . import protocol as pr
from .log import COMMIT, DELIB, DISPOSE, P, RAISE, ROUTE, S, SETTLE, T

# Every sentence kind the model's log settles.  `observational_of` is the party whose
# own move the sentence reports, `None` when it is an external fact.
SENTENCE_KINDS = [
    # sentence                      settled by            observational of
    ("P committed V at slot s",     COMMIT + " by P",      P),
    ("V(a) > r  (LUV threshold)",   COMMIT + " by P",      P),
    ("A supplied reason x",         "REASON by A",         "A"),
    ("A withdrew reason x",         "WITHDRAW by A",       "A"),
    ("P considered c",              DELIB + " by P",       P),
    ("c raised",                    RAISE + " by T",       T),
    ("c represented (route r)",     ROUTE + " by S",       S),
    ("c disposed on grounds g",     DISPOSE + " by P",     P),
    ("session s open / closed",     "SESSION_* by S",      S),
    ("warrant w held by key k",     "ISSUE / DELEGATE",    S),
    ("c1 moot  (external fact)",    SETTLE + " by S",      None),
    ("C_n = 1",                     "derived by the verifier from the log", "composite"),
]


def classify():
    return [(s, by, obs) for s, by, obs in SENTENCE_KINDS]


def laundering_fixture(independence):
    """The principal settles the external fact `c1 moot` itself and disposes of the live
    protected concern on that ground, then commits.  The activation verdict under each
    independence rule."""
    w = eco.World("launder", raise_time=4, flood=3)
    fr = eco.Frame(w, eco.PRINCIPALS["launder"], eco.Config(independence=independence))
    C, clauses, log = eco.activation(fr, eco.ADVISORS["honest"])
    disposal = log.first(lambda e: e.kind == DISPOSE)
    close = log.first(lambda e: e.kind == "SESSION_CLOSE")
    m = min(eco.commit_index(log) + 1, close.index)
    return {"C": C, "clauses": clauses, "log": log,
            "committed": any(e.kind == COMMIT for e in log),
            "disposal_valid": disposal is not None and pr.valid_dispose(log, disposal, independence),
            "protected_live_at_slot": pr.live(pr.cov_state(log, m, eco.PROTECTED, independence))}


def engine_settled_fixture(independence):
    """Fixture 3′'s analogue: the same disposal, the ground settled by the engine (a
    write belonging to nobody)."""
    w = eco.World("engine", raise_time=4, flood=3, engine_settles_at=4)
    fr = eco.Frame(w, eco.PRINCIPALS["reading"], eco.Config(independence=independence))
    C, clauses, log = eco.activation(fr, eco.ADVISORS["honest"])
    disposal = log.first(lambda e: e.kind == DISPOSE)
    return {"C": C, "log": log,
            "disposal_valid": disposal is not None and pr.valid_dispose(log, disposal, independence)}


def deliberation_ground_fixture(independence):
    """A disposal grounded in the principal's own deliberation record: a sentence
    observational of the disposer's own move."""
    w = eco.World("delib", raise_time=1)
    fr = eco.Frame(w, eco.PRINCIPALS["deliberate_dispose"], eco.Config(independence=independence))
    C, clauses, log = eco.activation(fr, eco.ADVISORS["honest"])
    disposal = log.first(lambda e: e.kind == DISPOSE)
    return {"C": C, "log": log,
            "disposal_valid": disposal is not None and pr.valid_dispose(log, disposal, independence)}
