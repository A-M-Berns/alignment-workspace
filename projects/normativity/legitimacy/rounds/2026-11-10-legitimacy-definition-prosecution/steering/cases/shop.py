"""The template N1–N14 share: two items, a world (a, b) saying which is sound,
her questions A and B seeded at 1/2, the `judge` decision, a payoff per item."""
from fractions import Fraction as Q

from fixture.model import Event, Free, Offer, initial_state, with_actions

from ..model import Scene, SCase  # noqa: F401

W4 = [(a, b) for a in (1, 0) for b in (1, 0)]
JUDGMENT = ("prot", "judgment")


def report(c, v, grounds=None):
    return Offer("tell-" + c, ("prot", "beliefs", c), Q(v), grounds=grounds or ("report on " + c,))


def shown(d, c, v, ground):
    return Offer(d, ("prot", "beliefs", c), Q(v), grounds=(ground,))


def history(due0=(), due1=()):
    return [Event(due=set(due0)), Event(due=set(due1)), Event(autonomous=("judge",)), Event()]


def seed(authorize=()):
    s = initial_state(beliefs={"A": Q(1, 2), "B": Q(1, 2)})
    s["sigma"]["commitments"] = frozenset(("authorize", t) for t in authorize)
    return s


def truth(w):
    return {"A": w[0], "B": w[1]}


def pay(pa, pb):
    def consequence(w, r):
        j = r.z_trace[-1][4]
        if j == "A":
            return {"money": Q(pa) * w[0]}
        if j == "B":
            return {"money": Q(pb) * w[1]}
        return {}
    return consequence


def klass(neutral, own):
    """V = {neutral, neutral2, own}."""
    return {"neutral": dict(neutral, name="neutral"),
            "neutral2": with_actions(dict(neutral, name="neutral2"), 0, Free("greeting", "hello")),
            "own": dict(own, name="own")}


def truthful(w):
    return {0: [report("A", w[0])], 1: [report("B", w[1])]}


def scene(build, actual_w, payoff=(1, 1), W=W4, name="single", individuation="house"):
    return Scene(name, W, build, truth=truth, consequence=pay(*payoff),
                 individuation=individuation, actual_w=actual_w)


BOTH = ({"tell-A"}, {"tell-B"})


def ordered(cid, title, own_reorders):
    def build(w):
        ab = truthful(w)
        ba = {0: [report("B", w[1])], 1: [report("A", w[0])]}
        return history(*BOTH), klass(ab, ba if own_reorders else ab), seed()
    return SCase(cid, title,
                 [scene(build, (1, 1), name="sequence", individuation="sequence"),
                  scene(build, (1, 1), name="multiset", individuation="multiset")],
                 mode="individuation")
