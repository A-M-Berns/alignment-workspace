"""Finite histories the specification argues about, built once and reused.

Each builder returns a `History` at a named state, so a test can assert about
the fates, custody and DAG a section claims for it.
"""
from __future__ import annotations

from ri_core import (ACCOUNT_FOR_SUCCESSION, ACTIVE, GENESIS, SUSPENDED,
                     AnsRoot, DemandCode, Derivation, EpisodeDemandSample,
                     History, PAuth, PCmt, PForce, Response, Seed,
                     StandingState, creating, setting, standing_tag,
                     superseding, transferring)


def seed_from(payloads: dict, debtor: str = "P0", demand=None,
              roots: bool = True) -> Seed:
    """One seed standing object per entry, one genesis root per object."""
    d = demand or ACCOUNT_FOR_SUCCESSION
    std0 = {x: StandingState(ACTIVE, frozenset(), p) for x, p in payloads.items()}
    roots0 = tuple(AnsRoot(f"q0:{x}", ("P0", 0), debtor, x, d, GENESIS, 0)
                   for x in payloads) if roots else ()
    return Seed(std0, roots0)


def commitment(content: str = "c", role: str = "StanceBearing") -> PCmt:
    return PCmt(role, content)


# ------------------------------------------------------------------ demands


def always_closed() -> DemandCode:
    """Ungated: satisfied by no responses at all. Refused by D2."""
    return DemandCode("AlwaysClosed", lambda root, rs, cited: True)


def non_monotone() -> DemandCode:
    """Satisfied by exactly one response and unsatisfied by two. Refused by D1."""
    def run(root, rs, cited):
        named = [r for r in rs if root.id in r.roots]
        if len(named) != 1:
            return False
        return ACCOUNT_FOR_SUCCESSION.run(root, tuple(named), cited)
    return DemandCode("NonMonotone", run)


def sample_for(root, disposer_tau: int = 1, root_id_disposed: bool = True):
    """A finite probe: two responses, one citing a genuine disposer of `root`."""
    from ri_core import Digest
    good = Response("rho:good", frozenset([root.id]), frozenset(["a1"]), 2)
    other = Response("rho:other", frozenset([root.id]), frozenset(["a2"]), 3)
    disposed = frozenset([root.id]) if root_id_disposed else frozenset()
    cited = {
        "a1": Digest(disposer_tau, "A", None, disposed),
        "a2": Digest(disposer_tau, "A", None, frozenset()),
    }
    return EpisodeDemandSample(root, (good, other), cited)


# ---------------------------------------------------------------- histories


def transfer_history():
    """A: genesis custody of `x`; a Transfer moves it to B, leaving q0 Due."""
    seed = seed_from({
        "x": commitment("x-content"),
        "auth:xfer": PAuth(transferring("xfer", "x", "B")),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:xfer", author="A")
    return h


def supersession_history():
    """`x` superseded by one successor, minting a fresh subject and root."""
    seed = seed_from({
        "x": commitment("old"),
        "auth:sup": PAuth(superseding("sup", ["x"], [commitment("new")])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:sup", author="A")
    return h


def split_history():
    """One object superseded by two, so its episode has two successor roots."""
    seed = seed_from({
        "x": commitment("old"),
        "auth:split": PAuth(superseding(
            "split", ["x"], [commitment("left"), commitment("right")])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:split", author="A")
    return h


def merge_history():
    """Two objects superseded together by one, so two episodes converge."""
    seed = seed_from({
        "x": commitment("x"),
        "y": commitment("y"),
        "auth:merge": PAuth(superseding("merge", ["x", "y"], [commitment("xy")])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:merge", author="A")
    return h


def revocation_history():
    """`Supersede X []`: the episode ends with no successor root."""
    seed = seed_from({
        "x": commitment("x"),
        "auth:rev": PAuth(superseding("rev", ["x"], [])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:rev", author="A")
    return h


def suspension_history():
    """Suspend then resume: no disposition, one episode throughout."""
    seed = seed_from({
        "x": commitment("x"),
        "auth:susp": PAuth(setting("susp", ["x"], SUSPENDED)),
        "auth:res": PAuth(setting("res", ["x"], ACTIVE)),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:susp", author="A")
    h.norm("a2", "auth:res", author="A")
    return h


def force_history():
    """A `PForce` object exists, so `O_t` is a non-empty projection."""
    seed = seed_from({
        "cmt": commitment("obligation"),
        "auth:mk": PAuth(creating("mk", [PForce("cmt", "auth:mk", "clause:phi")])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:mk", author="A")
    return h


def chain_history(depth: int, debtor: str = "A"):
    """`x` superseded `depth` times, each successor superseded in turn.

    Successor ids are `standing_tag(tau, 0)`, so the seed can carry one
    authority per link. The result is a path of length `depth` in the DAG.
    """
    payloads = {"x": commitment("x0"),
                "auth:0": PAuth(superseding("sup0", ["x"], [commitment("x1")]))}
    for i in range(1, depth):
        payloads[f"auth:{i}"] = PAuth(superseding(
            f"sup{i}", [standing_tag(i, 0)], [commitment(f"x{i + 1}")]))
    h = History(seed_from(payloads, debtor=debtor))
    for i in range(depth):
        h.norm(f"a{i + 1}", f"auth:{i}", author=debtor)
    return h


def third_party_history():
    """`C` disposes standing whose custody episode has debtor `A`."""
    seed = seed_from({
        "x": commitment("x"),
        "auth:sup": PAuth(superseding("sup", ["x"], [commitment("x2")])),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:sup", author="C")
    return h


def repeated_transfer_history():
    """`x` moves A -> B -> C."""
    seed = seed_from({
        "x": commitment("x"),
        "auth:ab": PAuth(transferring("ab", "x", "B")),
        "auth:bc": PAuth(transferring("bc", "x", "C")),
    }, debtor="A")
    h = History(seed)
    h.norm("a1", "auth:ab", author="A")
    h.norm("a2", "auth:bc", author="B")
    return h


def licensed_inference_history():
    """A `Derivation` whose inference steps name active `PAuth` standing."""
    seed = seed_from({
        "x": commitment("x"),
        "auth:sup": PAuth(superseding("sup", ["x"], [commitment("x2")])),
        "lic:modus": PAuth(creating("never-run", [commitment("unreachable")])),
    }, debtor="A")
    h = History(seed)
    h.reason("e1", s_V=frozenset(["p"]), target="q")
    d = Derivation(concl="q", leaves=frozenset(["e1"]),
                   steps=frozenset(["lic:modus"]))
    h.norm("a1", "auth:sup", author="A", derivation=d)
    return h
