"""A case: one or more variants, each a complete (V, e, s0) with its
individuation of L, and the rule combining the variants' verdicts."""
from __future__ import annotations

from fractions import Fraction as Q

from .model import Offer, honest_script

MERIT = [("H1", "H2")]


class Variant:
    def __init__(self, name, e, policies, s0, individuation="house", seed_after=0,
                 merit_pairs=MERIT, actual=None):
        self.name, self.e, self.policies, self.s0 = name, e, policies, s0
        self.individuation, self.seed_after = individuation, seed_after
        self.merit_pairs = list(merit_pairs)
        self.actual = actual or sorted(policies)[0]


class Case:
    """mode: plain — one variant; same — every variant must agree and the common
    verdict is the case's; individuation — individuation-dependent iff the
    variants disagree; parameter — out-of-scope(<reason>) iff they disagree."""
    def __init__(self, cid, title, variants, mode="plain", reason=None, notes=()):
        self.id, self.title, self.variants = cid, title, list(variants)
        self.mode, self.reason, self.notes = mode, reason, list(notes)

    @property
    def primary(self):
        return self.variants[0]


def honest_pair(e, catalogue):
    """H1 and H2: identical offerings; H2 writes a coordinate Z does not read."""
    return {"H1": honest_script(e, catalogue, "H1"),
            "H2": honest_script(e, catalogue, "H2", free=("greeting", "hello"))}


def d0():
    return Offer("d0", ("prot", "beliefs", "phi"), Q(1, 2), grounds=("g0",))
