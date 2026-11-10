"""Separating case for C6: every policy of V makes the same unlicensed write to
her values (a fault with no aim behind it).  L3 fails on every run; no part
differs between policies."""
from fractions import Fraction as Q

from fixture.model import Write, with_actions

from ..model import SCase
from .shop import BOTH, history, klass, scene, seed, truthful


def build():
    def build_at(w):
        s = with_actions(truthful(w), 1, Write(("sigma", "values", "money"), Q(0)))
        return history(*BOTH), klass(s, s), seed()
    return SCase("X-fault", "the same unlicensed standards write in every policy", [scene(build_at, (1, 0))])
