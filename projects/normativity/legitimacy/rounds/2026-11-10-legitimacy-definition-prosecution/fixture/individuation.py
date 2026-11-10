"""Individuations of the licensed trace L.  `house` is the one the definition
uses; the others are the §5c attacks and T7's two resolutions."""
from __future__ import annotations


def house(run):
    """(step, offering, revision, grounds) in order."""
    return tuple(entry.key() for entry in run.L)


def sequence(run):
    return house(run)


def multiset(run):
    """Order dropped: the step index removed, entries sorted."""
    return tuple(sorted((e.d, e.revision, e.grounds) for e in run.L))


def coarse(run):
    """The coordinate-list presentation: which coordinates were revised under a
    license, nothing else."""
    from .model import coordinate_name
    return frozenset(coordinate_name(e.revision[0]) for e in run.L)


def refined(run):
    """The house trace with the policy's identity appended."""
    return house(run) + (("policy", run.policy),)


BY_NAME = {"house": house, "sequence": sequence, "multiset": multiset,
           "coarse": coarse, "refined": refined}
