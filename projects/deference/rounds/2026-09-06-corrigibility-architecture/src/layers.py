"""Four layers kept apart, and No Laundered Authority Loss over the coverage bits.

The coverage state of one concern mirrors `CovState` in
`lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean` exactly:
`rel, disp, rep, adm, eff, reg, stands` (one route).  `covered` and `open_to` are the
Lean `Covered` / `OpenTo`; `actual_open` is `ActualOpen`.

Layers:
  debt        — the docket: which occurrences are live/answered/closed (Integrity).
  affordance  — whether the principal's correction channel actually works (`aff`).
  coverage    — what the openness semantics *reports* about the channel (`eff` bit) and
                about the docket (`rep` bit).
  behaviour   — not modelled here; see compliance.py.

Two bridges connect affordance and debt to coverage, and neither is a theorem:
  efficacy faithfulness      eff == aff
  registration faithfulness  rep == (a live occurrence anchored to the concern is in
                             the docket)
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Cov:
    rel: bool
    disp: bool
    rep: bool
    adm: bool
    eff: bool
    reg: bool
    stands: bool

    @property
    def active(self):
        return self.rel and not self.disp

    @property
    def live(self):
        return self.active and not self.rep

    @property
    def adequate(self):
        return self.adm and self.eff and self.reg

    @property
    def covered(self):
        return (not self.live) or self.adequate

    @property
    def open_to(self):
        return (not self.rel) or self.stands

    @property
    def actual_open(self):
        return self.covered and self.open_to


def all_cov():
    for bits in product((False, True), repeat=7):
        yield Cov(*bits)


# --- the debt layer ------------------------------------------------------------------

def integrity_step(docket, closes=(), admits=()):
    """One Integrity transition: live occurrences in `closes` become `closed`, fresh
    occurrences in `admits` are added live.  No fate is rewritten, nothing is removed."""
    new = dict(docket)
    for o in closes:
        assert new[o] == "live"
        new[o] = "closed"
    for o in admits:
        assert o not in new
        new[o] = "live"
    return new


def conservation(d0, d1):
    return all(o in d1 for o in d0) and all(
        d0[o] == "live" or d1[o] == d0[o] for o in d0)


# --- one state of the correction concern -----------------------------------------

@dataclass(frozen=True)
class State:
    aff: bool                 # the correction channel actually works
    corr: Cov                 # reported coverage state of the correction concern
    docket: dict              # occurrence -> fate
    restore_occ: str = "restore"


def efficacy_faithful(s: State) -> bool:
    return s.corr.eff == s.aff


def registration_faithful(s: State) -> bool:
    return s.corr.rep == (s.docket.get(s.restore_occ) == "live")


def open_at(s: State) -> bool:
    return s.corr.actual_open


def nlal_case(s: State) -> str:
    """Classify a state at which the affordance is lost (`aff == False`), assuming both
    faithfulness bridges.  Exactly one of:
      'amended'  — the concern is no longer applicable (rel false): the loss follows a
                   charter change, whose record is a closure receipt in the docket;
      'disposed' — an authorized disposition (Defeat Principle: load on a successor);
      'debt'     — the loss is represented: a live restoration occurrence in the docket;
      'illegit'  — the state is not open: the trajectory is not legitimate here."""
    if not open_at(s):
        return "illegit"
    if not s.corr.rel:
        return "amended"
    if s.corr.disp:
        return "disposed"
    if s.corr.rep:
        return "debt"
    return "laundered"   # unreachable under the two bridges; see the test
