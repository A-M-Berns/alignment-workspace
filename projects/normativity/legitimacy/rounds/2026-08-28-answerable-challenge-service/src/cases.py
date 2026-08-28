"""ACS1-ACS13. The pinned episode is the hypothesis under prosecution."""
from __future__ import annotations

import service as sv

TARGET = "policy:dispatch"
AUTH = "rule:authority"
BASE_TERMS = sv.Terms(threshold=10.0, evaluator="Lambda0", protocol="A")


def ch(cid="c1", at=1, terms=None, target=TARGET) -> sv.Challenge:
    return sv.Challenge(cid, target, at, terms or BASE_TERMS)


def steady(cid, lo, hi, o=1.0, u=1.0) -> tuple:
    opp = {(cid, t): o for t in range(lo, hi)}
    ser = {(cid, t): u for t in range(lo, hi)}
    return opp, ser


def _d(horizon=40, register=None, global_terms=None, opportunity=None,
       served=None, defeated=None, transfers=None, addressed=None,
       unpinned=False, retroactive_admission=None, rate=1.0) -> sv.Docket:
    return sv.Docket(horizon=horizon, register=register or {},
                     global_terms=global_terms or {-1: BASE_TERMS},
                     opportunity=opportunity or {}, served=served or {},
                     defeated=defeated or {}, transfers=transfers or {},
                     addressed=addressed or {}, unpinned=unpinned,
                     retroactive_admission=retroactive_admission,
                     evidence_rate=rate)


# ------------------------------------------------------------------ ACS1-2


def acs1_silent_drop() -> sv.Record:
    """Registered, evidence begins accumulating, then simply de-registered.

    Modelled as the record no longer showing the registration, which is what
    de-registration means when the docket is the record.
    """
    c = ch()
    o, u = steady("c1", 1, 20)
    return sv.build("ACS1 silent drop after registration",
                    _d(register={1: (c,)}, opportunity=o, served=u,
                       retroactive_admission=lambda _c: False))


def acs2_retroactive_admission_rewrite() -> sv.Record:
    """A new admission standard says challenges of this form were never
    admissible, and the process recomputes its own history."""
    c = ch()
    o, u = steady("c1", 1, 20)
    return sv.build("ACS2 retroactive admission rewrite",
                    _d(register={1: (c,)}, opportunity=o, served=u,
                       retroactive_admission=lambda x: x.target != TARGET))


# ------------------------------------------------------------------ ACS3


def acs3_moving_threshold(unpinned=True) -> sv.Record:
    """The central attack. Threshold 10, evidence reaches 9, threshold becomes
    100, evidence reaches 90, threshold becomes 1000.

    Nothing is erased, nothing is rejected, and no reason is ever promoted. The
    question is whether pinning catches it.
    """
    c = ch(terms=BASE_TERMS)
    o, u = steady("c1", 1, 40)
    return sv.build("ACS3 moving threshold" + ("" if unpinned else " (pinned)"),
                    _d(horizon=40, register={1: (c,)}, opportunity=o, served=u,
                       global_terms={-1: BASE_TERMS,
                                     10: sv.Terms(100.0, "Lambda0", "A"),
                                     20: sv.Terms(1000.0, "Lambda0", "A")},
                       unpinned=unpinned))


def acs3_pinned() -> sv.Record:
    return acs3_moving_threshold(unpinned=False)


# ------------------------------------------------------------------ ACS4


def acs4_evaluator_change_mid_episode(unpinned=True) -> sv.Record:
    """The evaluator changes while the episode is open and the evidence is
    becoming threatening."""
    c = ch()
    o, u = steady("c1", 1, 30)
    return sv.build("ACS4 evaluator change mid-episode",
                    _d(horizon=30, register={1: (c,)}, opportunity=o, served=u,
                       global_terms={-1: BASE_TERMS,
                                     5: sv.Terms(10.0, "Lambda1", "A")},
                       unpinned=unpinned))


# ------------------------------------------------------------------ ACS5


def acs5_indefinite_starvation() -> sv.Record:
    """Open forever, opportunity recurs forever, nothing is ever served, and no
    defeater is cited.

    Frozen `A1` is entirely content with this: the claim stays outstanding, which
    is what it is supposed to do. Only the service premise sees it.
    """
    c = ch()
    o = {("c1", t): 1.0 for t in range(1, 40)}
    return sv.build("ACS5 indefinite starvation",
                    _d(register={1: (c,)}, opportunity=o, served={}))


# ------------------------------------------------------------------ ACS6-8


def acs6_resource_priority() -> sv.Record:
    """A standing priority rule says another challenge is served first.

    Non-address may be legitimate, and the theory must not demand universal
    immediate service.
    """
    c = ch()
    rule = sv.Defeater("d:priority", installed=0,
                       defeats=lambda x: x.target == TARGET)
    o = {("c1", t): 1.0 for t in range(1, 12)}
    return sv.build("ACS6 resource-priority defeater",
                    _d(register={1: (c,)}, opportunity=o, served={},
                       defeated={6: {"c1": rule}}))


def acs7_irrelevant_excuse() -> sv.Record:
    """An unrelated represented reason is cited as the defeater."""
    c = ch()
    junk = sv.Defeater("d:unrelated", installed=0,
                       defeats=lambda x: x.target == "policy:something-else")
    o, u = steady("c1", 1, 12)
    return sv.build("ACS7 irrelevant excuse token",
                    _d(register={1: (c,)}, opportunity=o, served=u,
                       defeated={6: {"c1": junk}}))


def acs8_post_hoc_exception() -> sv.Record:
    """The challenge starts succeeding, so a bespoke rule is written for it."""
    c = ch()
    bespoke = sv.Defeater("d:not-this-one", installed=7,
                          defeats=lambda x: x.cid == "c1")
    o, u = steady("c1", 1, 12)
    return sv.build("ACS8 post-hoc bespoke exception",
                    _d(register={1: (c,)}, opportunity=o, served=u,
                       defeated={8: {"c1": bespoke}}))


# ------------------------------------------------------------------ ACS9


def acs9_pre_existing_self_sealing() -> sv.Record:
    """A general rule, predating every challenge: *criticisms threatening
    authority are rejected*.

    Temporally clean and inferentially relevant. The structural theory accepts
    it, and the round says so rather than inventing a premise to make it fail.
    """
    c = ch(target=AUTH)
    seal = sv.Defeater("d:authority-shield", installed=0,
                       defeats=lambda x: x.target == AUTH)
    o, u = steady("c1", 1, 12)
    return sv.build("ACS9 pre-existing self-sealing rule",
                    _d(register={1: (c,)}, opportunity=o, served=u,
                       defeated={4: {"c1": seal}}))


# ------------------------------------------------------------------ ACS10-13


def acs10_explicit_transfer() -> sv.Record:
    """The process adopts a new protocol and explicitly carries the open
    challenge onto it."""
    c = ch()
    c2 = sv.Challenge("c1'", TARGET, 12, sv.Terms(10.0, "Lambda1", "A'"))
    o, u = steady("c1", 1, 12)
    o2, u2 = steady("c1'", 12, 30)
    o.update(o2)
    u.update(u2)
    return sv.build("ACS10 explicit transfer to a new protocol",
                    _d(horizon=30, register={1: (c,), 12: (c2,)},
                       opportunity=o, served=u,
                       global_terms={-1: BASE_TERMS,
                                     11: sv.Terms(10.0, "Lambda1", "A'")},
                       transfers={12: {"c1": "c1'"}}))


def acs11_challenge_the_defeater_rule() -> sv.Record:
    """After the self-sealing rule defeats one challenge, a second challenge is
    registered whose target is the rule itself.

    Ordinary machinery, no meta-hierarchy: the target is just an identifier.
    What this does **not** show is that the second challenge will be admitted.
    """
    c = ch(target=AUTH)
    seal = sv.Defeater("d:authority-shield", installed=0,
                       defeats=lambda x: x.target == AUTH)
    meta = sv.Challenge("c2", "d:authority-shield", 6, BASE_TERMS)
    o, u = steady("c1", 1, 6)
    o2, u2 = steady("c2", 6, 30)
    o.update(o2)
    u.update(u2)
    return sv.build("ACS11 challenge the defeater rule",
                    _d(horizon=30, register={1: (c,), 6: (meta,)},
                       opportunity=o, served=u, defeated={4: {"c1": seal}}))


def acs12_indistinguishable_worlds() -> tuple:
    """Two dockets with identical represented history; in one, decisive criticism
    exists externally and is never registered.

    Not a `Record` pair to be compared by a premise -- the point is that no
    predicate over represented history can separate them.
    """
    quiet = sv.build("ACS12a no criticism exists", _d(register={}))
    also_quiet = sv.build("ACS12b criticism exists, never registered",
                          _d(register={}))
    return quiet, also_quiet


def acs13_duplicate_challenges() -> sv.Record:
    """Two registrations of the same substantive criticism, merged by transfer."""
    a = sv.Challenge("c-a", TARGET, 1, BASE_TERMS)
    b = sv.Challenge("c-b", TARGET, 2, BASE_TERMS)
    merged = sv.Challenge("c-ab", TARGET, 4, BASE_TERMS)
    o, u = steady("c-ab", 4, 30)
    return sv.build("ACS13 duplicate challenges merged",
                    _d(horizon=30, register={1: (a,), 2: (b,), 4: (merged,)},
                       opportunity=o, served=u,
                       transfers={4: {"c-a": "c-ab", "c-b": "c-ab"}}))


def served_to_promotion() -> sv.Record:
    """The consumer lemma's positive case: open, served, promoted."""
    c = ch()
    o, u = steady("c1", 1, 30)
    return sv.build("consumer: service yields promotion",
                    _d(horizon=30, register={1: (c,)}, opportunity=o, served=u))


ALL = (acs1_silent_drop, acs2_retroactive_admission_rewrite,
       acs3_moving_threshold, acs3_pinned, acs4_evaluator_change_mid_episode,
       acs5_indefinite_starvation, acs6_resource_priority,
       acs7_irrelevant_excuse, acs8_post_hoc_exception,
       acs9_pre_existing_self_sealing, acs10_explicit_transfer,
       acs11_challenge_the_defeater_rule, acs13_duplicate_challenges,
       served_to_promotion)
