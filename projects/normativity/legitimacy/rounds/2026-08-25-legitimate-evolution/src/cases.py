"""The records this round needed and the Carroll round did not have.

Four, and each exists because a clause of `LegitSucc` or of the certificate is
decided by it. The Carroll round's own fixtures carry everything else and are
imported rather than restated: `C7b` for a legitimate lineage from a seed, `C10`
and `C23` for manufactured and laundered authority, `C11` for two trajectories to
one endpoint, `C14` and `C33` for genuine content change.

Nothing here adds a historical event kind. `Transfer` and `Supersede` are the
core's own effects and `PProto` its own payload.
"""
from __future__ import annotations

import ri_core as ri

import carroll_cases as cc
import enrichment as en
import fixtures as fx


USER = fx.USER
AI = fx.AI
OTHER = "P_B"

PARENT = "auth.parent"
DELEGABLE = "auth.delegable"
CONST_TRANSFER = "const.transfer"
CONST_SPLIT = "const.split"
CONST_REVOKE_TAINTED = "const.revoke-tainted"
CONST_REVOKE = "const.revoke"

#: `Supersede` at `tau = 3` mints `@s3.0` and `@s3.1`; the revoking schema names
#: the second, and the id is fixed by `tag(tau, i)` rather than chosen.
LEFT = ri.standing_tag(3, 0)
RIGHT = ri.standing_tag(3, 1)


def _proto(pid: str) -> ri.PProto:
    return ri.PProto(fx.trainer_protocol(pid))


# --------------------------------------------------- delegation by transfer


def delegated_custody(answered: bool = True) -> dict:
    """Authority moves to another principal; the object does not move at all.

    `applyEffect` is the identity on a `Transfer`, so `auth.delegable` keeps its
    id, its payload and its `pred`. What changes is the debtor of its current
    episode. With `answered=False` the disposed episode is never responded to
    and stays `Due`: every authority-side clause holds and answerability
    continuity fails.
    """
    m = cc.ai_personal_trainer()
    s = fx.seed({DELEGABLE: _proto("p:delegable"),
                 CONST_TRANSFER: ri.PAuth(
                     ri.transferring("transfer", DELEGABLE, OTHER))})
    b = en.CaseBuilder(m, s, fx.narrative("delegated custody", "D"))
    b.settle("s:handover")
    b.reason("r:handover", s_L={"s:handover"}, target="v:delegate")
    b.norm("a:transfer", CONST_TRANSFER, USER, leaves={"r:handover"})
    disposed = seed_root(s, DELEGABLE)
    if answered:
        b.respond("rho:handover", roots={disposed}, cited={"a:transfer"})
    return {"case": b.build(), "standing": DELEGABLE, "event": "a:transfer",
            "disposed_root": disposed, "successor_root": ri.root_tag(3, 0)}


# ------------------------------------------------------ split, and a branch


def split_with_due_branch() -> dict:
    """One supersession, two successors, and one of them left unanswered.

    The lineage to `LEFT` is legitimate and its own edge is answered. The
    lineage to `RIGHT` ends in a revocation whose episode nobody answers, so
    `ContinuityOK` fails at the base while every clause a chain certificate for
    `LEFT` can carry holds.
    """
    m = cc.ai_personal_trainer()
    s = fx.seed({PARENT: _proto("p:parent"),
                 CONST_SPLIT: ri.PAuth(ri.superseding(
                     "split", {PARENT}, (_proto("p:left"), _proto("p:right")))),
                 CONST_REVOKE: ri.PAuth(ri.superseding("revoke", {RIGHT}, ()))})
    b = en.CaseBuilder(m, s, fx.narrative("split with a due branch", "D"))
    b.settle("s:review")
    b.reason("r:split", s_L={"s:review"}, target="v:split")
    b.norm("a:split", CONST_SPLIT, USER, leaves={"r:split"})
    parent_root = seed_root(s, PARENT)
    b.respond("rho:split", roots={parent_root}, cited={"a:split"})
    b.reason("r:revoke", s_L={"s:review"}, target="v:revoke")
    b.norm("a:revoke", CONST_REVOKE, USER, leaves={"r:revoke"})
    return {"case": b.build(), "base": PARENT, "left": LEFT, "right": RIGHT,
            "base_root": parent_root, "right_root": ri.root_tag(3, 1),
            "event": "a:split"}


# ------------------------------------------ effects that change in one part


CONST_PARTIAL = "const.partial"


def _partial(wit, pre):
    """One `Create`, two payloads, and only the second reads the pre-state.

    The first payload is a function of the witness alone; the second names the
    number of reasons on the ledger. Excising an episode that contributed a
    reason therefore changes the effect **and leaves the first payload alone**.
    """
    return ri.Standing(ri.Create((
        _proto("p:fixed"),
        _proto(f"p:var-{len(pre.R)}"),
    )))


def partial_effect() -> dict:
    """The record that separates the two exercise identities.

    ```text
    identity = "event"    the event is admitted in the excised replay, so the
                          exercise survives, and `@s5.1` does not: L3 fails
    identity = "effect"   the effect differs, so the exercise does not survive,
                          and `@s5.0` does: L3' fails
    ```

    Both are the same record and the same defect. Pre-state-blindness is what
    discharges either, which is why the round does not treat it as an artefact of
    a coarse realization map.
    """
    m = cc.ai_personal_trainer()
    s = fx.seed({CONST_PARTIAL: ri.PAuth(ri.SchemaCode("partial", _partial))})
    b = en.CaseBuilder(m, s, fx.narrative("partial effect", "D"))
    b.begin("E")
    b.settle("s:influence")                                   # tau 1
    b.end()
    b.reason("r:noise", s_L={"s:influence"}, target="v:noise")  # tau 2
    b.settle("s:ordinary")                                    # tau 3
    b.reason("r:ground", s_L={"s:ordinary"}, target="v:ground")  # tau 4
    b.norm("a:mint", CONST_PARTIAL, USER, leaves={"r:ground"})   # tau 5
    return {"case": b.build(), "event": "a:mint", "episode": "E",
            "unchanged": ri.standing_tag(5, 0), "changed": ri.standing_tag(5, 1)}


# ------------------------------------------- cleanup, in the record calculus


def record_cleanup() -> dict:
    """Revoking an illegitimate standing and separately creating a replacement.

    Two events. The revocation acts on the tainted standing and issues nothing;
    the creation issues under a seeded authority and inherits from nothing. So
    the replacement has no illegitimate parent, and the record calculus can
    express a cleanup without the successor inheriting the taint — which is what
    `affected` and `parents` being two fields amounts to here.
    """
    m = cc.ai_personal_trainer()
    tainted = ri.standing_tag(3, 0)
    s = fx.seed({CONST_REVOKE_TAINTED: ri.PAuth(
        ri.superseding("revoke-tainted", {tainted}, ()))})
    b = en.CaseBuilder(m, s, fx.narrative("record cleanup", "D"))
    b.begin("E")
    b.settle("s:influence")                                   # tau 1
    b.end()
    b.reason("r:influenced", s_L={"s:influence"}, target="v:install")  # tau 2
    b.norm("a:plant", fx.CONST_CREATE, USER,
           wit=(_proto("p:tainted"),), leaves={"r:influenced"})        # tau 3
    b.settle("s:audit")                                       # tau 4
    b.reason("r:audit", s_L={"s:audit"}, target="v:revoke")   # tau 5
    b.norm("a:revoke", CONST_REVOKE_TAINTED, USER, leaves={"r:audit"})  # tau 6
    b.norm("a:replace", fx.CONST_CREATE, USER,
           wit=(_proto("p:proper"),), leaves={"r:audit"})     # tau 7
    return {"case": b.build(), "tainted": tainted, "episode": "E",
            "replacement": ri.standing_tag(7, 0)}


# ------------------------------------------------ a force-bearing frontier


CONST_ISSUE_FORCE = "const.issue-force"
CONST_REVISE_FORCE = "const.revise-force"


def force_bearing() -> dict:
    """A norm issued, legitimately superseded, and one manufactured beside it.

    `PForce` standing is what the operative projection reads, so this is the
    record on which `NormView` is a real set rather than an empty one. Three
    injunctions:

    ```text
    @s3.0   issued under a seeded authority on an ordinary settlement
    @s6.0   its legitimate successor, saying something else
    @s9.0   issued inside an influence episode
    ```

    The frontier at the end holds the successor and not the first; the
    manufactured one is live and outside it. That pairing — *legitimately live*
    against merely *live* — is what the enforcement consumer needs and what a
    projection of `Std_t` alone cannot give it.
    """
    m = cc.ai_personal_trainer()
    first = ri.standing_tag(3, 0)
    s = fx.seed({
        CONST_ISSUE_FORCE: ri.PAuth(ri.creating(
            "issue-force", (ri.PForce("c:one", "s:one", "J1"),))),
        CONST_REVISE_FORCE: ri.PAuth(ri.superseding(
            "revise-force", {first}, (ri.PForce("c:two", "s:two", "J2"),))),
    })
    b = en.CaseBuilder(m, s, fx.narrative("force bearing", "D"))
    b.settle("s:mandate")                                       # tau 1
    b.reason("r:mandate", s_L={"s:mandate"}, target="v:issue")   # tau 2
    b.norm("a:issue", CONST_ISSUE_FORCE, USER, leaves={"r:mandate"})   # tau 3
    b.settle("s:review")                                        # tau 4
    b.reason("r:review", s_L={"s:review"}, target="v:revise")    # tau 5
    b.norm("a:revise", CONST_REVISE_FORCE, USER, leaves={"r:review"})  # tau 6
    b.begin("E")
    b.settle("s:capture")                                       # tau 7
    b.end()
    b.reason("r:capture", s_L={"s:capture"}, target="v:capture")  # tau 8
    b.norm("a:capture", fx.CONST_CREATE, USER,
           wit=(ri.PForce("c:three", "s:three", "J3"),),
           leaves={"r:capture"})                                # tau 9
    return {"case": b.build(), "first": first,
            "successor": ri.standing_tag(6, 0),
            "manufactured": ri.standing_tag(9, 0), "episode": "E"}


# ------------------------------------------------------------- conveniences


def seed_root(seed: ri.Seed, x: str) -> str:
    """The genesis root whose subject is `x`. `WFSeed` Z3 makes it unique."""
    found = [q.id for q in seed.roots0 if q.subject == x]
    assert len(found) == 1, f"{x}: {found}"
    return found[0]
