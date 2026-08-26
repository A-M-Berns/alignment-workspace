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


# ------------------------------------------------------------- conveniences


def seed_root(seed: ri.Seed, x: str) -> str:
    """The genesis root whose subject is `x`. `WFSeed` Z3 makes it unique."""
    found = [q.id for q in seed.roots0 if q.subject == x]
    assert len(found) == 1, f"{x}: {found}"
    return found[0]
