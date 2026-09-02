"""The 2026-09-02 defeat model with standing made explicit.

The Lean of the previous round had `Licence.lic : Q -> K -> Ty -> X -> Prop` and a
`standsFor` with no participant argument, so `Answerable.contested` — which binds a
participant `b` and then asks a question not mentioning `b` — was satisfied by any
participant type with two elements. The standing half of D3 was vacuous.

**The Python model was not vacuous**, which is why its 24 fixtures passed and the
defect went unnoticed: `DefeatModel.stands_for_other` reads the *opener* of each
licence issue as its standing-holder, so a participant was there all along, implicitly.
This subclass makes it explicit, matching the repaired Lean
(`lic : Q -> A -> K -> Ty -> X -> Prop`), and adds the principal-relative form.

Licence entries here are `(holder, kappa, tau, x)` quadruples rather than the parent
class's `(kappa, tau, x)` triples; the parent's fixtures are untouched.
"""
from __future__ import annotations

import sys
import pathlib

_PREV = (pathlib.Path(__file__).resolve().parents[2]
         / "2026-09-02-unified-grounds-answerable-defeat" / "src")
if str(_PREV) not in sys.path:
    sys.path.insert(0, str(_PREV))

from defeat_model import (  # noqa: E402
    ANSWER,
    DISPOSE,
    SETTLE,
    DefeatModel,
    DefeatViolation,
    MassLedger,
    issue,
    settled,
)

__all__ = [
    "ANSWER", "DISPOSE", "SETTLE", "DefeatViolation", "MassLedger",
    "issue", "settled", "StandingModel",
]


class StandingModel(DefeatModel):
    """`licences[q]` is a set of `(holder, kappa, tau, x)`: issue `q` licenses
    participant `holder` to hold anchor `kappa` for `(tau, x)`."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.edge_holders = {}      # (q, successor) -> holders at the disposal's batch

    def stands_for(self, holder, kappa, tau, x):
        """`b |-_n (kappa, tau, x)`. The participant is now an argument, which is the
        whole of the repair."""
        return any(
            (holder, kappa, tau, x) in self.licences.get(q, ()) for q in self.O
        )

    def standing_holders(self, s):
        """Everyone with standing on successor `s`, read off its anchor."""
        tau, x, _ = self.anchor[s]
        return {
            h
            for q in self.O
            for (h, _k, t, xx) in self.licences.get(q, ())
            if (t, xx) == (tau, x)
        }

    def stands_for_other(self, s, resolver):
        """D3's standing side: somebody other than the resolver holds standing."""
        return bool(self.standing_holders(s) - {resolver})

    def check_answerable(self, n, q, grounds, successors, resolver):
        """As the parent, and additionally **snapshot the standing-holders at `n`**.

        Standing is read at the strict prefix, matching the Lean's `standsFor Li n b`.
        Reading it at the end of the trace instead is wrong and silently so: a licence
        answered away later would retroactively remove standing from an edge that had
        it at the time. The `principal_absent_from_one` fixture is exactly that case.
        """
        super().check_answerable(n, q, grounds, successors, resolver)
        for s in successors:
            self.edge_holders[(q, s)] = self.standing_holders(s)

    # ---- the principal-relative form ---------------------------------------
    def answerable_for(self, principal, q, s):
        """`AnswerableFor P`: `P` held standing on successor `s` **at the batch the
        disposal happened**, which is the snapshot and not the live set."""
        return principal in self.edge_holders.get((q, s), set())

    def principal_holds_throughout(self, principal):
        """Every disposal successor had `P` among its standing-holders at its own batch.

        This is the P-relative laundering theorem's hypothesis; when it holds, no
        coalition excluding `P` holds all the standing on any edge of any walk.
        """
        return all(
            self.answerable_for(principal, q, s)
            for (q, s, _r, _g) in self.disposal_edges
        )

    def coalition_walks_excluding(self, principal):
        """Disposal edges whose standing-holders all avoid `principal`. Empty exactly
        when `principal_holds_throughout` — the P-relative theorem, computed."""
        return [
            (q, s, r)
            for (q, s, r, _g) in self.disposal_edges
            if principal not in self.edge_holders.get((q, s), set())
        ]

    def single_handed_edges(self):
        """Edges in one hand on **both** sides: the resolver opened every issue ground
        and is the only standing-holder on the successor. A disciplined trace has none,
        and after the repair the standing clause alone rules them out."""
        out = []
        for (q, s, r, g) in self.disposal_edges:
            grounds_own = all(
                self.opener.get(v) == r for (tag, v) in g if tag == "issue"
            )
            standing_own = self.edge_holders.get((q, s), set()) <= {r}
            if grounds_own and standing_own:
                out.append((q, s, r))
        return out
