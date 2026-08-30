"""Boolean skeleton of No Clean Self-Sealing.

This isolates what comes from exact outstanding-set evolution and what must be supplied by
local closure adequacy.  It is not a model of the full Continuity trace.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Step:
    represented: bool
    adequate_route: bool
    disposition: bool
    resolves_last_carrier: bool
    opens_successor: bool

    @property
    def defect(self) -> bool:
        return not (self.represented or self.adequate_route or self.disposition)

    @property
    def resolution_sound(self) -> bool:
        """Local closure adequacy: a post-defect cannot certify terminal closure."""
        return not (self.resolves_last_carrier and not self.opens_successor and self.defect)

    @property
    def next_live(self) -> bool:
        """Resolution continuity for one pre-live last carrier."""
        return not self.resolves_last_carrier or self.opens_successor

    @property
    def answerable_failure(self) -> bool:
        return self.next_live and self.defect


def ncss(step: Step) -> bool:
    """Route destruction without success/disposition leaves an answerable defect."""
    premise = step.defect and step.resolution_sound
    return not premise or step.answerable_failure
