"""The composed interface.

Four clauses over a variation class, and the composition is a conjunction because
the prosecution found no theorem letting any of them absorb another.

```
answerability      predicates of the record          imported, unchanged
coverage           one run against what was due      not counterfactual
access             policies against each other       counterfactual
non-capture        policies against each other       counterfactual
```

`coverage` and `access` are the two halves the round had to separate: a class
every member of which withholds the same due reason satisfies `access` and fails
`coverage`, and an advisor that alone withholds it fails `access` while a single
arm of it can pass `coverage`.
"""

from __future__ import annotations

from typing import Sequence

from coverage import coverage
from fixture import Fixture, Policy
from noncapture import access, non_capture, uncoupled_pairs
from response import alphabet_of, process_projection


def clauses(fixture: Fixture, variation: Sequence[Policy]) -> dict:
    """Every clause's verdict on one class, separately.

    Separately because the round's results are about which clause catches what,
    and a single boolean would hide all of them.
    """
    alphabet = alphabet_of(fixture)
    return {
        "answerability": tuple(
            sorted({code for policy in variation
                    for code in fixture.run(policy).four().codes()})),
        "coverage": tuple(sorted({code for policy in variation
                                  for code in coverage(fixture, policy)})),
        "access": access(fixture, variation),
        "non_capture": non_capture(fixture, variation,
                                   process_projection(alphabet)),
        "uncoupled": uncoupled_pairs(fixture, variation),
    }


def legitimate(fixture: Fixture, variation: Sequence[Policy]) -> bool:
    return not any(clauses(fixture, variation).values())


def target_holds(fixture: Fixture, variation: Sequence[Policy]) -> bool:
    """Whether the environment-relative target holds on every arm.

    Not a clause. It is what the interface is graded against, and the two
    disagree deliberately in both directions — autonomous error fails it and is
    legitimate, and no scenario here is illegitimate while meeting it.
    """
    return all(fixture.run(policy).target().legitimate for policy in variation)
