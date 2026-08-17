# Follow-up dispatch — traderized enforcement

Continue work on the existing `traderized-enforcement` branch / PR #38. **Do not
start over and do not discard the research already in the PR.** The existing
mathematical results, negative results, source audit, Lean work, fixtures, and
conservative evidence labels are valuable.

This follow-up corrects the architectural question the first pass answered.

## Central correction

The previous pass implicitly asked: *can traderization replace the settlement /
answerability / SI-minus architecture?* That is **not** the intended replacement
question. The intended question is: **can traderization replace a specially
constrained market maker as our general story for how an admissibility constraint
acquires operative force?**

The working architectural hypothesis is now

    constraint source / constitution → K_t → feasibility + presentation
        → constraint-to-trade compiler → E_t → ordinary LI market maker

with ordinary traders / TradingFirm also entering the ordinary LI market maker.
The constitution/source layer determines what constraints deserve force;
settlement still provides reports, timing, persistence and grounding; feasibility
machinery checks the constraint is coherent and nonempty; answerability determines
who may write, revise, object, breach or be held responsible; legitimacy asks
whether a source deserves this power; traderization is the force mechanism; and
the market maker stays as close as possible to the ordinary Logical Induction
market maker.

    OLD: constraint source → K_t → specially constrained market maker → P_t
    NEW: constraint source → K_t → enforcement trader → ordinary LI market maker → P_t

Do **not** treat the fact that traderization does not itself construct `K_t`,
check its legitimacy, guarantee persistence, or diagnose emptiness as evidence
against this replacement. Those are upstream constitutional/interface
responsibilities unless a proof genuinely shows enforcement cannot be modularized
from them.

The full dispatch, sections 1 through 11, is reproduced verbatim in the pull
request's follow-up description and covers: preserving and reinterpreting the
first pass's results; separating the force interface from its implementations;
the `theta`-admissible/core-minimum polytope as a direct compiler input;
treating emptiness and `D1` as upstream; the exactness fork (compiler weakness /
impossibility / limit-only / unnecessary); reopening the safety condition below
world-inclusiveness; reconstructing answerability around a mechanical force layer;
deduction as calibration case rather than whole generalization; the desired
five-theory decomposition; the required revisions to the PR's conceptual
surfaces; and the six-part verdict format.
