# Report — φ-regret preparation

**Prompt author:** GPT-5.6 Sol · **Executor:** Claude Opus 5 (Anthropic) ·
**Dispatched and executed:** 2026-08-11 · **Branch:**
`research/phi-regret-prep-20260811` from `9e37c4f`

The work product is `projects/leverage/rounds/2026-08-11-phi-regret-prep/`, and
its `COMPLETION_AUDIT.md` is the mechanical account: files, tests, what is
specified, what stays parametric, which conjectures survived, the strongest
statement established and the strongest not. This report is the rest — what the
round decided, what it did not show, what it deviated from, and what it reserves.

## What was built

A finite substrate on which "did the learner have low regret against the lawful
repairs its own record licensed?" is a question with a computable answer. The
substrate's one structural commitment is that legality and advantage are decided
by different machinery: a certificate is checked through a reader with a declared
footprint that omits the charge table, so a check consulting what an edit saves
raises rather than returning. This is the objection grammar's `GR-J1` discipline
reused, and a test writes a guard that tries.

Thirteen experiments, fifteen fixtures, 25 tests, exact rationals. Five witnesses
refuse edits that would have paid; three measure what admitted edits are worth;
four measure what each v1 replay restriction costs; one separates affordability
from charge.

## The finding

Bounded counterfactual influence is **sharply conditional, and fencing is not the
condition.** The dispatch expected it to be. One history, one lawful edit at date
0, four accounting configurations:

| configuration | `T = 12` | `T = 24` |
|---|---|---|
| the edit's account holds only the edited occasion | 2 | 2 |
| solvency coupling off | 2 | 2 |
| **one fenced account for the whole run** | **24** | **48** |
| pooled | 24 | 48 |

The third row is a fence. Nothing is shared with any other stream, and the
divergence still grows linearly in the horizon, from a single edit at a single
occasion. The mechanism is not money: exhausting a reserve withdraws merits
service, so one edit can decide whether a stream stays able to rule at all, and
that plays out over every occasion the stream ever sees.

So the fenced accounting lemma — divergence bounded by the touched accounts'
admitted lifetime liability — is true, is tight, and is empty at run-sized
granularity. The condition that makes replay-based φ-regret a standard object is
the absence of the solvency coupling, or fences short enough that their lifetime
liability is not horizon-sized. `PHI_REGRET_TEST_SPEC.md` declares the first of
those, and says it is a declaration.

## What this round does not establish

**Any regret bound.** None was attempted. `E4`'s linear advantage is what a
failure looks like, not evidence about what any learner achieves.

**That the standard machinery applies.** The Blum–Mansour reduction is
*conjectured* to instantiate. The guard is measurable before the action, which is
the condition it needs; the per-occasion action set varies with the bound
schedule, which the standard statement does not have to handle. Nobody has
checked it line by line.

**That the interface is adequate.** Three of nine checks rest on supplied
relations, and the supplied `BearsOn` is a bookkeeping relation wearing the name
of a normative one: it asks whether a record declares a coordinate and names the
occasion. Whether a substantively adequate one exists is untouched.

**That the licence declarations are right.** Scope discipline is checked against
a `licenses` field on each reason record, and nothing decides whether a record's
declared licences are correct. This is the same shape as the consolidation's open
registry-completeness problem and inherits its standing.

**That the obligation adapter is faithful.** It reimplements rather than imports,
and no cross-check was run. It may coarsen distinctions the ledger draws: the
ledger separates withdrawal from loss and this substrate does not.

**Anything about coverage.** Φ_law is a declared list. A remediable failure absent
from it generates no regret however costly and however lawful the repair, and the
learner is under no pressure from this machinery to notice. That gap is the whole
distance between "does not persist in a mistake it can see" and "does not persist
in a mistake."

**That `unresolved` is a coherent verdict.** A comparator whose firing is
`unresolved` does not fire, so operationally it is a rejection and the
distinction lives in the report. Either it becomes a real third status with
consequences or it is a label on a rejection; the round chose neither and says so
in `OPEN_PROBLEMS.md` §5.

## Deviations

1. **Three experiments beyond the E-list.** `E10b` and `E10c` isolate fence
   granularity from the solvency coupling; without them the round reports a false
   conclusion. `E13` is the resource-feasibility witness acceptance criterion F
   requires and the list omits.
2. **A trust-chain edit.** `tests/path_gate.py` gains
   `projects/leverage/deck-2026-08-10/**` as a specification pattern and two
   self-test cases. The dispatch did not scope it; the mid-round addendum asked
   for the deck in the repository, and an unlisted path defaults to the proof
   layer, so without it a contributor pull request could rewrite the author's own
   talk. Flagged for confirmation; it only removes contributor write access.
3. **Adapter rather than import** for the answerability algebra, because its only
   executable form declares itself deletable. Filed as friction F4.
4. **`FOR_HUMANS.md` added**, not in the required package. The dual-register rule
   is binding on every substantive deliverable.
5. **`E11`'s expected numbers were wrong in the design and are corrected in the
   record.** The replayed-prefix guard was expected to fire once; it fires twice,
   because the unedited second occasion restores the decline the guard reads by
   the third. The experiment's stated expectation and the test both carry the
   observed behaviour, which is a sharper witness than the predicted one.

## Structural defect filed

**F4 — a layer's theory is authoritative and its only code is in a disposable
tree.** `consolidation-aug9` states the answerability ledger and the case docket
in Theory 9 and carries their rows; its `src/` implements neither. The only
executable version of both is `projects/leverage/forward/src/`, which says of
itself that it may be deleted wholesale and is evidence for nothing. Every round
building on that layer pays a reimplementation. Three ways out are stated in
`PRIORITIES.md`; choosing one is not this round's to do.

## Items filed

`PRIORITIES.md` gains a *Leverage line — the learning track* section with items
29 (does the reduction instantiate), 30 (the learner and its consequence — the
controlling question), and 31 (does the objection grammar already represent a
remediable-pattern filing). Filed within the round's dispatched scope per
*Demand-gating*, with this directory's `PROMPT.md` as the authorization. No
existing item was renumbered or removed.

## New names introduced

All provisional, all flagged, none proposed for permanence:
**lawful-edit certificate** · **comparator class Φ_law** · **remediable failure
pattern** · **service window** · **fenced accounting lemma** · **admitted
lifetime liability** · **certifier footprint** · the obstruction-code vocabulary
(`certificate.*`, `edit.*`, `burden.*`) · the reason kinds *interval*,
*impediment*, *ripeness*, *authority*, *ratification*.

`Λ_s` and `ℓ_max` are notation, not names.

## Outstanding maintainer actions

Each is also a line in `DECISIONS.md`'s *Awaiting the author*, which is the queue.

1. **Confirm or revert the path-gate entry** for
   `projects/leverage/deck-2026-08-10/**` in `tests/path_gate.py`. One line and
   one self-test case to read. Reverting makes the deck contributor-editable.
2. **Rule on the deck's review status.** `PROVENANCE.md` now carries the leverage
   line's first `maintainer-reviewed` row, qualified: the deck marks its own
   frames — 22 as the author's language, two as still model-drafted — and the row
   points at those marks rather than asserting a flat label. Confirm that a
   self-marking artifact may carry a qualified status, or replace it with
   `ci-only` and lose the distinction the deck itself draws.
3. **Decide friction F4** — consolidate the answerability and docket modules,
   promote them out of `forward/`, or rule that adapters are the expected pattern.
4. **Name review** on the twelve provisional names above, under standard 6.
5. **Registry**, if wanted: nothing from this round is in
   `projects/leverage/CLAIMS.md`. The two derived statements — the fenced
   accounting lemma and its sharpness — are the only candidates, and both are
   `witness-checked` at best without a Lean port. Registering them would need an
   item they answer; item 29 is the natural one.

## The next task

> Given the frozen finite comparator and replay environment prepared here,
> determine whether exponential weights over Φ_law under the Blum–Mansour
> transformation reduction achieves sublinear Φ_law-regret, and whether that
> guarantee implies retirement of every positive-rate uniformly remediable failure
> pattern.

Item 30, with item 29 settled first. Nothing found here suggests the formulation
is ill-posed, so it should not be broadened.
