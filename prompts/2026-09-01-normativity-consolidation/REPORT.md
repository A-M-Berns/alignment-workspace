# Report — September 2026 consolidation checkpoint

## Part I — PR75

Reviewed the affordability round in full at its final head, ran the round's 204
exact-rational fixtures and the whole workspace gate suite, and verified that the
canonical endpoint theorem is stated with all five hypotheses, that its three
asymptotic corollaries are correctly typed, and that no claim listed in the round's
own consistency audit survives anywhere as a current assertion.

**Two small inconsistencies were found and repaired before merge**, both of them
places where the ninth dispatch's repairs had not been propagated:

1. The frozen fixed-era theorem stated its transport term with a *uniform*
   stability constant, while Deferred Service Transfer had been generalized to an
   edge-dependent error contributing a claim-normalized average. The uniform
   constant is the special case, so the statements were true as written but a
   reader had to notice they differed. The frozen document now records the
   relationship explicitly and points at the sharpened form.
2. The closed-loop hierarchy's E2 row read the sharp persistence criterion as
   depth-only "in the normal regime" — a reading the seventh dispatch had
   restricted. The row now carries the exact form and names the engine-scale floor
   under which it reduces to the depth alone.

The PR body was checked against the twelve withdrawn claims and marks each
historical assertion as superseded where a later dispatch superseded it. It remains
chronological provenance, which is correct for a PR body.

All seven CI jobs green. **Merged**, squashed to `main`.

## Part II — the checkpoint

Branched from the post-merge `main`. No research was performed and no new
mathematics was derived, with one class of exception noted below.

### What was produced

A canonical checkpoint at
`projects/normativity/legitimacy/checkpoint-2026-09-01/`: current theory with an
audited dependency spine; a status ledger over fifty-seven results and interfaces;
a supersession map; sharply scoped open problems; a roadmap that also says what to
stop working on; the reconciliation of the conceptual answerability theory with the
service mathematics; an assessment of the candidate legitimacy decomposition; the
August-to-September reconciliation; extraction candidates; and a self-administered
final audit against the dispatch's sixteen questions.

The program-level prior-art note was extended rather than duplicated: every entry
now carries a role, and a new section covers the mathematical antecedents of the
service and affordability line.

Six new wiki pages and four updated ones. Repository navigation updated at the
project README and `RESEARCH_STATE.md`.

### The four findings worth naming

**The two theories meet at exactly one point, and it is a clean join.** The
conceptual answerability theory's service dichotomy ends at *"attention diverges"*.
The service mathematics begins at `A_N -> infinity`. The note names its own missing
piece — a reason-to-response structure plus a dynamic uptake condition — and that
piece is precisely Actionability plus Uptake, both of which now exist.

**Their budgets disagree, and the disagreement resolves favourably.** The note's
attention budget is renewable per stage; the mathematics' is a consumable lifetime
stock. Non-starvation is nearly free under the first and not under the second. The
reconciliation is that the same geometric-tranche construction works on both sides,
and the equivalence of persistence with eventual full service is the liability-priced
version of the note's feasibility witness — non-starvation survives at exactly one
price, `liminf L_t(1) = 0`, and no more.

**Disposition is the largest gap and it is three gaps at once.** The note permits
content to legitimately cease being owed; the mathematics has no analogue, and
claim mass is served or it persists. That single missing notion is where defeat
lives, is the obvious laundering channel, and changes the hypothesis the whole
persistence analysis rests on. Filed as `PRIORITIES.md` item 77.

**Three fixed-era results are probably rediscoveries.** The transfer theorem is in
substance a standard consequence of Le Cam contiguity; the interval feasibility
condition is a Gale–Hoffman / Horn-1974 specialization; serve-oldest-first is the
Jackson exchange argument. Each was derived independently here and each is now
recorded as adjacent prior art rather than as a contribution, with three further
places marked *literature review needed*.

### Judgments the checkpoint makes that its sources do not

Four, each marked as the checkpoint's own in the document that makes it: the
four-layer decomposition; the audit of the dependency spine, which moves
Actionability from downstream of allocation to beside it and separates the
normative demand from the force mechanism; the budget reconciliation above; and the
assessment of `Legitimacy = Answerability + Affordability + Non-capture` as a
**research framing, not canonical**, with two amendments — the first pillar must
include its semantic-authentication obligation, and affordability is better read as
a realizability side condition than a conjunct.

### Deviations from the dispatch

- The dispatch's candidate document names were mapped onto one directory rather
  than scattered at the project root, and `PRIOR_ART.md` extends the existing
  program note rather than becoming a second one, per the dispatch's own
  instruction not to duplicate a canonical file.
- No `CURRENT_THEORY.md` was placed at the repository root; navigation points at
  the checkpoint from `RESEARCH_STATE.md` and the project README instead.
- `Relation-to-the-Field` was left alone. It is explicitly reserved to the
  maintainer, and a new `Prior-Art` page was added beside it rather than filling it
  in.

### Blockers

None. The one input that could have been unavailable — the diachronic-answerability
note — was present and was read in full.

## Attribution

| field | value |
|---|---|
| prompt author | unrecorded — authored outside this repository |
| executor | Claude Opus 5 (Anthropic) |
| date | dispatched and executed 2026-09-01 |
| round record | `prompts/2026-09-01-normativity-consolidation/` |
