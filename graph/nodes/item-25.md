---
id: item-25
kind: leaf
leaf_kind: task
action: "Execute item 25 per its deliverable shape and acceptance check: Bound the near-indifference leakage, or show it cannot be bounded."
who: agent
item: "25"
title: "Bound the near-indifference leakage, or show it cannot be bounded"
section: "Deference line — second wave"
maintainer_order: 65
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "the refuting family as a `witness-checked` instance with exact rationals; or a `lean-proved` bound on the leakage under a stated non-circular hypothesis, with an inhabitation witness."
acceptance: "the house `witness` checker accepts the instance; or the `lean` gate builds and audits clean with a typechecking witness."
context: ["prompts/2026-08-11-corrigibility-phase-ii/REPORT.md", "prompts/2026-08-11-phase-ii-competence/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 335 words"
version: 1
---
## Statement
A solution to item 25 ships the verdict, plus an explicit statement of whether the competence candidate survives it, plus — if the bound exists — whether the bounding hypothesis is itself credence-free or is a joint competence–credence hypothesis under skeleton v2 §2a.

## Source
PRIORITIES.md, item 25 (Bound the near-indifference leakage, or show it cannot be bounded); its context: `prompts/2026-08-11-phase-ii-competence/REPORT.md` §1.6, §4.3 and §10; `prompts/2026-08-11-corrigibility-phase-ii/REPORT.md` §9.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The controlling competence question after Stage II, and the one item that decides whether
the surviving competence candidate has any finite consequence at all.

Margin-gated calibration — *the principal's grades are calibrated where the principal is
decisive* — is the only non-circular candidate found. It supports

```
Δ_𝒞  ≤  2η  +  2B · P(γ_n < γ̄)
```

and asserts nothing on `{γ_n < γ̄}` by construction. The second term is **not** a
competence claim: it is the agent's credence mass on the principal's near-indifference
region, a fact about a different object. Unbounded, it makes the bound `2η + 2B`, which
is vacuous.

Decide the question in the sharp negative shape, which is the cheaper direction: exhibit
a family in which margin-gated calibration holds at `η = 0`, the decision-time margin
estimate `γ̂_n ≥ γ̄ + 2s` on the certified event, the trust tolerance holds at `ε_n → 0`,
and `Δ_{𝒞_fix} → 2B` anyway — or prove no such family exists.

The one partial lead is a relocation, not a bound. Under the trust tolerance the gate is
estimable at decision time — `|γ_n − γ̂_n| ≤ 2η_n` pointwise and attained — so
`P(γ_n < γ̄) ≤ P(γ̂_n < γ̄ + 2s) + ε_n/s` for every rational `s > 0`, the first term
computable at `t(n)` from the model's grades alone. Nothing bounds that first term, and
whether relocating the leakage into a decision-time observable suffices **is** the
question.

*Deliverable shape:* the refuting family as a `witness-checked` instance with exact
rationals; or a `lean-proved` bound on the leakage under a stated non-circular hypothesis,
with an inhabitation witness.
*Acceptance check:* the house `witness` checker accepts the instance; or the `lean` gate
builds and audits clean with a typechecking witness.
*Context:* `prompts/2026-08-11-phase-ii-competence/REPORT.md` §1.6, §4.3 and §10;
`prompts/2026-08-11-corrigibility-phase-ii/REPORT.md` §9.
*A solution ships:* the verdict, plus an explicit statement of whether the competence
candidate survives it, plus — if the bound exists — whether the bounding hypothesis is
itself credence-free or is a joint competence–credence hypothesis under skeleton v2 §2a.
