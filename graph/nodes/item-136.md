---
id: item-136
kind: leaf
leaf_kind: task
action: "Execute item 136 per its deliverable shape and acceptance check: Whether the classification of a change and the baseline survive re-encoding; the moving baseline over several steps."
who: agent
item: "136"
title: "Whether the classification of a change and the baseline survive re-encoding; the moving baseline over several steps"
section: "Normativity line — legitimacy"
maintainer_order: 148
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — modules under `account/` of the prosecution round: a stated class of re-encodings of a scene and, for each of M, A and the baseline's update, a proof on paper that it is invariant under the class or the smallest scene on which it is not; a model of several steps with a randomising adviser and more than one history at a step; the baseline under the two senses of alteration and under clause I as a third condition, each with the grain at which a step is judged stated; predictions frozen before the code on the four benchmark examples and on the chain of `blocks/RESULTS.md` 5.4; a second rendering of each case of `account/CASES.md` written without sight of the first; and statements in `account/RESULTS.md`, each with one status, giving for each sense of alteration a bound on the loss, by her starting baseline, of a run of clean changes, or the run that defeats it."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each new statement, the invariance statements among them; the baseline on each benchmark example under each sense of alteration; the number of the 45 cases on which the two renderings give the same M, A and I; C16 and C34 classified under each condition."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
  - {kind: decision, ref: 2026-11-13--blocks-setting-readings}
  - {kind: decision, ref: 2026-11-14--estimates-account-readings}
  - {kind: decision, ref: 2026-11-16--consolidated-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_CHANGE.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BENCHMARK.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 8
---
## Statement
Item 136, Whether the classification of a change and the baseline survive re-encoding; the moving baseline over several steps, is delivered in the shape its entry states: `test-supported` — modules under `account/` of the prosecution round: a stated class of re-encodings of a scene and, for each of M, A and the baseline's update, a proof on paper that it is invariant under the class or the smallest scene on which it is not; a model of several steps with a randomising adviser and more than one history at a step; the baseline under the two senses of alteration and under clause I as a third condition, each with the grain at which a step is judged stated; predictions frozen before the code on the four benchmark examples and on the chain of `blocks/RESULTS.md` 5.4; a second rendering of each case of `account/CASES.md` written without sight of the first; and statements in `account/RESULTS.md`, each with one status, giving for each sense of alteration a bound on the loss, by her starting baseline, of a run of clean changes, or the run that defeats it.

## Source
ATTENTION.md, item 136 (Whether the classification of a change and the baseline survive re-encoding; the moving baseline over several steps); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/ACCOUNT.md` (§4, §8, §9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_CHANGE.md` (§3–§6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BENCHMARK.md` (§2, §3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 5.1–5.7), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Eighth follow-up*).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's eighth follow-up (PROMPT-followup-8.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of account/ACCOUNT.md leaves open.

## Item
In the account of `account/ACCOUNT.md` of the prosecution round her true utility is her baseline way of
valuing applied to the true values, and the baseline follows her way of valuing through every step in which
her adviser neither induced a mistake nor altered her without her say. The eighth follow-up computes it on
four published examples (`account/BENCHMARK.md`) and tests on 45 published cases the claim it rests on, that
an illegitimate change of her valuing runs through a mistake or is an alteration
(`account/VALUE_CHANGE.md`). It finds four things the account does not settle. A change she registers and
did not choose (upbringing, a nudge, exposure, a feed) is not an alteration as the account reads one, and
the benchmark's verdicts reverse when it is counted as one. A total over steps is needed and the verdict on
one example reverses with it. Two illegitimate changes have neither a mistake nor an alteration: a
preference reversed by the wording of a choice, and addictive design with everything disclosed and foreseen.
And eleven of 34 verdicts turn on a detail the case does not fix, every rendering being one executor's. The
account of manipulation as induced mistake is Noggle's (Robert Noggle, *Manipulation: Its Nature,
Mechanisms, and Moral Status* (Oxford University Press, 2025, doi:10.1093/9780198924920.001.0001), and "The
Mistake Account of Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951); the
benchmark is Carroll, Foote, Siththaranjan, Russell and Dragan, "AI Alignment with Changing and
Influenceable Reward Functions", ICML 2024, arXiv:2405.17713.

Wanted first: with her observations, choices, trajectories, forecasts, her say, the adviser's role and the
facts held fixed, whether M, A and the baseline's updates are the same under every encoding that moves
cognitive state between her appraisals and her way of valuing, or that refines a step without changing the
episode; a theorem or a minimal counterexample (the conspiracy example is encoded both ways in that pass).
Then: one model of several steps, with an adviser that may randomise and several histories at a step, in
which the baseline is computed under each sense of alteration (direct only; anything not through her
appraisals and her choice) and with the invariance clause of the addendum as a third condition; the 45 cases
rendered a second time, independently, to say how far a verdict is the rendering's; and either a bound on
what a run of clean changes can cost her by the baseline she started with or the run that defeats it, the
fifth follow-up's chain (`blocks/RESULTS.md`, 5.4) among those tried

*Deliverable shape:* `test-supported` — modules under `account/` of the prosecution round: a stated class of re-encodings of a scene and, for each of M, A and the baseline's update, a proof on paper that it is invariant under the class or the smallest scene on which it is not; a model of several steps with a randomising adviser and more than one history at a step; the baseline under the two senses of alteration and under clause I as a third condition, each with the grain at which a step is judged stated; predictions frozen before the code on the four benchmark examples and on the chain of `blocks/RESULTS.md` 5.4; a second rendering of each case of `account/CASES.md` written without sight of the first; and statements in `account/RESULTS.md`, each with one status, giving for each sense of alteration a bound on the loss, by her starting baseline, of a run of clean changes, or the run that defeats it.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each new statement, the invariance statements among them; the baseline on each benchmark example under each sense of alteration; the number of the 45 cases on which the two renderings give the same M, A and I; C16 and C34 classified under each condition.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/ACCOUNT.md` (§4, §8, §9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VALUE_CHANGE.md` (§3–§6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BENCHMARK.md` (§2, §3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 5.1–5.7), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Eighth follow-up*).
