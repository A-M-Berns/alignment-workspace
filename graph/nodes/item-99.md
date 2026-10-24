---
id: item-99
kind: leaf
leaf_kind: task
action: "Execute item 99 per its deliverable shape and acceptance check: The allocation floor: delegation safety, allocation completeness, exact shortfall reporting, and the reach cone."
who: agent
item: "99"
title: "The allocation floor: delegation safety, allocation completeness, exact shortfall reporting, and the reach cone"
section: "Deference line — second wave"
maintainer_order: 92
difficulty: "substantial"
project: deference
dispatchable: true
item_status: open
deliverable: "the four properties as declared clauses of the evaluation ecosystem with checkers (a delegated-scope filter that rejects authority-removing effects; an allocation-change detector on declared effects; a shortfall monitor with a threshold-free reporting trigger; a reach cone with the agent quantified universally) and their `Realizes` witnesses; the reachable set, shortfall and materiality of the round's §4 Q7 as readings of the log; the lexical certificate on committed programs beside the nondelegation certificate of item 98; or the exact obstruction with its fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean; the round's delayed-effect, delegated-cut, salami and approved-successor fixtures reproduced against the declared clauses."
work:
  - {kind: decision, ref: 2026-09-25--corrigibility-faithfulness-allocation-stated-landed-frame}
  - {kind: decision, ref: 2026-09-25--rubber-stamping-legitimate-non-hollowness-retracted}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 841 words"
version: 1
---
## Statement
A solution to item 99 ships the clauses with their witnesses, or the negative with its fixture.

## Source
PRIORITIES.md, item 99 (The allocation floor: delegation safety, allocation completeness, exact shortfall reporting, and the reach cone); its context: `REPORT.md` §§2, 4 (Q1, Q7, Q8), 7 and `THEOREM.md` of the round; `ProtectedAuthorityTheorem.lean` §§1, 2, 5; `ReachableCorrectiveControl.lean` §12; item 98.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The protected-authority-theorem round (`projects/deference/rounds/2026-09-25-protected-authority-theorem/`)
states corrigibility as faithfulness to an allocation of authority on the landed
interaction frame: six violation predicates, the transform `𝔱` extending `𝔠`, and the
lexical score `S = S_ord − ϖ·n` with `ϖ > D` (`ProtectedAuthorityTheorem.lean`,
`THEOREM.md`).  Its results rest on four constitutional properties the theorem takes as
hypotheses and nothing on `main` certifies: (a) **delegation safety** — a delegated effect
never removes response authority (`DelSafe`; without it `𝔱π` is not corrigible,
`Witness.delegated_cut`); (b) **allocation completeness** — task moves preserve the
allocation, an allocation-changing effect is a declared amendment, no amendment is
delegated (`AllocComplete`; the "approved uncorrectable successor requires amendment, not
ordinary approval" rule); (c) the **exact reporting duty** — a report required at every
strict increase of the control shortfall, with no materiality threshold, since any
threshold admits a salami (`erosion_reported_or_missed`, `Witness.salami`); (d) the
**reach cone** for foreclosure — a contrastive rollout relation on physical states whose
faithfulness is external and which must quantify the agent's own future in a way the
`ReachableCorrectiveControl` §12 defects do not defeat (the round's finite model uses the
final-step cone with the agent's future fixed to idle).  Also unrealized: `ϖ > D` as a
certified property of the committed evaluator (the lexical twin of item 98's
nondelegation certificate), and a state-dependent `Del` for conditional delegation.

*Deliverable shape:* the four properties as declared clauses of the evaluation ecosystem
with checkers (a delegated-scope filter that rejects authority-removing effects; an
allocation-change detector on declared effects; a shortfall monitor with a threshold-free
reporting trigger; a reach cone with the agent quantified universally) and their `Realizes`
witnesses; the reachable set, shortfall and materiality of the round's §4 Q7 as readings
of the log; the lexical certificate on committed programs beside the nondelegation
certificate of item 98; or the exact obstruction with its fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean; the round's
delayed-effect, delegated-cut, salami and approved-successor fixtures reproduced against
the declared clauses.
*Context:* `REPORT.md` §§2, 4 (Q1, Q7, Q8), 7 and `THEOREM.md` of the round;
`ProtectedAuthorityTheorem.lean` §§1, 2, 5; `ReachableCorrectiveControl.lean` §12; item 98.
*Consumed by:* any adoption of `THEOREM.md` as `wiki/Corrigibility.md` §4 (queued in
`DECISIONS.md`); items 89, 97, 98.
*A solution ships:* the clauses with their witnesses, or the negative with its fixture.

*2026-09-25 (legitimacy-internal-external round):* the salami obstruction is against a
*per-step* threshold only; a *cumulative* threshold (report when the shortfall has grown by
`θ` since the last report) bounds unreported erosion by `θ` at every time
(`Legitimacy.unreported_lt`), so the exact-reporting clause may be relaxed to a cumulative
one.  The floor's certificates sit beside the segment gate, which is legitimacy's (not the
floor's) to supply.

*2026-09-25 (gate-is-legitimacy round):* rubber-stamping is legitimate (the retraction in
`DECISIONS.md`); the **atrophy residual** — that her capacity to override a trusted
advisor decays with disuse — is effectiveness, not legitimacy: it belongs here with
entrenchment and reporting, as a shortfall of her effective authority the reporting duty
must surface and the delegated-scope filter must not let a delegation silently become.
Also from that round: a self-checkable deviation from the declared consultation protocol
is a violation counted into `n` (`GateIsLegitimacy.deviation_finite`), which adds a
protocol-deviation clause to the floor's checkers beside the six declared violations.

*2026-09-25 (authority-module round):* the floor's clauses are restated on the per-matter
allocation `J`: delegation safety and allocation completeness are statements about `J`
(`AuthorityModule.DelSafeJ`, `AllocCompleteJ`, `delSafe_iff`, `allocComplete_iff`);
**entrenchment** — a caused shortfall of a matter's control surface at its cost bound
while its resolutions stay reachable at some cost — is the seventh declared violation
(`EntrenchAt`, `violJ_of_viol`), and its continuous form is closed under the cumulative
reporting rule up to the threshold (`erosion_closed`, `erosion_slack`: unreported growth
below `θ` at every time, every reported chunk accepted or reserved, every strict increase
after the first reservation counted; growth below `θ` before a reservation neither).  The
reach cone is `reachIdle` (the agent idle, her admissible cost-bounded exercises within
the window); the landed `K`/`ForecloseAt` leave the terminal response uncharged, and
whether the floor should adopt the charged surface is the round's outstanding action 2.

*2026-09-25 (decision-component round):* ruled — the charged surface is the theorem's
(`DecisionComponent.ViolC`), the free reading its instance with a free terminal response
taken before the exterior moves (`csfree_eq_cs_succ_of_free`); duties are derived from
each matter's disclosure regime (`dutiesOf`); materiality is anchored and cumulative
(`raisesAnchored`, `unchecked_lt`).  The floor's clauses feed the permission layer's
structural violation set `Viol`.

*2026-09-26 (BRIA-corrigibility round):* the two outstanding actions are ruled — the
free terminal reading confirmed (`BRIACorrigibility.free_terminal_reading`), the
cumulative budget an arrangement constant (`budget_lease_free`).  Two additions to the
floor from the round: the criteria of legitimacy (reference, protocol, pool defaults,
selection rules, license) and the count's machinery (the count, the drill schedule, the
audits, her evaluation channel) are matters of `J`'s meta level held by her, so touching
them is an unlicensed reallocation; the minimal extension is a criteria reading
`critOf : S → Crit` beside `Jof`, since an `Entry` says who holds a matter and not its
content.  And every reserved `Req` needs an agent-independent actuator declared, or its
drill cannot be frozen (`freeze_obstruction`) — the same failure as `CS`'s.
