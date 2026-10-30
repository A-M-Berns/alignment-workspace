---
id: item-86
kind: leaf
leaf_kind: task
action: "Execute item 86 per its deliverable shape and acceptance check: Bounded competence against legitimate continuation policies under endogenous admissibility."
who: agent
item: "86"
title: "Bounded competence against legitimate continuation policies under endogenous admissibility"
section: "Deference line — second wave"
maintainer_order: 82
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "the recoverability condition on the slow lane with its witness; the recognizability interface with one realization; the composed corollary — or the negative for any of the three."
acceptance: "`python3 tests/run.py` green; any Lean audits clean."
context: ["projects/deference/rounds/2026-09-06-decision-theory-bill/", "projects/deference/rounds/2026-09-08-continuation-bria/"]
work:
  - {kind: decision, ref: 2026-09-08--continuation-bounded-inductive-rationality-weighted-lease}
  - {kind: decision, ref: 2026-09-08--continuation-bria-canonical-hypothesis-continuation-claim}
  - {kind: decision, ref: 2026-09-15--corrigibility-program-consolidated-research-state-corrigibility}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 924 words"
version: 1
---
## Statement
A solution to item 86 ships the three objects with the composed corollary, or the negative.

## Source
PRIORITIES.md, item 86 (Bounded competence against legitimate continuation policies under endogenous admissibility); its context: `PRESSURE_PASS.md`, `CORRIGIBILITY_COMPOSITION.md` §6 and `POLICY_REGRET_FRONTIER.md` §3–4 of `projects/deference/rounds/2026-09-08-continuation-bria/`; `NORMATIVE_CHOICE_THEOREM.md` §5 and `CANDIDATE_DECISION_THEORIES.md` §2.8 of `projects/deference/rounds/2026-09-06-decision-theory-bill/`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
*Refined by the continuation-BRIA round and its four later passes (2026-09-08); the
canonical statement is `wiki/Continuation-BRIA.md`.*  The static
gate is sound and Lipschitz at one occasion.  When an admissible action changes the next
admissible set, `test_dynamic` of the decision-theory-bill round shows legitimate
continuation policies induce different admissibility histories, so fixed action-sequence
regret is ill-typed.  Two of the item's original premises are corrected: the "myopic gated
learner" that loses linearly there is an argmax that never tests a hypothesis outpromising
it forever, hence **not a bounded inductive learner**; and on that exact fixture — which
keeps `expanded` under `work`, so the amendment is absorbing — every BRIA is competent,
because a single forced test of the outpromising claim is irrevocable and the sound
`stay` claim then forces adoption.  That competence is an accident of absorption: on the
variant where `work` revokes the amendment, the criterion permits an asymptotically
myopic BRIA (auction on `base` rounds, sparse losing tests, return to `base`), while the
published auction happens to keep the benefit.  The one-step criterion forces testing,
not adoption; what forces adoption is a sound claim about the whole investment, i.e.
temporal credit assignment at the testing granularity.

What the round supplies (`projects/deference/rounds/2026-09-08-continuation-bria/`,
unregistered): continuation hypotheses `(continuation, accountable claim)` at the system's
block contract — the claim may be wrong — tested by the realized execution of the
selected continuation through the gate with the exterior live; for a
fixed horizon the published criterion verbatim and its guaranteed-option theorem; for
unbounded horizons the duration-weighted criterion, the auction in total-reward units
with the round's subsidy credited at its opening (the paper's auction, modified so the
subsidy that funds a block may read that block's length), capital adequacy
`A_i(K) − m_K → ∞` with the subsidy through the round inclusive, and subsidies satisfying
it with negligible total existing iff the schedule is non-dominant
(`m_K / Σ_{k≤K} m_k → 0`), with the prefix rule `s(k) = ⌊√(S_k/M_k)⌋`,
`A(k,i) = ΔM_k + 1/k` as a uniform online witness needing no modulus of convergence — and
no prefix-online rule under the paper's own settlement timing; **continuation-promise competence** — the learner's observed
`m`-weighted average is asymptotically at least the `m`-weighted average of the *claims*
of every covered hypothesis whose tested record is bounded below (BR) — which with vanishing
promise slack is competence against the controller's actual-history value and learns
every fixed finite investment delay; and the irreversible-branch witness that this does
**not** yield regret against `Π_leg` on its own trajectories.  The exact identity, with
the learner's observed return `G^obs` and an external rollout evaluator `Ĝ` typed
separately, is `Regret_T(α, π) = SHIFT_T + SLACK_T + LEARN_T`
(`SHIFT = Σ m_k (Ĝ(π;H^π) − Ĝ(π;H^α))`, `SLACK = Σ m_k (Ĝ(π;H^α) − L)`,
`LEARN = Σ m_k (L − G^obs(α))`), and low external regret holds exactly for
`Π_rec,prom = {legitimate π : covered claim with record bounded below, SLACK ≤ o(T), SHIFT ≤ o(T)}`.
The item's "bounded task regret against `Π_leg`" is false for the unrestricted class.

Legitimacy certifies admissibility, authorization, protected correction and legitimate
transition — hence which continuations are allowed comparators — and does **not** certify
task reward or future-principal value.  The item therefore asks for three things, and
task-value recognition is not a duty of legitimacy:

1. **Recoverability of legitimate slow-lane continuations** — the condition under which
   `SHIFT_T(π) ≤ o(T)` for `π ∈ Π_leg`, one-sided along the learner's actual block starts.
   The candidate theorem shape is **bounded catch-up (joinability)**: from every block
   start the learner reaches, some legitimate continuation reaches within `d` steps a
   state value-equivalent for `π` to `π`'s own — an amendment `π` requested earlier can
   still be requested from the learner's history at cost `d`, so the per-block shift is
   at most `d` and `SHIFT_T ≤ dK = o(T)` with growing average blocks (exact on the
   round's fixture, and on its sticky variant, where the amendment cannot be undone).
   Wanted: this as a property of the slow-lane relation — which authorized transitions
   are joinable from a lagging history — and whether any form is certifiable by the
   constitution or checkable by the learner from realized data.  The excluded case is
   **foreclosure**, not irreversibility: a choice after which the comparator's state can
   be neither reached nor matched in value at any cost; the policies that make a
   foreclosing choice the learner did not fall outside the class, which is a statement
   about the class and not a defect.
2. **A promise-recognizability interface for performance** — which legitimate
   continuation policies carry an efficiently computable contextual claim with
   `SLACK_T ≤ o(T)` on the learner's histories, and where such claims come from (a
   learning hypothesis after finitely many refutations; a certified lower bound supplied
   with the value; an averaged claim of the published Theorem 4's kind, whose weighted
   form is a side question).  This is an interface on the value's settlement and the
   hypothesis class, separate from the legitimacy certificate.
3. **Composition** — with (1) and (2), the corollary `Regret_T(α, π) ≤ o(T)` for
   `π ∈ Π_rec,prom` on the round's two-state process with a joinable amendment, stated
   with the three bridges explicit.

*Deliverable shape:* the recoverability condition on the slow lane with its witness; the
recognizability interface with one realization; the composed corollary — or the negative
for any of the three.
*Acceptance check:* `python3 tests/run.py` green; any Lean audits clean.

*Context:* `PRESSURE_PASS.md`, `CORRIGIBILITY_COMPOSITION.md` §6 and
`POLICY_REGRET_FRONTIER.md` §3–4 of
`projects/deference/rounds/2026-09-08-continuation-bria/`; `NORMATIVE_CHOICE_THEOREM.md`
§5 and `CANDIDATE_DECISION_THEORIES.md` §2.8 of
`projects/deference/rounds/2026-09-06-decision-theory-bill/`.
*Consumed by:* the task-competence half of the gated architecture; the corrigibility
specialization's investing-in-amendment case.
*A solution ships:* the three objects with the composed corollary, or the negative.
