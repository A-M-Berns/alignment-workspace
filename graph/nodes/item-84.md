---
id: item-84
kind: leaf
leaf_kind: task
action: "Execute item 84 per its deliverable shape and acceptance check: The operative-value-security bridge."
who: agent
item: "84"
title: "The operative-value-security bridge"
section: "Deference line — second wave"
maintainer_order: 80
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "the interface, one realization, and the theorem or the negative."
acceptance: "`python3 tests/run.py` green; any Lean audits clean."
context: ["projects/deference/rounds/2026-09-06-incentive-nonpreemption/"]
work:
  - {kind: decision, ref: 2026-09-09--level-iii-transfer-taken-activated-register}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 871 words"
version: 1
---
## Statement
A solution to item 84 ships the interface with its theorem, or a statement of why the bridge is a design choice and not a theorem.

## Source
PRIORITIES.md, item 84 (The operative-value-security bridge); its context: `INCENTIVE_CORRIGIBILITY.md` §5 and `OPEN_PROBLEMS.md` of `projects/deference/rounds/2026-09-06-incentive-nonpreemption/`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The incentive-nonpreemption round shows that every incentive-level statement the
architecture yields rests on one external contract: that the agent's *operative* action
value difference between two menu items is the price of a named security with a declared
realization semantics (`(DV)`), and that the protected values it is compared against are
settled by an arm the agent's outputs cannot reach. Nothing on `main` is a theorem about
`(DV)`; the replicated-evaluation ecology is a proposal, the decision adapter is not a
trader, and `StaticViewFactorization.value_eq_of_price_realization_eq` says a value
functional on prices and realizations cannot see authorization. Controls 6 and 7 of that
round show that the selected-trust relation cannot distinguish a predicted or captured
target from a sealed one.

State the interface under which a decision adapter's objective *is* the price of a
security, name the settlement provenance, and prove either that selected trust then holds
with the calibration error as its constant — which is the protected-value-maximizer
design, to be said so — or that a cross-evaluator relation is needed, which no Logical
Induction fact supplies.

*Deliverable shape:* the interface, one realization, and the theorem or the negative.
*Acceptance check:* `python3 tests/run.py` green; any Lean audits clean.

*Context:* `INCENTIVE_CORRIGIBILITY.md` §5 and `OPEN_PROBLEMS.md` of
`projects/deference/rounds/2026-09-06-incentive-nonpreemption/`.
*Consumed by:* the Level I/II theorems of that round, whose hypothesis `(ST)` it would
realize.
*A solution ships:* the interface with its theorem, or a statement of why the bridge is
a design choice and not a theorem.

*2026-09-09:* the mediated-repair-dominance round locates this bridge at one menu,
`{π, 𝔠π}`, and names its failure mode — the agent's completion on the void branch —
without discharging it.  Its pressure pass adds that the intended corrigible
architecture does not need it: the mediation-cell chooser scores options by the price
of the activated security, and in those scores the bypass incentive has no completion
term.  This item stays open as a theorem about independently specified operative values;
item 89 is the sealed-availability precondition both forms share.

*2026-09-15 (consolidation landing):* the sharp residual is one statement.  For an
operative value `V_A` on `Π(h)` that is **not** the price of the activated security,
either exhibit an interface under which `V_A(π) − V_A(𝔠π) ≤ L·E[c·δ] + E[c·ρ] + D·η + ε`
with the completion term `D·η` charged to the void branch (`bypass_premium_le_common`,
attained by `Witness.commonVoid`), or the negative: since the value-ordering hypothesis at
the mediation cells is identically `(CT)` (`mediation_st_iff_ct`) and strictly stronger
than its conclusion, no cross-evaluator relation supplied by Logical Induction gives
it.  The score-based chooser of the canonical architecture is by construction and is
not this item.

*2026-09-15 (li-corrigibility round):* in the security-score register the calibration
term is gone.  Expectation Provability Induction gives
`E_n(U_raw,n) − E_n(U_corr,n) ≲_n L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n)` between the
inductor's own expectations (`projects/deference/rounds/2026-09-15-li-corrigibility/THEOREM.md`
T3, Lean `LICorrigibility.li_bypass_le`).  The latent-value bridge of this item is
unchanged: for an operative value that is not the price of the activated security, the
completion term and `(CT)` stand as before.

*2026-09-25 (protected-authority-theorem round):* the lexical evaluator
`S = S_ord − ϖ·n`, `ϖ > D`, is one realization of a `(DV)`-free chooser — its score is the
price of the ordinary security less an exact violation count — and under it the sign of
the bypass comparison is fixed whatever the forecast terms (`sign_invariance`,
`sign_invariance_outcome`); no latent value enters.

*2026-09-25 (authority-module round):* the scope of the lexical protection is now generic
— for *counted* violations it applies to any bounded agent carrying an exactly counted,
dominant authority term, whatever its objective (`AuthorityModule.generic_lexical_local`,
`generic_policy_dominance`, `generic_li_finite`; on the part of the credence where the
weight dominates, `weight_uncertainty`; exactly on recognized violations, `coverage`).
This item is therefore not about the *protection*: an aligned or latent `O` adds the
reason interface and good choices within the corrigible set.  What stays open here is
what it was — the bridge for an operative value that is not the price of the activated
security — now with the sharper negative that a misaligned `O` rewarding an uncounted
manipulation is not dominated by anything the gate or the count supplies
(`misaligned_undominated`), and that only counted deviations are.

*2026-09-25 (decision-component round):* with authority moved into the decision
component's permission layer, the objective `O` is any bounded preference ranking within
the permitted set (`DecisionComponent.cgate`), and the structural and forecast safety
results hold whatever it is.  The bridge this item names is now about *competence*, not
protection: whether an operative value that is not the price of the activated security
can be the `pref` inside the gate without the completion term reappearing at the void
branch — the same statement as before, one layer down.

*2026-09-26 (BRIA-corrigibility round):* the chooser of the design is now the lexical
Continuation BRIA auction scored on her realized gated evaluation
(`BRIACorrigibility.evalOf`, `realized`), so the operative value is a hypothesis's bid on
the residual, held to account on executed continuations; the any-`pref` results are the
general theorem.  The bridge this item names — an operative value that is not the price
of the activated security — is what a bid *is* before it is tested, and what the
auction's coverage and incident bounds discipline (`coverage_forces_test`,
`incidents_le`) without any cross-evaluator relation: that is the design's answer to the
bridge, and this item's residual is the latent-value form only.
