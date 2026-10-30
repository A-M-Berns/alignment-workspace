---
id: item-74
kind: leaf
leaf_kind: task
action: "Execute item 74 per its deliverable shape and acceptance check: Is the finite-horizon infeasibility certificate complete for the causal problem?."
who: agent
item: "74"
title: "Is the finite-horizon infeasibility certificate complete for the causal problem?"
section: "Deference line — second wave"
maintainer_order: 70
difficulty: "entry"
heading_notes: " — *sequenced behind item 40*"
project: normativity
dispatchable: true
item_status: open
deliverable: "`witness-checked` for the separating instance, or a stated theorem with an exact-rational fixture inhabiting its hypotheses for the completeness direction."
acceptance: "the round's runner is discovered by `python3 tests/run.py` and passes; a registered entry, if one is filed, is accepted by `python3 -m checkers.run`."
context: ["projects/normativity/legitimacy/rounds/2026-08-30-liability-theory/DUALITY.md", "projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/EXISTENCE_AND_DUALITY.md", "tests/"]
work:
  - {kind: decision, ref: 2026-09-02--september-naming-audit}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 491 words"
version: 1
---
## Statement
A solution to item 74 ships the theorem or the separating instance, and in either case a statement of what a certificate can and cannot be fed back into Answerability as.

## Source
PRIORITIES.md, item 74 (Is the finite-horizon infeasibility certificate complete for the causal problem?); its context: `projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/EXISTENCE_AND_DUALITY.md` §4 for the certificate and the soundness proof, §1–§3 for the causal problem it is a relaxation of, that round's `FOLLOWUP_REPORT.md` for why the account is signed and what that does to the dual, and its `src/overload.py` and `src/li_account.py` with the matching modules under `tests/` for the exact instances; `projects/normativity/legitimacy/rounds/2026-08-30-liability-theory/DUALITY.md` for the synchronic certificate the horizon version extends.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
A Farkas pair `(y, z)` with positive deficit refutes finite-horizon affordability on
any settlement-consistent path, and that direction is proved. The converse is open,
and it is the difference between a diagnostic and a dichotomy: a program feasible on
every path separately may still admit no causal policy, because the per-path relaxation
hands the controller the path in advance.

Settle it. Either exhibit a certificate class complete for the causal problem — the
transport plan of the Deferred Service Transfer theorem is already a flow, so flow/cut
duality on the plan is the first place to look — or exhibit a causally unaffordable
instance every path of which is feasible, which shows no per-path certificate class can
be complete and moves the question to certificates over policies.

**Sequencing.** Take item 40 first, and the existence of an affordable schedule
second — with the service variable now typed as enforcement intensity, that question
is well posed for the first time: does a schedule with divergent enforcement intensity
for every persistent reason exist inside the per-date liability capacity boxes,
against an adversarial docket arrival process? Until the necessity of bounded cumulative
enforcement liability is settled or refuted, an finite-horizon infeasibility certificate for the causal
problem certifies the failure of a hypothesis whose necessity is unknown, and every
"unaffordable" verdict in this line means "the known route to safety no longer
applies" rather than "no safe policy exists".

**What the dual object probably is.** The account is signed and cumulative and must
stay above a floor at every world the settlement process keeps live, so what has to
be separated is a *policy* from a family of adversary responses rather than a point
from a per-path feasible set. That points at a potential or supermartingale over the
assessment family — a function of the history upper-bounding the account slack still
achievable, decreasing along every admissible control, starting below what is owed —
rather than a flow or a cut. A cut is a sum of per-date capacities and the account is
not, so flow/cut duality recovers the per-path relaxation and cannot see the
cross-period financing the alternating countermodel exhibits.

*Deliverable shape:* `witness-checked` for the separating instance, or a stated theorem
with an exact-rational fixture inhabiting its hypotheses for the completeness direction.
*Acceptance check:* the round's runner is discovered by `python3 tests/run.py` and
passes; a registered entry, if one is filed, is accepted by `python3 -m checkers.run`.

*Context:*
`projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/EXISTENCE_AND_DUALITY.md`
§4 for the certificate and the soundness proof, §1–§3 for the causal problem it is a
relaxation of, that round's `FOLLOWUP_REPORT.md` for why the account is signed and
what that does to the dual, and its `src/overload.py` and `src/li_account.py` with
the matching modules under `tests/` for the exact instances; `projects/normativity/legitimacy/rounds/2026-08-30-liability-theory/DUALITY.md`
for the synchronic certificate the horizon version extends.
*A solution ships:* the theorem or the separating instance, and in either case a
statement of what a certificate can and cannot be fed back into Answerability as.
