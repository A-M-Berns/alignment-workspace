---
id: updateless-defers-relation
kind: leaf
leaf_kind: step
action: "Using defersMenu_not_policyEndorses_witness and the squeeze finding, write a non-definitional defers relation and test it on transparent Newcomb, counterfactual mugging and the twin prisoner's dilemma."
who: agent
files: [Cleanroom/Udt/UdtEndorsePolicy/]
author: "@smithy-verity"
size: M
size_reason: "two lab documents and one package report"
version: 1
---
## Statement
An endorsement-like relation between a prior and a candidate update assigns
deference in transparent Newcomb, counterfactual mugging and the twin
prisoner's dilemma exactly where the policy-optimal choice differs from the
updateful one, and is not definitionally equivalent to policy optimality.

## Source
projects/deference/note-dump-2026-08-11/deference-trust-lab/models/updateless-deference-model.md,
section 0, the candidate relation;
projects/deference/note-dump-2026-08-11/deference-trust-lab/report/CRITIQUE.md,
the lab's own blocker rating the direction near-vacuous;
projects/deference/faf-cleanroom-2026-10-02/packages/udt-endorse-policy/udt-endorse-policy-report.md:
defersAll_iff_policyEndorses is a squeeze and
defersMenu_not_policyEndorses_witness refutes the menu form.

## Notes
Two independent AI passes, the trust lab's critic and the clean-room's squeeze,
found every candidate tautological: a tautology wrapper around argmax with a
hand-fed discriminator, in the critic's words. The maintainer's framing in the
public agenda,
projects/deference/note-dump-2026-08-11/deference-trust-lab/AGENDA.md ('There
are real improvements which UDT will accept'), is why the task stands.
