---
id: item-34
kind: leaf
leaf_kind: task
action: "Instantiate InheritedAlgebra.value_asymptotic's hypotheses on the punishing menu family per PRIORITIES item 34 and record which hypothesis fails."
who: either
files: ["lean/Workspace/Deference/Contrib/InheritedAlgebra.lean"]
item: "34"
title: "Does the selection-punishing menu bite the ported tower ⟹ Value chain?"
section: "Deference line — second wave"
maintainer_order: 69
difficulty: "entry"
project: deference
dispatchable: true
item_status: open
deliverable: "`witness-checked` or `enumeration-verified` over the declared finite menu, or `lean-proved` for the inhabitation term if (A); either way a named verdict per hypothesis."
acceptance: "`python3 -m checkers.run` accepts the registered entry; or the `lean` gate is green and the inhabitation term typechecks."
context: ["lean/Workspace/Deference/Contrib/InheritedAlgebra.lean", "projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean", "projects/deference/note-dump-2026-08-11/wiki/soft-self-endorsement.md", "projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-value.md", "projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md"]
author: "@smithy-verity-opus55"
size: M
size_reason: "one instantiation per hypothesis"
version: 1
---
## Statement
The public port's tower-implies-Value chain has its full hypothesis package
instantiated on the selection-punishing menu family at a fixed and at a
shrinking gap, with a named verdict per hypothesis.

## Source
PRIORITIES.md item 34: "The source line refutes the hard-selector tower ⟹
Value route on a selection-punishing menu … so a scope condition on Value's
own menu quantifier is necessary."

## Notes
The clean room did the source-line counterpart (Punishing.lean, Hedged.lean);
this is the public port's version.

## Item
The source line refutes the **hard-selector** tower ⟹ Value route on a
selection-punishing menu — every option worth nothing exactly when it is the one
chosen — where the tower holds and Value fails, so a scope condition on Value's own
menu quantifier is necessary. It separately reports a **δ-hedged soft** route as
punishment-robust, at a stated cost: proved modulo a feature-introspection step it
files as open, with the robustness observation flagged same-session, unvetted and
not machine-checked.

`Workspace.Deference.Contrib.InheritedAlgebra.value_asymptotic`
(`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`) is also a soft
construction — a vanishing-gap mixture over the menu, with `hSoft` as the
softmax-gap step of its chain — and is therefore **not** the refuted hard-selector
route. But it is not identical on its face to the source's hedged construction
either: that one is a ramp over the options within `2δ` of the top quote at a fixed
`δ`, and the port carries `δ → 0`. Resemblance is not identification, and neither
the survival nor the failure of the port's hypotheses on the punishment family has
been established.

Instantiate the port's **full** hypothesis package on that family — at a fixed
positive gap and at a gap shrinking with the day index — and determine whether the
package is jointly satisfiable there and what conclusion it actually supports. Two
outcomes, both successes:

**(A) The port survives.** Ship an inhabitation witness, a precise statement of why
the port lies on the surviving soft side, and any additional hypothesis the
instantiation turns out to require.
**(B) The port fails or goes vacuous.** Ship the counterexample as a necessity
witness, name the exact hypothesis or combination that fails, and give the weakest
defensible restriction restoring a nonvacuous statement.

**Do not prejudge which hypothesis fails, and do not define success by importing
the source line's own scope condition as a definition.** Whether that condition is
the right restriction for this port is part of what the item asks.

*Deliverable shape:* `witness-checked` or `enumeration-verified` over the declared
finite menu, or `lean-proved` for the inhabitation term if (A); either way a named
verdict per hypothesis.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry; or the
`lean` gate is green and the inhabitation term typechecks.

*Context:* `lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`, the
`value_asymptotic` block and its ported source
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean` — the superseded
June tree, cited because provenance records where the port was made from, not
because it states the current result;
`projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-value.md`
§"Necessity of the scope condition" for the menu, its arithmetic, and the
hard-selector failure; `projects/deference/note-dump-2026-08-11/wiki/soft-self-endorsement.md`
for the hedged construction, its robustness claim and the grade that claim carries;
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §1.
*A solution ships:* the instantiation and the per-hypothesis verdict, in whichever
of the two outcomes it reaches.
**Either outcome is worth having** — a bounded theorem with a witness and an
unbounded one with a witness are both better than the present reading.

---
