# Integrity

**Status: open / unregistered**, with a kernel-checked structural core. The
components named below have Lean declarations or exact fixtures in the rounds cited
at the end; no legitimacy claim is registered, and the settlement-integrity hypothesis
is external by design.

## The role

A cognitive trajectory that can rewrite its own past can escape anything. It need not
refuse a criticism; it can misremember having received it, re-anchor the debt to a
specification that is easier to meet, mint the authority it needs, or retire the
vocabulary the obligation was stated in. Every step is locally defensible and the
obligation is gone.

**Integrity** is the part of the theory that rules this out:

> A cognitive trajectory cannot falsify or silently rewrite its own normative history.

It is a theory about the relation between a process and its own record. It says
nothing about whether the record is *good*, whether the right things reached it, or
whether anyone outside was allowed to challenge it. Those are the other half of
[legitimate evolution](Legitimacy) — see *Integrity is not Non-Capture* below.

## What a full integrity theory governs

The full normative history `H` of the [settlement interface](Settlement-Interface) is
the object. Integrity constrains how entries may enter it and how they may be read.

- **Authenticated births and admissions.** An obligation, ground, licence or
  standing enters the history at a recorded position, opened by a named participant,
  under a protocol that was already in force. Nothing enters retroactively.
- **Immutable anchors.** Each incurred obligation carries an anchored specification
  fixed at birth. Later presentations point back to the anchor; they do not redefine
  it.
- **Provenance and lineage.** Every change in what rules apply is licensed by rules
  already applicable, and the citation chain terminates in the recorded initial state.
  Every successor of an obligation names its predecessor; ancestry is
  prefix-determined and never revised by a later event.
- **Write permissions.** Who may append which kind of entry is itself part of the
  history. A participant does not write another's standing, and no participant writes
  a settlement fact.
- **Faithful carry under representation change.** When a representation changes and
  the process asserts that the thing represented did not, the assertion is a
  certificate anchored to the increment being carried — an interpretation fixed at
  the increment's birth, not one the current evaluator supplies. The faithful
  semantic preservation rounds state this as an order embedding on slice-relative
  quotients that covers in-place mutation; their *no semantic laundering* result says
  that under it a change of representation cannot lower what is owed.
- **Replayability.** The current standing state is a function of the history: replay
  the history and you recompute it. Grounded replay — that every licence, standing and
  ground cited at a position has an authorization tree reaching back through the
  record — is a theorem of the unified trace, not a postulate.
- **Authenticated settlement receipts and terminal discharge.** Only a receipt
  arriving through the settlement interface, typed as settling the anchored
  obligation, can make an unanswered obligation cease to be owed. A participant's
  challenge, verdict or valuation cannot manufacture that event.

The proof technology for most of this is the successor and ancestry machinery of the
normative-continuity specification — fresh successors, time-indexed ancestry, `Live`
and `Routes` read off the trace. That machinery is how the invariants are *proved*;
it is not itself the public definition of integrity, and a different realization
could discharge the same obligations with different bookkeeping.

## No self-grounding, as a theorem

The sharpest single consequence: **a transition cannot mint its own reasons or its own
authority.** Under strict pre-state citation, constitutive immutability and
answerability continuation, no-self-grounding is derived rather than assumed, and the
laundering attacks the program has catalogued die without any dedicated
anti-laundering rule. One clause survives as a clause: priority alone does not refuse
a disposition grounded in the very issue it disposes of, because that issue is in the
record strictly before its own disposal, so the `not_self` requirement is stated, and
the kernel-checked pair of witnesses shows it is exactly the one clause standing
between the system and a self-grounded disposal.

## Settlement integrity is an external hypothesis

Everything above is internal: it quantifies over the history and is checkable against
it. It rests on one assumption it cannot discharge:

> **Settlement integrity.** The settled view is written only through the privileged
> interface, the assessed process cannot write, forge, delay or suppress it, and it is
> monotone.

That hypothesis is stated on the [settlement interface](Settlement-Interface) page,
and it is where the internal theory hands off to whatever institution actually
supplies settlement. An integrity theorem is conditional on it, and the theory is
better for saying so than for pretending a trajectory could certify its own oracle.

## Integrity is not Non-Capture

The two are easy to run together and the program keeps them apart on purpose.

> **Integrity:** did the process faithfully preserve and account for what entered it?
>
> **Non-Capture:** could the process improperly control what was *able* to enter,
> challenge, or evaluate it?

Integrity is a property of one history and is largely formal: a record that satisfies
it can be replayed and audited from the inside. Non-Capture is a property of the
process *and its alternatives* — whether a criticism that would have been raised was
foreclosed, whether an evaluator was shaped by the thing it evaluates — and it
necessarily depends on counterfactual structure outside the trajectory. A history can
have perfect integrity while the process that produced it quietly ensured nothing
awkward was ever admitted. That failure is the subject of
[Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture), and the
theory deliberately bills it to an external certificate rather than pretending
integrity covers it.

## Where it sits

Integrity is the deeper theory under the history side of
[Diachronic Answerability](Diachronic-Answerability): answerability's conservation law
— every incurred obligation is answered, settlement-discharged, or faithfully carried
live — is only meaningful if the history it is stated over cannot be rewritten. The
qualitative obligation process that [Normative Induction](Normative-Induction)
consumes is exported from a history with integrity; without it the export could be
tuned after the fact.

---

**Evidence.** Grounded replay, the unified ground type, `Met` as a definition and
no-self-grounding are in the unified-grounds round —
[`GROUNDS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/GROUNDS.md)
and
[`THEOREMS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/THEOREMS.md)
— with the Lean witnesses in the defeat-landing round's
[`WITNESS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f7489cf5a610927b9e85e33d5d42228cd64da7de/projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/WITNESS.md).
Transition certificates and the three principles are the transition-certificates
round's
[`MEMO.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md).
Anchored slices and authenticated transfer are
[`ANCHORED_SLICES.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-anchored-slices-auth-transfer/ANCHORED_SLICES.md)
and
[`SEMANTIC_AUTHENTICATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-anchored-slices-auth-transfer/SEMANTIC_AUTHENTICATION.md);
faithful carry and no semantic laundering are
[`NO_SEMANTIC_LAUNDERING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-31-faithful-semantic-preservation/NO_SEMANTIC_LAUNDERING.md).
The Lean spine is
[`NormativeContinuity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f7489cf5a610927b9e85e33d5d42228cd64da7de/lean/Workspace/Normativity/Contrib/NormativeContinuity.lean).
