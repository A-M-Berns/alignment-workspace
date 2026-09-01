# Prior art

A curated reading of what this program actually owes to existing work, and — more
usefully — what it does not. The full ledger with citations is
[`PRIOR_ART.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/notes/PRIOR_ART.md)
in the repository; [Sources](Sources) lists everything read.

This page is **not** [Relation to the Field](Relation-to-the-Field), which is the
maintainer's to write. Placing a program against a literature is a judgment about
what the literature says; this page only reports what was used.

## Six roles, because "related work" is too coarse

The ledger classifies every entry by how much it constrains us:

**Direct mathematical dependency** — we use or inherit a theorem.
**Formal substrate** — our objects are built inside a pre-existing framework.
**Conceptual dependency** — the source shaped the theory or its terminology.
**Adjacent prior art** — a close analogue, independently derived here, *not*
logically imported.
**Verification target** — our theory should eventually recover or subsume it; it is
not an input.
**Historical motivation** — motivated the question, contributes no current result.

Most entries are adjacent, and the distinction between *adjacent* and *dependency*
is the one the program is most careful about in both directions.

## What is genuinely substrate

**Logical induction** is the ground the enforcement construction is built on — the
market, the traders, the market maker, and the inexploitability criterion are all
inherited. The program's contribution there is a finite-time strengthening: a
conformance bound *at a date* where the criterion gives only an asymptotic
guarantee.

**Imprecise probability** — coherent lower and upper previsions, sets of
probabilities, and the linear-feasibility characterization of probabilistic
entailment — is what the credal state is. The regions the enforcement mechanism
operates on are convex sets of probabilities, and their exactness comes from that
reduction being a linear program.

**Convex projection and Farkas duality** supply the enforcement direction and the
infeasibility certificates. Nothing there is novel and nothing should be presented
as such; what is ours is what is being projected and who pays for it.

## What shaped the vocabulary

**Brandom's deontic scorekeeping** gives the shape of the whole thing: normative
status as instituted by practice through tracked commitments and entitlements,
with attributing distinguished from acknowledging. The conservation law — what was
owed is satisfied, disposed of, or remaining — is a scorekeeping identity in his
sense.

**Pettit** on responsibility as a two-place relation is why answerability has a
creditor and a debtor rather than being a property of one agent.

**Truth-maintenance systems** (Doyle 1979, de Kleer 1986) supply the
identity-bearing justification structure — dependency-directed, with the
environment/label separation that lets several stances be held at once.

**Horty** on reasons as defaults gives the treatment of a reason's weight and
priority as normative content rather than machinery. The program needs something
Horty does not provide — a *licence to stop owing* rather than a priority ordering
— and whether his machinery can express it is an open literature question.

What none of these supply: a commitment to inferentialist semantics. The
architecture uses the scorekeeping shape and leaves the theory of meaning alone.

## Where the program probably rediscovered known mathematics

This is the section that matters, and it was written because the program's habit is
to derive rather than to search — which produces exactness and also produces
avoidable novelty claims.

**Contiguity.** The condition under which service-weighted convergence transfers to
claim-weighted convergence is *contiguity of measures*, in exactly Le Cam's 1960
sense — the same definition, and the transfer direction is in substance a standard
consequence. The setting is different (no likelihood ratios, no asymptotic
normality), and the necessity result for triangular arrays may be new. The transfer
theorem should be presented as an **application of contiguity**, not as a new
theorem.

**Interval feasibility.** The exact condition for transporting obligations onto
service dates within a deadline is a specialization of the Gale–Hoffman flow
feasibility theorem, and more directly of Horn's 1974 conditions for preemptive
scheduling with release times and deadlines — described in the scheduling
literature as one of its cornerstones. Independently derived here. Very probably a
rediscovery.

**Serve-oldest-first.** The optimality of first-in-first-out is the same exchange
argument as Jackson's 1955 earliest-due-date rule. Classical.

Three further places are marked **literature review needed** rather than guessed at:
whether the *cost* form of the timely-service criterion is classical; whether the
join-semilattice conservation law has an antecedent in belief revision; and whether
the persistent-wait theorem is a standard fairness argument in disguise. The third
is the one most likely to already exist.

## Verification targets

**Carroll et al. on influenceable reward functions** is the clearest external
statement of the failure the program is trying to prevent: a system rewarded for
satisfying preferences is rewarded for changing them. The repository reproduces its
examples, and the criterion should eventually explain rather than merely match
them.

**The learning-normativity agenda** is the nearest statement of the problem this
line is working on, and the closest thing to a shared target.

**A standing criticism, not a target.** The objection that asymptotic
inexploitability leaves finite behaviour almost unconstrained — for any given
mistake there is a logical inductor making it until arbitrarily late — applies to
anything this program claims on the basis of the criterion. The enforcement
construction's finite-date bound is a partial response and has not been written up
as one.

## The standing hazard

Three of the four results the program might extract as papers rest on mathematics
with classical antecedents that were found *after* the derivation. The rule adopted
at the September checkpoint is that **every extraction candidate has its literature
review completed before any novelty claim is made outside the repository** — and
that independent derivation is a fact about our process, never evidence about the
literature.
