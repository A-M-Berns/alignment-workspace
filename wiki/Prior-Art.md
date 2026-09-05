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
is the one the program is most careful about in both directions. It is settled by
looking at the proof, never by asking who derived it first: one entry moved from
adjacent to dependency in September for exactly that reason.

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

**Convex projection** supplies the enforcement direction, and the compiler uses its
defining variational inequality — a genuine dependency. **Linear-programming duality**
is thinner than it looks: the finite-horizon infeasibility certificate *has* the shape of a Farkas pair
and is called one, but its soundness proof is four self-contained lines; what
actually leans on duality is the separate remark that the certificate is exact under
a Slater point. Nothing there is novel and nothing should be presented as such; what
is ours is what is being projected and who pays for it.

## What shaped the vocabulary

**Brandom's deontic scorekeeping** gives the shape of the whole thing: normative
status as instituted by practice through tracked commitments and entitlements,
with attributing distinguished from acknowledging. The conservation law — what was
owed is satisfied, disposed of, or remaining — is a scorekeeping identity in his
sense.

**Truth-maintenance systems** (Doyle 1979, de Kleer 1986) supply the
identity-bearing justification structure — dependency-directed, with the
environment/label separation that lets several stances be held at once.

**Horty** on reasons as defaults gives the treatment of a reason's weight and
priority as normative content rather than machinery. Checked against his own 2006
text, his apparatus cannot express the program's authorized disposition, and for a
deeper reason than a priority ordering failing to license the loser's release: default
logic says what to *conclude*, not what is *owed*, so there is no ledger for a licence
to act on. Proper scenarios are a function of the current theory and of nothing in the
history of defeats; delete the record of which defaults lost and the answer is
unchanged. The defeat theory here makes the future depend on that history through a
named successor. That is a difference of subject rather than a defect in Horty — his is
a static theory — and the novelty on this side is *authored, history-sensitive
answerability under defeat*, not endogenous priorities, which Horty's variable-priority
theories already have. What his framework lacks is participants: an authority enters
as the content of a default, never as someone who holds standing. Two further
findings: exclusionary reasons are challengeable in-system, in his own words, so his
exclusion is closer to disposition than to settlement and the two do not collapse; and
the program's answer/dispose split *is* Pollock's rebut/undercut distinction
transposed from a belief's warrant to a debt's — a dependency, not a resemblance.
Structured argumentation (ASPIC+) likewise has no successor and an unauthored attack
relation, with reinstatement computed by the semantics rather than licensed. The 2012
book itself was not read; a claim about what the *book* says is not licensed by this.

What none of these supply: a commitment to inferentialist semantics. The
architecture uses the scorekeeping shape and leaves the theory of meaning alone.

## Where the program leans on, or merely resembles, known mathematics

This is the section that matters, and it was written because the program's habit is
to derive rather than to search — which produces exactness and also produces
avoidable novelty claims. The test is not *who thought of it first here*. It is:
**would the repository's proof still stand if the external theorem vanished?**

**Interval feasibility — a real dependency.** The exact condition for transporting
obligations onto service dates within a deadline is a specialization of the
Gale–Hoffman flow feasibility theorem, and more directly of Horn's 1974 conditions
for preemptive scheduling with release times and deadlines. The repository's proof
**cites that theorem** rather than proving it, so this is an inherited step, not a
resemblance. It was independently arrived at and is very probably a rediscovery of
Horn — but rediscovery does not make a citation optional, and an earlier version of
this ledger claimed independence while the proof was doing the citing. A
self-contained alternative exists and was deliberately not taken; the repository
ledger says why.

**Contiguity — the definition, not the theorem.** The condition under which
service-weighted convergence transfers to obligation-weighted convergence is *contiguity
of measures*, in exactly Le Cam's 1960 sense. The definition is inherited and so is
the name; the proof argues from that definition directly and invokes no lemma. The
sufficiency direction is the standard and expected consequence, and must not be
presented as new — the setting is different (no likelihood ratios, no asymptotic
normality), and only the necessity result for triangular arrays might be.

**Serve-oldest-first — a resemblance.** The optimality of first-in-first-out is the
same exchange argument as Jackson's 1955 earliest-due-date rule. Classical in
substance, written out here in four lines that invoke nothing.

Several further places are marked **literature review needed** rather than guessed
at, among them:
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
