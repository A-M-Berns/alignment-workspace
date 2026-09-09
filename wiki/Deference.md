# Deference

Deference asks how a bounded reasoner can benefit from a better-informed process
without surrendering the ability to correct what that process does. The problem
is not simply whether the advisor predicts well. It is whether the principal's
future reasoning and corrective role remain real parts of the decision process.

The line follows a progression:

1. [Logical Induction and Deference](Logical-Induction-and-Deference) asks how a
   present bounded reasoner can form beliefs about later computations and why a
   favorable decision comparison is only an epistemic beginning.
2. [What Deference Requires](What-Deference-Requires) separates delegation from
   simulation, prediction from authorization, and competence from calibration.
3. [Corrigibility](Corrigibility) asks whether corrective capacity remains
   reachable and unpreempted across time.

## Core idea

An advisor may have information the principal lacks. Using that information is
**epistemic deference**. It does not follow that the advisor has **practical
authority**, that its action is **authorized**, or that it should control the
transition system. A process can predict exactly what the principal would do and
then substitute its own actuator; behavioral agreement alone does not preserve
who acted or whose permission mattered.

Corrigibility therefore targets more than obedience. The principal must retain a
qualified corrective role through time. That requires temporal reachability, an
authorization structure, some principal-exclusive effect, and model-relative
efficacy robust to the advisor policies being quantified.

[Legitimacy](Legitimacy) enters because preserving a channel is not enough. The
surrounding process must preserve standing, provenance, and write boundaries so
the advisor cannot manipulate what counts as a correction or the principal
cannot launder a failure by self-authorization. [Corrigibility](Corrigibility) now
carries the research state across three rounds: principal authority as part of the
protected admissibility structure, the constitutional theorems with their bridges, a
conditional incentive-compatible mediated-delegation result whose hypothesis is a
selected-trust relation between the agent's operative values and the protected
principal's, and the static decision interface shared with ordinary normativity.  What
is not proved — incentive corrigibility, gate preservation as a preference, provenance
and containment — is stated there, not here.

## Legitimate deference — the active consumer

*Research state, unregistered; three stacked rounds, landed together.*

**The interface.** At time `n` the advisor admits, as an ordinary obligation in the
account calculus, an anchored *evaluation occurrence*: a request that the principal
score a fixed menu at a designated session. The actual future principal — after
interacting with the advisor — may answer. There is no counterfactual no-AI evaluator
and no ideal-value oracle; on worlds where no evaluation occurs there is no value
vector, and none is invented. The evaluation is a **partial** object on the worlds where
it exists.

**Activation.** A common event `C_n` says whether that evaluation validly inherits the
present mandate's authority: exactly one authenticated answer receipt in the
occurrence's propagated account (never a closure, never a live port); an authentic
event payload binding the exact vector, at a principal-exclusive endpoint; an
occurrence-local Integrity trace with the evaluation's concern scope robustly open at
every snapshot — a *consumer projection* of a legitimate segment, not a new legitimacy
notion; issuance-rooted **reason-mediated authorship** — over the advisor's whole
continuation from issuance to commitment, interventions that leave the same admitted
reason trace leave the same committed payload, with the trace blind to the declared
prohibited channels, and the binding event the principal's; and the **protected
reason-coverage barrier** — no protected live concern at commitment, with
representation faithful into the trace. Authorship is not a conjunct of legitimacy and
`AnswerOK` is unchanged; the evaluation-specific clauses are derived predicates over
the receipt, the event payload and the session's receipts.

**Deference.** Ordinary Logical Induction Value runs unchanged on the activated
securities `C_n · Ṽ_n(a)`, which are bounded securities independent of how the partial
evaluation is completed. Its scope condition — the menu must not reference the
advisor's selection — is selection-induced channel blindness of the reason trace
across the advisor's whole continuation, a theorem-domain condition kept apart from
`C_n`; a sealed commitment is one implementation and is not sufficient alone.

**The conclusion is conditional authoritative regret.** Activated regret equals the
activation mass times the regret *by the actual authoritative future principal,
conditional on the worlds where that principal's evaluation exists*, against the best
fixed candidate of the issued menu. With Value's bound `ε` and availability `𝔼[1 − C_n]
≤ η < 1`, that regret is at most `ε/(1 − η)`; as both vanish it vanishes. Any total
regret written against an arbitrary completion of the void worlds lies within the
payoff diameter times `η` of activated regret, in either direction — a robustness
lemma, not a target; the one-sided interval an earlier round stated is withdrawn, since a
world-dependent strategy on the void branch can push completion regret *below* activated
regret. Under sound activation the credence of worlds where a protected reason was
suppressed is at most `η`, relative to the declared scope. The theorem-level statements,
with their Lean names and the sign hypothesis the bound needs, are on the
[Theorem Spine](Theorem-Spine).

**What is not claimed.** That legitimacy chooses the correct answer; that Robust
Openness makes the principal consider anything — it supplies a route for a live
protected concern, not its exercise; that authorship alone puts the menu on Value's
domain; that any concrete protocol realizes authorship, coverage, or `η → 0`. Those are
the realization bill, `PRIORITIES.md` item 87. The stack is
[authority-activated value](https://github.com/A-M-Berns/alignment-workspace/tree/a8b25af87684e6b902cc1d008919f4aa1fd3cc60/projects/deference/rounds/2026-09-07-authority-activated-value),
[reason-mediated authorship](https://github.com/A-M-Berns/alignment-workspace/tree/a8b25af87684e6b902cc1d008919f4aa1fd3cc60/projects/deference/rounds/2026-09-07-reason-mediated-authorship)
and the
[consolidation](https://github.com/A-M-Berns/alignment-workspace/tree/a8b25af87684e6b902cc1d008919f4aa1fd3cc60/projects/deference/rounds/2026-09-08-legitimate-deference-consolidation),
whose `LEGITIMATE_DEFERENCE.md` is the statement of record.

**Realization, partial.** The
[evaluation-ecosystem round](https://github.com/A-M-Berns/alignment-workspace/tree/57b373bfe542d0c7b1ee78ba7e170fade4cc9003/projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization)
runs the theorem end to end in a concrete model: an authenticated event log, a
protocol read off the log with Integrity propagation proved a function of the log,
a simulated continuation frame, and an exact market on finite worlds, with
`R_auth = ε/(1 − η)` attained on the worked trace. Of the bill's seven clauses,
principal-exclusive binding, non-degeneracy of the reason trace and representation
faithfulness are discharged (the last in Lean for every log and scope); frame
factorization is discharged for the reading principal, with the receipts' meaning as
the one thing a log cannot certify about itself; selection sealing is discharged for
the sealed advisor class with the leak exhibited; reason-supply liveness and
availability are residual with their exact criteria named — the bounded-delay
affordability criterion for the concern stream, and a vanishing void frequency
against which the ecosystem's price tracks the empirical frequency within `3/(n+2)`.

## Current status

> **Two targets, both live.** The legitimate-deference consumer above is **active
> research state**, unregistered, landed in three rounds; it consumes the legitimacy
> spine. The original target — the corrigibility model with temporal depth and what
> foreclosure loses — now has its temporal-depth half supplied by
> [Continuation BRIA](Continuation-BRIA): bounded learning against accountable
> continuation claims on the histories the learner reaches, with foreclosure named
> exactly as the case in which a comparator's own history is not joinable from the
> learner's. What it holds is registered; what remains is the succession of item 28
> (`DECISIONS.md`, *Awaiting the author*), a decision about what is worth proving.
> Endpoint preservation is **ruled out** (`DECISIONS.md`, 2026-09-08): legitimate
> influence is causal factorization through declared reasons, not convergence location.

> **Established — `lean-proved`.** The
> <!--state:workspace:counts.registered_claims_by_project.deference-->31<!--/state-->
> entries in this line's registry are its finite results: the delegation bridge
> and the certificate, exposure and substitution lemmas; the signed-versus-magnitude
> separation; the static-view factorization; and the corrective-control model. Each
> names a Lean declaration and the priority item it answers.

**The strongest results here are impossibilities, and they are the line's
companion findings rather than an aside.** The magnitude functional is not a
trader payoff and cannot be made one — every trader averages to zero over a
coherent mixture, because net worth is affine in the payout vector and the
absolute value is not — so the magnitude target is retired rather than open. The
corrective-control model has no protected coordinate: the advisor reproduces the
principal's entire successor state, and reachable capability turns out to measure
advisor cooperation. A hard-selector route to Value does not survive the relevant
punishment menus, while a classwise, domain-relative route does; which of the two
the line's target should be is live as items 14 and 34.

**What the older target still waits on.** One decision sits in `DECISIONS.md`'s
*Awaiting the author*: whether the two candidate objects for what foreclosure loses are
enough for that question to graduate, and what succeeds item 28, which is *what is
worth proving* and no round's to decide. The temporal-depth requirement is now met at
the learning layer: [Continuation BRIA](Continuation-BRIA) supplies bounded competence
against accountable continuation claims for every non-dominant block schedule, and the
policy-regret frontier `Regret = LEARN + SLACK + SHIFT` types what foreclosure loses as
the `SHIFT` term. What remains specified and not started is the authorization relation
at that depth, and the Logical-Induction-native side still supplies bounded belief and
forcing tools under explicit assumptions but no resource-indexed proof that the quoted
future process is unavailable now.

**The bridge to continuation claims.** Future authoritative evaluation — the activated
value `C_n · V_n(a)` of the legitimate-deference stack, settled on the principal side —
is one candidate source of the realized block scores continuation BRIA settles claims
against, and of the accountable claims themselves: a prediction of that value that a
hypothesis is willing to be held to is a claim with slack, and discharging the `SLACK`
bridge is what would make continuation competence competence against the principal's
value. That is an interface, not a theorem; nothing here proves that Logical Induction's
prices are near-tight claims about realized activated value.

## Evidence and deeper reading

- [LI-native deference interface](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/notes/LI_NATIVE_DEFERENCE.md)
- [Deference vocabulary and interface boundaries](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/notes/TERMS.md)
- [Corpus reconciliation](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md)
- [Reachable corrective control — `Dynamics-positive, protection-incomplete.`](https://github.com/A-M-Berns/alignment-workspace/tree/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/rounds/2026-08-12-reachable-corrective-control)
