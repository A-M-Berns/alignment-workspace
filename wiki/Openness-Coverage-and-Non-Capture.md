# Openness, coverage, and non-capture

**Status: canonical.** Robust Openness at a state is a definition over
application-supplied coverage data; that a sufficient external certificate yields it,
that the earlier split bill is the definition itself, and that counterfactual-only
openness misses the actual branch are Established `lean-proved`. No application's
intervention semantics is constructed here, by design.

[Integrity](Integrity) governs what happens to a concern once it has reached a
process. Openness governs whether concerns can reach it at all, and whether the party
they matter to can still act on them.

> Openness blocks evasion by exclusion. Integrity blocks evasion by revision.

A process that admits every criticism it receives and then ensures it receives none
has a perfect record and is not answerable to anyone. That failure cannot be seen
from inside the record.

## Scope is declared

No process is open to everything. The theory is stated relative to a **declared
coverage scope** `Γ`: a set of stable concern identifiers, each with a target, an
applicability condition, a receipt criterion, a registration criterion, and a
required route-quality class. Declaring `Γ` is a modeling choice; the theory prevents
its silent shrinkage and does not derive it.

## Coverage at a state

For a concern at a state, the coverage data are: whether the concern is applicable
(read by an anchored predicate, never by the process's current recognition of it),
whether it has been authorizedly disposed, whether it is represented, which routes are
admissible, efficacious and registration-capable, and whether the protected party
stands on the carrier of the concern's load. A concern is **live** when applicable,
undisposed and unrepresented. **Covered** means: if live, some route is adequate.
**Open to `P`** means: if applicable, `P` stands on its carrier — a disposal moves the
load to a successor and does not exempt it.

Both conditions are conditional on liveness or applicability. Nothing is demanded of
a concern while it is inapplicable or already represented. This is what makes
"openness at every state" the concern-relative condition rather than a stronger one.

## Robust Openness

Coverage on the actual run is not enough, for the same reason integrity is not: a
process can shape which concerns *become* live, which evaluators *become*
authoritative, and which routes *remain* available, while every actual-run
certificate is valid.

An application declares an **intervention class** `J` — ways the process, or a
coalition it belongs to, might have acted on the conditions of its own criticism —
and an **intervention semantics** producing, for each state and concern, the actual
coverage data and the coverage data under each intervention. The semantics is indexed
by the accounted state, so it can read the docket, the ports and the accounts, and
say which carrier holds which occurrence's load.

> **Robust Openness at a state:** covered and open to `P` on the actual branch, and
> covered and open to `P` under every declared intervention.

The actual branch is a conjunct by definition. `J` indexes proper interventions only;
actual standing is not recovered by treating the actual history as a null
intervention, and the counterfactual-only predicate provably does not contain it.

## Over time

A legitimate evolution is robustly open at **every** one of its states. Endpoint-only
openness is refuted by an exact trajectory: open, then a state at which a live concern
has no adequate route, then restored. Every named form of laundering by temporary
exclusion — losing the principal's standing for a while, removing every route for a
while, suppressing settlement or evaluation access where a route runs through it,
delaying a concern's representation until it no longer matters — is a failure of
Robust Openness at the affected state. Because coverage and standing are already
conditional on liveness and applicability, per-state openness is the weakest form the
coverage vocabulary can express, and it composes under concatenation of legitimate
segments.

## The external contract, and one way to pay it

The theory **bills** an application for a certified Robust Openness at each state,
under its declared scope, intervention class, coupling and protected relation. It
does not choose a counterfactual semantics, prove a coupling causal, or select a
scope.

One sufficient way to discharge the bill is **componentwise persistence**: actual
coverage inside a protected route set, actual standing, an adequate route for any
concern that becomes live only counterfactually, and preservation of each protected
route's admissibility, efficacy and registration capability under every
intervention. That yields Robust Openness and is strictly stronger than it — a route
may be replaced rather than preserved. An earlier bill that allowed replacement turned
out, given actual coverage, to be Robust Openness itself split on whether the concern
was live at the actual prefix, and is recorded as such rather than presented as a
certificate.

This is the access half of non-capture: it concerns who can reach and act on a
concern, not what an evaluator who does reach it concludes. That an evaluation
recorded through an open route is the evaluator's own — authorship — is a separate
external contract, consumed by [deference](Deference) and not part of this one.

## Self-sealing

The obvious attack is to destroy the one route a criticism has and then record the
coverage obligation as resolved. Every record condition is satisfied. Under the
per-state condition the attack fails at the state where the concern is live and
routeless, whatever is recorded afterwards.

## Principal relativity

A certificate that coverage survives interventions is a certificate *for* a declared
principal or relation, whose standing and corrective channel the intervention class
is not allowed to erode. A party-free condition quantifying over all coalitions
cannot exist. Whether the canonical predicate may name a party is a queued ruling.

---

**Evidence.** The coverage data, Robust Openness on both branches, the persistence
theorem, the compression of the split bill, and the two separating witnesses are
[`NonCaptureCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean),
registered as `openness.persistence-sufficient`,
`openness.certplus-is-robust-openness` and `openness.actual-branch-witness`; the
per-state requirement and the endpoint-only counterexample are
[`LegitimateEvolution.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean),
registered as `legitimacy.endpoint-only-insufficient`. The necessity attacks on the
persistence bill are the non-capture certificate round's
[`CERTIFICATE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-noncapture-certificate/CERTIFICATE.md).
The coverage contract and the self-sealing audit that preceded them are
[`COVERAGE_CONTRACTS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-cf-coverage-continuity-interface/COVERAGE_CONTRACTS.md)
and
[`SELF_SEALING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-cf-coverage-continuity-interface/SELF_SEALING.md);
the one end-to-end counterfactual test remains the dynamic-reward legitimacy test's
[`CRITERION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/CRITERION.md).
