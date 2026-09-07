# Normative Inductor

**Status: canonical architecture; conditional theorems.** The substrate — Logical
Induction over an assessment process, projection enforcement, its preservation under
bounded liability, and the effective deductive end-to-end result — is Established
`lean-proved` in the normativity registry. The two theorems that compose the
substrate with the Progress bound are Lean-proved and deliberately *not* registered:
the general one's Logical-Induction hypotheses are not inhabited, and the deductive
one has no single witness for its joint package. The name is provisional.

The Normative Inductor is the concrete candidate for a bounded reasoner that realizes
[normative induction](Normative-Induction): a Logical Inductor made to answer to
legitimately incurred obligations without ceasing to be a Logical Inductor.

## The architecture

    NI = MarketMaker( TradingFirm^L + JointProjectionEnforcer[ Compile(O_P) ] )
         + DecisionAdapter

The ordinary trading firm over the language `L` is the substrate and is left alone.
One additional trader — the enforcer — is added to the aggregate the market maker
prices against, with bounded liability. The decision adapter *consumes* the market
state; it is not another trader and does not feed back into prices. Enforcement is
additive, which is why every theorem about the underlying inductor survives.

## From the accounted state to a region

At a strict prefix, the compiler receives the live docket of the accounted state with
each port's anchor, the current semantic realization and its transport from the
anchor, the settlement items available, and the compiler's declared schema and
conflict policy. It returns **one joint convex region** `K_s` for every constraint
serviced together — a finite system of rational inequalities over canonical security
identities with a nonemptiness witness — or an accountable failure that **conserves
every cited obligation**. Simultaneously serviced constraints are conjoined, never run
as independent traders: individually feasible constraints can have an empty
conjunction.

Five properties are kept apart: compiler soundness (proved for the rational-row
schema, with a sound Farkas conflict certificate); completeness within a declared
class; convex representability of the obligation language; joint feasibility; and
affordable enforceability. Only the first is landed.

## Enforcement and the public defect

The enforcer is Euclidean projection of displayed prices onto `K_s`, scaled by a
prospective multiplier `λ_s`. Euclidean projection is the *implementation*. The
public interface is the sup-distance and the bare multiplier:

    d_s = dist_∞(b_s, K_s),        a_s = λ_s ,

chosen because they are invariant under enforcement-null coordinate padding, which
the dimension-normalized alternative was not. The work relation is an inequality,
`λ_s d_s² ≤ λ_s ‖b_s − proj(b_s)‖² ≤ ρ_s`, so the kernel-checked Euclidean work bound
controls the public uptake certificate without the two being equal.

## Admissibility is not value

The region says which market states the obligations *admit*, not that any admitted
state contains the true value of a policy: a state with zero defect can display as
best the policy whose authenticated counterfactual value is worst. The practical
semantics is external and enters only through `PracticalCert`. Value correspondences
with pre-committed calibration are one sufficient way to produce it.

## One response per service

One service occurrence realizes one response and may be matched to several
exposures; every matched edge certifies against that same response. Joint feasibility
of the price region does not give this; when matched obligations demand incompatible
responses the realization separates them, invokes a licensed adjudication rule, finds
a common adequate response, or leaves mass unserved — and never charges two edges to
a response that only one certifies.

## The conditional theorems

**General assessment.** Bounded assessed liability of the enforcer and a computable
augmented market give ordinary Logical Induction relative to the assessment process;
the practical/uptake certificate at that same market gives the Progress bound on the
accounted state. Every hypothesis is consumed; none is returned as a conclusion.

**Compiled deductive schedule.** The registered effective end-to-end theorem's own
hypotheses — a computable compiled schedule, a computable deductive process, and
admissibility of every compiled row by every plausible world — plus domination of the
public defect by finite-time conformance, plus the edge certificates and the
amplification bound, give Logical Induction and the Progress bound with the uptake
certificate *derived* from conformance. Its admissibility hypothesis restricts it to
regions every plausible world satisfies, the zero-liability case; genuinely
normative regions go through the general theorem, whose liability hypothesis is what
a scheduler's affordability produces.

Reading either signature says exactly why the realization is conditional: the
compiler, the scheduler, the practical semantics and the market's computability are
how a realization *produces* the named hypotheses, and none is produced here.

## The adapter is not the Inductor

The decision adapter that consumes the market state is a separate object.  What the
conditional theorems ask of it is the practical certificate; the adequate-set route
reduces that to a coupling — mass off the adequate set affine in the public defect —
which any adapter sound at the region and Lipschitz in the scores satisfies, and which a
ramped adequacy gate realizes with an explicit constant
([Normative induction](Normative-Induction)).  The gate is a realization of `Pi`, not a
component of the architecture above; the positive margin it needs is a semantic or
epistemic input, and competence inside the adequate set is the application's.

## What remains

Realization and integration, not conceptual theory: a `Protocol` implemented over an
event log with its evolution builder; the connector from the predictable-window
scheduler's rational budget to the enforcer's assessed net worth; the transport
checker binding every served edge to one response receipt; effective rows-to-vertices
for the compiled region. The genuine research problems — representability and
completeness for a nontrivial obligation class, adaptive affordable scheduling,
quantitative semantic-transport constants, a jointly compatible response ecology — are
on the [Roadmap](Roadmap).

---

**Evidence.** The two conditional theorems and the deductive composition are
[`NormativeInductionInterface.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NormativeInductionInterface.lean);
the export adapter on the older trace model, the rational-row compiler with its
conflict certificate and failure conservation, the compiled schedule's instantiation
of the registered effective theorem, the predictable-window scheduler, and the finite
Progress algebra are
[`NormativeInductorComposition.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean);
the padding analysis, the value counterexample and the projection-work domination are
[`NormativeInductor.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/lean/Workspace/Normativity/Contrib/NormativeInductor.lean)
with the realization round's
[`NORMATIVE_INDUCTOR_REALIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/NORMATIVE_INDUCTOR_REALIZATION.md).
The connector classification is §7 of the consolidation round's
[`CONSOLIDATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md).
The substrate's registered claims are in the
[normativity claims registry](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/CLAIMS.md)
and the enforcement construction is summarized on
[Actionability and normative force](Actionability-and-Normative-Force).
