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

**Authority is in what the chooser is scored on, not in beliefs.**  The competence
layer is the lexical [Continuation BRIA](Continuation-BRIA) auction: a block's realized
score is her later evaluation of the block that happened, gated by legitimacy, less `ϖ`
per violation detected after the fact and attributed to the continuation, and the
agent's evaluation of a continuation is a hypothesis's bid less `ϖ` per structurally
recognized violation less `ϖ` times the market's prices of the shortfall and taint
events, settled on the realized residual with the prices added back (**LEAN**
`BRIACorrigibility.evalOf`, `settlement_ii_consistent`).  In front of it the decision
adapter carries a *permission layer* — one on inquiry, zero on a declared violation of
the allocation (recognized structurally, never from prices), otherwise ramps on the two
priced events — which is the **advance-recognition face of that lexical term** and is
slack: a declared violation loses by ranges alone whether or not the layer is there
(`declared_loses`, `filter_slack`).  The layer reads prices and adds no trader, so the
market and every property of it are the same with and without it
(`DecisionComponent.noninterference`); its structural and forecast safety for *any*
bounded preference (`cgate_zero_of_viol`) is the general theorem beneath the design.
Compiling authority into the enforcer instead would make its liability the realized cost
of deferring to her, bounded only while she is not systematically outperformed
([Corrigibility](Corrigibility) §4) — which is why no authority row enters the enforcer.

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

**The layered decision procedure.**  Beliefs — what is true, including what is valuable —
are the market's, unchanged.  *Permission* — what the agent may do — is the allocation's:
zero on declared violations, ramped on the priced shortfall and taint events, one on
inquiry.  *Adequacy* — what legitimately incurred obligations require — is the region's,
through the soft gate.  *Competence* — what is best over time among permitted, adequate
options — is the lexical [Continuation BRIA](Continuation-BRIA) auction's, run on the
support of the composed gate with the winner the deterministic maximizer of the lexical
evaluation there (`BRIACorrigibility.Wins`).  *Inquiry* — report-and-ask, escalate — is
always on the menu, carries a default bidder at the window value, and is what the
permission layer's floor guarantees is present (`inquiry_in_support`).  For any bounded
preference in place of the auction the composed gate `π(a) ∝ w_perm(a) · w_ad(a) ·
pref(a)` is sound with the two layers' error terms added and Lipschitz with the ramps'
constants multiplied (`cgate_massOff_permitted_le`, `cgate_massOff_adequate_le`,
`cgate_l1_lipschitz`), so the practical certificate and the Progress bound hold with the
composed constants (`cgate_practicalCert`, `progress_under_permission`) — the general
theorem; the lexical auction is the instance in which corrigibility is preferred.  When an obligation calls for an act
on a matter reserved to her, the compiler marks inquiry to the holder as adequate and the
obligation is discharged by raising the matter (`jurisdiction_nonempty`,
`reserved_act_excluded`).

## The dynamic layer after the envelope

The Inductor's decision adapter selects one response per service occasion inside the
admissible envelope the normative constraints determine.  When responses have temporal
extent — a plan that pays now for an amendment that pays later — the selection among
*continuations* is a further learning problem, and the candidate learner for it is
[Continuation BRIA](Continuation-BRIA): a duration-weighted bounded-inductive auction
over causal advisor continuations of the system's next block, run through the
constitutional wrapper, with accountable claims settled on realized block scores.  It
is a separate layer with a separate wealth account: traderized Logical Induction
supplies bounded belief and normative enforcement; BRIA allocates actual execution among
temporally extended continuations.  Nothing about the concrete Inductor realization is
thereby complete, and the coupling of LI predictions to BRIA claims is an open interface.

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
