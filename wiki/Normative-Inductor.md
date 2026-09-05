# Normative Inductor

**Status: open / unregistered; the end-to-end theorem is conditional.** The
substrate — Logical Induction over an assessment process, projection enforcement, and
its preservation under bounded liability — is Established `lean-proved` in the
normativity registry. The realization's own contributions are nine kernel-checked
algebraic lemmas, ten exact-rational witnesses, and paper-level proofs; nothing new is
registered, and the composed theorem rests on hypotheses named below. The name is
provisional.

The Normative Inductor is the program's concrete candidate for a bounded reasoner that
realizes [normative induction](Normative-Induction): a Logical Inductor made to answer
to legitimately incurred obligations, without ceasing to be a Logical Inductor.

## The architecture

```text
qualitative legitimate obligations
        |
        v
proof-carrying compiler
        |
        v
joint feasible convex operative region K_s
        |
        v
projection-based normative enforcer
        |
        v
small public defect d_s = dist_infinity(b_s, K_s)
        |
        +---- external authenticated value/response semantics
        |
        v
Decision Adapter / practical response
        |
        v
anchored Progress
```

As a formula,

    NI = MarketMaker( TradingFirm^L + JointProjectionEnforcer[ Compile(O_P) ] )
         + DecisionAdapter .

The ordinary Trading Firm over the language `L` is the substrate and is left alone.
One additional trader — the enforcer — is added to the aggregate the market maker
prices against, and its position is bounded in liability. The Decision Adapter
*consumes* the market state; it is not another trader inside the market maker's fixed
point, and it does not feed back into prices. Enforcement is additive: the
construction does not replace Logical Induction or constrain the price-setter directly,
which is why every theorem about the underlying inductor survives.

## From obligations to a region

The compiler receives, at a strict prefix of the history, the bundle of live
obligations to be serviced together, each with its immutable anchor, its authenticated
current semantic realization, its standing and licence provenance, and the settlement
facts and security basis available at that prefix. It returns either a compiled region
or an accountable failure.

A compiled result is **one joint convex region** `K_s` for every constraint serviced at
that date, presented as a finite system of rational inequalities over canonical
security identities, with a nonemptiness witness. Simultaneously serviced constraints
are conjoined, not run as independent per-reason traders: two individually feasible
constraints can have an empty conjunction, and independent enforcers can oppose one
another so that aggregate uptake says nothing about either.

Five properties are kept distinct, because conflating them has cost the program real
errors:

- **compiler correctness** — every emitted row is an authenticated current realization
  of the obligation it cites, or a separately authenticated structural or value row;
- **compiler completeness** — the implementation finds a realization whenever one
  exists in its declared schema, and only relative to that schema;
- **convex representability** — the obligation *has* a sound convex price-space
  realization at all, which is a property of the obligation language, not the compiler;
- **joint feasibility** — the realizations of the serviced bundle intersect;
- **affordable enforceability** — the joint region can be enforced within a liability
  budget over time, which is a scheduling question and needs no interior or core
  assumption for projection itself.

If conjunction fails, the compiler returns a conflict core or `Unknown` **and
conserves every cited obligation**: nothing is dropped, reweighted, or presented as an
empty region to the enforcer. A new adjudication obligation arises only if an upstream
licensed rule of the practice says that such a conflict requires one; hierarchical or
weighted dropping is likewise legitimate only when a licensed rule makes it part of the
anchored answer specification. It is never default compiler behaviour.

## Enforcement, and the public defect

The enforcer is the projection trader of the traderized-enforcement construction:
Euclidean projection of the displayed prices onto `K_s`, scaled by a prospective
multiplier `λ_s`. Euclidean projection is the *implementation* — it is what makes the
enforcer a legal, effectively compilable trading strategy with a proved work bound.

The public interface is different, and the difference was forced by a counterexample.
The **public operative defect** is the sup-distance to the joint region and the
**service intensity** is the multiplier itself:

    d_s(b) = dist_∞(b, K_s),        a_s = λ_s .

An earlier convention divided the Euclidean distance by the square root of the
dimension and multiplied the intensity by the dimension. It was rejected because padding
a fragment with harmless zero-error coordinates lowered the reported defect and raised
the reported service while leaving the enforcement work unchanged — a compiler could
report improvement by adding irrelevant coordinates. Sup-distance and the bare
multiplier are exactly invariant under that padding.

The work relation the theory needs is an inequality, not an equality:

    λ_s · d_s²  ≤  λ_s · ‖b_s − proj²_{K_s}(b_s)‖₂²  ≤  ρ_s ,

so the kernel-checked Euclidean projection-work bound controls the public work quantity
without anyone claiming the two are the same.

Presentation invariance is claimed exactly this far: canonical security identities;
enforcement-null product padding; the ordinary book and market resistance unchanged.
It is **not** claimed under arbitrary affine reparameterization, under duplication with
inconsistent prices, or under the addition of genuinely new tradable content, each of
which can legitimately change the defect. Aliases are rejected at the compiler.

## Admissibility is not value

The region says which market states the serviced obligations *admit*. It does not say
that any admitted state contains the true value of a policy.

The exact example: a fragment with one normative coordinate pinned to one half and two
unconstrained displayed policy values. A state inside the region has zero defect —
Euclidean and sup — and its displayed best policy is the one whose authenticated
counterfactual value is the worst. Projection onto `K_s` certifies closeness to an
admissible operative region and nothing about which action is good.

So the realization needs an **externally authenticated practical interface**. Its
typical internal witness is a *value correspondence* `V_es` — a nonempty set of possible
counterfactual value vectors for a finite policy menu — with a target vector `v*_es`
that lies in it, an ambiguity bound `ζ_es` on how far any admitted value coordinate can
sit from the target, and a calibration certificate issued *before* the response is
observed. Calibration then gives, for a randomized approximate optimizer with
optimization error `η_s`,

    Regret_{v*}  ≤  2 d_s + 2 ζ_es + η_s ,

and an independently authenticated anchored-response theorem carries that regret into
the abstract practical-response certificate with constants

    M_es = 2 L_es ,        ε_es = L_es (2 ζ_es + η_s) + ε^resp_es .

The projection point is a proof witness for the calibration step. It is never described
as the true or certified value vector.

## Joint feasibility is not joint response compatibility

One service occurrence realizes **one** response distribution, and it may be matched to
several obligation exposures. Every matched edge must carry its own response
certificate against that *same* realized distribution:

    joint price-space feasibility  ⇏  joint practical-response compatibility .

Two obligations can sit inside one nonempty `K_s` while no single response is adequate
for both. This is a realization obligation: the abstract admissible-edge relation
already admits an edge only when its practical-response certificate exists, so the
excluded mass appears as residual and is paid for. When matched obligations demand
incompatible responses the realization may separate them into distinct service
contexts, invoke a licensed upstream adjudication or aggregation rule, find a common
adequate response, or leave part of the evaluation mass unserved. It may not charge two
edges to a response that only one of them certifies.

## Settlement, three ways

The construction uses one full history and three distinct settlement functions
([Settlement interface](Settlement-Interface)): certified reports translated into
sentences the assessment process settles; settlement facts as citable grounds for a
disposition, whose relevance stays a history question; and typed receipts that
terminally discharge an anchored obligation, which no participant's challenge, verdict
or quote can manufacture. Value securities share the settlement namespace only when
their payout is rigidly defined by it, and counterfactual policy value usually needs
more than terminal outcome settlement — that extra identification belongs to the
external practical interface and is never inferred by the inductor.

## Service transport back to exposure

Service happens on dates; obligations were incurred on other dates. A committed
transport plan carries service back to historical exposure, and the amplification
factor of the abstract bound is its worst weighted column load. The older fixed-era
service theorems normalize exactly into this interface, with the product of the
Lipschitz and service-to-obligation constants as one admissible amplification; that
normalization step is one of the kernel-checked lemmas, and the older theorems it
consumes stay at their own evidence class.

## What the substrate guarantees

Established results the realization stands on: the Logical Induction criterion
generalized to an assessment process; the projection strategy as a legal,
finite-support, effectively compilable trader; finite-time conformance to the region
within a declared tolerance; preservation of the criterion under a uniform bound on the
enforcer's assessed liability; and, in the deductive case, zero liability with the
source's original criterion recovered. Upgrading preservation to a packaged Logical
Inductor also needs the augmented market to be computable, which the effective
compiler supplies in the registered deductive case and which stays an explicit premise
for a general assessment process with arbitrary regions.

## Remaining realization obligations

These are implementation and theorem obligations, not foundational confusion. Each is
named in the realization report with its dependencies.

- one unified concrete representation of the history's events;
- the export theorem from that history to the qualitative obligation process;
- compiler soundness for a declared obligation schema;
- convex representability of the chosen obligation language;
- joint feasibility, or accountable conflict, for serviced bundles;
- affordable service under a declared workload class — the predictable-window
  cheapest-date scheduler is a proved conditional instance; the general online problem
  is open;
- joint practical-response compatibility;
- quantitative semantic-transport certificates — the composition algebra is
  kernel-checked, the generation of constants is not;
- effective, computable packaging of the augmented market;
- the composed end-to-end theorem, and its Lean formalization.

## What is checked and what is not

Kernel-checked here: the deterministic and randomized approximate-argmax transfer,
calibration through a value correspondence, domination of the public work by the
projection work, the failure of the old normalization under padding, decision and
semantic certificate composition, and the old-service-to-amplification normalization.
One of those lemmas, exact carry, says only that an *already certified* identity
transport edge composes as the identity; it does not say that defeat or disposition has
that semantic certificate, which remains an external premise. Exact rationals check
the padding counterexample, the invariance of the replacement, the projection/value
counterexample, the shared-service Progress arithmetic, and reason incompatibility as
finite instances. The general Progress theorem is not newly Lean-proved. The end-to-end
theorem is conditional on the ambient, history, compiler, scheduler, and semantic
hypotheses listed by owner in the realization report.

---

**Evidence.** The construction, witness table, theorem spine, evidence ledger, exact
final bound and remaining tasks are
[`NORMATIVE_INDUCTOR_REALIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/NORMATIVE_INDUCTOR_REALIZATION.md);
the padding analysis, value counterexample and randomized bridge are
[`PRESENTATION_AND_VALUE_SEMANTICS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/PRESENTATION_AND_VALUE_SEMANTICS.md);
the local ledger with each result's evidence class is
[`THEOREMS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/THEOREMS.md);
the Lean lemmas are
[`NormativeInductor.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/lean/Workspace/Normativity/Contrib/NormativeInductor.lean).
The substrate's registered claims are in the
[normativity claims registry](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/CLAIMS.md)
and the enforcement construction is summarized on
[Actionability and normative force](Actionability-and-Normative-Force).
