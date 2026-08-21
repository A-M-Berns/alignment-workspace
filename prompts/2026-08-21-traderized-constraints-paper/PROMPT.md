Work in the current `A-M-Berns/alignment-workspace` repository.

Goal
====

Create a small standalone, paper-facing Lean companion for the paper

    Strengthening Logical Induction with Traderized Constraints

The artifact should mirror the mathematical paper rather than the backend module structure.

Stage it for now in a new folder:

    lean/Workspace/TraderizedConstraints/

Do NOT move the existing backend formalization. The existing theorem library under
`lean/Workspace/Normativity/Contrib/` should remain the implementation backend.

Read the repository instructions (`AGENTS.md`, relevant CONTRIBUTING/docs, lake setup) before editing.

High-level deliverable
======================

Prefer this shape:

    lean/Workspace/TraderizedConstraints/
      Computability.lean   -- only if useful for isolating the computability lift
      Paper.lean           -- thin public paper-facing API

A very short README is optional if it materially helps explain the relation between
the paper-facing declarations and the backend, but do not create documentation noise.

The artifact should satisfy:

    paper statement
        ↕
    Paper.lean declaration
        ↓
    existing checked backend theorem(s)

Do not duplicate substantial mathematical proofs merely to obtain nicer theorem names.

Most important new formal work: Computable schedule lift
========================================================

The current checked end-to-end theorem uses primitive-recursive hypotheses for the
fragment/tolerance schedule. The paper now states the mathematically natural result
for ordinary total computable schedules.

Generalize this interface.

The intended mathematical claim is:

- the finite-data rational-polytope projector compiler can remain primitive recursive;
- composing that compiler with merely computable schedule data should yield a computable
  enforcement trader;
- the modified LIA recurrence should therefore be computable;
- the generic and deductive paper-facing theorems should require only ordinary
  `Computable` schedule hypotheses.

Important: do NOT pretend that a `Computable` function is `Primrec`.

Inspect the exact existing interfaces before changing anything. In particular, locate
the current schedule/enforcer computation structures and the bounded-evaluator compiler.
The likely issue is that some current structures ask for a `Primrec` trade hook even
though the downstream Logical Induction compiler ultimately only requires computability.

Add a genuine computable-level path, schematically:

    computable enforcement-trade hook
        -> computable bounded modified-LIA recurrence
        -> computable bounded evaluator / market

Reuse existing primitive-recursive helper results via `Primrec.to_comp` wherever possible.

Preserve the existing primitive-recursive results. They are stronger finite-data
implementation facts and should remain available.

Do not make an efficiency claim.

Paper-facing API
================

Aim to expose declarations corresponding closely to the current paper results.

The exact Lean names may vary slightly if the types demand it, but keep the public API
human-readable and paper-shaped.

§2 Quantitative constraints as trades

    projection_trade_profitable_on_constraint

This should correspond to the paper result that for q = proj_K(p) and y in K,

    (q - p) · (y - p) >= ||q - p||^2

and therefore the scaled projection trade has value at least

    lambda * dist(p,K)^2.

§3 Finite-time enforcement

    one_day_enforcement

    constraint_schedule_compilation

    constraint_schedules_enforceable

The paper-facing constraint schedule bakes in:

- a finite fragment on each date;
- a nonempty rational-polytope constraint region;
- a positive rational tolerance;
- computable fragment, rational-vertex, and tolerance data.

The traderized LIA recurrence must preserve the original source TradingFirm and
MarketMaker and should have the form corresponding to

    P_n =
      MarketMaker_n(
        TradingFirm^D_n(P_{<=n-1}) + E_n,
        P_{<=n-1})

where TradingFirm is evaluated on the modified prior price history.

§4 Preserving logical induction

    tradingFirm_upper_bound_under_bounded_enforcement

    bounded_liability_preserves_lic

    li_with_quantitative_constraints

    plausible_worlds_zero_liability

Lifetime liability should match the paper's quantified definition: one finite B such
that for every horizon N and every world still plausible at N, cumulative enforcement
value through N is at least -B.

The generic headline theorem should express:

    constraint schedule
    + bounded lifetime liability
    -> resulting market is a logical inductor
    + every requested datewise distance bound.

§5 Deduction at zero liability

    deductive_regions_form_constraint_schedule

    strengthened_logical_induction

    different_deductive_processes

The deductive region is

    K_n^D =
      conv { W|Phi_n : W in PC(D_n) }.

The paper-facing strengthened theorem should have the following conceptual shape.

Assume:

- D is a deductive process;
- each finite stage is propositionally satisfiable;
- Phi is a computable finite-fragment schedule;
- delta is a computable positive rational tolerance schedule.

Let E^D be the corresponding deductive projection enforcement trader, and let P be
the pricing sequence produced by adding E^D to the ordinary LIA construction.

Then prove together:

(a) P is a logical inductor over D;

(b) for every n,

      dist(P_n|Phi_n, K_n^D) <= delta_n;

(c) E^D has zero lifetime liability relative to D.

The public theorem should not require random-access primitive recursion of n ↦ D_n.
Retain the source-style stage-by-stage deductive-process computation interface.

For the two-deductive-process result, the exact sufficient condition is fragmentwise:

    W in PC(D_n)
      -> W|Phi_n in K_n^{D'}

for every n.

Full world-set inclusion PC(D_n) ⊆ PC(D'_n) is only a stronger sufficient condition.

§6 Beyond zero liability

    projection_loss_controlled_by_distance

Expose the sharp local inequality if it is clean to do so:

    W(E_n) >= lambda_n (d_n^2 - d_n e_n(W))

where

    d_n = dist(P_n|Phi_n, K_n)
    e_n(W) = dist(W|Phi_n, K_n).

Implementation discipline
=========================

- Keep `Paper.lean` small.
- Prefer wrappers/compositions over duplicated proofs.
- Do not rename or refactor large backend areas merely for cosmetic paper alignment.
- Small backend helper lemmas or a computable-level parallel interface are fine where
  genuinely needed for the computability lift.
- Preserve original Logical Induction abstractions and criterion.
- Do not replace or modify MarketMaker itself.
- Do not introduce paper terminology such as “effective,” “conformance,”
  “projection force,” or backend class names unless unavoidable internally.
- Public comments should use paper language:
    constraint region,
    projection trade,
    enforcement trader,
    lifetime liability,
    deductive region.
- No `sorry`.
- Do not add axioms.

Validation
==========

Run the appropriate Lake/Lean build for all files touched.

Then explicitly audit:

1. no `sorry`;
2. no unexpected axioms;
3. `Paper.lean` imports and compiles independently as the paper-facing entry point;
4. the computable schedule theorem really has `Computable` hypotheses, not hidden
   `Primrec` assumptions;
5. the strengthened theorem has exactly the three paper conclusions above;
6. existing primitive-recursive theorems still compile.

If a truly substantive obstacle prevents the `Primrec -> Computable` lift, do not weaken
or alter the paper theorem silently. Isolate the exact obstruction and report it.

Final report
============

At the end, report concisely:

- files added/changed;
- public declarations in `Paper.lean`;
- what new computability lemmas/interfaces were required;
- whether the full `Computable` schedule lift succeeded;
- exact assumptions of the final strengthened theorem;
- build commands/results;
- sorry/axiom audit;
- any remaining mismatch between the Lean artifact and the current paper.

The desired outcome is a thin, readable companion artifact, not another large formalization.
