# Surgical final pass: projective semantics, stale theorem removal, claim discipline

Continue on PR #38. A **narrow final pass**; do not reopen the force mechanism
unless a genuine new counterexample appears.

**The typing issue.** The model says `Ω_t = {0,1}^{Φ_t}` with `C_t ⊆ Δ(Ω_t)`, but
the lift is stated as `L_{t+1} ⊆ L_t` and as though `L_t` answers restriction
queries on arbitrary finite sentence sets. Those do not type-check when the priced
fragment grows. Prosecute two architectures — global worlds with finite marginals,
or projective finite-fragment semantics with restriction coherence replacing
literal nesting — and choose by fit to the source construction and the repo's
finite discipline, not by prose elegance. Then state the live-world process at the
exact type the Budgeter consumes, with an interface `worlds(t, S)` and only the
weakest properties the source proofs actually use: restriction consistency,
temporal persistence on common supports, effective finite presentation,
nonemptiness. Restate the lift so its objects type-check, naming the source step
each hypothesis pays for.

**Deduction** must instantiate that interface exactly, with temporal nesting,
effective presentation, restriction coherence, nonemptiness, Budgeter
specialization and criterion specialization all checked.

**Remove the stale false deductive theorem** derived from `K^D`; keep it only as
explicitly withdrawn, pointing at the anticorrelated-mixture counterexample.

**Remove the remaining exactness overclaim** — do not say every lower-dimensional
region in no proper cube face is impossible; keep the four earned evidence levels.

**Purge accidental necessity language**: world-inclusivity, deficit summability,
support coverage and bounded liability are all sufficient, none proved necessary.
State the open converse explicitly.

**Generalize enforcement liability** to the live-world process first, with
`PC(D_t)` as the deductive specialization, and flow that notation through every
surface. **Fix exact-steering language**: the stable API guarantees conformance,
not `P_t ∈ K_t`, and "whoever writes the rows sets the displayed price" needs
exactness hypotheses.

**Recheck the source-side legality claim** for consistency only; keep it `derived`.

Add projective-semantics regressions: growing fragment, a failure case the
validator rejects, Budgeter restriction, and the deductive case over two growing
fragments. Update the theorem map and paper spine, run the stale-claim search, and
rewrite the PR body.

# Addendum — the motivating Normativity application must discharge safety

Do **not** require exact finite-time enforcement of the motivating normative
constraint. Tolerance-level conformance `g_{t,j}(P_t) ≤ δ_t` is the intended
application, analogous to the market maker's own positive slack. Exactness keeps
its classification as a force-theory result but is **not** a success criterion for
the Normativity instantiation.

The essential requirement is instead: **show that the motivating
normative-constraint statics can satisfy the bounded-enforcement-liability
hypothesis needed to preserve nonexploitability.**

Identify the exact motivating process — post-settlement simplex, endorsed region,
declared core minimum, `NL-SI-A2`'s admissible-reference polytope, its priceable
row presentation, the surrounding settlement/tolerance machinery — and write down
`K_t^norm` and `E_t^norm`, separating rows by source and not conflating their
liability properties. State the safety obligation as a finite `B` bounding
`inf over n and live ω of ω(Σ_{t≤n} E_t^norm)`.

Audit the existing statics — `P2`, participant budgets, core-minimum persistence,
settlement monotonicity, no-claw-back, finite gating, tolerance schedule,
endorsement leverage, the liability accounting, any cumulative-outflow discipline
— with an exact type comparison for each candidate, and conclude: safety already
follows; follows after a small bridge lemma; or a new quantitative condition is
needed. Try the deficit route first, then the support-capacity route. Pay
particular attention to persistent normative disagreement, where an endorsement
stays in force while a live world violates it, and identify what actually prevents
unbounded loss there.

Build at least one full multi-date motivating trajectory, preferably two: a safe
instance with `B < ∞` and a minimally altered unsafe contrast. Give one of three
verdicts, keep the distinction from `P2` explicit, update item 39 so success
requires both force generation and safety discharge, and classify the Normativity
application separately from the core paper.

Success: answer *why doesn't the trader enforcing the motivating normative
constraint become an unlimited subsidy that destroys nonexploitability* with a
theorem, a theorem plus one explicit source condition, or a counterexample. A
statement that bounded liability would suffice is not enough.
