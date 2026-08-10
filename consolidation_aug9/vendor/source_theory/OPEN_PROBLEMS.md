# Open problems

No item here is a proved claim.

1. **Tight jump recursion.** Determine the exact worst-case reference jump total
   under common \(\theta,\bar\varepsilon,R,M_{\rm ord},\Psi_0\). \(U_m\) is compositional and uniform but
   may be loose because it discards favorable movement and correlations between
   payoff extrema.
2. **Variable-core joint cap.** Replace the prefix-minimum reduction by a sharp
   recursion using the weighted `C-OF2` holdings when core strengths vary or
   oscillate.
3. **Weakest serviceable coverage.** Characterize when a terminal answerability
   route graph can be transformed into one whose endpoints are core-certified,
   without assuming a universally available suspension edge.
4. **Compiler choice and movement.** Among provenance-respecting certified
   references, compute a canonical choice minimizing worst-case jump while
   preserving public extensionality.  Geometry alone cannot choose the repair
   lineage (`C-PROV-IRR`).
5. **Full system formalization.** Encode the typed event order, projection stutter
   proof, and direct-product liability invariant.  Current Lean checks only the
   jump range and recurrence algebra.
6. **Conditional LI implementation.** Build the effective witness-extension
   compiler, recursive constrained history, clock integration, and solver needed
   by `C-MOVING-INTERFACE`; the joint theorem does not supply them.
7. **Behavioral challenge mechanism.** Add preferences, information, filing
   costs, and equilibrium.  The frozen positive-charge identity does not itself
   settle voluntary participation or nuisance incentives.

## Accountable migration frontiers

8. **Local-span composition theorem beyond two steps.** The two-step case is
   settled in `COMPOSITION_THEORY.md`: `CM-J2` gives the necessary and
   sufficient live-support condition for the fiber product of two arenas,
   `CM-J3` normalizes many-to-many intermediate lineage without duplicating
   ancestry, `CM-N1` supplies the liveness condition that cell-level authority
   counting was missing, and `CM-E1` exhibits a verified two-step history.  What
   remains open is the general statement `CM-J5` for `n` steps, and three
   specific gaps: whether pairwise live-support adequacy implies adequacy of the
   `n`-fold fiber product; whether consecutive-pair challenge-frontier coverage
   implies coverage at every prefix; and whether the per-step endpoint `NL-J3`
   recertification can be replaced by a composite condition.
9. **Weakest mixed conservativity condition.** Characterize exactly which old
   semantic objects must have new representations, which may remain as legacy
   carriers, and which explicit losses are compatible with the joint invariant.
10. **Reference lifts without full payoff coupling.** Determine whether the
    live-payoff polytope construction in `AM-J2` can be weakened while retaining
    the payoff-range jump proof and no holdings-norm assumption.
11. **Legacy collection.** Decide when a local comparison arena may be
    discarded after every referenced payoff settles and every suspended burden
    is terminally disposed, without breaking future provenance reconstruction or
    invalidating a later payoff-carrier lift.  `CM-C1` proposes a four-clause
    criterion and computes it, but only its sufficiency direction is exercised;
    its necessity quantifies over migrations the history does not contain and is
    blocked by `AM-X10`.  The displayed traces settle the two extremes — an
    unanswered challenge retains its whole lineage, a witnessed terminal
    disposition releases it — and in both the arenas stay retained because a
    contract is still outstanding.
12. **Migration-token governance.** Extend the single consuming migration token
    to a finite sequence policy without allowing candidate generation, funding,
    compiler choice, or semantic fit to self-authorize the next migration.

## Composition frontiers

13. **The capacity/rate conjecture.** Under bounded answerability capacity and a
    live case-arrival process, persistent substantive silence should not remain
    cost-free: it should appear as accumulating refusal liability, default load,
    or both. Turning this into a theorem needs a bounded-capacity hypothesis, an
    arrival process with a positive rate of well-formed queries, a solvency or
    budget constraint making accumulated liability bite, and a link from the
    liability stream to the bounded-force machinery. `CaseStreamLiabilities` is
    the typed interface; nothing else exists.

14. **Do tariffs do anything?** `CD-J1` accounts default and refusal liability
    exactly. Whether either changes what a learner does needs an optimization or
    solvency assumption this phase deliberately omits, and no behavioral claim is
    made.
15. **The adequacy oracle for merits.** The credal interval is supplied input.
    What makes an interval the *right* input, and how the book comes to have one
    for a filed query, is the interface where this meets the learning theory.
16. **The schema-rate theorem.** `CD-C1` records the canonical liability-key rule
    as a design proposal. Making it a theorem needs schema amortization, arrival
    asymptotics, and an aggregate objection model, none of which exist here.

17. **Necessity of the ledger transition conditions.** `AD-J1` shows (T1)-(T7)
    sufficient for conservation across finite linear histories. Whether each is
    necessary, and whether a weaker set suffices, is unproved.
18. **Branching and multi-actor dockets.** Everything in `AD-` assumes a linear
    singleton-actor history. `basis`, the event authorizations, and the
    identification certificate are the fields that would become actor-indexed;
    `AD-J5` is what makes the extension plausible, since identification never
    destroys a filer's record.
19. **Adopting `AD-C1`.** Whether a migration certificate can emit ledger events
    without disturbing any `AM-`, `CM-`, `ST-`, or `LG-` claim is unchecked, and
    the ledger remains a separate object until it is.
20. **What an adequacy oracle should be.** The coverage relation is parametric in
    it deliberately. Supplying a substantive theory of when a response answers a
    question is the point at which this work meets the learning theory, and
    nothing here constrains it.

21. **Weakest liveness condition.** Partly settled by
    `STANDING_TRANSPORT.md`. The provenance-sensitive transport condition
    permits the liveness lifts `CM-N1` needlessly forbids (902 cells on the
    realizable sub-scope) while blocking `CM-X1`, and it additionally blocks the
    burden disappearance and authority duplication `CM-N1` misses (291 cells).
    The two are incomparable; `CM-N1` conjoined with burden conservation and
    authority allocation implies the transport condition, not conversely
    (`ST-J5`). What remains open: whether condition 5's carrier-monotonicity
    clause is itself weakest; whether a still weaker provenance rule blocks
    `ST-X1` and benchmark case A; and whether any of this holds beyond cells of
    two inputs and two outputs.
22. **Local-to-global for liveness transport.** Partly answered by
    `LOCAL_TO_GLOBAL.md`. Liveness sponsorship composes by transitivity of the
    liveness order, and authority licences compose because the local condition is
    an injection (`LG-J2`). Burden transport does **not** compose: `LG-X1`
    exhibits two cells, each locally accepted, in which one witness closes two
    owed answers. What remains open is whether the ledger-relative repair
    (`LG-J5`) is sufficient beyond the bounded scope, whether it holds for
    histories deeper than two steps and cells larger than `(2,2)`, and whether
    `CM-J5` can then be restated with the transport condition in place of
    `CM-N1`. `CM-J5` remains **unrevised**.
23. **Adopting the transport plan into the one-step certificate.** `ST-C1`
    proposes five additions, of which two are load-bearing: a per-occurrence
    unresolved-burden bit, and input-scoped terminal dispositions. Whether
    adding them preserves every existing `AM-` and `CM-` claim is unchecked. A
    sixth question is whether the mixed-status many-to-many cell that `ST-X6`
    shows to be missing can be added without breaking `AM-J0`'s
    coefficient-one invariant.
24. **Necessity of the composability conditions.** `CM-J6` gives sufficient
    conditions for a certified composite; whether (L), (S), and the component
    construction are also necessary is unproved. In particular it is not known
    whether some non-component composite exists for the `authorized-loss`
    history, or whether the branch-disposition obstruction is unavoidable given
    any cell vocabulary satisfying `AM-J0`.
25. **Composite accounting.** `CM-X10` shows a composite can under-report the
    movement its history charged and consumes one token where the history
    consumed two. What is missing is a composite record that carries the
    history's jump count and per-step charges as first-class data, so that a
    summary cannot be mistaken for an account.
26. **General associativity.** Associativity is now *verified on one constructed
    three-step history* (`LG-J6`): both bracketings of a split-merge-split
    example agree with each other and with the direct fold on the outcome map.
    General associativity, for arbitrary finite linear histories and arbitrary
    cell shapes, remains **unproved**, and one machine-checked instance is not
    evidence for the general statement.
27. **Comparison objects weaker than the strict fiber product.** The fiber
    product is adequate here because `CM-J2` holds.  Determine whether a lax,
    weighted, or partial comparison object composes accountably when neither
    arena is surjective onto the intermediate ontology, and whether `AM-J4` still
    yields additive discrepancies there.
28. **Branching and several actors.** The version layer carries `actor_id` and
    `parent_version_id` but implements only the singleton-actor linear case.
    Adding concurrent proposals raises questions this phase does not touch: what
    a merge of two divergent version branches is, whether two grants can
    conflict, and whether the consuming-token policy of item 12 survives
    concurrency.
29. **Composite endpoint recertification.** `CM-J5` assumes the `NL-J3`
    endpoint conditions afresh at each version.  Characterize when they can be
    inherited across a composite instead, which is what would make a long history
    checkable in less than per-step full recertification.

30. **Persistence of a declared core minimum.** Containment of the core
    homothet is linear in the reference at fixed coefficient, so satisfiability
    of a declared core minimum *at a date* is a linear program with a declared
    branch on emptiness (`NL-SI-11`).  What no per-date program bounds is the
    infimum over time: whether a declared minimum keeps being satisfiable as
    settlement contracts the region.  The finite sweep (`NL-SI-10`) shows both
    outcomes occur on small instances — some pin trajectories preserve the
    coefficient and some collapse it to zero — so the question is now precisely
    conjectured rather than uninvestigated, and it is the residue the
    parametric composite carries as a hypothesis object.

31. **A coherence modulus, or a proof there is none.** The incoherence
    functional (`NL-SI-1`) defines the quantity a modulus would have to bound
    and makes conformance checkable in matched units.  Whether a given engine
    admits a computable tolerance schedule tending to zero, with its prices
    provably within the schedule at every finite date, is open in both
    directions.  The certification layering (`NL-SI-4`) lets the mechanism
    operate without one, at the price of the book carrying the liability, so
    this is a question about what can be certified rather than a blocker.

32. **Is the maximal core coefficient exact beyond the single-row case?**
    `single_row_core_coefficient` gives a closed form when one endorsed row
    binds, and the per-row minimum is an exact upper bound in general, but the
    joint optimum is a maximum over a polytope of a minimum of linear-fractional
    functions and is currently returned as a verified bracket.  Characterize
    when the per-row bound is attained, or give the finite candidate set the
    optimum always lies in.

33. **A dependent pin that neither collapses nor preserves the coefficient.**
    The sweep classifies dependent pins into those that void the coefficient and
    those that strictly lower it, and both occur.  What is not characterized is
    *which* — a condition on the endorsed rows and the pin that predicts the
    post-pin coefficient without recomputing it.  A transport lemma for
    dependent pins, with a computable loss term, is the natural target.

**Priority.** The highest-priority open item is registry completeness: the
grammar's per-table ablation gives witnesses for two of ten tables, and an
incomplete registry is the one gap that would make a footprint declaration
unsound rather than merely coarse. Next is the enforcement/extraction trade-off
inherited from the joint layer, then higher-dimensional sharpness for the
movement cap, which `NL-J2'-B` settles only in the scalar two-world setting.
Among the settlement-interface items, 30 is the one the composite actually leans
on: it is the single hypothesis object that separates the parametric result
from an unconditional core commitment.


## Identifier mapping (old to new)

External references to the previous numbering survive here.

| old | new | slug |
|---|---|---|
| 1 | 1 | `tight-jump-recursion` |
| 2 | 2 | `variable-core-joint-cap` |
| 3 | 3 | `weakest-serviceable-coverage` |
| 4 | 4 | `compiler-choice-and-movement` |
| 5 | 5 | `full-system-formalization` |
| 6 | 6 | `conditional-li-implementation` |
| 7 | 7 | `behavioral-challenge-mechanism` |
| 8 | 8 | `local-span-composition-theorem-beyond-two-steps` |
| 9 | 9 | `weakest-mixed-conservativity-condition` |
| 10 | 10 | `reference-lifts-without-full-payoff-coupling` |
| 11 | 11 | `legacy-collection` |
| 12 | 12 | `migration-token-governance` |
| 29 | 13 | `the-capacity-rate-conjecture` |
| 26 | 14 | `do-tariffs-do-anything` |
| 27 | 15 | `the-adequacy-oracle-for-merits` |
| 28 | 16 | `the-schema-rate-theorem` |
| 22 | 17 | `necessity-of-the-ledger-transition-conditions` |
| 23 | 18 | `branching-and-multi-actor-dockets` |
| 24 | 19 | `adopting-ad-c1` |
| 25 | 20 | `what-an-adequacy-oracle-should-be` |
| 13 | 21 | `weakest-liveness-condition` |
| 14 | 22 | `local-to-global-for-liveness-transport` |
| 15 | 23 | `adopting-the-transport-plan-into-the-one-step-certificate` |
| 16 | 24 | `necessity-of-the-composability-conditions` |
| 17 | 25 | `composite-accounting` |
| 18 | 26 | `general-associativity` |
| 19 | 27 | `comparison-objects-weaker-than-the-strict-fiber-product` |
| 20 | 28 | `branching-and-several-actors` |
| 21 | 29 | `composite-endpoint-recertification` |
