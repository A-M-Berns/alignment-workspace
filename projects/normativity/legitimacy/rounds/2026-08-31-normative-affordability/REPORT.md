# Report

## 1. The recommended theorem stack

Eight results, ordered by dependency. Every one is stated and proved in this
round's documents; none is registered, and none is in Lean.

1. **Service Transfer (T1) and its exact converse (T2).** For bounded defect
   arrays, `E_{nu_N}[d] -> 0` and `mu ◁ nu` give `E_{mu_N}[d] -> 0`; and
   contiguity is necessary, with indicator arrays as the extremal witnesses.
   Contiguity equals asymptotic uniform absolute continuity (T1.0), so that is
   not a separate condition. A bounded density gives the quantitative form
   (T1.1). For `N`-independent defect sequences the exact condition is instead
   fixed-set contiguity (T2'), which is strictly weaker; the separating instance
   is one-step delay. The array version is the one this theory needs, because a
   settlement-relative defect is re-assessed at every horizon.
2. **Deferred Service Transfer (T3).** A feasible adapted transport plan with
   stability `(L, eps)`, a service-to-claim cap `K` and vanishing residual gives
   `E_{mu_N}[d] <= L K E_{nu_N}[d] + eps + D R_N/C_N`. Contiguity is a
   consequence, not a hypothesis. Depends on nothing above; T1.1 is used inside
   the proof.
3. **Joint Actionability by common-region superposition (T4).** Individual
   Actionability, additive aggregation, nonnegative weights and a nonempty common
   region give `G >= sum_r w^r gamma_r d^r`. Corollary: the composition weights
   are the service intensities.
4. **Non-revocation of safety certificates (T5).** A settlement-antitone robust
   risk makes a certified prefix stay certified under every extension.
5. **Sustainable Progress (T6).** T3 + T4 (or per-reason Uptake) + T5's
   preservation give `limsup E_{mu^r_N}[d^r] <= eps_r`. Five premise-removal
   countermodels, each hitting a different object.
6. **Backlog-to-transport (E1) and existence by drift (T7).** Bounded backlog
   yields an adapted FIFO plan with vanishing residual and, under a window
   service floor, a delay bound; a self-financing slack condition makes
   max-weight scheduling a witness. T7 is a proof sketch.
7. **Overload certificates (T8).** A Farkas pair `(y, z)` with positive deficit
   refutes finite-horizon affordability. Sound for the causal problem; not
   complete.
8. **The realization identities.** The score identity
   `<zeta, x - p> = (lambda/2)(Br_x(p) - Br_x(q) + d^2)`, the friction inequality
   `>= lambda(d^2 - de)` with equality for a halfspace and an outside world, and
   the core-minimum misfit bound `dist(x, S) <= (1 - theta)|x - q|`.

## 2. Direct answers to the governing questions

**Is contiguity the correct and minimal Service Transfer condition?** Correct and
exactly minimal as a *characterization* for triangular arrays (T1, T2). Not
minimal as an *interface*: T3 derives it from a checkable finite-horizon object.
The triangular-array caveat the dispatch flags is real and resolves the other way
from what the flag suggests — the naive indicator counterexample does need an
`N`-dependent defect, and the fixed-sequence condition is strictly weaker (T2'),
but settlement-relative assessment makes the defect `N`-dependent, so the strong
version is the one in force.

**Which of the stronger sufficient conditions is the right interface?** The
pointwise sandwich `eta c <= w <= K c` is sufficient and forbids deferral.
Uniform absolute continuity is contiguity restated. Bounded Radon–Nikodym density
is the quantitative form and is what T3 produces internally. Prefix-discrepancy,
queue-stability, bounded-delay and fair-scheduling conditions are **not**
sufficient — the rotation countermodel has delay 1 and backlog 1 — and their
correct role is to establish that a transport plan exists (E1). The interface is
the plan and its constants.

**Does individual Actionability compose?** No, when the gain is read against
reason-relative regions; the countermodel has jointly satisfiable demands, so
conflict is not the mechanism. Yes, when read against the common region, and the
sufficient conditions are only additivity and positive homogeneity of the
aggregation — convexity, separability, noninterference and superposition-as-an-
axiom are not needed.

**What does traderized Logical Induction get for free?** Additivity of positions;
a common scoring set, since every position is scored against the same live
assessment worlds; and per-reason Uptake, since the criterion quantifies over each
efficiently computable trader separately. Not free: nonemptiness of the
intersection of the demands with the assessment set, which is covered
compatibility; and the reactive fixed point, which is the construction rather than
a theorem about arbitrary engines.

**What is the minimal SafeCert type?** A prefix-closed class of control histories
whose membership is antitone in settlement. Actual-path safety is not a candidate
at all: it is not measurable at the date the control must be chosen. An account, a
risk functional or a burden monoid are presentations, not interface content; an
ordered monoid buys nothing over `R`, or `R^k` with the product order for
incomparable budgets.

**Should the analogous history-relative risk be robust?** Yes, and the argument is
not a preference: predictability of the controller forces it, and settlement
monotonicity then makes prefix closure and time consistency automatic rather than
axioms.

**Does overload admit a dual certificate?** One direction. A positive-deficit
Farkas pair on any settlement-consistent path refutes affordability. The converse
fails because the per-path relaxation hands the controller the path; no exact
dynamic alternative is offered, and the dispatch's dichotomy is therefore not
established.

**Do deferral and cross-era transport unify?** The inequality does — the same
`(T3)` with a plan whose support crosses the boundary. The provenance of the
constants does not: delay stability is persistence of one defect, era stability
needs a semantic bridge fixing which successor coordinate is compared against.
Unify the interface, not the construction.

**Is immutable history enough for no-reset?** For claims, pins, created exposures
and the account, yes, and T5 is the reason. Semantic transport is needed only for
what is still owed; an exposure already created keeps its original semantics
because settlements are never re-spoken.

## 3. Which hypotheses are schematic and which are realization-specific

| hypothesis | class |
|---|---|
| transport feasibility `(T1)`, `(T2)` | schematic; supplied by a scheduler |
| transport stability `(T3)` | schematic; supplied by the reason's semantics, never by a scheduler |
| service parsimony `W_N <= K C_N` | schematic |
| nonempty common region | schematic; realized as covered compatibility |
| additive aggregation | realization-specific (free in traderization) |
| per-reason Uptake | realization-specific (free in traderization) |
| share persistence | schematic, and needed only on the aggregate-Uptake route |
| prefix closure, settlement monotonicity | schematic; properties of the settlement interface |
| `SafeCert ==> Uptake` | realization-specific; the traderized instance is bounded liability implies preservation |
| bounded-liability accounting, Brier form, core minimum | realization-specific |
| self-financing slack | schematic, and the place existence actually fails |

## 4. Deviations from the dispatch

1. **The boxed conclusion is weakened.** The composition gives
   `limsup E_{mu^r}[d^r] <= eps_r`, not `-> 0`. Exact transport stability closes
   the gap and nothing else in the premises does.
2. **Contiguity is deleted from the definition** and replaced by the transport
   plan, against the dispatch's clause 2 as written. The dispatch invited this
   ("or whatever weaker correct Service Transfer condition replaces this"), and
   the replacement is not weaker but differently placed: it is stronger as a
   hypothesis and checkable, where contiguity is weaker and is not.
3. **The `J_t` type loses its third coordinate.** `q_t^r` is the reason's own
   position and carrying it separately invites the reason-relative scoring the
   interference countermodel exploits.
4. **The dispatch's reading of Surface Fairness is corrected rather than used.**
   The inherited service hypothesis does not support a claim-weighted conclusion,
   and the round does not repair the merged schematic — it exhibits the gap and
   states the replacement interface.
5. **Priority 4 is delivered at lower strength than the rest.** T7 is a proof
   sketch with a standard drift argument and no inhabitation fixture; the other
   theorems are proved and their instances are exact.
6. **The round's `depends_on` is empty.** It reads the Progress and liability
   research checkpoints and refutes one of their hypotheses, but consumes none of
   their results, so nothing is claimed as a hypothesis. That is accurate here and
   would not have been available had a result been consumed: those checkpoints
   carry no round records, so no `depends_on` can name them. Filed as
   `PRIORITIES.md` *Workspace friction* F7.
7. **No Lean.** Nothing here is close enough to a settled definition to formalize;
   the algebra is elementary and the open seams are the substance.

## 5. What this round does not establish

Every document carries its own list; the ones that matter across the round:

- **No existence theorem.** T7 is a sketch, its condition 4 is the strong one, and
  nothing here shows it is ever satisfied in a traderized instance with
  unboundedly many live reasons.
- **No completeness for T8.** The dichotomy the dispatch hoped for is one
  implication and a counterexample-free gap, not a theorem.
- **`eps_r = 0` is never constructed.** Every claim-weighted conclusion in this
  round is up to a transport error that no result bounds by zero.
- **Answer-Mode Adequacy is assumed throughout.** `gamma_r` and `d^r` being
  correctly recognized is the semantic boundary of the whole family, and this
  round does not touch it.
- **The countermodels are two-reason instances.** Nothing here shows they exhaust
  the failure modes at larger reason sets.
- **The realization identities are checked on a rational halfspace.** The convex
  case follows from the projection property and is not machine-checked.
- **`test-supported` is the ceiling.** Forty-four exact-rational checks illustrate
  finite instances of theorems proved in prose; the proofs are the evidence, and
  the fixtures are the guard against a proof about nothing.

## 6. Strongest unresolved questions

1. Is there an exact alternative for the *causal* affordability problem — an
   overload certificate class that is complete as well as sound? Flow/cut duality
   on the transport plan is the obvious place to look, since T3's plan is already
   a flow.
2. Can exact transport stability (`eps_r = 0`) be certified for any reason type
   that a practice actually produces, or is the claim-weighted conclusion always
   approximate?
3. Does self-financing slack ever hold with a growing reason set? Observation E2
   says a fixed budget funds a bounded total of non-self-financing service, so a
   growing set of persistent reasons must be served almost entirely by controls
   that are nonnegative in every live assessment.
4. Is per-reason Uptake available outside logical induction — in a regret-bearing
   online learner, is each reason's own comparator guaranteed separately?
5. What certifies `(T3)`'s constants across an era boundary? That is the semantic
   bridge, and it is the one obligation in the stack with no candidate mechanism.

## 7. New names introduced

All provisional. **Service parsimony** (the cap `W_N <= K C_N`). **Transport
stability** (the `(T3)` inequality and its constants `(L, eps)`). **Self-financing
control** (robust liability increment at most zero). **Overload certificate** (the
Farkas pair `(y, z)` with positive deficit). **Fixed-set contiguity** (the exact
condition for `N`-independent defect sequences). The dispatch's own provisional
terms — affordability witness, claim measure, actual service measure — are kept as
given.

## 8. Outstanding maintainer actions

1. **Rule on what Progress means: claim-weighted or service-weighted.** The
   merged schematic concludes `D_N/W_N -> 0`, which this round shows is
   compatible with never touching a defective date. Making Progress
   claim-weighted imports the transport interface and its `eps` residual into the
   settled statement; leaving it service-weighted keeps the current theorem and
   moves the burden onto whatever consumes it. *Turns on:* what the paper's
   Progress claim has to be able to say — external knowledge the round lacks.
   Appended to `DECISIONS.md`, *Awaiting the author*.
2. **Naming audit** over §7 when one is next run.

The residual blocker of §6.1 is filed as `PRIORITIES.md` item 74, naming the round
that would consume it.

Everything else this round recommends is adopted as a dated `DECISIONS.md` entry,
agent-decided and reversible.

## Attribution

| field | value |
|---|---|
| prompt author | unrecorded — authored outside this repository |
| executor | Claude Opus 5 (Anthropic) |
| dates | dispatched and executed 2026-08-31 |
| round record | `prompts/2026-08-31-normative-affordability/` |
