# Provenance-sensitive liveness transport

## 0. Verdict and authority

The authoritative inputs are `MIGRATION_THEORY.md` (`AM-J0`–`AM-X17`) and
`COMPOSITION_THEORY.md` (`CM-J0`–`CM-X8`).  No claim of either is altered,
deleted, or weakened.  `CM-N1` retains its status as an established sufficient
condition; what follows shows it is a **coarse** one, and locates exactly where.
The frozen one-step verifier `src/migration.py` is unchanged; this phase adds
`src/standing.py` and gives its claims the `ST-` namespace.

**Lead verdict: `CM-N1` is both too strong and too weak, and the two failures
are on different axes.**

- *Too strong.* `CM-N1` quantifies universally over inputs, so it rejects any
  merge in which one input is weaker than the output — including the safe case
  in which a live authoritative input alone sponsors the merged liveness while
  the suspended input's burden continues on a residual.  On the realizable
  search space of §7 there are **902** such cells.
- *Too weak.* `CM-N1` says nothing about burdens and nothing about allocation.
  It accepts a one-input, one-output cell that simply drops an unresolved
  burden, and it accepts a split that assigns one authority source to two
  authoritative outputs.  On the same space there are **291** such cells.

The two conditions are therefore **incomparable**.  The replacement is not a
weakening of `CM-N1` but a re-analysis of it into four separately typed
relations, of which `CM-N1` conflates three.

The central finding is narrower and sharper than expected:

> The original laundering merge is not a liveness-lift failure.  It is a
> **burden-disappearance** failure.  What must not happen is that an occurrence
> suspended for an unanswered challenge is consumed without its burden either
> continuing on a carrier or being answered.  Whether the *semantic* content
> merges is irrelevant; whether the *liveness* strengthens is a consequence, not
> the fault.

A merge of concepts need not be a merger of reasons.  Semantic identification
buys no entitlement, no authority, and no discharge.

## 1. What a transport plan must distinguish

Each disposition cell `d` with inputs `A_d` and outputs `B_d` carries one
**liveness transport plan** with four separate relations and two record sets:

| component | type | answers |
|---|---|---|
| `semantic_support` | `A_d x B_d` | which inputs contribute content to each output |
| `standing_support` | `A_d x B_d` | which inputs sponsor each output's liveness |
| `authority_support` | `A_d x B_d` | which input authority licenses each authoritative output |
| `burden_routes` | `A_d -> B_d + terminations` | where each unresolved burden goes |
| `terminations` | scoped to one **input** | which input dimensions end, and how |
| `grants` | scoped to one **output** | which positive warrants license what |

Three separations are load-bearing and none is derivable from another.

**Semantic merger is not deontic merger.** `semantic_support` may be total while
`standing_support` is a single edge.  The predicate never reads
`semantic_support` when deciding sponsorship, authority, or burdens; `ST-N1`
makes this exact.

**Occurrence lineage is not liveness provenance.** Sharing a cell — hence
sharing occurrence ancestry under `AM-J0` — is what a merge *is*.  It is not
evidence that the shared ancestors sponsor anything.  `standing_support` must be
declared, and only inputs at least as strong as the output count.

**Liveness sponsorship is not authority sponsorship.** An input may sponsor an
output's liveness without licensing its practical authority; `authority_support`
is a separate relation, required to be contained in `standing_support` (you
cannot be authorized by something that does not sponsor your liveness) and
required to be injective across authoritative outputs.

Two further distinctions are enforced by the record types rather than the
relations.  **Suspension continuation** is a burden route to a carrier that
still owes the answer; **suspension resolution** is a scoped termination with a
witness.  **A terminal disposition** ends an input dimension; **a positive
grant** licenses an output.  Neither substitutes for the other — §4.

## 2. The predicate

`check_transport_plan(cell, plan)` decides seven typed conditions and returns
finite counterwitnesses.  Writing `s(u)` for liveness in the order
`terminal < suspended < live`:

1. **sponsorship.** Every output with `s(v) > terminal` has some
   `u in standing_support(v)` with `s(u) >= s(v)`, or a scoped reinstatement
   (or, for a cell with no inputs, introduction) grant naming `v` with a
   nonempty evidential basis and authorization.
2. **authority.** Every authoritative output has some
   `u in authority_support(v)` with `authority(u)` and `s(u) >= s(v)`, or a
   scoped authority grant naming `v`.
3. **lineage.** `authority_support(v) subset standing_support(v)`; every
   declared endpoint is an actual input or output of the cell; an introduction
   grant appears only on a cell with no inputs.
4. **allocation.** The assignment of authoritative outputs to their authority
   sources is injective; one grant licenses at most one output; one output takes
   at most one licence of each kind.
5. **burden.** Every input with an unresolved burden reaches either a carrier
   output that still carries it, or a scoped termination naming *that input*,
   witnessed and authorized, whose kind can resolve a burden.  A carrier may not
   be stronger in liveness than the input, and may not be newly authoritative.
6. **separation.** Conditions 1, 2, and 5 are decided without reading
   `semantic_support`; a plan that offers only semantic edges where sponsorship
   is required is rejected with a distinct code.
7. **hygiene.** No idle assertion, no contradictory route, no unknown endpoint.

**Finite transport-plan decidability.** {#ST-J1}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** For a finite cell and a finite
declared plan, all seven conditions terminate and return finite typed
counterwitnesses.

**Proof.** Conditions 1–3 and 5–7 are finite quantifications over
`A_d x B_d` and over the declared record sets, with equality, membership, and
the three-element liveness order as the only tests.  Condition 4 is a bipartite
matching on a graph with at most `|B_d|` left vertices and `|A_d|` right
vertices, decided by exhaustive search over injections. `square`

Condition 5's carrier clause is `CM-N1` restricted to the pairs that still owe
an answer.  This is the whole of the weakening: where `CM-N1` quantifies over
`A_d x B_d`, the transport condition quantifies over the burden-carrying pairs
only, and requires a named sponsor everywhere else.

## 3. The canonical plan

A plan is a public declaration, so the predicate decides *the declared plan*.
For comparison with `CM-N1`, which needs no plan, one asks whether **any** plan
is accepted.  That question is decided by a single plan.

`canonical_plan(cell, grants, terminations)` declares total semantic support;
liveness support from every input at least as strong as the output; authority
support from every authoritative such input; a burden route to a carrier when
one exists, and otherwise to a supplied termination.  It attaches a supplied
record only where the cell cannot do without it, and it **never invents one**.

**Canonical maximality.** {#ST-J7}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** Over the enumeration scope of §7.2
and at each of the four record settings, if any plan in the declared family is
accepted then the canonical plan is accepted.  Hence satisfiability is decided
by one plan, and a rejection of the canonical plan is a rejection of every plan.

**Proof sketch, and the machine check.** Each condition is monotone in the
declared supports in the direction the canonical plan maximizes: adding a
sufficient sponsor can only satisfy conditions 1 and 2, and the canonical plan
declares every sufficient sponsor.  Conditions 4 and 7 cut the other way —
declaring *more* can duplicate an allocation or leave an assertion idle — and
the canonical plan declares no idle record and leaves allocation to the
matching, which is exact.  The remaining direction is condition 5, where the
carrier is chosen among outputs that satisfy the monotonicity clause, so a
carrier the canonical plan rejects is rejected under any declaration.  The
combination is verified exhaustively rather than argued: 576 cells at four
record settings, `0` failures, with `15,228` plans examined at the bare
setting where only `218` of the `576` cells are satisfiable at all. `square`

## 4. Pressure-testing the terminal-disposition exception

`CM-N1` excuses every lift at a cell that carries a terminal disposition.  Two
things are wrong with that.

**Scope.** `TerminalDisposition` names a `source_cell_id` and nothing finer.  A
retraction cell with two burdened inputs and one witness therefore discharges
both.  The transport type scopes a termination to one `input_id`, and a
cell-scoped record routed to two inputs yields two
`standing.termination_unscoped` counterwitnesses.

**Direction.** Terminating one input's burden is not a warrant for a different
output's liveness.

**A terminal disposition is not a grant.** {#ST-X3}
**Status: REFUTED (witness displayed).** Take inputs `S1` (suspended, unresolved
burden) and `S2` (suspended), and outputs `R` (suspended, still burdened) and
`M` (live, authoritative).  With a terminal disposition present at the cell,
`CM-N1` accepts the whole cell, `M` included.  The transport predicate answers
`S1`'s burden through the scoped termination and still rejects `M` with
`standing.semantic_support_is_not_sponsorship`: no input is live, so no input
sponsors a live output, and the plan offers no reinstatement basis.

The repair is the record separation of §1: a **reinstatement grant** is the only
thing that lifts liveness, and it needs a named evidential basis and
authorization scoped to the output.  Case F of §5 is precisely this: the same
cell fails with a termination alone and passes with a scoped basis.

## 5. The benchmark cases

Each is a cell together with the plan the case actually declares.

| case | cell | `CM-N1` | transport | code |
|---|---|---|---|---|
| **A** laundering merge | `{L live auth, S susp burden} -> {M live auth}` | reject | **reject** | `burden_vanished` |
| **B** provenance-separated merge | `{L, S} -> {M live auth, S' susp burden}` | **reject** | **accept** | — |
| **C** residual-free merge | as A, no residual, no response | reject | **reject** | `burden_vanished` |
| **D** authority-duplicating split | `{L} -> {M1 live auth, M2 live auth}` | **accept** | **reject** | `authority_duplicated` |
| **E** downward reconciliation | `{L, S} -> {M susp burden}` | accept | accept | — |
| **F** reinstatement | `{S susp burden} -> {M live auth}` | reject | reject bare, **accept** with a scoped basis | `semantic_support_is_not_sponsorship` |
| **G** mixed semantic/deontic | `{L auth, E live} -> {M live auth}`, liveness from `E`, authority by grant | **reject** | **accept** | — |

Four of the seven separate the conditions.  **B** and **G** are accepted by the
transport predicate and rejected by `CM-N1`: these are the merges that are safe
because provenance is declared.  **D** is accepted by `CM-N1` and rejected by
the transport predicate: `CM-N1` has nothing to say about allocation.  **F**
distinguishes a termination from a grant.

In **A**, the accepted-then-rejected diagnosis is the finding of §0: the sole
counterwitness is `standing.burden_vanished`, and `verdict.burden_outcomes`
records `in:S -> vanished`.  `CM-N1` also rejects A, but for the status lift —
the wrong reason, as **C** shows by failing identically while **B**, with the
same inputs and the same lift, is safe.

## 6. What the one-step certificate would have to carry

The plan is deliberately outside `MigrationCertificate`.  Were it to be adopted,
the minimum additional information is:

**Proposed one-step interface revision.** {#ST-C1}
**Status: PROPOSED (interface revision).** A one-step certificate that decided
transport locally would have to add:

1. **A per-occurrence unresolved-burden bit.** This is the one datum a single
   step genuinely lacks.  At `C_{12}` alone, an inherited suspended occurrence
   is only a status; that its burden remains, and that a route still owes an
   answer, is recorded in `C_{01}`'s suspension entry.  Equivalently: suspension
   entries belong to the *state*, not only to the certificate that created it.
2. **`scope_input_ids` on `TerminalDisposition`,** so a witness discharges the
   dimension it answers and no other (§4).
3. **The three typed support relations per cell,** since exactly one of them —
   semantic — is currently recoverable from `reconstruction_ref`, and the other
   two are not recoverable at all.
4. **Scoped grants** of kinds `introduction`, `reinstatement`, `authority`, and
   `authority-split`.  `AuthorizationRecord.authority_grants` already provides
   the fourth in `(cell, output)` form; the other three do not exist.
5. **A mixed-status many-to-many cell** — see `ST-X6`.

Items 1 and 2 are the load-bearing ones.  Items 3 and 4 are bookkeeping that
makes the check local rather than historical.

**Case B is inexpressible as one frozen cell.** {#ST-X6}
**Status: REFUTED (witness displayed).** The mode cardinality rules admit
`preserve` at `(1,1)`, `refine` at `(1,n)`, `merge` at `(m,1)`, the terminal
modes at `(m,0)`, `introduce` at `(0,n)`, and `suspend` only when **every**
output is suspended.  A `(2,2)` cell with one live and one suspended output
therefore has no legal mode: all eight are rejected, each on shape.

This is the expressive resource that is missing.  What is expressible — and what
the repaired history of `CM-E1` already does — is to keep the *occurrence*-level
cells separate while the merge happens at the semantic layer.  That is the
correct answer to the central question, but the cell partition then hides the
fact that the two cells participate in one semantic merger, and only the
transport plan records it.

## 7. The finite exhaustive experiment

### 7.1 What is enumerated

Every cell of shapes `(1,1)`, `(1,2)`, `(2,1)`, `(2,2)`, where each occurrence
ranges over `status x practical-authority x unresolved-burden`.  With three
statuses that is 12 configurations per occurrence and

\[
144+1728+1728+20736=24{,}336\ \text{cells},
\]

each decided at four record settings (grants on/off, terminations on/off), for
`97,344` plan checks.  The enumeration is deterministic, uses no sampling, and
reports its scope with its counts.

**The scope is the claim.** These are facts about cells of at most two inputs
and two outputs with three statuses and two Boolean bits, and about the declared
plan family of §3.  Nothing here is evidence of philosophical adequacy, and
nothing extends to larger cells without proof.

### 7.2 The realizable sub-scope

The frozen verifier forbids terminal occurrences as cell inputs or outputs
(`cell.terminal_input`, `cell.terminal_output`).  Restricting to
`{suspended, live}` gives the **realizable sub-scope** of

\[
64+512+512+4096=5{,}184\ \text{cells},
\]

and every comparison below is stated there.  On the full scope the minimal
disagreements all involve terminal endpoints and so are not reachable by any
valid certificate.

### 7.3 Results

**Exhaustive classification.** {#ST-E1}
**Status: PROVED+MACHINE-CHECKED.** On the realizable sub-scope: `CM-N1` accepts
`1,220` cells; the transport predicate with no records on offer accepts `1,831`;
they agree on `3,991`.  With grants and terminations both available every cell
is satisfiable.  On the full `24,336`-cell scope the four record settings accept
`4,055`, `9,732`, `8,004`, and `24,336` respectively.

**Soundness and exactness.** {#ST-J2}
**Status: PROVED+MACHINE-CHECKED.** On the realizable sub-scope, a cell is
accepted by the canonical plan **if and only if** none of the four independently
stated safety properties holds:

- liveness created without a sponsor,
- authority duplicated or transferred between branches,
- a burden disappeared,
- a suspension laundered.

Both directions are exhaustively checked: `0` unsound acceptances and `0`
rejections not witnessed by a safety property.  In particular the predicate
never accepts a laundered suspension — the no-liveness-laundering result.

The safety properties are stated directly from the facts and the plan, not by
re-running the predicate, so the coincidence is a check and not a tautology.  On
the full scope, soundness still holds (`0` unsound acceptances) while the
predicate is strictly stronger than the four properties on `1,156` cells, all of
them with terminal endpoints.

**No authority duplication.** {#ST-J3}
**Status: PROVED (single derivation).** If a plan satisfies conditions 2, 3, and
4, then the map from authoritative outputs to their licensing sources is
injective into (authoritative inputs at least as strong) union (scoped grants),
each grant licensing one output.  Hence the count of authoritative outputs never
exceeds the count of distinct licences, and no source licenses two branches.

**Proof.** Condition 4 asks exactly for an injection, decided by exhaustive
search over injections, and rejects when none exists; condition 2 makes its
domain the authoritative outputs and its codomain the eligible sources; the
per-grant and per-output multiplicity checks of condition 4 make the grant part
injective as well. `square`

This is strictly finer than the cell-level counting of `AM-X16`, which compares
cardinalities: a plan may satisfy the counting and still declare one source
twice, and `ST-J3` rejects that declaration.

**Burden conservation.** {#ST-J4}
**Status: PROVED (single derivation).** If a plan satisfies condition 5, then
every input carrying an unresolved burden has either a carrier output that still
carries it and is no stronger in liveness and no more authoritative, or a
witnessed authorized termination scoped to that input whose kind can resolve a
burden.  No burden is lost, and none is transferred to a stronger branch.

**Proof.** Condition 5 is a case analysis over the burden route of each burdened
input, with the empty route and the missing termination both rejected, the
carrier required to carry, and the monotonicity clause applied to the pair
`(input, carrier)`. `square`

**Comparison.** {#ST-J5}
**Status: PROVED+MACHINE-CHECKED.** On the realizable sub-scope:

\[
\textbf{CM-N1}\ \wedge\ \text{burden conservation}\ \wedge\ \text{authority allocation}
\ \Longrightarrow\ \textbf{ST}
\]

with `0` counterexamples, and the converse fails on `902` cells.  Hence `CM-N1`
is a **coarse sufficient special case** once conjoined with the two properties it
does not express, and the transport condition is strictly weaker than that
conjunction.  `CM-N1` alone is not sufficient: it accepts `291` cells the
transport predicate rejects, `330` counterwitnesses of them
`standing.burden_vanished` and `40` `standing.authority_duplicated`.

**Semantic support never decides.** {#ST-N1}
**Status: PROVED+MACHINE-CHECKED.** Over the realizable sub-scope, varying
`semantic_support` over all `2^{|A_d||B_d|}` well-formed subsets while holding
the rest of the plan fixed leaves the verdict unchanged: `5,184` cells,
`69,760` variants, `0` failures.

By inspection the predicate reads `semantic_support` in exactly two places, both
of which only select which counterwitness to report; well-formedness of the
declared edges is the sole way semantic content can affect a verdict, and that
is a hygiene condition, not sponsorship.

### 7.4 Minimal witnesses

**`CM-N1` accepts a vanishing burden.** {#ST-X1}
**Status: REFUTED (witness displayed).** The `(1,1)` cell
`{S suspended, burden} -> {S' suspended, no burden}`.  Status does not increase
and no authority appears, so `CM-N1` accepts.  The burden is simply gone; the
transport predicate returns `standing.burden_vanished`.  This is minimal: one
input, one output.

**`CM-N1` accepts an authority duplication.** {#ST-X2}
**Status: REFUTED (witness displayed).** Case D.  Pairwise, neither output is
stronger than the input and both inherit authority from an authoritative input,
so `CM-N1` accepts.  One source licenses two branches.  (`AM-X16`'s counting
catches this instance; `CM-N1` alone does not, and the counting in turn misses
the declared-duplication instance of `ST-J3`.)

**Semantic support does not sponsor.** {#ST-X4}
**Status: REFUTED (witness displayed).** `{S suspended} -> {M live, auth}` with
total semantic support and nothing else: rejected with both
`standing.semantic_support_is_not_sponsorship` and
`..._is_not_authority`.  Re-declaring the same edge as liveness and authority
support does not help — the input is too weak — which is the point: sponsorship
is a fact about liveness, not about content.

**A cell-scoped termination discharges every input.** {#ST-X5}
**Status: REFUTED (witness displayed).** A terminal cell with two burdened
inputs and one witness satisfies `cell.unbacked_retraction` in the frozen
verifier.  Scoping yields two `standing.termination_unscoped` counterwitnesses.

**Minimal transport-accepted, `CM-N1`-rejected witness.** The `(2,1)` cell
`{u0 suspended, u1 suspended authoritative} -> {v suspended authoritative}`:
`CM-N1` rejects because `u0` is not authoritative; the transport predicate
accepts because `u1` sponsors, injectively, and no burden is at stake.

## 8. Compositionality

**Two-step compositionality.** {#ST-J6}
**Status: PROVED+MACHINE-CHECKED.** Running the transport predicate over every
cell of both certificates of the two-step history of `CM-E1`, with the
unresolved-burden bit read from the *previous* certificate's suspension entries:
the three composing repairs (`suspended-lineage`, `merged-suspension`,
`authorized-loss`) are accepted at every cell, and `merged-live` is rejected at
exactly one cell, `step:12/d12:e-merge`.

The transport condition therefore accepts exactly the histories `verify_history`
accepts on this family, and rejects the laundering history — but the
counterwitness is `standing.burden_vanished` on `e:frustration-suspended`, not a
complaint about the status lift.  The split-then-merge history keeps two lineage
paths into one output while the merge cell's authority assignment stays empty
and its liveness sponsors number two: path multiplicity is not duplicated
sponsorship, which is `CM-J3` at the deontic layer.

The composition claim is exactly this finite instance.  Nothing here shows that
per-cell transport acceptance implies composite acceptance in general; that is
the open item of §9.

## 9. What remains open

- **Whether condition 5's monotonicity clause is itself weakest.** It is
  restricted to burden-carrying pairs, which is a large weakening of `CM-N1`,
  but no argument shows a still weaker provenance rule cannot block `ST-X1` and
  case A.
- **Local-to-global.** `ST-J6` is one finite history.  Whether per-cell
  transport acceptance composes along normalized ancestry for arbitrary
  histories — the analogue of `CM-J5` with `CM-N1` replaced by the transport
  condition — is not proved.  Revising `CM-J5` to use the weaker condition is
  **not** done here, because the proof of `CM-J5` uses `CM-N1`'s universal form
  in the induction and does not obviously go through.
- **Larger cells.** Every enumerated result stops at two inputs and two outputs.
  Condition 4's matching and condition 5's case analysis are stated for
  arbitrary finite cells, but only the small shapes are checked.
- **The interface revision `ST-C1`.** Whether adding the per-occurrence burden
  bit breaks any existing `AM-` or `CM-` claim has not been checked; it is
  proposed, not adopted.
- **Legacy carriers.** Condition 5 admits a `legacy` termination kind with a
  retained carrier, but no benchmark exercises it against `LegacyRetention`.
- Everything already open in `OPEN_PROBLEMS.md`, unchanged.

## 10. Philosophical reading

The result is a separation of two things ordinary usage runs together.

To identify two concepts is to say that a distinction does no work *for the
purpose at hand*.  It is not to say that the reasons which stood behind each,
the liveness they conferred, the authority they licensed, or the challenges
still outstanding against them, may be pooled.  Those are answers owed to
someone, and an ontology change is not an answer.

`CM-N1` enforces this by refusing to let anything get stronger.  That is safe and
too blunt: it forbids the ordinary case in which two concepts merge and the
merged concept inherits its liveness from the branch that had liveness, while
the challenged branch keeps its challenge.  What the finer analysis shows is
that the thing to protect is not the strength of the output but the
**continuity of the answer owed**.  A system may merge whatever it likes, as
long as every unanswered question survives the merge attached to something, and
no branch acquires liveness it was not sponsored for.

Semantic identification buys no entitlement.  Shared ancestry buys no authority.
And a response to one question is not a licence for a different claim.
