# Accountable ontology migration

## 0. Verdict and authority

The authoritative input is this project's August 8 joint theory,
`JOINT_THEORY.md`, together with its ledger, exact witnesses, tests, and Lean
mechanisms.  Its inherited external authorities retain their canonical `C-...`
identifiers.  This phase cites the joint results as `NL-J1` through `NL-J4` and
does not alter them.

**Lead verdict: Positive.** A nontrivial one-step theorem holds for a finite,
conservative, proof-carrying ontology migration.  The decorated span proposal is
adequate after two corrections:

1. separate maps `T_K,...,T_P` are replaced by one typed collection of
   many-to-many **disposition cells**; and
2. semantic correspondence is supplemented by a typed audit of justificatory,
   challenge-target, inferential, and incompatibility edges.

“Exactly one successor per old item” is false under splitting.  The correct
conservation rule is exactly one consuming disposition **cell** per old live
occurrence, with cells allowed to have many inputs and many outputs.  A revision
trilemma proves that a new ontology cannot collapse a distinction separated by a
live payoff or deontic observable while also preserving it exactly and retaining
no legacy representation, suspension, or loss.

The theory remains relative to one supplied finite public interface.  It does not
select the true ontology or authorize a candidate generator.

## 1. Finite ontology states and deontic score

A finite ontology is represented by

\[
\mathcal O=(\Omega,C,\llbracket\cdot\rrbracket,U,A,\mathcal E_t).
\]

- `Omega` is a finite semantic state carrier.
- `C` is a finite typed claim vocabulary.  A claim has an executable rational or
  Boolean table on `Omega`.
- `U` is a finite set of occurrence-level live objects, sorted as commitments
  `K`, entitlements `E`, warrant occurrences `W`, challenges and repair burdens
  `B`, and outstanding payoff positions `P`.
- `A` is a finite typed edge set: justificatory ancestry, challenge targets,
  warrant premises and conclusions, incompatibilities, scope, and provenance.
- `\mathcal E_t` is the active endorsement book and its statuses.  The compiler, flow mechanism,
  accounts, and force state are the fields of `NL-J3`.

These sorts are not identified.  A commitment records responsibility; an
entitlement records current standing; a warrant is an inferential route; a burden
is an unresolved demand; a semantic claim is a table; a payoff is a contract;
and activation is a public event.  Equal claim tables do not imply equal
entitlement or ancestry (`C-PROV-IRR`).

The executable state gives each immutable occurrence ID one of three statuses:
**live**, **suspended**, or **terminal**.  Suspended objects remain live for
coverage and provenance but are nonoperative.  Live and suspended objects must
be migrated; terminal historical records remain in the append-only history and
are not copied as if newly live.

## 2. Local comparison arena

A comparison arena is a finite span

\[
\mathcal O_-\xleftarrow{\pi_-}\Gamma
\xrightarrow{\pi_+}\mathcal O_+.
\]

Here the arrows mean finite maps from comparison states to old and new semantic
states.  Pullback gives common tables

\[
f^-_\Gamma=f^-\circ\pi_-,\qquad
f^+_\Gamma=f^+\circ\pi_+.
\]

The arena need cover only the declared live semantic support, old claim
distinctions, outstanding payoff meanings, and reference witnesses used by this
migration.  It need not embed all possible ontologies or carry metaphysical
privilege.  Conservative refinement requires every relevant old claim and every
nonzero-holdings payoff to have an exact new representation on `Gamma`, unless
the old object is retained as an explicit legacy contract.  Mere equality on an
uncovered subset is not conservativity.

For the canonical refinement case one may take `Gamma=Omega_+`, `pi_+=id`, and
`pi_-` the finite coarsening map.  Full surjectivity of both projections is
sufficient but not minimal; the verifier instead checks coverage of the finite
declared live support and the reference lifts in section 6.

## 3. Minimal migration object

The retained object is

\[
M=(\Gamma,\pi_-,\pi_+,\mathcal D,\mathcal R,\Delta,\chi,a).
\]

### 3.1 Disposition cells

Each `d in D` is a typed decorated cell

\[
d=(A_d,B_d,m_d,\lambda_d),
\]

where `A_d subset U_-` and `B_d subset U_+` contain occurrences of one sort,
`m_d` is preserve, refine, merge, retract, discharge, suspend, loss, or introduce,
and `lambda_d` stores occurrence ancestry and a finite semantic reconstruction
witness where applicable.

The input cells satisfy

\[
\sum_{d\in\mathcal D}\mathbf 1[u\in A_d]=1
\quad(u\in U_-^{live}). \tag{3.1}
\]

The outputs declared live at activation satisfy the analogous equality.  Empty
input is allowed only for an introduction.  Empty output is allowed only for a
checked terminal disposition with a unique loss, retraction, or discharge
record; suspension instead produces a typed suspended occurrence with a live
route.  A split is one cell with one input and several outputs; a
merge is one cell with several inputs and one output.  Thus ancestry is shared
without duplicating the consumed old occurrence.

Cell conservation is not authority conservation.  If a cell has `r`
authority-bearing inputs, at most `r` outputs inherit practical authority.  Any
additional authority-bearing output requires a separately named authorization
grant bound to that cell and output.  In particular, a semantic split may share
ancestry while only one branch remains operative.  A terminal discharge also
requires an response/discharge witness; an authorization reference plus
inexpressibility is not such a witness.

**Occurrence-cell conservation.** {#AM-J0}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** If (3.1) and its output analogue hold,
every live old occurrence is consumed by exactly one disposition, every live new
occurrence has exactly one producing disposition, and splits and mergers retain
the complete input ancestry of their cell.

**Proof.** The two displayed coefficient equalities say precisely that the input
and output families are partitions.  Assign to each output the input block and
stored prior ancestry of its unique cell.  One-to-many and many-to-one cardinality
does not change uniqueness of cell membership. `square`

### 3.2 Relation audit

`\mathcal R` is not another sentence translator.  It is a finite set of edge dispositions
for:

- evidence and warrant ancestry of entitlements;
- challenge targets and the complete descendant frontier of a split target;
- warrant premise/conclusion and consequence edges;
- incompatibility edges;
- burden scopes, route paths, account assignments, and provenance.

Every live old edge is transported to finite new edges or receives an explicit
loss/suspension record.  Every new authority-bearing edge with no old source must
name a new public authorization and evidence path.  In particular, a preserved
claim table does not preserve entitlement unless the required ancestry graph is
transported or independently resupplied.

An edge image must also use descendants of its old endpoints; preserving only the
edge kind is insufficient.  For semantic nodes the certificate therefore gives
finite node-image relations.  If incompatible old nodes merge, their Cartesian
image includes a self-pair, which must remain visible as a self-conflict or receive
an authorized disposition.  This endpoint check makes the merge witness
operational rather than trusting a relabeled incompatibility edge.

Challenge targets are typed as occurrence, ancestry edge, warrant-premise edge,
warrant-consequence edge, or semantic component.  Their descendant frontier is
computed from the same certificate: an occurrence target maps to all outputs of
its unique consuming cell; an edge target maps to all declared images of that
edge transport; and a semantic-component target maps through the declared table
reconstruction.  The transported challenge targets must equal this frozen
frontier, unless an omitted target has a checked terminal disposition.  This
prevents both branch omission and retrospective target reassignment.

### 3.3 Discrepancy, endpoint, and authority

`Delta` is a typed keyed ledger.  It distinguishes:

- semantic claim discrepancy;
- lost or suspended inferential consequence;
- payoff discrepancy;
- retained legacy dependence.

It contains no literal currency and no analytic movement entry.  A nonzero
payoff discrepancy does not authorize substitution of a new contract: the old
contract must remain on a legacy carrier, be settled by its own rule, or be
suspended through an authorized contract disposition.

Three outcomes are distinct.  **Suspension** retains a live, nonoperative object,
its burden, and a route.  **Loss** is terminal failure of preservation and needs
both a disclosure naming the exact lost content and a separate authorization
whose allow-list contains that loss ID; hence loss disclosure is not loss
authorization.  **Legacy retention** keeps the old payoff object and settlement
rule on a retained carrier.  None is literal flow money or the analytic movement
scalar.

`chi` contains finite machine-checkable endpoint material: the new active book,
core-certified compiler witness, finite flow mechanism, remaining consuming
potential, eventual route coverage, account assignments, market/mechanism
noninterference, payoff reference lifts, and the data needed to reapply `NL-J3`.
Geometry in `chi` is feasibility, not authority.

`a` contains a prior authorization, the signed migration certificate hash, the
old snapshot ID, one consuming ontology-change token, and the eventual atomic
activation record.  A proposal generator may supply every other field and still
has no practical authority without `a`.

## 4. Operational finite verifier

Validity does not mean “everything good remains good.”  The verifier performs
the following finite checks.

1. Check unique IDs, occurrence sorts/statuses, input/output partition equations,
   legal cell modes/cardinalities, suspension status, and authority conservation.
2. Exhaustively compare old and new claim tables on the declared support in
   `Gamma`; check each refine/merge reconstruction table and key every discrepancy.
3. Run finite graph reachability for every active new entitlement.  Accept only a
   transported ancestry path or a newly authorized evidence root.
4. For each typed challenge target, compute its descendant frontier from cells,
   edge transports, and semantic reconstructions; verify exact target coverage.
   Burden scopes are transported as typed edges and separately require routes.
5. Transport every live warrant consequence and incompatibility edge, or require
   a uniquely keyed suspension/loss entry.  A merge of incompatible items must
   retain a self-conflict representation or record the loss.
6. Construct the nonzero-holdings position set, pulled-back payoff tables,
   `W_Gamma`, `conv(W_Gamma)`, reference lifts, holdings transport, new-coordinate
   zero padding, and analytic movement.  Require exact payoff equality or an
   authorized legacy settlement; a discrepancy entry alone fails.
7. Check separate suspension, loss, legacy, literal-liability, and movement types;
   loss and literal keys are unique, and every loss authorization is bound.
8. Derive old and endpoint compiler/core validity, route coverage, finite
   potential, account assignment, and `NL-J3` noninterference from raw data.
9. Check prior authorization, certificate/snapshot/token binding, token
   consumption, shadow identity, endpoint recheck, preactivation pointer, and the
   final compare-and-swap identities.

**Finite migration-verifier theorem.** {#AM-J1}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** For finite rational input, all nine
checks terminate and return finite counterwitnesses on failure.

**Proof.** Partition and key checks are finite counting.  Semantic, payoff,
refinement, and incompatibility checks enumerate finite tables.  Ancestry,
challenge, route, and eventual route coverage are finite graph reachability.  Compiler
and reference membership are rational polytope checks, and every remaining guard
is equality, membership, signature, or rational comparison. `square`

This verifier has operational content: it can reject a candidate without knowing
whether the new ontology is philosophically superior.  The implementation is
`verify_migration(old_state, proposed_state, certificate)` in
`src/migration.py`; it returns all nine results, derived carrier/coverage data,
and typed local counterwitnesses.  The canonical trace supplies no success
Booleans.

## 5. Exact migration protocol

The public order is:

1. **Proposal.** Publish `O_+` and candidate metadata.  The active pointer and
   force projection remain unchanged.
2. **Arena construction.** Publish `Gamma,pi_-,pi_+`, its live-support declaration,
   and rational tables.
3. **Transport declaration.** Publish disposition cells, edge dispositions,
   discrepancies, proposed legacy carriers, and endpoint data.
4. **Challenge and audit.** Admit migration challenges under the old active
   mechanism.  The verifier publishes either local failures or a complete report.
5. **Certification or failure.** Obtain independent authorization and reserve the
   consuming migration token.  A failed proposal stays nonoperative.
6. **Freeze.** Freeze the old active pointer, outstanding holdings, live status
   set, challenges, burdens, account assignments, and reference under one snapshot
   hash.  Due literal obligations are settled before the freeze.
7. **Shadow transport.** Construct the entire successor off to the side.  No
   active field is mutated.  Check the partition against the frozen snapshot.
8. **Ledger computation.** Compute semantic/consequence/payoff loss entries and
   the single analytic migration movement entry.  Literal liabilities, if any,
   remain separate typed entries.
9. **Endpoint recheck.** Recompile the exact shadow book, recheck the core,
   eventual route coverage, accounts, and reference lifts against the frozen holdings.
10. **Atomic activation.** One compare-and-swap event simultaneously appends all
    status/edge/loss/movement records and changes the active pointer.  On hash or
    certificate failure the shadow is discarded, a failure event is appended,
    and the old active pointer is unfrozen unchanged.

Proposal bypass is excluded at step 1.  Partial activation and duplicate
dispositions fail the partition at steps 7 and 9.  Burdens are assigned before
the freeze, not after observing migration outcomes.  Rollback never needs to
reverse an operative mutation because the sole mutation is step 10.

Steps 6–10 are one finite critical section inside a single public date.  No due
charge, settlement, filing admission, or service event interleaves with it; those
events occur before the freeze or after activation/failure under the appropriate
active mechanism.  Most shadow construction is completed before step 6, so the
freeze is a verification-and-swap boundary rather than an unbounded service
pause.

## 6. Weakest common payoff carrier and movement

Let `L` be the finite set of outstanding payoff occurrence IDs with nonzero
holdings. Exact payoff transport gives one comparison evaluation

\[
e_\ell:\Gamma\to\mathbb Q\quad(\ell\in L)
\]

because old and new payoff tables agree after pullback.  Put

\[
W_\Gamma=\{(e_\ell(\gamma))_{\ell\in L}:\gamma\in\Gamma\},
\qquad P_\Gamma=\operatorname{conv}(W_\Gamma).
\]

The migration certificate supplies reference lifts
`bar q^-,bar q^+ in P_Gamma` whose coordinates equal the old and new public
reference prices of those same payoff occurrences.  Old holdings transports by
occurrence ID to `bar H`.  New coordinates with no old position are zero before
activation, as in `C-CONS-EXT`.

This is weaker than a universal common ontology.  It is only the finite carrier
of contracts that are live across this boundary.  A bare semantic span does not
automatically supply reference lifts, because semantic maps alone do not choose
probability couplings or reference mixtures.

**Migration reference-jump theorem.** {#AM-J2}
**Status: PROVED (single derivation).** Assume exact transport of every nonzero
holdings payoff, the two reference lifts in `P_Gamma`, and the inherited prefix
payoff lower/upper caps on the old live payoff projection.  Then the migration
movement is

\[
\ell_M=[-\langle\bar H,\bar q^- -\bar q^+\rangle]_+,
\]

and `NL-J1` bounds its adverse and absolute sizes by the old prefix payoff range.
No holdings norm and no literal movement reserve are required.

**Proof.** Exact payoff transport identifies the outstanding-position coordinate
space on both sides.  Evaluation on every `gamma` is the old live payoff vector
at `pi_-(gamma)`, so old worldwise prefix bounds pull back to `W_Gamma` and by
convexity to `P_Gamma`.  Both lifted references lie in that polytope.  The payoff
difference identity of `NL-J1` now applies verbatim. `square`

If payoff transport is not exact, this proof is unavailable for the changed
coordinate.  Retaining the old payoff as a legacy coordinate restores a common
carrier; merely writing its discrepancy in `Delta` does not.

## 7. One-step accountable migration theorem

**One-step migration theorem.** {#AM-J3}
**Status: PROVED (single derivation).** Suppose:

1. the frozen pre-migration state satisfies `NL-J3` and its typed liability
   invariant;
2. `M` passes the hardened nine finite checks of section 4, including typed
   target-frontier equality, authority conservation across splits, separately
   authorized loss/legacy outcomes, and exact activation identities;
3. the migration is conservative for every relevant old claim and every
   nonzero-holdings payoff, except for objects explicitly retained on a legacy
   carrier or terminally suspended/lost;
4. every active entitlement output passes the ancestry check, every challenge
   covers its descendant frontier, and every incompatibility or warrant
   consequence is transported or uniquely disposed;
5. `chi` certifies a finite new mechanism satisfying the full hypotheses needed to
   reapply `NL-J3`, including eventual route coverage and a uniform positive core;
6. the migration consumes one predeclared book-change token, its reference lifts
   satisfy `AM-J2`, and the protocol of section 5 is followed.

Then the atomic transition produces a public state with:

1. no orphaned live commitments, entitlements, challenges, burdens, warrants, or
   positions;
2. occurrence-level lineage through every split and merger;
3. no active inherited entitlement without transported or newly authorized
   ancestry;
4. every old incompatibility and inferential consequence visible as a new edge,
   suspension, or unique discrepancy;
5. identity force projection before activation;
6. exact outstanding payoff meaning on the common carrier, or an explicit legacy
   contract disposition rather than silent substitution;
7. a core-certified active endpoint book;
8. terminal challenge coverage for the new finite mechanism;
9. separate, unique semantic-loss, literal-liability, and analytic-movement
   accounting; and
10. postactivation operative-force and answerability projections satisfying the
    hypotheses of `NL-J3`, with this migration counted as one reference jump.

**Proof.** `AM-J0` gives conclusions 1 and 2.  The finite ancestry reachability
check gives 3.  Edge-disposition coverage gives 4 and transports each challenge
to its full descendant frontier, giving 8 with the endpoint route certificate.
Until the atomic pointer swap, the old operative projection is unchanged by
construction, giving 5 (`C-ACTIVATION`).  Exact payoff table equality and the
legacy fallback give 6; `AM-J2` supplies the only permitted movement comparison.
The endpoint compiler check gives 7.  Key uniqueness and the product of semantic,
literal, and analytic ledger sorts give 9 by the same coordinate argument as
`NL-J4`.

The endpoint recheck supplies every local hypothesis of the new finite joint
mechanism rather than assuming its conclusions.  Market events still stutter in the
answerability projection, and the certified book/core/solver fields supply the
force projection.  The consuming migration token bounds ontology changes; the
migration reference move is one reference jump in `NL-J2`.  Therefore `NL-J3`
applies after activation, proving 10. `square`

For one uniform cap over the whole old/migration/new history, let `m_-` be the
remaining old reference jump allowance and `m_+` the certified new allowance.
Use `m_-+1+m_+` jumps, the minimum old/new core coefficient, the sum of old/new
solver-error and ordinary-movement budgets, and the unchanged cumulative risk
guard.  Zero-padding and exact-preimage scope on newly admitted coordinates give
the conservative extension required by `C-CONS-EXT`.  Substitution in `NL-J2`
then supplies one horizon-uniform cap; no wealth or movement budget is reset at
activation.

The theorem does not say that every old entitlement survives.  It says that its
survival, suspension, or loss is public, ancestry-sensitive, and complete.

## 8. Exact harm-refinement trace

Let

\[
\Gamma=\{n,p,c,f\}
\]

mean no harm, physical injury, coercion, and preference frustration.  The old
ontology has states `no-harm,harm`; `pi_-` maps `n` to no-harm and the other three
states to harm.  The new ontology uses `Gamma` itself.  Thus

\[
\mathbf 1_{harm}\circ\pi_-
=\mathbf 1_{p\lor c\lor f}\circ\pi_+.
\]

The old live occurrences are:

- commitment `k:harm` to the active bound `Pr(harm)>=1/2`;
- warrant `w:harm-protect`, and entitlement `e:harm` to use that warrant, with
  recorded testimony branches;
- challenge `c:frustration` and burden `b:justify-frustration`, undercutting the
  frustration branch of the entitlement/warrant;
- outstanding position `p:harm` with holdings `-2` and payoff the harm indicator;
- incompatibility `protect perp ignore`.

The disposition cells are:

| Cell | Input | Output | Mode |
|---|---|---|---|
| `d:k` | `k:harm` | `k:any-harm` | preserve |
| `d:e` | `e:harm` | active `e:physical-or-coercion`; suspended `e:frustration` | refine/split |
| `d:w` | `w:harm-protect` | active physical-or-coercion warrant; suspended frustration warrant | refine/split |
| `d:c` | old challenge | challenge on transported frustration-testimony ancestry edge | preserve |
| `d:b` | old burden | unchanged unresolved burden | preserve |
| `d:p` | old harm position | new any-harm position | exact preserve |

The old challenge targets the ancestry edge from frustration testimony to the
coarse entitlement—not the entire coarse entitlement.  Edge transport therefore
computes the singleton frontier containing the new frustration-support edge.
The physical/coercive entitlement descends from the distinct physical/coercive
testimony edge, so it is not a descendant of the challenged object.  The active
refined entitlement reaches the transported authorized root `root:pc+`; it is not
inferred from the coarse conclusion alone.  The suspended frustration
entitlement retains its testimony and challenge IDs.  The physical-or-coercion
warrant retains its old occurrence ancestry.  The nonoperative frustration
entitlement and warrant receive two typed suspension records, each naming its
producing cell and the still-live repair route.  No loss is declared.

The new semantic item `preference-frustration` exists in the proposal but has no
standalone commitment, entitlement, or force before activation.  Its only
action-guiding branch is suspended after activation pending the transported
challenge.  The incompatibility `protect perp ignore` is copied as an edge, not
inferred from equal words.

On `Gamma`, the old and new position payoffs are both `(0,1,1,1)`, so discrepancy
is zero.  Let

\[
q^-=3/4,\qquad q^+=2/3,\qquad \bar H=-2.
\]

Both references lie in the live-payoff polytope `[0,1]`, and

\[
\ell_M=[-(-2)(3/4-2/3)]_+=1/6.
\]

The position was entered at price `1/2`, so its prefix payoff is
`Phi(z)=1-2z`, with represented-world range `[-1,1]`.  At the two references,
`Phi(q^-)=-1/2` and `Phi(q^+)=-1/3`; their difference is exactly `1/6`, checking
the `AM-J2`/`NL-J1` jump identity without an holdings norm.

The old full force coordinates are `(harm,protect)`, with active endorsements

\[
h\ge1/2,\qquad a\ge h,
\]

so the old warrant really is operative.  Its full reference is
`(3/4,7/8)`.  The new force coordinates are `(any-harm,physical-or-coercive,
protect)`, with active endorsements

\[
h\ge1/2,\qquad a\ge r.
\]

The frustration branch is absent from the second endorsement because it is suspended.
The new full reference is `(2/3,1/2,3/4)`.  With uniform `theta=1/10`, the
verifier constructs the finite represented-world vertices, checks both
references by exact convex-hull membership, and evaluates every affine compiler
endorsement on every contracted vertex.  Affinity extends these checks to the represented
polytopes.  The old worlds are the binary `(h,a)` vertices.  The new worlds are
the four semantic states crossed with binary action and satisfy `r<=h`; the
check derives `h>=1/2` and `a>=r` on the contracted core.  Only the harm ticket
has old nonzero holdings; the genuinely new refinement coordinate is verified
to have zero holdings at activation.

There is no literal migration debit, loss, or legacy contract in this exact
trace.  Zero semantic/payoff discrepancy, two normative suspension records, and
analytic movement `1/6` remain different types.  Eventual route coverage for both the
live challenge and burden is derived from the authorized, assigned, consuming
route before atomic activation.

**Exact migration trace.** {#AM-E1}
**Status: PROVED+MACHINE-CHECKED.** The displayed finite instance—not `AM-J3`—is
accepted from raw states and a raw certificate by the Python verifier.  Exact
rational tests check all nine reports, graph reachability, the computed typed
challenge frontier, relation visibility, payoff carrier and lifts, holdings and
movement `1/6`, both compiler cores, computed eventual route coverage, authorization
binding, and atomic activation.  Sixteen one-field malformed variants return
typed counterwitnesses.  No Lean model of the migration transition is claimed.

## 9. Revision trilemma

Let `s:Gamma->Omega_+` be the new semantic projection, and let
`f:Gamma->V` be any live old observable: a payoff, a challenge-address predicate,
an incompatibility indicator, or another deontically relevant finite value.

**Finite revision trilemma.** {#AM-N1}
**Status: PROVED+MACHINE-CHECKED.** If there are `gamma_0,gamma_1` such that

\[
s(\gamma_0)=s(\gamma_1),\qquad f(\gamma_0)\ne f(\gamma_1), \tag{9.1}
\]

then no new-only function `f_+:Omega_+->V` exactly represents `f` on `Gamma`.
Consequently one cannot simultaneously have:

1. exact preservation of the live old observable;
2. complete elimination of the distinction between `gamma_0,gamma_1`; and
3. no residual legacy representation, suspension, or explicit loss.

**Proof.** If `f=f_+ circ s`, then (9.1) gives

\[
f(\gamma_0)=f_+(s(\gamma_0))=f_+(s(\gamma_1))=f(\gamma_1),
\]

a contradiction.  `lean/Migration.lean` mechanism-checks the general factorization
obstruction. `square`

The separation assumption is exact and minimal: if every live observable is
constant on each collapsed fiber, this particular obstruction disappears.
Other governance objections may remain, but the collapse is extensionally
lossless for the declared live interface.

## 10. Required failure witnesses

Each witness names the false claim, smallest countermodel, failed invariant, and
repair or impossibility verdict.

1. **Claim preservation preserves entitlement ancestry.** {#AM-X1}
   **Status: REFUTED (witness displayed).** One old claim `x` has entitlement
   occurrence `e` justified by evidence `t`.  The new claim has the same truth
   table and an active `e'` with no ancestry edge.  Semantic equality holds;
   entitlement fidelity fails.  Require the relation audit or new evidence.

2. **A challenge on a split target may follow one branch.** {#AM-X2}
   **Status: REFUTED (witness displayed).** Split `x` into `x_1,x_2`; transport the
   live challenge only to `x_1`.  `x_2` can exercise unchallenged force although
   it descends from the challenged occurrence.  Target the whole descendant
   frontier or explicitly discharge the omitted branch.

3. **Merging erases incompatibility.** {#AM-X3}
   **Status: REFUTED (witness displayed).** Old `a perp b`; merge both into `c`
   and record no `c perp c`, suspension, or loss.  The old conflict disappears.
   The edge audit must retain a self-conflict representation or block/record the
   lossy merge.

4. **A position may adopt the nearest new payoff.** {#AM-X4}
   **Status: REFUTED (witness displayed).** On two comparison states, the old
   payoff is `(0,1)` and the new payoff `(0,0)`.  One unit of holdings changes
   world-1 settlement by `1`.  Exact transport fails; retain the legacy contract,
   settle it, or use an authorized contract disposition.  A loss note alone is
   insufficient.

5. **A useful new distinction may constrain quotes during audit.** {#AM-X5}
   **Status: REFUTED (witness displayed).** Old region `[0,1]` gives sell-demand
   quote `0`; the proposed endorsement creates `[1/2,1]` and quote `1/2`.  Preactivation
   use changes practical force, exactly the bypass excluded by `NL-X1`.

6. **Refusal or inexpressibility discharges a burden.** {#AM-X6}
   **Status: REFUTED (witness displayed).** Delete target `x` from the new
   vocabulary and mark its challenge responded to without an response certificate.
   The old challenge occurrence has no consuming disposition.  Retain a legacy
   target, suspend it, or record an authorized terminal failure.

7. **Loss may be entered once per report section.** {#AM-X7}
   **Status: REFUTED (witness displayed).** Two entries with key
   `(loss:x,semantic)` count one lost distinction twice.  Unique typed keys reject
   the second; different literal and movement entries remain different risks.

8. **A semantic coupling warrants adoption.** {#AM-X8}
   **Status: REFUTED (witness displayed).** Two histories contain the identical
   span and tables; only one contains the prior authorization signature.  Their
   semantic records are equal and their activation predicates differ.  `a` is
   load-bearing; no geometric or latent fact creates it.

9. **A live collapsed distinction can migrate losslessly.** {#AM-X9}
   **Status: REFUTED (witness displayed).** Two old/comparison states map to one
   new state while a payoff takes values `0` and `1`.  `AM-N1` proves genuine
   impossibility unless one of the three trilemma demands is relaxed.

10. **One local arena determines a permanent universal comparison ontology.**
    {#AM-X10} **Status: REFUTED (witness displayed).** A singleton bridge from
    old `a` to current `b` is compatible with two future refinements `c_0` and
    `c_1`.  The local record is identical and cannot choose between them.  Retain
    the local bridge and require a new bridge later; universal privilege is not
    justified.

11. **Two cells may each refine the same old occurrence.** {#AM-X11}
    **Status: REFUTED (witness displayed).** Cells `d_1:{k}->{k_1}` and
    `d_2:{k}->{k_2}` consume `k` twice.  A genuine split is the single cell
    `{k}->{k_1,k_2}`.  Equation (3.1) rejects the duplicate.

12. **Statuses can activate before their challenges finish transport.** {#AM-X12}
    **Status: REFUTED (witness displayed).** Activate `k'` while old live challenge
    `c` has no successor.  The commitment partition passes locally but the full
    live-occurrence partition fails.  One atomic shadow transaction repairs it.

13. **A split burden may be assigned after observing which branch is costly.**
    {#AM-X13} **Status: REFUTED (witness displayed).** The same frozen prefix is
    sent to branch `x_1` after a loss and `x_2` after a gain.  Assignment is not a
    function of the public freeze record and can strategically unburden one
    branch.  Publish the descendant target set before freeze.

14. **Rollback can restore an early active-pointer mutation.** {#AM-X14}
    **Status: REFUTED (witness displayed).** Swap to the new book, then discover
    its compiler region is empty.  The public history already contains an
    uncertified operative interval; a later reverse event cannot make it never
    have occurred.  Shadow construction and one final compare-and-swap are
    necessary.

15. **Disclosing a loss authorizes it.** {#AM-X15}
    **Status: REFUTED (witness displayed).** A well-formed loss entry names the
    frustration consequence but its ID is absent from the prior authorization's
    loss allow-list.  Disclosure makes the failure visible; it does not confer
    authority to terminate the status.  The verifier returns the loss and
    authorization IDs.

16. **A split may copy practical authority with shared ancestry.** {#AM-X16}
    **Status: REFUTED (witness displayed).** One authority-bearing entitlement is
    refined into two authority-bearing descendants without a new grant.  Cell
    conservation preserves ancestry but changes one operative authorization into
    two.  Authority-output count plus cell-bound grants reject the duplication.

17. **A terminal-coverage assertion is a route certificate.** {#AM-X17}
    **Status: REFUTED (witness displayed).** Delete the only endpoint route while
    retaining the live challenge and burden.  No stored claim can make either
    occurrence terminally covered; finite route search returns the uncovered
    IDs.

## 11. Hypothesis audit

- Cell partition is necessary against duplicate dispositions and orphans
  (`AM-X2`, `AM-X6`, `AM-X11`, `AM-X12`).  The particular cell encoding is
  replaceable by any decidable finite hypergraph with the same coefficient-one
  invariant.
- The relation audit is load-bearing for entitlement, challenge, warrant, and
  incompatibility fidelity (`AM-X1` through `AM-X3`).  Claim-table equality cannot
  derive it.
- Exact payoff transport or a retained legacy carrier is load-bearing for live
  nonzero holdings (`AM-X4`, `AM-N1`).  Explicit discrepancy alone is not enough.
- The reference-lift condition is sufficient and close to minimal for applying
  `NL-J1`; whether still weaker couplings can support the same bound without a
  common live-payoff polytope is open.
- Prior authorization and atomic activation are load-bearing (`AM-X5`, `AM-X8`,
  `AM-X14`–`AM-X16`).  Compiler success is not adoption authority.
- Eventual route coverage and the endpoint core are inherited load-bearing conditions
  of `NL-J3`; migration does not manufacture them (`AM-X17`).
- A consuming ontology-change token is sufficient to retain the finite-jump
  theorem.  For one migration, an explicit `+1` jump cap would also suffice;
  repeated unbudgeted migration is outside scope.
- Conservative refinement is stronger than necessary for objects already
  terminally disposed or deliberately retained on a legacy carrier.  The exact
  weakest mixed semantic/deontic condition is open.
- Finiteness and rational tables make verification decidable.  Infinite language
  or endogenous candidate generation is not covered.

## 12. Compositional preview without a universal ontology

Suppose a later migration has local arenas

\[
\mathcal O_0\xleftarrow{}\Gamma_{01}\xrightarrow{}\mathcal O_1,
\qquad
\mathcal O_1\xleftarrow{}\Gamma_{12}\xrightarrow{}\mathcal O_2.
\]

Their candidate comparison is the finite fiber product

\[
\Gamma_{02}=\{(g,h):\pi^+_{01}(g)=\pi^-_{12}(h)\}.
\]

It carries composite occurrence lineage through the intermediate IDs.  Legacy
arenas referenced by unresolved burdens or unsettled positions must remain public;
irrelevant arenas need not become a universal substrate.  The next certificate
must state which intermediate claims, discrepancies, suspended burdens, payoff
maps, and authorizations it relies upon.

**Local discrepancy composition.** {#AM-J4}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** On the fiber product, if

\[
\delta_{01}=f_0-f_1,\qquad\delta_{12}=f_1-f_2,
\]

then the composite discrepancy is `delta_02=delta_01+delta_12` after pullback.

**Proof.** The two intermediate evaluations are equal by the defining fiber
product equation.  Add the two discrepancies and cancel `f_1`. `square`

This is only a preview.  The fiber product may fail to cover required live support,
and many-to-many lineage composition may need normalization to avoid duplicate
intermediate paths.  Those are checks for a future theorem, not assumptions that
all local spans automatically compose.

## 13. Generator and interpretation boundary

A future latent or Wentworth-style learner may output `O_+`, a candidate arena,
semantic tables, and proposed disposition cells.  Its output enters step 1.  It
cannot sign `a`, mark its own audit successful, create entitlement ancestry, spend
a migration token, activate a book, or settle a discrepant legacy payoff.

The philosophical gain is finite and procedural.  Deontic scorekeeping can
survive one conceptual refinement because responsibility, standing, reasons,
challenges, incompatibilities, and practical consequences are transported as
typed occurrences and edges rather than as bare sentences.  The theorem does not
show that the refined concepts are true, uniquely adequate, morally correct, or
eventually convergent.
