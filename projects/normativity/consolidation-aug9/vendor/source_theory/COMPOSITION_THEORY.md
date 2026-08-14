# Composition of accountable ontology migrations

## 0. Verdict and authority

The authoritative inputs are this project's `MIGRATION_THEORY.md` (claims `AM-J0`
through `AM-X17`) and `JOINT_THEORY.md` (`NL-J0` through `NL-X18`).  Nothing in
those documents is altered, weakened, or re-proved here.  The one-step verifier
`verify_migration` in `src/migration.py` is used as a frozen base layer; this
phase adds a version/history layer around it in `src/composition.py` and gives
its claims the distinct `CM-` namespace.

**Lead verdict: positive, with one strictly stronger invariant required.**
Two accountable migrations compose in the displayed finite example, but not
because both components verify.  The pair

- (v_0 -> v_1) the certified harm refinement of `AM-E1`, and
- (v_1 -> v_2) a locally certified merge of coercion and preference frustration

can be assembled so that **both component certificates pass all nine one-step
checks and the composite is still inadmissible**.  The exhibited obstruction is
not semantic and not monetary.  It is that a *merge* may join a suspended branch
to a live one, and cell-level authority counting — the invariant `AM-J0` and
`AM-X16` actually enforce — conserves the authority total while permitting the
liveness of the suspended branch to be laundered into the live output.

The correction is a monotonicity condition on liveness, stated as `CM-N1` below.
It is local (it can be checked on a single cell), but the reason it is needed is
visible only from composition, because at the second step alone the inherited
suspension is an unexplained status and its unresolved burden lives in the
*previous* certificate.

Nothing here makes `v_1` a permanent ontology.  §8 gives the retention criterion
under which most of `v_1` becomes collectable, and the exact finite trace in
which it does.

## 1. Versioned migration history

A **versioned migration history** for a single actor is a finite linear diagram

\[
v_0\xrightarrow{C_{01}}v_1\xrightarrow{C_{12}}\dots\xrightarrow{C_{n-1,n}}v_n
\]

together with, for each index,

- a **version identity** `(version_id, ontology_id, sequence_index, actor_id,
  parent_version_id)`;
- for an intermediate version, an **arrival state** (the state the incoming
  certificate produced) and a **departure state** (the state the outgoing
  certificate consumes); and
- an **administrative grant** relating the two.

The actor index is carried but not quantified over: every construction and test
in this phase is the singleton-actor, linear-history case.  Branching, several
simultaneously active actors, strategic filing, and equilibrium are outside this
phase and are deliberately not foreclosed by the representation: the identity
record already carries `actor_id` and `parent_version_id`, and steps are typed
edges rather than a global sequence variable.

### 1.1 Administrative grants

The **only** difference permitted between the arrival and departure states of an
intermediate version is an administrative grant: added authorization
identifiers, added consuming migration tokens, and (if the grant declares one) a
retaken freeze snapshot.  Every other field of the state — semantic carrier,
claim and payoff tables, occurrences, evidence roots, relation edges,
challenges, positions, compiler, force holdings, routes, accounts, remaining
consuming potential, and noninterference — must be byte-equal.

This is not bookkeeping.  A second migration needs prior external authorization
and a fresh consuming token, and by `AM-X8` neither can be manufactured by the
migration that wants them.  Making the grant the *only* legal intermediate edit
is what stops a history from smuggling an uncertified state change into the gap
between two certified ones.

**Administrative continuity.** {#CM-J0}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** Let `s^-` and `s^+` be the arrival
and departure states of an intermediate version and `g` its grant.  If every
field of `s^+` other than `authorization_ids`, `migration_tokens`, and a
grant-declared `snapshot_id` equals the corresponding field of `s^-`, if no
authorization or token is dropped, and if every added identifier appears in `g`,
then the history contains no state change that is not either certified by a
migration or recorded as a grant.

**Proof.** The state record is a finite product of comparable fields.  The
hypothesis is a field-by-field equality test on that product with three named
exceptions, each of which is checked against the grant's declared additions.
Any change outside the exceptions is exhibited by the field name that differs;
any change inside them is exhibited by the added or dropped identifier. `square`

### 1.2 Activation chain

The two certificates must also link as public events.  Writing `A_{01}` and
`A_{12}` for the activation records of the two migrations, the history requires

\[
A_{01}.\text{final active state}=s^+_1.\text{state id},\qquad
A_{12}.\text{preactivation active state}=s^-_1.\text{state id},
\]

the second certificate's bound old snapshot to equal `s^+_1`'s snapshot, and the
two consuming tokens to be distinct.  Together with `AM-J3`'s per-step
compare-and-swap identities this makes the history one chain of atomic public
events rather than two unrelated ones.

## 2. Composable local spans

Let the two comparison arenas be

\[
\mathcal O_0\xleftarrow{\pi^-_{01}}\Gamma_{01}\xrightarrow{\pi^+_{01}}\mathcal O_1,
\qquad
\mathcal O_1\xleftarrow{\pi^-_{12}}\Gamma_{12}\xrightarrow{\pi^+_{12}}\mathcal O_2 .
\]

Their candidate composite is the finite fiber product of `AM-J4`,

\[
\Gamma_{02}=\{(g,h)\in\Gamma_{01}\times\Gamma_{12}:\pi^+_{01}(g)=\pi^-_{12}(h)\},
\]

with `pi^-_{02}(g,h)=pi^-_{01}(g)`, `pi^+_{02}(g,h)=pi^+_{12}(h)`, and the
intermediate projection `mu(g,h)=pi^+_{01}(g)=pi^-_{12}(h)`.  The declared
covered support of `Gamma_02` is the set of pairs both of whose components are
covered.

The fiber product always exists.  It is not always adequate.

**Fiber-product live-support criterion.** {#CM-J2}
**Status: PROVED (single derivation).** `Gamma_02` carries every live semantic
and payoff distinction of the composite if and only if

\[
\pi^+_{01}\bigl(\operatorname{supp}\Gamma_{01}\bigr)\subseteq
\pi^-_{12}\bigl(\operatorname{supp}\Gamma_{12}\bigr),
\]

and every outstanding nonzero-holdings payoff table of `O_0` is defined on
`pi^-_{02}(\operatorname{supp}\Gamma_{02})`.

**Proof.** ( <= ) Every covered `g` has some covered `h` with
`pi^+_{01}(g)=pi^-_{12}(h)`, so `(g,h)` is a covered pair of `Gamma_02` whose
start projection is `pi^-_{01}(g)`; hence every covered start evaluation is
realized and pullback along `pi^-_{02}` is defined wherever it was defined on
`Gamma_01`.  ( => ) If some covered `g` has `pi^+_{01}(g)=omega` with `omega`
outside `pi^-_{12}(\operatorname{supp}\Gamma_{12})`, then no covered pair of
`Gamma_02` projects to `omega`, so any two start states separated only at
`pi^-_{01}(g)` are identified on the composite carrier, and the discrepancy of
`AM-J4` cannot be stated there. `square`

The second clause is not implied by the first: a step may keep every
intermediate state and still lose a start payoff whose table was only ever
declared on an uncovered subset.  The verifier reports the two failures with
distinct codes (`composition.fiber_support_gap`,
`composition.payoff_support_gap`).

The criterion is sharp in the following operational sense.  Truncating
`Gamma_12` to `{none, physical, coercion}` leaves the second certificate
**locally valid** — the two remaining reconstructions are exact or disposed of,
the payoff pullback is `(0,1,1)`, and both reference lifts stay in the carrier —
while the composite loses the frustration column entirely.  This is `CM-X3`.

## 3. Composite lineage, and why paths are not ancestry

Let `D_{01}` and `D_{12}` be the disposition cells of the two certificates.  A
**composite lineage path** is a tuple

\[
(u_0,\;u_1,\;u_2,\;d_{01},\;d_{12})
\]

with `u_0 in A_{d_{01}}`, `u_1 in B_{d_{01}} cap A_{d_{12}}`, `u_2 in B_{d_{12}}`.
The **normalized composite ancestry** is the image relation

\[
\mathrm{Anc}=\{(u_0,u_2):\exists u_1\ \text{a path exists}\}\subseteq U_0\times U_2 .
\]

**Lineage normalization.** {#CM-J3}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** Under `AM-J0` at both steps, for
every `(u_0,u_2)` the set of intermediates witnessing it is a nonempty subset of
`B_{d_{01}}` for the unique cell `d_{01}` consuming `u_0`, the relation
`Anc` is well defined and independent of any path enumeration order, and
`|paths| >= |Anc|` with equality exactly when no start/end pair has two
intermediates.

**Proof.** By `AM-J0` each live `u_0` is consumed by exactly one cell and each
live `u_2` is produced by exactly one cell, so the first and last components of
a path are determined by their cells; the intermediates witnessing `(u_0,u_2)`
are those elements of `B_{d_{01}}` whose consuming cell produces `u_2`.  `Anc`
is defined as an image of a finite relation and so is order-independent.  The
inequality is the statement that the fibers of the path set over `Anc` are
nonempty. `square`

A split followed by a merge produces `|paths| > |Anc|`.  In the exact trace of
§5 under the conservative merge repair there are **8 paths and 7 ancestry
pairs**, the surplus being `e:harm -> e:merged-suspended++` witnessed by both
`e:physical-or-coercion` and `e:frustration-suspended`.

The distinction matters because two derived quantities are computed over
lineage: practical authority and residue keys.  If either were computed over
paths rather than over `Anc`, the split-then-merge history would double an
authority or a loss that was only ever granted once.  The composition report
therefore computes authority from occurrence records and residue from
certificate entries, and uses paths only to *report* multiplicity — never as a
multiplicity to be summed.

## 4. What composition must check that one step cannot

The composition verifier derives thirteen results, each returning typed finite
counterwitnesses:

1. **components** — both migrations re-verified by `verify_migration`;
2. **continuity** — snapshot, grant confinement (`CM-J0`), activation chain,
   token distinctness, actor agreement;
3. **fiber** — construction of `Gamma_02` and its three projections;
4. **coverage** — the live-support criterion `CM-J2`;
5. **lineage** — normalized end-to-end ancestry; no unanchored descendant and no
   silently lost start occurrence;
6. **duplication** — duplicate intermediate paths, unreconciled merges, and
   cross-step repetition of a loss or literal-obligation key;
7. **edges** — composite justification, warrant, challenge-target, scope,
   incompatibility, and provenance images;
8. **targets** — the composite descendant frontier of every frozen start
   challenge target, checked for both omission and dilation;
9. **authority** — start/intermediate/end authoritative occurrences, recorded
   grants, and liveness lifts;
10. **residue** — inherited suspensions, losses, and legacy dependencies;
11. **movement** — composite payoff meaning on `Gamma_02` and the exact
    reference-movement ledger;
12. **retention** — intermediate records that must remain public;
13. **collection** — intermediate records eligible for discard.

**Finite composition verifier.** {#CM-J1}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** For finite rational input, all
thirteen checks terminate and return finite typed counterwitnesses on failure.

**Proof.** Each check is a finite operation on the same class of objects as
`AM-J1`: field comparison, finite product formation, image computation on finite
relations, set difference on typed target sets, counting over finite index sets,
and exact rational sums.  No check performs unbounded search. `square`

Six of the thirteen can fail while **both** components pass.  Composition is
therefore not a corollary of component validity:

| composite failure | why one step cannot see it |
|---|---|
| fiber lacks required support | each arena is adequate for its own span |
| lineage normalization is ambiguous | each cell partition is separately valid |
| a challenge target loses a descendant end to end | the frontier is recomputed against a *later* frontier |
| an intermediate distinction is still normatively live | liveness is a property of the *next* state |
| authority or liveness is duplicated | the previous certificate holds the suspension |
| activation identities do not link | each activation is internally consistent |

## 5. The exact positive trace

### 5.1 The two spans

`v_0` has the binary carrier `{no-harm, harm}`, one commitment, one entitlement
with two evidence roots, one warrant, one live challenge `c:frustration`
targeting the ancestry edge `edge:f-support`, its burden, and one outstanding
position `p:harm` with holdings `H = -2`.

`C_{01}` is the certified refinement of `AM-E1`, unchanged: `Omega_1 = {none,
physical, coercion, frustration}`, the entitlement splits into a live
physical-or-coercion branch and a **suspended** preference-frustration branch,
the warrant splits likewise, and the challenge and burden transport.  The
frustration entitlement and warrant remain suspended with their burdens
outstanding; the live `any-harm` position has holdings `-2`.

`C_{12}` merges: `Omega_2 = {none, bodily-harm, nonphysical-harm}` with
`physical |-> bodily-harm` and `coercion, frustration |-> nonphysical-harm`.
`Gamma_12 = Omega_1` with `pi^-_{12} = id`.

### 5.2 The fiber product

`pi^+_{01} = id` on `Gamma_01 = Omega_1` and `pi^-_{12} = id`, so

\[
\Gamma_{02}\cong\{n,p,c,f\},
\]

four covered pairs, with `pi^-_{02}` the coarsening to `{no-harm, harm}` and
`pi^+_{02}` the merge to `Omega_2`.  The criterion `CM-J2` holds.

### 5.3 Composite semantic accounting

Instantiating `AM-J4` on `Gamma_02`, the start claim `harm` reconstructs as
`or(physical-injury, coercion, preference-frustration)` at the first step and
each component reconstructs identically at the second, giving

\[
\delta_{02}(\mathrm{harm})=\delta_{01}+\delta_{12}=0 .
\]

**No `v_0` claim is lost.**  What the merge destroys is a distinction `v_1`
itself introduced:

\[
\delta_{12}(\mathrm{coercion})=(0,0,0,-1),\qquad
\delta_{12}(\mathrm{preference\text{-}frustration})=(0,0,-1,0)
\]

on `(n,p,c,f)`.  Each is keyed as a discrepancy and separately disposed of; by
`AM-X9` disclosure alone would not suffice.

The composite reconstruction is recomputed rather than asserted: pulling `harm`
back along `pi^-_{02}` gives `(0,1,1,1)`, the disjunction of the three `v_1`
claims along the intermediate projection gives `(0,1,1,1)`, and the disjunction
of their `v_2` images along `pi^+_{02}` gives `(0,1,1,1)`
(`tests/test_composition.py::test_start_claim_is_conserved_end_to_end`).

### 5.4 Exact movement

The outstanding position transports by coordinate as
`harm -> any-harm -> any-harm` with holdings `H = -2` unchanged at every step,
and the certified public references are

\[
q_0=\tfrac34,\qquad q_1=\tfrac23,\qquad q_2=\tfrac35 .
\]

By `AM-J2` applied at each step,

\[
\ell_{01}=\bigl[-H\,(q_0-q_1)\bigr]_+=2\cdot\tfrac1{12}=\tfrac16,\qquad
\ell_{12}=\bigl[-H\,(q_1-q_2)\bigr]_+=2\cdot\tfrac1{15}=\tfrac2{15},
\]

\[
\ell_{02}=\ell_{01}+\ell_{12}=\tfrac16+\tfrac2{15}=\tfrac3{10}.
\]

The other two transported coordinates (`protect -> protect` and
`physical-or-coercion -> bodily-harm`) carry holdings `0` and contribute `0`.
Every one of these rationals is recomputed by the verifier from the raw
compiler references, the raw force holdings, and the raw coordinate transports;
none is stored.

**Composite movement additivity.** {#CM-J4}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** If both steps satisfy the
hypotheses of `AM-J2` and the outstanding holdings vector transports unchanged,
the composite reference movement is the sum of the two step movements, and the
history consumes exactly two of the reference jumps budgeted by `NL-J2`.

**Proof.** `AM-J2` gives each step's movement as
`[-<H, q^- - q^+>]_+` on that step's live-payoff carrier.  Holdings transport by
occurrence identity and are checked equal at both steps, so the same `H` indexes
both charges; the ledger is the ordered pair of charges and its total is their
sum.  Each step consumes one predeclared consuming migration token and the two
tokens are distinct by `CM-J0`, so the history contributes two jumps. `square`

**This does not require a holdings norm.**  Each charge is the positive part of
a holdings-weighted reference difference; substituting into `NL-J2` with
`m_- + 2 + m_+` jumps, the minimum core coefficient over the three compilers,
the sum of the solver-error and ordinary-movement budgets, and the unchanged
cumulative risk guard yields one horizon-uniform cap by exactly the argument of
`AM-J3`, with `1` replaced by `2`.  No wealth or movement budget is reset at
either activation, and no bound on `|H|` is used.  In the trace,
`H = -2` is exact data, never a norm hypothesis.

Concretely, the three compilers share `theta = 1/10`; with inherited budgets
`bar epsilon = 1/100`, `R = 1/10`, and `M_ord = 1/5`, the recursion (6.1) of
`NL-J2` gives `U_0 = 1/5`, `U_1 = 31/10`, `U_2 = 321/10`, and the composite
`3/10` is admitted at two jumps.  The hypothesis actually discharged at each
step is that both reference lifts lie in the live-payoff carrier — which the
one-step verifier checks and reports — and not any bound on the holdings vector.
Both facts are recomputed in
`tests/test_composition.py::test_composite_movement_enters_the_joint_cap_without_a_holdings_norm`.

**Exact two-step harm history.** {#CM-E1}
**Status: PROVED+MACHINE-CHECKED.** The displayed history verifies: both
components pass all nine one-step checks, all thirteen composition checks pass,
the derived movements are `1/6` and `2/15` with total `3/10`, the fiber product
has four covered pairs, and the composite frontier of `c:frustration` is the
single ancestry edge `edge:f-support++`.

Verification: `tests/test_composition.py`.

## 6. The naive-collapse counterexample

The naive composite takes `Omega_2` at face value: merge the two nonphysical
grounds, merge the entitlements into one live authoritative entitlement, and
declare the composite lossless because every `v_0` claim still reconstructs
exactly (which, by §5.3, it does).

**Naive lossless collapse.** {#CM-X2}
**Status: REFUTED (witness displayed).** The second certificate fails
`semantic.lossless_collapse` on both `reconstruct:coercion` and
`reconstruct:frustration` with the exact unrecorded discrepancies
`(0,0,0,-1)` and `(0,0,-1,0)`.

This is `AM-N1` at the second step, and it is the easy failure.  The instructive
one is the next section.

## 7. The repaired composites, compared

Four repairs make the second span **locally valid**.  All four pass all nine
one-step checks.  They differ in what carries the residue and in what the
composite then preserves.

| repair | residual object | composite | live frontier of `c:frustration` | end authoritative occurrences |
|---|---|---|---|---|
| **R-A** authorized terminal disposition | witnessed discharge/retraction plus four relation losses | passes | empty (answered) | 4 |
| **R-B** suspended lineage component | suspended entitlement, warrant, and a distinct ancestry edge | passes | `edge:f-support++` | 4 |
| **R-C** merge with downward reconciliation | one suspended merged entitlement | passes | `edge:f-support++` | 3 |
| **R-D** merge with upward reconciliation | authorized semantic loss only | **fails** | `edge:f-support++` | 4 |

**R-B is the strongest.**  It is the only repair that simultaneously (i) keeps a
live challenge whose target is specific to the frustration ancestry and distinct
from the coercion ancestry, and (ii) leaves the operative coercion liveness
intact.  R-C buys the same target discrimination by suspending the merged
entitlement, losing one live authoritative occurrence.  R-A resolves rather than
preserves: it requires a real response witness, which the given history does not
contain, and is admissible only if one is produced; it is displayed here because
it is the case in which the residue becomes collectable (§8).

R-D is the result.

### 7.1 The obstruction: liveness laundering across a merge

**Component validity does not imply composite validity.** {#CM-X1}
**Status: REFUTED (witness displayed).** In R-D the merge cell

\[
d:\ \{\underbrace{e{:}\text{physical-or-coercion}}_{\text{live, authoritative}},\
\underbrace{e{:}\text{frustration-suspended}}_{\text{suspended, nonoperative}}\}
\ \longrightarrow\ \{\underbrace{e{:}\text{merged}}_{\text{live, authoritative}}\}
\]

satisfies every one-step check.  Cell conservation (`AM-J0`) holds: two inputs
consumed once each, one output produced once.  Authority conservation
(`AM-X16`) holds: one authoritative input, one authoritative output, so the
count does not increase and no grant is required.  The semantic discrepancies
are keyed and disposed of by an authorized loss.  The challenge transports to a
frustration-specific ancestry edge and its frontier matches exactly.

Yet the suspended entitlement — suspended by `C_{01}` with `burdens_remain`
true and a live answerability route — has been re-admitted as a live
authoritative liveness without any response, discharge, retraction, or new
grant.  The suspension has been laundered through a merge.

The composite verifier reports three independent counterwitnesses:
`composition.standing_not_monotone` (the cell), `composition.suspension_resurrected`
(the inherited suspension entry), and
`composition.unreconciled_duplicate_path` (the split-then-merge pair whose
branches carried unequal liveness).

This is minimal: **one** cell, **two** inputs, **one** output.

### 7.2 The revised invariant

Order statuses by `terminal < suspended < live`.

**Liveness monotonicity.** {#CM-N1}
**Status: PROVED (single derivation).** Require of every disposition cell `d`,
every input `u in A_d`, and every output `v in B_d`:

\[
\mathrm{status}(v)\preceq\mathrm{status}(u),
\qquad
\mathrm{authority}(v)\Rightarrow\mathrm{authority}(u),
\]

**unless** the certificate carries a terminal disposition sourced at `d`, or an
authorization grant naming the pair `(d,v)`.  Then no history satisfying the
one-step checks at every step admits a lineage branch along which liveness or
practical authority strictly increases without a public record, and R-D is
excluded.

**Proof.** The condition is a finite check on the pairs of each cell.  If it
holds at every cell, then along any composite lineage path the status sequence
is nonincreasing and the authority predicate is nonincreasing, except at cells
carrying a disposition or a grant, which are exactly the public records that
`AM-J3` conclusions 1 and 9 require to exist.  R-D's merge cell has an input of
status `suspended` and an output of status `live` with neither record, so it
violates the condition; conversely R-A satisfies it through its terminal
dispositions, and R-B and R-C satisfy it outright. `square`

**Later refinement.** `STANDING_TRANSPORT.md` re-analyses this condition and
shows it is *coarse* rather than correct-as-stated: `CM-N1` is both too strong
(it rejects a merge whose live input alone sponsors the merged liveness while
the suspended input's burden continues on a residual — `902` such cells) and too
weak (it accepts a cell that simply drops an unresolved burden, and a split that
licenses two authoritative outputs from one source — `291` such cells).  The
finding there is that the laundering in `CM-X1` is a *burden-disappearance*
failure, not a liveness-lift failure.  `CM-N1` remains established and
sufficient for the histories in this document; it is not weakened, and `CM-J5`
below still uses it.

Two observations, both load-bearing for how this should be read.

First, **the condition is local.**  It could have been a tenth one-step check.
It was not, and the reason is instructive: at the second step in isolation,
`e:frustration-suspended` is merely an occurrence carrying the status
`suspended`, with no visible obligation attached.  The obligation —
`burdens_remain` and a live route — is recorded in the *first* certificate's
suspension entry.  Composition is what forces the question "why was this
suspended, and has that reason been answered?" to be asked at all.

Second, **cell-level counting is genuinely insufficient.**  `AM-J0` conserves
occurrences and `AM-X16` conserves authority totals.  Both hold in R-D.  What
neither expresses is that authority may not be *transferred* from a branch that
does not hold it into an output, which is exactly what a merge with mixed
liveness does.  Conservation of a total is not conservation of provenance.

## 8. Retention and collection

An intermediate record is either **retention-required** or
**collection-eligible**.  Disclosure records — authorized suspensions, losses,
legacy retentions, terminal dispositions, and authorization records — are never
collectable; they are the residue, and discarding them would discard the account
of what happened.  The question is about intermediate *structure*: the
occurrences, edges, and comparison arenas of `v_1`.

**Retention criterion.** {#CM-C1}
**Status: CONJECTURE (not proved).** An intermediate structural record `r` at
`v_1` must remain public if and only if at least one holds:

- (a) a live or suspended `v_2` occurrence's justification or provenance
  ancestry passes through `r`;
- (b) a live `v_2` challenge or burden has a typed target whose descendant chain
  passes through `r`;
- (c) an outstanding nonzero-holdings position's composite payoff meaning or
  reference lift is indexed by an arena column requiring `r`;
- (d) a retained disclosure record states values indexed by `r`.

Otherwise `r` is collection-eligible.

The finite construction establishes the *sufficiency* direction operationally —
the verifier computes (a)–(d) and no displayed history has ever needed a record
it declared collectable — and establishes the *necessity* direction only on the
displayed instances.  It is a conjecture because "must remain public" quantifies
over future migrations, and by `AM-X10` a local record does not determine its
own future extensions.  A record collectable against every migration this
history contains may be required by one it does not.

What the finite trace does establish exactly, and this is the sharp part:

- Under **R-B**, no intermediate occurrence is collectable.  The live challenge
  `c:frustration+`, its burden, the suspended entitlement, and the suspended
  warrant all have live `v_2` descendants; every `v_1` occurrence is retained by
  clause (a) or (b).  An unresolved intermediate distinction prevents
  collection.
- Under **R-A**, exactly the four frustration-lineage occurrences
  `c:frustration+`, `b:justify-frustration+`, `e:frustration-suspended`, and
  `w:frustration-suspended` become collectable, each with the recorded reason
  that its lineage ended in a witnessed terminal disposition.  Every suspended
  `v_1` occurrence is collected.
- Under **both**, the two comparison arenas remain retained, by clause (c): the
  position `p:any-harm++` still carries holdings `-2`, and its composite payoff
  meaning and reference lift are indexed by the arena support.  **Answering a
  challenge does not settle a contract.**

So `v_1` is not a permanent foundational ontology; it degrades to whatever
unresolved positions, challenges, burdens, provenance, and authorization records
still require, and the verifier names each retained record together with the
dependent that requires it.

## 9. The proposed general theorem

**Local-span composition.** {#CM-J5}
**Status: PROVED-CONDITIONAL (conditions listed).** Let
`v_0 -> v_1 -> ... -> v_n` be a versioned migration history in which

1. every step passes the nine checks of `AM-J3`;
2. every intermediate version satisfies administrative continuity `CM-J0` and
   the activation chain of §1.2, with pairwise distinct consuming tokens;
3. every consecutive arena pair satisfies the live-support criterion `CM-J2`;
4. every cell satisfies liveness monotonicity `CM-N1`;
5. every frozen challenge target's composite descendant frontier is covered
   exactly — no omission and no dilation — at every prefix; and
6. every outstanding nonzero-holdings position transports by coordinate at every
   step with unchanged holdings, each step satisfying `AM-J2`.

Then the composite is an accountable migration in the sense of `AM-J3`: the
composite ancestry `Anc` is well defined and duplication-free, every live start
occurrence has a live composite descendant or a recorded terminal outcome, no
practical authority or liveness is created, every start challenge has a covered
composite frontier or a witnessed disposition, the composite payoff meaning is
exact on `Gamma_{0n}`, and the total reference movement is the sum of the step
movements, entering `NL-J2` as `n` jumps.

**Status of this statement.** For `n = 2` the conclusions are established for
the displayed finite history by direct computation (`CM-E1`) and the individual
implications by `CM-J0`–`CM-J4` and `CM-N1`.  For general `n` the argument is a
straightforward induction on the prefix — the fiber product is associative up to
the evident isomorphism and `Anc` composes as a relation — but three points are
**not** discharged here:

- hypothesis 5 quantifies over *every prefix*, and it has not been shown that
  checking consecutive pairs suffices to imply it;
- hypothesis 3 is stated pairwise; whether pairwise adequacy implies adequacy of
  the `n`-fold fiber product is exactly open problem 13 below;
- the endpoint `NL-J3` recertification is assumed at each step rather than
  derived from a composite condition.

It is therefore labelled conditional, and the general form is listed as open.

## 10. Hypothesis audit

What the finite construction actually establishes, separated from what it
merely illustrates.

**Established by computation on raw data.**

- Two accountable migrations *can* compose: `CM-E1` exhibits a history in which
  both components and all thirteen composite checks pass, with exact rationals.
- Component validity does **not** imply composite validity: `CM-X1` exhibits a
  pair passing all eighteen one-step checks whose composite fails on three
  independent counts.  This is the load-bearing negative result.
- Liveness monotonicity `CM-N1` is *sufficient* to exclude the exhibited
  obstruction, and *necessary* in the sense that dropping it readmits `CM-X1`.
  It is **not** shown to be the weakest such condition.
- The live-support criterion `CM-J2` is both directions proved, and its failure
  is realized by a locally valid certificate (`CM-X3`).
- Movement additivity and the two-jump accounting are exact; the composite total
  `3/10` is recomputed from raw compiler references and holdings.
- Lineage paths and normalized ancestry are genuinely distinct: `8` versus `7`
  in the split-then-merge history.

**Illustrated but not established.**

- That `CM-C1` is the correct retention criterion.  Only the sufficiency
  computation and two instances are exhibited.
- That the four repairs of §7 exhaust the coherent options.  They exhaust the
  options *expressible in the frozen one-step certificate types*, which is a
  weaker claim.
- That R-B is optimal.  It is strongest among the four on the two stated axes
  (live target discrimination, retained operative liveness); no optimality over
  all repairs is claimed.
- That `CM-J5` holds for `n > 2`.

**Assumed throughout, not proved.**

- The singleton-actor linear history.  Nothing here addresses concurrent
  proposals, conflicting grants, or merge of divergent version branches.
- External authorization.  Grants are checked for confinement and binding, never
  justified.  By `AM-X8` and `NL-X4` this is deliberate.
- Finiteness and rational tables, inherited from `AM-J1`.
- The endpoint `NL-J3` conditions at each version, inherited from `AM-J3`
  hypothesis 5 and not manufactured by composition.

**Explicitly not claimed.** That `v_2` is a better ontology than `v_1`, that the
history converges, that merging coercion with preference frustration is
substantively correct, or that any of this selects a true ontology.  The
theorem is about accountability of a revision, not its correctness.

## 11. Required failure witnesses

1. **Both components passing implies the composite passes.** `CM-X1`, stated and
   refuted in §7.1: three composite counterwitnesses on a pair with no component
   failure.

2. **A merge of two nonphysical grounds is lossless because every start claim
   survives.** {#CM-X2}
   **Status: REFUTED (witness displayed).** §6; start claims do survive, and two
   intermediate distinctions are still destroyed.

3. **A locally adequate arena is adequate in composition.** {#CM-X3}
   **Status: REFUTED (witness displayed).** Truncating `Gamma_12` to three
   states keeps the second certificate locally valid and drops the frustration
   column from `Gamma_02`; the composite reports
   `composition.fiber_support_gap` on `frustration`.

4. **Self-consistent activation records chain.** {#CM-X4}
   **Status: REFUTED (witness displayed).** Relabelling the intermediate state
   identity and updating the second certificate to match keeps both components
   valid; the composite reports `composition.activation_chain_broken` in both
   directions and `composition.unauthorized_intermediate_edit` on `state_id`.

5. **One consuming migration token may authorize a second migration.** {#CM-X5}
   **Status: REFUTED (witness displayed).** Reusing `token:migration-1` leaves
   both components valid — each checks only its own token — and the composite
   reports `composition.token_reuse`.

6. **A stored expected output can make an invalid certificate pass.** {#CM-X6}
   **Status: REFUTED (witness displayed).** Overwriting the stored discrepancy
   values with zeros does not silence the reconstruction; the recomputed delta
   still fails `semantic.lossless_collapse`.  Declaring the composite total to
   be `1/6` produces `composition.declared_movement_mismatch` against the
   derived `3/10`.

7. **A transported challenge may follow one descendant of a split target.**
   {#CM-X7}
   **Status: REFUTED (witness displayed).** Splitting `edge:f-support+` into two
   images while the successor challenge covers one yields
   `composition.frontier_uncovered` naming `edge:f-support-b++`.

8. **A state may be edited between two certified migrations.** {#CM-X8}
   **Status: REFUTED (witness displayed).** Changing `protect` force holdings on
   the departure state is reported as
   `composition.unauthorized_intermediate_edit` naming the field, independently
   of whether the second certificate happens to notice.

## 12. Relationship to normative version control

The history answers the eight questions a version-control layer must answer, and
answers each from derived data rather than stored metadata.

| question | derived from |
|---|---|
| What changed between versions? | per-step semantic, claim, cell-mode, and edge deltas |
| Which old occurrence is responsible for a current one? | normalized ancestry `Anc` (`CM-J3`) |
| Which challenges and burdens remain unresolved? | retained intermediate occurrences with live dependents |
| Why was each transition authorized? | per-step authorization binding and the grant record |
| What authority survived, disappeared, or stayed suspended? | the authority ledger and the liveness-lift list |
| Which distinctions still have live dependents? | retained records with their named dependents |
| Why can or cannot an intermediate arena be discarded? | `CM-C1` clauses, with the reason recorded per record |
| What is the end-to-end movement ledger? | per-step charges, components, and total (`CM-J4`) |

Two features distinguish this from ordinary version control, and they are the
reason the analogy should not be pushed.  First, a commit here cannot be
rewritten: outstanding contracts and unanswered challenges make the previous
version partially load-bearing, and the retention criterion says exactly which
part.  Second, merge is not symmetric: `CM-N1` makes merging a suspended branch
into a live one inadmissible without a public disposition, so the operation that
version control treats as recoverable is precisely the one that requires an
answer here.

The representation carries `actor_id` and `parent_version_id` on every version
so that branching and multi-actor histories are expressible later.  They are not
implemented, and no claim about them is made.

## 13. What remains unproved

- The general `n`-step theorem `CM-J5`, in particular whether pairwise
  live-support adequacy implies `n`-fold adequacy, and whether consecutive-pair
  frontier coverage implies prefix coverage.
- Whether `CM-N1` is the weakest sufficient liveness condition.  Partly settled:
  `STANDING_TRANSPORT.md` gives a provenance-sensitive condition that is
  incomparable with `CM-N1` and strictly weaker than `CM-N1` conjoined with the
  burden and allocation properties it does not express (`ST-J5`).  Whether that
  condition is itself weakest, and whether `CM-J5` survives substituting it, are
  both still open — the induction below uses `CM-N1`'s universal form.
- The retention criterion `CM-C1`, whose necessity direction quantifies over
  future migrations and is blocked by `AM-X10`.
- Whether the fiber product is the right composite arena at all when the two
  arenas are not both surjective onto the intermediate ontology.  It is adequate
  here because `CM-J2` holds; a lax or weighted comparison object might be
  adequate in cases where the strict fiber product is not.
- Any statement about branching histories, several actors, conflicting grants,
  or the incentive to file a challenge.
- Mechanization.  No claim in this document is Lean-checked.  `CM-E1` is
  machine-checked in the sense of `AM-E1`: a finite Python instance, exact
  rationals, no stored success assertion.

## 14. The composite migration `M_02`

Sections 1–13 decide whether a *pair* of certificates is jointly admissible.
They never build the one-step object

\[
M_{02}:V_0\longrightarrow V_2 .
\]

This section does, and the result is a two-sided negative: **certified
composability and composite certification are incomparable.** Neither implies
the other, so composability cannot be defined as "the composite verifier
accepts" — which is why §14.1 states it as invariants instead.

### 14.1 Certified composability, defined

Two certified migrations are **composable** when three groups of conditions
hold.  The groups are stated separately because they fail separately.

**(L) Local, on each migration alone.** `M_{01}` and `M_{12}` each pass the nine
checks of `AM-J3`.

**(S) Shared-version compatibility, at `V_1`.** Administrative continuity
`CM-J0`; the activation chain of §1.2 with distinct consuming tokens; the
live-support criterion `CM-J2` on the two arenas; normalized lineage `CM-J3`;
and inherited-residue conservation — every occurrence suspended by `M_{01}`
with a remaining burden is consumed by `M_{12}` into a suspended descendant or a
witnessed terminal disposition.

**(E) Endpoint, on the composite.** There is a `M_{02}` such that: its cells are
the connected components of the lineage graph; its arena is the fiber product
`Gamma_02` with its covered support; its relational, node, and coordinate
transports are the composites of the two steps'; every disposition record of
either step is re-sourced onto the component that owns it; and
`verify_migration(V_0, V_2, M_02)` passes.

Composability is (L) **and** (S) **and** (E).  Dropping any group admits a
history the other two accept.

### 14.2 The three candidates

**A — naive endpoint translation.** Build `M_{02}` from the endpoint semantic
correspondence `Omega_0 <- Omega_2` only.  Semantic correspondence determines no
relational transport, so every start relation edge is orphaned and the frozen
challenge target has no declared image.  The verifier returns
`relation.orphaned_edge` on all eight start edges and
`challenge.unknown_edge_target` on `c:frustration`.  **The violated invariants
are ancestry and challenge transport, not semantics**: the endpoint claim tables
agree exactly.

**B — blind composition.** Compose the two certificate records pairwise, one
composite cell per `(d_{01}, d_{12})`.  A split whose branches later merge then
consumes its common ancestor once per branch.

**C — repaired accountable composition.** Compose lineage by connected
component, retain the fiber-product arena with its legacy distinctions, and
re-source every disposition record.  For the `suspended-lineage` history this
composite is accepted by the frozen verifier with movement `3/10`.

### 14.3 Lineage collision

**Blind composition duplicates shared ancestry.** {#CM-X9}
**Status: REFUTED (witness displayed).** In candidate B the start entitlement
`e:harm` is consumed by two composite cells, one per intermediate branch, and
the verifier returns `occurrence.duplicate_input`.  The obstruction certificate
names the original occurrence `e:harm`, the intermediate paths
`e:physical-or-coercion` and `e:frustration-suspended`, the merged descendant
`e:bodily-or-coercive++`, and the resource at risk, the **consuming
disposition** — which is simultaneously the occurrence's single authority and
its single answer.  The same collision appears on `w:harm-protect`.

The repair is `CM-J3`: compose over normalized ancestry, not over paths.  The
connected component is the coarsest unit that counts common ancestry once.

**Positive composition.** {#CM-J6}
**Status: PROVED+MACHINE-CHECKED.** If (L), (S), and the component construction
apply, and no component has both several start occurrences and several end
occurrences, and no component carries a terminal disposition on one branch while
another branch survives, then the component composite `M_02` is a well-formed
certificate accepted by `verify_migration`, its cells consume each live start
occurrence exactly once, and its analytic movement is the composite reference
charge of `CM-J4`.

**Proof.** Components partition the active occurrences of all three versions, so
each live start occurrence lies in exactly one component and is an input of
exactly one composite cell; likewise each live end occurrence is an output of
exactly one.  Cardinality determines a legal mode in every case except
many-to-many, excluded by hypothesis.  Transport composition is image
composition of finite relations, so a start edge's composite image is nonempty
whenever both steps' images are.  The arena is the fiber product, adequate by
`CM-J2`.  Payoff transport composes because each step's pullback is exact.  The
machine check is the `suspended-lineage` and `merged-suspension` histories. `square`

**Uniqueness.** The composite is **not unique**.  The legitimate degrees of
freedom are exactly: the choice of representative for each fiber-product state
identified by both projections; the retention or collection of a legacy
distinction that satisfies `CM-J9`; and the choice among equivalent re-sourcings
of a disposition record onto its component.  It **is** canonical up to these:
the component partition is the unique coarsest lineage-respecting one, so the
cell structure is forced.

### 14.4 The obstruction theorem

**Composite certification is incomparable with composability.** {#CM-J7}
**Status: PROVED+MACHINE-CHECKED.** Both implications fail, each with a witness
in the displayed family.

- *A certified composite exists for an inadmissible history.*  In `merged-live`,
  `M_{01}` and `M_{12}` each pass all nine checks, and the component composite
  `M_{02}` also passes all nine.  Yet the history violates (S): the entitlement
  suspended at `V_1` with a remaining burden is merged into a live authoritative
  occurrence.  **The composite cannot object, because `V_0` has no suspended
  occurrence and `V_2` has none either** — the suspension exists only at the
  intermediate version, and a one-step certificate cannot see it.  The same
  happens in `naive`, where a *component* migration fails
  (`semantic.lossless_collapse` on two `V_1` claims) while the composite passes,
  because the collapsed distinctions were introduced at `V_1` and are not in
  `V_0`'s vocabulary.
- *An admissible history has no certified composite.*  In `authorized-loss`,
  (L) and (S) both hold, but the frustration branch is terminally retracted
  while the coercion branch survives.  The composite cell for that component has
  outputs, so it is not a terminal mode, and the verifier rejects its terminal
  disposition with `accounting.invalid_terminal_disposition`.  The obstruction
  certificate is `composite.branch_disposition_unexpressible`.

**Consequence.** Separate one-step certification is not sufficient for
composability — and neither is composite certification.  The additional
compatibility data forced by the first witness is precisely **(S)**: the
inherited-residue and liveness conditions, which quantify over the intermediate
version and are therefore invisible to any one-step certificate over `V_0` and
`V_2`.  The data forced by the second is an interface item: a per-branch
terminal disposition, `ST-C1` item 2.

### 14.5 No double authority

**No recombination duplicates inherited authority.** {#CM-J8}
**Status: PROVED (single derivation).** For every lineage component `K`, write
`A_i(K)` for the number of authority-bearing occurrences of version `i` in `K`
and `g_{t,t+1}(K)` for the scoped authority grants issued by step `t` naming an
output of `K` at version `t+1`.  Then

\[
A_j(K)\ \le\ A_i(K)+\sum_{t=i}^{j-1} g_{t,t+1}(K)
\qquad (i\le j).
\]

**Correction.** An earlier display of this claim pooled the grants into a single
`g(K)` and asserted `A_2 <= A_1 + g <= A_0 + g`.  Its second inequality asserts
`A_1 <= A_0`, which a legitimate grant issued at the *first* step falsifies, and
the implementation discarded every such grant by filtering against the endpoint
occurrence set.  Grants are step-specific; the accumulated form above is the
correct statement, established as `LG-J0` in `LOCAL_TO_GLOBAL.md` §1.  The
grant-free corollary — if no grant is issued in `[i,j]` then `A_j(K) <= A_i(K)` —
is the stronger statement the old display was reaching for and survives intact.

In particular **one inherited authority licence sponsors at most one endpoint
authority**, however many intermediate branches its lineage crossed; any further
authority-bearing endpoint occurrence requires its own distinct scoped grant.
The count of authority-bearing descendants is therefore bounded by the inherited
licences plus the grants, not by one.

**Proof.** Each step's cells partition `K`'s occurrences at the adjacent
versions (`AM-J0`), and `AM-X16` bounds each cell's authoritative outputs by its
authoritative inputs plus the grants bound to that cell.  Summing over the cells
of `K` gives the one-step bound `A_{t+1}(K) <= A_t(K) + g_{t,t+1}(K)`, and
telescoping it over `t` from `i` to `j-1` gives the accumulated bound. `square`

**What this does not say.** Descendants may be genuinely distinct occurrences
with common provenance.  In `suspended-lineage` the component of `e:harm` has
**two** end occurrences, `e:bodily-or-coercive++` and
`e:frustration-suspended++`; they are distinct entitlements with distinct
ancestry edges and distinct challenge exposure.  Exactly one bears authority.
The invariant is about authority-bearing descendants, never about descendants,
and collapsing the two would be its own error.

### 14.6 Legacy retention and discharge

The composite arena is the fiber product, so a distinction the endpoint ontology
drops survives as two arena states.  Here `coercion|coercion` and
`frustration|frustration` both project to `nonphysical-harm`: `Omega_2` has
three states and `Gamma_02` keeps four.  This is the retained legacy
distinction, and it is **local to the comparison arena** — no permanent
universal ontology is introduced, and `V_1` is not foundational.

**Legacy discharge.** {#CM-J9}
**Status: PROVED+MACHINE-CHECKED.** A retained group of arena states identified
by the endpoint projection may be collapsed exactly when

1. no live challenge or burden remains at `V_2`, and
2. every outstanding nonzero-holdings payoff pullback is constant on the group,
   and
3. every recorded discrepancy is constant on the group.

Under these conditions the reduced certificate is still accepted, and the
challenge frontiers, entitlement roots, payoff meaning, and analytic movement
are unchanged.

**Proof of the payoff clause, and a corollary.** Condition 2 is automatic for
any distinction *introduced after* `V_0`: both states of such a group have the
same image under the start projection, which factors through `Omega_0`, so every
start payoff pulled back along it is constant on the group.  Hence for
distinctions born at an intermediate version, discharge is blocked only by a
live dependent or a recorded discrepancy.  The remaining clauses are
`constant_on_fibers` on finite tables. `square`

This separates the three kinds of retained structure the question asks about:

- **normatively live legacy structure** — the two arena states while
  `c:frustration++` and `b:justify-frustration++` are live; not collectable;
- **merely historical provenance** — the loss records, terminal dispositions,
  and lineage; never collectable, and not part of the live arena;
- **safely dischargeable scaffolding** — the arena states once the challenge is
  answered.  Collapsing them takes `Gamma_02` from four states to three, and the
  composite still verifies with identical frontiers, roots, and movement.

So composition requires retaining the intermediate distinction **only while a
challenge depends on it**.  Afterwards `V_1` leaves no residue in the live
arena.

### 14.7 Composite reference movement

**Composite movement is subadditive.** {#CM-J10}
**Status: PROVED (single derivation).** For one payoff coordinate transported
across both steps with unchanged holdings `H`,

\[
\ell_{02}=\bigl[-H(q_0-q_2)\bigr]_+\ \le\ \ell_{01}+\ell_{12},
\]

with equality if and only if the two step charges are not of opposite adverse
sign.  In the displayed trace `q_0=3/4`, `q_1=2/3`, `q_2=3/5`, `H=-2` give
`1/6`, `2/15`, and `3/10`, so equality holds and the composite reproduces the
history's total exactly.

**Proof.** Write `a=-H(q_0-q_1)` and `b=-H(q_1-q_2)`; then `a+b=-H(q_0-q_2)` and
the claim is `[a+b]_+ <= [a]_+ + [b]_+`, the subadditivity of the positive part,
with equality iff `a,b` are not strictly opposite in sign. `square`

**The composite is not a substitute for the history.** {#CM-X10}
**Status: REFUTED (witness displayed).** Take `q_0=3/5`, `q_1=3/4`, `q_2=3/5`,
`H=-2`.  The steps charge `0` and `3/10`; the composite charges `0`.  The
composite therefore under-reports the movement the history incurred, and it
consumes one migration token where the history consumed two.  A composite may be
used to *summarize* a history but never to *account* for it: `NL-J2` must be fed
the history's jump count and per-step charges.

**The sufficient local carrier.** No global exposure norm is used anywhere
above.  What suffices is the live-payoff polytope on the fiber product,
`conv(W_{Gamma_02})`, containing both endpoint reference lifts.  In the trace
`W_{Gamma_02}={(0),(1),(1),(1)}` and the lifts are `3/4` and `3/5`; the holdings
`H=-2` enter as exact data and never as a bound.

### 14.8 What this section adds, and what it does not

Executable: composite cells, quotient-aware lineage components, relational
ancestry and challenge-frontier transport, payoff-carrier compatibility, arena
retention, structured obstruction certificates, discharge eligibility, and the
authority ledger.

Not claimed: that (L)+(S)+(E) is necessary as well as sufficient; that the
component composite is the only reasonable one; that any of this holds for more
than two steps.  `CM-J5` is unchanged and still uses `CM-N1`.
