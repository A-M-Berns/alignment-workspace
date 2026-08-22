# Internal-answerability kernel prosecution

Status: **research memo; unregistered**. All new names are provisional. The
executable witnesses use finite sets and exact discrete objects. General positive
claims below are single derivations, not Lean statements or registered claims.

## Verdict

**Adopt after four repairs, and only as an internal answerability core.** The
small kernel is real:

1. an immutable undertaken certificate checked in the pre-transition reason
   state;
2. an input-scoped account DAG over reified liability identities;
3. per-input semantic transport by safety-language derivative;
4. edge-triggered review liabilities when an undertaken basis loses standing.

The proposal as stated is too weak at four points.

- Finite `deps(p)` is incompatible with a checker that scans an open-ended
  defeater universe. The certificate must depend on a versioned aggregate
  standing/defeat key, or on another finite key changed by every relevant new
  defeater.
- The multiset equation does not determine lineage. A rewrite needs an explicit
  input/output incidence relation, input-scoped closed branches, and a tag
  separating fresh output from inherited output.
- Joint transport over all inputs permits cross-parent compensation. Soundness
  must be checked for each consumed liability's account fragment.
- An existential current-time extraction `Now` need not preserve conjunction.
  Joint trace semantics must be composed before extraction unless current events
  are canonical or the constraints are saturated on extraction fibres.

The kernel establishes record-internal authorization and conservation. It does
not establish reason-guided control, environment-relative adequacy, inquiry
coverage, normative progress, counterfactual non-capture, future corrective
authority, or traderizability. Those boundaries are forced by existing workspace
counterexamples, not by a choice to keep the kernel small.

## 1. Repository orientation

The current structured state reports the legitimacy and learning interfaces as
unregistered research artifacts. The frozen consolidation is the only registered
legacy claim set. This pass tests the following live results.

| Existing object or result | What this pass uses |
|---|---|
| `consolidation-aug9/THEORY_8_DIACHRONIC_IDENTITY.md` | accountable disposition cells; split/merge lineage; standing and burden transport; local-to-global composition; append-only reopening |
| `THEORY_8_DIACHRONIC_IDENTITY.md` `LG-X1`, `LG-C1`, `AD-J5` | one merged burden bit loses multiplicity; borne burden lineages repair it; identification need not merge obligations |
| procedural-legitimacy `THEOREM_MAP.md` | provenance/no-amplification; pre-edit bearing; branching-safe DA forest; forest composition; six environment-relative counterexamples |
| procedural-legitimacy `src/forest.py` | branch-specific live, suspended and terminal leaves and proof substitution across segments |
| relational-scorekeeping `TWO_ARC_INTERFACE.md` | ordinary consequential burdens may be recomputed; explicit transport remains needed through vocabulary change; normative compilation is distinct from performance |
| relational-scorekeeping `ACTION_SEMANTICS.md` | an old vindication is not currently reopened when its premise is undercut; the same display would be refused prospectively |
| counterfactual-legitimacy `LEGITIMACY_INTERFACE.md` | `Licensed` must range over revisions; reason-guided non-capture is a factorization over coupled policy arms; coverage and access stay separate |
| crown-jewel `INTERFACES.md` and `COMPILER_SOUNDNESS.md` | `Due`, `Licensed`, performance, and compiler soundness are separate; reason-connection, scope and defeat remain substantive interfaces |
| `consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` | settlements are basis-free, incorrigible record events; no claw-back is load-bearing |
| traderized-enforcement `SEMANTIC_PROJECTION.md` | `C_t -> K_t` loses fibre information; a price region is not a semantics |
| `TRADERIZED_FORCE_INTERFACE.md` and projection-enforcement | force consumes a nonempty closed convex price region and a liability budget; it does not validate normative provenance or semantics |
| `PRIORITIES.md` item 39 | the normative-record-to-credal-set compiler remains open |

Two corrections to the starting picture follow immediately. First, DA is not
needed to carry every ordinary scorekeeping consequence: the critic can recompute
those from acknowledgments and its own practice. DA is needed for *reified owed
identities*, especially through split, merge and vocabulary change. Second,
settlement events are not historical normative moves with defeasible bases. They
carry no basis tag and are never reopened. A downstream normative use of a
settlement may be reviewed; the settled event itself may not be.

## 2. Smallest surviving state and transition system

At date `t`, use the state

```
S_t = (R_t, U_t, H_t, L_t, A_t, Q_t, B_t)
```

where:

- `R_t : DependencyId -> VersionedValue` is the current reason view;
- `U_t` is the immutable archive of certificates and historical check receipts;
- `H_t` is the append-only event/rewrite ledger;
- `L_t` is the finite multiset of live or suspended liability occurrences;
- `A_t` is the account DAG, including closed branches;
- `Q_t` is the joint current safety semantics extracted from accounts;
- `B_t` is the separate finite enforcement-liability account, when force is
  requested.

A normative event contains

```
e_t = (move, undertaken_certificate, rewrite_fragment,
       semantic_transport_witness, fresh_liabilities)
```

and is admitted only when the certificate checks against `R_t`, before any field
the move changes. The step first records the historical receipt, then applies the
move and account fragment, then audits old undertaken bases against `R_{t+1}` and
mints review liabilities for new validity-loss epochs. This ordering prevents a
move from installing the rule or bearing judgment that licenses itself and
prevents a newly minted review from recursively triggering in the same step.

`Q_t` and `B_t` are derived interfaces, not required components when no credal
force is requested. Relational consequences that are recomputable need not be
duplicated into `L_t`; once a demand is docketed as a reified obligation, its
identity is governed by the account calculus.

## 3. Reason representation

### 3.1 Interface

The minimum certificate interface is:

```
Judgment, Certificate, DependencyId, VersionedValue
concl : Certificate -> Judgment
deps  : Certificate -> FiniteSet DependencyId
check : ReasonView -> Certificate -> ValidityResult
```

`ValidityResult` should not be a Boolean in the durable interface. It is either a
valid receipt or an invalidity explanation naming at least one declared
dependency and its observed version. The following axioms are required.

**R1 — conclusion binding.** A move records `p` only if
`concl(p) = Licensed(pre_state, move)`; the transition identity and proposal are
part of the conclusion.

**R2 — pre-state check.** `check(R_t,p)` is valid before the move is applied.

**R3 — immutable receipt.** `CheckedAt(p,t,digest(R_t|deps(p)),valid)` is append
only. Current checking never overwrites it.

**R4 — dependency extensionality.** If `R|deps(p) = R'|deps(p)`, then
`check(R,p) = check(R',p)` including the explanation payload.

**R5 — explanatory failure.** If the result changes, the checker returns a
changed `d in deps(p)` and the old/current versions. R4 entails only that *some*
dependency changed. R5 makes that fact inspectable rather than requiring a
global diff.

**R6 — checker closure.** Every semantic input to checking is either fixed by a
trusted checker version or named in `deps(p)`. Changes to rule interpretation,
bearing, adequacy or proof-checking code therefore cannot be hidden outside the
dependency view.

**R7 — finite invalidation key.** Any open-ended negative premise such as “no
standing defeater exists” is represented by a stable aggregate key whose version
changes whenever a relevant defeater is added. A finite list of currently known
defeaters is insufficient.

The witness `fresh_defeater_breaks_locality` has a certificate depending only on
`warrant_stands`. Adding a fresh defeater changes the global checker while the
states agree on the declared dependency. R4 fails. Making the proof depend on
`defeat-index:w`, whose version changes on the addition, repairs the witness.

### 3.2 What must be a dependency

The distinction is semantic, not a fixed enumeration: a dependency is every
stable identity whose current value can affect `check`. In the current workspace
that includes, when read by the derivation:

- ground identities and derivation parents;
- warrant and rule-version identities;
- current standing/defeat-index keys;
- bearing entries and their rule versions;
- adequacy entries for a disposition certificate;
- provenance grants, scopes and consumed authority tokens;
- the licensed revision/proposal identity;
- the checker/rule-set version unless its semantics is fixed outside `R`.

Future defeaters remain compatible with finite proofs only through R7. Without
an aggregate key, the absence of an arbitrary future item is a global property
and finite locality is false.

### 3.3 `Supported`, proof search and multiple routes

No primitive global `Supported(phi)` is needed by this kernel. Define

```
Supported(R, phi) := exists p, concl(p) = phi and check(R,p).valid.
```

This is a semantic definition; it need not be decidable or searched by the
transition gate. The gate consumes a supplied certificate. Proof search,
IN/OUT labels, backtracking, consistency maintenance and multiple ATMS contexts
are implementation choices, not theorem hypotheses.

A certificate may itself contain alternative support branches. Its checker is
valid while one undertaken branch remains valid. If the process instead records
one route `p`, a different unrecorded `p'` does not make it false that its
undertaken basis was lost; `p'` is a ready way to discharge the resulting review.
This is the required distinction between available authorization and the basis
the process stood behind.

### 3.4 Authorization, undertaking and control

The three strengths do not collapse.

| Strength | Kernel role | Verdict |
|---|---|---|
| A. some current valid licence exists | admission | necessary but insufficient for historical review |
| B. the process records the certificate it undertakes | historical answerability | necessary for basis-loss reopening |
| C. action selection factors through represented reasons | authorship/non-capture | not supplied by A or B; separate hyperproperty |

`hidden_control_pair` gives the smallest separation of B from C: the same valid
recorded certificate appears in both runs, while one hidden bit changes the
action. Certificate validity does not show that the certificate controlled the
decision.

The weakest defensible C-clause is the counterfactual interface the workspace
already reached. For a named variation class `V`, exogenous history `E`, admitted
fine-grained reason trace `L`, and protected normative response trace `Z`:

```
for all a,b in V,
  Coupled_E(a,b) and L(a)=L(b) -> Z(a)=Z(b).
```

Equivalently, `Z` factors through `(E,L)` on `V`. The class must contain the null
policy and the reason trace must bind reasons to licensed revisions. This is a
hyperproperty of coupled runs, not a condition on one certificate or one record.
The internal answerability theorem needs A and B. A theorem using “reason-guided”
or “authored” needs C separately.

### 3.5 Provenance

Provenance belongs in certificate derivations, checked by the same gate, while
no-authority-amplification is proved compositionally about the derivation rules.
Primitive leaves carry conferred scope. Derived nodes may transform content but
their jurisdiction is bounded by a declared parent-combination rule. Grant and
authority-token identities are dependencies, so revocation can cause basis loss.

A separate top-level provenance status is unnecessary. Treating provenance as
an opaque Boolean inside `check` would lose the ancestry needed for the existing
no-amplification induction. Treating it as a wholly separate post-check would
permit a certificate to be valid while unauthorized. The small interface is one
checker over a proof-relevant derivation with a compositional scope invariant.
The union-versus-intersection parent rule remains an explicit modelling choice;
the current prosecution already shows they differ.

## 4. Liability resources and account proofs

### 4.1 Rewrite data

The equation

```
L_{t+1} = (L_t - P_t) multiset-union C_t multiset-union F_t
```

is necessary and not sufficient. A rewrite fragment must also contain:

```
tau = (P, C, F, incidence, closed, certificate)
incidence subset P x C
closed : P -> finite closed-branch witnesses
```

with these structural checks.

1. `P` is a submultiset of `L_t`; occurrence identifiers are unique at a date.
2. Every consumed input has an account fragment: at least one linked output or
   an input-scoped closed branch, possibly both for mixed decomposition.
3. Every `c in C` has an inherited input sponsor. Every `f in F` is explicitly
   fresh and has none.
4. A terminal witness is scoped to the obligation branch it closes.
5. Suspension records a route; resumption records its basis.
6. No event acts on a closed occurrence.
7. The rewrite certificate authenticates the identity/adequacy of the links;
   semantic inclusion alone does not.

The multiset equation alone has a 2-by-2 counterexample. `{a,b}` is consumed and
`{c,d}` produced under both `a->c,b->d` and `a->d,b->c`. The state equation is
identical and the ancestry differs. `same_equation_different_ancestry` computes
the witness.

### 4.2 Account DAG and forest representation

For each original obligation `ell`, its account proof at `t` is the unfolding of
the append-only rewrite DAG from `ell`. Open leaves are live or routed-suspended
occurrences. Closed leaves contain dated disposition witnesses. Status is derived:
an account is open exactly when it has an open leaf; terminal exactly when every
branch is closed; mixed status is represented without choosing one label.

A merge makes a DAG. If `a->c` and `b->c`, the same occurrence `c` is an open
leaf in the account of both ancestors. Per-ancestor unfolding may duplicate the
*display* of `c`, but retains its global occurrence identity. This is controlled
sharing of a carrier, not contraction of owed identities.

The resource that is linear is the owed account lineage, not evidence or physical
carriers. One response may cover two obligations when it carries two certified
adequacy edges and two disposition events. One merged carrier may bear two
lineages. Weakening is allowed only by an explicit closed branch; contraction of
lineages is not allowed. This exactly matches the consolidation's `LG-X1` repair
and `AD-J5`: a bit on the merged carrier is too small, while distinct obligation
accounts need not forbid a shared adequate response.

### 4.3 Representation result

**Rewrite/forest representation — false as proposed; true after repair.** The
multiset ledger plus an unstructured hyperedge does not determine the forest.
With incidence, branch status, input-scoped closure witnesses, unique occurrence
identities and fresh/inherited tags, unfolding the DAG at each root recovers the
existing DA forest. Conversely, quotienting equal occurrence identities across
all root forests produces the account DAG. The two constructions preserve root,
open/suspended leaves, closed witnesses and composition. They are inverse up to
the duplication of a shared merge node in per-root displays.

The proof is structural induction on ledger length. At a step, substitute the
fragment for each consumed open leaf and leave all other open and closed leaves
unchanged. This is the existing forest composition operation. The converse
identifies display nodes with the same global occurrence ID. The equation alone
cannot support the induction because it supplies no substitution site.

### 4.4 No Forgotten Liability

**Proposition (single derivation).** Suppose every rewrite satisfies checks 1–6
above and fresh occurrences never enter an old account without a later explicit
incidence edge. Then every historical obligation at every later finite date has
either an ancestry-linked live/suspended frontier or input-scoped closed branches
covering every branch. An unrelated fresh liability cannot count toward the
account without an explicit later rewrite.

**Proof.** At creation, the obligation is its own live frontier. A step not
consuming a frontier occurrence preserves it. A consuming step substitutes a
nonempty linked frontier and/or scoped closed branches by check 2. No other
operation removes a branch. Fresh output is excluded by check 3. Induction on
steps gives the result.

This is an accounting theorem, not semantic identity. `unrelated_stronger_impersonates`
shows that an unrelated stricter specification can satisfy refinement if falsely
declared a descendant. Check 7—the licensed identity/adequacy certificate—is
therefore independent and necessary.

## 5. Safety semantics and semantic transport

### 5.1 Canonical object

For a reified liability occurrence `ell` at its current history, let
`[[ell]] subset E^{<omega}` be the prefix-closed language of finite continuations
on which the liability has not been violated. Events include the public move and
the identity of any checked disposition certificate. Let

```
d_e Q = {x | e.x in Q}.
```

The derivative of a prefix-closed language is prefix closed (possibly empty), and

```
d_e(Q intersect R) = d_e Q intersect d_e R
d_v(d_u Q) = d_{uv} Q.
```

The first identity is exhaustively checked over every prefix-closed binary
language through horizon two. It is set algebra and needs no safety-specific
hypothesis; safety keeps the residuals in the same semantic class.

### 5.2 Correct local rule

For each consumed input `p`, let `Account_tau(p)` be the intersection of the
specifications of the outputs incident to `p`, together with the denotations of
its closed branch proofs. A valid closure proof denotes `top` after its event.
Require separately for every `p`:

```
Account_tau(p) subset d_move [[p]].
```

A pure `1->0` closure therefore requires `d_move[[p]] = top`. This is natural
only when `[[p]]` describes compliant disposition as well as direct performance.
An authorized-loss event can close an obligation because that event is an allowed
disposition in its specification; merely failing the substantive demand cannot.

The proposed joint rule is false as an account condition. Let, at one-event
horizon, `p_a` forbid `a`, `p_b` forbid `b`, `c_a=top`, and `c_b` forbid both.
Then

```
[[c_a]] intersect [[c_b]] subset [[p_a]] intersect [[p_b]]
```

while `c_a` does not refine `p_a`. One parent is an empty shell and the other
overcompensates. `joint_transport_laundering` is the exact 2-parent/2-child
witness.

### 5.3 Local-to-global semantic conservation

**Proposition (single derivation).** If every input-scoped rewrite is locally
sound, then at every later date each historical liability's current account
semantics refines the derivative of its original specification along the actual
event history.

**Proof.** Induct on steps. At a rewrite, replace each open child specification
in the prior account by its sound successor-account intersection. Monotonicity of
intersection and the local inclusion preserve refinement. Derivative distributes
over intersection, and temporal derivatives compose, giving the residual along
the concatenated history. Closed branches substitute `top` only when their
input-scoped closure rule permits it. Shared merge children may be substituted in
several ancestor proofs without being multiplied semantically.

`local_to_global_chain` checks every two-step chain over the same finite language
family. The theorem does not follow from the rejected joint rule.

Semantic laundering is now precise: an inherited account is weakened without an
explicit locally sound, identity-authenticated rewrite or disposition. Equality
in both directions characterizes semantically equivalent representation change;
one-way inclusion characterizes refinement.

### 5.4 Where safety stops

The trace clauses “every executed move has a pre-state receipt,” “no account
branch silently disappears,” “every local transport is sound,” and “a new basis
loss immediately mints review” are prefix safety properties when events and
checks are finite and decidable. A finite bad prefix witnesses every violation.

Safety does not cover all nearby desiderata.

- “Every due inquiry is eventually answered” with no finite deadline is liveness.
  Every prefix `b^n` can still be extended by an answer; no finite bad prefix
  exists. A fixed service window converts it to safety.
- Reason-guided control/non-capture compares runs and is a hyperproperty.
- Normative learning/progress is a performance or convergence property, not
  conservation.
- Future corrective authority includes reachability/effectiveness and is not
  implied by a current account proof.

Thus the classification is defensible only after narrowing the first term:

```
record-internal answerability discipline  safety-like
bounded service discipline                safety-like
unbounded service / improvement           liveness or performance
reason-guided authorship / non-capture     counterfactual hyperproperty
```

“Internal legitimacy” without that narrowing is not a single safety property.

## 6. Basis loss and review

### 6.1 Temporal facts

Keep two predicates:

```
ValidWhenUsed(p,s) := the immutable receipt stored at s was valid
StandsNow(p,t)     := check(R_t,p) is currently valid
```

Later invalidity does not change the first. It changes present answerability.
No current workspace theorem needs retroactive erasure of a normative move. The
scorekeeping model explicitly leaves old vindications recorded after later
undercutting, and the answerability ledger already has basis-keyed reopening.
The settlement no-claw-back theorem is stronger: settlement events themselves
must never reopen.

### 6.2 Trigger

For every `UsedAt(m,p,s)`, retain a Boolean standing state and an invalidation
epoch. On a `true -> false` edge at `t`, append `BasisLost(m,p,s,t,epoch)` and mint
exactly one fresh `Review(m,p,s,epoch)` liability. Persistence while false does
not remint. Reaffirmation followed by another loss creates a new epoch.
`basis_loss_epochs((T,F,F,T,F)) = (1,4)` checks this discipline.

Audit only usage records that predate the current event. Review liabilities and
their certificates enter the next state. This time stratification blocks
instantaneous self-trigger loops. A later loss of the basis used to dispose of a
review mints a new review of that disposition; it does not edit the old proof.
The number of new liabilities at a finite step is bounded by the finite set of
newly invalidated historical usages. There is no bound over an infinite history
without a bound on validity oscillation.

### 6.3 Review demand

The conservative version-one review is wholesale but current-facing:

> Reassess whether the still-operative consequences and current descendant
> accounts of `m` should be reaffirmed, revised, suspended, remedied or
> compensated under current reasons; record a new valid certificate and sound
> account rewrite for the chosen disposition.

For a discharge, review the present consequences of having closed it. For an old
split or merge, follow the account DAG to the current frontier; do not restore a
stale snapshot. For a rule-, bearing- or adequacy-system revision, R6 makes the
changed rule a declared dependency and the same trigger applies. For a chain of
authorized transitions, each actually undertaken certificate is audited; a
review of an early step may point to all current descendants reached through
that step's effect/lineage map.

A semantically equivalent successor warrant can close the review immediately,
but only through an explicit current certificate establishing the same licensed
conclusion or an authorized transport between conclusions. Version equality is
not required; silent substitution is not allowed.

### 6.4 No Forgotten Basis Loss

**Proposition (single derivation, conditional).** Assume:

1. every certificate normatively relied upon by a transition or disposition is
   recorded with `UsedAt` and a valid historical receipt;
2. every current checker input satisfies R4–R7;
3. each true-to-false standing edge is detected and atomically mints one fresh
   review liability linked to the usage and its currently operative effect/account
   frontier;
4. review liabilities enter the No Forgotten Liability calculus;
5. no closure of a review counts without a current certificate and account proof.

Then no detected loss of an undertaken basis can occur while the affected
historical commitment is absent from the current answerability structure.

**Proof.** At the loss step, assumption 3 creates the linked review. By No
Forgotten Liability and assumptions 4–5, every later date retains a live/routed
review descendant or a backed closed review branch. The link records which usage
and current effects it accounts for. Therefore the loss cannot become
unrepresented without violating one of the hypotheses.

The theorem does not show that the review is correct, timely, or eventually
closed; that all materially relevant certificates were recorded; that the
checker tracks environment-relative bearing/adequacy; or that review repairs the
world. Over-approximating dependencies can cause unnecessary review but does not
falsify this safety theorem. Under-approximation does.

## 7. Current semantic demand and traderized enforcement

### 7.1 `Now`

Let a next event contain a current credal state plus possible auxiliary data, and
let `obs(e)=mu`. The natural existential extraction is

```
Now(Q) = {mu | exists e, obs(e)=mu and e in Q}.
```

This is a projection. It does not preserve conjunction. With visible values
`{0,1}` and hidden tags `{0,1}`, let

```
Q allow (0,0),(1,1)
R allow (0,1),(1,0).
```

Then `Now(Q)=Now(R)={0,1}` while `Now(Q intersect R)=empty`.
`now_meet_counterexample` checks the one-step witness. This is the same formal
failure as compiling credal components separately and intersecting their price
images: witnesses in different fibres are incorrectly combined.

Meet preservation holds in either of two useful fragments.

1. **Canonical event:** there is one designated event `emit(mu)` per credal state
   and `Now(Q)={mu | emit(mu) in Q}`. `Now` is then inverse image and preserves
   arbitrary intersections.
2. **Fibre saturation:** next-event membership for every component depends only
   on `obs(e)`. Every visible value admitted separately then has a common event
   witness. Saturation is sufficient, not necessary; the exact condition is the
   common-witness property on every fibre.

Outside these fragments the architecture must form the joint account language

```
Q_t = intersection over current account semantics
```

before applying `Now`. Componentwise `Now` followed by intersection is unsound.

### 7.2 Admissibility gap

Prefix closure supplies none of the force compiler's geometric premises.

- `Now(Q)` may be empty.
- It may be nonconvex: allowing only two endpoint credences excludes their
  midpoint (`now_need_not_be_convex`).
- With an infinite event alphabet it need not be closed.
- It need not have a rational polyhedral presentation or a computable projector.

The missing compiler theorem is therefore explicit:

```
joint current account semantics
  -> nonempty closed convex credal C_t with an effective rational presentation
  -> K_t = pi_t(C_t), nonempty/closed/convex in the price cube
  -> presentation or projector data accepted by force
  -> bounded cumulative enforcement-liability certificate.
```

Convexifying `Now(Q)` is a relaxation, not an identity; it can admit mixtures the
normative semantics excluded. This pass provides no general construction of
`C_t`. It narrows, but does not close, priority item 39.

### 7.3 Division of enforcement work

The transition gate should enforce certificate validity, provenance and scope,
pre-state bearing, account conservation, identity-authenticated rewrites,
input-scoped disposition adequacy, semantic transport, basis-loss minting, and
the feasibility/compiler certificate.

Traderized force should consume only the resulting `K_t` plus the declarations
required by the installed interface. It enforces price-visible credal safety to a
declared tolerance. It cannot enforce historical provenance, inquiry service,
account lineage, non-capture, or semantic distinctions lost by `pi_t`.

The existing preservation theorem consumes a bound on the enforcement position's
cumulative value over the live assessment worlds. A caller must therefore export
not just `C_t` and `K_t`, but the live-world set/capacities or deficit data and a
finite cumulative liability certificate. Procedural safety and credal force are
two gates, not one compilation target.

## 8. Theorem and counterexample matrix

| Candidate claim | Status | Minimal assumptions | Counterexample / proof idea |
|---|---|---|---|
| Rewrite ledger subsumes DA forest | **false as stated; repaired representation theorem** | incidence, global IDs, branch statuses, input-scoped closures, fresh tags | same `{a,b}->{c,d}` equation has parallel and crossed ancestry |
| No Forgotten Liability | **proved, single derivation** | total input fragments; scoped closure; no fresh-as-inherited; unique IDs | induction by account-fragment substitution |
| Local transport implies global transport | **proved after per-input repair** | per-input inclusion; derivative/meet laws; authenticated lineage | induction/cut; exhaustive two-step finite check |
| Proposed joint transport is sufficient | **false** | — | 2 parents, `c_a=top`, `c_b` carries both constraints; joint inclusion passes |
| Safety semantics suffices for record-internal answerability | **conditional yes** | finite decidable events; immediate review; bounded deadlines if service included | every violation has a finite bad prefix |
| Safety semantics suffices for full internal legitimacy | **false** | — | reason-guided control is a coupled-run hyperproperty; eventual service is liveness |
| Undertaken basis is enough without control factorization | **yes for historical answerability; false for reason-guided authorship** | A+B for the first | same certificate record, hidden bit selects different action |
| Finite deps handle arbitrary future defeaters directly | **false** | — | add a fresh undeclared defeater; checker changes while declared view agrees |
| Basis loss plus DA prevents forgotten undermining | **proved, conditional** | complete usage logging; edge trigger; linked review; account conservation | minted review remains live/routed or backed-closed by induction |
| Semantic refinement authenticates successor identity | **false** | — | unrelated stronger obligation is a semantic subset of the old one |
| `Now` preserves conjunction | **false generally** | — | disjoint hidden witnesses in a 2-by-2 event fibre |
| `Now` preserves conjunction in a useful fragment | **proved** | canonical credal event or common-witness/fibre-saturation condition | inverse images preserve intersections |
| Prefix safety yields traderizable `C_t` | **false** | — | current set can be empty or two-point nonconvex |
| Joint current semantics yields traderizable `C_t` | **open** | needs nonempty/closed/convex/effective compiler theorem and liability bound | this is the missing arrow in priority item 39 |
| Internal-answerability conjunction is prefix closed | **yes only for the trace discipline** | checks local and immediate; fixed checker/event schema | bad certification, dropping, unsound rewrite or missed review is finitely witnessed |

## 9. Adversarial cases

| # | Finite case | Outcome |
|---|---|---|
| 1 | `a -> b` carry | one linked open leaf; per-input transport checks |
| 2 | `a -> {b,c}` split | two leaves remain in `a`'s account; neither may be omitted |
| 3 | `{a,b} -> c` merge | `c` occurs in both ancestor accounts; owed lineages do not contract |
| 4 | split with one input-scoped closed branch and one live child | mixed account, not a single status; closure proof retained |
| 5 | suspend `a` with route, later resume with basis | same occurrence identity; status derived from the two account nodes |
| 6 | discharge under `p`, then `p` loses standing | discharge proof remains historical; fresh review targets present consequences |
| 7 | `p` replaced by equivalent `p'` | review closes only on an explicit current equivalence/licence certificate |
| 8 | `p` and `q` independently license `m`, only `p` undertaken | loss of `p` triggers review; `q` can discharge but cannot rewrite the undertaken basis |
| 9 | silently drop `a`, independently mint stronger `f` | equation may leave only `f`; old account is empty, and semantic subset cannot authenticate it |
| 10 | same undertaken certificate, hidden bit changes action | A+B hold, C fails (`hidden_control_pair`) |
| 11 | checker/bearing/adequacy rule self-modifies | rule-version dependency changes; old receipt stands and review is minted after the step |
| 12 | review closure basis later fails | a new review-of-disposition is minted; old review proof is not edited |
| 13 | `Now`/price compilation by components | hidden-fibre witness makes separate extraction accept `{0,1}` while joint semantics accepts none |

Two additional merge attacks matter. A joint semantic rule permits one child to
launder another parent's account. A single terminal witness after two burdens
merge can falsely close both unless disposition witnesses are input scoped. Both
are three-occurrence phenomena already anticipated by the consolidation's
`LG-X1`.

## 10. Relation to the current decomposition

| Current concept | Disposition after this pass |
|---|---|
| provenance `P` | certificate-derivation invariant; not a separate status layer, but not eliminated |
| inquiry/service `I` | generation/entitlement remain state machinery; docketed service becomes a liability; coverage and unbounded service remain separate |
| reasons-responsiveness `RR` | split into certificate-backed authorization/undertaking and counterfactual reason-guided control |
| diachronic answerability `DA` | split into account-resource conservation/transport and automatic basis-loss review |
| semantic faithfulness/statics | separate; account safety is reasoner-relative unless an external adequacy semantics is supplied |
| normative learning | separate performance theorem over `Due`, `Licensed`, loss, margin and coverage |
| counterfactual non-capture/authorship | separate factorization hyperproperty C |
| future corrective authority | separate reachability/effectiveness property |
| settlements | excluded from basis-loss reopening; downstream uses remain reviewable |
| traderized enforcement | downstream consumer of `K_t` and a bounded liability certificate only |

Nothing in the kernel repairs the procedural prosecution's record/environment
gap. A certificate can correctly prove licence under the reasoner's current
bearing and adequacy rules while those rules diverge from the environment. The
kernel makes that use inspectable and re-openable if its represented basis later
changes; it does not prove the represented standard was substantively apt.

## 11. Remaining blockers

1. A substantive instantiation of `Licensed` connecting certificates to reasons,
   scope and defeat without assuming environment-relative bearing.
2. A canonical rule for the dependencies of negative/defeasible judgments,
   including invalidation-index maintenance under self-modification.
3. A typed account-fragment calculus for mixed split/disposition and semantic
   identity certificates; this memo gives the minimum data, not a promoted type.
4. A decision about whether liability specifications describe direct performance
   only or all authorized dispositions. The `1->0` rule requires the latter.
5. A joint-semantics-to-credal compiler proving nonemptiness, closure, convexity,
   effective rational presentation and bounded enforcement liability.
6. A policy for relevance/operative effects in wholesale review. Reviewing every
   historical use is safe and can be prohibitively broad.
7. Any bound on repeated invalidation/reaffirmation cycles or meta-review growth.
8. Lean statements and nonvacuity witnesses for the repaired representation,
   conservation and basis-loss theorems if they are selected for promotion.

## 12. Recommendation

Adopt the repaired kernel as the provisional **record-internal answerability
core**, not as a replacement for the legitimacy architecture.

Adopt:

- immutable undertaken certificates with finite declared dependency views;
- valid-at-use receipts distinct from current standing;
- input-scoped account DAGs with fresh/inherited separation;
- per-input safety-language transport and proof substitution;
- edge-triggered review liabilities with no retroactive history editing;
- joint semantic composition before any lossy `Now` or price projection.

Do not adopt:

- a historical TMS as a theorem hypothesis;
- the multiset equation without incidence and scoped proofs;
- joint transport over an undifferentiated input block;
- authorization or undertaken basis as evidence of reason-guided control;
- prefix safety as a source of convex credal geometry;
- a universal instruction to reopen settlement events.

The kernel stops exactly where a theorem needs substantive reason-connection,
coverage, performance, counterfactual authorship, effective authority, or a
credal compiler. Those remain separate inputs.

## What this memo does not establish

No claim here is registered or kernel checked. The general results are paper
derivations supported by finite executable witnesses, not formal proofs. The
finite language sweep reaches binary traces only through horizon two. The memo
does not construct a full account checker, a reason search procedure, a
substantive `Due` or `Licensed`, a credal compiler, a market, or a learning
process. It does not prove dependency completeness, environmental faithfulness,
review adequacy, eventual review completion, manipulation-freedom, or bounded
meta-liability.

Run the checks with:

```sh
python3 tests/run.py
```
