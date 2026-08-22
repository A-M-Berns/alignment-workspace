# Role-parametric answerability prosecution

Status: **research memo; unregistered**. All new names are provisional. Positive
general claims are paper derivations supported by finite executable witnesses,
not Lean theorems or registry claims.

## Verdict

**UNIFIED WITH WRAPPER.** There is one useful mathematical account kernel, but
not one undifferentiated notion of answerability.

The common kernel says that a reified standing liability cannot be consumed
without a certified, lineage-linked, per-input semantically adequate account.
Its conservation and composition theorems are equivariant under renaming the
parties. They do not care whether the labels name temporal stages, people, or
offices. Later loss of a recognized undertaken basis has the same account-level
effect in every instantiation: mint a linked review liability.

Interpersonal **answerability to** someone needs a distinct relational wrapper:
a recognized standing context, shared liability identifiers, inspectability by
an authorized audience, a non-unilateral semantics and disposition jurisdiction,
and a challenge/adjudication transition. Private reason states alone do not
determine `BasisLost`. A challenge merely raised is not a defeater; an admitted
challenge that changes the recognized standing state is.

The minimal common primitive is therefore **a respondent is answerable for a
standing liability in a named answerability context**. A claimant is not a core
field. `answerable-to(x,ell)` is derived from a context-specific relation giving
`x` standing to demand, inspect, contest, accept, waive, or represent the claim.
Source, beneficiary, holder, and audience cannot safely be collapsed into one
claimant role.

Three repairs to the naïve unification are load-bearing.

1. `respondent` is role-parametric but not inert metadata. Personal performance,
   authority to rewrite, and transfer conditions can depend on it.
2. PR #45's single current reason state must be read as a **recognized
   answerability state indexed by context**, not whichever participant's private
   view is selected after the fact.
3. Delegation is not ordinary content transport. It is an account rewrite plus
   a separately certified change of respondent jurisdiction; whether the old
   respondent remains secondarily liable is part of the rewrite semantics.

This does not produce cooperation, obedience, benevolence, competence,
environment-relative correctness, non-capture, or corrective control.

## 1. Repository orientation

This pass starts from the repaired kernel merged by PR #45, not from a TMS.

| Live result | Constraint on this pass |
|---|---|
| internal-answerability `MEMO.md` | immutable undertaken certificates; input-scoped account DAG; per-input transport; basis-loss review; authorization/undertaking/control split |
| consolidation `THEORY_8_DIACHRONIC_IDENTITY.md` | standing is an entitlement to be answered; burdens require lineage; `LG-X1` forbids one merged bit/witness from closing two burdens; `AD-J5` permits one response with separate coverage edges |
| relational-scorekeeping `TWO_ARC_INTERFACE.md` | another participant's practice can attribute a consequence and challenge; ordinary consequences may be recomputed; ontology change still needs transport; there is no oracle |
| relational-scorekeeping `MODEL.md` | the target writes its acknowledgments while scorekeepers retain distinct practices; challenge force is derived from the challenger's entitlement; a challenge can remain unresolved |
| counterfactual-legitimacy `LEGITIMACY_INTERFACE.md` | answerability is single-run; non-capture is a coupled-run factorization; standing, coverage, access, and effective authority remain distinct |
| deference `FUTURE_AGENT_SPEC.md` | jurisdiction omitted from the type becomes mathematically invisible even when prose calls two arms different |
| reachable-corrective-control | authorization, capability, and effective control cannot be distinguished by labels or by a transition signature that omits the relevant role |

Two existing observations already resist a simple claimant/respondent tuple.
The consolidation's “standing” need not identify a person, and the scorekeeping
round allows several participants to attribute different commitments without an
oracle. Conversely, the deference line shows that a jurisdiction label which no
transition reads is decorative. Roles must be included exactly where they change
authorization or semantics, and nowhere else.

## 2. The common invariant

Fix an answerability context `kappa`. At date `t`, a liability occurrence `ell`
has an immutable identity, a current respondent, and a safety specification.
A move consuming `ell` is admitted only when:

1. its undertaken certificate checked in the recognized pre-move state of
   `kappa`;
2. the mover is authorized to act for `ell`;
3. the account DAG supplies an input-scoped successor or closure branch for
   `ell`;
4. the account semantics refines the residual of `[[ell]]` after the move; and
5. any change of respondent or standing holder has the jurisdictional authority
   required by `kappa`.

For each old input separately,

```
[[Account_tau(ell)]]  subseteq  derivative(move, [[ell]]).
```

No joint strengthening by another input may pay this debt. A shared response is
allowed only by retaining one coverage/disposition edge per old liability, as in
`AD-J5` and PR #45's merge repair.

What is conserved is not a past conclusion, preference, wording, person, or
physical carrier. It is:

```
old occurrence identity
  + its account lineage
  + its residual semantic demand
  + the standing context's entitlement to an account.
```

The last term belongs to the wrapper. The first three support the common
conservation theorem.

## 3. Smallest surviving interface

### 3.1 Account kernel

```
Context, Party, Occurrence, Spec, Move, Certificate, Account

respondent : Occurrence -> Party
spec       : Occurrence -> Spec
inputs     : Account -> FiniteMultiset Occurrence
outputs    : Account -> FiniteMultiset Occurrence
incidence  : Account -> inputs x outputs -> Prop
closed     : Account -> inputs -> Option DispositionWitness

undertaken : Move -> Certificate
stands     : Context -> RecognizedState -> Certificate -> Prop
authorized : Context -> RecognizedState -> Party -> Occurrence -> Move -> Prop
transport  : Context -> Account -> Occurrence -> Prop
```

`transport(kappa,a,ell)` is the per-input semantic inclusion, evaluated with the
semantic/checker version recognized by `kappa`. The existing certificate
interface supplies conclusion binding, declared dependencies, pre-state checks,
immutable receipts, explanatory invalidation, checker closure, and aggregate
defeat keys. Provenance remains proof-relevant inside that checker.

The account theorem itself can erase `Party` after authorization has been
checked. An honest transition gate cannot: it must know who may submit a move and
whether changing the respondent is authorized. `respondent` is therefore the one
party role retained in the common interface.

The following fields are not required by conservation or transport and are
removed from the kernel:

- claimant;
- source;
- beneficiary;
- audience;
- private belief/reason states;
- challenge generation;
- consent as a universal primitive.

Consent can be one jurisdictional route to authority, but institutional office,
statute, prior contract, or court order can be others.

### 3.2 Interpersonal standing wrapper

```
StandingContext kappa
recognizedState : kappa x Time -> RecognizedState
holdsStanding   : kappa x Party x Occurrence -> Prop
audience        : kappa x Party x Occurrence -> Prop
canInspect      : kappa x Party x RecordObject -> Prop
mayChallenge    : kappa x Party x Occurrence -> Prop
admitChallenge  : kappa x Challenge x RecognizedState -> RecognizedState
mayDispose      : kappa x Party x Occurrence x Disposition -> Prop
mayTransfer     : kappa x Occurrence x Party x Party -> Prop
meaningVersion  : kappa x Occurrence -> SemanticVersion
```

`answerableTo(kappa,x,ell)` is derived when `x` is a holder or authorized
audience and the context gives a real route to inspect and contest the alleged
account. The challenger need not personally run the checker; an authorized
representative or forum can do so. A nominal challenge right with no transition
by which a successful challenge changes standing is not enough.

This wrapper is not an oracle. It states whose verdict is constitutive **within
this relation**. Environment-relative adequacy remains a further theorem. If two
institutions recognize different standing states, the correct model has two
contexts `kappa_1,kappa_2`, not one secretly privileged private reason state.

## 4. Is a claimant fundamental?

No, for three independent reasons.

First, a constitution can impose a reporting or preservation liability on an
office without granting one person sovereign ownership of it. The finite witness
`constitutional-duty` passes account conservation with an empty holder relation.

Second, one interpersonal claim can separate four roles:

```
source       the event or authority from which the claim arose
beneficiary  whose interests performance serves
holder       who may demand, waive, assign, or settle it
audience     who may inspect or contest an account
```

They can be different parties. Treating all four as “Alice” loses institutional
succession, representation, third-party beneficiaries, and public duties.

Third, the diachronic source is often an earlier transition, not a sovereign past
self. The later reasoner owes an account **for** what remains standing; it does
not owe obedience **to** the temporal stage that first recorded it.

The primitive `Claim(Alice,ell,Bob)` is a valid interpersonal presentation only
when the context makes Alice both holder and audience. It is not the common
mathematical core.

Holder transfer is normally a wrapper transition: replace the authorized holder
edge while leaving `ell`, its respondent, and its meaning fixed. Beneficiary
transfer is different when the beneficiary occurs in the specification (for
example, “pay Alice”); it then needs semantic transport as well. Institutional
succession at both endpoints is the composition of a holder/audience transition
and an authorized respondent-changing account rewrite. A single undifferentiated
claimant field cannot state these three cases without ambiguity.

## 5. Respondent identity is not metadata

The claim that party identity can be removed entirely is false. One old
liability requiring Bob's personal apology and a proposed Carol apology have the
same action-kind trace after actor labels are erased. The role-erasing checker
accepts the substitution; the role-sensitive derivative of the old language on
Carol's action is empty.

This is a two-event counterexample:

```
[[ell]] = prefix-closure { Bob.apologize_to(Alice) }
proposed event = Carol.apologize_to(Alice)
```

It also shows why a bare transfer grant is not always sufficient. Some
liabilities are delegable; personal performance liabilities are not. The
respondent may be represented as a typed parameter inside `Spec` rather than a
separate semantic field, but then it is still semantic and the checker must bind
it. Treating it as inert metadata is unsound.

## 6. Role-parametric representation theorem

**Proposition (single derivation).** Let two finite account histories differ only
by a bijection on party labels. Rename every respondent, actor, counterparty,
authorization edge, transfer grant, and party-indexed event in every
specification by the same bijection. If certificate standing is unchanged, the
account checker returns the same result on both histories. Consequently No
Forgotten Liability and Local-to-Global Semantic Conservation hold in one iff
they hold in the other.

**Proof idea.** Incidence, occurrence identity, fresh/inherited tags, and scoped
closure witnesses contain no party labels. Equality tests on respondents and
membership tests in authorization relations commute with a bijection. Derivative,
intersection, and subset commute with pointwise event renaming. Induct over
account substitutions. The executable `test_16` checks the smallest nontrivial
closure history under the relabeling `Earlier->Alice`, `Later->Bob`.

The assumptions are important. Renaming respondents without renaming the event
semantics or authority relations is not an isomorphism; it is an unauthorized
role change. The theorem proves a common calculus, not that temporal succession
and interpersonal standing have the same wrapper.

## 7. Diachronic instantiation

Use a persistent reasoner or office `A` as respondent. Temporal stages
`A_t,A_{t+1}` are states/actors implementing that role, not claimant and
respondent endpoints of every liability. A liability can record its birth event
at `t`, and the stage at `t+k` inherits the live account frontier.

The later stage may:

- reverse the old conclusion when the old specification permits a certified
  defeat/disposition;
- split or merge occurrences with per-input coverage;
- translate obsolete vocabulary with an identity/adequacy certificate;
- revise the reason system after a pre-state certificate check;
- discover an old error and create a current-facing remedy/review;
- continue an account whose original source no longer exists; or
- update a holder/beneficiary relation without treating that relation as the
  source of semantic authority.

It may not silently delete the old account, replace it with an unrelated strong
liability, or redefine the old specification before checking transport.

Later defeat of the undertaken basis leaves `ValidWhenUsed` intact and changes
recognized current standing. The old transition remains in history and a review
liability targets its current effects/frontier. This recovers PR #45 without
past-self obedience. The executable reversal passes; the same one-node history
with its coverage entry omitted fails `lineage.forgotten`.

Exactly conserved: owed identity, lineage, and residual demand under the current
recognized account semantics. Not conserved: literal wording, current status,
the original carrier, the old verdict, or the old stage's authority over future
judgment.

## 8. Interagent instantiation

For `Alice --ell--> Bob`, the core makes Bob the current respondent and keeps
`ell`'s old meaning immutable during the rewrite check. This is enough for an
internally coherent Bob-led account. It is not yet answerability to Alice.

The smallest additional conditions are:

1. `ell` is a shared identifier in context `kappa`;
2. Alice is a holder or authorized audience for it;
3. Alice or her forum can inspect the certificate, dependency receipt, incidence
   edge, and adequacy witness allegedly answering `ell`;
4. the old meaning and checker version cannot be changed by Bob unilaterally;
5. there is a challenge protocol whose successful branch changes recognized
   standing or disposition status; and
6. jurisdiction states who may waive, settle, novate, transfer, or adjudicate.

The executable uninspectable-certificate case passes the core checker and fails
`answerable_to(Alice,ell)`. Therefore the interpersonal case is not obtained by
merely adding a claimant label. Visibility and contestability have operational
content.

The wrapper need not guarantee that Alice wins, that Bob agrees, or that the
forum is objectively correct. It must make successful and unsuccessful
challenges distinguishable in the transition system. Otherwise “contestability”
is decorative in the same way the deference line's unread jurisdiction label was.

## 9. Multiple reason states and recognized standing

Let Alice privately reject `p` and Bob privately accept it. Neither private
predicate can define unqualified basis loss:

```
Alice: not stands_A(p)
Bob:       stands_B(p)
```

The two-element witness returns both truth values. Choosing Bob makes
answerability self-certified; choosing Alice gives the holder unilateral control
over Bob's licenses. Taking consensus leaves every contested basis standing.

| Candidate standing rule | Verdict |
|---|---|
| Bob-relative | valid as Bob-internal answerability; insufficient for answerability to Alice |
| Alice-relative | valid as Alice's attribution; gives Alice unilateral constitutive authority if used globally |
| public/institutional | supplies one determinate relation-relative trigger, without claiming objective truth |
| perspectival | honest when no shared forum exists; yields several indexed verdicts, not one |

The smallest repair is context-indexed recognition:

```
StandsNow(kappa,p,t) := check(RecognizedState(kappa,t),p).valid
BasisLost(kappa,p,t) := StandsNow(kappa,p,t-1) and not StandsNow(kappa,p,t).
```

`RecognizedState` can be an institutional public record, a contractually selected
forum, or the single reasoner's adopted current record. “Public” means common to
the answerability relation, not universally accepted or objectively correct.

This slightly sharpens PR #45. Its `R_t` was sufficient in a single-record
model, but the reusable interface must say **which context's standing** the basis
loss trigger reads. Private discovery becomes a proposal/challenge; admission
into the recognized state is the standing-changing event.

## 10. Challenge and reconsideration

The proposed correspondence is true only after admission.

```
new reason d privately appears
        |
        v
challenge/proposal is raised             no basis loss yet
        |
        v
adjudication recognizes d as defeating p
        |
        v
recognized standing p: true -> false
        |
        v
BasisLost(kappa,m,p) and Review(kappa,m,p)
```

Diachronic reflection and interpersonal contestation can use different routes to
the third line. Their formal effect from that line onward is identical. An
unsuccessful challenge leaves recognized standing unchanged and mints no review.

Interpersonal answerability requires both a right/route to challenge and a
substantive admission rule. It does not require every challenge to succeed.
Diachronic answerability can lack a separately empowered challenger because the
reasoner's update process supplies proposals, but it still needs a rule deciding
when a private discovery changes the recognized record.

## 11. Who decides adequacy?

Respondent-relative semantics alone is vacuous: Bob can weaken Alice's `pay`
claim to `pay-or-skip` and certify his own restatement. The finite checker rejects
this because the successor language is not a subset of the old residual.
Claimant-relative semantics alone creates the symmetric domination risk.

The weakest anti-laundering requirement is not an objective oracle. It is:

> The old liability's meaning and adequacy-checker version are fixed by the
> recognized context during a rewrite, and neither endpoint alone can change
> them without a separately authorized, visible, challengeable transition.

This can be constitutional semantics, a shared protocol, or an explicitly
selected external standard. If Alice and Bob retain irreconcilable semantics,
use perspectival predicates `adequate_kappaA` and `adequate_kappaB`; there is then
no single interpersonal-adequacy verdict to prove. Environment-relative
faithfulness is still a separate property, exactly as the procedural
prosecution's record-equivalent counterexamples require.

This is a relational adequacy problem, but it does not change derivative,
incidence, or per-input transport. It supplies the interpretation those core
operations consume.

## 12. Delegation and role-changing rewrites

Suppose `Alice --ell--> Bob` and Bob proposes Carol as successor respondent.
Lineage plus semantic transport is insufficient. The minimal accepted form is:

```
ell_Bob --delegate(Carol), q--> ell'_Carol
```

where:

- `q` is standing and licenses this transfer under `kappa`;
- `mayTransfer(kappa,ell,Bob,Carol)` holds;
- Carol's successor specification refines the derivative of `ell` after the
  delegation event; and
- the account says whether Bob is novated out or remains a secondary respondent.

The executable pair has identical lineage and semantics. With the transfer grant
it passes; without the grant it fails `role.transfer_unauthorized`. A personal
apology counterexample fails even with generic delegation authority because the
old semantics does not admit Carol's performance.

Stress-test results:

| Case | Account consequence |
|---|---|
| Bob disappears | valid only under authorized novation and a delegable old specification |
| Bob remains secondary | retain a Bob branch and link Carol's performance branch; no weakening |
| Alice consents | consent can witness `mayTransfer`; it is sufficient only in a context granting Alice that jurisdiction |
| Alice does not consent | invalid unless another recognized authority already permits delegation |
| Carol less capable | not detected unless competence/service is in `Spec`; otherwise outside answerability |
| Carol more capable, manipulative selection | may pass account safety and fail authorship/non-capture |
| one branch delegated | only that split occurrence changes respondent |
| Carol delegates onward | ordinary proof substitution, with a fresh transfer authorization at every edge |
| Alice replaced by successor institution | usually a wrapper holder/audience transfer; if beneficiary-sensitive meaning changes, also an account rewrite |

Thus target claim E is false as worded if “ordinary” means semantic transport
alone, and true after adding explicit role-change jurisdiction. This is a real
connection to AI delegation at the level of authority and obligation lineage.
It does not import the deference line's epistemic trust, competence, or corrective
control theorems.

## 13. Shared response, merge, and mutuality

One response can answer liabilities held by two claimants when the respondent is
Bob and the move has two input-scoped coverage/disposition witnesses. The two old
identities remain distinct. This is exactly PR #45's reading of `AD-J5`.

The rejected joint rule remains dangerous. In the smallest witness, child
`c_a=top` carries nothing for parent `p_a`, while `c_b` carries both parents'
semantic strength. The global intersection passes and the per-input check rejects
`p_a`. Different holders do not repair it; they make the laundering politically
visible but mathematically unchanged.

Mutual answerability is two directed liabilities:

```
Alice --ell_AB--> Bob
Bob   --ell_BA--> Alice.
```

No new conservation primitive is needed. A joint settlement can cover both only
with authority for both inputs and two scoped witnesses. Answering one may mint a
fresh liability in the reverse direction; conflicts may make the joint semantic
book infeasible; negotiations may propose a two-input superseding rewrite. Those
are interactions between ledgers, not a new kind of edge. Feasibility,
bargaining, fairness, and conflict resolution remain separate.

If each party challenges the other's undertaken basis, each recognized
true-to-false edge mints its own review occurrence. If their recognized contexts
diverge, mutuality does not manufacture consensus: each context has its own
account verdict. A negotiated merge is valid only if both old inputs have
authorization and per-input transport into the common successor.

## 14. Answerability is not cooperation

The strongest nontrivial common theorem is:

> Under complete certified logging, total input-scoped account fragments,
> recognized authorization, per-input semantic transport, and basis-loss
> reopening, no standing liability can silently disappear or be weakened in the
> named context.

It does not imply that the respondent performs the claimant's preferred action.
A liability specification may permit refusal, defeat, compensation, suspension,
or another authorized disposition. The finite Bob case closes an Alice-held
claim with `refuse-with-reasons`, because that event is explicitly admitted by
the old specification. If the old claim instead requires payment, reasons alone
do not make refusal adequate.

Accordingly answerability guarantees integrity of disposition relative to a
standing context. It does not guarantee agreement, obedience, benevolence,
aligned preferences, successful service, or cooperation.

## 15. Separation from authorship/non-capture

Neither direction holds.

**Answerability without authorship.** Both runs receive the same admitted reason
set `{p_yes,p_no}`. A hidden advisor bit selects which licensed answer Bob
undertakes. Each realized run has a standing certificate and a complete account,
but the protected response differs while the admitted reason trace is held
fixed. The coupled-run factorization fails.

**Authorship without answerability.** Bob's response is a deterministic function
of his admitted reason trace under every advisor policy, while he silently omits
Alice's old liability from the account ledger. Factorization holds and No
Forgotten Liability fails.

This supports, but does not prove sufficient, the prospective decomposition:

```
relational legitimacy = answerability + authorship/non-capture + other clauses.
```

It cannot yet be an equality. Coverage, environmental adequacy, standing
legitimacy, and effective authority remain independent inputs in the current
workspace.

## 16. Theorem and counterexample matrix

| Candidate claim | Status | Minimal assumptions | Witness / proof idea |
|---|---|---|---|
| One kernel covers diachronic + interagent | **yes for account conservation; full verdict requires wrapper** | role-equivariant checker/semantics; context-indexed standing | party-bijection induction; executable case 16 |
| Claimant is a necessary primitive | **false** | respondent, occurrence, standing context | constitutional duty with no holder; source/beneficiary/audience can differ |
| Respondent identity is metadata only | **false** | — | Bob/Carol personal-apology traces become equal only after unsound role erasure |
| Interpersonal case only needs contestability wrapper | **false if read narrowly; repaired yes** | standing, shared IDs, visibility, non-unilateral semantics, adjudication, jurisdiction | Bob's invisible certificate and unilateral `pay-or-skip` restatement |
| Basis loss can use a single public standing state | **yes per named context, not globally** | recognized state and checker version fixed by `kappa` | Alice/Bob private disagreement has no unindexed verdict |
| Successful challenge = diachronic defeater formally | **yes after recognition** | admission changes recognized dependency/standing | both become the same true-to-false edge; raised/failed challenges do not |
| Delegation is ordinary account transport | **false** | — | semantic transport passes without a transfer grant; role gate rejects |
| Delegation preservation after repair | **conditional yes** | transfer authority, delegable semantics, acceptance/novation rule, per-input lineage | role-changing rewrite; composition for onward delegation |
| Mutual answerability needs no new primitive | **yes account-wise** | distinct inputs; scoped authority and coverage | two directed liabilities; one joint move with two witnesses |
| Answerability implies reason-guided control | **false** | — | fixed admitted reasons, hidden policy selects response |
| Reason-guided control implies answerability | **false** | — | deterministic reason-mediated policy silently deletes an old liability |
| Answerability is sufficient for cooperation | **false** | — | adequate certified refusal |
| Common kernel proves objective adequacy | **false** | — | two recognized contexts may interpret/check the claim differently |

## 17. Adversarial microcases

| # | Case | Result |
|---|---|---|
| 1 | future self reverses old commitment with certified closure | accepted; conclusion preservation is not required |
| 2 | future self deletes the same one-node liability without coverage | rejected as `lineage.forgotten` |
| 3 | Bob gives Alice a genuine reason-backed revision/refusal | core accepted when old semantics permits the disposition |
| 4 | Bob's certificate is valid but invisible to Alice | core accepted; `answerableTo(Alice)` false |
| 5 | Alice's challenge is admitted | recognized standing edge falls; basis loss emitted |
| 6 | Alice's challenge is rejected | no recognized edge; no basis loss |
| 7 | Bob accepts `p`, Alice rejects `p` privately | no unique unindexed basis-loss verdict |
| 8 | public/contextual adjudication admits the defeater | deterministic recognized basis loss |
| 9 | Bob restates `pay` as `pay-or-skip` | per-input semantic transport rejects weakening |
| 10 | Bob delegates to Carol with grant and delegable semantics | accepted role-changing rewrite |
| 11 | same rewrite without transfer grant | rejected despite semantic adequacy |
| 12 | one Bob response answers Alice and Dana liabilities | accepted with two old IDs and two coverage witnesses |
| 13 | one strong child launders another parent's account | global intersection passes; per-input transport rejects |
| 14 | reciprocal Alice/Bob liabilities settle in one joint event | ordinary two-input rewrite with authority/witness per input |
| 15 | hidden policy selects between two admitted licensed reasons | every run answerable; coupled-run authorship fails |
| 16 | diachronic closure relabeled as Alice/Bob closure | same checker verdict under role bijection |

Additional witnesses show an institutional duty with no claimant, authorship
without account conservation, a reason-backed refusal without cooperation, and
role erasure equating Bob's and Carol's personal performance.

Run them with:

```sh
python3 projects/normativity/legitimacy/rounds/2026-08-22-role-parametric-answerability/tests/run.py
```

## 18. What changes between instantiations

| Object | Diachronic | Interagent |
|---|---|---|
| respondent | persistent reasoner/office implemented by current stage | Bob or another present party |
| source | prior event/stage; normally no current sovereignty | promise, institution, event, or party |
| holder/audience | often the current reasoner or institutional record; can be implicit | must be stated to obtain `answerable-to` |
| recognized state | current adopted normative record | public/contractual/institutional record indexed by context |
| private disagreement | proposal for self-revision | challenge from one participant |
| standing change | admitted self-revision | successful adjudicated challenge |
| visibility | internal archive access can be architectural | must reach Alice or an authorized forum |
| role transfer | stage succession usually preserves persistent respondent | delegation/novation changes respondent and needs authority |

The account DAG, per-input transport, basis receipts, and review minting do not
change. The route by which facts acquire recognized standing does.

## 19. Boundaries and workspace implications

- **RR:** the authorization/undertaken-basis versus control split survives.
  Interpersonal visibility belongs to the standing wrapper, not to control.
- **DA:** account conservation is role-parametric. Automatic reopening must be
  indexed by a recognized answerability context.
- **Provenance/authority:** certificate provenance still prevents scope
  amplification; respondent/holder transfer needs an explicit jurisdictional
  grant, not merely semantic inclusion.
- **Relational scorekeeping:** its distinct practices are not noise; they are the
  counterexample to an unindexed `StandsNow`. Challenges become account-relevant
  only when the selected context recognizes them.
- **Deference:** the connection is mathematically real for delegation lineage and
  jurisdiction. Trust, competence, and value are not supplied. An unread
  respondent/authority role would repeat the deference line's signature collapse.
- **Corrigibility:** review liabilities make undermining answerable; they do not
  guarantee that a principal can causally reach or enforce correction.
- **Traderized enforcement:** unchanged. A context must still compile joint
  semantics to a nonempty closed convex credal set before price projection.

No current theorem map should be rewritten around the unification. The result is
an interface diagnosis, not a promoted replacement architecture.

## 20. Remaining mathematical blockers

1. A typed recognized-standing transition system showing when a private reason or
   challenge is admitted without assuming an oracle.
2. A nonvacuous interpersonal visibility/contestability definition allowing
   authorized representatives and privacy-preserving verification.
3. A semantic theory of respondent-sensitive and beneficiary-sensitive
   liabilities, including exactly when novation is possible.
4. Composition of role-changing rewrites with secondary liability, split
   delegation, and holder succession.
5. Conflict/feasibility conditions for interacting mutual ledgers.
6. Environment-relative adequacy or a principled plural-context result; the
   wrapper supplies constitutive standing, not truth.
7. Lean statements for party-equivariance and context-indexed No Forgotten Basis
   Loss if the interface is selected for promotion.
8. Any theorem connecting account-safe delegation to epistemic deference,
   competence, cooperation, or effective corrective control.

## 21. Recommendation

### Direct answers

1. **One concept?** Yes at the level of certified account conservation;
   interpersonal answerability-to has an additional irreducibly relational
   standing institution.
2. **Common kernel?** A respondent may change or close a standing liability only
   by a standing undertaken certificate, explicit old-input lineage, and an
   account that refines that old input's residual semantics; recognized later
   basis loss mints a linked review.
3. **What changes?** The account algebra does not. Holder/audience standing,
   visibility, adjudication, and role-transfer jurisdiction become explicit.
4. **Merely standing plus contestability?** No if that phrase omits shared IDs,
   inspectability, non-unilateral meaning, and consequential adjudication. Yes
   when those are included in the wrapper.
5. **Public standing state?** A single recognized state is required per
   non-perspectival answerability context; no globally privileged public state is
   required or justified.
6. **Claimant fundamental?** No. `answerable for` is core; `answerable to` is
   derived from holder/audience rights in a context.
7. **Delegation?** Yes as respondent-changing account preservation, but only
   with transfer jurisdiction and delegable semantics; semantic inclusion alone
   is insufficient.
8. **Legitimacy/deference/corrigibility payoff?** Real but narrow: it supplies a
   common obligation-lineage and jurisdiction interface for delegation and
   review. Connections to trust, competence, cooperation, and effective
   corrective authority remain unproved.

Adopt **UNIFIED WITH WRAPPER** as the provisional research verdict.

Adopt as common:

- certified undertaken moves;
- respondent-indexed liability occurrences;
- explicit lineage and scoped account proofs;
- per-old-liability semantic transport;
- context-indexed basis-loss reopening; and
- role-equivariance under coherent relabeling.

Add for interpersonal `answerable-to`:

- a recognized standing/adjudication context;
- holder/audience and shared-identifier relations;
- inspectability and a consequential challenge route;
- non-unilateral semantic/checker versioning; and
- explicit disposition and transfer jurisdiction.

Reject:

- claimant as a universal core primitive;
- private Bob-relative or Alice-relative standing as the unqualified trigger;
- respondent identity as decorative metadata;
- delegation by semantic transport alone;
- challenge-raised as equivalent to challenge-successful;
- answerability as cooperation, correctness, authorship, or control.

The central invariant survives, but only in its `answerable for` form. The
irreducibly interpersonal ingredient is not a different conservation calculus;
it is the institution of **who has standing to see, contest, and authoritatively
alter the recognized account**.

## What this memo does not establish

No claim is registered. The finite checker is deliberately small and does not
model proof search, cryptographic visibility, strategic adjudication, objective
normative truth, competence, bargaining, enforcement, learning, or market force.
Its safety languages are finite. Its party-equivariance test is one minimal
history, while the general result is a paper induction. The memo does not prove
that any real institution has legitimate standing, that every challenge is heard,
that review terminates, or that authorized delegation is wise.
