# Role-parametric answerability: final consolidation

Status: **research memo; unregistered**. The general results below are paper
derivations supported by finite witnesses, not Lean theorems or registry claims.

## Final verdict

Registered round verdict: **UNIFIED WITH WRAPPER.** Final architectural
recommendation: **SINGH-INFORMED WRAPPER.** The architecture is ready to freeze
as a provisional interface.

Once a standing liability exists, the proof obligations governing its
accountable transformation are role-parametric. Social commitment theory and a
diachronic constitutional record supply different kinds of standing; neither is
reduced to the other. The common answerability law says that an inherited
liability cannot be transformed or removed without a standing undertaken basis,
old-input lineage, and a disposition valid for that old liability. Later
recognized loss of the undertaken basis creates a linked review liability.

The remaining semantic ambiguity has a small repair. Do not make an opaque
`Spec` primitive, and do not derive meaning from whatever lifecycle rules happen
to be current. A liability occurrence carries substantive content and an
immutable receipt for the lifecycle/semantic version governing that occurrence.
Its full answer semantics is derived from those components. The abstract account
theorem consumes only an old-input-indexed `ValidDisposition` judgment; finite
prefix-safety languages and derivatives are one implementation and proof method.

The headline is:

> Standing theory tells us what is owed and which operations have normative
> effect. Answerability theory tells us what must be shown when what is owed
> changes.

Neither box establishes that the standing institution is morally legitimate or
environmentally correct.

## 1. Repository constraint

This round starts from PR #45's repaired internal-answerability kernel:

- immutable undertaken reason certificates checked in the pre-state;
- input-scoped account lineage and explicit closure witnesses;
- per-old-input semantic transport, not global-strength compensation;
- basis-loss review without retroactive history editing; and
- separation of authorization, undertaken basis, and counterfactual control.

The consolidation's `LG-X1`/`AD-J5` distinction remains load-bearing: one event
may answer several old liabilities, but each old identity needs its own coverage
or disposition edge. Relational scorekeeping supplies the counterexample to a
single private reason state. Counterfactual legitimacy keeps authorship/non-
capture outside single-run answerability. Deference work shows why role or
jurisdiction labels are meaningful only when a transition reads them.

## 2. The theory in two boxes

### Box 1 — standing

A standing institution supplies:

```
Occurrence
  id                immutable occurrence identity
  respondent        generic party currently bearing it
  demand            substantive content
  context            pointer to the governing standing institution
  meaningReceipt     pinned lifecycle and semantic versions

ContextState(context,t)
  live occurrences
  recognized reasons and policies
  operations that have normative effect
  evidence and contest routes, where interpersonal answerability requires them
```

The interpersonal instantiation uses a Singh-style named social commitment:

```
C(debtor, creditor, G, p)
```

Here `debtor` instantiates generic `respondent`, `creditor` gives the social
direction, `G` is the social context group, and `p` is the substantive discharge
condition. `G` plus its time-indexed record/protocol instantiates generic
`context`; `G` alone is not a transition system.

The diachronic instantiation uses a persistent reasoner, office, or constitution
as respondent/context. Earlier and later stages are carriers of that role. It
does not invent an earlier-self creditor or make the future stage obedient to a
past judgment.

### Box 2 — answerability

For every nonfresh transformation of an old occurrence `ell`, record:

```
undertaken basis p : Licensed(move)
lineage edge        ell ~~> disposition
disposition proof  ValidDisposition(preState, ell, move, disposition)
```

A disposition is one of only three generic account shapes:

```
Performance(evidence)                  old demand is satisfied; 1 -> 0
Closure(kind, evidence, ruleVersion)   valid nonsatisfaction exit; 1 -> 0
Transform(children, roleEffect, proof) liability continues; 1 -> k
```

Fresh creation is `0 -> 1` and does not answer an unrelated old occurrence.
Shared events, splits, merges, and mixed discharge are represented by one
input-scoped disposition per consumed occurrence. Suspension is a Transform
whose live child has suspended lifecycle status. Composition is account-proof
substitution/cut.

If an undertaken historical basis later changes from standing to nonstanding in
the recognized context state, retain the historical disposition and mint:

```
Review(oldOccurrence, operation, historicalBasis)
```

## 3. Disposition and lifecycle semantics

### 3.1 Why authorization is not adequacy

For `c = C(Bob,Alice,G,p)`, these facts differ:

- Bob performs and evidence shows `p` obtained;
- Alice or `G` exercises a recognized power to Release;
- Bob exercises a recognized cancellation power under a standing policy;
- a recognized Delegate or Assign changes one role.

The first is substantive satisfaction. The others are normatively operative
alterations. A certificate that merely says an actor is authorized does not show
which effect follows, that the operation has the required shape, or that it
applies under the lifecycle version governing this occurrence.

Let `v = meaningReceipt(ell).lifecycleVersion`. The social implementation uses:

```
AnswerSem(ell)
  := LifecycleSem_v(
       demand(ell), respondent(ell), socialRoles(ell), context(ell))

ValidDisposition(kappa,t,ell,m,d)
  := stands_pre(undertakenBasis(m))
   and operationEnabled_v(ell,m)
   and actorHasPower(ContextState(kappa,t),ell,m)
   and lifecycleEffect_v(ell,m) = frontier(d)
   and evidenceAdequate_v(ell,m,d).
```

For Performance, `evidenceAdequate` establishes the substantive condition. For
Release or Cancel, it establishes the operative act, actor, policy, version, and
recognized lifecycle effect—not that `p` occurred. For Delegate or Assign, it
also checks the correct role change and the successor demand/meaning receipt.

This yields three distinct judgments:

```
institutionally effective in kappa
semantically valid under ell's pinned lifecycle semantics
morally/environmentally adequate
```

The first two constitute record-internal answerability. The third remains an
environment/standing-legitimacy theorem. A context can correctly record that
Alice released Bob without thereby proving that the context or release rule is
morally legitimate.

### 3.2 Why current lifecycle rules alone are insufficient

The smallest counterexample has one old commitment and two policy versions.

```
t0: v0 permits release only by Alice; ell is created under v0
t1: G adopts v1 permitting unilateral debtor self-release
t2: Bob invokes v1 to erase ell
```

If `ell` contains only a context pointer and its meaning is recomputed from the
current policy, the rule change silently widens an old liability's exits. No
rewrite of `ell` is visible. Therefore substantive content plus an unversioned
context pointer does **not** suffice.

Smallest repair: pin a lifecycle/semantic receipt at birth. A later policy may
govern new occurrences immediately. Applying it to an old occurrence requires
either a rule that was already part of the pinned lifecycle semantics or an
explicit, reason-backed migration disposition for that occurrence. Thus the old
opaque `Spec` can be decomposed, but not erased completely.

The finite checker calls the derived denotation `answer_language`. It is built
from the substantive condition and pinned lifecycle version. In a fuller model,
the lifecycle compiler must prove:

```
[[Account_d(ell)]] subseteq derivative(move, AnswerSem(ell)).
```

This per-input inclusion remains the semantic soundness obligation for a
trace/safety implementation. The abstract conservation theorem needs only
`ValidDisposition` with the corresponding per-input soundness law; it need not
make prefix languages primitive.

## 4. Singh operations compile to generic accounts

| Singh operation | Account shape | Substantive/lifecycle effect | Required proof retained in history |
|---|---|---|---|
| Create | `0 -> 1` | instantiate a fresh commitment, typically from role/policy | creation basis and new occurrence receipt; never payment for an old input |
| Discharge | `1 -> 0` | substantive condition obtains | `Performance(conditionEvidence)` |
| Cancel | `1 -> 0` | debtor revokes subject to applicable cancellation policy | `Closure(Cancellation,operativeEvidence,v)` |
| Release | `1 -> 0` | creditor or context lets debtor off without success/failure | `Closure(Release,operativeEvidence,v)` |
| Delegate | `1 -> 1` | debtor changes within the context | `Transform(child,DebtorChange,role/policy/transport proof)` |
| Assign | `1 -> 1` | creditor changes within the context | `Transform(child,CreditorChange,role/policy/transport proof)` |

The kernel should not have six constructors. The six typed standing-layer
operations compile to fresh, closure, and transform accounts. Their types remain
proof-relevant. Discharge and Release can have the same empty live frontier but
different account histories: condition-obtained versus release-power exercised.
Delegate and Assign both have one successor but alter different normative roles.

Singh's O5 permits Delegate by the **new debtor or context**, not automatically
by the old debtor. A separate policy may empower the old debtor, but that is an
extension. O6 permits Assign by the present creditor if authorized, or by the
context. Singh (1999) does not specify retained secondary liability; if Bob
remains secondarily answerable after Carol becomes debtor, the account DAG keeps
a Bob branch rather than reading that result into Delegate.

## 5. Minimal common theorem

### No Silent Disposition / Answerability Conservation

Fix a recognized standing context and a finite history. Assume:

1. every normatively operative transformation is completely logged, with fresh
   outputs distinguished from successors;
2. each move records an undertaken certificate valid in the recognized
   pre-state;
3. every consumed old occurrence has an input-scoped lineage edge to exactly its
   disposition account;
4. each such account satisfies `ValidDisposition` for that old occurrence, and
   the disposition semantics is per-input sound;
5. disposition/account proofs compose by substitution; and
6. recognized loss of every relied-upon historical basis mints a linked review
   occurrence which itself remains under account conservation.

Then, at every later time, each historical liability occurrence has either:

- lineage-linked current descendants;
- an explicit typed closure proof; or
- both, for a mixed disposition;

and every recognized undermining of its historical disposition has a linked live
or closed review account. No unrelated fresh liability can count toward that
account, and global strength from another input cannot compensate for weakening
this input.

**Proof idea.** Induct over the rewrite ledger. Total input-scoped incidence gives
the local case; `ValidDisposition` rules out silent deletion and invalid closure;
freshness tags rule out substitution by unrelated obligations; per-input
soundness rules out semantic laundering; proof substitution gives the inductive
step. On a recognized true-to-false basis edge, the logging rule adds a fresh
review occurrence, to which the same invariant applies.

The theorem is conditional integrity of disposition history. It does not imply
cooperation, obedience, truth, objective normative adequacy, service,
competence, learning, authorship/non-capture, corrigibility, or enforcement.

## 6. Exact unification claim

The common claim is not that social commitments are internal commitments. Singh
explicitly rejects a definitional reduction of social to internal commitment.
The common claim is:

> Given a standing liability occurrence, the account law for transforming it is
> invariant under coherent substitution of the parties occupying its roles.

The account checker is equivariant when respondent/actor labels, role-sensitive
event semantics, and authorization relations are renamed together. A temporal
successor, person, office, institution, or delegated agent may occupy the generic
respondent role. Renaming only the labels while leaving authority or semantics
fixed is an unauthorized role change, not an isomorphism.

What is common:

- occurrence identity, undertaken basis, per-input lineage;
- valid typed disposition and semantic anti-laundering;
- proof composition and basis-loss review.

What differs:

- **interpersonal standing:** debtor, creditor, `G`, powers/policies, evidence
  access, and consequential contest;
- **diachronic standing:** persistent constitutional/reasoner record and its
  self-revision/admission process, with no fake past-self creditor.

Thus the wrappers differ and the account law does not.

## 7. Minimal Singh-informed interpersonal wrapper

```
SocialCommitment(id, debtor, creditor, G, p, meaningReceipt)
ContextState(G,t)
effectiveOperation(state, actor, operation, commitment, args)
evidenceAccess(state, creditor, accountRecord)
contest(state, creditor, challenge) -> state x result
```

No separate `claimant`, `holdsStanding`, `mayDispose`, `mayTransfer`, `audience`,
or free-floating `meaningVersion` is required:

- the live commitment and creditor field supply the directed claim;
- typed effective operations derived from policy/power replace disposal and
  transfer predicates;
- noncreditor auditors/representatives are optional context policies, not a
  universal occurrence field;
- the meaning receipt belongs to the immutable occurrence;
- evidence access and consequential contest remain explicit because Singh's
  four-place relation does not itself specify their transition semantics.

`respondent` and `debtor` are not synonyms: respondent is the generic account
role; debtor is its social-commitment instantiation. Likewise `standing context`
is generic; `G` is Singh's social instantiation.

## 8. Singh source-boundary audit

Source: Munindar P. Singh, “An Ontology for Commitments in Multiagent Systems:
Toward a Unification of Normative Concepts,” *Artificial Intelligence and Law*
7 (1999), 97–113. The local PDF was read in full for this audit.

### Source-backed

| Memo use | Paper support and qualification |
|---|---|
| `C(x,y,G,p)` | Definition 1: debtor `x`, creditor `y`, context group `G`, discharge condition `p`; the paper neglects temporal aspects and states constraints rather than formal semantics |
| named commitments | section 2 treats commitments as first-class abstract objects with names, enabling self/cross-reference |
| creditor versus beneficiary | section 2.1 says creditor need not be the direct beneficiary, although the paper then assumes they can be treated alike for its practical purposes |
| role of `G` | section 2.1: group containing participants, relevant social norms/conventions, and a court of appeals for debtor/creditor disputes |
| semantics/pragmatics and objectivity | assumptions A7–A8 and section 2: semantics differs from use; conditions are evaluated in the world, though they may explicitly mention mental states |
| six operations | O1–O6: Create, Discharge, Cancel, Release, Delegate, Assign, with the effects summarized in section 4 above |
| operation actors | Release by creditor or context; Delegate by new debtor or context; Assign by present creditor if authorized or context; `cancel(x,c)` presupposes debtor `x`, with cancellation subject to policy |
| social policies | section 3.2: conditional expressions involving commitments and operations, applicable to each operation |
| higher-order commitments | sections 3.2–3.3: policies have orders; normative policies can themselves be commitments, while policies need not all be norms |
| explicit/implicit | section 3.1.1: explicit commitments are represented by one or more agents; implicit commitments are not and function as unarticulated interaction habits |
| Hohfeldian mapping | section 4.2 maps claim to directed commitment, power to a context commitment to effect a requested legal-relation change, and immunity to absence of the corresponding power |
| no formal model semantics | section 2.1 says semantics is not formally defined; the conclusion leaves model-theoretic semantics for future work |
| social/internal irreducibility | assumption A3 says the relationship cannot be definitional; the conclusion rejects reduction to mental concepts such as mutual belief |

### Our extrapolation, not attributed to Singh

- immutable occurrence identities through arbitrary transformation histories;
- account DAGs, resource rewrites, and per-old-input lineage;
- prefix-safety languages, derivatives, and per-input semantic transport;
- undertaken reason certificates and dependency receipts;
- context-indexed basis-loss review;
- a local-to-global answerability-conservation theorem;
- evidence-access and consequential-contest interfaces;
- pinned lifecycle receipts, retained secondary liability, and the diachronic
  self-revision instantiation.

The cautious local novelty claim is only:

> Singh (1999) supplies the relational social object and lifecycle vocabulary.
> This workspace develops a proof-relevant, reason-sensitive account of the
> diachronic transformation history of standing liabilities.

Nothing here claims that these additions are absent from the broader commitment
literature.

## 9. Executable witnesses

The finite suite retains the original attacks: legitimate diachronic reversal,
silent deletion, invisible certificates, successful/failed challenge, private
standing disagreement, semantic laundering, authorized/unauthorized delegation,
shared responses with distinct old identities, mutuality, role-equivariance,
and separations from authorship and cooperation.

Lifecycle-specific witnesses now establish:

| Case | Verdict |
|---|---|
| performance Discharge | accepted only with the substantive condition event and `Performance` proof |
| authorized Release | same empty frontier as Discharge, but distinct `Release` proof |
| authorized Cancel | accepted with matching cancellation policy and versioned proof |
| silent deletion | rejected for missing input lineage/disposition |
| authorized Delegate | accepted with debtor change, typed policy, and transport |
| unauthorized Delegate | rejected even when trace transport happens to pass |
| Assign | accepted as creditor change, not confused with Delegate |
| later basis loss | Release, Cancel, and Delegate historical uses each create an operation-linked review docket entry |
| permission versus power | ability to utter “cancel” does not alter the relation without an effective operation policy |
| current rule versus pinned old lifecycle | a `v1` self-release policy cannot operate on a `v0` occurrence without explicit migration |

Most importantly, `frontier(history1) = frontier(history2)` does not imply equal
accounts. Discharge and Release both end with no live successor, yet their typed
disposition proofs differ. History is proof-relevant.

Run:

```sh
python3 projects/normativity/legitimacy/rounds/2026-08-22-role-parametric-answerability/tests/run.py
```

## 10. Theorem/counterexample matrix

| Candidate | Status | Minimal reason |
|---|---|---|
| One account law covers diachronic and interpersonal roles | **survives** | coherent role relabeling preserves the checker; wrappers remain distinct |
| Social commitments reduce to internal commitments | **false / rejected** | unnecessary for the theorem and contrary to Singh A3 |
| Creditor is a common account primitive | **false** | claimantless constitutional account passes |
| Creditor is constitutive of Singh social commitment | **true by type** | Definition 1; creditor still differs from beneficiary/audience |
| Current context rules plus substantive content determine old meaning | **false** | two-version unilateral-self-release counterexample |
| Pinned content + lifecycle receipt can derive answer semantics | **provisional yes** | blocks retroactive widening; needs a formal compiler theorem |
| Authorized implies valid disposition | **false** | authority alone omits lifecycle applicability/effect/evidence |
| Typed lifecycle operation compiles to generic account | **yes provisionally** | six operations use fresh, closure, or transform shapes |
| Same live frontier means same answer | **false** | Discharge and Release both `1 -> 0`, with different proofs |
| Global strength can compensate for one dropped input | **false** | existing two-parent laundering witness |
| Successful challenge equals diachronic defeater | **only after recognition** | both induce the same standing true-to-false basis edge |
| Answerability implies cooperation or authorship | **false** | certified refusal and hidden-policy witnesses |

## 11. Boundaries and downstream interfaces

The two boxes feed, but do not contain:

- **environmental adequacy:** whether the standing/lifecycle semantics tracks the
  world or justified norms;
- **service and learning:** liveness/performance beyond safe disposition;
- **authorship/non-capture:** coupled-run reason/control factorization;
- **enforcement:** joint current semantics must still compile to a nonempty
  closed convex credal set before price projection and traderization;
- **corrigibility/deference:** effective corrective authority, competence, and
  control are not consequences of account-safe delegation.

The procedural gate should enforce certified operation and valid disposition.
Only current credal constraints satisfying the existing compiler interface should
flow to `C_t -> K_t ->` traderized enforcement.

## 12. Freeze decision and next questions

1. **Remaining counterexample to two boxes?** None in the current workspace or
   finite attacks. The lifecycle-version counterexample required the pinned
   receipt repair; after that repair it no longer breaks the architecture.
2. **Lifecycle semantics clear enough to target formalization?** Yes as an
   interface: substantive demand, pinned lifecycle version, effective operation,
   typed effect/evidence, and per-input soundness. No particular full compiler is
   proved here.
3. **Kernel stable enough to move outward?** Yes provisionally. Further redesign
   should require a counterexample to `ValidDisposition` plus input-scoped
   conservation, not merely a new social operation name.
4. **Top three open mathematical questions:**
   1. construct and prove sound a formal lifecycle/disposition compiler,
      including policy migration, suspension, secondary liability, and review;
   2. characterize when the joint current answer semantics compiles to a
      nonempty closed convex credal constraint without projection loss;
   3. compose single-run answerability with counterfactual authorship/non-capture
      and effective delegation/corrective authority without conflating them.

The next source checks remain Herrestad–Krogh (1995) on directed obligation,
Hohfeld (1919) on operative power, and Singh (1997) on operational commitments.
They are future inputs to the standing/lifecycle formalization, not blockers to
freezing this research-round interface.

## What is not established

No claim is registered or kernel-checked. The finite languages are tiny. This
memo does not construct a morally legitimate context, an objective semantic
oracle, a complete challenge institution, a lifecycle compiler, cryptographic
evidence access, strategic adjudication, bargaining, competence, cooperation,
learning, enforcement, non-capture, or corrective control. It establishes a
small conditional account interface and its present boundary—not a completed
legitimacy theory.
