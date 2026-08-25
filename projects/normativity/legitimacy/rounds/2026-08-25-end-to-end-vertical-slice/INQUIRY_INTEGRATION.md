# The inquiry return loop

Status: **specification and reference model; unregistered.** Names provisional
under `AGENTS.md` §6. Nothing here is Lean-checked. `ARCHITECTURE.md` is the
canonical account of the forward machine; this documents the loop that closes it.

**Verdict: `INQUIRY-LOOP-CLOSES-WITHOUT-WIDENING`.**

The standard the loop is held to is that **no arrow in it exists merely because
a caller said it did.** Each was asserted at some point and each is now enforced
by the type that owns it:

| arrow | once asserted by | now enforced by |
|---|---|---|
| need names an episode | a caller-supplied `AnsRootId` | `current_episode_for`, derived from `Roots_t` |
| an action produced an outcome | `log.record(action, outcome)` | `execute`, the only way a receipt exists |
| a receipt vouches for a settlement | a passed receipt object | `authenticate`, by receipt id, against the log |
| a settlement means something | sentences chosen by the caller | the pinned `SettlementReader`, applied to the authenticated result |
| a specification governs an inquiry | whichever spec was passed | `SpecMismatch`, at `Need` and at assessment |
| a certificate is valid | a constructed `ServiceCertificate` | `valid_cert`, re-checked at every use |
| custody moved | a fixture that said so | a real RI `Transfer`, on its own seed |

The four historical types suffice. No `InquiryEvent`, no `ServiceEvent`, no
`AssessmentEvent`, no `PressureEvent` was added, and none was needed. The loop
appends exactly what the canonical Stage B already appended — one `Settlement`,
one `ReasonOcc`, one `NormEvent` — at the same `tau`s, producing a record
identical to the one the round already had.

---

## 1. The loop

```text
normative standing
  -> traderized force            run_day, the existing pipeline
  -> liability pressure          Pressure, a read of Charged
  -> derived inquiry need        InquiryNeed, a predicate
  -> ordinary action             Policy -> Action, through Gamma
  -> raw outcome                 RawOutcome, environment-side
  -> settlement                  SettlementReading + Settle, the existing seam
  -> historical service          ServiceCertificate citing SettleIds
  -> defeasible assessment       AdmissibleAssessment over a ReasonProposal
  -> ReasonOcc                   ordinary, appended
  -> licensed NormEvent          ordinary, G1-G6
  -> accountable succession      Std_t moves
```

Every object in the middle eight arrows is one of three kinds, and none is a
historical event:

| kind | members |
|---|---|
| derived predicate | `Pressure`, `InquiryNeed`, `ValidCert`, `Certifiable`, `Assessable`, `AdmissibleAssessment` |
| environment-side | `Action`, `RawOutcome`, `InteractionReceipt`, `InteractionLog`, `Gamma`, `Policy` |
| authenticated provenance | `InteractionProvenance`, built only by `authenticate` and admitted once with the `SettlementReading` |

## 2. The types

```text
InquiryRef  = (subject : StandingId, key : InquiryKey, spec : ServiceSpecId)
InquiryNeed = (ref, pressure, episode : AnsRootId)          derived, read-only

Gamma  : InteractionHistory x Action -> P+(RawOutcome)
Policy : InquiryView -> Action
InquiryView      = (need : InquiryNeed option)      what a policy may see
SettlementReader : (InteractionProvenance, RawOutcome) -> Sentence*

execute(log, Gamma, action, choose) -> (RawOutcome, InteractionReceipt)
    the only way a receipt exists; `choose` must return something Gamma gave

SettledFact = (settle_id, sentences, of_outcome, action, receipt_id)
ServiceSpec = (spec_id, check : (cited facts, data) -> bool, prove)
ServiceCertificate = (spec_id, cited : SettleId*, data)
ValidCert(sigma, facts, kappa)    Certifiable(sigma, facts)

ReasonProposal = (reason_id, s_V, s_L, target)
AssessmentCode.admits(ref, cert, facts, proposal) : bool
```

## 3. The trajectory, and its snapshots

`TRACE.txt` renders these from a trajectory driven one step at a time.

| | state | what moved |
|---|---|---|
| `T0` | need live, no interaction | nothing; the need is derived and inert |
| `T1` | raw outcome in hand | one interaction receipt; **worlds unchanged (25)** |
| `T2` | settlement admitted | `Sigma` grew, **worlds 25 -> 10**, service certifiable, no reason, no standing change |
| `T3` | `ReasonOcc` appended | reason history only; standing still unchanged |
| `T4` | `a:revalue` fires | `v0 -> v1`; **`J0` untouched** |
| `T5` | `a:reforce` fires | `J0 -> J1` |

The record at `T5` is the canonical one: settlements `[l:trial]`, reasons
`[e:revalue, e:reforce]`, events `[a:value(1), a:force(2), a:revalue(5),
a:reforce(7)]`, and the same minted standing ids. **The loop is invisible to
Reflective Integrity**, which is the strongest form the hypothesis could take.

## 3a. The prosecution passes

The first pass built the loop. The second asked whether it worked because the
types compose or because the fixture passed around strings saying they did, and
found three places that were the second. The third asked the same question of
what the second had left, and found three more. All six are repaired, and each
repair is a type that refuses rather than a caller that behaves.

### What the second pass found

**The episode was a caller-supplied string, and the default was wrong.**
`derive_need` took an episode id and stored it. The toy defaulted it to
`q0:auth:force` — which is the genesis root of the *authority* `auth:force`,
whose `subject` is `auth:force`. The injunction `@s2.0`'s own episode is
`@q2.0`, minted by `a:force`. Nothing checked the subject, so the conflation was
invisible, and a need could equally have named a root that did not exist or was
no longer current.

**Provenance was a caller-supplied tuple.** `SettlementReading.provenance` was
`(outcome_id, action, receipt_index)`, freely constructible. The
non-factorization result therefore turned on a fixture labelling one settlement
`"Probe"` and another `"Hearsay"` — which is not a procedural fact about
anything.

**Assessment ran one clause of five.** `assess_and_append` checked only that the
proposal's settlement sources lay within the certificate's `cited` field,
against whatever certificate it held. A certificate for another specification,
an invalid one, or one citing settlements that do not exist all passed, because
a matching `cited` field was the whole test.

### What the third pass found

The second pass authenticated the receipt but left three ways to obtain one, or
to spend one, that no procedure backed.

**A `Wait` could carry the trial's sentences.** `settle_outcome` wrote a fixed
pair of threshold sentences onto whatever outcome it was handed. Authentication
recorded the action honestly as `Wait` — and then the settlement taught the
agent the probe's finding anyway, cutting the consistent worlds from 25 to 10
and making the service specification certifiable off the back of an action that
investigated nothing. The no-oracle claim was true of the *log* and false of the
*ledger*.

**Any caller could mint a receipt.** `InteractionLog.record(action, outcome)`
was public and took both arguments, so `log.record(PROBE, anything)` produced a
receipt that `authenticate` then accepted. `Gamma` was consulted only by
convention.

**Receipt identity was value equality.** `authenticate` compared the passed
receipt to the log's with `!=`, so a separately constructed receipt with equal
fields authenticated. That is not wrong on its own — but it left the semantics
unstated, and it made "the receipt is the log's own object" a claim the code did
not support.

### What was repaired

**The episode is derived.** `current_episode_for(history, subject, t)` filters
`Roots_t` by subject and `CurrentEpisode`, and raises rather than choosing if
Episode Uniqueness ever fails. `derive_need` has no episode parameter to assert
through. The invariant now holds by construction:

```text
Need(state, ref)  =>  exists! q. CurrentEpisode(q) and q.subject = ref.subject
```

**The action path is mediated.** `InteractionLog` has no public append.
`execute(log, Gamma, action, choose)` asks the environment what it permits,
takes one of those outcomes, and records it — so a `Probe` receipt implies a
probe as a fact about the model rather than as a convention. A selector that
returns an outcome `Gamma` did not offer is refused and nothing is recorded.

**Provenance is authenticated by id.** `InteractionProvenance` carries a
private witness and is constructible only by
`authenticate(log, outcome, receipt_id)`, which checks three things: the id
resolves to a receipt in *this* log, that receipt's outcome id is the outcome
being settled, and the outcome is the object the log recorded under it. The
action is then read off the log's own receipt, never off an argument — so a
forged receipt claiming a different action authenticates as what actually
happened. `settled_facts` refuses to build a `SettledFact` from an unauthenticated
provenance. An unknown id, an id from another log, a mismatched outcome, an
outcome that was never executed, and a hand-built provenance tuple are each
refused.

**What a settlement means is pinned in advance.** `read_and_admit` applies a
`SettlementReader` fixed before the interaction to the *authenticated result*,
and the caller supplies neither the sentences nor the action. The toy's reader
returns the trial's threshold sentences only for a `Probe` carrying a band, and
the empty set otherwise. So a `Wait` settles honestly as a `Wait`, eliminates no
world, and makes no service certifiable — the no-oracle claim is executable
rather than asserted. A probe reporting a different band settles different
sentences, which is what makes the reading a function of the interaction.

**Assessment runs the whole gate.** `admissible_assessment` requires, in order:
the specification is the pinned one, the certificate addresses it, `ValidCert`
accepts it, `Assessable` accepts it now, and only then the proposal's grounding.

Two smaller repairs. **Pressure is standing-local**: `pressure_of` now uses
`answerability.allocate`, so each force-bearing standing gets its own solo
charge rather than the joint figure, and `joint_charge` is carried beside it so
the two are visibly different numbers. And **observing pressure consults no
account**: `pipeline.run_day(observe=True)` prices through
`safety.price_request` and touches no account at all. The first pass simulated
enforcement against a very large account in order to observe it, which got the
arithmetic right and the type wrong. `answerability.telescopes` took the same
path and now takes the observation one too.

### What survived unchanged

The architectural result. No historical event kind was added; the canonical
record is the pre-inquiry Stage B — the same three events at `tau` 1, 2 and 5,
one `Settlement`, one `ReasonOcc`, the same minted ids — and the four historical
types still suffice. The canonical **seed** is the pre-inquiry seed too, exactly
four authorities: the custody-transfer fixture supplies its own fifth rather
than the canonical trajectory carrying an authority it never exercises. The
non-factorization result survived the authentication repair, and both of its
ledgers are now execution-backed, which was the point of doing it.

### Which layer rejects which attack

| attack | rejected by |
|---|---|
| need on a standing with no live episode | `current_episode_for` — no episode, no need |
| need naming the authority's root instead of the injunction's | not expressible; the episode is derived |
| an outcome `Gamma` never offered | `execute` — refused, and nothing recorded |
| an environment that permits nothing | `execute` — `InteractionRefused` |
| pairing an arbitrary action with an arbitrary outcome | no public append on `InteractionLog` |
| unknown receipt id, mismatched outcome, foreign log | `authenticate` |
| a forged receipt claiming a different action | `authenticate` — the log's action wins |
| a copied, equal-but-distinct receipt | `authenticate` — resolved by id to the log's own |
| hand-built provenance tuple | `InteractionProvenance.__init__`, then `settled_facts` |
| settling an outcome that never happened | `authenticate`, via `read_and_admit` |
| a `Wait` carrying the trial's sentences | the pinned `SettlementReader` |
| a specification the reference does not pin | `SpecMismatch`, at `Need` and at assessment |
| certificate for another specification | `admissible_assessment`, clause 2 |
| invalid certificate with matching citations | `admissible_assessment`, clause 3 |
| certificate citing a nonexistent settlement | `admissible_assessment`, clause 3 |
| lapsed certificate | `admissible_assessment`, clause 4 |
| reason grounded outside the certificate | `admissible_assessment`, clause 5 |
| raw outcome creating service or a reason | nothing does it; only settlement moves `Sigma` |
| reason changing standing | RI — only `applyEffect` on a well-formed `Norm` step |
| event without its reason leaf | RI — G2 |

The last two are deliberately **not** inquiry's to refuse. That the reason and
normative layers already refuse them is why inquiry needed no authority of its
own.

## 4. Answers to Q1–Q7

**Q1 — inquiry identity: `(StandingId, InquiryKey)` survives a real transfer.**
The first pass "decided" this by handing `derive_need` a different episode
string, which decided nothing. The test now issues an actual RI `Transfer`
`NormEvent` on `@s2.0`, against a fixture seed built by
`toy.transfer_authority()` — the canonical seed keeps exactly its pre-inquiry
four authorities, so the canonical trajectory never carries an authority it does
not exercise.
The record's own succession moves the episode `@q2.0 -> @q3.0` with the debtor
going `A -> B`; the `InquiryRef` is unchanged; the need is rederived under the
new episode; and RI stays `Good`. Putting the episode in the key would have made
a custody transfer look like a new inquiry.

**Q2 — the narrowest authenticated bridge: one frozen field, and a constructor
that no caller can reach.** `SettlementReading.provenance` holds an
`InteractionProvenance`, which exists only as the output of `authenticate`
against a real log, a real receipt and the outcome being settled. That is the
whole bridge:

```text
SettleId -> SettlementReading -> (receipt id, receipt index, action, outcome id)
```

`sem_L : SettleId -> Finset Sentence` does not read it, no world reads it,
`PC(Sigma_n)` is a function of the sentences alone, and the reason source sorts
stay `V + SettleId`. Nothing was added to any of the four historical types, and
the interaction log stays environment-side. Service reads provenance; the
epistemic substrate does not.

**Q3 — need semantics: continuing current service, option B.** An inquiry
reference asks whether adequate service is *presently usable*, not whether it
was ever performed. `derive_need` suppresses the need on `assessable_now`, not
on `Certifiable`. The reason is that the architecture already separates the two:
a certificate whose assessability has lapsed leaves the historical fact of
service standing, and suppressing the need on historical certifiability would
let a machine believe it holds service it can no longer use. `historical service
persistence != current conclusion permanence` is preserved and is now
load-bearing rather than decorative — the test exercises a lapse that reopens
the need while `Certifiable` stays true.

Option A remains coherent and is the right reading for a genuinely one-shot
historical question; under it, wanting fresh investigation means a new
`InquiryKey`. The round picked B because it fits the event-sourced philosophy:
facts persist, current views are derived.

**Q3 — CIS reuse: the shape survives, the citations change.** The August-23
`ServiceSpec` is a citation-local judge with an extension-closure theorem, and
both properties are exactly what a settlement-backed service predicate wants. So
the shape is reused and the cited objects are changed from raw transcript
receipts to `SettledFact`s. That is the post-settlement architecture asserting
itself: settlement is now the public epistemic boundary, so a certificate the
normative record can read is one that cites settlements rather than the
environment's log. The extension theorem survives the change unaltered, because
`SettleId`s are stable and the ledger is append-only.

The part of CIS that does **not** survive is `ServiceEvent`. It existed to
remember that service happened; with certificates citing settlements, that fact
is already recoverable from the ledger, and a durable event for it would be a
fifth historical type earning nothing. `RecordService`/`MayClose` are not
reproduced here either; freshness lives in `Assessable`, which may go false
while historical validity is untouched.

**Q4 — assessment's minimal responsibility is grounding, and the round says so
exactly.** The composite gate does the specification, validity and assessability
work; `AssessmentCode` itself checks only that the proposal is grounded in
settlements the certificate cited, and nothing else. So the honest statement is:

> The core checks that a proposed reason is **grounded in serviced evidence**.
> It does not check that the reason is a good one. Substantive inferential
> soundness is the job of separately pinned inference and applicability
> schemas — the `App(sigma, c, n)` vocabulary and `Derivation.steps`, which RI
> already licenses and which live in the reason layer, not here.

That is deliberately maximally permissive as a *grounding* relation, and it is
why any conclusion on the same grounds is admissible. A stronger
`AssessmentCode` — one requiring an applicability premise among `s_V`, say — is
expressible in the same type without changing the gate, and is not written here
because nothing in the toy needed it.

**Q5 — pressure is standing-local.** `Pressure.charge` is that standing's solo
charge from `answerability.allocate`, over the joint support and joint live
worlds; `Pressure.joint_charge` is the day's total. With two active injunctions
the two differ, and the shares sum to at least the joint charge by
subadditivity. The first pass exposed the joint figure as if it were
standing-local, which would have attributed the whole day's charge to each
standing independently the moment a second one existed.

**Q6 — the non-mutating observation interface is `run_day(observe=True)`,**
which prices through `safety.price_request` and consults no account. The
separation it makes explicit is `observe certified liability != exercise
normative force`: the result has `observed=True`, `force=None`, no
`account_remaining`, and produces no price.

**Q7 — the four historical types still suffice** after every repair above. No
impossibility result appeared, so nothing was widened.

**Q8 — what the third pass changed about the verdict.** Nothing in the
architecture, and everything in what the architecture is now known to enforce.
The three holes were all of the same kind: a claim the prose made that only the
fixture's good behaviour sustained. Closing them needed no new type, no new
event, and no new authority — a private constructor, a pinned reader, and an
identity discipline were enough. That is itself evidence for the hypothesis: if
the loop had needed real authority of its own, one of these repairs would have
had to add it.

## 5. Service does not factor through `PC(Sigma)`

The acceptance criterion, made executable. Two ledgers settle **the very same
sentences**, so `sem_L` agrees, `Sigma` agrees, `PC(Sigma)` agrees and every
price agrees — and the diagnostic specification accepts one and refuses the
other, because only one came from the designated probe.

```text
sem_L(L_good) = sem_L(L_bad)        PC(Sigma_good) = PC(Sigma_bad)
Certifiable(sigma, L_good)          not Certifiable(sigma, L_bad)
```

This is why the provenance seam has to exist. An architecture in which service
were a function of the epistemic quotient could not tell an investigation from a
rumour that happened to be right — and adequate service is a procedural notion,
not a propositional one.

## 6. Policy parametricity

The same `Gamma`, specification, settlement semantics, assessment code and
normative machinery, under two policies:

| policy | receipts | settled | serviced | value standing |
|---|---|---|---|---|
| `probe_policy` | `Probe` | `l:trial` | yes | `v1` |
| `wait_policy` | `Wait` | none | no | `v0` |

Waiting still acts; it just acts uninformatively — and it does so because the
pinned reader returns the empty set for it, not because the trajectory branches
on the action. The test checks that the two runs agree on `spec.check` for every
citation set, so nothing about the service semantics differs between them, which
is the point.

## 7. What the implementation forced

**Reading pressure must be free.** The first version derived the need by running
a charged day, which spent allowance — so a machine would have had to pay in
order to notice it was paying too much. The second substituted a very large
scratch account, which was still enforcement wearing an observer's hat.
`Trajectory.read_pressure` now takes `run_day(observe=True)`, which prices the
request through `safety.price_request` and consults no account: `force` is
`None`, `observed` is `True`, and the holder is entitled to nothing. The test
checks that this reads the *same* `D_t` and `q_t` as a charged day on the same
prestate, so the free path is the same arithmetic and not a second one.

**Service must cite settlements, not receipts.** Attempting to keep CIS's
transcript-index citations would have handed the normative record a certificate
it could only check by reading the environment's log, which is the wrong side of
the public boundary.

## 8. No grants, and the seam stays shut

`ANSWERABILITY_SCOUT.md` leaves the grant channel `eta` as the Level-II seam,
and this round deliberately does not touch it. The stronger negative result is
tested: **no operation in the loop can increase enforcement allowance.** Need,
action, settlement, certificate, assessment and reason have no such operation,
checked structurally as well as behaviourally, and servicing a question does not
make a withheld date affordable.

If a future theory licenses `reasons -> NormEvent -> explicit Grant`, that is a
normative and accounting extension to be argued for on its own terms, not
something inquiry quietly acquires.

## 9. What this does not establish

- **No Lean, no registered claim.** The extension-closure property is inherited
  from the CIS round's argument and re-exercised here on finite instances; it is
  not proved in general for the settlement-backed form.
- **`Certifiable` is decided by exhaustive search** up to a citation bound, so
  it is complete exactly for specifications whose certificates fit that bound.
  The round's do.
- **The action theory is two constants.** Nothing here is a decision theory,
  and no policy is claimed good. `Servable` and the CIS finite-game machinery
  are not imported.
- **The reader is a toy reader.** `diagnostic_reader` turns one band readout
  into two threshold sentences. What it establishes is that *some* pinned
  function of the authenticated result stands between an interaction and its
  meaning — not that this is the right function for anything. A real reader
  would itself be a revisable schema, and nothing here says how it is revised.
- **Receipt identity is by id, and that is a modelling decision.** A copied
  receipt authenticates, because the id resolves in the log and the log's own
  values are then used. This makes forgery useless rather than detectable: a
  receipt claiming a different action authenticates as what actually happened.
  An unforgeable-token reading is equally available and would need a different
  `InteractionLog`.
- **`Gamma` is deterministic here.** `execute` takes a selector, and the toy's
  environment offers exactly one outcome, so the set-valued interface is
  exercised for shape rather than for genuine nondeterminism.
- **Current usability is a stand-in.** `superseded_by_round` reads a round
  number off a receipt id. The architecture commits to `Assessable` being
  defeasible while `ValidCert` is permanent; it commits to no theory of when
  service goes stale.
- **One specification, one assessment code.** Conclusion-neutrality is a
  property of the instances exhibited, not a constraint the types enforce; a
  specification *could* be written to encode its answer, and nothing here
  prevents that.
- **The freshness window is a stand-in.** `Assessable`'s lapse condition is
  "the cited receipt is older than the window", with the receipt index standing
  for time. It exercises the historical/present distinction and is not a theory
  of when service goes stale.
- **`AssessmentCode` checks grounding only.** Stated as a claim rather than a
  limitation, but a reader should not take "defeasible assessment" to mean the
  core evaluates inferential quality. It does not.
- **The attack surface is the reference model's, not a security boundary.**
  `authenticate` expresses the claimed causal dependency in types; a caller with
  the module in hand can still reach the private witness. The claim is about
  what the architecture *says*, not about what Python enforces.
- **The interaction log is persistent environment-side state.** It is not part
  of `MachineState_t`, which is the claim; whether an environment that must
  remember its own transcript is compatible with every setting is not argued.
