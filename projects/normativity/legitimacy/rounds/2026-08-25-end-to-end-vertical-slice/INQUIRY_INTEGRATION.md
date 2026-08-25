# The inquiry return loop

Status: **specification and reference model; unregistered.** Names provisional
under `AGENTS.md` §6. Nothing here is Lean-checked. `ARCHITECTURE.md` is the
canonical account of the forward machine; this documents the loop that closes it.

**Verdict: `INQUIRY-LOOP-CLOSES-WITHOUT-WIDENING`.**

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
| frozen provenance | the receipt carried on `SettlementReading`, admitted once with it |

## 2. The types

```text
InquiryRef  = (subject : StandingId, key : InquiryKey, spec : ServiceSpecId)
InquiryNeed = (ref, pressure, episode : AnsRootId)          derived, read-only

Gamma  : InteractionHistory x Action -> P+(RawOutcome)
Policy : MachineView -> Action

SettledFact = (settle_id, sentences, of_outcome, action, receipt_index)
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

## 4. Answers to Q1–Q4

**Q1 — inquiry identity: `(StandingId, InquiryKey)`, with the episode supplied
separately.** The matter under inquiry is a property of the standing; which
episode currently carries it is custody information. The case that decides it is
in `test_inquiry.py`: handing `derive_need` a different current episode leaves
the reference identical, so an inquiry does not lose its identity when custody
moves. Putting the episode in the key would have made a transfer look like a new
inquiry.

**Q2 — the provenance seam: one frozen field on `SettlementReading`.** It
already carried `of_outcome`; it now also carries `(outcome_id, action,
receipt_index)`, frozen at admission. That is the whole bridge:

```text
SettleId -> SettlementReading -> (outcome id, action, receipt index)
```

`sem_L : SettleId -> Finset Sentence` does not read it, no world reads it,
`PC(Sigma_n)` is a function of the sentences alone, and the reason source sorts
stay `V + SettleId`. Nothing was added to any of the four historical types, and
the interaction log stays environment-side. Service reads provenance; the
epistemic substrate does not.

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

**Q4 — assessment thinness: yes, a checker suffices.** `AdmissibleAssessment` is
a predicate over a proposed `ReasonOcc`; no hidden inference or update machinery
appeared. The round's instance is two citation-local conditions — the proposal's
settlement sources are non-empty and lie within what the certificate cited — and
it is conclusion-neutral: a proposal for the opposite target on the same grounds
is equally admissible. There is deliberately no `assess : certificate ->
conclusion`, because the same adequate investigation can bear several ways.

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

Waiting still acts; it just acts uninformatively. Nothing about the service
semantics differs between the two runs, which is the point.

## 7. What the implementation forced

**Reading pressure must be free.** The first version derived the need by running
a charged day, which spent allowance — so a machine would have had to pay in
order to notice it was paying too much. `Trajectory.read_pressure` now runs
against a scratch account and returns the result as a view. This is a small
thing that only appeared under test, and it is the shape the architecture
wanted: the account is drawn down by force actually emitted, never by looking.

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
- **One specification, one assessment code.** Conclusion-neutrality is a
  property of the instances exhibited, not a constraint the types enforce; a
  specification *could* be written to encode its answer, and nothing here
  prevents that.
- **`Assessable` has a freshness parameter that nothing in the toy exercises.**
  It exists to hold the historical/present distinction open, and the lapse case
  is untested.
- **The interaction log is persistent environment-side state.** It is not part
  of `MachineState_t`, which is the claim; whether an environment that must
  remember its own transcript is compatible with every setting is not argued.
