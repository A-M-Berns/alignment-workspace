# The answerability ledger

## 0. Verdict

`LG-X1` refuted the unresolved-burden Boolean: two owed answers may merge onto
one occurrence and be closed by one terminal record.  The obvious correction —
*one witness answers one obligation* — is also wrong.  A single proof, decision,
or evidential record may legitimately answer several questions, and a system that
forbids this is safe only by being unable to say something true.

The invariant is neither, and it is the whole content of this phase:

> Every open obligation has its own identity and receives an explicit, authorized
> disposition.  A single response may discharge several obligations **only when
> its adequacy for each is separately represented.**

Bounded comparison of the three systems (§7) confirms both halves: the Boolean
system accepts `24` unsafe closures, the rivalrous system accepts `0` but also
rejects every one of the `8` legitimate shared responses, and certified coverage
accepts all `8` while still accepting `0` unsafe closures.

Nothing in `src/migration.py` or `StandingTransportPlan` is changed.  `CM-J5`
and `LG-J5` are unchanged.

## 1. Why the ledger is separate from the ontology

Two architectures were compared.

**Candidate A** attaches a finite set of obligation identifiers to each
occurrence.  **Candidate B** makes each obligation an independent ledger entry
pointing at its current carrier.

Candidate B is adopted, for three reasons that are failures rather than tastes.

1. **Obligation identity must not coincide with claim identity.**  Under A, two
   obligations on one occurrence are a set attached to that occurrence, so the
   occurrence's identity is doing the individuating work.  When the occurrence
   merges, nothing distinguishes "these are two questions here" from "this is one
   question here".  That is `LG-X1` re-entering through the representation.
2. **An obligation survives its carrier.**  When a target is retracted, lost, or
   becomes inexpressible, the obligation is still owed (§5, Example G).  Under A
   it would have nowhere to live.
3. **Migration retargets carriers without touching obligations.**  Under B a
   migration emits `Carry` events and the obligation identifiers are untouched,
   which is exactly the separation the phase is trying to express.

The ledger is a **demand record**.  It says what the learner owes an answer
to.  It does not select the answer, does not make a proposed answer
authoritative, does not choose an ontology, and does not endorse warrants.  It
may receive items from a query stream, an authorized challenge, an appeal, a live
contract, or an inconsistency the learner finds itself.  No thresholds,
deadlines, utilities, or scheduling appear, because no result below needs one.

## 2. The object

An **identified answerability obligation** is a record

```
Obligation(obligation_id, kind, origin_version, origin_event, basis, carrier, lineage)
```

Each field earns its place by a demonstrated failure:

| field | prevents |
|---|---|
| `obligation_id` | `LG-X1`: two owed answers conflated on one carrier |
| `origin_version`, `origin_event` | cross-version identifier collision (Gate 0.3) |
| `kind` | a response answering a different sort of question |
| `carrier` | nothing — it is *what a migration changes*, and must be mutable state |
| `basis` | unauthorized obligation creation |
| `lineage` | refinement and identification provenance |

Rejected candidate fields: a **satisfaction specification** on the entry (Gate 3
prefers adequacy parametric, so it lives on the coverage edge), and a
**terminal disposition** field (the closure is an event, so the log already
carries it).

**Status algebra.** Three statuses — `open`, `suspended`, `closed` — with the
closure *kind* (`discharge`, `withdrawal`, `loss`) carried by the disposition
record rather than by a fourth and fifth status.  Suspended is not closed: it is
still owed and still appears in `open_ids`.

**The log is append-only.**  The live ledger is a fold over it.  Nothing is ever
rewritten, which is what makes reopening (§5, Example F) coherent and makes
composition trivially associative (§6).

## 3. Coverage, not rivalrous witnesses

Let `D` be the ledger obligations and `R` the responses.  The answer relation is

\[
\mathsf{Answers}\subseteq R\times D ,
\]

realized as `Cover` events, each carrying its own `adequacy_ref` and
`authorization`.  A response may have several outgoing edges; **each must pass
separately**.

**A response is not a discharge.**  `Discharge` names a specific `Cover` event,
and the verifier checks that the named edge targets *that* obligation.  Filing a
response closes nothing.

**Adequacy is parametric.**  `verify_ledger` takes an `AdequacyOracle`; the
default checks only that a certificate was supplied and that the response kind
matches the obligation kind.  The theorem of §6 is stated for an arbitrary
oracle, so no substantive theory of what makes an argument good is baked in.
This is the point at which a later learning theory plugs in.

## 4. Dispositions under migration

Six dispositions, each an explicit event: **carry** (retarget), **refine**
(decompose, with a declared completion rule), **identify** (equivalence
certificate), **suspend**, **discharge** (via a coverage edge), and **terminal
disposition** (withdrawal or authorized loss).

**Concept merger is not obligation merger.**  An `Identify` event whose declared
grounds are `carrier-merger` is rejected outright with
`ledger.identification_by_carrier_merger`.

## 5. Examples and their verdicts

All seven are machine-checked; the verdicts below are computed from raw records.

| example | verdict |
|---|---|
| **A** two obligations merge onto one carrier, only `d_A` covered | accepted; `d_A` closed, **`d_B` stays open**; closing `d_B` with `d_A`'s edge gives `ledger.implicit_co_discharge` |
| **B** one response, two certified edges | accepted; both closed, **two** coverage edges, **two** distinct adequacy certificates, **two** disposition events |
| **C** identification grounded in carrier merger | rejected, `ledger.identification_by_carrier_merger` |
| **D** authorized identification of duplicate filings | accepted; two obligations, one shared adequacy argument, two edges, two dispositions |
| **E** refinement under an `all` rule, one child answered | rejected, `ledger.parent_discharged_early`; answering the second child closes the parent; under a declared `any` rule one child suffices |
| **F** discharge then undercutter | accepted; obligation open again, `reopened = 1`, the prior `Discharge` still in the log, and the prefix at the earlier version still shows it closed |
| **G** endpoint ontology cannot express the target | accepted; obligation **suspended on a legacy carrier**, still owed, not closed |

**Example D, design choice.** {#AD-J5}
**Status: PROVED (single derivation).** Identification need never merge
obligations.  Two designs were compared: *one obligation with two provenance
roots*, and *two obligations sharing one permitted disposition*.  The second is
adopted, and the first is unnecessary: an `Identify` certificate licenses one
adequacy argument to ground a coverage edge for each identified obligation, so
every filing keeps its own identity, its own coverage edge, and its own
disposition record.

**Proof.** Merger would replace two entries by one, destroying one origin record
and one disposition record; every use of merger is reproduced by `n` coverage
edges sharing an `adequacy_ref` and an `identification_ref`, which strictly
dominates it on auditability because the closure of each original filing remains
individually witnessed. `square`

The consequence is that **obligation merger is never required**, so the
theory has no operation that can destroy an objector's outstanding challenge by
identifying it with someone else's.

## 6. The composition theorem

Local transition conditions, each a property of one event and the state it acts
on — never of the global outcome:

- **(T1)** every `FileObligation` has a nonempty basis and a fresh identifier;
- **(T2)** at a declared migration boundary every open obligation is named by at
  least one authorized disposition event;
- **(T3)** every `Discharge` names a `Cover` event that exists, is authorized,
  passes the adequacy oracle, and targets *that* obligation;
- **(T4)** every `Cover` names an existing open obligation and an existing
  response;
- **(T5)** a refined parent closes only when its declared completion rule is met;
- **(T6)** every `Reopen` names an undercutter and an authorization;
- **(T7)** every `Identify` carries a certificate and grounds other than carrier
  merger.

**Ledger conservation.** {#AD-J1}
**Status: PROVED (single derivation).** For any finite linear history whose
events satisfy (T1)–(T7):

1. *obligation-origin uniqueness* — identifiers are fresh, so each obligation has
   exactly one origin `(version, event)`;
2. *no silent discharge* — an obligation is `closed` only at an event naming it;
3. *no implicit co-discharge* — an obligation is `discharged` only via a coverage
   edge whose target is that obligation;
4. *authorized shared responses* — a response may close several obligations, and
   does so only through one separately authorized and separately adequate edge
   per obligation;
5. *decomposition ancestry* — every child records its parent in its lineage, and
   the parent closes only under its declared rule;
6. *reopening without erasure* — `Reopen` appends, and every prefix fold
   reproduces the state as of that prefix;
7. *conservation* — no obligation disappears: at every version each is `open`,
   `suspended`, or `closed` with a named closure event.

**Proof.** The live ledger is a fold of an append-only log, and every state
transition in the fold is guarded by the condition on the event that causes it.
(1) is the freshness check in (T1).  (2) holds because `closed` is written only
in the `Discharge` and `Dispose` branches, both of which name their obligation.
(3) is the equality check `cover.obligation_id == event.obligation_id` in (T3).
(4) is (T3) plus the absence of any rule that closes a second obligation when one
closes.  (5) is (T5) together with the lineage written at `Refine`.  (6) holds
because folding is a function of the event prefix.  (7) holds because the three
statuses partition the state space and no branch deletes an entry. `square`

**Associativity.** {#AD-J4}
**Status: PROVED (single derivation).** Docket composition is concatenation of
logs, which is associative on the nose; the derived live and historical states
are functions of the concatenated log, hence equal under either bracketing.

**Proof.** `LedgerLog` under `+` is the free monoid on events; `verify_ledger` is
a function of the event sequence. `square`

This is a **stronger** associativity than `LG-J6`, which was machine-checked on
one three-step instance and only up to outcome-map equality.

### 6.1 What this does and does not settle

**It does not discharge `LG-J5`.**  `LG-J5` is a statement about the
burden-bit transport object in `src/history.py`; the ledger *replaces* that
object rather than repairing it.  `LG-J5` keeps its `PROVED-CONDITIONAL` status,
and `AD-J1` is a general theorem about a different object.  Claiming otherwise
would be exactly the substitution this project exists to catch.

**The ledger does not imply the prefix challenge-frontier condition.** {#AD-X3}
**Status: REFUTED (witness displayed).** A `Carry` event requires an
authorization and a new carrier; it does not require that the new carrier cover
the descendants of the old target.  A history can therefore conserve every
obligation while retargeting one onto an unrelated carrier, satisfying docket
conservation and violating frontier coverage.  The two conditions remain
**independently necessary**.

## 7. Three systems compared

| system | accepts | unsafe accepted | legitimate shared accepted |
|---|---|---|---|
| 1. Boolean burden bit | `92` | **`24`** | `8` |
| 2. one response, one obligation | `36` | `0` | **`0`** |
| 3. certified coverage | `68` | `0` | `8` |

**System comparison.** {#AD-E2}
**Status: MACHINE-CHECKED (stated finite scope).** Over `92` scenarios of at most
two obligations and two responses with every coverage subset and every discharge
subset: system 3 accepts strictly more than system 2 (`68` against `36`),
accepts every legitimate shared response that system 2 rejects, and accepts
exactly as few unsafe closures as system 2, namely none.

System 1 is modelled by the *absence* of the check — with no obligation identity
there is nothing to verify — which is faithful to `LG-X1`.

**Benchmark examples.** {#AD-E1}
**Status: MACHINE-CHECKED (stated finite scope).** The seven examples of §5
produce the verdicts displayed there, computed from raw records.

**Rivalrous witnesses are too strong.** {#AD-X2}
**Status: REFUTED (witness displayed).** System 2 rejects all `8` scenarios in
which one response carries two independently certified coverage edges.  Safety
purchased this way costs the ability to record a true fact: that one argument
settled two questions.

## 8. Interface analysis

**Demand, generation, authorization, and force stay separate.**

| stage | object | what it does |
|---|---|---|
| demand | `Obligation` | says an answer is owed |
| generation | `Response` | proposes an answer; closes nothing |
| authorization | `Cover` with adequacy and authorization | admits the response as an answer to *this* obligation |
| force | `Discharge`, and the deontic layers of `AM-`/`CM-` | changes what is owed and what is operative |

Filing a response has no normative effect whatever.  This is the ledger's main
structural contribution: it makes "we have an answer" and "the question is
settled" different events with different authorizations.

**Later actor indexing.** `basis`, `authorization` on every event, and the
`Identify` certificate are the fields that would become actor-indexed: an
obligation is owed *by* someone *to* someone, and identification requires the
consent of both filers.  `obligation_id`, `kind`, `carrier`, and `lineage` would
not change.  Every result here assumes the singleton actor, and `AD-J5` in
particular — that identification need not merge obligations — is what makes the
multi-actor extension plausible, since it never destroys a filer's record.

**Bridge to the migration interface.** {#AD-C1}
**Status: PROPOSED (interface revision).** A migration certificate would emit one
ledger event per open obligation, replacing `ST-C1` item 1 entirely.  Not
adopted: compatibility with every `AM-`, `CM-`, `ST-`, and `LG-` claim is
unchecked, and the ledger is currently a separate object with its own tests.

## 9. What remains open

- Whether (T1)–(T7) are *necessary* as well as sufficient.
- Whether the ledger composes across **branching** histories; everything here is
  linear and singleton-actor.
- Whether `AD-C1` can be adopted without disturbing the frozen interface.
- What an adequacy oracle should be.  The parametric treatment is deliberate:
  this phase supplies the demand interface, not the theory of good answers.
