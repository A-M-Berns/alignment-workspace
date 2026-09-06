# Canonicalization readiness: the legitimacy / normative-induction spine

This document says what the canonical theory should now state. It is not itself
canonical. Every name is provisional. Evidence classes are those of `THEOREMS.md`;
"Lean" means a sorry-free declaration in this round's modules auditing to the allowed
axioms.

## 1. Primitive structures, certificates, consequences

The current material contains three kinds of thing that prose has been running
together. Sorting them is most of the consolidation.

**Primitive structures** (supplied; nothing proves them):

| object | type | where |
|---|---|---|
| history prefix | `List Nat` of authenticated event identities, ordered by prefix | `OccurrenceIntegrity.Boundary.history` |
| obligation occurrence | element of `Occ`, distinct from its content | `Boundary.exposed : Finset Occ` |
| anchor | `anchor : Occ → Req`, fixed at admission | parameter of `Accounted`, `Initial`, `Step`, `Segment` |
| docket | live ports with demanded content, `Fin portCount → Req` | `Boundary.demand` |
| anchored evidence | `Evidence : Req → Type` — what adequately answers a requirement | `Protocol.Evidence` |
| settlement view | `SetView : prefix → Settlement → Prop` | `Protocol.SetView` |
| closure judgment | `Closes : prefix → Req → Settlement → Warrant → Prop` | `Protocol.Closes` |
| authority | `Authorized : prefix → Warrant → Prop`, `AnswerOK`, `Admitted`, `Live` | `Protocol` |
| intervention semantics | a concern's coverage state at the actual prefix and at each `j ∈ J` | `NonCapture.Scenario` |
| evaluation protocol | `μ`, `T`, `Λ`, `D`, `Π_s`, `d_s`, constants | `NormativeInductionInterface.Evaluation` |

**Certificates** (data about the primitives, stored, never recomputed):

| certificate | content | where |
|---|---|---|
| `Authority` | fresh event at a strict prefix, prior grounds, warrant in force | `OccurrenceIntegrity.Authority` |
| `AnswerReceipt r` | authority + `AnswerOK` | |
| `ClosureReceipt r` | authority + settlement item + `SetView` at that prefix + `Closes` at that prefix | |
| `LocalLaw r` | authority + successors + `toChildren`, `ofChildren` evidence maps | |
| `Program B r` | the account of one requirement at boundary `B`: a tree of local laws over the three fates | |
| `Initial` | every exposed occurrence admitted and on a live port demanding its anchor | |
| `Step A B` | one fresh event; an account at `B` for every live port of `A`; fresh occurrences admitted and ported | |
| `Segment A B` | a boundary-indexed chain of steps — **the Integrity certificate** | |
| Non-Capture bill | `CoverageActual`, `ClauseS`, `ClauseRa/Rb/Rc`, `ClauseP` | `NonCaptureCertificate` |
| `PracticalCert` | `Λ_{anchor e,s}(Π_s) ≤ M_es d_s + ε_es` at the realized market | `Evaluation.PracticalCert` |
| `PracticalUptake` | the edge certificates, `λ_s d_s² ≤ ρ_s`, the amplification bound | `Evaluation.PracticalUptake` |

**Consequences** (Lean theorems, this round unless marked):

| theorem | statement | class |
|---|---|---|
| `Program.evaluate_subst` | substitution preserves anchored denotation: carry is faithful | Lean |
| `Program.terminals_subst`, `terminals_le_subst` | a step keeps every recorded receipt and adds only receipts at live leaves | Lean |
| `Program.livePorts_subst` | a step replaces exactly the live leaves | Lean |
| `Program.fates_ne_zero` | no account is empty | Lean |
| `Segment.complete_accounting` | initial exposure + segment ⇒ an account for every exposed occurrence | Lean |
| `Segment.propagate_trans` | composition of certificates is composition of accounting | Lean |
| `Segment.denote` | every occurrence's account denotes evidence for its own anchor | Lean |
| `Witness.distinct_fates` | equal anchors, distinct fates: multiplicity is not erasable | Lean |
| `Scenario.certPlus_iff_robustOpen` | given actual coverage, the PR85 bill *is* Robust Openness | Lean |
| `Scenario.robustOpen_of_persistence` | the componentwise persistence bill implies Robust Openness | Lean |
| `Witness.persistence_not_necessary` | and is strictly stronger | Lean |
| `edge_progress_bound`, `edge_progress_bound_quadratic` | the finite Progress bound at the edge endpoint | Lean (Codex worker) |
| `edge_headline_separation` | the headline endpoint is not the edge endpoint | Lean (Codex worker) |
| `Evaluation.progress_bound` | the same, typed on the Integrity export | Lean |
| `Evaluation.conditional_normative_inductor` | liability + computable market + `PracticalUptake` ⇒ LI ∧ Progress bound | Lean, unverified-nonvacuous on the LI half |
| `Evaluation.deductive_normative_inductor` | registered effective end-to-end + defect domination + edge certificates ⇒ LI ∧ Progress bound, with `λd² ≤ ρ` derived | Lean, inherits the registered theorem's inhabitation status |

The lattice-valued `HistoryIntegrity.SliceLedger` theory of PR85 is an instance of the
program model with `Evidence` read off a join-semilattice; it is retained as
evidence and demoted below.

## 2. Integrity ⇒ Answerability, settled

**What PR85 showed and what survives.** Record integrity in the I1–I9 sense does not
imply the three-fate conservation; the countermodels stand. PR85's repair,
`LocalConservation`, is close to a restatement: its `carry_complete` clause says the
successors' load dominates the parent's, which is the conclusion at one step.

**The lowest local invariant.** The primitive that actually does the work is that a
transition supplies, for each live port, *an account* — a term of `Program`, whose
constructors are the three fates plus authenticated local laws — and has no
constructor by which content leaves. Conservation is then not a clause but a
consequence of the type: `complete_accounting` is a definition, and the content of
the theorem is carried by `evaluate_subst` (the account still denotes the original
anchor's evidence), `terminals_subst` (no receipt is rewritten), and the fact that
`Step` speaks only about ports while the conclusion speaks about occurrences. That is
the local-to-global step: a transition is local to the docket; the account is global
over exposure.

Every PR85 attack is blocked by the typing, not by a clause:

| attack | what blocks it |
|---|---|
| unchecked answer label | `Program.answer` needs an `AnswerReceipt`, whose `adequate` field is `AnswerOK` at a strict prefix |
| self-grounded / unauthorized disposal | every internal node and receipt extends `Authority`: fresh event, grounds strictly prior, warrant in force |
| manufactured settlement or closure | `Program.close` needs `SetView` (external) and `Closes` (internal) at the receipt's prefix, both stored |
| retroactive recomputation of `Closes` | `Closes` is a field of a stored `ClosureReceipt` at `atHistory`; `subst` carries the receipt unchanged (`terminals_subst`) |
| zero-ledger / bottom witness | `Initial` requires `Admitted` and a live port per exposed occurrence; there is no bottom `Program` |
| existential segment witnesses disagreeing at boundaries | `Segment` is indexed by both boundaries; `trans` needs a literally shared middle |
| multiplicity collapse under equal content | accounting is a dependent function on `Occ`; `Witness.distinct_fates` |
| weakened or infeasible successor | `LocalLaw` carries `ofChildren` (no loss) and `toChildren` (no growth); `LocalLaw.feasibility` |

**Occurrence identity: decided.** Occurrence identity lives *outside* the content
type. The account is occurrence-indexed and proof-relevant; the content type `Req` and
its evidence carry no multiplicity. A single receipt may discharge two occurrences
only if the transition explicitly routes both ports to it; that routing is data in
`Step.replacement`. There is no additive or multiset layer over content, because none
is needed: multiplicity is in the index.

**Faithful carry: decided.** A local law carries evidence maps in both directions.
The forward map excludes growth (a successor may not demand more than the parent);
the backward map excludes loss (the successors jointly still answer the parent).
Neither is an equivalence and neither has a round-trip law; those would be
proof-relevant conditions with no normative content. A disposal successor under the
Defeat Principle is the identity law with the grounds recorded in its `Authority`.

**Standing is not in Integrity.** The remaining PR85 attacks — a successor at an
anchor where the protected party no longer stands, minted standing, licence
reinterpretation — concern *who may act*, not *what is owed*. They are Robust
Openness failures (§4). Integrity's `Live` credential is the record fact that a port
is open; it is not a standing claim.

**The theorem, stated.**

> **Answerability Conservation.** Let `S` be a protocol, `anchor` an anchoring, `A`,
> `B` boundaries. Given `Initial S anchor A` and `Segment S anchor A B`, every `o ∈
> B.exposed` has an account `Program S B (anchor o)`; its fates are nonempty and drawn
> from `{answered, closed, live}`; its denotation is evidence for `anchor o`; and every
> receipt it records was recorded at a strict prefix and is never rewritten.

Hypotheses: none beyond the certificate data. Genericity: generic. Evidence: Lean
(`complete_accounting`, `fates_ne_zero`, `denote`, `terminals_subst`).

## 3. Settlement semantics, exact

Six distinct things were being called "settlement integrity". Their homes:

| # | condition | home | form |
|---|---|---|---|
| 1 | boundary/interface authenticity of an item | external bill | `Protocol.SetView` is assumed to mean "available through the boundary" |
| 2 | epistemic trustworthiness of the source | external bill, separate from 1 | nothing in the theory consumes item truth |
| 3 | append-only historical availability | Integrity | a `ClosureReceipt` stores `available` at its own prefix; later prefixes need not re-establish it |
| 4 | the internal `Closes` judgment | Integrity, stored | `ClosureReceipt.closes` at `atHistory` under `warrant` |
| 5 | authority to use the closure | Integrity, stored | `ClosureReceipt.permitted` |
| 6 | resistance to suppression or delay under interventions | Robust Openness, only when the application puts settlement access in a route's adequacy or names it in `J` | `ClauseRa/Rb/Rc` on that route |

A historical discharge is the immutable term `Program.close receipt _`. Later
rejection of the closure rationale is an appended event admitting a fresh occurrence
(a `Step` with a new element of `exposed`, anchored at "reconsider `receipt`"), and
the old account is unchanged (`terminals_le_subst`). Whether a successful challenge
*must* create such a fresh occurrence is licence content of the practice, external.

The phrase "settlement integrity" should not survive canonicalization as a single
hypothesis. The wiki's current statement conflates 1, 2, 3 and 6.

## 4. Legitimacy, factored

**Statement.**

> `Leg_P(H, m, n) := Segment S anchor (H_m) (H_n) × RobustOpen_P(H_n; Γ, J, I)`.

Diachronic Answerability is not a conjunct. Its content half is §2's theorem, a
consequence of the segment. Its standing half — the protected party keeps standing on
every carrier of a concern applicable to it — is the `(P)` clause of Robust Openness
evaluated at the actual history. For that reading the intervention class must contain
the null intervention; this round adopts that as the meaning of `RobustOpen` (an
agent-decided, reversible entry).

**Counterexample to deriving standing from Integrity.** PR85's A6: content carried
faithfully to a successor at an anchor where only the resolver stands. Every Integrity
condition holds; the protected party cannot act. No additional primitive is needed,
because `(P)` already states the missing condition over carriers; what changes is only
that `(P)` is read at the actual prefix as well as the counterfactual ones.

**The Non-Capture bill, after compression.** `certPlus_iff_robustOpen` shows that,
given actual coverage, PR85's bill `(S) ∧ (R+) ∧ (P)` is logically identical to
`RobustOpen`. It is the conclusion split on whether the concern is live at the actual
prefix; it is not a sufficient condition with independent content. The public
statement should therefore be:

> **Robust Openness.** For every `j ∈ J` (including the null intervention) and every
> concern `c ∈ Γ`: if `c` is live in `H^j` then some route is adequate in `H^j`; and if
> `c` is applicable in `H^j` then `P` stands on its carrier in `H^j`.

What an external capture theory substantively certifies is the **persistence bill**
`CoverageActual(W) ∧ (S) ∧ (Ra) ∧ (Rb) ∧ (Rc) ∧ (P)` — that protected routes keep
their admissibility, efficacy and registration capability under every intervention.
`robustOpen_of_persistence` proves it sufficient; `persistence_not_necessary` shows it
strictly stronger. PR85's necessity attacks attach to the persistence bill and are
retained as such. Concern identity, applicability transport, branch coupling, the
protected relation, and the fixed exterior policy are the *type* of the intervention
semantics (`Scenario`), not clauses.

**The slogan, checked against the definitions.** "Integrity blocks evasion by
revision" is true in the form: no `Step` has a constructor by which content leaves, and
no receipt is rewritten. "Robust Openness blocks evasion by exclusion" is true in the
form: coverage and standing are required in every declared branch including the
actual one. What the slogan omits is that the two are stated over different objects —
a segment of the actual history versus a family of coupled branches at one prefix —
so the conjunction is not a single predicate on a history. That is the correct shape,
not a defect.

## 5. The public handoff `O_P`

`O_P` at prefix `n` is the boundary and its account:

```text
O_P(n) = (B_n : Boundary Occ Req, anchor : Occ → Req, account : Accounted S anchor B_n)
```

- historical exposure `E_{≤n}` = `B_n.exposed`;
- live docket = `B_n.demand` over its ports;
- anchored specification = `anchor`;
- status and lineage = `account o : Program S B_n (anchor o)`, whose `fates` give the
  status and whose internal nodes give the authenticated lineage.

No weights, importance, intensities, probabilities, or securities. Consumption is
checked: `Evaluation` reads `B_n.exposed` and `anchor` and nothing else; a
compiler/scheduler reads the docket; an auditor reads the account. The PR85
`ObligationExport` on `DefeatTrace` is the structural instance of this for the older
trace model and is demoted to evidence.

## 6. Progress, at its canonical endpoint

The Progress statistic is

```text
progress(T, Π) = Σ_{e,s} T(e,s) · Λ_{anchor e, s}(Π_s) + D · (1 − Σ_{e,s} T(e,s)),
```

with `Π_s` the one response realized at `s` and every edge into `s` scored against it.
This is PR82's statistic (`progress_certificate` sums certified edge bounds plus the
residual charge). PR85's `progress_bound` silently replaced it with a headline
`Σ_e μ(e) ℓ(e)` and then needed `HeadlineToEdgeDominance` to reconnect; that adapter
is not a missing core arrow. It is retained as an optional corollary for
applications wanting one loss per exposure, and `edge_headline_separation` shows its
premise is not free.

**The theorem.**

> **Finite Progress.** If `T ≥ 0`, `d ≥ 0`, `PracticalCert` holds on every edge with
> `T(e,s) > 0`, and `Σ_e T(e,s) M_es ≤ Γ ν_s`, then
> `progress ≤ Γ Σ_s ν_s d_s + Σ_{e,s} T(e,s) ε_es + D r`.
> With `ν_s = λ_s / Σλ`, `λ_s d_s² ≤ ρ_s`, and `Γ ≥ 0`, the first term is
> `Γ √(Σρ / Σλ)`.

Lean: `edge_progress_bound`, `edge_progress_bound_quadratic`, `Evaluation.progress_bound`.
Generic. The loss is a function of the anchor: `Λ : Req → (s) → Response s → ℝ`. Two
occurrences with one anchor get one loss and two transport rows; multiplicity is in
`μ` and `T`, never in `Λ`.

**The practical-semantics boundary.** The public certificate is exactly
`PracticalCert(e, s, Π_s; M_es, ε_es)`. Value correspondences, approximate argmax,
finite menus, adequate sets, and replicated evaluation ecologies are sufficient
plugins for producing it (`anchored_response_transport`, `adequate_set_route`) and are
not public structure. Joint practical-response compatibility is the requirement that
every edge into `s` certify against the same `Π_s`, which the type of
`PracticalUptake.practical` enforces.

## 7. The Normative Inductor realization, re-typed

The architecture stands:

```text
NI = MarketMaker(TradingFirm^L + JointProjectionEnforcer[Compile(O_P)]) + DecisionAdapter.
```

Against the cleaned contracts, every PR82 lesson type-checks: one joint region per
service occurrence; public defect `d_s = dist_∞(b_s, K_s)`; intensity `a_s = λ_s`;
Euclidean projection as internal implementation with `λ d_∞² ≤ λ ‖b − proj b‖² ≤ ρ`
(`public_work_le_projection_work`); padding invariance; admissibility is not value;
one response per service; compiler failure conserves (`failure_conserves`).

**The conditional theorems.**

> **General assessment.** Bounded assessed liability of the enforcer and a computable
> augmented market give ordinary Logical Induction; `PracticalUptake` at that market
> gives the Progress bound. (`conditional_normative_inductor`)

> **Compiled deductive schedule.** The registered effective end-to-end theorem's
> hypotheses (schedule computation, process computation, admissibility of every
> compiled row by every plausible world), plus domination of the public defect by
> conformance, plus the edge certificates and amplification bound, give Logical
> Induction and the Progress bound with `λ_s d_s² ≤ ρ_s` *derived* from finite-time
> conformance. (`deductive_normative_inductor`)

The second composes landed pieces end to end; its admissibility hypothesis restricts
it to regions every plausible world satisfies — the zero-liability case. Genuinely
normative regions go through the first theorem, whose liability hypothesis is what the
scheduler's affordability produces (`Workload.liability_le` at the workload level;
the connector to the enforcer's net worth is item B2 below).

**Minimization.** The former `EndToEndHypotheses` carried six opaque predicates
(Integrity, Robust Openness, settlement trust, export, compilation, affordability) and
returned them unchanged in its conclusion. None was consumed by the proof. They are
removed; the conditional theorems now name only hypotheses they use. Integrity and
Robust Openness enter the NI theorem not as predicates but through the *type* of
`Evaluation`, which is indexed by the Integrity boundary.

**Classification of the remaining connectors.**

A. Generic mathematics, provable now:
- A1. none outstanding at the abstraction boundaries; see B and C.

B. Executable/engineering integration:
- B1. an implementation of `Protocol` with an event log, and its `Segment` builder;
- B2. the connector from `Workload.liability_le` (rational budget over a declared
  workload) to the enforcer's assessed net worth in `conditional_normative_inductor`;
- B3. the transport checker binding every supported edge to one response receipt;
- B4. rows-to-vertices for `CompiledDay.represents`, effectively.

C. Research (§9).

D. External by design (§8).

## 8. The external bill

Nothing in the generic theory derives these; each is a typed input.

| assumption | where it enters |
|---|---|
| semantic authentication: `Evidence`, `AnswerOK`, `Admitted`, `Live`, the maps of every `LocalLaw` | `Protocol`, `LocalLaw` |
| settlement boundary authenticity (1) and source trust (2) | `Protocol.SetView`; item truth is never consumed |
| authority rules: `Authorized`, `Closes`, and which practice rules license disposal, reconsideration, and prerequisite drop | `Protocol`; the ruling on disposal licence is item 77 |
| the declared scope `Γ`, intervention class `J`, coupling `I`, protected principal/relation `P` | `Scenario`; the ruling on naming `P` is queued |
| counterfactual identification and response-evaluator adequacy | `Evaluation.loss`, `Pi`, and the truth of each `PracticalCert` |
| the evaluation protocol: `μ`, `T` committed before responses, `D` | `Evaluation` |
| computability of the augmented market for general assessment regions | hypothesis of `conditional_normative_inductor` |
| admissibility of compiled rows by plausible worlds, in the deductive composition | hypothesis of `deductive_normative_inductor` |

## 9. The research frontier

Only genuine problems; integration chores are in §7B and external premises in §8.

1. **Convex representability.** Characterize the class of anchored requirements whose
   evidence type admits a sound finite rational-row realization over a security
   fragment, and prove compiler completeness within a declared subclass. Soundness
   (`compile_sound`), conflict certification (`conflict_sound`), and conservation on
   failure are done; representability of any nontrivial class and completeness are
   open. Joint feasibility and affordable enforceability are separate and downstream.
2. **Adaptive affordable scheduling.** Predictable finite workloads have the
   cheapest-date construction with liability `≤ B` and zero residual. Closed-loop,
   adversarial, or unboundedly growing dockets have no theorem; the units are fixed —
   intensity `λ_s` is what the liability theorem consumes.
3. **Quantitative semantic transport.** A `LocalLaw` fixes what must be transported
   through ontology change: the anchor's evidence type, with maps both ways. The
   quantitative constants `(L, ε)` per law enter `ε̄` through `chain_transport`;
   generating them from a law is open.
4. **A jointly compatible practical-response ecology.** An adapter that certifies
   every edge into a service occurrence against one realized response, for a declared
   obligation class, does not exist. `disjoint_adequate_sets_force_loss` shows the
   problem is real.
5. **Answerability liveness under contest.** Summability of contest durations is shown
   only for exogenous durations; endogenous contest is open.

## 10. Canonicalization blockers

None. Every major object has a type and every major theorem a statement. The two
queued rulings — whether the predicate may name a protected principal, and whether
settlement independence is standing or per-realization — change what the canonical
text *commits to*, not what it *says*: the P-indexed form is the only one that exists
(the party-free form is proved not to), and settlement independence is two typed
inputs (§3, rows 1 and 2) under either ruling.

## 11. Migration map

| current page or concept | action | target |
|---|---|---|
| Legitimacy | redefine | `Leg_P = Segment × RobustOpen_P`; Diachronic Answerability derived, not a conjunct; the two-bills section becomes §8 |
| Integrity | redefine | the program model: boundary, protocol, receipts, local laws, step, segment; the seven-bullet list becomes the constructor list; "settlement integrity is an external hypothesis" becomes §3's six rows |
| Diachronic Answerability | merge into Integrity + Robust Openness | conservation = §2 theorem; standing = `(P)` at the null intervention; the liveness half stays as a research frontier item |
| Openness, coverage, and non-capture | redefine | Robust Openness as the definition; the persistence bill as the external certificate; `(S,R+,P)` no longer presented as a certificate |
| Settlement interface | redefine | six typed conditions; `SetView` and `Closes` as protocol fields; reconsideration as a fresh occurrence |
| Normative induction and Progress | retain, correct endpoint | edge statistic; `PracticalCert`; `PracticalUptake` |
| Normative Inductor | retain, retype | the two conditional theorems; connector classes B/C/D; drop the "remaining obligations" list in favour of §7–9 |
| Progress (fixed-era) | demote to instance | the fixed-era bound is the edge bound with one era, one semantics |
| Actionability and normative force | demote to realization | force/intensity/uptake distinctions live in the NI page and the `PracticalUptake` fields |
| Liability and affordability | demote to realization | scheduling produces the liability hypothesis; frontier item 2 |
| Serviceability | demote to realization | service/liveness dichotomy; frontier item 5 |
| Normative Record and Inquiry | archive as superseded | already marked historical |
| `HistoryIntegrity.SliceLedger`, `LocalConservation` | demote to evidence | the lattice instance of the program model |
| `IntegrityAdversary`, PR85 attacks | retain as necessity evidence | re-index each attack to the constructor that blocks it (§2 table) |
| `NormativeInductorComposition.ObligationExport`, `export_sound` | demote to evidence | structural instance of `O_P` on `DefeatTrace` |
| `EndToEndHypotheses` | archived (removed) | superseded by `NormativeInductionInterface` |
| `progress_bound`, `progress_bound_quadratic` (headline) | demote to optional corollary | stated as such in the module |
| Glossary entries: settlement integrity, answerability conservation, non-capture certificate, Progress | redefine per the rows above | |
