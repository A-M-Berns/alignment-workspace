# Reason-state narrow waist: prosecution memo

Status: **research memo; unregistered**. All names are provisional under
`AGENTS.md` §6. General positive statements are design arguments supported by
finite executable witnesses in `src/` and `tests/`; nothing is registered or
Lean-checked.

## Verdict

**Survives after two structural additions and two conventions; the TMS framing
is discarded rather than refined.** The candidate waist is the identity-bearing
reason hypergraph + schemas + cases + `Inst` + `App`; what it needed is below.

**Forced addition 1 — a contradiction floor.** The content language needs a
constitutive involutive negation. Without it the undercutting target
`¬App(σ,c@n)` is unstatable and rebuttal is inexpressible, so the substrate
cannot even pose the conflicts it is required to expose. Compiling negation
away — a positive `Inapp` atom plus a learnable incompatibility claim linking
it to `App` — makes the coherence of the substrate's own reflective vocabulary
a revisable judgment, which hides normative work in the opposite direction:
a stance adopting both `App(σ,c@n)` and its "negation" would not even be
logically criticizable.

**Forced addition 2 — two-sorted sources.** Sources draw from claims *and*
transcript receipts: `s : E → P_fin(V ⊎ L)`. With claim-only sources, evidence
cannot enter a reason at all. Mirroring receipts as claims either makes the
transcript's content defeasible — falsifying the settlement discipline the
record already imposes — or requires a designated indefeasible claim fragment
checked against `L`, which is the receipt sort under another name. A receipt
source is enabled by transcript membership, a claim source by stance
membership; the monotone/defeasible boundary is exactly the sort boundary.

**Convention 1 — applicability-in-source.** An occurrence applying schema `σ`
to case-view `c@n` carries `App(σ,c@n)` among its sources. `Enabled_B(e) ⟺
s(e) ⊆ B ∪ L` is then strong enough on its own: an undercutter is an ordinary
reason for `¬App(σ,c@n)`, and the learner registers it by withdrawing the
applicability claim, which disables the occurrence with no attack primitive
and no reason for the opposite conclusion. The alternative — negative
dependencies in the Doyle style, where an occurrence is enabled partly by what
is *absent* — builds the presumption of applicability into the substrate,
which is precisely the hidden normative work this round exists to evict.

**Convention 2 — persistence schemas.** Staged applicability creates an
applicability frame problem: `App(σ,c@n)` says nothing about stage `n+1`, so
something must carry applicability forward. The carry is expressible inside
the waist as an ordinary defeasible schema — sources `{App(σ,c@n),
App(π,c@(n+1))}`, target `App(σ,c@(n+1))` — and must not be automatic:
whether applicability persists for a volatile matter is substantive.

**The structural reframing.** The right abstraction is not a maintenance
system. The substrate stores no labels, no contexts, no IN/OUT statuses, and
runs no update procedure; it is a stateless family of total queries over
`(structure, stance, transcript)`. Everything a JTMS or ATMS *does* —
truth maintenance, backtracking, context switching, label update — is an
artifact of the substrate caching a stance or a stance policy, and reappears
here as one explicitly named policy plus optional caching (§5, §10). With no
stored stance there is nothing to maintain, hypothetical queries are the same
functions at another argument, and Doyle's odd loops stop being substrate
failures and become what they are: pathologies of a candidate stance policy.
The provisional name used here is **reason state**, written `𝓡_n`, against the
**normative record** `N_{≤n}` and the transcript `L_{≤n}`; the naming ruling
is reserved (§14).

## 1. Constraints inherited from the workspace

| Existing object | Constraint it imposes here |
|---|---|
| internal-answerability `MEMO.md` §3 (R1–R7) | certificates carry finite declared dependency views checked in the pre-state; the reason state must supply stable identities those views can name |
| internal-answerability §3.3–3.4 | available authorization ≠ undertaken basis; the substrate must not conflate "some valid support exists" with "this support was relied on" |
| internal-answerability §6 | basis loss is edge-triggered from `UsedAt` records; the reason state must keep retired occurrences resolvable forever |
| role-parametric answerability §2–3 | dispositions are typed and input-scoped; the reason state feeds the account law, it does not duplicate it |
| afoundational-inquiry `MEMO.md` §3–4 | due tokens, coverage debts, docketing and accrual are record machinery; `App` of a warrant is already a `Hold`-content there |
| `THEORY_11` settlement interface (via internal-answerability §6.1) | settled transcript events are basis-free and incorrigible; nothing in the reason state may make them defeasible |
| `Reasons-Answerability-and-the-Score` statics | committive/permissive inference and incompatibility are distinct relations; applicability is contestable content |
| crown-jewel `Due`/`Licensed`/`Performance` | the reason state must let `Licensed` certificates cite reasons without hardwiring `Due` into the graph |

The reason state slots into the internal-answerability state `S_t` as a
refinement of its `R_t` ("current reason view"): occurrence identities and
claims are the `DependencyId`s certificates declare, and `App` claims are the
aggregate-key targets R7 requires for defeasible standing.

## 2. The prosecuted interface

### 2.1 Content language `V`

Five constructors, closed under each other; no others.

| Constructor | Semantics |
|---|---|
| `Atom(a)` | opaque first-order content, including practical contents ("respond `r` to `d`"); the typed content language downstream refines it |
| `Neg(x)` with `Neg(Neg(x)) = x` | the contradiction floor; `x` and `Neg(x)` are jointly incoherent by grammar, not by adopted content |
| `App(σ, c, n)` | schema `σ` applies to case `c` on the stage-`n` view; `n` is record time, never world time |
| `Inst(e, σ)` | occurrence `e` is an instance of schema `σ`; a revisable classification, never consulted by enabledness (§2.3) |
| `Incomp(S)` for finite `S ⊆ V` | the members of `S` cannot jointly be adopted; reified, learnable, defeatable (§7) |

`V` is the type of expressible claims; it needs no registry. Reflectivity
comes from `App` and `Inst` taking structure identities as arguments.

### 2.2 Structure

- **Occurrence** `e = (id, s(e), t(e))` with `s(e) ⊆_fin V ⊎ L` and
  `t(e) ∈ V`. Sources and target are constitutive: fixed at minting, never
  revised. Occurrence identities are never reused and never deleted —
  disabling routes exclusively through sources leaving the stance, so
  record-side reliance references stay resolvable forever.
- **Schema** `σ ∈ Σ_n`: a bare identity. Everything else about a schema —
  membership, applicability, priority, reliability, continuity with a
  successor — is claims.
- **Case** `c ∈ C`: a bare persistent identity (§4).
- **Docket item** `d ∈ D` with `about : D → C` and an open/closed status —
  record machinery, included here only to keep the three-way distinction
  testable.
- **Transcript** `L`: the set of receipt identities so far; monotone.
- **Procedural provenance** `T ⊆ C × L`: receipt `ℓ` arose in working on case
  `c`. Constitutive history; generates no reasons (tested).
- **Stance** `B ⊆_fin V`: the learner's current adopted claims. Not a
  component of `𝓡_n` (§6).

### 2.3 Queries

For `e` in the structure, `B` a stance, `L` the transcript:

```text
Enabled_B(e)     iff  claims(s(e)) ⊆ B  and  receipts(s(e)) ⊆ L
Reasons_B(v)      =   { e : t(e) = v, Enabled_B(e) }
Dependents(x)     =   { e : x ∈ s(e) }
Explain(e)        =   (s(e), t(e))                       [structure lookup]
LostBasis_B(log)  =   { (m,e,n) ∈ log : ¬Enabled_B(e) }  [record-facing]
```

All are total on every `(B, L)`, including incoherent stances, and none
mutates anything. `Inst` claims never enter enabledness: reclassifying an
occurrence must not retroactively rewire what its past reliance depended on
(tested — constitutive sources survive reclassification).

## 3. Deliberately not primitive

| Rejected primitive | Where its work went |
|---|---|
| `Undercuts` edge | derived: `t(e') = ¬a` for an `App` claim `a ∈ s(e)` |
| `Rebuts` / attack edges | derived from the floor plus adopted `Incomp` (§7); stance-relative |
| structural incompatibility over arbitrary contents | reified `Incomp` claims; only the logical floor is constitutive |
| `Hold`, `Do` | record commitment contents; the reason state targets claims, including practical ones |
| `May`, `Must` | record rule modes; a rule's applicability is already an `App`-shaped content there |
| `Supported`, `Live` | the queries `Reasons`, `Enabled` — asking, not asserting |
| priority, reliability, evidential relevance | ordinary revisable claims (§8) |
| negative dependencies (outlists) | evicted; presumption of applicability is a learner policy over reified `App` |
| IN/OUT labels, contexts, environments | policy-plus-caching over the queries (§5, §10) |
| deletion / retraction of occurrences | does not exist; disabling routes through sources |
| closure (`Reasons_B(v) ≠ ∅ ⟹ v ∈ B`) | one nameable policy among many; running it silently is the failure the round guards against |

## 4. Case, docket, transcript

The surviving type is **Candidate A structurally, Candidate C temporally**: a
case is a bare persistent identity, and *applicability* targets the staged
view `c@n` — which is notation for the pair `(c, n)`, not a new sort.

Answers to the dispatch's questions, in order:

- **Issue field:** no. Questions, investigations and reviews are docket items
  with `about : D → C`; a case with no live docket item is just an identity.
- **What makes two receipts same-case:** `T` is a constitutive procedural
  fact — this receipt arose in working on that case — and it carries no
  evidential weight (tested: `T` edges generate no reasons). *Taking* a
  receipt to bear on a case is a revisable relevance claim, an ordinary
  target.
- **Split/merge:** new case identities with record provenance, exactly the
  account-DAG pattern the answerability kernel already uses for liabilities.
  Same-case *judgments* (`these two threads are one situation`) are revisable
  claims; acting on one is a record act minting successors, not an edit to an
  identity.
- **After the docket closes:** the case persists; liveness is docket-level.
- **Several practices, one case:** cases are shared referents; dockets are
  practice-local. Nothing in the type resists this.
- **Seed versus runtime cases:** same type. A seed example is a case with
  historical occurrences and no live docket item (tested in example 1: the
  historical instances ground applicability to the new case through `Inst`
  claims).
- **The temporal object `App` takes:** the record-time-staged view, forced by
  example 12. `¬App(σ,c@n)` adopted later contradicts the earlier
  `App(σ,c@n)` — a correction; `App(σ,c@n) ∧ ¬App(σ,c@(n+1))` is jointly
  coherent — a changed world. Unstaged `App` identifies the two claims and
  the distinction is unrepresentable (tested both ways). Stage indices are
  record positions because accrual time already is (afoundational round §4);
  a world-time argument would smuggle an unobservable.

The cost of staging is Convention 2: persistence must be earned by schemas,
not granted by the substrate.

## 5. The query interface, derived from consumers

Consumers: the normative learner (stance revision, response selection); the
record (undertaken certificates, basis-loss review); the operative compiler
`R → O`; inquiry generation.

**Mandatory narrow waist:** `Enabled`, `Reasons`, `Dependents`, `Explain`,
`LostBasis` — the five in §2.3.

- The learner needs `Reasons`/`Enabled` to see what bears on what, and needs
  them *total* — a substrate that refuses incoherent stances is enforcing
  coherence, which is a norm.
- The record's certificates cite occurrence identities and their sources;
  `Explain` is the lookup. The dependency-DAG the internal-answerability
  kernel consumes is assembled by chasing cited sources — record-side
  composition, not a substrate primitive.
- Basis-loss review needs exactly `LostBasis` over the reliance log, and
  `Dependents(x)` answers "if I withdrew `x`, what loses basis" before the
  withdrawal happens.
- "Which conclusions have support paths through this applicability judgment"
  is `Dependents` composed transitively through *cited* certificates — the
  record knows what was relied on; the substrate should not pretend every
  syntactic path was a reliance.
- Hypothetical queries are free: `Enabled_{B'}` is the same function at `B'`.
  No snapshot, no context switch, no unouting (§10).

**Optional derived queries** an implementation may cache: `bearing` (image of
`Reasons`), the attack relations (§7), support closure under a *named*
policy, minimal supporting environments (ATMS labels), nogoods. None is
primitive, and two of them are policy-relative (below).

**Implementation-independence claim (provisional).** Any backend computing
`Enabled`, `Reasons`, `Dependents`, `Explain`, `LostBasis` extensionally, as
total functions of `(structure, B, L)`, can serve as the substrate for the
downstream learner and record. Two caveats keep it honest:

1. **Totality is part of the interface.** An ATMS-style backend that prunes
   nogood environments is answering a different question — it has quietly
   adjudicated the incompatibility claims (see caveat 2) and imposed the
   credulous closure policy inside the label computation. It may serve as a
   *cache* for a learner that has explicitly chosen that policy; it cannot be
   the substrate.
2. **Nogood-hood is policy-relative and non-monotone here.** Classical ATMS
   caching is sound because `⊥`-justifications are fixed and monotone. With
   incompatibility reified and learnable, an environment's nogood status
   depends on which stance policy is run (a learner that declines to adopt a
   derived `Incomp` claim gets different nogoods — witnessed), and a newly
   minted occurrence targeting an `Incomp` claim flips previously good
   environments (witnessed). Cached labels survive; cached *consistency
   filtering* does not.

The two-backend witness: exhaustive enumeration of minimal supporting
environments and ATMS-style label propagation agree extensionally on the
finite fixtures (`test_label_backends_agree_extensionally`).

## 6. Support versus stance

**What `B` is.** A finite set of claims — the learner's current adopted
content. It is a separate state, not a component of `𝓡_n` and not derived
from it; the record tracks its public trajectory through acknowledgment acts,
which is where relational scorekeeping already lives. Actions are not members
of `B`; practical claims about responses are, and performance is a record
event. This keeps `Hold`/`Do` downstream, as expected.

**Guarantees imposable on `B` without smuggling norms:** grammar only —
finiteness and membership in `V`. Not consistency: with incompatibility
learnable, requiring `B` to respect adopted `Incomp` claims would have the
substrate enforce a judgment the learner is entitled to revise. A stance
violating an adopted incompatibility is *criticizable* — the queries expose
the violation — not unrepresentable (tested). Not closure: adopting
everything supported is one policy, named `support_closure` in the model and
kept out of the substrate (tested: bearing and stance differ).

**On basis loss** the division of labor is: the substrate reports that the
relied-on occurrence is no longer enabled (`LostBasis`), and that a currently
valid alternative exists if one does (`Reasons`); the record mints the review
liability; the learner decides among reaffirm, revise, suspend, investigate,
distinguish the case, or reclassify the schema. The alternative support does
not silence the report — reliance history is the record's, and the tests
fail any implementation that overwrites it.

**The odd-loop dividend.** A self-undercutter — `s(e) ∋ App(σ,c@n)`,
`t(e) = ¬App(σ,c@n)` — is Doyle's odd loop. A labeling substrate must find a
stable status assignment and there is none; here the substrate is total and
merely reports: enabled under stances containing the applicability, bearing
against it (tested). The instability belongs to candidate stance policies,
where it is real information — no coherent stance adopts this occurrence's
closure — rather than a crash.

## 7. Incompatibility

What rebuttal actually requires came apart into two objects:

1. **The constitutive floor.** `x` versus `Neg(x)` — grammar. This is what
   makes "corrected belief" a *logical* correction (§4) and keeps the
   reflective vocabulary itself coherent. It is the one incompatibility the
   learner does not get to revise.
2. **Reified `Incomp(S)`** for finite `S` — ordinary claims, supported and
   attacked by ordinary occurrences. Practical infeasibility ("cannot attend
   both"), commitment conflicts, and n-ary resource conflicts (any two of
   three, not all three — binary is insufficient) are all here. An `Incomp`
   claim is defeated the same way anything else is: undercut the supporting
   occurrence's `App`, or rebut it.

**Rebuttal is derived and stance-relative:** `e` rebuts `e'` at `B` iff both
are enabled and their targets are floor-contradictory or jointly covered by
an adopted `Incomp` in `B` (tested: the practical conflict appears exactly
when the incompatibility claim is adopted). Nogoods are the closure of this
under a stance policy and inherit its relativity (§5).

`Claim`/`Act` target sorts are not forced: practical contents ride as atoms,
and a typed action target is a compatible later refinement. What *is* settled
is that no `Do` constructor belongs in `V` — a reason bears on the claim that
a response is called for; undertaking the response is a record act.

## 8. Reflective vocabulary and the reification criterion

Criterion: revisable-for-reasons → expressible as a target. Constitutive
provenance → record, not target. Applying it:

| Judgment | Disposition |
|---|---|
| schema membership | **reified** (`Inst`); construction-provenance (minted-under-σ) stays record-side; `Inst` never feeds enabledness |
| applicability | **reified** (`App`, staged); feeds enabledness through sources by Convention 1 |
| incompatibility | **reified** (`Incomp`), over a constitutive logical floor |
| evidential relevance | **reified** as ordinary claims; plausibly `App` of an evidential schema — not forced here |
| receipt-belongs-to-case | constitutive `T` (procedural fact) *plus* revisable relevance claims; the split dissolves the tension |
| same-case identity | revisable claims; acting on one is a record act with provenance |
| schema identity across time | identities are constitutive; continuity judgments are claims |
| reason priority | **reified as ordinary claims**, not substrate-consumed — the substrate never adjudicates, so priority has no structural seat; precedent: variable-priority default theories (§10) |
| reliability | ordinary claims |
| "this reason was relied upon" | **constitutive record fact** (`UsedAt`); claims about it may exist, the fact is not revisable |
| authorization / standing | record-side (license genealogy, certificates); claims about standing are ordinary targets |
| `May` / `Must` | record rule modes; not reason-graph constructors |
| `Live` / `Supported` | derived queries |
| source/target of an edge | constitutive — reclassification (example 5) proves why: revisable sources would let a later classification rewrite what past reliance depended on |

## 9. Prosecution matrix

Columns: what carried the example. `structure` = constitutive reason state,
`V` = revisable claims, `N` = record, `L` = transcript, `API` = query,
`learner` = left to policy. Each row names its test in
`tests/test_reason_state.py`.

| # | Example | Carried by | Test |
|---|---|---|---|
| 1 | ordinary schema application | `Inst` claims ground `App`; application carries `App` in source (V, structure) | `TestOrdinarySchemaApplication` |
| 2 | undercutting | reason for `¬App` (V); learner withdraws `App`; `Enabled` flips (API); no opposite support | `test_undercut_disables_without_supporting_the_opposite` |
| 3 | undercutter of undercutter | same machinery one level up; closes with ordinary structure | `test_nested_reflection_closes_with_ordinary_structure` |
| 4 | rebuttal / conflict | floor (structure) + `Reasons` exposes both sides; nothing resolves (API) | `TestRebuttalAndConflict` |
| 5 | schema reclassification | `¬Inst(e,σ)`, `Inst(e,τ)` as targets (V); constitutive sources untouched (structure) | `test_reclassification_revises_claims_not_constitutive_sources` |
| 6 | schema split | new identities (structure) + reclassification reasons (V) | `test_split_and_merge_are_new_identities_plus_claims` |
| 7 | schema merge | dual of split; same machinery | same |
| 8 | cross-cutting schemas | multiple `Inst` claims coexist; no partition anywhere | `test_cross_cutting_schemas_are_not_a_partition` |
| 9 | same content, distinct occurrence | occurrence identity (structure); reliance distinguishes them (N) | `TestStructuralIdentity`, `test_only_the_relied_on_occurrence_is_reported` |
| 10 | one case, several docket items | `about : D → C` (N) | `test_one_case_several_docket_items` |
| 11 | one receipt, several cases | `T` relation (L/N boundary) | `test_one_receipt_two_cases` |
| 12 | changed world vs corrected belief | staged `App` + floor (structure) | `TestStagedApplicability` |
| 13 | basis loss and review | `UsedAt` log (N) + `LostBasis` (API); alternative support does not overwrite | `TestBasisLossAndReliance` |
| 14 | uninterpreted evidence | receipt in `L`, `T` recorded, no occurrence → no bearing | `test_uninterpreted_evidence_changes_nothing` |
| 15 | reasons about organization | `Inst` targets of ordinary occurrences (V) | `test_reasons_about_organization_are_ordinary_reasons` |

No example forced a new primitive beyond the two additions in the verdict;
examples 2, 4 and 12–14 are the ones that forced them.

## 10. JTMS, ATMS, and defaults at the interface level

Sources were read in the primary PDFs; page references are to the published
texts.

**Doyle 1979.** An SL-justification is an inlist/outlist pair, valid when the
inlist is believed and the outlist is not; a node is *in* iff some
justification is valid; truth maintenance finds a well-founded status
assignment; dependency-directed backtracking locates the assumptions under a
contradiction, records their inconsistency, and *retracts one by adding a
justification* (pp. 236–238; de Kleer's summary p. 138 concurs). At the
interface level: (a) the TMS chooses beliefs — substrate and stance policy in
one box; (b) the outlist is a presumption policy inside the substrate — the
exact mechanism this round replaces with reified `App` plus learner
withdrawal; (c) Doyle's own *in/out ≠ true/false* (p. 238) already marks the
status/content distinction this design finishes; (d) odd loops and unouting
are costs of storing statuses at all.

**de Kleer 1986.** Each datum is labeled with the minimal assumption
environments deriving it; multiple contexts are held simultaneously; a
contradiction marks an assumption set nogood rather than forcing retraction
(pp. 130–132). Decisive for this round: *"The task of selecting the part of
the search space to examine is the problem solver's; the TMS should only
record the state of the search so far"* (p. 131) — the stance/substrate
division stated in 1986. But the ATMS realizes it only half-way: labels are
computed under monotone Horn justifications with a fixed `⊥`, so consistency
filtering is baked into the label algebra. Under this round's semantics the
ATMS is a *cache* of hypothetical support queries for the credulous closure
policy — sound while incompatibility is fixed, unsound once `Incomp` is
learnable content (§5 caveat 2, executable witnesses). His catalogue of JTMS
limitations — single state, switching difficulty, context-dependent
assumption status, unouting (pp. 138–139) — reads as a list of costs of a
stored stance, all of which vanish for a stateless substrate.

**Horty 2006 (draft of August 16).** Reasons are the premises of triggered
defaults; defaults *provide* reasons (p. 12). Triggered/conflicted/defeated
(pp. 11–14) map to enabled / rebutted-at-`B` / outweighed — the first is
substrate, the second derived and stance-relative, the third has no seat in
the substrate at all, matching Horty: defeat needs priorities, and his
variable-priority theories put priority statements in the object language as
conclusions of defaults, defeasible like anything else (pp. 21–22) — the
direct precedent for §8's disposition of priority. His defeat is explicitly
rebutting-only, with undercutting deferred and glossed as undermining "the
capacity to provide a reason" (p. 21); reified staged `App` supplies exactly
that capacity as content, and the derived relations keep the two attack forms
structurally distinct (undercut targets a source's `App`; rebuttal is target
incompatibility — tested to be disjoint on the fixtures). His proper-scenario
theory occupies the normative learner's seat: it is one stance policy, and
the substrate here deliberately does not choose it.

**Second-order structure.** Schema organization does not introduce a
hypergraph over schemas: `Inst` and `App` as vertices keep one graph, and
schema-level reasoning is ordinary edges targeting them (examples 1, 15).
Reifying `Inst` is cleaner than a second-order edge sort because the same
occurrence machinery then covers organizational revision — which is the
point of the criterion in §8.

## 11. Known failures and forced additions

What failed in the candidate as dispatched:

1. `H_n = (V, E, s, t)` with `s : E → P_fin(V)` — **no way in for evidence**.
   Two-sorted sources forced (verdict, addition 2).
2. `V` as bare contents with `App`/`Inst` — **conflict inexpressible**. The
   negation floor forced (verdict, addition 1). Anything less re-imports a
   primitive attack relation: without `¬`, "undercutter" cannot be a reason
   *for* anything, and `Undercuts` comes back as structure.
3. `Enabled_B(e) ⟺ s(e) ⊆ B` — **too weak on its own**: nothing connects an
   undercutter to the occurrence it disables. Survives only under Convention
   1 (applicability-in-source). This is a representational discipline the
   memo can state but the type system does not enforce; a checker for it is
   future work.
4. Unstaged `App(σ,c)` — fails example 12 outright.
5. The TMS reading of the substrate — fails Investigation 4 by construction:
   any component that stores IN/OUT or prunes nogoods has adjudicated
   something. What survives is the query interface plus policy-labeled
   caching.

Costs accepted knowingly: staging is verbose (a persistence schema per
volatile applicability family); the applicability-in-source convention makes
sources heavier; `B` must explicitly carry `App` claims the learner presumes,
so presumption policies do bookkeeping the JTMS outlist did silently. Each
cost is the price of an eviction the round was dispatched to make.

## 12. Downstream interfaces

**The handoff `(N_{≤n}, L_{≤n}, 𝓡_n, B_n) → O_n`.** The compiler can recover:
current bearing (`Reasons_B`); the occurrences involved and their sources
(`Explain`); their schemas (`Inst` claims in `B`, plus record
construction-provenance); the applicability judgments relied on (`App`
sources); case and stage (`App` arguments); the historically relied-on basis
(`UsedAt` in `N`); what lost basis (`LostBasis` + the record's review
docket); live-versus-endorsed (`Reasons_B` versus membership in `B`); open
docket items (`N`). Each is a query or a record lookup; none needs a new
projection.

**`Due` / `Licensed` / `Performance`.** `Due` stays record-side — due tokens
and docket coverage generate it; the reason state supplies no burden calculus
and must not (hardwiring `Due` into the graph was the failure mode the
dispatch flagged). `Licensed` is where the reason state pays rent: a
licensing certificate can now cite the occurrence identities it relies on,
their `App` sources give it exactly the defeasible dependency keys R7 asks
for, and defeat of a licence is basis loss of a cited `App` — which narrows
internal-answerability blocker 1 ("a substantive `Licensed` connecting
certificates to reasons, scope and defeat") to: pick the citation discipline
and prove the transport. `Performance` is untouched.

**`I_0 → R_0`.** The reason state is neutral about bootstrapping: seed
schemas and seed occurrences are minted at initialization like anything else,
and the seed's authority is record genealogy, not reason-state structure.
Nothing here spends primitive normativity.

**Enforcement.** Nothing in `𝓡_n` mentions prices, probabilities, utilities
or liability. The credal fragment, if any, enters through claims the compiler
selects — the open `R → O` problem is unchanged in difficulty but now has a
typed left input.

## 13. Recommended interface (provisional)

```text
reason state 𝓡_n:
  V     ::= Atom | Neg V | App(σ, c, n) | Inst(e, σ) | Incomp(P_fin V)
  E     :   occurrences e = (id, s(e) ⊆_fin V ⊎ L, t(e) ∈ V)   append-only
  Σ     :   schema identities                                   bare
  C     :   case identities                                     bare
conventions:
  applicability-in-source; persistence by ordinary schemas
environment:
  L transcript (monotone receipts);  T ⊆ C × L procedural, non-evidential
  D docket items, about : D → C                                  record-side
stance:
  B ⊆_fin V, the learner's; grammar constraints only
queries (total, stateless, mandatory):
  Enabled_B(e), Reasons_B(v), Dependents(x), Explain(e), LostBasis_B(log)
derived (optional, cacheable, policy-labeled where policy-relative):
  bearing, undercuts, rebuts, closure_π, labels_π, nogoods_π
```

## 14. Naming

Provisional, listed for the ruling: **reason state** (`𝓡_n`) versus
**normative record** (`N_{≤n}`) — the wiki currently writes the record as
`Rₙ`, and this round does not rename it; **occurrence**, **schema**, **case
view** (`c@n`), **stance**, **contradiction floor**,
**applicability-in-source**, **persistence schema**, **applicability frame
problem**, `Enabled`, `Reasons`, `Dependents`, `Explain`, `LostBasis`,
`Incomp`, and the module vocabulary in `src/reason_state.py`.

## What is not established

No claim is registered or kernel-checked. The executable witnesses are finite
fixtures, not proofs; the backend-equivalence check covers two backends on
small universes, not the implementation-independence claim in general. The
memo does not construct: a checker for the applicability-in-source
convention; a persistence-schema library or any account of *which*
applicabilities persist; a substantive `Due` or `Licensed`; a stance policy;
a priority calculus; a typed action target sort; the `R → O` compiler; or any
Lean statement. The claim that no further primitive is missing rests on
fifteen prosecution examples, not on a completeness argument, and the
composition of this reason state with the record calculus is designed-for but
not formally verified.

Run the checks with:

```sh
python3 tests/run.py
```
