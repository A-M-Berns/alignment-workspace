# Reason-accounted transition certificates: closing the waist

Status: **research memo; unregistered**. All names are provisional under
`AGENTS.md` §6. General statements are design arguments and paper derivations
supported by finite executable witnesses in `src/` and `tests/`; nothing is
registered or Lean-checked. This round is based on the PR #48 head and
neither merges nor promotes it.

## Verdict

**The transition interface closes: three principles do the work of the five
proposed postulates, and Licensed becomes record-internally substantive.**
Part I found and repaired four defects in the PR #48 representation — one of
them, the incompatibility semantics, was wrong in exactly the direction the
dispatch predicted. Part II's certificate needs only three fields of citation
beyond its own identity — grounds, license, lineage — and every
self-certification attack dies on two clauses with no dedicated
non-laundering axiom.

## 1. What survived from PR #48

- The five-constructor content language, identity-bearing append-only
  occurrences, bare schema and case identities, external stance, and the
  total stateless query interface. All queries carry over unchanged in
  meaning.
- `Inst` outside enabledness: schema reclassification and cross-cutting
  organization never touch what a cited basis depended on (retested after
  certification — dispatch fixtures 8 and 9).
- Staged applicability and the persistence discipline: the
  corrected-belief/changed-world separation, and persistence as an ordinary
  defeasible schema, now exercised across two cases where the learner adopts
  the carry in one and declines it in the other (fixture 14).
- The substrate/policy boundary: the certificate checker adjudicates citation
  discipline only. A licitly certified transition into a criticizable stance
  is accepted and left to the criticism machinery
  (`TestCheckerDoesNotAdjudicate`), because refusing it would make the
  checker enforce stance coherence — a norm.
- Reliance monitoring at occurrence identity, now consumed by the
  certificate's frozen citation rather than a bare log.

## 2. What failed and why

1. **`Incomp` had the wrong semantics — backwards from the dispatch's
   worry.** PR #48's `incompatible(a,b,B)` tested `{a,b} ⊆ S` against each
   adopted `Incomp(S)`, so a ternary conflict *implied* every pairwise
   conflict; joint impossibility with pairwise compatibility was
   unrepresentable. Repair: the set-level query
   `Conflict_B(S) ⟺ (∃x∈S. ¬x∈S) ∨ (∃ Incomp(T)∈B. T ⊆ S)` — an adopted
   incompatibility binds exactly its member set and every superset, never a
   proper subset. Binary rebuttal is the two-element special case and is now
   deliberately incomplete for conflict; `joint_conflicts` exposes what it
   cannot. `Incomp` itself survives as the reified content — the abstraction
   was right, its consumption was wrong.
2. **Canonical negation was a convention, not a fact.** `Neg(Neg(x))` was
   directly constructible as a claim distinct from `x`. Repair: double
   negation is unconstructible (`Neg` refuses a negated body), so `¬¬x = x`
   holds by there being no second object. On the floor's minimality: with
   `Incomp` now genuinely n-ary, the floor could in principle shrink to
   *nothing* by encoding `x`/`x̄` as paired atoms under adopted
   `Incomp({x, x̄})` — but then the correction reading of staged
   applicability (`¬App` contradicting `App`) becomes revisable content, and
   the reflective language loses the one conflict that must be intelligible
   before any incompatibility is learned. The floor stays: one involutive
   negation, no other connectives, none forced by any fixture.
3. **`c@n` was an identity tag with no semantics.** Repair, kept external to
   the reason state: `View(c,n) =` the receipts procedurally tied to `c`
   whose record arrival index is `≤ n`. Views are prefix-determined and
   monotone; two global histories with the same `c`-restricted prefix induce
   the same view (tested), so `App(σ,c,n)` is applicability to the case's
   stage-`n` evidential situation, not to a global record position. The
   record-time choice survived its attack: a delayed receipt about an old
   case extends later views only, and grounds an ordinary *correction*
   targeting the old staged claim — retroactive learning without retroactive
   view change (fixture 3). World-time stays out as unobservable;
   receipt-time is arrival order, which is what the view already uses. `App`
   needs no more structure; `Case` stays thin.
4. **Applicability-in-source was unenforceable.** PR #48 stated it as a
   convention the types could not see, because *which* schema an occurrence
   presents itself as applying was recorded nowhere structural. Repair:
   occurrences carry a constitutive `instantiates` declaration — frozen
   provenance, like sources — and minting refuses a declared instantiation
   whose staged `App` claim is missing from the sources. The check is
   grammar: it never judges whether the schema applies, only that the
   occurrence says what its application depends on. The unconditional form
   is too strong — a seed or brute reason instantiates nothing — so the
   condition is *declared → App-in-source*, and whether a cited basis may
   contain undeclared occurrences is record-side policy. A joint declaration
   of several schemas depends on all its `App` claims; independence is
   minted as separate occurrences.
5. **Occurrences had no birth index**, so "this occurrence predates the
   transition" — the load-bearing clause of the whole certificate discipline
   — was inexpressible. `born` is now constitutive.

## 3. Final reason-state interface

```text
V     ::= Atom | Neg V (canonical, no ¬¬) | App(σ,c,n) | Inst(e,σ) | Incomp(S), |S| ≥ 2
E     :   e = (id, s(e) ⊆_fin V ⊎ L, t(e) ∈ V, born(e) ∈ ℕ, inst(e) ⊆_fin Σ×C×ℕ)
          append-only; identities never reused; all five components constitutive
          well-formedness: (σ,c,n) ∈ inst(e) ⟹ App(σ,c,n) ∈ s(e)
Σ, C  :   bare identities
views :   View(c,n) = case-restricted arrival prefix; external; App keeps (σ,c,n) identity
queries (total, stateless, mandatory):
  Enabled_B(e), Reasons_B(v), Dependents(x), Explain(e), LostBasis_B(log)
conflict (derived, stance-relative):
  Conflict_B(S); incompatible = Conflict on pairs; joint_conflicts over live targets;
  criticizable(B) = Conflict_B(B)
```

## 4. Final transition-certificate interface

```text
Cert(m) = (move, kind ∈ KINDS, index n, basis ⊆_fin E-ids, license ∈ Act-ids,
           consumed ⊆_fin commitment-ids)
KINDS   = belief-revision | practical-undertaking | schema-reclassification
        | rule-amendment | inquiry-launch
Act     = (id, index, seed?, license_parents, scope ⊆ KINDS)   [record-side stand-in]

check(𝓡, Acts, Commitments, cert, B_pre, arrivals) — every clause explanatory:
  basis     nonempty; each cited e exists, born(e) < n, Enabled under
            (B_pre, {r : arrival(r) < n}); failure names the occurrence and a
            missing source
  license   cited act exists, index < n, kind ∈ scope, genealogy seed-terminating
            with strictly earlier parents
  lineage   each consumed commitment exists and predates n
  receipt   frozen snapshot of cited constitutive structure — derivable from
            the append-only store, kept as convenience, reproducible later
derived:  ApplicabilityProvenance(cert) = App claims among cited sources
          TransitionLostBasis(cert, B, L) = cited e with ¬Enabled — never
          silenced by alternative support
Licensed(S,d,a) ⟺ ∃ well-formed cert for (respond a to d) valid in S
```

Answers to the dispatch's candidate requirements:

- **A. Finite cited basis — necessary.** Two occurrences with identical
  sources and target, different histories: conclusion- or content-level
  citation cannot say which one the transition relied on, so review could
  not target the actual reliance (`TestCitationNecessity`).
- **B. Pre-state validity — strictly earlier, uniformly.** Basis birth,
  license act index, lineage birth, and transcript arrivals are all `< n`;
  enabledness is at `B_pre`. Nothing else needs freezing: the receipt is
  redundant given immutability (reproducibility test), which is why it is a
  convenience and not a primitive.
- **C. Applicability provenance — derived, not restated.** The `App` claims
  are read off the cited constitutive sources, so the certificate cannot
  misstate them, and basis-loss review needs nothing further: withdrawing
  exactly those claims is what disables the citation.
- **D. License versus grounds — separate field, different sort.** The
  license cites a record-side authority act with a typed scope, not an
  occurrence; the conflation kill test (fixture 15) shows a pooled checker
  accepting an ordinary reason as authority where the repaired checker
  refuses. The act is a deliberate stand-in for the record's `May`-rule
  machinery; compiling rules into scopes is the named record-side gap (§8).
- **E. Target/scope typing — `Licensed : S → D → A → Prop` stands.** All
  five transition kinds run through one certificate shape with `kind`
  checked against the license scope; no richer target typing was forced by
  any fixture.
- **F. Basis loss — composes with the record.** Same conclusion different
  basis, substitute support, post-certification reclassification, stage-4
  persistence over a withdrawn stage-3 reliance, and a defeated underlying
  incompatibility: all report at the frozen citation; none is silenced
  (`TestBasisLossAfterCertification`). What follows from a report is the
  record's review law, consumed, not reimplemented.
- **G. Non-laundering — no new axiom.** All six attacks die on clauses
  already present: self-minted basis and license fall to strict priority;
  mutual licensing falls to the genealogy's strictly-earlier-parent rule;
  reclassification cannot rewrite frozen declarations; a later receipt or
  richer stance cannot flip a check that is a function of the pre-state
  prefix; a later persistence judgment addresses a different staged claim
  than the one relied on.

## 5. Which postulates are independent

The dispatched five compress to three; two of the five are not certificate
postulates at all.

| Proposed | Fate |
|---|---|
| 1. Basis | absorbed into Principle 1 |
| 2. Prior license | absorbed into Principle 1 |
| 5. No self-grounding | **a theorem, not an axiom**: the checker has no self-grounding clause, and every self-certification fixture is refused by priority or genealogy codes alone (`test_no_self_grounding_clause_exists_yet_the_attacks_fail`) |
| 3. Conservation / lineage | the record's account law; the certificate contributes only the input-scoped `consumed` citation it consumes |
| 4. Defeat sensitivity | decomposes: frozen citation (certificate) + `LostBasis` detection (substrate) + review minting (record) |

The three surviving principles, each with a minimal failure witness and its
consumer:

1. **Strict pre-state citation.** Finite particular basis, prior scoped
   license, existing prior lineage, all checked against the pre-state
   prefix. *Witness:* the lax checker without the posterior clauses accepts
   a transition citing a reason minted by itself. *Consumers:* No New
   Normative Roots, all of §4 G. *Lives in:* the certificate checker.
2. **Constitutive immutability.** Append-only identities; frozen sources,
   targets, declarations; check verdicts a function of frozen inputs.
   *Witness:* mutating sources or declarations raises; were it permitted,
   reclassification would rewrite claimed historical basis. *Consumers:*
   `ValidWhenUsed` versus `StandsNow`, receipt reproducibility. *Lives in:*
   the reason state's structure.
3. **Answerability continuation.** The frozen citation stays monitored:
   `LostBasis` over cited identities feeds the record's edge-triggered
   review. *Witness:* conclusion-level monitoring reports nothing while the
   cited basis is gone and a substitute stands. *Consumers:* No Forgotten
   Basis Loss. *Lives in:* substrate query plus record law.

Theorem-shaped statement (finite-test-supported; the record side is consumed
from the internal-answerability round, not reproved):

> Every admitted transition carries a certificate valid under strict
> pre-state citation (1), over an immutable append-only structure (2), with
> its citation wired into `LostBasis` and the record's review minting (3)
> ⟹ no transition can be self-certified or mutually certified, its claimed
> historical basis cannot be rewritten, and every later loss of a relied-on
> basis is detected at the frozen citation and enters the review calculus.

The frozen-citation detection clause is exhaustively checked over every
stance on a small claim universe (`TestFrozenCitationLocality`); the rest is
witnessed on the named fixtures.

## 6. Licensed verdict

`Licensed(S,d,a)` is now a nontrivial object: witnessed by a certificate,
refused for identifiable reasons, and mechanically defeasible. The fixtures
separate it in both directions — valid genealogy with absent grounds fails
exactly on grounds; excellent grounds without scoped authority fails exactly
on scope — so licence is not derivable from support, which is the
independence the response-learning interface always demanded. What a valid
certificate establishes is exactly *licensed within the current accountable
practice*: no clause judges whether a cited `App` is true or the practice
apt.

Against the internal-answerability kernel's axioms: R1 conclusion binding —
the certificate names its move, kind, and index; R2 pre-state check — §4 B;
R3 immutable receipt — reproducible frozen snapshot; R4 dependency
extensionality — enabledness is local to cited sources (inherited, retested
via the sweep); R5 explanatory failure — every failure names the offending
citation and, for enabledness, a missing source; R6 checker closure — the
checker's own version sits outside the structure, as there; R7 finite
invalidation key — the cited `App` claims are the finite defeasible keys.

**The exact remaining blockers, named:** (i) `AuthorityAct.scope` is a
stand-in — the real object is the record's versioned `May` rules, and the
compiler from rules to certificate-checkable scopes is record-side work not
done here; (ii) R7's residue moved rather than vanished: a defeater the
practice has not yet taken up into its stance is invisible to `LostBasis`,
so detection-completeness is an inquiry/uptake obligation of the record, not
a certificate property; (iii) `Due` is untouched — nothing here generates
burdens. None of these is a smuggled normative judgment inside the checker;
all three are honest handoffs.

## 7. What remains policy rather than substrate

Stance selection and revision; conflict resolution among live reasons;
adopting or declining applicability and persistence claims; priority
weighing; choosing *which* licensed transition to perform; whether a basis
may contain undeclared occurrences; review disposition after a basis-loss
report. The checker is grammar over citations; the substrate is queries; the
record accrues, reviews, and accounts.

## 8. What remains genuinely open

- The `May`-rule-to-scope compiler (§6 i), which is where substantive
  authorization content actually lives.
- Defeater-uptake completeness (§6 ii): what the practice owes by way of
  processing new defeaters into the stance so that `LostBasis` sees them.
- The `Due` connection: due token → docket item → certified response,
  closing the response-learning loop on one fixture.
- A persistence account: which applicability families warrant carry, and at
  what review cost.
- Lean statements of Principles 1–3 and the boxed implication over finite
  histories, if selected for promotion.
- Typed action targets, priorities, and everything PR #48 already listed as
  open and this round did not touch.

## Mapping to prior interfaces

| This round | Existing object |
|---|---|
| `basis` / `license` / `consumed` | grounds / normative license / account incidence (afoundational round §1) |
| `check_certificate` failure codes | R5 explanatory failure; strict pre-state = R2 |
| `AuthorityAct`, `genealogy_errors` | seed-terminating authority genealogy (No New Normative Roots) |
| `transition_lost_basis` | `UsedAt` + `BasisLost` edge trigger (internal-answerability §6) |
| `consumed` citations | account DAG inputs (role-parametric account law) |
| `Licensed` witness | crown-jewel `Licensed(S,d,r)` interface slot |
| omitted policy layer | PR #48's `support_closure`/labels/nogoods — unchanged there |

## 9. Narrow-waist closure phase

A late-stage addendum to the dispatch asks a stricter question than whether
the representation handles the examples: is the interface now stable enough
that future work should occur above it? Closure here is a
research-engineering status indexed to the known consumers and the
accumulated fixture corpus of both rounds, not a uniqueness or minimality
theorem.

### 9.1 Criterion

The addendum's five-clause criterion is adopted with one tightening of
clause 2: consumers must obtain what they need through the public types and
queries *without inspecting representation internals or adding hidden
semantic fields* — which is how this round in fact ran, since the
certificate checker consumes only `Enabled`, the constitutive lookups, and
record-side objects. Under that criterion the verdict must also record that
this round itself *forced two constitutive additions* (`born`,
`instantiates`) before its consumer could be served: the boundary was found
by pressure, not assumed.

### 9.2 Prosecution by subtraction

Each surviving primitive was attacked by removal; each removal has a
concrete loss, witnessed in `tests/test_closure.py` where a finite witness
exists.

| Primitive | Removal attempt | Loss |
|---|---|---|
| occurrence identity | identify by `(sources, target)` | two historically distinct applications collapse; reliance logs and basis-loss reports become ambiguous (witnessed; also `TestCitationNecessity`) |
| hyper-sources | compile `{a,b}` through a conjunction vertex | nonconservative: the compiled edge waits on a claim the learner never adopted, and the compilation invents reason applications the practice never performed — keeping them synced is hidden bookkeeping policy (witnessed) |
| two source sorts | mirror receipts as claims | either transcript facts become withdrawable, breaking settlement, or an indefeasible-claim subtype appears that *is* the receipt sort renamed — a relabeling, not a reduction |
| `App` constructor | encode as ordinary atoms; attack edges; case-indexed schemas; negative dependencies | atoms are expressible but grammar-invisible: applicability-in-source and `ApplicabilityProvenance` become naming conventions nothing can check; attack edges and outlists move policy into structure (round 1); case-indexed schemas destroy cross-case schema learning and still need staging |
| `Inst` | recover organization from `instantiates` provenance | provenance is frozen, so the learner could not disagree with a classification without rewriting history; the revisable half is exactly what `Inst` carries (round 1 example 5) |
| stage index | unstaged `App`, or any unordered replacement | corrected-belief and changed-world collapse; any adequate replacement orders applicability claims by record position, which is a stage index up to isomorphism |
| contradiction floor | make all incompatibility revisable | at the empty stance nothing marks a correction as a correction: `App` versus `¬App` would conflict only under an adopted norm, so the reflective language could not state its own corrections (witnessed). The floor is representational — it fixes what the tilde means and generates criticism-content; it obliges no response, and floor-violating stances stay representable |
| `Incomp` | ordinary atoms or feasibility predicates | atoms lose the typed member set that `Conflict` computes containment over; feasibility is downstream semantics. The constructor survives with the §2 repair |

The characterization audit: "append-only identity-bearing directed
multi-hypergraph plus a stance marking" is accurate **as a labeled
structure** — `E` carries constitutive labels (`born`, `instantiates`)
beyond `(s, t)`, sources split over two sorts, and `B` is a separate finite
marking of `V`, not a component of the graph. "Multi" and "hyper" are both
essential (first two rows above); schemas and cases are correctly external
identity sorts reached only through reflective constructors. A bare
`(V,E,s,t)` reading is lossy and should not be used.

### 9.3 Prosecution by addition — the negative boundary

Every plausible missing primitive classifies as something the interface
already provides. None is `GENUINELY MISSING PRIMITIVE`.

| Candidate | Class | Reason |
|---|---|---|
| `Undercuts` | derived query | `¬App` target meeting a source, under enabledness |
| `Rebuts` | derived query | `Conflict` on a target pair; incomplete for n-ary conflict by design |
| `Priority` | existing content | ordinary revisable claims (Horty variable-priority precedent); their *consumption* is learner policy |
| `Reliability` | existing content | ordinary claims about sources/schemas; distinct from applicability (tested) |
| `EvidentialRelevance` | existing content | relevance claims, plausibly `App` of evidential schemas |
| `Hold` / `Do` | existing record fact | commitment contents in the record's occurrence machinery |
| `May` / `Must` | existing record fact | versioned rule modes; their compilation into scopes is the named downstream gap |
| `Supported` / `Live` | derived query | `Reasons` / `Enabled`, asked rather than asserted |
| `Defeated` | derived query | undercut-or-rebutted at `B`; the priority-weighing sense is learner policy |
| `Assumption` | learner policy | a withdrawability label on stance members — de Kleer's observation that assumption-status is context-dependent, resolved by making it the policy's label |
| `Context` / `Environment` | derived query | cached hypothetical-support queries (round 1's policy layer) |
| `CaseView` | derived query | the case-restricted arrival prefix, computed from record and transcript |
| `SameCase` | existing content | revisable identity judgments (tested); acting on one is a record act |
| `SchemaSuccessor` | existing content | continuity judgments; the split/merge act is a record fact |
| `ReasonStrength` | learner policy | graded weighing; strength *judgments* could ride as content, but a strength primitive in structure would smuggle the weighing conception into the substrate |

### 9.4 Consumer-completeness

| Consumer | Needs | Supplied by | Needs new primitive? |
|---|---|---|---|
| normative learner | bearing, conflicts against a candidate stance, hypothetical enabledness, organization open to reasons | `Reasons`/`bearing`; `Conflict`/`joint_conflicts`/`criticizable`; same queries at `B'`; `Inst`/`App` as targets | no |
| historical answerability | exact relied-on occurrence, its sources later, loss detection, alternative-vs-original | identity + `Explain`; `LostBasis` over frozen citations (substitute support never silences, tested) | no |
| `Licensed` | particular occurrences, applicability dependencies, case/stage, pre-state enabledness; authorization record-side | certificate `basis` + derived `ApplicabilityProvenance` + `App` arguments + strict pre-state check; license as a separate record sort | no — but it *did* force `born` and `instantiates` during this round, now part of the interface |
| inquiry | occurred-during versus taken-to-bear versus docketable trouble | `T` non-evidential; relevance/`App` claims; `Conflict` and `LostBasis` reports as docketable conditions | no |
| operative compiler | endorsed content, bearing, cited bases, applicability, organization, case/stage, reliance | `B` vs `Reasons`; certificates; `Inst` claims + provenance; `App` args; record `UsedAt` | no |

### 9.5 Representation-versus-policy audit

Every checker and invariant shipped by the two rounds, audited against
"well-formedness or response-adjudication": identifier uniqueness,
receipt-not-target, `Incomp` arity, canonical negation, declared-implies-
cited, and every certificate clause are grammar over structure and
citations. The one honest borderline is the certificate's nonempty-basis
clause: it does not oblige transitions to have reasons — it defines what a
*reason-accounted* transition is, and an unreasoned transition simply has no
certificate, which the record may then criticize. Stance consistency,
closure, conflict resolution, priority, persistence adoption, undercutter
uptake, mandatory review, strength, and schema choice are enforced nowhere;
criticizable and even floor-violating stances stay total
(`TestCheckerDoesNotAdjudicate`, closure witnesses). No shipped invariant
rules out behavior that later legitimacy theory is supposed to criticize.

### 9.6 Microhistory search

The addendum's nineteen classes, asked only as "is the content and
dependency structure expressible": fourteen were already fixtured across the
two rounds; the five genuinely new ones are now tested — testimony about
testimony (chained applications), a reason that a source is unreliable *but
not inapplicable* (bears on the reliability claim; a separate mintable
bridge carries it to `¬App`), circular support and mutual undercutting
(total, exposed, unresolved), case-merge judgments and their retraction, and
one receipt bearing differently on two cases. Permissions versus positive
reasons is the certificate's grounds/license separation itself; reasons to
investigate ride as inquiry-launch contents; priority change is revisable
content; scorekeeper conflict is free because every query is
stance-parametric (tested). Nothing in the sweep required a new
representational kind.

## Narrow-waist closure verdict

```text
Verdict: CLOSED-PROVISIONALLY

Core representation:
  V ::= Atom | Neg V (canonical) | App(σ,c,n) | Inst(e,σ) | Incomp(S), |S| ≥ 2
  E : e = (id, s(e) ⊆_fin V ⊎ L, t(e) ∈ V, born, instantiates) — append-only,
      constitutive, well-formed iff declared instantiations cite their App
  Σ, C bare identity sorts; L monotone receipts; B ⊆_fin V a separate stance
  Queries: Enabled, Reasons, Dependents, Explain, LostBasis;
  Conflict / joint_conflicts / criticizable as public derived queries

Why each primitive survives: §9.2 — every removal loses a fixtured
  distinction: identity → answerability; hyper-sources → conservativity;
  two sorts → settlement; App → checkable reflective criticism; Inst →
  revisable organization without history rewrite; stages → correction vs
  change; floor → statable correction; Incomp → typed n-ary conflict.

Negative boundary — what is deliberately outside: §9.3 — attack relations,
  Supported/Live/Defeated, contexts and environments as derived queries;
  priority, reliability, relevance, same-case and schema-continuity as
  ordinary content; Hold/Do/May/Must as record facts; assumptions and
  strength as learner policy. No candidate classified as missing.

Consumer-completeness result: all five known consumers served through the
  public interface with no new primitive (§9.4). This round's own consumer
  forced born and instantiates before closing — the criterion's clause 5
  operated once, and now holds.

Remaining representation-open blockers: none known.

Remaining semantics-open questions: truth conditions of App against the
  case view (the view fixes the situation; schema semantics is open);
  whether views need docket events beyond receipts; the typed content
  language refining Atom; Incomp member typing for action contents.

Remaining policy/theory-open questions: stance revision, conflict
  resolution, priority, persistence adoption, review disposition,
  defeater-uptake completeness, the May-rule-to-scope compiler, Due,
  and the learning connection.

Freeze recommendation: freeze the public types and queries listed above.
  A new primitive or breaking change requires a minimal counterexample
  showing some required reason structure cannot be expressed through the
  existing interface without importing learner policy or rewriting
  constitutive provenance. Provisional (frozen in role, revisable in
  content): applicability-in-source scope, persistence-by-schema,
  record-time staging, view semantics, undeclared-occurrence basis policy.
  Explicitly outside the freeze: the certificate layer (one round old),
  the AuthorityAct stand-in, the policy layer, caching strategies, and
  all implementation choices.

Minimal evidence that would reopen the interface: a concrete microhistory
  whose reason-dependency structure cannot be expressed via contents,
  occurrences, record facts, or derived queries — with the artifact, not
  an intuition — or a consumer whose required fact is unqueryable.
```

Future work should stop touching the reason representation and build
revision, authorization, and legitimacy above it.

## 10. Continuation: finishing and freezing the waist

A continuation dispatch on this pull request asked for a stricter end state:
finish the waist, freeze it, and leave contracts to both sides without
solving either side. The frozen contract is stated in
`REASON_STATE_INTERFACE.md`; the two consumer contracts are
`INQUIRY_HANDOFF.md` (left) and `FRONTIER_HANDOFF.md` (right). This section
records the decisions and their prosecution.

### 10.1 The two late-added fields, placed

**`born` is removed from the occurrence.** The deciding question — does any
consumer need *when it entered* as a fact about the reason object, or only
prefix existence — came out uniformly on the prefix side: the certificate
checker, the only consumer of birth, needs exactly `e existed strictly
before n`. Temporal provenance therefore belongs to the append-only ledger,
whose own history carries it; the public temporal fact is the query
`ExistedBefore(e, n)`, and `Explain` no longer returns a stamp. The
subtraction witness transfers from the field to the capability: without any
temporal prefix access, the self-minted-basis attack passes (the lax-checker
witness); with the prefix query, it is refused as before (retested). The
minting stamp survives inside the implementation, which the freeze
deliberately does not cover.

**`instantiates` is renamed `applied_as` and stays constitutive on the
occurrence.** The distinction it carries against `Inst` is now stated in the
contract: *minted as an application of σ to `c@n`* (historical fact) versus
*correctly classified under σ* (revisable judgment). It cannot move to the
record without letting occurrence and registry drift apart — the
well-formedness check is local to minting — and it cannot be dropped,
because schema-use is not recoverable from sources: an occurrence may cite
an `App` claim as an ordinary premise without being that schema's
application. The typed-constructor option was adopted *in addition*:
`mint_schema_use` inserts the staged `App` source and the provenance
together, so the load-bearing invariant is enforced twice — by construction
on the convenient path and by well-formedness on the general one (both
tested, including their agreement).

### 10.2 The public API, minimized

Frozen queries: `Enabled`, `Reasons`, `Dependents`, `Explain`,
`ExistedBefore`, `LostBasis`, `Conflict` — of which `Enabled`, `Explain`,
`ExistedBefore`, and `Conflict` are a generating basis; the other three are
frozen because consumers cite them by name. `Conflict` is frozen despite
being derivable precisely so no consumer reinvents the pairwise-decomposed
semantics this round repaired. `bearing`, `undercuts`, `rebuts`,
`joint_conflicts`, `criticizable`, `case_view`, and `provenance_manifest`
are library conveniences outside the freeze.

### 10.3 Quantitative content, qualitative stance

The waist must not restrict contents to Boolean propositions, and does not:
`Atom` payloads are opaque, so a content like `P(rain|front) ≥ 4/5` rides as
ordinary content — reasons bear on it, a stance endorses it by membership,
a certificate cites reliance on it, and the manifest hands its provenance
over, all on one fixture (`test_handoff.TestRightHandoff`). The coefficients
live inside the content; endorsement remains membership. The quantitative
book itself stays downstream.

### 10.4 The notebook, the stance, and the diary

The human-facing picture: **the notebook (`𝓡`) remembers particular reasons
and their dependencies; the current view (`B`) records what is presently
endorsed; the diary (`N`) binds what was actually undertaken, relied on,
licensed, and accounted for. A reason state is a reason ledger, not a
reasoner.** Each attempted collapse of the three has a minimal failure
witness (`test_handoff.TestNotebookStanceDiarySplit`): folding the ledger
into the stance deletes disabled reasons and makes a reliance loss
unreportable exactly when it matters; folding the stance into the diary
makes every hypothetical query need a fake record event; folding endorsement
into the graph makes support imply endorsement, which is the closure policy
the substrate exists to refuse. The split stands as an architecture
decision, and it carries the frontier design constraint stated in the right
contract: arbitrary stance may be queried; only diary-bound stance may
acquire operative force.

### 10.5 Freeze verdict

```text
Verdict: FROZEN-PROVISIONALLY

1. every public primitive has an explicit subtraction witness       yes (§9.2, §10.1)
2. born and schema-use provenance placed at the correct layer       yes (§10.1)
3. applicability-in-source mechanically enforced, twice             yes (§10.1)
4. quantitative content expressible, stance stays qualitative       yes (§10.3)
5. no known inquiry consumer needs a new reason primitive           yes (INQUIRY_HANDOFF)
6. no known frontier consumer needs a new reason primitive          yes (FRONTIER_HANDOFF)
7. notebook/stance/diary split survives attempted collapse          yes (§10.4)
8. remaining gaps classify cleanly by downstream area               yes (§10.6)

Reopening rule: the interface may be changed only upon presentation of a
concrete microhistory or downstream consumer requirement that cannot be
expressed through the frozen types and queries without importing response
policy, authorization semantics, or rewriting historical provenance.
```

### 10.6 Open problems, by area

```text
representation:                  none known
inquiry/coverage:                exposure norms, interpretation norms,
                                 docketing thresholds, service under load,
                                 defeater-uptake completeness
revision/reflective integrity:   stance revision policy, conflict resolution,
                                 priority and strength, persistence adoption,
                                 review disposition
authorization:                   the May-rule-to-scope compiler; substantive
                                 standing beyond the AuthorityAct stand-in
frontier compilation:            defining the record-accounted stance B̂_n;
                                 joint semantics of endorsed quantitative
                                 contents; the credal compiler (item 39)
operative force:                 unchanged — consumes the compiler's output
                                 under its existing liability interface
```

## Naming

Provisional, for the ruling: **transition certificate**, `basis`, `license`,
`consumed`, `kind`, `KINDS`, **authority act**, `scope`, `Conflict`,
`joint_conflicts`, `criticizable`, `case_view`, `applied_as`,
`ExistedBefore`, `mint_schema_use`, `provenance_manifest`, the
failure-code vocabulary, the three principle names **strict pre-state
citation**, **constitutive immutability**, **answerability continuation**,
the freeze statuses (`FROZEN-PROVISIONALLY` family), and the human-facing
triple **notebook / current view / diary** with the sentence *a reason state
is a reason ledger, not a reasoner*.

## What is not established

No claim is registered or kernel-checked. The closure and freeze verdicts
are research-engineering statuses indexed to the known consumers and the
accumulated fixture corpus; neither is a uniqueness, minimality, or
completeness theorem, and the reopening clause is part of both. The freeze
itself is a recommendation — enacting it is the maintainer's. The
handoff contracts constrain future layers; they do not build them, and the
frontier constraint on diary-bound stance is a design rule, not a theorem.
The
boxed implication in §5 is a
paper derivation whose clauses are individually finite-test-supported; only
the frozen-citation locality clause is exhaustively checked, and only on a
small universe. The round does not construct: the rule-to-scope compiler; a
burden generator; a stance policy; review disposition; a proof that three
principles remain sufficient under richer transition kinds; or any Lean
artifact. `AuthorityAct` deliberately under-models the record's rule
machinery, and the composition with the full account calculus is mapped, not
verified.

Run the checks with:

```sh
python3 tests/run.py
```
