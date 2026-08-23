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

## Naming

Provisional, for the ruling: **transition certificate**, `basis`, `license`,
`consumed`, `kind`, `KINDS`, **authority act**, `scope`, `Conflict`,
`joint_conflicts`, `criticizable`, `case_view`, `born`, `instantiates`, the
failure-code vocabulary, and the three principle names **strict pre-state
citation**, **constitutive immutability**, **answerability continuation**.

## What is not established

No claim is registered or kernel-checked. The boxed implication in §5 is a
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
