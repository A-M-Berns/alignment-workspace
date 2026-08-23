# The frozen reason-state interface

Status: **provisional freeze; unregistered**. This is the round's recommended
contract, subject to the maintainer's naming and adoption rulings. The
reference implementation is `src/reason_state.py`; nothing about its
implementation choices is frozen.

**A reason state is a reason ledger, not a reasoner.**

## Frozen public types

```text
Content   V ::= Atom(payload)            payload opaque; may carry quantitative
                                         constraint content such as P(A|B) ≥ 4/5
              | Neg(V)                   canonical: double negation unconstructible
              | App(σ, c, n)             schema σ applies on case c's stage-n view
              | Inst(e, σ)               occurrence e is classified under σ (revisable)
              | Incomp(S), |S| ≥ 2       the members of S are jointly unadoptable;
                                         nothing follows about proper subsets

Occurrence e = (id, s(e) ⊆_fin V ⊎ L, t(e) ∈ V, applied_as(e) ⊆_fin Σ×C×ℕ)
              identity-bearing; all components constitutive and immutable;
              the ledger is append-only and identities are never reused

Sorts      Σ (schemas), C (cases): bare external identities
           L: monotone transcript receipts — the settled source sort
Stance     B ⊆_fin V — the learner's, never stored by the ledger
```

Well-formedness (mechanically enforced at minting):

```text
(σ, c, n) ∈ applied_as(e)  ⟹  App(σ, c, n) ∈ s_V(e)
```

`applied_as` is historical schema-use provenance — *this occurrence was
minted as an application of σ to c@n* — and is not recoverable from sources
alone, since an occurrence may cite an `App` claim as an ordinary premise
without being that schema's application. It is disjoint in role from the
revisable classification `Inst(e, σ)`, which never affects enabledness.

Temporal provenance is the ledger's, not the occurrence's: *when* an
occurrence entered the practice is asked through the prefix query below, and
no birth field exists on the frozen occurrence tuple.

## Frozen public queries

All total on every `(B, L)` — including conflicted, irrational, or
floor-violating stances — and all stateless, so a hypothetical query is the
same function at another argument.

```text
Enabled_{B,L}(e)      ⟺  s_V(e) ⊆ B  ∧  s_L(e) ⊆ L
Reasons_{B,L}(v)      =  { e : t(e) = v, Enabled_{B,L}(e) }
Dependents(x)         =  { e : x ∈ s(e) }
Explain(e)            =  (s(e), t(e), applied_as(e))
ExistedBefore(e, n)   ⟺  e entered the ledger strictly before record index n
LostBasis_{B,L}(log)  =  { (m, e, k) ∈ log : ¬Enabled_{B,L}(e) }
Conflict_B(S)         ⟺  (∃x ∈ S. ¬x ∈ S) ∨ (∃ Incomp(T) ∈ B. T ⊆ S)
```

`Enabled`, `Explain`, `ExistedBefore`, and `Conflict` generate the rest;
`Reasons`, `Dependents`, and `LostBasis` are frozen anyway because they are
the names consumers cite. Library conveniences — `bearing`, `undercuts`,
`rebuts`, `joint_conflicts`, `criticizable`, `case_view`,
`provenance_manifest` — are derived and not part of the freeze, though
`Conflict` is frozen precisely so that no consumer reinvents a
pairwise-decomposed conflict semantics.

## Semantic conventions (frozen in role, revisable in content)

- **Applicability-in-source**: enforced as above; `mint_schema_use` is the
  constructor that cannot get it wrong.
- **Staging**: `n` is record time; `App(σ,c,n) ∧ ¬App(σ,c,n)` is a
  correction, `App(σ,c,n) ∧ ¬App(σ,c,m)` for `m ≠ n` can be change.
- **Persistence**: applicability carries across stages only by ordinary
  defeasible persistence schemas, never by substrate default.
- **Views**: `c@n` denotes the case-restricted arrival prefix; external to
  the ledger.
- **Undeclared occurrences**: permitted; whether a cited basis may contain
  them is record-side policy.

## The negative boundary

Deliberately outside the waist, with their homes: stance revision, conflict
resolution, priority, reason strength, reliability weighing, assumption
status, undercutter uptake — **learner policy** (priority, strength, and
reliability *judgments* may ride as ordinary contents); review disposition,
inquiry scheduling, `May`/`Must` rules, authorization genealogy, `Due` —
**normative record**; operative force, traderization, utility and loss,
quantitative optimization — **downstream realization**. Nothing on this list
becomes a reason-state primitive without a concrete counterexample.

## Reopening rule

The interface may be changed only upon presentation of a concrete
microhistory or downstream consumer requirement that cannot be expressed
through the frozen types and queries without importing response policy,
authorization semantics, or rewriting historical provenance.
