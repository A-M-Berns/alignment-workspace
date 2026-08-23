# Closeout report

**Attribution.** Prompt author: user, model not stated. Executor: Claude
Fable 5 (Anthropic). Dispatched and executed 2026-08-23, continuing PR #49 on
its existing branch.

**Verdict.** `FROZEN-PROVISIONALLY`. The waist is finished and frozen: the
two late-added constitutive fields are placed at their correct layers, the
public contract is stated in `REASON_STATE_INTERFACE.md` with its reopening
rule, and both downstream programs receive explicit consumer contracts —
`INQUIRY_HANDOFF.md` on the left, `FRONTIER_HANDOFF.md` on the right —
without either being developed here. Sixty-seven tests, all green.

## Findings

1. `born` was redundant as a public field: its only consumer needs the
   prefix fact, not a birth stamp. It moved to ledger provenance behind the
   frozen query `ExistedBefore(e, n)`; `Explain` no longer returns temporal
   data, and the self-minted-basis attack is refused as before. The
   subtraction witness attaches to the temporal *capability*, which is
   load-bearing, not to the field, which was not.
2. Schema-use provenance stays constitutive on the occurrence, renamed
   `applied_as`: it cannot be recovered from sources (an occurrence may cite
   an `App` claim as an ordinary premise without being that schema's
   application) and cannot move to the record without letting occurrence and
   registry drift. The typed constructor `mint_schema_use` was added, so the
   applicability-in-source invariant is enforced twice — by construction on
   the convenient path, by well-formedness on the general one.
3. The frozen public API is seven queries — `Enabled`, `Reasons`,
   `Dependents`, `Explain`, `ExistedBefore`, `LostBasis`, `Conflict` — of
   which four generate the rest; `Conflict` is frozen despite derivability
   so no consumer reinvents the pairwise-decomposed semantics this round
   repaired. `bearing`, `joint_conflicts`, `criticizable`, `case_view`,
   `provenance_manifest` and the attack relations are library conveniences
   outside the freeze.
4. Quantitative contents ride as opaque `Atom` payloads under a qualitative
   stance: one fixture carries `P(rain|front) ≥ 4/5` through reasons,
   endorsement, a valid certificate, basis loss, and the provenance
   manifest, without any change to the stance type.
5. The provenance manifest gives the frontier its settled-versus-defeasible
   split: `(ReceiptDeps, ClaimDeps)` with internally supplied targets closed
   off — syntactic, computable, and exactly what the two-sorted source
   structure was for. Fundability and settlement safety are explicitly not
   claimed.
6. The notebook/stance/diary split survived all three attempted collapses
   with minimal witnesses: pruning the ledger to enabled reasoning makes a
   reliance loss unreportable exactly when it matters; deriving the stance
   from the record makes hypothetical queries need fake events; storing
   endorsement in the graph makes support imply endorsement. The frontier
   design constraint is recorded: arbitrary stance may be queried; only
   diary-bound stance may acquire operative force.
7. Defeater-uptake completeness is recorded as not a representation
   problem: once uptake occurs the waist represents the defeater and every
   detection works; what uptake is owed is left-side theory.
8. All eight freeze criteria hold; the remaining gaps classify cleanly into
   inquiry/coverage, revision, authorization, frontier compilation, and
   operative force, with the representation column empty.

## Deviations

- The continuation was executed inside this round rather than a new
  subdirectory, as the dispatch prefers and governance permits; its prompt
  and this report follow the existing `-closeout` convention.
- `REASON_STATE_INTERFACE.md` and the two handoff notes live in the round
  directory, not `projects/normativity/notes/` — installing living notes is
  the maintainer's call, already queued in `DECISIONS.md`.
- The dispatch's `SchemaUse(id,G,σ,c,n,q)` desugaring was adopted as an
  additional constructor rather than a replacement for the general mint,
  because seed and brute reasons apply no schema and still need minting.

## What was not shown

The freeze is a recommendation indexed to the known consumers and fixture
corpus; enacting it is the maintainer's. The handoff contracts constrain
future layers without building them; the diary-bound-stance rule is a design
constraint, not a theorem; `B̂_n` is deliberately undefined; and the
manifest's adequacy for the eventual compiler is untested beyond the finite
fixture. Nothing is registered or kernel-checked.

## Outstanding maintainer actions

1. Rule on the round's vocabulary and on enacting the freeze — the single
   `DECISIONS.md` queue entry now covers both, with the two entries from the
   #48 round still open above it.

## Recommended next pass

Unchanged from the main report, now sharpened by the contracts: build the
`May`-rule-to-scope compiler record-side and define `B̂_n` against the
frontier contract, then run due token → docket item → certified response →
manifest handoff on one fixture, touching the frozen waist not at all.
