# Report — max–min representation of piecewise affine functions

The result, the declaration table, the proof's departure from the source, the
errata and the open items are in
`projects/normativity/rounds/2026-08-18-maxmin-representation/README.md`. This
report carries what that register does not: deviations from the dispatch, what the
work does not establish, the Aristotle log, and the reserved items.

## Deviations from the dispatch

**The dispatch's finding (A) — sign cells instead of connected components — was
not used, and neither was any notion of region.** Finding (B) named density of
`∪T` and geodesic connectivity of the tope graph as the two expensive leaves, and
asked prominently for any route that avoids the second. Neither leaf was proved,
because neither arises: restricting to the segment `[x, y]` turns Lemma 4.1 into an
induction on the crossing parameters of finitely many affine functions of one real
variable, where the linear order on `ℝ` does what the tope graph was needed for,
and where the base case needs agreement of two components at a single parameter
rather than on a common facet. There are no cells, no separation sets, no adjacency
and no arrangement in the development. The theorem, in both directions, came to
about 300 lines.

**Finding (C) was declared and not followed.** The dispatch instructed: "Your Lean
statement must carry `(interior Γ).Nonempty` or work inside the affine hull."
Carrying that hypothesis would have weakened the theorem for no reason — the proof
here needs only that `Γ` is convex and nonempty. The dispatch was right that the
source's *proof* silently needs full-dimensionality; it was wrong that the
*statement* does. Errata 1 and 2 in the round README record both halves, with a
counterexample to the source's `H ≠ ∅`.

**`safe-lake.sh` was not used for the full build.** The resource guard reports
`LOADED` on the swap high-water reading the dispatch itself documents as a false
positive (memory 41% free, load 2.4/10, no Lean workers), and `safe-lake.sh` waits
900 s on that guard and then refuses. The build was run as
`LEAN_NUM_THREADS=2 lake build` — one capped Lean process, the fan-out control the
lock exists to provide — and the axiom audit as
`LEAN_NUM_THREADS=2 python3 tests/audit_axioms.py`. No other Lean process ran
concurrently from this session.

**Aristotle was used once, not "aggressively".** Every leaf closed on the first or
second attempt, so nothing was waiting on a prover. The one submission was the
converse direction, outside the dispatch's target but stated by the source as
Theorem 4.1(b).

## What this does not establish

- **That `IsPiecewiseAffineOn` is equivalent to Definition 2.1.** The implication
  that matters — every Definition-2.1 function satisfies it, so the theorem here
  implies the paper's — is by inspection of the two definitions, not formalized;
  formalizing it would need a Lean rendering of "closed domain", which the paper
  does not define. The definition here is weaker in three respects: pieces need not
  be full-dimensional, need not lie inside `Γ`, and the family `g` need not consist
  exactly of the distinct components.
- **That PR #41's external dependency is discharged.** It is not.
  `ProjectionCompiler.lean` cites two classical facts; this round closes the
  second. The first — that Euclidean projection onto a polyhedron is a piecewise
  affine map of the point projected — is untouched, and without it the projection
  compiler's representation hypothesis stands exactly where it stood.
- **That the result is consumable by the projection compiler as it stands.** No
  adapter from `Finset.sup'`/`Finset.inf'` to `ProjectionCompiler.Rep`'s nested
  lists exists. The conversion is routine; it is also an edit to a file this round
  was scoped away from.
- **Erratum 1's counterexample is hand-checked, not formalized.** That
  `interior ([0,1] × {0}) = ∅` in `ℝ²` is not proved in Lean here.
- **Nothing is registered.** No claim, no statement of record, no `PRIORITIES.md`
  item; the file sits in a contribution namespace, `ci-only`.

## Aristotle log

One project, `6df59235-52ca-4e58-84b2-3e0e7df08d34`, task
`bd961493-bef1-4e3a-bec2-7afa5293a4b2`.

**Submitted.** A self-contained `Converse.lean` — the imports, the
`IsPiecewiseAffineOn` definition, the proved helper `isPiecewiseAffineOn_of_finite`,
and Theorem 4.1(b) with a single `sorry` — plus a `NOTES.md` carrying the intended
proof (index the pieces by `Fin (m+1) × ι × (Fin (m+1) → ι)`, the piece for
`(j, i, k)`, closedness from `isClosed_le`, the cover from
`Finset.exists_mem_eq_sup'`/`exists_mem_eq_inf'` and `choose`), with the instruction
not to modify any statement.

**Returned**, complete, in about eight minutes. The diff against the submitted file
touches nothing but the `sorry`. The proof follows the outline and adds one thing
the outline got wrong: the piece must be guarded by
`if i ∈ S j ∧ ∀ j', k j' ∈ S j' then … else ∅`, because the agreement obligation
quantifies over *all* pieces, including triples whose indices lie outside the
relevant `S j`, on which the equality is false. The submitted outline would not have
closed without that guard.

**Kept**, unmodified except for the `omit` line the unused-section-variable linter
asks for and the surrounding docstring. It was reviewed line by line against the
statement, rebuilt against this repository's mathlib (Lean 4.31.0; Aristotle warned
it prefers 4.28.0, and the returned proof needed no adaptation — it already uses the
4.31 spelling `Set.notMem_empty`), and audits to the allowed three axioms. The
declaration is attributed in `lean/Workspace/Normativity/Contrib/PROVENANCE.md`.

**Rejected:** nothing. **Not submitted:** everything else, because nothing else
resisted.

## New names introduced

All provisional, `AGENTS.md` §6. Namespace `Workspace.Normativity.Contrib.MaxMin`;
file `MaxMinRepresentation.lean`; definitions `IsPiecewiseAffineOn`, `negLine`,
`absComponent`, `absPiece`; theorems `affine_apply_eq_slope`, `affine_eq_of_ne`,
`affine_le_of_lt_of_le`, `exists_forall_eq_of_isPreconnected`,
`exists_le_of_le_of_forall_selects`, `isPiecewiseAffineOn_of_finite`,
`continuousOn_of_isPiecewiseAffineOn`, `exists_le_and_le`,
`exists_maxMin_representation`, `isPiecewiseAffineOn_maxMin`,
`abs_isPiecewiseAffineOn`, `maxMin_hypotheses_nonvacuous`.

## Outstanding maintainer actions

1. Rule on the item appended to `DECISIONS.md`'s *Awaiting the author*: whether the
   names above are confirmed, whether the theorem is promoted to a statement of
   record (which needs a `PRIORITIES.md` item first), and who writes the adapter
   into `ProjectionCompiler.Rep` on the `projection-enforcement` branch.
2. Decide whether to file the remaining external fact — projection onto a
   polyhedron is piecewise affine — as a `PRIORITIES.md` item, since it is now the
   only thing between this theorem and PR #41's spine.

## Model attribution

- **Model:** Claude Opus 5 (Anthropic) — the executor.
- **Prompt author:** unrecorded.
- One Lean declaration, `isPiecewiseAffineOn_maxMin`, was proved by Harmonic's
  Aristotle from a statement and outline written by the executor, and reviewed and
  rebuilt by the executor.
