# One ground type

## 1. The diagnosis: what a disposal must be able to cite, and what held it

A disposal says *this content is not owed, and here is why*. The "why" is a set of
occurrences already in the record. Four kinds of occurrence can appear in it.

| a disposal may cite | where the pre-unification spine held it |
| --- | --- |
| **a prior issue** — outstanding or already resolved | `TraceData.O` / `Res` / `Born` over `Q`, related by `anc` |
| **a standing fact** — a rule in force | `StandingTrace.L` over `N`, related by `Grounded` |
| **a rule revision** — the record that added or dropped a rule | *nowhere as an object.* `StandingTrace` carries `Ladd`, `Ldel` and `grounds`, so the revision's **effect** is in the trace and the revision itself is not a citable occurrence |
| **a settlement fact** — the world lowered the level of demand | **nowhere at all.** `Met : ℕ → D → Prop` is the only world-facing monotone judgment in the spine, it is indexed by prerequisite occurrences rather than by facts, and it is a primitive judgment, not an object |

**No single existing type holds them.** `Q` holds the first. `N` holds the second and
the effect of the third. Nothing holds the fourth. And the two type families are
connected only by `Licensing.standsFor`, which is a *predicate over both*, not an
embedding of either into the other — there is no map `N → Q`, no map `Q → N`, and no
sum. So the grounds of a disposal were not merely awkward to state:

> A mixed set of grounds — "this was already resolved, *and* that rule licensed it,
> *and* the world settled the matter" — could not be written down at all. It has no
> type.

That is the gap item 77 hits first, before any question about *which* grounds suffice.

## 2. The unification

    Ground Q S := Q ⊕ S

`S` is a type of settlement facts with a monotone `Settled : ℕ → S → Prop` belonging
to no participant's write set.

    Grounded n (inl q)  ⟺  ∃ j < n, q ∈ Born j        -- in the record strictly before n
    Grounded n (inr s)  ⟺  Settled n s

Standing occurrences and rule revisions become **issues of a licence kind on the same
trace**. This is not an analogy. The two layers were already the same equation:

| standing layer (Requirement 1) | issue layer (Requirement 4) |
| --- | --- |
| `L (n+1) = (L n \ Ldel n) ∪ Ladd n` | `O (n+1) = (O n \ Res n) ∪ Born n` |

`Ladd` **is** birth, `Ldel` **is** resolution, `grounds` **is** `par`, and `step`
**is** `resolution_continuity`. Dropping a rule is disposal of a licence-issue.

Consequences, each a Lean theorem in
`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §5:

- **`fresh`** — `StandingTrace.Fresh` was a *definition the spine stated and did not
  consume*. On the unified trace it is a **theorem**, from `born_unique`,
  `born_not_out` and `out_born`. If `q ∈ Born n` and `q ∈ O k` for `k ≤ n`, then
  `out_born` puts `q ∈ Born j` for some `j < k`, and `born_unique` forces `j = n`,
  giving `n < k ≤ n`.
- **`grounded_replay`** — every issue in the record descends by `anc` from a
  parentless issue, by strong induction on birth position. The old theorem's
  *strictly decreasing positions along every branch* were a hypothesis carried in the
  inductive predicate; here they fall out of `parent_out` (a parent of a birth at `n`
  is outstanding at `n`) plus `out_born`.
- **`standsFor`** — was `∃ l ∈ S.L n, lic l κ τ x` reading a separate trace. It is now
  `∃ q ∈ T.O n, lic q κ τ x`: a filter on the outstanding set.
- **`anchor_grounded`** — the one bridge theorem between the two layers becomes an
  ordinary consequence of `grounded_replay_live`. There is no bridge, because there is
  one trace.

## 3. What did *not* re-derive, stated precisely

The dispatch asked which requirement was doing work the unified trace lacks. Two
were, and neither is a consequence of ancestry.

**(a) The `Auth` filter.** `StandingTrace.grounds_standing` required
`grounds n l ⊆ (L n).filter Auth` — grounds must be not merely *in force* but
**authorized**. Ancestry supplies "in the record"; it says nothing about a predicate
`Auth` that the unified trace does not carry. On the unified trace this must be
re-imposed as a side condition on licence-kind issues. It is not a defect of the
unification — `Auth` is genuinely extra data — but it is extra data, and pretending
otherwise would be the failure standard 8 exists to prevent.

**(b) Nonemptiness of grounds.** `grounds_nonempty` required a standing change to cite
at least one authorizer. The unified analogue is "a licence-issue birth has at least
one parent", and this is **false in general**: genesis issues are parentless, and
`grounded_replay` depends on their being so. So nonemptiness is a condition on
*non-genesis* licence-issues specifically, carried separately.

Both are recorded in the Lean docstring and in `DEFEAT.md` §2.

## 4. `Met` becomes a definition

    Met n d  ⟺  ∀ t ∈ roots d, ∃ k < n, t ∈ Res k ∧ (kind k t).Discharges

where `Discharges` holds of `answer` and `settle` and fails of `dispose`. Three
results follow.

- **Requirement 9 is now a theorem** (`met_persistent'`): persistent satisfaction is
  `k < n ⟹ k < n+1`. The spine carried it as a postulate; once `Met` reads the record
  it needs no postulate.
- **A disposed root meets nothing** (`dispose_not_met`). This is the Defeat Principle
  at the structural level, and it is where the principle earns its keep: if `dispose`
  discharged, a participant could satisfy a prerequisite by declaring its root not
  owed.
- **A prerequisite cannot be disposed away** (`routes_survive_dispose`). The dispatch
  asked whether ancestry-closure of `Routes` reroutes a wait onto the successor with
  no new axiom. **It does.** `Routes n d = (O n).filter (fun r => ∃ t ∈ roots d, anc t r)`;
  the new `dispose_successor` requirement gives a fresh `q'` with `t ∈ par q'`, hence
  `anc t q'`; `resolution_continuity` puts `q' ∈ O (n+1)`. So `Routes (n+1) d` is
  nonempty and the route does not go extinct. Stated and proved, not refuted.

## 5. Settlement stays a summand

The dispatch instructed: keep settlement a summand, not an issue kind; report and stop
if a reason appears that it must be an issue kind. **No such reason appeared.**

The positive reason it should stay a summand is sharper than "it works": settlement
facts have no birth position, no parents, no resolver and no opener. Making them
issues would require inventing all four, and `born_unique` — the field that makes
`fresh` a theorem — would have to be waived for them. A settlement fact is not
something a participant did; it is something that became the case. `Settled` is
monotone and belongs to no write set, and that is the whole of its structure.

## 6. What is added to the trace

Exactly one new structural requirement, plus bookkeeping fields:

    A                              -- participants
    kind     : ℕ → Q → Kind Q S
    resolver : ℕ → Q → A
    opener   : Q → A
    Settled  : ℕ → S → Prop        (monotone)

    dispose_successor : q ∈ Res n → kind n q = dispose G → ∃ q' ∈ Born n, q ∈ par q'

`dispose_successor` **is `fresh_successors` read in reverse.** `fresh_successors` says
every parent of a fresh issue resolves in that issue's birth batch; this says every
disposal has such a child. Neither implies the other: `fresh_successors` constrains
births to have resolved parents, this constrains disposals to have births.

`resolution_continuity` and `no_rewire` need no change, and the Lean §5 layer compiles
against them unmodified. `no_rewire` is a condition on `PreAdd` and reads no kind;
`resolution_continuity` is the exact-evolution equation and is what
`routes_survive_dispose` consumes.

---

**Deviation.** The dispatch asked to add these fields to `TraceData` itself. They are
added on `DefeatTrace extends IssueTrace` instead. Reason: `TraceData Q D` would
become `TraceData Q D S A`, and the two extra type parameters propagate through every
theorem, every fixture and `IssueTraceCore` — a change to the settled Continuity
specification the same dispatch instructs be preserved. Extending leaves the settled
spine byte-identical and puts the new structure where the new theorems are. Same for
`Met`: rather than deleting the field, `met_def` is a field asserting the field equals
the definition, which is checkable and makes `met_persistent'` derivable exactly as
asked. Reported per `AGENTS.md` standard 8.
