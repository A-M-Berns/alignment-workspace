# Nonvacuity

## The gap

PR79 defined `DefeatTrace` and `Disciplined` and exhibited **no Lean inhabitant of
either**. Every fixture in that round was Python, and its own report listed the gap:
*"Nothing here shows a defeat-disciplined trace exists."* A specification nothing
satisfies proves everything, so this is not a cosmetic omission.

## The witness

`Witness.witness` in the spine file, in the style of `Fixtures.fixE_issueTrace`.

Five issues over two participants (`true` = principal `P`, `false` = advisor `V`), one
settlement fact, and **no prerequisites** — `WD := Empty`, so `Met` and the wait
machinery are vacuous and the witness isolates the thing under test, which is the
resolution kinds.

| issue | born | fate |
| --- | --- | --- |
| `lic` | 0 | stays outstanding; licenses `P` for the anchor |
| `ans` | 0 | **answered** at 1 |
| `stl` | 0 | **settled** at 1, against a fact settled from 1 on |
| `dis` | 0 | **disposed** at 1 by `V`, on grounds `{inl lic}` |
| `dis1` | 1 | the disposal's successor, `dis ∈ par dis1` |

The three kinds, each exercised once. Membership is defined by two functions `bornAt`
and `resAt` rather than by literal `Finset`s per position, which is what makes the
fourteen `OtherRequirements` conjuncts provable by `omega` and a `cases` on the issue
type instead of by brute enumeration over positions.

### What is proved

| declaration | content |
| --- | --- |
| `Witness.witness_answerable` | the disposal satisfies all six clauses of `Answerable`, including the repaired `contested` — `P ≠ V` and `P` actually holds standing on `dis1` |
| `Witness.witness_disciplined` | **`Disciplined` is satisfiable.** Every resolution is an answer, an answerable disposal, or a settlement of a settled fact |

`witness_disciplined` is the headline: the specification PR79 wrote down has a model.

## The witness that fails by exactly one clause

`Witness.witnessBad` is the same trace with the disposal grounded in **itself** —
`wGbad = {Sum.inl dis}` instead of `{Sum.inl lic}`.

| declaration | content |
| --- | --- |
| `Witness.witnessBad_grounded` | `Grounded 1 (inl dis)` **holds** — the self-ground passes D1's priority test |
| `Witness.witnessBad_born` | `dis1 ∈ Born 1` — D2's first half holds |
| `Witness.witnessBad_inherits` | `dis ∈ par dis1` — D2's second half holds |
| `Witness.witnessBad_not_answerable` | it fails `Answerable`, **at `not_self` and nowhere else** |

This is PR79's first finding — *priority does not refuse self-grounding* — turned from
a remark into a Lean pair. The disposed issue `dis` is born at 0 and disposed at 1, so
`∃ j < 1, dis ∈ Born j` is satisfied by `j = 0`: the priority test is not merely
passed, it is passed *for the right reason*, because the issue really is prior to its
own disposal. `contested` and `foreign_ground` also hold of `witnessBad` (`P` still
stands on `dis1`; `dis`'s opener is `P ≠ V`).

So the fixture isolates `not_self` as the single clause between the system and a
self-grounded disposal, which is what "a clause and not a lemma" means, checked.

## `Disciplined` is not vacuous, and not trivial either

Worth stating because a satisfiable specification can still be satisfied only by
degenerate traces. This one is not: the witness has a nonempty outstanding set at every
prefix from 1 on, a genuine parent/child edge, a live licence issue that grounds a
disposal by a *different* participant than the one who holds standing on the successor,
and all three resolution kinds. What it does not exercise is the prerequisite and route
machinery, deliberately — `routes_survive_dispose` is proved in general in §5.3 and
does not need a fixture, whereas `Disciplined` needed one and did not have it.

## Verification

Built with the module: sorry-free, and every one of the **43** `#print axioms`
declarations in the file audits to exactly `[propext, Classical.choice, Quot.sound]`.
