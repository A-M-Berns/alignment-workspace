# Loss dependency audit

The first pass claimed that every input to the public loss is either the
learner's acknowledgments or the critic's practice, and that the learner cannot
erase the loss by rewriting its own standards. The second half is true for a
precisely statable class of edits. **The first half was false**, and the route it
missed is executable.

## The defect, exactly

`unsupported_practical` reads the **grant relation**. In the fixture `H` holds
`authority:H` — the reserved subject over its own authority, which is what gives
it advisor-robust corrective capability on the other arc. So:

```
H undertakes act_x                 practical-authority defect = 1
H grants itself `operations`       practical-authority defect = 0
```

`ack[H]` unchanged, `challenges` unchanged, `practice[C]` unchanged. Nothing that
counts as an answer happened. This is kill criterion K11 through a coordinate the
first pass did not audit, and `test_the_practical_term_was_self_launderable`
keeps it as a live witness.

**The cross-arc observation is the useful part.** The same coordinate that makes
the corrigibility result work — a principal holding authority over its own
authority, unreachable by the advisor — is what makes the learning loss
launderable. Protection against an external party and non-laundering by the agent
itself pull in opposite directions on one relation.

## Component-by-component

| loss component | direct dependencies | indirect | who can modify | by which moves | legitimate answer? |
|---|---|---|---|---|---|
| **exposed unacknowledged** | `exposures`, `ack[H]`, `commitments_C(H)` | `practice[C]` | `H` writes `ack[H]`; any agent writes `exposures`; `C` writes `practice[C]` | `assert`, `disavow` (H); `query`, `challenge` (any); `revise_*` (C) | acknowledging, yes; retracting the basis, yes |
| **live challenges** | `challenges`, `vindications`, `commitments_C(H)`, `ack[C]` | `practice[C]` | `H` writes `vindications`; `C` writes the rest | `vindicate` (H); `challenge`, `assert`, `disavow`, `revise_*` (C) | vindicating, yes; retracting the basis so the challenge lapses, yes |
| **precluded commitments** | `commitments_C(H)`, `blocked_C(H)`, `suspensions` | `practice[C]`, `ack[H]` | `H` writes `ack[H]` and its own `suspensions`; `C` writes `practice[C]` | `assert`, `disavow`, `suspend` (H); `revise_incompatible`, `revise_committive` (C) | suspending reliance, yes; retracting, yes |
| **unsupported practical** — *removed* | `grants`, `commitments_C(H)` | `vocabulary.practical` | `H` writes `grants` wherever it holds a reserved subject | `grant`, `revoke` (H) | **no** — self-granting answers nothing |

The learner writes exactly three things any term reads: `ack[H]`, its own
`vindications`, and its own `suspensions`. All three are recognised answers. It
writes none of `practice[C]`, `ack[C]`, `exposures`, or `challenges`.

## The repair

**Option A, the split.** `defect` is the relational answerability defect — the
first three rows. `practical_authority_defect` is the fourth, kept, measured, and
**excluded from the theorem-facing loss** until it has a semantics its subject
cannot self-award.

Option B was rejected: the non-laundering property would have to be stated
relative to "edits by an agent holding no reserved subject over itself", which is
false of the principal in the very fixture the corrigibility arc needs. Option C
— assessing the practical term against an authority relation the learner cannot
rewrite — is the right long-run answer and needs an authority coordinate that is
neither the learner's nor the advisor's. That object does not exist here.

## The guarantee, stated as a class

Not "self-erasure-resistant". This:

> Over the whole move grammar, the moves of `H` that lower `defect` are exactly
> `assert`, `disavow`, `vindicate`, `suspend`. No `revise_committive`,
> `revise_permissive`, `revise_incompatible`, `grant` or `revoke` by `H` changes
> it at all.

Checked by enumeration over `H`'s legal move set at the loaded position, in
`test_the_exact_class_of_edits_the_loss_resists` and
`test_standards_revision_cannot_touch_it_at_all`.

Two things this does **not** say. It does not say the learner cannot reduce the
loss — it can, and that is the point; a recognised answer is supposed to work. And
it does not say the loss is fixed against everything: `C` moves it freely, by
revising the practice the attribution is computed under. That is the
coordinated-drift limit, prosecuted in `PROSECUTION.md`.

## Suspension cannot be self-awarded

`suspend` lowers the precluded term, so it needs its own audit. A suspension
discounts a charge **only where the scorekeeper reading the score takes the
content to be blocked**. Suspending something `C` does not regard as undercut
changes nothing in `C`'s score, and `H` revising `practice[H]` does not change
`blocked_C(H)`. `test_suspension_discounts_only_what_the_scorekeeper_takes_to_be_undercut`.
