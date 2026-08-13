# Report

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched and executed 2026-08-13
**Verdict:** `LOCAL-THEOREM-POSITIVE / NORMATIVE-INTERPRETATION-OPEN`

The round's documents carry the results: `SOURCE_AUDIT.md` for the primary-source
map, `THEOREM_TARGET.md` for the lemma and the numbers, `PROSECUTION.md` for the
negative controls and the four weaknesses, `PATH_INVENTORY.md` for what remains.
This carries what belongs to the round.

## The central question, answered

**Yes for the mathematics.** Ordinary lawful modification regret suffices for
actual-trajectory response learning, and the previous round's blockage was a
blockage of a different claim.

Three source facts settle it, quoted in `SOURCE_AUDIT.md`. A modification rule may
depend on history — stated in the definition. A time selector may depend on history
— stated in footnote 1. And the transformed distribution is scored against the loss
vector of the same date, so the comparator's own trajectory is never constructed.
Theorem 18's proof is a weight-potential argument on realized `(p^t, ell^t)` pairs
with no expectation taken, so it holds for any sequence however generated —
including one generated from the learner's own past actions.

**The interpretation is open**, for reasons that are not about regret at all. See
the verdict section below.

## What the round corrects in the repository

Two readings, neither of which is an error in any test or any Lean.

1. **"Frozen environment" was being treated as a hypothesis of the source
   theorem.** It is not. It is the condition under which replay equals local
   comparison. Theorem 18 has no state, no additivity hypothesis beyond bounded
   per-round loss vectors, and no obliviousness requirement.

2. **The previous round's `learning-replay-blocked` verdict.** The blockage is
   real and is a blockage of Claim C. Claim A is what the source theorem delivers,
   and it survives the same evolving process untouched — demonstrated on one run
   where the replay gap grows `5, 13, 29, 61` while the local quantity sits exactly
   on `delta * Q_T` at `2, 4, 8, 16`.

Historical artifacts of the merged round are unmodified; the correction is stated
here and in this round's own documents.

## What had to change to make the lemma work

The previous round's comparators rewrite many actions at once. That is admissible
to Theorem 18 but fatal to a lower bound, because gains and losses across actions
cancel. The repairs here are **surgical** — one selector, one source action, one
replacement, identity everywhere else — which is the shape of the source's own
internal-regret family, `F_{i,j}(i) = j` and `F_{i,j}(i') = i'`.

With that shape the per-date difference is exactly
`p^t(b) * (ell_t(b) - ell_t(r_t))`, and the bound
`R_T(g) >= delta * Q_T` follows with equality when the gap is constant. Verified
exactly at four horizons.

## The secondary finding, which was not asked for

The repository's Theorem 18 learner runs on the endogenous process — the
integration §XIV asked for — and satisfies the bound with `Q_T = 0` at every date.
It never makes the mistake.

Chasing that produced a structural result. Theorem 18 plays a stationary
distribution of the rule-mixture chain; a stationary distribution is supported on
the recurrent states; and on this class the transient set is **exactly the source
actions the repairs point away from**, with every replacement absorbing.

This is what a class of genuine repairs does. A repair points away from a mistake;
if every rule has that shape, every targeted mistake is transient and carries zero
mass. Making one recurrent needs a rule pointing back into it from a repair target
— "having acknowledged, stop acknowledging" — which is not a repair.

So the conclusion holds in its strongest form and **no repair class consisting only
of repairs can exhibit a learning curve for its own targets**. That is a new
adequacy constraint on any future generated repair grammar, filed in
`PATH_INVENTORY.md` §G, and a naive "collect all the repairs" construction violates
it.

## Deviations from the dispatch

1. **No Lean.** The lemma's arithmetic is a clean port target and the existing
   `recurrentFailure_lowerBound` takes the lower bound as a hypothesis rather than
   deriving it. A local `lake build` was started to check the toolchain and did not
   complete inside the round's budget; shipping unverified Lean is worse than
   shipping none. Filed in `PATH_INVENTORY.md` §E.
2. **§XIII, the policy-regret branch, was not investigated.** It is conditioned on
   the primary branch failing, and the primary branch did not fail. Recorded as
   `OPEN` rather than answered.
3. **The selector was folded into the modification rule** rather than carried as a
   separate time-selection function. Equivalent under the source definitions, and
   it lets the instantiation run at `M = 1`, which is what the repository's learner
   implements.
4. **One repair in the class is lawful and worsens the loss** (`gap = -2`). Kept
   rather than replaced, because it is the visible form of lawfulness being
   independent of performance.

## What this round does not establish

- No pathwise statement. `Q_T` and `E[N_T]` are claimed; `N_T/T -> 0` almost
  surely is not, and needs a concentration argument the source does not supply.
- No anytime guarantee. `beta` is tuned from `T`.
- Regret was never measured against the `O(sqrt(T N log K))` bound; only the
  lemma's inequality was checked.
- No learner shedding mass, and per the secondary finding this is structurally
  unavailable for a class of genuine repairs rather than merely absent.
- Coverage is untouched. A learner never asked has `Q_T = 0` free, and nothing
  here bounds what gets raised.
- Four hand-chosen repairs are not a repair language.
- Everything inherited from the merged round's declared simplifications.

## Why the verdict is split

`LOCAL-LEARNING-PATH-POSITIVE` requires that the resulting claim be substantively
adequate as the core normative-learning theorem. Two things stop that, and neither
is a regret question.

**Coverage.** Only exposed burdens are theorem-facing, which was the right fix for
a logical-omniscience norm and leaves an agent that arranges to be asked nothing
with a perfect score.

**Repertoire.** What makes this *normative* learning rather than local loss
reduction is that the repair class is normatively meaningful and adequate. Four
hand-picked rules do not establish adequacy, and the recurrence finding adds a
second constraint any candidate class must satisfy.

The mathematics is open and the interpretation rests on those two, which is what
the split label says.

## New names introduced

All **provisional**: `surgical repair`, `Actual-Trajectory Repair Lemma`,
`local modification regret` (as distinguished from replay), `bad-response mass`,
`recurrence adequacy`, `replenishing environment` (carried from the merged round).

## Structural defects found

None.

## Outstanding maintainer actions

Nothing is reserved. No `PRIORITIES.md` item filed, nothing appended to
`DECISIONS.md`, no claim registered, no decision requested. The PR is opened and
not merged.

The next target is named rather than reserved: a coverage condition, which
`PATH_INVENTORY.md` marks `BLOCKING` and which is where the merged corrigibility
work may compose.
