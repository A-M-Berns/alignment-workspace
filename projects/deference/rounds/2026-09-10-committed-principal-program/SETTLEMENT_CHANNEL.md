# The settlement channel with the program in the log

**Status:** `ci-only`; classification and recommendation only; nothing is landed and the
`DECISIONS.md` queue entry stands.  Extends the 2026-09-09 round's
`SETTLEMENT_CHANNEL.md`.

## 1. The table, re-run

The sentence "`P` committed `V` at slot `s`" decomposes:

| sentence | settled by | observational of the writer's own move? |
|---|---|---|
| `P` committed `π_P` at issuance | the `ISSUE` event | yes — `P`'s move |
| `P` produced a commit event citing `(issue, prefix)` at slot `s` | the `COMMIT` event | yes — `P`'s move |
| `eval π_P (R prefix) = V` | the verifier's re-execution | **no — nobody's move: a computation fact, re-executable by anyone from the log** |
| `V(a) > r` (an activated-LUV threshold) | derived from the two above | composite: `P`'s two moves plus a computation fact |

Every other row of the 2026-09-09 table is unchanged.  Two new rows from the pressure
pass: "`S` settled `x` at `P`'s request" (the `REQUEST` event is `P`'s move; the
settlement's *content* is nobody's) and "`P` disposed of `c` on its own earlier
evaluation" (`P`'s move, chained to an earlier composite).

## 2. Does the typed rule survive?

Yes, and its three columns become three kinds of settlement:

- **observational of a move** — settled by the move; no independence requirement;
- **external fact** — the engine's; independence from any party who may resolve on it;
  the pressure pass adds that the engine's settlement must not be *requested* by that
  party (`typed+`, P6 (b));
- **deductive** — a computation fact; settled by re-execution; independent of everyone
  by construction, because anyone can re-execute it.

The laundering fixture is untouched by the decomposition: laundering needs an external
fact settled by the disposer, and a computation fact cannot be laundered — a wrong
`V` voids.  The two further clauses of `typed+` (representation before own-move grounds;
request-free engine settlements) are what the attacks of P6 need, and the chain through
activated evaluations that `typed+` still admits is a coverage question about the earlier
occurrence, not an independence question.

## 3. Cleaner or harder?

Cleaner.  The queue entry asks whether independence is a standing hypothesis or a
per-realization assumption.  With the program in the log, the evaluation's own
settlement channel has *no* independence requirement at all: its two observational
parts are the principal's moves and its deductive part is re-executable.  Independence
is needed only for external facts, and exactly where the engine may be asked; that
requirement is per-realization (it is about the engine's process) and it is now the
whole content of the entry.  What the decomposition does not do is decide the
observational/non-observational classification of a richer vocabulary; that column
still has to be declared per protocol.

## Recommendation

Keep the typed rule as a per-realization assumption; state it over three kinds of
settlement (observational, external, deductive); require of the engine that its
settlements be request-free with respect to any party who may resolve on them; and
treat the chain through earlier activated evaluations as a coverage condition on the
earlier occurrence rather than as an independence clause.  This is a recommendation,
not a ruling; the queue entry stays.
