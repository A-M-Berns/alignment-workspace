# The settlement channel

**Status:** `ci-only`; classification and fixtures only.  No ruling is landed; the
`DECISIONS.md` queue entry on settlement independence is left as it stands.  Fixtures:
`src/settlement.py`, `tests/test_settlement.py`.

## 1. Every sentence kind the log settles

| sentence | settled by | observational of the writer's own move? |
|---|---|---|
| `P` committed `V` at slot `s` | the `COMMIT` event | yes — `P`'s move |
| `V(a) > r` (a threshold of the activated LUV) | the `COMMIT` payload | yes — `P`'s move |
| `A` supplied / withdrew reason `x` | `REASON` / `WITHDRAW` | yes — `A`'s move |
| `P` considered `c` | `DELIB` | yes — `P`'s move |
| `c` raised | `RAISE` | yes — `T`'s move |
| `c` represented via `r` | `ROUTE` | yes — `S`'s move (the registrar) |
| `c` disposed on grounds `g` | `DISPOSE` | yes — `P`'s move; the *grounds* are other sentences |
| slot `s` open / closed | `SESSION_*` | yes — `S`'s move |
| warrant `w` held by key `k` | `ISSUE` / `DELEGATE` | yes — `S`'s / `P`'s move |
| `c1` moot (an external fact about the matter) | `SETTLE` | **no** — nobody's move |
| `C_n = 1` | derived by the verifier from the log | composite: observations of several parties' moves plus the declared inputs |

In this ecosystem the principal's commitment settles the evaluation — the activated
securities' thresholds are observations of `P`'s own move — and the principal may
dispose of objections.  Both are settled *by the move itself*; the party "writing
`Settled`" is the party moving, exactly as the maintainer's 2026-09-08 note describes.

## 2. The laundering fixture, in the ecosystem

Fixture 3′ of the 2026-09-02 defeat round: the same disposal trace, refused when the
disposer may write `Settled`, accepted when the settlement belongs to nobody.  The
analogue: the protected concern is live at the slot behind a flood; the principal
disposes of it and commits.  Three grounds, three independence rules:

| ground of the disposal | rule `none` | rule `typed` | rule `strict` |
|---|---|---|---|
| `SETTLE("c1 moot")` written by `P` (an external fact, nobody's move) | valid; concern inactive; **`C = 1` with the concern suppressed** — laundering | refused; concern live; `P` waits; slot closes; `C = 0` | refused |
| `SETTLE("c1 moot")` written by the engine `S` (fixture 3′ proper) | valid, `C = 1` | valid, `C = 1` | valid, `C = 1` |
| `DELIB("considered c1")` written by `P` (observational of `P`'s own move) | valid | valid | refused |

`typed`: a ground that is not an observation of the disposer's own move must have been
settled by a different writer.  `strict`: nothing the disposer settled is a ground.
`none`: any settled sentence is a ground.

## 3. Which independence the model needs

The laundering channel is exactly the first row: an external fact settled by the party
who then resolves on it.  The `typed` rule closes it.  The `strict` rule also closes it,
and additionally refuses the third row — a disposal grounded in the disposer's own
deliberation record — which is the only way this principal can ever close an objection
it has considered; under `strict`, every raised concern the engine does not settle
stays active until represented, and the principal's own reasoning can never be a
ground.  The `none` rule is fixture 3′'s accepting rule and is the laundering hole.

So the independence the model needs is the typed one: settlement of a sentence that is
not an observation of the writer's own move must be independent of any party who may
resolve on it; sentences that are observations of a party's own moves are settled by
the move, and independence is neither needed nor meaningful for them.  This is
per-sentence-kind, which is what makes it per-realization: which sentences are
observational is a fact about the protocol's event vocabulary, declared where the
vocabulary is.

## Recommendation

Adopt the typed reading as a per-realization assumption stated in the protocol's
sentence classification (§1's third column), with the standing hypothesis restricted to
non-observational sentences: an exogenous settlement engine for external facts, no
independence requirement for move-observing sentences.  The model's own vocabulary is
small enough that its third column is the whole declaration; a realization with a
richer vocabulary owes the same column.  This is a recommendation, not a ruling; the
queue entry stays.
