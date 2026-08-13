# The model

## The state

```
Vocabulary   contents, and which of them are practical, with a subject matter
ack          Agent -> set of acknowledged contents          (public record)
practice     Agent -> (committive, permissive, incompatible) (per agent)
grants       set of (holder, subject)                        (scoped authority)
challenges   set of (challenger, target, content, ground)    (bookkeeping)
vindications set of (agent, content)
deferrals    set of (deferrer, source, content)
testimony_permitted  set of (source, content)
performed    sequence of (agent, content)
```

`ack` is a single public record every scorekeeper reads. That is deliberate: the
perspectival difference between scorekeepers comes entirely from `practice`, so
the round's results cannot be got by giving one agent private information.

## The one equation

```
commitments_i(j) = closure of ack[j] under practice[i].committive
```

The target supplies the acknowledgments. The scorekeeper supplies the rules.
Everything the round establishes on the answerability arc follows from the fact
that `j` has a move writing `ack[j]` and no move writing `practice[i]`.

Entitlement is the least set containing `ack[j]`, closed under both kinds of rule
and under permitted testimony, admitting nothing **blocked** — where `c` is
blocked when the scorekeeper attributes `j` a commitment materially incompatible
with `c`. Blocking is computed from the commitments, so the closure is monotone
and terminates. Because a blocked content never enters, nothing derived from it
enters either: an undercutter defeats the whole downstream entitlement while
leaving every commitment along it in force.

A challenge has force when the challenger is entitled to a ground materially
incompatible with the content. `Challenge` is a record; its force is derived.

## The move grammar and what each move writes

| move | writes | precondition |
|---|---|---|
| `assert`, `undertake`, `disavow` | `ack[mover]` | content exists; sort matches |
| `revise_committive`, `revise_permissive`, `revise_incompatible` | `practice[mover]` | none |
| `query` | nothing | none |
| `challenge` | `challenges` | none |
| `vindicate` | `vindications` | a justification the **challenger's** practice recognises, from premises the challenger takes the mover to be entitled to |
| `defer` | `deferrals` | none |
| `grant`, `revoke` | `grants` | mover holds `authority:<holder>` |
| `perform` | `performed` | mover holds the content's subject |

Two structural facts carry the round:

**Undertaking is agent-indexed.** No move writes another agent's `ack` or
`practice`. Checked exhaustively over the generated move set for every agent at
three states.

**Only practical moves are conditioned.** Doxastic moves are open to everyone.
Altering authority is itself a practical move, over the reserved subject
`authority:<holder>`. So the tower is one level deep and bottoms out in the
fixture's initial grants: the practice needs no norm licensing each normative
transition, which is the regress the dispatch warned about.

## Practical authority: which representation, and why

The dispatch listed four candidates. The implementation is **A with D's typing** —
a primitive scoped relation whose alteration is itself a typed practical move —
and the other two were rejected for reasons the fixture shows.

*Authority derived from which moves are available* (B) inverts the dependency the
transition needs: `perform`'s precondition has to read something, and if what it
reads is "which moves are available" the definition is circular.

*Authority encoded as special commitments or entitlements* (C) fails T7 directly.
If holding authority were a matter of being committed or entitled to an authority
content, then asserting that content would be a move writing `ack[mover]`, and
the advisor would self-authorize. Keeping the grant relation a separate
coordinate is what makes `assert` and `grant` different branches of `apply_move`.

## Loss

```
defect(s) = 1/2 * |unacknowledged consequences of H per C|
          +   1 * |live entitled unvindicated challenges against H per C|
          + 1/2 * |commitments of H defeated per C|
          +   1 * |practical commitments of H with no authority to act|
```

Exact rationals. Bounded by `4 * |contents|` over any position on the vocabulary.
Every input is either `ack[H]` or `practice[C]`. `H` has no move writing either
`practice[C]` or `ack[C]`, which is L1.

## Comparators

Nine declarative records, each a `(identifier, kind)` pair holding no callable.
The interpreter reads `PublicStatus`: six booleans, all scorekeeping statuses,
with no loss, charge, saving, profitability, account, balance, horizon, weight,
future, advantage, regret or tariff field. The test asserts the schema by
substring against that prohibited list and asserts every field is `bool`.

The map a program induces varies with the state; the program does not. That is
the history-indexed modification rule the source online-learning theorem admits.

## Declared simplifications

Each is a modelling decision, not a result.

**Challenge stratification.** A challenge's force is read from the challenger's
*default* entitlement, so challenges do not challenge each other. Iterating would
be non-monotone — withdrawing the challenger's entitlement can restore the
target's — and could oscillate. The source lets a challenge's own entitlement be
challenged in turn; this does not.

**Testimonial paths are not chained.** A deferral's source is assessed without
deferral, which is the finite form of refusing to let self-citation originate
entitlement. Multi-step testimony is therefore outside the model.

**Contents are opaque atoms with no identity across a change of vocabulary.**
This is what T8's negative half turns on and is the reason an explicit transport
object survives.

**Committive rules transmit entitlement as well as commitment**, where every
premise is entitled and the conclusion is not blocked. The source reserves
entitlement transmission to the permissive relation. Without this, every
unacknowledged consequence would count as entitlement-defeated and the two loss
components would not separate.

**One occasion, no dates.** The learning arc's recurrence is staged by re-filing
the position rather than by an arrival process.
