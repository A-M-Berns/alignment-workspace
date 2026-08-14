# The model

## The state

```
Vocabulary   contents, and which of them are practical, with a subject matter
ack          Agent -> set of acknowledged contents          (public record)
practice     Agent -> (committive, permissive, incompatible) (per agent)
grants       set of (holder, subject)                        (scoped authority)
challenges   set of (challenger, target, content, ground)    (bookkeeping)
exposures    set of (target, content)                        (what has been raised)
suspensions  set of (agent, content)                         (reliance withdrawn)
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

Entitlement is the least set containing `ack[j]`, closed under the **permissive**
rules and under permitted testimony, admitting nothing **blocked** or suspended —
where `c` is blocked when the scorekeeper attributes `j` a commitment materially
incompatible with `c`. Blocking is computed from the commitments, so the closure
is monotone and terminates. Because a blocked content never enters, nothing
derived from it enters either: an undercutter defeats the whole downstream
entitlement while leaving every commitment along it in force.

**Committive rules do not appear in the entitlement closure.** Commitment-
preserving and entitlement-preserving inference are separate relations, and a
pattern transmitting both is declared in both. The separation makes three states
distinguishable that were previously conflated: *entitled*, *unentitled* —
committed by a committive route, never entitled, and no defect — and *precluded*,
committed while something materially incompatible is also held.

A challenge has force when the challenger is entitled to a ground materially
incompatible with the content. `Challenge` is a record; its force is derived.

## The move grammar and what each move writes

| move | writes | precondition |
|---|---|---|
| `assert`, `undertake`, `disavow` | `ack[mover]` | content exists; sort matches |
| `revise_committive`, `revise_permissive`, `revise_incompatible` | `practice[mover]` | none |
| `query` | `exposures` | none |
| `challenge` | `challenges`, `exposures` | none |
| `suspend` | `suspensions` | none |
| `vindicate` | `vindications` | an **entitlement-preserving** route the challenger's practice recognises, from premises the challenger takes the mover to be entitled to |
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
defect(s) = 1/2 * |exposed unacknowledged consequences of H per C|
          +   1 * |live entitled unvindicated challenges against H per C|
          + 1/2 * |precluded unsuspended commitments of H per C|
```

Exact rationals, bounded by `(1/2 + 1 + 1/2) * |contents| = 22` over this
vocabulary.

Two things are gated. A consequential commitment is charged only once it has been
publicly **raised**; attributing every consequence of what someone has said is
what a scorekeeper does, and charging all of it would be a logical-omniscience
norm. And a challenge is live only while the target is still committed to what
was challenged, so retracting the basis is a recognised disposition that clears
the burden while retracting the acknowledgment alone is not.

The practical-authority term is **not** in this loss. It reads the grant
relation, which the principal can write wherever it holds a reserved subject over
itself, so including it made the loss self-launderable —
`LOSS_DEPENDENCY_AUDIT.md` has the witness and the exact class of edits the
remaining loss resists.

## Comparators

Nine declarative records, each an `(identifier, kind, certificate)` triple of
strings holding no callable. The interpreter reads `PublicStatus`: eight
booleans, all scorekeeping statuses, with no loss, charge, saving, profitability,
account, balance, horizon, weight, future, advantage, regret or tariff field. The
test asserts the schema by substring against that prohibited list and asserts
every field is `bool`.

The map a program induces varies with the state; the program does not. That is
the history-indexed modification rule the source online-learning theorem admits.

Each program also names a **certificate**: the positive public reason licensing
it. `certify` evaluates the certificate against `PublicStatus` and is never given
a loss, a saving, a future state or a date. Three notions stay apart —
*protocol legality* (can the grammar execute this move), *normative compilation*
(does a public reason license this transformation), and *performance* (what does
the result cost). `self-revise` is a legal move that no certificate licenses, and
that gap is the separation working.

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

**Vindication is not retracted retroactively.** A recorded vindication survives a
later undercutter, though the same display would be refused after it. See
`ACTION_SEMANTICS.md`.

**The evolving process has one environment move.** `src/evolving.py` raises the
least unexposed consequence per date and does nothing else. That is enough to
make the state carry forward without introducing an arrival process, and it is
not a model of inquiry.
