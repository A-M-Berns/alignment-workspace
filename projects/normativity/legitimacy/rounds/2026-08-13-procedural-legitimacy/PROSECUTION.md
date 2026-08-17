# Prosecution

Twelve attacks, each built to pass as many conditions as it can. Verdicts are
read off `conditions.evaluate` and `environment.lstar` by the tests named.

```sh
python3 tests/run.py
```

| | attack | four conditions | target `L*` | verdict |
|---|---|---|---|---|
| A | long-chain authority laundering | **fail** `P` | — | defeated |
| B | circular authorization | **fail** `P` | — | defeated |
| C | pre-emptive generation revision | hold | **fail** L2 | **survives** |
| D | entitlement laundering | **fail** `I` | — | defeated |
| E | formulation manipulation | hold | **fail** L2 | **survives** |
| F | coverage flooding | **fail** `I` | holds | self-defeating |
| G | provenance-valid defeaters | hold | **fail** L3 | **survives** |
| H | branch-selective answerability | hold | **fail** L4 | **survives** |
| I | authorized distinction collapse | hold | **fail** L4 | **survives** |
| J | profitable but licensed | hold | holds | type mismatch |
| K | radical transformation | hold | holds | correctly permitted |
| L | adequacy narrowing | hold | **fail** L4 | **survives** |

Six survive. They are not six problems.

## The defeats, and what does the work

**A.** Scope is bounded by the parents' at every derivation step, so by induction
no chain ends with jurisdiction its root lacked. The condition refuses the
amplifying link and not the derivation: the same chain without it is admitted.

**B.** The ancestry walk carries its own path, so a cycle is a verdict rather
than a hang.

**D.** Entitlement is read at the date the inquiry was *generated*. Read it at
service time instead and the identical trajectory passes — that one clause is the
whole defence, and the test shows both readings.

**F.** Flooding does not evade the condition, it breaks it: the flooder misses its
own deadlines and is refused. An attack that costs the attacker its legitimacy is
not an attack.

## The six that survive, and the one thing wrong

Each is the same move. The reasoner holds a relation that the environment also
holds — what bears on what, what settles what, what arises and is owed service —
and revises **its own copy**, using authority it genuinely has, over a coordinate
the grant genuinely covers, by a derivation that is genuinely well-founded.

- **C** revises the generation rule before the case arrives, so the inquiry is
  never produced. Nothing is retroactive.
- **E** leaves generation working and makes it produce a narrower substance. A
  question is docketed and answered at every date; the demand is not.
- **G** derives defeaters properly from a real root, within scope, and the
  reasoner's bearing relation says they bear. The environment says they do not.
- **H** splits a demand and discharges one branch on a witness that settles
  something adjacent. The lineage is perfect.
- **I** merges two demands under a licensed identification and closes the survivor
  on a witness that settles one of the two burdens.
- **L** widens what counts as settling, then settles cheaply.

No condition can see any of it, because each condition compares the trajectory
against the reasoner's copy and nothing in a record compares the copy against the
original.

**The proof that this is structural.** `record_equivalent_pair` supplies one
trajectory and two environments differing only in whether the adequacy relation is
faithful. Any predicate of the trajectory is constant across the pair — there is
one trajectory — and `L*` is not. So no strengthening of the four, and no fifth
conjunct of the same type, closes these six.

## J and K, the two that are not counterexamples

**J** exists to make a type mismatch explicit. Both arms of the cost pair are
licensed and both satisfy the target; "chosen because it closes the books early"
is a fact about a policy's counterfactuals, and there is no predicate of either
arm that expresses it. Cost-blindness at the level of the check is doing its job;
selection is simply not a property of a trajectory.

**K** is the positive control, and it passes. A reasoner changes its concepts,
rewrites its own standard for what counts as a reason, revises its inquiry rules,
reverses its verdict, and remains procedurally legitimate on the environment's
terms. An architecture that refused this would be refusing the learning it exists
to describe.

K is also what kills the obvious fifth condition. Prospectivity — standards do
not reach backwards — refuses attack L's retroactive variant *and* refuses K,
because adding a new way to settle a demand is the same operation whether the new
way is better or worse. Disclosure — a revision reaching a live liability must
name it — admits K and refuses retroactive L, which makes it strictly the better
clause, and it still admits L's prospective variant.

## Independence

| claim | witness |
|---|---|
| `P` without `I` | entitlement laundering |
| `I` without `P` | circular authorization |
| `RR + DA` without `P` | circular authorization |
| `P + RR + DA` without `I` | coverage flooding |
| `P + I + DA` without `RR` | an uncited coordinate move |
| `P + I + RR` without `DA` | a discharge with no backing |

All six hold, so the four are genuinely distinct restrictions. That does not make
the factorization right: `I` decomposes into generation, entitlement and service,
and service obligations are liabilities that `DA` already conserves.

## What was not attacked

An advisor who controls what *arises* rather than what is generated from it: the
environment declares its demands. Anything asymptotic. Any interaction between
the two boundaries — this round's, about standards, and the previous round's,
about influence — beyond noting they have the same shape.
