# Countermodels

## CM-1: hollow disposal

The landed disciplined witness disposes `dis` at position 1 and births successor `dis1`. Give the old token load `{a}` and its successor the empty load. Identity framing, incoming soundness, answer receipts, closure receipts, grounded disposal, standing, freshness, and ancestry all hold. `carry_complete` fails, and the account changes from `{a}` to empty.

Evidence: lean-proved by `Witness.hollow_other_clauses`, `hollow_carry_fails`, and `hollow_account_changes`; exact-witness in `src/fixtures.py`.

This is the smallest fourth fate: neither answer, valid closure, nor faithful carry, but erasure. It separates structural record integrity from Answerability Conservation.

## CM-2: authenticated settlement without closure

An immutable authenticated settlement item `s` is present. An obligation `q` is tagged `settle(s)`, but `Closes(n,s,q)` is false. A checker that equates `Settled(s)` with closure accepts; the typed local certificate refuses.

Evidence: exact-witness in `src/fixtures.py`. It establishes only the finite instance. The general separation is immediate from the independent predicates and is recorded as a proposed interface, not a theorem of the current spine.

## CM-3: posterior closure rejection

At position 1, `s` is authenticated and a grounded, licensed closure event closes `q`. At position 2, new grounds defeat that event. Mutating `q` back to outstanding violates append-only token history. Appending `review(q,closure-event)` preserves replay and records the new debt. Reincurring the old load requires an explicit fresh slice or successor.

Evidence: exact-witness in `src/fixtures.py`; the general reopening rule is a proposed interface.

## Clause scope

The Lean necessity witness isolates `carry_complete`. No necessity theorem is claimed for every other field of `LocalConservation`; `incoming_sound` and receipt equalities have direct one-step finite failures in the Python runner, while a minimal independent witness for locality across arbitrary ancestry was not constructed.
