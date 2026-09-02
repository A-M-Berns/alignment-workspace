# Countermodels and hostile fixtures

Eleven exact finite cases, in the settlement round's runner style. Every one names the
clause that refused it, or records that nothing did. `python3 tests/run.py` from the
round directory; 24 tests, all passing.

Participants: `P` principal, `V` advisor, `W` third party. Genesis opens three licence
issues `l_P`, `l_V`, `l_W` and one corrective matter `a`.

| # | fixture | outcome | clause |
| --- | --- | --- | --- |
| 1 | disposal grounded in its own successor | **refused** | `D1-ungrounded` (priority alone) |
| 2 | disposal grounded in **itself** | **refused only by the explicit clause** | `D1-self-grounded` — **finding** |
| 3 | disposal on a fact the disposer settled | **refused** | `settlement-not-independent` |
| 3′ | the same trace, settlement belonging to nobody | **accepted** | — the independence hypothesis is necessary |
| 4 | a wait on a disposed root | **reroutes**; `Met` stays false | `routes_survive_dispose` |
| 5 | a wait on an answered root | **met** | `met_def` |
| 6 | mixed resolution, componentwise receipts | **conserved** | per-component identity frame |
| 7 | single-author laundering walk | **refused** | `D3-uncontested` / `D3-self-grounds` |
| 8 | two-author alternating walk | **accepted** | — **finding**, filed |
| 9 | disposal chain, divergent contest, `liminf L_t(1)=0` | **not persistent** | `Σ τ(q') = ∞` |
| 10 | the same chain, bounded contest | **persistent** | `Σ τ(q') < ∞` |
| 11 | settlement lowering demand, no successor, no charge | **accepted** | `settle` is the only kind that may close with no successor |
| 12 | a fourth resolution kind | **refused** | `bad-kind` |

## The two findings

### Finding 1 — priority does not refuse self-grounding

Fixture 2. The transition-certificates round's postulate 5 collapsed because every
self-certification attack died on priority or genealogy with no dedicated clause. On
the unified trace that collapse is **narrower than it reads**.

A disposal at `n` of an issue `q` has `q ∈ Res n ⊆ O n`, so `out_born` gives
`q ∈ Born j` for some `j < n`, so `Grounded n (inl q)` is **true**. Priority is
satisfied and refuses nothing. The successor and everything else born in batch `n` are
refused by exactly the argument the certificates round used (`born_unique` forces
`j = n`, contradicting `j < n`), so two of the three cases do collapse.

The asymmetry has a clean reading: **priority refuses grounding in what a record
mints, and cannot refuse grounding in what it consumes.** A certificate mints; a
disposal consumes. `Answerable.not_self` is therefore a clause and not a lemma, and
`DefeatTrace.self_grounding_not_excluded_by_priority` records this in Lean as a
positive statement rather than a gap in a comment.

### Finding 2 — separation does not stop coalitions

Fixture 8, and the round's substantive negative result.

    a  --V disposes, ground g_W (opened by W), successor a1 (W stands)-->  a1
    a1 --W disposes, ground g_V (opened by V), successor a2 (V stands)-->  a2

Every edge satisfies D3 in full: each has a foreign ground and a foreign
standing-holder, because each participant supplies the other's foreignness. The pair
launders indefinitely and nobody outside `{V, W}` ever contests.

D3 is a per-edge predicate at `C = {resolver}`. The general non-capture predicate needs
the **coalition-indexed** form given in `DEFEAT.md` §5, and that form is unsatisfiable
at `C = A` unless a **designated protected participant** sits outside every coalition
quantified over. Whether legitimacy may presuppose such a designation is reserved to
the author. Not repaired here.

## Why fixture 3′ matters

Fixtures 3 and 3′ are the same trace under different `settled_writer`. With
`settled_writer="V"` the disposer both settles the fact and resolves on it, and the
model refuses. With `settled_writer=None` — settlement belonging to nobody, which is
the intended reading — the identical trace is accepted.

That is what makes the independence of `Settled` from the disposer's writes a
**load-bearing hypothesis rather than a decorative one**: drop it and a participant
manufactures its own settlements, which is the laundering channel item 77 names, in
its purest form. Whether the independence is a standing hypothesis of the program or a
per-realization assumption is reserved to the author.

## Fixture 4 in detail

`d0` is a prerequisite on `b` with route root `a`. `a` is disposed into `a1`.

- `Routes(d0)` before: `{a}`. After: `{a1}` — **not empty**. The route did not go
  extinct; it followed the debt.
- `Met(d0)`: **false** before and after. A disposed root is not a discharging
  resolution, so it never satisfies anything.

This is the Defeat Principle doing structural work. Were `dispose` to discharge, a
participant could satisfy any prerequisite by declaring its root not owed — which is
precisely the move the principle forbids, and precisely the one that would make every
liveness theorem in the spine vacuous.
