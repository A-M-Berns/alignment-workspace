# Legitimate Improvement — report

**Verdict:** `NO-FREE-EVASION-SURVIVES`, for a demonstrated repair.

## What the round was asked

Whether Legitimate Evolution plus low repair regret proves that a demonstrated
improvement cannot be escaped for free — rather than falsely proving that every
proposed improvement must eventually be adopted.

It does, and the second half of that sentence is the part the result respects.

## What survives

An accounting statement, not a second bound. Once a repair has been demonstrated
on the process's own record, every later diagnosed occasion is LIVE, CONTESTED or
SETTLED. The fourth cell is empty, and it is *representable* — `CM2` puts 196
occasions in it — which is what keeps the claim from being a tautology.

What connects one retirement to an unbounded later stream is not counting
retirement events, which cannot work. It is that the claim is **outstanding at
each later occasion**, which is frozen `A1` doing the work: an incurred claim
leaves the outstanding set only through an accepted `Resolve`. `CM3` runs 340
diagnosed occasions covered by one opened claim.

The theorem does not bound the CONTESTED cell and says so. A process may contest
forever; `CM8` does, and satisfies everything.

## Three findings worth more than the headline

**The effective mass is neither definition proposed for it.** Khot-Ponnuswami's
equation (5) forces the inner player's own loss to zero, so AdaNormalHedge's
adaptive quantity collapses to `sum_t I(t)|p^T(M_f - 1)l|` — each occasion
weighted by how much the repair would actually have changed the incurred loss.
`CM9` separates it from both proposals: a repair moving real probability mass
across actions of equal loss scores full under each of them and exactly zero
under this one.

**A surgical repair empties the LIVE cell structurally.** `pi(BAD) = pi(BAD)
M(BAD,BAD)`, so a repair mapping the diagnosed action elsewhere gives it zero
stationary mass the instant it carries weight — regardless of losses. That is
stronger than the bound expected to cover it, and it means Theorem B's content
is for diagnostics a registered repair does not fully eliminate, of which this
round has none. Said plainly rather than papered over.

**The hypothesis that makes regret mean anything is that the process runs the
algorithm.** Two wrong models were built first. A stubborn process is outside
every learning theorem, so nothing composes. A process playing its own fixed
point adopts the repair and therefore never accumulates evidence for the
improvement it is already making. Evidence has to be counterfactual.

## What this round does not establish

That recurrent defects disappear. They do not.

Anything about delay: `tau_t = 0` throughout, the anchor is carried so the
delayed consumer will not need a redesign, and no delayed bound is claimed.

Anything about evaluator manipulation. `CM5` is invisible here, and era locking
is explicitly declined as a solution while the same process writes the evaluator
before choosing its action.

Novelty in the learning kernel. It is two published results and a sign check; §F
says so.

## Outstanding maintainer actions

1. **Rule on priority 72** — the two escapes (`CM2` preemptive retirement, `CM5`
   evaluator shedding) are real, executed, and not this theorem's to close. They
   need a Coverage or independence premise, or a finding that they are
   ineliminable at this layer.

2. **The frozen LE seam is untouched and priority 71 is unchanged.** This round
   read `replay.py` and `answer.py` and modified neither.

3. **No other item is reserved.** The three forks this round faced it adopted, as
   dated `DECISIONS.md` entries marked agent-decided and reversible.

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; one dispatch |
| executor | Claude Opus 5 (Anthropic) |
| date | 2026-08-27 |
