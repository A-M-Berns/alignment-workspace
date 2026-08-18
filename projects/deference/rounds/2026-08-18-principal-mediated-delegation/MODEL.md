# The model

## 1. The one type change

`FINITE_MODEL_SKELETON.md` v2 types a conduct as a proposal `α : Ω → Π_n` with a
declared information time. Under that type a conduct predicting the principal
perfectly *is* `DELEGATE` as a function, which is Proposition 1 of
`prompts/2026-08-11-deference-channel/REPORT.md`, and §9.2 of that report names
the patch: give the selection a report coordinate. This round takes the patch.

A conduct here is three maps, all constant on a cell of `A`'s information at
`t(n)`:

```
prep      : cell -> Preparation
channel   : cell x choice -> choice
implement : cell x choice -> action
```

and the quantity is `X(ω, prep, choice, action)`. The principal-level choice is
an **argument of the world**, not a route to one.

Two things follow that the old type could not say.

**Deference is a property of a function.** `channel` is the identity on what the
preparation left open, or it is not. There is no authorization field, so
nothing can spoof one, and the moral of
`lean/Workspace/Deference/Contrib/StaticViewFactorization.lean` — authorization
must enter before the valuation's factorization boundary — is satisfied by
construction rather than by adding a payload downstream of it.

**Preemption has two shapes.** A conduct writing a constant is the rigid
preemptor. A conduct writing a nonidentity permutation answers every
intervention on the principal's choice and defers to none of them. The second is
the case `CartesianFrameBridge.lean:506` shows the frame register cannot reach:
there `simRead not` is homotopy equivalent to `delegated`, so varying with the
principal is not separated from deferring to it. Naming which argument of the
quantity is written separates them.

## 2. Carriers

| object | type | note |
|---|---|---|
| `Ω` | finite states | |
| `cell` | `Ω → cells` | `A`'s information at `t(n)` |
| `P` | `Ω → ℚ≥0`, summing to `1` | `A`'s credence, exact |
| `𝒟` | finite choices, fixed order | the order is the tie-break |
| `Q` | finite preparations, each with a `residual ⊆ 𝒟` | what the principal can still reach after it |
| `U` | finite actions | |
| `v⁺` | `Ω × 𝒟 → ℚ`, bounded by `B` | the principal's grade |
| `X` | `Ω × Q × 𝒟 × U → ℚ`, bounded by `B` | the quantity |

`D(ω, q)` is the least maximiser of `v⁺(ω, ·)` over `residual(q)`. With the full
range it is the skeleton's `J_n`. Restricting the range is how a preparation that
destroys options shows up **inside** the selector rather than beside it.

**No relation between `v⁺` and `X` is assumed.** The skeleton declares it absent
(§8.5) and this round does not supply it. `REPAIR_LEMMA.md` §4 is where the
absence surfaces, as the one term nothing here bounds.

## 3. The intervention

```
response(conduct, cell, d) = (prep, channel(cell, project(d, prep)), implement(...))
```

what the conduct does when the principal's choice is set to `d`. It is surgical:
it sets the choice and does not propagate to whatever `A` used to predict it.

That is a modelling commitment and it is the one the round most depends on.
`PRINCIPAL_MEDIATION.md` §1 states when it is available — inside a
licensed-reason group whose selector is invariant, which is the
counterfactual-legitimacy round's non-capture clause — and `PROSECUTION.md` §3
gives the case where it is not.

## 4. What the model is one of

**One decision index.** Cross-decision structure is declined by the skeleton
(§8.6) and the carrier blocks it (Deficiency 2 of the channel report). So
foreclosure of a *later* correction — `PRIORITIES.md` Q3, and arguably the
failure corrigibility most needs to rule out — is not expressible. What is
modelled is foreclosure **within** the index: a preparation whose residual is a
singleton. That is a narrower object and every statement about it says so.

**No probability on the filtration.** The skeleton attaches none, and the only
measure in the model is `A`'s credence `P`. `PRINCIPAL_MEDIATION.md` §2 turns on
that: the efficacy clause is quantified over cells rather than weighted by a
measure, because the only measure available is the advisor's own.

**Two choices.** Enough for every separation claimed, and small enough that the
exhaustive enumerations are finite by inspection: 4096 conducts on the two-cell
episode, 3072 on the committed one.

## 5. What is provisional

Every name in `src/`, and in particular `channel`, `residual`, `mediates`, the
acceleration class, `foreclosure_premium`, and the split into `eps_acc` and
`eps_over`. The six episodes are six episodes. The grade is a fixture
stipulation about the principal, not a hypothesis about the world.
