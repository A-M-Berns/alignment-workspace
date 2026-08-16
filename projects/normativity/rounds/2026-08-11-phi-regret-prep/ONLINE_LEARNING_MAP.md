# Which standard machinery this is, and which it is not

## The seven questions

**1. What is the action space?** Finite, per occasion: `merits(v)` for each
verdict label, `default`, and `decline(k)` for `k` in `0..w`. With two verdicts
and `w = 4` that is `2 + 1 + 5 = 8` actions. Loss is bounded in `[0, ℓ_max]`.

**2. What is a transformation φ?** A guarded swap. Where the guard fires and a
certificate is admitted, the learner's action is replaced by a specified one;
elsewhere it is left alone. The identity is in the class.

**3. Is φ action-only, context-conditional, or history-conditional?** All three
at once, and this is the one structural fact that decides everything else. The
guard may read the occasion (context), the learner's action at that occasion
(action-only — this is the swap part), and the actual prefix (history). The
canonical repair of `E4` uses all three: *where the learner declined* (action) *at
an occasion whose target* (context) *has a live clearing interval on the record*
(history).

**4. Are losses exogenous, adaptive, or policy-dependent?** Exogenous in v1.
The loss of an action at an occasion is a function of the frozen schedule and the
frozen reason state. This is bought by three exclusions — no book edits, frozen
filings, and the solvency coupling switched off — and each is a real restriction,
priced in `LAWFUL_EDIT_GRAMMAR.md` and `COUNTERFACTUAL_CHARGE_INFLUENCE.md`.

**5. Does replay make comparator loss well-defined from the actual history?**
Yes in v1, and only because guards read the actual prefix. `E11` is the witness
that the alternative convention gives a different comparator and a different
number, so this is a choice with content and not a formality.

**6. What bounded-influence assumption is required?** That one firing changes the
total by at most `ℓ_max`, so that the comparator's cumulative loss is the sum of
its per-occasion losses. In this substrate that is exactly the statement that the
solvency coupling is off, or that fences are per-occasion. With the coupling on
and a long fence, `E10b` shows one firing moving the total by `Θ(T)`, and the
per-occasion decomposition on which every regret bound rests fails.

**7. Is this genuinely φ-regret, or φ-regret-shaped?**

**Genuinely Φ-regret, in the v1 configuration, and the honest gloss is that the
configuration is what makes it so.**

With guards on the actual prefix, frozen arrivals and no coupling, the object is
a finite set of transformations of the action space, each measurable with respect
to information available before the action is chosen, applied to a sequence of
bounded exogenous loss vectors. That is the standard setting. The distance
between it and the interesting question is exactly the three exclusions, and
each is a place where the object stops being standard rather than a place where
the model is coarse.

## Where it sits

| notion | fit |
|---|---|
| **external regret** | too weak. The comparator class here is not a set of fixed actions; a fixed action across all occasions is not a lawful edit and would not be certifiable at most of them. |
| **internal / swap regret** | the closest classical relative. `E4`'s comparator is a swap — decline to merits — restricted by a guard. Swap regret over the full swap class is a strictly larger comparator class, and most of it is unlawful here. |
| **Φ-regret / transformation regret** (Greenwald–Jafari; Gordon–Greenwald–Marks) | **the right frame.** Φ_law is a set of transformations `A → A`; the reduction from Φ-regret to external regret over |Φ| experts applies verbatim in the v1 configuration. |
| **sleeping experts / specialists** | relevant. A guard that does not fire is a specialist that abstains, and the guard-conditional structure is the specialist structure. Worth reaching for if Φ_law is enlarged by guards rather than by replacements. |
| **contextual bandits** | not needed. Losses are fully observed: the charge of every action at an occasion is computable from the frozen schedule, so this is full information, not bandit feedback. |
| **policy regret / history-dependent loss** | what the object becomes if guards move to the replayed prefix, or filings become endogenous, or the coupling is reinstated. Any one of the three suffices. |
| **approachability** | no use identified. Recorded so a later round does not spend time discovering the same. |

## The reduction, and what it would buy

Blum–Mansour reduces Φ-regret to external regret over `|Φ|` experts by a
fixed-point step: at each step the algorithm holds a distribution over
transformations, and plays a distribution fixed by them. It needs each `φ` to act
as a map on distributions over actions at the time of acting.

That holds here. A guard is a function of the actual prefix and the action, both
available before the loss is revealed, so `φ` induces a stochastic matrix on
actions at each occasion. The standard bound would give

```
sup_{φ ∈ Φ_law} R_T(φ)  =  O( ℓ_max √(T log |Φ_law|) )
```

**Status: conjectured.** No one has checked the reduction against this substrate
line by line, the fixed-point step has not been instantiated, and the
per-occasion action set varies with the bound schedule, which the standard
statement does not have to handle. That check is the next round's first job and
is item 1 of `PHI_REGRET_TEST_SPEC.md` §6.

## What must not be said

That this is standard Φ-regret without naming the configuration. The comparator
class is defined by a legality predicate over the record; the environment is
standard only after three exclusions whose cost this round measured — 4 against 6
for the guard convention, 2 against 8 for the filing freeze, 2 against `2T` for
the coupling. Calling it standard while dropping those numbers would make a
restriction look like a fact.
