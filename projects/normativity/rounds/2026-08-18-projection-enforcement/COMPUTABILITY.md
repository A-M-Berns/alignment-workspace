# Computability of the modified construction

What has to be computable for the projection route to be a construction rather than a
description, what is now proved, and exactly what is left.

**Summary.** `ComputableMarket` is no longer a premise. The end-to-end theorem takes
effective source data — a computable deductive process, a fragment schedule, a positive
rational tolerance schedule, and a finite representation of each day's projector — plus
one bounded-evaluator compiler — **and that compiler is now built**. The ingredients were
`private` in `LIACompiler.lean`; the dependency is pinned to a revision that re-exports
them publicly, and `EnforcedCompiler` runs the source's own primitive-recursion argument
with one extra list append. Debt B is discharged for any enforcer given as effective data.
§7 has the state and the one narrow item that remains.

## 1. The region and its piecewise-affine projector

Let `Φ_n` be the day-`n` fragment, `d = |Φ_n|`, and let `K_n ⊆ [0,1]^d` be a nonempty
rational polytope. In the deductive case
`K_n = conv{W|_{Φ_n} : W ∈ PC(D_n)}`, whose vertex list is obtained by enumerating the
sign patterns on `Φ_n` and keeping those extendable to a propositionally consistent
assignment satisfying the finite set `D_n` — a decidable question about a finite
propositional theory.

**Each coordinate of `p ↦ proj_{K_n}(p)` is piecewise affine with rational components.**
With `K_n = {x : Ax ≤ b}` rational, the projection is characterised by

```
q = p − Aᵀ μ,      μ ≥ 0,      A q ≤ b,      μ_i (A_i q − b_i) = 0.
```

On the set of `p` whose optimal active set is `I`, the constraints in `I` hold with
equality and the rest are slack, so `q(p)` is the projection of `p` onto
`{x : A_I x = b_I}`; for a maximal linearly independent subset `J ⊆ I`,

```
q(p) = p − A_Jᵀ (A_J A_Jᵀ)^{-1} (A_J p − b_J),
```

affine with rational coefficients. Finitely many index sets, polyhedral regions, closures
covering `[0,1]^d`: exactly Ovchinnikov's Definition 2.1 with rational components, so his
Theorem 4.1(a) applies coordinatewise and gives a finite max–min family over rational
affine forms. All the linear algebra is over `ℚ`; nothing is approximated.

Context: Bemporad, Morari, Dua and Pistikopoulos, Automatica **38** (2002) 3–20;
Rockafellar and Wets, *Variational Analysis*, §12.E; Scholtes, *Introduction to Piecewise
Differentiable Equations*, Springer 2012, §2.2.

**This step is not formalized.** It is the same external input named in
`DECISION_MEMO.md §C`, here in its effective form. A separate pass is attempting
Ovchinnikov's theorem in Lean.

## 2. The intensity, and why it exists before the price

```
ε_n = marketMakerError n = 2^{-(n+1)}                (pinned source, `def` into ℚ)
A_n = Strategy.tradeListAbsBound (ordinary trades)   (pinned source, `def` into ℚ)
ρ_n = ε_n + A_n                                      `ProjectionCalibrated.resistance`
λ_n = ρ_n / δ_n²                                     `ProjectionCalibrated.calibratedIntensity`
```

`tradeListAbsBound` is structural recursion over the trade list's syntax and never looks
at a price. The enforcer's type makes this structural rather than a matter of care:

```lean
trades : ℕ → List (EF × Sentence) → List (EF × Sentence)
```

An `EffectiveEnforcer` is a function from the date and the ordinary aggregate's *syntax*
to its own syntax. It cannot inspect the day's price at all; the price enters only later,
when the market maker evaluates the compiled `EF.price φ n` at its fixed point. So both
"the enforcer does not peek at the eventual price" and "`absBound` is computed before the
day's fixed point" are consequences of the interface, not side conditions to check.

`λ_n > 0` is `ProjectionCalibrated.calibratedIntensity_pos`, from `ε_n > 0` and
`δ_n > 0` — the latter a field of the schedule.

## 3. The enforcer as finite data

`ProjectionCompiler` takes representations as `Sentence → Rep`, and its `AffineForm`
carries `coeff : Sentence → ℚ`. Both are *functions on sentences*, which is fine for the
algebra and inadmissible as input to a primitive-recursive evaluator. `ProjectionEnforcer`
supplies the finite presentation:

| object | presentation |
| --- | --- |
| `FinAffine` | `List ℚ × ℚ` — coefficients positionally aligned with the fragment, and the constant |
| `FinGroup`, `FinRep` | nonempty lists of the above, as in the compiler |
| `ProjectionSchedule` | `coords : ℕ → List Sentence`, `tol : ℕ → ℚ` (positive), `reps : ℕ → List FinRep` |
| `ProjectionSchedule.enforcer` | an `EffectiveEnforcer`, a `def` |

`FinAffine` is an `abbrev` of a product of standard types rather than a structure,
deliberately: every type in the schedule is then `Primcodable` from the pinned
dependency's public instances (`ratPrimcodable`, `sentencePrimcodable`, `efPrimcodable`)
with no new instances to write. `ProjectionScheduleComputation` states the effectiveness
requirement — `Primrec` for each of the three components — and typechecks, which is the
check that the data really is finite.

## 4. Exact evaluation

The displayed prices are exactly rational and the compiled term is evaluated by the
source's `EF.denoteRat` in `ℚ`. `ProjectionCompiler.repEF_denoteRat` proves the rational
evaluation agrees term by term with the real denotation the theorems use, so nothing is
lost between what is proved and what would run.

## 5. The modified recurrence

`EnforcedComputation` mirrors the source's `LIAComputation` with one extra trade list
appended to the day's aggregate:

```
day 0      : []
day n + 1  : past  ← recurse n
             state ← marketMakerSearchUpTo
                       (join [firm(past, n), enforcer(n, firm(past,n).trades)])
                       past (marketMakerError n) fuel
             past ++ [state]
```

Kernel-checked: monotonicity in the fuel, existence of a sufficient fuel, soundness
(`enfPrefixFromStagesAtFuel_sound` — every successful bounded run *is* the semantic
prefix), the bounded exact-quote evaluator, minimization over the fuel clock, and
`toComputableMarket`. Nothing here is new mathematics; it is the source's architecture
instantiated at a bigger aggregate, which is why the proofs match it line for line.

## 6. Cost — what can and cannot be claimed

The construction is **effective**. It is not efficient, and the honest statement is weaker
than "exponential in the fragment":

* **Vertex enumeration.** At most `2^{|Φ_n|}` sign patterns, each requiring a
  propositional-consistency decision against `D_n`. That decision's cost is not bounded
  here.
* **Active-set enumeration.** At most `2^m` for an inequality description with `m` rows —
  but obtaining an inequality description from a vertex list is facet enumeration, which
  is not polynomial in general, so `m` is not controlled by `|Φ_n|` alone.
* **Max–min expansion.** Bounded by the number of regions of the arrangement of the
  distinct affine components, itself governed by the number of active sets.

These compound, and this pass claims no single closed-form bound over the composite. What
the paper needs is that the construction terminates and is computable; that is what is
claimed. `EfficientlyComputable` in the criterion constrains the traders that attempt to
exploit the market, not the enforcement trader added to it, so the cost conflicts with no
hypothesis — but no claim of an efficient intrinsic enforcer is supported, and none is
made.

## 6b. The homothetic-core refinement introduces no effective assumptions

`ProjectionCore` is a semantic refinement of the liability certificate: the core condition
is a geometric hypothesis about the region and the live possibility set, consumed only in
the budget, and it never reaches the compiled trader. The enforcer, the schedule, the
intensity and the bounded evaluator are unchanged. Nothing in §§1–6 above is affected, and
no new computation is required to *use* the refinement — though of course *checking* that a
given region has an `α`-core is its own finite question, which this pass does not address
beyond the two one-dimensional witnesses.

## 7. Debt B: discharged

**The premise is gone and the compiler is built.**

| claim | statement of record |
| --- | --- |
| the modified market is computable | `EnforcedCompiler.computableMarket` |
| traderized deduction with an effective enforcer is a logical inductor, in the source's *original* sense, with no computability premise | `EnforcedCompiler.isLogicalInductor` |
| the projection market's theorem of record, from effective data alone | `EnforcedCompiler.ProjectionSchedule.end_to_end_effective` |

### How

The upstream ingredients were `private`. The dependency is now pinned to
`d89817bc15d23c663d0520e3a854d6d02374074d`, which branches from the previous pin
`1fffea44` and adds exactly one purely additive section — public names for existing
private lemmas, no definition, statement or proof changed:

| exported | what it gives |
| --- | --- |
| `efConst_primrec`, `efPrice_primrec`, `efAdd_primrec`, `efMul_primrec`, `efMax_primrec` | the expressible-feature constructors |
| `efAbsBound_primrec` | `EF.absBound`, hence the calibrated intensity's input |
| `marketMakerError_primrec` | the day error schedule |
| `rationalBeliefStateQuote_primrec` | the belief state's exact rational quote |
| `processStagePrefixAtFuel_primrec` | the bounded deductive-stage prefix decoder |
| `tradingFirmTradesFromStageTradeLists_primrec` | the firm's day trade list |
| `marketMakerSearchUpToTradeList_primrec` | the bounded MarketMaker search over a raw trade list |

The recurrence itself was deliberately *not* exported: a downstream construction states and
proves its own, which is where its soundness obligation belongs — and this development
already had that (`EnforcedComputation.enfPrefixFromStagesAtFuel_sound`).

`EnforcedCompiler` then supplies the erased recurrence
(`enfPrefixFromTradeListsAtFuel`), identifies it with the proof-carrying one through the
source's two bridging lemmas (`enfPrefixFromTradeListsAtFuel_eq`), and runs the
primitive-recursion argument up through the bounded quote evaluator.

### The one hypothesis that remains, and why it is not a hidden premise

`EffectiveEnforcerComputation E`, whose single field is `Primrec₂ E.trades`. This is the
definition of "the enforcer is given as effective data", and it sits exactly where
`DeductiveProcessComputation` sits upstream: the construction is computable *given* that
its inputs are. An `EffectiveEnforcer`'s type already forbids it from seeing the day's
price; this says its syntax-to-syntax map is effective.

### What that section used to say, and why it no longer says it

An earlier draft listed `Primrec₂ S.enforcer.trades` for the projection schedule as open,
pending `Primrec` certificates for the `EF` construction and a presentation of `affineEF`
not routed through `AffineForm.coeff` (a function on sentences, hence not `Primcodable`).
**That is now closed.** `ProjectionPrimrec.lean` supplies positional reimplementations —
`affineEFof`, `groupEFof`, `repEFof`, `coefEFof` — each proved equal to the original by
`rfl` and then proved `Primrec`, together with `tradeListAbsBound_primrec`,
`resistance_primrec` and `calibratedIntensity_primrec`. `ProjectionEffective.lean` then
proves `scheduleTrades_primrec`: the schedule's enforcer is effective as a *consequence* of
the schedule's own computability, not as a hypothesis. It was mechanical and bounded, as
predicted.

### What is genuinely still open

Two things, in different states.

**1. An executable generator for the projector's max–min representation.** This is the one
headline-blocking item; `FINAL_FORMALIZATION_STATUS.md` is the authority on it. The route
is settled and the pieces are landing:

* `MaxMinRepresentation.maxMin_of_family` restates Ovchinnikov 4.1(a) with the index family
  **supplied**, replacing the internal `Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)`
  that no primitive recursive function can evaluate.
* `FourierMotzkin.lean` decides rational linear feasibility: `feasible_iff` in both
  directions, with `<` and `≤` genuinely distinguished — the strict form is load-bearing,
  since `λ_j > 0` is what separates a support from a face containing it. Equalities encode
  as two non-strict constraints.
* `feasible_primrec₂` gives the certificate **uniform in the dimension**. This matters and
  the fixed-dimension form does not suffice: the compiler must be `Primrec₂` in
  `(fragment, vertex data)`, and the ambient dimension `d + m + 1` is read off those
  arguments. `feasible_primrec_comp` is the shape a caller applies.
* What remains is the generator itself — building the constraint systems, deciding them,
  and emitting `Rep`.

**2. `Primrec` for the deductive region's vertex enumeration.** Needed only for the
*deductive specialization*'s computability, not for the generic headline. It reduces to
`Primrec fun n => admissiblePatterns (DP.D n) (coords n)`, and thence to `Primrec` for
`Sentence.atoms`, `sentenceBool` and `tableConsistent`. The pinned dependency proves
precisely these at `LIACompiler.lean` 5279–5560 — `atomListTable_prim`,
`formulaBoolStep_prim`, `formulaBoolDecoded_prim`, `sentenceBoolFromAtomList_prim`,
`tableConsistentFromAtomList_prim` — and **all five are `private`**.

This is the same category of blocker as Debt B: module visibility, not mathematics. Debt B
was resolved by a purely additive public re-export upstream (`d89817bc`), and the identical
remedy applies here. Note also that `Primcodable (Finset Sentence)` already exists
(`LIACompiler.lean:2224`), so `Primrec DP.D` is directly statable; what
`DeductiveProcessComputation` supplies is weaker, and that mismatch is recorded in
`FINAL_FORMALIZATION_STATUS.md` §8.

### Verification

Each re-exported lemma typechecks from this repository against the new pin, and CI's `lean`
job builds the whole tree against it in 3m17s against a 25-minute budget. That build is
itself the check that the new pin is in force: `EnforcedCompiler.lean` names the new public
lemmas, so a build against the old revision would fail on unknown identifiers.

### On Aristotle

Not used in this pass. Every goal here is stated against the pinned dependency's own
machinery rather than against mathlib, so none of it can be extracted as the self-contained
statement an offload needs — and once the visibility block was lifted, the recurrence proof
went through on the first attempt. The Aristotle-shaped work in this line was the
representation theorem of §1, pursued separately.
