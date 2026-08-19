# Computability of the modified construction

What has to be computable for the projection route to be a construction rather than a
description, what is now proved, and exactly what is left.

**Summary.** `ComputableMarket` is no longer a premise. The end-to-end theorem takes
effective source data — a computable deductive process, a fragment schedule, a positive
rational tolerance schedule, and a finite representation of each day's projector — plus
one bounded-evaluator compiler, which is the same boundary the pinned source isolates for
its own recurrence. That compiler is **not** discharged here, and §7 says precisely why:
the lemmas needed to discharge it are `private` in the pinned dependency. The obstruction
is module visibility and assembly, not mathematics.

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

## 7. Debt B: what is closed, and what is left

**Closed.** `ComputableMarket` is gone as a premise.
`EnforcedComputation.isLogicalInductor_of_compiler` and
`ProjectionEnforcer.ProjectionSchedule.end_to_end` conclude
`IsLogicalInductor (S.market DP) DP` — the source's *original* criterion — from effective
data plus one bounded-evaluator compiler.

**Left.** Exactly one object:

```lean
structure EnforcedBoundedEvaluatorCompiler (process) (E) where
  computable : Computable₂ (enfEncodedQuoteNatAtFuel process E)
```

This is the same boundary `LIAComputation.LIABoundedEvaluatorCompiler` states for ordinary
LIA, and which `LIACompiler.lean` discharges there in 7366 lines.

**Why it is not discharged here.** The three lemmas the discharge needs are `private` in
the pinned dependency:

| lemma | file:line | what it gives |
| --- | --- | --- |
| `marketMakerSearchUpToTradeList_prim` | `LIACompiler.lean:4804` | the day's bounded market-maker search is primitive recursive in a raw trade list |
| `tradingFirmTradesFromStageTradeLists_prim` | `LIACompiler.lean:6960` | the firm's day-`n` trade list is primitive recursive in the decoded stages |
| `efAbsBound_prim` | `LIACompiler.lean:6254` | `EF.absBound` is primitive recursive |

`LIACompiler.lean` carries 398 private declarations, and the two recurrence-level entry
points sit on top of most of them; the whole erased recurrence
`liaPrefixFromTradeListsAtFuel_prim` is private as well. Re-deriving them downstream would
mean re-doing the bulk of that file, which is neither feasible in one pass nor the right
engineering.

Public and therefore already usable: `Primcodable` for `Sentence`, `ℚ`,
`RationalBeliefState`, `EF`, `Strategy n`, `Finset Sentence`, plus the rational arithmetic
lemmas and `EF.priceQueries`.

**Route to closure — smallest change.** Upstream, in `Formalized-Agent-Foundations`, give
the erased recurrence a trade-list hook:

```lean
def liaPrefixFromTradeListsAtFuel (D) (hook : ℕ → List (EF × Sentence) → List (EF × Sentence))
    (fuel) : ℕ → Option (List RationalBeliefState)
```

appending `hook n firmTrades` to the day's trade list, and prove
`liaPrefixFromTradeListsAtFuel_prim` under a `Primrec₂ hook` hypothesis. Ordinary LIA is
the instance `hook = fun _ _ => []`, so `LIA_is_logical_inductor` is unchanged; this
market is the instance `hook = S.enforcer.trades`. Then expose a public constructor for
the bounded-evaluator compiler. A cruder alternative is simply to drop `private` from the
three lemmas above.

**What remains on this side after that unlock.** `Primrec₂ S.enforcer.trades` — that the
compiled trade list is primitive recursive in the date and the ordinary trade list. That
needs `Primrec` for `repAt` (list zip and lookup), for the `EF` construction in
`affineEF`/`groupEF`/`repEF`/`coefEF` (structural recursion over lists, against the public
`efPrimcodable`), and for `Strategy.tradeListAbsBound` (a list map and sum over
`EF.absBound`). Mechanical; no new mathematics.

**Classification.** Formalization engineering plus one upstream visibility change. **Not
mathematical.**

### On Aristotle

The formalization-orchestration harness's prover backend was not used in this pass, and
the reason is worth recording rather than hiding: every remaining goal here is stated
against the pinned dependency's internal machinery — `Primrec` of specific `private`
definitions in `LIACompiler.lean` — rather than against mathlib, so none of them can be
extracted as the self-contained statement an offload needs. The Aristotle-shaped work in
this line of research is the representation theorem of §1, which is being attempted
separately.
