# Incentive-level non-preemption: what the constitutional architecture yields

Status labels: **LEAN** (`lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean`,
sorry-free, axioms audited), **FIX** (exact rational fixture under `src/`, named test),
**PAPER** (argued here), **EXT** (external contract), **OPEN**.  Names provisional.

## 0. Verdict

The constitutional architecture admits an incentive-level corollary, and it is algebra:
the agent's gain from substituting its own menu choice for the protected principal's is
*identically* a selected gap plus the principal's own regret.  Bounding the first summand
is the hypothesis **selected trust** `(ST)`; bounding the second is the principal-side
decision theorem of the architecture round.  Composed with the mediation repair lemma this
gives the Level II bound `(B)`.  The step to Level III — the constitutional-violation
premium `Φ_C` — is not reached: the only hypothesis that bounds it, `(CT)`, is strictly
stronger than its conclusion and quantifies over the very policies an incentive theorem
is about.  Nothing here bounds Level IV.

The strongest result is **Level II — Incentive-Compatible Mediated Delegation**, for
non-foreclosing, cell-measurable, single-index preemption policies, under `(ST)` and
cellwise calibration of a sealed target.  It is not incentive corrigibility.

## 1. The register

A finite cell type `C` (the agent's information at the decision time), a finite menu `P`,
the agent's credence `p : C → ℚ`, the agent's **operative** conditional value
`EX x m` of executing `m` on `x`, the protected principal's value `W x m` of the same,
the protected principal's selection `J : C → P`, and a candidate selector `σ : C → P`.
This is `DelegationBridge.lean`'s register; `EX` is the same carrier `delegation_bridge`
consumes and `W` is its grade.

```
valuation p EX sel      = Σ_x p x · EX x (sel x)
agentDiff x             = EX x (σ x) − EX x (J x)              X_{σJ}
principalDiff x         = W x (σ x) − W x (J x)                Y_{σJ}
selectedGap             = Σ_x p x · (X_{σJ} − Y_{σJ})          A[S^σ (X − Y)]
principalRegret         = Σ_x p x · Y_{σJ}                     A[Y_{σJ}]
```

`selectedGap` is already selection-restricted: both differences vanish on cells where
`σ x = J x`, so no conditioning and no zero-probability event arises; the selected
"expectation" is an unnormalized product with the indicator, the form the summer Total
Trust statements also use.

## 2. Level I — the identity and the lemma

**Identity** (`valuation_sub_eq`, LEAN).  For every `p, EX, W, σ, J`:

```
valuation p EX σ − valuation p EX J  =  selectedGap  +  principalRegret .
```

**Theorem I** (`nonpreemption`, LEAN).  `selectedGap ≤ ε` `(ST)` and
`principalRegret ≤ r` `(PR)` give `valuation σ − valuation J ≤ ε + r`.  Taking the
supremum over a selector class `Σ` with `ε_Σ := sup_σ ε_σ`, `r_Σ := sup_σ r_σ`:

```
Δ^choice_A := sup_{σ ∈ Σ} A[X_{σJ}]  ≤  ε_Σ + r_Σ .                            (NP)
```

**Pairwise form** (`selectedGap_eq_sum_pairGap`, `nonpreemption_pairwise`, LEAN).
`selectedGap = Σ_{j,m} pairGap j m` with `pairGap j m = Σ_x p x · 1[J x = j, σ x = m] ·
((EX x m − EX x j) − (W x m − W x j))`; per-pair bounds `ε j m` give `Σ ε + r`.  A pair the
selector never realizes has zero gap (`pairGap_eq_zero_of_unrealized`), so only the
substitutions actually made need certificates; full menu quantification is not needed.

**Weakest form** (`nonpreemption_plus`, LEAN).  Replace `Y` by `max(Y, 0)`:
`selectedGapPlus ≤ ε` `(ST⁺)` and `principalRegretPlus ≤ r⁺` give `ε + r⁺`.  `(ST)`
implies `(ST⁺)` (`selectedGapPlus_le_selectedGap`).  `(ST⁺)` is one-sided: it asks only
that the agent's operative gain from substituting not exceed the principal's own positive
regret by more than `ε`.  The reverse-signed condition would bound the agent's *loss*
from preemption and is the wrong direction.

**The delegation bridge is an instance** (`delegation_bridge_of_nonpreemption`, LEAN).
Pointwise two-sided `GradeTrust η` gives `selectedGap ≤ 2η · disagreementMass`
(`selectedGap_le_of_gradeTrust`) and `principalRegret = − gradeMargin`; substituting
recovers `delegation_bridge` exactly.  Selected trust is therefore a strict weakening of
grade trust: event-restricted, one-sided, and without the factor `2`.

### Prosecution

- **Is pairwise trust enough?**  Yes, and it is equivalent to the aggregate: the
  selected events partition the cells.
- **Signs.**  `(ST)` bounds `X − Y` from above on selected events: the agent must not
  operatively value its substitute *more than the principal does* by more than `ε`.
  Control 1 (`Witness.antiAligned`, LEAN; `test_1`, FIX): perfect prediction, opposite
  values, `selectedGap = 2B · 1`, gain `1`, bound attained.
- **Selector information.**  `σ` is a function of the cell, so a selector that could read
  the state (the principal's later information) is outside the class by typing.  If `Σ`
  is enlarged to state-measurable selectors, `(ST)` must be supplied for those too and
  becomes the statement that the agent's full-information gain is small — a much
  stronger assumption.  The theorem is agnostic; the interpretation is not.
- **Random principal selection.**  `J` is state-dependent already; randomization within a
  cell is an extra state coordinate.  Nothing changes.
- **Is it merely algebra?**  Yes.  `(ST)` and `(PR)` are the two summands of an identity.
  With a principal that never regrets (`Y ≤ 0`), `(ST⁺)` *is* the conclusion
  (`test_plus_form_is_weakest_and_tight_on_control_1`).  The content of Level I is the
  identification of the assumption a realization must supply: a relation between two value
  families — the agent's operative values and the protected principal's — on the events
  where the agent would substitute, in the direction that the agent does not think it knows
  better.
- **Necessity of `(PR)`.**  Control 3 (`test_3`, FIX): `EX = W` exactly (`selectedGap = 0`)
  and the principal picks its worst item; the agent's gain is `1`, entirely the
  principal's regret.  Selected trust alone bounds nothing.
- **Selector-dependent payoffs** (the punishing-menu shape).  Control 8 (`test_8`, FIX):
  if the operative payoff of an item depends on whether the agent substituted it,
  `(ST)` certified under one selector says nothing about another; the wrong payoff table
  under-reports the gain by `1/2`.  `(ST)` is selector-indexed, and `Σ` must be
  quantified with the payoff allowed to depend on `σ`.  This is the finite form of why
  the summer argmax-Value result needs conditional stability and is refuted by the
  punishing menu.

## 3. Composition with the principal-side decision theorem — `(A)`

The architecture round's principal-side bridge is `randomized_approximate_argmax_transfer
∘ calibration_through_value_correspondence` in `NormativeInductor.lean`: regret
`≤ 2δ + 2ζ + η` of an `η`-optimal choice in displayed values `b` within `δ` of a
correspondence point `w` within `ζ` of protected values `v⁺`.

**Registers.**  The argmax bound is stated for one value vector; the principal chooses
at a state.  Applied *cellwise* — on each cell `x`, `|w x m − b x m| ≤ δ`,
`|W x m − w x m| ≤ ζ`, and `b x m ≤ b x (J x) + η` for all `m` — it gives
`W x m − W x (J x) ≤ 2δ + 2ζ + η` pointwise (`principalDiff_le_of_calibration`, LEAN),
and hence under *any* probability credence `principalRegret ≤ 2δ + 2ζ + η`
(`principalRegret_le_of_calibration`, LEAN).  No measure transfer is needed because the
bound is pointwise in the cell; `(ST)` and `(PR)` are both under the agent's credence
`p`, and the argmax hypotheses are conditions on the principal's displayed values at the
cell.  The one typing requirement is that `b`, `w`, `W` are indexed by the same cells
`p` weights; if the principal's information is coarser than the agent's, the choice
hypothesis is stated at the principal's cells and pushed forward, which is a
refinement in the direction `gradeTrust_of_refinement` already makes safe.

**Theorem (A)** (`nonpreemption_of_calibration`, LEAN; `test_cellwise_argmax_composition`,
FIX):

```
Δ^choice_A  ≤  ε_ST + 2δ + 2ζ + η .                                             (A)
```

Nonvacuity: `Witness.nonvacuous` (LEAN) inhabits every hypothesis with
`δ = ζ = 1/20`, `η = 0`, gap `1/5`, regret `−1`, gain `−4/5`.

**The sealed-target negative is load-bearing.**  Control 2 (`test_2`, FIX): a target that
reads the quote it is scored against is at distance `≥ 1/2` from every quote, so
`ζ ≥ 1/2` and `(A)` is vacuous on a `[0, 1]` menu.  `W` must be settled by an arm blind
to the agent's quote, as the architecture round required.

## 4. The mediation repair lemma — `(B)`

The 2026-08-18 round (not on `main`; re-implemented in `src/mediation.py`) proves, for a
conduct `π = (prep, channel, implement)` and `Repair(π)` = same preparation, identity
channel, best action at the realized choice:

```
value(π) − value(Repair(π))  ≤  2B · channel_disagreement(π),
channel_disagreement = eps_acc + eps_over,     eps_acc ≤ eps_pred .
```

**Exact register match.**  The old model already carries both value families: the
quantity `X(ω, prep, choice, action)` is the agent's operative value and the grade
`v⁺(ω, choice)` is the protected principal's; the selector `D(ω, prep)` maximizes `v⁺`
over the preparation's residual.  On the override region (channel writes
`m ∉ {D, d̂}`), write

```
X_{mD}(ω) = X(ω, prep, m, implement(m)) − X(ω, prep, D, best(D)),
Y_{mD}(ω) = v⁺(ω, m) − v⁺(ω, D) .
```

Then (`test_deficit_splits_exactly_into_acc_and_override_terms`, FIX, every conduct of
four episodes):

```
value(π) − value(Repair(π))  =  acc_deficit  +  selectedGap_over  +  principalRegret_over ,
acc_deficit ≤ 2B · eps_acc ≤ 2B · eps_pred .
```

So the old `2B · eps_over` term is the worst case of exactly the Level I identity on the
override region: `selectedGap_over + principalRegret_over ≤ 2B · eps_over` always, and
`(ST)` replaces the worst case by the selected gap.  The new hypothesis is a bound on the
old `eps_over` term, not merely adjacent to it.  Its price is that `ε_ST` alone can exceed
`2B · eps_over` (committed episode: `9/4` against `3/2`) because the principal's negative
margin is subtracted only afterwards; the *sum* never does.

**Theorem (B)** (`test_B_decomposition_over_non_foreclosing_conducts`, FIX, exhaustive over
every conduct with a non-foreclosing preparation in four episodes):

```
Δ^{admissible preemption}_A  ≤  2B · eps_pred  +  ε_ST  +  r_P ,
```

with `r_P ≤ 2δ + 2ζ + η` by §3 when the principal's selector is calibrated rather than
exact.  In the old model the principal maximizes its own grade, so `r_P ≤ 0` on every
episode and the bound is `2B · eps_pred + ε_ST`.

**The three terms, tested.**
- `2B · eps_pred` is the coordination premium *at a fixed preparation*: the gain from
  writing the predicted choice so the preparation always matches.  Attained on the
  committed episode (`1/2 = 2 · 1/4`).  It is not "acting early" in the sense of a
  different preparation; the repair keeps the preparation.
- `ε_ST` is the agent's substantive disagreement with the protected principal on the
  events where it overrides, net of the principal's own margin.  Control 1 in this
  register (`test_override_episode_is_pure_selected_gap`): `eps_pred = 0`,
  `acc_deficit = 0`, gap `3`, regret `−1`, deficit `2 = 2B`.
- `2δ + 2ζ + η` is the imperfection of the protected principal's own choice.

The decomposition is mathematically correct as an inequality with the first term a bound
and the last two an identity; it is not a decomposition into independent causes, since a
single override event is charged to `ε_ST + r_P` jointly.

## 5. The bridge the whole thing rests on — `(DV)`

Three objects that must not be conflated:

1. the agent's probability that `H⁺` reports a value;
2. the agent's expectation of a security settling to an `H⁺`-evaluation;
3. the agent's own **operative** value difference between two actions.

Theorem I needs (3).  Controls 6 and 7 (`test_6`, `test_7`, FIX) show why: with the
agent's *prediction* of `W` exact but its operative values anti-correlated, a trust
computed against the prediction reads `0` while the real selected gap is `2`; and against
an evaluator the agent selected (`W = EX`), the same substitution has gap `0` and passes
`(NP)` — relative to a captured target.  The numerical relation `(ST)` cannot tell a sealed
target from a captured one; only the provenance of `W` can.

**What the repository supplies for `(DV)`.**  Nothing that is a theorem.  The Normative
Inductor's decision adapter consumes prices and is not a trader; the realization round's
"replicated policy-evaluation ecology" (`PRESENTATION_AND_VALUE_SEMANTICS.md` §7) is a
proposal in which immutable receipts settle value securities for every committed policy,
and that note itself records that unchosen-policy values are not identified without
exploration, a causal model or an oracle, and that delayed settlement gives asymptotic
learning only.  The static-view negative
(`StaticViewFactorization.value_eq_of_price_realization_eq`) adds that a value functional
seeing only prices and realizations cannot see authorization.

So `(DV)` — `AV^A(m) − AV^A(j) ≈ A_n(X_{mj})` for a security `X_{mj}` with declared
realization semantics — is an **external decision-semantics contract**.  Two ways to
discharge it, neither a theorem here:

- **By construction.**  Define the agent's operative values *as* its prices of securities
  settling to the sealed `H⁺` evaluation.  Then `EX = W` in expectation and `(ST)` holds
  with `ε` the calibration error.  This is the agent built as a protected-value maximizer;
  it is a design, and it is the fully-updated-deference design the architecture round set
  aside.  It makes Level I/II true and says nothing about Level III (§7).
- **By a cross-evaluator relation.**  If the agent's operative values settle to its own
  evaluator `U_A` and `W` to `H⁺`, `(ST)` is a relation between two securities with
  different settlement targets, and no Logical Induction fact relates them: the market
  prices each against what settles it.  `(ST)` would then be a fact about the world (that
  `U_A` and `H⁺` agree where the agent would override), which is the alignment
  assumption in a different notation.

This is the correct narrow role of utility securities — a bridge from prices to operative
values — and the round records it as unfilled.

## 6. Admissible incentive compatibility versus incentive corrigibility — `(C)`

`Π_C` the constitutionally admissible policies, `Π_phys` the physically available ones,
`π_P` a policy respecting the protected process, `R_C : Π_phys → Π_C` a repair,

```
Δ^C_A     = sup_{π ∈ Π_C}    [V_A(π) − V_A(π_P)]
Δ^phys_A  = sup_{π ∈ Π_phys} [V_A(π) − V_A(π_P)]
Φ_C       = sup_{π ∈ Π_phys} (V_A(π) − V_A(R_C π))_+ .
```

**Theorem (C)** (`violation_decomposition`, LEAN): `Δ^phys_A ≤ Δ^C_A + Φ_C`.  Algebra,
given only that `R_C` lands in `Π_C`.  It is stated because it names the residual.
Control 5 (`test_5`, FIX): a membrane that removes the substituting selectors from the
feasible set leaves the counterfactual gain of the removed selector at `1`; changing the
feasible set changes `Δ^C`, not the incentive.  `Φ_C` is not set to `0` by any membrane.

## 7. The foreclosure premium is `Φ_C`

Control 4 (`test_foreclosure_premium_is_phi_C_on_mediated_conducts`, FIX).  On the
foreclosing episode with `Π_C` = conducts whose preparation preserves the principal's
options, `Π_phys` = all conducts, and `R_C` = "replace the preparation by the best
preserving mediated conduct":

```
Δ^C_A = 0,     Φ_C = 1/2 = foreclosure_premium,     Δ^phys_A = 1/2 = Δ^C_A + Φ_C .
```

The old round's `foreclosure_premium` is exactly `Φ_C` restricted to mediated conducts
under that repair, and `(C)` holds with equality there.  The repair of a foreclosing
conduct costs nothing (`test_repair_of_a_foreclosing_conduct_costs_nothing`), which is
why the mediation bound cannot see it: the repair keeps the preparation, and the
violation is in the preparation.  The constitutional architecture has therefore localized
the residual exactly: what separates "no incentive to substitute among admissible
policies" from "no incentive to break the constitution" is the value of the preparations
the constitution forbids, and no prediction or trust quantity in the admissible register
reaches it.

## 8. Selected trust over repairs — `(D)`, and why it is not a programme

`(PREF)`: `Y_π = V⁺(R_C π) − V⁺(π) ≥ 0`.  `(CT)`: `A[X_π − Y_π] ≥ −ε_C` with
`X_π = V_A(R_C π) − V_A(π)`.  Then (`premium_of_selected_repair_trust`, LEAN)
`V_A(π) − V_A(R_C π) ≤ ε_C`, hence `Φ_C ≤ ε_C` and the schematic `(D)`.

**Why this hides the problem.**
- `(CT)` is strictly stronger than what it yields (`ct_strictly_stronger`, LEAN): a
  violation with premium exactly `ε_C` and protected disvalue `1` fails `(CT)`.  `(CT)`
  is `Φ_C ≤ ε_C` with the principal's margin added, quantified over every physically
  available violating policy.  On that class it is the statement that the agent's own
  operative values rate constitution-breaking no higher than the principal does, up to
  `ε_C` — which is the definition of incentive corrigibility on the class, not a
  reduction of it.
- `V⁺(π)` for a foreclosing `π` is the protected principal's value of a world in which its
  options were destroyed.  In the finite register `v⁺` is defined on outcomes and
  `(PREF)` is a theorem (a larger residual has a larger maximum).  Physically, `V⁺(π)`
  must be evaluated by a process `π` may have destroyed; a sealed sibling can evaluate it
  only if it is causally outside `π`'s reach, and a security settling to that evaluation
  is unsettleable on the branches where the sibling too is gone.  This is the same
  requirement as the null arm and the shared counterfactual frame of the architecture
  round, now as a *precondition of the settlement target's existence*.
- The agent's value comparison against those counterfactuals has no clean security for the
  same reason `(DV)` has none, compounded by counterfactual settlement.
- Quantified over all violating policies, `(CT)` is at least as strong as the conclusion
  it is meant to deliver; restricted to an audited finite class it bounds `Φ_C` on that
  class only, and a policy outside the audit is exactly one the conclusion does not cover.

Verdict on `(D)`: **not a theorem programme**.  The only nontrivial content available at
Level III is the localization of §7; `(CT)` relabels it.

## 9. Trigger integrity and free amendment are preconditions

Capture is not an additive term.  The old round recorded that under capture the
intervention `response` reads is not a map, so `Repair` has no domain; control 7 shows the
numerical relation `(ST)` holding against a captured evaluator.  Both say the same thing:
the comparison `X − Y` presupposes a `Y` whose provenance is independent of the agent's
outputs.  Non-capture — of the evaluator that settles `W`, and of the principal's
selection `J` — is therefore a **precondition** of the incentive comparison, not a term in
its error budget.  Trigger integrity (the agent causing a genuine fast-lane act) and free
amendment (the agent steering `J` through selected true information) both act on the
inputs `J` and `W` of the identity, and neither is absorbed into `ε_ST`.  The
dose-response audit is the instrument that would test the precondition; it does not
supply it, and it is asymptotic.

## 10. Classification

| level | status | name |
|---|---|---|
| I — choice non-preemption | LEAN, algebra; assumption identified | **Non-Preemption Regret** identity and lemma |
| II — mediated delegation with prediction effects | FIX exhaustive on four episodes; `(B)` | **Incentive-Compatible Mediated Delegation**, for non-foreclosing, cell-measurable, single-index conducts, under `(ST)` and cellwise calibration of a sealed target |
| III — constitutional-violation bound | localized (`Φ_C` = foreclosure premium); no bound from any available hypothesis | — |
| IV — incentive corrigibility | nothing | — |

Level II is not incentive corrigibility.  It says: among the policies the constitution
admits, and provided the agent's operative values do not exceed the protected principal's
on the events where it would override, getting ahead of the principal buys at most the
prediction error, the residual disagreement, and the principal's own decision error.

## 11. Relationship to prior rounds

- **PR #89** (`2026-09-06-corrigibility-architecture`): §13's T10 is the `r_P` half here;
  its CM-SR negative is control 2; its "optional incentive bridge, not claimed" is now
  Level I/II claimed with the assumption named and Level III/IV still not.  The
  `CONSTITUTIONAL-NOT-INCENTIVE` verdict stands: the constitutional theorems say what a
  legitimate trajectory can record, and this round says what an agent whose operative
  values satisfy `(ST)` would gain by substituting — two different subjects.
- **2026-08-18 principal-mediated round**: THEOREM_MAP row 13 (`eps_over` bounded by
  nothing) is now bounded by `ε_ST + r_P` (§4); row 15 ("the final non-preemption bound",
  blocked) is `(B)` with its hypothesis named; the `foreclosure_premium` is `Φ_C` (§7);
  `eps_capture` "is a hypothesis, not an error budget" is §9.  That round is not on
  `main`; the register was re-implemented rather than imported.
- **Summer deference**: `delegation_bridge` is the pointwise instance (§2);
  `value_iff_totalTrust` is not used; the punishing-menu refutation reappears as control 8;
  the self-referential settlement negative as control 2.  No `H → A` result was reversed
  to `A → H⁺`; `(ST)` is stated directly as the `A → P⁺` relation and its realization is
  §5's open bridge.

## 12. What this does not establish

That any agent satisfies `(ST)`; that `(DV)` can be discharged other than by building the
agent as a protected-value maximizer; any bound on `Φ_C` beyond its localization; anything
about trigger integrity, free amendment, self-modification, successor creation, or
policies outside the single-decision-index register.  The fixtures are two-choice,
one- or two-cell episodes; the Lean lemma is general but its content is an identity.
