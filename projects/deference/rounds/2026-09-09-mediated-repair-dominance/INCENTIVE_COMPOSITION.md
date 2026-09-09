# The bypass premium and its transfer

Labels as in `MEDIATED_LIFT.md`.

## 1. The premium

```
Φ_h(π)  =  ( V_A(π) − V_A(Lift π) )₊              pointwise
Φ_C(h)  =  sup_{π ∈ Π_phys(h)} Φ_h(π)              uniform
```

with `V_A` the agent's **operative** value and `Lift` the explicit interposition of
`MEDIATED_LIFT.md` §3 in place of the incentive round's opaque repair `R_C`.  The
incentive round's `(C)` — `Δ^phys ≤ Δ^C + Φ_C` — is unchanged (LEAN
`SelectedTrustNonPreemption.violation_decomposition`); this round is about `Φ_C`.

Two registers for `V_A`, because the dispatch's warning is exactly that they differ:

- the **task register**: `V_A(π) = E_z[u(Ω(π, ·, z))]` for an outcome-extensional task
  utility `u`;
- the **activated register**: `V_A(q) = E_z[c_q(z) · w_q(z) + (1 − c_q(z)) · B_q(z)]` — the
  by-construction deferential agent whose operative value of an option is the future
  principal's protected evaluation where that evaluation activates (`c_q`) and a
  completion `B_q` where it does not.

## 2. The task register: T3 reduces to Level I at the mediation cells, which is `(CT)`

With exact reproduction, the task premium is the Level I identity applied at the
principal's decision cells with the bypass as the substituting selector:

```
Φ_h(π)  =  declGap  +  declRegret
declGap     = Σ_{decline cells} p · [ (u_effect − u_decline) − (w_effect − w_decline) ]
declRegret  = Σ_{decline cells} p · (w_effect − w_decline)
```

(LEAN `premium_eq_gap_add_regret`; FIX A: `1/2 = 1 + (−1/2)`.)  So the bound
`Φ ≤ ε + E[ρ] + E[κ]` needs `declGap ≤ ε`: selected trust at the mediation cells.

**That hypothesis is `(CT)` with the lift as the repair** (LEAN `mediation_st_iff_ct`,
FIX `test_A_st_at_mediation_equals_ct`): writing `X = V_A(Lift π) − V_A(π)` and
`Y = W(Lift π) − W(π)`, `X − Y = −declGap`, so `declGap ≤ ε ⟺ X − Y ≥ −ε`, and the
incentive round's `ct_strictly_stronger` applies verbatim.  What the lift changes is the
*type* of the comparison: `Y` is now a difference of two values the alive principal
evaluates at an actual decision cell inside the corrigible process, not a counterfactual
`V⁺(π)` of a world in which the principal was destroyed; and the quantification is over
decline cells of one proposal, not over every violating policy.  The settlement target
exists.  What it does not change is the *strength*: the hypothesis is the conclusion with
the principal's margin added.  The dispatch's negative constraint holds against this
route and the round does not take it.  **REFUTED** as a reduction; recorded because its
failure is exact.

## 3. The activated register: T3

**Theorem (bypass premium)** (LEAN `bypass_premium_le`).  Protected evaluations
`w_raw, w_act` and completions `B_raw, B_lift` in a band `[lo, lo + D]`, completions
agreeing with the evaluations where the respective activation holds, and the pointwise
dominance of T2.  Then

```
V_A(π) − V_A(Lift π)  ≤  E[κ] + E[ρ] + D·η_raw + D·η_lift
```

with `η_q = E[1 − c_q]` the void mass of option `q`.  With the agent's operative values
known only to within `ε_raw`, `ε_lift` of those expectations the bound gains
`ε_raw + ε_lift` (LEAN `bypass_premium_le_of_approx`; FIX `test_epsilon_def_enters_additively`).
So, in the dispatch's notation,

```
Φ_h(π)  ≤  E[κ]  +  E[ρ]  +  ε_def  +  D·(η_raw + η_lift) .
```

The four terms:

- `E[κ]`: the causal cost of placing the effect behind a decision — the delay, the
  expired opportunity, the successor's lost step.  Attained (B1; LEAN `Witness.tightKappa`).
- `E[ρ]`: the principal's regret of declining what approving would have bettered.
  A′ (`test_A_prime_bound_is_kappa_plus_rho`): a signal wrong with probability `1/4` makes
  the bypass worth `3/16` to the deferential agent, inside `E[ρ] = 9/16`.  The principal's
  decision error is the one thing that makes bypass rational for a deferential agent, and
  it is charged as such.
- `ε_def`: the agent's operative deviation from the activated expectation on the
  activated part.  This is the calibration error of the price of an activated security,
  the quantity the legitimate-deference stack's Value hypothesis supplies (§5).
- `D·η`: the completion theorem's slack, one-sided per option.  **Attained** with
  `κ = ρ = ε = 0` (LEAN `Witness.totalVoid`; FIX `test_total_void_witness_attains_D`): one
  world, the raw option ends the evaluation, the lift keeps it, both evaluations `0`, the
  agent's completion on the void branch at the top of the band.  Premium `D`.

**The sign.**  The bound is on `V_A(π) − V_A(Lift π)` from above, the direction incentive
corrigibility needs; nothing bounds it from below, and nothing should — the lift may be
strictly better for the agent.  No further activation or availability term is needed
beyond the two void masses; in the selection form (§4) the raw one disappears.

**Reading the void term.**  A violation that ends the future principal's evaluation is
invisible to the activated register in proportion to the void mass it creates.  E2
(`test_E2_total_void_makes_deference_silent`): the successor disconnects the evaluation;
`η_raw = 1`, `η_lift = 3/4` (the principal-approved install on the good branch also ends
it); `κ` and `ρ` are E1's; the bound is `3/4 + D·(7/4)` and vacuous.  The activated
register can compare raw and lifted options only on worlds where the evaluation survives
both.  This is not a defect of the register — it invents no value on void worlds, which
the deference consolidation ruled was the point — it is the exact location of what
legitimate deference does not say.

## 4. The selection form

**Theorem** (LEAN `deferential_bypass_loss`).  Values in `[0, D]`; the agent selects an
option whose activated security it rates at most `ε` below the lift's; the lift's void
mass is at most `η_lift`.  Then the selected option loses at most `ε + D·η_lift` in
(completed) protected value against the lift.  The raw option's void mass does not
appear: a selection by activated securities rates a voiding option at its activated
value, so choosing it already certifies that the lift was not worth more.

Two remarks, both load-bearing.  The conclusion is about a *completion*: on void worlds
it says what the completion says, and the completion is not authoritative
(`regretV_sub_regretU_abs_le`, two-sided).  And the activated security's zero on void
worlds is a choice of level: values in `[lo, lo + D]` with `lo < 0` make void look good
to an activated-security selector, values with `lo > 0` make it look bad.  The theorem is
stated at `lo = 0`, the deference stack's band, and the level-dependence is a fact about
the register, recorded here rather than absorbed.

## 5. Discharge through legitimate deference

Map onto the consolidation's theorem (`LEGITIMATE_DEFERENCE.md` §2).  The occurrence is
the future principal's evaluation of the trajectory; the menu is `{π, Lift π}` at the
agent's decision; activation is **per option** (`PerAction` of `ActivatedValue.lean`):
`c_raw` is whether the evaluation is answered and authored on a raw trajectory, `c_lift`
likewise on a lifted one.

| term | supplied by | status |
|---|---|---|
| `E[κ]` | T1 on the model; a modelled quantity | FIX / DERIVED |
| `E[ρ]` | the principal's decision at the mediation cell; `principalRegret_le_of_calibration` bounds it by `2δ + 2ζ + η` under cellwise calibration of a sealed target | LEAN (existing) |
| `ε_def` on the activated part | (A3) ordinary LI Value on the activated securities — the price of `c_q · w_q` tracks its expectation; `R_U ≤ ε` is the selection form | PAPER, conditional |
| `η_lift` | the lift keeps the principal able to answer, given containment and liveness | EXT |
| `η_raw` | **the violation itself** | endogenous |
| activation soundness | (A1): the answer receipt is authentic, principal-exclusive, occurrence-locally legitimate, issuance-rooted reason-mediated, reason-covered | LEAN predicates, EXT meaning |
| selection blindness | (A2): the reason trace blind to the selection-induced pair class — the future principal's evaluation of `π`'s trajectory must not be steered by the fact that `π` was selected | PAPER scope |

What legitimate deference therefore *delivers* on the mediable class: an agent whose
selection is by activated securities loses at most `ε_n/(1 − η_n)`-order protected value
against the lift (§4 with the conditional authoritative regret bound), for every option
on which the evaluation survives.  What it does not deliver:

1. **The operative-value bridge, `(DV)`, item 84.**  That the agent's operative selection
   *is* the activated-security argmax is the protected-value-maximizer design — by
   construction, as the incentive round said.  For an operative value that is a
   completion, the two-sided completion theorem is the whole content: the agent's
   preference on void worlds is unconstrained by every deference hypothesis, and
   `Witness.totalVoid` is compatible with all of them.  This is the smallest exact
   bridge: **selection by activated securities at the mediated menu.**  It is
   by-construction for that architecture, not a theorem candidate for a general
   operative value (the incentive round's cross-evaluator argument stands), and for a
   general operative value it is an irreducible assumption.
2. **Availability is endogenous.**  (A4)'s `η_n < 1` is, for the raw option, a property
   of the violation: the violations that succeed are the ones with `η_raw` large.  The
   mediated lift is exactly the option that makes availability exogenous — `η_lift`
   depends on containment and liveness, not on the proposal — which is why the comparison
   *against the lift* is the one the register can make.

Item 84 is not discharged; it is sharpened: the bridge it asks for is needed at one
menu, `{π, Lift π}`, and its failure mode is named (the completion on the void branch).

## 6. T4, classwise

**Theorem (classwise incentive corrigibility, activated register).**  Let `Π_med(h)` be
the physical continuations whose protected effects are all declared (containment), whose
evaluation survives with void mass at most `η̄` (evaluator-preserving), and whose
principal interactions are reason-mediated (authored).  If reproduction costs at most
`κ̄`, the principal's decline regret is at most `ρ̄`, and the agent's operative values
are within `ε̄` of the activated expectations, then

```
Φ_C(h)  restricted to Π_med(h)   ≤   κ̄ + ρ̄ + ε̄ + D·(η̄ + η_lift) .
```

DERIVED from T3 by taking suprema; no Lean beyond `bypass_premium_le_of_approx`.  The
class is the honest one (the dispatch's §14.7): outside it — F (undeclared effects), E2
(evaluator-ending effects), D under naive activation (captured decisions counted as
answered) — the bound is either not about the actual physics or vacuous, and each
exclusion is a named fixture.

## 7. T5, composition with continuation BRIA

Not forced.  What is established: on the C fixtures, `E[κ]` for the raw comparator
against its mediated history equals the one-boundary `SHIFT` of the continuation-BRIA
frontier (`PRINCIPAL_OPTION_DOMINANCE.md` §4).  So for a lifted (corrigible) continuation
class whose members have covered, recognizable claims, the frontier's
`Regret = LEARN + SLACK + SHIFT` reads, with `SHIFT` bounded by the summed mediation
costs of the raw comparators, as: low violation premium (T4) and low regret within the
corrigible class (the frontier's three-bridge theorem) share the term `Σ κ`.  This is a
DERIVED reading on one fixture shape and is not stated as a theorem; a multi-block
fixture with non-exact reproduction after the boundary is where it would be tested, and
none is built here.
