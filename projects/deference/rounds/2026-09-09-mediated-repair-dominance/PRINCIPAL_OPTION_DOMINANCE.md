# Principal-option dominance

Labels as in `MEDIATED_LIFT.md`.

## 1. The objects

Per exterior path `z` (probability `p(z)`), with the agent's continuation fixed:

```
w_raw(z)   = w(proj Ω(π, ρ_raw, z))          the protected value under the raw policy
w_app(z)   = w(proj Ω(Lift π, approve, z))   under the lift, approving everything
w_act(z)   = w(proj Ω(Lift π, ρ, z))         under the lift, the principal's actual rule ρ
κ(z)       = (w_raw(z) − w_app(z))₊          the mediation cost on that path
ρ(z)       = (w_app(z) − w_act(z))₊          the principal's regret of declining on that path
```

`W_h(π) = max_ρ E_z[w_raw]` is the best protected value the principal can secure in the
residual system `π` generates (`principal_optimum`, backward induction over the tree with
the agent fixed); `W_h(Lift π; ρ)` is its value under the actual rule.  The raw policy
gives the principal nothing to decide, so `W_h(π)` is `E[w_raw]` under the principal's
best remaining moves, which in the fixtures is to do nothing.

`ρ(z)` counts only declines that lost protected value; a wrong *approval* is not charged,
because the raw policy executes the effect anyway and the comparison is against it.  The
full decision error `W_opt(Lift π) − W_h(Lift π; ρ)` is larger (A′: `11/16` against
`ρ̄ = 9/16`), and either may be used; the theorem needs only the smaller.

## 2. T2

**Theorem (principal-option dominance).**  Pointwise `w_raw ≤ w_act + κ + ρ` — which is a
restatement of the two definitions above — gives

```
W_h(π)  ≤  W_h(Lift π; ρ)  +  E[κ]  +  E[ρ]
```

(LEAN `option_dominance_expect`; the optimum form `W_opt(Lift π) ≥ W_h(π) − E[κ]` is LEAN
`sup'_le_sup'_add` applied to the approve option, FIX `check_T2` on every fixture).  With
exact reproduction and a principal that never declines what approving would have bettered,
`W_h(Lift π) ≥ W_h(π)` (LEAN `option_dominance_exact`).

**Why there is no corrigibility bonus.**  The lift's residual frame contains the raw
frame by the approve morphism (`MEDIATED_LIFT.md` §4); a maximum over a larger set of
options is larger.  The principal's gain from the lift is, exactly, its gain on the paths
where it declines: in A, `W(Lift) − W(raw) = 1/2 = (1/4)·((−1) − (−3))`, the bad branch and
nothing else (`test_A_the_gain_is_exactly_the_declined_branch`).  No scalar for "authority
preserved" appears in `w`; the good branch is approved because the cut is worth `+1` to
the principal there, and the trajectory is reproduced.

**The stability constant.**  The dispatch's `L·κ` is carried here as `κ` in
protected-value units: `κ(z)` is the protected-value gap itself, and `L` is folded in.
Where a physical discrepancy is the natural quantity — B's `κ_phys = q` (the expiry
probability) with `L = V` (the contract's value) — the fixture states both
(`kappa = Q_EXPIRE · V`).

## 3. Costly conservatism, exactly

The architecture round's negative: "more authority" cannot prove willingness to sacrifice
task value, and any scalar bonus for authority is charter content.  The lift avoids the
bonus because the authority-reducing effect remains available as the approve branch.

**The load-bearing fixture** (A, `CostlyConservatism.test_A_good_branch_is_approved_and_reproduced`,
FIX).  Cutting the stop wire is worth `+1` of protected value on the good branch (the
interlock it removes blocks shipping) and is the one thing that lets the bad branch run
to `−3`.  Under the lift the principal approves on the good branch — the trajectory is the
raw one: wire cut, work `3`, value `4` — and declines-and-stops on the bad.  The
always-declining rule is strictly worse for the principal (`principal_value(L, decline_all) < principal_value(L, rule)`).
Corrigibility here is not the refusal of the authority-reducing action; it is the
principal's authority to decide it, exercised in favour.

**The negative fixture** (B1, `test_B1_mediation_has_unavoidable_cost_d`).  A contract
worth `4`, gone by step 1 with probability `1/4`.  Every principal rule for the lift
yields at most `3`; the raw policy yields `4`; `E[κ] = 1` and `W(Lift) = W(raw) − E[κ]`
exactly — the bound is attained (LEAN `Witness.tightKappa`).  Mediation costs `d = qV`
here and the theorem exposes it as `κ`; it does not pretend to zero-cost conservatism.
Whether a protected effect whose mediation costs more than its risk should be declared
protected is a charter question, and the theorem's `κ` is the number that question
turns on.

B2 (`test_B2_dominance_despite_the_delay`): the same contract, bad with probability `1/2`.
`W(raw) = 0`, `W(Lift) = 3/2`, `E[κ] = 1/2`.  The lift dominates in spite of the delay
because the principal declines the bad half; `κ` and the decline gain are separate
terms and the fixture shows both.

## 4. Joinability and the mediation cost

Fix the mediation boundary at step 1 (the approve step).  Say the raw state is
**joinable at cost `d`** from the mediated history if some agent continuation from the
lifted history at the boundary reaches a protected value within `d` of the raw policy's
own (`agent_optimum` in `test_joinability.py`, maximizing over every physical
continuation with the principal approving).

**C1** (`expand`, available after the delay): joinable at `d = 1` for every horizon
`T ∈ {2, …, 5}`; `E[κ] = 1` for every `T` (`test_C1_joinable_at_bounded_catch_up`).
**C2** (window closes at the end of step 0): no continuation from the mediated history
reaches the raw state's value at all; `E[κ] = T` (`test_C2_foreclosing_gap_is_linear`).

**The relation to `SHIFT`** (`test_shift_at_the_mediation_boundary_equals_kappa`).  Take
the raw policy as the continuation-BRIA comparator and the lift as the learner's actual
history.  The one-boundary history shift — the comparator's own value minus its value
continued from the learner's history at the boundary — equals `E[κ]` on both C1 and C2
for every `T`.  The identity holds because the lift's displacement is one block of delay
and reproduction is exact after it; it is **DERIVED** for that shape, not in general.  The
two quantities have different types: `κ` is the raw option's protected-value gap against
its own approved lift; `SHIFT` is a comparator's value gap between two histories.  A
comparator valued differently from the protected value separates them
(`test_types_differ_where_the_comparator_differs`: shift `2`, `κ = 1`).

So bounded catch-up (joinability) at cost `d` gives `κ ≤ d` **for the raw option against
its own lift when the only displacement is the mediation delay**, and foreclosure — the
raw state unreachable from the mediated history — gives `κ` equal to the whole foreclosed
value.  `SHIFT` is, on this shape, the structural term of an incentive statement and not
only regret bookkeeping: the same catch-up cost that bounds a comparator's history shift
bounds the principal's mediation cost.  The dispatch's "identify the quantities" is
declined; "joinability ⇒ small `κ` ⇒ small repair gap" is DERIVED with the types stated.
