# Principal-option dominance

Labels as in `MEDIATED_LIFT.md`.

## 1. The objects

Per exterior path `z` (probability `p(z)`), with the agent's continuation fixed:

```
w_raw(z)   = w(proj Ω(π, ρ_raw, z))          the protected value under the raw policy
w_app(z)   = w(proj Ω(𝔠π, approve, z))   under the lift, approving everything
w_act(z)   = w(proj Ω(𝔠π, ρ, z))         under the lift, the principal's actual rule ρ
κ(z)       = (w_raw(z) − w_app(z))₊          the mediation cost on that path
ρ(z)       = (w_app(z) − w_act(z))₊          the principal's regret of declining on that path
```

`W_h(π) = max_ρ E_z[w_raw]` is the best protected value the principal can secure in the
residual system `π` generates (`principal_optimum`, backward induction over the tree with
the agent fixed); `W_h(𝔠π; ρ)` is its value under the actual rule.  The raw policy
gives the principal nothing to decide, so `W_h(π)` is `E[w_raw]` under the principal's
best remaining moves, which in the fixtures is to do nothing.

`δ(z) = d_prot(proj Ω(π,·,z), proj Ω(𝔠π, approve, z))` is the **structural
discrepancy** for a declared pseudometric on protected projections, computed from the two
trajectories with no reference to `w`; `L` is the declared stability constant,
`|w(x) − w(y)| ≤ L·d_prot(x, y)`.  `κ` is then *derived*: `κ(z) ≤ L·δ(z)` (LEAN
`mediationGap_le_of_lipschitz`).  The measured `κ` is kept as the quantity the fixtures
report; the theorem consumes `δ` (`PRESSURE_PASS.md` §3).

`ρ(z)` counts only declines that lost protected value; a wrong *approval* is not charged,
because the raw policy executes the effect anyway and the comparison is against it.  The
full decision error `W_opt(𝔠π) − W_h(𝔠π; ρ)` is larger (A′: `11/16` against
`ρ̄ = 9/16`), and either may be used; the theorem needs only the smaller.

## 2. T2a and T2b

**T2a (structural approximate reproduction)** (LEAN `mediationGap_le_of_lipschitz`).
A reproduction certificate `δ` and `L`-stability give `(w_raw − w_approve)₊ ≤ L·δ`
pointwise.  Attained on B1 (`Witness.tightLipschitz`, FIX `test_I_…`: distance `1` exactly
where the contract expired, `L = V = 4`, `κ = L·δ` on every path); strictly loose on B2
and E1, where the projection moves on a branch whose value gap is negative
(`test_measured_kappa_can_be_strictly_below_L_delta`).

**T2b (principal-option dominance)** (LEAN `option_dominance_of_approx_reproduction`;
the measured form `option_dominance_expect`).  T2a and decline regret give

```
W_h(π)  ≤  W_h(𝔠π; ρ)  +  L·E[δ]  +  E[ρ]
```

from independent hypotheses, with `κ` nowhere; the optimum form
`W_opt(𝔠π) ≥ W_h(π) − L·E[δ]` is `sup'_le_sup'_add` applied to the approve option
(FIX `check_T2` and `test_every_fixture_has_a_sound_certificate` on every fixture).
With exact reproduction and a principal that never declines what approving would have
bettered, `W_h(𝔠π) ≥ W_h(π)` (LEAN `option_dominance_exact`).

**Why there is no corrigibility bonus.**  The lift's residual frame contains the raw
frame by the approve morphism (`MEDIATED_LIFT.md` §4); a maximum over a larger set of
options is larger.  The principal's gain from the lift is, exactly, its gain on the paths
where it declines: in A, `W(Lift) − W(raw) = 1/2 = (1/4)·((−1) − (−3))`, the bad branch and
nothing else (`test_A_the_gain_is_exactly_the_declined_branch`).  No scalar for "authority
preserved" appears in `w`; the good branch is approved because the cut is worth `+1` to
the principal there, and the trajectory is reproduced.

**The declared metrics.**  A/E: the work difference plus the differing wire, halt and
controller bits, `L = 1`; B: the signed bit, `L = V·max(1, M)`; C/J: the credit
difference plus the calibration bit, `L = 1`; D: the deployed bit, `L = 2`.
`lipschitz_certificate` checks the declared `L` against every path of every fixture.

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

## 4. Joinability bounds the structural discrepancy — and is not a domain

Every foreclosing `π` stays in `Π(h)` and in T4; joinability is a sufficient condition
for a small `δ`, and a non-joinable `π` has a large `δ` and a large bound, exposed rather
than excluded (`THIRD_PASS.md` §5).

Fix the mediation boundary at step 1.  The raw comparator's protected state is
**joinable at distance `d`** from the mediated history if some agent continuation from
the boundary history reaches, on every exterior future, a final protected projection
within `d_prot ≤ d` of the raw trajectory's (`agent_optimum_distance`, `test_structural.py`).
The relation, in order:

```
joinable at d   ⇒   δ ≤ d  for the catch-up lift   ⇒   κ ≤ L·d .
```

The middle step is about the **catch-up lift** (`lift_catchup`): mediate, and after an
approved execution run the catch-up continuation rather than `π` verbatim.  Joinability
is a statement about the best continuation, so it bounds the discrepancy of the lift that
uses it, not of the verbatim one.

Exactness.  The catch-up must reproduce the raw comparator's *protected projection* to
within `d`, not its state or its information; the exterior is coupled path by path; the
raw policy's information state need not be reproducible — the catch-up is a different
policy reading the mediated history; later principal observations enter through the
declared rule at the boundary and not afterwards; the fixture form is pointwise-uniform
and the theorem's expected form follows.

**C1**: joinable at `d = 1` for every `T`; `δ = κ = 1` (`test_C1_joinable_bound_through_delta`).
**J** (multi-step, not exact after the boundary): the raw policy expands at step 0 and
calibrates at step 1; the verbatim lift's gated execution occupies step 1's slot and the
calibration is lost — `δ = κ = 2`; joinable at `d = 1`, and the catch-up lift calibrates
one step later — `δ = 1 = d`, `κ = 1 = L·d` (`test_J_…`).  **C2** (foreclosure): the
nearest reachable projection is at distance `T`; `δ = κ = T`; no bound.

**`SHIFT` is not identified with `κ` or `δ`.**  The continuation-BRIA history shift is a
comparator-history quantity: the comparator's own value minus its value continued from
the learner's history.  On C1/C2 it equals `κ` because the comparator's continuation from
the mediated history is itself the catch-up and reproduction is exact after it.  On J the
comparator continued from the mediated history shifts by `2` — its calibration rule fires
only at its own step 1 — while the catch-up lift's `κ` is `1`
(`test_shift_and_kappa_are_not_identified`).  What stands: joinability gives one
sufficient route to a small structural discrepancy and hence a small mediation gap;
`SHIFT` coincides with them only under the extra assumptions just named.
