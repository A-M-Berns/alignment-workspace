# Countermodels

Numbered as the prompt numbers the pressure tests; C1/C3/S1 witnesses first.  Every
fixture is in `src/fixtures.py` and asserted in `tests/`.

## C1 — the measure form (`c1_measure_form`, Lean `measure_form_refuted`)

`I¹ = [0, 1/10]`, `I² = [9/10, 1]`; `p¹ = 0`, `p² = 9/10`.  Gap `9/10`; hull width `1`;
union length `1/5`.  The hull bound holds; the measure bound fails.  Breaks: C1 as
written with `|·|` read as length.

## C3 — item-level humility (`sandwich`, Lean `c3_refuted`)

Fragment `{φ, ¬φ}`, coherence `P(φ) + P(¬φ) = 1`.  `S¹ = {P(φ) ≥ 1/2, P(¬φ) ≥ 1/2}`
(both strengths `1/2`), `S² = ∅`, `W = ∅`.  `I_φ(S¹) = [1/2, 1/2]`, `I_φ(S²) = [0, 1]`.
Elimination cross-check agrees.  Breaks: C3 under the prompt's humility.

## C3 — strict humility does not break (`strict_humility`)

Closed layer `p ≤ q`, `q ≤ 1/2`.  Closed item `p ≥ 1/2`: `p = q = 1/2` pinned.  Strict item
`p > 1/2`: empty.  Refuted, not pinned.  Records that C3′'s hypothesis is what the
sandwich violates.

## C2 — the calculus does not compute an extension (`defeat_calculus`)

`W ← D1 ← D2`.  Grounded `{W, D2}`; live sets `{W', D1', D2}`, `{W', D1, D2}`,
`{W, D1, D2}` on three exhaustive admissible traces.  Breaks: C2 as a theorem of the
landed calculus.

## S1 — infinite discovery class (`stabilization_oscillation`)

`w_k : P(φ) ≥ 1/2` at date `2k − 1`, its undercut at `2k`.  `I_φ` alternates
`[1/2,1], [0,1], …`; four reopenings of `1/2` in eight dates, no limit.  Breaks: S1
without finiteness.  Restored by summable reopenings (`stabilization_summable`, drops
`3/4, 1/8, 1/16, 1/32, 1/64, 1/128`, sum `127/128`, limit `1/2`; Lean
`tendsto_of_summable_drops`).

## 1. Dogmatic item (`test_1_dogmatic_item`)

`S¹ = {P(φ) ≥ 1}`, `S² = ∅`: `[1,1]` versus `[0,1]`.  Not item-humble; not strict; the
pin is permanent under every `F`, `W` extending these.

## 2. Hysteresis (`hysteresis`)

Candidates `ρ ∈ {3/10, 6/10, 9/10}` (lower), `σ ∈ {95/100, 8/10, 5/10}` (upper),
strongest-feasible on arrival.  Order `ρ,σ`: `[9/10, 19/20]`.  Order `σ,ρ`:
`[3/10, 1/2]`.  Both maximal.  Canonical joint rule (widest feasible combination):
`[9/10, 19/20]` in either order.  Breaks: order-independence of the forced region under
greedy strength selection; also shows plain reopening does not restore it.

## 3. Refinement without transport (`refinement`)

Old `{p, q}` with structural `P(p) = P(q)`; new `{p, q, p₁, p₂}` with `p = p₁ + p₂`
and `q = 1/2`.  Conservative: `p = 1/2`, `p₁ ∈ [0, 1/2]`, `p₂ ∈ [0, 1/2]`.  Narrowing
(`p ↦ p₁`): `p₁ = 1/2`, `p₂ ∈ [0, 1/2]`, `p ∈ [1/2, 1]`.  Breaks: C3 through the
structural layer with identical substantive seeds.  Both on `τ`: equal.

## 4. Price convergence without reason convergence (`price_without_reason`)

`X`, `Z` settled true.  `R¹`: `P(X) ≥ 9/10`, `P(φ) ≥ 2/3·P(X)` (ports `0,1`);
`R²`: `P(Z) ≥ 9/10`, `P(φ) ≥ 2/3·P(Z)` (ports `2,3`).  `I_φ = [2/3, 1]` for both;
ports disjoint.  Breaks nothing; bounds what confinement says.

## 5. Substantive in disguise (`disguise`, Lean `disguise_caught`)

`P(φ) = P(¬φ)` as impartiality, with coherence: both coordinates pinned to `1/2`;
level neutrality catches it.  `P(x) = P(y)` on unrelated `x, y`: no level narrowed;
caught by symmetry generation under the identity symmetry, passed under a declared swap.
Breaks: the claim that a checkable criterion catches every disguise — it catches every
disguise not licensed by a declared symmetry.

## Also on file

- **Defeat widens** (`defeat_widening`, Lean `defeat_widens`): `[1/2,1] → [0,1]`.
- **Mirror-pair impartiality narrows a level** (moral fixture): `r(a,b) = r(b,a)` with
  completeness gives `[1/2, 1]` from structure alone; flagged by level neutrality, passed
  by symmetry generation (`SEED.md` §3).
- **Seed leverage is blind to relational content**: `P(x) = P(y)` has leverage `0`.
- **Humble population axioms still break** (`population_fixture(c)`): infeasible for
  every `c > 2/3`, feasible at `c = 2/3`.
