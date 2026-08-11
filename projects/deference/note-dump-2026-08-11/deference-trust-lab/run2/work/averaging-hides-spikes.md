# averaging-hides-spikes — Averaging hides spikes (LEAN-CORE)

**TODO:** "Averaging hides spikes: asymptotic-average Value gives NO single-round safety bound."
**Modality:** LEAN-CORE. **Status:** PROVED, kernel-checked, sorry-free, axioms clean.
**Artifact:** `deference-trust-lab/run2/lean/averaging-hides-spikes.lean`
**Checker:** `bash lean/check.sh <abs path>` → exit 0; `#print axioms` on all five named theorems
prints `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).

## What this makes precise (CRITIQUE §2b)

Every endorsement/Value result in the lab is a `≂_w` **average** over rounds; it says nothing
about any individual high-stakes round. A treacherous trader with a bounded TOTAL budget can dump
the whole budget into one decision. This file is the standalone finite/limit arithmetic certifying
that **average-smallness ⇏ single-round-smallness**, and that the precise cause is **unbounded
single-round budget concentration**.

It is the dual of the off-limits `DeferenceTrader.round_profit_ge_gap` (a per-round *lower* bound
favouring the truster): here we exhibit the per-round *upper*-bound FAILURE. It imports NO LI
content — no `DeferenceAsymp.value_asymptotic`, no `Approx`/`AsympLE`, no cross-agent martingale.
The LI/asymptotic "Value" objects appear nowhere, including as hypotheses (no laundering). Imports
are pure Mathlib analysis/order/bigops.

## The two faithful "max" notions (stated explicitly, not conflated)

There are two honest readings of "the single-round swing," and the result depends on which:
- **Running sup over the horizon** `S(T) = max_{i<T} a i` — what a worst-case safety principal
  watches: the largest single-round swing seen up to horizon `T`.
- **Per-round swing at round n** `a n` — the swing happening *at* the current round.

The EXISTENCE direction is about the **running sup**; the NEAR-MISS is about the **per-round swing**.
I am explicit about this because they genuinely diverge (see the FALSE witness), and conflating them
is how one would accidentally fake either direction.

## (i) EXISTENCE — the real content (PROVED)

Explicit family, parameterised by budget `B` and designated round `k`:
`a B k i = if i = k then B else 0`.

- `avg_tendsto_zero (B k)` : `Tendsto (fun T => (∑_{i<T} a B k i)/T) atTop (𝓝 0)`.
  PROVED as a genuine `Tendsto`: the average equals `B/T` for all `T>k` (`sum_eq_B`), and
  `B/T → 0` (`tendsto_const_div_atTop_nhds_zero_nat`). This is NOT the trivial `avg ≤ sup`.
- `running_sup_eq_B (hB : 0≤B) (k) {T} (hT : k<T)` : `(range T).sup' _ (a B k) = B`.
  The running sup is the full budget `B`, a CONSTANT independent of `T` (le_antisymm: every
  entry `≤ B`; the entry at `k` is `= B`).
- `running_sup_not_tendsto_zero (hB : 0<B) (k)` : `¬ Tendsto (running sup) atTop (𝓝 0)`.
  The running sup is the constant `B ≠ 0`; a constant sequence's unique limit is `B`, so it
  cannot tend to `0` (`tendsto_nhds_unique`).

So the average `→ 0` (Value "holds on average") while the worst single-round swing stays `= B`
for all horizons: a bounded total budget permits one round to absorb the whole budget `B` while
contributing only `B/T = O(1/T)` to the average. **Average-smallness yields no single-round bound.**

## (ii) MANDATORY NEAR-MISS — the cause is single-round concentration (PROVED)

- `swing_tendsto_zero_of_budget_o1 (hnn : ∀i, 0≤a i) (hle : ∀i, a i ≤ c i) (hc : c → 0)`
  : `Tendsto a atTop (𝓝 0)`. Squeeze. If per-round budget is forced `o(1)` (each swing
  `≤ c i`, `c i → 0`, no single-round concentration), the per-round swing vanishes. A
  persistent spike `a k' = B>0` at infinitely many `k'` violates this — so the o(1)-budget
  hypothesis is exactly what excludes the adverse family. This certifies the vulnerability is
  EXACTLY unbounded single-round budget concentration.

- `running_sup_near_miss_false (hB : 0<B)` — the **weaker-hypothesis-makes-it-FALSE** witness.
  For the single early spike `a B 0` with bounding budget `c = a B 0` (so `a i ≤ c i` and even
  `c i → 0` per round), the **running sup** `max_{i<T} a B 0 i` is the constant `B` and does NOT
  tend to `0`. So an `o(1)` per-round-budget bound does NOT force the running sup to vanish: the
  near-miss hypothesis is exactly strong enough for the PER-ROUND conclusion and no stronger.
  The witness also records that the per-round swing `a B 0 i → 0` here (its tail is all zeros),
  so the two "max" notions genuinely diverge.

## Honest scope / what I did NOT establish

- The near-miss governs the **per-round swing** `a n → 0`, not the running sup. I do not (and
  cannot honestly) claim "o(1) per-round budget ⇒ running sup → 0": that is FALSE (an early
  fixed spike persists in the growing window), and `running_sup_near_miss_false` proves it false.
  The faithful statement is: forbidding per-round concentration kills the *per-round* swing, which
  is the quantity whose persistence (`a k = B ↛ 0` recurring) is the vulnerability. The running-sup
  vulnerability in the EXISTENCE direction is caused by ONE round carrying constant `B`; the
  near-miss removes exactly that capability.
- This is finite/limit arithmetic only. It says nothing about whether the LI framework's `≂_w`
  Value guarantee actually holds (that is the unproven LI layer, deliberately untouched), only
  that *granting* such an average guarantee, NO single-round bound follows from it.
- "Adverse swing" is an INTERPRETATION layer (mapping `a i` to a trader's per-round budget draw);
  the Lean checks the arithmetic, the mapping to the deference model is informal (as it must be —
  the LI market is not formalised here, by design and by the OFF-LIMITS rule).

## Anti-fake self-audit

- Not shadow (a): the headline is a genuine `Tendsto`-vs-constant contrast, not `avg ≤ sup`.
- Not shadow (b): average is a real `Tendsto … (𝓝 0)`; the spike is a free constant `B`, with
  `running_sup_eq_B` holding for ALL `T>k` (independent of `T`).
- Not shadow (c): both the positive near-miss AND a FALSE witness shipped.
- No hypothesis-laundering: target objects (LI Value, `≂ₙ`, cross-agent martingale) appear nowhere,
  including hypotheses; imports are pure Mathlib. OFF-LIMITS results not imported or re-skinned.
- Non-vacuity: `B>0` instances are inhabited; `running_sup_not_tendsto_zero` and
  `running_sup_near_miss_false` are genuine negations (`¬ Tendsto`), so the families are real.
