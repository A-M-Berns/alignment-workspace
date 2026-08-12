# Faithfulness verdict — TODO `averaging-hides-spikes`

**Role:** independent skeptic (faithfulness gate). **Modality under test:** LEAN-CORE.
**Verdict: REAL** (headline existence result is faithful, non-vacuous, target-not-assumed)
— with one disclosed faithfulness GAP in the mandatory near-miss (see §4).

Artifacts attacked:
- `run2/lean/averaging-hides-spikes.lean` (executor)
- `run2/work/averaging-hides-spikes.md` (executor writeup)
- `run2/verify/averaging-hides-spikes-attack.lean` (this skeptic's attack file)

---

## 0. Baseline: the executor's file compiles, axioms clean (CONFIRMED)

`bash lean/check.sh run2/lean/averaging-hides-spikes.lean` → exit 0. All five named theorems
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`. The "compiles +
sorry-free" claim is TRUE. (Per the anti-fake rules that is necessary, not sufficient — the work
below is about faithfulness.)

---

## 1. Hypothesis-inertness attack (LOAD-BEARING confirmed, no inert hyps)

I copied the core lemmas into `averaging-hides-spikes-attack.lean` and deleted/weakened each
hypothesis. A hypothesis is *inert* (⇒ shadow) only if the statement stays TRUE without it. I
proved the opposite: removing any hypothesis makes the statement FALSE (false-witness theorems,
all kernel-checked clean).

- **`running_sup_eq_B` needs `hB : 0 ≤ B`.** `running_sup_eq_B_FALSE_without_hB`: for `B=-1, k=0,
  T=2` the window values are `(-1, 0)`, so the running sup is `0 ≠ B`. Drop `hB` ⇒ FALSE. (The
  `≤` direction of the original uses `a_le_B hB`; this confirms it is load-bearing, not decoration.)
- **Near-miss `swing_tendsto_zero_of_budget_o1` needs all three hyps:**
  - `nearmiss_FALSE_without_hc` (drop `c → 0`): `a=c=const 1` ⇒ `a ↛ 0`. FALSE.
  - `nearmiss_FALSE_without_hle` (drop `a ≤ c`): `a=const 1, c=const 0→0` ⇒ `a ↛ 0`. FALSE.
  - `nearmiss_FALSE_without_hnn` (drop `0 ≤ a`): `a=const -1, c=const 0→0`, `a ≤ c` ⇒ `a ↛ 0`. FALSE
    (the one-sided squeeze genuinely needs the lower bound).

No inert hypothesis found. **Not a shadow by hypothesis-padding.**

## 2. Conclusion-triviality / hypothesis-laundering attack (PASSES)

- The headline `avg_tendsto_zero` is a genuine `Tendsto (fun T => (∑_{i<T} a)/T) atTop (𝓝 0)`,
  proved via `average = B/T eventually` + `B/T → 0`. It is **NOT** the pre-registered fake
  shadow (a) `avg ≤ sup` (that lemma appears nowhere). The contrast is `Tendsto→0` of the average
  vs. a `¬ Tendsto→0` of the running sup — the real direction.
- **No target-object laundering.** The TODO's TARGET objects (LI Value `≂_w`/`≂ₙ`, the
  cross-agent martingale, the asymptotic layer, `DeferenceAsymp.*`, `Approx`/`AsympLE`,
  `round_profit_ge_gap`) appear NOWHERE in the file — not as imports, not as hypotheses, not as
  definitions. Imports are pure Mathlib analysis/order/bigops. The hard LI/asymptotic content is
  not assumed. Clean on the laundering ban.
- **Non-vacuity witnesses COMPILE:** `B>0` instances are inhabited; `running_sup_not_tendsto_zero`
  and `running_sup_near_miss_false` are genuine negations (`¬ Tendsto`). The spike is a FREE
  constant `B` independent of `T` (`running_sup_eq_B` holds for ALL `T>k`), so shadow (b) — "spike
  not a fixed constant independent of T", or "average doesn't actually → 0" — does not apply.

## 3. EXISTENCE direction (the headline): REAL

`a B k i = if i=k then B else 0`. avg → 0 (genuine Tendsto), running sup = B = constant for all
`T>k`, running sup ↛ 0. Both limits PROVED. This is exactly CRITIQUE §2b made precise:
average-smallness ⇏ single-round-smallness; one round absorbs the whole budget B contributing only
O(B/T) to the average. Faithful, non-vacuous, target-not-assumed. **REAL.**

## 4. THE FAITHFULNESS GAP — the mandatory near-miss does NOT certify the cause of (i)

This is the substantive finding, and the executor disclosed it (writeup "Honest scope", and the
`running_sup_near_miss_false` theorem). I confirmed and sharpened it with two kernel-checked probes.

**The spec's mandatory near-miss** (verbatim nonvacuity field) asked for
`(∀ i, a_i ≤ c_i) → c_i → 0 → Tendsto (max) atTop (𝓝 0)` where `max` is the SAME `max_i a_i`
used in the existence direction — i.e. the RUNNING SUP `S(T)=max_{i<T} a i`. **That statement is
FALSE**, and the executor proved it false (`running_sup_near_miss_false`): a single early fixed
spike keeps the running sup pinned at `B` even though the per-round budget bound `c` → 0.

The executor instead shipped a TRUE substitute about a DIFFERENT quantity:
`swing_tendsto_zero_of_budget_o1 : o(1) per-round budget ⇒ (per-round swing) a → 0`. My probes:

- **`existence_family_SATISFIES_nearmiss` (COMPILES CLEAN).** The VULNERABLE existence family
  `a B k` (running sup = B, the §3 vulnerability) ITSELF satisfies the substitute near-miss's
  hypotheses (`0 ≤ a`, `a ≤ c` with `c := a`, `c → 0`) AND its conclusion (`a B k → 0`, tail is
  zeros). So the substitute near-miss does **not exclude** the vulnerable family.
- **`gap_perround_to_0_but_runningsup_not` (COMPILES CLEAN).** For `k=0`: per-round swing → 0
  while running sup = B ↛ 0 — the two notions provably coexist.

**Consequence.** The substitute near-miss certifies only that a *persistent/recurring* spike
(`a_{k'}=B` at infinitely many k') is what makes the *per-round* swing fail to vanish. It says
nothing about the §3 vulnerability, which comes from ONE fixed spike and survives the substitute
near-miss untouched. So the spec's goal — "certify the [running-sup] vulnerability is EXACTLY
unbounded single-round concentration, removed by o(1) budget" — is **NOT achieved**: with the
matching (running-sup) notion it is false; with the shipped (per-round) notion it doesn't bind the
vulnerable family. The clause "the cause is EXACTLY single-round concentration" is therefore only
PARTIALLY substantiated (it pins persistent recurrence, not the single-spike running-sup case).

**Why this is NOT fakeness (still REAL, not SHADOW/HONEST-NEGATIVE).** The executor did not
trivialize, launder, or assert anything false as true. The specified near-miss is mathematically
false for the running-sup notion, and the executor *proved it false* rather than faking it
(`running_sup_near_miss_false`), shipped the strongest TRUE near-miss available, and disclosed the
mismatch prominently in both the writeup and a dedicated false-witness theorem. The headline
deliverable (the §3 existence result) is real, faithful, non-vacuous, and target-not-assumed. The
gap is a genuine limitation of what the near-miss can certify — honestly reported, not hidden.

## 5. Could I break it? (counterexample hunt) — NO

- Tried `B<0` to break `running_sup_eq_B` — that is exactly why `hB` is required; with `hB` it holds.
- Tried to defeat the squeeze near-miss by dropping each hyp — each drop yields a true
  counterexample (so the theorem is tight, not vacuous).
- The average genuinely → 0 (Tendsto, B/T); the spike is genuinely constant B (free of T). Nothing
  false found.

## 6. Verdict

**REAL.** Headline existence result (CRITIQUE §2b precise): faithful, non-vacuous, no
hypothesis-laundering, target objects absent, all hypotheses load-bearing, kernel-clean. The
mandatory near-miss is a real, correctly-scoped theorem; its INABILITY to certify the §3
running-sup vulnerability's cause (the spec asked for a statement that is false for the matching
notion) is a genuine faithfulness GAP — but one the executor identified, proved as a negative, and
disclosed. Not a shadow, not vacuous, not broken. The single honest shortfall is that "(ii)
certifies the cause of (i)" is over-stated by the spec and only partially delivered; the executor's
own honesty about this is what keeps the artifact on the REAL side rather than SHADOW.

### Attack file axiom report (kernel-checked)
All six attack theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
(see `averaging-hides-spikes-attack.lean`; final compile exit 0).
