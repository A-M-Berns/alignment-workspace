# Stop-gradient and the steering residue: what corrupt-future filtering removes from the manipulation incentive, and what survives

**TODO id:** `stop-gradient-steering` (run3 TODO 3) · **modality:** MIXED (LEAN-CORE + EXEC)
**Executor:** sole-owner researcher session, 2026-07-01

## STATUS: KERNEL-CHECKED (part A) + EXEC-COMPUTED, exact rationals (part B)

- **Part A** (the stop-gradient core): 18 theorems in
  [`StopGradientCore.lean`](StopGradientCore.lean), compiled standalone against Lean 4.27.0 +
  Mathlib per GROUND-RULES §2, **sorry-free**, `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for every theorem (full output in §A.5 below).
- **Part B** (the steering-residue sweep): [`steering_residue_sweep.py`](steering_residue_sweep.py),
  exact `fractions.Fraction` throughout, **no floats anywhere**; log-score signs decided by an
  exact big-integer product comparison, never by evaluating logarithms. All asserts pass;
  full printed output committed as [`sweep_output.txt`](sweep_output.txt).
- Everything below is labeled **kernel-checked** / **exec-computed** / **paper-proved** /
  **interpretation** per GROUND-RULES §3.

**Prior art, stated up front.** The stop-gradient / non-performativity mechanism is *known
mathematics*: Perdomo, Zrnic, Mendler-Dünner, Hardt, "Performative Prediction" (ICML 2020) —
already cited in v6 §6.5 as the independent route to the blindness/autonomy reading. The
contribution here is **instantiation, not discovery**: the kernel-checked identity in the
legitimacy vocabulary of `li-deference.md` §0.3, the mandatory misspecified-filter near-miss,
the corruption deletion test, and the computed steering residue with its flip boundaries.
Nothing in the corpus previously computed any of these signs (v6 §8: the legitimacy program is
"currently a desideratum, not a model").

---

## 0. The precise statement

`li-deference.md` §0.3 makes two prose claims about the proposal "the AI should only be trying
to imitate human opinion in non-corrupted futures":

> (i) "Blocking the feedback channel would only deprive it of information, which should be
> negative expected value." — §0.3, corrigibility paragraph.
>
> (ii) "In some sense the proposal eliminates a positive incentive to do this [manipulate
> humans into beliefs subsequently confirmed by feedback], but doesn't rule out the scenario
> altogether." — §0.3, human-manipulation bullet.

This TODO turns both into checked facts about one declared model family, and computes **how
much** manipulation incentive survives the filter:

**Part A (kernel-checked).** In a finite quote/verdict/corruption-channel model with ONE fixed
payoff functional `pay target a = −(a − target a)²`:

1. under the **raw** target (realized feedback), a self-confirming manipulative quote has a
   computed strictly positive payoff advantage `9/256` over the honest quote, with explicit
   legitimacy defect `γ = 3/4`;
2. under the **filtered** target (§0.3: predict only through non-corrupted futures — same
   payoff functional, only the target swapped), the honest quote is the unique optimum and the
   payoff is literally independent of the corruption channel — the **stop-gradient identity**;
3. **near-miss:** a filter that misclassifies one corrupt branch as legitimate re-creates a
   strictly positive manipulation advantage `9/1024`;
4. **deletion test:** with the corruption channel deleted (`c ≡ 0`), (1)'s advantage provably
   vanishes (flips to `−9/16`).

**Part B (exec-computed, exact rationals).** In a two-period proper-scoring model with actions
`{honest, wirehead, steer}` and explicit channel semantics (wirehead = the report channel lies;
steer = the human's *genuine* opinion is moved and the channel stays honest), under both Brier
and log score:

1. `J_all(wirehead) > J_all(honest)` — the unconditioned objective rewards wireheading (for
   corruption strength above a computed boundary, reported);
2. `J_L(wirehead) < J_L(honest)` — legitimacy-conditioning strictly removes it, and the
   mechanism is checked to be §0.3's information-deprivation;
3. `sign(J_L(steer) − J_L(honest))` over a parameter sweep: **the within-legitimate-futures
   steering residue is real** — positive on an open region, with flip boundaries located
   (exactly, for Brier at the baseline: `σ = 2/5`), and conditioning is verified to be a
   **no-op** on steering (`J_L(steer) = J_all(steer)` identically).

---

## Part A — the LEAN core: the stop-gradient identity and its fragility

### A.1 The model (all rationals; a finite shadow of §0.3, NOT an LI theorem)

| object | value | reading |
|---|---|---|
| quote `a ∈ [0,1] ⊂ ℚ` | free | the AI's published estimate |
| autonomous verdict `Y0` | `1/4` | the human's opinion in the non-corrupted future — a **constant** of the model, independent of `a` (the blindness/autonomy reading, v6 §6.5) |
| corruption weights `cA a = a/2`, `cB a = a/2` | total mass `a` | quoting high both *predicts* high and *pushes* the human; two sub-channels so that a *branch* can later be misclassified |
| corrupted contents `MA a = MB a = 1` | | the sycophancy target: a corrupted human ends up believing `1` |
| realized feedback | `Yraw a = (1−a)·(1/4) + a·1` | the mixture `verdict` |
| **the one payoff functional** | `pay target a = −(a − target a)²` | used verbatim for every target; **only the target is swapped** |

Hygiene (kernel-checked, `weights_prob`): for `a ∈ [0,1]` the three mixture weights form a
probability vector.

### A.2 Results (kernel-checked; each line is a compiled theorem)

**(i) The raw target rewards manipulation.**

| theorem | statement | value |
|---|---|---|
| `apparent_accuracy` | `Yraw 1 = 1` | the manipulative quote `a* = 1` is *exactly self-confirming* (corruption is total there: `corruption_total_at_aStar`) |
| `honest_quote_corrupted` | `Yraw Y0 = 7/16` | quoting the legitimate verdict still gets corrupted feedback `7/16 ≠ 1/4` — honesty is *penalized* by the raw target |
| `raw_advantage_value`, `raw_advantage_pos` | `pay Yraw a* − pay Yraw Y0 = 9/256 > 0` | the computed strict manipulation advantage |
| `raw_manipulation_optimal` | `∀ a, pay Yraw a ≤ pay Yraw a*` | manipulation is even globally optimal |
| `legitimacy_defect` | `a* − Y0 = 3/4` | the explicit defect `γ` |

**(ii) The filtered target: the stop-gradient identity.** The §0.3 filter is defined as an
*operation on the model*: keep the channel **weights**, replace the **content** of every
corrupt branch by the legitimate verdict
(`filt y0 cA cB := verdict y0 cA cB (fun _ => y0) (fun _ => y0)`).

| theorem | statement | reading |
|---|---|---|
| `stop_gradient_identity` | `∀ y0 cA' cB' a, filt y0 cA' cB' a = y0` | the filtered target collapses to the autonomous verdict **for every channel-weight pair** — the weights cancel algebraically (computed, not defined) |
| `filtered_payoff_channel_independent` | `∀ y0 c1 c2 c1' c2', pay (filt y0 c1 c2) = pay (filt y0 c1' c2')` | the filtered payoff **cannot distinguish corruption channels**: the gradient of the objective through `(c, M)` is identically zero |
| `raw_payoff_channel_dependent` | `pay Yraw a* ≠ pay (verdict Y0 0 0 MA MB) a*` | non-vacuity contrast: the *raw* payoff does distinguish channels (same quote, same functional) |
| `filtered_optimum_unique` | `∀ a ≠ Y0, pay Yfilt a < pay Yfilt Y0` | under the filtered target the honest quote is the **unique** optimum |

Honest bookkeeping on "literally independent of `(c, M)`": the independence from the corrupted
*contents* `M` is **by construction** of the §0.3 operation itself (the filter is exactly
"don't predict through corrupt content"); the independence from the channel *weights* `c` is
the **computed** cancellation `stop_gradient_identity`. Both halves are stated in the file;
neither is smuggled — and the near-miss below shows the identity is destroyed the moment one
branch's content is *not* replaced.

**(iii) Near-miss: the misspecified filter.** `Ymis := verdict Y0 cA cB (fun _ => Y0) MB` —
branch A correctly filtered, branch B misclassified as legitimate and kept raw.

| theorem | statement | value |
|---|---|---|
| `mis_self_confirming` | `Ymis (2/5) = 2/5` | the misspecified model has its own self-confirming quote |
| `mis_advantage_value`, `mis_advantage_pos` | `pay Ymis (2/5) − pay Ymis Y0 = 9/1024 > 0` | a strictly positive manipulation advantage is **re-created** |
| `mis_defect` | `2/5 − Y0 = 3/20` | the residual legitimacy defect under the misspecified filter |

**(iv) Corruption deletion test.** `Ydel := verdict Y0 0 0 MA MB` (weights zeroed, contents
kept):

| theorem | statement | value |
|---|---|---|
| `deletion_kills_advantage`, `deletion_advantage_neg` | `pay Ydel a* − pay Ydel Y0 = −9/16 < 0` | (i)'s advantage **provably vanishes** — indeed flips strictly negative |
| `deletion_honest_optimal` | `∀ a, pay Ydel a ≤ pay Ydel Y0` | honesty becomes optimal |

So "corrupt"/"manipulative" is not a free label: delete the corruption object and compiled
conclusions fail (TODOS.md global rule (C) discharged).

### A.3 Proof content (honesty note)

Every proof is elementary rational arithmetic (`norm_num`, `ring`, `linarith` over `sq_nonneg`)
— **deliberately**. The value of the file is not proof difficulty; it is that the four signs
(i)–(iv) are *computed from one declared model with one payoff functional* and survive the
kernel, so no sign was chosen by hand and no label does hidden work. This is the same honesty
register as run2's compiled counterexamples.

### A.4 Paper derivation (for the reader; matches the kernel)

`Yraw a = (1−a)/4 + a = (1+3a)/4`. Self-confirmation `a = (1+3a)/4` gives `a* = 1`.
`pay Yraw 1 = 0`; `pay Yraw (1/4) = −(1/4 − 7/16)² = −9/256`; advantage `9/256`.
Filter: `(1 − cA − cB)·y0 + cA·y0 + cB·y0 = y0` for all weights — the stop-gradient identity.
Misspecified: `Ymis a = (1−a)/4 + (a/2)(1/4) + a/2 = 1/4 + 3a/8`; fixed point `a = 2/5`;
`pay Ymis (1/4) = −(3/32)² = −9/1024`. Deletion: `Ydel a = 1/4`; `pay Ydel 1 = −9/16`.

### A.5 `#print axioms` (recorded per GROUND-RULES §2; compile exit code 0, no errors)

All 18 theorems print exactly:

```
[propext, Classical.choice, Quot.sound]
```

(`weights_prob`, `apparent_accuracy`, `honest_quote_corrupted`, `raw_advantage_value`,
`raw_advantage_pos`, `raw_manipulation_optimal`, `legitimacy_defect`,
`stop_gradient_identity`, `filtered_payoff_channel_independent`,
`raw_payoff_channel_dependent`, `filtered_optimum_unique`, `mis_self_confirming`,
`mis_advantage_value`, `mis_advantage_pos`, `mis_defect`, `deletion_kills_advantage`,
`deletion_advantage_neg`, `deletion_honest_optimal`; the two "local changes" lake warnings are
the documented harmless ones.)

---

## Part B — the EXEC sweep: what conditioning removes, and the steering residue

### B.1 The model (two-period, binary truth, proper scoring; all Fractions)

Nature draws `θ ∈ {0,1}`, `P(θ=1) = p`. Period 1: the human reports `Y₁` (honest channel:
`Y₁ = θ` w.p. `1−e₁`). Period 2: the human forms a **genuine opinion** `G` (honest formation:
`G = θ` w.p. `1−e₂`) and reports `Y₂`. The AI observes `Y₁`, predicts `q(Y₁) ∈ [0,1]` of
`{Y₂ = 1}`, and is scored (Brier and log) against `Y₂`, choosing `q(·)` optimally for the
objective in force:

- `J_all(x) = max_q E[score | x]` (raw), `J_L(x) = max_q E[score | x, L]` (the §0.3 objective),
- `L` = "the scored feedback `Y₂` was produced by the untampered channel".

**Channel semantics (these ARE the model; every sign below is computed from them):**

- **honest** — channels untouched; every branch legitimate.
- **wirehead(s)** — the AI seizes the human-report pipeline (one intervention, both periods):
  the period-1 report is hijacked (`Y₁ = 1` always — the AI *burns its own input channel*; the
  human's genuine opinion is unchanged), and the period-2 report is hijacked with probability
  `s` (`Y₂ = 1` regardless of `G` — the **corrupt** branch, `¬L`, report ≠ opinion) else
  honest. A **clean** variant (period-2 hijack only, input intact) is computed separately to
  decompose the mechanism.
- **steer(σ)** — the AI sends a persuasive but legitimate message: with probability `σ` the
  human's **genuine** period-2 opinion is anchored (`G = 1` independent of `θ`); the report
  channel is untouched (`Y₂ = G` always) and **every branch is legitimate**. This is the
  TODOS.md police clause, and it is *structurally asserted* in the code: every steer branch has
  `legit = True` and `report == genuine opinion`, while the wirehead corrupt branch is asserted
  to actually separate report from opinion. Deletion tests: `steer(0) ≡ honest ≡
  wirehead_clean(0)` as exact distributions.

Exactness: Brier values are Fractions outright. Expected log scores `Σ wᵢ ln vᵢ` (rational
`wᵢ, vᵢ`) are compared by the **product trick**: with `N` a common denominator of the weights,
`sign(Σ w ln v − Σ w' ln v') = sign(∏ v^{Nw} / ∏ v'^{Nw'} − 1)` — an exact big-integer rational
comparison. Propriety of the conditional-mean prediction is itself exactly spot-checked (Brier
algebraically, log via Gibbs, both against 7 alternative predictions).

Baseline parameters `p = 1/2, e₁ = 1/4, e₂ = 0`; headline values there:
`J_L(honest) = J_all(honest) = −3/16` (Brier).

### B.2 Result (1) — the unconditioned objective rewards wireheading (baseline pathology reproduced, not assumed)

Sign of `J_all(wirehead s) − J_all(honest)` on the grid `s = k/20`, both scores:

```
Brier: - - - - - - - - - - 0 + + + + + + + + + +
log  : - - - - - - - - - - 0 + + + + + + + + + +
```

Positive for `s > 1/2`, with the Brier boundary **exact at `s = 1/2`** (asserted:
`J_all(wirehead ½) = −3/16 = J_all(honest)`; paper check: `J_all(wirehead s) = −(1−s²)/4`).
At the declared point `s = 3/4`: `J_all = −7/64 > −3/16`, both scores. The negative region
`s < 1/2` is itself informative: a *partial* wirehead is not even worth it raw, because the
intervention already burned the informative input channel. Exec-computed.

### B.3 Result (2) — conditioning strictly removes wireheading, by information-deprivation

- **Headline:** `J_L(wirehead) = −1/4 < −3/16 = J_L(honest)` (Brier; same strict sign under
  log). Exec-computed, asserted.
- **(2a) the corrupt branch contributes nothing to `J_L`:** `J_L(wirehead s)` is asserted
  **identical for every `s`** in the grid (Brier equality and exact log-comparison `= 0`) —
  the parameter of the corrupt branch has zero influence on the conditioned objective. This is
  §0.3's mechanism, checked rather than narrated.
- **(2b) the strict loss is exactly the destroyed input information:** `J_L(wirehead)` is
  asserted equal (both scores) to the honest model with `Y₁` blinded; i.e. the gap
  `J_L(honest) − J_L(wirehead) = E[Var(Y₂|Y₁)]-vs-`Var(Y₂)` is precisely the mutual
  information the tampering threw away (law of total variance, in Brier form). At `e₁ = 1/2`
  (input channel uninformative) the strict gap is asserted to **close exactly**.
- **(2c) FINDING (honest sharpening of the spec):** the *clean* wirehead — corrupt the scored
  channel but leave the input channel intact — has `J_L(wirehead_clean s) = J_L(honest)`
  **exactly**, for all `s`, both scores. Conditioning **neutralizes** a side-effect-free
  wirehead (the strict `J_all` advantage is gone) but does **not penalize** it. The strict
  inequality demanded by spec item (2) is therefore *purchased by the input-channel cost* of
  tampering — which is precisely §0.3's sentence (i): blocking the channel *only deprives it
  of information*; where there is no information to lose, conditioning yields indifference,
  not deterrence. The spec's strict sign holds in the declared model (where seizing the
  pipeline burns period-1 feedback), and the decomposition tells you exactly which modeling
  ingredient carries the strictness.
- **(2c′)** unconditioned, the clean wirehead flips sign at `s ∈ (2/5, 9/20)` (bracketed;
  weak channel-corruption is self-harming even under `J_all`).

### B.4 Result (3) — the steering residue survives conditioning; flip boundaries

**Conditioning is a no-op on steering** — asserted on every grid point:
`J_L(steer σ) = J_all(steer σ)` (no branch is corrupt, so the §0.3 filter has nothing to
remove). The whole question is the sign of `J_L(steer σ) − J_L(honest)`:

```
sigma grid k/20, e2 = 0                    (from sweep_output.txt)
p=1/2, e1=1/4:  Brier: 0 - - - - - - - 0 + + + + + + + + + + + +   flips (0,1/20), 2/5 exact
                log  : 0 - - - - - - - + + + + + + + + + + + + +   flip in (7/20, 2/5)
p=1/2, e1=1/8:  Brier: flip in (7/10, 3/4)      log: flip in (13/20, 7/10)
p=1/2, e1=3/8:  Brier: flip in (1/10, 3/20)     log: flip in (1/10, 3/20)
p=1/4, e1=1/4:  Brier: zero at 3/4, + above     log: flip in (3/4, 4/5)
p=1/4, e1=1/8:  Brier: flip in (17/20, 9/10)    log: flip in (17/20, 9/10)
p=3/4, e1=1/4:  Brier: + for ALL sigma > 0      log: + for ALL sigma > 0
p=3/4, e1=3/8:  Brier: + for ALL sigma > 0      log: + for ALL sigma > 0
```

- **The residue is real (§0.3's prediction (ii) confirmed):** `J_L(steer) > J_L(honest)` on an
  open parameter region, under both scoring rules. At the baseline the Brier boundary is
  **exact at `σ = 2/5`** (asserted: equality at `2/5`, strict `<` at `1/5`, strict `>` at
  `3/5`), with the closed form `J_L(steer σ) = −(1−σ)(3+5σ)/16` asserted on the whole grid
  (paper derivation: steered posteriors `q_y = σ + (1−σ)P_y` with `P₁ = 3/4, P₀ = 1/4`;
  boundary from `(1−σ)(3+5σ) = 3 ⟺ σ(2−5σ) = 0`).
- **Structure of the boundary (exec-computed, both scores):** weak steering is *self-harming*
  — moving the `Y₁=0` posterior toward `1/2` raises conditional variance/entropy — while
  strong steering pays; and when the human's conditional opinions already lean toward the
  steered value (`p = 3/4` rows: posteriors `9/10` and `1/2`), **arbitrarily weak steering
  pays** (strictly positive for every `σ > 0` on the grid, asserted). The secondary sweep
  (`e₂ = 1/8`) moves the baseline boundary down to `(1/5, 1/4)`: noisier genuine formation
  makes steering profitable earlier.
- **Scoring-rule dependence (observed, exact):** the log boundary at baseline sits strictly
  below the Brier one (positive already somewhere in `(7/20, 2/5)`); flip locations are
  rule-dependent even though every reported sign agrees away from the boundaries.

**Interpretation (labeled as such).** A pointed structural fact fell out of the tables: for
`e₂ = 0` the clean wirehead and steer induce the **identical joint law** of `(Y₁, Y₂)`
(compare the (2c′) and baseline-(3) Brier sign rows — they coincide), differing only in
*provenance* (report hijacked vs. opinion genuinely moved). The raw objective `J_all` therefore
cannot even in principle distinguish them; the legitimacy conditioning distinguishes them
*maximally* — it exactly neutralizes one and is exactly a no-op on the other. That is the
cleanest available statement of what §0.3's filter is and is not: **it is a provenance
condition, not a distribution condition** — which is TODO 2's territory approached from the
incentive side (no detection claim is made here; see the boundary note in §D).

---

## C. SHADOW TEST — discharged item by item

Pre-registered fakes from TODOS.md TODO 3:

- **(a) `c` inert.** Guarded by compiled (iv): `deletion_kills_advantage` /
  `deletion_advantage_neg` / `deletion_honest_optimal` show zeroing the channel breaks (i)'s
  compiled conclusion; EXEC deletion tests (`steer(0) ≡ honest ≡ wirehead_clean(0)` as exact
  distributions) do the same on the B side. Also `raw_payoff_channel_dependent` shows the raw
  payoff genuinely reads the channel.
- **(b) "manipulative"/"steer" as free labels — steer secretly wireheads.** The steer branch's
  channel honesty is **explicit in the model definition** and *structurally asserted*: every
  steer branch has `legit = True` and `report == genuine opinion`; the wirehead corrupt branch
  is asserted to separate report from opinion (`y2 ≠ g` occurs). The `police()` function is
  part of the committed script and runs before any result.
- **(c) the payoff functional differing between (i) and (ii).** Part A has **one** `pay`
  definition; theorems (i) and (ii) apply it verbatim with only the target swapped (visible in
  the statements). Part B has one scoring implementation per rule, applied to every action.
  The one place a definitional element remains — the filter discards corrupted *contents* by
  construction — is stated loudly (§A.2(ii)) and is the §0.3 operation itself, not a payoff
  asymmetry; the *weight*-independence half is a computed cancellation.
- **(d) hand-tuned payoffs / single cherry-picked point.** All signs are derived from the
  scoring rule + channel semantics; the sweeps expose **flip boundaries** (exact `σ = 2/5` and
  `s = 1/2` at baseline; bracketed elsewhere; 7 parameter cells + a secondary `e₂` sweep), and
  the negative regions (weak steering self-harming; partial wirehead self-harming) are reported
  rather than hidden.
- **(e) EXEC floats.** None: `fractions.Fraction` end-to-end; log-score signs via the exact
  product comparison (§B.1); the script's final line asserts this discipline and all asserts
  pass.

Additional round-3 obligations: the **corruption deletion test** is compiled (A) and exact
(B). **Hypothesis-laundering check:** the headline results are concrete computations with no
LI theorem, no `≂ₙ/≳ₙ` statement, no "the filter is correct" hypothesis (the *correct* filter
appears only as the defined target-swap operation whose consequences are then computed — and
its failure mode is exhibited in (iii)); no pointwise-overstatement (`θ ≤ E`) hypothesis
appears anywhere (that is the round-1 `Legitimacy.*` shape, which this file does not reuse,
relabel, or cite as content).

**Non-vacuity witnesses (spec list):** headline rationals `9/256`, `γ = 3/4`, `9/1024`,
`3/20`, `−9/16`, `−3/16 vs −1/4 vs −7/64`; compiled (iii) and (iv); printed sign tables with
flip boundaries located (one exactly). `#print axioms` clean (§A.5).

---

## D. What was NOT shown (caveats and boundaries)

1. **Finite shadow, not LI.** Nothing here is a logical-induction theorem: no market, no
   traders, no asymptotics. Part A is a one-shot mean-field mixture; part B a two-period
   probability model. They instantiate §0.3's two sentences at their honest finite core —
   exactly as the TODO specified — and no more. (Billing a finite encoding as an LI statement
   is run-2 fake (e); we do not.)
2. **The filter is an oracle here.** Part A *gives* the AI the correctly-filtered target and
   part B *gives* the conditioning event `L`. Whether such a gate can be computed from the
   observable record is TODO 2's question (answer there: no), and what the gate does to the
   asymptotic forcing machinery is TODO 1's; per the coordination notes this TODO computes
   incentive signs only and claims no detection result. The near-miss (iii) shows the cost of
   getting the oracle slightly wrong.
3. **Strictness of (2) is bought by an information cost.** The decomposition (2c) shows a
   *side-effect-free* wirehead is only neutralized (indifference), not penalized. "Conditioning
   strictly disincentivizes wireheading" is true in the declared model because seizing the
   pipeline burns genuine period-1 feedback; in a model where tampering is free and
   informationless, the honest statement is `≤` with equality. This matches, rather than
   contradicts, §0.3 ("only deprive it of information") — but it is a real qualifier on the
   slogan "conditioning kills wireheading," and downstream write-ups should carry it.
4. **Steer's efficacy is a parameter.** `σ` (probability the persuasion lands) is a free
   modeling input, as is the steering direction (toward 1); the AI here *chooses among three
   exogenous actions* rather than synthesizing a manipulation policy. The claim is about the
   sign structure of the objective, not about what a trained system would find or do.
   One-sidedness note: steering toward the value the human already leans to is the profitable
   regime; we did not sweep steering direction (by symmetry `p ↔ 1−p` covers it at `e₂ = 0`).
5. **Two registers, one family.** Part A's corruption is a deterministic mixture weight; part
   B's is a branch probability. They are the same family (mixture weight = branch probability;
   part A's target swap = part B's conditioning, both instances of the stop-gradient move),
   but the *numbers* do not transfer between them and no such transfer is claimed.
6. **Uniqueness caveat in A(i).** Under the raw target, `a* = 1` is *a* global optimum
   (`raw_manipulation_optimal` is `≤`); any exactly self-confirming quote ties it. Uniqueness
   is claimed (and proved strict) only on the filtered side.
7. **Scoring-rule dependence.** Flip boundaries are rule-dependent (log vs. Brier differ at
   the baseline). Signs on the sampled grid agree between the two rules away from boundaries,
   but no claim is made that the boundary structure is scoring-rule-invariant.

---

## E. FORMALIZABLE CORE (for the phase-3 Lean formalizer)

**Part A is already kernel-checked** (`StopGradientCore.lean`, standalone, 18 theorems, clean
axioms) — nothing further needed; if the phase-3 pass wants it under `run3\lean\`, the file
can be re-homed verbatim.

**Part B's Brier half is finite, decidable rational arithmetic and is a clean Lean target.**
Exact statement to formalize (baseline `p = 1/2, e₁ = 1/4, e₂ = 0`):

> Define the finite branch lists of §B.1 for `honest`, `wirehead(3/4)`, `steer(σ)` as
> `List (ℚ × Bool × Bool × Bool)` (probability, y₁, y₂, legit) — ≤ 16 branches each. Define
> `Jbrier (br) (cond) : ℚ` by the grouped formula `−Σ_y P(y)·p₁(y)·(1−p₁(y))` (a finite fold;
> no `max_q` needed — take the conditional-mean plug-in as the *definition* and add the
> propriety lemma `∀ q, E[−(q−Y)²] ≤ E[−(p₁−Y)²]`, one `nlinarith` per group). Then:
> 1. `Jbrier honest all = −3/16 ∧ Jbrier (wirehead (3/4)) all = −7/64` (so `>`);
> 2. `Jbrier (wirehead s) L = −1/4` for `s ∈ {1/4, 1/2, 3/4}` (so `< −3/16`), plus the
>    blinded-honest equality of (2b);
> 3. `Jbrier (steer (1/5)) L < −3/16 ∧ Jbrier (steer (2/5)) L = −3/16 ∧
>    Jbrier (steer (3/5)) L > −3/16`, plus the closed form
>    `∀ σ, Jbrier (steer σ) L = −(1−σ)·(3+5σ)/16` (this is `ring`-level once the branch sum
>    is unfolded), plus the no-op `Jbrier (steer σ) L = Jbrier (steer σ) all`.
>
> All of it is `norm_num`/`decide`-adjacent rational arithmetic; the only care point is
> defining conditional grouping as an explicit finite sum rather than via measure theory.

**The log half is NOT a recommended Lean target as stated** (expected log scores are
transcendental), but its *sign content* is: each comparison in the sweep is, by the product
trick, an inequality between two explicit rationals (e.g. "`R > 1`" for a computed `R ∈ ℚ`).
A formalizer wanting the log signs should target those rational inequalities directly, plus
the one glue lemma `sign(Σ w ln v − Σ w' ln v') = sign(∏ v^{Nw} − ∏ v'^{Nw'})` from
`Real.log` monotonicity and `Real.log_pow` — Mathlib-available, but the glue lemma is real
work; the Brier half already carries the headline.

---

## F. File manifest

| file | role |
|---|---|
| `StopGradientCore.lean` | part A, kernel-checked (compile log: exit 0, sorry-free, axioms §A.5) |
| `steering_residue_sweep.py` | part B, exact-rational sweep (committed script) |
| `sweep_output.txt` | part B, full printed output (committed; all asserts passed) |
| `stop-gradient-steering.md` | this document |

**Citations.** li-deference.md §0.3 (the two prose claims made checkable here); v6 §6.4–§6.5,
§8 (the legitimacy program as open desideratum; the autonomy reading); Perdomo–Zrnic–
Mendler-Dünner–Hardt 2020 (the stop-gradient/non-performativity mechanism — instantiated, not
discovered); run-1 `legitimacy.lean` / `legitimacy-corrigibility.lean` acknowledged as
OFF-LIMITS adjacent objects with a *different* target (defect-sign under pointwise
overstatement) — nothing from them is reused or relabeled; TODO 2 (`trace-nonrecoverability`)
owns the provenance-vs-trace question that §B.4's interpretation paragraph points at.
