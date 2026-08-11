# Lean Audit: What the `lean-deference` Proofs Actually Verify

*A statement-level adversarial audit of the five Lean modules backing the deference
research notes (`deference-in-logical-induction-v5.md`, `faithful-acceleration.md`, and the
`anson-notes/` sources). Written 2026-06-26 by Claude (Opus 4.8), at Abram Demski's request,
after reading all five modules in full. Read-only: no Lean or notes were modified for it.*

Scope: `LeanDeference.lean` (705 lines, 47 decls), `SelfReferentialTarget.lean` (320, 22),
`FrozenDeliberation.lean` (352, 30), `FaithfulAcceleration.lean` (229, 16),
`TowerAndAcceleration.lean` (195, 14). All are `sorry`-free and audit to
`[propext, Classical.choice, Quot.sound]`.

---

## 0. Why this audit exists, and what it is looking for

"Kernel-checked, `sorry`-free, standard axioms" is easy to over-read. It is a real guarantee,
but a narrow one, and the gap between what it guarantees and what the prose claims is exactly
where a formalization can go wrong **without the kernel ever complaining**. The specific
failure mode this audit hunts for is:

> a theorem **engineered to typecheck** — true as stated — that nonetheless tests something
> *weaker than, or beside,* the mathematical claim it is named for.

This is not hypothetical. It is the default risk of the "named-hypothesis discipline" these
modules adopt (formalize the arithmetic, take the Logical-Induction theorems and the market as
named hypotheses). That discipline is legitimate and standard. But it shades, at its edges,
into *assuming what you meant to prove*, and the only way to know which side of that line a
given theorem falls on is to read the statement adversarially. That is what follows.

### 0.1 What `#print axioms` does and does not certify

`#print axioms T = [propext, Classical.choice, Quot.sound]` certifies exactly one thing: the
term inhabiting `T`'s type contains no `sorryAx` and no exotic axiom — i.e. **the proof is a
genuine proof of the proposition `T` as written**. It certifies nothing about whether `T` *as
written* is the proposition you care about. In particular it cannot see:

- whether `T`'s hypotheses are true, applicable, or jointly satisfiable (a vacuous `T` passes);
- whether `T`'s hypotheses already contain its conclusion;
- whether `T`'s definitions mean what the prose word means;
- whether `T`'s conclusion, in Lean terms, renders the informal claim.

So the **trust surface** of this corpus is *not* the proof bodies (the kernel has those
covered). It is three much smaller things, which a human must read: the **definitions**, the
**hypotheses** of each top-level theorem, and the **conclusion statements**. This document is
an audit of that surface.

### 0.2 Two classifications used throughout

**Hypothesis provenance** — for each hypothesis of each theorem:

- **(a) derived** — proved elsewhere in the development, or no hypothesis at all.
- **(b) LI citation** — a Logical-Induction paper theorem taken as-stated (`loe`, `expprovind`,
  `ccee`, `cee`, per-member convergence, Non-Dogmatism, the no-Dutch-book criterion *as a
  property of an inductor*). **This is the accepted kind of gap.**
- **(c) modeling substitution** — *not* a clean citation, but an identification that quietly
  puts a weaker or different object in place of the intended one. The paradigm case: "the
  criterion, applied to *this particular (unmodeled) trader*, yields *this inequality*." The
  criterion is (b); its application to an unmodeled trader to manufacture a named inequality is
  (c). Other (c)'s: complexity-class content rendered as abstract monotone sequences; an
  "on-`G`" bound assembled in prose and handed in as one hypothesis; a hand-evaluated integral.

**Proof-content kind** — for each theorem, what its body actually does:

| Kind | Meaning |
|---|---|
| **Proved** | Genuine non-trivial math, proved outright (or composed from genuinely-proved pieces). A real check. |
| **Composition** | Genuinely *chains* several named LI facts into the conclusion via real multi-step work. The work is real; the inputs are named. |
| **Squeeze** | The conclusion follows from named hypotheses by a one-step squeeze / triangle inequality, where the hypotheses are *logically equivalent to, or are,* the conclusion. Weak check. |
| **Stub** | Arithmetically trivial (`a ≤ a+b`, `0·ε = 0`, modus tollens), standing in for an unmodeled argument. |
| **Non-vacuity** | An existence/counterexample lemma guarding against vacuity. `+` = genuine/non-degenerate; `−` = degenerate (e.g. constant sequences). |
| **Propositional** | Pure propositional logic over abstract `Prop`s; no mathematical content. |

---

## 1. The central finding

The corpus divides on one fault line, and the division is the whole story.

> **The Lean proves the *implications* of the deference theory. It does not prove the
> *antecedents*.**

Concretely, what is genuinely established is the **conditional skeleton**:

- `tower ⟹ Value` (and the argmax/menu form), asymptotically and finite-exactly;
- `Value ⟺ Total Trust`, from linearity alone, both arrows, finite-exactly and asymptotically;
- the finite-frame algebra (the keystone `decomposition`, the softmax bound, the immodesty
  collapse, the two-option `witness_identity`);
- the obstruction arithmetic (`no_exact_quote`'s ½-gap, `cost_circularity`'s regress);
- the asymptotic calculus that glues all of it (`≈ₙ`/`≳ₙ` as real-sequence limits).

What is **not** established — what enters as named hypotheses, and for the forcing results as
named hypotheses *that are essentially the conclusion restated* — is the **antecedent**: that
the no-Dutch-book criterion **forces** the tower / the tracking / the calibration. That step
requires modeling the market and traders, which no module does. So:

> The corpus certifies **"the deference algebra composes correctly"**. It does **not** certify
> **"deference is forced."** The forcing — the entire novelty of the cross-process results — is
> the part that lives outside the kernel's reach, in type-(c) hypotheses.

This is not a defect of any one proof; it is a property of where the modeling boundary was
drawn. But it has a sharp consequence for how the "kernel-checked" label should be read,
especially for the §5 / `FrozenDeliberation` forcing suite, which is advertised as the
headline new result and is in fact **the least independently checked module in the corpus**.

---

## 2. The genuinely-proved tier (the real checks)

Credit first, because it is substantial and it is what the label legitimately covers.

### 2.1 `LeanDeference` — the finite-frame algebra and the converse

This is the strongest module. It contains real, non-trivial, outright-proved mathematics:

- **`decomposition`** — the keystone identity `gap_i = D_CM + D_UM_i + soft_i`, for *every*
  finite frame/menu/weight, pure linearity, no frame hypothesis. Everything in the finite Value
  story rests on this, and it is genuinely proved (`simp [mul_sub, sum_sub_distrib]; ring`).
- **`witness_identity`** — the two-option DDB Lemma 7.1 identity, the engine of the converse.
  Proved outright. From it, `value_iff_totalTrust` (finite-exact) follows by algebra alone.
- **`softmax_lower_bound`** — a genuine `exp`-analysis bound (temperature-`δ` softmax mean
  within `card·δ` of the max), using `Real.add_one_le_exp`. Notably this *removes* the softmax
  bound from the assumed facts — it used to be a hypothesis and is now a theorem.
- **`CM_implies_immodest`** — the §2.2 finite-collapse core (the conditional-martingale
  identity at `w` forces `P_w(fiber) = 1`), proved by instantiating at the fiber indicator.
- **`value_of_argmax`, `payoff_gap_le_l1`** — the tie-break-free argmax Value backbone and the
  L¹ softmax→argmax bound, both genuine finite algebra.
- **`value_asymptotic`, `value_argmax_asymptotic`, `value_iff_totalTrust_asymptotic` and the
  `…ConverseAsymp` family** — **Compositions**: these genuinely chain `loe`/`ccee`/`cee`/
  `expprovind` (named, type-(b)) into Value / Total Trust via real multi-step asymptotic work.
  `value_iff_totalTrust_asymptotic` deriving *both* arrows from linearity alone is a clean,
  honest result. `totalTrust_of_value_asymptotic`'s docstring even says "Neither hypothesis is
  the conclusion" — and that is correct.

**Relevance to `faithful-acceleration.md`:** that note's load-bearing citation,
`value_iff_totalTrust`, is genuinely proved here. One precision note: the note cites the
*finite-exact* name while its own setting is asymptotic; the exact citation is
`value_iff_totalTrust_asymptotic` (also proved). Both hold, so the conclusion stands; only the
pointer is loose.

### 2.2 `SelfReferentialTarget` — the obstruction cores

The negative results (2a/2b) are genuinely captured at the arithmetic/asymptotic level:

- **`no_exact_quote` / `residual_half` / `no_exact_quote'` / `residual_lb`** — the ½
  discontinuity gap (`|a − antiInd a| ≥ ½`, tight, rounding-robust). Pure real analysis, the
  real heart of 2a. Proved outright.
- **`tracking_fails_liminf` / `tracking_fails`** — **Composition**: `residual_lb` plus two named
  convergences (rounding; provability induction `hLIPI`, type-(b)) genuinely yield
  `liminf |a_n − Y_n| ≥ ½`, refuting timely tracking. Real triangle-inequality composition.
- **`regress` / `cost_circularity`** — the 2b cost regress, pure arithmetic. (Its load-bearing
  `hcost` is a flagged type-(c) soft joint; see §3.6.)
- **`resale_lb`** — the subtle one-sided-indicator resale algebra of externalized self-trust,
  proved outright.

### 2.3 `FrozenDeliberation` — the amplifier algebra and the calculus

- **The `≈ₙ`/`≳ₙ` calculus** (`approx_of_asympLE_both`, `approx_of_abs_le`, the `trans` lemmas)
  — genuine real-analysis utility, correct.
- **The amplifier** (`amp_*`) — the §1.6 obstruction to the soft⇒hard squeeze: `g(e)=(1+2c)e−c`
  passes both threshold-trust cuts (`amp_upper_cut_nonneg`, `amp_lower_cut_nonpos`) yet is not
  the identity, and boundedness at the extreme forces `c=0` (`amp_boundedness_forces_id`). The
  cut *sign algebra* is genuinely proved. (One caveat, §3.7: the integral itself is
  hand-evaluated.)

### 2.4 `FaithfulAcceleration` — the trader skeleton and the doubly-soft weight

- **`round_profit_ge` → `profit_partial_sum_ge` → `profit_diverges` → `violation_not_persistent`
  → `soft_total_trust`** — a genuine arithmetic/asymptotic chain: per-round profit bound,
  summation, "calibration + divergent weight ⇒ banked value diverges," "criterion ⇒ weight
  bounded." Real composition.
- **`softInd` / `dsWeight` + `dsWeight_continuous` + `dsWeight_pos_imp_fst/_snd`** — the
  doubly-soft weight is now *constructed*, its **joint continuity** proved (the legality-relevant
  property), and the support hypotheses `hone`/`hmis` *discharged from the construction* rather
  than assumed. This closed one specific type-(c) leak (see §3.2).

### 2.5 `TowerAndAcceleration` — the reduction and the two-faces witness

- **`tower_imp_tracking`** — the pure `≈ₙ` algebra reducing the timely pointwise tower to
  tracking via the three corner-quote collapses (taken as hypotheses).
- **`witness_partial_sum` / `witness_gap` / `witness_tracking_fails` / `two_faces_distinct`** —
  a genuine, non-degenerate witness (`a_n ≡ ½`, `Y_n` alternating) that is pointwise-wrong by ½
  yet aggregate-unbiased. Real content; the bias closed form is proved by induction. This
  formalizes the "per-day dead, averaged alive" distinction precisely.

### 2.6 Good non-vacuity guards (credit where due)

Several lemmas actively defend against the vacuity trap, and they are the sign of an author who
saw the risk:

- **`cost_setup_realizable`** — proves the *non-cost* hypotheses of `cost_circularity` are
  jointly realizable, *locating the contradiction squarely on the soft `hcost`*. This is a
  sophisticated guard: it rules out "the contradiction comes from an unsatisfiable structural
  setup."
- **`AntiExpert.{stationary, TT_negative, value_fails}`** — a genuine, non-degenerate DDB
  anti-expert frame, witnessing that the converse is non-vacuous *and* that marginal-martingale
  ≠ Value.
- **`tracking_fails_nonvacuous`, `TS_off_G_fails`, `fold_hypothesis_fails`** — concrete
  witnesses exhibiting real failure where the theory says failure should occur.

---

## 3. The concerning gaps (type (c), elaborated)

These are the findings the audit was commissioned to surface. None is hidden by `#print
axioms`; several are disclosed in docstrings or in v5 §7's "trusted boundary"; but the
disclosure is at the section level, while the **theorem names** invite the stronger reading.

### 3.1 The market and traders are entirely unmodeled

No module models a trader, a price as a tradable instrument, the budget mechanism, legality
(continuity / `𝒞`-expressibility), or cash accounting. Consequently **every** appeal to "the
no-Dutch-book criterion forbids the exploit" is either a named hypothesis (the inequality the
criterion is supposed to deliver) or a **trivial arithmetic stub** standing in for the actual
arbitrage argument:

- `DeferenceTrader.round_profit_ge_gap` — `en i − en jstar ≤ (en i − en jstar) + (ef jstar −
  ef i)` given the unwind `ef jstar − ef i ≥ 0`. This is `a ≤ a + b, b ≥ 0`.
- `Frozen.tracking_sell_profit` — `Y + ε ≤ a ⟹ ε ≤ a − Y`. One `linarith`.
- `SelfRefTarget.round_profit_pos` — `pbuy < psell ⟹ 0 < psell − pbuy`.

Each docstring is honest ("the exploit itself … is the trusted criterion, not formalized
here"). But the upshot is structural: **the inference "criterion ⇒ the forcing inequality" is
nowhere in the corpus.** It is the single largest type-(c) boundary, and it underlies §3.2–3.4.
Converting it to type-(b) would require modeling a minimal market — a real project, not a patch.

### 3.2 The doubly-soft weight: one leak closed, the class still open

Originally `soft_total_trust` took the trader weight `w` as an abstract sequence with only
`(hone : 0 < w i → t < a i)` and `(hmis : 0 < w i → p i < t − ε)`. Because *both* a legal
(continuous) weight and the buggy illegal hard-restriction-to-the-violation-set weight satisfy
those two hypotheses, the Lean **could not distinguish them**, and was literally *unaffected*
by the write-up's trader-legality fix. That is the cleanest possible illustration of a type-(c)
substitution: the object the theorem quantified over was strictly weaker than the intended
(legal) trader.

`soft_total_trust_doublysoft` now closes this *specific* leak: `dsWeight` is the actual gate,
`dsWeight_continuous` proves the joint continuity a hard indicator violates, and `hone`/`hmis`
are theorems about the construction. **But the class is not fully closed:** "continuous ⟹ legal
`𝒞_H`-expressible-feature trader" remains a modeling step, and `hbias` (calibration) and `hbdd`
(criterion) remain named. So the fix moved one object from (c) to (a); the market-legality and
the criterion-application around it are still (c)/(b).

### 3.3 The forcing headlines are squeezes over hypotheses equivalent to their conclusions

This is the sharpest "constructed to pass" pattern, and it sits on the most important theorems —
the §5 forcing suite, which is the cross-process novelty.

- **T1 · `Frozen.faithful_tracking`** : `(hUpper : a ≲ Y) → (hLower : Y ≲ a) → a ≈ Y`. But
  `a ≈ Y` *is, by definition,* the conjunction `a ≲ Y ∧ Y ≲ a` (that is `approx_of_asympLE_both`
  in one direction and `Approx.asympLE` in the other — an iff). So the theorem is the trivial
  direction of "≈ is two-sided ≲." The entire mathematical claim of T1 ("the `𝒞_A` criterion
  *forces* both inequalities") is in the two named hypotheses; the Lean adds nothing to it. It
  is a dressed-up tautology whose name reads as "faithfulness is forced."

- **T3 · `Frozen.conditional_tower`** : `(hcarry : ∀ n, |Elhs n − Erhs n| ≤ d n) → (hd : d → 0)
  → Elhs ≈ Erhs`. This is `approx_of_abs_le` verbatim. The substance — that `loe`+`expprovind`
  carry the provably-small integrand, *which is `hcarry`* — is the named hypothesis. T3 is the
  "conditional tower forced on `G`," the substantive `Mart` content; in Lean it is a one-line
  squeeze over an assumption that already says `|Elhs − Erhs| → 0`.

- **`Frozen.quote_is_truth_on_G`** (the soundness engine), **T6 `calibration_residual_on_G`**,
  **T7 `limit_agreement_on_G`**, **`TS_on_G`** — all the same shape: a triangle inequality or
  squeeze whose content is the named on-`G` bound (`hG`, `hbin`/`htruth`, per-member
  convergence). The mathematics ("on `G` the quote is early-revealed truth") is assembled in
  prose and handed in; the Lean checks `|x − z| ≤ |x − y| + |y − z|`.

The honest reading of the forcing suite: **`value_on_G` (T4) is a genuine Composition** (the
§1.1 four-liner really does chain the tower steps into Value) — but the tower steps it chains
*are themselves* T3, i.e. squeezes over named carries. So even the one real composition in the
suite bottoms out in named antecedents.

### 3.4 Theorems whose names oversell near-vacuous bodies

The clearest "engineered to typecheck" cases, where the name promises a deep result and the
body delivers a triviality:

- **`Frozen.underdetermination_off_G`** — the name (and docstring) promise the model-theoretic
  claim: *two valid inductors* satisfying (A1)–(A5) with the same `A`/target/ledger, agreeing on
  every `G`-quantity, non-exploitable, can differ by any `γ` off `G`. The **body proves**
  `∀ γ ∈ (0,1), ∃ pa pb ∈ (0,1), |pa − pb| = γ` — witnessed by `pa = (1+γ)/2, pb = (1−γ)/2`.
  That is "two points in an interval." It says nothing about inductors, validity, agreement, or
  exploitability. The entire content of T7-off-`G` is unmodeled; the theorem is a real-number
  triviality wearing its name.

- **`Frozen.worth_zero_if_never_settles`** — literally `((0:ℕ):ℝ) · ε = 0`. It "represents"
  the silence safety property (zero settled rounds ⇒ zero worth). The representation is `0·ε=0`.

- **`SelfRefTarget.manipulation_confined`** — `δ ≤ Yinf ≤ 1 − δ ⟹ 0 < Yinf < 1`. The
  conclusion is *strictly weaker* than the assumed interval, which *is* the (named) Non-Dogmatism
  margin. Nothing about manipulation or confinement is established; a weaker interval is read off
  a stronger assumed one.

- **`SelfRefTarget.nondogmatism_refutes`** — `Yinf < 1, Yinf = 1 ⟹ False`. Modus tollens on a
  named bound.

- **`Frozen.worth_unbounded_if_settles`** — `ε > 0 ⟹ ∀ M, ∃ k, M < k·ε`. This is genuinely
  proved (Archimedean), but its content is Archimedean unboundedness; the load-bearing claim
  ("the trader banks ≥ ε per settled round") is the unmodeled part.

### 3.5 The dichotomy is propositional plumbing, not instantiated

`SelfRefTarget.predictable_imp_uninfluenced` takes `{Blind Tracks SatPower QuoteRef : Prop}` as
**abstract propositions** and proves `(¬Blind → QuoteRef → ¬Tracks) → (¬Blind → ¬SatPower) →
(QuoteRef → Tracks → Blind) ∧ (SatPower → Blind)`. This is a propositional tautology. It is
**never connected** to the real `tracking_fails` (2a, about real sequences) or `cost_circularity`
(2b) — the types do not even match (opaque `Prop`s vs. real-sequence theorems). So the *composed*
dichotomy ("the real 2a and the real 2b together force blindness") is **not formed in Lean**;
only its logical silhouette is. The docstring says as much ("this is their logical structure"),
but the theorem name reads as the substantive dichotomy.

### 3.6 The complexity classes are not modeled

The §3.3 hinge — "blindness-with-power is satisfiable *exactly because* P ⊊ EXP" — is rendered
as a contrast between two statements about **abstract monotone cost sequences**:
`Frozen.blind_cost_realizable` (a separate `RH∘F` can be dominated by a strictly-increasing
`RA`) versus `SelfRefTarget.cost_circularity` (a self-composition `RA∘F` cannot dominate
itself). The *structural* contrast is real and correctly captured. But "P ⊊ EXP," "EXP
dominates the `2^{O(n)}` horizon cost," "doubly-exponential is unsatisfiable in EXP" — the
actual complexity content — is interpretation laid on top of `n ↦ n` and `n ↦ n+1`. The witness
in `blind_cost_realizable` is linear functions; it certifies satisfiability of the abstract
inequality, not the complexity-class claim.

### 3.7 The amplifier integral is hand-evaluated

`amp_upper_cut_value` asserts `((1+2c)(1−t²)/2 − c(1−t)) − t(1−t) = (1−t)/2·((1−t)+2ct)` — a
`ring` identity between the **hand-computed** antiderivative expression and its factored form.
The claim that the left expression *equals* `∫_t^1 g(e) de − t(1−t)` is **not** in Lean (no
`MeasureTheory.integral`). If the antiderivative were miscomputed, `amp_upper_cut_nonneg` would
still "pass" (it proves the sign of *whatever expression is written*). I re-derived it by hand —
`∫_t^1 ((1+2c)e − c) de = [(1+2c)e²/2 − ce]_t^1 = (1+2c)(1−t²)/2 − c(1−t)`, correct — so the
result is sound; but the kernel does not certify the integration step. v5 §7 discloses this.

### 3.8 Some non-vacuity guards are degenerate

Contrast the good guards of §2.6 with the weak ones:

- `DeferenceConverseAsymp.ccee_bridge_satisfiable` and `value_side_satisfiable` use **constant**
  sequences (`Exw ≡ ½`, etc.). With everything constant, `Approx` and `AsympLE` hold trivially.
  These rule out "the hypotheses are contradictory" but *not* "the theorem is trivial on every
  interesting instance" — the asymptotic content is never exercised by the witness.
- `tracking_fails_nonvacuous` uses the constant best-response `a_n ≡ ½` — semi-degenerate, but
  it does exhibit a genuine constant-½ tracking failure, so it is meaningfully stronger than the
  above.

---

## 4. Definitions and conclusion-statements

The two parts of the trust surface that are *not* the concerning gaps:

**Definitions — clean.** `Approx a b := Tendsto (fun n => a n − b n) atTop (𝓝 0)` and
`AsympLE a b := ∀ ε>0, ∀ᶠ n, a n ≤ b n + ε` correctly encode `≈ₙ` and `≳ₙ`. `antiInd`
(`if a ≤ ½ then 1 else 0`), `amp` (`(1+2c)e − c`), `softInd` (the clamp ramp), `dsWeight` (the
product gate) all match their prose definitions. **No degenerate or mismatched definitions
found.** This matters: a wrong definition would silently invalidate everything above it, and
none does.

**Conclusion-statements — sometimes weaker than the prose headline.** The cases are exactly
§3.3 and §3.4: where the Lean conclusion is `a ≈ Y` (T1), `Elhs ≈ Erhs` (T3), or
`∃ pa pb ∈ (0,1)` (underdetermination), the rendered conclusion does not carry the forcing /
model-theoretic content the name claims. Elsewhere conclusions are faithful.

---

## 5. Severity-ranked findings

| # | Finding | Severity | Disclosed? |
|---|---|---|---|
| 1 | Market/traders unmodeled; "criterion ⇒ forcing inequality" never in Lean (§3.1) | **High** (structural) | Partly (docstrings, v5 §7) |
| 2 | Forcing headlines T1/T3 are squeezes over hypotheses equivalent to conclusions (§3.3) | **High** | No (names oversell) |
| 3 | `underdetermination_off_G` proves a real-number triviality vs. its model-theoretic name (§3.4) | **High** | Docstring describes intent only |
| 4 | Dichotomy is propositional, never instantiated from real 2a/2b (§3.5) | Medium | Docstring |
| 5 | Several trivial stubs named for substantive results (`worth_zero…`, `manipulation_confined`, trader stubs) (§3.1, §3.4) | Medium | Partly |
| 6 | Complexity content rendered as abstract cost sequences (§3.6) | Medium | Docstring |
| 7 | "continuous ⟹ legal trader" still named even after the `dsWeight` fix (§3.2) | Medium | This audit + note §9 |
| 8 | Amplifier integral hand-evaluated, not via Mathlib `∫` (§3.7) | Low (verified correct) | v5 §7 |
| 9 | Degenerate (constant-sequence) non-vacuity witnesses (§3.8) | Low | No |

---

## 6. Recommendations, in value order

1. **Re-label the notes' "Lean (§N)" blocks** to mark each cited theorem as *Proved* /
   *Composition* / *Squeeze-over-named* / *Stub*, so a reader cannot mistake `faithful_tracking`,
   `conditional_tower`, or `underdetermination_off_G` for "the forcing is verified." Lowest-risk,
   highest-honesty-per-effort. (No Lean changes.)
2. **Strengthen or rename the §3.4 near-vacuous theorems.** `underdetermination_off_G` in
   particular should either model "two valid inductors agreeing on `G`" (hard) or drop the name
   for something like `exists_two_interior_points_at_distance` (honest).
3. **Instantiate `predictable_imp_uninfluenced`** with the real `tracking_fails` and
   `cost_circularity` so the dichotomy is genuinely composed rather than merely shaped. Requires
   reconciling the abstract-`Prop` interface with the real-sequence theorems.
4. **Discharge the amplifier integral** via `MeasureTheory.integral` to remove the one
   hand-computation (§3.7). Self-contained, finite effort.
5. **The structural fix (large):** model a minimal market/trader — even a single abstract
   "legal strategy" type with a continuity field and a no-persistent-profit axiom — so that
   "criterion ⇒ the forcing inequality" becomes a *theorem* (type-(b)) rather than a named
   hypothesis or a stub (type-(c)). This is the only route that converts the §3.1 / §3.3 gaps,
   and it is the difference between "the algebra composes" and "deference is forced." It is a
   project in its own right, and it is where the real assurance would come from.

---

## 7. How to read "kernel-checked" for this corpus, going forward

A calibrated one-sentence status:

> These modules verify that **the deference theory's arithmetic and asymptotics compose without
> error, given the Logical-Induction literature and a set of modeling identifications** — and,
> for the cross-process *forcing* results specifically, the substantive claim (that the criterion
> forces the tower) is among those identifications, not among the proved content.

That is a genuine and non-trivial guarantee — informal proofs routinely get the composition,
the limits, the quantifiers, and the signs wrong, and the kernel has in fact caught such slips
in this very development. But it is *not* "the informal theorems are verified true end-to-end,"
and for the forcing suite the distance between the two is largest. The phrase to retire is
"the full §5 forcing suite is kernel-checked" without the qualifier "modulo the named criterion
applications, which are the forcing itself."

---

## Appendix A. Per-theorem ledger

Kind codes: **P** proved · **C** composition · **S** squeeze · **T** trivial stub ·
**N±** non-vacuity (genuine/degenerate) · **L** propositional. Hypothesis codes: (a) derived ·
(b) LI citation · (c) modeling substitution.

### `LeanDeference.lean`

| Theorem | Kind | Notes / hyp provenance |
|---|---|---|
| `decomposition` | P | pure linearity identity; no hyps |
| `value_of_defects`, `soft_nonneg`, `value_of_CM` | P | finite tower⇒Value; `hCM`/`hUM` exact-frame conditions |
| `Approx.*`, `AsympLE.*`, `approx_sum`, `approx_of_abs_le` | P | the `≈ₙ`/`≳ₙ` calculus |
| `value_asymptotic` | C | chains loe/ccee/cee/expprovind (b) into Value |
| `softmax_lower_bound` | P | genuine exp-analysis; ex-hypothesis now proved |
| `CM_implies_immodest` | P | easy half; hard spectral-gap half is prose (disclosed) |
| `value_of_argmax`, `payoff_gap_le_l1`, `value_argmax_via_softmax` | P | finite argmax backbone, L¹ bound |
| `value_argmax_asymptotic` | C | 3-step chain; tower steps (b) |
| `witness_identity` | P | DDB Lemma 7.1 identity, the converse engine |
| `value_witness_iff_totalTrust`, `totalTrust_sum_split`, `..._mass`, `totalTrust_of_value`, `value_iff_totalTrust` | P | finite Value⟺TT, all from `witness_identity` |
| `AntiExpert.{E0_lt,E1_ge,stationary,TT_negative,value_fails}` | N+ | genuine non-degenerate counter-frame |
| `fold_pointwise`, `fold_sum` | P | the cee/ccee fold |
| `fold_hypothesis_fails` | N+ | fold genuinely needs expert-knowledge |
| `totalTrust_asymptotic`, `totalTrust_of_value_asymptotic`, `value_of_totalTrust_asymptotic`, `value_iff_totalTrust_asymptotic` | C | asymptotic Value⟺TT from linearity (b); both arrows |
| `ccee_bridge_satisfiable`, `value_side_satisfiable` | N− | constant-sequence witnesses (weak) |
| `round_profit_ge_gap`, `gap_pos_imp_profit_pos` | T | `a ≤ a+b`; trader unmodeled (§3.1) |

### `SelfReferentialTarget.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `Approx`/`AsympLE`/`AsympLE.trans` | P | calculus |
| `no_exact_quote`, `residual_half`, `no_exact_quote'`, `residual_lb` | P | the ½ obstruction core, rounding-robust |
| `tracking_fails_liminf`, `tracking_fails` | C | `residual_lb` + rounding(c) + `hLIPI`(b) |
| `tracking_fails_nonvacuous` | N+/0 | constant-½ but real failure |
| `regress`, `cost_circularity` | P | 2b regress; `hcost` is flagged soft-joint (c) |
| `cost_setup_realizable` | N+ | locates the contradiction on `hcost` (good guard) |
| `predictable_imp_uninfluenced` | L | propositional; not instantiated (§3.5) |
| `resale_lb`, `asympLE_zero_of_lb` | P | one-sided-indicator resale algebra |
| `externalized_self_trust` | C | conditional on the *dead* Tracking hyp + `hNoArb`(b/c) |
| `round_profit_pos` | T | `a<b ⟹ 0<b−a` |
| `nondogmatism_refutes`, `manipulation_confined` | T | modus tollens; conclusion ⊂ assumed (§3.4) |

### `FrozenDeliberation.lean`

| Theorem | Kind | Notes |
|---|---|---|
| calculus (`approx_of_asympLE_both`, etc.) | P | the squeeze/triangle toolkit |
| `blind_cost_realizable` | N+ / (c) | abstract cost contrast; complexity content interpretive (§3.6) |
| `amp_fixed_half`, `amp_zero`, `amp_boundedness_forces_id` | P | small but real |
| `amp_*_cut_value`, `amp_*_cut_nonneg/nonpos` | P | sign algebra; **integral hand-evaluated** (§3.7) |
| `tracking_sell_profit` | T | one `linarith`; exploit unmodeled |
| **T1** `faithful_tracking` | S | conclusion ≡ conjunction of the two named hyps (§3.3) |
| **T2** `meta_trust` | S/C | small squeeze; `hexpprovind`(b) |
| `quote_is_truth_on_G` | S | engine = triangle over named on-`G` bound |
| **T3** `conditional_tower` | S | = `approx_of_abs_le`; content is named `hcarry` (§3.3) |
| **T4** `value_on_G` | C | genuine four-liner; but tower steps are T3 |
| **T6** `calibration_residual_on_G` | S/T | triangle inequality |
| **T7** `limit_agreement_on_G` | S/T | triangle; per-member convergence (b) named |
| **T7** `underdetermination_off_G` | T | two points in `(0,1)`; oversold name (§3.4) |
| `TS_on_G` | S | squeeze over def-of-`G` |
| `TS_off_G_fails` | N+ | genuine miscalibration counterexample |
| `worth_unbounded_if_settles` | P/T | Archimedean; "ε per round" unmodeled |
| `worth_zero_if_never_settles` | T | `0·ε = 0` |

### `FaithfulAcceleration.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `round_profit_ge`, `profit_partial_sum_ge`, `profit_diverges`, `violation_not_persistent` | P | genuine trader-arithmetic chain |
| `soft_total_trust` | C | `w` abstract; `hone`/`hmis` were the (c) leak; `hbias`/`hbdd`(b/c) named |
| `profit_diverges_nonvacuous` | N+ | concrete divergence model |
| `softInd_*`, `dsWeight_*` (incl. `dsWeight_continuous`, `_pos_imp_fst/_snd`) | P | the weight now constructed; continuity proved (§3.2) |
| `soft_total_trust_doublysoft` | C | `hone`/`hmis` discharged; `hbias`/`hbdd` still named |

### `TowerAndAcceleration.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `approx_refl/symm/trans` | P | calculus |
| `tower_imp_tracking` | P | pure `≈ₙ` reduction; corner-quote collapses are hyps (b/c) |
| `pointwise_tower_fails` | C | composes the reduction with named `tracking_fails` |
| `witness_partial_sum`, `witness_gap`, `witness_tracking_fails` | P | genuine ½-defect witness arithmetic |
| `two_faces_distinct` | P/N+ | the "per-day dead, averaged alive" witness — real content |
| `tower_dead_on_witness` | C | composition through Part 1 |

---

*End of audit. The genuinely-proved tier (§2) is real and worth trusting for what it is; the
concerning gaps (§3) are concentrated in the cross-process forcing results and the trivial
stubs, and the gap between "the algebra composes" and "deference is forced" is the thing to keep
in view whenever the corpus is cited.*
