# Scout report — Formalization frontier (run 3, LEGITIMACY & DEFERENCE)

*Scout id: `scout-lean-scout`. Written 2026-07-01. Lens: what can actually be kernel-checked
next, ranked by feasibility × value. Sources read in full: the five `lean-deference` modules
(`LeanDeference.lean`, `SelfReferentialTarget.lean`, `FrozenDeliberation.lean`,
`FaithfulAcceleration.lean`, `TowerAndAcceleration.lean`), `lean-deference\AUDIT.md`, run-1
`deference-trust-lab\lean\` artifacts, run-2 `run2\lean\` artifacts + `run2\todos\TODOS.md`
(GLOBAL OFF-LIMITS) + `run2\report\CRITIQUE.md`, `li-deference.md` (whole file, esp. §0.3 and
the translation-chain material), `deference-in-logical-induction-v6.md` (§1, §3, §5, §8),
`faithful-acceleration.md` section map.*

## 0. Where the frontier actually is

The honest boundary, per AUDIT §1 and run-2 CRITIQUE §0, is:

1. **Everything machine-checked so far is finite single-frame or named-hypothesis-asymptotic.**
   The genuinely-proved tier (AUDIT §2) is real; the *forcing* (criterion ⇒ tower/tracking)
   is nowhere in Lean — T1/T3 are squeezes over hypotheses equivalent to their conclusions
   (AUDIT §3.3, severity High #1–#2).
2. **Not one cross-agent statement is kernel-checked.** Run 2's only cross-agent object
   (`trust-laundering`) is a SHADOW: its links were checked on a 32-point indicator grid,
   not the real `∀ X : W → ℝ, ∀ s` quantifier (CRITIQUE §5).
3. **The legitimacy program (li-deference §0.3, v6 §6.5/§8) has zero formal objects** beyond
   the round-1 finite sign-lemmas (`Legitimacy.*`, off-limits as objects).
4. Named, explicitly-invited Lean gaps: AUDIT recommendations 2–5 (rename/strengthen
   near-vacuous theorems; instantiate the dichotomy; Mathlib-`∫` the amplifier integrals;
   model a minimal market), echoed verbatim in v6 §8.

So the highest-value kernel-checkable moves are: (a) **discharge a named hypothesis** of an
existing headline theorem from a criterion-like axiom over a *class* of strategies (the
scoped version of "model a minimal market"); (b) **kernel-check the actively-edited
translation chain** in Abram's own master notes, where I believe one arrow is *false as
written* for soft gates; (c) **the first honest cross-agent statement** with the real
quantifier; (d) **the first legitimacy-program formal object** that is not a sign lemma;
(e) close AUDIT-flagged gaps that are self-contained (`∫`, the off-G stub, the dichotomy).

A finding made during scouting that upgrades one proposal from "chore" to "result": the
parallel threshold-trust cuts admit a **bounded, [0,1]-valued, continuous non-identity
impostor** (`g(e) = min(2e, 1)`), not just the unbounded affine amplifier. Hand-checked
algebra (to be kernel-checked; exact-rational script check was blocked by a transient
tool-permission outage this session, but the algebra is two one-line case splits):
lower cut `∫₀ᵗ g ≤ t²` is an *equality* for `t ≤ ½` and reduces to `(t−½)² ≥ 0` for
`t > ½`; upper cut `∫ₜ¹ g ≥ t(1−t)` reduces to `¾ ≥ t` for `t ≤ ½` and `(1−t)² ≥ 0` for
`t > ½`. This sharpens v6 §1.6: **boundedness does not rescue the soft⇒hard squeeze** —
it only kills the *affine* impostor. See Q3.

A second scouting find: in `li-deference.md` (the boxed `v_n / q_n / w_n` chain, lines
~213–226), the second displayed implication
`q_n ≳ₙ 0 ⟹ Σ w_n < ∞` is **false as stated once the gate is soft** — exactly the softening
the same file mandates two chains earlier ("a 0/1 weight is illegal in logical induction").
Counterexample: `g_n = 1/(n+1)`, `E^H_n(X) ≡ t − 2ε`. Then `q_n = −2ε/(n+1) → 0` (so
`q_n ≳ₙ 0` holds) while `w_n = g_n·Ind_δ(E_n < t−ε) = 1/(n+1)` (gate saturated for `δ ≤ ε`)
and `Σ w_n` is harmonic-divergent. The implication is rescued exactly when the gate has a
support gap (`g_n ∈ {0} ∪ [c,1]`) — i.e. is effectively hard. The *first* implication
(`Σ v_n < ∞ ⟹ q_n ≳ₙ 0`) survives softness, via the ramp identity `q_n = −δ·v_n` on the
ramp region. See Q2. This is checkable against a live, actively-edited argument in the
principal's master notes — the best kind of formalization target.

Everything below: **modality legend** LEAN-CORE / EXEC / PROSE / MIXED as defined by the
orchestrator. All Lean encodings are standalone files (no `import LeanDeference`), copying
needed definitions with citations, ending in `#print axioms`, per GROUND-RULES §2.

---

## Q1 — The criterion-to-forcing microscope: discharge T1's hypotheses from a no-unbounded-profit axiom over a class of legal strategies

**Claim (acceptance target).** A standalone Lean file defining a minimal market
`(a Y : ℕ → ℝ)` (quotes, settlements, both `[0,1]`-bounded), a *class* of legal strategies
`Legal w := (∀ i, w i ∈ [0,1]) ∧ ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ ∀ i, w i = g (a i, Y i)`,
sell-side profit `Profit w n := ∑ i ∈ range n, w i * (a i − Y i)` (and the buy-side mirror),
and the criterion `Criterion := ∀ w, Legal w → ¬ Tendsto (Profit w) atTop atTop`; and proving,
with NO `AsympLE`/`Approx` hypothesis anywhere:

```
theorem criterion_forces_upper (h01 : bounds) (hC : Criterion) : AsympLE a Y
theorem criterion_forces_lower (h01 : bounds) (hC : CriterionBuy) : AsympLE Y a
theorem criterion_forces_tracking (…) : Approx a Y     -- T1 with hypotheses DISCHARGED
```

Proof route (real content, not a squeeze): negate `AsympLE a Y` to get `∃ ε > 0` with
`a n > Y n + ε` frequently (`Filter.Frequently` extraction from the `∀ᶠ` negation);
instantiate the criterion at the *constructed* legal strategy `w i = softInd δ (a i − Y i − ε/2)`
(`softInd` copied from `FaithfulAcceleration.lean` with citation; continuity is
`dsWeight_continuous`-style `fun_prop`); per-round profit is `≥ 0` always and `≥ ε` on the
frequent days (one-sidedness of `softInd`); monotone partial sums unbounded ⟹
`tendsto_atTop_atTop_of_monotone'` ⟹ contradiction. Required extras: (i) **non-vacuity of
the criterion**: a concrete market (`a = Y = const ½`) satisfying `Criterion` (profit ≡ 0 for
every legal `w` bounded by… careful: sell profit is 0 identically when `a = Y`); (ii) a
**near-miss**: a market with a persistent gap plus an explicit legal strategy whose profit
provably `Tendsto atTop` (so `Criterion` genuinely excludes something).

**Why it matters.** This is the scoped version of AUDIT recommendation 5 and v6 §8 bullet
"Model a minimal market in Lean so 'criterion ⇒ forcing' becomes a theorem" — the *only*
route AUDIT names to convert its two High-severity findings (§3.1, §3.3) from
named-hypothesis to theorem. It turns `Frozen.faithful_tracking` (T1, currently a dressed
tautology per AUDIT §3.3) into a genuine composition: the conclusion `Approx a Y` is derived
by instantiating a quantified criterion at a *constructed member of a class*, which is
exactly the logical shape of the informal argument (v6 §5.4 T1). Honest scope to declare in
the artifact: the criterion is still an axiom about the market (that is the intended type-(b)
boundary — it is the LI criterion); the strategy's read-access to `Y i` at round `i` is the
declared Lean rendering of the power assumption (A4); real LI cash accounting (buy at `n`,
settle at `σ(n)`, budgets) is collapsed to per-round net, same discipline as
`FaithfulAccel`. Possible stretch goal: derive `soft_total_trust`'s `hbdd` the same way
(needs care — those partial sums are not monotone, so "not → ∞" does not give a bound; if it
doesn't go through cleanly, say so).

**Modality.** LEAN-CORE. **Difficulty.** Medium (one focused session; the `Frequently`
extraction and the monotone-divergence lemma are the only nonstandard steps). Mathlib:
`Filter.Frequently`, `eventually_atTop`, `tendsto_atTop_atTop_of_monotone'`,
`Finset.sum_le_sum`, `Continuous`/`fun_prop`.

**Novelty risk.** `DeferenceTrader.*`, `Frozen.tracking_sell_profit`,
`FaithfulAccel.soft_total_trust(_doublysoft)` are off-limits/established — none of them
*quantifies over a strategy class* or *derives* an `AsympLE` conclusion from a criterion; all
take the inequality as hypothesis or prove one-line stubs. The pre-registered fake: a
"criterion" quantifying only over the single needed `w` (then the axiom *is* the conclusion),
or `Legal` defined with the target inequality inside. The shadow test is the class-quantifier
plus the two witnesses ((i) and (ii) above).

---

## Q2 — The weakening chain of `li-deference.md` is sound for hard gates and FALSE for soft gates

**Claim (acceptance target).** Kernel-check the three-statement chain of `li-deference.md`
(boxed definitions `g_n, w_n, q_n, v_n`, lines ~213–226), as three theorems about real
sequences with `Ind_δ` the actual clamp ramp (copied `softInd`), `E : ℕ → ℝ` bounded,
`g : ℕ → ℝ` valued in `[0,1]`, `q n := g n * (E n − t)`:

1. **(sound, soft)** `Summable (fun n => g n * softInd δ (t − E n)) → AsympLE (fun _ => 0) q`
   — "bounded sum of violations implies convergence to the rule" — a genuine proof via the
   ramp identity `q n = −δ · v n` on the ramp region and `q n ≥ −B · v n` on the saturated
   region, then `Summable.tendsto_atTop_zero`.
2. **(FALSE, soft — the negative result)** the second arrow as written,
   `AsympLE (fun _ => 0) q → Summable (fun n => g n * softInd δ (t − ε − E n))`, is refuted
   by the explicit witness `g n = 1/(n+1)`, `E n ≡ t − 2ε`, `δ ≤ ε`: hypothesis holds
   (`q n = −2ε/(n+1) → 0`), conclusion fails (harmonic divergence,
   `Real.not_summable_one_div_natCast`).
3. **(repaired)** the arrow holds under a support gap: if `∀ n, g n = 0 ∨ c ≤ g n` for some
   `c > 0`, then `AsympLE 0 q → (∀ᶠ n, w n = 0)`, hence `Summable w` — i.e. the note's
   "convergence to the rule implies only finitely many violations of any slightly stricter
   rule" is exactly the **hard-gate** regime.

**Why it matters.** These three arrows are load-bearing in the actively-edited translation
chain of `li-deference.md` ("Five Variations of Total Trust" — the same section round-3's
legitimacy focus points at) and in `faithful-acceleration.md` §5's "the weakening". The note
itself softens the indicator two chains earlier because "a 0/1 weight is illegal in logical
induction" — and the scouting analysis says the chain's second arrow does not survive that
softening. A kernel-checked (sound / false / repaired) triple is direct, actionable feedback
into the principal's live notes: the weakening step is valid **only where the gate is
effectively hard**, so the prose must either keep the margin-δ bookkeeping explicit or state
the support-gap condition. It is also precisely the requested kind of asymptotic target:
`Tendsto`/`Summable` statements over a parameterized family that are more than
average-vs-sup arithmetic (the false direction *is* an average-vs-count subtlety, but the
sound direction's ramp identity and the repair's support-gap dichotomy are new content, and
the target is a named chain in the corpus, not a generic fact).

**Modality.** LEAN-CORE. **Difficulty.** Easy-medium (one session).
Mathlib: `Summable.tendsto_atTop_zero`, `Real.not_summable_one_div_natCast` (or
`not_summable_natCast_inv`), `Filter.Eventually`, `squeeze` lemmas.

**Novelty risk.** Off-limits `averaging-hides-spikes` (run 2) is avg→0-vs-sup↛0 for a spike
family — different statement, different objects (that one has no gates, no summability, no
liminf; flag the family resemblance honestly). `FaithfulAccel.violation_not_persistent` is
the established *criterion ⇒ ¬(W → ∞)* contrapositive — also different (it never relates the
pointwise law `q_n ≳ 0` to `Σ w_n`). Fake version: proving the chain with a *hard* indicator
throughout (then (2) is true and the finding evaporates) or laundering the support gap into
(2) without exhibiting the soft counterexample. Detection: theorem (2) must be a `¬(∀ …)`
with the explicit `1/(n+1)` witness compiled.

---

## Q3 — The bounded impostor: parallel threshold-trust cuts cannot pin the calibration curve even among bounded curves (with the amplifier integrals finally done via Mathlib `∫`)

**Claim (acceptance target).** One standalone file, three parts, all integrals as genuine
`intervalIntegral` (no hand-evaluated antiderivatives anywhere in the statements):

1. **AUDIT §3.7 discharge:** `∫ e in t..1, amp c e = (1+2c)*(1−t^2)/2 − c*(1−t)` and the
   `0..t` companion, via `intervalIntegral.integral_comp`-free elementary lemmas
   (`integral_id`, `integral_const`, linearity), then restate
   `amp_upper_cut_nonneg`/`amp_lower_cut_nonpos` with the *integral* on the left-hand side:
   `t*(1−t) ≤ ∫ e in t..1, amp c e` etc.
2. **The bounded impostor (new result):** define `gimp e := min (2*e) 1`; prove
   `Continuous gimp`, `∀ e ∈ [0,1], gimp e ∈ [0,1]`, `gimp (1/4) ≠ 1/4` (non-identity), and
   BOTH cut families for every `t ∈ [0,1]`:
   `∫ e in 0..t, gimp e ≤ t^2` and `t*(1−t) ≤ ∫ e in t..1, gimp e`
   (piecewise-linear integrals via `intervalIntegral.integral_add_adjacent_intervals` split
   at `½`; closed forms `t^2` for `t ≤ ½`, `t − ¼` above).
3. **The affine classification (completes the amp story):** for `g e = α*e + β` with
   `g` mapping `[0,1]` into `[0,1]`, passing both cut families for all `t ∈ [0,1]` forces
   `α = 1 ∧ β = 0` — generalizing `amp_boundedness_forces_id` (which handles only the
   one-parameter `(1+2c)e − c`, `c ≥ 0` family) to all affine curves.

**Why it matters.** (1) is AUDIT recommendation 4 verbatim (the corpus's one remaining
hand-computation; v6 §8 explicitly invites it). (2) is a genuinely new obstruction result
for v6 §1.6: the note's story is "the amplifier passes every parallel cut; what rules it out
is boundedness biting at the extremes" — inviting the hope that boundedness closes the
soft⇒hard squeeze. The bounded impostor kills that hope inside the kernel: even among
continuous `[0,1]→[0,1]` curves, the parallel cuts leave a non-identity survivor, so the
squeeze genuinely needs the non-parallel cuts (DDB's convex-hull machinery), full stop.
(3) pins where boundedness *does* bite: exactly the affine class. Together they sharpen the
§1.6 frontier from "prose expectation" to a machine-checked trichotomy (affine+bounded ⟹ id;
bounded alone ⟹ not id; the survivor exhibited). Hand-verified this session; the kernel
check is the deliverable.

**Modality.** LEAN-CORE. **Difficulty.** Medium (Mathlib `intervalIntegral` bookkeeping is
the cost center; the piecewise split and `Continuous.intervalIntegrable` are standard).

**Novelty risk.** `Frozen.amp_*` are established/off-limits as objects — this file *uses*
them only as the comparison point and proves strictly more: the amp cut *statements* are
upgraded (integral LHS, closing AUDIT §3.7), the impostor is a new object, the affine
classification is a new theorem strictly containing `amp_boundedness_forces_id`. Fake
version: re-proving the `ring` identities with `∫`-free statements (detectable: the word
`intervalIntegral` must appear in the *theorem statements*, not just proofs), or an impostor
that fails boundedness (detectable: the `[0,1]` mapping lemma must compile).

---

## Q4 — First kernel-checked cross-agent trust statement: Total Trust is not transitive, with the honest `∀ X : W → ℝ, ∀ s : ℝ` quantifier

**Claim (acceptance target).** A standalone Lean file with a concrete 3-or-4-world frame and
three agents (prior `πH`, expert maps `PA PB : W → W → ℝ`), where Total Trust is the exact
DDB/LeanDeference conditional-mass inequality
`TT π P := ∀ (X : W → ℝ) (s : ℝ), s * ∑ w, (if s ≤ ∑ v, P w v * X v then π w else 0) ≤ ∑ w, (if s ≤ … then π w * X w else 0)`,
proving:

1. **Ingredient lemma (general, reusable):** if `P` is the `π`-conditional-expectation
   expert of a *partition* (encoded as `c : W → W` idempotent cell-representatives, with
   `P w v = π v * ind (c v = c w) / πcell w` on positive cells), then `TT π P` holds — for
   ALL real `X` and `s`. Proof: `{w : E_w(X) ≥ s}` is a union of cells (E is
   cell-constant); the TT mass splits fiberwise (`Finset.sum_fiberwise`) into per-cell terms
   `π(cell)·(E_cell(X) − s) ≥ 0`. This is the finite tower property as a Total-Trust
   statement — classical math, but the load-bearing new tool here.
2. **Link 1:** `TT πH PA` with `PA` = `πH`-conditional on partition `F_A` — by lemma 1.
3. **Link 2:** `TT πA PB` with `PB` = `πA`-conditional on partition `F_B`, `πA ≠ πH` — by
   lemma 1.
4. **Long edge fails:** `¬ TT πH PB`, witnessed at an explicit rational `(X, s)` by
   `norm_num` — possible because `PB` is a conditional expectation w.r.t. `πA`, not `πH`.
5. **Recovery near-miss (mandatory):** setting `πA := πH` in the same frame makes the long
   edge hold (by lemma 1 again) — certifying the failure is caused by the prior mismatch,
   not the frame.

An EXEC pre-phase (exact rationals, Python `fractions`) searches small frames for a witness
`(πH, πA, F_A, F_B, X, s)` before any Lean is written; the run-2 gate's six fine-grid
witnesses (CRITIQUE §5) are candidate seeds but need re-derivation since the artifact's
numbers are explicitly not to be cited.

**Why it matters.** Run-2 CRITIQUE §0's headline deficiency: "not a single cross-agent trust
claim is machine-checked, and the one genuine cross-agent search is a shadow." The shadow was
precisely the quantifier: `∀ X` checked on a 32-point indicator grid. This proposal crosses
the boundary honestly: links 2–3 hold for **all real X and s** because they are *proved*
(via lemma 1), not grid-checked; only the *failure* needs a point witness, which is the
logically correct asymmetry (∀-claims proved, ∃-claims witnessed). Safety reading (state
with the run-2 qualifiers): alignment/trust is not closed under delegation, now as a theorem
about the exact DDB inequality on a concrete frame rather than a refuted grid search.

**Modality.** MIXED (EXEC search + LEAN-CORE proof; the deliverable of record is the Lean).
**Difficulty.** Medium-hard — lemma 1's fiberwise sum manipulation is the crux; the frame
hunt is easy. One generous session.

**Novelty risk.** GLOBAL OFF-LIMITS: `DeferenceConverse.*` (incl. `value_iff_totalTrust`) is
two-party Value⟺TT — not touched; the TT definition is *copied* with citation, and nothing
about Value is (re-)proved. Run-2 `trust-laundering` is the refuted EXEC shadow — this is
its correction, explicitly invited by CRITIQUE §5 ("re-run required") and stronger than a
re-run (proof, not grid). Run-2 `aumann-modesty` is single-agent averaging — disjoint.
Lemma 1 is classical (law of total expectation / immodest-case collapse) — label it as
classical instantiation, not discovery; check it is not `CM_implies_immodest` (it is not:
that theorem goes CM-identity ⇒ fiber mass 1, one agent, opposite direction). Fake version:
links "proved" by `decide` over an indicator grid (the run-2 shadow), or `PB` accidentally
`πH`-conditional (then the long edge holds and the witness is fabricated — the near-miss (5)
guards this).

---

## Q5 — Legitimacy gates vs. the calibration class: filtering to non-corrupt futures is exactly a change of calibration class (first formal object of the §0.3 program)

**Claim (acceptance target).** Model the §0.3 legitimacy move — "the AI should predict human
feedback only through non-corrupted futures" — as a **gate** `c : ℕ → ℝ`, `c n ∈ [0,1]`
(legitimacy weight on day `n`'s feedback), multiplying the faithful-acceleration violation
weight. Standalone file, three theorems + one counterexample:

1. **(transfer, easy but necessary)** The support/one-sidedness hypotheses of
   `soft_total_trust` transfer from `w` to `c·w`: `0 < c n * w n → 0 < w n`, so `hone`/`hmis`
   hold for the gated weight; hence the *entire trader chain* of `FaithfulAcceleration.lean`
   (copied with citation) applies verbatim to `c·w` — **provided** the calibration hypothesis
   `hbias` holds *for the gated weight*.
2. **(the honest heart — gating breaks calibration)** An explicit witness where calibration
   holds for `w` but FAILS for `c·w`: `w ≡ 1`, bias `v n − a n = (−1)^n` (so
   `Cₙ/Wₙ = O(1/n) → 0`, a compiled `Tendsto`), gate `c n = 1` on odd days, `0` on even
   (so the gated ratio is identically `1`, `¬ Tendsto … (𝓝 0)` compiled). Interpretation
   (labeled as such): a legitimacy filter that correlates with the sign of the forecast
   error destroys the forced-Total-Trust argument — "predict only through non-corrupt
   futures" is NOT free; it is a new calibration assumption about the *gated* feedback.
3. **(the positive closure condition)** If calibration is assumed for **every weight in a
   class 𝒲 closed under pointwise multiplication by gates in a class 𝒞** (the Lean encoding:
   `hbias : ∀ w ∈ 𝒲, Tendsto (ratio w) atTop (𝓝 0)` plus `hclosed : ∀ w ∈ 𝒲, ∀ c ∈ 𝒞, c•w ∈ 𝒲`),
   then gated soft Total Trust holds for every `c ∈ 𝒞` — the first machine-checked statement
   of the shape "legitimacy-gated deference is forced iff the gate stays inside the
   generable-weight class", which is the formal face of v6 §8's "replacing 'all futures' with
   'non-corrupt futures' in the target".

**Why it matters.** Round 3's stated focus. li-deference §0.3 and v6 §6.5/§8 say the
legitimacy program "is currently a desideratum, not a model". This proposal does not pretend
to model corruption; it locates, inside the kernel, the *exact mathematical joint* where a
legitimacy filter meets the existing positive result: the filter is a weight-class operation,
and the forced-trust theorem survives it exactly when the LI calibration theorem (Expectation
Unbiasedness From Feedback, quantified over generable weights) covers the gated weight.
Theorem 2 is the honest negative: an adversarially-correlated "legitimacy" gate (e.g. one
the AI itself influences — the §0.3 corruption scenarios) sits outside the class and voids
the guarantee. That is a real, checkable, non-obvious statement of the manipulation worry.

**Modality.** LEAN-CORE. **Difficulty.** Easy-medium (theorem 3's class plumbing is the only
design work; 1 and 2 are short). One session with room to spare — could pair with Q2.

**Novelty risk.** Round-1 `Legitimacy.*` / `LegitimacyCorrigibility.*` (off-limits) are
finite sign-lemmas about a defect object — no gates, no asymptotics, no calibration; nothing
is re-skinned. `soft_total_trust(_doublysoft)` is established — it is *used* (copied,
cited), not re-proved; the new content is the transfer lemma + the gating-breaks-calibration
witness + the closure theorem. Run-2 `averaging-hides-spikes` is avg-vs-sup — different.
Fake version: proving only theorem 1 (a one-line instantiation) and calling it "legitimacy
formalized" — the pre-registered fake; the deliverable stands or falls on theorems 2 and 3.

---

## Q6 — Two-agent finite Aumann agreement, kernel-checked, with a PROPER common-knowledge event — and the modest two-agent disagreement witness

**Claim (acceptance target).** Standalone file, concrete finite frame(s):

1. **The two-agent theorem (classical, instantiated):** worlds `W` (4–5), common prior `π`,
   TWO partitional correspondences `E1 E2 : W → Finset W` (decide-checked partitions), common
   knowledge defined genuinely as closure: an event `C` with `decide`-checked
   (i) `C` is a union of `E1`-cells AND of `E2`-cells, (ii) `C ≠ univ` (**a proper
   self-evident sub-event**, fixing run-2 CRITIQUE §1b's vacuity), (iii) nonempty. Theorem:
   if the posterior `E_π(X | Ei(w))` equals `qi` on every agent-`i` cell inside `C`
   (`i = 1, 2`), then `q1 = q2` (both equal `E_π(X | C)`, by the partition-averaging
   identity per agent). All by `decide`/`norm_num` on explicit rationals plus one general
   partition-averaging lemma.
2. **The modest two-agent near-miss (the lab-specific content):** replace `E2` by a
   reflexive-transitive NON-partitional (S4) correspondence; exhibit a `C` that both
   correspondences' cells cover, with agent-1 cell-posteriors constant `q1` and agent-2
   cell-posteriors constant `q2 ≠ q1` — two agents "sharing" a common-knowledge event and
   still disagreeing, with the disagreement *computed from* `π, E1, E2, X` (conclusion, not
   hypothesis).

**Why it matters.** Run-2 CRITIQUE §1a's explicit gap: `aumann-modesty` is a **single-agent**
averaging fact; "two rational agents fail to agree" was never built, and the whole-space `C`
made the self-evidence checks vacuous (§1b). This delivers the genuine two-agent object both
ways: agreement forced in the partitional case (the near-miss anchoring), disagreement
exhibited in the modest case — the finite reflection of v6's "persistent human–AI
disagreement is not by itself evidence of misalignment" with, for the first time, two actual
agents. It would be the corpus's first kernel-checked statement whose very *statement* has
two epistemic agents in it.

**Modality.** LEAN-CORE. **Difficulty.** Medium (the common-knowledge closure bookkeeping;
`decide` on Finset partition predicates is routine).

**Novelty risk.** Aumann 1976 is classical — label part 1 as instantiation, cite, do not
present as discovery. Run-2 `aumann-modesty` (off-limits as object): its
`partition_averaging` lemma may be needed — *copy with citation* (ground-rules §2 standalone
discipline), and the new content must be strictly the two-agent composition + the proper-`C`
fixed point + the two-agent modest witness. Fake version: `C = univ` again (detectable:
`C ≠ univ` must be a compiled theorem), or the "disagreement" hypothesized rather than
computed.

---

## Q7 — Instantiate the §D dichotomy with real-sequence types (AUDIT rec 3) — with a pre-registered refusal condition

**Claim (acceptance target).** Replace `SelfRefTarget.predictable_imp_uninfluenced`'s opaque
`Prop`s by the real objects, producing one theorem whose hypotheses are the actual 2a data
and 2b cost data and whose conclusion is the composed dichotomy:

```
theorem dichotomy_instantiated
    (a r Y : ℕ → ℝ) (R RA : ℕ → ℝ) (F : ℕ → ℕ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hQuoteRef : Tendsto (fun n => Y n - antiInd (r n)) atTop (𝓝 0))   -- the target IS quote-referencing
    (hround : Tendsto (fun n => r n - a n) atTop (𝓝 0))
    (hmono : StrictMono RA) (hF : ∀ n, n < F n) (hshare : ∀ n, RA (F n) ≤ R (F n)) :
    (¬ Approx a Y) ∧ ((∀ n, R (F n) ≤ RA n) → False)
```

with `tracking_fails` and `cost_circularity` (copied, cited) as the engines — i.e. the
dichotomy formed *at matching types*, not as a propositional silhouette. **Pre-registered
refusal condition:** if the honest instantiation turns out to be nothing but the conjunction
of the two existing theorems with no compositional content beyond `And.intro` (a live risk —
AUDIT §3.5 says the composition is the missing part, but the composition may simply BE the
conjunction once types match), the deliverable is a short negative note saying exactly that,
recommending AUDIT rec-3 be re-scoped or closed as "nothing further to prove", with the
compiled conjunction attached as evidence.

**Why it matters.** AUDIT recommendation 3 verbatim; finding #4 (Medium). Either outcome is
informative: a genuine composition upgrades the §4.4 dichotomy from "logical silhouette" to
theorem; the negative outcome retires a standing audit recommendation with proof that it was
already as composed as it can be — which is itself a contribution to the audit ledger.

**Modality.** LEAN-CORE. **Difficulty.** Easy (the risk is not difficulty but triviality —
hence the refusal condition).

**Novelty risk.** High re-skin risk by construction, and declared: `tracking_fails`,
`cost_circularity`, `predictable_imp_uninfluenced` are all established. What is NOT
established is their type-matched composition (AUDIT §3.5: "the composed dichotomy is not
formed in Lean; only its logical silhouette is"). The fake version is shipping the
conjunction *as if* it were more; the shadow test is the explicit triviality verdict in the
notes either way.

---

## Q8 — Replace the `underdetermination_off_G` stub: settlement-gated profit is invariant under off-settlement differences (AUDIT finding #3)

**Claim (acceptance target).** AUDIT severity-High finding #3: `underdetermination_off_G`
proves "two points in an interval" under a model-theoretic name. Honest replacement, one
file: define settled indices `S : Set ℕ` (decidable), settlement-gated trader profit
`Profit p w n := ∑ i ∈ range n ∩ S, w i * (settle i − p i)` for a price sequence `p`; prove

1. **(invariance — the T7 mechanism, made real)** for any two price sequences `pa pb` with
   `∀ i ∈ S, pa i = pb i`, every settlement-gated trader accrues *identical* profit against
   both: `∀ w n, Profit pa w n = Profit pb w n` — so no such trader distinguishes them, ever;
2. **(non-degenerate witness)** an explicit pair `pa pb` agreeing on an infinite `S`
   (e.g. even indices, where both track a settling truth sequence — so both are individually
   "calibrated on S", a compiled `Tendsto` on the S-subsequence) and differing by exactly a
   prescribed `γ ∈ (0,1)` on every odd index, with `Approx`-on-S proved and
   `¬ Approx pa pb` proved;
3. **(the sharpening that makes it non-trivial)** the *converse* boundary: a trader whose
   gate is NOT settlement-confined (fires on odd days) DOES distinguish them — compiled —
   so the invariance is exactly co-extensive with settlement-gating (the v6 §5.6/T7 "forcing
   goes silent the instant settlement is withdrawn", as a theorem about this model).

**Why it matters.** Converts the corpus's most oversold theorem (AUDIT table row 3,
"Docstring describes intent only") into an object where "agree on G", "differ by γ off G",
and "no settlement-gated trader profits from the difference" are all *theorems about
constructed objects* rather than a naming convention. It does not model validity-as-inductor
(declared out of reach); it models exactly the mechanism v6 §5.6 asserts.

**Modality.** LEAN-CORE. **Difficulty.** Easy-medium. **Triviality risk, declared:** part 1
alone is close to "profit depends only on settled coordinates" (near-definitional). The
deliverable's honesty hangs on parts 2–3: the infinite-S calibrated witness pair and the
compiled non-gated-trader separation. If a referee judges 1–3 together still too thin, the
correct verdict is "stub honestly retired, no deep theorem here" — also acceptable.

**Novelty risk.** `Frozen.underdetermination_off_G` / `worth_*` are established objects —
this file replaces, not re-skins, them (the statement types are disjoint: theirs is
`∃ pa pb ∈ (0,1)²`, this is a quantified invariance + witnesses). `TS_off_G_fails` exhibits
diagonal miscalibration — different statement (no traders, no gating). Fake version: only
part 1 shipped.

---

## Ranking (feasibility × value, one focused session each)

| rank | id | value | feasibility | one-line |
|---|---|---|---|---|
| 1 | Q2 | high (live notes, likely-false arrow) | high | weakening chain: sound/false/repaired triple |
| 2 | Q1 | highest (AUDIT rec 5, the forcing gap) | medium | criterion ⇒ T1's hypotheses, over a strategy class |
| 3 | Q5 | high (round-3 legitimacy focus, first formal object) | high | legitimacy gate = calibration-class change |
| 4 | Q3 | medium-high (new §1.6 obstruction + AUDIT §3.7) | medium | bounded impostor + Mathlib-∫ amplifier |
| 5 | Q4 | high (first honest cross-agent theorem) | medium-low | TT non-transitivity with the real ∀X∀s |
| 6 | Q6 | medium (fixes run-2 §1a/§1b) | medium | genuine two-agent Aumann + modest witness |
| 7 | Q8 | medium (retires AUDIT #3) | high | settlement-gated invariance replaces the stub |
| 8 | Q7 | low-medium (either way informative) | high | dichotomy instantiation, refusal pre-registered |

**Claim-status labels used above:** the Q2 counterexample and Q3 impostor computations are
*hand-checked interpretation* as of this report (exact-rational script verification was
blocked by a transient tool-permission outage; the algebra is displayed and elementary);
everything cited from the corpus is labeled per its AUDIT classification; nothing above is
claimed as kernel-checked yet — kernel-checking them is precisely the proposed work.
